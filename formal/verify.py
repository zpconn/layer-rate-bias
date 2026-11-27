"""Build the complete project in a new directory and replay its exported proofs.

Run "python3 formal/verify.py" from the repository root after populating Lake's
dependency cache. No compiled project modules are reused. Reports are published
only after every verification step has succeeded.
"""

import argparse
from collections import Counter
from hashlib import file_digest, sha256
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import tomllib

FORMAL = Path(__file__).resolve().parent
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
KINDS = {"theorem", "definition", "opaque", "constructor", "inductive", "recursor"}
PROOF_DATA = ["layer-rates/paired-runs.csv"]
PAPER = FORMAL.parent / "paper/paper.md"


def paper_audit(manuscript, modules):
    """Translate manuscript source links to imports and theorem declarations."""
    imports, theorems = set(), set()
    for module, number in re.findall(r"formal/(\w+)\.lean(?:#L(\d+))?", manuscript):
        if module == "PaperAudit":
            continue
        if module not in modules:
            raise ValueError(f"Unknown paper module {module}")
        imports.add(module)
        if not number:
            continue
        lines = (FORMAL / f"{module}.lean").read_text().splitlines()
        index = int(number) - 1
        if lines[index].lstrip().startswith("/--"):
            while "-/" not in lines[index]:
                index += 1
            index += 1
        decl = re.match(r"^(?:@\[[^\]]+\]\s+)?(?:(?:private|public|noncomputable|protected|nonrec)\s+)*"
                        r"(theorem|lemma|def|abbrev|structure|inductive|class)\s+([\w'.]+)", lines[index])
        if not decl:
            raise ValueError(f"Expected a declaration at {module}.lean#L{number}")
        if decl[1] in ("theorem", "lemma"):
            # Project theorem links use declarations directly inside the module's namespace.
            theorems.add(f"{module}.{decl[2]}")
    if not theorems:
        raise ValueError("No paper theorems found")
    return ("module\n" + "".join(f"import all {name}\n" for name in sorted(imports))
            + "\n/-! Axiom reports for the theorem declarations linked from the manuscript. -/\n"
            + "".join(f"#print axioms {name}\n" for name in sorted(theorems)))


def check_paper_closure(modules):
    """Ensure every registered project module is reachable from the paper audit."""
    if PAPER.is_file() and paper_audit(PAPER.read_text(), modules) != (FORMAL / "PaperAudit.lean").read_text():
        raise ValueError("PaperAudit.lean differs from the paper links. Run verify.py --write-paper-audit.")
    needed = set()
    todo = ["PaperAudit"]
    while todo:
        current = todo.pop()
        source = (FORMAL / f"{current}.lean").read_text()
        for name in re.findall(r"^(?:public )?import (?:all )?(\w+)", source, re.MULTILINE):
            if name in modules and name not in needed:
                needed.add(name)
                todo.append(name)
    if set(modules) != needed:
        raise ValueError(f"Modules outside the paper closure: {sorted(set(modules) - needed)}")



def run(args, cwd, destination, *, log=False):
    """Capture diagnostics separately from machine-readable output."""
    with destination.open("wb") as stream:
        result = subprocess.run(
            args, cwd=cwd, stdout=stream,
            stderr=subprocess.STDOUT if log else subprocess.PIPE,
        )
    if result.returncode:
        diagnostic = (result.stderr or b"").decode(errors="replace")
        if destination.stat().st_size < 1_000_000:
            diagnostic += destination.read_text(errors="replace")
        raise RuntimeError(f"{args[:4]} failed\n{diagnostic[-6000:]}")
    if result.stderr:
        print(result.stderr.decode(errors="replace").strip(), flush=True)


def make_inventory(modules):
    imports = "\n".join(f"import all {module}" for module in modules)
    names = ", ".join(f"`{module}" for module in modules)
    return f"module\n{imports}\nimport Lean.Util.CollectAxioms\n" + """
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mods := [MODULES]
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  let mut results : Array String := #[]
  for (name, ci) in env.constants.map₁ do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless mods.contains mod do continue
    if let .axiomInfo _ := ci then throwError "project declares axiom {name}"
    let axioms ← collectAxioms name
    if axioms.any (fun a => !allowed.contains a) then throwError "{name} uses {axioms}"
    let kind := match ci with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive"
      | .quotInfo _ => "quotient"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
    results := results.push (String.intercalate "\\t" [mod.toString,kind,name.toString,
      String.intercalate "," (axioms.toList.map Name.toString),
      if ci.isUnsafe then "unsafe" else "safe"])
  for line in results.qsort (· < ·) do liftIO (IO.println line)
""".replace("MODULES", names)


def verify_dependencies(stage, versions):
    cache = FORMAL / ".lake/packages"
    (stage / ".lake").mkdir()
    (stage / ".lake/packages").symlink_to(cache, target_is_directory=True)
    for package in json.loads((stage / "lake-manifest.json").read_text())["packages"]:
        path = cache / package["name"]
        head = subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()
        if head != package["rev"]:
            raise ValueError(f"Dependency revision mismatch: {path.name}")
        changes = subprocess.check_output(
            ["git", "-C", str(path), "status", "--porcelain", "--untracked-files=no"], text=True,
        )
        if changes:
            raise ValueError(f"Modified tracked dependency source: {path.name}")
        versions[path.name] = head


def check_export(stream_path, roots):
    """Require an exported proof body for every theorem, including private ones."""
    names = {0: ""}
    axioms = set()
    found = set()
    tags = {"thm": "theorem", "def": "definition", "opaque": "opaque"}
    prefixes = tuple(b'{"' + key.encode() + b'":' for key in (*tags, "inductive", "axiom", "in"))

    def register(kind, data):
        name = names[data["name"]]
        if name in roots:
            if roots[name] != kind:
                raise ValueError(f"Export kind mismatch for {name}")
            found.add(name)
        if kind in tags.values() and "value" not in data:
            raise ValueError(f"Missing exported body of {name}")

    with stream_path.open("rb") as stream:
        for raw in stream:
            if not raw.startswith(prefixes):
                continue
            node = json.loads(raw)
            tag, data = next(iter(node.items()))
            if tag == "in":
                component = node.get("str", node.get("num"))
                prefix = names[component["pre"]]
                end = str(component.get("str", component.get("i")))
                names[data] = prefix + "." + end if prefix else end
            elif tag == "axiom":
                axioms.add(names[data["name"]])
            elif tag == "inductive":
                for part, kind in (("types", "inductive"), ("ctors", "constructor"), ("recs", "recursor")):
                    for decl in data[part]:
                        register(kind, decl)
            else:
                register(tags[tag], data)
    if axioms - STANDARD:
        raise ValueError(f"Unapproved axioms in closed export: {axioms - STANDARD}")
    if missing := (roots.keys() - found):
        raise ValueError(f"Export omitted {len(missing)} roots: {sorted(missing)[:12]}")
    return sorted(axioms)


def verify(stage, report):
    config = tomllib.loads((FORMAL / "lakefile.toml").read_text())
    modules = list(config["defaultTargets"])
    if set(modules) != {lib["name"] for lib in config["lean_lib"]}:
        raise ValueError("A library is missing from the default build")
    check_paper_closure(modules)
    sources = {"lakefile.toml", "lake-manifest.json", "lean-toolchain"}
    expected = {f"{m}.lean" for m in modules + ["PaperAudit"]}
    def current_sources():
        return {str(p.relative_to(FORMAL)) for p in FORMAL.rglob("*.lean") if ".lake" not in p.parts}

    if expected != current_sources():
        raise ValueError("Unregistered Lean source or missing source file")
    sources.update(expected)
    for source in sorted(sources):
        shutil.copyfile(FORMAL / source, stage / source)
    data_hashes = {}
    for name in PROOF_DATA:
        target = stage.parent / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(FORMAL.parent / name, target)
        data_hashes[name] = sha256(target.read_bytes()).hexdigest()
    versions = {}
    verify_dependencies(stage, versions)
    hashes = {source: sha256((stage / source).read_bytes()).hexdigest() for source in sorted(sources)}
    print(f"Building {len(modules)} project libraries from source", flush=True)
    run(["lake", "build", "--wfail"], stage, report / "build.log", log=True)
    run(["lake", "env", "lean", "-DwarningAsError=true", "PaperAudit.lean"], stage, report / "PaperAudit.log")
    print("Enumerating kernel declarations, including private proofs", flush=True)
    (stage / "CompleteInventory.lean").write_text(make_inventory(modules))
    run(["lake", "env", "lean", "-DwarningAsError=true", "CompleteInventory.lean"], stage, report / "declarations.tsv")
    roots, modules_seen, kinds = {}, set(), Counter()
    unsafe_helpers = []
    names = set()
    for line in (report / "declarations.tsv").read_text().splitlines():
        mod, kind, name, ax, safety = line.split("\t")
        if mod not in modules or kind not in KINDS or set(filter(None, ax.split(","))) - STANDARD:
            raise ValueError(line)
        modules_seen.add(mod)
        if name in names:
            raise ValueError(f"Duplicate inventory entry: {name}")
        names.add(name)
        if safety == "unsafe" and kind == "definition":
            unsafe_helpers.append(name)
        elif safety == "safe":
            roots[name] = kind
        else:
            raise ValueError(f"Unexpected declaration safety: {line}")
        kinds[kind] += 1
    if modules_seen != set(modules):
        raise ValueError("Incomplete declaration inventory")
    print(f"Exporting the dependency closure of {len(roots)} safe declarations", flush=True)
    export = stage / "proofs.ndjson"
    run(["lake", "env", "leanexport", *modules, "--", *roots], stage, export)
    axioms = check_export(export, roots)
    for checker, log in (("leanchecker", "kernel.log"), ("leanchecker-paranoid", "paranoid.log")):
        print(f"Replaying the closed export with {checker}", flush=True)
        run(["lake", "env", checker, "--from-export", str(export)], stage, report / log, log=True)
    check_paper_closure(modules)
    if expected != current_sources():
        raise ValueError("Lean sources were added or removed during the audit")
    for source, original in hashes.items():
        if sha256((FORMAL / source).read_bytes()).hexdigest() != original:
            raise ValueError(f"Source changed during verification: {source}")
    for name, original in data_hashes.items():
        if sha256((FORMAL.parent / name).read_bytes()).hexdigest() != original:
            raise ValueError(f"Proof data changed during verification: {name}")
    receipt = {
        "data_sha256": data_hashes,
        "toolchain": (stage / "lean-toolchain").read_text().strip(),
        "modules": modules,
        "declarations_by_kind": dict(kinds),
        "verified_export_roots": len(roots),
        "unsafe_compiler_helpers": unsafe_helpers,
        "allowed_axioms": axioms,
        "dependency_revisions": versions,
        "source_sha256": hashes,
        "verifier_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "export_bytes": export.stat().st_size,
        "checkers": ["leanchecker", "leanchecker-paranoid"],
    }
    with export.open("rb") as stream:
        receipt["export_sha256"] = file_digest(stream, "sha256").hexdigest()
    (report / "receipt.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path, default=FORMAL / "verification")
    parser.add_argument("--export", type=Path, help="Also retain the checked proof export at this path")
    parser.add_argument("--write-paper-audit", action="store_true", help="Update PaperAudit.lean from the paper links and exit")
    args = parser.parse_args()
    if args.write_paper_audit:
        modules = tomllib.loads((FORMAL / "lakefile.toml").read_text())["defaultTargets"]
        (FORMAL / "PaperAudit.lean").write_text(paper_audit(PAPER.read_text(), modules))
        return
    with tempfile.TemporaryDirectory(prefix="circle-lean-all-") as tmp:
        stage = Path(tmp) / "formal"
        stage.mkdir()
        report = Path(tmp) / "report"
        report.mkdir()
        verify(stage, report)
        if args.export is not None:
            args.export.parent.mkdir(parents=True, exist_ok=True)
            with (stage / "proofs.ndjson").open("rb") as src, args.export.open("xb") as dest:
                shutil.copyfileobj(src, dest)
        args.report.mkdir(parents=True, exist_ok=True)
        for file in report.iterdir():
            shutil.copyfile(file, args.report / file.name)
    print(f"All verification steps passed. Reports: {args.report}")


if __name__ == "__main__":
    main()
