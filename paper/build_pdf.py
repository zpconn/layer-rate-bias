"""Typeset paper/paper.pdf with its receipt-verified Lean source attachment."""

import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unicodedata
from urllib.parse import urlsplit
from zipfile import ZIP_DEFLATED, ZipFile, ZipInfo

from proof_attachment import inspect_text, prepare_attachment


REPOSITORY = "https://github.com/zpconn/layer-rate-bias/blob/"
TMLR_ASSETS = {
    "fancyhdr.sty": "3d2922548e0e5f1a6c5676eda6ebb6dc20d7d305b4d8c2be5f1c833fb1084e6d",
    "tmlr.bst": "306fd454cf40771bee01293eeb98d2c1cd5f4e11ed0cd7296b335f354fc45206",
    "tmlr.sty": "816214ff5919aa457b6b443bee52b15d9561421417b7f8a50cc84651519f0002",
}
DECLARATION = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|unsafe)\s+)*"
    r"(?:theorem\b|lemma\b|def\b|abbrev\b|structure\b|class\b|inductive\b|instance\b|/--|@\[)"
)


def take_labeled_paragraph(blocks, label):
    """Read the content following a bold Markdown label, preserving inline math."""
    line = blocks[0]["c"] if blocks and blocks[0]["t"] == "Para" else []
    if len(line) >= 3 and line[0]["t"] == "Strong" and line[1]["t"] == "Space":
        heading = "".join(word.get("c", " ") for word in line[0]["c"])
        if heading == label:
            blocks.pop(0)
            return {"t": "MetaInlines", "c": line[2:]}
    raise ValueError(f"Expected a manuscript paragraph starting with **{label}**")


def repo_target(target, paper_dir):
    url = urlsplit(target)
    if url.scheme or url.netloc or not url.path:
        return None
    source = (paper_dir / url.path).resolve()
    return source.relative_to(paper_dir.parent).as_posix()


def pdf_link(target, paper_dir, revision, anonymous, members, changed):
    """Use immutable repository URLs or human-readable locations in the ZIP."""
    url = urlsplit(target)
    path = repo_target(target, paper_dir)
    if not path:
        return ("https:" + target if url.netloc and not url.scheme else target), None
    if path == "paper/paper.md" and url.fragment:
        return "#" + url.fragment, None
    suffix = "#" + url.fragment if url.fragment else ""
    if anonymous or path in changed:
        if path not in members:
            raise ValueError(f"Manuscript target is missing from the supplement: {path}")
        line = ":" + url.fragment[1:] if re.fullmatch(r"L\d+", url.fragment) else suffix
        return path + suffix, path + line
    return REPOSITORY + revision + "/" + path + suffix, None


def verify_lean_anchor(source, fragment):
    lines = source.read_text(encoding="utf-8").splitlines()
    anchor = re.fullmatch(r"L([1-9]\d*)", fragment)
    if not anchor or int(anchor[1]) > len(lines) or not DECLARATION.match(lines[int(anchor[1]) - 1]):
        raise ValueError(f"Lean anchor must point to a declaration or its docstring: {source.name}#{fragment}")


def verify_documentation_anchors(root):
    for folder in (root, root / "docs", root / "formal", root / "paper", root / "layer-rates"):
        for doc in folder.glob("*.md"):
            if doc.name in {"paper.md", "paper-reader.md"}:
                continue  # The canonical manuscript is validated through its Pandoc AST.
            for target, line in re.findall(r"\]\(([^):\s]+\.lean)#(L\d+)\)", doc.read_text()):
                verify_lean_anchor((doc.parent / target).resolve(), line)


def verify_lean_listings(blocks, paper_dir):
    """Check each printed Lean listing against the source link immediately above it."""
    for i, block in enumerate(blocks):
        if block["t"] != "CodeBlock":
            continue
        attributes, listing = block["c"]
        if "lean" not in attributes[1]:
            continue
        previous = blocks[i - 1] if i else {}
        inlines = previous["c"] if previous.get("t") == "Para" else []
        if not inlines or inlines[-1]["t"] != "Link":
            raise ValueError("Each Lean listing must follow a paragraph ending in its source link")
        link = urlsplit(inlines[-1]["c"][2][0])
        source = (paper_dir / link.path).resolve()
        formal = paper_dir.parent / "formal"
        if (source.parent != formal or source.suffix != ".lean" or not link.fragment.startswith("L")
                or not link.fragment[1:].isdigit()):
            raise ValueError(f"Expected a local Lean source and a line anchor, got {link.geturl()}")
        start = int(link.fragment[1:]) - 1
        lines = listing.splitlines()
        original = source.read_text(encoding="utf-8").splitlines()
        if start < 0 or not lines or original[start:start + len(lines)] != lines:
            raise ValueError(f"Lean listing differs from {link.geturl()}")


def manuscript(pandoc, paper_dir, attachment_size, venue, anonymous, members):
    document = json.loads(subprocess.check_output(
        [pandoc, "--from=markdown+gfm_auto_identifiers", "paper.md", "--to=json"], cwd=paper_dir))
    verify_documentation_anchors(paper_dir.parent)
    blocks = document["blocks"]
    verify_lean_listings(blocks, paper_dir)
    if not blocks or blocks[0]["t"] != "Header" or blocks[0]["c"][0] != 1:
        raise ValueError("Expected the manuscript title as the first level-one heading")
    meta = document["meta"]
    meta["title"] = {"t": "MetaInlines", "c": blocks.pop(0)["c"][2]}
    author = take_labeled_paragraph(blocks, "Author")
    if anonymous:
        blocks[:] = [block for block in blocks if not (
            block["t"] == "Div" and "named-only" in block["c"][0][1])]
        meta["anonymous"] = {"t": "MetaBool", "c": True}
    else:
        meta["author"] = author
    meta["abstract"] = take_labeled_paragraph(blocks, "Abstract.")
    meta["proof-source-size"] = {"t": "MetaString", "c": str(attachment_size)}

    root = paper_dir.parent
    # An export-only commit must reproduce the same immutable source links.
    revision = subprocess.check_output(
        ["git", "log", "-1", "--format=%H", "--", "paper/paper.md", "formal", "docs", "layer-rates"],
        cwd=root, text=True).strip()
    changed = set()
    for args in (["diff", "--name-only", "-z", "HEAD"], ["ls-files", "-o", "--exclude-standard", "-z"]):
        changed.update(subprocess.check_output(["git", *args], cwd=root, text=True).split("\0"))

    # TMLR puts the bibliography before any appendices. citeproc fills #refs.
    position = next((i for i, block in enumerate(blocks) if block["t"] == "Header" and
                     block["c"][2][:1] == [{"t": "Str", "c": "Appendix."}]), len(blocks))
    if venue == "tmlr":
        ref_blocks = [{"t": "RawBlock", "c": ["latex", r"\bibliographystyle{tmlr}\bibliography{references}"]}]
    else:
        ref_blocks = [{"t": "Header", "c": [2, ["references", ["unnumbered"], []], [{"t": "Str", "c": "References"}]]},
                      {"t": "Div", "c": [["refs", [], []], []]}]
    blocks[position:position] = ref_blocks
    images = set()
    # The title is now metadata. Promote the remaining headings by one level.
    nodes = [document]
    while nodes:
        node = nodes.pop()
        if isinstance(node, list):
            nodes.extend(node)
        elif isinstance(node, dict):
            if node.get("t") == "Header":
                node["c"][0] -= 1
            elif node.get("t") == "Link":
                target = node["c"][2]
                path = repo_target(target[0], paper_dir)
                url = urlsplit(target[0])
                if path and path.endswith(".lean") and url.fragment:
                    verify_lean_anchor(root / path, url.fragment)
                target[0], location = pdf_link(target[0], paper_dir, revision, anonymous, members, changed)
                label = node["c"][1]
                already_named = label == [{"t": "Str", "c": Path(location or "").name}]
                if location and not already_named:
                    node["c"][1].extend([{"t": "Space"}, {"t": "Code", "c": [["", [], []], location]}])
            elif node.get("t") == "Image":
                path = repo_target(node["c"][2][0], paper_dir)
                if not path:
                    raise ValueError("Manuscript image must be a local file")
                images.add(path)
                node["c"][2][0] = path
            nodes.extend(node.values())
    return json.dumps(document), images


def tex_characters(text):
    """Render punctuation and accented Latin names with the template's TeX fonts."""
    symbols = {"’": r"\textquoteright{}", "‘": r"\textquoteleft{}", "“": r"\textquotedblleft{}",
               "”": r"\textquotedblright{}", "–": r"\textendash{}", "—": r"\textemdash{}",
               "·": r"\textperiodcentered{}", "§": r"\S{}"}
    accents = {"\u0300": "`", "\u0301": "'", "\u0302": "^", "\u0303": "~", "\u0308": '"'}
    for char in set(text):
        parts = unicodedata.normalize("NFD", char)
        if len(parts) == 2 and parts[0].isascii() and parts[1] in accents:
            symbols[char] = "{\\" + accents[parts[1]] + "{" + parts[0] + "}}"
    return text.translate(str.maketrans(symbols))


def verify_export(pdf, attachment, anonymous):
    from pypdf import PdfReader

    reader = PdfReader(pdf)
    if reader.attachments.get("proof-sources.zip") != [attachment.read_bytes()]:
        raise ValueError("Embedded ZIP differs from the checked supplement")
    metadata = reader.metadata
    if (metadata.author or "") != ("" if anonymous else "Zach Conn"):
        raise ValueError("Unexpected PDF author metadata")
    inspect_text(str(metadata).encode(), "PDF metadata", anonymous)
    for i, page in enumerate(reader.pages, 1):
        inspect_text(page.extract_text().encode(), f"PDF text on page {i}", anonymous)
        for ref in page.get("/Annots", []):
            annotation = ref.get_object()
            inspect_text(str(annotation).encode(), f"PDF annotation on page {i}", anonymous)
            if "/A" in annotation:
                inspect_text(str(annotation["/A"]).encode(), f"PDF link action on page {i}", anonymous)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--only-cached", action="store_true", help="use Tectonic's local bundle cache")
    parser.add_argument("--venue", choices=("arxiv", "tmlr"), default="arxiv")
    parser.add_argument("--anonymous", action="store_true", help="omit author identity and use the source ZIP")
    parser.add_argument("--github", action="store_true", help="generate paper-reader.md with resolved citations")
    parser.add_argument("--source-zip", action="store_true", help="also package the TeX source and inputs")
    args = parser.parse_args()
    paper_dir = Path(__file__).resolve().parent
    pandoc = os.environ.get("PANDOC", "pandoc")
    tectonic = os.environ.get("TECTONIC", "tectonic")
    env = dict(os.environ)
    env.setdefault("SOURCE_DATE_EPOCH", "0")
    if args.github:
        subprocess.run([pandoc, "paper.md", "--lua-filter=print.lua", "--citeproc", "--bibliography=references.bib",
                        "-M", "reference-section-title=References", "--to=gfm+tex_math_dollars", "--fail-if-warnings",
                        "--wrap=none", "-o", "paper-reader.md"], cwd=paper_dir, check=True)
        return
    edition = "paper" + ("-tmlr" if args.venue == "tmlr" else "") + ("-anon" if args.anonymous else "")
    output = paper_dir / (edition + ".pdf")
    with tempfile.TemporaryDirectory(prefix=".typeset-", dir=paper_dir) as temporary:
        build = Path(temporary)
        attachment = build / "proof-sources.zip"
        inspect_text((paper_dir / "paper.md").read_bytes(), "Markdown source", False)
        members = prepare_attachment(paper_dir.parent, attachment, args.anonymous)
        source, images = manuscript(pandoc, paper_dir, attachment.stat().st_size, args.venue, args.anonymous, members)
        template = "tmlr.tex" if args.venue == "tmlr" else "print.tex"
        citations = "--natbib" if args.venue == "tmlr" else "--citeproc"
        subprocess.run(
            [pandoc, "--from=json", "--to=latex-smart", "--standalone", "--number-sections",
             "--wrap=none", "--syntax-highlighting=none", f"--template={template}", citations, "--bibliography=references.bib",
             "--fail-if-warnings",
             "--lua-filter=print.lua", "-o", str(build / "paper.tex")],
            input=source, text=True, cwd=paper_dir, env=env, check=True,
        )
        tex = build / "paper.tex"
        tex.write_text(tex_characters(tex.read_text(encoding="utf-8")), encoding="utf-8")
        inspect_text(tex.read_bytes(), "generated TeX", args.anonymous)
        for image in images:
            (build / image).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(paper_dir.parent / image, build / image)
        if args.venue == "tmlr":
            (build / "references.bib").write_text(tex_characters((paper_dir / "references.bib").read_text()), encoding="utf-8")
            shutil.copyfile(paper_dir / "tmlr-style/LICENSE", build / "TMLR-LICENSE")
            for name, expected in TMLR_ASSETS.items():
                style = (paper_dir / "tmlr-style" / name).read_bytes()
                if sha256(style).hexdigest() != expected:
                    raise ValueError(f"Journal asset differs from the official distribution: {name}")
                (build / name).write_bytes(style)
        flags = ["--only-cached"] if args.only_cached else []
        subprocess.run(
            [tectonic, *flags, "--keep-logs", "--keep-intermediates", "-Z", "deterministic-mode", "paper.tex"],
            cwd=build, env=env, check=True,
        )
        for log in (*build.glob("*.log"), *build.glob("*.blg")):
            log_data = log.read_bytes()
            inspect_text(log_data, log.name, False)
            if b"Missing character:" in log_data:
                raise ValueError(f"Missing printed glyph in {log.name}")
            if re.search(rb"Citation .* undefined|There were undefined (references|citations)"
                         rb"|Warning--I didn't find a database entry", log_data):
                raise ValueError(f"Unresolved citation or cross-reference in {log.name}")
        verify_export(build / "paper.pdf", attachment, args.anonymous)
        if args.source_zip:
            extensions = {".tex", ".bib", ".bst", ".sty", ".bbl"}
            assets = {*images, attachment.name, "TMLR-LICENSE"}
            if args.venue == "arxiv":
                shutil.copyfile(paper_dir / "00README.json", build / "00README.json")
                assets.add("00README.json")
            with ZipFile(build / "tex-sources.zip", "w") as archive:
                for path in sorted(build.rglob("*")):
                    name = path.relative_to(build).as_posix()
                    if path.is_file() and (name in assets or path.suffix in extensions):
                        archive.writestr(ZipInfo(name), path.read_bytes(), compress_type=ZIP_DEFLATED)
            (build / "tex-sources.zip").replace(paper_dir / (edition + "-sources.zip"))
        if args.venue == "tmlr" and args.anonymous:
            attachment.replace(paper_dir / "paper-tmlr-anon-supplement.zip")
        (build / "paper.pdf").replace(output)
    print(output)


if __name__ == "__main__":
    main()
