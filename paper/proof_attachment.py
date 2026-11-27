"""Bundle the manuscript's Lean sources and verification record for the PDF."""

from hashlib import sha256
import json
import re
from pathlib import Path
from zipfile import ZIP_STORED, ZipFile, ZipInfo


REPLAY = b"""# Replay the Lean proofs

The formal directory contains the project's Lean sources and the Lake manifest
that pins its dependencies. Open formal/CirclePairedGDTheorem.lean for the
discrete gradient descent result and formal/CirclePairedTheorem.lean for
gradient flow. The repository-relative source paths in the paper also apply
inside this archive.

To replay the proofs, extract the entire archive. With Git, elan, and Python
3.11 or newer installed, run these commands from the extracted directory.
The first Lake invocation needs access to any pinned dependencies absent
from the local cache.

    cd formal
    lake exe cache get
    python3 verify.py --report .lake/replay

The verifier rebuilds the project, inventories the declarations and their
axioms, exports the dependencies of every safe project declaration, and replays
the export with leanchecker and leanchecker-paranoid. Compare the resulting
.lake/replay/receipt.json with verification/receipt.json. The original build
log, axiom audits, checker logs, and declaration inventory are in verification/.
"""


PROCESS_TEXT = re.compile(rb"research agents|as an AI language model|TODO from (?:Codex|Claude)|<codex_internal_context", re.I)


def inspect_text(data, name):
    match = PROCESS_TEXT.search(data)
    if match:
        raise ValueError(f"Export contains {match[0]!r} in {name}")


def prepare_attachment(repo_root: Path, dest: Path) -> set[str]:
    """Write a reproducible source ZIP after checking every input hash in the receipt."""
    report = Path("formal/verification")
    receipt_name = report / "receipt.json"
    files = {receipt_name: (repo_root / receipt_name).read_bytes(), Path("REPLAY.md"): REPLAY}
    receipt = json.loads(files[receipt_name])
    hashes = {Path("formal") / name: digest for name, digest in receipt["source_sha256"].items()}
    hashes.update({Path(name): digest for name, digest in receipt["data_sha256"].items()})
    hashes[Path("formal/verify.py")] = receipt["verifier_sha256"]

    for path, expected in hashes.items():
        if path.is_absolute() or ".." in path.parts or ".lake" in path.parts:
            raise ValueError(f"Unexpected path in proof receipt: {path}")
        data = (repo_root / path).read_bytes()
        if sha256(data).hexdigest() != expected:
            raise ValueError(f"Proof input differs from verification receipt: {path}")
        files[path] = data

    for name in (
        "build.log", "kernel.log", "paranoid.log", "declarations.tsv", "PaperAudit.log",
    ):
        path = report / name
        files[path] = (repo_root / path).read_bytes()

    # Relative manuscript references can also be followed after extraction.
    for pattern in ("LICENSE", "layer-rates/*.py", "layer-rates/*.cpp", "layer-rates/*.csv", "layer-rates/*.md",
                    "layer-rates/*.png", "docs/*.md", "paper/majority.py", "paper/*.png", "paper/references.bib"):
        for source in repo_root.glob(pattern):
            files[source.relative_to(repo_root)] = source.read_bytes()
    # Include the citation targets so the verifier can match PaperAudit to the manuscript.
    files[Path("paper/paper.md")] = (repo_root / "paper/paper.md").read_bytes()
    if Path("LICENSE") not in files:
        raise ValueError("The source supplement needs the repository LICENSE")
    for path, data in files.items():
        inspect_text(data, str(path))

    # The PDF stream compresses the ZIP. Stored entries also keep ZIP hashes
    # independent of the zlib version, file timestamps, and executable bits.
    with ZipFile(dest, "w", compression=ZIP_STORED) as archive:
        for path in sorted(files, key=Path.as_posix):
            entry = ZipInfo(path.as_posix(), date_time=(1980, 1, 1, 0, 0, 0))
            entry.create_system = 3
            entry.external_attr = 0o100644 << 16
            archive.writestr(entry, files[path])
    return {path.as_posix() for path in files}
