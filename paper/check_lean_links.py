"""Check the released manuscript's Lean links against its reader, PDF and source ZIP."""

import argparse
from functools import cache
from io import BytesIO
from itertools import groupby
import json
import os
from pathlib import Path
import re
import subprocess
from zipfile import ZipFile

from pypdf import PdfReader

from build_pdf import verify_lean_anchor


ROOT = Path(__file__).resolve().parents[1]
LOCAL = re.compile(r"\.\./(formal/\w+\.lean)#L([1-9]\d*)")
PINNED = re.compile(r"https://github\.com/zpconn/layer-rate-bias/blob/"
                    r"([0-9a-f]{40})/(formal/\w+\.lean)#L([1-9]\d*)")


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT)


@cache
def blob(revision, path):
    return git("show", f"{revision}:{path}")


def manuscript_links(path, syntax):
    """Read Markdown links through Pandoc, retaining label and occurrence order."""
    document = json.loads(subprocess.check_output(
        [os.environ.get("PANDOC", "pandoc"), "--from", syntax, "--to=json", str(path)]
    ))
    def walk(node):
        if isinstance(node, dict):
            if node.get("t") == "Link":
                _, label, (target, _) = node["c"]
                if ".lean" in target:
                    match = LOCAL.fullmatch(target)
                    if not match:
                        raise ValueError(f"{path.name}: unexpected Lean link {target}")
                    yield (*match.groups(), label)
            else:
                for value in node.values():
                    yield from walk(value)
        elif isinstance(node, list):
            for value in node:
                yield from walk(value)
    return list(walk(document["blocks"]))


def split_pinned(uri, revision):
    match = PINNED.fullmatch(uri)
    if not match or match[1] != revision:
        raise ValueError(f"Expected a Lean link pinned to {revision}, found {uri}")
    return match[2], match[3]


def check_links(pdf, upload, reader, revision):
    manuscript = ROOT / "paper/paper.md"
    if blob(revision, "paper/paper.md") != manuscript.read_bytes():
        raise ValueError("Canonical manuscript differs from the pinned source commit")
    links = manuscript_links(manuscript, "markdown+gfm_auto_identifiers")
    if not links or manuscript_links(reader, "gfm+tex_math_dollars") != links:
        raise ValueError("Reader Lean labels, destinations or occurrence order differ from the manuscript")
    expected = [(path, line) for path, line, _ in links]
    with ZipFile(upload) as archive:
        source = archive.read("paper.tex").decode()
        supplement = archive.read("proof-sources.zip")
    tex_links = [split_pinned(uri.replace(r"\#", "#"), revision)
                 for uri in re.findall(r"\\href\{([^{}]+)\}", source) if ".lean" in uri]
    if tex_links != expected:
        raise ValueError("Upload TeX Lean destinations differ from the canonical sequence")

    document = PdfReader(pdf)
    if document.attachments.get("proof-sources.zip") != [supplement]:
        raise ValueError("Embedded and upload proof ZIPs differ")
    with ZipFile(BytesIO(supplement)) as archive:
        if archive.read("paper/paper.md") != manuscript.read_bytes():
            raise ValueError("Embedded manuscript differs from the canonical source")
        paths = {p for p in git("ls-tree", "-r", "--name-only", revision, "formal").decode().splitlines()
                 if p.endswith(".lean")}
        if sorted(paths) != sorted(p for p in archive.namelist() if p.endswith(".lean")):
            raise ValueError("The supplement and pinned repository differ in their Lean source inventory")
        for path in sorted(paths):
            pinned = blob(revision, path)
            if archive.read(path) != pinned or (ROOT / path).read_bytes() != pinned:
                raise ValueError(f"Embedded, working and pinned source bytes disagree for {path}")
    for path, line in set(expected):
        verify_lean_anchor(ROOT / path, "L" + line)

    annotations = []
    for number, page in enumerate(document.pages, 1):
        for ref in page.get("/Annots", []):
            annotation = ref.get_object()
            uri = annotation.get("/A", {}).get("/URI", "")
            if ".lean" not in uri:
                continue
            if annotation.get("/Subtype") != "/Link" or annotation["/A"].get("/S") != "/URI":
                raise ValueError(f"Page {number}: expected a URI link")
            x0, y0, x1, y1 = annotation["/Rect"]
            left, bottom, right, top = page.cropbox
            if not (left <= x0 < x1 <= right and bottom <= y0 < y1 <= top):
                raise ValueError(f"Page {number}: empty or out-of-bounds rectangle for {uri}")
            annotations.append(split_pinned(uri, revision))
    # XeLaTeX splits a link at each line break. Each occurrence needs a rectangle,
    # and the sequence of target runs must survive the split.
    expected_runs = [(key, len(list(run))) for key, run in groupby(expected)]
    actual_runs = [(key, len(list(run))) for key, run in groupby(annotations)]
    if len(expected_runs) != len(actual_runs) or any(
        key != found or rectangles < occurrences
        for (key, occurrences), (found, rectangles) in zip(expected_runs, actual_runs)
    ):
        raise ValueError("PDF annotation destinations differ from the manuscript")
    print(f"{len(expected)} manuscript, reader and upload-TeX links; {len(set(expected))} distinct "
          f"anchors in {len({p for p, _ in expected})} files; {len(annotations)} PDF link rectangles. "
          f"All {len(paths)} supplemental Lean sources match {revision}.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pdf", type=Path, default=ROOT / "paper/paper.pdf")
    parser.add_argument("--upload", type=Path, default=ROOT / "paper/paper-sources.zip")
    parser.add_argument("--reader", type=Path, default=ROOT / "paper/paper-reader.md")
    parser.add_argument("--revision", help="full source commit, defaulting to the manuscript's build pin")
    args = parser.parse_args()
    revision = args.revision or git("log", "-1", "--format=%H", "--", "paper/paper.md", "formal",
                                    "docs", "layer-rates").decode().strip()
    check_links(args.pdf, args.upload, args.reader, revision)
