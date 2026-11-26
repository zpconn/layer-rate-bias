"""Typeset paper/paper.pdf with its receipt-verified Lean source attachment."""

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
from urllib.parse import urljoin, urlsplit

from proof_attachment import prepare_attachment


REPOSITORY = "https://github.com/zpconn/layer-rate-bias/blob/"
# This tag identifies the release containing the PDF and its audited Lean sources.
PROOF_REVISION = "paper-v1"


def take_labeled_paragraph(blocks, label):
    """Read the content following a bold Markdown label, preserving inline math."""
    line = blocks[0]["c"] if blocks and blocks[0]["t"] == "Para" else []
    if len(line) >= 3 and line[0]["t"] == "Strong" and line[1]["t"] == "Space":
        heading = "".join(word.get("c", " ") for word in line[0]["c"])
        if heading == label:
            blocks.pop(0)
            return {"t": "MetaInlines", "c": line[2:]}
    raise ValueError(f"Expected a manuscript paragraph starting with **{label}**")


def pdf_link(target):
    """Resolve repository links for a standalone PDF and pin the audited proofs."""
    url = urlsplit(target)
    if url.netloc and not url.scheme:
        return "https:" + target
    if url.scheme or not url.path:
        return target
    if url.path in {"paper.md", "./paper.md"} and url.fragment and not url.query:
        return "#" + url.fragment
    resolved = urljoin(REPOSITORY + "main/paper/", target)
    return resolved.replace(REPOSITORY + "main/formal/", REPOSITORY + PROOF_REVISION + "/formal/", 1)


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


def manuscript(pandoc, paper_dir, attachment_size):
    document = json.loads(subprocess.check_output([pandoc, "--from=markdown+gfm_auto_identifiers", "paper.md", "--to=json"], cwd=paper_dir))
    blocks = document["blocks"]
    verify_lean_listings(blocks, paper_dir)
    if not blocks or blocks[0]["t"] != "Header" or blocks[0]["c"][0] != 1:
        raise ValueError("Expected the manuscript title as the first level-one heading")
    meta = document["meta"]
    meta["title"] = {"t": "MetaInlines", "c": blocks.pop(0)["c"][2]}
    credits = []
    for role in ("Investigator", "Research agents"):
        credits.append({"t": "MetaMap", "c": {
            "role": {"t": "MetaString", "c": role},
            "names": take_labeled_paragraph(blocks, role),
        }})
    meta["credits"] = {"t": "MetaList", "c": credits}
    meta["investigator"] = credits[0]["c"]["names"]
    meta["abstract"] = take_labeled_paragraph(blocks, "Abstract.")
    meta["proof-source-size"] = {"t": "MetaString", "c": str(attachment_size)}

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
                target[0] = pdf_link(target[0])
            nodes.extend(node.values())
    return json.dumps(document)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--only-cached", action="store_true", help="use Tectonic's local bundle cache")
    args = parser.parse_args()
    paper_dir = Path(__file__).resolve().parent
    pandoc = os.environ.get("PANDOC", "pandoc")
    tectonic = os.environ.get("TECTONIC", "tectonic")
    env = dict(os.environ)
    env.setdefault("SOURCE_DATE_EPOCH", "0")
    output = paper_dir / "paper.pdf"
    with tempfile.TemporaryDirectory(prefix=".typeset-", dir=paper_dir) as temporary:
        build = Path(temporary)
        attachment = build / "proof-sources.zip"
        prepare_attachment(paper_dir.parent, attachment)
        source = manuscript(pandoc, paper_dir, attachment.stat().st_size)
        subprocess.run(
            [pandoc, "--from=json", "--to=latex-smart", "--standalone", "--number-sections",
             "--wrap=none", "--syntax-highlighting=none", "--template=print.tex",
             "--lua-filter=print.lua", "-o", str(build / "paper.tex")],
            input=source, text=True, cwd=paper_dir, env=env, check=True,
        )
        shutil.copyfile(paper_dir / "paired-ordering.png", build / "paired-ordering.png")
        flags = ["--only-cached"] if args.only_cached else []
        subprocess.run(
            [tectonic, *flags, "-Z", "deterministic-mode", "paper.tex"],
            cwd=build, env=env, check=True,
        )
        (build / "paper.pdf").replace(output)
    print(output)


if __name__ == "__main__":
    main()
