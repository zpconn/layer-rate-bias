"""Compile an arXiv upload archive or check the attachment in its downloaded preview."""

import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
from zipfile import ZipFile

from build_pdf import verify_export


SUPPLEMENT = "proof-sources.zip"


def check_upload(archive):
    names = archive.namelist()
    if [name for name in names if name.lower().endswith(".zip")] != [SUPPLEMENT]:
        raise ValueError("The upload must contain exactly one nested ZIP, named proof-sources.zip")
    if any(names.count(required) != 1 for required in ("paper.tex", "00README.json")):
        raise ValueError("Expected exactly one paper.tex and 00README.json at the upload root")
    config = json.loads(archive.read("00README.json"))
    if (config["spec_version"], config["process"]["compiler"], config["texlive_version"]) != (1, "xelatex", 2025):
        raise ValueError("Expected arXiv's version 1 XeLaTeX configuration for TeX Live 2025")
    entries = sorted((entry["filename"], entry["usage"]) for entry in config["sources"])
    if entries != [("paper.tex", "toplevel"), (SUPPLEMENT, "include")]:
        raise ValueError("The arXiv manifest must select paper.tex and include proof-sources.zip")
    return archive.read(SUPPLEMENT)


def check_pdf_attachment(pdf, original):
    from pypdf import PdfReader
    from pypdf.generic import EmbeddedFile

    if pdfdetach := shutil.which("pdfdetach"):
        listing = subprocess.check_output([pdfdetach, "-list", str(pdf.resolve())], text=True,
                                          env={**os.environ, "LC_ALL": "C"}).strip()
        print(listing)
        if not re.fullmatch(r"1 embedded files?\n1: proof-sources\.zip", listing):
            raise ValueError("pdfdetach did not find exactly one attachment named proof-sources.zip")
    reader = PdfReader(pdf)
    files = list(reader.attachment_list)
    for page in reader.pages:
        for ref in page.get("/Annots", []):
            annot = ref.get_object()
            if annot.get("/Subtype") == "/FileAttachment":
                spec = annot["/FS"]
                files.append(EmbeddedFile(spec.get("/UF") or spec["/F"], spec))
    if [item.name for item in files] != [SUPPLEMENT]:
        raise ValueError(f"Expected one {SUPPLEMENT} attachment, found {[item.name for item in files]}")
    content = files[0].content
    digest = sha256(content).hexdigest()
    if content != original:
        raise ValueError(f"Attachment SHA-256 {digest} differs from upload SHA-256 {sha256(original).hexdigest()}")
    print(f"One {SUPPLEMENT} attachment matches the upload byte for byte: "
          f"{len(content):,} bytes, SHA-256 {digest}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path, help="source ZIP used for the upload")
    parser.add_argument("--preview", type=Path, help="inspect the downloaded arXiv PDF without running XeLaTeX")
    args = parser.parse_args()
    with ZipFile(args.archive) as archive:
        original = check_upload(archive)
        if args.preview:
            check_pdf_attachment(args.preview, original)
            return
    compiler = "xelatex"
    with tempfile.TemporaryDirectory(prefix="arxiv-xelatex-") as tmp:
        build = Path(tmp)
        with ZipFile(args.archive) as archive:
            archive.extractall(build)
        version = subprocess.check_output([compiler, "--version"], text=True).splitlines()[0]
        if not re.search(r"\bTeX Live 2025\b", version):
            raise ValueError(f"Expected TeX Live 2025, found {version}")
        print(version, flush=True)
        rerun = re.compile(r"Rerun to get|Rerun to resolve|Label\(s\) may have changed|File .+ has changed\.", re.I)
        for _ in range(3):
            result = subprocess.run([compiler, "-no-shell-escape", "-interaction=nonstopmode",
                                     "-halt-on-error", "paper.tex"], cwd=build, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT)
            if result.returncode:
                raise RuntimeError(result.stdout.decode(errors="replace")[-4000:])
            log = (build / "paper.log").read_text(errors="replace")
            if not rerun.search(log):
                break
        else:
            raise ValueError("XeLaTeX still requests another pass")
        if re.search(r"undefined (?:references|citations)|Missing character:", log, re.I):
            raise ValueError("Unresolved text, references or citations after XeLaTeX compilation")
        attachment = build / "proof-sources.zip"
        if attachment.read_bytes() != original:
            raise ValueError("The compiler changed its proof supplement input")
        verify_export(build / "paper.pdf", attachment)
        check_pdf_attachment(build / "paper.pdf", original)


if __name__ == "__main__":
    main()
