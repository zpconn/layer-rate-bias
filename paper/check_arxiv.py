"""Compile the upload archive in a clean directory and check its PDF attachment."""

import argparse
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess
import tempfile
from zipfile import ZipFile

from build_pdf import verify_export


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="arxiv-xelatex-") as tmp:
        build = Path(tmp)
        with ZipFile(args.archive) as archive:
            original = archive.read("proof-sources.zip")
            archive.extractall(build)
        config = json.loads((build / "00README.json").read_text())
        compiler = config["process"]["compiler"]
        year = config["texlive_version"]
        if (config["spec_version"], compiler, year) != (1, "xelatex", 2025):
            raise ValueError("Expected arXiv's version 1 XeLaTeX configuration for TeX Live 2025")
        entries = {entry["filename"]: entry["usage"] for entry in config["sources"]}
        if entries != {"paper.tex": "toplevel", "proof-sources.zip": "include"}:
            raise ValueError("The arXiv manifest must select paper.tex and include proof-sources.zip")
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
        verify_export(build / "paper.pdf", attachment, anonymous=False)
        print(f"Embedded proof-sources.zip matches {attachment.stat().st_size:,} bytes, "
              f"SHA-256 {sha256(original).hexdigest()}")


if __name__ == "__main__":
    main()
