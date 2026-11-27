# Manuscript

**Steering a network’s inductive bias with the hidden-layer learning rate**

Zach Conn

The current edition is the [named preprint](paper.pdf). The same [manuscript](paper.md) and [bibliography](references.bib) generate the [GitHub reader edition](paper-reader.md). The earlier anonymous review edition and supplement are archived in the [paper-v2 release](https://github.com/zpconn/layer-rate-bias/releases/tag/paper-v2).

## Upload paper-v3 to arXiv

Use the [released source ZIP](https://github.com/zpconn/layer-rate-bias/releases/download/paper-v3/paper-sources.zip) and paste the [ASCII metadata](arxiv-metadata.txt) into the corresponding fields. The suggested primary category is `cs.LG`, with `stat.ML` as a cross-list. If arXiv asks for endorsement, its account workflow identifies the relevant domain. [Metadata requirements](https://info.arxiv.org/help/prep.html) · [Endorsement policy](https://info.arxiv.org/help/endorsement.html)

1. On **Review Files**, confirm the processor shows `paper.tex` as the main file, XeLaTeX as the compiler and TeX Live 2025 as the distribution. Check that `proof-sources.zip` appears as one file at the upload root.
2. Download the PDF that arXiv processed. Run the command below from the repository root, substituting the downloaded PDF's path. It lists attachments with Poppler’s `pdfdetach` when available and compares the embedded proof ZIP byte for byte with the upload archive.
3. Read the processed PDF before submitting. The author is responsible for its content, including work produced with AI assistance. An announced version remains accessible after a withdrawal. [Code of conduct](https://info.arxiv.org/help/policies/code_of_conduct.html) · [Withdrawal policy](https://info.arxiv.org/help/withdraw.html)

```sh
python3 paper/check_arxiv.py paper/paper-sources.zip --preview /path/to/arxiv-preview.pdf
```

The released proof ZIP contains 4,614,906 bytes. Its SHA-256 is `b565b1707fc7928eb0b86f2c6049923d98c34a10fdb0e8ce4912c8c831e71f83`. If arXiv expands the ZIP or the preview loses the attachment, use an embed-free variant with this digest and the archived release identifier in Section 10. Keep all compiler inputs outside `anc/`. Release commit `394f4f70bbb60676416846f2d145debbbaa372c8` records the complete upload; its sources are at `ac6b4f59c68069ebed08b5ccc2800a86f895635b`. [Software Heritage archive](https://archive.softwareheritage.org/swh:1:rev:394f4f70bbb60676416846f2d145debbbaa372c8/) · [Ancillary-file guidance](https://info.arxiv.org/help/ancillary_files.html)

## Rebuild the preprint

Use Python 3.11 or newer with `pypdf==6.7.5`, Pandoc 3.10.2, Git and Tectonic 0.17.0. Run from the repository root.

```sh
python3 paper/build_pdf.py --source-zip
python3 paper/build_pdf.py --github
```

The first command produces `paper/paper.pdf` and the [arXiv source archive](paper-sources.zip). The second regenerates `paper/paper-reader.md`. Both editions resolve the bibliography with citeproc. After Tectonic caches its TeX resources, `--only-cached` builds offline.

## Check the arXiv source archive

The archive contains `paper.tex`, its figures, `proof-sources.zip` and `00README.json`. The manifest selects XeLaTeX on TeX Live 2025 and identifies the proof supplement as an input to the compiler. The xdvipdfmx driver embeds that file in the PDF. [arXiv compiler specification](https://info.arxiv.org/help/00README.html)

The tested Linux installation used TeX Live 2025’s `scheme-basic` plus `xetex`, `dejavu`, `lm-math`, `booktabs` and `xurl` with their package dependencies. The two font packages supply the DejaVu Sans Mono and Latin Modern Math files used for Lean listings. With this distribution’s `xelatex` on `PATH` and the same Python requirements, run

```sh
python3 paper/check_arxiv.py paper/paper-sources.zip
```

The check extracts the archive in a fresh directory, compiles it with shell escape disabled, checks the author and PDF text, and compares the embedded supplement with the complete ZIP supplied in the archive.

## Replay the artifacts

Named PDF links locate each source at the latest Git commit affecting the manuscript, formalization, experiments or proof guides. For uncommitted targets, the paper gives file locations inside `proof-sources.zip`. The builder checks Lean anchors, exact source listings, PDF text, links and metadata.

Extract `proof-sources.zip` from the PDF attachments panel. Its `REPLAY.md` gives the commands for replay through Lean’s kernel checker in standard and paranoid modes. Its `layer-rates/` directory contains simulation inputs, code, results and instructions. The builder checks the formal sources, numerical proof input and verifier against the [verification receipt](../formal/verification/receipt.json).
