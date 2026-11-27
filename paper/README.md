# Manuscript

**Steering a network’s inductive bias with the hidden-layer learning rate**

Zach Conn

[Read the PDF](paper.pdf) · [Read on GitHub](paper-reader.md) · [Manuscript source](paper.md) · [Bibliography](references.bib)

## Upload to arXiv

Use the [source archive](paper-sources.zip) and paste the [ASCII metadata](arxiv-metadata.txt) into the corresponding fields. The suggested primary category is `cs.LG`, with `stat.ML` as a cross-list. If arXiv asks for endorsement, its account workflow identifies the relevant domain. [Metadata requirements](https://info.arxiv.org/help/prep.html) · [Endorsement policy](https://info.arxiv.org/help/endorsement.html)

1. On **Review Files**, confirm the processor shows `paper.tex` as the main file, XeLaTeX as the compiler and TeX Live 2025 as the distribution. Check that `proof-sources.zip` appears as one file at the upload root.
2. Download the PDF that arXiv processed. Run the command below from the repository root, substituting the downloaded PDF's path. It lists attachments with Poppler’s `pdfdetach` when available and compares the embedded proof ZIP byte for byte with the upload archive.
3. Read the processed PDF before submitting. The author is responsible for its content, including work produced with AI assistance. An announced version remains accessible after a withdrawal. [Code of conduct](https://info.arxiv.org/help/policies/code_of_conduct.html) · [Withdrawal policy](https://info.arxiv.org/help/withdraw.html)

```sh
python3 paper/check_arxiv.py paper/paper-sources.zip --preview /path/to/arxiv-preview.pdf
```

## Rebuild the preprint

Use Python 3.11 or newer with `pypdf==6.7.5`, Pandoc 3.10.2, Git and Tectonic 0.17.0. Run from the repository root.

```sh
python3 paper/build_pdf.py --source-zip
python3 paper/build_pdf.py --github
```

The first command produces `paper/paper.pdf` and the [arXiv source archive](paper-sources.zip). The second regenerates `paper/paper-reader.md`. Both formats resolve the bibliography with citeproc. After Tectonic caches its TeX resources, `--only-cached` builds offline.

## Check the arXiv source archive

The archive contains `paper.tex`, its figures, `proof-sources.zip` and `00README.json`. The manifest selects XeLaTeX on TeX Live 2025 and identifies the proof supplement as an input to the compiler. The xdvipdfmx driver embeds that file in the PDF. [arXiv compiler specification](https://info.arxiv.org/help/00README.html)

The tested Linux installation used TeX Live 2025’s `scheme-basic` plus `xetex`, `dejavu`, `lm-math`, `booktabs` and `xurl` with their package dependencies. The two font packages supply the DejaVu Sans Mono and Latin Modern Math files used for Lean listings. With this distribution’s `xelatex` on `PATH` and the same Python requirements, run

```sh
python3 paper/check_arxiv.py paper/paper-sources.zip
```

The check extracts the archive in a fresh directory, compiles it with shell escape disabled, checks the author and PDF text, and compares the embedded supplement with the complete ZIP supplied in the archive.

## Replay the artifacts

The PDF links to source files at the commit used for the build. For uncommitted targets, the paper gives file locations inside `proof-sources.zip`. The builder checks Lean anchors and compares the six printed listings with their source lines. To check every Lean link in the PDF, GitHub reader and arXiv archive against the manuscript and its pinned repository sources, run

```sh
python3 paper/check_lean_links.py
```

Extract `proof-sources.zip` from the PDF attachments panel. Its `REPLAY.md` gives the commands for replay through Lean’s kernel checker in standard and paranoid modes. Its `layer-rates/` directory contains simulation inputs, code, results and instructions. The builder checks the formal sources, numerical proof input and verifier against the [verification receipt](../formal/verification/receipt.json).
