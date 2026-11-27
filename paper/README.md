# Manuscript

**Steering a network’s inductive bias with the hidden-layer learning rate**

Zach Conn

The current edition is the [named preprint](paper.pdf). The same [manuscript](paper.md) and [bibliography](references.bib) generate the [GitHub reader edition](paper-reader.md). The earlier anonymous review edition and supplement are archived in the [paper-v2 release](https://github.com/zpconn/layer-rate-bias/releases/tag/paper-v2).

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
