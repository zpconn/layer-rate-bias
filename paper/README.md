# Manuscript

**Steering a network’s inductive bias with the hidden-layer learning rate**

Zach Conn

Read the [preprint](paper.pdf), the [anonymous TMLR edition](paper-tmlr-anon.pdf), or the [GitHub reader edition](paper-reader.md). The [manuscript source](paper.md) and [bibliography](references.bib) generate all three.

## Rebuild

Use Python 3.11 or newer with `pypdf==6.7.5`, Pandoc 3.10.2, Git and Tectonic 0.17.0. Run from the repository root.

```sh
python3 paper/build_pdf.py
python3 paper/build_pdf.py --venue tmlr --anonymous
python3 paper/build_pdf.py --github
```

The anonymous build also writes `paper/paper-tmlr-anon-supplement.zip` for separate upload. The three manuscript outputs are `paper/paper.pdf`, `paper/paper-tmlr-anon.pdf` and `paper/paper-reader.md`. After Tectonic caches the required TeX resources, `--only-cached` builds offline. The optional `--source-zip` packages the generated XeLaTeX source, graphics and embedded supplement beside the PDF. The preprint and reader process Pandoc citations with citeproc. The TMLR edition uses natbib with the journal’s bibliography style. The style files in `tmlr-style/` come unchanged from the journal’s [template repository](https://github.com/JmlrOrg/tmlr-style-file/tree/7bf90efe3a0debbba703c05c43f3ff7e4d4a2992).

Named PDF links use the latest Git commit affecting the manuscript, formalization, experiments or proof guides. For uncommitted targets and anonymous builds, the paper gives file locations inside `proof-sources.zip`. Extract it alongside the PDF to access those paths. The build checks line anchors against Lean declarations and printed listings against their source text. It also compares the embedded ZIP with the checked supplement and scans the PDF’s text, links and metadata.

## Replay the artifacts

Extract `proof-sources.zip` from the PDF attachments panel. Its `REPLAY.md` gives the commands for replay through Lean’s kernel checker in standard and paranoid modes. Its `layer-rates/` directory contains simulation inputs, code, results and instructions. The builder checks the formal sources, numerical proof input and verifier against the [verification receipt](../formal/verification/receipt.json).
