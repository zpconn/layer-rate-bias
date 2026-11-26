# Manuscript

[**Steering a network’s inductive bias with the hidden-layer learning rate**](paper.pdf)

Zach Conn, investigator · OpenAI Codex and Anthropic Claude, research agents

The paper derives the paired prediction from the finite-grid spectrum and proves it for the discrete updates and the gradient flows. Each theorem, lemma, proposition, and corollary comes with a proof idea, a mathematical proof, and the relevant Lean declarations. Appendix B prints six complete Lean proofs that are checked against their source files at build time. [Read the manuscript on GitHub](paper.md) · [Proof guide](../docs/proof-guide.md)

## Rebuild the PDF

From the repository root, with Python 3.11 or newer, Pandoc 3.10.2 and Tectonic 0.17.0 installed, run

```sh
python3 paper/build_pdf.py
```

The command writes `paper/paper.pdf`. Once Tectonic has cached its TeX resources, `--only-cached` builds offline. The builder checks the Lean sources, numerical proof input, and verifier against the verification receipt before embedding them in the PDF. [Verification receipt](../formal/verification/receipt.json)

## Replay the proofs from the PDF

Save the PDF and open its attachments panel to extract `proof-sources.zip`. Follow the archive’s `REPLAY.md` to build the pinned Lean project and run both kernel checkers. The same proofs and verification logs are available in the repository. [Lean formalization](../formal/)
