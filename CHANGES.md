# Release history

## paper-v3 · arXiv preprint

This revision follows the review of `paper-v2` at commit `9ecb601e86e50505850d24244a63482039fd0a12`. The author selected the named arXiv edition for this revision. The anonymous TMLR files belong to the earlier release.

| Review item | Change |
| --- | --- |
| R1 | Section 4.1 and Table 6 give all 25 adjacent-width exponents with pointwise intervals from 4,096 bootstrap draws that preserve seed pairing across widths. Table 5 identifies its single-power-law assumption. The abstract reports the measured width range and the curvature visible in local estimates. The optional two-term fit was omitted because these data leave the asymptotic exponent open. |
| R2 | Appendix C now identifies the nine Lean declarations for Theorem 1, including the rate factor, width, deadline and its inputs, residual norm, coefficient and guarantee. The update-segment derivative cited in Section 5 is public and directly importable. |
| R3 | The reader-facing text identifies the primary sample, integrator and theorem directly. The named edition cites the current release tag; historical comparisons are recorded here. |
| R4 | The named upload archive includes an arXiv compiler manifest selecting XeLaTeX and TeX Live 2025, all figures and the embedded proof supplement. The archive check performs a clean native XeLaTeX build and compares the PDF attachment with the uploaded ZIP. |
| R5 | Fixed score margins use Γ. The notation for rate scales, density bounds, layer magnitudes, kernel errors and tails is now distinguished in the statements and their proofs. |
| R6 | Rendered source notes identify proofs, Lean declarations, data and verification records consistently in the preprint and GitHub reader. |
| R7 | Related work immediately follows the introduction. Section 4.2 compares unit-step GD with flow at two widths, both on the same 24 seeds and against the full primary flow sample. |
| R8 | Anonymous-edition wording was outside the author's selected venue for this revision. |

The source commit is `ac6b4f59c68069ebed08b5ccc2800a86f895635b`. Native XeLaTeX from TeX Live 2025 compiled the complete upload archive and embedded the 4,614,906-byte supplement without changing a byte (SHA-256 `b565b1707fc7928eb0b86f2c6049923d98c34a10fdb0e8ce4912c8c831e71f83`). Repeated builds reproduced the preprint, upload ZIP and GitHub reader byte for byte. Both kernel modes accepted the fresh proof export with SHA-256 `1bbfa7c246ab3672f35e0781fb9353f3ef581fc327d51070dea0c4ceb47ce8f9`. [Verification receipt](formal/verification/receipt.json)

## paper-v2 · changes since paper-v1

The comparison point is commit `34cc12b89d7b5b60853c8e74f1df75f9087e82e0`. Section numbers below refer to the revised manuscript.

### Manuscript and submission files

| Review item | Change |
| --- | --- |
| P0.1 | Zach Conn is the sole author. The author confirmed reviewing the revised manuscript and accepting responsibility for it. The contribution statement describes the human direction and the use of Codex and Claude in proof development, formalization, experiments and writing. |
| P0.2 | The named and anonymous editions share one Markdown source and bibliography. The TMLR edition uses the upstream style and bibliography style, an empty PDF author field, and supplementary file locations for the implementation and proof links. |
| P0.3 | The introduction starts from exact interpolation and conditional support, motivates per-layer rates, and presents the contributions and a mechanism figure. The related-work section covers all nine requested topics. The bibliography audit gives the primary source and scope of each citation, including the editions used when suggested references lacked verified identifiers. |
| P0.4 | The introduction gives the first admissible odd grids for the unit-step and flow fitting estimates, the implied widths, and an explicit finite-grid alternative. Section 5 identifies where width controls motion and kernel concentration. |
| P0.5 | Appendix C maps the definitions of the data, seed law, learners, endpoints, errors and events to Lean. It distinguishes the closed-form definition of the population mean from the angular integral theorem and identifies the existence theorems and trusted components. |
| P0.6 | The formal tree follows the paper's transitive import closure. Superseded and earlier-phase sources remain in the immutable baseline. The replay checks both modes of Lean's kernel checker. The proof attachment includes the Apache-2.0 license, experiment programs and frozen data. The builder validates Lean anchors and exact listings. The revised release uses a fresh tag so the reviewed baseline remains retrievable. |
| P1.1 | Section 1 motivates the comparison with full support at a first fit. Sections 2–3 and Appendix A use the single-rate schedules, exact cotangent formulas, flow and GD Gaussian laws, broader equal-rate moment theorem, independent-training contrast and first-cosine results. The new paired GD proof gives one event and the same stopping step for both rates at all widths above the design. |
| P1.2 | The coordinate change rescales both hidden weights and their initial covariance. The Lean development checks the scaled output, GD update, flow correspondence and transformed Gaussian law. |
| P1.3 | The paper gives a strictly positive exact coefficient for any ordered positive multiplier pair and its explicit limit. It treats common-seed trained flows throughout the rate interval and states the single-rate Gaussian limit. |
| P1.4 | The kernel mechanism follows the model in Section 2. The figure identifies an alias on the three-point grid. The quadrature derivation gives the weight per node for a general residual. |
| P1.5 | Section 2 gives the cotangent formulas, eight numerical coefficients, the limit, and a Lean-checked expansion through the sixth inverse power with a certified eighth-order remainder. It retains the explicit uniform remainder inequality, whose finite-grid role differs from an asymptotic expansion. |
| P1.6 | The main text distinguishes a high-probability prediction from a second-moment claim. It gives two-sided probability estimates for the particular escaping box and distinguishes the equal-rate capped and unit-step Gaussian laws from the rare-seed divergence for the paired observable. |
| P1.7 | Section 4 includes sign, margin, calibration and refinement tables from the original records. It reports shared seed prefixes, empirical discretization errors and the scope of the Lean arithmetic checks. The expanded width sweep, optimizer comparisons and antisymmetric control have separate frozen outputs. The fixed-seed joint bootstrap resamples whole seed trajectories across widths. Optional changes to optimizer, batching and parametrization beyond the listed controls were omitted to keep the experiment tied to the training rules in the theorems. |
| P1.8–9 | The notation table and figure axes use the same deficit and scaled gap. The GD trajectory proof distinguishes the contraction factor, residual bound and neuron energy. The introduction distinguishes the off-grid extension from bias averaged over seeds. |
| P1.10–11 | Proposition 2.2 treats general continuous targets. Proposition 2.4 gives the Fourier coefficients for all integer frequencies and specializes the zero mode to quadrature. The paper identifies the teacher-specific moments, the target quadrature error and the limits of nonlinear tracking. |
| P2 | The abstract gives the prediction and experimental regime. The manuscript includes the effect sizes at three and 31 nodes, the scope of the training model, explicit toolchain versions and a source-checked bibliography. The width sweep figure and paired scatter use the same colors and symbols as the text. |

### Distribution

The author chose the tagged GitHub release as the public archive for this revision. The author has no Zenodo account, and this release has no Zenodo DOI.

The public release does not constitute a journal or arXiv submission. TMLR's editorial policy permits assistive use and makes the author responsible for the content. Its FAQ also gives an expectation about the human origin of ideas, claims and results. The contribution statement describes how this work was actually produced. Editorial eligibility remains a decision for the journal. [Editorial policy](https://jmlr.org/tmlr/editorial-policies.html) · [Author FAQ](https://jmlr.org/tmlr/faq.html)

### Verification of this release

The clean build covered 145 Lean libraries. The closed export contained 5,428 safe project declarations, including 4,511 theorems. The manuscript links identify 209 distinct theorem declarations for the axiom audit. Standard and paranoid kernel replay both passed for export SHA-256 `eb21895b80bfe0cff6c071f5841aef3c5ab5e2c4f6fbd40a5b9659f189661566`. [Receipt](formal/verification/receipt.json)

Both 41-page PDFs and both source ZIPs matched byte for byte across two offline builds. Recompiling the extracted named TeX archive also reproduced the preprint PDF byte for byte. The named and anonymous supplements each contain 189 files. The anonymous edition has an empty PDF author field. Its separate supplement matches its embedded ZIP byte for byte.

All 38 bibliography entries have a DOI or arXiv identifier, are cited in the manuscript, and have an opened-source claim audit. Re-running the original direct simulator reproduced its 472 primary and refinement records and 27 boundary records byte for byte. The expanded sweep covers 30 designs and 3,216 natural pairs. [Reference audit](paper/references-check.md) · [Experiment methods and results](layer-rates/README.md)
