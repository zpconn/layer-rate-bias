# Changes since paper-v1

The comparison point is commit `34cc12b89d7b5b60853c8e74f1df75f9087e82e0`. Section numbers below refer to the revised manuscript.

## Manuscript and submission files

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

## Distribution

The author chose the tagged GitHub release as the public archive for this revision. The author has no Zenodo account, and this release has no Zenodo DOI.

The public release does not constitute a journal or arXiv submission. TMLR's editorial policy permits assistive use and makes the author responsible for the content. Its FAQ also gives an expectation about the human origin of ideas, claims and results. The contribution statement describes how this work was actually produced. Editorial eligibility remains a decision for the journal. [Editorial policy](https://jmlr.org/tmlr/editorial-policies.html) · [Author FAQ](https://jmlr.org/tmlr/faq.html)
