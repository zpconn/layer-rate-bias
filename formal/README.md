# Lean formalization

The project proves the paired learning-rate prediction directly from Gaussian initialization, the network equations and the training rules. The construction uses an odd grid of size $N$ on the circle, width $N^{32}$ and a fixed training endpoint. The two networks share initial weights and a readout rate of one. Their hidden rates are $1/2$ and $2$. In the Lean statements, `n+1` denotes $N$. [Paper](../paper/paper.pdf) · [Proof guide](../docs/proof-guide.md)

## Main declarations

Write $X$ for one minus the initial mean prediction on the grid. Let $\Delta$ be the slow-minus-fast difference of the final means around the circle. If the initialization-averaged tangent kernel is held fixed until it fits the grid, its predicted gap is exactly $c_NX/N^2$, where $c_N\to\pi^2/40$. The theorems compare the actual $\Delta$ to that prediction. A fit means grid RMS error at most $N^{-3}$.

| Result | Lean declaration |
| --- | --- |
| The network’s simultaneous full-batch GD update, with zero ReLU derivative at a kink | [iterate](CircleWeightedStep.lean#L30) |
| For every odd grid, joint GD fitting and tracking after a common deadline at width of order $N^{16}$ | [paired_gd](CircleRateDial.lean#L53) |
| Fourier coefficients of the full tangent-kernel interpolant | [interpolation](CircleFourierInterpolant.lean#L39) |
| The eighth-order scaled coefficient remainder and its limit | [expansion](CircleCoefficientExpansion.lean#L111) |
| For GD, joint fitting and correct ordering with high probability, the limiting gap in probability, and divergence of the unscaled mean-square error | [paired_discrete_gradient_descent](CirclePairedGDTheorem.lean#L59) |
| Existence of measurably selected global Clarke gradient flows for the network | [CircleFlowConstruction](CircleFlowConstruction.lean#L75) |
| For flow, both fits and a population-gap bound on one measurable event | [common_event](CirclePairedTheorem.lean#L41) |
| For flow, RMS error over all seeds, ordering error probability, and a two-term expansion of $c_N$ | [all_seed_bounds](CirclePairedTheorem.lean#L209) |
| Leading RMS error constant for flow with the limiting slope $\pi^2/40$ | [leading_rms](CirclePairedSecondOrder.lean#L93) |

For gradient flow, the expected slow-minus-fast population shift has a positive leading term and an explicit second-order correction. [Finite-grid signed mean](CirclePairedTheorem.lean#L234) · [Signed mean expansion](CirclePairedTheorem.lean#L264)

The GD proof splits into a typical-seed trajectory estimate and a lower bound from rare initial weights. Every finite iterate has finite moments. For flow, the estimate integrates over all initial weights and holds for every admissible measurable pair. The paper’s equal-rate companion compares bias, variance and fitting at three endpoints. [GD proof](../docs/paired-discrete-gd.md) · [Flow tracking](CircleSharpMoments.lean#L159) · [Equal-rate results](../docs/from-first-principles.md#how-long-you-train-also-matters)

## Scope of the formal artifact

Appendix C maps the finite-grid GD theorem to the Lean definitions of its width, common deadline, training error and predicted slope. [Theorem 1 statement audit](../paper/paper.md#finite-grid-gradient-descent-theorem-1)

The formal tree contains the local import closure of the manuscript's source links. `PaperAudit.lean` imports these modules and prints the axioms of the theorems at the cited lines, including private lemmas. The verifier checks this list against the Markdown when the manuscript is present and checks the import closure on every replay. To update the audit after changing a citation, run `python3 verify.py --write-paper-audit` in this directory. [Paper audit](PaperAudit.lean)

## Build and replay

From this directory with Git, Python 3.11 or newer, and elan installed, run

```sh
lake exe cache get
python3 verify.py --report .lake/replay
```

The verifier rebuilds the paper’s module closure, inventories every project declaration within it and exports the dependency closure of each safe declaration. It replays the same export through Lean’s kernel checker in standard and paranoid modes. It records the allowed axioms, pinned revisions, and hashes of the source, data, and proof export. To compile without replaying the export, run `lake build --wfail` after the cache download. [Verifier](verify.py) · [Pinned toolchain](lean-toolchain) · [Dependency revisions](lake-manifest.json)

The recorded verification covers 5,428 safe declarations, including 4,511 theorems, in the paper’s 145-module import closure. The theorem-level audit lists the axioms of the 233 distinct theorems cited in the manuscript. The inventory gives the dependencies on foundational axioms for each named declaration, including private proofs. [Verification receipt](verification/receipt.json) · [Declaration inventory](verification/declarations.tsv) · [Build log](verification/build.log) · [Standard checker](verification/kernel.log) · [Paranoid checker](verification/paranoid.log)
