# Paired gradient-flow experiments

Two ReLU networks share one Gaussian initialization and train on the same $N$ equally spaced circle points with labels $1+\cos u$. The readout rate is one in both networks. The hidden rate is $1/2$ in one and $2$ in the other. Let $X$ be one minus the initial grid mean, and let $D$ be $N^2$ times the final slow-minus-fast difference in whole-circle means. The theory predicts $D\approx c_N X$, where $c_N$ is computed from the grid before training. These experiments test the prediction at finite widths by numerically integrating gradient flow. [Paper](../paper/paper.pdf) · [Derivation](../docs/from-first-principles.md)

## Figure 1

At $N=3$ and width 32,768 the predicted slope is $c_3\approx 0.239159$. On 48 ordinary Gaussian draws, the deficit predicts all 48 orderings. Always predicting a higher mean for the slower run gives 45 correct. On 48 independent draws conditioned on $X<0$, the faster run finishes higher in 46. The two samples estimate success under their respective initialization laws. [Paper figure](../paper/paired-ordering.png) · [Comparison at widths 512 and 32,768](paired-contrast.png) · [Width-comparison script](plot_pairs.py)

## Data and methods

| File | Contents |
| --- | --- |
| [paired-runs.csv](paired-runs.csv) | 384 primary pairs from four grid-size and width combinations, plus 88 repeats with smaller time steps. Each row records initialization, endpoint means, residuals and predicted gap. |
| [paired-summary.csv](paired-summary.csv) | Sign accuracy with exact binomial intervals, through-origin regression slopes and prediction RMS errors. The 95% bootstrap intervals resample whole pairs 4,096 times within each design and sampling group. |
| [paired-refinement.csv](paired-refinement.csv) | Changes in the observed gap and ordering after halving the integration step on prespecified draws. |
| [paired-boundary.csv](paired-boundary.csv) | 27 additional checks at step 0.0625 for near ties and wrong orderings, covering all 19 sign misses across the primary designs. |

The integrator uses Heun’s explicit trapezoidal rule with both gradients recomputed at the trial point. Primary runs use step 0.25 and stop at time 160 for $N=3$ or 512 for $N=5$. The reported continuation bound controls exact flow starting from the computed endpoint. Step refinement measures sensitivity to the preceding numerical integration. [Integrator](paired_flows.py) · [Lean certificates for numerical residuals](../formal/CirclePairedResidualData.lean)

## Reproduce the figure and tables

From the repository root, run the following in a POSIX shell with Python 3.11. Rebuilt outputs go to a fresh directory. The baseline calculation checks the SHA-256 digest of the primary data before counting correct orderings. [Figure script](plot_ordering.py) · [Baselines](../paper/majority.py) · [Statistical summaries](paired_summary.py)

```sh
work=$(mktemp -d)
python3.11 -m venv "$work/venv"
py="$work/venv/bin/python"
"$py" -m pip install numpy==2.4.6 scipy==1.17.1 matplotlib==3.10.8 mpmath==1.3.0
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1
export MPLCONFIGDIR="$work/matplotlib"

"$py" layer-rates/plot_ordering.py --output "$work/paired-ordering.png"
"$py" paper/majority.py > "$work/majority.csv"
"$py" layer-rates/paired_summary.py --output-dir "$work"
cmp "$work/paired-summary.csv" layer-rates/paired-summary.csv
cmp "$work/paired-refinement.csv" layer-rates/paired-refinement.csv
```

To regenerate the trajectories from the recorded random seeds, continue in the same shell. The simulator writes `paired-runs.csv` and `paired-boundary.csv` in the output directory. For a quick check of one draw under each sampling law, add `--design 3x512 --count 1`.

```sh
"$py" layer-rates/paired_flows.py --workers 8 --output-dir "$work/trajectories"
```

To typeset the paper from the repository root, run `python3 paper/build_pdf.py`. The result is `paper/paper.pdf`. [Typesetting requirements and proof attachment](../paper/README.md)
