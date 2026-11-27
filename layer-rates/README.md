# Paired gradient-flow experiments

Two ReLU networks share one Gaussian initialization and train on the same $N$ equally spaced circle points with labels $1+\cos u$. The readout rate is one in both networks. The hidden rate is $1/2$ in one and $2$ in the other. Let $X$ be one minus the initial grid mean, and let $D$ be $N^2$ times the final slow-minus-fast difference in whole-circle means. The theory predicts $D\approx c_N X$, where $c_N$ is computed from the grid before training. These experiments test the prediction at finite widths by numerically integrating gradient flow. [Paper](../paper/paper.pdf) · [Derivation](../docs/from-first-principles.md)

## Ordering figure

At $N=3$ and width 32,768 the predicted slope is $c_3\approx 0.239159$. On 48 ordinary Gaussian draws, the deficit predicts all 48 orderings. Always predicting a higher mean for the slower run gives 45 correct. On 48 independent draws conditioned on $X<0$, the faster run finishes higher in 46. The two samples estimate success under their respective initialization laws. [Paper figure](../paper/paired-ordering.png) · [Comparison at widths 512 and 32,768](paired-contrast.png) · [Width-comparison script](plot_pairs.py)

The opening mechanism figure evaluates the two kernel interpolants on a continuous angular mesh. [Mechanism figure script](plot_mechanism.py)

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
"$py" layer-rates/paired_summary.py --width-fit --output-dir "$work"
cmp "$work/paired-summary.csv" layer-rates/paired-summary.csv
cmp "$work/paired-refinement.csv" layer-rates/paired-refinement.csv
cmp "$work/paired-width-fit.csv" layer-rates/paired-width-fit.csv
```

To regenerate the trajectories from the recorded random seeds, continue in the same shell. The simulator writes `paired-runs.csv` and `paired-boundary.csv` in the output directory. For a quick check of one draw under each sampling law, add `--design 3x512 --count 1`.

```sh
"$py" layer-rates/paired_flows.py --workers 8 --output-dir "$work/trajectories"
```

To typeset the paper from the repository root, run `python3 paper/build_pdf.py`. The result is `paper/paper.pdf`. [Typesetting requirements and proof attachment](../paper/README.md)

## Expanded width sweep and controls

The main sweep measures 3,216 natural pairs on grids of size 3, 5, 7, 9 and 11. Each grid uses the six widths $512\cdot4^j$, $j=0,\dots,5$. The respective seed counts per width are 200, 128, 96, 64 and 48. Each seed uses the same Gaussian stream across grid sizes and widths. A larger width extends the smaller network with new neurons. All 192 natural pairs in the original four designs recur in this sweep. [Raw data](width-runs.csv) · [Driver](width_sweep.py)

Heun steps have size 0.25. Each copy stops at the first checked block endpoint with RMS grid residual below $10^{-10}$ or at the horizon $H$. Rows give both step counts, both endpoint means, both residuals and their exact-flow continuation bounds. The first three seeds per design were repeated with step 0.125. The 95% percentile intervals for the power-law fit resample seeds jointly across all six widths within each grid, using 4,096 replicates and PCG64 seed 723492. The figure also shows sensitivity to the integration step. With $e$ the largest observed absolute change in $D$ on step halving at that design, the sensitivity displayed is $e\sum_i |X_i|/\sum_i X_i^2$. It gives the maximum slope change **if** every recorded $D_i$ changes by at most $e$. Refinement covers three seeds per design. [Step refinement](width-refinement.csv) · [Width summaries](width-summary.csv) · [Power-law fits](width-trends.csv) · [Width figure](width-scaling.png)

The solver groups neurons by their common set of active gates over a block of steps. For a fixed gate set, the gradient is a linear map of the three coordinates $(a,w_1,w_2)$ once the residual vector is given. A common $3\times3$ matrix $M$ therefore advances the whole group. Its contribution to the residual follows from the group’s summed outer products. At every gradient evaluation we check that the Frobenius norm of the hidden rows of $M-I$ is smaller than the least initial normalized gate margin $\min_{j,i}|w_j^\top x_i|/\|(a_j,w_j)\|$. This ensures that the gates used in the grouped calculation still hold for every member. Each block retries with a larger set of individually updated neurons if the check fails. The explicit updates recompute every gate in both Heun stages. Direct comparisons check all parameter coordinates across gate crossings in eighteen designs and the observable in all 192 overlapping natural pairs. The largest absolute difference in the scaled endpoint gap on the latter comparison was $6.27\times10^{-10}$, including the change in stopping rule. [Grouped solver](grouped_solver.cpp) · [Comparison with direct updates](check_solver.py)

Unit-step GD uses simultaneous gradients and runs both rates to update $H$. Equal-rate GD and its capped counterpart use the same seeds and the same update count. The capped run determines its step once from the largest eigenvalue of the initial grid prediction Gram matrix divided by $N$. Its single endpoint is stored in the slow columns. The small-width diagnostic uses $N=3$, $m=8$, and 128 natural seeds to exercise the cap. Antisymmetric flow initializes pairs of neurons with matching hidden weights and opposite readouts. It gives $f_0=0$ and $X=1$. [Control records](control-runs.csv) · [Control summaries](control-summary.csv)

### Reproduce the expanded runs

The full direct NumPy rerun of the original experiment took 55.63 s with eight workers on the same CPU. Its 472 primary and refinement rows and 27 boundary rows reproduced both original CSVs byte for byte under CPython 3.11.15, NumPy 2.4.6 and SciPy 1.17.1.

The expanded runs used CPython 3.12.3, NumPy 2.4.4, Matplotlib 3.10.8 and GCC 13.3.0 on an Intel Core Ultra 9 285K under x86-64 WSL2 Linux. BLAS used one thread per process. The six-width sweep took 143.64 s elapsed (eight worker processes). The controls took 0.58 s (three workers). The first five refinement widths took 12.64 s and the largest width took 35.35 s (two workers each). Other jobs shared this host during timing. Runtimes include creation of the CSVs and exclude compilation. Use a fresh working directory as below. Floating-point last digits can vary with compiler and BLAS builds.

```sh
work=$(mktemp -d)
python3.12 -m venv "$work/env"
py="$work/env/bin/python"
"$py" -m pip install numpy==2.4.4 matplotlib==3.10.8
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1
export MPLCONFIGDIR="$work/matplotlib"
g++ -O3 -std=c++17 -shared -fPIC layer-rates/grouped_solver.cpp -o "$work/solver.so"
"$py" layer-rates/width_sweep.py --library "$work/solver.so" --section width --workers 8 --output "$work/width-runs.csv"
"$py" layer-rates/width_sweep.py --library "$work/solver.so" --section refinement --workers 2 --output "$work/width-refinement.csv"
"$py" layer-rates/width_sweep.py --library "$work/solver.so" --section controls --workers 3 --output "$work/control-runs.csv"
"$py" layer-rates/sweep_summary.py --input-dir "$work" --output-dir "$work"
cp layer-rates/paired-runs.csv "$work/"
"$py" layer-rates/check_solver.py --library "$work/solver.so" --data-dir "$work"
```
