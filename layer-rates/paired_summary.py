"""Report seed-paired accuracy, sampling uncertainty, and discretization checks."""

import argparse
import csv
from collections import defaultdict
from pathlib import Path

import numpy as np
from scipy.stats import binomtest

DIR = Path(__file__).parent


def save(path, rows):
    with path.open("w", newline="") as fp:
        w = csv.DictWriter(fp, fieldnames=list(rows[0]))
        w.writeheader()
        w.writerows(rows)


def group_rows(rows, keys):
    out = defaultdict(list)
    for r in rows:
        out[tuple(r[k] for k in keys)].append(r)
    return out


def subset_stats(g, threshold):
    rr = [r for r in g if abs(1 - r["grid0"]) >= threshold]
    init = np.array([1 - r["grid0"] for r in rr])
    pred = np.array([r["predicted_scaled"] for r in rr])
    asym = np.array([r["asymptotic_scaled"] for r in rr])
    obs = np.array([r["observed_scaled"] for r in rr])
    error = obs - pred
    correct = np.count_nonzero(obs * pred > 0)
    ci = binomtest(correct, len(rr)).proportion_ci(0.95)
    ix = np.random.default_rng(723492).integers(len(rr), size=(4096, len(rr)))
    rmse_ci = np.quantile(np.sqrt((error[ix] ** 2).mean(axis=1)), [0.025, 0.975])
    beta = np.dot(init, obs) / np.dot(init, init)
    beta_boot = (init[ix] * obs[ix]).sum(axis=1) / (init[ix] ** 2).sum(axis=1)
    blo, bhi = np.quantile(beta_boot, [0.025, 0.975])
    return {
        "margin": threshold,
        "count": len(rr),
        "initial_above": sum(init < 0),
        "sign_matches": correct,
        "match_fraction": correct / len(rr),
        "match_low": ci.low,
        "match_high": ci.high,
        "observed_coefficient": beta,
        "coef_low": blo,
        "coef_high": bhi,
        "exact_coefficient": rr[0]["n"] ** 2 * (rr[0]["b_slow"] - rr[0]["b_fast"]),
        "rms_finite_error": np.sqrt(np.mean(error**2)),
        "rms_low": rmse_ci[0],
        "rms_high": rmse_ci[1],
        "rms_limit_error": np.sqrt(np.mean((obs - asym) ** 2)),
        "scaled_pred_rms": np.sqrt(np.mean(pred**2)),
        "mean_scaled_difference": np.mean(obs),
        "mean_scaled_prediction": np.mean(pred),
    }


def original_width_fit(primary):
    """Fit the three-width trend in the unconditional three-point design."""
    widths = [512, 8192, 32768]
    natural = [r for r in primary if r["n"] == 3 and r["stratum"] == "natural"]
    by_width = [
        sorted((r for r in natural if r["m"] == m), key=lambda r: r["seed"])
        for m in widths
    ]
    seeds = [r["seed"] for r in by_width[0]]
    if not seeds or len(set(seeds)) != len(seeds) or any(
        [r["seed"] for r in group] != seeds for group in by_width
    ):
        raise ValueError("The original width fit needs matching distinct seeds at all three widths")
    coefficients = {9 * (r["b_slow"] - r["b_fast"]) for group in by_width for r in group}
    if len(coefficients) != 1:
        raise ValueError("Expected one finite-grid coefficient at N=3")
    coefficient = coefficients.pop()
    deficit = np.array([[1 - r["grid0"] for r in group] for group in by_width])
    scaled_gap = np.array([[r["observed_scaled"] for r in group] for group in by_width])

    def exponent(indices):
        x, y = deficit[:, indices], scaled_gap[:, indices]
        shortfall = coefficient - (x * y).sum(axis=-1) / (x * x).sum(axis=-1)
        if not np.all(shortfall > 0):
            raise ValueError("The log-width fit requires positive shortfalls")
        return -np.polyfit(np.log(widths), np.log(shortfall), 1)[0]

    # Each column of the bootstrap index matrix selects one seed at all widths.
    replicates = 4096
    bootstrap_seed = 723492
    draws = np.random.default_rng(bootstrap_seed).integers(
        len(seeds), size=(replicates, len(seeds))
    )
    low, high = np.quantile(exponent(draws), [0.025, 0.975])
    return dict(n=3, widths=" ".join(map(str, widths)), seeds=len(seeds),
                replicates=replicates, bootstrap_seed=bootstrap_seed,
                alpha=exponent(np.arange(len(seeds))), alpha_low=low, alpha_high=high)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=DIR / "paired-runs.csv")
    parser.add_argument("--output-dir", type=Path, default=DIR)
    parser.add_argument("--width-fit", action="store_true",
                        help="also fit the unconditional N=3 three-width trend")
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    with args.input.open() as f:
        rows = list(csv.DictReader(f))
    for r in rows:
        for k in r.keys() - {"stratum"}:
            r[k] = (
                int(r[k])
                if k in ("n", "m", "seed", "draws", "theorem_time")
                else float(r[k])
            )
    base = [r for r in rows if r["step"] == 0.25]
    summary = []
    refinements = []
    for (n, m, st), g in group_rows(base, ("n", "m", "stratum")).items():
        for delta in (0.0, 0.1):
            summary.append(dict(n=n, m=m, stratum=st, **subset_stats(g, delta)))
        allruns = [
            r for r in rows if r["n"] == n and r["m"] == m and r["stratum"] == st
        ]
        lookup = {(r["seed"], r["step"]): r for r in allruns}
        for h in (0.25, 0.125):
            coarse = [
                r for r in allruns if r["step"] == h and (r["seed"], h / 2) in lookup
            ]
            fine = [lookup[(r["seed"], h / 2)] for r in coarse]
            errors = np.array(
                [
                    r["observed_scaled"] - s["observed_scaled"]
                    for r, s in zip(coarse, fine)
                ]
            )
            refinements.append(
                {
                    "n": n,
                    "m": m,
                    "stratum": st,
                    "coarse_step": h,
                    "fine_step": h / 2,
                    "count": len(fine),
                    "rms_pair_change": np.sqrt(np.mean(errors**2)),
                    "max_pair_change": np.max(abs(errors)),
                    "sign_flips": sum(
                        r["observed_scaled"] * s["observed_scaled"] <= 0
                        for r, s in zip(coarse, fine)
                    ),
                    "max_scaled_tail": n
                    * n
                    * max(r["tail_slow"] + r["tail_fast"] for r in allruns),
                    "max_resid": max(
                        max(r["rms_slow"], r["rms_fast"]) for r in allruns
                    ),
                    "max_invariant_drift": max(
                        max(r["imbalance_drift_slow"], r["imbalance_drift_fast"])
                        for r in fine
                    ),
                }
            )
    save(args.output_dir / "paired-summary.csv", summary)
    save(args.output_dir / "paired-refinement.csv", refinements)
    if args.width_fit:
        save(args.output_dir / "paired-width-fit.csv", [original_width_fit(base)])


if __name__ == "__main__":
    main()
