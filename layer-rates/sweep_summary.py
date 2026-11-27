"""Estimate the finite-width slope correction using a seed-cluster bootstrap."""

import argparse
import csv
from collections import defaultdict
from pathlib import Path

import numpy as np

from width_sweep import COUNTS, DIR, WIDTHS


def read(path):
    with path.open() as stream:
        return list(csv.DictReader(stream))


def save(path, rows):
    with path.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=rows[0])
        writer.writeheader()
        writer.writerows(rows)


def get_pairs(rows):
    groups = defaultdict(dict)
    for row in rows:
        key = int(row["n"]), int(row["m"])
        seed = int(row["seed"])
        if seed in groups[key] or row["method"] != "flow":
            raise ValueError(
                f"Duplicate seed or unexpected method at {key}, seed {seed}"
            )
        groups[key][seed] = row
    return groups


def width_estimates(records, repeats):
    groups, refined = get_pairs(records), get_pairs(repeats)
    expected = {(n, m) for n in COUNTS for m in WIDTHS}
    if groups.keys() != expected or refined.keys() != expected:
        raise ValueError("Missing or unexpected design")
    designs, trends = [], []
    log_width = np.log(np.asarray(WIDTHS, dtype=float))
    log_centered = log_width - log_width.mean()
    for n, count in COUNTS.items():
        seeds = range(count)
        resample = np.random.default_rng(723492).integers(count, size=(4096, count))
        shortfalls, bootstraps = [], []
        for m in WIDTHS:
            group, refinement = groups[n, m], refined[n, m]
            if group.keys() != set(seeds) or refinement.keys() != {0, 1, 2}:
                raise ValueError(f"Unexpected seed set at N={n}, m={m}")
            x, d = np.array(
                [[float(group[i][field]) for i in seeds] for field in ("X", "D")]
            )
            coeff = float(group[0]["c"])
            beta = np.dot(x, d) / np.dot(x, x)
            shortfalls.append(coeff - beta)
            boot_beta = (x * d)[resample].sum(axis=1) / (x * x)[resample].sum(axis=1)
            boot = coeff - boot_beta
            lo, hi = np.quantile(boot, [0.025, 0.975])
            bootstraps.append(boot)
            refine = max(abs(float(refinement[i]["D"]) - d[i]) for i in refinement)
            tail = (
                n
                * n
                * max(
                    float(r["tail_slow"]) + float(r["tail_fast"])
                    for r in group.values()
                )
            )
            designs.append(
                {
                    "n": n,
                    "m": m,
                    "seeds": count,
                    "c": coeff,
                    "fitted": beta,
                    "shortfall": coeff - beta,
                    "shortfall_low": lo,
                    "shortfall_high": hi,
                    "sign_matches": int(np.count_nonzero(d * x > 0)),
                    "max_step_change": refine,
                    "slope_step_sensitivity": refine * np.abs(x).sum() / np.dot(x, x),
                    "max_scaled_tail": tail,
                }
            )
        shortfalls = np.asarray(shortfalls)
        bootstrap = np.stack(bootstraps, axis=1)
        if np.any(shortfalls <= 0) or np.any(bootstrap <= 0):
            raise ValueError(f"Nonpositive shortfall prevents log-scale fit at N={n}")

        def fit(values):
            logs = np.log(values)
            alpha = -(logs @ log_centered) / (log_centered @ log_centered)
            kappa = np.exp(logs.mean(axis=-1) + alpha * log_width.mean())
            return alpha, kappa

        alpha, kappa = fit(shortfalls)
        boot_alpha, boot_kappa = fit(bootstrap)
        alo, ahi = np.quantile(boot_alpha, [0.025, 0.975])
        klo, khi = np.quantile(boot_kappa, [0.025, 0.975])
        trends.append(
            {
                "n": n,
                "seeds": count,
                "alpha": alpha,
                "alpha_low": alo,
                "alpha_high": ahi,
                "kappa": kappa,
                "kappa_low": klo,
                "kappa_high": khi,
            }
        )
    return designs, trends


def control_estimates(records):
    groups = defaultdict(dict)
    for row in records:
        key = int(row["n"]), int(row["m"]), row["method"]
        seed = int(row["seed"])
        if seed in groups[key]:
            raise ValueError(f"Duplicate control {key}, seed {seed}")
        groups[key][seed] = row
    summary = []
    for (n, m, method), group in groups.items():
        rows = [group[i] for i in range(len(group))]
        result = {
            "n": n,
            "m": m,
            "method": method,
            "seeds": len(rows),
            "sign_matches": "",
            "mean_scaled": "",
            "fitted": "",
            "c": rows[0]["c"],
            "caps_active": "",
            "max_equal_gd_mean_change": "",
        }
        if method in ("antisymmetric", "unit_gd"):
            x, d = np.array([[float(r[field]) for r in rows] for field in ("X", "D")])
            if method == "antisymmetric":
                np.testing.assert_allclose(x, 1.0, rtol=0.0, atol=2e-13)
            result.update(
                sign_matches=int(np.count_nonzero(x * d > 0.0)),
                mean_scaled=d.mean(),
                fitted=np.dot(x, d) / np.dot(x, x),
            )
        elif method == "capped":
            other = groups[n, m, "equal_gd"]
            changes = [
                abs(float(r["mean_slow"]) - float(other[i]["mean_slow"]))
                for i, r in enumerate(rows)
            ]
            active = [float(r["step"]) < 1.0 for r in rows]
            if any(change != 0 and not cap for change, cap in zip(changes, active)):
                raise ValueError("Uncapped identical trajectories disagree")
            result.update(
                caps_active=sum(active), max_equal_gd_mean_change=max(changes)
            )
        summary.append(result)
    return summary


def plot(path, designs, trends):
    import matplotlib.pyplot as plt

    fig, ax = plt.subplots(figsize=(6.8, 3.8), layout="constrained")
    colors = ("#0072B2", "#D55E00", "#009E73", "#CC79A7", "#343434")
    for marker, color, trend in zip(("o", "s", "^", "D", "v"), colors, trends):
        n = trend["n"]
        group = [r for r in designs if r["n"] == n]
        w = np.array([r["m"] for r in group])
        y = np.array([r["shortfall"] for r in group])
        bounds = np.array(
            [[r[key] for r in group] for key in ("shortfall_low", "shortfall_high")]
        )
        sensitivity = np.array([r["slope_step_sensitivity"] for r in group])
        ax.errorbar(
            w * 1.075,
            y,
            yerr=sensitivity,
            color=color,
            alpha=0.7,
            ls="none",
            elinewidth=1.4,
            capsize=1,
        )
        ax.errorbar(
            w,
            y,
            yerr=np.abs(bounds - y),
            color=color,
            marker=marker,
            ls="none",
            ms=4,
            capsize=2,
            label=f"N = {n}",
        )
        ax.plot(
            w,
            trend["kappa"] * w.astype(float) ** (-trend["alpha"]),
            color=color,
            alpha=0.65,
            lw=0.9,
        )
    ax.set(
        xscale="log",
        yscale="log",
        xlabel="Hidden width, m",
        ylabel=r"Slope shortfall, $c_N-\hat\beta$",
    )
    ax.set_xticks(WIDTHS, ["512", "2,048", "8,192", "32,768", "131,072", "524,288"])
    ax.tick_params(axis="x", labelsize=9)
    ax.spines[["top", "right"]].set_visible(False)
    ax.grid(axis="y", alpha=0.18)
    ax.legend(loc="lower left", ncol=2, frameon=False, fontsize=8)
    fig.savefig(path, dpi=200)
    plt.close(fig)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-dir", type=Path, default=DIR)
    parser.add_argument("--output-dir", type=Path, default=DIR)
    args = parser.parse_args()
    d, t = width_estimates(
        read(args.input_dir / "width-runs.csv"),
        read(args.input_dir / "width-refinement.csv"),
    )
    args.output_dir.mkdir(parents=True, exist_ok=True)
    save(args.output_dir / "width-summary.csv", d)
    save(args.output_dir / "width-trends.csv", t)
    save(
        args.output_dir / "control-summary.csv",
        control_estimates(read(args.input_dir / "control-runs.csv")),
    )
    plot(args.output_dir / "width-scaling.png", d, t)


if __name__ == "__main__":
    main()
