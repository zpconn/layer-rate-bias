"""Plot measured paired orderings against the initial grid-mean deficit."""

import argparse
import csv
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import FixedLocator, StrMethodFormatter

HERE = Path(__file__).resolve().parent
STRATA = (
    ("natural", "Unconditional Gaussian", "o", "#0072B2"),
    ("above", r"Gaussian given $Q_N f_0>1$", "^", "#C54D00"),
)


def load_pairs(path):
    with path.open(newline="") as csv_file:
        rows = [
            row
            for row in csv.DictReader(csv_file)
            if int(row["n"]) == 3
            and int(row["m"]) == 32768
            and float(row["step"]) == 0.25
        ]
    coefficients = {9 * (float(row["b_slow"]) - float(row["b_fast"])) for row in rows}
    if len(coefficients) != 1:
        raise ValueError("Expected one finite-grid slope for the three-point design")
    pairs = {}
    for stratum, *_ in STRATA:
        group = [row for row in rows if row["stratum"] == stratum]
        if len(group) != 48 or len({row["seed"] for row in group}) != 48:
            raise ValueError(f"Expected 48 distinct primary seeds in {stratum}")
        pairs[stratum] = [
            (1 - float(row["grid0"]), float(row["observed_scaled"])) for row in group
        ]
    return coefficients.pop(), pairs


def draw_panel(ax, xlim, ylim, slope, pairs, title):
    ax.axhline(0, color="0.63", linewidth=0.75, zorder=0)
    ax.axvline(0, color="0.63", linewidth=0.75, zorder=0)
    (reference,) = ax.plot(
        xlim,
        [slope * x for x in xlim],
        color="0.18",
        linewidth=1.0,
        label=r"Finite grid $D=c_3 x$",
        zorder=1,
    )
    point_handles = []
    for stratum, label, marker, color in STRATA:
        x, y = zip(*pairs[stratum])
        point_handles.append(
            ax.scatter(
                x,
                y,
                s=24,
                marker=marker,
                color=color,
                linewidths=0.45,
                edgecolors="white",
                alpha=0.9,
                label=label,
                zorder=2,
            )
        )
    ax.set(xlim=xlim, ylim=ylim, xlabel=r"Initial deficit $x=1-Q_N f_0$")
    ax.set_title(title, loc="left", pad=8, fontsize=10.5, fontweight="bold")
    ax.spines[["top", "right"]].set_visible(False)
    ax.spines[["bottom", "left"]].set_color("0.4")
    ax.tick_params(width=0.65, length=3)
    return [*point_handles, reference]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--input", type=Path, default=HERE / "paired-runs.csv"
    )
    parser.add_argument("--output", type=Path, default=HERE.parent / "paper" / "paired-ordering.png")
    args = parser.parse_args()
    slope, pairs = load_pairs(args.input)
    for stratum, points in pairs.items():
        correct = sum(x * y > 0 for x, y in points)
        slow_larger = sum(y > 0 for _, y in points)
        print(
            f"{stratum}: sign rule {correct}/{len(points)}, "
            f"always predicting the slow rate is larger {slow_larger}/{len(points)}"
        )
    plt.rcParams.update(
        {
            "font.family": "DejaVu Sans",
            "mathtext.fontset": "dejavusans",
            "font.size": 9.0,
            "axes.linewidth": 0.65,
            "axes.labelsize": 9.5,
            "xtick.labelsize": 8.5,
            "ytick.labelsize": 8.5,
        }
    )
    fig, (full, zoom) = plt.subplots(
        1, 2, figsize=(7.2, 3.45), gridspec_kw={"width_ratios": [1.12, 1]}
    )
    fig.subplots_adjust(left=0.105, right=0.985, bottom=0.165, top=0.795, wspace=0.29)
    handles = draw_panel(
        full, (-0.82, 1.70), (-0.198, 0.39), slope, pairs, "A   All 96 pairs"
    )
    full.set_ylabel(r"Measured contrast $D=N^2(Y_{1/2}-Y_2)$", labelpad=4)
    full.xaxis.set_major_locator(FixedLocator([-0.5, 0, 0.5, 1.0, 1.5]))
    draw_panel(
        zoom, (-0.061, 0.008), (-0.0238, 0.0048), slope, pairs, "B   Near the tie"
    )
    zoom.xaxis.set_major_locator(FixedLocator([-0.06, -0.04, -0.02, 0]))
    zoom.yaxis.set_major_locator(FixedLocator([-0.02, -0.01, 0]))
    zoom.xaxis.set_major_formatter(StrMethodFormatter("{x:.2f}"))
    zoom.yaxis.set_major_formatter(StrMethodFormatter("{x:.2f}"))
    zoom.annotate(
        "Two sign mismatches",
        xy=(-0.0042, 0.00115),
        xytext=(-0.058, 0.0026),
        fontsize=8.3,
        color="0.17",
        ha="left",
        va="center",
        arrowprops={"arrowstyle": "-", "color": "0.38", "linewidth": 0.7},
    )
    fig.legend(
        handles=handles,
        loc="upper center",
        ncols=3,
        frameon=False,
        bbox_to_anchor=(0.52, 0.98),
        columnspacing=1.55,
        handletextpad=0.45,
        handlelength=1.7,
        fontsize=8.8,
    )
    fig.savefig(args.output, dpi=300, facecolor="white")
    plt.close(fig)


if __name__ == "__main__":
    main()
