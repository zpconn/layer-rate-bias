"""Plot constant-mode aliasing and the kernel response to a unit grid residual."""

import argparse
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


def kernel_row_mean(u, nodes, tau):
    relative = u[:, None] - nodes
    distance = np.abs((relative + np.pi) % (2 * np.pi) - np.pi)
    kernel = (
        np.sin(distance) + (1 + tau) * (np.pi - distance) * np.cos(distance)
    ) / (2 * np.pi)
    return kernel.mean(axis=1)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=(
        Path(__file__).resolve().parents[1] / "paper" / "kernel-alias.png"
    ))
    args = parser.parse_args()
    plt.rcParams.update({
        "font.family": "DejaVu Sans", "mathtext.fontset": "dejavusans",
        "font.size": 9, "axes.linewidth": 0.65, "xtick.labelsize": 8.5,
        "ytick.labelsize": 8.5, "legend.fontsize": 8.4,
    })
    n = 3
    cell = 2 * np.pi / n
    nodes = np.arange(n) * cell
    blue, orange = "#0072B2", "#D55E00"
    fig, (left, right) = plt.subplots(1, 2, figsize=(7.2, 3.15))
    fig.subplots_adjust(left=0.085, right=0.98, bottom=0.33, top=0.86, wspace=0.34)

    angle = np.linspace(0, 2 * np.pi, 1201)
    left.axhline(0, color="0.83", linewidth=0.7)
    left.axhline(1, color="0.22", linestyle="--", linewidth=1.05, label="Constant 1")
    left.plot(angle, np.cos(2 * n * angle), color=blue, label=r"$\cos(6u)$")
    left.scatter(nodes, np.ones(n), s=23, color="0.15", zorder=3, label="Grid nodes")
    left.set(xlim=(-0.09, 2 * np.pi + 0.09), ylim=(-1.15, 1.18),
             yticks=[-1, 0, 1], ylabel="Mode value", xlabel=r"Angle $u$")
    left.set_xticks([0, cell, 2 * cell, 3 * cell],
                    ["0", r"$2\pi/3$", r"$4\pi/3$", r"$2\pi$"])
    left.set_title("A   Grid and population averages", loc="left", fontsize=10.2)
    left.legend(loc="upper center", bbox_to_anchor=(0.5, -0.34), ncols=3,
                frameon=False, columnspacing=0.9, handlelength=1.25)

    angle = np.linspace(0, cell, 1201)
    for tau, rate, color, style in ((0.5, "1/2", blue, "-"), (2, "2", orange, "--")):
        zero_mode = kernel_row_mean(nodes[:1], nodes, tau)[0]
        correction = kernel_row_mean(angle, nodes, tau) / zero_mode
        weight = (2 + tau) / (np.pi**2 * zero_mode)
        # Check the plotted cell mean independently of the kernel's analytic integral.
        numerical_mean = (correction[:-1] + correction[1:]).mean() / 2
        np.testing.assert_allclose(numerical_mean, weight, atol=2e-7, rtol=0)
        right.plot(angle, correction, color=color, linestyle=style, linewidth=1.5,
                   label=rf"$\tau={rate}$, mean {weight:.4f}")
    right.scatter([0, cell], [1, 1], s=23, color="0.15", zorder=3)
    right.set(xlim=(-0.035, cell + 0.035), ylim=(0.922, 1.006),
              yticks=[0.94, 0.96, 0.98, 1], ylabel="Kernel correction", xlabel=r"Angle $u$")
    right.set_xticks([0, cell / 2, cell], ["0", r"$\pi/3$", r"$2\pi/3$"])
    right.set_title("B   Unit residual at every node", loc="left", fontsize=10.2)
    right.legend(loc="upper center", bbox_to_anchor=(0.5, -0.34),
                 frameon=False, borderaxespad=0.4, handlelength=1.7)
    for ax in (left, right):
        ax.spines[["top", "right"]].set_visible(False)
        ax.tick_params(width=0.65, length=3)
    fig.savefig(args.output, dpi=300, facecolor="white")
    plt.close(fig)


if __name__ == "__main__":
    main()
