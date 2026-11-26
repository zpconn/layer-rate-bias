"""Plot the principal finite-width comparisons from the paired ODE sweep."""

import csv
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

folder = Path(__file__).parent
with (folder / "paired-runs.csv").open() as f:
    rows = [r for r in csv.DictReader(f) if r["step"] == "0.25" and r["n"] == "3"]
fig, axes = plt.subplots(
    1, 2, figsize=(8.4, 4.35), sharex=True, sharey=True, layout="constrained"
)
for ax, m in zip(axes, (512, 32768)):
    ax.plot(
        [-0.17, 0.49],
        [-0.17, 0.49],
        color="0.35",
        linewidth=1,
        zorder=0,
        label="Exact kernel prediction",
    )
    ax.axhline(0, color="0.85", linewidth=0.7, zorder=0)
    ax.axvline(0, color="0.85", linewidth=0.7, zorder=0)
    for group, label, color, marker in [
        ("natural", "Gaussian seeds", "#0072B2", "o"),
        ("above", "Initial grid mean > 1", "#D55E00", "^"),
    ]:
        g = [r for r in rows if r["m"] == str(m) and r["stratum"] == group]
        ax.scatter(
            [float(r["predicted_scaled"]) for r in g],
            [float(r["observed_scaled"]) for r in g],
            s=22,
            c=color,
            marker=marker,
            alpha=0.78,
            label=label,
            linewidth=0.3,
            edgecolor="white",
        )
    ax.set_title(f"Width {m:,}, N = 3")
    ax.set_aspect("equal", adjustable="box")
    ax.set_xlabel(r"Predicted $N^2(Y_{1/2}-Y_2)$")
    ax.spines[["top", "right"]].set_visible(False)
axes[0].set_ylabel(r"Measured $N^2(Y_{1/2}-Y_2)$")
axes[0].legend(loc="upper left", fontsize=8, frameon=False)
fig.savefig(
    folder / "paired-contrast.png", dpi=180, bbox_inches="tight", pad_inches=0.12
)
