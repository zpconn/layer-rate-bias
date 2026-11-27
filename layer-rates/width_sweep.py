"""Natural-pair width sweep and optimizer/initialization controls.

Compile grouped_solver.cpp first (see README). Every CSV row is a full-network
run. Families with the same seed share PCG64 draws across widths and grids.
"""

import argparse
import csv
import ctypes
import math
import os
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

import numpy as np

from paired_flows import evaluate, inputs, kernel_weights, seed_case

DIR = Path(__file__).resolve().parent
COUNTS = {3: 200, 5: 128, 7: 96, 9: 64, 11: 48}
WIDTHS = (512, 2048, 8192, 32768, 131072, 524288)
LIB = None


def setup(library):
    global LIB
    LIB = ctypes.CDLL(os.fspath(library)).simulate
    array = np.ctypeslib.ndpointer(dtype=np.float64, flags="C_CONTIGUOUS")
    integer, real = ctypes.c_int, ctypes.c_double
    LIB.argtypes = [integer, integer, array, array, real, real, integer, integer, real]
    LIB.restype = integer


def capped_step(a, w, x):
    z = x @ w.T
    h = np.maximum(z, 0.0)
    active_readout = a * (z > 0.0)
    gram = (h @ h.T + (x @ x.T) * (active_readout @ active_readout.T)) / (
        len(x) * len(a)
    )
    curvature = np.linalg.eigvalsh(gram)[-1]
    return 1.0 / max(1.0, curvature)


def task_result(task):
    n, m, seed, method, step = task
    x = inputs(n)
    mirror = method == "antisymmetric"
    a, w, _, _, _ = seed_case(x, m // 2 if mirror else m, seed, "natural")
    if mirror:
        a, w = np.concatenate((a, -a)), np.vstack((w, w))
    initial = np.column_stack((a, w))
    f0, q0 = evaluate(a, w, x)
    deficit = 1.0 - f0.mean()
    horizon = math.ceil(2 * math.pi**2 * n * n * math.log(2 * math.sqrt(12) * n**3.5))
    flow = method in ("flow", "antisymmetric")
    equal = method in ("equal_gd", "capped")
    rates = (1.0,) if equal else (0.5, 2.0)
    if method == "capped":
        step = capped_step(a, w, x)
    row = {
        "n": n,
        "m": m,
        "seed": seed,
        "method": method,
        "step": step,
        "H": horizon,
        "X": deficit,
        "q0": q0,
    }
    means = []
    for label, tau in zip(("slow", "fast") if not equal else ("slow",), rates):
        params = initial.copy()
        updates = LIB(
            n,
            m,
            params,
            x,
            tau,
            step,
            round(horizon / step) if flow else horizon,
            int(flow),
            1e-10 if flow else 0.0,
        )
        f, q = evaluate(params[:, 0], params[:, 1:], x)
        rms = np.sqrt(np.mean((f - 1.0 - x[:, 0]) ** 2))
        if not np.isfinite([q, rms]).all():
            raise ValueError(f"nonfinite result for {task}")
        tail = ""
        if flow:
            d = (
                math.sqrt(max(1.0, tau) * max(0.0, horizon - updates * step) / 2.0)
                * rms
            )
            tail = d * (np.linalg.norm(params) + d / 2.0) / (math.pi * math.sqrt(m))
        row.update(
            {
                f"updates_{label}": updates,
                f"mean_{label}": q,
                f"rms_{label}": rms,
                f"tail_{label}": tail,
            }
        )
        means.append(q)
    if equal:
        row.update(updates_fast="", mean_fast="", rms_fast="", tail_fast="")
    coeff = n * n * (kernel_weights(x, 0.5) - kernel_weights(x, 2.0))
    row.update(c=coeff, D=n * n * (means[0] - means[-1]) if not equal else "")
    return row


def design_tasks(section, widths):
    if section == "width":
        for n, count in COUNTS.items():
            for seed in range(count):
                for m in widths:
                    yield n, m, seed, "flow", 0.25
    elif section == "refinement":
        for n in COUNTS:
            for seed in range(3):
                for m in widths:
                    yield n, m, seed, "flow", 0.125
    elif section == "controls":
        for n in (3, 5):
            for m in (512, 8192):
                for seed in range(24):
                    for method in ("unit_gd", "equal_gd", "capped", "antisymmetric"):
                        yield (
                            n,
                            m,
                            seed,
                            method,
                            0.25 if method == "antisymmetric" else 1.0,
                        )
        # A small-width diagnostic where the initialization cap can activate.
        for seed in range(128):
            for method in ("equal_gd", "capped"):
                yield 3, 8, seed, method, 1.0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--library", type=Path, required=True)
    parser.add_argument(
        "--section", choices=("width", "refinement", "controls"), required=True
    )
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--widths", type=int, nargs="+", default=WIDTHS)
    args = parser.parse_args()
    tasks = design_tasks(args.section, args.widths)
    with (
        ProcessPoolExecutor(
            args.workers, initializer=setup, initargs=(args.library.resolve(),)
        ) as pool,
        args.output.open("w", newline="") as target,
    ):
        for k, row in enumerate(pool.map(task_result, tasks, chunksize=1)):
            if k == 0:
                writer = csv.DictWriter(target, fieldnames=row)
                writer.writeheader()
            writer.writerow(row)
            target.flush()


if __name__ == "__main__":
    main()
