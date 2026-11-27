"""Check the grouped integrator against direct finite-network updates."""

import argparse
import csv
from pathlib import Path

import numpy as np

import width_sweep
from paired_flows import grad, inputs, seed_case


def velocity(params, tau, x):
    da, dw = grad(
        params[:, 0], params[:, 1:], tau, x, 1 + x[:, 0], np.sqrt(len(params))
    )
    return np.column_stack((da, dw))


def check_steps(library):
    width_sweep.setup(library)
    for n, m in ((3, 512), (7, 97), (11, 129)):
        x = inputs(n)
        a, w, *_ = seed_case(x, m, 0, "natural")
        for tau in (0.5, 1.0, 2.0):
            for heun in (False, True):
                step = 0.25 if heun else 1.0
                state = np.column_stack((a, w))
                reference = state.copy()
                for _ in range(129):
                    first = velocity(reference, tau, x)
                    if heun:
                        first = (first + velocity(reference + step * first, tau, x)) / 2
                    reference += step * first
                steps = width_sweep.LIB(n, m, state, x, tau, step, 129, int(heun), 0.0)
                assert steps == 129
                np.testing.assert_allclose(state, reference, rtol=2e-12, atol=2e-12)
                assert np.any((x @ state[:, 1:].T > 0) != (x @ w.T > 0))


def check_overlap(data_dir):
    def read(name):
        with (data_dir / name).open() as f:
            return list(csv.DictReader(f))

    new = {(r["n"], r["m"], r["seed"]): r for r in read("width-runs.csv")}
    old = [
        r
        for r in read("paired-runs.csv")
        if r["stratum"] == "natural" and float(r["step"]) == 0.25
    ]
    errors = []
    for r in old:
        s = new[r["n"], r["m"], r["seed"]]
        np.testing.assert_allclose(float(s["X"]), 1 - float(r["grid0"]), atol=2e-13)
        errors.append(abs(float(s["D"]) - float(r["observed_scaled"])))
    assert len(errors) == 192 and max(errors) < 1e-7
    print(
        f"{len(errors)} overlapping natural pairs, max scaled endpoint difference {max(errors):.6g}"
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--library", type=Path, required=True)
    parser.add_argument("--data-dir", type=Path, default=width_sweep.DIR)
    args = parser.parse_args()
    check_steps(args.library.resolve())
    check_overlap(args.data_dir)
    print("Direct GD and Heun weight comparisons passed.")
