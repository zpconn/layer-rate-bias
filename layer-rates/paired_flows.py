"""Paired, full-batch Heun integration of the two continuous-time circle learners."""

import argparse
import csv
import math
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

import numpy as np

DIR = Path(__file__).parent
TAUS = (0.5, 2.0)


def inputs(n):
    u = np.arange(n) * 2 * np.pi / n
    return np.ascontiguousarray(np.column_stack((np.cos(u), np.sin(u))))


def kernel_weights(x, tau):
    # Solve in angle space, independently of the Fourier/alias derivation.
    cross = np.outer(x[:, 0], x[:, 1])
    t = np.arctan2(np.abs(cross - cross.T), x @ x.T)
    k = (np.sin(t) + (1 + tau) * (np.pi - t) * np.cos(t)) / (2 * np.pi)
    p = np.linalg.solve(k, np.full(len(x), (2 + tau) / np.pi**2))
    np.testing.assert_allclose(p, p.sum() / len(x), atol=3e-15)
    return p.sum()


def evaluate(a, w, x):
    s = np.maximum(x @ w.T, 0)
    f = s @ a / np.sqrt(len(a))
    q = a @ np.linalg.norm(w, axis=1) / (np.pi * np.sqrt(len(a)))
    return f, q


def seed_case(x, m, seed, stratum):
    # The two strata use independent PCG64 streams. Reject the *entire* draw.
    rng = np.random.default_rng(
        np.random.SeedSequence([229731, seed, int(stratum == "above")])
    )
    for attempt in range(1, 20001):
        vals = rng.standard_normal((m, 3))
        a, w = vals[:, 0].copy(), vals[:, 1:].copy()
        f0, q0 = evaluate(a, w, x)
        if stratum == "natural" or f0.mean() > 1:
            return a, w, f0.mean(), q0, attempt
    raise RuntimeError("rejection cap reached")


def grad(a, w, tau, x, y, scale):
    z = x @ w.T
    h = np.maximum(z, 0)
    resid = h @ a / scale - y
    v = -resid / (len(x) * scale)
    return v @ h, (tau * a[:, None]) * (((z > 0).T * v) @ x)


def integrate(a0, w0, x, tau, step, local_horizon, full_horizon):
    a, w = a0.copy(), w0.copy()
    y = 1 + x[:, 0]
    m = len(a)
    scale = np.sqrt(m)
    initial_imbalance = a * a - np.sum(w * w, axis=1) / tau
    for _ in range(round(local_horizon / step)):
        da, dw = grad(a, w, tau, x, y, scale)
        ea, ew = grad(a + step * da, w + step * dw, tau, x, y, scale)
        a += step / 2 * (da + ea)
        w += step / 2 * (dw + ew)
    f, q = evaluate(a, w, x)
    rms = np.sqrt(np.mean((f - y) ** 2))
    # For any exact continuation from these numerical weights, energy dissipation
    # bounds the remaining distance in ordinary parameter coordinates.
    gap_bound = np.sqrt(max(1, tau) * (full_horizon - local_horizon) / 2) * rms
    param_norm = np.sqrt(a @ a + np.sum(w * w))
    mean_tail = gap_bound * (param_norm + gap_bound / 2) / (np.pi * scale)
    imbalance_drift = np.max(
        np.abs((a * a - np.sum(w * w, axis=1) / tau) - initial_imbalance)
    )
    return q, rms, mean_tail, imbalance_drift


def run(task):
    n, m, seed, stratum, step = task
    x = inputs(n)
    a, w, grid0, q0, attempts = seed_case(x, m, seed, stratum)
    horizon = 160.0 if n == 3 else 512.0
    H = math.ceil(2 * math.pi**2 * n * n * math.log(2 * math.sqrt(12) * n**3.5))
    b = [kernel_weights(x, tau) for tau in TAUS]
    values = [integrate(a, w, x, tau, step, horizon, H) for tau in TAUS]
    (slow, rslow, tslow, islow), (fast, rfast, tfast, ifast) = values
    predicted = n**2 * (b[0] - b[1]) * (1 - grid0)
    return {
        "n": n,
        "m": m,
        "seed": seed,
        "stratum": stratum,
        "draws": attempts,
        "step": step,
        "observed_time": horizon,
        "theorem_time": H,
        "grid0": grid0,
        "q0": q0,
        "b_slow": b[0],
        "b_fast": b[1],
        "slow": slow,
        "fast": fast,
        "rms_slow": rslow,
        "rms_fast": rfast,
        "tail_slow": tslow,
        "tail_fast": tfast,
        "imbalance_drift_slow": islow,
        "imbalance_drift_fast": ifast,
        "observed_scaled": n**2 * (slow - fast),
        "predicted_scaled": predicted,
        "asymptotic_scaled": np.pi**2 / 40 * (1 - grid0),
    }


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--workers", type=int, default=8)
    p.add_argument("--suffix", default="")
    p.add_argument("--output-dir", type=Path, default=DIR)
    p.add_argument("--count", type=int, default=48)
    p.add_argument(
        "--design", nargs="+", default=["3x512", "3x8192", "3x32768", "5x8192"]
    )
    a = p.parse_args()
    cases = []
    for design in a.design:
        n, m = map(int, design.split("x"))
        for st in ("natural", "above"):
            for seed in range(a.count):
                cases.append((n, m, seed, st, 0.25))
                if seed < 8:
                    cases.append((n, m, seed, st, 0.125))
                if seed < 3:
                    cases.append((n, m, seed, st, 0.0625))

    def write_cases(tasks, path):
        with ProcessPoolExecutor(a.workers) as pool, path.open("w", newline="") as out:
            for idx, row in enumerate(pool.map(run, tasks, chunksize=1)):
                if idx == 0:
                    writer = csv.DictWriter(out, fieldnames=list(row))
                    writer.writeheader()
                writer.writerow(row)
                if idx % 16 == 0:
                    out.flush()

    a.output_dir.mkdir(parents=True, exist_ok=True)
    output = a.output_dir / f"paired-runs{a.suffix}.csv"
    write_cases(cases, output)
    recheck_boundaries(output, a.workers, a.suffix)


def recheck_boundaries(output, workers, suffix):
    # Falsification check. Keep the main sample and its estimator unchanged.
    with output.open() as fp:
        base = [r for r in csv.DictReader(fp) if float(r["step"]) == 0.25]
    tasks = []
    for r in base:
        obs, pred = float(r["observed_scaled"]), float(r["predicted_scaled"])
        if obs * pred <= 0 or abs(obs) < 0.002:
            tasks.append(
                (int(r["n"]), int(r["m"]), int(r["seed"]), r["stratum"], 0.0625)
            )
    with (
        ProcessPoolExecutor(workers) as pool,
        output.with_name(f"paired-boundary{suffix}.csv").open("w", newline="") as out,
    ):
        for idx, row in enumerate(pool.map(run, tasks, chunksize=1)):
            if idx == 0:
                writer = csv.DictWriter(out, fieldnames=list(row))
                writer.writeheader()
            writer.writerow(row)


if __name__ == "__main__":
    main()
