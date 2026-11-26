# /// script
# requires-python = ">=3.10"
# dependencies = ["mpmath==1.3.0"]
# ///
"""Reproduce majority baselines with `uv run --script paper/majority.py`.

Natural baseline probabilities refer to the exact rule G=Q_N f0 < 1. With
G>1 conditioning the rule always predicts fast. Counts are primary numerical
outcomes, including the accuracy of a constant-slow and a constant-fast call.
"""
import argparse
import csv
import hashlib
import io
from collections import defaultdict
from pathlib import Path

from mpmath import iv, mp

SOURCE = Path(__file__).resolve().parents[1] / 'layer-rates' / 'paired-runs.csv'
DIGEST = '0fc9fff87505049f61b26b950e3ef64f3f92053c05f5acafe94090a08261366e'


def natural_probabilities(n, m):
    """Return fixed-grid Gaussian limit and enclosure of the finite-width CDF."""
    # The grid average of a unit feature in each period is c*cos(theta),
    # theta uniform on [-d,d]. The integral over that period is 1/pi.
    d = mp.pi / (2 * n)
    c = 1 / (2 * n * mp.sin(d))
    variance = c**2 * (1 + mp.sin(2*d) / (2*d))
    gaussian_limit = mp.ncdf(1 / mp.sqrt(variance))

    # Each unscaled a*|w|*q has characteristic function E[1/(1+t²q²)],
    # by conditioning on a Rayleigh radius and a uniform angle. Substitution
    # u=tan(theta) gives atan(tan(d)/b)/(d*b), b=sqrt(1+c²t²).
    d = iv.pi / (2 * n)
    c = 1 / (2 * n * iv.sin(d))
    tan_d = iv.tan(d)
    t_max, divisions = 24, 6144
    step = iv.mpf(t_max) / divisions
    total = iv.mpf(1)
    for i in range(1, divisions + 1):
        t = i * step
        b = iv.sqrt(1 + c**2 * t**2 / m)
        characteristic = (iv.atan2(tan_d, b) / (d*b))**m
        weight = 1 if i == divisions else 4 if i % 2 else 2
        total += weight * iv.sin(t) / t * characteristic

    # Fourier inversion at 1 uses sinc(t) times the characteristic function.
    # This product is itself the characteristic function of G+U, U uniform
    # on [-1,1] independent. Its fourth derivative has modulus bounded by
    # E[(G+U)^4] <= 24/81 + 2*(2/9) + 1/5 < 1 (q <= 1/3).
    simpson_error = t_max * step**4 / (180*iv.pi)
    # Bound the omitted integrand in absolute value by (1+q_min² t²/m)^-m/t.
    z = (c * iv.cos(d) * t_max)**2 / m
    tail_error = (1 + 1/z) * (1 + z)**(-m) / (2*m*iv.pi)
    error = simpson_error + tail_error
    estimate = iv.mpf('0.5') + total * step / (3*iv.pi)
    return gaussian_limit, estimate + iv.mpf([-1, 1]) * error


def frozen_cells(source):
    data = source.read_bytes()
    if hashlib.sha256(data).hexdigest() != DIGEST:
        raise ValueError('Primary paired data differ from the frozen CSV')
    cells = defaultdict(list)
    for r in csv.DictReader(io.StringIO(data.decode())):
        if float(r['step']) != 0.25:
            continue
        g = float(r['grid0'])
        slow, fast = float(r['slow']), float(r['fast'])
        if g == 1 or slow == fast:
            raise ValueError('Tie requires a separate count')
        cells[int(r['n']), int(r['m']), r['stratum']].append((g < 1, slow > fast))
    return cells


def main():
    mp.dps = iv.dps = 35
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=SOURCE, help="path to frozen paired-runs.csv")
    cells = frozen_cells(parser.parse_args().input)
    print('N,m,stratum,P_rule_slow_large_width,P_rule_slow_finite_width,'
          'pairs,rule_slow_calls,constant_slow_correct,constant_fast_correct,rule_correct')
    for n, m in sorted({(n, m) for n, m, _ in cells}):
        limit, finite = natural_probabilities(n, m)
        # Both ends round to the same nine decimal places, including enclosure error.
        lo, hi = (format(float(x), '.9f') for x in (finite.a, finite.b))
        if lo != hi:
            raise ArithmeticError('Increase quadrature resolution for this design')
        for stratum in ('natural', 'above'):
            pairs = cells[n, m, stratum]
            slow_calls = sum(pred for pred, _ in pairs)
            slow_wins = sum(win for _, win in pairs)
            correct = sum(pred == win for pred, win in pairs)
            theoretical = [f'{float(limit):.9f}', lo] if stratum == 'natural' else ['0', '0']
            print(n, m, stratum, *theoretical, len(pairs), slow_calls,
                  slow_wins, len(pairs) - slow_wins, correct, sep=',')


if __name__ == '__main__':
    main()
