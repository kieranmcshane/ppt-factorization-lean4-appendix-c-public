#!/usr/bin/env python3
"""Small-r spectrum fits for the CL diagonal variational test.

This script is deliberately conservative: it fits only the exact small-r bands
available in the CSV files and labels the output as extrapolation.  It does not
claim to settle the diagonal regime.
"""

from __future__ import annotations

import argparse
import csv
import math
from collections import defaultdict
from pathlib import Path


def read_rows(path: Path, k: int) -> list[dict[str, int]]:
    rows: list[dict[str, int]] = []
    with path.open() as f:
        for row in csv.DictReader(f):
            if int(row["k"]) == k:
                rows.append({key: int(value) for key, value in row.items()})
    return rows


def aggregate_by_energy(rows: list[dict[str, int]]) -> dict[tuple[int, int], int]:
    out: dict[tuple[int, int], int] = defaultdict(int)
    for row in rows:
        out[(row["r"], row["E"])] += row["count"]
    return dict(out)


def solve_linear_3x3(a: list[list[float]], b: list[float]) -> list[float]:
    m = [a[i][:] + [b[i]] for i in range(3)]
    for col in range(3):
        pivot = max(range(col, 3), key=lambda r: abs(m[r][col]))
        if abs(m[pivot][col]) < 1e-12:
            raise ValueError("singular fit")
        m[col], m[pivot] = m[pivot], m[col]
        scale = m[col][col]
        for j in range(col, 4):
            m[col][j] /= scale
        for r in range(3):
            if r == col:
                continue
            factor = m[r][col]
            for j in range(col, 4):
                m[r][j] -= factor * m[col][j]
    return [m[i][3] for i in range(3)]


def least_squares(features: list[list[float]], y: list[float]) -> list[float]:
    # Model has three coefficients: a * r log r + b * r + c.
    ata = [[0.0] * 3 for _ in range(3)]
    aty = [0.0] * 3
    for x, yi in zip(features, y):
        for i in range(3):
            aty[i] += x[i] * yi
            for j in range(3):
                ata[i][j] += x[i] * x[j]
    return solve_linear_3x3(ata, aty)


def fit_fixed_excess_bands(agg: dict[tuple[int, int], int]):
    by_t: dict[int, list[tuple[int, int]]] = defaultdict(list)
    for (r, E), count in agg.items():
        t = E - 2 * r
        by_t[t].append((r, count))
    fits = {}
    for t, vals in sorted(by_t.items()):
        vals.sort()
        if len(vals) < 3:
            continue
        features = [[r * math.log(r), float(r), 1.0] for r, _ in vals]
        y = [math.log(count) for _, count in vals]
        coeff = least_squares(features, y)
        fits[t] = (coeff, vals)
    return fits


def log_rising_ratio(k: int, r: int, N: int, lam: float) -> float:
    s = lam * N
    q = k * r
    return sum(math.log1p(i / s) for i in range(q))


def fitted_log_count(coeff: list[float], r: int) -> float:
    return coeff[0] * r * math.log(r) + coeff[1] * r + coeff[2]


def diagonal_report(k: int, fits, Ns: list[int], rhos: list[float], lam: float):
    print(f"# Diagonal extrapolation for k={k}, lambda={lam}")
    print("WARNING: fitted from exact small-r fixed-excess bands only.")
    print("rho,N,r,t,E,log_count_fit,G,G_over_a")
    for rho in rhos:
        for N in Ns:
            a = N ** (1.0 + 1.0 / k)
            r = max(1, int(math.floor(rho * a)))
            penalty = log_rising_ratio(k, r, N, lam)
            best = None
            for t, (coeff, _vals) in fits.items():
                E = 2 * r + t
                log_count = fitted_log_count(coeff, r)
                G = log_count - (E / 2.0) * math.log(N) - penalty
                candidate = (G, t, E, log_count)
                if best is None or candidate > best:
                    best = candidate
            if best is None:
                continue
            G, t, E, log_count = best
            print(
                f"{rho},{N},{r},{t},{E},{log_count:.6g},"
                f"{G:.6g},{G / a:.6g}"
            )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--k", type=int, default=2)
    parser.add_argument(
        "--csv",
        type=Path,
        default=Path(__file__).with_name("spectrum_k2_exact.csv"),
    )
    parser.add_argument("--lambda", dest="lam", type=float, default=1.0)
    parser.add_argument(
        "--N", type=int, nargs="*", default=[50, 200, 1000, 4000]
    )
    parser.add_argument(
        "--rho", type=float, nargs="*", default=[0.5, 1.0, 2.0]
    )
    args = parser.parse_args()

    rows = read_rows(args.csv, args.k)
    agg = aggregate_by_energy(rows)
    fits = fit_fixed_excess_bands(agg)

    print(f"# Exact aggregate bands from {args.csv}")
    for (r, E), count in sorted(agg.items()):
        print(f"band r={r} E={E} count={count}")
    print("\n# Fixed-excess fits: log N_r(2r+t) = a r log r + b r + c")
    for t, (coeff, vals) in sorted(fits.items()):
        print(
            f"t={t}: a={coeff[0]:.6g} b={coeff[1]:.6g} c={coeff[2]:.6g}; "
            f"points={vals}"
        )
    print()
    diagonal_report(args.k, fits, args.N, args.rho, args.lam)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
