#!/usr/bin/env python3
"""Proportional-ray extrapolation for the CL diagonal test.

The fixed-excess fit in analyze_cl.py studies E = 2r + t.  The diagonal CL
question can also fail through proportional bands E/r ~= alpha.  This script
therefore follows approximate alpha-rays in the exact finite table and fits

    beta_emp(r,E) = log N_r(E) / (r log r)

as a function of 1/log(r).  The intercept is a crude estimate of the
asymptotic proportional entropy beta(alpha).  The leading CL margin for that
ray is then

    beta(alpha) - (k/(k+1)) * alpha/2 - k/(k+1).

This is only a finite-data extrapolation.  It is useful as a stress test for
visible higher-energy breaches, not as a proof of CL.
"""

from __future__ import annotations

import argparse
import csv
import math
from collections import defaultdict
from pathlib import Path


def frange(start: float, stop: float, step: float) -> list[float]:
    out = []
    value = start
    while value <= stop + 1e-12:
        out.append(round(value, 10))
        value += step
    return out


def read_aggregate(path: Path, k: int) -> dict[tuple[int, int], int]:
    out: dict[tuple[int, int], int] = defaultdict(int)
    with path.open() as f:
        for row in csv.DictReader(f):
            if int(row["k"]) != k:
                continue
            out[(int(row["r"]), int(row["E"]))] += int(row["count"])
    return dict(out)


def beta_emp(r: int, count: int) -> float:
    return math.log(count) / (r * math.log(r))


def leading_margin_from_beta(k: int, alpha: float, beta: float) -> float:
    logn_coeff = k / (k + 1)
    return beta - logn_coeff * (alpha / 2) - logn_coeff


def leading_margin(k: int, r: int, E: int, count: int) -> float:
    return leading_margin_from_beta(k, E / r, beta_emp(r, count))


def linear_fit(xs: list[float], ys: list[float]) -> tuple[float, float] | None:
    if len(xs) < 2:
        return None
    xbar = sum(xs) / len(xs)
    ybar = sum(ys) / len(ys)
    denom = sum((x - xbar) ** 2 for x in xs)
    if denom == 0:
        return None
    slope = sum((x - xbar) * (y - ybar) for x, y in zip(xs, ys)) / denom
    intercept = ybar - slope * xbar
    return intercept, slope


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--k", type=int, default=2)
    parser.add_argument(
        "--csv",
        type=Path,
        default=Path(__file__).with_name("spectrum_k2_character.csv"),
    )
    parser.add_argument("--min-r", type=int, default=10)
    parser.add_argument("--alpha-min", type=float, default=2.0)
    parser.add_argument("--alpha-max", type=float, default=6.0)
    parser.add_argument("--alpha-step", type=float, default=0.25)
    parser.add_argument("--window", type=float, default=0.13)
    parser.add_argument("--min-points", type=int, default=6)
    args = parser.parse_args()

    agg = read_aggregate(args.csv, args.k)
    by_r: dict[int, list[tuple[int, int]]] = defaultdict(list)
    for (r, E), count in agg.items():
        if r >= args.min_r:
            by_r[r].append((E, count))

    targets = frange(args.alpha_min, args.alpha_max, args.alpha_step)
    rows = []
    for target in targets:
        chosen = []
        for r in sorted(by_r):
            candidates = sorted(by_r[r], key=lambda item: abs(item[0] / r - target))
            if not candidates:
                continue
            E, count = candidates[0]
            alpha = E / r
            if abs(alpha - target) <= args.window:
                chosen.append((r, E, alpha, count))
        if len(chosen) < args.min_points:
            continue

        xs = [1 / math.log(r) for r, _E, _alpha, _count in chosen]
        betas = [beta_emp(r, count) for r, _E, _alpha, count in chosen]
        fit = linear_fit(xs, betas)
        if fit is None:
            continue
        beta_intercept, beta_slope = fit
        mean_alpha = sum(alpha for _r, _E, alpha, _count in chosen) / len(chosen)
        fitted_margin = leading_margin_from_beta(args.k, mean_alpha, beta_intercept)
        latest = chosen[-1]
        latest_margin = leading_margin(args.k, latest[0], latest[1], latest[3])
        max_emp_margin = max(
            leading_margin(args.k, r, E, count) for r, E, _alpha, count in chosen
        )
        rows.append(
            {
                "target": target,
                "n": len(chosen),
                "r_min": chosen[0][0],
                "r_max": chosen[-1][0],
                "mean_alpha": mean_alpha,
                "beta_intercept": beta_intercept,
                "beta_slope": beta_slope,
                "fitted_margin": fitted_margin,
                "latest_r": latest[0],
                "latest_alpha": latest[2],
                "latest_margin": latest_margin,
                "max_emp_margin": max_emp_margin,
            }
        )

    print(f"# Proportional-ray fit from {args.csv} for k={args.k}")
    print("# finite-data extrapolation only; not a proof of CL")
    print(
        "target_alpha,n,r_min,r_max,mean_alpha,beta_intercept,beta_slope,"
        "fitted_margin,latest_r,latest_alpha,latest_margin,max_emp_margin"
    )
    for row in rows:
        print(
            f"{row['target']:.9g},{row['n']},{row['r_min']},{row['r_max']},"
            f"{row['mean_alpha']:.9g},{row['beta_intercept']:.9g},"
            f"{row['beta_slope']:.9g},{row['fitted_margin']:.9g},"
            f"{row['latest_r']},{row['latest_alpha']:.9g},"
            f"{row['latest_margin']:.9g},{row['max_emp_margin']:.9g}"
        )

    if rows:
        best = max(rows, key=lambda row: row["fitted_margin"])
        print()
        print("# Least favorable fitted ray")
        print(
            "target_alpha,mean_alpha,beta_intercept,fitted_margin,"
            "latest_alpha,latest_margin,max_emp_margin"
        )
        print(
            f"{best['target']:.9g},{best['mean_alpha']:.9g},"
            f"{best['beta_intercept']:.9g},{best['fitted_margin']:.9g},"
            f"{best['latest_alpha']:.9g},{best['latest_margin']:.9g},"
            f"{best['max_emp_margin']:.9g}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
