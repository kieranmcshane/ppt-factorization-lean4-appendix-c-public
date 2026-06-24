#!/usr/bin/env python3
"""Tail-window trend diagnostics for the CL proportional-energy profile.

This script is not a proof of the diagonal entropy bound.  It is a finite-data
diagnostic aimed at the main failure mode: a higher-energy band whose empirical
entropy keeps the leading CL margin near or above zero as r grows.

For each exact r it computes

    beta_emp(r,E) = log N_r(E) / (r log r)

and the leading diagonal CL margin

    beta_emp(r,E) - (k/(k+1)) * E/(2r) - k/(k+1).

It then reports the least favorable band in moving tail windows.  If CL were
being threatened by a visible proportional band in the exact data, these window
maxima would stop drifting downward or turn positive.  The output remains
finite-data evidence only.
"""

from __future__ import annotations

import argparse
import csv
import math
from collections import defaultdict
from pathlib import Path


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


def leading_margin(k: int, r: int, E: int, count: int) -> float:
    logn_coeff = k / (k + 1)
    return beta_emp(r, count) - logn_coeff * (E / (2 * r)) - logn_coeff


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
    parser.add_argument(
        "--tail-starts",
        type=int,
        nargs="*",
        default=[6, 10, 14, 18, 22, 24, 26],
    )
    parser.add_argument("--recent-count", type=int, default=8)
    args = parser.parse_args()

    agg = read_aggregate(args.csv, args.k)
    by_r: dict[int, list[tuple[int, int]]] = defaultdict(list)
    for (r, E), count in agg.items():
        by_r[r].append((E, count))

    per_r = []
    for r in sorted(by_r):
        rows = sorted(by_r[r])
        peak_E, peak_count = max(rows, key=lambda item: item[1])
        worst_E, worst_count = max(
            rows, key=lambda item: leading_margin(args.k, r, item[0], item[1])
        )
        per_r.append(
            {
                "r": r,
                "peak_E": peak_E,
                "peak_alpha": peak_E / r,
                "peak_count": peak_count,
                "worst_E": worst_E,
                "worst_alpha": worst_E / r,
                "worst_beta": beta_emp(r, worst_count),
                "worst_margin": leading_margin(args.k, r, worst_E, worst_count),
                "worst_count": worst_count,
            }
        )

    max_r = max(row["r"] for row in per_r)
    print(f"# Tail-window CL profile trends from {args.csv} for k={args.k}")
    print("# finite-data diagnostic only; negative margins do not prove CL")
    print()

    print("# Window maxima of the leading margin")
    print("tail_start,r,E,alpha,beta_emp,leading_margin,count")
    for start in args.tail_starts:
        candidates = [row for row in per_r if row["r"] >= start]
        if not candidates:
            continue
        row = max(candidates, key=lambda item: item["worst_margin"])
        print(
            f"{start},{row['r']},{row['worst_E']},{row['worst_alpha']:.9g},"
            f"{row['worst_beta']:.9g},{row['worst_margin']:.9g},"
            f"{row['worst_count']}"
        )

    print()
    print(f"# Per-r least favorable bands near the frontier r >= {max(2, max_r - args.recent_count + 1)}")
    print("r,E,alpha,beta_emp,leading_margin,count")
    for row in per_r[-args.recent_count :]:
        print(
            f"{row['r']},{row['worst_E']},{row['worst_alpha']:.9g},"
            f"{row['worst_beta']:.9g},{row['worst_margin']:.9g},"
            f"{row['worst_count']}"
        )

    print()
    print(f"# Entropy peak bands near the frontier r >= {max(2, max_r - args.recent_count + 1)}")
    print("r,E_peak,alpha_peak,count_peak")
    for row in per_r[-args.recent_count :]:
        print(
            f"{row['r']},{row['peak_E']},{row['peak_alpha']:.9g},"
            f"{row['peak_count']}"
        )

    recent = per_r[-args.recent_count :]
    xs_inv_log = [1 / math.log(row["r"]) for row in recent]
    ys_margin = [row["worst_margin"] for row in recent]
    fit = linear_fit(xs_inv_log, ys_margin)
    print()
    print("# Heuristic recent-window extrapolation")
    print("model,intercept,slope,note")
    if fit is None:
        print("margin_vs_inv_log_r,,,insufficient data")
    else:
        intercept, slope = fit
        print(
            "margin_vs_inv_log_r,"
            f"{intercept:.9g},{slope:.9g},"
            "fit on recent exact per-r least-favorable margins; not a proof"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
