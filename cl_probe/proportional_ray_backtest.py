#!/usr/bin/env python3
"""Backtest proportional-ray CL extrapolations.

This is a finite-data sanity check for proportional_ray_fit.py.  For each
approximate alpha ray, fit beta_emp(r,E) against 1/log(r) using only rows up to
a training cutoff, then predict the later exact rows on that ray.  The point is
to detect a visibly over-optimistic extrapolation before using ray fits as CL
evidence.
"""

from __future__ import annotations

import argparse
import math
from collections import defaultdict
from pathlib import Path

from proportional_ray_fit import (
    beta_emp,
    frange,
    leading_margin,
    leading_margin_from_beta,
    linear_fit,
    read_aggregate,
)


def choose_ray_points(
    *,
    csv_path: Path,
    k: int,
    target: float,
    min_r: int,
    window: float,
) -> list[tuple[int, int, float, int]]:
    agg = read_aggregate(csv_path, k)
    by_r: dict[int, list[tuple[int, int]]] = defaultdict(list)
    for (r, E), count in agg.items():
        if r >= min_r:
            by_r[r].append((E, count))

    chosen = []
    for r in sorted(by_r):
        candidates = sorted(by_r[r], key=lambda item: abs(item[0] / r - target))
        if not candidates:
            continue
        E, count = candidates[0]
        alpha = E / r
        if abs(alpha - target) <= window:
            chosen.append((r, E, alpha, count))
    return chosen


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--k", type=int, default=2)
    parser.add_argument(
        "--csv",
        type=Path,
        default=Path(__file__).with_name("spectrum_k2_character.csv"),
    )
    parser.add_argument("--min-r", type=int, default=10)
    parser.add_argument("--alpha-min", type=float, default=3.0)
    parser.add_argument("--alpha-max", type=float, default=6.0)
    parser.add_argument("--alpha-step", type=float, default=0.25)
    parser.add_argument("--window", type=float, default=0.13)
    parser.add_argument("--train-max-values", type=int, nargs="*", default=[18, 20, 22, 24])
    parser.add_argument("--min-train-points", type=int, default=6)
    parser.add_argument("--min-test-points", type=int, default=2)
    args = parser.parse_args()

    rows = []
    for target in frange(args.alpha_min, args.alpha_max, args.alpha_step):
        points = choose_ray_points(
            csv_path=args.csv,
            k=args.k,
            target=target,
            min_r=args.min_r,
            window=args.window,
        )
        if len(points) < args.min_train_points + args.min_test_points:
            continue
        for train_max in args.train_max_values:
            train = [point for point in points if point[0] <= train_max]
            test = [point for point in points if point[0] > train_max]
            if len(train) < args.min_train_points or len(test) < args.min_test_points:
                continue

            xs = [1 / math.log(r) for r, _E, _alpha, _count in train]
            ys = [beta_emp(r, count) for r, _E, _alpha, count in train]
            fit = linear_fit(xs, ys)
            if fit is None:
                continue
            intercept, slope = fit

            test_rows = []
            for r, E, alpha, count in test:
                pred_beta = intercept + slope / math.log(r)
                pred_margin = leading_margin_from_beta(args.k, alpha, pred_beta)
                actual_margin = leading_margin(args.k, r, E, count)
                test_rows.append((r, alpha, pred_margin, actual_margin))

            max_pred = max(row[2] for row in test_rows)
            max_actual = max(row[3] for row in test_rows)
            max_over = max(row[2] - row[3] for row in test_rows)
            mean_abs = sum(abs(row[2] - row[3]) for row in test_rows) / len(test_rows)
            latest = test_rows[-1]
            mean_alpha = sum(alpha for _r, _E, alpha, _count in points) / len(points)
            rows.append(
                {
                    "target": target,
                    "train_max": train_max,
                    "train_n": len(train),
                    "test_n": len(test),
                    "mean_alpha": mean_alpha,
                    "fit_intercept": intercept,
                    "max_pred_margin": max_pred,
                    "max_actual_margin": max_actual,
                    "max_overprediction": max_over,
                    "mean_abs_error": mean_abs,
                    "latest_r": latest[0],
                    "latest_alpha": latest[1],
                    "latest_pred_margin": latest[2],
                    "latest_actual_margin": latest[3],
                }
            )

    print(f"# Proportional-ray backtest from {args.csv} for k={args.k}")
    print("# finite-data predictive check only; not a proof of CL")
    print(
        "target_alpha,train_max,train_n,test_n,mean_alpha,fit_intercept,"
        "max_pred_margin,max_actual_margin,max_overprediction,mean_abs_error,"
        "latest_r,latest_alpha,latest_pred_margin,latest_actual_margin"
    )
    for row in rows:
        print(
            f"{row['target']:.9g},{row['train_max']},{row['train_n']},"
            f"{row['test_n']},{row['mean_alpha']:.9g},{row['fit_intercept']:.9g},"
            f"{row['max_pred_margin']:.9g},{row['max_actual_margin']:.9g},"
            f"{row['max_overprediction']:.9g},{row['mean_abs_error']:.9g},"
            f"{row['latest_r']},{row['latest_alpha']:.9g},"
            f"{row['latest_pred_margin']:.9g},{row['latest_actual_margin']:.9g}"
        )

    if rows:
        worst_pred = max(rows, key=lambda row: row["max_pred_margin"])
        worst_over = max(rows, key=lambda row: row["max_overprediction"])
        print()
        print("# Backtest summary")
        print("kind,target_alpha,train_max,mean_alpha,value,latest_pred_margin,latest_actual_margin")
        print(
            f"largest_predicted_margin,{worst_pred['target']:.9g},"
            f"{worst_pred['train_max']},{worst_pred['mean_alpha']:.9g},"
            f"{worst_pred['max_pred_margin']:.9g},"
            f"{worst_pred['latest_pred_margin']:.9g},"
            f"{worst_pred['latest_actual_margin']:.9g}"
        )
        print(
            f"largest_overprediction,{worst_over['target']:.9g},"
            f"{worst_over['train_max']},{worst_over['mean_alpha']:.9g},"
            f"{worst_over['max_overprediction']:.9g},"
            f"{worst_over['latest_pred_margin']:.9g},"
            f"{worst_over['latest_actual_margin']:.9g}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
