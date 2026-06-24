#!/usr/bin/env python3
"""Sensitivity grid for proportional-ray CL fits.

The proportional_ray_fit.py script reports one choice of alpha grid, matching
window, and r cutoff.  This wrapper runs a small family of such choices and
records the least favorable fitted ray for each.  It is a robustness diagnostic
for the finite-data extrapolation, not a proof of CL.
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


def best_ray_for_config(
    *,
    csv_path: Path,
    k: int,
    min_r: int,
    alpha_min: float,
    alpha_max: float,
    alpha_step: float,
    window: float,
    min_points: int,
):
    agg = read_aggregate(csv_path, k)
    by_r: dict[int, list[tuple[int, int]]] = defaultdict(list)
    for (r, E), count in agg.items():
        if r >= min_r:
            by_r[r].append((E, count))

    rows = []
    for target in frange(alpha_min, alpha_max, alpha_step):
        chosen = []
        for r in sorted(by_r):
            candidates = sorted(by_r[r], key=lambda item: abs(item[0] / r - target))
            if not candidates:
                continue
            E, count = candidates[0]
            alpha = E / r
            if abs(alpha - target) <= window:
                chosen.append((r, E, alpha, count))
        if len(chosen) < min_points:
            continue

        xs = [1 / math.log(r) for r, _E, _alpha, _count in chosen]
        betas = [beta_emp(r, count) for r, _E, _alpha, count in chosen]
        fit = linear_fit(xs, betas)
        if fit is None:
            continue
        beta_intercept, beta_slope = fit
        mean_alpha = sum(alpha for _r, _E, alpha, _count in chosen) / len(chosen)
        fitted_margin = leading_margin_from_beta(k, mean_alpha, beta_intercept)
        latest = chosen[-1]
        latest_margin = leading_margin(k, latest[0], latest[1], latest[3])
        max_emp_margin = max(
            leading_margin(k, r, E, count) for r, E, _alpha, count in chosen
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
                "latest_alpha": latest[2],
                "latest_margin": latest_margin,
                "max_emp_margin": max_emp_margin,
            }
        )

    if not rows:
        return None
    best = max(rows, key=lambda row: row["fitted_margin"])
    return best | {"num_rays": len(rows)}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--k", type=int, default=2)
    parser.add_argument(
        "--csv",
        type=Path,
        default=Path(__file__).with_name("spectrum_k2_character.csv"),
    )
    parser.add_argument("--alpha-min", type=float, default=2.0)
    parser.add_argument("--alpha-max", type=float, default=6.0)
    parser.add_argument("--min-points", type=int, default=6)
    parser.add_argument("--min-r-values", type=int, nargs="*", default=[10, 12, 14, 16])
    parser.add_argument("--alpha-steps", type=float, nargs="*", default=[0.2, 0.25])
    parser.add_argument("--windows", type=float, nargs="*", default=[0.11, 0.13, 0.17, 0.2])
    args = parser.parse_args()

    print(f"# Proportional-ray sensitivity grid from {args.csv} for k={args.k}")
    print("# finite-data extrapolation only; not a proof of CL")
    print(
        "min_r,alpha_step,window,num_rays,best_target_alpha,best_mean_alpha,"
        "best_beta_intercept,best_fitted_margin,latest_alpha,latest_margin,"
        "max_emp_margin"
    )
    summaries = []
    for min_r in args.min_r_values:
        for alpha_step in args.alpha_steps:
            for window in args.windows:
                best = best_ray_for_config(
                    csv_path=args.csv,
                    k=args.k,
                    min_r=min_r,
                    alpha_min=args.alpha_min,
                    alpha_max=args.alpha_max,
                    alpha_step=alpha_step,
                    window=window,
                    min_points=args.min_points,
                )
                if best is None:
                    continue
                summaries.append((min_r, alpha_step, window, best))
                print(
                    f"{min_r},{alpha_step:.9g},{window:.9g},{best['num_rays']},"
                    f"{best['target']:.9g},{best['mean_alpha']:.9g},"
                    f"{best['beta_intercept']:.9g},{best['fitted_margin']:.9g},"
                    f"{best['latest_alpha']:.9g},{best['latest_margin']:.9g},"
                    f"{best['max_emp_margin']:.9g}"
                )

    if summaries:
        min_r, alpha_step, window, best = max(
            summaries, key=lambda item: item[3]["fitted_margin"]
        )
        print()
        print("# Least favorable sensitivity-grid configuration")
        print(
            "min_r,alpha_step,window,best_target_alpha,best_mean_alpha,"
            "best_fitted_margin,latest_alpha,latest_margin,max_emp_margin"
        )
        print(
            f"{min_r},{alpha_step:.9g},{window:.9g},{best['target']:.9g},"
            f"{best['mean_alpha']:.9g},{best['fitted_margin']:.9g},"
            f"{best['latest_alpha']:.9g},{best['latest_margin']:.9g},"
            f"{best['max_emp_margin']:.9g}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
