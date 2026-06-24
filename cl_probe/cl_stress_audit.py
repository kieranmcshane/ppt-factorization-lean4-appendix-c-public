#!/usr/bin/env python3
"""Consolidated finite-data stress audit for the CL diagonal probes.

This command reruns the headline diagnostics used in CODEX_RESULTS.md:

* fixed-excess diagonal extrapolation;
* empirical proportional-band leading margins;
* empirical margins in the remaining central window E/r <= 2k;
* moving tail-window profile maxima;
* proportional-ray sensitivity grid;
* proportional-ray held-out backtest.

It exits nonzero if any tested diagnostic reports a positive margin.  Passing
this audit is finite-data evidence only; it is not a proof of CL.
"""

from __future__ import annotations

import argparse
import csv
import math
from collections import defaultdict
from pathlib import Path

from analyze_cl import (
    aggregate_by_energy,
    fit_fixed_excess_bands,
    fitted_log_count,
    log_rising_ratio,
    read_rows,
)
from profile_cl import diagonal_leading_margin
from proportional_ray_backtest import choose_ray_points
from proportional_ray_fit import (
    beta_emp,
    frange,
    leading_margin,
    leading_margin_from_beta,
    linear_fit,
)
from proportional_ray_sensitivity import best_ray_for_config


def csv_summary(path: Path, k: int) -> tuple[int, int]:
    rows = 0
    max_r = 0
    with path.open() as f:
        for row in csv.DictReader(f):
            if int(row["k"]) != k:
                continue
            rows += 1
            max_r = max(max_r, int(row["r"]))
    return rows, max_r


def fixed_excess_audit(
    *, csv_path: Path, k: int, lam: float, Ns: list[int], rhos: list[float]
):
    rows = read_rows(csv_path, k)
    fits = fit_fixed_excess_bands(aggregate_by_energy(rows))
    best = None
    for rho in rhos:
        for N in Ns:
            a = N ** (1.0 + 1.0 / k)
            r = max(1, int(math.floor(rho * a)))
            penalty = log_rising_ratio(k, r, N, lam)
            for t, (coeff, _vals) in fits.items():
                E = 2 * r + t
                log_count = fitted_log_count(coeff, r)
                G = log_count - (E / 2.0) * math.log(N) - penalty
                candidate = {
                    "rho": rho,
                    "N": N,
                    "r": r,
                    "t": t,
                    "E": E,
                    "G_over_a": G / a,
                }
                if best is None or candidate["G_over_a"] > best["G_over_a"]:
                    best = candidate
    return best


def aggregate_by_r(csv_path: Path, k: int):
    agg: dict[tuple[int, int], int] = defaultdict(int)
    with csv_path.open() as f:
        for row in csv.DictReader(f):
            if int(row["k"]) != k:
                continue
            agg[(int(row["r"]), int(row["E"]))] += int(row["count"])
    by_r: dict[int, list[tuple[int, int]]] = defaultdict(list)
    for (r, E), count in agg.items():
        by_r[r].append((E, count))
    return by_r


def proportional_tail_audit(*, csv_path: Path, k: int, tail_min_r: int):
    by_r = aggregate_by_r(csv_path, k)
    best = None
    for r, rows in by_r.items():
        if r < tail_min_r:
            continue
        for E, count in rows:
            margin = diagonal_leading_margin(k, r, E, count)
            candidate = {
                "r": r,
                "E": E,
                "alpha": E / r,
                "beta": beta_emp(r, count),
                "margin": margin,
            }
            if best is None or margin > best["margin"]:
                best = candidate
    return best


def central_window_audit(
    *, csv_path: Path, k: int, tail_min_r: int, max_alpha: float
):
    by_r = aggregate_by_r(csv_path, k)
    best = None
    for r, rows in by_r.items():
        if r < tail_min_r:
            continue
        for E, count in rows:
            alpha = E / r
            if alpha > max_alpha:
                continue
            margin = diagonal_leading_margin(k, r, E, count)
            candidate = {
                "r": r,
                "E": E,
                "alpha": alpha,
                "beta": beta_emp(r, count),
                "margin": margin,
            }
            if best is None or margin > best["margin"]:
                best = candidate
    return best


def trend_window_audit(*, csv_path: Path, k: int, tail_starts: list[int]):
    by_r = aggregate_by_r(csv_path, k)
    per_r = []
    for r in sorted(by_r):
        rows = sorted(by_r[r])
        worst_E, worst_count = max(
            rows, key=lambda item: diagonal_leading_margin(k, r, item[0], item[1])
        )
        per_r.append(
            {
                "r": r,
                "E": worst_E,
                "alpha": worst_E / r,
                "beta": beta_emp(r, worst_count),
                "margin": diagonal_leading_margin(k, r, worst_E, worst_count),
            }
        )
    best = None
    for start in tail_starts:
        candidates = [row for row in per_r if row["r"] >= start]
        if not candidates:
            continue
        row = max(candidates, key=lambda item: item["margin"])
        candidate = {"tail_start": start, **row}
        if best is None or candidate["margin"] > best["margin"]:
            best = candidate
    return best


def ray_sensitivity_audit(
    *,
    csv_path: Path,
    k: int,
    min_r_values: list[int],
    alpha_steps: list[float],
    windows: list[float],
    alpha_min: float,
    alpha_max: float,
    min_points: int,
):
    best_all = None
    for min_r in min_r_values:
        for alpha_step in alpha_steps:
            for window in windows:
                best = best_ray_for_config(
                    csv_path=csv_path,
                    k=k,
                    min_r=min_r,
                    alpha_min=alpha_min,
                    alpha_max=alpha_max,
                    alpha_step=alpha_step,
                    window=window,
                    min_points=min_points,
                )
                if best is None:
                    continue
                candidate = {
                    "min_r": min_r,
                    "alpha_step": alpha_step,
                    "window": window,
                    "target": best["target"],
                    "mean_alpha": best["mean_alpha"],
                    "margin": best["fitted_margin"],
                    "latest_margin": best["latest_margin"],
                }
                if best_all is None or candidate["margin"] > best_all["margin"]:
                    best_all = candidate
    return best_all


def ray_backtest_audit(
    *,
    csv_path: Path,
    k: int,
    min_r: int,
    alpha_min: float,
    alpha_max: float,
    alpha_step: float,
    window: float,
    train_max_values: list[int],
    min_train_points: int,
    min_test_points: int,
):
    best_pred = None
    best_over = None
    for target in frange(alpha_min, alpha_max, alpha_step):
        points = choose_ray_points(
            csv_path=csv_path, k=k, target=target, min_r=min_r, window=window
        )
        if len(points) < min_train_points + min_test_points:
            continue
        for train_max in train_max_values:
            train = [point for point in points if point[0] <= train_max]
            test = [point for point in points if point[0] > train_max]
            if len(train) < min_train_points or len(test) < min_test_points:
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
                pred_margin = leading_margin_from_beta(k, alpha, pred_beta)
                actual_margin = leading_margin(k, r, E, count)
                test_rows.append((r, alpha, pred_margin, actual_margin))
            max_pred = max(row[2] for row in test_rows)
            max_over = max(row[2] - row[3] for row in test_rows)
            latest = test_rows[-1]
            mean_alpha = sum(alpha for _r, _E, alpha, _count in points) / len(points)
            pred_candidate = {
                "target": target,
                "train_max": train_max,
                "mean_alpha": mean_alpha,
                "margin": max_pred,
                "latest_pred": latest[2],
                "latest_actual": latest[3],
            }
            over_candidate = {
                "target": target,
                "train_max": train_max,
                "mean_alpha": mean_alpha,
                "overprediction": max_over,
                "latest_pred": latest[2],
                "latest_actual": latest[3],
            }
            if best_pred is None or max_pred > best_pred["margin"]:
                best_pred = pred_candidate
            if best_over is None or max_over > best_over["overprediction"]:
                best_over = over_candidate
    return best_pred, best_over


def fail_if_positive(name: str, value: float, failures: list[str]) -> None:
    if value > 0:
        failures.append(f"{name} is positive: {value:.9g}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--k", type=int, default=2)
    parser.add_argument(
        "--csv",
        type=Path,
        default=Path(__file__).with_name("spectrum_k2_character.csv"),
    )
    parser.add_argument("--lambda", dest="lam", type=float, default=1.0)
    parser.add_argument("--N", type=int, nargs="*", default=[50, 200, 1000, 4000])
    parser.add_argument("--rho", type=float, nargs="*", default=[0.5, 1.0, 2.0])
    args = parser.parse_args()

    rows, max_r = csv_summary(args.csv, args.k)
    fixed = fixed_excess_audit(
        csv_path=args.csv, k=args.k, lam=args.lam, Ns=args.N, rhos=args.rho
    )
    proportional = proportional_tail_audit(csv_path=args.csv, k=args.k, tail_min_r=6)
    central = central_window_audit(
        csv_path=args.csv, k=args.k, tail_min_r=6, max_alpha=2.0 * args.k
    )
    trend = trend_window_audit(
        csv_path=args.csv, k=args.k, tail_starts=[6, 10, 14, 18, 22, 24, 26]
    )
    ray = ray_sensitivity_audit(
        csv_path=args.csv,
        k=args.k,
        min_r_values=[10, 12, 14, 16],
        alpha_steps=[0.2, 0.25],
        windows=[0.11, 0.13, 0.17, 0.2],
        alpha_min=2.0,
        alpha_max=6.0,
        min_points=6,
    )
    backtest_pred, backtest_over = ray_backtest_audit(
        csv_path=args.csv,
        k=args.k,
        min_r=10,
        alpha_min=3.0,
        alpha_max=6.0,
        alpha_step=0.25,
        window=0.13,
        train_max_values=[18, 20, 22, 24],
        min_train_points=6,
        min_test_points=2,
    )

    failures: list[str] = []
    fail_if_positive("fixed_excess_G_over_a", fixed["G_over_a"], failures)
    fail_if_positive("proportional_empirical_margin", proportional["margin"], failures)
    if central is None:
        failures.append("central_window has no rows")
    else:
        fail_if_positive("central_window_margin", central["margin"], failures)
    fail_if_positive("trend_window_margin", trend["margin"], failures)
    fail_if_positive("ray_sensitivity_fitted_margin", ray["margin"], failures)
    fail_if_positive("ray_backtest_predicted_margin", backtest_pred["margin"], failures)

    print("# CL finite-data stress audit")
    print("# Passing this audit is evidence only; it is not a proof of CL.")
    print(f"csv={args.csv}")
    print(f"k={args.k}, rows={rows}, max_r={max_r}")
    print(
        "fixed_excess_best="
        f"rho:{fixed['rho']} N:{fixed['N']} r:{fixed['r']} "
        f"t:{fixed['t']} E:{fixed['E']} G_over_a:{fixed['G_over_a']:.9g}"
    )
    print(
        "proportional_empirical_worst="
        f"r:{proportional['r']} E:{proportional['E']} "
        f"alpha:{proportional['alpha']:.9g} margin:{proportional['margin']:.9g}"
    )
    if central is not None:
        print(
            "central_window_worst="
            f"max_alpha:{2.0 * args.k:.9g} r:{central['r']} E:{central['E']} "
            f"alpha:{central['alpha']:.9g} margin:{central['margin']:.9g}"
        )
    print(
        "trend_window_worst="
        f"tail_start:{trend['tail_start']} r:{trend['r']} "
        f"alpha:{trend['alpha']:.9g} margin:{trend['margin']:.9g}"
    )
    print(
        "ray_sensitivity_worst="
        f"min_r:{ray['min_r']} alpha_step:{ray['alpha_step']:.9g} "
        f"window:{ray['window']:.9g} target:{ray['target']:.9g} "
        f"mean_alpha:{ray['mean_alpha']:.9g} margin:{ray['margin']:.9g}"
    )
    print(
        "ray_backtest_worst_predicted="
        f"target:{backtest_pred['target']:.9g} train_max:{backtest_pred['train_max']} "
        f"mean_alpha:{backtest_pred['mean_alpha']:.9g} "
        f"margin:{backtest_pred['margin']:.9g}"
    )
    print(
        "ray_backtest_worst_overprediction="
        f"target:{backtest_over['target']:.9g} train_max:{backtest_over['train_max']} "
        f"mean_alpha:{backtest_over['mean_alpha']:.9g} "
        f"overprediction:{backtest_over['overprediction']:.9g}"
    )
    if failures:
        print("audit_status=FAIL")
        for failure in failures:
            print(f"failure={failure}")
        return 1
    print("audit_status=PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
