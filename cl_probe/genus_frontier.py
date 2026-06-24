#!/usr/bin/env python3
"""Benchmark one-sided genus bounds against the CL proportional threshold.

Suppose a one-sided plus-defect/genus count has the form

    count(defect = 2g) <= exp(O(r)) r^(eta * g).

For a bidefect slice with total proportional energy alpha = E/r, the best
intersection bound from the two one-sided estimates is obtained at balanced
defects, giving

    beta_k(alpha) <= eta * alpha / 4.

This script compares that benchmark with the CL threshold

    beta_k(alpha) <= (k/(k+1)) * (1 + alpha/2).

It is a proof-target calculator, not an enumerator.
"""

from __future__ import annotations

import argparse


def threshold(k: int, alpha: float) -> float:
    return (k / (k + 1)) * (1 + alpha / 2)


def genus_beta(eta: float, alpha: float) -> float:
    return eta * alpha / 4


def closed_until_alpha(k: int, eta: float) -> float | None:
    """Largest alpha closed by the eta-genus benchmark.

    Returns None when the benchmark closes all nonnegative alpha.
    """

    denom = eta * (k + 1) - 2 * k
    if denom <= 0:
        return None
    return 4 * k / denom


def central_critical_eta() -> float:
    """Critical leading eta for the full central window 0 <= alpha <= 2k."""

    return 2.0


def all_alpha_critical_eta(k: int) -> float:
    """Largest eta for which the one-sided benchmark closes all alpha >= 0."""

    return 2 * k / (k + 1)


def central_window_status(k: int, eta: float) -> str:
    closed = closed_until_alpha(k, eta)
    if closed is None or closed > 2 * k:
        return "strict"
    if abs(closed - 2 * k) <= 1e-10:
        return "critical_boundary"
    return "no"


def frange(start: float, stop: float, step: float):
    value = start
    eps = step / 10
    while value <= stop + eps:
        yield round(value, 12)
        value += step


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--k", type=int, default=4)
    parser.add_argument("--eta", type=float, default=3.0)
    parser.add_argument("--alpha-min", type=float, default=2.0)
    parser.add_argument("--alpha-max", type=float, default=None)
    parser.add_argument("--alpha-step", type=float, default=0.25)
    parser.add_argument("--table-k-max", type=int, default=None)
    args = parser.parse_args()

    if args.k < 2:
        raise SystemExit("k must be at least 2")

    if args.table_k_max is not None:
        print("# One-sided genus-bound frontier")
        print(
            "k,eta,eta_central_critical,eta_all_alpha_critical,"
            "closed_until_alpha,central_window_status"
        )
        for k in range(2, args.table_k_max + 1, 2):
            closed = closed_until_alpha(k, args.eta)
            value = "all" if closed is None else f"{closed:.12g}"
            print(
                f"{k},{args.eta:.12g},{central_critical_eta():.12g},"
                f"{all_alpha_critical_eta(k):.12g},{value},"
                f"{central_window_status(k, args.eta)}"
            )
        return 0

    alpha_max = args.alpha_max
    if alpha_max is None:
        alpha_max = 2 * args.k

    closed = closed_until_alpha(args.k, args.eta)
    print(f"# eta_central_critical={central_critical_eta():.12g}")
    print(f"# eta_all_alpha_critical={all_alpha_critical_eta(args.k):.12g}")
    print(f"# central_window_status={central_window_status(args.k, args.eta)}")
    if closed is None:
        print("# closed_until_alpha=all")
    else:
        print(f"# closed_until_alpha={closed:.12g}")
    print("k,eta,alpha,genus_beta,threshold,margin")
    worst = None
    for alpha in frange(args.alpha_min, alpha_max, args.alpha_step):
        beta = genus_beta(args.eta, alpha)
        target = threshold(args.k, alpha)
        margin = beta - target
        row = (margin, alpha, beta, target)
        if worst is None or row > worst:
            worst = row
        print(
            f"{args.k},{args.eta:.12g},{alpha:.12g},"
            f"{beta:.12g},{target:.12g},{margin:.12g}"
        )

    assert worst is not None
    margin, alpha, beta, target = worst
    print()
    print("# Worst sampled genus-bound margin")
    print("k,eta,alpha,genus_beta,threshold,margin")
    print(
        f"{args.k},{args.eta:.12g},{alpha:.12g},"
        f"{beta:.12g},{target:.12g},{margin:.12g}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
