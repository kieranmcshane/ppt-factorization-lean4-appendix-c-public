#!/usr/bin/env python3
"""Cycle-count entropy envelope for the CL proportional bands.

This is an analytic, not fitted, envelope.  It uses only the three cycle
counts appearing in the energy

    E = 2kr + 2r - #(gamma*pi) - #(pi*gamma^{-1}) - 2#pi.

For n = kr, the number of permutations with q cycles is bounded by an
unsigned-Stirling estimate with leading coefficient (k - q/r) r log r.
Combining the three cycle-count constraints gives

    beta_k(alpha) <= (k - 1)/2 + alpha/4,

where alpha = E/r.  This script compares that envelope with the CL threshold

    beta_k(alpha) <= (k/(k+1)) * (1 + alpha/2).

For k=2 the envelope is strictly below the CL threshold for the full
proportional energy range.  For larger k it only closes the upper part of the
central window.
"""

from __future__ import annotations

import argparse


def beta_threshold(k: int, alpha: float) -> float:
    return (k / (k + 1)) * (1 + alpha / 2)


def cycle_count_beta_bound(k: int, alpha: float) -> float:
    return (k - 1) / 2 + alpha / 4


def margin_bound(k: int, alpha: float) -> float:
    return cycle_count_beta_bound(k, alpha) - beta_threshold(k, alpha)


def crossing_alpha(k: int) -> float | None:
    """Return the alpha where the envelope meets the CL threshold.

    If the returned value is <= 0, the envelope is below threshold throughout
    the nonnegative proportional-energy range.
    """

    if k == 1:
        return None
    return (2 * k * k - 4 * k - 2) / (k - 1)


def frange(start: float, stop: float, step: float):
    value = start
    eps = step / 10
    while value <= stop + eps:
        yield round(value, 12)
        value += step


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--k", type=int, default=2)
    parser.add_argument(
        "--table-k-max",
        type=int,
        default=None,
        help="print a summary table for even k up to this value",
    )
    parser.add_argument("--alpha-min", type=float, default=0.0)
    parser.add_argument("--alpha-max", type=float, default=None)
    parser.add_argument("--alpha-step", type=float, default=0.5)
    args = parser.parse_args()

    if args.k < 2:
        raise SystemExit("k must be at least 2")
    alpha_max = args.alpha_max
    if alpha_max is None:
        alpha_max = 2 * args.k + 2

    if args.table_k_max is not None:
        print("# Cycle-count envelope frontier by even k")
        print("k,crossing_alpha,closed_alpha_range,remaining_open_window")
        for k in range(2, args.table_k_max + 1, 2):
            cross = crossing_alpha(k)
            if cross is None or cross <= 0:
                closed = "all alpha >= 0"
                open_window = "none"
            else:
                closed = f"alpha >= {cross:.12g}"
                open_window = f"2 <= alpha < {cross:.12g}"
            print(f"{k},{cross:.12g},{closed},{open_window}")
        return 0

    print("# Cycle-count CL entropy envelope")
    print("# beta_bound = (k - 1)/2 + alpha/4")
    print("# threshold = (k/(k+1)) * (1 + alpha/2)")
    cross = crossing_alpha(args.k)
    if cross is not None:
        print(f"# crossing_alpha={cross:.12g}")
    print("k,alpha,beta_bound,beta_threshold,margin_bound")
    worst = None
    for alpha in frange(args.alpha_min, alpha_max, args.alpha_step):
        beta_bound = cycle_count_beta_bound(args.k, alpha)
        threshold = beta_threshold(args.k, alpha)
        margin = beta_bound - threshold
        row = (margin, alpha, beta_bound, threshold)
        if worst is None or row > worst:
            worst = row
        print(
            f"{args.k},{alpha:.12g},{beta_bound:.12g},"
            f"{threshold:.12g},{margin:.12g}"
        )

    assert worst is not None
    margin, alpha, beta_bound, threshold = worst
    print()
    print("# Worst sampled envelope margin")
    print("k,alpha,beta_bound,beta_threshold,margin_bound")
    print(
        f"{args.k},{alpha:.12g},{beta_bound:.12g},"
        f"{threshold:.12g},{margin:.12g}"
    )
    if margin < 0:
        print("sampled verdict: envelope is below threshold on this grid")
    else:
        print("sampled verdict: envelope does not close this grid")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
