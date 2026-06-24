#!/usr/bin/env python3
"""Crude cycle-count frontier for one-sided plus-defect slices.

This is an analytic proof-target calculator.  For n=kr and

    delta_+(pi) = kr + r - #pi - #(gamma*pi),

write delta_+ = d r.  The unsigned-Stirling cycle-count bound gives

    beta_+(d) <= (k - 1 + d)/2,

because #pi/r + #(gamma*pi)/r = k + 1 - d and the number of permutations in
the slice is bounded by the smaller of the two one-cycle-count classes.

The desired one-sided genus target

    count(delta_+ = 2g) <= exp(O(r)) r^(eta*g)

would give beta_+(d) <= eta*d/2.  This script compares the crude cycle-count
bound with that target and identifies the plus-defect density above which no
topological input is needed.
"""

from __future__ import annotations

import argparse


def cycle_beta(k: int, d: float) -> float:
    return (k - 1 + d) / 2


def genus_target(eta: float, d: float) -> float:
    return eta * d / 2


def closing_density(k: int, eta: float) -> float | None:
    if eta <= 1:
        return None
    return (k - 1) / (eta - 1)


def frange(start: float, stop: float, step: float):
    value = start
    eps = step / 10
    while value <= stop + eps:
        yield round(value, 12)
        value += step


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--k", type=int, default=4)
    parser.add_argument("--eta", type=float, default=2.0)
    parser.add_argument("--d-min", type=float, default=0.0)
    parser.add_argument("--d-max", type=float, default=None)
    parser.add_argument("--d-step", type=float, default=0.5)
    parser.add_argument("--table-k-max", type=int, default=None)
    args = parser.parse_args()

    if args.k < 2:
        raise SystemExit("k must be at least 2")

    if args.table_k_max is not None:
        print("# One-sided cycle-count frontier")
        print("k,eta,closing_plus_defect_density,central_top_density,verdict")
        for k in range(2, args.table_k_max + 1, 2):
            close = closing_density(k, args.eta)
            value = "none" if close is None else f"{close:.12g}"
            verdict = (
                "reaches_top"
                if close is not None and close <= k
                else "below_top_only"
            )
            print(f"{k},{args.eta:.12g},{value},{k},{verdict}")
        return 0

    d_max = args.d_max
    if d_max is None:
        d_max = args.k
    close = closing_density(args.k, args.eta)
    if close is None:
        print("# closing_plus_defect_density=none")
    else:
        print(f"# closing_plus_defect_density={close:.12g}")
    print("k,eta,d,cycle_beta,genus_target,margin")
    worst = None
    for d in frange(args.d_min, d_max, args.d_step):
        beta = cycle_beta(args.k, d)
        target = genus_target(args.eta, d)
        margin = beta - target
        row = (margin, d, beta, target)
        if worst is None or row > worst:
            worst = row
        print(
            f"{args.k},{args.eta:.12g},{d:.12g},"
            f"{beta:.12g},{target:.12g},{margin:.12g}"
        )

    assert worst is not None
    margin, d, beta, target = worst
    print()
    print("# Worst sampled one-sided cycle-count margin")
    print("k,eta,d,cycle_beta,genus_target,margin")
    print(
        f"{args.k},{args.eta:.12g},{d:.12g},"
        f"{beta:.12g},{target:.12g},{margin:.12g}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
