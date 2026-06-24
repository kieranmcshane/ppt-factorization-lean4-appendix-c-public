#!/usr/bin/env python3
"""Bounded-component finite-type frontier for the one-sided CL target.

This is a proof-target calculator, not a proof of CL.

Fix a finite catalogue of connected component types whose block sizes are
bounded independently of the global number of blocks r.  Repeating such
components in a labelled SET contributes only the set-partition entropy

    beta_+ = M / r

at the leading r log r scale, where M = r - c is the merger count.  The
internal component genera are finite-type data and affect only exp(O(r)).

For a component of size t and one-sided genus g,

    M/t = (t - 1)/t,
    G/t = g/t,
    delta_+ / r = 2(M+G)/r.

Thus the eta=2 one-sided target has leading margin

    finite_type_beta - 2(M+G)/r
      = (t-1)/t - 2(t-1+g)/t < 0

for every nontrivial fixed component type.  In particular, fixed-size
benchmark-open rows such as the exact k=6,t=2,g=2,3 rows are not diagonal
obstructions by themselves.  The remaining danger must involve component sizes
that grow with r, or a different entropy source.
"""

from __future__ import annotations

import argparse
import math


def open_range(k: int, t: int) -> tuple[int, int] | None:
    if t < 2:
        return None
    low = t
    upper_exclusive = ((k - 3) * t) / 2 + 1
    high = math.ceil(upper_exclusive) - 1
    if low > high:
        return None
    return low, high


def finite_type_beta(t: int) -> float:
    return (t - 1) / t


def eta_two_target(t: int, g: int) -> float:
    return 2 * (t - 1 + g) / t


def crude_map_set_beta(t: int, g: int) -> float:
    return (t - 1) / t + 3 * g / t


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--k", type=int, default=6)
    parser.add_argument("--t-max", type=int, default=12)
    parser.add_argument("--all-rows", action="store_true")
    args = parser.parse_args()

    if args.k < 2:
        raise SystemExit("k must be at least 2")

    print("# Bounded-component finite-type frontier")
    print("# finite_type_beta=(t-1)/t; target_eta2=2(t-1+g)/t")
    print("# Rows are connected component types; fixed finite catalogues cost exp(O(r))")
    print(
        "k,t,g,status,finite_type_beta,crude_map_set_beta,"
        "eta2_target,finite_type_margin,crude_margin"
    )
    rows = 0
    worst = None
    for t in range(2, args.t_max + 1):
        interval = open_range(args.k, t)
        if interval is None:
            if args.all_rows:
                print(f"{args.k},{t},,empty,,,,,")
            continue
        low, high = interval
        for g in range(low, high + 1):
            beta_finite = finite_type_beta(t)
            beta_crude = crude_map_set_beta(t, g)
            target = eta_two_target(t, g)
            finite_margin = beta_finite - target
            crude_margin = beta_crude - target
            row = (finite_margin, args.k, t, g, beta_finite, beta_crude, target)
            if worst is None or row > worst:
                worst = row
            rows += 1
            print(
                f"{args.k},{t},{g},benchmark_open,"
                f"{beta_finite:.12g},{beta_crude:.12g},{target:.12g},"
                f"{finite_margin:.12g},{crude_margin:.12g}"
            )

    print()
    print("# Summary")
    print("k,t_max,open_rows,worst_finite_type_margin,status")
    if worst is None:
        print(f"{args.k},{args.t_max},0,,no_open_bounded_rows")
    else:
        finite_margin, _k, t, g, _beta_finite, _beta_crude, _target = worst
        status = "finite_type_closes" if finite_margin < 0 else "needs_attention"
        print(
            f"{args.k},{args.t_max},{rows},{finite_margin:.12g},{status}"
        )
        print()
        print("# Worst finite-type row")
        print("k,t,g,finite_type_margin")
        print(f"{args.k},{t},{g},{finite_margin:.12g}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
