#!/usr/bin/env python3
"""Entropy threshold on the k=6 balanced remaining strip.

This is a proof-target calculator, not an enumerator.

For a connected `k=6` component on `t` blocks in the balanced leftover strip

    g_+ = g_- = g,
    11/9 < g/t < 13/10,

the leading local energy density is

    alpha = 4 + 4(g/t).

If the number of such connected components has leading exponent

    count(t,g,g) = exp((beta + o(1)) t log t),

then a pure macroscopic component family can threaten CL only if

    beta > T_6(alpha) = (6/7) (1 + alpha/2).

The current min-genus upper envelope gives beta <= 1 + 3(g/t).  This script
prints the threshold and the remaining room between that envelope and the
threshold.
"""

from __future__ import annotations

import argparse

from k6_remaining_arithmetic import balanced_rows


def threshold_k6(alpha: float) -> float:
    return (6 / 7) * (1 + alpha / 2)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--t-max", type=int, default=80)
    parser.add_argument("--t-min", type=int, default=2)
    args = parser.parse_args()

    if args.t_min < 2:
        raise SystemExit("t-min must be at least 2")
    if args.t_max < args.t_min:
        raise SystemExit("t-max must be at least t-min")

    print("# k=6 balanced strip entropy threshold")
    print("# proof-target calculator; not an enumerator")
    print("# beta_required = T_6(alpha); min_genus_bound = 1 + 3g/t")
    print(
        "t,g,y,alpha_leading,beta_required,min_genus_bound,"
        "envelope_room,one_witness_margin"
    )

    rows = 0
    worst_room = None
    for t in range(args.t_min, args.t_max + 1):
        for g in balanced_rows(t):
            rows += 1
            y = g / t
            alpha = 4 + 4 * y
            beta_required = threshold_k6(alpha)
            min_bound = 1 + 3 * y
            room = min_bound - beta_required
            one_witness_margin = -beta_required
            row = (room, t, g, y, alpha, beta_required, min_bound)
            if worst_room is None or row > worst_room:
                worst_room = row
            print(
                f"{t},{g},{y:.12g},{alpha:.12g},{beta_required:.12g},"
                f"{min_bound:.12g},{room:.12g},{one_witness_margin:.12g}"
            )

    print()
    print("# Summary")
    print("t_min,t_max,rows,worst_room_t,worst_room_g,worst_room")
    if worst_room is None:
        print(f"{args.t_min},{args.t_max},0,,,")
    else:
        room, t, g, _y, _alpha, _beta_required, _min_bound = worst_room
        print(f"{args.t_min},{args.t_max},{rows},{t},{g},{room:.12g}")
    print()
    print("# Interpretation")
    print("one_witness_beta=0")
    print("one_witness_margin=-beta_required")
    print("positive_envelope_room_means_current_upper_bound_does_not_close")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
