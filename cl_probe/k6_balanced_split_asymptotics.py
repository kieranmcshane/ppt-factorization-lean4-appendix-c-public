#!/usr/bin/env python3
"""Asymptotic arithmetic size of the k=6 strict split window.

This is a proof-target calculator, not a permutation enumerator.  It counts
the integer split slots left after the split-refined three-cycle-count
envelope on the balanced k=6 strip.

For y=g/t in (11/9,13/10), the continuous strict split width is

    (13 - 10y)t / 7.

Thus the expected leading cumulative arithmetic size through T is

    strict_rows    ~ (7/180) T^2,
    strict_slots   ~ (7/4860) T^3.

These are only counts of arithmetic target slots.  They do not count
permutations inside those slots.
"""

from __future__ import annotations

import argparse
from fractions import Fraction

from k6_balanced_split_window import split_slots
from k6_remaining_arithmetic import balanced_rows


STRICT_ROW_COEFF = Fraction(7, 180)
STRICT_SLOT_COEFF = Fraction(7, 4860)


def counts_through(t_max: int, t_min: int = 13) -> tuple[int, int, int, int, int]:
    balanced = strict_rows = boundary_rows = strict_slots = boundary_slots = 0
    for t in range(t_min, t_max + 1):
        for g in balanced_rows(t):
            balanced += 1
            strict, boundary = split_slots(t, g)
            if strict:
                strict_rows += 1
                strict_slots += len(strict)
            if boundary:
                boundary_rows += 1
                boundary_slots += len(boundary)
    return balanced, strict_rows, boundary_rows, strict_slots, boundary_slots


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--t-min", type=int, default=13)
    parser.add_argument(
        "--t-max-list",
        default="40,80,120,200,400",
        help="comma-separated cutoffs",
    )
    args = parser.parse_args()

    if args.t_min < 2:
        raise SystemExit("t-min must be at least 2")
    cutoffs = [int(part) for part in args.t_max_list.split(",") if part]
    if not cutoffs or any(t < args.t_min for t in cutoffs):
        raise SystemExit("all cutoffs must be at least t-min")

    print("# k=6 balanced strict split arithmetic asymptotics")
    print("# arithmetic target slots only; not permutation counts")
    print(f"# leading_strict_row_coeff={STRICT_ROW_COEFF}")
    print(f"# leading_strict_slot_coeff={STRICT_SLOT_COEFF}")
    print(
        "t_min,t_max,balanced_rows,strict_rows,boundary_rows,"
        "strict_slots,boundary_slots,"
        "strict_rows_over_T2,strict_slots_over_T3,"
        "strict_rows_over_leading,strict_slots_over_leading"
    )
    for t_max in cutoffs:
        balanced, strict_rows, boundary_rows, strict_slots, boundary_slots = counts_through(
            t_max, args.t_min
        )
        strict_rows_over_t2 = strict_rows / (t_max * t_max)
        strict_slots_over_t3 = strict_slots / (t_max * t_max * t_max)
        row_leading = float(STRICT_ROW_COEFF) * t_max * t_max
        slot_leading = float(STRICT_SLOT_COEFF) * t_max * t_max * t_max
        print(
            f"{args.t_min},{t_max},{balanced},{strict_rows},{boundary_rows},"
            f"{strict_slots},{boundary_slots},"
            f"{strict_rows_over_t2:.12g},{strict_slots_over_t3:.12g},"
            f"{strict_rows / row_leading:.12g},"
            f"{strict_slots / slot_leading:.12g}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
