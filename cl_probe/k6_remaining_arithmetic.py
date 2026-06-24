#!/usr/bin/env python3
"""Exact arithmetic form of the k=6 remaining bidefect window.

This is a proof-target calculator, not an enumerator.  It rewrites the
`k=6`, `eta_min=3` min-genus leftover conditions using integer arithmetic.

For a connected component on `t` blocks, enumerate pairs `g_+ <= g_-`.  The
row is before cycle-count takeover exactly when

    (g_+ + g_-)/t < 13/5.

It is not closed by the min-genus route exactly when

    1 + 3 g_+/t > (6/7) (3 + (g_+ + g_-)/t),

or equivalently

    15 g_+ - 6 g_- > 11 t.

For balanced rows `g_+=g_-=g`, this reduces to the rational interval

    11/9 < g/t < 13/10.
"""

from __future__ import annotations

import argparse
from fractions import Fraction


def is_remaining(t: int, gp: int, gm: int) -> bool:
    if not (0 <= gp <= gm):
        return False
    return 5 * (gp + gm) < 13 * t and 15 * gp - 6 * gm > 11 * t


def remaining_rows(t: int) -> list[tuple[int, int]]:
    # The pre-cycle inequality gives gp+gm < 13t/5.
    max_sum = (13 * t - 1) // 5
    out = []
    for gp in range(max_sum + 1):
        for gm in range(gp, max_sum - gp + 1):
            if is_remaining(t, gp, gm):
                out.append((gp, gm))
    return out


def balanced_rows(t: int) -> list[int]:
    out = []
    # 11/9 < g/t < 13/10.
    for g in range(0, (13 * t - 1) // 10 + 1):
        if 9 * g > 11 * t and 10 * g < 13 * t:
            out.append(g)
    return out


def balanced_interval_length(t: int) -> Fraction:
    return Fraction(7 * t, 90)


def fmt_fraction(num: int, den: int) -> str:
    return str(Fraction(num, den))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--t-max", type=int, default=80)
    parser.add_argument("--all-t", action="store_true")
    args = parser.parse_args()

    if args.t_max < 2:
        raise SystemExit("t-max must be at least 2")

    print("# k=6 remaining bidefect arithmetic window")
    print("# exact integer arithmetic; candidate rows only")
    print("# conditions: gp<=gm, 5(gp+gm)<13t, 15gp-6gm>11t")
    print("# balanced condition: 11/9 < g/t < 13/10")
    print("t,row_count,balanced_count,first_row,worst_ratio_row,balanced_g")

    total_rows = 0
    total_balanced = 0
    first_t = None
    for t in range(2, args.t_max + 1):
        rows = remaining_rows(t)
        balanced = balanced_rows(t)
        if not rows and not args.all_t:
            continue
        total_rows += len(rows)
        total_balanced += len(balanced)
        if rows and first_t is None:
            first_t = t
        if rows:
            first = rows[0]
            worst = max(rows, key=lambda row: Fraction(row[0] + row[1], t))
            first_text = f"{first[0]}:{first[1]}"
            worst_text = (
                f"{worst[0]}:{worst[1]}@"
                f"{fmt_fraction(worst[0] + worst[1], t)}"
            )
        else:
            first_text = ""
            worst_text = ""
        balanced_text = ";".join(str(g) for g in balanced)
        print(
            f"{t},{len(rows)},{len(balanced)},"
            f"{first_text},{worst_text},{balanced_text}"
        )

    print()
    print("# Summary")
    print("t_max,total_rows,total_balanced,first_t,balanced_all_t_from_13")
    if args.t_max >= 13:
        all_from_13 = all(balanced_rows(t) for t in range(13, args.t_max + 1))
        all_from_13_text = "yes" if all_from_13 else "no"
    else:
        all_from_13_text = "not_checked"
    print(
        f"{args.t_max},{total_rows},{total_balanced},"
        f"{first_t or ''},{all_from_13_text}"
    )
    print()
    print("# Balanced strip")
    print("condition,interval_length,consequence")
    print(
        "11/9<g/t<13/10,"
        f"{balanced_interval_length(1)},"
        "length is 7t/90, so every t>=13 has a balanced candidate"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
