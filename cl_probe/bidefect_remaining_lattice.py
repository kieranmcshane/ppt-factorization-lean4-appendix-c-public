#!/usr/bin/env python3
"""Integer bidefect rows left by the min-genus intersection route.

This is a proof-target calculator, not an enumerator and not an existence
result.  It lists integer pairs `(g_+, g_-)` for connected non-singleton
components on `t` blocks that are still in the asymptotic pre-cycle window and
are not closed by the current min-genus intersection envelope.

Coordinates:

    s = (g_+ + g_-)/t,
    m = min(g_+, g_-)/t,
    alpha_leading = 4 + 2s.

The cycle-count envelope closes rows with

    alpha_leading >= cycle_crossing_alpha(k).

The min-genus route with exponent `eta_min` closes a row when

    1 + eta_min*m <= T_k(4+2s),

where `T_k(alpha)=k/(k+1)(1+alpha/2)` is the local CL threshold.
"""

from __future__ import annotations

import argparse
from collections import defaultdict


def threshold(k: int, alpha: float) -> float:
    return (k / (k + 1)) * (1 + alpha / 2)


def cycle_crossing_alpha(k: int) -> float | None:
    if k < 4:
        return None
    return (2 * k * k - 4 * k - 2) / (k - 1)


def s_cycle(k: int) -> float | None:
    crossing = cycle_crossing_alpha(k)
    if crossing is None:
        return None
    return max(0.0, (crossing - 4) / 2)


def row_margin(k: int, t: int, gp: int, gm: int, eta_min: float) -> float:
    s = (gp + gm) / t
    m = min(gp, gm) / t
    return 1 + eta_min * m - threshold(k, 4 + 2 * s)


def row_status(k: int, t: int, gp: int, gm: int, eta_min: float) -> str:
    sc = s_cycle(k)
    if sc is None:
        return "no_cycle_window"
    s = (gp + gm) / t
    if s >= sc - 1e-12:
        return "cycle_closes"
    if row_margin(k, t, gp, gm, eta_min) <= 1e-12:
        return "min_genus_closes"
    return "remaining_candidate"


def candidate_rows(k: int, t_max: int, eta_min: float, only_open: bool):
    sc = s_cycle(k)
    if sc is None:
        return
    for t in range(2, t_max + 1):
        max_sum = int(sc * t)
        while max_sum / t >= sc - 1e-12:
            max_sum -= 1
        for gp in range(max_sum + 1):
            for gm in range(gp, max_sum - gp + 1):
                if gp == 0 and gm == 0:
                    continue
                status = row_status(k, t, gp, gm, eta_min)
                if only_open and status != "remaining_candidate":
                    continue
                yield t, gp, gm, status


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--k", type=int, default=6)
    parser.add_argument("--t-max", type=int, default=20)
    parser.add_argument("--eta-min", type=float, default=3.0)
    parser.add_argument("--all-rows", action="store_true")
    args = parser.parse_args()

    if args.k < 2:
        raise SystemExit("k must be at least 2")
    if args.t_max < 2:
        raise SystemExit("t-max must be at least 2")
    if args.eta_min <= 0:
        raise SystemExit("eta-min must be positive")

    sc = s_cycle(args.k)
    print("# Remaining integer bidefect lattice")
    print("# candidate rows only; this is not an existence theorem")
    print(f"# k={args.k}")
    if sc is None:
        print("# no positive cycle-count obstruction window")
        return 0
    print(f"# cycle_crossing_alpha={cycle_crossing_alpha(args.k):.12g}")
    print(f"# s_cycle={sc:.12g}")
    print(f"# eta_min={args.eta_min:.12g}")
    print(
        "k,t,g_plus,g_minus,s,min_ratio,alpha_leading,"
        "threshold,beta_min_genus,margin,status"
    )

    rows_by_t: dict[int, int] = defaultdict(int)
    first = None
    worst = None
    for t, gp, gm, status in candidate_rows(
        args.k, args.t_max, args.eta_min, only_open=not args.all_rows
    ):
        s = (gp + gm) / t
        m = min(gp, gm) / t
        alpha = 4 + 2 * s
        target = threshold(args.k, alpha)
        beta = 1 + args.eta_min * m
        margin = beta - target
        print(
            f"{args.k},{t},{gp},{gm},{s:.12g},{m:.12g},{alpha:.12g},"
            f"{target:.12g},{beta:.12g},{margin:.12g},{status}"
        )
        if status == "remaining_candidate":
            rows_by_t[t] += 1
            row = (t, gp, gm, s, m, alpha, margin)
            if first is None:
                first = row
            if worst is None or margin > worst[-1]:
                worst = row

    print()
    print("# Summary")
    print("k,t_max,eta_min,remaining_rows,first_t,status")
    total = sum(rows_by_t.values())
    if first is None:
        print(f"{args.k},{args.t_max},{args.eta_min:.12g},0,,no_remaining_rows")
    else:
        print(
            f"{args.k},{args.t_max},{args.eta_min:.12g},{total},"
            f"{first[0]},remaining_rows_present"
        )
        print()
        print("# First remaining row")
        print("k,t,g_plus,g_minus,s,min_ratio,alpha_leading,margin")
        t, gp, gm, s, m, alpha, margin = first
        print(
            f"{args.k},{t},{gp},{gm},{s:.12g},{m:.12g},"
            f"{alpha:.12g},{margin:.12g}"
        )
        print()
        print("# Worst remaining row in listed range")
        print("k,t,g_plus,g_minus,s,min_ratio,alpha_leading,margin")
        assert worst is not None
        t, gp, gm, s, m, alpha, margin = worst
        print(
            f"{args.k},{t},{gp},{gm},{s:.12g},{m:.12g},"
            f"{alpha:.12g},{margin:.12g}"
        )
        print()
        print("# Remaining row counts by t")
        print("t,count")
        for t in sorted(rows_by_t):
            print(f"{t},{rows_by_t[t]}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
