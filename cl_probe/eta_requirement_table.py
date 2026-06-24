#!/usr/bin/env python3
"""Eta requirements for the remaining unbounded-component frontier.

This table separates two thresholds that are easy to conflate.

1. One-sided target.  For a connected component with t -> infinity and
   y = g_+/t, the critical eta=2 one-sided inequality compares

       1 + eta*y <= 2(1+y).

   In the benchmark-open connected window, y > 1 and
   y < (k-3)/2.  The worst one-sided eta allowed over that open window is

       eta <= 2 + 2/(k-3),

   interpreted as absent when the open window is empty.  Thus eta=2 is not
   the obstruction at leading one-sided scale; the boundary issue is global.

2. Direct component strategy for full CL.  Combining the component map/genus
   envelope with the three-cycle-count envelope gives the stricter threshold

       eta_crit(k) = (k^2 - 3k + 1)/(k^2 - 4k + 1).

   This is the threshold used by k_map_genus_frontier.py.  It is 19/13 at
   k=6 and tends to 1 as k grows.

The script is a proof-target calculator, not a proof of CL.
"""

from __future__ import annotations

import argparse


def eta_critical_component(k: int) -> float | None:
    denom = k * k - 4 * k + 1
    if denom <= 0:
        return None
    return (k * k - 3 * k + 1) / denom


def one_sided_open_y_range(k: int) -> tuple[float, float] | None:
    # As t -> infinity, benchmark-open components need
    #   y = g/t >= 1 and 1+y < (k-1)/2.
    high = (k - 3) / 2
    if high <= 1:
        return None
    return 1.0, high


def worst_one_sided_eta(k: int) -> float | None:
    interval = one_sided_open_y_range(k)
    if interval is None:
        return None
    _low, high = interval
    return 2 + 1 / high


def fmt(value: float | None) -> str:
    if value is None:
        return "none"
    return f"{value:.12g}"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--table-k-max", type=int, default=20)
    args = parser.parse_args()

    print("# Eta requirements for the unbounded-component frontier")
    print(
        "k,open_y_range,worst_one_sided_eta_allowed,"
        "direct_component_eta_crit,interpretation"
    )
    for k in range(2, args.table_k_max + 1, 2):
        interval = one_sided_open_y_range(k)
        if interval is None:
            y_range = "empty"
            interpretation = "no benchmark-open connected y-window"
        else:
            low, high = interval
            y_range = f"{low:.12g}<y<{high:.12g}"
            interpretation = "unbounded component sizes require new entropy input"
        print(
            f"{k},{y_range},{fmt(worst_one_sided_eta(k))},"
            f"{fmt(eta_critical_component(k))},{interpretation}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
