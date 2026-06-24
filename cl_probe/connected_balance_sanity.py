#!/usr/bin/env python3
"""Classify connected bidefect rows by the one-sided balance frontier.

This script refines `connected_defect_spectrum.py`.  For each connected row it
computes

    M = t - 1,
    G = g_plus,
    H = (M + G)/t.

At eta=2, the standard map/SET benchmark closes `G <= M`; the crude cycle
bound closes `H >= (k-1)/2`.  If `t=1`, the component has only finitely many
labelled placements per block and is treated as `singleton_finite` rather than
as a genuine r log r entropy obstruction.
"""

from __future__ import annotations

import argparse
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from connected_defect_spectrum import (  # noqa: E402
    connected_from_active_defects,
    connected_genera,
    read_active_defects,
)


def classify(k: int, t: int, g_plus: int) -> str:
    merger = t - 1
    half_density = (merger + g_plus) / t
    if t == 1:
        return "singleton_finite"
    if g_plus <= merger:
        return "map_set_closes"
    if half_density >= (k - 1) / 2:
        return "cycle_closes"
    return "open_non_singleton"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("csv", type=Path)
    parser.add_argument("--k", type=int, required=True)
    parser.add_argument("--top-open", type=int, default=20)
    args = parser.parse_args()

    max_r, active = read_active_defects(args.csv, args.k)
    connected = connected_from_active_defects(active, max_r)

    rows = []
    counts: Counter[str] = Counter()
    for (t, (plus, minus)), count in sorted(connected.items()):
        g_plus, g_minus = connected_genera(t, plus, minus)
        merger = t - 1
        half_density = (merger + g_plus) / t
        status = classify(args.k, t, g_plus)
        counts[status] += 1
        rows.append((status, count, t, plus, minus, g_plus, g_minus, half_density))

    print("# Connected one-sided balance sanity")
    print(f"# k={args.k}")
    print("status,row_count")
    for status in [
        "map_set_closes",
        "cycle_closes",
        "singleton_finite",
        "open_non_singleton",
    ]:
        print(f"{status},{counts[status]}")

    print()
    print("# Connected rows")
    print("status,t,plus_defect,minus_defect,g_plus,g_minus,half_density,count")
    for status, count, t, plus, minus, g_plus, g_minus, half_density in rows:
        print(
            f"{status},{t},{plus},{minus},{g_plus},{g_minus},"
            f"{half_density:.12g},{count}"
        )

    open_rows = [row for row in rows if row[0] == "open_non_singleton"]
    print()
    print("# Largest open non-singleton rows")
    print("rank,t,plus_defect,minus_defect,g_plus,g_minus,half_density,count")
    for rank, row in enumerate(
        sorted(open_rows, key=lambda item: item[1], reverse=True)[: args.top_open],
        start=1,
    ):
        _, count, t, plus, minus, g_plus, g_minus, half_density = row
        print(
            f"{rank},{t},{plus},{minus},{g_plus},{g_minus},"
            f"{half_density:.12g},{count}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
