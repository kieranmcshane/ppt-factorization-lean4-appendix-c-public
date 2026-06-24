#!/usr/bin/env python3
"""Check the k=4 connected map/genus bound shape on exact small data.

This is only a sanity check.  It extracts the connected active component
spectrum from the exact active k=4 CSV and reports the exponential base `C`
needed in

    count <= C^t * t! * t^(3h),

where E = 4(t-1)+2h.
"""

from __future__ import annotations

import argparse
import math
from pathlib import Path

from connected_spectrum import connected_from_active, read_active


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--csv",
        type=Path,
        default=Path(__file__).with_name("spectrum_k4_exact.csv"),
    )
    parser.add_argument("--k", type=int, default=4)
    args = parser.parse_args()

    max_r, active = read_active(args.csv, args.k)
    connected = connected_from_active(active, max_r)

    print("# Connected map/genus bound sanity")
    print("# C_needed is defined by count = C_needed^t * t! * t^(3h)")
    print("k,t,E,h,count,C_needed")
    worst = None
    for (t, energy), count in sorted(connected.items()):
        remainder = energy - 4 * (t - 1)
        if remainder < 0 or remainder % 2 != 0:
            continue
        h = remainder // 2
        denom = math.factorial(t) * (t ** (3 * h))
        c_needed = (count / denom) ** (1 / t)
        row = (c_needed, t, energy, h, count)
        if worst is None or row > worst:
            worst = row
        print(f"{args.k},{t},{energy},{h},{count},{c_needed:.12g}")

    assert worst is not None
    c_needed, t, energy, h, count = worst
    print()
    print("# Worst exact small connected row")
    print("k,t,E,h,count,C_needed")
    print(f"{args.k},{t},{energy},{h},{count},{c_needed:.12g}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
