#!/usr/bin/env python3
"""Sanity-check one-sided defect counts from a defect CSV.

This is not a proof.  It aggregates rows produced by

    ./cl_probe/bin/cl_spectrum --defect-csv

by one-sided plus defect and reports the exponential base A required for a
bound of the form

    count(r, plus_defect = 2g) <= A^r * r^(eta*g).

The intended use is to stress small exact data against the global one-sided
genus target recorded in `genus_frontier.py`.
"""

from __future__ import annotations

import argparse
import csv
from collections import defaultdict
from pathlib import Path


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("csv", type=Path)
    parser.add_argument("--eta", type=float, default=2.0)
    args = parser.parse_args()

    by_plus: dict[tuple[int, int], int] = defaultdict(int)
    with args.csv.open() as f:
        for row in csv.DictReader(f):
            r = int(row["r"])
            plus = int(row["plus_defect"])
            minus = int(row["minus_defect"])
            energy = int(row["E"])
            count = int(row["count"])
            if plus + minus != energy:
                raise ValueError(f"bad defect sum at r={r}, E={energy}")
            if plus % 2 != 0:
                raise ValueError(f"plus defect is not even: {plus}")
            by_plus[(r, plus)] += count

    print("# One-sided plus-defect sanity check")
    print("# target: count <= A^r * r^(eta*g), plus_defect=2g")
    print(f"# eta={args.eta:.12g}")
    print("r,plus_defect,g,count,A_needed")

    worst: tuple[float, int, int, int, int] | None = None
    for (r, plus), count in sorted(by_plus.items()):
        g = plus // 2
        if r <= 0:
            raise ValueError("r must be positive")
        denominator = r ** (args.eta * g)
        base = (count / denominator) ** (1 / r)
        if worst is None or base > worst[0]:
            worst = (base, r, plus, g, count)
        print(f"{r},{plus},{g},{count},{base:.12g}")

    assert worst is not None
    base, r, plus, g, count = worst
    print()
    print("# Worst required exponential base")
    print("r,plus_defect,g,count,A_needed")
    print(f"{r},{plus},{g},{count},{base:.12g}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
