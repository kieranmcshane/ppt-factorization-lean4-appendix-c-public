#!/usr/bin/env python3
"""Sanity-check the one-sided defect target on exact k=2 spectra.

For k=2, the fixed block permutation satisfies gamma^{-1}=gamma, so the two
one-sided defects coincide and

    plus_defect = minus_defect = E/2.

This script reads the exact `k=2` active spectrum CSV produced by
`k2_character_spectrum.py` or `k2_character_spectrum_gmp.cpp`, aggregates by
plus defect, and reports the exponential base A required for

    count(r, plus_defect = 2g) <= A^r * r^(eta*g).

It is a finite exact stress check for the one-sided genus target, not a proof.
"""

from __future__ import annotations

import argparse
import csv
from collections import defaultdict
from pathlib import Path


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "csv",
        type=Path,
        nargs="?",
        default=Path(__file__).with_name("spectrum_k2_character.csv"),
    )
    parser.add_argument("--eta", type=float, default=2.0)
    args = parser.parse_args()

    by_plus: dict[tuple[int, int], int] = defaultdict(int)
    with args.csv.open() as f:
        for row in csv.DictReader(f):
            if int(row["k"]) != 2:
                continue
            r = int(row["r"])
            energy = int(row["E"])
            count = int(row["count"])
            if energy % 2 != 0:
                raise ValueError(f"k=2 energy should be even: {energy}")
            plus = energy // 2
            if plus % 2 != 0:
                raise ValueError(f"k=2 plus defect should be even: {plus}")
            by_plus[(r, plus)] += count

    print("# k=2 one-sided defect sanity check")
    print("# target: count <= A^r * r^(eta*g), plus_defect=2g")
    print(f"# eta={args.eta:.12g}")
    print("r,plus_defect,g,count,A_needed")

    worst: tuple[float, int, int, int, int] | None = None
    by_r: dict[int, tuple[float, int, int, int, int]] = {}
    for (r, plus), count in sorted(by_plus.items()):
        g = plus // 2
        denominator = r ** (args.eta * g)
        base = (count / denominator) ** (1 / r)
        row = (base, r, plus, g, count)
        if worst is None or base > worst[0]:
            worst = row
        if r not in by_r or base > by_r[r][0]:
            by_r[r] = row
        print(f"{r},{plus},{g},{count},{base:.12g}")

    print()
    print("# Worst required exponential base by r")
    print("r,plus_defect,g,count,A_needed")
    for r, (base, _, plus, g, count) in sorted(by_r.items()):
        print(f"{r},{plus},{g},{count},{base:.12g}")

    assert worst is not None
    base, r, plus, g, count = worst
    print()
    print("# Global worst required exponential base")
    print("r,plus_defect,g,count,A_needed")
    print(f"{r},{plus},{g},{count},{base:.12g}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
