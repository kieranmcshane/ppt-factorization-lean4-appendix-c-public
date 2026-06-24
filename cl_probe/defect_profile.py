#!/usr/bin/env python3
"""Summarize bidefect/cycle-count CSV output from cl_spectrum.

Input is produced by:

    ./cl_probe/bin/cl_spectrum --k 4 --r-min 2 --r-max 2 --defect-csv

The script is diagnostic only.  It helps inspect the low central window left by
the cycle-count envelope by showing which bidefect splits and cycle-count
triples dominate each exact energy band.
"""

from __future__ import annotations

import argparse
import csv
from collections import Counter, defaultdict
from pathlib import Path


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("csv", type=Path)
    parser.add_argument("--top", type=int, default=8)
    args = parser.parse_args()

    by_energy: dict[tuple[int, int], int] = defaultdict(int)
    by_energy_j: dict[tuple[int, int, int], int] = defaultdict(int)
    by_defect: dict[tuple[int, int], Counter[tuple[int, int]]] = defaultdict(Counter)
    by_cycles: dict[tuple[int, int], Counter[tuple[int, int, int]]] = defaultdict(
        Counter
    )

    with args.csv.open() as f:
        for row in csv.DictReader(f):
            count = int(row["count"])
            r = int(row["r"])
            energy = int(row["E"])
            j = int(row["j"])
            plus = int(row["plus_defect"])
            minus = int(row["minus_defect"])
            pi_cycles = int(row["pi_cycles"])
            gamma_pi_cycles = int(row["gamma_pi_cycles"])
            pi_gamma_inv_cycles = int(row["pi_gamma_inv_cycles"])

            if plus + minus != energy:
                raise ValueError(
                    f"bad defect sum at E={energy}: {plus}+{minus}"
                )

            by_energy[(r, energy)] += count
            by_energy_j[(r, energy, j)] += count
            by_defect[(r, energy)][(plus, minus)] += count
            by_cycles[(r, energy)][
                (pi_cycles, gamma_pi_cycles, pi_gamma_inv_cycles)
            ] += count

    print("# Energy aggregate")
    print("r,E,count")
    for (r, energy), count in sorted(by_energy.items()):
        print(f"{r},{energy},{count}")

    print()
    print("# Energy and merge aggregate")
    print("r,E,j,count")
    for (r, energy, j), count in sorted(by_energy_j.items()):
        print(f"{r},{energy},{j},{count}")

    print()
    print("# Top bidefect splits by energy")
    print("r,E,rank,plus_defect,minus_defect,count")
    for r, energy in sorted(by_defect):
        for rank, ((plus, minus), count) in enumerate(
            by_defect[(r, energy)].most_common(args.top), start=1
        ):
            print(f"{r},{energy},{rank},{plus},{minus},{count}")

    print()
    print("# Top cycle-count triples by energy")
    print("r,E,rank,pi_cycles,gamma_pi_cycles,pi_gamma_inv_cycles,count")
    for r, energy in sorted(by_cycles):
        for rank, ((pi_cycles, gamma_pi_cycles, pi_gamma_inv_cycles), count) in (
            enumerate(by_cycles[(r, energy)].most_common(args.top), start=1)
        ):
            print(
                f"{r},{energy},{rank},{pi_cycles},{gamma_pi_cycles},"
                f"{pi_gamma_inv_cycles},{count}"
            )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
