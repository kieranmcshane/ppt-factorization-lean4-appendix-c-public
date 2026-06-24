#!/usr/bin/env python3
"""Extract connected active component spectra by the labelled exponential formula.

The active spectra count permutations on `r` labelled k-blocks.  Decomposing
such a permutation into orbits of <gamma, pi> is a labelled SET construction,
so the exponential generating functions satisfy

    A(z,u) = exp(C(z,u)),

where `u` marks the energy.  This script reads a `k,r,j,h,E,count` CSV,
aggregates by `(r,E)`, and computes the connected component counts from
`C = log A`.
"""

from __future__ import annotations

import argparse
import csv
import math
from collections import defaultdict
from fractions import Fraction
from pathlib import Path

Poly = dict[int, Fraction]
Series = list[Poly]


def poly_add(a: Poly, b: Poly, scale: Fraction = Fraction(1)) -> Poly:
    out = dict(a)
    for energy, coeff in b.items():
        out[energy] = out.get(energy, Fraction(0)) + scale * coeff
        if out[energy] == 0:
            del out[energy]
    return out


def poly_mul(a: Poly, b: Poly) -> Poly:
    out: Poly = {}
    for ea, ca in a.items():
        for eb, cb in b.items():
            out[ea + eb] = out.get(ea + eb, Fraction(0)) + ca * cb
    return {energy: coeff for energy, coeff in out.items() if coeff}


def series_mul(a: Series, b: Series, max_r: int) -> Series:
    out: Series = [dict() for _ in range(max_r + 1)]
    for i in range(min(len(a), max_r + 1)):
        if not a[i]:
            continue
        for j in range(min(len(b), max_r + 1 - i)):
            if b[j]:
                out[i + j] = poly_add(out[i + j], poly_mul(a[i], b[j]))
    return out


def read_active(path: Path, k: int | None) -> tuple[int, dict[tuple[int, int], int]]:
    active: dict[tuple[int, int], int] = defaultdict(int)
    max_r = 0
    with path.open() as f:
        for row in csv.DictReader(f):
            if k is not None and int(row["k"]) != k:
                continue
            r = int(row["r"])
            energy = int(row["E"])
            count = int(row["count"])
            active[(r, energy)] += count
            max_r = max(max_r, r)
    return max_r, dict(active)


def connected_from_active(
    active: dict[tuple[int, int], int], max_r: int
) -> dict[tuple[int, int], int]:
    # A stores EGF coefficients A_r(E)/r!, with A_0(0)=1.
    a: Series = [dict() for _ in range(max_r + 1)]
    a[0][0] = Fraction(1)
    for (r, energy), count in active.items():
        a[r][energy] = a[r].get(energy, Fraction(0)) + Fraction(
            count, math.factorial(r)
        )

    b: Series = [dict(poly) for poly in a]
    b[0] = poly_add(b[0], {0: Fraction(1)}, scale=Fraction(-1))

    c: Series = [dict() for _ in range(max_r + 1)]
    power: Series = [dict(poly) for poly in b]
    for m in range(1, max_r + 1):
        scale = Fraction(1, m) if m % 2 == 1 else Fraction(-1, m)
        for r in range(max_r + 1):
            if power[r]:
                c[r] = poly_add(c[r], power[r], scale=scale)
        if m != max_r:
            power = series_mul(power, b, max_r)

    connected: dict[tuple[int, int], int] = {}
    for r in range(1, max_r + 1):
        factor = math.factorial(r)
        for energy, coeff in c[r].items():
            value = coeff * factor
            if value.denominator != 1:
                raise ArithmeticError((r, energy, value))
            connected[(r, energy)] = int(value)
    return connected


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("csv", type=Path)
    parser.add_argument("--k", type=int, default=None)
    args = parser.parse_args()

    max_r, active = read_active(args.csv, args.k)
    connected = connected_from_active(active, max_r)

    print("# Active aggregate by energy")
    print("r,E,count")
    for (r, energy), count in sorted(active.items()):
        print(f"{r},{energy},{count}")

    print()
    print("# Connected active component spectrum")
    print("r,E,count")
    for (r, energy), count in sorted(connected.items()):
        print(f"{r},{energy},{count}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
