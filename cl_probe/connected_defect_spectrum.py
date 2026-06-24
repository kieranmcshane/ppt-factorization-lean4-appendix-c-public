#!/usr/bin/env python3
"""Extract connected active bidefect spectra by labelled logarithm.

Input is a defect CSV produced by `cl_spectrum --defect-csv`, with rows
containing `r`, `plus_defect`, `minus_defect`, and `count`.  The active class is
a labelled SET of connected components for the orbits of `<gamma, pi>`, so the
connected bidefect spectrum is obtained by taking the logarithm of the
exponential generating function.

For a connected component on t blocks, the one-sided Euler identities predict

    plus_defect  = 2 * (t - 1 + g_plus),
    minus_defect = 2 * (t - 1 + g_minus),

with nonnegative integers g_plus and g_minus.  This script prints those genera
and fails if the parity or lower-bound check is violated.
"""

from __future__ import annotations

import argparse
import csv
import math
from collections import defaultdict
from fractions import Fraction
from pathlib import Path

Grade = tuple[int, int]
Poly = dict[Grade, Fraction]
Series = list[Poly]


def poly_add(a: Poly, b: Poly, scale: Fraction = Fraction(1)) -> Poly:
    out = dict(a)
    for grade, coeff in b.items():
        out[grade] = out.get(grade, Fraction(0)) + scale * coeff
        if out[grade] == 0:
            del out[grade]
    return out


def poly_mul(a: Poly, b: Poly) -> Poly:
    out: Poly = {}
    for (pa, ma), ca in a.items():
        for (pb, mb), cb in b.items():
            grade = (pa + pb, ma + mb)
            out[grade] = out.get(grade, Fraction(0)) + ca * cb
    return {grade: coeff for grade, coeff in out.items() if coeff}


def series_mul(a: Series, b: Series, max_r: int) -> Series:
    out: Series = [dict() for _ in range(max_r + 1)]
    for i in range(min(len(a), max_r + 1)):
        if not a[i]:
            continue
        for j in range(min(len(b), max_r + 1 - i)):
            if b[j]:
                out[i + j] = poly_add(out[i + j], poly_mul(a[i], b[j]))
    return out


def read_active_defects(
    path: Path, k: int | None
) -> tuple[int, dict[tuple[int, Grade], int]]:
    active: dict[tuple[int, Grade], int] = defaultdict(int)
    max_r = 0
    with path.open() as f:
        for row in csv.DictReader(f):
            if k is not None and int(row["k"]) != k:
                continue
            r = int(row["r"])
            plus = int(row["plus_defect"])
            minus = int(row["minus_defect"])
            energy = int(row["E"])
            count = int(row["count"])
            if plus + minus != energy:
                raise ValueError(f"bad defect sum at r={r}, E={energy}")
            active[(r, (plus, minus))] += count
            max_r = max(max_r, r)
    return max_r, dict(active)


def connected_from_active_defects(
    active: dict[tuple[int, Grade], int], max_r: int
) -> dict[tuple[int, Grade], int]:
    a: Series = [dict() for _ in range(max_r + 1)]
    a[0][(0, 0)] = Fraction(1)
    for (r, grade), count in active.items():
        a[r][grade] = a[r].get(grade, Fraction(0)) + Fraction(
            count, math.factorial(r)
        )

    b: Series = [dict(poly) for poly in a]
    b[0] = poly_add(b[0], {(0, 0): Fraction(1)}, scale=Fraction(-1))

    c: Series = [dict() for _ in range(max_r + 1)]
    power: Series = [dict(poly) for poly in b]
    for m in range(1, max_r + 1):
        scale = Fraction(1, m) if m % 2 == 1 else Fraction(-1, m)
        for r in range(max_r + 1):
            if power[r]:
                c[r] = poly_add(c[r], power[r], scale=scale)
        if m != max_r:
            power = series_mul(power, b, max_r)

    connected: dict[tuple[int, Grade], int] = {}
    for r in range(1, max_r + 1):
        factor = math.factorial(r)
        for grade, coeff in c[r].items():
            value = coeff * factor
            if value.denominator != 1:
                raise ArithmeticError((r, grade, value))
            connected[(r, grade)] = int(value)
    return connected


def connected_genera(t: int, plus: int, minus: int) -> tuple[int, int]:
    plus_excess = plus - 2 * (t - 1)
    minus_excess = minus - 2 * (t - 1)
    if plus_excess < 0 or minus_excess < 0:
        raise ValueError((t, plus, minus, "defect below connected minimum"))
    if plus_excess % 2 != 0 or minus_excess % 2 != 0:
        raise ValueError((t, plus, minus, "bad connected defect parity"))
    return plus_excess // 2, minus_excess // 2


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("csv", type=Path)
    parser.add_argument("--k", type=int, default=None)
    parser.add_argument("--top", type=int, default=12)
    args = parser.parse_args()

    max_r, active = read_active_defects(args.csv, args.k)
    connected = connected_from_active_defects(active, max_r)

    print("# Active aggregate by bidefect")
    print("r,plus_defect,minus_defect,count")
    for (r, (plus, minus)), count in sorted(active.items()):
        print(f"{r},{plus},{minus},{count}")

    print()
    print("# Connected active bidefect spectrum")
    print("r,plus_defect,minus_defect,g_plus,g_minus,count")
    worst_rows = []
    for (r, (plus, minus)), count in sorted(connected.items()):
        g_plus, g_minus = connected_genera(r, plus, minus)
        worst_rows.append((count, r, plus, minus, g_plus, g_minus))
        print(f"{r},{plus},{minus},{g_plus},{g_minus},{count}")

    print()
    print("# Largest connected bidefect rows")
    print("rank,r,plus_defect,minus_defect,g_plus,g_minus,count")
    for rank, (count, r, plus, minus, g_plus, g_minus) in enumerate(
        sorted(worst_rows, reverse=True)[: args.top], start=1
    ):
        print(f"{rank},{r},{plus},{minus},{g_plus},{g_minus},{count}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
