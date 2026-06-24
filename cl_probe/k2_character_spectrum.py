#!/usr/bin/env python3
"""Exact k=2 active spectrum via connection coefficients.

For k=2, gamma is a fixed perfect matching.  Instead of enumerating all
permutations in S_{2r}, this script computes the total two-cycle-count
polynomial

    F_r(x,y) = sum_pi x^{#pi} y^{#(gamma*pi)}

from the character table of S_{2r}.  The labelled exponential formula then
extracts connected components with respect to <gamma, pi>; removing the
size-one components gives the active spectrum.

This is exact, but still intended as a computational probe, not a proof of CL.
"""

from __future__ import annotations

import argparse
import csv
import functools
import math
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import product
from pathlib import Path


Partition = tuple[int, ...]


def partitions(n: int, max_part: int | None = None) -> list[Partition]:
    if n == 0:
        return [()]
    if max_part is None or max_part > n:
        max_part = n
    out: list[Partition] = []
    for first in range(max_part, 0, -1):
        for rest in partitions(n - first, min(first, n - first) if n - first else 0):
            out.append((first,) + rest)
    return out


def part_size(p: Partition) -> int:
    return sum(p)


def cycle_count_of_type(p: Partition) -> int:
    return len(p)


def z_value(mu: Partition) -> int:
    counts = Counter(mu)
    z = 1
    for i, m in counts.items():
        z *= (i**m) * math.factorial(m)
    return z


def class_size(mu: Partition) -> int:
    n = part_size(mu)
    return math.factorial(n) // z_value(mu)


def dim_specht(lam: Partition) -> int:
    n = part_size(lam)
    hooks = 1
    col_heights = [sum(1 for row in lam if row > c) for c in range(max(lam, default=0))]
    for r, row_len in enumerate(lam):
        for c in range(row_len):
            hooks *= (row_len - c) + (col_heights[c] - r - 1)
    return math.factorial(n) // hooks


def subpartitions_bounded(lam: Partition, target: int) -> list[Partition]:
    rows = len(lam)
    out: list[Partition] = []

    def rec(i: int, prev: int, remaining: int, acc: list[int]) -> None:
        if i == rows:
            if remaining == 0:
                trimmed = acc[:]
                while trimmed and trimmed[-1] == 0:
                    trimmed.pop()
                out.append(tuple(trimmed))
            return
        upper = min(prev, lam[i], remaining)
        for value in range(upper, -1, -1):
            acc.append(value)
            rec(i + 1, value, remaining - value, acc)
            acc.pop()

    rec(0, 10**9, target, [])
    return out


def skew_cells(lam: Partition, nu: Partition) -> set[tuple[int, int]]:
    cells: set[tuple[int, int]] = set()
    for r, row_len in enumerate(lam):
        nu_len = nu[r] if r < len(nu) else 0
        for c in range(nu_len, row_len):
            cells.add((r, c))
    return cells


def connected(cells: set[tuple[int, int]]) -> bool:
    if not cells:
        return False
    stack = [next(iter(cells))]
    seen = {stack[0]}
    while stack:
        r, c = stack.pop()
        for nb in ((r - 1, c), (r + 1, c), (r, c - 1), (r, c + 1)):
            if nb in cells and nb not in seen:
                seen.add(nb)
                stack.append(nb)
    return len(seen) == len(cells)


def no_two_by_two(cells: set[tuple[int, int]]) -> bool:
    for r, c in cells:
        if (r + 1, c) in cells and (r, c + 1) in cells and (r + 1, c + 1) in cells:
            return False
    return True


@functools.lru_cache(maxsize=None)
def rim_hooks(lam: Partition, m: int) -> tuple[tuple[Partition, int], ...]:
    n = part_size(lam)
    if m > n:
        return ()
    hooks: list[tuple[Partition, int]] = []
    for nu in subpartitions_bounded(lam, n - m):
        cells = skew_cells(lam, nu)
        if len(cells) != m:
            continue
        if not connected(cells) or not no_two_by_two(cells):
            continue
        height = 1 + max(r for r, _ in cells) - min(r for r, _ in cells)
        hooks.append((nu, height))
    return tuple(hooks)


@functools.lru_cache(maxsize=None)
def character(lam: Partition, mu: Partition) -> int:
    if not mu:
        return 1 if part_size(lam) == 0 else 0
    m = mu[0]
    total = 0
    for nu, height in rim_hooks(lam, m):
        total += (-1 if (height - 1) % 2 else 1) * character(nu, mu[1:])
    return total


def content_cycle_transform(lam: Partition, dim: int) -> dict[int, int]:
    """Return sum_{#mu=p} |C_mu| chi_lam(mu), indexed by cycle count p.

    The Jucys--Murphy content identity gives

        sum_{sigma in S_n} x^{#cycles(sigma)} chi_lam(sigma)
          = dim(lam) * product_{cells u in lam} (x + content(u)).

    This replaces a full scan over conjugacy classes for every irreducible.
    """
    coeff = [1]
    for row, row_len in enumerate(lam):
        for col in range(row_len):
            content = col - row
            nxt = [0] * (len(coeff) + 1)
            for degree, value in enumerate(coeff):
                nxt[degree] += content * value
                nxt[degree + 1] += value
            coeff = nxt
    return {degree: dim * value for degree, value in enumerate(coeff) if value}


def total_polynomial_for_r(r: int) -> dict[tuple[int, int], int]:
    n = 2 * r
    irreps = partitions(n)
    matching_type = tuple([2] * r)
    dims = {lam: dim_specht(lam) for lam in irreps}
    nfac = math.factorial(n)
    common_den = nfac * nfac
    term_buckets: dict[tuple[int, int], int] = defaultdict(int)
    for lam in irreps:
        match_char = character(lam, matching_type)
        if match_char == 0:
            continue
        dim = dims[lam]
        if nfac % dim != 0:
            raise ArithmeticError((r, lam, dim, nfac))
        denom_multiplier = nfac // dim
        by_cycles = content_cycle_transform(lam, dim)
        for p, left in by_cycles.items():
            if left == 0:
                continue
            for q, right in by_cycles.items():
                if right:
                    term_buckets[(p, q)] += (
                        match_char * left * right * denom_multiplier
                    )
    out: dict[tuple[int, int], int] = {}
    for key, numerator in term_buckets.items():
        coeff, rem = divmod(numerator, common_den)
        if rem:
            raise ArithmeticError((r, key, numerator, common_den, rem))
        if coeff:
            out[key] = coeff
    return dict(out)


Poly = dict[tuple[int, int], Fraction]
PolyC = dict[tuple[int, int, int], Fraction]


def poly_add(a: Poly, b: Poly, scale: Fraction = Fraction(1)) -> Poly:
    out = defaultdict(Fraction)
    for key, value in a.items():
        out[key] += value
    for key, value in b.items():
        out[key] += scale * value
    return {k: v for k, v in out.items() if v}


def poly_mul(a: Poly, b: Poly) -> Poly:
    out = defaultdict(Fraction)
    for (p1, q1), v1 in a.items():
        for (p2, q2), v2 in b.items():
            out[(p1 + p2, q1 + q2)] += v1 * v2
    return {k: v for k, v in out.items() if v}


def series_mul(a: list[Poly], b: list[Poly], R: int) -> list[Poly]:
    out = [dict() for _ in range(R + 1)]
    for i in range(R + 1):
        if not a[i]:
            continue
        for j in range(R + 1 - i):
            if b[j]:
                out[i + j] = poly_add(out[i + j], poly_mul(a[i], b[j]))
    return out


def series_log(total: list[Poly], R: int) -> list[Poly]:
    # total[0] must be 1.  log(total)=log(1+u).
    u = [dict() for _ in range(R + 1)]
    u[0] = {}
    for i in range(1, R + 1):
        u[i] = total[i]
    out = [dict() for _ in range(R + 1)]
    power = [dict() for _ in range(R + 1)]
    power[0] = {(0, 0): Fraction(1)}
    for m in range(1, R + 1):
        power = series_mul(power, u, R)
        scale = Fraction(1 if m % 2 else -1, m)
        for i in range(R + 1):
            if power[i]:
                out[i] = poly_add(out[i], power[i], scale)
    return out


def polyc_add(a: PolyC, b: PolyC, scale: Fraction = Fraction(1)) -> PolyC:
    out = defaultdict(Fraction)
    for key, value in a.items():
        out[key] += value
    for key, value in b.items():
        out[key] += scale * value
    return {k: v for k, v in out.items() if v}


def polyc_mul(a: PolyC, b: PolyC) -> PolyC:
    out = defaultdict(Fraction)
    for (c1, p1, q1), v1 in a.items():
        for (c2, p2, q2), v2 in b.items():
            out[(c1 + c2, p1 + p2, q1 + q2)] += v1 * v2
    return {k: v for k, v in out.items() if v}


def seriesc_mul(a: list[PolyC], b: list[PolyC], R: int) -> list[PolyC]:
    out = [dict() for _ in range(R + 1)]
    for i in range(R + 1):
        if not a[i]:
            continue
        for j in range(R + 1 - i):
            if b[j]:
                out[i + j] = polyc_add(out[i + j], polyc_mul(a[i], b[j]))
    return out


def seriesc_exp(a: list[PolyC], R: int) -> list[PolyC]:
    out = [dict() for _ in range(R + 1)]
    out[0] = {(0, 0, 0): Fraction(1)}
    for n in range(1, R + 1):
        acc: PolyC = {}
        for i in range(1, n + 1):
            if not a[i] or not out[n - i]:
                continue
            term = polyc_mul(a[i], out[n - i])
            acc = polyc_add(acc, term, Fraction(i, 1))
        out[n] = {k: v / n for k, v in acc.items()}
    return out


def active_spectra(R: int) -> dict[int, dict[tuple[int, int], int]]:
    total: list[Poly] = [dict() for _ in range(R + 1)]
    total[0] = {(0, 0): Fraction(1)}
    for r in range(1, R + 1):
        print(f"computing total polynomial r={r}", flush=True)
        total_r = total_polynomial_for_r(r)
        total[r] = {key: Fraction(value, math.factorial(r)) for key, value in total_r.items()}
    connected = series_log(total, R)
    active_conn: list[PolyC] = [dict() for _ in range(R + 1)]
    for r in range(2, R + 1):
        active_conn[r] = {
            (1, p, q): value for (p, q), value in connected[r].items()
        }
    active = seriesc_exp(active_conn, R)
    spectra: dict[int, dict[tuple[int, int], int]] = {}
    for r in range(1, R + 1):
        table: dict[tuple[int, int], int] = defaultdict(int)
        for (components, pcycles, qcycles), value in active[r].items():
            count = value * math.factorial(r)
            if count.denominator != 1:
                raise ArithmeticError((r, components, pcycles, qcycles, count))
            j = r - components
            h = r - pcycles - qcycles + 2 * components
            table[(j, h)] += count.numerator
        spectra[r] = dict(table)
    return spectra


def write_csv(path: Path, spectra: dict[int, dict[tuple[int, int], int]]) -> None:
    with path.open("w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["k", "r", "j", "h", "E", "count"])
        for r, table in sorted(spectra.items()):
            for (j, h), count in sorted(table.items(), key=lambda item: (4 * item[0][0] + 2 * item[0][1], item[0])):
                if count:
                    writer.writerow([2, r, j, h, 4 * j + 2 * h, count])


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--r-max", type=int, default=20)
    parser.add_argument("--out", type=Path, default=Path("cl_probe/spectrum_k2_character.csv"))
    args = parser.parse_args()
    spectra = active_spectra(args.r_max)
    write_csv(args.out, spectra)
    for r, table in sorted(spectra.items()):
        total = sum(table.values())
        if total == 0:
            print(f"r={r}: no active permutations")
            continue
        print(f"r={r}: active_total={total}")
        for (j, h), count in sorted(table.items(), key=lambda item: (4 * item[0][0] + 2 * item[0][1], item[0])):
            if count:
                print(f"  j={j} h={h} E={4*j+2*h} count={count}")
    print(f"wrote {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
