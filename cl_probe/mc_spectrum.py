#!/usr/bin/env python3
"""Monte Carlo active-spectrum probe for CL.

This is not an exact enumerator and never proves CL.  It samples uniform
permutations in S_{kr}, applies the same active/energy definitions as the
exact enumerator, and reports estimated active counts by (j,h,E).

The purpose is to stress the proportional-energy profile just beyond the
largest exact brute-force values, especially for k=4 where exact r=4 would
require enumerating 16! permutations.
"""

from __future__ import annotations

import argparse
import itertools
import math
from collections import Counter

import numpy as np


def gamma_perm(k: int, r: int) -> tuple[int, ...]:
    g = list(range(k * r))
    for block in range(r):
        base = block * k
        for j in range(k):
            g[base + j] = base + ((j + 1) % k)
    return tuple(g)


def inverse_perm(p: tuple[int, ...]) -> tuple[int, ...]:
    out = [0] * len(p)
    for i, value in enumerate(p):
        out[value] = i
    return tuple(out)


def compose(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(a[b[i]] for i in range(len(b)))


def cycle_count_one(p: tuple[int, ...]) -> int:
    seen = [False] * len(p)
    cycles = 0
    for i in range(len(p)):
        if seen[i]:
            continue
        cycles += 1
        j = i
        while not seen[j]:
            seen[j] = True
            j = p[j]
    return cycles


def cycle_counts_batch(perms: np.ndarray) -> np.ndarray:
    batch, n = perms.shape
    idx = np.arange(n)
    mn = np.broadcast_to(idx, (batch, n)).copy()
    cur = mn.copy()
    for _ in range(n):
        cur = np.take_along_axis(perms, cur, axis=1)
        np.minimum(mn, cur, out=mn)
    return (mn == idx).sum(axis=1)


def genus_zero_block_perms(k: int) -> set[tuple[int, ...]]:
    g = gamma_perm(k, 1)
    gi = inverse_perm(g)
    out = set()
    for p in itertools.permutations(range(k)):
        energy = (
            2 * k
            + 2
            - cycle_count_one(compose(g, p))
            - cycle_count_one(compose(p, gi))
            - 2 * cycle_count_one(p)
        )
        if energy == 0:
            out.add(tuple(p))
    return out


class DSU:
    def __init__(self, n: int):
        self.parent = list(range(n))

    def find(self, x: int) -> int:
        while self.parent[x] != x:
            self.parent[x] = self.parent[self.parent[x]]
            x = self.parent[x]
        return x

    def unite(self, a: int, b: int) -> None:
        ra = self.find(a)
        rb = self.find(b)
        if ra != rb:
            self.parent[ra] = rb


def active_and_components(
    p: list[int], g: tuple[int, ...], k: int, genus_zero: set[tuple[int, ...]]
) -> tuple[bool, int]:
    n = len(p)
    dsu = DSU(n)
    for i in range(n):
        dsu.unite(i, p[i])
        dsu.unite(i, g[i])

    components: dict[int, list[int]] = {}
    for i in range(n):
        components.setdefault(dsu.find(i), []).append(i)

    for elems in components.values():
        if len(elems) != k:
            continue
        elems.sort()
        base = elems[0]
        if base % k != 0:
            continue
        if elems != list(range(base, base + k)):
            continue
        restricted = []
        block = True
        for j in range(k):
            image = p[base + j]
            if image < base or image >= base + k:
                block = False
                break
            restricted.append(image - base)
        if block and tuple(restricted) in genus_zero:
            return False, len(components)

    return True, len(components)


def leading_margin(k: int, r: int, energy: int, log_count: float) -> float:
    beta = log_count / (r * math.log(r))
    logn_coeff = k / (k + 1)
    return beta - logn_coeff * energy / (2 * r) - logn_coeff


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--k", type=int, required=True)
    parser.add_argument("--r", type=int, required=True)
    parser.add_argument("--samples", type=int, default=200_000)
    parser.add_argument("--chunk", type=int, default=50_000)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--summary-min-hits", type=int, default=20)
    args = parser.parse_args()

    if args.r <= 1:
        raise SystemExit("the r log r diagnostic needs r >= 2")

    n = args.k * args.r
    g = gamma_perm(args.k, args.r)
    gi = inverse_perm(g)
    g_array = np.asarray(g, dtype=np.int64)
    gi_array = np.asarray(gi, dtype=np.int64)
    genus_zero = genus_zero_block_perms(args.k)
    rng = np.random.default_rng(args.seed)

    rows: Counter[tuple[int, int, int]] = Counter()
    active_hits = 0
    seen = 0

    while seen < args.samples:
        batch = min(args.chunk, args.samples - seen)
        perms = np.argsort(rng.random((batch, n)), axis=1).astype(np.int64)
        c_pi = cycle_counts_batch(perms)
        c_gamma_pi = cycle_counts_batch(g_array[perms])
        c_pi_gamma_inv = cycle_counts_batch(perms[:, gi_array])
        energies = 2 * args.k * args.r + 2 * args.r - c_gamma_pi - c_pi_gamma_inv - 2 * c_pi

        for idx in range(batch):
            p = perms[idx].tolist()
            active, comps = active_and_components(p, g, args.k, genus_zero)
            if not active:
                continue
            energy = int(energies[idx])
            j = args.r - comps
            h = (energy - 4 * j) // 2
            rows[(j, h, energy)] += 1
            active_hits += 1
        seen += batch

    log_factorial = math.lgamma(n + 1)
    print("# Monte Carlo active spectrum")
    print("# finite-sample diagnostic only; not a proof of CL")
    print(f"k={args.k},r={args.r},n={n},samples={seen},active_hits={active_hits},seed={args.seed}")
    print("k,r,j,h,E,hits,frequency,log_count_est,rel_se,beta_est,leading_margin_est")

    best = None
    best_supported = None
    for (j, h, energy), hits in sorted(rows.items(), key=lambda item: (item[0][2], item[0][0], item[0][1])):
        freq = hits / seen
        log_count = log_factorial + math.log(freq)
        rel_se = 1 / math.sqrt(hits)
        beta = log_count / (args.r * math.log(args.r))
        margin = leading_margin(args.k, args.r, energy, log_count)
        candidate = (margin, energy, j, h, hits, beta, log_count)
        if best is None or candidate > best:
            best = candidate
        if hits >= args.summary_min_hits and (
            best_supported is None or candidate > best_supported
        ):
            best_supported = candidate
        print(
            f"{args.k},{args.r},{j},{h},{energy},{hits},{freq:.9g},"
            f"{log_count:.9g},{rel_se:.9g},{beta:.9g},{margin:.9g}"
        )

    if best is not None:
        margin, energy, j, h, hits, beta, log_count = best
        print()
        print("# Least favorable sampled band")
        print("k,r,j,h,E,hits,log_count_est,beta_est,leading_margin_est")
        print(
            f"{args.k},{args.r},{j},{h},{energy},{hits},"
            f"{log_count:.9g},{beta:.9g},{margin:.9g}"
        )

    if best_supported is not None:
        margin, energy, j, h, hits, beta, log_count = best_supported
        print()
        print(f"# Least favorable sampled band with hits >= {args.summary_min_hits}")
        print("k,r,j,h,E,hits,log_count_est,beta_est,leading_margin_est")
        print(
            f"{args.k},{args.r},{j},{h},{energy},{hits},"
            f"{log_count:.9g},{beta:.9g},{margin:.9g}"
        )

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
