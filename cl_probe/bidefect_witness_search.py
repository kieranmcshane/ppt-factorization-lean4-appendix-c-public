#!/usr/bin/env python3
"""Search for an explicit connected bidefect witness.

This is a finite witness finder, not an asymptotic estimate.  It samples
uniform permutations on `k*t` symbols until it finds a connected permutation
whose one-sided genera are the requested `(g_+,g_-)`.  The output includes
the permutation image and independent verification data.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


def gamma_perm(k: int, t: int) -> tuple[int, ...]:
    return tuple(block * k + ((j + 1) % k) for block in range(t) for j in range(k))


def inverse_perm(p: tuple[int, ...]) -> tuple[int, ...]:
    out = [0] * len(p)
    for i, value in enumerate(p):
        out[value] = i
    return tuple(out)


def cycle_count(p: list[int] | tuple[int, ...]) -> int:
    seen = [False] * len(p)
    total = 0
    for start in range(len(p)):
        if seen[start]:
            continue
        total += 1
        cur = start
        while not seen[cur]:
            seen[cur] = True
            cur = p[cur]
    return total


def compose(p: tuple[int, ...] | list[int], q: tuple[int, ...] | list[int]) -> tuple[int, ...]:
    return tuple(p[q[i]] for i in range(len(p)))


class DSU:
    def __init__(self, n: int):
        self.parent = list(range(n))

    def find(self, x: int) -> int:
        while self.parent[x] != x:
            self.parent[x] = self.parent[self.parent[x]]
            x = self.parent[x]
        return x

    def unite(self, a: int, b: int) -> None:
        a = self.find(a)
        b = self.find(b)
        if a != b:
            self.parent[a] = b


def connected_for_gamma(pi: list[int], gamma: tuple[int, ...]) -> bool:
    dsu = DSU(len(pi))
    for i in range(len(pi)):
        dsu.unite(i, pi[i])
        dsu.unite(i, gamma[i])
    root = dsu.find(0)
    return all(dsu.find(i) == root for i in range(1, len(pi)))


def cycle_notation(p: list[int]) -> str:
    seen = [False] * len(p)
    cycles = []
    for start in range(len(p)):
        if seen[start]:
            continue
        cycle = []
        cur = start
        while not seen[cur]:
            seen[cur] = True
            cycle.append(cur)
            cur = p[cur]
        if len(cycle) > 1:
            cycles.append("(" + " ".join(str(x) for x in cycle) + ")")
    return " ".join(cycles) if cycles else "()"


def threshold(k: int, alpha: float) -> float:
    return (k / (k + 1)) * (1 + alpha / 2)


def cycle_crossing_alpha(k: int) -> float | None:
    if k < 4:
        return None
    return (2 * k * k - 4 * k - 2) / (k - 1)


def min_genus_margin(k: int, t: int, g_plus: int, g_minus: int, eta_min: float) -> float:
    s = (g_plus + g_minus) / t
    m = min(g_plus, g_minus) / t
    return 1 + eta_min * m - threshold(k, 4 + 2 * s)


def bidefect_data(k: int, t: int, pi: list[int], gamma: tuple[int, ...], gamma_inv: tuple[int, ...]):
    n = k * t
    c_pi = cycle_count(pi)
    c_gamma_pi = cycle_count(compose(gamma, pi))
    c_pi_gamma_inv = cycle_count(compose(pi, gamma_inv))
    plus = n + t - c_pi - c_gamma_pi
    minus = n + t - c_pi - c_pi_gamma_inv
    if plus % 2 or minus % 2:
        raise ValueError((plus, minus, "bad parity"))
    g_plus = (plus - 2 * (t - 1)) // 2
    g_minus = (minus - 2 * (t - 1)) // 2
    return c_pi, c_gamma_pi, c_pi_gamma_inv, plus, minus, g_plus, g_minus


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--k", type=int, default=6)
    parser.add_argument("--t", type=int, default=4)
    parser.add_argument("--g-plus", type=int, required=True)
    parser.add_argument("--g-minus", type=int, required=True)
    parser.add_argument("--max-samples", type=int, default=200000)
    parser.add_argument("--chunk", type=int, default=10000)
    parser.add_argument("--seed", type=int, default=1730)
    parser.add_argument("--eta-min", type=float, default=3.0)
    args = parser.parse_args()

    if args.k < 2:
        raise SystemExit("k must be at least 2")
    if args.t < 2:
        raise SystemExit("t must be at least 2")
    if args.g_plus < 0 or args.g_minus < 0:
        raise SystemExit("target genera must be nonnegative")
    if args.max_samples <= 0 or args.chunk <= 0:
        raise SystemExit("max-samples and chunk must be positive")

    n = args.k * args.t
    gamma = gamma_perm(args.k, args.t)
    gamma_inv = inverse_perm(gamma)
    rng = np.random.default_rng(args.seed)
    seen = 0
    connected_hits = 0

    while seen < args.max_samples:
        batch = min(args.chunk, args.max_samples - seen)
        perms = np.argsort(rng.random((batch, n)), axis=1).astype(np.int64)
        for row in perms:
            seen += 1
            pi = row.tolist()
            if not connected_for_gamma(pi, gamma):
                continue
            connected_hits += 1
            (
                c_pi,
                c_gamma_pi,
                c_pi_gamma_inv,
                plus,
                minus,
                g_plus,
                g_minus,
            ) = bidefect_data(args.k, args.t, pi, gamma, gamma_inv)
            if g_plus != args.g_plus or g_minus != args.g_minus:
                continue

            alpha_exact = (plus + minus) / args.t
            alpha_leading = 4 + 2 * (g_plus + g_minus) / args.t
            crossing = cycle_crossing_alpha(args.k)
            margin = min_genus_margin(args.k, args.t, g_plus, g_minus, args.eta_min)
            print("# Connected bidefect witness")
            print("# finite witness only; not an asymptotic estimate")
            print(
                f"k={args.k},t={args.t},n={n},seed={args.seed},"
                f"attempts={seen},connected_hits={connected_hits}"
            )
            print(
                f"target_g_plus={args.g_plus},target_g_minus={args.g_minus},"
                f"eta_min={args.eta_min:.12g}"
            )
            print(
                "c_pi,c_gamma_pi,c_pi_gamma_inv,plus_defect,minus_defect,"
                "g_plus,g_minus,alpha_exact,alpha_leading,cycle_crossing_alpha,"
                "min_genus_margin"
            )
            print(
                f"{c_pi},{c_gamma_pi},{c_pi_gamma_inv},{plus},{minus},"
                f"{g_plus},{g_minus},{alpha_exact:.12g},{alpha_leading:.12g},"
                f"{'none' if crossing is None else f'{crossing:.12g}'},"
                f"{margin:.12g}"
            )
            print("permutation_image")
            print(",".join(str(x) for x in pi))
            print("permutation_cycles")
            print(cycle_notation(pi))
            return 0

    print("# Connected bidefect witness")
    print("# no witness found")
    print(
        f"k={args.k},t={args.t},n={n},seed={args.seed},"
        f"attempts={seen},connected_hits={connected_hits}"
    )
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
