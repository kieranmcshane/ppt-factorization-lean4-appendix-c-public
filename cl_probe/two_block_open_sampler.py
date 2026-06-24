#!/usr/bin/env python3
"""Monte Carlo sampler for the first connected one-sided open ranges.

The first benchmark-open connected cases occur for `k=6`, two blocks, and
one-sided genus `g_+ = 2` or `3`.  This sampler draws random permutations on
two k-blocks, keeps those connected for `<gamma, pi>`, and reports the
one-sided plus-defect/genus distribution.

It is a finite random stress check, not an exact count and not a proof.
"""

from __future__ import annotations

import argparse
import random
from collections import Counter


def gamma_perm(k: int, r: int) -> list[int]:
    return [b * k + ((i + 1) % k) for b in range(r) for i in range(k)]


def compose(a: list[int], b: list[int]) -> list[int]:
    return [a[b[i]] for i in range(len(a))]


def cycle_count(p: list[int]) -> int:
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


def orbit_count(p: list[int], gamma: list[int]) -> int:
    dsu = DSU(len(p))
    for i in range(len(p)):
        dsu.unite(i, p[i])
        dsu.unite(i, gamma[i])
    return len({dsu.find(i) for i in range(len(p))})


def classify(k: int, r: int, g_plus: int) -> str:
    merger = r - 1
    half_density = (merger + g_plus) / r
    if g_plus <= merger:
        return "map_set_closes"
    if half_density >= (k - 1) / 2:
        return "cycle_closes"
    return "open_benchmark"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--k", type=int, default=6)
    parser.add_argument("--samples", type=int, default=50000)
    parser.add_argument("--seed", type=int, default=1729)
    args = parser.parse_args()

    r = 2
    n = args.k * r
    gamma = gamma_perm(args.k, r)
    rng = random.Random(args.seed)
    distribution: Counter[tuple[int, int, str]] = Counter()
    connected = 0

    for _ in range(args.samples):
        pi = list(range(n))
        rng.shuffle(pi)
        if orbit_count(pi, gamma) != 1:
            continue
        connected += 1
        pi_cycles = cycle_count(pi)
        gamma_pi_cycles = cycle_count(compose(gamma, pi))
        plus_defect = n + r - pi_cycles - gamma_pi_cycles
        if plus_defect < 2 * (r - 1) or plus_defect % 2 != 0:
            raise ValueError(f"bad connected plus defect: {plus_defect}")
        g_plus = (plus_defect - 2 * (r - 1)) // 2
        status = classify(args.k, r, g_plus)
        distribution[(plus_defect, g_plus, status)] += 1

    print("# Two-block connected one-sided sampler")
    print("# random stress check, not exact")
    print(f"# k={args.k}")
    print(f"# samples={args.samples}")
    print(f"# seed={args.seed}")
    print(f"# connected_samples={connected}")
    print("plus_defect,g_plus,status,hits,frequency_among_connected")
    for (plus_defect, g_plus, status), hits in sorted(distribution.items()):
        freq = hits / connected if connected else 0.0
        print(f"{plus_defect},{g_plus},{status},{hits},{freq:.12g}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
