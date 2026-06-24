#!/usr/bin/env python3
"""Small finite-permutation explorer for the U-AUB-02 Aubrun route.

This is a conjecture finder, not Lean evidence.  It enumerates permutations of
`n = m + 1` points, records the two Cayley defects against the long cycle, and
profiles the left-tight slice used by the current Biane/noncrossing frontier.
"""

from __future__ import annotations

import argparse
from collections import Counter
from itertools import permutations
from math import factorial


Perm = tuple[int, ...]


def compose(sigma: Perm, tau: Perm) -> Perm:
    return tuple(sigma[tau[i]] for i in range(len(sigma)))


def invert(sigma: Perm) -> Perm:
    inv = [0] * len(sigma)
    for i, j in enumerate(sigma):
        inv[j] = i
    return tuple(inv)


def long_cycle(n: int) -> Perm:
    return tuple((i + 1) % n for i in range(n))


def cycles(perm: Perm) -> list[list[int]]:
    n = len(perm)
    seen = [False] * n
    out: list[list[int]] = []
    for start in range(n):
        if seen[start]:
            continue
        cur: list[int] = []
        x = start
        while not seen[x]:
            seen[x] = True
            cur.append(x)
            x = perm[x]
        out.append(cur)
    return out


def cycle_count(perm: Perm) -> int:
    return len(cycles(perm))


def classes(perm: Perm) -> list[int]:
    cls = [0] * len(perm)
    for idx, cyc in enumerate(cycles(perm)):
        for x in cyc:
            cls[x] = idx
    return cls


def same(cls: list[int], x: int, y: int) -> bool:
    return cls[x] == cls[y]


def plus_defect(perm: Perm) -> int:
    """Cayley geodesic defect for `π` and `γπ`.

    The zero-defect left-tight condition is
    `#cycles(π) + #cycles(γπ) = n + 1`.
    """

    n = len(perm)
    gamma = long_cycle(n)
    return (n + 1) - cycle_count(perm) - cycle_count(compose(gamma, perm))


def minus_defect(perm: Perm) -> int:
    n = len(perm)
    gamma_inv = invert(long_cycle(n))
    return (n + 1) - cycle_count(perm) - cycle_count(compose(gamma_inv, perm))


def left_tight(perm: Perm) -> bool:
    return plus_defect(perm) == 0


def crossing_count(perm: Perm) -> int:
    cls = classes(perm)
    out = 0
    n = len(perm)
    for a in range(n):
        for b in range(a + 1, n):
            for c in range(b + 1, n):
                for d in range(c + 1, n):
                    if same(cls, a, c) and same(cls, b, d) and not same(cls, a, b):
                        out += 1
    return out


def summarize(n: int) -> None:
    pair_counts: Counter[tuple[int, int]] = Counter()
    plus_counts: Counter[int] = Counter()
    left_tight_count = 0
    left_tight_crossings = 0

    for perm in permutations(range(n)):
        p = tuple(perm)
        a = plus_defect(p)
        b = minus_defect(p)
        pair_counts[(a, b)] += 1
        plus_counts[a] += 1
        if a == 0:
            left_tight_count += 1
            left_tight_crossings += crossing_count(p)

    print(f"n={n}  permutations={factorial(n)}")
    print("  plus-defect counts:")
    for defect, count in sorted(plus_counts.items()):
        print(f"    a={defect}: {count}")
    print("  bidefect counts:")
    for (a, b), count in sorted(pair_counts.items()):
        print(f"    a={a}, b={b}: {count}")
    print(f"  left-tight plus-defect-zero permutations: {left_tight_count}")
    print(f"  total crossing hypotheses inside left-tight slice: {left_tight_crossings}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-n", type=int, default=7)
    parser.add_argument("--n", type=int, default=None)
    args = parser.parse_args()

    ns = [args.n] if args.n is not None else range(2, args.max_n + 1)
    for idx, n in enumerate(ns):
        if idx:
            print()
        summarize(n)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
