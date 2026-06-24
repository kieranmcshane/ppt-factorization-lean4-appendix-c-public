#!/usr/bin/env python3
"""Targeted local search for connected bidefect witnesses.

This is a heuristic finite search, not a proof.  It tries to find a
permutation on `k*t` symbols whose connected component for `<gamma,pi>` has
the requested balanced one-sided genera `(g,g)`.

Uniform permutation sampling can miss thin high-cycle-count rows.  This script
instead performs a transposition walk on permutation images and scores the two
cycle-sum equations that define the target bidefect row.
"""

from __future__ import annotations

import argparse
import math
import random
from typing import Any


def gamma_perm(k: int, t: int) -> tuple[int, ...]:
    return tuple(block * k + ((j + 1) % k) for block in range(t) for j in range(k))


def inverse_perm(p: list[int] | tuple[int, ...]) -> tuple[int, ...]:
    out = [0] * len(p)
    for i, value in enumerate(p):
        out[value] = i
    return tuple(out)


def compose(p: list[int] | tuple[int, ...], q: list[int] | tuple[int, ...]) -> tuple[int, ...]:
    return tuple(p[q[i]] for i in range(len(p)))


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


def orbit_count(pi: list[int], gamma: tuple[int, ...]) -> int:
    dsu = DSU(len(pi))
    for i in range(len(pi)):
        dsu.unite(i, pi[i])
        dsu.unite(i, gamma[i])
    return len({dsu.find(i) for i in range(len(pi))})


def cycle_notation(p: list[int]) -> str:
    seen = [False] * len(p)
    cycles = []
    for start in range(len(p)):
        if seen[start]:
            continue
        cur = start
        cycle = []
        while not seen[cur]:
            seen[cur] = True
            cycle.append(cur)
            cur = p[cur]
        if len(cycle) > 1:
            cycles.append("(" + " ".join(str(x) for x in cycle) + ")")
    return " ".join(cycles) if cycles else "()"


def row_data(k: int, t: int, pi: list[int], gamma: tuple[int, ...], gamma_inv: tuple[int, ...]):
    n = k * t
    c_pi = cycle_count(pi)
    c_gamma_pi = cycle_count(compose(gamma, pi))
    c_pi_gamma_inv = cycle_count(compose(pi, gamma_inv))
    plus = n + t - c_pi - c_gamma_pi
    minus = n + t - c_pi - c_pi_gamma_inv
    if plus % 2 or minus % 2:
        return c_pi, c_gamma_pi, c_pi_gamma_inv, plus, minus, None, None
    g_plus = (plus - 2 * (t - 1)) // 2
    g_minus = (minus - 2 * (t - 1)) // 2
    return c_pi, c_gamma_pi, c_pi_gamma_inv, plus, minus, g_plus, g_minus


def score(
    k: int,
    t: int,
    target_g: int,
    pi: list[int],
    gamma: tuple[int, ...],
    gamma_inv: tuple[int, ...],
    connected_weight: int,
) -> tuple[int, tuple[int, int, int, int, int, int | None, int | None, int]]:
    n = k * t
    target_defect = 2 * (t - 1) + 2 * target_g
    target_sum = n + t - target_defect
    c_pi, c_gamma_pi, c_pi_gamma_inv, plus, minus, g_plus, g_minus = row_data(
        k, t, pi, gamma, gamma_inv
    )
    components = orbit_count(pi, gamma)
    penalty = abs(c_pi + c_gamma_pi - target_sum)
    penalty += abs(c_pi + c_pi_gamma_inv - target_sum)
    penalty += connected_weight * max(0, components - 1)
    return (
        penalty,
        (c_pi, c_gamma_pi, c_pi_gamma_inv, plus, minus, g_plus, g_minus, components),
    )


def random_perm(n: int, rng: random.Random) -> list[int]:
    pi = list(range(n))
    rng.shuffle(pi)
    return pi


def search_target(
    *,
    k: int,
    t: int,
    target_g: int,
    restarts: int,
    steps: int,
    seed: int,
    connected_weight: int,
    temperature: float,
) -> dict[str, Any]:
    """Run the transposition-walk search and return the best/found state.

    The search is heuristic finite evidence only.  A returned miss is not a
    proof of nonexistence; it just records the best row seen by this run.
    """

    if k < 2:
        raise ValueError("k must be at least 2")
    if t < 2:
        raise ValueError("t must be at least 2")
    if target_g < 0:
        raise ValueError("target_g must be nonnegative")
    if restarts <= 0 or steps <= 0:
        raise ValueError("restarts and steps must be positive")

    n = k * t
    gamma = gamma_perm(k, t)
    gamma_inv = inverse_perm(gamma)
    rng = random.Random(seed)
    best = None
    best_pi = None

    for restart in range(restarts):
        pi = random_perm(n, rng)
        current_score, current_data = score(
            k, t, target_g, pi, gamma, gamma_inv, connected_weight
        )
        for step in range(steps):
            i, j = rng.sample(range(n), 2)
            pi[i], pi[j] = pi[j], pi[i]
            new_score, new_data = score(
                k, t, target_g, pi, gamma, gamma_inv, connected_weight
            )
            accept = new_score <= current_score
            if not accept and temperature > 0:
                accept = rng.random() < math.exp((current_score - new_score) / temperature)
            if accept:
                current_score, current_data = new_score, new_data
            else:
                pi[i], pi[j] = pi[j], pi[i]

            row = (current_score, restart, step, current_data)
            if best is None or row < best:
                best = row
                best_pi = pi.copy()
            if current_score == 0 and current_data[-1] == 1:
                return {
                    "found": True,
                    "score": current_score,
                    "restart": restart,
                    "step": step,
                    "data": current_data,
                    "pi": pi.copy(),
                }

    assert best is not None and best_pi is not None
    best_score, restart, step, data = best
    return {
        "found": False,
        "score": best_score,
        "restart": restart,
        "step": step,
        "data": data,
        "pi": best_pi,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--k", type=int, default=6)
    parser.add_argument("--t", type=int, required=True)
    parser.add_argument("--g", type=int, required=True)
    parser.add_argument("--restarts", type=int, default=20)
    parser.add_argument("--steps", type=int, default=200000)
    parser.add_argument("--seed", type=int, default=20260617)
    parser.add_argument("--connected-weight", type=int, default=8)
    parser.add_argument("--temperature", type=float, default=0.02)
    args = parser.parse_args()

    n = args.k * args.t
    try:
        result = search_target(
            k=args.k,
            t=args.t,
            target_g=args.g,
            restarts=args.restarts,
            steps=args.steps,
            seed=args.seed,
            connected_weight=args.connected_weight,
            temperature=args.temperature,
        )
    except ValueError as exc:
        raise SystemExit(str(exc)) from exc

    print("# Targeted bidefect local search")
    print("# heuristic finite search only; not a proof of nonexistence")
    print(
        f"k={args.k},t={args.t},g={args.g},n={n},seed={args.seed},"
        f"restarts={args.restarts},steps={args.steps}"
    )
    print("status,c_pi,c_gamma_pi,c_pi_gamma_inv,plus,minus,g_plus,g_minus,components")
    data = result["data"]
    pi = result["pi"]
    if result["found"]:
        print("found," + ",".join(str(x) for x in data))
        print("permutation_image")
        print(",".join(str(x) for x in pi))
        print("permutation_cycles")
        print(cycle_notation(pi))
        return 0

    print("not_found_best," + ",".join(str(x) for x in data))
    print("best_penalty,restart,step")
    print(f"{result['score']},{result['restart']},{result['step']}")
    print("best_permutation_image")
    print(",".join(str(x) for x in pi))
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
