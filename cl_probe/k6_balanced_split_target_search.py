#!/usr/bin/env python3
"""Heuristic search for strict k=6 balanced split slots.

This is finite search evidence only.  It targets the actual remaining
cycle-count split slots from `k6_balanced_split_window.py`:

    #pi = p,
    #(gamma*pi) = q,
    #(pi*gamma^-1) = q.

Finding a connected permutation in such a slot would populate a split not
closed by the split-refined three-cycle-count envelope.  A miss is not a proof
of emptiness.
"""

from __future__ import annotations

import argparse
import csv
import math
import random
import sys
from typing import Any

from bidefect_target_local_search import (
    gamma_perm,
    inverse_perm,
    orbit_count,
    row_data,
)
from k6_balanced_split_window import split_slots, target_sum
from k6_remaining_arithmetic import balanced_rows


FIELDNAMES = [
    "t",
    "g",
    "p",
    "q",
    "seed",
    "status",
    "best_score",
    "best_c_pi",
    "best_c_gamma_pi",
    "best_c_pi_gamma_inv",
    "best_plus",
    "best_minus",
    "best_g_plus",
    "best_g_minus",
    "best_components",
    "best_restart",
    "best_step",
    "permutation_image",
]


def row_seed(seed: int, t: int, g: int, p: int, q: int) -> int:
    return seed + 1009 * t + 9176 * g + 65537 * p + 131071 * q


def random_perm(n: int, rng: random.Random) -> list[int]:
    pi = list(range(n))
    rng.shuffle(pi)
    return pi


def score_split(
    t: int,
    p: int,
    q: int,
    pi: list[int],
    gamma: tuple[int, ...],
    gamma_inv: tuple[int, ...],
    connected_weight: int,
) -> tuple[int, tuple[int, int, int, int, int, int | None, int | None, int]]:
    c_pi, c_gamma_pi, c_pi_gamma_inv, plus, minus, g_plus, g_minus = row_data(
        6, t, pi, gamma, gamma_inv
    )
    components = orbit_count(pi, gamma)
    penalty = abs(c_pi - p)
    penalty += abs(c_gamma_pi - q)
    penalty += abs(c_pi_gamma_inv - q)
    penalty += connected_weight * max(0, components - 1)
    return (
        penalty,
        (c_pi, c_gamma_pi, c_pi_gamma_inv, plus, minus, g_plus, g_minus, components),
    )


def search_split(
    *,
    t: int,
    g: int,
    p: int,
    q: int,
    restarts: int,
    steps: int,
    seed: int,
    connected_weight: int,
    temperature: float,
) -> dict[str, Any]:
    if target_sum(t, g) != p + q:
        raise ValueError(f"target split p+q={p+q} does not match row sum")
    n = 6 * t
    gamma = gamma_perm(6, t)
    gamma_inv = inverse_perm(gamma)
    rng = random.Random(seed)
    best = None
    best_pi = None

    for restart in range(restarts):
        pi = random_perm(n, rng)
        current_score, current_data = score_split(
            t, p, q, pi, gamma, gamma_inv, connected_weight
        )
        for step in range(steps):
            i, j = rng.sample(range(n), 2)
            pi[i], pi[j] = pi[j], pi[i]
            new_score, new_data = score_split(
                t, p, q, pi, gamma, gamma_inv, connected_weight
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
            if current_score == 0:
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


def candidate_splits(t_min: int, t_max: int, include_boundary: bool) -> list[tuple[int, int, int, int]]:
    out: list[tuple[int, int, int, int]] = []
    for t in range(t_min, t_max + 1):
        for g in balanced_rows(t):
            strict, boundary = split_slots(t, g)
            slots = strict + (boundary if include_boundary else [])
            for p, q in slots:
                # The two side counts are symmetric; keep both orientations
                # because the concrete search is not symmetric in pi.
                out.append((t, g, p, q))
    return out


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--t-min", type=int, default=13)
    parser.add_argument("--t-max", type=int, default=40)
    parser.add_argument("--include-boundary", action="store_true")
    parser.add_argument("--seed", type=int, default=20260617)
    parser.add_argument("--restarts", type=int, default=8)
    parser.add_argument("--steps", type=int, default=30000)
    parser.add_argument("--temperature", type=float, default=0.05)
    parser.add_argument("--connected-weight", type=int, default=8)
    parser.add_argument(
        "--emit-permutation",
        action="store_true",
        help="emit the best permutation image, including best misses",
    )
    args = parser.parse_args()

    if args.t_min < 2:
        raise SystemExit("t-min must be at least 2")
    if args.t_max < args.t_min:
        raise SystemExit("t-max must be at least t-min")
    if args.restarts <= 0 or args.steps <= 0:
        raise SystemExit("restarts and steps must be positive")

    writer = csv.DictWriter(sys.stdout, fieldnames=FIELDNAMES, lineterminator="\n")
    writer.writeheader()
    found = 0
    rows = 0
    for t, g, p, q in candidate_splits(args.t_min, args.t_max, args.include_boundary):
        rows += 1
        seed = row_seed(args.seed, t, g, p, q)
        result = search_split(
            t=t,
            g=g,
            p=p,
            q=q,
            restarts=args.restarts,
            steps=args.steps,
            seed=seed,
            connected_weight=args.connected_weight,
            temperature=args.temperature,
        )
        if result["found"]:
            found += 1
        data = result["data"]
        writer.writerow(
            {
                "t": t,
                "g": g,
                "p": p,
                "q": q,
                "seed": seed,
                "status": "found" if result["found"] else "miss",
                "best_score": result["score"],
                "best_c_pi": data[0],
                "best_c_gamma_pi": data[1],
                "best_c_pi_gamma_inv": data[2],
                "best_plus": data[3],
                "best_minus": data[4],
                "best_g_plus": data[5],
                "best_g_minus": data[6],
                "best_components": data[7],
                "best_restart": result["restart"],
                "best_step": result["step"],
                "permutation_image": (
                    " ".join(str(x) for x in result["pi"])
                    if args.emit_permutation
                    else ""
                ),
            }
        )
    print(f"# split_targets={rows},found={found},missed={rows-found}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
