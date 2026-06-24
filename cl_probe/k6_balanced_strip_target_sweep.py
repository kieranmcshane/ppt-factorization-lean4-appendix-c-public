#!/usr/bin/env python3
"""Heuristic witness sweep for the k=6 balanced remaining strip.

This script is finite evidence only.  It searches the balanced candidates

    11/9 < g/t < 13/10

from the exact k=6 arithmetic window and tries to find connected permutations
in each target row with the transposition-walk local search.
"""

from __future__ import annotations

import argparse
import csv
import sys

from bidefect_target_local_search import search_target
from k6_remaining_arithmetic import balanced_rows


def row_seed(seed: int, t: int, row_index: int) -> int:
    return seed + 1009 * t + 9176 * row_index


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--t-min", type=int, default=13)
    parser.add_argument("--t-max", type=int, default=20)
    parser.add_argument("--seed", type=int, default=424242)
    parser.add_argument("--restarts", type=int, default=12)
    parser.add_argument("--steps", type=int, default=60000)
    parser.add_argument("--temperature", type=float, default=0.05)
    parser.add_argument("--connected-weight", type=int, default=8)
    parser.add_argument(
        "--first-balanced-only",
        action="store_true",
        help="search only the first balanced g for each t",
    )
    parser.add_argument(
        "--fail-on-miss",
        action="store_true",
        help="return nonzero if any searched target is missed",
    )
    args = parser.parse_args()

    if args.t_min < 2:
        raise SystemExit("t-min must be at least 2")
    if args.t_max < args.t_min:
        raise SystemExit("t-max must be at least t-min")
    if args.restarts <= 0 or args.steps <= 0:
        raise SystemExit("restarts and steps must be positive")

    writer = csv.writer(sys.stdout)
    writer.writerow(
        [
            "t",
            "g",
            "seed",
            "status",
            "c_pi",
            "c_gamma_pi",
            "c_pi_gamma_inv",
            "plus",
            "minus",
            "g_plus",
            "g_minus",
            "components",
            "penalty",
            "restart",
            "step",
        ]
    )

    searched = 0
    misses = 0
    for t in range(args.t_min, args.t_max + 1):
        candidates = balanced_rows(t)
        if args.first_balanced_only and candidates:
            candidates = candidates[:1]
        for row_index, g in enumerate(candidates):
            seed = row_seed(args.seed, t, row_index)
            result = search_target(
                k=6,
                t=t,
                target_g=g,
                restarts=args.restarts,
                steps=args.steps,
                seed=seed,
                connected_weight=args.connected_weight,
                temperature=args.temperature,
            )
            data = result["data"]
            status = "found" if result["found"] else "miss"
            if not result["found"]:
                misses += 1
            searched += 1
            writer.writerow(
                [
                    t,
                    g,
                    seed,
                    status,
                    *data,
                    result["score"],
                    result["restart"],
                    result["step"],
                ]
            )

    if searched == 0:
        print("# no balanced targets in requested t-range", file=sys.stderr)
    print(
        f"# searched={searched},found={searched - misses},missed={misses}",
        file=sys.stderr,
    )
    if args.fail_on_miss and misses:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
