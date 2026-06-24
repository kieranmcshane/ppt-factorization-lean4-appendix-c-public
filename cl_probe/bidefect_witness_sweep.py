#!/usr/bin/env python3
"""Sweep remaining bidefect lattice rows for finite witnesses.

This is finite Monte Carlo evidence, not an asymptotic count.  It takes the
candidate rows left by `bidefect_remaining_lattice.py` and tries to find a
connected permutation witness for each row within a fixed sample budget.
"""

from __future__ import annotations

import argparse

import numpy as np

from bidefect_remaining_lattice import candidate_rows, row_margin
from bidefect_witness_search import (
    bidefect_data,
    connected_for_gamma,
    gamma_perm,
    inverse_perm,
)


def find_witness(
    k: int,
    t: int,
    target_gp: int,
    target_gm: int,
    seed: int,
    max_samples: int,
    chunk: int,
) -> tuple[bool, int, int, list[int] | None]:
    n = k * t
    gamma = gamma_perm(k, t)
    gamma_inv = inverse_perm(gamma)
    rng = np.random.default_rng(seed)
    attempts = 0
    connected_hits = 0

    while attempts < max_samples:
        batch = min(chunk, max_samples - attempts)
        perms = np.argsort(rng.random((batch, n)), axis=1).astype(np.int64)
        for row in perms:
            attempts += 1
            pi = row.tolist()
            if not connected_for_gamma(pi, gamma):
                continue
            connected_hits += 1
            *_counts, gp, gm = bidefect_data(k, t, pi, gamma, gamma_inv)
            if gp == target_gp and gm == target_gm:
                return True, attempts, connected_hits, pi
        if batch <= 0:
            break
    return False, attempts, connected_hits, None


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--k", type=int, default=6)
    parser.add_argument("--t-max", type=int, default=12)
    parser.add_argument("--eta-min", type=float, default=3.0)
    parser.add_argument("--max-samples", type=int, default=50000)
    parser.add_argument("--chunk", type=int, default=5000)
    parser.add_argument("--seed", type=int, default=20260617)
    parser.add_argument("--max-targets", type=int, default=None)
    parser.add_argument("--show-images", action="store_true")
    parser.add_argument("--require-all", action="store_true")
    args = parser.parse_args()

    if args.k < 2:
        raise SystemExit("k must be at least 2")
    if args.t_max < 2:
        raise SystemExit("t-max must be at least 2")
    if args.max_samples <= 0 or args.chunk <= 0:
        raise SystemExit("max-samples and chunk must be positive")
    if args.eta_min <= 0:
        raise SystemExit("eta-min must be positive")

    candidates = list(
        candidate_rows(args.k, args.t_max, args.eta_min, only_open=True)
    )
    if args.max_targets is not None:
        candidates = candidates[: args.max_targets]

    print("# Remaining bidefect witness sweep")
    print("# finite Monte Carlo evidence only; not an asymptotic estimate")
    print(
        f"# k={args.k},t_max={args.t_max},eta_min={args.eta_min:.12g},"
        f"targets={len(candidates)},max_samples_per_target={args.max_samples},"
        f"seed_base={args.seed}"
    )
    print(
        "k,t,g_plus,g_minus,s,alpha_leading,margin,seed,attempts,"
        "connected_hits,found"
    )

    found_count = 0
    first_missing = None
    for index, (t, gp, gm, _status) in enumerate(candidates):
        seed = args.seed + index
        found, attempts, connected_hits, pi = find_witness(
            args.k, t, gp, gm, seed, args.max_samples, args.chunk
        )
        if found:
            found_count += 1
        elif first_missing is None:
            first_missing = (t, gp, gm)
        s = (gp + gm) / t
        alpha = 4 + 2 * s
        margin = row_margin(args.k, t, gp, gm, args.eta_min)
        print(
            f"{args.k},{t},{gp},{gm},{s:.12g},{alpha:.12g},"
            f"{margin:.12g},{seed},{attempts},{connected_hits},"
            f"{'yes' if found else 'no'}"
        )
        if found and args.show_images and pi is not None:
            print("permutation_image")
            print(",".join(str(x) for x in pi))

    print()
    print("# Summary")
    print("k,t_max,targets,found,not_found,first_missing")
    missing = len(candidates) - found_count
    if first_missing is None:
        first_missing_text = ""
    else:
        first_missing_text = f"{first_missing[0]}:{first_missing[1]}:{first_missing[2]}"
    print(
        f"{args.k},{args.t_max},{len(candidates)},{found_count},"
        f"{missing},{first_missing_text}"
    )
    return 1 if args.require_all and missing else 0


if __name__ == "__main__":
    raise SystemExit(main())
