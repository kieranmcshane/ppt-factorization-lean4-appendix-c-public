#!/usr/bin/env python3
"""Deterministic one-swap descent from strict split near-hits.

Input is a target-search CSV produced by
`k6_balanced_split_target_search.py --emit-permutation`.  Starting from each
saved best permutation, this script repeatedly enumerates all image-swaps and
applies the first lexicographically best strict-score improvement.  It stops
at score zero, a one-swap local minimum, or `--max-rounds`.

This is a finite diagnostic.  A failure to reach score zero is not an
emptiness proof for the target slot.
"""

from __future__ import annotations

import argparse
import csv
import sys
from pathlib import Path

from bidefect_target_local_search import gamma_perm, inverse_perm
from k6_balanced_split_target_search import score_split
from k6_strict_split_near_hit_local_profile import format_swap, parse_image


FIELDNAMES = [
    "t",
    "g",
    "p",
    "q",
    "start_score",
    "final_score",
    "steps_taken",
    "stop_reason",
    "score_path",
    "swap_path",
    "final_c_pi",
    "final_c_gamma_pi",
    "final_c_pi_gamma_inv",
    "final_plus",
    "final_minus",
    "final_g_plus",
    "final_g_minus",
    "final_components",
    "permutation_image",
]


def best_improving_swap(
    *,
    t: int,
    p: int,
    q: int,
    pi: list[int],
    gamma: tuple[int, ...],
    gamma_inv: tuple[int, ...],
    connected_weight: int,
    current_score: int,
) -> tuple[int, tuple[int, int, int, int, int, int | None, int | None, int], tuple[int, int] | None]:
    best_score = current_score
    best_data: tuple[int, int, int, int, int, int | None, int | None, int] | None = None
    best_swap: tuple[int, int] | None = None
    for i in range(len(pi)):
        for j in range(i + 1, len(pi)):
            pi[i], pi[j] = pi[j], pi[i]
            score, data = score_split(t, p, q, pi, gamma, gamma_inv, connected_weight)
            pi[i], pi[j] = pi[j], pi[i]
            key = (score, data, i, j)
            if score < best_score and (
                best_data is None or key < (best_score, best_data, best_swap[0], best_swap[1])
            ):
                best_score = score
                best_data = data
                best_swap = (i, j)
    if best_data is None:
        _, current_data = score_split(t, p, q, pi, gamma, gamma_inv, connected_weight)
        return current_score, current_data, None
    return best_score, best_data, best_swap


def descend_row(
    row: dict[str, str],
    *,
    connected_weight: int,
    max_rounds: int,
    emit_permutation: bool,
) -> dict[str, object]:
    t = int(row["t"])
    g = int(row["g"])
    p = int(row["p"])
    q = int(row["q"])
    pi = parse_image(row["permutation_image"])
    gamma = gamma_perm(6, t)
    gamma_inv = inverse_perm(gamma)
    current_score, current_data = score_split(t, p, q, pi, gamma, gamma_inv, connected_weight)
    start_score = current_score
    score_path = [str(current_score)]
    swap_path: list[str] = []
    stop_reason = "max_rounds"

    for _round in range(max_rounds):
        if current_score == 0:
            stop_reason = "zero"
            break
        next_score, next_data, swap = best_improving_swap(
            t=t,
            p=p,
            q=q,
            pi=pi,
            gamma=gamma,
            gamma_inv=gamma_inv,
            connected_weight=connected_weight,
            current_score=current_score,
        )
        if swap is None:
            stop_reason = "local_min"
            current_data = next_data
            break
        i, j = swap
        pi[i], pi[j] = pi[j], pi[i]
        current_score = next_score
        current_data = next_data
        score_path.append(str(current_score))
        swap_path.append(format_swap(swap))
    else:
        if current_score == 0:
            stop_reason = "zero"

    return {
        "t": t,
        "g": g,
        "p": p,
        "q": q,
        "start_score": start_score,
        "final_score": current_score,
        "steps_taken": len(swap_path),
        "stop_reason": stop_reason,
        "score_path": ";".join(score_path),
        "swap_path": ";".join(swap_path),
        "final_c_pi": current_data[0],
        "final_c_gamma_pi": current_data[1],
        "final_c_pi_gamma_inv": current_data[2],
        "final_plus": current_data[3],
        "final_minus": current_data[4],
        "final_g_plus": current_data[5],
        "final_g_minus": current_data[6],
        "final_components": current_data[7],
        "permutation_image": " ".join(str(x) for x in pi) if emit_permutation else "",
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("target_search_csv", type=Path)
    parser.add_argument("--connected-weight", type=int, default=8)
    parser.add_argument("--max-rounds", type=int, default=4)
    parser.add_argument("--emit-permutation", action="store_true")
    args = parser.parse_args()

    if args.max_rounds < 0:
        raise SystemExit("max-rounds must be nonnegative")

    writer = csv.DictWriter(sys.stdout, fieldnames=FIELDNAMES, lineterminator="\n")
    writer.writeheader()
    with args.target_search_csv.open(newline="") as handle:
        for row in csv.DictReader(handle):
            if row.get("permutation_image", "").strip():
                writer.writerow(
                    descend_row(
                        row,
                        connected_weight=args.connected_weight,
                        max_rounds=args.max_rounds,
                        emit_permutation=args.emit_permutation,
                    )
                )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
