#!/usr/bin/env python3
"""One-swap local profile around strict split near-hits.

Input is a CSV produced by `k6_balanced_split_target_search.py` with
`--emit-permutation`.  For every row with a saved best permutation, this
script enumerates all image-swaps and recomputes the same strict split score.

This is not an emptiness proof.  It only makes the current search frontier
inspectable: if a best miss has no one-swap neighbor with score zero, then that
particular near-hit is a genuine local obstruction for the chosen move.
"""

from __future__ import annotations

import argparse
import csv
import sys
from pathlib import Path

from bidefect_target_local_search import gamma_perm, inverse_perm
from k6_balanced_split_target_search import score_split


FIELDNAMES = [
    "t",
    "g",
    "p",
    "q",
    "base_score",
    "base_c_pi",
    "base_c_gamma_pi",
    "base_c_pi_gamma_inv",
    "base_plus",
    "base_minus",
    "base_g_plus",
    "base_g_minus",
    "base_components",
    "neighbor_count",
    "min_neighbor_score",
    "zero_neighbors",
    "improving_neighbors",
    "same_score_neighbors",
    "score_one_neighbors",
    "score_two_neighbors",
    "first_zero_swap",
    "best_neighbor_swap",
    "best_neighbor_c_pi",
    "best_neighbor_c_gamma_pi",
    "best_neighbor_c_pi_gamma_inv",
    "best_neighbor_plus",
    "best_neighbor_minus",
    "best_neighbor_g_plus",
    "best_neighbor_g_minus",
    "best_neighbor_components",
]


def parse_image(text: str) -> list[int]:
    if not text.strip():
        raise ValueError("missing permutation_image; rerun target search with --emit-permutation")
    return [int(part) for part in text.split()]


def format_swap(swap: tuple[int, int] | None) -> str:
    if swap is None:
        return ""
    return f"{swap[0]}:{swap[1]}"


def profile_row(row: dict[str, str], connected_weight: int) -> dict[str, object]:
    t = int(row["t"])
    g = int(row["g"])
    p = int(row["p"])
    q = int(row["q"])
    pi = parse_image(row["permutation_image"])
    gamma = gamma_perm(6, t)
    gamma_inv = inverse_perm(gamma)
    base_score, base_data = score_split(t, p, q, pi, gamma, gamma_inv, connected_weight)

    best_score: int | None = None
    best_data = None
    best_swap: tuple[int, int] | None = None
    first_zero: tuple[int, int] | None = None
    zero = improving = same = score_one = score_two = 0
    neighbor_count = 0

    for i in range(len(pi)):
        for j in range(i + 1, len(pi)):
            neighbor_count += 1
            pi[i], pi[j] = pi[j], pi[i]
            score, data = score_split(t, p, q, pi, gamma, gamma_inv, connected_weight)
            pi[i], pi[j] = pi[j], pi[i]

            if best_score is None or score < best_score:
                best_score = score
                best_data = data
                best_swap = (i, j)
            if score == 0:
                zero += 1
                if first_zero is None:
                    first_zero = (i, j)
            if score < base_score:
                improving += 1
            elif score == base_score:
                same += 1
            if score == 1:
                score_one += 1
            if score == 2:
                score_two += 1

    assert best_score is not None and best_data is not None
    return {
        "t": t,
        "g": g,
        "p": p,
        "q": q,
        "base_score": base_score,
        "base_c_pi": base_data[0],
        "base_c_gamma_pi": base_data[1],
        "base_c_pi_gamma_inv": base_data[2],
        "base_plus": base_data[3],
        "base_minus": base_data[4],
        "base_g_plus": base_data[5],
        "base_g_minus": base_data[6],
        "base_components": base_data[7],
        "neighbor_count": neighbor_count,
        "min_neighbor_score": best_score,
        "zero_neighbors": zero,
        "improving_neighbors": improving,
        "same_score_neighbors": same,
        "score_one_neighbors": score_one,
        "score_two_neighbors": score_two,
        "first_zero_swap": format_swap(first_zero),
        "best_neighbor_swap": format_swap(best_swap),
        "best_neighbor_c_pi": best_data[0],
        "best_neighbor_c_gamma_pi": best_data[1],
        "best_neighbor_c_pi_gamma_inv": best_data[2],
        "best_neighbor_plus": best_data[3],
        "best_neighbor_minus": best_data[4],
        "best_neighbor_g_plus": best_data[5],
        "best_neighbor_g_minus": best_data[6],
        "best_neighbor_components": best_data[7],
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("target_search_csv", type=Path)
    parser.add_argument("--connected-weight", type=int, default=8)
    args = parser.parse_args()

    writer = csv.DictWriter(sys.stdout, fieldnames=FIELDNAMES, lineterminator="\n")
    writer.writeheader()
    with args.target_search_csv.open(newline="") as handle:
        reader = csv.DictReader(handle)
        for row in reader:
            if row.get("permutation_image", "").strip():
                writer.writerow(profile_row(row, args.connected_weight))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
