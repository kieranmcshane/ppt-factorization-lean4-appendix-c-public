#!/usr/bin/env python3
"""Extract strict split witnesses found in a near-hit local profile.

Inputs:
* a target-search CSV produced with `--emit-permutation`;
* a local-profile CSV produced by `k6_strict_split_near_hit_local_profile.py`.

For every row whose profile reports a `first_zero_swap`, this script applies
that swap to the saved best permutation, verifies that the strict split score
is zero, and emits a certificate row.
"""

from __future__ import annotations

import argparse
import csv
import sys
from pathlib import Path

from bidefect_target_local_search import gamma_perm, inverse_perm
from k6_balanced_split_target_search import score_split
from k6_strict_split_near_hit_local_profile import parse_image


FIELDNAMES = [
    "t",
    "g",
    "p",
    "q",
    "source_base_score",
    "zero_swap",
    "c_pi",
    "c_gamma_pi",
    "c_pi_gamma_inv",
    "plus",
    "minus",
    "g_plus",
    "g_minus",
    "components",
    "permutation_image",
]


def key(row: dict[str, str]) -> tuple[str, str, str, str]:
    return row["t"], row["g"], row["p"], row["q"]


def parse_swap(text: str) -> tuple[int, int] | None:
    if not text.strip():
        return None
    left, right = text.split(":")
    return int(left), int(right)


def load_target_rows(path: Path) -> dict[tuple[str, str, str, str], dict[str, str]]:
    with path.open(newline="") as handle:
        return {key(row): row for row in csv.DictReader(handle)}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("target_search_csv", type=Path)
    parser.add_argument("local_profile_csv", type=Path)
    parser.add_argument("--connected-weight", type=int, default=8)
    args = parser.parse_args()

    targets = load_target_rows(args.target_search_csv)
    writer = csv.DictWriter(sys.stdout, fieldnames=FIELDNAMES, lineterminator="\n")
    writer.writeheader()

    with args.local_profile_csv.open(newline="") as handle:
        for row in csv.DictReader(handle):
            swap = parse_swap(row["first_zero_swap"])
            if swap is None:
                continue
            target = targets[key(row)]
            t = int(row["t"])
            g = int(row["g"])
            p = int(row["p"])
            q = int(row["q"])
            pi = parse_image(target["permutation_image"])
            i, j = swap
            pi[i], pi[j] = pi[j], pi[i]

            gamma = gamma_perm(6, t)
            gamma_inv = inverse_perm(gamma)
            score, data = score_split(t, p, q, pi, gamma, gamma_inv, args.connected_weight)
            if score != 0:
                raise SystemExit(f"zero swap failed to verify for {(t, g, p, q)}")
            writer.writerow(
                {
                    "t": t,
                    "g": g,
                    "p": p,
                    "q": q,
                    "source_base_score": row["base_score"],
                    "zero_swap": row["first_zero_swap"],
                    "c_pi": data[0],
                    "c_gamma_pi": data[1],
                    "c_pi_gamma_inv": data[2],
                    "plus": data[3],
                    "minus": data[4],
                    "g_plus": data[5],
                    "g_minus": data[6],
                    "components": data[7],
                    "permutation_image": " ".join(str(x) for x in pi),
                }
            )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
