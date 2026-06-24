#!/usr/bin/env python3
"""Count bridge locations for strict split add-a-block growth.

This probe fixes a source witness and a target strict split slot at `t+1`.
For each requested new-domain offset and each old domain, it enumerates all
`6!` internal permutations of the new block and counts exact witnesses.

This measures the polynomial bridge-location factor for a fixed growth step.
It is finite constructive evidence, not an asymptotic entropy theorem.
"""

from __future__ import annotations

import argparse
import csv
import itertools
import sys
from pathlib import Path

from bidefect_target_local_search import gamma_perm, inverse_perm
from k6_balanced_split_target_search import score_split
from k6_strict_split_block_growth import row_value
from k6_strict_split_near_hit_local_profile import parse_image


FIELDNAMES = [
    "source_row",
    "source_t",
    "source_g",
    "source_p",
    "source_q",
    "target_t",
    "target_g",
    "target_p",
    "target_q",
    "old_domain",
    "new_domain_offset",
    "new_domain",
    "checked",
    "hit_count",
    "first_hit_perm",
    "best_score",
    "best_c_pi",
    "best_c_gamma_pi",
    "best_c_pi_gamma_inv",
    "best_plus",
    "best_minus",
    "best_g_plus",
    "best_g_minus",
    "best_components",
]


def format_perm(perm: tuple[int, ...] | None) -> str:
    if perm is None:
        return ""
    return " ".join(str(x) for x in perm)


def parse_offsets(text: str) -> list[int]:
    out = [int(part) for part in text.split(",") if part != ""]
    if not out:
        raise ValueError("at least one offset is required")
    if any(offset < 0 or offset >= 6 for offset in out):
        raise ValueError("new-domain offsets must lie in 0..5")
    return out


def count_for_bridge(
    *,
    source_row: int,
    source: dict[str, str],
    target_t: int,
    target_g: int,
    target_p: int,
    target_q: int,
    old_domain: int,
    new_domain_offset: int,
    connected_weight: int,
) -> dict[str, object]:
    source_t = int(row_value(source, "t", "target_t"))
    old_pi = parse_image(source["permutation_image"])
    old_n = 6 * source_t
    new_n = 6 * target_t
    new_block = tuple(range(old_n, new_n))
    new_domain = new_block[new_domain_offset]
    gamma = gamma_perm(6, target_t)
    gamma_inv = inverse_perm(gamma)

    hit_count = 0
    checked = 0
    first_hit: tuple[int, ...] | None = None
    best_score: int | None = None
    best_data = None

    for block_perm in itertools.permutations(new_block):
        pi = list(range(new_n))
        pi[:old_n] = old_pi
        for domain, image in zip(new_block, block_perm):
            pi[domain] = image
        pi[old_domain], pi[new_domain] = pi[new_domain], pi[old_domain]
        score, data = score_split(
            target_t,
            target_p,
            target_q,
            pi,
            gamma,
            gamma_inv,
            connected_weight,
        )
        checked += 1
        if best_score is None or score < best_score:
            best_score = score
            best_data = data
        if score == 0:
            hit_count += 1
            if first_hit is None:
                first_hit = block_perm

    assert best_score is not None and best_data is not None
    return {
        "source_row": source_row,
        "source_t": source_t,
        "source_g": row_value(source, "g", "target_g"),
        "source_p": row_value(source, "p", "target_p"),
        "source_q": row_value(source, "q", "target_q"),
        "target_t": target_t,
        "target_g": target_g,
        "target_p": target_p,
        "target_q": target_q,
        "old_domain": old_domain,
        "new_domain_offset": new_domain_offset,
        "new_domain": new_domain,
        "checked": checked,
        "hit_count": hit_count,
        "first_hit_perm": format_perm(first_hit),
        "best_score": best_score,
        "best_c_pi": best_data[0],
        "best_c_gamma_pi": best_data[1],
        "best_c_pi_gamma_inv": best_data[2],
        "best_plus": best_data[3],
        "best_minus": best_data[4],
        "best_g_plus": best_data[5],
        "best_g_minus": best_data[6],
        "best_components": best_data[7],
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("source_csv", type=Path)
    parser.add_argument("--source-row", type=int, required=True)
    parser.add_argument("--target-g", type=int, required=True)
    parser.add_argument("--target-p", type=int, required=True)
    parser.add_argument("--target-q", type=int, required=True)
    parser.add_argument("--target-t", type=int)
    parser.add_argument("--new-domain-offsets", default="0")
    parser.add_argument("--connected-weight", type=int, default=8)
    args = parser.parse_args()

    rows = list(csv.DictReader(args.source_csv.open(newline="")))
    if not (0 <= args.source_row < len(rows)):
        raise SystemExit("source-row out of range")
    source = rows[args.source_row]
    source_t = int(row_value(source, "t", "target_t"))
    target_t = args.target_t if args.target_t is not None else source_t + 1
    if target_t != source_t + 1:
        raise SystemExit("target-t must be source_t + 1")
    if not source.get("permutation_image", "").strip():
        raise SystemExit("source row must include permutation_image")

    old_n = 6 * source_t
    offsets = parse_offsets(args.new_domain_offsets)

    writer = csv.DictWriter(sys.stdout, fieldnames=FIELDNAMES, lineterminator="\n")
    writer.writeheader()
    for offset in offsets:
        for old_domain in range(old_n):
            writer.writerow(
                count_for_bridge(
                    source_row=args.source_row,
                    source=source,
                    target_t=target_t,
                    target_g=args.target_g,
                    target_p=args.target_p,
                    target_q=args.target_q,
                    old_domain=old_domain,
                    new_domain_offset=offset,
                    connected_weight=args.connected_weight,
                )
            )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
