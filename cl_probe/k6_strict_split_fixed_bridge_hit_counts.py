#!/usr/bin/env python3
"""Count fixed-bridge internal-block choices hitting strict split targets.

For each source witness and each strict target at `t+1`, keep the fixed bridge
from old domain `0` to the first new domain and enumerate all 6! internal
permutations of the new block.  The output counts how many choices give an
exact strict split witness.

This is a finite branching diagnostic, not an asymptotic entropy theorem.
"""

from __future__ import annotations

import argparse
import csv
import itertools
import sys
from pathlib import Path

from bidefect_target_local_search import gamma_perm, inverse_perm
from k6_balanced_split_target_search import score_split
from k6_balanced_split_window import split_slots
from k6_remaining_arithmetic import balanced_rows
from k6_strict_split_block_growth import row_value
from k6_strict_split_near_hit_local_profile import parse_image


FIELDNAMES = [
    "source_index",
    "source_t",
    "source_g",
    "source_p",
    "source_q",
    "target_t",
    "target_g",
    "target_p",
    "target_q",
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


def load_sources(path: Path, found_only: bool) -> list[dict[str, str]]:
    with path.open(newline="") as handle:
        rows = list(csv.DictReader(handle))
    if found_only and rows and "status" in rows[0]:
        rows = [row for row in rows if row["status"] == "found"]
    return rows


def strict_targets(t: int) -> list[tuple[int, int, int]]:
    out: list[tuple[int, int, int]] = []
    for g in balanced_rows(t):
        strict, _boundary = split_slots(t, g)
        out.extend((g, p, q) for p, q in strict)
    return out


def format_perm(perm: tuple[int, ...] | None) -> str:
    if perm is None:
        return ""
    return " ".join(str(x) for x in perm)


def count_hits(
    source: dict[str, str],
    *,
    target_t: int,
    target_g: int,
    target_p: int,
    target_q: int,
    old_domain: int,
    new_domain_offset: int,
    connected_weight: int,
) -> dict[str, object]:
    source_t = int(row_value(source, "t", "target_t"))
    if target_t != source_t + 1:
        raise ValueError("target_t must be source_t + 1")
    old_pi = parse_image(source["permutation_image"])
    old_n = 6 * source_t
    new_n = 6 * target_t
    if len(old_pi) != old_n:
        raise ValueError("source permutation length does not match source_t")

    new_block = tuple(range(old_n, new_n))
    new_domain = new_block[new_domain_offset]
    gamma = gamma_perm(6, target_t)
    gamma_inv = inverse_perm(gamma)
    checked = 0
    hit_count = 0
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
        "checked": checked,
        "hit_count": hit_count,
        "first_hit_perm": format_perm(first_hit),
        "best_score": best_score,
        "best_data": best_data,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("source_witness_csv", type=Path)
    parser.add_argument("--target-t", type=int)
    parser.add_argument("--found-only", action="store_true")
    parser.add_argument("--old-domain", type=int, default=0)
    parser.add_argument("--new-domain-offset", type=int, default=0)
    parser.add_argument("--connected-weight", type=int, default=8)
    args = parser.parse_args()

    sources = load_sources(args.source_witness_csv, args.found_only)
    if not sources:
        raise SystemExit("no source rows available")
    source_ts = {int(row_value(row, "t", "target_t")) for row in sources}
    if len(source_ts) != 1:
        raise SystemExit("all source rows must have the same source t")
    source_t = next(iter(source_ts))
    target_t = args.target_t if args.target_t is not None else source_t + 1
    if target_t != source_t + 1:
        raise SystemExit("target-t must be source_t + 1")

    writer = csv.DictWriter(sys.stdout, fieldnames=FIELDNAMES, lineterminator="\n")
    writer.writeheader()
    for source_index, source in enumerate(sources):
        for target_g, target_p, target_q in strict_targets(target_t):
            result = count_hits(
                source,
                target_t=target_t,
                target_g=target_g,
                target_p=target_p,
                target_q=target_q,
                old_domain=args.old_domain,
                new_domain_offset=args.new_domain_offset,
                connected_weight=args.connected_weight,
            )
            best_data = result["best_data"]
            writer.writerow(
                {
                    "source_index": source_index,
                    "source_t": source_t,
                    "source_g": row_value(source, "g", "target_g"),
                    "source_p": row_value(source, "p", "target_p"),
                    "source_q": row_value(source, "q", "target_q"),
                    "target_t": target_t,
                    "target_g": target_g,
                    "target_p": target_p,
                    "target_q": target_q,
                    "checked": result["checked"],
                    "hit_count": result["hit_count"],
                    "first_hit_perm": result["first_hit_perm"],
                    "best_score": result["best_score"],
                    "best_c_pi": best_data[0],
                    "best_c_gamma_pi": best_data[1],
                    "best_c_pi_gamma_inv": best_data[2],
                    "best_plus": best_data[3],
                    "best_minus": best_data[4],
                    "best_g_plus": best_data[5],
                    "best_g_minus": best_data[6],
                    "best_components": best_data[7],
                }
            )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
