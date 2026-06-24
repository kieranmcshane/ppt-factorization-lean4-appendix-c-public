#!/usr/bin/env python3
"""Fixed-bridge add-a-block growth for strict split witnesses.

This is a structured variant of `k6_strict_split_block_growth.py`.  It keeps
the old permutation, adds one new 6-point block, swaps the image of one fixed
old domain with the image of one fixed new-domain offset, and varies only the
new block's internal permutation.

Found rows are verified witnesses.  Misses are finite evidence only.
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
    "status",
    "checked",
    "bridge_swap",
    "new_block_perm",
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


def load_sources(path: Path, found_only: bool) -> list[dict[str, str]]:
    with path.open(newline="") as handle:
        rows = list(csv.DictReader(handle))
    if found_only and "status" in rows[0]:
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


def try_fixed_bridge(
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
    if not (0 <= old_domain < old_n):
        raise ValueError("old-domain is outside the old permutation")
    if not (0 <= new_domain_offset < 6):
        raise ValueError("new-domain-offset must be in 0..5")

    new_block = tuple(range(old_n, new_n))
    new_domain = new_block[new_domain_offset]
    gamma = gamma_perm(6, target_t)
    gamma_inv = inverse_perm(gamma)
    checked = 0
    best_score: int | None = None
    best_data = None
    best_perm: tuple[int, ...] | None = None

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
            best_perm = block_perm
        if score == 0:
            return {
                "status": "found",
                "checked": checked,
                "bridge_swap": f"{old_domain}:{new_domain}",
                "new_block_perm": format_perm(block_perm),
                "data": data,
                "pi": pi,
            }

    assert best_score is not None and best_data is not None
    return {
        "status": f"miss_best_score_{best_score}",
        "checked": checked,
        "bridge_swap": f"{old_domain}:{new_domain}",
        "new_block_perm": format_perm(best_perm),
        "data": best_data,
        "pi": [],
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("source_witness_csv", type=Path)
    parser.add_argument("--target-t", type=int)
    parser.add_argument("--found-only", action="store_true")
    parser.add_argument("--old-domain", type=int, default=0)
    parser.add_argument("--new-domain-offset", type=int, default=0)
    parser.add_argument("--connected-weight", type=int, default=8)
    parser.add_argument("--emit-permutation", action="store_true")
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
            result = try_fixed_bridge(
                source,
                target_t=target_t,
                target_g=target_g,
                target_p=target_p,
                target_q=target_q,
                old_domain=args.old_domain,
                new_domain_offset=args.new_domain_offset,
                connected_weight=args.connected_weight,
            )
            data = result["data"]
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
                    "status": result["status"],
                    "checked": result["checked"],
                    "bridge_swap": result["bridge_swap"],
                    "new_block_perm": result["new_block_perm"],
                    "c_pi": data[0],
                    "c_gamma_pi": data[1],
                    "c_pi_gamma_inv": data[2],
                    "plus": data[3],
                    "minus": data[4],
                    "g_plus": data[5],
                    "g_minus": data[6],
                    "components": data[7],
                    "permutation_image": (
                        " ".join(str(x) for x in result["pi"])
                        if args.emit_permutation and result["status"] == "found"
                        else ""
                    ),
                }
            )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
