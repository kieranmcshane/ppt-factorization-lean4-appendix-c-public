#!/usr/bin/env python3
"""Count distinct witnesses produced by bridge-location choices.

The bridge-location hit counts count successful construction choices.  This
script checks whether those choices collapse to duplicate permutations for one
source-target step.  It stores only aggregate counts, not the witness images.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import itertools
import struct
import sys
from collections import Counter
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
    "new_domain_offsets",
    "old_domains_checked",
    "choices_checked",
    "hit_count",
    "distinct_witnesses",
    "duplicate_hits",
    "min_hits_per_old_domain",
    "max_hits_per_old_domain",
    "hits_by_offset",
]


def parse_offsets(text: str) -> list[int]:
    offsets = [int(part) for part in text.split(",") if part != ""]
    if not offsets:
        raise ValueError("at least one offset is required")
    if any(offset < 0 or offset >= 6 for offset in offsets):
        raise ValueError("new-domain offsets must lie in 0..5")
    return offsets


def perm_digest(pi: list[int]) -> bytes:
    # Two bytes per value keeps this valid for future larger n as well.
    payload = b"".join(struct.pack("<H", value) for value in pi)
    return hashlib.blake2b(payload, digest_size=16).digest()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("source_csv", type=Path)
    parser.add_argument("--source-row", type=int, required=True)
    parser.add_argument("--target-g", type=int, required=True)
    parser.add_argument("--target-p", type=int, required=True)
    parser.add_argument("--target-q", type=int, required=True)
    parser.add_argument("--target-t", type=int)
    parser.add_argument("--new-domain-offsets", default="0,1,2,3,4,5")
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

    offsets = parse_offsets(args.new_domain_offsets)
    old_pi = parse_image(source["permutation_image"])
    old_n = 6 * source_t
    new_n = 6 * target_t
    new_block = tuple(range(old_n, new_n))
    gamma = gamma_perm(6, target_t)
    gamma_inv = inverse_perm(gamma)

    hit_count = 0
    choices_checked = 0
    seen: set[bytes] = set()
    hits_by_offset: Counter[int] = Counter()
    hits_by_old_domain: Counter[int] = Counter()

    for offset in offsets:
        new_domain = new_block[offset]
        for old_domain in range(old_n):
            for block_perm in itertools.permutations(new_block):
                pi = list(range(new_n))
                pi[:old_n] = old_pi
                for domain, image in zip(new_block, block_perm):
                    pi[domain] = image
                pi[old_domain], pi[new_domain] = pi[new_domain], pi[old_domain]
                score, _data = score_split(
                    target_t,
                    args.target_p,
                    args.target_q,
                    pi,
                    gamma,
                    gamma_inv,
                    args.connected_weight,
                )
                choices_checked += 1
                if score == 0:
                    hit_count += 1
                    hits_by_offset[offset] += 1
                    hits_by_old_domain[old_domain] += 1
                    seen.add(perm_digest(pi))

    positive_old_counts = list(hits_by_old_domain.values())
    row = {
        "source_row": args.source_row,
        "source_t": source_t,
        "source_g": row_value(source, "g", "target_g"),
        "source_p": row_value(source, "p", "target_p"),
        "source_q": row_value(source, "q", "target_q"),
        "target_t": target_t,
        "target_g": args.target_g,
        "target_p": args.target_p,
        "target_q": args.target_q,
        "new_domain_offsets": ",".join(str(offset) for offset in offsets),
        "old_domains_checked": old_n,
        "choices_checked": choices_checked,
        "hit_count": hit_count,
        "distinct_witnesses": len(seen),
        "duplicate_hits": hit_count - len(seen),
        "min_hits_per_old_domain": min(positive_old_counts) if positive_old_counts else 0,
        "max_hits_per_old_domain": max(positive_old_counts) if positive_old_counts else 0,
        "hits_by_offset": ";".join(
            f"{offset}:{hits_by_offset[offset]}" for offset in offsets
        ),
    }
    writer = csv.DictWriter(sys.stdout, fieldnames=FIELDNAMES, lineterminator="\n")
    writer.writeheader()
    writer.writerow(row)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
