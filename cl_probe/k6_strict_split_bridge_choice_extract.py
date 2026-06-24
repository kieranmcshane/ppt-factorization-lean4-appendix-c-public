#!/usr/bin/env python3
"""Extract selected bridge-location choices as witness certificates.

Input:
* a source witness CSV containing `permutation_image`;
* a bridge-location count CSV produced by
  `k6_strict_split_bridge_location_counts.py`.

For selected old domains and new-domain offsets, apply the recorded
`first_hit_perm`, verify the strict split score is zero, and emit witness rows
usable by the next growth/counting scripts.
"""

from __future__ import annotations

import argparse
import csv
import sys
from pathlib import Path

from bidefect_target_local_search import gamma_perm, inverse_perm
from k6_balanced_split_target_search import score_split
from k6_strict_split_block_growth import row_value
from k6_strict_split_near_hit_local_profile import parse_image


FIELDNAMES = [
    "t",
    "g",
    "p",
    "q",
    "source_row",
    "old_domain",
    "new_domain_offset",
    "new_domain",
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


def parse_int_set(text: str) -> set[int] | None:
    if text == "all":
        return None
    return {int(part) for part in text.split(",") if part != ""}


def load_source_rows(path: Path) -> list[dict[str, str]]:
    with path.open(newline="") as handle:
        return list(csv.DictReader(handle))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("source_csv", type=Path)
    parser.add_argument("bridge_count_csv", type=Path)
    parser.add_argument("--old-domains", default="0,1,120,245")
    parser.add_argument("--new-domain-offsets", default="0")
    parser.add_argument("--connected-weight", type=int, default=8)
    args = parser.parse_args()

    old_domains = parse_int_set(args.old_domains)
    offsets = parse_int_set(args.new_domain_offsets)
    source_rows = load_source_rows(args.source_csv)

    writer = csv.DictWriter(sys.stdout, fieldnames=FIELDNAMES, lineterminator="\n")
    writer.writeheader()
    with args.bridge_count_csv.open(newline="") as handle:
        for bridge in csv.DictReader(handle):
            if int(bridge["hit_count"]) <= 0:
                continue
            old_domain = int(bridge["old_domain"])
            offset = int(bridge["new_domain_offset"])
            if old_domains is not None and old_domain not in old_domains:
                continue
            if offsets is not None and offset not in offsets:
                continue
            source_row = int(bridge["source_row"])
            source = source_rows[source_row]
            source_t = int(row_value(source, "t", "target_t"))
            target_t = int(bridge["target_t"])
            if target_t != source_t + 1:
                raise SystemExit("bridge target_t must be source_t + 1")
            old_pi = parse_image(source["permutation_image"])
            old_n = 6 * source_t
            new_n = 6 * target_t
            new_block = tuple(range(old_n, new_n))
            block_perm = tuple(int(part) for part in bridge["first_hit_perm"].split())
            if len(block_perm) != 6:
                raise SystemExit("first_hit_perm must have length 6")

            pi = list(range(new_n))
            pi[:old_n] = old_pi
            for domain, image in zip(new_block, block_perm):
                pi[domain] = image
            new_domain = int(bridge["new_domain"])
            pi[old_domain], pi[new_domain] = pi[new_domain], pi[old_domain]

            target_p = int(bridge["target_p"])
            target_q = int(bridge["target_q"])
            gamma = gamma_perm(6, target_t)
            gamma_inv = inverse_perm(gamma)
            score, data = score_split(
                target_t,
                target_p,
                target_q,
                pi,
                gamma,
                gamma_inv,
                args.connected_weight,
            )
            if score != 0:
                raise SystemExit(
                    f"selected bridge choice failed verification: old_domain={old_domain}, offset={offset}"
                )
            writer.writerow(
                {
                    "t": target_t,
                    "g": bridge["target_g"],
                    "p": bridge["target_p"],
                    "q": bridge["target_q"],
                    "source_row": source_row,
                    "old_domain": old_domain,
                    "new_domain_offset": offset,
                    "new_domain": new_domain,
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
