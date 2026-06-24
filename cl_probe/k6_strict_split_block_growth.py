#!/usr/bin/env python3
"""Grow strict split witnesses by adding one 6-block and one bridge.

Given strict split witness certificates at size `t`, this deterministic probe
tries to populate strict split slots at size `t+1` as follows:

1. keep the old permutation on the first `6t` points;
2. choose an internal permutation of the new 6-point block;
3. swap one old image with one new image to connect the new block.

The search is finite and constructive.  A found row is a verified witness; a
miss is not a proof of nonexistence for the target slot.
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
from k6_strict_split_near_hit_local_profile import parse_image


FIELDNAMES = [
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


def load_witnesses(path: Path) -> list[dict[str, str]]:
    with path.open(newline="") as handle:
        return [row for row in csv.DictReader(handle)]


def row_value(row: dict[str, str], *names: str) -> str:
    for name in names:
        value = row.get(name)
        if value is not None and value != "":
            return value
    raise KeyError(f"none of these columns is available: {names}")


def format_swap(swap: tuple[int, int] | None) -> str:
    if swap is None:
        return ""
    return f"{swap[0]}:{swap[1]}"


def format_perm(perm: tuple[int, ...] | None) -> str:
    if perm is None:
        return ""
    return " ".join(str(x) for x in perm)


def strict_targets(t: int) -> list[tuple[int, int, int]]:
    out: list[tuple[int, int, int]] = []
    for g in balanced_rows(t):
        strict, _boundary = split_slots(t, g)
        for p, q in strict:
            out.append((g, p, q))
    return out


def try_grow(
    source: dict[str, str],
    *,
    target_t: int,
    target_g: int,
    target_p: int,
    target_q: int,
    connected_weight: int,
) -> dict[str, object]:
    source_t = int(row_value(source, "t", "target_t"))
    if target_t != source_t + 1:
        raise ValueError("this growth probe only supports target_t = source_t + 1")

    old_pi = parse_image(source["permutation_image"])
    old_n = 6 * source_t
    new_n = 6 * target_t
    if len(old_pi) != old_n:
        raise ValueError("source permutation length does not match source_t")

    new_block = tuple(range(old_n, new_n))
    gamma = gamma_perm(6, target_t)
    gamma_inv = inverse_perm(gamma)
    checked = 0
    best_score: int | None = None
    best_data = None
    best_swap: tuple[int, int] | None = None
    best_perm: tuple[int, ...] | None = None

    for block_perm in itertools.permutations(new_block):
        pi = list(range(new_n))
        pi[:old_n] = old_pi
        for domain, image in zip(new_block, block_perm):
            pi[domain] = image
        for old_domain in range(old_n):
            for new_domain in new_block:
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
                    best_swap = (old_domain, new_domain)
                    best_perm = block_perm
                if score == 0:
                    return {
                        "status": "found",
                        "checked": checked,
                        "bridge_swap": format_swap((old_domain, new_domain)),
                        "new_block_perm": format_perm(block_perm),
                        "data": data,
                        "pi": pi.copy(),
                    }
                pi[old_domain], pi[new_domain] = pi[new_domain], pi[old_domain]

    assert best_score is not None and best_data is not None
    return {
        "status": f"miss_best_score_{best_score}",
        "checked": checked,
        "bridge_swap": format_swap(best_swap),
        "new_block_perm": format_perm(best_perm),
        "data": best_data,
        "pi": [],
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("source_witness_csv", type=Path)
    parser.add_argument("--source-index", type=int, default=0)
    parser.add_argument("--target-t", type=int)
    parser.add_argument("--connected-weight", type=int, default=8)
    parser.add_argument("--emit-permutation", action="store_true")
    args = parser.parse_args()

    sources = load_witnesses(args.source_witness_csv)
    if not sources:
        raise SystemExit("source witness CSV is empty")
    if not (0 <= args.source_index < len(sources)):
        raise SystemExit("source-index out of range")

    source = sources[args.source_index]
    source_t = int(row_value(source, "t", "target_t"))
    target_t = args.target_t if args.target_t is not None else source_t + 1
    if target_t != source_t + 1:
        raise SystemExit("target-t must be source_t + 1")

    writer = csv.DictWriter(sys.stdout, fieldnames=FIELDNAMES, lineterminator="\n")
    writer.writeheader()
    for target_g, target_p, target_q in strict_targets(target_t):
        result = try_grow(
            source,
            target_t=target_t,
            target_g=target_g,
            target_p=target_p,
            target_q=target_q,
            connected_weight=args.connected_weight,
        )
        data = result["data"]
        writer.writerow(
            {
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
