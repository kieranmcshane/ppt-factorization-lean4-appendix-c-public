#!/usr/bin/env python3
"""Cheap invariant checks for the k=6 strict split slots.

This is a diagnostic, not a proof.  It records two facts:

* the necessary sign parity relation for a slot is automatic on the strict
  split lattice;
* a target-search CSV can be summarized by its best deficit pattern, so the
  current misses are easy to compare across runs.
"""

from __future__ import annotations

import argparse
import csv
from collections import Counter
from pathlib import Path

from k6_balanced_split_window import split_slots
from k6_remaining_arithmetic import balanced_rows


def parity_ok(t: int, p: int, q: int) -> bool:
    # For n=6t and gamma a product of t six-cycles,
    # sign(gamma*pi) = sign(gamma) sign(pi) forces q-p == t mod 2.
    return (q - p - t) % 2 == 0


def strict_slot_parity_counts(t_min: int, t_max: int) -> Counter[tuple[str, str]]:
    counts: Counter[tuple[str, str]] = Counter()
    for t in range(t_min, t_max + 1):
        for g in balanced_rows(t):
            strict, _boundary = split_slots(t, g)
            for p, q in strict:
                shape = "diagonal" if p == q else "off_diagonal"
                status = "parity_ok" if parity_ok(t, p, q) else "parity_bad"
                counts[(shape, status)] += 1
    return counts


def target_search_deficits(path: Path) -> Counter[tuple[int, int, int, int]]:
    counts: Counter[tuple[int, int, int, int]] = Counter()
    with path.open(newline="") as handle:
        reader = csv.DictReader(handle)
        for row in reader:
            p = int(row["p"])
            q = int(row["q"])
            score = int(row["best_score"])
            dp = int(row["best_c_pi"]) - p
            dq_plus = int(row["best_c_gamma_pi"]) - q
            dq_minus = int(row["best_c_pi_gamma_inv"]) - q
            counts[(score, dp, dq_plus, dq_minus)] += 1
    return counts


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--t-min", type=int, default=13)
    parser.add_argument("--t-max", type=int, default=80)
    parser.add_argument("--target-search-csv", type=Path)
    args = parser.parse_args()

    if args.t_min < 2:
        raise SystemExit("t-min must be at least 2")
    if args.t_max < args.t_min:
        raise SystemExit("t-max must be at least t-min")

    print("# k=6 strict split invariant sanity")
    print("# parity relation: q-p == t mod 2")
    print("section,key,value,count")
    for (shape, status), count in sorted(strict_slot_parity_counts(args.t_min, args.t_max).items()):
        print(f"parity,{shape},{status},{count}")

    if args.target_search_csv is not None:
        for (score, dp, dq_plus, dq_minus), count in target_search_deficits(
            args.target_search_csv
        ).most_common():
            key = f"score={score}"
            value = f"dp={dp};dq_plus={dq_plus};dq_minus={dq_minus}"
            print(f"target_search,{key},{value},{count}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
