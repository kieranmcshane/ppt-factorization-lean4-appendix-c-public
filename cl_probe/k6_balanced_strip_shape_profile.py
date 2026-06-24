#!/usr/bin/env python3
"""Cycle-shape profile for certified k=6 balanced-strip witnesses.

This is a deterministic finite diagnostic.  It records how the forced
balanced-row equation

    #pi + #(gamma*pi) = #pi + #(pi*gamma^-1)

is split in the stored certificates, together with coarse cycle-shape data.
"""

from __future__ import annotations

import argparse
import csv
import sys
from collections import Counter
from pathlib import Path

from bidefect_target_local_search import compose, gamma_perm, inverse_perm
from k6_balanced_strip_certificates import decode_perm, verify_perm_row


FIELDNAMES = [
    "t",
    "g",
    "target_sum",
    "c_pi",
    "c_side",
    "g_over_t",
    "c_pi_over_t",
    "c_side_over_t",
    "pi_fixed_fraction",
    "plus_fixed_fraction",
    "minus_fixed_fraction",
    "pi_largest_fraction",
    "plus_largest_fraction",
    "minus_largest_fraction",
    "pi_small_cycle_hist",
    "plus_small_cycle_hist",
    "minus_small_cycle_hist",
]


def cycle_lengths(p: list[int] | tuple[int, ...]) -> list[int]:
    seen = [False] * len(p)
    out: list[int] = []
    for start in range(len(p)):
        if seen[start]:
            continue
        cur = start
        length = 0
        while not seen[cur]:
            seen[cur] = True
            length += 1
            cur = p[cur]
        out.append(length)
    return sorted(out, reverse=True)


def small_hist(lengths: list[int], max_len: int = 6) -> str:
    counts = Counter(lengths)
    return ";".join(f"{i}:{counts[i]}" for i in range(1, max_len + 1))


def fraction_with_length(lengths: list[int], length: int, n: int) -> float:
    return Counter(lengths)[length] / n


def profile_row(row: dict[str, str]) -> dict[str, int | float | str]:
    ok, message = verify_perm_row(row)
    if not ok:
        raise ValueError(message)

    t = int(row["t"])
    g = int(row["g"])
    n = 6 * t
    pi = decode_perm(row["permutation_image"])
    gamma = gamma_perm(6, t)
    gamma_inv = inverse_perm(gamma)
    plus = compose(gamma, pi)
    minus = compose(pi, gamma_inv)
    pi_lengths = cycle_lengths(pi)
    plus_lengths = cycle_lengths(plus)
    minus_lengths = cycle_lengths(minus)
    c_pi = len(pi_lengths)
    c_plus = len(plus_lengths)
    c_minus = len(minus_lengths)
    if c_plus != c_minus:
        raise ValueError(f"unbalanced side cycle counts at t={t},g={g}")
    target_sum = 5 * t + 2 - 2 * g
    if c_pi + c_plus != target_sum:
        raise ValueError(
            f"cycle-count split mismatch at t={t},g={g}: "
            f"{c_pi}+{c_plus}!={target_sum}"
        )

    return {
        "t": t,
        "g": g,
        "target_sum": target_sum,
        "c_pi": c_pi,
        "c_side": c_plus,
        "g_over_t": g / t,
        "c_pi_over_t": c_pi / t,
        "c_side_over_t": c_plus / t,
        "pi_fixed_fraction": fraction_with_length(pi_lengths, 1, n),
        "plus_fixed_fraction": fraction_with_length(plus_lengths, 1, n),
        "minus_fixed_fraction": fraction_with_length(minus_lengths, 1, n),
        "pi_largest_fraction": pi_lengths[0] / n,
        "plus_largest_fraction": plus_lengths[0] / n,
        "minus_largest_fraction": minus_lengths[0] / n,
        "pi_small_cycle_hist": small_hist(pi_lengths),
        "plus_small_cycle_hist": small_hist(plus_lengths),
        "minus_small_cycle_hist": small_hist(minus_lengths),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate_csv", type=Path)
    args = parser.parse_args()

    writer = csv.DictWriter(sys.stdout, fieldnames=FIELDNAMES, lineterminator="\n")
    writer.writeheader()
    rows = 0
    with args.certificate_csv.open(newline="") as handle:
        reader = csv.DictReader(handle)
        for row in reader:
            writer.writerow(profile_row(row))
            rows += 1
    print(f"# profiled_rows={rows}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
