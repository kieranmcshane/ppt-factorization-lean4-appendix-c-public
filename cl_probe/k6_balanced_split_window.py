#!/usr/bin/env python3
"""Exact cycle-count split window inside the k=6 balanced strip.

This is a proof-target calculator.  For a balanced row `(t,g,g)`, write

    p = #pi,
    q = #(gamma*pi) = #(pi*gamma^-1).

The row condition forces

    p + q = 5t + 2 - 2g.

The three-cycle-count envelope gives the leading bound

    beta <= 6 - max(p,q)/t.

The CL threshold on the row is

    T = (6/7) (3 + 2g/t).

Thus a split is still strictly dangerous for this envelope exactly when

    max(p,q) < t(6 - T) = 12(2t-g)/7.

This script lists the remaining strict and boundary split slots.
"""

from __future__ import annotations

import argparse
import csv
from fractions import Fraction
from pathlib import Path

from k6_remaining_arithmetic import balanced_rows


def target_sum(t: int, g: int) -> int:
    return 5 * t + 2 - 2 * g


def split_bound(t: int, g: int) -> Fraction:
    return Fraction(12 * (2 * t - g), 7)


def split_gap(t: int, g: int, p: int, q: int) -> Fraction:
    return split_bound(t, g) - max(p, q)


def split_slots(t: int, g: int) -> tuple[list[tuple[int, int]], list[tuple[int, int]]]:
    strict: list[tuple[int, int]] = []
    boundary: list[tuple[int, int]] = []
    total = target_sum(t, g)
    bound = split_bound(t, g)
    for p in range(1, total):
        q = total - p
        gap = bound - max(p, q)
        if gap > 0:
            strict.append((p, q))
        elif gap == 0:
            boundary.append((p, q))
    return strict, boundary


def load_cert_splits(path: Path | None) -> dict[tuple[int, int], list[tuple[int, int]]]:
    if path is None:
        return {}
    out: dict[tuple[int, int], list[tuple[int, int]]] = {}
    with path.open(newline="") as handle:
        reader = csv.DictReader(handle)
        for row in reader:
            t = int(row["t"])
            g = int(row["g"])
            p = int(row["c_pi"])
            q = int(row["c_gamma_pi"])
            out.setdefault((t, g), []).append((p, q))
    return out


def slot_text(slots: list[tuple[int, int]]) -> str:
    if not slots:
        return ""
    if len(slots) == 1:
        p, q = slots[0]
        return f"{p}:{q}"
    first = slots[0]
    last = slots[-1]
    return f"{first[0]}:{first[1]}..{last[0]}:{last[1]}"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--t-min", type=int, default=13)
    parser.add_argument("--t-max", type=int, default=80)
    parser.add_argument("--certificates", type=Path)
    args = parser.parse_args()

    if args.t_min < 2:
        raise SystemExit("t-min must be at least 2")
    if args.t_max < args.t_min:
        raise SystemExit("t-max must be at least t-min")

    certs = load_cert_splits(args.certificates)
    print("# k=6 balanced strip cycle-count split window")
    print("# strict_open means three-cycle-count envelope does not close the split")
    print("# boundary means equality in the leading cycle-count threshold")
    print(
        "t,g,target_sum,split_bound,strict_open_count,boundary_count,"
        "strict_open_splits,boundary_splits,cert_splits,cert_best_gap"
    )

    rows = strict_rows = boundary_rows = cert_strict_hits = 0
    for t in range(args.t_min, args.t_max + 1):
        for g in balanced_rows(t):
            rows += 1
            strict, boundary = split_slots(t, g)
            if strict:
                strict_rows += 1
            if boundary:
                boundary_rows += 1
            cert_list = certs.get((t, g), [])
            cert_gap = ""
            if cert_list:
                gaps = [split_gap(t, g, p, q) for p, q in cert_list]
                if any(gap > 0 for gap in gaps):
                    cert_strict_hits += 1
                cert_gap = str(max(gaps))
            cert_text = ";".join(f"{p}:{q}" for p, q in cert_list)
            print(
                f"{t},{g},{target_sum(t,g)},{split_bound(t,g)},"
                f"{len(strict)},{len(boundary)},"
                f"{slot_text(strict)},{slot_text(boundary)},"
                f"{cert_text},{cert_gap}"
            )

    print()
    print(
        "t_min,t_max,rows,strict_open_rows,boundary_rows,"
        "certificate_rows_with_strict_open_hit"
    )
    print(
        f"{args.t_min},{args.t_max},{rows},{strict_rows},"
        f"{boundary_rows},{cert_strict_hits}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
