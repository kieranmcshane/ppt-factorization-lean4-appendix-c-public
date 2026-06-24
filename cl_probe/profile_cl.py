#!/usr/bin/env python3
"""Proportional-energy profile checks for the CL variational criterion.

The fixed-excess fit in analyze_cl.py intentionally studies bands
E = 2r + t.  This script looks at the complementary finite-data question:
what happens to bands with E/r away from 2?

For each exact band it prints the empirical entropy density

    beta_emp(r,E) = log N_r(E) / (r log r)

and the leading diagonal CL margin

    beta_emp - (k/(k+1)) * (E/(2r)) - k/(k+1).

For k=2 this is beta_emp - E/(3r) - 2/3.  A negative value is supportive
finite evidence for CL at that band.  It is not a proof: beta_emp still has
large lower-order finite-r contamination, and exact data here are small.  For
that reason the headline verdict is computed only on a tail window, defaulting
to r >= 6.
"""

from __future__ import annotations

import argparse
import csv
import math
from collections import defaultdict
from pathlib import Path


def read_aggregate(path: Path, k: int) -> dict[tuple[int, int], int]:
    out: dict[tuple[int, int], int] = defaultdict(int)
    with path.open() as f:
        for row in csv.DictReader(f):
            if int(row["k"]) != k:
                continue
            out[(int(row["r"]), int(row["E"]))] += int(row["count"])
    return dict(out)


def diagonal_leading_margin(k: int, r: int, E: int, count: int) -> float:
    beta = math.log(count) / (r * math.log(r))
    logn_coeff = k / (k + 1)
    return beta - logn_coeff * (E / (2 * r)) - logn_coeff


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--k", type=int, default=2)
    parser.add_argument(
        "--csv",
        type=Path,
        default=Path(__file__).with_name("spectrum_k2_character.csv"),
    )
    parser.add_argument("--tail-min-r", type=int, default=6)
    args = parser.parse_args()

    agg = read_aggregate(args.csv, args.k)
    by_r: dict[int, list[tuple[int, int]]] = defaultdict(list)
    for (r, E), count in agg.items():
        by_r[r].append((E, count))

    print(f"# Proportional-energy profile from {args.csv} for k={args.k}")
    print("# margin = log(count)/(r log r) - (k/(k+1))*E/(2r) - k/(k+1)")
    print("r,E,alpha,log_count_over_r_log_r,leading_margin,count")
    worst = None
    worst_tail = None
    entropy_peaks = []
    for r in sorted(by_r):
        if r <= 1:
            continue
        rows = sorted(by_r[r])
        peak = max(rows, key=lambda item: item[1])
        entropy_peaks.append((r, peak[0], peak[1]))
        for E, count in rows:
            beta = math.log(count) / (r * math.log(r))
            margin = diagonal_leading_margin(args.k, r, E, count)
            candidate = (margin, r, E, count, beta)
            if worst is None or candidate > worst:
                worst = candidate
            if r >= args.tail_min_r and (
                worst_tail is None or candidate > worst_tail
            ):
                worst_tail = candidate
            print(f"{r},{E},{E/r:.9g},{beta:.9g},{margin:.9g},{count}")

    print()
    print("# Entropy peak by r")
    print("r,E_peak,alpha_peak,count_peak")
    for r, E, count in entropy_peaks:
        print(f"{r},{E},{E/r:.9g},{count}")

    if worst is not None:
        margin, r, E, count, beta = worst
        print()
        print("# Least favorable observed band by leading margin")
        print("r,E,alpha,beta_emp,leading_margin,count")
        print(f"{r},{E},{E/r:.9g},{beta:.9g},{margin:.9g},{count}")
        if margin < 0:
            print("all-r verdict: no observed leading-margin breach")
        else:
            print("all-r verdict: finite-size leading-margin breach")

    if worst_tail is not None:
        margin, r, E, count, beta = worst_tail
        print()
        print(f"# Least favorable observed band with r >= {args.tail_min_r}")
        print("r,E,alpha,beta_emp,leading_margin,count")
        print(f"{r},{E},{E/r:.9g},{beta:.9g},{margin:.9g},{count}")
        if margin < 0:
            print("tail-window verdict: no observed proportional-band breach")
        else:
            print("tail-window verdict: finite-data leading-margin breach")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
