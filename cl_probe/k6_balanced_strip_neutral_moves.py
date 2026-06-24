#!/usr/bin/env python3
"""Profile one-swap neutral neighborhoods of k=6 strip certificates.

This is a deterministic finite diagnostic, not an asymptotic count.  For each
stored witness permutation, the script swaps two images of pi, recomputes the
two bidefects, and counts how many swaps keep the same balanced target row.
It then checks connectedness only for row-preserving swaps.
"""

from __future__ import annotations

import argparse
import csv
import math
import sys
from pathlib import Path

from bidefect_target_local_search import gamma_perm, inverse_perm, orbit_count, row_data
from k6_balanced_strip_certificates import decode_perm, verify_perm_row


FIELDNAMES = [
    "t",
    "g",
    "total_swaps",
    "row_preserving_swaps",
    "connected_row_preserving_swaps",
    "exact_triple_swaps",
    "row_preserving_density",
    "connected_density",
    "log_connected_over_t_log_t",
]


def profile_row(row: dict[str, str]) -> dict[str, int | float]:
    ok, message = verify_perm_row(row)
    if not ok:
        raise ValueError(message)

    t = int(row["t"])
    g = int(row["g"])
    pi = decode_perm(row["permutation_image"])
    n = 6 * t
    gamma = gamma_perm(6, t)
    gamma_inv = inverse_perm(gamma)
    target_defect = 2 * (t - 1) + 2 * g
    original_triple = (
        int(row["c_pi"]),
        int(row["c_gamma_pi"]),
        int(row["c_pi_gamma_inv"]),
    )

    total_swaps = n * (n - 1) // 2
    row_preserving = 0
    connected_row_preserving = 0
    exact_triple = 0

    for i in range(n):
        for j in range(i + 1, n):
            pi[i], pi[j] = pi[j], pi[i]
            c_pi, c_gamma_pi, c_pi_gamma_inv, plus, minus, g_plus, g_minus = row_data(
                6, t, pi, gamma, gamma_inv
            )
            same_row = (
                plus == target_defect
                and minus == target_defect
                and g_plus == g
                and g_minus == g
            )
            if same_row:
                row_preserving += 1
                if (c_pi, c_gamma_pi, c_pi_gamma_inv) == original_triple:
                    exact_triple += 1
                if orbit_count(pi, gamma) == 1:
                    connected_row_preserving += 1
            pi[i], pi[j] = pi[j], pi[i]

    row_density = row_preserving / total_swaps if total_swaps else 0.0
    connected_density = connected_row_preserving / total_swaps if total_swaps else 0.0
    if connected_row_preserving > 0 and t > 1:
        beta_proxy = math.log(connected_row_preserving) / (t * math.log(t))
    else:
        beta_proxy = 0.0

    return {
        "t": t,
        "g": g,
        "total_swaps": total_swaps,
        "row_preserving_swaps": row_preserving,
        "connected_row_preserving_swaps": connected_row_preserving,
        "exact_triple_swaps": exact_triple,
        "row_preserving_density": row_density,
        "connected_density": connected_density,
        "log_connected_over_t_log_t": beta_proxy,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate_csv", type=Path)
    parser.add_argument("--t-min", type=int)
    parser.add_argument("--t-max", type=int)
    parser.add_argument("--first-balanced-only", action="store_true")
    args = parser.parse_args()

    writer = csv.DictWriter(sys.stdout, fieldnames=FIELDNAMES, lineterminator="\n")
    writer.writeheader()
    rows = 0
    with args.certificate_csv.open(newline="") as handle:
        reader = csv.DictReader(handle)
        seen_t: set[int] = set()
        for row in reader:
            t = int(row["t"])
            if args.t_min is not None and t < args.t_min:
                continue
            if args.t_max is not None and t > args.t_max:
                continue
            if args.first_balanced_only and t in seen_t:
                continue
            seen_t.add(t)
            writer.writerow(profile_row(row))
            rows += 1
    print(f"# profiled_rows={rows}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
