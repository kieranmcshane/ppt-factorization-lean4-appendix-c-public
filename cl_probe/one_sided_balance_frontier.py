#!/usr/bin/env python3
"""Merger/genus balance frontier for the one-sided defect target.

This is a proof-target calculator.  Write

    M = r - c(pi),
    G = sum non-singleton connected one-sided genera.

A standard connected-map estimate with Chapuy exponent 3, combined with the
labelled SET decomposition, gives the leading benchmark

    beta_+ <= M/r + 3G/r.

The critical one-sided target eta=2 asks, on the non-singleton part, for

    beta_+ <= 2(M+G)/r.

Thus this map/SET benchmark closes the region G <= M.  Separately, the crude
one-sided cycle-count bound closes the high plus-defect edge

    delta_+/(2r) >= (k-1)/2

at eta=2.  The remaining benchmark gap is therefore

    G > M  and  delta_+/(2r) < (k-1)/2,

after singleton components have been removed as finite-type `exp(O(r))` data.

The script samples this two-parameter frontier.
"""

from __future__ import annotations

import argparse


def map_set_margin(merger: float, genus: float) -> float:
    """Map/SET beta minus eta=2 target, in leading r log r units."""

    return (merger + 3 * genus) - 2 * (merger + genus)


def cycle_threshold(k: int) -> float:
    """Half-defect density (M+G)/r where eta=2 cycle counts begin to close."""

    return (k - 1) / 2


def classify(k: int, merger: float, genus: float) -> str:
    if genus <= merger:
        return "map_set_closes"
    if merger + genus >= cycle_threshold(k):
        return "cycle_closes"
    return "open_benchmark"


def frange(start: float, stop: float, step: float):
    value = start
    eps = step / 10
    while value <= stop + eps:
        yield round(value, 12)
        value += step


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--k", type=int, default=6)
    parser.add_argument("--step", type=float, default=0.5)
    parser.add_argument("--density-max", type=float, default=None)
    parser.add_argument("--table-k-max", type=int, default=None)
    args = parser.parse_args()

    if args.k < 2:
        raise SystemExit("k must be at least 2")

    if args.table_k_max is not None:
        print("# One-sided merger/genus balance frontier at eta=2")
        print("k,cycle_half_defect_threshold,open_region")
        for k in range(2, args.table_k_max + 1, 2):
            threshold = cycle_threshold(k)
            open_region = f"G_ns>M and delta_plus/(2r)<{threshold:.12g}"
            print(f"{k},{threshold:.12g},{open_region}")
        return 0

    density_max = args.density_max
    if density_max is None:
        density_max = args.k / 2

    print("# One-sided merger/genus balance frontier at eta=2")
    print(f"# cycle_half_defect_threshold={cycle_threshold(args.k):.12g}")
    print("k,M_over_r,G_over_r,half_defect_density,map_set_margin,status")
    counts: dict[str, int] = {
        "map_set_closes": 0,
        "cycle_closes": 0,
        "open_benchmark": 0,
    }
    for merger in frange(0.0, density_max, args.step):
        for genus in frange(0.0, density_max - merger, args.step):
            status = classify(args.k, merger, genus)
            counts[status] += 1
            print(
                f"{args.k},{merger:.12g},{genus:.12g},"
                f"{merger + genus:.12g},{map_set_margin(merger, genus):.12g},"
                f"{status}"
            )

    print()
    print("# Sampled status counts")
    print("status,count")
    for status, count in counts.items():
        print(f"{status},{count}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
