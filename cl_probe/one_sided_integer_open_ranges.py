#!/usr/bin/env python3
"""Integer open genus ranges for connected one-sided components.

For a connected non-singleton component on t blocks, M=t-1 and

    delta_+/2 = M + g.

The map/SET benchmark closes `g <= M`.  The one-sided cycle-count edge at
eta=2 closes `(M+g)/t >= (k-1)/2`.  Therefore a connected component can lie in
the benchmark-open region only if

    g >= t
    and
    (t - 1 + g)/t < (k - 1)/2.

This script prints the resulting integer intervals for g.  It is not a proof
of CL; it identifies where a remaining component-level estimate would have to
act.
"""

from __future__ import annotations

import argparse
import math


def open_range(k: int, t: int) -> tuple[int, int] | None:
    if t < 2:
        return None
    low = t
    # Strict inequality:
    #   g < ((k - 1) * t) / 2 - (t - 1)
    #     = ((k - 3) * t) / 2 + 1.
    upper_exclusive = ((k - 3) * t) / 2 + 1
    high = math.ceil(upper_exclusive) - 1
    if low > high:
        return None
    return low, high


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--k", type=int, default=6)
    parser.add_argument("--t-max", type=int, default=12)
    parser.add_argument("--table-k-max", type=int, default=None)
    args = parser.parse_args()

    if args.k < 2:
        raise SystemExit("k must be at least 2")

    if args.table_k_max is not None:
        print("# One-sided connected integer open ranges")
        print("k,t_min_with_open,first_open_range")
        for k in range(2, args.table_k_max + 1, 2):
            first = None
            for t in range(2, args.t_max + 1):
                interval = open_range(k, t)
                if interval is not None:
                    first = (t, interval)
                    break
            if first is None:
                print(f"{k},none,none")
            else:
                t, (low, high) = first
                print(f"{k},{t},{low}<=g<={high}")
        return 0

    print("# One-sided connected integer open ranges")
    print("k,t,g_min,g_max,status")
    for t in range(2, args.t_max + 1):
        interval = open_range(args.k, t)
        if interval is None:
            print(f"{args.k},{t},,,empty")
        else:
            low, high = interval
            print(f"{args.k},{t},{low},{high},open")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
