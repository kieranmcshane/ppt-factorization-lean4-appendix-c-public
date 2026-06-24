#!/usr/bin/env python3
"""Local two-sided/bidefect exponent required by the full CL threshold.

This is a proof-target calculator, not a proof.

For an unbounded connected non-singleton component on t blocks, write

    s = (g_+ + g_-)/t,
    alpha_local = 4 + 2s.

If a two-sided connected count had the leading form

    count(t,g_+,g_-) <= exp(O(t)) * t! * t^(eta * (g_+ + g_-)),

then the local leading entropy would be

    beta_local = 1 + eta*s.

The full CL threshold at local energy alpha is

    T_k(alpha) = k/(k+1) * (1 + alpha/2).

Thus the connected count is locally compatible with the full CL threshold
provided

    eta <= (T_k(4+2s) - 1) / s.

The three-cycle-count envelope already closes the local window beyond
`cycle_crossing_alpha(k)`, so the direct component strategy only needs this
comparison up to

    s_cycle = (cycle_crossing_alpha(k) - 4)/2.

The minimum of the allowed eta over that window is exactly the eta_crit(k)
reported by k_map_genus_frontier.py.
"""

from __future__ import annotations

import argparse
import math


def threshold(k: int, alpha: float) -> float:
    return (k / (k + 1)) * (1 + alpha / 2)


def cycle_crossing_alpha(k: int) -> float | None:
    if k == 2:
        return None
    return (2 * k * k - 4 * k - 2) / (k - 1)


def s_cycle(k: int) -> float | None:
    crossing = cycle_crossing_alpha(k)
    if crossing is None:
        return None
    return max(0.0, (crossing - 4) / 2)


def eta_allowed(k: int, s: float) -> float:
    if s <= 0:
        return math.inf
    return (threshold(k, 4 + 2 * s) - 1) / s


def eta_critical(k: int) -> float | None:
    sc = s_cycle(k)
    if sc is None or sc <= 0:
        return None
    return eta_allowed(k, sc)


def margin(k: int, s: float, eta: float) -> float:
    return 1 + eta * s - threshold(k, 4 + 2 * s)


def frange(start: float, stop: float, step: float):
    value = start
    eps = step / 10
    while value <= stop + eps:
        yield round(value, 12)
        value += step


def fmt(value: float | None) -> str:
    if value is None:
        return "none"
    if math.isinf(value):
        return "inf"
    return f"{value:.12g}"


def table(k: int, step: float) -> None:
    sc = s_cycle(k)
    if sc is None:
        raise SystemExit("k=2 has no positive cycle-count obstruction window here")
    print("# Local bidefect exponent threshold")
    print(f"# k={k}")
    print(f"# cycle_crossing_alpha={cycle_crossing_alpha(k):.12g}")
    print(f"# s_cycle={sc:.12g}")
    print(f"# eta_critical={eta_critical(k):.12g}")
    print("k,s,alpha_local,eta_allowed,margin_eta_3,margin_eta_2,margin_eta_crit")
    critical = eta_critical(k)
    assert critical is not None
    for s in frange(step, sc, step):
        alpha = 4 + 2 * s
        print(
            f"{k},{s:.12g},{alpha:.12g},{eta_allowed(k, s):.12g},"
            f"{margin(k, s, 3):.12g},{margin(k, s, 2):.12g},"
            f"{margin(k, s, critical):.12g}"
        )
    if sc % step > 1e-9:
        s = sc
        alpha = 4 + 2 * s
        print(
            f"{k},{s:.12g},{alpha:.12g},{eta_allowed(k, s):.12g},"
            f"{margin(k, s, 3):.12g},{margin(k, s, 2):.12g},"
            f"{margin(k, s, critical):.12g}"
        )


def summary(table_k_max: int) -> None:
    print("# Local bidefect exponent threshold summary")
    print(
        "k,cycle_crossing_alpha,s_cycle,eta_critical,"
        "margin_eta_3_at_s_cycle,margin_eta_2_at_s_cycle"
    )
    for k in range(2, table_k_max + 1, 2):
        sc = s_cycle(k)
        critical = eta_critical(k)
        if sc is None or critical is None:
            print(f"{k},none,none,none,none,none")
            continue
        print(
            f"{k},{cycle_crossing_alpha(k):.12g},{sc:.12g},"
            f"{critical:.12g},{margin(k, sc, 3):.12g},"
            f"{margin(k, sc, 2):.12g}"
        )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--k", type=int, default=6)
    parser.add_argument("--s-step", type=float, default=0.25)
    parser.add_argument("--table-k-max", type=int, default=None)
    args = parser.parse_args()

    if args.k < 2:
        raise SystemExit("k must be at least 2")
    if args.s_step <= 0:
        raise SystemExit("s-step must be positive")

    if args.table_k_max is not None:
        summary(args.table_k_max)
    else:
        table(args.k, args.s_step)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
