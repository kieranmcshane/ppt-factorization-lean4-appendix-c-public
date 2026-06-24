#!/usr/bin/env python3
"""Min-genus bidefect threshold for the unbounded-component CL frontier.

This is a proof-target calculator, not a proof.

The direct total-bidefect route assumes a connected bidefect estimate of the
form

    count(t,g_+,g_-) <= exp(O(t)) * t! * t^(eta_sum * (g_+ + g_-)).

The standard one-sided map estimate gives a different intersection bound:
for fixed `(g_+,g_-)`, the two-sided class is contained in each one-sided
class, hence

    count(t,g_+,g_-) <= exp(O(t)) * t! * t^(eta_min * min(g_+,g_-)).

With the usual Chapuy slicing exponent, `eta_min=3`.  If

    s = (g_+ + g_-)/t,
    alpha_local = 4 + 2s,

then the largest min-genus exponent at fixed `s` occurs in the balanced split
and gives the local entropy envelope

    beta_local <= 1 + eta_min * s/2.

The full CL local threshold is

    T_k(alpha) = k/(k+1) * (1 + alpha/2).

Thus the min-genus route is locally compatible when

    1 + eta_min*s/2 <= T_k(4+2s).

The cycle-count envelope takes over at `cycle_crossing_alpha(k)`, so the
relevant endpoint is `s_cycle = (cycle_crossing_alpha(k)-4)/2`.
"""

from __future__ import annotations

import argparse
import math


def threshold(k: int, alpha: float) -> float:
    return (k / (k + 1)) * (1 + alpha / 2)


def cycle_crossing_alpha(k: int) -> float | None:
    if k < 4:
        return None
    return (2 * k * k - 4 * k - 2) / (k - 1)


def s_cycle(k: int) -> float | None:
    crossing = cycle_crossing_alpha(k)
    if crossing is None:
        return None
    return max(0.0, (crossing - 4) / 2)


def eta_min_allowed(k: int, s: float) -> float:
    if s <= 0:
        return math.inf
    return 2 * (threshold(k, 4 + 2 * s) - 1) / s


def eta_min_critical(k: int) -> float | None:
    sc = s_cycle(k)
    if sc is None or sc <= 0:
        return None
    return eta_min_allowed(k, sc)


def beta_min_genus(s: float, eta_min: float) -> float:
    return 1 + eta_min * s / 2


def margin(k: int, s: float, eta_min: float) -> float:
    return beta_min_genus(s, eta_min) - threshold(k, 4 + 2 * s)


def closed_s_max(k: int, eta_min: float) -> float:
    """Largest s closed by the min-genus route.

    Returns infinity when the slope is already below the threshold slope.
    """

    denom = (eta_min / 2) * (k + 1) - k
    if denom <= 0:
        return math.inf
    return (2 * k - 1) / denom


def fmt(value: float | None) -> str:
    if value is None:
        return "none"
    if math.isinf(value):
        return "inf"
    return f"{value:.12g}"


def frange(start: float, stop: float, step: float):
    value = start
    eps = step / 10
    while value <= stop + eps:
        yield round(value, 12)
        value += step


def table(k: int, eta_min: float, step: float) -> None:
    sc = s_cycle(k)
    if sc is None:
        raise SystemExit("this local cycle window is empty for k < 4")
    critical = eta_min_critical(k)
    assert critical is not None
    print("# Min-genus bidefect threshold")
    print("# Assumption: count <= exp(O(t)) t! t^(eta_min*min(g_plus,g_minus))")
    print(f"# k={k}")
    print(f"# cycle_crossing_alpha={cycle_crossing_alpha(k):.12g}")
    print(f"# s_cycle={sc:.12g}")
    print(f"# eta_min_critical={critical:.12g}")
    print(f"# closed_s_max_at_eta_min={fmt(closed_s_max(k, eta_min))}")
    print(
        "k,s,alpha_local,eta_min_allowed,margin_eta_min,"
        "margin_eta_min_3,margin_eta_min_critical"
    )
    last_s = None
    for s in frange(step, sc, step):
        last_s = s
        print(
            f"{k},{s:.12g},{4 + 2*s:.12g},{eta_min_allowed(k, s):.12g},"
            f"{margin(k, s, eta_min):.12g},{margin(k, s, 3):.12g},"
            f"{margin(k, s, critical):.12g}"
        )
    if last_s is None or abs(last_s - sc) > 1e-9:
        s = sc
        print(
            f"{k},{s:.12g},{4 + 2*s:.12g},{eta_min_allowed(k, s):.12g},"
            f"{margin(k, s, eta_min):.12g},{margin(k, s, 3):.12g},"
            f"{margin(k, s, critical):.12g}"
        )


def summary(table_k_max: int, eta_min: float) -> None:
    print("# Min-genus bidefect threshold summary")
    print("# eta_min is the exponent on min(g_plus,g_minus)")
    print(
        "k,cycle_crossing_alpha,s_cycle,eta_min_critical,"
        "closed_s_max_at_eta_min,remaining_s_window,margin_at_s_cycle,verdict"
    )
    for k in range(2, table_k_max + 1, 2):
        sc = s_cycle(k)
        critical = eta_min_critical(k)
        if sc is None or critical is None:
            print(f"{k},none,none,none,none,none,none,no_cycle_window")
            continue
        closed = closed_s_max(k, eta_min)
        if math.isinf(closed) or closed >= sc:
            remaining = "empty"
            verdict = "closes_pre_cycle_window"
        else:
            remaining = f"{closed:.12g}<s<{sc:.12g}"
            verdict = "leaves_endpoint_window"
        print(
            f"{k},{cycle_crossing_alpha(k):.12g},{sc:.12g},"
            f"{critical:.12g},{fmt(closed)},{remaining},"
            f"{margin(k, sc, eta_min):.12g},{verdict}"
        )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--k", type=int, default=6)
    parser.add_argument("--eta-min", type=float, default=3.0)
    parser.add_argument("--s-step", type=float, default=0.25)
    parser.add_argument("--table-k-max", type=int, default=None)
    args = parser.parse_args()

    if args.k < 2:
        raise SystemExit("k must be at least 2")
    if args.eta_min <= 0:
        raise SystemExit("eta-min must be positive")
    if args.s_step <= 0:
        raise SystemExit("s-step must be positive")

    if args.table_k_max is not None:
        summary(args.table_k_max, args.eta_min)
    else:
        table(args.k, args.eta_min, args.s_step)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
