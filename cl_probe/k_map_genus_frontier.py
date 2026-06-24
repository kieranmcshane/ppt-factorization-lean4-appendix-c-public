#!/usr/bin/env python3
"""General even-k map/genus component frontier.

This is a proof-target calculator, not an enumerator.

Assume that connected non-singleton degree-k components on t labelled blocks
and total genus parameter h satisfy

    count(t,h) <= exp(O(t)) * t! * t^(eta*h).

As in the k=4 proof packet, a connected non-singleton component has local
energy density a >= 4 and h/t = (a - 4)/2 at leading order.  This gives the
map/genus local envelope

    beta_map(a) <= 1 + eta*(a - 4)/2.

The three-cycle-count envelope gives independently

    beta_cycle,k(a) <= (k - 1)/2 + a/4.

If a fraction q of all blocks belongs to non-singleton components and the
rest are one-block active components at energy density 2, then

    alpha = 2 + q*(a - 2),
    beta  <= q * min(beta_map(a), beta_cycle,k(a)).

For eta > 1, beta_map(a)/(a-2) is increasing and beta_cycle,k(a)/(a-2) is
decreasing, so the optimizer is the intersection of the two local envelopes,
unless the requested total density alpha is already beyond that intersection.
"""

from __future__ import annotations

import argparse


def threshold(k: int, alpha: float) -> float:
    return (k / (k + 1)) * (1 + alpha / 2)


def beta_cycle(k: int, local_alpha: float) -> float:
    return (k - 1) / 2 + local_alpha / 4


def beta_map(local_alpha: float, eta: float) -> float:
    if local_alpha < 4:
        raise ValueError("non-singleton local density must be at least 4")
    return 1 + eta * (local_alpha - 4) / 2


def local_beta(k: int, local_alpha: float, eta: float) -> float:
    return min(beta_cycle(k, local_alpha), beta_map(local_alpha, eta))


def intersection_alpha(k: int, eta: float) -> float:
    """Intersection of beta_map(a) and beta_cycle,k(a)."""

    if eta <= 0.5:
        raise ValueError("intersection formula requires eta > 1/2")
    return (2 * k - 6 + 8 * eta) / (2 * eta - 1)


def cycle_crossing_alpha(k: int) -> float:
    """Where the cycle-count envelope meets the CL threshold."""

    return (2 * k * k - 4 * k - 2) / (k - 1)


def eta_critical(k: int) -> float:
    """Largest eta for which this component strategy closes the central range.

    For eta > 1, the component optimizer is controlled by the intersection of
    the map/genus and cycle-count local envelopes.  The strategy closes exactly
    when that intersection lies at or to the right of the cycle-count/threshold
    crossing.  Solving the equality gives this value.
    """

    denom = k * k - 4 * k + 1
    if denom <= 0:
        raise ValueError("eta_critical formula expects even k >= 4")
    return (k * k - 3 * k + 1) / denom


def optimize_beta(k: int, alpha: float, eta: float) -> tuple[float, float, float]:
    """Return beta, local_alpha, q for the component envelope."""

    if alpha < 2:
        return 0.0, 4.0, 0.0
    if eta <= 1:
        raise ValueError("exact optimizer currently assumes eta > 1")

    pivot = intersection_alpha(k, eta)
    local_alpha = max(alpha, 4.0, pivot)
    q = (alpha - 2) / (local_alpha - 2)
    beta = q * local_beta(k, local_alpha, eta)
    return beta, local_alpha, q


def worst_margin_on_interval(
    k: int, alpha_min: float, alpha_max: float, eta: float
) -> tuple[float, float, float, float, float]:
    """Return margin, alpha, beta, local_alpha, q on a closed interval."""

    candidates = [alpha_min, alpha_max]
    pivot = intersection_alpha(k, eta)
    if alpha_min <= pivot <= alpha_max:
        candidates.append(pivot)

    worst = None
    for alpha in candidates:
        beta, local_alpha, q = optimize_beta(k, alpha, eta)
        margin = beta - threshold(k, alpha)
        row = (margin, alpha, beta, local_alpha, q)
        if worst is None or row > worst:
            worst = row
    assert worst is not None
    return worst


def frange(start: float, stop: float, step: float):
    value = start
    eps = step / 10
    while value <= stop + eps:
        yield round(value, 12)
        value += step


def print_table(table_k_max: int, eta: float) -> None:
    print("# General even-k map/genus component frontier")
    print("# Assumption: connected count <= exp(O(t)) t! t^(eta*h)")
    print("# interval: 2 <= alpha <= 2k")
    print(
        "k,eta,eta_critical,cycle_crossing_alpha,pivot_alpha,worst_alpha,"
        "beta_bound,threshold,margin,verdict"
    )
    for k in range(2, table_k_max + 1, 2):
        margin, alpha, beta, local_alpha, q = worst_margin_on_interval(
            k, 2.0, 2.0 * k, eta
        )
        verdict = "closes" if margin < 0 else "does_not_close"
        critical = "all" if k == 2 else f"{eta_critical(k):.12g}"
        crossing = "all" if k == 2 else f"{cycle_crossing_alpha(k):.12g}"
        print(
            f"{k},{eta:.12g},{critical},{crossing},"
            f"{intersection_alpha(k, eta):.12g},"
            f"{alpha:.12g},{beta:.12g},{threshold(k, alpha):.12g},"
            f"{margin:.12g},{verdict}"
        )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--k", type=int, default=4)
    parser.add_argument("--eta", type=float, default=3.0)
    parser.add_argument("--alpha-min", type=float, default=2.0)
    parser.add_argument("--alpha-max", type=float, default=None)
    parser.add_argument("--alpha-step", type=float, default=0.25)
    parser.add_argument("--table-k-max", type=int, default=None)
    args = parser.parse_args()

    if args.k < 2:
        raise SystemExit("k must be at least 2")
    if args.eta <= 1:
        raise SystemExit("this optimizer currently assumes eta > 1")

    if args.table_k_max is not None:
        print_table(args.table_k_max, args.eta)
        return 0

    alpha_max = args.alpha_max
    if alpha_max is None:
        alpha_max = 2 * args.k

    print("# General even-k map/genus component frontier")
    print("# Assumption: connected count <= exp(O(t)) t! t^(eta*h)")
    print(f"# local_envelope_intersection={intersection_alpha(args.k, args.eta):.12g}")
    if args.k >= 4:
        print(f"# eta_critical={eta_critical(args.k):.12g}")
        print(f"# cycle_crossing_alpha={cycle_crossing_alpha(args.k):.12g}")
    print("k,eta,alpha,beta_bound,threshold,margin,local_alpha,q")
    worst = None
    for alpha in frange(args.alpha_min, alpha_max, args.alpha_step):
        beta, local_alpha, q = optimize_beta(args.k, alpha, args.eta)
        target = threshold(args.k, alpha)
        margin = beta - target
        row = (margin, alpha, beta, local_alpha, q)
        if worst is None or row > worst:
            worst = row
        print(
            f"{args.k},{args.eta:.12g},{alpha:.12g},{beta:.12g},"
            f"{target:.12g},{margin:.12g},{local_alpha:.12g},{q:.12g}"
        )

    assert worst is not None
    margin, alpha, beta, local_alpha, q = worst
    print()
    print("# Worst listed-row conditional margin")
    print("k,eta,alpha,beta_bound,threshold,margin,local_alpha,q")
    print(
        f"{args.k},{args.eta:.12g},{alpha:.12g},{beta:.12g},"
        f"{threshold(args.k, alpha):.12g},{margin:.12g},"
        f"{local_alpha:.12g},{q:.12g}"
    )

    margin, alpha, beta, local_alpha, q = worst_margin_on_interval(
        args.k, args.alpha_min, alpha_max, args.eta
    )
    print()
    print("# Exact worst conditional margin on requested interval")
    print("k,eta,alpha,beta_bound,threshold,margin,local_alpha,q")
    print(
        f"{args.k},{args.eta:.12g},{alpha:.12g},{beta:.12g},"
        f"{threshold(args.k, alpha):.12g},{margin:.12g},"
        f"{local_alpha:.12g},{q:.12g}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
