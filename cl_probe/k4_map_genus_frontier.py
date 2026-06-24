#!/usr/bin/env python3
"""Conditional k=4 map/genus frontier.

This calculator is a proof-target diagnostic, not an enumerator.

Assume a connected non-singleton k=4 component on t labelled blocks and genus h
has count

    <= exp(O(t)) * t! * t^(eta*h).

With Chapuy slicing one expects eta=3.  A non-singleton component has local
energy density at least 4, and h/t = (local_alpha - 4)/2 at leading order.
For a local component density a >= 4 this gives the map/genus bound

    beta_map(a) <= 1 + eta*(a - 4)/2.

The cycle-count envelope gives independently

    beta_cycle(a) <= 3/2 + a/4.

If a fraction q of all blocks belongs to such non-singleton components and the
rest are one-block active components at energy density 2, then

    alpha = 2 + q*(a - 2),
    beta  <= q * min(beta_map(a), beta_cycle(a)).

Optimizing over a gives an explicit conditional upper envelope for the
remaining k=4 window.  For eta=3 the local map/genus and cycle-count lines meet
at a = 26/5, and the envelope is below the CL threshold throughout the window
left by the previous component/cycle benchmark.
"""

from __future__ import annotations

import argparse


def threshold(alpha: float) -> float:
    return 0.8 + 0.4 * alpha


def beta_cycle(local_alpha: float) -> float:
    return 1.5 + 0.25 * local_alpha


def beta_map(local_alpha: float, eta: float) -> float:
    if local_alpha < 4:
        raise ValueError("non-singleton local density must be at least 4")
    return 1 + eta * (local_alpha - 4) / 2


def local_beta(local_alpha: float, eta: float) -> float:
    return min(beta_cycle(local_alpha), beta_map(local_alpha, eta))


def intersection_alpha(eta: float) -> float:
    """Intersection of beta_map(a) and beta_cycle(a)."""

    if eta <= 1:
        raise ValueError("exact optimizer currently assumes eta > 1")
    return (8 * eta + 2) / (2 * eta - 1)


def optimize_beta(alpha: float, eta: float) -> tuple[float, float, float]:
    """Return beta, local_alpha, q for the exact conditional envelope."""

    if alpha < 2:
        return 0.0, 4.0, 0.0

    pivot = intersection_alpha(eta)
    local_alpha = max(alpha, pivot)
    q = (alpha - 2) / (local_alpha - 2)
    beta = q * local_beta(local_alpha, eta)
    return beta, local_alpha, q


def worst_margin_on_interval(
    alpha_min: float, alpha_max: float, eta: float
) -> tuple[float, float, float, float, float]:
    """Return margin, alpha, beta, local_alpha, q on a closed interval."""

    pivot = intersection_alpha(eta)
    candidates = [alpha_min, alpha_max]
    if alpha_min <= pivot <= alpha_max:
        candidates.append(pivot)

    worst = None
    for alpha in candidates:
        beta, local_alpha, q = optimize_beta(alpha, eta)
        margin = beta - threshold(alpha)
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


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--eta", type=float, default=3.0)
    parser.add_argument("--alpha-min", type=float, default=2.0)
    parser.add_argument("--alpha-max", type=float, default=14 / 3)
    parser.add_argument("--alpha-step", type=float, default=0.1)
    args = parser.parse_args()

    print("# Conditional k=4 map/genus frontier")
    print("# Assumption: connected count <= exp(O(t)) t! t^(eta*h)")
    print("# exact optimizer for eta > 1; proof target only")
    print(f"# local_envelope_intersection={intersection_alpha(args.eta):.12g}")
    print("alpha,beta_bound,threshold,margin,local_alpha,q")
    worst: tuple[float, float, float, float, float] | None = None
    for alpha in frange(args.alpha_min, args.alpha_max, args.alpha_step):
        beta, local_alpha, q = optimize_beta(alpha, args.eta)
        target = threshold(alpha)
        margin = beta - target
        row = (margin, alpha, beta, local_alpha, q)
        if worst is None or row > worst:
            worst = row
        print(
            f"{alpha:.12g},{beta:.12g},{target:.12g},{margin:.12g},"
            f"{local_alpha:.12g},{q:.12g}"
        )

    assert worst is not None
    margin, alpha, beta, local_alpha, q = worst
    print()
    print("# Worst listed-row conditional margin")
    print("alpha,beta_bound,threshold,margin,local_alpha,q")
    print(
        f"{alpha:.12g},{beta:.12g},{threshold(alpha):.12g},{margin:.12g},"
        f"{local_alpha:.12g},{q:.12g}"
    )

    interval_worst = worst_margin_on_interval(args.alpha_min, args.alpha_max, args.eta)
    margin, alpha, beta, local_alpha, q = interval_worst
    print()
    print("# Exact worst conditional margin on requested interval")
    print("alpha,beta_bound,threshold,margin,local_alpha,q")
    print(
        f"{alpha:.12g},{beta:.12g},{threshold(alpha):.12g},{margin:.12g},"
        f"{local_alpha:.12g},{q:.12g}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
