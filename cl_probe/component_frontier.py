#!/usr/bin/env python3
"""Component/cycle-count benchmark for the remaining k=4 CL window.

For k=4, a one-block active component has energy at least 2, while any
macroscopic connected component with at least two blocks has asymptotic local
energy at least 4.  Combining this component-energy split with the
three-cycle-count envelope for connected components gives, for 2 <= alpha <= 4,

    beta_4(alpha) <= (5/4) * (alpha - 2).

This benchmark closes the CL threshold up to alpha = 66/17.  The ordinary
three-cycle-count envelope closes alpha >= 14/3, leaving only the narrower
window 66/17 < alpha < 14/3 for k=4.
"""

from __future__ import annotations

import argparse


def threshold(k: int, alpha: float) -> float:
    return (k / (k + 1)) * (1 + alpha / 2)


def k4_component_beta(alpha: float) -> float:
    if alpha < 2:
        return 0.0
    if alpha <= 4:
        return 1.25 * (alpha - 2)
    return 1.5 + alpha / 4


def frange(start: float, stop: float, step: float):
    value = start
    eps = step / 10
    while value <= stop + eps:
        yield round(value, 12)
        value += step


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--alpha-min", type=float, default=2.0)
    parser.add_argument("--alpha-max", type=float, default=14 / 3)
    parser.add_argument("--alpha-step", type=float, default=0.25)
    args = parser.parse_args()

    print("# k=4 component/cycle-count frontier")
    print("# component benchmark closes alpha <= 66/17")
    print("# cycle-count benchmark closes alpha >= 14/3")
    print("alpha,component_beta,threshold,margin")
    worst = None
    for alpha in frange(args.alpha_min, args.alpha_max, args.alpha_step):
        beta = k4_component_beta(alpha)
        target = threshold(4, alpha)
        margin = beta - target
        row = (margin, alpha, beta, target)
        if worst is None or row > worst:
            worst = row
        print(f"{alpha:.12g},{beta:.12g},{target:.12g},{margin:.12g}")

    assert worst is not None
    margin, alpha, beta, target = worst
    print()
    print("# Worst sampled component margin")
    print("alpha,component_beta,threshold,margin")
    print(f"{alpha:.12g},{beta:.12g},{target:.12g},{margin:.12g}")
    print()
    print("closed_low_alpha=66/17")
    print("closed_high_alpha=14/3")
    print("remaining_window=(66/17,14/3)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
