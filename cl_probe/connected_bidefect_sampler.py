#!/usr/bin/env python3
"""Monte Carlo connected bidefect profile for unbounded-component diagnostics.

This is not an exact count and not a proof of CL.  It samples uniform
permutations on `k*t` symbols, keeps those connected for `<gamma, pi>`, and
estimates the connected bidefect count by

    count_est(plus,minus) = (kt)! * hits(plus,minus) / samples.

For each sampled bidefect row it reports the finite local CL margin

    log(count_est)/(t log t) - k/(k+1) * (1 + alpha_exact/2),

where `alpha_exact = (plus + minus)/t`.  It also reports the asymptotic
leading alpha

    alpha_leading = 4 + 2*(g_plus + g_minus)/t,

which removes the finite connected-component correction `-4/t`.  This is the
right coordinate for comparing sampled rows to the unbounded-component
frontier isolated in `bidefect_local_threshold.py`.
"""

from __future__ import annotations

import argparse
import math
from collections import Counter

import numpy as np


def gamma_perm(k: int, t: int) -> tuple[int, ...]:
    return tuple(block * k + ((j + 1) % k) for block in range(t) for j in range(k))


def inverse_perm(p: tuple[int, ...]) -> tuple[int, ...]:
    out = [0] * len(p)
    for i, value in enumerate(p):
        out[value] = i
    return tuple(out)


def cycle_counts_batch(perms: np.ndarray) -> np.ndarray:
    batch, n = perms.shape
    idx = np.arange(n)
    mn = np.broadcast_to(idx, (batch, n)).copy()
    cur = mn.copy()
    for _ in range(n):
        cur = np.take_along_axis(perms, cur, axis=1)
        np.minimum(mn, cur, out=mn)
    return (mn == idx).sum(axis=1)


class DSU:
    def __init__(self, n: int):
        self.parent = list(range(n))

    def find(self, x: int) -> int:
        while self.parent[x] != x:
            self.parent[x] = self.parent[self.parent[x]]
            x = self.parent[x]
        return x

    def unite(self, a: int, b: int) -> None:
        a = self.find(a)
        b = self.find(b)
        if a != b:
            self.parent[a] = b


def connected_for_gamma(pi: list[int], gamma: tuple[int, ...]) -> bool:
    dsu = DSU(len(pi))
    for i in range(len(pi)):
        dsu.unite(i, pi[i])
        dsu.unite(i, gamma[i])
    root = dsu.find(0)
    return all(dsu.find(i) == root for i in range(1, len(pi)))


def threshold(k: int, alpha: float) -> float:
    return (k / (k + 1)) * (1 + alpha / 2)


def cycle_crossing_alpha(k: int) -> float | None:
    if k < 4:
        return None
    return (2 * k * k - 4 * k - 2) / (k - 1)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--k", type=int, default=6)
    parser.add_argument("--t", type=int, required=True)
    parser.add_argument("--samples", type=int, default=100000)
    parser.add_argument("--chunk", type=int, default=20000)
    parser.add_argument("--seed", type=int, default=1729)
    parser.add_argument("--min-hits", type=int, default=20)
    parser.add_argument("--top", type=int, default=12)
    args = parser.parse_args()

    if args.k < 2:
        raise SystemExit("k must be at least 2")
    if args.t < 2:
        raise SystemExit("t must be at least 2")
    if args.samples <= 0 or args.chunk <= 0:
        raise SystemExit("samples and chunk must be positive")

    n = args.k * args.t
    gamma = gamma_perm(args.k, args.t)
    gamma_inv = inverse_perm(gamma)
    gamma_arr = np.asarray(gamma, dtype=np.int64)
    gamma_inv_arr = np.asarray(gamma_inv, dtype=np.int64)
    rng = np.random.default_rng(args.seed)
    counts: Counter[tuple[int, int, int, int]] = Counter()
    connected_hits = 0
    seen = 0

    while seen < args.samples:
        batch = min(args.chunk, args.samples - seen)
        perms = np.argsort(rng.random((batch, n)), axis=1).astype(np.int64)
        c_pi = cycle_counts_batch(perms)
        c_gamma_pi = cycle_counts_batch(gamma_arr[perms])
        c_pi_gamma_inv = cycle_counts_batch(perms[:, gamma_inv_arr])

        for idx in range(batch):
            pi = perms[idx].tolist()
            if not connected_for_gamma(pi, gamma):
                continue
            connected_hits += 1
            plus = n + args.t - int(c_pi[idx]) - int(c_gamma_pi[idx])
            minus = n + args.t - int(c_pi[idx]) - int(c_pi_gamma_inv[idx])
            if plus < 2 * (args.t - 1) or minus < 2 * (args.t - 1):
                raise ValueError((plus, minus, "below connected minimum"))
            if plus % 2 or minus % 2:
                raise ValueError((plus, minus, "bad parity"))
            g_plus = (plus - 2 * (args.t - 1)) // 2
            g_minus = (minus - 2 * (args.t - 1)) // 2
            counts[(plus, minus, g_plus, g_minus)] += 1
        seen += batch

    log_factorial = math.lgamma(n + 1)
    crossing = cycle_crossing_alpha(args.k)
    print("# Monte Carlo connected bidefect profile")
    print("# finite-sample diagnostic only; not a proof of CL")
    print(
        f"k={args.k},t={args.t},n={n},samples={seen},"
        f"connected_hits={connected_hits},seed={args.seed}"
    )
    if crossing is None:
        print("# cycle_crossing_alpha=none")
    else:
        print(
            "# cycle_crossing_alpha="
            f"{crossing:.12g}; asymptotic pre-cycle rows have "
            "alpha_leading <= this value"
        )
    print(
        "plus_defect,minus_defect,g_plus,g_minus,hits,frequency,"
        "log_count_est,rel_se,alpha_exact,alpha_leading,beta_est,"
        "threshold_exact,margin_exact,threshold_leading,margin_leading"
    )

    rows = []
    supported = []
    pre_cycle_supported = []
    for (plus, minus, g_plus, g_minus), hits in sorted(counts.items()):
        freq = hits / seen
        log_count = log_factorial + math.log(freq)
        rel_se = 1 / math.sqrt(hits)
        alpha_exact = (plus + minus) / args.t
        alpha_leading = 4 + 2 * (g_plus + g_minus) / args.t
        beta = log_count / (args.t * math.log(args.t))
        target_exact = threshold(args.k, alpha_exact)
        target_leading = threshold(args.k, alpha_leading)
        margin_exact = beta - target_exact
        margin_leading = beta - target_leading
        row = (
            margin_leading,
            hits,
            plus,
            minus,
            g_plus,
            g_minus,
            alpha_exact,
            alpha_leading,
            beta,
            target_exact,
            margin_exact,
            target_leading,
        )
        rows.append(row)
        if hits >= args.min_hits:
            supported.append(row)
            if crossing is not None and alpha_leading <= crossing + 1e-12:
                pre_cycle_supported.append(row)
        print(
            f"{plus},{minus},{g_plus},{g_minus},{hits},{freq:.9g},"
            f"{log_count:.9g},{rel_se:.9g},{alpha_exact:.9g},"
            f"{alpha_leading:.9g},{beta:.9g},{target_exact:.9g},"
            f"{margin_exact:.9g},{target_leading:.9g},{margin_leading:.9g}"
        )

    print()
    print("# Largest rows by hits")
    print(
        "rank,plus_defect,minus_defect,g_plus,g_minus,hits,"
        "alpha_exact,alpha_leading,margin_leading"
    )
    largest = sorted(rows, key=lambda item: item[1], reverse=True)[: args.top]
    for rank, row in enumerate(largest, start=1):
        (
            margin,
            hits,
            plus,
            minus,
            g_plus,
            g_minus,
            alpha_exact,
            alpha_leading,
            _beta,
            _target_exact,
            _margin_exact,
            _target_leading,
        ) = row
        print(
            f"{rank},{plus},{minus},{g_plus},{g_minus},{hits},"
            f"{alpha_exact:.9g},{alpha_leading:.9g},{margin:.9g}"
        )

    if supported:
        print()
        print("# Largest supported leading local margin")
        print(
            "plus_defect,minus_defect,g_plus,g_minus,hits,"
            "alpha_exact,alpha_leading,margin_leading"
        )
        (
            margin,
            hits,
            plus,
            minus,
            g_plus,
            g_minus,
            alpha_exact,
            alpha_leading,
            _beta,
            _target_exact,
            _margin_exact,
            _target_leading,
        ) = max(supported)
        print(
            f"{plus},{minus},{g_plus},{g_minus},{hits},"
            f"{alpha_exact:.9g},{alpha_leading:.9g},{margin:.9g}"
        )

    if pre_cycle_supported:
        print()
        print("# Largest supported asymptotic pre-cycle local margin")
        print(
            "plus_defect,minus_defect,g_plus,g_minus,hits,"
            "alpha_exact,alpha_leading,margin_leading"
        )
        (
            margin,
            hits,
            plus,
            minus,
            g_plus,
            g_minus,
            alpha_exact,
            alpha_leading,
            _beta,
            _target_exact,
            _margin_exact,
            _target_leading,
        ) = max(pre_cycle_supported)
        print(
            f"{plus},{minus},{g_plus},{g_minus},{hits},"
            f"{alpha_exact:.9g},{alpha_leading:.9g},{margin:.9g}"
        )
    elif crossing is not None:
        print()
        print("# Largest supported asymptotic pre-cycle local margin")
        print("none")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
