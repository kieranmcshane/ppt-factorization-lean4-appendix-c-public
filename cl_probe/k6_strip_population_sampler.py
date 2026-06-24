#!/usr/bin/env python3
"""Monte Carlo population estimates for the k=6 balanced remaining strip.

This is finite-sample evidence, not an asymptotic estimate.  It samples
uniform permutations on `6*t` symbols and estimates counts for balanced
remaining-strip rows `(g_+,g_-)=(g,g)`.

For each balanced strip row it reports

    beta_est = log((6t)! * hits / samples) / (t log t),

and compares it to the local CL threshold

    T_6(4+4g/t) = (6/7)(3+2g/t).
"""

from __future__ import annotations

import argparse
import math
from collections import Counter

import numpy as np

from k6_remaining_arithmetic import balanced_rows


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


def threshold_k6(y: float) -> float:
    return (6 / 7) * (3 + 2 * y)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--t", type=int, required=True)
    parser.add_argument("--samples", type=int, default=100000)
    parser.add_argument("--chunk", type=int, default=5000)
    parser.add_argument("--seed", type=int, default=20260617)
    parser.add_argument("--show-all", action="store_true")
    args = parser.parse_args()

    if args.t < 2:
        raise SystemExit("t must be at least 2")
    if args.samples <= 0 or args.chunk <= 0:
        raise SystemExit("samples and chunk must be positive")

    k = 6
    n = k * args.t
    targets = set(balanced_rows(args.t))
    gamma = gamma_perm(k, args.t)
    gamma_inv = inverse_perm(gamma)
    gamma_arr = np.asarray(gamma, dtype=np.int64)
    gamma_inv_arr = np.asarray(gamma_inv, dtype=np.int64)
    rng = np.random.default_rng(args.seed)
    counts: Counter[int] = Counter()
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
            if plus % 2 or minus % 2:
                raise ValueError((plus, minus, "bad parity"))
            g_plus = (plus - 2 * (args.t - 1)) // 2
            g_minus = (minus - 2 * (args.t - 1)) // 2
            if g_plus == g_minus and g_plus in targets:
                counts[g_plus] += 1
        seen += batch

    log_factorial = math.lgamma(n + 1)
    print("# k=6 balanced strip population sampler")
    print("# finite Monte Carlo evidence only; not an asymptotic estimate")
    print(
        f"t={args.t},n={n},samples={seen},connected_hits={connected_hits},"
        f"seed={args.seed},balanced_targets={';'.join(str(g) for g in sorted(targets))}"
    )
    print(
        "t,g,hits,frequency,log_count_est,rel_se,y,alpha_leading,"
        "beta_est,beta_required,margin"
    )

    total_hits = 0
    best_margin = None
    for g in sorted(targets):
        hits = counts[g]
        total_hits += hits
        y = g / args.t
        alpha = 4 + 4 * y
        beta_required = threshold_k6(y)
        if hits:
            freq = hits / seen
            log_count = log_factorial + math.log(freq)
            rel_se = 1 / math.sqrt(hits)
            beta_est = log_count / (args.t * math.log(args.t))
            margin = beta_est - beta_required
            row = (margin, g, hits, beta_est, beta_required)
            if best_margin is None or row > best_margin:
                best_margin = row
            print(
                f"{args.t},{g},{hits},{freq:.12g},{log_count:.12g},"
                f"{rel_se:.12g},{y:.12g},{alpha:.12g},{beta_est:.12g},"
                f"{beta_required:.12g},{margin:.12g}"
            )
        elif args.show_all:
            print(
                f"{args.t},{g},0,0,,,{y:.12g},{alpha:.12g},,"
                f"{beta_required:.12g},"
            )

    print()
    print("# Summary")
    print("t,samples,total_strip_hits,best_g,best_margin,status")
    if best_margin is None:
        print(f"{args.t},{seen},{total_hits},,,no_strip_hits")
    else:
        margin, g, _hits, _beta_est, _beta_required = best_margin
        status = "finite_beta_above_threshold" if margin > 0 else "finite_beta_below_threshold"
        print(f"{args.t},{seen},{total_hits},{g},{margin:.12g},{status}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
