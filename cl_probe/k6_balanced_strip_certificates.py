#!/usr/bin/env python3
"""Generate and verify k=6 balanced-strip witness certificates.

The certificates are finite evidence only.  They store explicit permutation
images for balanced rows in the remaining k=6 strip, so the nonemptiness claim
can be checked deterministically without rerunning the heuristic search.
"""

from __future__ import annotations

import argparse
import csv
import sys
from pathlib import Path

from bidefect_target_local_search import (
    gamma_perm,
    inverse_perm,
    orbit_count,
    row_data,
    search_target,
)
from k6_balanced_strip_target_sweep import row_seed
from k6_remaining_arithmetic import balanced_rows


FIELDNAMES = [
    "t",
    "g",
    "seed",
    "status",
    "c_pi",
    "c_gamma_pi",
    "c_pi_gamma_inv",
    "plus",
    "minus",
    "g_plus",
    "g_minus",
    "components",
    "penalty",
    "restart",
    "step",
    "permutation_image",
]


def encode_perm(pi: list[int]) -> str:
    return " ".join(str(x) for x in pi)


def decode_perm(text: str) -> list[int]:
    text = text.strip()
    if not text:
        raise ValueError("empty permutation image")
    return [int(part) for part in text.split()]


def verify_perm_row(row: dict[str, str]) -> tuple[bool, str]:
    try:
        t = int(row["t"])
        g = int(row["g"])
        status = row["status"]
        pi = decode_perm(row["permutation_image"])
    except (KeyError, ValueError) as exc:
        return False, f"malformed row: {exc}"

    if status != "found":
        return False, f"row t={t},g={g} has non-certificate status {status!r}"
    if g not in balanced_rows(t):
        return False, f"row t={t},g={g} is not in the balanced arithmetic strip"

    n = 6 * t
    if len(pi) != n:
        return False, f"row t={t},g={g} has length {len(pi)}, expected {n}"
    if sorted(pi) != list(range(n)):
        return False, f"row t={t},g={g} is not a permutation of 0..{n - 1}"

    gamma = gamma_perm(6, t)
    gamma_inv = inverse_perm(gamma)
    data = row_data(6, t, pi, gamma, gamma_inv)
    c_pi, c_gamma_pi, c_pi_gamma_inv, plus, minus, g_plus, g_minus = data
    target_defect = 2 * (t - 1) + 2 * g
    components = orbit_count(pi, gamma)

    checks = [
        (c_pi, "c_pi"),
        (c_gamma_pi, "c_gamma_pi"),
        (c_pi_gamma_inv, "c_pi_gamma_inv"),
        (plus, "plus"),
        (minus, "minus"),
        (g_plus, "g_plus"),
        (g_minus, "g_minus"),
    ]
    for actual, name in checks:
        if actual != int(row[name]):
            return False, f"row t={t},g={g} has {name}={row[name]}, computed {actual}"
    if components != int(row["components"]):
        return False, (
            f"row t={t},g={g} has components={row['components']}, "
            f"computed {components}"
        )
    if components != 1:
        return False, f"row t={t},g={g} is not connected: components={components}"
    if plus != target_defect or minus != target_defect:
        return False, (
            f"row t={t},g={g} has defects plus={plus},minus={minus}, "
            f"expected {target_defect}"
        )
    if g_plus != g or g_minus != g:
        return False, f"row t={t},g={g} has genera ({g_plus},{g_minus})"
    return True, "ok"


def verify_file(path: Path) -> int:
    rows = 0
    with path.open(newline="") as handle:
        reader = csv.DictReader(handle)
        for row in reader:
            rows += 1
            ok, message = verify_perm_row(row)
            if not ok:
                print(f"verification failed on row {rows}: {message}", file=sys.stderr)
                return 1
    print(f"verified_rows={rows}")
    return 0


def generate(args: argparse.Namespace) -> int:
    writer = csv.DictWriter(sys.stdout, fieldnames=FIELDNAMES, lineterminator="\n")
    writer.writeheader()
    searched = 0
    misses = 0
    for t in range(args.t_min, args.t_max + 1):
        candidates = balanced_rows(t)
        if args.first_balanced_only and candidates:
            candidates = candidates[:1]
        for row_index, g in enumerate(candidates):
            seed = row_seed(args.seed, t, row_index)
            result = search_target(
                k=6,
                t=t,
                target_g=g,
                restarts=args.restarts,
                steps=args.steps,
                seed=seed,
                connected_weight=args.connected_weight,
                temperature=args.temperature,
            )
            searched += 1
            if not result["found"]:
                misses += 1
            c_pi, c_gamma_pi, c_pi_gamma_inv, plus, minus, g_plus, g_minus, components = (
                result["data"]
            )
            writer.writerow(
                {
                    "t": t,
                    "g": g,
                    "seed": seed,
                    "status": "found" if result["found"] else "miss",
                    "c_pi": c_pi,
                    "c_gamma_pi": c_gamma_pi,
                    "c_pi_gamma_inv": c_pi_gamma_inv,
                    "plus": plus,
                    "minus": minus,
                    "g_plus": g_plus,
                    "g_minus": g_minus,
                    "components": components,
                    "penalty": result["score"],
                    "restart": result["restart"],
                    "step": result["step"],
                    "permutation_image": encode_perm(result["pi"]),
                }
            )
    print(
        f"# searched={searched},found={searched - misses},missed={misses}",
        file=sys.stderr,
    )
    if args.fail_on_miss and misses:
        return 1
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--verify", type=Path)
    parser.add_argument("--t-min", type=int, default=13)
    parser.add_argument("--t-max", type=int, default=20)
    parser.add_argument("--seed", type=int, default=424242)
    parser.add_argument("--restarts", type=int, default=12)
    parser.add_argument("--steps", type=int, default=60000)
    parser.add_argument("--temperature", type=float, default=0.05)
    parser.add_argument("--connected-weight", type=int, default=8)
    parser.add_argument("--first-balanced-only", action="store_true")
    parser.add_argument("--fail-on-miss", action="store_true")
    args = parser.parse_args()

    if args.verify is not None:
        return verify_file(args.verify)
    if args.t_min < 2:
        raise SystemExit("t-min must be at least 2")
    if args.t_max < args.t_min:
        raise SystemExit("t-max must be at least t-min")
    if args.restarts <= 0 or args.steps <= 0:
        raise SystemExit("restarts and steps must be positive")
    return generate(args)


if __name__ == "__main__":
    raise SystemExit(main())
