#!/usr/bin/env python3
"""Finite sanity checks for the active Aubrun/Biane branch implications.

This is not proof evidence.  It enumerates small left-tight permutations and
looks for counterexamples to the finite branch implications currently exposed
by the U-AUB-02 endpoint.  Use it before spending Lean time on a proposed local
branch closure.

As of U-AUB-322, the checked finite gap-three branch list is empty on the
current sharp endpoint.  The remaining Biane leaves are broad large-gap
inputs.  This script therefore also profiles the live large-gap crossing
obligations and the nested predecessor-skip residual frontier in small
left-tight models.  A clean profile is only a conjecture finder; it is not a
Lean proof.
"""

from __future__ import annotations

import argparse
from collections.abc import Callable
from collections import Counter
from itertools import permutations
from typing import NamedTuple


Perm = tuple[int, ...]
BranchPred = Callable[[Perm, list[int], list[int], int, int, int, int], bool]
TargetPred = Callable[[Perm, list[int], list[int], int, int, int, int], bool]


class Branch(NamedTuple):
    name: str
    shape: str
    branch: BranchPred
    target: TargetPred


def compose(sigma: Perm, tau: Perm) -> Perm:
    return tuple(sigma[tau[i]] for i in range(len(sigma)))


def cycle_classes(perm: Perm) -> tuple[list[list[int]], list[int]]:
    n = len(perm)
    seen = [False] * n
    cls = [-1] * n
    cycles: list[list[int]] = []
    for start in range(n):
        if seen[start]:
            continue
        cur: list[int] = []
        x = start
        while not seen[x]:
            seen[x] = True
            cls[x] = len(cycles)
            cur.append(x)
            x = perm[x]
        cycles.append(cur)
    return cycles, cls


def same(cls: list[int], x: int, y: int) -> bool:
    return cls[x] == cls[y]


def gamma_value(n: int, x: int) -> int:
    return (x + 1) % n


def left_tight_perms(n: int):
    gamma = tuple((i + 1) % n for i in range(n))
    for perm in permutations(range(n)):
        t_cycles, t_cls = cycle_classes(perm)
        s_cycles, s_cls = cycle_classes(compose(gamma, perm))
        if len(t_cycles) + len(s_cycles) == n + 1:
            yield perm, s_cls, t_cls


def crossing_hypotheses(t_cls: list[int], a: int, b: int, c: int, d: int) -> bool:
    return same(t_cls, a, c) and same(t_cls, b, d) and not same(t_cls, a, b)


def common_pair_exists(s_cls: list[int], t_cls: list[int]) -> bool:
    n = len(s_cls)
    for y in range(n):
        for z in range(y + 1, n):
            if same(t_cls, y, z) and same(s_cls, y, z):
                return True
    return False


def noncrossing_partition(cls: list[int]) -> bool:
    n = len(cls)
    for a in range(n):
        for b in range(a + 1, n):
            for c in range(b + 1, n):
                for d in range(c + 1, n):
                    if same(cls, a, c) and same(cls, b, d) and not same(cls, a, b):
                        return False
    return True


def predecessor_skip_case(perm: Perm, t_cls: list[int], x: int) -> str | None:
    px = perm[x]
    if px < x:
        if any(same(t_cls, z, x) and px < z < x for z in range(len(perm))):
            return "nonwrap"
        return None
    if any(same(t_cls, z, x) and z < x for z in range(len(perm))):
        return "wrap_below"
    if any(same(t_cls, z, x) and px < z for z in range(len(perm))):
        return "wrap_above"
    return None


def direct_hit(perm: Perm, t_cls: list[int], x: int) -> bool:
    return same(t_cls, x, gamma_value(len(perm), perm[x]))


def nested_return_interval(
    perm: Perm, t_cls: list[int], x: int, skip_case: str
) -> tuple[str, int, int] | None:
    """Mirror the three branch-normalized return intervals used in Lean."""

    px = perm[x]
    if skip_case == "nonwrap":
        candidates = [
            z for z in range(len(perm)) if same(t_cls, z, x) and px < z < x
        ]
        if not candidates:
            return None
        return ("A_nonwrap_first", px, min(candidates))
    if skip_case == "wrap_below":
        candidates = [z for z in range(len(perm)) if same(t_cls, z, x) and z < x]
        if not candidates:
            return None
        return ("B_wrap_below_last", max(candidates), px)
    if skip_case == "wrap_above":
        candidates = [z for z in range(len(perm)) if same(t_cls, z, x) and px < z]
        if not candidates:
            return None
        return ("C_wrap_above_first", x, min(candidates))
    raise ValueError(f"unknown skip case: {skip_case}")


def primitive_residual_branches(
    perm: Perm, s_cls: list[int], t_cls: list[int], a: int, c: int
) -> set[str]:
    """Evaluate the current primitive residual frontier on a concrete interval."""

    out: set[str] = set()
    gap = c - a
    for r in range(gap + 1):
        for s in range(gap + 1):
            if 0 < r and s < gap and r < s and same(s_cls, a + r, a + s):
                out.add("R1_internal_S")
    for s in range(gap + 1):
        if 1 < s and s < gap and same(s_cls, a, a + s):
            out.add("R2_start_S")
    for r in range(gap + 1):
        if 0 < r and r + 1 < gap and same(s_cls, a + r, c):
            out.add("R3_end_S")
    if gap > 0 and perm[c - 1] == c - 1:
        out.add("R4_fixed_pred")
    for r in range(gap):
        if r + 1 < gap and same(t_cls, a + r, a + r + 1):
            out.add("R5_adjacent_T")
    return out


def strict_smaller_child_branches(
    perm: Perm, s_cls: list[int], t_cls: list[int], a: int, c: int
) -> set[str]:
    """Evaluate the five strict smaller-contour child branches.

    This mirrors the theorem-facing nonwrapping child leaves exposed by
    U-AUB-355, with `a,c` now the child interval endpoints.
    """

    out: set[str] = set()
    gap = c - a
    for r in range(gap + 1):
        for s in range(gap + 1):
            if 0 < r and s < gap and r < s and same(s_cls, a + r, a + s):
                out.add("C1_internal_S")
    for s in range(gap + 1):
        if 1 < s and s < gap and same(s_cls, a, a + s):
            out.add("C2_start_S")
    for r in range(gap + 1):
        if 0 < r and r + 1 < gap and same(s_cls, a + r, c):
            out.add("C3_end_S")
    if gap > 0 and perm[c - 1] == c - 1:
        out.add("C4_fixed_pred")
    for r in range(gap):
        for s in range(gap):
            if r < s and same(t_cls, a + r, a + s):
                out.add("C5_internal_T")
    return out


def no_x_cycle_between(t_cls: list[int], x: int, a: int, c: int) -> bool:
    return not any(same(t_cls, z, x) and a < z < c for z in range(len(t_cls)))


def block_off_x(t_cls: list[int], x: int, parent_a: int, parent_c: int, child_a: int) -> bool:
    """Concrete version of the child block invariant in the strict branch leaves."""

    return all(
        parent_a < y < parent_c and not same(t_cls, y, x)
        for y in range(len(t_cls))
        if same(t_cls, y, child_a)
    )


def run_strict_nonwrap_smaller_child_profile(max_n: int, stop_first: bool) -> int:
    """Stress-test the exact U-AUB-355 nonwrapping child branch shape.

    This is conjecture-finding only.  It enumerates the theorem-facing
    hypotheses for the five strict smaller contour-repeat branch leaves and
    checks whether a global common pi/(gamma*pi) pair is already present.
    """

    total_left_tight = 0
    total_noncrossing = 0
    total_nonwrap_parents = 0
    total_child_intervals = 0
    branch_counts: Counter[str] = Counter()
    branch_by_n: Counter[tuple[int, str]] = Counter()
    failures = []

    for n in range(2, max_n + 1):
        for perm, s_cls, t_cls in left_tight_perms(n):
            total_left_tight += 1
            if not noncrossing_partition(t_cls):
                continue
            total_noncrossing += 1
            has_common = common_pair_exists(s_cls, t_cls)
            for x in range(n):
                if perm[x] == x:
                    continue
                skip_case = predecessor_skip_case(perm, t_cls, x)
                if skip_case != "nonwrap":
                    continue
                if direct_hit(perm, t_cls, x):
                    continue
                interval = nested_return_interval(perm, t_cls, x, skip_case)
                if interval is None:
                    continue
                side, a, c = interval
                if side != "A_nonwrap_first":
                    continue
                if not (0 <= a < c < x < n and 1 < c - a and same(t_cls, a, c)):
                    continue
                if a != perm[x] or not no_x_cycle_between(t_cls, x, a, c):
                    continue
                total_nonwrap_parents += 1

                for child_a in range(a + 1, c):
                    for child_c in range(child_a + 2, c):
                        if not same(t_cls, child_a, child_c):
                            continue
                        if not no_x_cycle_between(t_cls, x, child_a, child_c):
                            continue
                        if not block_off_x(t_cls, x, a, c, child_a):
                            continue
                        total_child_intervals += 1
                        branches = strict_smaller_child_branches(
                            perm, s_cls, t_cls, child_a, child_c
                        )
                        for branch in sorted(branches):
                            branch_counts[branch] += 1
                            branch_by_n[(n, branch)] += 1
                            if has_common:
                                continue
                            s_cycles, _ = cycle_classes(
                                compose(tuple((i + 1) % n for i in range(n)), perm)
                            )
                            t_cycles, _ = cycle_classes(perm)
                            failures.append(
                                (
                                    n,
                                    perm,
                                    x,
                                    (a, c),
                                    (child_a, child_c),
                                    branch,
                                    s_cycles,
                                    t_cycles,
                                )
                            )
                            if stop_first:
                                break
                        if failures and stop_first:
                            break
                    if failures and stop_first:
                        break
                if failures and stop_first:
                    break
            if failures and stop_first:
                break
        if failures and stop_first:
            break

    print("strict nonwrapping smaller-contour child profile")
    print(f"  checked n <= {max_n}")
    print(f"  left-tight permutations: {total_left_tight}")
    print(f"  noncrossing left-tight permutations: {total_noncrossing}")
    print(f"  nonwrapping parent first-return intervals: {total_nonwrap_parents}")
    print(f"  strict child intervals satisfying side data: {total_child_intervals}")
    if branch_counts:
        print("  strict child branches reached:")
        for branch, count in sorted(branch_counts.items()):
            print(f"    {branch}: {count}")
        print("  strict child branches by n:")
        for (n, branch), count in sorted(branch_by_n.items()):
            print(f"    n={n} / {branch}: {count}")
    else:
        print("  strict child branches reached: none")
    if failures:
        print("  strict child branch counterexamples:")
        for n, perm, x, parent, child, branch, s_cycles, t_cycles in failures[:5]:
            print(
                f"    n={n} perm={perm} x={x} parent={parent} "
                f"child={child} branch={branch}"
            )
            print(f"      S cycles={s_cycles}")
            print(f"      T cycles={t_cycles}")
        return 1
    print("  strict child branch counterexamples: none")
    return 0


def wrap_position_refined_branches(
    perm: Perm, t_cls: list[int], x: int, side: str, a: int, c: int
) -> set[str]:
    """Evaluate the four position-refined wrap internal-subinterval leaves."""

    out: set[str] = set()
    gap = c - a
    if side == "B_wrap_below_last":
        for s in range(gap):
            if 1 < s and same(t_cls, a, a + s) and x <= a + s:
                out.add("below_start_after_skipped")
        for r in range(gap):
            for s in range(gap):
                if (
                    0 < r
                    and r < s
                    and 1 < s - r
                    and same(t_cls, a + r, a + s)
                    and same(t_cls, a + r, x)
                    and x <= a + r
                ):
                    out.add("below_open_on_cycle_after_skipped")
    elif side == "C_wrap_above_first":
        px = perm[x]
        for s in range(gap):
            if 1 < s and same(t_cls, a, a + s) and a + s <= px:
                out.add("above_start_before_image")
        for r in range(gap):
            for s in range(gap):
                if (
                    0 < r
                    and r < s
                    and 1 < s - r
                    and same(t_cls, a + r, a + s)
                    and same(t_cls, a + r, x)
                    and a + r <= px
                ):
                    out.add("above_open_on_cycle_before_image")
    return out


def run_wrap_position_refined_profile(max_n: int, stop_first: bool) -> int:
    """Stress-test the four remaining wrap internal-subinterval leaves.

    This mirrors the theorem-facing hypotheses after U-AUB-368.  A clean run is
    only conjecture-finding evidence, not proof evidence.
    """

    total_left_tight = 0
    total_noncrossing = 0
    total_nested_wrap = 0
    branch_counts: Counter[str] = Counter()
    branch_by_n: Counter[tuple[int, str]] = Counter()
    failures = []

    for n in range(2, max_n + 1):
        for perm, s_cls, t_cls in left_tight_perms(n):
            total_left_tight += 1
            if not noncrossing_partition(t_cls):
                continue
            total_noncrossing += 1
            has_common = common_pair_exists(s_cls, t_cls)
            for x in range(n):
                if perm[x] == x:
                    continue
                skip_case = predecessor_skip_case(perm, t_cls, x)
                if skip_case not in {"wrap_below", "wrap_above"}:
                    continue
                if direct_hit(perm, t_cls, x):
                    continue
                interval = nested_return_interval(perm, t_cls, x, skip_case)
                if interval is None:
                    continue
                side, a, c = interval
                if not (0 <= a < c < n and 1 < c - a and same(t_cls, a, c)):
                    continue
                total_nested_wrap += 1
                branches = wrap_position_refined_branches(perm, t_cls, x, side, a, c)
                for branch in sorted(branches):
                    branch_counts[branch] += 1
                    branch_by_n[(n, branch)] += 1
                    if has_common:
                        continue
                    s_cycles, _ = cycle_classes(
                        compose(tuple((i + 1) % n for i in range(n)), perm)
                    )
                    t_cycles, _ = cycle_classes(perm)
                    failures.append((n, perm, x, side, (a, c), branch, s_cycles, t_cycles))
                    if stop_first:
                        break
                if failures and stop_first:
                    break
            if failures and stop_first:
                break
        if failures and stop_first:
            break

    print("wrap position-refined residual profile")
    print(f"  checked n <= {max_n}")
    print(f"  left-tight permutations: {total_left_tight}")
    print(f"  noncrossing left-tight permutations: {total_noncrossing}")
    print(f"  nested non-direct wrap intervals: {total_nested_wrap}")
    if branch_counts:
        print("  position-refined branches reached:")
        for branch, count in sorted(branch_counts.items()):
            print(f"    {branch}: {count}")
        print("  branches by n:")
        for (n, branch), count in sorted(branch_by_n.items()):
            print(f"    n={n} / {branch}: {count}")
    else:
        print("  position-refined branches reached: none")
    if failures:
        print("  position-refined wrap counterexamples:")
        for n, perm, x, side, interval, branch, s_cycles, t_cycles in failures[:5]:
            print(
                f"    n={n} perm={perm} x={x} side={side} "
                f"interval={interval} branch={branch}"
            )
            print(f"      S cycles={s_cycles}")
            print(f"      T cycles={t_cycles}")
        return 1
    print("  position-refined wrap counterexamples: none")
    return 0


def run_nested_residual_profile(max_n: int, stop_first: bool) -> int:
    """Profile the current nested predecessor-skip residual leaf in small models."""

    total_left_tight = 0
    total_nonfixed_skips = 0
    total_nested = 0
    side_counts: Counter[str] = Counter()
    branch_counts: Counter[str] = Counter()
    branch_by_side: Counter[tuple[str, str]] = Counter()
    common_pair_hits = 0
    malformed = []

    for n in range(2, max_n + 1):
        for perm, s_cls, t_cls in left_tight_perms(n):
            total_left_tight += 1
            has_common = common_pair_exists(s_cls, t_cls)
            for x in range(n):
                if perm[x] == x:
                    continue
                skip_case = predecessor_skip_case(perm, t_cls, x)
                if skip_case is None:
                    continue
                total_nonfixed_skips += 1
                if direct_hit(perm, t_cls, x):
                    continue
                total_nested += 1
                interval = nested_return_interval(perm, t_cls, x, skip_case)
                if interval is None:
                    malformed.append((n, perm, x, skip_case, "no interval"))
                    if stop_first:
                        break
                    continue
                side, a, c = interval
                if not (0 <= a < c < n and 1 < c - a and same(t_cls, a, c)):
                    malformed.append((n, perm, x, skip_case, interval))
                    if stop_first:
                        break
                    continue
                side_counts[side] += 1
                branches = primitive_residual_branches(perm, s_cls, t_cls, a, c)
                for branch in sorted(branches):
                    branch_counts[branch] += 1
                    branch_by_side[(side, branch)] += 1
                if has_common:
                    common_pair_hits += 1
            if malformed and stop_first:
                break
        if malformed and stop_first:
            break

    print("nested predecessor-skip residual profile")
    print(f"  checked n <= {max_n}")
    print(f"  left-tight permutations: {total_left_tight}")
    print(f"  nonfixed predecessor skips: {total_nonfixed_skips}")
    print(f"  nested non-direct skips: {total_nested}")
    print(f"  nested skips with common T/S pair: {common_pair_hits}")
    if side_counts:
        print("  side counts:")
        for side, count in sorted(side_counts.items()):
            print(f"    {side}: {count}")
    else:
        print("  side counts: none")
    if branch_counts:
        print("  primitive residual branches reached:")
        for branch, count in sorted(branch_counts.items()):
            print(f"    {branch}: {count}")
        print("  branches by side:")
        for (side, branch), count in sorted(branch_by_side.items()):
            print(f"    {side} / {branch}: {count}")
    else:
        print("  primitive residual branches reached: none")
    if malformed:
        print("  malformed interval extractions:")
        for item in malformed[:3]:
            print(f"    {item}")
        return 1
    return 0


def run_loose_primitive_counterexample_profile(max_n: int, stop_first: bool) -> int:
    """Test the over-broad primitive residual leaf without nested side data.

    The current endpoint exposes a hypothesis saying that any noncrossing
    left-tight permutation, any longer same-pi interval, and any primitive
    residual branch imply a nontrivial common pi/(gamma*pi) pair.  That statement is
    intentionally broader than the nested return-interval leaf produced by the
    predecessor-skip pipeline.  This diagnostic enumerates exactly that loose
    statement in small finite models.

    Finding examples here does not refute the side-tied nested route.  It only
    shows that the theorem-facing loose primitive hypothesis is not the right
    mathematical leaf to prove.
    """

    total_left_tight = 0
    total_noncrossing = 0
    primitive_intervals = 0
    no_common = []
    branch_counts: Counter[str] = Counter()
    by_n: Counter[int] = Counter()

    for n in range(2, max_n + 1):
        for perm, s_cls, t_cls in left_tight_perms(n):
            total_left_tight += 1
            if not noncrossing_partition(t_cls):
                continue
            total_noncrossing += 1
            has_common = common_pair_exists(s_cls, t_cls)
            for a in range(n):
                for c in range(a + 2, n):
                    if not same(t_cls, a, c):
                        continue
                    branches = primitive_residual_branches(perm, s_cls, t_cls, a, c)
                    if not branches:
                        continue
                    primitive_intervals += 1
                    by_n[n] += 1
                    for branch in sorted(branches):
                        branch_counts[branch] += 1
                    if not has_common:
                        s_cycles, _ = cycle_classes(compose(tuple((i + 1) % n for i in range(n)), perm))
                        t_cycles, _ = cycle_classes(perm)
                        no_common.append((n, perm, a, c, sorted(branches), s_cycles, t_cycles))
                        if stop_first:
                            break
                if no_common and stop_first:
                    break
            if no_common and stop_first:
                break
        if no_common and stop_first:
            break

    print("loose primitive-residual counterdiagnostic")
    print(f"  checked n <= {max_n}")
    print(f"  left-tight permutations: {total_left_tight}")
    print(f"  noncrossing left-tight permutations: {total_noncrossing}")
    print(f"  primitive same-pi intervals: {primitive_intervals}")
    if by_n:
        print("  primitive intervals by n:")
        for n, count in sorted(by_n.items()):
            print(f"    n={n}: {count}")
    else:
        print("  primitive intervals by n: none")
    if branch_counts:
        print("  primitive branch counts:")
        for branch, count in sorted(branch_counts.items()):
            print(f"    {branch}: {count}")
    else:
        print("  primitive branch counts: none")
    if no_common:
        print("  loose primitive intervals with no common T/S pair:")
        for n, perm, a, c, branches, s_cycles, t_cycles in no_common[:5]:
            print(f"    n={n} perm={perm} interval=({a},{c}) branches={branches}")
            print(f"      S cycles={s_cycles}")
            print(f"      T cycles={t_cycles}")
    else:
        print("  loose primitive intervals with no common T/S pair: none")
    return 0


BRANCHES: list[Branch] = []


def shape_ranges(n: int, shape: str):
    if shape == "c-a=3, b=a+1":
        for a in range(n):
            b = a + 1
            c = a + 3
            if c >= n:
                continue
            for d in range(c + 1, n):
                yield a, b, c, d
    elif shape == "c-a=3, b=a+2":
        for a in range(n):
            b = a + 2
            c = a + 3
            if c >= n:
                continue
            for d in range(c + 1, n):
                yield a, b, c, d
    elif shape == "d-b=3, c=b+2":
        for b in range(n):
            c = b + 2
            d = b + 3
            if d >= n:
                continue
            for a in range(0, b):
                yield a, b, c, d
    else:
        raise ValueError(f"unknown branch shape: {shape}")


def run(max_n: int, stop_first: bool) -> int:
    if not BRANCHES:
        print("no active finite gap-three branches")
        large_gap_exit = run_live_large_gap_profile(max_n, stop_first)
        print()
        nested_exit = run_nested_residual_profile(max_n, stop_first)
        print()
        strict_child_exit = run_strict_nonwrap_smaller_child_profile(max_n, stop_first)
        return large_gap_exit or nested_exit or strict_child_exit
    exit_code = 0
    for branch in BRANCHES:
        hits = 0
        failures = []
        for n in range(2, max_n + 1):
            for perm, s_cls, t_cls in left_tight_perms(n):
                for a, b, c, d in shape_ranges(n, branch.shape):
                    if not crossing_hypotheses(t_cls, a, b, c, d):
                        continue
                    if not branch.branch(perm, s_cls, t_cls, a, b, c, d):
                        continue
                    hits += 1
                    if not branch.target(perm, s_cls, t_cls, a, b, c, d):
                        s_cycles, _ = cycle_classes(compose(tuple((i + 1) % n for i in range(n)), perm))
                        t_cycles, _ = cycle_classes(perm)
                        failures.append((n, perm, (a, b, c, d), s_cycles, t_cycles))
                        exit_code = 1
                        if stop_first:
                            break
                if failures and stop_first:
                    break
            if failures and stop_first:
                break
        status = "ok" if not failures else "counterexample"
        print(f"{branch.name:22s} {status:14s} hits={hits}")
        for n, perm, abcd, s_cycles, t_cycles in failures[:3]:
            print(f"  n={n} perm={perm} a,b,c,d={abcd}")
            print(f"  S cycles={s_cycles}")
            print(f"  T cycles={t_cycles}")
    return exit_code


def run_live_large_gap_profile(max_n: int, stop_first: bool) -> int:
    """Probe the broad large-gap leaves currently visible on U-AUB-02.

    The active endpoint asks for:
    * the left link S(a,b) when 2 < c-a and c-a != 3;
    * the right link S(c,d) when 2 < d-b outside the checked
      d-b=3, c=b+2 slice.

    We enumerate small left-tight permutations and check these implications
    wherever the crossing hypotheses occur.  In the currently tested range the
    stronger phenomenon is that no crossing hypotheses occur at all.
    """

    exit_code = 0
    total_left_tight = 0
    total_crossings = 0
    left_large_hits = 0
    right_large_hits = 0
    left_failures = []
    right_failures = []
    gap_pair_counts: dict[tuple[int, int], int] = {}

    for n in range(2, max_n + 1):
        for perm, s_cls, t_cls in left_tight_perms(n):
            total_left_tight += 1
            for a in range(n):
                for b in range(a + 1, n):
                    for c in range(b + 1, n):
                        for d in range(c + 1, n):
                            if not crossing_hypotheses(t_cls, a, b, c, d):
                                continue
                            total_crossings += 1
                            gap_pair = (c - a, d - b)
                            gap_pair_counts[gap_pair] = (
                                gap_pair_counts.get(gap_pair, 0) + 1
                            )

                            if 2 < c - a and c - a != 3:
                                left_large_hits += 1
                                if not same(s_cls, a, b):
                                    left_failures.append((n, perm, (a, b, c, d)))
                                    exit_code = 1
                                    if stop_first:
                                        break

                            if 2 < d - b and not (d - b == 3 and c == b + 2):
                                right_large_hits += 1
                                if not same(s_cls, c, d):
                                    right_failures.append((n, perm, (a, b, c, d)))
                                    exit_code = 1
                                    if stop_first:
                                        break
                        if (left_failures or right_failures) and stop_first:
                            break
                    if (left_failures or right_failures) and stop_first:
                        break
                if (left_failures or right_failures) and stop_first:
                    break
            if (left_failures or right_failures) and stop_first:
                break
        if (left_failures or right_failures) and stop_first:
            break

    print("live large-gap profile")
    print(f"  checked n <= {max_n}")
    print(f"  left-tight permutations: {total_left_tight}")
    print(f"  crossing hypotheses: {total_crossings}")
    print(f"  active left large-gap hits: {left_large_hits}")
    print(f"  active right large-gap hits: {right_large_hits}")
    if gap_pair_counts:
        print("  crossing gap pairs:")
        for (left_gap, right_gap), count in sorted(gap_pair_counts.items()):
            print(f"    c-a={left_gap}, d-b={right_gap}: {count}")
    else:
        print("  crossing gap pairs: none")

    if left_failures:
        print("  left large-gap counterexamples:")
        for item in left_failures[:3]:
            print(f"    n={item[0]} perm={item[1]} a,b,c,d={item[2]}")
    if right_failures:
        print("  right large-gap counterexamples:")
        for item in right_failures[:3]:
            print(f"    n={item[0]} perm={item[1]} a,b,c,d={item[2]}")

    return exit_code


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-n", type=int, default=8)
    parser.add_argument("--all", action="store_true", help="collect more than the first counterexample")
    parser.add_argument(
        "--loose-primitive",
        action="store_true",
        help="also profile the over-broad primitive residual leaf without nested side data",
    )
    parser.add_argument(
        "--wrap-position",
        action="store_true",
        help="profile the four position-refined wrap internal-subinterval leaves",
    )
    args = parser.parse_args()
    exit_code = run(args.max_n, stop_first=not args.all)
    if args.wrap_position:
        print()
        exit_code = (
            run_wrap_position_refined_profile(args.max_n, stop_first=not args.all)
            or exit_code
        )
    if args.loose_primitive:
        print()
        exit_code = (
            run_loose_primitive_counterexample_profile(
                args.max_n, stop_first=not args.all
            )
            or exit_code
        )
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
