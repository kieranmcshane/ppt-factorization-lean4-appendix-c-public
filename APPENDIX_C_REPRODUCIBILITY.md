# Appendix C Lean Reproducibility

This branch contains a standalone Lean module for the main Appendix C result:

```text
PptFactorization/AppendixCMainResult.lean
```

The module consolidates the already-proved Lean routes:

- the exact algebraic Appendix C endpoint, proving both `g ∣ f₁ - f₀'` and the first-order coefficient `-1`;
- the canonical tridiagonal/Chebyshev route proving the universal `-1/d1` displacement;
- the self-contained tridiagonal scaling route from `UniversalScalingLawProof`;
- the concrete physical determinant checks for `m = 1, 2, 3`.

## Check

From the repository root, run:

```bash
lake build PptFactorization.AppendixCMainResult
```

The public endpoints audited in this branch are:

```text
AppendixCMainResult.appendixC_main_algebraic_universality
AppendixCMainResult.appendixC_rootwise_coefficient_eq_neg_one
AppendixCMainResult.appendixC_congruence_mod_threshold_polynomial
AppendixCMainResult.appendixC_chebyshev_tridiagonal_spine
AppendixCMainResult.appendixC_hankel_bridge_ratio
AppendixCMainResult.appendixC_canonical_universal_scaling_law
AppendixCMainResult.appendixC_self_contained_tridiagonal_scaling_law
AppendixCMainResult.appendixC_self_contained_tridiagonal_sharpness
AppendixCMainResult.appendixC_physical_scaling_law_m1
AppendixCMainResult.appendixC_physical_scaling_law_m2
AppendixCMainResult.appendixC_physical_scaling_law_m3
```

Local audit result: each endpoint depends only on the standard Lean/mathlib
foundational axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Companion Problem

The file

```text
AppendixC_olympiad_problem.tex
```

is a self-contained problem statement that asks a reader to prove the
deterministic core of the Appendix C universality theorem without requiring any
random-matrix context.
