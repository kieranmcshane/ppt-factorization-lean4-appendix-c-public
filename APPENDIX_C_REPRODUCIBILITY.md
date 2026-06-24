# Appendix C Lean Reproducibility

This branch contains a standalone Lean module for the checked Appendix C
reductions and scaling endpoints:

```text
PptFactorization/AppendixCMainResult.lean
```

The module consolidates the already-proved Lean routes, with the following
scope distinctions:

- `appendixC_main_algebraic_universality`: checked conditional algebraic
  reduction proving both `g | f1 - f0'` and the first-order coefficient `-1`
  from explicit rootwise trace/kernel/coprimality hypotheses;
- `appendixC_canonical_universal_scaling_law`: checked all-`m` canonical
  engineered branch, not the all-`m` physical determinant theorem;
- `appendixC_self_contained_tridiagonal_scaling_law`: checked
  tridiagonal/Chebyshev route from `UniversalScalingLawProof`;
- `appendixC_physical_scaling_law_m1/m2/m3`: checked concrete physical
  determinant cases.

The all-`m` identification of the actual physical determinant with the
canonical Appendix C branch is not formalized in this module.

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
