# PPT factorization Lean archive

This repository is a Lean 4 formalization workspace for parts of the
moment-based PPT threshold project.  It contains checked algebraic reductions,
concrete small cases, finite computations, and Appendix B assembly interfaces.
It is not a complete formal proof of every Appendix B/C paper claim.

The public API is deliberately status-labelled.  In particular:

- all-`m` canonical scaling is formalized for an engineered canonical branch;
- physical determinant scaling is checked here only for `m = 1, 2, 3`;
- Appendix C algebraic universality is a conditional spine with supplier
  hypotheses;
- Appendix B high-level statements are conditional assemblies exposing analytic
  hypotheses in their theorem statements.

## Build

The pinned toolchain is:

```text
leanprover/lean4:v4.29.0-rc8
```

Recommended local check:

```bash
lake exe cache get
lake build
```

Focused Appendix C check:

```bash
lake build PptFactorization.AppendixCMainResult
```

Portable focused axiom audit:

```bash
lake env lean --stdin <<'EOF'
import PptFactorization.AppendixCMainResult
#print axioms AppendixCMainResult.appendixC_algebraic_spine_universality
#print axioms AppendixCMainResult.appendixC_canonical_universal_scaling_law
#print axioms AppendixCMainResult.appendixC_physical_scaling_law_m1
#print axioms AppendixCMainResult.appendixC_physical_scaling_law_m2
#print axioms AppendixCMainResult.appendixC_physical_scaling_law_m3
EOF
```

The expected axiom output for these endpoints is only the usual Lean/mathlib
foundations: `propext`, `Classical.choice`, and `Quot.sound`.

CI is configured under `.github/workflows/lean_action_ci.yml` and runs the
pinned Lean/Lake build through `leanprover/lean-action`.

## Theorem Inventory

| File | Endpoint | Mathematical meaning | Status |
| --- | --- | --- | --- |
| `PptFactorization/AppendixCMainResult.lean` | `appendixC_algebraic_spine_universality` | Appendix C determinant congruence `g | f1 - f0'` plus coefficient `-1`, assuming trace/root/rank-one/kernel/coprimality/coefficient suppliers | conditional reduction |
| `PptFactorization/AppendixCMainResult.lean` | `appendixC_main_algebraic_universality` | Backwards-compatible name for the same algebraic spine | conditional reduction |
| `PptFactorization/AppendixCMainResult.lean` | `appendixC_canonical_universal_scaling_law` | All-`m` scaling for the engineered canonical branch | canonical branch |
| `PptFactorization/PhysicalScalingLaw.lean` | `canonical_universal_scaling_law` | Underlying all-`m` canonical scaling theorem | canonical branch |
| `PptFactorization/PhysicalScalingLaw.lean` | `universal_physical_scaling_law` | Compatibility alias for the canonical branch; despite the old name, not the all-`m` physical determinant theorem | canonical branch / legacy alias |
| `PptFactorization/PhysicalScalingLaw.lean` | `physical_scaling_law_conditional` | Taylor theorem implication from `PhysicalThresholdExists m` to the scaling estimate | conditional reduction |
| `PptFactorization/AppendixCMainResult.lean` | `appendixC_physical_scaling_law_m1/m2/m3` | Physical determinant scaling checked for concrete small cases | small concrete cases |
| `PptFactorization/AppendixBFinal.lean` | `final_appendixB_assembly_no_structure_inputs` | Appendix B tail assembly once analytic assumptions are supplied directly | conditional assembly |
| `PptFactorization/ComplexGaussianWick.lean` | `concrete_wick_isserlis_entry_monomial_noInput` | No-input Wick/Isserlis expansion for concrete Gaussian matrix-entry monomials | fully proved |
| `PptFactorization/Verify.lean` | `factorization_m0/m1/m2` | Determinant factorization checks using the safe finite `Phi_d*` table | small theorem-certified cases |
| `PptFactorization/Verify.lean` | `#eval verifyAll` | Runtime diagnostics for `m = 0..8`, using `rhs?`/`phiStar?` | runtime computation |
| `PptFactorization/FormalizationStatus.lean` | grouped namespace exports | Reviewer-facing index of the public theorem surface by status | documentation/API index |

## What Is Proved

- The Appendix C algebraic spine proves the congruence and coefficient
  conclusion once the stated supplier hypotheses are provided.
- The canonical Chebyshev/tridiagonal scaling branch is checked for all `m`.
- The physical determinant scaling branch is checked concretely for
  `m = 1, 2, 3`.
- The concrete Gaussian Wick/Isserlis entry-monomial endpoint is no-input.
- The determinant factorization file theorem-certifies `m = 0,1,2`.
- Appendix B assembly theorems correctly combine supplied analytic hypotheses
  with already-available probability/expectation interfaces.

## What Is Not Proved Here

- The all-`m` identification of the physical determinant `detB_m(., d1)` with
  the canonical Appendix C branch.
- The full all-`m` non-crossing-partition/subleading correction supplier for
  Appendix C.
- A closed Appendix B proof of the global spherical Levy theorem for the exact
  concrete spherical model, unless supplied through the theorem interface.
- A closed Appendix B proof of every local Lipschitz, bad-set, median/range,
  integrability, expectation-bound, and localized tail-smallness input.
- Determinant factorization beyond the theorem-certified small cases in
  `Verify.lean`; the `m = 0..8` loop is runtime evidence, not theorem-level
  certification.

## Finite Computation Safety

`PptFactorization.Poly` now exposes:

- `phiStar? : Nat -> Option Poly`;
- `rhs? : Nat -> Option Poly`;
- `verifyDetFactorization? : Nat -> Option Bool`.

These return `none` when a requested `Phi_d*` factor is outside the finite
table.  The legacy wrappers `phiStar` and `rhs` remain only for compatibility
with old demos and are documented as unsafe for public verification.

## Reproducibility

`lakefile.toml` pins `mathlib` to the same commit as `lake-manifest.json`.
Avoid running a broad dependency update when reproducing this snapshot.  Use the
toolchain and manifest as committed.

## Public Claim Discipline

When citing this repository, distinguish:

- fully proved no-input endpoints;
- checked conditional reductions;
- checked canonical engineered branches;
- checked concrete small cases;
- runtime computations;
- theorem-shaped contracts for paper-side inputs;
- results not yet formalized for all parameters.
