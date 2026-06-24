# Formalization status

This file records the intended claim scope of the main public endpoints.  It is
not a proof script; it is a map for reviewers.

## Appendix C

| Item | Formal status | Notes |
| --- | --- | --- |
| Algebraic congruence and coefficient extraction | Checked conditional reduction | `AppendixCMainResult.appendixC_main_algebraic_universality` proves `g | f1 - f0'` and `coeff = -1` from explicit Appendix C supplier hypotheses. |
| Rootwise coefficient endpoint | Checked conditional reduction | `appendixC_rootwise_coefficient_eq_neg_one` exposes only `coeff = -1`. |
| Congruence-only endpoint | Checked conditional reduction | `appendixC_congruence_mod_threshold_polynomial` proves `g | f1 - f0'` from rootwise vanishing and trace data. |
| Canonical all-`m` scaling branch | Checked, canonical only | `appendixC_canonical_universal_scaling_law` uses the engineered canonical ambient function.  It is not the all-`m` physical determinant theorem. |
| Self-contained tridiagonal branch | Checked | `appendixC_self_contained_tridiagonal_scaling_law` exposes `UniversalScalingLawProof.complete`. |
| Physical determinant, `m = 1` | Checked concrete case | `appendixC_physical_scaling_law_m1`. |
| Physical determinant, `m = 2` | Checked concrete case | `appendixC_physical_scaling_law_m2`. |
| Physical determinant, `m = 3` | Checked concrete case | `appendixC_physical_scaling_law_m3`. |
| Physical determinant, all `m` | Not closed here | The paper-side identification of the actual finite-`d1` determinant with the canonical/all-`m` Appendix C spine remains outside the checked all-`m` endpoints. |

## Appendix B

Appendix B contains meaningful assembly and transport lemmas, but high-level
wrappers still take theorem-strength analytic inputs.  Treat these as
interfaces/reductions unless a wrapper's assumptions have been separately
discharged for the concrete spherical model.

Examples of still-visible theorem-strength inputs include spherical Levy-type
concentration, bad-set probability estimates, expectation comparisons,
local-Lipschitz controls, and tail-smallness estimates.

## Computational evidence

Some files contain runtime checks or `#eval`-style evidence for finite
determinants.  These checks are useful diagnostics, but only named theorem
statements that build in Lean should be counted as formal proof coverage.

In particular, `PptFactorization.Verify` theorem-certifies the determinant
factorization for `m = 0,1,2`.  The cases `m = 3..8` are recorded there as
runtime `#eval` evidence/commented local checks, not as public theorem
certificates in this snapshot.

The helper `PPT.phiStar` in `PptFactorization.Poly` is a finite table for the
currently tested cyclotomic factors.  It returns `1` outside the table, so it
should be treated as a finite-range computational helper unless accompanied by a
separate proof that all queried divisors lie in the supported range.

## Dependency note

The checked snapshot uses Lean `v4.29.0-rc8` and the dependency revisions in
`lake-manifest.json`.  Avoid running an unconstrained dependency update when
reproducing the public snapshot.
