# PPT factorization Lean archive

This repository is a Lean 4 formalization workspace for parts of the PPT
threshold project.  It contains checked algebraic reductions, concrete small
cases, and supporting probabilistic/combinatorial infrastructure.  It should
not be read as a complete formal proof of every Appendix B/C paper claim.

## Quick check

The Appendix C consolidation module is the main public entry point:

```bash
lake build PptFactorization.AppendixCMainResult
```

Portable focused axiom audit:

```bash
lake env lean --stdin <<'EOF'
import PptFactorization.AppendixCMainResult
#print axioms AppendixCMainResult.appendixC_main_algebraic_universality
#print axioms AppendixCMainResult.appendixC_canonical_universal_scaling_law
#print axioms AppendixCMainResult.appendixC_physical_scaling_law_m1
#print axioms AppendixCMainResult.appendixC_physical_scaling_law_m2
#print axioms AppendixCMainResult.appendixC_physical_scaling_law_m3
EOF
```

The expected axiom output for these endpoints is only the usual Lean/mathlib
foundations: `propext`, `Classical.choice`, and `Quot.sound`.

## Appendix C status

| Lean endpoint | Status |
| --- | --- |
| `AppendixCMainResult.appendixC_main_algebraic_universality` | Checked conditional algebraic reduction.  It proves `g | f1 - f0'` and `coeff = -1` from explicit trace, root, rank-one, kernel, and coprimality hypotheses. |
| `AppendixCMainResult.appendixC_canonical_universal_scaling_law` | Checked all-`m` canonical engineered branch.  It is not the all-`m` physical determinant theorem. |
| `AppendixCMainResult.appendixC_self_contained_tridiagonal_scaling_law` | Checked tridiagonal/Chebyshev scaling route from `UniversalScalingLawProof`. |
| `AppendixCMainResult.appendixC_physical_scaling_law_m1` | Checked concrete physical determinant case. |
| `AppendixCMainResult.appendixC_physical_scaling_law_m2` | Checked concrete physical determinant case. |
| `AppendixCMainResult.appendixC_physical_scaling_law_m3` | Checked concrete physical determinant case. |
| all-`m` physical determinant identification | Not formalized here.  The algebraic endpoint states the data needed to connect a physical finite-`d1` determinant to the universal Appendix C spine. |

The companion problem sheet
`AppendixC_olympiad_problem.tex` gives a self-contained pure problem version of
Theorem C.2, using noncrossing partitions and coefficient extraction.

## Appendix B status

Appendix B files are currently best read as reduction/interface layers.  Some
final-looking wrappers still take theorem-strength analytic hypotheses directly,
including spherical concentration, bad-set estimates, expectation controls,
local Lipschitz inputs, and tail-smallness assumptions.  Those wrappers are
useful for checking how the final concentration proof assembles, but they do
not by themselves close the full paper-level Appendix B theorem.

## Reproducibility notes

The project uses Lean `v4.29.0-rc8`.  The manifest pins exact dependency
revisions.  The public snapshot is intended for source-level review and focused
Lean checks, not as a polished release package with CI.

See `FORMALIZATION_STATUS.md` for the current claim ledger, including finite
runtime checks and finite-domain helper limitations.

## Public claim discipline

When citing this repository, distinguish:

- checked conditional algebraic reductions;
- checked canonical engineered branches;
- checked concrete small cases;
- theorem-shaped contracts for paper-side inputs;
- results not yet formalized for all parameters.
