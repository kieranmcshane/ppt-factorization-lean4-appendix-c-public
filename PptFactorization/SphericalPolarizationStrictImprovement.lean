import PptFactorization.PolarizationLemma43Core
import PptFactorization.PolarizationLemma43MeasureTrimming
import PptFactorization.SphericalPolarizationGeometricKernel

/-!
# Spherical polarization: strict improvement from the kernel block estimate

This file connects the geometric-kernel interface to the quantitative core of
Lemma 4.3.

**Closed upstream:** spherical change-of-variables / Jacobian with explicit
`K_n = 2^{-(n-2)} (‖x-y‖/2)^{-(n-2)}` — see
`finRealSphereReflectionMap_pushforward_withDensity` and
`finRealSphereReflectionMap_isJacobianTarget` in
`SphericalPolarizationPushforwardTransport.lean`, plus the abstract
`HasKernelChangeOfVariables` chain in `SphericalPolarizationGeometricKernel.lean`.

**What this file consumes:** the scalar rectangular-block inequality
`HasRectangularBlockLowerBound` (integral restriction to `D_- × D_+` with
`Δ ≥ τ` and `K_n ≥ 2^{-(n-2)}`, packaged as a real hypothesis for the
algebraic core). That is not the Jacobian itself; it is the post-COV
product lower bound feeding `PolarizationLemma43Core`.
-/

namespace SphericalPolarization.GeometricKernel

open scoped symmDiff
open PptFactorization.AppendixB

/-- The named geometric block estimate implies the average-to-supremum strict
improvement lower bound with the constant `tau * eps^2 / 2^(n+1)`. -/
theorem strict_improvement_from_rectangularBlockLowerBound
    (n : ℕ)
    (hn : 2 ≤ n)
    {eps tau muMinus muPlus avg supDelta : ℝ}
    (heps : 0 ≤ eps)
    (htau : 0 ≤ tau)
    (hminus : eps / 4 ≤ muMinus)
    (hplus : eps / 4 ≤ muPlus)
    (hRect : HasRectangularBlockLowerBound n tau muMinus muPlus avg)
    (havgLeSup : avg ≤ supDelta) :
    tau * eps ^ 2 / ((2 : ℝ) ^ (n + 1)) ≤ supDelta := by
  exact PolarizationLemma43Core.strict_improvement_from_average
    n hn heps htau hminus hplus
    (rectangularBlockLowerBound_as_core_hypothesis hRect)
    havgLeSup

/--
Full quantitative strict-improvement conclusion from the named rectangular
kernel block estimate.

This is the bridge theorem once `HasRectangularBlockLowerBound` is available
(Jacobian/CV already closed separately).
-/
theorem lemma43_strict_improvement_from_rectangularBlockLowerBound
    (n : ℕ)
    (hn : 2 ≤ n)
    {eps tau symm miss extra bandPlus bandMinus
      muMinus muPlus avg supDelta : ℝ}
    (heps : 0 < eps)
    (htau : 0 < tau)
    (hsymm : symm = miss + extra)
    (hbalance : miss = extra)
    (hfar : eps ≤ symm)
    (hbandPlus : bandPlus ≤ eps / 4)
    (hbandMinus : bandMinus ≤ eps / 4)
    (hDplus : miss - bandPlus ≤ muPlus)
    (hDminus : extra - bandMinus ≤ muMinus)
    (hRect : HasRectangularBlockLowerBound n tau muMinus muPlus avg)
    (havgLeSup : avg ≤ supDelta) :
    0 < tau * eps ^ 2 / ((2 : ℝ) ^ (n + 1)) ∧
      tau * eps ^ 2 / ((2 : ℝ) ^ (n + 1)) ≤ supDelta := by
  exact PolarizationLemma43Core.lemma43_strict_improvement_core
    n hn heps htau hsymm hbalance hfar
    hbandPlus hbandMinus hDplus hDminus
    (rectangularBlockLowerBound_as_core_hypothesis hRect)
    havgLeSup

/--
Strict improvement with measure-theoretic trimming on `FinRealSphere` (sets and
`finRealSurfaceProbabilityMeasure` hypotheses instead of abstract reals).
-/
theorem lemma43_strict_improvement_from_measure_trimming
    (n : ℕ)
    [NeZero n]
    (hn : 2 ≤ n)
    {eps tau avg supDelta : ℝ}
    {C E bandPlus bandMinus : Set (FinRealSphere n)}
    (heps : 0 < eps)
    (htau : 0 < tau)
    (hC : MeasurableSet C) (hE : MeasurableSet E)
    (hBandPlus : MeasurableSet bandPlus) (hBandMinus : MeasurableSet bandMinus)
    (hbalance :
      (finRealSurfaceProbabilityMeasure n).real (finRealPolarizationMiss C E) =
        (finRealSurfaceProbabilityMeasure n).real (finRealPolarizationExtra C E))
    (hfar :
      eps ≤ (finRealSurfaceProbabilityMeasure n).real (C ∆ E))
    (hbandPlus : (finRealSurfaceProbabilityMeasure n).real bandPlus ≤ eps / 4)
    (hbandMinus : (finRealSurfaceProbabilityMeasure n).real bandMinus ≤ eps / 4)
    (hRect :
      HasRectangularBlockLowerBound n tau
        (finRealPolarizationMuMinus C E bandMinus)
        (finRealPolarizationMuPlus C E bandPlus)
        avg)
    (havgLeSup : avg ≤ supDelta) :
    0 < tau * eps ^ 2 / ((2 : ℝ) ^ (n + 1)) ∧
      tau * eps ^ 2 / ((2 : ℝ) ^ (n + 1)) ≤ supDelta :=
  PptFactorization.AppendixB.lemma43_strict_improvement_from_measure_trimming
    n hn heps htau hC hE hBandPlus hBandMinus hbalance hfar hbandPlus hbandMinus
    hRect havgLeSup

end SphericalPolarization.GeometricKernel
