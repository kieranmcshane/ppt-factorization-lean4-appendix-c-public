import PptFactorization.MeasureTheoreticTrimming
import PptFactorization.PolarizationLemma43Core
import PptFactorization.AppendixBSurfaceMeasure
import PptFactorization.SphericalPolarizationJacobianTargets
import PptFactorization.SphericalPolarizationGeometricKernel
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Real

/-!
# Lemma 4.3: `FinRealSphere` set dictionary and measure trimming bridge

Article-aligned set names on the canonical sphere, measurability of height bands,
and the specialization of `PolarizationLemma43Core.lemma43_strict_improvement_core_of_measureTrimming`
to `finRealSurfaceProbabilityMeasure`.

Generic finite-measure trimming lemmas live in `MeasureTheoreticTrimming`.
-/

noncomputable section

open MeasureTheory Set SphericalPolarization.MeasureTrimming
open scoped symmDiff Pointwise

namespace PptFactorization
namespace AppendixB

open SphericalPolarization.GeometricKernel

/-- Height band `{a ≤ φ ≤ a + τ}` relative to pole `p`. -/
def finRealSphereHeightBandAbove (n : ℕ) (p : FinRealSphere n) (a τ : ℝ) :
    Set (FinRealSphere n) :=
  {x | a ≤ finRealSphereHeight n p x ∧ finRealSphereHeight n p x ≤ a + τ}

/-- Height band `{a - τ ≤ φ ≤ a}` relative to pole `p`. -/
def finRealSphereHeightBandBelow (n : ℕ) (p : FinRealSphere n) (a τ : ℝ) :
    Set (FinRealSphere n) :=
  {x | a - τ ≤ finRealSphereHeight n p x ∧ finRealSphereHeight n p x ≤ a}

/-- Mass in `C` missing from `E`. -/
def finRealPolarizationMiss (C E : Set (FinRealSphere n)) : Set (FinRealSphere n) :=
  C \ E

/-- Mass in `E` not in `C`. -/
def finRealPolarizationExtra (C E : Set (FinRealSphere n)) : Set (FinRealSphere n) :=
  E \ C

/-- Trimmed positive defect `D₊ = (C \ E) \ bandPlus`. -/
def finRealPolarizationDPlus
    (C E bandPlus : Set (FinRealSphere n)) : Set (FinRealSphere n) :=
  finRealPolarizationMiss C E \ bandPlus

/-- Trimmed negative defect `D₋ = (E \ C) \ bandMinus`. -/
def finRealPolarizationDMinus
    (C E bandMinus : Set (FinRealSphere n)) : Set (FinRealSphere n) :=
  finRealPolarizationExtra C E \ bandMinus

theorem measurable_finRealSphereHeight (n : ℕ) (p : FinRealSphere n) :
    Measurable (fun x : FinRealSphere n => finRealSphereHeight n p x) := by
  unfold finRealSphereHeight
  fun_prop

theorem measurableSet_finRealSphereHeightBandAbove
    (n : ℕ) (p : FinRealSphere n) (a τ : ℝ) :
    MeasurableSet (finRealSphereHeightBandAbove n p a τ) := by
  unfold finRealSphereHeightBandAbove
  have hheight := measurable_finRealSphereHeight n p
  exact (measurableSet_le measurable_const hheight).inter
    (measurableSet_le hheight measurable_const)

theorem measurableSet_finRealSphereHeightBandBelow
    (n : ℕ) (p : FinRealSphere n) (a τ : ℝ) :
    MeasurableSet (finRealSphereHeightBandBelow n p a τ) := by
  unfold finRealSphereHeightBandBelow
  have hheight := measurable_finRealSphereHeight n p
  exact (measurableSet_le measurable_const hheight).inter
    (measurableSet_le hheight measurable_const)

theorem measurableSet_finRealPolarizationMiss
    {n : ℕ} {C E : Set (FinRealSphere n)}
    (hC : MeasurableSet C) (hE : MeasurableSet E) :
    MeasurableSet (finRealPolarizationMiss C E) :=
  hC.diff hE

theorem measurableSet_finRealPolarizationExtra
    {n : ℕ} {C E : Set (FinRealSphere n)}
    (hC : MeasurableSet C) (hE : MeasurableSet E) :
    MeasurableSet (finRealPolarizationExtra C E) :=
  hE.diff hC

theorem measurableSet_finRealPolarizationDPlus
    {n : ℕ} {C E bandPlus : Set (FinRealSphere n)}
    (hC : MeasurableSet C) (hE : MeasurableSet E) (hBand : MeasurableSet bandPlus) :
    MeasurableSet (finRealPolarizationDPlus C E bandPlus) :=
  (measurableSet_finRealPolarizationMiss hC hE).diff hBand

theorem measurableSet_finRealPolarizationDMinus
    {n : ℕ} {C E bandMinus : Set (FinRealSphere n)}
    (hC : MeasurableSet C) (hE : MeasurableSet E) (hBand : MeasurableSet bandMinus) :
    MeasurableSet (finRealPolarizationDMinus C E bandMinus) :=
  (measurableSet_finRealPolarizationExtra hC hE).diff hBand

variable {n : ℕ} [NeZero n]

private def μ (n : ℕ) : Measure (FinRealSphere n) :=
  finRealSurfaceProbabilityMeasure n

instance instIsProbabilityMeasureFinRealSurfaceProb {n : ℕ} [NeZero n] :
    IsProbabilityMeasure (finRealSurfaceProbabilityMeasure n) :=
  finRealSurfaceProbabilityMeasure_isProbabilityMeasure n

/-- Surface probability mass of the positive trimmed defect. -/
noncomputable def finRealPolarizationMuPlus
    (C E bandPlus : Set (FinRealSphere n)) : ℝ :=
  (μ n).real (finRealPolarizationDPlus C E bandPlus)

/-- Surface probability mass of the negative trimmed defect. -/
noncomputable def finRealPolarizationMuMinus
    (C E bandMinus : Set (FinRealSphere n)) : ℝ :=
  (μ n).real (finRealPolarizationDMinus C E bandMinus)

omit [NeZero n] in
/-- The positive trimmed defect has nonnegative surface mass. -/
theorem finRealPolarizationMuPlus_nonneg
    (C E bandPlus : Set (FinRealSphere n)) :
    0 ≤ finRealPolarizationMuPlus C E bandPlus := by
  simp [finRealPolarizationMuPlus]

omit [NeZero n] in
/-- The negative trimmed defect has nonnegative surface mass. -/
theorem finRealPolarizationMuMinus_nonneg
    (C E bandMinus : Set (FinRealSphere n)) :
    0 ≤ finRealPolarizationMuMinus C E bandMinus := by
  simp [finRealPolarizationMuMinus]

omit [NeZero n] in
/-- The rectangular-block lower bound for the concrete trimmed defects can be
degraded to any smaller separation parameter. -/
theorem finRealPolarization_rectangularBlockLowerBound_mono_tau
    {τsmall τbig avg : ℝ}
    {C E bandPlus bandMinus : Set (FinRealSphere n)}
    (hτ : τsmall ≤ τbig)
    (h :
      HasRectangularBlockLowerBound n τbig
        (finRealPolarizationMuMinus C E bandMinus)
        (finRealPolarizationMuPlus C E bandPlus)
        avg) :
      HasRectangularBlockLowerBound n τsmall
        (finRealPolarizationMuMinus C E bandMinus)
        (finRealPolarizationMuPlus C E bandPlus)
        avg :=
  HasRectangularBlockLowerBound.mono_tau hτ
    (finRealPolarizationMuMinus_nonneg C E bandMinus)
    (finRealPolarizationMuPlus_nonneg C E bandPlus) h

/-- Concrete two-sided trimming lower bound for the `FinRealSphere`
polarization defects, stated with the article's `D₊`/`D₋` names. -/
theorem finRealPolarization_trimmed_masses_lower_bound_of_balance
    {eps : ℝ}
    {C E bandPlus bandMinus : Set (FinRealSphere n)}
    (hE : MeasurableSet E) (hC : MeasurableSet C)
    (hBandPlus : MeasurableSet bandPlus)
    (hBandMinus : MeasurableSet bandMinus)
    (hfar :
      eps ≤
        (finRealSurfaceProbabilityMeasure n).real (C ∆ E))
    (hbalance :
      (finRealSurfaceProbabilityMeasure n).real (C \ E) =
        (finRealSurfaceProbabilityMeasure n).real (E \ C))
    (hbandPlus :
      (finRealSurfaceProbabilityMeasure n).real bandPlus ≤ eps / 4)
    (hbandMinus :
      (finRealSurfaceProbabilityMeasure n).real bandMinus ≤ eps / 4) :
    eps / 4 ≤ finRealPolarizationMuPlus C E bandPlus ∧
      eps / 4 ≤ finRealPolarizationMuMinus C E bandMinus := by
  haveI : IsFiniteMeasure (finRealSurfaceProbabilityMeasure n) := inferInstance
  have htrim :=
    PolarizationLemma43Core.measureReal_symmDiff_trim_lower_bounds
      (μ := finRealSurfaceProbabilityMeasure n)
      (eps := eps)
      (E := E) (C := C)
      (Bplus := bandPlus) (Bminus := bandMinus)
      (Dplus := finRealPolarizationDPlus C E bandPlus)
      (Dminus := finRealPolarizationDMinus C E bandMinus)
      hE hC hBandPlus hBandMinus
      (by simpa [symmDiff_comm] using hfar)
      hbalance hbandPlus hbandMinus
      (by
        intro x hx
        simpa [finRealPolarizationDPlus, finRealPolarizationMiss] using hx)
      (by
        intro x hx
        simpa [finRealPolarizationDMinus, finRealPolarizationExtra] using hx)
  simpa [finRealPolarizationMuPlus, finRealPolarizationMuMinus, μ] using htrim

/-- Concrete two-sided trimming lower bound when the model set and competitor
have equal normalized surface mass. -/
theorem finRealPolarization_trimmed_masses_lower_bound_of_equal_mass
    {eps : ℝ}
    {C E bandPlus bandMinus : Set (FinRealSphere n)}
    (hE : MeasurableSet E) (hC : MeasurableSet C)
    (hBandPlus : MeasurableSet bandPlus)
    (hBandMinus : MeasurableSet bandMinus)
    (hmass :
      (finRealSurfaceProbabilityMeasure n).real C =
        (finRealSurfaceProbabilityMeasure n).real E)
    (hfar :
      eps ≤
        (finRealSurfaceProbabilityMeasure n).real (C ∆ E))
    (hbandPlus :
      (finRealSurfaceProbabilityMeasure n).real bandPlus ≤ eps / 4)
    (hbandMinus :
      (finRealSurfaceProbabilityMeasure n).real bandMinus ≤ eps / 4) :
    eps / 4 ≤ finRealPolarizationMuPlus C E bandPlus ∧
      eps / 4 ≤ finRealPolarizationMuMinus C E bandMinus := by
  have hbalance :
      (finRealSurfaceProbabilityMeasure n).real (C \ E) =
        (finRealSurfaceProbabilityMeasure n).real (E \ C) := by
    have hCdecomp :
        (finRealSurfaceProbabilityMeasure n).real (C \ E) +
            (finRealSurfaceProbabilityMeasure n).real (C ∩ E) =
          (finRealSurfaceProbabilityMeasure n).real C :=
      measureReal_diff_add_inter
        (μ := finRealSurfaceProbabilityMeasure n) (s := C) (t := E) hE
    have hEdecomp :
        (finRealSurfaceProbabilityMeasure n).real (E \ C) +
            (finRealSurfaceProbabilityMeasure n).real (E ∩ C) =
          (finRealSurfaceProbabilityMeasure n).real E :=
      measureReal_diff_add_inter
        (μ := finRealSurfaceProbabilityMeasure n) (s := E) (t := C) hC
    have hinter :
        (finRealSurfaceProbabilityMeasure n).real (E ∩ C) =
          (finRealSurfaceProbabilityMeasure n).real (C ∩ E) := by
      rw [Set.inter_comm]
    linarith
  exact
    finRealPolarization_trimmed_masses_lower_bound_of_balance
      hE hC hBandPlus hBandMinus hfar hbalance hbandPlus hbandMinus

/--
Lemma 4.3 strict improvement on `FinRealSphere`, with trimming and symmetric
difference stated measure-theoretically.
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
      (μ n).real (finRealPolarizationMiss C E) =
        (μ n).real (finRealPolarizationExtra C E))
    (hfar : eps ≤ (μ n).real (C ∆ E))
    (hbandPlus : (μ n).real bandPlus ≤ eps / 4)
    (hbandMinus : (μ n).real bandMinus ≤ eps / 4)
    (hRect :
      HasRectangularBlockLowerBound n tau
        (finRealPolarizationMuMinus C E bandMinus)
        (finRealPolarizationMuPlus C E bandPlus)
        avg)
    (havgLeSup : avg ≤ supDelta) :
    0 < tau * eps ^ 2 / ((2 : ℝ) ^ (n + 1)) ∧
      tau * eps ^ 2 / ((2 : ℝ) ^ (n + 1)) ≤ supDelta :=
  haveI : IsFiniteMeasure (finRealSurfaceProbabilityMeasure n) := inferInstance
  PolarizationLemma43Core.lemma43_strict_improvement_core_of_measureTrimming
    (μ := finRealSurfaceProbabilityMeasure n)
    (Dplus := finRealPolarizationDPlus C E bandPlus)
    (Dminus := finRealPolarizationDMinus C E bandMinus)
    n hn heps htau hE hC hBandPlus hBandMinus
    (by
      simpa [symmDiff_comm] using hfar)
    hbalance hbandPlus hbandMinus
    (by
      intro x hx
      simpa [finRealPolarizationDPlus, finRealPolarizationMiss] using hx)
    (by
      intro x hx
      simpa [finRealPolarizationDMinus, finRealPolarizationExtra] using hx)
    (by
      simpa [finRealPolarizationMuMinus, finRealPolarizationMuPlus] using
        rectangularBlockLowerBound_as_core_hypothesis hRect)
    havgLeSup

end AppendixB
end PptFactorization
