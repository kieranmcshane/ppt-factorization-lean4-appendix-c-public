import PptFactorization.SphericalPolarizationJacobianTargets
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.LinearAlgebra.Determinant
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.Jacobian

set_option maxHeartbeats 0
/-!
# Surface-measure transport for the reflection push-forward

Closed transport proof for
`finRealSphereReflectionMap_pushforward_withDensity`.

**Closed upstream (`SphericalPolarizationJacobianTargets`):** bijection/image
identities, measurability, null boundaries, and the `lintegral ↔ withDensity`
bridges.

**Closed here:**
1. `finRealSphereReflectionMap_tangentJacobian_eq_polarizationKernel`
2. `finRealSphereReflectionMap_ambient_surfaceCone_transport`
3. `finRealSphereReflectionMap_pushforward_lintegral_formula`

The measure-level `withDensity` formula follows from
`finRealSphereReflectionMap_pushforward_withDensity_of_lintegral`.
-/

noncomputable section

open scoped ENNReal Pointwise
open MeasureTheory Set
open InnerProductSpace

namespace PptFactorization
namespace AppendixB

variable {n : ℕ}

open SphericalPolarization.GeometricKernel

/-- Local names for one reflection fibre `(p,y)`. -/
structure FibrePackaging (n : ℕ) (p y : FinRealSphere n) where
  ρ : FinRealSphereReflectionMap n := finRealSphereReflectionMap n
  φ : FinRealSphere n → FinRealSphere n := finRealSpherePolarizationParam ρ y
  domain : Set (FinRealSphere n) :=
    finRealSphereAdmissibleHemisphere n p ∩ finRealSphereDirectionHemisphere n y
  targetPunctured : Set (FinRealSphere n) :=
    {x : FinRealSphere n |
      finRealSphereHeight n p x ≤ finRealSphereHeight n p y} \ {y}

namespace FibrePackaging

/-- Measurability and bijection/image identities for one fibre (all proved). -/
theorem closed_geometric_packaging (n : ℕ) (p y : FinRealSphere n) :
    Measurable (finRealSpherePolarizationParam (finRealSphereReflectionMap n) y) ∧
      BijOn
        (finRealSpherePolarizationParam (finRealSphereReflectionMap n) y)
        (finRealSphereAdmissibleHemisphere n p ∩
          finRealSphereDirectionHemisphere n y)
        ({x : FinRealSphere n |
            finRealSphereHeight n p x ≤ finRealSphereHeight n p y} \ {y}) ∧
        (finRealSpherePolarizationParam (finRealSphereReflectionMap n) y) ''
          (finRealSphereAdmissibleHemisphere n p ∩
            finRealSphereDirectionHemisphere n y) =
          {x : FinRealSphere n |
            finRealSphereHeight n p x ≤ finRealSphereHeight n p y} \ {y} := by
  constructor
  · exact finRealSphereReflectionMap_param_measurable n y
  constructor
  · exact
      finRealSpherePolarizationParam_bijOn_admissible_direction_heightSublevel_diff_singleton
        n p y
  · exact
      finRealSpherePolarizationParam_image_admissible_direction_eq_heightSublevel_diff_singleton
        n p y

end FibrePackaging

/-- Canonical reflected tangent frame for the fibre Jacobian at `(y,v)`. -/
noncomputable def finRealSphereReflectionTangentJacobianFrame
    (n : ℕ) (hn2 : 2 ≤ n) (y v : FinRealSphere n)
    (hmer :
      SphericalPolarization.GeometricKernel.meridianDirection
        (y : FinRealEuclideanSpace n) (v : FinRealEuclideanSpace n) ≠ 0) :
    Fin (n - 2 + 1) →
      SphericalPolarization.GeometricKernel.tangentSubspace
        (SphericalPolarization.GeometricKernel.reflection
          (v : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n)) :=
  fun i =>
    SphericalPolarization.GeometricKernel.reflectionTangentDeriv
      (y : FinRealEuclideanSpace n) (v : FinRealEuclideanSpace n)
      (finRealSphere_norm_coe n v)
      (SphericalPolarization.GeometricKernel.adaptedTangentFrame
        (y : FinRealEuclideanSpace n) (v : FinRealEuclideanSpace n)
        (finRealSphere_norm_coe n v)
        (SphericalPolarization.GeometricKernel.planeOrthogonalSubspace.orthonormalBasisOfFinrank
          (y := (y : FinRealEuclideanSpace n))
          (v := (v : FinRealEuclideanSpace n)) (n - 2)
          (SphericalPolarization.GeometricKernel.planeOrthogonalSubspace_finrank_of_pair_linearIndependent
            (y := (y : FinRealEuclideanSpace n))
            (v := (v : FinRealEuclideanSpace n)) (m := n - 2)
            (by
              rw [finRealSphere_moduleFinrank n]
              omega)
            (SphericalPolarization.GeometricKernel.polarizationPair_linearIndependent_of_meridian_ne_zero
              (finRealSphere_norm_coe n v) hmer)))
        i)

/-- Density function in the target `withDensity` formula. -/
def finRealSphereReflectionMap_pushforward_density
    (n : ℕ) (p y : FinRealSphere n) : FinRealSphere n → ℝ≥0∞ :=
  fun x =>
    if finRealSphereHeight n p x ≤ finRealSphereHeight n p y then
      finRealSpherePolarizationKernel n x y
    else
      0

/-- Restricted source measure for one fibre. -/
def finRealSphereReflectionMap_pushforward_sourceMeasure
    (n : ℕ) (p y : FinRealSphere n) : Measure (FinRealSphere n) :=
  (finRealSurfaceProbabilityMeasure n).restrict
    (finRealSphereAdmissibleHemisphere n p ∩ finRealSphereDirectionHemisphere n y)

/-!
### Leaf 1 — tangent Jacobian density on a fibre

Package the `GeometricKernel` chordal identity on the concrete sphere.
Expected supplier:
`normalized_inverse_abs_volumeForm_reflectionTangentDeriv_eq_sphericalKernelChordal`.
-/

def FinRealSphereReflectionMapTangentJacobianOnFibre (n : ℕ) : Prop :=
  ∀ (hn2 : 2 ≤ n) (y v : FinRealSphere n)
      (_hv : v ∈ finRealSphereDirectionHemisphere n y)
      (hmer :
        SphericalPolarization.GeometricKernel.meridianDirection
          (y : FinRealEuclideanSpace n) (v : FinRealEuclideanSpace n) ≠ 0)
      (_hFin :
        Fact (Module.finrank ℝ
          (SphericalPolarization.GeometricKernel.tangentSubspace
            (SphericalPolarization.GeometricKernel.reflection
              (v : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n))) =
          n - 2 + 1)),
    ∀ (o : Orientation ℝ
          (SphericalPolarization.GeometricKernel.tangentSubspace
            (SphericalPolarization.GeometricKernel.reflection
              (v : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n)))
          (Fin (n - 2 + 1))),
      (2 : ℝ) *
          (|o.volumeForm (finRealSphereReflectionTangentJacobianFrame n hn2 y v hmer)|)⁻¹ =
        SphericalPolarization.GeometricKernel.sphericalKernelChordal n
          (SphericalPolarization.GeometricKernel.reflection
            (v : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n))
          (y : FinRealEuclideanSpace n)

theorem finRealSphereReflectionMap_tangentJacobian_eq_polarizationKernel
    (n : ℕ) :
    FinRealSphereReflectionMapTangentJacobianOnFibre n := by
  intro hn2 y v _hv hmer hFin o
  haveI := hFin
  let E := FinRealEuclideanSpace n
  let m := n - 2
  have hy : ‖(y : E)‖ = 1 := finRealSphere_norm_coe n y
  have hv1 : ‖(v : E)‖ = 1 := finRealSphere_norm_coe n v
  have hpos : 0 < inner ℝ (y : E) (v : E) := _hv
  have hE : Module.finrank ℝ E = m + 2 := by
    rw [finRealSphere_moduleFinrank n]
    omega
  have hm : m + 1 = n - 2 + 1 := by omega
  haveI :
      Fact (Module.finrank ℝ
          (SphericalPolarization.GeometricKernel.tangentSubspace
            (SphericalPolarization.GeometricKernel.reflection (v : E) (y : E))) =
        m + 1) :=
    ⟨by rw [← hm]; exact hFin.out⟩
  exact
    normalized_inverse_abs_volumeForm_reflectionTangentDeriv_eq_sphericalKernelChordal
      (m := m) o hy hv1 hpos hmer hE

/-!
### Leaf 2 — ambient cone / `toSphere` transport

For any measurable set `S ⊆ FinRealSphere n`, the unnormalized surface measure
of `S` equals the ambient additive-Haar measure of the open cone
`(0,1) • (Subtype.val '' S)`, scaled by the ambient dimension.

This is `MeasureTheory.Measure.toSphere_apply'` repackaged in the project's
concrete notation.  It is the basic bridge between the surface side
(`finRealSurfaceMeasure` / `finRealSurfaceProbabilityMeasure`) and the ambient
side (`finRealHaarMeasure`) used by the leaf 3 change-of-variables.
-/

/-- Statement of the cone transport identity on the canonical real sphere. -/
def FinRealSphereReflectionMapAmbientSurfaceConeTransport (n : ℕ) : Prop :=
  ∀ ⦃S : Set (FinRealSphere n)⦄, MeasurableSet S →
    (finRealSurfaceMeasure n) S =
      (Module.finrank ℝ (FinRealEuclideanSpace n) : ℝ≥0∞) *
        (finRealHaarMeasure n)
          (Set.Ioo (0 : ℝ) 1 •
            ((↑) : FinRealSphere n → FinRealEuclideanSpace n) '' S)

/-- Leaf 2 (closed): the ambient surface-cone transport identity for
the canonical real-sphere reflection parametrization. -/
theorem finRealSphereReflectionMap_ambient_surfaceCone_transport
    (n : ℕ) :
    FinRealSphereReflectionMapAmbientSurfaceConeTransport n := by
  intro S hS
  show (finRealHaarMeasure n).toSphere S = _
  exact Measure.toSphere_apply' (finRealHaarMeasure n) hS

/-- Probability-measure form of leaf 2.  Combines the cone identity for the
unnormalized surface measure with the `toFinite` normalization.

For `n ≥ 1` and a measurable set `S ⊆ FinRealSphere n`, the normalized surface
measure of `S` times `haar(ball 0 1)` equals the ambient cone volume of
`(0,1) • (↑ '' S)`.  Equivalently, `μ_prob(S) = haar(cone S) / haar(ball 0 1)`. -/
theorem finRealSurfaceProbabilityMeasure_eq_cone_ratio
    {n : ℕ} [NeZero n] {S : Set (FinRealSphere n)} (hS : MeasurableSet S) :
    (finRealSurfaceProbabilityMeasure n) S *
        ((finRealHaarMeasure n) (Metric.ball (0 : FinRealEuclideanSpace n) 1)) =
      (finRealHaarMeasure n)
        (Set.Ioo (0 : ℝ) 1 •
          ((↑) : FinRealSphere n → FinRealEuclideanSpace n) '' S) := by
  haveI : (finRealHaarMeasure n).IsAddHaarMeasure := by
    unfold finRealHaarMeasure; infer_instance
  -- Cone identity for `finRealSurfaceMeasure` from leaf 2.
  have hcone :
      (finRealSurfaceMeasure n) S =
        (Module.finrank ℝ (FinRealEuclideanSpace n) : ℝ≥0∞) *
          (finRealHaarMeasure n)
            (Set.Ioo (0 : ℝ) 1 •
              ((↑) : FinRealSphere n → FinRealEuclideanSpace n) '' S) :=
    finRealSphereReflectionMap_ambient_surfaceCone_transport n hS
  -- Total surface measure is `n * haar(ball)` via `toSphere_apply_univ`.
  have huniv :
      (finRealSurfaceMeasure n) Set.univ =
        (Module.finrank ℝ (FinRealEuclideanSpace n) : ℝ≥0∞) *
          (finRealHaarMeasure n)
            (Metric.ball (0 : FinRealEuclideanSpace n) 1) := by
    show (finRealHaarMeasure n).toSphere Set.univ = _
    exact Measure.toSphere_apply_univ (finRealHaarMeasure n)
  -- Dimension positivity / finiteness.
  have hdim_pos : 0 < Module.finrank ℝ (FinRealEuclideanSpace n) := by
    rw [finRealSphere_moduleFinrank]
    exact Nat.pos_of_ne_zero (NeZero.ne n)
  have hdim_ne : (Module.finrank ℝ (FinRealEuclideanSpace n) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hdim_pos.ne'
  have hdim_top : (Module.finrank ℝ (FinRealEuclideanSpace n) : ℝ≥0∞) ≠ ∞ :=
    ENNReal.natCast_ne_top _
  -- Ball is positive and finite.
  have hball_lt_top :
      (finRealHaarMeasure n) (Metric.ball (0 : FinRealEuclideanSpace n) 1) < ∞ :=
    lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
      ((isCompact_closedBall (0 : FinRealEuclideanSpace n) 1).measure_lt_top)
  have hball_ne_top :
      (finRealHaarMeasure n) (Metric.ball (0 : FinRealEuclideanSpace n) 1) ≠ ∞ :=
    hball_lt_top.ne
  have hball_ne_zero :
      (finRealHaarMeasure n) (Metric.ball (0 : FinRealEuclideanSpace n) 1) ≠ 0 := by
    have hopen : IsOpen (Metric.ball (0 : FinRealEuclideanSpace n) 1) :=
      Metric.isOpen_ball
    exact hopen.measure_ne_zero _ ⟨0, by simp⟩
  -- Total surface measure is finite and positive.
  have huniv_lt_top : (finRealSurfaceMeasure n) Set.univ < ∞ := by
    rw [huniv]
    exact ENNReal.mul_lt_top hdim_top.lt_top hball_lt_top
  have huniv_ne_top : (finRealSurfaceMeasure n) Set.univ ≠ ∞ := huniv_lt_top.ne
  have huniv_ne_zero : (finRealSurfaceMeasure n) Set.univ ≠ 0 := by
    rw [huniv]
    exact mul_ne_zero hdim_ne hball_ne_zero
  -- Unfold `finRealSurfaceProbabilityMeasure` as `cond _ univ`.
  haveI hfin : IsFiniteMeasure (finRealSurfaceMeasure n) := ⟨huniv_lt_top⟩
  have hprob :
      (finRealSurfaceProbabilityMeasure n) S =
        ((finRealSurfaceMeasure n) Set.univ)⁻¹ *
          (finRealSurfaceMeasure n) S := by
    unfold finRealSurfaceProbabilityMeasure Measure.toFinite Measure.toFiniteAux
    rw [if_pos hfin, ProbabilityTheory.cond_apply MeasurableSet.univ,
      Set.univ_inter]
  -- Cancel the `μ_surface(univ)⁻¹` factor by multiplying through.
  apply (ENNReal.mul_right_inj huniv_ne_zero huniv_ne_top).mp
  -- Goal: μ_surface(univ) * (μ_prob(S) * B) = μ_surface(univ) * C
  -- where B = haar(ball), C = haar(cone S)
  rw [hprob]
  -- Goal: μ_surface(univ) * (μ_surface(univ)⁻¹ * μ_surface(S) * B)
  --     = μ_surface(univ) * C
  rw [show ∀ (a b c : ℝ≥0∞), a * (a⁻¹ * b * c) = (a * a⁻¹) * b * c from
        fun _ _ _ => by ring]
  rw [ENNReal.mul_inv_cancel huniv_ne_zero huniv_ne_top, one_mul]
  -- Goal: μ_surface(S) * B = μ_surface(univ) * C
  rw [hcone, huniv]
  -- Goal: (n * C) * B = (n * B) * C
  ring

/-- Open radial cone over a measurable subset of the real sphere. -/
def finRealSphereRadialOpenCone
    (n : ℕ) (S : Set (FinRealSphere n)) : Set (FinRealEuclideanSpace n) :=
  Set.Ioo (0 : ℝ) 1 •
    ((↑) : FinRealSphere n → FinRealEuclideanSpace n) '' S

/-- Ambient cone-volume form of the remaining north-pole large-exponent
coordinate-tail estimate.  This is the direct analytic volume-ratio statement
behind the spherical coordinate law. -/
def FinRealSphereNorthPoleCapConeGaussianTailLargeExponent
    (n : ℕ) [NeZero n] (realDim : ℝ) : Prop :=
  ∀ ⦃r : ℝ⦄, 2 ≤ n → 0 < r → r < Real.pi / 2 →
    Real.log 2 < ((realDim - 1) * r ^ 2) / 2 →
    (finRealHaarMeasure n)
        (finRealSphereRadialOpenCone n
          (finRealSphereClosedHalfspace n
            (-(finRealSphereNorthPole n : FinRealEuclideanSpace n))
            (Real.sin r))) ≤
      ENNReal.ofReal (Real.exp (-(((realDim - 1) * r ^ 2) / 2))) *
        (finRealHaarMeasure n) (Metric.ball (0 : FinRealEuclideanSpace n) 1)

/-- No-input package for the ambient cone-volume north-pole coordinate tail. -/
def sphere_northPoleCapConeGaussianTailLargeExponent : Prop :=
  ∀ (n : ℕ) [NeZero n],
    FinRealSphereNorthPoleCapConeGaussianTailLargeExponent n (n : ℝ)

/-- Algebraic cone-volume form of the north-pole coordinate tail.  It leaves
only the geometric power-law estimate for the spherical cap cone; the
exponential tail follows from `cos r ≤ exp(-r^2 / 2)`. -/
def FinRealSphereNorthPoleCapConeCosinePowerTail
    (n : ℕ) [NeZero n] : Prop :=
  ∀ ⦃r : ℝ⦄, 2 ≤ n → 0 < r → r < Real.pi / 2 →
    (finRealHaarMeasure n)
        (finRealSphereRadialOpenCone n
          (finRealSphereClosedHalfspace n
            (-(finRealSphereNorthPole n : FinRealEuclideanSpace n))
            (Real.sin r))) ≤
      ENNReal.ofReal (Real.cos r ^ (n - 1)) *
        (finRealHaarMeasure n) (Metric.ball (0 : FinRealEuclideanSpace n) 1)

/-- No-input package for the algebraic cap-cone tail. -/
def sphere_northPoleCapConeCosinePowerTail : Prop :=
  ∀ (n : ℕ) [NeZero n],
    FinRealSphereNorthPoleCapConeCosinePowerTail n

/-- Nontrivial below-half range of the algebraic cap-cone power law.  This is
the exact cone-volume tail range needed by the active upper endpoint; the
complementary range is handled elsewhere by antipodal half-tail symmetry. -/
def FinRealSphereNorthPoleCapConeCosinePowerTailBelowHalf
    (n : ℕ) [NeZero n] : Prop :=
  ∀ ⦃r : ℝ⦄, 2 ≤ n → 0 < r → r < Real.pi / 2 →
    Real.cos r ^ (n - 1) < 1 / 2 →
    (finRealHaarMeasure n)
        (finRealSphereRadialOpenCone n
          (finRealSphereClosedHalfspace n
            (-(finRealSphereNorthPole n : FinRealEuclideanSpace n))
            (Real.sin r))) ≤
      ENNReal.ofReal (Real.cos r ^ (n - 1)) *
        (finRealHaarMeasure n) (Metric.ball (0 : FinRealEuclideanSpace n) 1)

/-- No-input package for the below-half algebraic cap-cone tail. -/
def sphere_northPoleCapConeCosinePowerTailBelowHalf : Prop :=
  ∀ (n : ℕ) [NeZero n],
    FinRealSphereNorthPoleCapConeCosinePowerTailBelowHalf n

/-- The full cap-cone power law supplies its active below-half restriction. -/
theorem finRealSphereNorthPoleCapConeCosinePowerTailBelowHalf_of_capConeCosinePowerTail
    (n : ℕ) [NeZero n]
    (hTail : FinRealSphereNorthPoleCapConeCosinePowerTail n) :
    FinRealSphereNorthPoleCapConeCosinePowerTailBelowHalf n := by
  intro r hn2 hrpos hrlt _hhalf
  exact hTail hn2 hrpos hrlt

/-- No-input adapter from the full cap-cone power law to the below-half
cap-cone power law. -/
theorem sphere_northPoleCapConeCosinePowerTailBelowHalf_of_capConeCosinePowerTail
    (hTail : sphere_northPoleCapConeCosinePowerTail) :
    sphere_northPoleCapConeCosinePowerTailBelowHalf := by
  intro n hn
  exact
    finRealSphereNorthPoleCapConeCosinePowerTailBelowHalf_of_capConeCosinePowerTail
      n (hTail n)

/-- Normalized surface-measure form of the elementary north-pole cap tail.
This is the standard spherical-cap probability inequality behind the ambient
cone-volume power law. -/
def FinRealSphereNorthPoleClosedHalfspaceCosinePowerTail
    (n : ℕ) [NeZero n] : Prop :=
  ∀ ⦃r : ℝ⦄, 2 ≤ n → 0 < r → r < Real.pi / 2 →
    (finRealSurfaceProbabilityMeasure n).real
        (finRealSphereClosedHalfspace n
          (-(finRealSphereNorthPole n : FinRealEuclideanSpace n))
          (Real.sin r)) ≤
      Real.cos r ^ (n - 1)

/-- No-input package for the normalized surface-measure cap power law. -/
def sphere_northPoleClosedHalfspaceCosinePowerTail : Prop :=
  ∀ (n : ℕ) [NeZero n],
    FinRealSphereNorthPoleClosedHalfspaceCosinePowerTail n

/-- One-dimensional coordinate-law form of the elementary north-pole cap tail.
This removes the set-level spherical halfspace from the active tail leaf. -/
def FinRealSphereNorthPoleCoordinateCosinePowerTail
    (n : ℕ) [NeZero n] : Prop :=
  ∀ ⦃r : ℝ⦄, 2 ≤ n → 0 < r → r < Real.pi / 2 →
    (finRealSphereCoordinateLaw n
      (-(finRealSphereNorthPole n : FinRealEuclideanSpace n))).real
        (Set.Ici (Real.sin r)) ≤
      Real.cos r ^ (n - 1)

/-- No-input package for the north-pole coordinate-law cap power tail. -/
def sphere_northPoleCoordinateCosinePowerTail : Prop :=
  ∀ (n : ℕ) [NeZero n],
    FinRealSphereNorthPoleCoordinateCosinePowerTail n

/-- Nontrivial part of the north-pole coordinate-law power tail.  The omitted
case `1 / 2 ≤ cos(r)^(n-1)` is supplied by antipodal symmetry, which gives the
positive coordinate tail mass at most `1 / 2`. -/
def FinRealSphereNorthPoleCoordinateCosinePowerTailBelowHalf
    (n : ℕ) [NeZero n] : Prop :=
  ∀ ⦃r : ℝ⦄, 2 ≤ n → 0 < r → r < Real.pi / 2 →
    Real.cos r ^ (n - 1) < (1 / 2 : ℝ) →
      (finRealSphereCoordinateLaw n
        (-(finRealSphereNorthPole n : FinRealEuclideanSpace n))).real
          (Set.Ici (Real.sin r)) ≤
        Real.cos r ^ (n - 1)

/-- No-input package for the nontrivial below-half coordinate-law power tail. -/
def sphere_northPoleCoordinateCosinePowerTailBelowHalf : Prop :=
  ∀ (n : ℕ) [NeZero n],
    FinRealSphereNorthPoleCoordinateCosinePowerTailBelowHalf n

/-- Surface halfspace form of the nontrivial below-half north-pole cap power
tail.  This is the same leaf as the coordinate-law version, but stated on the
normalized surface measure of the concrete spherical cap. -/
def FinRealSphereNorthPoleClosedHalfspaceCosinePowerTailBelowHalf
    (n : ℕ) [NeZero n] : Prop :=
  ∀ ⦃r : ℝ⦄, 2 ≤ n → 0 < r → r < Real.pi / 2 →
    Real.cos r ^ (n - 1) < (1 / 2 : ℝ) →
      (finRealSurfaceProbabilityMeasure n).real
          (finRealSphereClosedHalfspace n
            (-(finRealSphereNorthPole n : FinRealEuclideanSpace n))
            (Real.sin r)) ≤
        Real.cos r ^ (n - 1)

/-- No-input package for the surface-halfspace below-half cap power tail. -/
def sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf : Prop :=
  ∀ (n : ℕ) [NeZero n],
    FinRealSphereNorthPoleClosedHalfspaceCosinePowerTailBelowHalf n

/-- The full normalized surface-cap power law supplies its active below-half
restriction. -/
theorem finRealSphereNorthPoleClosedHalfspaceCosinePowerTailBelowHalf_of_closedHalfspaceCosinePowerTail
    (n : ℕ) [NeZero n]
    (hTail : FinRealSphereNorthPoleClosedHalfspaceCosinePowerTail n) :
    FinRealSphereNorthPoleClosedHalfspaceCosinePowerTailBelowHalf n := by
  intro r hn2 hrpos hrlt _hhalf
  exact hTail hn2 hrpos hrlt

/-- No-input adapter from the full normalized surface-cap power law to the
active below-half normalized surface-cap power law. -/
theorem sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf_of_closedHalfspaceCosinePowerTail
    (hTail : sphere_northPoleClosedHalfspaceCosinePowerTail) :
    sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf := by
  intro n hn
  exact
    finRealSphereNorthPoleClosedHalfspaceCosinePowerTailBelowHalf_of_closedHalfspaceCosinePowerTail
      n (hTail n)

/-- The surface halfspace below-half cap tail supplies the coordinate-law
below-half cap tail by the coordinate push-forward formula. -/
theorem finRealSphereNorthPoleCoordinateCosinePowerTailBelowHalf_of_closedHalfspaceCosinePowerTailBelowHalf
    (n : ℕ) [NeZero n]
    (hTail : FinRealSphereNorthPoleClosedHalfspaceCosinePowerTailBelowHalf n) :
    FinRealSphereNorthPoleCoordinateCosinePowerTailBelowHalf n := by
  intro r hn2 hrpos hrlt hhalf
  let e : FinRealEuclideanSpace n :=
    -(finRealSphereNorthPole n : FinRealEuclideanSpace n)
  have hcoord :
      (finRealSphereCoordinateLaw n e).real (Set.Ici (Real.sin r)) =
        (finRealSurfaceProbabilityMeasure n).real
          (finRealSphereClosedHalfspace n e (Real.sin r)) := by
    simpa [e] using
      (sphereClosedHalfspaceMeasure_coordinate_formula n e (Real.sin r)).symm
  rw [hcoord]
  exact hTail hn2 hrpos hrlt hhalf

/-- No-input adapter from the surface-halfspace below-half cap tail to the
coordinate-law below-half cap tail. -/
theorem sphere_northPoleCoordinateCosinePowerTailBelowHalf_of_closedHalfspaceCosinePowerTailBelowHalf
    (hTail : sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf) :
    sphere_northPoleCoordinateCosinePowerTailBelowHalf := by
  intro n hn
  exact
    finRealSphereNorthPoleCoordinateCosinePowerTailBelowHalf_of_closedHalfspaceCosinePowerTailBelowHalf
      n (hTail n)

/-- The coordinate-law below-half cap tail supplies the surface-halfspace
below-half cap tail by the coordinate push-forward formula. -/
theorem finRealSphereNorthPoleClosedHalfspaceCosinePowerTailBelowHalf_of_coordinateCosinePowerTailBelowHalf
    (n : ℕ) [NeZero n]
    (hTail : FinRealSphereNorthPoleCoordinateCosinePowerTailBelowHalf n) :
    FinRealSphereNorthPoleClosedHalfspaceCosinePowerTailBelowHalf n := by
  intro r hn2 hrpos hrlt hhalf
  let e : FinRealEuclideanSpace n :=
    -(finRealSphereNorthPole n : FinRealEuclideanSpace n)
  have hcoord :
      (finRealSurfaceProbabilityMeasure n).real
          (finRealSphereClosedHalfspace n e (Real.sin r)) =
        (finRealSphereCoordinateLaw n e).real (Set.Ici (Real.sin r)) := by
    simpa [e] using
      sphereClosedHalfspaceMeasure_coordinate_formula n e (Real.sin r)
  rw [hcoord]
  exact hTail hn2 hrpos hrlt hhalf

/-- No-input adapter from the coordinate-law below-half cap tail to the
surface-halfspace below-half cap tail. -/
theorem sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf_of_coordinateCosinePowerTailBelowHalf
    (hTail : sphere_northPoleCoordinateCosinePowerTailBelowHalf) :
    sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf := by
  intro n hn
  exact
    finRealSphereNorthPoleClosedHalfspaceCosinePowerTailBelowHalf_of_coordinateCosinePowerTailBelowHalf
      n (hTail n)

/-- The coordinate-law and normalized surface-cap formulations of the active
below-half north-pole tail are equivalent.  This is the exact rewrite bridge
for switching the final hard leaf between a one-dimensional coordinate-law
statement and a geometric cap-measure statement. -/
theorem finRealSphereNorthPoleCoordinateCosinePowerTailBelowHalf_iff_closedHalfspaceCosinePowerTailBelowHalf
    (n : ℕ) [NeZero n] :
    FinRealSphereNorthPoleCoordinateCosinePowerTailBelowHalf n ↔
      FinRealSphereNorthPoleClosedHalfspaceCosinePowerTailBelowHalf n := by
  constructor
  · exact
      finRealSphereNorthPoleClosedHalfspaceCosinePowerTailBelowHalf_of_coordinateCosinePowerTailBelowHalf
        n
  · exact
      finRealSphereNorthPoleCoordinateCosinePowerTailBelowHalf_of_closedHalfspaceCosinePowerTailBelowHalf
        n

/-- No-input equivalence between the coordinate-law and normalized surface-cap
forms of the active below-half north-pole tail. -/
theorem sphere_northPoleCoordinateCosinePowerTailBelowHalf_iff_closedHalfspaceCosinePowerTailBelowHalf :
    sphere_northPoleCoordinateCosinePowerTailBelowHalf ↔
      sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf := by
  constructor
  · exact
      sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf_of_coordinateCosinePowerTailBelowHalf
  · exact
      sphere_northPoleCoordinateCosinePowerTailBelowHalf_of_closedHalfspaceCosinePowerTailBelowHalf

/-- The coordinate-law cap power tail supplies the normalized closed-halfspace
cap power tail by the coordinate push-forward formula. -/
theorem finRealSphereNorthPoleClosedHalfspaceCosinePowerTail_of_coordinateCosinePowerTail
    (n : ℕ) [NeZero n]
    (hTail : FinRealSphereNorthPoleCoordinateCosinePowerTail n) :
    FinRealSphereNorthPoleClosedHalfspaceCosinePowerTail n := by
  intro r hn2 hrpos hrlt
  let e : FinRealEuclideanSpace n :=
    -(finRealSphereNorthPole n : FinRealEuclideanSpace n)
  calc
    (finRealSurfaceProbabilityMeasure n).real
        (finRealSphereClosedHalfspace n
          (-(finRealSphereNorthPole n : FinRealEuclideanSpace n))
          (Real.sin r)) =
      (finRealSphereCoordinateLaw n e).real (Set.Ici (Real.sin r)) := by
        simpa [e] using
          sphereClosedHalfspaceMeasure_coordinate_formula n e (Real.sin r)
    _ ≤ Real.cos r ^ (n - 1) := by
        simpa [e] using hTail hn2 hrpos hrlt

/-- No-input adapter from the north-pole coordinate-law cap power tail to the
normalized closed-halfspace cap power tail. -/
theorem sphere_northPoleClosedHalfspaceCosinePowerTail_of_coordinateCosinePowerTail
    (hTail : sphere_northPoleCoordinateCosinePowerTail) :
    sphere_northPoleClosedHalfspaceCosinePowerTail := by
  intro n hn
  exact
    finRealSphereNorthPoleClosedHalfspaceCosinePowerTail_of_coordinateCosinePowerTail
      n (hTail n)

/-- Scalar comparison used to turn the cap-cone power-law estimate into the
large-exponent Gaussian estimate. -/
theorem real_cos_le_exp_neg_sq_div_two {r : ℝ}
    (h0 : 0 ≤ r) (hlt : r < Real.pi / 2) :
    Real.cos r ≤ Real.exp (-(r ^ 2 / 2)) := by
  let f : ℝ → ℝ := fun x => Real.log (Real.cos x) + x ^ 2 / 2
  have hcos_pos_on : ∀ x ∈ Set.Icc (0 : ℝ) r, 0 < Real.cos x := by
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    have hxlt : x < Real.pi / 2 := lt_of_le_of_lt hx.2 hlt
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith, hxlt⟩
  have hcont : ContinuousOn f (Set.Icc (0 : ℝ) r) := by
    intro x hx
    have hxcos : Real.cos x ≠ 0 := (hcos_pos_on x hx).ne'
    exact
      (((Real.continuous_cos.continuousAt).log hxcos).add
        ((continuousAt_id.pow 2).div_const _)).continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (interior (Set.Icc (0 : ℝ) r)) := by
    intro x hx
    have hxmem : x ∈ Set.Icc (0 : ℝ) r := interior_subset hx
    have hxcos : Real.cos x ≠ 0 := (hcos_pos_on x hxmem).ne'
    exact
      (((Real.differentiableAt_cos).log hxcos).add
        ((differentiableAt_id.pow 2).div_const _)).differentiableWithinAt
  have hderiv_nonpos : ∀ x ∈ interior (Set.Icc (0 : ℝ) r), deriv f x ≤ 0 := by
    intro x hx
    have hxmem : x ∈ Set.Icc (0 : ℝ) r := interior_subset hx
    have hx0 : 0 ≤ x := hxmem.1
    have hxlt : x < Real.pi / 2 := lt_of_le_of_lt hxmem.2 hlt
    have hcospos : 0 < Real.cos x := hcos_pos_on x hxmem
    have hcos_ne : Real.cos x ≠ 0 := hcospos.ne'
    have htan : x ≤ Real.tan x := Real.le_tan hx0 hxlt
    have hraw :=
      (((Real.hasDerivAt_cos x).log hcos_ne).add
        ((hasDerivAt_pow 2 x).div_const (2 : ℝ))).deriv
    have hfraw :
        deriv f x = -Real.sin x / Real.cos x + (2 * x ^ (2 - 1)) / 2 := by
      simpa [f] using hraw
    have hx_le_sin_div : x ≤ Real.sin x / Real.cos x := by
      simpa [Real.tan_eq_sin_div_cos] using htan
    have hsimpl :
        -Real.sin x / Real.cos x + (2 * x ^ (2 - 1)) / 2 =
          x - Real.sin x / Real.cos x := by
      ring_nf
    rw [hfraw, hsimpl]
    linarith
  have hanti : AntitoneOn f (Set.Icc (0 : ℝ) r) :=
    antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) r) hcont hdiff hderiv_nonpos
  have hf_le : f r ≤ f 0 :=
    hanti ⟨le_rfl, h0⟩ ⟨h0, le_rfl⟩ h0
  have hf0 : f 0 = 0 := by
    simp [f]
  have hlog_le : Real.log (Real.cos r) ≤ -(r ^ 2 / 2) := by
    have : Real.log (Real.cos r) + r ^ 2 / 2 ≤ 0 := by
      simpa [f, hf0] using hf_le
    linarith
  have hcos_pos : 0 < Real.cos r := hcos_pos_on r ⟨h0, le_rfl⟩
  exact (Real.log_le_iff_le_exp hcos_pos).mp hlog_le

/-- Power form of the scalar comparison, with the exact exponent used by the
finite real sphere of dimension `n`. -/
theorem real_cos_pow_nat_sub_one_le_exp_neg_mul_sq_div_two
    {n : ℕ} {r : ℝ} (hn2 : 2 ≤ n) (h0 : 0 ≤ r) (hlt : r < Real.pi / 2) :
    Real.cos r ^ (n - 1) ≤
      Real.exp (-((((n : ℝ) - 1) * r ^ 2) / 2)) := by
  have hcos_nonneg : 0 ≤ Real.cos r := by
    exact le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith, hlt⟩)
  have hbase := real_cos_le_exp_neg_sq_div_two (r := r) h0 hlt
  have hpow :
      Real.cos r ^ (n - 1) ≤ Real.exp (-(r ^ 2 / 2)) ^ (n - 1) := by
    exact pow_le_pow_left₀ hcos_nonneg hbase (n - 1)
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    simpa using (Nat.cast_sub (R := ℝ) (by omega : 1 ≤ n))
  calc
    Real.cos r ^ (n - 1) ≤ Real.exp (-(r ^ 2 / 2)) ^ (n - 1) := hpow
    _ = Real.exp (-((((n : ℝ) - 1) * r ^ 2) / 2)) := by
      rw [← Real.exp_nat_mul]
      rw [hcast]
      congr 1
      ring

/-- The geometric cap-cone power law implies the large-exponent Gaussian
cap-cone tail.  This removes the scalar exponential comparison from the
remaining geometric leaf. -/
theorem finRealSphereNorthPoleCapConeGaussianTailLargeExponent_of_cosinePowerTail
    (n : ℕ) [NeZero n]
    (hTail : FinRealSphereNorthPoleCapConeCosinePowerTail n) :
    FinRealSphereNorthPoleCapConeGaussianTailLargeExponent n (n : ℝ) := by
  intro r hn2 hrpos hrlt _hlarge
  let B : ℝ≥0∞ :=
    (finRealHaarMeasure n) (Metric.ball (0 : FinRealEuclideanSpace n) 1)
  have hPower :
      (finRealHaarMeasure n)
          (finRealSphereRadialOpenCone n
            (finRealSphereClosedHalfspace n
              (-(finRealSphereNorthPole n : FinRealEuclideanSpace n))
              (Real.sin r))) ≤
        ENNReal.ofReal (Real.cos r ^ (n - 1)) * B := by
    simpa [B] using hTail hn2 hrpos hrlt
  have hscalar :
      ENNReal.ofReal (Real.cos r ^ (n - 1)) ≤
        ENNReal.ofReal
          (Real.exp (-(((((n : ℕ) : ℝ) - 1) * r ^ 2) / 2))) := by
    exact ENNReal.ofReal_le_ofReal
      (real_cos_pow_nat_sub_one_le_exp_neg_mul_sq_div_two
        (n := n) hn2 hrpos.le hrlt)
  calc
    (finRealHaarMeasure n)
        (finRealSphereRadialOpenCone n
          (finRealSphereClosedHalfspace n
            (-(finRealSphereNorthPole n : FinRealEuclideanSpace n))
            (Real.sin r))) ≤
        ENNReal.ofReal (Real.cos r ^ (n - 1)) * B := hPower
    _ ≤ ENNReal.ofReal
          (Real.exp (-(((((n : ℕ) : ℝ) - 1) * r ^ 2) / 2))) *
        B := mul_le_mul_left hscalar B

/-- No-input adapter from the algebraic cap-cone power law to the Gaussian
large-exponent cap-cone tail. -/
theorem sphere_northPoleCapConeGaussianTailLargeExponent_of_cosinePowerTail
    (hTail : sphere_northPoleCapConeCosinePowerTail) :
    sphere_northPoleCapConeGaussianTailLargeExponent := by
  intro n hn
  exact
    finRealSphereNorthPoleCapConeGaussianTailLargeExponent_of_cosinePowerTail
      n (hTail n)

/-- The below-half cap-cone power law is already enough for the
large-exponent Gaussian cap-cone tail: the large-exponent hypothesis implies
`cos(r)^(n-1) < 1 / 2`, so only the nontrivial below-half range is used. -/
theorem finRealSphereNorthPoleCapConeGaussianTailLargeExponent_of_cosinePowerTailBelowHalf
    (n : ℕ) [NeZero n]
    (hTail : FinRealSphereNorthPoleCapConeCosinePowerTailBelowHalf n) :
    FinRealSphereNorthPoleCapConeGaussianTailLargeExponent n (n : ℝ) := by
  intro r hn2 hrpos hrlt hlarge
  let B : ℝ≥0∞ :=
    (finRealHaarMeasure n) (Metric.ball (0 : FinRealEuclideanSpace n) 1)
  have hscalar_real :
      Real.cos r ^ (n - 1) ≤
        Real.exp (-(((((n : ℕ) : ℝ) - 1) * r ^ 2) / 2)) :=
    real_cos_pow_nat_sub_one_le_exp_neg_mul_sq_div_two
      (n := n) hn2 hrpos.le hrlt
  have hexp_neg_log_two : Real.exp (-(Real.log 2)) = (1 / 2 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hexp_lt_half :
      Real.exp (-(((((n : ℕ) : ℝ) - 1) * r ^ 2) / 2)) < (1 / 2 : ℝ) := by
    have hExp :
        Real.exp (-(((((n : ℕ) : ℝ) - 1) * r ^ 2) / 2)) <
          Real.exp (-(Real.log 2)) :=
      Real.exp_lt_exp.mpr (neg_lt_neg hlarge)
    simpa [hexp_neg_log_two] using hExp
  have hhalf : Real.cos r ^ (n - 1) < (1 / 2 : ℝ) :=
    lt_of_le_of_lt hscalar_real hexp_lt_half
  have hPower :
      (finRealHaarMeasure n)
          (finRealSphereRadialOpenCone n
            (finRealSphereClosedHalfspace n
              (-(finRealSphereNorthPole n : FinRealEuclideanSpace n))
              (Real.sin r))) ≤
        ENNReal.ofReal (Real.cos r ^ (n - 1)) * B := by
    simpa [B] using hTail hn2 hrpos hrlt hhalf
  have hscalar :
      ENNReal.ofReal (Real.cos r ^ (n - 1)) ≤
        ENNReal.ofReal
          (Real.exp (-(((((n : ℕ) : ℝ) - 1) * r ^ 2) / 2))) := by
    exact ENNReal.ofReal_le_ofReal hscalar_real
  calc
    (finRealHaarMeasure n)
        (finRealSphereRadialOpenCone n
          (finRealSphereClosedHalfspace n
            (-(finRealSphereNorthPole n : FinRealEuclideanSpace n))
            (Real.sin r))) ≤
        ENNReal.ofReal (Real.cos r ^ (n - 1)) * B := hPower
    _ ≤ ENNReal.ofReal
          (Real.exp (-(((((n : ℕ) : ℝ) - 1) * r ^ 2) / 2))) *
        B := mul_le_mul_left hscalar B

/-- No-input adapter from the below-half algebraic cap-cone power law to the
Gaussian large-exponent cap-cone tail. -/
theorem sphere_northPoleCapConeGaussianTailLargeExponent_of_cosinePowerTailBelowHalf
    (hTail : sphere_northPoleCapConeCosinePowerTailBelowHalf) :
    sphere_northPoleCapConeGaussianTailLargeExponent := by
  intro n hn
  exact
    finRealSphereNorthPoleCapConeGaussianTailLargeExponent_of_cosinePowerTailBelowHalf
      n (hTail n)

/-- The normalized surface cap power law supplies the ambient cap-cone power
law by the surface/cone formula.  Thus the remaining geometric tail can be
attacked as the standard spherical-cap probability estimate. -/
theorem finRealSphereNorthPoleCapConeCosinePowerTail_of_closedHalfspaceCosinePowerTail
    (n : ℕ) [NeZero n]
    (hTail : FinRealSphereNorthPoleClosedHalfspaceCosinePowerTail n) :
    FinRealSphereNorthPoleCapConeCosinePowerTail n := by
  intro r hn2 hrpos hrlt
  let e : FinRealEuclideanSpace n :=
    -(finRealSphereNorthPole n : FinRealEuclideanSpace n)
  let S : Set (FinRealSphere n) := finRealSphereClosedHalfspace n e (Real.sin r)
  let μ := finRealSurfaceProbabilityMeasure n
  let B : ℝ≥0∞ :=
    (finRealHaarMeasure n) (Metric.ball (0 : FinRealEuclideanSpace n) 1)
  haveI : (finRealHaarMeasure n).IsAddHaarMeasure := by
    unfold finRealHaarMeasure
    infer_instance
  have hS : MeasurableSet S :=
    measurableSet_finRealSphereClosedHalfspace n e (Real.sin r)
  have hcone_eq :
      μ S * B = (finRealHaarMeasure n) (finRealSphereRadialOpenCone n S) := by
    simpa [μ, B, S] using
      finRealSurfaceProbabilityMeasure_eq_cone_ratio (n := n) hS
  have hμ_real : μ.real S ≤ Real.cos r ^ (n - 1) := by
    simpa [μ, S, e] using hTail hn2 hrpos hrlt
  have hμ_fin : μ S ≠ ⊤ := by
    haveI : IsFiniteMeasure μ := by
      unfold μ finRealSurfaceProbabilityMeasure
      infer_instance
    exact (measure_lt_top μ S).ne
  have hcos_nonneg : 0 ≤ Real.cos r ^ (n - 1) := by
    exact pow_nonneg (le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith, hrlt⟩)) _
  have hμ_enn :
      μ S ≤ ENNReal.ofReal (Real.cos r ^ (n - 1)) := by
    rw [ENNReal.le_ofReal_iff_toReal_le hμ_fin hcos_nonneg]
    simpa [measureReal_def] using hμ_real
  calc
    (finRealHaarMeasure n) (finRealSphereRadialOpenCone n S) = μ S * B :=
      hcone_eq.symm
    _ ≤ ENNReal.ofReal (Real.cos r ^ (n - 1)) * B :=
      mul_le_mul_left hμ_enn B

/-- No-input adapter from the normalized surface cap power law to the ambient
cap-cone power law. -/
theorem sphere_northPoleCapConeCosinePowerTail_of_closedHalfspaceCosinePowerTail
    (hTail : sphere_northPoleClosedHalfspaceCosinePowerTail) :
    sphere_northPoleCapConeCosinePowerTail := by
  intro n hn
  exact
    finRealSphereNorthPoleCapConeCosinePowerTail_of_closedHalfspaceCosinePowerTail
      n (hTail n)

/-- The normalized below-half surface cap power law supplies the ambient
below-half cap-cone power law by the surface/cone formula. -/
theorem finRealSphereNorthPoleCapConeCosinePowerTailBelowHalf_of_closedHalfspaceCosinePowerTailBelowHalf
    (n : ℕ) [NeZero n]
    (hTail : FinRealSphereNorthPoleClosedHalfspaceCosinePowerTailBelowHalf n) :
    FinRealSphereNorthPoleCapConeCosinePowerTailBelowHalf n := by
  intro r hn2 hrpos hrlt hhalf
  let e : FinRealEuclideanSpace n :=
    -(finRealSphereNorthPole n : FinRealEuclideanSpace n)
  let S : Set (FinRealSphere n) := finRealSphereClosedHalfspace n e (Real.sin r)
  let μ := finRealSurfaceProbabilityMeasure n
  let B : ℝ≥0∞ :=
    (finRealHaarMeasure n) (Metric.ball (0 : FinRealEuclideanSpace n) 1)
  haveI : (finRealHaarMeasure n).IsAddHaarMeasure := by
    unfold finRealHaarMeasure
    infer_instance
  have hS : MeasurableSet S :=
    measurableSet_finRealSphereClosedHalfspace n e (Real.sin r)
  have hcone_eq :
      μ S * B = (finRealHaarMeasure n) (finRealSphereRadialOpenCone n S) := by
    simpa [μ, B, S] using
      finRealSurfaceProbabilityMeasure_eq_cone_ratio (n := n) hS
  have hμ_real : μ.real S ≤ Real.cos r ^ (n - 1) := by
    simpa [μ, S, e] using hTail hn2 hrpos hrlt hhalf
  have hμ_fin : μ S ≠ ⊤ := by
    haveI : IsFiniteMeasure μ := by
      unfold μ finRealSurfaceProbabilityMeasure
      infer_instance
    exact (measure_lt_top μ S).ne
  have hcos_nonneg : 0 ≤ Real.cos r ^ (n - 1) := by
    exact pow_nonneg (le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith, hrlt⟩)) _
  have hμ_enn :
      μ S ≤ ENNReal.ofReal (Real.cos r ^ (n - 1)) := by
    rw [ENNReal.le_ofReal_iff_toReal_le hμ_fin hcos_nonneg]
    simpa [measureReal_def] using hμ_real
  calc
    (finRealHaarMeasure n) (finRealSphereRadialOpenCone n S) = μ S * B :=
      hcone_eq.symm
    _ ≤ ENNReal.ofReal (Real.cos r ^ (n - 1)) * B :=
      mul_le_mul_left hμ_enn B

/-- No-input adapter from the normalized below-half surface cap power law to
the ambient below-half cap-cone power law. -/
theorem sphere_northPoleCapConeCosinePowerTailBelowHalf_of_closedHalfspaceCosinePowerTailBelowHalf
    (hTail : sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf) :
    sphere_northPoleCapConeCosinePowerTailBelowHalf := by
  intro n hn
  exact
    finRealSphereNorthPoleCapConeCosinePowerTailBelowHalf_of_closedHalfspaceCosinePowerTailBelowHalf
      n (hTail n)

/-- The normalized below-half surface cap power law supplies the direct
large-exponent Gaussian cap-cone package. -/
theorem sphere_northPoleCapConeGaussianTailLargeExponent_of_closedHalfspaceCosinePowerTailBelowHalf
    (hTail : sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf) :
    sphere_northPoleCapConeGaussianTailLargeExponent :=
  sphere_northPoleCapConeGaussianTailLargeExponent_of_cosinePowerTailBelowHalf
    (sphere_northPoleCapConeCosinePowerTailBelowHalf_of_closedHalfspaceCosinePowerTailBelowHalf
      hTail)

/-- The ambient cap-cone power law supplies the normalized surface cap power
law by dividing through the positive finite unit-ball volume in the `toSphere`
cone formula. -/
theorem finRealSphereNorthPoleClosedHalfspaceCosinePowerTail_of_capConeCosinePowerTail
    (n : ℕ) [NeZero n]
    (hCone : FinRealSphereNorthPoleCapConeCosinePowerTail n) :
    FinRealSphereNorthPoleClosedHalfspaceCosinePowerTail n := by
  intro r hn2 hrpos hrlt
  let e : FinRealEuclideanSpace n :=
    -(finRealSphereNorthPole n : FinRealEuclideanSpace n)
  let S : Set (FinRealSphere n) := finRealSphereClosedHalfspace n e (Real.sin r)
  let μ := finRealSurfaceProbabilityMeasure n
  let B : ℝ≥0∞ :=
    (finRealHaarMeasure n) (Metric.ball (0 : FinRealEuclideanSpace n) 1)
  haveI : (finRealHaarMeasure n).IsAddHaarMeasure := by
    unfold finRealHaarMeasure
    infer_instance
  have hS : MeasurableSet S :=
    measurableSet_finRealSphereClosedHalfspace n e (Real.sin r)
  have hcone_eq :
      μ S * B = (finRealHaarMeasure n) (finRealSphereRadialOpenCone n S) := by
    simpa [μ, B, S] using
      finRealSurfaceProbabilityMeasure_eq_cone_ratio (n := n) hS
  have hB_ne_zero : B ≠ 0 := by
    haveI : (finRealHaarMeasure n).IsOpenPosMeasure := by
      unfold finRealHaarMeasure
      infer_instance
    exact Metric.isOpen_ball.measure_ne_zero _ ⟨0, by simp⟩
  have hB_ne_top : B ≠ ⊤ := by
    have hball_lt_top : B < ⊤ := by
      exact lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
        ((isCompact_closedBall (0 : FinRealEuclideanSpace n) 1).measure_lt_top)
    exact hball_lt_top.ne
  have hConeBound :
      (finRealHaarMeasure n) (finRealSphereRadialOpenCone n S) ≤
        ENNReal.ofReal (Real.cos r ^ (n - 1)) * B := by
    simpa [S, e, B] using hCone hn2 hrpos hrlt
  have hmu_enn :
      μ S ≤ ENNReal.ofReal (Real.cos r ^ (n - 1)) := by
    exact (ENNReal.mul_le_mul_iff_left hB_ne_zero hB_ne_top).mp (by
      calc
        μ S * B =
            (finRealHaarMeasure n) (finRealSphereRadialOpenCone n S) := hcone_eq
        _ ≤ ENNReal.ofReal (Real.cos r ^ (n - 1)) * B := hConeBound)
  have hμ_fin : μ S ≠ ⊤ := by
    haveI : IsFiniteMeasure μ := by
      unfold μ finRealSurfaceProbabilityMeasure
      infer_instance
    exact (measure_lt_top μ S).ne
  have hcos_nonneg : 0 ≤ Real.cos r ^ (n - 1) := by
    exact pow_nonneg (le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith, hrlt⟩)) _
  have hreal : μ.real S ≤ Real.cos r ^ (n - 1) := by
    rw [measureReal_def]
    have h :=
      (ENNReal.toReal_le_toReal hμ_fin ENNReal.ofReal_ne_top).mpr hmu_enn
    simpa [ENNReal.toReal_ofReal hcos_nonneg] using h
  exact by
    simpa [μ, S, e] using hreal

/-- No-input adapter from the ambient cap-cone power law to the normalized
surface cap power law. -/
theorem sphere_northPoleClosedHalfspaceCosinePowerTail_of_capConeCosinePowerTail
    (hCone : sphere_northPoleCapConeCosinePowerTail) :
    sphere_northPoleClosedHalfspaceCosinePowerTail := by
  intro n hn
  exact
    finRealSphereNorthPoleClosedHalfspaceCosinePowerTail_of_capConeCosinePowerTail
      n (hCone n)

/-- The ambient cap-cone power law also supplies the active below-half
surface-cap tail by restriction to the below-half range. -/
theorem sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf_of_capConeCosinePowerTail
    (hCone : sphere_northPoleCapConeCosinePowerTail) :
    sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf := by
  intro n hn r hn2 hrpos hrlt _hhalf
  exact
    (sphere_northPoleClosedHalfspaceCosinePowerTail_of_capConeCosinePowerTail hCone
      n) hn2 hrpos hrlt

/-- The below-half ambient cap-cone power law supplies exactly the active
below-half normalized surface cap tail by the same cone/surface division. -/
theorem finRealSphereNorthPoleClosedHalfspaceCosinePowerTailBelowHalf_of_capConeCosinePowerTailBelowHalf
    (n : ℕ) [NeZero n]
    (hCone : FinRealSphereNorthPoleCapConeCosinePowerTailBelowHalf n) :
    FinRealSphereNorthPoleClosedHalfspaceCosinePowerTailBelowHalf n := by
  intro r hn2 hrpos hrlt hhalf
  let e : FinRealEuclideanSpace n :=
    -(finRealSphereNorthPole n : FinRealEuclideanSpace n)
  let S : Set (FinRealSphere n) := finRealSphereClosedHalfspace n e (Real.sin r)
  let μ := finRealSurfaceProbabilityMeasure n
  let B : ℝ≥0∞ :=
    (finRealHaarMeasure n) (Metric.ball (0 : FinRealEuclideanSpace n) 1)
  haveI : (finRealHaarMeasure n).IsAddHaarMeasure := by
    unfold finRealHaarMeasure
    infer_instance
  have hS : MeasurableSet S :=
    measurableSet_finRealSphereClosedHalfspace n e (Real.sin r)
  have hcone_eq :
      μ S * B = (finRealHaarMeasure n) (finRealSphereRadialOpenCone n S) := by
    simpa [μ, B, S] using
      finRealSurfaceProbabilityMeasure_eq_cone_ratio (n := n) hS
  have hB_ne_zero : B ≠ 0 := by
    haveI : (finRealHaarMeasure n).IsOpenPosMeasure := by
      unfold finRealHaarMeasure
      infer_instance
    exact Metric.isOpen_ball.measure_ne_zero _ ⟨0, by simp⟩
  have hB_ne_top : B ≠ ⊤ := by
    have hball_lt_top : B < ⊤ := by
      exact lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
        ((isCompact_closedBall (0 : FinRealEuclideanSpace n) 1).measure_lt_top)
    exact hball_lt_top.ne
  have hConeBound :
      (finRealHaarMeasure n) (finRealSphereRadialOpenCone n S) ≤
        ENNReal.ofReal (Real.cos r ^ (n - 1)) * B := by
    simpa [S, e, B] using hCone hn2 hrpos hrlt hhalf
  have hmu_enn :
      μ S ≤ ENNReal.ofReal (Real.cos r ^ (n - 1)) := by
    exact (ENNReal.mul_le_mul_iff_left hB_ne_zero hB_ne_top).mp (by
      calc
        μ S * B =
            (finRealHaarMeasure n) (finRealSphereRadialOpenCone n S) := hcone_eq
        _ ≤ ENNReal.ofReal (Real.cos r ^ (n - 1)) * B := hConeBound)
  have hμ_fin : μ S ≠ ⊤ := by
    haveI : IsFiniteMeasure μ := by
      unfold μ finRealSurfaceProbabilityMeasure
      infer_instance
    exact (measure_lt_top μ S).ne
  have hcos_nonneg : 0 ≤ Real.cos r ^ (n - 1) := by
    exact pow_nonneg (le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith, hrlt⟩)) _
  have hreal : μ.real S ≤ Real.cos r ^ (n - 1) := by
    rw [measureReal_def]
    have h :=
      (ENNReal.toReal_le_toReal hμ_fin ENNReal.ofReal_ne_top).mpr hmu_enn
    simpa [ENNReal.toReal_ofReal hcos_nonneg] using h
  exact by
    simpa [μ, S, e] using hreal

/-- No-input adapter from the below-half ambient cap-cone power law to the
active below-half normalized surface cap tail. -/
theorem sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf_of_capConeCosinePowerTailBelowHalf
    (hCone : sphere_northPoleCapConeCosinePowerTailBelowHalf) :
    sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf := by
  intro n hn
  exact
    finRealSphereNorthPoleClosedHalfspaceCosinePowerTailBelowHalf_of_capConeCosinePowerTailBelowHalf
      n (hCone n)

/-- The normalized surface-cap and ambient cap-cone formulations of the active
below-half north-pole tail are equivalent.  This records that the `toSphere`
cone formula loses no strength for the remaining cap estimate. -/
theorem finRealSphereNorthPoleClosedHalfspaceCosinePowerTailBelowHalf_iff_capConeCosinePowerTailBelowHalf
    (n : ℕ) [NeZero n] :
    FinRealSphereNorthPoleClosedHalfspaceCosinePowerTailBelowHalf n ↔
      FinRealSphereNorthPoleCapConeCosinePowerTailBelowHalf n := by
  constructor
  · exact
      finRealSphereNorthPoleCapConeCosinePowerTailBelowHalf_of_closedHalfspaceCosinePowerTailBelowHalf
        n
  · exact
      finRealSphereNorthPoleClosedHalfspaceCosinePowerTailBelowHalf_of_capConeCosinePowerTailBelowHalf
        n

/-- No-input equivalence between the normalized surface-cap and ambient
cap-cone forms of the active below-half north-pole tail. -/
theorem sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf_iff_capConeCosinePowerTailBelowHalf :
    sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf ↔
      sphere_northPoleCapConeCosinePowerTailBelowHalf := by
  constructor
  · exact
      sphere_northPoleCapConeCosinePowerTailBelowHalf_of_closedHalfspaceCosinePowerTailBelowHalf
  · exact
      sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf_of_capConeCosinePowerTailBelowHalf

/-- The coordinate-law and ambient cap-cone formulations of the active
below-half north-pole tail are equivalent.  This is the direct composed bridge
from the endpoint-visible coordinate tail to the open-cone volume proof
target. -/
theorem finRealSphereNorthPoleCoordinateCosinePowerTailBelowHalf_iff_capConeCosinePowerTailBelowHalf
    (n : ℕ) [NeZero n] :
    FinRealSphereNorthPoleCoordinateCosinePowerTailBelowHalf n ↔
      FinRealSphereNorthPoleCapConeCosinePowerTailBelowHalf n := by
  constructor
  · intro hTail
    exact
      finRealSphereNorthPoleCapConeCosinePowerTailBelowHalf_of_closedHalfspaceCosinePowerTailBelowHalf
        n
        (finRealSphereNorthPoleClosedHalfspaceCosinePowerTailBelowHalf_of_coordinateCosinePowerTailBelowHalf
          n hTail)
  · intro hCone
    exact
      finRealSphereNorthPoleCoordinateCosinePowerTailBelowHalf_of_closedHalfspaceCosinePowerTailBelowHalf
        n
        (finRealSphereNorthPoleClosedHalfspaceCosinePowerTailBelowHalf_of_capConeCosinePowerTailBelowHalf
          n hCone)

/-- No-input equivalence between the endpoint-visible coordinate-law tail and
the ambient open-cone volume form of the active below-half north-pole tail. -/
theorem sphere_northPoleCoordinateCosinePowerTailBelowHalf_iff_capConeCosinePowerTailBelowHalf :
    sphere_northPoleCoordinateCosinePowerTailBelowHalf ↔
      sphere_northPoleCapConeCosinePowerTailBelowHalf := by
  constructor
  · intro hTail
    exact
      sphere_northPoleCapConeCosinePowerTailBelowHalf_of_closedHalfspaceCosinePowerTailBelowHalf
        (sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf_of_coordinateCosinePowerTailBelowHalf
          hTail)
  · intro hCone
    exact
      sphere_northPoleCoordinateCosinePowerTailBelowHalf_of_closedHalfspaceCosinePowerTailBelowHalf
        (sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf_of_capConeCosinePowerTailBelowHalf
          hCone)

/-- Surface halfspace form of the remaining north-pole large-exponent
coordinate-tail estimate.  This is the same scalar tail as the coordinate-law
package, but stated directly for the normalized surface measure. -/
def FinRealSphereNorthPoleClosedHalfspaceGaussianTailLargeExponent
    (n : ℕ) [NeZero n] (realDim : ℝ) : Prop :=
  ∀ ⦃r : ℝ⦄, 2 ≤ n → 0 < r → r < Real.pi / 2 →
    Real.log 2 < ((realDim - 1) * r ^ 2) / 2 →
    (finRealSurfaceProbabilityMeasure n).real
        (finRealSphereClosedHalfspace n
          (-(finRealSphereNorthPole n : FinRealEuclideanSpace n))
          (Real.sin r)) ≤
      Real.exp (-(((realDim - 1) * r ^ 2) / 2))

/-- No-input package for the surface halfspace north-pole coordinate tail. -/
def sphere_northPoleClosedHalfspaceGaussianTailLargeExponent : Prop :=
  ∀ (n : ℕ) [NeZero n],
    FinRealSphereNorthPoleClosedHalfspaceGaussianTailLargeExponent n (n : ℝ)

/-- Radial projection from the ambient space back to the real sphere, with a
chosen fallback value at the origin.  On the open cones used below the origin is
absent, so the fallback is only a totalization device. -/
noncomputable def finRealSphereRadialDirectionFrom
    {n : ℕ} (u : FinRealSphere n) (z : FinRealEuclideanSpace n) :
    FinRealSphere n :=
  if hz : z = 0 then u else
    ⟨‖z‖⁻¹ • z, by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul]
      have hnorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm_pos),
        inv_mul_cancel₀ hnorm_pos.ne']⟩

@[simp]
theorem finRealSphereRadialDirectionFrom_smul
    {n : ℕ} (u x : FinRealSphere n) {r : ℝ} (hr : 0 < r) :
    finRealSphereRadialDirectionFrom u
        (r • (x : FinRealEuclideanSpace n)) = x := by
  apply Subtype.ext
  unfold finRealSphereRadialDirectionFrom
  have hz : r • (x : FinRealEuclideanSpace n) ≠ 0 := by
    exact smul_ne_zero hr.ne' (finRealSphere_ne_zero n x)
  rw [dif_neg hz]
  change
    (‖r • (x : FinRealEuclideanSpace n)‖)⁻¹ •
        (r • (x : FinRealEuclideanSpace n)) =
      (x : FinRealEuclideanSpace n)
  rw [norm_smul, finRealSphere_norm_coe n x, Real.norm_eq_abs, abs_of_pos hr]
  simp [hr.ne']

/-- Function-level cone bridge still needed for leaf 3.  It upgrades the
set-level cone-volume identity to arbitrary nonnegative measurable angular
integrands by pulling them back along radial projection. -/
def FinRealSurfaceProbabilityMeasureLIntegralConeBridge (n : ℕ) : Prop :=
  ∀ (u : FinRealSphere n) ⦃S : Set (FinRealSphere n)⦄,
    MeasurableSet S →
      ∀ F : FinRealSphere n → ℝ≥0∞,
        Measurable F →
          (∫⁻ x in S, F x ∂(finRealSurfaceProbabilityMeasure n)) =
            (finRealHaarMeasure n
                (Metric.ball (0 : FinRealEuclideanSpace n) 1))⁻¹ *
              ∫⁻ z in finRealSphereRadialOpenCone n S,
                F (finRealSphereRadialDirectionFrom u z)
                ∂(finRealHaarMeasure n)

/-- Indicator lintegral form of `finRealSurfaceProbabilityMeasure_eq_cone_ratio`. -/
theorem lintegral_indicator_finRealSurfaceProbabilityMeasure_eq_cone
    {n : ℕ} [NeZero n] {S : Set (FinRealSphere n)} (hS : MeasurableSet S) :
    (∫⁻ _ in S, (1 : ℝ≥0∞) ∂(finRealSurfaceProbabilityMeasure n)) =
      (finRealHaarMeasure n (Metric.ball (0 : FinRealEuclideanSpace n) 1))⁻¹ *
        ∫⁻ _ in finRealSphereRadialOpenCone n S, (1 : ℝ≥0∞)
          ∂(finRealHaarMeasure n) := by
  haveI : (finRealHaarMeasure n).IsAddHaarMeasure := by
    unfold finRealHaarMeasure; infer_instance
  have hball_ne :
      (finRealHaarMeasure n) (Metric.ball (0 : FinRealEuclideanSpace n) 1) ≠ 0 := by
    haveI : (finRealHaarMeasure n).IsOpenPosMeasure := by
      unfold finRealHaarMeasure; infer_instance
    have hopen : IsOpen (Metric.ball (0 : FinRealEuclideanSpace n) 1) :=
      Metric.isOpen_ball
    exact hopen.measure_ne_zero _ ⟨0, by simp⟩
  have hball_top :
      (finRealHaarMeasure n) (Metric.ball (0 : FinRealEuclideanSpace n) 1) ≠ ∞ := by
    have hball_lt_top :
        (finRealHaarMeasure n) (Metric.ball (0 : FinRealEuclideanSpace n) 1) < ∞ :=
      lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
        ((isCompact_closedBall (0 : FinRealEuclideanSpace n) 1).measure_lt_top)
    exact hball_lt_top.ne
  rw [setLIntegral_one, setLIntegral_one, eq_comm]
  have hcone := finRealSurfaceProbabilityMeasure_eq_cone_ratio hS
  unfold finRealSphereRadialOpenCone at hcone ⊢
  rw [← hcone, mul_comm, mul_assoc, ENNReal.mul_inv_cancel hball_ne hball_top]
  simp

/-- The ambient cone-volume tail supplies the north-pole spherical coordinate
tail by the `toSphere` cone formula. -/
theorem finRealSphereCoordinateGaussianTailInteriorLargeExponentNorthPole_of_coneTail
    (n : ℕ) [NeZero n]
    (hCone :
      FinRealSphereNorthPoleCapConeGaussianTailLargeExponent n (n : ℝ)) :
    FinRealSphereCoordinateGaussianTailInteriorLargeExponentNorthPole n (n : ℝ) := by
  intro r hn2 hrpos hrlt hlarge
  let e : FinRealEuclideanSpace n :=
    -(finRealSphereNorthPole n : FinRealEuclideanSpace n)
  let S : Set (FinRealSphere n) := finRealSphereClosedHalfspace n e (Real.sin r)
  let μ := finRealSurfaceProbabilityMeasure n
  let B : ℝ≥0∞ :=
    (finRealHaarMeasure n) (Metric.ball (0 : FinRealEuclideanSpace n) 1)
  haveI : (finRealHaarMeasure n).IsAddHaarMeasure := by
    unfold finRealHaarMeasure
    infer_instance
  have hS : MeasurableSet S :=
    measurableSet_finRealSphereClosedHalfspace n e (Real.sin r)
  have hcone_eq :
      μ S * B = (finRealHaarMeasure n) (finRealSphereRadialOpenCone n S) := by
    simpa [μ, B, S] using
      finRealSurfaceProbabilityMeasure_eq_cone_ratio (n := n) hS
  have hB_ne_zero : B ≠ 0 := by
    haveI : (finRealHaarMeasure n).IsOpenPosMeasure := by
      unfold finRealHaarMeasure
      infer_instance
    exact Metric.isOpen_ball.measure_ne_zero _ ⟨0, by simp⟩
  have hB_ne_top : B ≠ ⊤ := by
    have hball_lt_top : B < ⊤ := by
      exact lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
        ((isCompact_closedBall (0 : FinRealEuclideanSpace n) 1).measure_lt_top)
    exact hball_lt_top.ne
  have hConeBound :
      (finRealHaarMeasure n) (finRealSphereRadialOpenCone n S) ≤
        ENNReal.ofReal (Real.exp (-(((((n : ℕ) : ℝ) - 1) * r ^ 2) / 2))) *
          B := by
    simpa [S, e, B] using hCone hn2 hrpos hrlt hlarge
  have hmu_enn :
      μ S ≤ ENNReal.ofReal
        (Real.exp (-(((((n : ℕ) : ℝ) - 1) * r ^ 2) / 2))) := by
    exact (ENNReal.mul_le_mul_iff_left hB_ne_zero hB_ne_top).mp (by
      calc
        μ S * B =
            (finRealHaarMeasure n) (finRealSphereRadialOpenCone n S) := hcone_eq
        _ ≤ ENNReal.ofReal
              (Real.exp (-(((((n : ℕ) : ℝ) - 1) * r ^ 2) / 2))) *
              B := hConeBound)
  have hμ_fin : μ S ≠ ⊤ := by
    haveI : IsFiniteMeasure μ := by
      unfold μ finRealSurfaceProbabilityMeasure
      infer_instance
    exact (measure_lt_top μ S).ne
  have hreal :
      μ.real S ≤ Real.exp (-(((((n : ℕ) : ℝ) - 1) * r ^ 2) / 2)) := by
    rw [measureReal_def]
    have h :=
      (ENNReal.toReal_le_toReal hμ_fin ENNReal.ofReal_ne_top).mpr hmu_enn
    simpa [ENNReal.toReal_ofReal (Real.exp_nonneg _)] using h
  have hcoord :
      (finRealSphereCoordinateLaw n
          (-(finRealSphereNorthPole n : FinRealEuclideanSpace n))).real
          (Set.Ici (Real.sin r)) =
        μ.real S := by
    simpa [μ, S, e] using
      (sphereClosedHalfspaceMeasure_coordinate_formula n e (Real.sin r)).symm
  rw [hcoord]
  exact hreal

/-- No-input adapter from the ambient cone-volume north-pole tail to the
north-pole spherical coordinate-tail package. -/
theorem sphere_coordinateGaussianTailInteriorLargeExponentNorthPole_of_coneTail
    (hCone : sphere_northPoleCapConeGaussianTailLargeExponent) :
    sphere_coordinateGaussianTailInteriorLargeExponentNorthPole := by
  intro n hn
  exact
    finRealSphereCoordinateGaussianTailInteriorLargeExponentNorthPole_of_coneTail
      n (hCone n)

/-- The ambient cone-volume north-pole tail supplies the normalized surface
closed-halfspace north-pole tail by the `toSphere` cone formula. -/
theorem finRealSphereNorthPoleClosedHalfspaceGaussianTailLargeExponent_of_coneTail
    (n : ℕ) [NeZero n]
    (hCone :
      FinRealSphereNorthPoleCapConeGaussianTailLargeExponent n (n : ℝ)) :
    FinRealSphereNorthPoleClosedHalfspaceGaussianTailLargeExponent n (n : ℝ) := by
  intro r hn2 hrpos hrlt hlarge
  let e : FinRealEuclideanSpace n :=
    -(finRealSphereNorthPole n : FinRealEuclideanSpace n)
  let S : Set (FinRealSphere n) := finRealSphereClosedHalfspace n e (Real.sin r)
  let μ := finRealSurfaceProbabilityMeasure n
  let B : ℝ≥0∞ :=
    (finRealHaarMeasure n) (Metric.ball (0 : FinRealEuclideanSpace n) 1)
  haveI : (finRealHaarMeasure n).IsAddHaarMeasure := by
    unfold finRealHaarMeasure
    infer_instance
  have hS : MeasurableSet S :=
    measurableSet_finRealSphereClosedHalfspace n e (Real.sin r)
  have hcone_eq :
      μ S * B = (finRealHaarMeasure n) (finRealSphereRadialOpenCone n S) := by
    simpa [μ, B, S] using
      finRealSurfaceProbabilityMeasure_eq_cone_ratio (n := n) hS
  have hB_ne_zero : B ≠ 0 := by
    haveI : (finRealHaarMeasure n).IsOpenPosMeasure := by
      unfold finRealHaarMeasure
      infer_instance
    exact Metric.isOpen_ball.measure_ne_zero _ ⟨0, by simp⟩
  have hB_ne_top : B ≠ ⊤ := by
    have hball_lt_top : B < ⊤ := by
      exact lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
        ((isCompact_closedBall (0 : FinRealEuclideanSpace n) 1).measure_lt_top)
    exact hball_lt_top.ne
  have hConeBound :
      (finRealHaarMeasure n) (finRealSphereRadialOpenCone n S) ≤
        ENNReal.ofReal (Real.exp (-(((((n : ℕ) : ℝ) - 1) * r ^ 2) / 2))) *
          B := by
    simpa [S, e, B] using hCone hn2 hrpos hrlt hlarge
  have hmu_enn :
      μ S ≤ ENNReal.ofReal
        (Real.exp (-(((((n : ℕ) : ℝ) - 1) * r ^ 2) / 2))) := by
    exact (ENNReal.mul_le_mul_iff_left hB_ne_zero hB_ne_top).mp (by
      calc
        μ S * B =
            (finRealHaarMeasure n) (finRealSphereRadialOpenCone n S) := hcone_eq
        _ ≤ ENNReal.ofReal
              (Real.exp (-(((((n : ℕ) : ℝ) - 1) * r ^ 2) / 2))) *
              B := hConeBound)
  have hμ_fin : μ S ≠ ⊤ := by
    haveI : IsFiniteMeasure μ := by
      unfold μ finRealSurfaceProbabilityMeasure
      infer_instance
    exact (measure_lt_top μ S).ne
  have hreal :
      μ.real S ≤ Real.exp (-(((((n : ℕ) : ℝ) - 1) * r ^ 2) / 2)) := by
    rw [measureReal_def]
    have h :=
      (ENNReal.toReal_le_toReal hμ_fin ENNReal.ofReal_ne_top).mpr hmu_enn
    simpa [ENNReal.toReal_ofReal (Real.exp_nonneg _)] using h
  exact hreal

/-- No-input adapter from the ambient cone-volume north-pole tail to the
normalized surface closed-halfspace north-pole tail. -/
theorem sphere_northPoleClosedHalfspaceGaussianTailLargeExponent_of_coneTail
    (hCone : sphere_northPoleCapConeGaussianTailLargeExponent) :
    sphere_northPoleClosedHalfspaceGaussianTailLargeExponent := by
  intro n hn
  exact
    finRealSphereNorthPoleClosedHalfspaceGaussianTailLargeExponent_of_coneTail
      n (hCone n)

/-- The surface halfspace north-pole tail is definitionally the same estimate
as the north-pole coordinate-law tail, via the coordinate push-forward formula. -/
theorem finRealSphereCoordinateGaussianTailInteriorLargeExponentNorthPole_of_closedHalfspaceTail
    (n : ℕ) [NeZero n]
    (hTail :
      FinRealSphereNorthPoleClosedHalfspaceGaussianTailLargeExponent n (n : ℝ)) :
    FinRealSphereCoordinateGaussianTailInteriorLargeExponentNorthPole n (n : ℝ) := by
  intro r hn2 hrpos hrlt hlarge
  let e : FinRealEuclideanSpace n :=
    -(finRealSphereNorthPole n : FinRealEuclideanSpace n)
  have hcoord :
      (finRealSphereCoordinateLaw n e).real (Set.Ici (Real.sin r)) =
        (finRealSurfaceProbabilityMeasure n).real
          (finRealSphereClosedHalfspace n e (Real.sin r)) := by
    simpa [e] using
      (sphereClosedHalfspaceMeasure_coordinate_formula n e (Real.sin r)).symm
  rw [hcoord]
  exact hTail hn2 hrpos hrlt hlarge

/-- No-input adapter from the surface halfspace north-pole tail to the
north-pole spherical coordinate-tail package. -/
theorem sphere_coordinateGaussianTailInteriorLargeExponentNorthPole_of_closedHalfspaceTail
    (hTail : sphere_northPoleClosedHalfspaceGaussianTailLargeExponent) :
    sphere_coordinateGaussianTailInteriorLargeExponentNorthPole := by
  intro n hn
  exact
    finRealSphereCoordinateGaussianTailInteriorLargeExponentNorthPole_of_closedHalfspaceTail
      n (hTail n)

/-- The nontrivial below-half north-pole coordinate power tail supplies the
north-pole coordinate Gaussian tail in the large-exponent range.

The large-exponent hypothesis implies `cos(r)^(n-1) < 1 / 2`, so the
below-half coordinate power-law estimate applies.  The scalar comparison
`cos r ≤ exp(-r^2/2)` then gives the Gaussian exponent. -/
theorem finRealSphereCoordinateGaussianTailInteriorLargeExponentNorthPole_of_coordinateCosinePowerTailBelowHalf
    (n : ℕ) [NeZero n]
    (hTail : FinRealSphereNorthPoleCoordinateCosinePowerTailBelowHalf n) :
    FinRealSphereCoordinateGaussianTailInteriorLargeExponentNorthPole n (n : ℝ) := by
  intro r hn2 hrpos hrlt hlarge
  have hscalar_real :
      Real.cos r ^ (n - 1) ≤
        Real.exp (-(((((n : ℕ) : ℝ) - 1) * r ^ 2) / 2)) :=
    real_cos_pow_nat_sub_one_le_exp_neg_mul_sq_div_two
      (n := n) hn2 hrpos.le hrlt
  have hexp_neg_log_two : Real.exp (-(Real.log 2)) = (1 / 2 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hexp_lt_half :
      Real.exp (-(((((n : ℕ) : ℝ) - 1) * r ^ 2) / 2)) < (1 / 2 : ℝ) := by
    have hExp :
        Real.exp (-(((((n : ℕ) : ℝ) - 1) * r ^ 2) / 2)) <
          Real.exp (-(Real.log 2)) :=
      Real.exp_lt_exp.mpr (neg_lt_neg hlarge)
    simpa [hexp_neg_log_two] using hExp
  have hhalf : Real.cos r ^ (n - 1) < (1 / 2 : ℝ) :=
    lt_of_le_of_lt hscalar_real hexp_lt_half
  exact (hTail hn2 hrpos hrlt hhalf).trans hscalar_real

/-- No-input adapter from the below-half north-pole coordinate power tail to
the north-pole coordinate Gaussian large-exponent tail. -/
theorem sphere_coordinateGaussianTailInteriorLargeExponentNorthPole_of_coordinateCosinePowerTailBelowHalf
    (hTail : sphere_northPoleCoordinateCosinePowerTailBelowHalf) :
    sphere_coordinateGaussianTailInteriorLargeExponentNorthPole := by
  intro n hn
  exact
    finRealSphereCoordinateGaussianTailInteriorLargeExponentNorthPole_of_coordinateCosinePowerTailBelowHalf
      n (hTail n)

/-- The north-pole spherical coordinate tail supplies the ambient cone-volume
north-pole tail by the `toSphere` cone formula. -/
theorem finRealSphereNorthPoleCapConeGaussianTailLargeExponent_of_coordinateTail
    (n : ℕ) [NeZero n]
    (hTail :
      FinRealSphereCoordinateGaussianTailInteriorLargeExponentNorthPole n (n : ℝ)) :
    FinRealSphereNorthPoleCapConeGaussianTailLargeExponent n (n : ℝ) := by
  intro r hn2 hrpos hrlt hlarge
  let e : FinRealEuclideanSpace n :=
    -(finRealSphereNorthPole n : FinRealEuclideanSpace n)
  let S : Set (FinRealSphere n) := finRealSphereClosedHalfspace n e (Real.sin r)
  let μ := finRealSurfaceProbabilityMeasure n
  let B : ℝ≥0∞ :=
    (finRealHaarMeasure n) (Metric.ball (0 : FinRealEuclideanSpace n) 1)
  haveI : (finRealHaarMeasure n).IsAddHaarMeasure := by
    unfold finRealHaarMeasure
    infer_instance
  have hS : MeasurableSet S :=
    measurableSet_finRealSphereClosedHalfspace n e (Real.sin r)
  have hcone_eq :
      μ S * B = (finRealHaarMeasure n) (finRealSphereRadialOpenCone n S) := by
    simpa [μ, B, S] using
      finRealSurfaceProbabilityMeasure_eq_cone_ratio (n := n) hS
  have hcoord :
      (finRealSphereCoordinateLaw n
          (-(finRealSphereNorthPole n : FinRealEuclideanSpace n))).real
          (Set.Ici (Real.sin r)) =
        μ.real S := by
    simpa [μ, S, e] using
      (sphereClosedHalfspaceMeasure_coordinate_formula n e (Real.sin r)).symm
  have hμ_real :
      μ.real S ≤ Real.exp (-(((((n : ℕ) : ℝ) - 1) * r ^ 2) / 2)) := by
    rw [← hcoord]
    exact hTail hn2 hrpos hrlt hlarge
  have hμ_fin : μ S ≠ ⊤ := by
    haveI : IsFiniteMeasure μ := by
      unfold μ finRealSurfaceProbabilityMeasure
      infer_instance
    exact (measure_lt_top μ S).ne
  have hμ_enn :
      μ S ≤ ENNReal.ofReal
        (Real.exp (-(((((n : ℕ) : ℝ) - 1) * r ^ 2) / 2))) := by
    rw [ENNReal.le_ofReal_iff_toReal_le hμ_fin (Real.exp_nonneg _)]
    simpa [measureReal_def] using hμ_real
  calc
    (finRealHaarMeasure n) (finRealSphereRadialOpenCone n S) = μ S * B :=
      hcone_eq.symm
    _ ≤ ENNReal.ofReal
          (Real.exp (-(((((n : ℕ) : ℝ) - 1) * r ^ 2) / 2))) *
          B := mul_le_mul_left hμ_enn B

/-- No-input adapter from the north-pole spherical coordinate-tail package to
the ambient cone-volume north-pole tail. -/
theorem sphere_northPoleCapConeGaussianTailLargeExponent_of_coordinateTail
    (hTail : sphere_coordinateGaussianTailInteriorLargeExponentNorthPole) :
    sphere_northPoleCapConeGaussianTailLargeExponent := by
  intro n hn
  exact
    finRealSphereNorthPoleCapConeGaussianTailLargeExponent_of_coordinateTail
      n (hTail n)

/-- Constant-integrand cone bridge.  This is the first function-level extension
of the indicator cone identity and fixes the normalization/algebra for the
arbitrary-integrand bridge above. -/
theorem lintegral_const_finRealSurfaceProbabilityMeasure_eq_cone
    {n : ℕ} [NeZero n] {S : Set (FinRealSphere n)} (hS : MeasurableSet S)
    (c : ℝ≥0∞) :
    (∫⁻ _ in S, c ∂(finRealSurfaceProbabilityMeasure n)) =
      (finRealHaarMeasure n (Metric.ball (0 : FinRealEuclideanSpace n) 1))⁻¹ *
        ∫⁻ _ in finRealSphereRadialOpenCone n S, c
          ∂(finRealHaarMeasure n) := by
  rw [setLIntegral_const, setLIntegral_const]
  have h1 :=
    lintegral_indicator_finRealSurfaceProbabilityMeasure_eq_cone (n := n) hS
  rw [setLIntegral_one, setLIntegral_one] at h1
  rw [h1]
  ring

/-- Compatibility of the radial cone construction with intersections: the
ambient cone of `S ∩ T` equals the cone of `S` intersected with the
preimage of `T` under any radial-direction projection.

The fallback parameter `u` only matters at the origin, which is absent from the
open cone, so the resulting set equality is independent of `u`.

This is the geometric step that lets us pass from set-level cone identities to
indicator-style function-level identities for the surface probability measure. -/
theorem finRealSphereRadialOpenCone_inter_eq_inter_direction_preimage
    {n : ℕ} (u : FinRealSphere n) (S T : Set (FinRealSphere n)) :
    finRealSphereRadialOpenCone n (S ∩ T) =
      finRealSphereRadialOpenCone n S ∩
        (finRealSphereRadialDirectionFrom (n := n) u ⁻¹' T) := by
  unfold finRealSphereRadialOpenCone
  ext z
  constructor
  · rintro ⟨r, hr, w, ⟨x, ⟨hxS, hxT⟩, rfl⟩, rfl⟩
    refine ⟨⟨r, hr, _, ⟨x, hxS, rfl⟩, rfl⟩, ?_⟩
    change finRealSphereRadialDirectionFrom u (r • (x : FinRealEuclideanSpace n)) ∈ T
    rw [finRealSphereRadialDirectionFrom_smul u x hr.1]
    exact hxT
  · rintro ⟨⟨r, hr, w, ⟨x, hxS, rfl⟩, rfl⟩, hdir⟩
    refine ⟨r, hr, _, ⟨x, ⟨hxS, ?_⟩, rfl⟩, rfl⟩
    have hxT :
        finRealSphereRadialDirectionFrom u
            (r • (x : FinRealEuclideanSpace n)) ∈ T := hdir
    rwa [finRealSphereRadialDirectionFrom_smul u x hr.1] at hxT

/-- Pointwise compatibility of the indicator with radial-direction pullback:
if `z` belongs to the open cone, then `T.indicator c (dir z) = T.indicator c (dir z)`,
written as a preimage indicator. -/
theorem finRealSphereRadialOpenCone_indicator_comp
    {n : ℕ} (u : FinRealSphere n) (T : Set (FinRealSphere n)) (c : ℝ≥0∞)
    (z : FinRealEuclideanSpace n) :
    T.indicator (fun _ => c) (finRealSphereRadialDirectionFrom (n := n) u z) =
      (finRealSphereRadialDirectionFrom (n := n) u ⁻¹' T).indicator
        (fun _ => c) z := by
  by_cases hz : finRealSphereRadialDirectionFrom (n := n) u z ∈ T
  · simp [Set.indicator, hz, Set.mem_preimage]
  · simp [Set.indicator, hz, Set.mem_preimage]

/-- Measurability of the radial direction. -/
theorem measurable_finRealSphereRadialDirectionFrom
    {n : ℕ} (u : FinRealSphere n) :
    Measurable (finRealSphereRadialDirectionFrom (n := n) u) := by
  classical
  -- Underlying ambient function
  let g : FinRealEuclideanSpace n → FinRealEuclideanSpace n :=
    fun z => if z = 0 then (u : FinRealEuclideanSpace n) else ‖z‖⁻¹ • z
  have hg_norm : ∀ z, ‖g z‖ = 1 := by
    intro z
    by_cases hz : z = 0
    · simp only [g, if_pos hz]
      exact finRealSphere_norm_coe n u
    · simp only [g, if_neg hz]
      have hnorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm_pos),
        inv_mul_cancel₀ hnorm_pos.ne']
  have hg_mem :
      ∀ z, g z ∈ Metric.sphere (0 : FinRealEuclideanSpace n) 1 := by
    intro z
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    exact hg_norm z
  have hg_meas : Measurable g := by
    refine Measurable.ite (measurableSet_singleton (0 : FinRealEuclideanSpace n))
      measurable_const ?_
    have hnorm : Measurable (fun z : FinRealEuclideanSpace n => ‖z‖) := by
      fun_prop
    exact (hnorm.inv).smul measurable_id
  -- The subtype-valued radial direction equals the canonical wrapping of g.
  have heq :
      finRealSphereRadialDirectionFrom (n := n) u =
        fun z : FinRealEuclideanSpace n => ⟨g z, hg_mem z⟩ := by
    funext z
    apply Subtype.ext
    show (finRealSphereRadialDirectionFrom (n := n) u z :
        FinRealEuclideanSpace n) = g z
    unfold finRealSphereRadialDirectionFrom
    by_cases hz : z = 0
    · simp [hz, g]
    · simp [hz, g]
  rw [heq]
  exact hg_meas.subtype_mk

/-- Step A — indicator × constant cone bridge.

Lifts the constant-integrand cone identity to integrands of the form
`T.indicator (fun _ => c)`, by intersecting with `T` on the sphere and using the
geometric compatibility lemma for the radial cone. -/
theorem lintegral_indicator_const_finRealSurfaceProbabilityMeasure_eq_cone
    {n : ℕ} [NeZero n] (u : FinRealSphere n)
    {S T : Set (FinRealSphere n)} (hS : MeasurableSet S)
    (hT : MeasurableSet T) (c : ℝ≥0∞) :
    (∫⁻ x in S, T.indicator (fun _ => c) x
        ∂(finRealSurfaceProbabilityMeasure n)) =
      (finRealHaarMeasure n (Metric.ball (0 : FinRealEuclideanSpace n) 1))⁻¹ *
        ∫⁻ z in finRealSphereRadialOpenCone n S,
          T.indicator (fun _ => c)
            (finRealSphereRadialDirectionFrom (n := n) u z)
          ∂(finRealHaarMeasure n) := by
  classical
  -- LHS: rewrite via setLIntegral_indicator and the constant cone identity.
  have hLHS :
      (∫⁻ x in S, T.indicator (fun _ => c) x
          ∂(finRealSurfaceProbabilityMeasure n)) =
        ∫⁻ _ in S ∩ T, c ∂(finRealSurfaceProbabilityMeasure n) := by
    rw [Set.inter_comm]
    exact setLIntegral_indicator hT (μ := finRealSurfaceProbabilityMeasure n)
      (t := S) (fun _ : FinRealSphere n => c)
  have hcone :
      (∫⁻ _ in S ∩ T, c ∂(finRealSurfaceProbabilityMeasure n)) =
        (finRealHaarMeasure n
            (Metric.ball (0 : FinRealEuclideanSpace n) 1))⁻¹ *
          ∫⁻ _ in finRealSphereRadialOpenCone n (S ∩ T), c
            ∂(finRealHaarMeasure n) :=
    lintegral_const_finRealSurfaceProbabilityMeasure_eq_cone (hS.inter hT) c
  -- Rewrite cone(S ∩ T) using the geometric intersection identity.
  have hcone_eq :
      finRealSphereRadialOpenCone n (S ∩ T) =
        finRealSphereRadialOpenCone n S ∩
          (finRealSphereRadialDirectionFrom (n := n) u ⁻¹' T) :=
    finRealSphereRadialOpenCone_inter_eq_inter_direction_preimage u S T
  -- RHS integrand: rewrite indicator on dir z as preimage indicator on z.
  have hRHS_integrand :
      ∀ z : FinRealEuclideanSpace n,
        T.indicator (fun _ => c)
            (finRealSphereRadialDirectionFrom (n := n) u z) =
          (finRealSphereRadialDirectionFrom (n := n) u ⁻¹' T).indicator
            (fun _ => c) z :=
    fun z => finRealSphereRadialOpenCone_indicator_comp u T c z
  have hRHS :
      (∫⁻ z in finRealSphereRadialOpenCone n S,
          T.indicator (fun _ => c)
            (finRealSphereRadialDirectionFrom (n := n) u z)
          ∂(finRealHaarMeasure n)) =
        ∫⁻ _ in finRealSphereRadialOpenCone n (S ∩ T), c
          ∂(finRealHaarMeasure n) := by
    have hpre_meas :
        MeasurableSet
          (finRealSphereRadialDirectionFrom (n := n) u ⁻¹' T) :=
      (measurable_finRealSphereRadialDirectionFrom u) hT
    calc
      (∫⁻ z in finRealSphereRadialOpenCone n S,
          T.indicator (fun _ => c)
            (finRealSphereRadialDirectionFrom (n := n) u z)
          ∂(finRealHaarMeasure n))
          =
        ∫⁻ z in finRealSphereRadialOpenCone n S,
          (finRealSphereRadialDirectionFrom (n := n) u ⁻¹' T).indicator
            (fun _ => c) z ∂(finRealHaarMeasure n) := by
          apply lintegral_congr_ae
          filter_upwards with z
          exact hRHS_integrand z
      _ =
        ∫⁻ _ in
          (finRealSphereRadialDirectionFrom (n := n) u ⁻¹' T) ∩
            finRealSphereRadialOpenCone n S, c
          ∂(finRealHaarMeasure n) :=
          setLIntegral_indicator hpre_meas (μ := finRealHaarMeasure n)
            (t := finRealSphereRadialOpenCone n S)
            (fun _ : FinRealEuclideanSpace n => c)
      _ =
        ∫⁻ _ in finRealSphereRadialOpenCone n (S ∩ T), c
          ∂(finRealHaarMeasure n) := by
          rw [hcone_eq, Set.inter_comm]
  rw [hLHS, hcone, hRHS]

/-- Pointwise cap-shadow estimate on the sphere.  If a unit vector `x` lies in
the closed cap `⟪e,x⟫ ≥ sin r` with `0 ≤ r ≤ π/2`, then its component
orthogonal to the unit axis `e` has length at most `cos r`. -/
theorem finRealSphereClosedHalfspace_orthogonalProjection_norm_le_cos
    {n : ℕ} [NeZero n] (e : FinRealEuclideanSpace n) (x : FinRealSphere n)
    {r : ℝ} (he : ‖e‖ = 1) (hr0 : 0 ≤ r) (hrle : r ≤ Real.pi / 2)
    (hx : x ∈ finRealSphereClosedHalfspace n e (Real.sin r)) :
    ‖(x : FinRealEuclideanSpace n) -
        (inner ℝ e (x : FinRealEuclideanSpace n)) • e‖ ≤ Real.cos r := by
  set a : ℝ := inner ℝ e (x : FinRealEuclideanSpace n)
  have hxnorm : ‖(x : FinRealEuclideanSpace n)‖ = 1 :=
    finRealSphere_norm_coe n x
  have ha_ge : Real.sin r ≤ a := by
    simpa [finRealSphereClosedHalfspace, finRealSphereInnerCoordinate, a] using hx
  have hsin_nonneg : 0 ≤ Real.sin r :=
    Real.sin_nonneg_of_nonneg_of_le_pi hr0 (by linarith [Real.pi_pos, hrle])
  have ha_nonneg : 0 ≤ a := le_trans hsin_nonneg ha_ge
  have ha_le_one : a ≤ 1 := by
    have hcs := abs_real_inner_le_norm e (x : FinRealEuclideanSpace n)
    rw [hxnorm, he, mul_one] at hcs
    have : |a| ≤ 1 := by
      simpa [a, real_inner_comm] using hcs
    exact le_trans (le_abs_self a) this
  have hsq_le : 1 - a ^ 2 ≤ Real.cos r ^ 2 := by
    have hsin_sq_le : Real.sin r ^ 2 ≤ a ^ 2 := by
      have hsin_abs : |Real.sin r| = Real.sin r := abs_of_nonneg hsin_nonneg
      have ha_abs : |a| = a := abs_of_nonneg ha_nonneg
      exact sq_le_sq.mpr (by simpa [hsin_abs, ha_abs] using ha_ge)
    have htrig : Real.cos r ^ 2 = 1 - Real.sin r ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq r]
    rw [htrig]
    linarith
  have hproj_sq :
      ‖(x : FinRealEuclideanSpace n) - a • e‖ ^ 2 = 1 - a ^ 2 := by
    rw [norm_sub_sq_real, hxnorm, norm_smul, he]
    rw [Real.norm_eq_abs, abs_of_nonneg ha_nonneg]
    have hinner : inner ℝ (x : FinRealEuclideanSpace n) e = a := by
      simp [a, real_inner_comm]
    rw [real_inner_smul_right, hinner]
    ring
  have hcos_nonneg : 0 ≤ Real.cos r :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, hrle⟩
  have hproj_nonneg :
      0 ≤ ‖(x : FinRealEuclideanSpace n) - a • e‖ :=
    norm_nonneg _
  rw [← sq_le_sq₀ hproj_nonneg hcos_nonneg]
  rw [hproj_sq]
  exact hsq_le

/-- Cone form of the pointwise cap-shadow estimate.  For every point `z` in
the radial open cone over the cap `⟪e,x⟫ ≥ sin r`, the orthogonal component of
`z` is bounded by `cos r` times its radius. -/
theorem finRealSphereRadialOpenCone_closedHalfspace_orthogonalProjection_norm_le_cos_mul_norm
    {n : ℕ} [NeZero n] (e : FinRealEuclideanSpace n)
    {r : ℝ} (he : ‖e‖ = 1) (hr0 : 0 ≤ r) (hrle : r ≤ Real.pi / 2)
    {z : FinRealEuclideanSpace n}
    (hz : z ∈ finRealSphereRadialOpenCone n
        (finRealSphereClosedHalfspace n e (Real.sin r))) :
    ‖z - (inner ℝ e z) • e‖ ≤ Real.cos r * ‖z‖ := by
  rcases hz with ⟨ρ, hρ, w, ⟨x, hx, rfl⟩, rfl⟩
  have hxbound :=
    finRealSphereClosedHalfspace_orthogonalProjection_norm_le_cos
      e x he hr0 hrle hx
  have hrewrite :
      ρ • (x : FinRealEuclideanSpace n) -
          (inner ℝ e (ρ • (x : FinRealEuclideanSpace n))) • e =
        ρ • ((x : FinRealEuclideanSpace n) -
          (inner ℝ e (x : FinRealEuclideanSpace n)) • e) := by
    simp [inner_smul_right, smul_sub, smul_smul]
  rw [hrewrite, norm_smul, norm_smul, finRealSphere_norm_coe n x,
    Real.norm_eq_abs, abs_of_pos hρ.1, mul_one]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hxbound hρ.1.le

/-- The radial open cone `(0,1) • S` is contained in the open unit ball. -/
theorem finRealSphereRadialOpenCone_subset_ball
    {n : ℕ} (S : Set (FinRealSphere n)) :
    finRealSphereRadialOpenCone n S ⊆
      Metric.ball (0 : FinRealEuclideanSpace n) 1 := by
  rintro z ⟨r, hr, w, ⟨x, _hx, rfl⟩, rfl⟩
  rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos hr.1, finRealSphere_norm_coe, mul_one]
  exact hr.2

/-- Ambient characterization of the radial open cone over a closed spherical
halfspace.  A point is in the cone exactly when it is a nonzero point of the
open unit ball whose radial direction satisfies the halfspace inequality. -/
theorem finRealSphereRadialOpenCone_closedHalfspace_mem_iff
    {n : ℕ} (e : FinRealEuclideanSpace n) (t : ℝ)
    {z : FinRealEuclideanSpace n} :
    z ∈ finRealSphereRadialOpenCone n (finRealSphereClosedHalfspace n e t) ↔
      z ∈ Metric.ball (0 : FinRealEuclideanSpace n) 1 ∧
        z ≠ 0 ∧ t * ‖z‖ ≤ inner ℝ e z := by
  constructor
  · rintro ⟨ρ, hρ, w, ⟨x, hx, rfl⟩, rfl⟩
    have hball :
        ρ • (x : FinRealEuclideanSpace n) ∈
          Metric.ball (0 : FinRealEuclideanSpace n) 1 :=
      finRealSphereRadialOpenCone_subset_ball
        (finRealSphereClosedHalfspace n e t)
        ⟨ρ, hρ, (x : FinRealEuclideanSpace n), ⟨x, hx, rfl⟩, rfl⟩
    have hz0 :
        ρ • (x : FinRealEuclideanSpace n) ≠ 0 :=
      smul_ne_zero hρ.1.ne' (finRealSphere_ne_zero n x)
    have hxcoord : t ≤ inner ℝ e (x : FinRealEuclideanSpace n) := by
      simpa [finRealSphereClosedHalfspace, finRealSphereInnerCoordinate] using hx
    have hnorm :
        ‖ρ • (x : FinRealEuclideanSpace n)‖ = ρ := by
      rw [norm_smul, finRealSphere_norm_coe n x, Real.norm_eq_abs,
        abs_of_pos hρ.1, mul_one]
    have hinner :
        inner ℝ e (ρ • (x : FinRealEuclideanSpace n)) =
          ρ * inner ℝ e (x : FinRealEuclideanSpace n) := by
      rw [inner_smul_right]
    refine ⟨hball, hz0, ?_⟩
    rw [hnorm, hinner]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hxcoord hρ.1.le
  · rintro ⟨hball, hz0, hineq⟩
    have hnorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hnorm_lt : ‖z‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hball
    let x : FinRealSphere n :=
      ⟨‖z‖⁻¹ • z, by
        rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul]
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm_pos),
          inv_mul_cancel₀ hnorm_pos.ne']⟩
    have hx : x ∈ finRealSphereClosedHalfspace n e t := by
      have hscaled :
          t ≤ ‖z‖⁻¹ * inner ℝ e z := by
        have hmul :=
          mul_le_mul_of_nonneg_right hineq (inv_nonneg.mpr hnorm_pos.le)
        rw [mul_assoc, mul_inv_cancel₀ hnorm_pos.ne', mul_one] at hmul
        simpa [mul_comm] using hmul
      simpa [x, finRealSphereClosedHalfspace, finRealSphereInnerCoordinate,
        inner_smul_right] using hscaled
    refine ⟨‖z‖, ⟨hnorm_pos, hnorm_lt⟩, (x : FinRealEuclideanSpace n),
      ⟨x, hx, rfl⟩, ?_⟩
    change ‖z‖ • (‖z‖⁻¹ • z) = z
    rw [smul_smul, mul_inv_cancel₀ hnorm_pos.ne', one_smul]

/-- Ambient closed cone corresponding to a spherical closed halfspace.  For
`0 ≤ t`, this is the finite-dimensional Lorentz-type cone
`t ‖z‖ ≤ ⟪e,z⟫`. -/
def finRealSphereClosedHalfspaceAmbientCone
    {n : ℕ} (e : FinRealEuclideanSpace n) (t : ℝ) :
    Set (FinRealEuclideanSpace n) :=
  {z | t * ‖z‖ ≤ inner ℝ e z}

/-- The radial open cone is contained in its ambient closed-cone inequality. -/
theorem finRealSphereRadialOpenCone_closedHalfspace_subset_ambientCone
    {n : ℕ} (e : FinRealEuclideanSpace n) (t : ℝ) :
    finRealSphereRadialOpenCone n (finRealSphereClosedHalfspace n e t) ⊆
      finRealSphereClosedHalfspaceAmbientCone e t := by
  intro z hz
  exact (finRealSphereRadialOpenCone_closedHalfspace_mem_iff e t).mp hz |>.2.2

/-- The ambient closed halfspace cone is convex.  This is the exact convexity
input needed to invoke mathlib's null-frontier theorem for finite-dimensional
Haar measure. -/
theorem convex_finRealSphereClosedHalfspaceAmbientCone
    {n : ℕ} (e : FinRealEuclideanSpace n) {t : ℝ} (ht : 0 ≤ t) :
    Convex ℝ (finRealSphereClosedHalfspaceAmbientCone e t) := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  change t * ‖a • x + b • y‖ ≤ inner ℝ e (a • x + b • y)
  have hnorm :
      ‖a • x + b • y‖ ≤ a * ‖x‖ + b * ‖y‖ := by
    calc
      ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = |a| * ‖x‖ + |b| * ‖y‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ = a * ‖x‖ + b * ‖y‖ := by
          rw [abs_of_nonneg ha, abs_of_nonneg hb]
  calc
    t * ‖a • x + b • y‖
        ≤ t * (a * ‖x‖ + b * ‖y‖) :=
          mul_le_mul_of_nonneg_left hnorm ht
    _ = a * (t * ‖x‖) + b * (t * ‖y‖) := by ring
    _ ≤ a * inner ℝ e x + b * inner ℝ e y :=
          add_le_add
            (mul_le_mul_of_nonneg_left hx ha)
            (mul_le_mul_of_nonneg_left hy hb)
    _ = inner ℝ e (a • x + b • y) := by
          rw [inner_add_right, inner_smul_right, inner_smul_right]

/-- The frontier of the ambient closed halfspace cone has zero Haar measure.
This packages mathlib's `Convex.addHaar_frontier` for the cap-tail boundary
removal step. -/
theorem finRealSphereClosedHalfspaceAmbientCone_frontier_measure_zero
    {n : ℕ} (e : FinRealEuclideanSpace n) {t : ℝ} (ht : 0 ≤ t) :
    (finRealHaarMeasure n) (frontier (finRealSphereClosedHalfspaceAmbientCone e t)) =
      0 := by
  haveI : (finRealHaarMeasure n).IsAddHaarMeasure := by
    unfold finRealHaarMeasure
    infer_instance
  exact
    (convex_finRealSphereClosedHalfspaceAmbientCone e ht).addHaar_frontier
      (finRealHaarMeasure n)

/-- Tangent-square form of the cap-cone inequality.  It is the radicand
nonnegativity estimate needed by the cap-flattening map:
if `z` lies in the cone over `⟪e,x⟫ ≥ sin r`, then the axial coordinate
dominates `tan(r)` times the orthogonal component. -/
theorem finRealSphereRadialOpenCone_closedHalfspace_tan_sq_mul_orthogonalProjection_norm_sq_le_inner_sq
    {n : ℕ} (e : FinRealEuclideanSpace n)
    {r : ℝ} (he : ‖e‖ = 1) (hrpos : 0 < r) (hrlt : r < Real.pi / 2)
    {z : FinRealEuclideanSpace n}
    (hz : z ∈ finRealSphereRadialOpenCone n
        (finRealSphereClosedHalfspace n e (Real.sin r))) :
    (Real.sin r / Real.cos r) ^ 2 *
        ‖z - (inner ℝ e z) • e‖ ^ 2 ≤ (inner ℝ e z) ^ 2 := by
  set a : ℝ := inner ℝ e z
  set u : FinRealEuclideanSpace n := z - a • e
  have hmem := (finRealSphereRadialOpenCone_closedHalfspace_mem_iff e (Real.sin r)).mp hz
  have hineq : Real.sin r * ‖z‖ ≤ a := by
    simpa [a] using hmem.2.2
  have hr0 : 0 ≤ r := le_of_lt hrpos
  have hrle : r ≤ Real.pi / 2 := le_of_lt hrlt
  have hsin_nonneg : 0 ≤ Real.sin r :=
    Real.sin_nonneg_of_nonneg_of_le_pi hr0 (by linarith [Real.pi_pos, hrle])
  have hcos_pos : 0 < Real.cos r := by
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hrpos], hrlt⟩
  have hsnorm_nonneg : 0 ≤ Real.sin r * ‖z‖ :=
    mul_nonneg hsin_nonneg (norm_nonneg z)
  have ha_nonneg : 0 ≤ a := le_trans hsnorm_nonneg hineq
  have hs_sq_norm : (Real.sin r * ‖z‖) ^ 2 ≤ a ^ 2 := by
    exact (sq_le_sq₀ hsnorm_nonneg ha_nonneg).2 hineq
  have hs_sq_norm' : Real.sin r ^ 2 * ‖z‖ ^ 2 ≤ a ^ 2 := by
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hs_sq_norm
  have hproj_sq : ‖u‖ ^ 2 = ‖z‖ ^ 2 - a ^ 2 := by
    change ‖z - a • e‖ ^ 2 = ‖z‖ ^ 2 - a ^ 2
    rw [norm_sub_sq_real, norm_smul, he]
    rw [Real.norm_eq_abs, abs_of_nonneg ha_nonneg]
    have hinner : inner ℝ z e = a := by
      simp [a, real_inner_comm]
    rw [real_inner_smul_right, hinner]
    ring
  have hmain :
      Real.sin r ^ 2 * (‖z‖ ^ 2 - a ^ 2) ≤ Real.cos r ^ 2 * a ^ 2 := by
    nlinarith [hs_sq_norm', Real.sin_sq_add_cos_sq r]
  rw [hproj_sq]
  have hcos_sq_pos : 0 < Real.cos r ^ 2 :=
    sq_pos_of_ne_zero hcos_pos.ne'
  have hdiv :
      (Real.sin r / Real.cos r) ^ 2 * (‖z‖ ^ 2 - a ^ 2) =
        (Real.sin r ^ 2 * (‖z‖ ^ 2 - a ^ 2)) / Real.cos r ^ 2 := by
    field_simp [hcos_pos.ne']
  rw [hdiv]
  exact (div_le_iff₀ hcos_sq_pos).2 (by simpa [mul_comm] using hmain)

/-- Cap-flattening map for the ambient cone over `⟪e,x⟫ ≥ sin r`.
Writing `a = ⟪e,z⟫` and `u = z - a e`, the map stretches the orthogonal
coordinate by `cos(r)⁻¹` and replaces the axial coordinate by
`sqrt(a^2 - tan(r)^2 ‖u‖^2)`. -/
noncomputable def finRealSphereCapConeFlatteningMap
    {n : ℕ} (e : FinRealEuclideanSpace n) (r : ℝ)
    (z : FinRealEuclideanSpace n) : FinRealEuclideanSpace n :=
  let a : ℝ := inner ℝ e z
  let u : FinRealEuclideanSpace n := z - a • e
  Real.sqrt (a ^ 2 - (Real.sin r / Real.cos r) ^ 2 * ‖u‖ ^ 2) • e +
    (Real.cos r)⁻¹ • u

/-- Axial coordinate of the cap-flattening map. -/
theorem finRealSphereCapConeFlatteningMap_inner_eq
    {n : ℕ} (e : FinRealEuclideanSpace n) (r : ℝ)
    (z : FinRealEuclideanSpace n) (he : ‖e‖ = 1) :
    inner ℝ e (finRealSphereCapConeFlatteningMap e r z) =
      Real.sqrt
        ((inner ℝ e z) ^ 2 -
          (Real.sin r / Real.cos r) ^ 2 *
            ‖z - (inner ℝ e z) • e‖ ^ 2) := by
  set a : ℝ := inner ℝ e z
  set u : FinRealEuclideanSpace n := z - a • e
  have horth : inner ℝ e u = 0 := by
    dsimp [u, a]
    rw [inner_sub_right, real_inner_smul_right]
    rw [real_inner_self_eq_norm_sq, he]
    ring
  dsimp [finRealSphereCapConeFlatteningMap, a, u]
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, horth]
  rw [real_inner_self_eq_norm_sq, he]
  ring

/-- Orthogonal coordinate of the cap-flattening map. -/
theorem finRealSphereCapConeFlatteningMap_orthogonalProjection_eq
    {n : ℕ} (e : FinRealEuclideanSpace n) (r : ℝ)
    (z : FinRealEuclideanSpace n) (he : ‖e‖ = 1) :
    finRealSphereCapConeFlatteningMap e r z -
        (inner ℝ e (finRealSphereCapConeFlatteningMap e r z)) • e =
      (Real.cos r)⁻¹ • (z - (inner ℝ e z) • e) := by
  set a : ℝ := inner ℝ e z
  set u : FinRealEuclideanSpace n := z - a • e
  have horth : inner ℝ e u = 0 := by
    dsimp [u, a]
    rw [inner_sub_right, real_inner_smul_right]
    rw [real_inner_self_eq_norm_sq, he]
    ring
  have hinnerF :=
    finRealSphereCapConeFlatteningMap_inner_eq e r z he
  rw [hinnerF]
  dsimp [finRealSphereCapConeFlatteningMap, a, u]
  abel

/-- The cap-flattening map sends the radial cone over the cap
`⟪e,x⟫ ≥ sin r` into the open unit ball.  Pointwise, the square norm of the
flattened point is exactly `‖z‖^2`; the cap condition is used only to make the
square-root radicand nonnegative. -/
theorem finRealSphereCapConeFlatteningMap_mem_ball_of_mem_closedHalfspaceCone
    {n : ℕ} (e : FinRealEuclideanSpace n)
    {r : ℝ} (he : ‖e‖ = 1) (hrpos : 0 < r) (hrlt : r < Real.pi / 2)
    {z : FinRealEuclideanSpace n}
    (hz : z ∈ finRealSphereRadialOpenCone n
        (finRealSphereClosedHalfspace n e (Real.sin r))) :
    finRealSphereCapConeFlatteningMap e r z ∈
      Metric.ball (0 : FinRealEuclideanSpace n) 1 := by
  set a : ℝ := inner ℝ e z
  set u : FinRealEuclideanSpace n := z - a • e
  set q : ℝ := a ^ 2 - (Real.sin r / Real.cos r) ^ 2 * ‖u‖ ^ 2
  have htan :=
    finRealSphereRadialOpenCone_closedHalfspace_tan_sq_mul_orthogonalProjection_norm_sq_le_inner_sq
      e he hrpos hrlt hz
  have hq_nonneg : 0 ≤ q := by
    dsimp [q, u, a]
    nlinarith [htan]
  have hcos_pos : 0 < Real.cos r :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hrpos], hrlt⟩
  have hmem :=
    (finRealSphereRadialOpenCone_closedHalfspace_mem_iff e (Real.sin r)).mp hz
  have hz_norm_lt : ‖z‖ < 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hmem.1
  have ha_nonneg : 0 ≤ a := by
    have hineq : Real.sin r * ‖z‖ ≤ a := by
      simpa [a] using hmem.2.2
    have hr0 : 0 ≤ r := le_of_lt hrpos
    have hrle : r ≤ Real.pi / 2 := le_of_lt hrlt
    have hsin_nonneg : 0 ≤ Real.sin r :=
      Real.sin_nonneg_of_nonneg_of_le_pi hr0 (by linarith [Real.pi_pos, hrle])
    exact le_trans (mul_nonneg hsin_nonneg (norm_nonneg z)) hineq
  have horth : inner ℝ e u = 0 := by
    dsimp [u, a]
    rw [inner_sub_right, real_inner_smul_right]
    rw [real_inner_self_eq_norm_sq, he]
    ring
  have hproj_sq : ‖u‖ ^ 2 = ‖z‖ ^ 2 - a ^ 2 := by
    dsimp [u]
    change ‖z - a • e‖ ^ 2 = ‖z‖ ^ 2 - a ^ 2
    rw [norm_sub_sq_real, norm_smul, he]
    rw [Real.norm_eq_abs, abs_of_nonneg ha_nonneg]
    have hinner : inner ℝ z e = a := by
      simp [a, real_inner_comm]
    rw [real_inner_smul_right, hinner]
    ring
  have hnorm_sq :
      ‖finRealSphereCapConeFlatteningMap e r z‖ ^ 2 = ‖z‖ ^ 2 := by
    dsimp [finRealSphereCapConeFlatteningMap, q, u, a]
    rw [norm_add_sq_real]
    have hcross :
        inner ℝ
          (Real.sqrt
            (a ^ 2 - (Real.sin r / Real.cos r) ^ 2 * ‖u‖ ^ 2) • e)
          ((Real.cos r)⁻¹ • u) = 0 := by
      rw [real_inner_smul_left, real_inner_smul_right, horth]
      ring
    rw [hcross]
    simp [norm_smul, he, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [abs_of_pos hcos_pos]
    rw [Real.sq_sqrt hq_nonneg]
    change q + ((Real.cos r)⁻¹ * ‖u‖) ^ 2 = ‖z‖ ^ 2
    rw [mul_pow]
    have hcalc : q + (Real.cos r)⁻¹ ^ 2 * ‖u‖ ^ 2 = ‖z‖ ^ 2 := by
      dsimp [q]
      rw [div_pow]
      field_simp [hcos_pos.ne']
      nlinarith [hproj_sq, Real.sin_sq_add_cos_sq r]
    exact hcalc
  rw [Metric.mem_ball, dist_zero_right]
  rw [← sq_lt_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  change ‖finRealSphereCapConeFlatteningMap e r z‖ ^ 2 < (1 : ℝ) ^ 2
  rw [hnorm_sq]
  nlinarith [hz_norm_lt, norm_nonneg z]

/-- `MapsTo` form of `finRealSphereCapConeFlatteningMap_mem_ball_of_mem_closedHalfspaceCone`. -/
theorem finRealSphereCapConeFlatteningMap_mapsTo_closedHalfspaceCone_ball
    {n : ℕ} (e : FinRealEuclideanSpace n)
    {r : ℝ} (he : ‖e‖ = 1) (hrpos : 0 < r) (hrlt : r < Real.pi / 2) :
    Set.MapsTo (finRealSphereCapConeFlatteningMap e r)
      (finRealSphereRadialOpenCone n
        (finRealSphereClosedHalfspace n e (Real.sin r)))
      (Metric.ball (0 : FinRealEuclideanSpace n) 1) := by
  intro z hz
  exact
    finRealSphereCapConeFlatteningMap_mem_ball_of_mem_closedHalfspaceCone
      e he hrpos hrlt hz

/-- The cap-flattening map is injective on the cap cone.  The proof recovers
the orthogonal coordinate from the flattened orthogonal projection and then
recovers the nonnegative axial coordinate from the flattened axial coordinate. -/
theorem finRealSphereCapConeFlatteningMap_injOn_closedHalfspaceCone
    {n : ℕ} (e : FinRealEuclideanSpace n)
    {r : ℝ} (he : ‖e‖ = 1) (hrpos : 0 < r) (hrlt : r < Real.pi / 2) :
    Set.InjOn (finRealSphereCapConeFlatteningMap e r)
      (finRealSphereRadialOpenCone n
        (finRealSphereClosedHalfspace n e (Real.sin r))) := by
  intro z hz w hw hF
  set az : ℝ := inner ℝ e z
  set aw : ℝ := inner ℝ e w
  set uz : FinRealEuclideanSpace n := z - az • e
  set uw : FinRealEuclideanSpace n := w - aw • e
  have hcos_pos : 0 < Real.cos r :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hrpos], hrlt⟩
  have hproj_eq_raw :=
    congrArg (fun y : FinRealEuclideanSpace n => y - (inner ℝ e y) • e) hF
  have hproj_eq :
      (Real.cos r)⁻¹ • uz = (Real.cos r)⁻¹ • uw := by
    rw [← finRealSphereCapConeFlatteningMap_orthogonalProjection_eq e r z he,
      ← finRealSphereCapConeFlatteningMap_orthogonalProjection_eq e r w he]
    exact hproj_eq_raw
  have hu_eq : uz = uw := by
    have h := congrArg (fun y : FinRealEuclideanSpace n => Real.cos r • y) hproj_eq
    simpa [uz, uw, smul_smul, hcos_pos.ne'] using h
  have hinner_eq_raw := congrArg (fun y : FinRealEuclideanSpace n => inner ℝ e y) hF
  have hb_eq :
      Real.sqrt (az ^ 2 - (Real.sin r / Real.cos r) ^ 2 * ‖uz‖ ^ 2) =
        Real.sqrt (aw ^ 2 - (Real.sin r / Real.cos r) ^ 2 * ‖uw‖ ^ 2) := by
    change inner ℝ e (finRealSphereCapConeFlatteningMap e r z) =
        inner ℝ e (finRealSphereCapConeFlatteningMap e r w) at hinner_eq_raw
    rw [finRealSphereCapConeFlatteningMap_inner_eq e r z he,
      finRealSphereCapConeFlatteningMap_inner_eq e r w he] at hinner_eq_raw
    simpa [az, aw, uz, uw] using hinner_eq_raw
  have htan_z :=
    finRealSphereRadialOpenCone_closedHalfspace_tan_sq_mul_orthogonalProjection_norm_sq_le_inner_sq
      e he hrpos hrlt hz
  have htan_w :=
    finRealSphereRadialOpenCone_closedHalfspace_tan_sq_mul_orthogonalProjection_norm_sq_le_inner_sq
      e he hrpos hrlt hw
  have hqz_nonneg :
      0 ≤ az ^ 2 - (Real.sin r / Real.cos r) ^ 2 * ‖uz‖ ^ 2 := by
    dsimp [az, uz]
    nlinarith [htan_z]
  have hqw_nonneg :
      0 ≤ aw ^ 2 - (Real.sin r / Real.cos r) ^ 2 * ‖uw‖ ^ 2 := by
    dsimp [aw, uw]
    nlinarith [htan_w]
  have hb_sq_eq :
      az ^ 2 - (Real.sin r / Real.cos r) ^ 2 * ‖uz‖ ^ 2 =
        aw ^ 2 - (Real.sin r / Real.cos r) ^ 2 * ‖uw‖ ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hb_eq
    change
      Real.sqrt (az ^ 2 - (Real.sin r / Real.cos r) ^ 2 * ‖uz‖ ^ 2) ^ 2 =
        Real.sqrt (aw ^ 2 - (Real.sin r / Real.cos r) ^ 2 * ‖uw‖ ^ 2) ^ 2 at h
    rw [Real.sq_sqrt hqz_nonneg, Real.sq_sqrt hqw_nonneg] at h
    exact h
  have haz_sq_eq : az ^ 2 = aw ^ 2 := by
    rw [hu_eq] at hb_sq_eq
    nlinarith
  have hmem_z :=
    (finRealSphereRadialOpenCone_closedHalfspace_mem_iff e (Real.sin r)).mp hz
  have hmem_w :=
    (finRealSphereRadialOpenCone_closedHalfspace_mem_iff e (Real.sin r)).mp hw
  have haz_nonneg : 0 ≤ az := by
    have hineq : Real.sin r * ‖z‖ ≤ az := by
      simpa [az] using hmem_z.2.2
    have hr0 : 0 ≤ r := le_of_lt hrpos
    have hrle : r ≤ Real.pi / 2 := le_of_lt hrlt
    have hsin_nonneg : 0 ≤ Real.sin r :=
      Real.sin_nonneg_of_nonneg_of_le_pi hr0 (by linarith [Real.pi_pos, hrle])
    exact le_trans (mul_nonneg hsin_nonneg (norm_nonneg z)) hineq
  have haw_nonneg : 0 ≤ aw := by
    have hineq : Real.sin r * ‖w‖ ≤ aw := by
      simpa [aw] using hmem_w.2.2
    have hr0 : 0 ≤ r := le_of_lt hrpos
    have hrle : r ≤ Real.pi / 2 := le_of_lt hrlt
    have hsin_nonneg : 0 ≤ Real.sin r :=
      Real.sin_nonneg_of_nonneg_of_le_pi hr0 (by linarith [Real.pi_pos, hrle])
    exact le_trans (mul_nonneg hsin_nonneg (norm_nonneg w)) hineq
  have ha_eq : az = aw := by
    exact (sq_eq_sq₀ haz_nonneg haw_nonneg).mp haz_sq_eq
  have hz_decomp : z = az • e + uz := by
    dsimp [uz, az]
    abel
  have hw_decomp : w = aw • e + uw := by
    dsimp [uw, aw]
    abel
  rw [hz_decomp, hw_decomp, ha_eq, hu_eq]

/-- Orthogonal component used by the cap-flattening map. -/
noncomputable def finRealSphereCapConeOrthogonalComponent
    {n : ℕ} (e : FinRealEuclideanSpace n)
    (z : FinRealEuclideanSpace n) : FinRealEuclideanSpace n :=
  z - (inner ℝ e z) • e

/-- Linear derivative of the orthogonal-component map
`z ↦ z - ⟪e,z⟫ e`. -/
noncomputable def finRealSphereCapConeOrthogonalComponentFDeriv
    {n : ℕ} (e : FinRealEuclideanSpace n) :
    FinRealEuclideanSpace n →L[ℝ] FinRealEuclideanSpace n :=
  ContinuousLinearMap.id ℝ (FinRealEuclideanSpace n) - (innerSL ℝ e).smulRight e

/-- Radicand under the square root in the cap-flattening map. -/
noncomputable def finRealSphereCapConeRadicand
    {n : ℕ} (e : FinRealEuclideanSpace n) (r : ℝ)
    (z : FinRealEuclideanSpace n) : ℝ :=
  (inner ℝ e z) ^ 2 -
    (Real.sin r / Real.cos r) ^ 2 *
      ‖finRealSphereCapConeOrthogonalComponent e z‖ ^ 2

/-- Explicit derivative of the cap-flattening radicand. -/
noncomputable def finRealSphereCapConeRadicandFDeriv
    {n : ℕ} (e : FinRealEuclideanSpace n) (r : ℝ)
    (z : FinRealEuclideanSpace n) :
    FinRealEuclideanSpace n →L[ℝ] ℝ :=
  let a : ℝ := inner ℝ e z
  let u : FinRealEuclideanSpace n := finRealSphereCapConeOrthogonalComponent e z
  let t : ℝ := Real.sin r / Real.cos r
  (2 * a) • innerSL ℝ e -
    (t ^ 2) •
      (((2 : ℕ) • innerSL ℝ u).comp
        (finRealSphereCapConeOrthogonalComponentFDeriv e))

/-- Explicit derivative of the cap-flattening map away from the radicand-zero
boundary. -/
noncomputable def finRealSphereCapConeFlatteningMapFDeriv
    {n : ℕ} (e : FinRealEuclideanSpace n) (r : ℝ)
    (z : FinRealEuclideanSpace n) :
    FinRealEuclideanSpace n →L[ℝ] FinRealEuclideanSpace n :=
  ((1 / (2 * Real.sqrt (finRealSphereCapConeRadicand e r z))) •
      finRealSphereCapConeRadicandFDeriv e r z).smulRight e +
    (Real.cos r)⁻¹ • finRealSphereCapConeOrthogonalComponentFDeriv e

/-- The orthogonal-component map has the advertised linear derivative. -/
theorem hasFDerivAt_finRealSphereCapConeOrthogonalComponent
    {n : ℕ} (e : FinRealEuclideanSpace n) (z : FinRealEuclideanSpace n) :
    HasFDerivAt (finRealSphereCapConeOrthogonalComponent e)
      (finRealSphereCapConeOrthogonalComponentFDeriv e) z := by
  have hinner : HasFDerivAt (fun y : FinRealEuclideanSpace n => inner ℝ e y)
      (innerSL ℝ e) z :=
    (innerSL ℝ e).hasFDerivAt
  have hmain :=
    (hasFDerivAt_id z).sub (hinner.smul_const e)
  simpa [finRealSphereCapConeOrthogonalComponent,
    finRealSphereCapConeOrthogonalComponentFDeriv] using hmain

/-- The cap-flattening radicand is a smooth quadratic expression, with the
explicit derivative used by the later determinant calculation. -/
theorem hasFDerivAt_finRealSphereCapConeRadicand
    {n : ℕ} (e : FinRealEuclideanSpace n) (r : ℝ)
    (z : FinRealEuclideanSpace n) :
    HasFDerivAt (finRealSphereCapConeRadicand e r)
      (finRealSphereCapConeRadicandFDeriv e r z) z := by
  let a : ℝ := inner ℝ e z
  let u : FinRealEuclideanSpace n := finRealSphereCapConeOrthogonalComponent e z
  let t : ℝ := Real.sin r / Real.cos r
  have hinner : HasFDerivAt (fun y : FinRealEuclideanSpace n => inner ℝ e y)
      (innerSL ℝ e) z :=
    (innerSL ℝ e).hasFDerivAt
  have horth := hasFDerivAt_finRealSphereCapConeOrthogonalComponent e z
  have hinner_sq :
      HasFDerivAt (fun y : FinRealEuclideanSpace n => (inner ℝ e y) ^ 2)
        ((2 * a) • innerSL ℝ e) z := by
    simpa [a, two_nsmul] using hinner.pow 2
  have horth_sq :
      HasFDerivAt
        (fun y : FinRealEuclideanSpace n =>
          ‖finRealSphereCapConeOrthogonalComponent e y‖ ^ 2)
        (((2 : ℕ) • innerSL ℝ u).comp
          (finRealSphereCapConeOrthogonalComponentFDeriv e)) z := by
    simpa only [Function.comp_apply, u] using
      (hasStrictFDerivAt_norm_sq u).hasFDerivAt.comp z horth
  have hscaled :
      HasFDerivAt
        (fun y : FinRealEuclideanSpace n =>
          t ^ 2 * ‖finRealSphereCapConeOrthogonalComponent e y‖ ^ 2)
        ((t ^ 2) •
          (((2 : ℕ) • innerSL ℝ u).comp
            (finRealSphereCapConeOrthogonalComponentFDeriv e))) z := by
    simpa [smul_eq_mul] using horth_sq.const_smul (t ^ 2)
  have hmain := hinner_sq.sub hscaled
  simpa [finRealSphereCapConeRadicand, finRealSphereCapConeRadicandFDeriv,
    a, u, t] using hmain

/-- The cap-flattening radicand is continuous. -/
theorem continuous_finRealSphereCapConeRadicand
    {n : ℕ} (e : FinRealEuclideanSpace n) (r : ℝ) :
    Continuous (finRealSphereCapConeRadicand e r) := by
  exact continuous_iff_continuousAt.mpr fun z =>
    (hasFDerivAt_finRealSphereCapConeRadicand e r z).continuousAt

/-- Away from the radicand-zero boundary, the cap-flattening map has the
advertised explicit derivative.  The boundary is the remaining place where the
closed-cone change-of-variables route needs a null-boundary/a.e. treatment. -/
theorem hasFDerivAt_finRealSphereCapConeFlatteningMap_of_radicand_ne_zero
    {n : ℕ} (e : FinRealEuclideanSpace n) (r : ℝ)
    {z : FinRealEuclideanSpace n}
    (hq : finRealSphereCapConeRadicand e r z ≠ 0) :
    HasFDerivAt (finRealSphereCapConeFlatteningMap e r)
      (finRealSphereCapConeFlatteningMapFDeriv e r z) z := by
  let q : ℝ := finRealSphereCapConeRadicand e r z
  have hqderiv := hasFDerivAt_finRealSphereCapConeRadicand e r z
  have hsqrt :
      HasFDerivAt
        (fun y : FinRealEuclideanSpace n =>
          Real.sqrt (finRealSphereCapConeRadicand e r y))
        ((1 / (2 * Real.sqrt q)) •
          finRealSphereCapConeRadicandFDeriv e r z) z := by
    simpa [q] using hqderiv.sqrt hq
  have hfirst :
      HasFDerivAt
        (fun y : FinRealEuclideanSpace n =>
          Real.sqrt (finRealSphereCapConeRadicand e r y) • e)
        (((1 / (2 * Real.sqrt q)) •
          finRealSphereCapConeRadicandFDeriv e r z).smulRight e) z :=
    hsqrt.smul_const e
  have horth := hasFDerivAt_finRealSphereCapConeOrthogonalComponent e z
  have hsecond :
      HasFDerivAt
        (fun y : FinRealEuclideanSpace n =>
          (Real.cos r)⁻¹ • finRealSphereCapConeOrthogonalComponent e y)
        ((Real.cos r)⁻¹ •
          finRealSphereCapConeOrthogonalComponentFDeriv e) z :=
    horth.const_smul (Real.cos r)⁻¹
  have hmain := hfirst.add hsecond
  simpa [finRealSphereCapConeFlatteningMap, finRealSphereCapConeRadicand,
    finRealSphereCapConeOrthogonalComponent, finRealSphereCapConeFlatteningMapFDeriv,
    q] using hmain

/-- The orthogonal component is orthogonal to the unit axis. -/
theorem finRealSphereCapConeOrthogonalComponent_inner_eq_zero
    {n : ℕ} (e : FinRealEuclideanSpace n) (z : FinRealEuclideanSpace n)
    (he : ‖e‖ = 1) :
    inner ℝ e (finRealSphereCapConeOrthogonalComponent e z) = 0 := by
  simp [finRealSphereCapConeOrthogonalComponent, inner_sub_right,
    inner_smul_right, he]

/-- Decomposition into axial and orthogonal components. -/
theorem finRealSphereCapConeOrthogonalComponent_decomp
    {n : ℕ} (e : FinRealEuclideanSpace n) (z : FinRealEuclideanSpace n) :
    (inner ℝ e z) • e + finRealSphereCapConeOrthogonalComponent e z = z := by
  simp [finRealSphereCapConeOrthogonalComponent, sub_eq_add_neg]

/-- Pythagorean decomposition of a vector into its unit-axis component and
orthogonal component. -/
theorem finRealSphereCapConeOrthogonalComponent_norm_sq_eq
    {n : ℕ} (e : FinRealEuclideanSpace n) (z : FinRealEuclideanSpace n)
    (he : ‖e‖ = 1) :
    ‖z‖ ^ 2 =
      (inner ℝ e z) ^ 2 +
        ‖finRealSphereCapConeOrthogonalComponent e z‖ ^ 2 := by
  let a : ℝ := inner ℝ e z
  let u : FinRealEuclideanSpace n := finRealSphereCapConeOrthogonalComponent e z
  have hdecomp : z = a • e + u := by
    simpa [a, u] using (finRealSphereCapConeOrthogonalComponent_decomp e z).symm
  have horth : inner ℝ (a • e) u = 0 := by
    rw [inner_smul_left, finRealSphereCapConeOrthogonalComponent_inner_eq_zero e z he,
      mul_zero]
  calc
    ‖z‖ ^ 2 = ‖a • e + u‖ ^ 2 := by rw [hdecomp]
    _ = ‖a • e‖ ^ 2 + ‖u‖ ^ 2 :=
        by simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real horth
    _ = a ^ 2 + ‖u‖ ^ 2 := by
        rw [norm_smul, he, mul_one, Real.norm_eq_abs, sq_abs]

/-- On the cap cone, vanishing of the cap-flattening radicand is exactly
equality in the ambient cone inequality. -/
theorem finRealSphereRadialOpenCone_closedHalfspace_boundary_eq_of_radicand_eq_zero
    {n : ℕ} [NeZero n] (e : FinRealEuclideanSpace n)
    {r : ℝ} (he : ‖e‖ = 1) (hrpos : 0 < r) (hrlt : r < Real.pi / 2)
    {z : FinRealEuclideanSpace n}
    (hz : z ∈ finRealSphereRadialOpenCone n
        (finRealSphereClosedHalfspace n e (Real.sin r)))
    (hq : finRealSphereCapConeRadicand e r z = 0) :
    Real.sin r * ‖z‖ = inner ℝ e z := by
  let a : ℝ := inner ℝ e z
  let u : FinRealEuclideanSpace n := finRealSphereCapConeOrthogonalComponent e z
  have hmem := (finRealSphereRadialOpenCone_closedHalfspace_mem_iff e (Real.sin r)).mp hz
  have hineq : Real.sin r * ‖z‖ ≤ a := by
    simpa [a] using hmem.2.2
  have hr0 : 0 ≤ r := le_of_lt hrpos
  have hrle : r ≤ Real.pi / 2 := le_of_lt hrlt
  have hsin_nonneg : 0 ≤ Real.sin r :=
    Real.sin_nonneg_of_nonneg_of_le_pi hr0 (by linarith [Real.pi_pos, hrle])
  have hcos_pos : 0 < Real.cos r :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hrpos], hrlt⟩
  have hleft_nonneg : 0 ≤ Real.sin r * ‖z‖ :=
    mul_nonneg hsin_nonneg (norm_nonneg z)
  have ha_nonneg : 0 ≤ a := le_trans hleft_nonneg hineq
  have hq' :
      a ^ 2 = (Real.sin r / Real.cos r) ^ 2 * ‖u‖ ^ 2 := by
    have hq0 : a ^ 2 - (Real.sin r / Real.cos r) ^ 2 * ‖u‖ ^ 2 = 0 := by
      simpa [finRealSphereCapConeRadicand, a, u] using hq
    linarith
  have hnormsq :
      ‖z‖ ^ 2 = a ^ 2 + ‖u‖ ^ 2 := by
    simpa [a, u] using
      finRealSphereCapConeOrthogonalComponent_norm_sq_eq e z he
  have hsquare :
      (Real.sin r * ‖z‖) ^ 2 = a ^ 2 := by
    have hcos_ne : Real.cos r ≠ 0 := hcos_pos.ne'
    have htrig : Real.sin r ^ 2 + Real.cos r ^ 2 = 1 :=
      Real.sin_sq_add_cos_sq r
    calc
      (Real.sin r * ‖z‖) ^ 2
          = Real.sin r ^ 2 * ‖z‖ ^ 2 := by ring
      _ = Real.sin r ^ 2 * (a ^ 2 + ‖u‖ ^ 2) := by rw [hnormsq]
      _ = Real.sin r ^ 2 *
            ((Real.sin r / Real.cos r) ^ 2 * ‖u‖ ^ 2 + ‖u‖ ^ 2) := by
              rw [hq']
      _ = (Real.sin r / Real.cos r) ^ 2 * ‖u‖ ^ 2 := by
              field_simp [hcos_ne]
              rw [htrig]
              ring
      _ = a ^ 2 := hq'.symm
  exact (sq_eq_sq₀ hleft_nonneg ha_nonneg).mp hsquare

/-- On the cap cone, the radicand-zero locus lies on the frontier of the
ambient closed cone.  The exterior-closure side is witnessed by moving an
arbitrarily small amount in the `-e` direction: equality is broken because
`sin r < 1`. -/
theorem finRealSphereRadialOpenCone_closedHalfspace_mem_frontier_of_radicand_eq_zero
    {n : ℕ} [NeZero n] (e : FinRealEuclideanSpace n)
    {r : ℝ} (he : ‖e‖ = 1) (hrpos : 0 < r) (hrlt : r < Real.pi / 2)
    {z : FinRealEuclideanSpace n}
    (hz : z ∈ finRealSphereRadialOpenCone n
        (finRealSphereClosedHalfspace n e (Real.sin r)))
    (hq : finRealSphereCapConeRadicand e r z = 0) :
    z ∈ frontier (finRealSphereClosedHalfspaceAmbientCone e (Real.sin r)) := by
  let A : Set (FinRealEuclideanSpace n) :=
    finRealSphereClosedHalfspaceAmbientCone e (Real.sin r)
  have heinner : inner ℝ e e = 1 := by
    simp [he]
  have hr0 : 0 ≤ r := le_of_lt hrpos
  have hrle : r ≤ Real.pi / 2 := le_of_lt hrlt
  have hsin_nonneg : 0 ≤ Real.sin r :=
    Real.sin_nonneg_of_nonneg_of_le_pi hr0 (by linarith [Real.pi_pos, hrle])
  have hsin_lt_one : Real.sin r < 1 := by
    rw [← Real.sin_pi_div_two]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (by linarith [Real.pi_pos, hrpos]) (le_refl _) hrlt
  have heq : Real.sin r * ‖z‖ = inner ℝ e z :=
    finRealSphereRadialOpenCone_closedHalfspace_boundary_eq_of_radicand_eq_zero
      e he hrpos hrlt hz hq
  have hzA : z ∈ A := by
    change Real.sin r * ‖z‖ ≤ inner ℝ e z
    exact le_of_eq heq
  have hzClosure : z ∈ closure A := subset_closure hzA
  have hzComplClosure : z ∈ closure Aᶜ := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    let δ : ℝ := ε / 2
    let y : FinRealEuclideanSpace n := z - δ • e
    have hδpos : 0 < δ := by
      dsimp [δ]
      positivity
    have hδlt : δ < ε := by
      dsimp [δ]
      linarith
    have hnorm_smul : ‖δ • e‖ = δ := by
      rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos hδpos]
    have hzy : z = y + δ • e := by
      dsimp [y]
      abel
    have hnorm_lower : ‖z‖ - δ ≤ ‖y‖ := by
      have htri : ‖z‖ ≤ ‖y‖ + δ := by
        calc
          ‖z‖ = ‖y + δ • e‖ := by rw [hzy]
          _ ≤ ‖y‖ + ‖δ • e‖ := norm_add_le _ _
          _ = ‖y‖ + δ := by rw [hnorm_smul]
      linarith
    have hmul_lower : Real.sin r * (‖z‖ - δ) ≤ Real.sin r * ‖y‖ :=
      mul_le_mul_of_nonneg_left hnorm_lower hsin_nonneg
    have hinner_y : inner ℝ e y = inner ℝ e z - δ := by
      dsimp [y]
      rw [inner_sub_right, inner_smul_right, heinner, mul_one]
    have hsin_delta_lt_delta : Real.sin r * δ < δ := by
      have := mul_lt_mul_of_pos_right hsin_lt_one hδpos
      simpa using this
    have hinner_lt_lower : inner ℝ e y < Real.sin r * (‖z‖ - δ) := by
      calc
        inner ℝ e y = Real.sin r * ‖z‖ - δ := by rw [hinner_y, ← heq]
        _ < Real.sin r * ‖z‖ - Real.sin r * δ := by linarith
        _ = Real.sin r * (‖z‖ - δ) := by ring
    have hy_not_A : y ∈ Aᶜ := by
      intro hyA
      have hyAineq : Real.sin r * ‖y‖ ≤ inner ℝ e y := by
        change y ∈ finRealSphereClosedHalfspaceAmbientCone e (Real.sin r) at hyA
        exact hyA
      exact (not_le.mpr (lt_of_lt_of_le hinner_lt_lower hmul_lower)) hyAineq
    refine ⟨y, hy_not_A, ?_⟩
    rw [dist_eq_norm]
    have hdiff : z - y = δ • e := by
      dsimp [y]
      abel
    rw [hdiff, hnorm_smul]
    exact hδlt
  rw [frontier_eq_closure_inter_closure]
  exact ⟨hzClosure, hzComplClosure⟩

/-- The cap-cone radicand-zero locus has zero ambient Haar measure. -/
theorem finRealSphereRadialOpenCone_closedHalfspace_radicand_zero_measure_zero
    {n : ℕ} [NeZero n] (e : FinRealEuclideanSpace n)
    {r : ℝ} (he : ‖e‖ = 1) (hrpos : 0 < r) (hrlt : r < Real.pi / 2) :
    (finRealHaarMeasure n)
      {z : FinRealEuclideanSpace n |
        z ∈ finRealSphereRadialOpenCone n
          (finRealSphereClosedHalfspace n e (Real.sin r)) ∧
        finRealSphereCapConeRadicand e r z = 0} = 0 := by
  have hr0 : 0 ≤ r := le_of_lt hrpos
  have hrle : r ≤ Real.pi / 2 := le_of_lt hrlt
  have hsin_nonneg : 0 ≤ Real.sin r :=
    Real.sin_nonneg_of_nonneg_of_le_pi hr0 (by linarith [Real.pi_pos, hrle])
  refine MeasureTheory.measure_mono_null
    (t := frontier (finRealSphereClosedHalfspaceAmbientCone e (Real.sin r)))
    ?_ ?_
  · intro z hz
    exact
      finRealSphereRadialOpenCone_closedHalfspace_mem_frontier_of_radicand_eq_zero
        e he hrpos hrlt hz.1 hz.2
  · exact finRealSphereClosedHalfspaceAmbientCone_frontier_measure_zero e hsin_nonneg

/-- The derivative of the orthogonal-component map is the orthogonal projection
when the axis is unit. -/
theorem finRealSphereCapConeOrthogonalComponentFDeriv_apply
    {n : ℕ} (e : FinRealEuclideanSpace n)
    (v : FinRealEuclideanSpace n) :
    finRealSphereCapConeOrthogonalComponentFDeriv e v =
      v - (inner ℝ e v) • e := by
  simp [finRealSphereCapConeOrthogonalComponentFDeriv]

/-- The projection derivative kills the unit axis. -/
theorem finRealSphereCapConeOrthogonalComponentFDeriv_apply_axis
    {n : ℕ} (e : FinRealEuclideanSpace n) (he : ‖e‖ = 1) :
    finRealSphereCapConeOrthogonalComponentFDeriv e e = 0 := by
  rw [finRealSphereCapConeOrthogonalComponentFDeriv_apply]
  simp [he]

/-- The projection derivative fixes vectors orthogonal to the axis. -/
theorem finRealSphereCapConeOrthogonalComponentFDeriv_apply_of_inner_eq_zero
    {n : ℕ} (e : FinRealEuclideanSpace n)
    {v : FinRealEuclideanSpace n} (hv : inner ℝ e v = 0) :
    finRealSphereCapConeOrthogonalComponentFDeriv e v = v := by
  rw [finRealSphereCapConeOrthogonalComponentFDeriv_apply, hv, zero_smul, sub_zero]

/-- The projection derivative fixes the orthogonal component itself. -/
theorem finRealSphereCapConeOrthogonalComponentFDeriv_apply_orthogonalComponent
    {n : ℕ} (e : FinRealEuclideanSpace n) (z : FinRealEuclideanSpace n)
    (he : ‖e‖ = 1) :
    finRealSphereCapConeOrthogonalComponentFDeriv e
        (finRealSphereCapConeOrthogonalComponent e z) =
      finRealSphereCapConeOrthogonalComponent e z :=
  finRealSphereCapConeOrthogonalComponentFDeriv_apply_of_inner_eq_zero e
    (finRealSphereCapConeOrthogonalComponent_inner_eq_zero e z he)

/-- The radicand derivative in the axial direction. -/
theorem finRealSphereCapConeRadicandFDeriv_apply_axis
    {n : ℕ} (e : FinRealEuclideanSpace n) (r : ℝ)
    (z : FinRealEuclideanSpace n) (he : ‖e‖ = 1) :
    finRealSphereCapConeRadicandFDeriv e r z e =
      2 * inner ℝ e z := by
  simp [finRealSphereCapConeRadicandFDeriv,
    finRealSphereCapConeOrthogonalComponentFDeriv_apply_axis e he,
    he]

/-- The radicand derivative vanishes on directions orthogonal to both the axis
and the current orthogonal component. -/
theorem finRealSphereCapConeRadicandFDeriv_apply_orthogonalBlock
    {n : ℕ} (e : FinRealEuclideanSpace n) (r : ℝ)
    (z : FinRealEuclideanSpace n) {w : FinRealEuclideanSpace n}
    (hwe : inner ℝ e w = 0)
    (hwu : inner ℝ (finRealSphereCapConeOrthogonalComponent e z) w = 0) :
    finRealSphereCapConeRadicandFDeriv e r z w = 0 := by
  simp [finRealSphereCapConeRadicandFDeriv,
    finRealSphereCapConeOrthogonalComponentFDeriv_apply_of_inner_eq_zero e hwe,
    hwe, hwu]

/-- The radicand derivative in the orthogonal-component direction. -/
theorem finRealSphereCapConeRadicandFDeriv_apply_orthogonalComponent
    {n : ℕ} (e : FinRealEuclideanSpace n) (r : ℝ)
    (z : FinRealEuclideanSpace n) (he : ‖e‖ = 1) :
    finRealSphereCapConeRadicandFDeriv e r z
        (finRealSphereCapConeOrthogonalComponent e z) =
      -((Real.sin r / Real.cos r) ^ 2 *
        (2 * ‖finRealSphereCapConeOrthogonalComponent e z‖ ^ 2)) := by
  have huinner :=
    finRealSphereCapConeOrthogonalComponent_inner_eq_zero e z he
  simp [finRealSphereCapConeRadicandFDeriv,
    finRealSphereCapConeOrthogonalComponentFDeriv_apply_orthogonalComponent e z he,
    huinner, mul_left_comm, mul_comm]

/-- The cap-flattening derivative sends the axis to the expected axial vector.
This is the first diagonal entry in the determinant computation. -/
theorem finRealSphereCapConeFlatteningMapFDeriv_apply_axis
    {n : ℕ} (e : FinRealEuclideanSpace n) (r : ℝ)
    (z : FinRealEuclideanSpace n) (he : ‖e‖ = 1) :
    finRealSphereCapConeFlatteningMapFDeriv e r z e =
      ((inner ℝ e z) /
        Real.sqrt (finRealSphereCapConeRadicand e r z)) • e := by
  simp [finRealSphereCapConeFlatteningMapFDeriv,
    finRealSphereCapConeRadicandFDeriv_apply_axis e r z he,
    finRealSphereCapConeOrthogonalComponentFDeriv_apply_axis e he]
  ring_nf

/-- On the block orthogonal to both the axis and the current orthogonal
component, the cap-flattening derivative is scalar multiplication by
`(cos r)⁻¹`.  This is the repeated diagonal block in the determinant
computation. -/
theorem finRealSphereCapConeFlatteningMapFDeriv_apply_orthogonalBlock
    {n : ℕ} (e : FinRealEuclideanSpace n) (r : ℝ)
    (z : FinRealEuclideanSpace n) {w : FinRealEuclideanSpace n}
    (hwe : inner ℝ e w = 0)
    (hwu : inner ℝ (finRealSphereCapConeOrthogonalComponent e z) w = 0) :
    finRealSphereCapConeFlatteningMapFDeriv e r z w =
      (Real.cos r)⁻¹ • w := by
  simp [finRealSphereCapConeFlatteningMapFDeriv,
    finRealSphereCapConeRadicandFDeriv_apply_orthogonalBlock e r z hwe hwu,
    finRealSphereCapConeOrthogonalComponentFDeriv_apply_of_inner_eq_zero e hwe]

/-- In the current orthogonal-component direction, the derivative has an
upper-triangular form: an axial correction plus the same `(cos r)⁻¹` multiple
of the orthogonal component. -/
theorem finRealSphereCapConeFlatteningMapFDeriv_apply_orthogonalComponent
    {n : ℕ} (e : FinRealEuclideanSpace n) (r : ℝ)
    (z : FinRealEuclideanSpace n) (he : ‖e‖ = 1) :
    finRealSphereCapConeFlatteningMapFDeriv e r z
        (finRealSphereCapConeOrthogonalComponent e z) =
      (-(Real.sin r / Real.cos r) ^ 2 *
          ‖finRealSphereCapConeOrthogonalComponent e z‖ ^ 2 /
          Real.sqrt (finRealSphereCapConeRadicand e r z)) • e +
        (Real.cos r)⁻¹ • finRealSphereCapConeOrthogonalComponent e z := by
  simp [finRealSphereCapConeFlatteningMapFDeriv,
    finRealSphereCapConeRadicandFDeriv_apply_orthogonalComponent e r z he,
    finRealSphereCapConeOrthogonalComponentFDeriv_apply_orthogonalComponent e z he,
    mul_assoc]
  ring_nf
  rw [neg_smul]

/-- On any vector orthogonal to the axis, the cap-flattening derivative is an
axial correction plus scalar multiplication by `(cos r)⁻¹`.  This is the
block-triangular form used by the determinant computation. -/
theorem finRealSphereCapConeFlatteningMapFDeriv_apply_of_inner_eq_zero
    {n : ℕ} (e : FinRealEuclideanSpace n) (r : ℝ)
    (z : FinRealEuclideanSpace n) {w : FinRealEuclideanSpace n}
    (hwe : inner ℝ e w = 0) :
    ∃ γ : ℝ,
      finRealSphereCapConeFlatteningMapFDeriv e r z w =
        γ • e + (Real.cos r)⁻¹ • w := by
  refine ⟨((1 / (2 * Real.sqrt (finRealSphereCapConeRadicand e r z))) *
      finRealSphereCapConeRadicandFDeriv e r z w), ?_⟩
  simp [finRealSphereCapConeFlatteningMapFDeriv,
    finRealSphereCapConeOrthogonalComponentFDeriv_apply_of_inner_eq_zero e hwe]

/-- Block-triangular determinant lemma for a unit axis.  If a linear map sends
the axis to `α` times the axis and sends every vector orthogonal to the axis to
an arbitrary axial correction plus `β` times that vector, then its determinant
is `α * β^(n-1)`. -/
theorem axis_tangent_block_det
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {n : ℕ} (hn : 1 < n) {e : E} (he : ‖e‖ = 1)
    (hE : Module.finrank ℝ E = n)
    (L : E →L[ℝ] E) (α β : ℝ)
    (h_axis : L e = α • e)
    (h_tang :
      ∀ w : E, inner ℝ e w = 0 →
        ∃ γ : ℝ, L w = γ • e + β • w) :
    L.det = α * β ^ (n - 1) := by
  classical
  have hn2 : n = n - 2 + 2 := by omega
  have hn1 : n - 2 + 1 = n - 1 := by omega
  let tang := tangentSubspace e
  have hfin_tang : Module.finrank ℝ tang = n - 1 := by
    have hene : e ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at he
      norm_num at he
    let S : Submodule ℝ E := Submodule.span ℝ ({e} : Set E)
    have hSfin : Module.finrank ℝ S = 1 := finrank_span_singleton hene
    have heq : tang = Sᗮ := by
      ext w
      constructor
      · intro hw
        rw [Submodule.mem_orthogonal]
        intro u hu
        rcases Submodule.mem_span_singleton.mp hu with ⟨c, rfl⟩
        rw [mem_tangentSubspace_iff] at hw
        rw [inner_smul_left, hw, mul_zero]
      · intro hw
        rw [mem_tangentSubspace_iff]
        have := hw e (Submodule.subset_span (by simp))
        simpa using this
    rw [heq]
    have hsum := Submodule.finrank_add_finrank_orthogonal (K := S)
    rw [hSfin, hE] at hsum
    omega
  have hfin' : Module.finrank ℝ tang = n - 2 + 1 := by omega
  let b_tang := (stdOrthonormalBasis ℝ tang).reindex (finCongr hfin')
  let tangVec : Fin (n - 2 + 1) → E := fun i => (b_tang i : E)
  have horth_tang : Orthonormal ℝ tangVec := b_tang.orthonormal
  have horth_v : ∀ i, inner ℝ e (tangVec i) = 0 := by
    intro i
    exact (mem_tangentSubspace_iff).1 (b_tang i).2
  have horth_frame : Orthonormal ℝ (Fin.cons e tangVec) :=
    finCons_unit_orthonormal (m := n - 2) he horth_tang horth_v
  let frame : Fin (n - 2 + 2) → E := fun i =>
    if h0 : i = 0 then e else tangVec (Fin.pred i h0)
  have heqframe : frame = Fin.cons e tangVec := by
    ext i
    cases i using Fin.cases with
    | zero => simp [frame, Fin.cons_zero]
    | succ j => simp [frame, Fin.cons_succ, Fin.pred_succ]
  have horth_frame' : Orthonormal ℝ frame := by
    rw [heqframe]
    exact horth_frame
  have hspan : Submodule.span ℝ (Set.range frame) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hE, finrank_span_eq_card horth_frame'.linearIndependent, Fintype.card_fin]
    exact hn2.symm
  let b_basis :=
    Module.Basis.mk (v := frame) horth_frame'.linearIndependent (hspan ▸ le_rfl)
  have hb0 : b_basis 0 = e := by
    simp [b_basis, frame]
  have hbsucc : ∀ i : Fin (n - 2 + 1), b_basis (Fin.succ i) = tangVec i := by
    intro i
    simp [b_basis, frame, Fin.pred_succ]
  let M : Matrix (Fin (n - 2 + 2)) (Fin (n - 2 + 2)) ℝ :=
    (LinearMap.toMatrix b_basis b_basis) L.toLinearMap
  have hM00 : M 0 0 = α := by
    dsimp [M]
    rw [LinearMap.toMatrix_apply, hb0]
    change (b_basis.repr (L e)) 0 = α
    rw [h_axis]
    rw [← hb0]
    simp
  have hMsucc0 : ∀ i : Fin (n - 2 + 1), M (Fin.succ i) 0 = 0 := by
    intro i
    dsimp [M]
    rw [LinearMap.toMatrix_apply, hb0]
    change (b_basis.repr (L e)) (Fin.succ i) = 0
    rw [h_axis]
    rw [← hb0]
    simp
  have hMsuccsucc : ∀ i j : Fin (n - 2 + 1),
      M (Fin.succ i) (Fin.succ j) = if i = j then β else 0 := by
    intro i j
    dsimp [M]
    rw [LinearMap.toMatrix_apply, hbsucc j]
    change (b_basis.repr (L (tangVec j))) (Fin.succ i) =
      if i = j then β else 0
    obtain ⟨γ, hγ⟩ := h_tang (tangVec j) (horth_v j)
    rw [hγ]
    by_cases hij : i = j
    · subst i
      rw [← hb0, ← hbsucc j]
      simp
    · rw [← hb0, ← hbsucc j]
      have hs : (Fin.succ i : Fin (n - 2 + 2)) ≠ Fin.succ j := by
        intro h
        apply hij
        apply Fin.ext
        have hv := congrArg Fin.val h
        simp at hv
        omega
      simp [hij, Finsupp.single_eq_of_ne hs]
  have hupper : M.BlockTriangular id := by
    intro i j hij
    cases i using Fin.cases with
    | zero =>
      simp at hij
    | succ i =>
      cases j using Fin.cases with
      | zero => exact hMsucc0 i
      | succ j =>
        have hij' : j ≠ i := by
          intro hji
          subst hji
          simp at hij
        rw [hMsuccsucc i j]
        simp [hij'.symm]
  have hdetM : M.det = α * β ^ (n - 1) := by
    rw [Matrix.det_of_upperTriangular hupper]
    rw [Fin.prod_univ_succ]
    rw [hM00]
    have hdiag : ∀ i : Fin (n - 2 + 1), M (Fin.succ i) (Fin.succ i) = β := by
      intro i
      rw [hMsuccsucc i i]
      simp
    rw [Finset.prod_congr rfl (fun x _ => hdiag x)]
    simp [hn1]
  have hdet_to_matrix : M.det = LinearMap.det L.toLinearMap := by
    simp [M, LinearMap.det_toMatrix b_basis L.toLinearMap]
  rw [ContinuousLinearMap.det]
  rw [← hdet_to_matrix]
  exact hdetM

/-- Exact determinant of the cap-flattening derivative on its differentiability
locus.  The determinant computation is purely block triangular: axial scale
`⟪e,z⟫ / sqrt(q_r(z))` and tangent scale `(cos r)⁻¹`. -/
theorem finRealSphereCapConeFlatteningMapFDeriv_det_eq
    {n : ℕ} [NeZero n] (hn2 : 2 ≤ n)
    (e : FinRealEuclideanSpace n) (r : ℝ)
    (z : FinRealEuclideanSpace n) (he : ‖e‖ = 1) :
    (finRealSphereCapConeFlatteningMapFDeriv e r z).det =
      ((inner ℝ e z) /
          Real.sqrt (finRealSphereCapConeRadicand e r z)) *
        (Real.cos r)⁻¹ ^ (n - 1) := by
  have hn : 1 < n := by omega
  have hE : Module.finrank ℝ (FinRealEuclideanSpace n) = n := by
    rw [finRealSphere_moduleFinrank]
  exact
    axis_tangent_block_det
      (n := n) hn (e := e) he hE
      (finRealSphereCapConeFlatteningMapFDeriv e r z)
      ((inner ℝ e z) / Real.sqrt (finRealSphereCapConeRadicand e r z))
      (Real.cos r)⁻¹
      (finRealSphereCapConeFlatteningMapFDeriv_apply_axis e r z he)
      (fun w hw =>
        finRealSphereCapConeFlatteningMapFDeriv_apply_of_inner_eq_zero e r z hw)

/-- Determinant lower bound for the cap-flattening derivative on the
nonzero-radicand locus.  After the exact determinant formula, this is the
scalar comparison `sqrt(q_r(z)) ≤ ⟪e,z⟫` coming from the cap-cone radicand
inequality. -/
theorem finRealSphereCapConeFlatteningMapFDeriv_detLowerBound
    {n : ℕ} [NeZero n] (hn2 : 2 ≤ n)
    (e : FinRealEuclideanSpace n) {r : ℝ}
    (he : ‖e‖ = 1) (hrpos : 0 < r) (hrlt : r < Real.pi / 2)
    {z : FinRealEuclideanSpace n}
    (hz : z ∈ finRealSphereRadialOpenCone n
        (finRealSphereClosedHalfspace n e (Real.sin r)))
    (hq : finRealSphereCapConeRadicand e r z ≠ 0) :
    (1 : ℝ≥0∞) ≤
      ENNReal.ofReal (Real.cos r ^ (n - 1)) *
        ENNReal.ofReal |(finRealSphereCapConeFlatteningMapFDeriv e r z).det| := by
  let a : ℝ := inner ℝ e z
  let q : ℝ := finRealSphereCapConeRadicand e r z
  let u : FinRealEuclideanSpace n := finRealSphereCapConeOrthogonalComponent e z
  have htan_sq :
      (Real.sin r / Real.cos r) ^ 2 * ‖u‖ ^ 2 ≤ a ^ 2 := by
    simpa [a, u, finRealSphereCapConeOrthogonalComponent] using
      finRealSphereRadialOpenCone_closedHalfspace_tan_sq_mul_orthogonalProjection_norm_sq_le_inner_sq
        e he hrpos hrlt hz
  have hq_nonneg : 0 ≤ q := by
    dsimp [q, finRealSphereCapConeRadicand, a, u]
    linarith
  have hq_ne : q ≠ 0 := by
    simpa [q] using hq
  have hq_pos : 0 < q := lt_of_le_of_ne hq_nonneg (Ne.symm hq_ne)
  have hmem :=
    (finRealSphereRadialOpenCone_closedHalfspace_mem_iff e (Real.sin r)).mp hz
  have ha_nonneg : 0 ≤ a := by
    have hineq : Real.sin r * ‖z‖ ≤ a := by
      simpa [a] using hmem.2.2
    have hr0 : 0 ≤ r := le_of_lt hrpos
    have hrle : r ≤ Real.pi / 2 := le_of_lt hrlt
    have hsin_nonneg : 0 ≤ Real.sin r :=
      Real.sin_nonneg_of_nonneg_of_le_pi hr0 (by linarith [Real.pi_pos, hrle])
    exact le_trans (mul_nonneg hsin_nonneg (norm_nonneg z)) hineq
  have hq_le_a_sq : q ≤ a ^ 2 := by
    have hnonneg :
        0 ≤ (Real.sin r / Real.cos r) ^ 2 * ‖u‖ ^ 2 := by
      positivity
    dsimp [q, finRealSphereCapConeRadicand, a, u]
    linarith
  have hsqrt_le_a : Real.sqrt q ≤ a := by
    rw [← (sq_le_sq₀ (Real.sqrt_nonneg q) ha_nonneg)]
    simpa [Real.sq_sqrt hq_nonneg] using hq_le_a_sq
  have hsqrt_pos : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq_pos
  have hone_le_ratio : 1 ≤ a / Real.sqrt q :=
    (one_le_div hsqrt_pos).mpr hsqrt_le_a
  have hcos_pos : 0 < Real.cos r :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hrpos], hrlt⟩
  have hcos_pow_nonneg : 0 ≤ Real.cos r ^ (n - 1) :=
    pow_nonneg (le_of_lt hcos_pos) _
  have hratio_nonneg : 0 ≤ a / Real.sqrt q :=
    le_trans zero_le_one hone_le_ratio
  have hinv_pow_nonneg : 0 ≤ (Real.cos r)⁻¹ ^ (n - 1) :=
    pow_nonneg (le_of_lt (inv_pos.mpr hcos_pos)) _
  have hdet_abs :
      |(finRealSphereCapConeFlatteningMapFDeriv e r z).det| =
        (a / Real.sqrt q) * (Real.cos r)⁻¹ ^ (n - 1) := by
    rw [finRealSphereCapConeFlatteningMapFDeriv_det_eq hn2 e r z he]
    exact abs_of_nonneg (mul_nonneg hratio_nonneg hinv_pow_nonneg)
  have hpow_cancel :
      Real.cos r ^ (n - 1) * (Real.cos r)⁻¹ ^ (n - 1) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hcos_pos.ne', one_pow]
  have hreal :
      1 ≤
        Real.cos r ^ (n - 1) *
          |(finRealSphereCapConeFlatteningMapFDeriv e r z).det| := by
    rw [hdet_abs]
    calc
      1 ≤ a / Real.sqrt q := hone_le_ratio
      _ = Real.cos r ^ (n - 1) *
            ((a / Real.sqrt q) * (Real.cos r)⁻¹ ^ (n - 1)) := by
          symm
          calc
            Real.cos r ^ (n - 1) *
                ((a / Real.sqrt q) * (Real.cos r)⁻¹ ^ (n - 1)) =
              (a / Real.sqrt q) *
                (Real.cos r ^ (n - 1) * (Real.cos r)⁻¹ ^ (n - 1)) := by
                ring
            _ = a / Real.sqrt q := by rw [hpow_cancel, mul_one]
  rw [← ENNReal.ofReal_mul hcos_pow_nonneg]
  simpa [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hreal

/-- The radial direction maps the open cone of `S` into `S`. -/
theorem finRealSphereRadialDirectionFrom_mapsTo_openCone
    {n : ℕ} (u : FinRealSphere n) (S : Set (FinRealSphere n)) :
    Set.MapsTo (finRealSphereRadialDirectionFrom (n := n) u)
      (finRealSphereRadialOpenCone n S) S := by
  rintro z ⟨r, hr, w, ⟨x, hx, rfl⟩, rfl⟩
  rw [finRealSphereRadialDirectionFrom_smul u x hr.1]
  exact hx

/-- Symmetric difference between `(B \ {0}) ∩ dir⁻¹(S)` and `cone(S)`: both sides
agree pointwise away from the origin. -/
theorem finRealSphereRadialOpenCone_eq_ball_inter_direction_preimage_diff_zero
    {n : ℕ} (u : FinRealSphere n) (S : Set (FinRealSphere n)) :
    finRealSphereRadialOpenCone n S =
      (Metric.ball (0 : FinRealEuclideanSpace n) 1 \ {0}) ∩
        (finRealSphereRadialDirectionFrom (n := n) u ⁻¹' S) := by
  classical
  ext z
  constructor
  · intro hz
    refine ⟨⟨finRealSphereRadialOpenCone_subset_ball S hz, ?_⟩,
      finRealSphereRadialDirectionFrom_mapsTo_openCone u S hz⟩
    rcases hz with ⟨r, hr, w, ⟨x, _hx, rfl⟩, rfl⟩
    exact smul_ne_zero hr.1.ne' (finRealSphere_ne_zero n x)
  · rintro ⟨⟨hball, hne⟩, hdir⟩
    have hne' : z ≠ 0 := by
      intro h0
      exact hne (by simp [h0])
    have hnorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hne'
    have hnorm_lt : ‖z‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hball
    refine ⟨‖z‖, ⟨hnorm_pos, hnorm_lt⟩,
      ‖z‖⁻¹ • z, ⟨finRealSphereRadialDirectionFrom (n := n) u z, hdir, ?_⟩, ?_⟩
    · show (finRealSphereRadialDirectionFrom (n := n) u z :
          FinRealEuclideanSpace n) = ‖z‖⁻¹ • z
      unfold finRealSphereRadialDirectionFrom
      rw [dif_neg hne']
    · show ‖z‖ • (‖z‖⁻¹ • z) = z
      rw [smul_smul, mul_inv_cancel₀ hnorm_pos.ne', one_smul]

/-- Key measure identity: the unnormalised surface measure equals the ambient
dimension scalar times the pushforward of the open unit ball Haar mass by the
radial direction projection.

Mathematically this is the integral form of `toSphere_apply'` packaged as a
measure equality.  The proof goes through `toSphere_apply'` set-by-set,
identifying the cone of `A` with `(B \ {0}) ∩ dir⁻¹(A)` and noting that the
singleton `{0}` is `IsAddHaarMeasure`-null. -/
theorem finRealSurfaceMeasure_eq_finrank_smul_map_radialDirection
    {n : ℕ} [NeZero n] (u : FinRealSphere n) :
    finRealSurfaceMeasure n =
      (Module.finrank ℝ (FinRealEuclideanSpace n) : ℝ≥0∞) •
        Measure.map (finRealSphereRadialDirectionFrom (n := n) u)
          ((finRealHaarMeasure n).restrict
            (Metric.ball (0 : FinRealEuclideanSpace n) 1)) := by
  haveI : (finRealHaarMeasure n).IsAddHaarMeasure := by
    unfold finRealHaarMeasure; infer_instance
  haveI : Nontrivial (FinRealEuclideanSpace n) := by
    refine ⟨EuclideanSpace.single ⟨0, ?_⟩ (1 : ℝ), 0, ?_⟩
    · exact Nat.pos_of_ne_zero (NeZero.ne n)
    · intro h
      have := congrArg (fun f : FinRealEuclideanSpace n => f ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩) h
      simp at this
  haveI : NoAtoms (finRealHaarMeasure n) := inferInstance
  have hdir_meas : Measurable (finRealSphereRadialDirectionFrom (n := n) u) :=
    measurable_finRealSphereRadialDirectionFrom u
  ext A hA
  rw [Measure.smul_apply, Measure.map_apply hdir_meas hA,
    Measure.restrict_apply (hdir_meas hA)]
  -- LHS = (haar.toSphere) A.
  change (finRealHaarMeasure n).toSphere A = _
  rw [Measure.toSphere_apply' _ hA]
  -- Need to identify (0,1) • ↑'' A with dir⁻¹(A) ∩ ball (up to a null set).
  congr 1
  have hcone_eq :
      Set.Ioo (0 : ℝ) 1 •
            ((↑) : FinRealSphere n → FinRealEuclideanSpace n) '' A =
        (Metric.ball (0 : FinRealEuclideanSpace n) 1 \ {0}) ∩
          (finRealSphereRadialDirectionFrom (n := n) u ⁻¹' A) := by
    have := finRealSphereRadialOpenCone_eq_ball_inter_direction_preimage_diff_zero
      (n := n) u A
    simpa [finRealSphereRadialOpenCone] using this
  rw [hcone_eq]
  -- Now reduce to the haar measure being unchanged by removing {0}.
  set Bset := Metric.ball (0 : FinRealEuclideanSpace n) 1
  set Aset := finRealSphereRadialDirectionFrom (n := n) u ⁻¹' A
  -- We want (Bset \ {0}) ∩ Aset = Aset ∩ Bset modulo the singleton {0}.
  -- Use measure_diff_null or directly union argument.
  have hBnull : (finRealHaarMeasure n) ({(0 : FinRealEuclideanSpace n)}) = 0 :=
    measure_singleton _
  have hsubeq :
      (Bset \ {0}) ∩ Aset = (Bset ∩ Aset) \ ({0} ∩ Aset) := by
    ext z; constructor
    · rintro ⟨⟨hb, hne⟩, ha⟩
      refine ⟨⟨hb, ha⟩, ?_⟩
      rintro ⟨h0, _⟩
      exact hne h0
    · rintro ⟨⟨hb, ha⟩, hne0⟩
      refine ⟨⟨hb, ?_⟩, ha⟩
      intro h0
      exact hne0 ⟨h0, ha⟩
  rw [hsubeq]
  -- `{0} ∩ Aset` has haar measure 0 (subset of {0}).
  have hnull_inter : (finRealHaarMeasure n) ({(0 : FinRealEuclideanSpace n)} ∩ Aset) = 0 := by
    apply measure_mono_null (Set.inter_subset_left) hBnull
  -- Use measure_diff_null.
  rw [show (Bset ∩ Aset) \ ({0} ∩ Aset) =
      (Bset ∩ Aset) \ ((Bset ∩ Aset) ∩ ({0} ∩ Aset)) by
    rw [Set.diff_self_inter]]
  -- (Bset ∩ Aset) \ (subset of null) has same measure.
  have hsub_null :
      (finRealHaarMeasure n) ((Bset ∩ Aset) ∩ ({0} ∩ Aset)) = 0 := by
    apply measure_mono_null (Set.inter_subset_right) hnull_inter
  rw [measure_diff_null hsub_null, Set.inter_comm Aset Bset]

/-- General Cone bridge: lintegral on the sphere lifts to a Haar integral on
the open unit ball with the radial pull-back integrand. -/
theorem lintegral_finRealSurfaceProbabilityMeasure_eq_cone
    {n : ℕ} [NeZero n] (u : FinRealSphere n)
    {S : Set (FinRealSphere n)} (hS : MeasurableSet S)
    (F : FinRealSphere n → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x in S, F x ∂(finRealSurfaceProbabilityMeasure n)) =
      (finRealHaarMeasure n (Metric.ball (0 : FinRealEuclideanSpace n) 1))⁻¹ *
        ∫⁻ z in finRealSphereRadialOpenCone n S,
          F (finRealSphereRadialDirectionFrom (n := n) u z)
          ∂(finRealHaarMeasure n) := by
  haveI : (finRealHaarMeasure n).IsAddHaarMeasure := by
    unfold finRealHaarMeasure; infer_instance
  haveI : Nontrivial (FinRealEuclideanSpace n) := by
    refine ⟨EuclideanSpace.single ⟨0, ?_⟩ (1 : ℝ), 0, ?_⟩
    · exact Nat.pos_of_ne_zero (NeZero.ne n)
    · intro h
      have :=
        congrArg (fun f : FinRealEuclideanSpace n =>
          f ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩) h
      simp at this
  haveI : NoAtoms (finRealHaarMeasure n) := inferInstance
  have hdir_meas : Measurable (finRealSphereRadialDirectionFrom (n := n) u) :=
    measurable_finRealSphereRadialDirectionFrom u
  have hball_lt_top :
      (finRealHaarMeasure n) (Metric.ball (0 : FinRealEuclideanSpace n) 1) < ∞ :=
    lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
      ((isCompact_closedBall (0 : FinRealEuclideanSpace n) 1).measure_lt_top)
  have hball_ne_top :
      (finRealHaarMeasure n) (Metric.ball (0 : FinRealEuclideanSpace n) 1) ≠ ∞ :=
    hball_lt_top.ne
  have hball_ne_zero :
      (finRealHaarMeasure n) (Metric.ball (0 : FinRealEuclideanSpace n) 1) ≠ 0 := by
    haveI : (finRealHaarMeasure n).IsOpenPosMeasure := by
      unfold finRealHaarMeasure; infer_instance
    exact (Metric.isOpen_ball).measure_ne_zero _ ⟨0, by simp⟩
  -- Universe surface measure.
  have huniv :
      (finRealSurfaceMeasure n) Set.univ =
        (Module.finrank ℝ (FinRealEuclideanSpace n) : ℝ≥0∞) *
          (finRealHaarMeasure n)
            (Metric.ball (0 : FinRealEuclideanSpace n) 1) := by
    show (finRealHaarMeasure n).toSphere Set.univ = _
    exact Measure.toSphere_apply_univ (finRealHaarMeasure n)
  -- Dimension positivity / finiteness.
  have hdim_pos : 0 < Module.finrank ℝ (FinRealEuclideanSpace n) := by
    rw [finRealSphere_moduleFinrank]
    exact Nat.pos_of_ne_zero (NeZero.ne n)
  have hdim_ne : (Module.finrank ℝ (FinRealEuclideanSpace n) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hdim_pos.ne'
  have hdim_top : (Module.finrank ℝ (FinRealEuclideanSpace n) : ℝ≥0∞) ≠ ∞ :=
    ENNReal.natCast_ne_top _
  have huniv_ne_top : (finRealSurfaceMeasure n) Set.univ ≠ ∞ := by
    rw [huniv]
    exact (ENNReal.mul_lt_top hdim_top.lt_top hball_lt_top).ne
  have huniv_ne_zero : (finRealSurfaceMeasure n) Set.univ ≠ 0 := by
    rw [huniv]
    exact mul_ne_zero hdim_ne hball_ne_zero
  haveI hfin : IsFiniteMeasure (finRealSurfaceMeasure n) := ⟨huniv_ne_top.lt_top⟩
  -- Unfold probability as scaled finRealSurfaceMeasure.
  have hprob_eq :
      finRealSurfaceProbabilityMeasure n =
        ((finRealSurfaceMeasure n) Set.univ)⁻¹ • finRealSurfaceMeasure n := by
    unfold finRealSurfaceProbabilityMeasure Measure.toFinite Measure.toFiniteAux
    rw [if_pos hfin]
    ext A hA
    rw [ProbabilityTheory.cond_apply MeasurableSet.univ, Set.univ_inter,
      Measure.smul_apply]
    rfl
  -- Helper for scalar extraction in restricted integrals.
  have hscalar_extract :
      ∀ (c : ℝ≥0∞) (ν : Measure (FinRealSphere n)) (T : Set (FinRealSphere n))
        (G : FinRealSphere n → ℝ≥0∞),
        (∫⁻ x in T, G x ∂(c • ν)) = c * ∫⁻ x in T, G x ∂ν := by
    intro c ν T G
    rw [Measure.restrict_smul, MeasureTheory.lintegral_smul_measure, smul_eq_mul]
  -- LHS = ((μ_S univ)⁻¹) * ∫_S F dμ_S.
  rw [hprob_eq, hscalar_extract]
  -- Now apply measure identity.
  rw [finRealSurfaceMeasure_eq_finrank_smul_map_radialDirection (n := n) u,
    hscalar_extract]
  -- ∫ F d(map dir _) = ∫ F ∘ dir d_
  rw [setLIntegral_map hS hF hdir_meas, Measure.restrict_restrict (hdir_meas hS)]
  -- Now: ((μ_S univ)⁻¹) * (n * ∫ in (dir⁻¹S) ∩ Ball, F(dir z) dHaar)
  -- We replace (dir⁻¹S) ∩ Ball by cone(S) modulo null at origin.
  have hcone_eq :
      finRealSphereRadialOpenCone n S =
        (Metric.ball (0 : FinRealEuclideanSpace n) 1 \ {0}) ∩
          (finRealSphereRadialDirectionFrom (n := n) u ⁻¹' S) :=
    finRealSphereRadialOpenCone_eq_ball_inter_direction_preimage_diff_zero
      (n := n) u S
  have hpre_meas : MeasurableSet
      (finRealSphereRadialDirectionFrom (n := n) u ⁻¹' S) :=
    hdir_meas hS
  have hcone_inter_meas :
      MeasurableSet (finRealSphereRadialOpenCone n S) := by
    rw [hcone_eq]
    exact (MeasurableSet.diff Metric.isOpen_ball.measurableSet
      (measurableSet_singleton _)).inter hpre_meas
  -- The set equality with the null intersection.
  have hset_eq :
      (finRealSphereRadialDirectionFrom (n := n) u ⁻¹' S) ∩
          (Metric.ball (0 : FinRealEuclideanSpace n) 1) =
        finRealSphereRadialOpenCone n S ∪
          ({(0 : FinRealEuclideanSpace n)} ∩
            (Metric.ball (0 : FinRealEuclideanSpace n) 1) ∩
            (finRealSphereRadialDirectionFrom (n := n) u ⁻¹' S)) := by
    rw [hcone_eq]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_singleton_iff,
      Set.mem_union, Set.mem_preimage]
    constructor
    · rintro ⟨hd, hb⟩
      by_cases hz : z = 0
      · right; exact ⟨⟨hz, hb⟩, hd⟩
      · left; exact ⟨⟨hb, hz⟩, hd⟩
    · rintro (⟨⟨hb, _⟩, hd⟩ | ⟨⟨h0, hb⟩, hd⟩)
      · exact ⟨hd, hb⟩
      · exact ⟨hd, hb⟩
  -- This union is disjoint (the cone excludes 0).
  have hdisj :
      Disjoint (finRealSphereRadialOpenCone n S)
        ({(0 : FinRealEuclideanSpace n)} ∩
          (Metric.ball (0 : FinRealEuclideanSpace n) 1) ∩
          (finRealSphereRadialDirectionFrom (n := n) u ⁻¹' S)) := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext z
    constructor
    · rintro ⟨hcone, ⟨⟨h0, _⟩, _⟩⟩
      rw [hcone_eq] at hcone
      exact hcone.1.2 h0
    · intro h
      exact absurd h (Set.notMem_empty z)
  -- The null intersection is haar-null.
  have hnull_inter :
      (finRealHaarMeasure n)
          ({(0 : FinRealEuclideanSpace n)} ∩
            (Metric.ball (0 : FinRealEuclideanSpace n) 1) ∩
            (finRealSphereRadialDirectionFrom (n := n) u ⁻¹' S)) = 0 := by
    apply measure_mono_null Set.inter_subset_left
    apply measure_mono_null Set.inter_subset_left
    exact measure_singleton _
  -- Split the integral.
  have hsing_meas : MeasurableSet
      ({(0 : FinRealEuclideanSpace n)} ∩
        (Metric.ball (0 : FinRealEuclideanSpace n) 1) ∩
        (finRealSphereRadialDirectionFrom (n := n) u ⁻¹' S)) := by
    exact ((measurableSet_singleton _).inter
      Metric.isOpen_ball.measurableSet).inter hpre_meas
  have hsplit :
      (∫⁻ z in (finRealSphereRadialDirectionFrom (n := n) u ⁻¹' S) ∩
            (Metric.ball (0 : FinRealEuclideanSpace n) 1),
          F (finRealSphereRadialDirectionFrom (n := n) u z)
          ∂(finRealHaarMeasure n))
        =
      ∫⁻ z in finRealSphereRadialOpenCone n S,
          F (finRealSphereRadialDirectionFrom (n := n) u z)
          ∂(finRealHaarMeasure n) := by
    rw [hset_eq, lintegral_union hsing_meas hdisj]
    have hzero :
        (∫⁻ z in {(0 : FinRealEuclideanSpace n)} ∩
            (Metric.ball (0 : FinRealEuclideanSpace n) 1) ∩
            (finRealSphereRadialDirectionFrom (n := n) u ⁻¹' S),
          F (finRealSphereRadialDirectionFrom (n := n) u z)
          ∂(finRealHaarMeasure n)) = 0 := by
      apply MeasureTheory.setLIntegral_measure_zero
      exact hnull_inter
    rw [hzero, add_zero]
  rw [hsplit]
  -- Compute the universe measure factor.
  have hmap_univ :
      ((Module.finrank ℝ (FinRealEuclideanSpace n) : ℝ≥0∞) •
            Measure.map (finRealSphereRadialDirectionFrom (n := n) u)
              ((finRealHaarMeasure n).restrict
                (Metric.ball (0 : FinRealEuclideanSpace n) 1))) Set.univ
        = (Module.finrank ℝ (FinRealEuclideanSpace n) : ℝ≥0∞) *
            (finRealHaarMeasure n) (Metric.ball (0 : FinRealEuclideanSpace n) 1) := by
    rw [Measure.smul_apply, Measure.map_apply hdir_meas MeasurableSet.univ,
      Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      smul_eq_mul]
  rw [hmap_univ]
  -- Algebra: ((n * b)⁻¹) * (n * I) = b⁻¹ * I when n, b finite & nonzero.
  rw [ENNReal.mul_inv (Or.inl hdim_ne) (Or.inl hdim_top)]
  rw [show ∀ a b c d : ℝ≥0∞, (a * b) * (c * d) = (a * c) * (b * d) from
        fun _ _ _ _ => by ring,
    ENNReal.inv_mul_cancel hdim_ne hdim_top, one_mul]

/-- The function-level cone bridge packaged as the named leaf-3 prerequisite. -/
theorem finRealSurfaceProbabilityMeasure_lintegralConeBridge
    {n : ℕ} [NeZero n] :
    FinRealSurfaceProbabilityMeasureLIntegralConeBridge n :=
  fun u _S hS F hF =>
    lintegral_finRealSurfaceProbabilityMeasure_eq_cone (u := u) hS F hF

/-!
### Leaf 3 infrastructure — homogeneous ambient extension

The homogeneous map `Ψ(z) = ‖z‖ • (↑(φ (dir z)))` linearly extends the sphere
parametrization to the open radial cone.  Leaf 3 compares cone integrals on the
source/target hemispheres through this map and the ambient Haar change-of-variables
formula.
-/

/-- Homogeneous extension of a sphere map `φ` to the ambient open cone. -/
noncomputable def finRealSphereReflectionHomogeneousMap
    (n : ℕ) (_y : FinRealSphere n)
    (φ : FinRealSphere n → FinRealSphere n)
    (u : FinRealSphere n) (z : FinRealEuclideanSpace n) :
    FinRealEuclideanSpace n :=
  ‖z‖ • ((φ (finRealSphereRadialDirectionFrom (n := n) u z)) :
      FinRealEuclideanSpace n)

@[simp]
theorem finRealSphereReflectionHomogeneousMap_smul
    {n : ℕ} (y : FinRealSphere n)
    (φ : FinRealSphere n → FinRealSphere n) (u x : FinRealSphere n) {r : ℝ}
    (hr : 0 < r) :
    finRealSphereReflectionHomogeneousMap n y φ u
        (r • (x : FinRealEuclideanSpace n)) =
      r • ((φ x : FinRealEuclideanSpace n)) := by
  simp [finRealSphereReflectionHomogeneousMap,
    finRealSphereRadialDirectionFrom_smul u x hr, norm_smul,
    finRealSphere_norm_coe n x, Real.norm_eq_abs, abs_of_pos hr]

theorem finRealSphereReflectionHomogeneousMap_mapsTo_openCone
    {n : ℕ} (y : FinRealSphere n)
    (φ : FinRealSphere n → FinRealSphere n) (u : FinRealSphere n)
    {S T : Set (FinRealSphere n)}
    (hmaps : Set.MapsTo φ S T) :
    Set.MapsTo (finRealSphereReflectionHomogeneousMap n y φ u)
      (finRealSphereRadialOpenCone n S)
      (finRealSphereRadialOpenCone n T) := by
  rintro z ⟨r, hr, w, ⟨x, hx, rfl⟩, rfl⟩
  refine ⟨r, hr, _, ⟨φ x, hmaps hx, rfl⟩, ?_⟩
  simp [finRealSphereReflectionHomogeneousMap,
    finRealSphereRadialDirectionFrom_smul u x hr.1, norm_smul,
    finRealSphere_norm_coe n x, Real.norm_eq_abs, abs_of_pos hr.1]

theorem finRealSphereReflectionHomogeneousMap_injOn_openCone
    {n : ℕ} (y : FinRealSphere n)
    (φ : FinRealSphere n → FinRealSphere n) (u : FinRealSphere n)
    {S : Set (FinRealSphere n)} (hinj : Set.InjOn φ S) :
    Set.InjOn (finRealSphereReflectionHomogeneousMap n y φ u)
      (finRealSphereRadialOpenCone n S) := by
  intro z₁ hz₁ z₂ hz₂ hEq
  rcases hz₁ with ⟨r₁, hr₁, w₁, ⟨x₁, hx₁, rfl⟩, rfl⟩
  rcases hz₂ with ⟨r₂, hr₂, w₂, ⟨x₂, hx₂, rfl⟩, rfl⟩
  have hEq' :
      r₁ • ((φ x₁ : FinRealEuclideanSpace n)) =
        r₂ • ((φ x₂ : FinRealEuclideanSpace n)) := by
    have hEq'' :
        finRealSphereReflectionHomogeneousMap n y φ u (r₁ • (x₁ : FinRealEuclideanSpace n)) =
          finRealSphereReflectionHomogeneousMap n y φ u (r₂ • (x₂ : FinRealEuclideanSpace n)) :=
      hEq
    simpa [finRealSphereReflectionHomogeneousMap_smul y φ u x₁ hr₁.1,
      finRealSphereReflectionHomogeneousMap_smul y φ u x₂ hr₂.1] using hEq''
  have hrEq : r₁ = r₂ := by
    have hnorm :
        ‖r₁ • ((φ x₁ : FinRealEuclideanSpace n))‖ =
          ‖r₂ • ((φ x₂ : FinRealEuclideanSpace n))‖ := by
      rw [hEq']
    rw [norm_smul, norm_smul, finRealSphere_norm_coe n (φ x₁),
      finRealSphere_norm_coe n (φ x₂)] at hnorm
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hr₁.1, abs_of_pos hr₂.1] at hnorm
    linarith
  have hφAmbient :
      (φ x₁ : FinRealEuclideanSpace n) = (φ x₂ : FinRealEuclideanSpace n) := by
    rw [hrEq] at hEq'
    exact (smul_right_inj hr₂.1.ne').mp hEq'
  have hφEq : φ x₁ = φ x₂ := Subtype.ext hφAmbient
  have hxEq : x₁ = x₂ := hinj hx₁ hx₂ hφEq
  simp [hrEq, hxEq]

theorem measurable_finRealSphereReflectionHomogeneousMap
    {n : ℕ} (y : FinRealSphere n)
    (φ : FinRealSphere n → FinRealSphere n) (u : FinRealSphere n)
    (hφ : Measurable φ) :
    Measurable (finRealSphereReflectionHomogeneousMap n y φ u) := by
  classical
  let dir := finRealSphereRadialDirectionFrom (n := n) u
  have hdir : Measurable dir := measurable_finRealSphereRadialDirectionFrom u
  have hval : Measurable (Subtype.val ∘ φ ∘ dir) :=
    measurable_subtype_coe.comp (hφ.comp hdir)
  have hnorm : Measurable (fun z : FinRealEuclideanSpace n => ‖z‖) := by fun_prop
  simpa [finRealSphereReflectionHomogeneousMap] using hnorm.smul hval

/-- Source/target packaging for one fibre. -/
def fibreConeData (n : ℕ) (p y : FinRealSphere n) :
    Set (FinRealSphere n) × Set (FinRealSphere n) × (FinRealSphere n → FinRealSphere n) :=
  (finRealSphereAdmissibleHemisphere n p ∩ finRealSphereDirectionHemisphere n y,
    {x : FinRealSphere n |
      finRealSphereHeight n p x ≤ finRealSphereHeight n p y} \ {y},
    finRealSpherePolarizationParam (finRealSphereReflectionMap n) y)

theorem fibreConeData_domain_meas (n : ℕ) (p y : FinRealSphere n) :
    MeasurableSet (fibreConeData n p y).1 :=
  measurableSet_finRealSphereAdmissibleDirectionDomain n p y

theorem fibreConeData_target_meas (n : ℕ) (p y : FinRealSphere n) :
    MeasurableSet (fibreConeData n p y).2.1 :=
  measurableSet_finRealSphereHeightSublevel_diff_singleton n p y

theorem fibreConeData_φ_meas (n : ℕ) (p y : FinRealSphere n) :
    Measurable (fibreConeData n p y).2.2 :=
  finRealSphereReflectionMap_param_measurable n y

theorem fibreConeData_bij (n : ℕ) (p y : FinRealSphere n) :
    BijOn (fibreConeData n p y).2.2 (fibreConeData n p y).1 (fibreConeData n p y).2.1 :=
  finRealSpherePolarizationParam_bijOn_admissible_direction_heightSublevel_diff_singleton
    n p y

theorem finRealSphereRadialOpenCone_measurableSet
    {n : ℕ} (u : FinRealSphere n) {S : Set (FinRealSphere n)} (hS : MeasurableSet S) :
    MeasurableSet (finRealSphereRadialOpenCone n S) := by
  rw [finRealSphereRadialOpenCone_eq_ball_inter_direction_preimage_diff_zero u S]
  have hpre :
      MeasurableSet (finRealSphereRadialDirectionFrom (n := n) u ⁻¹' S) :=
    (measurable_finRealSphereRadialDirectionFrom u) hS
  exact (Metric.isOpen_ball.measurableSet.diff
    (measurableSet_singleton (0 : FinRealEuclideanSpace n))).inter hpre

theorem homogeneousMap_image_sourceCone
    (n : ℕ) (p y u : FinRealSphere n) :
    finRealSphereReflectionHomogeneousMap n y (fibreConeData n p y).2.2 u ''
      (finRealSphereRadialOpenCone n (fibreConeData n p y).1) =
      finRealSphereRadialOpenCone n (fibreConeData n p y).2.1 := by
  let d := fibreConeData n p y
  let φ := d.2.2
  let hbij := fibreConeData_bij n p y
  ext z
  constructor
  · rintro ⟨z, ⟨r, hr, w, ⟨v, hv, rfl⟩, rfl⟩, rfl⟩
    refine ⟨r, hr, _, ⟨φ v, hbij.mapsTo hv, rfl⟩, ?_⟩
    simp [d, finRealSphereReflectionHomogeneousMap,
      finRealSphereRadialDirectionFrom_smul u v hr.1, norm_smul,
      finRealSphere_norm_coe n v, Real.norm_eq_abs, abs_of_pos hr.1, φ]
  · intro hz
    rcases hz with ⟨r, hr, w, ⟨x, hx, rfl⟩, rfl⟩
    obtain ⟨v, hv, hφv⟩ := hbij.surjOn hx
    refine ⟨r • (v : FinRealEuclideanSpace n), ⟨r, hr, _, ⟨v, hv, rfl⟩, rfl⟩, ?_⟩
    rw [finRealSphereReflectionHomogeneousMap_smul y φ u v hr.1]
    exact congrArg (fun t : FinRealEuclideanSpace n => r • t)
      (congrArg Subtype.val hφv)

theorem homogeneousMap_injOn_sourceCone
    (n : ℕ) (p y u : FinRealSphere n) :
    Set.InjOn
      (finRealSphereReflectionHomogeneousMap n y (fibreConeData n p y).2.2 u)
      (finRealSphereRadialOpenCone n (fibreConeData n p y).1) := by
  exact
    finRealSphereReflectionHomogeneousMap_injOn_openCone (y := y)
      (φ := (fibreConeData n p y).2.2) (u := u)
      (hinj := (fibreConeData_bij n p y).injOn)

/-- The punctured target fibre is the height sublevel with the diagonal removed. -/
theorem fibreConeData_target_eq_heightSublevel_diff_singleton
    (n : ℕ) (p y : FinRealSphere n) :
    (fibreConeData n p y).2.1 =
      {x : FinRealSphere n |
        finRealSphereHeight n p x ≤ finRealSphereHeight n p y} \ {y} := by
  rfl

/-- The source fibre domain packaged by `fibreConeData`. -/
theorem fibreConeData_domain_eq
    (n : ℕ) (p y : FinRealSphere n) :
    (fibreConeData n p y).1 =
      finRealSphereAdmissibleHemisphere n p ∩
        finRealSphereDirectionHemisphere n y := by
  rfl

/-- `NeZero n` from real dimension at least two. -/
theorem neZero_of_two_le {n : ℕ} (hn2 : 2 ≤ n) : NeZero n :=
  ⟨by omega⟩

/-- Rewrite the full-sphere kernel integrand as an integral over the height
sublevel set. -/
theorem lintegral_kernel_heightSublevel_eq_indicator
    {n : ℕ} (p y : FinRealSphere n)
    (F : FinRealSphere n → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ x : FinRealSphere n,
        F x *
          (if finRealSphereHeight n p x ≤ finRealSphereHeight n p y then
            finRealSpherePolarizationKernel n x y
          else
            0)
        ∂(finRealSurfaceProbabilityMeasure n))
      =
    (∫⁻ x in {x : FinRealSphere n |
          finRealSphereHeight n p x ≤ finRealSphereHeight n p y},
        F x * finRealSpherePolarizationKernel n x y
      ∂(finRealSurfaceProbabilityMeasure n)) := by
  let S : Set (FinRealSphere n) :=
    {x : FinRealSphere n | finRealSphereHeight n p x ≤ finRealSphereHeight n p y}
  have hS : MeasurableSet S := measurableSet_finRealSphereHeightSublevel n p y
  have hheight :
      Measurable (fun x : FinRealSphere n => finRealSphereHeight n p x) := by
    unfold finRealSphereHeight
    fun_prop
  have hkernel :
      Measurable (fun x : FinRealSphere n =>
        finRealSpherePolarizationKernel n x y) :=
    measurable_finRealSpherePolarizationKernel_right n y
  have hintegrand :
      Measurable (fun x : FinRealSphere n =>
        F x *
          (if finRealSphereHeight n p x ≤ finRealSphereHeight n p y then
            finRealSpherePolarizationKernel n x y
          else
            0)) := by
    have hmeas :
        Measurable (fun x : FinRealSphere n =>
          if finRealSphereHeight n p x ≤ finRealSphereHeight n p y then
            F x * finRealSpherePolarizationKernel n x y
          else 0) := by
      refine Measurable.ite ?_ (hF.mul hkernel) measurable_const
      exact measurableSet_le hheight measurable_const
    convert hmeas using 1
    ext x
    by_cases h : finRealSphereHeight n p x ≤ finRealSphereHeight n p y <;> simp [h]
  have hintegrand' :
      Measurable (fun x : FinRealSphere n =>
        S.indicator (fun x => F x * finRealSpherePolarizationKernel n x y) x) := by
    exact (hF.mul hkernel).indicator hS
  rw [← lintegral_indicator hS]
  apply lintegral_congr_ae
  filter_upwards with x
  by_cases hx : finRealSphereHeight n p x ≤ finRealSphereHeight n p y <;>
    simp [S, Set.indicator, hx]

/-- The height sublevel integral equals the punctured target integral, because
the diagonal point `{y}` has zero surface probability in dimension at least
two. -/
theorem lintegral_finRealSurfaceProbabilityMeasure_heightSublevel_eq_punctured
    {n : ℕ} (hn2 : 2 ≤ n) (p y : FinRealSphere n)
    (F : FinRealSphere n → ℝ≥0∞) (_hF : Measurable F) :
    (∫⁻ x in {x : FinRealSphere n |
          finRealSphereHeight n p x ≤ finRealSphereHeight n p y},
        F x ∂(finRealSurfaceProbabilityMeasure n))
      =
    (∫⁻ x in (fibreConeData n p y).2.1,
        F x ∂(finRealSurfaceProbabilityMeasure n)) := by
  have htarget :
      {x : FinRealSphere n |
          finRealSphereHeight n p x ≤ finRealSphereHeight n p y} =
        (fibreConeData n p y).2.1 ∪ {y} := by
    rw [fibreConeData_target_eq_heightSublevel_diff_singleton n p y]
    ext x
    simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · intro hle
      by_cases hxy : x = y
      · exact Or.inr hxy
      · exact Or.inl ⟨hle, hxy⟩
    · intro hx
      rcases hx with (⟨hle, _⟩ | rfl)
      · exact hle
      · exact le_rfl
  have hS : MeasurableSet
      {x : FinRealSphere n |
        finRealSphereHeight n p x ≤ finRealSphereHeight n p y} :=
    measurableSet_finRealSphereHeightSublevel n p y
  have hT : MeasurableSet (fibreConeData n p y).2.1 :=
    fibreConeData_target_meas n p y
  have hsing : MeasurableSet ({y} : Set (FinRealSphere n)) :=
    measurableSet_singleton y
  have hdisj :
      Disjoint (fibreConeData n p y).2.1 ({y} : Set (FinRealSphere n)) := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
      iff_false]
    intro ⟨hx, hmem⟩
    exact hx.2 hmem
  have hsing_null :
      (finRealSurfaceProbabilityMeasure n) {y} = 0 :=
    finRealSurfaceProbabilityMeasure_singleton n hn2 y
  have hzero :
      (∫⁻ x in {y}, F x ∂(finRealSurfaceProbabilityMeasure n)) = 0 := by
    apply MeasureTheory.setLIntegral_measure_zero
    exact hsing_null
  calc
    (∫⁻ x in {x : FinRealSphere n |
          finRealSphereHeight n p x ≤ finRealSphereHeight n p y},
        F x ∂(finRealSurfaceProbabilityMeasure n))
        =
      (∫⁻ x in (fibreConeData n p y).2.1 ∪ {y},
          F x ∂(finRealSurfaceProbabilityMeasure n)) := by
        rw [htarget]
    _ =
      (∫⁻ x in (fibreConeData n p y).2.1,
          F x ∂(finRealSurfaceProbabilityMeasure n)) +
        (∫⁻ x in {y}, F x ∂(finRealSurfaceProbabilityMeasure n)) := by
          exact lintegral_union hsing hdisj
    _ =
      (∫⁻ x in (fibreConeData n p y).2.1,
          F x ∂(finRealSurfaceProbabilityMeasure n)) := by
        rw [hzero, add_zero]

/-- Same splitting for a kernel-weighted height-sublevel integrand. -/
theorem lintegral_kernel_heightSublevel_eq_punctured
    {n : ℕ} (hn2 : 2 ≤ n) (p y : FinRealSphere n)
    (F : FinRealSphere n → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x in {x : FinRealSphere n |
          finRealSphereHeight n p x ≤ finRealSphereHeight n p y},
        F x * finRealSpherePolarizationKernel n x y
      ∂(finRealSurfaceProbabilityMeasure n))
      =
    (∫⁻ x in (fibreConeData n p y).2.1,
        F x * finRealSpherePolarizationKernel n x y
      ∂(finRealSurfaceProbabilityMeasure n)) := by
  have hkernel :
      Measurable (fun x : FinRealSphere n =>
        finRealSpherePolarizationKernel n x y) :=
    measurable_finRealSpherePolarizationKernel_right n y
  exact
    lintegral_finRealSurfaceProbabilityMeasure_heightSublevel_eq_punctured
      hn2 p y (fun x => F x * finRealSpherePolarizationKernel n x y)
      (hF.mul hkernel)

/-- The open radial cone over a measurable sphere set is a measurable subset of
ambient space. -/
theorem measurableSet_finRealSphereRadialOpenCone
    {n : ℕ} (u : FinRealSphere n) {S : Set (FinRealSphere n)} (hS : MeasurableSet S) :
    MeasurableSet (finRealSphereRadialOpenCone n S) :=
  finRealSphereRadialOpenCone_measurableSet u hS

/-- Jacobian-image reduction for the cap-flattening map.  If the concrete
cap-flattening map has a derivative on the cap cone whose absolute determinant
is pointwise at least `cos(r)^(1-n)` (written as the product inequality below),
then the cap-cone volume satisfies the desired `cos(r)^(n-1)` bound.

This is the exact mathlib change-of-variables step; the remaining
theorem-strength work is the derivative and determinant estimate for
`finRealSphereCapConeFlatteningMap`. -/
theorem finRealSphereRadialOpenCone_closedHalfspace_measure_le_of_capConeFlatteningMap_jacobianLowerBound
    {n : ℕ} [NeZero n] (e : FinRealEuclideanSpace n)
    {r : ℝ} (he : ‖e‖ = 1) (hrpos : 0 < r) (hrlt : r < Real.pi / 2)
    (f' : FinRealEuclideanSpace n → FinRealEuclideanSpace n →L[ℝ] FinRealEuclideanSpace n)
    (hfderiv :
      ∀ z ∈ finRealSphereRadialOpenCone n
          (finRealSphereClosedHalfspace n e (Real.sin r)),
        HasFDerivWithinAt (finRealSphereCapConeFlatteningMap e r)
          (f' z)
          (finRealSphereRadialOpenCone n
            (finRealSphereClosedHalfspace n e (Real.sin r))) z)
    (hdet :
      ∀ z ∈ finRealSphereRadialOpenCone n
          (finRealSphereClosedHalfspace n e (Real.sin r)),
        (1 : ℝ≥0∞) ≤
          ENNReal.ofReal (Real.cos r ^ (n - 1)) *
            ENNReal.ofReal |(f' z).det|) :
    (finRealHaarMeasure n)
        (finRealSphereRadialOpenCone n
          (finRealSphereClosedHalfspace n e (Real.sin r))) ≤
      ENNReal.ofReal (Real.cos r ^ (n - 1)) *
        (finRealHaarMeasure n) (Metric.ball (0 : FinRealEuclideanSpace n) 1) := by
  let source : Set (FinRealEuclideanSpace n) :=
    finRealSphereRadialOpenCone n
      (finRealSphereClosedHalfspace n e (Real.sin r))
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.cos r ^ (n - 1))
  haveI : (finRealHaarMeasure n).IsAddHaarMeasure := by
    unfold finRealHaarMeasure
    infer_instance
  have hsource_meas : MeasurableSet source := by
    dsimp [source]
    exact measurableSet_finRealSphereRadialOpenCone (finRealSphereNorthPole n)
      (measurableSet_finRealSphereClosedHalfspace n e (Real.sin r))
  have hinj : Set.InjOn (finRealSphereCapConeFlatteningMap e r) source := by
    dsimp [source]
    exact finRealSphereCapConeFlatteningMap_injOn_closedHalfspaceCone e he hrpos hrlt
  have hmaps : Set.MapsTo (finRealSphereCapConeFlatteningMap e r) source
      (Metric.ball (0 : FinRealEuclideanSpace n) 1) := by
    dsimp [source]
    exact finRealSphereCapConeFlatteningMap_mapsTo_closedHalfspaceCone_ball e he hrpos hrlt
  have himage_le :
      (finRealHaarMeasure n) ((finRealSphereCapConeFlatteningMap e r) '' source) ≤
        (finRealHaarMeasure n) (Metric.ball (0 : FinRealEuclideanSpace n) 1) := by
    exact measure_mono (Set.image_subset_iff.mpr hmaps)
  have hchange :
      ∫⁻ z in source, ENNReal.ofReal |(f' z).det| ∂(finRealHaarMeasure n) =
        (finRealHaarMeasure n) ((finRealSphereCapConeFlatteningMap e r) '' source) := by
    simpa using
      (SphericalPolarization.GeometricKernel.mathlib_lintegral_abs_det_fderiv_eq_addHaar_image
        (E := FinRealEuclideanSpace n)
        (s := source)
        (f := finRealSphereCapConeFlatteningMap e r)
        (f' := f')
        (μ := finRealHaarMeasure n)
        hsource_meas hfderiv hinj)
  have hconst_le :
      (finRealHaarMeasure n) source ≤
        ∫⁻ z in source, c * ENNReal.ofReal |(f' z).det| ∂(finRealHaarMeasure n) := by
    rw [← setLIntegral_one]
    exact setLIntegral_mono' hsource_meas (fun z hz => by
      simpa [c, source] using hdet z hz)
  have hpull :
      ∫⁻ z in source, c * ENNReal.ofReal |(f' z).det| ∂(finRealHaarMeasure n) =
        c * ∫⁻ z in source, ENNReal.ofReal |(f' z).det| ∂(finRealHaarMeasure n) := by
    rw [lintegral_const_mul' c
      (fun z : FinRealEuclideanSpace n => ENNReal.ofReal |(f' z).det|)
      (by simp [c])]
  calc
    (finRealHaarMeasure n) source
        ≤ ∫⁻ z in source, c * ENNReal.ofReal |(f' z).det| ∂(finRealHaarMeasure n) :=
          hconst_le
    _ = c * ∫⁻ z in source, ENNReal.ofReal |(f' z).det| ∂(finRealHaarMeasure n) :=
          hpull
    _ = c * (finRealHaarMeasure n) ((finRealSphereCapConeFlatteningMap e r) '' source) := by
          rw [hchange]
    _ ≤ c * (finRealHaarMeasure n) (Metric.ball (0 : FinRealEuclideanSpace n) 1) := by
          simpa [mul_comm] using mul_le_mul_left himage_le c

/-- Jacobian-image reduction on the differentiability locus of the
cap-flattening map.  The only points omitted here are the radicand-zero
boundary points of the closed cap cone; proving that boundary null is the
separate measure-theoretic leaf needed to upgrade this to the full closed-cone
bound. -/
theorem finRealSphereRadialOpenCone_closedHalfspace_nonzeroRadicand_measure_le_of_capConeFlatteningMap_detLowerBound
    {n : ℕ} [NeZero n] (e : FinRealEuclideanSpace n)
    {r : ℝ} (he : ‖e‖ = 1) (hrpos : 0 < r) (hrlt : r < Real.pi / 2)
    (hdet :
      ∀ z ∈
          finRealSphereRadialOpenCone n
            (finRealSphereClosedHalfspace n e (Real.sin r)) ∩
            {z | finRealSphereCapConeRadicand e r z ≠ 0},
        (1 : ℝ≥0∞) ≤
          ENNReal.ofReal (Real.cos r ^ (n - 1)) *
            ENNReal.ofReal |(finRealSphereCapConeFlatteningMapFDeriv e r z).det|) :
    (finRealHaarMeasure n)
        (finRealSphereRadialOpenCone n
          (finRealSphereClosedHalfspace n e (Real.sin r)) ∩
          {z | finRealSphereCapConeRadicand e r z ≠ 0}) ≤
      ENNReal.ofReal (Real.cos r ^ (n - 1)) *
        (finRealHaarMeasure n) (Metric.ball (0 : FinRealEuclideanSpace n) 1) := by
  let fullSource : Set (FinRealEuclideanSpace n) :=
    finRealSphereRadialOpenCone n
      (finRealSphereClosedHalfspace n e (Real.sin r))
  let source : Set (FinRealEuclideanSpace n) :=
    fullSource ∩ {z | finRealSphereCapConeRadicand e r z ≠ 0}
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.cos r ^ (n - 1))
  haveI : (finRealHaarMeasure n).IsAddHaarMeasure := by
    unfold finRealHaarMeasure
    infer_instance
  have hfull_meas : MeasurableSet fullSource := by
    dsimp [fullSource]
    exact measurableSet_finRealSphereRadialOpenCone (finRealSphereNorthPole n)
      (measurableSet_finRealSphereClosedHalfspace n e (Real.sin r))
  have hrad_meas :
      MeasurableSet {z : FinRealEuclideanSpace n |
        finRealSphereCapConeRadicand e r z ≠ 0} := by
    simpa [Set.preimage] using
      (continuous_finRealSphereCapConeRadicand e r).measurable
        ((measurableSet_singleton (0 : ℝ)).compl)
  have hsource_meas : MeasurableSet source := hfull_meas.inter hrad_meas
  have hinj_full :
      Set.InjOn (finRealSphereCapConeFlatteningMap e r) fullSource := by
    dsimp [fullSource]
    exact finRealSphereCapConeFlatteningMap_injOn_closedHalfspaceCone e he hrpos hrlt
  have hinj : Set.InjOn (finRealSphereCapConeFlatteningMap e r) source := by
    intro x hx y hy hxy
    exact hinj_full hx.1 hy.1 hxy
  have hmaps_full : Set.MapsTo (finRealSphereCapConeFlatteningMap e r) fullSource
      (Metric.ball (0 : FinRealEuclideanSpace n) 1) := by
    dsimp [fullSource]
    exact finRealSphereCapConeFlatteningMap_mapsTo_closedHalfspaceCone_ball e he hrpos hrlt
  have hmaps : Set.MapsTo (finRealSphereCapConeFlatteningMap e r) source
      (Metric.ball (0 : FinRealEuclideanSpace n) 1) := by
    intro z hz
    exact hmaps_full hz.1
  have hfderiv :
      ∀ z ∈ source,
        HasFDerivWithinAt (finRealSphereCapConeFlatteningMap e r)
          (finRealSphereCapConeFlatteningMapFDeriv e r z) source z := by
    intro z hz
    exact
      (hasFDerivAt_finRealSphereCapConeFlatteningMap_of_radicand_ne_zero
        e r hz.2).hasFDerivWithinAt
  have himage_le :
      (finRealHaarMeasure n) ((finRealSphereCapConeFlatteningMap e r) '' source) ≤
        (finRealHaarMeasure n) (Metric.ball (0 : FinRealEuclideanSpace n) 1) := by
    exact measure_mono (Set.image_subset_iff.mpr hmaps)
  have hchange :
      ∫⁻ z in source,
          ENNReal.ofReal |(finRealSphereCapConeFlatteningMapFDeriv e r z).det|
            ∂(finRealHaarMeasure n) =
        (finRealHaarMeasure n) ((finRealSphereCapConeFlatteningMap e r) '' source) := by
    simpa using
      (SphericalPolarization.GeometricKernel.mathlib_lintegral_abs_det_fderiv_eq_addHaar_image
        (E := FinRealEuclideanSpace n)
        (s := source)
        (f := finRealSphereCapConeFlatteningMap e r)
        (f' := finRealSphereCapConeFlatteningMapFDeriv e r)
        (μ := finRealHaarMeasure n)
        hsource_meas hfderiv hinj)
  have hconst_le :
      (finRealHaarMeasure n) source ≤
        ∫⁻ z in source,
          c * ENNReal.ofReal |(finRealSphereCapConeFlatteningMapFDeriv e r z).det|
            ∂(finRealHaarMeasure n) := by
    rw [← setLIntegral_one]
    exact setLIntegral_mono' hsource_meas (fun z hz => by
      simpa [c, source, fullSource] using hdet z hz)
  have hpull :
      ∫⁻ z in source,
          c * ENNReal.ofReal |(finRealSphereCapConeFlatteningMapFDeriv e r z).det|
            ∂(finRealHaarMeasure n) =
        c * ∫⁻ z in source,
          ENNReal.ofReal |(finRealSphereCapConeFlatteningMapFDeriv e r z).det|
            ∂(finRealHaarMeasure n) := by
    rw [lintegral_const_mul' c
      (fun z : FinRealEuclideanSpace n =>
        ENNReal.ofReal |(finRealSphereCapConeFlatteningMapFDeriv e r z).det|)
      (by simp [c])]
  calc
    (finRealHaarMeasure n) source
        ≤ ∫⁻ z in source,
            c * ENNReal.ofReal |(finRealSphereCapConeFlatteningMapFDeriv e r z).det|
              ∂(finRealHaarMeasure n) :=
          hconst_le
    _ = c * ∫⁻ z in source,
          ENNReal.ofReal |(finRealSphereCapConeFlatteningMapFDeriv e r z).det|
            ∂(finRealHaarMeasure n) :=
          hpull
    _ = c * (finRealHaarMeasure n) ((finRealSphereCapConeFlatteningMap e r) '' source) := by
          rw [hchange]
    _ ≤ c * (finRealHaarMeasure n) (Metric.ball (0 : FinRealEuclideanSpace n) 1) := by
          simpa [mul_comm] using mul_le_mul_left himage_le c

/-- Full closed-cone Jacobian reduction from the determinant lower bound on
the nonzero-radicand locus.  The radicand-zero part is the null frontier
boundary proved above, so the change-of-variables argument only needs the
explicit determinant estimate where the cap-flattening map is differentiable. -/
theorem finRealSphereRadialOpenCone_closedHalfspace_measure_le_of_capConeFlatteningMap_detLowerBound
    {n : ℕ} [NeZero n] (e : FinRealEuclideanSpace n)
    {r : ℝ} (he : ‖e‖ = 1) (hrpos : 0 < r) (hrlt : r < Real.pi / 2)
    (hdet :
      ∀ z ∈
          finRealSphereRadialOpenCone n
            (finRealSphereClosedHalfspace n e (Real.sin r)) ∩
            {z | finRealSphereCapConeRadicand e r z ≠ 0},
        (1 : ℝ≥0∞) ≤
          ENNReal.ofReal (Real.cos r ^ (n - 1)) *
            ENNReal.ofReal |(finRealSphereCapConeFlatteningMapFDeriv e r z).det|) :
    (finRealHaarMeasure n)
        (finRealSphereRadialOpenCone n
          (finRealSphereClosedHalfspace n e (Real.sin r))) ≤
      ENNReal.ofReal (Real.cos r ^ (n - 1)) *
        (finRealHaarMeasure n) (Metric.ball (0 : FinRealEuclideanSpace n) 1) := by
  let fullSource : Set (FinRealEuclideanSpace n) :=
    finRealSphereRadialOpenCone n
      (finRealSphereClosedHalfspace n e (Real.sin r))
  let nonzeroSource : Set (FinRealEuclideanSpace n) :=
    fullSource ∩ {z | finRealSphereCapConeRadicand e r z ≠ 0}
  let zeroSource : Set (FinRealEuclideanSpace n) :=
    fullSource ∩ {z | finRealSphereCapConeRadicand e r z = 0}
  let bound : ℝ≥0∞ :=
    ENNReal.ofReal (Real.cos r ^ (n - 1)) *
      (finRealHaarMeasure n) (Metric.ball (0 : FinRealEuclideanSpace n) 1)
  have hnonzero : (finRealHaarMeasure n) nonzeroSource ≤ bound := by
    dsimp [nonzeroSource, fullSource, bound]
    exact
      finRealSphereRadialOpenCone_closedHalfspace_nonzeroRadicand_measure_le_of_capConeFlatteningMap_detLowerBound
        e he hrpos hrlt hdet
  have hzero : (finRealHaarMeasure n) zeroSource = 0 := by
    dsimp [zeroSource, fullSource]
    simpa [Set.inter_def] using
      finRealSphereRadialOpenCone_closedHalfspace_radicand_zero_measure_zero
        e he hrpos hrlt
  have hcover : fullSource ⊆ nonzeroSource ∪ zeroSource := by
    intro z hz
    by_cases hq : finRealSphereCapConeRadicand e r z = 0
    · exact Or.inr ⟨hz, hq⟩
    · exact Or.inl ⟨hz, hq⟩
  have hsplit : (finRealHaarMeasure n) fullSource ≤
      (finRealHaarMeasure n) nonzeroSource + (finRealHaarMeasure n) zeroSource := by
    calc
      (finRealHaarMeasure n) fullSource ≤
          (finRealHaarMeasure n) (nonzeroSource ∪ zeroSource) :=
        measure_mono hcover
      _ ≤ (finRealHaarMeasure n) nonzeroSource +
            (finRealHaarMeasure n) zeroSource :=
        MeasureTheory.measure_union_le nonzeroSource zeroSource
  calc
    (finRealHaarMeasure n) fullSource ≤
        (finRealHaarMeasure n) nonzeroSource + (finRealHaarMeasure n) zeroSource := hsplit
    _ = (finRealHaarMeasure n) nonzeroSource := by rw [hzero, add_zero]
    _ ≤ bound := hnonzero

/-- Full cap-cone volume bound from the explicit cap-flattening map.  This
combines the null radicand boundary, the Jacobian-image reducer, and the
determinant lower bound proved from the exact block-triangular determinant. -/
theorem finRealSphereRadialOpenCone_closedHalfspace_measure_le_from_capConeFlatteningMap
    {n : ℕ} [NeZero n] (e : FinRealEuclideanSpace n)
    {r : ℝ} (hn2 : 2 ≤ n) (he : ‖e‖ = 1)
    (hrpos : 0 < r) (hrlt : r < Real.pi / 2) :
    (finRealHaarMeasure n)
        (finRealSphereRadialOpenCone n
          (finRealSphereClosedHalfspace n e (Real.sin r))) ≤
      ENNReal.ofReal (Real.cos r ^ (n - 1)) *
        (finRealHaarMeasure n) (Metric.ball (0 : FinRealEuclideanSpace n) 1) := by
  exact
    finRealSphereRadialOpenCone_closedHalfspace_measure_le_of_capConeFlatteningMap_detLowerBound
      e he hrpos hrlt
      (fun z hz =>
        finRealSphereCapConeFlatteningMapFDeriv_detLowerBound
          hn2 e he hrpos hrlt hz.1 hz.2)

/-- North-pole cap-cone power tail supplied by the explicit cap-flattening map. -/
theorem finRealSphereNorthPoleCapConeCosinePowerTail_from_capConeFlatteningMap
    (n : ℕ) [NeZero n] :
    FinRealSphereNorthPoleCapConeCosinePowerTail n := by
  intro r hn2 hrpos hrlt
  let e : FinRealEuclideanSpace n :=
    -(finRealSphereNorthPole n : FinRealEuclideanSpace n)
  have he : ‖e‖ = 1 := by
    rw [norm_neg]
    have h := (finRealSphereNorthPole n).2
    simp [FinRealSphere] at h ⊢
  simpa [e] using
    finRealSphereRadialOpenCone_closedHalfspace_measure_le_from_capConeFlatteningMap
      (n := n) e hn2 he hrpos hrlt

/-- No-input north-pole cap-cone power tail supplied by the explicit
cap-flattening map. -/
theorem sphere_northPoleCapConeCosinePowerTail_from_capConeFlatteningMap :
    sphere_northPoleCapConeCosinePowerTail := by
  intro n hn
  exact finRealSphereNorthPoleCapConeCosinePowerTail_from_capConeFlatteningMap n

/-- No-input below-half cap-cone power tail supplied by the explicit
cap-flattening map. -/
theorem sphere_northPoleCapConeCosinePowerTailBelowHalf_from_capConeFlatteningMap :
    sphere_northPoleCapConeCosinePowerTailBelowHalf :=
  sphere_northPoleCapConeCosinePowerTailBelowHalf_of_capConeCosinePowerTail
    sphere_northPoleCapConeCosinePowerTail_from_capConeFlatteningMap

/-- The homogeneous map sends the source open cone onto the target open cone for
one fibre. -/
theorem finRealSphereReflectionMap_homogeneousMap_image_sourceCone
    (n : ℕ) (p y u : FinRealSphere n) :
    finRealSphereReflectionHomogeneousMap n y (fibreConeData n p y).2.2 u ''
      (finRealSphereRadialOpenCone n (fibreConeData n p y).1) =
      finRealSphereRadialOpenCone n (fibreConeData n p y).2.1 :=
  homogeneousMap_image_sourceCone n p y u

/-- Injectivity of the homogeneous map on the source open cone for one fibre. -/
theorem finRealSphereReflectionMap_homogeneousMap_injOn_sourceCone
    (n : ℕ) (p y u : FinRealSphere n) :
    Set.InjOn
      (finRealSphereReflectionHomogeneousMap n y (fibreConeData n p y).2.2 u)
      (finRealSphereRadialOpenCone n (fibreConeData n p y).1) :=
  homogeneousMap_injOn_sourceCone n p y u

/-- On the open radial cone, the homogeneous map preserves radial direction data:
`dir (Ψ z) = φ (dir z)`. -/
theorem finRealSphereReflectionHomogeneousMap_radialDirectionFrom_eq
    {n : ℕ} (y : FinRealSphere n)
    (φ : FinRealSphere n → FinRealSphere n) (u : FinRealSphere n)
    {S : Set (FinRealSphere n)} {z : FinRealEuclideanSpace n}
    (hz : z ∈ finRealSphereRadialOpenCone n S) :
    finRealSphereRadialDirectionFrom u
        (finRealSphereReflectionHomogeneousMap n y φ u z) =
      φ (finRealSphereRadialDirectionFrom u z) := by
  have hz0 : z ≠ 0 := by
    rcases hz with ⟨r, hr, w, ⟨x, _, rfl⟩, rfl⟩
    exact smul_ne_zero hr.1.ne' (finRealSphere_ne_zero n x)
  let v := finRealSphereRadialDirectionFrom u z
  have hΨ :
      (finRealSphereReflectionHomogeneousMap n y φ u z :
          FinRealEuclideanSpace n) =
        ‖z‖ • ((φ v : FinRealEuclideanSpace n)) := by
    simp [finRealSphereReflectionHomogeneousMap, v]
  have hφnorm : ‖((φ v : FinRealEuclideanSpace n))‖ = 1 :=
    finRealSphere_norm_coe n (φ v)
  have hw0 :
      (finRealSphereReflectionHomogeneousMap n y φ u z :
          FinRealEuclideanSpace n) ≠ 0 := by
    rw [hΨ]
    exact smul_ne_zero (norm_pos_iff.mpr hz0).ne' (finRealSphere_ne_zero n (φ v))
  apply Subtype.ext
  show
    (finRealSphereRadialDirectionFrom u
        (finRealSphereReflectionHomogeneousMap n y φ u z) :
        FinRealEuclideanSpace n) =
      (φ v : FinRealEuclideanSpace n)
  unfold finRealSphereRadialDirectionFrom
  rw [dif_neg hw0]
  have hnorm :
      ‖finRealSphereReflectionHomogeneousMap n y φ u z‖ = ‖z‖ := by
    rw [hΨ, norm_smul, hφnorm, Real.norm_eq_abs, abs_of_pos (norm_pos_iff.mpr hz0),
      mul_one]
  change
      (‖finRealSphereReflectionHomogeneousMap n y φ u z‖⁻¹ •
          finRealSphereReflectionHomogeneousMap n y φ u z :
        FinRealEuclideanSpace n) =
      (φ v : FinRealEuclideanSpace n)
  rw [hnorm, hΨ, smul_smul, inv_mul_cancel₀ (norm_pos_iff.mpr hz0).ne', one_smul]

/-- Measurability of the source-side open-cone integrand. -/
theorem measurable_finRealSphereReflectionMap_openCone_sourceIntegrand
    {n : ℕ} (p y u : FinRealSphere n)
    (F : FinRealSphere n → ℝ≥0∞) (hF : Measurable F) :
    Measurable
      (fun z : FinRealEuclideanSpace n =>
        (2 : ℝ≥0∞) *
          F ((fibreConeData n p y).2.2
            (finRealSphereRadialDirectionFrom (n := n) u z))) := by
  have hdir := measurable_finRealSphereRadialDirectionFrom u
  have hφ := fibreConeData_φ_meas n p y
  exact measurable_const.mul (hF.comp (hφ.comp hdir))

/-- Measurability of the target-side open-cone integrand. -/
theorem measurable_finRealSphereReflectionMap_openCone_targetIntegrand
    {n : ℕ} (_p y u : FinRealSphere n)
    (F : FinRealSphere n → ℝ≥0∞) (hF : Measurable F) :
    Measurable
      (fun w : FinRealEuclideanSpace n =>
        F (finRealSphereRadialDirectionFrom (n := n) u w) *
          finRealSpherePolarizationKernel n
            (finRealSphereRadialDirectionFrom (n := n) u w) y) := by
  have hdir := measurable_finRealSphereRadialDirectionFrom u
  have hkernel := measurable_finRealSpherePolarizationKernel_right n y
  exact (hF.comp hdir).mul (hkernel.comp hdir)

/-!
### Homogeneous-map Jacobian helpers for the open-cone change of variables
-/

/-- Ambient unit direction chart away from the origin.  On the open cones below this
agrees with `finRealSphereRadialDirectionFrom`. -/
noncomputable def finRealSphereAmbientUnitDirection
    {n : ℕ} (u : FinRealSphere n) :
    FinRealEuclideanSpace n → FinRealEuclideanSpace n :=
  fun z =>
    if z = 0 then (u : FinRealEuclideanSpace n) else ‖z‖⁻¹ • z

theorem finRealSphereAmbientUnitDirection_eq_norm_smul
    {n : ℕ} (u : FinRealSphere n) {z : FinRealEuclideanSpace n} (hz : z ≠ 0) :
    finRealSphereAmbientUnitDirection u z = ‖z‖⁻¹ • z := by
  simp [finRealSphereAmbientUnitDirection, hz]

theorem finRealSphereRadialDirectionFrom_coe_eq_ambientUnitDirection
    {n : ℕ} (u : FinRealSphere n) {z : FinRealEuclideanSpace n} (hz : z ≠ 0) :
    (finRealSphereRadialDirectionFrom u z : FinRealEuclideanSpace n) =
      finRealSphereAmbientUnitDirection u z := by
  unfold finRealSphereRadialDirectionFrom finRealSphereAmbientUnitDirection
  simp [hz]

private def finRealSphereAmbientUnitDirectionFDeriv
    {n : ℕ} (z : FinRealEuclideanSpace n) (_hz : z ≠ 0) :
    FinRealEuclideanSpace n →L[ℝ] FinRealEuclideanSpace n :=
  ‖z‖⁻¹ • (ContinuousLinearMap.id ℝ (FinRealEuclideanSpace n) -
    (‖z‖ ^ 2)⁻¹ •
      (ContinuousLinearMap.toSpanSingleton ℝ z).comp (innerSL ℝ z))

private theorem inner_z_finRealSphereAmbientUnitDirection_eq_norm
    {n : ℕ} (u : FinRealSphere n) {z : FinRealEuclideanSpace n} (hz : z ≠ 0) :
    inner ℝ z (finRealSphereAmbientUnitDirection u z) = ‖z‖ := by
  rw [finRealSphereAmbientUnitDirection_eq_norm_smul u hz, inner_smul_right,
    real_inner_self_eq_norm_sq]
  field_simp [norm_ne_zero_iff.mpr hz]

private theorem finRealSphereRadialOpenCone_ne_zero
    {n : ℕ} {S : Set (FinRealSphere n)} {z : FinRealEuclideanSpace n}
    (hz : z ∈ finRealSphereRadialOpenCone n S) : z ≠ 0 := by
  rcases hz with ⟨r, hr, _, ⟨x, _, rfl⟩, rfl⟩
  exact smul_ne_zero hr.1.ne' (finRealSphere_ne_zero n x)

private theorem hasFDerivAt_norm_at
    {n : ℕ} {z : FinRealEuclideanSpace n} (hz : z ≠ 0) :
    HasFDerivAt (fun w : FinRealEuclideanSpace n => ‖w‖)
      (‖z‖⁻¹ • innerSL ℝ z) z := by
  have hsq : HasFDerivAt (fun w : FinRealEuclideanSpace n => ‖w‖ ^ 2)
      (2 • innerSL ℝ z) z :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hpos : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_pos_iff.mpr hz).ne'
  have hsqrt := hsq.sqrt hpos
  have h₁ : HasFDerivAt (fun w : FinRealEuclideanSpace n => Real.sqrt (‖w‖ ^ 2))
      (‖z‖⁻¹ • innerSL ℝ z) z := by
    convert hsqrt using 1
    ext v
    simp [innerSL_apply_apply, real_inner_comm]
    field_simp [hpos]
  have h₂ : (fun w : FinRealEuclideanSpace n => ‖w‖) =ᶠ[nhds z]
      (fun w : FinRealEuclideanSpace n => Real.sqrt (‖w‖ ^ 2)) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hz] with w hw
    exact (Real.sqrt_sq (norm_nonneg w)).symm
  exact HasFDerivAt.congr_of_eventuallyEq h₁ h₂

private theorem hasFDerivAt_norm_inv_at
    {n : ℕ} {z : FinRealEuclideanSpace n} (hz : z ≠ 0) :
    HasFDerivAt (fun w : FinRealEuclideanSpace n => ‖w‖⁻¹)
      (-(‖z‖ ^ 3)⁻¹ • innerSL ℝ z) z := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hf : HasDerivAt (fun t : ℝ => t⁻¹) (-(‖z‖ ^ 2)⁻¹) (‖z‖) := hasDerivAt_inv hn
  convert hf.hasFDerivAt.comp z (hasFDerivAt_norm_at (n := n) (z := z) hz) using 1
  ext v
  simp [innerSL_apply_apply, real_inner_comm, hn]
  field_simp

theorem hasFDerivAt_finRealSphereAmbientUnitDirection
    {n : ℕ} (u : FinRealSphere n) {z : FinRealEuclideanSpace n} (hz : z ≠ 0) :
    HasFDerivAt (finRealSphereAmbientUnitDirection u)
      (finRealSphereAmbientUnitDirectionFDeriv z hz) z := by
  have h_eq : finRealSphereAmbientUnitDirection u =ᶠ[nhds z] fun w => ‖w‖⁻¹ • w := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hz] with w hw
    simp [finRealSphereAmbientUnitDirection, show w ≠ 0 from hw]
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hnorm := hasFDerivAt_norm_at (n := n) (z := z) hz
  have hinv := hasFDerivAt_norm_inv_at (n := n) (z := z) hz
  have hsmul :
      HasFDerivAt (fun w : FinRealEuclideanSpace n => ‖w‖⁻¹ • w)
        (finRealSphereAmbientUnitDirectionFDeriv z hz) z := by
    convert hinv.smul (hasFDerivAt_id z) using 1
    ext v
    simp [finRealSphereAmbientUnitDirectionFDeriv, ContinuousLinearMap.toSpanSingleton_apply,
      innerSL_apply_apply, real_inner_comm, hn]
    ring_nf <;> field_simp [hn]
  exact HasFDerivAt.congr_of_eventuallyEq hsmul h_eq

theorem hasFDerivAt_finRealSpherePolarizationParamAmbient
    (n : ℕ) (y v : FinRealSphere n) {z : FinRealEuclideanSpace n} (hz : z ≠ 0) :
    HasFDerivAt
      (fun w : FinRealEuclideanSpace n =>
        (finRealSpherePolarizationParam (finRealSphereReflectionMap n) y
          (finRealSphereRadialDirectionFrom v w) :
          FinRealEuclideanSpace n))
      (SphericalPolarization.GeometricKernel.reflectionFDeriv
          (y : FinRealEuclideanSpace n)
          (finRealSphereAmbientUnitDirection v z) ∘L
        finRealSphereAmbientUnitDirectionFDeriv z hz) z := by
  have h_eq :
      (fun w : FinRealEuclideanSpace n =>
          (finRealSpherePolarizationParam (finRealSphereReflectionMap n) y
            (finRealSphereRadialDirectionFrom v w) :
            FinRealEuclideanSpace n)) =ᶠ[nhds z]
        fun w : FinRealEuclideanSpace n =>
          SphericalPolarization.GeometricKernel.reflection
            (finRealSphereAmbientUnitDirection v w) (y : FinRealEuclideanSpace n) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hz] with w hw
    rw [finRealSpherePolarizationParam_coe_eq_reflection,
      finRealSphereRadialDirectionFrom_coe_eq_ambientUnitDirection v hw]
  have hdir :
      HasFDerivAt (finRealSphereAmbientUnitDirection v)
        (finRealSphereAmbientUnitDirectionFDeriv z hz) z :=
    hasFDerivAt_finRealSphereAmbientUnitDirection v hz
  have hrefl :
      HasFDerivAt
        (fun w : FinRealEuclideanSpace n =>
          SphericalPolarization.GeometricKernel.reflection
            (finRealSphereAmbientUnitDirection v w) (y : FinRealEuclideanSpace n))
        (SphericalPolarization.GeometricKernel.reflectionFDeriv
            (y : FinRealEuclideanSpace n) (finRealSphereAmbientUnitDirection v z) ∘L
          finRealSphereAmbientUnitDirectionFDeriv z hz) z := by
    exact
      (SphericalPolarization.GeometricKernel.hasFDerivAt_reflection
          (y := (y : FinRealEuclideanSpace n))
          (v := finRealSphereAmbientUnitDirection v z)).comp z hdir
  exact HasFDerivAt.congr_of_eventuallyEq hrefl h_eq

/-- Explicit ambient Fréchet derivative of the homogeneous extension at a nonzero point. -/
noncomputable def finRealSphereReflectionHomogeneousMapFDeriv
    (n : ℕ) (y : FinRealSphere n)
    (φ : FinRealSphere n → FinRealSphere n)
    (u : FinRealSphere n) {z : FinRealEuclideanSpace n} (hz : z ≠ 0) :
    FinRealEuclideanSpace n →L[ℝ] FinRealEuclideanSpace n :=
  let w : FinRealEuclideanSpace n :=
    (φ (finRealSphereRadialDirectionFrom (n := n) u z) : FinRealEuclideanSpace n)
  let dφ :=
    SphericalPolarization.GeometricKernel.reflectionFDeriv
        (y : FinRealEuclideanSpace n)
        (finRealSphereAmbientUnitDirection u z) ∘L
      finRealSphereAmbientUnitDirectionFDeriv z hz
  ‖z‖ • dφ + (‖z‖⁻¹ • innerSL ℝ z).smulRight w

theorem hasFDerivAt_finRealSphereReflectionHomogeneousMap_fibre
    (n : ℕ) (p y u : FinRealSphere n) {z : FinRealEuclideanSpace n} (hz : z ≠ 0) :
    HasFDerivAt
      (finRealSphereReflectionHomogeneousMap n y (fibreConeData n p y).2.2 u)
      (finRealSphereReflectionHomogeneousMapFDeriv n y (fibreConeData n p y).2.2 u hz) z := by
  let φ := (fibreConeData n p y).2.2
  have hval :
      HasFDerivAt (fun w : FinRealEuclideanSpace n =>
          (φ (finRealSphereRadialDirectionFrom u w) : FinRealEuclideanSpace n))
        (SphericalPolarization.GeometricKernel.reflectionFDeriv
            (y : FinRealEuclideanSpace n)
            (finRealSphereAmbientUnitDirection u z) ∘L
          finRealSphereAmbientUnitDirectionFDeriv z hz) z := by
    unfold φ fibreConeData
    exact hasFDerivAt_finRealSpherePolarizationParamAmbient n y u hz
  have hnorm := hasFDerivAt_norm_at (n := n) (z := z) hz
  have hmul := hnorm.smul hval
  convert hmul using 1 <;> simp [finRealSphereReflectionHomogeneousMapFDeriv,
    finRealSphereReflectionHomogeneousMap]

theorem hasFDerivWithinAt_finRealSphereReflectionHomogeneousMap_fibre_openCone
    (n : ℕ) (p y u : FinRealSphere n)
    {z : FinRealEuclideanSpace n}
    (hz : z ∈ finRealSphereRadialOpenCone n (fibreConeData n p y).1) :
    HasFDerivWithinAt
      (finRealSphereReflectionHomogeneousMap n y (fibreConeData n p y).2.2 u)
      (finRealSphereReflectionHomogeneousMapFDeriv n y (fibreConeData n p y).2.2 u
        (finRealSphereRadialOpenCone_ne_zero hz))
      (finRealSphereRadialOpenCone n (fibreConeData n p y).1) z := by
  have hz0 := finRealSphereRadialOpenCone_ne_zero hz
  exact
    (hasFDerivAt_finRealSphereReflectionHomogeneousMap_fibre n p y u hz0).hasFDerivWithinAt

theorem finRealSphereRadialDirectionFrom_mem_fibreDomain_of_mem_openCone
    (n : ℕ) (p y u : FinRealSphere n)
    {z : FinRealEuclideanSpace n}
    (hz : z ∈ finRealSphereRadialOpenCone n (fibreConeData n p y).1) :
    finRealSphereRadialDirectionFrom (n := n) u z ∈ (fibreConeData n p y).1 := by
  exact finRealSphereRadialDirectionFrom_mapsTo_openCone u (fibreConeData n p y).1 hz

theorem finRealSphereRadialDirectionFrom_mem_directionHemisphere_of_mem_openCone
    (n : ℕ) (p y u : FinRealSphere n)
    {z : FinRealEuclideanSpace n}
    (hz : z ∈ finRealSphereRadialOpenCone n (fibreConeData n p y).1) :
    finRealSphereRadialDirectionFrom (n := n) u z ∈
      finRealSphereDirectionHemisphere n y := by
  have h := finRealSphereRadialDirectionFrom_mem_fibreDomain_of_mem_openCone n p y u hz
  exact h.2

private lemma finRealSphereAmbientUnitDirectionFDeriv_apply_self
    {n : ℕ} (u : FinRealSphere n) {z : FinRealEuclideanSpace n} (hz : z ≠ 0) :
    finRealSphereAmbientUnitDirectionFDeriv z hz (finRealSphereAmbientUnitDirection u z) = 0 := by
  simp [finRealSphereAmbientUnitDirectionFDeriv, finRealSphereAmbientUnitDirection_eq_norm_smul u hz,
    ContinuousLinearMap.toSpanSingleton_apply, innerSL_apply_apply, inner_smul_right,
    real_inner_self_eq_norm_sq, hz]

private lemma finRealSphereAmbientUnitDirectionFDeriv_apply_tangent
    {n : ℕ} {z w : FinRealEuclideanSpace n} (hz : z ≠ 0) (hinner : inner ℝ z w = 0) :
    finRealSphereAmbientUnitDirectionFDeriv z hz w = ‖z‖⁻¹ • w := by
  dsimp [finRealSphereAmbientUnitDirectionFDeriv]
  simp [ContinuousLinearMap.toSpanSingleton_apply, innerSL_apply_apply, hinner, sub_eq_add_neg]

theorem finRealSphereReflectionHomogeneousMapFDeriv_apply_unitDirection
    {n : ℕ} (y : FinRealSphere n)
    (φ : FinRealSphere n → FinRealSphere n) (u : FinRealSphere n)
    {z : FinRealEuclideanSpace n} (hz : z ≠ 0) :
    finRealSphereReflectionHomogeneousMapFDeriv n y φ u hz
      ((‖z‖ : ℝ)⁻¹ • z) =
      (φ (finRealSphereRadialDirectionFrom u z) : FinRealEuclideanSpace n) := by
  let udir := finRealSphereAmbientUnitDirection u z
  have hz' : (‖z‖ : ℝ)⁻¹ • z = udir :=
    (finRealSphereAmbientUnitDirection_eq_norm_smul u hz).symm
  rw [hz']
  have hD0 := finRealSphereAmbientUnitDirectionFDeriv_apply_self u hz
  have hinner := inner_z_finRealSphereAmbientUnitDirection_eq_norm u hz
  simp only [finRealSphereReflectionHomogeneousMapFDeriv, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply, innerSL_apply_apply]
  rw [hD0, map_zero, smul_zero, hinner, zero_add]
  simp only [smul_eq_mul]
  field_simp [norm_ne_zero_iff.mpr hz]
  simp only [one_smul]

theorem finRealSphereReflectionHomogeneousMapFDeriv_apply_tangent
    {n : ℕ} (y : FinRealSphere n)
    (φ : FinRealSphere n → FinRealSphere n) (u : FinRealSphere n)
    {z w : FinRealEuclideanSpace n} (hz : z ≠ 0)
    (hw : inner ℝ (finRealSphereAmbientUnitDirection u z) w = 0) :
    finRealSphereReflectionHomogeneousMapFDeriv n y φ u hz w =
      SphericalPolarization.GeometricKernel.reflectionFDeriv
        (y : FinRealEuclideanSpace n)
        (finRealSphereAmbientUnitDirection u z) w := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hinner : inner ℝ z w = 0 := by
    rw [finRealSphereAmbientUnitDirection_eq_norm_smul u hz] at hw
    rw [inner_smul_left] at hw
    exact (mul_eq_zero.mp hw).resolve_left (inv_ne_zero hn)
  have hD := finRealSphereAmbientUnitDirectionFDeriv_apply_tangent hz hinner
  simp only [finRealSphereReflectionHomogeneousMapFDeriv, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply, innerSL_apply_apply]
  rw [hD, map_smul, hinner, smul_zero, zero_smul, smul_smul]
  field_simp [hn]
  simp [one_smul, add_zero]

/-- On tangent directions, the homogeneous extension derivative equals the ambient
reflection derivative: the radial and unit-direction scalings cancel. -/
theorem finRealSphereReflectionHomogeneousMapFDeriv_apply_orthogonal
    {n : ℕ} (y : FinRealSphere n)
    (φ : FinRealSphere n → FinRealSphere n) (u : FinRealSphere n)
    {z w : FinRealEuclideanSpace n} (hz : z ≠ 0)
    (hw : inner ℝ (finRealSphereAmbientUnitDirection u z) w = 0) :
    finRealSphereReflectionHomogeneousMapFDeriv n y φ u hz w =
      SphericalPolarization.GeometricKernel.reflectionFDeriv
        (y : FinRealEuclideanSpace n)
        (finRealSphereAmbientUnitDirection u z) w :=
  finRealSphereReflectionHomogeneousMapFDeriv_apply_tangent y φ u hz hw

private lemma finRealSphere_unit_neg_ne_self
    {n : ℕ} {y : FinRealSphere n}
    (hy : ‖(y : FinRealEuclideanSpace n)‖ = 1) :
    (-(y : FinRealEuclideanSpace n)) ≠ (y : FinRealEuclideanSpace n) := by
  intro h
  have h0 : (2 : ℝ) • (y : FinRealEuclideanSpace n) = 0 := by
    calc (2 : ℝ) • (y : FinRealEuclideanSpace n)
        = (y : FinRealEuclideanSpace n) + (y : FinRealEuclideanSpace n) := two_smul ..
      _ = (-(y : FinRealEuclideanSpace n)) + (y : FinRealEuclideanSpace n) := by rw [h]
      _ = 0 := neg_add_cancel (y : FinRealEuclideanSpace n)
  exact finRealSphere_ne_zero n y ((smul_eq_zero.mp h0).resolve_left (two_ne_zero' ℝ))

private lemma finRealSphere_chordalHalf_pos_of_ne
    {x y : FinRealEuclideanSpace n} (hne : x ≠ y) :
    0 < SphericalPolarization.GeometricKernel.chordalHalf x y := by
  dsimp [SphericalPolarization.GeometricKernel.chordalHalf]
  exact div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) (by norm_num)

private lemma finRealSphere_chordalHalf_neg_self
    {n : ℕ} {y : FinRealSphere n}
    (hy : ‖(y : FinRealEuclideanSpace n)‖ = 1) :
    SphericalPolarization.GeometricKernel.chordalHalf
      (-(y : FinRealEuclideanSpace n)) (y : FinRealEuclideanSpace n) = 1 := by
  dsimp [SphericalPolarization.GeometricKernel.chordalHalf]
  have hnorm : ‖-(y : FinRealEuclideanSpace n) - (y : FinRealEuclideanSpace n)‖ = 2 := by
    have hsub :
        -(y : FinRealEuclideanSpace n) - (y : FinRealEuclideanSpace n) =
          -(2 : ℝ) • (y : FinRealEuclideanSpace n) := by
      simp [two_smul, sub_eq_add_neg]
    rw [hsub, norm_smul, hy]
    norm_num
  rw [hnorm]
  norm_num

/-- Leaf-1 packaged as an ambient determinant density on the homogeneous extension:
a.e. on the source open cone, `|det DΨ| * K(φ(dir z), y) = 2`. -/
theorem finRealSphereReflectionHomogeneousMap_abs_det_mul_kernel_eq_two
    (n : ℕ) (hn2 : 2 ≤ n) (p y u : FinRealSphere n)
    {z : FinRealEuclideanSpace n}
    (hz : z ∈ finRealSphereRadialOpenCone n (fibreConeData n p y).1) :
    ENNReal.ofReal
        |(finRealSphereReflectionHomogeneousMapFDeriv n y (fibreConeData n p y).2.2 u
            (finRealSphereRadialOpenCone_ne_zero hz)).det| *
      finRealSpherePolarizationKernel n
        ((fibreConeData n p y).2.2
          (finRealSphereRadialDirectionFrom (n := n) u z)) y =
      (2 : ℝ≥0∞) := by
  classical
  haveI : NeZero n := neZero_of_two_le hn2
  let φ := (fibreConeData n p y).2.2
  let v := finRealSphereRadialDirectionFrom (n := n) u z
  have hz0 := finRealSphereRadialOpenCone_ne_zero hz
  have hvDir :=
    finRealSphereRadialDirectionFrom_mem_directionHemisphere_of_mem_openCone n p y u hz
  have hy : ‖(y : FinRealEuclideanSpace n)‖ = 1 := finRealSphere_norm_coe n y
  have hv : ‖(v : FinRealEuclideanSpace n)‖ = 1 := finRealSphere_norm_coe n v
  have hpos : 0 < inner ℝ (y : FinRealEuclideanSpace n) (v : FinRealEuclideanSpace n) :=
    hvDir
  have hφv :
      (φ v : FinRealEuclideanSpace n) =
        SphericalPolarization.GeometricKernel.reflection
          (v : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n) := by
    simpa using finRealSpherePolarizationParam_coe_eq_reflection n y v
  have hK :
      finRealSpherePolarizationKernel n (φ v) y =
        SphericalPolarization.GeometricKernel.sphericalKernelChordalENNReal n
          (SphericalPolarization.GeometricKernel.reflection
            (v : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n))
          (y : FinRealEuclideanSpace n) := by
    unfold finRealSpherePolarizationKernel
    rw [hφv]
  by_cases hvy : v = y
  · -- Symmetry at the pole direction: both sides reduce by direct evaluation.
    have hvEq :
        (v : FinRealEuclideanSpace n) =
          finRealSphereAmbientUnitDirection u z := by
      rw [← finRealSphereRadialDirectionFrom_coe_eq_ambientUnitDirection u hz0]
    have hyEq :
        (y : FinRealEuclideanSpace n) =
          finRealSphereAmbientUnitDirection u z := by
      rw [← hvy, hvEq]
    have hrefl :
        SphericalPolarization.GeometricKernel.reflection
            (v : FinRealEuclideanSpace n) (v : FinRealEuclideanSpace n) =
          -(v : FinRealEuclideanSpace n) := by
      suffices
          SphericalPolarization.GeometricKernel.reflection
              (y : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n) =
            -(y : FinRealEuclideanSpace n) by
        simpa [hvy] using this
      unfold SphericalPolarization.GeometricKernel.reflection
      simp [hy, real_inner_self_eq_norm_sq, two_smul, sub_eq_add_neg]
    have hφv' :
        (φ v : FinRealEuclideanSpace n) = -(v : FinRealEuclideanSpace n) := by
      calc
        (φ v : FinRealEuclideanSpace n) =
            SphericalPolarization.GeometricKernel.reflection
              (v : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n) := hφv
        _ =
            SphericalPolarization.GeometricKernel.reflection
              (v : FinRealEuclideanSpace n) (v : FinRealEuclideanSpace n) := by rw [hvy]
        _ = -(v : FinRealEuclideanSpace n) := hrefl
    have hrefly :
        SphericalPolarization.GeometricKernel.reflection
            (y : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n) =
          -(y : FinRealEuclideanSpace n) := by
      simpa [hvy] using hrefl
    have hKpos :
        finRealSpherePolarizationKernel n (φ v) v ≠ 0 := by
      have hKvy :
          finRealSpherePolarizationKernel n (φ v) v =
            finRealSpherePolarizationKernel n (φ y) y := by
        congr 1 <;> rw [hvy]
      have hK' := by simpa [hvy] using hK
      rw [hKvy, hK', hrefly]
      unfold SphericalPolarization.GeometricKernel.sphericalKernelChordalENNReal
      have hne := finRealSphere_unit_neg_ne_self hy
      rw [SphericalPolarization.GeometricKernel.sphericalKernelChordal_of_ne n hne,
        finRealSphere_chordalHalf_neg_self hy]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
    have hKreal :
        (finRealSpherePolarizationKernel n (φ v) v).toReal =
          ((2 : ℝ) ^ (n - 2))⁻¹ := by
      have hKvy :
          finRealSpherePolarizationKernel n (φ v) v =
            finRealSpherePolarizationKernel n (φ y) y := by
        congr 1 <;> rw [hvy]
      have hK' := by simpa [hvy] using hK
      rw [hKvy, hK', hrefly]
      unfold SphericalPolarization.GeometricKernel.sphericalKernelChordalENNReal
      have hne := finRealSphere_unit_neg_ne_self hy
      rw [SphericalPolarization.GeometricKernel.sphericalKernelChordal_of_ne n hne,
        finRealSphere_chordalHalf_neg_self hy, one_pow]
      simp [one_zpow, inv_one, one_mul, ENNReal.toReal_ofReal (show 0 ≤ ((2 : ℝ) ^ (n - 2))⁻¹ by positivity)]
    have hdet :
        |(finRealSphereReflectionHomogeneousMapFDeriv n y φ u hz0).det| =
          (2 : ℝ) / (finRealSpherePolarizationKernel n (φ v) v).toReal := by
      have hdetpow :=
        SphericalPolarization.GeometricKernel.abs_det_reflectionExtension_at_pole
          (n := n) (by omega : 1 < n) hv
          (by rw [finRealSphere_moduleFinrank n])
          (finRealSphereReflectionHomogeneousMapFDeriv n y φ u hz0)
          (by
            calc (finRealSphereReflectionHomogeneousMapFDeriv n y φ u hz0)
                    (v : FinRealEuclideanSpace n)
                = (finRealSphereReflectionHomogeneousMapFDeriv n y φ u hz0)
                    (finRealSphereAmbientUnitDirection u z) := by rw [hvEq]
              _ = (finRealSphereReflectionHomogeneousMapFDeriv n y φ u hz0)
                    ((‖z‖ : ℝ)⁻¹ • z) := by
                    rw [← finRealSphereAmbientUnitDirection_eq_norm_smul u hz0]
              _ = (φ v : FinRealEuclideanSpace n) :=
                    finRealSphereReflectionHomogeneousMapFDeriv_apply_unitDirection y φ u hz0
              _ = -(v : FinRealEuclideanSpace n) := hφv')
          (by
            intro w hw
            have hyudir :
                inner ℝ (y : FinRealEuclideanSpace n) (finRealSphereAmbientUnitDirection u z) = 1 := by
              rw [← hyEq, real_inner_self_eq_norm_sq, hy]
              norm_num
            have hwy : inner ℝ (y : FinRealEuclideanSpace n) w = 0 := by
              simpa [hvy] using hw
            rw [finRealSphereReflectionHomogeneousMapFDeriv_apply_orthogonal y φ u hz0
                (by rw [← hyEq]; simpa [hvy] using hw),
              SphericalPolarization.GeometricKernel.reflectionFDeriv_apply, hwy, hyudir]
            simp [two_smul, neg_smul])
      rw [hdetpow, hKreal, div_eq_mul_inv, inv_inv]
      have hnpos : 0 < (2 : ℝ) ^ (n - 2) := pow_pos (by norm_num) _
      field_simp [hnpos.ne']
      rw [show n - 1 = (n -  2) + 1 from by omega, pow_succ]
      ring
    have hKchord :
        SphericalPolarization.GeometricKernel.sphericalKernelChordal n
            (SphericalPolarization.GeometricKernel.reflection
              (v : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n))
            (y : FinRealEuclideanSpace n) =
          ((2 : ℝ) ^ (n - 2))⁻¹ := by
      rw [hvy, hrefly,
        SphericalPolarization.GeometricKernel.sphericalKernelChordal_of_ne n
          (finRealSphere_unit_neg_ne_self hy),
        finRealSphere_chordalHalf_neg_self hy]
      ring
    have hreal :
        |(finRealSphereReflectionHomogeneousMapFDeriv n y φ u hz0).det| *
          SphericalPolarization.GeometricKernel.sphericalKernelChordal n
            (SphericalPolarization.GeometricKernel.reflection
              (v : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n))
            (y : FinRealEuclideanSpace n) =
          (2 : ℝ) := by
      rw [hdet, hKchord, hKreal]
      have hkne : ((2 : ℝ) ^ (n - 2))⁻¹ ≠ 0 := by positivity
      field_simp [hkne]
    have hKeq :
        finRealSpherePolarizationKernel n (φ v) y =
          ENNReal.ofReal
            (SphericalPolarization.GeometricKernel.sphericalKernelChordal n
              (SphericalPolarization.GeometricKernel.reflection
                (v : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n))
              (y : FinRealEuclideanSpace n)) := by
      rw [hK]
      dsimp [SphericalPolarization.GeometricKernel.sphericalKernelChordalENNReal]
    have hposDet :
        0 ≤ |(finRealSphereReflectionHomogeneousMapFDeriv n y φ u hz0).det| :=
      abs_nonneg _
    have hposK :
        0 ≤ SphericalPolarization.GeometricKernel.sphericalKernelChordal n
            (SphericalPolarization.GeometricKernel.reflection
              (v : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n))
            (y : FinRealEuclideanSpace n) := by
      have hne : SphericalPolarization.GeometricKernel.reflection
            (v : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n) ≠
          (y : FinRealEuclideanSpace n) := by
        rw [hvy, hrefly]
        exact finRealSphere_unit_neg_ne_self hy
      rw [SphericalPolarization.GeometricKernel.sphericalKernelChordal_of_ne n hne]
      rw [show SphericalPolarization.GeometricKernel.reflection
            (v : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n) =
          -(y : FinRealEuclideanSpace n) from by rw [hvy, hrefly]]
      rw [finRealSphere_chordalHalf_neg_self hy, one_pow]
      simp only [one_zpow, inv_one, one_mul]
      positivity
    have hposMul :
        0 ≤ |(finRealSphereReflectionHomogeneousMapFDeriv n y φ u hz0).det| *
          SphericalPolarization.GeometricKernel.sphericalKernelChordal n
            (SphericalPolarization.GeometricKernel.reflection
              (v : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n))
            (y : FinRealEuclideanSpace n) :=
      mul_nonneg hposDet hposK
    rw [hKeq, ← ENNReal.ofReal_mul hposDet, hreal]
    norm_num
  · have hmer :
        SphericalPolarization.GeometricKernel.meridianDirection
            (y : FinRealEuclideanSpace n) (v : FinRealEuclideanSpace n) ≠ 0 := by
      intro h0
      have hparallel : (y : FinRealEuclideanSpace n) =
          (inner ℝ (y : FinRealEuclideanSpace n) (v : FinRealEuclideanSpace n)) •
            (v : FinRealEuclideanSpace n) := by
        unfold SphericalPolarization.GeometricKernel.meridianDirection at h0
        exact eq_of_sub_eq_zero h0
      have hvy' : v = y := by
        have hc : (inner ℝ (y : FinRealEuclideanSpace n) (v : FinRealEuclideanSpace n)) = 1 := by
          have hcnorm : |inner ℝ (y : FinRealEuclideanSpace n) (v : FinRealEuclideanSpace n)| = 1 := by
            have := congrArg norm hparallel
            rw [hy, norm_smul, hv, mul_one] at this
            exact this.symm
          rw [← abs_of_pos hpos, hcnorm]
        apply Subtype.ext
        show (v : FinRealEuclideanSpace n) = (y : FinRealEuclideanSpace n)
        rw [hparallel, hc, one_smul]
      exact hvy hvy'
    let m := n - 2
    have hm : m + 2 = n := by omega
    have hE : Module.finrank ℝ (FinRealEuclideanSpace n) = m + 2 := by
      rw [finRealSphere_moduleFinrank n, hm]
    have hFin :
        Fact (Module.finrank ℝ
            (SphericalPolarization.GeometricKernel.tangentSubspace
              (SphericalPolarization.GeometricKernel.reflection
                (v : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n))) =
          m + 1) := by
      refine ⟨?_⟩
      convert finRealSphere_reflection_tangentSubspace_finrank n hn2 y v hvDir using 1
    haveI := hFin
    let ρ :=
      SphericalPolarization.GeometricKernel.reflection
        (v : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n)
    let tang := SphericalPolarization.GeometricKernel.tangentSubspace ρ
    have hfin_tang : Module.finrank ℝ tang = m + 1 := hFin.out
    let o :=
      ((stdOrthonormalBasis ℝ tang).reindex (finCongr hfin_tang)).toBasis.orientation
    have hLeaf :=
      finRealSphereReflectionMap_tangentJacobian_eq_polarizationKernel n hn2 y v hvDir hmer hFin o
    have hvol :=
      SphericalPolarization.GeometricKernel.abs_volumeForm_reflectionTangentDeriv_of_ambient_finrank
        (m := m) o hy hv hpos hmer hE
    have hframe :
        (fun i => finRealSphereReflectionTangentJacobianFrame n hn2 y v hmer i) =
          fun i =>
            SphericalPolarization.GeometricKernel.reflectionTangentDeriv
              (y : FinRealEuclideanSpace n) (v : FinRealEuclideanSpace n) hv
              (SphericalPolarization.GeometricKernel.adaptedTangentFrame
                (y : FinRealEuclideanSpace n) (v : FinRealEuclideanSpace n) hv
                (SphericalPolarization.GeometricKernel.planeOrthogonalSubspace.orthonormalBasisOfFinrank
                  (y := (y : FinRealEuclideanSpace n))
                  (v := (v : FinRealEuclideanSpace n)) m
                  (SphericalPolarization.GeometricKernel.planeOrthogonalSubspace_finrank_of_pair_linearIndependent
                    (y := (y : FinRealEuclideanSpace n))
                    (v := (v : FinRealEuclideanSpace n)) (m := m) hE
                    (SphericalPolarization.GeometricKernel.polarizationPair_linearIndependent_of_meridian_ne_zero
                      hv hmer))) i) := by
      funext i
      rfl
    have hvol' :
        |o.volumeForm (fun i => finRealSphereReflectionTangentJacobianFrame n hn2 y v hmer i)| =
          2 * (2 * inner ℝ (y : FinRealEuclideanSpace n) (v : FinRealEuclideanSpace n)) ^ m := by
      simpa [hframe] using hvol
    have hdet :
        |(finRealSphereReflectionHomogeneousMapFDeriv n y φ u hz0).det| =
          (2 : ℝ) * (2 * inner ℝ (y : FinRealEuclideanSpace n) (v : FinRealEuclideanSpace n)) ^ m := by
      have hvEq :
          (v : FinRealEuclideanSpace n) =
            finRealSphereAmbientUnitDirection u z := by
        rw [← finRealSphereRadialDirectionFrom_coe_eq_ambientUnitDirection u hz0]
      exact
        SphericalPolarization.GeometricKernel.abs_det_reflectionExtension_eq_tangentJacobianVolume
          (m := m) hy hv hpos hmer
          (by rw [finRealSphere_moduleFinrank n, hm])
          (finRealSphereReflectionHomogeneousMapFDeriv n y φ u hz0)
          (by
            calc (finRealSphereReflectionHomogeneousMapFDeriv n y φ u hz0)
                    (v : FinRealEuclideanSpace n)
                = (finRealSphereReflectionHomogeneousMapFDeriv n y φ u hz0)
                    (finRealSphereAmbientUnitDirection u z) := by rw [hvEq]
              _ = (finRealSphereReflectionHomogeneousMapFDeriv n y φ u hz0)
                    ((‖z‖ : ℝ)⁻¹ • z) := by
                    rw [← finRealSphereAmbientUnitDirection_eq_norm_smul u hz0]
              _ = (φ v : FinRealEuclideanSpace n) :=
                    (finRealSphereReflectionHomogeneousMapFDeriv_apply_unitDirection y φ u hz0).trans hφv)
          (by
            intro w hw
            have hw' :
                inner ℝ (finRealSphereAmbientUnitDirection u z) w = 0 := by
              rw [hvEq] at hw
              exact hw
            exact (finRealSphereReflectionHomogeneousMapFDeriv_apply_orthogonal y φ u hz0 hw').trans
              (by congr 1; rw [hvEq]))
    have hKpos : finRealSpherePolarizationKernel n (φ v) y ≠ 0 := by
      rw [hK]
      unfold SphericalPolarization.GeometricKernel.sphericalKernelChordalENNReal
      have hne :
          SphericalPolarization.GeometricKernel.reflection
              (v : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n) ≠
            (y : FinRealEuclideanSpace n) :=
        SphericalPolarization.GeometricKernel.reflection_ne_self_of_unit_pos hy hv hpos
      rw [SphericalPolarization.GeometricKernel.sphericalKernelChordal_of_ne n hne]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (by
        apply mul_pos (by positivity)
        exact inv_pos.mpr (pow_pos (finRealSphere_chordalHalf_pos_of_ne hne) (n - 2))))
    have hreal :
        |(finRealSphereReflectionHomogeneousMapFDeriv n y φ u hz0).det| *
          SphericalPolarization.GeometricKernel.sphericalKernelChordal n
            (SphericalPolarization.GeometricKernel.reflection
              (v : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n))
            (y : FinRealEuclideanSpace n) =
          (2 : ℝ) := by
      rw [hdet, ← hLeaf, hvol']
      field_simp [show (2 * (2 * inner ℝ (y : FinRealEuclideanSpace n) (v : FinRealEuclideanSpace n)) ^ m) ≠ 0
          from by positivity]
    have hKeq :
        finRealSpherePolarizationKernel n (φ v) y =
          ENNReal.ofReal
            (SphericalPolarization.GeometricKernel.sphericalKernelChordal n
              (SphericalPolarization.GeometricKernel.reflection
                (v : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n))
              (y : FinRealEuclideanSpace n)) := by
      rw [hK]
      dsimp [SphericalPolarization.GeometricKernel.sphericalKernelChordalENNReal]
    have hposDet :
        0 ≤ |(finRealSphereReflectionHomogeneousMapFDeriv n y φ u hz0).det| :=
      abs_nonneg _
    have hposK :
        0 ≤ SphericalPolarization.GeometricKernel.sphericalKernelChordal n
            (SphericalPolarization.GeometricKernel.reflection
              (v : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n))
            (y : FinRealEuclideanSpace n) := by
      have hne :
          SphericalPolarization.GeometricKernel.reflection
              (v : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n) ≠
            (y : FinRealEuclideanSpace n) :=
        SphericalPolarization.GeometricKernel.reflection_ne_self_of_unit_pos hy hv hpos
      rw [SphericalPolarization.GeometricKernel.sphericalKernelChordal_of_ne n hne]
      apply mul_nonneg (by positivity)
      exact inv_nonneg.mpr (pow_nonneg (finRealSphere_chordalHalf_pos_of_ne hne).le (n - 2))
    have hposMul :
        0 ≤ |(finRealSphereReflectionHomogeneousMapFDeriv n y φ u hz0).det| *
          SphericalPolarization.GeometricKernel.sphericalKernelChordal n
            (SphericalPolarization.GeometricKernel.reflection
              (v : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n))
            (y : FinRealEuclideanSpace n) :=
      mul_nonneg hposDet hposK
    rw [hKeq, ← ENNReal.ofReal_mul hposDet, hreal]
    norm_num

private lemma finRealSphereReflectionHomogeneousMap_openCone_sourceIntegrand_eq
    (n : ℕ) (hn2 : 2 ≤ n) (p y u : FinRealSphere n)
    {z : FinRealEuclideanSpace n}
    (hz : z ∈ finRealSphereRadialOpenCone n (fibreConeData n p y).1)
    (F : FinRealSphere n → ℝ≥0∞) :
    (2 : ℝ≥0∞) *
        F ((fibreConeData n p y).2.2 (finRealSphereRadialDirectionFrom (n := n) u z)) =
      ENNReal.ofReal
          |(finRealSphereReflectionHomogeneousMapFDeriv n y (fibreConeData n p y).2.2 u
              (finRealSphereRadialOpenCone_ne_zero hz)).det| *
        (F (finRealSphereRadialDirectionFrom (n := n) u
              (finRealSphereReflectionHomogeneousMap n y (fibreConeData n p y).2.2 u z)) *
          finRealSpherePolarizationKernel n
            (finRealSphereRadialDirectionFrom (n := n) u
              (finRealSphereReflectionHomogeneousMap n y (fibreConeData n p y).2.2 u z)) y) := by
  let φ := (fibreConeData n p y).2.2
  have hz0 := finRealSphereRadialOpenCone_ne_zero hz
  have hdir :=
    finRealSphereReflectionHomogeneousMap_radialDirectionFrom_eq (y := y) (φ := φ) (u := u) hz
  have hdet :=
    finRealSphereReflectionHomogeneousMap_abs_det_mul_kernel_eq_two n hn2 p y u hz
  rw [hdir]
  calc
    (2 : ℝ≥0∞) * F (φ (finRealSphereRadialDirectionFrom (n := n) u z)) =
        F (φ (finRealSphereRadialDirectionFrom (n := n) u z)) * (2 : ℝ≥0∞) := by ring
    _ = F (φ (finRealSphereRadialDirectionFrom (n := n) u z)) *
          (ENNReal.ofReal
              |(finRealSphereReflectionHomogeneousMapFDeriv n y φ u hz0).det| *
            finRealSpherePolarizationKernel n
              (φ (finRealSphereRadialDirectionFrom (n := n) u z)) y) :=
        (congrArg (fun t =>
          F (φ (finRealSphereRadialDirectionFrom (n := n) u z)) * t) hdet).symm
    _ = ENNReal.ofReal
            |(finRealSphereReflectionHomogeneousMapFDeriv n y φ u hz0).det| *
          (F (φ (finRealSphereRadialDirectionFrom (n := n) u z)) *
            finRealSpherePolarizationKernel n
              (φ (finRealSphereRadialDirectionFrom (n := n) u z)) y) := by ring

theorem finRealSphereReflectionMap_openCone_lintegral_eq_of_homogeneousMap
    (n : ℕ) (hn2 : 2 ≤ n) (p y u : FinRealSphere n)
    (F : FinRealSphere n → ℝ≥0∞) (_hF : Measurable F) :
    (finRealHaarMeasure n (Metric.ball (0 : FinRealEuclideanSpace n) 1))⁻¹ *
      ∫⁻ z in finRealSphereRadialOpenCone n (fibreConeData n p y).1,
        (2 : ℝ≥0∞) *
          F ((fibreConeData n p y).2.2
            (finRealSphereRadialDirectionFrom (n := n) u z))
        ∂(finRealHaarMeasure n)
      =
    (finRealHaarMeasure n (Metric.ball (0 : FinRealEuclideanSpace n) 1))⁻¹ *
      ∫⁻ w in finRealSphereRadialOpenCone n (fibreConeData n p y).2.1,
        F (finRealSphereRadialDirectionFrom (n := n) u w) *
          finRealSpherePolarizationKernel n
            (finRealSphereRadialDirectionFrom (n := n) u w) y
        ∂(finRealHaarMeasure n) := by
  classical
  haveI : NeZero n := neZero_of_two_le hn2
  haveI : (finRealHaarMeasure n).IsAddHaarMeasure := by
    unfold finRealHaarMeasure; infer_instance
  let φ := (fibreConeData n p y).2.2
  let Ψ := finRealSphereReflectionHomogeneousMap n y φ u
  let source := finRealSphereRadialOpenCone n (fibreConeData n p y).1
  let target := finRealSphereRadialOpenCone n (fibreConeData n p y).2.1
  have hsource_meas :
      MeasurableSet source :=
    finRealSphereRadialOpenCone_measurableSet u (fibreConeData_domain_meas n p y)
  have htarget_meas :
      MeasurableSet target :=
    finRealSphereRadialOpenCone_measurableSet u (fibreConeData_target_meas n p y)
  have hinj := homogeneousMap_injOn_sourceCone n p y u
  have himage := homogeneousMap_image_sourceCone n p y u
  let f' (x : FinRealEuclideanSpace n) : FinRealEuclideanSpace n →L[ℝ] FinRealEuclideanSpace n :=
    if h : x ∈ source then
      finRealSphereReflectionHomogeneousMapFDeriv n y φ u
        (finRealSphereRadialOpenCone_ne_zero h)
    else 0
  have hCOV :=
    mathlib_lintegral_image_eq_lintegral_abs_det_fderiv_mul
      (μ := finRealHaarMeasure n)
      (f := Ψ)
      (f' := f')
      hsource_meas
      (fun x hx => by
        dsimp [source, f']
        rw [dif_pos hx]
        exact hasFDerivWithinAt_finRealSphereReflectionHomogeneousMap_fibre_openCone n p y u hx)
      hinj
      (fun w : FinRealEuclideanSpace n =>
        F (finRealSphereRadialDirectionFrom (n := n) u w) *
          finRealSpherePolarizationKernel n
            (finRealSphereRadialDirectionFrom (n := n) u w) y)
  rw [himage] at hCOV
  have hball :
      (finRealHaarMeasure n (Metric.ball (0 : FinRealEuclideanSpace n) 1)) ≠ 0 := by
    haveI : (finRealHaarMeasure n).IsOpenPosMeasure := by
      unfold finRealHaarMeasure; infer_instance
    exact (Metric.isOpen_ball).measure_ne_zero _ ⟨0, by simp⟩
  have hball_top :
      (finRealHaarMeasure n (Metric.ball (0 : FinRealEuclideanSpace n) 1)) ≠ ∞ := by
    have hball_lt_top :
        (finRealHaarMeasure n (Metric.ball (0 : FinRealEuclideanSpace n) 1)) < ∞ :=
      lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
        ((isCompact_closedBall (0 : FinRealEuclideanSpace n) 1).measure_lt_top)
    exact hball_lt_top.ne
  let detMulKernel (z : FinRealEuclideanSpace n) : ℝ≥0∞ :=
    ENNReal.ofReal |(f' z).det| *
      (F (finRealSphereRadialDirectionFrom (n := n) u (Ψ z)) *
        finRealSpherePolarizationKernel n
          (finRealSphereRadialDirectionFrom (n := n) u (Ψ z)) y)
  have hstep1 :
      ∫⁻ z in source,
          (2 : ℝ≥0∞) * F (φ (finRealSphereRadialDirectionFrom (n := n) u z))
        ∂(finRealHaarMeasure n) =
        ∫⁻ z in source, detMulKernel z ∂(finRealHaarMeasure n) := by
    refine setLIntegral_congr_fun hsource_meas fun z hz => ?_
    dsimp [detMulKernel, f']
    rw [dif_pos hz]
    exact finRealSphereReflectionHomogeneousMap_openCone_sourceIntegrand_eq n hn2 p y u hz F
  let g := fun w : FinRealEuclideanSpace n =>
    F (finRealSphereRadialDirectionFrom (n := n) u w) *
      finRealSpherePolarizationKernel n
        (finRealSphereRadialDirectionFrom (n := n) u w) y
  have hstep2 :
      ∫⁻ z in source, detMulKernel z ∂(finRealHaarMeasure n) =
        ∫⁻ w in target, g w ∂(finRealHaarMeasure n) :=
    hCOV.symm
  calc
    (finRealHaarMeasure n (Metric.ball (0 : FinRealEuclideanSpace n) 1))⁻¹ *
        ∫⁻ z in source,
          (2 : ℝ≥0∞) *
            F (φ (finRealSphereRadialDirectionFrom (n := n) u z))
          ∂(finRealHaarMeasure n)
      =
    (finRealHaarMeasure n (Metric.ball (0 : FinRealEuclideanSpace n) 1))⁻¹ *
        ∫⁻ z in source, detMulKernel z ∂(finRealHaarMeasure n) := by
      rw [hstep1]
    _ =
    (finRealHaarMeasure n (Metric.ball (0 : FinRealEuclideanSpace n) 1))⁻¹ *
        ∫⁻ w in target,
          F (finRealSphereRadialDirectionFrom (n := n) u w) *
            finRealSpherePolarizationKernel n
              (finRealSphereRadialDirectionFrom (n := n) u w) y
          ∂(finRealHaarMeasure n) := by
      rw [hstep2]

/-- Ambient open-cone change of variables for one fibre: after the cone bridge,
the source-side factor `2` matches the target-side kernel density under the
homogeneous extension of the polarization parametrization. -/
theorem finRealSphereReflectionMap_openCone_lintegral_eq
    (n : ℕ) (hn2 : 2 ≤ n) (p y u : FinRealSphere n)
    (F : FinRealSphere n → ℝ≥0∞) (hF : Measurable F) :
    (finRealHaarMeasure n (Metric.ball (0 : FinRealEuclideanSpace n) 1))⁻¹ *
      ∫⁻ z in finRealSphereRadialOpenCone n (fibreConeData n p y).1,
        (2 : ℝ≥0∞) *
          F ((fibreConeData n p y).2.2
            (finRealSphereRadialDirectionFrom (n := n) u z))
        ∂(finRealHaarMeasure n)
      =
    (finRealHaarMeasure n (Metric.ball (0 : FinRealEuclideanSpace n) 1))⁻¹ *
      ∫⁻ w in finRealSphereRadialOpenCone n (fibreConeData n p y).2.1,
        F (finRealSphereRadialDirectionFrom (n := n) u w) *
          finRealSpherePolarizationKernel n
            (finRealSphereRadialDirectionFrom (n := n) u w) y
        ∂(finRealHaarMeasure n) := by
  exact finRealSphereReflectionMap_openCone_lintegral_eq_of_homogeneousMap n hn2 p y u F hF

/-!
### Leaf 3 — fibrewise nonnegative-integral change of variables

Main analytic leaf.  Intended to consume leaves 1–2 and
`FibrePackaging.closed_geometric_packaging`.
-/

theorem finRealSphereReflectionMap_pushforward_lintegral_formula
    (n : ℕ) (hn2 : 2 ≤ n) :
    FinRealSpherePolarizationPushforwardLIntegralFormula
      (finRealSphereReflectionMap n) := by
  intro p y F hF
  haveI : NeZero n := neZero_of_two_le hn2
  have hdomain :
      MeasurableSet (fibreConeData n p y).1 :=
    fibreConeData_domain_meas n p y
  have hφ : Measurable (fibreConeData n p y).2.2 :=
    fibreConeData_φ_meas n p y
  have hparam :
      (fibreConeData n p y).2.2 =
        finRealSpherePolarizationParam (finRealSphereReflectionMap n) y := by
    rfl
  have hLHS :=
    lintegral_finRealSurfaceProbabilityMeasure_eq_cone (u := y) hdomain
      (fun v => (2 : ℝ≥0∞) * F (finRealSpherePolarizationParam (finRealSphereReflectionMap n) y v))
      (measurable_const.mul (hF.comp hφ))
  have hRHS₁ := lintegral_kernel_heightSublevel_eq_indicator (n := n) p y F hF
  have hRHS₂ :=
    lintegral_kernel_heightSublevel_eq_punctured hn2 p y F hF
  have hRHS₃ :=
    lintegral_finRealSurfaceProbabilityMeasure_eq_cone (u := y)
      (fibreConeData_target_meas n p y)
      (fun x => F x * finRealSpherePolarizationKernel n x y)
      (hF.mul (measurable_finRealSpherePolarizationKernel_right n y))
  have hopenCone :=
    finRealSphereReflectionMap_openCone_lintegral_eq n hn2 p y y F hF
  calc
    (∫⁻ v in finRealSphereAdmissibleHemisphere n p ∩
          finRealSphereDirectionHemisphere n y,
        (2 : ℝ≥0∞) *
          F (finRealSpherePolarizationParam (finRealSphereReflectionMap n) y v)
      ∂(finRealSurfaceProbabilityMeasure n))
        =
      (finRealHaarMeasure n (Metric.ball (0 : FinRealEuclideanSpace n) 1))⁻¹ *
        ∫⁻ z in finRealSphereRadialOpenCone n (fibreConeData n p y).1,
          (2 : ℝ≥0∞) *
            F ((fibreConeData n p y).2.2
              (finRealSphereRadialDirectionFrom (n := n) y z))
          ∂(finRealHaarMeasure n) := by
        rw [fibreConeData_domain_eq n p y, hparam]
        exact hLHS
    _ =
      (finRealHaarMeasure n (Metric.ball (0 : FinRealEuclideanSpace n) 1))⁻¹ *
        ∫⁻ w in finRealSphereRadialOpenCone n (fibreConeData n p y).2.1,
          F (finRealSphereRadialDirectionFrom (n := n) y w) *
            finRealSpherePolarizationKernel n
              (finRealSphereRadialDirectionFrom (n := n) y w) y
          ∂(finRealHaarMeasure n) := hopenCone
    _ =
      (∫⁻ x in (fibreConeData n p y).2.1,
          F x * finRealSpherePolarizationKernel n x y
        ∂(finRealSurfaceProbabilityMeasure n)) := by
        simpa using hRHS₃.symm
    _ =
      (∫⁻ x in {x : FinRealSphere n |
            finRealSphereHeight n p x ≤ finRealSphereHeight n p y},
          F x * finRealSpherePolarizationKernel n x y
        ∂(finRealSurfaceProbabilityMeasure n)) := by
        exact hRHS₂.symm
    _ =
      (∫⁻ x : FinRealSphere n,
          F x *
            (if finRealSphereHeight n p x ≤ finRealSphereHeight n p y then
              finRealSpherePolarizationKernel n x y
            else
              0)
        ∂(finRealSurfaceProbabilityMeasure n)) := hRHS₁.symm

/-!
### Closure — measure-level `withDensity` from the lintegral leaf
-/

theorem finRealSphereReflectionMap_pushforward_withDensity
    {n : ℕ} (hn2 : 2 ≤ n) (p y : FinRealSphere n) :
    (2 : ℝ≥0∞) •
      (Measure.map
        (finRealSpherePolarizationParam (finRealSphereReflectionMap n) y)
        (finRealSphereReflectionMap_pushforward_sourceMeasure n p y))
    =
    (finRealSurfaceProbabilityMeasure n).withDensity
      (finRealSphereReflectionMap_pushforward_density n p y) := by
  have hL :
      FinRealSpherePolarizationPushforwardLIntegralFormula
        (finRealSphereReflectionMap n) :=
    finRealSphereReflectionMap_pushforward_lintegral_formula n hn2
  have hK :
      FinRealSpherePolarizationPushforwardKernelFormula
        (finRealSphereReflectionMap n) :=
    finRealSphereReflectionMap_pushforward_withDensity_of_lintegral n hL
  simpa [finRealSphereReflectionMap_pushforward_density,
    finRealSphereReflectionMap_pushforward_sourceMeasure] using hK p y

theorem finRealSphereReflectionMap_pushforwardKernelFormula
    (n : ℕ) (hn2 : 2 ≤ n) :
    FinRealSpherePolarizationPushforwardKernelFormula
      (finRealSphereReflectionMap n) := by
  intro p y
  exact finRealSphereReflectionMap_pushforward_withDensity hn2 p y

/-- Full target closure for the canonical reflection map. -/
theorem finRealSphereReflectionMap_isJacobianTarget (n : ℕ) (hn2 : 2 ≤ n) :
    FinRealSpherePolarizationJacobianTarget (finRealSphereReflectionMap n) :=
    finRealSphereReflectionMap_jacobianTarget_of_pushforward n hn2
    (finRealSphereReflectionMap_pushforwardKernelFormula n hn2)

end AppendixB
end PptFactorization

end
