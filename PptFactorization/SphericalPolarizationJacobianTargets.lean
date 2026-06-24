import PptFactorization.AppendixBSurfaceMeasure
import PptFactorization.SphericalPolarizationGeometricKernel
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.MeasureTheory.Measure.Haar.Disintegration

/-!
# Concrete spherical-polarization Jacobian targets

This file pins the polarization Jacobian theorem package for the project's
canonical real sphere `FinRealSphere n` and its normalized surface probability
measure `finRealSurfaceProbabilityMeasure n`.

The main target is the measure-level push-forward formula with the explicit
chordal kernel

`2^{-(n-2)} * (‖x-y‖/2)^{-(n-2)}`.

We deliberately do not include a weak tangent-Jacobian field of the form
"there exists some linear map with this determinant": that would not say the
determinant belongs to the actual derivative of `v ↦ rho_v(y)`.  The
downstream proof only needs the push-forward density, while the derivative and
inverse statements below document the intended proof route.

The concrete reflection-map transport proof is closed in
`PptFactorization/SphericalPolarizationPushforwardTransport.lean`; this file
keeps the interface and the reusable target definitions.
-/

noncomputable section

open scoped ENNReal Pointwise
open MeasureTheory Set
open InnerProductSpace

namespace PptFactorization
namespace AppendixB

/-- Height function relative to a pole `p` on the canonical real sphere. -/
def finRealSphereHeight (n : ℕ) (p x : FinRealSphere n) : ℝ :=
  ⟪(x : FinRealEuclideanSpace n), (p : FinRealEuclideanSpace n)⟫_ℝ

/-- The open hemisphere of directions `v` satisfying `0 < ⟪y,v⟫`. -/
def finRealSphereDirectionHemisphere
    (n : ℕ) (y : FinRealSphere n) : Set (FinRealSphere n) :=
  {v | 0 < ⟪(y : FinRealEuclideanSpace n),
    (v : FinRealEuclideanSpace n)⟫_ℝ}

/-- The admissible closed hemisphere of directions oriented toward pole `p`. -/
def finRealSphereAdmissibleHemisphere
    (n : ℕ) (p : FinRealSphere n) : Set (FinRealSphere n) :=
  {v | 0 ≤ ⟪(p : FinRealEuclideanSpace n),
    (v : FinRealEuclideanSpace n)⟫_ℝ}

/-- Chordal half-distance.  On the unit sphere this equals
`sin(d_geo(x,y)/2)`. -/
def finRealSphereChordalHalf (n : ℕ) (x y : FinRealSphere n) : ℝ :=
  dist x y / 2

/-- The project-specific chordal half-distance agrees with the generic
ambient/Frobenius half-distance used in the geometric kernel file. -/
theorem finRealSphereChordalHalf_eq_chordalHalf
    (n : ℕ) (x y : FinRealSphere n) :
    finRealSphereChordalHalf n x y =
      SphericalPolarization.GeometricKernel.chordalHalf
        (x : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n) := by
  rw [finRealSphereChordalHalf,
    SphericalPolarization.GeometricKernel.chordalHalf]
  rw [Subtype.dist_eq, dist_eq_norm]

/-- The explicit kernel for the normalized admissible-direction push-forward.
It is extended by zero on the diagonal. -/
def finRealSpherePolarizationKernel
    (n : ℕ) (x y : FinRealSphere n) : ℝ≥0∞ :=
  SphericalPolarization.GeometricKernel.sphericalKernelChordalENNReal n
    (x : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n)

/-- Off the diagonal, the concrete kernel is exactly
`2^{-(n-2)} * (dist x y / 2)^{-(n-2)}` in `ENNReal.ofReal` form. -/
theorem finRealSpherePolarizationKernel_of_ne
    (n : ℕ) {x y : FinRealSphere n}
    (hxy : x ≠ y) :
    finRealSpherePolarizationKernel n x y =
      ENNReal.ofReal
        ((((2 : ℝ) ^ (n - 2))⁻¹) *
          (((finRealSphereChordalHalf n x y) ^ (n - 2))⁻¹)) := by
  have hval : (x : FinRealEuclideanSpace n) ≠
      (y : FinRealEuclideanSpace n) := by
    intro h
    exact hxy (Subtype.ext h)
  unfold finRealSpherePolarizationKernel
  unfold SphericalPolarization.GeometricKernel.sphericalKernelChordalENNReal
  rw [SphericalPolarization.GeometricKernel.sphericalKernelChordal_of_ne
    (n := n) hval]
  rw [← finRealSphereChordalHalf_eq_chordalHalf n x y]

/-- Points of `FinRealSphere n` have ambient norm one. -/
theorem finRealSphere_norm_coe
    (n : ℕ) (x : FinRealSphere n) :
    ‖(x : FinRealEuclideanSpace n)‖ = 1 := by
  have hx : dist (x : FinRealEuclideanSpace n) 0 = 1 := x.property
  rw [dist_eq_norm, sub_zero] at hx
  exact hx

/-- Ambient dimension of the canonical finite-dimensional model. -/
theorem finRealSphere_moduleFinrank (n : ℕ) :
    Module.finrank ℝ (FinRealEuclideanSpace n) = n := by
  simp only [FinRealEuclideanSpace, finrank_euclideanSpace_fin]

/-- Sphere points are nonzero in ambient coordinates. -/
theorem finRealSphere_ne_zero (n : ℕ) (x : FinRealSphere n) :
    (x : FinRealEuclideanSpace n) ≠ 0 := by
  intro hx
  have h := finRealSphere_norm_coe n x
  rw [hx, norm_zero] at h
  norm_num at h

/-- Tangent hyperplane dimension at a nonzero ambient point. -/
theorem finRealSphere_tangentSubspace_finrank
    (n : ℕ) (x : FinRealEuclideanSpace n) (hx : x ≠ 0) :
    Module.finrank ℝ
        (SphericalPolarization.GeometricKernel.tangentSubspace x) = n - 1 := by
  classical
  let E := FinRealEuclideanSpace n
  let K : Submodule ℝ E := ℝ ∙ x
  have hK : Module.finrank ℝ K = 1 := finrank_span_singleton hx
  have hE : Module.finrank ℝ E = n := finRealSphere_moduleFinrank n
  have hor :
      SphericalPolarization.GeometricKernel.tangentSubspace x = Kᗮ := by
    ext w
    simp only [SphericalPolarization.GeometricKernel.mem_tangentSubspace_iff,
      Submodule.mem_orthogonal]
    constructor
    · intro hw y hy
      rcases Submodule.mem_span_singleton.mp hy with ⟨c, rfl⟩
      rw [inner_smul_left, hw, mul_zero]
    · intro hw
      exact hw x (Submodule.subset_span (Set.mem_singleton x))
  rw [hor]
  have hsum := K.finrank_add_finrank_orthogonal
  have hb : Module.finrank ℝ Kᗮ = n - 1 := by
    rw [hK, hE] at hsum
    exact Nat.eq_sub_of_add_eq' hsum
  exact hb

/-- Tangent-space dimension at the reflected target point `rho_v(y)`. -/
theorem finRealSphere_reflection_tangentSubspace_finrank
    (n : ℕ) (hn2 : 2 ≤ n) (y v : FinRealSphere n)
    (_hv : v ∈ finRealSphereDirectionHemisphere n y) :
    Module.finrank ℝ
        (SphericalPolarization.GeometricKernel.tangentSubspace
          (SphericalPolarization.GeometricKernel.reflection
            (v : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n))) =
      n - 2 + 1 := by
  have hb :=
    finRealSphere_tangentSubspace_finrank n
      (SphericalPolarization.GeometricKernel.reflection
        (v : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n)) ?_
  · convert hb using 1
    omega
  · intro hzero
    have hnorm :=
      SphericalPolarization.GeometricKernel.reflection_norm_eq_of_unit
        (v := (v : FinRealEuclideanSpace n))
        (y := (y : FinRealEuclideanSpace n))
        (finRealSphere_norm_coe n v)
    rw [hzero, norm_zero] at hnorm
    rw [finRealSphere_norm_coe n y] at hnorm
    norm_num at hnorm

/-- Any nontrivial linear height hyperplane cuts out a null set for the
probability-normalized real-sphere surface measure. -/
theorem finRealSurfaceProbabilityMeasure_inner_eq_zero
    (n : ℕ) (a : FinRealEuclideanSpace n) (ha : a ≠ 0) :
    (finRealSurfaceProbabilityMeasure n)
      {v : FinRealSphere n |
        ⟪a, (v : FinRealEuclideanSpace n)⟫_ℝ = 0} = 0 := by
  rw [finRealSurfaceProbabilityMeasure]
  rw [MeasureTheory.toFinite_apply_eq_zero_iff]
  let s : Set (FinRealSphere n) :=
    {v : FinRealSphere n |
      ⟪a, (v : FinRealEuclideanSpace n)⟫_ℝ = 0}
  have hs : MeasurableSet s := by
    have hcont : Continuous
        (fun v : FinRealSphere n =>
          ⟪a, (v : FinRealEuclideanSpace n)⟫_ℝ) := by
      fun_prop
    exact (isClosed_eq hcont continuous_const).measurableSet
  change finRealSurfaceMeasure n s = 0
  unfold finRealSurfaceMeasure finRealHaarMeasure
  rw [Measure.toSphere_apply' _ hs]
  have hcone_zero :
      ((Module.finBasis ℝ (FinRealEuclideanSpace n)).addHaar :
          Measure (FinRealEuclideanSpace n))
        (Set.Ioo (0 : ℝ) 1 •
          ((Subtype.val : FinRealSphere n → FinRealEuclideanSpace n) '' s)) = 0 := by
    let μ : Measure (FinRealEuclideanSpace n) :=
      (Module.finBasis ℝ (FinRealEuclideanSpace n)).addHaar
    let ℓ : FinRealEuclideanSpace n →ₗ[ℝ] ℝ :=
      (innerSL ℝ (E := FinRealEuclideanSpace n) a).toLinearMap
    let A : AffineSubspace ℝ (FinRealEuclideanSpace n) :=
      (LinearMap.ker ℓ).toAffineSubspace
    have hsubset :
        Set.Ioo (0 : ℝ) 1 •
            ((Subtype.val : FinRealSphere n → FinRealEuclideanSpace n) '' s) ⊆
          (A : Set (FinRealEuclideanSpace n)) := by
      intro z hz
      rcases hz with ⟨r, _hr, _u, ⟨v, hv, rfl⟩, rfl⟩
      change r • (v : FinRealEuclideanSpace n) ∈ A
      rw [Submodule.mem_toAffineSubspace]
      have hv0 : ⟪a, (v : FinRealEuclideanSpace n)⟫_ℝ = 0 := by
        simpa [s] using hv
      change ℓ (r • (v : FinRealEuclideanSpace n)) = 0
      simp [ℓ, hv0]
    have hA_ne_top : A ≠ ⊤ := by
      intro htop
      have hay : a ∈ (A : Set (FinRealEuclideanSpace n)) := by
        rw [htop]
        trivial
      have hay' : a ∈ LinearMap.ker ℓ := by
        simpa [A] using hay
      change ℓ a = 0 at hay'
      have hinner : ⟪a, a⟫_ℝ = 0 := by
        simpa [ℓ] using hay'
      have hnorm : ‖a‖ = 0 := by
        rw [← sq_eq_zero_iff]
        rw [← real_inner_self_eq_norm_sq]
        exact hinner
      exact ha (norm_eq_zero.mp hnorm)
    exact measure_mono_null hsubset
      (Measure.addHaar_affineSubspace μ A hA_ne_top)
  rw [hcone_zero, mul_zero]

/-- The boundary of the open direction hemisphere has zero surface
probability. -/
theorem finRealSphere_direction_boundary_null
    (n : ℕ) (y : FinRealSphere n) :
    (finRealSurfaceProbabilityMeasure n)
      {v : FinRealSphere n |
        ⟪(y : FinRealEuclideanSpace n),
          (v : FinRealEuclideanSpace n)⟫_ℝ = 0} = 0 := by
  exact finRealSurfaceProbabilityMeasure_inner_eq_zero n
    (y : FinRealEuclideanSpace n)
    (by
      intro hy
      have hynorm : ‖(y : FinRealEuclideanSpace n)‖ = 0 := by simp [hy]
      rw [finRealSphere_norm_coe n y] at hynorm
      norm_num at hynorm)

/-- The boundary of the admissible closed hemisphere has zero surface
probability. -/
theorem finRealSphere_admissible_boundary_null
    (n : ℕ) (p : FinRealSphere n) :
    (finRealSurfaceProbabilityMeasure n)
      {v : FinRealSphere n |
        ⟪(p : FinRealEuclideanSpace n),
          (v : FinRealEuclideanSpace n)⟫_ℝ = 0} = 0 := by
  exact finRealSphere_direction_boundary_null n p

/-- A singleton on the real sphere has zero surface probability in real
dimension at least two. -/
theorem finRealSurfaceProbabilityMeasure_singleton
    (n : ℕ) (hn : 2 ≤ n) (x : FinRealSphere n) :
    (finRealSurfaceProbabilityMeasure n) {x} = 0 := by
  rw [finRealSurfaceProbabilityMeasure]
  rw [MeasureTheory.toFinite_apply_eq_zero_iff]
  unfold finRealSurfaceMeasure finRealHaarMeasure
  rw [Measure.toSphere_apply' _ (measurableSet_singleton x)]
  have hcone_zero :
      ((Module.finBasis ℝ (FinRealEuclideanSpace n)).addHaar :
          Measure (FinRealEuclideanSpace n))
        (Set.Ioo (0 : ℝ) 1 •
          ((Subtype.val : FinRealSphere n → FinRealEuclideanSpace n) ''
            ({x} : Set (FinRealSphere n)))) = 0 := by
    let μ : Measure (FinRealEuclideanSpace n) :=
      (Module.finBasis ℝ (FinRealEuclideanSpace n)).addHaar
    let A : AffineSubspace ℝ (FinRealEuclideanSpace n) :=
      (ℝ ∙ (x : FinRealEuclideanSpace n)).toAffineSubspace
    have hsubset :
        Set.Ioo (0 : ℝ) 1 •
            ((Subtype.val : FinRealSphere n → FinRealEuclideanSpace n) ''
              ({x} : Set (FinRealSphere n))) ⊆
          (A : Set (FinRealEuclideanSpace n)) := by
      intro z hz
      rcases hz with ⟨r, _hr, _u, ⟨v, hv, rfl⟩, rfl⟩
      have hvx : v = x := by
        simpa using hv
      rw [hvx]
      change r • (x : FinRealEuclideanSpace n) ∈ A
      rw [Submodule.mem_toAffineSubspace]
      exact Submodule.smul_mem _ r (Submodule.mem_span_singleton_self _)
    have hxne : (x : FinRealEuclideanSpace n) ≠ 0 := by
      intro hx0
      have hxnorm : ‖(x : FinRealEuclideanSpace n)‖ = 0 := by
        simp [hx0]
      rw [finRealSphere_norm_coe n x] at hxnorm
      norm_num at hxnorm
    have hA_ne_top : A ≠ ⊤ := by
      intro htop
      have hdir :
          (ℝ ∙ (x : FinRealEuclideanSpace n)) =
            (⊤ : Submodule ℝ (FinRealEuclideanSpace n)) := by
        have h := congrArg
          (fun B : AffineSubspace ℝ (FinRealEuclideanSpace n) => B.direction)
          htop
        simpa [A, Submodule.toAffineSubspace_direction,
          AffineSubspace.direction_top] using h
      have hfin := congrArg
        (fun S : Submodule ℝ (FinRealEuclideanSpace n) =>
          Module.finrank ℝ S) hdir
      have hfin' :
          Module.finrank ℝ
              (↥(ℝ ∙ (x : FinRealEuclideanSpace n))) =
            Module.finrank ℝ
              (↥(⊤ : Submodule ℝ (FinRealEuclideanSpace n))) := by
        simpa using hfin
      have hspan :
          Module.finrank ℝ
              (↥(ℝ ∙ (x : FinRealEuclideanSpace n))) = 1 :=
        finrank_span_singleton hxne
      have htopfin :
          Module.finrank ℝ
              (↥(⊤ : Submodule ℝ (FinRealEuclideanSpace n))) = n := by
        rw [finrank_top, finrank_euclideanSpace_fin]
      rw [hspan, htopfin] at hfin'
      omega
    exact measure_mono_null hsubset
      (Measure.addHaar_affineSubspace μ A hA_ne_top)
  rw [hcone_zero, mul_zero]

/-- The diagonal in the product of two real spheres has zero product surface
probability in real dimension at least two. -/
theorem finRealSphere_diagonal_null
    (n : ℕ) (hn : 2 ≤ n) :
    ((finRealSurfaceProbabilityMeasure n).prod
      (finRealSurfaceProbabilityMeasure n))
        {z : FinRealSphere n × FinRealSphere n | z.1 = z.2} = 0 := by
  haveI : SFinite (finRealSurfaceProbabilityMeasure n) := by
    unfold finRealSurfaceProbabilityMeasure
    infer_instance
  let D : Set (FinRealSphere n × FinRealSphere n) := {z | z.1 = z.2}
  have hD : MeasurableSet D := by
    exact (isClosed_eq continuous_fst continuous_snd).measurableSet
  rw [show {z : FinRealSphere n × FinRealSphere n | z.1 = z.2} = D by rfl]
  rw [Measure.prod_apply hD]
  have hsection :
      ∀ x : FinRealSphere n,
        (finRealSurfaceProbabilityMeasure n) (Prod.mk x ⁻¹' D) = 0 := by
    intro x
    simpa [D, eq_comm] using
      finRealSurfaceProbabilityMeasure_singleton n hn x
  simp [hsection]

/-- The one-dimensional atomlessness input for height functions on the
canonical real sphere.  This is the precise measure-theoretic content needed
for the height tie-level null set: the distribution of `x ↦ ⟪x,p⟫` under the
surface probability law has no atoms. -/
def FinRealSphereHeightDistributionAtomless (n : ℕ) : Prop :=
  ∀ p : FinRealSphere n,
    NoAtoms
      (Measure.map (finRealSphereHeight n p)
        (finRealSurfaceProbabilityMeasure n))

/-- The remaining open-latitude null input for height functions on the
canonical real sphere.  This excludes the equator, antipodal endpoints, and
empty out-of-range levels, all of which are proved below from existing
surface-measure lemmas. -/
def FinRealSphereOpenLatitudeNull (n : ℕ) : Prop :=
  ∀ p : FinRealSphere n,
    ∀ t : ℝ,
      |t| < 1 →
        (finRealSurfaceProbabilityMeasure n)
          {x : FinRealSphere n | finRealSphereHeight n p x = t} = 0

/-- The equatorial height level is exactly the already-proved hyperplane
section, hence null. -/
theorem finRealSphere_height_level_null_zero
    (n : ℕ) (p : FinRealSphere n) :
    (finRealSurfaceProbabilityMeasure n)
      {x : FinRealSphere n | finRealSphereHeight n p x = 0} = 0 := by
  simpa [finRealSphereHeight, real_inner_comm] using
    finRealSphere_direction_boundary_null n p

/-- The top height level consists only of the pole and is null in dimension
at least two. -/
theorem finRealSphere_height_level_null_one
    (n : ℕ) (hn : 2 ≤ n) (p : FinRealSphere n) :
    (finRealSurfaceProbabilityMeasure n)
      {x : FinRealSphere n | finRealSphereHeight n p x = 1} = 0 := by
  have hsubset :
      {x : FinRealSphere n | finRealSphereHeight n p x = 1} ⊆
        ({p} : Set (FinRealSphere n)) := by
    intro x hx
    have hval : (x : FinRealEuclideanSpace n) =
        (p : FinRealEuclideanSpace n) := by
      have hxnorm := finRealSphere_norm_coe n x
      have hpnorm := finRealSphere_norm_coe n p
      have hinner :
          ⟪(x : FinRealEuclideanSpace n),
            (p : FinRealEuclideanSpace n)⟫_ℝ = 1 := by
        simpa [finRealSphereHeight] using hx
      exact (inner_eq_one_iff_of_norm_eq_one hxnorm hpnorm).mp hinner
    exact Subtype.ext hval
  exact measure_mono_null hsubset
    (finRealSurfaceProbabilityMeasure_singleton n hn p)

/-- The bottom height level consists only of the antipode of the pole and is
null in dimension at least two. -/
theorem finRealSphere_height_level_null_neg_one
    (n : ℕ) (hn : 2 ≤ n) (p : FinRealSphere n) :
    (finRealSurfaceProbabilityMeasure n)
      {x : FinRealSphere n | finRealSphereHeight n p x = -1} = 0 := by
  let negp : FinRealSphere n :=
    ⟨-(p : FinRealEuclideanSpace n), by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_neg]
      exact finRealSphere_norm_coe n p⟩
  have hsubset :
      {x : FinRealSphere n | finRealSphereHeight n p x = -1} ⊆
        ({negp} : Set (FinRealSphere n)) := by
    intro x hx
    have hval : (x : FinRealEuclideanSpace n) =
        -(p : FinRealEuclideanSpace n) := by
      have hxnorm := finRealSphere_norm_coe n x
      have hpnorm := finRealSphere_norm_coe n p
      have hinner :
          ⟪(x : FinRealEuclideanSpace n),
            (p : FinRealEuclideanSpace n)⟫_ℝ = -1 := by
        simpa [finRealSphereHeight] using hx
      exact (inner_eq_neg_one_iff_of_norm_eq_one hxnorm hpnorm).mp hinner
    exact Subtype.ext hval
  exact measure_mono_null hsubset
    (finRealSurfaceProbabilityMeasure_singleton n hn negp)

/-- Height levels outside the interval `[-1,1]` are empty by Cauchy-Schwarz. -/
theorem finRealSphere_height_level_null_of_one_lt_abs
    (n : ℕ) (p : FinRealSphere n) (t : ℝ)
    (ht : 1 < |t|) :
    (finRealSurfaceProbabilityMeasure n)
      {x : FinRealSphere n | finRealSphereHeight n p x = t} = 0 := by
  have hempty :
      {x : FinRealSphere n | finRealSphereHeight n p x = t} =
        (∅ : Set (FinRealSphere n)) := by
    ext x
    constructor
    · intro hx
      have hb :
          |finRealSphereHeight n p x| ≤ 1 := by
        have hb0 := abs_real_inner_le_norm
          (x : FinRealEuclideanSpace n) (p : FinRealEuclideanSpace n)
        simpa [finRealSphereHeight, finRealSphere_norm_coe n x,
          finRealSphere_norm_coe n p] using hb0
      have ht_le : |t| ≤ 1 := by
        rw [hx] at hb
        exact hb
      exact False.elim ((not_lt_of_ge ht_le) ht)
    · intro hx
      cases hx
  rw [hempty, measure_empty]

/-- It is enough to prove nullity for genuine open latitude levels
`|t| < 1`: equator, endpoint, and impossible levels are already closed here. -/
theorem finRealSphere_height_level_null_of_openLatitudeNull
    (n : ℕ) (hn : 2 ≤ n)
    (hOpen : FinRealSphereOpenLatitudeNull n)
    (p : FinRealSphere n) (t : ℝ) :
    (finRealSurfaceProbabilityMeasure n)
      {x : FinRealSphere n | finRealSphereHeight n p x = t} = 0 := by
  by_cases hlt : |t| < 1
  · exact hOpen p t hlt
  · have hge : (1 : ℝ) ≤ |t| := le_of_not_gt hlt
    rcases lt_or_eq_of_le hge with hgt | heq
    · exact finRealSphere_height_level_null_of_one_lt_abs n p t hgt
    · have ht_cases : t = 1 ∨ t = -1 := by
        exact (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp heq.symm
      rcases ht_cases with rfl | rfl
      · exact finRealSphere_height_level_null_one n hn p
      · exact finRealSphere_height_level_null_neg_one n hn p

/-- The open-latitude null theorem supplies atomlessness of every scalar
height distribution. -/
theorem finRealSphereHeightDistributionAtomless_of_openLatitudeNull
    (n : ℕ) (hn : 2 ≤ n)
    (hOpen : FinRealSphereOpenLatitudeNull n) :
    FinRealSphereHeightDistributionAtomless n := by
  intro p
  refine ⟨?_⟩
  intro t
  have hheight_meas : Measurable (finRealSphereHeight n p) := by
    unfold finRealSphereHeight
    fun_prop
  rw [Measure.map_apply hheight_meas (measurableSet_singleton t)]
  simpa [Set.preimage] using
    finRealSphere_height_level_null_of_openLatitudeNull n hn hOpen p t

/-- Along any line parallel to a unit vector `p`, the cone level
`⟪z,p⟫ = t‖z‖` has at most one point when `|t| < 1`.  This is the elementary
one-dimensional algebra behind the open-latitude null proof. -/
theorem height_norm_lineFiber_subsingleton
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {p y : E} (hp : ‖p‖ = 1)
    {t : ℝ} (ht : |t| < 1) :
    {a : ℝ | ⟪y + a • p, p⟫_ℝ = t * ‖y + a • p‖}.Subsingleton := by
  intro a ha b hb
  have hpinner : ⟪p, p⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hp]
    norm_num
  let u : ℝ := ⟪y, p⟫_ℝ + a
  let v : ℝ := ⟪y, p⟫_ℝ + b
  have hau : u = t * ‖y + a • p‖ := by
    dsimp [u]
    simpa [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      hp] using ha
  have hbv : v = t * ‖y + b • p‖ := by
    dsimp [v]
    simpa [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      hp] using hb
  have hsame_sign : 0 ≤ u * v := by
    rw [hau, hbv]
    have hnn :
        0 ≤ t ^ 2 * (‖y + a • p‖ * ‖y + b • p‖) :=
      mul_nonneg (sq_nonneg t)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    convert hnn using 1
    ring
  have hnorm_sq_eq (c : ℝ) :
      ‖y + c • p‖ ^ 2 =
        (⟪y, p⟫_ℝ + c) ^ 2 +
          (‖y‖ ^ 2 - ⟪y, p⟫_ℝ ^ 2) := by
    rw [norm_add_sq_real]
    simp [real_inner_smul_right, norm_smul, hp]
    ring
  have hau_sq :
      u ^ 2 = t ^ 2 * ‖y + a • p‖ ^ 2 := by
    rw [hau]
    ring
  have hbv_sq :
      v ^ 2 = t ^ 2 * ‖y + b • p‖ ^ 2 := by
    rw [hbv]
    ring
  have hquad_u :
      (1 - t ^ 2) * u ^ 2 =
        t ^ 2 * (‖y‖ ^ 2 - ⟪y, p⟫_ℝ ^ 2) := by
    have hnormu :
        ‖y + a • p‖ ^ 2 =
          u ^ 2 + (‖y‖ ^ 2 - ⟪y, p⟫_ℝ ^ 2) := by
      simpa [u] using hnorm_sq_eq a
    nlinarith
  have hquad_v :
      (1 - t ^ 2) * v ^ 2 =
        t ^ 2 * (‖y‖ ^ 2 - ⟪y, p⟫_ℝ ^ 2) := by
    have hnormv :
        ‖y + b • p‖ ^ 2 =
          v ^ 2 + (‖y‖ ^ 2 - ⟪y, p⟫_ℝ ^ 2) := by
      simpa [v] using hnorm_sq_eq b
    nlinarith
  have hcoef_ne : 1 - t ^ 2 ≠ 0 := by
    have ht_sq_lt : t ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one t).mpr ht
    nlinarith
  have huv_sq : u ^ 2 = v ^ 2 := by
    apply mul_left_cancel₀ hcoef_ne
    rw [hquad_u, hquad_v]
  have huv_abs : |u| = |v| := by
    exact (sq_eq_sq_iff_abs_eq_abs u v).mp huv_sq
  have huv_or : u = v ∨ u = -v := by
    exact abs_eq_abs.mp huv_abs
  have huv : u = v := by
    rcases huv_or with huv | huvneg
    · exact huv
    · have : u * v = -v ^ 2 := by rw [huvneg]; ring
      have hvzero : v = 0 := by
        have hv2_nonpos : v ^ 2 ≤ 0 := by nlinarith
        exact sq_eq_zero_iff.mp (le_antisymm hv2_nonpos (sq_nonneg v))
      rw [hvzero] at huvneg
      simpa [hvzero] using huvneg
  dsimp [u, v] at huv
  linarith

/-- The ambient cone `⟪z,p⟫ = t‖z‖` has Lebesgue/Haar measure zero for
`|t| < 1`.  The proof slices along lines parallel to `p` and uses the
subsingleton fibre lemma above. -/
theorem finRealHaarMeasure_height_eq_norm_smul_null
    (n : ℕ) (p : FinRealSphere n) (t : ℝ) (ht : |t| < 1) :
    (finRealHaarMeasure n)
      {z : FinRealEuclideanSpace n |
        ⟪z, (p : FinRealEuclideanSpace n)⟫_ℝ = t * ‖z‖} = 0 := by
  let E := FinRealEuclideanSpace n
  let μ : Measure E := finRealHaarMeasure n
  haveI : μ.IsAddHaarMeasure := by
    dsimp [μ, finRealHaarMeasure]
    infer_instance
  let C : Set E := {z : E | ⟪z, (p : E)⟫_ℝ = t * ‖z‖}
  let L : ℝ →ₗ[ℝ] E :=
    { toFun := fun a => a • (p : E)
      map_add' := by
        intro a b
        rw [add_smul]
      map_smul' := by
        intro a b
        simpa [smul_eq_mul] using (smul_smul a b (p : E)).symm }
  have hC_meas : MeasurableSet C := by
    have hleft : Measurable (fun z : E => ⟪z, (p : E)⟫_ℝ) := by fun_prop
    have hright : Measurable (fun z : E => t * ‖z‖) := by fun_prop
    exact measurableSet_eq_fun hleft hright
  have hae_comp : ∀ᵐ z ∂μ, z ∈ Cᶜ := by
    apply MeasureTheory.ae_mem_of_ae_add_linearMap_mem
      (L := L) (μ := (volume : Measure ℝ)) (ν := μ) hC_meas.compl
    intro y
    rw [ae_iff]
    have hsub :
        {a : ℝ | ¬ y + L a ∈ Cᶜ} ⊆
          {a : ℝ |
            ⟪y + a • (p : E), (p : E)⟫_ℝ =
              t * ‖y + a • (p : E)‖} := by
      intro a ha
      simpa [C, L] using ha
    exact measure_mono_null hsub
      ((height_norm_lineFiber_subsingleton
        (p := (p : E)) (y := y) (t := t)
        (finRealSphere_norm_coe n p) ht).measure_zero (volume : Measure ℝ))
  rw [ae_iff] at hae_comp
  simpa [μ, C] using hae_comp

/-- Concrete proof that all genuine open latitude levels on the real sphere
have zero normalized surface probability. -/
theorem finRealSphere_openLatitudeNull
    (n : ℕ) : FinRealSphereOpenLatitudeNull n := by
  intro p t ht
  rw [finRealSurfaceProbabilityMeasure]
  rw [MeasureTheory.toFinite_apply_eq_zero_iff]
  let s : Set (FinRealSphere n) :=
    {x : FinRealSphere n | finRealSphereHeight n p x = t}
  have hs : MeasurableSet s := by
    have hheight : Measurable (finRealSphereHeight n p) := by
      unfold finRealSphereHeight
      fun_prop
    exact measurableSet_eq_fun hheight measurable_const
  change finRealSurfaceMeasure n s = 0
  unfold finRealSurfaceMeasure finRealHaarMeasure
  rw [Measure.toSphere_apply' _ hs]
  have hcone_subset :
      Set.Ioo (0 : ℝ) 1 •
          ((Subtype.val : FinRealSphere n → FinRealEuclideanSpace n) '' s) ⊆
        {z : FinRealEuclideanSpace n |
          ⟪z, (p : FinRealEuclideanSpace n)⟫_ℝ = t * ‖z‖} := by
    intro z hz
    rcases hz with ⟨r, hr, _u, ⟨x, hx, rfl⟩, rfl⟩
    have hxinner :
        ⟪(x : FinRealEuclideanSpace n),
          (p : FinRealEuclideanSpace n)⟫_ℝ = t := by
      simpa [s, finRealSphereHeight] using hx
    change ⟪r • (x : FinRealEuclideanSpace n),
        (p : FinRealEuclideanSpace n)⟫_ℝ =
      t * ‖r • (x : FinRealEuclideanSpace n)‖
    rw [real_inner_smul_left, hxinner, norm_smul,
      finRealSphere_norm_coe n x, mul_one, Real.norm_eq_abs,
      abs_of_pos hr.1]
    ring
  have hcone_null :
      ((Module.finBasis ℝ (FinRealEuclideanSpace n)).addHaar :
          Measure (FinRealEuclideanSpace n))
        (Set.Ioo (0 : ℝ) 1 •
          ((Subtype.val : FinRealSphere n → FinRealEuclideanSpace n) '' s)) = 0 := by
    exact measure_mono_null hcone_subset
      (finRealHaarMeasure_height_eq_norm_smul_null n p t ht)
  rw [hcone_null, mul_zero]

/-- Concrete atomlessness of every real-sphere height distribution. -/
theorem finRealSphereHeightDistributionAtomless_concrete
    (n : ℕ) (hn : 2 ≤ n) :
    FinRealSphereHeightDistributionAtomless n :=
  finRealSphereHeightDistributionAtomless_of_openLatitudeNull n hn
    (finRealSphere_openLatitudeNull n)

/-- Atomlessness of the one-dimensional height distribution implies that
every fixed latitude has zero surface probability. -/
theorem finRealSphere_height_level_null_of_heightDistributionAtomless
    (n : ℕ)
    (hAtomless : FinRealSphereHeightDistributionAtomless n)
    (p : FinRealSphere n) (t : ℝ) :
    (finRealSurfaceProbabilityMeasure n)
      {x : FinRealSphere n | finRealSphereHeight n p x = t} = 0 := by
  haveI :
      NoAtoms
        (Measure.map (finRealSphereHeight n p)
          (finRealSurfaceProbabilityMeasure n)) :=
    hAtomless p
  have hheight_meas : Measurable (finRealSphereHeight n p) := by
    unfold finRealSphereHeight
    fun_prop
  have hsingle :
      Measure.map (finRealSphereHeight n p)
          (finRealSurfaceProbabilityMeasure n) {t} = 0 :=
    measure_singleton t
  rw [Measure.map_apply hheight_meas (measurableSet_singleton t)] at hsingle
  simpa [Set.preimage] using hsingle

/-- The product tie-level null set follows from zero mass of every
one-dimensional height latitude. -/
theorem finRealSphere_tie_level_null_of_height_level_null
    (n : ℕ)
    (hLevel :
      ∀ p : FinRealSphere n,
        ∀ t : ℝ,
          (finRealSurfaceProbabilityMeasure n)
            {x : FinRealSphere n | finRealSphereHeight n p x = t} = 0)
    (p : FinRealSphere n) :
    ((finRealSurfaceProbabilityMeasure n).prod
      (finRealSurfaceProbabilityMeasure n))
        {z : FinRealSphere n × FinRealSphere n |
          finRealSphereHeight n p z.1 =
            finRealSphereHeight n p z.2} = 0 := by
  haveI : SFinite (finRealSurfaceProbabilityMeasure n) := by
    unfold finRealSurfaceProbabilityMeasure
    infer_instance
  let T : Set (FinRealSphere n × FinRealSphere n) :=
    {z : FinRealSphere n × FinRealSphere n |
      finRealSphereHeight n p z.1 =
        finRealSphereHeight n p z.2}
  have hT : MeasurableSet T := by
    have hleft : Measurable
        (fun z : FinRealSphere n × FinRealSphere n =>
          finRealSphereHeight n p z.1) := by
      unfold finRealSphereHeight
      fun_prop
    have hright : Measurable
        (fun z : FinRealSphere n × FinRealSphere n =>
          finRealSphereHeight n p z.2) := by
      unfold finRealSphereHeight
      fun_prop
    exact measurableSet_eq_fun hleft hright
  rw [show
      {z : FinRealSphere n × FinRealSphere n |
        finRealSphereHeight n p z.1 =
          finRealSphereHeight n p z.2} = T by rfl]
  rw [Measure.prod_apply hT]
  have hsection :
      ∀ x : FinRealSphere n,
        (finRealSurfaceProbabilityMeasure n) (Prod.mk x ⁻¹' T) = 0 := by
    intro x
    have hpre :
        Prod.mk x ⁻¹' T =
          {y : FinRealSphere n |
            finRealSphereHeight n p y =
              finRealSphereHeight n p x} := by
      ext y
      simp [T, eq_comm]
    rw [hpre]
    exact hLevel p (finRealSphereHeight n p x)
  simp [hsection]

/-- The height tie-level null set follows from atomlessness of every height
distribution.  This removes the product-measure bookkeeping from the
polarization Jacobian frontier. -/
theorem finRealSphere_tie_level_null_of_heightDistributionAtomless
    (n : ℕ)
    (hAtomless : FinRealSphereHeightDistributionAtomless n)
    (p : FinRealSphere n) :
    ((finRealSurfaceProbabilityMeasure n).prod
      (finRealSurfaceProbabilityMeasure n))
        {z : FinRealSphere n × FinRealSphere n |
          finRealSphereHeight n p z.1 =
            finRealSphereHeight n p z.2} = 0 :=
  finRealSphere_tie_level_null_of_height_level_null n
    (fun q t =>
      finRealSphere_height_level_null_of_heightDistributionAtomless
        n hAtomless q t)
    p

/-- Ambient reflection is involutive when the normal vector is unit. -/
theorem reflection_involutive_of_unit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v x : E} (hv : ‖v‖ = 1) :
    SphericalPolarization.GeometricKernel.reflection v
      (SphericalPolarization.GeometricKernel.reflection v x) = x := by
  have hvv : inner ℝ v v = 1 := by
    rw [real_inner_self_eq_norm_sq, hv]
    norm_num
  have hinner :
      inner ℝ
        (SphericalPolarization.GeometricKernel.reflection v x) v =
        -inner ℝ x v := by
    calc
      inner ℝ
          (x - (2 * inner ℝ x v) • v) v =
        inner ℝ x v - (2 * inner ℝ x v) * inner ℝ v v := by
          simp [inner_sub_left, inner_smul_left]
      _ = -inner ℝ x v := by
          rw [hvv]
          ring
  calc
    SphericalPolarization.GeometricKernel.reflection v
        (SphericalPolarization.GeometricKernel.reflection v x) =
      SphericalPolarization.GeometricKernel.reflection v x -
        (2 * inner ℝ
          (SphericalPolarization.GeometricKernel.reflection v x) v) • v := rfl
    _ =
      SphericalPolarization.GeometricKernel.reflection v x -
        (2 * (-inner ℝ x v)) • v := by rw [hinner]
    _ = x := by
        unfold SphericalPolarization.GeometricKernel.reflection
        module

/-- A concrete reflection map package pinned to the ambient formula
`rho_v(x) = x - 2⟪x,v⟫v`. -/
structure FinRealSphereReflectionMap (n : ℕ) where
  map : FinRealSphere n → FinRealSphere n → FinRealSphere n
  map_coe :
    ∀ v x : FinRealSphere n,
      ((map v x : FinRealSphere n) : FinRealEuclideanSpace n) =
        (x : FinRealEuclideanSpace n) -
          (((2 : ℝ) *
            ⟪(x : FinRealEuclideanSpace n),
              (v : FinRealEuclideanSpace n)⟫_ℝ) •
            (v : FinRealEuclideanSpace n))
  map_involutive : ∀ v x : FinRealSphere n, map v (map v x) = x
  map_measurable : ∀ v : FinRealSphere n, Measurable (map v)

/-- The canonical ambient reflection as a self-map of `FinRealSphere n`. -/
def finRealSphereReflectionMap : (n : ℕ) → FinRealSphereReflectionMap n :=
  fun n =>
  { map := fun v x =>
      ⟨SphericalPolarization.GeometricKernel.reflection
          (v : FinRealEuclideanSpace n) (x : FinRealEuclideanSpace n), by
        rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
        have hv : ‖(v : FinRealEuclideanSpace n)‖ = 1 :=
          finRealSphere_norm_coe n v
        have hx : ‖(x : FinRealEuclideanSpace n)‖ = 1 :=
          finRealSphere_norm_coe n x
        simpa [hx] using
          SphericalPolarization.GeometricKernel.reflection_norm_eq_of_unit
            (v := (v : FinRealEuclideanSpace n))
            (y := (x : FinRealEuclideanSpace n)) hv⟩
    map_coe := by
      intro v x
      rfl
    map_involutive := by
      intro v x
      apply Subtype.ext
      exact reflection_involutive_of_unit
        (v := (v : FinRealEuclideanSpace n))
        (x := (x : FinRealEuclideanSpace n))
        (finRealSphere_norm_coe n v)
    map_measurable := by
      intro v
      have hcont :
          Continuous (fun x : FinRealSphere n =>
            SphericalPolarization.GeometricKernel.reflection
              (v : FinRealEuclideanSpace n) (x : FinRealEuclideanSpace n)) := by
        unfold SphericalPolarization.GeometricKernel.reflection
        fun_prop
      exact (hcont.subtype_mk (fun x => by
        rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
        have hv : ‖(v : FinRealEuclideanSpace n)‖ = 1 :=
          finRealSphere_norm_coe n v
        have hx : ‖(x : FinRealEuclideanSpace n)‖ = 1 :=
          finRealSphere_norm_coe n x
        simpa [hx] using
          SphericalPolarization.GeometricKernel.reflection_norm_eq_of_unit
            (v := (v : FinRealEuclideanSpace n))
            (y := (x : FinRealEuclideanSpace n)) hv)).measurable }

/-- Coercion formula for the canonical real-sphere reflection. -/
theorem finRealSphereReflectionMap_map_coe
    (n : ℕ) (v x : FinRealSphere n) :
    (((finRealSphereReflectionMap n).map v x : FinRealSphere n) :
        FinRealEuclideanSpace n) =
      (x : FinRealEuclideanSpace n) -
        (((2 : ℝ) *
          ⟪(x : FinRealEuclideanSpace n),
            (v : FinRealEuclideanSpace n)⟫_ℝ) •
          (v : FinRealEuclideanSpace n)) :=
  rfl

/-- The ambient linear isometry whose restriction to the sphere is the canonical
reflection through the hyperplane orthogonal to `v`. -/
noncomputable def finRealSphereReflectionLinearIsometryEquiv
    (n : ℕ) (v : FinRealSphere n) :
    FinRealEuclideanSpace n ≃ₗᵢ[ℝ] FinRealEuclideanSpace n :=
  ((ℝ ∙ (v : FinRealEuclideanSpace n))ᗮ).reflection

/-- The submodule-reflection linear isometry has the same ambient formula as
the concrete reflection map. -/
theorem finRealSphereReflectionLinearIsometryEquiv_apply
    (n : ℕ) (v : FinRealSphere n) (x : FinRealEuclideanSpace n) :
    finRealSphereReflectionLinearIsometryEquiv n v x =
      x - (((2 : ℝ) * ⟪x, (v : FinRealEuclideanSpace n)⟫_ℝ) •
        (v : FinRealEuclideanSpace n)) := by
  unfold finRealSphereReflectionLinearIsometryEquiv
  rw [Submodule.reflection_orthogonal_apply]
  rw [Submodule.reflection_singleton_apply]
  have hv : ‖(v : FinRealEuclideanSpace n)‖ = 1 :=
    finRealSphere_norm_coe n v
  rw [hv]
  simp [real_inner_comm]
  module

/-- The concrete reflection map is the sphere action of the ambient orthogonal
reflection. -/
theorem finRealSphereReflectionMap_eq_orthogonalSphereMap
    (n : ℕ) (v : FinRealSphere n) :
    (finRealSphereReflectionMap n).map v =
      finRealOrthogonalSphereMap n
        (finRealSphereReflectionLinearIsometryEquiv n v) := by
  funext x
  apply Subtype.ext
  rw [(finRealSphereReflectionMap n).map_coe]
  simp [finRealOrthogonalSphereMap,
    finRealSphereReflectionLinearIsometryEquiv_apply]

/-- The concrete reflection preserves chordal distance on the real sphere. -/
theorem finRealSphereReflectionMap_dist
    (n : ℕ) (v x y : FinRealSphere n) :
    dist ((finRealSphereReflectionMap n).map v x)
        ((finRealSphereReflectionMap n).map v y) =
      dist x y := by
  rw [finRealSphereReflectionMap_eq_orthogonalSphereMap]
  rw [Subtype.dist_eq, Subtype.dist_eq]
  change
    dist
        (finRealSphereReflectionLinearIsometryEquiv n v
          (x : FinRealEuclideanSpace n))
        (finRealSphereReflectionLinearIsometryEquiv n v
          (y : FinRealEuclideanSpace n)) =
      dist (x : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n)
  exact LinearIsometryEquiv.dist_map
    (finRealSphereReflectionLinearIsometryEquiv n v)
    (x : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n)

/-- The concrete reflection preserves the geodesic distance used in the
isoperimetric layer. -/
theorem finRealSphereReflectionMap_geodesicDistance
    (n : ℕ) (v x y : FinRealSphere n) :
    finRealSphereGeodesicDistance n
        ((finRealSphereReflectionMap n).map v x)
        ((finRealSphereReflectionMap n).map v y) =
      finRealSphereGeodesicDistance n x y := by
  unfold finRealSphereGeodesicDistance
  rw [finRealSphereReflectionMap_dist n v x y]

/-- If `x` lies in the closed positive half-sphere and `y` lies in the closed
negative half-sphere, reflecting `y` to the positive side does not increase the
ambient chord distance from `x`. -/
theorem finRealSphereReflectionMap_dist_reflection_right_le_of_nonneg_nonpos
    {n : ℕ} (v x y : FinRealSphere n)
    (hx : 0 ≤ finRealSphereInnerCoordinate n (v : FinRealEuclideanSpace n) x)
    (hy : finRealSphereInnerCoordinate n (v : FinRealEuclideanSpace n) y ≤ 0) :
    dist x ((finRealSphereReflectionMap n).map v y) ≤ dist x y := by
  have hinner :
      inner ℝ (x : FinRealEuclideanSpace n)
          (y : FinRealEuclideanSpace n) ≤
        inner ℝ (x : FinRealEuclideanSpace n)
          (((finRealSphereReflectionMap n).map v y : FinRealSphere n) :
            FinRealEuclideanSpace n) := by
    rw [finRealSphereReflectionMap_map_coe]
    simp [finRealSphereInnerCoordinate] at hx hy ⊢
    rw [inner_sub_right, inner_smul_right]
    have hx' :
        0 ≤ inner ℝ (x : FinRealEuclideanSpace n)
          (v : FinRealEuclideanSpace n) := by
      simpa [real_inner_comm] using hx
    have hy' :
        inner ℝ (y : FinRealEuclideanSpace n)
            (v : FinRealEuclideanSpace n) ≤ 0 := by
      simpa [real_inner_comm] using hy
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hx' hy']
  have hsq :
      dist x ((finRealSphereReflectionMap n).map v y) ^ 2 ≤
        dist x y ^ 2 := by
    rw [finRealSphere_dist_sq_eq_two_sub_two_inner n x
        ((finRealSphereReflectionMap n).map v y),
      finRealSphere_dist_sq_eq_two_sub_two_inner n x y]
    nlinarith
  exact (sq_le_sq₀ dist_nonneg dist_nonneg).mp hsq

/-- Geodesic-distance form of
`finRealSphereReflectionMap_dist_reflection_right_le_of_nonneg_nonpos`. -/
theorem finRealSphereReflectionMap_geodesicDistance_reflection_right_le_of_nonneg_nonpos
    {n : ℕ} (v x y : FinRealSphere n)
    (hx : 0 ≤ finRealSphereInnerCoordinate n (v : FinRealEuclideanSpace n) x)
    (hy : finRealSphereInnerCoordinate n (v : FinRealEuclideanSpace n) y ≤ 0) :
    finRealSphereGeodesicDistance n x ((finRealSphereReflectionMap n).map v y) ≤
      finRealSphereGeodesicDistance n x y := by
  unfold finRealSphereGeodesicDistance
  gcongr
  exact finRealSphereReflectionMap_dist_reflection_right_le_of_nonneg_nonpos
    v x y hx hy

/-- If two points lie in the closed positive half-sphere, reflecting the first
one to the negative side does not decrease its ambient chord distance from the
second. -/
theorem finRealSphereReflectionMap_dist_le_reflection_left_of_nonneg_nonneg
    {n : ℕ} (v x y : FinRealSphere n)
    (hx : 0 ≤ finRealSphereInnerCoordinate n (v : FinRealEuclideanSpace n) x)
    (hy : 0 ≤ finRealSphereInnerCoordinate n (v : FinRealEuclideanSpace n) y) :
    dist x y ≤ dist ((finRealSphereReflectionMap n).map v x) y := by
  have hinner :
      inner ℝ (((finRealSphereReflectionMap n).map v x : FinRealSphere n) :
          FinRealEuclideanSpace n)
          (y : FinRealEuclideanSpace n) ≤
        inner ℝ (x : FinRealEuclideanSpace n)
          (y : FinRealEuclideanSpace n) := by
    rw [finRealSphereReflectionMap_map_coe]
    simp [finRealSphereInnerCoordinate] at hx hy ⊢
    rw [inner_sub_left, real_inner_smul_left]
    have hx' :
        0 ≤ inner ℝ (x : FinRealEuclideanSpace n)
          (v : FinRealEuclideanSpace n) := by
      simpa [real_inner_comm] using hx
    have hy' :
        0 ≤ inner ℝ (v : FinRealEuclideanSpace n)
          (y : FinRealEuclideanSpace n) := by
      simpa using hy
    nlinarith [mul_nonneg hx' hy']
  have hsq :
      dist x y ^ 2 ≤ dist ((finRealSphereReflectionMap n).map v x) y ^ 2 := by
    rw [finRealSphere_dist_sq_eq_two_sub_two_inner n x y,
      finRealSphere_dist_sq_eq_two_sub_two_inner n
        ((finRealSphereReflectionMap n).map v x) y]
    nlinarith
  exact (sq_le_sq₀ dist_nonneg dist_nonneg).mp hsq

/-- Geodesic-distance form of
`finRealSphereReflectionMap_dist_le_reflection_left_of_nonneg_nonneg`. -/
theorem finRealSphereReflectionMap_geodesicDistance_le_reflection_left_of_nonneg_nonneg
    {n : ℕ} (v x y : FinRealSphere n)
    (hx : 0 ≤ finRealSphereInnerCoordinate n (v : FinRealEuclideanSpace n) x)
    (hy : 0 ≤ finRealSphereInnerCoordinate n (v : FinRealEuclideanSpace n) y) :
    finRealSphereGeodesicDistance n x y ≤
      finRealSphereGeodesicDistance n ((finRealSphereReflectionMap n).map v x) y := by
  unfold finRealSphereGeodesicDistance
  gcongr
  exact finRealSphereReflectionMap_dist_le_reflection_left_of_nonneg_nonneg
    v x y hx hy

/-- Reflection transports geodesic thickenings to the geodesic thickening of
the reflected set. -/
theorem finRealSphereReflectionMap_image_geodesicThickening
    (n : ℕ) (v : FinRealSphere n) (r : ℝ)
    (A : Set (FinRealSphere n)) :
    (finRealSphereReflectionMap n).map v ''
        finRealSphereGeodesicThickening n r A =
      finRealSphereGeodesicThickening n r
        ((finRealSphereReflectionMap n).map v '' A) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨y, hyA, hdist⟩
    refine ⟨(finRealSphereReflectionMap n).map v y, ⟨y, hyA, rfl⟩, ?_⟩
    rwa [finRealSphereReflectionMap_geodesicDistance n v x y]
  · intro hz
    rcases hz with ⟨y, hy, hdist⟩
    rcases hy with ⟨a, haA, rfl⟩
    refine ⟨(finRealSphereReflectionMap n).map v z, ?_, ?_⟩
    · refine ⟨a, haA, ?_⟩
      have hdist_eq :
          finRealSphereGeodesicDistance n
              ((finRealSphereReflectionMap n).map v z) a =
            finRealSphereGeodesicDistance n z
              ((finRealSphereReflectionMap n).map v a) := by
        simpa [(finRealSphereReflectionMap n).map_involutive] using
          finRealSphereReflectionMap_geodesicDistance n v z
            ((finRealSphereReflectionMap n).map v a)
      rwa [hdist_eq]
    · simp [(finRealSphereReflectionMap n).map_involutive]

/-- Preimage form of reflection transport for geodesic thickenings. -/
theorem finRealSphereReflectionMap_preimage_geodesicThickening_image
    (n : ℕ) (v : FinRealSphere n) (r : ℝ)
    (A : Set (FinRealSphere n)) :
    ((finRealSphereReflectionMap n).map v) ⁻¹'
        finRealSphereGeodesicThickening n r
          ((finRealSphereReflectionMap n).map v '' A) =
      finRealSphereGeodesicThickening n r A := by
  ext x
  constructor
  · intro hx
    have himg :
        (finRealSphereReflectionMap n).map v x ∈
          (finRealSphereReflectionMap n).map v ''
            finRealSphereGeodesicThickening n r A := by
      rw [finRealSphereReflectionMap_image_geodesicThickening]
      exact hx
    rcases himg with ⟨z, hz, hzx⟩
    have hxz : x = z := by
      calc
        x = (finRealSphereReflectionMap n).map v
              ((finRealSphereReflectionMap n).map v x) := by
            rw [(finRealSphereReflectionMap n).map_involutive]
        _ = (finRealSphereReflectionMap n).map v
              ((finRealSphereReflectionMap n).map v z) := by
            rw [hzx]
        _ = z := by rw [(finRealSphereReflectionMap n).map_involutive]
    simpa [hxz] using hz
  · intro hx
    have himg :
        (finRealSphereReflectionMap n).map v x ∈
          (finRealSphereReflectionMap n).map v ''
            finRealSphereGeodesicThickening n r A :=
      ⟨x, hx, rfl⟩
    rw [finRealSphereReflectionMap_image_geodesicThickening] at himg
    exact himg

/-- The normalized surface probability is invariant under the canonical
reflection. -/
theorem finRealSurfaceProbabilityMeasure_map_reflection
    (n : ℕ) [NeZero n] (v : FinRealSphere n) :
    Measure.map ((finRealSphereReflectionMap n).map v)
        (finRealSurfaceProbabilityMeasure n) =
      finRealSurfaceProbabilityMeasure n := by
  rw [finRealSphereReflectionMap_eq_orthogonalSphereMap]
  exact finRealSurfaceProbabilityMeasure_map_orthogonal n
    (finRealSphereReflectionLinearIsometryEquiv n v)

/-- Preimages under the canonical reflection have the same surface probability
as the original measurable set. -/
theorem finRealSurfaceProbabilityMeasure_reflection_preimage_real
    (n : ℕ) [NeZero n] (v : FinRealSphere n)
    {A : Set (FinRealSphere n)} (hA : MeasurableSet A) :
    (finRealSurfaceProbabilityMeasure n).real
        (((finRealSphereReflectionMap n).map v) ⁻¹' A) =
      (finRealSurfaceProbabilityMeasure n).real A := by
  rw [← map_measureReal_apply ((finRealSphereReflectionMap n).map_measurable v) hA,
    finRealSurfaceProbabilityMeasure_map_reflection n v]

/-- The geodesic-neighbourhood complement objective is invariant under
reflecting the competitor. -/
theorem finRealSurfaceProbabilityMeasure_reflection_image_neighbourhoodComplement_real
    {n : ℕ} [NeZero n] (v : FinRealSphere n) (r : ℝ)
    (A : Set (FinRealSphere n)) :
    (finRealSurfaceProbabilityMeasure n).real
        ((finRealSphereGeodesicThickening n r
          ((finRealSphereReflectionMap n).map v '' A))ᶜ) =
      (finRealSurfaceProbabilityMeasure n).real
        ((finRealSphereGeodesicThickening n r A)ᶜ) := by
  let T :=
    finRealSphereGeodesicThickening n r
      ((finRealSphereReflectionMap n).map v '' A)
  have hT : MeasurableSet T :=
    measurableSet_finRealSphereGeodesicThickening n r
      ((finRealSphereReflectionMap n).map v '' A)
  calc
    (finRealSurfaceProbabilityMeasure n).real Tᶜ =
        (finRealSurfaceProbabilityMeasure n).real
          (((finRealSphereReflectionMap n).map v) ⁻¹' Tᶜ) := by
        rw [finRealSurfaceProbabilityMeasure_reflection_preimage_real n v hT.compl]
    _ =
        (finRealSurfaceProbabilityMeasure n).real
          ((finRealSphereGeodesicThickening n r A)ᶜ) := by
        congr 1
        rw [preimage_compl,
          finRealSphereReflectionMap_preimage_geodesicThickening_image]

/-- Equivalent form using the named neighbourhood-complement objective. -/
theorem finRealSphereNeighbourhoodComplementMass_reflection_image
    {n : ℕ} [NeZero n] (v : FinRealSphere n) (r : ℝ)
    (A : Set (FinRealSphere n)) :
    finRealSphereNeighbourhoodComplementMass n
        (finRealSurfaceProbabilityMeasure n) r
        ((finRealSphereReflectionMap n).map v '' A) =
      finRealSphereNeighbourhoodComplementMass n
        (finRealSurfaceProbabilityMeasure n) r A := by
  simpa [finRealSphereNeighbourhoodComplementMass] using
    finRealSurfaceProbabilityMeasure_reflection_image_neighbourhoodComplement_real
      v r A

/-- The parametrization `T_y(v)=rho_v(y)` used in the Jacobian computation. -/
def finRealSpherePolarizationParam
    {n : ℕ} (ρ : FinRealSphereReflectionMap n) (y : FinRealSphere n) :
    FinRealSphere n → FinRealSphere n :=
  fun v => ρ.map v y

/-- The parametrization value `rho_v(y)` coerces to ambient reflection. -/
theorem finRealSpherePolarizationParam_coe_eq_reflection
    (n : ℕ) (y v : FinRealSphere n) :
    ((finRealSpherePolarizationParam (finRealSphereReflectionMap n) y v) :
        FinRealEuclideanSpace n) =
      SphericalPolarization.GeometricKernel.reflection
        (v : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n) := by
  show
    ((finRealSphereReflectionMap n).map v y : FinRealEuclideanSpace n) =
      SphericalPolarization.GeometricKernel.reflection
        (v : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n)
  rw [(finRealSphereReflectionMap n).map_coe v y]
  rfl

/-- The canonical real-sphere parametrization `v ↦ rho_v(y)` is measurable. -/
theorem finRealSphereReflectionMap_param_measurable
    (n : ℕ) :
    ∀ y : FinRealSphere n,
      Measurable
        (finRealSpherePolarizationParam (finRealSphereReflectionMap n) y) := by
  intro y
  have hcont :
      Continuous (fun v : FinRealSphere n =>
        SphericalPolarization.GeometricKernel.reflection
          (v : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n)) := by
    unfold SphericalPolarization.GeometricKernel.reflection
    fun_prop
  exact (hcont.subtype_mk (fun v => by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    have hv : ‖(v : FinRealEuclideanSpace n)‖ = 1 :=
      finRealSphere_norm_coe n v
    have hy : ‖(y : FinRealEuclideanSpace n)‖ = 1 :=
      finRealSphere_norm_coe n y
    simpa [hy] using
      SphericalPolarization.GeometricKernel.reflection_norm_eq_of_unit
        (v := (v : FinRealEuclideanSpace n))
        (y := (y : FinRealEuclideanSpace n)) hv)).measurable

/-- The canonical real-sphere parametrization is injective on the open
hemisphere `0 < ⟪y,v⟫`. -/
theorem finRealSphereReflectionMap_param_injOn
    (n : ℕ) :
    ∀ y : FinRealSphere n,
      InjOn
        (finRealSpherePolarizationParam (finRealSphereReflectionMap n) y)
        (finRealSphereDirectionHemisphere n y) := by
  intro y v₁ hv₁ v₂ hv₂ hmap
  apply Subtype.ext
  have hmapAmbient :
      SphericalPolarization.GeometricKernel.reflection
          (v₁ : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n) =
        SphericalPolarization.GeometricKernel.reflection
          (v₂ : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n) := by
    exact congrArg Subtype.val hmap
  exact
    SphericalPolarization.GeometricKernel.reflection_injOn_positive_halfSphere
      (y := (y : FinRealEuclideanSpace n))
      ⟨finRealSphere_norm_coe n v₁, hv₁⟩
      ⟨finRealSphere_norm_coe n v₂, hv₂⟩
      hmapAmbient

/-- Correct two-point spherical polarization associated to a reflection map. -/
def finRealSpherePolarization
    {n : ℕ} (ρ : FinRealSphereReflectionMap n)
    (v : FinRealSphere n) (A : Set (FinRealSphere n)) :
    Set (FinRealSphere n) :=
  (finRealSphereClosedHemisphere n (v : FinRealEuclideanSpace n) ∩
      (A ∪ (ρ.map v) ⁻¹' A)) ∪
    ((finRealSphereClosedHemisphere n (v : FinRealEuclideanSpace n))ᶜ ∩
      (A ∩ (ρ.map v) ⁻¹' A))

/-- Spherical polarization preserves measurability of sets.  This is the first
bookkeeping step needed before using polarized competitors in the half-mass
variational problem. -/
theorem measurableSet_finRealSpherePolarization
    {n : ℕ} (ρ : FinRealSphereReflectionMap n)
    (v : FinRealSphere n) {A : Set (FinRealSphere n)}
    (hA : MeasurableSet A) :
    MeasurableSet (finRealSpherePolarization ρ v A) := by
  have hH :
      MeasurableSet
        (finRealSphereClosedHemisphere n (v : FinRealEuclideanSpace n)) :=
    measurableSet_finRealSphereClosedHemisphere n (v : FinRealEuclideanSpace n)
  have hpre : MeasurableSet ((ρ.map v) ⁻¹' A) :=
    hA.preimage (ρ.map_measurable v)
  exact (hH.inter (hA.union hpre)).union (hH.compl.inter (hA.inter hpre))

/-- The part of `A` lost by polarizing across the hyperplane orthogonal to `v`:
it lies on the negative side and its reflected partner is outside `A`. -/
def finRealSpherePolarizationLost
    {n : ℕ} (v : FinRealSphere n) (A : Set (FinRealSphere n)) :
    Set (FinRealSphere n) :=
  (finRealSphereClosedHemisphere n (v : FinRealEuclideanSpace n))ᶜ ∩
    (A \ ((finRealSphereReflectionMap n).map v) ⁻¹' A)

/-- The part gained by polarizing across the hyperplane orthogonal to `v`: it
lies on the positive side, is not in `A`, and its reflected partner is in `A`. -/
def finRealSpherePolarizationGained
    {n : ℕ} (v : FinRealSphere n) (A : Set (FinRealSphere n)) :
    Set (FinRealSphere n) :=
  finRealSphereClosedHemisphere n (v : FinRealEuclideanSpace n) ∩
    (Aᶜ ∩ ((finRealSphereReflectionMap n).map v) ⁻¹' A)

/-- Reflection through `vᗮ` flips the signed `v`-height on the concrete real
sphere. -/
theorem finRealSphereReflectionMap_innerCoordinate
    {n : ℕ} (v x : FinRealSphere n) :
    finRealSphereInnerCoordinate n (v : FinRealEuclideanSpace n)
        ((finRealSphereReflectionMap n).map v x) =
      -finRealSphereInnerCoordinate n (v : FinRealEuclideanSpace n) x := by
  simp [finRealSphereInnerCoordinate, finRealSphereReflectionMap_map_coe,
    inner_sub_right, inner_smul_right, finRealSphere_norm_coe n v,
    real_inner_comm]
  ring_nf

/-- Positive-side half of the neighbourhood comparison for polarization:
points on the positive side that belong to the polarization of the
`r`-neighbourhood of `A` already lie in the `r`-neighbourhood of the
polarized set.  This is the direct pointwise input for the full
polarization-neighbourhood objective comparison. -/
theorem finRealSpherePolarization_positiveSide_geodesicThickening_subset
    {n : ℕ} (v : FinRealSphere n) (r : ℝ)
    (A : Set (FinRealSphere n)) :
    finRealSphereClosedHemisphere n (v : FinRealEuclideanSpace n) ∩
        (finRealSphereGeodesicThickening n r A ∪
          ((finRealSphereReflectionMap n).map v) ⁻¹'
            finRealSphereGeodesicThickening n r A) ⊆
      finRealSphereGeodesicThickening n r
        (finRealSpherePolarization (finRealSphereReflectionMap n) v A) := by
  intro x hx
  rcases hx with ⟨hxH, hxN | hxpre⟩
  · rcases hxN with ⟨a, haA, hdist⟩
    by_cases haH :
        a ∈ finRealSphereClosedHemisphere n (v : FinRealEuclideanSpace n)
    · refine ⟨a, ?_, hdist⟩
      left
      exact ⟨haH, Or.inl haA⟩
    · have haNonpos :
          finRealSphereInnerCoordinate n (v : FinRealEuclideanSpace n) a ≤ 0 := by
        have hlt :
            finRealSphereInnerCoordinate n (v : FinRealEuclideanSpace n) a < 0 := by
          simpa [finRealSphereClosedHemisphere, finRealSphereClosedHalfspace] using
            lt_of_not_ge haH
        exact le_of_lt hlt
      refine ⟨(finRealSphereReflectionMap n).map v a, ?_, ?_⟩
      · left
        refine ⟨?_, Or.inr ?_⟩
        · have hcoord := finRealSphereReflectionMap_innerCoordinate v a
          have hnonneg :
              0 ≤ -finRealSphereInnerCoordinate n
                (v : FinRealEuclideanSpace n) a := by
            linarith
          simpa [finRealSphereClosedHemisphere, finRealSphereClosedHalfspace,
            hcoord] using hnonneg
        · simpa [(finRealSphereReflectionMap n).map_involutive] using haA
      · exact lt_of_le_of_lt
          (finRealSphereReflectionMap_geodesicDistance_reflection_right_le_of_nonneg_nonpos
            v x a
            (by
              simpa [finRealSphereClosedHemisphere, finRealSphereClosedHalfspace]
                using hxH)
            haNonpos)
          hdist
  · rcases hxpre with ⟨a, haA, hdist⟩
    by_cases haH :
        a ∈ finRealSphereClosedHemisphere n (v : FinRealEuclideanSpace n)
    · refine ⟨a, ?_, ?_⟩
      · left
        exact ⟨haH, Or.inl haA⟩
      · exact lt_of_le_of_lt
          (finRealSphereReflectionMap_geodesicDistance_le_reflection_left_of_nonneg_nonneg
            v x a
            (by
              simpa [finRealSphereClosedHemisphere, finRealSphereClosedHalfspace]
                using hxH)
            (by
              simpa [finRealSphereClosedHemisphere, finRealSphereClosedHalfspace]
                using haH))
          hdist
    · have haNonpos :
          finRealSphereInnerCoordinate n (v : FinRealEuclideanSpace n) a ≤ 0 := by
        have hlt :
            finRealSphereInnerCoordinate n (v : FinRealEuclideanSpace n) a < 0 := by
          simpa [finRealSphereClosedHemisphere, finRealSphereClosedHalfspace] using
            lt_of_not_ge haH
        exact le_of_lt hlt
      refine ⟨(finRealSphereReflectionMap n).map v a, ?_, ?_⟩
      · left
        refine ⟨?_, Or.inr ?_⟩
        · have hcoord := finRealSphereReflectionMap_innerCoordinate v a
          have hnonneg :
              0 ≤ -finRealSphereInnerCoordinate n
                (v : FinRealEuclideanSpace n) a := by
            linarith
          simpa [finRealSphereClosedHemisphere, finRealSphereClosedHalfspace,
            hcoord] using hnonneg
        · simpa [(finRealSphereReflectionMap n).map_involutive] using haA
      · have heq :
            finRealSphereGeodesicDistance n x
                ((finRealSphereReflectionMap n).map v a) =
              finRealSphereGeodesicDistance n
                ((finRealSphereReflectionMap n).map v x) a := by
          simpa [(finRealSphereReflectionMap n).map_involutive] using
            (finRealSphereReflectionMap_geodesicDistance n v x
              ((finRealSphereReflectionMap n).map v a)).symm
        rwa [heq]

/-- Pairwise neighbourhood statement for polarization: every point of the
`r`-neighbourhood of `A` has at least one representative in its reflection pair
inside the `r`-neighbourhood of the polarized set. -/
theorem finRealSpherePolarization_geodesicThickening_pair_of_mem
    {n : ℕ} (v : FinRealSphere n) (r : ℝ)
    (A : Set (FinRealSphere n)) {x : FinRealSphere n}
    (hxN : x ∈ finRealSphereGeodesicThickening n r A) :
    x ∈ finRealSphereGeodesicThickening n r
        (finRealSpherePolarization (finRealSphereReflectionMap n) v A) ∨
      (finRealSphereReflectionMap n).map v x ∈
        finRealSphereGeodesicThickening n r
          (finRealSpherePolarization (finRealSphereReflectionMap n) v A) := by
  rcases hxN with ⟨a, haA, hdist⟩
  by_cases haH :
      a ∈ finRealSphereClosedHemisphere n (v : FinRealEuclideanSpace n)
  · left
    exact ⟨a, Or.inl ⟨haH, Or.inl haA⟩, hdist⟩
  · right
    refine ⟨(finRealSphereReflectionMap n).map v a, ?_, ?_⟩
    · left
      refine ⟨?_, Or.inr ?_⟩
      · have haNonpos :
            finRealSphereInnerCoordinate n (v : FinRealEuclideanSpace n) a ≤ 0 := by
          have hlt :
              finRealSphereInnerCoordinate n
                (v : FinRealEuclideanSpace n) a < 0 := by
            simpa [finRealSphereClosedHemisphere, finRealSphereClosedHalfspace] using
              lt_of_not_ge haH
          exact le_of_lt hlt
        have hcoord := finRealSphereReflectionMap_innerCoordinate v a
        have hnonneg :
            0 ≤ -finRealSphereInnerCoordinate n
              (v : FinRealEuclideanSpace n) a := by
          linarith
        simpa [finRealSphereClosedHemisphere, finRealSphereClosedHalfspace,
          hcoord] using hnonneg
      · simpa [(finRealSphereReflectionMap n).map_involutive] using haA
    · rwa [finRealSphereReflectionMap_geodesicDistance n v x a]

/-- Set-level union form of the pairwise neighbourhood statement: the
`r`-neighbourhood of `A` is contained in the union of the polarized
neighbourhood and its reflection preimage. -/
theorem finRealSphereGeodesicThickening_subset_polarized_union_reflection_preimage
    {n : ℕ} (v : FinRealSphere n) (r : ℝ)
    (A : Set (FinRealSphere n)) :
    finRealSphereGeodesicThickening n r A ⊆
      finRealSphereGeodesicThickening n r
          (finRealSpherePolarization (finRealSphereReflectionMap n) v A) ∪
        ((finRealSphereReflectionMap n).map v) ⁻¹'
          finRealSphereGeodesicThickening n r
            (finRealSpherePolarization (finRealSphereReflectionMap n) v A) := by
  intro x hx
  rcases finRealSpherePolarization_geodesicThickening_pair_of_mem v r A hx with
    hxP | hxP
  · exact Or.inl hxP
  · exact Or.inr hxP

/-- Measure-level positive-side consequence of the polarization-neighbourhood
inclusion.  This is the first `measureReal` form needed for the eventual
two-point comparison of neighbourhood complements. -/
theorem finRealSurfaceProbabilityMeasure_positiveSide_pairNeighbourhood_real_le_polarizedThickening
    {n : ℕ} (v : FinRealSphere n) (r : ℝ)
    (A : Set (FinRealSphere n)) :
    (finRealSurfaceProbabilityMeasure n).real
        (finRealSphereClosedHemisphere n (v : FinRealEuclideanSpace n) ∩
          (finRealSphereGeodesicThickening n r A ∪
            ((finRealSphereReflectionMap n).map v) ⁻¹'
              finRealSphereGeodesicThickening n r A)) ≤
      (finRealSurfaceProbabilityMeasure n).real
        (finRealSphereGeodesicThickening n r
          (finRealSpherePolarization (finRealSphereReflectionMap n) v A)) := by
  haveI : IsFiniteMeasure (finRealSurfaceProbabilityMeasure n) := by
    unfold finRealSurfaceProbabilityMeasure
    infer_instance
  exact measureReal_mono
    (finRealSpherePolarization_positiveSide_geodesicThickening_subset v r A)
    (h₂ := (measure_lt_top (finRealSurfaceProbabilityMeasure n)
      (finRealSphereGeodesicThickening n r
        (finRealSpherePolarization (finRealSphereReflectionMap n) v A))).ne)

/-- Pair-count measure bound for reflection-invariant sets: the total
normalized surface mass is controlled by twice the mass of the positive-side
representatives. -/
theorem finRealSurfaceProbabilityMeasure_reflectionInvariant_real_le_two_positiveSide
    {n : ℕ} [NeZero n] (v : FinRealSphere n)
    {S : Set (FinRealSphere n)} (hS : MeasurableSet S)
    (hInv : ((finRealSphereReflectionMap n).map v) ⁻¹' S = S) :
    (finRealSurfaceProbabilityMeasure n).real S ≤
      2 * (finRealSurfaceProbabilityMeasure n).real
        (finRealSphereClosedHemisphere n (v : FinRealEuclideanSpace n) ∩ S) := by
  let μ := finRealSurfaceProbabilityMeasure n
  let T : FinRealSphere n → FinRealSphere n := (finRealSphereReflectionMap n).map v
  let H : Set (FinRealSphere n) :=
    finRealSphereClosedHemisphere n (v : FinRealEuclideanSpace n)
  let TH : Set (FinRealSphere n) := T ⁻¹' H
  haveI : IsFiniteMeasure μ := by
    unfold μ finRealSurfaceProbabilityMeasure
    infer_instance
  have hcover : S ⊆ (H ∩ S) ∪ (TH ∩ S) := by
    intro x hxS
    by_cases hxH : x ∈ H
    · exact Or.inl ⟨hxH, hxS⟩
    · have hxcoord_lt :
          finRealSphereInnerCoordinate n (v : FinRealEuclideanSpace n) x < 0 := by
        simpa [H, finRealSphereClosedHemisphere, finRealSphereClosedHalfspace] using
          lt_of_not_ge hxH
      have hTxH : T x ∈ H := by
        have hcoord := finRealSphereReflectionMap_innerCoordinate v x
        have hnonneg :
            0 ≤ finRealSphereInnerCoordinate n
              (v : FinRealEuclideanSpace n) (T x) := by
          linarith
        simpa [T, H, finRealSphereClosedHemisphere, finRealSphereClosedHalfspace]
          using hnonneg
      exact Or.inr ⟨hTxH, hxS⟩
  have hmono : μ.real S ≤ μ.real ((H ∩ S) ∪ (TH ∩ S)) :=
    measureReal_mono hcover
      (h₂ := (measure_lt_top μ ((H ∩ S) ∪ (TH ∩ S))).ne)
  have hunion :
      μ.real ((H ∩ S) ∪ (TH ∩ S)) ≤ μ.real (H ∩ S) + μ.real (TH ∩ S) :=
    measureReal_union_le _ _
  have hHmeas : MeasurableSet H := by
    dsimp [H]
    exact measurableSet_finRealSphereClosedHemisphere n (v : FinRealEuclideanSpace n)
  have hpre : T ⁻¹' (H ∩ S) = TH ∩ S := by
    ext x
    simp [T, TH, hInv, and_comm]
  have hEq : μ.real (TH ∩ S) = μ.real (H ∩ S) := by
    rw [← hpre]
    exact finRealSurfaceProbabilityMeasure_reflection_preimage_real n v (hHmeas.inter hS)
  calc
    μ.real S ≤ μ.real ((H ∩ S) ∪ (TH ∩ S)) := hmono
    _ ≤ μ.real (H ∩ S) + μ.real (TH ∩ S) := hunion
    _ = 2 * μ.real (H ∩ S) := by
      rw [hEq]
      ring

/-- Combined pair-count form for neighbourhoods: the union of a geodesic
neighbourhood and its reflection preimage has mass at most twice the mass of
the polarized geodesic neighbourhood. -/
theorem finRealSurfaceProbabilityMeasure_pairNeighbourhoodUnion_real_le_two_polarizedThickening
    {n : ℕ} [NeZero n] (v : FinRealSphere n) (r : ℝ)
    (A : Set (FinRealSphere n)) :
    (finRealSurfaceProbabilityMeasure n).real
        (finRealSphereGeodesicThickening n r A ∪
          ((finRealSphereReflectionMap n).map v) ⁻¹'
            finRealSphereGeodesicThickening n r A) ≤
      2 * (finRealSurfaceProbabilityMeasure n).real
        (finRealSphereGeodesicThickening n r
          (finRealSpherePolarization (finRealSphereReflectionMap n) v A)) := by
  let μ := finRealSurfaceProbabilityMeasure n
  let T : FinRealSphere n → FinRealSphere n := (finRealSphereReflectionMap n).map v
  let B : Set (FinRealSphere n) := finRealSphereGeodesicThickening n r A
  let P : Set (FinRealSphere n) :=
    finRealSphereGeodesicThickening n r
      (finRealSpherePolarization (finRealSphereReflectionMap n) v A)
  let U : Set (FinRealSphere n) := B ∪ T ⁻¹' B
  have hB : MeasurableSet B := by
    dsimp [B]
    exact measurableSet_finRealSphereGeodesicThickening n r A
  have hU : MeasurableSet U := by
    dsimp [U]
    exact hB.union (hB.preimage ((finRealSphereReflectionMap n).map_measurable v))
  have hInv : T ⁻¹' U = U := by
    ext x
    simp [U, B, T, (finRealSphereReflectionMap n).map_involutive, or_comm]
  have hcount :=
    finRealSurfaceProbabilityMeasure_reflectionInvariant_real_le_two_positiveSide
      v hU hInv
  have hpos :=
    finRealSurfaceProbabilityMeasure_positiveSide_pairNeighbourhood_real_le_polarizedThickening
      v r A
  dsimp [U, B, P, T] at hcount hpos ⊢
  nlinarith

/-- Sharp neighbourhood comparison under polarization: the geodesic
neighbourhood of the polarized set is contained in the polarization of the
geodesic neighbourhood.  This is the no-factor-loss set inclusion needed for
the objective comparison. -/
theorem finRealSphereGeodesicThickening_polarization_subset_polarization_geodesicThickening
    {n : ℕ} (v : FinRealSphere n) (r : ℝ)
    (A : Set (FinRealSphere n)) :
    finRealSphereGeodesicThickening n r
        (finRealSpherePolarization (finRealSphereReflectionMap n) v A) ⊆
      finRealSpherePolarization (finRealSphereReflectionMap n) v
        (finRealSphereGeodesicThickening n r A) := by
  intro x hx
  rcases hx with ⟨a, haPA, hdist⟩
  let H : Set (FinRealSphere n) :=
    finRealSphereClosedHemisphere n (v : FinRealEuclideanSpace n)
  let T : FinRealSphere n → FinRealSphere n := (finRealSphereReflectionMap n).map v
  by_cases hxH : x ∈ H
  · left
    refine ⟨hxH, ?_⟩
    rcases haPA with haPos | haNeg
    · rcases haPos with ⟨haH, haA | hTaA⟩
      · exact Or.inl ⟨a, haA, hdist⟩
      · right
        refine ⟨T a, hTaA, ?_⟩
        have heq :
            finRealSphereGeodesicDistance n (T x) (T a) =
              finRealSphereGeodesicDistance n x a := by
          simpa [T] using finRealSphereReflectionMap_geodesicDistance n v x a
        simpa [T, heq] using hdist
    · rcases haNeg with ⟨haHc, haA, hTaA⟩
      exact Or.inl ⟨a, haA, hdist⟩
  · right
    refine ⟨hxH, ?_⟩
    constructor
    · rcases haPA with haPos | haNeg
      · rcases haPos with ⟨haH, haA | hTaA⟩
        · exact ⟨a, haA, hdist⟩
        · refine ⟨T a, hTaA, ?_⟩
          have hxNonpos :
              finRealSphereInnerCoordinate n (v : FinRealEuclideanSpace n) x ≤ 0 := by
            have hlt :
                finRealSphereInnerCoordinate n (v : FinRealEuclideanSpace n) x < 0 := by
              simpa [H, finRealSphereClosedHemisphere, finRealSphereClosedHalfspace] using
                lt_of_not_ge hxH
            exact le_of_lt hlt
          have haNonneg :
              0 ≤ finRealSphereInnerCoordinate n (v : FinRealEuclideanSpace n) a := by
            simpa [H, finRealSphereClosedHemisphere, finRealSphereClosedHalfspace] using haH
          have hleTx :
              finRealSphereGeodesicDistance n (T x) a ≤
                finRealSphereGeodesicDistance n x a := by
            have h :=
              finRealSphereReflectionMap_geodesicDistance_reflection_right_le_of_nonneg_nonpos
                v a x haNonneg hxNonpos
            simpa [T, finRealSphereGeodesicDistance, dist_comm] using h
          have heq :
              finRealSphereGeodesicDistance n x (T a) =
                finRealSphereGeodesicDistance n (T x) a := by
            simpa [T, (finRealSphereReflectionMap n).map_involutive] using
              (finRealSphereReflectionMap_geodesicDistance n v x (T a)).symm
          exact lt_of_le_of_lt (by simpa [heq] using hleTx) hdist
      · rcases haNeg with ⟨haHc, haA, hTaA⟩
        exact ⟨a, haA, hdist⟩
    · rcases haPA with haPos | haNeg
      · rcases haPos with ⟨haH, haA | hTaA⟩
        · refine ⟨a, haA, ?_⟩
          have hxNonpos :
              finRealSphereInnerCoordinate n (v : FinRealEuclideanSpace n) x ≤ 0 := by
            have hlt :
                finRealSphereInnerCoordinate n (v : FinRealEuclideanSpace n) x < 0 := by
              simpa [H, finRealSphereClosedHemisphere, finRealSphereClosedHalfspace] using
                lt_of_not_ge hxH
            exact le_of_lt hlt
          have haNonneg :
              0 ≤ finRealSphereInnerCoordinate n (v : FinRealEuclideanSpace n) a := by
            simpa [H, finRealSphereClosedHemisphere, finRealSphereClosedHalfspace] using haH
          have hle :
              finRealSphereGeodesicDistance n (T x) a ≤
                finRealSphereGeodesicDistance n x a := by
            have h :=
              finRealSphereReflectionMap_geodesicDistance_reflection_right_le_of_nonneg_nonpos
                v a x haNonneg hxNonpos
            simpa [T, finRealSphereGeodesicDistance, dist_comm] using h
          exact lt_of_le_of_lt hle hdist
        · refine ⟨T a, hTaA, ?_⟩
          have heq :
              finRealSphereGeodesicDistance n (T x) (T a) =
                finRealSphereGeodesicDistance n x a := by
            simpa [T] using finRealSphereReflectionMap_geodesicDistance n v x a
          simpa [T, heq] using hdist
      · rcases haNeg with ⟨haHc, haA, hTaA⟩
        refine ⟨T a, hTaA, ?_⟩
        have heq :
            finRealSphereGeodesicDistance n (T x) (T a) =
              finRealSphereGeodesicDistance n x a := by
          simpa [T] using finRealSphereReflectionMap_geodesicDistance n v x a
        simpa [T, heq] using hdist

/-- Boundary points of the reflecting hyperplane are fixed by the canonical
sphere reflection. -/
theorem finRealSphereReflectionMap_eq_self_of_innerCoordinate_eq_zero
    {n : ℕ} (v x : FinRealSphere n)
    (hcoord :
      finRealSphereInnerCoordinate n (v : FinRealEuclideanSpace n) x = 0) :
    (finRealSphereReflectionMap n).map v x = x := by
  apply Subtype.ext
  rw [finRealSphereReflectionMap_map_coe]
  have hinner :
      ⟪(x : FinRealEuclideanSpace n), (v : FinRealEuclideanSpace n)⟫_ℝ = 0 := by
    simpa [finRealSphereInnerCoordinate, real_inner_comm] using hcoord
  simp [hinner]

/-- Polarization is obtained from `A` by deleting the lost part and adding the
gained part. -/
theorem finRealSpherePolarization_eq_diff_union_gained
    {n : ℕ} (v : FinRealSphere n) (A : Set (FinRealSphere n)) :
    finRealSpherePolarization (finRealSphereReflectionMap n) v A =
      (A \ finRealSpherePolarizationLost v A) ∪
        finRealSpherePolarizationGained v A := by
  ext x
  simp [finRealSpherePolarization, finRealSpherePolarizationLost,
    finRealSpherePolarizationGained]
  tauto

/-- Under reflection, the gained part pulls back to the lost part.  The only
boundary case is harmless because the reflection fixes the equator. -/
theorem finRealSphereReflectionMap_preimage_polarizationGained
    {n : ℕ} (v : FinRealSphere n) (A : Set (FinRealSphere n)) :
    ((finRealSphereReflectionMap n).map v) ⁻¹'
        (finRealSpherePolarizationGained v A) =
      finRealSpherePolarizationLost v A := by
  ext x
  have hcoord :
      finRealSphereInnerCoordinate n (v : FinRealEuclideanSpace n)
          ((finRealSphereReflectionMap n).map v x) =
        -finRealSphereInnerCoordinate n (v : FinRealEuclideanSpace n) x :=
    finRealSphereReflectionMap_innerCoordinate v x
  have hfix_of_zero :
      finRealSphereInnerCoordinate n (v : FinRealEuclideanSpace n) x = 0 →
        (finRealSphereReflectionMap n).map v x = x :=
    finRealSphereReflectionMap_eq_self_of_innerCoordinate_eq_zero v x
  simp [finRealSpherePolarizationGained, finRealSpherePolarizationLost,
    finRealSphereClosedHemisphere, finRealSphereClosedHalfspace, hcoord,
    (finRealSphereReflectionMap n).map_involutive]
  constructor
  · intro h
    have hnonpos :
        finRealSphereInnerCoordinate n (v : FinRealEuclideanSpace n) x ≤ 0 := h.1
    have hnot : (finRealSphereReflectionMap n).map v x ∉ A := h.2.1
    have hxA : x ∈ A := h.2.2
    have hlt :
        finRealSphereInnerCoordinate n (v : FinRealEuclideanSpace n) x < 0 := by
      rcases lt_or_eq_of_le hnonpos with hlt | hzero
      · exact hlt
      · exfalso
        exact hnot (by simpa [hfix_of_zero hzero] using hxA)
    exact ⟨hlt, hxA, hnot⟩
  · intro h
    exact ⟨by linarith [h.1], h.2.2, h.2.1⟩

/-- The lost part of a measurable set is measurable. -/
theorem measurableSet_finRealSpherePolarizationLost
    {n : ℕ} (v : FinRealSphere n) {A : Set (FinRealSphere n)}
    (hA : MeasurableSet A) :
    MeasurableSet (finRealSpherePolarizationLost v A) := by
  have hH :
      MeasurableSet
        (finRealSphereClosedHemisphere n (v : FinRealEuclideanSpace n)) :=
    measurableSet_finRealSphereClosedHemisphere n (v : FinRealEuclideanSpace n)
  have hpre :
      MeasurableSet (((finRealSphereReflectionMap n).map v) ⁻¹' A) :=
    hA.preimage ((finRealSphereReflectionMap n).map_measurable v)
  exact hH.compl.inter (hA.diff hpre)

/-- The gained part of a measurable set is measurable. -/
theorem measurableSet_finRealSpherePolarizationGained
    {n : ℕ} (v : FinRealSphere n) {A : Set (FinRealSphere n)}
    (hA : MeasurableSet A) :
    MeasurableSet (finRealSpherePolarizationGained v A) := by
  have hH :
      MeasurableSet
        (finRealSphereClosedHemisphere n (v : FinRealEuclideanSpace n)) :=
    measurableSet_finRealSphereClosedHemisphere n (v : FinRealEuclideanSpace n)
  have hpre :
      MeasurableSet (((finRealSphereReflectionMap n).map v) ⁻¹' A) :=
    hA.preimage ((finRealSphereReflectionMap n).map_measurable v)
  exact hH.inter (hA.compl.inter hpre)

/-- The gained and lost pieces have equal normalized surface mass. -/
theorem finRealSurfaceProbabilityMeasure_polarizationGained_real_eq_lost_real
    {n : ℕ} [NeZero n] (v : FinRealSphere n)
    {A : Set (FinRealSphere n)} (hA : MeasurableSet A) :
    (finRealSurfaceProbabilityMeasure n).real
        (finRealSpherePolarizationGained v A) =
      (finRealSurfaceProbabilityMeasure n).real
        (finRealSpherePolarizationLost v A) := by
  calc
    (finRealSurfaceProbabilityMeasure n).real
        (finRealSpherePolarizationGained v A)
        =
      (finRealSurfaceProbabilityMeasure n).real
        (((finRealSphereReflectionMap n).map v) ⁻¹'
          (finRealSpherePolarizationGained v A)) := by
        rw [finRealSurfaceProbabilityMeasure_reflection_preimage_real n v
          (measurableSet_finRealSpherePolarizationGained v hA)]
    _ =
      (finRealSurfaceProbabilityMeasure n).real
        (finRealSpherePolarizationLost v A) := by
        rw [finRealSphereReflectionMap_preimage_polarizationGained]

/-- Every value of the normalized surface probability is finite. -/
theorem finRealSurfaceProbabilityMeasure_ne_top
    {n : ℕ} [NeZero n] (S : Set (FinRealSphere n)) :
    (finRealSurfaceProbabilityMeasure n) S ≠ ⊤ := by
  have hprob : IsProbabilityMeasure (finRealSurfaceProbabilityMeasure n) :=
    finRealSurfaceProbabilityMeasure_isProbabilityMeasure n
  letI := hprob
  have hle :
      (finRealSurfaceProbabilityMeasure n) S ≤
        (finRealSurfaceProbabilityMeasure n) Set.univ :=
    measure_mono (Set.subset_univ S)
  have huniv : (finRealSurfaceProbabilityMeasure n) Set.univ = 1 := by
    exact measure_univ (μ := finRealSurfaceProbabilityMeasure n)
  have hlt : (finRealSurfaceProbabilityMeasure n) S < ⊤ := by
    calc
      (finRealSurfaceProbabilityMeasure n) S ≤
          (finRealSurfaceProbabilityMeasure n) Set.univ := hle
      _ = 1 := huniv
      _ < ⊤ := ENNReal.one_lt_top
  exact hlt.ne

/-- Spherical polarization preserves normalized surface mass. -/
theorem finRealSurfaceProbabilityMeasure_polarization_real_eq
    {n : ℕ} [NeZero n] (v : FinRealSphere n)
    {A : Set (FinRealSphere n)} (hA : MeasurableSet A) :
    (finRealSurfaceProbabilityMeasure n).real
        (finRealSpherePolarization (finRealSphereReflectionMap n) v A) =
      (finRealSurfaceProbabilityMeasure n).real A := by
  let μ := finRealSurfaceProbabilityMeasure n
  let lost := finRealSpherePolarizationLost v A
  let gained := finRealSpherePolarizationGained v A
  have hlost_meas : MeasurableSet lost :=
    measurableSet_finRealSpherePolarizationLost v hA
  have hgained_meas : MeasurableSet gained :=
    measurableSet_finRealSpherePolarizationGained v hA
  have hgain_eq_lost : μ.real gained = μ.real lost := by
    dsimp [μ, gained, lost]
    exact finRealSurfaceProbabilityMeasure_polarizationGained_real_eq_lost_real v hA
  have hpolar :
      finRealSpherePolarization (finRealSphereReflectionMap n) v A =
        (A \ lost) ∪ gained := by
    dsimp [lost, gained]
    exact finRealSpherePolarization_eq_diff_union_gained v A
  have hlost_subset : lost ⊆ A := by
    intro x hx
    exact hx.2.1
  have hgained_subset_compl : gained ⊆ Aᶜ := by
    intro x hx
    exact hx.2.1
  have hdisj₁ : Disjoint (A \ lost) gained := by
    rw [disjoint_left]
    intro x hxA hxg
    exact hgained_subset_compl hxg hxA.1
  have hdisj₂ : Disjoint (A \ lost) lost := by
    rw [disjoint_left]
    intro x hxA hxl
    exact hxA.2 hxl
  have hunionA : (A \ lost) ∪ lost = A := by
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact hx.1
      · exact hlost_subset hx
    · intro hxA
      by_cases hxl : x ∈ lost
      · exact Or.inr hxl
      · exact Or.inl ⟨hxA, hxl⟩
  have hfinite (S : Set (FinRealSphere n)) : μ S ≠ ⊤ := by
    dsimp [μ]
    exact finRealSurfaceProbabilityMeasure_ne_top S
  have hPmeasure :
      μ.real (finRealSpherePolarization (finRealSphereReflectionMap n) v A) =
        μ.real (A \ lost) + μ.real gained := by
    rw [hpolar]
    exact measureReal_union hdisj₁ hgained_meas
      (hfinite (A \ lost)) (hfinite gained)
  have hAmeasure : μ.real A = μ.real (A \ lost) + μ.real lost := by
    calc
      μ.real A = μ.real ((A \ lost) ∪ lost) := by rw [hunionA]
      _ = μ.real (A \ lost) + μ.real lost :=
        measureReal_union hdisj₂ hlost_meas
          (hfinite (A \ lost)) (hfinite lost)
  rw [hPmeasure, hAmeasure, hgain_eq_lost]

/-- Polarization does not increase the normalized surface mass of a geodesic
neighbourhood.  This is the objective-monotonicity form of the sharp
neighbourhood inclusion above. -/
theorem finRealSurfaceProbabilityMeasure_geodesicThickening_polarization_real_le
    {n : ℕ} [NeZero n] (v : FinRealSphere n) (r : ℝ)
    (A : Set (FinRealSphere n)) :
    (finRealSurfaceProbabilityMeasure n).real
        (finRealSphereGeodesicThickening n r
          (finRealSpherePolarization (finRealSphereReflectionMap n) v A)) ≤
      (finRealSurfaceProbabilityMeasure n).real
        (finRealSphereGeodesicThickening n r A) := by
  let μ := finRealSurfaceProbabilityMeasure n
  have hthick_meas :
      MeasurableSet (finRealSphereGeodesicThickening n r A) :=
    measurableSet_finRealSphereGeodesicThickening n r A
  have hsubset :=
    finRealSphereGeodesicThickening_polarization_subset_polarization_geodesicThickening
      v r A
  have hmono :
      μ.real
          (finRealSphereGeodesicThickening n r
            (finRealSpherePolarization (finRealSphereReflectionMap n) v A)) ≤
        μ.real
          (finRealSpherePolarization (finRealSphereReflectionMap n) v
            (finRealSphereGeodesicThickening n r A)) := by
    exact measureReal_mono (μ := μ) hsubset
      (h₂ := by
        dsimp [μ]
        exact finRealSurfaceProbabilityMeasure_ne_top
          (finRealSpherePolarization (finRealSphereReflectionMap n) v
            (finRealSphereGeodesicThickening n r A)))
  have hmass :=
    finRealSurfaceProbabilityMeasure_polarization_real_eq v hthick_meas
  exact hmono.trans (le_of_eq hmass)

/-- In the half-mass variational objective, polarization can only increase the
mass of the complement of the geodesic neighbourhood. -/
theorem finRealSphereNeighbourhoodComplementMass_polarization_ge
    {n : ℕ} [NeZero n] (v : FinRealSphere n) (r : ℝ)
    (A : Set (FinRealSphere n)) :
    finRealSphereNeighbourhoodComplementMass n
        (finRealSurfaceProbabilityMeasure n) r A ≤
      finRealSphereNeighbourhoodComplementMass n
        (finRealSurfaceProbabilityMeasure n) r
        (finRealSpherePolarization (finRealSphereReflectionMap n) v A) := by
  let μ := finRealSurfaceProbabilityMeasure n
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact finRealSurfaceProbabilityMeasure_isProbabilityMeasure n
  have hthick_le :=
    finRealSurfaceProbabilityMeasure_geodesicThickening_polarization_real_le
      v r A
  have hA_meas :
      MeasurableSet (finRealSphereGeodesicThickening n r A) :=
    measurableSet_finRealSphereGeodesicThickening n r A
  have hP_meas :
      MeasurableSet
        (finRealSphereGeodesicThickening n r
          (finRealSpherePolarization (finRealSphereReflectionMap n) v A)) :=
    measurableSet_finRealSphereGeodesicThickening n r
      (finRealSpherePolarization (finRealSphereReflectionMap n) v A)
  have hA_compl :
      μ.real (finRealSphereGeodesicThickening n r A)ᶜ =
        1 - μ.real (finRealSphereGeodesicThickening n r A) := by
    simpa [μ] using measureReal_compl (μ := μ) hA_meas
  have hP_compl :
      μ.real
          (finRealSphereGeodesicThickening n r
            (finRealSpherePolarization (finRealSphereReflectionMap n) v A))ᶜ =
        1 - μ.real
          (finRealSphereGeodesicThickening n r
            (finRealSpherePolarization (finRealSphereReflectionMap n) v A)) := by
    simpa [μ] using measureReal_compl (μ := μ) hP_meas
  dsimp [finRealSphereNeighbourhoodComplementMass, μ]
  rw [hA_compl, hP_compl]
  linarith

/-- Polarizing a half-mass competitor keeps it a half-mass competitor. -/
theorem finRealSphereHalfMassCompetitor_polarization
    {n : ℕ} [NeZero n] (v : FinRealSphere n)
    {A : Set (FinRealSphere n)}
    (hA :
      FinRealSphereHalfMassCompetitor n
        (finRealSurfaceProbabilityMeasure n) A) :
    FinRealSphereHalfMassCompetitor n
      (finRealSurfaceProbabilityMeasure n)
      (finRealSpherePolarization (finRealSphereReflectionMap n) v A) := by
  refine ⟨measurableSet_finRealSpherePolarization
      (finRealSphereReflectionMap n) v hA.1, ?_⟩
  rw [finRealSurfaceProbabilityMeasure_polarization_real_eq v hA.1]
  exact hA.2

/-- Polarizing a half-mass competitor preserves admissibility and does not
decrease the geodesic-neighbourhood complement objective. -/
theorem finRealSphereHalfMassCompetitor_polarization_objective_ge
    {n : ℕ} [NeZero n] (v : FinRealSphere n) (r : ℝ)
    {A : Set (FinRealSphere n)}
    (hA :
      FinRealSphereHalfMassCompetitor n
        (finRealSurfaceProbabilityMeasure n) A) :
    FinRealSphereHalfMassCompetitor n
        (finRealSurfaceProbabilityMeasure n)
        (finRealSpherePolarization (finRealSphereReflectionMap n) v A) ∧
      finRealSphereNeighbourhoodComplementMass n
          (finRealSurfaceProbabilityMeasure n) r A ≤
        finRealSphereNeighbourhoodComplementMass n
          (finRealSurfaceProbabilityMeasure n) r
          (finRealSpherePolarization (finRealSphereReflectionMap n) v A) := by
  exact ⟨finRealSphereHalfMassCompetitor_polarization v hA,
    finRealSphereNeighbourhoodComplementMass_polarization_ge v r A⟩

/-- Near-minimizers may be chosen together with their polarized admissible
competitor, and the polarized objective is no worse.  This is the
minimizing-sequence adapter used before the strict-improvement contradiction. -/
theorem exists_finRealSphereHalfMassCompetitor_near_complementInf_with_polarized_objective_ge
    (n : ℕ) [NeZero n] (v : FinRealSphere n) (r : ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : Set (FinRealSphere n),
      FinRealSphereHalfMassCompetitor n
          (finRealSurfaceProbabilityMeasure n) A ∧
        finRealSphereNeighbourhoodComplementMass n
            (finRealSurfaceProbabilityMeasure n) r A <
          finRealSphereHalfMassComplementInf n
            (finRealSurfaceProbabilityMeasure n) r + δ ∧
        FinRealSphereHalfMassCompetitor n
          (finRealSurfaceProbabilityMeasure n)
          (finRealSpherePolarization (finRealSphereReflectionMap n) v A) ∧
        finRealSphereNeighbourhoodComplementMass n
            (finRealSurfaceProbabilityMeasure n) r A ≤
          finRealSphereNeighbourhoodComplementMass n
            (finRealSurfaceProbabilityMeasure n) r
            (finRealSpherePolarization (finRealSphereReflectionMap n) v A) := by
  rcases exists_finRealSphereHalfMassCompetitor_near_complementInf n r hδ with
    ⟨A, hA, hnear⟩
  exact ⟨A, hA, hnear,
    finRealSphereHalfMassCompetitor_polarization_objective_ge v r hA⟩

/-- Near-supremizers may be chosen together with their polarized admissible
competitor, and the polarized objective is no worse.  This is the correctly
oriented maximizing-sequence adapter for the cap-comparison theorem. -/
theorem exists_finRealSphereHalfMassCompetitor_near_complementSup_with_polarized_objective_ge
    (n : ℕ) [NeZero n] (v : FinRealSphere n) (r : ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : Set (FinRealSphere n),
      FinRealSphereHalfMassCompetitor n
          (finRealSurfaceProbabilityMeasure n) A ∧
        finRealSphereHalfMassComplementSup n
            (finRealSurfaceProbabilityMeasure n) r - δ <
          finRealSphereNeighbourhoodComplementMass n
            (finRealSurfaceProbabilityMeasure n) r A ∧
        FinRealSphereHalfMassCompetitor n
          (finRealSurfaceProbabilityMeasure n)
          (finRealSpherePolarization (finRealSphereReflectionMap n) v A) ∧
        finRealSphereNeighbourhoodComplementMass n
            (finRealSurfaceProbabilityMeasure n) r A ≤
          finRealSphereNeighbourhoodComplementMass n
            (finRealSurfaceProbabilityMeasure n) r
            (finRealSpherePolarization (finRealSphereReflectionMap n) v A) := by
  rcases exists_finRealSphereHalfMassCompetitor_near_complementSup n r hδ with
    ⟨A, hA, hnear⟩
  exact ⟨A, hA, hnear,
    finRealSphereHalfMassCompetitor_polarization_objective_ge v r hA⟩

/-- Supremum contradiction arithmetic: a `δ`-near supremizer cannot have an
admissible strict improvement of size at least `η` unless `η < δ`. -/
theorem finRealSphereHalfMassComplementSup_strictImprovement_lt_tolerance
    (n : ℕ) [NeZero n] (r : ℝ)
    {δ η : ℝ} {A B : Set (FinRealSphere n)}
    (hB :
      FinRealSphereHalfMassCompetitor n
        (finRealSurfaceProbabilityMeasure n) B)
    (hnear :
      finRealSphereHalfMassComplementSup n
          (finRealSurfaceProbabilityMeasure n) r - δ <
        finRealSphereNeighbourhoodComplementMass n
          (finRealSurfaceProbabilityMeasure n) r A)
    (himprove :
      finRealSphereNeighbourhoodComplementMass n
          (finRealSurfaceProbabilityMeasure n) r A + η ≤
        finRealSphereNeighbourhoodComplementMass n
          (finRealSurfaceProbabilityMeasure n) r B) :
    η < δ := by
  have hB_le :=
    finRealSphereHalfMassComplementSup_ge_of_competitor n r hB
  linarith

/-- A near-supremizer can be chosen so that no admissible competitor improves
the neighbourhood-complement objective by the prescribed amount `η`.

This is the direction-free supremum contradiction package: once the tolerance
is `η / 2`, any admissible improvement of size `η` would contradict the
definition of the supremum. -/
theorem exists_finRealSphereHalfMassCompetitor_near_complementSup_no_admissible_eta_improvement
    (n : ℕ) [NeZero n] (r : ℝ)
    {η : ℝ} (hη : 0 < η) :
    ∃ A : Set (FinRealSphere n),
      FinRealSphereHalfMassCompetitor n
          (finRealSurfaceProbabilityMeasure n) A ∧
        finRealSphereHalfMassComplementSup n
            (finRealSurfaceProbabilityMeasure n) r - η / 2 <
          finRealSphereNeighbourhoodComplementMass n
            (finRealSurfaceProbabilityMeasure n) r A ∧
        ∀ B : Set (FinRealSphere n),
          FinRealSphereHalfMassCompetitor n
              (finRealSurfaceProbabilityMeasure n) B →
            ¬
              finRealSphereNeighbourhoodComplementMass n
                  (finRealSurfaceProbabilityMeasure n) r A + η ≤
                finRealSphereNeighbourhoodComplementMass n
                  (finRealSurfaceProbabilityMeasure n) r B := by
  have hδ : 0 < η / 2 := by linarith
  rcases exists_finRealSphereHalfMassCompetitor_near_complementSup n r hδ with
    ⟨A, hA, hnear⟩
  refine ⟨A, hA, hnear, ?_⟩
  intro B hB himprove
  have hlt : η < η / 2 :=
    finRealSphereHalfMassComplementSup_strictImprovement_lt_tolerance
      n r hB hnear himprove
  linarith

/-- A single near-supremizer can be chosen so that every polarization is
admissible, no worse, and nevertheless cannot improve the objective by `η`.

This removes the fixed-direction dependency from the older package below and
is the form needed for a minimizing/maximizing-sequence contradiction against
a geometric strict-improvement theorem. -/
theorem exists_finRealSphereHalfMassCompetitor_near_complementSup_all_polarizations_no_eta_improvement
    (n : ℕ) [NeZero n] (r : ℝ)
    {η : ℝ} (hη : 0 < η) :
    ∃ A : Set (FinRealSphere n),
      FinRealSphereHalfMassCompetitor n
          (finRealSurfaceProbabilityMeasure n) A ∧
        finRealSphereHalfMassComplementSup n
            (finRealSurfaceProbabilityMeasure n) r - η / 2 <
          finRealSphereNeighbourhoodComplementMass n
            (finRealSurfaceProbabilityMeasure n) r A ∧
        ∀ v : FinRealSphere n,
          FinRealSphereHalfMassCompetitor n
              (finRealSurfaceProbabilityMeasure n)
              (finRealSpherePolarization (finRealSphereReflectionMap n) v A) ∧
            finRealSphereNeighbourhoodComplementMass n
                (finRealSurfaceProbabilityMeasure n) r A ≤
              finRealSphereNeighbourhoodComplementMass n
                (finRealSurfaceProbabilityMeasure n) r
                (finRealSpherePolarization (finRealSphereReflectionMap n) v A) ∧
            ¬
              finRealSphereNeighbourhoodComplementMass n
                  (finRealSurfaceProbabilityMeasure n) r A + η ≤
                finRealSphereNeighbourhoodComplementMass n
                  (finRealSurfaceProbabilityMeasure n) r
                  (finRealSpherePolarization (finRealSphereReflectionMap n) v A) := by
  rcases exists_finRealSphereHalfMassCompetitor_near_complementSup_no_admissible_eta_improvement
      n r hη with
    ⟨A, hA, hnear, hno⟩
  refine ⟨A, hA, hnear, ?_⟩
  intro v
  have hpack := finRealSphereHalfMassCompetitor_polarization_objective_ge v r hA
  exact ⟨hpack.1, hpack.2, hno _ hpack.1⟩

/-- A near-supremizer can be chosen so that a fixed polarization cannot improve
the neighbourhood-complement objective by the prescribed amount `η`.

This is the maximizing-sequence contradiction package used before invoking the
geometric strict-improvement theorem: choose the tolerance `η / 2`; any
admissible improvement of size at least `η` would contradict the supremum
arithmetic above. -/
theorem exists_finRealSphereHalfMassCompetitor_near_complementSup_no_fixed_polarization_eta_improvement
    (n : ℕ) [NeZero n] (v : FinRealSphere n) (r : ℝ)
    {η : ℝ} (hη : 0 < η) :
    ∃ A : Set (FinRealSphere n),
      FinRealSphereHalfMassCompetitor n
          (finRealSurfaceProbabilityMeasure n) A ∧
        finRealSphereHalfMassComplementSup n
            (finRealSurfaceProbabilityMeasure n) r - η / 2 <
          finRealSphereNeighbourhoodComplementMass n
            (finRealSurfaceProbabilityMeasure n) r A ∧
        FinRealSphereHalfMassCompetitor n
          (finRealSurfaceProbabilityMeasure n)
          (finRealSpherePolarization (finRealSphereReflectionMap n) v A) ∧
        finRealSphereNeighbourhoodComplementMass n
            (finRealSurfaceProbabilityMeasure n) r A ≤
          finRealSphereNeighbourhoodComplementMass n
            (finRealSurfaceProbabilityMeasure n) r
            (finRealSpherePolarization (finRealSphereReflectionMap n) v A) ∧
        ¬
          finRealSphereNeighbourhoodComplementMass n
              (finRealSurfaceProbabilityMeasure n) r A + η ≤
            finRealSphereNeighbourhoodComplementMass n
              (finRealSurfaceProbabilityMeasure n) r
              (finRealSpherePolarization (finRealSphereReflectionMap n) v A) := by
  have hδ : 0 < η / 2 := by linarith
  rcases exists_finRealSphereHalfMassCompetitor_near_complementSup_with_polarized_objective_ge
      n v r hδ with
    ⟨A, hA, hnear, hPA, hmono⟩
  refine ⟨A, hA, hnear, hPA, hmono, ?_⟩
  intro himprove
  have hlt :
      η < η / 2 :=
    finRealSphereHalfMassComplementSup_strictImprovement_lt_tolerance
      n r hPA hnear himprove
  linarith

/-- Tangent submodule at a point of the unit sphere. -/
def finRealSphereTangentSubmodule
    {n : ℕ} (x : FinRealSphere n) :
    Submodule ℝ (FinRealEuclideanSpace n) :=
  (ℝ ∙ (x : FinRealEuclideanSpace n))ᗮ

/-- Ambient inverse direction for `v ↦ rho_v(y)`, defined off the diagonal. -/
def finRealSpherePolarizationInverseDirectionAmbient
    {n : ℕ} (y x : FinRealSphere n) : FinRealEuclideanSpace n :=
  (‖(y : FinRealEuclideanSpace n) - (x : FinRealEuclideanSpace n)‖)⁻¹ •
    ((y : FinRealEuclideanSpace n) - (x : FinRealEuclideanSpace n))

@[simp]
theorem finRealSpherePolarizationInverseDirectionAmbient_eq
    {n : ℕ} (y x : FinRealSphere n) :
    finRealSpherePolarizationInverseDirectionAmbient y x =
      SphericalPolarization.GeometricKernel.polarizationInverseDirection
        (y : FinRealEuclideanSpace n) (x : FinRealEuclideanSpace n) :=
  rfl

/-- Explicit inverse target for the parametrization, off the diagonal. -/
def FinRealSpherePolarizationInverseFormula
    {n : ℕ} (ρ : FinRealSphereReflectionMap n) : Prop :=
  ∀ y x : FinRealSphere n,
    x ≠ y →
      ∃ v : FinRealSphere n,
        v ∈ finRealSphereDirectionHemisphere n y ∧
          (v : FinRealEuclideanSpace n) =
            finRealSpherePolarizationInverseDirectionAmbient y x ∧
          finRealSpherePolarizationParam ρ y v = x

/-- The explicit inverse direction closes the inverse-formula ingredient for
the canonical real-sphere reflection map. -/
theorem finRealSphereReflectionMap_inverse_formula
    (n : ℕ) :
    FinRealSpherePolarizationInverseFormula (finRealSphereReflectionMap n) := by
  intro y x hxy
  have hxyAmbient :
      (x : FinRealEuclideanSpace n) ≠ (y : FinRealEuclideanSpace n) := by
    intro h
    exact hxy (Subtype.ext h)
  let v : FinRealSphere n :=
    ⟨SphericalPolarization.GeometricKernel.polarizationInverseDirection
        (y : FinRealEuclideanSpace n) (x : FinRealEuclideanSpace n), by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
      exact
        SphericalPolarization.GeometricKernel.polarizationInverseDirection_norm_eq_one
          hxyAmbient⟩
  refine ⟨v, ?_, ?_, ?_⟩
  · exact
      SphericalPolarization.GeometricKernel.inner_unit_polarizationInverseDirection_pos
          (finRealSphere_norm_coe n y)
          (finRealSphere_norm_coe n x)
          hxyAmbient
  · rfl
  · apply Subtype.ext
    exact
      SphericalPolarization.GeometricKernel.reflection_polarizationInverseDirection_eq
          (finRealSphere_norm_coe n y)
          (finRealSphere_norm_coe n x)
          hxyAmbient

/-- Admissible positive directions are sent by the canonical parametrization
to the height-lower side of the target fibre. -/
theorem finRealSpherePolarizationParam_height_le_of_mem
    (n : ℕ) (p y v : FinRealSphere n)
    (hvDir : v ∈ finRealSphereDirectionHemisphere n y)
    (hvAdm : v ∈ finRealSphereAdmissibleHemisphere n p) :
    finRealSphereHeight n p
        (finRealSpherePolarizationParam (finRealSphereReflectionMap n) y v) ≤
      finRealSphereHeight n p y := by
  have h := SphericalPolarization.GeometricKernel.height_reflection_le_height
    (p := (p : FinRealEuclideanSpace n))
    (v := (v : FinRealEuclideanSpace n))
    (y := (y : FinRealEuclideanSpace n))
    (hy := by
      simpa [SphericalPolarization.GeometricKernel.halfSpace,
        finRealSphereDirectionHemisphere] using le_of_lt hvDir)
    (hv := by
      simpa [SphericalPolarization.GeometricKernel.admissibleDirections,
        finRealSphereAdmissibleHemisphere, real_inner_comm] using hvAdm)
  simpa [finRealSphereHeight, finRealSpherePolarizationParam,
    finRealSphereReflectionMap_map_coe,
    SphericalPolarization.GeometricKernel.height,
    SphericalPolarization.GeometricKernel.reflection] using h

/-- For the explicit inverse direction `v=(y-x)/‖y-x‖`, admissibility is
exactly the target height inequality. -/
theorem finRealSpherePolarizationInverseDirectionAmbient_admissible_iff_height_le
    (n : ℕ) (p y x v : FinRealSphere n) (hxy : x ≠ y)
    (hv : (v : FinRealEuclideanSpace n) =
      finRealSpherePolarizationInverseDirectionAmbient y x) :
    v ∈ finRealSphereAdmissibleHemisphere n p ↔
      finRealSphereHeight n p x ≤ finRealSphereHeight n p y := by
  have hxyAmbient :
      (x : FinRealEuclideanSpace n) ≠ (y : FinRealEuclideanSpace n) := by
    intro h
    exact hxy (Subtype.ext h)
  have hnorm_pos :
      0 < ‖(y : FinRealEuclideanSpace n) -
        (x : FinRealEuclideanSpace n)‖ := by
    exact norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hxyAmbient))
  have hinv_pos :
      0 < (‖(y : FinRealEuclideanSpace n) -
        (x : FinRealEuclideanSpace n)‖)⁻¹ := by
    positivity
  constructor
  · intro hvAdm
    have hvle :
        ⟪(p : FinRealEuclideanSpace n),
            (x : FinRealEuclideanSpace n)⟫_ℝ *
            (‖(y : FinRealEuclideanSpace n) -
              (x : FinRealEuclideanSpace n)‖)⁻¹ ≤
          ⟪(p : FinRealEuclideanSpace n),
            (y : FinRealEuclideanSpace n)⟫_ℝ *
            (‖(y : FinRealEuclideanSpace n) -
              (x : FinRealEuclideanSpace n)‖)⁻¹ := by
      change 0 ≤
        ⟪(p : FinRealEuclideanSpace n),
          (v : FinRealEuclideanSpace n)⟫_ℝ at hvAdm
      rw [hv] at hvAdm
      rw [finRealSpherePolarizationInverseDirectionAmbient] at hvAdm
      simpa [real_inner_smul_right, inner_add_right, inner_neg_right,
        inner_sub_right, sub_eq_add_neg, real_inner_comm, mul_comm,
        mul_left_comm, mul_assoc] using hvAdm
    have hheight :
        ⟪(p : FinRealEuclideanSpace n),
          (x : FinRealEuclideanSpace n)⟫_ℝ ≤
          ⟪(p : FinRealEuclideanSpace n),
            (y : FinRealEuclideanSpace n)⟫_ℝ :=
      (mul_le_mul_iff_of_pos_right hinv_pos).mp hvle
    simpa [finRealSphereHeight, real_inner_comm] using hheight
  · intro hle
    have hheight :
        ⟪(p : FinRealEuclideanSpace n),
          (x : FinRealEuclideanSpace n)⟫_ℝ ≤
          ⟪(p : FinRealEuclideanSpace n),
            (y : FinRealEuclideanSpace n)⟫_ℝ := by
      simpa [finRealSphereHeight, real_inner_comm] using hle
    have hvle :
        ⟪(p : FinRealEuclideanSpace n),
            (x : FinRealEuclideanSpace n)⟫_ℝ *
            (‖(y : FinRealEuclideanSpace n) -
              (x : FinRealEuclideanSpace n)‖)⁻¹ ≤
          ⟪(p : FinRealEuclideanSpace n),
            (y : FinRealEuclideanSpace n)⟫_ℝ *
            (‖(y : FinRealEuclideanSpace n) -
              (x : FinRealEuclideanSpace n)‖)⁻¹ :=
      (mul_le_mul_iff_of_pos_right hinv_pos).mpr hheight
    change 0 ≤
      ⟪(p : FinRealEuclideanSpace n),
        (v : FinRealEuclideanSpace n)⟫_ℝ
    rw [hv]
    rw [finRealSpherePolarizationInverseDirectionAmbient]
    simpa [real_inner_smul_right, inner_add_right, inner_neg_right,
      inner_sub_right, sub_eq_add_neg, real_inner_comm, mul_comm,
      mul_left_comm, mul_assoc] using hvle

/-- The canonical parametrization sends the admissible positive directions
onto exactly the height-lower side of the fibre, except for the excluded
diagonal point `y`. -/
theorem finRealSpherePolarizationParam_image_admissible_direction_eq_heightSublevel_diff_singleton
    (n : ℕ) (p y : FinRealSphere n) :
    (finRealSpherePolarizationParam (finRealSphereReflectionMap n) y) ''
        (finRealSphereAdmissibleHemisphere n p ∩
          finRealSphereDirectionHemisphere n y) =
      {x : FinRealSphere n |
        finRealSphereHeight n p x ≤ finRealSphereHeight n p y} \ {y} := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨v, hv, rfl⟩
    constructor
    · exact finRealSpherePolarizationParam_height_le_of_mem n p y v hv.2 hv.1
    · intro hxy
      have hambient :
          SphericalPolarization.GeometricKernel.reflection
              (v : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n) =
            (y : FinRealEuclideanSpace n) := by
        simpa [finRealSpherePolarizationParam,
          finRealSphereReflectionMap_map_coe,
          SphericalPolarization.GeometricKernel.reflection] using
          congrArg Subtype.val hxy
      have hne :=
        SphericalPolarization.GeometricKernel.reflection_ne_self_of_unit_pos
          (y := (y : FinRealEuclideanSpace n))
          (v := (v : FinRealEuclideanSpace n))
          (finRealSphere_norm_coe n y)
          (finRealSphere_norm_coe n v)
          hv.2
      exact hne hambient
  · intro hx
    rcases hx with ⟨hheight, hne⟩
    rcases finRealSphereReflectionMap_inverse_formula n y x hne with
      ⟨v, hvDir, hvEq, hvMap⟩
    refine ⟨v, ?_, hvMap⟩
    constructor
    · exact
        (finRealSpherePolarizationInverseDirectionAmbient_admissible_iff_height_le
          n p y x v hne hvEq).2 hheight
    · exact hvDir

/-- The positive direction hemisphere is measurable. -/
theorem measurableSet_finRealSphereDirectionHemisphere
    (n : ℕ) (y : FinRealSphere n) :
    MeasurableSet (finRealSphereDirectionHemisphere n y) := by
  unfold finRealSphereDirectionHemisphere
  have h : Measurable (fun v : FinRealSphere n =>
      ⟪(y : FinRealEuclideanSpace n),
        (v : FinRealEuclideanSpace n)⟫_ℝ) := by
    fun_prop
  exact measurableSet_lt measurable_const h

/-- The admissible closed hemisphere is measurable. -/
theorem measurableSet_finRealSphereAdmissibleHemisphere
    (n : ℕ) (p : FinRealSphere n) :
    MeasurableSet (finRealSphereAdmissibleHemisphere n p) := by
  unfold finRealSphereAdmissibleHemisphere
  have h : Measurable (fun v : FinRealSphere n =>
      ⟪(p : FinRealEuclideanSpace n),
        (v : FinRealEuclideanSpace n)⟫_ℝ) := by
    fun_prop
  exact measurableSet_le measurable_const h

/-- The source domain of one polarization fibre is measurable. -/
theorem measurableSet_finRealSphereAdmissibleDirectionDomain
    (n : ℕ) (p y : FinRealSphere n) :
    MeasurableSet (finRealSphereAdmissibleHemisphere n p ∩
      finRealSphereDirectionHemisphere n y) :=
  (measurableSet_finRealSphereAdmissibleHemisphere n p).inter
    (measurableSet_finRealSphereDirectionHemisphere n y)

/-- The target height sublevel set of one polarization fibre is measurable. -/
theorem measurableSet_finRealSphereHeightSublevel
    (n : ℕ) (p y : FinRealSphere n) :
    MeasurableSet {x : FinRealSphere n |
      finRealSphereHeight n p x ≤ finRealSphereHeight n p y} := by
  have hheight : Measurable (fun x : FinRealSphere n =>
      finRealSphereHeight n p x) := by
    unfold finRealSphereHeight
    fun_prop
  exact measurableSet_le hheight measurable_const

/-- The punctured target height sublevel set of one polarization fibre is
measurable. -/
theorem measurableSet_finRealSphereHeightSublevel_diff_singleton
    (n : ℕ) (p y : FinRealSphere n) :
    MeasurableSet ({x : FinRealSphere n |
      finRealSphereHeight n p x ≤ finRealSphereHeight n p y} \ {y}) :=
  (measurableSet_finRealSphereHeightSublevel n p y).diff
    (measurableSet_singleton y)

/-- The canonical parametrization is a bijection from the admissible positive
directions onto the punctured target height sublevel. -/
theorem finRealSpherePolarizationParam_bijOn_admissible_direction_heightSublevel_diff_singleton
    (n : ℕ) (p y : FinRealSphere n) :
    BijOn
      (finRealSpherePolarizationParam (finRealSphereReflectionMap n) y)
      (finRealSphereAdmissibleHemisphere n p ∩
        finRealSphereDirectionHemisphere n y)
      ({x : FinRealSphere n |
        finRealSphereHeight n p x ≤ finRealSphereHeight n p y} \ {y}) := by
  refine ⟨?maps, ?inj, ?surj⟩
  · intro v hv
    rw [←
      finRealSpherePolarizationParam_image_admissible_direction_eq_heightSublevel_diff_singleton
        n p y]
    exact ⟨v, hv, rfl⟩
  · exact (finRealSphereReflectionMap_param_injOn n y).mono
      inter_subset_right
  · intro x hx
    rw [←
      finRealSpherePolarizationParam_image_admissible_direction_eq_heightSublevel_diff_singleton
        n p y] at hx
    exact hx

/-- Ambient derivative formula for `w ↦ y - 2⟪y,w⟫w`, the polynomial
representative of `v ↦ rho_v(y)` in ambient coordinates. -/
def FinRealSpherePolarizationAmbientDerivativeFormula
    {n : ℕ} (_ρ : FinRealSphereReflectionMap n) : Prop :=
  ∀ y v : FinRealSphere n,
    v ∈ finRealSphereDirectionHemisphere n y →
      ∃ L : FinRealEuclideanSpace n →L[ℝ] FinRealEuclideanSpace n,
        HasFDerivWithinAt
          (fun w : FinRealEuclideanSpace n =>
            (y : FinRealEuclideanSpace n) -
              (((2 : ℝ) *
                ⟪(y : FinRealEuclideanSpace n), w⟫_ℝ) • w))
          L
          (Metric.sphere (0 : FinRealEuclideanSpace n) 1 ∩
            {w | 0 < ⟪(y : FinRealEuclideanSpace n), w⟫_ℝ})
          (v : FinRealEuclideanSpace n)
        ∧
        ∀ h : FinRealEuclideanSpace n,
          L h =
            -(((2 : ℝ) *
              ⟪(y : FinRealEuclideanSpace n), h⟫_ℝ) •
              (v : FinRealEuclideanSpace n)) -
            (((2 : ℝ) *
              ⟪(y : FinRealEuclideanSpace n),
                (v : FinRealEuclideanSpace n)⟫_ℝ) • h)

/-- The ambient Fréchet derivative ingredient for the canonical real-sphere
reflection map. -/
theorem finRealSphereReflectionMap_ambient_derivative_formula
    (n : ℕ) :
    FinRealSpherePolarizationAmbientDerivativeFormula
      (finRealSphereReflectionMap n) := by
  intro y v _hv
  refine
    ⟨SphericalPolarization.GeometricKernel.reflectionFDeriv
        (y : FinRealEuclideanSpace n) (v : FinRealEuclideanSpace n),
      ?_, ?_⟩
  · simpa [SphericalPolarization.GeometricKernel.reflection] using
      SphericalPolarization.GeometricKernel.hasFDerivWithinAt_reflection
        (y := (y : FinRealEuclideanSpace n))
        (v := (v : FinRealEuclideanSpace n))
        (s := Metric.sphere (0 : FinRealEuclideanSpace n) 1 ∩
          {w : FinRealEuclideanSpace n |
            0 < ⟪(y : FinRealEuclideanSpace n), w⟫_ℝ})
  · intro h
    simpa [sub_eq_add_neg, neg_add, add_comm, add_left_comm, add_assoc] using
      SphericalPolarization.GeometricKernel.reflectionFDeriv_apply
        (y : FinRealEuclideanSpace n) (v : FinRealEuclideanSpace n) h

/-- Canonical one-parameter push-forward kernel statement for the project
sphere and normalized surface probability measure. -/
def FinRealSpherePolarizationPushforwardKernelFormula
    {n : ℕ} (ρ : FinRealSphereReflectionMap n) : Prop :=
  ∀ p y : FinRealSphere n,
    (2 : ℝ≥0∞) •
      (((finRealSurfaceProbabilityMeasure n).restrict
        (finRealSphereAdmissibleHemisphere n p ∩
          finRealSphereDirectionHemisphere n y)).map
        (finRealSpherePolarizationParam ρ y))
      =
    (finRealSurfaceProbabilityMeasure n).withDensity
      (fun x : FinRealSphere n =>
        if finRealSphereHeight n p x ≤ finRealSphereHeight n p y then
          finRealSpherePolarizationKernel n x y
        else
          0)

/-- Nonnegative-integral form of the concrete fibre push-forward theorem.
Surface-coordinate change-of-variables on the concrete reflection map (proved
in `SphericalPolarizationPushforwardTransport.lean`). -/
def FinRealSpherePolarizationPushforwardLIntegralFormula
    {n : ℕ} (ρ : FinRealSphereReflectionMap n) : Prop :=
  ∀ p y : FinRealSphere n,
    ∀ F : FinRealSphere n → ℝ≥0∞,
      Measurable F →
        (∫⁻ v in finRealSphereAdmissibleHemisphere n p ∩
              finRealSphereDirectionHemisphere n y,
            (2 : ℝ≥0∞) *
              F (finRealSpherePolarizationParam ρ y v)
          ∂(finRealSurfaceProbabilityMeasure n))
        =
        (∫⁻ x : FinRealSphere n,
            F x *
              (if finRealSphereHeight n p x ≤ finRealSphereHeight n p y then
                finRealSpherePolarizationKernel n x y
              else
                0)
          ∂(finRealSurfaceProbabilityMeasure n))

/-- The fibrewise nonnegative-integral formula is equivalent to the
measure-level `withDensity` push-forward endpoint. -/
theorem finRealSpherePolarizationPushforwardKernelFormula_of_lintegral
    {n : ℕ} {ρ : FinRealSphereReflectionMap n}
    (hMeas :
      ∀ y : FinRealSphere n,
        Measurable (finRealSpherePolarizationParam ρ y))
    (h :
      FinRealSpherePolarizationPushforwardLIntegralFormula ρ) :
    FinRealSpherePolarizationPushforwardKernelFormula ρ := by
  intro p y
  ext s hs
  let μ := finRealSurfaceProbabilityMeasure n
  let domain : Set (FinRealSphere n) :=
    finRealSphereAdmissibleHemisphere n p ∩
      finRealSphereDirectionHemisphere n y
  let φ : FinRealSphere n → FinRealSphere n :=
    finRealSpherePolarizationParam ρ y
  let g : FinRealSphere n → ℝ≥0∞ :=
    fun x =>
      if finRealSphereHeight n p x ≤ finRealSphereHeight n p y then
        finRealSpherePolarizationKernel n x y
      else
        0
  have hF :
      Measurable (s.indicator
        (fun _ : FinRealSphere n => (1 : ℝ≥0∞))) :=
    Measurable.indicator measurable_const hs
  have hmain :=
    h p y (s.indicator
      (fun _ : FinRealSphere n => (1 : ℝ≥0∞))) hF
  change
    ((2 : ℝ≥0∞) •
        (Measure.map φ (μ.restrict domain))) s =
      (μ.withDensity g) s
  have hφ : Measurable φ := hMeas y
  have hpre : MeasurableSet (φ ⁻¹' s) := hs.preimage hφ
  have hleft_measure :
      ((2 : ℝ≥0∞) •
          (Measure.map φ (μ.restrict domain))) s =
        (2 : ℝ≥0∞) * μ ((φ ⁻¹' s) ∩ domain) := by
    rw [Measure.smul_apply]
    rw [Measure.map_apply hφ hs]
    rw [Measure.restrict_apply hpre]
    rfl
  have hleft_integral :
      (∫⁻ v in domain,
          (2 : ℝ≥0∞) *
            s.indicator (fun _ => (1 : ℝ≥0∞)) (φ v) ∂μ)
        =
      (2 : ℝ≥0∞) * μ ((φ ⁻¹' s) ∩ domain) := by
    calc
      (∫⁻ v in domain,
          (2 : ℝ≥0∞) *
            s.indicator (fun _ => (1 : ℝ≥0∞)) (φ v) ∂μ)
          =
        ∫⁻ v,
          s.indicator (fun _ => (2 : ℝ≥0∞)) (φ v)
            ∂(μ.restrict domain) := by
          apply lintegral_congr_ae
          filter_upwards with v
          by_cases hv : φ v ∈ s <;> simp [Set.indicator, hv]
      _ =
        (2 : ℝ≥0∞) * (μ.restrict domain) (φ ⁻¹' s) := by
          rw [lintegral_indicator_const_comp hφ hs (2 : ℝ≥0∞)]
      _ =
        (2 : ℝ≥0∞) * μ ((φ ⁻¹' s) ∩ domain) := by
          rw [Measure.restrict_apply hpre]
  have hright_measure :
      (μ.withDensity g) s =
        ∫⁻ x : FinRealSphere n,
          s.indicator (fun _ => (1 : ℝ≥0∞)) x * g x ∂μ := by
    rw [withDensity_apply g hs]
    rw [← lintegral_indicator hs]
    apply lintegral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ s <;> simp [Set.indicator, hx]
  rw [hleft_measure, ← hleft_integral, hmain, hright_measure]

/-- The concrete kernel is measurable in its first argument. -/
theorem measurable_finRealSpherePolarizationKernel_right
    (n : ℕ) (y : FinRealSphere n) :
    Measurable (fun x : FinRealSphere n =>
      finRealSpherePolarizationKernel n x y) := by
  unfold finRealSpherePolarizationKernel
  unfold SphericalPolarization.GeometricKernel.sphericalKernelChordalENNReal
  apply Measurable.ennreal_ofReal
  unfold SphericalPolarization.GeometricKernel.sphericalKernelChordal
  exact Measurable.ite
    ((isClosed_eq continuous_subtype_val continuous_const).measurableSet)
    measurable_const
    (by
      apply Measurable.mul measurable_const
      apply Measurable.inv
      apply Measurable.pow_const
      unfold SphericalPolarization.GeometricKernel.chordalHalf
      fun_prop)

/-- The measure-level `withDensity` push-forward endpoint implies the
fibrewise nonnegative-integral formula. -/
theorem finRealSpherePolarizationPushforwardLIntegralFormula_of_kernelFormula
    {n : ℕ} {ρ : FinRealSphereReflectionMap n}
    (hMeas :
      ∀ y : FinRealSphere n,
        Measurable (finRealSpherePolarizationParam ρ y))
    (h :
      FinRealSpherePolarizationPushforwardKernelFormula ρ) :
    FinRealSpherePolarizationPushforwardLIntegralFormula ρ := by
  intro p y F hF
  let μ := finRealSurfaceProbabilityMeasure n
  let domain : Set (FinRealSphere n) :=
    finRealSphereAdmissibleHemisphere n p ∩
      finRealSphereDirectionHemisphere n y
  let φ : FinRealSphere n → FinRealSphere n :=
    finRealSpherePolarizationParam ρ y
  let g : FinRealSphere n → ℝ≥0∞ :=
    fun x =>
      if finRealSphereHeight n p x ≤ finRealSphereHeight n p y then
        finRealSpherePolarizationKernel n x y
      else
        0
  have hφ : Measurable φ := hMeas y
  have hkernel :
      (2 : ℝ≥0∞) • (Measure.map φ (μ.restrict domain)) =
        μ.withDensity g := by
    simpa [μ, domain, φ, g] using h p y
  have hleft :
      (∫⁻ v in domain, (2 : ℝ≥0∞) * F (φ v) ∂μ) =
        ∫⁻ x, F x ∂((2 : ℝ≥0∞) •
          (Measure.map φ (μ.restrict domain))) := by
    rw [lintegral_smul_measure]
    rw [lintegral_map hF hφ]
    rw [lintegral_const_mul']
    · rfl
    · norm_num
  have hright :
      (∫⁻ x, F x ∂(μ.withDensity g)) =
        ∫⁻ x, F x * g x ∂μ := by
    rw [lintegral_withDensity_eq_lintegral_mul _ ?_ hF]
    · apply lintegral_congr_ae
      filter_upwards with x
      simp [mul_comm]
    · unfold g
      refine Measurable.ite ?_
        (measurable_finRealSpherePolarizationKernel_right n y)
        measurable_const
      have hheight :
          Measurable (fun x : FinRealSphere n =>
            finRealSphereHeight n p x) := by
        unfold finRealSphereHeight
        fun_prop
      exact measurableSet_le hheight measurable_const
  calc
    (∫⁻ v in domain, (2 : ℝ≥0∞) * F (φ v) ∂μ)
        = ∫⁻ x, F x ∂((2 : ℝ≥0∞) •
          (Measure.map φ (μ.restrict domain))) := hleft
    _ = ∫⁻ x, F x ∂(μ.withDensity g) := by rw [hkernel]
    _ = ∫⁻ x, F x * g x ∂μ := hright

/-- Concrete specialization of the integral-to-`withDensity` bridge to the
canonical real-sphere reflection map. -/
theorem finRealSphereReflectionMap_pushforward_withDensity_of_lintegral
    (n : ℕ)
    (h :
      FinRealSpherePolarizationPushforwardLIntegralFormula
        (finRealSphereReflectionMap n)) :
    FinRealSpherePolarizationPushforwardKernelFormula
      (finRealSphereReflectionMap n) :=
  finRealSpherePolarizationPushforwardKernelFormula_of_lintegral
    (finRealSphereReflectionMap_param_measurable n) h

/-- Concrete specialization of the `withDensity`-to-integral bridge to the
canonical real-sphere reflection map. -/
theorem finRealSphereReflectionMap_lintegral_of_pushforward_withDensity
    (n : ℕ)
    (h :
      FinRealSpherePolarizationPushforwardKernelFormula
        (finRealSphereReflectionMap n)) :
    FinRealSpherePolarizationPushforwardLIntegralFormula
      (finRealSphereReflectionMap n) :=
  finRealSpherePolarizationPushforwardLIntegralFormula_of_kernelFormula
    (finRealSphereReflectionMap_param_measurable n) h

/-- For the canonical real-sphere reflection map, the measure-level
`withDensity` endpoint and the fibrewise nonnegative-integral endpoint are
equivalent. -/
theorem finRealSphereReflectionMap_pushforwardKernelFormula_iff_lintegralFormula
    (n : ℕ) :
    FinRealSpherePolarizationPushforwardKernelFormula
        (finRealSphereReflectionMap n) ↔
      FinRealSpherePolarizationPushforwardLIntegralFormula
        (finRealSphereReflectionMap n) := by
  constructor
  · exact finRealSphereReflectionMap_lintegral_of_pushforward_withDensity n
  · exact finRealSphereReflectionMap_pushforward_withDensity_of_lintegral n

/-- Null-boundary facts needed to move between open/closed hemisphere choices,
ignore the diagonal, and replace strict height inequalities by non-strict ones
in the downstream polarization identities. -/
structure FinRealSpherePolarizationNullBoundaries
    (n : ℕ) : Prop where
  direction_boundary_null :
    ∀ y : FinRealSphere n,
      (finRealSurfaceProbabilityMeasure n)
        {v : FinRealSphere n |
          ⟪(y : FinRealEuclideanSpace n),
            (v : FinRealEuclideanSpace n)⟫_ℝ = 0} = 0
  admissible_boundary_null :
    ∀ p : FinRealSphere n,
      (finRealSurfaceProbabilityMeasure n)
        {v : FinRealSphere n |
          ⟪(p : FinRealEuclideanSpace n),
            (v : FinRealEuclideanSpace n)⟫_ℝ = 0} = 0
  diagonal_null :
    ((finRealSurfaceProbabilityMeasure n).prod
      (finRealSurfaceProbabilityMeasure n))
        {z : FinRealSphere n × FinRealSphere n | z.1 = z.2} = 0
  tie_level_null :
    ∀ p : FinRealSphere n,
      ((finRealSurfaceProbabilityMeasure n).prod
        (finRealSurfaceProbabilityMeasure n))
          {z : FinRealSphere n × FinRealSphere n |
            finRealSphereHeight n p z.1 =
              finRealSphereHeight n p z.2} = 0

/-- Concrete theorem package for the polarization Jacobian block (closed for
the canonical reflection map via push-forward transport).

The exported mathematical target is the push-forward density.  The ambient
derivative, inverse formula, injectivity, and null-boundary fields are kept
visible because they are the intended proof ingredients, not hidden axioms. -/
structure FinRealSpherePolarizationJacobianTarget
    {n : ℕ} (ρ : FinRealSphereReflectionMap n) : Prop where
  hn2 : 2 ≤ n
  param_measurable :
    ∀ y : FinRealSphere n,
      Measurable (finRealSpherePolarizationParam ρ y)
  param_injOn :
    ∀ y : FinRealSphere n,
      InjOn (finRealSpherePolarizationParam ρ y)
        (finRealSphereDirectionHemisphere n y)
  inverse_formula :
    FinRealSpherePolarizationInverseFormula ρ
  ambient_derivative :
    FinRealSpherePolarizationAmbientDerivativeFormula ρ
  null_boundaries :
    FinRealSpherePolarizationNullBoundaries n
  pushforward_kernel :
    FinRealSpherePolarizationPushforwardKernelFormula ρ

/-- The remaining null-boundary package is completely determined by the
product-null height-tie statement.  All other boundary fields are supplied
above from the real-sphere surface law. -/
theorem finRealSpherePolarizationNullBoundaries_of_tieLevel
    (n : ℕ) (hn : 2 ≤ n)
    (hTie :
      ∀ p : FinRealSphere n,
        ((finRealSurfaceProbabilityMeasure n).prod
          (finRealSurfaceProbabilityMeasure n))
            {z : FinRealSphere n × FinRealSphere n |
              finRealSphereHeight n p z.1 =
                finRealSphereHeight n p z.2} = 0) :
    FinRealSpherePolarizationNullBoundaries n where
  direction_boundary_null :=
    finRealSphere_direction_boundary_null n
  admissible_boundary_null :=
    finRealSphere_admissible_boundary_null n
  diagonal_null :=
    finRealSphere_diagonal_null n hn
  tie_level_null :=
    hTie

/-- Null-boundary package supplied from the sharper one-dimensional
height-distribution atomlessness input. -/
theorem finRealSpherePolarizationNullBoundaries_of_heightDistributionAtomless
    (n : ℕ) (hn : 2 ≤ n)
    (hAtomless : FinRealSphereHeightDistributionAtomless n) :
    FinRealSpherePolarizationNullBoundaries n :=
  finRealSpherePolarizationNullBoundaries_of_tieLevel n hn
    (finRealSphere_tie_level_null_of_heightDistributionAtomless n hAtomless)

/-- Concrete product-null height tie theorem for the real-sphere surface law. -/
theorem finRealSphere_tie_level_null
    (n : ℕ) (hn : 2 ≤ n) (p : FinRealSphere n) :
    ((finRealSurfaceProbabilityMeasure n).prod
      (finRealSurfaceProbabilityMeasure n))
        {z : FinRealSphere n × FinRealSphere n |
          finRealSphereHeight n p z.1 =
            finRealSphereHeight n p z.2} = 0 :=
  finRealSphere_tie_level_null_of_heightDistributionAtomless n
    (finRealSphereHeightDistributionAtomless_concrete n hn) p

/-- Concrete null-boundary package for the real-sphere surface law. -/
theorem finRealSpherePolarizationNullBoundaries_concrete
    (n : ℕ) (hn : 2 ≤ n) :
    FinRealSpherePolarizationNullBoundaries n :=
  finRealSpherePolarizationNullBoundaries_of_tieLevel n hn
    (finRealSphere_tie_level_null n hn)

/-- Canonical closure constructor for the concrete real-sphere reflection
target.  This compatibility endpoint keeps the product-null height-tie
statement visible, even though the concrete supplier
`finRealSphere_tie_level_null` below closes it for the canonical sphere. -/
theorem finRealSphereReflectionMap_jacobianTarget_of_tieLevel_and_pushforward
    (n : ℕ) (hn : 2 ≤ n)
    (hTie :
      ∀ p : FinRealSphere n,
        ((finRealSurfaceProbabilityMeasure n).prod
          (finRealSurfaceProbabilityMeasure n))
            {z : FinRealSphere n × FinRealSphere n |
              finRealSphereHeight n p z.1 =
                finRealSphereHeight n p z.2} = 0)
    (hPush :
      FinRealSpherePolarizationPushforwardKernelFormula
        (finRealSphereReflectionMap n)) :
    FinRealSpherePolarizationJacobianTarget
      (finRealSphereReflectionMap n) where
  hn2 := hn
  param_measurable :=
    finRealSphereReflectionMap_param_measurable n
  param_injOn :=
    finRealSphereReflectionMap_param_injOn n
  inverse_formula :=
    finRealSphereReflectionMap_inverse_formula n
  ambient_derivative :=
    finRealSphereReflectionMap_ambient_derivative_formula n
  null_boundaries :=
    finRealSpherePolarizationNullBoundaries_of_tieLevel n hn hTie
  pushforward_kernel :=
    hPush

/-- Compatibility constructor using the fibrewise integral form of the
surface-coordinate theorem and an externally supplied height-tie statement. -/
theorem finRealSphereReflectionMap_jacobianTarget_of_tieLevel_and_lintegral
    (n : ℕ) (hn : 2 ≤ n)
    (hTie :
      ∀ p : FinRealSphere n,
        ((finRealSurfaceProbabilityMeasure n).prod
          (finRealSurfaceProbabilityMeasure n))
            {z : FinRealSphere n × FinRealSphere n |
              finRealSphereHeight n p z.1 =
                finRealSphereHeight n p z.2} = 0)
    (hIntegral :
      FinRealSpherePolarizationPushforwardLIntegralFormula
        (finRealSphereReflectionMap n)) :
    FinRealSpherePolarizationJacobianTarget
      (finRealSphereReflectionMap n) :=
  finRealSphereReflectionMap_jacobianTarget_of_tieLevel_and_pushforward
    n hn hTie
    (finRealSphereReflectionMap_pushforward_withDensity_of_lintegral
      n hIntegral)

/-- Canonical closure constructor using the sharper scalar atomlessness input
for height distributions, together with the measure-level push-forward
formula. -/
theorem finRealSphereReflectionMap_jacobianTarget_of_heightAtomless_and_pushforward
    (n : ℕ) (hn : 2 ≤ n)
    (hAtomless : FinRealSphereHeightDistributionAtomless n)
    (hPush :
      FinRealSpherePolarizationPushforwardKernelFormula
        (finRealSphereReflectionMap n)) :
    FinRealSpherePolarizationJacobianTarget
      (finRealSphereReflectionMap n) :=
  finRealSphereReflectionMap_jacobianTarget_of_tieLevel_and_pushforward
    n hn
    (finRealSphere_tie_level_null_of_heightDistributionAtomless n hAtomless)
    hPush

/-- Canonical closure constructor using the sharper scalar atomlessness input
for height distributions and the fibrewise nonnegative-integral form of the
push-forward theorem. -/
theorem finRealSphereReflectionMap_jacobianTarget_of_heightAtomless_and_lintegral
    (n : ℕ) (hn : 2 ≤ n)
    (hAtomless : FinRealSphereHeightDistributionAtomless n)
    (hIntegral :
      FinRealSpherePolarizationPushforwardLIntegralFormula
        (finRealSphereReflectionMap n)) :
    FinRealSpherePolarizationJacobianTarget
      (finRealSphereReflectionMap n) :=
  finRealSphereReflectionMap_jacobianTarget_of_tieLevel_and_lintegral
    n hn
    (finRealSphere_tie_level_null_of_heightDistributionAtomless n hAtomless)
    hIntegral

/-- Canonical closure constructor for the concrete real-sphere reflection
target.  The height-null and boundary obligations are proved in this file; the
only remaining theorem-strength input is the measure-level push-forward kernel
formula. -/
theorem finRealSphereReflectionMap_jacobianTarget_of_pushforward
    (n : ℕ) (hn : 2 ≤ n)
    (hPush :
      FinRealSpherePolarizationPushforwardKernelFormula
        (finRealSphereReflectionMap n)) :
    FinRealSpherePolarizationJacobianTarget
      (finRealSphereReflectionMap n) :=
  finRealSphereReflectionMap_jacobianTarget_of_tieLevel_and_pushforward
    n hn (finRealSphere_tie_level_null n hn) hPush

/-- Canonical closure constructor using the fibrewise nonnegative-integral
form of the remaining push-forward theorem.  This is now the cleanest
conditional endpoint for the concrete real-sphere Jacobian target. -/
theorem finRealSphereReflectionMap_jacobianTarget_of_lintegral
    (n : ℕ) (hn : 2 ≤ n)
    (hIntegral :
      FinRealSpherePolarizationPushforwardLIntegralFormula
        (finRealSphereReflectionMap n)) :
    FinRealSpherePolarizationJacobianTarget
      (finRealSphereReflectionMap n) :=
  finRealSphereReflectionMap_jacobianTarget_of_tieLevel_and_lintegral
    n hn (finRealSphere_tie_level_null n hn) hIntegral

end AppendixB
end PptFactorization
