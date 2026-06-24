import PptFactorization.AppendixBSurfaceMeasure
import PptFactorization.SphericalPolarizationJacobianTargets
import PptFactorization.PolarizationLemma43MeasureTrimming
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Real-sphere isoperimetry: first proved supplier

Sorry-free suppliers on the hemisphere-tail ladder in
`AppendixBSurfaceMeasure.lean`:

* `sphere_hemisphereLargeRadiusTail_surface`;
* `sphere_hemisphereComplementCoordinateDominance_surface`;
* `sphere_halfMeasure_hemisphereComparison_of_geTwo`;
* `sphere_coordinateGaussianTailInterior_of_geTwo`;
* `sphere_coordinateGaussianTail_of_interior`.

Still open on the same ladder:

* `sphere_coordinateGaussianTailInteriorGeTwo`;
* `sphere_halfMeasure_hemisphereComparisonGeTwo`.
-/

noncomputable section

open PptFactorization.AppendixB
open MeasureTheory Set InnerProductSpace Filter
open scoped ENNReal EuclideanSpace symmDiff

namespace PptFactorization
namespace AppendixB

variable {p q σ : Type*}
variable [Fintype p] [Fintype q] [Fintype σ]
variable [DecidableEq p] [DecidableEq q]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Antipodal point on the concrete real unit sphere. -/
noncomputable def finRealSphere_neg (n : ℕ) (c : FinRealSphere n) : FinRealSphere n :=
  ⟨- (c : FinRealEuclideanSpace n), by
    simpa [dist_eq_norm, sub_zero] using congrArg norm c.2⟩

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
theorem finRealSphere_coe_norm_eq_one (n : ℕ) (x : FinRealSphere n) :
    ‖(x : FinRealEuclideanSpace n)‖ = 1 := by
  have hx : dist (x : FinRealEuclideanSpace n) 0 = 1 := x.2
  rw [dist_eq_norm, sub_zero] at hx
  exact hx

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
theorem finRealSphere_inner_ge_neg_one (n : ℕ) (c : FinRealSphere n) (x : FinRealSphere n) :
    -1 ≤ finRealSphereInnerCoordinate n (c : FinRealEuclideanSpace n) x := by
  simp only [finRealSphereInnerCoordinate]
  have h :=
    abs_real_inner_le_norm
      (c : FinRealEuclideanSpace n) (x : FinRealEuclideanSpace n)
  rw [finRealSphere_coe_norm_eq_one n c, finRealSphere_coe_norm_eq_one n x] at h
  have hneg :
      - |inner ℝ (c : FinRealEuclideanSpace n) (x : FinRealEuclideanSpace n)| ≤
        inner ℝ (c : FinRealEuclideanSpace n) (x : FinRealEuclideanSpace n) :=
    neg_abs_le _
  linarith

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
theorem finRealSphere_inner_eq_neg_one_iff_eq_neg (n : ℕ) (c : FinRealSphere n)
    (x : FinRealSphere n) :
    finRealSphereInnerCoordinate n (c : FinRealEuclideanSpace n) x = -1 ↔
      x = finRealSphere_neg n c := by
  constructor
  · intro hcoord
    apply Subtype.ext
    have hc := finRealSphere_coe_norm_eq_one n c
    have hx := finRealSphere_coe_norm_eq_one n x
    have hinner :
        inner ℝ (c : FinRealEuclideanSpace n) (x : FinRealEuclideanSpace n) = -1 := by
      simpa [finRealSphereInnerCoordinate] using hcoord
    have hsum :
        ‖(c : FinRealEuclideanSpace n) + (x : FinRealEuclideanSpace n)‖ ^ 2 = 0 := by
      rw [norm_add_sq_real, hinner, hc, hx]
      norm_num
    have hzero : (c : FinRealEuclideanSpace n) + (x : FinRealEuclideanSpace n) = 0 :=
      norm_eq_zero.mp (eq_zero_of_pow_eq_zero hsum)
    exact (neg_eq_iff_add_eq_zero.mpr hzero).symm
  · intro hx
    subst hx
    simp [finRealSphere_neg, finRealSphereInnerCoordinate, inner_neg_right,
      finRealSphere_coe_norm_eq_one n c]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
theorem mem_finRealSphereClosedHemisphere_iff (n : ℕ)
    (e : FinRealEuclideanSpace n) (x : FinRealSphere n) :
    x ∈ finRealSphereClosedHemisphere n e ↔
      0 ≤ finRealSphereInnerCoordinate n e x := by
  simp [finRealSphereClosedHemisphere, finRealSphereClosedHalfspace]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
theorem finRealSphereGeodesicDistance_self (n : ℕ) (x : FinRealSphere n) :
    finRealSphereGeodesicDistance n x x = 0 := by
  unfold finRealSphereGeodesicDistance
  simp [dist_self, Real.arcsin_zero, mul_zero]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The project geodesic distance on the concrete real sphere is nonnegative. -/
theorem finRealSphereGeodesicDistance_nonneg
    (n : ℕ) (x y : FinRealSphere n) :
    0 ≤ finRealSphereGeodesicDistance n x y := by
  unfold finRealSphereGeodesicDistance
  have hhalf : 0 ≤ dist x y / 2 := by positivity
  have harc : 0 ≤ Real.arcsin (dist x y / 2) :=
    Real.arcsin_nonneg.mpr hhalf
  positivity

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The project geodesic distance on the concrete real sphere is at most `π`. -/
theorem finRealSphereGeodesicDistance_le_pi
    (n : ℕ) (x y : FinRealSphere n) :
    finRealSphereGeodesicDistance n x y ≤ Real.pi := by
  unfold finRealSphereGeodesicDistance
  have harc : Real.arcsin (dist x y / 2) ≤ Real.pi / 2 :=
    Real.arcsin_le_pi_div_two (dist x y / 2)
  linarith

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Orthogonal projection of `x` onto the equator `{⟪e,·⟫ = 0}`. -/
noncomputable def finRealSphere_equatorProjection (n : ℕ)
    (e : FinRealEuclideanSpace n) (x : FinRealSphere n) : FinRealEuclideanSpace n :=
  let t := finRealSphereInnerCoordinate n e x
  (Real.sqrt (1 - t ^ 2))⁻¹ • ((x : FinRealEuclideanSpace n) - t • e)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
theorem finRealSphere_equatorProjection_inner_eq_zero (n : ℕ)
    (e : FinRealEuclideanSpace n) (x : FinRealSphere n) :
    ‖e‖ = 1 →
    inner ℝ e (finRealSphere_equatorProjection n e x) = 0 := by
  intro he
  simp [finRealSphere_equatorProjection, finRealSphereInnerCoordinate,
    inner_smul_right, inner_sub_right, real_inner_self_eq_norm_sq, he]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
theorem finRealSphere_equatorProjection_norm_eq_one (n : ℕ)
    (e : FinRealEuclideanSpace n) (x : FinRealSphere n)
    (he : ‖e‖ = 1)
    (ht : finRealSphereInnerCoordinate n e x < 0)
    (ht' : -1 < finRealSphereInnerCoordinate n e x) :
    ‖finRealSphere_equatorProjection n e x‖ = 1 := by
  set t := finRealSphereInnerCoordinate n e x
  have hx := finRealSphere_coe_norm_eq_one n x
  have ht0 : t < 0 := by simpa [t] using ht
  have htneg : -1 < t := by simpa [t] using ht'
  have ht_sq : t ^ 2 < 1 := by nlinarith
  have hsq_pos : 0 < 1 - t ^ 2 := by nlinarith
  have hsqrt_pos : 0 < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.mpr hsq_pos
  have hinner_xt :
      inner ℝ (x : FinRealEuclideanSpace n) e = t := by
    simpa [t, finRealSphereInnerCoordinate, real_inner_comm]
  have hu_sq :
      ‖(x : FinRealEuclideanSpace n) - t • e‖ ^ 2 = 1 - t ^ 2 := by
    rw [norm_sub_sq_real, hx, norm_smul, he, real_inner_smul_right, hinner_xt]
    rw [Real.norm_eq_abs]
    ring_nf
    rw [sq_abs]
    linarith
  have hu_norm :
      ‖(x : FinRealEuclideanSpace n) - t • e‖ =
        Real.sqrt (1 - t ^ 2) := by
    apply (sq_eq_sq₀ (norm_nonneg _) (le_of_lt hsqrt_pos)).mp
    rw [hu_sq, Real.sq_sqrt (le_of_lt hsq_pos)]
  rw [finRealSphere_equatorProjection]
  simp [t, norm_smul, hu_norm, Real.norm_eq_abs, abs_inv,
    abs_of_pos hsqrt_pos]
  exact inv_mul_cancel₀ (ne_of_gt hsqrt_pos)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
noncomputable def finRealSphere_equatorPoint (n : ℕ)
    (e : FinRealEuclideanSpace n) (x : FinRealSphere n)
    (he : ‖e‖ = 1)
    (ht : finRealSphereInnerCoordinate n e x < 0)
    (ht' : -1 < finRealSphereInnerCoordinate n e x) : FinRealSphere n :=
  ⟨finRealSphere_equatorProjection n e x,
    by simpa [dist_eq_norm, sub_zero] using
      finRealSphere_equatorProjection_norm_eq_one n e x he ht ht'⟩

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
theorem finRealSphere_equatorPoint_mem_closedHemisphere (n : ℕ)
    (e : FinRealEuclideanSpace n) (x : FinRealSphere n)
    (he : ‖e‖ = 1)
    (ht : finRealSphereInnerCoordinate n e x < 0)
    (ht' : -1 < finRealSphereInnerCoordinate n e x) :
    finRealSphere_equatorPoint n e x he ht ht' ∈
      finRealSphereClosedHemisphere n e := by
  rw [mem_finRealSphereClosedHemisphere_iff]
  rw [finRealSphereInnerCoordinate, finRealSphere_equatorPoint]
  exact le_of_eq (finRealSphere_equatorProjection_inner_eq_zero n e x he).symm

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
theorem finRealSphere_geodesicDistance_to_equatorPoint_lt_pi_div_two
    (n : ℕ) (e : FinRealEuclideanSpace n) (x : FinRealSphere n)
    (he : ‖e‖ = 1)
    (ht : finRealSphereInnerCoordinate n e x < 0)
    (ht' : -1 < finRealSphereInnerCoordinate n e x) :
    finRealSphereGeodesicDistance n x (finRealSphere_equatorPoint n e x he ht ht') <
      Real.pi / 2 := by
  unfold finRealSphereGeodesicDistance
  set t := finRealSphereInnerCoordinate n e x
  set y := finRealSphere_equatorPoint n e x he ht ht'
  have ht_sq : t ^ 2 < 1 := by nlinarith
  have hsq_pos : 0 < 1 - t ^ 2 := sub_pos.mpr ht_sq
  have hinner :
      inner ℝ (x : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n) =
        Real.sqrt (1 - t ^ 2) := by
    have hinner_ex :
        inner ℝ e (x : FinRealEuclideanSpace n) = t := by
      simpa [t, finRealSphereInnerCoordinate]
    simp [y, finRealSphere_equatorPoint, finRealSphere_equatorProjection,
      finRealSphereInnerCoordinate, inner_smul_right, inner_sub_right,
      real_inner_comm, finRealSphere_coe_norm_eq_one n x, hinner_ex]
    field_simp [Real.sqrt_ne_zero'.mpr hsq_pos]
    rw [Real.sq_sqrt (le_of_lt hsq_pos)]
  have hdist_sq :
      dist x y ^ 2 = 2 * (1 - Real.sqrt (1 - t ^ 2)) := by
    rw [finRealSphere_dist_sq_eq_two_sub_two_inner, hinner]
    ring
  have hsqrt_lt_one : Real.sqrt (1 - t ^ 2) < 1 := by
    nlinarith [Real.sq_sqrt (le_of_lt hsq_pos)]
  have hdist_lt_sqrt_two : dist x y < Real.sqrt 2 := by
    have hpos : 0 ≤ dist x y := dist_nonneg
    have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    rw [← sq_lt_sq₀ hpos (le_of_lt hsqrt2_pos), hdist_sq]
    nlinarith [Real.sqrt_pos.mpr hsq_pos,
      Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
  have hhalf_lt_sqrt_half :
      dist x y / 2 < Real.sqrt 2 / 2 :=
    (div_lt_div_of_pos_right hdist_lt_sqrt_two (by norm_num))
  have hdist_nonneg : 0 ≤ dist x y := dist_nonneg
  have hdist_le_two : dist x y ≤ 2 := finRealSphere_dist_le_two n x y
  have harc_lt_quarter :
      Real.arcsin (dist x y / 2) < Real.pi / 4 := by
    have harg0 : -1 ≤ dist x y / 2 := by linarith [hdist_nonneg]
    have harg1 : dist x y / 2 ≤ 1 := by linarith [hdist_le_two]
    have hquarter0 : -1 ≤ Real.sqrt 2 / 2 := by linarith [Real.sqrt_nonneg 2]
    have hquarter1 : Real.sqrt 2 / 2 ≤ 1 := by
      have hsqrt2_le_two : Real.sqrt 2 ≤ 2 := by
        nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num),
          Real.sqrt_nonneg 2]
      linarith
    have harc_lt_sqrt :
        Real.arcsin (dist x y / 2) < Real.arcsin (Real.sqrt 2 / 2) :=
      Real.arcsin_lt_arcsin harg0 hhalf_lt_sqrt_half hquarter1
    have harc_sqrt :
        Real.arcsin (Real.sqrt 2 / 2) = Real.pi / 4 := by
      rw [← Real.sin_pi_div_four]
      exact Real.arcsin_sin
        (by linarith [Real.pi_pos])
        (by linarith [Real.pi_pos])
    exact harc_lt_sqrt.trans_eq harc_sqrt
  calc
    finRealSphereGeodesicDistance n x y
        = 2 * Real.arcsin (dist x y / 2) := rfl
    _ < 2 * (Real.pi / 4) := mul_lt_mul_of_pos_left harc_lt_quarter (by norm_num)
    _ = Real.pi / 2 := by ring_nf

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The geodesic distance from a point in the negative open halfspace to its
orthogonal equator projection is exactly the latitude angle `arcsin (-⟪e,x⟫)`.
This is the scalar geometry needed for the positive-radius coordinate-tail
dominance of hemisphere-neighbourhood complements. -/
theorem finRealSphere_geodesicDistance_to_equatorPoint_eq_arcsin_neg_inner
    (n : ℕ) (e : FinRealEuclideanSpace n) (x : FinRealSphere n)
    (he : ‖e‖ = 1)
    (ht : finRealSphereInnerCoordinate n e x < 0)
    (ht' : -1 < finRealSphereInnerCoordinate n e x) :
    finRealSphereGeodesicDistance n x
        (finRealSphere_equatorPoint n e x he ht ht') =
      Real.arcsin (-finRealSphereInnerCoordinate n e x) := by
  set t := finRealSphereInnerCoordinate n e x
  set y := finRealSphere_equatorPoint n e x he ht ht'
  set d := dist x y
  have ht_neg : t < 0 := by simpa [t] using ht
  have ht_gt : -1 < t := by simpa [t] using ht'
  have ht_sq : t ^ 2 < 1 := by nlinarith
  have hsq_pos : 0 < 1 - t ^ 2 := by nlinarith
  have hinner :
      inner ℝ (x : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n) =
        Real.sqrt (1 - t ^ 2) := by
    have hinner_ex :
        inner ℝ e (x : FinRealEuclideanSpace n) = t := by
      simpa [t, finRealSphereInnerCoordinate]
    simp [y, finRealSphere_equatorPoint, finRealSphere_equatorProjection,
      finRealSphereInnerCoordinate, inner_smul_right, inner_sub_right,
      real_inner_comm, finRealSphere_coe_norm_eq_one n x, hinner_ex]
    field_simp [Real.sqrt_ne_zero'.mpr hsq_pos]
    rw [Real.sq_sqrt (le_of_lt hsq_pos)]
  have hdist_sq :
      d ^ 2 = 2 * (1 - Real.sqrt (1 - t ^ 2)) := by
    dsimp [d]
    rw [finRealSphere_dist_sq_eq_two_sub_two_inner, hinner]
    ring
  have hdist_nonneg : 0 ≤ d := by
    dsimp [d]
    exact dist_nonneg
  have hdist_le_two : d ≤ 2 := by
    dsimp [d]
    exact finRealSphere_dist_le_two n x y
  have hhalf_nonneg : 0 ≤ d / 2 := by linarith
  have hhalf_le_one : d / 2 ≤ 1 := by linarith
  have hhalf_ge_neg_one : -1 ≤ d / 2 := by linarith
  have hhalf_arg_nonneg : 0 ≤ 1 - (d / 2) ^ 2 := by
    nlinarith
  have hsin_delta_sq :
      Real.sin (finRealSphereGeodesicDistance n x y) ^ 2 = (-t) ^ 2 := by
    have hsin_arc :
        Real.sin (Real.arcsin (d / 2)) = d / 2 :=
      Real.sin_arcsin hhalf_ge_neg_one hhalf_le_one
    have hcos_arc :
        Real.cos (Real.arcsin (d / 2)) =
          Real.sqrt (1 - (d / 2) ^ 2) :=
      Real.cos_arcsin (d / 2)
    have hs_sqrt :
        (Real.sqrt (1 - t ^ 2)) ^ 2 = 1 - t ^ 2 :=
      Real.sq_sqrt (le_of_lt hsq_pos)
    calc
      Real.sin (finRealSphereGeodesicDistance n x y) ^ 2
          =
          (2 * (d / 2) * Real.sqrt (1 - (d / 2) ^ 2)) ^ 2 := by
            dsimp [finRealSphereGeodesicDistance, d]
            rw [Real.sin_two_mul, hsin_arc, hcos_arc]
      _ = d ^ 2 * (1 - d ^ 2 / 4) := by
            nlinarith [Real.sq_sqrt hhalf_arg_nonneg]
      _ = (-t) ^ 2 := by
            rw [hdist_sq]
            nlinarith
  have hdist_lt_pi_div_two :
      finRealSphereGeodesicDistance n x y < Real.pi / 2 := by
    simpa [y] using
      finRealSphere_geodesicDistance_to_equatorPoint_lt_pi_div_two
        n e x he ht ht'
  have hdelta_nonneg :
      0 ≤ finRealSphereGeodesicDistance n x y := by
    dsimp [finRealSphereGeodesicDistance]
    have harc_nonneg : 0 ≤ Real.arcsin (d / 2) := by
      simpa using Real.arcsin_nonneg.mpr hhalf_nonneg
    positivity
  have hsin_delta_nonneg :
      0 ≤ Real.sin (finRealSphereGeodesicDistance n x y) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hdelta_nonneg
      (by linarith [hdist_lt_pi_div_two, Real.pi_pos])
  have hneg_nonneg : 0 ≤ -t := by linarith
  have hsin_delta :
      Real.sin (finRealSphereGeodesicDistance n x y) = -t :=
    (sq_eq_sq₀ hsin_delta_nonneg hneg_nonneg).mp hsin_delta_sq
  exact
    (Real.arcsin_eq_of_sin_eq hsin_delta
      ⟨by linarith [Real.pi_pos], le_of_lt hdist_lt_pi_div_two⟩).symm

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Pointwise positive-radius coordinate dominance for the complement of an
open geodesic neighbourhood of a closed hemisphere. -/
theorem finRealSphereGeodesicThickening_closedHemisphere_compl_subset_coordinateTail
    (n : ℕ) (c : FinRealSphere n) {r : ℝ}
    (hrpos : 0 < r) (hrle : r ≤ Real.pi / 2) :
    ((finRealSphereGeodesicThickening n r
      (finRealSphereClosedHemisphere n
        (c : FinRealEuclideanSpace n)))ᶜ) ⊆
      finRealSphereClosedHalfspace n
        (-(c : FinRealEuclideanSpace n)) (Real.sin r) := by
  intro x hx
  by_contra hnot
  have hnot_le :
      ¬ Real.sin r ≤
        finRealSphereInnerCoordinate n (-(c : FinRealEuclideanSpace n)) x := by
    simpa [finRealSphereClosedHalfspace] using hnot
  have hlt_neg :
      finRealSphereInnerCoordinate n (-(c : FinRealEuclideanSpace n)) x <
        Real.sin r :=
    not_le.mp hnot_le
  set t := finRealSphereInnerCoordinate n (c : FinRealEuclideanSpace n) x
  have hcoord_neg :
      finRealSphereInnerCoordinate n (-(c : FinRealEuclideanSpace n)) x = -t := by
    simp [t, finRealSphereInnerCoordinate]
  have hlt : -t < Real.sin r := by
    simpa [hcoord_neg] using hlt_neg
  by_cases htnonneg : 0 ≤ t
  · have hxhemi :
        x ∈ finRealSphereClosedHemisphere n (c : FinRealEuclideanSpace n) := by
      simpa [finRealSphereClosedHemisphere, finRealSphereClosedHalfspace, t]
        using htnonneg
    have hdist : finRealSphereGeodesicDistance n x x < r := by
      simpa [finRealSphereGeodesicDistance_self] using hrpos
    exact hx ⟨x, hxhemi, hdist⟩
  · have htneg : t < 0 := lt_of_not_ge htnonneg
    have htge : -1 ≤ t := by
      simpa [t] using finRealSphere_inner_ge_neg_one n c x
    have htne : t ≠ -1 := by
      intro ht_eq
      have hsin_gt_one : 1 < Real.sin r := by
        nlinarith
      exact not_lt_of_ge (Real.sin_le_one r) hsin_gt_one
    have htgt : -1 < t :=
      lt_of_le_of_ne htge (fun h => htne h.symm)
    let y :=
      finRealSphere_equatorPoint n (c : FinRealEuclideanSpace n) x
        (finRealSphere_coe_norm_eq_one n c)
        (by simpa [t] using htneg)
        (by simpa [t] using htgt)
    have hyhemi :
        y ∈ finRealSphereClosedHemisphere n (c : FinRealEuclideanSpace n) := by
      dsimp [y]
      exact
        finRealSphere_equatorPoint_mem_closedHemisphere n
          (c : FinRealEuclideanSpace n) x
          (finRealSphere_coe_norm_eq_one n c)
          (by simpa [t] using htneg)
          (by simpa [t] using htgt)
    have hdist_eq :
        finRealSphereGeodesicDistance n x y = Real.arcsin (-t) := by
      dsimp [y]
      simpa [t] using
        finRealSphere_geodesicDistance_to_equatorPoint_eq_arcsin_neg_inner n
          (c : FinRealEuclideanSpace n) x
          (finRealSphere_coe_norm_eq_one n c)
          (by simpa [t] using htneg)
          (by simpa [t] using htgt)
    have hr_mem : r ∈ Set.Ioc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [hrpos, Real.pi_pos], hrle⟩
    have harc_lt : Real.arcsin (-t) < r :=
      (Real.arcsin_lt_iff_lt_sin' hr_mem).2 hlt
    have hdist : finRealSphereGeodesicDistance n x y < r :=
      hdist_eq.trans_lt harc_lt
    exact hx ⟨y, hyhemi, hdist⟩

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Surface-measure version of positive-radius coordinate dominance for closed
hemisphere neighbourhood complements. -/
theorem finRealSphereHemisphereComplementCoordinateDominance_surface
    (n : ℕ) [NeZero n] :
    FinRealSphereHemisphereComplementCoordinateDominance n
      (finRealSurfaceProbabilityMeasure n) := by
  intro c r hrpos hrle
  haveI : IsFiniteMeasure (finRealSurfaceProbabilityMeasure n) := by
    unfold finRealSurfaceProbabilityMeasure
    infer_instance
  have hsubset :=
    finRealSphereGeodesicThickening_closedHemisphere_compl_subset_coordinateTail
      n c hrpos hrle
  calc
    (finRealSurfaceProbabilityMeasure n).real
        ((finRealSphereGeodesicThickening n r
          (finRealSphereClosedHemisphere n
            (c : FinRealEuclideanSpace n)))ᶜ) ≤
      (finRealSurfaceProbabilityMeasure n).real
        (finRealSphereClosedHalfspace n
          (-(c : FinRealEuclideanSpace n)) (Real.sin r)) :=
        measureReal_mono hsubset
          (h₂ := (measure_lt_top (finRealSurfaceProbabilityMeasure n)
            (finRealSphereClosedHalfspace n
              (-(c : FinRealEuclideanSpace n)) (Real.sin r))).ne)
    _ =
      (finRealSphereCoordinateLaw n
        (-(c : FinRealEuclideanSpace n))).real (Set.Ici (Real.sin r)) := by
        exact sphereClosedHalfspaceMeasure_coordinate_formula n
          (-(c : FinRealEuclideanSpace n)) (Real.sin r)

omit [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] in
/-- No-input supplier for the positive-radius coordinate-dominance step in the
hemisphere-tail proof. -/
theorem sphere_hemisphereComplementCoordinateDominance_surface :
    sphere_hemisphereComplementCoordinateDominance := by
  intro n hn
  exact finRealSphereHemisphereComplementCoordinateDominance_surface n

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The opposite-coordinate tail at threshold `1` is contained in the antipode
singleton. -/
theorem finRealSphereClosedHalfspace_neg_center_one_subset_singleton
    (n : ℕ) (c : FinRealSphere n) :
    finRealSphereClosedHalfspace n (-(c : FinRealEuclideanSpace n)) 1 ⊆
      {finRealSphere_neg n c} := by
  intro x hx
  have hcoord_neg :
      finRealSphereInnerCoordinate n (-(c : FinRealEuclideanSpace n)) x =
        -finRealSphereInnerCoordinate n (c : FinRealEuclideanSpace n) x := by
    simp [finRealSphereInnerCoordinate]
  have hle_neg_one :
      finRealSphereInnerCoordinate n (c : FinRealEuclideanSpace n) x ≤ -1 := by
    have hx' : 1 ≤
        finRealSphereInnerCoordinate n (-(c : FinRealEuclideanSpace n)) x := by
      simpa [finRealSphereClosedHalfspace] using hx
    linarith
  have hge_neg_one :
      -1 ≤ finRealSphereInnerCoordinate n (c : FinRealEuclideanSpace n) x :=
    finRealSphere_inner_ge_neg_one n c x
  have heq :
      finRealSphereInnerCoordinate n (c : FinRealEuclideanSpace n) x = -1 := by
    linarith
  exact Set.mem_singleton_iff.mpr
    ((finRealSphere_inner_eq_neg_one_iff_eq_neg n c x).mp heq)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The two endpoint radii in the spherical coordinate tail are elementary:
`r = 0` follows from probability mass at most one, and `r = π/2` from the
antipode singleton. Thus the full closed small-radius coordinate tail follows
from its strict interior form. -/
theorem finRealSphereCoordinateGaussianTail_of_interior
    (n : ℕ) [NeZero n]
    (hInterior : FinRealSphereCoordinateGaussianTailInterior n (n : ℝ)) :
    FinRealSphereCoordinateGaussianTail n (n : ℝ) := by
  intro c r hr0 hrle
  rcases lt_or_eq_of_le hr0 with hrpos | rfl
  · by_cases htop : r = Real.pi / 2
    · subst r
      by_cases hn2 : 2 ≤ n
      · have hsubset :
            finRealSphereClosedHalfspace n (-(c : FinRealEuclideanSpace n)) 1 ⊆
              {finRealSphere_neg n c} :=
          finRealSphereClosedHalfspace_neg_center_one_subset_singleton n c
        haveI : IsProbabilityMeasure (finRealSurfaceProbabilityMeasure n) :=
          finRealSurfaceProbabilityMeasure_isProbabilityMeasure n
        have hzero :
            (finRealSurfaceProbabilityMeasure n).real {finRealSphere_neg n c} = 0 := by
          rw [measureReal_def, finRealSurfaceProbabilityMeasure_singleton n hn2
            (finRealSphere_neg n c)]
          simp
        have hcap :
            (finRealSphereCoordinateLaw n
              (-(c : FinRealEuclideanSpace n))).real (Set.Ici 1) ≤ 0 := by
          calc
            (finRealSphereCoordinateLaw n
                (-(c : FinRealEuclideanSpace n))).real (Set.Ici 1) =
                (finRealSurfaceProbabilityMeasure n).real
                  (finRealSphereClosedHalfspace n
                    (-(c : FinRealEuclideanSpace n)) 1) := by
                  rw [sphereClosedHalfspaceMeasure_coordinate_formula]
            _ ≤ (finRealSurfaceProbabilityMeasure n).real {finRealSphere_neg n c} :=
                measureReal_mono hsubset
                  (h₂ := (measure_lt_top (finRealSurfaceProbabilityMeasure n)
                    {finRealSphere_neg n c}).ne)
            _ = 0 := hzero
        have htail :
            (finRealSphereCoordinateLaw n
                (-(c : FinRealEuclideanSpace n))).real
                (Set.Ici (Real.sin (Real.pi / 2))) ≤
              Real.exp (-((((n : ℕ) : ℝ) - 1) * (Real.pi / 2) ^ 2 / 2)) := by
          rw [Real.sin_pi_div_two]
          exact hcap.trans (Real.exp_nonneg _)
        simpa using htail
      · have hn1 : n = 1 := by
          have hlt : n < 2 := lt_of_not_ge hn2
          rcases n with (_ | _ | n)
          · cases NeZero.ne 0 rfl
          · rfl
          · exfalso
            exact Nat.not_lt_of_ge
              (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n))) hlt
        subst hn1
        haveI :=
          finRealSphereCoordinateLaw_isProbabilityMeasure 1
            (-(c : FinRealEuclideanSpace 1))
        have hprob :
            (finRealSphereCoordinateLaw 1
              (-(c : FinRealEuclideanSpace 1))).real
              (Set.Ici (Real.sin (Real.pi / 2))) ≤ 1 :=
          measureReal_le_one
        have hrhs :
            Real.exp (-((((1 : ℕ) : ℝ) - 1) * (Real.pi / 2) ^ 2 / 2)) = 1 := by
          simp
        simpa [hrhs] using hprob
    · exact hInterior c hrpos (lt_of_le_of_ne hrle htop)
  · haveI :=
      finRealSphereCoordinateLaw_isProbabilityMeasure n
        (-(c : FinRealEuclideanSpace n))
    have hprob :
        (finRealSphereCoordinateLaw n
          (-(c : FinRealEuclideanSpace n))).real
          (Set.Ici (Real.sin 0)) ≤ 1 :=
      measureReal_le_one
    simpa using hprob

omit [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] in
/-- The only strict-interior coordinate-tail case below dimension two is
`n = 1`; there the right hand side is `1`, so probability boundedness closes
the case. -/
theorem finRealSphereCoordinateGaussianTailInterior_of_geTwo
    (n : ℕ) [NeZero n]
    (hGeTwo : FinRealSphereCoordinateGaussianTailInteriorGeTwo n (n : ℝ)) :
    FinRealSphereCoordinateGaussianTailInterior n (n : ℝ) := by
  intro c r hrpos hrlt
  by_cases hn2 : 2 ≤ n
  · exact hGeTwo c hn2 hrpos hrlt
  · have hn1 : n = 1 := by
      have hlt : n < 2 := lt_of_not_ge hn2
      rcases n with (_ | _ | n)
      · cases NeZero.ne 0 rfl
      · rfl
      · exfalso
        exact Nat.not_lt_of_ge
          (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n))) hlt
    subst hn1
    haveI :=
      finRealSphereCoordinateLaw_isProbabilityMeasure 1
        (-(c : FinRealEuclideanSpace 1))
    have hprob :
        (finRealSphereCoordinateLaw 1
          (-(c : FinRealEuclideanSpace 1))).real
          (Set.Ici (Real.sin r)) ≤ 1 :=
      measureReal_le_one
    have hrhs :
        Real.exp (-((((1 : ℕ) : ℝ) - 1) * r ^ 2 / 2)) = 1 := by
      simp
    simpa [hrhs] using hprob

omit [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] in
/-- The dimension-at-least-two no-input package supplies the full strict
interior coordinate-tail package because the `n = 1` case is elementary. -/
theorem sphere_coordinateGaussianTailInterior_of_geTwo
    (hGeTwo : sphere_coordinateGaussianTailInteriorGeTwo) :
    sphere_coordinateGaussianTailInterior := by
  intro n hn
  exact finRealSphereCoordinateGaussianTailInterior_of_geTwo n (hGeTwo n)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The antipodal orthogonal map sends a closed coordinate halfspace to the
opposite coordinate halfspace. -/
theorem finRealOrthogonalSphereMap_neg_preimage_closedHalfspace
    (n : ℕ) (e : FinRealEuclideanSpace n) (t : ℝ) :
    (finRealOrthogonalSphereMap n
        (LinearIsometryEquiv.neg ℝ (E := FinRealEuclideanSpace n))) ⁻¹'
        finRealSphereClosedHalfspace n e t =
      finRealSphereClosedHalfspace n (-e) t := by
  ext x
  simp [finRealOrthogonalSphereMap, finRealSphereClosedHalfspace,
    finRealSphereInnerCoordinate]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Antipodal symmetry gives a universal half-mass bound for every strictly
positive coordinate tail. -/
theorem finRealSphere_positive_coordinate_tail_le_half
    (n : ℕ) [NeZero n] (c : FinRealSphere n) {t : ℝ} (ht : 0 < t) :
    (finRealSphereCoordinateLaw n (-(c : FinRealEuclideanSpace n))).real
        (Set.Ici t) ≤
      (1 / 2 : ℝ) := by
  let μ := finRealSurfaceProbabilityMeasure n
  let e : FinRealEuclideanSpace n := -(c : FinRealEuclideanSpace n)
  let E : Set (FinRealSphere n) := finRealSphereClosedHalfspace n e t
  let Eopp : Set (FinRealSphere n) := finRealSphereClosedHalfspace n (-e) t
  let U : FinRealOrthogonalGroup n :=
    LinearIsometryEquiv.neg ℝ (E := FinRealEuclideanSpace n)
  let S : FinRealSphere n → FinRealSphere n :=
    finRealOrthogonalSphereMap n U
  have hS_meas : Measurable S := by
    dsimp [S, finRealOrthogonalSphereMap]
    exact U.continuous.subtype_map (fun _ hx => by simpa using hx) |>.measurable
  have hE_meas : MeasurableSet E := by
    exact measurableSet_finRealSphereClosedHalfspace n e t
  have hEopp_meas : MeasurableSet Eopp := by
    exact measurableSet_finRealSphereClosedHalfspace n (-e) t
  have hmap : Measure.map S μ = μ := by
    simpa [μ, S, U] using
      finRealSurfaceProbabilityMeasure_map_orthogonal n U
  have hEqOpp : μ.real E = μ.real Eopp := by
    calc
      μ.real E = (Measure.map S μ).real E := by rw [hmap]
      _ = μ.real (S ⁻¹' E) := by
          rw [map_measureReal_apply hS_meas hE_meas]
      _ = μ.real Eopp := by
          have hpre := finRealOrthogonalSphereMap_neg_preimage_closedHalfspace n e t
          simpa [S, U, E, Eopp] using congrArg (fun T => μ.real T) hpre
  have hdisj : Disjoint E Eopp := by
    rw [Set.disjoint_left]
    intro x hx hxopp
    have hx1 : t ≤ finRealSphereInnerCoordinate n e x := by
      simpa [E, finRealSphereClosedHalfspace] using hx
    have hx2 : t ≤ finRealSphereInnerCoordinate n (-e) x := by
      simpa [Eopp, finRealSphereClosedHalfspace] using hxopp
    have hneg :
        finRealSphereInnerCoordinate n (-e) x =
          -finRealSphereInnerCoordinate n e x := by
      simp [finRealSphereInnerCoordinate]
    linarith
  haveI : IsProbabilityMeasure μ := finRealSurfaceProbabilityMeasure_isProbabilityMeasure n
  have hunion_le_one : μ.real (E ∪ Eopp) ≤ 1 := by
    exact measureReal_le_one
  have hunion_eq : μ.real (E ∪ Eopp) = μ.real E + μ.real Eopp := by
    have hE_ne_top : μ E ≠ ⊤ := (measure_lt_top μ E).ne
    have hEopp_ne_top : μ Eopp ≠ ⊤ := (measure_lt_top μ Eopp).ne
    rw [measureReal_def, measureReal_def, measureReal_def]
    rw [measure_union hdisj hEopp_meas]
    rw [ENNReal.toReal_add hE_ne_top hEopp_ne_top]
  have hsum : 2 * μ.real E ≤ 1 := by
    calc
      2 * μ.real E = μ.real E + μ.real Eopp := by
        rw [hEqOpp]
        ring
      _ = μ.real (E ∪ Eopp) := hunion_eq.symm
      _ ≤ 1 := hunion_le_one
  have hcoord :
      (finRealSphereCoordinateLaw n (-(c : FinRealEuclideanSpace n))).real
          (Set.Ici t) =
        μ.real E := by
    simpa [μ, E, e] using
      (sphereClosedHalfspaceMeasure_coordinate_formula n e t).symm
  rw [hcoord]
  nlinarith

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The large-exponent interior coordinate tail implies the full
dimension-at-least-two interior coordinate tail; the small-exponent regime is
absorbed by the antipodal half-tail bound. -/
theorem finRealSphereCoordinateGaussianTailInteriorGeTwo_of_largeExponent
    (n : ℕ) [NeZero n]
    (hLarge : FinRealSphereCoordinateGaussianTailInteriorLargeExponent n (n : ℝ)) :
    FinRealSphereCoordinateGaussianTailInteriorGeTwo n (n : ℝ) := by
  intro c r hn2 hrpos hrlt
  let A : ℝ := ((((n : ℕ) : ℝ) - 1) * r ^ 2) / 2
  by_cases hA : A ≤ Real.log 2
  · have hrpi : r < Real.pi := by
      have hpi_pos : 0 < Real.pi := Real.pi_pos
      linarith
    have hsin_pos : 0 < Real.sin r :=
      Real.sin_pos_of_pos_of_lt_pi hrpos hrpi
    have htail_half :
        (finRealSphereCoordinateLaw n (-(c : FinRealEuclideanSpace n))).real
            (Set.Ici (Real.sin r)) ≤
          (1 / 2 : ℝ) :=
      finRealSphere_positive_coordinate_tail_le_half n c hsin_pos
    have hhalf_exp : (1 / 2 : ℝ) ≤ Real.exp (-A) := by
      have hlog_pos : 0 < (2 : ℝ) := by norm_num
      calc
        (1 / 2 : ℝ) = Real.exp (-(Real.log 2)) := by
          rw [Real.exp_neg, Real.exp_log hlog_pos]
          norm_num
        _ ≤ Real.exp (-A) := by
          exact Real.exp_le_exp.mpr (by linarith)
    exact htail_half.trans (by simpa [A] using hhalf_exp)
  · have hA_lt : Real.log 2 < A := lt_of_not_ge hA
    exact hLarge c hn2 hrpos hrlt (by simpa [A] using hA_lt)

omit [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] in
/-- No-input adapter from the large-exponent coordinate tail package to the
previous dimension-at-least-two interior coordinate-tail package. -/
theorem sphere_coordinateGaussianTailInteriorGeTwo_of_largeExponent
    (hLarge : sphere_coordinateGaussianTailInteriorLargeExponent) :
    sphere_coordinateGaussianTailInteriorGeTwo := by
  intro n hn
  exact finRealSphereCoordinateGaussianTailInteriorGeTwo_of_largeExponent n (hLarge n)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Orthogonal transitivity on the concrete real sphere. -/
theorem exists_finRealOrthogonal_map
    (n : ℕ) [NeZero n] (x y : FinRealSphere n) :
    ∃ U : FinRealOrthogonalGroup n,
      U (x : FinRealEuclideanSpace n) = (y : FinRealEuclideanSpace n) := by
  classical
  let i0 : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  let vx : Fin n → FinRealEuclideanSpace n := fun i => if i = i0 then x else 0
  let vy : Fin n → FinRealEuclideanSpace n := fun i => if i = i0 then y else 0
  have hvx : Orthonormal ℝ (({i0} : Set (Fin n)).restrict vx) := by
    refine ⟨?_, ?_⟩
    · intro a
      have ha : ((a : ({i0} : Set (Fin n))) : Fin n) = i0 :=
        Set.mem_singleton_iff.mp a.2
      have hx : ‖(x : FinRealEuclideanSpace n)‖ = 1 := by
        rw [← dist_zero_right (a := (x : FinRealEuclideanSpace n))]
        change
          (x : FinRealEuclideanSpace n) ∈
            Metric.sphere (0 : FinRealEuclideanSpace n) 1
        exact x.2
      change ‖vx a‖ = 1
      rw [ha]
      simp [vx, hx]
    · intro a b hab
      exact False.elim (hab (Subsingleton.elim a b))
  have hvy : Orthonormal ℝ (({i0} : Set (Fin n)).restrict vy) := by
    refine ⟨?_, ?_⟩
    · intro a
      have ha : ((a : ({i0} : Set (Fin n))) : Fin n) = i0 :=
        Set.mem_singleton_iff.mp a.2
      have hy : ‖(y : FinRealEuclideanSpace n)‖ = 1 := by
        rw [← dist_zero_right (a := (y : FinRealEuclideanSpace n))]
        change
          (y : FinRealEuclideanSpace n) ∈
            Metric.sphere (0 : FinRealEuclideanSpace n) 1
        exact y.2
      change ‖vy a‖ = 1
      rw [ha]
      simp [vy, hy]
    · intro a b hab
      exact False.elim (hab (Subsingleton.elim a b))
  have hcard : Module.finrank ℝ (FinRealEuclideanSpace n) = Fintype.card (Fin n) := by
    exact Module.finrank_eq_card_basis (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  obtain ⟨bx, hbx⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (𝕜 := ℝ) (E := FinRealEuclideanSpace n) hcard hvx
  obtain ⟨byBasis, hby⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (𝕜 := ℝ) (E := FinRealEuclideanSpace n) hcard hvy
  let F : FinRealEuclideanSpace n ≃ₗᵢ[ℝ] FinRealEuclideanSpace n :=
    bx.equiv byBasis (Equiv.refl (Fin n))
  have hFx : F (x : FinRealEuclideanSpace n) = (y : FinRealEuclideanSpace n) := by
    have hbx0 : bx i0 = (x : FinRealEuclideanSpace n) := by
      simpa [vx] using hbx i0 (by simp)
    have hby0 : byBasis i0 = (y : FinRealEuclideanSpace n) := by
      simpa [vy] using hby i0 (by simp)
    rw [← hbx0, OrthonormalBasis.equiv_apply_basis]
    simpa using hby0
  exact ⟨F, hFx⟩

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- By orthogonal invariance of surface measure, every unit coordinate law is
the north-pole coordinate law. -/
theorem finRealSphereCoordinateLaw_eq_northPole
    (n : ℕ) [NeZero n] (c : FinRealSphere n) :
    finRealSphereCoordinateLaw n (-(c : FinRealEuclideanSpace n)) =
      finRealSphereCoordinateLaw n
        (-(finRealSphereNorthPole n : FinRealEuclideanSpace n)) := by
  let north := finRealSphereNorthPole n
  obtain ⟨U, hU⟩ := exists_finRealOrthogonal_map n north c
  let μ := finRealSurfaceProbabilityMeasure n
  let S : FinRealSphere n → FinRealSphere n := finRealOrthogonalSphereMap n U
  let f : FinRealSphere n → ℝ :=
    finRealSphereInnerCoordinate n (-(c : FinRealEuclideanSpace n))
  let g : FinRealSphere n → ℝ :=
    finRealSphereInnerCoordinate n (-(north : FinRealEuclideanSpace n))
  have hS_meas : Measurable S := by
    dsimp [S, finRealOrthogonalSphereMap]
    exact U.continuous.subtype_map (fun _ hx => by simpa using hx) |>.measurable
  have hf_meas : Measurable f := by
    exact
      (continuous_finRealSphereInnerCoordinate n
        (-(c : FinRealEuclideanSpace n))).measurable
  have hmap : Measure.map S μ = μ := by
    simpa [μ, S] using finRealSurfaceProbabilityMeasure_map_orthogonal n U
  have hcomp : f ∘ S = g := by
    funext x
    have hUnorth_neg :
        U (-(north : FinRealEuclideanSpace n)) =
          -(c : FinRealEuclideanSpace n) := by
      rw [map_neg, hU]
    dsimp [f, g, S, finRealSphereInnerCoordinate, finRealOrthogonalSphereMap]
    calc
      inner ℝ (-(c : FinRealEuclideanSpace n))
          (U (x : FinRealEuclideanSpace n)) =
        inner ℝ (U (-(north : FinRealEuclideanSpace n)))
          (U (x : FinRealEuclideanSpace n)) := by
          rw [hUnorth_neg]
      _ =
        inner ℝ (-(north : FinRealEuclideanSpace n))
          (x : FinRealEuclideanSpace n) := by
          rw [LinearIsometryEquiv.inner_map_map]
  unfold finRealSphereCoordinateLaw
  calc
    Measure.map f μ = Measure.map f (Measure.map S μ) := by rw [hmap]
    _ = Measure.map (f ∘ S) μ := by
      rw [MeasureTheory.Measure.map_map hf_meas hS_meas]
    _ = Measure.map g μ := by rw [hcomp]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Orthogonal maps send a closed hemisphere to the closed hemisphere with
transported pole. -/
theorem finRealOrthogonalSphereMap_image_closedHemisphere
    (n : ℕ) (U : FinRealOrthogonalGroup n) (c : FinRealSphere n) :
    finRealOrthogonalSphereMap n U ''
        finRealSphereClosedHemisphere n (c : FinRealEuclideanSpace n) =
      finRealSphereClosedHemisphere n
        (U (c : FinRealEuclideanSpace n)) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' :
        0 ≤ inner ℝ (c : FinRealEuclideanSpace n)
          (y : FinRealEuclideanSpace n) := by
      simpa [finRealSphereClosedHemisphere, finRealSphereClosedHalfspace,
        finRealSphereInnerCoordinate] using hy
    simpa [finRealSphereClosedHemisphere, finRealSphereClosedHalfspace,
      finRealSphereInnerCoordinate, finRealOrthogonalSphereMap,
      LinearIsometryEquiv.inner_map_map] using hy'
  · intro hx
    refine ⟨finRealOrthogonalSphereMap n U.symm x, ?_, ?_⟩
    · have hx' :
          0 ≤ inner ℝ (U (c : FinRealEuclideanSpace n))
            (x : FinRealEuclideanSpace n) := by
        simpa [finRealSphereClosedHemisphere, finRealSphereClosedHalfspace,
          finRealSphereInnerCoordinate] using hx
      have hpre :
          0 ≤ inner ℝ (c : FinRealEuclideanSpace n)
            ((finRealOrthogonalSphereMap n U.symm x : FinRealSphere n) :
              FinRealEuclideanSpace n) := by
        have hinner :
            inner ℝ (c : FinRealEuclideanSpace n) (U.symm (x : FinRealEuclideanSpace n)) =
              inner ℝ (U (c : FinRealEuclideanSpace n)) (x : FinRealEuclideanSpace n) := by
          calc
            inner ℝ (c : FinRealEuclideanSpace n) (U.symm (x : FinRealEuclideanSpace n)) =
                inner ℝ (U (c : FinRealEuclideanSpace n))
                  (U (U.symm (x : FinRealEuclideanSpace n))) := by
                  rw [LinearIsometryEquiv.inner_map_map]
            _ = inner ℝ (U (c : FinRealEuclideanSpace n)) (x : FinRealEuclideanSpace n) := by
                  rw [LinearIsometryEquiv.apply_symm_apply]
        simpa [finRealOrthogonalSphereMap, hinner] using hx'
      simpa [finRealSphereClosedHemisphere, finRealSphereClosedHalfspace,
        finRealSphereInnerCoordinate] using hpre
    · apply Subtype.ext
      simp [finRealOrthogonalSphereMap]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The geodesic-neighbourhood complement objective of a closed hemisphere does
not depend on its pole. -/
theorem finRealSphereNeighbourhoodComplementMass_closedHemisphere_eq
    (n : ℕ) [NeZero n] (r : ℝ) (c d : FinRealSphere n) :
    finRealSphereNeighbourhoodComplementMass n
        (finRealSurfaceProbabilityMeasure n) r
        (finRealSphereClosedHemisphere n (c : FinRealEuclideanSpace n)) =
      finRealSphereNeighbourhoodComplementMass n
        (finRealSurfaceProbabilityMeasure n) r
        (finRealSphereClosedHemisphere n (d : FinRealEuclideanSpace n)) := by
  obtain ⟨U, hU⟩ := exists_finRealOrthogonal_map n c d
  have himage :
      finRealOrthogonalSphereMap n U ''
          finRealSphereClosedHemisphere n (c : FinRealEuclideanSpace n) =
        finRealSphereClosedHemisphere n (d : FinRealEuclideanSpace n) := by
    rw [finRealOrthogonalSphereMap_image_closedHemisphere n U c, hU]
  rw [← himage]
  exact (finRealSphereNeighbourhoodComplementMass_orthogonal_image U r
    (finRealSphereClosedHemisphere n (c : FinRealEuclideanSpace n))).symm

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- North-pole normalization for the closed-hemisphere objective. -/
theorem finRealSphereNeighbourhoodComplementMass_closedHemisphere_eq_northPole
    (n : ℕ) [NeZero n] (r : ℝ) (c : FinRealSphere n) :
    finRealSphereNeighbourhoodComplementMass n
        (finRealSurfaceProbabilityMeasure n) r
        (finRealSphereClosedHemisphere n (c : FinRealEuclideanSpace n)) =
      finRealSphereNeighbourhoodComplementMass n
        (finRealSurfaceProbabilityMeasure n) r
        (finRealSphereClosedHemisphere n
          (finRealSphereNorthPole n : FinRealEuclideanSpace n)) :=
  finRealSphereNeighbourhoodComplementMass_closedHemisphere_eq n r c
    (finRealSphereNorthPole n)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Radius-wise supremum domination by some closed hemisphere is equivalent to
domination by the north-pole closed hemisphere. -/
theorem finRealSphere_complementSup_le_some_closedHemisphere_iff_northPole
    (n : ℕ) [NeZero n] (r : ℝ) :
    (∃ c : FinRealSphere n,
      finRealSphereHalfMassComplementSup n
          (finRealSurfaceProbabilityMeasure n) r ≤
        finRealSphereNeighbourhoodComplementMass n
          (finRealSurfaceProbabilityMeasure n) r
          (finRealSphereClosedHemisphere n
            (c : FinRealEuclideanSpace n))) ↔
      finRealSphereHalfMassComplementSup n
          (finRealSurfaceProbabilityMeasure n) r ≤
        finRealSphereNeighbourhoodComplementMass n
          (finRealSurfaceProbabilityMeasure n) r
          (finRealSphereClosedHemisphere n
            (finRealSphereNorthPole n : FinRealEuclideanSpace n)) := by
  constructor
  · rintro ⟨c, hc⟩
    simpa [finRealSphereNeighbourhoodComplementMass_closedHemisphere_eq_northPole n r c] using hc
  · intro h
    exact ⟨finRealSphereNorthPole n, h⟩

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Dimension-at-least-two cap comparison follows from radius-wise domination
of the half-mass complement supremum by the north-pole closed hemisphere. -/
theorem finRealSphereHalfMeasureHemisphereComparisonGeTwo_of_complementSup_le_northPole
    (hSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 ≤ r →
          finRealSphereHalfMassComplementSup n
              (finRealSurfaceProbabilityMeasure n) r ≤
            finRealSphereNeighbourhoodComplementMass n
              (finRealSurfaceProbabilityMeasure n) r
              (finRealSphereClosedHemisphere n
                (finRealSphereNorthPole n : FinRealEuclideanSpace n))) :
    ∀ (n : ℕ) [NeZero n],
      FinRealSphereHalfMeasureHemisphereComparisonGeTwo n
        (finRealSurfaceProbabilityMeasure n) := by
  intro n _ hn2
  refine
    finRealSphereHalfMeasureHemisphereComparisonGeTwo_of_complementSup_le_hemisphere
      ?_ n hn2
  intro m _ hm2 r hr
  exact
    (finRealSphere_complementSup_le_some_closedHemisphere_iff_northPole m r).2
      (hSup (n := m) hm2 (r := r) hr)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- No-input cap comparison in dimensions at least two follows from radius-wise
domination of the half-mass complement supremum by the north-pole closed
hemisphere. -/
theorem sphere_halfMeasure_hemisphereComparisonGeTwo_of_complementSup_le_northPole
    (hSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 ≤ r →
          finRealSphereHalfMassComplementSup n
              (finRealSurfaceProbabilityMeasure n) r ≤
            finRealSphereNeighbourhoodComplementMass n
              (finRealSurfaceProbabilityMeasure n) r
              (finRealSphereClosedHemisphere n
                (finRealSphereNorthPole n : FinRealEuclideanSpace n))) :
    sphere_halfMeasure_hemisphereComparisonGeTwo :=
  finRealSphereHalfMeasureHemisphereComparisonGeTwo_of_complementSup_le_northPole hSup

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Nonpositive-radius geodesic thickenings are empty for the open thickening
convention used in Appendix B. -/
theorem finRealSphereGeodesicThickening_eq_empty_of_nonpos
    (n : ℕ) {r : ℝ} (hr : r ≤ 0) (A : Set (FinRealSphere n)) :
    finRealSphereGeodesicThickening n r A = ∅ := by
  ext x
  constructor
  · rintro ⟨y, _hy, hdist⟩
    exact (not_lt_of_ge (finRealSphereGeodesicDistance_nonneg n x y))
      (lt_of_lt_of_le hdist hr)
  · simp

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- At nonpositive radii, every competitor has full neighbourhood-complement
mass for the normalized surface measure. -/
theorem finRealSphereNeighbourhoodComplementMass_eq_one_of_nonpos
    (n : ℕ) [NeZero n] {r : ℝ} (hr : r ≤ 0)
    (A : Set (FinRealSphere n)) :
    finRealSphereNeighbourhoodComplementMass n
        (finRealSurfaceProbabilityMeasure n) r A = 1 := by
  haveI : IsProbabilityMeasure (finRealSurfaceProbabilityMeasure n) :=
    finRealSurfaceProbabilityMeasure_isProbabilityMeasure n
  simp [finRealSphereNeighbourhoodComplementMass,
    finRealSphereGeodesicThickening_eq_empty_of_nonpos n hr A]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The half-mass complement supremum is bounded by one for the normalized
surface measure. -/
theorem finRealSphereHalfMassComplementSup_le_one_surface
    (n : ℕ) [NeZero n] (r : ℝ) :
    finRealSphereHalfMassComplementSup n
        (finRealSurfaceProbabilityMeasure n) r ≤ 1 := by
  let values :=
    finRealSphereHalfMassComplementValues n (finRealSurfaceProbabilityMeasure n) r
  have hne : values.Nonempty :=
    finRealSphereHalfMassComplementValues_nonempty_surface n r
  refine csSup_le hne ?_
  intro t ht
  rcases ht with ⟨A, _hA, rfl⟩
  haveI : IsProbabilityMeasure (finRealSurfaceProbabilityMeasure n) :=
    finRealSurfaceProbabilityMeasure_isProbabilityMeasure n
  exact measureReal_le_one

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The normalized north-pole supremum domination is automatic at
nonpositive radii. -/
theorem finRealSphereHalfMassComplementSup_le_northPole_of_nonpos
    (n : ℕ) [NeZero n] {r : ℝ} (hr : r ≤ 0) :
    finRealSphereHalfMassComplementSup n
        (finRealSurfaceProbabilityMeasure n) r ≤
      finRealSphereNeighbourhoodComplementMass n
        (finRealSurfaceProbabilityMeasure n) r
        (finRealSphereClosedHemisphere n
          (finRealSphereNorthPole n : FinRealEuclideanSpace n)) := by
  simpa [finRealSphereNeighbourhoodComplementMass_eq_one_of_nonpos n hr
      (finRealSphereClosedHemisphere n
        (finRealSphereNorthPole n : FinRealEuclideanSpace n))] using
    finRealSphereHalfMassComplementSup_le_one_surface n r

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- A half-mass competitor is nonempty. -/
theorem FinRealSphereHalfMassCompetitor.nonempty
    {n : ℕ} {μ : Measure (FinRealSphere n)} {A : Set (FinRealSphere n)}
    (hA : FinRealSphereHalfMassCompetitor n μ A) :
    A.Nonempty := by
  by_contra hne
  have hA_empty : A = ∅ := by
    ext x
    constructor
    · intro hx
      exact False.elim (hne ⟨x, hx⟩)
    · intro hx
      cases hx
  have hhalf : (1 / 2 : ℝ) ≤ 0 := by
    simpa [hA_empty] using hA.2
  norm_num at hhalf

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- If the radius is larger than the sphere diameter, the geodesic thickening
of any nonempty set is the whole sphere. -/
theorem finRealSphereGeodesicThickening_eq_univ_of_pi_lt
    (n : ℕ) {r : ℝ} (hr : Real.pi < r)
    {A : Set (FinRealSphere n)} (hA : A.Nonempty) :
    finRealSphereGeodesicThickening n r A = Set.univ := by
  ext x
  constructor
  · intro _hx
    trivial
  · intro _hx
    rcases hA with ⟨y, hy⟩
    exact ⟨y, hy, (finRealSphereGeodesicDistance_le_pi n x y).trans_lt hr⟩

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- At radii larger than `π`, any half-mass competitor has zero
neighbourhood-complement mass. -/
theorem finRealSphereNeighbourhoodComplementMass_eq_zero_of_pi_lt
    (n : ℕ) {r : ℝ} (hr : Real.pi < r)
    {A : Set (FinRealSphere n)}
    (hA : FinRealSphereHalfMassCompetitor n
      (finRealSurfaceProbabilityMeasure n) A) :
    finRealSphereNeighbourhoodComplementMass n
        (finRealSurfaceProbabilityMeasure n) r A = 0 := by
  simp [finRealSphereNeighbourhoodComplementMass,
    finRealSphereGeodesicThickening_eq_univ_of_pi_lt n hr hA.nonempty]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The normalized north-pole supremum domination is automatic at radii larger
than the sphere diameter. -/
theorem finRealSphereHalfMassComplementSup_le_northPole_of_pi_lt
    (n : ℕ) [NeZero n] {r : ℝ} (hr : Real.pi < r) :
    finRealSphereHalfMassComplementSup n
        (finRealSurfaceProbabilityMeasure n) r ≤
      finRealSphereNeighbourhoodComplementMass n
        (finRealSurfaceProbabilityMeasure n) r
        (finRealSphereClosedHemisphere n
          (finRealSphereNorthPole n : FinRealEuclideanSpace n)) := by
  let values :=
    finRealSphereHalfMassComplementValues n (finRealSurfaceProbabilityMeasure n) r
  have hne : values.Nonempty :=
    finRealSphereHalfMassComplementValues_nonempty_surface n r
  have hsup_zero :
      finRealSphereHalfMassComplementSup n
          (finRealSurfaceProbabilityMeasure n) r ≤ 0 := by
    refine csSup_le hne ?_
    intro t ht
    rcases ht with ⟨A, hA, rfl⟩
    rw [finRealSphereNeighbourhoodComplementMass_eq_zero_of_pi_lt n hr hA]
  have hnorth_zero :
      finRealSphereNeighbourhoodComplementMass n
          (finRealSurfaceProbabilityMeasure n) r
          (finRealSphereClosedHemisphere n
            (finRealSphereNorthPole n : FinRealEuclideanSpace n)) = 0 := by
    exact finRealSphereNeighbourhoodComplementMass_eq_zero_of_pi_lt n hr
      (finRealSphereHalfMassCompetitor_closedHemisphere n
        (finRealSphereNorthPole n : FinRealEuclideanSpace n))
  simpa [hnorth_zero] using hsup_zero

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Non-antipodal points on the unit sphere have chord distance strictly less
than the diameter `2`. -/
theorem finRealSphere_dist_lt_two_of_ne_neg
    (n : ℕ) (x y : FinRealSphere n) (hy : y ≠ finRealSphere_neg n x) :
    dist x y < 2 := by
  have hinner_gt :
      -1 < inner ℝ (x : FinRealEuclideanSpace n)
        (y : FinRealEuclideanSpace n) := by
    have hle :
        -1 ≤ finRealSphereInnerCoordinate n
          (x : FinRealEuclideanSpace n) y :=
      finRealSphere_inner_ge_neg_one n x y
    rcases lt_or_eq_of_le hle with hlt | heq
    · simpa [finRealSphereInnerCoordinate] using hlt
    · exfalso
      exact hy ((finRealSphere_inner_eq_neg_one_iff_eq_neg n x y).mp heq.symm)
  have hdist_sq : dist x y ^ 2 < 2 ^ 2 := by
    rw [finRealSphere_dist_sq_eq_two_sub_two_inner n x y]
    nlinarith
  exact (sq_lt_sq₀ dist_nonneg (by norm_num : (0 : ℝ) ≤ 2)).mp hdist_sq

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Non-antipodal points on the concrete sphere have geodesic distance
strictly less than `π`. -/
theorem finRealSphereGeodesicDistance_lt_pi_of_ne_neg
    (n : ℕ) (x y : FinRealSphere n) (hy : y ≠ finRealSphere_neg n x) :
    finRealSphereGeodesicDistance n x y < Real.pi := by
  unfold finRealSphereGeodesicDistance
  have hdist_lt : dist x y < 2 := finRealSphere_dist_lt_two_of_ne_neg n x y hy
  have hhalf_lt : dist x y / 2 < 1 := by linarith
  have harc_lt : Real.arcsin (dist x y / 2) < Real.pi / 2 :=
    Real.arcsin_lt_pi_div_two.mpr hhalf_lt
  linarith

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- A half-mass competitor for the normalized surface law in dimension at
least two cannot be contained in a singleton. -/
theorem FinRealSphereHalfMassCompetitor.not_subset_singleton_surface
    (n : ℕ) [NeZero n] (hn2 : 2 ≤ n)
    {A : Set (FinRealSphere n)}
    (hA : FinRealSphereHalfMassCompetitor n
      (finRealSurfaceProbabilityMeasure n) A)
    (x : FinRealSphere n) :
    ¬ A ⊆ {x} := by
  intro hsubset
  haveI : IsProbabilityMeasure (finRealSurfaceProbabilityMeasure n) :=
    finRealSurfaceProbabilityMeasure_isProbabilityMeasure n
  have hsing_real :
      (finRealSurfaceProbabilityMeasure n).real
        ({x} : Set (FinRealSphere n)) = 0 := by
    rw [measureReal_def, finRealSurfaceProbabilityMeasure_singleton n hn2 x]
    simp
  have hA_le_zero : (finRealSurfaceProbabilityMeasure n).real A ≤ 0 := by
    have hmono := measureReal_mono hsubset
      (h₂ := (measure_lt_top (finRealSurfaceProbabilityMeasure n)
        ({x} : Set (FinRealSphere n))).ne)
    simpa [hsing_real] using hmono
  have hhalf : (1 / 2 : ℝ) ≤ 0 := hA.2.trans hA_le_zero
  norm_num at hhalf

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- At the boundary radius `π`, every half-mass competitor in dimension at
least two has whole-sphere open geodesic thickening. -/
theorem finRealSphereGeodesicThickening_eq_univ_of_pi_of_halfMass
    (n : ℕ) [NeZero n] (hn2 : 2 ≤ n)
    {A : Set (FinRealSphere n)}
    (hA : FinRealSphereHalfMassCompetitor n
      (finRealSurfaceProbabilityMeasure n) A) :
    finRealSphereGeodesicThickening n Real.pi A = Set.univ := by
  ext x
  constructor
  · intro _hx
    trivial
  · intro _hx
    have hnot_subset : ¬ A ⊆ {finRealSphere_neg n x} :=
      hA.not_subset_singleton_surface n hn2 (finRealSphere_neg n x)
    have hex : ∃ y ∈ A, y ≠ finRealSphere_neg n x := by
      by_contra hnone
      apply hnot_subset
      intro y hy
      by_contra hyne
      exact hnone ⟨y, hy, hyne⟩
    rcases hex with ⟨y, hyA, hyne⟩
    exact ⟨y, hyA, finRealSphereGeodesicDistance_lt_pi_of_ne_neg n x y hyne⟩

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- At radius `π`, every half-mass competitor has zero
neighbourhood-complement mass. -/
theorem finRealSphereNeighbourhoodComplementMass_eq_zero_of_pi_of_halfMass
    (n : ℕ) [NeZero n] (hn2 : 2 ≤ n)
    {A : Set (FinRealSphere n)}
    (hA : FinRealSphereHalfMassCompetitor n
      (finRealSurfaceProbabilityMeasure n) A) :
    finRealSphereNeighbourhoodComplementMass n
        (finRealSurfaceProbabilityMeasure n) Real.pi A = 0 := by
  simp [finRealSphereNeighbourhoodComplementMass,
    finRealSphereGeodesicThickening_eq_univ_of_pi_of_halfMass n hn2 hA]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The normalized north-pole supremum domination is automatic at the boundary
radius `π`. -/
theorem finRealSphereHalfMassComplementSup_le_northPole_of_pi
    (n : ℕ) [NeZero n] (hn2 : 2 ≤ n) :
    finRealSphereHalfMassComplementSup n
        (finRealSurfaceProbabilityMeasure n) Real.pi ≤
      finRealSphereNeighbourhoodComplementMass n
        (finRealSurfaceProbabilityMeasure n) Real.pi
        (finRealSphereClosedHemisphere n
          (finRealSphereNorthPole n : FinRealEuclideanSpace n)) := by
  let values :=
    finRealSphereHalfMassComplementValues n
      (finRealSurfaceProbabilityMeasure n) Real.pi
  have hne : values.Nonempty :=
    finRealSphereHalfMassComplementValues_nonempty_surface n Real.pi
  have hsup_zero :
      finRealSphereHalfMassComplementSup n
          (finRealSurfaceProbabilityMeasure n) Real.pi ≤ 0 := by
    refine csSup_le hne ?_
    intro t ht
    rcases ht with ⟨A, hA, rfl⟩
    rw [finRealSphereNeighbourhoodComplementMass_eq_zero_of_pi_of_halfMass
      n hn2 hA]
  have hnorth_zero :
      finRealSphereNeighbourhoodComplementMass n
          (finRealSurfaceProbabilityMeasure n) Real.pi
          (finRealSphereClosedHemisphere n
            (finRealSphereNorthPole n : FinRealEuclideanSpace n)) = 0 := by
    exact finRealSphereNeighbourhoodComplementMass_eq_zero_of_pi_of_halfMass
      n hn2
      (finRealSphereHalfMassCompetitor_closedHemisphere n
        (finRealSphereNorthPole n : FinRealEuclideanSpace n))
  simpa [hnorth_zero] using hsup_zero

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- No-input cap comparison in dimensions at least two follows from proving
the normalized north-pole supremum domination only at positive radii. -/
theorem sphere_halfMeasure_hemisphereComparisonGeTwo_of_complementSup_le_northPole_pos
    (hSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r →
          finRealSphereHalfMassComplementSup n
              (finRealSurfaceProbabilityMeasure n) r ≤
          finRealSphereNeighbourhoodComplementMass n
              (finRealSurfaceProbabilityMeasure n) r
              (finRealSphereClosedHemisphere n
                (finRealSphereNorthPole n : FinRealEuclideanSpace n))) :
    sphere_halfMeasure_hemisphereComparisonGeTwo := by
  exact sphere_halfMeasure_hemisphereComparisonGeTwo_of_complementSup_le_northPole
    (fun n _ hn2 {r} _hr => by
      by_cases hpos : 0 < r
      · exact hSup (n := n) hn2 (r := r) hpos
      · exact finRealSphereHalfMassComplementSup_le_northPole_of_nonpos n
          (r := r) (le_of_not_gt hpos))

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- No-input cap comparison in dimensions at least two follows from proving
the normalized north-pole supremum domination only on `0 < r ≤ π`. -/
theorem sphere_halfMeasure_hemisphereComparisonGeTwo_of_complementSup_le_northPole_pos_le_pi
    (hSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r ≤ Real.pi →
          finRealSphereHalfMassComplementSup n
              (finRealSurfaceProbabilityMeasure n) r ≤
          finRealSphereNeighbourhoodComplementMass n
              (finRealSurfaceProbabilityMeasure n) r
              (finRealSphereClosedHemisphere n
                (finRealSphereNorthPole n : FinRealEuclideanSpace n))) :
    sphere_halfMeasure_hemisphereComparisonGeTwo := by
  exact sphere_halfMeasure_hemisphereComparisonGeTwo_of_complementSup_le_northPole_pos
    (fun n _ hn2 {r} hrpos => by
      by_cases hrπ : r ≤ Real.pi
      · exact hSup (n := n) hn2 (r := r) hrpos hrπ
      · exact finRealSphereHalfMassComplementSup_le_northPole_of_pi_lt n
          (r := r) (lt_of_not_ge hrπ))

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- No-input cap comparison in dimensions at least two follows from proving
the normalized north-pole supremum domination only on the strict interval
`0 < r < π`.  The boundary cases `r ≤ 0`, `r = π`, and `π < r` are automatic. -/
theorem sphere_halfMeasure_hemisphereComparisonGeTwo_of_complementSup_le_northPole_pos_lt_pi
    (hSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          finRealSphereHalfMassComplementSup n
              (finRealSurfaceProbabilityMeasure n) r ≤
          finRealSphereNeighbourhoodComplementMass n
              (finRealSurfaceProbabilityMeasure n) r
              (finRealSphereClosedHemisphere n
                (finRealSphereNorthPole n : FinRealEuclideanSpace n))) :
    sphere_halfMeasure_hemisphereComparisonGeTwo := by
  exact sphere_halfMeasure_hemisphereComparisonGeTwo_of_complementSup_le_northPole_pos_le_pi
    (fun n _ hn2 {r} hrpos hrle => by
      rcases lt_or_eq_of_le hrle with hrlt | hreq
      · exact hSup (n := n) hn2 (r := r) hrpos hrlt
      · subst hreq
        exact finRealSphereHalfMassComplementSup_le_northPole_of_pi n hn2)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Quantitative gap-improvement criterion for normalized north-pole supremum
domination.

If every half-mass competitor whose objective exceeds the north-pole
hemisphere objective by `η` admits an admissible improvement by the same `η`,
then the half-mass complement supremum is dominated by the north-pole
hemisphere objective. -/
theorem finRealSphereHalfMassComplementSup_le_northPole_of_quantitative_gap_improvement
    (n : ℕ) [NeZero n] (r : ℝ)
    (hImprove :
      ∀ ⦃η : ℝ⦄, 0 < η →
        ∀ ⦃A : Set (FinRealSphere n)⦄,
          FinRealSphereHalfMassCompetitor n
              (finRealSurfaceProbabilityMeasure n) A →
          finRealSphereNeighbourhoodComplementMass n
                (finRealSurfaceProbabilityMeasure n) r
                (finRealSphereClosedHemisphere n
                  (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
            finRealSphereNeighbourhoodComplementMass n
              (finRealSurfaceProbabilityMeasure n) r A →
          ∃ B : Set (FinRealSphere n),
            FinRealSphereHalfMassCompetitor n
                (finRealSurfaceProbabilityMeasure n) B ∧
              finRealSphereNeighbourhoodComplementMass n
                  (finRealSurfaceProbabilityMeasure n) r A + η ≤
                finRealSphereNeighbourhoodComplementMass n
                  (finRealSurfaceProbabilityMeasure n) r B) :
    finRealSphereHalfMassComplementSup n
        (finRealSurfaceProbabilityMeasure n) r ≤
      finRealSphereNeighbourhoodComplementMass n
        (finRealSurfaceProbabilityMeasure n) r
        (finRealSphereClosedHemisphere n
          (finRealSphereNorthPole n : FinRealEuclideanSpace n)) := by
  by_contra hnot
  let S :=
    finRealSphereHalfMassComplementSup n
      (finRealSurfaceProbabilityMeasure n) r
  let H :=
    finRealSphereNeighbourhoodComplementMass n
      (finRealSurfaceProbabilityMeasure n) r
      (finRealSphereClosedHemisphere n
        (finRealSphereNorthPole n : FinRealEuclideanSpace n))
  have hlt : H < S := lt_of_not_ge hnot
  let η : ℝ := (S - H) / 4
  have hη : 0 < η := by
    dsimp [η]
    linarith
  rcases
      exists_finRealSphereHalfMassCompetitor_near_complementSup_no_admissible_eta_improvement
        n r hη with
    ⟨A, hA, hnear, hno⟩
  have hgap :
      H + η ≤
        finRealSphereNeighbourhoodComplementMass n
          (finRealSurfaceProbabilityMeasure n) r A := by
    dsimp [S, H, η] at hnear ⊢
    linarith
  rcases hImprove hη hA hgap with ⟨B, hB, himprove⟩
  exact hno B hB himprove

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- No-input cap comparison in dimensions at least two follows from a
quantitative gap-improvement theorem on the strict radius interval
`0 < r < π`.

This is the final order-theoretic adapter before the geometric
strict-improvement/cap-characterization supplier. -/
theorem sphere_halfMeasure_hemisphereComparisonGeTwo_of_quantitative_gap_improvement_pos_lt_pi
    (hImprove :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∀ ⦃A : Set (FinRealSphere n)⦄,
              FinRealSphereHalfMassCompetitor n
                  (finRealSurfaceProbabilityMeasure n) A →
              finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r
                    (finRealSphereClosedHemisphere n
                      (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
                finRealSphereNeighbourhoodComplementMass n
                  (finRealSurfaceProbabilityMeasure n) r A →
              ∃ B : Set (FinRealSphere n),
                FinRealSphereHalfMassCompetitor n
                    (finRealSurfaceProbabilityMeasure n) B ∧
                  finRealSphereNeighbourhoodComplementMass n
                      (finRealSurfaceProbabilityMeasure n) r A + η ≤
                    finRealSphereNeighbourhoodComplementMass n
                      (finRealSurfaceProbabilityMeasure n) r B) :
    sphere_halfMeasure_hemisphereComparisonGeTwo := by
  exact sphere_halfMeasure_hemisphereComparisonGeTwo_of_complementSup_le_northPole_pos_lt_pi
    (fun n _ hn2 {r} hrpos hrlt =>
      finRealSphereHalfMassComplementSup_le_northPole_of_quantitative_gap_improvement
        n r (hImprove n hn2 hrpos hrlt))

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Polarization-specific quantitative gap-improvement criterion for
normalized north-pole supremum domination.

It is enough to improve an above-hemisphere competitor by polarizing it in
some direction; the polarized set is automatically an admissible half-mass
competitor. -/
theorem finRealSphereHalfMassComplementSup_le_northPole_of_polarization_gap_improvement
    (n : ℕ) [NeZero n] (r : ℝ)
    (hImprove :
      ∀ ⦃η : ℝ⦄, 0 < η →
        ∀ ⦃A : Set (FinRealSphere n)⦄,
          FinRealSphereHalfMassCompetitor n
              (finRealSurfaceProbabilityMeasure n) A →
          finRealSphereNeighbourhoodComplementMass n
                (finRealSurfaceProbabilityMeasure n) r
                (finRealSphereClosedHemisphere n
                  (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
            finRealSphereNeighbourhoodComplementMass n
              (finRealSurfaceProbabilityMeasure n) r A →
          ∃ v : FinRealSphere n,
            finRealSphereNeighbourhoodComplementMass n
                (finRealSurfaceProbabilityMeasure n) r A + η ≤
              finRealSphereNeighbourhoodComplementMass n
                (finRealSurfaceProbabilityMeasure n) r
                (finRealSpherePolarization (finRealSphereReflectionMap n) v A)) :
    finRealSphereHalfMassComplementSup n
        (finRealSurfaceProbabilityMeasure n) r ≤
      finRealSphereNeighbourhoodComplementMass n
        (finRealSurfaceProbabilityMeasure n) r
        (finRealSphereClosedHemisphere n
          (finRealSphereNorthPole n : FinRealEuclideanSpace n)) := by
  exact finRealSphereHalfMassComplementSup_le_northPole_of_quantitative_gap_improvement
    n r (fun {η} hη {A} hA hgap => by
      rcases hImprove hη hA hgap with ⟨v, himprove⟩
      exact ⟨finRealSpherePolarization (finRealSphereReflectionMap n) v A,
        finRealSphereHalfMassCompetitor_polarization v hA, himprove⟩)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- No-input cap comparison in dimensions at least two follows from a
polarization-specific quantitative gap-improvement theorem on `0 < r < π`. -/
theorem sphere_halfMeasure_hemisphereComparisonGeTwo_of_polarization_gap_improvement_pos_lt_pi
    (hImprove :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∀ ⦃A : Set (FinRealSphere n)⦄,
              FinRealSphereHalfMassCompetitor n
                  (finRealSurfaceProbabilityMeasure n) A →
              finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r
                    (finRealSphereClosedHemisphere n
                      (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
                finRealSphereNeighbourhoodComplementMass n
                  (finRealSurfaceProbabilityMeasure n) r A →
              ∃ v : FinRealSphere n,
                finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r A + η ≤
                  finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r
                    (finRealSpherePolarization (finRealSphereReflectionMap n) v A)) :
    sphere_halfMeasure_hemisphereComparisonGeTwo := by
  exact sphere_halfMeasure_hemisphereComparisonGeTwo_of_quantitative_gap_improvement_pos_lt_pi
    (fun n _ hn2 {r} hrpos hrlt {η} hη {A} hA hgap => by
      rcases hImprove n hn2 hrpos hrlt hη hA hgap with ⟨v, himprove⟩
      exact ⟨finRealSpherePolarization (finRealSphereReflectionMap n) v A,
        finRealSphereHalfMassCompetitor_polarization v hA, himprove⟩)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- A near-supremizer can be chosen with arbitrary tolerance `β` while still
forbidding any admissible improvement of size `δ`, provided `β ≤ δ`. -/
theorem exists_finRealSphereHalfMassCompetitor_near_complementSup_no_admissible_delta_improvement
    (n : ℕ) [NeZero n] (r : ℝ)
    {β δ : ℝ} (hβ : 0 < β) (hβδ : β ≤ δ) :
    ∃ A : Set (FinRealSphere n),
      FinRealSphereHalfMassCompetitor n
          (finRealSurfaceProbabilityMeasure n) A ∧
        finRealSphereHalfMassComplementSup n
            (finRealSurfaceProbabilityMeasure n) r - β <
          finRealSphereNeighbourhoodComplementMass n
            (finRealSurfaceProbabilityMeasure n) r A ∧
        ∀ B : Set (FinRealSphere n),
          FinRealSphereHalfMassCompetitor n
              (finRealSurfaceProbabilityMeasure n) B →
            ¬
              finRealSphereNeighbourhoodComplementMass n
                  (finRealSurfaceProbabilityMeasure n) r A + δ ≤
                finRealSphereNeighbourhoodComplementMass n
                  (finRealSurfaceProbabilityMeasure n) r B := by
  rcases exists_finRealSphereHalfMassCompetitor_near_complementSup n r hβ with
    ⟨A, hA, hnear⟩
  refine ⟨A, hA, hnear, ?_⟩
  intro B hB himprove
  have hlt :
      δ < β :=
    finRealSphereHalfMassComplementSup_strictImprovement_lt_tolerance
      n r hB hnear himprove
  linarith

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- A near-supremizer can be chosen above a fixed north-pole gap while still
forbidding any admissible `δ`-improvement.

This packages the maximizing-sequence contradiction in the exact shape needed
by the uniform polarization-improvement argument: the chosen competitor is
already above the north-pole hemisphere by `γ`, and no admissible competitor
can improve it by `δ`. -/
theorem exists_finRealSphereHalfMassCompetitor_above_northPole_no_admissible_delta_improvement
    (n : ℕ) [NeZero n] (r : ℝ)
    {γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ)
    (hgapSup :
      finRealSphereNeighbourhoodComplementMass n
            (finRealSurfaceProbabilityMeasure n) r
            (finRealSphereClosedHemisphere n
              (finRealSphereNorthPole n : FinRealEuclideanSpace n)) +
          2 * γ ≤
        finRealSphereHalfMassComplementSup n
          (finRealSurfaceProbabilityMeasure n) r) :
    ∃ A : Set (FinRealSphere n),
      FinRealSphereHalfMassCompetitor n
          (finRealSurfaceProbabilityMeasure n) A ∧
        finRealSphereNeighbourhoodComplementMass n
              (finRealSurfaceProbabilityMeasure n) r
              (finRealSphereClosedHemisphere n
                (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + γ ≤
          finRealSphereNeighbourhoodComplementMass n
            (finRealSurfaceProbabilityMeasure n) r A ∧
        ∀ B : Set (FinRealSphere n),
          FinRealSphereHalfMassCompetitor n
              (finRealSurfaceProbabilityMeasure n) B →
            ¬
              finRealSphereNeighbourhoodComplementMass n
                  (finRealSurfaceProbabilityMeasure n) r A + δ ≤
                finRealSphereNeighbourhoodComplementMass n
                  (finRealSurfaceProbabilityMeasure n) r B := by
  let β : ℝ := min (δ / 2) γ
  have hβ : 0 < β := by
    dsimp [β]
    exact lt_min (by linarith) hγ
  have hβδ : β ≤ δ := by
    dsimp [β]
    exact (min_le_left _ _).trans (by linarith)
  have hβγ : β ≤ γ := by
    dsimp [β]
    exact min_le_right _ _
  rcases
      exists_finRealSphereHalfMassCompetitor_near_complementSup_no_admissible_delta_improvement
        n r hβ hβδ with
    ⟨A, hA, hnear, hno⟩
  refine ⟨A, hA, ?_, hno⟩
  dsimp [β] at hnear hβγ
  linarith

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Above-gap near-supremizers may be chosen so that every polarization is
admissible, no worse, and still cannot improve by the prescribed `δ`.

This is the compact maximizing-sequence contradiction package used before the
strict polarization-improvement theorem: once the supremum is above the
north-pole hemisphere by a fixed gap, choose a near-supremizer that already
lies above half that gap and forbids every admissible `δ`-improvement. -/
theorem exists_finRealSphereHalfMassCompetitor_above_northPole_all_polarizations_no_delta_improvement
    (n : ℕ) [NeZero n] (r : ℝ)
    {γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ)
    (hgapSup :
      finRealSphereNeighbourhoodComplementMass n
            (finRealSurfaceProbabilityMeasure n) r
            (finRealSphereClosedHemisphere n
              (finRealSphereNorthPole n : FinRealEuclideanSpace n)) +
          2 * γ ≤
        finRealSphereHalfMassComplementSup n
          (finRealSurfaceProbabilityMeasure n) r) :
    ∃ A : Set (FinRealSphere n),
      FinRealSphereHalfMassCompetitor n
          (finRealSurfaceProbabilityMeasure n) A ∧
        finRealSphereNeighbourhoodComplementMass n
              (finRealSurfaceProbabilityMeasure n) r
              (finRealSphereClosedHemisphere n
                (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + γ ≤
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
                  (finRealSurfaceProbabilityMeasure n) r A + δ ≤
                finRealSphereNeighbourhoodComplementMass n
                  (finRealSurfaceProbabilityMeasure n) r
                  (finRealSpherePolarization (finRealSphereReflectionMap n) v A) := by
  rcases
      exists_finRealSphereHalfMassCompetitor_above_northPole_no_admissible_delta_improvement
        n r hγ hδ hgapSup with
    ⟨A, hA, hgap, hno⟩
  refine ⟨A, hA, hgap, ?_⟩
  intro v
  have hpack := finRealSphereHalfMassCompetitor_polarization_objective_ge v r hA
  exact ⟨hpack.1, hpack.2, hno _ hpack.1⟩

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Uniform positive polarization improvement above a fixed hemisphere gap
suffices for normalized north-pole supremum domination.

This is the order-theoretic form closest to Lemma 4.3: the improvement size
`δ` may depend on the gap size `η`, but not on the competitor `A`. -/
theorem finRealSphereHalfMassComplementSup_le_northPole_of_uniform_polarization_gap_improvement
    (n : ℕ) [NeZero n] (r : ℝ)
    (hImprove :
      ∀ ⦃η : ℝ⦄, 0 < η →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ ⦃A : Set (FinRealSphere n)⦄,
            FinRealSphereHalfMassCompetitor n
                (finRealSurfaceProbabilityMeasure n) A →
            finRealSphereNeighbourhoodComplementMass n
                  (finRealSurfaceProbabilityMeasure n) r
                  (finRealSphereClosedHemisphere n
                    (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
              finRealSphereNeighbourhoodComplementMass n
                (finRealSurfaceProbabilityMeasure n) r A →
            ∃ v : FinRealSphere n,
              finRealSphereNeighbourhoodComplementMass n
                  (finRealSurfaceProbabilityMeasure n) r A + δ ≤
                finRealSphereNeighbourhoodComplementMass n
                  (finRealSurfaceProbabilityMeasure n) r
                  (finRealSpherePolarization (finRealSphereReflectionMap n) v A)) :
    finRealSphereHalfMassComplementSup n
        (finRealSurfaceProbabilityMeasure n) r ≤
      finRealSphereNeighbourhoodComplementMass n
        (finRealSurfaceProbabilityMeasure n) r
        (finRealSphereClosedHemisphere n
          (finRealSphereNorthPole n : FinRealEuclideanSpace n)) := by
  by_contra hnot
  let S :=
    finRealSphereHalfMassComplementSup n
      (finRealSurfaceProbabilityMeasure n) r
  let H :=
    finRealSphereNeighbourhoodComplementMass n
      (finRealSurfaceProbabilityMeasure n) r
      (finRealSphereClosedHemisphere n
        (finRealSphereNorthPole n : FinRealEuclideanSpace n))
  have hlt : H < S := lt_of_not_ge hnot
  let η : ℝ := (S - H) / 4
  have hη : 0 < η := by
    dsimp [η]
    linarith
  rcases hImprove hη with ⟨δ, hδ, hImproveδ⟩
  have hgapSup : H + 2 * η ≤ S := by
    dsimp [S, H, η]
    linarith
  rcases
      exists_finRealSphereHalfMassCompetitor_above_northPole_all_polarizations_no_delta_improvement
        n r hη hδ hgapSup with
    ⟨A, hA, hgap, hpolNo⟩
  rcases hImproveδ hA hgap with ⟨v, himprove⟩
  exact (hpolNo v).2.2 himprove

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- No-input cap comparison in dimensions at least two follows from a uniform
positive polarization-improvement theorem on `0 < r < π`. -/
theorem sphere_halfMeasure_hemisphereComparisonGeTwo_of_uniform_polarization_gap_improvement_pos_lt_pi
    (hImprove :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ δ : ℝ, 0 < δ ∧
              ∀ ⦃A : Set (FinRealSphere n)⦄,
                FinRealSphereHalfMassCompetitor n
                    (finRealSurfaceProbabilityMeasure n) A →
                finRealSphereNeighbourhoodComplementMass n
                      (finRealSurfaceProbabilityMeasure n) r
                      (finRealSphereClosedHemisphere n
                        (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
                  finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r A →
                ∃ v : FinRealSphere n,
                  finRealSphereNeighbourhoodComplementMass n
                      (finRealSurfaceProbabilityMeasure n) r A + δ ≤
                    finRealSphereNeighbourhoodComplementMass n
                      (finRealSurfaceProbabilityMeasure n) r
                      (finRealSpherePolarization (finRealSphereReflectionMap n) v A)) :
    sphere_halfMeasure_hemisphereComparisonGeTwo := by
  exact sphere_halfMeasure_hemisphereComparisonGeTwo_of_complementSup_le_northPole_pos_lt_pi
    (fun n _ hn2 {r} hrpos hrlt =>
      finRealSphereHalfMassComplementSup_le_northPole_of_uniform_polarization_gap_improvement
        n r (hImprove n hn2 hrpos hrlt))

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Real gains in neighbourhood-complement objective obtained by polarizing a
fixed competitor. -/
def finRealSpherePolarizationObjectiveGainValues
    (n : ℕ) (r : ℝ) (A : Set (FinRealSphere n)) : Set ℝ :=
  {t | ∃ v : FinRealSphere n,
    t =
      finRealSphereNeighbourhoodComplementMass n
          (finRealSurfaceProbabilityMeasure n) r
          (finRealSpherePolarization (finRealSphereReflectionMap n) v A) -
        finRealSphereNeighbourhoodComplementMass n
          (finRealSurfaceProbabilityMeasure n) r A}

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- A positive lower bound on the supremum of polarization gains yields an
actual polarization direction with half that gain. -/
theorem exists_finRealSpherePolarization_objective_improvement_of_gainSup_lower
    (n : ℕ) [NeZero n] (r : ℝ) (A : Set (FinRealSphere n))
    {δ : ℝ} (hδ : 0 < δ)
    (hSup :
      δ ≤ sSup (finRealSpherePolarizationObjectiveGainValues n r A)) :
    ∃ v : FinRealSphere n,
      finRealSphereNeighbourhoodComplementMass n
          (finRealSurfaceProbabilityMeasure n) r A + δ / 2 ≤
        finRealSphereNeighbourhoodComplementMass n
          (finRealSurfaceProbabilityMeasure n) r
          (finRealSpherePolarization (finRealSphereReflectionMap n) v A) := by
  let gains := finRealSpherePolarizationObjectiveGainValues n r A
  have hne : gains.Nonempty := by
    refine ⟨finRealSphereNeighbourhoodComplementMass n
        (finRealSurfaceProbabilityMeasure n) r
        (finRealSpherePolarization (finRealSphereReflectionMap n)
          (finRealSphereNorthPole n) A) -
      finRealSphereNeighbourhoodComplementMass n
        (finRealSurfaceProbabilityMeasure n) r A, ?_⟩
    exact ⟨finRealSphereNorthPole n, rfl⟩
  have hlt : δ / 2 < sSup gains := by
    dsimp [gains] at hSup ⊢
    linarith
  rcases exists_lt_of_lt_csSup hne hlt with ⟨t, ht, htle⟩
  rcases ht with ⟨v, rfl⟩
  refine ⟨v, ?_⟩
  linarith

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- A uniform positive lower bound on the supremum of polarization gains gives
the corresponding uniform actual-polarization improvement theorem.

This is the bridge from the Lemma 4.3 `sSup` output to the stricter
polarization-direction API: after obtaining `δ ≤ sSup gains`, choose a
direction that realizes more than `δ / 2` of that gain. -/
theorem uniform_polarization_gap_improvement_of_uniform_polarization_gainSup_lower_pos_lt_pi
    (hImprove :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ δ : ℝ, 0 < δ ∧
              ∀ ⦃A : Set (FinRealSphere n)⦄,
                FinRealSphereHalfMassCompetitor n
                    (finRealSurfaceProbabilityMeasure n) A →
                finRealSphereNeighbourhoodComplementMass n
                      (finRealSurfaceProbabilityMeasure n) r
                      (finRealSphereClosedHemisphere n
                        (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
                  finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r A →
                δ ≤ sSup (finRealSpherePolarizationObjectiveGainValues n r A)) :
    ∀ (n : ℕ) [NeZero n], 2 ≤ n →
      ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
        ∀ ⦃η : ℝ⦄, 0 < η →
          ∃ δ : ℝ, 0 < δ ∧
            ∀ ⦃A : Set (FinRealSphere n)⦄,
              FinRealSphereHalfMassCompetitor n
                  (finRealSurfaceProbabilityMeasure n) A →
              finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r
                    (finRealSphereClosedHemisphere n
                      (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
                finRealSphereNeighbourhoodComplementMass n
                  (finRealSurfaceProbabilityMeasure n) r A →
              ∃ v : FinRealSphere n,
                finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r A + δ ≤
                  finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r
                    (finRealSpherePolarization (finRealSphereReflectionMap n) v A) := by
  intro n _ hn r hrpos hrlt η hη
  rcases hImprove n hn hrpos hrlt hη with ⟨δ, hδ, hImproveδ⟩
  refine ⟨δ / 2, by linarith, ?_⟩
  intro A hA hgap
  exact
    exists_finRealSpherePolarization_objective_improvement_of_gainSup_lower
      n r A hδ (hImproveδ hA hgap)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Above-gap near-supremizers may be chosen so that a prescribed positive
lower bound on the supremum of polarization gains is impossible.

This is the gain-supremum form of the maximizing-sequence contradiction:
if the half-mass complement supremum is separated from the north-pole
hemisphere objective, choose a competitor above half the gap whose every
polarization forbids a `δ / 2` improvement.  A lower bound
`δ ≤ sSup gains` would produce exactly such a forbidden polarization. -/
theorem exists_finRealSphereHalfMassCompetitor_above_northPole_no_gainSup_lower
    (n : ℕ) [NeZero n] (r : ℝ)
    {γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ)
    (hgapSup :
      finRealSphereNeighbourhoodComplementMass n
            (finRealSurfaceProbabilityMeasure n) r
            (finRealSphereClosedHemisphere n
              (finRealSphereNorthPole n : FinRealEuclideanSpace n)) +
          2 * γ ≤
        finRealSphereHalfMassComplementSup n
          (finRealSurfaceProbabilityMeasure n) r) :
    ∃ A : Set (FinRealSphere n),
      FinRealSphereHalfMassCompetitor n
          (finRealSurfaceProbabilityMeasure n) A ∧
        finRealSphereNeighbourhoodComplementMass n
              (finRealSurfaceProbabilityMeasure n) r
              (finRealSphereClosedHemisphere n
                (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + γ ≤
          finRealSphereNeighbourhoodComplementMass n
            (finRealSurfaceProbabilityMeasure n) r A ∧
        ¬ δ ≤ sSup (finRealSpherePolarizationObjectiveGainValues n r A) := by
  have hδhalf : 0 < δ / 2 := by linarith
  rcases
      exists_finRealSphereHalfMassCompetitor_above_northPole_all_polarizations_no_delta_improvement
        n r hγ hδhalf hgapSup with
    ⟨A, hA, hgap, hpolNo⟩
  refine ⟨A, hA, hgap, ?_⟩
  intro hSup
  rcases exists_finRealSpherePolarization_objective_improvement_of_gainSup_lower
      n r A hδ hSup with
    ⟨v, himprove⟩
  exact (hpolNo v).2.2 himprove

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- A uniform positive lower bound on the supremum of polarization gains
suffices for normalized north-pole supremum domination. -/
theorem finRealSphereHalfMassComplementSup_le_northPole_of_uniform_polarization_gainSup_lower
    (n : ℕ) [NeZero n] (r : ℝ)
    (hImprove :
      ∀ ⦃η : ℝ⦄, 0 < η →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ ⦃A : Set (FinRealSphere n)⦄,
            FinRealSphereHalfMassCompetitor n
                (finRealSurfaceProbabilityMeasure n) A →
            finRealSphereNeighbourhoodComplementMass n
                  (finRealSurfaceProbabilityMeasure n) r
                  (finRealSphereClosedHemisphere n
                    (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
              finRealSphereNeighbourhoodComplementMass n
                (finRealSurfaceProbabilityMeasure n) r A →
            δ ≤ sSup (finRealSpherePolarizationObjectiveGainValues n r A)) :
    finRealSphereHalfMassComplementSup n
        (finRealSurfaceProbabilityMeasure n) r ≤
      finRealSphereNeighbourhoodComplementMass n
        (finRealSurfaceProbabilityMeasure n) r
        (finRealSphereClosedHemisphere n
          (finRealSphereNorthPole n : FinRealEuclideanSpace n)) := by
  by_contra hnot
  let S :=
    finRealSphereHalfMassComplementSup n
      (finRealSurfaceProbabilityMeasure n) r
  let H :=
    finRealSphereNeighbourhoodComplementMass n
      (finRealSurfaceProbabilityMeasure n) r
      (finRealSphereClosedHemisphere n
        (finRealSphereNorthPole n : FinRealEuclideanSpace n))
  have hlt : H < S := lt_of_not_ge hnot
  let η : ℝ := (S - H) / 4
  have hη : 0 < η := by
    dsimp [η]
    linarith
  rcases hImprove hη with ⟨δ, hδ, hImproveδ⟩
  have hgapSup : H + 2 * η ≤ S := by
    dsimp [S, H, η]
    linarith
  rcases
      exists_finRealSphereHalfMassCompetitor_above_northPole_no_gainSup_lower
        n r hη hδ hgapSup with
    ⟨A, hA, hgap, hnoSup⟩
  exact hnoSup (hImproveδ hA hgap)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- No-input cap comparison in dimensions at least two follows from a uniform
lower bound on the supremum of polarization gains on `0 < r < π`. -/
theorem sphere_halfMeasure_hemisphereComparisonGeTwo_of_uniform_polarization_gainSup_lower_pos_lt_pi
    (hImprove :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ δ : ℝ, 0 < δ ∧
              ∀ ⦃A : Set (FinRealSphere n)⦄,
                FinRealSphereHalfMassCompetitor n
                    (finRealSurfaceProbabilityMeasure n) A →
                finRealSphereNeighbourhoodComplementMass n
                      (finRealSurfaceProbabilityMeasure n) r
                      (finRealSphereClosedHemisphere n
                        (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
                  finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r A →
                δ ≤ sSup (finRealSpherePolarizationObjectiveGainValues n r A)) :
    sphere_halfMeasure_hemisphereComparisonGeTwo := by
  exact sphere_halfMeasure_hemisphereComparisonGeTwo_of_complementSup_le_northPole_pos_lt_pi
    (fun n _ hn2 {r} hrpos hrlt =>
      finRealSphereHalfMassComplementSup_le_northPole_of_uniform_polarization_gainSup_lower
        n r (hImprove n hn2 hrpos hrlt))

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Lemma 4.3 in measure-trimming form gives a lower bound on the supremum of
polarization objective gains when its `supDelta` parameter is instantiated by
that supremum. -/
theorem finRealSpherePolarization_gainSup_lower_of_lemma43_measure_trimming
    (n : ℕ) [NeZero n] (hn : 2 ≤ n) (r : ℝ)
    (A C bandPlus bandMinus : Set (FinRealSphere n))
    {eps tau avg : ℝ}
    (heps : 0 < eps) (htau : 0 < tau)
    (hA : MeasurableSet A) (hC : MeasurableSet C)
    (hBandPlus : MeasurableSet bandPlus)
    (hBandMinus : MeasurableSet bandMinus)
    (hbalance :
      (finRealSurfaceProbabilityMeasure n).real
          (finRealPolarizationMiss C A) =
        (finRealSurfaceProbabilityMeasure n).real
          (finRealPolarizationExtra C A))
    (hfar : eps ≤ (finRealSurfaceProbabilityMeasure n).real (C ∆ A))
    (hbandPlus :
      (finRealSurfaceProbabilityMeasure n).real bandPlus ≤ eps / 4)
    (hbandMinus :
      (finRealSurfaceProbabilityMeasure n).real bandMinus ≤ eps / 4)
    (hRect :
      SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tau
        (finRealPolarizationMuMinus C A bandMinus)
        (finRealPolarizationMuPlus C A bandPlus)
        avg)
    (havgLeGainSup :
      avg ≤ sSup (finRealSpherePolarizationObjectiveGainValues n r A)) :
    tau * eps ^ 2 / ((2 : ℝ) ^ (n + 1)) ≤
      sSup (finRealSpherePolarizationObjectiveGainValues n r A) := by
  exact
    (lemma43_strict_improvement_from_measure_trimming
      n hn heps htau hC hA hBandPlus hBandMinus
      hbalance hfar hbandPlus hbandMinus hRect havgLeGainSup).2

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- If two measurable sets have the same real measure, then the two one-sided
pieces of their symmetric difference have the same real measure. -/
theorem measureReal_diff_eq_diff_of_measureReal_eq
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {A C : Set Ω}
    (hA : MeasurableSet A) (hC : MeasurableSet C)
    (hmass : μ.real C = μ.real A) :
    μ.real (C \ A) = μ.real (A \ C) := by
  have hCdecomp :
      μ.real (C \ A) + μ.real (C ∩ A) = μ.real C :=
    measureReal_diff_add_inter (μ := μ) (s := C) (t := A) hA
  have hAdecomp :
      μ.real (A \ C) + μ.real (A ∩ C) = μ.real A :=
    measureReal_diff_add_inter (μ := μ) (s := A) (t := C) hC
  have hinter : μ.real (A ∩ C) = μ.real (C ∩ A) := by
    rw [Set.inter_comm]
  linarith

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Same-measure cap/model data supply the balance hypothesis in the
polarization trimming form of Lemma 4.3. -/
theorem finRealPolarization_balance_of_measureReal_eq
    {n : ℕ} [NeZero n] {A C : Set (FinRealSphere n)}
    (hA : MeasurableSet A) (hC : MeasurableSet C)
    (hmass :
      (finRealSurfaceProbabilityMeasure n).real C =
        (finRealSurfaceProbabilityMeasure n).real A) :
    (finRealSurfaceProbabilityMeasure n).real
        (finRealPolarizationMiss C A) =
      (finRealSurfaceProbabilityMeasure n).real
        (finRealPolarizationExtra C A) := by
  haveI : IsFiniteMeasure (finRealSurfaceProbabilityMeasure n) := inferInstance
  simpa [finRealPolarizationMiss, finRealPolarizationExtra] using
    measureReal_diff_eq_diff_of_measureReal_eq
      (μ := finRealSurfaceProbabilityMeasure n) hA hC hmass

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Lemma 4.3 gain-supremum supplier with the balance condition generated from
equal real mass of the model set and the competitor. -/
theorem finRealSpherePolarization_gainSup_lower_of_lemma43_measure_trimming_equal_mass
    (n : ℕ) [NeZero n] (hn : 2 ≤ n) (r : ℝ)
    (A C bandPlus bandMinus : Set (FinRealSphere n))
    {eps tau avg : ℝ}
    (heps : 0 < eps) (htau : 0 < tau)
    (hA : MeasurableSet A) (hC : MeasurableSet C)
    (hBandPlus : MeasurableSet bandPlus)
    (hBandMinus : MeasurableSet bandMinus)
    (hmass :
      (finRealSurfaceProbabilityMeasure n).real C =
        (finRealSurfaceProbabilityMeasure n).real A)
    (hfar : eps ≤ (finRealSurfaceProbabilityMeasure n).real (C ∆ A))
    (hbandPlus :
      (finRealSurfaceProbabilityMeasure n).real bandPlus ≤ eps / 4)
    (hbandMinus :
      (finRealSurfaceProbabilityMeasure n).real bandMinus ≤ eps / 4)
    (hRect :
      SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tau
        (finRealPolarizationMuMinus C A bandMinus)
        (finRealPolarizationMuPlus C A bandPlus)
        avg)
    (havgLeGainSup :
      avg ≤ sSup (finRealSpherePolarizationObjectiveGainValues n r A)) :
    tau * eps ^ 2 / ((2 : ℝ) ^ (n + 1)) ≤
      sSup (finRealSpherePolarizationObjectiveGainValues n r A) := by
  exact
    finRealSpherePolarization_gainSup_lower_of_lemma43_measure_trimming
      n hn r A C bandPlus bandMinus heps htau hA hC
      hBandPlus hBandMinus
      (finRealPolarization_balance_of_measureReal_eq hA hC hmass)
      hfar hbandPlus hbandMinus hRect havgLeGainSup

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- A fully geometric Lemma 4.3 data supplier, instantiated with the supremum
of polarization gains as `supDelta`, closes normalized north-pole supremum
domination.

The remaining assumptions are exactly the geometric/content part: for each
positive hemisphere gap, choose uniform `eps,tau`, and for each competitor
above that gap provide the cap model `C`, trimmed bands, rectangular block
bound, and average-to-gain-supremum comparison. -/
theorem finRealSphereHalfMassComplementSup_le_northPole_of_lemma43_measure_trimming_gainSup
    (n : ℕ) [NeZero n] (hn : 2 ≤ n) (r : ℝ)
    (hData :
      ∀ ⦃η : ℝ⦄, 0 < η →
        ∃ eps tau : ℝ, 0 < eps ∧ 0 < tau ∧
          ∀ ⦃A : Set (FinRealSphere n)⦄,
            FinRealSphereHalfMassCompetitor n
                (finRealSurfaceProbabilityMeasure n) A →
            finRealSphereNeighbourhoodComplementMass n
                  (finRealSurfaceProbabilityMeasure n) r
                  (finRealSphereClosedHemisphere n
                    (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
              finRealSphereNeighbourhoodComplementMass n
                (finRealSurfaceProbabilityMeasure n) r A →
            ∃ C bandPlus bandMinus : Set (FinRealSphere n),
              ∃ avg : ℝ,
                MeasurableSet C ∧
                MeasurableSet bandPlus ∧
                MeasurableSet bandMinus ∧
                (finRealSurfaceProbabilityMeasure n).real
                    (finRealPolarizationMiss C A) =
                  (finRealSurfaceProbabilityMeasure n).real
                    (finRealPolarizationExtra C A) ∧
                eps ≤ (finRealSurfaceProbabilityMeasure n).real (C ∆ A) ∧
                (finRealSurfaceProbabilityMeasure n).real bandPlus ≤ eps / 4 ∧
                (finRealSurfaceProbabilityMeasure n).real bandMinus ≤ eps / 4 ∧
                SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tau
                  (finRealPolarizationMuMinus C A bandMinus)
                  (finRealPolarizationMuPlus C A bandPlus)
                  avg ∧
                avg ≤ sSup (finRealSpherePolarizationObjectiveGainValues n r A)) :
    finRealSphereHalfMassComplementSup n
        (finRealSurfaceProbabilityMeasure n) r ≤
      finRealSphereNeighbourhoodComplementMass n
        (finRealSurfaceProbabilityMeasure n) r
        (finRealSphereClosedHemisphere n
          (finRealSphereNorthPole n : FinRealEuclideanSpace n)) := by
  exact
    finRealSphereHalfMassComplementSup_le_northPole_of_uniform_polarization_gainSup_lower
      n r (fun {η} hη => by
        rcases hData hη with ⟨eps, tau, heps, htau, hDataη⟩
        refine ⟨tau * eps ^ 2 / ((2 : ℝ) ^ (n + 1)), ?_, ?_⟩
        · positivity
        · intro A hA hgap
          rcases hDataη hA hgap with
            ⟨C, bandPlus, bandMinus, avg,
              hC, hBandPlus, hBandMinus, hbalance, hfar,
              hbandPlus, hbandMinus, hRect, havgLeGainSup⟩
          exact
            finRealSpherePolarization_gainSup_lower_of_lemma43_measure_trimming
              n hn r A C bandPlus bandMinus
              heps htau hA.1 hC hBandPlus hBandMinus
              hbalance hfar hbandPlus hbandMinus hRect havgLeGainSup)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- No-input cap comparison in dimensions at least two follows from the
geometric Lemma 4.3 data supplier on `0 < r < π`. -/
theorem sphere_halfMeasure_hemisphereComparisonGeTwo_of_lemma43_measure_trimming_gainSup_pos_lt_pi
    (hData :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tau : ℝ, 0 < eps ∧ 0 < tau ∧
              ∀ ⦃A : Set (FinRealSphere n)⦄,
                FinRealSphereHalfMassCompetitor n
                    (finRealSurfaceProbabilityMeasure n) A →
                finRealSphereNeighbourhoodComplementMass n
                      (finRealSurfaceProbabilityMeasure n) r
                      (finRealSphereClosedHemisphere n
                        (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
                  finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r A →
                ∃ C bandPlus bandMinus : Set (FinRealSphere n),
                  ∃ avg : ℝ,
                    MeasurableSet C ∧
                    MeasurableSet bandPlus ∧
                    MeasurableSet bandMinus ∧
                    (finRealSurfaceProbabilityMeasure n).real
                        (finRealPolarizationMiss C A) =
                      (finRealSurfaceProbabilityMeasure n).real
                        (finRealPolarizationExtra C A) ∧
                    eps ≤ (finRealSurfaceProbabilityMeasure n).real (C ∆ A) ∧
                    (finRealSurfaceProbabilityMeasure n).real bandPlus ≤ eps / 4 ∧
                    (finRealSurfaceProbabilityMeasure n).real bandMinus ≤ eps / 4 ∧
                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tau
                      (finRealPolarizationMuMinus C A bandMinus)
                      (finRealPolarizationMuPlus C A bandPlus)
                      avg ∧
                    avg ≤ sSup (finRealSpherePolarizationObjectiveGainValues n r A)) :
    sphere_halfMeasure_hemisphereComparisonGeTwo := by
  exact sphere_halfMeasure_hemisphereComparisonGeTwo_of_complementSup_le_northPole_pos_lt_pi
    (fun n _ hn2 {r} hrpos hrlt =>
      finRealSphereHalfMassComplementSup_le_northPole_of_lemma43_measure_trimming_gainSup
      n hn2 r (hData n hn2 hrpos hrlt))

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Variant of the Lemma 4.3 data supplier where the symmetric-difference
balance is produced from the model set having the same mass as the competitor. -/
theorem finRealSphereHalfMassComplementSup_le_northPole_of_lemma43_measure_trimming_gainSup_equal_mass
    (n : ℕ) [NeZero n] (hn : 2 ≤ n) (r : ℝ)
    (hData :
      ∀ ⦃η : ℝ⦄, 0 < η →
        ∃ eps tau : ℝ, 0 < eps ∧ 0 < tau ∧
          ∀ ⦃A : Set (FinRealSphere n)⦄,
            FinRealSphereHalfMassCompetitor n
                (finRealSurfaceProbabilityMeasure n) A →
            finRealSphereNeighbourhoodComplementMass n
                  (finRealSurfaceProbabilityMeasure n) r
                  (finRealSphereClosedHemisphere n
                    (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
              finRealSphereNeighbourhoodComplementMass n
                (finRealSurfaceProbabilityMeasure n) r A →
            ∃ C bandPlus bandMinus : Set (FinRealSphere n),
              ∃ avg : ℝ,
                MeasurableSet C ∧
                MeasurableSet bandPlus ∧
                MeasurableSet bandMinus ∧
                (finRealSurfaceProbabilityMeasure n).real C =
                  (finRealSurfaceProbabilityMeasure n).real A ∧
                eps ≤ (finRealSurfaceProbabilityMeasure n).real (C ∆ A) ∧
                (finRealSurfaceProbabilityMeasure n).real bandPlus ≤ eps / 4 ∧
                (finRealSurfaceProbabilityMeasure n).real bandMinus ≤ eps / 4 ∧
                SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tau
                  (finRealPolarizationMuMinus C A bandMinus)
                  (finRealPolarizationMuPlus C A bandPlus)
                  avg ∧
                avg ≤ sSup (finRealSpherePolarizationObjectiveGainValues n r A)) :
    finRealSphereHalfMassComplementSup n
        (finRealSurfaceProbabilityMeasure n) r ≤
      finRealSphereNeighbourhoodComplementMass n
        (finRealSurfaceProbabilityMeasure n) r
        (finRealSphereClosedHemisphere n
          (finRealSphereNorthPole n : FinRealEuclideanSpace n)) := by
  exact
    finRealSphereHalfMassComplementSup_le_northPole_of_uniform_polarization_gainSup_lower
      n r (fun {η} hη => by
        rcases hData hη with ⟨eps, tau, heps, htau, hDataη⟩
        refine ⟨tau * eps ^ 2 / ((2 : ℝ) ^ (n + 1)), ?_, ?_⟩
        · positivity
        · intro A hA hgap
          rcases hDataη hA hgap with
            ⟨C, bandPlus, bandMinus, avg,
              hC, hBandPlus, hBandMinus, hmass, hfar,
              hbandPlus, hbandMinus, hRect, havgLeGainSup⟩
          exact
            finRealSpherePolarization_gainSup_lower_of_lemma43_measure_trimming_equal_mass
              n hn r A C bandPlus bandMinus
              heps htau hA.1 hC hBandPlus hBandMinus
              hmass hfar hbandPlus hbandMinus hRect havgLeGainSup)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Same-mass Lemma 4.3 data gives the direct uniform gain-supremum supplier
used by the sharp modular upper endpoint. -/
theorem uniform_polarization_gainSup_lower_of_lemma43_measure_trimming_gainSup_equal_mass_pos_lt_pi
    (hData :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tau : ℝ, 0 < eps ∧ 0 < tau ∧
              ∀ ⦃A : Set (FinRealSphere n)⦄,
                FinRealSphereHalfMassCompetitor n
                    (finRealSurfaceProbabilityMeasure n) A →
                finRealSphereNeighbourhoodComplementMass n
                      (finRealSurfaceProbabilityMeasure n) r
                      (finRealSphereClosedHemisphere n
                        (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
                  finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r A →
                ∃ C bandPlus bandMinus : Set (FinRealSphere n),
                  ∃ avg : ℝ,
                    MeasurableSet C ∧
                    MeasurableSet bandPlus ∧
                    MeasurableSet bandMinus ∧
                    (finRealSurfaceProbabilityMeasure n).real C =
                      (finRealSurfaceProbabilityMeasure n).real A ∧
                    eps ≤ (finRealSurfaceProbabilityMeasure n).real (C ∆ A) ∧
                    (finRealSurfaceProbabilityMeasure n).real bandPlus ≤ eps / 4 ∧
                    (finRealSurfaceProbabilityMeasure n).real bandMinus ≤ eps / 4 ∧
                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tau
                      (finRealPolarizationMuMinus C A bandMinus)
                      (finRealPolarizationMuPlus C A bandPlus)
                      avg ∧
                    avg ≤ sSup (finRealSpherePolarizationObjectiveGainValues n r A)) :
    ∀ (n : ℕ) [NeZero n], 2 ≤ n →
      ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
        ∀ ⦃η : ℝ⦄, 0 < η →
          ∃ δ : ℝ, 0 < δ ∧
            ∀ ⦃A : Set (FinRealSphere n)⦄,
              FinRealSphereHalfMassCompetitor n
                  (finRealSurfaceProbabilityMeasure n) A →
              finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r
                    (finRealSphereClosedHemisphere n
                      (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
                finRealSphereNeighbourhoodComplementMass n
                  (finRealSurfaceProbabilityMeasure n) r A →
              δ ≤
                sSup (finRealSpherePolarizationObjectiveGainValues n r A) := by
  intro n _ hn r hrpos hrlt η hη
  rcases hData n hn hrpos hrlt hη with ⟨eps, tau, heps, htau, hDataη⟩
  refine ⟨tau * eps ^ 2 / ((2 : ℝ) ^ (n + 1)), ?_, ?_⟩
  · positivity
  · intro A hA hgap
    rcases hDataη hA hgap with
      ⟨C, bandPlus, bandMinus, avg,
        hC, hBandPlus, hBandMinus, hmass, hfar,
        hbandPlus, hbandMinus, hRect, havgLeGainSup⟩
    exact
      finRealSpherePolarization_gainSup_lower_of_lemma43_measure_trimming_equal_mass
        n hn r A C bandPlus bandMinus
        heps htau hA.1 hC hBandPlus hBandMinus
        hmass hfar hbandPlus hbandMinus hRect havgLeGainSup

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- No-input cap comparison in dimensions at least two follows from a
same-mass geometric Lemma 4.3 data supplier on `0 < r < π`. -/
theorem sphere_halfMeasure_hemisphereComparisonGeTwo_of_lemma43_measure_trimming_gainSup_equal_mass_pos_lt_pi
    (hData :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tau : ℝ, 0 < eps ∧ 0 < tau ∧
              ∀ ⦃A : Set (FinRealSphere n)⦄,
                FinRealSphereHalfMassCompetitor n
                    (finRealSurfaceProbabilityMeasure n) A →
                finRealSphereNeighbourhoodComplementMass n
                      (finRealSurfaceProbabilityMeasure n) r
                      (finRealSphereClosedHemisphere n
                        (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
                  finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r A →
                ∃ C bandPlus bandMinus : Set (FinRealSphere n),
                  ∃ avg : ℝ,
                    MeasurableSet C ∧
                    MeasurableSet bandPlus ∧
                    MeasurableSet bandMinus ∧
                    (finRealSurfaceProbabilityMeasure n).real C =
                      (finRealSurfaceProbabilityMeasure n).real A ∧
                    eps ≤ (finRealSurfaceProbabilityMeasure n).real (C ∆ A) ∧
                    (finRealSurfaceProbabilityMeasure n).real bandPlus ≤ eps / 4 ∧
                    (finRealSurfaceProbabilityMeasure n).real bandMinus ≤ eps / 4 ∧
                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tau
                      (finRealPolarizationMuMinus C A bandMinus)
                      (finRealPolarizationMuPlus C A bandPlus)
                      avg ∧
                    avg ≤ sSup (finRealSpherePolarizationObjectiveGainValues n r A)) :
    sphere_halfMeasure_hemisphereComparisonGeTwo := by
  exact sphere_halfMeasure_hemisphereComparisonGeTwo_of_complementSup_le_northPole_pos_lt_pi
    (fun n _ hn2 {r} hrpos hrlt =>
      finRealSphereHalfMassComplementSup_le_northPole_of_lemma43_measure_trimming_gainSup_equal_mass
        n hn2 r (hData n hn2 hrpos hrlt))

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Atomlessness of the height distribution gives arbitrarily thin concrete
height bands with small surface mass. -/
theorem exists_finRealSphereHeightBands_small
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (pole : FinRealSphere n) (a eps : ℝ) (heps : 0 < eps) :
    ∃ tau : ℝ, 0 < tau ∧
      (finRealSurfaceProbabilityMeasure n).real
          (finRealSphereHeightBandAbove n pole a tau) ≤ eps / 4 ∧
      (finRealSurfaceProbabilityMeasure n).real
          (finRealSphereHeightBandBelow n pole a tau) ≤ eps / 4 := by
  let μ := finRealSurfaceProbabilityMeasure n
  let ν : Measure ℝ := Measure.map (finRealSphereHeight n pole) μ
  haveI : NoAtoms ν :=
    (finRealSphereHeightDistributionAtomless_concrete n hn) pole
  have hlim :
      Tendsto (fun δ : ℝ => ν (Icc (a - δ) (a + δ)))
        (nhds (0 : ℝ)) (nhds (0 : ℝ≥0∞)) := by
    simpa [ν] using tendsto_measure_Icc ν a
  have htarget :
      {x : ℝ≥0∞ | x < ENNReal.ofReal (eps / 4)}
        ∈ nhds (0 : ℝ≥0∞) := by
    apply Iio_mem_nhds
    exact ENNReal.ofReal_pos.mpr (by linarith)
  have hev :
      {δ : ℝ | ν (Icc (a - δ) (a + δ)) <
          ENNReal.ofReal (eps / 4)} ∈ nhds (0 : ℝ) :=
    hlim htarget
  rcases Metric.mem_nhds_iff.mp hev with ⟨r, hrpos, hrsub⟩
  let tau : ℝ := r / 2
  have htau : 0 < tau := by
    dsimp [tau]
    positivity
  have htau_mem : tau ∈ Metric.ball (0 : ℝ) r := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [tau]
    rw [sub_zero, abs_of_nonneg]
    · linarith
    · positivity
  have hsmall :
      ν (Icc (a - tau) (a + tau)) < ENNReal.ofReal (eps / 4) :=
    hrsub htau_mem
  have hheight_meas : Measurable (finRealSphereHeight n pole) := by
    unfold finRealSphereHeight
    fun_prop
  have hIcc_meas : MeasurableSet (Icc (a - tau) (a + tau)) :=
    measurableSet_Icc
  have hmap :
      ν (Icc (a - tau) (a + tau)) =
        μ ((finRealSphereHeight n pole) ⁻¹' Icc (a - tau) (a + tau)) := by
    simpa [ν] using
      (MeasureTheory.Measure.map_apply
        (μ := μ) (f := finRealSphereHeight n pole) hheight_meas hIcc_meas)
  have hbandAbove_sub :
      finRealSphereHeightBandAbove n pole a tau ⊆
        (finRealSphereHeight n pole) ⁻¹' Icc (a - tau) (a + tau) := by
    intro x hx
    rcases hx with ⟨hlo, hhi⟩
    exact ⟨by linarith [htau.le], hhi⟩
  have hbandBelow_sub :
      finRealSphereHeightBandBelow n pole a tau ⊆
        (finRealSphereHeight n pole) ⁻¹' Icc (a - tau) (a + tau) := by
    intro x hx
    rcases hx with ⟨hlo, hhi⟩
    exact ⟨hlo, by linarith [htau.le]⟩
  have hpre_lt :
      μ ((finRealSphereHeight n pole) ⁻¹' Icc (a - tau) (a + tau)) <
        ENNReal.ofReal (eps / 4) := by
    rwa [hmap] at hsmall
  have habove_le_enn :
      μ (finRealSphereHeightBandAbove n pole a tau) ≤
        ENNReal.ofReal (eps / 4) :=
    le_of_lt ((measure_mono hbandAbove_sub).trans_lt hpre_lt)
  have hbelow_le_enn :
      μ (finRealSphereHeightBandBelow n pole a tau) ≤
        ENNReal.ofReal (eps / 4) :=
    le_of_lt ((measure_mono hbandBelow_sub).trans_lt hpre_lt)
  have hof_ne_top : ENNReal.ofReal (eps / 4) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have heps4_nonneg : 0 ≤ eps / 4 := by
    positivity
  have habove :
      μ.real (finRealSphereHeightBandAbove n pole a tau) ≤ eps / 4 := by
    calc
      μ.real (finRealSphereHeightBandAbove n pole a tau)
          = (μ (finRealSphereHeightBandAbove n pole a tau)).toReal := rfl
      _ ≤ (ENNReal.ofReal (eps / 4)).toReal :=
          ENNReal.toReal_mono hof_ne_top habove_le_enn
      _ = eps / 4 := ENNReal.toReal_ofReal heps4_nonneg
  have hbelow :
      μ.real (finRealSphereHeightBandBelow n pole a tau) ≤ eps / 4 := by
    calc
      μ.real (finRealSphereHeightBandBelow n pole a tau)
          = (μ (finRealSphereHeightBandBelow n pole a tau)).toReal := rfl
      _ ≤ (ENNReal.ofReal (eps / 4)).toReal :=
          ENNReal.toReal_mono hof_ne_top hbelow_le_enn
      _ = eps / 4 := ENNReal.toReal_ofReal heps4_nonneg
  exact ⟨tau, htau, by simpa [μ] using habove, by simpa [μ] using hbelow⟩

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Upper height bands are monotone in their thickness. -/
theorem finRealSphereHeightBandAbove_subset_of_le
    (n : ℕ) (pole : FinRealSphere n) (a : ℝ) {tau₁ tau₂ : ℝ}
    (htau : tau₁ ≤ tau₂) :
    finRealSphereHeightBandAbove n pole a tau₁ ⊆
      finRealSphereHeightBandAbove n pole a tau₂ := by
  intro x hx
  rcases hx with ⟨hlo, hhi⟩
  exact ⟨hlo, by linarith⟩

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Lower height bands are monotone in their thickness. -/
theorem finRealSphereHeightBandBelow_subset_of_le
    (n : ℕ) (pole : FinRealSphere n) (a : ℝ) {tau₁ tau₂ : ℝ}
    (htau : tau₁ ≤ tau₂) :
    finRealSphereHeightBandBelow n pole a tau₁ ⊆
      finRealSphereHeightBandBelow n pole a tau₂ := by
  intro x hx
  rcases hx with ⟨hlo, hhi⟩
  exact ⟨by linarith, hhi⟩

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The thin height bands can be chosen below any prescribed positive
thickness. -/
theorem exists_finRealSphereHeightBands_small_le
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (pole : FinRealSphere n) (a eps tauMax : ℝ)
    (heps : 0 < eps) (htauMax : 0 < tauMax) :
    ∃ tau : ℝ, 0 < tau ∧ tau ≤ tauMax ∧
      (finRealSurfaceProbabilityMeasure n).real
          (finRealSphereHeightBandAbove n pole a tau) ≤ eps / 4 ∧
      (finRealSurfaceProbabilityMeasure n).real
          (finRealSphereHeightBandBelow n pole a tau) ≤ eps / 4 := by
  rcases exists_finRealSphereHeightBands_small n hn pole a eps heps with
    ⟨tau₀, htau₀, habove₀, hbelow₀⟩
  let tau : ℝ := min tau₀ (tauMax / 2)
  have htau : 0 < tau := by
    dsimp [tau]
    exact lt_min htau₀ (by positivity)
  have htau_le_tau₀ : tau ≤ tau₀ := by
    dsimp [tau]
    exact min_le_left _ _
  have htau_le_max : tau ≤ tauMax := by
    dsimp [tau]
    exact (min_le_right _ _).trans (by linarith)
  have habove_sub :
      finRealSphereHeightBandAbove n pole a tau ⊆
        finRealSphereHeightBandAbove n pole a tau₀ :=
    finRealSphereHeightBandAbove_subset_of_le n pole a htau_le_tau₀
  have hbelow_sub :
      finRealSphereHeightBandBelow n pole a tau ⊆
        finRealSphereHeightBandBelow n pole a tau₀ :=
    finRealSphereHeightBandBelow_subset_of_le n pole a htau_le_tau₀
  refine ⟨tau, htau, htau_le_max, ?_, ?_⟩
  · exact (measureReal_mono (μ := finRealSurfaceProbabilityMeasure n) habove_sub).trans habove₀
  · exact (measureReal_mono (μ := finRealSurfaceProbabilityMeasure n) hbelow_sub).trans hbelow₀

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Lemma 4.3 supplier with the height-band masses chosen internally by
atomlessness.  The geometric data only has to provide a positive upper
thickness up to which the rectangular block and average-to-supremum comparison
hold. -/
theorem finRealSphereHalfMassComplementSup_le_northPole_of_lemma43_autoHeightBands_gainSup_equal_mass
    (n : ℕ) [NeZero n] (hn : 2 ≤ n) (r : ℝ)
    (hData :
      ∀ ⦃η : ℝ⦄, 0 < η →
        ∃ eps tauSep : ℝ, 0 < eps ∧ 0 < tauSep ∧
          ∀ ⦃A : Set (FinRealSphere n)⦄,
            FinRealSphereHalfMassCompetitor n
                (finRealSurfaceProbabilityMeasure n) A →
            finRealSphereNeighbourhoodComplementMass n
                  (finRealSurfaceProbabilityMeasure n) r
                  (finRealSphereClosedHemisphere n
                    (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
              finRealSphereNeighbourhoodComplementMass n
                (finRealSurfaceProbabilityMeasure n) r A →
            ∃ C : Set (FinRealSphere n),
              ∃ pole : FinRealSphere n,
              ∃ a tauMax : ℝ,
                0 < tauMax ∧
                MeasurableSet C ∧
                (finRealSurfaceProbabilityMeasure n).real C =
                  (finRealSurfaceProbabilityMeasure n).real A ∧
                eps ≤ (finRealSurfaceProbabilityMeasure n).real (C ∆ A) ∧
                ∀ ⦃tauBand : ℝ⦄, 0 < tauBand → tauBand ≤ tauMax →
                  ∃ avg : ℝ,
                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tauSep
                      (finRealPolarizationMuMinus C A
                        (finRealSphereHeightBandBelow n pole a tauBand))
                      (finRealPolarizationMuPlus C A
                        (finRealSphereHeightBandAbove n pole a tauBand))
                      avg ∧
                    avg ≤ sSup (finRealSpherePolarizationObjectiveGainValues n r A)) :
    finRealSphereHalfMassComplementSup n
        (finRealSurfaceProbabilityMeasure n) r ≤
      finRealSphereNeighbourhoodComplementMass n
        (finRealSurfaceProbabilityMeasure n) r
        (finRealSphereClosedHemisphere n
          (finRealSphereNorthPole n : FinRealEuclideanSpace n)) := by
  exact
    finRealSphereHalfMassComplementSup_le_northPole_of_lemma43_measure_trimming_gainSup_equal_mass
      n hn r (fun {η} hη => by
        rcases hData hη with ⟨eps, tauSep, heps, htauSep, hDataη⟩
        refine ⟨eps, tauSep, heps, htauSep, ?_⟩
        intro A hA hgap
        rcases hDataη hA hgap with
          ⟨C, pole, a, tauMax, htauMax, hC, hmass, hfar, hRectData⟩
        rcases exists_finRealSphereHeightBands_small_le
            n hn pole a eps tauMax heps htauMax with
          ⟨tauBand, htauBand, htauBand_le, hbandPlus, hbandMinus⟩
        rcases hRectData htauBand htauBand_le with
          ⟨avg, hRect, havgLeGainSup⟩
        refine ⟨C, finRealSphereHeightBandAbove n pole a tauBand,
          finRealSphereHeightBandBelow n pole a tauBand, avg, hC, ?_, ?_, hmass,
          hfar, hbandPlus, hbandMinus, hRect, havgLeGainSup⟩
        · exact measurableSet_finRealSphereHeightBandAbove n pole a tauBand
        · exact measurableSet_finRealSphereHeightBandBelow n pole a tauBand)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- No-input cap comparison in dimensions at least two follows from a
same-mass Lemma 4.3 supplier whose small height bands are chosen internally by
height-distribution atomlessness. -/
theorem sphere_halfMeasure_hemisphereComparisonGeTwo_of_lemma43_autoHeightBands_gainSup_equal_mass_pos_lt_pi
    (hData :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tauSep : ℝ, 0 < eps ∧ 0 < tauSep ∧
              ∀ ⦃A : Set (FinRealSphere n)⦄,
                FinRealSphereHalfMassCompetitor n
                    (finRealSurfaceProbabilityMeasure n) A →
                finRealSphereNeighbourhoodComplementMass n
                      (finRealSurfaceProbabilityMeasure n) r
                      (finRealSphereClosedHemisphere n
                        (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
                  finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r A →
                ∃ C : Set (FinRealSphere n),
                  ∃ pole : FinRealSphere n,
                  ∃ a tauMax : ℝ,
                    0 < tauMax ∧
                    MeasurableSet C ∧
                    (finRealSurfaceProbabilityMeasure n).real C =
                      (finRealSurfaceProbabilityMeasure n).real A ∧
                    eps ≤ (finRealSurfaceProbabilityMeasure n).real (C ∆ A) ∧
                    ∀ ⦃tauBand : ℝ⦄, 0 < tauBand → tauBand ≤ tauMax →
                      ∃ avg : ℝ,
                        SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tauSep
                          (finRealPolarizationMuMinus C A
                            (finRealSphereHeightBandBelow n pole a tauBand))
                          (finRealPolarizationMuPlus C A
                            (finRealSphereHeightBandAbove n pole a tauBand))
                          avg ∧
                        avg ≤ sSup (finRealSpherePolarizationObjectiveGainValues n r A)) :
    sphere_halfMeasure_hemisphereComparisonGeTwo := by
  exact sphere_halfMeasure_hemisphereComparisonGeTwo_of_complementSup_le_northPole_pos_lt_pi
    (fun n _ hn2 {r} hrpos hrlt =>
      finRealSphereHalfMassComplementSup_le_northPole_of_lemma43_autoHeightBands_gainSup_equal_mass
        n hn2 r (hData n hn2 hrpos hrlt))

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Same-mass auto-height-band Lemma 4.3 data with an auxiliary average
supplies the direct block-to-`sSup` auto-height data used by the sharp
coordinate endpoint.

The scalar step is the same as in the fixed-height adapter: a rectangular
block lower bound by `avg`, followed by `avg ≤ sSup` of the objective gains,
is a rectangular block lower bound by that same supremum. -/
theorem lemma43_autoHeightBands_directGainSup_equal_mass_of_autoHeightBands_gainSup_equal_mass_pos_lt_pi
    (hData :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tauSep : ℝ, 0 < eps ∧ 0 < tauSep ∧
              ∀ ⦃A : Set (FinRealSphere n)⦄,
                FinRealSphereHalfMassCompetitor n
                    (finRealSurfaceProbabilityMeasure n) A →
                finRealSphereNeighbourhoodComplementMass n
                      (finRealSurfaceProbabilityMeasure n) r
                      (finRealSphereClosedHemisphere n
                        (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
                  finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r A →
                ∃ C : Set (FinRealSphere n),
                  ∃ pole : FinRealSphere n,
                  ∃ a tauMax : ℝ,
                    0 < tauMax ∧
                    MeasurableSet C ∧
                    (finRealSurfaceProbabilityMeasure n).real C =
                      (finRealSurfaceProbabilityMeasure n).real A ∧
                    eps ≤ (finRealSurfaceProbabilityMeasure n).real (C ∆ A) ∧
                    ∀ ⦃tauBand : ℝ⦄, 0 < tauBand → tauBand ≤ tauMax →
                      ∃ avg : ℝ,
                        SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tauSep
                          (finRealPolarizationMuMinus C A
                            (finRealSphereHeightBandBelow n pole a tauBand))
                          (finRealPolarizationMuPlus C A
                            (finRealSphereHeightBandAbove n pole a tauBand))
                          avg ∧
                        avg ≤ sSup (finRealSpherePolarizationObjectiveGainValues n r A)) :
    ∀ (n : ℕ) [NeZero n], 2 ≤ n →
      ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
        ∀ ⦃η : ℝ⦄, 0 < η →
          ∃ eps tauSep : ℝ, 0 < eps ∧ 0 < tauSep ∧
            ∀ ⦃A : Set (FinRealSphere n)⦄,
              FinRealSphereHalfMassCompetitor n
                  (finRealSurfaceProbabilityMeasure n) A →
              finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r
                    (finRealSphereClosedHemisphere n
                      (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
                finRealSphereNeighbourhoodComplementMass n
                  (finRealSurfaceProbabilityMeasure n) r A →
              ∃ C : Set (FinRealSphere n),
                ∃ pole : FinRealSphere n,
                ∃ a tauMax : ℝ,
                  0 < tauMax ∧
                  MeasurableSet C ∧
                  (finRealSurfaceProbabilityMeasure n).real C =
                    (finRealSurfaceProbabilityMeasure n).real A ∧
                  eps ≤ (finRealSurfaceProbabilityMeasure n).real (C ∆ A) ∧
                  ∀ ⦃tauBand : ℝ⦄, 0 < tauBand → tauBand ≤ tauMax →
                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tauSep
                      (finRealPolarizationMuMinus C A
                        (finRealSphereHeightBandBelow n pole a tauBand))
                      (finRealPolarizationMuPlus C A
                        (finRealSphereHeightBandAbove n pole a tauBand))
                      (sSup (finRealSpherePolarizationObjectiveGainValues n r A)) := by
  intro n hn hn2 r hrpos hrlt η hη
  rcases hData n hn2 hrpos hrlt hη with
    ⟨eps, tauSep, heps, htauSep, hDataη⟩
  refine ⟨eps, tauSep, heps, htauSep, ?_⟩
  intro A hA hgap
  rcases hDataη hA hgap with
    ⟨C, pole, a, tauMax, htauMax, hC, hmass, hfar, hRectData⟩
  refine ⟨C, pole, a, tauMax, htauMax, hC, hmass, hfar, ?_⟩
  intro tauBand htauBand htauBand_le
  rcases hRectData htauBand htauBand_le with ⟨avg, hRect, havgLeGainSup⟩
  exact hRect.trans havgLeGainSup

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Same-mass auto-height-band Lemma 4.3 data gives the direct uniform
gain-supremum supplier.

The only extra work beyond the auto-height statement is choosing a sufficiently
thin height band below the supplied `tauMax`; atomlessness gives the required
small band masses. -/
theorem uniform_polarization_gainSup_lower_of_lemma43_autoHeightBands_gainSup_equal_mass_pos_lt_pi
    (hData :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tauSep : ℝ, 0 < eps ∧ 0 < tauSep ∧
              ∀ ⦃A : Set (FinRealSphere n)⦄,
                FinRealSphereHalfMassCompetitor n
                    (finRealSurfaceProbabilityMeasure n) A →
                finRealSphereNeighbourhoodComplementMass n
                      (finRealSurfaceProbabilityMeasure n) r
                      (finRealSphereClosedHemisphere n
                        (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
                  finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r A →
                ∃ C : Set (FinRealSphere n),
                  ∃ pole : FinRealSphere n,
                  ∃ a tauMax : ℝ,
                    0 < tauMax ∧
                    MeasurableSet C ∧
                    (finRealSurfaceProbabilityMeasure n).real C =
                      (finRealSurfaceProbabilityMeasure n).real A ∧
                    eps ≤ (finRealSurfaceProbabilityMeasure n).real (C ∆ A) ∧
                    ∀ ⦃tauBand : ℝ⦄, 0 < tauBand → tauBand ≤ tauMax →
                      ∃ avg : ℝ,
                        SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tauSep
                          (finRealPolarizationMuMinus C A
                            (finRealSphereHeightBandBelow n pole a tauBand))
                          (finRealPolarizationMuPlus C A
                            (finRealSphereHeightBandAbove n pole a tauBand))
                          avg ∧
                        avg ≤ sSup (finRealSpherePolarizationObjectiveGainValues n r A)) :
    ∀ (n : ℕ) [NeZero n], 2 ≤ n →
      ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
        ∀ ⦃η : ℝ⦄, 0 < η →
          ∃ δ : ℝ, 0 < δ ∧
            ∀ ⦃A : Set (FinRealSphere n)⦄,
              FinRealSphereHalfMassCompetitor n
                  (finRealSurfaceProbabilityMeasure n) A →
              finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r
                    (finRealSphereClosedHemisphere n
                      (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
                finRealSphereNeighbourhoodComplementMass n
                  (finRealSurfaceProbabilityMeasure n) r A →
              δ ≤ sSup (finRealSpherePolarizationObjectiveGainValues n r A) := by
  refine
    uniform_polarization_gainSup_lower_of_lemma43_measure_trimming_gainSup_equal_mass_pos_lt_pi
      ?_
  intro n _ hn r hrpos hrlt η hη
  rcases hData n hn hrpos hrlt hη with
    ⟨eps, tauSep, heps, htauSep, hDataη⟩
  refine ⟨eps, tauSep, heps, htauSep, ?_⟩
  intro A hA hgap
  rcases hDataη hA hgap with
    ⟨C, pole, a, tauMax, htauMax, hC, hmass, hfar, hRectData⟩
  rcases exists_finRealSphereHeightBands_small_le
      n hn pole a eps tauMax heps htauMax with
    ⟨tauBand, htauBand, htauBand_le, hbandPlus, hbandMinus⟩
  rcases hRectData htauBand htauBand_le with
    ⟨avg, hRect, havgLeGainSup⟩
  refine ⟨C, finRealSphereHeightBandAbove n pole a tauBand,
    finRealSphereHeightBandBelow n pole a tauBand, avg, hC, ?_, ?_, hmass,
    hfar, hbandPlus, hbandMinus, hRect, havgLeGainSup⟩
  · exact measurableSet_finRealSphereHeightBandAbove n pole a tauBand
  · exact measurableSet_finRealSphereHeightBandBelow n pole a tauBand

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Same-mass auto-height-band Lemma 4.3 data gives the uniform actual
polarization-improvement supplier.

This is the strict-improvement API for the natural average-form Lemma 4.3
output: first turn the average/block data into a uniform lower bound on the
supremum of polarization gains, then extract an actual improving direction by
the half-gain argument. -/
theorem uniform_polarization_gap_improvement_of_lemma43_autoHeightBands_gainSup_equal_mass_pos_lt_pi
    (hData :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tauSep : ℝ, 0 < eps ∧ 0 < tauSep ∧
              ∀ ⦃A : Set (FinRealSphere n)⦄,
                FinRealSphereHalfMassCompetitor n
                    (finRealSurfaceProbabilityMeasure n) A →
                finRealSphereNeighbourhoodComplementMass n
                      (finRealSurfaceProbabilityMeasure n) r
                      (finRealSphereClosedHemisphere n
                        (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
                  finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r A →
                ∃ C : Set (FinRealSphere n),
                  ∃ pole : FinRealSphere n,
                  ∃ a tauMax : ℝ,
                    0 < tauMax ∧
                    MeasurableSet C ∧
                    (finRealSurfaceProbabilityMeasure n).real C =
                      (finRealSurfaceProbabilityMeasure n).real A ∧
                    eps ≤ (finRealSurfaceProbabilityMeasure n).real (C ∆ A) ∧
                    ∀ ⦃tauBand : ℝ⦄, 0 < tauBand → tauBand ≤ tauMax →
                      ∃ avg : ℝ,
                        SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tauSep
                          (finRealPolarizationMuMinus C A
                            (finRealSphereHeightBandBelow n pole a tauBand))
                          (finRealPolarizationMuPlus C A
                            (finRealSphereHeightBandAbove n pole a tauBand))
                          avg ∧
                        avg ≤ sSup (finRealSpherePolarizationObjectiveGainValues n r A)) :
    ∀ (n : ℕ) [NeZero n], 2 ≤ n →
      ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
        ∀ ⦃η : ℝ⦄, 0 < η →
          ∃ δ : ℝ, 0 < δ ∧
            ∀ ⦃A : Set (FinRealSphere n)⦄,
              FinRealSphereHalfMassCompetitor n
                  (finRealSurfaceProbabilityMeasure n) A →
              finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r
                    (finRealSphereClosedHemisphere n
                      (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
                finRealSphereNeighbourhoodComplementMass n
                  (finRealSurfaceProbabilityMeasure n) r A →
              ∃ v : FinRealSphere n,
                finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r A + δ ≤
                  finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r
                    (finRealSpherePolarization (finRealSphereReflectionMap n) v A) := by
  exact
    uniform_polarization_gap_improvement_of_uniform_polarization_gainSup_lower_pos_lt_pi
      (uniform_polarization_gainSup_lower_of_lemma43_autoHeightBands_gainSup_equal_mass_pos_lt_pi
        hData)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Direct auto-height-band Lemma 4.3 data gives the uniform gain-supremum
supplier without an auxiliary average witness.

This is just the preceding auto-height adapter with `avg` specialized to the
actual supremum of polarization objective gains.  It is the tightest local
frontier for the geometric supplier: after choosing the same-mass model and a
thin height band, the remaining block estimate is stated directly as a lower
bound on `sSup` of the gains. -/
theorem uniform_polarization_gainSup_lower_of_lemma43_autoHeightBands_directGainSup_equal_mass_pos_lt_pi
    (hData :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tauSep : ℝ, 0 < eps ∧ 0 < tauSep ∧
              ∀ ⦃A : Set (FinRealSphere n)⦄,
                FinRealSphereHalfMassCompetitor n
                    (finRealSurfaceProbabilityMeasure n) A →
                finRealSphereNeighbourhoodComplementMass n
                      (finRealSurfaceProbabilityMeasure n) r
                      (finRealSphereClosedHemisphere n
                        (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
                  finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r A →
                ∃ C : Set (FinRealSphere n),
                  ∃ pole : FinRealSphere n,
                  ∃ a tauMax : ℝ,
                    0 < tauMax ∧
                    MeasurableSet C ∧
                    (finRealSurfaceProbabilityMeasure n).real C =
                      (finRealSurfaceProbabilityMeasure n).real A ∧
                    eps ≤ (finRealSurfaceProbabilityMeasure n).real (C ∆ A) ∧
                    ∀ ⦃tauBand : ℝ⦄, 0 < tauBand → tauBand ≤ tauMax →
                      SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tauSep
                        (finRealPolarizationMuMinus C A
                          (finRealSphereHeightBandBelow n pole a tauBand))
                        (finRealPolarizationMuPlus C A
                          (finRealSphereHeightBandAbove n pole a tauBand))
                        (sSup (finRealSpherePolarizationObjectiveGainValues n r A))) :
    ∀ (n : ℕ) [NeZero n], 2 ≤ n →
      ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
        ∀ ⦃η : ℝ⦄, 0 < η →
          ∃ δ : ℝ, 0 < δ ∧
            ∀ ⦃A : Set (FinRealSphere n)⦄,
              FinRealSphereHalfMassCompetitor n
                  (finRealSurfaceProbabilityMeasure n) A →
              finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r
                    (finRealSphereClosedHemisphere n
                      (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
                finRealSphereNeighbourhoodComplementMass n
                  (finRealSurfaceProbabilityMeasure n) r A →
              δ ≤ sSup (finRealSpherePolarizationObjectiveGainValues n r A) := by
  refine
    uniform_polarization_gainSup_lower_of_lemma43_autoHeightBands_gainSup_equal_mass_pos_lt_pi
      ?_
  intro n _ hn r hrpos hrlt η hη
  rcases hData n hn hrpos hrlt hη with
    ⟨eps, tauSep, heps, htauSep, hDataη⟩
  refine ⟨eps, tauSep, heps, htauSep, ?_⟩
  intro A hA hgap
  rcases hDataη hA hgap with
    ⟨C, pole, a, tauMax, htauMax, hC, hmass, hfar, hBlockData⟩
  refine ⟨C, pole, a, tauMax, htauMax, hC, hmass, hfar, ?_⟩
  intro tauBand htauBand htauBand_le
  refine
    ⟨sSup (finRealSpherePolarizationObjectiveGainValues n r A),
      hBlockData htauBand htauBand_le, le_rfl⟩

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Direct auto-height-band Lemma 4.3 data also gives the uniform actual
polarization-improvement supplier.

This exposes the strict-improvement API directly from the same direct
block-to-`sSup` data: first derive the uniform gain-supremum lower bound, then
extract an improving polarization direction by taking half the gain. -/
theorem uniform_polarization_gap_improvement_of_lemma43_autoHeightBands_directGainSup_equal_mass_pos_lt_pi
    (hData :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tauSep : ℝ, 0 < eps ∧ 0 < tauSep ∧
              ∀ ⦃A : Set (FinRealSphere n)⦄,
                FinRealSphereHalfMassCompetitor n
                    (finRealSurfaceProbabilityMeasure n) A →
                finRealSphereNeighbourhoodComplementMass n
                      (finRealSurfaceProbabilityMeasure n) r
                      (finRealSphereClosedHemisphere n
                        (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
                  finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r A →
                ∃ C : Set (FinRealSphere n),
                  ∃ pole : FinRealSphere n,
                  ∃ a tauMax : ℝ,
                    0 < tauMax ∧
                    MeasurableSet C ∧
                    (finRealSurfaceProbabilityMeasure n).real C =
                      (finRealSurfaceProbabilityMeasure n).real A ∧
                    eps ≤ (finRealSurfaceProbabilityMeasure n).real (C ∆ A) ∧
                    ∀ ⦃tauBand : ℝ⦄, 0 < tauBand → tauBand ≤ tauMax →
                      SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tauSep
                        (finRealPolarizationMuMinus C A
                          (finRealSphereHeightBandBelow n pole a tauBand))
                        (finRealPolarizationMuPlus C A
                          (finRealSphereHeightBandAbove n pole a tauBand))
                        (sSup (finRealSpherePolarizationObjectiveGainValues n r A))) :
    ∀ (n : ℕ) [NeZero n], 2 ≤ n →
      ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
        ∀ ⦃η : ℝ⦄, 0 < η →
          ∃ δ : ℝ, 0 < δ ∧
            ∀ ⦃A : Set (FinRealSphere n)⦄,
              FinRealSphereHalfMassCompetitor n
                  (finRealSurfaceProbabilityMeasure n) A →
              finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r
                    (finRealSphereClosedHemisphere n
                      (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
                finRealSphereNeighbourhoodComplementMass n
                  (finRealSurfaceProbabilityMeasure n) r A →
              ∃ v : FinRealSphere n,
                finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r A + δ ≤
                  finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r
                    (finRealSpherePolarization (finRealSphereReflectionMap n) v A) := by
  exact
    uniform_polarization_gap_improvement_of_uniform_polarization_gainSup_lower_pos_lt_pi
      (uniform_polarization_gainSup_lower_of_lemma43_autoHeightBands_directGainSup_equal_mass_pos_lt_pi
        hData)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Fixed-radius supremum domination from direct auto-height-band Lemma 4.3
data.  This is the cap-comparison-facing form of the direct block-to-`sSup`
adapter. -/
theorem finRealSphereHalfMassComplementSup_le_northPole_of_lemma43_autoHeightBands_directGainSup_equal_mass
    (n : ℕ) [NeZero n] (hn : 2 ≤ n) (r : ℝ)
    (hData :
      ∀ ⦃η : ℝ⦄, 0 < η →
        ∃ eps tauSep : ℝ, 0 < eps ∧ 0 < tauSep ∧
          ∀ ⦃A : Set (FinRealSphere n)⦄,
            FinRealSphereHalfMassCompetitor n
                (finRealSurfaceProbabilityMeasure n) A →
            finRealSphereNeighbourhoodComplementMass n
                  (finRealSurfaceProbabilityMeasure n) r
                  (finRealSphereClosedHemisphere n
                    (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
              finRealSphereNeighbourhoodComplementMass n
                (finRealSurfaceProbabilityMeasure n) r A →
            ∃ C : Set (FinRealSphere n),
              ∃ pole : FinRealSphere n,
              ∃ a tauMax : ℝ,
                0 < tauMax ∧
                MeasurableSet C ∧
                (finRealSurfaceProbabilityMeasure n).real C =
                  (finRealSurfaceProbabilityMeasure n).real A ∧
                eps ≤ (finRealSurfaceProbabilityMeasure n).real (C ∆ A) ∧
                ∀ ⦃tauBand : ℝ⦄, 0 < tauBand → tauBand ≤ tauMax →
                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tauSep
                    (finRealPolarizationMuMinus C A
                      (finRealSphereHeightBandBelow n pole a tauBand))
                    (finRealPolarizationMuPlus C A
                      (finRealSphereHeightBandAbove n pole a tauBand))
                    (sSup (finRealSpherePolarizationObjectiveGainValues n r A))) :
    finRealSphereHalfMassComplementSup n
        (finRealSurfaceProbabilityMeasure n) r ≤
      finRealSphereNeighbourhoodComplementMass n
        (finRealSurfaceProbabilityMeasure n) r
        (finRealSphereClosedHemisphere n
          (finRealSphereNorthPole n : FinRealEuclideanSpace n)) := by
  exact
    finRealSphereHalfMassComplementSup_le_northPole_of_lemma43_autoHeightBands_gainSup_equal_mass
      n hn r (fun {η} hη => by
        rcases hData hη with ⟨eps, tauSep, heps, htauSep, hDataη⟩
        refine ⟨eps, tauSep, heps, htauSep, ?_⟩
        intro A hA hgap
        rcases hDataη hA hgap with
          ⟨C, pole, a, tauMax, htauMax, hC, hmass, hfar, hBlockData⟩
        refine ⟨C, pole, a, tauMax, htauMax, hC, hmass, hfar, ?_⟩
        intro tauBand htauBand htauBand_le
        refine
          ⟨sSup (finRealSpherePolarizationObjectiveGainValues n r A),
            hBlockData htauBand htauBand_le, le_rfl⟩)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- No-input cap comparison in dimensions at least two from direct
auto-height-band Lemma 4.3 data.  The direct data targets `sSup` of
polarization objective gains, so the auxiliary average witness is not visible
in this public comparison theorem. -/
theorem sphere_halfMeasure_hemisphereComparisonGeTwo_of_lemma43_autoHeightBands_directGainSup_equal_mass_pos_lt_pi
    (hData :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tauSep : ℝ, 0 < eps ∧ 0 < tauSep ∧
              ∀ ⦃A : Set (FinRealSphere n)⦄,
                FinRealSphereHalfMassCompetitor n
                    (finRealSurfaceProbabilityMeasure n) A →
                finRealSphereNeighbourhoodComplementMass n
                      (finRealSurfaceProbabilityMeasure n) r
                      (finRealSphereClosedHemisphere n
                        (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
                  finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r A →
                ∃ C : Set (FinRealSphere n),
                  ∃ pole : FinRealSphere n,
                  ∃ a tauMax : ℝ,
                    0 < tauMax ∧
                    MeasurableSet C ∧
                    (finRealSurfaceProbabilityMeasure n).real C =
                      (finRealSurfaceProbabilityMeasure n).real A ∧
                    eps ≤ (finRealSurfaceProbabilityMeasure n).real (C ∆ A) ∧
                    ∀ ⦃tauBand : ℝ⦄, 0 < tauBand → tauBand ≤ tauMax →
                      SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tauSep
                        (finRealPolarizationMuMinus C A
                          (finRealSphereHeightBandBelow n pole a tauBand))
                        (finRealPolarizationMuPlus C A
                          (finRealSphereHeightBandAbove n pole a tauBand))
                        (sSup (finRealSpherePolarizationObjectiveGainValues n r A))) :
    sphere_halfMeasure_hemisphereComparisonGeTwo := by
  exact sphere_halfMeasure_hemisphereComparisonGeTwo_of_complementSup_le_northPole_pos_lt_pi
    (fun n _ hn2 {r} hrpos hrlt =>
      finRealSphereHalfMassComplementSup_le_northPole_of_lemma43_autoHeightBands_directGainSup_equal_mass
        n hn2 r (hData n hn2 hrpos hrlt))

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Variant of the Lemma 4.3 same-mass data supplier where the two trimming
bands are concrete height bands.  Their measurability is supplied by the
height-band API, so the remaining geometric data only has to choose the model,
the height pole/level, and prove the two band-mass bounds. -/
theorem finRealSphereHalfMassComplementSup_le_northPole_of_lemma43_heightBands_gainSup_equal_mass
    (n : ℕ) [NeZero n] (hn : 2 ≤ n) (r : ℝ)
    (hData :
      ∀ ⦃η : ℝ⦄, 0 < η →
        ∃ eps tau : ℝ, 0 < eps ∧ 0 < tau ∧
          ∀ ⦃A : Set (FinRealSphere n)⦄,
            FinRealSphereHalfMassCompetitor n
                (finRealSurfaceProbabilityMeasure n) A →
            finRealSphereNeighbourhoodComplementMass n
                  (finRealSurfaceProbabilityMeasure n) r
                  (finRealSphereClosedHemisphere n
                    (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
              finRealSphereNeighbourhoodComplementMass n
                (finRealSurfaceProbabilityMeasure n) r A →
            ∃ C : Set (FinRealSphere n),
              ∃ pole : FinRealSphere n,
              ∃ a avg : ℝ,
                MeasurableSet C ∧
                (finRealSurfaceProbabilityMeasure n).real C =
                  (finRealSurfaceProbabilityMeasure n).real A ∧
                eps ≤ (finRealSurfaceProbabilityMeasure n).real (C ∆ A) ∧
                (finRealSurfaceProbabilityMeasure n).real
                    (finRealSphereHeightBandAbove n pole a tau) ≤ eps / 4 ∧
                (finRealSurfaceProbabilityMeasure n).real
                    (finRealSphereHeightBandBelow n pole a tau) ≤ eps / 4 ∧
                SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tau
                  (finRealPolarizationMuMinus C A
                    (finRealSphereHeightBandBelow n pole a tau))
                  (finRealPolarizationMuPlus C A
                    (finRealSphereHeightBandAbove n pole a tau))
                  avg ∧
                avg ≤ sSup (finRealSpherePolarizationObjectiveGainValues n r A)) :
    finRealSphereHalfMassComplementSup n
        (finRealSurfaceProbabilityMeasure n) r ≤
      finRealSphereNeighbourhoodComplementMass n
        (finRealSurfaceProbabilityMeasure n) r
        (finRealSphereClosedHemisphere n
          (finRealSphereNorthPole n : FinRealEuclideanSpace n)) := by
  exact
    finRealSphereHalfMassComplementSup_le_northPole_of_lemma43_measure_trimming_gainSup_equal_mass
      n hn r (fun {η} hη => by
        rcases hData hη with ⟨eps, tau, heps, htau, hDataη⟩
        refine ⟨eps, tau, heps, htau, ?_⟩
        intro A hA hgap
        rcases hDataη hA hgap with
          ⟨C, pole, a, avg, hC, hmass, hfar,
            hbandPlus, hbandMinus, hRect, havgLeGainSup⟩
        refine ⟨C, finRealSphereHeightBandAbove n pole a tau,
          finRealSphereHeightBandBelow n pole a tau, avg, hC, ?_, ?_, hmass,
          hfar, hbandPlus, hbandMinus, hRect, havgLeGainSup⟩
        · exact measurableSet_finRealSphereHeightBandAbove n pole a tau
        · exact measurableSet_finRealSphereHeightBandBelow n pole a tau)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- No-input cap comparison in dimensions at least two follows from a
same-mass Lemma 4.3 supplier with concrete height bands on `0 < r < π`. -/
theorem sphere_halfMeasure_hemisphereComparisonGeTwo_of_lemma43_heightBands_gainSup_equal_mass_pos_lt_pi
    (hData :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tau : ℝ, 0 < eps ∧ 0 < tau ∧
              ∀ ⦃A : Set (FinRealSphere n)⦄,
                FinRealSphereHalfMassCompetitor n
                    (finRealSurfaceProbabilityMeasure n) A →
                finRealSphereNeighbourhoodComplementMass n
                      (finRealSurfaceProbabilityMeasure n) r
                      (finRealSphereClosedHemisphere n
                        (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
                  finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r A →
                ∃ C : Set (FinRealSphere n),
                  ∃ pole : FinRealSphere n,
                  ∃ a avg : ℝ,
                    MeasurableSet C ∧
                    (finRealSurfaceProbabilityMeasure n).real C =
                      (finRealSurfaceProbabilityMeasure n).real A ∧
                    eps ≤ (finRealSurfaceProbabilityMeasure n).real (C ∆ A) ∧
                    (finRealSurfaceProbabilityMeasure n).real
                        (finRealSphereHeightBandAbove n pole a tau) ≤ eps / 4 ∧
                    (finRealSurfaceProbabilityMeasure n).real
                        (finRealSphereHeightBandBelow n pole a tau) ≤ eps / 4 ∧
                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tau
                      (finRealPolarizationMuMinus C A
                        (finRealSphereHeightBandBelow n pole a tau))
                      (finRealPolarizationMuPlus C A
                        (finRealSphereHeightBandAbove n pole a tau))
                      avg ∧
                    avg ≤ sSup (finRealSpherePolarizationObjectiveGainValues n r A)) :
    sphere_halfMeasure_hemisphereComparisonGeTwo := by
  exact sphere_halfMeasure_hemisphereComparisonGeTwo_of_complementSup_le_northPole_pos_lt_pi
    (fun n _ hn2 {r} hrpos hrlt =>
      finRealSphereHalfMassComplementSup_le_northPole_of_lemma43_heightBands_gainSup_equal_mass
        n hn2 r (hData n hn2 hrpos hrlt))

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Same-mass height-band Lemma 4.3 data with an auxiliary average supplies
the direct block-to-`sSup` height-band data used by the sharp fixed-height
endpoint.

The only extra step is scalar: a rectangular block lower bound by `avg`, plus
`avg ≤ sSup` of the objective gains, is a rectangular block lower bound by that
same supremum. -/
theorem lemma43_heightBands_directGainSup_equal_mass_of_heightBands_gainSup_equal_mass_pos_lt_pi
    (hData :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tau : ℝ, 0 < eps ∧ 0 < tau ∧
              ∀ ⦃A : Set (FinRealSphere n)⦄,
                FinRealSphereHalfMassCompetitor n
                    (finRealSurfaceProbabilityMeasure n) A →
                finRealSphereNeighbourhoodComplementMass n
                      (finRealSurfaceProbabilityMeasure n) r
                      (finRealSphereClosedHemisphere n
                        (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
                  finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r A →
                ∃ C : Set (FinRealSphere n),
                  ∃ pole : FinRealSphere n,
                  ∃ a avg : ℝ,
                    MeasurableSet C ∧
                    (finRealSurfaceProbabilityMeasure n).real C =
                      (finRealSurfaceProbabilityMeasure n).real A ∧
                    eps ≤ (finRealSurfaceProbabilityMeasure n).real (C ∆ A) ∧
                    (finRealSurfaceProbabilityMeasure n).real
                        (finRealSphereHeightBandAbove n pole a tau) ≤ eps / 4 ∧
                    (finRealSurfaceProbabilityMeasure n).real
                        (finRealSphereHeightBandBelow n pole a tau) ≤ eps / 4 ∧
                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tau
                      (finRealPolarizationMuMinus C A
                        (finRealSphereHeightBandBelow n pole a tau))
                      (finRealPolarizationMuPlus C A
                        (finRealSphereHeightBandAbove n pole a tau))
                      avg ∧
                    avg ≤ sSup (finRealSpherePolarizationObjectiveGainValues n r A)) :
    ∀ (n : ℕ) [NeZero n], 2 ≤ n →
      ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
        ∀ ⦃η : ℝ⦄, 0 < η →
          ∃ eps tau : ℝ, 0 < eps ∧ 0 < tau ∧
            ∀ ⦃A : Set (FinRealSphere n)⦄,
              FinRealSphereHalfMassCompetitor n
                  (finRealSurfaceProbabilityMeasure n) A →
              finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r
                    (finRealSphereClosedHemisphere n
                      (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
                finRealSphereNeighbourhoodComplementMass n
                  (finRealSurfaceProbabilityMeasure n) r A →
              ∃ C : Set (FinRealSphere n),
                ∃ pole : FinRealSphere n,
                ∃ a : ℝ,
                  MeasurableSet C ∧
                  (finRealSurfaceProbabilityMeasure n).real C =
                    (finRealSurfaceProbabilityMeasure n).real A ∧
                  eps ≤ (finRealSurfaceProbabilityMeasure n).real (C ∆ A) ∧
                  (finRealSurfaceProbabilityMeasure n).real
                      (finRealSphereHeightBandAbove n pole a tau) ≤ eps / 4 ∧
                  (finRealSurfaceProbabilityMeasure n).real
                      (finRealSphereHeightBandBelow n pole a tau) ≤ eps / 4 ∧
                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tau
                    (finRealPolarizationMuMinus C A
                      (finRealSphereHeightBandBelow n pole a tau))
                    (finRealPolarizationMuPlus C A
                      (finRealSphereHeightBandAbove n pole a tau))
                    (sSup (finRealSpherePolarizationObjectiveGainValues n r A)) := by
  intro n hn hn2 r hrpos hrlt η hη
  rcases hData n hn2 hrpos hrlt hη with
    ⟨eps, tau, heps, htau, hDataη⟩
  refine ⟨eps, tau, heps, htau, ?_⟩
  intro A hA hgap
  rcases hDataη hA hgap with
    ⟨C, pole, a, avg, hC, hmass, hfar, hbandPlus, hbandMinus,
      hRect, havgLeGainSup⟩
  refine ⟨C, pole, a, hC, hmass, hfar, hbandPlus, hbandMinus, ?_⟩
  exact hRect.trans havgLeGainSup

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Fixed-height-band direct `sSup` data gives normalized north-pole
supremum domination without exposing an auxiliary average witness. -/
theorem finRealSphereHalfMassComplementSup_le_northPole_of_lemma43_heightBands_directGainSup_equal_mass
    (n : ℕ) [NeZero n] (hn : 2 ≤ n) (r : ℝ)
    (hData :
      ∀ ⦃η : ℝ⦄, 0 < η →
        ∃ eps tau : ℝ, 0 < eps ∧ 0 < tau ∧
          ∀ ⦃A : Set (FinRealSphere n)⦄,
            FinRealSphereHalfMassCompetitor n
                (finRealSurfaceProbabilityMeasure n) A →
            finRealSphereNeighbourhoodComplementMass n
                  (finRealSurfaceProbabilityMeasure n) r
                  (finRealSphereClosedHemisphere n
                    (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
              finRealSphereNeighbourhoodComplementMass n
                (finRealSurfaceProbabilityMeasure n) r A →
            ∃ C : Set (FinRealSphere n),
              ∃ pole : FinRealSphere n,
              ∃ a : ℝ,
                MeasurableSet C ∧
                (finRealSurfaceProbabilityMeasure n).real C =
                  (finRealSurfaceProbabilityMeasure n).real A ∧
                eps ≤ (finRealSurfaceProbabilityMeasure n).real (C ∆ A) ∧
                (finRealSurfaceProbabilityMeasure n).real
                    (finRealSphereHeightBandAbove n pole a tau) ≤ eps / 4 ∧
                (finRealSurfaceProbabilityMeasure n).real
                    (finRealSphereHeightBandBelow n pole a tau) ≤ eps / 4 ∧
                SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tau
                  (finRealPolarizationMuMinus C A
                    (finRealSphereHeightBandBelow n pole a tau))
                  (finRealPolarizationMuPlus C A
                    (finRealSphereHeightBandAbove n pole a tau))
                  (sSup (finRealSpherePolarizationObjectiveGainValues n r A))) :
    finRealSphereHalfMassComplementSup n
        (finRealSurfaceProbabilityMeasure n) r ≤
      finRealSphereNeighbourhoodComplementMass n
        (finRealSurfaceProbabilityMeasure n) r
        (finRealSphereClosedHemisphere n
          (finRealSphereNorthPole n : FinRealEuclideanSpace n)) := by
  exact
    finRealSphereHalfMassComplementSup_le_northPole_of_lemma43_heightBands_gainSup_equal_mass
      n hn r (fun {η} hη => by
        rcases hData hη with ⟨eps, tau, heps, htau, hDataη⟩
        refine ⟨eps, tau, heps, htau, ?_⟩
        intro A hA hgap
        rcases hDataη hA hgap with
          ⟨C, pole, a, hC, hmass, hfar, hbandPlus, hbandMinus, hRect⟩
        refine ⟨C, pole, a,
          sSup (finRealSpherePolarizationObjectiveGainValues n r A),
          hC, hmass, hfar, hbandPlus, hbandMinus, hRect, le_rfl⟩)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- No-input cap comparison in dimensions at least two follows from fixed
height-band Lemma 4.3 data whose rectangular block lower bound is already
stated against the supremum of polarization gains. -/
theorem sphere_halfMeasure_hemisphereComparisonGeTwo_of_lemma43_heightBands_directGainSup_equal_mass_pos_lt_pi
    (hData :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tau : ℝ, 0 < eps ∧ 0 < tau ∧
              ∀ ⦃A : Set (FinRealSphere n)⦄,
                FinRealSphereHalfMassCompetitor n
                    (finRealSurfaceProbabilityMeasure n) A →
                finRealSphereNeighbourhoodComplementMass n
                      (finRealSurfaceProbabilityMeasure n) r
                      (finRealSphereClosedHemisphere n
                        (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
                  finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r A →
                ∃ C : Set (FinRealSphere n),
                  ∃ pole : FinRealSphere n,
                  ∃ a : ℝ,
                    MeasurableSet C ∧
                    (finRealSurfaceProbabilityMeasure n).real C =
                      (finRealSurfaceProbabilityMeasure n).real A ∧
                    eps ≤ (finRealSurfaceProbabilityMeasure n).real (C ∆ A) ∧
                    (finRealSurfaceProbabilityMeasure n).real
                        (finRealSphereHeightBandAbove n pole a tau) ≤ eps / 4 ∧
                    (finRealSurfaceProbabilityMeasure n).real
                        (finRealSphereHeightBandBelow n pole a tau) ≤ eps / 4 ∧
                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tau
                      (finRealPolarizationMuMinus C A
                        (finRealSphereHeightBandBelow n pole a tau))
                      (finRealPolarizationMuPlus C A
                        (finRealSphereHeightBandAbove n pole a tau))
                      (sSup (finRealSpherePolarizationObjectiveGainValues n r A))) :
    sphere_halfMeasure_hemisphereComparisonGeTwo := by
  exact sphere_halfMeasure_hemisphereComparisonGeTwo_of_complementSup_le_northPole_pos_lt_pi
    (fun n _ hn2 {r} hrpos hrlt =>
      finRealSphereHalfMassComplementSup_le_northPole_of_lemma43_heightBands_directGainSup_equal_mass
        n hn2 r (hData n hn2 hrpos hrlt))

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Variant of the concrete height-band supplier where the rectangular block
may be proved at a larger separation parameter `tauRect`.  The concrete
trimmed-defect monotonicity adapter degrades it to the smaller band thickness
`tau`. -/
theorem finRealSphereHalfMassComplementSup_le_northPole_of_lemma43_heightBands_rectTau_gainSup_equal_mass
    (n : ℕ) [NeZero n] (hn : 2 ≤ n) (r : ℝ)
    (hData :
      ∀ ⦃η : ℝ⦄, 0 < η →
        ∃ eps tau tauRect : ℝ, 0 < eps ∧ 0 < tau ∧ tau ≤ tauRect ∧
          ∀ ⦃A : Set (FinRealSphere n)⦄,
            FinRealSphereHalfMassCompetitor n
                (finRealSurfaceProbabilityMeasure n) A →
            finRealSphereNeighbourhoodComplementMass n
                  (finRealSurfaceProbabilityMeasure n) r
                  (finRealSphereClosedHemisphere n
                    (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
              finRealSphereNeighbourhoodComplementMass n
                (finRealSurfaceProbabilityMeasure n) r A →
            ∃ C : Set (FinRealSphere n),
              ∃ pole : FinRealSphere n,
              ∃ a avg : ℝ,
                MeasurableSet C ∧
                (finRealSurfaceProbabilityMeasure n).real C =
                  (finRealSurfaceProbabilityMeasure n).real A ∧
                eps ≤ (finRealSurfaceProbabilityMeasure n).real (C ∆ A) ∧
                (finRealSurfaceProbabilityMeasure n).real
                    (finRealSphereHeightBandAbove n pole a tau) ≤ eps / 4 ∧
                (finRealSurfaceProbabilityMeasure n).real
                    (finRealSphereHeightBandBelow n pole a tau) ≤ eps / 4 ∧
                SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tauRect
                  (finRealPolarizationMuMinus C A
                    (finRealSphereHeightBandBelow n pole a tau))
                  (finRealPolarizationMuPlus C A
                    (finRealSphereHeightBandAbove n pole a tau))
                  avg ∧
                avg ≤ sSup (finRealSpherePolarizationObjectiveGainValues n r A)) :
    finRealSphereHalfMassComplementSup n
        (finRealSurfaceProbabilityMeasure n) r ≤
      finRealSphereNeighbourhoodComplementMass n
        (finRealSurfaceProbabilityMeasure n) r
        (finRealSphereClosedHemisphere n
          (finRealSphereNorthPole n : FinRealEuclideanSpace n)) := by
  exact
    finRealSphereHalfMassComplementSup_le_northPole_of_lemma43_heightBands_gainSup_equal_mass
      n hn r (fun {η} hη => by
        rcases hData hη with
          ⟨eps, tau, tauRect, heps, htau, htau_le_rect, hDataη⟩
        refine ⟨eps, tau, heps, htau, ?_⟩
        intro A hA hgap
        rcases hDataη hA hgap with
          ⟨C, pole, a, avg, hC, hmass, hfar, hbandPlus, hbandMinus,
            hRect, havgLeGainSup⟩
        refine ⟨C, pole, a, avg, hC, hmass, hfar, hbandPlus, hbandMinus, ?_,
          havgLeGainSup⟩
        exact finRealPolarization_rectangularBlockLowerBound_mono_tau
          (n := n) (C := C) (E := A)
          (bandPlus := finRealSphereHeightBandAbove n pole a tau)
          (bandMinus := finRealSphereHeightBandBelow n pole a tau)
          htau_le_rect hRect)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- No-input cap comparison in dimensions at least two follows from a
same-mass height-band supplier whose rectangular block is available at a
separation parameter at least as large as the chosen band thickness. -/
theorem sphere_halfMeasure_hemisphereComparisonGeTwo_of_lemma43_heightBands_rectTau_gainSup_equal_mass_pos_lt_pi
    (hData :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tau tauRect : ℝ, 0 < eps ∧ 0 < tau ∧ tau ≤ tauRect ∧
              ∀ ⦃A : Set (FinRealSphere n)⦄,
                FinRealSphereHalfMassCompetitor n
                    (finRealSurfaceProbabilityMeasure n) A →
                finRealSphereNeighbourhoodComplementMass n
                      (finRealSurfaceProbabilityMeasure n) r
                      (finRealSphereClosedHemisphere n
                        (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
                  finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r A →
                ∃ C : Set (FinRealSphere n),
                  ∃ pole : FinRealSphere n,
                  ∃ a avg : ℝ,
                    MeasurableSet C ∧
                    (finRealSurfaceProbabilityMeasure n).real C =
                      (finRealSurfaceProbabilityMeasure n).real A ∧
                    eps ≤ (finRealSurfaceProbabilityMeasure n).real (C ∆ A) ∧
                    (finRealSurfaceProbabilityMeasure n).real
                        (finRealSphereHeightBandAbove n pole a tau) ≤ eps / 4 ∧
                    (finRealSurfaceProbabilityMeasure n).real
                        (finRealSphereHeightBandBelow n pole a tau) ≤ eps / 4 ∧
                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tauRect
                      (finRealPolarizationMuMinus C A
                        (finRealSphereHeightBandBelow n pole a tau))
                      (finRealPolarizationMuPlus C A
                        (finRealSphereHeightBandAbove n pole a tau))
                      avg ∧
                    avg ≤ sSup (finRealSpherePolarizationObjectiveGainValues n r A)) :
    sphere_halfMeasure_hemisphereComparisonGeTwo := by
  exact sphere_halfMeasure_hemisphereComparisonGeTwo_of_complementSup_le_northPole_pos_lt_pi
    (fun n _ hn2 {r} hrpos hrlt =>
      finRealSphereHalfMassComplementSup_le_northPole_of_lemma43_heightBands_rectTau_gainSup_equal_mass
        n hn2 r (hData n hn2 hrpos hrlt))

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Same-mass height-band Lemma 4.3 data with a rectangular-block separation
`tauRect` at least as large as the chosen height-band thickness gives the
uniform gain-supremum supplier.

This is the proof-core form suited to first choosing thin trimming bands and
then proving the rectangular block estimate at a possibly larger separation
parameter. -/
theorem uniform_polarization_gainSup_lower_of_lemma43_heightBands_rectTau_gainSup_equal_mass_pos_lt_pi
    (hData :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tau tauRect : ℝ, 0 < eps ∧ 0 < tau ∧ tau ≤ tauRect ∧
              ∀ ⦃A : Set (FinRealSphere n)⦄,
                FinRealSphereHalfMassCompetitor n
                    (finRealSurfaceProbabilityMeasure n) A →
                finRealSphereNeighbourhoodComplementMass n
                      (finRealSurfaceProbabilityMeasure n) r
                      (finRealSphereClosedHemisphere n
                        (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
                  finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r A →
                ∃ C : Set (FinRealSphere n),
                  ∃ pole : FinRealSphere n,
                  ∃ a avg : ℝ,
                    MeasurableSet C ∧
                    (finRealSurfaceProbabilityMeasure n).real C =
                      (finRealSurfaceProbabilityMeasure n).real A ∧
                    eps ≤ (finRealSurfaceProbabilityMeasure n).real (C ∆ A) ∧
                    (finRealSurfaceProbabilityMeasure n).real
                        (finRealSphereHeightBandAbove n pole a tau) ≤ eps / 4 ∧
                    (finRealSurfaceProbabilityMeasure n).real
                        (finRealSphereHeightBandBelow n pole a tau) ≤ eps / 4 ∧
                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tauRect
                      (finRealPolarizationMuMinus C A
                        (finRealSphereHeightBandBelow n pole a tau))
                      (finRealPolarizationMuPlus C A
                        (finRealSphereHeightBandAbove n pole a tau))
                      avg ∧
                    avg ≤ sSup (finRealSpherePolarizationObjectiveGainValues n r A)) :
    ∀ (n : ℕ) [NeZero n], 2 ≤ n →
      ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
        ∀ ⦃η : ℝ⦄, 0 < η →
          ∃ δ : ℝ, 0 < δ ∧
            ∀ ⦃A : Set (FinRealSphere n)⦄,
              FinRealSphereHalfMassCompetitor n
                  (finRealSurfaceProbabilityMeasure n) A →
              finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r
                    (finRealSphereClosedHemisphere n
                      (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
                finRealSphereNeighbourhoodComplementMass n
                  (finRealSurfaceProbabilityMeasure n) r A →
              δ ≤
                sSup (finRealSpherePolarizationObjectiveGainValues n r A) := by
  refine
    uniform_polarization_gainSup_lower_of_lemma43_measure_trimming_gainSup_equal_mass_pos_lt_pi
      ?_
  intro n _ hn r hrpos hrlt η hη
  rcases hData n hn hrpos hrlt hη with
    ⟨eps, tau, tauRect, heps, htau, htau_le_rect, hDataη⟩
  have htauRect : 0 < tauRect := lt_of_lt_of_le htau htau_le_rect
  refine ⟨eps, tauRect, heps, htauRect, ?_⟩
  intro A hA hgap
  rcases hDataη hA hgap with
    ⟨C, pole, a, avg, hC, hmass, hfar, hbandPlus, hbandMinus,
      hRect, havgLeGainSup⟩
  refine ⟨C, finRealSphereHeightBandAbove n pole a tau,
    finRealSphereHeightBandBelow n pole a tau, avg, hC, ?_, ?_, hmass,
    hfar, hbandPlus, hbandMinus, hRect, havgLeGainSup⟩
  · exact measurableSet_finRealSphereHeightBandAbove n pole a tau
  · exact measurableSet_finRealSphereHeightBandBelow n pole a tau

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Variant of the concrete height-band supplier where the height-band
thickness and the rectangular-block separation are independent parameters. -/
theorem finRealSphereHalfMassComplementSup_le_northPole_of_lemma43_heightBands_separateTau_gainSup_equal_mass
    (n : ℕ) [NeZero n] (hn : 2 ≤ n) (r : ℝ)
    (hData :
      ∀ ⦃η : ℝ⦄, 0 < η →
        ∃ eps tauBand tauSep : ℝ, 0 < eps ∧ 0 < tauSep ∧
          ∀ ⦃A : Set (FinRealSphere n)⦄,
            FinRealSphereHalfMassCompetitor n
                (finRealSurfaceProbabilityMeasure n) A →
            finRealSphereNeighbourhoodComplementMass n
                  (finRealSurfaceProbabilityMeasure n) r
                  (finRealSphereClosedHemisphere n
                    (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
              finRealSphereNeighbourhoodComplementMass n
                (finRealSurfaceProbabilityMeasure n) r A →
            ∃ C : Set (FinRealSphere n),
              ∃ pole : FinRealSphere n,
              ∃ a avg : ℝ,
                MeasurableSet C ∧
                (finRealSurfaceProbabilityMeasure n).real C =
                  (finRealSurfaceProbabilityMeasure n).real A ∧
                eps ≤ (finRealSurfaceProbabilityMeasure n).real (C ∆ A) ∧
                (finRealSurfaceProbabilityMeasure n).real
                    (finRealSphereHeightBandAbove n pole a tauBand) ≤ eps / 4 ∧
                (finRealSurfaceProbabilityMeasure n).real
                    (finRealSphereHeightBandBelow n pole a tauBand) ≤ eps / 4 ∧
                SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tauSep
                  (finRealPolarizationMuMinus C A
                    (finRealSphereHeightBandBelow n pole a tauBand))
                  (finRealPolarizationMuPlus C A
                    (finRealSphereHeightBandAbove n pole a tauBand))
                  avg ∧
                avg ≤ sSup (finRealSpherePolarizationObjectiveGainValues n r A)) :
    finRealSphereHalfMassComplementSup n
        (finRealSurfaceProbabilityMeasure n) r ≤
      finRealSphereNeighbourhoodComplementMass n
        (finRealSurfaceProbabilityMeasure n) r
        (finRealSphereClosedHemisphere n
          (finRealSphereNorthPole n : FinRealEuclideanSpace n)) := by
  exact
    finRealSphereHalfMassComplementSup_le_northPole_of_lemma43_measure_trimming_gainSup_equal_mass
      n hn r (fun {η} hη => by
        rcases hData hη with ⟨eps, tauBand, tauSep, heps, htauSep, hDataη⟩
        refine ⟨eps, tauSep, heps, htauSep, ?_⟩
        intro A hA hgap
        rcases hDataη hA hgap with
          ⟨C, pole, a, avg, hC, hmass, hfar, hbandPlus, hbandMinus,
            hRect, havgLeGainSup⟩
        refine ⟨C, finRealSphereHeightBandAbove n pole a tauBand,
          finRealSphereHeightBandBelow n pole a tauBand, avg, hC, ?_, ?_, hmass,
          hfar, hbandPlus, hbandMinus, hRect, havgLeGainSup⟩
        · exact measurableSet_finRealSphereHeightBandAbove n pole a tauBand
        · exact measurableSet_finRealSphereHeightBandBelow n pole a tauBand)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Same-mass height-band Lemma 4.3 data with independent band thickness and
rectangular separation gives the direct uniform gain-supremum supplier. -/
theorem uniform_polarization_gainSup_lower_of_lemma43_heightBands_separateTau_gainSup_equal_mass_pos_lt_pi
    (hData :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tauBand tauSep : ℝ, 0 < eps ∧ 0 < tauSep ∧
              ∀ ⦃A : Set (FinRealSphere n)⦄,
                FinRealSphereHalfMassCompetitor n
                    (finRealSurfaceProbabilityMeasure n) A →
                finRealSphereNeighbourhoodComplementMass n
                      (finRealSurfaceProbabilityMeasure n) r
                      (finRealSphereClosedHemisphere n
                        (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
                  finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r A →
                ∃ C : Set (FinRealSphere n),
                  ∃ pole : FinRealSphere n,
                  ∃ a avg : ℝ,
                    MeasurableSet C ∧
                    (finRealSurfaceProbabilityMeasure n).real C =
                      (finRealSurfaceProbabilityMeasure n).real A ∧
                    eps ≤ (finRealSurfaceProbabilityMeasure n).real (C ∆ A) ∧
                    (finRealSurfaceProbabilityMeasure n).real
                        (finRealSphereHeightBandAbove n pole a tauBand) ≤ eps / 4 ∧
                    (finRealSurfaceProbabilityMeasure n).real
                        (finRealSphereHeightBandBelow n pole a tauBand) ≤ eps / 4 ∧
                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tauSep
                      (finRealPolarizationMuMinus C A
                        (finRealSphereHeightBandBelow n pole a tauBand))
                      (finRealPolarizationMuPlus C A
                        (finRealSphereHeightBandAbove n pole a tauBand))
                      avg ∧
                    avg ≤ sSup (finRealSpherePolarizationObjectiveGainValues n r A)) :
    ∀ (n : ℕ) [NeZero n], 2 ≤ n →
      ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
        ∀ ⦃η : ℝ⦄, 0 < η →
          ∃ δ : ℝ, 0 < δ ∧
            ∀ ⦃A : Set (FinRealSphere n)⦄,
              FinRealSphereHalfMassCompetitor n
                  (finRealSurfaceProbabilityMeasure n) A →
              finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r
                    (finRealSphereClosedHemisphere n
                      (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
                finRealSphereNeighbourhoodComplementMass n
                  (finRealSurfaceProbabilityMeasure n) r A →
              δ ≤
                sSup (finRealSpherePolarizationObjectiveGainValues n r A) := by
  refine
    uniform_polarization_gainSup_lower_of_lemma43_measure_trimming_gainSup_equal_mass_pos_lt_pi
      ?_
  intro n _ hn r hrpos hrlt η hη
  rcases hData n hn hrpos hrlt hη with
    ⟨eps, tauBand, tauSep, heps, htauSep, hDataη⟩
  refine ⟨eps, tauSep, heps, htauSep, ?_⟩
  intro A hA hgap
  rcases hDataη hA hgap with
    ⟨C, pole, a, avg, hC, hmass, hfar, hbandPlus, hbandMinus,
      hRect, havgLeGainSup⟩
  refine ⟨C, finRealSphereHeightBandAbove n pole a tauBand,
    finRealSphereHeightBandBelow n pole a tauBand, avg, hC, ?_, ?_, hmass,
    hfar, hbandPlus, hbandMinus, hRect, havgLeGainSup⟩
  · exact measurableSet_finRealSphereHeightBandAbove n pole a tauBand
  · exact measurableSet_finRealSphereHeightBandBelow n pole a tauBand

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- No-input cap comparison in dimensions at least two follows from a
same-mass height-band supplier with independent band thickness and
rectangular-block separation. -/
theorem sphere_halfMeasure_hemisphereComparisonGeTwo_of_lemma43_heightBands_separateTau_gainSup_equal_mass_pos_lt_pi
    (hData :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tauBand tauSep : ℝ, 0 < eps ∧ 0 < tauSep ∧
              ∀ ⦃A : Set (FinRealSphere n)⦄,
                FinRealSphereHalfMassCompetitor n
                    (finRealSurfaceProbabilityMeasure n) A →
                finRealSphereNeighbourhoodComplementMass n
                      (finRealSurfaceProbabilityMeasure n) r
                      (finRealSphereClosedHemisphere n
                        (finRealSphereNorthPole n : FinRealEuclideanSpace n)) + η ≤
                  finRealSphereNeighbourhoodComplementMass n
                    (finRealSurfaceProbabilityMeasure n) r A →
                ∃ C : Set (FinRealSphere n),
                  ∃ pole : FinRealSphere n,
                  ∃ a avg : ℝ,
                    MeasurableSet C ∧
                    (finRealSurfaceProbabilityMeasure n).real C =
                      (finRealSurfaceProbabilityMeasure n).real A ∧
                    eps ≤ (finRealSurfaceProbabilityMeasure n).real (C ∆ A) ∧
                    (finRealSurfaceProbabilityMeasure n).real
                        (finRealSphereHeightBandAbove n pole a tauBand) ≤ eps / 4 ∧
                    (finRealSurfaceProbabilityMeasure n).real
                        (finRealSphereHeightBandBelow n pole a tauBand) ≤ eps / 4 ∧
                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tauSep
                      (finRealPolarizationMuMinus C A
                        (finRealSphereHeightBandBelow n pole a tauBand))
                      (finRealPolarizationMuPlus C A
                        (finRealSphereHeightBandAbove n pole a tauBand))
                      avg ∧
                    avg ≤ sSup (finRealSpherePolarizationObjectiveGainValues n r A)) :
    sphere_halfMeasure_hemisphereComparisonGeTwo := by
  exact sphere_halfMeasure_hemisphereComparisonGeTwo_of_complementSup_le_northPole_pos_lt_pi
    (fun n _ hn2 {r} hrpos hrlt =>
      finRealSphereHalfMassComplementSup_le_northPole_of_lemma43_heightBands_separateTau_gainSup_equal_mass
        n hn2 r (hData n hn2 hrpos hrlt))

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The north-pole large-exponent coordinate tail supplies the arbitrary-pole
large-exponent coordinate tail by orthogonal invariance. -/
theorem finRealSphereCoordinateGaussianTailInteriorLargeExponent_of_northPole
    (n : ℕ) [NeZero n]
    (hNorth :
      FinRealSphereCoordinateGaussianTailInteriorLargeExponentNorthPole n (n : ℝ)) :
    FinRealSphereCoordinateGaussianTailInteriorLargeExponent n (n : ℝ) := by
  intro c r hn2 hrpos hrlt hlarge
  rw [finRealSphereCoordinateLaw_eq_northPole n c]
  exact hNorth hn2 hrpos hrlt hlarge

omit [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] in
/-- No-input adapter from the north-pole large-exponent coordinate tail package
to the arbitrary-pole large-exponent coordinate-tail package. -/
theorem sphere_coordinateGaussianTailInteriorLargeExponent_of_northPole
    (hNorth : sphere_coordinateGaussianTailInteriorLargeExponentNorthPole) :
    sphere_coordinateGaussianTailInteriorLargeExponent := by
  intro n hn
  exact finRealSphereCoordinateGaussianTailInteriorLargeExponent_of_northPole n (hNorth n)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- In real dimension one, a closed hemisphere is a singleton. -/
theorem finRealSphereClosedHemisphere_one_subset_singleton
    (c : FinRealSphere 1) :
    finRealSphereClosedHemisphere 1 (c : FinRealEuclideanSpace 1) ⊆ {c} := by
  intro x hx
  apply Set.mem_singleton_iff.mpr
  apply Subtype.ext
  ext i
  fin_cases i
  let a : ℝ := ((x : FinRealEuclideanSpace 1).ofLp 0)
  let b : ℝ := ((c : FinRealEuclideanSpace 1).ofLp 0)
  have hxnormsq : a ^ 2 = 1 := by
    have h : ‖(x : FinRealEuclideanSpace 1)‖ ^ 2 = (1 : ℝ) ^ 2 := by
      rw [finRealSphere_coe_norm_eq_one 1 x]
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_one] at h
    simpa [a, Real.norm_eq_abs, sq_abs] using h
  have hcnormsq : b ^ 2 = 1 := by
    have h : ‖(c : FinRealEuclideanSpace 1)‖ ^ 2 = (1 : ℝ) ^ 2 := by
      rw [finRealSphere_coe_norm_eq_one 1 c]
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_one] at h
    simpa [b, Real.norm_eq_abs, sq_abs] using h
  have hinner_nonneg :
      0 ≤ inner ℝ (c : FinRealEuclideanSpace 1) (x : FinRealEuclideanSpace 1) := by
    simpa [mem_finRealSphereClosedHemisphere_iff, finRealSphereInnerCoordinate] using hx
  have hinner_coord : 0 ≤ inner ℝ b a := by
    rw [PiLp.inner_apply, Fin.sum_univ_one] at hinner_nonneg
    simpa [a, b] using hinner_nonneg
  have hprod_nonneg : 0 ≤ a * b := by
    convert hinner_coord using 1
  have hprod_sq : (a * b) ^ 2 = 1 := by
    nlinarith
  have hprod_abs : |a * b| = 1 := by
    have hsq : (a * b) ^ 2 = (1 : ℝ) ^ 2 := by
      simpa using hprod_sq
    simpa using (sq_eq_sq_iff_abs_eq_abs (a * b) (1 : ℝ)).mp hsq
  have hprod_eq : a * b = 1 := by
    rw [abs_of_nonneg hprod_nonneg] at hprod_abs
    exact hprod_abs
  have ha_eq_b : a = b := by
    nlinarith
  simpa [a, b] using ha_eq_b

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The half-measure comparison is elementary on the zero-dimensional sphere:
any half-mass set contains a point, and that point is a closed hemisphere. -/
theorem finRealSphereHalfMeasureHemisphereComparison_one :
    FinRealSphereHalfMeasureHemisphereComparison 1
      (finRealSurfaceProbabilityMeasure 1) := by
  haveI : IsProbabilityMeasure (finRealSurfaceProbabilityMeasure 1) :=
    finRealSurfaceProbabilityMeasure_isProbabilityMeasure 1
  intro A hA hhalf r hr
  have hA_nonempty : ∃ x, x ∈ A := by
    by_contra hne
    push_neg at hne
    have hAempty : A = ∅ := by
      ext x
      constructor
      · intro hx
        exact False.elim (hne x hx)
      · intro hx
        cases hx
    subst A
    have hzero : (finRealSurfaceProbabilityMeasure 1).real (∅ : Set (FinRealSphere 1)) = 0 := by
      simp [measureReal_def]
    linarith
  rcases hA_nonempty with ⟨c, hcA⟩
  refine ⟨c, ?_⟩
  have hH_subset_A : finRealSphereClosedHemisphere 1 (c : FinRealEuclideanSpace 1) ⊆ A := by
    intro x hx
    have hxc : x = c :=
      Set.mem_singleton_iff.mp (finRealSphereClosedHemisphere_one_subset_singleton c hx)
    simpa [hxc]
  have hthick_subset :
      finRealSphereGeodesicThickening 1 r
          (finRealSphereClosedHemisphere 1 (c : FinRealEuclideanSpace 1)) ⊆
        finRealSphereGeodesicThickening 1 r A := by
    intro x hx
    rcases hx with ⟨y, hy, hdist⟩
    exact ⟨y, hH_subset_A hy, hdist⟩
  have hcompl_subset :
      (finRealSphereGeodesicThickening 1 r A)ᶜ ⊆
        (finRealSphereGeodesicThickening 1 r
          (finRealSphereClosedHemisphere 1 (c : FinRealEuclideanSpace 1)))ᶜ :=
    Set.compl_subset_compl.mpr hthick_subset
  exact measureReal_mono hcompl_subset
    (h₂ := (measure_lt_top (finRealSurfaceProbabilityMeasure 1)
      ((finRealSphereGeodesicThickening 1 r
        (finRealSphereClosedHemisphere 1 (c : FinRealEuclideanSpace 1)))ᶜ)).ne)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The dimension-at-least-two cap-comparison package supplies the full
cap-comparison package because the `n = 1` case is elementary. -/
theorem sphere_halfMeasure_hemisphereComparison_of_geTwo
    (hGeTwo : sphere_halfMeasure_hemisphereComparisonGeTwo) :
    sphere_halfMeasure_hemisphereComparison := by
  intro n hn
  by_cases hn2 : 2 ≤ n
  · exact hGeTwo n hn2
  · have hn1 : n = 1 := by
      have hlt : n < 2 := lt_of_not_ge hn2
      rcases n with (_ | _ | n)
      · cases NeZero.ne 0 rfl
      · rfl
      · exfalso
        exact Nat.not_lt_of_ge
          (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n))) hlt
    subst hn1
    exact finRealSphereHalfMeasureHemisphereComparison_one

omit [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] in
/-- No-input adapter from the interior coordinate tail to the closed
small-radius coordinate tail used by the hemisphere Gaussian estimate. -/
theorem sphere_coordinateGaussianTail_of_interior
    (hInterior : sphere_coordinateGaussianTailInterior) :
    sphere_coordinateGaussianTail := by
  intro n hn
  exact finRealSphereCoordinateGaussianTail_of_interior n (hInterior n)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
theorem finRealSphereGeodesicThickening_closedHemisphere_compl_subset_antipode
    (n : ℕ) (c : FinRealSphere n) {r : ℝ}
    (hr : r = Real.pi / 2) {x : FinRealSphere n}
    (hx :
      x ∈
        (finRealSphereGeodesicThickening n r
          (finRealSphereClosedHemisphere n (c : FinRealEuclideanSpace n)))ᶜ) :
    x = finRealSphere_neg n c := by
  simp only [finRealSphereGeodesicThickening, Set.mem_compl_iff, Set.mem_setOf_eq] at hx
  push_neg at hx
  by_contra hne
  have ht_gt : -1 < finRealSphereInnerCoordinate n (c : FinRealEuclideanSpace n) x := by
    rcases eq_or_lt_of_le (finRealSphere_inner_ge_neg_one n c x) with h_eq | h_lt
    · exfalso
      exact hne ((finRealSphere_inner_eq_neg_one_iff_eq_neg n c x).mp h_eq.symm)
    · exact h_lt
  rcases lt_or_ge (finRealSphereInnerCoordinate n (c : FinRealEuclideanSpace n) x) 0 with
      htneg | htnonneg
  · have hc_norm : ‖(c : FinRealEuclideanSpace n)‖ = 1 :=
      finRealSphere_coe_norm_eq_one n c
    set y := finRealSphere_equatorPoint n
      (c : FinRealEuclideanSpace n) x hc_norm htneg ht_gt
    have hy : y ∈ finRealSphereClosedHemisphere n (c : FinRealEuclideanSpace n) :=
      finRealSphere_equatorPoint_mem_closedHemisphere n
        (c : FinRealEuclideanSpace n) x hc_norm htneg ht_gt
    have hgeo := hx y hy
    linarith [hgeo,
      finRealSphere_geodesicDistance_to_equatorPoint_lt_pi_div_two
        n (c : FinRealEuclideanSpace n) x hc_norm htneg ht_gt,
      hr]
  · have hxH : x ∈ finRealSphereClosedHemisphere n (c : FinRealEuclideanSpace n) := by
      rwa [mem_finRealSphereClosedHemisphere_iff]
    have hgeo := hx x hxH
    linarith [finRealSphereGeodesicDistance_self n x, hgeo, hr, Real.pi_div_two_pos]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Boundary radius `r = π/2`: the hemisphere thickening complement is the antipode,
which has zero surface measure in dimension at least two. -/
theorem finRealSurfaceProbabilityMeasure_hemisphereLargeRadiusTail_at_pi_div_two
    (n : ℕ) [NeZero n] (hn2 : 2 ≤ n) (c : FinRealSphere n) {r : ℝ}
    (hr : r = Real.pi / 2) :
    (finRealSurfaceProbabilityMeasure n).real
        ((finRealSphereGeodesicThickening n r
          (finRealSphereClosedHemisphere n (c : FinRealEuclideanSpace n)))ᶜ) ≤
      Real.exp (-((((n : ℝ) - 1) * r ^ 2) / 2)) := by
  have hsubset :
      ((finRealSphereGeodesicThickening n r
          (finRealSphereClosedHemisphere n (c : FinRealEuclideanSpace n)))ᶜ) ⊆
        {finRealSphere_neg n c} := by
    intro x hx'
    exact finRealSphereGeodesicThickening_closedHemisphere_compl_subset_antipode
      (n := n) (c := c) (hr := hr) (x := x) (hx := hx')
  haveI : IsProbabilityMeasure (finRealSurfaceProbabilityMeasure n) :=
    finRealSurfaceProbabilityMeasure_isProbabilityMeasure n
  have hzero :
      (finRealSurfaceProbabilityMeasure n).real {finRealSphere_neg n c} = 0 := by
    rw [measureReal_def, finRealSurfaceProbabilityMeasure_singleton n hn2
      (finRealSphere_neg n c)]
    simp
  exact
    (measureReal_mono hsubset
      (h₂ := (measure_lt_top (finRealSurfaceProbabilityMeasure n) _).ne)).trans
      (by rw [hzero]; exact Real.exp_nonneg _)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
theorem finRealSphereHemisphereLargeRadiusTail_at_pi_div_two (n : ℕ) [NeZero n]
    (c : FinRealSphere n) {r : ℝ} (hr : r = Real.pi / 2) :
    (finRealSurfaceProbabilityMeasure n).real
        ((finRealSphereGeodesicThickening n r
          (finRealSphereClosedHemisphere n (c : FinRealEuclideanSpace n)))ᶜ) ≤
      Real.exp (-((((n : ℝ) - 1) * r ^ 2) / 2)) := by
  by_cases hn2 : 2 ≤ n
  · exact finRealSurfaceProbabilityMeasure_hemisphereLargeRadiusTail_at_pi_div_two n hn2 c hr
  · have hn1 : n = 1 := by
      have hlt : n < 2 := lt_of_not_ge hn2
      rcases n with (_ | _ | n)
      · cases NeZero.ne 0 rfl
      · rfl
      · exfalso
        exact Nat.not_lt_of_ge (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n))) hlt
    subst hn1
    haveI := finRealSurfaceProbabilityMeasure_isProbabilityMeasure 1
    have hrhs :
        Real.exp (-((↑(1 : ℕ) - 1) * (Real.pi / 2) ^ 2 / 2)) = 1 := by
      simp
    rw [hr, hrhs]
    exact measureReal_le_one

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- For `r ≥ π/2`, the complement of the open `r`-neighbourhood of a closed
hemisphere is contained in the antipode singleton.  The boundary case was
proved above; the monotonicity in `r` gives the general large-radius case. -/
theorem finRealSphereGeodesicThickening_closedHemisphere_largeRadius_compl_subset_antipode
    (n : ℕ) (c : FinRealSphere n) {r : ℝ}
    (hr : Real.pi / 2 ≤ r) :
    ((finRealSphereGeodesicThickening n r
        (finRealSphereClosedHemisphere n (c : FinRealEuclideanSpace n)))ᶜ) ⊆
      {finRealSphere_neg n c} := by
  intro x hx
  have hx_pi :
      x ∈
        (finRealSphereGeodesicThickening n (Real.pi / 2)
          (finRealSphereClosedHemisphere n (c : FinRealEuclideanSpace n)))ᶜ := by
    intro hxmem
    rcases hxmem with ⟨y, hyH, hdist⟩
    exact hx ⟨y, hyH, lt_of_lt_of_le hdist hr⟩
  exact
    finRealSphereGeodesicThickening_closedHemisphere_compl_subset_antipode
      (n := n) (c := c) (r := Real.pi / 2) (hr := rfl)
      (x := x) (hx := hx_pi)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Large-radius hemisphere tail for the normalized surface probability in
dimension at least two. -/
theorem finRealSurfaceProbabilityMeasure_hemisphereLargeRadiusTail
    (n : ℕ) [NeZero n] (hn2 : 2 ≤ n) (c : FinRealSphere n) {r : ℝ}
    (hr : Real.pi / 2 ≤ r) :
    (finRealSurfaceProbabilityMeasure n).real
        ((finRealSphereGeodesicThickening n r
          (finRealSphereClosedHemisphere n (c : FinRealEuclideanSpace n)))ᶜ) ≤
      Real.exp (-((((n : ℝ) - 1) * r ^ 2) / 2)) := by
  have hsubset :
      ((finRealSphereGeodesicThickening n r
          (finRealSphereClosedHemisphere n (c : FinRealEuclideanSpace n)))ᶜ) ⊆
        {finRealSphere_neg n c} :=
    finRealSphereGeodesicThickening_closedHemisphere_largeRadius_compl_subset_antipode
      n c hr
  haveI : IsProbabilityMeasure (finRealSurfaceProbabilityMeasure n) :=
    finRealSurfaceProbabilityMeasure_isProbabilityMeasure n
  have hzero :
      (finRealSurfaceProbabilityMeasure n).real {finRealSphere_neg n c} = 0 := by
    rw [measureReal_def, finRealSurfaceProbabilityMeasure_singleton n hn2
      (finRealSphere_neg n c)]
    simp
  exact
    (measureReal_mono hsubset
      (h₂ := (measure_lt_top (finRealSurfaceProbabilityMeasure n) _).ne)).trans
      (by rw [hzero]; exact Real.exp_nonneg _)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Large-radius hemisphere tail for every nonzero concrete real sphere. -/
theorem finRealSphereHemisphereLargeRadiusTail_surface
    (n : ℕ) [NeZero n] :
    FinRealSphereHemisphereLargeRadiusTail n
      (finRealSurfaceProbabilityMeasure n) (n : ℝ) := by
  intro c r hr
  by_cases hn2 : 2 ≤ n
  · exact finRealSurfaceProbabilityMeasure_hemisphereLargeRadiusTail n hn2 c hr
  · have hn1 : n = 1 := by
      have hlt : n < 2 := lt_of_not_ge hn2
      rcases n with (_ | _ | n)
      · cases NeZero.ne 0 rfl
      · rfl
      · exfalso
        exact Nat.not_lt_of_ge
          (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n))) hlt
    subst hn1
    haveI := finRealSurfaceProbabilityMeasure_isProbabilityMeasure 1
    have hrhs :
        Real.exp (-((((1 : ℕ) : ℝ) - 1) * r ^ 2 / 2)) = 1 := by
      simp
    rw [hrhs]
    exact measureReal_le_one

omit [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] in
/-- No-input large-radius hemisphere neighbourhood tail supplier. -/
theorem sphere_hemisphereLargeRadiusTail_surface :
    sphere_hemisphereLargeRadiusTail := by
  intro n hn
  exact finRealSphereHemisphereLargeRadiusTail_surface n

end AppendixB
end PptFactorization
