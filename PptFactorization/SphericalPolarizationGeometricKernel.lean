import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic

/-!
# Spherical polarization: geometric kernel interface

This file is the geometric companion to the quantitative strict-improvement
core. It isolates the objects coming from the spherical reflection argument:

* the oriented half-space `halfSpace v`;
* the admissible directions `admissibleDirections p`;
* the reflection `reflection v x = x - 2 * inner x v • v`;
* the explicit kernel

  `2^{-(n-2)} * sin(d_geo x y / 2)^{-(n-2)}`

  off the diagonal, and `0` on the diagonal;
* the equivalent chordal/Frobenius form

  `2^{-(n-2)} * (‖x-y‖/2)^{-(n-2)}`

  on unit vectors, which is the form used in the push-forward density;
* the proposition `HasKernelChangeOfVariables`, expressing the positive
  function change-of-variables theorem needed in Lemma 4.3.

There are no primitive assumptions here. The actual analytic Jacobian theorem
is supplied by `Mathlib.MeasureTheory.Function.Jacobian`; this file gives
stable local wrapper names for those mathlib change-of-variables theorems.
What remains, for the spherical polarization proof itself, is the
sphere-specific specialization: construct the polarization parametrization,
verify its chartwise differentiability and injectivity, compute the determinant
as the displayed kernel, and identify the surface measures.
-/

noncomputable section

open Classical
open MeasureTheory
open scoped ENNReal

namespace SphericalPolarization.GeometricKernel

/-! ## Mathlib Jacobian suppliers -/

section MathlibJacobianSupplier

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Stable local name for mathlib's positive-integral image change-of-variables
formula on finite-dimensional real normed spaces.

This is the general Jacobian supplier.  The spherical kernel still requires a
separate specialization/computation of the chosen spherical parametrization. -/
theorem mathlib_lintegral_image_eq_lintegral_abs_det_fderiv_mul
    {s : Set E} {f : E → E} {f' : E → E →L[ℝ] E}
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hf : Set.InjOn f s)
    (g : E → ℝ≥0∞) :
    ∫⁻ x in f '' s, g x ∂μ =
      ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * g (f x) ∂μ := by
  exact MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
    μ hs hf' hf g

/-- Stable local name for mathlib's Bochner-integral image change-of-variables
formula on finite-dimensional real normed spaces. -/
theorem mathlib_integral_image_eq_integral_abs_det_fderiv_smul
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {f : E → E} {f' : E → E →L[ℝ] E}
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hf : Set.InjOn f s)
    (g : E → F) :
    ∫ x in f '' s, g x ∂μ =
      ∫ x in s, |(f' x).det| • g (f x) ∂μ := by
  exact MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
    μ hs hf' hf g

/-- Stable local name for the mathlib Jacobian formula with constant
integrand, identifying the integral of the absolute determinant with the
additive Haar measure of the image. -/
theorem mathlib_lintegral_abs_det_fderiv_eq_addHaar_image
    {s : Set E} {f : E → E} {f' : E → E →L[ℝ] E}
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hf : Set.InjOn f s) :
    ∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ = μ (f '' s) := by
  exact MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image
    μ hs hf' hf

end MathlibJacobianSupplier

/-! ## Elementary inner-product geometry -/

section InnerProductGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Height with respect to the pole `p`: `phi(x)=inner x p`. -/
def height (p x : E) : ℝ :=
  inner ℝ x p

/-- The oriented half-space `H_v = {x : 0 ≤ inner x v}`. -/
def halfSpace (v : E) : Set E :=
  {x | 0 ≤ inner ℝ x v}

/-- The admissible half-sphere of directions `V_p = {v : 0 ≤ inner v p}`. -/
def admissibleDirections (p : E) : Set E :=
  {v | 0 ≤ inner ℝ v p}

/-- Reflection in the hyperplane orthogonal to `v`. On the unit sphere and
for unit `v`, this is the map denoted `rho_v` in the paper. -/
def reflection (v x : E) : E :=
  x - (2 * inner ℝ x v) • v

lemma mem_halfSpace_iff {v x : E} :
    x ∈ halfSpace v ↔ 0 ≤ inner ℝ x v := by
  rfl

lemma mem_admissibleDirections_iff {p v : E} :
    v ∈ admissibleDirections p ↔ 0 ≤ inner ℝ v p := by
  rfl

/-- Algebraic gain identity for an admissible reflection:

`phi(y)-phi(rho_v y) = 2 * inner y v * inner v p`.

This is the pointwise identity used before integrating the improvement. -/
lemma height_sub_height_reflection (p v y : E) :
    height p y - height p (reflection v y) =
      2 * inner ℝ y v * inner ℝ v p := by
  unfold height reflection
  simp [inner_sub_left, inner_smul_left, mul_comm]

/-- If `y ∈ H_v` and `v ∈ V_p`, then reflecting `y` cannot increase its
height relative to `p`. -/
lemma height_reflection_le_height
    {p v y : E}
    (hy : y ∈ halfSpace v)
    (hv : v ∈ admissibleDirections p) :
    height p (reflection v y) ≤ height p y := by
  rw [mem_halfSpace_iff] at hy
  rw [mem_admissibleDirections_iff] at hv
  have hprod : 0 ≤ inner ℝ y v * inner ℝ v p := mul_nonneg hy hv
  have hgap : 0 ≤ height p y - height p (reflection v y) := by
    rw [height_sub_height_reflection]
    nlinarith
  linarith

/-- Strict version of `height_reflection_le_height`. -/
lemma height_reflection_lt_height
    {p v y : E}
    (hy : 0 < inner ℝ y v)
    (hv : 0 < inner ℝ v p) :
    height p (reflection v y) < height p y := by
  have hprod : 0 < inner ℝ y v * inner ℝ v p := mul_pos hy hv
  have hgap : 0 < height p y - height p (reflection v y) := by
    rw [height_sub_height_reflection]
    nlinarith
  linarith

/-- The inverse direction in the polarization parametrization:
`v(x) = (y - x) / ‖y - x‖`. -/
def polarizationInverseDirection (y x : E) : E :=
  (‖y - x‖)⁻¹ • (y - x)

/-- For `x ≠ y`, the inverse direction has unit norm. -/
lemma polarizationInverseDirection_norm_eq_one
    {y x : E} (hxy : x ≠ y) :
    ‖polarizationInverseDirection y x‖ = 1 := by
  unfold polarizationInverseDirection
  have hsub : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  have hnorm_pos : 0 < ‖y - x‖ := norm_pos_iff.mpr hsub
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact inv_mul_cancel₀ (ne_of_gt hnorm_pos)

/-- Unit-sphere algebra behind
`⟪y, y - x⟫ = ‖y - x‖^2 / 2`. -/
lemma inner_sub_self_of_unit
    {y x : E} (hy : ‖y‖ = 1) (hx : ‖x‖ = 1) :
    inner ℝ y (y - x) = ‖y - x‖ ^ 2 / 2 := by
  have hy2 : ‖y‖ ^ 2 = 1 := by rw [hy]; norm_num
  have hx2 : ‖x‖ ^ 2 = 1 := by rw [hx]; norm_num
  have hnormsq : ‖y - x‖ ^ 2 =
      inner ℝ (y - x) (y - x) := by
    rw [← real_inner_self_eq_norm_sq]
  rw [hnormsq]
  simp only [inner_sub_left, inner_sub_right]
  have hyy : inner ℝ y y = 1 := by
    rw [real_inner_self_eq_norm_sq, hy2]
  have hxx : inner ℝ x x = 1 := by
    rw [real_inner_self_eq_norm_sq, hx2]
  rw [hyy, hxx]
  have hxycomm : inner ℝ x y = inner ℝ y x := (real_inner_comm x y).symm
  rw [hxycomm]
  ring

/-- For unit `x,y`, the inverse direction satisfies
`⟪y, v(x)⟫ = ‖y - x‖ / 2`. -/
lemma inner_unit_polarizationInverseDirection
    {y x : E} (hy : ‖y‖ = 1) (hx : ‖x‖ = 1) :
    inner ℝ y (polarizationInverseDirection y x) = ‖y - x‖ / 2 := by
  unfold polarizationInverseDirection
  rw [inner_smul_right, inner_sub_self_of_unit hy hx]
  by_cases h : ‖y - x‖ = 0
  · simp [h]
  · field_simp [h]

/-- For distinct unit `x,y`, the inverse direction lies in the open
half-sphere where `⟪y,v⟫ > 0`. -/
lemma inner_unit_polarizationInverseDirection_pos
    {y x : E} (hy : ‖y‖ = 1) (hx : ‖x‖ = 1) (hxy : x ≠ y) :
    0 < inner ℝ y (polarizationInverseDirection y x) := by
  rw [inner_unit_polarizationInverseDirection hy hx]
  have hsub : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  have hnorm_pos : 0 < ‖y - x‖ := norm_pos_iff.mpr hsub
  positivity

/-- The explicit inverse direction inverts the reflection parametrization:
if `x,y` are distinct unit vectors, then reflecting `y` across the hyperplane
normal to `(y - x)/‖y - x‖` gives `x`. -/
lemma reflection_polarizationInverseDirection_eq
    {y x : E} (hy : ‖y‖ = 1) (hx : ‖x‖ = 1) (hxy : x ≠ y) :
    reflection (polarizationInverseDirection y x) y = x := by
  unfold reflection
  have hsub : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  have hnorm_pos : 0 < ‖y - x‖ := norm_pos_iff.mpr hsub
  have hinner :
      inner ℝ y (polarizationInverseDirection y x) = ‖y - x‖ / 2 :=
    inner_unit_polarizationInverseDirection hy hx
  rw [hinner]
  unfold polarizationInverseDirection
  have hscale : (2 * (‖y - x‖ / 2)) * (‖y - x‖)⁻¹ = 1 := by
    field_simp [ne_of_gt hnorm_pos]
  rw [smul_smul]
  rw [hscale]
  simp

/-- Reflection across a unit normal preserves norms. -/
lemma reflection_norm_eq_of_unit
    {v y : E} (hv : ‖v‖ = 1) :
    ‖reflection v y‖ = ‖y‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  unfold reflection
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
  have hvv : inner ℝ v v = 1 := by
    rw [real_inner_self_eq_norm_sq]
    rw [hv]
    norm_num
  rw [hvv]
  rw [← real_inner_comm v y]
  simp [mul_assoc, mul_left_comm, mul_comm]
  ring_nf

/-- Chord from the pole to its reflected image. -/
lemma sub_reflection_eq_two_inner_smul (v y : E) :
    y - reflection v y = (2 * inner ℝ y v) • v := by
  unfold reflection
  abel

/-- On the positive half-sphere, the Frobenius/chordal half-distance from
`y` to its reflected point is exactly the parameter `⟪y,v⟫`. -/
lemma half_chordal_distance_reflection_eq_inner_of_unit_pos
    {y v : E} (hv : ‖v‖ = 1) (hpos : 0 < inner ℝ y v) :
    ‖y - reflection v y‖ / 2 = inner ℝ y v := by
  rw [sub_reflection_eq_two_inner_smul]
  rw [norm_smul, hv]
  have hpos2 : 0 < 2 * inner ℝ y v := by nlinarith
  rw [Real.norm_eq_abs, abs_of_pos hpos2]
  ring

/-- Unit vectors have inner product in `[-1,1]`. -/
lemma inner_bounds_of_unit
    {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    -1 ≤ inner ℝ x y ∧ inner ℝ x y ≤ 1 := by
  have h : |inner ℝ x y| ≤ (1 : ℝ) := by
    simpa [hx, hy] using abs_real_inner_le_norm x y
  exact abs_le.mp h

/-- For unit vectors, the sine of half the intrinsic spherical distance
`arccos ⟪x,y⟫` is the Frobenius/chordal half-distance. -/
lemma sin_arccos_half_eq_half_norm_sub_of_unit
    {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    Real.sin (Real.arccos (inner ℝ x y) / 2) = ‖x - y‖ / 2 := by
  have hbounds := inner_bounds_of_unit (x := x) (y := y) hx hy
  rw [Real.sin_half_eq_sqrt (Real.arccos_nonneg _)
    (by linarith [Real.arccos_le_pi (inner ℝ x y), Real.pi_pos.le])]
  rw [Real.cos_arccos hbounds.1 hbounds.2]
  have hleft : inner ℝ x (x - y) = 1 - inner ℝ x y := by
    simp only [inner_sub_right]
    have hxx : inner ℝ x x = 1 := by
      rw [real_inner_self_eq_norm_sq, hx]
      norm_num
    rw [hxx]
  have hbase := inner_sub_self_of_unit (y := x) (x := y) hx hy
  rw [hleft] at hbase
  have hsqrt : √((1 - inner ℝ x y) / 2) = ‖x - y‖ / 2 := by
    rw [hbase]
    have hrewrite : ‖x - y‖ ^ 2 / 2 / 2 = (‖x - y‖ / 2) ^ 2 := by
      ring
    rw [hrewrite, Real.sqrt_sq_eq_abs]
    rw [abs_of_nonneg]
    positivity
  exact hsqrt

/-- Specialization of the half-angle/chordal bridge to the reflection
parametrization.  This identifies the `sin(d(x,y)/2)` factor in the kernel
with `⟪y,v⟫` before the final tangent-determinant calculation. -/
lemma sin_arccos_half_reflection_eq_inner_of_unit_pos
    {y v : E} (hy : ‖y‖ = 1) (hv : ‖v‖ = 1)
    (hpos : 0 < inner ℝ y v) :
    Real.sin (Real.arccos (inner ℝ (reflection v y) y) / 2) =
      inner ℝ y v := by
  have hx : ‖reflection v y‖ = 1 := by
    rw [reflection_norm_eq_of_unit hv, hy]
  rw [sin_arccos_half_eq_half_norm_sub_of_unit
    (x := reflection v y) (y := y) hx hy]
  have hnormsym : ‖reflection v y - y‖ = ‖y - reflection v y‖ := by
    rw [← norm_neg (reflection v y - y)]
    congr 1
    abel
  rw [hnormsym]
  exact half_chordal_distance_reflection_eq_inner_of_unit_pos hv hpos

/-- Algebraic normalization of the tangent Jacobian factor.

The tangent singular-value computation gives the unnormalized Jacobian
`2 * (2 * a)^(n-2)`.  Pushing forward the normalized half-sphere measure
contributes the extra factor `2`; this lemma rewrites the resulting inverse
Jacobian as the paper's kernel scalar. -/
lemma normalized_inverse_tangent_jacobian_factor
    (n : ℕ) {a : ℝ} (ha : a ≠ 0) :
    2 * (2 * (2 * a) ^ (n - 2))⁻¹ =
      ((2 : ℝ) ^ (n - 2))⁻¹ * (a ^ (n - 2))⁻¹ := by
  rw [mul_pow]
  field_simp [ha]

/-- The same normalization after substituting the reflection half-angle
identity `sin(arccos ⟪rho_v y,y⟫ / 2) = ⟪y,v⟫`. -/
lemma normalized_inverse_tangent_jacobian_reflection_eq_spherical_kernel_factor
    (n : ℕ) {y v : E} (hy : ‖y‖ = 1) (hv : ‖v‖ = 1)
    (hpos : 0 < inner ℝ y v) :
    2 * (2 * (2 * inner ℝ y v) ^ (n - 2))⁻¹ =
      ((2 : ℝ) ^ (n - 2))⁻¹ *
        ((Real.sin (Real.arccos (inner ℝ (reflection v y) y) / 2)) ^ (n - 2))⁻¹ := by
  rw [sin_arccos_half_reflection_eq_inner_of_unit_pos hy hv hpos]
  exact normalized_inverse_tangent_jacobian_factor n (ne_of_gt hpos)

/-- The reflection parametrization is injective on the open half-sphere
`{v | ‖v‖ = 1 ∧ 0 < ⟪y,v⟫}`. -/
lemma reflection_injOn_positive_halfSphere
    {y : E} :
    Set.InjOn (fun v => reflection v y)
      {v : E | ‖v‖ = 1 ∧ 0 < inner ℝ y v} := by
  intro v₁ hv₁ v₂ hv₂ hEq
  have hscale :
      (2 * inner ℝ y v₁) • v₁ = (2 * inner ℝ y v₂) • v₂ := by
    unfold reflection at hEq
    exact sub_right_injective hEq
  have hnormEq := congrArg norm hscale
  simp only [norm_smul, Real.norm_eq_abs, hv₁.1, hv₂.1, mul_one] at hnormEq
  have hpos₁ : 0 < 2 * inner ℝ y v₁ := by nlinarith [hv₁.2]
  have hpos₂ : 0 < 2 * inner ℝ y v₂ := by nlinarith [hv₂.2]
  have habs₁ : |2 * inner ℝ y v₁| = 2 * inner ℝ y v₁ := abs_of_pos hpos₁
  have habs₂ : |2 * inner ℝ y v₂| = 2 * inner ℝ y v₂ := abs_of_pos hpos₂
  rw [habs₁, habs₂] at hnormEq
  have hcoef : 2 * inner ℝ y v₁ = 2 * inner ℝ y v₂ := hnormEq
  have hcoef_ne : 2 * inner ℝ y v₁ ≠ 0 := ne_of_gt hpos₁
  rw [← hcoef] at hscale
  exact (smul_right_injective E hcoef_ne) hscale

/-- The reflection parametrization maps the positive half-sphere into the
punctured unit sphere. -/
lemma reflection_mapsTo_positive_halfSphere_punctured_unitSphere
    {y : E} (hy : ‖y‖ = 1) :
    Set.MapsTo (fun v => reflection v y)
      {v : E | ‖v‖ = 1 ∧ 0 < inner ℝ y v}
      {x : E | ‖x‖ = 1 ∧ x ≠ y} := by
  intro v hv
  constructor
  · rw [reflection_norm_eq_of_unit hv.1, hy]
  · intro hEq
    have hv' : 0 < inner ℝ v y := by
      simpa [real_inner_comm] using hv.2
    have hheight :
        height y (reflection v y) < height y y :=
      height_reflection_lt_height hv.2 hv'
    have hEq' : reflection v y = y := hEq
    rw [hEq'] at hheight
    exact (lt_irrefl _ hheight)

/-- Every point of the punctured unit sphere is reached by reflecting `y` in
the inverse direction `(y - x)/‖y - x‖`. -/
lemma reflection_surjOn_positive_halfSphere_punctured_unitSphere
    {y : E} (hy : ‖y‖ = 1) :
    Set.SurjOn (fun v => reflection v y)
      {v : E | ‖v‖ = 1 ∧ 0 < inner ℝ y v}
      {x : E | ‖x‖ = 1 ∧ x ≠ y} := by
  intro x hx
  refine ⟨polarizationInverseDirection y x, ?_, ?_⟩
  · exact ⟨polarizationInverseDirection_norm_eq_one hx.2,
      inner_unit_polarizationInverseDirection_pos hy hx.1 hx.2⟩
  · exact reflection_polarizationInverseDirection_eq hy hx.1 hx.2

/-- The reflection parametrization is a bijection from the open positive
half-sphere around `y` to the punctured unit sphere. -/
theorem reflection_bijOn_positive_halfSphere_punctured_unitSphere
    {y : E} (hy : ‖y‖ = 1) :
    Set.BijOn (fun v => reflection v y)
      {v : E | ‖v‖ = 1 ∧ 0 < inner ℝ y v}
      {x : E | ‖x‖ = 1 ∧ x ≠ y} := by
  exact ⟨reflection_mapsTo_positive_halfSphere_punctured_unitSphere hy,
    reflection_injOn_positive_halfSphere,
    reflection_surjOn_positive_halfSphere_punctured_unitSphere hy⟩

/-- Ambient Fréchet derivative of `v ↦ reflection v y` at `v`.  The later
tangent-space Jacobian calculation restricts this map to `T_v S^{n-1}`. -/
def reflectionFDeriv (y v : E) : E →L[ℝ] E :=
  - ((2 * inner ℝ y v) • ContinuousLinearMap.id ℝ E +
      ((2 : ℝ) • (innerSL ℝ (E := E) y)).smulRight v)

/-- Pointwise form of the ambient derivative:
`D_v rho_y(w) = -2⟪y,w⟫v - 2⟪y,v⟫w`. -/
lemma reflectionFDeriv_apply (y v w : E) :
    reflectionFDeriv y v w =
      -((2 * inner ℝ y w) • v + (2 * inner ℝ y v) • w) := by
  unfold reflectionFDeriv
  simp [add_comm, mul_comm]

/-- Ambient differentiability of the reflection parametrization. -/
lemma hasFDerivAt_reflection (y v : E) :
    HasFDerivAt (fun z : E => reflection z y) (reflectionFDeriv y v) v := by
  unfold reflection reflectionFDeriv
  have hc :
      HasFDerivAt (fun z : E => 2 * inner ℝ y z)
        ((2 : ℝ) • (innerSL ℝ (E := E) y)) v := by
    have hc0 :=
      ((innerSL ℝ (E := E) y).hasFDerivAt (x := v)).const_smul (2 : ℝ)
    simpa [Pi.smul_apply, innerSL_apply_apply] using hc0
  have hid : HasFDerivAt (fun z : E => z) (ContinuousLinearMap.id ℝ E) v :=
    hasFDerivAt_id v
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    ((hc.smul hid).neg.const_add y)

/-- Within-set version of the ambient differentiability statement. -/
lemma hasFDerivWithinAt_reflection (y v : E) (s : Set E) :
    HasFDerivWithinAt (fun z : E => reflection z y) (reflectionFDeriv y v) s v :=
  (hasFDerivAt_reflection y v).hasFDerivWithinAt

/-- The ambient derivative sends tangent vectors at a unit source point to
tangent vectors at the reflected target point. -/
lemma reflectionFDeriv_apply_tangent_to_reflection_tangent
    {y v w : E} (hv : ‖v‖ = 1) (hw : inner ℝ v w = 0) :
    inner ℝ (reflection v y) (reflectionFDeriv y v w) = 0 := by
  rw [reflectionFDeriv_apply]
  unfold reflection
  simp only [inner_sub_left, inner_neg_right, inner_add_right, inner_smul_left,
    inner_smul_right]
  have hvv : inner ℝ v v = 1 := by
    rw [real_inner_self_eq_norm_sq]
    rw [hv]
    norm_num
  rw [hvv, hw]
  simp
  ring

/-- The tangent hyperplane at an ambient point `x`, represented as the
orthogonal complement of `x`.  On the unit sphere this is the usual tangent
space. -/
def tangentSubspace (x : E) : Submodule ℝ E where
  carrier := {w | inner ℝ x w = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change inner ℝ x a = 0 at ha
    change inner ℝ x b = 0 at hb
    change inner ℝ x (a + b) = 0
    rw [inner_add_right, ha, hb]
    norm_num
  smul_mem' := by
    intro c w hw
    change inner ℝ x w = 0 at hw
    change inner ℝ x (c • w) = 0
    rw [inner_smul_right, hw]
    simp

lemma mem_tangentSubspace_iff {x w : E} :
    w ∈ tangentSubspace x ↔ inner ℝ x w = 0 := by
  rfl

/-- The ambient derivative restricted to tangent hyperplanes.  This is the
linear map whose determinant is computed in the spherical Jacobian theorem. -/
def reflectionTangentDeriv (y v : E) (hv : ‖v‖ = 1) :
    tangentSubspace v →ₗ[ℝ] tangentSubspace (reflection v y) where
  toFun w := ⟨reflectionFDeriv y v (w : E),
    reflectionFDeriv_apply_tangent_to_reflection_tangent hv w.2⟩
  map_add' w₁ w₂ := by
    apply Subtype.ext
    simp
  map_smul' c w := by
    apply Subtype.ext
    simp

lemma coe_reflectionTangentDeriv
    {y v : E} (hv : ‖v‖ = 1) (w : tangentSubspace v) :
    (reflectionTangentDeriv y v hv w : E) =
      reflectionFDeriv y v (w : E) := by
  rfl

/-- The codimension-two block orthogonal to both `v` and `y`.

Inside the tangent space at `v`, this is the block perpendicular to the
meridian direction.  An orthonormal basis of this subspace supplies the
`n-2` equal singular directions in the spherical Jacobian computation. -/
def planeOrthogonalSubspace (y v : E) : Submodule ℝ E where
  carrier := {w | inner ℝ v w = 0 ∧ inner ℝ y w = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    constructor
    · rw [inner_add_right, ha.1, hb.1]
      norm_num
    · rw [inner_add_right, ha.2, hb.2]
      norm_num
  smul_mem' := by
    intro c w hw
    constructor
    · rw [inner_smul_right, hw.1]
      simp
    · rw [inner_smul_right, hw.2]
      simp

lemma mem_planeOrthogonalSubspace_iff {y v w : E} :
    w ∈ planeOrthogonalSubspace y v ↔
      inner ℝ v w = 0 ∧ inner ℝ y w = 0 := by
  rfl

/-- The codimension-two block included into the tangent hyperplane at `v`. -/
def planeOrthogonalSubspace.toTangent (y v : E) :
    planeOrthogonalSubspace y v →ₗ[ℝ] tangentSubspace v where
  toFun w := ⟨(w : E), w.2.1⟩
  map_add' w₁ w₂ := by
    apply Subtype.ext
    rfl
  map_smul' c w := by
    apply Subtype.ext
    rfl

lemma coe_planeOrthogonalSubspace_toTangent
    {y v : E} (w : planeOrthogonalSubspace y v) :
    ((planeOrthogonalSubspace.toTangent y v w : tangentSubspace v) : E) =
      (w : E) := by
  rfl

lemma planeOrthogonalSubspace_toTangent_inner_y
    {y v : E} (w : planeOrthogonalSubspace y v) :
    inner ℝ y ((planeOrthogonalSubspace.toTangent y v w : tangentSubspace v) : E) = 0 := by
  exact w.2.2

lemma planeOrthogonalSubspace_toTangent_norm
    {y v : E} (w : planeOrthogonalSubspace y v) :
    ‖((planeOrthogonalSubspace.toTangent y v w : tangentSubspace v) : E)‖ =
      ‖(w : E)‖ := by
  rfl

lemma planeOrthogonalSubspace_toTangent_inner
    {y v : E} (w₁ w₂ : planeOrthogonalSubspace y v) :
    inner ℝ ((planeOrthogonalSubspace.toTangent y v w₁ : tangentSubspace v) : E)
      ((planeOrthogonalSubspace.toTangent y v w₂ : tangentSubspace v) : E) =
        inner ℝ (w₁ : E) (w₂ : E) := by
  rfl

/-- The ordered pair whose span is the two-plane generated by the pole `y` and
the direction `v`.  It is ordered as `(v,y)` to match
`planeOrthogonalSubspace y v`, whose defining equations are first
orthogonality to `v` and then orthogonality to `y`. -/
def polarizationPair (y v : E) : Fin 2 → E :=
  ![v, y]

/-- The codimension-two block is exactly the orthogonal complement of the
two-plane spanned by `v` and `y`. -/
lemma planeOrthogonalSubspace_eq_pairSpan_orthogonal (y v : E) :
    planeOrthogonalSubspace y v =
      (Submodule.span ℝ (Set.range (polarizationPair y v)))ᗮ := by
  ext w
  rw [mem_planeOrthogonalSubspace_iff, Submodule.mem_orthogonal]
  constructor
  · intro h u hu
    refine Submodule.span_induction
      (p := fun u _ => inner ℝ u w = 0) ?hbase ?hzero ?hadd ?hsmul hu
    · intro z hz
      rcases hz with ⟨i, rfl⟩
      fin_cases i <;> simp [polarizationPair, h.1, h.2]
    · simp
    · intro a b ha hb hia hib
      rw [inner_add_left, hia, hib, zero_add]
    · intro a z hz hzw
      rw [inner_smul_left, hzw, mul_zero]
  · intro h
    constructor
    · exact h v (Submodule.subset_span ⟨0, by simp [polarizationPair]⟩)
    · exact h y (Submodule.subset_span ⟨1, by simp [polarizationPair]⟩)

/-- Dimension bridge for the codimension-two block: if the ambient space has
dimension `m+2` and the pair `(v,y)` is linearly independent, then the block
orthogonal to both vectors has dimension `m`. -/
theorem planeOrthogonalSubspace_finrank_of_pair_linearIndependent
    [FiniteDimensional ℝ E]
    {y v : E} {m : ℕ}
    (hE : Module.finrank ℝ E = m + 2)
    (hlin : LinearIndependent ℝ (polarizationPair y v)) :
    Module.finrank ℝ (planeOrthogonalSubspace y v) = m := by
  let S : Submodule ℝ E := Submodule.span ℝ (Set.range (polarizationPair y v))
  have hSdim : Module.finrank ℝ S = 2 := by
    simpa [S] using (finrank_span_eq_card hlin)
  have hsum : Module.finrank ℝ S + Module.finrank ℝ Sᗮ = Module.finrank ℝ E :=
    S.finrank_add_finrank_orthogonal
  have horth : Module.finrank ℝ Sᗮ = m := by
    omega
  have heq :
      planeOrthogonalSubspace y v = Sᗮ := by
    simpa [S] using planeOrthogonalSubspace_eq_pairSpan_orthogonal y v
  rw [heq]
  exact horth

/-- On tangent directions orthogonal to `y`, the derivative acts by the scalar
`-2⟪y,v⟫`.  These are the `n-2` directions orthogonal to the
`span{v,y}` plane in the later determinant computation. -/
lemma reflectionFDeriv_apply_of_inner_y_eq_zero
    {y v w : E} (hyw : inner ℝ y w = 0) :
    reflectionFDeriv y v w = -((2 * inner ℝ y v) • w) := by
  rw [reflectionFDeriv_apply]
  simp [hyw]

/-- Norm form of `reflectionFDeriv_apply_of_inner_y_eq_zero`. -/
lemma norm_reflectionFDeriv_apply_of_inner_y_eq_zero
    {y v w : E} (hyw : inner ℝ y w = 0) :
    ‖reflectionFDeriv y v w‖ = |2 * inner ℝ y v| * ‖w‖ := by
  rw [reflectionFDeriv_apply_of_inner_y_eq_zero hyw]
  simp [norm_smul]

/-- On unit directions orthogonal to the `span{v,y}` plane and with
`⟪y,v⟫ > 0`, the derivative has norm `2⟪y,v⟫`. -/
lemma norm_reflectionFDeriv_apply_of_positive_plane_orthogonal_unit
    {y v w : E} (hyw : inner ℝ y w = 0)
    (hpos : 0 < inner ℝ y v) (hw : ‖w‖ = 1) :
    ‖reflectionFDeriv y v w‖ = 2 * inner ℝ y v := by
  rw [norm_reflectionFDeriv_apply_of_inner_y_eq_zero hyw, hw]
  have hpos2 : 0 < 2 * inner ℝ y v := by nlinarith
  rw [mul_one, abs_of_pos hpos2]

/-- The meridian tangent direction in the plane spanned by `y` and `v`:
`y - ⟪y,v⟫ v`. -/
def meridianDirection (y v : E) : E :=
  y - (inner ℝ y v) • v

/-- If `v` is unit and the meridian direction is nonzero, then the ordered pair
`(v,y)` is linearly independent.  Geometrically, the failure of linear
independence would put `y` on the line through `v`, which makes
`y - ⟪y,v⟫v` vanish. -/
lemma polarizationPair_linearIndependent_of_meridian_ne_zero
    {y v : E} (hv : ‖v‖ = 1)
    (hmer : meridianDirection y v ≠ 0) :
    LinearIndependent ℝ (polarizationPair y v) := by
  change LinearIndependent ℝ ![v, y]
  have hv0 : v ≠ 0 := by
    intro hvz
    rw [hvz, norm_zero] at hv
    norm_num at hv
  rw [LinearIndependent.pair_iff' hv0]
  intro a ha
  apply hmer
  unfold meridianDirection
  rw [← ha]
  have hvv : inner ℝ v v = 1 := by
    rw [real_inner_self_eq_norm_sq, hv]
    norm_num
  rw [inner_smul_left, hvv]
  simp

/-- The meridian direction is tangent to the source unit sphere at `v`. -/
lemma inner_v_meridianDirection_eq_zero_of_unit
    {y v : E} (hv : ‖v‖ = 1) :
    inner ℝ v (meridianDirection y v) = 0 := by
  unfold meridianDirection
  simp only [inner_sub_right, inner_smul_right]
  have hvv : inner ℝ v v = 1 := by
    rw [real_inner_self_eq_norm_sq, hv]
    norm_num
  have hcomm : inner ℝ v y = inner ℝ y v := (real_inner_comm v y).symm
  rw [hvv, hcomm]
  ring

/-- The adapted tangent frame built from the normalized meridian direction and
an orthonormal basis of the codimension-two block. -/
def adaptedTangentFrame
    {m : ℕ} (y v : E) (hv : ‖v‖ = 1)
    (b : OrthonormalBasis (Fin m) ℝ (planeOrthogonalSubspace y v)) :
    Fin (m + 1) → tangentSubspace v :=
  Fin.cons ⟨(‖meridianDirection y v‖)⁻¹ • meridianDirection y v, by
      change inner ℝ v ((‖meridianDirection y v‖)⁻¹ • meridianDirection y v) = 0
      rw [inner_smul_right, inner_v_meridianDirection_eq_zero_of_unit hv]
      simp⟩
    fun i => planeOrthogonalSubspace.toTangent y v (b i)

lemma adaptedTangentFrame_zero
    {m : ℕ} {y v : E} (hv : ‖v‖ = 1)
    (b : OrthonormalBasis (Fin m) ℝ (planeOrthogonalSubspace y v)) :
    (adaptedTangentFrame y v hv b 0 : E) =
      (‖meridianDirection y v‖)⁻¹ • meridianDirection y v := by
  rfl

lemma adaptedTangentFrame_succ
    {m : ℕ} {y v : E} (hv : ‖v‖ = 1)
    (b : OrthonormalBasis (Fin m) ℝ (planeOrthogonalSubspace y v))
    (i : Fin m) :
    (adaptedTangentFrame y v hv b i.succ : E) = (b i : E) := by
  rfl

lemma adaptedTangentFrame_succ_inner_y
    {m : ℕ} {y v : E} (hv : ‖v‖ = 1)
    (b : OrthonormalBasis (Fin m) ℝ (planeOrthogonalSubspace y v))
    (i : Fin m) :
    inner ℝ y (adaptedTangentFrame y v hv b i.succ : E) = 0 := by
  exact (b i).2.2

lemma adaptedTangentFrame_succ_norm
    {m : ℕ} {y v : E} (hv : ‖v‖ = 1)
    (b : OrthonormalBasis (Fin m) ℝ (planeOrthogonalSubspace y v))
    (i : Fin m) :
    ‖(adaptedTangentFrame y v hv b i.succ : E)‖ = 1 := by
  change ‖(b i : E)‖ = 1
  exact b.orthonormal.1 i

lemma adaptedTangentFrame_succ_pairwise
    {m : ℕ} {y v : E} (hv : ‖v‖ = 1)
    (b : OrthonormalBasis (Fin m) ℝ (planeOrthogonalSubspace y v)) :
    Pairwise fun i j : Fin m =>
      inner ℝ (adaptedTangentFrame y v hv b i.succ : E)
        (adaptedTangentFrame y v hv b j.succ : E) = 0 := by
  intro i j hij
  change inner ℝ (b i : E) (b j : E) = 0
  exact b.orthonormal.2 hij

/-- Inner product of `y` with the meridian direction. -/
lemma inner_y_meridianDirection_of_unit
    {y v : E} (hy : ‖y‖ = 1) :
    inner ℝ y (meridianDirection y v) = 1 - (inner ℝ y v)^2 := by
  unfold meridianDirection
  simp only [inner_sub_right, inner_smul_right]
  have hyy : inner ℝ y y = 1 := by
    rw [real_inner_self_eq_norm_sq, hy]
    norm_num
  rw [hyy]
  ring

/-- Squared norm of the meridian direction. -/
lemma norm_sq_meridianDirection_of_units
    {y v : E} (hy : ‖y‖ = 1) (hv : ‖v‖ = 1) :
    ‖meridianDirection y v‖ ^ 2 = 1 - (inner ℝ y v)^2 := by
  rw [← real_inner_self_eq_norm_sq]
  unfold meridianDirection
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
  have hyy : inner ℝ y y = 1 := by
    rw [real_inner_self_eq_norm_sq, hy]
    norm_num
  have hvv : inner ℝ v v = 1 := by
    rw [real_inner_self_eq_norm_sq, hv]
    norm_num
  have hcomm : inner ℝ v y = inner ℝ y v := (real_inner_comm v y).symm
  rw [hyy, hvv, hcomm]
  ring

/-- Squared norm of the derivative on the meridian direction. -/
lemma norm_sq_reflectionFDeriv_meridianDirection_of_units
    {y v : E} (hy : ‖y‖ = 1) (hv : ‖v‖ = 1) :
    ‖reflectionFDeriv y v (meridianDirection y v)‖ ^ 2 =
      4 * (1 - (inner ℝ y v)^2) := by
  rw [← real_inner_self_eq_norm_sq]
  rw [reflectionFDeriv_apply]
  unfold meridianDirection
  simp only [inner_neg_left, inner_neg_right, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
  have hyy : inner ℝ y y = 1 := by
    rw [real_inner_self_eq_norm_sq, hy]
    norm_num
  have hvv : inner ℝ v v = 1 := by
    rw [real_inner_self_eq_norm_sq, hv]
    norm_num
  have hcomm : inner ℝ v y = inner ℝ y v := (real_inner_comm v y).symm
  rw [hyy, hvv, hcomm]
  simp
  ring

/-- The derivative stretches the meridian direction by the factor `2` in norm. -/
lemma norm_reflectionFDeriv_meridianDirection_of_units
    {y v : E} (hy : ‖y‖ = 1) (hv : ‖v‖ = 1) :
    ‖reflectionFDeriv y v (meridianDirection y v)‖ =
      2 * ‖meridianDirection y v‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _)
    (mul_nonneg (by norm_num) (norm_nonneg _))]
  rw [norm_sq_reflectionFDeriv_meridianDirection_of_units hy hv]
  have hsq : (2 * ‖meridianDirection y v‖) ^ 2 =
      4 * ‖meridianDirection y v‖ ^ 2 := by ring
  rw [hsq, norm_sq_meridianDirection_of_units hy hv]

/-- The normalized meridian direction has singular value `2`. -/
lemma norm_reflectionFDeriv_unit_meridianDirection_of_units
    {y v : E} (hy : ‖y‖ = 1) (hv : ‖v‖ = 1)
    (hmer : meridianDirection y v ≠ 0) :
    ‖reflectionFDeriv y v
        ((‖meridianDirection y v‖)⁻¹ • meridianDirection y v)‖ = 2 := by
  rw [map_smul, norm_smul, norm_reflectionFDeriv_meridianDirection_of_units hy hv]
  have hnorm_pos : 0 < ‖meridianDirection y v‖ := norm_pos_iff.mpr hmer
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  field_simp [ne_of_gt hnorm_pos]

/-- On the plane-orthogonal block, the derivative scales the Gram form by
`(2⟪y,v⟫)^2`.  This is the determinant-ready form of the `n-2` singular
directions. -/
lemma inner_reflectionFDeriv_apply_of_inner_y_eq_zero
    {y v w₁ w₂ : E}
    (hy₁ : inner ℝ y w₁ = 0) (hy₂ : inner ℝ y w₂ = 0) :
    inner ℝ (reflectionFDeriv y v w₁) (reflectionFDeriv y v w₂) =
      (2 * inner ℝ y v) ^ 2 * inner ℝ w₁ w₂ := by
  rw [reflectionFDeriv_apply_of_inner_y_eq_zero hy₁,
    reflectionFDeriv_apply_of_inner_y_eq_zero hy₂]
  simp only [inner_neg_left, inner_neg_right, inner_smul_left, inner_smul_right]
  simp
  ring

/-- The meridian image is orthogonal to every image of a vector orthogonal to
both `y` and `v`.  Together with the previous Gram-scaling lemma, this gives
the adapted block diagonal structure used in the tangent Jacobian. -/
lemma inner_reflectionFDeriv_meridian_plane_orthogonal_eq_zero
    {y v w : E} (hy : ‖y‖ = 1)
    (hyw : inner ℝ y w = 0) (hvw : inner ℝ v w = 0) :
    inner ℝ (reflectionFDeriv y v (meridianDirection y v))
      (reflectionFDeriv y v w) = 0 := by
  rw [reflectionFDeriv_apply]
  rw [reflectionFDeriv_apply_of_inner_y_eq_zero hyw]
  rw [inner_y_meridianDirection_of_unit hy]
  unfold meridianDirection
  simp only [inner_neg_left, inner_neg_right, inner_add_left, inner_smul_left,
    inner_smul_right, inner_sub_left]
  simp [hyw, hvw]

/-- Orthogonality inside the plane-orthogonal block is preserved by the
derivative. -/
lemma inner_reflectionFDeriv_plane_orthogonal_eq_zero
    {y v w₁ w₂ : E}
    (hy₁ : inner ℝ y w₁ = 0) (hy₂ : inner ℝ y w₂ = 0)
    (hw : inner ℝ w₁ w₂ = 0) :
    inner ℝ (reflectionFDeriv y v w₁) (reflectionFDeriv y v w₂) = 0 := by
  rw [inner_reflectionFDeriv_apply_of_inner_y_eq_zero hy₁ hy₂, hw]
  ring

/-- Volume-form version of the tangent determinant calculation: if the
reflected images of a tangent frame are pairwise orthogonal, then the absolute
target volume form is the product of their ambient norms. -/
theorem abs_volumeForm_reflectionTangentDeriv_of_pairwise_image_orthogonal
    {y v : E} (n : ℕ)
    [Fact (Module.finrank ℝ (tangentSubspace (reflection v y)) = n)]
    (o : Orientation ℝ (tangentSubspace (reflection v y)) (Fin n))
    (hv : ‖v‖ = 1)
    (frame : Fin n → tangentSubspace v)
    (hpair : Pairwise fun i j =>
      inner ℝ (reflectionFDeriv y v (frame i : E))
        (reflectionFDeriv y v (frame j : E)) = 0) :
    |o.volumeForm (fun i => reflectionTangentDeriv y v hv (frame i))| =
      ∏ i : Fin n, ‖reflectionFDeriv y v (frame i : E)‖ := by
  rw [o.abs_volumeForm_apply_of_pairwise_orthogonal]
  · simp [coe_reflectionTangentDeriv]
  · intro i j hij
    simpa [coe_reflectionTangentDeriv] using hpair hij

/-- Determinant-ready adapted-frame package.  If the meridian image has
singular value `2`, the remaining `m` frame directions have singular value
`2⟪y,v⟫`, and the reflected frame is orthogonal, then the absolute tangent
volume scaling is `2 * (2⟪y,v⟫)^m`.

For the sphere `S^{n-1}`, this is the algebraic core of the Jacobian
`2 * (2⟪y,v⟫)^(n-2)`. -/
theorem abs_volumeForm_reflectionTangentDeriv_of_adapted_norms
    {y v : E} (m : ℕ)
    [Fact (Module.finrank ℝ (tangentSubspace (reflection v y)) = m + 1)]
    (o : Orientation ℝ (tangentSubspace (reflection v y)) (Fin (m + 1)))
    (hv : ‖v‖ = 1)
    (frame : Fin (m + 1) → tangentSubspace v)
    (hpair : Pairwise fun i j =>
      inner ℝ (reflectionFDeriv y v (frame i : E))
        (reflectionFDeriv y v (frame j : E)) = 0)
    (hzero : ‖reflectionFDeriv y v (frame 0 : E)‖ = 2)
    (hrest : ∀ i : Fin m,
      ‖reflectionFDeriv y v (frame i.succ : E)‖ = 2 * inner ℝ y v) :
    |o.volumeForm (fun i => reflectionTangentDeriv y v hv (frame i))| =
      2 * (2 * inner ℝ y v) ^ m := by
  rw [abs_volumeForm_reflectionTangentDeriv_of_pairwise_image_orthogonal
    (n := m + 1) o hv frame hpair]
  rw [Fin.prod_univ_succ]
  rw [hzero]
  simp [hrest]

/-- Adapted-frame version of the tangent Jacobian package.

The first frame vector is the normalized meridian direction
`(‖y - ⟪y,v⟫v‖)⁻¹ • (y - ⟪y,v⟫v)`.  The remaining vectors are unit, mutually
orthogonal, and orthogonal to both `y` and `v`.  Under these concrete
geometric hypotheses, the restricted derivative has absolute tangent volume
scaling `2 * (2⟪y,v⟫)^m`.

This is the last determinant step before replacing the explicit adapted-frame
hypotheses by an actual orthonormal-basis construction for the
codimension-two plane. -/
theorem abs_volumeForm_reflectionTangentDeriv_of_normalized_meridian_frame
    {y v : E} (m : ℕ)
    [Fact (Module.finrank ℝ (tangentSubspace (reflection v y)) = m + 1)]
    (o : Orientation ℝ (tangentSubspace (reflection v y)) (Fin (m + 1)))
    (hy : ‖y‖ = 1) (hv : ‖v‖ = 1)
    (hpos : 0 < inner ℝ y v)
    (hmer : meridianDirection y v ≠ 0)
    (frame : Fin (m + 1) → tangentSubspace v)
    (hzero_vec : (frame 0 : E) =
      (‖meridianDirection y v‖)⁻¹ • meridianDirection y v)
    (hsucc_y : ∀ i : Fin m, inner ℝ y (frame i.succ : E) = 0)
    (hsucc_norm : ∀ i : Fin m, ‖(frame i.succ : E)‖ = 1)
    (hsucc_orth : Pairwise fun i j : Fin m =>
      inner ℝ (frame i.succ : E) (frame j.succ : E) = 0) :
    |o.volumeForm (fun i => reflectionTangentDeriv y v hv (frame i))| =
      2 * (2 * inner ℝ y v) ^ m := by
  refine abs_volumeForm_reflectionTangentDeriv_of_adapted_norms
    (m := m) o hv frame ?hpair ?hzero ?hrest
  · intro i j hij
    by_cases hi0 : i = 0
    · subst i
      have hj0 : j ≠ 0 := by
        intro hj0
        exact hij hj0.symm
      rcases Fin.exists_succ_eq_of_ne_zero hj0 with ⟨j', rfl⟩
      rw [hzero_vec]
      have hbase : inner ℝ (reflectionFDeriv y v (meridianDirection y v))
          (reflectionFDeriv y v (frame j'.succ : E)) = 0 :=
        inner_reflectionFDeriv_meridian_plane_orthogonal_eq_zero
          hy (hsucc_y j') (frame j'.succ).2
      calc
        inner ℝ (reflectionFDeriv y v
            ((‖meridianDirection y v‖)⁻¹ • meridianDirection y v))
            (reflectionFDeriv y v (frame j'.succ : E))
            =
          (‖meridianDirection y v‖)⁻¹ *
            inner ℝ (reflectionFDeriv y v (meridianDirection y v))
              (reflectionFDeriv y v (frame j'.succ : E)) := by
              rw [map_smul, inner_smul_left]
              simp
        _ = 0 := by rw [hbase]; ring
    · rcases Fin.exists_succ_eq_of_ne_zero hi0 with ⟨i', rfl⟩
      by_cases hj0 : j = 0
      · subst j
        rw [hzero_vec]
        have hbase : inner ℝ (reflectionFDeriv y v (meridianDirection y v))
            (reflectionFDeriv y v (frame i'.succ : E)) = 0 :=
          inner_reflectionFDeriv_meridian_plane_orthogonal_eq_zero
            hy (hsucc_y i') (frame i'.succ).2
        calc
          inner ℝ (reflectionFDeriv y v (frame i'.succ : E))
              (reflectionFDeriv y v
                ((‖meridianDirection y v‖)⁻¹ • meridianDirection y v))
              =
            (‖meridianDirection y v‖)⁻¹ *
              inner ℝ (reflectionFDeriv y v (frame i'.succ : E))
                (reflectionFDeriv y v (meridianDirection y v)) := by
                rw [map_smul, inner_smul_right]
          _ = 0 := by
            rw [real_inner_comm, hbase]
            ring
      · rcases Fin.exists_succ_eq_of_ne_zero hj0 with ⟨j', rfl⟩
        exact inner_reflectionFDeriv_plane_orthogonal_eq_zero
          (hsucc_y i') (hsucc_y j') (hsucc_orth (by
            intro hij'
            exact hij (by simp [hij'])))
  · rw [hzero_vec]
    exact norm_reflectionFDeriv_unit_meridianDirection_of_units hy hv hmer
  · intro i
    exact norm_reflectionFDeriv_apply_of_positive_plane_orthogonal_unit
      (hsucc_y i) hpos (hsucc_norm i)

/-- Tangent Jacobian package from an orthonormal basis of the codimension-two
block.  This removes the explicit adapted-frame side conditions from
`abs_volumeForm_reflectionTangentDeriv_of_normalized_meridian_frame`: the frame
is now built canonically from the normalized meridian direction and the supplied
orthonormal basis of `planeOrthogonalSubspace y v`. -/
theorem abs_volumeForm_reflectionTangentDeriv_of_plane_orthonormalBasis
    {y v : E} (m : ℕ)
    [Fact (Module.finrank ℝ (tangentSubspace (reflection v y)) = m + 1)]
    (o : Orientation ℝ (tangentSubspace (reflection v y)) (Fin (m + 1)))
    (hy : ‖y‖ = 1) (hv : ‖v‖ = 1)
    (hpos : 0 < inner ℝ y v)
    (hmer : meridianDirection y v ≠ 0)
    (b : OrthonormalBasis (Fin m) ℝ (planeOrthogonalSubspace y v)) :
    |o.volumeForm (fun i =>
      reflectionTangentDeriv y v hv (adaptedTangentFrame y v hv b i))| =
      2 * (2 * inner ℝ y v) ^ m := by
  exact abs_volumeForm_reflectionTangentDeriv_of_normalized_meridian_frame
    (m := m) o hy hv hpos hmer (adaptedTangentFrame y v hv b)
    (adaptedTangentFrame_zero hv b)
    (adaptedTangentFrame_succ_inner_y hv b)
    (adaptedTangentFrame_succ_norm hv b)
    (adaptedTangentFrame_succ_pairwise hv b)

/-- Choose an orthonormal basis of the codimension-two block once its
finite dimension has been identified.

This is only a bookkeeping bridge: the real geometric content is the dimension
identity for `planeOrthogonalSubspace y v`; after that identity is available,
mathlib's finite-dimensional Gram-Schmidt construction supplies the basis. -/
noncomputable def planeOrthogonalSubspace.orthonormalBasisOfFinrank
    [FiniteDimensional ℝ E]
    {y v : E} (m : ℕ)
    (hfin : Module.finrank ℝ (planeOrthogonalSubspace y v) = m) :
    OrthonormalBasis (Fin m) ℝ (planeOrthogonalSubspace y v) :=
  (stdOrthonormalBasis ℝ (planeOrthogonalSubspace y v)).reindex (finCongr hfin)

/-- Tangent Jacobian package with the codimension-two basis chosen from its
dimension identity.  This leaves the next genuine bridge as the proof that the
block `planeOrthogonalSubspace y v` has dimension `m`. -/
theorem abs_volumeForm_reflectionTangentDeriv_of_plane_finrank
    [FiniteDimensional ℝ E]
    {y v : E} (m : ℕ)
    [Fact (Module.finrank ℝ (tangentSubspace (reflection v y)) = m + 1)]
    (o : Orientation ℝ (tangentSubspace (reflection v y)) (Fin (m + 1)))
    (hy : ‖y‖ = 1) (hv : ‖v‖ = 1)
    (hpos : 0 < inner ℝ y v)
    (hmer : meridianDirection y v ≠ 0)
    (hfin : Module.finrank ℝ (planeOrthogonalSubspace y v) = m) :
    |o.volumeForm (fun i =>
      reflectionTangentDeriv y v hv
        (adaptedTangentFrame y v hv
          (planeOrthogonalSubspace.orthonormalBasisOfFinrank
            (y := y) (v := v) m hfin) i))| =
      2 * (2 * inner ℝ y v) ^ m := by
  exact abs_volumeForm_reflectionTangentDeriv_of_plane_orthonormalBasis
    (m := m) o hy hv hpos hmer
    (planeOrthogonalSubspace.orthonormalBasisOfFinrank
      (y := y) (v := v) m hfin)

/-- Clean codimension-two tangent Jacobian endpoint from the ambient dimension
and linear independence of `(v,y)`.  The orthonormal basis and block finrank
are now chosen/proved internally. -/
theorem abs_volumeForm_reflectionTangentDeriv_of_pair_linearIndependent
    [FiniteDimensional ℝ E]
    {y v : E} (m : ℕ)
    [Fact (Module.finrank ℝ (tangentSubspace (reflection v y)) = m + 1)]
    (o : Orientation ℝ (tangentSubspace (reflection v y)) (Fin (m + 1)))
    (hy : ‖y‖ = 1) (hv : ‖v‖ = 1)
    (hpos : 0 < inner ℝ y v)
    (hmer : meridianDirection y v ≠ 0)
    (hE : Module.finrank ℝ E = m + 2)
    (hlin : LinearIndependent ℝ (polarizationPair y v)) :
    |o.volumeForm (fun i =>
      reflectionTangentDeriv y v hv
        (adaptedTangentFrame y v hv
          (planeOrthogonalSubspace.orthonormalBasisOfFinrank
            (y := y) (v := v) m
            (planeOrthogonalSubspace_finrank_of_pair_linearIndependent
              (y := y) (v := v) (m := m) hE hlin)) i))| =
      2 * (2 * inner ℝ y v) ^ m := by
  exact abs_volumeForm_reflectionTangentDeriv_of_plane_finrank
    (m := m) o hy hv hpos hmer
    (planeOrthogonalSubspace_finrank_of_pair_linearIndependent
      (y := y) (v := v) (m := m) hE hlin)

/-- Clean codimension-two tangent Jacobian endpoint from ambient dimension and
the meridian non-degeneracy.  This folds the linear-independence proof of
`(v,y)` into the determinant package. -/
theorem abs_volumeForm_reflectionTangentDeriv_of_ambient_finrank
    [FiniteDimensional ℝ E]
    {y v : E} (m : ℕ)
    [Fact (Module.finrank ℝ (tangentSubspace (reflection v y)) = m + 1)]
    (o : Orientation ℝ (tangentSubspace (reflection v y)) (Fin (m + 1)))
    (hy : ‖y‖ = 1) (hv : ‖v‖ = 1)
    (hpos : 0 < inner ℝ y v)
    (hmer : meridianDirection y v ≠ 0)
    (hE : Module.finrank ℝ E = m + 2) :
    |o.volumeForm (fun i =>
      reflectionTangentDeriv y v hv
        (adaptedTangentFrame y v hv
          (planeOrthogonalSubspace.orthonormalBasisOfFinrank
            (y := y) (v := v) m
            (planeOrthogonalSubspace_finrank_of_pair_linearIndependent
              (y := y) (v := v) (m := m) hE
              (polarizationPair_linearIndependent_of_meridian_ne_zero hv hmer))) i))| =
      2 * (2 * inner ℝ y v) ^ m := by
  exact abs_volumeForm_reflectionTangentDeriv_of_pair_linearIndependent
    (m := m) o hy hv hpos hmer hE
    (polarizationPair_linearIndependent_of_meridian_ne_zero hv hmer)

end InnerProductGeometry

/-! ## Explicit kernel -/

section Kernel

variable {S : Type*}

/-- Real-valued kernel. Off the diagonal this is

`2^{-(n-2)} * sin(d_geo(x,y)/2)^{-(n-2)}`.

It is set to `0` on the diagonal, matching the manuscript convention. -/
def sphericalKernel (n : ℕ) (dgeo : S → S → ℝ) (x y : S) : ℝ :=
  if x = y then 0
  else
    (((2 : ℝ) ^ (n - 2))⁻¹) *
      (((Real.sin (dgeo x y / 2)) ^ (n - 2))⁻¹)

/-- `ENNReal` version of the kernel, convenient for positive-function
integrals. -/
def sphericalKernelENNReal (n : ℕ) (dgeo : S → S → ℝ) (x y : S) : ℝ≥0∞ :=
  ENNReal.ofReal (sphericalKernel n dgeo x y)

lemma sphericalKernel_of_ne
    (n : ℕ) {dgeo : S → S → ℝ} {x y : S}
    (hxy : x ≠ y) :
    sphericalKernel n dgeo x y =
      (((2 : ℝ) ^ (n - 2))⁻¹) *
        (((Real.sin (dgeo x y / 2)) ^ (n - 2))⁻¹) := by
  simp [sphericalKernel, hxy]

section ChordalKernel

variable {E : Type*} [NormedAddCommGroup E]

/-- Chordal half-distance on the ambient Euclidean/Frobenius space.

For unit vectors this is exactly `sin(d_geo(x,y)/2)`, so it is the correct
coordinate for the explicit kernel without confusing the subtype metric with
the intrinsic geodesic distance. -/
def chordalHalf (x y : E) : ℝ :=
  ‖x - y‖ / 2

/-- The explicit chordal form of the spherical kernel.

Off the diagonal this is

`2^{-(n-2)} * (‖x-y‖/2)^{-(n-2)}`.

It is set to `0` on the diagonal, matching the totalized kernel convention used
for `withDensity` statements. -/
def sphericalKernelChordal (n : ℕ) (x y : E) : ℝ :=
  if x = y then 0
  else
    (((2 : ℝ) ^ (n - 2))⁻¹) *
      (((chordalHalf x y) ^ (n - 2))⁻¹)

/-- `ENNReal` version of the explicit chordal kernel, the shape used in
positive-integral and `withDensity` formulations. -/
def sphericalKernelChordalENNReal (n : ℕ) (x y : E) : ℝ≥0∞ :=
  ENNReal.ofReal (sphericalKernelChordal n x y)

lemma sphericalKernelChordal_of_ne
    (n : ℕ) {x y : E}
    (hxy : x ≠ y) :
    sphericalKernelChordal n x y =
      (((2 : ℝ) ^ (n - 2))⁻¹) *
        (((chordalHalf x y) ^ (n - 2))⁻¹) := by
  simp [sphericalKernelChordal, hxy]

/-- The chordal kernel is the same as the half-angle/geodesic kernel once the
intrinsic spherical distance is written as `arccos ⟪x,y⟫` on unit vectors. -/
theorem sphericalKernelChordal_eq_sphericalKernel_arccos_inner_of_unit
    [InnerProductSpace ℝ E]
    (n : ℕ) {x y : E}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : x ≠ y) :
    sphericalKernelChordal n x y =
      sphericalKernel n
        (fun x y : E => Real.arccos (inner ℝ x y)) x y := by
  rw [sphericalKernelChordal_of_ne n hxy,
    sphericalKernel_of_ne n hxy]
  rw [sin_arccos_half_eq_half_norm_sub_of_unit
    (x := x) (y := y) hx hy]
  rfl

end ChordalKernel

section ReflectionKernelFactor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `m`-indexed form of the normalized inverse tangent-Jacobian scalar.

The spherical dimension convention is `n = m + 2`, so the exponent `n - 2`
from the paper becomes the codimension-two block dimension `m`. -/
lemma normalized_inverse_tangent_jacobian_factor_m
    (m : ℕ) {a : ℝ} (ha : a ≠ 0) :
    2 * (2 * (2 * a) ^ m)⁻¹ =
      ((2 : ℝ) ^ m)⁻¹ * (a ^ m)⁻¹ := by
  simpa using normalized_inverse_tangent_jacobian_factor (m + 2) (a := a) ha

/-- A positive reflection direction does not fix the reflected unit point. -/
lemma reflection_ne_self_of_unit_pos
    {y v : E} (hy : ‖y‖ = 1) (hv : ‖v‖ = 1)
    (hpos : 0 < inner ℝ y v) :
    reflection v y ≠ y := by
  exact (reflection_mapsTo_positive_halfSphere_punctured_unitSphere hy ⟨hv, hpos⟩).2

/-- The determinant computation, after half-sphere normalization, is exactly
the inverse kernel scalar in half-angle form. -/
theorem normalized_inverse_abs_volumeForm_reflectionTangentDeriv_eq_kernel_factor
    [FiniteDimensional ℝ E]
    {y v : E} (m : ℕ)
    [Fact (Module.finrank ℝ (tangentSubspace (reflection v y)) = m + 1)]
    (o : Orientation ℝ (tangentSubspace (reflection v y)) (Fin (m + 1)))
    (hy : ‖y‖ = 1) (hv : ‖v‖ = 1)
    (hpos : 0 < inner ℝ y v)
    (hmer : meridianDirection y v ≠ 0)
    (hE : Module.finrank ℝ E = m + 2) :
    2 * (|o.volumeForm (fun i =>
      reflectionTangentDeriv y v hv
        (adaptedTangentFrame y v hv
          (planeOrthogonalSubspace.orthonormalBasisOfFinrank
            (y := y) (v := v) m
            (planeOrthogonalSubspace_finrank_of_pair_linearIndependent
              (y := y) (v := v) (m := m) hE
              (polarizationPair_linearIndependent_of_meridian_ne_zero hv hmer))) i))|)⁻¹ =
      ((2 : ℝ) ^ m)⁻¹ *
        ((Real.sin (Real.arccos (inner ℝ (reflection v y) y) / 2)) ^ m)⁻¹ := by
  rw [abs_volumeForm_reflectionTangentDeriv_of_ambient_finrank
    (m := m) o hy hv hpos hmer hE]
  rw [sin_arccos_half_reflection_eq_inner_of_unit_pos hy hv hpos]
  exact normalized_inverse_tangent_jacobian_factor_m m (ne_of_gt hpos)

/-- The determinant computation, after half-sphere normalization, is exactly
the real spherical kernel evaluated at `(rho_v y, y)` for the chordal/geodesic
distance `arccos inner`. -/
theorem normalized_inverse_abs_volumeForm_reflectionTangentDeriv_eq_sphericalKernel
    [FiniteDimensional ℝ E]
    {y v : E} (m : ℕ)
    [Fact (Module.finrank ℝ (tangentSubspace (reflection v y)) = m + 1)]
    (o : Orientation ℝ (tangentSubspace (reflection v y)) (Fin (m + 1)))
    (hy : ‖y‖ = 1) (hv : ‖v‖ = 1)
    (hpos : 0 < inner ℝ y v)
    (hmer : meridianDirection y v ≠ 0)
    (hE : Module.finrank ℝ E = m + 2) :
    2 * (|o.volumeForm (fun i =>
      reflectionTangentDeriv y v hv
        (adaptedTangentFrame y v hv
          (planeOrthogonalSubspace.orthonormalBasisOfFinrank
            (y := y) (v := v) m
            (planeOrthogonalSubspace_finrank_of_pair_linearIndependent
              (y := y) (v := v) (m := m) hE
              (polarizationPair_linearIndependent_of_meridian_ne_zero hv hmer))) i))|)⁻¹ =
      sphericalKernel (m + 2)
        (fun x y : E => Real.arccos (inner ℝ x y))
        (reflection v y) y := by
  rw [sphericalKernel_of_ne (m + 2)
    (hxy := reflection_ne_self_of_unit_pos hy hv hpos)]
  simpa using
    normalized_inverse_abs_volumeForm_reflectionTangentDeriv_eq_kernel_factor
      (m := m) o hy hv hpos hmer hE

/-- Chordal version of the determinant computation.

This is the explicit `K_n` form used by the push-forward theorem: after the
normalization of the admissible half-sphere, the inverse tangent Jacobian is

`2^{-(n-2)} * (‖rho_v(y)-y‖/2)^{-(n-2)}`. -/
theorem normalized_inverse_abs_volumeForm_reflectionTangentDeriv_eq_sphericalKernelChordal
    [FiniteDimensional ℝ E]
    {y v : E} (m : ℕ)
    [Fact (Module.finrank ℝ (tangentSubspace (reflection v y)) = m + 1)]
    (o : Orientation ℝ (tangentSubspace (reflection v y)) (Fin (m + 1)))
    (hy : ‖y‖ = 1) (hv : ‖v‖ = 1)
    (hpos : 0 < inner ℝ y v)
    (hmer : meridianDirection y v ≠ 0)
    (hE : Module.finrank ℝ E = m + 2) :
    2 * (|o.volumeForm (fun i =>
      reflectionTangentDeriv y v hv
        (adaptedTangentFrame y v hv
          (planeOrthogonalSubspace.orthonormalBasisOfFinrank
            (y := y) (v := v) m
            (planeOrthogonalSubspace_finrank_of_pair_linearIndependent
              (y := y) (v := v) (m := m) hE
              (polarizationPair_linearIndependent_of_meridian_ne_zero hv hmer))) i))|)⁻¹ =
      sphericalKernelChordal (m + 2) (reflection v y) y := by
  rw [sphericalKernelChordal_eq_sphericalKernel_arccos_inner_of_unit
    (n := m + 2)
    (x := reflection v y) (y := y)
    (hx := by rw [reflection_norm_eq_of_unit hv, hy])
    (hy := hy)
    (hxy := reflection_ne_self_of_unit_pos hy hv hpos)]
  exact normalized_inverse_abs_volumeForm_reflectionTangentDeriv_eq_sphericalKernel
    (m := m) o hy hv hpos hmer hE

lemma inner_meridianDirection_planeOrthogonal_eq_zero
    {y v w : E} (hw : w ∈ planeOrthogonalSubspace y v) :
    inner ℝ (meridianDirection y v) w = 0 := by
  rcases hw with ⟨hvw, hyw⟩
  unfold meridianDirection
  simp [inner_sub_left, inner_smul_left, hyw, hvw]

lemma inner_meridianDirection_planeOrthogonalSubtype_eq_zero
    {y v : E} (w : planeOrthogonalSubspace y v) :
    inner ℝ (meridianDirection y v) (w : E) = 0 :=
  inner_meridianDirection_planeOrthogonal_eq_zero (SetLike.mem_coe.mp w.2)

lemma finCons_unit_orthonormal
    {m : ℕ} {v : E} (hv : ‖v‖ = 1)
    {tang : Fin (m + 1) → E} (htang : Orthonormal ℝ tang)
    (horth : ∀ i, inner ℝ v (tang i) = 0) :
    Orthonormal ℝ (Fin.cons v tang) := by
  constructor
  · intro i
    cases i using Fin.cases with
    | zero => simp [Fin.cons_zero, hv]
    | succ i => simp [Fin.cons_succ]; exact htang.1 i
  · intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j => simp [Fin.cons_zero, Fin.cons_succ, hv, horth, htang]
    | succ i =>
      cases j using Fin.cases with
      | zero => simp [Fin.cons_zero, Fin.cons_succ, hv, horth, htang, real_inner_comm]
      | succ j => simp [Fin.cons_succ, real_inner_comm, htang.2 (ne_of_apply_ne Fin.succ hij)]

lemma adaptedTangentFrame_zero_norm
    {m : ℕ} {y v : E} (hv : ‖v‖ = 1)
    (b : OrthonormalBasis (Fin m) ℝ (planeOrthogonalSubspace y v))
    (hmer : meridianDirection y v ≠ 0) :
    ‖(adaptedTangentFrame y v hv b 0 : E)‖ = 1 := by
  rw [adaptedTangentFrame_zero, norm_smul, norm_inv]
  have hpos : 0 < ‖meridianDirection y v‖ := norm_pos_iff.mpr hmer
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  field_simp [hpos.ne']

lemma inner_reflectionFDeriv_smul_meridian_plane_orthogonal_eq_zero
    {y v w : E} (hy : ‖y‖ = 1) (hmer : meridianDirection y v ≠ 0)
    (hyw : inner ℝ y w = 0) (hvw : inner ℝ v w = 0) :
    inner ℝ (reflectionFDeriv y v ((‖meridianDirection y v‖)⁻¹ • meridianDirection y v))
      (reflectionFDeriv y v w) = 0 := by
  rw [ContinuousLinearMap.map_smul, inner_smul_left,
    inner_reflectionFDeriv_meridian_plane_orthogonal_eq_zero hy hyw hvw]
  simp [norm_pos_iff.mpr hmer]

lemma ambientRadialFrame_zero
    {m : ℕ} {v : E} {tangVec : Fin (m + 1) → E} :
    (fun i : Fin (m + 2) =>
        if h0 : i = 0 then v else tangVec (i.pred h0)) 0 = v := by
  simp

lemma ambientRadialFrame_succ
    {m : ℕ} {v : E} {tangVec : Fin (m + 1) → E} (i : Fin (m + 1)) :
    (fun j : Fin (m + 2) =>
        if h0 : j = 0 then v else tangVec (j.pred h0)) (Fin.succ i) =
      tangVec i := by
  simp [Fin.pred_succ]

lemma adaptedTangentFrame_orthonormal
    {m : ℕ} {y v : E} (hv : ‖v‖ = 1)
    (b : OrthonormalBasis (Fin m) ℝ (planeOrthogonalSubspace y v))
    (hmer : meridianDirection y v ≠ 0) :
    Orthonormal ℝ fun i => (adaptedTangentFrame y v hv b i : E) := by
  constructor
  · intro i
    cases i using Fin.cases with
    | zero => exact adaptedTangentFrame_zero_norm hv b hmer
    | succ i => exact adaptedTangentFrame_succ_norm hv b i
  · intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j =>
        simp [adaptedTangentFrame_zero, adaptedTangentFrame_succ, inner_smul_left,
          inner_meridianDirection_planeOrthogonalSubtype_eq_zero (b j)]
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        simp [adaptedTangentFrame_zero, adaptedTangentFrame_succ, inner_smul_right,
          real_inner_comm, inner_meridianDirection_planeOrthogonalSubtype_eq_zero (b i)]
      | succ j =>
        simp [adaptedTangentFrame_succ]
        exact b.orthonormal.inner_eq_zero (ne_of_apply_ne Fin.succ hij)

/-- If a linear map agrees with the reflection extension on a radial unit direction and
on the adapted tangent frame, its absolute determinant equals the tangent Jacobian
volume `2 * (2⟪y,v⟫)^m`. -/
theorem abs_det_reflectionExtension_eq_tangentJacobianVolume
    [FiniteDimensional ℝ E]
    {y v : E} (m : ℕ)
    (hy : ‖y‖ = 1) (hv : ‖v‖ = 1)
    (hpos : 0 < inner ℝ y v)
    (hmer : meridianDirection y v ≠ 0)
    (hE : Module.finrank ℝ E = m + 2)
    (L : E →L[ℝ] E)
    (h_radial : L v = reflection v y)
    (h_tang :
      ∀ w : E, inner ℝ v w = 0 →
        L w = reflectionFDeriv y v w) :
    |L.det| = 2 * (2 * inner ℝ y v) ^ m := by
  classical
  haveI : Fact (Module.finrank ℝ E = m + 2) := ⟨hE⟩
  let b_plane :=
    planeOrthogonalSubspace.orthonormalBasisOfFinrank
      (y := y) (v := v) m
      (planeOrthogonalSubspace_finrank_of_pair_linearIndependent
        (y := y) (v := v) (m := m) hE
        (polarizationPair_linearIndependent_of_meridian_ne_zero hv hmer))
  let tang := adaptedTangentFrame y v hv b_plane
  let tangVec : Fin (m + 1) → E := fun i => (tang i : E)
  let frame : Fin (m + 2) → E := fun i =>
    if h0 : i = 0 then v
    else tangVec (i.pred h0)
  have horth_tang := adaptedTangentFrame_orthonormal hv b_plane hmer
  have horth_v :
      ∀ i, inner ℝ v (tangVec i) = 0 := by
    intro i
    exact (mem_tangentSubspace_iff).1 (tang i).2
  have horth : Orthonormal ℝ frame := by
    have heq : frame = Fin.cons v tangVec := by
      ext i
      cases i using Fin.cases with
      | zero => simp [frame, Fin.cons_zero]
      | succ j => simp [frame, Fin.cons_succ, Fin.pred_succ]
    rw [heq]
    exact finCons_unit_orthonormal hv horth_tang horth_v
  have hspan :
      Submodule.span ℝ (Set.range frame) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hE, finrank_span_eq_card horth.linearIndependent, Fintype.card_fin]
  let b_basis := Module.Basis.mk (v := frame) horth.linearIndependent (hspan ▸ le_rfl)
  let b := b_basis.toOrthonormalBasis (show Orthonormal ℝ b_basis from by
    rw [Module.Basis.coe_mk]
    exact horth)
  let o := b.toBasis.orientation
  have hradial_norm : ‖L (frame 0)‖ = 1 := by
    simp [frame, h_radial, reflection_norm_eq_of_unit hv, hy]
  have htang' :
      ∀ i : Fin (m + 1), L (frame i.succ) = reflectionFDeriv y v (frame i.succ) := by
    intro i
    simp [frame]
    exact h_tang _ ((mem_tangentSubspace_iff).1 (tang i).2)
  have hpair :
      Pairwise fun i j => inner ℝ (L (frame i)) (L (frame j)) = 0 := by
    intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j =>
        have hvw := (mem_tangentSubspace_iff).1 (tang j).2
        have hr0 : frame 0 = v := by simp [frame]
        have hrs : frame (Fin.succ j) = tangVec j := by simp [frame, Fin.pred_succ]
        rw [hr0, h_radial, htang' j, hrs]
        exact reflectionFDeriv_apply_tangent_to_reflection_tangent hv hvw
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        have hvw := (mem_tangentSubspace_iff).1 (tang i).2
        have hr0 : frame 0 = v := by simp [frame]
        have hrs : frame (Fin.succ i) = tangVec i := by simp [frame, Fin.pred_succ]
        rw [real_inner_comm, hr0, h_radial, htang' i, hrs]
        exact reflectionFDeriv_apply_tangent_to_reflection_tangent hv hvw
      | succ j =>
        by_cases hi : i = 0
        · subst hi
          by_cases hj : j = 0
          · subst hj; exact absurd rfl hij
          · have hyw : inner ℝ y (tangVec j) = 0 := by
              rcases Fin.exists_succ_eq_of_ne_zero hj with ⟨k, rfl⟩
              simpa [tangVec, adaptedTangentFrame_succ] using
                adaptedTangentFrame_succ_inner_y hv b_plane k
            have hvw : inner ℝ v (tangVec j) = 0 := (mem_tangentSubspace_iff).1 (tang j).2
            have hrs : frame (Fin.succ j) = tangVec j := by simp [frame, Fin.pred_succ]
            rw [htang' 0, htang' j, hrs]
            simp [adaptedTangentFrame_zero, tangVec]
            exact inner_reflectionFDeriv_smul_meridian_plane_orthogonal_eq_zero hy hmer hyw hvw
        · by_cases hj : j = 0
          · subst hj
            have hyw : inner ℝ y (tangVec i) = 0 := by
              rcases Fin.exists_succ_eq_of_ne_zero hi with ⟨k, rfl⟩
              simpa [tangVec, adaptedTangentFrame_succ] using
                adaptedTangentFrame_succ_inner_y hv b_plane k
            have hvw : inner ℝ v (tangVec i) = 0 := (mem_tangentSubspace_iff).1 (tang i).2
            have hrs : frame (Fin.succ i) = tangVec i := by simp [frame, Fin.pred_succ]
            rw [htang' i, htang' 0, hrs, real_inner_comm]
            simp [adaptedTangentFrame_zero, tangVec]
            exact inner_reflectionFDeriv_smul_meridian_plane_orthogonal_eq_zero hy hmer hyw hvw
          · have hij' : i ≠ j := ne_of_apply_ne Fin.succ hij
            have horth' : inner ℝ (tangVec i) (tangVec j) = 0 := horth_tang.2 hij'
            rw [htang' i, htang' j]
            simp [frame, tangVec, adaptedTangentFrame_succ]
            exact inner_reflectionFDeriv_plane_orthogonal_eq_zero
              (by
                rcases Fin.exists_succ_eq_of_ne_zero hi with ⟨ki, rfl⟩
                simpa [tangVec, adaptedTangentFrame_succ] using
                  adaptedTangentFrame_succ_inner_y hv b_plane ki)
              (by
                rcases Fin.exists_succ_eq_of_ne_zero hj with ⟨kj, rfl⟩
                simpa [tangVec, adaptedTangentFrame_succ] using
                  adaptedTangentFrame_succ_inner_y hv b_plane kj)
              horth'
  have hnorms :
      ∀ i : Fin (m + 2), ‖L (frame i)‖ =
        if i = 0 then 1
        else if i.val = 1 then 2
        else 2 * inner ℝ y v := by
    intro i
    cases i using Fin.cases with
    | zero => simp [frame, h_radial, reflection_norm_eq_of_unit hv, hy]
    | succ i =>
      by_cases hi : i = 0
      · subst hi
        have hrs : frame (Fin.succ (0 : Fin (m + 1))) = tangVec 0 := by simp [frame, Fin.pred_succ]
        rw [htang' 0, hrs]
        simp [adaptedTangentFrame_zero, tangVec]
        exact norm_reflectionFDeriv_unit_meridianDirection_of_units hy hv hmer
      · have hrs : frame (Fin.succ i) = tangVec i := by simp [frame, Fin.pred_succ]
        rw [htang' i, hrs]
        simp [adaptedTangentFrame_succ, tangVec]
        rcases Fin.exists_succ_eq_of_ne_zero hi with ⟨k, rfl⟩
        exact norm_reflectionFDeriv_apply_of_positive_plane_orthogonal_unit
          (adaptedTangentFrame_succ_inner_y hv b_plane k) hpos
          (adaptedTangentFrame_succ_norm hv b_plane k)
  have hdet_eq :
      |L.det| = |o.volumeForm (fun i => L (frame i))| := by
    have hvol := o.volumeForm_robust' b (fun i => L (frame i))
    have hb : |b.toBasis.det b| = 1 :=
      OrthonormalBasis.det_to_matrix_orthonormalBasis b b
    have hbasis : ∀ i, (b i : E) = frame i := fun i => by
      rw [Module.Basis.coe_toOrthonormalBasis, Module.Basis.coe_mk]
    have hfun : (fun i => L (frame i)) = (L.toLinearMap ∘ b) :=
      funext fun i => by simp [Function.comp_apply, hbasis i, ContinuousLinearMap.coe_coe]
    rw [hfun] at hvol
    have hdet := congrArg abs (Module.Basis.det_comp b.toBasis L.toLinearMap b)
    rw [hdet, abs_mul, hb, mul_one] at hvol
    rw [ContinuousLinearMap.det]
    rw [← hfun] at hvol
    exact hvol.symm
  rw [hdet_eq, o.abs_volumeForm_apply_of_pairwise_orthogonal hpair]
  have hrest :
      ∀ i : Fin m, ‖L (frame i.succ.succ)‖ = 2 * inner ℝ y v := by
    intro i
    have := hnorms (Fin.succ i.succ)
    simp [Fin.ext_iff, Fin.val_succ] at this
    exact this
  have hmerid : ‖L (frame (Fin.succ (0 : Fin (m + 1))))‖ = 2 := by
    have := hnorms (Fin.succ (0 : Fin (m + 1)))
    simpa [Fin.ext_iff] using this
  have hprod :
      (∏ x : Fin (m + 1), ‖L (frame x.succ)‖) = 2 * (2 * inner ℝ y v) ^ m := by
    rw [Fin.prod_univ_succ, hmerid]
    simp [hrest]
  rw [Fin.prod_univ_succ]
  rw [show ‖L (frame 0)‖ = 1 from by simpa using hnorms 0, hprod]
  ring

/-- Pole-direction version: when `v = y`, the extension determinant is `2^(n-1)`. -/
theorem abs_det_reflectionExtension_at_pole
    [FiniteDimensional ℝ E]
    {y : E} {n : ℕ}
    (hn : 1 < n)
    (hy : ‖y‖ = 1)
    (hE : Module.finrank ℝ E = n)
    (L : E →L[ℝ] E)
    (h_radial : L y = -y)
    (h_tang :
      ∀ w : E, inner ℝ y w = 0 →
        L w = -((2 : ℝ) • w)) :
    |L.det| = (2 : ℝ) ^ (n - 1) := by
  classical
  haveI : Fact (Module.finrank ℝ E = n) := ⟨hE⟩
  have hn2 : n = n - 2 + 2 := by omega
  haveI : Fact (Module.finrank ℝ E = n - 2 + 2) := ⟨by rw [← hn2]; exact hE⟩
  let tang := tangentSubspace y
  have hfin_tang : Module.finrank ℝ tang = n - 1 := by
    have hyne : y ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hy
      norm_num at hy
    let S : Submodule ℝ E := Submodule.span ℝ ({y} : Set E)
    have hSfin : Module.finrank ℝ S = 1 := finrank_span_singleton hyne
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
        have := hw y (Submodule.subset_span (by simp))
        simpa using this
    rw [heq]
    have hsum := Submodule.finrank_add_finrank_orthogonal (K := S)
    rw [hSfin, hE] at hsum
    omega
  have hfin' : Module.finrank ℝ tang = n - 2 + 1 := by omega
  let b_tang := (stdOrthonormalBasis ℝ tang).reindex (finCongr hfin')
  let tangVec : Fin (n - 2 + 1) → E := fun i => (b_tang i : E)
  have horth_tang : Orthonormal ℝ tangVec := b_tang.orthonormal
  have horth_v :
      ∀ i, inner ℝ y (tangVec i) = 0 := by
    intro i
    exact (mem_tangentSubspace_iff).1 (b_tang i).2
  have horth_frame : Orthonormal ℝ (Fin.cons y tangVec) :=
    finCons_unit_orthonormal (m := n - 2) hy horth_tang horth_v
  let frame : Fin (n - 2 + 2) → E := fun i =>
    if h0 : i = 0 then y
    else tangVec (Fin.pred i h0)
  have heq : frame = Fin.cons y tangVec := by
    ext i
    cases i using Fin.cases with
    | zero => simp [frame, Fin.cons_zero]
    | succ j => simp [frame, Fin.cons_succ, Fin.pred_succ]
  have horth_frame' : Orthonormal ℝ frame := by
    rw [heq]
    exact finCons_unit_orthonormal (m := n - 2) hy horth_tang horth_v
  have hspan :
      Submodule.span ℝ (Set.range frame) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hE, finrank_span_eq_card horth_frame'.linearIndependent, Fintype.card_fin]
    exact hn2.symm
  let b_basis := Module.Basis.mk (v := frame) horth_frame'.linearIndependent (hspan ▸ le_rfl)
  let b := b_basis.toOrthonormalBasis (show Orthonormal ℝ b_basis from by
    rw [Module.Basis.coe_mk]
    exact horth_frame')
  let o := b.toBasis.orientation
  have hradial_norm : ‖L y‖ = 1 := by simp [h_radial, hy]
  have htang' :
      ∀ i : Fin (n - 2 + 1), L (tangVec i) = -((2 : ℝ) • tangVec i) := by
    intro i
    exact h_tang _ ((mem_tangentSubspace_iff).1 (b_tang i).2)
  have htang : ∀ i : Fin (n - 2 + 1), ‖L (tangVec i)‖ = 2 := by
    intro i
    have hnorm : ‖tangVec i‖ = 1 := by
      change ‖(b_tang i : E)‖ = 1
      exact b_tang.orthonormal.1 i
    rw [htang' i, norm_neg, norm_smul, hnorm]
    norm_num
  have hpair :
      Pairwise fun i j => inner ℝ (L (frame i)) (L (frame j)) = 0 := by
    intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j =>
        have hr0 : frame 0 = y := by simp [frame]
        have hrs : frame (Fin.succ j) = tangVec j := by simp [frame, Fin.pred_succ]
        rw [hr0, h_radial, hrs, htang' j]
        simp [inner_neg_left, inner_neg_right, inner_smul_right,
          (mem_tangentSubspace_iff).1 (b_tang j).2, tangVec]
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        have hr0 : frame 0 = y := by simp [frame]
        have hrs : frame (Fin.succ i) = tangVec i := by simp [frame, Fin.pred_succ]
        rw [real_inner_comm, hr0, h_radial, hrs, htang' i]
        simp [inner_neg_left, inner_neg_right, inner_smul_right,
          (mem_tangentSubspace_iff).1 (b_tang i).2, tangVec]
      | succ j =>
        have hrsi : frame (Fin.succ i) = tangVec i := by simp [frame, Fin.pred_succ]
        have hrsj : frame (Fin.succ j) = tangVec j := by simp [frame, Fin.pred_succ]
        have hij' : i ≠ j := ne_of_apply_ne Fin.succ hij
        have horth' : inner ℝ (tangVec i) (tangVec j) = 0 := by
          change inner ℝ (b_tang i : E) (b_tang j : E) = 0
          exact b_tang.orthonormal.inner_eq_zero hij'
        rw [hrsi, htang' i, hrsj, htang' j]
        simp [inner_neg_left, inner_neg_right, inner_smul_left, inner_smul_right, horth']
  have hnorms : ∀ i : Fin (n - 2 + 2), ‖L (frame i)‖ = if i = 0 then 1 else 2 := by
    intro i
    cases i using Fin.cases with
    | zero => simp [frame, hradial_norm]
    | succ i =>
      have hrs : frame (Fin.succ i) = tangVec i := by simp [frame, Fin.pred_succ]
      have hnorm : ‖tangVec i‖ = 1 := by
        change ‖(b_tang i : E)‖ = 1
        exact b_tang.orthonormal.1 i
      rw [hrs, htang' i, norm_neg, norm_smul, hnorm]
      simp [Fin.ext_iff, Fin.succ_ne_zero i]
  have hdet_eq :
      |L.det| = |o.volumeForm (fun i => L (frame i))| := by
    have hvol := o.volumeForm_robust' b (fun i => L (frame i))
    have hb : |b.toBasis.det b| = 1 :=
      OrthonormalBasis.det_to_matrix_orthonormalBasis b b
    have hbasis : ∀ i, (b i : E) = frame i := fun i => by
      rw [Module.Basis.coe_toOrthonormalBasis, Module.Basis.coe_mk]
    have hfun : (fun i => L (frame i)) = (L.toLinearMap ∘ b) :=
      funext fun i => by simp [Function.comp_apply, hbasis i, ContinuousLinearMap.coe_coe]
    rw [hfun] at hvol
    have hdet := congrArg abs (Module.Basis.det_comp b.toBasis L.toLinearMap b)
    rw [hdet, abs_mul, hb, mul_one] at hvol
    rw [ContinuousLinearMap.det]
    rw [← hfun] at hvol
    exact hvol.symm
  rw [hdet_eq, o.abs_volumeForm_apply_of_pairwise_orthogonal hpair]
  have hsucc : ∀ i : Fin (n - 2 + 1), ‖L (frame i.succ)‖ = 2 := by
    intro i
    have hi := hnorms i.succ
    cases i using Fin.cases with
    | zero => simpa [Fin.ext_iff] using hi
    | succ i => simpa [Fin.ext_iff, Fin.val_succ] using hi
  have hprod :
      (∏ x : Fin (n - 2 + 1), ‖L (frame x.succ)‖) = (2 : ℝ) ^ (n - 2 + 1) := by
    rw [Finset.prod_congr rfl (fun x _ => hsucc x)]
    simp
  rw [Fin.prod_univ_succ]
  rw [show ‖L (frame 0)‖ = 1 from by simpa using hnorms 0, hprod]
  rw [show (n - 2 + 1 : ℕ) = n - 1 from by omega]
  ring

end ReflectionKernelFactor

/-- A real-analysis helper: if `0 < s ≤ 1`, then `s^k ≤ 1`. -/
lemma pow_le_one_of_nonneg_of_le_one
    {s : ℝ}
    (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) :
    ∀ k : ℕ, s ^ k ≤ 1 := by
  intro k
  induction k with
  | zero =>
      norm_num
  | succ k ih =>
      rw [pow_succ]
      calc
        s ^ k * s ≤ 1 * 1 := mul_le_mul ih hs1 hs0 (by norm_num)
        _ = 1 := by norm_num

/-- If `0 < s ≤ 1`, then `(s^k)⁻¹ ≥ 1`. -/
lemma one_le_inv_pow_of_pos_le_one
    {s : ℝ}
    (k : ℕ)
    (hs0 : 0 < s)
    (hs1 : s ≤ 1) :
    1 ≤ (s ^ k)⁻¹ := by
  have hpow_le_one : s ^ k ≤ 1 :=
    pow_le_one_of_nonneg_of_le_one (le_of_lt hs0) hs1 k
  have hpow_pos : 0 < s ^ k := pow_pos hs0 k
  have hmul :=
    mul_le_mul_of_nonneg_right hpow_le_one
      (inv_nonneg.mpr (le_of_lt hpow_pos))
  calc
    1 = s ^ k * (s ^ k)⁻¹ := by
      exact (mul_inv_cancel₀ (ne_of_gt hpow_pos)).symm
    _ ≤ 1 * (s ^ k)⁻¹ := hmul
    _ = (s ^ k)⁻¹ := by rw [one_mul]

/-- Uniform lower bound for the explicit kernel, assuming the usual spherical
bounds `0 < sin(d_geo(x,y)/2) ≤ 1` away from the diagonal. -/
lemma sphericalKernel_lower_bound_of_sin_bounds
    (n : ℕ)
    {dgeo : S → S → ℝ}
    {x y : S}
    (hxy : x ≠ y)
    (hs0 : 0 < Real.sin (dgeo x y / 2))
    (hs1 : Real.sin (dgeo x y / 2) ≤ 1) :
    ((2 : ℝ) ^ (n - 2))⁻¹ ≤ sphericalKernel n dgeo x y := by
  rw [sphericalKernel_of_ne n hxy]
  have hsinv :
      1 ≤ ((Real.sin (dgeo x y / 2)) ^ (n - 2))⁻¹ :=
    one_le_inv_pow_of_pos_le_one (n - 2) hs0 hs1
  have hc : 0 ≤ ((2 : ℝ) ^ (n - 2))⁻¹ := by positivity
  calc
    ((2 : ℝ) ^ (n - 2))⁻¹
        = ((2 : ℝ) ^ (n - 2))⁻¹ * 1 := by rw [mul_one]
    _ ≤ ((2 : ℝ) ^ (n - 2))⁻¹ *
          ((Real.sin (dgeo x y / 2)) ^ (n - 2))⁻¹ :=
        mul_le_mul_of_nonneg_left hsinv hc

end Kernel

/-! ## Change-of-variables theorem as a Lean interface -/

section ChangeOfVariablesInterface

variable {S V : Type*} [MeasurableSpace S] [MeasurableSpace V]

/-- The exact positive-function change-of-variables formula needed for the
spherical polarization proof.

In the intended spherical instance:

* `S` is `S^{n-1}`;
* `V` is the same sphere of directions;
* `mu` is normalized spherical surface measure;
* `nup` is the normalized restriction to `V_p`;
* `H v = H_v`;
* `rho v y = rho_v y`;
* `phi x = inner x p`;
* `K x y = ofReal (K_n(x,y))`.

The formula is written for `ENNReal`-valued measurable functions, the standard
Lean shape for positive measurable integrands. -/
def HasKernelChangeOfVariables
    (μ : Measure S)
    (νp : Measure V)
    (H : V → Set S)
    (ρ : V → S → S)
    (φ : S → ℝ)
    (K : S → S → ℝ≥0∞) : Prop :=
  ∀ F : S × S → ℝ≥0∞,
    Measurable F →
      (∫⁻ v, (∫⁻ y in H v, F (ρ v y, y) ∂μ) ∂νp)
        =
      (∫⁻ z in {z : S × S | φ z.1 ≤ φ z.2},
          F z * K z.1 z.2 ∂(μ.prod μ))

/-- Measure-level push-forward form of the same kernel theorem.

This is the `withDensity` version of the geometric Jacobian statement.  The
source measure is the product direction/surface measure restricted to the
admissible incidence relation `y ∈ H v`, and the map sends `(v,y)` to
`(rho_v y, y)`.  In the spherical instance, `K` is
`sphericalKernelChordalENNReal`, i.e. the explicit kernel
`2^{-(n-2)} * (‖x-y‖/2)^{-(n-2)}` off the diagonal. -/
def HasKernelPushForwardDensity
    (μ : Measure S)
    (νp : Measure V)
    (H : V → Set S)
    (ρ : V → S → S)
    (φ : S → ℝ)
    (K : S → S → ℝ≥0∞) : Prop :=
  Measure.map (fun z : V × S => (ρ z.1 z.2, z.2))
      ((νp.prod μ).restrict {z : V × S | z.2 ∈ H z.1})
    =
    ((μ.prod μ).restrict {z : S × S | φ z.1 ≤ φ z.2}).withDensity
      (fun z : S × S => K z.1 z.2)

/-- The measure-level `withDensity` statement immediately gives the positive
integral change-of-variables formula on the product space.  The remaining
passage from this product-space formula to the iterated `v,y` formula is a
Fubini/measurability step, not a Jacobian computation. -/
theorem HasKernelPushForwardDensity.lintegral_pair
    {μ : Measure S}
    {νp : Measure V}
    {H : V → Set S}
    {ρ : V → S → S}
    {φ : S → ℝ}
    {K : S → S → ℝ≥0∞}
    (hPF : HasKernelPushForwardDensity μ νp H ρ φ K)
    (hρ : Measurable (fun z : V × S => (ρ z.1 z.2, z.2)))
    (hK : Measurable (fun z : S × S => K z.1 z.2))
    (F : S × S → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ z in {z : V × S | z.2 ∈ H z.1},
        F (ρ z.1 z.2, z.2) ∂(νp.prod μ))
      =
    (∫⁻ z in {z : S × S | φ z.1 ≤ φ z.2},
        F z * K z.1 z.2 ∂(μ.prod μ)) := by
  calc
    (∫⁻ z in {z : V × S | z.2 ∈ H z.1},
        F (ρ z.1 z.2, z.2) ∂(νp.prod μ))
        =
      ∫⁻ z, F z ∂Measure.map (fun z : V × S => (ρ z.1 z.2, z.2))
        ((νp.prod μ).restrict {z : V × S | z.2 ∈ H z.1}) := by
          rw [lintegral_map hF hρ]
    _ =
      ∫⁻ z, F z ∂(((μ.prod μ).restrict
          {z : S × S | φ z.1 ≤ φ z.2}).withDensity
            (fun z : S × S => K z.1 z.2)) := by
          rw [hPF]
    _ =
      ∫⁻ z, ((fun z : S × S => K z.1 z.2) * F) z
          ∂((μ.prod μ).restrict {z : S × S | φ z.1 ≤ φ z.2}) := by
          rw [lintegral_withDensity_eq_lintegral_mul _ hK hF]
    _ =
      (∫⁻ z in {z : S × S | φ z.1 ≤ φ z.2},
        F z * K z.1 z.2 ∂(μ.prod μ)) := by
          apply lintegral_congr_ae
          filter_upwards with z
          simp [mul_comm]

/-- A measure-level push-forward density theorem supplies the older iterated
kernel change-of-variables interface, after the standard Tonelli/Fubini
unfolding of the incidence restriction. -/
theorem HasKernelPushForwardDensity.to_hasKernelChangeOfVariables
    {μ : Measure S}
    {νp : Measure V}
    [SFinite μ]
    {H : V → Set S}
    {ρ : V → S → S}
    {φ : S → ℝ}
    {K : S → S → ℝ≥0∞}
    (hPF : HasKernelPushForwardDensity μ νp H ρ φ K)
    (hInc : MeasurableSet {z : V × S | z.2 ∈ H z.1})
    (hH : ∀ v : V, MeasurableSet (H v))
    (hρ : Measurable (fun z : V × S => (ρ z.1 z.2, z.2)))
    (hK : Measurable (fun z : S × S => K z.1 z.2)) :
    HasKernelChangeOfVariables μ νp H ρ φ K := by
  intro F hF
  let sourceIncidence : Set (V × S) := {z : V × S | z.2 ∈ H z.1}
  let sourceIntegrand : V × S → ℝ≥0∞ :=
    fun z => F (ρ z.1 z.2, z.2)
  have hSourceIntegrand :
      Measurable sourceIntegrand := by
    exact hF.comp hρ
  have hIndicator :
      Measurable (sourceIncidence.indicator sourceIntegrand) := by
    exact hSourceIntegrand.indicator hInc
  have hIterated :
      (∫⁻ v, (∫⁻ y in H v, F (ρ v y, y) ∂μ) ∂νp)
        =
      (∫⁻ z in sourceIncidence, sourceIntegrand z ∂(νp.prod μ)) := by
    calc
      (∫⁻ v, (∫⁻ y in H v, F (ρ v y, y) ∂μ) ∂νp)
          =
        ∫⁻ v, ∫⁻ y, (H v).indicator
          (fun y => F (ρ v y, y)) y ∂μ ∂νp := by
            apply lintegral_congr_ae
            filter_upwards with v
            rw [lintegral_indicator (hH v)]
      _ =
        ∫⁻ v, ∫⁻ y, sourceIncidence.indicator
          sourceIntegrand (v, y) ∂μ ∂νp := by
            apply lintegral_congr_ae
            filter_upwards with v
            apply lintegral_congr_ae
            filter_upwards with y
            by_cases hy : y ∈ H v <;>
              simp [sourceIncidence, sourceIntegrand, Set.indicator, hy]
      _ =
        ∫⁻ z, sourceIncidence.indicator sourceIntegrand z
          ∂(νp.prod μ) := by
            rw [lintegral_prod
              (sourceIncidence.indicator sourceIntegrand)
              hIndicator.aemeasurable]
      _ =
        (∫⁻ z in sourceIncidence, sourceIntegrand z ∂(νp.prod μ)) := by
            rw [lintegral_indicator hInc]
  exact hIterated.trans
    (hPF.lintegral_pair hρ hK F hF)

/-- The pairwise gain integrand used after applying the kernel formula. -/
def pairGain
    (φ : S → ℝ)
    (E : Set S)
    (z : S × S) : ℝ≥0∞ :=
  if z.1 ∈ E ∧ z.2 ∉ E then
    ENNReal.ofReal (φ z.2 - φ z.1)
  else
    0

/-- The averaged pair gain before change of variables. -/
def averagedPairGainBeforeCV
    (μ : Measure S)
    (νp : Measure V)
    (H : V → Set S)
    (ρ : V → S → S)
    (φ : S → ℝ)
    (E : Set S) : ℝ≥0∞ :=
  ∫⁻ v, (∫⁻ y in H v, pairGain φ E (ρ v y, y) ∂μ) ∂νp

/-- The averaged pair gain after change of variables. -/
def averagedPairGainAfterCV
    (μ : Measure S)
    (φ : S → ℝ)
    (K : S → S → ℝ≥0∞)
    (E : Set S) : ℝ≥0∞ :=
  ∫⁻ z in {z : S × S | φ z.1 ≤ φ z.2},
    pairGain φ E z * K z.1 z.2 ∂(μ.prod μ)

/-- Applying `HasKernelChangeOfVariables` to the pairwise gain integrand. -/
theorem averagedPairGain_eq_afterCV
    {μ : Measure S}
    {νp : Measure V}
    {H : V → Set S}
    {ρ : V → S → S}
    {φ : S → ℝ}
    {K : S → S → ℝ≥0∞}
    (hCV : HasKernelChangeOfVariables μ νp H ρ φ K)
    (E : Set S)
    (hMeas : Measurable (pairGain φ E)) :
    averagedPairGainBeforeCV μ νp H ρ φ E =
      averagedPairGainAfterCV μ φ K E := by
  unfold averagedPairGainBeforeCV averagedPairGainAfterCV
  exact hCV (pairGain φ E) hMeas

/-- Product-null tie-level condition needed to pass from `≤` to `<`. -/
def HasProductNullTieLevel
    (μ : Measure S)
    (φ : S → ℝ) : Prop :=
  (μ.prod μ) {z : S × S | φ z.1 = φ z.2} = 0

/-- The weak height-order domain `{phi x ≤ phi y}` is a.e. equal to the strict
domain `{phi x < phi y}` when the tie level has product measure zero. -/
lemma weakHeightDomain_ae_eq_strict_of_nullTie
    {μ : Measure S} {φ : S → ℝ}
    (hTie : HasProductNullTieLevel μ φ) :
    ({z : S × S | φ z.1 ≤ φ z.2} : Set (S × S))
      =ᵐ[μ.prod μ]
    ({z : S × S | φ z.1 < φ z.2} : Set (S × S)) := by
  refine ae_eq_set.2 ⟨?_, ?_⟩
  · refine measure_mono_null ?_ hTie
    intro z hz
    rcases hz with ⟨hle, hnotlt⟩
    change ¬ φ z.1 < φ z.2 at hnotlt
    exact (le_antisymm (not_lt.mp hnotlt) hle).symm
  · rw [Set.diff_eq_empty.mpr]
    · simp
    · intro z hz
      change φ z.1 < φ z.2 at hz
      exact le_of_lt hz

/-- Applying the kernel change-of-variables theorem and then removing the
product-null tie level gives the strict-domain average-improvement formula for
one event. -/
theorem averagedPairGain_eq_afterCV_strict
    {μ : Measure S}
    {νp : Measure V}
    {H : V → Set S}
    {ρ : V → S → S}
    {φ : S → ℝ}
    {K : S → S → ℝ≥0∞}
    (hCV : HasKernelChangeOfVariables μ νp H ρ φ K)
    (hTie : HasProductNullTieLevel μ φ)
    (E : Set S)
    (hMeas : Measurable (pairGain φ E)) :
    averagedPairGainBeforeCV μ νp H ρ φ E =
      ∫⁻ z in {z : S × S | φ z.1 < φ z.2},
        pairGain φ E z * K z.1 z.2 ∂(μ.prod μ) := by
  calc
    averagedPairGainBeforeCV μ νp H ρ φ E
        = averagedPairGainAfterCV μ φ K E := by
            exact averagedPairGain_eq_afterCV hCV E hMeas
    _ = ∫⁻ z in {z : S × S | φ z.1 < φ z.2},
        pairGain φ E z * K z.1 z.2 ∂(μ.prod μ) := by
            unfold averagedPairGainAfterCV
            exact setLIntegral_congr
              (weakHeightDomain_ae_eq_strict_of_nullTie hTie)

/-- A named proposition for the exact improvement formula after the kernel
change of variables.

The strict-domain version uses `<`; the change-of-variables interface above
naturally gives `≤`. In the spherical application, the replacement is justified
by the product-null level set `{(x,y) : phi x = phi y}`. -/
def HasAverageImprovementFormula
    (μ : Measure S)
    (φ : S → ℝ)
    (K : S → S → ℝ≥0∞)
    (avgGain : Set S → ℝ≥0∞) : Prop :=
  ∀ E : Set S,
    avgGain E =
      ∫⁻ z in {z : S × S | φ z.1 < φ z.2},
        pairGain φ E z * K z.1 z.2 ∂(μ.prod μ)

/-- The kernel change-of-variables formula plus a product-null tie level imply
the named strict-domain average-improvement formula.  Thus
`HasAverageImprovementFormula` is not an additional geometric theorem once
`HasKernelChangeOfVariables` and `HasProductNullTieLevel` have been supplied. -/
theorem hasAverageImprovementFormula_of_kernelCV_and_nullTie
    {μ : Measure S}
    {νp : Measure V}
    {H : V → Set S}
    {ρ : V → S → S}
    {φ : S → ℝ}
    {K : S → S → ℝ≥0∞}
    (hCV : HasKernelChangeOfVariables μ νp H ρ φ K)
    (hTie : HasProductNullTieLevel μ φ)
    (hMeas : ∀ E : Set S, Measurable (pairGain φ E)) :
    HasAverageImprovementFormula μ φ K
      (averagedPairGainBeforeCV μ νp H ρ φ) := by
  intro E
  exact averagedPairGain_eq_afterCV_strict hCV hTie E (hMeas E)

/-- Scalar post-COV lower bound on the averaged pair gain: restriction to
`D_- × D_+` with gain at least `τ` and kernel at least `2^{-(n-2)}` yields this
inequality.  The Jacobian / push-forward with `K_n` is proved elsewhere; this
`Prop` is only the packaged real input to `PolarizationLemma43Core`. -/
def HasRectangularBlockLowerBound
    (n : ℕ)
    (τ : ℝ)
    (μMinus μPlus avg : ℝ) : Prop :=
  2 * τ * (1 / ((2 : ℝ) ^ (n - 2))) * μMinus * μPlus ≤ avg

/-- A wrapper showing the real-valued hypothesis name expected by the
quantitative core. -/
theorem rectangularBlockLowerBound_as_core_hypothesis
    {n : ℕ}
    {τ μMinus μPlus avg : ℝ}
    (h : HasRectangularBlockLowerBound n τ μMinus μPlus avg) :
    2 * τ * (1 / ((2 : ℝ) ^ (n - 2))) * μMinus * μPlus ≤ avg := by
  exact h

/-- The rectangular-block lower bound is monotone in the separation parameter:
an estimate at a larger separation also gives the same estimate at any smaller
separation, provided the two masses are nonnegative. -/
theorem HasRectangularBlockLowerBound.mono_tau
    {n : ℕ} {τsmall τbig μMinus μPlus avg : ℝ}
    (hτ : τsmall ≤ τbig)
    (hminus : 0 ≤ μMinus) (hplus : 0 ≤ μPlus)
    (h : HasRectangularBlockLowerBound n τbig μMinus μPlus avg) :
    HasRectangularBlockLowerBound n τsmall μMinus μPlus avg := by
  unfold HasRectangularBlockLowerBound at *
  have hprod :
      0 ≤ 2 * (1 / ((2 : ℝ) ^ (n - 2))) * μMinus * μPlus := by
    positivity
  have hmono :
      τsmall * (2 * (1 / ((2 : ℝ) ^ (n - 2))) * μMinus * μPlus) ≤
        τbig * (2 * (1 / ((2 : ℝ) ^ (n - 2))) * μMinus * μPlus) :=
    mul_le_mul_of_nonneg_right hτ hprod
  nlinarith

end ChangeOfVariablesInterface

end SphericalPolarization.GeometricKernel
