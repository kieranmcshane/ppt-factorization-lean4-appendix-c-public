import PptFactorization.GaussianModel
import PptFactorization.HighProbabilityBounds
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Complex Wick/Isserlis expansions for entry monomials

This file isolates the combinatorial Wick expansion used for monomials in
complex Gaussian matrix entries and their conjugates.

The concrete analytic law is packaged as the interface
`HasComplexGaussianWickMoments`: once a Gaussian entry family is registered as
satisfying that interface, downstream moment computations can rewrite every
entry monomial expectation as the corresponding Wick contraction sum.
-/

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal Topology

noncomputable section

namespace PptFactorization
namespace ComplexGaussianWick

open RandomMatrixModel GaussianModel

variable {ι Ω₀ : Type*}

/-! ## Standard complex coordinates -/

/-- One standard complex Gaussian coordinate, written in the real-coordinate
model used throughout the project:
`z = (x₀ + I x₁) / sqrt 2`. -/
def standardComplexScalar (x : Fin 2 → ℝ) : ℂ :=
  ((complexGaussianScale * x 0 : ℝ) : ℂ) +
    ((complexGaussianScale * x 1 : ℝ) : ℂ) * Complex.I

@[simp] theorem complexVectorOfRealCoordinates_eq_standardComplexScalar
    {ι : Type*} [Fintype ι] (x : ComplexRealCoordSpace ι) (i : ι) :
    complexVectorOfRealCoordinates (ι := ι) x i =
      standardComplexScalar (fun k : Fin 2 => x (i, k)) := by
  rfl

/-- Product factorization for functions of independent standard complex
coordinate blocks.  This is the measure-theoretic independence step for the
real-coordinate product model. -/
theorem standardComplexCoordinateBlock_integral_prod
    {ι : Type*} [Fintype ι]
    (f : ι → (Fin 2 → ℝ) → ℂ) :
    ∫ x : ι → Fin 2 → ℝ, ∏ i : ι, f i (x i)
      ∂(Measure.pi (fun _ : ι =>
        Measure.pi (fun _ : Fin 2 => ProbabilityTheory.gaussianReal 0 1))) =
      ∏ i : ι, ∫ xi : Fin 2 → ℝ, f i xi
        ∂(Measure.pi (fun _ : Fin 2 => ProbabilityTheory.gaussianReal 0 1)) := by
  exact integral_fintype_prod_eq_prod (ι := ι) (E := fun _ => Fin 2 → ℝ)
    (μ := fun _ : ι =>
      Measure.pi (fun _ : Fin 2 => ProbabilityTheory.gaussianReal 0 1)) f

/-! ## The scalar complex Gaussian moment brick -/

/-- Squared modulus of the one-coordinate standard complex Gaussian under the
project's concrete complex Gaussian vector measure. -/
def standardComplexGaussianScalarNormSq (z : EuclideanSpace ℂ Unit) : ℝ :=
  ‖z ()‖ ^ 2

@[simp] theorem standardComplexGaussianScalarNormSq_apply
    (z : EuclideanSpace ℂ Unit) :
    standardComplexGaussianScalarNormSq z = ‖z ()‖ ^ 2 :=
  rfl

/-- Centered Laplace transform of the scalar squared modulus, specialized from
the already-proved product MGF for standard complex Gaussian coordinates. -/
theorem standardComplexGaussianScalarNormSq_centered_mgf {t : ℝ} (ht : t < 1) :
    ∫ z : EuclideanSpace ℂ Unit,
        Real.exp (t * (standardComplexGaussianScalarNormSq z - 1))
          ∂(standardComplexGaussianVectorMeasure Unit) =
      Real.exp (-t) / (1 - t) := by
  have h := HighProbabilityBounds.complex_standard_diagonal_mgf_factorization
    (ι := Unit) t (fun _ : Unit => (1 : ℝ)) (by intro i; simpa using ht)
  simpa [standardComplexGaussianScalarNormSq] using h

/-- Exponential integrability of the scalar squared modulus in a neighborhood
of the origin. -/
theorem integrable_exp_standardComplexGaussianScalarNormSq_of_lt_one
    {t : ℝ} (ht : t < 1) :
    Integrable (fun z : EuclideanSpace ℂ Unit =>
        Real.exp (t * standardComplexGaussianScalarNormSq z))
      (standardComplexGaussianVectorMeasure Unit) := by
  let μ : Measure (EuclideanSpace ℂ Unit) := standardComplexGaussianVectorMeasure Unit
  have hcenter_eq := standardComplexGaussianScalarNormSq_centered_mgf (t := t) ht
  have hcenter_integrable :
      Integrable
        (fun z : EuclideanSpace ℂ Unit =>
          Real.exp (t * (standardComplexGaussianScalarNormSq z - 1))) μ := by
    by_contra hnot
    have hzero :
        ∫ z : EuclideanSpace ℂ Unit,
          Real.exp (t * (standardComplexGaussianScalarNormSq z - 1)) ∂μ = 0 := by
      exact integral_undef hnot
    have hdenpos : 0 < 1 - t := by linarith
    have hpos : 0 < Real.exp (-t) / (1 - t) := div_pos (Real.exp_pos _) hdenpos
    have hzero' :
        ∫ z : EuclideanSpace ℂ Unit,
          Real.exp (t * (standardComplexGaussianScalarNormSq z - 1))
            ∂(standardComplexGaussianVectorMeasure Unit) = 0 := by
      simpa [μ] using hzero
    have hcontr : (0 : ℝ) = Real.exp (-t) / (1 - t) := hzero'.symm.trans hcenter_eq
    linarith
  have hfun :
      (fun z : EuclideanSpace ℂ Unit =>
          Real.exp (t * standardComplexGaussianScalarNormSq z)) =
        fun z : EuclideanSpace ℂ Unit =>
          Real.exp t * Real.exp (t * (standardComplexGaussianScalarNormSq z - 1)) := by
    funext z
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hfun]
  exact hcenter_integrable.const_mul (Real.exp t)

/-- MGF of the scalar squared modulus. -/
theorem standardComplexGaussianScalarNormSq_mgf_eq_inv_one_sub
    {t : ℝ} (ht : t < 1) :
    ProbabilityTheory.mgf standardComplexGaussianScalarNormSq
        (standardComplexGaussianVectorMeasure Unit) t = (1 - t)⁻¹ := by
  let μ : Measure (EuclideanSpace ℂ Unit) := standardComplexGaussianVectorMeasure Unit
  have hcenter_eq := standardComplexGaussianScalarNormSq_centered_mgf (t := t) ht
  have hfun :
      (fun z : EuclideanSpace ℂ Unit =>
          Real.exp (t * standardComplexGaussianScalarNormSq z)) =
        fun z : EuclideanSpace ℂ Unit =>
          Real.exp t * Real.exp (t * (standardComplexGaussianScalarNormSq z - 1)) := by
    funext z
    rw [← Real.exp_add]
    congr 1
    ring
  rw [ProbabilityTheory.mgf]
  change (∫ z : EuclideanSpace ℂ Unit,
    Real.exp (t * standardComplexGaussianScalarNormSq z) ∂μ) = (1 - t)⁻¹
  rw [hfun]
  rw [integral_const_mul]
  rw [show (∫ z : EuclideanSpace ℂ Unit,
          Real.exp (t * (standardComplexGaussianScalarNormSq z - 1)) ∂μ) =
        Real.exp (-t) / (1 - t) by simpa [μ] using hcenter_eq]
  rw [div_eq_mul_inv]
  rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

/-- Derivatives at zero of `(1 - t)⁻¹`. -/
theorem iteratedDeriv_one_sub_inv_zero (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => (1 - t)⁻¹) 0 = (Nat.factorial n : ℝ) := by
  have hcomp := iteratedDeriv_comp_const_sub
    (n := n) (f := fun y : ℝ => y⁻¹) (s := (1 : ℝ))
  have hbase : iteratedDeriv n (fun y : ℝ => y⁻¹) (1 : ℝ) =
      (-1 : ℝ) ^ n * (Nat.factorial n : ℝ) := by
    have hwithin := iteratedDerivWithin_one_div
      (𝕜 := ℝ) (k := n) (s := Set.univ) isOpen_univ
    have h1 := hwithin (Set.mem_univ (1 : ℝ))
    simpa using h1
  have h0 := congrFun hcomp (0 : ℝ)
  simp only [sub_zero] at h0
  rw [h0, hbase]
  have hpow : (-1 : ℝ) ^ n * ((-1 : ℝ) ^ n) = 1 := by
    rw [← pow_add]
    exact (Even.add_self n).neg_one_pow
  rw [smul_eq_mul, ← mul_assoc, hpow, one_mul]

/-- The radial moments of one standard complex Gaussian coordinate:
`E |z|^(2n) = n!`. -/
theorem standardComplexGaussianScalarNormSq_moment (n : ℕ) :
    ∫ z : EuclideanSpace ℂ Unit, standardComplexGaussianScalarNormSq z ^ n
      ∂(standardComplexGaussianVectorMeasure Unit) = (Nat.factorial n : ℝ) := by
  let μ : Measure (EuclideanSpace ℂ Unit) := standardComplexGaussianVectorMeasure Unit
  have hinterior :
      (0 : ℝ) ∈ interior
        (ProbabilityTheory.integrableExpSet standardComplexGaussianScalarNormSq μ) := by
    rw [mem_interior_iff_mem_nhds]
    refine Filter.mem_of_superset
      (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)) ?_
    intro t ht
    exact integrable_exp_standardComplexGaussianScalarNormSq_of_lt_one (t := t) ht
  have hderiv := ProbabilityTheory.iteratedDeriv_mgf_zero
    (X := standardComplexGaussianScalarNormSq) (μ := μ) hinterior n
  have hev :
      ProbabilityTheory.mgf standardComplexGaussianScalarNormSq μ =ᶠ[𝓝 (0 : ℝ)]
        (fun t : ℝ => (1 - t)⁻¹) := by
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact standardComplexGaussianScalarNormSq_mgf_eq_inv_one_sub (t := t) ht
  have hderivEq := Filter.EventuallyEq.iteratedDeriv_eq n hev
  have hcalc :
      ∫ z : EuclideanSpace ℂ Unit, standardComplexGaussianScalarNormSq z ^ n ∂μ =
        (Nat.factorial n : ℝ) := by
    calc
      ∫ z : EuclideanSpace ℂ Unit, standardComplexGaussianScalarNormSq z ^ n ∂μ
          = iteratedDeriv n
              (ProbabilityTheory.mgf standardComplexGaussianScalarNormSq μ) 0 := hderiv.symm
      _ = iteratedDeriv n (fun t : ℝ => (1 - t)⁻¹) 0 := hderivEq
      _ = (Nat.factorial n : ℝ) := iteratedDeriv_one_sub_inv_zero n
  simpa [μ] using hcalc

/-- Multiplication by a unit complex scalar as a complex-linear isometry on a
one-coordinate complex Euclidean space. -/
def phaseScalarLinearIsometryEquiv (γ : ℂ) (hγ : ‖γ‖ = 1) :
    EuclideanSpace ℂ Unit ≃ₗᵢ[ℂ] EuclideanSpace ℂ Unit := by
  have hγ_ne : γ ≠ 0 := by
    intro hzero
    have : ‖γ‖ = 0 := by simp [hzero]
    linarith
  refine LinearIsometryEquiv.mk ?e ?norm
  · refine
      { toFun := fun z => γ • z
        map_add' := ?_
        map_smul' := ?_
        invFun := fun z => γ⁻¹ • z
        left_inv := ?_
        right_inv := ?_ }
    · intro z w
      exact smul_add γ z w
    · intro c z
      ext i
      simp [mul_left_comm]
    · intro z
      ext i
      simp [hγ_ne]
    · intro z
      ext i
      simp [hγ_ne]
  · intro z
    change ‖γ • z‖ = ‖z‖
    rw [norm_smul, hγ, one_mul]

@[simp] theorem phaseScalarLinearIsometryEquiv_apply
    (γ : ℂ) (hγ : ‖γ‖ = 1) (z : EuclideanSpace ℂ Unit) (i : Unit) :
    phaseScalarLinearIsometryEquiv γ hγ z i = γ * z i :=
  rfl

/-- Phase invariance of scalar complex Gaussian moments. -/
theorem standardComplexGaussianScalar_phase_integral_eq
    (γ : ℂ) (hγ : ‖γ‖ = 1) (a b : ℕ) :
    ∫ z : EuclideanSpace ℂ Unit,
        (z ()) ^ a * star (z ()) ^ b ∂(standardComplexGaussianVectorMeasure Unit) =
      ∫ z : EuclideanSpace ℂ Unit,
        ((γ * z ()) ^ a * star (γ * z ()) ^ b)
          ∂(standardComplexGaussianVectorMeasure Unit) := by
  let U := phaseScalarLinearIsometryEquiv γ hγ
  have hmap := HighProbabilityBounds.standardComplexGaussianVectorMeasure_map_complexLinearIsometryEquiv
    (ι := Unit) U
  calc
    ∫ z : EuclideanSpace ℂ Unit,
        (z ()) ^ a * star (z ()) ^ b ∂(standardComplexGaussianVectorMeasure Unit)
        = ∫ z : EuclideanSpace ℂ Unit,
          (z ()) ^ a * star (z ()) ^ b
            ∂(Measure.map U (standardComplexGaussianVectorMeasure Unit)) := by
            rw [hmap]
    _ = ∫ z : EuclideanSpace ℂ Unit,
        ((γ * z ()) ^ a * star (γ * z ()) ^ b)
          ∂(standardComplexGaussianVectorMeasure Unit) := by
          rw [integral_map]
          · simp [U]
          · exact U.continuous.aemeasurable
          · fun_prop

/-- Phase invariance converted into an algebraic relation for the moment. -/
theorem standardComplexGaussianScalar_phase_moment_relation
    (γ : ℂ) (hγ : ‖γ‖ = 1) (a b : ℕ) :
    let M : ℂ := ∫ z : EuclideanSpace ℂ Unit,
        (z ()) ^ a * star (z ()) ^ b ∂(standardComplexGaussianVectorMeasure Unit)
    M = (γ ^ a * star γ ^ b) * M := by
  intro M
  have h := standardComplexGaussianScalar_phase_integral_eq γ hγ a b
  have hfactor :
      (fun z : EuclideanSpace ℂ Unit => (γ * z ()) ^ a * star (γ * z ()) ^ b) =
        fun z : EuclideanSpace ℂ Unit =>
          (γ ^ a * star γ ^ b) * ((z ()) ^ a * star (z ()) ^ b) := by
    funext z
    simp [mul_pow]
    ring
  calc
    M = ∫ z : EuclideanSpace ℂ Unit,
        ((γ * z ()) ^ a * star (γ * z ()) ^ b)
          ∂(standardComplexGaussianVectorMeasure Unit) := h
    _ = ∫ z : EuclideanSpace ℂ Unit,
        (γ ^ a * star γ ^ b) * ((z ()) ^ a * star (z ()) ^ b)
          ∂(standardComplexGaussianVectorMeasure Unit) := by rw [hfactor]
    _ = (γ ^ a * star γ ^ b) * M := by
      simpa [M] using
        (MeasureTheory.integral_const_mul
          (μ := standardComplexGaussianVectorMeasure Unit)
          (r := γ ^ a * star γ ^ b)
          (f := fun z : EuclideanSpace ℂ Unit =>
            (z ()) ^ a * star (z ()) ^ b))

lemma standardComplexPhase_star (θ : ℝ) :
    star (Complex.exp ((θ : ℂ) * Complex.I)) =
      Complex.exp ((-θ : ℝ) * Complex.I) := by
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  apply Complex.ext <;> simp

lemma standardComplexPhase_factor (θ : ℝ) (a b : ℕ) :
    (Complex.exp ((θ : ℂ) * Complex.I)) ^ a *
        star (Complex.exp ((θ : ℂ) * Complex.I)) ^ b =
      Complex.exp ((((a : ℂ) - (b : ℂ)) * (θ : ℂ)) * Complex.I) := by
  rw [standardComplexPhase_star]
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  norm_num
  ring

lemma nat_cast_sub_ne_zero_of_ne {a b : ℕ} (h : a ≠ b) :
    (a : ℝ) - (b : ℝ) ≠ 0 := by
  intro hz
  have hcast : (a : ℝ) = (b : ℝ) := by linarith
  exact h (Nat.cast_injective hcast)

/-- For unequal exponents, one can choose a phase whose algebraic phase factor
is not `1`. -/
lemma standardComplexPhase_factor_ne_one_of_ne (a b : ℕ) (h : a ≠ b) :
    let θ : ℝ := Real.pi / ((a + b + 1 : ℕ) : ℝ)
    (Complex.exp ((θ : ℂ) * Complex.I)) ^ a *
        star (Complex.exp ((θ : ℂ) * Complex.I)) ^ b ≠ 1 := by
  intro θ
  rw [standardComplexPhase_factor]
  intro hcoeff
  let φ : ℝ := ((a : ℝ) - (b : ℝ)) * θ
  have hcoeff' : Complex.exp ((φ : ℂ) * Complex.I) = 1 := by
    simpa [φ, sub_mul] using hcoeff
  have hcos : Real.cos φ = 1 := by
    have hre := congrArg Complex.re hcoeff'
    simpa [Complex.exp_mul_I] using hre
  have hdenpos : 0 < ((a + b + 1 : ℕ) : ℝ) := by positivity
  have hθpos : 0 < θ := by
    dsimp [θ]
    positivity
  have hφ_ne : φ ≠ 0 := by
    have hsub : (a : ℝ) - (b : ℝ) ≠ 0 := nat_cast_sub_ne_zero_of_ne h
    exact mul_ne_zero hsub (ne_of_gt hθpos)
  have hφ_lt : φ < 2 * Real.pi := by
    by_cases hab : b ≤ a
    · have hle_abs : (a : ℝ) - (b : ℝ) ≤ ((a + b + 1 : ℕ) : ℝ) := by
        have hb_nonneg : (0 : ℝ) ≤ (b : ℝ) := by positivity
        norm_num
        nlinarith
      have hφ_le_pi : φ ≤ Real.pi := by
        dsimp [φ, θ]
        have hsub_nonneg : 0 ≤ (a : ℝ) - (b : ℝ) := by
          have hbr : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast hab
          linarith
        calc
          ((a : ℝ) - (b : ℝ)) * (Real.pi / ((a + b + 1 : ℕ) : ℝ))
              = Real.pi * (((a : ℝ) - (b : ℝ)) / ((a + b + 1 : ℕ) : ℝ)) := by ring
          _ ≤ Real.pi * 1 := by
            gcongr
            exact div_le_one_of_le₀ hle_abs hdenpos.le
          _ = Real.pi := by ring
      nlinarith [Real.pi_pos]
    · have hneg : (a : ℝ) - (b : ℝ) < 0 := by
        have hlt : a < b := Nat.lt_of_not_ge hab
        have hltR : (a : ℝ) < (b : ℝ) := by exact_mod_cast hlt
        linarith
      dsimp [φ]
      nlinarith [Real.pi_pos, hθpos]
  have hφ_gt : -(2 * Real.pi) < φ := by
    by_cases hab : a ≤ b
    · have hle_abs : (b : ℝ) - (a : ℝ) ≤ ((a + b + 1 : ℕ) : ℝ) := by
        have ha_nonneg : (0 : ℝ) ≤ (a : ℝ) := by positivity
        norm_num
        nlinarith
      have hφ_ge_neg_pi : -Real.pi ≤ φ := by
        dsimp [φ, θ]
        have hpospart_nonneg : 0 ≤ (b : ℝ) - (a : ℝ) := by
          have har : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
          linarith
        calc
          -Real.pi ≤ -Real.pi * (((b : ℝ) - (a : ℝ)) / ((a + b + 1 : ℕ) : ℝ)) := by
            have hratio_le : ((b : ℝ) - (a : ℝ)) /
                ((a + b + 1 : ℕ) : ℝ) ≤ 1 :=
              div_le_one_of_le₀ hle_abs hdenpos.le
            have hratio_nonneg : 0 ≤ ((b : ℝ) - (a : ℝ)) /
                ((a + b + 1 : ℕ) : ℝ) :=
              div_nonneg hpospart_nonneg hdenpos.le
            nlinarith [Real.pi_pos]
          _ = ((a : ℝ) - (b : ℝ)) * (Real.pi / ((a + b + 1 : ℕ) : ℝ)) := by ring
      nlinarith [Real.pi_pos]
    · have hpos : 0 < (a : ℝ) - (b : ℝ) := by
        have hlt : b < a := Nat.lt_of_not_ge hab
        have hltR : (b : ℝ) < (a : ℝ) := by exact_mod_cast hlt
        linarith
      dsimp [φ]
      nlinarith [Real.pi_pos, hθpos]
  have hzero : φ = 0 := (Real.cos_eq_one_iff_of_lt_of_lt hφ_gt hφ_lt).mp hcos
  exact hφ_ne hzero

/-- Off-diagonal scalar complex Gaussian moments vanish. -/
theorem standardComplexGaussianScalar_moment_offdiag {a b : ℕ} (h : a ≠ b) :
    ∫ z : EuclideanSpace ℂ Unit,
        (z ()) ^ a * star (z ()) ^ b ∂(standardComplexGaussianVectorMeasure Unit) = 0 := by
  let θ : ℝ := Real.pi / ((a + b + 1 : ℕ) : ℝ)
  let γ : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
  have hγnorm : ‖γ‖ = 1 := by
    dsimp [γ]
    exact Complex.norm_exp_ofReal_mul_I θ
  let M : ℂ := ∫ z : EuclideanSpace ℂ Unit,
        (z ()) ^ a * star (z ()) ^ b ∂(standardComplexGaussianVectorMeasure Unit)
  have hrel := standardComplexGaussianScalar_phase_moment_relation γ hγnorm a b
  have hrel' : M = (γ ^ a * star γ ^ b) * M := by simpa [M] using hrel
  have hcoeff_ne : γ ^ a * star γ ^ b ≠ 1 := by
    dsimp [γ, θ]
    exact standardComplexPhase_factor_ne_one_of_ne a b h
  have hzero : (1 - γ ^ a * star γ ^ b) * M = 0 := by
    have hsub : M - (γ ^ a * star γ ^ b) * M = 0 := sub_eq_zero.mpr hrel'
    calc
      (1 - γ ^ a * star γ ^ b) * M = M - (γ ^ a * star γ ^ b) * M := by ring
      _ = 0 := hsub
  have hfactor_ne : 1 - γ ^ a * star γ ^ b ≠ 0 := by
    intro hz
    apply hcoeff_ne
    exact (sub_eq_zero.mp hz).symm
  have : M = 0 := by
    exact mul_eq_zero.mp hzero |>.resolve_left hfactor_ne
  simpa [M] using this

/-- Diagonal scalar complex Gaussian moments. -/
theorem standardComplexGaussianScalar_moment_diag (n : ℕ) :
    ∫ z : EuclideanSpace ℂ Unit,
        (z ()) ^ n * star (z ()) ^ n ∂(standardComplexGaussianVectorMeasure Unit) =
      (Nat.factorial n : ℂ) := by
  have hpoint :
      (fun z : EuclideanSpace ℂ Unit => (z ()) ^ n * star (z ()) ^ n) =
        fun z : EuclideanSpace ℂ Unit => (standardComplexGaussianScalarNormSq z : ℂ) ^ n := by
    funext z
    calc
      (z ()) ^ n * star (z ()) ^ n = (z () * star (z ())) ^ n := by rw [mul_pow]
      _ = ((‖z ()‖ ^ 2 : ℝ) : ℂ) ^ n := by
        have hz : z () * star (z ()) = ((‖z ()‖ ^ 2 : ℝ) : ℂ) := by
          simpa using Complex.mul_conj' (z ())
        rw [hz]
      _ = (standardComplexGaussianScalarNormSq z : ℂ) ^ n := by rfl
  rw [hpoint]
  simp_rw [← Complex.ofReal_pow]
  rw [integral_complex_ofReal]
  exact_mod_cast standardComplexGaussianScalarNormSq_moment n

/-- Central scalar complex Gaussian moment identity:
`E[z^a * conj(z)^b] = if a = b then a! else 0`, for the concrete standard
complex Gaussian measure obtained from real coordinates. -/
theorem standardComplexGaussianScalar_moment (a b : ℕ) :
    ∫ z : EuclideanSpace ℂ Unit,
        (z ()) ^ a * star (z ()) ^ b ∂(standardComplexGaussianVectorMeasure Unit) =
      if a = b then (Nat.factorial a : ℂ) else 0 := by
  by_cases h : a = b
  · subst b
    simpa using standardComplexGaussianScalar_moment_diag a
  · simpa [h] using standardComplexGaussianScalar_moment_offdiag (a := a) (b := b) h

/-- The same scalar moment identity pulled back to the raw real coordinates
`Unit × Fin 2`. -/
theorem complexVectorOfRealCoordinates_unit_raw_moment (a b : ℕ) :
    ∫ x : Unit × Fin 2 → ℝ,
        (complexVectorOfRealCoordinates (ι := Unit) (WithLp.toLp 2 x) ()) ^ a *
          star (complexVectorOfRealCoordinates (ι := Unit) (WithLp.toLp 2 x) ()) ^ b
        ∂(Measure.pi (fun _ : Unit × Fin 2 => ProbabilityTheory.gaussianReal 0 1)) =
      if a = b then (Nat.factorial a : ℂ) else 0 := by
  have h := standardComplexGaussianScalar_moment a b
  unfold standardComplexGaussianVectorMeasure at h
  rw [integral_map] at h
  rw [← ProbabilityTheory.map_pi_eq_stdGaussian (ι := Unit × Fin 2)] at h
  rw [integral_map] at h
  · simpa using h
  · fun_prop
  · fun_prop
  · exact (measurable_complexVectorOfRealCoordinates Unit).aemeasurable
  · fun_prop

/-- The requested literal two-real-coordinate form:
if `z = (x₀ + I x₁) / sqrt 2` with `x₀,x₁` independent real standard
Gaussians, then `E[z^a * conj(z)^b] = if a = b then a! else 0`. -/
theorem standardComplexScalar_moment (a b : ℕ) :
    ∫ x : Fin 2 → ℝ,
        standardComplexScalar x ^ a * star (standardComplexScalar x) ^ b
        ∂(Measure.pi (fun _ : Fin 2 => ProbabilityTheory.gaussianReal 0 1)) =
      if a = b then (Nat.factorial a : ℂ) else 0 := by
  let e : Fin 2 ≃ Unit × Fin 2 :=
    { toFun := fun k => ((), k)
      invFun := fun ik => ik.2
      left_inv := by intro k; rfl
      right_inv := by intro ik; cases ik.1; rfl }
  let f : (Unit × Fin 2 → ℝ) → ℂ := fun x =>
    (complexVectorOfRealCoordinates (ι := Unit) (WithLp.toLp 2 x) ()) ^ a *
      star (complexVectorOfRealCoordinates (ι := Unit) (WithLp.toLp 2 x) ()) ^ b
  have hmp := MeasureTheory.measurePreserving_piCongrLeft
    (μ := fun _ : Unit × Fin 2 => ProbabilityTheory.gaussianReal 0 1)
    (α := fun _ : Unit × Fin 2 => ℝ) e
  have hcomp :
      (fun x : Fin 2 → ℝ => f ((MeasurableEquiv.piCongrLeft
          (fun _ : Unit × Fin 2 => ℝ) e) x)) =
        fun x : Fin 2 → ℝ =>
          standardComplexScalar x ^ a * star (standardComplexScalar x) ^ b := by
    funext x
    have hx0 :
        (MeasurableEquiv.piCongrLeft (fun _ : Unit × Fin 2 => ℝ) e) x ((), 0) =
          x 0 := by
      simpa [e] using
        (MeasurableEquiv.piCongrLeft_apply_apply
          (e := e) (β := fun _ : Unit × Fin 2 => ℝ) x (0 : Fin 2))
    have hx1 :
        (MeasurableEquiv.piCongrLeft (fun _ : Unit × Fin 2 => ℝ) e) x ((), 1) =
          x 1 := by
      simpa [e] using
        (MeasurableEquiv.piCongrLeft_apply_apply
          (e := e) (β := fun _ : Unit × Fin 2 => ℝ) x (1 : Fin 2))
    simp [f, standardComplexScalar, complexVectorOfRealCoordinates,
      GaussianModel.complexGaussianScale, hx0, hx1]
  have hraw := complexVectorOfRealCoordinates_unit_raw_moment a b
  calc
    ∫ x : Fin 2 → ℝ,
        standardComplexScalar x ^ a * star (standardComplexScalar x) ^ b
        ∂(Measure.pi (fun _ : Fin 2 => ProbabilityTheory.gaussianReal 0 1))
        = ∫ x : Fin 2 → ℝ, f ((MeasurableEquiv.piCongrLeft
          (fun _ : Unit × Fin 2 => ℝ) e) x)
          ∂(Measure.pi (fun _ : Fin 2 => ProbabilityTheory.gaussianReal 0 1)) := by
            rw [hcomp]
    _ = ∫ x : Unit × Fin 2 → ℝ, f x
          ∂(Measure.pi (fun _ : Unit × Fin 2 => ProbabilityTheory.gaussianReal 0 1)) := by
          exact hmp.integral_comp' f
    _ = if a = b then (Nat.factorial a : ℂ) else 0 := by
          simpa [f] using hraw

/-- A monomial in complex Gaussian entries and conjugate entries. -/
structure EntryMonomial (ι : Type*) where
  holDegree : ℕ
  conjDegree : ℕ
  hol : Fin holDegree → ι
  conj : Fin conjDegree → ι

namespace EntryMonomial

/-- Evaluate the entry monomial at a complex-valued entry family. -/
def eval (M : EntryMonomial ι) (z : ι → ℂ) : ℂ :=
  (∏ k : Fin M.holDegree, z (M.hol k)) *
    (∏ k : Fin M.conjDegree, star (z (M.conj k)))

/-- Entry monomial evaluation is continuous as a polynomial in the coordinates. -/
@[fun_prop]
theorem continuous_eval (M : EntryMonomial ι) :
    Continuous (fun z : ι → ℂ => M.eval z) := by
  unfold eval
  fun_prop

/-- Holomorphic multiplicity of coordinate `i` in an entry monomial. -/
def holMultiplicity [DecidableEq ι] (M : EntryMonomial ι) (i : ι) : ℕ :=
  Fintype.card {k : Fin M.holDegree // M.hol k = i}

/-- Anti-holomorphic multiplicity of coordinate `i` in an entry monomial. -/
def conjMultiplicity [DecidableEq ι] (M : EntryMonomial ι) (i : ι) : ℕ :=
  Fintype.card {k : Fin M.conjDegree // M.conj k = i}

/-- Generic finite-product regrouping by multiplicity of each fiber. -/
theorem prod_comp_eq_prod_multiplicity
    {α β M₀ : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    [CommMonoid M₀] (g : α → β) (f : β → M₀) :
    (∏ a : α, f (g a)) =
      ∏ b : β, f b ^ Fintype.card {a : α // g a = b} := by
  classical
  rw [← Finset.prod_fiberwise' (s := Finset.univ) (g := g) (f := f)]
  apply Finset.prod_congr rfl
  intro b _
  simp [Fintype.card_subtype]

/-- Regroup the holomorphic part of an entry monomial by coordinate
multiplicity. -/
theorem holProduct_eq_prod_multiplicity [Fintype ι] [DecidableEq ι]
    (M : EntryMonomial ι) (z : ι → ℂ) :
    (∏ k : Fin M.holDegree, z (M.hol k)) =
      ∏ i : ι, z i ^ M.holMultiplicity i := by
  simpa [holMultiplicity] using
    (prod_comp_eq_prod_multiplicity (g := M.hol) (f := z))

/-- Regroup the anti-holomorphic part of an entry monomial by coordinate
multiplicity. -/
theorem conjProduct_eq_prod_multiplicity [Fintype ι] [DecidableEq ι]
    (M : EntryMonomial ι) (z : ι → ℂ) :
    (∏ k : Fin M.conjDegree, star (z (M.conj k))) =
      ∏ i : ι, star (z i) ^ M.conjMultiplicity i := by
  simpa [conjMultiplicity] using
    (prod_comp_eq_prod_multiplicity (g := M.conj) (f := fun i => star (z i)))

/-- Regroup `EntryMonomial.eval` into a holomorphic multiplicity product times
an anti-holomorphic multiplicity product. -/
theorem eval_eq_prod_multiplicities [Fintype ι] [DecidableEq ι]
    (M : EntryMonomial ι) (z : ι → ℂ) :
    M.eval z =
      (∏ i : ι, z i ^ M.holMultiplicity i) *
        (∏ i : ι, star (z i) ^ M.conjMultiplicity i) := by
  unfold EntryMonomial.eval
  rw [holProduct_eq_prod_multiplicity, conjProduct_eq_prod_multiplicity]

/-- Fully coordinatewise multiplicity regrouping of `EntryMonomial.eval`. -/
theorem eval_eq_prod_coordinate_multiplicities [Fintype ι] [DecidableEq ι]
    (M : EntryMonomial ι) (z : ι → ℂ) :
    M.eval z =
      ∏ i : ι, z i ^ M.holMultiplicity i * star (z i) ^ M.conjMultiplicity i := by
  rw [eval_eq_prod_multiplicities]
  rw [← Finset.prod_mul_distrib]

/-- The holomorphic multiplicities sum to the holomorphic degree. -/
theorem sum_holMultiplicity [Fintype ι] [DecidableEq ι]
    (M : EntryMonomial ι) :
    (∑ i : ι, M.holMultiplicity i) = M.holDegree := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin M.holDegree)))
    (t := (Finset.univ : Finset ι))
    (f := M.hol)
    (by intro a ha; simp)
  simpa [holMultiplicity, Fintype.card_subtype] using h.symm

/-- The anti-holomorphic multiplicities sum to the anti-holomorphic degree. -/
theorem sum_conjMultiplicity [Fintype ι] [DecidableEq ι]
    (M : EntryMonomial ι) :
    (∑ i : ι, M.conjMultiplicity i) = M.conjDegree := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin M.conjDegree)))
    (t := (Finset.univ : Finset ι))
    (f := M.conj)
    (by intro a ha; simp)
  simpa [conjMultiplicity, Fintype.card_subtype] using h.symm

/-- If all coordinate multiplicities agree, then the two total degrees agree. -/
theorem degree_eq_of_multiplicities_eq [Fintype ι] [DecidableEq ι]
    (M : EntryMonomial ι)
    (h : ∀ i : ι, M.holMultiplicity i = M.conjMultiplicity i) :
    M.holDegree = M.conjDegree := by
  calc
    M.holDegree = ∑ i : ι, M.holMultiplicity i :=
      (sum_holMultiplicity M).symm
    _ = ∑ i : ι, M.conjMultiplicity i := by
      exact Finset.sum_congr rfl (by intro i hi; exact h i)
    _ = M.conjDegree := sum_conjMultiplicity M

end EntryMonomial

/-- Equivalence between a finite type and the sigma-type of the fibers of a
map out of it. -/
noncomputable def fiberSigmaEquiv {α β : Type*} (f : α → β) :
    α ≃ Sigma (fun b : β => {a : α // f a = b}) where
  toFun a := ⟨f a, ⟨a, rfl⟩⟩
  invFun s := s.2.1
  left_inv := by intro a; rfl
  right_inv := by
    intro s
    rcases s with ⟨b, a, ha⟩
    cases ha
    rfl

/-- Product factorization of an entry monomial over the independent
two-real-coordinate blocks, followed by the scalar complex Gaussian moment
identity. -/
theorem standardComplexCoordinateBlock_integral_entryMonomial_multiplicity
    {ι : Type*} [Fintype ι] [DecidableEq ι] (M : EntryMonomial ι) :
    ∫ x : ι → Fin 2 → ℝ,
        M.eval (fun i : ι => standardComplexScalar (x i))
      ∂(Measure.pi (fun _ : ι =>
        Measure.pi (fun _ : Fin 2 => ProbabilityTheory.gaussianReal 0 1))) =
      ∏ i : ι,
        if M.holMultiplicity i = M.conjMultiplicity i
        then (Nat.factorial (M.holMultiplicity i) : ℂ)
        else 0 := by
  classical
  have hfun :
      (fun x : ι → Fin 2 → ℝ =>
          M.eval (fun i : ι => standardComplexScalar (x i))) =
        fun x : ι → Fin 2 → ℝ =>
          ∏ i : ι,
            standardComplexScalar (x i) ^ M.holMultiplicity i *
              star (standardComplexScalar (x i)) ^ M.conjMultiplicity i := by
    funext x
    exact EntryMonomial.eval_eq_prod_coordinate_multiplicities M
      (fun i : ι => standardComplexScalar (x i))
  rw [hfun]
  have hprod := standardComplexCoordinateBlock_integral_prod
    (ι := ι)
    (f := fun i xi =>
      standardComplexScalar xi ^ M.holMultiplicity i *
        star (standardComplexScalar xi) ^ M.conjMultiplicity i)
  rw [hprod]
  apply Finset.prod_congr rfl
  intro i hi
  exact standardComplexScalar_moment (M.holMultiplicity i) (M.conjMultiplicity i)

/-- The same multiplicity product formula, now expressed on the repository's
finite-dimensional real-coordinate `stdGaussian` model. -/
theorem standardComplexGaussianCoordinates_integral_entryMonomial_multiplicity
    {ι : Type*} [Fintype ι] [DecidableEq ι] (M : EntryMonomial ι) :
    ∫ ω : ComplexRealCoordSpace ι,
        M.eval (fun i : ι => complexVectorOfRealCoordinates ω i)
      ∂(stdGaussian (ComplexRealCoordSpace ι)) =
      ∏ i : ι,
        if M.holMultiplicity i = M.conjMultiplicity i
        then (Nat.factorial (M.holMultiplicity i) : ℂ)
        else 0 := by
  classical
  let μraw : Measure ((ι × Fin 2) → ℝ) :=
    Measure.pi (fun _ : ι × Fin 2 => ProbabilityTheory.gaussianReal 0 1)
  let μblock : Measure (ι → Fin 2 → ℝ) :=
    Measure.pi (fun _ : ι =>
      Measure.pi (fun _ : Fin 2 => ProbabilityTheory.gaussianReal 0 1))
  have hcurry :
      Measure.map (MeasurableEquiv.curry ι (Fin 2) ℝ) μraw = μblock := by
    simpa [μraw, μblock, Measure.infinitePi_eq_pi] using
      (Measure.infinitePi_map_curry
        (μ := fun _ : ι => fun _ : Fin 2 =>
          ProbabilityTheory.gaussianReal 0 1))
  have hcoordReal :
      Measurable (fun ω : ComplexRealCoordSpace ι =>
        fun i : ι => complexVectorOfRealCoordinates ω i) := by
    apply measurable_pi_lambda
    intro i
    have happly : Measurable (fun z : EuclideanSpace ℂ ι => z i) := by
      fun_prop
    exact happly.comp (measurable_complexVectorOfRealCoordinates ι)
  have hmeasReal :
      AEStronglyMeasurable
        (fun ω : ComplexRealCoordSpace ι =>
          M.eval (fun i : ι => complexVectorOfRealCoordinates ω i))
        (Measure.map (WithLp.toLp 2) μraw) := by
    exact ((EntryMonomial.continuous_eval M).measurable.comp hcoordReal).aestronglyMeasurable
  have hcoordBlock :
      Measurable (fun x : ι → Fin 2 → ℝ =>
        fun i : ι => standardComplexScalar (x i)) := by
    apply measurable_pi_lambda
    intro i
    unfold standardComplexScalar
    fun_prop
  have hmeasBlock :
      AEStronglyMeasurable
        (fun x : ι → Fin 2 → ℝ =>
          M.eval (fun i : ι => standardComplexScalar (x i)))
        (Measure.map (MeasurableEquiv.curry ι (Fin 2) ℝ) μraw) := by
    exact ((EntryMonomial.continuous_eval M).measurable.comp hcoordBlock).aestronglyMeasurable
  rw [← ProbabilityTheory.map_pi_eq_stdGaussian (ι := ι × Fin 2)]
  rw [integral_map (by fun_prop : AEMeasurable (WithLp.toLp 2) μraw) hmeasReal]
  · change
      ∫ x : (ι × Fin 2) → ℝ,
          M.eval (fun i : ι =>
            complexVectorOfRealCoordinates (WithLp.toLp 2 x) i) ∂μraw =
        ∏ i : ι,
          if M.holMultiplicity i = M.conjMultiplicity i
          then (Nat.factorial (M.holMultiplicity i) : ℂ)
          else 0
    have hpoint :
        (fun x : (ι × Fin 2) → ℝ =>
            M.eval (fun i : ι =>
              complexVectorOfRealCoordinates (WithLp.toLp 2 x) i)) =
          fun x : (ι × Fin 2) → ℝ =>
            M.eval (fun i : ι =>
              standardComplexScalar ((MeasurableEquiv.curry ι (Fin 2) ℝ x) i)) := by
      funext x
      congr 1
    rw [hpoint]
    calc
      ∫ x : (ι × Fin 2) → ℝ,
          M.eval (fun i : ι =>
            standardComplexScalar ((MeasurableEquiv.curry ι (Fin 2) ℝ x) i)) ∂μraw
          = ∫ x : ι → Fin 2 → ℝ,
              M.eval (fun i : ι => standardComplexScalar (x i))
                ∂Measure.map (MeasurableEquiv.curry ι (Fin 2) ℝ) μraw := by
              rw [integral_map
                ((MeasurableEquiv.curry ι (Fin 2) ℝ).measurable.aemeasurable)
                hmeasBlock]
      _ = ∫ x : ι → Fin 2 → ℝ,
              M.eval (fun i : ι => standardComplexScalar (x i)) ∂μblock := by
            rw [hcurry]
      _ = ∏ i : ι,
          if M.holMultiplicity i = M.conjMultiplicity i
          then (Nat.factorial (M.holMultiplicity i) : ℂ)
          else 0 :=
            standardComplexCoordinateBlock_integral_entryMonomial_multiplicity M

/-- Contribution of one Wick contraction/permutation. -/
noncomputable def pairingContribution [DecidableEq ι] {n : ℕ}
    (hol conj : Fin n → ι) (π : Equiv.Perm (Fin n)) : ℂ :=
  ∏ k : Fin n, if hol k = conj (π k) then (1 : ℂ) else 0

/-- Sum over all complex Wick contractions. -/
noncomputable def pairingSum [DecidableEq ι] {n : ℕ}
    (hol conj : Fin n → ι) : ℂ :=
  ∑ π : Equiv.Perm (Fin n), pairingContribution hol conj π

/-- Wick/Isserlis expansion for a monomial: zero unless the holomorphic and
anti-holomorphic degrees agree; otherwise sum over all contractions. -/
noncomputable def wickExpansion [DecidableEq ι] (M : EntryMonomial ι) : ℂ :=
  if h : M.holDegree = M.conjDegree then
    pairingSum M.hol (fun k : Fin M.holDegree => M.conj (Fin.cast h k))
  else 0

theorem wickExpansion_of_degree_ne [DecidableEq ι] (M : EntryMonomial ι)
    (h : M.holDegree ≠ M.conjDegree) :
    wickExpansion M = 0 := by
  simp [wickExpansion, h]

theorem wickExpansion_eq_pairingSum_of_degree_eq [DecidableEq ι]
    (M : EntryMonomial ι) (h : M.holDegree = M.conjDegree) :
    wickExpansion M =
      pairingSum M.hol (fun k : Fin M.holDegree => M.conj (Fin.cast h k)) := by
  simp [wickExpansion, h]

theorem pairingContribution_eq_zero_of_mismatch [DecidableEq ι] {n : ℕ}
    {hol conj : Fin n → ι} {π : Equiv.Perm (Fin n)} {k : Fin n}
    (h : hol k ≠ conj (π k)) :
    pairingContribution hol conj π = 0 := by
  unfold pairingContribution
  exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [h])

theorem pairingContribution_eq_one_of_forall [DecidableEq ι] {n : ℕ}
    {hol conj : Fin n → ι} {π : Equiv.Perm (Fin n)}
    (h : ∀ k : Fin n, hol k = conj (π k)) :
    pairingContribution hol conj π = 1 := by
  simp [pairingContribution, h]

theorem pairingContribution_eq_indicator_forall [DecidableEq ι] {n : ℕ}
    (hol conj : Fin n → ι) (π : Equiv.Perm (Fin n)) :
    pairingContribution hol conj π =
      if (∀ k : Fin n, hol k = conj (π k)) then (1 : ℂ) else 0 := by
  by_cases h : ∀ k : Fin n, hol k = conj (π k)
  · simp [pairingContribution_eq_one_of_forall (hol := hol) (conj := conj)
      (π := π) h, h]
  · simp [h]
    push_neg at h
    rcases h with ⟨k, hk⟩
    exact pairingContribution_eq_zero_of_mismatch (hol := hol) (conj := conj)
      (π := π) hk

/-- The Wick pairing sum is the cardinality of the compatible permutations,
cast to `ℂ`. -/
theorem pairingSum_eq_card_compatible [DecidableEq ι] {n : ℕ}
    (hol conj : Fin n → ι) :
    pairingSum hol conj =
      (Fintype.card {π : Equiv.Perm (Fin n) //
        ∀ k : Fin n, hol k = conj (π k)} : ℂ) := by
  classical
  unfold pairingSum
  simp_rw [pairingContribution_eq_indicator_forall]
  rw [Finset.sum_ite]
  simp [Fintype.card_subtype]

/-- If one compatible permutation is fixed, all compatible permutations form
a torsor over the stabilizer of the holomorphic index map. -/
theorem compatiblePerm_card_eq_prod_factorials [Fintype ι] [DecidableEq ι]
    {n : ℕ} (hol conj : Fin n → ι)
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ k : Fin n, hol k = conj (σ k)) :
    Fintype.card {π : Equiv.Perm (Fin n) //
        ∀ k : Fin n, hol k = conj (π k)} =
      ∏ i : ι, Nat.factorial (Fintype.card {k : Fin n // hol k = i}) := by
  classical
  have hcard :
      Fintype.card {π : Equiv.Perm (Fin n) //
          ∀ k : Fin n, hol k = conj (π k)} =
        Fintype.card {τ : Equiv.Perm (Fin n) // hol ∘ τ = hol} := by
    refine Fintype.card_congr ?_
    refine
      { toFun := fun π => ⟨π.1.trans σ.symm, ?_⟩
        invFun := fun τ => ⟨τ.1.trans σ, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · funext k
      have hs := hσ (σ.symm (π.1 k))
      have hp := π.2 k
      calc
        (hol ∘ (π.1.trans σ.symm)) k = hol (σ.symm (π.1 k)) := rfl
        _ = conj (π.1 k) := by simpa using hs
        _ = hol k := hp.symm
    · intro k
      have hs := hσ (τ.1 k)
      have ht := congrFun τ.2 k
      calc
        hol k = hol (τ.1 k) := ht.symm
        _ = conj (σ (τ.1 k)) := hs
        _ = conj ((τ.1.trans σ) k) := rfl
    · intro π
      ext k
      simp
    · intro τ
      ext k
      simp
  rw [hcard]
  exact DomMulAct.stabilizer_card hol

/-- Combinatorial Wick count: once a compatible permutation exists, the
compatible-permutation sum is the product of factorials of the coordinate
multiplicities. -/
theorem pairingSum_eq_prod_factorials_of_compatible [Fintype ι] [DecidableEq ι]
    {n : ℕ} (hol conj : Fin n → ι)
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ k : Fin n, hol k = conj (σ k)) :
    pairingSum hol conj =
      (∏ i : ι,
        (Nat.factorial (Fintype.card {k : Fin n // hol k = i}) : ℂ)) := by
  classical
  rw [pairingSum_eq_card_compatible]
  rw [compatiblePerm_card_eq_prod_factorials hol conj σ hσ]
  norm_num

/-- Fiberwise equal cardinalities produce a Wick-compatible permutation. -/
theorem exists_compatiblePerm_of_fiber_card_eq [Fintype ι] [DecidableEq ι]
    {n : ℕ} (hol conj : Fin n → ι)
    (hmult : ∀ i : ι,
      Fintype.card {k : Fin n // hol k = i} =
        Fintype.card {k : Fin n // conj k = i}) :
    ∃ σ : Equiv.Perm (Fin n), ∀ k : Fin n, hol k = conj (σ k) := by
  classical
  let F : (i : ι) → {k : Fin n // hol k = i} ≃ {k : Fin n // conj k = i} :=
    fun i => Fintype.equivOfCardEq (hmult i)
  let σ : Equiv.Perm (Fin n) :=
    (fiberSigmaEquiv hol).trans ((Equiv.sigmaCongrRight F).trans (fiberSigmaEquiv conj).symm)
  refine ⟨σ, ?_⟩
  intro k
  have hprop : conj ((F (hol k)) ⟨k, rfl⟩).1 = hol k :=
    ((F (hol k)) ⟨k, rfl⟩).2
  simpa [σ, fiberSigmaEquiv, F] using hprop.symm

/-- A compatible permutation forces equality of all fiber cardinalities. -/
theorem fiber_card_eq_of_compatible [Fintype ι] [DecidableEq ι]
    {n : ℕ} (hol conj : Fin n → ι)
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ k : Fin n, hol k = conj (σ k))
    (i : ι) :
    Fintype.card {k : Fin n // hol k = i} =
      Fintype.card {k : Fin n // conj k = i} := by
  classical
  refine Fintype.card_congr ?_
  refine
    { toFun := fun k => ⟨σ k.1, ?_⟩
      invFun := fun k => ⟨σ.symm k.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · simpa [hσ k.1] using k.2
  · have h := hσ (σ.symm k.1)
    calc
      hol (σ.symm k.1) = conj (σ (σ.symm k.1)) := h
      _ = conj k.1 := by simp
      _ = i := k.2
  · intro k
    ext
    simp
  · intro k
    ext
    simp

/-- Wick pairing sum as the product of scalar complex Gaussian moments, grouped
by coordinate multiplicity. -/
theorem pairingSum_eq_prod_factorial_ifs [Fintype ι] [DecidableEq ι]
    {n : ℕ} (hol conj : Fin n → ι) :
    pairingSum hol conj =
      ∏ i : ι,
        if Fintype.card {k : Fin n // hol k = i} =
            Fintype.card {k : Fin n // conj k = i}
        then (Nat.factorial (Fintype.card {k : Fin n // hol k = i}) : ℂ)
        else 0 := by
  classical
  by_cases hmult : ∀ i : ι,
      Fintype.card {k : Fin n // hol k = i} =
        Fintype.card {k : Fin n // conj k = i}
  · rcases exists_compatiblePerm_of_fiber_card_eq hol conj hmult with ⟨σ, hσ⟩
    calc
      pairingSum hol conj =
          ∏ i : ι,
            (Nat.factorial (Fintype.card {k : Fin n // hol k = i}) : ℂ) :=
        pairingSum_eq_prod_factorials_of_compatible hol conj σ hσ
      _ = ∏ i : ι,
            if Fintype.card {k : Fin n // hol k = i} =
                Fintype.card {k : Fin n // conj k = i}
            then (Nat.factorial (Fintype.card {k : Fin n // hol k = i}) : ℂ)
            else 0 := by
        exact Finset.prod_congr rfl (by intro i hi; simp [hmult i])
  · push_neg at hmult
    rcases hmult with ⟨i₀, hi₀⟩
    have hpair_zero : pairingSum hol conj = 0 := by
      rw [pairingSum_eq_card_compatible]
      have hempty :
          IsEmpty {π : Equiv.Perm (Fin n) //
            ∀ k : Fin n, hol k = conj (π k)} := by
        rw [isEmpty_subtype]
        intro π hπ
        exact hi₀ (fiber_card_eq_of_compatible hol conj π hπ i₀)
      have hcard :
          Fintype.card {π : Equiv.Perm (Fin n) //
            ∀ k : Fin n, hol k = conj (π k)} = 0 :=
        @Fintype.card_eq_zero _ _ hempty
      exact_mod_cast hcard
    have hprod_zero :
        (∏ i : ι,
          if Fintype.card {k : Fin n // hol k = i} =
              Fintype.card {k : Fin n // conj k = i}
          then (Nat.factorial (Fintype.card {k : Fin n // hol k = i}) : ℂ)
          else 0) = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [hi₀])
    rw [hpair_zero, hprod_zero]

/-- Wick expansion equals the coordinatewise product of the scalar moment
values determined by holomorphic and anti-holomorphic multiplicities. -/
theorem wickExpansion_eq_prod_multiplicity_moments [Fintype ι] [DecidableEq ι]
    (M : EntryMonomial ι) :
    wickExpansion M =
      ∏ i : ι,
        if M.holMultiplicity i = M.conjMultiplicity i
        then (Nat.factorial (M.holMultiplicity i) : ℂ)
        else 0 := by
  classical
  rcases M with ⟨n, m, hol, conj⟩
  let M0 : EntryMonomial ι := { holDegree := n, conjDegree := m, hol := hol, conj := conj }
  change wickExpansion M0 =
      ∏ i : ι,
        if M0.holMultiplicity i = M0.conjMultiplicity i
        then (Nat.factorial (M0.holMultiplicity i) : ℂ)
        else 0
  by_cases hdeg : n = m
  · subst m
    rw [wickExpansion_eq_pairingSum_of_degree_eq
      ({ holDegree := n, conjDegree := n, hol := hol, conj := conj } : EntryMonomial ι) rfl]
    rw [pairingSum_eq_prod_factorial_ifs]
    rfl
  · have hnotall : ¬ ∀ i : ι, M0.holMultiplicity i = M0.conjMultiplicity i := by
      intro h
      have hdeg' := EntryMonomial.degree_eq_of_multiplicities_eq M0 h
      exact hdeg (by simpa [M0] using hdeg')
    push_neg at hnotall
    rcases hnotall with ⟨i₀, hi₀⟩
    have hprod_zero :
        (∏ i : ι,
          if M0.holMultiplicity i = M0.conjMultiplicity i
          then (Nat.factorial (M0.holMultiplicity i) : ℂ)
          else 0) = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [hi₀])
    have hdegM0 : M0.holDegree ≠ M0.conjDegree := by
      simpa [M0] using hdeg
    rw [wickExpansion_of_degree_ne M0 hdegM0, hprod_zero]

/-- Elementary domination: `x^n` is bounded by `1 + (x^2)^n` for `x ≥ 0`. -/
lemma real_pow_le_one_add_sq_pow {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    x ^ n ≤ 1 + (x ^ 2) ^ n := by
  by_cases hle : x ≤ 1
  · have hpow : x ^ n ≤ 1 := pow_le_one₀ hx hle
    have hnonneg : 0 ≤ (x ^ 2) ^ n := pow_nonneg (sq_nonneg x) n
    linarith
  · have h1 : 1 ≤ x := le_of_lt (lt_of_not_ge hle)
    have hpow : x ^ n ≤ (x ^ 2) ^ n := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ h1 (by omega)
    have hnonneg : 0 ≤ (x ^ 2) ^ n := pow_nonneg (sq_nonneg x) n
    linarith

/-- Exponential integrability of the uncentered squared norm of a standard
complex Gaussian vector, in the subcritical Laplace range. -/
theorem standardComplexGaussianVectorMeasure_integrable_exp_norm_sq_mul
    {ι : Type*} [Fintype ι] {θ : ℝ} (hθ : θ < 1) :
    Integrable
      (fun z : EuclideanSpace ℂ ι => Real.exp (θ * ‖z‖ ^ 2))
      (standardComplexGaussianVectorMeasure ι) := by
  have hcenter :=
    HighProbabilityBounds.standardComplexGaussianVectorMeasure_norm_sq_centered_integrable_exp_mul
      (ι := ι) (θ := θ) hθ
  have hfun :
      (fun z : EuclideanSpace ℂ ι => Real.exp (θ * ‖z‖ ^ 2)) =
        fun z : EuclideanSpace ℂ ι =>
          Real.exp (θ * Fintype.card ι) *
            Real.exp (θ * (‖z‖ ^ 2 - Fintype.card ι)) := by
    funext z
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hfun]
  exact hcenter.const_mul (Real.exp (θ * Fintype.card ι))

/-- All powers of the squared norm of a standard complex Gaussian vector are
integrable. -/
theorem standardComplexGaussianVectorMeasure_integrable_norm_sq_pow
    {ι : Type*} [Fintype ι] (n : ℕ) :
    Integrable (fun z : EuclideanSpace ℂ ι => (‖z‖ ^ 2) ^ n)
      (standardComplexGaussianVectorMeasure ι) := by
  exact ProbabilityTheory.integrable_pow_of_integrable_exp_mul
    (X := fun z : EuclideanSpace ℂ ι => ‖z‖ ^ 2)
    (μ := standardComplexGaussianVectorMeasure ι)
    (t := (1 / 2 : ℝ))
    (by norm_num)
    (standardComplexGaussianVectorMeasure_integrable_exp_norm_sq_mul
      (ι := ι) (θ := (1 / 2 : ℝ)) (by norm_num))
    (by
      convert
        standardComplexGaussianVectorMeasure_integrable_exp_norm_sq_mul
          (ι := ι) (θ := (-1 / 2 : ℝ)) (by norm_num) using 1
      funext z
      congr 1
      ring)
    n

/-- An entry monomial is pointwise bounded by the corresponding power of the
ambient Euclidean norm. -/
theorem EntryMonomial.norm_eval_le_norm_pow
    {ι : Type*} [Fintype ι] (M : EntryMonomial ι)
    (z : EuclideanSpace ℂ ι) :
    ‖M.eval (fun i : ι => z i)‖ ≤ ‖z‖ ^ (M.holDegree + M.conjDegree) := by
  classical
  have hcoord : ∀ i : ι, ‖z i‖ ≤ ‖z‖ := by
    intro i
    have hsq : ‖z i‖ ^ 2 ≤ ‖z‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq z]
      exact Finset.single_le_sum
        (by intro j hj; exact sq_nonneg (‖z j‖))
        (Finset.mem_univ i)
    have habs := (sq_le_sq.mp hsq)
    simpa [abs_of_nonneg (norm_nonneg (z i)), abs_of_nonneg (norm_nonneg z)] using habs
  have hhol :
      ‖∏ k : Fin M.holDegree, z (M.hol k)‖ ≤ ‖z‖ ^ M.holDegree := by
    calc
      ‖∏ k : Fin M.holDegree, z (M.hol k)‖ =
          ∏ k : Fin M.holDegree, ‖z (M.hol k)‖ := by
        rw [norm_prod]
      _ ≤ ∏ _k : Fin M.holDegree, ‖z‖ := by
        exact Finset.prod_le_prod
          (by intro k hk; exact norm_nonneg _)
          (by intro k hk; exact hcoord (M.hol k))
      _ = ‖z‖ ^ M.holDegree := by simp
  have hconj :
      ‖∏ k : Fin M.conjDegree, star (z (M.conj k))‖ ≤ ‖z‖ ^ M.conjDegree := by
    calc
      ‖∏ k : Fin M.conjDegree, star (z (M.conj k))‖ =
          ∏ k : Fin M.conjDegree, ‖z (M.conj k)‖ := by
        simp [norm_prod]
      _ ≤ ∏ _k : Fin M.conjDegree, ‖z‖ := by
        exact Finset.prod_le_prod
          (by intro k hk; exact norm_nonneg _)
          (by intro k hk; exact hcoord (M.conj k))
      _ = ‖z‖ ^ M.conjDegree := by simp
  calc
    ‖M.eval (fun i : ι => z i)‖ =
        ‖∏ k : Fin M.holDegree, z (M.hol k)‖ *
          ‖∏ k : Fin M.conjDegree, star (z (M.conj k))‖ := by
      simp [EntryMonomial.eval]
    _ ≤ ‖z‖ ^ M.holDegree * ‖z‖ ^ M.conjDegree := by
      exact mul_le_mul hhol hconj (norm_nonneg _) (pow_nonneg (norm_nonneg z) _)
    _ = ‖z‖ ^ (M.holDegree + M.conjDegree) := by
      rw [← pow_add]

/-- Entry monomials of a standard complex Gaussian vector are integrable. -/
theorem standardComplexGaussianVectorMeasure_integrable_entryMonomial
    {ι : Type*} [Fintype ι] (M : EntryMonomial ι) :
    Integrable (fun z : EuclideanSpace ℂ ι => M.eval (fun i : ι => z i))
      (standardComplexGaussianVectorMeasure ι) := by
  classical
  let N := M.holDegree + M.conjDegree
  have hboundInt :
      Integrable (fun z : EuclideanSpace ℂ ι =>
        (1 : ℝ) + (‖z‖ ^ 2) ^ N)
        (standardComplexGaussianVectorMeasure ι) := by
    exact (integrable_const (1 : ℝ)).add
      (standardComplexGaussianVectorMeasure_integrable_norm_sq_pow (ι := ι) N)
  refine hboundInt.mono' ?hmeas ?hbound
  · exact ((EntryMonomial.continuous_eval M).measurable.comp
      (measurable_pi_lambda _ fun i =>
        (by fun_prop : Measurable (fun z : EuclideanSpace ℂ ι => z i)))).aestronglyMeasurable
  · filter_upwards with z
    exact (EntryMonomial.norm_eval_le_norm_pow M z).trans
      (real_pow_le_one_add_sq_pow (norm_nonneg z) N)

/-- Entry monomials in the real-coordinate standard complex Gaussian model are
integrable. -/
theorem standardComplexGaussianCoordinates_integrable_entryMonomial
    {ι : Type*} [Fintype ι] (M : EntryMonomial ι) :
    Integrable
      (fun ω : ComplexRealCoordSpace ι =>
        M.eval (fun i : ι => complexVectorOfRealCoordinates ω i))
      (stdGaussian (ComplexRealCoordSpace ι)) := by
  have hvec := standardComplexGaussianVectorMeasure_integrable_entryMonomial
    (ι := ι) M
  unfold standardComplexGaussianVectorMeasure at hvec
  exact
    (MeasureTheory.integrable_map_measure
      (g := fun z : EuclideanSpace ℂ ι => M.eval (fun i : ι => z i))
      (f := complexVectorOfRealCoordinates (ι := ι))
      (by
        exact ((EntryMonomial.continuous_eval M).measurable.comp
          (measurable_pi_lambda _ fun i =>
            (by fun_prop : Measurable (fun z : EuclideanSpace ℂ ι => z i)))).aestronglyMeasurable)
      ((measurable_complexVectorOfRealCoordinates ι).aemeasurable)).1 hvec

/-- Multiplicity-product formula for vector-valued standard complex Gaussian
coordinates under `standardComplexGaussianVectorMeasure`. -/
theorem standardComplexGaussianVectorMeasure_integral_entryMonomial_multiplicity
    {ι : Type*} [Fintype ι] [DecidableEq ι] (M : EntryMonomial ι) :
    ∫ z : EuclideanSpace ℂ ι,
        M.eval (fun i : ι => z i)
      ∂(standardComplexGaussianVectorMeasure ι) =
      ∏ i : ι,
        if M.holMultiplicity i = M.conjMultiplicity i
        then (Nat.factorial (M.holMultiplicity i) : ℂ)
        else 0 := by
  unfold standardComplexGaussianVectorMeasure
  rw [integral_map]
  · exact standardComplexGaussianCoordinates_integral_entryMonomial_multiplicity M
  · exact (measurable_complexVectorOfRealCoordinates ι).aemeasurable
  · exact ((EntryMonomial.continuous_eval M).measurable.comp
      (measurable_pi_lambda _ fun i =>
        (by fun_prop : Measurable (fun z : EuclideanSpace ℂ ι => z i)))).aestronglyMeasurable

/-- The empty monomial. -/
def emptyMonomial (ι : Type*) : EntryMonomial ι where
  holDegree := 0
  conjDegree := 0
  hol := Fin.elim0
  conj := Fin.elim0

/-- The degree `(1,1)` monomial `z_a * conj z_b`. -/
def singlePairMonomial (a b : ι) : EntryMonomial ι where
  holDegree := 1
  conjDegree := 1
  hol := fun _ => a
  conj := fun _ => b

theorem wickExpansion_empty [DecidableEq ι] :
    wickExpansion (emptyMonomial ι) = 1 := by
  simp [emptyMonomial, wickExpansion, pairingSum, pairingContribution]

theorem wickExpansion_single [DecidableEq ι] (a b : ι) :
    wickExpansion (singlePairMonomial a b) = if a = b then (1 : ℂ) else 0 := by
  simp [singlePairMonomial, wickExpansion, pairingSum, pairingContribution]

/-- A probability-space interface saying that an entry family satisfies the
complex Wick/Isserlis rule for all entry monomials. -/
structure HasComplexGaussianWickMoments [MeasurableSpace Ω₀] [DecidableEq ι]
    (μ : Measure Ω₀) (g : Ω₀ → ι → ℂ) : Prop where
  integrable_entryMonomial :
    ∀ M : EntryMonomial ι, Integrable (fun ω => M.eval (g ω)) μ
  integral_entryMonomial_eq_wick :
    ∀ M : EntryMonomial ι, ∫ ω, M.eval (g ω) ∂μ = wickExpansion M

/-- The user-facing Wick/Isserlis theorem for monomials of entries, once the
entry family is registered as satisfying Wick moments. -/
theorem wick_isserlis_entry_monomial [MeasurableSpace Ω₀] [DecidableEq ι]
    {μ : Measure Ω₀} {g : Ω₀ → ι → ℂ}
    (h : HasComplexGaussianWickMoments μ g) (M : EntryMonomial ι) :
    ∫ ω, M.eval (g ω) ∂μ = wickExpansion M :=
  h.integral_entryMonomial_eq_wick M

/-- Odd/unbalanced complex Gaussian monomials vanish under Wick moments. -/
theorem wick_isserlis_entry_monomial_of_degree_ne [MeasurableSpace Ω₀] [DecidableEq ι]
    {μ : Measure Ω₀} {g : Ω₀ → ι → ℂ}
    (h : HasComplexGaussianWickMoments μ g) (M : EntryMonomial ι)
    (hdeg : M.holDegree ≠ M.conjDegree) :
    ∫ ω, M.eval (g ω) ∂μ = 0 := by
  rw [h.integral_entryMonomial_eq_wick M, wickExpansion_of_degree_ne M hdeg]

/-- Balanced complex Gaussian monomials expand as a sum over Wick contractions. -/
theorem wick_isserlis_entry_monomial_of_degree_eq [MeasurableSpace Ω₀] [DecidableEq ι]
    {μ : Measure Ω₀} {g : Ω₀ → ι → ℂ}
    (h : HasComplexGaussianWickMoments μ g) (M : EntryMonomial ι)
    (hdeg : M.holDegree = M.conjDegree) :
    ∫ ω, M.eval (g ω) ∂μ =
      pairingSum M.hol (fun k : Fin M.holDegree => M.conj (Fin.cast hdeg k)) := by
  rw [h.integral_entryMonomial_eq_wick M,
    wickExpansion_eq_pairingSum_of_degree_eq M hdeg]

/-- Final no-input Wick/Isserlis law directly for the standard complex Gaussian
vector measure. -/
theorem StandardComplexGaussianVectorMeasureHaveWickMoments
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    HasComplexGaussianWickMoments (standardComplexGaussianVectorMeasure ι)
      (fun z : EuclideanSpace ℂ ι => fun i : ι => z i) := by
  refine
    { integrable_entryMonomial := ?_
      integral_entryMonomial_eq_wick := ?_ }
  · intro M
    exact standardComplexGaussianVectorMeasure_integrable_entryMonomial (ι := ι) M
  · intro M
    rw [standardComplexGaussianVectorMeasure_integral_entryMonomial_multiplicity M]
    rw [wickExpansion_eq_prod_multiplicity_moments M]

/-- Direct vector-measure Wick/Isserlis formula for every multi-coordinate
monomial. -/
theorem standardComplexGaussianVectorMeasure_wick_isserlis_entry_monomial
    {ι : Type*} [Fintype ι] [DecidableEq ι] (M : EntryMonomial ι) :
    ∫ z : EuclideanSpace ℂ ι,
        M.eval (fun i : ι => z i)
          ∂(standardComplexGaussianVectorMeasure ι) =
      wickExpansion M := by
  exact (StandardComplexGaussianVectorMeasureHaveWickMoments ι).integral_entryMonomial_eq_wick M

/-- Flatten a sample matrix into its complex Gaussian entry family. -/
def sampleMatrixEntries {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    (G : SampleMatrix p q σ) : SampleCoord p q σ → ℂ :=
  fun a => G a.1 a.2

@[simp] theorem sampleMatrixEntries_apply
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    (G : SampleMatrix p q σ) (a : SampleCoord p q σ) :
    sampleMatrixEntries G a = G a.1 a.2 :=
  rfl

/-- Entry monomial of the canonical Gaussian sample matrix. -/
def gaussianEntryMonomial {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    (M : EntryMonomial (SampleCoord p q σ)) : GaussianSampleSpace p q σ → ℂ :=
  fun ω => M.eval (sampleMatrixEntries (gaussianSampleMatrix p q σ ω))

@[simp] theorem gaussianEntryMonomial_apply
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    (M : EntryMonomial (SampleCoord p q σ)) (ω : GaussianSampleSpace p q σ) :
    gaussianEntryMonomial (p := p) (q := q) (σ := σ) M ω =
      M.eval (sampleMatrixEntries (gaussianSampleMatrix p q σ ω)) :=
  rfl

/-- The canonical sample-matrix entries are exactly the standard complex
Gaussian coordinates built from the underlying real Gaussian coordinates. -/
@[simp] theorem sampleMatrixEntries_gaussianSampleMatrix
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    (ω : GaussianSampleSpace p q σ) :
    sampleMatrixEntries (gaussianSampleMatrix p q σ ω) =
      fun a : SampleCoord p q σ => complexVectorOfRealCoordinates ω a := by
  funext a
  rcases a with ⟨i, α⟩
  rfl

/-- Final no-input Wick/Isserlis law for the standard complex Gaussian
coordinate family in the repository's real-coordinate model. -/
theorem StandardComplexGaussianCoordinatesHaveWickMoments
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    HasComplexGaussianWickMoments (stdGaussian (ComplexRealCoordSpace ι))
      (fun ω : ComplexRealCoordSpace ι =>
        fun i : ι => complexVectorOfRealCoordinates ω i) := by
  refine
    { integrable_entryMonomial := ?_
      integral_entryMonomial_eq_wick := ?_ }
  · intro M
    exact standardComplexGaussianCoordinates_integrable_entryMonomial (ι := ι) M
  · intro M
    rw [standardComplexGaussianCoordinates_integral_entryMonomial_multiplicity M]
    rw [wickExpansion_eq_prod_multiplicity_moments M]

/-- Lowercase alias for the standard-vector Wick law. -/
theorem standardComplexGaussianCoordinatesHaveWickMoments
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    HasComplexGaussianWickMoments (stdGaussian (ComplexRealCoordSpace ι))
      (fun ω : ComplexRealCoordSpace ι =>
        fun i : ι => complexVectorOfRealCoordinates ω i) :=
  StandardComplexGaussianCoordinatesHaveWickMoments ι

/-- Direct no-input Wick/Isserlis formula for every multi-coordinate monomial
of a standard complex Gaussian vector. -/
theorem standardComplexGaussianCoordinates_wick_isserlis_entry_monomial
    {ι : Type*} [Fintype ι] [DecidableEq ι] (M : EntryMonomial ι) :
    ∫ ω : ComplexRealCoordSpace ι,
        M.eval (fun i : ι => complexVectorOfRealCoordinates ω i)
          ∂(stdGaussian (ComplexRealCoordSpace ι)) =
      wickExpansion M := by
  exact (StandardComplexGaussianCoordinatesHaveWickMoments ι).integral_entryMonomial_eq_wick M

/-- The concrete matrix-entry Wick interface is completely reduced to the
standard complex-vector Wick law on the flattened coordinate type. -/
theorem concreteGaussianEntriesHaveWickMoments_of_standardComplexGaussianCoordinates
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq (SampleCoord p q σ)]
    (h :
      HasComplexGaussianWickMoments
        (stdGaussian (ComplexRealCoordSpace (SampleCoord p q σ)))
        (fun ω : ComplexRealCoordSpace (SampleCoord p q σ) =>
          fun i : SampleCoord p q σ => complexVectorOfRealCoordinates ω i)) :
    HasComplexGaussianWickMoments (gaussianSampleMeasure p q σ)
      (fun ω : GaussianSampleSpace p q σ =>
        sampleMatrixEntries (gaussianSampleMatrix p q σ ω)) := by
  change HasComplexGaussianWickMoments
    (stdGaussian (ComplexRealCoordSpace (SampleCoord p q σ)))
    (fun ω : ComplexRealCoordSpace (SampleCoord p q σ) =>
      sampleMatrixEntries (sampleMatrixOfRealCoordinates ω))
  change HasComplexGaussianWickMoments
    (stdGaussian (ComplexRealCoordSpace (SampleCoord p q σ)))
    (fun ω : ComplexRealCoordSpace (SampleCoord p q σ) =>
      fun i : SampleCoord p q σ => complexVectorOfRealCoordinates ω i) at h
  convert h using 2

/-- Final no-input Wick/Isserlis law for the canonical concrete Gaussian
matrix entries. -/
theorem ConcreteGaussianEntriesHaveWickMoments
    (p q σ : Type*) [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq (SampleCoord p q σ)] :
    HasComplexGaussianWickMoments (gaussianSampleMeasure p q σ)
      (fun ω : GaussianSampleSpace p q σ =>
        sampleMatrixEntries (gaussianSampleMatrix p q σ ω)) := by
  exact concreteGaussianEntriesHaveWickMoments_of_standardComplexGaussianCoordinates
    (StandardComplexGaussianCoordinatesHaveWickMoments (SampleCoord p q σ))

/-- Lowercase alias for the concrete Gaussian-entry Wick law. -/
theorem concreteGaussianEntriesHaveWickMoments
    (p q σ : Type*) [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq (SampleCoord p q σ)] :
    HasComplexGaussianWickMoments (gaussianSampleMeasure p q σ)
      (fun ω : GaussianSampleSpace p q σ =>
        sampleMatrixEntries (gaussianSampleMatrix p q σ ω)) :=
  ConcreteGaussianEntriesHaveWickMoments p q σ

/-- Concrete Wick/Isserlis expansion for canonical matrix-entry monomials,
under an explicit Wick-moment law for those entries. -/
theorem concrete_wick_isserlis_entry_monomial_of_hasWick
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq (SampleCoord p q σ)]
    (h :
      HasComplexGaussianWickMoments (gaussianSampleMeasure p q σ)
        (fun ω : GaussianSampleSpace p q σ =>
          sampleMatrixEntries (gaussianSampleMatrix p q σ ω)))
    (M : EntryMonomial (SampleCoord p q σ)) :
    ∫ ω : GaussianSampleSpace p q σ,
        gaussianEntryMonomial (p := p) (q := q) (σ := σ) M ω ∂gaussianSampleMeasure p q σ =
      wickExpansion M := by
  exact h.integral_entryMonomial_eq_wick M

/-- Concrete matrix-entry Wick/Isserlis expansion, using only the single
standard-vector Wick law on the flattened coordinate type. -/
theorem concrete_wick_isserlis_entry_monomial_of_standardComplexGaussianCoordinates
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq (SampleCoord p q σ)]
    (h :
      HasComplexGaussianWickMoments
        (stdGaussian (ComplexRealCoordSpace (SampleCoord p q σ)))
        (fun ω : ComplexRealCoordSpace (SampleCoord p q σ) =>
          fun i : SampleCoord p q σ => complexVectorOfRealCoordinates ω i))
    (M : EntryMonomial (SampleCoord p q σ)) :
    ∫ ω : GaussianSampleSpace p q σ,
        gaussianEntryMonomial (p := p) (q := q) (σ := σ) M ω ∂gaussianSampleMeasure p q σ =
      wickExpansion M := by
  exact concrete_wick_isserlis_entry_monomial_of_hasWick
    (concreteGaussianEntriesHaveWickMoments_of_standardComplexGaussianCoordinates h) M

/-- Concrete matrix-entry Wick/Isserlis expansion with no remaining analytic
input hypotheses. -/
theorem concrete_wick_isserlis_entry_monomial
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq (SampleCoord p q σ)]
    (M : EntryMonomial (SampleCoord p q σ)) :
    ∫ ω : GaussianSampleSpace p q σ,
        gaussianEntryMonomial (p := p) (q := q) (σ := σ) M ω ∂gaussianSampleMeasure p q σ =
      wickExpansion M := by
  exact concrete_wick_isserlis_entry_monomial_of_hasWick
    (concreteGaussianEntriesHaveWickMoments p q σ) M

/-- Backwards-compatible name for the no-input concrete matrix-entry
Wick/Isserlis expansion. -/
theorem concrete_wick_isserlis_entry_monomial_noInput
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq (SampleCoord p q σ)]
    (M : EntryMonomial (SampleCoord p q σ)) :
    ∫ ω : GaussianSampleSpace p q σ,
        gaussianEntryMonomial (p := p) (q := q) (σ := σ) M ω ∂gaussianSampleMeasure p q σ =
      wickExpansion M :=
  concrete_wick_isserlis_entry_monomial M

end ComplexGaussianWick
end PptFactorization
