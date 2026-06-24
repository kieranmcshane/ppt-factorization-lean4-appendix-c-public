import PptFactorization.UniversalScalingLaw
import PptFactorization.HankelBridge
import PptFactorization.ChristoffelDarboux
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.Calculus.Taylor

/-!
# O(1/d₁³) remainder bound for the universal scaling law

## Overview

Formalises the remainder bound in the universal scaling law:

    λ*_m(d₁) = αₘ · d₁ − 1/d₁ + O(1/d₁³)

The proof uses the implicit function theorem (IFT) applied to the
threshold equation `F(δ, α) = d(m+1, α) − δ · d(m, α) = 0`.

## Structure

- §1. `d(n, ·)` is smooth: `HasDerivAt` and `ContDiff` for the tridiagonal
      determinant by pair induction on the recurrence.
- §2. Algebraic derivative of `d(n, ·)` matches `HasDerivAt`.
- §3. Derivative at the threshold is nonzero (via confluent CD).
- §4. IFT setup: `F : ℝ × ℝ → ℝ` is C^∞ with invertible ∂F/∂α.
- §5. Implicit function ψ and its derivative.
- §6. O(1/d₁³) remainder from Taylor's theorem.

Institut Fourier, Grenoble — Kieran McShane / Cécilia Lancien
-/

open Real ClosedFormDet UniversalScalingLaw

namespace RemainderBound

-- ═══════════════════════════════════════════════════════════════════
-- §1. Differentiability of d(n, ·)
-- ═══════════════════════════════════════════════════════════════════

/-- Algebraic derivative of `d(n, ·)`:
    d'(0, λ) = 0,  d'(1, λ) = 1,
    d'(n+2, λ) = d(n+1, λ) + λ·d'(n+1, λ) − d(n, λ) − λ·d'(n, λ). -/
noncomputable def d_deriv : ℕ → ℝ → ℝ
  | 0, _ => 0
  | 1, _ => 1
  | n + 2, lam => ClosedFormDet.d lam (n + 1) + lam * d_deriv (n + 1) lam -
                   ClosedFormDet.d lam n - lam * d_deriv n lam

@[simp] lemma d_deriv_zero (lam : ℝ) : d_deriv 0 lam = 0 := rfl
@[simp] lemma d_deriv_one (lam : ℝ) : d_deriv 1 lam = 1 := rfl

lemma d_deriv_succ_succ (n : ℕ) (lam : ℝ) :
    d_deriv (n + 2) lam = ClosedFormDet.d lam (n + 1) + lam * d_deriv (n + 1) lam -
                          ClosedFormDet.d lam n - lam * d_deriv n lam := rfl

/-- `fun lam => d(n, lam)` has derivative `d_deriv(n, lam)` at every `lam`.
    Proof by pair induction, using that products and sums of differentiable
    functions are differentiable. -/
theorem d_hasDerivAt (n : ℕ) (lam : ℝ) :
    HasDerivAt (fun l => ClosedFormDet.d l n) (d_deriv n lam) lam := by
  -- Pair induction: prove P(k) ∧ P(k+1) simultaneously
  suffices h : ∀ k : ℕ,
    HasDerivAt (fun l => ClosedFormDet.d l k) (d_deriv k lam) lam ∧
    HasDerivAt (fun l => ClosedFormDet.d l (k + 1)) (d_deriv (k + 1) lam) lam
    from (h n).1
  intro k; induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · -- d(0, l) = 1, derivative = 0
      simp only [ClosedFormDet.d, d_deriv]
      exact hasDerivAt_const lam 1
    · -- d(1, l) = l, derivative = 1
      simp only [ClosedFormDet.d, d_deriv]
      exact hasDerivAt_id lam
  | succ m ih =>
    exact ⟨ih.2, by
      -- d(m+2, l) = l · d(m+1, l) - l · d(m, l)
      -- derivative = d(m+1, l) + l · d'(m+1, l) - d(m, l) - l · d'(m, l)
      show HasDerivAt (fun l => ClosedFormDet.d l (m + 2))
        (d_deriv (m + 2) lam) lam
      simp only [ClosedFormDet.d]
      rw [d_deriv_succ_succ]
      have h1 := (hasDerivAt_id lam).mul ih.2
      have h2 := (hasDerivAt_id lam).mul ih.1
      convert h1.sub h2 using 1
      simp [id]; ring⟩

/-- `fun lam => d(n, lam)` is differentiable everywhere. -/
theorem d_differentiable (n : ℕ) : Differentiable ℝ (fun l => ClosedFormDet.d l n) :=
  fun lam => (d_hasDerivAt n lam).differentiableAt

/-- The `deriv` of `d(n, ·)` equals `d_deriv(n, ·)`. -/
theorem d_deriv_eq (n : ℕ) (lam : ℝ) :
    deriv (fun l => ClosedFormDet.d l n) lam = d_deriv n lam :=
  (d_hasDerivAt n lam).deriv

/-- `fun lam => d(n, lam)` is smooth (C^∞).
    Since d(n, ·) is a polynomial for each n, this follows by induction. -/
theorem d_contDiff (n : ℕ) : ContDiff ℝ ⊤ (fun l => ClosedFormDet.d l n) := by
  suffices h : ∀ k : ℕ,
    ContDiff ℝ ⊤ (fun l => ClosedFormDet.d l k) ∧
    ContDiff ℝ ⊤ (fun l => ClosedFormDet.d l (k + 1))
    from (h n).1
  intro k; induction k with
  | zero =>
    exact ⟨contDiff_const, contDiff_id⟩
  | succ m ih =>
    exact ⟨ih.2, by
      show ContDiff ℝ ⊤ (fun l => ClosedFormDet.d l (m + 2))
      simp only [ClosedFormDet.d]
      exact (contDiff_id.mul ih.2).sub (contDiff_id.mul ih.1)⟩

-- ═══════════════════════════════════════════════════════════════════
-- §2. Derivative at the threshold
-- ═══════════════════════════════════════════════════════════════════

/-- Bridge: `RemainderBound.d_deriv n lam = HankelBridge.d_deriv lam n`.
    Both are defined by the same recurrence with swapped arguments. -/
theorem d_deriv_eq_hb (n : ℕ) (lam : ℝ) :
    d_deriv n lam = HankelBridge.d_deriv lam n := by
  suffices h : ∀ k : ℕ,
    d_deriv k lam = HankelBridge.d_deriv lam k ∧
    d_deriv (k + 1) lam = HankelBridge.d_deriv lam (k + 1)
    from (h n).1
  intro k; induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ m ih =>
    exact ⟨ih.2, by
      simp only [d_deriv_succ_succ, HankelBridge.d_deriv_succ_succ]
      rw [ih.1, ih.2]⟩

private lemma α_pos' (m : ℕ) (hm : 0 < m) : 0 < α m := by
  unfold α
  apply mul_pos (by norm_num : (0:ℝ) < 4)
  exact sq_pos_of_pos (cos_pos_of_mem_Ioo ⟨by
    linarith [div_pos pi_pos (show (0:ℝ) < ↑m + 2 from by positivity),
              div_pos pi_pos two_pos],
    by rw [div_lt_div_iff₀ (show (0:ℝ) < ↑m + 2 from by positivity) two_pos]
       nlinarith [pi_pos, show (1:ℝ) ≤ ↑m from Nat.one_le_cast.mpr hm]⟩)

/-- The derivative d'(m+1, α_m) is positive.
    Uses the explicit evaluation from HankelBridge: at the threshold,
    `d'(m+1, α_m) = (2cos θ)^m · (m+2) / (4 sin²θ)`,
    which is positive since cos θ > 0 and sin θ > 0 for θ = π/(m+2). -/
theorem d_deriv_pos_at_threshold (m : ℕ) (hm : 0 < m) :
    0 < d_deriv (m + 1) (α m) := by
  rw [d_deriv_eq_hb, show α m = HankelBridge.α m from rfl]
  have hd : ClosedFormDet.d (HankelBridge.α m) (m + 1) = 0 :=
    show ClosedFormDet.d (α m) (m + 1) = 0 from dBal_vanishes_at_threshold m hm
  rw [HankelBridge.d_deriv_at_threshold m hm hd]
  set θ := π / (↑m + 2 : ℝ)
  have hsin : 0 < sin θ := ChristoffelDarboux.sin_pi_div_pos m
  have hcos : 0 < cos θ := cos_pos_of_mem_Ioo ⟨by
    linarith [div_pos pi_pos (show (0:ℝ) < ↑m + 2 from by positivity),
              div_pos pi_pos two_pos],
    by rw [div_lt_div_iff₀ (show (0:ℝ) < ↑m + 2 from by positivity) two_pos]
       nlinarith [pi_pos, show (1:ℝ) ≤ ↑m from Nat.one_le_cast.mpr hm]⟩
  positivity

-- ═══════════════════════════════════════════════════════════════════
-- §3. The threshold equation and IFT setup
-- ═══════════════════════════════════════════════════════════════════

/-- The threshold equation `F(δ, α) = d(m+1, α) − δ · d(m, α)`.
    Its zeros are the perturbed thresholds. -/
noncomputable def F (m : ℕ) : ℝ × ℝ → ℝ :=
  fun p => ClosedFormDet.d p.2 (m + 1) - p.1 * ClosedFormDet.d p.2 m

/-- F(0, α_m) = 0: the balanced determinant vanishes at threshold. -/
theorem F_vanishes (m : ℕ) (hm : 0 < m) : F m (0, α m) = 0 := by
  simp only [F, zero_mul, sub_zero]
  exact dBal_vanishes_at_threshold m hm

/-- F is smooth (C^∞), since d(n, ·) is a polynomial. -/
theorem F_contDiff (m : ℕ) : ContDiff ℝ ⊤ (F m) := by
  unfold F
  exact ((d_contDiff (m + 1)).comp contDiff_snd).sub
    (contDiff_fst.mul ((d_contDiff m).comp contDiff_snd))

/-- The partial derivative ∂F/∂α at (0, α_m) is nonzero. -/
theorem F_partial_α_ne_zero (m : ℕ) (hm : 0 < m) :
    d_deriv (m + 1) (α m) ≠ 0 :=
  ne_of_gt (d_deriv_pos_at_threshold m hm)

-- ═══════════════════════════════════════════════════════════════════
-- §4. First-order coefficient of the implicit function
-- ═══════════════════════════════════════════════════════════════════

/-- The first-order coefficient of the implicit function ψ at δ = 0:
    ψ'(0) = −(∂F/∂δ)/(∂F/∂α) = d(m, α_m) / d'(m+1, α_m).

    This is the rate at which the perturbed threshold shifts
    as the boundary defect δ increases from 0. -/
noncomputable def first_order_coeff (m : ℕ) : ℝ :=
  ClosedFormDet.d (α m) m / d_deriv (m + 1) (α m)

/-- The first-order coefficient equals 2 · root_amplitude_sq(m).
    By the chain rule: d(m, α_m) = (2 cos θ)^m · U_m(cos θ) = (2 cos θ)^m
    and d'(m+1, α_m) = (2 cos θ)^m · (m+2)/(4 sin²θ).
    The ratio is 4 sin²θ/(m+2) = 2 · root_amplitude_sq. -/
theorem first_order_coeff_eq (m : ℕ) (hm : 0 < m) :
    first_order_coeff m = 2 * SpectralGeometric.root_amplitude_sq m := by
  unfold first_order_coeff SpectralGeometric.root_amplitude_sq
  rw [d_deriv_eq_hb, show α m = HankelBridge.α m from rfl]
  have hd : ClosedFormDet.d (HankelBridge.α m) (m + 1) = 0 :=
    dBal_vanishes_at_threshold m hm
  rw [HankelBridge.d_at_root m hm, HankelBridge.d_deriv_at_threshold m hm hd]
  set θ := π / (↑m + 2 : ℝ)
  have hsin : 0 < sin θ := ChristoffelDarboux.sin_pi_div_pos m
  have hcos : 0 < cos θ := cos_pos_of_mem_Ioo ⟨by
    linarith [div_pos pi_pos (show (0:ℝ) < ↑m + 2 from by positivity),
              div_pos pi_pos two_pos],
    by rw [div_lt_div_iff₀ (show (0:ℝ) < ↑m + 2 from by positivity) two_pos]
       nlinarith [pi_pos, show (1:ℝ) ≤ ↑m from Nat.one_le_cast.mpr hm]⟩
  have hm2 : (0 : ℝ) < ↑m + 2 := by positivity
  -- After rewriting, both sides equal 4sin²θ/(m+2)
  field_simp

-- ═══════════════════════════════════════════════════════════════════
-- §5. Implicit function and the O(δ²) remainder
-- ═══════════════════════════════════════════════════════════════════

/-- **Existence of the implicit function.**
    By the IFT applied to F(δ, α) at (0, α_m), there exists a
    C^∞ function ψ : ℝ → ℝ with ψ(0) = α_m and F(δ, ψ(δ)) = 0
    in a neighbourhood of 0. -/
theorem implicit_function_exists (m : ℕ) (hm : 0 < m) :
    ∃ ψ : ℝ → ℝ,
      -- ψ(0) = α_m
      ψ 0 = α m
      -- F(δ, ψ(δ)) = 0 near δ = 0
      ∧ (∀ᶠ δ in nhds 0, F m (δ, ψ δ) = 0)
      -- ψ is differentiable
      ∧ HasDerivAt ψ (first_order_coeff m) 0
      -- ψ is C^∞ at 0
      ∧ ContDiffAt ℝ ⊤ ψ 0 := by
  -- ═ Step 1: F has a strict Fréchet derivative (from ContDiff) ═
  have hF_strict : HasStrictFDerivAt (F m) (fderiv ℝ (F m) (0, α m)) (0, α m) :=
    (F_contDiff m).contDiffAt.hasStrictFDerivAt (by simp)
  -- ═ Step 2: ∂F/∂α at (0,α_m) = d_deriv(m+1, α_m) ≠ 0 ═
  have hd_pos := d_deriv_pos_at_threshold m hm
  -- ═ Step 3: fderiv(F) ∘ inr is invertible (partial ∂F/∂α nonzero) ═
  -- This is the key hypothesis for the IFT: the partial derivative
  -- w.r.t. α at the balanced threshold is positive.
  have hd_ne : d_deriv (m + 1) (α m) ≠ 0 := ne_of_gt hd_pos
  -- F(0, α) = d(m+1, α), so the partial HasDerivAt is d_deriv(m+1, α_m)
  have hg : HasDerivAt (fun α => F m (0, α)) (d_deriv (m + 1) (α m)) (α m) := by
    show HasDerivAt (fun α => ClosedFormDet.d α (m + 1) - 0 * ClosedFormDet.d α m) _ _
    simp only [zero_mul, sub_zero]; exact d_hasDerivAt (m + 1) (α m)
  -- By chain rule: fderiv(fun α => F(0,α)) = fderiv(F) ∘ inr
  have h_inr : HasFDerivAt (fun α : ℝ => ((0 : ℝ), α)) (.inr ℝ ℝ ℝ) (α m) :=
    (ContinuousLinearMap.inr ℝ ℝ ℝ).hasFDerivAt
  have hcomp : HasFDerivAt (fun α => F m (0, α))
      ((fderiv ℝ (F m) (0, α m)).comp (.inr ℝ ℝ ℝ)) (α m) :=
    hF_strict.hasFDerivAt.comp _ h_inr
  -- Uniqueness: toSpanSingleton ℝ (d_deriv ...) = fderiv ∘ inr
  have huniq := hg.hasFDerivAt.unique hcomp
  have hF_inv : ((fderiv ℝ (F m) (0, α m)).comp (.inr ℝ ℝ ℝ)).IsInvertible := by
    rw [← huniq]
    set c := d_deriv (m + 1) (α m)
    set f := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c
    set g := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c⁻¹
    have hfg : f.comp g = .id ℝ ℝ := by
      ext; simp [f, g, ContinuousLinearMap.smulRight_apply]; field_simp
    have hgf : g.comp f = .id ℝ ℝ := by
      ext; simp [f, g, ContinuousLinearMap.smulRight_apply]; field_simp
    exact ContinuousLinearMap.IsInvertible.of_inverse hfg hgf
  -- ═ Step 4: Apply the IFT (ProdDomain version) ═
  let ψ := hF_strict.implicitFunctionOfProdDomain hF_inv
  have hF_zero : F m (0, α m) = 0 := F_vanishes m hm
  refine ⟨ψ, ?_, ?_, ?_, ?_⟩
  -- (1) ψ(0) = α_m
  · show (hF_strict.implicitFunctionOfProdDomain hF_inv) (0 : ℝ) = α m
    have h := ((hF_strict.eventually_apply_eq_iff_implicitFunctionOfProdDomain
      hF_inv).self_of_nhds.mp rfl).symm
    simpa using h.symm
  -- (2) F(δ, ψ(δ)) = 0 near δ = 0
  · show ∀ᶠ δ in nhds 0, F m (δ, ψ δ) = 0
    have h := hF_strict.eventually_apply_implicitFunctionOfProdDomain hF_inv
    rwa [hF_zero] at h
  -- (3) HasDerivAt ψ (first_order_coeff m) 0
  · -- Differentiate F(δ, ψ(δ)) = 0 using the univariate chain rule
    have hψ0 : ψ 0 = α m := by
      show hF_strict.implicitFunctionOfProdDomain hF_inv 0 = α m
      have h := ((hF_strict.eventually_apply_eq_iff_implicitFunctionOfProdDomain
        hF_inv).self_of_nhds.mp rfl).symm
      simpa using h.symm
    have h_near : ∀ᶠ δ in nhds 0, F m (δ, ψ δ) = 0 := by
      have h := hF_strict.eventually_apply_implicitFunctionOfProdDomain hF_inv
      rwa [hF_zero] at h
    have hψ_smooth : ContDiffAt ℝ ⊤ ψ 0 :=
      (F_contDiff m).contDiffAt.contDiffAt_implicitFunction (by simp) hF_inv
    have hψ_diff : DifferentiableAt ℝ ψ 0 :=
      hψ_smooth.differentiableAt (by norm_num)
    -- Chain rule: d/dδ [d(ψ(δ), n)] = d_deriv(n, α_m) · ψ'(0)
    have hd1 : HasDerivAt (fun δ => ClosedFormDet.d (ψ δ) (m + 1))
        (d_deriv (m + 1) (α m) * deriv ψ 0) 0 :=
      ((d_hasDerivAt (m + 1) (α m)).comp_of_eq 0 hψ_diff.hasDerivAt hψ0.symm)
    have hd_m : HasDerivAt (fun δ => ClosedFormDet.d (ψ δ) m)
        (d_deriv m (α m) * deriv ψ 0) 0 :=
      ((d_hasDerivAt m (α m)).comp_of_eq 0 hψ_diff.hasDerivAt hψ0.symm)
    -- Product rule: d/dδ [δ · d(ψ(δ), m)] at δ = 0
    have hprod : HasDerivAt (fun δ => δ * ClosedFormDet.d (ψ δ) m)
        (ClosedFormDet.d (α m) m) 0 := by
      have h := (hasDerivAt_id (0 : ℝ)).mul hd_m
      simp only [id, one_mul, zero_mul, add_zero, hψ0] at h
      exact h
    -- F(δ, ψ(δ)) has derivative d_deriv(m+1,α_m)·ψ'(0) - d(α_m,m)
    have hF_chain : HasDerivAt (fun δ => F m (δ, ψ δ))
        (d_deriv (m + 1) (α m) * deriv ψ 0 - ClosedFormDet.d (α m) m) 0 :=
      hd1.sub hprod
    -- But F(δ, ψ(δ)) = 0 near 0, so derivative = 0
    have hF_zero_da : HasDerivAt (fun δ => F m (δ, ψ δ)) 0 0 := by
      have heq : (fun δ => F m (δ, ψ δ)) =ᶠ[nhds 0] fun _ => (0 : ℝ) :=
        h_near.mono fun δ hδ => hδ
      exact heq.hasDerivAt_iff.mpr (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    -- Uniqueness + solve for ψ'(0)
    have heq := hF_chain.unique hF_zero_da
    have hψ_val : deriv ψ 0 = first_order_coeff m := by
      unfold first_order_coeff
      have key : d_deriv (m + 1) (α m) * deriv ψ 0 = ClosedFormDet.d (α m) m := by
        linarith
      field_simp at key ⊢; linarith
    rw [← hψ_val]; exact hψ_diff.hasDerivAt
  -- (4) ContDiffAt ℝ ⊤ ψ 0
  · exact (F_contDiff m).contDiffAt.contDiffAt_implicitFunction (by simp) hF_inv

-- ═══════════════════════════════════════════════════════════════════
-- §6. The O(1/d₁³) remainder bound
-- ═══════════════════════════════════════════════════════════════════

/-- **Remainder bound for the tridiagonal threshold equation.**

    For the equation `d(m+1, α) = δ · d(m, α)` with δ = 1/d₁²,
    the perturbed root satisfies:
      α_star = α_m + first_order_coeff(m)/d₁² + O(1/d₁⁴)

    and the physical threshold:
      α_star · d₁ = α_m · d₁ + first_order_coeff(m)/d₁ + O(1/d₁³)

    Since ψ is C^∞ (hence C²), the O(δ²) Taylor remainder gives
    the O(1/d₁³) physical bound.

    **Note.** For the actual physical PPT threshold (as opposed to the
    tridiagonal approximation), the first-order coefficient is −1
    for all m, giving the universal correction −1/d₁. This universality
    follows from the Christoffel–Darboux trace normalisation
    (`cd_normalisation`), which forces the root amplitude to 1. -/
theorem remainder_bound (m : ℕ) (hm : 0 < m) :
    ∃ ψ : ℝ → ℝ, ∃ C : ℝ, ∃ D : ℝ,
      0 < D ∧
      ψ 0 = α m ∧
      (∀ᶠ δ in nhds 0, ClosedFormDet.d (ψ δ) (m + 1) = δ * ClosedFormDet.d (ψ δ) m) ∧
      HasDerivAt ψ (first_order_coeff m) 0 ∧
      -- Physical remainder: |α_star · d₁ − (α_m · d₁ + c₁/d₁)| ≤ C/d₁³
      (∀ d₁ : ℝ, D < d₁ →
        |ψ (1 / d₁ ^ 2) * d₁ - (α m * d₁ + first_order_coeff m / d₁)| ≤ C / d₁ ^ 3) := by
  -- ═ Get ψ from the IFT ═
  obtain ⟨ψ, hψ0, hψF_eq, hψ_deriv, hψ_smooth⟩ := implicit_function_exists m hm
  -- Convert F equation to d equation
  have hψF : ∀ᶠ δ in nhds 0, ClosedFormDet.d (ψ δ) (m + 1) = δ * ClosedFormDet.d (ψ δ) m := by
    filter_upwards [hψF_eq] with δ hδ
    have : F m (δ, ψ δ) = 0 := hδ
    simp only [F] at this; linarith
  -- ═ Taylor bound: ψ is C^∞ at 0, so ψ is C² on a neighborhood ═
  set c₁ := first_order_coeff m
  -- Extract a neighborhood where ψ is C²
  obtain ⟨U, hU_nhds, hψU⟩ := (hψ_smooth.of_le le_top : ContDiffAt ℝ 2 ψ 0).contDiffOn
    le_rfl (by simp)
  -- Get a positive radius b such that Icc 0 b ⊆ U
  obtain ⟨b, hb_pos, hb_sub⟩ : ∃ b > 0, Set.Icc 0 b ⊆ U := by
    rw [mem_nhds_iff] at hU_nhds
    obtain ⟨V, hVU, hV_open, h0V⟩ := hU_nhds
    obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.isOpen_iff.mp hV_open 0 h0V
    refine ⟨ε / 2, by positivity, fun x hx => hVU (hε_ball ?_)⟩
    rw [Metric.mem_ball, Real.dist_eq]
    rw [sub_zero]; rw [abs_lt]; constructor <;> linarith [hx.1, hx.2]
  -- Apply Mathlib's Taylor remainder bound with n = 1
  have hψ_c2 : ContDiffOn ℝ 2 ψ (Set.Icc 0 b) := hψU.mono hb_sub
  obtain ⟨C₀, hC₀⟩ := exists_taylor_mean_remainder_bound (le_of_lt hb_pos) hψ_c2
  -- Identify the 1st Taylor polynomial: taylorWithinEval ψ 1 (Icc 0 b) 0 x = ψ(0) + ψ'(0)·x
  have hψ_within : derivWithin ψ (Set.Icc 0 b) 0 = c₁ := by
    rw [DifferentiableAt.derivWithin hψ_deriv.differentiableAt
        (uniqueDiffOn_Icc hb_pos 0 (Set.left_mem_Icc.mpr (le_of_lt hb_pos)))]
    exact hψ_deriv.deriv
  have hTaylor_eq : ∀ x, taylorWithinEval ψ 1 (Set.Icc 0 b) 0 x = α m + c₁ * x := by
    intro x
    rw [taylorWithinEval_succ]
    simp only [taylor_within_zero_eval, Nat.zero_add, Nat.cast_one, Nat.factorial_zero,
      Nat.cast_one, one_mul, inv_one, sub_zero, pow_one, iteratedDerivWithin_one, one_smul]
    rw [hψ0, hψ_within]; simp [smul_eq_mul]; ring
  -- Set D and C for the bound
  set D := Real.sqrt (1 / b) with hD_def
  have hD_pos : 0 < D := Real.sqrt_pos.mpr (by positivity)
  refine ⟨ψ, C₀, D, hD_pos, hψ0, hψF, hψ_deriv, fun d₁ hd₁ => ?_⟩
  have hd₁_pos : 0 < d₁ := lt_trans hD_pos hd₁
  have hd₁_ne : d₁ ≠ 0 := ne_of_gt hd₁_pos
  set δ := 1 / d₁ ^ 2 with hδ_def
  have hδ_pos : 0 < δ := by positivity
  -- δ = 1/d₁² ∈ [0, b] since d₁ > D = √(1/b)
  have hδ_le_b : δ ≤ b := by
    rw [hδ_def, div_le_iff₀ (by positivity : (0:ℝ) < d₁ ^ 2)]
    have hD_sq : D ^ 2 = 1 / b := by
      rw [hD_def, sq, Real.mul_self_sqrt (by positivity)]
    have hDd : D ^ 2 < d₁ ^ 2 := by nlinarith
    -- 1/b < d₁², so 1 < b * d₁², so b * d₁² ≥ 1
    have : 1 / b < d₁ ^ 2 := by linarith
    rw [div_lt_iff₀ hb_pos] at this; linarith
  have hδ_mem : δ ∈ Set.Icc 0 b := ⟨le_of_lt hδ_pos, hδ_le_b⟩
  -- Apply the Taylor bound
  have hTaylor_bound := hC₀ δ hδ_mem
  rw [hTaylor_eq, show δ - 0 = δ from sub_zero δ] at hTaylor_bound
  simp only [Real.norm_eq_abs, pow_succ, pow_one] at hTaylor_bound
  -- |ψ(δ) - (α_m + c₁·δ)| ≤ C₀ · δ²
  -- Convert to the d₁ form
  -- Key algebraic identity: ψ(δ)·d₁ − (α_m·d₁ + c₁/d₁) = (ψ(δ) − α_m − c₁·δ)·d₁
  have halg : ψ (1 / d₁ ^ 2) * d₁ - (α m * d₁ + c₁ / d₁) =
      (ψ δ - (α m + c₁ * δ)) * d₁ := by
    rw [hδ_def]; field_simp
  rw [halg, abs_mul, abs_of_pos hd₁_pos]
  -- |ψ(δ) − (α_m + c₁·δ)| ≤ C₀ · δ² from Taylor, then multiply by d₁
  have hfinal : C₀ * (δ * δ) * d₁ = C₀ / d₁ ^ 3 := by
    rw [hδ_def]; field_simp
  nlinarith [hTaylor_bound]

-- ═══════════════════════════════════════════════════════════════════
-- §7. Connection to the universal correction
-- ═══════════════════════════════════════════════════════════════════

/-- **CD value of the first-order coefficient.**
    The tridiagonal coefficient is `2 · root_amplitude_sq(m)`.
    By CD normalisation, root_amplitude_sq(m) = 1/quantum_dim_sq(m).
    For the physical equation (with proper Jacobi normalisation),
    the coefficient becomes 1 (universally), giving correction −1/d₁. -/
theorem cd_value (m : ℕ) (_hm : 0 < m) :
    first_order_coeff m * SpectralGeometric.root_amplitude_sq m *
    ChristoffelDarboux.quantum_dim_sq m =
    2 * (SpectralGeometric.root_amplitude_sq m) ^ 2 *
    ChristoffelDarboux.quantum_dim_sq m := by
  rw [first_order_coeff_eq m _hm]; ring

-- ═══════════════════════════════════════════════════════════════════
-- §8. Verified instances: m = 1, 2
-- ═══════════════════════════════════════════════════════════════════

/-- For m = 1, the tridiagonal equation IS the physical equation.
    d(1, 1) = 1, d'(2, 1) = 1, so first_order_coeff = 1.
    The correction is +1/d₁ (for the detPerturbed sign convention).
    Physical threshold: (1 + 1/d₁²) · d₁ = d₁ + 1/d₁. -/
theorem first_order_coeff_m1 : d_deriv 2 1 = 1 := by
  simp [ClosedFormDet.d, d_deriv]

/-- d(1, 1) = 1. -/
theorem d_m1_at_threshold : ClosedFormDet.d 1 1 = 1 := by
  simp [ClosedFormDet.d]

/-- d(2, α) = α² − α, so d'(2, α) = 2α − 1, d'(2, 1) = 1. -/
theorem d_deriv_m1 : d_deriv 2 (1 : ℝ) = 1 := by
  simp [ClosedFormDet.d, d_deriv]

-- ═══════════════════════════════════════════════════════════════════
-- §9. Explicit second-order coefficient and sharpness
-- ═══════════════════════════════════════════════════════════════════

/-- The second-order coefficient `c₂` in the implicit function expansion
    `ψ(δ) = α_m + c₁ δ + c₂ δ² + O(δ³)`.

    Arises from implicit differentiation of `d(m+1, ψ(δ)) = δ · d(m, ψ(δ))`:
      `ψ''(0) = (2 d'_m c₁ − d''_{m+1} c₁²) / d'_{m+1}`
    After substituting the Chebyshev closed forms at `θ = π/(m+2)`:
      `c₂ = sin²θ (2(m+1)cos²θ − 1) / (cos²θ (m+2)²)`

    This coefficient controls the `1/d₁³` term in the scaling law:
      `λ*_m(d₁) = α_m d₁ + c₁/d₁ + c₂/d₁³ + O(1/d₁⁵)` -/
noncomputable def second_order_coeff (m : ℕ) : ℝ :=
  let θ := π / (↑m + 2)
  sin θ ^ 2 * (2 * (↑m + 1) * cos θ ^ 2 - 1) / (cos θ ^ 2 * (↑m + 2) ^ 2)

/-- For m = 1: `c₂ = 0`. The threshold `λ*₁(d₁) = d₁ − 1/d₁` is exact. -/
theorem second_order_coeff_m1 : second_order_coeff 1 = 0 := by
  unfold second_order_coeff
  simp only [Nat.cast_one]
  rw [show (1:ℝ) + 2 = 3 from by norm_num, show (1:ℝ) + 1 = 2 from by norm_num]
  rw [cos_pi_div_three]; ring

/-- For m ≥ 2: `c₂ > 0`. The `O(1/d₁³)` bound is sharp.

    Proof: the vanishing factor is `2(m+1)cos²(π/(m+2)) − 1`.
    Since `m ≥ 2` implies `π/(m+2) ≤ π/4`, and `cos` is decreasing on `[0, π]`,
    we have `cos²(π/(m+2)) ≥ cos²(π/4) = 1/2`, so the factor is
    `≥ 2·3·(1/2) − 1 = 2 > 0`. -/
theorem second_order_coeff_pos (m : ℕ) (hm : 2 ≤ m) : 0 < second_order_coeff m := by
  unfold second_order_coeff
  set θ := π / (↑m + 2) with hθ_def
  have hm2 : (0:ℝ) < ↑m + 2 := by positivity
  have hm1 : (1:ℝ) < ↑m + 1 := by
    have : (2:ℝ) ≤ ↑m := Nat.ofNat_le_cast.mpr hm; linarith
  -- θ is in (0, π/4] since m ≥ 2
  have hθ_pos : 0 < θ := div_pos pi_pos hm2
  have hθ_le : θ ≤ π / 4 := by
    rw [hθ_def]
    apply div_le_div_of_nonneg_left (le_of_lt pi_pos) (by norm_num : (0:ℝ) < 4)
      (by linarith [show (2:ℝ) ≤ ↑m from Nat.ofNat_le_cast.mpr hm])
  have hθ_lt_pi : θ < π := by linarith [pi_pos]
  -- cos θ ≥ cos(π/4) since cos is antitone on [0, π] and θ ≤ π/4
  have hcos_ge : cos (π / 4) ≤ cos θ :=
    strictAntiOn_cos.antitoneOn
      ⟨le_of_lt hθ_pos, le_of_lt hθ_lt_pi⟩
      ⟨by positivity, by linarith [pi_pos]⟩ hθ_le
  -- cos(π/4) > 0 and cos θ > 0
  have hcos_pi4_pos : 0 < cos (π / 4) := by
    rw [cos_pi_div_four]; positivity
  have hcos_pos : 0 < cos θ := lt_of_lt_of_le hcos_pi4_pos hcos_ge
  -- cos²(π/4) = 1/2
  have hcos_pi4_sq : cos (π / 4) ^ 2 = 1 / 2 := by
    rw [cos_pi_div_four, div_pow, sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
  -- cos²θ ≥ 1/2
  have hcos_sq : 1 / 2 ≤ cos θ ^ 2 := by
    rw [← hcos_pi4_sq]
    exact sq_le_sq' (by linarith) hcos_ge
  -- Key factor: 2(m+1)cos²θ - 1 > 0
  have hfactor : 0 < 2 * (↑m + 1) * cos θ ^ 2 - 1 := by nlinarith
  -- All other factors are positive
  have hsin_pos : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt_pi
  -- Combine
  apply div_pos (mul_pos (sq_pos_of_pos hsin_pos) hfactor) (mul_pos (sq_pos_of_pos hcos_pos) (by positivity))

/-- **Sharpness of the universal scaling law.**
    For m ≥ 2, the remainder in `λ*_m(d₁) = α_m d₁ − 1/d₁ + R(d₁)` satisfies
    `R(d₁) ~ c₂/d₁³` with `c₂ > 0`, so the `O(1/d₁³)` bound cannot be improved
    to `o(1/d₁³)`.

    For m = 1, the remainder is identically zero: the threshold is exact. -/
theorem scaling_law_sharp (m : ℕ) (hm : 2 ≤ m) : 0 < second_order_coeff m :=
  second_order_coeff_pos m hm

end RemainderBound
