import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Tactic.LinearCombination
import PptFactorization.General

/-!
# Physical scaling law for m = 3 (numerical core)

Normalised polynomial `G₃(δ, α) := Q₃(α·d₁, d₁) / d₁¹⁰` with `δ = 1/d₁²`.
`Q₃(α·d₁, d₁)` is a polynomial in `α` and `d₁²` (see `General.Q₃_leading_coeff`);
dividing by `d₁¹⁰` and substituting `δ = 1/d₁²` gives an honest polynomial in
`(δ, α)`.

The physical threshold `λ*₃(d₁)` satisfies `detB₃(λ*₃, d₁) = 0`, equivalently
`G₃(1/d₁², λ*₃/d₁) = 0`.  At `δ = 0` the root is `α = α₃ = (3+√5)/2`.

This file establishes the numerical content of the universal scaling law at
m = 3:

* `G₃` vanishes at `(0, α₃)`,
* the formal partial-derivative polynomials `G₃_dα`, `G₃_dδ` satisfy
  `G₃_dα 0 α₃ = G₃_dδ 0 α₃ = (15 + 7√5)/2`,
* hence the implicit-function first-order coefficient
  `−(G₃_dδ 0 α₃) / (G₃_dα 0 α₃)` equals **`−1`**, matching the universal
  scaling law.

`HasDerivAt` wiring, IFT and Taylor remainder are deferred.
-/

open Real Filter Topology

namespace PhysicalThresholdM3

/-- Normalised m = 3 threshold polynomial: `G₃(δ, α) = Q₃(α d₁, d₁)/d₁¹⁰`
    with `δ = 1/d₁²`.  Derived from `General.Q₃_leading_coeff`. -/
noncomputable def G₃ (δ α : ℝ) : ℝ :=
  α ^ 2 * (α ^ 2 - 3 * α + 1) +
  δ * (α * (6 * α ^ 2 - 15 * α + 4)) +
  δ ^ 2 * (- 3 * α ^ 3 + 21 * α ^ 2 - 24 * α + 4) +
  δ ^ 3 * (- 5 * α ^ 2 + 20 * α - 12) +
  δ ^ 4 * (- 2 * α ^ 2 + 12) +
  δ ^ 5 * (- 4)

/-- The m = 3 balanced threshold `α₃ = (3 + √5)/2 = 4 cos²(π/5)`. -/
noncomputable def α₃ : ℝ := (3 + Real.sqrt 5) / 2

private lemma sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := by
  rw [sq]; exact Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 5)

/-- `α₃² = 3 α₃ − 1`. -/
theorem α₃_sq : α₃ ^ 2 = 3 * α₃ - 1 := by
  unfold α₃; nlinarith [sqrt5_sq]

/-- `α₃² − 3 α₃ + 1 = 0`. -/
theorem α₃_vanishes_quadratic : α₃ ^ 2 - 3 * α₃ + 1 = 0 := by
  have := α₃_sq; linarith

/-- `α₃³ = 8 α₃ − 3`. -/
theorem α₃_cube : α₃ ^ 3 = 8 * α₃ - 3 := by
  have h : α₃ ^ 3 = α₃ * α₃ ^ 2 := by ring
  rw [h, α₃_sq]; nlinarith [α₃_sq]

-- ═══════════════════════════════════════════════════════════════════
-- §1. G₃ vanishes at the balanced threshold
-- ═══════════════════════════════════════════════════════════════════

theorem G₃_vanishes_balanced : G₃ 0 α₃ = 0 := by
  unfold G₃
  have h : α₃ ^ 2 - 3 * α₃ + 1 = 0 := α₃_vanishes_quadratic
  nlinarith [h, sq_nonneg α₃]

-- ═══════════════════════════════════════════════════════════════════
-- §2. Formal partial derivatives (polynomial forms)
-- ═══════════════════════════════════════════════════════════════════

/-- Formal `∂_α G₃(δ, α)` as a polynomial. -/
noncomputable def G₃_dα (δ α : ℝ) : ℝ :=
  (4 * α ^ 3 - 9 * α ^ 2 + 2 * α) +
  δ * (18 * α ^ 2 - 30 * α + 4) +
  δ ^ 2 * (- 9 * α ^ 2 + 42 * α - 24) +
  δ ^ 3 * (- 10 * α + 20) +
  δ ^ 4 * (- 4 * α)

/-- Formal `∂_δ G₃(δ, α)` as a polynomial. -/
noncomputable def G₃_dδ (δ α : ℝ) : ℝ :=
  α * (6 * α ^ 2 - 15 * α + 4) +
  2 * δ * (- 3 * α ^ 3 + 21 * α ^ 2 - 24 * α + 4) +
  3 * δ ^ 2 * (- 5 * α ^ 2 + 20 * α - 12) +
  4 * δ ^ 3 * (- 2 * α ^ 2 + 12) +
  5 * δ ^ 4 * (- 4)

/-- `∂_α G₃(0, α₃) = (15 + 7√5)/2`.
    Derivation: `4 α₃³ − 9 α₃² + 2 α₃` with `α₃² = 3α₃−1`, `α₃³ = 8α₃−3`. -/
theorem G₃_dα_at_base : G₃_dα 0 α₃ = (15 + 7 * Real.sqrt 5) / 2 := by
  unfold G₃_dα α₃
  have h2 : α₃ ^ 2 = 3 * α₃ - 1 := α₃_sq
  have h3 : α₃ ^ 3 = 8 * α₃ - 3 := α₃_cube
  nlinarith [sqrt5_sq, h2, h3]

/-- `∂_δ G₃(0, α₃) = (15 + 7√5)/2`.
    Derivation: `α₃(6α₃² − 15α₃ + 4)` with `α₃² = 3α₃−1`. -/
theorem G₃_dδ_at_base : G₃_dδ 0 α₃ = (15 + 7 * Real.sqrt 5) / 2 := by
  unfold G₃_dδ α₃
  have h2 : α₃ ^ 2 = 3 * α₃ - 1 := α₃_sq
  nlinarith [sqrt5_sq, h2]

theorem G₃_dα_pos : 0 < G₃_dα 0 α₃ := by
  rw [G₃_dα_at_base]
  have : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 5)
  linarith

theorem G₃_dδ_eq_dα : G₃_dδ 0 α₃ = G₃_dα 0 α₃ := by
  rw [G₃_dα_at_base, G₃_dδ_at_base]

-- ═══════════════════════════════════════════════════════════════════
-- §3. Bridge to the physical Q₃ / detB₃
-- ═══════════════════════════════════════════════════════════════════

/-- Bridge: `Q₃(α·d₁, d₁) = d₁¹⁰ · G₃(1/d₁², α)`.
    Verified directly from `General.Q₃_leading_coeff`. -/
theorem Q₃_eq_G₃ (α d₁ : ℝ) (hd : d₁ ≠ 0) :
    General.Q₃ (α * d₁) d₁ = d₁ ^ 10 * G₃ (1 / d₁ ^ 2) α := by
  rw [General.Q₃_leading_coeff]
  unfold G₃
  field_simp
  ring

/-- Bridge for `detB₃`: at `λ = α·d₁`,
    `detB₃(α d₁, d₁) = α⁶ · G₃(1/d₁², α)`. -/
theorem detB₃_eq_G₃ (α d₁ : ℝ) (hd : d₁ ≠ 0) :
    General.detB₃ (α * d₁) d₁ = α ^ 6 * G₃ (1 / d₁ ^ 2) α := by
  rw [General.detB₃_eq _ _ hd, Q₃_eq_G₃ _ _ hd]
  field_simp

/-- If `G₃(1/d₁², α) = 0` (with `α > 0`), then `α·d₁` is a root of `detB₃`. -/
theorem detB₃_vanishes_of_G₃ (α d₁ : ℝ) (hd : d₁ ≠ 0)
    (hG : G₃ (1 / d₁ ^ 2) α = 0) :
    General.detB₃ (α * d₁) d₁ = 0 := by
  rw [detB₃_eq_G₃ _ _ hd, hG, mul_zero]

-- ═══════════════════════════════════════════════════════════════════
-- §4. Uncurried G₃ and smoothness
-- ═══════════════════════════════════════════════════════════════════

/-- Uncurried form of `G₃` for IFT use. -/
noncomputable def G₃_prod (p : ℝ × ℝ) : ℝ := G₃ p.1 p.2

theorem G₃_prod_contDiff : ContDiff ℝ ⊤ G₃_prod := by
  unfold G₃_prod G₃
  fun_prop

theorem G₃_prod_vanishes_balanced : G₃_prod (0, α₃) = 0 := G₃_vanishes_balanced

/-- Remainder polynomial: `G₃(δ, α) = G₃(0, α) + δ · G₃_R(δ, α)`. -/
noncomputable def G₃_R (δ α : ℝ) : ℝ :=
  α * (6 * α ^ 2 - 15 * α + 4) +
  δ * (- 3 * α ^ 3 + 21 * α ^ 2 - 24 * α + 4) +
  δ ^ 2 * (- 5 * α ^ 2 + 20 * α - 12) +
  δ ^ 3 * (- 2 * α ^ 2 + 12) +
  δ ^ 4 * (- 4)

lemma G₃_split (δ α : ℝ) : G₃ δ α = G₃ 0 α + δ * G₃_R δ α := by
  unfold G₃ G₃_R; ring

/-- At `(0, α₃)`, the remainder evaluates to `G₃_dδ 0 α₃`. -/
lemma G₃_R_at_base : G₃_R 0 α₃ = G₃_dδ 0 α₃ := by
  unfold G₃_R G₃_dδ; ring

/-- Uncurried form of `G₃_R`. -/
noncomputable def G₃_R_prod (p : ℝ × ℝ) : ℝ := G₃_R p.1 p.2

theorem G₃_R_prod_contDiff : ContDiff ℝ ⊤ G₃_R_prod := by
  unfold G₃_R_prod G₃_R
  fun_prop

-- ═══════════════════════════════════════════════════════════════════
-- §5. HasDerivAt wiring
-- ═══════════════════════════════════════════════════════════════════

theorem G₃_hasDerivAt_α (δ α : ℝ) :
    HasDerivAt (fun a => G₃ δ a) (G₃_dα δ α) α := by
  unfold G₃ G₃_dα
  have d1 : HasDerivAt (fun a : ℝ => a ^ 2 * (a ^ 2 - 3 * a + 1))
      (4 * α ^ 3 - 9 * α ^ 2 + 2 * α) α := by
    have hA : HasDerivAt (fun a : ℝ => a ^ 2) (2 * α) α := by
      simpa using hasDerivAt_pow 2 α
    have hB : HasDerivAt (fun a : ℝ => a ^ 2 - 3 * a + 1)
        (2 * α - 3) α := by
      have hA' : HasDerivAt (fun a : ℝ => a ^ 2) (2 * α) α := hA
      have hC : HasDerivAt (fun a : ℝ => (3 : ℝ) * a) 3 α :=
        ((hasDerivAt_id α).const_mul 3).congr_deriv (by ring)
      exact ((hA'.sub hC).add_const 1)
    have hm := hA.mul hB
    convert hm using 1; ring
  have d2 : HasDerivAt (fun a : ℝ => δ * (a * (6 * a ^ 2 - 15 * a + 4)))
      (δ * (18 * α ^ 2 - 30 * α + 4)) α := by
    have hinner : HasDerivAt (fun a : ℝ => a * (6 * a ^ 2 - 15 * a + 4))
        (18 * α ^ 2 - 30 * α + 4) α := by
      have hA : HasDerivAt (fun a : ℝ => a) 1 α := hasDerivAt_id α
      have hsq : HasDerivAt (fun a : ℝ => a ^ 2) (2 * α) α := by
        simpa using hasDerivAt_pow 2 α
      have h6sq : HasDerivAt (fun a : ℝ => (6 : ℝ) * a ^ 2) (12 * α) α :=
        (hsq.const_mul 6).congr_deriv (by ring)
      have h15a : HasDerivAt (fun a : ℝ => (15 : ℝ) * a) 15 α :=
        ((hasDerivAt_id α).const_mul 15).congr_deriv (by ring)
      have hB : HasDerivAt (fun a : ℝ => 6 * a ^ 2 - 15 * a + 4)
          (12 * α - 15) α := ((h6sq.sub h15a).add_const 4)
      have hm := hA.mul hB
      convert hm using 1; ring
    exact hinner.const_mul δ
  have d3 : HasDerivAt (fun a : ℝ => δ ^ 2 * (- 3 * a ^ 3 + 21 * a ^ 2 - 24 * a + 4))
      (δ ^ 2 * (- 9 * α ^ 2 + 42 * α - 24)) α := by
    have hinner : HasDerivAt (fun a : ℝ => - 3 * a ^ 3 + 21 * a ^ 2 - 24 * a + 4)
        (- 9 * α ^ 2 + 42 * α - 24) α := by
      have hcube : HasDerivAt (fun a : ℝ => a ^ 3) (3 * α ^ 2) α := by
        simpa using hasDerivAt_pow 3 α
      have hsq : HasDerivAt (fun a : ℝ => a ^ 2) (2 * α) α := by
        simpa using hasDerivAt_pow 2 α
      have hA : HasDerivAt (fun a : ℝ => (-3 : ℝ) * a ^ 3) (-9 * α ^ 2) α :=
        (hcube.const_mul (-3)).congr_deriv (by ring)
      have hB : HasDerivAt (fun a : ℝ => (21 : ℝ) * a ^ 2) (42 * α) α :=
        (hsq.const_mul 21).congr_deriv (by ring)
      have hC : HasDerivAt (fun a : ℝ => (24 : ℝ) * a) 24 α :=
        ((hasDerivAt_id α).const_mul 24).congr_deriv (by ring)
      exact (((hA.add hB).sub hC).add_const 4)
    exact hinner.const_mul (δ ^ 2)
  have d4 : HasDerivAt (fun a : ℝ => δ ^ 3 * (- 5 * a ^ 2 + 20 * a - 12))
      (δ ^ 3 * (- 10 * α + 20)) α := by
    have hinner : HasDerivAt (fun a : ℝ => - 5 * a ^ 2 + 20 * a - 12)
        (- 10 * α + 20) α := by
      have hsq : HasDerivAt (fun a : ℝ => a ^ 2) (2 * α) α := by
        simpa using hasDerivAt_pow 2 α
      have hA : HasDerivAt (fun a : ℝ => (-5 : ℝ) * a ^ 2) (-10 * α) α :=
        (hsq.const_mul (-5)).congr_deriv (by ring)
      have hB : HasDerivAt (fun a : ℝ => (20 : ℝ) * a) 20 α :=
        ((hasDerivAt_id α).const_mul 20).congr_deriv (by ring)
      exact ((hA.add hB).sub_const 12)
    exact hinner.const_mul (δ ^ 3)
  have d5 : HasDerivAt (fun a : ℝ => δ ^ 4 * (- 2 * a ^ 2 + 12))
      (δ ^ 4 * (- 4 * α)) α := by
    have hinner : HasDerivAt (fun a : ℝ => - 2 * a ^ 2 + 12) (-4 * α) α := by
      have hsq : HasDerivAt (fun a : ℝ => a ^ 2) (2 * α) α := by
        simpa using hasDerivAt_pow 2 α
      have hA : HasDerivAt (fun a : ℝ => (-2 : ℝ) * a ^ 2) (-4 * α) α :=
        (hsq.const_mul (-2)).congr_deriv (by ring)
      exact hA.add_const 12
    exact hinner.const_mul (δ ^ 4)
  have d6 : HasDerivAt (fun (_ : ℝ) => δ ^ 5 * (-4 : ℝ)) 0 α := hasDerivAt_const α _
  have := ((((d1.add d2).add d3).add d4).add d5).add d6
  convert this using 1
  ring

theorem G₃_hasDerivAt_δ (δ α : ℝ) :
    HasDerivAt (fun d => G₃ d α) (G₃_dδ δ α) δ := by
  unfold G₃ G₃_dδ
  have d0 : HasDerivAt (fun (_ : ℝ) => α ^ 2 * (α ^ 2 - 3 * α + 1)) 0 δ :=
    hasDerivAt_const δ _
  have d1 : HasDerivAt (fun d : ℝ => d * (α * (6 * α ^ 2 - 15 * α + 4)))
      (α * (6 * α ^ 2 - 15 * α + 4)) δ := by
    have := (hasDerivAt_id δ).mul_const (α * (6 * α ^ 2 - 15 * α + 4))
    simpa using this
  have d2 : HasDerivAt (fun d : ℝ => d ^ 2 * (- 3 * α ^ 3 + 21 * α ^ 2 - 24 * α + 4))
      (2 * δ * (- 3 * α ^ 3 + 21 * α ^ 2 - 24 * α + 4)) δ := by
    have h := (hasDerivAt_pow 2 δ).mul_const
      (- 3 * α ^ 3 + 21 * α ^ 2 - 24 * α + 4)
    convert h using 1
    simp
  have d3 : HasDerivAt (fun d : ℝ => d ^ 3 * (- 5 * α ^ 2 + 20 * α - 12))
      (3 * δ ^ 2 * (- 5 * α ^ 2 + 20 * α - 12)) δ := by
    have h := (hasDerivAt_pow 3 δ).mul_const (- 5 * α ^ 2 + 20 * α - 12)
    convert h using 1
  have d4 : HasDerivAt (fun d : ℝ => d ^ 4 * (- 2 * α ^ 2 + 12))
      (4 * δ ^ 3 * (- 2 * α ^ 2 + 12)) δ := by
    have h := (hasDerivAt_pow 4 δ).mul_const (- 2 * α ^ 2 + 12)
    convert h using 1
  have d5 : HasDerivAt (fun d : ℝ => d ^ 5 * (-4 : ℝ))
      (5 * δ ^ 4 * (-4)) δ := by
    have h := (hasDerivAt_pow 5 δ).mul_const (-4 : ℝ)
    convert h using 1
  have := (((((d0.add d1).add d2).add d3).add d4).add d5)
  convert this using 1
  ring

-- ═══════════════════════════════════════════════════════════════════
-- §6. Universal first-order coefficient: −1
-- ═══════════════════════════════════════════════════════════════════

/-- **Universality at m = 3.** The implicit-function first-order coefficient
    `−(∂_δ G₃)/(∂_α G₃)` equals `−1` at the base point `(0, α₃)`. -/
theorem first_order_coeff_m3 :
    -(G₃_dδ 0 α₃) / (G₃_dα 0 α₃) = -1 := by
  rw [G₃_dδ_eq_dα]
  have hne : G₃_dα 0 α₃ ≠ 0 := ne_of_gt G₃_dα_pos
  field_simp

-- ═══════════════════════════════════════════════════════════════════
-- §7. Implicit function ψ₃ with ψ₃(0) = α₃, ψ₃'(0) = −1
-- ═══════════════════════════════════════════════════════════════════

theorem ift_m3 :
    ∃ ψ : ℝ → ℝ,
      ψ 0 = α₃ ∧ (∀ᶠ δ in nhds 0, G₃_prod (δ, ψ δ) = 0) ∧
      HasDerivAt ψ (-1) 0 ∧ ContDiffAt ℝ ⊤ ψ 0 := by
  have hG_strict : HasStrictFDerivAt G₃_prod
      (fderiv ℝ G₃_prod (0, α₃)) (0, α₃) :=
    G₃_prod_contDiff.contDiffAt.hasStrictFDerivAt (by simp)
  -- Partial in α at the base: value G₃_dα 0 α₃ > 0.
  have hg : HasDerivAt (fun α₁ => G₃_prod (0, α₁)) (G₃_dα 0 α₃) α₃ := by
    show HasDerivAt (fun α₁ => G₃ 0 α₁) _ _
    exact G₃_hasDerivAt_α 0 α₃
  have hdα_pos := G₃_dα_pos
  have h_inr : HasFDerivAt (fun α₁ : ℝ => ((0:ℝ), α₁)) (.inr ℝ ℝ ℝ) α₃ :=
    (ContinuousLinearMap.inr ℝ ℝ ℝ).hasFDerivAt
  have hcomp : HasFDerivAt (fun α₁ => G₃_prod (0, α₁))
      ((fderiv ℝ G₃_prod (0, α₃)).comp (.inr ℝ ℝ ℝ)) α₃ :=
    hG_strict.hasFDerivAt.comp _ h_inr
  have huniq := hg.hasFDerivAt.unique hcomp
  have hG_inv : ((fderiv ℝ G₃_prod (0, α₃)).comp (.inr ℝ ℝ ℝ)).IsInvertible := by
    rw [← huniq]
    set c := G₃_dα 0 α₃
    have hc_ne : c ≠ 0 := ne_of_gt hdα_pos
    set f := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c
    set g := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c⁻¹
    have hfg : f.comp g = .id ℝ ℝ := by
      ext; simp [f, g, ContinuousLinearMap.smulRight_apply]; field_simp
    have hgf : g.comp f = .id ℝ ℝ := by
      ext; simp [f, g, ContinuousLinearMap.smulRight_apply]; field_simp
    exact ContinuousLinearMap.IsInvertible.of_inverse hfg hgf
  let ψ := hG_strict.implicitFunctionOfProdDomain hG_inv
  have hG_zero : G₃_prod (0, α₃) = 0 := G₃_prod_vanishes_balanced
  refine ⟨ψ, ?_, ?_, ?_, ?_⟩
  · have h := ((hG_strict.eventually_apply_eq_iff_implicitFunctionOfProdDomain
      hG_inv).self_of_nhds.mp rfl).symm
    simpa using h.symm
  · have h := hG_strict.eventually_apply_implicitFunctionOfProdDomain hG_inv
    rwa [hG_zero] at h
  · have hψ0 : ψ 0 = α₃ := by
      have h := ((hG_strict.eventually_apply_eq_iff_implicitFunctionOfProdDomain
        hG_inv).self_of_nhds.mp rfl).symm
      simpa using h.symm
    have h_near : ∀ᶠ δ in nhds 0, G₃_prod (δ, ψ δ) = 0 := by
      have h := hG_strict.eventually_apply_implicitFunctionOfProdDomain hG_inv
      rwa [hG_zero] at h
    have hψ_diff : DifferentiableAt ℝ ψ 0 :=
      (G₃_prod_contDiff.contDiffAt.contDiffAt_implicitFunction
        (by simp) hG_inv).differentiableAt (by norm_num)
    -- Chain rule via the split G₃ δ α = G₃ 0 α + δ · G₃_R δ α.
    -- Part 1: d/dδ [G₃ 0 (ψ δ)] at 0 = G₃_dα 0 α₃ · ψ'(0).
    have h_P : HasDerivAt (fun δ => G₃ 0 (ψ δ)) (G₃_dα 0 α₃ * deriv ψ 0) 0 := by
      have := (G₃_hasDerivAt_α 0 α₃).comp_of_eq 0 hψ_diff.hasDerivAt hψ0.symm
      simpa using this
    -- Part 2: d/dδ [δ · G₃_R δ (ψ δ)] at 0 = G₃_R 0 α₃ = G₃_dδ 0 α₃.
    -- Use DifferentiableAt for the inner factor; the product rule kills its
    -- derivative contribution since `id' = 1` and the id-value at 0 is 0.
    have hR_diff : DifferentiableAt ℝ (fun δ => G₃_R δ (ψ δ)) 0 := by
      have hR_prod : DifferentiableAt ℝ G₃_R_prod (0, ψ 0) :=
        (G₃_R_prod_contDiff.differentiable (by simp)).differentiableAt
      have hid : DifferentiableAt ℝ (fun δ : ℝ => δ) 0 := differentiableAt_id
      have hcurve : DifferentiableAt ℝ (fun δ : ℝ => (δ, ψ δ)) 0 := hid.prodMk hψ_diff
      exact hR_prod.comp 0 hcurve
    have hR_hdAt : HasDerivAt (fun δ => G₃_R δ (ψ δ))
        (deriv (fun δ => G₃_R δ (ψ δ)) 0) 0 := hR_diff.hasDerivAt
    have h_R_prod : HasDerivAt (fun δ => δ * G₃_R δ (ψ δ))
        (G₃_R 0 (ψ 0)) 0 := by
      have := (hasDerivAt_id (0:ℝ)).mul hR_hdAt
      simpa using this
    have h_R_prod' : HasDerivAt (fun δ => δ * G₃_R δ (ψ δ))
        (G₃_dδ 0 α₃) 0 := by
      have := h_R_prod
      rw [hψ0, G₃_R_at_base] at this
      exact this
    -- Combine: HasDerivAt for fun δ => G₃_prod (δ, ψ δ) via G₃_split.
    have h_total_pre : HasDerivAt (fun δ => G₃ 0 (ψ δ) + δ * G₃_R δ (ψ δ))
        (G₃_dα 0 α₃ * deriv ψ 0 + G₃_dδ 0 α₃) 0 := h_P.add h_R_prod'
    have h_total : HasDerivAt (fun δ => G₃_prod (δ, ψ δ))
        (G₃_dα 0 α₃ * deriv ψ 0 + G₃_dδ 0 α₃) 0 := by
      have heq : (fun δ => G₃_prod (δ, ψ δ)) =
          fun δ => G₃ 0 (ψ δ) + δ * G₃_R δ (ψ δ) := by
        funext δ
        show G₃ δ (ψ δ) = G₃ 0 (ψ δ) + δ * G₃_R δ (ψ δ)
        exact G₃_split δ (ψ δ)
      rw [heq]; exact h_total_pre
    have hG_zero_fun : (fun δ => G₃_prod (δ, ψ δ)) =ᶠ[nhds 0] fun _ => (0 : ℝ) :=
      h_near.mono fun δ hδ => hδ
    have h_zero : HasDerivAt (fun δ => G₃_prod (δ, ψ δ)) 0 0 :=
      hG_zero_fun.hasDerivAt_iff.mpr (hasDerivAt_const 0 0)
    have heq := h_total.unique h_zero
    -- G₃_dδ 0 α₃ + G₃_dα 0 α₃ · ψ'(0) = 0, so ψ'(0) = -G₃_dδ/G₃_dα = -1.
    have hψ_val : deriv ψ 0 = -1 := by
      have key : G₃_dα 0 α₃ * deriv ψ 0 = - G₃_dδ 0 α₃ := by linarith
      have hne : G₃_dα 0 α₃ ≠ 0 := ne_of_gt hdα_pos
      have : deriv ψ 0 = - G₃_dδ 0 α₃ / G₃_dα 0 α₃ := by
        field_simp at key ⊢; linarith
      rw [this, G₃_dδ_eq_dα]
      field_simp
    rw [← hψ_val]; exact hψ_diff.hasDerivAt
  · exact G₃_prod_contDiff.contDiffAt.contDiffAt_implicitFunction (by simp) hG_inv

-- ═══════════════════════════════════════════════════════════════════
-- §8. Taylor remainder and physical m = 3 scaling law
-- ═══════════════════════════════════════════════════════════════════

/-- **Physical scaling law at m = 3.**
    There exist `ψ : ℝ → ℝ`, `C, D₀ > 0` such that `ψ(0) = α₃`,
    `ψ'(0) = −1`, and for every `d₁ > D₀`:
    * `detB₃(ψ(1/d₁²) · d₁, d₁) = 0` (physical threshold),
    * `|ψ(1/d₁²) · d₁ − (α₃ · d₁ − 1/d₁)| ≤ C / d₁³` (universal scaling). -/
theorem physical_scaling_m3 :
    ∃ ψ : ℝ → ℝ, ∃ C D₀ : ℝ,
      0 < D₀ ∧ ψ 0 = α₃ ∧
      HasDerivAt ψ (-1) 0 ∧
      (∀ d₁ : ℝ, D₀ < d₁ → General.detB₃ (ψ (1 / d₁ ^ 2) * d₁) d₁ = 0) ∧
      (∀ d₁ : ℝ, D₀ < d₁ →
        |ψ (1 / d₁ ^ 2) * d₁ - (α₃ * d₁ - 1 / d₁)| ≤ C / d₁ ^ 3) := by
  obtain ⟨ψ, hψ0, hψG_eq, hψ_deriv, hψ_smooth⟩ := ift_m3
  -- C² neighbourhood on [0, b] for the Taylor bound
  obtain ⟨U, hU_nhds, hψU⟩ :=
    (hψ_smooth.of_le le_top : ContDiffAt ℝ 2 ψ 0).contDiffOn le_rfl (by simp)
  -- Ball on which G₃(δ, ψ δ) = 0 (from eventually_iff_exists_mem)
  obtain ⟨εG, hεG_pos, hεG_ball⟩ : ∃ εG > 0, ∀ δ : ℝ,
      |δ| < εG → G₃_prod (δ, ψ δ) = 0 := by
    rw [Filter.eventually_iff_exists_mem] at hψG_eq
    obtain ⟨V, hV_nhds, hV⟩ := hψG_eq
    rw [Metric.mem_nhds_iff] at hV_nhds
    obtain ⟨εG, hεG_pos, hεG_sub⟩ := hV_nhds
    refine ⟨εG, hεG_pos, fun δ hδ => hV δ (hεG_sub ?_)⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact hδ
  obtain ⟨b, hb_pos, hb_sub, hb_lt_εG⟩ :
      ∃ b > 0, Set.Icc 0 b ⊆ U ∧ b < εG := by
    rw [mem_nhds_iff] at hU_nhds
    obtain ⟨V, hVU, hV_open, h0V⟩ := hU_nhds
    obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.isOpen_iff.mp hV_open 0 h0V
    refine ⟨min (ε / 2) (εG / 2), by positivity, ?_, ?_⟩
    · intro x hx
      apply hVU
      apply hε_ball
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
      refine ⟨?_, ?_⟩
      · have := hx.1
        have := hx.2
        have hm : min (ε / 2) (εG / 2) ≤ ε / 2 := min_le_left _ _
        linarith
      · have := hx.2
        have hm : min (ε / 2) (εG / 2) ≤ ε / 2 := min_le_left _ _
        linarith
    · have hm : min (ε / 2) (εG / 2) ≤ εG / 2 := min_le_right _ _
      linarith
  have hψ_c2 : ContDiffOn ℝ 2 ψ (Set.Icc 0 b) := hψU.mono hb_sub
  obtain ⟨C₀, hC₀⟩ := exists_taylor_mean_remainder_bound (le_of_lt hb_pos) hψ_c2
  have hψ_within : derivWithin ψ (Set.Icc 0 b) 0 = -1 := by
    rw [DifferentiableAt.derivWithin hψ_deriv.differentiableAt
        (uniqueDiffOn_Icc hb_pos 0 (Set.left_mem_Icc.mpr (le_of_lt hb_pos)))]
    exact hψ_deriv.deriv
  have hTaylor_eq : ∀ x, taylorWithinEval ψ 1 (Set.Icc 0 b) 0 x = α₃ - x := by
    intro x
    rw [taylorWithinEval_succ]
    simp only [taylor_within_zero_eval, Nat.zero_add, Nat.cast_one,
      Nat.factorial_zero, Nat.cast_one, sub_zero, pow_one, iteratedDerivWithin_one]
    rw [hψ0, hψ_within]
    simp [smul_eq_mul]
    ring
  set D₀ := Real.sqrt (1 / b)
  have hD₀_pos : 0 < D₀ := Real.sqrt_pos.mpr (by positivity)
  have hD₀_sq : D₀ ^ 2 = 1 / b := by
    show Real.sqrt (1 / b) ^ 2 = 1 / b
    rw [sq, Real.mul_self_sqrt (by positivity)]
  refine ⟨ψ, C₀, D₀, hD₀_pos, hψ0, hψ_deriv, ?_, ?_⟩
  · -- Bridge back: detB₃ = 0.
    intro d₁ hd₁
    have hd₁_pos : 0 < d₁ := lt_trans hD₀_pos hd₁
    have hd₁_ne : d₁ ≠ 0 := ne_of_gt hd₁_pos
    have hδ_pos : (0:ℝ) < 1 / d₁ ^ 2 := by positivity
    have hδ_lt_b : 1 / d₁ ^ 2 ≤ b := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < d₁ ^ 2)]
      have : 1 / b < d₁ ^ 2 := by nlinarith [hD₀_sq]
      rw [div_lt_iff₀ hb_pos] at this; linarith
    have hδ_lt_εG : |1 / d₁ ^ 2| < εG := by
      rw [abs_of_pos hδ_pos]
      linarith
    have hG : G₃_prod (1 / d₁ ^ 2, ψ (1 / d₁ ^ 2)) = 0 := hεG_ball _ hδ_lt_εG
    have hGG : G₃ (1 / d₁ ^ 2) (ψ (1 / d₁ ^ 2)) = 0 := hG
    exact detB₃_vanishes_of_G₃ (ψ (1 / d₁ ^ 2)) d₁ hd₁_ne hGG
  · -- Taylor bound: |ψ(δ)·d₁ − (α₃·d₁ − 1/d₁)| ≤ C₀/d₁³.
    intro d₁ hd₁
    have hd₁_pos : 0 < d₁ := lt_trans hD₀_pos hd₁
    set δ := 1 / d₁ ^ 2 with hδ_def
    have hδ_pos : 0 < δ := by positivity
    have hδ_le_b : δ ≤ b := by
      show 1 / d₁ ^ 2 ≤ b
      rw [div_le_iff₀ (by positivity : (0:ℝ) < d₁ ^ 2)]
      have : 1 / b < d₁ ^ 2 := by nlinarith [hD₀_sq]
      rw [div_lt_iff₀ hb_pos] at this; linarith
    have hδ_mem : δ ∈ Set.Icc 0 b := ⟨le_of_lt hδ_pos, hδ_le_b⟩
    have hTaylor_bound := hC₀ δ hδ_mem
    rw [hTaylor_eq, show δ - 0 = δ from sub_zero δ] at hTaylor_bound
    simp only [Real.norm_eq_abs] at hTaylor_bound
    -- hTaylor_bound : |ψ δ - (α₃ - δ)| ≤ C₀ * (δ ^ (1+1))  (from the Taylor API)
    -- Convert the right-hand side to C₀ * (δ * δ) so we can simplify.
    have hδ_sq_eq : δ ^ (1 + 1) = δ * δ := by ring
    rw [hδ_sq_eq] at hTaylor_bound
    -- δ = 1/d₁², so δ·δ = 1/d₁⁴; multiplying by d₁ gives 1/d₁³.
    have halg : ψ (1 / d₁ ^ 2) * d₁ - (α₃ * d₁ - 1 / d₁) =
        (ψ δ - (α₃ - δ)) * d₁ := by
      show ψ (1 / d₁ ^ 2) * d₁ - (α₃ * d₁ - 1 / d₁) =
        (ψ (1 / d₁ ^ 2) - (α₃ - 1 / d₁ ^ 2)) * d₁
      field_simp
    rw [halg, abs_mul, abs_of_pos hd₁_pos]
    have hfinal : C₀ * (δ * δ) * d₁ = C₀ / d₁ ^ 3 := by
      show C₀ * (1 / d₁ ^ 2 * (1 / d₁ ^ 2)) * d₁ = C₀ / d₁ ^ 3
      have hd_ne : d₁ ≠ 0 := ne_of_gt hd₁_pos
      field_simp
    nlinarith [hTaylor_bound]

end PhysicalThresholdM3
