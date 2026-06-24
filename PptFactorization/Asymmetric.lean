import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Asymmetric regime: exact p₃-PPT threshold

## Main result

For `d₁ > 0` and `λ > 0`, the asymmetric p₃-PPT Hankel determinant is

    det B₁(λ, d₁) = λ²(d₁ λ − d₁² + 1) / d₁⁴

and hence the exact threshold is `λ*₁(d₁) = d₁ − 1/d₁`.

## Correct asymmetric moments

The moments sum over NC_{γ⁻¹}(k), which for k ≤ 3 comprises NC≤2(k)
plus the full-cycle (1 2 3) at k = 3.  The cycle-count exponents
`#(γ⁻¹π)` are:
- identity: 1  (all k)
- transpositions in k = 2, 3: 2
- 3-cycle (1 2 3) in k = 3: 1

Using the exponent `d₁^{#(γ⁻¹π) − k − 1}` (s = λ d₂ parametrisation):

    c₁(λ, d₁) = λ / d₁
    c₂(λ, d₁) = (λ² + λ d₁) / d₁²
    c₃(λ, d₁) = (λ³ + 3 λ² d₁ + λ) / d₁³

The extra `+λ` in c₃ comes from π = (1 2 3) ∈ NC_{γ⁻¹}(3) \ NC≤2(3).

Institut Fourier, Grenoble — Kieran McShane / Cécilia Lancien
-/

open Real

namespace Asymmetric

variable (lam d₁ : ℝ)

-- ═══════════════════════════════════════════════════════════════════
-- §1. Asymmetric moment coefficients (k ≤ 3)
-- ═══════════════════════════════════════════════════════════════════

/-- Asymmetric `c₁(λ, d₁) = λ / d₁`.
    NC_{γ⁻¹}(1) = {e}: #(γ⁻¹e) = 1, exponent = 1 − 2 = −1. -/
noncomputable def c₁ : ℝ := lam / d₁

/-- Asymmetric `c₂(λ, d₁) = (λ² + λ d₁) / d₁²`.
    NC_{γ⁻¹}(2) = {e, (12)}.
    e: #(γ⁻¹e) = 1, exponent −2 → λ²/d₁².
    (12): #(γ⁻¹(12)) = 2, exponent −1 → λ/d₁. -/
noncomputable def c₂ : ℝ := (lam ^ 2 + lam * d₁) / d₁ ^ 2

/-- Asymmetric `c₃(λ, d₁) = (λ³ + 3λ²d₁ + λ) / d₁³`.
    NC_{γ⁻¹}(3) = {e, (12), (23), (13), (123)}.
    e: #(γ⁻¹e) = 1, exponent −3 → λ³/d₁³.
    (12),(23),(13): #(γ⁻¹π) = 2, exponent −2 → λ²/d₁² each.
    (123): #(γ⁻¹(123)) = 1, exponent −3 → λ/d₁³. -/
noncomputable def c₃ : ℝ := (lam ^ 3 + 3 * lam ^ 2 * d₁ + lam) / d₁ ^ 3

-- ═══════════════════════════════════════════════════════════════════
-- §2. The 2×2 Hankel determinant
-- ═══════════════════════════════════════════════════════════════════

/-- The asymmetric p₃-PPT Hankel determinant:
    `det B₁(λ, d₁) = c₁ · c₃ − c₂²`. -/
noncomputable def detB₁ : ℝ := c₁ lam d₁ * c₃ lam d₁ - c₂ lam d₁ ^ 2

-- ═══════════════════════════════════════════════════════════════════
-- §3. Closed-form factorization
-- ═══════════════════════════════════════════════════════════════════

/-- **Key identity.** `det B₁(λ, d₁) = λ²(d₁ λ − d₁² + 1) / d₁⁴`.
    Pure algebra: expand and simplify. -/
theorem detB₁_eq (hd : d₁ ≠ 0) :
    detB₁ lam d₁ = lam ^ 2 * (d₁ * lam - d₁ ^ 2 + 1) / d₁ ^ 4 := by
  simp only [detB₁, c₁, c₂, c₃]
  field_simp
  ring

-- ═══════════════════════════════════════════════════════════════════
-- §4. Threshold characterization
-- ═══════════════════════════════════════════════════════════════════

/-- `det B₁ = 0` at `λ = d₁ − 1/d₁` (and at `λ = 0`). -/
theorem detB₁_vanishes_at_threshold (hd : d₁ ≠ 0) :
    detB₁ (d₁ - 1 / d₁) d₁ = 0 := by
  rw [detB₁_eq _ _ hd]
  field_simp
  ring

/-- `det B₁ > 0` for `λ > d₁ − 1/d₁` and `λ > 0`. -/
theorem detB₁_pos_above (hd : 0 < d₁) (hlam : 0 < lam)
    (hgt : d₁ - 1 / d₁ < lam) :
    0 < detB₁ lam d₁ := by
  rw [detB₁_eq lam d₁ (ne_of_gt hd)]
  apply div_pos
  · apply mul_pos
    · exact pow_pos hlam 2
    · have h : d₁ * lam > d₁ ^ 2 - 1 := by
        rw [gt_iff_lt, ← sub_pos]
        have := mul_lt_mul_of_pos_left hgt hd
        rw [mul_sub, mul_div_cancel₀ _ (ne_of_gt hd)] at this
        linarith
      linarith
  · exact pow_pos hd 4

/-- `det B₁ < 0` for `0 < λ < d₁ − 1/d₁` (and `d₁ > 1`). -/
theorem detB₁_neg_below (hd : 1 < d₁) (hlam : 0 < lam)
    (hlt : lam < d₁ - 1 / d₁) :
    detB₁ lam d₁ < 0 := by
  have hd0 : (0 : ℝ) < d₁ := by linarith
  rw [detB₁_eq lam d₁ (ne_of_gt hd0)]
  apply div_neg_of_neg_of_pos
  · apply mul_neg_of_pos_of_neg
    · exact pow_pos hlam 2
    · have h : d₁ * lam < d₁ ^ 2 - 1 := by
        rw [← sub_pos]
        have := mul_lt_mul_of_pos_left hlt hd0
        rw [mul_sub, mul_div_cancel₀ _ (ne_of_gt hd0)] at this
        linarith
      linarith
  · exact pow_pos hd0 4

-- ═══════════════════════════════════════════════════════════════════
-- §5. Slope = Jones threshold α₁ = 4cos²(π/3) = 1
-- ═══════════════════════════════════════════════════════════════════

/-- As `d₁ → ∞`, `λ*₁(d₁)/d₁ → 1 = 4cos²(π/3)`.
    More precisely: `λ*₁(d₁) = d₁ − 1/d₁ = 1 · d₁ − 1/d₁`. -/
theorem threshold_slope (hd : d₁ ≠ 0) :
    (d₁ - 1 / d₁) / d₁ = 1 - 1 / d₁ ^ 2 := by
  field_simp

/-- The correction `−1/d₁` is universal (same for all m).
    Here we verify it for m = 1: the threshold is `d₁ − 1/d₁ = α₁ · d₁ − 1/d₁`
    with `α₁ = 1`. -/
theorem threshold_decomposition :
    d₁ - 1 / d₁ = 1 * d₁ - 1 / d₁ := by ring

end Asymmetric
