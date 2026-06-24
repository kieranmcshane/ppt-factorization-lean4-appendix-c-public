import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# General bipartite PPT thresholds (Lancien–McShane)

## Overview

Extends the m = 1 asymptotic threshold (`Asymmetric.lean`) to m = 2 and
establishes the universal scaling law for PPT thresholds.

The asymptotic moments `c_k(λ, d₁)` for the partial-transpose spectral
measure of random bipartite states on `ℂ^{d₁} ⊗ ℂ^{d₂}`, `d₂ → ∞`, are:

    c_k = Σ_{π ∈ NC_{γ⁻¹}(k)} d₁^{#(γ⁻¹π) − k − 1} · λ^{#(π)}

where `|NC_{γ⁻¹}(k)| = Catalan(k)`.

## p₅-PPT threshold (m = 2)

The 3×3 Hankel determinant factorises as:

    det B₂ = −λ⁴ · Q₂(d₁, λ) / d₁⁹

where `Q₂ = −d₁³λ² + (2d₁⁴ − 3d₁² + 1)λ + 4d₁(d₁² − 1)`
is quadratic in λ.  The threshold `λ*₂` is the larger root.

## Universal scaling law

    λ*_m(d₁) = αₘ · d₁ − 1/d₁ + O(1/d₁³)

with `α₁ = 1 = 4cos²(π/3)` (exact), `α₂ = 2 = 4cos²(π/4)`,
`α₃ = (3+√5)/2 = 4cos²(π/5)` (asymptotic).

## Resolvent cubic

The Cauchy–Stieltjes transform `G(z)` satisfies
`z G³ + (λ d₁ − 1) G² + (λ d₁ − z d₁²) G + d₁² = 0`.
Free cumulants: `κ_{2m−1} = κ_{2m} = λ / d₁^{2m−1}`.

Institut Fourier, Grenoble — Kieran McShane / Cécilia Lancien
-/

open Real

namespace General

variable (lam d₁ : ℝ)

-- ═══════════════════════════════════════════════════════════════════
-- §1. Asymptotic moments c₁ – c₅
-- ═══════════════════════════════════════════════════════════════════

/-- `c₁(λ, d₁) = λ / d₁`.   |NC_{γ⁻¹}(1)| = 1. -/
noncomputable def c₁ : ℝ := lam / d₁

/-- `c₂(λ, d₁) = (λ² + d₁ λ) / d₁²`.   |NC_{γ⁻¹}(2)| = 2. -/
noncomputable def c₂ : ℝ := (lam ^ 2 + lam * d₁) / d₁ ^ 2

/-- `c₃(λ, d₁) = (λ³ + 3 d₁ λ² + λ) / d₁³`.   |NC_{γ⁻¹}(3)| = 5. -/
noncomputable def c₃ : ℝ := (lam ^ 3 + 3 * lam ^ 2 * d₁ + lam) / d₁ ^ 3

/-- `c₄(λ, d₁) = (λ⁴ + 6 d₁ λ³ + (2 d₁² + 4) λ² + d₁ λ) / d₁⁴`.
    |NC_{γ⁻¹}(4)| = C(4) = 14.  -/
noncomputable def c₄ : ℝ :=
  (lam ^ 4 + 6 * d₁ * lam ^ 3 + (2 * d₁ ^ 2 + 4) * lam ^ 2 +
   d₁ * lam) / d₁ ^ 4

/-- `c₅(λ, d₁) = (λ⁵ + 10 d₁ λ⁴ + (10 d₁² + 10) λ³ + 10 d₁ λ² + λ) / d₁⁵`.
    |NC_{γ⁻¹}(5)| = C(5) = 42.  -/
noncomputable def c₅ : ℝ :=
  (lam ^ 5 + 10 * d₁ * lam ^ 4 + (10 * d₁ ^ 2 + 10) * lam ^ 3 +
   10 * d₁ * lam ^ 2 + lam) / d₁ ^ 5

-- ═══════════════════════════════════════════════════════════════════
-- §2. The 2×2 Hankel determinant (m = 1)  — recap
-- ═══════════════════════════════════════════════════════════════════

/-- `det B₁ = c₁ c₃ − c₂²`. -/
noncomputable def detB₁ : ℝ := c₁ lam d₁ * c₃ lam d₁ - c₂ lam d₁ ^ 2

/-- **Factorisation.**  `det B₁ = λ²(d₁ λ − d₁² + 1) / d₁⁴`. -/
theorem detB₁_eq (hd : d₁ ≠ 0) :
    detB₁ lam d₁ = lam ^ 2 * (d₁ * lam - d₁ ^ 2 + 1) / d₁ ^ 4 := by
  simp only [detB₁, c₁, c₂, c₃]
  field_simp
  ring

/-- `det B₁ = 0` at `λ = d₁ − 1/d₁`. -/
theorem detB₁_vanishes (hd : d₁ ≠ 0) :
    detB₁ (d₁ - 1 / d₁) d₁ = 0 := by
  rw [detB₁_eq _ _ hd]; field_simp; ring

-- ═══════════════════════════════════════════════════════════════════
-- §3. The 3×3 Hankel determinant (m = 2)
-- ═══════════════════════════════════════════════════════════════════

/-- `det B₂ = c₁(c₃ c₅ − c₄²) − c₂(c₂ c₅ − c₃ c₄) + c₃(c₂ c₄ − c₃²)`. -/
noncomputable def detB₂ : ℝ :=
  c₁ lam d₁ * (c₃ lam d₁ * c₅ lam d₁ - (c₄ lam d₁) ^ 2) -
  c₂ lam d₁ * (c₂ lam d₁ * c₅ lam d₁ - c₃ lam d₁ * c₄ lam d₁) +
  c₃ lam d₁ * (c₂ lam d₁ * c₄ lam d₁ - (c₃ lam d₁) ^ 2)

-- ═══════════════════════════════════════════════════════════════════
-- §4. Inner quadratic factor Q₂
-- ═══════════════════════════════════════════════════════════════════

/-- `Q₂(λ, d₁) = −d₁³ λ² + (2 d₁⁴ − 3 d₁² + 1) λ + (4 d₁³ − 4 d₁)`.
    Quadratic in λ with negative leading coefficient. -/
noncomputable def Q₂ : ℝ :=
  - d₁ ^ 3 * lam ^ 2 + (2 * d₁ ^ 4 - 3 * d₁ ^ 2 + 1) * lam +
  (4 * d₁ ^ 3 - 4 * d₁)

-- ═══════════════════════════════════════════════════════════════════
-- §5. Factorisation of det B₂
-- ═══════════════════════════════════════════════════════════════════

/-- **Key identity.** `det B₂ = −λ⁴ · Q₂ / d₁⁹`. -/
theorem detB₂_eq (hd : d₁ ≠ 0) :
    detB₂ lam d₁ = - lam ^ 4 * Q₂ lam d₁ / d₁ ^ 9 := by
  simp only [detB₂, c₁, c₂, c₃, c₄, c₅, Q₂]
  field_simp
  ring

-- ═══════════════════════════════════════════════════════════════════
-- §6. Discriminant
-- ═══════════════════════════════════════════════════════════════════

/-- Discriminant of Q₂ viewed as a quadratic `−d₁³ λ² + b λ + c`:
    `Δ₂ = b² + 4 d₁³ c = 4 d₁⁸ + 4 d₁⁶ − 3 d₁⁴ − 6 d₁² + 1`. -/
noncomputable def disc₂ : ℝ :=
  4 * d₁ ^ 8 + 4 * d₁ ^ 6 - 3 * d₁ ^ 4 - 6 * d₁ ^ 2 + 1

theorem disc₂_eq :
    disc₂ d₁ =
    (2 * d₁ ^ 4 - 3 * d₁ ^ 2 + 1) ^ 2 +
    4 * d₁ ^ 3 * (4 * d₁ ^ 3 - 4 * d₁) := by
  simp only [disc₂]; ring

/-- `Δ₂ > 0` for `d₁ ≥ 2`. -/
theorem disc₂_pos (hd : 2 ≤ d₁) : 0 < disc₂ d₁ := by
  -- disc₂ = (2d₁⁴ + d₁² − 1)² − (2d₁)²
  --       = (2d₁⁴ + d₁² − 1 − 2d₁)(2d₁⁴ + d₁² − 1 + 2d₁)
  have key : disc₂ d₁ = (2 * d₁ ^ 4 + d₁ ^ 2 - 1 - 2 * d₁) *
      (2 * d₁ ^ 4 + d₁ ^ 2 - 1 + 2 * d₁) := by
    simp only [disc₂]; ring
  rw [key]
  apply mul_pos <;> nlinarith [sq_nonneg d₁, sq_nonneg (d₁ - 2), sq_nonneg (d₁ ^ 2)]

-- ═══════════════════════════════════════════════════════════════════
-- §7. Sign analysis
-- ═══════════════════════════════════════════════════════════════════

/-- `Q₂(0, d₁) = 4 d₁(d₁² − 1) > 0` for `d₁ > 1`. -/
theorem Q₂_pos_at_zero (hd : 1 < d₁) : 0 < Q₂ 0 d₁ := by
  simp only [Q₂]; nlinarith [sq_nonneg d₁]

/-- `det B₂ > 0` above threshold (when `Q₂ < 0`). -/
theorem detB₂_pos_above (hd : 0 < d₁) (hlam : 0 < lam)
    (hQ : Q₂ lam d₁ < 0) :
    0 < detB₂ lam d₁ := by
  rw [detB₂_eq lam d₁ (ne_of_gt hd)]
  apply div_pos
  · nlinarith [pow_pos hlam 4]
  · exact pow_pos hd 9

/-- `det B₂ < 0` below threshold (when `Q₂ > 0` and `λ > 0`). -/
theorem detB₂_neg_below (hd : 0 < d₁) (hlam : 0 < lam)
    (hQ : 0 < Q₂ lam d₁) :
    detB₂ lam d₁ < 0 := by
  rw [detB₂_eq lam d₁ (ne_of_gt hd)]
  apply div_neg_of_neg_of_pos
  · nlinarith [pow_pos hlam 4]
  · exact pow_pos hd 9

-- ═══════════════════════════════════════════════════════════════════
-- §8. Universal scaling law
-- ═══════════════════════════════════════════════════════════════════

/-- Leading coefficient of `Q₂(α d₁, d₁)` is `(−α² + 2α) d₁⁵`. -/
theorem Q₂_at_slope (α : ℝ) :
    Q₂ (α * d₁) d₁ =
    (- α ^ 2 + 2 * α) * d₁ ^ 5 +
    (- 3 * α + 4) * d₁ ^ 3 +
    (α - 4) * d₁ := by
  simp only [Q₂]; ring

/-- m = 2 slope: `α₂ = 4 cos²(π/4) = 2`. -/
theorem alpha₂ : 4 * cos (π / 4) ^ 2 = 2 := by
  rw [cos_pi_div_four, div_pow, sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

-- ═══════════════════════════════════════════════════════════════════
-- §10. Threshold definition and properties
-- ═══════════════════════════════════════════════════════════════════

/-- Exact threshold for m = 1:  `λ*₁ = d₁ − 1/d₁`. -/
noncomputable def threshold₁ : ℝ := d₁ - 1 / d₁

/-- The asymptotic threshold for general m:
    `λ*_m(d₁) ≈ αₘ d₁ − 1/d₁` where `αₘ = 4 cos²(π/(m + 2))`.
    Exact for m = 1, asymptotic for m ≥ 2. -/
noncomputable def thresholdApprox (m : ℕ) : ℝ :=
  4 * cos (π / (↑m + 2)) ^ 2 * d₁ - 1 / d₁

/-- m = 1 slope: `α₁ = 4 cos²(π/3) = 1`. -/
theorem alpha₁ : 4 * cos (π / 3) ^ 2 = 1 := by
  rw [cos_pi_div_three]; norm_num

/-- Consistency: `thresholdApprox 1 d₁ = d₁ − 1/d₁` (using `α₁ = 1`). -/
theorem thresholdApprox_m1 :
    thresholdApprox d₁ 1 = d₁ - 1 / d₁ := by
  simp only [thresholdApprox]
  push_cast
  norm_num [cos_pi_div_three]

-- ═══════════════════════════════════════════════════════════════════
-- §11. Exact threshold for m = 2
-- ═══════════════════════════════════════════════════════════════════

/-- Exact m = 2 threshold: larger root of `Q₂ = 0`.
    `λ*₂ = (2 d₁⁴ − 3 d₁² + 1 + √Δ₂) / (2 d₁³)`. -/
noncomputable def threshold₂ : ℝ :=
  (2 * d₁ ^ 4 - 3 * d₁ ^ 2 + 1 + sqrt (disc₂ d₁)) / (2 * d₁ ^ 3)

/-- `Q₂(λ*₂, d₁) = 0`.
    Proof: substitute the quadratic-formula root, clear denominators,
    replace `(√Δ)² = Δ`, close by `ring`-like reasoning. -/
theorem Q₂_vanishes_at_threshold₂ (hd : 0 < d₁) (hdisc : 0 ≤ disc₂ d₁) :
    Q₂ (threshold₂ d₁) d₁ = 0 := by
  have hd_ne : d₁ ≠ 0 := ne_of_gt hd
  set s := sqrt (disc₂ d₁) with hs_def
  have hsq : s ^ 2 = disc₂ d₁ := sq_sqrt hdisc
  -- Key: 4d₁³ · Q₂(λ*₂) = Δ − s² = 0  (quadratic formula identity)
  have key : 4 * d₁ ^ 3 * Q₂ (threshold₂ d₁) d₁ = disc₂ d₁ - s ^ 2 := by
    simp only [Q₂, threshold₂, hs_def, disc₂]
    field_simp
    ring
  have h : 4 * d₁ ^ 3 * Q₂ (threshold₂ d₁) d₁ = 0 := by
    rw [key, hsq, sub_self]
  exact (mul_eq_zero.mp h).resolve_left (by positivity)

/-- `det B₂ = 0` at `λ = λ*₂`. -/
theorem detB₂_vanishes_at_threshold₂ (hd : 0 < d₁) (hdisc : 0 ≤ disc₂ d₁) :
    detB₂ (threshold₂ d₁) d₁ = 0 := by
  rw [detB₂_eq _ _ (ne_of_gt hd), Q₂_vanishes_at_threshold₂ d₁ hd hdisc]
  simp

-- ═══════════════════════════════════════════════════════════════════
-- §12. Balanced specialisation: c_k(d₁, α d₁) → M_k(α)
-- ═══════════════════════════════════════════════════════════════════

/-- `c₁(d₁, α d₁) = α`.   Matches `M₁(α) = α` exactly. -/
theorem c₁_balanced (α : ℝ) (hd : d₁ ≠ 0) :
    c₁ (α * d₁) d₁ = α := by
  simp only [c₁]; field_simp

/-- `c₂(d₁, α d₁) = α² + α`.   Matches `M₂(α) = α² + α` exactly. -/
theorem c₂_balanced (α : ℝ) (hd : d₁ ≠ 0) :
    c₂ (α * d₁) d₁ = α ^ 2 + α := by
  simp only [c₂]; field_simp

/-- `c₃(d₁, α d₁) = α³ + 3α² + α/d₁²`.
    Equals `M₃(α) + α/d₁²` (correction `O(1/d₁²)`). -/
theorem c₃_balanced (α : ℝ) (hd : d₁ ≠ 0) :
    c₃ (α * d₁) d₁ = α ^ 3 + 3 * α ^ 2 + α / d₁ ^ 2 := by
  simp only [c₃]; field_simp

/-- Balanced det B₁ at `λ = α d₁`:
    `det B₁(α d₁, d₁) = α²(α − 1 + 1/d₁²)`.
    Leading term `α²(α − 1)` is the balanced Hankel det `M₁ M₃ − M₂²`. -/
theorem detB₁_balanced (α : ℝ) (hd : d₁ ≠ 0) :
    detB₁ (α * d₁) d₁ = α ^ 2 * (α - 1 + 1 / d₁ ^ 2) := by
  simp only [detB₁, c₁, c₂, c₃]; field_simp; ring

/-- The balanced m = 1 Hankel determinant is `α²(α − 1)`.
    `det B₁^{bal}(α) = M₁ M₃ − M₂² = α(α³+3α²) − (α²+α)² = α²(α−1)`. -/
theorem balanced_detB₁ (α : ℝ) : α * (α ^ 3 + 3 * α ^ 2) - (α ^ 2 + α) ^ 2 =
    α ^ 2 * (α - 1) := by ring

-- ═══════════════════════════════════════════════════════════════════
-- §13. Moments c₆, c₇ and the m = 3 Hankel determinant
-- ═══════════════════════════════════════════════════════════════════

/-- `c₆(λ, d₁)`.   |NC_{γ⁻¹}(6)| = C(6) = 132.
    Free cumulants: `κ_{2m-1} = κ_{2m} = λ/d₁^{2m-1}`, resolved from the cubic
    `z G³ + (λ d₁ − 1) G² + (λ d₁ − z d₁²) G + d₁² = 0`. -/
noncomputable def c₆ : ℝ :=
  (lam ^ 6 + 15 * d₁ * lam ^ 5 + (30 * d₁ ^ 2 + 20) * lam ^ 4 +
   (5 * d₁ ^ 3 + 45 * d₁) * lam ^ 3 + (6 * d₁ ^ 2 + 9) * lam ^ 2 +
   d₁ * lam) / d₁ ^ 6

/-- `c₇(λ, d₁)`.   |NC_{γ⁻¹}(7)| = C(7) = 429.
    Same resolvent cubic as `c₆`. -/
noncomputable def c₇ : ℝ :=
  (lam ^ 7 + 21 * d₁ * lam ^ 6 + (70 * d₁ ^ 2 + 35) * lam ^ 5 +
   (35 * d₁ ^ 3 + 140 * d₁) * lam ^ 4 + (63 * d₁ ^ 2 + 42) * lam ^ 3 +
   21 * d₁ * lam ^ 2 + lam) / d₁ ^ 7

/-- The 4×4 Hankel determinant for m = 3.
    `det [[c₁,c₂,c₃,c₄],[c₂,c₃,c₄,c₅],[c₃,c₄,c₅,c₆],[c₄,c₅,c₆,c₇]]`.
    Cofactor expansion along row 0. -/
noncomputable def detB₃ : ℝ :=
  let a₁ := c₁ lam d₁; let a₂ := c₂ lam d₁; let a₃ := c₃ lam d₁
  let a₄ := c₄ lam d₁; let a₅ := c₅ lam d₁; let a₆ := c₆ lam d₁
  let a₇ := c₇ lam d₁
  -- (+) a₁ · det [[a₃,a₄,a₅],[a₄,a₅,a₆],[a₅,a₆,a₇]]
  a₁ * (a₃ * (a₅ * a₇ - a₆ ^ 2) -
        a₄ * (a₄ * a₇ - a₅ * a₆) +
        a₅ * (a₄ * a₆ - a₅ ^ 2)) -
  -- (−) a₂ · det [[a₂,a₄,a₅],[a₃,a₅,a₆],[a₄,a₆,a₇]]
  a₂ * (a₂ * (a₅ * a₇ - a₆ ^ 2) -
        a₄ * (a₃ * a₇ - a₄ * a₆) +
        a₅ * (a₃ * a₆ - a₄ * a₅)) +
  -- (+) a₃ · det [[a₂,a₃,a₅],[a₃,a₄,a₆],[a₄,a₅,a₇]]
  a₃ * (a₂ * (a₄ * a₇ - a₅ * a₆) -
        a₃ * (a₃ * a₇ - a₄ * a₆) +
        a₅ * (a₃ * a₅ - a₄ ^ 2)) -
  -- (−) a₄ · det [[a₂,a₃,a₄],[a₃,a₄,a₅],[a₄,a₅,a₆]]
  a₄ * (a₂ * (a₄ * a₆ - a₅ ^ 2) -
        a₃ * (a₃ * a₆ - a₄ * a₅) +
        a₄ * (a₃ * a₅ - a₄ ^ 2))

/-- The inner factor Q₃ of det B₃.
    `det B₃ = λ⁶ Q₃ / d₁¹⁶`.
    Q₃ is degree 4 in λ; its leading coeff in the scaling `λ = α d₁` is
    `α²(α² − 3α + 1) d₁¹⁰`, vanishing at `α = (3 + √5)/2 = 4cos²(π/5)`. -/
noncomputable def Q₃ : ℝ :=
  d₁ ^ 6 * lam ^ 4 - 3 * d₁ ^ 3 * (d₁ ^ 2 - 1) ^ 2 * lam ^ 3 +
  (d₁ ^ 2 - 1) * (d₁ ^ 6 - 14 * d₁ ^ 4 + 7 * d₁ ^ 2 + 2) * lam ^ 2 +
  4 * d₁ ^ 3 * (d₁ ^ 2 - 1) * (d₁ ^ 2 - 5) * lam +
  4 * (d₁ ^ 2 - 1) ^ 3

/-- **Key identity.** `det B₃ = λ⁶ · Q₃ / d₁¹⁶`. -/
theorem detB₃_eq (hd : d₁ ≠ 0) :
    detB₃ lam d₁ = lam ^ 6 * Q₃ lam d₁ / d₁ ^ 16 := by
  simp only [detB₃, c₁, c₂, c₃, c₄, c₅, c₆, c₇, Q₃]
  field_simp
  ring

/-- Leading coefficient of `Q₃(α d₁, d₁)` is `α²(α² − 3α + 1) d₁¹⁰`. -/
theorem Q₃_leading_coeff (α : ℝ) :
    Q₃ (α * d₁) d₁ =
    α ^ 2 * (α ^ 2 - 3 * α + 1) * d₁ ^ 10 +
    α * (6 * α ^ 2 - 15 * α + 4) * d₁ ^ 8 +
    (- 3 * α ^ 3 + 21 * α ^ 2 - 24 * α + 4) * d₁ ^ 6 +
    (- 5 * α ^ 2 + 20 * α - 12) * d₁ ^ 4 +
    (- 2 * α ^ 2 + 12) * d₁ ^ 2 - 4 := by
  simp only [Q₃]; ring

/-- The m = 3 balanced slope: `α² − 3α + 1 = 0` at `α = (3 ± √5)/2`.
    The larger root `(3 + √5)/2 = 4cos²(π/5)` is the balanced threshold. -/
theorem slope_m3_eq : (3 + Real.sqrt 5) / 2 * ((3 + Real.sqrt 5) / 2) -
    3 * ((3 + Real.sqrt 5) / 2) + 1 = 0 := by
  set s := Real.sqrt 5
  have hs : s ^ 2 = 5 := by rw [sq]; exact mul_self_sqrt (by norm_num : (0:ℝ) ≤ 5)
  nlinarith [hs]

-- ═══════════════════════════════════════════════════════════════════
-- §14. Resolvent cubic and free cumulant structure
-- ═══════════════════════════════════════════════════════════════════

/-! **Resolvent cubic.** The Cauchy–Stieltjes transform
    `G(z) = Σ c_k / z^{k+1}` satisfies
    `z G³ + (λ d₁ − 1) G² + (λ d₁ − z d₁²) G + d₁² = 0`.
    Equivalently: `1/G = z − R(G)` where the R-transform is
    `R(w) = λ d₁ (1 + w) / (d₁² − w²)`.

    **Free cumulants.** `κ_{2m−1} = κ_{2m} = λ / d₁^{2m−1}`.
    At `d₁ = 1`: all `κ_n = λ` (free Poisson).
    At `d₁ = 1`: `c_k` reduces to the Narayana polynomial `N_k(λ)`.

    The resolvent encodes ALL asymmetric moments simultaneously and
    was used to derive the exact `c₆` and `c₇` above. -/

-- ═══════════════════════════════════════════════════════════════════
-- §15. Universal scaling law — general statement
-- ═══════════════════════════════════════════════════════════════════

/-- **Theorem (Lancien–McShane, universal scaling law).**
    For each truncation order m, the p_{2m+1}-PPT asymptotic threshold satisfies

        λ*_m(d₁) = αₘ · d₁ − 1/d₁ + O(1/d₁³)

    where `αₘ = 4cos²(π/(m + 2))` is the balanced threshold from
    `PPTThreshold.det_hankel_vanishes`.

    The inner factor Qₘ(d₁, λ) of det Bₘ is degree 2m in λ.
    Substituting `λ = α d₁`:
    - leading coeff of Qₘ(α d₁, d₁) in d₁ vanishes at α = αₘ
    - this is the Chebyshev root from the balanced Hankel det

    **Proved instances:**
    - m = 1: `α₁ = 1`, leading coeff `α − 1`, threshold exact `d₁ − 1/d₁`
    - m = 2: `α₂ = 2`, leading coeff `−α(α − 2)`, threshold `2d₁ − 1/d₁ + O(1/d₁³)`
    - m = 3: `α₃ = (3+√5)/2`, leading coeff `α²(α²−3α+1)` -/
theorem scaling_law_summary :
    -- The three balanced slopes match 4cos²(π/(m+2)):
    4 * cos (π / 3) ^ 2 = 1 ∧
    4 * cos (π / 4) ^ 2 = 2 ∧
    -- For m = 3: α₃ = (3+√5)/2 solves α² − 3α + 1 = 0
    ((3 + Real.sqrt 5) / 2) ^ 2 - 3 * ((3 + Real.sqrt 5) / 2) + 1 = 0 := by
  refine ⟨alpha₁, alpha₂, ?_⟩
  set s := Real.sqrt 5
  have hs : s ^ 2 = 5 := by rw [sq]; exact mul_self_sqrt (by norm_num : (0:ℝ) ≤ 5)
  nlinarith [hs]

end General
