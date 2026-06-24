import PptFactorization.General
import PptFactorization.ClosedFormDet
import PptFactorization.Threshold
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Universal Scaling Law for PPT Thresholds

## Bridge between asymmetric (finite d₁) and balanced (d₁ → ∞) worlds

The balanced Hankel determinant `det H_m(α) = (√α)^{(m+1)²} U_{m+1}(√α/2)`
vanishes at `α_m = 4cos²(π/(m+2))` (proved in `Threshold.lean` for all m).

The asymmetric Hankel determinant `det B_m(λ, d₁)` at `λ = α d₁` has
leading term equal to the balanced determinant (as `d₁ → ∞`), so its
threshold satisfies `λ*_m(d₁) ≈ α_m d₁`.

The universal correction is `−1/d₁`:

    **λ*_m(d₁) = αₘ · d₁ − 1/d₁ + O(1/d₁³)**

## Main results

* `threshold₂_correction_exact` : exact formula for the m = 2 correction
* `threshold₂_scaling_bound` : `|λ*₂ − (2d₁ − 1/d₁)| ≤ 1/d₁⁵`
* `detB₁_leading_eq_balanced` : bridge theorem for m = 1
* `detB₂_leading_eq_balanced` : bridge theorem for m = 2

Institut Fourier, Grenoble — Kieran McShane / Cécilia Lancien
-/

open Real General

namespace ScalingLaw

variable (d₁ : ℝ)

-- ═══════════════════════════════════════════════════════════════════
-- §1. Conjugate identity
-- ═══════════════════════════════════════════════════════════════════

/-- `(2d₁⁴ + d₁² − 1)² − Δ₂ = 4d₁²`.
    This is the key to the conjugate/rationalization trick. -/
theorem sq_minus_disc₂ :
    (2 * d₁ ^ 4 + d₁ ^ 2 - 1) ^ 2 - disc₂ d₁ = 4 * d₁ ^ 2 := by
  simp only [disc₂]; ring

-- ═══════════════════════════════════════════════════════════════════
-- §2. Exact correction formula for m = 2 threshold
-- ═══════════════════════════════════════════════════════════════════

/-- **Exact correction.**
    `λ*₂(d₁) − (2d₁ − 1/d₁) = −2 / (d₁ · (a + √Δ₂))`
    where `a = 2d₁⁴ + d₁² − 1`.

    Proof by rationalization: `a² − Δ₂ = 4d₁²`, so
    `√Δ₂ − a = −4d₁²/(a + √Δ₂)`, and the threshold difference
    equals `(√Δ₂ − a)/(2d₁³)`. -/
theorem threshold₂_correction_exact (hd : 1 ≤ d₁) (hdisc : 0 ≤ disc₂ d₁) :
    threshold₂ d₁ - (2 * d₁ - 1 / d₁) =
    -2 / (d₁ * ((2 * d₁ ^ 4 + d₁ ^ 2 - 1) + sqrt (disc₂ d₁))) := by
  set s := sqrt (disc₂ d₁) with hs_def
  set a := 2 * d₁ ^ 4 + d₁ ^ 2 - (1 : ℝ) with ha_def
  have hs_sq : s ^ 2 = disc₂ d₁ := sq_sqrt hdisc
  have hd_pos : 0 < d₁ := by linarith
  have hd_ne : d₁ ≠ 0 := ne_of_gt hd_pos
  have hs_nn : 0 ≤ s := sqrt_nonneg _
  have ha_pos : 0 < a := by
    simp only [a]; nlinarith [sq_nonneg (d₁ - 1), sq_nonneg (d₁ ^ 2)]
  have has_pos : 0 < a + s := by linarith
  have has_ne : a + s ≠ 0 := ne_of_gt has_pos
  -- Step 1: the difference equals (s − a)/(2d₁³)
  have step1 : threshold₂ d₁ - (2 * d₁ - 1 / d₁) = (s - a) / (2 * d₁ ^ 3) := by
    simp only [threshold₂, a, hs_def]
    field_simp
    ring
  -- Step 2: conjugate identity  (s − a)(a + s) = s² − a² = −4d₁²
  have conj : (s - a) * (a + s) = -(4 * d₁ ^ 2) := by
    have h := sq_minus_disc₂ d₁
    nlinarith [hs_sq, sq_abs (a : ℝ)]
  -- Step 3: s − a = −4d₁²/(a + s)
  have step2 : s - a = -(4 * d₁ ^ 2) / (a + s) := by
    rw [eq_div_iff has_ne]; linarith [conj]
  -- Combine
  rw [step1, step2]
  field_simp
  ring

-- ═══════════════════════════════════════════════════════════════════
-- §3. Scaling law bound for m = 2
-- ═══════════════════════════════════════════════════════════════════

/-- `a + √Δ₂ ≥ 2d₁⁴` (since `a ≥ 2d₁⁴` and `√Δ₂ ≥ 0`). -/
theorem a_plus_sqrt_disc₂_lower (hd : 1 ≤ d₁) (_hdisc : 0 ≤ disc₂ d₁) :
    2 * d₁ ^ 4 ≤ (2 * d₁ ^ 4 + d₁ ^ 2 - 1) + sqrt (disc₂ d₁) := by
  have : 0 ≤ sqrt (disc₂ d₁) := sqrt_nonneg _
  nlinarith [sq_nonneg d₁]

/-- **Scaling law for m = 2.**
    `|λ*₂(d₁) − (2d₁ − 1/d₁)| ≤ 1/d₁⁵` for `d₁ ≥ 2`. -/
theorem threshold₂_scaling_bound (hd : 2 ≤ d₁) :
    |threshold₂ d₁ - (2 * d₁ - 1 / d₁)| ≤ 1 / d₁ ^ 5 := by
  have hd_pos : 0 < d₁ := by linarith
  have hdisc : 0 ≤ disc₂ d₁ := le_of_lt (disc₂_pos d₁ hd)
  -- Use the exact formula
  rw [threshold₂_correction_exact d₁ (by linarith) hdisc]
  set s := sqrt (disc₂ d₁)
  set a := 2 * d₁ ^ 4 + d₁ ^ 2 - (1 : ℝ)
  have ha_pos : 0 < a := by
    simp only [a]; nlinarith [sq_nonneg (d₁ - 1), sq_nonneg (d₁ ^ 2)]
  have hs_nn : 0 ≤ s := sqrt_nonneg _
  have has_pos : 0 < a + s := by linarith
  -- a + s ≥ 2d₁⁴  (since a ≥ 2d₁⁴ for d₁ ≥ 1 and s ≥ 0)
  have hlower : 2 * d₁ ^ 4 ≤ a + s :=
    a_plus_sqrt_disc₂_lower d₁ (by linarith) hdisc
  -- d₁(a+s) ≥ 2d₁⁵
  have hprod : 2 * d₁ ^ 5 ≤ d₁ * (a + s) := by nlinarith
  -- |−2/(d₁(a+s))| = 2/(d₁(a+s)) ≤ 2/(2d₁⁵) = 1/d₁⁵
  rw [show (1 : ℝ) / d₁ ^ 5 = 2 / (2 * d₁ ^ 5) from by ring]
  rw [show (-2 : ℝ) / (d₁ * (a + s)) = -(2 / (d₁ * (a + s))) from by ring]
  rw [abs_neg, abs_of_pos (div_pos (by positivity) (by positivity : 0 < d₁ * (a + s)))]
  gcongr

-- ═══════════════════════════════════════════════════════════════════
-- §4. Bridge: asymmetric det → balanced det
-- ═══════════════════════════════════════════════════════════════════

/-- **Bridge (m = 1).** `det B₁(α d₁, d₁) = α²(α − 1) + α²/d₁²`.
    The leading term `α²(α − 1)` is the balanced Hankel determinant
    `det H₁(α) = M₁M₃ − M₂²`. -/
theorem detB₁_leading_eq_balanced (α : ℝ) (hd : d₁ ≠ 0) :
    detB₁ (α * d₁) d₁ = α ^ 2 * (α - 1) + α ^ 2 / d₁ ^ 2 := by
  rw [detB₁_balanced d₁ α hd]; field_simp

/-- **Bridge (m = 2).** The exact balanced expansion of `det B₂`:
    `det B₂(α d₁, d₁) = α⁵(α−2) + α⁴(3α−4)/d₁² + α⁴(4−α)/d₁⁴`. -/
theorem detB₂_balanced_expansion (α : ℝ) (hd : d₁ ≠ 0) :
    detB₂ (α * d₁) d₁ =
    α ^ 5 * (α - 2) +
    α ^ 4 * (3 * α - 4) / d₁ ^ 2 +
    α ^ 4 * (4 - α) / d₁ ^ 4 := by
  rw [detB₂_eq _ _ hd, Q₂_at_slope]
  field_simp; ring

-- ═══════════════════════════════════════════════════════════════════
-- §5. Scaling law: m = 1 (exact)
-- ═══════════════════════════════════════════════════════════════════

/-- **Scaling law (m = 1, exact).**
    `λ*₁(d₁) = d₁ − 1/d₁ = 1 · d₁ − 1/d₁` where `α₁ = 1 = 4cos²(π/3)`.
    The correction beyond `α₁ d₁ − 1/d₁` is exactly zero. -/
theorem scaling_m1 (_hd : d₁ ≠ 0) :
    threshold₁ d₁ = 1 * d₁ - 1 / d₁ := by
  simp only [threshold₁]; ring

-- ═══════════════════════════════════════════════════════════════════
-- §6. Scaling law: m = 2
-- ═══════════════════════════════════════════════════════════════════

/-- **Scaling law (m = 2).**
    `λ*₂(d₁) = 2d₁ − 1/d₁ + ε` where `|ε| ≤ 1/d₁⁵`.
    The slope `α₂ = 2 = 4cos²(π/4)` and the correction `−1/d₁` are universal. -/
theorem scaling_m2 (hd : 2 ≤ d₁) :
    ∃ ε : ℝ, threshold₂ d₁ = 2 * d₁ - 1 / d₁ + ε ∧ |ε| ≤ 1 / d₁ ^ 5 := by
  exact ⟨threshold₂ d₁ - (2 * d₁ - 1 / d₁), by ring,
    threshold₂_scaling_bound d₁ hd⟩

-- ═══════════════════════════════════════════════════════════════════
-- §7. Universal statement
-- ═══════════════════════════════════════════════════════════════════

/-- **Universal scaling law — proved instances.**

    For m = 1: `λ*₁ = d₁ − 1/d₁` (exact, correction = 0).
    For m = 2: `λ*₂ = 2d₁ − 1/d₁ + O(1/d₁⁵)` (correction ≤ 1/d₁⁵).

    In both cases, `αₘ = 4cos²(π/(m+2))`:
    - `α₁ = 4cos²(π/3) = 1`
    - `α₂ = 4cos²(π/4) = 2`

    The balanced threshold `αₘ` is the Chebyshev U root from
    `PPTThreshold.det_hankel_vanishes` (proved for all m).

    The bridge theorems `detB₁_leading_eq_balanced` and
    `detB₂_balanced_expansion` show that the leading term of the
    asymmetric Hankel determinant at `λ = α d₁` equals the balanced
    Hankel determinant — connecting the two worlds. -/
theorem universal_scaling_law_instances :
    -- m = 1: slope
    4 * cos (π / 3) ^ 2 = 1 ∧
    -- m = 2: slope
    4 * cos (π / 4) ^ 2 = 2 ∧
    -- m = 1: threshold exact
    (∀ d₁ : ℝ, d₁ ≠ 0 → threshold₁ d₁ = 1 * d₁ - 1 / d₁) ∧
    -- m = 2: threshold asymptotic
    (∀ d₁ : ℝ, 2 ≤ d₁ →
      ∃ ε, threshold₂ d₁ = 2 * d₁ - 1 / d₁ + ε ∧ |ε| ≤ 1 / d₁ ^ 5) :=
  ⟨alpha₁, alpha₂, scaling_m1, scaling_m2⟩

end ScalingLaw
