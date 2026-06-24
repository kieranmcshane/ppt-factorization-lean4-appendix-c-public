import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.LinearCombination

/-!
# E-type Balanced Polynomial Vanishings

Proves that the correct E₆, E₇, E₈ balanced polynomials vanish at
their respective Jones-index thresholds.

- **E₆** : `α³ − 6α² + 9α − 2 = 0` at `α = 2 + √3 = 4cos²(π/12)`
- **E₇** : `α³ − 6α² + 9α − 3 = 0` at `α = 4cos²(π/18)`
- **E₈** : `α⁴ − 7α³ + 14α² − 8α + 1 = 0` at `α = 4cos²(π/30)`

Derivations:

- **E₆**: elementary, uses `(√3)² = 3`.

- **E₇**: `cos(3·π/9) = cos(π/3) = ½` with the triple-angle identity gives
  `8·cos³(π/9) − 6·cos(π/9) = 1`.  Substituting
  `α = 2 + 2·cos(π/9) = 4cos²(π/18)` (via `cos(2·π/18) = 2cos²(π/18) − 1`)
  produces exactly `α³ − 6α² + 9α − 3 = 0`.

- **E₈**: derive the quintuple-angle formula `cos(5θ) = 16c⁵ − 20c³ + 5c`
  (where `c = cos θ`) from `cos_add_cos` plus `cos_three_mul`, `cos_two_mul`.
  Apply at `θ = π/15` where `cos(5·π/15) = cos(π/3) = ½`, yielding
  `32·c⁵ − 40·c³ + 10·c − 1 = 0`.  Substituting `α = 2 + 2c = 4cos²(π/30)`
  gives the quintic `α⁵ − 10α⁴ + 35α³ − 50α² + 25α − 3 = 0`, which factors
  as `(α − 3)·(α⁴ − 7α³ + 14α² − 8α + 1)`.  Since `cos(π/30) > cos(π/6) = √3/2`
  by strict antitonicity of `cos` on `[0, π]`, we have `α > 3`, so
  `α − 3 ≠ 0` and the quartic factor vanishes.
-/

open Real

namespace ETypeBalanced

-- ═══════════════════════════════════════════════════════════════════
-- §1. E₆ : α³ − 6α² + 9α − 2 = 0 at α = 2 + √3
-- ═══════════════════════════════════════════════════════════════════

theorem E6_vanishes :
    (2 + Real.sqrt 3) ^ 3 - 6 * (2 + Real.sqrt 3) ^ 2 + 9 * (2 + Real.sqrt 3) - 2 = 0 := by
  have h : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  linear_combination Real.sqrt 3 * h

-- ═══════════════════════════════════════════════════════════════════
-- §2. E₇ : α³ − 6α² + 9α − 3 = 0 at α = 4cos²(π/18)
-- ═══════════════════════════════════════════════════════════════════

theorem E7_vanishes :
    (4 * cos (π / 18) ^ 2) ^ 3 - 6 * (4 * cos (π / 18) ^ 2) ^ 2
      + 9 * (4 * cos (π / 18) ^ 2) - 3 = 0 := by
  -- 4·cos²(π/18) = 2 + 2·cos(π/9)
  have h_dbl : 4 * cos (π / 18) ^ 2 = 2 + 2 * cos (π / 9) := by
    have h := Real.cos_two_mul (π / 18)
    rw [show (2 : ℝ) * (π / 18) = π / 9 from by ring] at h
    linarith
  -- 4·cos³(π/9) − 3·cos(π/9) = ½
  have h_tri : 4 * cos (π / 9) ^ 3 - 3 * cos (π / 9) = 1 / 2 := by
    have h := Real.cos_three_mul (π / 9)
    rw [show (3 : ℝ) * (π / 9) = π / 3 from by ring, Real.cos_pi_div_three] at h
    linarith
  rw [h_dbl]
  linear_combination 2 * h_tri

-- ═══════════════════════════════════════════════════════════════════
-- §3. Quintuple-angle formula: cos(5θ) = 16·c⁵ − 20·c³ + 5·c
-- ═══════════════════════════════════════════════════════════════════

/-- Quintuple-angle identity, derived from
    `cos(5θ) + cos(θ) = 2·cos(3θ)·cos(2θ)` plus triple/double angle. -/
private lemma cos_five_mul (θ : ℝ) :
    cos (5 * θ) = 16 * cos θ ^ 5 - 20 * cos θ ^ 3 + 5 * cos θ := by
  have h_add := Real.cos_add_cos (5 * θ) θ
  rw [show (5 * θ + θ) / 2 = 3 * θ from by ring,
      show (5 * θ - θ) / 2 = 2 * θ from by ring] at h_add
  rw [Real.cos_three_mul, Real.cos_two_mul] at h_add
  linear_combination h_add

-- ═══════════════════════════════════════════════════════════════════
-- §4. E₈ : α⁴ − 7α³ + 14α² − 8α + 1 = 0 at α = 4cos²(π/30)
-- ═══════════════════════════════════════════════════════════════════

theorem E8_vanishes :
    (4 * cos (π / 30) ^ 2) ^ 4 - 7 * (4 * cos (π / 30) ^ 2) ^ 3
      + 14 * (4 * cos (π / 30) ^ 2) ^ 2 - 8 * (4 * cos (π / 30) ^ 2) + 1 = 0 := by
  set α := 4 * cos (π / 30) ^ 2 with hα_def
  -- α = 2 + 2·cos(π/15)
  have h_dbl : α = 2 + 2 * cos (π / 15) := by
    show 4 * cos (π / 30) ^ 2 = 2 + 2 * cos (π / 15)
    have h := Real.cos_two_mul (π / 30)
    rw [show (2 : ℝ) * (π / 30) = π / 15 from by ring] at h
    linarith
  -- Quintuple-angle at π/15: 16·c⁵ − 20·c³ + 5·c = ½
  have h_quint : 16 * cos (π / 15) ^ 5 - 20 * cos (π / 15) ^ 3
      + 5 * cos (π / 15) = 1 / 2 := by
    have h := cos_five_mul (π / 15)
    rw [show (5 : ℝ) * (π / 15) = π / 3 from by ring, Real.cos_pi_div_three] at h
    linarith
  -- α is a root of the quintic α⁵ − 10α⁴ + 35α³ − 50α² + 25α − 3
  have h_quintic : α ^ 5 - 10 * α ^ 4 + 35 * α ^ 3 - 50 * α ^ 2 + 25 * α - 3 = 0 := by
    rw [h_dbl]
    linear_combination 2 * h_quint
  -- α > 3 via cos(π/30) > cos(π/6) = √3/2
  have h_gt : 3 < α := by
    show 3 < 4 * cos (π / 30) ^ 2
    have hmem1 : π / 30 ∈ Set.Icc (0:ℝ) π :=
      ⟨by positivity, by linarith [Real.pi_pos]⟩
    have hmem2 : π / 6 ∈ Set.Icc (0:ℝ) π :=
      ⟨by positivity, by linarith [Real.pi_pos]⟩
    have h_lt : π / 30 < π / 6 := by linarith [Real.pi_pos]
    have h_mono := Real.strictAntiOn_cos hmem1 hmem2 h_lt
    rw [Real.cos_pi_div_six] at h_mono
    -- h_mono : √3 / 2 < cos (π / 30)
    have h_sqrt_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    have hc_pos : 0 < cos (π / 30) := by linarith
    have h_sq : (Real.sqrt 3 / 2) ^ 2 < cos (π / 30) ^ 2 :=
      sq_lt_sq' (by linarith) h_mono
    have h_sqrt_sq : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]; norm_num
    linarith
  -- Factor and conclude the quartic factor vanishes
  have h_ne : α - 3 ≠ 0 := sub_ne_zero.mpr (ne_of_gt h_gt)
  have h_factor : (α - 3) * (α ^ 4 - 7 * α ^ 3 + 14 * α ^ 2 - 8 * α + 1) =
      α ^ 5 - 10 * α ^ 4 + 35 * α ^ 3 - 50 * α ^ 2 + 25 * α - 3 := by ring
  have h_prod_zero : (α - 3) * (α ^ 4 - 7 * α ^ 3 + 14 * α ^ 2 - 8 * α + 1) = 0 := by
    rw [h_factor]; exact h_quintic
  exact (mul_eq_zero.mp h_prod_zero).resolve_left h_ne

-- ═══════════════════════════════════════════════════════════════════
-- §5. E₆ transversality: P'(2+√3) = 6 > 0
-- ═══════════════════════════════════════════════════════════════════

/-- For E₆, `P'(α) = 3α² − 12α + 9`.  At `α = 2+√3`, this equals 6. -/
theorem E6_deriv_eq :
    3 * (2 + Real.sqrt 3) ^ 2 - 12 * (2 + Real.sqrt 3) + 9 = 6 := by
  have h : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  linear_combination 3 * h

theorem E6_transverse :
    0 < 3 * (2 + Real.sqrt 3) ^ 2 - 12 * (2 + Real.sqrt 3) + 9 := by
  rw [E6_deriv_eq]; norm_num

-- ═══════════════════════════════════════════════════════════════════
-- §6. E₇ transversality: P'(α) = 12·cos²(π/9) − 3 > 0
-- ═══════════════════════════════════════════════════════════════════

/-- For E₇, `P'(α) = 3α² − 12α + 9`.  Substituting `α = 2 + 2cos(π/9)`
    gives `12·cos²(π/9) − 3`, which is positive since
    `cos(π/9) > cos(π/3) = 1/2`. -/
theorem E7_transverse :
    0 < 3 * (4 * cos (π / 18) ^ 2) ^ 2 - 12 * (4 * cos (π / 18) ^ 2) + 9 := by
  have h_dbl : 4 * cos (π / 18) ^ 2 = 2 + 2 * cos (π / 9) := by
    have h := Real.cos_two_mul (π / 18)
    rw [show (2 : ℝ) * (π / 18) = π / 9 from by ring] at h
    linarith
  rw [h_dbl]
  have h_simp : 3 * (2 + 2 * cos (π / 9)) ^ 2 - 12 * (2 + 2 * cos (π / 9)) + 9
              = 12 * cos (π / 9) ^ 2 - 3 := by ring
  rw [h_simp]
  -- Show cos(π/9) > 1/2 via strict antitonicity on [0, π]
  have h_mono : cos (π / 3) < cos (π / 9) :=
    Real.strictAntiOn_cos
      ⟨by positivity, by linarith [Real.pi_pos]⟩
      ⟨by positivity, by linarith [Real.pi_pos]⟩
      (by linarith [Real.pi_pos])
  rw [Real.cos_pi_div_three] at h_mono
  -- 12·cos²(π/9) − 3 > 0 since cos(π/9) > 1/2
  nlinarith [h_mono, sq_nonneg (cos (π / 9) - 1 / 2)]

-- ═══════════════════════════════════════════════════════════════════
-- §7. E₈ transversality: 32c³ + 12c² − 16c − 4 > 0 (c = cos(π/15))
-- ═══════════════════════════════════════════════════════════════════

/-- For E₈, `P'(α) = 4α³ − 21α² + 28α − 8`.  Substituting `α = 2 + 2c`
    where `c = cos(π/15)` gives `32c³ + 12c² − 16c − 4`.
    Since `c > cos(π/6) = √3/2`, we have `c² > 3/4` and `c³ > 3√3/8`
    (the latter via the factorisation
    `c³ − 3√3/8 = (c − √3/2)(c² + c·√3/2 + 3/4)`).
    Combined with `c ≤ 1`, this gives the lower bound `12√3 − 11 > 0`,
    since `(12√3)² = 432 > 121 = 11²`. -/
theorem E8_transverse :
    0 < 4 * (4 * cos (π / 30) ^ 2) ^ 3 - 21 * (4 * cos (π / 30) ^ 2) ^ 2
        + 28 * (4 * cos (π / 30) ^ 2) - 8 := by
  have h_dbl : 4 * cos (π / 30) ^ 2 = 2 + 2 * cos (π / 15) := by
    have h := Real.cos_two_mul (π / 30)
    rw [show (2 : ℝ) * (π / 30) = π / 15 from by ring] at h
    linarith
  rw [h_dbl]
  have h_simp : 4 * (2 + 2 * cos (π / 15)) ^ 3 - 21 * (2 + 2 * cos (π / 15)) ^ 2
              + 28 * (2 + 2 * cos (π / 15)) - 8
              = 32 * cos (π / 15) ^ 3 + 12 * cos (π / 15) ^ 2
                  - 16 * cos (π / 15) - 4 := by ring
  rw [h_simp]
  -- c > √3/2 via cos strict antitonicity (π/15 < π/6)
  have h_mono : Real.sqrt 3 / 2 < cos (π / 15) := by
    have h := Real.strictAntiOn_cos
      (show π / 15 ∈ Set.Icc (0:ℝ) π from
        ⟨by positivity, by linarith [Real.pi_pos]⟩)
      (show π / 6 ∈ Set.Icc (0:ℝ) π from
        ⟨by positivity, by linarith [Real.pi_pos]⟩)
      (by linarith [Real.pi_pos] : π / 15 < π / 6)
    rwa [Real.cos_pi_div_six] at h
  have h_sqrt_sq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h_sqrt_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hc_pos : 0 < cos (π / 15) := by linarith
  have hc_le_1 : cos (π / 15) ≤ 1 := Real.cos_le_one _
  -- 11 < 12√3 (equivalently 121 < 432)
  have h_11_lt : 11 < 12 * Real.sqrt 3 := by
    have h_sub : (11 / 12 : ℝ) < Real.sqrt 3 := by
      have h_eq : ((11 : ℝ) / 12) = Real.sqrt ((11 / 12) ^ 2) :=
        (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 11 / 12)).symm
      rw [h_eq]
      exact Real.sqrt_lt_sqrt (by positivity) (by norm_num)
    linarith
  -- c² > 3/4
  have h_c_sq : 3 / 4 < cos (π / 15) ^ 2 := by
    have h1 : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]; norm_num
    calc 3 / 4 = (Real.sqrt 3 / 2) ^ 2 := h1.symm
      _ < cos (π / 15) ^ 2 := sq_lt_sq' (by linarith) h_mono
  -- c³ > 3√3/8 via factorisation
  have h_c_cube : 3 * Real.sqrt 3 / 8 < cos (π / 15) ^ 3 := by
    have h_factor : cos (π / 15) ^ 3 - 3 * Real.sqrt 3 / 8 =
        (cos (π / 15) - Real.sqrt 3 / 2) *
        (cos (π / 15) ^ 2 + cos (π / 15) * (Real.sqrt 3 / 2) + 3 / 4) := by
      linear_combination (cos (π / 15) / 4) * h_sqrt_sq
    have h_diff : 0 < cos (π / 15) - Real.sqrt 3 / 2 := by linarith
    have h_other : 0 < cos (π / 15) ^ 2 + cos (π / 15) * (Real.sqrt 3 / 2) + 3 / 4 := by
      have h1 : 0 ≤ cos (π / 15) ^ 2 := sq_nonneg _
      have h2 : 0 ≤ cos (π / 15) * (Real.sqrt 3 / 2) :=
        mul_nonneg (le_of_lt hc_pos) (by linarith)
      linarith
    linarith [mul_pos h_diff h_other, h_factor]
  -- Combine: 32c³ + 12c² − 16c − 4 > 12√3 + 9 − 16 − 4 = 12√3 − 11 > 0
  linarith [h_11_lt, h_c_sq, h_c_cube, hc_le_1]

end ETypeBalanced
