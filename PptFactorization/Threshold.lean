import PptFactorization.ClosedFormDet
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# PPT Threshold = 4cos²(π/(m+2))

Assembles `det_hankel_chebyshev` with the trigonometric characterization
of Chebyshev U roots.

## Proof chain

1. `chebyshev_U_eval_cos` : U_n(cos θ) = sin((n+1)θ) / sin θ
2. `chebyshev_U_root`     : U_n(cos(jπ/(n+1))) = 0  for 1 ≤ j ≤ n
3. `det_hankel_vanishes`  : det H_m(4cos²(jπ/(m+2))) = 0
4. `det_pos_above_threshold` : λ > 4cos²(π/(m+2)) ⟹ det H_m(λ) > 0

Institut Fourier, Grenoble — Kieran McShane / Cécilia Lancien
-/

open Real Polynomial ClosedFormDet Finset

namespace PPTThreshold

-- ═══════════════════════════════════════════════════════════════════
-- §1. Product-to-sum
-- ═══════════════════════════════════════════════════════════════════

/-- `2 cos a sin b = sin(b+a) + sin(b−a)`. -/
private lemma two_cos_mul_sin (a b : ℝ) :
    2 * cos a * sin b = sin (b + a) + sin (b - a) := by
  have h1 := sin_add b a
  have h2 := sin_sub b a
  -- sin(b+a) + sin(b-a) = 2 sin b cos a
  linarith

-- ═══════════════════════════════════════════════════════════════════
-- §2. U_n(cos θ) = sin((n+1)θ) / sin θ
-- ═══════════════════════════════════════════════════════════════════

/-- **Chebyshev–trigonometric identity.**
    Proof by pair induction; inductive step uses `2cos θ sin((n+1)θ)
    = sin((n+2)θ) + sin(nθ)`. -/
theorem chebyshev_U_eval_cos (n : ℕ) (θ : ℝ) (hθ : sin θ ≠ 0) :
    (Chebyshev.U ℝ (↑n : ℤ)).eval (cos θ) =
    sin ((↑n + 1) * θ) / sin θ := by
  -- Pair induction: P(k) ∧ P(k+1) for all k
  suffices h : ∀ k : ℕ,
    (Chebyshev.U ℝ (↑k : ℤ)).eval (cos θ) = sin ((↑k + 1) * θ) / sin θ ∧
    (Chebyshev.U ℝ (↑(k + 1) : ℤ)).eval (cos θ) =
      sin ((↑(k + 1) + 1) * θ) / sin θ
    from (h n).1
  intro k; induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · -- U₀(cos θ) = 1 = sin θ / sin θ
      simp only [Nat.cast_zero, Chebyshev.U_zero, eval_one, zero_add, one_mul]
      exact (div_self hθ).symm
    · -- U₁(cos θ) = 2cos θ = sin(2θ) / sin θ
      simp only [show 0 + 1 = 1 from rfl, Nat.cast_one,
        Chebyshev.U_one, eval_mul, eval_ofNat, eval_X]
      rw [show ((1 : ℝ) + 1) * θ = θ + θ from by ring, sin_add]
      field_simp; ring
  | succ m ih =>
    exact ⟨ih.2, by
      -- U_{m+2} = 2X · U_{m+1} − U_m
      have hcast : (↑(m + 2) : ℤ) = ↑m + 2 := by push_cast; ring
      conv_lhs => rw [hcast, Chebyshev.U_add_two]
      simp only [eval_sub, eval_mul, eval_ofNat, eval_X]
      -- Substitute IH (normalize ih.1 and ih.2 to match expanded cast form)
      have hcast1 : (↑(m + 1) : ℤ) = ↑m + 1 := by push_cast; ring
      rw [hcast1] at ih
      rw [ih.2, ih.1]
      -- Clear denominators and close with trig
      rw [show (↑(m + 1) + 1 : ℝ) = ↑m + 2 from by push_cast; ring]
      rw [show (↑(m + 1 + 1) + 1 : ℝ) = ↑m + 3 from by push_cast; ring]
      rw [show (↑m + 1 : ℝ) = ↑m + 1 from rfl]
      field_simp
      -- Goal: 2 cos θ · sin((m+2)θ) − sin((m+1)θ) = sin((m+3)θ)
      have key := two_cos_mul_sin θ ((↑m + 2) * θ)
      rw [show (↑m + 2) * θ + θ = (↑m + 3) * θ from by ring,
          show (↑m + 2) * θ - θ = (↑m + 1) * θ from by ring] at key
      ring_nf at key ⊢
      linarith⟩

-- ═══════════════════════════════════════════════════════════════════
-- §3. sin(nπ) = 0 and positivity
-- ═══════════════════════════════════════════════════════════════════

lemma sin_nat_mul_pi (j : ℕ) : sin (↑j * π) = 0 := by
  induction j with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, sin_add, sin_pi, cos_pi]
    nlinarith

lemma sin_div_pos (n j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    0 < sin (↑j * π / (↑n + 1)) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · have hj : (0 : ℝ) < ↑j := Nat.cast_pos.mpr (by omega)
    have hn : (0 : ℝ) < ↑n + 1 := by positivity
    positivity
  · have hn : (0 : ℝ) < ↑n + 1 := by positivity
    rw [div_lt_iff₀ hn]
    have : (↑j : ℝ) ≤ ↑n := Nat.cast_le.mpr hjn
    nlinarith [pi_pos]

-- ═══════════════════════════════════════════════════════════════════
-- §4. Roots of U_n
-- ═══════════════════════════════════════════════════════════════════

/-- `U_n(cos(jπ/(n+1))) = 0` for `1 ≤ j ≤ n`. -/
theorem chebyshev_U_root (n j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    (Chebyshev.U ℝ (↑n : ℤ)).eval (cos (↑j * π / (↑n + 1))) = 0 := by
  have hsin := sin_div_pos n j hj1 hjn
  rw [chebyshev_U_eval_cos n _ (ne_of_gt hsin)]
  have hn : (↑n + 1 : ℝ) ≠ 0 := by positivity
  rw [show (↑n + 1) * (↑j * π / (↑n + 1)) = ↑j * π from by field_simp]
  rw [sin_nat_mul_pi, zero_div]

-- ═══════════════════════════════════════════════════════════════════
-- §5. Positivity of U_n for t ≥ 1
-- ═══════════════════════════════════════════════════════════════════

/-- For `t ≥ 1`, `U_n(t) > 0`.
    Proof: pair induction showing `1 ≤ U_k(t)` and `U_k ≤ U_{k+1}`.
    The recurrence `U_{k+2} = 2t·U_{k+1} − U_k` with `2t ≥ 2` preserves both. -/
private lemma chebyshev_U_pos_of_one_le (n : ℕ) (t : ℝ) (ht : 1 ≤ t) :
    0 < (Chebyshev.U ℝ (↑n : ℤ)).eval t := by
  suffices h : ∀ k : ℕ,
    1 ≤ (Chebyshev.U ℝ (↑k : ℤ)).eval t ∧
    (Chebyshev.U ℝ (↑k : ℤ)).eval t ≤ (Chebyshev.U ℝ (↑(k + 1) : ℤ)).eval t by
    linarith [(h n).1]
  intro k; induction k with
  | zero =>
    constructor
    · simp [Chebyshev.U_zero]
    · simp only [show 0 + 1 = 1 from rfl, Nat.cast_zero, Nat.cast_one,
        Chebyshev.U_zero, Chebyshev.U_one, eval_one, eval_mul, eval_ofNat, eval_X]
      linarith
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih
    constructor
    · linarith
    · -- U_{m+2} = 2t·U_{m+1} − U_m ≥ U_{m+1}
      have heval : (Chebyshev.U ℝ (↑(m + 1 + 1) : ℤ)).eval t =
          2 * t * (Chebyshev.U ℝ (↑(m + 1) : ℤ)).eval t -
          (Chebyshev.U ℝ (↑m : ℤ)).eval t := by
        have : (↑(m + 1 + 1) : ℤ) = (↑m : ℤ) + 2 := by push_cast; ring
        rw [this, Chebyshev.U_add_two]
        simp [eval_sub, eval_mul, eval_ofNat, eval_X]
      rw [heval]
      -- U_{m+1} ≤ 2t·U_{m+1} − U_m  ⟺  U_m ≤ (2t−1)·U_{m+1}
      -- from h2: U_m ≤ U_{m+1}; from ht: 2t−1 ≥ 1; from h1,h2: U_{m+1} ≥ 1
      have ht2 : 1 ≤ 2 * t - 1 := by linarith
      have u_m1_pos : 0 < (Chebyshev.U ℝ (↑(m + 1) : ℤ)).eval t := by linarith
      nlinarith [mul_le_mul_of_nonneg_right ht2 (le_of_lt u_m1_pos)]

-- ═══════════════════════════════════════════════════════════════════
-- §6. Threshold roots of det H_m
-- ═══════════════════════════════════════════════════════════════════

/-- `cos(π/(m+2)) ≥ 0` since `π/(m+2) ∈ (0, π/2]`. -/
private lemma cos_pi_div_nonneg (m : ℕ) : 0 ≤ cos (π / (↑m + 2)) := by
  have hm2 : (0 : ℝ) < ↑m + 2 := by positivity
  have hge : 0 ≤ π / (↑m + 2) := div_nonneg (le_of_lt pi_pos) (le_of_lt hm2)
  have hle : π / (↑m + 2) ≤ π / 2 := by
    rw [div_le_iff₀ hm2]
    have : (↑m : ℝ) ≥ 0 := Nat.cast_nonneg m
    nlinarith [pi_pos]
  exact Real.cos_nonneg_of_mem_Icc ⟨by linarith, hle⟩

/-- `det H_m(4cos²(jπ/(m+2))) = 0` for `1 ≤ j ≤ m+1`. -/
theorem det_hankel_vanishes (m j : ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ m + 1)
    (hlam : 0 < 4 * cos (↑j * π / (↑m + 2)) ^ 2) :
    (hankelH (4 * cos (↑j * π / (↑m + 2)) ^ 2) m).det = 0 := by
  set α := ↑j * π / (↑m + 2) with hα_def
  set lj := 4 * cos α ^ 2 with hlj_def
  rw [det_hankel_chebyshev lj hlam]
  suffices h : (Chebyshev.U ℝ (↑(m + 1) : ℤ)).eval (sqrt lj / 2) = 0 by
    rw [show (↑(m + 1) : ℤ) = ↑m + 1 from by push_cast; ring] at h
    rw [h, mul_zero]
  -- √(4cos²α) / 2 = |cos α|
  have hsqrt : sqrt lj / 2 = |cos α| := by
    have : lj = (2 * cos α) ^ 2 := by rw [hlj_def]; ring
    rw [this, sqrt_sq_eq_abs, abs_mul, show |(2 : ℝ)| = 2 from abs_of_pos (by norm_num)]
    ring
  rw [hsqrt]
  -- Case split on sign of cos α
  by_cases hcos : 0 ≤ cos α
  -- Normalize α to match chebyshev_U_root's expected form
  have hα_norm : α = ↑j * π / (↑(m + 1) + 1) := by
    rw [hα_def]; push_cast; ring
  · -- |cos α| = cos α = cos(jπ/(m+2))
    rw [abs_of_nonneg hcos, hα_norm]
    exact chebyshev_U_root (m + 1) j hj1 hjm
  · -- |cos α| = −cos α = cos(π − α) = cos((m+2−j)π/(m+2))
    push_neg at hcos
    rw [abs_of_neg hcos, ← Real.cos_pi_sub α]
    have hjm2 : j ≤ m + 2 := by omega
    have hα_eq : π - α = ↑(m + 2 - j) * π / (↑(m + 1) + 1) := by
      rw [hα_def, Nat.cast_sub hjm2]
      push_cast
      have hm2 : (↑m : ℝ) + 2 ≠ 0 := by positivity
      field_simp
      ring
    rw [hα_eq]
    exact chebyshev_U_root (m + 1) (m + 2 - j) (by omega) (by omega)

-- ═══════════════════════════════════════════════════════════════════
-- §7. Positivity above threshold
-- ═══════════════════════════════════════════════════════════════════

/-- **Threshold (positive direction).**
    For `λ > 4cos²(π/(m+2))`, `det H_m(λ) > 0`.

    *Proof:*  Let `t = √λ/2`.
    - If `t ≥ 1`: `U_{m+1}(t) > 0` by `chebyshev_U_pos_of_one_le`.
    - If `t < 1`: set `θ = arccos t ∈ (0, π/(m+2))`.
      Then `U_{m+1}(cos θ) = sin((m+2)θ)/sin θ > 0`
      since `0 < (m+2)θ < π`. -/
theorem det_pos_above_threshold (m : ℕ) (lam : ℝ) (hlam : 0 < lam)
    (hgt : 4 * cos (π / (↑m + 2)) ^ 2 < lam) :
    0 < (hankelH lam m).det := by
  rw [det_hankel_chebyshev lam hlam]
  set t := sqrt lam / 2
  have ht_pos : 0 < t := by simp only [t]; positivity
  have hpow : 0 < sqrt lam ^ ((m + 1) ^ 2) := pow_pos (sqrt_pos.mpr hlam) _
  -- Suffices: U_{m+1}(t) > 0
  suffices hU : 0 < (Chebyshev.U ℝ (↑(m + 1) : ℤ)).eval t from mul_pos hpow hU
  -- Key: t > cos(π/(m+2))
  have hcos_nn : 0 ≤ cos (π / (↑m + 2)) := cos_pi_div_nonneg m
  have ht_gt_cos : cos (π / (↑m + 2)) < t := by
    simp only [t]
    -- From 4cos²(π/(m+2)) < λ and t = √λ/2 : cos < t follows by squaring
    have h_sq : cos (π / (↑m + 2)) ^ 2 < (sqrt lam / 2) ^ 2 := by
      rw [div_pow, sq_sqrt (le_of_lt hlam)]
      linarith
    have ht_pos' : (0 : ℝ) < sqrt lam / 2 := by positivity
    nlinarith [sq_nonneg (sqrt lam / 2 - cos (π / (↑m + 2))),
               sq_nonneg (sqrt lam / 2 + cos (π / (↑m + 2)))]
  by_cases ht1 : 1 ≤ t
  · -- Case t ≥ 1 : direct by pair induction
    exact chebyshev_U_pos_of_one_le (m + 1) t ht1
  · -- Case t < 1 : use arccos and trig formula
    push_neg at ht1
    set θ := Real.arccos t
    have ht_range : -1 ≤ t ∧ t ≤ 1 := ⟨by linarith, le_of_lt ht1⟩
    have hcos_θ : cos θ = t := Real.cos_arccos ht_range.1 ht_range.2
    -- θ > 0 (since t < 1 implies arccos t > arccos 1 = 0)
    have hθ_pos : 0 < θ := by
      have h0 : Real.arccos 1 = 0 := by
        have := Real.arccos_cos (le_refl (0 : ℝ)) (le_of_lt pi_pos)
        rwa [cos_zero] at this
      have := Real.arccos_lt_arccos ht_range.1 ht1 (le_refl 1)
      linarith
    -- θ < π/(m+2) (since cos(π/(m+2)) < t = cos θ and arccos is anti-monotone)
    have hθ_lt : θ < π / (↑m + 2) := by
      have h := Real.arccos_lt_arccos (neg_one_le_cos _) ht_gt_cos ht_range.2
      have hac : Real.arccos (cos (π / (↑m + 2))) = π / (↑m + 2) :=
        Real.arccos_cos (le_of_lt (by positivity))
          (div_le_self (le_of_lt pi_pos) (by have := (Nat.cast_nonneg (α := ℝ) m); linarith))
      linarith
    -- sin θ > 0 and sin((m+2)θ) > 0
    have hsin_θ : 0 < sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθ_pos (by
        have : π / (↑m + 2) ≤ π :=
          div_le_self (le_of_lt pi_pos) (by have := Nat.cast_nonneg (α := ℝ) m; linarith)
        linarith)
    rw [← hcos_θ, chebyshev_U_eval_cos (m + 1) θ (ne_of_gt hsin_θ)]
    apply div_pos _ hsin_θ
    -- sin((m+2)θ) > 0 since 0 < (m+2)θ < π
    apply Real.sin_pos_of_pos_of_lt_pi
    · have : (0 : ℝ) < ↑(m + 1) + 1 := by positivity
      positivity
    · have hm2 : (↑(m + 1) + 1 : ℝ) = ↑m + 2 := by push_cast; ring
      rw [hm2]
      have hm2_pos : (0 : ℝ) < ↑m + 2 := by positivity
      calc (↑m + 2) * θ < (↑m + 2) * (π / (↑m + 2)) :=
            mul_lt_mul_of_pos_left hθ_lt hm2_pos
        _ = π := mul_div_cancel₀ π (ne_of_gt hm2_pos)

-- ═══════════════════════════════════════════════════════════════════
-- §8. Negativity of U_n between roots
-- ═══════════════════════════════════════════════════════════════════

/-- `U_n(cos θ) < 0` for `n ≥ 1` and `θ ∈ (π/(n+1), 2π/(n+1))`.
    Since `(n+1)θ ∈ (π, 2π)`, we get `sin((n+1)θ) < 0` while `sin θ > 0`. -/
theorem chebyshev_U_neg_of_theta_in_gap (n : ℕ) (hn : 1 ≤ n) (θ : ℝ)
    (hlo : π / (↑n + 1) < θ) (hhi : θ < 2 * π / (↑n + 1)) :
    (Chebyshev.U ℝ (↑n : ℤ)).eval (cos θ) < 0 := by
  have hn1 : (0 : ℝ) < ↑n + 1 := by positivity
  have hθ_pos : 0 < θ := lt_trans (by positivity) hlo
  have hθ_lt_pi : θ < π := by
    calc θ < 2 * π / (↑n + 1) := hhi
      _ ≤ π := by
        rw [div_le_iff₀ hn1]
        nlinarith [show (1 : ℝ) ≤ ↑n from Nat.one_le_cast.mpr hn, pi_pos]
  have hsin_pos : 0 < sin θ := Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt_pi
  rw [chebyshev_U_eval_cos n θ (ne_of_gt hsin_pos)]
  apply div_neg_of_neg_of_pos _ hsin_pos
  -- sin((n+1)θ) < 0 via sin(π + ψ) = −sin ψ with ψ ∈ (0, π)
  set ψ := (↑n + 1) * θ - π
  have hψ_pos : 0 < ψ := by
    have : π < (↑n + 1) * θ := by
      calc π = (↑n + 1) * (π / (↑n + 1)) := (mul_div_cancel₀ π (ne_of_gt hn1)).symm
        _ < (↑n + 1) * θ := mul_lt_mul_of_pos_left hlo hn1
    linarith
  have hψ_lt_pi : ψ < π := by
    have : (↑n + 1) * θ < 2 * π := by
      calc (↑n + 1) * θ < (↑n + 1) * (2 * π / (↑n + 1)) :=
            mul_lt_mul_of_pos_left hhi hn1
        _ = 2 * π := by field_simp
    linarith
  have hkey : sin ((↑n + 1) * θ) = -(sin ψ) := by
    have heq : (↑n + 1) * θ = π + ψ := by simp only [ψ]; ring
    rw [heq, sin_add, sin_pi, cos_pi]; ring
  rw [hkey]
  linarith [Real.sin_pos_of_pos_of_lt_pi hψ_pos hψ_lt_pi]

-- ═══════════════════════════════════════════════════════════════════
-- §9. det H_m < 0 below threshold
-- ═══════════════════════════════════════════════════════════════════

/-- **Threshold (negative direction).**
    For `m ≥ 1`, if `cos(2π/(m+2)) < √λ/2 < cos(π/(m+2))`, then `det H_m(λ) < 0`.
    Combined with `det_pos_above_threshold`, this shows `4cos²(π/(m+2))` is sharp. -/
theorem det_neg_below_threshold (m : ℕ) (hm : 1 ≤ m) (lam : ℝ) (hlam : 0 < lam)
    (hlt : lam < 4 * cos (π / (↑m + 2)) ^ 2)
    (hgt : cos (2 * π / (↑m + 2)) < Real.sqrt lam / 2) :
    (hankelH lam m).det < 0 := by
  rw [det_hankel_chebyshev lam hlam]
  set t := Real.sqrt lam / 2
  have hpow : 0 < Real.sqrt lam ^ ((m + 1) ^ 2) := pow_pos (Real.sqrt_pos.mpr hlam) _
  suffices hU : (Chebyshev.U ℝ (↑(m + 1) : ℤ)).eval t < 0 from
    mul_neg_of_pos_of_neg hpow hU
  have ht_pos : 0 < t := by simp only [t]; positivity
  -- t < 1 since λ < 4cos²(…) ≤ 4
  have ht_lt_one : t < 1 := by
    simp only [t]
    rw [div_lt_one (by norm_num : (0 : ℝ) < 2)]
    have hlam4 : lam < 4 := by
      nlinarith [cos_le_one (π / (↑m + 2)), neg_one_le_cos (π / (↑m + 2))]
    calc Real.sqrt lam < Real.sqrt 4 := Real.sqrt_lt_sqrt (le_of_lt hlam) hlam4
      _ = 2 := by
        rw [show (4 : ℝ) = 2 * 2 from by norm_num]
        exact Real.sqrt_mul_self (by norm_num : (0 : ℝ) ≤ 2)
  -- arccos approach
  set θ := Real.arccos t
  have ht_range : -1 ≤ t ∧ t ≤ 1 := ⟨by linarith, le_of_lt ht_lt_one⟩
  have hcos_θ : cos θ = t := Real.cos_arccos ht_range.1 ht_range.2
  have hm2 : (0 : ℝ) < ↑m + 2 := by positivity
  have hm1_eq : (↑(m + 1) + 1 : ℝ) = ↑m + 2 := by push_cast; ring
  -- t < cos(π/(m+2))
  have hcos_nn : 0 ≤ cos (π / (↑m + 2)) := cos_pi_div_nonneg m
  have ht_lt_cos : t < cos (π / (↑m + 2)) := by
    simp only [t]
    have h_sq : (Real.sqrt lam / 2) ^ 2 < cos (π / (↑m + 2)) ^ 2 := by
      rw [div_pow, sq_sqrt (le_of_lt hlam)]; linarith
    nlinarith [sq_nonneg (Real.sqrt lam / 2 - cos (π / (↑m + 2))),
               sq_nonneg (Real.sqrt lam / 2 + cos (π / (↑m + 2)))]
  -- θ > π/(m+2)
  have hθ_lo : π / (↑(m + 1) + 1) < θ := by
    rw [hm1_eq]
    have hac : Real.arccos (cos (π / (↑m + 2))) = π / (↑m + 2) :=
      Real.arccos_cos (le_of_lt (by positivity))
        (div_le_self (le_of_lt pi_pos) (by linarith))
    have := Real.arccos_lt_arccos ht_range.1 ht_lt_cos (cos_le_one _)
    linarith
  -- θ < 2π/(m+2)
  have hθ_hi : θ < 2 * π / (↑(m + 1) + 1) := by
    rw [hm1_eq]
    have h2pi_le_pi : 2 * π / (↑m + 2) ≤ π := by
      rw [div_le_iff₀ hm2]
      nlinarith [show (1 : ℝ) ≤ ↑m from Nat.one_le_cast.mpr hm, pi_pos]
    have hac2 : Real.arccos (cos (2 * π / (↑m + 2))) = 2 * π / (↑m + 2) :=
      Real.arccos_cos (by positivity) h2pi_le_pi
    have := Real.arccos_lt_arccos (neg_one_le_cos _) hgt ht_range.2
    linarith
  rw [← hcos_θ]
  exact chebyshev_U_neg_of_theta_in_gap (m + 1) (by omega) θ hθ_lo hθ_hi

end PPTThreshold
