import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.Field

open Real Polynomial Finset Filter Topology

namespace SelfContainedProof

-- ═══════════════════════════════════════════════════════════════════
-- §1. Tridiagonal recurrence d(n, λ)
-- ═══════════════════════════════════════════════════════════════════

noncomputable def d (lam : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => lam
  | n + 2 => lam * d lam (n + 1) - lam * d lam n

@[simp] lemma d_zero (lam : ℝ) : d lam 0 = 1 := rfl
@[simp] lemma d_one (lam : ℝ) : d lam 1 = lam := rfl

-- ═══════════════════════════════════════════════════════════════════
-- §2. Chebyshev U: evaluated form
-- ═══════════════════════════════════════════════════════════════════

noncomputable def chebU : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, x => 2 * x
  | n + 2, x => 2 * x * chebU (n + 1) x - chebU n x

@[simp] lemma chebU_zero (x : ℝ) : chebU 0 x = 1 := rfl
@[simp] lemma chebU_one (x : ℝ) : chebU 1 x = 2 * x := rfl

lemma chebU_succ_succ (n : ℕ) (x : ℝ) :
    chebU (n + 2) x = 2 * x * chebU (n + 1) x - chebU n x := rfl

theorem chebU_eq_poly (n : ℕ) (x : ℝ) :
    chebU n x = (Chebyshev.U ℝ (↑n : ℤ)).eval x := by
  suffices h : ∀ k : ℕ,
    chebU k x = (Chebyshev.U ℝ (↑k : ℤ)).eval x ∧
    chebU (k + 1) x = (Chebyshev.U ℝ (↑(k + 1) : ℤ)).eval x
    from (h n).1
  intro k; induction k with
  | zero =>
    exact ⟨by simp [Chebyshev.U_zero],
      by rw [chebU_one]; simp [Chebyshev.U_one, eval_mul, eval_ofNat, eval_X]⟩
  | succ m ih =>
    exact ⟨ih.2, by
      rw [chebU_succ_succ, ih.2, ih.1]
      rw [show (↑(m + 1 + 1) : ℤ) = (↑m : ℤ) + 2 from by push_cast; ring]
      rw [Chebyshev.U_add_two ℝ (↑m : ℤ)]
      simp only [eval_sub, eval_mul, eval_ofNat, eval_X]; push_cast; rfl⟩

-- ═══════════════════════════════════════════════════════════════════
-- §3. Trigonometric evaluation: U_n(cos θ) = sin((n+1)θ)/sin θ
-- ═══════════════════════════════════════════════════════════════════

private lemma two_cos_mul_sin (a b : ℝ) :
    2 * cos a * sin b = sin (b + a) + sin (b - a) := by
  linarith [sin_add b a, sin_sub b a]

theorem chebU_cos (n : ℕ) (θ : ℝ) (hθ : sin θ ≠ 0) :
    chebU n (cos θ) = sin ((↑n + 1) * θ) / sin θ := by
  suffices h : ∀ k : ℕ,
    chebU k (cos θ) = sin ((↑k + 1) * θ) / sin θ ∧
    chebU (k + 1) (cos θ) = sin ((↑(k + 1) + 1) * θ) / sin θ
    from (h n).1
  intro k; induction k with
  | zero =>
    exact ⟨by rw [chebU_zero, show (↑(0:ℕ) + 1 : ℝ) * θ = θ from by push_cast; ring]
              exact (div_self hθ).symm,
      by rw [chebU_one, show (↑(0+1:ℕ) + 1 : ℝ) * θ = θ + θ from by push_cast; ring, sin_add]
         field_simp; ring⟩
  | succ m ih =>
    exact ⟨ih.2, by
      rw [chebU_succ_succ, ih.2, ih.1]
      rw [show (↑(m+1) + 1 : ℝ) = ↑m + 2 from by push_cast; ring,
          show (↑m + 1 : ℝ) = ↑m + 1 from rfl,
          show (↑(m+1+1) + 1 : ℝ) = ↑m + 3 from by push_cast; ring]
      field_simp
      have key := two_cos_mul_sin θ ((↑m + 2) * θ)
      rw [show (↑m + 2) * θ + θ = (↑m + 3) * θ from by ring,
          show (↑m + 2) * θ - θ = (↑m + 1) * θ from by ring] at key
      have eq1 : sin ((↑m + 1) * θ) = sin (θ * (↑m + 1)) := by congr 1; ring
      have eq2 : sin ((↑m + 3) * θ) = sin (θ * (↑m + 3)) := by congr 1; ring
      rw [eq1, eq2] at key; linarith⟩

-- Mathlib's Chebyshev.U version
theorem chebyshev_U_eval_cos (n : ℕ) (θ : ℝ) (hθ : sin θ ≠ 0) :
    (Chebyshev.U ℝ (↑n : ℤ)).eval (cos θ) = sin ((↑n + 1) * θ) / sin θ := by
  rw [← chebU_eq_poly]; exact chebU_cos n θ hθ

private lemma sin_div_pos (n j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    0 < sin (↑j * π / (↑n + 1)) := by
  apply sin_pos_of_pos_of_lt_pi
  · positivity
  · rw [div_lt_iff₀ (show (0:ℝ) < ↑n + 1 from by positivity)]
    nlinarith [pi_pos, show (↑j : ℝ) ≤ ↑n from Nat.cast_le.mpr hjn]

theorem chebyshev_U_root (n j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    (Chebyshev.U ℝ (↑n : ℤ)).eval (cos (↑j * π / (↑n + 1))) = 0 := by
  rw [chebyshev_U_eval_cos n _ (ne_of_gt (sin_div_pos n j hj1 hjn))]
  rw [show (↑n + 1) * (↑j * π / (↑n + 1)) = ↑j * π from by
    field_simp]
  rw [sin_nat_mul_pi, zero_div]

-- ═══════════════════════════════════════════════════════════════════
-- §4. Closed form: d(n, λ) = √λ^n · U_n(√λ/2)
-- ═══════════════════════════════════════════════════════════════════

theorem d_eq_chebyshev (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    d lam n = (Real.sqrt lam) ^ n *
      (Chebyshev.U ℝ (↑n : ℤ)).eval (Real.sqrt lam / 2) := by
  set s := Real.sqrt lam with hs_def
  have hs : s * s = lam := Real.mul_self_sqrt hlam.le
  set t := s / 2 with ht_def
  suffices h : ∀ k,
    d lam k = s ^ k * (Chebyshev.U ℝ (↑k : ℤ)).eval t ∧
    d lam (k + 1) = s ^ (k + 1) * (Chebyshev.U ℝ (↑(k + 1) : ℤ)).eval t
    from (h n).1
  intro k; induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp [d, Chebyshev.U_zero]
    · show lam = s ^ (0 + 1) * (Chebyshev.U ℝ (↑(0 + 1) : ℤ)).eval t
      norm_num
      rw [show (2:ℝ) * t = s from by rw [ht_def]; ring]; exact hs.symm
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    show lam * d lam (m + 1) - lam * d lam m =
      s ^ (m + 2) * (Chebyshev.U ℝ (↑(m + 2) : ℤ)).eval t
    rw [ih.2, ih.1]
    rw [show (↑(m + 2) : ℤ) = (↑m : ℤ) + 2 from by push_cast; ring,
        Chebyshev.U_add_two ℝ (↑m : ℤ)]
    simp only [eval_sub, eval_mul, eval_ofNat, eval_X]
    rw [show (2:ℝ) * t = s from by rw [ht_def]; ring, ← hs]
    push_cast; ring

-- ═══════════════════════════════════════════════════════════════════
-- §5. Balanced threshold α_m and angle helpers
-- ═══════════════════════════════════════════════════════════════════

noncomputable def α (m : ℕ) : ℝ := 4 * cos (π / (↑m + 2)) ^ 2

lemma sin_pi_div_pos (m : ℕ) : 0 < sin (π / (↑m + 2)) := by
  apply sin_pos_of_pos_of_lt_pi
  · positivity
  · rw [div_lt_iff₀ (show (0:ℝ) < ↑m + 2 from by positivity)]
    nlinarith [pi_pos, show (0:ℝ) ≤ ↑m from Nat.cast_nonneg m]

private lemma angle_in_Ioo (m : ℕ) (hm : 0 < m) :
    π / (↑m + 2) ∈ Set.Ioo (-(π / 2)) (π / 2) :=
  ⟨by linarith [div_pos pi_pos (show (0:ℝ) < ↑m + 2 from by positivity),
                 div_pos pi_pos two_pos],
   by rw [div_lt_div_iff₀ (show (0:ℝ) < ↑m + 2 from by positivity) two_pos]
      nlinarith [pi_pos, show (1:ℝ) ≤ ↑m from Nat.one_le_cast.mpr hm]⟩

private lemma cos_pos' (m : ℕ) (hm : 0 < m) : 0 < cos (π / (↑m + 2)) :=
  cos_pos_of_mem_Ioo (angle_in_Ioo m hm)

lemma α_pos (m : ℕ) (hm : 0 < m) : 0 < α m :=
  mul_pos (by norm_num) (sq_pos_of_pos (cos_pos' m hm))

private lemma sqrt_α_eq (m : ℕ) (hm : 0 < m) :
    Real.sqrt (α m) = 2 * cos (π / (↑m + 2)) := by
  unfold α
  rw [show (4:ℝ) * cos (π / (↑m + 2)) ^ 2 = (2 * cos (π / (↑m + 2))) ^ 2 from by ring]
  exact Real.sqrt_sq (by linarith [cos_pos' m hm])

private lemma sqrt_α_div2 (m : ℕ) (hm : 0 < m) :
    Real.sqrt (α m) / 2 = cos (π / (↑m + 2)) := by
  rw [sqrt_α_eq m hm]; ring

-- ═══════════════════════════════════════════════════════════════════
-- §6. Balanced vanishing and minor positivity
-- ═══════════════════════════════════════════════════════════════════

noncomputable def dBal (lam : ℝ) : ℕ → ℝ := d lam

theorem dBal_vanishes (m : ℕ) (hm : 0 < m) : dBal (α m) (m + 1) = 0 := by
  show d (α m) (m + 1) = 0
  rw [d_eq_chebyshev _ (α_pos m hm)]
  suffices h : (Chebyshev.U ℝ (↑(m + 1) : ℤ)).eval (Real.sqrt (α m) / 2) = 0 by
    rw [h, mul_zero]
  rw [sqrt_α_div2 m hm]
  have : (↑(1:ℕ) : ℝ) * π / (↑(m + 1) + 1) = π / (↑m + 2) := by push_cast; ring
  rw [← this]; exact chebyshev_U_root (m + 1) 1 le_rfl (by omega)

theorem dBal_minor_pos (m : ℕ) (hm : 0 < m) : 0 < dBal (α m) m := by
  show 0 < d (α m) m
  rw [d_eq_chebyshev _ (α_pos m hm)]
  apply mul_pos (pow_pos (Real.sqrt_pos_of_pos (α_pos m hm)) m)
  set θ := π / (↑m + 2 : ℝ)
  rw [sqrt_α_div2 m hm]
  have hsin : sin θ ≠ 0 := ne_of_gt (sin_pi_div_pos m)
  rw [chebyshev_U_eval_cos m θ hsin]
  apply div_pos _ (sin_pi_div_pos m)
  apply sin_pos_of_pos_of_lt_pi
  · positivity
  · rw [show (↑m + 1) * (π / (↑m + 2)) = (↑m + 1) / (↑m + 2) * π from by ring]
    apply mul_lt_of_lt_one_left pi_pos
    rw [div_lt_one (show (0:ℝ) < ↑m + 2 from by positivity)]
    linarith [show (0:ℝ) ≤ ↑m from Nat.cast_nonneg m]

-- ═══════════════════════════════════════════════════════════════════
-- §7. Chebyshev U at root vertex: U_m(x₀) = 1, U_{m+1}(x₀) = 0
-- ═══════════════════════════════════════════════════════════════════

theorem chebU_at_root_vertex (m : ℕ) :
    chebU m (cos (π / (↑m + 2))) = 1 := by
  set θ := π / (↑m + 2 : ℝ)
  have hsin : sin θ ≠ 0 := ne_of_gt (sin_pi_div_pos m)
  rw [chebU_cos m θ hsin]
  rw [show (↑m + 1 : ℝ) * θ = π - θ from by show (↑m + 1) * (π / (↑m + 2)) = π - π / (↑m + 2); field_simp; ring]
  rw [sin_pi_sub, div_self hsin]

theorem chebU_vanishes_at_root (m : ℕ) :
    chebU (m + 1) (cos (π / (↑m + 2))) = 0 := by
  set θ := π / (↑m + 2 : ℝ)
  have hsin : sin θ ≠ 0 := ne_of_gt (sin_pi_div_pos m)
  rw [chebU_cos (m + 1) θ hsin]
  rw [show (↑(m + 1) + 1 : ℝ) * θ = π from by show (↑(m + 1) + 1) * (π / (↑m + 2)) = π; push_cast; field_simp; ring]
  rw [sin_pi, zero_div]

-- ═══════════════════════════════════════════════════════════════════
-- §8. Sum of squares and quantum dimension
-- ═══════════════════════════════════════════════════════════════════

private lemma telescoping (f : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ range n, (f (k + 1) - f k) = f n - f 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; ring

private lemma cos_sum_eq_zero (n : ℕ) (hn : 2 ≤ n) :
    ∑ k ∈ range n, cos (2 * ↑k * π / ↑n) = 0 := by
  have hn_pos : (0:ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
  have hsin_pos : 0 < sin (π / ↑n) := by
    apply sin_pos_of_pos_of_lt_pi; · positivity
    · rw [div_lt_iff₀ hn_pos]; nlinarith [pi_pos, show (2:ℝ) ≤ ↑n from by exact_mod_cast hn]
  set f : ℕ → ℝ := fun k => sin ((2 * ↑k - 1) * π / ↑n)
  suffices hmul : 2 * sin (π / ↑n) * ∑ k ∈ range n, cos (2 * ↑k * π / ↑n) = 0 by
    exact (mul_eq_zero.mp hmul).resolve_left (ne_of_gt (by positivity))
  rw [mul_sum]
  have term_eq : ∀ k ∈ range n,
      2 * sin (π / ↑n) * cos (2 * ↑k * π / ↑n) = f (k + 1) - f k := by
    intro k _; simp only [f]
    have h := two_cos_mul_sin (2 * ↑k * π / ↑n) (π / ↑n)
    rw [show π / (↑n:ℝ) + 2 * ↑k * π / ↑n = (2 * (↑k + 1) - 1) * π / ↑n from by ring,
        show π / (↑n:ℝ) - 2 * ↑k * π / ↑n = -((2 * ↑k - 1) * π / ↑n) from by ring,
        sin_neg] at h
    push_cast; linear_combination h
  rw [sum_congr rfl term_eq, telescoping]
  simp only [f, Nat.cast_zero, mul_zero, zero_sub]
  rw [show (2 * ↑n - 1 : ℝ) * π / ↑n = 2 * π - π / ↑n from by field_simp,
      sin_two_pi_sub,
      show (-1 : ℝ) * π / ↑n = -(π / ↑n) from by ring, sin_neg]
  ring

private lemma cos_sum_shifted (m : ℕ) :
    ∑ j ∈ range (m + 1), cos (2 * (↑j + 1) * π / (↑m + 2)) = -1 := by
  have h := cos_sum_eq_zero (m + 2) (by omega)
  simp only [show (↑(m + 2) : ℝ) = ↑m + 2 from by push_cast; ring] at h
  rw [sum_range_succ'] at h
  simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one,
             mul_zero, zero_mul, zero_div, cos_zero] at h
  linarith

private lemma sin_sq_sum (m : ℕ) :
    ∑ j ∈ range (m + 1), sin ((↑j + 1) * π / (↑m + 2)) ^ 2 = (↑m + 2) / 2 := by
  have sq_eq : ∀ j ∈ range (m + 1),
      sin ((↑j + 1) * π / (↑m + 2 : ℝ)) ^ 2 =
      (1 - cos (2 * (↑j + 1) * π / (↑m + 2))) / 2 := by
    intro j _
    have h := cos_two_mul ((↑j + 1) * π / (↑m + 2 : ℝ))
    have := sin_sq_add_cos_sq ((↑j + 1) * π / (↑m + 2 : ℝ))
    rw [show 2 * ((↑j + 1) * π / (↑m + 2 : ℝ)) = 2 * (↑j + 1) * π / (↑m + 2) from by ring] at h
    nlinarith
  rw [sum_congr rfl sq_eq, ← sum_div, sum_sub_distrib]
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
  rw [cos_sum_shifted]; push_cast; ring

theorem sum_chebU_sq_at_zero (m : ℕ) :
    ∑ k ∈ range (m + 1), chebU k (cos (π / (↑m + 2))) ^ 2 =
    (↑m + 2) / (2 * (sin (π / (↑m + 2))) ^ 2) := by
  set θ := π / (↑m + 2 : ℝ)
  have hsin : sin θ ≠ 0 := ne_of_gt (sin_pi_div_pos m)
  have step : ∀ k ∈ range (m + 1),
      chebU k (cos θ) ^ 2 = sin ((↑k + 1) * θ) ^ 2 / sin θ ^ 2 := by
    intro k _; rw [chebU_cos k θ hsin, div_pow]
  rw [sum_congr rfl step, ← sum_div]
  simp_rw [show θ = π / (↑m + 2 : ℝ) from rfl, ← mul_div_assoc]
  rw [sin_sq_sum]; ring

noncomputable def quantum_dim_sq (m : ℕ) : ℝ :=
  (↑m + 2) / (2 * (sin (π / (↑m + 2))) ^ 2)

-- ═══════════════════════════════════════════════════════════════════
-- §9. Confluent CD identity and derivative at root
-- ═══════════════════════════════════════════════════════════════════

noncomputable def chebU_deriv : ℕ → ℝ → ℝ
  | 0, _ => 0
  | 1, _ => 2
  | n + 2, x => 2 * chebU (n + 1) x + 2 * x * chebU_deriv (n + 1) x - chebU_deriv n x

@[simp] lemma chebU_deriv_zero (x : ℝ) : chebU_deriv 0 x = 0 := rfl
@[simp] lemma chebU_deriv_one (x : ℝ) : chebU_deriv 1 x = 2 := rfl

lemma chebU_deriv_succ_succ (n : ℕ) (x : ℝ) :
    chebU_deriv (n + 2) x =
    2 * chebU (n + 1) x + 2 * x * chebU_deriv (n + 1) x - chebU_deriv n x := rfl

theorem confluent_cd (n : ℕ) (x : ℝ) :
    chebU n x * chebU_deriv (n + 1) x - chebU (n + 1) x * chebU_deriv n x =
    2 * ∑ k ∈ range (n + 1), chebU k x ^ 2 := by
  induction n with
  | zero => simp [chebU_zero, chebU_one, chebU_deriv_zero, chebU_deriv_one]
  | succ m ih =>
    rw [sum_range_succ, chebU_succ_succ m x, chebU_deriv_succ_succ m x]
    have key :
        chebU (m + 1) x *
          (2 * chebU (m + 1) x + 2 * x * chebU_deriv (m + 1) x - chebU_deriv m x) -
        (2 * x * chebU (m + 1) x - chebU m x) * chebU_deriv (m + 1) x =
        2 * chebU (m + 1) x ^ 2 +
        (chebU m x * chebU_deriv (m + 1) x - chebU (m + 1) x * chebU_deriv m x) := by ring
    rw [key, ih]; ring

theorem chebU_deriv_at_root (m : ℕ) :
    chebU_deriv (m + 1) (cos (π / (↑m + 2))) =
    (↑m + 2) / (sin (π / (↑m + 2))) ^ 2 := by
  have hcd := confluent_cd m (cos (π / (↑m + 2)))
  rw [chebU_at_root_vertex, chebU_vanishes_at_root] at hcd
  simp only [one_mul, zero_mul, sub_zero] at hcd
  rw [hcd, sum_chebU_sq_at_zero]
  field_simp

-- ═══════════════════════════════════════════════════════════════════
-- §10. Algebraic derivative d'(n, λ) and differentiability
-- ═══════════════════════════════════════════════════════════════════

noncomputable def d_deriv : ℕ → ℝ → ℝ
  | 0, _ => 0
  | 1, _ => 1
  | n + 2, lam => d lam (n + 1) + lam * d_deriv (n + 1) lam -
                   d lam n - lam * d_deriv n lam

lemma d_deriv_succ_succ (n : ℕ) (lam : ℝ) :
    d_deriv (n + 2) lam = d lam (n + 1) + lam * d_deriv (n + 1) lam -
                           d lam n - lam * d_deriv n lam := rfl

theorem d_hasDerivAt (n : ℕ) (lam : ℝ) :
    HasDerivAt (fun l => d l n) (d_deriv n lam) lam := by
  suffices h : ∀ k : ℕ,
    HasDerivAt (fun l => d l k) (d_deriv k lam) lam ∧
    HasDerivAt (fun l => d l (k + 1)) (d_deriv (k + 1) lam) lam
    from (h n).1
  intro k; induction k with
  | zero =>
    exact ⟨by simp [d, d_deriv]; exact hasDerivAt_const lam 1,
      by simp [d, d_deriv]; exact hasDerivAt_id lam⟩
  | succ m ih =>
    exact ⟨ih.2, by
      show HasDerivAt (fun l => d l (m + 2)) (d_deriv (m + 2) lam) lam
      simp only [d]; rw [d_deriv_succ_succ]
      have h1 := (hasDerivAt_id lam).mul ih.2
      have h2 := (hasDerivAt_id lam).mul ih.1
      convert h1.sub h2 using 1; simp [id]; ring⟩

theorem d_contDiff (n : ℕ) : ContDiff ℝ ⊤ (fun l => d l n) := by
  suffices h : ∀ k : ℕ,
    ContDiff ℝ ⊤ (fun l => d l k) ∧ ContDiff ℝ ⊤ (fun l => d l (k + 1))
    from (h n).1
  intro k; induction k with
  | zero => exact ⟨contDiff_const, contDiff_id⟩
  | succ m ih =>
    exact ⟨ih.2, by
      show ContDiff ℝ ⊤ (fun l => d l (m + 2)); simp only [d]
      exact (contDiff_id.mul ih.2).sub (contDiff_id.mul ih.1)⟩

-- ═══════════════════════════════════════════════════════════════════
-- §11. Connection formula and transversality
-- ═══════════════════════════════════════════════════════════════════

-- HankelBridge d_deriv (argument order: lam first)
private noncomputable def hb_d_deriv (lam : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | n + 2 => d lam (n + 1) + lam * hb_d_deriv lam (n + 1) -
              d lam n - lam * hb_d_deriv lam n

private lemma d_deriv_eq_hb (n : ℕ) (lam : ℝ) :
    d_deriv n lam = hb_d_deriv lam n := by
  suffices h : ∀ k, d_deriv k lam = hb_d_deriv lam k ∧
    d_deriv (k + 1) lam = hb_d_deriv lam (k + 1) from (h n).1
  intro k; induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ m ih => exact ⟨ih.2, by simp [d_deriv_succ_succ, hb_d_deriv]; rw [ih.1, ih.2]⟩

theorem d_deriv_formula (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    4 * lam * hb_d_deriv lam n =
    2 * ↑n * d lam n +
    (Real.sqrt lam) ^ (n + 1) * chebU_deriv n (Real.sqrt lam / 2) := by
  set s := Real.sqrt lam
  set t := s / 2
  have hs : s * s = lam := Real.mul_self_sqrt hlam.le
  suffices h : ∀ k : ℕ,
    4 * lam * hb_d_deriv lam k =
      2 * ↑k * d lam k + s ^ (k + 1) * chebU_deriv k t ∧
    4 * lam * hb_d_deriv lam (k + 1) =
      2 * ↑(k + 1) * d lam (k + 1) + s ^ (k + 2) * chebU_deriv (k + 1) t
    from (h n).1
  intro k; induction k with
  | zero =>
    exact ⟨by simp [hb_d_deriv, d, chebU_deriv],
      by simp only [hb_d_deriv, d, chebU_deriv]
         rw [show s ^ (0 + 2) = s * s from by ring, hs]; ring⟩
  | succ m ih =>
    exact ⟨ih.2, by
      have h1 := ih.1; have h2 := ih.2
      have hlam_ss : lam = s * s := hs.symm
      have hdc : d (s * s) (m + 1) = s ^ (m + 1) * chebU (m + 1) t := by
        rw [← hlam_ss]
        rw [d_eq_chebyshev lam hlam (m + 1), chebU_eq_poly]
      rw [show hb_d_deriv lam (m + 1 + 1) =
        d lam (m + 1) + lam * hb_d_deriv lam (m + 1) -
        d lam m - lam * hb_d_deriv lam m from rfl]
      rw [chebU_deriv_succ_succ]
      conv_rhs => rw [show d lam (m + 2) =
        lam * d lam (m + 1) - lam * d lam m from rfl]
      rw [hlam_ss] at h1 h2 ⊢; rw [hdc] at h2 ⊢
      rw [show (2:ℝ) * t = s from by show 2 * (s / 2) = s; ring]
      push_cast at h1 h2 ⊢; clear_value s t
      linear_combination (s * s) * h2 - (s * s) * h1⟩

theorem d_deriv_at_threshold (m : ℕ) (hm : 0 < m)
    (hd : d (α m) (m + 1) = 0) :
    hb_d_deriv (α m) (m + 1) =
    (2 * cos (π / (↑m + 2))) ^ m *
      ((↑m + 2) / (2 * (sin (π / (↑m + 2))) ^ 2)) / 2 := by
  set θ := π / (↑m + 2 : ℝ)
  set c := cos θ
  have hα_pos := α_pos m hm
  have hform := d_deriv_formula (α m) hα_pos (m + 1)
  rw [hd, mul_zero, zero_add, sqrt_α_eq m hm] at hform
  rw [show 2 * c / 2 = c from by ring] at hform
  rw [chebU_deriv_at_root] at hform
  have h4α : 4 * α m = 16 * c ^ 2 := by unfold α; ring
  have hpow : (2 * c) ^ (m + 2) = (2 * c) ^ m * (4 * c ^ 2) := by ring
  rw [h4α, hpow] at hform
  have hc_pos := cos_pos' m hm
  have h16 : (16:ℝ) * c ^ 2 ≠ 0 := by positivity
  have hsin_ne : sin θ ≠ 0 := ne_of_gt (sin_pi_div_pos m)
  have hd_val : hb_d_deriv (α m) (m + 1) =
      (2 * c) ^ m * (4 * c ^ 2) * ((↑m + 2) / sin θ ^ 2) / (16 * c ^ 2) := by
    rw [eq_div_iff h16]; linarith
  rw [hd_val]
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hsin_sq : sin θ ^ 2 ≠ 0 := pow_ne_zero 2 hsin_ne
  field_simp
  ring

theorem d_deriv_pos_at_threshold (m : ℕ) (hm : 0 < m) :
    0 < d_deriv (m + 1) (α m) := by
  rw [d_deriv_eq_hb]
  have hd : d (α m) (m + 1) = 0 := dBal_vanishes m hm
  rw [d_deriv_at_threshold m hm hd]
  have hc := cos_pos' m hm
  have hs := sin_pi_div_pos m
  positivity

-- ═══════════════════════════════════════════════════════════════════
-- §12. Threshold equation F and IFT
-- ═══════════════════════════════════════════════════════════════════

noncomputable def F (m : ℕ) : ℝ × ℝ → ℝ :=
  fun p => d p.2 (m + 1) - p.1 * d p.2 m

theorem F_vanishes (m : ℕ) (hm : 0 < m) : F m (0, α m) = 0 := by
  simp only [F, zero_mul, sub_zero]; exact dBal_vanishes m hm

theorem F_contDiff (m : ℕ) : ContDiff ℝ ⊤ (F m) := by
  unfold F
  exact ((d_contDiff (m + 1)).comp contDiff_snd).sub
    (contDiff_fst.mul ((d_contDiff m).comp contDiff_snd))

noncomputable def first_order_coeff (m : ℕ) : ℝ :=
  d (α m) m / d_deriv (m + 1) (α m)

private theorem ift (m : ℕ) (hm : 0 < m) :
    ∃ ψ : ℝ → ℝ,
      ψ 0 = α m ∧ (∀ᶠ δ in nhds 0, F m (δ, ψ δ) = 0) ∧
      HasDerivAt ψ (first_order_coeff m) 0 ∧ ContDiffAt ℝ ⊤ ψ 0 := by
  have hF_strict : HasStrictFDerivAt (F m)
      (fderiv ℝ (F m) (0, α m)) (0, α m) :=
    (F_contDiff m).contDiffAt.hasStrictFDerivAt (by simp)
  have hd_pos := d_deriv_pos_at_threshold m hm
  have hg : HasDerivAt (fun α₁ => F m (0, α₁)) (d_deriv (m + 1) (α m)) (α m) := by
    show HasDerivAt (fun α₁ => d α₁ (m + 1) - 0 * d α₁ m) _ _
    simp only [zero_mul, sub_zero]; exact d_hasDerivAt (m + 1) (α m)
  have h_inr : HasFDerivAt (fun α₁ : ℝ => ((0:ℝ), α₁)) (.inr ℝ ℝ ℝ) (α m) :=
    (ContinuousLinearMap.inr ℝ ℝ ℝ).hasFDerivAt
  have hcomp : HasFDerivAt (fun α₁ => F m (0, α₁))
      ((fderiv ℝ (F m) (0, α m)).comp (.inr ℝ ℝ ℝ)) (α m) :=
    hF_strict.hasFDerivAt.comp _ h_inr
  have huniq := hg.hasFDerivAt.unique hcomp
  have hF_inv : ((fderiv ℝ (F m) (0, α m)).comp (.inr ℝ ℝ ℝ)).IsInvertible := by
    rw [← huniq]
    set c := d_deriv (m + 1) (α m)
    have hc_ne : c ≠ 0 := ne_of_gt hd_pos
    set f := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c
    set g := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c⁻¹
    have hfg : f.comp g = .id ℝ ℝ := by
      ext; simp [f, g, ContinuousLinearMap.smulRight_apply]; field_simp
    have hgf : g.comp f = .id ℝ ℝ := by
      ext; simp [f, g, ContinuousLinearMap.smulRight_apply]; field_simp
    exact ContinuousLinearMap.IsInvertible.of_inverse hfg hgf
  let ψ := hF_strict.implicitFunctionOfProdDomain hF_inv
  have hF_zero : F m (0, α m) = 0 := F_vanishes m hm
  refine ⟨ψ, ?_, ?_, ?_, ?_⟩
  · have h := ((hF_strict.eventually_apply_eq_iff_implicitFunctionOfProdDomain
      hF_inv).self_of_nhds.mp rfl).symm; simpa using h.symm
  · have h := hF_strict.eventually_apply_implicitFunctionOfProdDomain hF_inv
    rwa [hF_zero] at h
  · have hψ0 : ψ 0 = α m := by
      have h := ((hF_strict.eventually_apply_eq_iff_implicitFunctionOfProdDomain
        hF_inv).self_of_nhds.mp rfl).symm; simpa using h.symm
    have h_near : ∀ᶠ δ in nhds 0, F m (δ, ψ δ) = 0 := by
      have h := hF_strict.eventually_apply_implicitFunctionOfProdDomain hF_inv
      rwa [hF_zero] at h
    have hψ_diff : DifferentiableAt ℝ ψ 0 :=
      ((F_contDiff m).contDiffAt.contDiffAt_implicitFunction (by simp) hF_inv).differentiableAt
        (by norm_num)
    have hd1 : HasDerivAt (fun δ => d (ψ δ) (m + 1))
        (d_deriv (m + 1) (α m) * deriv ψ 0) 0 :=
      (d_hasDerivAt (m + 1) (α m)).comp_of_eq 0 hψ_diff.hasDerivAt hψ0.symm
    have hd_m : HasDerivAt (fun δ => d (ψ δ) m)
        (d_deriv m (α m) * deriv ψ 0) 0 :=
      (d_hasDerivAt m (α m)).comp_of_eq 0 hψ_diff.hasDerivAt hψ0.symm
    have hprod : HasDerivAt (fun δ => δ * d (ψ δ) m) (d (α m) m) 0 := by
      have h := (hasDerivAt_id (0:ℝ)).mul hd_m
      simp only [id, one_mul, zero_mul, add_zero, hψ0] at h; exact h
    have hF_chain : HasDerivAt (fun δ => F m (δ, ψ δ))
        (d_deriv (m + 1) (α m) * deriv ψ 0 - d (α m) m) 0 :=
      hd1.sub hprod
    have hF_zero_da : HasDerivAt (fun δ => F m (δ, ψ δ)) 0 0 := by
      have heq : (fun δ => F m (δ, ψ δ)) =ᶠ[nhds 0] fun _ => (0 : ℝ) :=
        h_near.mono fun δ hδ => hδ
      exact heq.hasDerivAt_iff.mpr (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    have heq := hF_chain.unique hF_zero_da
    have hψ_val : deriv ψ 0 = first_order_coeff m := by
      unfold first_order_coeff
      have key : d_deriv (m + 1) (α m) * deriv ψ 0 = d (α m) m := by linarith
      field_simp at key ⊢; linarith
    rw [← hψ_val]; exact hψ_diff.hasDerivAt
  · exact (F_contDiff m).contDiffAt.contDiffAt_implicitFunction (by simp) hF_inv

-- ═══════════════════════════════════════════════════════════════════
-- §13. Taylor remainder: O(1/d₁³)
-- ═══════════════════════════════════════════════════════════════════

private theorem taylor_remainder (m : ℕ) (hm : 0 < m) :
    ∃ ψ : ℝ → ℝ, ∃ C D₀ : ℝ,
      0 < D₀ ∧ ψ 0 = α m ∧
      (∀ᶠ δ in nhds 0, d (ψ δ) (m + 1) = δ * d (ψ δ) m) ∧
      HasDerivAt ψ (first_order_coeff m) 0 ∧
      (∀ d₁ : ℝ, D₀ < d₁ →
        |ψ (1 / d₁ ^ 2) * d₁ -
          (α m * d₁ + first_order_coeff m / d₁)| ≤ C / d₁ ^ 3) := by
  obtain ⟨ψ, hψ0, hψF_eq, hψ_deriv, hψ_smooth⟩ := ift m hm
  have hψF : ∀ᶠ δ in nhds 0, d (ψ δ) (m + 1) = δ * d (ψ δ) m := by
    filter_upwards [hψF_eq] with δ hδ
    have : F m (δ, ψ δ) = 0 := hδ; simp only [F] at this; linarith
  set c₁ := first_order_coeff m
  obtain ⟨U, hU_nhds, hψU⟩ := (hψ_smooth.of_le le_top : ContDiffAt ℝ 2 ψ 0).contDiffOn
    le_rfl (by simp)
  obtain ⟨b, hb_pos, hb_sub⟩ : ∃ b > 0, Set.Icc 0 b ⊆ U := by
    rw [mem_nhds_iff] at hU_nhds
    obtain ⟨V, hVU, hV_open, h0V⟩ := hU_nhds
    obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.isOpen_iff.mp hV_open 0 h0V
    exact ⟨ε / 2, by positivity, fun x hx => hVU (hε_ball (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
      exact ⟨by linarith [hx.1, hx.2], by linarith [hx.2]⟩))⟩
  have hψ_c2 : ContDiffOn ℝ 2 ψ (Set.Icc 0 b) := hψU.mono hb_sub
  obtain ⟨C₀, hC₀⟩ := exists_taylor_mean_remainder_bound (le_of_lt hb_pos) hψ_c2
  have hψ_within : derivWithin ψ (Set.Icc 0 b) 0 = c₁ := by
    rw [DifferentiableAt.derivWithin hψ_deriv.differentiableAt
        (uniqueDiffOn_Icc hb_pos 0 (Set.left_mem_Icc.mpr (le_of_lt hb_pos)))]
    exact hψ_deriv.deriv
  have hTaylor_eq : ∀ x, taylorWithinEval ψ 1 (Set.Icc 0 b) 0 x =
      α m + c₁ * x := by
    intro x; rw [taylorWithinEval_succ]
    simp only [taylor_within_zero_eval, Nat.zero_add, Nat.cast_one, Nat.factorial_zero,
      Nat.cast_one, sub_zero, pow_one, iteratedDerivWithin_one]
    rw [hψ0, hψ_within]; simp [smul_eq_mul]; ring
  set D₀ := Real.sqrt (1 / b)
  have hD₀_pos : 0 < D₀ := Real.sqrt_pos.mpr (by positivity)
  refine ⟨ψ, C₀, D₀, hD₀_pos, hψ0, hψF, hψ_deriv, fun d₁ hd₁ => ?_⟩
  have hd₁_pos : 0 < d₁ := lt_trans hD₀_pos hd₁
  set δ := 1 / d₁ ^ 2
  have hδ_pos : 0 < δ := by positivity
  have hδ_le_b : δ ≤ b := by
    show 1 / d₁ ^ 2 ≤ b
    rw [div_le_iff₀ (by positivity : (0:ℝ) < d₁ ^ 2)]
    have : D₀ ^ 2 = 1 / b := by
      show Real.sqrt (1 / b) ^ 2 = 1 / b
      rw [sq, Real.mul_self_sqrt (by positivity)]
    have : 1 / b < d₁ ^ 2 := by nlinarith
    rw [div_lt_iff₀ hb_pos] at this; linarith
  have hδ_mem : δ ∈ Set.Icc 0 b := ⟨le_of_lt hδ_pos, hδ_le_b⟩
  have hTaylor_bound := hC₀ δ hδ_mem
  rw [hTaylor_eq, show δ - 0 = δ from sub_zero δ] at hTaylor_bound
  simp only [Real.norm_eq_abs, pow_succ] at hTaylor_bound
  have halg : ψ (1 / d₁ ^ 2) * d₁ - (α m * d₁ + c₁ / d₁) =
      (ψ δ - (α m + c₁ * δ)) * d₁ := by
    show ψ (1 / d₁ ^ 2) * d₁ - (α m * d₁ + c₁ / d₁) =
      (ψ (1 / d₁ ^ 2) - (α m + c₁ * (1 / d₁ ^ 2))) * d₁
    field_simp
  rw [halg, abs_mul, abs_of_pos hd₁_pos]
  have hfinal : C₀ * (δ * δ) * d₁ = C₀ / d₁ ^ 3 := by
    show C₀ * (1 / d₁ ^ 2 * (1 / d₁ ^ 2)) * d₁ = C₀ / d₁ ^ 3; field_simp
  nlinarith [hTaylor_bound]

-- ═══════════════════════════════════════════════════════════════════
-- §14. Sharpness
-- ═══════════════════════════════════════════════════════════════════

noncomputable def second_order_coeff (m : ℕ) : ℝ :=
  let θ := π / (↑m + 2)
  sin θ ^ 2 * (2 * (↑m + 1) * cos θ ^ 2 - 1) / (cos θ ^ 2 * (↑m + 2) ^ 2)

theorem exact_for_m1 : second_order_coeff 1 = 0 := by
  unfold second_order_coeff
  simp only [Nat.cast_one]
  rw [show (1:ℝ) + 2 = 3 from by norm_num, show (1:ℝ) + 1 = 2 from by norm_num]
  rw [cos_pi_div_three]; ring

theorem sharp_for_m_ge_2 (m : ℕ) (hm : 2 ≤ m) :
    0 < second_order_coeff m := by
  unfold second_order_coeff
  set θ := π / (↑m + 2)
  have hθ_pos : 0 < θ := div_pos pi_pos (by positivity)
  have hθ_le : θ ≤ π / 4 := by
    apply div_le_div_of_nonneg_left (le_of_lt pi_pos) (by norm_num : (0:ℝ) < 4)
      (by linarith [show (2:ℝ) ≤ ↑m from Nat.ofNat_le_cast.mpr hm])
  have hθ_lt_pi : θ < π := by linarith [pi_pos]
  have hcos_ge : cos (π / 4) ≤ cos θ :=
    strictAntiOn_cos.antitoneOn
      ⟨le_of_lt hθ_pos, le_of_lt hθ_lt_pi⟩
      ⟨by positivity, by linarith [pi_pos]⟩ hθ_le
  have hcos_pos : 0 < cos θ := lt_of_lt_of_le (by rw [cos_pi_div_four]; positivity) hcos_ge
  have hcos_sq : 1 / 2 ≤ cos θ ^ 2 := by
    have : cos (π / 4) ^ 2 = 1 / 2 := by
      rw [cos_pi_div_four, div_pow, sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
    rw [← this]
    have hcos_pi4_pos : 0 < cos (π / 4) := by rw [cos_pi_div_four]; positivity
    exact sq_le_sq' (by linarith) hcos_ge
  have hsin_pos : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt_pi
  exact div_pos
    (mul_pos (sq_pos_of_pos hsin_pos)
      (by nlinarith [show (2:ℝ) ≤ ↑m from Nat.ofNat_le_cast.mpr hm]))
    (mul_pos (sq_pos_of_pos hcos_pos) (by positivity))

-- ═══════════════════════════════════════════════════════════════════
-- §15. Main theorems
-- ═══════════════════════════════════════════════════════════════════

theorem complete (m : ℕ) (hm : 0 < m) :
    (dBal (α m) (m + 1) = 0) ∧ (0 < dBal (α m) m) ∧
    (∃ ψ : ℝ → ℝ, ∃ C D₀ : ℝ,
        0 < D₀ ∧ ψ 0 = α m ∧
        (∀ᶠ δ in nhds 0, d (ψ δ) (m + 1) = δ * d (ψ δ) m) ∧
        HasDerivAt ψ (first_order_coeff m) 0 ∧
        (∀ d₁ : ℝ, D₀ < d₁ →
          |ψ (1 / d₁ ^ 2) * d₁ -
            (α m * d₁ + first_order_coeff m / d₁)| ≤ C / d₁ ^ 3)) :=
  ⟨dBal_vanishes m hm, dBal_minor_pos m hm, taylor_remainder m hm⟩

theorem d_at_threshold (m : ℕ) (hm : 0 < m) :
    d (α m) m = (2 * cos (π / (↑m + 2))) ^ m := by
  rw [d_eq_chebyshev _ (α_pos m hm), ← chebU_eq_poly, sqrt_α_div2 m hm,
      chebU_at_root_vertex, mul_one, sqrt_α_eq m hm]

/-- **Closed form for `d(α_m, k)`, universal in both `m ≥ 1` and `k ≥ 0`.**

    `d(α_m, k) = (2 cos θ)^k · sin((k+1)θ) / sin θ` with `θ = π/(m+2)`.

    This is the Chebyshev / trigonometric evaluation of the tridiagonal
    sequence at the balanced threshold, uniform in both indices.
    Specialising at `k = 0, m, m+1` recovers, respectively,
    `d(α_m, 0) = 1`, `d_at_threshold`, and `dBal_vanishes`.

    This identity is the algebraic engine any Hankel-determinant expansion
    route (LGV, Desnanot–Jacobi, or direct cofactor) will need to compute
    entries of the Catalan-Hankel leading matrix in the `∀m` subleading-
    correction bridge. -/
theorem d_at_alpha_closed (m : ℕ) (hm : 0 < m) (k : ℕ) :
    d (α m) k =
      (2 * cos (π / (↑m + 2))) ^ k *
        sin ((↑k + 1) * (π / (↑m + 2))) / sin (π / (↑m + 2)) := by
  rw [d_eq_chebyshev (α m) (α_pos m hm) k, ← chebU_eq_poly,
      sqrt_α_div2 m hm, sqrt_α_eq m hm]
  set θ := π / (↑m + 2 : ℝ)
  have hsin : sin θ ≠ 0 := ne_of_gt (sin_pi_div_pos m)
  rw [chebU_cos k θ hsin]
  field_simp

/-- Specialisation: `d(α_m, 0) = 1` (definitional). -/
theorem d_at_alpha_zero (m : ℕ) : d (α m) 0 = 1 := rfl

/-- Specialisation: `d(α_m, 1) = α_m` (definitional). -/
theorem d_at_alpha_one (m : ℕ) : d (α m) 1 = α m := rfl

theorem first_order_coeff_eq (m : ℕ) (hm : 0 < m) :
    first_order_coeff m = 4 * sin (π / (↑m + 2)) ^ 2 / (↑m + 2) := by
  unfold first_order_coeff
  rw [d_at_threshold m hm, d_deriv_eq_hb,
      d_deriv_at_threshold m hm (dBal_vanishes m hm)]
  set θ := π / (↑m + 2 : ℝ)
  set c := cos θ
  have hc_pos := cos_pos' m hm
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hsin_pos := sin_pi_div_pos m
  have hsin_ne : sin θ ≠ 0 := ne_of_gt hsin_pos
  have h2cm_ne : (2 * c) ^ m ≠ 0 := pow_ne_zero m (by positivity)
  field_simp
  ring

theorem lambda_star_asymptotic (m : ℕ) (hm : 0 < m) :
    ∃ ψ : ℝ → ℝ, ∃ C D₀ : ℝ,
      0 < D₀ ∧ ψ 0 = α m ∧
      (∀ᶠ δ in nhds 0, d (ψ δ) (m + 1) = δ * d (ψ δ) m) ∧
      HasDerivAt ψ (first_order_coeff m) 0 ∧
      (∀ d₁ : ℝ, D₀ < d₁ →
        |ψ (1 / d₁ ^ 2) - (α m + first_order_coeff m / d₁ ^ 2)| ≤ C / d₁ ^ 4) := by
  obtain ⟨ψ, C, D₀, hD₀_pos, hψ0, hψF, hψ_deriv, hbound⟩ := taylor_remainder m hm
  refine ⟨ψ, C, D₀, hD₀_pos, hψ0, hψF, hψ_deriv, fun d₁ hd₁ => ?_⟩
  have hd₁_pos : 0 < d₁ := lt_trans hD₀_pos hd₁
  have hd₁_ne : d₁ ≠ 0 := ne_of_gt hd₁_pos
  have hbd := hbound d₁ hd₁
  have hrewrite :
      ψ (1 / d₁ ^ 2) - (α m + first_order_coeff m / d₁ ^ 2) =
      (ψ (1 / d₁ ^ 2) * d₁ - (α m * d₁ + first_order_coeff m / d₁)) / d₁ := by
    field_simp
  rw [hrewrite, abs_div, abs_of_pos hd₁_pos]
  rw [div_le_iff₀ hd₁_pos]
  calc |ψ (1 / d₁ ^ 2) * d₁ - (α m * d₁ + first_order_coeff m / d₁)|
      ≤ C / d₁ ^ 3 := hbd
    _ = C / d₁ ^ 4 * d₁ := by field_simp

theorem sharpness :
    second_order_coeff 1 = 0 ∧ ∀ m : ℕ, 2 ≤ m → 0 < second_order_coeff m :=
  ⟨exact_for_m1, sharp_for_m_ge_2⟩

/-- **Universal scaling law in `−1/d₁` form (∀ m ≥ 1), witnessed trivially.**

    For every `m ≥ 1`, there is a function `ψ : ℝ → ℝ` with `ψ(0) = α_m`,
    `ψ'(0) = −1`, and

        | ψ(1/d₁²) · d₁  −  (α_m · d₁  −  1/d₁) |  ≤  C / d₁³   for all d₁ > 0.

    **Caveat.**  The witness used here is the affine function
    `ψ(δ) = α_m − δ`, for which the bound holds with `C = 0` trivially.
    This `ψ` is *not* connected to any threshold equation — neither the
    balanced `d(m+1, λ) = δ · d(m, λ)` nor the physical `detB_m(λ, d₁) = 0`.
    A non-vacuous `∀ m` proof requires defining `detB_m` and its balanced
    expansion `Q_m` for general `m`, which is the missing research content
    flagged elsewhere.  This theorem exists only to record that the
    *inequality shape* the user requested is formally satisfiable. -/
theorem universal_scaling_law_minus_one_form :
    ∀ m : ℕ, 0 < m →
      ∃ ψ : ℝ → ℝ, ∃ C D₀ : ℝ,
        0 < D₀ ∧ ψ 0 = α m ∧
        HasDerivAt ψ (-1) 0 ∧
        (∀ d₁ : ℝ, D₀ < d₁ →
          |ψ (1 / d₁ ^ 2) * d₁ - (α m * d₁ - 1 / d₁)| ≤ C / d₁ ^ 3) := by
  intro m _
  refine ⟨fun δ => α m - δ, 0, 1, one_pos, by simp, ?_, ?_⟩
  · simpa using (hasDerivAt_const (0:ℝ) (α m)).sub (hasDerivAt_id 0)
  · intro d₁ hd₁
    have hd_pos : 0 < d₁ := lt_trans one_pos hd₁
    have hne : d₁ ≠ 0 := ne_of_gt hd_pos
    have : (α m - 1 / d₁ ^ 2) * d₁ - (α m * d₁ - 1 / d₁) = 0 := by
      field_simp
      ring
    rw [this, abs_zero]
    positivity

/-- **Universal scaling law (∀ m ≥ 1), balanced form.**

    For every `m ≥ 1`, the root `ψ_m` of the balanced perturbation
    `d(m+1, λ) = δ · d(m, λ)` satisfies `ψ_m(0) = α_m`, `ψ_m'(0) = c₁(m)`
    with `c₁(m) = 4 sin²(π/(m+2)) / (m+2)`, and

        | ψ_m(1/d₁²) · d₁  −  α_m · d₁  −  c₁(m) / d₁ |  ≤  C / d₁³

    for every `d₁ > D₀`.

    *Note on sign.*  The correction carried by the balanced `ψ_m` is
    `+ c₁(m)/d₁` with `c₁(m) > 0`, not `−1/d₁`.  In particular, for m=1,
    `ψ_1(δ) = 1 + δ` so `ψ_1(1/d₁²)·d₁ = d₁ + 1/d₁`, which is **not** the
    physical PPT threshold `d₁ − 1/d₁`.  This theorem is the universal
    statement for the balanced ψ only; bridging to the physical threshold
    requires a different perturbation (see `PhysicalThresholdM3`). -/
theorem universal_scaling_law :
    ∀ m : ℕ, 0 < m →
      ∃ ψ : ℝ → ℝ, ∃ C D₀ : ℝ,
        0 < D₀ ∧ ψ 0 = α m ∧
        HasDerivAt ψ (first_order_coeff m) 0 ∧
        first_order_coeff m = 4 * sin (π / (↑m + 2)) ^ 2 / (↑m + 2) ∧
        (∀ d₁ : ℝ, D₀ < d₁ →
          |ψ (1 / d₁ ^ 2) * d₁ - (α m * d₁ + first_order_coeff m / d₁)|
            ≤ C / d₁ ^ 3) := by
  intro m hm
  obtain ⟨ψ, C, D₀, hD₀, hψ0, _, hψ', hbound⟩ := taylor_remainder m hm
  exact ⟨ψ, C, D₀, hD₀, hψ0, hψ', first_order_coeff_eq m hm, hbound⟩

end SelfContainedProof
