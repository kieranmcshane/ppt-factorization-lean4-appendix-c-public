import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field

/-!
# Christoffel–Darboux identity for Chebyshev U polynomials

## Scope

Formalises the Christoffel–Darboux summation identity for Chebyshev
polynomials of the second kind U_n, and derives the trace-normalisation
consequence needed by SpectralGeometric.lean:

  (2/(m+2)) sin²(π/(m+2)) · (m+2)/(2 sin²(π/(m+2))) = 1

i.e. root_amplitude_sq(m) × D²(m) = 1, so |ψ̃(0)|²_Tr = 1 for all m.

### Proved here (all sorry-free)
- `chebU` : recursive evaluation U_n(x)
- `chebU_zero/one/two` : base cases
- `cd_kernel_step` : D_{n+1} = D_n + 2(x−y)U_{n+1}(x)U_{n+1}(y)
- `cd_kernel_eq_sum` : D_n = 2(x−y) ∑ U_k(x)U_k(y)  (full induction)
- `cd_identity` : classical CD formula (for x ≠ y)
- `chebU_cos` : U_n(cos θ) = sin((n+1)θ)/sin θ  (pair induction)
- `sum_chebU_sq_at_zero` : ∑ U_k(x_j)² = D²  (sine-sum + roots of unity)
- `trace_normalisation` : algebraic cancellation giving 1

Institut Fourier, Grenoble — Kieran McShane / Cécilia Lancien
-/

open Real Finset

namespace ChristoffelDarboux

-- ═══════════════════════════════════════════════════════════════════
-- §1. Chebyshev U polynomials (evaluated at a point)
-- ═══════════════════════════════════════════════════════════════════

/-- Chebyshev polynomial of the second kind, evaluated:
    U₀(x) = 1,  U₁(x) = 2x,  U_{n+2}(x) = 2x U_{n+1}(x) − U_n(x). -/
noncomputable def chebU : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, x => 2 * x
  | n + 2, x => 2 * x * chebU (n + 1) x - chebU n x

@[simp] lemma chebU_zero (x : ℝ) : chebU 0 x = 1 := rfl
@[simp] lemma chebU_one (x : ℝ) : chebU 1 x = 2 * x := rfl

lemma chebU_succ_succ (n : ℕ) (x : ℝ) :
    chebU (n + 2) x = 2 * x * chebU (n + 1) x - chebU n x := rfl

lemma chebU_two (x : ℝ) : chebU 2 x = 4 * x ^ 2 - 1 := by
  simp only [chebU_succ_succ, chebU_zero]
  rw [chebU_one]
  ring

-- ═══════════════════════════════════════════════════════════════════
-- §2. Christoffel–Darboux kernel (without division)
-- ═══════════════════════════════════════════════════════════════════

/-- The CD kernel: D_n(x,y) = U_{n+1}(x)U_n(y) − U_n(x)U_{n+1}(y).
    Avoids division by 2(x−y); the classical identity is recovered in §4. -/
noncomputable def cd_kernel (n : ℕ) (x y : ℝ) : ℝ :=
  chebU (n + 1) x * chebU n y - chebU n x * chebU (n + 1) y

/-- Inductive step: D_{n+1} = D_n + 2(x−y) U_{n+1}(x) U_{n+1}(y).
    Uses only the three-term recurrence for U. -/
theorem cd_kernel_step (n : ℕ) (x y : ℝ) :
    cd_kernel (n + 1) x y =
    cd_kernel n x y + 2 * (x - y) * chebU (n + 1) x * chebU (n + 1) y := by
  simp only [cd_kernel, chebU_succ_succ n]
  ring

-- ═══════════════════════════════════════════════════════════════════
-- §3. CD identity — integral form (no division, no sorry)
-- ═══════════════════════════════════════════════════════════════════

/-- D_n(x,y) = 2(x−y) ∑_{k=0}^n U_k(x) U_k(y).
    Proved by induction on n using `cd_kernel_step`. -/
theorem cd_kernel_eq_sum (n : ℕ) (x y : ℝ) :
    cd_kernel n x y =
    2 * (x - y) * ∑ k ∈ range (n + 1), chebU k x * chebU k y := by
  induction n with
  | zero =>
    simp only [cd_kernel, chebU_zero, sum_range_succ, sum_range_zero]
    rw [chebU_one, chebU_one]
    ring
  | succ n ih =>
    rw [cd_kernel_step, ih]
    simp only [sum_range_succ]
    ring

-- ═══════════════════════════════════════════════════════════════════
-- §4. Classical CD identity (for x ≠ y, no sorry)
-- ═══════════════════════════════════════════════════════════════════

/-- ∑_{k=0}^n U_k(x) U_k(y) = D_n(x,y) / (2(x−y))  for x ≠ y. -/
theorem cd_identity (n : ℕ) (x y : ℝ) (hxy : x ≠ y) :
    ∑ k ∈ range (n + 1), chebU k x * chebU k y =
    cd_kernel n x y / (2 * (x - y)) := by
  have h : (2 : ℝ) * (x - y) ≠ 0 :=
    mul_ne_zero (by norm_num) (sub_ne_zero.mpr hxy)
  rw [eq_div_iff h, cd_kernel_eq_sum]
  ring

-- ═══════════════════════════════════════════════════════════════════
-- §5. Trigonometric connection (no sorry)
-- ═══════════════════════════════════════════════════════════════════

/-- Product-to-sum: `2 cos a · sin b = sin(b + a) + sin(b − a)`. -/
private lemma two_cos_mul_sin (a b : ℝ) :
    2 * cos a * sin b = sin (b + a) + sin (b - a) := by
  linarith [sin_add b a, sin_sub b a]

/-- U_n(cos θ) = sin((n+1)θ) / sin θ  for sin θ ≠ 0.
    Proof by pair induction using the product-to-sum identity. -/
theorem chebU_cos (n : ℕ) (θ : ℝ) (hθ : sin θ ≠ 0) :
    chebU n (cos θ) = sin ((↑n + 1) * θ) / sin θ := by
  -- Pair induction: prove P(k) ∧ P(k+1) simultaneously
  suffices h : ∀ k : ℕ,
    chebU k (cos θ) = sin ((↑k + 1) * θ) / sin θ ∧
    chebU (k + 1) (cos θ) = sin ((↑(k + 1) + 1) * θ) / sin θ
    from (h n).1
  intro k; induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · -- U₀(cos θ) = 1 = sin θ / sin θ
      rw [chebU_zero, show (↑(0 : ℕ) + 1 : ℝ) * θ = θ from by push_cast; ring]
      exact (div_self hθ).symm
    · -- U₁(cos θ) = 2cos θ = sin(2θ) / sin θ
      rw [chebU_one, show (↑(0 + 1 : ℕ) + 1 : ℝ) * θ = θ + θ from by push_cast; ring,
          sin_add]
      field_simp; ring
  | succ m ih =>
    exact ⟨ih.2, by
      -- U_{m+2}(cos θ) = 2cos θ · U_{m+1}(cos θ) − U_m(cos θ)
      rw [chebU_succ_succ, ih.2, ih.1]
      -- Normalize the cast expressions
      rw [show (↑(m + 1) + 1 : ℝ) = ↑m + 2 from by push_cast; ring,
          show (↑(m + 1 + 1) + 1 : ℝ) = ↑m + 3 from by push_cast; ring]
      field_simp
      -- Goal: 2 cos θ · sin((m+2)θ) − sin((m+1)θ) = sin((m+3)θ)
      have key := two_cos_mul_sin θ ((↑m + 2) * θ)
      rw [show (↑m + 2) * θ + θ = (↑m + 3) * θ from by ring,
          show (↑m + 2) * θ - θ = (↑m + 1) * θ from by ring] at key
      have eq1 : sin ((↑m + 1) * θ) = sin (θ * (↑m + 1)) := by congr 1; ring
      have eq2 : sin ((↑m + 3) * θ) = sin (θ * (↑m + 3)) := by congr 1; ring
      rw [eq1, eq2] at key; linarith⟩

-- ═══════════════════════════════════════════════════════════════════
-- §6. Sum of squares at zeros of U_{m+1} (no sorry)
-- ═══════════════════════════════════════════════════════════════════

/-- Telescoping sum helper. -/
private lemma telescoping (f : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ range n, (f (k + 1) - f k) = f n - f 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; ring

/-- `∑_{k=0}^{n-1} cos(2kπ/n) = 0` for `n ≥ 2` (roots of unity). -/
private lemma cos_sum_eq_zero (n : ℕ) (hn : 2 ≤ n) :
    ∑ k ∈ range n, cos (2 * ↑k * π / ↑n) = 0 := by
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
  have hsin_pos : 0 < sin (π / ↑n) := by
    apply sin_pos_of_pos_of_lt_pi
    · positivity
    · rw [div_lt_iff₀ hn_pos]
      have : (2 : ℝ) ≤ ↑n := by exact_mod_cast hn
      nlinarith [pi_pos]
  -- Telescoping: 2sin(π/n)·cos(2kπ/n) = f(k+1) − f(k) where f(k) = sin((2k−1)π/n)
  set f : ℕ → ℝ := fun k => sin ((2 * ↑k - 1) * π / ↑n) with hf
  suffices hmul : 2 * sin (π / ↑n) * ∑ k ∈ range n, cos (2 * ↑k * π / ↑n) = 0 by
    exact (mul_eq_zero.mp hmul).resolve_left (ne_of_gt (by positivity))
  rw [mul_sum]
  -- Each term equals f(k+1) − f(k)
  have term_eq : ∀ k ∈ range n,
      2 * sin (π / ↑n) * cos (2 * ↑k * π / ↑n) = f (k + 1) - f k := by
    intro k _; simp only [f]
    have h := two_cos_mul_sin (2 * ↑k * π / ↑n) (π / ↑n)
    rw [show π / (↑n : ℝ) + 2 * ↑k * π / ↑n = (2 * (↑k + 1) - 1) * π / ↑n from by ring,
        show π / (↑n : ℝ) - 2 * ↑k * π / ↑n = -((2 * ↑k - 1) * π / ↑n) from by ring,
        sin_neg] at h
    push_cast; linear_combination h
  rw [sum_congr rfl term_eq, telescoping]
  -- f(n) − f(0) = sin((2n−1)π/n) − sin(−π/n)
  simp only [f, Nat.cast_zero, mul_zero, zero_sub]
  -- sin((2n−1)π/n) = sin(2π − π/n) = −sin(π/n)
  have h1 : sin ((2 * ↑n - 1) * π / ↑n) = -sin (π / ↑n) := by
    rw [show (2 * ↑n - 1 : ℝ) * π / ↑n = 2 * π - π / ↑n from by field_simp]
    rw [sin_two_pi_sub]
  -- sin(−π/n) = −sin(π/n)
  have h2 : sin ((-1) * π / ↑n) = -sin (π / ↑n) := by
    rw [show (-1 : ℝ) * π / ↑n = -(π / ↑n) from by ring, sin_neg]
  rw [h1, h2, sub_self]

/-- Shifted cosine sum: `∑_{j=0}^m cos(2(j+1)π/(m+2)) = −1`. -/
private lemma cos_sum_shifted (m : ℕ) :
    ∑ j ∈ range (m + 1), cos (2 * (↑j + 1) * π / (↑m + 2)) = -1 := by
  have h := cos_sum_eq_zero (m + 2) (by omega)
  -- Normalize ↑(m + 2) → ↑m + 2 inside the sum
  simp only [show (↑(m + 2) : ℝ) = ↑m + 2 from by push_cast; ring] at h
  -- Split off k=0 term: ∑_{k=0}^{m+1} f(k) = f(0) + ∑_{j=0}^m f(j+1)
  rw [sum_range_succ'] at h
  -- Simplify the k=0 term and normalize ↑(j+1) → ↑j + 1
  simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one,
             mul_zero, zero_mul, zero_div, cos_zero] at h
  linarith

/-- `∑_{j=1}^{m+1} sin²(jπ/(m+2)) = (m+2)/2`. -/
private lemma sin_sq_sum (m : ℕ) :
    ∑ j ∈ range (m + 1), sin ((↑j + 1) * π / (↑m + 2)) ^ 2 =
    (↑m + 2) / 2 := by
  -- sin²(x) = (1 − cos(2x))/2
  have sq_eq : ∀ j ∈ range (m + 1),
      sin ((↑j + 1) * π / (↑m + 2 : ℝ)) ^ 2 =
      (1 - cos (2 * (↑j + 1) * π / (↑m + 2))) / 2 := by
    intro j _
    have h := cos_two_mul ((↑j + 1) * π / (↑m + 2 : ℝ))
    -- cos(2x) = 1 − 2sin²(x)
    have := sin_sq_add_cos_sq ((↑j + 1) * π / (↑m + 2 : ℝ))
    rw [show 2 * ((↑j + 1) * π / (↑m + 2 : ℝ)) = 2 * (↑j + 1) * π / (↑m + 2) from by ring] at h
    nlinarith
  rw [sum_congr rfl sq_eq, ← Finset.sum_div, sum_sub_distrib]
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
  rw [cos_sum_shifted]
  push_cast; ring

/-- At x = cos(π/(m+2)), a zero of U_{m+1}, we have
      ∑_{k=0}^m U_k(x)² = (m+2) / (2 sin²(π/(m+2))).
    Proved using `chebU_cos` and the sine-sum identity. -/
theorem sum_chebU_sq_at_zero (m : ℕ) :
    ∑ k ∈ range (m + 1), chebU k (cos (π / (↑m + 2))) ^ 2 =
    (↑m + 2) / (2 * (sin (π / (↑m + 2))) ^ 2) := by
  set θ := π / (↑m + 2 : ℝ) with hθ_def
  have hsin : sin θ ≠ 0 := by
    apply ne_of_gt; apply sin_pos_of_pos_of_lt_pi
    · positivity
    · rw [hθ_def, div_lt_iff₀ (show (0:ℝ) < ↑m + 2 from by positivity)]
      nlinarith [pi_pos, show (0:ℝ) ≤ ↑m from Nat.cast_nonneg m]
  -- Rewrite each term using chebU_cos
  have step : ∀ k ∈ range (m + 1),
      chebU k (cos θ) ^ 2 = sin ((↑k + 1) * θ) ^ 2 / sin θ ^ 2 := by
    intro k _; rw [chebU_cos k θ hsin, div_pow]
  rw [sum_congr rfl step, ← Finset.sum_div]
  simp_rw [hθ_def, ← mul_div_assoc]
  rw [sin_sq_sum]
  ring

-- ═══════════════════════════════════════════════════════════════════
-- §7. Squared quantum dimension
-- ═══════════════════════════════════════════════════════════════════

/-- D²(m) = (m+2) / (2 sin²(π/(m+2))) = ∑_{k=0}^m U_k(cos(π/(m+2)))².
    The Perron–Frobenius squared dimension of the A_{m+1} principal graph. -/
noncomputable def quantum_dim_sq (m : ℕ) : ℝ :=
  (↑m + 2) / (2 * (sin (π / (↑m + 2))) ^ 2)

-- ═══════════════════════════════════════════════════════════════════
-- §8. Trace normalisation (no sorry)
-- ═══════════════════════════════════════════════════════════════════

/-- The Christoffel–Darboux normalisation:
      root_amplitude_sq(m) × D²(m) = 1.
    Algebraic cancellation:
      (2/(m+2)) sin²(π/(m+2)) · (m+2)/(2 sin²(π/(m+2))) = 1.
    This is eq (11.8) in the notes: |ψ̃(0)|²_Tr = 1 for all m. -/
theorem trace_normalisation (m : ℕ) :
    2 / (↑m + 2) * (sin (π / (↑m + 2))) ^ 2 * quantum_dim_sq m = 1 := by
  unfold quantum_dim_sq
  have hm : (↑m + 2 : ℝ) ≠ 0 := by positivity
  have hs : sin (π / (↑m + 2)) ≠ 0 := by
    apply ne_of_gt
    apply sin_pos_of_pos_of_lt_pi
    · positivity
    · exact div_lt_self pi_pos (by linarith [Nat.cast_nonneg (α := ℝ) m])
  field_simp

-- ═══════════════════════════════════════════════════════════════════
-- §9. Chebyshev U values at the root x₀ = cos(π/(m+2))
-- ═══════════════════════════════════════════════════════════════════

/-- Helper: sin(π/(m+2)) > 0. -/
lemma sin_pi_div_pos (m : ℕ) : 0 < sin (π / (↑m + 2)) := by
  apply sin_pos_of_pos_of_lt_pi
  · positivity
  · rw [div_lt_iff₀ (show (0:ℝ) < ↑m + 2 from by positivity)]
    nlinarith [pi_pos, show (0:ℝ) ≤ ↑m from Nat.cast_nonneg m]

/-- U_m(cos(π/(m+2))) = 1.
    Proof: U_m(cos θ) = sin((m+1)θ)/sin θ, and (m+1)·π/(m+2) = π − π/(m+2),
    so sin((m+1)θ) = sin(π/(m+2)) = sin θ. -/
theorem chebU_at_root_vertex (m : ℕ) :
    chebU m (cos (π / (↑m + 2))) = 1 := by
  set θ := π / (↑m + 2 : ℝ) with hθ_def
  have hsin : sin θ ≠ 0 := ne_of_gt (sin_pi_div_pos m)
  rw [chebU_cos m θ hsin]
  have hshift : (↑m + 1 : ℝ) * θ = π - θ := by
    rw [hθ_def]; field_simp; ring
  rw [hshift, sin_pi_sub, div_self hsin]

/-- U_{m+1}(cos(π/(m+2))) = 0.
    Proof: sin((m+2)·π/(m+2)) = sin(π) = 0. -/
theorem chebU_vanishes_at_root (m : ℕ) :
    chebU (m + 1) (cos (π / (↑m + 2))) = 0 := by
  set θ := π / (↑m + 2 : ℝ) with hθ_def
  have hsin : sin θ ≠ 0 := ne_of_gt (sin_pi_div_pos m)
  rw [chebU_cos (m + 1) θ hsin]
  have hshift : (↑(m + 1) + 1 : ℝ) * θ = π := by
    rw [hθ_def]; push_cast; field_simp; ring
  rw [hshift, sin_pi, zero_div]

-- ═══════════════════════════════════════════════════════════════════
-- §10. Algebraic derivative of Chebyshev U
-- ═══════════════════════════════════════════════════════════════════

/-- Algebraic derivative of U_n(x), defined by differentiating the
    three-term recurrence:
      U₀' = 0,  U₁' = 2,  U'_{n+2} = 2U_{n+1} + 2x·U'_{n+1} − U'_n. -/
noncomputable def chebU_deriv : ℕ → ℝ → ℝ
  | 0, _ => 0
  | 1, _ => 2
  | n + 2, x => 2 * chebU (n + 1) x + 2 * x * chebU_deriv (n + 1) x - chebU_deriv n x

@[simp] lemma chebU_deriv_zero (x : ℝ) : chebU_deriv 0 x = 0 := rfl
@[simp] lemma chebU_deriv_one (x : ℝ) : chebU_deriv 1 x = 2 := rfl

lemma chebU_deriv_succ_succ (n : ℕ) (x : ℝ) :
    chebU_deriv (n + 2) x =
    2 * chebU (n + 1) x + 2 * x * chebU_deriv (n + 1) x - chebU_deriv n x := rfl

-- ═══════════════════════════════════════════════════════════════════
-- §11. Confluent Christoffel–Darboux identity
--      U_n · U'_{n+1} − U_{n+1} · U'_n = 2 ∑_{k=0}^n U_k²
-- ═══════════════════════════════════════════════════════════════════

/-- **Confluent CD identity.**
    U_n(x) · U'_{n+1}(x) − U_{n+1}(x) · U'_n(x) = 2 ∑_{k=0}^n U_k(x)².
    Obtained by differentiating the CD kernel D_n(x,y) and setting y → x,
    or equivalently by induction using the differentiated recurrence. -/
theorem confluent_cd (n : ℕ) (x : ℝ) :
    chebU n x * chebU_deriv (n + 1) x - chebU (n + 1) x * chebU_deriv n x =
    2 * ∑ k ∈ range (n + 1), chebU k x ^ 2 := by
  induction n with
  | zero =>
    simp only [chebU_zero, chebU_deriv_zero,
               sum_range_succ, sum_range_zero, Nat.zero_add,
               chebU_deriv_one, chebU_one]
    ring
  | succ m ih =>
    rw [sum_range_succ]
    rw [chebU_succ_succ m x, chebU_deriv_succ_succ m x]
    -- Expand and collect: the LHS decomposes into the IH plus 2·U_{m+1}²
    have key :
        chebU (m + 1) x *
          (2 * chebU (m + 1) x + 2 * x * chebU_deriv (m + 1) x - chebU_deriv m x) -
        (2 * x * chebU (m + 1) x - chebU m x) * chebU_deriv (m + 1) x =
        2 * chebU (m + 1) x ^ 2 +
        (chebU m x * chebU_deriv (m + 1) x - chebU (m + 1) x * chebU_deriv m x) := by ring
    rw [key, ih]
    ring

-- ═══════════════════════════════════════════════════════════════════
-- §12. Derivative of U_{m+1} at the root
--      U'_{m+1}(x₀) = (m+2) / sin²(π/(m+2)) = 2D²
-- ═══════════════════════════════════════════════════════════════════

/-- **Derivative at the root.**
    U'_{m+1}(cos(π/(m+2))) = (m+2) / sin²(π/(m+2)) = 2 D²(m).

    Proof: by `confluent_cd` with U_m(x₀)=1 and U_{m+1}(x₀)=0,
    LHS = 1 · U'_{m+1}(x₀) − 0 = U'_{m+1}(x₀),
    RHS = 2 ∑ U_k(x₀)² = 2 · (m+2)/(2 sin²(π/(m+2))). -/
theorem chebU_deriv_at_root (m : ℕ) :
    chebU_deriv (m + 1) (cos (π / (↑m + 2))) =
    (↑m + 2) / (sin (π / (↑m + 2))) ^ 2 := by
  have hcd := confluent_cd m (cos (π / (↑m + 2)))
  rw [chebU_at_root_vertex, chebU_vanishes_at_root] at hcd
  simp only [one_mul, zero_mul, sub_zero] at hcd
  rw [hcd, sum_chebU_sq_at_zero]
  have hsin : sin (π / (↑m + 2)) ≠ 0 := ne_of_gt (sin_pi_div_pos m)
  field_simp

/-- Equivalent formulation: U'_{m+1}(x₀) = 2 · D²(m). -/
theorem chebU_deriv_at_root' (m : ℕ) :
    chebU_deriv (m + 1) (cos (π / (↑m + 2))) = 2 * quantum_dim_sq m := by
  rw [chebU_deriv_at_root]; unfold quantum_dim_sq
  have hsin : sin (π / (↑m + 2)) ≠ 0 := ne_of_gt (sin_pi_div_pos m)
  field_simp

end ChristoffelDarboux
