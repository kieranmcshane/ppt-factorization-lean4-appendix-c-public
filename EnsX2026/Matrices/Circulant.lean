import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# ENS/Polytechnique 2026 Math A — Q22, Q23, Q24

We define the cyclic-graph Laplacian

`C_n = 2 I_n − J_n − J_n⁻¹`,

where `J_n` is the cyclic shift, as a circulant matrix over `ZMod n`,
diagonalise it via the discrete Fourier basis, and read off its spectrum

`{ 4 sin²(π (p−1)/n) : p ∈ [1,n] } = { 2 − 2 cos(2π p / n) : p ∈ ZMod n }`.

Mathlib contains `Matrix.circulant` (definition and basic algebraic lemmas)
but has **no** DFT / Fourier diagonalisation of circulant matrices. This file
therefore acts both as the answer to Q22–24 and as a small reusable circulant
diagonalisation library, built from scratch.

## Hypothesis on `n`

We work under `3 ≤ n` throughout. The edge case `n = 2` is genuinely awkward
because in `ZMod 2` we have `1 = −1`, so the off-diagonal pattern
`v(1) = v(−1) = −1` "double-counts" and would change the matrix entries.
Mirroring the exam, which always assumes `n ≥ 3`, we adopt the same
convention. With `3 ≤ n`, the residues `0, 1, −1 ∈ ZMod n` are distinct,
hence the definition is unambiguous.

Institut Fourier, Grenoble — Kieran McShane
-/

noncomputable section

namespace EnsX2026.Matrices.Circulant

open Matrix Complex

/-! ### Cyclic shift and Laplacian -/

/-- The cyclic shift matrix `J_n`, expressed as a circulant. -/
def shift_matrix (n : ℕ) : Matrix (ZMod n) (ZMod n) ℂ :=
  Matrix.circulant (fun k : ZMod n => if k = 1 then (1 : ℂ) else 0)

/-- The "inverse" shift matrix, `J_n⁻¹` realised as a circulant. -/
def shift_matrix_inv (n : ℕ) : Matrix (ZMod n) (ZMod n) ℂ :=
  Matrix.circulant (fun k : ZMod n => if k = -1 then (1 : ℂ) else 0)

/-- The cyclic-graph Laplacian on `n` vertices, expressed as a circulant. -/
def cycle_laplacian (n : ℕ) (_hn : 3 ≤ n) : Matrix (ZMod n) (ZMod n) ℂ :=
  Matrix.circulant (fun k : ZMod n =>
    if k = 0 then 2
    else if k = 1 ∨ k = -1 then -1
    else 0)

/-! ### Distinctness of `0, 1, -1` in `ZMod n` for `n ≥ 3` -/

section Distinctness

variable {n : ℕ}

lemma zero_ne_one_of_three_le (hn : 3 ≤ n) : (0 : ZMod n) ≠ 1 := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : Fact (1 < n) := ⟨by omega⟩
  intro h
  have : ((0 : ZMod n)).val = (1 : ZMod n).val := by rw [h]
  rw [ZMod.val_zero, ZMod.val_one] at this
  exact absurd this (by omega)

lemma zero_ne_neg_one_of_three_le (hn : 3 ≤ n) : (0 : ZMod n) ≠ -1 := by
  haveI : NeZero n := ⟨by omega⟩
  intro h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hv : (-1 : ZMod (m + 1)).val = m := ZMod.val_neg_one m
  have : ((0 : ZMod (m + 1))).val = (-1 : ZMod (m + 1)).val := by rw [h]
  rw [ZMod.val_zero, hv] at this
  -- this : 0 = m, and n = m + 1, so m = 0 means n = 1, contradicts n ≥ 3.
  omega

lemma one_ne_neg_one_of_three_le (hn : 3 ≤ n) : (1 : ZMod n) ≠ -1 := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : Fact (1 < n) := ⟨by omega⟩
  intro h
  -- 1 = -1 ⟹ 2 = 0 in ZMod n ⟹ n | 2 ⟹ n ≤ 2, contradiction.
  have h2 : (2 : ZMod n) = 0 := by
    have e : (1 : ZMod n) + 1 = 0 := by
      nth_rewrite 1 [h]; ring
    have h21 : (2 : ZMod n) = 1 + 1 := by ring
    rw [h21]; exact e
  have h2nat : ((2 : ℕ) : ZMod n) = 0 := by exact_mod_cast h2
  have hdvd : n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 n).mp h2nat
  have : n ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

end Distinctness

/-- For `3 ≤ n`, the cyclic Laplacian agrees with `2 • I − J_n − J_n⁻¹`. -/
theorem cycle_laplacian_eq (n : ℕ) (hn : 3 ≤ n) :
    cycle_laplacian n hn =
      (2 : ℂ) • (1 : Matrix (ZMod n) (ZMod n) ℂ)
        - shift_matrix n - shift_matrix_inv n := by
  haveI : NeZero n := ⟨by omega⟩
  have h01 : (0 : ZMod n) ≠ 1 := zero_ne_one_of_three_le hn
  have h0m1 : (0 : ZMod n) ≠ -1 := zero_ne_neg_one_of_three_le hn
  have h1m1 : (1 : ZMod n) ≠ -1 := one_ne_neg_one_of_three_le hn
  unfold cycle_laplacian shift_matrix shift_matrix_inv
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.circulant_apply, smul_eq_mul]
  -- Distinctness: handy rewrites for `if`-elims.
  have h10 : (1 : ZMod n) ≠ 0 := fun h => h01 h.symm
  have hm10 : (-1 : ZMod n) ≠ 0 := fun h => h0m1 h.symm
  have hm11 : (-1 : ZMod n) ≠ 1 := fun h => h1m1 h.symm
  by_cases h0 : i - j = 0
  · rw [h0]
    have hij : i = j := sub_eq_zero.mp h0
    subst hij
    simp [h01, h0m1]
  · have hne : (i : ZMod n) ≠ j := fun hij => h0 (by rw [hij]; ring)
    by_cases h1 : i - j = 1
    · rw [h1]
      simp [h10, h1m1, hne]
    · by_cases hm1 : i - j = -1
      · rw [hm1]
        simp [hm10, hm11, hne]
      · simp [h0, h1, hm1, hne]

/-! ### A key computational lemma: powers of an `n`-th root on `ZMod n` values -/

/-- If `ω ^ n = 1`, then for `x : ℕ`, `ω^x = ω^(x % n)`. -/
lemma pow_mod_n_eq {n : ℕ} {ω : ℂ} (hω : ω ^ n = 1) (x : ℕ) :
    ω ^ x = ω ^ (x % n) := by
  conv_lhs => rw [← Nat.mod_add_div x n, pow_add, pow_mul, hω, one_pow, mul_one]

/-- Power of an `n`-th root of unity on values of `ZMod n` is additive
under addition of residues. -/
lemma pow_val_add {n : ℕ} [NeZero n] {ω : ℂ} (hω : ω ^ n = 1) (a b : ZMod n) :
    ω ^ (a + b).val = ω ^ a.val * ω ^ b.val := by
  rw [ZMod.val_add, ← pow_mod_n_eq hω, pow_add]

/-! ### Primitive `n`-th root of unity `ω := exp(2πi/n)` -/

/-- `ω_n := exp(2π i / n)`, a primitive `n`-th root of unity. -/
def omega_root (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * I / n)

/-- `ω_n ≠ 0`. -/
lemma omega_root_ne_zero (n : ℕ) : omega_root n ≠ 0 := Complex.exp_ne_zero _

/-- `ω_n^n = 1`. -/
lemma omega_root_pow_n (n : ℕ) (hn : 1 ≤ n) : (omega_root n) ^ n = 1 := by
  unfold omega_root
  rw [← Complex.exp_nat_mul]
  have hn_ne : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
  have : (n : ℂ) * (2 * Real.pi * I / n) = 2 * Real.pi * I := by field_simp
  rw [this, Complex.exp_two_pi_mul_I]

/-! ### The Fourier modes (Q23) -/

/-- The `p`-th Fourier mode: `v_p(k) = ω_n^(p.val · k.val)`. -/
def fourier_mode (n : ℕ) (p : ZMod n) : (ZMod n) → ℂ :=
  fun k => (omega_root n) ^ (p.val * k.val)

/-- Reformulation in terms of `Complex.exp`. -/
lemma fourier_mode_eq (n : ℕ) (p : ZMod n) (k : ZMod n) :
    fourier_mode n p k =
      Complex.exp (2 * Real.pi * I * (p.val * k.val) / n) := by
  unfold fourier_mode omega_root
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-! ### Shift-eigenvector lemma for an arbitrary circulant indicator

Having a uniform version avoids repeating the proof for `shift_matrix` and
`shift_matrix_inv`. -/

/-- For a target residue `c : ZMod n` and a function `φ : ZMod n → ℂ`, the
matrix-vector product `(circulant [k = c]) φ` evaluated at `i` equals
`φ(i - c)`. -/
private lemma circulant_indicator_mulVec (n : ℕ) [NeZero n]
    (c : ZMod n) (φ : (ZMod n) → ℂ) (i : ZMod n) :
    (Matrix.circulant (fun k : ZMod n => if k = c then (1 : ℂ) else 0)).mulVec
        φ i = φ (i - c) := by
  simp only [Matrix.mulVec, Matrix.circulant_apply, dotProduct]
  -- Reindex via `Equiv.subLeft i`: `j ↦ i - j`.
  rw [show (∑ j, (if i - j = c then (1 : ℂ) else 0) * φ j)
        = ∑ j, (if j = c then (1 : ℂ) else 0) * φ (i - j) from by
    refine Fintype.sum_equiv (Equiv.subLeft i) _ _ (fun j => ?_)
    simp]
  rw [Finset.sum_eq_single c]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; simp at h

/-! ### Fourier eigenvectors of the shift (Q23) -/

/-- (Q23) The Fourier mode `v_p` is an eigenvector of the shift `J_n` for
eigenvalue `ω_n^{(-p).val} = exp(-2π i p / n)`.

**Note on sign convention.** With Mathlib's definition
`(circulant w) i j = w (i - j)`, the shift `J_n = circulant (k ↦ [k = 1])`
acts on a function `φ : ZMod n → ℂ` by `(J_n φ)(i) = φ(i - 1)`. Thus the
associated eigenvalue on `v_p(k) = ω^{p k}` is `ω^{-p}`. -/
theorem fourier_mode_eigenvector_shift (n : ℕ) [NeZero n] (p : ZMod n) :
    (shift_matrix n).mulVec (fourier_mode n p) =
      (omega_root n) ^ ((-p).val) • (fourier_mode n p) := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hω := omega_root_pow_n n hn
  have hω_ne := omega_root_ne_zero n
  funext i
  unfold shift_matrix
  rw [circulant_indicator_mulVec n 1 (fourier_mode n p) i]
  -- Goal: φ(i - 1) = ω^((-p).val) * φ(i).
  show fourier_mode n p (i - 1) = (omega_root n ^ ((-p).val)) * fourier_mode n p i
  -- Use pow_val_add: ω^((a + b).val) = ω^a.val * ω^b.val on appropriate residues.
  -- Key identity: (-p) + p = 0, so ω^(-p).val * ω^p.val = ω^0.val = 1.
  have hsum_neg :
      omega_root n ^ ((-p).val) * omega_root n ^ p.val = 1 := by
    have h := pow_val_add hω (-p) p
    have h0 : ((-p) + p : ZMod n) = 0 := by ring
    rw [h0] at h
    simpa using h.symm
  -- We will show:  ω^(p.val * (i - 1).val) * ω^p.val = ω^(p.val * i.val)
  -- then multiply by ω^((-p).val) on the left to conclude.
  have step_shift :
      omega_root n ^ (p.val * (i - 1).val) * omega_root n ^ p.val =
      omega_root n ^ (p.val * i.val) := by
    -- (i - 1) + 1 = i, so by pow_val_add:
    -- ω^((i-1) + 1).val = ω^(i-1).val * ω^(1).val, hence ω^(i.val) = ω^(i-1).val * ω^(1).val
    have baseIdent : omega_root n ^ i.val =
        omega_root n ^ (i - 1).val * omega_root n ^ (1 : ZMod n).val := by
      have := pow_val_add hω (i - 1) 1
      simpa using this
    -- Raise both sides to p.val-th power.
    have raised :
        omega_root n ^ (p.val * i.val) =
        omega_root n ^ (p.val * (i - 1).val)
          * omega_root n ^ (p.val * (1 : ZMod n).val) := by
      calc omega_root n ^ (p.val * i.val)
          = (omega_root n ^ i.val) ^ p.val := by
              rw [mul_comm p.val i.val, pow_mul]
        _ = (omega_root n ^ (i - 1).val * omega_root n ^ (1 : ZMod n).val) ^ p.val := by
              rw [baseIdent]
        _ = (omega_root n ^ (i - 1).val) ^ p.val
              * (omega_root n ^ (1 : ZMod n).val) ^ p.val := by rw [mul_pow]
        _ = omega_root n ^ ((i - 1).val * p.val)
              * omega_root n ^ ((1 : ZMod n).val * p.val) := by rw [← pow_mul, ← pow_mul]
        _ = omega_root n ^ (p.val * (i - 1).val)
              * omega_root n ^ (p.val * (1 : ZMod n).val) := by
              rw [mul_comm (i - 1).val p.val, mul_comm (1 : ZMod n).val p.val]
    -- Now relate ω^(p.val * (1:ZMod n).val) to ω^p.val via ω^n = 1.
    have pow_one :
        omega_root n ^ (p.val * (1 : ZMod n).val) = omega_root n ^ p.val := by
      rw [ZMod.val_one_eq_one_mod]
      -- Goal: ω^(p.val * (1 % n)) = ω^p.val
      -- Use pow_mod_n_eq twice.
      rw [pow_mod_n_eq hω, pow_mod_n_eq hω p.val]
      congr 1
      rcases eq_or_lt_of_le hn with h | h
      · -- n = 1: 1 % 1 = 0, p.val % 1 = 0, p.val * 0 = 0, so both sides have exponent 0.
        subst h
        simp [Nat.mod_one]
      · -- n ≥ 2: 1 % n = 1, so p.val * 1 = p.val.
        have hone : 1 % n = 1 := Nat.mod_eq_of_lt h
        rw [hone, mul_one]
    rw [raised, pow_one]
  -- Now chain:
  -- φ(i-1) = ω^(p.val * (i-1).val)
  --        = 1 * ω^(p.val * (i-1).val)
  --        = (ω^(-p).val * ω^(p.val)) * ω^(p.val * (i-1).val)
  --        = ω^(-p).val * (ω^(p.val * (i-1).val) * ω^(p.val))
  --        = ω^(-p).val * ω^(p.val * i.val)
  --        = ω^(-p).val * φ(i).
  unfold fourier_mode
  calc omega_root n ^ (p.val * (i - 1).val)
      = 1 * omega_root n ^ (p.val * (i - 1).val) := by ring
    _ = (omega_root n ^ ((-p).val) * omega_root n ^ p.val)
          * omega_root n ^ (p.val * (i - 1).val) := by rw [hsum_neg]
    _ = omega_root n ^ ((-p).val)
          * (omega_root n ^ (p.val * (i - 1).val) * omega_root n ^ p.val) := by ring
    _ = omega_root n ^ ((-p).val) * omega_root n ^ (p.val * i.val) := by rw [step_shift]

/-- Analogous eigenvector property for `J_n⁻¹`: eigenvalue `ω_n^p.val`. -/
theorem fourier_mode_eigenvector_shift_inv (n : ℕ) [NeZero n] (p : ZMod n) :
    (shift_matrix_inv n).mulVec (fourier_mode n p) =
      (omega_root n) ^ p.val • (fourier_mode n p) := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hω := omega_root_pow_n n hn
  funext i
  unfold shift_matrix_inv
  rw [circulant_indicator_mulVec n (-1) (fourier_mode n p) i]
  show fourier_mode n p (i - (-1)) = (omega_root n ^ p.val) * fourier_mode n p i
  -- i - (-1) = i + 1.
  have hi1 : i - (-1 : ZMod n) = i + 1 := by ring
  rw [hi1]
  unfold fourier_mode
  -- ω^(p.val * (i+1).val) = ω^(p.val * i.val) * ω^(p.val).
  have baseIdent : omega_root n ^ (i + 1).val =
      omega_root n ^ i.val * omega_root n ^ (1 : ZMod n).val := by
    have := pow_val_add hω i 1
    simpa using this
  have raised :
      omega_root n ^ (p.val * (i + 1).val) =
      omega_root n ^ (p.val * i.val)
        * omega_root n ^ (p.val * (1 : ZMod n).val) := by
    calc omega_root n ^ (p.val * (i + 1).val)
        = (omega_root n ^ (i + 1).val) ^ p.val := by
            rw [mul_comm p.val (i + 1).val, pow_mul]
      _ = (omega_root n ^ i.val * omega_root n ^ (1 : ZMod n).val) ^ p.val := by
            rw [baseIdent]
      _ = (omega_root n ^ i.val) ^ p.val
            * (omega_root n ^ (1 : ZMod n).val) ^ p.val := by rw [mul_pow]
      _ = omega_root n ^ (i.val * p.val)
            * omega_root n ^ ((1 : ZMod n).val * p.val) := by rw [← pow_mul, ← pow_mul]
      _ = omega_root n ^ (p.val * i.val)
            * omega_root n ^ (p.val * (1 : ZMod n).val) := by
            rw [mul_comm i.val p.val, mul_comm (1 : ZMod n).val p.val]
  have pow_one :
      omega_root n ^ (p.val * (1 : ZMod n).val) = omega_root n ^ p.val := by
    rw [ZMod.val_one_eq_one_mod]
    rw [pow_mod_n_eq hω, pow_mod_n_eq hω p.val]
    congr 1
    rcases eq_or_lt_of_le hn with h | h
    · subst h
      simp [Nat.mod_one]
    · have hone : 1 % n = 1 := Nat.mod_eq_of_lt h
      rw [hone, mul_one]
  rw [raised, pow_one, mul_comm]

/-! ### Spectrum of `cycle_laplacian` (Q24) -/

/-- (Q24) The Fourier mode `v_p` is an eigenvector of the cyclic Laplacian
`C_n = 2 I − J − J⁻¹` for eigenvalue `2 − 2 cos(2π p / n)`. -/
theorem cycle_laplacian_eigenvalue (n : ℕ) (hn : 3 ≤ n) (p : ZMod n) :
    haveI : NeZero n := ⟨by omega⟩
    (cycle_laplacian n hn).mulVec (fourier_mode n p) =
      ((2 : ℂ) - 2 * Complex.cos (2 * Real.pi * p.val / n)) • fourier_mode n p := by
  haveI : NeZero n := ⟨by omega⟩
  rw [cycle_laplacian_eq n hn, Matrix.sub_mulVec, Matrix.sub_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec,
      fourier_mode_eigenvector_shift n p,
      fourier_mode_eigenvector_shift_inv n p]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  -- Goal: 2 * v(i) - ω^(-p).val * v(i) - ω^p.val * v(i)
  --     = (2 - 2 cos(2π p/n)) * v(i)
  have hω := omega_root_pow_n n (by omega : 1 ≤ n)
  have hω_ne := omega_root_ne_zero n
  -- Step 1: ω^p.val = exp(θ * I) where θ = 2π p.val / n.
  set θ : ℂ := 2 * Real.pi * p.val / n with hθdef
  have hωp : omega_root n ^ p.val = Complex.exp (θ * I) := by
    unfold omega_root
    rw [← Complex.exp_nat_mul]
    congr 1
    simp only [θ]
    ring
  -- Step 2: ω^(-p).val = exp(-θ * I). Use: ω^(-p).val * ω^p.val = 1.
  have hsum_neg : omega_root n ^ ((-p).val) * omega_root n ^ p.val = 1 := by
    have h := pow_val_add hω (-p) p
    have h0 : ((-p) + p : ZMod n) = 0 := by ring
    rw [h0] at h
    simpa using h.symm
  have hω_neg : omega_root n ^ ((-p).val) = Complex.exp (-θ * I) := by
    have hpne : omega_root n ^ p.val ≠ 0 := pow_ne_zero _ hω_ne
    have : omega_root n ^ ((-p).val) = (omega_root n ^ p.val)⁻¹ := by
      field_simp
      linear_combination hsum_neg
    rw [this, hωp]
    rw [← Complex.exp_neg]
    congr 1
    ring
  -- Step 3: ω^(-p).val + ω^p.val = 2 cos θ.
  have hsum_cos :
      omega_root n ^ ((-p).val) + omega_root n ^ p.val = 2 * Complex.cos θ := by
    rw [hω_neg, hωp]
    rw [add_comm]
    exact (Complex.two_cos θ).symm
  -- Step 4: Complex.cos θ = Complex.cos (2π p.val / n) literally (by defn of θ).
  -- Now finish via linear combination.
  have key : (2 : ℂ) - omega_root n ^ ((-p).val) - omega_root n ^ p.val
      = 2 - 2 * Complex.cos (2 * Real.pi * p.val / n) := by
    show _ = 2 - 2 * Complex.cos θ
    linear_combination -hsum_cos
  -- Conclude by a direct linear combination on the current fully-expanded goal.
  linear_combination (fourier_mode n p i) * key

/-- (Q24) Equivalent form using `4 sin²(π p / n) = 2 − 2 cos(2π p / n)`. -/
theorem cycle_laplacian_eigenvalue' (n : ℕ) (hn : 3 ≤ n) (p : ZMod n) :
    haveI : NeZero n := ⟨by omega⟩
    (cycle_laplacian n hn).mulVec (fourier_mode n p) =
      (4 * (Real.sin (Real.pi * p.val / n)) ^ 2 : ℂ) • fourier_mode n p := by
  haveI : NeZero n := ⟨by omega⟩
  rw [cycle_laplacian_eigenvalue n hn p]
  congr 1
  -- Goal: (2 : ℂ) - 2 * cos(2π p/n) = 4 * sin²(π p/n).
  -- Use `cos(2θ) = 1 - 2 sin²θ` with θ = π p/n.
  have hreal : (2 : ℝ) - 2 * Real.cos (2 * Real.pi * (p.val : ℝ) / n)
      = 4 * (Real.sin (Real.pi * (p.val : ℝ) / n)) ^ 2 := by
    have h2 : 2 * Real.pi * (p.val : ℝ) / n = 2 * (Real.pi * (p.val : ℝ) / n) := by ring
    rw [h2, Real.cos_two_mul_eq_one_sub]
    ring
  have hC := congrArg (fun x : ℝ => (x : ℂ)) hreal
  push_cast at hC
  convert hC using 1
  push_cast; ring

/-! ### Fourier modes form a linearly independent family (bonus)

The proof proceeds via the Vandermonde determinant of `{ω_n^p : p ∈ ZMod n}`,
which is nonzero since these `n` roots of unity are pairwise distinct (a
consequence of `omega_root n` being a primitive `n`-th root of unity).

The argument:
1. Use `Fintype.linearIndependent_iff`: a family is LI iff any vanishing linear
   combination has zero coefficients.
2. Evaluating `∑_q c q • v_q = 0` at a point `k` gives
   `∑_q c q · ω^(q.val · k.val) = 0 = ∑_q c q · (ω^(q.val))^(k.val)`.
3. Transfer indices from `ZMod n` to `Fin n` via the obvious equivalence
   (both have `val : · → ℕ` with the same image `{0, …, n-1}`).
4. Apply `Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero` with
   `f : Fin n → ℂ`, `f i = ω^(i.val)`, which is injective by
   `IsPrimitiveRoot.pow_inj` applied to `Complex.isPrimitiveRoot_exp`.
-/

/-- Natural equivalence `ZMod n ≃ Fin n` via `.val`, for `[NeZero n]`. -/
private def zmodEquivFin (n : ℕ) [NeZero n] : ZMod n ≃ Fin n where
  toFun p := ⟨p.val, p.val_lt⟩
  invFun i := ((i : ℕ) : ZMod n)
  left_inv p := ZMod.natCast_zmod_val p
  right_inv i := Fin.ext (ZMod.val_natCast_of_lt i.is_lt)

@[simp] private lemma zmodEquivFin_apply_val (n : ℕ) [NeZero n] (p : ZMod n) :
    ((zmodEquivFin n p) : ℕ) = p.val := rfl

private lemma zmodEquivFin_symm_val (n : ℕ) [NeZero n] (i : Fin n) :
    ((zmodEquivFin n).symm i).val = (i : ℕ) :=
  ZMod.val_natCast_of_lt i.is_lt

/-- Fourier modes form a linearly independent family.

Proof: transfer to `Fin n` via `zmodEquivFin`, then apply the Vandermonde
determinant formula: `v_p(k) = ω^{p.val · k.val} = (ω^{p.val})^{k.val}` so the
rows form a Vandermonde matrix on the pairwise-distinct sample points
`{ω^{p.val} : p : ZMod n}`. These are distinct because `ω_n` is a primitive
`n`-th root of unity (`Complex.isPrimitiveRoot_exp`). -/
theorem fourier_modes_linear_independent (n : ℕ) [NeZero n] :
    LinearIndependent ℂ (fun p : ZMod n => fourier_mode n p) := by
  have hn_ne : n ≠ 0 := NeZero.ne n
  have hprim : IsPrimitiveRoot (omega_root n) n :=
    Complex.isPrimitiveRoot_exp n hn_ne
  -- Transfer to `Fin n` via `zmodEquivFin`.
  let E : ZMod n ≃ Fin n := zmodEquivFin n
  rw [← linearIndependent_equiv E.symm]
  -- Goal: `LinearIndependent ℂ ((fun p : ZMod n => fourier_mode n p) ∘ E.symm)`.
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  -- `hg : ∑ j : Fin n, g j • (fourier_mode n (E.symm j)) = 0` (function equality).
  -- Evaluate at `E.symm k : ZMod n` for each `k : Fin n` to produce the
  -- Vandermonde system.
  have hg_eval : ∀ k : Fin n,
      (∑ j : Fin n, g j * (omega_root n ^ ((j : ℕ))) ^ ((k : ℕ))) = 0 := by
    intro k
    have h := congrFun hg ((E.symm) k)
    simp only [Finset.sum_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul,
      Function.comp_apply, fourier_mode] at h
    -- `h : ∑ j, g j * ω^((E.symm j).val * (E.symm k).val) = 0`.
    -- Convert each exponent `(E.symm j).val * (E.symm k).val`
    --         to `(j : ℕ) * (k : ℕ)`.
    -- And rewrite `ω^((j : ℕ) * (k : ℕ))` as `(ω^(j : ℕ))^((k : ℕ))`.
    refine h.symm.trans ?_ |>.symm
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hj : ((E.symm) j).val = (j : ℕ) := zmodEquivFin_symm_val n j
    have hk : ((E.symm) k).val = (k : ℕ) := zmodEquivFin_symm_val n k
    rw [hj, hk, pow_mul]
  -- Apply the Vandermonde non-vanishing lemma.
  have f_inj : Function.Injective (fun i : Fin n => omega_root n ^ (i : ℕ)) := by
    intro a b hab
    exact Fin.ext (hprim.pow_inj a.is_lt b.is_lt hab)
  have g_zero : g = 0 :=
    Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero f_inj hg_eval
  exact congrFun g_zero i

end EnsX2026.Matrices.Circulant

end
