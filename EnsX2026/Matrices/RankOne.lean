import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.RowCol
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star

/-!
# ENS/Polytechnique 2026 Math A — Q3

Characteristic polynomial of `Kₙ = n·Iₙ − Jₙ`, where `Jₙ` is the all-ones
`n × n` matrix. We prove
$$\chi_{K_n}(X) = X \cdot (X - n)^{\,n-1}.$$

The proof uses Mathlib's `Matrix.charpoly_vecMulVec`, which states that the
characteristic polynomial of a rank-one matrix `vecMulVec u v` equals
`X^n - (u · v) • X^(n-1)`. Writing `Jₙ = vecMulVec 1 1` and
`Kₙ = −Jₙ − scalar (−n)`, a single application of `Matrix.charpoly_sub_scalar`
reduces the problem to an elementary polynomial identity.

The formula fails in the degenerate case `n = 0` (characteristic polynomial
of a `0 × 0` matrix is `1`, whereas the RHS evaluates to `X`), so the main
theorem is stated under the hypothesis `1 ≤ n`.
-/

namespace EnsX2026.Matrices

open Matrix Polynomial

/-- The exam matrix `Kₙ = n · Iₙ − Jₙ`. -/
def K_matrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) - Matrix.of (fun _ _ => (1 : ℝ))

/-- `Kₙ` is symmetric (Hermitian over ℝ). -/
lemma K_matrix_isHermitian (n : ℕ) : (K_matrix n).IsHermitian := by
  unfold Matrix.IsHermitian K_matrix
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, Matrix.of_apply, eq_comm]

/-- Rewrite `Kₙ` as `(−Jₙ) − scalar _ (−n)`, where `Jₙ = vecMulVec 1 1`.
This is the key algebraic identity we feed into `Matrix.charpoly_sub_scalar`. -/
private lemma K_matrix_eq_sub_scalar (n : ℕ) :
    K_matrix n =
      (- vecMulVec (fun _ : Fin n => (1 : ℝ)) (fun _ : Fin n => (1 : ℝ))) -
        Matrix.scalar (Fin n) (-(n : ℝ)) := by
  unfold K_matrix
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.scalar_apply, Matrix.diagonal, Matrix.of_apply,
      vecMulVec_apply]
    ring
  · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h,
      Matrix.of_apply, vecMulVec_apply]

/-- Characteristic polynomial of `−Jₙ`. Direct application of
`Matrix.charpoly_vecMulVec` to the rank-one outer product `(−1) ⊗ 1`. -/
private lemma charpoly_neg_J (n : ℕ) :
    (- vecMulVec (fun _ : Fin n => (1 : ℝ)) (fun _ : Fin n => (1 : ℝ))).charpoly =
      Polynomial.X ^ n + (n : ℝ) • Polynomial.X ^ (n - 1) := by
  have h1 : - vecMulVec (fun _ : Fin n => (1 : ℝ)) (fun _ : Fin n => (1 : ℝ))
      = vecMulVec (fun _ : Fin n => (-1 : ℝ)) (fun _ : Fin n => (1 : ℝ)) := by
    rw [show (fun _ : Fin n => (-1 : ℝ)) = -(fun _ : Fin n => (1 : ℝ)) from rfl,
      neg_vecMulVec]
  rw [h1, Matrix.charpoly_vecMulVec]
  have hdot : ((fun _ : Fin n => (-1 : ℝ)) ⬝ᵥ (fun _ : Fin n => (1 : ℝ))) = -(n : ℝ) := by
    simp [dotProduct, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [hdot, Fintype.card_fin, neg_smul, sub_neg_eq_add]

/-- **Main theorem (ENS/X 2026 Math A, Q3).** For `n ≥ 1`, the
characteristic polynomial of `Kₙ = n·Iₙ − Jₙ` factors as `X · (X − n)^(n−1)`. -/
theorem K_matrix_charpoly (n : ℕ) (hn : 1 ≤ n) :
    (K_matrix n).charpoly =
      Polynomial.X * (Polynomial.X - Polynomial.C (n : ℝ)) ^ (n - 1) := by
  rw [K_matrix_eq_sub_scalar, Matrix.charpoly_sub_scalar, charpoly_neg_J]
  -- Goal: (X^n + n • X^(n-1)).comp (X + C (-(n : ℝ))) = X * (X - C n)^(n-1)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  -- Now n = k + 1, so n - 1 = k.
  simp only [Nat.add_sub_cancel]
  -- After simp: (X^(k+1) + ↑(k+1) • X^k).comp (X + C (-↑(k+1))) = X * (X - C ↑(k+1))^k
  rw [add_comp, pow_comp, X_comp, smul_comp, pow_comp, X_comp]
  -- Goal: (X + C (-↑(k+1)))^(k+1) + ↑(k+1) • (X + C (-↑(k+1)))^k
  --     = X * (X - C ↑(k+1))^k
  have hXsub : (X + C (-((k + 1 : ℕ) : ℝ))) = X - C (((k + 1 : ℕ) : ℝ)) := by
    rw [map_neg]
    ring
  rw [hXsub]
  -- Let Y := X - C ((k+1 : ℕ) : ℝ). Then goal:
  --   Y^(k+1) + (k+1 : ℝ) • Y^k = X * Y^k
  -- which follows from Y^(k+1) = Y * Y^k and Y + (k+1) = X.
  rw [pow_succ]
  -- Now: (X - C ↑(k+1))^k * (X - C ↑(k+1)) + ↑(k+1) • (X - C ↑(k+1))^k
  --    = X * (X - C ↑(k+1))^k
  rw [smul_eq_C_mul]
  -- Now: Y^k * Y + C (k+1) * Y^k = X * Y^k
  push_cast
  ring

end EnsX2026.Matrices
