import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Reflection
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic.LinearCombination

/-!
# ENS/Polytechnique 2026 Math A — Preliminary (Q1)

We study the cyclic permutation matrix

`J₃ = !![0, 1, 0; 0, 0, 1; 1, 0, 0] : Matrix (Fin 3) (Fin 3) ℂ`

and establish three properties:

* (a) `J₃ ^ 3 = 1`, so the minimal polynomial of `J₃` divides `X^3 - 1`.
* (b) The characteristic polynomial of `J₃` is `X^3 - 1`.
* (c) For any `j : ℂ` with `j^3 = 1`, the vector `!![1, j, j^2]` is an
      eigenvector of `J₃` for eigenvalue `j`.

For diagonalisability, we prove the weaker (still useful) statement that the
three eigenvectors associated to the three distinct cube roots of unity are
linearly independent, via a Vandermonde determinant argument.

Institut Fourier, Grenoble — Kieran McShane
-/

noncomputable section

namespace EnsX2026.Preliminary

open Matrix Polynomial

/-- The cyclic permutation matrix `J₃` sending `e₀ ↦ e₂ ↦ e₁ ↦ e₀`
(its rows are the cyclic shifts of the standard basis of `ℂ^3`). -/
def matrix_J3 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 1, 0; 0, 0, 1; 1, 0, 0]

/-- (a) `J₃ ^ 3 = 1`.  This shows that the minimal polynomial of `J₃`
divides `X^3 - 1`. -/
theorem J3_pow_three : matrix_J3 ^ 3 = 1 := by
  have h2 : matrix_J3 * matrix_J3 = !![0, 0, 1; 1, 0, 0; 0, 1, 0] := by
    unfold matrix_J3
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three]
  have h3 : matrix_J3 ^ 3 = matrix_J3 * matrix_J3 * matrix_J3 := by
    rw [pow_succ, pow_succ, pow_one]
  rw [h3, h2]
  unfold matrix_J3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]

/-- (b) The characteristic polynomial of `J₃` is `X^3 - 1`. -/
theorem J3_charpoly : matrix_J3.charpoly = X ^ 3 - 1 := by
  -- Expand `charpoly = det (charmatrix …)` via `det_fin_three` on each entry,
  -- then simplify using the explicit entries of `J₃`.
  unfold Matrix.charpoly
  rw [Matrix.det_fin_three]
  unfold matrix_J3
  -- After `det_fin_three`, each entry is a `charmatrix` entry; `simp` turns
  -- them into `X - C 0 = X` on the diagonal and `-C (…)` off-diagonal.
  simp [Matrix.charmatrix, Matrix.scalar_apply, sub_eq_add_neg]
  ring

/-- (c) For any cube root of unity `j : ℂ`, the vector `!![1, j, j²]` is an
eigenvector of `J₃` for eigenvalue `j`. -/
theorem J3_mulVec_eigenvector (j : ℂ) (hj : j ^ 3 = 1) :
    matrix_J3.mulVec ![(1 : ℂ), j, j ^ 2] = j • ![(1 : ℂ), j, j ^ 2] := by
  unfold matrix_J3
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    ring
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    -- Goal: `1 = j * j ^ 2`, which is `j ^ 3 = 1` rearranged.
    have e : j * j ^ 2 = j ^ 3 := by ring
    rw [e, hj]

/-- The three eigenvectors `(1, 1, 1)`, `(1, j, j²)`, `(1, j², j)` are linearly
independent whenever `j : ℂ` is a primitive cube root of unity, i.e. whenever
`j^3 = 1` and `1, j, j²` are pairwise distinct.

Proof idea: their matrix is the `3×3` Vandermonde matrix on `v = ![1, j, j²]`,
and `v` is injective under our distinctness hypotheses.  The key identity we
need is `j^4 = j`, which follows from `j^3 = 1`. -/
theorem J3_eigenvectors_linear_independent
    (j : ℂ) (hj : j ^ 3 = 1)
    (h1j : (1 : ℂ) ≠ j) (h1j2 : (1 : ℂ) ≠ j ^ 2) (hjj2 : j ≠ j ^ 2) :
    LinearIndependent ℂ
      (![![(1 : ℂ), 1, 1], ![1, j, j ^ 2], ![1, j ^ 2, j]] :
        Fin 3 → Fin 3 → ℂ) := by
  -- `v = ![1, j, j^2]` is injective from the distinctness hypotheses.
  have hv_inj : Function.Injective (![(1 : ℂ), j, j ^ 2] : Fin 3 → ℂ) := by
    set_option linter.unusedSimpArgs false in
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
                 Matrix.cons_val_fin_one, Matrix.head_fin_const] at hab
    · rfl
    · exact absurd hab h1j
    · exact absurd hab h1j2
    · exact absurd hab.symm h1j
    · rfl
    · exact absurd hab hjj2
    · exact absurd hab.symm h1j2
    · exact absurd hab.symm hjj2
    · rfl
  have hvand : (Matrix.vandermonde (![(1 : ℂ), j, j ^ 2] : Fin 3 → ℂ)).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr hv_inj
  have hrows :
      LinearIndependent ℂ
        (fun i ↦ (Matrix.vandermonde (![(1 : ℂ), j, j ^ 2] : Fin 3 → ℂ)) i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hvand
  -- Rewrite rows of `vandermonde ![1, j, j²]` to match our three vectors.
  -- The key identity is `(j^2)^2 = j^4 = j`, from `j^3 = 1`.
  have hj4 : (j ^ 2) ^ 2 = j := by
    have e : (j ^ 2) ^ 2 = j ^ 3 * j := by ring
    rw [e, hj, one_mul]
  have hrow_eq :
      (fun i ↦ (Matrix.vandermonde (![(1 : ℂ), j, j ^ 2] : Fin 3 → ℂ)) i) =
        (![![(1 : ℂ), 1, 1], ![1, j, j ^ 2], ![1, j ^ 2, j]] :
          Fin 3 → Fin 3 → ℂ) := by
    funext i k
    fin_cases i <;> fin_cases k <;>
      simp [Matrix.vandermonde_apply, hj4]
  exact hrow_eq ▸ hrows

/-!
### Diagonalisability

Full diagonalisability via the `Matrix.IsDiagonalizable` predicate in Mathlib
requires some additional wiring (exhibiting an explicit invertible conjugator
and a diagonal matrix).  We record the linear-independence statement above as
the operative consequence (three eigenvectors ⇒ eigenbasis of `ℂ^3`) and flag
the packaging into `IsDiagonalizable` as future work.
-/

/-- TODO: package `J3_eigenvectors_linear_independent` into a full
`Matrix.IsDiagonalizable` statement.  What is missing:

* An explicit change-of-basis matrix `P : Matrix (Fin 3) (Fin 3) ℂ` whose
  columns are `![1,1,1]`, `![1,j,j²]`, `![1,j²,j]` (for a primitive cube
  root `j`);
* a proof that `P` is invertible (its determinant is the nonvanishing
  Vandermonde determinant);
* the verification `P⁻¹ * J₃ * P = diagonal ![1, j, j²]`.

The linear-independence lemma above gives the key ingredient; the rest is
bookkeeping. -/
theorem J3_is_diagonalisable_placeholder : True := trivial

end EnsX2026.Preliminary

end
