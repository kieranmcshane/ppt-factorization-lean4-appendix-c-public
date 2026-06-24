-- Test: tridG_minor01_det
-- The minor M = (tridG(n+2)).submatrix succ (succAbove 1) has:
-- Row i of M = row (i+1) of tridG(n+2)
-- Col j of M = col (succAbove 1 j) of tridG(n+2)
--   succAbove 1 j = j.castSucc if j < 1, i.e. j=0 maps to 0
--                  = j.succ    if j ≥ 1, i.e. j maps to j+1
-- So columns of M are {0, 2, 3, ..., n+2} (skipping column 1).
--
-- M(i,j) = tridG(n+2)(i+1, col(j)) where col(0)=0, col(j)=j+1 for j≥1.
--
-- Row 0: M(0,j) = tridG(n+2)(1, col(j)):
--   j=0: tridG(1, 0) = 1 (sub-diagonal)
--   j=1: tridG(1, 2) = lam (super-diagonal: 2 = 1+1)
--   j≥2: tridG(1, j+1): 1 ≠ j+1 for j≥2, j+1 ≠ 2 for j≥2, 1 ≠ j+2 for j≥1 → 0
--
-- So row 0 of M is [1, lam, 0, 0, ...]
-- Expanding det(M) along row 0:
-- det(M) = 1 * det(minor00_of_M) - lam * det(minor01_of_M)
--
-- minor00_of_M = M.submatrix succ (succAbove 0)
-- M(succ i, succAbove 0 j) = M(i+1, j+1) = tridG(n+2)(i+2, col(j+1))
-- = tridG(n+2)(i+2, j+2) = tridG(n)(i, j) (by nat_succ_eq twice)
-- So det(minor00_of_M) = det(tridG(n))
--
-- minor01_of_M has more complex structure.
-- But for the FIRST minor computation (from det_succ_row_zero on M):
-- We need M 0 0 = 1 and M 0 (succ j) entries.
-- Actually we can use det_succ_row_zero on M directly.

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Linarith

open Matrix Finset Fin
noncomputable section
variable (lam : ℝ)

def trid' (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := fun i j =>
  if (i : ℕ) = j then lam
  else if (j : ℕ) = (i : ℕ) + 1 then lam
  else if (i : ℕ) = (j : ℕ) + 1 then 1
  else 0

private lemma nat_succ_eq (a b : ℕ) : (a + 1 = b + 1) = (a = b) :=
  propext (by omega)

-- The minor01: M = (trid'(n+2)).submatrix succ (succAbove 1)
-- We need det(M) = det(trid'(n)).
-- Strategy: show M(0,0) = 1, M(0, succ j) = 0 for j ≥ 1 (i.e. all but j=0 in row 0 of M).
-- Wait — M(0,1) = lam ≠ 0. So row 0 has TWO nonzero entries.
--
-- Alternative: expand along COLUMN 0 instead of row 0.
-- Column 0 of M: M(i,0) = tridG(n+2)(i+1, 0).
--   i=0: tridG(1, 0) = 1 (sub-diagonal)
--   i≥1: tridG(i+1, 0): i+1 ≠ 0, 0 ≠ i+2, i+1 ≠ 1 for i≥1 → 0 (except i=0)
-- Wait: i=1 gives tridG(2, 0): 2≠0, 0≠3, 2≠1 → 0. ✓
-- So column 0 has SINGLE nonzero entry: M(0,0) = 1.
--
-- Expanding along column 0: det(M) = M(0,0) * cofactor(0,0)
-- = 1 * (-1)^(0+0) * det(M.submatrix (succAbove 0 ·) (succ ·))
-- Wait, column expansion uses det_succ_column or transpose.
-- det(M) = det(Mᵀ) and Mᵀ has row 0 = column 0 of M = [1, 0, 0, ...].
-- So det(Mᵀ) via det_succ_row_zero = 1 * det(minor) + 0 + ... = det(minor).
-- And minor = (Mᵀ).submatrix succ (succAbove 0) = (M.submatrix (succAbove 0 ·) succ)ᵀ? No...
-- Actually: det(M) = det(Mᵀ). And Mᵀ has row 0 with single nonzero = 1 at position 0.
-- det(Mᵀ) = 1 * det((Mᵀ).submatrix succ (succAbove 0)).
-- (Mᵀ).submatrix succ (succAbove 0) (i, j) = Mᵀ(succ i, succ j) = M(succ j, succ i).
-- = tridG(n+2)(succ j + 1, col(succ i + 1))... this gets complicated.

-- Simplest: use det_transpose + det_succ_row_zero on Mᵀ.
-- Mᵀ(0, j) = M(j, 0) = tridG(n+2)(j+1, 0).
-- For j=0: tridG(1,0) = 1.
-- For j≥1: tridG(j+1, 0) = 0 (since j+1 ≥ 2, 0 ≠ j+1, j+1 ≠ 1).
-- So Mᵀ row 0 = [1, 0, 0, ...] — only j=0 contributes!

-- Let me test this approach.
-- det(M) = det(Mᵀ) = 1 * det(Mᵀ.submatrix succ (succAbove 0))
-- Mᵀ.submatrix succ (succAbove 0) (i, j) = Mᵀ(i+1, j+1) = M(j+1, i+1)
-- = tridG(n+2)((j+1)+1, col((i+1)))
-- where col is succAbove 1.

-- For col(i+1): since i+1 ≥ 1, succAbove 1 (i+1) = (i+1)+1 = i+2.
-- So the entry = tridG(n+2)(j+2, i+2).
-- tridG(n+2)(j+2, i+2): checks j+2=i+2 (i.e. j=i), i+2=(j+2)+1 (i.e. i=j+1), j+2=(i+2)+1 (i.e. j=i+1).
-- This is tridG(n)(j, i) = tridG(n)(i, j) since tridG is symmetric!
-- Wait, tridG is NOT symmetric: diagonal=lam, super=lam, sub=1. So tridG(i,j) ≠ tridG(j,i) in general.
-- But Mᵀ.submatrix succ (succAbove 0) (i, j) = tridG(n+2)(j+2, i+2) = tridG(n)(j, i).
-- So this submatrix = tridG(n)ᵀ! And det(tridG(n)ᵀ) = det(tridG(n)).

-- So: det(M) = det(Mᵀ) = 1 * det(tridG(n)ᵀ) = det(tridG(n)). ✓

-- Let me verify this logic in Lean.

set_option maxHeartbeats 400000 in
example (n : ℕ) :
    ((trid' lam (n + 2)).submatrix Fin.succ (Fin.succAbove 1)).det =
    (trid' lam n).det := by
  -- det(M) = det(Mᵀ)
  rw [← Matrix.det_transpose]
  -- det(Mᵀ): expand along row 0
  rw [Matrix.det_succ_row_zero]
  -- Row 0 of Mᵀ: Mᵀ(0, j) = M(j, 0) = tridG(succ j, succAbove 1 0)
  -- = tridG(j+1, 0). Only j=0 gives 1; rest give 0.
  rw [Fin.sum_univ_succ]
  -- j=0 term + tail
  -- Tail vanishes: Mᵀ(0, succ j) = M(succ j, 0) = tridG(j+2, 0) = 0
  have htail : ∀ j : Fin (n + 1),
      (-1 : ℝ) ^ ((Fin.succ j : Fin (n + 2)) : ℕ) *
      ((trid' lam (n + 2)).submatrix Fin.succ (Fin.succAbove 1))ᵀ 0 (Fin.succ j) *
      (((trid' lam (n + 2)).submatrix Fin.succ (Fin.succAbove 1))ᵀ.submatrix
        Fin.succ (Fin.succAbove (Fin.succ j))).det = 0 := by
    intro ⟨j, hj⟩
    -- Mᵀ(0, succ j) = M(succ j, 0) = tridG(j+2, succAbove 1 0) = tridG(j+2, 0)
    suffices h : ((trid' lam (n + 2)).submatrix Fin.succ (Fin.succAbove 1))ᵀ 0
      (Fin.succ ⟨j, hj⟩) = 0 by rw [h, mul_zero, zero_mul]
    simp only [Matrix.transpose_apply, Matrix.submatrix_apply, trid']
    -- Entry: trid'(n+2)(succ(succ ⟨j,hj⟩), succAbove 1 0)
    -- succ(succ j).val = j+2, succAbove 1 0 = 0 (since 0 < 1)
    show (if (Fin.succ (Fin.succ ⟨j, hj⟩) : Fin (n + 3)).val =
      (Fin.succAbove 1 (0 : Fin (n + 2)) : Fin (n + 3)).val then lam
      else if (Fin.succAbove 1 (0 : Fin (n + 2)) : Fin (n + 3)).val =
        (Fin.succ (Fin.succ ⟨j, hj⟩) : Fin (n + 3)).val + 1 then lam
      else if (Fin.succ (Fin.succ ⟨j, hj⟩) : Fin (n + 3)).val =
        (Fin.succAbove 1 (0 : Fin (n + 2)) : Fin (n + 3)).val + 1 then 1
      else 0) = 0
    simp [Fin.succAbove, Fin.lt_def, Fin.val_succ, Fin.val_zero, Fin.val_castSucc]
  rw [Finset.sum_eq_zero (fun j _ => htail j), add_zero]
  -- j=0 term: (-1)^0 * Mᵀ(0,0) * det(Mᵀ.submatrix succ (succAbove 0))
  rw [show ((0 : Fin (n + 2)) : ℕ) = 0 from rfl, pow_zero, one_mul]
  -- Mᵀ(0,0) = M(0,0) = trid'(1, succAbove 1 0) = trid'(1, 0) = 1
  have hM00 : ((trid' lam (n + 2)).submatrix Fin.succ (Fin.succAbove 1))ᵀ 0 0 = 1 := by
    simp only [Matrix.transpose_apply, Matrix.submatrix_apply, trid']
    show (if (Fin.succ (0 : Fin (n + 2)) : Fin (n + 3)).val =
      (Fin.succAbove 1 (0 : Fin (n + 2)) : Fin (n + 3)).val then lam
      else if (Fin.succAbove 1 (0 : Fin (n + 2)) : Fin (n + 3)).val =
        (Fin.succ (0 : Fin (n + 2)) : Fin (n + 3)).val + 1 then lam
      else if (Fin.succ (0 : Fin (n + 2)) : Fin (n + 3)).val =
        (Fin.succAbove 1 (0 : Fin (n + 2)) : Fin (n + 3)).val + 1 then 1
      else 0) = 1
    simp [Fin.succAbove, Fin.lt_def, Fin.val_succ, Fin.val_zero, Fin.val_castSucc]
  rw [hM00, one_mul]
  -- Now: det(Mᵀ.submatrix succ (succAbove 0)) = det(trid'(n))
  -- Mᵀ.submatrix succ (succAbove 0) (i, j)
  -- = Mᵀ(i+1, j+1) = M(j+1, i+1) = trid'(n+2)(j+2, succAbove 1 (i+1))
  -- Since i+1 ≥ 1: succAbove 1 (i+1) = i+2.
  -- So entry = trid'(n+2)(j+2, i+2) which by nat_succ_eq = trid'(n)(j, i).
  -- This is trid'(n)ᵀ(i, j). So the submatrix = trid'(n)ᵀ.
  -- det(trid'(n)ᵀ) = det(trid'(n)).
  rw [← Matrix.det_transpose]
  congr 1
  ext ⟨i, hi⟩ ⟨j, hj⟩
  simp only [Matrix.transpose_apply, Matrix.submatrix_apply, Fin.succAbove_zero, trid']
  -- LHS: Mᵀ(succ(succ i), succ(succ j)) = M(succ(succ j), succ(succ i))
  -- = trid'(n+2)(succ(succ(succ j)), succAbove 1 (succ(succ i)))
  -- Need succAbove 1 (succ(succ i)).val = i + 2 + 1 = i + 3? No...
  -- succ(succ i) has val i+2. Since i+2 ≥ 1, succAbove 1 maps it to succ(i+2) = i+3.
  -- Hmm, that gives trid'(n+2)(j+3, i+3) which doesn't match trid'(n)(i,j).
  -- Wait, the succ in the submatrix is applied to Fin(n+1) → Fin(n+2).
  -- Let me re-examine.

  -- The submatrix is (Mᵀ).submatrix succ (succAbove 0).
  -- So entry (i,j) = Mᵀ(succ i, succAbove 0 j) = Mᵀ(i+1, j+1) [succAbove 0 = succ]
  -- = M(j+1, i+1).
  -- M(j+1, i+1) = trid'(n+2)(succ(j+1), succAbove 1 (i+1))
  -- succ(j+1) = Fin.succ ⟨j+1, ...⟩ has val j+2.
  -- succAbove 1 ⟨i+1, ...⟩: since i+1 ≥ 1, this = Fin.succ ⟨i+1, ...⟩ which has val i+2.
  -- So entry = trid'(n+2)(j+2, i+2).
  -- trid'(n+2)(j+2, i+2): if j+2=i+2 (j=i) → lam. if i+2=j+2+1 (i=j+1) → lam.
  --   if j+2=i+2+1 (j=i+1) → 1. else 0.
  -- This is trid'(n)(j, i) [shift both indices by 2].
  -- And trid'(n)ᵀ(i, j) = trid'(n)(j, i). ✓

  -- RHS: trid'(n)ᵀ(succ i, succ j) = trid'(n)(succ j, succ i)
  -- = trid'(n)(j+1, i+1) if we interpret succ correctly.
  -- Wait, the RHS is (trid'(n))ᵀ. After ← det_transpose, the goal is:
  -- det((Mᵀ).submatrix succ (succAbove 0)) = det((trid'(n))ᵀ)
  -- After congr 1 + ext, the goal is:
  -- (Mᵀ).submatrix succ (succAbove 0) (i, j) = (trid'(n))ᵀ (i, j)
  -- LHS: Mᵀ(succ i, succAbove 0 j) = Mᵀ(i+1, j+1) = M(j+1, i+1)
  --     = trid'(n+2)(succ(j+1), succAbove 1 (i+1))
  --     = trid'(n+2)(j+2, i+2) [since succAbove 1 (i+1) = i+2 for i+1 ≥ 1]
  -- RHS: trid'(n)ᵀ(i, j) = trid'(n)(j, i)
  -- Need: trid'(n+2)(j+2, i+2) = trid'(n)(j, i)
  -- This follows from nat_succ_eq: j+2=i+2 ↔ j=i, etc.

  -- Goal has succ.succ and succAbove 1 vals in ite conditions
  have h1 : (Fin.succ (Fin.succ ⟨i, hi⟩) : Fin (n + 3)).val = i + 2 := by simp [Fin.val_succ]
  have h2 : (Fin.succAbove 1 (Fin.succ ⟨j, hj⟩) : Fin (n + 3)).val = j + 2 := by
    rw [Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def])]
    simp [Fin.val_succ]
  rw [h1, h2]; simp only [nat_succ_eq]

end
