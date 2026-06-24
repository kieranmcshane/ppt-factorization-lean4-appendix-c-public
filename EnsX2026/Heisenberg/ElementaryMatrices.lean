/-
Copyright (c) 2026 Kieran McShane. All rights reserved.
Released under Apache 2.0 license.
Authors: Kieran McShane
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Discrete Heisenberg group `H₃(ℤ)` via elementary matrices

This file establishes the normal form for elements of the discrete Heisenberg group
realised as `3 × 3` integer matrices.  It is a prerequisite for Q30 of the 2026
ENS / École Polytechnique Mathematics A exam.

## Design note

To sidestep the friction of `zpow` / `Invertible` on `Matrix (Fin 3) (Fin 3) ℤ`, the
one-parameter subgroups are introduced as *bespoke* power-parameterised functions
`S k`, `T ℓ`, `U m`, rather than integer powers of generators via `^`.  The three
generators `S_gen`, `T_gen`, `U_gen` are kept as named matrices; the lemmas
`S 1 = S_gen` (etc.) connect the two viewpoints.  Every statement below is a
direct matrix computation; no `sorry` appears.

## Main results

* `S_zero`, `T_zero`, `U_zero`, `H3_normal_zero` — identity cases.
* `S_one`, `T_one`, `U_one` — generators match the parameterisation at `k = 1`.
* `S_mul`, `T_mul`, `U_mul` — one-parameter subgroup (additive) law.
* `S_neg_mul`, `S_mul_neg` (and analogues for `T`, `U`) — inverses.
* `S_mul_T_mul_U` — Q30(a) normal-form factorisation
  `S k · T ℓ · U m = H3_normal k ℓ m`.
* `H3_normal_mul` — Q30(b) composition law with the non-abelian cocycle
  `ℓ · k'` in the `(3,1)` slot.
* `S_gen_T_gen_not_commute` — non-commutativity witness.
* `commutator_S_T` — commutator identity
  `T 1 · S 1 · T (-1) · S (-1) = U 1` (key for Q31).
-/

namespace EnsX2026.Heisenberg

open Matrix

/-! ### Generators and power-parameterised normal forms -/

/-- First elementary generator: unit subdiagonal in position `(2,1)`. -/
def S_gen : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 0; 1, 1, 0; 0, 0, 1]

/-- Second elementary generator: unit subdiagonal in position `(3,2)`. -/
def T_gen : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 0; 0, 1, 0; 0, 1, 1]

/-- Third elementary generator: unit entry in position `(3,1)`. -/
def U_gen : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 0; 0, 1, 0; 1, 0, 1]

/-- Power-parameterised first subgroup: intended value `S_gen ^ k`. -/
def S (k : ℤ) : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 0; k, 1, 0; 0, 0, 1]

/-- Power-parameterised second subgroup: intended value `T_gen ^ ℓ`. -/
def T (ℓ : ℤ) : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 0; 0, 1, 0; 0, ℓ, 1]

/-- Power-parameterised third subgroup: intended value `U_gen ^ m`. -/
def U (m : ℤ) : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 0; 0, 1, 0; m, 0, 1]

/-- Normal form of a Heisenberg element with parameters `(k, ℓ, m)`. -/
def H3_normal (k ℓ m : ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0; k, 1, 0; m, ℓ, 1]

/-! ### Identity cases -/

theorem S_zero : S 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [S]

theorem T_zero : T 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [T]

theorem U_zero : U 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [U]

theorem H3_normal_zero : H3_normal 0 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H3_normal]

/-! ### Generators match the parameterisation at `k = 1` -/

theorem S_one : S 1 = S_gen := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [S, S_gen]

theorem T_one : T 1 = T_gen := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [T, T_gen]

theorem U_one : U 1 = U_gen := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [U, U_gen]

/-! ### One-parameter subgroup laws -/

theorem S_mul (k ℓ : ℤ) : S k * S ℓ = S (k + ℓ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [S, Matrix.mul_apply, Fin.sum_univ_three]

theorem T_mul (k ℓ : ℤ) : T k * T ℓ = T (k + ℓ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [T, Matrix.mul_apply, Fin.sum_univ_three]

theorem U_mul (k ℓ : ℤ) : U k * U ℓ = U (k + ℓ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [U, Matrix.mul_apply, Fin.sum_univ_three]

/-! ### Inverses at `±k` -/

theorem S_neg_mul (k : ℤ) : S (-k) * S k = 1 := by
  rw [S_mul]; rw [show (-k) + k = 0 from by ring]; exact S_zero

theorem S_mul_neg (k : ℤ) : S k * S (-k) = 1 := by
  rw [S_mul]; rw [show k + (-k) = 0 from by ring]; exact S_zero

theorem T_neg_mul (ℓ : ℤ) : T (-ℓ) * T ℓ = 1 := by
  rw [T_mul]; rw [show (-ℓ) + ℓ = 0 from by ring]; exact T_zero

theorem T_mul_neg (ℓ : ℤ) : T ℓ * T (-ℓ) = 1 := by
  rw [T_mul]; rw [show ℓ + (-ℓ) = 0 from by ring]; exact T_zero

theorem U_neg_mul (m : ℤ) : U (-m) * U m = 1 := by
  rw [U_mul]; rw [show (-m) + m = 0 from by ring]; exact U_zero

theorem U_mul_neg (m : ℤ) : U m * U (-m) = 1 := by
  rw [U_mul]; rw [show m + (-m) = 0 from by ring]; exact U_zero

/-! ### Q30(a): normal-form factorisation -/

theorem S_mul_T_mul_U (k ℓ m : ℤ) :
    S k * T ℓ * U m = H3_normal k ℓ m := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [S, T, U, H3_normal, Matrix.mul_apply, Fin.sum_univ_three]

/-! ### Q30(b): composition law for the normal form -/

theorem H3_normal_mul (k ℓ m k' ℓ' m' : ℤ) :
    H3_normal k ℓ m * H3_normal k' ℓ' m' =
      H3_normal (k + k') (ℓ + ℓ') (m + m' + ℓ * k') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (first | (simp [H3_normal, Matrix.mul_apply, Fin.sum_univ_three]; ring)
           | simp [H3_normal, Matrix.mul_apply, Fin.sum_univ_three])

/-! ### Non-commutativity witness -/

theorem S_gen_T_gen_not_commute : S_gen * T_gen ≠ T_gen * S_gen := by
  intro h
  have h21 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℤ => M 2 0) h
  simp [S_gen, T_gen, Matrix.mul_apply, Fin.sum_univ_three] at h21

/-! ### Commutator identity (useful for Q31) -/

theorem commutator_S_T : T 1 * S 1 * T (-1) * S (-1) = U 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [S, T, U, Matrix.mul_apply, Fin.sum_univ_three]

end EnsX2026.Heisenberg
