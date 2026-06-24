import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Fintype.BigOperators

/-!
# Partial transpose on bipartite matrices

This file provides the concrete finite-dimensional matrix API for partial
transpose on `Matrix (p × q) (p × q) 𝕜`.

It deliberately stops at exact algebraic identities and Frobenius-norm
invariance. The dimension-free operator-space estimate

`‖(Z₁ ⋯ Zₘ)^Γ‖ ≤ K^(m-1) ∏ max(‖Zᵢ‖, ‖Zᵢ^Γ‖)`

is a substantially deeper theorem: its proof uses noncommutative
Grothendieck/Haagerup factorization machinery, which is not currently present
in Mathlib or elsewhere in this repository.
-/

open scoped BigOperators Matrix.Norms.Frobenius

namespace Matrix

section PartialTranspose

variable {p q 𝕜 : Type*}

/-- Partial transpose on the second tensor factor, written in the standard
matrix indexing `((a,b),(c,d)) ↦ ((a,d),(c,b))`. -/
def partialTranspose
    (M : Matrix (p × q) (p × q) 𝕜) : Matrix (p × q) (p × q) 𝕜 :=
  fun i j => M (i.1, j.2) (j.1, i.2)

@[simp] theorem partialTranspose_apply
    (M : Matrix (p × q) (p × q) 𝕜) (i j : p × q) :
    partialTranspose M i j = M (i.1, j.2) (j.1, i.2) :=
  rfl

@[simp] theorem partialTranspose_zero [Zero 𝕜] :
    partialTranspose (0 : Matrix (p × q) (p × q) 𝕜) = 0 := by
  ext i j
  rfl

@[simp] theorem partialTranspose_add [Add 𝕜]
    (M N : Matrix (p × q) (p × q) 𝕜) :
    partialTranspose (M + N) = partialTranspose M + partialTranspose N := by
  ext i j
  rfl

@[simp] theorem partialTranspose_sub [Sub 𝕜]
    (M N : Matrix (p × q) (p × q) 𝕜) :
    partialTranspose (M - N) = partialTranspose M - partialTranspose N := by
  ext i j
  rfl

@[simp] theorem partialTranspose_neg [Neg 𝕜]
    (M : Matrix (p × q) (p × q) 𝕜) :
    partialTranspose (-M) = -partialTranspose M := by
  ext i j
  rfl

@[simp] theorem partialTranspose_smul {R : Type*} [SMul R 𝕜]
    (c : R) (M : Matrix (p × q) (p × q) 𝕜) :
    partialTranspose (c • M) = c • partialTranspose M := by
  ext i j
  rfl

@[simp] theorem partialTranspose_transpose
    (M : Matrix (p × q) (p × q) 𝕜) :
    partialTranspose Mᵀ = (partialTranspose M)ᵀ := by
  ext i j
  rfl

@[simp] theorem partialTranspose_conjTranspose
    [Star 𝕜] (M : Matrix (p × q) (p × q) 𝕜) :
    partialTranspose Mᴴ = (partialTranspose M)ᴴ := by
  ext i j
  rfl

@[simp] theorem partialTranspose_partialTranspose
    (M : Matrix (p × q) (p × q) 𝕜) :
    partialTranspose (partialTranspose M) = M := by
  ext i j
  cases i
  cases j
  rfl

theorem partialTranspose_involutive :
    Function.Involutive (@partialTranspose p q 𝕜) :=
  partialTranspose_partialTranspose

section Mul

variable [Fintype p] [Fintype q] [NonUnitalNonAssocSemiring 𝕜]

/-- Exact entrywise shuffle identity for partial transpose of a product. -/
theorem partialTranspose_mul_apply
    (X Y : Matrix (p × q) (p × q) 𝕜)
    (a c : p) (b d : q) :
    partialTranspose (X * Y) (a, b) (c, d) =
      ∑ u, ∑ v,
        partialTranspose X (a, v) (u, d) *
          partialTranspose Y (u, b) (c, v) := by
  simp [partialTranspose, Matrix.mul_apply, Fintype.sum_prod_type]

end Mul

section Frobenius

variable [Fintype p] [Fintype q]
variable [SeminormedAddCommGroup 𝕜]

/-- The permutation of matrix entries induced by partial transpose. -/
private def partialTransposeEntryEquiv :
    ((p × q) × (p × q)) ≃ ((p × q) × (p × q)) where
  toFun x := ((x.1.1, x.2.2), (x.2.1, x.1.2))
  invFun x := ((x.1.1, x.2.2), (x.2.1, x.1.2))
  left_inv x := by
    rcases x with ⟨⟨a, b⟩, ⟨c, d⟩⟩
    rfl
  right_inv x := by
    rcases x with ⟨⟨a, b⟩, ⟨c, d⟩⟩
    rfl

@[simp] theorem frobenius_nnnorm_partialTranspose
    (M : Matrix (p × q) (p × q) 𝕜) :
    ‖partialTranspose M‖₊ = ‖M‖₊ := by
  rw [Matrix.frobenius_nnnorm_def, Matrix.frobenius_nnnorm_def,
    ← Fintype.sum_prod_type',
    ← Fintype.sum_prod_type']
  congr 1
  refine Fintype.sum_equiv partialTransposeEntryEquiv _ _ ?_
  intro x
  rcases x with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  rfl

@[simp] theorem frobenius_norm_partialTranspose
    (M : Matrix (p × q) (p × q) 𝕜) :
    ‖partialTranspose M‖ = ‖M‖ :=
  congr_arg (fun x : NNReal => (x : ℝ)) (frobenius_nnnorm_partialTranspose M)

end Frobenius

end PartialTranspose

end Matrix
