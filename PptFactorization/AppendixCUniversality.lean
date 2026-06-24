import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic

/-!
# Appendix C: algebraic universality spine

This file is deliberately separate from the earlier scaling-law files.  Its
purpose is to formalise the algebraic spine used in Appendix C of the paper,
without invoking the implicit function theorem.

It now contains seven checked algebraic pieces from the appendix:

* the first-defect coefficient formula as the sum of size-3 and size-4
  exceptional-block contributions;
* the generating-function simplification after the first-defect decomposition;
* the matrix-free trace-sum derivation of the determinant-level trace identity;
* the divided-difference cancellation for the convolution quadratic form;
* the rank-one trace reduction after the adjugate has been reduced to a kernel
  vector;
* the finite-root product divisibility step used after proving rootwise
  vanishing of `Σ`;
* the final divisibility spine that turns the trace identity into the
  universal first-order coefficient `-1`.

The concrete random-matrix and non-crossing-partition work in the paper is
still responsible for producing the following inputs:

* the entrywise matrix relation and Jacobi/adjugate trace identifications that
  feed `traceIdentity_of_entrywise_matrix_relation`;
* the non-crossing first-defect decomposition, named below as
  `FirstDefectDecompositionSupplier`, that supplies the hypotheses of
  `generatingFunction_defect_identity`;
* the determinant divisibility `g ∣ f₀`;
* the corank-one/Chebyshev bridge, named below as `RootwiseRankOneTraceData`,
  that turns the divided-difference cancellation into the convolution-trace
  divisibility `g ∣ Sigma`;
* the coprimality `IsCoprime g X`.

Once the trace/divisibility/coprimality facts are available, the universal
congruence `g ∣ f₁ - derivative f₀` is purely algebraic.  The last theorem below
then turns that congruence into the coefficient `-1` at any root where `f₀'` is
non-zero.
-/

open Polynomial
open scoped BigOperators

namespace AppendixCUniversality

/-
Step 1 starts with a combinatorial supplier: the first unbalanced correction is
the sum of the contributions from exactly one exceptional block of size 3 or 4.
The bijection with non-crossing partitions remains a paper-side input, but the
finite coefficient formula used after that bijection is named here.
-/

section FirstDefectCoefficientFormula

variable {R : Type*} [CommSemiring R]

/-- The coefficient multiplier corresponding to the `r₁ + 1` choices of origin. -/
def weightedMoment (M : ℕ → R) (r : ℕ) : R :=
  ((r + 1 : ℕ) : R) * M r

/-- Contribution of one exceptional block of size `3` to the first defect. -/
def firstDefectSize3 (lam : R) (M : ℕ → R) (k : ℕ) : R :=
  lam * ∑ r1 ∈ Finset.range (k + 1), ∑ r2 ∈ Finset.range (k + 1),
    ∑ r3 ∈ Finset.range (k + 1),
      if r1 + r2 + r3 + 3 = k then weightedMoment M r1 * M r2 * M r3 else 0

/-- Contribution of one exceptional block of size `4` to the first defect. -/
def firstDefectSize4 (lam : R) (M : ℕ → R) (k : ℕ) : R :=
  lam * ∑ r1 ∈ Finset.range (k + 1), ∑ r2 ∈ Finset.range (k + 1),
    ∑ r3 ∈ Finset.range (k + 1), ∑ r4 ∈ Finset.range (k + 1),
      if r1 + r2 + r3 + r4 + 4 = k then
        weightedMoment M r1 * M r2 * M r3 * M r4
      else
        0

/-- The first-defect coefficient after the non-crossing decomposition is supplied. -/
def firstDefectCoeff (lam : R) (M : ℕ → R) (k : ℕ) : R :=
  firstDefectSize3 lam M k + firstDefectSize4 lam M k

/--
Paper-side supplier A.

This is the exact theorem-shaped contract for the first-defect decomposition:
the model-specific first correction `M1` must be the sum of the size-3 and
size-4 exceptional-block contributions for every coefficient.
-/
def FirstDefectDecompositionSupplier (lam : R) (M M1 : ℕ → R) : Prop :=
  ∀ k, M1 k = firstDefectCoeff lam M k

/-- The first defect splits into the size-3 and size-4 exceptional-block cases. -/
theorem firstDefectCoeff_decomposition (lam : R) (M : ℕ → R) (k : ℕ) :
    firstDefectCoeff lam M k = firstDefectSize3 lam M k + firstDefectSize4 lam M k := rfl

/-- Unpack the first-defect supplier at one coefficient. -/
theorem firstDefectCoeff_eq_of_supplier
    (lam : R) (M M1 : ℕ → R)
    (h : FirstDefectDecompositionSupplier lam M M1) (k : ℕ) :
    M1 k = firstDefectSize3 lam M k + firstDefectSize4 lam M k := by
  rw [h k, firstDefectCoeff_decomposition]

end FirstDefectCoefficientFormula

/-
The first block formalises the purely algebraic simplification in Step 1 of
Appendix C.  The paper obtains the hypotheses from the non-crossing first-defect
decomposition and the quadratic equation for the balanced generating function.
Lean checks the final ring calculation: once

  C¹ = λ z² C² C_λ
  D C_λ = - z C² (1 + z C)
  D = λ z² C² - 1
  C - 1 = λ z C (1 + z C),

the claimed coefficient identity is exactly

  λ (C¹ - C_λ) = C - C².
-/

section GeneratingFunctionIdentity

variable {R : Type*} [CommRing R]

/--
Algebraic core of Appendix C's generating-function identity.

This is the formal version of the final simplification in Step 1.  It does not
prove the non-crossing first-defect decomposition; it checks that, after the
generating-function equations have been derived, the defect identity follows by
ring algebra.
-/
theorem generatingFunction_defect_identity
    (lam z C Clam C1 D : R)
    (hC1 : C1 = lam * z ^ 2 * C ^ 2 * Clam)
    (hClam : D * Clam = - z * C ^ 2 * (1 + z * C))
    (hD : D = lam * z ^ 2 * C ^ 2 - 1)
    (hquad : C - 1 = lam * z * C * (1 + z * C)) :
    lam * (C1 - Clam) = C - C ^ 2 := by
  rw [hC1]
  have hfactor :
      lam * (lam * z ^ 2 * C ^ 2 * Clam - Clam)
        = lam * ((lam * z ^ 2 * C ^ 2 - 1) * Clam) := by
    ring
  rw [hfactor, ← hD, hClam]
  have hquad' : lam * z * C * (1 + z * C) = C - 1 := hquad.symm
  calc
    lam * (-z * C ^ 2 * (1 + z * C))
        = -C * (lam * z * C * (1 + z * C)) := by ring
    _ = -C * (C - 1) := by rw [hquad']
    _ = C - C ^ 2 := by ring

end GeneratingFunctionIdentity

/-
The next block formalises the divided-difference cancellation used to show that
the convolution trace vanishes on the kernel direction of the balanced Hankel
matrix.  We write the vector length as `n`; in the paper, `n = r + 1`.
-/

section DividedDifference

variable {A : Type*} [CommSemiring A]

/-- The convolution quadratic form from the divided-difference lemma. -/
def convolutionQuadratic (n : ℕ) (c v : ℕ → A) : A :=
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
    v i * v j * (∑ a ∈ Finset.range (i + j + 2), c a * c (i + j + 1 - a))

/-- The part of the convolution quadratic form with the split index on the left. -/
def leftSplitQuadratic (n : ℕ) (c v : ℕ → A) : A :=
  ∑ i ∈ Finset.range n, ∑ b ∈ Finset.range (i + 1),
    v i * c (i - b) * (∑ j ∈ Finset.range n, v j * c (b + j + 1))

/-- The part of the convolution quadratic form with the split index on the right. -/
def rightSplitQuadratic (n : ℕ) (c v : ℕ → A) : A :=
  ∑ j ∈ Finset.range n, ∑ b ∈ Finset.range (j + 1),
    v j * c (j - b) * (∑ i ∈ Finset.range n, v i * c (i + b + 1))

/-- Splitting the inner convolution sum at `a = i`. -/
theorem convolution_inner_split (c : ℕ → A) (i j : ℕ) :
    (∑ a ∈ Finset.range (i + j + 2), c a * c (i + j + 1 - a)) =
      (∑ b ∈ Finset.range (i + 1), c (i - b) * c (b + j + 1)) +
      (∑ b ∈ Finset.range (j + 1), c (i + 1 + b) * c (j - b)) := by
  have hadd : i + j + 2 = (i + 1) + (j + 1) := by omega
  rw [hadd, Finset.sum_range_add]
  congr 1
  · rw [← Finset.sum_range_reflect (fun x => c x * c (i + j + 1 - x)) (i + 1)]
    refine Finset.sum_congr rfl ?_
    intro b hb
    have hb' : b < i + 1 := Finset.mem_range.mp hb
    have h1 : i + 1 - 1 - b = i - b := by omega
    have h2 : i + j + 1 - (i - b) = b + j + 1 := by omega
    rw [h1, h2]
  · refine Finset.sum_congr rfl ?_
    intro b hb
    have hb' : b < j + 1 := Finset.mem_range.mp hb
    have h2 : i + j + 1 - (i + 1 + b) = j - b := by omega
    rw [h2]

/-- The convolution quadratic form is the sum of the two split forms. -/
theorem convolutionQuadratic_eq_split (n : ℕ) (c v : ℕ → A) :
    convolutionQuadratic n c v = leftSplitQuadratic n c v + rightSplitQuadratic n c v := by
  unfold convolutionQuadratic leftSplitQuadratic rightSplitQuadratic
  calc
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      v i * v j * (∑ a ∈ Finset.range (i + j + 2), c a * c (i + j + 1 - a)))
        = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
            v i * v j * ((∑ b ∈ Finset.range (i + 1), c (i - b) * c (b + j + 1)) +
              (∑ b ∈ Finset.range (j + 1), c (i + 1 + b) * c (j - b))) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [convolution_inner_split]
    _ = (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
            v i * v j * (∑ b ∈ Finset.range (i + 1), c (i - b) * c (b + j + 1))) +
          (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
            v i * v j * (∑ b ∈ Finset.range (j + 1), c (i + 1 + b) * c (j - b))) := by
          simp_rw [mul_add, Finset.sum_add_distrib]
    _ = (∑ i ∈ Finset.range n, ∑ b ∈ Finset.range (i + 1),
            v i * c (i - b) * (∑ j ∈ Finset.range n, v j * c (b + j + 1))) +
          (∑ j ∈ Finset.range n, ∑ b ∈ Finset.range (j + 1),
            v j * c (j - b) * (∑ i ∈ Finset.range n, v i * c (i + b + 1))) := by
          congr 1
          · refine Finset.sum_congr rfl ?_
            intro i hi
            calc
              (∑ j ∈ Finset.range n, v i * v j *
                (∑ b ∈ Finset.range (i + 1), c (i - b) * c (b + j + 1)))
                  = ∑ j ∈ Finset.range n, ∑ b ∈ Finset.range (i + 1),
                      v i * v j * (c (i - b) * c (b + j + 1)) := by
                    refine Finset.sum_congr rfl ?_
                    intro j hj
                    rw [Finset.mul_sum]
              _ = ∑ b ∈ Finset.range (i + 1), ∑ j ∈ Finset.range n,
                      v i * v j * (c (i - b) * c (b + j + 1)) := by
                    rw [Finset.sum_comm]
              _ = ∑ b ∈ Finset.range (i + 1),
                    v i * c (i - b) * (∑ j ∈ Finset.range n, v j * c (b + j + 1)) := by
                    refine Finset.sum_congr rfl ?_
                    intro b hb
                    rw [Finset.mul_sum]
                    refine Finset.sum_congr rfl ?_
                    intro j hj
                    ring_nf
          · calc
              (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
                v i * v j * (∑ b ∈ Finset.range (j + 1), c (i + 1 + b) * c (j - b)))
                  = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, ∑ b ∈ Finset.range (j + 1),
                      v i * v j * (c (i + 1 + b) * c (j - b)) := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    refine Finset.sum_congr rfl ?_
                    intro j hj
                    rw [Finset.mul_sum]
              _ = ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range n, ∑ b ∈ Finset.range (j + 1),
                      v i * v j * (c (i + 1 + b) * c (j - b)) := by
                    rw [Finset.sum_comm]
              _ = ∑ j ∈ Finset.range n, ∑ b ∈ Finset.range (j + 1), ∑ i ∈ Finset.range n,
                      v i * v j * (c (i + 1 + b) * c (j - b)) := by
                    refine Finset.sum_congr rfl ?_
                    intro j hj
                    rw [Finset.sum_comm]
              _ = ∑ j ∈ Finset.range n, ∑ b ∈ Finset.range (j + 1),
                    v j * c (j - b) * (∑ i ∈ Finset.range n, v i * c (i + b + 1)) := by
                    refine Finset.sum_congr rfl ?_
                    intro j hj
                    refine Finset.sum_congr rfl ?_
                    intro b hb
                    rw [Finset.mul_sum]
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    ring_nf

/-- The left split form vanishes under the Hankel orthogonality hypothesis. -/
theorem leftSplitQuadratic_eq_zero (n : ℕ) (c v : ℕ → A)
    (h : ∀ b, b < n → (∑ j ∈ Finset.range n, v j * c (b + j + 1)) = 0) :
    leftSplitQuadratic n c v = 0 := by
  unfold leftSplitQuadratic
  refine Finset.sum_eq_zero ?_
  intro i hi
  refine Finset.sum_eq_zero ?_
  intro b hb
  have hi' : i < n := Finset.mem_range.mp hi
  have hb' : b < i + 1 := Finset.mem_range.mp hb
  have hbn : b < n := by omega
  rw [h b hbn]
  simp

/-- The right split form vanishes under the same Hankel orthogonality hypothesis. -/
theorem rightSplitQuadratic_eq_zero (n : ℕ) (c v : ℕ → A)
    (h : ∀ b, b < n → (∑ i ∈ Finset.range n, v i * c (i + b + 1)) = 0) :
    rightSplitQuadratic n c v = 0 := by
  unfold rightSplitQuadratic
  refine Finset.sum_eq_zero ?_
  intro j hj
  refine Finset.sum_eq_zero ?_
  intro b hb
  have hj' : j < n := Finset.mem_range.mp hj
  have hb' : b < j + 1 := Finset.mem_range.mp hb
  have hbn : b < n := by omega
  rw [h b hbn]
  simp

/-- The divided-difference cancellation used in Appendix C. -/
theorem dividedDifference_convolutionQuadratic_eq_zero (n : ℕ) (c v : ℕ → A)
    (h : ∀ b, b < n → (∑ j ∈ Finset.range n, v j * c (b + j + 1)) = 0) :
    convolutionQuadratic n c v = 0 := by
  rw [convolutionQuadratic_eq_split]
  have hleft : leftSplitQuadratic n c v = 0 := leftSplitQuadratic_eq_zero n c v h
  have hright_h : ∀ b, b < n → (∑ i ∈ Finset.range n, v i * c (i + b + 1)) = 0 := by
    intro b hb
    calc
      (∑ i ∈ Finset.range n, v i * c (i + b + 1)) =
          (∑ i ∈ Finset.range n, v i * c (b + i + 1)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hidx : i + b + 1 = b + i + 1 := by omega
            rw [hidx]
      _ = 0 := h b hb
  have hright : rightSplitQuadratic n c v = 0 := rightSplitQuadratic_eq_zero n c v hright_h
  rw [hleft, hright, zero_add]

/--
The divided-difference cancellation in the paper's indexing convention
`0 ≤ i,j ≤ r`.
-/
theorem dividedDifference_convolutionQuadratic_eq_zero_range (r : ℕ) (c v : ℕ → A)
    (h : ∀ i, i ≤ r → (∑ j ∈ Finset.range (r + 1), v j * c (i + j + 1)) = 0) :
    (∑ i ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (r + 1),
      v i * v j * (∑ a ∈ Finset.range (i + j + 2), c a * c (i + j + 1 - a))) = 0 := by
  have h' : ∀ b, b < r + 1 →
      (∑ j ∈ Finset.range (r + 1), v j * c (b + j + 1)) = 0 := by
    intro b hb
    exact h b (by omega)
  simpa [convolutionQuadratic] using
    dividedDifference_convolutionQuadratic_eq_zero (r + 1) c v h'

/--
Once the adjugate trace has been reduced to a scalar multiple of the convolution
quadratic form, the divided-difference cancellation kills it.

In the paper this is the algebraic part of
`Σ_m(α)=q · vᵀ H_m^{[2]}(α) v=0`, after the corank-one matrix argument has
produced the scalar `q` and the kernel vector `v`.
-/
theorem rankOneConvolutionTrace_eq_zero (n : ℕ) (c v : ℕ → A) (q : A)
    (h : ∀ b, b < n → (∑ j ∈ Finset.range n, v j * c (b + j + 1)) = 0) :
    q * convolutionQuadratic n c v = 0 := by
  rw [dividedDifference_convolutionQuadratic_eq_zero n c v h, mul_zero]

/--
A version with an explicitly named trace value, useful for reading the paper's
`Σ_m(α)` step: if the trace value is a scalar multiple of the convolution
quadratic form, then it is zero.
-/
theorem sigmaRoot_eq_zero_of_rankOne_trace_formula (n : ℕ) (c v : ℕ → A) (q sigma : A)
    (hSigma : sigma = q * convolutionQuadratic n c v)
    (h : ∀ b, b < n → (∑ j ∈ Finset.range n, v j * c (b + j + 1)) = 0) :
    sigma = 0 := by
  rw [hSigma]
  exact rankOneConvolutionTrace_eq_zero n c v q h

/--
Paper-indexed version of `sigmaRoot_eq_zero_of_rankOne_trace_formula`, with
indices `0 ≤ i,j ≤ r`.
-/
theorem sigmaRoot_eq_zero_of_rankOne_trace_formula_range
    (r : ℕ) (c v : ℕ → A) (q sigma : A)
    (hSigma : sigma =
      q * (∑ i ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (r + 1),
        v i * v j * (∑ a ∈ Finset.range (i + j + 2), c a * c (i + j + 1 - a))))
    (h : ∀ i, i ≤ r → (∑ j ∈ Finset.range (r + 1), v j * c (i + j + 1)) = 0) :
    sigma = 0 := by
  rw [hSigma]
  rw [dividedDifference_convolutionQuadratic_eq_zero_range r c v h, mul_zero]

end DividedDifference

section RootwiseDivisibility

variable {K : Type*} [Field K]

/-- Distinct linear factors over a field are coprime. -/
theorem linearFactor_isCoprime_of_ne (a b : K) (h : a ≠ b) :
    IsCoprime (X - C a : K[X]) (X - C b : K[X]) := by
  refine ⟨C ((b - a)⁻¹), -C ((b - a)⁻¹), ?_⟩
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  calc
    C ((b - a)⁻¹) * (X - C a) + -C ((b - a)⁻¹) * (X - C b)
        = C ((b - a)⁻¹) * C (b - a) := by
          ring_nf
          rw [← C_mul, ← C_mul, ← C_mul]
          rw [← C_neg, ← C_add]
          congr 1
          ring
    _ = 1 := by
      rw [← C_mul, inv_mul_cancel₀ hba, C_1]

/-- A linear factor is coprime to the product of all other listed linear factors. -/
theorem linearFactor_isCoprime_prod_of_not_mem (a : K) (s : Finset K) (ha : a ∉ s) :
    IsCoprime (X - C a : K[X]) (∏ b ∈ s, (X - C b : K[X])) := by
  refine IsCoprime.prod_right ?_
  intro b hb
  apply linearFactor_isCoprime_of_ne
  intro hab
  exact ha (by simpa [hab] using hb)

/--
If a polynomial vanishes at every point of a finite set, then the product of
the corresponding distinct linear factors divides it.

This is the algebraic rootwise-vanishing-to-divisibility step used in Appendix
C after proving `Σ_m(α)=0` at every explicitly listed root of `g_m`.
-/
theorem prod_linearFactors_dvd_of_eval_zero (s : Finset K) (p : K[X])
    (h : ∀ a, a ∈ s → eval a p = 0) :
    (∏ a ∈ s, (X - C a : K[X])) ∣ p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have hlin : (X - C a : K[X]) ∣ p := by
        rw [Polynomial.dvd_iff_isRoot]
        exact h a (by simp)
      have hprod : (∏ b ∈ s, (X - C b : K[X])) ∣ p := by
        apply ih
        intro b hb
        exact h b (by simp [hb])
      have hcop : IsCoprime (X - C a : K[X]) (∏ b ∈ s, (X - C b : K[X])) :=
        linearFactor_isCoprime_prod_of_not_mem a s ha
      exact hcop.mul_dvd hlin hprod

end RootwiseDivisibility

variable {R : Type*} [CommRing R]

/-
Step 2 in the paper is a trace calculation.  We keep it matrix-free here by
writing the trace against an abstract cofactor matrix as a double finite sum.
This is enough to certify the algebraic passage from the entrywise matrix
relation

  X · (H¹ - H') = H - H²

to the determinant-level identity

  X · (f₁ - f₀') = (m+1)f₀ - Σ.
-/

section TraceSums

/-- Abstract trace pairing `Tr(A B)` written as a double sum. -/
noncomputable def tracePair (n : ℕ) (A B : ℕ → ℕ → R[X]) : R[X] :=
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, A i j * B j i

/--
If the entrywise matrix relation holds, then tracing against the same cofactor
matrix gives the corresponding scalar relation.
-/
theorem tracePair_entrywise_relation
    (n : ℕ) (A B1 Bp H H2 : ℕ → ℕ → R[X])
    (hrel : ∀ i, i < n → ∀ j, j < n →
      X * (B1 j i - Bp j i) = H j i - H2 j i) :
    X * (tracePair n A B1 - tracePair n A Bp) =
      tracePair n A H - tracePair n A H2 := by
  unfold tracePair
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hi' : i < n := Finset.mem_range.mp hi
  have hj' : j < n := Finset.mem_range.mp hj
  calc
    X * (A i j * B1 j i - A i j * Bp j i)
        = A i j * (X * (B1 j i - Bp j i)) := by ring
    _ = A i j * (H j i - H2 j i) := by rw [hrel i hi' j hj']
    _ = A i j * H j i - A i j * H2 j i := by ring

end TraceSums

/-- The determinant-level trace identity used in Appendix C. -/
def TraceIdentity (m : ℕ) (f₀ f₁ Sigma : R[X]) : Prop :=
  X * (f₁ - derivative f₀) = C ((m + 1 : ℕ) : R) * f₀ - Sigma

/--
Matrix-free formal version of Appendix C, Step 2.

The hypotheses are exactly the named scalar consequences of Jacobi's formula
and the adjugate identity:

* `f₁` is the trace pairing with the first finite-`d₁` correction;
* `derivative f₀` is the trace pairing with the balanced `λ`-derivative;
* `Sigma` is the trace pairing with the convolution Hankel matrix;
* tracing `adj(H_m) H_m` gives `(m+1)f₀`;
* the entrywise relation is `X(H¹-H')=H-H²`.
-/
theorem traceIdentity_of_entrywise_matrix_relation
    (m n : ℕ) (A B1 Bp H H2 : ℕ → ℕ → R[X]) (f₀ f₁ Sigma : R[X])
    (hf₁ : f₁ = tracePair n A B1)
    (hf₀' : derivative f₀ = tracePair n A Bp)
    (hSigma : Sigma = tracePair n A H2)
    (hbalanced : tracePair n A H = C ((m + 1 : ℕ) : R) * f₀)
    (hrel : ∀ i, i < n → ∀ j, j < n →
      X * (B1 j i - Bp j i) = H j i - H2 j i) :
    TraceIdentity m f₀ f₁ Sigma := by
  unfold TraceIdentity
  rw [hf₁, hf₀', hSigma, ← hbalanced]
  exact tracePair_entrywise_relation n A B1 Bp H H2 hrel

/--
Appendix C's algebraic core.

If the universality trace identity holds and the two right-hand terms are both
divisible by `g`, then `g` divides `X * (f₁ - f₀')`.  Since `g` is coprime to
`X`, the factor `X` can be cancelled, giving the desired congruence
`f₁ ≡ f₀' mod g`.
-/
theorem universality_congruence_of_trace_identity
    (m : ℕ) (g f₀ f₁ Sigma : R[X])
    (htrace : TraceIdentity m f₀ f₁ Sigma)
    (hg_f₀ : g ∣ f₀)
    (hg_Sigma : g ∣ Sigma)
    (hcop : IsCoprime g X) :
    g ∣ f₁ - derivative f₀ := by
  have hright : g ∣ C ((m + 1 : ℕ) : R) * f₀ - Sigma := by
    exact dvd_sub (dvd_mul_of_dvd_right hg_f₀ _) hg_Sigma
  have hmul : g ∣ X * (f₁ - derivative f₀) := by
    rw [htrace]
    exact hright
  exact hcop.dvd_of_dvd_mul_left hmul

variable {K : Type*} [Field K]

/--
Paper-side supplier B.

At each listed threshold root, the Chebyshev/corank-one argument must produce a
rank-one trace formula for `Sigma` and the Hankel-kernel orthogonality equations
for the same vector.  This definition is only a named contract: it does not
prove the spectral supplier.
-/
def RootwiseRankOneTraceData
    (m : ℕ) (roots : Finset K) (Sigma : K[X])
    (q : K → K) (c v : K → ℕ → K) : Prop :=
  (∀ a, a ∈ roots →
    eval a Sigma =
      q a * (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        v a i * v a j *
          (∑ b ∈ Finset.range (i + j + 2),
            c a b * c a (i + j + 1 - b)))) ∧
  (∀ a, a ∈ roots → ∀ i, i ≤ m →
    (∑ j ∈ Finset.range (m + 1), v a j * c a (i + j + 1)) = 0)

/--
The named rootwise trace-data supplier implies rootwise vanishing of `Sigma`.
This is the exact interface between the paper's Chebyshev/corank-one work and
the Lean-checked divided-difference cancellation.
-/
theorem sigma_roots_eq_zero_of_rootwiseRankOneTraceData
    (m : ℕ) (roots : Finset K) (Sigma : K[X])
    (q : K → K) (c v : K → ℕ → K)
    (hdata : RootwiseRankOneTraceData m roots Sigma q c v) :
    ∀ a, a ∈ roots → eval a Sigma = 0 := by
  intro a ha
  rcases hdata with ⟨hSigma, hkernel⟩
  exact sigmaRoot_eq_zero_of_rankOne_trace_formula_range
    m (c a) (v a) (q a) (eval a Sigma) (hSigma a ha) (hkernel a ha)

/--
Rootwise version of the final congruence.

Instead of assuming `g ∣ Sigma` directly, assume that `g` is the product of the
listed linear factors and that `Sigma` vanishes at every listed root.
-/
theorem universality_congruence_of_trace_identity_rootwise
    (m : ℕ) (roots : Finset K) (g f₀ f₁ Sigma : K[X])
    (htrace : TraceIdentity m f₀ f₁ Sigma)
    (hg_f₀ : g ∣ f₀)
    (hg_prod : g = ∏ a ∈ roots, (X - C a : K[X]))
    (hSigma_roots : ∀ a, a ∈ roots → eval a Sigma = 0)
    (hcop : IsCoprime g X) :
    g ∣ f₁ - derivative f₀ := by
  have hg_Sigma : g ∣ Sigma := by
    rw [hg_prod]
    exact prod_linearFactors_dvd_of_eval_zero roots Sigma hSigma_roots
  exact universality_congruence_of_trace_identity m g f₀ f₁ Sigma htrace
    hg_f₀ hg_Sigma hcop

/-- A divisibility congruence gives equality after evaluating at a root of `g`. -/
theorem eval_f₁_eq_eval_derivative_of_root
    (g f₀ f₁ : K[X]) (α : K)
    (hdiv : g ∣ f₁ - derivative f₀)
    (hroot : eval α g = 0) :
    eval α f₁ = eval α (derivative f₀) := by
  rcases hdiv with ⟨q, hq⟩
  have hzero : eval α (f₁ - derivative f₀) = 0 := by
    rw [hq, eval_mul, hroot, zero_mul]
  have hsub : eval α f₁ - eval α (derivative f₀) = 0 := by
    simpa using hzero
  exact sub_eq_zero.mp hsub

/-- The coefficient equation in the truncated first-order calculation. -/
theorem first_order_coefficient_eq_neg_ratio
    {c f₀' f₁val : K}
    (hf₀' : f₀' ≠ 0)
    (hcoeff : c * f₀' + f₁val = 0) :
    c = -f₁val / f₀' := by
  have hmul : c * f₀' = -f₁val := eq_neg_of_add_eq_zero_left hcoeff
  calc
    c = (c * f₀') / f₀' := by field_simp [hf₀']
    _ = -f₁val / f₀' := by rw [hmul]

/-- If the two evaluated determinant responses agree, the ratio coefficient is `-1`. -/
theorem first_order_ratio_eq_neg_one_of_eq
    {f₀' f₁val : K}
    (hf₀' : f₀' ≠ 0)
    (heq : f₁val = f₀') :
    -f₁val / f₀' = -1 := by
  rw [heq]
  field_simp [hf₀']

/--
Once the Appendix C congruence is known, the first-order threshold coefficient
at any simple non-zero threshold root is `-1`.
-/
theorem first_order_coefficient_eq_neg_one_of_trace_identity
    (m : ℕ) (g f₀ f₁ Sigma : K[X]) (α : K)
    (htrace : TraceIdentity m f₀ f₁ Sigma)
    (hg_f₀ : g ∣ f₀)
    (hg_Sigma : g ∣ Sigma)
    (hcop : IsCoprime g X)
    (hroot : eval α g = 0)
    (hf₀' : eval α (derivative f₀) ≠ 0) :
    - eval α f₁ / eval α (derivative f₀) = -1 := by
  have hdiv : g ∣ f₁ - derivative f₀ :=
    universality_congruence_of_trace_identity m g f₀ f₁ Sigma htrace
      hg_f₀ hg_Sigma hcop
  have heq : eval α f₁ = eval α (derivative f₀) :=
    eval_f₁_eq_eval_derivative_of_root g f₀ f₁ α hdiv hroot
  exact first_order_ratio_eq_neg_one_of_eq hf₀' heq

/--
Rootwise version of the coefficient theorem.  This matches the Appendix C route
where `Σ_m(α)=0` is proved at each listed threshold root before concluding
divisibility.
-/
theorem first_order_coefficient_eq_neg_one_of_trace_identity_rootwise
    (m : ℕ) (roots : Finset K) (g f₀ f₁ Sigma : K[X]) (α : K)
    (htrace : TraceIdentity m f₀ f₁ Sigma)
    (hg_f₀ : g ∣ f₀)
    (hg_prod : g = ∏ a ∈ roots, (X - C a : K[X]))
    (hSigma_roots : ∀ a, a ∈ roots → eval a Sigma = 0)
    (hcop : IsCoprime g X)
    (hroot : eval α g = 0)
    (hf₀' : eval α (derivative f₀) ≠ 0) :
    - eval α f₁ / eval α (derivative f₀) = -1 := by
  have hdiv : g ∣ f₁ - derivative f₀ :=
    universality_congruence_of_trace_identity_rootwise m roots g f₀ f₁ Sigma htrace
      hg_f₀ hg_prod hSigma_roots hcop
  have heq : eval α f₁ = eval α (derivative f₀) :=
    eval_f₁_eq_eval_derivative_of_root g f₀ f₁ α hdiv hroot
  exact first_order_ratio_eq_neg_one_of_eq hf₀' heq

/--
Integrated rootwise Appendix C spine using the named spectral supplier.

This is the same algebraic endpoint as
`first_order_coefficient_eq_neg_one_of_rootwise_rankOne_trace_data`, but with
the paper-side Chebyshev/corank-one package exposed under the shorter contract
`RootwiseRankOneTraceData`.
-/
theorem first_order_coefficient_eq_neg_one_of_rootwiseRankOneTraceData
    (m : ℕ) (roots : Finset K) (g f₀ f₁ Sigma : K[X]) (α : K)
    (q : K → K) (c v : K → ℕ → K)
    (htrace : TraceIdentity m f₀ f₁ Sigma)
    (hg_f₀ : g ∣ f₀)
    (hg_prod : g = ∏ a ∈ roots, (X - C a : K[X]))
    (hdata : RootwiseRankOneTraceData m roots Sigma q c v)
    (hcop : IsCoprime g X)
    (hroot : eval α g = 0)
    (hf₀' : eval α (derivative f₀) ≠ 0) :
    - eval α f₁ / eval α (derivative f₀) = -1 := by
  have hSigma_roots : ∀ a, a ∈ roots → eval a Sigma = 0 :=
    sigma_roots_eq_zero_of_rootwiseRankOneTraceData m roots Sigma q c v hdata
  exact first_order_coefficient_eq_neg_one_of_trace_identity_rootwise
    m roots g f₀ f₁ Sigma α htrace hg_f₀ hg_prod hSigma_roots hcop hroot hf₀'

/--
Coefficient-extraction endpoint using the named spectral supplier.

The coefficient equation comes from the selected truncated root expansion; the
rootwise trace data is still an explicit paper-side supplier.
-/
theorem selected_first_order_coefficient_eq_neg_one_of_rootwiseRankOneTraceData
    (m : ℕ) (roots : Finset K) (g f₀ f₁ Sigma : K[X]) (α coeff : K)
    (q : K → K) (c v : K → ℕ → K)
    (hcoeff : coeff * eval α (derivative f₀) + eval α f₁ = 0)
    (htrace : TraceIdentity m f₀ f₁ Sigma)
    (hg_f₀ : g ∣ f₀)
    (hg_prod : g = ∏ a ∈ roots, (X - C a : K[X]))
    (hdata : RootwiseRankOneTraceData m roots Sigma q c v)
    (hcop : IsCoprime g X)
    (hroot : eval α g = 0)
    (hf₀' : eval α (derivative f₀) ≠ 0) :
    coeff = -1 := by
  have hratio : - eval α f₁ / eval α (derivative f₀) = -1 :=
    first_order_coefficient_eq_neg_one_of_rootwiseRankOneTraceData
      m roots g f₀ f₁ Sigma α q c v htrace hg_f₀ hg_prod hdata hcop hroot hf₀'
  have hcoeff_ratio : coeff = - eval α f₁ / eval α (derivative f₀) :=
    first_order_coefficient_eq_neg_ratio hf₀' hcoeff
  rw [hcoeff_ratio]
  exact hratio

/--
Integrated rootwise Appendix C spine.

This theorem consumes the exact data produced in the paper after the
Chebyshev/corank-one argument: at each listed root, the trace value `Σ(α)` is a
scalar multiple of the convolution quadratic form in a kernel vector, and that
kernel vector satisfies the Hankel orthogonality relations.  Lean then performs
the divided-difference cancellation, the finite-root divisibility step, the
trace-identity cancellation, and the final coefficient calculation.
-/
theorem first_order_coefficient_eq_neg_one_of_rootwise_rankOne_trace_data
    (m : ℕ) (roots : Finset K) (g f₀ f₁ Sigma : K[X]) (α : K)
    (q : K → K) (c v : K → ℕ → K)
    (htrace : TraceIdentity m f₀ f₁ Sigma)
    (hg_f₀ : g ∣ f₀)
    (hg_prod : g = ∏ a ∈ roots, (X - C a : K[X]))
    (hSigma : ∀ a, a ∈ roots →
      eval a Sigma =
        q a * (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          v a i * v a j *
            (∑ b ∈ Finset.range (i + j + 2),
              c a b * c a (i + j + 1 - b))))
    (hkernel : ∀ a, a ∈ roots → ∀ i, i ≤ m →
      (∑ j ∈ Finset.range (m + 1), v a j * c a (i + j + 1)) = 0)
    (hcop : IsCoprime g X)
    (hroot : eval α g = 0)
    (hf₀' : eval α (derivative f₀) ≠ 0) :
    - eval α f₁ / eval α (derivative f₀) = -1 := by
  have hSigma_roots : ∀ a, a ∈ roots → eval a Sigma = 0 := by
    intro a ha
    exact sigmaRoot_eq_zero_of_rankOne_trace_formula_range
      m (c a) (v a) (q a) (eval a Sigma) (hSigma a ha) (hkernel a ha)
  exact first_order_coefficient_eq_neg_one_of_trace_identity_rootwise
    m roots g f₀ f₁ Sigma α htrace hg_f₀ hg_prod hSigma_roots hcop hroot hf₀'

/--
Integrated coefficient-extraction version of the Appendix C spine.

The paper first obtains the coefficient equation

  `coeff * f₀'(α) + f₁(α) = 0`

from the truncated first-order expansion of the selected local root.  This
theorem combines that equation with the rootwise rank-one trace data above and
returns the actual coefficient value `coeff = -1`.
-/
theorem selected_first_order_coefficient_eq_neg_one_of_rootwise_rankOne_trace_data
    (m : ℕ) (roots : Finset K) (g f₀ f₁ Sigma : K[X]) (α coeff : K)
    (q : K → K) (c v : K → ℕ → K)
    (hcoeff : coeff * eval α (derivative f₀) + eval α f₁ = 0)
    (htrace : TraceIdentity m f₀ f₁ Sigma)
    (hg_f₀ : g ∣ f₀)
    (hg_prod : g = ∏ a ∈ roots, (X - C a : K[X]))
    (hSigma : ∀ a, a ∈ roots →
      eval a Sigma =
        q a * (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          v a i * v a j *
            (∑ b ∈ Finset.range (i + j + 2),
              c a b * c a (i + j + 1 - b))))
    (hkernel : ∀ a, a ∈ roots → ∀ i, i ≤ m →
      (∑ j ∈ Finset.range (m + 1), v a j * c a (i + j + 1)) = 0)
    (hcop : IsCoprime g X)
    (hroot : eval α g = 0)
    (hf₀' : eval α (derivative f₀) ≠ 0) :
    coeff = -1 := by
  have hratio : - eval α f₁ / eval α (derivative f₀) = -1 :=
    first_order_coefficient_eq_neg_one_of_rootwise_rankOne_trace_data
      m roots g f₀ f₁ Sigma α q c v htrace hg_f₀ hg_prod hSigma hkernel hcop hroot hf₀'
  have hcoeff_ratio : coeff = - eval α f₁ / eval α (derivative f₀) :=
    first_order_coefficient_eq_neg_ratio hf₀' hcoeff
  rw [hcoeff_ratio]
  exact hratio

end AppendixCUniversality
