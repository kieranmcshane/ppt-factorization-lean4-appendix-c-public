import PptFactorization.ComplexGaussianWick
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Trace-power Wick expansion scaffolding

This file formalizes the finite combinatorial rewrite behind moments of the
off-diagonal partial-transposed Wishart matrix.

The closed result here has two layers:

* `trace_pow_succ_eq_closedWalk_sum`: a matrix trace power is exactly a finite
  sum over closed walks.
* `expected_trace_pow_succ_eq_wick_sum_of_monomial_expansion`: once each
  closed-walk product is expanded as a finite linear combination of Gaussian
  entry monomials, expectation rewrites as the corresponding finite Wick sum.

The file also introduces the canonical off-diagonal matrix
`wishartGammaOffDiagonal`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.Frobenius

noncomputable section

namespace PptFactorization
namespace TraceWickExpansion

open RandomMatrixModel GaussianModel ComplexGaussianWick

variable {ι Ω₀ η : Type*}

/-! ## Off-diagonal matrices and the concrete `Z` -/

/-- The diagonal part of a square complex matrix. -/
def diagonalPart [DecidableEq ι] (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Matrix.diagonal fun i => A i i

/-- The off-diagonal part of a square complex matrix. -/
def offDiagonal [DecidableEq ι] (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  A - diagonalPart A

@[simp] theorem diagonalPart_apply [DecidableEq ι]
    (A : Matrix ι ι ℂ) (i j : ι) :
    diagonalPart A i j = if i = j then A i i else 0 := by
  by_cases h : i = j
  · simp [diagonalPart, h]
  · simp [diagonalPart, h]

@[simp] theorem offDiagonal_apply [DecidableEq ι]
    (A : Matrix ι ι ℂ) (i j : ι) :
    offDiagonal A i j = if i = j then 0 else A i j := by
  by_cases h : i = j
  · simp [offDiagonal, h]
  · simp [offDiagonal, h]

/-- The paper's `Z`: the off-diagonal part of the normalized partial-transposed
Wishart matrix `W^Γ`. -/
def wishartGammaOffDiagonal
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    (G : SampleMatrix p q σ) : BipMatrix p q :=
  offDiagonal (wishartGamma (p := p) (q := q) (σ := σ) G)

@[simp] theorem wishartGammaOffDiagonal_apply
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    (G : SampleMatrix p q σ) (i j : BipIndex p q) :
    wishartGammaOffDiagonal (p := p) (q := q) (σ := σ) G i j =
      if i = j then 0 else wishartGamma (p := p) (q := q) (σ := σ) G i j := by
  simp [wishartGammaOffDiagonal]

theorem wishartGamma_eq_diagonalPart_add_offDiagonal
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    (G : SampleMatrix p q σ) :
    wishartGamma (p := p) (q := q) (σ := σ) G =
      diagonalPart (wishartGamma (p := p) (q := q) (σ := σ) G) +
        wishartGammaOffDiagonal (p := p) (q := q) (σ := σ) G := by
  ext i j
  by_cases h : i = j
  · simp [h, wishartGammaOffDiagonal, offDiagonal, diagonalPart]
  · simp [h, wishartGammaOffDiagonal, offDiagonal, diagonalPart]

@[simp] theorem wishartGammaOffDiagonal_diag
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    (G : SampleMatrix p q σ) (i : BipIndex p q) :
    wishartGammaOffDiagonal (p := p) (q := q) (σ := σ) G i i = 0 := by
  simp [wishartGammaOffDiagonal]

/-! ## Closed walks for trace powers -/

/-- A closed walk of length `m + 1`, represented by a base point and `m`
intermediate vertices. -/
abbrev ClosedWalk (ι : Type*) (m : ℕ) :=
  ι × (Fin m → ι)

/-- Product of matrix entries along the path from `i` to `j` through `m`
intermediate vertices.  For trace powers we set `j = i`. -/
def pathProduct (A : Matrix ι ι ℂ) (i j : ι) :
    (m : ℕ) → (Fin m → ι) → ℂ
  | 0, _ => A i j
  | m + 1, x => A i (x 0) * pathProduct A (x 0) j m (Fin.tail x)

@[simp] theorem pathProduct_zero (A : Matrix ι ι ℂ) (i j : ι)
    (x : Fin 0 → ι) :
    pathProduct A i j 0 x = A i j :=
  rfl

@[simp] theorem pathProduct_succ (A : Matrix ι ι ℂ) (i j : ι)
    (m : ℕ) (x : Fin (m + 1) → ι) :
    pathProduct A i j (m + 1) x =
      A i (x 0) * pathProduct A (x 0) j m (Fin.tail x) :=
  rfl

/-- Closed-walk product for a trace-power term. -/
def closedWalkProduct (A : Matrix ι ι ℂ) {m : ℕ}
    (w : ClosedWalk ι m) : ℂ :=
  pathProduct A w.1 w.1 m w.2

theorem sum_pathProduct_succ [Fintype ι]
    (A : Matrix ι ι ℂ) (i j : ι) (m : ℕ) :
    (∑ x : Fin (m + 1) → ι, pathProduct A i j (m + 1) x) =
      ∑ k : ι, ∑ y : Fin m → ι, A i k * pathProduct A k j m y := by
  let e : ι × (Fin m → ι) ≃ (Fin (m + 1) → ι) :=
    Fin.consEquiv fun _ : Fin (m + 1) => ι
  calc
    (∑ x : Fin (m + 1) → ι, pathProduct A i j (m + 1) x)
        = ∑ ky : ι × (Fin m → ι),
            pathProduct A i j (m + 1) (e ky) := by
          exact (Equiv.sum_comp e
            (fun x : Fin (m + 1) → ι => pathProduct A i j (m + 1) x)).symm
    _ = ∑ ky : ι × (Fin m → ι),
          A i ky.1 * pathProduct A ky.1 j m ky.2 := by
          refine Finset.sum_congr rfl ?_
          intro ky _
          cases ky with
          | mk k y =>
              simp [e, Fin.consEquiv, pathProduct]
    _ = ∑ k : ι, ∑ y : Fin m → ι,
          A i k * pathProduct A k j m y := by
          rw [Fintype.sum_prod_type]

theorem matrix_pow_succ_apply_eq_path_sum [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (m : ℕ) (i j : ι) :
    (A ^ (m + 1)) i j =
      ∑ x : Fin m → ι, pathProduct A i j m x := by
  induction m generalizing i with
  | zero =>
      simp [pathProduct]
  | succ m ih =>
      rw [pow_succ']
      simp only [Matrix.mul_apply]
      rw [sum_pathProduct_succ]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [ih]
      simp [Finset.mul_sum]

/-- Trace powers are finite sums over closed walks.  The exponent is written
as `m + 1` to avoid the degenerate `0`-power trace. -/
theorem trace_pow_succ_eq_closedWalk_sum [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (m : ℕ) :
    (A ^ (m + 1)).trace =
      ∑ w : ClosedWalk ι m, closedWalkProduct A w := by
  rw [Matrix.trace]
  calc
    (∑ i : ι, (A ^ (m + 1)) i i)
        = ∑ i : ι, ∑ x : Fin m → ι, pathProduct A i i m x := by
          refine Finset.sum_congr rfl ?_
          intro i _
          exact matrix_pow_succ_apply_eq_path_sum A m i i
    _ = ∑ w : ClosedWalk ι m, closedWalkProduct A w := by
          rw [Fintype.sum_prod_type]
          rfl

/-! ## Wick rewrite for expanded closed-walk products -/

/-- A finite monomial expansion of every closed-walk product. -/
structure ClosedWalkMonomialExpansion
    [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω₀] [DecidableEq η]
    (μ : Measure Ω₀) (Z : Ω₀ → Matrix ι ι ℂ) (g : Ω₀ → η → ℂ)
    (m : ℕ) where
  Term : ClosedWalk ι m → Type*
  termFintype : ∀ w, Fintype (Term w)
  coeff : ∀ w, Term w → ℂ
  monomial : ∀ w, Term w → EntryMonomial η
  closedWalkProduct_eq :
    ∀ (ω : Ω₀) (w : ClosedWalk ι m),
      closedWalkProduct (Z ω) w =
        ∑ t : Term w, coeff w t * (monomial w t).eval (g ω)

attribute [instance] ClosedWalkMonomialExpansion.termFintype

/-- The Wick-side finite sum attached to a closed-walk monomial expansion. -/
def closedWalkWickSum
    [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω₀] [DecidableEq η]
    {μ : Measure Ω₀} {Z : Ω₀ → Matrix ι ι ℂ} {g : Ω₀ → η → ℂ}
    {m : ℕ} (E : ClosedWalkMonomialExpansion μ Z g m) : ℂ :=
  ∑ w : ClosedWalk ι m, ∑ t : E.Term w,
    E.coeff w t * wickExpansion (E.monomial w t)

/-- The trace-power integrability part of the Wick expansion.  Once every
closed-walk product is a finite linear combination of Gaussian entry monomials,
the trace power itself is integrable because Wick moments include integrability
of every entry monomial. -/
theorem trace_pow_succ_integrable_of_monomial_expansion
    [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω₀] [DecidableEq η]
    {μ : Measure Ω₀} {Z : Ω₀ → Matrix ι ι ℂ} {g : Ω₀ → η → ℂ}
    {m : ℕ}
    (hWick : HasComplexGaussianWickMoments μ g)
    (E : ClosedWalkMonomialExpansion μ Z g m) :
    Integrable (fun ω : Ω₀ => ((Z ω) ^ (m + 1)).trace) μ := by
  have hTrace :
      (fun ω : Ω₀ => ((Z ω) ^ (m + 1)).trace) =
        fun ω : Ω₀ =>
          ∑ w : ClosedWalk ι m, ∑ t : E.Term w,
            E.coeff w t * (E.monomial w t).eval (g ω) := by
    funext ω
    rw [trace_pow_succ_eq_closedWalk_sum]
    refine Finset.sum_congr rfl ?_
    intro w _
    exact E.closedWalkProduct_eq ω w
  rw [hTrace]
  exact integrable_finset_sum _ fun w _ =>
    integrable_finset_sum _ fun t _ =>
      (hWick.integrable_entryMonomial (E.monomial w t)).const_mul _

theorem expected_trace_pow_succ_eq_wick_sum_of_monomial_expansion
    [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω₀] [DecidableEq η]
    {μ : Measure Ω₀} {Z : Ω₀ → Matrix ι ι ℂ} {g : Ω₀ → η → ℂ}
    {m : ℕ}
    (hWick : HasComplexGaussianWickMoments μ g)
    (E : ClosedWalkMonomialExpansion μ Z g m) :
    ∫ ω, ((Z ω) ^ (m + 1)).trace ∂μ =
      closedWalkWickSum E := by
  have hTrace :
      (fun ω : Ω₀ => ((Z ω) ^ (m + 1)).trace) =
        fun ω : Ω₀ =>
          ∑ w : ClosedWalk ι m, ∑ t : E.Term w,
            E.coeff w t * (E.monomial w t).eval (g ω) := by
    funext ω
    rw [trace_pow_succ_eq_closedWalk_sum]
    refine Finset.sum_congr rfl ?_
    intro w _
    exact E.closedWalkProduct_eq ω w
  rw [hTrace]
  unfold closedWalkWickSum
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl ?_
    intro w _
    rw [integral_finset_sum]
    · refine Finset.sum_congr rfl ?_
      intro t _
      calc
        ∫ a : Ω₀, E.coeff w t * (E.monomial w t).eval (g a) ∂μ =
            E.coeff w t *
              ∫ a : Ω₀, (E.monomial w t).eval (g a) ∂μ := by
          exact integral_const_mul (μ := μ) (r := E.coeff w t)
            (f := fun a : Ω₀ => (E.monomial w t).eval (g a))
        _ = E.coeff w t * wickExpansion (E.monomial w t) := by
          rw [hWick.integral_entryMonomial_eq_wick]
    · intro t _
      exact (hWick.integrable_entryMonomial (E.monomial w t)).const_mul _
  · intro w _
    exact integrable_finset_sum _ fun t _ =>
      (hWick.integrable_entryMonomial (E.monomial w t)).const_mul _

/-! ## Concrete Gaussian-entry monomials for `Z = offdiag(W^Γ)` -/

/-- The holomorphic coordinate contributed by one partial-transposed Wishart
edge from `i` to `j` in sample column `α`. -/
def gammaEdgeHol
    {p q σ : Type*} (i j : BipIndex p q) (α : σ) :
    SampleCoord p q σ :=
  ((i.1, j.2), α)

/-- The conjugate coordinate contributed by one partial-transposed Wishart
edge from `i` to `j` in sample column `α`. -/
def gammaEdgeConj
    {p q σ : Type*} (i j : BipIndex p q) (α : σ) :
    SampleCoord p q σ :=
  ((j.1, i.2), α)

/-- One edge monomial `G_(i₁,j₂),α * conj(G_(j₁,i₂),α)`. -/
def gammaEdgeMonomial
    {p q σ : Type*} (i j : BipIndex p q) (α : σ) :
    EntryMonomial (SampleCoord p q σ) where
  holDegree := 1
  conjDegree := 1
  hol := fun _ => gammaEdgeHol i j α
  conj := fun _ => gammaEdgeConj i j α

@[simp] theorem gammaEdgeMonomial_eval
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    (G : SampleMatrix p q σ) (i j : BipIndex p q) (α : σ) :
    (gammaEdgeMonomial (p := p) (q := q) (σ := σ) i j α).eval
        (sampleMatrixEntries G) =
      G (i.1, j.2) α * star (G (j.1, i.2) α) := by
  simp [gammaEdgeMonomial, EntryMonomial.eval, gammaEdgeHol, gammaEdgeConj]

/-- Entrywise expansion of `Z = offdiag(W^Γ)` as a finite sum of Gaussian
degree `(1,1)` monomials. -/
theorem wishartGammaOffDiagonal_entry_monomial_expansion
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    (G : SampleMatrix p q σ) (i j : BipIndex p q) :
    wishartGammaOffDiagonal (p := p) (q := q) (σ := σ) G i j =
      ∑ α : σ,
        (if i = j then 0 else ((Fintype.card σ : ℂ)⁻¹)) *
          (gammaEdgeMonomial (p := p) (q := q) (σ := σ) i j α).eval
            (sampleMatrixEntries G) := by
  by_cases hij : i = j
  · simp [hij]
  · simp only [wishartGammaOffDiagonal_apply, hij, if_false]
    simp [wishartGamma, gamma, wishart, densityMatrix, Matrix.mul_apply,
      gammaEdgeMonomial_eval, Finset.mul_sum]

/-- Entrywise expansion of the raw partial-transposed Wishart matrix.

This is the finite algebraic core behind the paper-facing formula
`(W^Γ)_(a,b),(c,e) = ∑ r G_(a,e),r * conj(G_(c,b),r)`.  Unlike the
off-diagonal version above, no diagonal coefficient is inserted and no
`1 / |σ|` Wishart normalization is present. -/
theorem rawWishartGamma_entry_monomial_expansion
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    (G : SampleMatrix p q σ) (i j : BipIndex p q) :
    HighProbabilityBounds.rawWishartGamma
        (p := p) (q := q) (σ := σ) G i j =
      ∑ α : σ,
        (gammaEdgeMonomial (p := p) (q := q) (σ := σ) i j α).eval
          (sampleMatrixEntries G) := by
  simp [HighProbabilityBounds.rawWishartGamma, HighProbabilityBounds.rawWishart,
    gamma, densityMatrix, Matrix.mul_apply, gammaEdgeMonomial_eval]

/-- Entrywise expansion of the normalized partial-transposed Wishart matrix.

This is the same PT entry formula with the repository's normalized Wishart
convention `W = |σ|⁻¹ GGᴴ`. -/
theorem wishartGamma_entry_monomial_expansion
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    (G : SampleMatrix p q σ) (i j : BipIndex p q) :
    wishartGamma (p := p) (q := q) (σ := σ) G i j =
      ∑ α : σ,
        ((Fintype.card σ : ℂ)⁻¹) *
          (gammaEdgeMonomial (p := p) (q := q) (σ := σ) i j α).eval
            (sampleMatrixEntries G) := by
  simp [wishartGamma, gamma, wishart, densityMatrix, Matrix.mul_apply,
    gammaEdgeMonomial_eval, Finset.mul_sum]

end TraceWickExpansion
end PptFactorization
