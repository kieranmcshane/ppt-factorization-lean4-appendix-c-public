import PptFactorization.TraceWickExpansion

/-!
# Automatic closed-walk monomial expansion for `Z`

This file turns the one-entry expansion of
`wishartGammaOffDiagonal` into a `ClosedWalkMonomialExpansion` for the whole
product of entries along a closed walk.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.Frobenius

noncomputable section

namespace PptFactorization
namespace TraceWickExpansion

open RandomMatrixModel GaussianModel ComplexGaussianWick

variable {ι : Type*}

/-! ## Path edge bookkeeping -/

/-- Source vertex of edge `e` in the path from `i` to `j` through `x`. -/
def pathSource (i : ι) {m : ℕ} (x : Fin m → ι) : Fin (m + 1) → ι :=
  Fin.cons i x

/-- Target vertex of edge `e` in the path from `i` to `j` through `x`. -/
def pathTarget (j : ι) {m : ℕ} (x : Fin m → ι) : Fin (m + 1) → ι :=
  fun e => if h : (e : ℕ) < m then x ⟨e, h⟩ else j

@[simp] theorem pathSource_zero (i : ι) {m : ℕ} (x : Fin m → ι) :
    pathSource i x 0 = i := by
  simp [pathSource]

@[simp] theorem pathSource_succ (i : ι) {m : ℕ} (x : Fin (m + 1) → ι)
    (e : Fin (m + 1)) :
    pathSource i x e.succ = x e := by
  simp [pathSource]

@[simp] theorem pathTarget_last (j : ι) {m : ℕ} (x : Fin m → ι) :
    pathTarget j x (Fin.last m) = j := by
  simp [pathTarget]

@[simp] theorem pathTarget_castSucc (j : ι) {m : ℕ} (x : Fin m → ι)
    (e : Fin m) :
    pathTarget j x e.castSucc = x e := by
  simp [pathTarget]

theorem pathSource_succ_eq_tail_pathSource (i : ι) {m : ℕ}
    (x : Fin (m + 1) → ι) (e : Fin (m + 1)) :
    pathSource i x e.succ = pathSource (x 0) (Fin.tail x) e := by
  cases e using Fin.cases with
  | zero => simp [pathSource]
  | succ e => simp [pathSource, Fin.tail]

theorem pathTarget_succ_eq_tail_pathTarget (j : ι) {m : ℕ}
    (x : Fin (m + 1) → ι) (e : Fin (m + 1)) :
    pathTarget j x e.succ = pathTarget j (Fin.tail x) e := by
  by_cases h : (e : ℕ) < m
  · simp [pathTarget, h, Fin.tail]
  · simp [pathTarget, h]

/-- Recursive `pathProduct` as the product over the edge source/target
bookkeeping above. -/
theorem pathProduct_eq_edge_prod (A : Matrix ι ι ℂ)
    (i j : ι) (m : ℕ) (x : Fin m → ι) :
    pathProduct A i j m x =
      ∏ e : Fin (m + 1), A (pathSource i x e) (pathTarget j x e) := by
  induction m generalizing i with
  | zero =>
      simp [pathProduct, pathSource, pathTarget]
  | succ m ih =>
      rw [pathProduct_succ, ih]
      conv_rhs => rw [Fin.prod_univ_succ]
      simp only [pathSource_zero]
      rw [show pathTarget j x (0 : Fin (m + 2)) = x 0 by simp [pathTarget]]
      congr 1
      refine Finset.prod_congr rfl ?_
      intro e _
      rw [pathSource_succ_eq_tail_pathSource, pathTarget_succ_eq_tail_pathTarget]

/-! ## Full path monomials -/

/-- Coefficient of one off-diagonal `W^Γ` edge after expanding over the sample
column. -/
def gammaEdgeCoeff {p q σ : Type*} [Fintype σ] [DecidableEq p] [DecidableEq q]
    (i j : BipIndex p q) : ℂ :=
  if i = j then 0 else ((Fintype.card σ : ℂ)⁻¹)

/-- Product of the edge coefficients along a path. -/
def pathGammaCoeff {p q σ : Type*} [Fintype σ] [DecidableEq p] [DecidableEq q]
    (i j : BipIndex p q) {m : ℕ} (x : Fin m → BipIndex p q)
    (_α : Fin (m + 1) → σ) : ℂ :=
  ∏ e : Fin (m + 1), gammaEdgeCoeff (σ := σ)
    (pathSource i x e) (pathTarget j x e)

/-- The Gaussian entry monomial obtained by choosing one sample column for
each edge in the path. -/
def pathGammaMonomial {p q σ : Type*}
    (i j : BipIndex p q) {m : ℕ} (x : Fin m → BipIndex p q)
    (α : Fin (m + 1) → σ) :
    EntryMonomial (SampleCoord p q σ) where
  holDegree := m + 1
  conjDegree := m + 1
  hol := fun e => gammaEdgeHol (pathSource i x e) (pathTarget j x e) (α e)
  conj := fun e => gammaEdgeConj (pathSource i x e) (pathTarget j x e) (α e)

@[simp] theorem pathGammaMonomial_eval
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    (G : SampleMatrix p q σ)
    (i j : BipIndex p q) {m : ℕ} (x : Fin m → BipIndex p q)
    (α : Fin (m + 1) → σ) :
    (pathGammaMonomial (p := p) (q := q) (σ := σ) i j x α).eval
        (sampleMatrixEntries G) =
      ∏ e : Fin (m + 1),
        (gammaEdgeMonomial (p := p) (q := q) (σ := σ)
          (pathSource i x e) (pathTarget j x e) (α e)).eval
          (sampleMatrixEntries G) := by
  simp [pathGammaMonomial, EntryMonomial.eval, gammaEdgeMonomial,
    gammaEdgeHol, gammaEdgeConj, Finset.prod_mul_distrib]
  rfl

theorem wishartGammaOffDiagonal_entry_monomial_expansion'
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    (G : SampleMatrix p q σ) (i j : BipIndex p q) :
    wishartGammaOffDiagonal (p := p) (q := q) (σ := σ) G i j =
      ∑ α : σ,
        gammaEdgeCoeff (σ := σ) i j *
          (gammaEdgeMonomial (p := p) (q := q) (σ := σ) i j α).eval
            (sampleMatrixEntries G) := by
  simpa [gammaEdgeCoeff] using
    wishartGammaOffDiagonal_entry_monomial_expansion
      (p := p) (q := q) (σ := σ) G i j

theorem pathProduct_wishartGammaOffDiagonal_monomial_expansion
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    (G : SampleMatrix p q σ)
    (i j : BipIndex p q) (m : ℕ) (x : Fin m → BipIndex p q) :
    pathProduct (wishartGammaOffDiagonal (p := p) (q := q) (σ := σ) G) i j m x =
      ∑ α : Fin (m + 1) → σ,
        pathGammaCoeff (p := p) (q := q) (σ := σ) i j x α *
          (pathGammaMonomial (p := p) (q := q) (σ := σ) i j x α).eval
            (sampleMatrixEntries G) := by
  rw [pathProduct_eq_edge_prod]
  simp_rw [wishartGammaOffDiagonal_entry_monomial_expansion']
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl ?_
  intro α _
  rw [pathGammaMonomial_eval]
  simp [pathGammaCoeff, Finset.prod_mul_distrib]

/-! ## Closed-walk instantiation -/

/-- The automatic monomial expansion of the full product of entries of
`Z = wishartGammaOffDiagonal` along every closed walk. -/
def wishartGammaOffDiagonal_closedWalkMonomialExpansion
    {Ω₀ p q σ : Type*} [MeasurableSpace Ω₀]
    {μ : Measure Ω₀} (G : Ω₀ → SampleMatrix p q σ)
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    (m : ℕ) :
    ClosedWalkMonomialExpansion
      (μ := μ)
      (Z := fun ω : Ω₀ =>
        wishartGammaOffDiagonal (p := p) (q := q) (σ := σ) (G ω))
      (g := fun ω : Ω₀ => sampleMatrixEntries (G ω))
      m where
  Term := fun _ => Fin (m + 1) → σ
  termFintype := fun _ => inferInstance
  coeff := fun w α =>
    pathGammaCoeff (p := p) (q := q) (σ := σ) w.1 w.1 w.2 α
  monomial := fun w α =>
    pathGammaMonomial (p := p) (q := q) (σ := σ) w.1 w.1 w.2 α
  closedWalkProduct_eq := by
    intro ω w
    exact pathProduct_wishartGammaOffDiagonal_monomial_expansion
      (p := p) (q := q) (σ := σ) (G ω) w.1 w.1 m w.2

/-- Canonical Gaussian-probability-space version of
`wishartGammaOffDiagonal_closedWalkMonomialExpansion`. -/
def gaussianWishartGammaOffDiagonal_closedWalkMonomialExpansion
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    (m : ℕ) :
    ClosedWalkMonomialExpansion
      (μ := gaussianSampleMeasure p q σ)
      (Z := fun ω : GaussianSampleSpace p q σ =>
        wishartGammaOffDiagonal (p := p) (q := q) (σ := σ)
          (gaussianSampleMatrix p q σ ω))
      (g := fun ω : GaussianSampleSpace p q σ =>
        sampleMatrixEntries (gaussianSampleMatrix p q σ ω))
      m :=
  wishartGammaOffDiagonal_closedWalkMonomialExpansion
    (μ := gaussianSampleMeasure p q σ)
    (G := gaussianSampleMatrix p q σ) m

/-- Final no-input Wick expansion of the trace power moments of the concrete
off-diagonal partial-transposed Wishart matrix. -/
theorem expected_trace_pow_succ_wishartGammaOffDiagonal_eq_wick_sum
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    (m : ℕ) :
    ∫ ω : GaussianSampleSpace p q σ,
        ((wishartGammaOffDiagonal (p := p) (q := q) (σ := σ)
            (gaussianSampleMatrix p q σ ω)) ^ (m + 1)).trace
          ∂gaussianSampleMeasure p q σ =
      closedWalkWickSum
        (gaussianWishartGammaOffDiagonal_closedWalkMonomialExpansion
          (p := p) (q := q) (σ := σ) m) := by
  exact expected_trace_pow_succ_eq_wick_sum_of_monomial_expansion
    (hWick := ComplexGaussianWick.ConcreteGaussianEntriesHaveWickMoments p q σ)
    (gaussianWishartGammaOffDiagonal_closedWalkMonomialExpansion
      (p := p) (q := q) (σ := σ) m)

/-- The concrete off-diagonal partial-transposed Wishart trace power is
integrable.  This is the integrability half of the finite closed-walk/Wick
expansion, separated out for downstream moment extraction. -/
theorem trace_pow_succ_wishartGammaOffDiagonal_integrable
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    (m : ℕ) :
    Integrable
      (fun ω : GaussianSampleSpace p q σ =>
        ((wishartGammaOffDiagonal (p := p) (q := q) (σ := σ)
            (gaussianSampleMatrix p q σ ω)) ^ (m + 1)).trace)
      (gaussianSampleMeasure p q σ) := by
  exact trace_pow_succ_integrable_of_monomial_expansion
    (hWick := ComplexGaussianWick.ConcreteGaussianEntriesHaveWickMoments p q σ)
    (gaussianWishartGammaOffDiagonal_closedWalkMonomialExpansion
      (p := p) (q := q) (σ := σ) m)

/-- Fully expanded form of the same concrete trace-power Wick sum. -/
theorem expected_trace_pow_succ_wishartGammaOffDiagonal_eq_explicit_wick_sum
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    (m : ℕ) :
    ∫ ω : GaussianSampleSpace p q σ,
        ((wishartGammaOffDiagonal (p := p) (q := q) (σ := σ)
            (gaussianSampleMatrix p q σ ω)) ^ (m + 1)).trace
          ∂gaussianSampleMeasure p q σ =
      ∑ w : ClosedWalk (BipIndex p q) m,
        ∑ α : Fin (m + 1) → σ,
          pathGammaCoeff (p := p) (q := q) (σ := σ) w.1 w.1 w.2 α *
            wickExpansion
              (pathGammaMonomial (p := p) (q := q) (σ := σ) w.1 w.1 w.2 α) := by
  rw [expected_trace_pow_succ_wishartGammaOffDiagonal_eq_wick_sum
    (p := p) (q := q) (σ := σ) m]
  rfl

/-! ## Raw full partial-transposed Wishart trace powers -/

/-- Path-product monomial expansion for the raw full partial-transposed
Wishart matrix `W^Γ = (GGᴴ)^Γ`.

This is the trace-power analogue of
`rawWishartGamma_entry_monomial_expansion`: every path edge contributes one
sample-column choice and one PT edge monomial
`G_(i₁,j₂),α * conj(G_(j₁,i₂),α)`.  No diagonal cutoff and no `1 / |σ|`
normalization coefficient is present. -/
theorem pathProduct_rawWishartGamma_monomial_expansion
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    (G : SampleMatrix p q σ)
    (i j : BipIndex p q) (m : ℕ) (x : Fin m → BipIndex p q) :
    pathProduct
        (HighProbabilityBounds.rawWishartGamma
          (p := p) (q := q) (σ := σ) G) i j m x =
      ∑ α : Fin (m + 1) → σ,
        (pathGammaMonomial (p := p) (q := q) (σ := σ) i j x α).eval
          (sampleMatrixEntries G) := by
  rw [pathProduct_eq_edge_prod]
  simp_rw [rawWishartGamma_entry_monomial_expansion]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl ?_
  intro α _
  rw [pathGammaMonomial_eval]

/-- The automatic monomial expansion of the full product of entries of the raw
matrix `Z = (GGᴴ)^Γ` along every closed walk. -/
def rawWishartGamma_closedWalkMonomialExpansion
    {Ω₀ p q σ : Type*} [MeasurableSpace Ω₀]
    {μ : Measure Ω₀} (G : Ω₀ → SampleMatrix p q σ)
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    (m : ℕ) :
    ClosedWalkMonomialExpansion
      (μ := μ)
      (Z := fun ω : Ω₀ =>
        HighProbabilityBounds.rawWishartGamma
          (p := p) (q := q) (σ := σ) (G ω))
      (g := fun ω : Ω₀ => sampleMatrixEntries (G ω))
      m where
  Term := fun _ => Fin (m + 1) → σ
  termFintype := fun _ => inferInstance
  coeff := fun _ _ => 1
  monomial := fun w α =>
    pathGammaMonomial (p := p) (q := q) (σ := σ) w.1 w.1 w.2 α
  closedWalkProduct_eq := by
    intro ω w
    simpa using
      pathProduct_rawWishartGamma_monomial_expansion
        (p := p) (q := q) (σ := σ) (G ω) w.1 w.1 m w.2

/-- Canonical Gaussian-probability-space version of
`rawWishartGamma_closedWalkMonomialExpansion`. -/
def gaussianRawWishartGamma_closedWalkMonomialExpansion
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    (m : ℕ) :
    ClosedWalkMonomialExpansion
      (μ := gaussianSampleMeasure p q σ)
      (Z := fun ω : GaussianSampleSpace p q σ =>
        HighProbabilityBounds.rawWishartGamma
          (p := p) (q := q) (σ := σ)
          (gaussianSampleMatrix p q σ ω))
      (g := fun ω : GaussianSampleSpace p q σ =>
        sampleMatrixEntries (gaussianSampleMatrix p q σ ω))
      m :=
  rawWishartGamma_closedWalkMonomialExpansion
    (μ := gaussianSampleMeasure p q σ)
    (G := gaussianSampleMatrix p q σ) m

/-- No-input finite Wick expansion for trace powers of the raw full
partial-transposed Wishart matrix.

This closes the local Gaussian Wick layer before the final permutation
cycle-count collapse: the expectation of
`Tr(((GGᴴ)^Γ)^(m+1))` is the finite Wick sum of the PT edge monomials along
closed walks. -/
theorem expected_trace_pow_succ_rawWishartGamma_eq_wick_sum
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    (m : ℕ) :
    ∫ ω : GaussianSampleSpace p q σ,
        ((HighProbabilityBounds.rawWishartGamma
            (p := p) (q := q) (σ := σ)
            (gaussianSampleMatrix p q σ ω)) ^ (m + 1)).trace
          ∂gaussianSampleMeasure p q σ =
      closedWalkWickSum
        (gaussianRawWishartGamma_closedWalkMonomialExpansion
          (p := p) (q := q) (σ := σ) m) := by
  exact expected_trace_pow_succ_eq_wick_sum_of_monomial_expansion
    (hWick := ComplexGaussianWick.ConcreteGaussianEntriesHaveWickMoments p q σ)
    (gaussianRawWishartGamma_closedWalkMonomialExpansion
      (p := p) (q := q) (σ := σ) m)

/-- Fully expanded finite Wick sum for raw full partial-transposed Wishart
trace powers. -/
theorem expected_trace_pow_succ_rawWishartGamma_eq_explicit_wick_sum
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    (m : ℕ) :
    ∫ ω : GaussianSampleSpace p q σ,
        ((HighProbabilityBounds.rawWishartGamma
            (p := p) (q := q) (σ := σ)
            (gaussianSampleMatrix p q σ ω)) ^ (m + 1)).trace
          ∂gaussianSampleMeasure p q σ =
      ∑ w : ClosedWalk (BipIndex p q) m,
        ∑ α : Fin (m + 1) → σ,
          wickExpansion
            (pathGammaMonomial (p := p) (q := q) (σ := σ)
              w.1 w.1 w.2 α) := by
  rw [expected_trace_pow_succ_rawWishartGamma_eq_wick_sum
    (p := p) (q := q) (σ := σ) m]
  simp [closedWalkWickSum, gaussianRawWishartGamma_closedWalkMonomialExpansion,
    rawWishartGamma_closedWalkMonomialExpansion]
  rfl

/-- One raw PT closed-walk Wick monomial expanded as an explicit sum over
contraction permutations.

For a contraction `π`, the three displayed constraints are exactly the sample
index constraint and the two tensor-factor constraints which later collapse to
the paper's cycle-count factors
`t^#π d^(#(γπ)+#(γ⁻¹π))`. -/
theorem wickExpansion_pathGammaMonomial_eq_perm_constraint_sum
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    (i j : BipIndex p q) {m : ℕ} (x : Fin m → BipIndex p q)
    (α : Fin (m + 1) → σ) :
    wickExpansion
        (pathGammaMonomial (p := p) (q := q) (σ := σ) i j x α) =
      ∑ π : Equiv.Perm (Fin (m + 1)),
        ∏ e : Fin (m + 1),
          if (pathSource i x e).1 = (pathTarget j x (π e)).1 ∧
              (pathTarget j x e).2 = (pathSource i x (π e)).2 ∧
              α e = α (π e)
          then (1 : ℂ) else 0 := by
  simp [wickExpansion_eq_pairingSum_of_degree_eq,
    pairingSum, pairingContribution, pathGammaMonomial,
    gammaEdgeHol, gammaEdgeConj, and_assoc]

/-- Fully expanded raw PT closed-walk Wick formula as a finite sum over
contraction permutations and their explicit constraints.

This is the last purely Wick-theoretic form before the remaining combinatorial
counting step which turns the constraint fibers into the paper-facing cycle
counts. -/
theorem expected_trace_pow_succ_rawWishartGamma_eq_perm_constraint_sum
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    (m : ℕ) :
    ∫ ω : GaussianSampleSpace p q σ,
        ((HighProbabilityBounds.rawWishartGamma
            (p := p) (q := q) (σ := σ)
            (gaussianSampleMatrix p q σ ω)) ^ (m + 1)).trace
          ∂gaussianSampleMeasure p q σ =
      ∑ w : ClosedWalk (BipIndex p q) m,
        ∑ α : Fin (m + 1) → σ,
          ∑ π : Equiv.Perm (Fin (m + 1)),
            ∏ e : Fin (m + 1),
              if (pathSource w.1 w.2 e).1 =
                    (pathTarget w.1 w.2 (π e)).1 ∧
                  (pathTarget w.1 w.2 e).2 =
                    (pathSource w.1 w.2 (π e)).2 ∧
                  α e = α (π e)
              then (1 : ℂ) else 0 := by
  rw [expected_trace_pow_succ_rawWishartGamma_eq_explicit_wick_sum
    (p := p) (q := q) (σ := σ) m]
  refine Finset.sum_congr rfl ?_
  intro w _
  refine Finset.sum_congr rfl ?_
  intro α _
  exact wickExpansion_pathGammaMonomial_eq_perm_constraint_sum
    (p := p) (q := q) (σ := σ) w.1 w.1 w.2 α

end TraceWickExpansion
end PptFactorization
