import PptFactorization.TraceWickProductExpansion
import PptFactorization.WickCountingCore
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Aubrun moment spine

This file connects the concrete Wick expansion for the off-diagonal partial
transpose

`Z = W^Γ - diag(W^Γ)`

to the finite family of surviving Wick contractions.  It proves the exact
no-input rewrite of the trace moment as a finite sum over those surviving
contractions, and records the polynomial counting closure available once the
Aubrun-specific encoding of surviving contractions is supplied.

The final Aubrun Proposition 7.1 polynomial encoding is not asserted here: that
is the remaining combinatorial theorem.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.Frobenius

noncomputable section

namespace PptFactorization
namespace TraceWickExpansion

open RandomMatrixModel GaussianModel ComplexGaussianWick

variable {p q σ : Type*}
variable [Fintype p] [Fintype q] [Fintype σ]
variable [DecidableEq p] [DecidableEq q] [DecidableEq σ]

/-! ## Surviving Wick contractions for one closed-walk monomial -/

/-- Surviving Wick contractions for one expanded off-diagonal Gamma path
monomial.  A permutation survives precisely when every holomorphic coordinate
is matched with the anti-holomorphic coordinate selected by the permutation. -/
abbrev SurvivingPathPairing
    (i j : BipIndex p q) {m : ℕ} (x : Fin m → BipIndex p q)
    (α : Fin (m + 1) → σ) :=
  {π : Equiv.Perm (Fin (m + 1)) //
    ∀ k : Fin (m + 1),
      gammaEdgeHol (pathSource i x k) (pathTarget j x k) (α k) =
        gammaEdgeConj
          (pathSource i x (π k)) (pathTarget j x (π k)) (α (π k))}

omit [Fintype p] [Fintype q] [Fintype σ] in
/-- The Wick expansion of one path monomial is exactly the number of surviving
contractions. -/
theorem wickExpansion_pathGammaMonomial_eq_survivingPathPairing_card
    (i j : BipIndex p q) {m : ℕ} (x : Fin m → BipIndex p q)
    (α : Fin (m + 1) → σ) :
    wickExpansion
        (pathGammaMonomial (p := p) (q := q) (σ := σ) i j x α) =
      (Fintype.card
        (SurvivingPathPairing (p := p) (q := q) (σ := σ) i j x α) : ℂ) := by
  classical
  rw [wickExpansion_eq_pairingSum_of_degree_eq
    (pathGammaMonomial (p := p) (q := q) (σ := σ) i j x α) rfl]
  rw [pairingSum_eq_card_compatible]
  rfl

/-- Surviving Wick contractions attached to a closed walk and a sample-column
word. -/
abbrev SurvivingClosedWalkPairing
    {m : ℕ} (w : ClosedWalk (BipIndex p q) m)
    (α : Fin (m + 1) → σ) :=
  SurvivingPathPairing (p := p) (q := q) (σ := σ) w.1 w.1 w.2 α

/-! ## Coordinate constraints carried by a surviving contraction -/

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q]
  [DecidableEq σ] in
/-- A surviving contraction pairs equal sample-column labels. -/
theorem survivingPathPairing_sample_eq
    (i j : BipIndex p q) {m : ℕ} (x : Fin m → BipIndex p q)
    (α : Fin (m + 1) → σ)
    (π : SurvivingPathPairing (p := p) (q := q) (σ := σ) i j x α)
    (k : Fin (m + 1)) :
    α k = α (π.1 k) := by
  have h := π.2 k
  simpa [gammaEdgeHol, gammaEdgeConj] using congrArg Prod.snd h

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q]
  [DecidableEq σ] in
/-- A surviving contraction identifies the left coordinate of a holomorphic
edge with the left coordinate of the transposed anti-holomorphic target edge. -/
theorem survivingPathPairing_left_eq
    (i j : BipIndex p q) {m : ℕ} (x : Fin m → BipIndex p q)
    (α : Fin (m + 1) → σ)
    (π : SurvivingPathPairing (p := p) (q := q) (σ := σ) i j x α)
    (k : Fin (m + 1)) :
    (pathSource i x k).1 = (pathTarget j x (π.1 k)).1 := by
  have h := π.2 k
  simpa [gammaEdgeHol, gammaEdgeConj] using
    congrArg (fun z : SampleCoord p q σ => z.1.1) h

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q]
  [DecidableEq σ] in
/-- A surviving contraction identifies the right coordinate of a holomorphic
edge with the right coordinate of the transposed anti-holomorphic source edge. -/
theorem survivingPathPairing_right_eq
    (i j : BipIndex p q) {m : ℕ} (x : Fin m → BipIndex p q)
    (α : Fin (m + 1) → σ)
    (π : SurvivingPathPairing (p := p) (q := q) (σ := σ) i j x α)
    (k : Fin (m + 1)) :
    (pathTarget j x k).2 = (pathSource i x (π.1 k)).2 := by
  have h := π.2 k
  simpa [gammaEdgeHol, gammaEdgeConj] using
    congrArg (fun z : SampleCoord p q σ => z.1.2) h

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q]
  [DecidableEq σ] in
/-- Closed-walk version of `survivingPathPairing_sample_eq`. -/
theorem survivingClosedWalkPairing_sample_eq
    {m : ℕ} (w : ClosedWalk (BipIndex p q) m)
    (α : Fin (m + 1) → σ)
    (π : SurvivingClosedWalkPairing (p := p) (q := q) (σ := σ) w α)
    (k : Fin (m + 1)) :
    α k = α (π.1 k) :=
  survivingPathPairing_sample_eq (p := p) (q := q) (σ := σ) w.1 w.1 w.2 α π k

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q]
  [DecidableEq σ] in
/-- Closed-walk version of `survivingPathPairing_left_eq`. -/
theorem survivingClosedWalkPairing_left_eq
    {m : ℕ} (w : ClosedWalk (BipIndex p q) m)
    (α : Fin (m + 1) → σ)
    (π : SurvivingClosedWalkPairing (p := p) (q := q) (σ := σ) w α)
    (k : Fin (m + 1)) :
    (pathSource w.1 w.2 k).1 = (pathTarget w.1 w.2 (π.1 k)).1 :=
  survivingPathPairing_left_eq (p := p) (q := q) (σ := σ) w.1 w.1 w.2 α π k

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q]
  [DecidableEq σ] in
/-- Closed-walk version of `survivingPathPairing_right_eq`. -/
theorem survivingClosedWalkPairing_right_eq
    {m : ℕ} (w : ClosedWalk (BipIndex p q) m)
    (α : Fin (m + 1) → σ)
    (π : SurvivingClosedWalkPairing (p := p) (q := q) (σ := σ) w α)
    (k : Fin (m + 1)) :
    (pathTarget w.1 w.2 k).2 = (pathSource w.1 w.2 (π.1 k)).2 :=
  survivingPathPairing_right_eq (p := p) (q := q) (σ := σ) w.1 w.1 w.2 α π k

/-! ## Nonzero off-diagonal coefficient support -/

/-- A path is off-diagonal when every edge is off the diagonal in the
`BipIndex p q` matrix. -/
def OffDiagonalPath (i j : BipIndex p q) {m : ℕ} (x : Fin m → BipIndex p q) :
    Prop :=
  ∀ e : Fin (m + 1), pathSource i x e ≠ pathTarget j x e

/-- Closed-walk specialization of `OffDiagonalPath`. -/
def OffDiagonalClosedWalk {m : ℕ} (w : ClosedWalk (BipIndex p q) m) : Prop :=
  OffDiagonalPath (p := p) (q := q) w.1 w.1 w.2

omit [Fintype p] [Fintype q] [DecidableEq σ] in
/-- If a path has a diagonal edge, then its off-diagonal expansion coefficient
is zero. -/
theorem pathGammaCoeff_eq_zero_of_not_offDiagonalPath
    (i j : BipIndex p q) {m : ℕ} (x : Fin m → BipIndex p q)
    (α : Fin (m + 1) → σ)
    (h : ¬ OffDiagonalPath (p := p) (q := q) i j x) :
    pathGammaCoeff (p := p) (q := q) (σ := σ) i j x α = 0 := by
  classical
  rw [OffDiagonalPath, not_forall] at h
  obtain ⟨e, he⟩ := h
  rw [not_ne_iff] at he
  have hterm :
      gammaEdgeCoeff (σ := σ) (pathSource i x e) (pathTarget j x e) = 0 := by
    simp [gammaEdgeCoeff, he]
  unfold pathGammaCoeff
  simpa using
    Finset.prod_eq_zero (s := (Finset.univ : Finset (Fin (m + 1))))
      (f := fun e =>
        gammaEdgeCoeff (σ := σ) (pathSource i x e) (pathTarget j x e))
      (by simp) hterm

omit [Fintype p] [Fintype q] [DecidableEq σ] in
/-- On an off-diagonal path, the coefficient is the pure normalization
`|σ|⁻¹` on each edge. -/
theorem pathGammaCoeff_of_offDiagonalPath
    (i j : BipIndex p q) {m : ℕ} (x : Fin m → BipIndex p q)
    (α : Fin (m + 1) → σ)
    (h : OffDiagonalPath (p := p) (q := q) i j x) :
    pathGammaCoeff (p := p) (q := q) (σ := σ) i j x α =
      ((Fintype.card σ : ℂ)⁻¹) ^ (m + 1) := by
  classical
  unfold pathGammaCoeff
  calc
    (∏ e : Fin (m + 1),
        gammaEdgeCoeff (σ := σ) (pathSource i x e) (pathTarget j x e))
        = ∏ _e : Fin (m + 1), ((Fintype.card σ : ℂ)⁻¹) := by
          refine Finset.prod_congr rfl ?_
          intro e _
          simp [gammaEdgeCoeff, h e]
    _ = ((Fintype.card σ : ℂ)⁻¹) ^ (m + 1) := by
          simp

omit [Fintype p] [Fintype q] [DecidableEq σ] in
/-- Closed-walk form of the zero-support statement. -/
theorem pathGammaCoeff_closedWalk_eq_zero_of_not_offDiagonal
    {m : ℕ} (w : ClosedWalk (BipIndex p q) m)
    (α : Fin (m + 1) → σ)
    (h : ¬ OffDiagonalClosedWalk (p := p) (q := q) w) :
    pathGammaCoeff (p := p) (q := q) (σ := σ) w.1 w.1 w.2 α = 0 :=
  pathGammaCoeff_eq_zero_of_not_offDiagonalPath
    (p := p) (q := q) (σ := σ) w.1 w.1 w.2 α h

omit [Fintype p] [Fintype q] [DecidableEq σ] in
/-- Closed-walk form of the off-diagonal coefficient formula. -/
theorem pathGammaCoeff_closedWalk_of_offDiagonal
    {m : ℕ} (w : ClosedWalk (BipIndex p q) m)
    (α : Fin (m + 1) → σ)
    (h : OffDiagonalClosedWalk (p := p) (q := q) w) :
    pathGammaCoeff (p := p) (q := q) (σ := σ) w.1 w.1 w.2 α =
      ((Fintype.card σ : ℂ)⁻¹) ^ (m + 1) :=
  pathGammaCoeff_of_offDiagonalPath
    (p := p) (q := q) (σ := σ) w.1 w.1 w.2 α h

/-- The concrete closed-walk Wick sum is exactly the sum over surviving Wick
contractions. -/
theorem closedWalkWickSum_wishartGammaOffDiagonal_eq_survivingPairing_sum
    (m : ℕ) :
    closedWalkWickSum
        (gaussianWishartGammaOffDiagonal_closedWalkMonomialExpansion
          (p := p) (q := q) (σ := σ) m) =
      ∑ w : ClosedWalk (BipIndex p q) m,
        ∑ α : Fin (m + 1) → σ,
          pathGammaCoeff (p := p) (q := q) (σ := σ) w.1 w.1 w.2 α *
            (Fintype.card
              (SurvivingClosedWalkPairing
                (p := p) (q := q) (σ := σ) w α) : ℂ) := by
  classical
  unfold closedWalkWickSum
  refine Finset.sum_congr rfl ?_
  intro w _
  refine Finset.sum_congr rfl ?_
  intro α _
  simp only [gaussianWishartGammaOffDiagonal_closedWalkMonomialExpansion,
    wishartGammaOffDiagonal_closedWalkMonomialExpansion]
  rw [wickExpansion_pathGammaMonomial_eq_survivingPathPairing_card
    (p := p) (q := q) (σ := σ) w.1 w.1 w.2 α]

/-- No-input trace moment rewrite: the expectation of `Tr(Z^(m+1))` is the
finite sum over closed walks, sample-column words, and surviving Wick
contractions. -/
theorem expected_trace_pow_succ_wishartGammaOffDiagonal_eq_survivingPairing_sum
    (m : ℕ) :
    ∫ ω : GaussianSampleSpace p q σ,
        ((wishartGammaOffDiagonal (p := p) (q := q) (σ := σ)
            (gaussianSampleMatrix p q σ ω)) ^ (m + 1)).trace
          ∂gaussianSampleMeasure p q σ =
      ∑ w : ClosedWalk (BipIndex p q) m,
        ∑ α : Fin (m + 1) → σ,
          pathGammaCoeff (p := p) (q := q) (σ := σ) w.1 w.1 w.2 α *
            (Fintype.card
              (SurvivingClosedWalkPairing
                (p := p) (q := q) (σ := σ) w α) : ℂ) := by
  rw [expected_trace_pow_succ_wishartGammaOffDiagonal_eq_wick_sum
    (p := p) (q := q) (σ := σ) m]
  exact closedWalkWickSum_wishartGammaOffDiagonal_eq_survivingPairing_sum
    (p := p) (q := q) (σ := σ) m

/-! ## Counting closure once Aubrun's surviving-contraction encoding is proved -/

namespace AubrunSurvivingCounting

/-- Cyclic successor on the edge/vertex positions of a closed walk of length
`m + 1`.  This is the Lean counterpart of the paper convention
`a_{k+1}=a_1`, `b_{k+1}=b_1`. -/
def cyclicSucc {m : ℕ} (e : Fin (m + 1)) : Fin (m + 1) :=
  if h : (e : ℕ) + 1 < m + 1 then ⟨(e : ℕ) + 1, h⟩ else 0

/-- The local cyclic successor is mathlib's standard rotation on `Fin`. -/
theorem cyclicSucc_eq_finRotate {m : ℕ} (e : Fin (m + 1)) :
    cyclicSucc e = finRotate (m + 1) e := by
  rw [finRotate_succ_apply]
  unfold cyclicSucc
  split
  · rename_i h
    have hne : e ≠ Fin.last m := by
      intro he
      have : (e : ℕ) = m := by simp [he]
      omega
    ext
    simp [Fin.val_add_one, hne]
  · rename_i h
    have heq : (e : ℕ) = m := by omega
    have hlast : e = Fin.last m := by exact Fin.ext heq
    ext
    simp [hlast]

/-- On a closed walk, the target of edge `e` is the source at the cyclic
successor of `e`. -/
theorem pathTarget_closed_eq_pathSource_cyclicSucc
    {ι : Type*} {m : ℕ} (w : ClosedWalk ι m) (e : Fin (m + 1)) :
    pathTarget w.1 w.2 e = pathSource w.1 w.2 (cyclicSucc e) := by
  by_cases h : (e : ℕ) < m
  · have hs : (e : ℕ) + 1 < m + 1 := by omega
    have hsucc : cyclicSucc e = (⟨(e : ℕ), h⟩ : Fin m).succ := by
      ext
      simp [cyclicSucc, hs]
    calc
      pathTarget w.1 w.2 e = w.2 ⟨(e : ℕ), h⟩ := by
        simp [pathTarget, h]
      _ = pathSource w.1 w.2 (cyclicSucc e) := by
        rw [hsucc, pathSource, Fin.cons_succ]
  · have hs : ¬ (e : ℕ) + 1 < m + 1 := by omega
    simp [cyclicSucc, pathTarget, pathSource, h, hs]

/-- Left coordinate of the vertex at position `e` in a closed walk. -/
def leftVertexLabel {m : ℕ} (w : ClosedWalk (BipIndex p q) m)
    (e : Fin (m + 1)) : p :=
  (pathSource w.1 w.2 e).1

/-- Right coordinate of the vertex at position `e` in a closed walk. -/
def rightVertexLabel {m : ℕ} (w : ClosedWalk (BipIndex p q) m)
    (e : Fin (m + 1)) : q :=
  (pathSource w.1 w.2 e).2

/-- The left-index relation generated by a Wick permutation:
`a_e = a_{π(e)+1}`. -/
def wickLeftRelGen {m : ℕ} (π : Equiv.Perm (Fin (m + 1)))
    (a b : Fin (m + 1)) : Prop :=
  ∃ e, a = e ∧ b = cyclicSucc (π e)

/-- The right-index relation generated by a Wick permutation:
`b_{e+1} = b_{π(e)}`. -/
def wickRightRelGen {m : ℕ} (π : Equiv.Perm (Fin (m + 1)))
    (a b : Fin (m + 1)) : Prop :=
  ∃ e, a = cyclicSucc e ∧ b = π e

/-- The sample-column relation generated by a Wick permutation:
`c_e = c_{π(e)}`. -/
def wickColumnRelGen {m : ℕ} (π : Equiv.Perm (Fin (m + 1)))
    (a b : Fin (m + 1)) : Prop :=
  b = π a

/-- Column Wick relation generator as a permutation edge. -/
theorem wickColumnRelGen_iff_perm_edge {m : ℕ}
    (π : Equiv.Perm (Fin (m + 1))) (a b : Fin (m + 1)) :
    wickColumnRelGen π a b ↔ b = π a := by
  rfl

/-- Left Wick relation generator as a permutation edge for
`finRotate * π`. -/
theorem wickLeftRelGen_iff_perm_edge {m : ℕ}
    (π : Equiv.Perm (Fin (m + 1))) (a b : Fin (m + 1)) :
    wickLeftRelGen π a b ↔ b = (finRotate (m + 1) * π) a := by
  constructor
  · rintro ⟨e, rfl, rfl⟩
    simp [cyclicSucc_eq_finRotate]
  · intro h
    refine ⟨a, rfl, ?_⟩
    simpa [cyclicSucc_eq_finRotate] using h

/-- Right Wick relation generator as a permutation edge for
`π * finRotate⁻¹`. -/
theorem wickRightRelGen_iff_perm_edge {m : ℕ}
    (π : Equiv.Perm (Fin (m + 1))) (a b : Fin (m + 1)) :
    wickRightRelGen π a b ↔ b = (π * (finRotate (m + 1)).symm) a := by
  constructor
  · rintro ⟨e, rfl, rfl⟩
    simp [cyclicSucc_eq_finRotate]
  · intro h
    refine ⟨(finRotate (m + 1)).symm a, ?_, ?_⟩
    · simp [cyclicSucc_eq_finRotate]
    · simpa using h

/-- Edge relation of a permutation. Its equivalence closure is the usual
cycle relation. -/
def permEdgeRel {α : Type*} (σ : Equiv.Perm α) (a b : α) : Prop :=
  b = σ a

/-- Forward powers of a permutation stay in the equivalence closure of its edge
relation. -/
lemma permEdgeRel_eqvGen_pow {α : Type*} (σ : Equiv.Perm α) (a : α) :
    ∀ n : ℕ, Relation.EqvGen (permEdgeRel σ) a ((σ ^ n) a) := by
  intro n
  induction n with
  | zero => simp [Relation.EqvGen.refl]
  | succ n ih =>
      have hstep :
          Relation.EqvGen (permEdgeRel σ) ((σ ^ n) a) ((σ ^ (n + 1)) a) := by
        apply Relation.EqvGen.rel
        unfold permEdgeRel
        simp [pow_succ']
      exact Relation.EqvGen.trans a ((σ ^ n) a) ((σ ^ (n + 1)) a) ih hstep

/-- Integer powers of a permutation stay in the equivalence closure of its edge
relation. -/
lemma permEdgeRel_eqvGen_zpow {α : Type*} (σ : Equiv.Perm α) (a : α) :
    ∀ i : ℤ, Relation.EqvGen (permEdgeRel σ) a ((σ ^ i) a) := by
  intro i
  rcases i with n | n
  · simpa using permEdgeRel_eqvGen_pow σ a n
  · have hforward :=
      permEdgeRel_eqvGen_pow σ ((σ ^ (Int.negSucc n)) a) (n + 1)
    have heq : (σ ^ (n + 1 : ℕ)) ((σ ^ (Int.negSucc n)) a) = a := by
      simp [zpow_negSucc]
    have hsymm :=
      Relation.EqvGen.symm ((σ ^ (Int.negSucc n)) a) a
        (by simpa [heq] using hforward)
    simpa using hsymm

/-- The equivalence closure of permutation edges is exactly mathlib's
`SameCycle` relation. -/
lemma permEdgeRel_eqvGen_iff_sameCycle {α : Type*}
    (σ : Equiv.Perm α) (a b : α) :
    Relation.EqvGen (permEdgeRel σ) a b ↔ σ.SameCycle a b := by
  constructor
  · intro h
    induction h with
    | rel x y hrel =>
        exact ⟨1, by simpa [permEdgeRel] using hrel.symm⟩
    | refl x => exact Equiv.Perm.SameCycle.refl σ x
    | symm x y hxy ih => exact ih.symm
    | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz
  · rintro ⟨i, rfl⟩
    exact permEdgeRel_eqvGen_zpow σ a i

/-- Cardinality of the quotient by an arbitrary finite setoid. -/
noncomputable def setoidQuotientCard {α : Type*} [Fintype α] (S : Setoid α) : ℕ := by
  classical
  exact Fintype.card (Quotient S)

/-- Number of cycle classes of a permutation, including fixed points. -/
noncomputable def permCycleClassCount {α : Type*} [Fintype α]
    (σ : Equiv.Perm α) : ℕ :=
  setoidQuotientCard (Equiv.Perm.SameCycle.setoid σ)

/-- Bipartite incidence graph of the two quotient partitions attached to
setoids `S` and `T`.  Its edges are represented by elements of the original
finite type. -/
noncomputable def setoidIncidenceGraph {α : Type*} [Fintype α]
    (S T : Setoid α) : SimpleGraph (Quotient S ⊕ Quotient T) where
  Adj u v := ∃ a : α,
    (u = Sum.inl (Quotient.mk'' a) ∧ v = Sum.inr (Quotient.mk'' a)) ∨
    (u = Sum.inr (Quotient.mk'' a) ∧ v = Sum.inl (Quotient.mk'' a))
  symm := by
    rintro u v ⟨a, h | h⟩
    · exact ⟨a, Or.inr ⟨h.2, h.1⟩⟩
    · exact ⟨a, Or.inl ⟨h.2, h.1⟩⟩
  loopless := ⟨by
    intro u
    rintro ⟨a, h | h⟩ <;> cases u <;> simp at h⟩

/-- The incidence graph has no more edges than original points. -/
lemma setoidIncidenceGraph_edgeSet_card_le {α : Type*} [Fintype α]
    (S T : Setoid α) :
    Nat.card (setoidIncidenceGraph S T).edgeSet ≤ Fintype.card α := by
  classical
  let edgeOf : α → (setoidIncidenceGraph S T).edgeSet := fun a =>
    ⟨s(Sum.inl (Quotient.mk'' a), Sum.inr (Quotient.mk'' a)), by
      change (setoidIncidenceGraph S T).Adj
        (Sum.inl (Quotient.mk'' a)) (Sum.inr (Quotient.mk'' a))
      exact ⟨a, Or.inl ⟨rfl, rfl⟩⟩⟩
  have hsurj : Function.Surjective edgeOf := by
    intro e
    rcases e with ⟨e, he⟩
    induction e using Sym2.ind with
    | h u v =>
        change (setoidIncidenceGraph S T).Adj u v at he
        rcases he with ⟨a, h | h⟩
        · rcases h with ⟨rfl, rfl⟩
          refine ⟨a, Subtype.ext ?_⟩
          rfl
        · rcases h with ⟨rfl, rfl⟩
          refine ⟨a, Subtype.ext ?_⟩
          exact Sym2.eq_swap
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_le_of_surjective edgeOf hsurj

lemma setoidIncidenceGraph_left_adj_right {α : Type*} [Fintype α]
    (S T : Setoid α) (a : α) :
    (setoidIncidenceGraph S T).Adj
      (Sum.inl (Quotient.mk'' a)) (Sum.inr (Quotient.mk'' a)) := by
  exact ⟨a, Or.inl ⟨rfl, rfl⟩⟩

lemma setoidIncidenceGraph_left_reachable_of_eqvGen {α : Type*} [Fintype α]
    (S T : Setoid α) {a b : α}
    (h : Relation.EqvGen (fun x y => S x y ∨ T x y) a b) :
    (setoidIncidenceGraph S T).Reachable
      (Sum.inl (Quotient.mk'' a)) (Sum.inl (Quotient.mk'' b)) := by
  induction h with
  | rel x y hxy =>
      rcases hxy with hS | hT
      · have hq : Quotient.mk'' x = (Quotient.mk'' y : Quotient S) :=
          Quotient.sound hS
        rw [hq]
      · have hxyq : Quotient.mk'' x = (Quotient.mk'' y : Quotient T) :=
          Quotient.sound hT
        have h1 : (setoidIncidenceGraph S T).Reachable
            (Sum.inl (Quotient.mk'' x)) (Sum.inr (Quotient.mk'' x)) :=
          SimpleGraph.Adj.reachable (setoidIncidenceGraph_left_adj_right S T x)
        have h2 : (setoidIncidenceGraph S T).Reachable
            (Sum.inr (Quotient.mk'' x)) (Sum.inl (Quotient.mk'' y)) := by
          rw [hxyq]
          exact
            (SimpleGraph.Adj.reachable
              (setoidIncidenceGraph_left_adj_right S T y)).symm
        exact h1.trans h2
  | refl x => exact SimpleGraph.Reachable.refl _
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ihxy ihyz => exact ihxy.trans ihyz

lemma setoidIncidenceGraph_right_reachable_left {α : Type*} [Fintype α]
    (S T : Setoid α) (a : α) :
    (setoidIncidenceGraph S T).Reachable
      (Sum.inr (Quotient.mk'' a)) (Sum.inl (Quotient.mk'' a)) := by
  exact (SimpleGraph.Adj.reachable (setoidIncidenceGraph_left_adj_right S T a)).symm

lemma eqvGen_of_sup_rel {α : Type*} (S T : Setoid α) {a b : α}
    (h : (S ⊔ T) a b) :
    Relation.EqvGen (fun x y => S x y ∨ T x y) a b := by
  rw [Setoid.sup_eq_eqvGen] at h
  exact h

/-- If two finite partitions jointly connect the underlying type, then the
sum of their numbers of classes is at most `|α| + 1`. -/
lemma setoidIncidenceGraph_connected_of_sup_top {α : Type*}
    [Fintype α] [Nonempty α] (S T : Setoid α) (htop : S ⊔ T = ⊤) :
    (setoidIncidenceGraph S T).Connected := by
  classical
  let base : α := Classical.choice inferInstance
  letI : Nonempty (Quotient S ⊕ Quotient T) := ⟨Sum.inl (Quotient.mk'' base)⟩
  refine SimpleGraph.Connected.mk ?_
  intro u v
  cases u with
  | inl qu =>
      refine Quotient.inductionOn qu ?_
      intro a
      cases v with
      | inl qv =>
          refine Quotient.inductionOn qv ?_
          intro b
          have hsup : (S ⊔ T) a b := by rw [htop]; trivial
          exact setoidIncidenceGraph_left_reachable_of_eqvGen S T
            (eqvGen_of_sup_rel S T hsup)
      | inr qv =>
          refine Quotient.inductionOn qv ?_
          intro b
          have hleft : (setoidIncidenceGraph S T).Reachable
              (Sum.inl (Quotient.mk'' a)) (Sum.inl (Quotient.mk'' b)) := by
            have hsup : (S ⊔ T) a b := by rw [htop]; trivial
            exact setoidIncidenceGraph_left_reachable_of_eqvGen S T
              (eqvGen_of_sup_rel S T hsup)
          exact hleft.trans
            (SimpleGraph.Adj.reachable (setoidIncidenceGraph_left_adj_right S T b))
  | inr qu =>
      refine Quotient.inductionOn qu ?_
      intro a
      have hToLeft := setoidIncidenceGraph_right_reachable_left S T a
      cases v with
      | inl qv =>
          refine Quotient.inductionOn qv ?_
          intro b
          have hleft : (setoidIncidenceGraph S T).Reachable
              (Sum.inl (Quotient.mk'' a)) (Sum.inl (Quotient.mk'' b)) := by
            have hsup : (S ⊔ T) a b := by rw [htop]; trivial
            exact setoidIncidenceGraph_left_reachable_of_eqvGen S T
              (eqvGen_of_sup_rel S T hsup)
          exact hToLeft.trans hleft
      | inr qv =>
          refine Quotient.inductionOn qv ?_
          intro b
          have hleft : (setoidIncidenceGraph S T).Reachable
              (Sum.inl (Quotient.mk'' a)) (Sum.inl (Quotient.mk'' b)) := by
            have hsup : (S ⊔ T) a b := by rw [htop]; trivial
            exact setoidIncidenceGraph_left_reachable_of_eqvGen S T
              (eqvGen_of_sup_rel S T hsup)
          exact (hToLeft.trans hleft).trans
            (SimpleGraph.Adj.reachable (setoidIncidenceGraph_left_adj_right S T b))

/-- Finite partition inequality used for the Cayley cycle-count bound. -/
lemma setoidQuotientCard_add_le_card_add_one_of_sup_top {α : Type*}
    [Fintype α] [Nonempty α] (S T : Setoid α) (htop : S ⊔ T = ⊤) :
    setoidQuotientCard S + setoidQuotientCard T ≤ Fintype.card α + 1 := by
  classical
  have hconn := setoidIncidenceGraph_connected_of_sup_top S T htop
  have hver := hconn.card_vert_le_card_edgeSet_add_one
  have hedge := setoidIncidenceGraph_edgeSet_card_le S T
  have hvertexCard : Nat.card (Quotient S ⊕ Quotient T) =
      setoidQuotientCard S + setoidQuotientCard T := by
    rw [Nat.card_eq_fintype_card, Fintype.card_sum]
    unfold setoidQuotientCard
    rfl
  omega

/-- Transport quotient classes across an equivalence that identifies two
setoids. -/
noncomputable def setoidQuotientEquivOfRel {α β : Type*}
    (S : Setoid α) (T : Setoid β) (e : α ≃ β)
    (h : ∀ a b, S a b ↔ T (e a) (e b)) :
    Quotient S ≃ Quotient T where
  toFun := Quotient.map' e (fun a b hab => (h a b).mp hab)
  invFun := Quotient.map' e.symm (fun a b hab => by
    have hab' : T (e (e.symm a)) (e (e.symm b)) := by
      simpa using hab
    exact (h (e.symm a) (e.symm b)).mpr hab')
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro a
    apply Quotient.sound
    simp
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro a
    apply Quotient.sound
    simp

/-- Equal quotient counts after transporting a finite setoid by an equivalence. -/
lemma setoidQuotientCard_eq_of_rel_equiv {α β : Type*} [Fintype α] [Fintype β]
    (S : Setoid α) (T : Setoid β) (e : α ≃ β)
    (h : ∀ a b, S a b ↔ T (e a) (e b)) :
    setoidQuotientCard S = setoidQuotientCard T := by
  classical
  unfold setoidQuotientCard
  exact Fintype.card_congr (setoidQuotientEquivOfRel S T e h)

/-- Cycle-class counts are invariant under inverse. -/
lemma permCycleClassCount_inv {α : Type*} [Fintype α]
    (σ : Equiv.Perm α) :
    permCycleClassCount σ⁻¹ = permCycleClassCount σ := by
  classical
  unfold permCycleClassCount
  exact setoidQuotientCard_eq_of_rel_equiv
    (Equiv.Perm.SameCycle.setoid σ⁻¹)
    (Equiv.Perm.SameCycle.setoid σ)
    (Equiv.refl α)
    (fun a b => by
      change σ⁻¹.SameCycle a b ↔ σ.SameCycle a b
      exact Equiv.Perm.sameCycle_inv)

/-- Cycle-class counts are invariant under conjugation. -/
lemma permCycleClassCount_conj {α : Type*} [Fintype α]
    (g σ : Equiv.Perm α) :
    permCycleClassCount (g * σ * g⁻¹) = permCycleClassCount σ := by
  classical
  unfold permCycleClassCount
  exact setoidQuotientCard_eq_of_rel_equiv
    (Equiv.Perm.SameCycle.setoid (g * σ * g⁻¹))
    (Equiv.Perm.SameCycle.setoid σ)
    g.symm
    (fun a b => by
      change (g * σ * g⁻¹).SameCycle a b ↔ σ.SameCycle (g⁻¹ a) (g⁻¹ b)
      exact Equiv.Perm.sameCycle_conj)

/-- The products `στ` and `τσ` have the same cycle-class count. -/
lemma permCycleClassCount_mul_comm {α : Type*} [Fintype α]
    (σ τ : Equiv.Perm α) :
    permCycleClassCount (σ * τ) = permCycleClassCount (τ * σ) := by
  have hconj : τ * (σ * τ) * τ⁻¹ = τ * σ := by
    ext a
    simp [Equiv.Perm.mul_apply]
  rw [← hconj]
  exact (permCycleClassCount_conj τ (σ * τ)).symm

/-- A full finite rotation puts all points in the same cycle. -/
lemma finRotate_sameCycle_all_of_two_le {n : ℕ} (h : 2 ≤ n)
    (a b : Fin n) : (finRotate n).SameCycle a b := by
  have hcyc : (finRotate n).IsCycle := isCycle_finRotate_of_le h
  have hsup : (finRotate n).support = Finset.univ := support_finRotate_of_le h
  have ha : finRotate n a ≠ a := by
    have : a ∈ (finRotate n).support := by
      rw [hsup]
      exact Finset.mem_univ a
    simpa [Equiv.Perm.mem_support] using this
  have hb : finRotate n b ≠ b := by
    have : b ∈ (finRotate n).support := by
      rw [hsup]
      exact Finset.mem_univ b
    simpa [Equiv.Perm.mem_support] using this
  exact hcyc.sameCycle ha hb

/-- The full finite rotation has exactly one cycle class, including the
one-point case. -/
lemma permCycleClassCount_finRotate_of_pos {n : ℕ} (hpos : 0 < n) :
    permCycleClassCount (finRotate n) = 1 := by
  classical
  unfold permCycleClassCount setoidQuotientCard
  rw [Fintype.card_eq_one_iff]
  let z : Fin n := ⟨0, hpos⟩
  refine ⟨Quotient.mk'' z, ?_⟩
  intro q
  refine Quotient.inductionOn q ?_
  intro a
  apply Quotient.sound
  cases n with
  | zero => omega
  | succ n =>
      by_cases hn : n = 0
      · subst hn
        have haz : a = z := by
          ext
          omega
        exact haz.sameCycle (finRotate (0 + 1))
      · have htwo : 2 ≤ n + 1 := by omega
        exact finRotate_sameCycle_all_of_two_le htwo a z

/-- The cycle setoid of a full finite rotation is the top setoid. -/
lemma finRotate_sameCycle_setoid_eq_top_of_pos {n : ℕ} (hpos : 0 < n) :
    Equiv.Perm.SameCycle.setoid (finRotate n) = ⊤ := by
  apply le_antisymm le_top
  intro a b _
  cases n with
  | zero => omega
  | succ n =>
      by_cases hn : n = 0
      · subst hn
        have hab : a = b := by
          ext
          omega
        simp [hab]
      · have htwo : 2 ≤ n + 1 := by omega
        exact finRotate_sameCycle_all_of_two_le htwo a b

/-- The inverse full rotation has top cycle setoid as well. -/
lemma finRotate_symm_sameCycle_setoid_eq_top_of_pos {n : ℕ} (hpos : 0 < n) :
    Equiv.Perm.SameCycle.setoid (finRotate n).symm = ⊤ := by
  apply le_antisymm le_top
  intro a b _
  change (finRotate n)⁻¹.SameCycle a b
  rw [Equiv.Perm.sameCycle_inv]
  have htop := finRotate_sameCycle_setoid_eq_top_of_pos hpos
  have hrel : (Equiv.Perm.SameCycle.setoid (finRotate n)) a b := by
    rw [htop]
    trivial
  exact hrel

/-- Cycle classes of a product are refined by the join of cycle classes of its
two factors. -/
lemma sameCycle_setoid_mul_le_sup {α : Type*} [Fintype α]
    (σ τ : Equiv.Perm α) :
    Equiv.Perm.SameCycle.setoid (σ * τ) ≤
      Equiv.Perm.SameCycle.setoid σ ⊔ Equiv.Perm.SameCycle.setoid τ := by
  intro a b hcycle
  let U : Setoid α := Equiv.Perm.SameCycle.setoid σ ⊔
    Equiv.Perm.SameCycle.setoid τ
  have hedge : ∀ x y, permEdgeRel (σ * τ) x y → U x y := by
    intro x y hxy
    rw [permEdgeRel] at hxy
    subst y
    have hT : U x (τ x) := by
      exact (le_sup_right : Equiv.Perm.SameCycle.setoid τ ≤ U) ⟨1, by simp⟩
    have hS : U (τ x) (σ (τ x)) := by
      exact (le_sup_left : Equiv.Perm.SameCycle.setoid σ ≤ U) ⟨1, by simp⟩
    simpa [U, Equiv.Perm.mul_apply] using U.trans hT hS
  have heqv : Relation.EqvGen (permEdgeRel (σ * τ)) a b :=
    (permEdgeRel_eqvGen_iff_sameCycle (σ * τ) a b).mpr hcycle
  have hUeqv : Relation.EqvGen U a b := Relation.EqvGen.mono hedge heqv
  change (Relation.EqvGen.setoid U.r) a b at hUeqv
  rwa [Setoid.eqvGen_of_setoid U] at hUeqv

lemma sameCycle_setoid_sup_top_of_mul_cycleSetoidTop {α : Type*} [Fintype α]
    (σ τ γ : Equiv.Perm α) (hγtop : Equiv.Perm.SameCycle.setoid γ = ⊤)
    (hmul : σ * τ = γ) :
    Equiv.Perm.SameCycle.setoid σ ⊔ Equiv.Perm.SameCycle.setoid τ = ⊤ := by
  apply le_antisymm le_top
  rw [← hγtop, ← hmul]
  exact sameCycle_setoid_mul_le_sup σ τ

lemma sameCycle_setoid_sup_top_of_mul_fullCycle {n : ℕ}
    (σ τ : Equiv.Perm (Fin n)) (hpos : 0 < n) (hmul : σ * τ = finRotate n) :
    Equiv.Perm.SameCycle.setoid σ ⊔ Equiv.Perm.SameCycle.setoid τ = ⊤ :=
  sameCycle_setoid_sup_top_of_mul_cycleSetoidTop σ τ (finRotate n)
    (finRotate_sameCycle_setoid_eq_top_of_pos hpos) hmul

/-- If a product is a one-cycle permutation, then the two factor cycle counts
satisfy the Cayley triangle inequality. -/
lemma cycleCount_add_le_of_mul_cycleSetoidTop {α : Type*}
    [Fintype α] [Nonempty α] (σ τ γ : Equiv.Perm α)
    (hγtop : Equiv.Perm.SameCycle.setoid γ = ⊤) (hmul : σ * τ = γ) :
    permCycleClassCount σ + permCycleClassCount τ ≤ Fintype.card α + 1 := by
  simpa [permCycleClassCount] using
    setoidQuotientCard_add_le_card_add_one_of_sup_top
      (Equiv.Perm.SameCycle.setoid σ)
      (Equiv.Perm.SameCycle.setoid τ)
      (sameCycle_setoid_sup_top_of_mul_cycleSetoidTop σ τ γ hγtop hmul)

/-- Cayley cycle-count inequality for a product equal to the long rotation. -/
lemma cycleCount_add_le_of_mul_fullCycle {n : ℕ}
    (σ τ : Equiv.Perm (Fin n)) (hpos : 0 < n) (hmul : σ * τ = finRotate n) :
    permCycleClassCount σ + permCycleClassCount τ ≤ n + 1 := by
  letI : Nonempty (Fin n) := ⟨⟨0, hpos⟩⟩
  simpa using cycleCount_add_le_of_mul_cycleSetoidTop σ τ (finRotate n)
    (finRotate_sameCycle_setoid_eq_top_of_pos hpos) hmul

/-- Cayley cycle-count inequality for a product equal to the inverse long
rotation. -/
lemma cycleCount_add_le_of_mul_fullCycleInv {n : ℕ}
    (σ τ : Equiv.Perm (Fin n)) (hpos : 0 < n)
    (hmul : σ * τ = (finRotate n).symm) :
    permCycleClassCount σ + permCycleClassCount τ ≤ n + 1 := by
  letI : Nonempty (Fin n) := ⟨⟨0, hpos⟩⟩
  simpa using cycleCount_add_le_of_mul_cycleSetoidTop σ τ (finRotate n).symm
    (finRotate_symm_sameCycle_setoid_eq_top_of_pos hpos) hmul

/-- The usual Cayley triangle inequality
`cycles(π)+cycles(π⁻¹γ)≤n+1`. -/
lemma cyclePair_inverseLongCycleBound {m : ℕ}
    (π : Equiv.Perm (Fin (m + 1))) :
    permCycleClassCount π +
      permCycleClassCount (π⁻¹ * finRotate (m + 1)) ≤ (m + 1) + 1 := by
  have hmul : π * (π⁻¹ * finRotate (m + 1)) = finRotate (m + 1) := by
    ext a
    simp
  exact cycleCount_add_le_of_mul_fullCycle π (π⁻¹ * finRotate (m + 1))
    (Nat.succ_pos m) hmul

/-- The inverse-long-cycle Cayley triangle inequality
`cycles(π)+cycles(π⁻¹γ⁻¹)≤n+1`. -/
lemma cyclePair_inverseLongCycleInvBound {m : ℕ}
    (π : Equiv.Perm (Fin (m + 1))) :
    permCycleClassCount π +
      permCycleClassCount (π⁻¹ * (finRotate (m + 1)).symm) ≤ (m + 1) + 1 := by
  have hmul :
      π * (π⁻¹ * (finRotate (m + 1)).symm) = (finRotate (m + 1)).symm := by
    ext a
    simp
  exact cycleCount_add_le_of_mul_fullCycleInv π
    (π⁻¹ * (finRotate (m + 1)).symm) (Nat.succ_pos m) hmul

/-- Congruence of equivalence closures under pointwise equivalence of
relations. -/
lemma eqvGen_congr_iff {α : Type*} {r s : α → α → Prop}
    (h : ∀ a b, r a b ↔ s a b) (a b : α) :
    Relation.EqvGen r a b ↔ Relation.EqvGen s a b := by
  constructor
  · intro hab
    induction hab with
    | rel x y hxy => exact Relation.EqvGen.rel x y ((h x y).mp hxy)
    | refl x => exact Relation.EqvGen.refl x
    | symm x y hxy ih => exact Relation.EqvGen.symm x y ih
    | trans x y z hxy hyz ihxy ihyz =>
        exact Relation.EqvGen.trans x y z ihxy ihyz
  · intro hab
    induction hab with
    | rel x y hxy => exact Relation.EqvGen.rel x y ((h x y).mpr hxy)
    | refl x => exact Relation.EqvGen.refl x
    | symm x y hxy ih => exact Relation.EqvGen.symm x y ih
    | trans x y z hxy hyz ihxy ihyz =>
        exact Relation.EqvGen.trans x y z ihxy ihyz

/-- Equivalence relation on left indices induced by a Wick permutation. -/
abbrev wickLeftSetoid {m : ℕ} (π : Equiv.Perm (Fin (m + 1))) :
    Setoid (Fin (m + 1)) :=
  Relation.EqvGen.setoid (wickLeftRelGen π)

/-- Equivalence relation on right indices induced by a Wick permutation. -/
abbrev wickRightSetoid {m : ℕ} (π : Equiv.Perm (Fin (m + 1))) :
    Setoid (Fin (m + 1)) :=
  Relation.EqvGen.setoid (wickRightRelGen π)

/-- Equivalence relation on sample-column indices induced by a Wick
permutation. -/
abbrev wickColumnSetoid {m : ℕ} (π : Equiv.Perm (Fin (m + 1))) :
    Setoid (Fin (m + 1)) :=
  Relation.EqvGen.setoid (wickColumnRelGen π)

/-- Column Wick setoid as the cycle setoid of `π`. -/
theorem wickColumnSetoid_eq_sameCycle {m : ℕ}
    (π : Equiv.Perm (Fin (m + 1))) :
    wickColumnSetoid π = Equiv.Perm.SameCycle.setoid π := by
  apply Setoid.ext
  intro a b
  exact (eqvGen_congr_iff (wickColumnRelGen_iff_perm_edge π) a b).trans
    (permEdgeRel_eqvGen_iff_sameCycle π a b)

/-- Left Wick setoid as the cycle setoid of `finRotate * π`. -/
theorem wickLeftSetoid_eq_sameCycle {m : ℕ}
    (π : Equiv.Perm (Fin (m + 1))) :
    wickLeftSetoid π = Equiv.Perm.SameCycle.setoid (finRotate (m + 1) * π) := by
  apply Setoid.ext
  intro a b
  exact (eqvGen_congr_iff (wickLeftRelGen_iff_perm_edge π) a b).trans
    (permEdgeRel_eqvGen_iff_sameCycle (finRotate (m + 1) * π) a b)

/-- Right Wick setoid as the cycle setoid of `π * finRotate⁻¹`. -/
theorem wickRightSetoid_eq_sameCycle {m : ℕ}
    (π : Equiv.Perm (Fin (m + 1))) :
    wickRightSetoid π =
      Equiv.Perm.SameCycle.setoid (π * (finRotate (m + 1)).symm) := by
  apply Setoid.ext
  intro a b
  exact (eqvGen_congr_iff (wickRightRelGen_iff_perm_edge π) a b).trans
    (permEdgeRel_eqvGen_iff_sameCycle (π * (finRotate (m + 1)).symm) a b)

/-- Number of left-index equivalence classes induced by a Wick permutation. -/
noncomputable def wickLeftClassCount {m : ℕ}
    (π : Equiv.Perm (Fin (m + 1))) : ℕ := by
  classical
  exact Fintype.card (Quotient (wickLeftSetoid π))

/-- Number of right-index equivalence classes induced by a Wick permutation. -/
noncomputable def wickRightClassCount {m : ℕ}
    (π : Equiv.Perm (Fin (m + 1))) : ℕ := by
  classical
  exact Fintype.card (Quotient (wickRightSetoid π))

/-- Number of sample-column equivalence classes induced by a Wick permutation. -/
noncomputable def wickColumnClassCount {m : ℕ}
    (π : Equiv.Perm (Fin (m + 1))) : ℕ := by
  classical
  exact Fintype.card (Quotient (wickColumnSetoid π))

theorem wickLeftClassCount_pos {m : ℕ}
    (π : Equiv.Perm (Fin (m + 1))) :
    0 < wickLeftClassCount π := by
  classical
  unfold wickLeftClassCount
  exact Fintype.card_pos_iff.mpr ⟨Quotient.mk'' (0 : Fin (m + 1))⟩

theorem wickRightClassCount_pos {m : ℕ}
    (π : Equiv.Perm (Fin (m + 1))) :
    0 < wickRightClassCount π := by
  classical
  unfold wickRightClassCount
  exact Fintype.card_pos_iff.mpr ⟨Quotient.mk'' (0 : Fin (m + 1))⟩

theorem wickColumnClassCount_pos {m : ℕ}
    (π : Equiv.Perm (Fin (m + 1))) :
    0 < wickColumnClassCount π := by
  classical
  unfold wickColumnClassCount
  exact Fintype.card_pos_iff.mpr ⟨Quotient.mk'' (0 : Fin (m + 1))⟩

/-- Column class count as a cycle-class count. -/
theorem wickColumnClassCount_eq_cycleClassCount {m : ℕ}
    (π : Equiv.Perm (Fin (m + 1))) :
    wickColumnClassCount π = permCycleClassCount π := by
  unfold wickColumnClassCount permCycleClassCount setoidQuotientCard
  rw [wickColumnSetoid_eq_sameCycle]

/-- Left class count as a cycle-class count. -/
theorem wickLeftClassCount_eq_cycleClassCount {m : ℕ}
    (π : Equiv.Perm (Fin (m + 1))) :
    wickLeftClassCount π = permCycleClassCount (finRotate (m + 1) * π) := by
  unfold wickLeftClassCount permCycleClassCount setoidQuotientCard
  rw [wickLeftSetoid_eq_sameCycle]

/-- Right class count as a cycle-class count. -/
theorem wickRightClassCount_eq_cycleClassCount {m : ℕ}
    (π : Equiv.Perm (Fin (m + 1))) :
    wickRightClassCount π =
      permCycleClassCount (π * (finRotate (m + 1)).symm) := by
  unfold wickRightClassCount permCycleClassCount setoidQuotientCard
  rw [wickRightSetoid_eq_sameCycle]

/-- Aubrun's weighted rank `#left + #right + 2 #columns` attached to a Wick
permutation.  This is the quantity that keeps the `d` and `sqrt s` factors
separate. -/
noncomputable def wickWeightedRank {m : ℕ}
    (π : Equiv.Perm (Fin (m + 1))) : ℕ :=
  wickLeftClassCount π + wickRightClassCount π + 2 * wickColumnClassCount π

/-- Every Wick permutation has at least one left class, one right class, and one
column class, so Aubrun's weighted rank is at least four. -/
theorem four_le_wickWeightedRank {m : ℕ}
    (π : Equiv.Perm (Fin (m + 1))) :
    4 ≤ wickWeightedRank π := by
  have hL := wickLeftClassCount_pos π
  have hR := wickRightClassCount_pos π
  have hC := wickColumnClassCount_pos π
  unfold wickWeightedRank
  omega

/-- Aubrun's weighted rank rewritten as a cycle-class budget for the three
explicit permutations attached to a Wick pairing. -/
theorem wickWeightedRank_eq_cycleClassBudget {m : ℕ}
    (π : Equiv.Perm (Fin (m + 1))) :
    wickWeightedRank π =
      permCycleClassCount (finRotate (m + 1) * π) +
        permCycleClassCount (π * (finRotate (m + 1)).symm) +
        2 * permCycleClassCount π := by
  simp [wickWeightedRank, wickLeftClassCount_eq_cycleClassCount,
    wickRightClassCount_eq_cycleClassCount, wickColumnClassCount_eq_cycleClassCount]

/-- The remaining rank-budget theorem follows from the two geodesic cycle-count
inequalities with the full rotation and its inverse. -/
theorem wickWeightedRank_le_of_cyclePairBounds {m : ℕ}
    (π : Equiv.Perm (Fin (m + 1)))
    (hLeft : permCycleClassCount π +
      permCycleClassCount (finRotate (m + 1) * π) ≤ (m + 1) + 1)
    (hRight : permCycleClassCount π +
      permCycleClassCount (π * (finRotate (m + 1)).symm) ≤ (m + 1) + 1) :
    wickWeightedRank π ≤ 2 * (m + 1) + 2 := by
  rw [wickWeightedRank_eq_cycleClassBudget]
  omega

/-- Convert the `π⁻¹γ⁻¹` geodesic inequality to the repository's left
cycle-pair convention. -/
lemma cyclePairLeftBound_of_inverseLongCycleInvBound {m : ℕ}
    (π : Equiv.Perm (Fin (m + 1)))
    (h : permCycleClassCount π +
      permCycleClassCount (π⁻¹ * (finRotate (m + 1)).symm) ≤ (m + 1) + 1) :
    permCycleClassCount π +
      permCycleClassCount (finRotate (m + 1) * π) ≤ (m + 1) + 1 := by
  convert h using 2
  rw [← permCycleClassCount_inv (finRotate (m + 1) * π)]
  simp [Equiv.Perm.inv_def]

/-- Convert the `π⁻¹γ` geodesic inequality to the repository's right
cycle-pair convention. -/
lemma cyclePairRightBound_of_inverseLongCycleBound {m : ℕ}
    (π : Equiv.Perm (Fin (m + 1)))
    (h : permCycleClassCount π +
      permCycleClassCount (π⁻¹ * finRotate (m + 1)) ≤ (m + 1) + 1) :
    permCycleClassCount π +
      permCycleClassCount (π * (finRotate (m + 1)).symm) ≤ (m + 1) + 1 := by
  convert h using 2
  calc
    permCycleClassCount (π * (finRotate (m + 1)).symm)
        = permCycleClassCount ((π * (finRotate (m + 1)).symm)⁻¹) := by
            rw [permCycleClassCount_inv]
    _ = permCycleClassCount (finRotate (m + 1) * π⁻¹) := by
            simp [Equiv.Perm.inv_def]
    _ = permCycleClassCount (π⁻¹ * finRotate (m + 1)) :=
            permCycleClassCount_mul_comm (finRotate (m + 1)) π⁻¹

/-- The weighted-rank budget follows directly from the two usual Cayley
geodesic inequalities written as `π⁻¹γ` and `π⁻¹γ⁻¹`. -/
theorem wickWeightedRank_le_of_inverseLongCycleBounds {m : ℕ}
    (π : Equiv.Perm (Fin (m + 1)))
    (hPlus : permCycleClassCount π +
      permCycleClassCount (π⁻¹ * finRotate (m + 1)) ≤ (m + 1) + 1)
    (hMinus : permCycleClassCount π +
      permCycleClassCount (π⁻¹ * (finRotate (m + 1)).symm) ≤ (m + 1) + 1) :
    wickWeightedRank π ≤ 2 * (m + 1) + 2 := by
  exact wickWeightedRank_le_of_cyclePairBounds π
    (cyclePairLeftBound_of_inverseLongCycleInvBound π hMinus)
    (cyclePairRightBound_of_inverseLongCycleBound π hPlus)

/-- Aubrun weighted-rank budget, closed by the two Cayley cycle-count
inequalities. -/
theorem wickWeightedRank_le_two_mul_add_two {m : ℕ}
    (π : Equiv.Perm (Fin (m + 1))) :
    wickWeightedRank π ≤ 2 * (m + 1) + 2 := by
  exact wickWeightedRank_le_of_inverseLongCycleBounds π
    (cyclePair_inverseLongCycleBound π)
    (cyclePair_inverseLongCycleInvBound π)

/-- Truncated combinatorial defect
`2k + 2 - (#left + #right + 2 #columns)` for `k = m + 1`. -/
noncomputable def wickDefect {m : ℕ}
    (π : Equiv.Perm (Fin (m + 1))) : ℕ :=
  2 * (m + 1) + 2 - wickWeightedRank π

/-- The weighted rank and the truncated defect exactly fill Aubrun's
`2k+2` budget. -/
theorem wickWeightedRank_add_wickDefect_eq_two_mul_add_two {m : ℕ}
    (π : Equiv.Perm (Fin (m + 1))) :
    wickWeightedRank π + wickDefect π = 2 * (m + 1) + 2 := by
  unfold wickDefect
  exact Nat.add_sub_of_le (wickWeightedRank_le_two_mul_add_two π)

/-- The elementary lower bound on weighted rank removes the top four values
from the naive defect range. -/
theorem wickDefect_le_two_mul {m : ℕ}
    (π : Equiv.Perm (Fin (m + 1))) :
    wickDefect π ≤ 2 * m := by
  unfold wickDefect
  have hRank := four_le_wickWeightedRank π
  omega

/-- Functions which are constant on the classes of a setoid. -/
def RelationLabeling {ι : Type*} (S : Setoid ι) (α : Type*) :=
  {f : ι → α // ∀ a b, S a b → f a = f b}

noncomputable local instance quotientSetoidFintype
    {ι : Type*} [Fintype ι] (S : Setoid ι) :
    Fintype (Quotient S) := by
  classical
  exact Fintype.ofSurjective Quotient.mk'' Quotient.mk''_surjective

noncomputable local instance relationLabelingFintype
    {ι α : Type*} [Fintype ι] [Fintype α] (S : Setoid ι) :
    Fintype (RelationLabeling S α) := by
  classical
  letI : DecidablePred
      (fun f : ι → α => ∀ a b, S a b → f a = f b) :=
    Classical.decPred _
  unfold RelationLabeling
  infer_instance

namespace RelationLabeling

variable {ι α : Type*}

/-- It is enough to check equality on the generators of an equivalence closure. -/
theorem respects_eqvGen {r : ι → ι → Prop} {f : ι → α}
    (h : ∀ a b, r a b → f a = f b) :
    ∀ a b, Relation.EqvGen.setoid r a b → f a = f b := by
  intro a b hab
  change Relation.EqvGen r a b at hab
  induction hab with
  | rel a b hrel => exact h a b hrel
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ihab ihbc => exact ihab.trans ihbc

/-- A labeling constant on equivalence classes descends to the quotient. -/
noncomputable def toQuotient (S : Setoid ι) (F : RelationLabeling S α) :
    Quotient S → α :=
  Quotient.lift F.1 (by intro a b h; exact F.2 a b h)

/-- Embedding of class-constant labelings into arbitrary quotient labelings. -/
noncomputable def embeddingToQuotient (S : Setoid ι) (α : Type*) :
    RelationLabeling S α ↪ (Quotient S → α) where
  toFun := toQuotient S
  inj' := by
    intro F G h
    apply Subtype.ext
    funext x
    have hx := congrFun h (Quotient.mk S x)
    simpa [toQuotient] using hx

theorem card_le_pow [Fintype ι] [Fintype α] (S : Setoid ι) :
    Fintype.card (RelationLabeling S α) ≤
      Fintype.card α ^ Fintype.card (Quotient S) := by
  classical
  calc
    Fintype.card (RelationLabeling S α)
        ≤ Fintype.card (Quotient S → α) :=
          Fintype.card_le_of_embedding (embeddingToQuotient S α)
    _ = Fintype.card α ^ Fintype.card (Quotient S) := by
          simp

end RelationLabeling

/-- Three independent labelings corresponding to Aubrun's left, right, and
sample-column equivalence relations for a fixed Wick permutation. -/
abbrev WickRelationLabelings (p q σ : Type*) {m : ℕ}
    (π : Equiv.Perm (Fin (m + 1))) :=
  RelationLabeling (wickLeftSetoid π) p ×
    RelationLabeling (wickRightSetoid π) q ×
      RelationLabeling (wickColumnSetoid π) σ

omit [DecidableEq p] [DecidableEq q] [DecidableEq σ] in
/-- Cardinality bound for the relation-labeling model, keeping the left,
right, and column factors separate. -/
theorem card_wickRelationLabelings_le {m : ℕ}
    (π : Equiv.Perm (Fin (m + 1))) :
    Fintype.card (WickRelationLabelings p q σ π) ≤
      Fintype.card p ^ wickLeftClassCount π *
        Fintype.card q ^ wickRightClassCount π *
          Fintype.card σ ^ wickColumnClassCount π := by
  classical
  have hL :
      Fintype.card (RelationLabeling (wickLeftSetoid π) p) ≤
        Fintype.card p ^ wickLeftClassCount π := by
    simpa [wickLeftClassCount] using
      RelationLabeling.card_le_pow (α := p) (S := wickLeftSetoid π)
  have hR :
      Fintype.card (RelationLabeling (wickRightSetoid π) q) ≤
        Fintype.card q ^ wickRightClassCount π := by
    simpa [wickRightClassCount] using
      RelationLabeling.card_le_pow (α := q) (S := wickRightSetoid π)
  have hC :
      Fintype.card (RelationLabeling (wickColumnSetoid π) σ) ≤
        Fintype.card σ ^ wickColumnClassCount π := by
    simpa [wickColumnClassCount] using
      RelationLabeling.card_le_pow (α := σ) (S := wickColumnSetoid π)
  calc
    Fintype.card (WickRelationLabelings p q σ π)
        =
          Fintype.card (RelationLabeling (wickLeftSetoid π) p) *
            Fintype.card (RelationLabeling (wickRightSetoid π) q) *
              Fintype.card (RelationLabeling (wickColumnSetoid π) σ) := by
          simp [WickRelationLabelings, mul_assoc]
    _ ≤
          Fintype.card p ^ wickLeftClassCount π *
            Fintype.card q ^ wickRightClassCount π *
              Fintype.card σ ^ wickColumnClassCount π := by
          exact Nat.mul_le_mul (Nat.mul_le_mul hL hR) hC

/-- Concrete closed-walk/sample-word fiber for one fixed Wick permutation.
This is the relation-level replacement for the older fixed-rank marked-position
certificate. -/
abbrev WickPermutationFiber (p q σ : Type*) {m : ℕ}
    (π : Equiv.Perm (Fin (m + 1))) :=
  {t : ClosedWalk (BipIndex p q) m × (Fin (m + 1) → σ) //
    ∀ e : Fin (m + 1),
      gammaEdgeHol
          (pathSource t.1.1 t.1.2 e)
          (pathTarget t.1.1 t.1.2 e)
          (t.2 e) =
        gammaEdgeConj
          (pathSource t.1.1 t.1.2 (π e))
          (pathTarget t.1.1 t.1.2 (π e))
          (t.2 (π e))}

/-- A closed walk is determined by its cyclic list of source vertices. -/
theorem closedWalk_eq_of_pathSource_eq
    {ι : Type*} {m : ℕ} {w₁ w₂ : ClosedWalk ι m}
    (h : ∀ e : Fin (m + 1),
      pathSource w₁.1 w₁.2 e = pathSource w₂.1 w₂.2 e) :
    w₁ = w₂ := by
  cases w₁ with
  | mk i x =>
    cases w₂ with
    | mk j y =>
      have hij : i = j := by
        simpa [pathSource] using h 0
      subst j
      have hxy : x = y := by
        funext e
        simpa [pathSource] using h e.succ
      subst y
      rfl

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q]
  [DecidableEq σ] in
/-- The left labels of a surviving fiber element respect the left relation
generated by its Wick permutation. -/
theorem fiber_leftLabel_respects {m : ℕ}
    {π : Equiv.Perm (Fin (m + 1))}
    (t : WickPermutationFiber p q σ π) :
    ∀ a b,
      wickLeftSetoid π a b →
        leftVertexLabel (p := p) (q := q) t.1.1 a =
          leftVertexLabel (p := p) (q := q) t.1.1 b := by
  exact RelationLabeling.respects_eqvGen
    (r := wickLeftRelGen π)
    (f := leftVertexLabel (p := p) (q := q) t.1.1)
    (by
      intro a b h
      rcases h with ⟨e0, ha, hb⟩
      subst a
      subst b
      have hmatch := congrArg (fun z : SampleCoord p q σ => z.1.1) (t.2 e0)
      calc
        leftVertexLabel (p := p) (q := q) t.1.1 e0
            = (pathTarget t.1.1.1 t.1.1.2 (π e0)).1 := by
              simpa [leftVertexLabel, gammaEdgeHol, gammaEdgeConj] using hmatch
        _ = leftVertexLabel (p := p) (q := q) t.1.1 (cyclicSucc (π e0)) := by
              rw [pathTarget_closed_eq_pathSource_cyclicSucc]
              rfl)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q]
  [DecidableEq σ] in
/-- The right labels of a surviving fiber element respect the right relation
generated by its Wick permutation. -/
theorem fiber_rightLabel_respects {m : ℕ}
    {π : Equiv.Perm (Fin (m + 1))}
    (t : WickPermutationFiber p q σ π) :
    ∀ a b,
      wickRightSetoid π a b →
        rightVertexLabel (p := p) (q := q) t.1.1 a =
          rightVertexLabel (p := p) (q := q) t.1.1 b := by
  exact RelationLabeling.respects_eqvGen
    (r := wickRightRelGen π)
    (f := rightVertexLabel (p := p) (q := q) t.1.1)
    (by
      intro a b h
      rcases h with ⟨e, rfl, rfl⟩
      have hmatch := congrArg (fun z : SampleCoord p q σ => z.1.2) (t.2 e)
      calc
        rightVertexLabel (p := p) (q := q) t.1.1 (cyclicSucc e)
            = (pathTarget t.1.1.1 t.1.1.2 e).2 := by
              rw [pathTarget_closed_eq_pathSource_cyclicSucc]
              rfl
        _ = rightVertexLabel (p := p) (q := q) t.1.1 (π e) := by
              simpa [rightVertexLabel, gammaEdgeHol, gammaEdgeConj] using hmatch)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q]
  [DecidableEq σ] in
/-- The sample-column labels of a surviving fiber element respect the column
relation generated by its Wick permutation. -/
theorem fiber_columnLabel_respects {m : ℕ}
    {π : Equiv.Perm (Fin (m + 1))}
    (t : WickPermutationFiber p q σ π) :
    ∀ a b,
      wickColumnSetoid π a b →
        t.1.2 a = t.1.2 b := by
  exact RelationLabeling.respects_eqvGen
    (r := wickColumnRelGen π)
    (f := t.1.2)
    (by
      intro a b h
      subst b
      have hmatch := congrArg Prod.snd (t.2 a)
      simpa [gammaEdgeHol, gammaEdgeConj] using hmatch)

/-- A concrete surviving Wick fiber injects into the three relation labelings
induced by the Wick permutation. -/
noncomputable def wickPermutationFiberToRelationLabelings {m : ℕ}
    (π : Equiv.Perm (Fin (m + 1))) :
    WickPermutationFiber p q σ π ↪
      WickRelationLabelings p q σ π where
  toFun := fun t =>
    (⟨leftVertexLabel (p := p) (q := q) t.1.1,
        fiber_leftLabel_respects t⟩,
      ⟨rightVertexLabel (p := p) (q := q) t.1.1,
        fiber_rightLabel_respects t⟩,
      ⟨t.1.2, fiber_columnLabel_respects t⟩)
  inj' := by
    intro t u h
    apply Subtype.ext
    have hLeft :
        leftVertexLabel (p := p) (q := q) t.1.1 =
          leftVertexLabel (p := p) (q := q) u.1.1 := by
      exact congrArg (fun z :
        WickRelationLabelings p q σ π => z.1.1) h
    have hRight :
        rightVertexLabel (p := p) (q := q) t.1.1 =
          rightVertexLabel (p := p) (q := q) u.1.1 := by
      exact congrArg (fun z :
        WickRelationLabelings p q σ π => z.2.1.1) h
    have hColumn : t.1.2 = u.1.2 := by
      exact congrArg (fun z :
        WickRelationLabelings p q σ π => z.2.2.1) h
    have hWalk : t.1.1 = u.1.1 := by
      apply closedWalk_eq_of_pathSource_eq
      intro e
      ext
      · exact congrFun hLeft e
      · exact congrFun hRight e
    exact Prod.ext hWalk hColumn

/-- Fixed-Wick-permutation counting bound with separate left, right, and
column factors. -/
theorem card_wickPermutationFiber_le_relation_powers {m : ℕ}
    (π : Equiv.Perm (Fin (m + 1))) :
    Fintype.card (WickPermutationFiber p q σ π) ≤
      Fintype.card p ^ wickLeftClassCount π *
        Fintype.card q ^ wickRightClassCount π *
          Fintype.card σ ^ wickColumnClassCount π := by
  classical
  calc
    Fintype.card (WickPermutationFiber p q σ π)
        ≤ Fintype.card
            (WickRelationLabelings p q σ π) :=
          Fintype.card_le_of_embedding
            (wickPermutationFiberToRelationLabelings
              (p := p) (q := q) (σ := σ) π)
    _ ≤
        Fintype.card p ^ wickLeftClassCount π *
          Fintype.card q ^ wickRightClassCount π *
            Fintype.card σ ^ wickColumnClassCount π :=
          card_wickRelationLabelings_le (p := p) (q := q) (σ := σ) π

/-- Real-valued version of the fixed-permutation bound, rewritten so that the
column contribution is expressed as a `sqrt s` factor. -/
theorem real_card_wickPermutationFiber_le_d_d_sqrt_powers {m : ℕ}
    (π : Equiv.Perm (Fin (m + 1))) :
    (Fintype.card
      (WickPermutationFiber p q σ π) : ℝ) ≤
      (Fintype.card p : ℝ) ^ wickLeftClassCount π *
        (Fintype.card q : ℝ) ^ wickRightClassCount π *
          Real.sqrt (Fintype.card σ : ℝ) ^ (2 * wickColumnClassCount π) := by
  classical
  have hnat :=
    card_wickPermutationFiber_le_relation_powers
      (p := p) (q := q) (σ := σ) π
  have hs : 0 ≤ (Fintype.card σ : ℝ) := by positivity
  have hsqrt :
      Real.sqrt (Fintype.card σ : ℝ) ^ (2 * wickColumnClassCount π) =
        (Fintype.card σ : ℝ) ^ wickColumnClassCount π := by
    rw [pow_mul]
    rw [Real.sq_sqrt hs]
  have hreal :
      (Fintype.card (WickPermutationFiber p q σ π) : ℝ) ≤
        (Fintype.card p : ℝ) ^ wickLeftClassCount π *
          (Fintype.card q : ℝ) ^ wickRightClassCount π *
            (Fintype.card σ : ℝ) ^ wickColumnClassCount π := by
    exact_mod_cast hnat
  simpa [hsqrt] using hreal

end AubrunSurvivingCounting

end TraceWickExpansion
end PptFactorization
