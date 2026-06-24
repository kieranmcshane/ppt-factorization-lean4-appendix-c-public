import PptFactorization.TraceWickExpansion

/-!
# Minimal polynomial counting core for the Aubrun moment argument

This is the overkill-free counting spine:

`surviving contractions ↪ fixed-rank marked positions`
`⇒ cardinality ≤ Q(m)`
`⇒ closed-walk total count ≤ |ι|^(m+1) Q(m)`.

The richer `WickCountingBounds` file is kept as reusable scaffolding.  This
file is the canonical slim interface for the Appendix B/Aubrun pipeline.
-/

open scoped BigOperators

namespace PptFactorization
namespace TraceWickExpansion
namespace AubrunCountingCore

universe u v

/-- The polynomial supplied by an encoding with `r` marked positions. -/
def Q (r m : ℕ) : ℕ :=
  (m + 1) ^ r

/-- The canonical target for a fixed-rank defect encoding. -/
abbrev DefectConfig (m r : ℕ) :=
  Fin r → Fin (m + 1)

@[simp] theorem card_defectConfig (m r : ℕ) :
    Fintype.card (DefectConfig m r) = Q r m := by
  simp [DefectConfig, Q]

/-- One closed-walk contraction family encoded by `r` marked positions. -/
structure Contractions (m r : ℕ) where
  Contraction : Type u
  fintype : Fintype Contraction
  encode : Contraction ↪ DefectConfig m r

attribute [instance] Contractions.fintype

theorem Contractions.card_le_Q {m r : ℕ} (C : Contractions.{u} m r) :
    Fintype.card C.Contraction ≤ Q r m := by
  letI := C.fintype
  calc
    Fintype.card C.Contraction ≤ Fintype.card (DefectConfig m r) :=
      Fintype.card_le_of_embedding C.encode
    _ = Q r m := card_defectConfig m r

/-- The only closed-walk cardinality fact needed by the count. -/
@[simp] theorem card_closedWalk {ι : Type u} [Fintype ι] (m : ℕ) :
    Fintype.card (ClosedWalk ι m) = Fintype.card ι ^ (m + 1) := by
  simp [ClosedWalk, pow_succ, Nat.mul_comm]

/-- Surviving contractions attached to every closed walk, uniformly encoded
by `r` marked positions. -/
structure WalkContractions (ι : Type u) [Fintype ι] (m r : ℕ) where
  Term : ClosedWalk ι m → Type v
  fintype : ∀ w, Fintype (Term w)
  encode : ∀ w, Term w ↪ DefectConfig m r

attribute [instance] WalkContractions.fintype

namespace WalkContractions

variable {ι : Type u} [Fintype ι] {m r : ℕ}

theorem term_card_le_Q (C : WalkContractions ι m r)
    (w : ClosedWalk ι m) :
    Fintype.card (C.Term w) ≤ Q r m := by
  calc
    Fintype.card (C.Term w) ≤ Fintype.card (DefectConfig m r) :=
      Fintype.card_le_of_embedding (C.encode w)
    _ = Q r m := card_defectConfig m r

/-- The canonical polynomial counting bound: closed walks times at most
`Q(m)` surviving contractions per walk. -/
theorem total_card_le_dim_pow_mul_Q
    (C : WalkContractions ι m r) :
    Fintype.card (Σ w : ClosedWalk ι m, C.Term w) ≤
      Fintype.card ι ^ (m + 1) * Q r m := by
  rw [Fintype.card_sigma]
  calc
    (∑ w : ClosedWalk ι m, Fintype.card (C.Term w))
        ≤ ∑ _w : ClosedWalk ι m, Q r m := by
          exact Finset.sum_le_sum fun w _ => term_card_le_Q C w
    _ = Fintype.card (ClosedWalk ι m) * Q r m := by
          simp
    _ = Fintype.card ι ^ (m + 1) * Q r m := by
          rw [card_closedWalk]

/-- Paper-shaped weakening of the same count, ready to combine with the
remaining analytic factors in Aubrun's estimate. -/
theorem total_card_le_paper_shape
    (C : WalkContractions ι m r) :
    Fintype.card (Σ w : ClosedWalk ι m, C.Term w) ≤
      (Fintype.card ι + Q r m) ^ (m + 1) * Q r m := by
  calc
    Fintype.card (Σ w : ClosedWalk ι m, C.Term w)
        ≤ Fintype.card ι ^ (m + 1) * Q r m :=
          total_card_le_dim_pow_mul_Q C
    _ ≤ (Fintype.card ι + Q r m) ^ (m + 1) * Q r m := by
          exact Nat.mul_le_mul_right (Q r m)
            (Nat.pow_le_pow_left
              (Nat.le_add_right (Fintype.card ι) (Q r m)) (m + 1))

end WalkContractions

end AubrunCountingCore
end TraceWickExpansion
end PptFactorization
