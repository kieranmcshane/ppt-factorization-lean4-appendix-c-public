import PptFactorization.NCPartition

/-!
# Heavy Catalan cardinality lemmas for `NCPart n`, `n = 5, 6, 7`

Verified by `native_decide` enumeration of `Finpartition (range n)` filtered
by `NonCrossing`.  Each lemma is slow to compile (~minutes) and memory
intensive — at `n = 7` we observed ~11 min wall time and ~1 GB peak RSS.

This file is **not imported by `PptFactorization.lean`** so downstream
development does not pay the compile cost on every rebuild.  Build it
explicitly with

    lake build PptFactorization.NCPartitionHeavyCard

when you want to re-verify.
-/

namespace NCPartition

/-- `|NC(5)| = 42 = Catalan 5`. -/
theorem card_NCPart_five : Fintype.card (NCPart 5) = 42 := by
  native_decide

/-- `|NC(6)| = 132 = Catalan 6`. -/
theorem card_NCPart_six : Fintype.card (NCPart 6) = 132 := by
  native_decide

/-- `|NC(7)| = 429 = Catalan 7`. -/
theorem card_NCPart_seven : Fintype.card (NCPart 7) = 429 := by
  native_decide

end NCPartition
