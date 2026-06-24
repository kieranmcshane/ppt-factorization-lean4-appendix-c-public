import PptFactorization.AppendixBUpperBoundClosure
import PptFactorization.AristotleTargets.WordProtocolLocalSpike
import Mathlib.Tactic

/-!
# Bridge from protocol words to local-expansion words

The manuscript-style spike protocol uses letters `A`, `P`, and `C`: background,
pure spike, and cross term.  The compiled local-expansion API uses `A`, `L`,
and `Q`: background, linear perturbation, and quadratic perturbation.

This file records the checked dictionary:

* protocol `A` is local `A`;
* protocol `P` is local `Q`;
* protocol `C` is local `L`.

The point is modest but important: the abstract word protocol and the concrete
finite local-expansion machinery use the same mixed-word predicate after this
renaming.
-/

namespace AppendixB

open PptFactorization.WordProtocol

namespace WordProtocolBridge

/-- Translate a local-expansion letter into the protocol alphabet. -/
def protocolLetterOfLocal : LocalExpansionLetter → Letter
  | LocalExpansionLetter.A => Letter.A
  | LocalExpansionLetter.L => Letter.C
  | LocalExpansionLetter.Q => Letter.P

/-- Translate a local-expansion word into a protocol word, preserving order. -/
def protocolWordOfLocal : {k : ℕ} → (Fin k → LocalExpansionLetter) → Word
  | 0, _ => []
  | _ + 1, w =>
      protocolLetterOfLocal (w 0) :: protocolWordOfLocal (Fin.tail w)

@[simp] theorem protocolWordOfLocal_zero
    (w : Fin 0 → LocalExpansionLetter) :
    protocolWordOfLocal w = [] := rfl

@[simp] theorem protocolWordOfLocal_succ
    {k : ℕ} (w : Fin (k + 1) → LocalExpansionLetter) :
    protocolWordOfLocal w =
      protocolLetterOfLocal (w 0) :: protocolWordOfLocal (Fin.tail w) := rfl

theorem protocolWordOfLocal_length :
    ∀ {k : ℕ} (w : Fin k → LocalExpansionLetter),
      (protocolWordOfLocal w).length = k
  | 0, _ => rfl
  | k + 1, w => by
      simp [protocolWordOfLocal, protocolWordOfLocal_length (Fin.tail w)]

namespace ProtocolWord

open PptFactorization.WordProtocol.Word

theorem countA_le_length : ∀ w : Word, countA w ≤ w.length
  | [] => by simp
  | Letter.A :: w => by
      simpa [countA] using Nat.succ_le_succ (countA_le_length w)
  | Letter.P :: w => by
      simpa [countA] using Nat.le_trans (countA_le_length w) (Nat.le_succ _)
  | Letter.C :: w => by
      simpa [countA] using Nat.le_trans (countA_le_length w) (Nat.le_succ _)

theorem countP_le_length : ∀ w : Word, countP w ≤ w.length
  | [] => by simp
  | Letter.A :: w => by
      simpa [countP] using Nat.le_trans (countP_le_length w) (Nat.le_succ _)
  | Letter.P :: w => by
      simpa [countP] using Nat.succ_le_succ (countP_le_length w)
  | Letter.C :: w => by
      simpa [countP] using Nat.le_trans (countP_le_length w) (Nat.le_succ _)

end ProtocolWord

theorem localWordLetterCount_le :
    ∀ {k : ℕ} (letter : LocalExpansionLetter)
      (w : Fin k → LocalExpansionLetter),
      localWordLetterCount letter w ≤ k
  | 0, _, _ => by simp [localWordLetterCount]
  | k + 1, letter, w => by
      let x := w 0
      let wt : Fin k → LocalExpansionLetter := Fin.tail w
      have hcount :
          localWordLetterCount letter w =
            (if x = letter then 1 else 0) +
              localWordLetterCount letter wt := by
        simpa [x, wt, Fin.cons_self_tail] using
          localWordLetterCount_cons (k := k) letter x wt
      rw [hcount]
      by_cases hx : x = letter
      · rw [if_pos hx]
        simpa [Nat.add_comm] using
          Nat.succ_le_succ (localWordLetterCount_le letter wt)
      · simp [hx]
        exact Nat.le_trans (localWordLetterCount_le letter wt) (Nat.le_succ k)

theorem localWordIsPure_iff_letterCount_eq :
    ∀ {k : ℕ} (letter : LocalExpansionLetter)
      (w : Fin k → LocalExpansionLetter),
      localWordIsPure letter w ↔ localWordLetterCount letter w = k
  | 0, letter, w => by
      constructor
      · intro _; simp [localWordLetterCount]
      · intro _ i; exact Fin.elim0 i
  | k + 1, letter, w => by
      let x := w 0
      let wt : Fin k → LocalExpansionLetter := Fin.tail w
      have hcount :
          localWordLetterCount letter w =
            (if x = letter then 1 else 0) +
              localWordLetterCount letter wt := by
        simpa [x, wt, Fin.cons_self_tail] using
          localWordLetterCount_cons (k := k) letter x wt
      constructor
      · intro hpure
        have hx : x = letter := by
          simpa [x] using hpure 0
        have htail : localWordIsPure letter wt := by
          intro i
          simpa [wt] using hpure i.succ
        rw [hcount]
        have htail_count :
            localWordLetterCount letter wt = k :=
          (localWordIsPure_iff_letterCount_eq letter wt).mp htail
        simp [hx, htail_count, Nat.add_comm]
      · intro hcard
        have hpure_tail : localWordIsPure letter wt := by
          by_cases hx : x = letter
          · have htail_count :
                localWordLetterCount letter wt = k := by
              rw [hcount] at hcard
              simp [hx] at hcard
              omega
            exact (localWordIsPure_iff_letterCount_eq letter wt).mpr htail_count
          · rw [hcount] at hcard
            simp [hx] at hcard
            have htail_le := localWordLetterCount_le letter wt
            omega
        intro i
        cases i using Fin.cases with
        | zero =>
            by_cases hx : x = letter
            · simpa [x] using hx
            · rw [hcount] at hcard
              simp [hx] at hcard
              have htail_le := localWordLetterCount_le letter wt
              omega
        | succ i =>
            simpa [wt] using hpure_tail i

theorem countA_protocolWordOfLocal :
    ∀ {k : ℕ} (w : Fin k → LocalExpansionLetter),
      Word.countA (protocolWordOfLocal w) =
        localWordLetterCount LocalExpansionLetter.A w
  | 0, _ => by simp [protocolWordOfLocal, localWordLetterCount]
  | k + 1, w => by
      let wt : Fin k → LocalExpansionLetter := Fin.tail w
      have hcount :
          localWordLetterCount LocalExpansionLetter.A w =
            (if w 0 = LocalExpansionLetter.A then 1 else 0) +
              localWordLetterCount LocalExpansionLetter.A wt := by
        simpa [wt, Fin.cons_self_tail] using
          localWordLetterCount_cons (k := k) LocalExpansionLetter.A (w 0) wt
      rw [hcount]
      cases h : w 0 <;>
        simp [protocolWordOfLocal, protocolLetterOfLocal, Word.countA, h, wt,
          Nat.add_comm,
          countA_protocolWordOfLocal]

theorem countP_protocolWordOfLocal :
    ∀ {k : ℕ} (w : Fin k → LocalExpansionLetter),
      Word.countP (protocolWordOfLocal w) =
        localWordLetterCount LocalExpansionLetter.Q w
  | 0, _ => by simp [protocolWordOfLocal, localWordLetterCount]
  | k + 1, w => by
      let wt : Fin k → LocalExpansionLetter := Fin.tail w
      have hcount :
          localWordLetterCount LocalExpansionLetter.Q w =
            (if w 0 = LocalExpansionLetter.Q then 1 else 0) +
              localWordLetterCount LocalExpansionLetter.Q wt := by
        simpa [wt, Fin.cons_self_tail] using
          localWordLetterCount_cons (k := k) LocalExpansionLetter.Q (w 0) wt
      rw [hcount]
      cases h : w 0 <;>
        simp [protocolWordOfLocal, protocolLetterOfLocal, Word.countP, h, wt,
          Nat.add_comm,
          countP_protocolWordOfLocal]

theorem countC_protocolWordOfLocal :
    ∀ {k : ℕ} (w : Fin k → LocalExpansionLetter),
      Word.countC (protocolWordOfLocal w) =
        localWordLetterCount LocalExpansionLetter.L w
  | 0, _ => by simp [protocolWordOfLocal, localWordLetterCount]
  | k + 1, w => by
      let wt : Fin k → LocalExpansionLetter := Fin.tail w
      have hcount :
          localWordLetterCount LocalExpansionLetter.L w =
            (if w 0 = LocalExpansionLetter.L then 1 else 0) +
              localWordLetterCount LocalExpansionLetter.L wt := by
        simpa [wt, Fin.cons_self_tail] using
          localWordLetterCount_cons (k := k) LocalExpansionLetter.L (w 0) wt
      rw [hcount]
      cases h : w 0 <;>
        simp [protocolWordOfLocal, protocolLetterOfLocal, Word.countC, h, wt,
          Nat.add_comm,
          countC_protocolWordOfLocal]

theorem isPureA_protocolWordOfLocal_iff
    {k : ℕ} (w : Fin k → LocalExpansionLetter) :
    Word.isPureA (protocolWordOfLocal w) ↔
      localWordIsPure LocalExpansionLetter.A w := by
  rw [Word.isPureA, countA_protocolWordOfLocal, protocolWordOfLocal_length]
  exact (localWordIsPure_iff_letterCount_eq LocalExpansionLetter.A w).symm

theorem isPureP_protocolWordOfLocal_iff
    {k : ℕ} (w : Fin k → LocalExpansionLetter) :
    Word.isPureP (protocolWordOfLocal w) ↔
      localWordIsPure LocalExpansionLetter.Q w := by
  rw [Word.isPureP, countP_protocolWordOfLocal, protocolWordOfLocal_length]
  exact (localWordIsPure_iff_letterCount_eq LocalExpansionLetter.Q w).symm

/--
The protocol and local-expansion mixed predicates agree after the letter
renaming `P ↔ Q` and `C ↔ L`.
-/
theorem isMixed_protocolWordOfLocal_iff
    {k : ℕ} (w : Fin k → LocalExpansionLetter) :
    Word.isMixed (protocolWordOfLocal w) ↔ localWordIsMixed w := by
  simp [Word.isMixed, localWordIsMixed,
    isPureA_protocolWordOfLocal_iff, isPureP_protocolWordOfLocal_iff]

/--
The ordered concrete matrix product attached to a local-expansion word is the
protocol word product evaluated with the same dictionary: protocol `P` is the
local quadratic letter `Q`, and protocol `C` is the local linear letter `L`.
-/
theorem evalProduct_protocolWordOfLocal_eq_localWordMatrixProduct
    {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (A L Q : PptFactorization.RandomMatrixModel.BipMatrix p q) :
    ∀ {k : ℕ} (w : Fin k → LocalExpansionLetter),
      Word.evalProduct A Q L (protocolWordOfLocal w) =
        localWordMatrixProduct (p := p) (q := q) A L Q w
  | 0, _ => by
      simp [protocolWordOfLocal, Word.evalProduct, localWordMatrixProduct]
  | k + 1, w => by
      have htail : Fin.tail w = (fun i : Fin k => w i.succ) := rfl
      cases h : w 0 <;>
        simp [protocolWordOfLocal, protocolLetterOfLocal, h,
          Word.evalProduct, Letter.eval, localWordMatrixProduct,
          localLetterMatrix,
          evalProduct_protocolWordOfLocal_eq_localWordMatrixProduct A L Q
            (Fin.tail w)] <;>
        rw [htail]

/-- The protocol-product bridge at the normalized trace-term level. -/
theorem localWordScaledTraceTerm_eq_protocol_evalProduct_trace
    {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (N : ℝ) (A L Q : PptFactorization.RandomMatrixModel.BipMatrix p q)
    {k : ℕ} (w : Fin k → LocalExpansionLetter) :
    localWordScaledTraceTerm (p := p) (q := q) N A L Q w =
      N ^ (k - 1) *
        (Matrix.trace (Word.evalProduct A Q L (protocolWordOfLocal w))).re := by
  rw [evalProduct_protocolWordOfLocal_eq_localWordMatrixProduct]
  rfl

/-- Concrete trace expansion expressed through the protocol word dictionary. -/
theorem scaledTracePower_eq_sum_protocolWordOfLocalScaledTraceTerm
    {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (N : ℝ) (k : ℕ) (A L Q : PptFactorization.RandomMatrixModel.BipMatrix p q) :
    scaledTracePower (p := p) (q := q) N k (A + L + Q) =
      ∑ w : Fin k → LocalExpansionLetter,
        N ^ (k - 1) *
          (Matrix.trace (Word.evalProduct A Q L (protocolWordOfLocal w))).re := by
  rw [scaledTracePower_eq_sum_localWordScaledTraceTerm]
  refine Finset.sum_congr rfl ?_
  intro w _
  exact localWordScaledTraceTerm_eq_protocol_evalProduct_trace N A L Q w

/-- The concrete mixed remainder is the filtered protocol trace-word sum.

After the dictionary `A ↦ A`, `P ↦ Q`, and `C ↦ L`, the abstract protocol
word products are exactly the concrete trace words appearing in the local
expansion remainder. -/
theorem localExpansionMixedRemainder_eq_sum_protocolMixedWordScaledTraceTerm
    {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (N : ℝ) (k : ℕ) (A L Q : PptFactorization.RandomMatrixModel.BipMatrix p q)
    (hk : 1 ≤ k) :
    localExpansionMixedRemainder (p := p) (q := q) N k A L Q =
      localMixedWordFilteredSum (k := k)
        (fun w : Fin k → LocalExpansionLetter =>
          N ^ (k - 1) *
            (Matrix.trace (Word.evalProduct A Q L (protocolWordOfLocal w))).re) := by
  rw [localExpansionMixedRemainder_eq_sum_mixedWordScaledTraceTerm
    (p := p) (q := q) N k A L Q hk]
  unfold localExpansionMixedWordSum localMixedWordFilteredSum
  refine Finset.sum_congr rfl ?_
  intro w _
  by_cases hw : localWordIsMixed w
  · simp [hw, localWordScaledTraceTerm_eq_protocol_evalProduct_trace]
  · simp [hw]

/--
The three local mixed-word branches assemble into the scalar envelope term used
by the upper mixed-remainder pipeline.
-/
theorem localWordScaledTraceTerm_le_envelope_of_branchNormBounds
    {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q]
    {N M a speed : ℝ} {k : ℕ}
    {A L Q : PptFactorization.RandomMatrixModel.BipMatrix p q}
    {w : Fin k → LocalExpansionLetter}
    (hNpos : 0 < N) (hM : 0 ≤ M) (ha : 0 ≤ a) (hk3 : 3 ≤ k)
    (hA_op : PptFactorization.RandomMatrixModel.opNorm A ≤ M / N)
    (hL1_frob :
      PptFactorization.RandomMatrixModel.frobeniusNorm L ≤
        upperMixedWordL1bound (p := p) (q := q) N M speed a /
          Real.sqrt
            (Fintype.card (PptFactorization.RandomMatrixModel.BipIndex p q)))
    (hL2_frob :
      PptFactorization.RandomMatrixModel.frobeniusNorm L ≤
        upperMixedWordL2bound (p := p) (q := q) N M speed a)
    (hQ_frob :
      PptFactorization.RandomMatrixModel.frobeniusNorm Q ≤
        upperMixedWordQ1bound (p := p) (q := q) N speed a /
          Real.sqrt
            (Fintype.card (PptFactorization.RandomMatrixModel.BipIndex p q)))
    (hmix : localWordIsMixed w) :
    |localWordScaledTraceTerm (p := p) (q := q) N A L Q w| ≤
      localExpansionMixedWordEnvelopeTerm
        N (upperMixedWordAbound M N)
        (upperMixedWordL2bound (p := p) (q := q) N M speed a)
        (upperMixedWordL1bound (p := p) (q := q) N M speed a)
        (upperMixedWordQ2bound (p := p) (q := q) N speed a)
        (upperMixedWordQ1bound (p := p) (q := q) N speed a) k w := by
  by_cases hLinear : localWordHasOneLinearDefect w
  · simpa [localExpansionMixedWordEnvelopeTerm, hLinear] using
      (localWordScaledTraceTerm_oneLinear_le_envelope
        (p := p) (q := q) (N := N) (M := M) (a := a) (speed := speed)
        (k := k) (A := A) (L := L) (Q := Q) (w := w)
        hNpos hM hk3 hA_op hL1_frob hLinear)
  · by_cases hQuadratic : localWordHasOneQuadraticDefect w
    · simpa [localExpansionMixedWordEnvelopeTerm, hLinear, hQuadratic] using
        (localWordScaledTraceTerm_oneQuadratic_le_envelope
          (p := p) (q := q) (N := N) (M := M) (a := a) (speed := speed)
          (k := k) (A := A) (L := L) (Q := Q) (w := w)
          hNpos hM hk3 hA_op hQ_frob hQuadratic)
    · simpa [localExpansionMixedWordEnvelopeTerm, hLinear, hQuadratic] using
        (localWordScaledTraceTerm_multiDefect_le_envelope
          (p := p) (q := q) (N := N) (M := M) (a := a) (speed := speed)
          (k := k) (A := A) (L := L) (Q := Q) (w := w)
          hNpos hM ha hA_op hL2_frob hQ_frob hmix hLinear hQuadratic)

end WordProtocolBridge
end AppendixB
