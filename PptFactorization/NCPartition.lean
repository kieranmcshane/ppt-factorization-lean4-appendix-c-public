import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

/-!
# Non-crossing partitions of `{0, …, n − 1}`

This file defines `NCPart n`, the type of non-crossing partitions of
`Finset.range n`.  A Finpartition is **non-crossing** when no two distinct
blocks interleave: there are no indices `a < b < c < d` with `a, c` in one
block and `b, d` in another.

This is the foundational layer for the moment–cumulant scaffold in
`MomentCumulant.lean`.  Subsequent files will provide:

* `NCPart n` is finite and `|NC n| = Catalan n` (bijection with `DyckWord`);
* Kreweras's formula `|NC(n, λ)| = (n! / (n − k + 1)!) / ∏ mⱼ!`;
* the moment–cumulant identity `cMC_k = Σ_{π ∈ NC k} ∏ κ_{|B|}`.

## Design

`NonCrossing` is stated in the contrapositive form: whenever four indices
`a < b < c < d` satisfy `a, c ∈ B₁` and `b, d ∈ B₂`, the two blocks coincide.
This avoids `B₁ ≠ B₂` as a hypothesis and makes the predicate decidable.

Institut Fourier, Grenoble — Kieran McShane / Cécilia Lancien
-/

namespace NCPartition

open Finset

/-- A Finpartition of `Finset.range n` is **non-crossing** if, whenever four
    natural numbers `a < b < c < d` satisfy `a, c ∈ B₁` and `b, d ∈ B₂` for
    blocks `B₁, B₂ ∈ P.parts`, we have `B₁ = B₂`.

    Quantifiers are bounded to `P.parts` and to each block so that the
    predicate is decidable. -/
def NonCrossing {n : ℕ} (P : Finpartition (range n)) : Prop :=
  ∀ B₁ ∈ P.parts, ∀ B₂ ∈ P.parts,
    ∀ a ∈ B₁, ∀ b ∈ B₂, ∀ c ∈ B₁, ∀ d ∈ B₂,
      a < b → b < c → c < d → B₁ = B₂

instance {n : ℕ} (P : Finpartition (range n)) : Decidable (NonCrossing P) :=
  Finset.decidableDforallFinset

/-- The type of non-crossing partitions of `{0, 1, …, n − 1}`. -/
def NCPart (n : ℕ) : Type := {P : Finpartition (range n) // NonCrossing P}

namespace NCPart

variable {n : ℕ}

/-- Underlying Finpartition. -/
def toFinpartition (π : NCPart n) : Finpartition (range n) := π.1

/-- Blocks of a non-crossing partition. -/
def parts (π : NCPart n) : Finset (Finset ℕ) := π.1.parts

theorem nonCrossing (π : NCPart n) : NonCrossing π.1 := π.2

/-- Extensionality: two non-crossing partitions are equal iff their
    underlying Finpartitions are equal. -/
@[ext] theorem ext {π σ : NCPart n} (h : π.1 = σ.1) : π = σ := Subtype.ext h

end NCPart

-- ═══════════════════════════════════════════════════════════════════
-- §1. Trivial non-crossing partitions
-- ═══════════════════════════════════════════════════════════════════

/-- The empty non-crossing partition of `∅ = range 0`. -/
def NCPart.empty : NCPart 0 :=
  ⟨Finpartition.empty _, by
    intro B₁ hB₁
    -- `Finpartition.empty` has no parts.
    simp [Finpartition.empty] at hB₁⟩

/-- The indiscrete non-crossing partition `{{0, …, n − 1}}` for `n ≥ 1`. -/
def NCPart.indiscrete (n : ℕ) (hn : n ≠ 0) : NCPart n :=
  ⟨Finpartition.indiscrete (fun h => by
      have h0 : (0 : ℕ) ∈ range n := mem_range.mpr (Nat.pos_of_ne_zero hn)
      rw [h] at h0
      exact absurd h0 (by simp)), by
    intro B₁ hB₁ B₂ hB₂ a _ b _ c _ d _ _ _ _
    -- `Finpartition.indiscrete` has a single block `range n`.
    have h1 : B₁ = range n := by
      simp [Finpartition.indiscrete] at hB₁; exact hB₁
    have h2 : B₂ = range n := by
      simp [Finpartition.indiscrete] at hB₂; exact hB₂
    rw [h1, h2]⟩

-- ═══════════════════════════════════════════════════════════════════
-- §2. Small-case sanity checks
-- ═══════════════════════════════════════════════════════════════════

/-- For `n = 0`, the empty partition is non-crossing. -/
example : NCPart 0 := NCPart.empty

/-- For `n = 1`, the singleton block `{0}` is non-crossing. -/
example : NCPart 1 := NCPart.indiscrete 1 (by decide)

/-- For `n = 2`, the indiscrete block `{0,1}` is non-crossing. -/
example : NCPart 2 := NCPart.indiscrete 2 (by decide)

-- ═══════════════════════════════════════════════════════════════════
-- §3. Fintype instance and small cardinalities
-- ═══════════════════════════════════════════════════════════════════

instance (n : ℕ) : Fintype (NCPart n) :=
  Subtype.fintype _

/-- A point is the minimum element of its block in a non-crossing partition. -/
def NCPart.isBlockMin {n : ℕ} (π : NCPart n) (i : Fin n) : Prop :=
  ∀ j ∈ π.1.part i.val, i.val ≤ j

/-- A point is the maximum element of its block in a non-crossing partition. -/
def NCPart.isBlockMax {n : ℕ} (π : NCPart n) (i : Fin n) : Prop :=
  ∀ j ∈ π.1.part i.val, j ≤ i.val

instance {n : ℕ} (π : NCPart n) (i : Fin n) :
    Decidable (π.isBlockMin i) := by
  unfold NCPart.isBlockMin
  infer_instance

instance {n : ℕ} (π : NCPart n) (i : Fin n) :
    Decidable (π.isBlockMax i) := by
  unfold NCPart.isBlockMax
  infer_instance

/-- The crude four-choice code attached to a non-crossing partition: at each
point record whether it is the minimum and/or maximum of its block.  The
remaining combinatorial content for a symbolic `4^n` bound is injectivity of
this code on non-crossing partitions. -/
def NCPart.minMaxCode {n : ℕ} (π : NCPart n) : Fin n → Bool × Bool :=
  fun i => (decide (π.isBlockMin i), decide (π.isBlockMax i))

/-- Prefix minimum-marker predicate: the marker is at or before `t`. -/
def NCPart.prefixMinMarker {n : ℕ} (π : NCPart n) (t : ℕ) (i : Fin n) : Prop :=
  i.val ≤ t ∧ π.isBlockMin i

/-- Prefix maximum-marker predicate: the marker is at or before `t`. -/
def NCPart.prefixMaxMarker {n : ℕ} (π : NCPart n) (t : ℕ) (i : Fin n) : Prop :=
  i.val ≤ t ∧ π.isBlockMax i

instance {n : ℕ} (π : NCPart n) (t : ℕ) (i : Fin n) :
    Decidable (π.prefixMinMarker t i) := by
  unfold NCPart.prefixMinMarker
  infer_instance

instance {n : ℕ} (π : NCPart n) (t : ℕ) (i : Fin n) :
    Decidable (π.prefixMaxMarker t i) := by
  unfold NCPart.prefixMaxMarker
  infer_instance

instance {n : ℕ} (π : NCPart n) (t : ℕ) :
    Fintype {i : Fin n // π.prefixMinMarker t i} :=
  Subtype.fintype _

instance {n : ℕ} (π : NCPart n) (t : ℕ) :
    Fintype {i : Fin n // π.prefixMaxMarker t i} :=
  Subtype.fintype _

/-- A prefix is balanced when the number of block starts seen so far equals
the number of block ends seen so far. -/
def NCPart.prefixBalanced {n : ℕ} (π : NCPart n) (t : ℕ) : Prop :=
  Fintype.card {i : Fin n // π.prefixMinMarker t i} =
    Fintype.card {i : Fin n // π.prefixMaxMarker t i}

/-- Prefix excess: number of opened blocks minus number of closed blocks seen
up to `t`.  Later lemmas show this is the code-visible stack height for the
min/max reconstruction. -/
def NCPart.prefixExcess {n : ℕ} (π : NCPart n) (t : ℕ) : ℕ :=
  Fintype.card {i : Fin n // π.prefixMinMarker t i} -
    Fintype.card {i : Fin n // π.prefixMaxMarker t i}

/-- `t` is the first prefix at which the prefix excess returns to zero. -/
def NCPart.prefixExcessFirstZero {n : ℕ} (π : NCPart n) (t : ℕ) : Prop :=
  π.prefixExcess t = 0 ∧ ∀ s : ℕ, s < t → 0 < π.prefixExcess s

/-- A point is neutral when it is neither the minimum nor the maximum marker of
its block. -/
def NCPart.isBlockNeutral {n : ℕ} (π : NCPart n) (i : Fin n) : Prop :=
  ¬ π.isBlockMin i ∧ ¬ π.isBlockMax i

/-- The first point is always the minimum marker of its block. -/
theorem NCPart.zero_isBlockMin
    {n : ℕ} (π : NCPart (n + 1)) :
    π.isBlockMin 0 := by
  intro x _hx
  exact Nat.zero_le x

/-- Every block has a minimum marker, represented as a point of `Fin n`. -/
theorem NCPart.exists_isBlockMin_mem_part
    {n : ℕ} (π : NCPart n) (i : Fin n) :
    ∃ j : Fin n, j.val ∈ π.1.part i.val ∧ π.isBlockMin j := by
  let s : Finset ℕ := π.1.part i.val
  have hiRange : i.val ∈ range n := mem_range.mpr i.2
  have hsPart : s ∈ π.1.parts := π.1.part_mem.mpr hiRange
  have hsNonempty : s.Nonempty := π.1.part_nonempty.mpr hiRange
  let a : ℕ := s.min' hsNonempty
  have haMem : a ∈ s := s.min'_mem hsNonempty
  have haRange : a ∈ range n := π.1.part_subset i.val haMem
  have hpart : π.1.part a = s := π.1.part_eq_of_mem hsPart haMem
  refine ⟨⟨a, mem_range.mp haRange⟩, haMem, ?_⟩
  intro b hb
  have hb' : b ∈ s := by
    simpa [hpart] using hb
  exact s.min'_le b hb'

/-- Every block has a maximum marker, represented as a point of `Fin n`. -/
theorem NCPart.exists_isBlockMax_mem_part
    {n : ℕ} (π : NCPart n) (i : Fin n) :
    ∃ j : Fin n, j.val ∈ π.1.part i.val ∧ π.isBlockMax j := by
  let s : Finset ℕ := π.1.part i.val
  have hiRange : i.val ∈ range n := mem_range.mpr i.2
  have hsPart : s ∈ π.1.parts := π.1.part_mem.mpr hiRange
  have hsNonempty : s.Nonempty := π.1.part_nonempty.mpr hiRange
  let a : ℕ := s.max' hsNonempty
  have haMem : a ∈ s := s.max'_mem hsNonempty
  have haRange : a ∈ range n := π.1.part_subset i.val haMem
  have hpart : π.1.part a = s := π.1.part_eq_of_mem hsPart haMem
  refine ⟨⟨a, mem_range.mp haRange⟩, haMem, ?_⟩
  intro b hb
  have hb' : b ∈ s := by
    simpa [hpart] using hb
  exact s.le_max' b hb'

/-- Equality of min/max marker codes preserves the minimum-marker predicate. -/
theorem NCPart.isBlockMin_iff_of_minMaxCode_eq
    {n : ℕ} {π σ : NCPart n}
    (hcode : π.minMaxCode = σ.minMaxCode) (i : Fin n) :
    π.isBlockMin i ↔ σ.isBlockMin i := by
  have h := congrFun hcode i
  have hfst :
      decide (π.isBlockMin i) = decide (σ.isBlockMin i) :=
    congrArg Prod.fst h
  constructor
  · intro hπ
    apply of_decide_eq_true
    rw [← hfst]
    exact decide_eq_true hπ
  · intro hσ
    apply of_decide_eq_true
    rw [hfst]
    exact decide_eq_true hσ

/-- Equality of min/max marker codes preserves the maximum-marker predicate. -/
theorem NCPart.isBlockMax_iff_of_minMaxCode_eq
    {n : ℕ} {π σ : NCPart n}
    (hcode : π.minMaxCode = σ.minMaxCode) (i : Fin n) :
    π.isBlockMax i ↔ σ.isBlockMax i := by
  have h := congrFun hcode i
  have hsnd :
      decide (π.isBlockMax i) = decide (σ.isBlockMax i) :=
    congrArg Prod.snd h
  constructor
  · intro hπ
    apply of_decide_eq_true
    rw [← hsnd]
    exact decide_eq_true hπ
  · intro hσ
    apply of_decide_eq_true
    rw [hsnd]
    exact decide_eq_true hσ

/-- Equality of min/max marker codes preserves neutral points. -/
theorem NCPart.isBlockNeutral_iff_of_minMaxCode_eq
    {n : ℕ} {π σ : NCPart n}
    (hcode : π.minMaxCode = σ.minMaxCode) (i : Fin n) :
    π.isBlockNeutral i ↔ σ.isBlockNeutral i := by
  unfold NCPart.isBlockNeutral
  rw [π.isBlockMin_iff_of_minMaxCode_eq hcode i,
    π.isBlockMax_iff_of_minMaxCode_eq hcode i]

/-- Equality of min/max marker codes preserves prefix minimum-marker
predicates. -/
theorem NCPart.prefixMinMarker_iff_of_minMaxCode_eq
    {n : ℕ} {π σ : NCPart n}
    (hcode : π.minMaxCode = σ.minMaxCode) (t : ℕ) (i : Fin n) :
    π.prefixMinMarker t i ↔ σ.prefixMinMarker t i := by
  constructor
  · intro h
    exact ⟨h.1, (π.isBlockMin_iff_of_minMaxCode_eq hcode i).mp h.2⟩
  · intro h
    exact ⟨h.1, (π.isBlockMin_iff_of_minMaxCode_eq hcode i).mpr h.2⟩

/-- Equality of min/max marker codes preserves prefix maximum-marker
predicates. -/
theorem NCPart.prefixMaxMarker_iff_of_minMaxCode_eq
    {n : ℕ} {π σ : NCPart n}
    (hcode : π.minMaxCode = σ.minMaxCode) (t : ℕ) (i : Fin n) :
    π.prefixMaxMarker t i ↔ σ.prefixMaxMarker t i := by
  constructor
  · intro h
    exact ⟨h.1, (π.isBlockMax_iff_of_minMaxCode_eq hcode i).mp h.2⟩
  · intro h
    exact ⟨h.1, (π.isBlockMax_iff_of_minMaxCode_eq hcode i).mpr h.2⟩

/-- Equal min/max codes have equal prefix minimum-marker counts. -/
theorem NCPart.prefixMinMarker_card_eq_of_minMaxCode_eq
    {n : ℕ} {π σ : NCPart n}
    (hcode : π.minMaxCode = σ.minMaxCode) (t : ℕ) :
    Fintype.card {i : Fin n // π.prefixMinMarker t i} =
      Fintype.card {i : Fin n // σ.prefixMinMarker t i} := by
  exact Fintype.card_congr
    (Equiv.subtypeEquivRight
      (fun i => π.prefixMinMarker_iff_of_minMaxCode_eq hcode t i))

/-- Equal min/max codes have equal prefix maximum-marker counts. -/
theorem NCPart.prefixMaxMarker_card_eq_of_minMaxCode_eq
    {n : ℕ} {π σ : NCPart n}
    (hcode : π.minMaxCode = σ.minMaxCode) (t : ℕ) :
    Fintype.card {i : Fin n // π.prefixMaxMarker t i} =
      Fintype.card {i : Fin n // σ.prefixMaxMarker t i} := by
  exact Fintype.card_congr
    (Equiv.subtypeEquivRight
      (fun i => π.prefixMaxMarker_iff_of_minMaxCode_eq hcode t i))

/-- Equal min/max codes preserve prefix balance. -/
theorem NCPart.prefixBalanced_iff_of_minMaxCode_eq
    {n : ℕ} {π σ : NCPart n}
    (hcode : π.minMaxCode = σ.minMaxCode) (t : ℕ) :
    π.prefixBalanced t ↔ σ.prefixBalanced t := by
  unfold NCPart.prefixBalanced
  rw [π.prefixMinMarker_card_eq_of_minMaxCode_eq hcode t,
    π.prefixMaxMarker_card_eq_of_minMaxCode_eq hcode t]

/-- Equal min/max codes have equal prefix excess. -/
theorem NCPart.prefixExcess_eq_of_minMaxCode_eq
    {n : ℕ} {π σ : NCPart n}
    (hcode : π.minMaxCode = σ.minMaxCode) (t : ℕ) :
    π.prefixExcess t = σ.prefixExcess t := by
  unfold NCPart.prefixExcess
  rw [π.prefixMinMarker_card_eq_of_minMaxCode_eq hcode t,
    π.prefixMaxMarker_card_eq_of_minMaxCode_eq hcode t]

/-- Equal min/max codes preserve the first-zero prefix-excess predicate. -/
theorem NCPart.prefixExcessFirstZero_iff_of_minMaxCode_eq
    {n : ℕ} {π σ : NCPart n}
    (hcode : π.minMaxCode = σ.minMaxCode) (t : ℕ) :
    π.prefixExcessFirstZero t ↔ σ.prefixExcessFirstZero t := by
  constructor
  · intro h
    constructor
    · rw [← π.prefixExcess_eq_of_minMaxCode_eq hcode t]
      exact h.1
    · intro s hs
      rw [← π.prefixExcess_eq_of_minMaxCode_eq hcode s]
      exact h.2 s hs
  · intro h
    constructor
    · rw [π.prefixExcess_eq_of_minMaxCode_eq hcode t]
      exact h.1
    · intro s hs
      rw [π.prefixExcess_eq_of_minMaxCode_eq hcode s]
      exact h.2 s hs

/-- The first-zero prefix-excess position is unique. -/
theorem NCPart.prefixExcessFirstZero_unique
    {n : ℕ} (π : NCPart n) {t u : ℕ}
    (ht : π.prefixExcessFirstZero t)
    (hu : π.prefixExcessFirstZero u) :
    t = u := by
  by_cases htu : t < u
  · have hpos : 0 < π.prefixExcess t := hu.2 t htu
    have hzero : π.prefixExcess t = 0 := ht.1
    omega
  · by_cases hut : u < t
    · have hpos : 0 < π.prefixExcess u := ht.2 u hut
      have hzero : π.prefixExcess u = 0 := hu.1
      omega
    · omega

/-- Noncrossing interval-nesting, right side.

If a block `B₁` contains `a<c` and a distinct block `B₂` contains a point
`b` strictly between them, then no point of `B₂` can lie to the right of `c`.
Otherwise the two blocks would cross. -/
theorem NonCrossing.block_element_le_right_of_between
    {n : ℕ} {P : Finpartition (range n)}
    (hNC : NonCrossing P)
    {B₁ B₂ : Finset ℕ} (hB₁ : B₁ ∈ P.parts) (hB₂ : B₂ ∈ P.parts)
    {a b c d : ℕ}
    (ha : a ∈ B₁) (hb : b ∈ B₂) (hc : c ∈ B₁) (hd : d ∈ B₂)
    (hab : a < b) (hbc : b < c) (hneq : B₁ ≠ B₂) :
    d ≤ c := by
  by_contra hdc
  have hcd : c < d := Nat.lt_of_not_ge hdc
  exact hneq (hNC B₁ hB₁ B₂ hB₂ a ha b hb c hc d hd hab hbc hcd)

/-- Noncrossing interval-nesting, left side.

If a block `B₁` contains `a<d` and a distinct block `B₂` contains a point
`c` strictly between them, then no point of `B₂` can lie to the left of `a`.
Otherwise the two blocks would cross. -/
theorem NonCrossing.left_le_block_element_of_between
    {n : ℕ} {P : Finpartition (range n)}
    (hNC : NonCrossing P)
    {B₁ B₂ : Finset ℕ} (hB₁ : B₁ ∈ P.parts) (hB₂ : B₂ ∈ P.parts)
    {a b c d : ℕ}
    (ha : a ∈ B₁) (hb : b ∈ B₂) (hc : c ∈ B₂) (hd : d ∈ B₁)
    (hac : a < c) (hcd : c < d) (hneq : B₁ ≠ B₂) :
    a ≤ b := by
  by_contra hab
  have hba : b < a := Nat.lt_of_not_ge hab
  exact hneq ((hNC B₂ hB₂ B₁ hB₁ b hb a ha c hc d hd hba hac hcd).symm)

/-- A block meeting the inside of a distinct noncrossing block cannot escape
that block's span.

If `i` and `j` lie in one block, `k` lies strictly between them in a distinct
block, then every element of the block of `k` lies between `i` and `j`. -/
theorem NCPart.part_subset_Icc_of_between_distinct
    {n : ℕ} (π : NCPart n) {i j k : Fin n}
    (hik : i.val < k.val) (hkj : k.val < j.val)
    (hjmem : j.val ∈ π.1.part i.val)
    (hneq : π.1.part i.val ≠ π.1.part k.val) :
    ∀ x ∈ π.1.part k.val, i.val ≤ x ∧ x ≤ j.val := by
  intro x hx
  have hiRange : i.val ∈ range n := mem_range.mpr i.2
  have hkRange : k.val ∈ range n := mem_range.mpr k.2
  have hB₁ : π.1.part i.val ∈ π.1.parts := π.1.part_mem.mpr hiRange
  have hB₂ : π.1.part k.val ∈ π.1.parts := π.1.part_mem.mpr hkRange
  have himem : i.val ∈ π.1.part i.val := π.1.mem_part hiRange
  have hkmem : k.val ∈ π.1.part k.val := π.1.mem_part hkRange
  constructor
  · exact
      NonCrossing.left_le_block_element_of_between π.2
        hB₁ hB₂ himem hx hkmem hjmem hik hkj hneq
  · exact
      NonCrossing.block_element_le_right_of_between π.2
        hB₁ hB₂ himem hkmem hjmem hx hik hkj hneq

/-- A block represented between two zero-block points, but not itself in the
zero block, is strictly confined to that zero-block gap. -/
theorem NCPart.part_subset_open_interval_of_between_zeroBlock_points
    {n : ℕ} (π : NCPart (n + 1)) {i j k : Fin (n + 1)}
    (himem : i.val ∈ π.1.part (0 : ℕ))
    (hjmem : j.val ∈ π.1.part (0 : ℕ))
    (hik : i.val < k.val) (hkj : k.val < j.val)
    (hknot : k.val ∉ π.1.part (0 : ℕ)) :
    ∀ x ∈ π.1.part k.val, i.val < x ∧ x < j.val := by
  intro x hx
  have hzeroRange : (0 : ℕ) ∈ range (n + 1) :=
    mem_range.mpr (Nat.succ_pos n)
  have hB₀ : π.1.part (0 : ℕ) ∈ π.1.parts := π.1.part_mem.mpr hzeroRange
  have hkRange : k.val ∈ range (n + 1) := mem_range.mpr k.2
  have hBₖ : π.1.part k.val ∈ π.1.parts := π.1.part_mem.mpr hkRange
  have hparti0 : π.1.part i.val = π.1.part (0 : ℕ) :=
    π.1.part_eq_of_mem hB₀ himem
  have hjmem_i : j.val ∈ π.1.part i.val := by
    rw [hparti0]
    exact hjmem
  have hneq : π.1.part i.val ≠ π.1.part k.val := by
    intro hpart
    apply hknot
    have hkmem : k.val ∈ π.1.part k.val := π.1.mem_part hkRange
    rw [← hparti0, hpart]
    exact hkmem
  have hclosed :=
    π.part_subset_Icc_of_between_distinct hik hkj hjmem_i hneq x hx
  have hxne_i : x ≠ i.val := by
    intro hxi
    apply hknot
    have hpartik : π.1.part i.val = π.1.part k.val :=
      π.1.part_eq_of_mem hBₖ (by
        simpa [hxi] using hx)
    have hkmem : k.val ∈ π.1.part k.val := π.1.mem_part hkRange
    rw [← hparti0, hpartik]
    exact hkmem
  have hxne_j : x ≠ j.val := by
    intro hxj
    apply hknot
    have hpartj0 : π.1.part j.val = π.1.part (0 : ℕ) :=
      π.1.part_eq_of_mem hB₀ hjmem
    have hpartjk : π.1.part j.val = π.1.part k.val :=
      π.1.part_eq_of_mem hBₖ (by
        simpa [hxj] using hx)
    have hkmem : k.val ∈ π.1.part k.val := π.1.mem_part hkRange
    rw [← hpartj0, hpartjk]
    exact hkmem
  constructor <;> omega

/-- Marker-level version of confinement to a zero-block gap. -/
theorem NCPart.exists_min_max_markers_open_interval_of_between_zeroBlock_points
    {n : ℕ} (π : NCPart (n + 1)) {i j k : Fin (n + 1)}
    (himem : i.val ∈ π.1.part (0 : ℕ))
    (hjmem : j.val ∈ π.1.part (0 : ℕ))
    (hik : i.val < k.val) (hkj : k.val < j.val)
    (hknot : k.val ∉ π.1.part (0 : ℕ)) :
    ∃ l r : Fin (n + 1),
      l.val ∈ π.1.part k.val ∧ π.isBlockMin l ∧
        r.val ∈ π.1.part k.val ∧ π.isBlockMax r ∧
          (i.val < l.val ∧ l.val < j.val) ∧
            (i.val < r.val ∧ r.val < j.val) := by
  rcases π.exists_isBlockMin_mem_part k with ⟨l, hlmem, hlmin⟩
  rcases π.exists_isBlockMax_mem_part k with ⟨r, hrmem, hrmax⟩
  have hlInside :=
    π.part_subset_open_interval_of_between_zeroBlock_points
      himem hjmem hik hkj hknot l.val hlmem
  have hrInside :=
    π.part_subset_open_interval_of_between_zeroBlock_points
      himem hjmem hik hkj hknot r.val hrmem
  exact ⟨l, r, hlmem, hlmin, hrmem, hrmax, hlInside, hrInside⟩

/-- A block meeting the inside of a block with known min/max endpoints stays
inside those endpoints.

This combines the same-block case, handled by the endpoint markers, with the
distinct-block case, handled by noncrossing interval containment. -/
theorem NCPart.part_subset_Icc_of_between_endpoints
    {n : ℕ} (π : NCPart n) {i j k : Fin n}
    (hiMin : π.isBlockMin i) (hjMax : π.isBlockMax j)
    (hik : i.val < k.val) (hkj : k.val < j.val)
    (hjmem : j.val ∈ π.1.part i.val) :
    ∀ x ∈ π.1.part k.val, i.val ≤ x ∧ x ≤ j.val := by
  intro x hx
  by_cases hneq : π.1.part i.val ≠ π.1.part k.val
  · exact π.part_subset_Icc_of_between_distinct hik hkj hjmem hneq x hx
  · have hEq : π.1.part i.val = π.1.part k.val := by
      exact not_not.mp hneq
    have hx_i : x ∈ π.1.part i.val := by
      rw [hEq]
      exact hx
    have hiRange : i.val ∈ range n := mem_range.mpr i.2
    have hBᵢ : π.1.part i.val ∈ π.1.parts := π.1.part_mem.mpr hiRange
    have hji : π.1.part j.val = π.1.part i.val :=
      π.1.part_eq_of_mem hBᵢ hjmem
    have hx_j : x ∈ π.1.part j.val := by
      rw [hji]
      exact hx_i
    exact ⟨hiMin x hx_i, hjMax x hx_j⟩

/-- Initial-interval form of endpoint containment for the block containing
`0`.

If `j` is the maximum marker of the block containing `0`, then every block
whose representative lies before `j` is contained in the initial interval
ending at `j`. -/
theorem NCPart.part_subset_initial_interval_of_lt_zeroBlockMax
    {n : ℕ} (π : NCPart (n + 1)) {j k : Fin (n + 1)}
    (hjMax : π.isBlockMax j)
    (hjmem : j.val ∈ π.1.part (0 : ℕ))
    (hk : k.val < j.val) :
    ∀ x ∈ π.1.part k.val, x ≤ j.val := by
  intro x hx
  by_cases hk0 : k.val = 0
  · have hkFin : k = 0 := by
      apply Fin.ext
      exact hk0
    subst k
    have hzeroRange : (0 : ℕ) ∈ range (n + 1) :=
      mem_range.mpr (Nat.succ_pos n)
    have hB₀ : π.1.part (0 : ℕ) ∈ π.1.parts := π.1.part_mem.mpr hzeroRange
    have hj0 : π.1.part j.val = π.1.part (0 : ℕ) :=
      π.1.part_eq_of_mem hB₀ hjmem
    have hxj : x ∈ π.1.part j.val := by
      rw [hj0]
      exact hx
    exact hjMax x hxj
  · have h0k : (0 : Fin (n + 1)).val < k.val := by
      exact Nat.pos_of_ne_zero hk0
    have hbound :=
      π.part_subset_Icc_of_between_endpoints
        (i := 0) (j := j) (k := k)
        (π.zero_isBlockMin) hjMax h0k hk hjmem x hx
    exact hbound.2

/-- Closed initial-interval form of endpoint containment for the block
containing `0`.

This includes the endpoint block itself: if `k = j`, the result is exactly
the maximum-marker property of `j`; if `k < j`, it is the strict initial
interval containment lemma. -/
theorem NCPart.part_subset_initial_interval_of_le_zeroBlockMax
    {n : ℕ} (π : NCPart (n + 1)) {j k : Fin (n + 1)}
    (hjMax : π.isBlockMax j)
    (hjmem : j.val ∈ π.1.part (0 : ℕ))
    (hk : k.val ≤ j.val) :
    ∀ x ∈ π.1.part k.val, x ≤ j.val := by
  intro x hx
  rcases Nat.lt_or_eq_of_le hk with hlt | heq
  · exact π.part_subset_initial_interval_of_lt_zeroBlockMax hjMax hjmem hlt x hx
  · have hxj : x ∈ π.1.part j.val := by
      simpa [heq] using hx
    exact hjMax x hxj

/-- The minimum and maximum markers of any block represented in the initial
interval of the `0`-block also lie in that initial interval.

This is the marker-level form needed by first-return reconstruction from the
min/max code: once the maximum marker `j` of the block containing `0` is fixed,
all block endpoint markers for representatives `k ≤ j` occur at positions
`≤ j`. -/
theorem NCPart.exists_min_max_markers_le_of_le_zeroBlockMax
    {n : ℕ} (π : NCPart (n + 1)) {j k : Fin (n + 1)}
    (hjMax : π.isBlockMax j)
    (hjmem : j.val ∈ π.1.part (0 : ℕ))
    (hk : k.val ≤ j.val) :
    ∃ l r : Fin (n + 1),
      l.val ∈ π.1.part k.val ∧ π.isBlockMin l ∧
        r.val ∈ π.1.part k.val ∧ π.isBlockMax r ∧
          l.val ≤ j.val ∧ r.val ≤ j.val := by
  rcases π.exists_isBlockMin_mem_part k with ⟨l, hlmem, hlmin⟩
  rcases π.exists_isBlockMax_mem_part k with ⟨r, hrmem, hrmax⟩
  have hl_le :
      l.val ≤ j.val :=
    π.part_subset_initial_interval_of_le_zeroBlockMax
      hjMax hjmem hk l.val hlmem
  have hr_le :
      r.val ≤ j.val :=
    π.part_subset_initial_interval_of_le_zeroBlockMax
      hjMax hjmem hk r.val hrmem
  exact ⟨l, r, hlmem, hlmin, hrmem, hrmax, hl_le, hr_le⟩

/-- Suffix separation for the block containing `0`.

If `j` is the maximum marker of the block containing `0`, then any block
represented strictly after `j` is contained strictly after `j`.  Otherwise a
point of that block at or before `j` would either belong to the zero block or
cross the zero block. -/
theorem NCPart.part_subset_suffix_interval_of_zeroBlockMax
    {n : ℕ} (π : NCPart (n + 1)) {j k : Fin (n + 1)}
    (hjMax : π.isBlockMax j)
    (hjmem : j.val ∈ π.1.part (0 : ℕ))
    (hjk : j.val < k.val) :
    ∀ x ∈ π.1.part k.val, j.val < x := by
  intro x hx
  by_contra hxnot
  have hxle : x ≤ j.val := Nat.le_of_not_gt hxnot
  have hzeroRange : (0 : ℕ) ∈ range (n + 1) :=
    mem_range.mpr (Nat.succ_pos n)
  have hkRange : k.val ∈ range (n + 1) := mem_range.mpr k.2
  have hB₀ : π.1.part (0 : ℕ) ∈ π.1.parts := π.1.part_mem.mpr hzeroRange
  have hBₖ : π.1.part k.val ∈ π.1.parts := π.1.part_mem.mpr hkRange
  have hjPart : π.1.part j.val = π.1.part (0 : ℕ) :=
    π.1.part_eq_of_mem hB₀ hjmem
  have hkmem : k.val ∈ π.1.part k.val := π.1.mem_part hkRange
  have hcontr_of_zero_part : k.val ∈ π.1.part (0 : ℕ) → False := by
    intro hk0
    have hkj : k.val ∈ π.1.part j.val := by
      rw [hjPart]
      exact hk0
    have hkle : k.val ≤ j.val := hjMax k.val hkj
    omega
  rcases Nat.lt_or_eq_of_le hxle with hxlt | hxeq
  · by_cases hx0 : x = 0
    · have hpart0k : π.1.part (0 : ℕ) = π.1.part k.val := by
        rw [hx0] at hx
        exact π.1.part_eq_of_mem hBₖ hx
      exact hcontr_of_zero_part (by
        rw [hpart0k]
        exact hkmem)
    · have h0x : (0 : ℕ) < x := Nat.pos_of_ne_zero hx0
      have h0mem : (0 : ℕ) ∈ π.1.part (0 : ℕ) := π.1.mem_part hzeroRange
      have hjmem0 : j.val ∈ π.1.part (0 : ℕ) := hjmem
      have hEq :
          π.1.part (0 : ℕ) = π.1.part k.val :=
        π.2 (π.1.part (0 : ℕ)) hB₀ (π.1.part k.val) hBₖ
          (0 : ℕ) h0mem x hx j.val hjmem0 k.val hkmem
          h0x hxlt hjk
      exact hcontr_of_zero_part (by
        rw [hEq]
        exact hkmem)
  · subst x
    have hjkPart : π.1.part j.val = π.1.part k.val :=
      π.1.part_eq_of_mem hBₖ hx
    exact hcontr_of_zero_part (by
      rw [← hjPart, hjkPart]
      exact hkmem)

/-- The minimum and maximum markers of any block represented after the
zero-block maximum also lie after that maximum. -/
theorem NCPart.exists_min_max_markers_gt_of_gt_zeroBlockMax
    {n : ℕ} (π : NCPart (n + 1)) {j k : Fin (n + 1)}
    (hjMax : π.isBlockMax j)
    (hjmem : j.val ∈ π.1.part (0 : ℕ))
    (hjk : j.val < k.val) :
    ∃ l r : Fin (n + 1),
      l.val ∈ π.1.part k.val ∧ π.isBlockMin l ∧
        r.val ∈ π.1.part k.val ∧ π.isBlockMax r ∧
          j.val < l.val ∧ j.val < r.val := by
  rcases π.exists_isBlockMin_mem_part k with ⟨l, hlmem, hlmin⟩
  rcases π.exists_isBlockMax_mem_part k with ⟨r, hrmem, hrmax⟩
  have hjl :
      j.val < l.val :=
    π.part_subset_suffix_interval_of_zeroBlockMax hjMax hjmem hjk l.val hlmem
  have hjr :
      j.val < r.val :=
    π.part_subset_suffix_interval_of_zeroBlockMax hjMax hjmem hjk r.val hrmem
  exact ⟨l, r, hlmem, hlmin, hrmem, hrmax, hjl, hjr⟩

/-- A block of a finite partition has at most one minimum marker. -/
theorem NCPart.eq_of_isBlockMin_of_same_part
    {n : ℕ} (π : NCPart n) {i j : Fin n}
    (hi : π.isBlockMin i) (hj : π.isBlockMin j)
    (hpart : π.1.part i.val = π.1.part j.val) :
    i = j := by
  apply Fin.ext
  have hjmem : j.val ∈ π.1.part i.val := by
    rw [hpart]
    exact π.1.mem_part (mem_range.mpr j.2)
  have himem : i.val ∈ π.1.part j.val := by
    rw [← hpart]
    exact π.1.mem_part (mem_range.mpr i.2)
  have hij : i.val ≤ j.val := hi j.val hjmem
  have hji : j.val ≤ i.val := hj i.val himem
  omega

/-- A block of a finite partition has at most one maximum marker. -/
theorem NCPart.eq_of_isBlockMax_of_same_part
    {n : ℕ} (π : NCPart n) {i j : Fin n}
    (hi : π.isBlockMax i) (hj : π.isBlockMax j)
    (hpart : π.1.part i.val = π.1.part j.val) :
    i = j := by
  apply Fin.ext
  have hjmem : j.val ∈ π.1.part i.val := by
    rw [hpart]
    exact π.1.mem_part (mem_range.mpr j.2)
  have himem : i.val ∈ π.1.part j.val := by
    rw [← hpart]
    exact π.1.mem_part (mem_range.mpr i.2)
  have hji : j.val ≤ i.val := hi j.val hjmem
  have hij : i.val ≤ j.val := hj i.val himem
  omega

/-- The block containing a point has a unique minimum marker. -/
theorem NCPart.existsUnique_isBlockMin_mem_part
    {n : ℕ} (π : NCPart n) (i : Fin n) :
    ∃! j : Fin n, j.val ∈ π.1.part i.val ∧ π.isBlockMin j := by
  rcases π.exists_isBlockMin_mem_part i with ⟨j, hjmem, hjmin⟩
  refine ⟨j, ⟨hjmem, hjmin⟩, ?_⟩
  intro k hk
  have hiRange : i.val ∈ range n := mem_range.mpr i.2
  have hsPart : π.1.part i.val ∈ π.1.parts := π.1.part_mem.mpr hiRange
  have hji : π.1.part j.val = π.1.part i.val :=
    π.1.part_eq_of_mem hsPart hjmem
  have hki : π.1.part k.val = π.1.part i.val :=
    π.1.part_eq_of_mem hsPart hk.1
  exact (π.eq_of_isBlockMin_of_same_part
    (i := j) (j := k) hjmin hk.2 (hji.trans hki.symm)).symm

/-- The block containing a point has a unique maximum marker. -/
theorem NCPart.existsUnique_isBlockMax_mem_part
    {n : ℕ} (π : NCPart n) (i : Fin n) :
    ∃! j : Fin n, j.val ∈ π.1.part i.val ∧ π.isBlockMax j := by
  rcases π.exists_isBlockMax_mem_part i with ⟨j, hjmem, hjmax⟩
  refine ⟨j, ⟨hjmem, hjmax⟩, ?_⟩
  intro k hk
  have hiRange : i.val ∈ range n := mem_range.mpr i.2
  have hsPart : π.1.part i.val ∈ π.1.parts := π.1.part_mem.mpr hiRange
  have hji : π.1.part j.val = π.1.part i.val :=
    π.1.part_eq_of_mem hsPart hjmem
  have hki : π.1.part k.val = π.1.part i.val :=
    π.1.part_eq_of_mem hsPart hk.1
  exact (π.eq_of_isBlockMax_of_same_part
    (i := j) (j := k) hjmax hk.2 (hji.trans hki.symm)).symm

/-- A nonzero block opened before a zero-block point stays before that point.

If `x` lies in the block containing `0`, then any other block whose minimum
marker is at or before `x` cannot have an element after `x`; otherwise it would
cross the zero block. -/
theorem NCPart.block_element_le_of_blockMin_le_mem_zeroBlock
    {n : ℕ} (π : NCPart (n + 1)) {x l r : Fin (n + 1)}
    (hxmem : x.val ∈ π.1.part (0 : ℕ))
    (hlMin : π.isBlockMin l)
    (hlle : l.val ≤ x.val)
    (hl0 : l ≠ 0)
    (hrmem : r.val ∈ π.1.part l.val) :
    r.val ≤ x.val := by
  by_contra hrnot
  have hxr : x.val < r.val := Nat.lt_of_not_ge hrnot
  have hzeroRange : (0 : ℕ) ∈ range (n + 1) :=
    mem_range.mpr (Nat.succ_pos n)
  have hlRange : l.val ∈ range (n + 1) := mem_range.mpr l.2
  have hB₀ : π.1.part (0 : ℕ) ∈ π.1.parts := π.1.part_mem.mpr hzeroRange
  have hBₗ : π.1.part l.val ∈ π.1.parts := π.1.part_mem.mpr hlRange
  have h0mem : (0 : ℕ) ∈ π.1.part (0 : ℕ) := π.1.mem_part hzeroRange
  have hllmem : l.val ∈ π.1.part l.val := π.1.mem_part hlRange
  have h0l : (0 : ℕ) < l.val := by
    exact Nat.pos_of_ne_zero (by
      intro hval
      apply hl0
      apply Fin.ext
      exact hval)
  have hlx : l.val < x.val := by
    rcases Nat.lt_or_eq_of_le hlle with hlt | heq
    · exact hlt
    · have hlxFin : l = x := by
        apply Fin.ext
        exact heq
      subst x
      have hpart_l0 : π.1.part l.val = π.1.part (0 : ℕ) :=
        π.1.part_eq_of_mem hB₀ hxmem
      have hl_eq_zero :
          (0 : Fin (n + 1)) = l :=
        π.eq_of_isBlockMin_of_same_part
          (i := 0) (j := l) π.zero_isBlockMin hlMin hpart_l0.symm
      exact False.elim (hl0 hl_eq_zero.symm)
  have hEq :
      π.1.part (0 : ℕ) = π.1.part l.val :=
    π.2 (π.1.part (0 : ℕ)) hB₀ (π.1.part l.val) hBₗ
      (0 : ℕ) h0mem l.val hllmem x.val hxmem r.val hrmem
      h0l hlx hxr
  have hl_eq_zero :
      (0 : Fin (n + 1)) = l :=
    π.eq_of_isBlockMin_of_same_part
      (i := 0) (j := l) π.zero_isBlockMin hlMin hEq
  exact hl0 hl_eq_zero.symm

/-- The canonical minimum marker of the block containing `i`. -/
noncomputable def NCPart.blockMinMarker
    {n : ℕ} (π : NCPart n) (i : Fin n) : Fin n :=
  Classical.choose (π.existsUnique_isBlockMin_mem_part i).exists

/-- The canonical minimum marker lies in the block containing `i`. -/
theorem NCPart.blockMinMarker_mem_part
    {n : ℕ} (π : NCPart n) (i : Fin n) :
    (π.blockMinMarker i).val ∈ π.1.part i.val :=
  (Classical.choose_spec (π.existsUnique_isBlockMin_mem_part i).exists).1

/-- The canonical minimum marker is a minimum marker. -/
theorem NCPart.blockMinMarker_isBlockMin
    {n : ℕ} (π : NCPart n) (i : Fin n) :
    π.isBlockMin (π.blockMinMarker i) :=
  (Classical.choose_spec (π.existsUnique_isBlockMin_mem_part i).exists).2

/-- Up to any prefix, closed blocks inject into opened blocks by sending a
maximum marker to the minimum marker of the same block. -/
theorem NCPart.prefixMaxMarker_card_le_prefixMinMarker_card
    {n : ℕ} (π : NCPart n) (t : ℕ) :
    Fintype.card {i : Fin n // π.prefixMaxMarker t i} ≤
      Fintype.card {i : Fin n // π.prefixMinMarker t i} := by
  classical
  let f :
      {i : Fin n // π.prefixMaxMarker t i} →
        {i : Fin n // π.prefixMinMarker t i} :=
    fun i =>
      ⟨π.blockMinMarker i.1, by
        rcases i.2 with ⟨hile, _himax⟩
        have hmin : π.isBlockMin (π.blockMinMarker i.1) :=
          π.blockMinMarker_isBlockMin i.1
        have hmem : (π.blockMinMarker i.1).val ∈ π.1.part i.1.val :=
          π.blockMinMarker_mem_part i.1
        have hiRange : i.1.val ∈ range n := mem_range.mpr i.1.2
        have hpart :
            π.1.part (π.blockMinMarker i.1).val = π.1.part i.1.val :=
          π.1.part_eq_of_mem (π.1.part_mem.mpr hiRange) hmem
        have hii : i.1.val ∈ π.1.part (π.blockMinMarker i.1).val := by
          rw [hpart]
          exact π.1.mem_part hiRange
        exact ⟨(hmin i.1.val hii).trans hile, hmin⟩⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    rcases x.2 with ⟨_hxle, hxmax⟩
    rcases y.2 with ⟨_hyle, hymax⟩
    have hminEq :
        π.blockMinMarker x.1 = π.blockMinMarker y.1 :=
      congrArg Subtype.val hxy
    have hxRange : x.1.val ∈ range n := mem_range.mpr x.1.2
    have hyRange : y.1.val ∈ range n := mem_range.mpr y.1.2
    have hxpart :
        π.1.part (π.blockMinMarker x.1).val = π.1.part x.1.val :=
      π.1.part_eq_of_mem (π.1.part_mem.mpr hxRange)
        (π.blockMinMarker_mem_part x.1)
    have hypart :
        π.1.part (π.blockMinMarker y.1).val = π.1.part y.1.val :=
      π.1.part_eq_of_mem (π.1.part_mem.mpr hyRange)
        (π.blockMinMarker_mem_part y.1)
    have hpart : π.1.part x.1.val = π.1.part y.1.val := by
      calc
        π.1.part x.1.val =
            π.1.part (π.blockMinMarker x.1).val := hxpart.symm
        _ = π.1.part (π.blockMinMarker y.1).val := by rw [hminEq]
        _ = π.1.part y.1.val := hypart
    exact π.eq_of_isBlockMax_of_same_part hxmax hymax hpart
  exact Fintype.card_le_of_injective f hf

/-- Prefix balance is equivalent to zero prefix excess. -/
theorem NCPart.prefixExcess_eq_zero_iff_prefixBalanced
    {n : ℕ} (π : NCPart n) (t : ℕ) :
    π.prefixExcess t = 0 ↔ π.prefixBalanced t := by
  have hle := π.prefixMaxMarker_card_le_prefixMinMarker_card t
  unfold NCPart.prefixExcess NCPart.prefixBalanced
  omega

/-- The canonical maximum marker of the block containing `i`. -/
noncomputable def NCPart.blockMaxMarker
    {n : ℕ} (π : NCPart n) (i : Fin n) : Fin n :=
  Classical.choose (π.existsUnique_isBlockMax_mem_part i).exists

/-- The canonical maximum marker lies in the block containing `i`. -/
theorem NCPart.blockMaxMarker_mem_part
    {n : ℕ} (π : NCPart n) (i : Fin n) :
    (π.blockMaxMarker i).val ∈ π.1.part i.val :=
  (Classical.choose_spec (π.existsUnique_isBlockMax_mem_part i).exists).1

/-- The canonical maximum marker is a maximum marker. -/
theorem NCPart.blockMaxMarker_isBlockMax
    {n : ℕ} (π : NCPart n) (i : Fin n) :
    π.isBlockMax (π.blockMaxMarker i) :=
  (Classical.choose_spec (π.existsUnique_isBlockMax_mem_part i).exists).2

/-- The canonical maximum marker of the block containing `0`. -/
noncomputable def NCPart.zeroBlockMaxMarker
    {n : ℕ} (π : NCPart (n + 1)) : Fin (n + 1) :=
  π.blockMaxMarker 0

/-- The canonical zero-block maximum marker lies in the block containing `0`. -/
theorem NCPart.zeroBlockMaxMarker_mem_part
    {n : ℕ} (π : NCPart (n + 1)) :
    (π.zeroBlockMaxMarker).val ∈ π.1.part (0 : ℕ) :=
  π.blockMaxMarker_mem_part 0

/-- The canonical zero-block maximum marker is a maximum marker. -/
theorem NCPart.zeroBlockMaxMarker_isBlockMax
    {n : ℕ} (π : NCPart (n + 1)) :
    π.isBlockMax π.zeroBlockMaxMarker :=
  π.blockMaxMarker_isBlockMax 0

/-- Before the maximum marker of the block containing `0`, prefix maximum
markers are strictly fewer than prefix minimum markers.

The injection sends a closed block to its minimum marker.  It is not surjective
onto prefix minimum markers because the marker `0` belongs to the open block
whose maximum marker is the later point `j`. -/
theorem NCPart.prefixMaxMarker_card_lt_prefixMinMarker_card_of_lt_zeroBlockMax
    {n : ℕ} (π : NCPart (n + 1)) {j : Fin (n + 1)} {t : ℕ}
    (hjMax : π.isBlockMax j)
    (hjmem : j.val ∈ π.1.part (0 : ℕ))
    (ht : t < j.val) :
    Fintype.card {i : Fin (n + 1) // π.prefixMaxMarker t i} <
      Fintype.card {i : Fin (n + 1) // π.prefixMinMarker t i} := by
  classical
  let f :
      {i : Fin (n + 1) // π.prefixMaxMarker t i} →
        {i : Fin (n + 1) // π.prefixMinMarker t i} :=
    fun i =>
      ⟨π.blockMinMarker i.1, by
        rcases i.2 with ⟨hile, _himax⟩
        have hmin : π.isBlockMin (π.blockMinMarker i.1) :=
          π.blockMinMarker_isBlockMin i.1
        have hmem : (π.blockMinMarker i.1).val ∈ π.1.part i.1.val :=
          π.blockMinMarker_mem_part i.1
        have hiRange : i.1.val ∈ range (n + 1) := mem_range.mpr i.1.2
        have hpart :
            π.1.part (π.blockMinMarker i.1).val = π.1.part i.1.val :=
          π.1.part_eq_of_mem (π.1.part_mem.mpr hiRange) hmem
        have hii : i.1.val ∈ π.1.part (π.blockMinMarker i.1).val := by
          rw [hpart]
          exact π.1.mem_part hiRange
        exact ⟨(hmin i.1.val hii).trans hile, hmin⟩⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    rcases x.2 with ⟨_hxle, hxmax⟩
    rcases y.2 with ⟨_hyle, hymax⟩
    have hminEq :
        π.blockMinMarker x.1 = π.blockMinMarker y.1 :=
      congrArg Subtype.val hxy
    have hxRange : x.1.val ∈ range (n + 1) := mem_range.mpr x.1.2
    have hyRange : y.1.val ∈ range (n + 1) := mem_range.mpr y.1.2
    have hxpart :
        π.1.part (π.blockMinMarker x.1).val = π.1.part x.1.val :=
      π.1.part_eq_of_mem (π.1.part_mem.mpr hxRange)
        (π.blockMinMarker_mem_part x.1)
    have hypart :
        π.1.part (π.blockMinMarker y.1).val = π.1.part y.1.val :=
      π.1.part_eq_of_mem (π.1.part_mem.mpr hyRange)
        (π.blockMinMarker_mem_part y.1)
    have hpart : π.1.part x.1.val = π.1.part y.1.val := by
      calc
        π.1.part x.1.val =
            π.1.part (π.blockMinMarker x.1).val := hxpart.symm
        _ = π.1.part (π.blockMinMarker y.1).val := by rw [hminEq]
        _ = π.1.part y.1.val := hypart
    exact π.eq_of_isBlockMax_of_same_part hxmax hymax hpart
  have hnotSurj : ¬ Function.Surjective f := by
    intro hsurj
    let z : {i : Fin (n + 1) // π.prefixMinMarker t i} :=
      ⟨0, ⟨Nat.zero_le t, π.zero_isBlockMin⟩⟩
    rcases hsurj z with ⟨x, hx⟩
    rcases x.2 with ⟨hxle, hxmax⟩
    have hminZero : π.blockMinMarker x.1 = (0 : Fin (n + 1)) :=
      congrArg Subtype.val hx
    have hxmem : (0 : ℕ) ∈ π.1.part x.1.val := by
      simpa [hminZero] using π.blockMinMarker_mem_part x.1
    have hxRange : x.1.val ∈ range (n + 1) := mem_range.mpr x.1.2
    have hzeroPart :
        π.1.part (0 : ℕ) = π.1.part x.1.val :=
      π.1.part_eq_of_mem (π.1.part_mem.mpr hxRange) hxmem
    have hzeroRange : (0 : ℕ) ∈ range (n + 1) :=
      mem_range.mpr (Nat.succ_pos n)
    have hjPart :
        π.1.part j.val = π.1.part (0 : ℕ) :=
      π.1.part_eq_of_mem (π.1.part_mem.mpr hzeroRange) hjmem
    have hxjPart : π.1.part x.1.val = π.1.part j.val :=
      hzeroPart.symm.trans hjPart.symm
    have hxj : x.1 = j :=
      π.eq_of_isBlockMax_of_same_part hxmax hjMax hxjPart
    have hjle : j.val ≤ t := by
      simpa [hxj] using hxle
    omega
  exact Fintype.card_lt_of_injective_not_surjective f hf hnotSurj

/-- At the maximum marker of the block containing `0`, prefix minimum and
maximum marker counts are equal.

Every block represented in the initial interval has both endpoint markers in
that same interval.  Mapping a prefix minimum marker to its block maximum gives
one injection, and mapping a prefix maximum marker to its block minimum gives
the other. -/
theorem NCPart.prefixMinMarker_card_eq_prefixMaxMarker_card_of_zeroBlockMax
    {n : ℕ} (π : NCPart (n + 1)) {j : Fin (n + 1)}
    (hjMax : π.isBlockMax j)
    (hjmem : j.val ∈ π.1.part (0 : ℕ)) :
    Fintype.card {i : Fin (n + 1) // π.prefixMinMarker j.val i} =
      Fintype.card {i : Fin (n + 1) // π.prefixMaxMarker j.val i} := by
  classical
  let minToMax :
      {i : Fin (n + 1) // π.prefixMinMarker j.val i} →
        {i : Fin (n + 1) // π.prefixMaxMarker j.val i} :=
    fun i =>
      ⟨π.blockMaxMarker i.1, by
        rcases i.2 with ⟨hile, _himin⟩
        have hmax : π.isBlockMax (π.blockMaxMarker i.1) :=
          π.blockMaxMarker_isBlockMax i.1
        have hmem : (π.blockMaxMarker i.1).val ∈ π.1.part i.1.val :=
          π.blockMaxMarker_mem_part i.1
        have hle :
            (π.blockMaxMarker i.1).val ≤ j.val :=
          π.part_subset_initial_interval_of_le_zeroBlockMax
            hjMax hjmem hile (π.blockMaxMarker i.1).val hmem
        exact ⟨hle, hmax⟩⟩
  have hMinToMax : Function.Injective minToMax := by
    intro x y hxy
    apply Subtype.ext
    rcases x.2 with ⟨_hxle, hxmin⟩
    rcases y.2 with ⟨_hyle, hymin⟩
    have hmaxEq :
        π.blockMaxMarker x.1 = π.blockMaxMarker y.1 :=
      congrArg Subtype.val hxy
    have hxRange : x.1.val ∈ range (n + 1) := mem_range.mpr x.1.2
    have hyRange : y.1.val ∈ range (n + 1) := mem_range.mpr y.1.2
    have hxpart :
        π.1.part (π.blockMaxMarker x.1).val = π.1.part x.1.val :=
      π.1.part_eq_of_mem (π.1.part_mem.mpr hxRange)
        (π.blockMaxMarker_mem_part x.1)
    have hypart :
        π.1.part (π.blockMaxMarker y.1).val = π.1.part y.1.val :=
      π.1.part_eq_of_mem (π.1.part_mem.mpr hyRange)
        (π.blockMaxMarker_mem_part y.1)
    have hpart : π.1.part x.1.val = π.1.part y.1.val := by
      calc
        π.1.part x.1.val =
            π.1.part (π.blockMaxMarker x.1).val := hxpart.symm
        _ = π.1.part (π.blockMaxMarker y.1).val := by rw [hmaxEq]
        _ = π.1.part y.1.val := hypart
    exact π.eq_of_isBlockMin_of_same_part hxmin hymin hpart
  let maxToMin :
      {i : Fin (n + 1) // π.prefixMaxMarker j.val i} →
        {i : Fin (n + 1) // π.prefixMinMarker j.val i} :=
    fun i =>
      ⟨π.blockMinMarker i.1, by
        rcases i.2 with ⟨hile, _himax⟩
        have hmin : π.isBlockMin (π.blockMinMarker i.1) :=
          π.blockMinMarker_isBlockMin i.1
        have hmem : (π.blockMinMarker i.1).val ∈ π.1.part i.1.val :=
          π.blockMinMarker_mem_part i.1
        have hiRange : i.1.val ∈ range (n + 1) := mem_range.mpr i.1.2
        have hpart :
            π.1.part (π.blockMinMarker i.1).val = π.1.part i.1.val :=
          π.1.part_eq_of_mem (π.1.part_mem.mpr hiRange) hmem
        have hii : i.1.val ∈ π.1.part (π.blockMinMarker i.1).val := by
          rw [hpart]
          exact π.1.mem_part hiRange
        exact ⟨(hmin i.1.val hii).trans hile, hmin⟩⟩
  have hMaxToMin : Function.Injective maxToMin := by
    intro x y hxy
    apply Subtype.ext
    rcases x.2 with ⟨_hxle, hxmax⟩
    rcases y.2 with ⟨_hyle, hymax⟩
    have hminEq :
        π.blockMinMarker x.1 = π.blockMinMarker y.1 :=
      congrArg Subtype.val hxy
    have hxRange : x.1.val ∈ range (n + 1) := mem_range.mpr x.1.2
    have hyRange : y.1.val ∈ range (n + 1) := mem_range.mpr y.1.2
    have hxpart :
        π.1.part (π.blockMinMarker x.1).val = π.1.part x.1.val :=
      π.1.part_eq_of_mem (π.1.part_mem.mpr hxRange)
        (π.blockMinMarker_mem_part x.1)
    have hypart :
        π.1.part (π.blockMinMarker y.1).val = π.1.part y.1.val :=
      π.1.part_eq_of_mem (π.1.part_mem.mpr hyRange)
        (π.blockMinMarker_mem_part y.1)
    have hpart : π.1.part x.1.val = π.1.part y.1.val := by
      calc
        π.1.part x.1.val =
            π.1.part (π.blockMinMarker x.1).val := hxpart.symm
        _ = π.1.part (π.blockMinMarker y.1).val := by rw [hminEq]
        _ = π.1.part y.1.val := hypart
    exact π.eq_of_isBlockMax_of_same_part hxmax hymax hpart
  apply le_antisymm
  · exact Fintype.card_le_of_injective minToMax hMinToMax
  · exact Fintype.card_le_of_injective maxToMin hMaxToMin

/-- The prefix ending at the maximum marker of the block containing `0` is
balanced. -/
theorem NCPart.prefixBalanced_of_zeroBlockMax
    {n : ℕ} (π : NCPart (n + 1)) {j : Fin (n + 1)}
    (hjMax : π.isBlockMax j)
    (hjmem : j.val ∈ π.1.part (0 : ℕ)) :
    π.prefixBalanced j.val := by
  exact π.prefixMinMarker_card_eq_prefixMaxMarker_card_of_zeroBlockMax
    hjMax hjmem

/-- The prefix excess is zero at the maximum marker of the block containing
`0`. -/
theorem NCPart.prefixExcess_eq_zero_of_zeroBlockMax
    {n : ℕ} (π : NCPart (n + 1)) {j : Fin (n + 1)}
    (hjMax : π.isBlockMax j)
    (hjmem : j.val ∈ π.1.part (0 : ℕ)) :
    π.prefixExcess j.val = 0 := by
  rw [π.prefixExcess_eq_zero_iff_prefixBalanced]
  exact π.prefixBalanced_of_zeroBlockMax hjMax hjmem

/-- No strict prefix before the maximum marker of the block containing `0` is
balanced. -/
theorem NCPart.not_prefixBalanced_of_lt_zeroBlockMax
    {n : ℕ} (π : NCPart (n + 1)) {j : Fin (n + 1)} {t : ℕ}
    (hjMax : π.isBlockMax j)
    (hjmem : j.val ∈ π.1.part (0 : ℕ))
    (ht : t < j.val) :
    ¬ π.prefixBalanced t := by
  intro hbal
  unfold NCPart.prefixBalanced at hbal
  have hlt :=
    π.prefixMaxMarker_card_lt_prefixMinMarker_card_of_lt_zeroBlockMax
      hjMax hjmem ht
  omega

/-- Before the maximum marker of the block containing `0`, the prefix excess is
strictly positive. -/
theorem NCPart.prefixExcess_pos_of_lt_zeroBlockMax
    {n : ℕ} (π : NCPart (n + 1)) {j : Fin (n + 1)} {t : ℕ}
    (hjMax : π.isBlockMax j)
    (hjmem : j.val ∈ π.1.part (0 : ℕ))
    (ht : t < j.val) :
    0 < π.prefixExcess t := by
  have hlt :=
    π.prefixMaxMarker_card_lt_prefixMinMarker_card_of_lt_zeroBlockMax
      hjMax hjmem ht
  unfold NCPart.prefixExcess
  omega

/-- A point of the zero block before its closing marker has prefix excess
exactly one.

The proof sends each opened block in the prefix either to `none` (for the zero
block itself) or to the maximum marker of that block.  The crossing-support
lemma proves that every nonzero block opened before `x` has already closed by
`x`, so this map lands in prefix maximum markers. -/
theorem NCPart.prefixExcess_eq_one_of_mem_zeroBlock_lt_zeroBlockMax
    {n : ℕ} (π : NCPart (n + 1)) {j x : Fin (n + 1)}
    (hjMax : π.isBlockMax j)
    (hjmem : j.val ∈ π.1.part (0 : ℕ))
    (hxmem : x.val ∈ π.1.part (0 : ℕ))
    (hxlt : x.val < j.val) :
    π.prefixExcess x.val = 1 := by
  classical
  let MinPrefix := {l : Fin (n + 1) // π.prefixMinMarker x.val l}
  let MaxPrefix := {r : Fin (n + 1) // π.prefixMaxMarker x.val r}
  let f : MinPrefix → Option MaxPrefix :=
    fun l =>
      if hl0 : l.1 = 0 then
        none
      else
        some
          ⟨π.blockMaxMarker l.1, by
            rcases l.2 with ⟨hlle, hlMin⟩
            have hrmem :
                (π.blockMaxMarker l.1).val ∈ π.1.part l.1.val :=
              π.blockMaxMarker_mem_part l.1
            have hrle :
                (π.blockMaxMarker l.1).val ≤ x.val :=
              π.block_element_le_of_blockMin_le_mem_zeroBlock
                hxmem hlMin hlle hl0 hrmem
            exact ⟨hrle, π.blockMaxMarker_isBlockMax l.1⟩⟩
  have hf : Function.Injective f := by
    intro a b hab
    by_cases ha0 : a.1 = 0
    · by_cases hb0 : b.1 = 0
      · apply Subtype.ext
        rw [ha0, hb0]
      · simp [f, ha0, hb0] at hab
    · by_cases hb0 : b.1 = 0
      · simp [f, ha0, hb0] at hab
      · simp [f, ha0, hb0] at hab
        apply Subtype.ext
        rcases a.2 with ⟨_hale, haMin⟩
        rcases b.2 with ⟨_hble, hbMin⟩
        have hmaxEq :
            π.blockMaxMarker a.1 = π.blockMaxMarker b.1 :=
          congrArg Subtype.val hab
        have haRange : a.1.val ∈ range (n + 1) := mem_range.mpr a.1.2
        have hbRange : b.1.val ∈ range (n + 1) := mem_range.mpr b.1.2
        have hapart :
            π.1.part (π.blockMaxMarker a.1).val = π.1.part a.1.val :=
          π.1.part_eq_of_mem (π.1.part_mem.mpr haRange)
            (π.blockMaxMarker_mem_part a.1)
        have hbpart :
            π.1.part (π.blockMaxMarker b.1).val = π.1.part b.1.val :=
          π.1.part_eq_of_mem (π.1.part_mem.mpr hbRange)
            (π.blockMaxMarker_mem_part b.1)
        have hpart : π.1.part a.1.val = π.1.part b.1.val := by
          calc
            π.1.part a.1.val =
                π.1.part (π.blockMaxMarker a.1).val := hapart.symm
            _ = π.1.part (π.blockMaxMarker b.1).val := by rw [hmaxEq]
            _ = π.1.part b.1.val := hbpart
        exact π.eq_of_isBlockMin_of_same_part haMin hbMin hpart
  have hUpper :
      Fintype.card MinPrefix ≤ Fintype.card MaxPrefix + 1 := by
    have hcard :
        Fintype.card MinPrefix ≤ Fintype.card (Option MaxPrefix) :=
      Fintype.card_le_of_injective f hf
    simpa [MaxPrefix, Fintype.card_option] using hcard
  have hLower :
      Fintype.card MaxPrefix + 1 ≤ Fintype.card MinPrefix := by
    have hlt :
        Fintype.card {i : Fin (n + 1) // π.prefixMaxMarker x.val i} <
          Fintype.card {i : Fin (n + 1) // π.prefixMinMarker x.val i} :=
      π.prefixMaxMarker_card_lt_prefixMinMarker_card_of_lt_zeroBlockMax
        hjMax hjmem hxlt
    dsimp [MinPrefix, MaxPrefix]
    exact Nat.succ_le_of_lt hlt
  have hEq :
      Fintype.card MinPrefix = Fintype.card MaxPrefix + 1 :=
    le_antisymm hUpper hLower
  unfold NCPart.prefixExcess
  dsimp [MinPrefix, MaxPrefix] at hEq
  omega

/-- A neutral point before the zero-block close but outside the zero block has
prefix excess at least two.

Besides the zero block, the block containing `x` is also open at `x`.  The
proof realizes this by injecting `Option (Option MaxPrefix)` into the prefix
minimum markers: `none` maps to the zero-block opener, `some none` maps to the
opener of the block containing `x`, and `some (some r)` maps a closed block to
its opener. -/
theorem NCPart.two_le_prefixExcess_of_not_mem_zeroBlock_of_lt_zeroBlockMaxMarker_of_neutral
    {n : ℕ} (π : NCPart (n + 1)) {x : Fin (n + 1)}
    (hxnot : x.val ∉ π.1.part (0 : ℕ))
    (hxlt : x.val < (π.zeroBlockMaxMarker).val)
    (hneutral : π.isBlockNeutral x) :
    2 ≤ π.prefixExcess x.val := by
  classical
  let MinPrefix := {l : Fin (n + 1) // π.prefixMinMarker x.val l}
  let MaxPrefix := {r : Fin (n + 1) // π.prefixMaxMarker x.val r}
  have hxRange : x.val ∈ range (n + 1) := mem_range.mpr x.2
  have hxmem_x : x.val ∈ π.1.part x.val := π.1.mem_part hxRange
  have hminMem :
      (π.blockMinMarker x).val ∈ π.1.part x.val :=
    π.blockMinMarker_mem_part x
  have hmaxMem :
      (π.blockMaxMarker x).val ∈ π.1.part x.val :=
    π.blockMaxMarker_mem_part x
  have hpart_min_x :
      π.1.part (π.blockMinMarker x).val = π.1.part x.val :=
    π.1.part_eq_of_mem (π.1.part_mem.mpr hxRange) hminMem
  have hx_in_min_part :
      x.val ∈ π.1.part (π.blockMinMarker x).val := by
    rw [hpart_min_x]
    exact hxmem_x
  have hmin_le_x :
      (π.blockMinMarker x).val ≤ x.val :=
    π.blockMinMarker_isBlockMin x x.val hx_in_min_part
  have hmin_ne_zero : π.blockMinMarker x ≠ 0 := by
    intro h
    apply hxnot
    have hzero_in_x : (0 : ℕ) ∈ π.1.part x.val := by
      simpa [h] using hminMem
    have hxpart0 : π.1.part (0 : ℕ) = π.1.part x.val :=
      π.1.part_eq_of_mem (π.1.part_mem.mpr hxRange) hzero_in_x
    rw [hxpart0]
    exact hxmem_x
  have hmax_gt_x :
      x.val < (π.blockMaxMarker x).val := by
    have hpart_max_x :
        π.1.part (π.blockMaxMarker x).val = π.1.part x.val :=
      π.1.part_eq_of_mem (π.1.part_mem.mpr hxRange) hmaxMem
    have hx_in_max_part :
        x.val ∈ π.1.part (π.blockMaxMarker x).val := by
      rw [hpart_max_x]
      exact hxmem_x
    have hx_le_max :
        x.val ≤ (π.blockMaxMarker x).val :=
      π.blockMaxMarker_isBlockMax x x.val hx_in_max_part
    have hmax_ne_x : π.blockMaxMarker x ≠ x := by
      intro h
      exact hneutral.2 (by simpa [h] using π.blockMaxMarker_isBlockMax x)
    have hne : (π.blockMaxMarker x).val ≠ x.val := by
      intro hval
      exact hmax_ne_x (Fin.ext hval)
    omega
  let g : Option (Option MaxPrefix) → MinPrefix :=
    fun q =>
      match q with
      | none =>
          ⟨0, ⟨Nat.zero_le x.val, π.zero_isBlockMin⟩⟩
      | some none =>
          ⟨π.blockMinMarker x, ⟨hmin_le_x, π.blockMinMarker_isBlockMin x⟩⟩
      | some (some r) =>
          ⟨π.blockMinMarker r.1, by
            rcases r.2 with ⟨hrle, _hrMax⟩
            have hmin : π.isBlockMin (π.blockMinMarker r.1) :=
              π.blockMinMarker_isBlockMin r.1
            have hmem : (π.blockMinMarker r.1).val ∈ π.1.part r.1.val :=
              π.blockMinMarker_mem_part r.1
            have hrRange : r.1.val ∈ range (n + 1) := mem_range.mpr r.1.2
            have hpart :
                π.1.part (π.blockMinMarker r.1).val = π.1.part r.1.val :=
              π.1.part_eq_of_mem (π.1.part_mem.mpr hrRange) hmem
            have hrr : r.1.val ∈ π.1.part (π.blockMinMarker r.1).val := by
              rw [hpart]
              exact π.1.mem_part hrRange
            exact ⟨(hmin r.1.val hrr).trans hrle, hmin⟩⟩
  have hnot_none_some_none : g none ≠ g (some none) := by
    intro h
    have hzero_min :
        (0 : Fin (n + 1)) = π.blockMinMarker x :=
      congrArg Subtype.val h
    exact hmin_ne_zero hzero_min.symm
  have hnot_none_some_some :
      ∀ r : MaxPrefix, g none ≠ g (some (some r)) := by
    intro r h
    have hzero_min :
        (0 : Fin (n + 1)) = π.blockMinMarker r.1 :=
      congrArg Subtype.val h
    rcases r.2 with ⟨hrle, hrMax⟩
    have hzero_mem_r :
        (0 : ℕ) ∈ π.1.part r.1.val := by
      simpa [← hzero_min] using π.blockMinMarker_mem_part r.1
    have hrRange : r.1.val ∈ range (n + 1) := mem_range.mpr r.1.2
    have hpart0r :
        π.1.part (0 : ℕ) = π.1.part r.1.val :=
      π.1.part_eq_of_mem (π.1.part_mem.mpr hrRange) hzero_mem_r
    have hzeroRange : (0 : ℕ) ∈ range (n + 1) :=
      mem_range.mpr (Nat.succ_pos n)
    have hB₀ : π.1.part (0 : ℕ) ∈ π.1.parts :=
      π.1.part_mem.mpr hzeroRange
    have hclosePart :
        π.1.part (π.zeroBlockMaxMarker).val = π.1.part (0 : ℕ) :=
      π.1.part_eq_of_mem hB₀ π.zeroBlockMaxMarker_mem_part
    have hclose_eq_r :
        π.zeroBlockMaxMarker = r.1 :=
      π.eq_of_isBlockMax_of_same_part
        (i := π.zeroBlockMaxMarker) (j := r.1)
        π.zeroBlockMaxMarker_isBlockMax hrMax
        (hclosePart.trans hpart0r)
    have hclose_le_x :
        (π.zeroBlockMaxMarker).val ≤ x.val := by
      simpa [hclose_eq_r] using hrle
    omega
  have hnot_some_none_some_some :
      ∀ r : MaxPrefix, g (some none) ≠ g (some (some r)) := by
    intro r h
    have hminEq :
        π.blockMinMarker x = π.blockMinMarker r.1 :=
      congrArg Subtype.val h
    rcases r.2 with ⟨hrle, hrMax⟩
    have hrRange : r.1.val ∈ range (n + 1) := mem_range.mpr r.1.2
    have hrpart :
        π.1.part (π.blockMinMarker r.1).val = π.1.part r.1.val :=
      π.1.part_eq_of_mem (π.1.part_mem.mpr hrRange)
        (π.blockMinMarker_mem_part r.1)
    have hpart_xr : π.1.part x.val = π.1.part r.1.val := by
      calc
        π.1.part x.val =
            π.1.part (π.blockMinMarker x).val := hpart_min_x.symm
        _ = π.1.part (π.blockMinMarker r.1).val := by rw [hminEq]
        _ = π.1.part r.1.val := hrpart
    have hmaxpart :
        π.1.part (π.blockMaxMarker x).val = π.1.part x.val :=
      π.1.part_eq_of_mem (π.1.part_mem.mpr hxRange) hmaxMem
    have hblockMax_eq_r :
        π.blockMaxMarker x = r.1 :=
      π.eq_of_isBlockMax_of_same_part
        (i := π.blockMaxMarker x) (j := r.1)
        (π.blockMaxMarker_isBlockMax x) hrMax
        (hmaxpart.trans hpart_xr)
    have hmax_le_x :
        (π.blockMaxMarker x).val ≤ x.val := by
      simpa [hblockMax_eq_r] using hrle
    omega
  have hg : Function.Injective g := by
    intro a b hab
    cases a with
    | none =>
        cases b with
        | none => rfl
        | some b' =>
            cases b' with
            | none => exact False.elim (hnot_none_some_none hab)
            | some r => exact False.elim (hnot_none_some_some r hab)
    | some a' =>
        cases a' with
        | none =>
            cases b with
            | none => exact False.elim (hnot_none_some_none hab.symm)
            | some b' =>
                cases b' with
                | none => rfl
                | some r => exact False.elim (hnot_some_none_some_some r hab)
        | some r₁ =>
            cases b with
            | none => exact False.elim (hnot_none_some_some r₁ hab.symm)
            | some b' =>
                cases b' with
                | none => exact False.elim (hnot_some_none_some_some r₁ hab.symm)
                | some r₂ =>
                    apply congrArg some
                    apply congrArg some
                    apply Subtype.ext
                    simp [g] at hab
                    rcases r₁.2 with ⟨_hrle₁, hrMax₁⟩
                    rcases r₂.2 with ⟨_hrle₂, hrMax₂⟩
                    have hminEq :
                        π.blockMinMarker r₁.1 = π.blockMinMarker r₂.1 :=
                      congrArg Subtype.val hab
                    have hrRange₁ : r₁.1.val ∈ range (n + 1) := mem_range.mpr r₁.1.2
                    have hrRange₂ : r₂.1.val ∈ range (n + 1) := mem_range.mpr r₂.1.2
                    have hpart₁ :
                        π.1.part (π.blockMinMarker r₁.1).val =
                          π.1.part r₁.1.val :=
                      π.1.part_eq_of_mem (π.1.part_mem.mpr hrRange₁)
                        (π.blockMinMarker_mem_part r₁.1)
                    have hpart₂ :
                        π.1.part (π.blockMinMarker r₂.1).val =
                          π.1.part r₂.1.val :=
                      π.1.part_eq_of_mem (π.1.part_mem.mpr hrRange₂)
                        (π.blockMinMarker_mem_part r₂.1)
                    have hpart : π.1.part r₁.1.val = π.1.part r₂.1.val := by
                      calc
                        π.1.part r₁.1.val =
                            π.1.part (π.blockMinMarker r₁.1).val := hpart₁.symm
                        _ = π.1.part (π.blockMinMarker r₂.1).val := by rw [hminEq]
                        _ = π.1.part r₂.1.val := hpart₂
                    exact π.eq_of_isBlockMax_of_same_part hrMax₁ hrMax₂ hpart
  have hcard :
      Fintype.card (Option (Option MaxPrefix)) ≤ Fintype.card MinPrefix :=
    Fintype.card_le_of_injective g hg
  have hLower :
      Fintype.card MaxPrefix + 2 ≤ Fintype.card MinPrefix := by
    rw [Fintype.card_option, Fintype.card_option] at hcard
    omega
  unfold NCPart.prefixExcess
  dsimp [MinPrefix, MaxPrefix] at hLower
  omega

/-- The maximum marker of the block containing `0` is the first prefix where
the prefix excess returns to zero. -/
theorem NCPart.prefixExcessFirstZero_of_zeroBlockMax
    {n : ℕ} (π : NCPart (n + 1)) {j : Fin (n + 1)}
    (hjMax : π.isBlockMax j)
    (hjmem : j.val ∈ π.1.part (0 : ℕ)) :
    π.prefixExcessFirstZero j.val := by
  constructor
  · exact π.prefixExcess_eq_zero_of_zeroBlockMax hjMax hjmem
  · intro s hs
    exact π.prefixExcess_pos_of_lt_zeroBlockMax hjMax hjmem hs

/-- The canonical zero-block maximum marker is the first prefix where the
prefix excess returns to zero. -/
theorem NCPart.zeroBlockMaxMarker_prefixExcessFirstZero
    {n : ℕ} (π : NCPart (n + 1)) :
    π.prefixExcessFirstZero (π.zeroBlockMaxMarker).val :=
  π.prefixExcessFirstZero_of_zeroBlockMax
    π.zeroBlockMaxMarker_isBlockMax π.zeroBlockMaxMarker_mem_part

/-- Any first-zero prefix-excess position is the canonical zero-block maximum
marker value. -/
theorem NCPart.zeroBlockMaxMarker_val_eq_of_prefixExcessFirstZero
    {n : ℕ} (π : NCPart (n + 1)) {t : ℕ}
    (ht : π.prefixExcessFirstZero t) :
    (π.zeroBlockMaxMarker).val = t :=
  π.prefixExcessFirstZero_unique
    π.zeroBlockMaxMarker_prefixExcessFirstZero ht

/-- Code-side candidate for membership in the block containing `0`.

The intended reconstruction theorem is that this predicate is equivalent to
actual membership in `π.1.part 0`.  The definition is already purely code
visible: it uses the recovered zero-block close, prefix excess, and neutral
marker status. -/
def NCPart.zeroBlockCodeMember
    {n : ℕ} (π : NCPart (n + 1)) (i : Fin (n + 1)) : Prop :=
  i = 0 ∨ i = π.zeroBlockMaxMarker ∨
    (i.val < (π.zeroBlockMaxMarker).val ∧
      π.prefixExcess i.val = 1 ∧ π.isBlockNeutral i)

/-- Equal min/max codes preserve the maximum marker value of the block
containing `0`.

This packages the first-return reconstruction step: the zero-block closing
marker is the first prefix where min/max marker counts balance, and prefix
balance is visible from the min/max code. -/
theorem NCPart.zeroBlockMax_val_eq_of_minMaxCode_eq
    {n : ℕ} {π σ : NCPart (n + 1)}
    (hcode : π.minMaxCode = σ.minMaxCode)
    {j k : Fin (n + 1)}
    (hjMax : π.isBlockMax j)
    (hjmem : j.val ∈ π.1.part (0 : ℕ))
    (hkMax : σ.isBlockMax k)
    (hkmem : k.val ∈ σ.1.part (0 : ℕ)) :
    j.val = k.val := by
  have hπbal_j : π.prefixBalanced j.val :=
    π.prefixBalanced_of_zeroBlockMax hjMax hjmem
  have hσbal_k : σ.prefixBalanced k.val :=
    σ.prefixBalanced_of_zeroBlockMax hkMax hkmem
  have hσbal_j : σ.prefixBalanced j.val :=
    (π.prefixBalanced_iff_of_minMaxCode_eq hcode j.val).mp hπbal_j
  have hπbal_k : π.prefixBalanced k.val :=
    (π.prefixBalanced_iff_of_minMaxCode_eq hcode k.val).mpr hσbal_k
  by_cases hjk : j.val < k.val
  · exact False.elim
      ((σ.not_prefixBalanced_of_lt_zeroBlockMax hkMax hkmem hjk) hσbal_j)
  · by_cases hkj : k.val < j.val
    · exact False.elim
        ((π.not_prefixBalanced_of_lt_zeroBlockMax hjMax hjmem hkj) hπbal_k)
    · omega

/-- Equal min/max codes transport the zero-block closing marker itself. -/
theorem NCPart.zeroBlockMax_mem_and_isBlockMax_of_minMaxCode_eq
    {n : ℕ} {π σ : NCPart (n + 1)}
    (hcode : π.minMaxCode = σ.minMaxCode)
    {j : Fin (n + 1)}
    (hjmem : j.val ∈ π.1.part (0 : ℕ))
    (hjMax : π.isBlockMax j) :
    j.val ∈ σ.1.part (0 : ℕ) ∧ σ.isBlockMax j := by
  rcases σ.exists_isBlockMax_mem_part (0 : Fin (n + 1)) with
    ⟨k, hkmem, hkMax⟩
  have hval :
      j.val = k.val :=
    NCPart.zeroBlockMax_val_eq_of_minMaxCode_eq
      (π := π) (σ := σ) hcode hjMax hjmem hkMax hkmem
  have hkj : k = j := by
    apply Fin.ext
    exact hval.symm
  subst k
  exact ⟨hkmem, hkMax⟩

/-- Equal min/max codes preserve the zero-block closing-marker predicate. -/
theorem NCPart.zeroBlockMax_iff_of_minMaxCode_eq
    {n : ℕ} {π σ : NCPart (n + 1)}
    (hcode : π.minMaxCode = σ.minMaxCode)
    (j : Fin (n + 1)) :
    (j.val ∈ π.1.part (0 : ℕ) ∧ π.isBlockMax j) ↔
      (j.val ∈ σ.1.part (0 : ℕ) ∧ σ.isBlockMax j) := by
  constructor
  · intro h
    exact π.zeroBlockMax_mem_and_isBlockMax_of_minMaxCode_eq
      hcode h.1 h.2
  · intro h
    exact σ.zeroBlockMax_mem_and_isBlockMax_of_minMaxCode_eq
      hcode.symm h.1 h.2

/-- Equal min/max codes have the same canonical zero-block maximum marker. -/
theorem NCPart.zeroBlockMaxMarker_eq_of_minMaxCode_eq
    {n : ℕ} {π σ : NCPart (n + 1)}
    (hcode : π.minMaxCode = σ.minMaxCode) :
    π.zeroBlockMaxMarker = σ.zeroBlockMaxMarker := by
  apply Fin.ext
  exact
    NCPart.zeroBlockMax_val_eq_of_minMaxCode_eq
      (π := π) (σ := σ) hcode
      π.zeroBlockMaxMarker_isBlockMax
      π.zeroBlockMaxMarker_mem_part
      σ.zeroBlockMaxMarker_isBlockMax
      σ.zeroBlockMaxMarker_mem_part

/-- Equal min/max codes preserve the code-side zero-block membership
candidate. -/
theorem NCPart.zeroBlockCodeMember_iff_of_minMaxCode_eq
    {n : ℕ} {π σ : NCPart (n + 1)}
    (hcode : π.minMaxCode = σ.minMaxCode)
    (i : Fin (n + 1)) :
    π.zeroBlockCodeMember i ↔ σ.zeroBlockCodeMember i := by
  have hclose : π.zeroBlockMaxMarker = σ.zeroBlockMaxMarker :=
    π.zeroBlockMaxMarker_eq_of_minMaxCode_eq hcode
  constructor
  · intro h
    rcases h with hzero | hcloseMem | hmid
    · exact Or.inl hzero
    · exact Or.inr (Or.inl (by simpa [hclose] using hcloseMem))
    · rcases hmid with ⟨hlt, hex, hneutral⟩
      refine Or.inr (Or.inr ⟨?_, ?_, ?_⟩)
      · simpa [← hclose] using hlt
      · rw [← π.prefixExcess_eq_of_minMaxCode_eq hcode i.val]
        exact hex
      · exact (π.isBlockNeutral_iff_of_minMaxCode_eq hcode i).mp hneutral
  · intro h
    rcases h with hzero | hcloseMem | hmid
    · exact Or.inl hzero
    · exact Or.inr (Or.inl (by simpa [hclose] using hcloseMem))
    · rcases hmid with ⟨hlt, hex, hneutral⟩
      refine Or.inr (Or.inr ⟨?_, ?_, ?_⟩)
      · simpa [hclose] using hlt
      · rw [π.prefixExcess_eq_of_minMaxCode_eq hcode i.val]
        exact hex
      · exact (π.isBlockNeutral_iff_of_minMaxCode_eq hcode i).mpr hneutral

/-- Initial containment specialized to the canonical zero-block maximum
marker. -/
theorem NCPart.part_subset_initial_interval_of_le_zeroBlockMaxMarker
    {n : ℕ} (π : NCPart (n + 1)) {k : Fin (n + 1)}
    (hk : k.val ≤ (π.zeroBlockMaxMarker).val) :
    ∀ x ∈ π.1.part k.val, x ≤ (π.zeroBlockMaxMarker).val :=
  π.part_subset_initial_interval_of_le_zeroBlockMax
    π.zeroBlockMaxMarker_isBlockMax π.zeroBlockMaxMarker_mem_part hk

/-- Suffix separation specialized to the canonical zero-block maximum
marker. -/
theorem NCPart.part_subset_suffix_interval_of_zeroBlockMaxMarker
    {n : ℕ} (π : NCPart (n + 1)) {k : Fin (n + 1)}
    (hk : (π.zeroBlockMaxMarker).val < k.val) :
    ∀ x ∈ π.1.part k.val, (π.zeroBlockMaxMarker).val < x :=
  π.part_subset_suffix_interval_of_zeroBlockMax
    π.zeroBlockMaxMarker_isBlockMax π.zeroBlockMaxMarker_mem_part hk

/-- Marker-level initial containment specialized to the canonical zero-block
maximum marker. -/
theorem NCPart.exists_min_max_markers_le_of_le_zeroBlockMaxMarker
    {n : ℕ} (π : NCPart (n + 1)) {k : Fin (n + 1)}
    (hk : k.val ≤ (π.zeroBlockMaxMarker).val) :
    ∃ l r : Fin (n + 1),
      l.val ∈ π.1.part k.val ∧ π.isBlockMin l ∧
        r.val ∈ π.1.part k.val ∧ π.isBlockMax r ∧
          l.val ≤ (π.zeroBlockMaxMarker).val ∧
            r.val ≤ (π.zeroBlockMaxMarker).val :=
  π.exists_min_max_markers_le_of_le_zeroBlockMax
    π.zeroBlockMaxMarker_isBlockMax π.zeroBlockMaxMarker_mem_part hk

/-- Marker-level suffix separation specialized to the canonical zero-block
maximum marker. -/
theorem NCPart.exists_min_max_markers_gt_of_gt_zeroBlockMaxMarker
    {n : ℕ} (π : NCPart (n + 1)) {k : Fin (n + 1)}
    (hk : (π.zeroBlockMaxMarker).val < k.val) :
    ∃ l r : Fin (n + 1),
      l.val ∈ π.1.part k.val ∧ π.isBlockMin l ∧
        r.val ∈ π.1.part k.val ∧ π.isBlockMax r ∧
          (π.zeroBlockMaxMarker).val < l.val ∧
            (π.zeroBlockMaxMarker).val < r.val :=
  π.exists_min_max_markers_gt_of_gt_zeroBlockMax
    π.zeroBlockMaxMarker_isBlockMax π.zeroBlockMaxMarker_mem_part hk

/-- A nonzero-block point before the zero-block close has its whole block
strictly inside the open initial interval. -/
theorem NCPart.part_subset_open_initial_interval_of_not_mem_zeroBlock_of_lt_zeroBlockMaxMarker
    {n : ℕ} (π : NCPart (n + 1)) {k : Fin (n + 1)}
    (hknot : k.val ∉ π.1.part (0 : ℕ))
    (hklt : k.val < (π.zeroBlockMaxMarker).val) :
    ∀ x ∈ π.1.part k.val,
      0 < x ∧ x < (π.zeroBlockMaxMarker).val := by
  intro x hx
  have hxle :
      x ≤ (π.zeroBlockMaxMarker).val :=
    π.part_subset_initial_interval_of_le_zeroBlockMaxMarker
      (Nat.le_of_lt hklt) x hx
  have hkRange : k.val ∈ range (n + 1) := mem_range.mpr k.2
  have hBₖ : π.1.part k.val ∈ π.1.parts := π.1.part_mem.mpr hkRange
  have hkmem : k.val ∈ π.1.part k.val := π.1.mem_part hkRange
  have hxneZero : x ≠ 0 := by
    intro hxzero
    apply hknot
    have hpart0k : π.1.part (0 : ℕ) = π.1.part k.val :=
      π.1.part_eq_of_mem hBₖ (by
        simpa [hxzero] using hx)
    rw [hpart0k]
    exact hkmem
  have hxneClose : x ≠ (π.zeroBlockMaxMarker).val := by
    intro hxclose
    apply hknot
    have hzeroRange : (0 : ℕ) ∈ range (n + 1) :=
      mem_range.mpr (Nat.succ_pos n)
    have hB₀ : π.1.part (0 : ℕ) ∈ π.1.parts := π.1.part_mem.mpr hzeroRange
    have hclosePart0 :
        π.1.part (π.zeroBlockMaxMarker).val = π.1.part (0 : ℕ) :=
      π.1.part_eq_of_mem hB₀ π.zeroBlockMaxMarker_mem_part
    have hclosePartK :
        π.1.part (π.zeroBlockMaxMarker).val = π.1.part k.val :=
      π.1.part_eq_of_mem hBₖ (by
        simpa [hxclose] using hx)
    have hpart0k : π.1.part (0 : ℕ) = π.1.part k.val :=
      hclosePart0.symm.trans hclosePartK
    rw [hpart0k]
    exact hkmem
  constructor
  · exact Nat.pos_of_ne_zero hxneZero
  · omega

/-- Marker-level open-initial containment for a nonzero block before the
zero-block close. -/
theorem NCPart.exists_min_max_markers_open_initial_of_not_mem_zeroBlock_of_lt_zeroBlockMaxMarker
    {n : ℕ} (π : NCPart (n + 1)) {k : Fin (n + 1)}
    (hknot : k.val ∉ π.1.part (0 : ℕ))
    (hklt : k.val < (π.zeroBlockMaxMarker).val) :
    ∃ l r : Fin (n + 1),
      l.val ∈ π.1.part k.val ∧ π.isBlockMin l ∧
        r.val ∈ π.1.part k.val ∧ π.isBlockMax r ∧
          (0 < l.val ∧ l.val < (π.zeroBlockMaxMarker).val) ∧
            (0 < r.val ∧ r.val < (π.zeroBlockMaxMarker).val) := by
  rcases π.exists_isBlockMin_mem_part k with ⟨l, hlmem, hlmin⟩
  rcases π.exists_isBlockMax_mem_part k with ⟨r, hrmem, hrmax⟩
  have hlInside :=
    π.part_subset_open_initial_interval_of_not_mem_zeroBlock_of_lt_zeroBlockMaxMarker
      hknot hklt l.val hlmem
  have hrInside :=
    π.part_subset_open_initial_interval_of_not_mem_zeroBlock_of_lt_zeroBlockMaxMarker
      hknot hklt r.val hrmem
  exact ⟨l, r, hlmem, hlmin, hrmem, hrmax, hlInside, hrInside⟩

/-- Any zero-block point different from the canonical close lies strictly
before that close. -/
theorem NCPart.lt_zeroBlockMaxMarker_of_mem_zeroBlock_of_ne_zeroBlockMaxMarker
    {n : ℕ} (π : NCPart (n + 1)) {x : Fin (n + 1)}
    (hxmem : x.val ∈ π.1.part (0 : ℕ))
    (hxClose : x ≠ π.zeroBlockMaxMarker) :
    x.val < (π.zeroBlockMaxMarker).val := by
  have hzeroRange : (0 : ℕ) ∈ range (n + 1) :=
    mem_range.mpr (Nat.succ_pos n)
  have hB₀ : π.1.part (0 : ℕ) ∈ π.1.parts := π.1.part_mem.mpr hzeroRange
  have hclosePart :
      π.1.part (π.zeroBlockMaxMarker).val = π.1.part (0 : ℕ) :=
    π.1.part_eq_of_mem hB₀ π.zeroBlockMaxMarker_mem_part
  have hxmemClose :
      x.val ∈ π.1.part (π.zeroBlockMaxMarker).val := by
    rw [hclosePart]
    exact hxmem
  have hxle :
      x.val ≤ (π.zeroBlockMaxMarker).val :=
    π.zeroBlockMaxMarker_isBlockMax x.val hxmemClose
  have hxne : x.val ≠ (π.zeroBlockMaxMarker).val := by
    intro hval
    apply hxClose
    apply Fin.ext
    exact hval
  omega

/-- A zero-block point that is neither endpoint is neutral. -/
theorem NCPart.isBlockNeutral_of_mem_zeroBlock_of_ne_zero_of_ne_zeroBlockMaxMarker
    {n : ℕ} (π : NCPart (n + 1)) {x : Fin (n + 1)}
    (hxmem : x.val ∈ π.1.part (0 : ℕ))
    (hx0 : x ≠ 0)
    (hxClose : x ≠ π.zeroBlockMaxMarker) :
    π.isBlockNeutral x := by
  constructor
  · intro hxMin
    have hzeroRange : (0 : ℕ) ∈ range (n + 1) :=
      mem_range.mpr (Nat.succ_pos n)
    have hB₀ : π.1.part (0 : ℕ) ∈ π.1.parts := π.1.part_mem.mpr hzeroRange
    have hxpart0 : π.1.part x.val = π.1.part (0 : ℕ) :=
      π.1.part_eq_of_mem hB₀ hxmem
    have hzero_eq_x :
        (0 : Fin (n + 1)) = x :=
      π.eq_of_isBlockMin_of_same_part
        (i := 0) (j := x) π.zero_isBlockMin hxMin hxpart0.symm
    exact hx0 hzero_eq_x.symm
  · intro hxMax
    have hzeroRange : (0 : ℕ) ∈ range (n + 1) :=
      mem_range.mpr (Nat.succ_pos n)
    have hB₀ : π.1.part (0 : ℕ) ∈ π.1.parts := π.1.part_mem.mpr hzeroRange
    have hxpart0 : π.1.part x.val = π.1.part (0 : ℕ) :=
      π.1.part_eq_of_mem hB₀ hxmem
    have hclosePart0 :
        π.1.part (π.zeroBlockMaxMarker).val = π.1.part (0 : ℕ) :=
      π.1.part_eq_of_mem hB₀ π.zeroBlockMaxMarker_mem_part
    have hclose_eq_x :
        π.zeroBlockMaxMarker = x :=
      π.eq_of_isBlockMax_of_same_part
        (i := π.zeroBlockMaxMarker) (j := x)
        π.zeroBlockMaxMarker_isBlockMax hxMax
        (hclosePart0.trans hxpart0.symm)
    exact hxClose hclose_eq_x.symm

/-- Forward correctness of the code-side zero-block membership predicate:
actual membership in the block containing `0` implies the code predicate. -/
theorem NCPart.zeroBlockCodeMember_of_mem_zeroBlock
    {n : ℕ} (π : NCPart (n + 1)) {x : Fin (n + 1)}
    (hxmem : x.val ∈ π.1.part (0 : ℕ)) :
    π.zeroBlockCodeMember x := by
  by_cases hx0 : x = 0
  · exact Or.inl hx0
  · by_cases hxClose : x = π.zeroBlockMaxMarker
    · exact Or.inr (Or.inl hxClose)
    · have hxlt :
        x.val < (π.zeroBlockMaxMarker).val :=
        π.lt_zeroBlockMaxMarker_of_mem_zeroBlock_of_ne_zeroBlockMaxMarker
          hxmem hxClose
      have hex :
          π.prefixExcess x.val = 1 :=
        π.prefixExcess_eq_one_of_mem_zeroBlock_lt_zeroBlockMax
          π.zeroBlockMaxMarker_isBlockMax
          π.zeroBlockMaxMarker_mem_part
          hxmem hxlt
      have hneutral :
          π.isBlockNeutral x :=
        π.isBlockNeutral_of_mem_zeroBlock_of_ne_zero_of_ne_zeroBlockMaxMarker
          hxmem hx0 hxClose
      exact Or.inr (Or.inr ⟨hxlt, hex, hneutral⟩)

/-- Reverse correctness of the code-side zero-block membership predicate:
the code predicate implies actual membership in the block containing `0`. -/
theorem NCPart.mem_zeroBlock_of_zeroBlockCodeMember
    {n : ℕ} (π : NCPart (n + 1)) {x : Fin (n + 1)}
    (hx : π.zeroBlockCodeMember x) :
    x.val ∈ π.1.part (0 : ℕ) := by
  rcases hx with hx0 | hxClose | hmid
  · subst x
    exact π.1.mem_part (mem_range.mpr (Nat.succ_pos n))
  · subst x
    exact π.zeroBlockMaxMarker_mem_part
  · rcases hmid with ⟨hxlt, hex, hneutral⟩
    by_contra hxnot
    have htwo :
        2 ≤ π.prefixExcess x.val :=
      π.two_le_prefixExcess_of_not_mem_zeroBlock_of_lt_zeroBlockMaxMarker_of_neutral
        hxnot hxlt hneutral
    omega

/-- The code-side zero-block membership predicate is exactly actual membership
in the block containing `0`. -/
theorem NCPart.zeroBlockCodeMember_iff_mem_zeroBlock
    {n : ℕ} (π : NCPart (n + 1)) (x : Fin (n + 1)) :
    π.zeroBlockCodeMember x ↔ x.val ∈ π.1.part (0 : ℕ) := by
  constructor
  · exact π.mem_zeroBlock_of_zeroBlockCodeMember
  · exact π.zeroBlockCodeMember_of_mem_zeroBlock

/-- Equal min/max codes have the same actual block containing `0`. -/
theorem NCPart.zeroBlock_part_eq_of_minMaxCode_eq
    {n : ℕ} {π σ : NCPart (n + 1)}
    (hcode : π.minMaxCode = σ.minMaxCode) :
    π.1.part (0 : ℕ) = σ.1.part (0 : ℕ) := by
  apply Finset.ext
  intro x
  constructor
  · intro hx
    have hxRange : x ∈ range (n + 1) := π.1.part_subset (0 : ℕ) hx
    let i : Fin (n + 1) := ⟨x, mem_range.mp hxRange⟩
    have hπcode : π.zeroBlockCodeMember i :=
      (π.zeroBlockCodeMember_iff_mem_zeroBlock i).mpr (by
        simpa [i] using hx)
    have hσcode : σ.zeroBlockCodeMember i :=
      (π.zeroBlockCodeMember_iff_of_minMaxCode_eq hcode i).mp hπcode
    have hσmem : i.val ∈ σ.1.part (0 : ℕ) :=
      (σ.zeroBlockCodeMember_iff_mem_zeroBlock i).mp hσcode
    simpa [i] using hσmem
  · intro hx
    have hxRange : x ∈ range (n + 1) := σ.1.part_subset (0 : ℕ) hx
    let i : Fin (n + 1) := ⟨x, mem_range.mp hxRange⟩
    have hσcode : σ.zeroBlockCodeMember i :=
      (σ.zeroBlockCodeMember_iff_mem_zeroBlock i).mpr (by
        simpa [i] using hx)
    have hπcode : π.zeroBlockCodeMember i :=
      (σ.zeroBlockCodeMember_iff_of_minMaxCode_eq hcode.symm i).mp hσcode
    have hπmem : i.val ∈ π.1.part (0 : ℕ) :=
      (π.zeroBlockCodeMember_iff_mem_zeroBlock i).mp hπcode
    simpa [i] using hπmem

/-- Equal min/max codes transport the whole block of any recovered zero-block
element. -/
theorem NCPart.part_eq_of_mem_zeroBlock_of_minMaxCode_eq
    {n : ℕ} {π σ : NCPart (n + 1)}
    (hcode : π.minMaxCode = σ.minMaxCode) {x : Fin (n + 1)}
    (hxmem : x.val ∈ π.1.part (0 : ℕ)) :
    π.1.part x.val = σ.1.part x.val := by
  have hzeroEq : π.1.part (0 : ℕ) = σ.1.part (0 : ℕ) :=
    π.zeroBlock_part_eq_of_minMaxCode_eq hcode
  have hzeroRange : (0 : ℕ) ∈ range (n + 1) :=
    mem_range.mpr (Nat.succ_pos n)
  have hπB₀ : π.1.part (0 : ℕ) ∈ π.1.parts :=
    π.1.part_mem.mpr hzeroRange
  have hσB₀ : σ.1.part (0 : ℕ) ∈ σ.1.parts :=
    σ.1.part_mem.mpr hzeroRange
  have hπx : π.1.part x.val = π.1.part (0 : ℕ) :=
    π.1.part_eq_of_mem hπB₀ hxmem
  have hxmemσ : x.val ∈ σ.1.part (0 : ℕ) := by
    simpa [← hzeroEq] using hxmem
  have hσx : σ.1.part x.val = σ.1.part (0 : ℕ) :=
    σ.1.part_eq_of_mem hσB₀ hxmemσ
  calc
    π.1.part x.val = π.1.part (0 : ℕ) := hπx
    _ = σ.1.part (0 : ℕ) := hzeroEq
    _ = σ.1.part x.val := hσx.symm

/-- Equal min/max codes transport the whole block of any point whose zero-block
membership is detected by the code-side predicate. -/
theorem NCPart.part_eq_of_zeroBlockCodeMember_of_minMaxCode_eq
    {n : ℕ} {π σ : NCPart (n + 1)}
    (hcode : π.minMaxCode = σ.minMaxCode) {x : Fin (n + 1)}
    (hx : π.zeroBlockCodeMember x) :
    π.1.part x.val = σ.1.part x.val :=
  π.part_eq_of_mem_zeroBlock_of_minMaxCode_eq hcode
    ((π.zeroBlockCodeMember_iff_mem_zeroBlock x).mp hx)

/-- A point outside the zero block cannot be the zero-block closing marker. -/
theorem NCPart.ne_zeroBlockMaxMarker_of_not_mem_zeroBlock
    {n : ℕ} (π : NCPart (n + 1)) {x : Fin (n + 1)}
    (hxnot : x.val ∉ π.1.part (0 : ℕ)) :
    x ≠ π.zeroBlockMaxMarker := by
  intro hx
  apply hxnot
  simpa [hx] using π.zeroBlockMaxMarker_mem_part

/-- Any point outside the zero block is strictly before or strictly after the
zero-block closing marker. -/
theorem NCPart.lt_or_gt_zeroBlockMaxMarker_of_not_mem_zeroBlock
    {n : ℕ} (π : NCPart (n + 1)) {x : Fin (n + 1)}
    (hxnot : x.val ∉ π.1.part (0 : ℕ)) :
    x.val < (π.zeroBlockMaxMarker).val ∨
      (π.zeroBlockMaxMarker).val < x.val := by
  have hxne : x ≠ π.zeroBlockMaxMarker :=
    π.ne_zeroBlockMaxMarker_of_not_mem_zeroBlock hxnot
  have hvalne : x.val ≠ (π.zeroBlockMaxMarker).val := by
    intro hval
    exact hxne (Fin.ext hval)
  omega

/-- Length of the open interval strictly between two ambient points. -/
def NCPart.zeroBlockOpenGapLength
    {n : ℕ} (i j : Fin (n + 1)) : ℕ :=
  j.val - (i.val + 1)

/-- The open interval strictly between two ambient points, as a finset of
ambient natural labels. -/
def NCPart.zeroBlockOpenGapFinset
    {n : ℕ} (i j : Fin (n + 1)) : Finset ℕ :=
  (range (n + 1)).filter fun x => i.val < x ∧ x < j.val

/-- Membership in the open-gap finset is exactly ambient membership plus the
two strict inequalities. -/
theorem NCPart.mem_zeroBlockOpenGapFinset_iff
    {n : ℕ} (i j : Fin (n + 1)) {x : ℕ} :
    x ∈ NCPart.zeroBlockOpenGapFinset i j ↔
      x ∈ range (n + 1) ∧ i.val < x ∧ x < j.val := by
  simp [NCPart.zeroBlockOpenGapFinset]

/-- The ambient carrier of the open interval strictly between two points. -/
def NCPart.zeroBlockOpenGapCarrier
    {n : ℕ} (i j : Fin (n + 1)) : Type :=
  {x : Fin (n + 1) // i.val < x.val ∧ x.val < j.val}

instance {n : ℕ} (i j : Fin (n + 1)) :
    Fintype (NCPart.zeroBlockOpenGapCarrier i j) :=
  Subtype.fintype _

/-- The open gap length is bounded by the ambient predecessor. -/
theorem NCPart.zeroBlockOpenGapLength_le_n
    {n : ℕ} (i j : Fin (n + 1)) :
    NCPart.zeroBlockOpenGapLength i j ≤ n := by
  unfold NCPart.zeroBlockOpenGapLength
  have hj : j.val ≤ n := Nat.le_of_lt_succ j.2
  omega

/-- Reindex the open ambient gap `(i,j)` by consecutive coordinates
`0, …, j-i-2`. -/
def NCPart.zeroBlockOpenGapFinEquiv
    {n : ℕ} (i j : Fin (n + 1)) :
    Fin (NCPart.zeroBlockOpenGapLength i j) ≃
      NCPart.zeroBlockOpenGapCarrier i j where
  toFun := fun t =>
    let x : ℕ := i.val + 1 + t.val
    ⟨⟨x, by
        have ht : t.val < j.val - (i.val + 1) := by
          exact t.2
        have hxlt : t.val + (i.val + 1) < j.val :=
          Nat.add_lt_of_lt_sub ht
        have hj : j.val < n + 1 := j.2
        omega⟩,
      by
        have ht : t.val < j.val - (i.val + 1) := by
          exact t.2
        have hxlt : t.val + (i.val + 1) < j.val :=
          Nat.add_lt_of_lt_sub ht
        dsimp
        constructor <;> omega⟩
  invFun := fun x =>
    ⟨x.1.val - (i.val + 1), by
      have hlt : x.1.val < j.val := x.2.2
      have hgt : i.val < x.1.val := x.2.1
      simp [NCPart.zeroBlockOpenGapLength]
      omega⟩
  left_inv := by
    intro t
    apply Fin.ext
    simp
  right_inv := by
    intro x
    apply Subtype.ext
    apply Fin.ext
    have hlt : x.1.val < j.val := x.2.2
    have hgt : i.val < x.1.val := x.2.1
    simp
    omega

/-- Coordinate formula for the open-gap reindexing equivalence. -/
theorem NCPart.zeroBlockOpenGapFinEquiv_apply_val
    {n : ℕ} (i j : Fin (n + 1))
    (t : Fin (NCPart.zeroBlockOpenGapLength i j)) :
    ((NCPart.zeroBlockOpenGapFinEquiv i j t).1).val =
      i.val + 1 + t.val := by
  rfl

/-- Coordinate formula for the inverse open-gap reindexing equivalence. -/
theorem NCPart.zeroBlockOpenGapFinEquiv_symm_apply_val
    {n : ℕ} (i j : Fin (n + 1))
    (x : NCPart.zeroBlockOpenGapCarrier i j) :
    ((NCPart.zeroBlockOpenGapFinEquiv i j).symm x).val =
      x.1.val - (i.val + 1) := by
  rfl

/-- The ambient carrier subtype is the same finite type as the subtype of
labels belonging to the open-gap finset. -/
def NCPart.zeroBlockOpenGapCarrierEquivFinsetSubtype
    {n : ℕ} (i j : Fin (n + 1)) :
    NCPart.zeroBlockOpenGapCarrier i j ≃
      {x : ℕ // x ∈ NCPart.zeroBlockOpenGapFinset i j} where
  toFun := fun x =>
    ⟨x.1.val, by
      exact
        (NCPart.mem_zeroBlockOpenGapFinset_iff i j).mpr
          ⟨mem_range.mpr x.1.2, x.2.1, x.2.2⟩⟩
  invFun := fun x =>
    ⟨⟨x.1,
      mem_range.mp ((NCPart.mem_zeroBlockOpenGapFinset_iff i j).mp x.2).1⟩,
      ((NCPart.mem_zeroBlockOpenGapFinset_iff i j).mp x.2).2.1,
      ((NCPart.mem_zeroBlockOpenGapFinset_iff i j).mp x.2).2.2⟩
  left_inv := by
    intro x
    apply Subtype.ext
    apply Fin.ext
    rfl
  right_inv := by
    intro x
    apply Subtype.ext
    rfl

/-- The open gap has exactly `j - (i+1)` ambient labels. -/
theorem NCPart.card_zeroBlockOpenGapFinset
    {n : ℕ} (i j : Fin (n + 1)) :
    (NCPart.zeroBlockOpenGapFinset i j).card =
      NCPart.zeroBlockOpenGapLength i j := by
  calc
    (NCPart.zeroBlockOpenGapFinset i j).card =
        Fintype.card {x : ℕ // x ∈ NCPart.zeroBlockOpenGapFinset i j} := by
      simp
    _ = Fintype.card (NCPart.zeroBlockOpenGapCarrier i j) := by
      exact (Fintype.card_congr
        (NCPart.zeroBlockOpenGapCarrierEquivFinsetSubtype i j)).symm
    _ = Fintype.card (Fin (NCPart.zeroBlockOpenGapLength i j)) := by
      exact (Fintype.card_congr (NCPart.zeroBlockOpenGapFinEquiv i j)).symm
    _ = NCPart.zeroBlockOpenGapLength i j := by
      simp

/-- Coordinate of an ambient label relative to the open gap after `i`. -/
def NCPart.zeroBlockOpenGapEncode
    {n : ℕ} (i _j : Fin (n + 1)) (x : ℕ) : ℕ :=
  x - (i.val + 1)

/-- Ambient label represented by a coordinate in the open gap after `i`. -/
def NCPart.zeroBlockOpenGapDecode
    {n : ℕ} (i _j : Fin (n + 1)) (t : ℕ) : ℕ :=
  i.val + 1 + t

/-- Encoding sends labels in the open-gap finset to the intrinsic coordinate
range. -/
theorem NCPart.zeroBlockOpenGapEncode_mem_range_of_mem
    {n : ℕ} (i j : Fin (n + 1)) {x : ℕ}
    (hx : x ∈ NCPart.zeroBlockOpenGapFinset i j) :
    NCPart.zeroBlockOpenGapEncode i j x ∈
      range (NCPart.zeroBlockOpenGapLength i j) := by
  have hx' := (NCPart.mem_zeroBlockOpenGapFinset_iff i j).mp hx
  rw [mem_range]
  unfold NCPart.zeroBlockOpenGapEncode NCPart.zeroBlockOpenGapLength
  omega

/-- Decoding sends intrinsic coordinates back into the open-gap finset. -/
theorem NCPart.zeroBlockOpenGapDecode_mem_of_mem_range
    {n : ℕ} (i j : Fin (n + 1)) {t : ℕ}
    (ht : t ∈ range (NCPart.zeroBlockOpenGapLength i j)) :
    NCPart.zeroBlockOpenGapDecode i j t ∈
      NCPart.zeroBlockOpenGapFinset i j := by
  have htlt : t < j.val - (i.val + 1) := by
    simpa [NCPart.zeroBlockOpenGapLength] using mem_range.mp ht
  have hlt : t + (i.val + 1) < j.val :=
    Nat.add_lt_of_lt_sub htlt
  have hj : j.val < n + 1 := j.2
  exact
    (NCPart.mem_zeroBlockOpenGapFinset_iff i j).mpr
      ⟨mem_range.mpr (by
          unfold NCPart.zeroBlockOpenGapDecode
          omega),
        by
          unfold NCPart.zeroBlockOpenGapDecode
          constructor <;> omega⟩

/-- Decoding after encoding recovers an open-gap ambient label. -/
theorem NCPart.zeroBlockOpenGapDecode_encode_of_mem
    {n : ℕ} (i j : Fin (n + 1)) {x : ℕ}
    (hx : x ∈ NCPart.zeroBlockOpenGapFinset i j) :
    NCPart.zeroBlockOpenGapDecode i j
        (NCPart.zeroBlockOpenGapEncode i j x) = x := by
  have hx' := (NCPart.mem_zeroBlockOpenGapFinset_iff i j).mp hx
  unfold NCPart.zeroBlockOpenGapDecode NCPart.zeroBlockOpenGapEncode
  omega

/-- Encoding after decoding recovers any intrinsic coordinate. -/
theorem NCPart.zeroBlockOpenGapEncode_decode
    {n : ℕ} (i j : Fin (n + 1)) (t : ℕ) :
    NCPart.zeroBlockOpenGapEncode i j
        (NCPart.zeroBlockOpenGapDecode i j t) = t := by
  unfold NCPart.zeroBlockOpenGapEncode NCPart.zeroBlockOpenGapDecode
  omega

/-- Length of the suffix strictly after an ambient point. -/
def NCPart.suffixLength
    {n : ℕ} (j : Fin (n + 1)) : ℕ :=
  (n + 1) - (j.val + 1)

/-- The suffix strictly after an ambient point, as a finset of ambient labels. -/
def NCPart.suffixFinset
    {n : ℕ} (j : Fin (n + 1)) : Finset ℕ :=
  (range (n + 1)).filter fun x => j.val < x

/-- Membership in the suffix finset is exactly ambient membership plus the
strict suffix inequality. -/
theorem NCPart.mem_suffixFinset_iff
    {n : ℕ} (j : Fin (n + 1)) {x : ℕ} :
    x ∈ NCPart.suffixFinset j ↔ x ∈ range (n + 1) ∧ j.val < x := by
  simp [NCPart.suffixFinset]

/-- The ambient carrier of the suffix strictly after a point. -/
def NCPart.suffixCarrier
    {n : ℕ} (j : Fin (n + 1)) : Type :=
  {x : Fin (n + 1) // j.val < x.val}

instance {n : ℕ} (j : Fin (n + 1)) :
    Fintype (NCPart.suffixCarrier j) :=
  Subtype.fintype _

/-- The suffix length is bounded by the ambient predecessor. -/
theorem NCPart.suffixLength_le_n
    {n : ℕ} (j : Fin (n + 1)) :
    NCPart.suffixLength j ≤ n := by
  unfold NCPart.suffixLength
  omega

/-- Reindex the suffix after `j` by consecutive coordinates. -/
def NCPart.suffixFinEquiv
    {n : ℕ} (j : Fin (n + 1)) :
    Fin (NCPart.suffixLength j) ≃ NCPart.suffixCarrier j where
  toFun := fun t =>
    let x : ℕ := j.val + 1 + t.val
    ⟨⟨x, by
        have ht : t.val < (n + 1) - (j.val + 1) := by
          exact t.2
        have hxlt : t.val + (j.val + 1) < n + 1 :=
          Nat.add_lt_of_lt_sub ht
        omega⟩,
      by
        dsimp
        omega⟩
  invFun := fun x =>
    ⟨x.1.val - (j.val + 1), by
      have hlt : x.1.val < n + 1 := x.1.2
      have hgt : j.val < x.1.val := x.2
      simp [NCPart.suffixLength]
      omega⟩
  left_inv := by
    intro t
    apply Fin.ext
    simp
  right_inv := by
    intro x
    apply Subtype.ext
    apply Fin.ext
    have hgt : j.val < x.1.val := x.2
    simp
    omega

/-- Coordinate formula for the suffix reindexing equivalence. -/
theorem NCPart.suffixFinEquiv_apply_val
    {n : ℕ} (j : Fin (n + 1)) (t : Fin (NCPart.suffixLength j)) :
    ((NCPart.suffixFinEquiv j t).1).val = j.val + 1 + t.val := by
  rfl

/-- Coordinate formula for the inverse suffix reindexing equivalence. -/
theorem NCPart.suffixFinEquiv_symm_apply_val
    {n : ℕ} (j : Fin (n + 1)) (x : NCPart.suffixCarrier j) :
    ((NCPart.suffixFinEquiv j).symm x).val = x.1.val - (j.val + 1) := by
  rfl

/-- Coordinate of an ambient label relative to the suffix after `j`. -/
def NCPart.suffixEncode
    {n : ℕ} (j : Fin (n + 1)) (x : ℕ) : ℕ :=
  x - (j.val + 1)

/-- Ambient label represented by a coordinate in the suffix after `j`. -/
def NCPart.suffixDecode
    {n : ℕ} (j : Fin (n + 1)) (t : ℕ) : ℕ :=
  j.val + 1 + t

/-- Encoding sends suffix labels to the intrinsic coordinate range. -/
theorem NCPart.suffixEncode_mem_range_of_mem
    {n : ℕ} (j : Fin (n + 1)) {x : ℕ}
    (hx : x ∈ NCPart.suffixFinset j) :
    NCPart.suffixEncode j x ∈ range (NCPart.suffixLength j) := by
  have hx' := (NCPart.mem_suffixFinset_iff j).mp hx
  rw [mem_range]
  unfold NCPart.suffixEncode NCPart.suffixLength
  exact Nat.sub_lt_sub_right (by omega) (mem_range.mp hx'.1)

/-- Decoding sends intrinsic suffix coordinates back into the suffix finset. -/
theorem NCPart.suffixDecode_mem_of_mem_range
    {n : ℕ} (j : Fin (n + 1)) {t : ℕ}
    (ht : t ∈ range (NCPart.suffixLength j)) :
    NCPart.suffixDecode j t ∈ NCPart.suffixFinset j := by
  have htlt : t < (n + 1) - (j.val + 1) := by
    simpa [NCPart.suffixLength] using mem_range.mp ht
  have hlt : t + (j.val + 1) < n + 1 :=
    Nat.add_lt_of_lt_sub htlt
  exact
    (NCPart.mem_suffixFinset_iff j).mpr
      ⟨mem_range.mpr (by
          unfold NCPart.suffixDecode
          omega),
        by
          unfold NCPart.suffixDecode
          omega⟩

/-- Decoding after encoding recovers a suffix ambient label. -/
theorem NCPart.suffixDecode_encode_of_mem
    {n : ℕ} (j : Fin (n + 1)) {x : ℕ}
    (hx : x ∈ NCPart.suffixFinset j) :
    NCPart.suffixDecode j (NCPart.suffixEncode j x) = x := by
  have hx' := (NCPart.mem_suffixFinset_iff j).mp hx
  unfold NCPart.suffixDecode NCPart.suffixEncode
  omega

/-- Encoding after decoding recovers any suffix coordinate. -/
theorem NCPart.suffixEncode_decode
    {n : ℕ} (j : Fin (n + 1)) (t : ℕ) :
    NCPart.suffixEncode j (NCPart.suffixDecode j t) = t := by
  unfold NCPart.suffixEncode NCPart.suffixDecode
  omega

/-- Restrict a noncrossing partition to the ambient suffix after a point. -/
def NCPart.suffixFinpartition
    {n : ℕ} (π : NCPart (n + 1)) (j : Fin (n + 1)) :
    Finpartition (NCPart.suffixFinset j) :=
  π.1.restrict (by
    intro x hx
    exact (NCPart.mem_suffixFinset_iff j).mp hx |>.1)

/-- Image of an ambient finset under the suffix coordinate map. -/
def NCPart.suffixMapFinset
    {n : ℕ} (j : Fin (n + 1)) (B : Finset ℕ) : Finset ℕ :=
  B.image (NCPart.suffixEncode j)

/-- A finset contained in the suffix maps into the intrinsic suffix coordinate
range. -/
theorem NCPart.suffixMapFinset_subset_range
    {n : ℕ} (j : Fin (n + 1)) {B : Finset ℕ}
    (hB : B ⊆ NCPart.suffixFinset j) :
    NCPart.suffixMapFinset j B ⊆ range (NCPart.suffixLength j) := by
  intro t ht
  rcases mem_image.mp ht with ⟨x, hxB, rfl⟩
  exact NCPart.suffixEncode_mem_range_of_mem j (hB hxB)

/-- On finsets contained in the suffix, membership in the coordinate image is
equivalent to decoded membership in the ambient finset. -/
theorem NCPart.mem_suffixMapFinset_iff_of_subset
    {n : ℕ} (j : Fin (n + 1)) {B : Finset ℕ}
    (hB : B ⊆ NCPart.suffixFinset j) {t : ℕ} :
    t ∈ NCPart.suffixMapFinset j B ↔ NCPart.suffixDecode j t ∈ B := by
  constructor
  · intro ht
    rcases mem_image.mp ht with ⟨x, hxB, htx⟩
    have hxSuffix : x ∈ NCPart.suffixFinset j := hB hxB
    rw [← htx]
    simpa [NCPart.suffixDecode_encode_of_mem j hxSuffix] using hxB
  · intro ht
    rw [NCPart.suffixMapFinset]
    exact mem_image.mpr
      ⟨NCPart.suffixDecode j t, ht, NCPart.suffixEncode_decode j t⟩

/-- Candidate coordinate parts of the induced suffix partition. -/
def NCPart.suffixReindexedParts
    {n : ℕ} (π : NCPart (n + 1)) (j : Fin (n + 1)) :
    Finset (Finset ℕ) :=
  (π.suffixFinpartition j).parts.image (NCPart.suffixMapFinset j)

/-- Every candidate suffix coordinate part lies in the intrinsic coordinate
range. -/
theorem NCPart.suffixReindexedParts_subset_range
    {n : ℕ} (π : NCPart (n + 1)) (j : Fin (n + 1)) :
    ∀ B ∈ π.suffixReindexedParts j, B ⊆ range (NCPart.suffixLength j) := by
  intro B hB
  rcases mem_image.mp hB with ⟨C, hC, rfl⟩
  exact
    NCPart.suffixMapFinset_subset_range j
      ((π.suffixFinpartition j).le hC)

/-- Candidate suffix coordinate parts are nonempty. -/
theorem NCPart.empty_notMem_suffixReindexedParts
    {n : ℕ} (π : NCPart (n + 1)) (j : Fin (n + 1)) :
    ∅ ∉ π.suffixReindexedParts j := by
  intro hEmpty
  rcases mem_image.mp hEmpty with ⟨C, hC, hCmap⟩
  rcases (π.suffixFinpartition j).nonempty_of_mem_parts hC with ⟨x, hxC⟩
  have hxImage :
      NCPart.suffixEncode j x ∈ NCPart.suffixMapFinset j C := by
    rw [NCPart.suffixMapFinset]
    exact mem_image.mpr ⟨x, hxC, rfl⟩
  simp [hCmap] at hxImage

/-- The reindexed suffix parts cover each intrinsic coordinate exactly once. -/
theorem NCPart.existsUnique_mem_suffixReindexedParts
    {n : ℕ} (π : NCPart (n + 1)) (j : Fin (n + 1)) :
    ∀ a ∈ range (NCPart.suffixLength j),
      ∃! B, B ∈ π.suffixReindexedParts j ∧ a ∈ B := by
  intro a ha
  let x := NCPart.suffixDecode j a
  have hxSuffix : x ∈ NCPart.suffixFinset j :=
    NCPart.suffixDecode_mem_of_mem_range j ha
  have hUnique := (π.suffixFinpartition j).existsUnique_mem hxSuffix
  rcases hUnique.exists with ⟨C, hCparts, hxC⟩
  refine
    ⟨NCPart.suffixMapFinset j C,
      ⟨mem_image.mpr ⟨C, hCparts, rfl⟩, ?_⟩, ?_⟩
  · exact
      (NCPart.mem_suffixMapFinset_iff_of_subset j
        ((π.suffixFinpartition j).le hCparts)).mpr hxC
  · intro B hB
    rcases hB with ⟨hBparts, haB⟩
    rcases mem_image.mp hBparts with ⟨D, hDparts, rfl⟩
    have hxD :
        x ∈ D := by
      exact
        (NCPart.mem_suffixMapFinset_iff_of_subset j
          ((π.suffixFinpartition j).le hDparts)).mp haB
    have hDC : D = C :=
      hUnique.unique ⟨hDparts, hxD⟩ ⟨hCparts, hxC⟩
    rw [hDC]

/-- The induced suffix finpartition in intrinsic coordinates. -/
def NCPart.suffixReindexedFinpartition
    {n : ℕ} (π : NCPart (n + 1)) (j : Fin (n + 1)) :
    Finpartition (range (NCPart.suffixLength j)) :=
  Finpartition.ofExistsUnique
    (π.suffixReindexedParts j)
    (π.suffixReindexedParts_subset_range j)
    (π.existsUnique_mem_suffixReindexedParts j)
    (π.empty_notMem_suffixReindexedParts j)

@[simp]
theorem NCPart.suffixReindexedFinpartition_parts
    {n : ℕ} (π : NCPart (n + 1)) (j : Fin (n + 1)) :
    (π.suffixReindexedFinpartition j).parts = π.suffixReindexedParts j := by
  rfl

/-- The induced suffix coordinate part of a coordinate is the coordinate image
of the raw restricted part of its decoded ambient label. -/
theorem NCPart.suffixReindexedFinpartition_part_eq_map_part
    {n : ℕ} (π : NCPart (n + 1)) (j : Fin (n + 1))
    {a : ℕ} (ha : a ∈ range (NCPart.suffixLength j)) :
    (π.suffixReindexedFinpartition j).part a =
      NCPart.suffixMapFinset j
        ((π.suffixFinpartition j).part (NCPart.suffixDecode j a)) := by
  let x := NCPart.suffixDecode j a
  have hxSuffix : x ∈ NCPart.suffixFinset j :=
    NCPart.suffixDecode_mem_of_mem_range j ha
  have hPartRaw :
      (π.suffixFinpartition j).part x ∈ (π.suffixFinpartition j).parts :=
    (π.suffixFinpartition j).part_mem.mpr hxSuffix
  have hPartCoord :
      NCPart.suffixMapFinset j ((π.suffixFinpartition j).part x) ∈
        π.suffixReindexedParts j :=
    mem_image.mpr ⟨(π.suffixFinpartition j).part x, hPartRaw, rfl⟩
  have hxRaw : x ∈ (π.suffixFinpartition j).part x :=
    (π.suffixFinpartition j).mem_part hxSuffix
  have haCoord :
      a ∈ NCPart.suffixMapFinset j ((π.suffixFinpartition j).part x) := by
    exact
      (NCPart.mem_suffixMapFinset_iff_of_subset j
        ((π.suffixFinpartition j).le hPartRaw)).mpr hxRaw
  exact
    (π.suffixReindexedFinpartition j).part_eq_of_mem
      (by simpa using hPartCoord) haCoord

/-- Membership in an induced suffix coordinate part is decoded membership in
the raw restricted suffix part. -/
theorem NCPart.mem_suffixReindexedFinpartition_part_iff
    {n : ℕ} (π : NCPart (n + 1)) (j : Fin (n + 1))
    {a t : ℕ} (ha : a ∈ range (NCPart.suffixLength j)) :
    t ∈ (π.suffixReindexedFinpartition j).part a ↔
      NCPart.suffixDecode j t ∈
        (π.suffixFinpartition j).part (NCPart.suffixDecode j a) := by
  rw [π.suffixReindexedFinpartition_part_eq_map_part j ha]
  exact
    NCPart.mem_suffixMapFinset_iff_of_subset j
      ((π.suffixFinpartition j).part_subset (NCPart.suffixDecode j a))

/-- In the raw suffix restriction, the part of a suffix point is its ambient
part intersected with the suffix finset. -/
theorem NCPart.suffixFinpartition_part_eq_inter
    {n : ℕ} (π : NCPart (n + 1)) (j : Fin (n + 1))
    {x : ℕ} (hx : x ∈ NCPart.suffixFinset j) :
    (π.suffixFinpartition j).part x = π.1.part x ∩ NCPart.suffixFinset j := by
  have hxRange : x ∈ range (n + 1) :=
    (NCPart.mem_suffixFinset_iff j).mp hx |>.1
  have hAmbientPart : π.1.part x ∈ π.1.parts :=
    π.1.part_mem.mpr hxRange
  have hInterNonempty :
      π.1.part x ∩ NCPart.suffixFinset j ≠ ∅ := by
    intro hEmpty
    have hxInter :
        x ∈ π.1.part x ∩ NCPart.suffixFinset j := by
      exact mem_inter.mpr ⟨π.1.mem_part hxRange, hx⟩
    simp [hEmpty] at hxInter
  have hInterPart :
      π.1.part x ∩ NCPart.suffixFinset j ∈
        (π.suffixFinpartition j).parts := by
    unfold NCPart.suffixFinpartition
    exact mem_erase.mpr
      ⟨hInterNonempty, mem_image.mpr ⟨π.1.part x, hAmbientPart, rfl⟩⟩
  exact
    (π.suffixFinpartition j).part_eq_of_mem
      hInterPart (mem_inter.mpr ⟨π.1.mem_part hxRange, hx⟩)

/-- Membership in an induced suffix coordinate part implies decoded membership
in the corresponding ambient block. -/
theorem NCPart.suffixDecode_mem_ambient_part_of_mem_reindexed_part
    {n : ℕ} (π : NCPart (n + 1)) (j : Fin (n + 1))
    {a t : ℕ}
    (ha : a ∈ range (NCPart.suffixLength j))
    (ht : t ∈ (π.suffixReindexedFinpartition j).part a) :
    NCPart.suffixDecode j t ∈ π.1.part (NCPart.suffixDecode j a) := by
  have haSuffix : NCPart.suffixDecode j a ∈ NCPart.suffixFinset j :=
    NCPart.suffixDecode_mem_of_mem_range j ha
  have htRaw := (π.mem_suffixReindexedFinpartition_part_iff j ha).mp ht
  rw [π.suffixFinpartition_part_eq_inter j haSuffix] at htRaw
  exact (mem_inter.mp htRaw).1

/-- The induced coordinate suffix finpartition is noncrossing. -/
theorem NCPart.suffixReindexedFinpartition_nonCrossing
    {n : ℕ} (π : NCPart (n + 1)) (j : Fin (n + 1)) :
    NonCrossing (π.suffixReindexedFinpartition j) := by
  intro B₁ hB₁ B₂ hB₂ a haB₁ b hbB₂ c hcB₁ d hdB₂ hab hbc hcd
  have haRange : a ∈ range (NCPart.suffixLength j) :=
    (π.suffixReindexedFinpartition j).le hB₁ haB₁
  have hbRange : b ∈ range (NCPart.suffixLength j) :=
    (π.suffixReindexedFinpartition j).le hB₂ hbB₂
  have hcRange : c ∈ range (NCPart.suffixLength j) :=
    (π.suffixReindexedFinpartition j).le hB₁ hcB₁
  have hdRange : d ∈ range (NCPart.suffixLength j) :=
    (π.suffixReindexedFinpartition j).le hB₂ hdB₂
  have hB₁eq :
      (π.suffixReindexedFinpartition j).part a = B₁ :=
    (π.suffixReindexedFinpartition j).part_eq_of_mem hB₁ haB₁
  have hB₂eq :
      (π.suffixReindexedFinpartition j).part b = B₂ :=
    (π.suffixReindexedFinpartition j).part_eq_of_mem hB₂ hbB₂
  let A := NCPart.suffixDecode j a
  let B := NCPart.suffixDecode j b
  let C := NCPart.suffixDecode j c
  let D := NCPart.suffixDecode j d
  have hASuffix : A ∈ NCPart.suffixFinset j :=
    NCPart.suffixDecode_mem_of_mem_range j haRange
  have hBSuffix : B ∈ NCPart.suffixFinset j :=
    NCPart.suffixDecode_mem_of_mem_range j hbRange
  have hCSuffix : C ∈ NCPart.suffixFinset j :=
    NCPart.suffixDecode_mem_of_mem_range j hcRange
  have hDSuffix : D ∈ NCPart.suffixFinset j :=
    NCPart.suffixDecode_mem_of_mem_range j hdRange
  have hARange : A ∈ range (n + 1) :=
    (NCPart.mem_suffixFinset_iff j).mp hASuffix |>.1
  have hBRange : B ∈ range (n + 1) :=
    (NCPart.mem_suffixFinset_iff j).mp hBSuffix |>.1
  have hCRange : C ∈ range (n + 1) :=
    (NCPart.mem_suffixFinset_iff j).mp hCSuffix |>.1
  have hDRange : D ∈ range (n + 1) :=
    (NCPart.mem_suffixFinset_iff j).mp hDSuffix |>.1
  have hApart : π.1.part A ∈ π.1.parts := π.1.part_mem.mpr hARange
  have hBpart : π.1.part B ∈ π.1.parts := π.1.part_mem.mpr hBRange
  have hAmem : A ∈ π.1.part A := π.1.mem_part hARange
  have hBmem : B ∈ π.1.part B := π.1.mem_part hBRange
  have hCmem : C ∈ π.1.part A := by
    apply π.suffixDecode_mem_ambient_part_of_mem_reindexed_part j haRange
    simpa [hB₁eq] using hcB₁
  have hDmem : D ∈ π.1.part B := by
    apply π.suffixDecode_mem_ambient_part_of_mem_reindexed_part j hbRange
    simpa [hB₂eq] using hdB₂
  have hAB : A < B := by
    unfold A B NCPart.suffixDecode
    omega
  have hBC : B < C := by
    unfold B C NCPart.suffixDecode
    omega
  have hCD : C < D := by
    unfold C D NCPart.suffixDecode
    omega
  have hAmbient :
      π.1.part A = π.1.part B :=
    π.2 (π.1.part A) hApart (π.1.part B) hBpart
      A hAmem B hBmem C hCmem D hDmem hAB hBC hCD
  have hRawA :
      (π.suffixFinpartition j).part A =
        π.1.part A ∩ NCPart.suffixFinset j :=
    π.suffixFinpartition_part_eq_inter j hASuffix
  have hRawB :
      (π.suffixFinpartition j).part B =
        π.1.part B ∩ NCPart.suffixFinset j :=
    π.suffixFinpartition_part_eq_inter j hBSuffix
  have hPartA :
      (π.suffixReindexedFinpartition j).part a =
        NCPart.suffixMapFinset j ((π.suffixFinpartition j).part A) := by
    simpa [A] using π.suffixReindexedFinpartition_part_eq_map_part j haRange
  have hPartB :
      (π.suffixReindexedFinpartition j).part b =
        NCPart.suffixMapFinset j ((π.suffixFinpartition j).part B) := by
    simpa [B] using π.suffixReindexedFinpartition_part_eq_map_part j hbRange
  calc
    B₁ = (π.suffixReindexedFinpartition j).part a := hB₁eq.symm
    _ = NCPart.suffixMapFinset j ((π.suffixFinpartition j).part A) := hPartA
    _ = NCPart.suffixMapFinset j ((π.suffixFinpartition j).part B) := by
          rw [hRawA, hRawB, hAmbient]
    _ = (π.suffixReindexedFinpartition j).part b := hPartB.symm
    _ = B₂ := hB₂eq

/-- The induced suffix noncrossing partition in intrinsic coordinates. -/
def NCPart.suffixNCPart
    {n : ℕ} (π : NCPart (n + 1)) (j : Fin (n + 1)) :
    NCPart (NCPart.suffixLength j) :=
  ⟨π.suffixReindexedFinpartition j,
    π.suffixReindexedFinpartition_nonCrossing j⟩

@[simp]
theorem NCPart.suffixNCPart_toFinpartition
    {n : ℕ} (π : NCPart (n + 1)) (j : Fin (n + 1)) :
    (π.suffixNCPart j).1 = π.suffixReindexedFinpartition j := by
  rfl

/-- Part membership in the induced suffix `NCPart` is decoded membership in
the raw restricted suffix part. -/
theorem NCPart.mem_suffixNCPart_part_iff
    {n : ℕ} (π : NCPart (n + 1)) (j : Fin (n + 1))
    {a t : ℕ} (ha : a ∈ range (NCPart.suffixLength j)) :
    t ∈ (π.suffixNCPart j).1.part a ↔
      NCPart.suffixDecode j t ∈
        (π.suffixFinpartition j).part (NCPart.suffixDecode j a) := by
  exact π.mem_suffixReindexedFinpartition_part_iff j ha

/-- When `j` is the maximum marker of the zero block, the ambient block of any
point in the suffix after `j` is wholly contained in that suffix. -/
theorem NCPart.part_subset_suffix_interval_of_mem_suffix_of_zeroBlockMax
    {n : ℕ} (π : NCPart (n + 1)) {j x : Fin (n + 1)}
    (hjMax : π.isBlockMax j)
    (hjmem : j.val ∈ π.1.part (0 : ℕ))
    (hx : j.val < x.val) :
    ∀ y ∈ π.1.part x.val, j.val < y := by
  exact π.part_subset_suffix_interval_of_zeroBlockMax hjMax hjmem hx

/-- Under the zero-block maximum-marker hypothesis, raw suffix restricted
parts are full ambient parts. -/
theorem NCPart.suffixFinpartition_part_eq_ambient_part_of_zeroBlockMax
    {n : ℕ} (π : NCPart (n + 1)) {j : Fin (n + 1)}
    (hjMax : π.isBlockMax j)
    (hjmem : j.val ∈ π.1.part (0 : ℕ))
    {x : ℕ} (hx : x ∈ NCPart.suffixFinset j) :
    (π.suffixFinpartition j).part x = π.1.part x := by
  have hInter := π.suffixFinpartition_part_eq_inter j hx
  apply Finset.ext
  intro y
  rw [hInter, mem_inter]
  constructor
  · intro hy
    exact hy.1
  · intro hy
    have hx' := (NCPart.mem_suffixFinset_iff j).mp hx
    let xf : Fin (n + 1) := ⟨x, mem_range.mp hx'.1⟩
    have hInside :=
      π.part_subset_suffix_interval_of_mem_suffix_of_zeroBlockMax
        hjMax hjmem (x := xf) hx'.2 y hy
    have hyRange : y ∈ range (n + 1) := π.1.part_subset x hy
    exact
      ⟨hy,
        (NCPart.mem_suffixFinset_iff j).mpr
          ⟨hyRange, hInside⟩⟩

/-- Under the zero-block maximum-marker hypothesis, block-min status in the
induced suffix partition is exactly ambient block-min status. -/
theorem NCPart.suffixNCPart_isBlockMin_iff_of_zeroBlockMax
    {n : ℕ} (π : NCPart (n + 1)) {j : Fin (n + 1)}
    (hjMax : π.isBlockMax j)
    (hjmem : j.val ∈ π.1.part (0 : ℕ))
    (t : Fin (NCPart.suffixLength j)) :
    (π.suffixNCPart j).isBlockMin t ↔
      π.isBlockMin ((NCPart.suffixFinEquiv j t).1) := by
  let x := NCPart.suffixDecode j t.val
  have htSuffix : x ∈ NCPart.suffixFinset j :=
    NCPart.suffixDecode_mem_of_mem_range j (mem_range.mpr t.2)
  have hRawEq :
      (π.suffixFinpartition j).part x = π.1.part x :=
    π.suffixFinpartition_part_eq_ambient_part_of_zeroBlockMax
      hjMax hjmem htSuffix
  have hEquivVal : ((NCPart.suffixFinEquiv j t).1).val = x := by
    rfl
  constructor
  · intro hMin y hy
    have hx' := (NCPart.mem_suffixFinset_iff j).mp htSuffix
    have hyInside :=
      π.part_subset_suffix_interval_of_mem_suffix_of_zeroBlockMax
        hjMax hjmem (x := ⟨x, mem_range.mp hx'.1⟩) hx'.2 y hy
    have hySuffix : y ∈ NCPart.suffixFinset j :=
      (NCPart.mem_suffixFinset_iff j).mpr
        ⟨π.1.part_subset x hy, hyInside⟩
    have hyInduced :
        NCPart.suffixEncode j y ∈ (π.suffixNCPart j).1.part t.val := by
      exact
        (π.mem_suffixNCPart_part_iff j (mem_range.mpr t.2)).mpr
          (by
            rw [NCPart.suffixDecode_encode_of_mem j hySuffix, hRawEq]
            exact hy)
    have hCoordLe := hMin (NCPart.suffixEncode j y) hyInduced
    have hDecode := NCPart.suffixDecode_encode_of_mem j hySuffix
    rw [hEquivVal]
    unfold x NCPart.suffixDecode at hDecode ⊢
    unfold NCPart.suffixEncode at hCoordLe hDecode
    omega
  · intro hMin u hu
    have huRaw :=
      (π.mem_suffixNCPart_part_iff j (mem_range.mpr t.2)).mp hu
    rw [hRawEq] at huRaw
    have hAmbientLe :
        ((NCPart.suffixFinEquiv j t).1).val ≤ NCPart.suffixDecode j u := by
      exact hMin (NCPart.suffixDecode j u)
        (by simpa [hEquivVal] using huRaw)
    rw [hEquivVal] at hAmbientLe
    unfold x NCPart.suffixDecode at hAmbientLe
    omega

/-- Under the zero-block maximum-marker hypothesis, block-max status in the
induced suffix partition is exactly ambient block-max status. -/
theorem NCPart.suffixNCPart_isBlockMax_iff_of_zeroBlockMax
    {n : ℕ} (π : NCPart (n + 1)) {j : Fin (n + 1)}
    (hjMax : π.isBlockMax j)
    (hjmem : j.val ∈ π.1.part (0 : ℕ))
    (t : Fin (NCPart.suffixLength j)) :
    (π.suffixNCPart j).isBlockMax t ↔
      π.isBlockMax ((NCPart.suffixFinEquiv j t).1) := by
  let x := NCPart.suffixDecode j t.val
  have htSuffix : x ∈ NCPart.suffixFinset j :=
    NCPart.suffixDecode_mem_of_mem_range j (mem_range.mpr t.2)
  have hRawEq :
      (π.suffixFinpartition j).part x = π.1.part x :=
    π.suffixFinpartition_part_eq_ambient_part_of_zeroBlockMax
      hjMax hjmem htSuffix
  have hEquivVal : ((NCPart.suffixFinEquiv j t).1).val = x := by
    rfl
  constructor
  · intro hMax y hy
    have hx' := (NCPart.mem_suffixFinset_iff j).mp htSuffix
    have hyInside :=
      π.part_subset_suffix_interval_of_mem_suffix_of_zeroBlockMax
        hjMax hjmem (x := ⟨x, mem_range.mp hx'.1⟩) hx'.2 y hy
    have hySuffix : y ∈ NCPart.suffixFinset j :=
      (NCPart.mem_suffixFinset_iff j).mpr
        ⟨π.1.part_subset x hy, hyInside⟩
    have hyInduced :
        NCPart.suffixEncode j y ∈ (π.suffixNCPart j).1.part t.val := by
      exact
        (π.mem_suffixNCPart_part_iff j (mem_range.mpr t.2)).mpr
          (by
            rw [NCPart.suffixDecode_encode_of_mem j hySuffix, hRawEq]
            exact hy)
    have hCoordLe := hMax (NCPart.suffixEncode j y) hyInduced
    have hDecode := NCPart.suffixDecode_encode_of_mem j hySuffix
    rw [hEquivVal]
    unfold x NCPart.suffixDecode at hDecode ⊢
    unfold NCPart.suffixEncode at hCoordLe hDecode
    omega
  · intro hMax u hu
    have huRaw :=
      (π.mem_suffixNCPart_part_iff j (mem_range.mpr t.2)).mp hu
    rw [hRawEq] at huRaw
    have hAmbientLe :
        NCPart.suffixDecode j u ≤ ((NCPart.suffixFinEquiv j t).1).val := by
      exact hMax (NCPart.suffixDecode j u)
        (by simpa [hEquivVal] using huRaw)
    rw [hEquivVal] at hAmbientLe
    unfold x NCPart.suffixDecode at hAmbientLe
    omega

/-- Under the zero-block maximum-marker hypothesis, the induced suffix
min/max code is the ambient min/max code restricted to suffix coordinates. -/
theorem NCPart.suffixNCPart_minMaxCode_apply_eq_of_zeroBlockMax
    {n : ℕ} (π : NCPart (n + 1)) {j : Fin (n + 1)}
    (hjMax : π.isBlockMax j)
    (hjmem : j.val ∈ π.1.part (0 : ℕ))
    (t : Fin (NCPart.suffixLength j)) :
    (π.suffixNCPart j).minMaxCode t =
      π.minMaxCode ((NCPart.suffixFinEquiv j t).1) := by
  unfold NCPart.minMaxCode
  apply Prod.ext
  · exact Bool.decide_congr
      (π.suffixNCPart_isBlockMin_iff_of_zeroBlockMax hjMax hjmem t)
  · exact Bool.decide_congr
      (π.suffixNCPart_isBlockMax_iff_of_zeroBlockMax hjMax hjmem t)

/-- Equal ambient min/max codes induce equal min/max codes on the common
suffix after a zero-block maximum marker. -/
theorem NCPart.suffixNCPart_minMaxCode_eq_of_minMaxCode_eq
    {n : ℕ} {π σ : NCPart (n + 1)}
    (hcode : π.minMaxCode = σ.minMaxCode) {j : Fin (n + 1)}
    (hjmem : j.val ∈ π.1.part (0 : ℕ)) (hjMax : π.isBlockMax j) :
    (π.suffixNCPart j).minMaxCode =
      (σ.suffixNCPart j).minMaxCode := by
  have hσ :
      j.val ∈ σ.1.part (0 : ℕ) ∧ σ.isBlockMax j :=
    (π.zeroBlockMax_iff_of_minMaxCode_eq hcode j).mp ⟨hjmem, hjMax⟩
  funext t
  rw [π.suffixNCPart_minMaxCode_apply_eq_of_zeroBlockMax hjMax hjmem t,
    σ.suffixNCPart_minMaxCode_apply_eq_of_zeroBlockMax hσ.2 hσ.1 t]
  exact congrFun hcode ((NCPart.suffixFinEquiv j t).1)

/-- Equality of induced suffix `NCPart`s lifts to equality of the ambient
block of a represented suffix point. -/
theorem NCPart.part_eq_of_suffixNCPart_eq_of_zeroBlockMax
    {n : ℕ} {π σ : NCPart (n + 1)} {j k : Fin (n + 1)}
    (hjMaxπ : π.isBlockMax j)
    (hjmemπ : j.val ∈ π.1.part (0 : ℕ))
    (hjMaxσ : σ.isBlockMax j)
    (hjmemσ : j.val ∈ σ.1.part (0 : ℕ))
    (hjk : j.val < k.val)
    (hSuffixEq : π.suffixNCPart j = σ.suffixNCPart j) :
    π.1.part k.val = σ.1.part k.val := by
  have hkSuffix : k.val ∈ NCPart.suffixFinset j :=
    (NCPart.mem_suffixFinset_iff j).mpr
      ⟨mem_range.mpr k.2, hjk⟩
  let a := NCPart.suffixEncode j k.val
  have haRange : a ∈ range (NCPart.suffixLength j) :=
    NCPart.suffixEncode_mem_range_of_mem j hkSuffix
  have hDecodeA : NCPart.suffixDecode j a = k.val :=
    NCPart.suffixDecode_encode_of_mem j hkSuffix
  apply Finset.ext
  intro y
  constructor
  · intro hyπ
    have hyInside :=
      π.part_subset_suffix_interval_of_mem_suffix_of_zeroBlockMax
        hjMaxπ hjmemπ (x := k) hjk y hyπ
    have hySuffix : y ∈ NCPart.suffixFinset j :=
      (NCPart.mem_suffixFinset_iff j).mpr
        ⟨π.1.part_subset k.val hyπ, hyInside⟩
    let b := NCPart.suffixEncode j y
    have hDecodeB : NCPart.suffixDecode j b = y :=
      NCPart.suffixDecode_encode_of_mem j hySuffix
    have hRawπ :
        (π.suffixFinpartition j).part k.val = π.1.part k.val :=
      π.suffixFinpartition_part_eq_ambient_part_of_zeroBlockMax
        hjMaxπ hjmemπ hkSuffix
    have hbInducedπ :
        b ∈ (π.suffixNCPart j).1.part a := by
      exact
        (π.mem_suffixNCPart_part_iff j haRange).mpr
          (by simpa [a, b, hDecodeA, hDecodeB, hRawπ] using hyπ)
    have hbInducedσ :
        b ∈ (σ.suffixNCPart j).1.part a := by
      simpa [hSuffixEq] using hbInducedπ
    have hRawσmem :=
      (σ.mem_suffixNCPart_part_iff j haRange).mp hbInducedσ
    have hRawσ :
        (σ.suffixFinpartition j).part k.val = σ.1.part k.val :=
      σ.suffixFinpartition_part_eq_ambient_part_of_zeroBlockMax
        hjMaxσ hjmemσ hkSuffix
    simpa [a, b, hDecodeA, hDecodeB, hRawσ] using hRawσmem
  · intro hyσ
    have hyInside :=
      σ.part_subset_suffix_interval_of_mem_suffix_of_zeroBlockMax
        hjMaxσ hjmemσ (x := k) hjk y hyσ
    have hySuffix : y ∈ NCPart.suffixFinset j :=
      (NCPart.mem_suffixFinset_iff j).mpr
        ⟨σ.1.part_subset k.val hyσ, hyInside⟩
    let b := NCPart.suffixEncode j y
    have hDecodeB : NCPart.suffixDecode j b = y :=
      NCPart.suffixDecode_encode_of_mem j hySuffix
    have hRawσ :
        (σ.suffixFinpartition j).part k.val = σ.1.part k.val :=
      σ.suffixFinpartition_part_eq_ambient_part_of_zeroBlockMax
        hjMaxσ hjmemσ hkSuffix
    have hbInducedσ :
        b ∈ (σ.suffixNCPart j).1.part a := by
      exact
        (σ.mem_suffixNCPart_part_iff j haRange).mpr
          (by simpa [a, b, hDecodeA, hDecodeB, hRawσ] using hyσ)
    have hbInducedπ :
        b ∈ (π.suffixNCPart j).1.part a := by
      simpa [hSuffixEq] using hbInducedσ
    have hRawπmem :=
      (π.mem_suffixNCPart_part_iff j haRange).mp hbInducedπ
    have hRawπ :
        (π.suffixFinpartition j).part k.val = π.1.part k.val :=
      π.suffixFinpartition_part_eq_ambient_part_of_zeroBlockMax
        hjMaxπ hjmemπ hkSuffix
    simpa [a, b, hDecodeA, hDecodeB, hRawπ] using hRawπmem

/-- Image of an ambient finset under the open-gap coordinate map. -/
def NCPart.zeroBlockOpenGapMapFinset
    {n : ℕ} (i j : Fin (n + 1)) (B : Finset ℕ) : Finset ℕ :=
  B.image (NCPart.zeroBlockOpenGapEncode i j)

/-- A finset contained in the open gap maps into the intrinsic coordinate
range. -/
theorem NCPart.zeroBlockOpenGapMapFinset_subset_range
    {n : ℕ} (i j : Fin (n + 1)) {B : Finset ℕ}
    (hB : B ⊆ NCPart.zeroBlockOpenGapFinset i j) :
    NCPart.zeroBlockOpenGapMapFinset i j B ⊆
      range (NCPart.zeroBlockOpenGapLength i j) := by
  intro t ht
  rcases mem_image.mp ht with ⟨x, hxB, rfl⟩
  exact NCPart.zeroBlockOpenGapEncode_mem_range_of_mem i j (hB hxB)

/-- On finsets contained in the open gap, membership in the coordinate image is
equivalent to decoded membership in the ambient finset. -/
theorem NCPart.mem_zeroBlockOpenGapMapFinset_iff_of_subset
    {n : ℕ} (i j : Fin (n + 1)) {B : Finset ℕ}
    (hB : B ⊆ NCPart.zeroBlockOpenGapFinset i j) {t : ℕ} :
    t ∈ NCPart.zeroBlockOpenGapMapFinset i j B ↔
      NCPart.zeroBlockOpenGapDecode i j t ∈ B := by
  constructor
  · intro ht
    rcases mem_image.mp ht with ⟨x, hxB, htx⟩
    have hxGap : x ∈ NCPart.zeroBlockOpenGapFinset i j := hB hxB
    rw [← htx]
    simpa [NCPart.zeroBlockOpenGapDecode_encode_of_mem i j hxGap] using hxB
  · intro ht
    rw [NCPart.zeroBlockOpenGapMapFinset]
    exact mem_image.mpr
      ⟨NCPart.zeroBlockOpenGapDecode i j t, ht,
        NCPart.zeroBlockOpenGapEncode_decode i j t⟩

/-- Restrict a noncrossing partition to the ambient open gap between two
points.  This is the raw finpartition restriction before reindexing the gap by
`Fin (zeroBlockOpenGapLength i j)`. -/
def NCPart.zeroBlockOpenGapFinpartition
    {n : ℕ} (π : NCPart (n + 1)) (i j : Fin (n + 1)) :
    Finpartition (NCPart.zeroBlockOpenGapFinset i j) :=
  π.1.restrict (by
    intro x hx
    exact (NCPart.mem_zeroBlockOpenGapFinset_iff i j).mp hx |>.1)

/-- Candidate coordinate parts of the induced open-gap partition. -/
def NCPart.zeroBlockOpenGapReindexedParts
    {n : ℕ} (π : NCPart (n + 1)) (i j : Fin (n + 1)) :
    Finset (Finset ℕ) :=
  (π.zeroBlockOpenGapFinpartition i j).parts.image
    (NCPart.zeroBlockOpenGapMapFinset i j)

/-- Every candidate coordinate part lies in the intrinsic coordinate range. -/
theorem NCPart.zeroBlockOpenGapReindexedParts_subset_range
    {n : ℕ} (π : NCPart (n + 1)) (i j : Fin (n + 1)) :
    ∀ B ∈ π.zeroBlockOpenGapReindexedParts i j,
      B ⊆ range (NCPart.zeroBlockOpenGapLength i j) := by
  intro B hB
  rcases mem_image.mp hB with ⟨C, hC, rfl⟩
  exact
    NCPart.zeroBlockOpenGapMapFinset_subset_range i j
      ((π.zeroBlockOpenGapFinpartition i j).le hC)

/-- Candidate coordinate parts are nonempty. -/
theorem NCPart.empty_notMem_zeroBlockOpenGapReindexedParts
    {n : ℕ} (π : NCPart (n + 1)) (i j : Fin (n + 1)) :
    ∅ ∉ π.zeroBlockOpenGapReindexedParts i j := by
  intro hEmpty
  rcases mem_image.mp hEmpty with ⟨C, hC, hCmap⟩
  rcases (π.zeroBlockOpenGapFinpartition i j).nonempty_of_mem_parts hC with
    ⟨x, hxC⟩
  have hxImage :
      NCPart.zeroBlockOpenGapEncode i j x ∈
        NCPart.zeroBlockOpenGapMapFinset i j C := by
    rw [NCPart.zeroBlockOpenGapMapFinset]
    exact mem_image.mpr ⟨x, hxC, rfl⟩
  simp [hCmap] at hxImage

/-- The reindexed open-gap parts cover each intrinsic coordinate exactly once. -/
theorem NCPart.existsUnique_mem_zeroBlockOpenGapReindexedParts
    {n : ℕ} (π : NCPart (n + 1)) (i j : Fin (n + 1)) :
    ∀ a ∈ range (NCPart.zeroBlockOpenGapLength i j),
      ∃! B, B ∈ π.zeroBlockOpenGapReindexedParts i j ∧ a ∈ B := by
  intro a ha
  let x := NCPart.zeroBlockOpenGapDecode i j a
  have hxGap : x ∈ NCPart.zeroBlockOpenGapFinset i j :=
    NCPart.zeroBlockOpenGapDecode_mem_of_mem_range i j ha
  have hUnique :=
    (π.zeroBlockOpenGapFinpartition i j).existsUnique_mem hxGap
  rcases hUnique.exists with ⟨C, hCparts, hxC⟩
  refine
    ⟨NCPart.zeroBlockOpenGapMapFinset i j C,
      ⟨mem_image.mpr ⟨C, hCparts, rfl⟩, ?_⟩, ?_⟩
  · exact
      (NCPart.mem_zeroBlockOpenGapMapFinset_iff_of_subset i j
        ((π.zeroBlockOpenGapFinpartition i j).le hCparts)).mpr hxC
  · intro B hB
    rcases hB with ⟨hBparts, haB⟩
    rcases mem_image.mp hBparts with ⟨D, hDparts, rfl⟩
    have hxD :
        x ∈ D := by
      exact
        (NCPart.mem_zeroBlockOpenGapMapFinset_iff_of_subset i j
          ((π.zeroBlockOpenGapFinpartition i j).le hDparts)).mp haB
    have hDC : D = C :=
      hUnique.unique ⟨hDparts, hxD⟩ ⟨hCparts, hxC⟩
    rw [hDC]

/-- The induced open-gap finpartition in intrinsic coordinates. -/
def NCPart.zeroBlockOpenGapReindexedFinpartition
    {n : ℕ} (π : NCPart (n + 1)) (i j : Fin (n + 1)) :
    Finpartition (range (NCPart.zeroBlockOpenGapLength i j)) :=
  Finpartition.ofExistsUnique
    (π.zeroBlockOpenGapReindexedParts i j)
    (π.zeroBlockOpenGapReindexedParts_subset_range i j)
    (π.existsUnique_mem_zeroBlockOpenGapReindexedParts i j)
    (π.empty_notMem_zeroBlockOpenGapReindexedParts i j)

@[simp]
theorem NCPart.zeroBlockOpenGapReindexedFinpartition_parts
    {n : ℕ} (π : NCPart (n + 1)) (i j : Fin (n + 1)) :
    (π.zeroBlockOpenGapReindexedFinpartition i j).parts =
      π.zeroBlockOpenGapReindexedParts i j := by
  rfl

/-- The induced coordinate part of a coordinate is the coordinate image of the
raw restricted part of its decoded ambient label. -/
theorem NCPart.zeroBlockOpenGapReindexedFinpartition_part_eq_map_part
    {n : ℕ} (π : NCPart (n + 1)) (i j : Fin (n + 1))
    {a : ℕ} (ha : a ∈ range (NCPart.zeroBlockOpenGapLength i j)) :
    (π.zeroBlockOpenGapReindexedFinpartition i j).part a =
      NCPart.zeroBlockOpenGapMapFinset i j
        ((π.zeroBlockOpenGapFinpartition i j).part
          (NCPart.zeroBlockOpenGapDecode i j a)) := by
  let x := NCPart.zeroBlockOpenGapDecode i j a
  have hxGap : x ∈ NCPart.zeroBlockOpenGapFinset i j :=
    NCPart.zeroBlockOpenGapDecode_mem_of_mem_range i j ha
  have hPartRaw :
      (π.zeroBlockOpenGapFinpartition i j).part x ∈
        (π.zeroBlockOpenGapFinpartition i j).parts :=
    (π.zeroBlockOpenGapFinpartition i j).part_mem.mpr hxGap
  have hPartCoord :
      NCPart.zeroBlockOpenGapMapFinset i j
          ((π.zeroBlockOpenGapFinpartition i j).part x) ∈
        π.zeroBlockOpenGapReindexedParts i j :=
    mem_image.mpr
      ⟨(π.zeroBlockOpenGapFinpartition i j).part x, hPartRaw, rfl⟩
  have hxRaw :
      x ∈ (π.zeroBlockOpenGapFinpartition i j).part x :=
    (π.zeroBlockOpenGapFinpartition i j).mem_part hxGap
  have haCoord :
      a ∈
        NCPart.zeroBlockOpenGapMapFinset i j
          ((π.zeroBlockOpenGapFinpartition i j).part x) := by
    exact
      (NCPart.mem_zeroBlockOpenGapMapFinset_iff_of_subset i j
        ((π.zeroBlockOpenGapFinpartition i j).le hPartRaw)).mpr hxRaw
  exact
    (π.zeroBlockOpenGapReindexedFinpartition i j).part_eq_of_mem
      (by simpa using hPartCoord) haCoord

/-- Membership in an induced coordinate part is decoded membership in the raw
restricted open-gap part. -/
theorem NCPart.mem_zeroBlockOpenGapReindexedFinpartition_part_iff
    {n : ℕ} (π : NCPart (n + 1)) (i j : Fin (n + 1))
    {a t : ℕ}
    (ha : a ∈ range (NCPart.zeroBlockOpenGapLength i j)) :
    t ∈ (π.zeroBlockOpenGapReindexedFinpartition i j).part a ↔
      NCPart.zeroBlockOpenGapDecode i j t ∈
        (π.zeroBlockOpenGapFinpartition i j).part
          (NCPart.zeroBlockOpenGapDecode i j a) := by
  rw [π.zeroBlockOpenGapReindexedFinpartition_part_eq_map_part i j ha]
  exact
    NCPart.mem_zeroBlockOpenGapMapFinset_iff_of_subset i j
      ((π.zeroBlockOpenGapFinpartition i j).part_subset
        (NCPart.zeroBlockOpenGapDecode i j a))

/-- In the raw open-gap restriction, the part of an open-gap point is its
ambient part intersected with the open-gap finset. -/
theorem NCPart.zeroBlockOpenGapFinpartition_part_eq_inter
    {n : ℕ} (π : NCPart (n + 1)) (i j : Fin (n + 1))
    {x : ℕ} (hx : x ∈ NCPart.zeroBlockOpenGapFinset i j) :
    (π.zeroBlockOpenGapFinpartition i j).part x =
      π.1.part x ∩ NCPart.zeroBlockOpenGapFinset i j := by
  have hxRange : x ∈ range (n + 1) :=
    (NCPart.mem_zeroBlockOpenGapFinset_iff i j).mp hx |>.1
  have hAmbientPart : π.1.part x ∈ π.1.parts :=
    π.1.part_mem.mpr hxRange
  have hInterNonempty :
      π.1.part x ∩ NCPart.zeroBlockOpenGapFinset i j ≠ ∅ := by
    intro hEmpty
    have hxInter :
        x ∈ π.1.part x ∩ NCPart.zeroBlockOpenGapFinset i j := by
      exact mem_inter.mpr ⟨π.1.mem_part hxRange, hx⟩
    simp [hEmpty] at hxInter
  have hInterPart :
      π.1.part x ∩ NCPart.zeroBlockOpenGapFinset i j ∈
        (π.zeroBlockOpenGapFinpartition i j).parts := by
    unfold NCPart.zeroBlockOpenGapFinpartition
    exact mem_erase.mpr
      ⟨hInterNonempty, mem_image.mpr ⟨π.1.part x, hAmbientPart, rfl⟩⟩
  exact
    (π.zeroBlockOpenGapFinpartition i j).part_eq_of_mem
      hInterPart (mem_inter.mpr ⟨π.1.mem_part hxRange, hx⟩)

/-- Membership in an induced coordinate part implies decoded membership in the
corresponding ambient block. -/
theorem NCPart.zeroBlockOpenGapDecode_mem_ambient_part_of_mem_reindexed_part
    {n : ℕ} (π : NCPart (n + 1)) (i j : Fin (n + 1))
    {a t : ℕ}
    (ha : a ∈ range (NCPart.zeroBlockOpenGapLength i j))
    (ht :
      t ∈ (π.zeroBlockOpenGapReindexedFinpartition i j).part a) :
    NCPart.zeroBlockOpenGapDecode i j t ∈
      π.1.part (NCPart.zeroBlockOpenGapDecode i j a) := by
  have haGap :
      NCPart.zeroBlockOpenGapDecode i j a ∈
        NCPart.zeroBlockOpenGapFinset i j :=
    NCPart.zeroBlockOpenGapDecode_mem_of_mem_range i j ha
  have htRaw :=
    (π.mem_zeroBlockOpenGapReindexedFinpartition_part_iff i j ha).mp ht
  rw [π.zeroBlockOpenGapFinpartition_part_eq_inter i j haGap] at htRaw
  exact (mem_inter.mp htRaw).1

/-- The induced coordinate open-gap finpartition is noncrossing. -/
theorem NCPart.zeroBlockOpenGapReindexedFinpartition_nonCrossing
    {n : ℕ} (π : NCPart (n + 1)) (i j : Fin (n + 1)) :
    NonCrossing (π.zeroBlockOpenGapReindexedFinpartition i j) := by
  intro B₁ hB₁ B₂ hB₂ a haB₁ b hbB₂ c hcB₁ d hdB₂ hab hbc hcd
  let P' := π.zeroBlockOpenGapReindexedFinpartition i j
  have haRange : a ∈ range (NCPart.zeroBlockOpenGapLength i j) :=
    (π.zeroBlockOpenGapReindexedFinpartition i j).le hB₁ haB₁
  have hbRange : b ∈ range (NCPart.zeroBlockOpenGapLength i j) :=
    (π.zeroBlockOpenGapReindexedFinpartition i j).le hB₂ hbB₂
  have hcRange : c ∈ range (NCPart.zeroBlockOpenGapLength i j) :=
    (π.zeroBlockOpenGapReindexedFinpartition i j).le hB₁ hcB₁
  have hdRange : d ∈ range (NCPart.zeroBlockOpenGapLength i j) :=
    (π.zeroBlockOpenGapReindexedFinpartition i j).le hB₂ hdB₂
  have hB₁eq :
      (π.zeroBlockOpenGapReindexedFinpartition i j).part a = B₁ :=
    (π.zeroBlockOpenGapReindexedFinpartition i j).part_eq_of_mem hB₁ haB₁
  have hB₂eq :
      (π.zeroBlockOpenGapReindexedFinpartition i j).part b = B₂ :=
    (π.zeroBlockOpenGapReindexedFinpartition i j).part_eq_of_mem hB₂ hbB₂
  let A := NCPart.zeroBlockOpenGapDecode i j a
  let B := NCPart.zeroBlockOpenGapDecode i j b
  let C := NCPart.zeroBlockOpenGapDecode i j c
  let D := NCPart.zeroBlockOpenGapDecode i j d
  have hAGap : A ∈ NCPart.zeroBlockOpenGapFinset i j := by
    exact NCPart.zeroBlockOpenGapDecode_mem_of_mem_range i j haRange
  have hBGap : B ∈ NCPart.zeroBlockOpenGapFinset i j := by
    exact NCPart.zeroBlockOpenGapDecode_mem_of_mem_range i j hbRange
  have hCGAP : C ∈ NCPart.zeroBlockOpenGapFinset i j := by
    exact NCPart.zeroBlockOpenGapDecode_mem_of_mem_range i j hcRange
  have hDGap : D ∈ NCPart.zeroBlockOpenGapFinset i j := by
    exact NCPart.zeroBlockOpenGapDecode_mem_of_mem_range i j hdRange
  have hARange : A ∈ range (n + 1) :=
    (NCPart.mem_zeroBlockOpenGapFinset_iff i j).mp hAGap |>.1
  have hBRange : B ∈ range (n + 1) :=
    (NCPart.mem_zeroBlockOpenGapFinset_iff i j).mp hBGap |>.1
  have hCRange : C ∈ range (n + 1) :=
    (NCPart.mem_zeroBlockOpenGapFinset_iff i j).mp hCGAP |>.1
  have hDRange : D ∈ range (n + 1) :=
    (NCPart.mem_zeroBlockOpenGapFinset_iff i j).mp hDGap |>.1
  have hApart : π.1.part A ∈ π.1.parts := π.1.part_mem.mpr hARange
  have hBpart : π.1.part B ∈ π.1.parts := π.1.part_mem.mpr hBRange
  have hAmem : A ∈ π.1.part A := π.1.mem_part hARange
  have hBmem : B ∈ π.1.part B := π.1.mem_part hBRange
  have hCmem : C ∈ π.1.part A := by
    apply
      π.zeroBlockOpenGapDecode_mem_ambient_part_of_mem_reindexed_part i j
        haRange
    simpa [hB₁eq] using hcB₁
  have hDmem : D ∈ π.1.part B := by
    apply
      π.zeroBlockOpenGapDecode_mem_ambient_part_of_mem_reindexed_part i j
        hbRange
    simpa [hB₂eq] using hdB₂
  have hAB : A < B := by
    unfold A B NCPart.zeroBlockOpenGapDecode
    omega
  have hBC : B < C := by
    unfold B C NCPart.zeroBlockOpenGapDecode
    omega
  have hCD : C < D := by
    unfold C D NCPart.zeroBlockOpenGapDecode
    omega
  have hAmbient :
      π.1.part A = π.1.part B :=
    π.2 (π.1.part A) hApart (π.1.part B) hBpart
      A hAmem B hBmem C hCmem D hDmem hAB hBC hCD
  have hRawA :
      (π.zeroBlockOpenGapFinpartition i j).part A =
        π.1.part A ∩ NCPart.zeroBlockOpenGapFinset i j :=
    π.zeroBlockOpenGapFinpartition_part_eq_inter i j hAGap
  have hRawB :
      (π.zeroBlockOpenGapFinpartition i j).part B =
        π.1.part B ∩ NCPart.zeroBlockOpenGapFinset i j :=
    π.zeroBlockOpenGapFinpartition_part_eq_inter i j hBGap
  have hPartA :
      (π.zeroBlockOpenGapReindexedFinpartition i j).part a =
        NCPart.zeroBlockOpenGapMapFinset i j
          ((π.zeroBlockOpenGapFinpartition i j).part A) := by
    simpa [A] using
      π.zeroBlockOpenGapReindexedFinpartition_part_eq_map_part i j haRange
  have hPartB :
      (π.zeroBlockOpenGapReindexedFinpartition i j).part b =
        NCPart.zeroBlockOpenGapMapFinset i j
          ((π.zeroBlockOpenGapFinpartition i j).part B) := by
    simpa [B] using
      π.zeroBlockOpenGapReindexedFinpartition_part_eq_map_part i j hbRange
  calc
    B₁ = (π.zeroBlockOpenGapReindexedFinpartition i j).part a := hB₁eq.symm
    _ = NCPart.zeroBlockOpenGapMapFinset i j
          ((π.zeroBlockOpenGapFinpartition i j).part A) := hPartA
    _ = NCPart.zeroBlockOpenGapMapFinset i j
          ((π.zeroBlockOpenGapFinpartition i j).part B) := by
          rw [hRawA, hRawB, hAmbient]
    _ = (π.zeroBlockOpenGapReindexedFinpartition i j).part b := hPartB.symm
    _ = B₂ := hB₂eq

/-- The induced open-gap noncrossing partition in intrinsic coordinates. -/
def NCPart.zeroBlockOpenGapNCPart
    {n : ℕ} (π : NCPart (n + 1)) (i j : Fin (n + 1)) :
    NCPart (NCPart.zeroBlockOpenGapLength i j) :=
  ⟨π.zeroBlockOpenGapReindexedFinpartition i j,
    π.zeroBlockOpenGapReindexedFinpartition_nonCrossing i j⟩

@[simp]
theorem NCPart.zeroBlockOpenGapNCPart_toFinpartition
    {n : ℕ} (π : NCPart (n + 1)) (i j : Fin (n + 1)) :
    (π.zeroBlockOpenGapNCPart i j).1 =
      π.zeroBlockOpenGapReindexedFinpartition i j := by
  rfl

/-- Part membership in the induced `NCPart` is decoded membership in the raw
restricted open-gap part. -/
theorem NCPart.mem_zeroBlockOpenGapNCPart_part_iff
    {n : ℕ} (π : NCPart (n + 1)) (i j : Fin (n + 1))
    {a t : ℕ}
    (ha : a ∈ range (NCPart.zeroBlockOpenGapLength i j)) :
    t ∈ (π.zeroBlockOpenGapNCPart i j).1.part a ↔
      NCPart.zeroBlockOpenGapDecode i j t ∈
        (π.zeroBlockOpenGapFinpartition i j).part
          (NCPart.zeroBlockOpenGapDecode i j a) := by
  exact π.mem_zeroBlockOpenGapReindexedFinpartition_part_iff i j ha

/-- `i` and `j` are the consecutive zero-block gap bounds around `k`: `i` is
the last zero-block point before `k`, and `j` is the first zero-block point
after `k`. -/
def NCPart.zeroBlockGapBounds
    {n : ℕ} (π : NCPart (n + 1))
    (i j k : Fin (n + 1)) : Prop :=
  i.val ∈ π.1.part (0 : ℕ) ∧
    j.val ∈ π.1.part (0 : ℕ) ∧
      i.val < k.val ∧ k.val < j.val ∧
        (∀ z : Fin (n + 1),
          z.val ∈ π.1.part (0 : ℕ) → z.val < k.val →
            z.val ≤ i.val) ∧
          (∀ z : Fin (n + 1),
            z.val ∈ π.1.part (0 : ℕ) → k.val < z.val →
              j.val ≤ z.val) ∧
            (∀ z : Fin (n + 1),
              z.val ∈ π.1.part (0 : ℕ) →
                i.val < z.val → z.val < j.val → False)

/-- A zero-block gap-bound package has nonempty open interval length. -/
theorem NCPart.zeroBlockOpenGapLength_pos_of_zeroBlockGapBounds
    {n : ℕ} {π : NCPart (n + 1)} {i j k : Fin (n + 1)}
    (hBounds : π.zeroBlockGapBounds i j k) :
    0 < NCPart.zeroBlockOpenGapLength i j := by
  unfold NCPart.zeroBlockOpenGapLength
  have hik : i.val < k.val := hBounds.2.2.1
  have hkj : k.val < j.val := hBounds.2.2.2.1
  omega

/-- Under consecutive zero-block gap bounds, the block of any point in the gap
is wholly contained in that gap. -/
theorem NCPart.part_subset_open_interval_of_mem_zeroBlockGapBounds
    {n : ℕ} (π : NCPart (n + 1)) {i j k x : Fin (n + 1)}
    (hBounds : π.zeroBlockGapBounds i j k)
    (hx : i.val < x.val ∧ x.val < j.val) :
    ∀ y ∈ π.1.part x.val, i.val < y ∧ y < j.val := by
  rcases hBounds with ⟨himem, hjmem, _hik, _hkj, _hLeft, _hRight, hGap⟩
  have hxnot : x.val ∉ π.1.part (0 : ℕ) := by
    intro hxzero
    exact hGap x hxzero hx.1 hx.2
  exact
    π.part_subset_open_interval_of_between_zeroBlock_points
      himem hjmem hx.1 hx.2 hxnot

/-- Under consecutive zero-block gap bounds, raw restricted parts in the gap
are the same as the ambient parts. -/
theorem NCPart.zeroBlockOpenGapFinpartition_part_eq_ambient_part_of_zeroBlockGapBounds
    {n : ℕ} (π : NCPart (n + 1)) {i j k : Fin (n + 1)}
    (hBounds : π.zeroBlockGapBounds i j k) {x : ℕ}
    (hx : x ∈ NCPart.zeroBlockOpenGapFinset i j) :
    (π.zeroBlockOpenGapFinpartition i j).part x = π.1.part x := by
  have hInter :=
    π.zeroBlockOpenGapFinpartition_part_eq_inter i j hx
  apply Finset.ext
  intro y
  rw [hInter, mem_inter]
  constructor
  · intro hy
    exact hy.1
  · intro hy
    have hx' := (NCPart.mem_zeroBlockOpenGapFinset_iff i j).mp hx
    let xf : Fin (n + 1) := ⟨x, mem_range.mp hx'.1⟩
    have hInside :=
      π.part_subset_open_interval_of_mem_zeroBlockGapBounds
        hBounds (x := xf) ⟨hx'.2.1, hx'.2.2⟩ y hy
    have hyRange : y ∈ range (n + 1) := π.1.part_subset x hy
    exact
      ⟨hy,
        (NCPart.mem_zeroBlockOpenGapFinset_iff i j).mpr
          ⟨hyRange, hInside.1, hInside.2⟩⟩

/-- Under consecutive zero-block gap bounds, block-min status in the induced
gap partition is exactly ambient block-min status. -/
theorem NCPart.zeroBlockOpenGapNCPart_isBlockMin_iff_of_zeroBlockGapBounds
    {n : ℕ} (π : NCPart (n + 1)) {i j k : Fin (n + 1)}
    (hBounds : π.zeroBlockGapBounds i j k)
    (t : Fin (NCPart.zeroBlockOpenGapLength i j)) :
    (π.zeroBlockOpenGapNCPart i j).isBlockMin t ↔
      π.isBlockMin ((NCPart.zeroBlockOpenGapFinEquiv i j t).1) := by
  let x := NCPart.zeroBlockOpenGapDecode i j t.val
  have htGap : x ∈ NCPart.zeroBlockOpenGapFinset i j :=
    NCPart.zeroBlockOpenGapDecode_mem_of_mem_range i j (mem_range.mpr t.2)
  have hRawEq :
      (π.zeroBlockOpenGapFinpartition i j).part x = π.1.part x :=
    π.zeroBlockOpenGapFinpartition_part_eq_ambient_part_of_zeroBlockGapBounds
      hBounds htGap
  have hEquivVal :
      ((NCPart.zeroBlockOpenGapFinEquiv i j t).1).val = x := by
    rfl
  constructor
  · intro hMin y hy
    let yf : Fin (n + 1) := ⟨y, mem_range.mp (π.1.part_subset x hy)⟩
    have hx' := (NCPart.mem_zeroBlockOpenGapFinset_iff i j).mp htGap
    have hyInside :=
      π.part_subset_open_interval_of_mem_zeroBlockGapBounds
        hBounds (x := ⟨x, mem_range.mp hx'.1⟩)
        ⟨hx'.2.1, hx'.2.2⟩ y hy
    have hyGap : y ∈ NCPart.zeroBlockOpenGapFinset i j :=
      (NCPart.mem_zeroBlockOpenGapFinset_iff i j).mpr
        ⟨π.1.part_subset x hy, hyInside.1, hyInside.2⟩
    have hyInduced :
        NCPart.zeroBlockOpenGapEncode i j y ∈
          (π.zeroBlockOpenGapNCPart i j).1.part t.val := by
      exact
        (π.mem_zeroBlockOpenGapNCPart_part_iff i j (mem_range.mpr t.2)).mpr
          (by
            rw [NCPart.zeroBlockOpenGapDecode_encode_of_mem i j hyGap, hRawEq]
            exact hy)
    have hCoordLe := hMin (NCPart.zeroBlockOpenGapEncode i j y) hyInduced
    have hDecode :=
      NCPart.zeroBlockOpenGapDecode_encode_of_mem i j hyGap
    rw [hEquivVal]
    unfold x NCPart.zeroBlockOpenGapDecode at hDecode ⊢
    unfold NCPart.zeroBlockOpenGapEncode at hCoordLe hDecode
    omega
  · intro hMin u hu
    have huRaw :=
      (π.mem_zeroBlockOpenGapNCPart_part_iff i j (mem_range.mpr t.2)).mp hu
    rw [hRawEq] at huRaw
    have hAmbientLe :
        ((NCPart.zeroBlockOpenGapFinEquiv i j t).1).val ≤
          NCPart.zeroBlockOpenGapDecode i j u := by
      exact hMin (NCPart.zeroBlockOpenGapDecode i j u)
        (by simpa [hEquivVal] using huRaw)
    rw [hEquivVal] at hAmbientLe
    unfold x NCPart.zeroBlockOpenGapDecode at hAmbientLe
    omega

/-- Under consecutive zero-block gap bounds, block-max status in the induced
gap partition is exactly ambient block-max status. -/
theorem NCPart.zeroBlockOpenGapNCPart_isBlockMax_iff_of_zeroBlockGapBounds
    {n : ℕ} (π : NCPart (n + 1)) {i j k : Fin (n + 1)}
    (hBounds : π.zeroBlockGapBounds i j k)
    (t : Fin (NCPart.zeroBlockOpenGapLength i j)) :
    (π.zeroBlockOpenGapNCPart i j).isBlockMax t ↔
      π.isBlockMax ((NCPart.zeroBlockOpenGapFinEquiv i j t).1) := by
  let x := NCPart.zeroBlockOpenGapDecode i j t.val
  have htGap : x ∈ NCPart.zeroBlockOpenGapFinset i j :=
    NCPart.zeroBlockOpenGapDecode_mem_of_mem_range i j (mem_range.mpr t.2)
  have hRawEq :
      (π.zeroBlockOpenGapFinpartition i j).part x = π.1.part x :=
    π.zeroBlockOpenGapFinpartition_part_eq_ambient_part_of_zeroBlockGapBounds
      hBounds htGap
  have hEquivVal :
      ((NCPart.zeroBlockOpenGapFinEquiv i j t).1).val = x := by
    rfl
  constructor
  · intro hMax y hy
    let yf : Fin (n + 1) := ⟨y, mem_range.mp (π.1.part_subset x hy)⟩
    have hx' := (NCPart.mem_zeroBlockOpenGapFinset_iff i j).mp htGap
    have hyInside :=
      π.part_subset_open_interval_of_mem_zeroBlockGapBounds
        hBounds (x := ⟨x, mem_range.mp hx'.1⟩)
        ⟨hx'.2.1, hx'.2.2⟩ y hy
    have hyGap : y ∈ NCPart.zeroBlockOpenGapFinset i j :=
      (NCPart.mem_zeroBlockOpenGapFinset_iff i j).mpr
        ⟨π.1.part_subset x hy, hyInside.1, hyInside.2⟩
    have hyInduced :
        NCPart.zeroBlockOpenGapEncode i j y ∈
          (π.zeroBlockOpenGapNCPart i j).1.part t.val := by
      exact
        (π.mem_zeroBlockOpenGapNCPart_part_iff i j (mem_range.mpr t.2)).mpr
          (by
            rw [NCPart.zeroBlockOpenGapDecode_encode_of_mem i j hyGap, hRawEq]
            exact hy)
    have hCoordLe := hMax (NCPart.zeroBlockOpenGapEncode i j y) hyInduced
    have hDecode :=
      NCPart.zeroBlockOpenGapDecode_encode_of_mem i j hyGap
    rw [hEquivVal]
    unfold x NCPart.zeroBlockOpenGapDecode at hDecode ⊢
    unfold NCPart.zeroBlockOpenGapEncode at hCoordLe hDecode
    omega
  · intro hMax u hu
    have huRaw :=
      (π.mem_zeroBlockOpenGapNCPart_part_iff i j (mem_range.mpr t.2)).mp hu
    rw [hRawEq] at huRaw
    have hAmbientLe :
        NCPart.zeroBlockOpenGapDecode i j u ≤
          ((NCPart.zeroBlockOpenGapFinEquiv i j t).1).val := by
      exact hMax (NCPart.zeroBlockOpenGapDecode i j u)
        (by simpa [hEquivVal] using huRaw)
    rw [hEquivVal] at hAmbientLe
    unfold x NCPart.zeroBlockOpenGapDecode at hAmbientLe
    omega

/-- Under consecutive zero-block gap bounds, the induced gap min/max code is
the ambient min/max code restricted to the gap coordinates. -/
theorem NCPart.zeroBlockOpenGapNCPart_minMaxCode_apply_eq_of_zeroBlockGapBounds
    {n : ℕ} (π : NCPart (n + 1)) {i j k : Fin (n + 1)}
    (hBounds : π.zeroBlockGapBounds i j k)
    (t : Fin (NCPart.zeroBlockOpenGapLength i j)) :
    (π.zeroBlockOpenGapNCPart i j).minMaxCode t =
      π.minMaxCode ((NCPart.zeroBlockOpenGapFinEquiv i j t).1) := by
  unfold NCPart.minMaxCode
  apply Prod.ext
  · exact Bool.decide_congr
      (π.zeroBlockOpenGapNCPart_isBlockMin_iff_of_zeroBlockGapBounds
        hBounds t)
  · exact Bool.decide_congr
      (π.zeroBlockOpenGapNCPart_isBlockMax_iff_of_zeroBlockGapBounds
        hBounds t)

/-- The represented point of a zero-block gap-bound package lies in the
associated open-gap carrier. -/
def NCPart.point_zeroBlockOpenGapCarrier_of_zeroBlockGapBounds
    {n : ℕ} {π : NCPart (n + 1)} {i j k : Fin (n + 1)}
    (hBounds : π.zeroBlockGapBounds i j k) :
    NCPart.zeroBlockOpenGapCarrier i j :=
  ⟨k, hBounds.2.2.1, hBounds.2.2.2.1⟩

/-- A zero-block gap-bound package gives a nonempty open-gap carrier. -/
theorem NCPart.nonempty_zeroBlockOpenGapCarrier_of_zeroBlockGapBounds
    {n : ℕ} {π : NCPart (n + 1)} {i j k : Fin (n + 1)}
    (hBounds : π.zeroBlockGapBounds i j k) :
    Nonempty (NCPart.zeroBlockOpenGapCarrier i j) :=
  ⟨π.point_zeroBlockOpenGapCarrier_of_zeroBlockGapBounds hBounds⟩

/-- A point outside the zero block but before its close has adjacent zero-block
brackets: the last zero-block point before it and the first zero-block point
after it. -/
theorem NCPart.exists_zeroBlock_gap_bounds_of_not_mem_zeroBlock_of_lt_zeroBlockMaxMarker
    {n : ℕ} (π : NCPart (n + 1)) {k : Fin (n + 1)}
    (hknot : k.val ∉ π.1.part (0 : ℕ))
    (hklt : k.val < (π.zeroBlockMaxMarker).val) :
    ∃ i j : Fin (n + 1),
      i.val ∈ π.1.part (0 : ℕ) ∧
        j.val ∈ π.1.part (0 : ℕ) ∧
          i.val < k.val ∧ k.val < j.val ∧
            (∀ z : Fin (n + 1),
              z.val ∈ π.1.part (0 : ℕ) → z.val < k.val →
                z.val ≤ i.val) ∧
              (∀ z : Fin (n + 1),
                z.val ∈ π.1.part (0 : ℕ) → k.val < z.val →
                  j.val ≤ z.val) ∧
                (∀ z : Fin (n + 1),
                  z.val ∈ π.1.part (0 : ℕ) →
                    i.val < z.val → z.val < j.val → False) := by
  classical
  let Left : Finset ℕ := (π.1.part (0 : ℕ)).filter (fun z => z < k.val)
  let Right : Finset ℕ := (π.1.part (0 : ℕ)).filter (fun z => k.val < z)
  have hzeroRange : (0 : ℕ) ∈ range (n + 1) :=
    mem_range.mpr (Nat.succ_pos n)
  have hzeroMem : (0 : ℕ) ∈ π.1.part (0 : ℕ) :=
    π.1.mem_part hzeroRange
  have hkpos : 0 < k.val := by
    by_contra hknotpos
    have hkzero : k.val = 0 := Nat.eq_zero_of_not_pos hknotpos
    exact hknot (by simp [hkzero, hzeroMem])
  have hLeftNonempty : Left.Nonempty := by
    refine ⟨0, ?_⟩
    simp [Left, hzeroMem, hkpos]
  have hRightNonempty : Right.Nonempty := by
    refine ⟨(π.zeroBlockMaxMarker).val, ?_⟩
    simp [Right, π.zeroBlockMaxMarker_mem_part, hklt]
  let iNat : ℕ := Left.max' hLeftNonempty
  let jNat : ℕ := Right.min' hRightNonempty
  have hiLeft : iNat ∈ Left := Left.max'_mem hLeftNonempty
  have hjRight : jNat ∈ Right := Right.min'_mem hRightNonempty
  have hiZero : iNat ∈ π.1.part (0 : ℕ) := (Finset.mem_filter.mp hiLeft).1
  have hiLt : iNat < k.val := (Finset.mem_filter.mp hiLeft).2
  have hjZero : jNat ∈ π.1.part (0 : ℕ) := (Finset.mem_filter.mp hjRight).1
  have hkLtJ : k.val < jNat := (Finset.mem_filter.mp hjRight).2
  have hiRange : iNat ∈ range (n + 1) :=
    π.1.part_subset (0 : ℕ) hiZero
  have hjRange : jNat ∈ range (n + 1) :=
    π.1.part_subset (0 : ℕ) hjZero
  let i : Fin (n + 1) := ⟨iNat, mem_range.mp hiRange⟩
  let j : Fin (n + 1) := ⟨jNat, mem_range.mp hjRange⟩
  refine ⟨i, j, by simpa [i] using hiZero, by simpa [j] using hjZero,
    by simpa [i] using hiLt, by simpa [j] using hkLtJ, ?_, ?_, ?_⟩
  · intro z hzmem hzlt
    have hzLeft : z.val ∈ Left := by
      simp [Left, hzmem, hzlt]
    have hzle : z.val ≤ iNat := Left.le_max' z.val hzLeft
    simpa [i] using hzle
  · intro z hzmem hkz
    have hzRight : z.val ∈ Right := by
      simp [Right, hzmem, hkz]
    have hjle : jNat ≤ z.val := Right.min'_le z.val hzRight
    simpa [j] using hjle
  · intro z hzmem hiz hzj
    rcases lt_trichotomy z.val k.val with hzk | hzk | hzk
    · have hzle : z.val ≤ iNat := by
        have hzLeft : z.val ∈ Left := by
          simp [Left, hzmem, hzk]
        exact Left.le_max' z.val hzLeft
      have hiz' : iNat < z.val := by simpa [i] using hiz
      omega
    · exact hknot (by simpa [hzk] using hzmem)
    · have hjle : jNat ≤ z.val := by
        have hzRight : z.val ∈ Right := by
          simp [Right, hzmem, hzk]
        exact Right.min'_le z.val hzRight
      have hzj' : z.val < jNat := by simpa [j] using hzj
      omega

/-- Predicate-packaged form of the zero-block gap-bound construction. -/
theorem NCPart.exists_zeroBlockGapBounds_of_not_mem_zeroBlock_of_lt_zeroBlockMaxMarker
    {n : ℕ} (π : NCPart (n + 1)) {k : Fin (n + 1)}
    (hknot : k.val ∉ π.1.part (0 : ℕ))
    (hklt : k.val < (π.zeroBlockMaxMarker).val) :
    ∃ i j : Fin (n + 1), π.zeroBlockGapBounds i j k := by
  rcases
    π.exists_zeroBlock_gap_bounds_of_not_mem_zeroBlock_of_lt_zeroBlockMaxMarker
      hknot hklt with
    ⟨i, j, hi, hj, hik, hkj, hLeft, hRight, hGap⟩
  exact ⟨i, j, hi, hj, hik, hkj, hLeft, hRight, hGap⟩

/-- Equal min/max codes transport the same zero-block gap bounds. -/
theorem NCPart.zeroBlockGapBounds_of_minMaxCode_eq
    {n : ℕ} {π σ : NCPart (n + 1)}
    (hcode : π.minMaxCode = σ.minMaxCode) {i j k : Fin (n + 1)}
    (hBounds : π.zeroBlockGapBounds i j k) :
    σ.zeroBlockGapBounds i j k := by
  rcases hBounds with ⟨hi, hj, hik, hkj, hLeft, hRight, hGap⟩
  have hzero : π.1.part (0 : ℕ) = σ.1.part (0 : ℕ) :=
    π.zeroBlock_part_eq_of_minMaxCode_eq hcode
  refine ⟨?_, ?_, hik, hkj, ?_, ?_, ?_⟩
  · simpa [← hzero] using hi
  · simpa [← hzero] using hj
  · intro z hz hzlt
    exact hLeft z (by simpa [hzero] using hz) hzlt
  · intro z hz hkz
    exact hRight z (by simpa [hzero] using hz) hkz
  · intro z hz hiz hzj
    exact hGap z (by simpa [hzero] using hz) hiz hzj

/-- Equal ambient min/max codes induce equal min/max codes on a common
zero-block gap. -/
theorem NCPart.zeroBlockOpenGapNCPart_minMaxCode_eq_of_minMaxCode_eq
    {n : ℕ} {π σ : NCPart (n + 1)}
    (hcode : π.minMaxCode = σ.minMaxCode) {i j k : Fin (n + 1)}
    (hBounds : π.zeroBlockGapBounds i j k) :
    (π.zeroBlockOpenGapNCPart i j).minMaxCode =
      (σ.zeroBlockOpenGapNCPart i j).minMaxCode := by
  funext t
  rw [π.zeroBlockOpenGapNCPart_minMaxCode_apply_eq_of_zeroBlockGapBounds
      hBounds t,
    σ.zeroBlockOpenGapNCPart_minMaxCode_apply_eq_of_zeroBlockGapBounds
      (π.zeroBlockGapBounds_of_minMaxCode_eq hcode hBounds) t]
  exact congrFun hcode ((NCPart.zeroBlockOpenGapFinEquiv i j t).1)

/-- Equality of induced gap `NCPart`s lifts to equality of the ambient block of
the represented gap point. -/
theorem NCPart.part_eq_of_zeroBlockOpenGapNCPart_eq_of_zeroBlockGapBounds
    {n : ℕ} {π σ : NCPart (n + 1)} {i j k : Fin (n + 1)}
    (hBoundsπ : π.zeroBlockGapBounds i j k)
    (hBoundsσ : σ.zeroBlockGapBounds i j k)
    (hGapEq : π.zeroBlockOpenGapNCPart i j = σ.zeroBlockOpenGapNCPart i j) :
    π.1.part k.val = σ.1.part k.val := by
  have hkGap : k.val ∈ NCPart.zeroBlockOpenGapFinset i j :=
    (NCPart.mem_zeroBlockOpenGapFinset_iff i j).mpr
      ⟨mem_range.mpr k.2, hBoundsπ.2.2.1, hBoundsπ.2.2.2.1⟩
  let a := NCPart.zeroBlockOpenGapEncode i j k.val
  have haRange : a ∈ range (NCPart.zeroBlockOpenGapLength i j) :=
    NCPart.zeroBlockOpenGapEncode_mem_range_of_mem i j hkGap
  have hDecodeA :
      NCPart.zeroBlockOpenGapDecode i j a = k.val :=
    NCPart.zeroBlockOpenGapDecode_encode_of_mem i j hkGap
  apply Finset.ext
  intro y
  constructor
  · intro hyπ
    have hyInside :=
      π.part_subset_open_interval_of_mem_zeroBlockGapBounds
        hBoundsπ (x := k) ⟨hBoundsπ.2.2.1, hBoundsπ.2.2.2.1⟩ y hyπ
    have hyGap : y ∈ NCPart.zeroBlockOpenGapFinset i j :=
      (NCPart.mem_zeroBlockOpenGapFinset_iff i j).mpr
        ⟨π.1.part_subset k.val hyπ, hyInside.1, hyInside.2⟩
    let b := NCPart.zeroBlockOpenGapEncode i j y
    have hDecodeB :
        NCPart.zeroBlockOpenGapDecode i j b = y :=
      NCPart.zeroBlockOpenGapDecode_encode_of_mem i j hyGap
    have hRawπ :
        (π.zeroBlockOpenGapFinpartition i j).part k.val = π.1.part k.val :=
      π.zeroBlockOpenGapFinpartition_part_eq_ambient_part_of_zeroBlockGapBounds
        hBoundsπ hkGap
    have hbInducedπ :
        b ∈ (π.zeroBlockOpenGapNCPart i j).1.part a := by
      exact
        (π.mem_zeroBlockOpenGapNCPart_part_iff i j haRange).mpr
          (by simpa [a, b, hDecodeA, hDecodeB, hRawπ] using hyπ)
    have hbInducedσ :
        b ∈ (σ.zeroBlockOpenGapNCPart i j).1.part a := by
      simpa [hGapEq] using hbInducedπ
    have hRawσmem :=
      (σ.mem_zeroBlockOpenGapNCPart_part_iff i j haRange).mp hbInducedσ
    have hRawσ :
        (σ.zeroBlockOpenGapFinpartition i j).part k.val = σ.1.part k.val :=
      σ.zeroBlockOpenGapFinpartition_part_eq_ambient_part_of_zeroBlockGapBounds
        hBoundsσ hkGap
    simpa [a, b, hDecodeA, hDecodeB, hRawσ] using hRawσmem
  · intro hyσ
    have hyInside :=
      σ.part_subset_open_interval_of_mem_zeroBlockGapBounds
        hBoundsσ (x := k) ⟨hBoundsσ.2.2.1, hBoundsσ.2.2.2.1⟩ y hyσ
    have hyGap : y ∈ NCPart.zeroBlockOpenGapFinset i j :=
      (NCPart.mem_zeroBlockOpenGapFinset_iff i j).mpr
        ⟨σ.1.part_subset k.val hyσ, hyInside.1, hyInside.2⟩
    let b := NCPart.zeroBlockOpenGapEncode i j y
    have hDecodeB :
        NCPart.zeroBlockOpenGapDecode i j b = y :=
      NCPart.zeroBlockOpenGapDecode_encode_of_mem i j hyGap
    have hRawσ :
        (σ.zeroBlockOpenGapFinpartition i j).part k.val = σ.1.part k.val :=
      σ.zeroBlockOpenGapFinpartition_part_eq_ambient_part_of_zeroBlockGapBounds
        hBoundsσ hkGap
    have hbInducedσ :
        b ∈ (σ.zeroBlockOpenGapNCPart i j).1.part a := by
      exact
        (σ.mem_zeroBlockOpenGapNCPart_part_iff i j haRange).mpr
          (by simpa [a, b, hDecodeA, hDecodeB, hRawσ] using hyσ)
    have hbInducedπ :
        b ∈ (π.zeroBlockOpenGapNCPart i j).1.part a := by
      simpa [hGapEq] using hbInducedσ
    have hRawπmem :=
      (π.mem_zeroBlockOpenGapNCPart_part_iff i j haRange).mp hbInducedπ
    have hRawπ :
        (π.zeroBlockOpenGapFinpartition i j).part k.val = π.1.part k.val :=
      π.zeroBlockOpenGapFinpartition_part_eq_ambient_part_of_zeroBlockGapBounds
        hBoundsπ hkGap
    simpa [a, b, hDecodeA, hDecodeB, hRawπ] using hRawπmem

/-- Gap-local block reconstruction follows from min/max-code injectivity on
smaller `NCPart`s. -/
theorem NCPart.zeroBlockGap_reconstruction_of_smaller_minMaxCode_injective
    {n : ℕ}
    (hSmall :
      ∀ m : ℕ, m ≤ n → Function.Injective (NCPart.minMaxCode (n := m)))
    {π σ : NCPart (n + 1)}
    (hcode : π.minMaxCode = σ.minMaxCode) {i j k : Fin (n + 1)}
    (hBounds : π.zeroBlockGapBounds i j k) :
    π.1.part k.val = σ.1.part k.val := by
  have hGapCode :
      (π.zeroBlockOpenGapNCPart i j).minMaxCode =
        (σ.zeroBlockOpenGapNCPart i j).minMaxCode :=
    π.zeroBlockOpenGapNCPart_minMaxCode_eq_of_minMaxCode_eq hcode hBounds
  have hGapEq :
      π.zeroBlockOpenGapNCPart i j = σ.zeroBlockOpenGapNCPart i j :=
    hSmall (NCPart.zeroBlockOpenGapLength i j)
      (NCPart.zeroBlockOpenGapLength_le_n i j) hGapCode
  exact
    NCPart.part_eq_of_zeroBlockOpenGapNCPart_eq_of_zeroBlockGapBounds
      hBounds (π.zeroBlockGapBounds_of_minMaxCode_eq hcode hBounds) hGapEq

/-- Suffix-local block reconstruction follows from min/max-code injectivity on
smaller `NCPart`s. -/
theorem NCPart.suffix_reconstruction_of_smaller_minMaxCode_injective
    {n : ℕ}
    (hSmall :
      ∀ m : ℕ, m ≤ n → Function.Injective (NCPart.minMaxCode (n := m)))
    {π σ : NCPart (n + 1)}
    (hcode : π.minMaxCode = σ.minMaxCode) (k : Fin (n + 1))
    (hgt : (π.zeroBlockMaxMarker).val < k.val) :
    π.1.part k.val = σ.1.part k.val := by
  let j := π.zeroBlockMaxMarker
  have hSuffixCode :
      (π.suffixNCPart j).minMaxCode =
        (σ.suffixNCPart j).minMaxCode :=
    π.suffixNCPart_minMaxCode_eq_of_minMaxCode_eq
      hcode π.zeroBlockMaxMarker_mem_part π.zeroBlockMaxMarker_isBlockMax
  have hSuffixEq :
      π.suffixNCPart j = σ.suffixNCPart j :=
    hSmall (NCPart.suffixLength j)
      (NCPart.suffixLength_le_n j) hSuffixCode
  have hσ :
      j.val ∈ σ.1.part (0 : ℕ) ∧ σ.isBlockMax j :=
    (π.zeroBlockMax_iff_of_minMaxCode_eq hcode j).mp
      ⟨π.zeroBlockMaxMarker_mem_part, π.zeroBlockMaxMarker_isBlockMax⟩
  exact
    NCPart.part_eq_of_suffixNCPart_eq_of_zeroBlockMax
      π.zeroBlockMaxMarker_isBlockMax
      π.zeroBlockMaxMarker_mem_part
      hσ.2 hσ.1
      (by simpa [j] using hgt)
      hSuffixEq

/-- Equal min/max codes share common zero-block gap bounds around any nonzero
point before the recovered close. -/
theorem NCPart.exists_common_zeroBlockGapBounds_of_minMaxCode_eq
    {n : ℕ} {π σ : NCPart (n + 1)}
    (hcode : π.minMaxCode = σ.minMaxCode) {k : Fin (n + 1)}
    (hknot : k.val ∉ π.1.part (0 : ℕ))
    (hklt : k.val < (π.zeroBlockMaxMarker).val) :
    ∃ i j : Fin (n + 1),
      π.zeroBlockGapBounds i j k ∧ σ.zeroBlockGapBounds i j k := by
  rcases
    π.exists_zeroBlockGapBounds_of_not_mem_zeroBlock_of_lt_zeroBlockMaxMarker
      hknot hklt with
    ⟨i, j, hBounds⟩
  exact ⟨i, j, hBounds, π.zeroBlockGapBounds_of_minMaxCode_eq hcode hBounds⟩

/-- A point with zero-block gap bounds is not itself in the zero block. -/
theorem NCPart.not_mem_zeroBlock_of_zeroBlockGapBounds
    {n : ℕ} (π : NCPart (n + 1)) {i j k : Fin (n + 1)}
    (hBounds : π.zeroBlockGapBounds i j k) :
    k.val ∉ π.1.part (0 : ℕ) := by
  rcases hBounds with ⟨_hi, _hj, hik, hkj, _hLeft, _hRight, hGap⟩
  intro hkmem
  exact hGap k hkmem hik hkj

/-- A zero-block gap-bound package confines the represented block to the gap. -/
theorem NCPart.part_subset_open_interval_of_zeroBlockGapBounds
    {n : ℕ} (π : NCPart (n + 1)) {i j k : Fin (n + 1)}
    (hBounds : π.zeroBlockGapBounds i j k) :
    ∀ x ∈ π.1.part k.val, i.val < x ∧ x < j.val := by
  exact
    π.part_subset_open_interval_of_between_zeroBlock_points
      hBounds.1 hBounds.2.1 hBounds.2.2.1 hBounds.2.2.2.1
      (π.not_mem_zeroBlock_of_zeroBlockGapBounds hBounds)

/-- Reinterpret an element of a gap-confined block as a point of the open-gap
carrier. -/
def NCPart.zeroBlockOpenGapCarrierOfMemPart
    {n : ℕ} (π : NCPart (n + 1)) {i j k : Fin (n + 1)}
    (hBounds : π.zeroBlockGapBounds i j k) {x : ℕ}
    (hx : x ∈ π.1.part k.val) :
    NCPart.zeroBlockOpenGapCarrier i j :=
  let xf : Fin (n + 1) :=
    ⟨x, mem_range.mp (π.1.part_subset k.val hx)⟩
  ⟨xf, by
    have hInside :=
      π.part_subset_open_interval_of_zeroBlockGapBounds hBounds x hx
    simpa [xf] using hInside⟩

/-- The carrier point obtained from a block element has the same ambient
value. -/
theorem NCPart.zeroBlockOpenGapCarrierOfMemPart_val
    {n : ℕ} (π : NCPart (n + 1)) {i j k : Fin (n + 1)}
    (hBounds : π.zeroBlockGapBounds i j k) {x : ℕ}
    (hx : x ∈ π.1.part k.val) :
    (π.zeroBlockOpenGapCarrierOfMemPart hBounds hx).1.val = x := by
  rfl

/-- Elements of a gap-confined block lie in the corresponding open-gap finset. -/
theorem NCPart.mem_zeroBlockOpenGapFinset_of_mem_part_zeroBlockGapBounds
    {n : ℕ} (π : NCPart (n + 1)) {i j k : Fin (n + 1)}
    (hBounds : π.zeroBlockGapBounds i j k) {x : ℕ}
    (hx : x ∈ π.1.part k.val) :
    x ∈ NCPart.zeroBlockOpenGapFinset i j := by
  have hxRange : x ∈ range (n + 1) := π.1.part_subset k.val hx
  have hInside :=
    π.part_subset_open_interval_of_zeroBlockGapBounds hBounds x hx
  exact
    (NCPart.mem_zeroBlockOpenGapFinset_iff i j).mpr
      ⟨hxRange, hInside.1, hInside.2⟩

/-- A zero-block gap-bound package confines the matching block in any equal-code
partition to the same gap. -/
theorem NCPart.part_subset_open_interval_of_zeroBlockGapBounds_of_minMaxCode_eq
    {n : ℕ} {π σ : NCPart (n + 1)}
    (hcode : π.minMaxCode = σ.minMaxCode) {i j k : Fin (n + 1)}
    (hBounds : π.zeroBlockGapBounds i j k) :
    ∀ x ∈ σ.1.part k.val, i.val < x ∧ x < j.val := by
  exact
    σ.part_subset_open_interval_of_zeroBlockGapBounds
      (π.zeroBlockGapBounds_of_minMaxCode_eq hcode hBounds)

/-- Marker-level form of a zero-block gap-bound package. -/
theorem NCPart.exists_min_max_markers_open_interval_of_zeroBlockGapBounds
    {n : ℕ} (π : NCPart (n + 1)) {i j k : Fin (n + 1)}
    (hBounds : π.zeroBlockGapBounds i j k) :
    ∃ l r : Fin (n + 1),
      l.val ∈ π.1.part k.val ∧ π.isBlockMin l ∧
        r.val ∈ π.1.part k.val ∧ π.isBlockMax r ∧
          (i.val < l.val ∧ l.val < j.val) ∧
            (i.val < r.val ∧ r.val < j.val) := by
  exact
    π.exists_min_max_markers_open_interval_of_between_zeroBlock_points
      hBounds.1 hBounds.2.1 hBounds.2.2.1 hBounds.2.2.2.1
      (π.not_mem_zeroBlock_of_zeroBlockGapBounds hBounds)

/-- Marker-level form of a transported zero-block gap-bound package. -/
theorem NCPart.exists_min_max_markers_open_interval_of_zeroBlockGapBounds_of_minMaxCode_eq
    {n : ℕ} {π σ : NCPart (n + 1)}
    (hcode : π.minMaxCode = σ.minMaxCode) {i j k : Fin (n + 1)}
    (hBounds : π.zeroBlockGapBounds i j k) :
    ∃ l r : Fin (n + 1),
      l.val ∈ σ.1.part k.val ∧ σ.isBlockMin l ∧
        r.val ∈ σ.1.part k.val ∧ σ.isBlockMax r ∧
          (i.val < l.val ∧ l.val < j.val) ∧
            (i.val < r.val ∧ r.val < j.val) := by
  exact
    σ.exists_min_max_markers_open_interval_of_zeroBlockGapBounds
      (π.zeroBlockGapBounds_of_minMaxCode_eq hcode hBounds)

/-- Equal min/max codes preserve non-membership in the zero block. -/
theorem NCPart.not_mem_zeroBlock_iff_of_minMaxCode_eq
    {n : ℕ} {π σ : NCPart (n + 1)}
    (hcode : π.minMaxCode = σ.minMaxCode) (x : Fin (n + 1)) :
    x.val ∉ π.1.part (0 : ℕ) ↔ x.val ∉ σ.1.part (0 : ℕ) := by
  have hzero : π.1.part (0 : ℕ) = σ.1.part (0 : ℕ) :=
    π.zeroBlock_part_eq_of_minMaxCode_eq hcode
  constructor
  · intro hnot hxσ
    exact hnot (by simpa [hzero] using hxσ)
  · intro hnot hxπ
    exact hnot (by simpa [hzero] using hxπ)

/-- Equal min/max codes preserve the initial side of the recovered zero-block
close. -/
theorem NCPart.lt_zeroBlockMaxMarker_iff_of_minMaxCode_eq
    {n : ℕ} {π σ : NCPart (n + 1)}
    (hcode : π.minMaxCode = σ.minMaxCode) (x : Fin (n + 1)) :
    x.val < (π.zeroBlockMaxMarker).val ↔
      x.val < (σ.zeroBlockMaxMarker).val := by
  have hclose : π.zeroBlockMaxMarker = σ.zeroBlockMaxMarker :=
    π.zeroBlockMaxMarker_eq_of_minMaxCode_eq hcode
  constructor <;> intro h <;> simpa [hclose] using h

/-- Equal min/max codes preserve the suffix side of the recovered zero-block
close. -/
theorem NCPart.zeroBlockMaxMarker_lt_iff_of_minMaxCode_eq
    {n : ℕ} {π σ : NCPart (n + 1)}
    (hcode : π.minMaxCode = σ.minMaxCode) (x : Fin (n + 1)) :
    (π.zeroBlockMaxMarker).val < x.val ↔
      (σ.zeroBlockMaxMarker).val < x.val := by
  have hclose : π.zeroBlockMaxMarker = σ.zeroBlockMaxMarker :=
    π.zeroBlockMaxMarker_eq_of_minMaxCode_eq hcode
  constructor <;> intro h <;> simpa [hclose] using h

/-- If a representative is in the open initial recursive region for `π`, then
the corresponding block of any equal-code partition `σ` is also contained in
that same open initial interval. -/
theorem NCPart.part_subset_open_initial_interval_of_minMaxCode_eq
    {n : ℕ} {π σ : NCPart (n + 1)}
    (hcode : π.minMaxCode = σ.minMaxCode) {k : Fin (n + 1)}
    (hknot : k.val ∉ π.1.part (0 : ℕ))
    (hklt : k.val < (π.zeroBlockMaxMarker).val) :
    ∀ x ∈ σ.1.part k.val,
      0 < x ∧ x < (π.zeroBlockMaxMarker).val := by
  have hknotσ :
      k.val ∉ σ.1.part (0 : ℕ) :=
    (π.not_mem_zeroBlock_iff_of_minMaxCode_eq hcode k).mp hknot
  have hkltσ :
      k.val < (σ.zeroBlockMaxMarker).val :=
    (π.lt_zeroBlockMaxMarker_iff_of_minMaxCode_eq hcode k).mp hklt
  intro x hx
  have hxInsideσ :=
    σ.part_subset_open_initial_interval_of_not_mem_zeroBlock_of_lt_zeroBlockMaxMarker
      hknotσ hkltσ x hx
  have hclose : π.zeroBlockMaxMarker = σ.zeroBlockMaxMarker :=
    π.zeroBlockMaxMarker_eq_of_minMaxCode_eq hcode
  exact ⟨hxInsideσ.1, by simpa [hclose] using hxInsideσ.2⟩

/-- If a representative is in the suffix recursive region for `π`, then the
corresponding block of any equal-code partition `σ` is also contained in that
same suffix interval. -/
theorem NCPart.part_subset_suffix_interval_of_minMaxCode_eq
    {n : ℕ} {π σ : NCPart (n + 1)}
    (hcode : π.minMaxCode = σ.minMaxCode) {k : Fin (n + 1)}
    (hkgt : (π.zeroBlockMaxMarker).val < k.val) :
    ∀ x ∈ σ.1.part k.val, (π.zeroBlockMaxMarker).val < x := by
  have hkgtσ :
      (σ.zeroBlockMaxMarker).val < k.val :=
    (π.zeroBlockMaxMarker_lt_iff_of_minMaxCode_eq hcode k).mp hkgt
  intro x hx
  have hxgtσ :=
    σ.part_subset_suffix_interval_of_zeroBlockMaxMarker hkgtσ x hx
  have hclose : π.zeroBlockMaxMarker = σ.zeroBlockMaxMarker :=
    π.zeroBlockMaxMarker_eq_of_minMaxCode_eq hcode
  simpa [hclose] using hxgtσ

/-- Equal min/max codes transport confinement to a zero-block gap. -/
theorem NCPart.part_subset_open_interval_of_between_zeroBlock_points_of_minMaxCode_eq
    {n : ℕ} {π σ : NCPart (n + 1)}
    (hcode : π.minMaxCode = σ.minMaxCode) {i j k : Fin (n + 1)}
    (himem : i.val ∈ π.1.part (0 : ℕ))
    (hjmem : j.val ∈ π.1.part (0 : ℕ))
    (hik : i.val < k.val) (hkj : k.val < j.val)
    (hknot : k.val ∉ π.1.part (0 : ℕ)) :
    ∀ x ∈ σ.1.part k.val, i.val < x ∧ x < j.val := by
  have hzero : π.1.part (0 : ℕ) = σ.1.part (0 : ℕ) :=
    π.zeroBlock_part_eq_of_minMaxCode_eq hcode
  have himemσ : i.val ∈ σ.1.part (0 : ℕ) := by
    simpa [← hzero] using himem
  have hjmemσ : j.val ∈ σ.1.part (0 : ℕ) := by
    simpa [← hzero] using hjmem
  have hknotσ : k.val ∉ σ.1.part (0 : ℕ) :=
    (π.not_mem_zeroBlock_iff_of_minMaxCode_eq hcode k).mp hknot
  exact
    σ.part_subset_open_interval_of_between_zeroBlock_points
      himemσ hjmemσ hik hkj hknotσ

/-- Marker-level transported confinement to a zero-block gap. -/
theorem NCPart.exists_min_max_markers_open_interval_of_between_zeroBlock_points_of_minMaxCode_eq
    {n : ℕ} {π σ : NCPart (n + 1)}
    (hcode : π.minMaxCode = σ.minMaxCode) {i j k : Fin (n + 1)}
    (himem : i.val ∈ π.1.part (0 : ℕ))
    (hjmem : j.val ∈ π.1.part (0 : ℕ))
    (hik : i.val < k.val) (hkj : k.val < j.val)
    (hknot : k.val ∉ π.1.part (0 : ℕ)) :
    ∃ l r : Fin (n + 1),
      l.val ∈ σ.1.part k.val ∧ σ.isBlockMin l ∧
        r.val ∈ σ.1.part k.val ∧ σ.isBlockMax r ∧
          (i.val < l.val ∧ l.val < j.val) ∧
            (i.val < r.val ∧ r.val < j.val) := by
  have hzero : π.1.part (0 : ℕ) = σ.1.part (0 : ℕ) :=
    π.zeroBlock_part_eq_of_minMaxCode_eq hcode
  have himemσ : i.val ∈ σ.1.part (0 : ℕ) := by
    simpa [← hzero] using himem
  have hjmemσ : j.val ∈ σ.1.part (0 : ℕ) := by
    simpa [← hzero] using hjmem
  have hknotσ : k.val ∉ σ.1.part (0 : ℕ) :=
    (π.not_mem_zeroBlock_iff_of_minMaxCode_eq hcode k).mp hknot
  exact
    σ.exists_min_max_markers_open_interval_of_between_zeroBlock_points
      himemσ hjmemσ hik hkj hknotσ

/-- Pointwise block reconstruction is reduced to the two recursive regions:
nonzero blocks before the recovered close, and suffix blocks after it.  The
zero-block case is discharged internally by the recovered zero-block predicate. -/
theorem NCPart.forall_part_eq_of_minMaxCode_eq_of_initial_suffix
    {n : ℕ} {π σ : NCPart (n + 1)}
    (hcode : π.minMaxCode = σ.minMaxCode)
    (hInitial :
      ∀ i : Fin (n + 1),
        i.val ∉ π.1.part (0 : ℕ) →
          i.val < (π.zeroBlockMaxMarker).val →
            π.1.part i.val = σ.1.part i.val)
    (hSuffix :
      ∀ i : Fin (n + 1),
        (π.zeroBlockMaxMarker).val < i.val →
          π.1.part i.val = σ.1.part i.val) :
    ∀ i : Fin (n + 1), π.1.part i.val = σ.1.part i.val := by
  intro i
  by_cases hzero : π.zeroBlockCodeMember i
  · exact π.part_eq_of_zeroBlockCodeMember_of_minMaxCode_eq hcode hzero
  · have hinot : i.val ∉ π.1.part (0 : ℕ) := by
      intro himem
      exact hzero ((π.zeroBlockCodeMember_iff_mem_zeroBlock i).mpr himem)
    rcases π.lt_or_gt_zeroBlockMaxMarker_of_not_mem_zeroBlock hinot with hlt | hgt
    · exact hInitial i hinot hlt
    · exact hSuffix i hgt

/-- Pointwise equality of the blocks containing each point determines an
`NCPart`. -/
theorem NCPart.eq_of_forall_part_eq
    {n : ℕ} {π σ : NCPart n}
    (hpart : ∀ i : Fin n, π.1.part i.val = σ.1.part i.val) :
    π = σ := by
  apply NCPart.ext
  apply Finpartition.ext
  apply Finset.ext
  intro B
  constructor
  · intro hBπ
    rcases π.1.nonempty_of_mem_parts hBπ with ⟨x, hxB⟩
    have hxRange : x ∈ range n := π.1.subset hBπ hxB
    let i : Fin n := ⟨x, mem_range.mp hxRange⟩
    have hπpart : π.1.part i.val = B :=
      π.1.part_eq_of_mem hBπ (by
        simpa [i] using hxB)
    have hσpart : σ.1.part i.val = B :=
      (hpart i).symm.trans hπpart
    have hσmem : σ.1.part i.val ∈ σ.1.parts :=
      σ.1.part_mem.mpr (by
        simpa [i] using hxRange)
    simpa [hσpart] using hσmem
  · intro hBσ
    rcases σ.1.nonempty_of_mem_parts hBσ with ⟨x, hxB⟩
    have hxRange : x ∈ range n := σ.1.subset hBσ hxB
    let i : Fin n := ⟨x, mem_range.mp hxRange⟩
    have hσpart : σ.1.part i.val = B :=
      σ.1.part_eq_of_mem hBσ (by
        simpa [i] using hxB)
    have hπpart : π.1.part i.val = B :=
      (hpart i).trans hσpart
    have hπmem : π.1.part i.val ∈ π.1.parts :=
      π.1.part_mem.mpr (by
        simpa [i] using hxRange)
    simpa [hπpart] using hπmem

/-- To prove the min/max marker code is injective, it is enough to reconstruct
the block containing every point from that code. -/
theorem NCPart.minMaxCode_injective_of_forall_part_eq
    {n : ℕ}
    (hpart :
      ∀ {π σ : NCPart n},
        π.minMaxCode = σ.minMaxCode →
          ∀ i : Fin n, π.1.part i.val = σ.1.part i.val) :
    Function.Injective (NCPart.minMaxCode (n := n)) := by
  intro π σ hcode
  exact NCPart.eq_of_forall_part_eq (hpart hcode)

/-- The min/max code is injective once the two recursive branches reconstruct
blocks in every equal-code pair. -/
theorem NCPart.minMaxCode_injective_of_initial_suffix_reconstruction
    {n : ℕ}
    (hInitial :
      ∀ {π σ : NCPart (n + 1)},
        π.minMaxCode = σ.minMaxCode →
          ∀ i : Fin (n + 1),
            i.val ∉ π.1.part (0 : ℕ) →
              i.val < (π.zeroBlockMaxMarker).val →
                π.1.part i.val = σ.1.part i.val)
    (hSuffix :
      ∀ {π σ : NCPart (n + 1)},
        π.minMaxCode = σ.minMaxCode →
          ∀ i : Fin (n + 1),
            (π.zeroBlockMaxMarker).val < i.val →
              π.1.part i.val = σ.1.part i.val) :
    Function.Injective (NCPart.minMaxCode (n := n + 1)) := by
  apply NCPart.minMaxCode_injective_of_forall_part_eq
  intro π σ hcode
  exact π.forall_part_eq_of_minMaxCode_eq_of_initial_suffix hcode
    (fun i hinot hlt => hInitial hcode i hinot hlt)
    (fun i hgt => hSuffix hcode i hgt)

/-- Initial-region reconstruction follows from reconstruction on the
consecutive zero-block gaps. -/
theorem NCPart.initial_reconstruction_of_zeroBlockGap_reconstruction
    {n : ℕ}
    (hGap :
      ∀ {π σ : NCPart (n + 1)},
        π.minMaxCode = σ.minMaxCode →
          ∀ i j k : Fin (n + 1),
            π.zeroBlockGapBounds i j k →
              π.1.part k.val = σ.1.part k.val) :
    ∀ {π σ : NCPart (n + 1)},
      π.minMaxCode = σ.minMaxCode →
        ∀ k : Fin (n + 1),
          k.val ∉ π.1.part (0 : ℕ) →
            k.val < (π.zeroBlockMaxMarker).val →
              π.1.part k.val = σ.1.part k.val := by
  intro π σ hcode k hknot hklt
  rcases
    π.exists_zeroBlockGapBounds_of_not_mem_zeroBlock_of_lt_zeroBlockMaxMarker
      hknot hklt with
    ⟨i, j, hBounds⟩
  exact hGap hcode i j k hBounds

/-- Initial-region reconstruction follows from min/max-code injectivity on
smaller `NCPart`s. -/
theorem NCPart.initial_reconstruction_of_smaller_minMaxCode_injective
    {n : ℕ}
    (hSmall :
      ∀ m : ℕ, m ≤ n → Function.Injective (NCPart.minMaxCode (n := m))) :
    ∀ {π σ : NCPart (n + 1)},
      π.minMaxCode = σ.minMaxCode →
        ∀ k : Fin (n + 1),
          k.val ∉ π.1.part (0 : ℕ) →
            k.val < (π.zeroBlockMaxMarker).val →
              π.1.part k.val = σ.1.part k.val := by
  exact
    NCPart.initial_reconstruction_of_zeroBlockGap_reconstruction
      (fun hcode i j k hBounds =>
        NCPart.zeroBlockGap_reconstruction_of_smaller_minMaxCode_injective
          hSmall hcode hBounds)

/-- The min/max code is injective once gap-local reconstruction and suffix
reconstruction are supplied. -/
theorem NCPart.minMaxCode_injective_of_gap_suffix_reconstruction
    {n : ℕ}
    (hGap :
      ∀ {π σ : NCPart (n + 1)},
        π.minMaxCode = σ.minMaxCode →
          ∀ i j k : Fin (n + 1),
            π.zeroBlockGapBounds i j k →
              π.1.part k.val = σ.1.part k.val)
    (hSuffix :
      ∀ {π σ : NCPart (n + 1)},
        π.minMaxCode = σ.minMaxCode →
          ∀ i : Fin (n + 1),
            (π.zeroBlockMaxMarker).val < i.val →
              π.1.part i.val = σ.1.part i.val) :
    Function.Injective (NCPart.minMaxCode (n := n + 1)) := by
  exact
    NCPart.minMaxCode_injective_of_initial_suffix_reconstruction
      (NCPart.initial_reconstruction_of_zeroBlockGap_reconstruction hGap)
      hSuffix

/-- The min/max code is injective once smaller gaps are handled by induction
and the suffix branch is reconstructed. -/
theorem NCPart.minMaxCode_injective_of_smaller_gap_and_suffix_reconstruction
    {n : ℕ}
    (hSmall :
      ∀ m : ℕ, m ≤ n → Function.Injective (NCPart.minMaxCode (n := m)))
    (hSuffix :
      ∀ {π σ : NCPart (n + 1)},
        π.minMaxCode = σ.minMaxCode →
          ∀ i : Fin (n + 1),
            (π.zeroBlockMaxMarker).val < i.val →
              π.1.part i.val = σ.1.part i.val) :
    Function.Injective (NCPart.minMaxCode (n := n + 1)) := by
  exact
    NCPart.minMaxCode_injective_of_initial_suffix_reconstruction
      (NCPart.initial_reconstruction_of_smaller_minMaxCode_injective hSmall)
      hSuffix

/-- The min/max code is injective at size `n + 1` once it is injective at
all smaller sizes. -/
theorem NCPart.minMaxCode_injective_of_smaller_minMaxCode_injective
    {n : ℕ}
    (hSmall :
      ∀ m : ℕ, m ≤ n → Function.Injective (NCPart.minMaxCode (n := m))) :
    Function.Injective (NCPart.minMaxCode (n := n + 1)) := by
  exact
    NCPart.minMaxCode_injective_of_smaller_gap_and_suffix_reconstruction
      hSmall
      (fun hcode i hgt =>
        NCPart.suffix_reconstruction_of_smaller_minMaxCode_injective
          hSmall hcode i hgt)

/-- The min/max marker code is injective on noncrossing partitions. -/
theorem NCPart.minMaxCode_injective (n : ℕ) :
    Function.Injective (NCPart.minMaxCode (n := n)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          intro π σ _hcode
          apply NCPart.eq_of_forall_part_eq
          intro i
          exact Fin.elim0 i
      | succ n =>
          exact
            NCPart.minMaxCode_injective_of_smaller_minMaxCode_injective
              (fun m hm => ih m (by omega))

/-- A point is both the minimum and maximum marker of its block exactly when
that block is the singleton containing the point. -/
theorem NCPart.isBlockMin_and_isBlockMax_iff_part_singleton
    {n : ℕ} (π : NCPart n) (i : Fin n) :
    π.isBlockMin i ∧ π.isBlockMax i ↔ π.1.part i.val = {i.val} := by
  constructor
  · intro h
    apply Finset.ext
    intro x
    constructor
    · intro hx
      have hle₁ : i.val ≤ x := h.1 x hx
      have hle₂ : x ≤ i.val := h.2 x hx
      have hxval : x = i.val := by omega
      simp [hxval]
    · intro hx
      have hxval : x = i.val := by
        simpa using (Finset.mem_singleton.mp hx)
      subst x
      exact π.1.mem_part (mem_range.mpr i.2)
  · intro hsing
    constructor
    · intro x hx
      have hxval : x = i.val := by
        have : x ∈ ({i.val} : Finset ℕ) := by
          simpa [hsing] using hx
        simpa using (Finset.mem_singleton.mp this)
      omega
    · intro x hx
      have hxval : x = i.val := by
        have : x ∈ ({i.val} : Finset ℕ) := by
          simpa [hsing] using hx
        simpa using (Finset.mem_singleton.mp this)
      omega

/-- Equality of min/max marker codes preserves singleton blocks. -/
theorem NCPart.part_singleton_iff_of_minMaxCode_eq
    {n : ℕ} {π σ : NCPart n}
    (hcode : π.minMaxCode = σ.minMaxCode) (i : Fin n) :
    π.1.part i.val = {i.val} ↔ σ.1.part i.val = {i.val} := by
  rw [← π.isBlockMin_and_isBlockMax_iff_part_singleton i,
    ← σ.isBlockMin_and_isBlockMax_iff_part_singleton i]
  constructor
  · intro h
    exact
      ⟨(π.isBlockMin_iff_of_minMaxCode_eq hcode i).mp h.1,
        (π.isBlockMax_iff_of_minMaxCode_eq hcode i).mp h.2⟩
  · intro h
    exact
      ⟨(π.isBlockMin_iff_of_minMaxCode_eq hcode i).mpr h.1,
        (π.isBlockMax_iff_of_minMaxCode_eq hcode i).mpr h.2⟩

/-- If the min/max block-marker code is injective, then the number of
non-crossing partitions is at most `4^n`. -/
theorem card_NCPart_le_four_pow_of_minMaxCode_injective
    {n : ℕ}
    (hInjective : Function.Injective (NCPart.minMaxCode (n := n))) :
    Fintype.card (NCPart n) ≤ 4 ^ n := by
  have hcard :
      Fintype.card (NCPart n) ≤ Fintype.card (Fin n → Bool × Bool) :=
    Fintype.card_le_of_embedding
      ⟨NCPart.minMaxCode, hInjective⟩
  exact hcard.trans (by simp [Fintype.card_prod])

/-- Symbolic Catalan-scale bound from the min/max-code injection. -/
theorem card_NCPart_le_four_pow (n : ℕ) :
    Fintype.card (NCPart n) ≤ 4 ^ n := by
  exact
    card_NCPart_le_four_pow_of_minMaxCode_injective
      (NCPart.minMaxCode_injective n)

/-- Count-facing version of the gap/suffix reconstruction reduction. -/
theorem card_NCPart_succ_le_four_pow_of_gap_suffix_reconstruction
    {n : ℕ}
    (hGap :
      ∀ {π σ : NCPart (n + 1)},
        π.minMaxCode = σ.minMaxCode →
          ∀ i j k : Fin (n + 1),
            π.zeroBlockGapBounds i j k →
              π.1.part k.val = σ.1.part k.val)
    (hSuffix :
      ∀ {π σ : NCPart (n + 1)},
        π.minMaxCode = σ.minMaxCode →
          ∀ i : Fin (n + 1),
            (π.zeroBlockMaxMarker).val < i.val →
              π.1.part i.val = σ.1.part i.val) :
    Fintype.card (NCPart (n + 1)) ≤ 4 ^ (n + 1) := by
  exact
    card_NCPart_le_four_pow_of_minMaxCode_injective
      (NCPart.minMaxCode_injective_of_gap_suffix_reconstruction hGap hSuffix)

/-- `|NC(0)| = 1 = Catalan 0`. -/
theorem card_NCPart_zero : Fintype.card (NCPart 0) = 1 := by
  native_decide

/-- `|NC(1)| = 1 = Catalan 1`. -/
theorem card_NCPart_one : Fintype.card (NCPart 1) = 1 := by
  native_decide

/-- `|NC(2)| = 2 = Catalan 2`. -/
theorem card_NCPart_two : Fintype.card (NCPart 2) = 2 := by
  native_decide

/-- `|NC(3)| = 5 = Catalan 3`. -/
theorem card_NCPart_three : Fintype.card (NCPart 3) = 5 := by
  native_decide

/-- `|NC(4)| = 14 = Catalan 4`. -/
theorem card_NCPart_four : Fintype.card (NCPart 4) = 14 := by
  native_decide

/-! **Catalan card lemmas for `n = 5, 6, 7`** have been moved to
`NCPartitionHeavyCard.lean` (not in the main import graph) because each
`native_decide` enumerates `Finpartition (range n)` — at `n = 7` this
alone costs ~11 min wall time and pushes memory past 1 GB per
invocation.  Keeping them isolated lets downstream files rebuild without
re-paying that cost. -/

-- ═══════════════════════════════════════════════════════════════════
-- §4. Block sizes and Kreweras counts
-- ═══════════════════════════════════════════════════════════════════

/-- Multiset of block sizes of a non-crossing partition.
    The moment–cumulant sum groups NC partitions by this multiset. -/
def NCPart.blockSizes {n : ℕ} (π : NCPart n) : Multiset ℕ :=
  π.1.parts.val.map Finset.card

-- Kreweras: `|NC(n, μ)| = (n! / (n − k + 1)!) / ∏ mⱼ!` where `μ ⊢ n`, `k`
-- is the number of parts, and `mⱼ` the multiplicity of the j-th distinct
-- part.  The theorems below are verified by `native_decide` enumeration
-- of `NCPart n`.

/-- `|NC(1, (1))| = 1`. -/
theorem kreweras_1_1 :
    Fintype.card {π : NCPart 1 // π.blockSizes = ({1} : Multiset ℕ)} = 1 := by
  native_decide

/-- `|NC(2, (2))| = 1`. -/
theorem kreweras_2_2 :
    Fintype.card {π : NCPart 2 // π.blockSizes = ({2} : Multiset ℕ)} = 1 := by
  native_decide

/-- `|NC(2, (1,1))| = 1`. -/
theorem kreweras_2_1_1 :
    Fintype.card {π : NCPart 2 // π.blockSizes = ({1, 1} : Multiset ℕ)} = 1 := by
  native_decide

/-- `|NC(3, (3))| = 1`. -/
theorem kreweras_3_3 :
    Fintype.card {π : NCPart 3 // π.blockSizes = ({3} : Multiset ℕ)} = 1 := by
  native_decide

/-- `|NC(3, (2,1))| = 3`. -/
theorem kreweras_3_2_1 :
    Fintype.card {π : NCPart 3 // π.blockSizes = ({2, 1} : Multiset ℕ)} = 3 := by
  native_decide

/-- `|NC(3, (1,1,1))| = 1`. -/
theorem kreweras_3_1_1_1 :
    Fintype.card {π : NCPart 3 // π.blockSizes = ({1, 1, 1} : Multiset ℕ)} = 1 := by
  native_decide

/-- `|NC(4, (4))| = 1`. -/
theorem kreweras_4_4 :
    Fintype.card {π : NCPart 4 // π.blockSizes = ({4} : Multiset ℕ)} = 1 := by
  native_decide

/-- `|NC(4, (3,1))| = 4`. -/
theorem kreweras_4_3_1 :
    Fintype.card {π : NCPart 4 // π.blockSizes = ({3, 1} : Multiset ℕ)} = 4 := by
  native_decide

/-- `|NC(4, (2,2))| = 2`. -/
theorem kreweras_4_2_2 :
    Fintype.card {π : NCPart 4 // π.blockSizes = ({2, 2} : Multiset ℕ)} = 2 := by
  native_decide

/-- `|NC(4, (2,1,1))| = 6`. -/
theorem kreweras_4_2_1_1 :
    Fintype.card {π : NCPart 4 // π.blockSizes = ({2, 1, 1} : Multiset ℕ)} = 6 := by
  native_decide

/-- `|NC(4, (1,1,1,1))| = 1`. -/
theorem kreweras_4_1_1_1_1 :
    Fintype.card {π : NCPart 4 // π.blockSizes = ({1, 1, 1, 1} : Multiset ℕ)} = 1 := by
  native_decide

/-! **Scope note.** Kreweras lemmas for `n ≥ 5` would need ~7 + 11 + 15 = 33
additional `native_decide` invocations.  Each enumerates a subtype of
`NCPart n` whose underlying Finpartition space is large (for `n = 7`,
`Bell(7) = 877` finpartitions before filtering by non-crossing).  In
practice this exhausted 16 GB of RAM + 44 GB swap on a laptop.  Left as
future work; see the module docstring for alternatives (e.g. splitting
into a separate file that is not in the main `PptFactorization` import
graph, or proving Kreweras symbolically from a recursive decomposition). -/

end NCPartition
