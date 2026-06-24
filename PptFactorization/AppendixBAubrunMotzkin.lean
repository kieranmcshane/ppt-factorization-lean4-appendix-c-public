import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
import PptFactorization.AppendixBTightFiberPackageEndpoint

/-!
# Motzkin checkpoint for the Aubrun zero-defect frontier

The current zero-defect audit predicts that the simultaneous-geodesic class has
Motzkin size.  This file records the small, kernel-checked Motzkin arithmetic
needed by the `m = 7` no-go checkpoint: `M₈ = 323`, hence `M₈ > 2^8`.
-/

open scoped BigOperators

namespace PptFactorization
namespace AppendixB

/-- A permutation is an involution, i.e. all non-fixed points form
transposition arcs. -/
def isInvolutionPerm {n : ℕ} (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ i : Fin n, π (π i) = i

/-- Linear noncrossing condition for permutation arcs.

For ordered arcs `(a,b)` and `(c,d)` with `a<c<b<d`, the two arcs are not both
present.  Together with `isInvolutionPerm`, this is the usual model of a
noncrossing partial matching on a linearly ordered finite set. -/
def isLinearNoncrossingPerm {n : ℕ} (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ a b c d : Fin n,
    a.1 < b.1 → c.1 < d.1 → a.1 < c.1 → c.1 < b.1 → b.1 < d.1 →
      ¬ (π a = b ∧ π c = d)

instance isInvolutionPerm_decidable {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Decidable (isInvolutionPerm π) := by
  unfold isInvolutionPerm
  infer_instance

instance isLinearNoncrossingPerm_decidable {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Decidable (isLinearNoncrossingPerm π) := by
  unfold isLinearNoncrossingPerm
  infer_instance

/-- Noncrossing partial matchings represented as involutive permutations with
noncrossing arcs. -/
def LinearNoncrossingMatchingPerm (n : ℕ) :=
  {π : Equiv.Perm (Fin n) // isInvolutionPerm π ∧ isLinearNoncrossingPerm π}

instance (n : ℕ) : Fintype (LinearNoncrossingMatchingPerm n) := by
  unfold LinearNoncrossingMatchingPerm
  infer_instance

/-- If `0` is matched to `b` in an involution, then `b` is matched back to
`0`. -/
theorem isInvolutionPerm_first_pair_partner_zero
    {n : ℕ} {π : Equiv.Perm (Fin (n + 1))}
    (hinv : isInvolutionPerm π) {b : Fin (n + 1)}
    (hb : π 0 = b) :
    π b = 0 := by
  calc
    π b = π (π 0) := by rw [hb]
    _ = 0 := hinv 0

/-- If the first vertex is matched to `b`, then no vertex strictly between
`0` and `b` can be matched to the right of `b`.  This is the interval-closure
half of the Motzkin first-return decomposition. -/
theorem isLinearNoncrossingPerm_first_pair_left_interval_closed
    {n : ℕ} {π : Equiv.Perm (Fin (n + 1))}
    (hnc : isLinearNoncrossingPerm π)
    {b c : Fin (n + 1)}
    (hb : π 0 = b) (h0b : 0 < b.1) (h0c : 0 < c.1) (hcb : c.1 < b.1) :
    (π c).1 < b.1 := by
  by_contra hnot
  have hbπc : b.1 < (π c).1 := by
    have hne : (π c).1 ≠ b.1 := by
      intro hval
      have hπeq : π c = b := Fin.ext hval
      have hc0 : c = 0 := π.injective (by simpa [hb] using hπeq)
      have : c.1 = 0 := congrArg Fin.val hc0
      omega
    omega
  have hcπc : c.1 < (π c).1 := by
    omega
  have hbad := hnc 0 b c (π c) h0b hcπc h0c hcb hbπc
  exact hbad ⟨hb, rfl⟩

/-- If the first vertex is matched to `b`, then no vertex to the right of `b`
can be matched into the interval `[0,b]`.  Together with the previous lemma,
this is the interval decomposition needed for the Motzkin recurrence. -/
theorem isLinearNoncrossingPerm_first_pair_right_interval_closed
    {n : ℕ} {π : Equiv.Perm (Fin (n + 1))}
    (hinv : isInvolutionPerm π) (hnc : isLinearNoncrossingPerm π)
    {b c : Fin (n + 1)}
    (hb : π 0 = b) (h0b : 0 < b.1) (hbc : b.1 < c.1) :
    b.1 < (π c).1 := by
  have hπb : π b = 0 :=
    isInvolutionPerm_first_pair_partner_zero hinv hb
  by_contra hnot
  have hπc_ne_b : (π c).1 ≠ b.1 := by
    intro hval
    have hπeq : π c = b := Fin.ext hval
    have hc0 : c = 0 := π.injective (by simpa [hb] using hπeq)
    have : c.1 = 0 := congrArg Fin.val hc0
    omega
  have hπc_le_b : (π c).1 ≤ b.1 := by
    omega
  by_cases hπc0 : (π c).1 = 0
  · have hπeq0 : π c = 0 := Fin.ext hπc0
    have hcb : c = b := π.injective (by simpa [hπb] using hπeq0)
    have : c.1 = b.1 := congrArg Fin.val hcb
    omega
  · have h0πc : 0 < (π c).1 := by
      omega
    have hπc_lt_b : (π c).1 < b.1 := by
      omega
    have hclosed :=
      isLinearNoncrossingPerm_first_pair_left_interval_closed
        (π := π) hnc hb h0b h0πc hπc_lt_b
    have hcc : (π (π c)).1 = c.1 := by
      rw [hinv c]
    omega

/-- If `0` is matched to `b`, then the open interval `(0,b)` is closed under
the matching.  This is the left recursive block in the Motzkin first-return
decomposition. -/
theorem isLinearNoncrossingPerm_first_pair_middle_interval_closed
    {n : ℕ} {π : Equiv.Perm (Fin (n + 1))}
    (hinv : isInvolutionPerm π) (hnc : isLinearNoncrossingPerm π)
    {b c : Fin (n + 1)}
    (hb : π 0 = b) (h0b : 0 < b.1) (h0c : 0 < c.1) (hcb : c.1 < b.1) :
    0 < (π c).1 ∧ (π c).1 < b.1 := by
  have hπb : π b = 0 :=
    isInvolutionPerm_first_pair_partner_zero hinv hb
  constructor
  · by_contra hnot
    have hπc0val : (π c).1 = 0 := Nat.eq_zero_of_not_pos hnot
    have hπc0 : π c = 0 := Fin.ext hπc0val
    have hcb' : c = b := π.injective (by simpa [hπb] using hπc0)
    have : c.1 = b.1 := congrArg Fin.val hcb'
    omega
  · exact isLinearNoncrossingPerm_first_pair_left_interval_closed
      (π := π) hnc hb h0b h0c hcb

/-- If the first vertex is fixed, then the positive tail is closed under the
matching.  This is the fixed-point branch of the Motzkin first-return
decomposition. -/
theorem isInvolutionPerm_first_fixed_tail_closed
    {n : ℕ} {π : Equiv.Perm (Fin (n + 1))}
    {c : Fin (n + 1)} (h0 : π 0 = 0) (h0c : 0 < c.1) :
    0 < (π c).1 := by
  by_contra hnot
  have hπc0val : (π c).1 = 0 := Nat.eq_zero_of_not_pos hnot
  have hπc0 : π c = 0 := Fin.ext hπc0val
  have hc0 : c = 0 := π.injective (by simpa [h0] using hπc0)
  have : c.1 = 0 := congrArg Fin.val hc0
  omega

/-- The open interval between the first vertex and its positive partner. -/
def FirstPairMiddleBlock {n : ℕ} (b : Fin (n + 1)) :=
  {c : Fin (n + 1) // 0 < c.1 ∧ c.1 < b.1}

/-- The right block after the positive partner of the first vertex. -/
def FirstPairRightBlock {n : ℕ} (b : Fin (n + 1)) :=
  {c : Fin (n + 1) // b.1 < c.1}

instance {n : ℕ} (b : Fin (n + 1)) : Fintype (FirstPairMiddleBlock b) := by
  unfold FirstPairMiddleBlock
  infer_instance

instance {n : ℕ} (b : Fin (n + 1)) : Fintype (FirstPairRightBlock b) := by
  unfold FirstPairRightBlock
  infer_instance

/-- The middle block `(0,b)` has the natural coordinates `0,...,b-2`. -/
def firstPairMiddleBlockEquivFin
    {n : ℕ} (b : Fin (n + 1)) :
    FirstPairMiddleBlock b ≃ Fin (b.1 - 1) where
  toFun := fun c =>
    ⟨c.1.1 - 1, by
      have h0c := c.2.1
      have hcb := c.2.2
      omega⟩
  invFun := fun i =>
    ⟨⟨i.1 + 1, by
        have hib := i.2
        have hb := b.2
        omega⟩,
      by
        constructor
        · change 0 < i.1 + 1
          omega
        · have hib := i.2
          change i.1 + 1 < b.1
          omega⟩
  left_inv := by
    intro c
    apply Subtype.ext
    apply Fin.ext
    have h0c := c.2.1
    change (c.1.1 - 1) + 1 = c.1.1
    omega
  right_inv := by
    intro i
    apply Fin.ext
    change (i.1 + 1) - 1 = i.1
    omega

/-- Cardinality of the middle block in the paired first-return branch. -/
theorem card_firstPairMiddleBlock
    {n : ℕ} (b : Fin (n + 1)) :
    Fintype.card (FirstPairMiddleBlock b) = b.1 - 1 := by
  rw [Fintype.card_congr (firstPairMiddleBlockEquivFin b), Fintype.card_fin]

/-- The right block after `b` has the natural coordinates `0,...,n-b-1`. -/
def firstPairRightBlockEquivFin
    {n : ℕ} (b : Fin (n + 1)) :
    FirstPairRightBlock b ≃ Fin (n - b.1) where
  toFun := fun c =>
    ⟨c.1.1 - (b.1 + 1), by
      have hbc := c.2
      have hc := c.1.2
      omega⟩
  invFun := fun i =>
    ⟨⟨b.1 + 1 + i.1, by
        have hi := i.2
        have hb := b.2
        omega⟩,
      by
        change b.1 < b.1 + 1 + i.1
        omega⟩
  left_inv := by
    intro c
    apply Subtype.ext
    apply Fin.ext
    have hbc := c.2
    change b.1 + 1 + (c.1.1 - (b.1 + 1)) = c.1.1
    omega
  right_inv := by
    intro i
    apply Fin.ext
    change b.1 + 1 + i.1 - (b.1 + 1) = i.1
    omega

/-- Cardinality of the right block in the paired first-return branch. -/
theorem card_firstPairRightBlock
    {n : ℕ} (b : Fin (n + 1)) :
    Fintype.card (FirstPairRightBlock b) = n - b.1 := by
  rw [Fintype.card_congr (firstPairRightBlockEquivFin b), Fintype.card_fin]

/-- Canonical inclusion of the middle paired block back into the ambient
finite interval. -/
def firstPairMiddleEmbed
    {n : ℕ} (b : Fin (n + 1)) (i : Fin (b.1 - 1)) :
    Fin (n + 1) :=
  ((firstPairMiddleBlockEquivFin b).symm i).1

@[simp] theorem firstPairMiddleEmbed_val
    {n : ℕ} (b : Fin (n + 1)) (i : Fin (b.1 - 1)) :
    (firstPairMiddleEmbed b i).1 = i.1 + 1 := by
  rfl

theorem firstPairMiddleEmbed_pos
    {n : ℕ} (b : Fin (n + 1)) (i : Fin (b.1 - 1)) :
    0 < (firstPairMiddleEmbed b i).1 := by
  rw [firstPairMiddleEmbed_val]
  omega

theorem firstPairMiddleEmbed_lt_partner
    {n : ℕ} (b : Fin (n + 1)) (i : Fin (b.1 - 1)) :
    (firstPairMiddleEmbed b i).1 < b.1 := by
  exact ((firstPairMiddleBlockEquivFin b).symm i).2.2

theorem firstPairMiddleEmbed_ne_zero
    {n : ℕ} (b : Fin (n + 1)) (i : Fin (b.1 - 1)) :
    firstPairMiddleEmbed b i ≠ 0 := by
  intro h
  have hpos := firstPairMiddleEmbed_pos b i
  exact (Nat.ne_of_gt hpos) (by simpa using congrArg Fin.val h)

theorem firstPairMiddleEmbed_ne_partner
    {n : ℕ} (b : Fin (n + 1)) (i : Fin (b.1 - 1)) :
    firstPairMiddleEmbed b i ≠ b := by
  intro h
  have hval := congrArg Fin.val h
  have hlt := firstPairMiddleEmbed_lt_partner b i
  omega

theorem firstPairMiddleEmbed_lt_iff
    {n : ℕ} (b : Fin (n + 1)) (i j : Fin (b.1 - 1)) :
    (firstPairMiddleEmbed b i).1 < (firstPairMiddleEmbed b j).1 ↔ i.1 < j.1 := by
  constructor
  · intro h
    change i.1 + 1 < j.1 + 1 at h
    omega
  · intro h
    change i.1 + 1 < j.1 + 1
    omega

/-- Canonical inclusion of the right paired block back into the ambient finite
interval. -/
def firstPairRightEmbed
    {n : ℕ} (b : Fin (n + 1)) (i : Fin (n - b.1)) :
    Fin (n + 1) :=
  ((firstPairRightBlockEquivFin b).symm i).1

@[simp] theorem firstPairRightEmbed_val
    {n : ℕ} (b : Fin (n + 1)) (i : Fin (n - b.1)) :
    (firstPairRightEmbed b i).1 = b.1 + 1 + i.1 := by
  rfl

theorem firstPairRightEmbed_partner_lt
    {n : ℕ} (b : Fin (n + 1)) (i : Fin (n - b.1)) :
    b.1 < (firstPairRightEmbed b i).1 := by
  exact ((firstPairRightBlockEquivFin b).symm i).2

theorem firstPairRightEmbed_ne_zero
    {n : ℕ} (b : Fin (n + 1)) (i : Fin (n - b.1)) :
    firstPairRightEmbed b i ≠ 0 := by
  intro h
  have hlt := firstPairRightEmbed_partner_lt b i
  have hpos : 0 < (firstPairRightEmbed b i).1 := by omega
  exact (Nat.ne_of_gt hpos) (by simpa using congrArg Fin.val h)

theorem firstPairRightEmbed_ne_partner
    {n : ℕ} (b : Fin (n + 1)) (i : Fin (n - b.1)) :
    firstPairRightEmbed b i ≠ b := by
  intro h
  have hval := congrArg Fin.val h
  have hlt := firstPairRightEmbed_partner_lt b i
  omega

theorem firstPairRightEmbed_lt_iff
    {n : ℕ} (b : Fin (n + 1)) (i j : Fin (n - b.1)) :
    (firstPairRightEmbed b i).1 < (firstPairRightEmbed b j).1 ↔ i.1 < j.1 := by
  constructor
  · intro h
    change b.1 + 1 + i.1 < b.1 + 1 + j.1 at h
    omega
  · intro h
    change b.1 + 1 + i.1 < b.1 + 1 + j.1
    omega

/-- Function-level paired extension.  It swaps `0` with its positive partner
`b`, uses `τ` on the middle block `(0,b)`, and uses `υ` on the right block. -/
def firstPairExtendFun
    {n : ℕ} (b : Fin (n + 1))
    (τ : Equiv.Perm (Fin (b.1 - 1))) (υ : Equiv.Perm (Fin (n - b.1))) :
    Fin (n + 1) → Fin (n + 1) := fun i =>
  if hzero : i = 0 then b
  else if hpartner : i = b then 0
  else if hmid : 0 < i.1 ∧ i.1 < b.1 then
    firstPairMiddleEmbed b
      (τ ((firstPairMiddleBlockEquivFin b) ⟨i, hmid⟩))
  else
    firstPairRightEmbed b
      (υ ((firstPairRightBlockEquivFin b) ⟨i, by
        have hi_ne_zero_val : i.1 ≠ 0 := by
          intro hi
          exact hzero (Fin.ext hi)
        have hi_pos : 0 < i.1 := Nat.pos_of_ne_zero hi_ne_zero_val
        have hnot_lt : ¬ i.1 < b.1 := by
          intro hlt
          exact hmid ⟨hi_pos, hlt⟩
        have hb_le_i : b.1 ≤ i.1 := le_of_not_gt hnot_lt
        have hne_val : i.1 ≠ b.1 := by
          intro hval
          exact hpartner (Fin.ext hval)
        omega⟩))

@[simp] theorem firstPairExtendFun_zero
    {n : ℕ} (b : Fin (n + 1))
    (τ : Equiv.Perm (Fin (b.1 - 1))) (υ : Equiv.Perm (Fin (n - b.1))) :
    firstPairExtendFun b τ υ 0 = b := by
  simp [firstPairExtendFun]

@[simp] theorem firstPairExtendFun_partner
    {n : ℕ} (b : Fin (n + 1))
    (τ : Equiv.Perm (Fin (b.1 - 1))) (υ : Equiv.Perm (Fin (n - b.1)))
    (h0b : 0 < b.1) :
    firstPairExtendFun b τ υ b = 0 := by
  have hb_ne_zero : b ≠ 0 := by
    intro h
    exact (Nat.ne_of_gt h0b) (by simpa using congrArg Fin.val h)
  simp [firstPairExtendFun, hb_ne_zero]

theorem firstPairExtendFun_middle
    {n : ℕ} (b : Fin (n + 1))
    (τ : Equiv.Perm (Fin (b.1 - 1))) (υ : Equiv.Perm (Fin (n - b.1)))
    (i : Fin (b.1 - 1)) :
    firstPairExtendFun b τ υ (firstPairMiddleEmbed b i) =
      firstPairMiddleEmbed b (τ i) := by
  have hne0 := firstPairMiddleEmbed_ne_zero b i
  have hneb := firstPairMiddleEmbed_ne_partner b i
  have hmid :
      0 < (firstPairMiddleEmbed b i).1 ∧
        (firstPairMiddleEmbed b i).1 < b.1 :=
    ⟨firstPairMiddleEmbed_pos b i, firstPairMiddleEmbed_lt_partner b i⟩
  have hcoord :
      (firstPairMiddleBlockEquivFin b)
        ⟨firstPairMiddleEmbed b i, hmid⟩ = i := by
    change (firstPairMiddleBlockEquivFin b)
      ((firstPairMiddleBlockEquivFin b).symm i) = i
    simp
  have hnot_right : ¬ b.1 ≤ (firstPairMiddleEmbed b i).1 := by
    intro hle
    have hlt := firstPairMiddleEmbed_lt_partner b i
    omega
  simp [firstPairExtendFun, hne0, hneb, hcoord]
  intro hle
  exfalso
  exact hnot_right (by simpa [firstPairMiddleEmbed_val] using hle)

theorem firstPairExtendFun_right
    {n : ℕ} (b : Fin (n + 1))
    (τ : Equiv.Perm (Fin (b.1 - 1))) (υ : Equiv.Perm (Fin (n - b.1)))
    (i : Fin (n - b.1)) :
    firstPairExtendFun b τ υ (firstPairRightEmbed b i) =
      firstPairRightEmbed b (υ i) := by
  have hne0 := firstPairRightEmbed_ne_zero b i
  have hneb := firstPairRightEmbed_ne_partner b i
  have hnotmid :
      ¬ (0 < (firstPairRightEmbed b i).1 ∧
        (firstPairRightEmbed b i).1 < b.1) := by
    intro hmid
    have hgt := firstPairRightEmbed_partner_lt b i
    omega
  have hnot_middle_lt : ¬ (firstPairRightEmbed b i).1 < b.1 := by
    intro hlt
    have hgt := firstPairRightEmbed_partner_lt b i
    omega
  have hcoord :
      (firstPairRightBlockEquivFin b)
        ⟨firstPairRightEmbed b i, firstPairRightEmbed_partner_lt b i⟩ = i := by
    change (firstPairRightBlockEquivFin b)
      ((firstPairRightBlockEquivFin b).symm i) = i
    simp
  simp [firstPairExtendFun, hne0, hneb, hcoord]
  intro hlt
  exfalso
  exact hnot_middle_lt (by simpa [firstPairRightEmbed_val] using hlt)

/-- Converting a middle-block point to canonical coordinates and embedding it
back recovers the original ambient point. -/
theorem firstPairMiddleEmbed_equiv_apply
    {n : ℕ} (b : Fin (n + 1)) (c : FirstPairMiddleBlock b) :
    firstPairMiddleEmbed b (firstPairMiddleBlockEquivFin b c) = c.1 := by
  unfold firstPairMiddleEmbed
  simp

/-- Converting a right-block point to canonical coordinates and embedding it
back recovers the original ambient point. -/
theorem firstPairRightEmbed_equiv_apply
    {n : ℕ} (b : Fin (n + 1)) (c : FirstPairRightBlock b) :
    firstPairRightEmbed b (firstPairRightBlockEquivFin b c) = c.1 := by
  unfold firstPairRightEmbed
  simp

/-- Applying the inverse paired extension after the paired extension recovers
the input point. -/
theorem firstPairExtendFun_left_inv
    {n : ℕ} (b : Fin (n + 1)) (h0b : 0 < b.1)
    (τ : Equiv.Perm (Fin (b.1 - 1))) (υ : Equiv.Perm (Fin (n - b.1))) :
    Function.LeftInverse
      (firstPairExtendFun b τ.symm υ.symm)
      (firstPairExtendFun b τ υ) := by
  intro x
  by_cases hzero : x = 0
  · subst x
    rw [firstPairExtendFun_zero, firstPairExtendFun_partner]
    exact h0b
  · by_cases hpartner : x = b
    · subst x
      rw [firstPairExtendFun_partner, firstPairExtendFun_zero]
      exact h0b
    · by_cases hmid : 0 < x.1 ∧ x.1 < b.1
      · let i : Fin (b.1 - 1) := firstPairMiddleBlockEquivFin b ⟨x, hmid⟩
        have hx : firstPairMiddleEmbed b i = x :=
          firstPairMiddleEmbed_equiv_apply b ⟨x, hmid⟩
        calc
          firstPairExtendFun b τ.symm υ.symm (firstPairExtendFun b τ υ x) =
              firstPairExtendFun b τ.symm υ.symm
                (firstPairMiddleEmbed b (τ i)) := by
                rw [← hx, firstPairExtendFun_middle]
          _ = firstPairMiddleEmbed b (τ.symm (τ i)) := by
                rw [firstPairExtendFun_middle]
          _ = x := by
                simpa [hx]
      · have hi_ne_zero_val : x.1 ≠ 0 := by
          intro hx0
          exact hzero (Fin.ext hx0)
        have hi_pos : 0 < x.1 := Nat.pos_of_ne_zero hi_ne_zero_val
        have hnot_lt : ¬ x.1 < b.1 := by
          intro hlt
          exact hmid ⟨hi_pos, hlt⟩
        have hb_le_x : b.1 ≤ x.1 := le_of_not_gt hnot_lt
        have hne_val : x.1 ≠ b.1 := by
          intro hval
          exact hpartner (Fin.ext hval)
        have hright : b.1 < x.1 := by omega
        let i : Fin (n - b.1) := firstPairRightBlockEquivFin b ⟨x, hright⟩
        have hx : firstPairRightEmbed b i = x :=
          firstPairRightEmbed_equiv_apply b ⟨x, hright⟩
        calc
          firstPairExtendFun b τ.symm υ.symm (firstPairExtendFun b τ υ x) =
              firstPairExtendFun b τ.symm υ.symm
                (firstPairRightEmbed b (υ i)) := by
                rw [← hx, firstPairExtendFun_right]
          _ = firstPairRightEmbed b (υ.symm (υ i)) := by
                rw [firstPairExtendFun_right]
          _ = x := by
                simpa [hx]

/-- Applying the paired extension after its inverse recovers the input point. -/
theorem firstPairExtendFun_right_inv
    {n : ℕ} (b : Fin (n + 1)) (h0b : 0 < b.1)
    (τ : Equiv.Perm (Fin (b.1 - 1))) (υ : Equiv.Perm (Fin (n - b.1))) :
    Function.RightInverse
      (firstPairExtendFun b τ.symm υ.symm)
      (firstPairExtendFun b τ υ) := by
  intro x
  exact firstPairExtendFun_left_inv b h0b τ.symm υ.symm x

/-- Permutation-level paired extension.  It is the inverse construction to the
middle/right restriction branch of the Motzkin first-return decomposition. -/
def firstPairExtendPerm
    {n : ℕ} (b : Fin (n + 1)) (h0b : 0 < b.1)
    (τ : Equiv.Perm (Fin (b.1 - 1))) (υ : Equiv.Perm (Fin (n - b.1))) :
    Equiv.Perm (Fin (n + 1)) where
  toFun := firstPairExtendFun b τ υ
  invFun := firstPairExtendFun b τ.symm υ.symm
  left_inv := firstPairExtendFun_left_inv b h0b τ υ
  right_inv := firstPairExtendFun_right_inv b h0b τ υ

@[simp] theorem firstPairExtendPerm_zero
    {n : ℕ} (b : Fin (n + 1)) (h0b : 0 < b.1)
    (τ : Equiv.Perm (Fin (b.1 - 1))) (υ : Equiv.Perm (Fin (n - b.1))) :
    firstPairExtendPerm b h0b τ υ 0 = b := by
  rfl

@[simp] theorem firstPairExtendPerm_partner
    {n : ℕ} (b : Fin (n + 1)) (h0b : 0 < b.1)
    (τ : Equiv.Perm (Fin (b.1 - 1))) (υ : Equiv.Perm (Fin (n - b.1))) :
    firstPairExtendPerm b h0b τ υ b = 0 := by
  exact firstPairExtendFun_partner b τ υ h0b

theorem firstPairExtendPerm_middle
    {n : ℕ} (b : Fin (n + 1)) (h0b : 0 < b.1)
    (τ : Equiv.Perm (Fin (b.1 - 1))) (υ : Equiv.Perm (Fin (n - b.1)))
    (i : Fin (b.1 - 1)) :
    firstPairExtendPerm b h0b τ υ (firstPairMiddleEmbed b i) =
      firstPairMiddleEmbed b (τ i) :=
  firstPairExtendFun_middle b τ υ i

theorem firstPairExtendPerm_right
    {n : ℕ} (b : Fin (n + 1)) (h0b : 0 < b.1)
    (τ : Equiv.Perm (Fin (b.1 - 1))) (υ : Equiv.Perm (Fin (n - b.1)))
    (i : Fin (n - b.1)) :
    firstPairExtendPerm b h0b τ υ (firstPairRightEmbed b i) =
      firstPairRightEmbed b (υ i) :=
  firstPairExtendFun_right b τ υ i

/-- The paired extension preserves the open middle interval `(0,b)`. -/
theorem firstPairExtendPerm_middle_interval
    {n : ℕ} (b : Fin (n + 1)) (h0b : 0 < b.1)
    (τ : Equiv.Perm (Fin (b.1 - 1))) (υ : Equiv.Perm (Fin (n - b.1)))
    {x : Fin (n + 1)} (hmid : 0 < x.1 ∧ x.1 < b.1) :
    0 < (firstPairExtendPerm b h0b τ υ x).1 ∧
      (firstPairExtendPerm b h0b τ υ x).1 < b.1 := by
  let i : Fin (b.1 - 1) := firstPairMiddleBlockEquivFin b ⟨x, hmid⟩
  have hx : firstPairMiddleEmbed b i = x :=
    firstPairMiddleEmbed_equiv_apply b ⟨x, hmid⟩
  rw [← hx, firstPairExtendPerm_middle]
  exact ⟨firstPairMiddleEmbed_pos b (τ i),
    firstPairMiddleEmbed_lt_partner b (τ i)⟩

/-- The paired extension preserves the right interval after `b`. -/
theorem firstPairExtendPerm_right_interval
    {n : ℕ} (b : Fin (n + 1)) (h0b : 0 < b.1)
    (τ : Equiv.Perm (Fin (b.1 - 1))) (υ : Equiv.Perm (Fin (n - b.1)))
    {x : Fin (n + 1)} (hright : b.1 < x.1) :
    b.1 < (firstPairExtendPerm b h0b τ υ x).1 := by
  let i : Fin (n - b.1) := firstPairRightBlockEquivFin b ⟨x, hright⟩
  have hx : firstPairRightEmbed b i = x :=
    firstPairRightEmbed_equiv_apply b ⟨x, hright⟩
  rw [← hx, firstPairExtendPerm_right]
  exact firstPairRightEmbed_partner_lt b (υ i)

/-- If the two recursive factors are involutions, then the paired extension is
also an involution. -/
theorem firstPairExtendPerm_isInvolutionPerm
    {n : ℕ} (b : Fin (n + 1)) (h0b : 0 < b.1)
    {τ : Equiv.Perm (Fin (b.1 - 1))} {υ : Equiv.Perm (Fin (n - b.1))}
    (hτ : isInvolutionPerm τ) (hυ : isInvolutionPerm υ) :
    isInvolutionPerm (firstPairExtendPerm b h0b τ υ) := by
  intro x
  by_cases hzero : x = 0
  · subst x
    rw [firstPairExtendPerm_zero, firstPairExtendPerm_partner]
  · by_cases hpartner : x = b
    · subst x
      rw [firstPairExtendPerm_partner, firstPairExtendPerm_zero]
    · by_cases hmid : 0 < x.1 ∧ x.1 < b.1
      · let i : Fin (b.1 - 1) := firstPairMiddleBlockEquivFin b ⟨x, hmid⟩
        have hx : firstPairMiddleEmbed b i = x :=
          firstPairMiddleEmbed_equiv_apply b ⟨x, hmid⟩
        calc
          firstPairExtendPerm b h0b τ υ
              (firstPairExtendPerm b h0b τ υ x) =
              firstPairExtendPerm b h0b τ υ
                (firstPairMiddleEmbed b (τ i)) := by
                rw [← hx, firstPairExtendPerm_middle]
          _ = firstPairMiddleEmbed b (τ (τ i)) := by
                rw [firstPairExtendPerm_middle]
          _ = x := by
                rw [hτ i, hx]
      · have hi_ne_zero_val : x.1 ≠ 0 := by
          intro hx0
          exact hzero (Fin.ext hx0)
        have hi_pos : 0 < x.1 := Nat.pos_of_ne_zero hi_ne_zero_val
        have hnot_lt : ¬ x.1 < b.1 := by
          intro hlt
          exact hmid ⟨hi_pos, hlt⟩
        have hb_le_x : b.1 ≤ x.1 := le_of_not_gt hnot_lt
        have hne_val : x.1 ≠ b.1 := by
          intro hval
          exact hpartner (Fin.ext hval)
        have hright : b.1 < x.1 := by omega
        let i : Fin (n - b.1) := firstPairRightBlockEquivFin b ⟨x, hright⟩
        have hx : firstPairRightEmbed b i = x :=
          firstPairRightEmbed_equiv_apply b ⟨x, hright⟩
        calc
          firstPairExtendPerm b h0b τ υ
              (firstPairExtendPerm b h0b τ υ x) =
              firstPairExtendPerm b h0b τ υ
                (firstPairRightEmbed b (υ i)) := by
                rw [← hx, firstPairExtendPerm_right]
          _ = firstPairRightEmbed b (υ (υ i)) := by
                rw [firstPairExtendPerm_right]
          _ = x := by
                rw [hυ i, hx]

/-- The paired extension preserves linear noncrossing. -/
theorem firstPairExtendPerm_isLinearNoncrossingPerm
    {n : ℕ} (p : Fin (n + 1)) (h0p : 0 < p.1)
    {τ : Equiv.Perm (Fin (p.1 - 1))} {υ : Equiv.Perm (Fin (n - p.1))}
    (hτ : isLinearNoncrossingPerm τ) (hυ : isLinearNoncrossingPerm υ) :
    isLinearNoncrossingPerm (firstPairExtendPerm p h0p τ υ) := by
  intro a b c d hab hcd hac hcb hbd hbad
  by_cases ha0 : a = 0
  · subst a
    have hb_eq : b = p := by
      simpa using hbad.1.symm
    subst b
    have hcmid : 0 < c.1 ∧ c.1 < p.1 := ⟨hac, hcb⟩
    have hd_mid :=
      firstPairExtendPerm_middle_interval p h0p τ υ hcmid
    rw [hbad.2] at hd_mid
    omega
  · by_cases hap : a = p
    · subst a
      have hb_eq : b = 0 := by
        simpa using hbad.1.symm
      subst b
      exact (Nat.not_lt_zero p.1) (by simpa using hab)
    · by_cases hamid : 0 < a.1 ∧ a.1 < p.1
      · let ia : Fin (p.1 - 1) := firstPairMiddleBlockEquivFin p ⟨a, hamid⟩
        have ha_eq : firstPairMiddleEmbed p ia = a :=
          firstPairMiddleEmbed_equiv_apply p ⟨a, hamid⟩
        have hb_eq : b = firstPairMiddleEmbed p (τ ia) := by
          have h := hbad.1
          rw [← ha_eq, firstPairExtendPerm_middle] at h
          exact h.symm
        have hb_lt_p : b.1 < p.1 := by
          rw [hb_eq]
          exact firstPairMiddleEmbed_lt_partner p (τ ia)
        have hcmid : 0 < c.1 ∧ c.1 < p.1 := by
          constructor <;> omega
        let ic : Fin (p.1 - 1) := firstPairMiddleBlockEquivFin p ⟨c, hcmid⟩
        have hc_eq : firstPairMiddleEmbed p ic = c :=
          firstPairMiddleEmbed_equiv_apply p ⟨c, hcmid⟩
        have hd_eq : d = firstPairMiddleEmbed p (τ ic) := by
          have h := hbad.2
          rw [← hc_eq, firstPairExtendPerm_middle] at h
          exact h.symm
        have habEmb :
            (firstPairMiddleEmbed p ia).1 <
              (firstPairMiddleEmbed p (τ ia)).1 := by
          rw [ha_eq, ← hb_eq]
          exact hab
        have hcdEmb :
            (firstPairMiddleEmbed p ic).1 <
              (firstPairMiddleEmbed p (τ ic)).1 := by
          rw [hc_eq, ← hd_eq]
          exact hcd
        have hacEmb :
            (firstPairMiddleEmbed p ia).1 <
              (firstPairMiddleEmbed p ic).1 := by
          rw [ha_eq, hc_eq]
          exact hac
        have hcbEmb :
            (firstPairMiddleEmbed p ic).1 <
              (firstPairMiddleEmbed p (τ ia)).1 := by
          rw [hc_eq, ← hb_eq]
          exact hcb
        have hbdEmb :
            (firstPairMiddleEmbed p (τ ia)).1 <
              (firstPairMiddleEmbed p (τ ic)).1 := by
          rw [← hb_eq, ← hd_eq]
          exact hbd
        exact
          (hτ ia (τ ia) ic (τ ic)
            ((firstPairMiddleEmbed_lt_iff p ia (τ ia)).mp habEmb)
            ((firstPairMiddleEmbed_lt_iff p ic (τ ic)).mp hcdEmb)
            ((firstPairMiddleEmbed_lt_iff p ia ic).mp hacEmb)
            ((firstPairMiddleEmbed_lt_iff p ic (τ ia)).mp hcbEmb)
            ((firstPairMiddleEmbed_lt_iff p (τ ia) (τ ic)).mp hbdEmb))
            ⟨rfl, rfl⟩
      · have ha_ne_zero_val : a.1 ≠ 0 := by
          intro ha
          exact ha0 (Fin.ext ha)
        have ha_pos : 0 < a.1 := Nat.pos_of_ne_zero ha_ne_zero_val
        have hnot_lt : ¬ a.1 < p.1 := by
          intro hlt
          exact hamid ⟨ha_pos, hlt⟩
        have hp_le_a : p.1 ≤ a.1 := le_of_not_gt hnot_lt
        have ha_ne_p_val : a.1 ≠ p.1 := by
          intro hval
          exact hap (Fin.ext hval)
        have haright : p.1 < a.1 := by omega
        let ia : Fin (n - p.1) := firstPairRightBlockEquivFin p ⟨a, haright⟩
        have ha_eq : firstPairRightEmbed p ia = a :=
          firstPairRightEmbed_equiv_apply p ⟨a, haright⟩
        have hb_eq : b = firstPairRightEmbed p (υ ia) := by
          have h := hbad.1
          rw [← ha_eq, firstPairExtendPerm_right] at h
          exact h.symm
        have hcright : p.1 < c.1 := by omega
        let ic : Fin (n - p.1) := firstPairRightBlockEquivFin p ⟨c, hcright⟩
        have hc_eq : firstPairRightEmbed p ic = c :=
          firstPairRightEmbed_equiv_apply p ⟨c, hcright⟩
        have hd_eq : d = firstPairRightEmbed p (υ ic) := by
          have h := hbad.2
          rw [← hc_eq, firstPairExtendPerm_right] at h
          exact h.symm
        have habEmb :
            (firstPairRightEmbed p ia).1 <
              (firstPairRightEmbed p (υ ia)).1 := by
          rw [ha_eq, ← hb_eq]
          exact hab
        have hcdEmb :
            (firstPairRightEmbed p ic).1 <
              (firstPairRightEmbed p (υ ic)).1 := by
          rw [hc_eq, ← hd_eq]
          exact hcd
        have hacEmb :
            (firstPairRightEmbed p ia).1 <
              (firstPairRightEmbed p ic).1 := by
          rw [ha_eq, hc_eq]
          exact hac
        have hcbEmb :
            (firstPairRightEmbed p ic).1 <
              (firstPairRightEmbed p (υ ia)).1 := by
          rw [hc_eq, ← hb_eq]
          exact hcb
        have hbdEmb :
            (firstPairRightEmbed p (υ ia)).1 <
              (firstPairRightEmbed p (υ ic)).1 := by
          rw [← hb_eq, ← hd_eq]
          exact hbd
        exact
          (hυ ia (υ ia) ic (υ ic)
            ((firstPairRightEmbed_lt_iff p ia (υ ia)).mp habEmb)
            ((firstPairRightEmbed_lt_iff p ic (υ ic)).mp hcdEmb)
            ((firstPairRightEmbed_lt_iff p ia ic).mp hacEmb)
            ((firstPairRightEmbed_lt_iff p ic (υ ia)).mp hcbEmb)
            ((firstPairRightEmbed_lt_iff p (υ ia) (υ ic)).mp hbdEmb))
            ⟨rfl, rfl⟩

/-- Matching-level paired extension branch of the Motzkin first-return
decomposition. -/
def firstPairExtendMatching
    {n : ℕ} (b : Fin (n + 1)) (h0b : 0 < b.1)
    (τ : LinearNoncrossingMatchingPerm (b.1 - 1))
    (υ : LinearNoncrossingMatchingPerm (n - b.1)) :
    LinearNoncrossingMatchingPerm (n + 1) :=
  ⟨firstPairExtendPerm b h0b τ.1 υ.1,
    firstPairExtendPerm_isInvolutionPerm b h0b τ.2.1 υ.2.1,
    firstPairExtendPerm_isLinearNoncrossingPerm b h0b τ.2.2 υ.2.2⟩

/-- Transport a permutation across an equivalence. -/
def transportPerm {α β : Type*} (e : α ≃ β) (σ : Equiv.Perm α) :
    Equiv.Perm β :=
  (e.symm.trans σ).trans e

/-- Transporting an involution across an equivalence preserves involutivity. -/
theorem transportPerm_isInvolutionPerm
    {α β : Type*} (e : α ≃ β) {σ : Equiv.Perm α}
    (hinv : ∀ a : α, σ (σ a) = a) :
    ∀ b : β, transportPerm e σ (transportPerm e σ b) = b := by
  intro b
  simp [transportPerm, hinv]

/-- Restriction of a noncrossing matching to the middle block `(0,b)` when
`0` is matched to a positive partner `b`. -/
def firstPairMiddlePerm
    {n : ℕ} {π : Equiv.Perm (Fin (n + 1))}
    (hinv : isInvolutionPerm π) (hnc : isLinearNoncrossingPerm π)
    {b : Fin (n + 1)} (hb : π 0 = b) (h0b : 0 < b.1) :
    Equiv.Perm (FirstPairMiddleBlock b) where
  toFun := fun c =>
    ⟨π c.1,
      isLinearNoncrossingPerm_first_pair_middle_interval_closed
        (π := π) hinv hnc hb h0b c.2.1 c.2.2⟩
  invFun := fun c =>
    ⟨π c.1,
      isLinearNoncrossingPerm_first_pair_middle_interval_closed
        (π := π) hinv hnc hb h0b c.2.1 c.2.2⟩
  left_inv := by
    intro c
    apply Subtype.ext
    exact hinv c.1
  right_inv := by
    intro c
    apply Subtype.ext
    exact hinv c.1

/-- Middle-block factor transported to its canonical `Fin` size. -/
def firstPairMiddleIndexedPerm
    {n : ℕ} {π : Equiv.Perm (Fin (n + 1))}
    (hinv : isInvolutionPerm π) (hnc : isLinearNoncrossingPerm π)
    {b : Fin (n + 1)} (hb : π 0 = b) (h0b : 0 < b.1) :
    Equiv.Perm (Fin (b.1 - 1)) :=
  transportPerm (firstPairMiddleBlockEquivFin b)
    (firstPairMiddlePerm hinv hnc hb h0b)

/-- The indexed middle-block factor is involutive. -/
theorem firstPairMiddleIndexedPerm_isInvolutionPerm
    {n : ℕ} {π : Equiv.Perm (Fin (n + 1))}
    (hinv : isInvolutionPerm π) (hnc : isLinearNoncrossingPerm π)
    {b : Fin (n + 1)} (hb : π 0 = b) (h0b : 0 < b.1) :
    isInvolutionPerm (firstPairMiddleIndexedPerm hinv hnc hb h0b) := by
  exact transportPerm_isInvolutionPerm (firstPairMiddleBlockEquivFin b)
    (fun c => by
      apply Subtype.ext
      exact hinv c.1)

/-- The indexed middle-block factor remains linearly noncrossing. -/
theorem firstPairMiddleIndexedPerm_isLinearNoncrossingPerm
    {n : ℕ} {π : Equiv.Perm (Fin (n + 1))}
    (hinv : isInvolutionPerm π) (hnc : isLinearNoncrossingPerm π)
    {p : Fin (n + 1)} (hp : π 0 = p) (h0p : 0 < p.1) :
    isLinearNoncrossingPerm (firstPairMiddleIndexedPerm hinv hnc hp h0p) := by
  intro a b c d hab hcd hac hcb hbd hbad
  let e := firstPairMiddleBlockEquivFin p
  let σ := firstPairMiddlePerm hinv hnc hp h0p
  have hσab : σ (e.symm a) = e.symm b := by
    apply e.injective
    simpa [e, σ, firstPairMiddleIndexedPerm, transportPerm] using hbad.1
  have hσcd : σ (e.symm c) = e.symm d := by
    apply e.injective
    simpa [e, σ, firstPairMiddleIndexedPerm, transportPerm] using hbad.2
  have hπab : π (e.symm a).1 = (e.symm b).1 := by
    have h := congrArg Subtype.val hσab
    simpa [e, σ, firstPairMiddlePerm] using h
  have hπcd : π (e.symm c).1 = (e.symm d).1 := by
    have h := congrArg Subtype.val hσcd
    simpa [e, σ, firstPairMiddlePerm] using h
  have hab' : (e.symm a).1.1 < (e.symm b).1.1 := by
    change a.1 + 1 < b.1 + 1
    omega
  have hcd' : (e.symm c).1.1 < (e.symm d).1.1 := by
    change c.1 + 1 < d.1 + 1
    omega
  have hac' : (e.symm a).1.1 < (e.symm c).1.1 := by
    change a.1 + 1 < c.1 + 1
    omega
  have hcb' : (e.symm c).1.1 < (e.symm b).1.1 := by
    change c.1 + 1 < b.1 + 1
    omega
  have hbd' : (e.symm b).1.1 < (e.symm d).1.1 := by
    change b.1 + 1 < d.1 + 1
    omega
  exact (hnc (e.symm a).1 (e.symm b).1 (e.symm c).1 (e.symm d).1
    hab' hcd' hac' hcb' hbd') ⟨hπab, hπcd⟩

/-- Middle paired branch packaged as a canonical-index noncrossing matching. -/
def firstPairMiddleIndexedMatching
    {n : ℕ} (π : LinearNoncrossingMatchingPerm (n + 1))
    {b : Fin (n + 1)} (hb : π.1 0 = b) (h0b : 0 < b.1) :
    LinearNoncrossingMatchingPerm (b.1 - 1) :=
  ⟨firstPairMiddleIndexedPerm π.2.1 π.2.2 hb h0b,
    firstPairMiddleIndexedPerm_isInvolutionPerm π.2.1 π.2.2 hb h0b,
    firstPairMiddleIndexedPerm_isLinearNoncrossingPerm π.2.1 π.2.2 hb h0b⟩

/-- Restriction of a noncrossing matching to the right block after the positive
partner `b` of `0`. -/
def firstPairRightPerm
    {n : ℕ} {π : Equiv.Perm (Fin (n + 1))}
    (hinv : isInvolutionPerm π) (hnc : isLinearNoncrossingPerm π)
    {b : Fin (n + 1)} (hb : π 0 = b) (h0b : 0 < b.1) :
    Equiv.Perm (FirstPairRightBlock b) where
  toFun := fun c =>
    ⟨π c.1,
      isLinearNoncrossingPerm_first_pair_right_interval_closed
        (π := π) hinv hnc hb h0b c.2⟩
  invFun := fun c =>
    ⟨π c.1,
      isLinearNoncrossingPerm_first_pair_right_interval_closed
        (π := π) hinv hnc hb h0b c.2⟩
  left_inv := by
    intro c
    apply Subtype.ext
    exact hinv c.1
  right_inv := by
    intro c
    apply Subtype.ext
    exact hinv c.1

/-- Right-block factor transported to its canonical `Fin` size. -/
def firstPairRightIndexedPerm
    {n : ℕ} {π : Equiv.Perm (Fin (n + 1))}
    (hinv : isInvolutionPerm π) (hnc : isLinearNoncrossingPerm π)
    {b : Fin (n + 1)} (hb : π 0 = b) (h0b : 0 < b.1) :
    Equiv.Perm (Fin (n - b.1)) :=
  transportPerm (firstPairRightBlockEquivFin b)
    (firstPairRightPerm hinv hnc hb h0b)

/-- The indexed right-block factor is involutive. -/
theorem firstPairRightIndexedPerm_isInvolutionPerm
    {n : ℕ} {π : Equiv.Perm (Fin (n + 1))}
    (hinv : isInvolutionPerm π) (hnc : isLinearNoncrossingPerm π)
    {b : Fin (n + 1)} (hb : π 0 = b) (h0b : 0 < b.1) :
    isInvolutionPerm (firstPairRightIndexedPerm hinv hnc hb h0b) := by
  exact transportPerm_isInvolutionPerm (firstPairRightBlockEquivFin b)
    (fun c => by
      apply Subtype.ext
      exact hinv c.1)

/-- The indexed right-block factor remains linearly noncrossing. -/
theorem firstPairRightIndexedPerm_isLinearNoncrossingPerm
    {n : ℕ} {π : Equiv.Perm (Fin (n + 1))}
    (hinv : isInvolutionPerm π) (hnc : isLinearNoncrossingPerm π)
    {p : Fin (n + 1)} (hp : π 0 = p) (h0p : 0 < p.1) :
    isLinearNoncrossingPerm (firstPairRightIndexedPerm hinv hnc hp h0p) := by
  intro a b c d hab hcd hac hcb hbd hbad
  let e := firstPairRightBlockEquivFin p
  let σ := firstPairRightPerm hinv hnc hp h0p
  have hσab : σ (e.symm a) = e.symm b := by
    apply e.injective
    simpa [e, σ, firstPairRightIndexedPerm, transportPerm] using hbad.1
  have hσcd : σ (e.symm c) = e.symm d := by
    apply e.injective
    simpa [e, σ, firstPairRightIndexedPerm, transportPerm] using hbad.2
  have hπab : π (e.symm a).1 = (e.symm b).1 := by
    have h := congrArg Subtype.val hσab
    simpa [e, σ, firstPairRightPerm] using h
  have hπcd : π (e.symm c).1 = (e.symm d).1 := by
    have h := congrArg Subtype.val hσcd
    simpa [e, σ, firstPairRightPerm] using h
  have hab' : (e.symm a).1.1 < (e.symm b).1.1 := by
    change p.1 + 1 + a.1 < p.1 + 1 + b.1
    omega
  have hcd' : (e.symm c).1.1 < (e.symm d).1.1 := by
    change p.1 + 1 + c.1 < p.1 + 1 + d.1
    omega
  have hac' : (e.symm a).1.1 < (e.symm c).1.1 := by
    change p.1 + 1 + a.1 < p.1 + 1 + c.1
    omega
  have hcb' : (e.symm c).1.1 < (e.symm b).1.1 := by
    change p.1 + 1 + c.1 < p.1 + 1 + b.1
    omega
  have hbd' : (e.symm b).1.1 < (e.symm d).1.1 := by
    change p.1 + 1 + b.1 < p.1 + 1 + d.1
    omega
  exact (hnc (e.symm a).1 (e.symm b).1 (e.symm c).1 (e.symm d).1
    hab' hcd' hac' hcb' hbd') ⟨hπab, hπcd⟩

/-- Right paired branch packaged as a canonical-index noncrossing matching. -/
def firstPairRightIndexedMatching
    {n : ℕ} (π : LinearNoncrossingMatchingPerm (n + 1))
    {b : Fin (n + 1)} (hb : π.1 0 = b) (h0b : 0 < b.1) :
    LinearNoncrossingMatchingPerm (n - b.1) :=
  ⟨firstPairRightIndexedPerm π.2.1 π.2.2 hb h0b,
    firstPairRightIndexedPerm_isInvolutionPerm π.2.1 π.2.2 hb h0b,
    firstPairRightIndexedPerm_isLinearNoncrossingPerm π.2.1 π.2.2 hb h0b⟩

/-- Restricting the paired extension to the middle block recovers the middle
factor. -/
theorem firstPairMiddleIndexedPerm_firstPairExtendPerm
    {n : ℕ} (b : Fin (n + 1)) (h0b : 0 < b.1)
    {τ : Equiv.Perm (Fin (b.1 - 1))} {υ : Equiv.Perm (Fin (n - b.1))}
    (hτinv : isInvolutionPerm τ) (hυinv : isInvolutionPerm υ)
    (hτnc : isLinearNoncrossingPerm τ) (hυnc : isLinearNoncrossingPerm υ) :
    firstPairMiddleIndexedPerm
      (firstPairExtendPerm_isInvolutionPerm b h0b hτinv hυinv)
      (firstPairExtendPerm_isLinearNoncrossingPerm b h0b hτnc hυnc)
      (firstPairExtendPerm_zero b h0b τ υ) h0b = τ := by
  apply Equiv.ext
  intro i
  let e := firstPairMiddleBlockEquivFin b
  apply e.symm.injective
  apply Subtype.ext
  simpa [e, firstPairMiddleIndexedPerm, transportPerm, firstPairMiddlePerm,
    firstPairMiddleEmbed] using firstPairExtendPerm_middle b h0b τ υ i

/-- Restricting the paired extension to the right block recovers the right
factor. -/
theorem firstPairRightIndexedPerm_firstPairExtendPerm
    {n : ℕ} (b : Fin (n + 1)) (h0b : 0 < b.1)
    {τ : Equiv.Perm (Fin (b.1 - 1))} {υ : Equiv.Perm (Fin (n - b.1))}
    (hτinv : isInvolutionPerm τ) (hυinv : isInvolutionPerm υ)
    (hτnc : isLinearNoncrossingPerm τ) (hυnc : isLinearNoncrossingPerm υ) :
    firstPairRightIndexedPerm
      (firstPairExtendPerm_isInvolutionPerm b h0b hτinv hυinv)
      (firstPairExtendPerm_isLinearNoncrossingPerm b h0b hτnc hυnc)
      (firstPairExtendPerm_zero b h0b τ υ) h0b = υ := by
  apply Equiv.ext
  intro i
  let e := firstPairRightBlockEquivFin b
  apply e.symm.injective
  apply Subtype.ext
  simpa [e, firstPairRightIndexedPerm, transportPerm, firstPairRightPerm,
    firstPairRightEmbed] using firstPairExtendPerm_right b h0b τ υ i

/-- Matching-level inverse law: middle restriction of the paired extension
recovers the middle matching. -/
theorem firstPairMiddleIndexedMatching_firstPairExtendMatching
    {n : ℕ} (b : Fin (n + 1)) (h0b : 0 < b.1)
    (τ : LinearNoncrossingMatchingPerm (b.1 - 1))
    (υ : LinearNoncrossingMatchingPerm (n - b.1)) :
    firstPairMiddleIndexedMatching
      (firstPairExtendMatching b h0b τ υ)
      (firstPairExtendPerm_zero b h0b τ.1 υ.1) h0b = τ := by
  apply Subtype.ext
  exact firstPairMiddleIndexedPerm_firstPairExtendPerm
    b h0b τ.2.1 υ.2.1 τ.2.2 υ.2.2

/-- Matching-level inverse law: right restriction of the paired extension
recovers the right matching. -/
theorem firstPairRightIndexedMatching_firstPairExtendMatching
    {n : ℕ} (b : Fin (n + 1)) (h0b : 0 < b.1)
    (τ : LinearNoncrossingMatchingPerm (b.1 - 1))
    (υ : LinearNoncrossingMatchingPerm (n - b.1)) :
    firstPairRightIndexedMatching
      (firstPairExtendMatching b h0b τ υ)
      (firstPairExtendPerm_zero b h0b τ.1 υ.1) h0b = υ := by
  apply Subtype.ext
  exact firstPairRightIndexedPerm_firstPairExtendPerm
    b h0b τ.2.1 υ.2.1 τ.2.2 υ.2.2

/-- Restricting a paired matching to its middle/right factors and extending
those factors recovers the original permutation. -/
theorem firstPairExtendPerm_firstPairIndexedPerms
    {n : ℕ} {π : Equiv.Perm (Fin (n + 1))}
    (hinv : isInvolutionPerm π) (hnc : isLinearNoncrossingPerm π)
    {b : Fin (n + 1)} (hb : π 0 = b) (h0b : 0 < b.1) :
    firstPairExtendPerm b h0b
      (firstPairMiddleIndexedPerm hinv hnc hb h0b)
      (firstPairRightIndexedPerm hinv hnc hb h0b) = π := by
  apply Equiv.ext
  intro x
  by_cases hzero : x = 0
  · subst x
    rw [firstPairExtendPerm_zero, hb]
  · by_cases hpartner : x = b
    · subst x
      rw [firstPairExtendPerm_partner]
      exact (isInvolutionPerm_first_pair_partner_zero hinv hb).symm
    · by_cases hmid : 0 < x.1 ∧ x.1 < b.1
      · let i : Fin (b.1 - 1) := firstPairMiddleBlockEquivFin b ⟨x, hmid⟩
        have hx : firstPairMiddleEmbed b i = x :=
          firstPairMiddleEmbed_equiv_apply b ⟨x, hmid⟩
        calc
          firstPairExtendPerm b h0b
              (firstPairMiddleIndexedPerm hinv hnc hb h0b)
              (firstPairRightIndexedPerm hinv hnc hb h0b) x =
              firstPairMiddleEmbed b
                (firstPairMiddleIndexedPerm hinv hnc hb h0b i) := by
                rw [← hx, firstPairExtendPerm_middle]
          _ = π x := by
                simpa [i, firstPairMiddleIndexedPerm, transportPerm,
                  firstPairMiddlePerm, firstPairMiddleEmbed] using rfl
      · have hx_ne_zero_val : x.1 ≠ 0 := by
          intro hx0
          exact hzero (Fin.ext hx0)
        have hx_pos : 0 < x.1 := Nat.pos_of_ne_zero hx_ne_zero_val
        have hnot_lt : ¬ x.1 < b.1 := by
          intro hlt
          exact hmid ⟨hx_pos, hlt⟩
        have hb_le_x : b.1 ≤ x.1 := le_of_not_gt hnot_lt
        have hne_val : x.1 ≠ b.1 := by
          intro hval
          exact hpartner (Fin.ext hval)
        have hright : b.1 < x.1 := by omega
        let i : Fin (n - b.1) := firstPairRightBlockEquivFin b ⟨x, hright⟩
        have hx : firstPairRightEmbed b i = x :=
          firstPairRightEmbed_equiv_apply b ⟨x, hright⟩
        calc
          firstPairExtendPerm b h0b
              (firstPairMiddleIndexedPerm hinv hnc hb h0b)
              (firstPairRightIndexedPerm hinv hnc hb h0b) x =
              firstPairRightEmbed b
                (firstPairRightIndexedPerm hinv hnc hb h0b i) := by
                rw [← hx, firstPairExtendPerm_right]
          _ = π x := by
                simpa [i, firstPairRightIndexedPerm, transportPerm,
                  firstPairRightPerm, firstPairRightEmbed] using rfl

/-- Restricting a paired matching to its middle/right factors and extending
those factors recovers the original matching. -/
theorem firstPairExtendMatching_firstPairIndexedMatchings
    {n : ℕ} (π : LinearNoncrossingMatchingPerm (n + 1))
    {b : Fin (n + 1)} (hb : π.1 0 = b) (h0b : 0 < b.1) :
    firstPairExtendMatching b h0b
      (firstPairMiddleIndexedMatching π hb h0b)
      (firstPairRightIndexedMatching π hb h0b) = π := by
  apply Subtype.ext
  exact firstPairExtendPerm_firstPairIndexedPerms π.2.1 π.2.2 hb h0b

/-- If `0` is fixed, then the image of every tail vertex is again a tail
vertex. -/
theorem firstFixedTail_image_succ_ne_zero
    {n : ℕ} (π : Equiv.Perm (Fin (n + 1))) (h0 : π 0 = 0) (i : Fin n) :
    π i.succ ≠ 0 := by
  intro h
  have hsucc0 : i.succ = 0 := π.injective (by
    calc
      π i.succ = 0 := h
      _ = π 0 := h0.symm)
  exact Fin.succ_ne_zero i hsucc0

/-- Tail restriction of a permutation fixing `0`.  This is the permutation
level of the fixed-point branch in the Motzkin first-return decomposition. -/
noncomputable def firstFixedTailPerm
    {n : ℕ} (π : Equiv.Perm (Fin (n + 1))) (h0 : π 0 = 0) :
    Equiv.Perm (Fin n) :=
  Equiv.ofBijective
    (fun i : Fin n =>
      (π i.succ).pred (firstFixedTail_image_succ_ne_zero π h0 i))
    ⟨by
      intro i j hij
      apply Fin.succ_injective n
      apply π.injective
      have hsucc := congrArg Fin.succ hij
      simpa [Fin.succ_pred] using hsucc,
    by
      intro y
      obtain ⟨z, hz⟩ := π.surjective y.succ
      have hz_ne_zero : z ≠ 0 := by
        intro hz0
        have hy0 : y.succ = 0 := by
          calc
            y.succ = π z := hz.symm
            _ = π 0 := by rw [hz0]
            _ = 0 := h0
        exact Fin.succ_ne_zero y hy0
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hz_ne_zero
      refine ⟨i, ?_⟩
      simp [hz]⟩

/-- The tail restriction is characterized by shifting back into the original
permutation. -/
theorem firstFixedTailPerm_succ_apply
    {n : ℕ} {π : Equiv.Perm (Fin (n + 1))} {h0 : π 0 = 0} (i : Fin n) :
    (firstFixedTailPerm π h0 i).succ = π i.succ := by
  simp [firstFixedTailPerm, Fin.succ_pred]

/-- The fixed-tail restriction of an involutive permutation is involutive. -/
theorem firstFixedTailPerm_isInvolutionPerm
    {n : ℕ} {π : Equiv.Perm (Fin (n + 1))}
    (h0 : π 0 = 0) (hinv : isInvolutionPerm π) :
    isInvolutionPerm (firstFixedTailPerm π h0) := by
  intro i
  apply Fin.succ_injective n
  calc
    (firstFixedTailPerm π h0 (firstFixedTailPerm π h0 i)).succ =
        π ((firstFixedTailPerm π h0 i).succ) :=
      firstFixedTailPerm_succ_apply (π := π) (h0 := h0)
        (firstFixedTailPerm π h0 i)
    _ = π (π i.succ) := by
      rw [firstFixedTailPerm_succ_apply (π := π) (h0 := h0) i]
    _ = i.succ := hinv i.succ

/-- The fixed-tail restriction of a linearly noncrossing permutation is still
linearly noncrossing. -/
theorem firstFixedTailPerm_isLinearNoncrossingPerm
    {n : ℕ} {π : Equiv.Perm (Fin (n + 1))}
    (h0 : π 0 = 0) (hnc : isLinearNoncrossingPerm π) :
    isLinearNoncrossingPerm (firstFixedTailPerm π h0) := by
  intro a b c d hab hcd hac hcb hbd hbad
  have hπab : π a.succ = b.succ := by
    calc
      π a.succ = (firstFixedTailPerm π h0 a).succ :=
        (firstFixedTailPerm_succ_apply (π := π) (h0 := h0) a).symm
      _ = b.succ := by rw [hbad.1]
  have hπcd : π c.succ = d.succ := by
    calc
      π c.succ = (firstFixedTailPerm π h0 c).succ :=
        (firstFixedTailPerm_succ_apply (π := π) (h0 := h0) c).symm
      _ = d.succ := by rw [hbad.2]
  have hbadOrig :=
    hnc a.succ b.succ c.succ d.succ
      (Fin.succ_lt_succ_iff.mpr hab)
      (Fin.succ_lt_succ_iff.mpr hcd)
      (Fin.succ_lt_succ_iff.mpr hac)
      (Fin.succ_lt_succ_iff.mpr hcb)
      (Fin.succ_lt_succ_iff.mpr hbd)
  exact hbadOrig ⟨hπab, hπcd⟩

/-- Fixed-point branch of the Motzkin decomposition: if a noncrossing matching
fixes `0`, its tail restriction is again a noncrossing matching. -/
noncomputable def firstFixedTailMatching
    {n : ℕ} (π : LinearNoncrossingMatchingPerm (n + 1)) (h0 : π.1 0 = 0) :
    LinearNoncrossingMatchingPerm n :=
  ⟨firstFixedTailPerm π.1 h0,
    firstFixedTailPerm_isInvolutionPerm h0 π.2.1,
    firstFixedTailPerm_isLinearNoncrossingPerm h0 π.2.2⟩

/-- Extend a permutation of the tail by fixing the new first vertex.  This is
the inverse construction for the fixed-point branch of the Motzkin
decomposition. -/
def firstFixedExtendPerm {n : ℕ} (τ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + 1)) where
  toFun := Fin.cases 0 fun i => (τ i).succ
  invFun := Fin.cases 0 fun i => (τ.symm i).succ
  left_inv := by
    intro i
    cases i using Fin.cases <;> simp
  right_inv := by
    intro i
    cases i using Fin.cases <;> simp

@[simp] theorem firstFixedExtendPerm_zero {n : ℕ} (τ : Equiv.Perm (Fin n)) :
    firstFixedExtendPerm τ 0 = 0 := by
  rfl

@[simp] theorem firstFixedExtendPerm_succ {n : ℕ}
    (τ : Equiv.Perm (Fin n)) (i : Fin n) :
    firstFixedExtendPerm τ i.succ = (τ i).succ := by
  rfl

/-- Extending an involutive tail permutation by a fixed first vertex preserves
involutivity. -/
theorem firstFixedExtendPerm_isInvolutionPerm
    {n : ℕ} {τ : Equiv.Perm (Fin n)} (hinv : isInvolutionPerm τ) :
    isInvolutionPerm (firstFixedExtendPerm τ) := by
  intro i
  cases i using Fin.cases with
  | zero => simp
  | succ i => simp [hinv i]

/-- Extending a linearly noncrossing tail permutation by a fixed first vertex
preserves linear noncrossing. -/
theorem firstFixedExtendPerm_isLinearNoncrossingPerm
    {n : ℕ} {τ : Equiv.Perm (Fin n)} (hnc : isLinearNoncrossingPerm τ) :
    isLinearNoncrossingPerm (firstFixedExtendPerm τ) := by
  intro a b c d hab hcd hac hcb hbd hbad
  cases a using Fin.cases with
  | zero =>
      have hb0 : b = 0 := by
        simpa using hbad.1.symm
      subst b
      simp at hab
  | succ a =>
      cases b using Fin.cases with
      | zero =>
          simp at hab
      | succ b =>
          cases c using Fin.cases with
          | zero =>
              simp at hac
          | succ c =>
              cases d using Fin.cases with
              | zero =>
                  simp at hcd
              | succ d =>
                  have hbadTail : ¬ (τ a = b ∧ τ c = d) :=
                    hnc a b c d
                      (Fin.succ_lt_succ_iff.mp hab)
                      (Fin.succ_lt_succ_iff.mp hcd)
                      (Fin.succ_lt_succ_iff.mp hac)
                      (Fin.succ_lt_succ_iff.mp hcb)
                      (Fin.succ_lt_succ_iff.mp hbd)
                  have hpair : τ a = b ∧ τ c = d := by
                    simpa using hbad
                  exact hbadTail hpair

/-- Fixed-point extension branch of the Motzkin decomposition: a noncrossing
matching on the tail extends to a noncrossing matching fixing `0`. -/
def firstFixedExtendMatching
    {n : ℕ} (τ : LinearNoncrossingMatchingPerm n) :
    LinearNoncrossingMatchingPerm (n + 1) :=
  ⟨firstFixedExtendPerm τ.1,
    firstFixedExtendPerm_isInvolutionPerm τ.2.1,
    firstFixedExtendPerm_isLinearNoncrossingPerm τ.2.2⟩

/-- Restricting the fixed extension recovers the original tail permutation. -/
theorem firstFixedTailPerm_firstFixedExtendPerm
    {n : ℕ} (τ : Equiv.Perm (Fin n))
    (h0 : firstFixedExtendPerm τ 0 = 0) :
    firstFixedTailPerm (firstFixedExtendPerm τ) h0 = τ := by
  apply Equiv.ext
  intro i
  apply Fin.succ_injective n
  rw [firstFixedTailPerm_succ_apply, firstFixedExtendPerm_succ]

/-- Extending the tail restriction recovers the original permutation, provided
the original permutation fixed `0`. -/
theorem firstFixedExtendPerm_firstFixedTailPerm
    {n : ℕ} {π : Equiv.Perm (Fin (n + 1))} (h0 : π 0 = 0) :
    firstFixedExtendPerm (firstFixedTailPerm π h0) = π := by
  apply Equiv.ext
  intro i
  cases i using Fin.cases with
  | zero => simp [h0]
  | succ i =>
      rw [firstFixedExtendPerm_succ, firstFixedTailPerm_succ_apply]

/-- Matching-level inverse law for fixed extension followed by tail
restriction. -/
theorem firstFixedTailMatching_firstFixedExtendMatching
    {n : ℕ} (τ : LinearNoncrossingMatchingPerm n)
    (h0 : (firstFixedExtendMatching τ).1 0 = 0) :
    firstFixedTailMatching (firstFixedExtendMatching τ) h0 = τ := by
  apply Subtype.ext
  exact firstFixedTailPerm_firstFixedExtendPerm τ.1 h0

/-- Matching-level inverse law for tail restriction followed by fixed
extension. -/
theorem firstFixedExtendMatching_firstFixedTailMatching
    {n : ℕ} (π : LinearNoncrossingMatchingPerm (n + 1)) (h0 : π.1 0 = 0) :
    firstFixedExtendMatching (firstFixedTailMatching π h0) = π := by
  apply Subtype.ext
  exact firstFixedExtendPerm_firstFixedTailPerm h0

/-- The first-return decomposition target for noncrossing matchings on
`Fin (n+1)`: either `0` is fixed and one keeps a tail matching on `Fin n`, or
`0` is paired with a positive partner `b`, leaving a middle matching on
`Fin (b.val-1)` and a right matching on `Fin (n-b.val)`. -/
abbrev LinearNoncrossingFirstReturnDecomposition (n : ℕ) : Type :=
  LinearNoncrossingMatchingPerm n ⊕
    (Σ b : {b : Fin (n + 1) // 0 < b.1},
      LinearNoncrossingMatchingPerm (b.1.1 - 1) ×
        LinearNoncrossingMatchingPerm (n - b.1.1))

instance (n : ℕ) : Fintype (LinearNoncrossingFirstReturnDecomposition n) := by
  unfold LinearNoncrossingFirstReturnDecomposition
  infer_instance

/-- First-return equivalence for linearly noncrossing matchings.  This is the
structural core behind the Motzkin recurrence. -/
noncomputable def linearNoncrossingFirstReturnEquiv (n : ℕ) :
    LinearNoncrossingMatchingPerm (n + 1) ≃
      LinearNoncrossingFirstReturnDecomposition n where
  toFun := fun π =>
    if h0 : π.1 0 = 0 then
      Sum.inl (firstFixedTailMatching π h0)
    else
      let b : Fin (n + 1) := π.1 0
      have h0b : 0 < b.1 := by
        have hb_ne_zero : b ≠ 0 := by
          intro hb0
          exact h0 (by simpa [b] using hb0)
        exact Fin.pos_iff_ne_zero.mpr hb_ne_zero
      Sum.inr
        ⟨⟨b, h0b⟩,
          firstPairMiddleIndexedMatching π rfl h0b,
          firstPairRightIndexedMatching π rfl h0b⟩
  invFun
    | Sum.inl τ => firstFixedExtendMatching τ
    | Sum.inr data => firstPairExtendMatching data.1.1 data.1.2 data.2.1 data.2.2
  left_inv := by
    intro π
    by_cases h0 : π.1 0 = 0
    · simp [h0, firstFixedExtendMatching_firstFixedTailMatching]
    · have h0b : 0 < (π.1 0).1 := by
        have hb_ne_zero : π.1 0 ≠ 0 := by
          intro hb0
          exact h0 hb0
        exact Fin.pos_iff_ne_zero.mpr hb_ne_zero
      simp [h0, firstPairExtendMatching_firstPairIndexedMatchings]
  right_inv := by
    intro data
    cases data with
    | inl τ =>
        have h0 : (firstFixedExtendMatching τ).1 0 = 0 := by
          rfl
        simp [h0, firstFixedTailMatching_firstFixedExtendMatching]
    | inr data =>
        rcases data with ⟨b, τ, υ⟩
        have hnot0 : ¬ (firstPairExtendMatching b.1 b.2 τ υ).1 0 = 0 := by
          intro h
          have hfin : b.1 = 0 := by
            simpa [firstPairExtendMatching, firstPairExtendPerm_zero] using h
          have hval := congrArg Fin.val hfin
          exact (Nat.ne_of_gt b.2) hval
        simp [hnot0]
        constructor
        · apply Subtype.ext
          simp [firstPairExtendMatching, firstPairExtendPerm_zero]
        · apply heq_of_eq
          exact Prod.ext
            (firstPairMiddleIndexedMatching_firstPairExtendMatching b.1 b.2 τ υ)
            (firstPairRightIndexedMatching_firstPairExtendMatching b.1 b.2 τ υ)

/-- The Motzkin pair-branch interval closure is not available for arbitrary
bidefect classes.

The inverse long cycle on `Fin 3` lies in the bidefect slice `(a,b)=(0,2)`,
sends `0` to `2`, and sends the middle point `1` back to `0`.  Thus the open
middle interval `(0,2)` is not preserved.  Any bidefect first-return
decomposition must therefore use different data from the noncrossing matching
pair branch, or add stronger hypotheses. -/
theorem not_forall_wickBiDefect_pair_middle_interval_closed :
    ¬ (∀ {m a b : ℕ} (π : WickBiDefectClass m a b)
        {partner c : Fin (m + 1)},
        π.1 0 = partner → 0 < partner.1 → 0 < c.1 → c.1 < partner.1 →
          0 < (π.1 c).1 ∧ (π.1 c).1 < partner.1) := by
  intro h
  let σ : Equiv.Perm (Fin (2 + 1)) := (finRotate (2 + 1)).symm
  have hplus : wickPlusDefect σ = 0 := by
    unfold wickPlusDefect
    repeat rw [permCycleClassCount_eq_cycleCountFormula]
    decide
  have hminus : wickMinusDefect σ = 2 := by
    unfold wickMinusDefect
    repeat rw [permCycleClassCount_eq_cycleCountFormula]
    decide
  let x : WickBiDefectClass 2 0 2 := ⟨σ, hplus, hminus⟩
  have hb : x.1 0 = (2 : Fin (2 + 1)) := by
    dsimp [x, σ]
    decide
  have hval : ((x.1 (1 : Fin (2 + 1))).1 = 0) := by
    dsimp [x, σ]
    decide
  have hclosed :=
    @h 2 0 2 x (2 : Fin (2 + 1)) (1 : Fin (2 + 1))
      hb (by norm_num) (by norm_num) (by norm_num)
  omega

/-- Cardinal form of the first-return decomposition, still indexed by the
positive partner of `0`. -/
theorem card_LinearNoncrossingMatchingPerm_succ_firstReturn
    (n : ℕ) :
    Fintype.card (LinearNoncrossingMatchingPerm (n + 1)) =
      Fintype.card (LinearNoncrossingMatchingPerm n) +
        Finset.univ.sum
          (fun b : {b : Fin (n + 1) // 0 < b.1} =>
            Fintype.card (LinearNoncrossingMatchingPerm (b.1.1 - 1)) *
              Fintype.card (LinearNoncrossingMatchingPerm (n - b.1.1))) := by
  rw [Fintype.card_congr (linearNoncrossingFirstReturnEquiv n)]
  unfold LinearNoncrossingFirstReturnDecomposition
  have hsum :
      Fintype.card
        (LinearNoncrossingMatchingPerm n ⊕
          (Sigma fun b : {b : Fin (n + 1) // 0 < b.1} =>
            LinearNoncrossingMatchingPerm (b.1.1 - 1) ×
              LinearNoncrossingMatchingPerm (n - b.1.1))) =
        Fintype.card (LinearNoncrossingMatchingPerm n) +
          Fintype.card
            (Sigma fun b : {b : Fin (n + 1) // 0 < b.1} =>
              LinearNoncrossingMatchingPerm (b.1.1 - 1) ×
                LinearNoncrossingMatchingPerm (n - b.1.1)) :=
    Fintype.card_sum
  rw [hsum]
  rw [Fintype.card_sigma]
  simp [Fintype.card_prod]

/-- Positive partners in `Fin (n+1)` are canonically indexed by
`Fin n`, via `b ↦ b.val-1`. -/
def positiveFinSuccEquiv (n : ℕ) :
    {b : Fin (n + 1) // 0 < b.1} ≃ Fin n where
  toFun := fun b =>
    ⟨b.1.1 - 1, by
      have hb_lt := b.1.2
      omega⟩
  invFun := fun i =>
    ⟨⟨i.1 + 1, by
        have hi_lt := i.2
        omega⟩,
      by
        change 0 < i.1 + 1
        omega⟩
  left_inv := by
    intro b
    apply Subtype.ext
    apply Fin.ext
    have hb_pos := b.2
    change (b.1.1 - 1) + 1 = b.1.1
    omega
  right_inv := by
    intro i
    apply Fin.ext
    change (i.1 + 1) - 1 = i.1
    omega

@[simp] theorem positiveFinSuccEquiv_symm_val
    (n : ℕ) (i : Fin n) :
    ((positiveFinSuccEquiv n).symm i).1.1 = i.1 + 1 := by
  rfl

/-- First-return cardinal recurrence in the standard Motzkin indexing. -/
theorem card_LinearNoncrossingMatchingPerm_succ_motzkinIndexed
    (n : ℕ) :
    Fintype.card (LinearNoncrossingMatchingPerm (n + 1)) =
      Fintype.card (LinearNoncrossingMatchingPerm n) +
        Finset.univ.sum
          (fun i : Fin n =>
            Fintype.card (LinearNoncrossingMatchingPerm i.1) *
              Fintype.card (LinearNoncrossingMatchingPerm (n - 1 - i.1))) := by
  rw [card_LinearNoncrossingMatchingPerm_succ_firstReturn n]
  congr 1
  simpa using
    Fintype.sum_equiv (positiveFinSuccEquiv n)
      (fun b : {b : Fin (n + 1) // 0 < b.1} =>
        Fintype.card (LinearNoncrossingMatchingPerm (b.1.1 - 1)) *
          Fintype.card (LinearNoncrossingMatchingPerm (n - b.1.1)))
      (fun i : Fin n =>
        Fintype.card (LinearNoncrossingMatchingPerm i.1) *
          Fintype.card (LinearNoncrossingMatchingPerm (n - 1 - i.1)))
      (by
        intro b
        have hright : n - 1 - (b.1.1 - 1) = n - b.1.1 := by
          have hb_pos := b.2
          omega
        change
          Fintype.card (LinearNoncrossingMatchingPerm (b.1.1 - 1)) *
              Fintype.card (LinearNoncrossingMatchingPerm (n - b.1.1)) =
            Fintype.card (LinearNoncrossingMatchingPerm (b.1.1 - 1)) *
              Fintype.card (LinearNoncrossingMatchingPerm (n - 1 - (b.1.1 - 1)))
        rw [hright])

/-- The pointwise predicate underlying `WickCyclePairTightClassFormula`. -/
def cyclePairTightFormulaPredicate
    (m : ℕ) (π : Equiv.Perm (Fin (m + 1))) : Prop :=
  cycleCountFormula π +
      cycleCountFormula (finRotate (m + 1) * π) = (m + 1) + 1 ∧
    cycleCountFormula π +
      cycleCountFormula (π * (finRotate (m + 1)).symm) = (m + 1) + 1

instance cyclePairTightFormulaPredicate_decidable
    (m : ℕ) (π : Equiv.Perm (Fin (m + 1))) :
    Decidable (cyclePairTightFormulaPredicate m π) := by
  unfold cyclePairTightFormulaPredicate
  infer_instance

/-- If the pointwise simultaneous-geodesic predicate is identified with
linear noncrossing matchings, then the two subtype formulations are equivalent.

This is the exact structural bridge needed for the Motzkin route to
`U-AUB-122`. -/
noncomputable def cyclePairTightClassFormulaEquivLinearNoncrossingMatching
    {m : ℕ}
    (h :
      ∀ π : Equiv.Perm (Fin (m + 1)),
        cyclePairTightFormulaPredicate m π ↔
          isInvolutionPerm π ∧ isLinearNoncrossingPerm π) :
    WickCyclePairTightClassFormula m ≃ LinearNoncrossingMatchingPerm (m + 1) where
  toFun := fun π =>
    ⟨π.1, (h π.1).mp (by
      simpa [WickCyclePairTightClassFormula, cyclePairTightFormulaPredicate]
        using π.2)⟩
  invFun := fun π =>
    ⟨π.1, by
      have hp := (h π.1).mpr π.2
      simpa [WickCyclePairTightClassFormula, cyclePairTightFormulaPredicate]
        using hp⟩
  left_inv := by
    intro π
    rfl
  right_inv := by
    intro π
    rfl

/-- Motzkin numbers in the standard first-return recurrence
`M₀ = 1`, `Mₙ₊₁ = Mₙ + Σᵢ Mᵢ Mₙ₋₁₋ᵢ`. -/
def motzkinNumber : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      motzkinNumber n +
        Finset.univ.sum
          (fun i : Fin n => motzkinNumber i.1 * motzkinNumber (n - 1 - i.1))
termination_by n => n
decreasing_by
  · exact Nat.lt_succ_self n
  · exact Nat.lt_trans i.isLt (Nat.lt_succ_self n)
  · exact Nat.lt_succ_of_le
      (le_trans (Nat.sub_le (n - 1) i.1) (Nat.sub_le n 1))

@[simp] theorem motzkinNumber_zero : motzkinNumber 0 = 1 := by
  rw [motzkinNumber]

theorem motzkinNumber_succ (n : ℕ) :
    motzkinNumber (n + 1) =
      motzkinNumber n +
        Finset.univ.sum
          (fun i : Fin n => motzkinNumber i.1 * motzkinNumber (n - 1 - i.1)) := by
  rw [motzkinNumber]

@[simp] theorem motzkinNumber_one : motzkinNumber 1 = 1 := by
  rw [motzkinNumber_succ]
  simp

@[simp] theorem motzkinNumber_two : motzkinNumber 2 = 2 := by
  rw [motzkinNumber_succ]
  simp

@[simp] theorem motzkinNumber_three : motzkinNumber 3 = 4 := by
  rw [motzkinNumber_succ]
  simp [Fin.sum_univ_two]

@[simp] theorem motzkinNumber_four : motzkinNumber 4 = 9 := by
  rw [motzkinNumber_succ]
  simp [Fin.sum_univ_three]

@[simp] theorem motzkinNumber_five : motzkinNumber 5 = 21 := by
  rw [motzkinNumber_succ]
  simp [Fin.sum_univ_four]

@[simp] theorem motzkinNumber_six : motzkinNumber 6 = 51 := by
  rw [motzkinNumber_succ]
  simp [Fin.sum_univ_five]

@[simp] theorem motzkinNumber_seven : motzkinNumber 7 = 127 := by
  rw [motzkinNumber_succ]
  simp [Fin.sum_univ_six]

@[simp] theorem motzkinNumber_eight : motzkinNumber 8 = 323 := by
  rw [motzkinNumber_succ]
  simp [Fin.sum_univ_seven]

/-- The Motzkin prediction at the first no-go length exceeds the old
zero-defect envelope `2^(m+1)` with `m = 7`. -/
theorem two_pow_eight_lt_motzkinNumber_eight :
    2 ^ 8 < motzkinNumber 8 := by
  rw [motzkinNumber_eight]
  norm_num

/-- Linearly noncrossing matching permutations are counted by Motzkin
numbers. -/
theorem card_LinearNoncrossingMatchingPerm_eq_motzkinNumber
    (n : ℕ) :
    Fintype.card (LinearNoncrossingMatchingPerm n) = motzkinNumber n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          rw [motzkinNumber_zero]
          decide
      | succ n =>
          rw [card_LinearNoncrossingMatchingPerm_succ_motzkinIndexed,
            motzkinNumber_succ]
          rw [ih n (Nat.lt_succ_self n)]
          congr 1
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [ih i.1 (by omega)]
          rw [ih (n - 1 - i.1) (by omega)]

/-- Canonical finite Motzkin code type of size `Mₙ`.

This is deliberately only a certificate target: proving that noncrossing
matchings are counted by Motzkin numbers is now the task of constructing an
equivalence with this finite type. -/
abbrev MotzkinCode (n : ℕ) : Type :=
  Fin (motzkinNumber n)

instance (n : ℕ) : Fintype (MotzkinCode n) := by
  unfold MotzkinCode
  infer_instance

/-- The canonical Motzkin code type has the Motzkin cardinality by definition. -/
theorem card_MotzkinCode (n : ℕ) :
    Fintype.card (MotzkinCode n) = motzkinNumber n := by
  change Fintype.card (Fin (motzkinNumber n)) = motzkinNumber n
  exact Fintype.card_fin _

/-- A concrete equivalence from noncrossing matchings to Motzkin codes is
exactly enough to prove the Motzkin enumeration of those matchings. -/
theorem card_LinearNoncrossingMatchingPerm_eq_motzkinNumber_of_equivMotzkinCode
    {n : ℕ} (e : LinearNoncrossingMatchingPerm n ≃ MotzkinCode n) :
    Fintype.card (LinearNoncrossingMatchingPerm n) = motzkinNumber n := by
  rw [Fintype.card_congr e, card_MotzkinCode]

/-- Kernel-checked small-size sanity count for noncrossing matchings. -/
theorem card_LinearNoncrossingMatchingPerm_four :
    Fintype.card (LinearNoncrossingMatchingPerm 4) = motzkinNumber 4 := by
  rw [motzkinNumber_four]
  decide

/-- Kernel-checked small-size sanity count for noncrossing matchings. -/
theorem card_LinearNoncrossingMatchingPerm_five :
    Fintype.card (LinearNoncrossingMatchingPerm 5) = motzkinNumber 5 := by
  rw [motzkinNumber_five]
  decide

/-- Kernel-checked first nontrivial pointwise tight/noncrossing classification. -/
theorem cyclePairTightFormulaPredicate_iff_linearNoncrossing_three :
    ∀ π : Equiv.Perm (Fin (3 + 1)),
      cyclePairTightFormulaPredicate 3 π ↔
        isInvolutionPerm π ∧ isLinearNoncrossingPerm π := by
  decide

/-- General card bridge from the pointwise noncrossing-matching classification
and the Motzkin enumeration of those matchings. -/
theorem card_WickCyclePairTightClassFormula_eq_motzkinNumber_of_linearNoncrossing
    {m : ℕ}
    (hClass :
      ∀ π : Equiv.Perm (Fin (m + 1)),
        cyclePairTightFormulaPredicate m π ↔
          isInvolutionPerm π ∧ isLinearNoncrossingPerm π)
    (hCard :
      Fintype.card (LinearNoncrossingMatchingPerm (m + 1)) =
        motzkinNumber (m + 1)) :
    Fintype.card (WickCyclePairTightClassFormula m) = motzkinNumber (m + 1) := by
  rw [Fintype.card_congr
    (cyclePairTightClassFormulaEquivLinearNoncrossingMatching hClass), hCard]

/-- The noncrossing/Motzkin route reproduces the already-closed first
nontrivial simultaneous-geodesic count. -/
theorem card_WickCyclePairTightClassFormula_three_eq_motzkinNumber_four :
    Fintype.card (WickCyclePairTightClassFormula 3) = motzkinNumber 4 :=
  card_WickCyclePairTightClassFormula_eq_motzkinNumber_of_linearNoncrossing
    cyclePairTightFormulaPredicate_iff_linearNoncrossing_three
    card_LinearNoncrossingMatchingPerm_four

/-- Numerical form of the first nontrivial count through the
noncrossing/Motzkin route. -/
theorem card_WickCyclePairTightClassFormula_three_eq_nine_from_noncrossing :
    Fintype.card (WickCyclePairTightClassFormula 3) = 9 := by
  rw [card_WickCyclePairTightClassFormula_three_eq_motzkinNumber_four,
    motzkinNumber_four]

/-- Motzkin-form no-go for the old zero-defect envelope.  This is still
conditional on identifying the `m = 7` simultaneous-geodesic class with
`M₈`; it only removes the magic number `323` from the frontier statement. -/
theorem not_forall_tightFiberPackage_of_formula_seven_eq_motzkinNumber_eight
    (h7 : Fintype.card (WickCyclePairTightClassFormula 7) = motzkinNumber 8) :
    ¬ (∀ m : ℕ, ∀ Δ ∈ Finset.range (2 * m + 1),
      Nonempty (TightAubrunInnovationFiberPackage m Δ)) := by
  rw [motzkinNumber_eight] at h7
  exact not_forall_tightFiberPackage_of_formula_seven_eq_323 h7

/-- Final `m = 7` Motzkin-form no-go reduced to the two natural structural
inputs: the pointwise tight/noncrossing classification and the Motzkin count of
linear noncrossing matchings. -/
theorem not_forall_tightFiberPackage_of_linearNoncrossingClassification_seven
    (hClass :
      ∀ π : Equiv.Perm (Fin (7 + 1)),
        cyclePairTightFormulaPredicate 7 π ↔
          isInvolutionPerm π ∧ isLinearNoncrossingPerm π)
    (hCard :
      Fintype.card (LinearNoncrossingMatchingPerm (7 + 1)) =
        motzkinNumber (7 + 1)) :
    ¬ (∀ m : ℕ, ∀ Δ ∈ Finset.range (2 * m + 1),
      Nonempty (TightAubrunInnovationFiberPackage m Δ)) := by
  apply not_forall_tightFiberPackage_of_formula_seven_eq_motzkinNumber_eight
  simpa using
    card_WickCyclePairTightClassFormula_eq_motzkinNumber_of_linearNoncrossing
      (m := 7) hClass hCard

/-- Final `m = 7` no-go reduced to the pointwise tight/noncrossing
classification plus an explicit Motzkin-code equivalence for noncrossing
matchings. -/
theorem not_forall_tightFiberPackage_of_linearNoncrossingEquivMotzkinCode_seven
    (hClass :
      ∀ π : Equiv.Perm (Fin (7 + 1)),
        cyclePairTightFormulaPredicate 7 π ↔
          isInvolutionPerm π ∧ isLinearNoncrossingPerm π)
    (e : LinearNoncrossingMatchingPerm (7 + 1) ≃ MotzkinCode (7 + 1)) :
    ¬ (∀ m : ℕ, ∀ Δ ∈ Finset.range (2 * m + 1),
      Nonempty (TightAubrunInnovationFiberPackage m Δ)) := by
  exact not_forall_tightFiberPackage_of_linearNoncrossingClassification_seven
    hClass
    (card_LinearNoncrossingMatchingPerm_eq_motzkinNumber_of_equivMotzkinCode e)

end AppendixB
end PptFactorization
