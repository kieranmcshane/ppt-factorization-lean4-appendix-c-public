import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# `reduce_concat_reduced` — the cancellation-at-tail dichotomy

When we append a single letter `ℓ` to a reduced word `L`, there are two cases
controlling what `FreeGroup.reduce` does:

* **Non-cancellation.** If `L`'s last letter does not form a cancelling pair
  with `ℓ`, the word `L ++ [ℓ]` is already reduced, and `reduce (L ++ [ℓ]) = L ++ [ℓ]`.
* **Cancellation.** If `L = L' ++ [ℓ']` is reduced and `ℓ` cancels with `ℓ'`
  (same generator, opposite polarity), then `reduce ((L' ++ [ℓ']) ++ [ℓ]) = L'`.

Both statements are elementary but are not readily available in Mathlib; they
are the "tail-step" primitive on which reduced-word constructions such as
infinite-word Busemann functions rely.
-/

namespace FreeGroup

open List

variable {α : Type*} [DecidableEq α]

/-- If `L` is reduced and its last letter does *not* cancel with `ℓ`, then
appending `ℓ` leaves the word reduced and in particular equal to its own
reduction. -/
theorem isReduced_concat_of_not_cancel {α : Type*}
    (L : List (α × Bool)) (ℓ : α × Bool)
    (hL : IsReduced L)
    (hne : ∀ ℓ' ∈ L.getLast?, ¬ (ℓ'.1 = ℓ.1 ∧ ℓ'.2 = !ℓ.2)) :
    IsReduced (L ++ [ℓ]) := by
  -- `IsReduced` is an `IsChain`; glue via `IsChain.append`.
  refine IsChain.append hL IsReduced.singleton ?_
  intro ℓ' hℓ' y hy
  -- `y = ℓ` since the second list is `[ℓ]` hence `head? = some ℓ`.
  rw [List.head?_cons, Option.mem_some_iff] at hy
  subst hy
  -- Turn the non-cancellation hypothesis `hne` on `ℓ'` into the chain relation.
  have hnc : ¬ (ℓ'.1 = ℓ.1 ∧ ℓ'.2 = !ℓ.2) := hne ℓ' hℓ'
  -- The chain relation for `IsReduced` is: `a.1 = b.1 → a.2 = b.2`.
  intro h1
  -- If `ℓ'.2 ≠ ℓ.2`, then `ℓ'.2 = !ℓ.2`, contradicting `hnc`.
  by_contra hne2
  apply hnc
  refine ⟨h1, ?_⟩
  cases hb : ℓ.2 <;> cases hb' : ℓ'.2 <;> simp_all

/-- The non-cancellation case of `reduce_concat`: if `L` is reduced and its
last letter does not cancel with `ℓ`, then `reduce (L ++ [ℓ]) = L ++ [ℓ]`. -/
theorem reduce_concat_of_not_cancel
    (L : List (α × Bool)) (ℓ : α × Bool)
    (hL : IsReduced L)
    (hne : ∀ ℓ' ∈ L.getLast?, ¬ (ℓ'.1 = ℓ.1 ∧ ℓ'.2 = !ℓ.2)) :
    IsReduced (L ++ [ℓ]) ∧ reduce (L ++ [ℓ]) = L ++ [ℓ] := by
  have hR : IsReduced (L ++ [ℓ]) := isReduced_concat_of_not_cancel L ℓ hL hne
  exact ⟨hR, hR.reduce_eq⟩

/-- The cancellation case of `reduce_concat`: if `L = L' ++ [ℓ']` is reduced and
`ℓ` cancels with `ℓ'` (same generator, opposite polarity), then
`reduce ((L' ++ [ℓ']) ++ [ℓ]) = L'`. -/
theorem reduce_concat_of_cancel
    (L' : List (α × Bool)) (ℓ' ℓ : α × Bool)
    (hL : IsReduced (L' ++ [ℓ']))
    (hcancel : ℓ'.1 = ℓ.1 ∧ ℓ'.2 = !ℓ.2) :
    reduce ((L' ++ [ℓ']) ++ [ℓ]) = L' := by
  -- Unfold `ℓ'` and `ℓ` into matching `(x, b) / (x, !b)` shape.
  obtain ⟨x', b'⟩ := ℓ'
  obtain ⟨x, b⟩ := ℓ
  obtain ⟨hx, hb⟩ := hcancel
  -- `hx : x' = x`, `hb : b' = !b`.
  dsimp only at hx hb
  subst hx
  subst hb
  -- We have a one-step reduction `L' ++ [(x', !b), (x', b)] ~>₁ L'` via `Red.Step.not_rev`
  -- or equivalently `Red.Step.not` with `b ↦ !b`.
  have hstep : Red.Step ((L' ++ [(x', !b)]) ++ [(x', b)]) L' := by
    rw [List.append_assoc]
    -- Shape: `L' ++ ((x', !b) :: (x', b) :: [])`.
    -- Invoke `Red.Step.not_rev` with `x = x'`, `b = b`, `L₁ = L'`, `L₂ = []`.
    have := @Red.Step.not_rev α L' [] x' b
    simpa using this
  -- Reduction preserves `reduce`; `L'` is reduced, so `reduce L' = L'`.
  have hL' : IsReduced L' := hL.infix ⟨[], [(x', !b)], by simp⟩
  calc reduce ((L' ++ [(x', !b)]) ++ [(x', b)])
      = reduce L' := reduce.Step.eq hstep
    _ = L' := hL'.reduce_eq

/-! ### Wave 23A.1 — `IsReduced` API for cancellation indicators

The lemmas below extend the `IsReduced` API in directions needed by the
common-prefix sublinearity proof (Q43). They are pure list/FreeGroup
combinatorics with no probabilistic content.

Mathlib already supplies:

* `FreeGroup.IsReduced.singleton`     (lemma 1 of the wave plan)
* `FreeGroup.toWord_mk`               (`(mk L).toWord = reduce L`)
* `FreeGroup.IsReduced.reduce_eq`     (`reduce L = L` for reduced `L`)
* `FreeGroup.IsReduced.infix`         (sublist closure of `IsReduced`)

The local file above already provides:

* `FreeGroup.isReduced_concat_of_not_cancel` (lemma 2: append a non-cancelling letter)

What follows is the genuinely new material:

* `FreeGroup.IsReduced.dropLast`      (lemma 3: drop the last letter)
* `FreeGroup.toWord_mk_of_isReduced`  (lemma 4: `(mk L).toWord = L` when reduced)

For lemmas 5 and 6 (word-length identities for `x * mk [ℓ]`), this file is
upstream of `BusemannLocal.lean`, which already supplies them under the names
`length_toWord_mul_mk_letter_noCancel` and `length_toWord_mul_mk_letter_cancel`.
We do not duplicate them here. -/

/-- Dropping the last letter of a reduced word leaves it reduced. -/
lemma _root_.FreeGroup.IsReduced.dropLast {α : Type*}
    {L : List (α × Bool)} (hL : _root_.FreeGroup.IsReduced L) :
    _root_.FreeGroup.IsReduced L.dropLast :=
  hL.infix L.dropLast_prefix.isInfix

/-- For a reduced list `L`, the canonical word of `mk L` is `L` itself. -/
lemma _root_.FreeGroup.toWord_mk_of_isReduced {α : Type*} [DecidableEq α]
    {L : List (α × Bool)} (hL : _root_.FreeGroup.IsReduced L) :
    (_root_.FreeGroup.mk L).toWord = L := by
  rw [_root_.FreeGroup.toWord_mk, hL.reduce_eq]

end FreeGroup

namespace EnsX2026.FreeGroup

/-!
The wrapper names used elsewhere in the `EnsX2026` library, re-exported from
the `FreeGroup` namespace for discoverability.
-/

export _root_.FreeGroup
  (reduce_concat_of_not_cancel reduce_concat_of_cancel isReduced_concat_of_not_cancel
   toWord_mk_of_isReduced)

end EnsX2026.FreeGroup
