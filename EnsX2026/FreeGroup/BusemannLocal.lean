import EnsX2026.FreeGroup.BusemannDef
import EnsX2026.FreeGroup.ReduceConcat
import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Busemann local-combinatorics: replacing the exam axioms by theorems

This module proves from first principles the three "admitted" facts in
`EnsX2026.FreeGroup.Busemann`, using the letter-append primitives in
`EnsX2026.FreeGroup.ReduceConcat`.

The theorems are given a `_thm` suffix so that downstream code can
incrementally migrate from the axiom to the theorem.
-/

namespace EnsX2026.FreeGroup

open scoped Classical
open EnsX2026.Cayley

namespace BusemannLocal

/-! ### The four letters of the alphabet of `F_2` -/

/-- The four letters of the alphabet of `F_2`. -/
def letters : Finset (Fin 2 × Bool) :=
  {(0, true), (0, false), (1, true), (1, false)}

lemma letters_card : letters.card = 4 := by
  decide

/-! ### The element `mk [ℓ]` as a generator -/

/-- `mk [(i, false)] = (of i)⁻¹`. -/
lemma mk_single_false (i : Fin 2) :
    _root_.FreeGroup.mk [(i, false)] = (_root_.FreeGroup.of i)⁻¹ := by
  have h1 : _root_.FreeGroup.mk [(i, true)] = _root_.FreeGroup.of i := rfl
  have h2 : (_root_.FreeGroup.of i)⁻¹ = (_root_.FreeGroup.mk [(i, true)])⁻¹ := by
    rw [h1]
  rw [h2, _root_.FreeGroup.inv_mk]
  rfl

/-- For every letter `ℓ`, the element `mk [ℓ]` lies in the generating set. -/
lemma mk_letter_mem_generating_set (ℓ : Fin 2 × Bool) :
    _root_.FreeGroup.mk [ℓ] ∈ F2_generating_set := by
  rcases ℓ with ⟨i, b⟩
  rcases b with _ | _
  · -- (i, false) = (of i)⁻¹
    rw [mk_single_false]
    fin_cases i
    · right; right; left; rfl
    · right; right; right; rfl
  · -- (i, true) = of i
    have : _root_.FreeGroup.mk [(i, true)] = _root_.FreeGroup.of i := rfl
    rw [this]
    fin_cases i
    · left; rfl
    · right; left; rfl

/-- `mk [ℓ] ≠ 1` for every letter. -/
lemma mk_letter_ne_one (ℓ : Fin 2 × Bool) :
    _root_.FreeGroup.mk [ℓ] ≠ (1 : F2) := by
  intro h
  have h' : ((_root_.FreeGroup.mk [ℓ]).toWord).length = 0 := by
    rw [h]; simp
  rw [_root_.FreeGroup.toWord_mk] at h'
  have : _root_.FreeGroup.IsReduced [ℓ] := by
    rw [_root_.FreeGroup.IsReduced]
    exact List.IsChain.singleton _
  rw [this.reduce_eq] at h'
  simp at h'

/-- Adjacency to `x * mk [ℓ]`. -/
lemma adj_mul_mk_letter (x : F2) (ℓ : Fin 2 × Bool) :
    (cayley_graph F2_generating_set).Adj x (x * _root_.FreeGroup.mk [ℓ]) :=
  EnsX2026.Cayley.cayley_graph_adj_mul F2_generating_set
    (mk_letter_mem_generating_set ℓ) (mk_letter_ne_one ℓ)

/-! ### Extracting a letter from adjacency -/

/-- For every adjacency `x ∼ y`, there exists a letter `ℓ` with
`y = x * mk [ℓ]`. -/
lemma exists_letter_of_adj {x y : F2}
    (hadj : (cayley_graph F2_generating_set).Adj x y) :
    ∃ ℓ : Fin 2 × Bool, y = x * _root_.FreeGroup.mk [ℓ] := by
  rw [EnsX2026.Cayley.cayley_graph_adj] at hadj
  obtain ⟨_, hcase⟩ := hadj
  rcases hcase with ⟨z, hz, hy⟩ | ⟨z, hz, hx⟩
  · -- y = x * z
    rcases hz with h | h | h | h
    · refine ⟨(0, true), ?_⟩; subst h; exact hy
    · refine ⟨(1, true), ?_⟩; subst h; exact hy
    · refine ⟨(0, false), ?_⟩
      subst h
      rw [hy, mk_single_false]
    · refine ⟨(1, false), ?_⟩
      subst h
      rw [hy, mk_single_false]
  · -- x = y * z, so y = x * z⁻¹
    have hyx : y = x * z⁻¹ := by rw [hx]; group
    rcases hz with h | h | h | h
    · refine ⟨(0, false), ?_⟩
      subst h
      rw [hyx, mk_single_false]
    · refine ⟨(1, false), ?_⟩
      subst h
      rw [hyx, mk_single_false]
    · refine ⟨(0, true), ?_⟩
      subst h
      rw [hyx]
      simp
      rfl
    · refine ⟨(1, true), ?_⟩
      subst h
      rw [hyx]
      simp
      rfl

/-! ### Computing `(x * mk [ℓ]).toWord` in the two cases -/

/-- Rewriting `x * mk [ℓ] = mk (x.toWord ++ [ℓ])`, used below. -/
lemma mul_mk_letter_eq_mk_append (x : F2) (ℓ : Fin 2 × Bool) :
    x * _root_.FreeGroup.mk [ℓ] = _root_.FreeGroup.mk (x.toWord ++ [ℓ]) := by
  conv_lhs =>
    rw [show x = _root_.FreeGroup.mk x.toWord from _root_.FreeGroup.mk_toWord.symm]
  rw [_root_.FreeGroup.mul_mk]

/-- Cancellation predicate between the last letter of `x` and `ℓ`. -/
def LastCancels (x : F2) (ℓ : Fin 2 × Bool) : Prop :=
  ∃ ℓ' ∈ x.toWord.getLast?, ℓ'.1 = ℓ.1 ∧ ℓ'.2 = !ℓ.2

/-- The non-cancellation predicate. -/
def NoLastCancel (x : F2) (ℓ : Fin 2 × Bool) : Prop :=
  ∀ ℓ' ∈ x.toWord.getLast?, ¬ (ℓ'.1 = ℓ.1 ∧ ℓ'.2 = !ℓ.2)

/-- If the last letter of `x` does not cancel with `ℓ`, then
`(x * mk [ℓ]).toWord = x.toWord ++ [ℓ]`. -/
lemma toWord_mul_mk_letter_noCancel (x : F2) (ℓ : Fin 2 × Bool)
    (h : NoLastCancel x ℓ) :
    (x * _root_.FreeGroup.mk [ℓ]).toWord = x.toWord ++ [ℓ] := by
  have ⟨_, hreduce⟩ :=
    _root_.FreeGroup.reduce_concat_of_not_cancel x.toWord ℓ
      _root_.FreeGroup.isReduced_toWord h
  rw [mul_mk_letter_eq_mk_append, _root_.FreeGroup.toWord_mk, hreduce]

/-- If the last letter of `x` cancels with `ℓ`, then
`(x * mk [ℓ]).toWord = x.toWord.dropLast`. -/
lemma toWord_mul_mk_letter_cancel (x : F2) (ℓ : Fin 2 × Bool)
    (h : LastCancels x ℓ) :
    (x * _root_.FreeGroup.mk [ℓ]).toWord = x.toWord.dropLast := by
  obtain ⟨ℓ', hℓ'_mem, hcancel⟩ := h
  -- `x.toWord = x.toWord.dropLast ++ [ℓ']`.
  have hsplit : x.toWord = x.toWord.dropLast ++ [ℓ'] :=
    (List.dropLast_append_getLast? ℓ' hℓ'_mem).symm
  -- Apply `reduce_concat_of_cancel`.
  have hreduced : _root_.FreeGroup.IsReduced (x.toWord.dropLast ++ [ℓ']) := by
    rw [← hsplit]
    exact _root_.FreeGroup.isReduced_toWord
  have hrec := _root_.FreeGroup.reduce_concat_of_cancel x.toWord.dropLast ℓ' ℓ
    hreduced hcancel
  rw [mul_mk_letter_eq_mk_append, _root_.FreeGroup.toWord_mk]
  conv_lhs => rw [hsplit]
  exact hrec

/-! ### Length of `(x * mk [ℓ]).toWord` in both cases -/

lemma length_toWord_mul_mk_letter_noCancel (x : F2) (ℓ : Fin 2 × Bool)
    (h : NoLastCancel x ℓ) :
    (x * _root_.FreeGroup.mk [ℓ]).toWord.length = x.toWord.length + 1 := by
  rw [toWord_mul_mk_letter_noCancel x ℓ h, List.length_append]
  simp

lemma length_toWord_mul_mk_letter_cancel (x : F2) (ℓ : Fin 2 × Bool)
    (h : LastCancels x ℓ) :
    (x * _root_.FreeGroup.mk [ℓ]).toWord.length = x.toWord.length - 1 := by
  rw [toWord_mul_mk_letter_cancel x ℓ h]
  -- `x.toWord.length - 1 = x.toWord.dropLast.length`.
  rw [List.length_dropLast]

/-! ### Length of `x.toWord` is positive when cancellation occurs -/

lemma length_pos_of_cancels {x : F2} {ℓ : Fin 2 × Bool}
    (h : LastCancels x ℓ) : 0 < x.toWord.length := by
  obtain ⟨ℓ', hmem, _⟩ := h
  rw [Option.mem_def] at hmem
  by_contra hnone
  push_neg at hnone
  have hzero : x.toWord.length = 0 := Nat.le_zero.mp hnone
  have hempty : x.toWord = [] := List.length_eq_zero_iff.mp hzero
  rw [hempty] at hmem
  simp at hmem

/-! ### Analyzing the common-prefix length under letter-append / dropLast

We now compute `common_prefix_length (x * mk [ℓ]) φ` in terms of
`m := common_prefix_length x φ` and `n := x.toWord.length`. There are four
sub-cases (non-cancel × on-ray, non-cancel × off-ray, cancel × on-ray,
cancel × off-ray).
-/

/-- **Monotonicity.** Suppose `y.toWord` has `x.toWord` as a prefix (i.e.
`y.toWord = x.toWord ++ tail`). Then every `p ≤ x.toWord.length` with
`PrefixMatches x φ p` also satisfies `PrefixMatches y φ p`. -/
lemma prefixMatches_of_append_left {x y : F2} {tail : List (Fin 2 × Bool)}
    {φ : ∂F2} {p : ℕ}
    (hy : y.toWord = x.toWord ++ tail)
    (hp : p ≤ x.toWord.length)
    (hpm : PrefixMatches x φ p) :
    PrefixMatches y φ p := by
  refine ⟨?_, ?_⟩
  · rw [hy]; simp [List.length_append]; omega
  · intro i hi
    rw [hy]
    rw [List.getElem?_append_left (lt_of_lt_of_le hi hp)]
    exact hpm.2 i hi

/-- If `y.toWord = x.toWord ++ tail` and `p ≤ x.toWord.length`, then
`PrefixMatches y φ p ↔ PrefixMatches x φ p`. -/
lemma prefixMatches_append_iff {x y : F2} {tail : List (Fin 2 × Bool)}
    {φ : ∂F2} {p : ℕ}
    (hy : y.toWord = x.toWord ++ tail)
    (hp : p ≤ x.toWord.length) :
    PrefixMatches y φ p ↔ PrefixMatches x φ p := by
  refine ⟨?_, prefixMatches_of_append_left hy hp⟩
  rintro ⟨_, hmatch⟩
  refine ⟨hp, ?_⟩
  intro i hi
  have hpi := hmatch i hi
  rw [hy, List.getElem?_append_left (lt_of_lt_of_le hi hp)] at hpi
  exact hpi

/-! #### Case A: non-cancellation, so `y.toWord = x.toWord ++ [ℓ]` -/

/-- In Case A (non-cancel) + on-ray (`m = n`), if `ℓ = φ.val n`, then
`common_prefix_length y φ = n + 1`; else `= n`. -/
lemma common_prefix_length_noCancel_on_ray
    (x : F2) (ℓ : Fin 2 × Bool) (φ : ∂F2)
    (h : NoLastCancel x ℓ)
    (hm : common_prefix_length x φ = x.toWord.length) :
    common_prefix_length (x * _root_.FreeGroup.mk [ℓ]) φ =
      if ℓ = φ.val x.toWord.length then x.toWord.length + 1 else x.toWord.length := by
  set n := x.toWord.length with hn_def
  set y := x * _root_.FreeGroup.mk [ℓ] with hy_def
  have hy_toWord : y.toWord = x.toWord ++ [ℓ] := toWord_mul_mk_letter_noCancel x ℓ h
  have hy_len : y.toWord.length = n + 1 := by
    rw [hy_toWord, List.length_append]
    rw [← hn_def]
    simp
  -- m = n means x.toWord agrees with the first n letters of φ.
  have hmatch_n : PrefixMatches x φ n := by
    have h_pm : PrefixMatches x φ (common_prefix_length x φ) := by
      by_cases hzero : common_prefix_length x φ = 0
      · refine ⟨?_, ?_⟩
        · rw [hzero]; exact Nat.zero_le _
        · intro i hi; rw [hzero] at hi; exact absurd hi (Nat.not_lt_zero _)
      · exact (Nat.findGreatest_eq_iff.mp rfl).2.1 hzero
    rw [hm] at h_pm
    exact h_pm
  split_ifs with hcase
  · -- ℓ = φ.val n → m(y, φ) = n + 1
    unfold common_prefix_length
    rw [hy_len, Nat.findGreatest_eq_iff]
    refine ⟨le_refl (n + 1), ?_, ?_⟩
    · intro _
      refine ⟨hy_len.ge, ?_⟩
      intro i hi
      rw [hy_toWord]
      by_cases hi_lt : i < n
      · rw [List.getElem?_append_left hi_lt]
        exact hmatch_n.2 i hi_lt
      · push_neg at hi_lt
        have hi_eq : i = n := by omega
        subst hi_eq
        rw [List.getElem?_append_right (le_refl _), Nat.sub_self]
        rw [List.getElem?_cons_zero]
        congr
    · intro k hk1 hk2
      omega
  · -- ℓ ≠ φ.val n → m(y, φ) = n.
    unfold common_prefix_length
    rw [hy_len, Nat.findGreatest_eq_iff]
    refine ⟨Nat.le_succ _, ?_, ?_⟩
    · intro _
      exact prefixMatches_of_append_left hy_toWord (le_refl _) hmatch_n
    · intro k hk1 hk2
      -- Only k = n + 1 is possible.
      have hk_eq : k = n + 1 := by omega
      subst hk_eq
      intro hpm
      -- PrefixMatches y φ (n+1) would imply ℓ = φ.val n.
      have := hpm.2 n (Nat.lt_succ_self _)
      rw [hy_toWord, List.getElem?_append_right (le_refl _), Nat.sub_self,
          List.getElem?_cons_zero] at this
      apply hcase
      exact Option.some_injective _ this

/-! #### Off-ray case (m < n) in non-cancellation -/

/-- `common_prefix_length x φ ≤ x.toWord.length`. -/
lemma common_prefix_length_le (x : F2) (φ : ∂F2) :
    common_prefix_length x φ ≤ x.toWord.length :=
  Nat.findGreatest_le _

/-- `PrefixMatches x φ (common_prefix_length x φ)` always holds. -/
lemma prefixMatches_common_prefix_length (x : F2) (φ : ∂F2) :
    PrefixMatches x φ (common_prefix_length x φ) := by
  by_cases h : common_prefix_length x φ = 0
  · refine ⟨?_, ?_⟩
    · rw [h]; exact Nat.zero_le _
    · intro i hi; rw [h] at hi; exact absurd hi (Nat.not_lt_zero _)
  · exact (Nat.findGreatest_eq_iff.mp rfl).2.1 h

/-- If `m := common_prefix_length x φ < n := x.toWord.length`, then
`x.toWord[m]? ≠ some (φ.val m)`. -/
lemma toWord_at_m_ne_phi_of_lt (x : F2) (φ : ∂F2)
    (hlt : common_prefix_length x φ < x.toWord.length) :
    x.toWord[common_prefix_length x φ]? ≠ some (φ.val (common_prefix_length x φ)) := by
  -- If the letters matched, we could extend the common prefix to length m+1.
  intro heq
  have h_pm : PrefixMatches x φ (common_prefix_length x φ) :=
    prefixMatches_common_prefix_length x φ
  have h_pm_succ : PrefixMatches x φ (common_prefix_length x φ + 1) := by
    refine ⟨hlt, ?_⟩
    intro i hi
    by_cases hi_lt : i < common_prefix_length x φ
    · exact h_pm.2 i hi_lt
    · have hi_eq : i = common_prefix_length x φ := by omega
      subst hi_eq
      exact heq
  have hle : common_prefix_length x φ + 1 ≤ common_prefix_length x φ := by
    show common_prefix_length x φ + 1 ≤
      Nat.findGreatest (PrefixMatches x φ) x.toWord.length
    exact Nat.le_findGreatest hlt h_pm_succ
  omega

/-- In Case A (non-cancel) + off-ray (`m < n`):
`common_prefix_length y φ = m`. -/
lemma common_prefix_length_noCancel_off_ray
    (x : F2) (ℓ : Fin 2 × Bool) (φ : ∂F2)
    (h : NoLastCancel x ℓ)
    (hlt : common_prefix_length x φ < x.toWord.length) :
    common_prefix_length (x * _root_.FreeGroup.mk [ℓ]) φ =
      common_prefix_length x φ := by
  set m := common_prefix_length x φ with hm_def
  set y := x * _root_.FreeGroup.mk [ℓ]
  have hy_toWord : y.toWord = x.toWord ++ [ℓ] := toWord_mul_mk_letter_noCancel x ℓ h
  have hy_len : y.toWord.length = x.toWord.length + 1 := by
    rw [hy_toWord, List.length_append]; simp
  -- Use findGreatest_eq_iff.
  unfold common_prefix_length
  rw [hy_len, Nat.findGreatest_eq_iff]
  refine ⟨?_, ?_, ?_⟩
  · exact le_trans (common_prefix_length_le x φ) (Nat.le_succ _)
  · intro _
    exact prefixMatches_of_append_left hy_toWord
      (common_prefix_length_le x φ)
      (prefixMatches_common_prefix_length x φ)
  · intro k hk1 hk2
    intro hpm
    -- hpm : PrefixMatches y φ k. Need to derive contradiction.
    -- Case k ≤ x.toWord.length: the same pattern holds for x, contradicting findGreatest.
    by_cases hk_le : k ≤ x.toWord.length
    · have hpx : PrefixMatches x φ k :=
        (prefixMatches_append_iff hy_toWord hk_le).mp hpm
      have hle : k ≤ common_prefix_length x φ := by
        show k ≤ Nat.findGreatest (PrefixMatches x φ) x.toWord.length
        exact Nat.le_findGreatest hk_le hpx
      rw [← hm_def] at hle
      omega
    · -- Case k > x.toWord.length: then k = x.toWord.length + 1.
      push_neg at hk_le
      have hk_eq : k = x.toWord.length + 1 := by omega
      subst hk_eq
      -- hpm forces match at index m (since m < x.toWord.length < k).
      have hm_lt_k : m < x.toWord.length + 1 := by omega
      have := hpm.2 m hm_lt_k
      rw [hy_toWord, List.getElem?_append_left hlt] at this
      exact toWord_at_m_ne_phi_of_lt x φ hlt this

/-! #### Case B: cancellation, so `y.toWord = x.toWord.dropLast` -/

/-- In the cancellation case, `y.toWord = x.toWord.dropLast`, so `y.toWord` is
a prefix of `x.toWord` of length `n - 1`. -/
lemma dropLast_append_getLast_cancel (x : F2) (ℓ : Fin 2 × Bool)
    (hc : LastCancels x ℓ) :
    ∃ ℓ' : Fin 2 × Bool, x.toWord = x.toWord.dropLast ++ [ℓ'] ∧
      (x * _root_.FreeGroup.mk [ℓ]).toWord = x.toWord.dropLast := by
  obtain ⟨ℓ', hℓ'_mem, hcancel⟩ := hc
  have hsplit : x.toWord = x.toWord.dropLast ++ [ℓ'] :=
    (List.dropLast_append_getLast? ℓ' hℓ'_mem).symm
  exact ⟨ℓ', hsplit, toWord_mul_mk_letter_cancel x ℓ ⟨ℓ', hℓ'_mem, hcancel⟩⟩

/-- In Case B (cancel) + on-ray (`m = n`):
`common_prefix_length y φ = n - 1`. -/
lemma common_prefix_length_cancel_on_ray
    (x : F2) (ℓ : Fin 2 × Bool) (φ : ∂F2)
    (hc : LastCancels x ℓ)
    (hm : common_prefix_length x φ = x.toWord.length) :
    common_prefix_length (x * _root_.FreeGroup.mk [ℓ]) φ =
      x.toWord.length - 1 := by
  set n := x.toWord.length with hn_def
  have hn_pos : 0 < n := length_pos_of_cancels hc
  set y := x * _root_.FreeGroup.mk [ℓ]
  have hy_toWord : y.toWord = x.toWord.dropLast :=
    toWord_mul_mk_letter_cancel x ℓ hc
  have hy_len : y.toWord.length = n - 1 := by
    rw [hy_toWord, List.length_dropLast]
  -- PrefixMatches x φ n (since m = n).
  have hmatch_n : PrefixMatches x φ n := by
    have h_pm := prefixMatches_common_prefix_length x φ
    rw [hm] at h_pm
    exact h_pm
  unfold common_prefix_length
  rw [hy_len, Nat.findGreatest_eq_iff]
  refine ⟨le_refl _, ?_, ?_⟩
  · intro _
    refine ⟨hy_len.ge, ?_⟩
    intro i hi
    rw [hy_toWord]
    -- y.toWord = x.toWord.dropLast, so y.toWord[i]? = x.toWord[i]? for i < n - 1.
    have hdrop_get :
        x.toWord.dropLast[i]? = x.toWord[i]? := by
      -- dropLast[i]? = l[i]? for i < dropLast.length
      rw [List.getElem?_dropLast]
      split
      · rfl
      · omega
    rw [hdrop_get]
    exact hmatch_n.2 i (by omega)
  · intro k hk1 hk2
    omega

/-- In Case B (cancel) + off-ray (`m < n`):
`common_prefix_length y φ = m`. -/
lemma common_prefix_length_cancel_off_ray
    (x : F2) (ℓ : Fin 2 × Bool) (φ : ∂F2)
    (hc : LastCancels x ℓ)
    (hlt : common_prefix_length x φ < x.toWord.length) :
    common_prefix_length (x * _root_.FreeGroup.mk [ℓ]) φ =
      common_prefix_length x φ := by
  set m := common_prefix_length x φ with hm_def
  have hn_pos : 0 < x.toWord.length := length_pos_of_cancels hc
  set y := x * _root_.FreeGroup.mk [ℓ]
  have hy_toWord : y.toWord = x.toWord.dropLast :=
    toWord_mul_mk_letter_cancel x ℓ hc
  have hy_len : y.toWord.length = x.toWord.length - 1 := by
    rw [hy_toWord, List.length_dropLast]
  -- m ≤ n - 1: we have m < n and we'll show m ≤ n - 1. Need m < n ⇒ m ≤ n-1.
  have hm_le : m ≤ x.toWord.length - 1 := by omega
  -- PrefixMatches x φ m implies PrefixMatches y φ m via dropLast.
  have h_pm_x : PrefixMatches x φ m := by
    rw [hm_def]; exact prefixMatches_common_prefix_length x φ
  have h_pm_y : PrefixMatches y φ m := by
    refine ⟨?_, ?_⟩
    · rw [hy_len]; exact hm_le
    · intro i hi
      rw [hy_toWord]
      have hdrop_get : x.toWord.dropLast[i]? = x.toWord[i]? := by
        rw [List.getElem?_dropLast]
        split
        · rfl
        · omega
      rw [hdrop_get]
      exact h_pm_x.2 i hi
  unfold common_prefix_length
  rw [hy_len, Nat.findGreatest_eq_iff]
  refine ⟨hm_le, ?_, ?_⟩
  · intro _; exact h_pm_y
  · intro k hk1 hk2 hpm_y
    -- hpm_y : PrefixMatches y φ k. This forces PrefixMatches x φ k via prepending back.
    have hk_le_x : k ≤ x.toWord.length := by omega
    -- y.toWord is a prefix of x.toWord of length n-1.
    have hy_is_prefix : x.toWord = y.toWord ++ [x.toWord.getLast (by
      intro h_empty; rw [h_empty] at hn_pos; simp at hn_pos)] := by
      rw [hy_toWord]
      exact (List.dropLast_append_getLast _).symm
    have h_pm_x_k : PrefixMatches x φ k := by
      refine ⟨hk_le_x, ?_⟩
      intro i hi
      have := hpm_y.2 i hi
      rw [hy_toWord] at this
      have hdrop_get : x.toWord.dropLast[i]? = x.toWord[i]? := by
        rw [List.getElem?_dropLast]
        split
        · rfl
        · omega
      rw [hdrop_get] at this
      exact this
    have hle : k ≤ common_prefix_length x φ := by
      show k ≤ Nat.findGreatest (PrefixMatches x φ) x.toWord.length
      exact Nat.le_findGreatest hk_le_x h_pm_x_k
    rw [← hm_def] at hle
    omega

/-! ### Busemann differences: the ±1 transition

We now collect the four cases into a single `busemann_diff` lemma. -/

-- In each of the four cases (A.1, A.2, B.1, B.2), `busemann φ y - busemann φ x ∈ {-1, +1}`.
-- We state the four subcases separately for usability.

/-- Case A.1 sub-cases: non-cancel + on-ray, ℓ = φ.val n → busemann decreases. -/
lemma busemann_diff_noCancel_on_ray_toward
    (x : F2) (ℓ : Fin 2 × Bool) (φ : ∂F2)
    (h : NoLastCancel x ℓ)
    (hm : common_prefix_length x φ = x.toWord.length)
    (hℓ : ℓ = φ.val x.toWord.length) :
    busemann φ (x * _root_.FreeGroup.mk [ℓ]) = busemann φ x - 1 := by
  unfold busemann
  rw [length_toWord_mul_mk_letter_noCancel x ℓ h,
      common_prefix_length_noCancel_on_ray x ℓ φ h hm]
  simp [hℓ, hm]
  push_cast
  ring

/-- Case A.1 other sub-case: non-cancel + on-ray, ℓ ≠ φ.val n → busemann increases. -/
lemma busemann_diff_noCancel_on_ray_away
    (x : F2) (ℓ : Fin 2 × Bool) (φ : ∂F2)
    (h : NoLastCancel x ℓ)
    (hm : common_prefix_length x φ = x.toWord.length)
    (hℓ : ℓ ≠ φ.val x.toWord.length) :
    busemann φ (x * _root_.FreeGroup.mk [ℓ]) = busemann φ x + 1 := by
  unfold busemann
  rw [length_toWord_mul_mk_letter_noCancel x ℓ h,
      common_prefix_length_noCancel_on_ray x ℓ φ h hm]
  rw [if_neg hℓ]
  rw [hm]
  push_cast
  ring

/-- Case A.2: non-cancel + off-ray → busemann increases. -/
lemma busemann_diff_noCancel_off_ray
    (x : F2) (ℓ : Fin 2 × Bool) (φ : ∂F2)
    (h : NoLastCancel x ℓ)
    (hlt : common_prefix_length x φ < x.toWord.length) :
    busemann φ (x * _root_.FreeGroup.mk [ℓ]) = busemann φ x + 1 := by
  unfold busemann
  rw [length_toWord_mul_mk_letter_noCancel x ℓ h,
      common_prefix_length_noCancel_off_ray x ℓ φ h hlt]
  push_cast
  ring

/-- Case B.1: cancel + on-ray → busemann increases. -/
lemma busemann_diff_cancel_on_ray
    (x : F2) (ℓ : Fin 2 × Bool) (φ : ∂F2)
    (hc : LastCancels x ℓ)
    (hm : common_prefix_length x φ = x.toWord.length) :
    busemann φ (x * _root_.FreeGroup.mk [ℓ]) = busemann φ x + 1 := by
  have hn_pos : 0 < x.toWord.length := length_pos_of_cancels hc
  unfold busemann
  rw [length_toWord_mul_mk_letter_cancel x ℓ hc,
      common_prefix_length_cancel_on_ray x ℓ φ hc hm]
  rw [hm]
  have : ((x.toWord.length - 1 : ℕ) : ℤ) = (x.toWord.length : ℤ) - 1 := by
    have := Nat.sub_one_add_one (Nat.ne_of_gt hn_pos)
    push_cast
    omega
  rw [this]
  ring

/-- Case B.2: cancel + off-ray → busemann decreases. -/
lemma busemann_diff_cancel_off_ray
    (x : F2) (ℓ : Fin 2 × Bool) (φ : ∂F2)
    (hc : LastCancels x ℓ)
    (hlt : common_prefix_length x φ < x.toWord.length) :
    busemann φ (x * _root_.FreeGroup.mk [ℓ]) = busemann φ x - 1 := by
  have hn_pos : 0 < x.toWord.length := length_pos_of_cancels hc
  unfold busemann
  rw [length_toWord_mul_mk_letter_cancel x ℓ hc,
      common_prefix_length_cancel_off_ray x ℓ φ hc hlt]
  have : ((x.toWord.length - 1 : ℕ) : ℤ) = (x.toWord.length : ℤ) - 1 := by
    push_cast
    omega
  rw [this]
  ring

/-! ### Combining: Busemann value of every neighbour is ±1 -/

/-- **Every neighbour has Busemann value ±1.** -/
theorem busemann_other_neighbours_thm (φ : ∂F2) (x : F2) :
    ∀ (y : F2), (cayley_graph F2_generating_set).Adj x y →
      busemann φ y = busemann φ x - 1 ∨ busemann φ y = busemann φ x + 1 := by
  intro y hadj
  obtain ⟨ℓ, hy⟩ := exists_letter_of_adj hadj
  subst hy
  -- Dispatch: cancel vs non-cancel; on-ray vs off-ray.
  by_cases hc : LastCancels x ℓ
  · -- Case B: cancel
    by_cases hray : common_prefix_length x φ = x.toWord.length
    · right; exact busemann_diff_cancel_on_ray x ℓ φ hc hray
    · have hlt : common_prefix_length x φ < x.toWord.length := by
        have := common_prefix_length_le x φ
        omega
      left; exact busemann_diff_cancel_off_ray x ℓ φ hc hlt
  · -- Case A: no cancel
    have hnc : NoLastCancel x ℓ := by
      intro ℓ' hmem hcontra
      exact hc ⟨ℓ', hmem, hcontra⟩
    by_cases hray : common_prefix_length x φ = x.toWord.length
    · by_cases hℓ : ℓ = φ.val x.toWord.length
      · left; exact busemann_diff_noCancel_on_ray_toward x ℓ φ hnc hray hℓ
      · right; exact busemann_diff_noCancel_on_ray_away x ℓ φ hnc hray hℓ
    · have hlt : common_prefix_length x φ < x.toWord.length := by
        have := common_prefix_length_le x φ
        omega
      right; exact busemann_diff_noCancel_off_ray x ℓ φ hnc hlt

/-! ### Identifying the unique toward-φ letter

For the `busemann_neighbour_structure` axiom, we need to single out the
unique `ℓ` such that `busemann φ (x * mk [ℓ]) = busemann φ x - 1`.

Per the case analysis:
* If `m = n` (on-ray): the unique letter is `ℓ = φ.val n` (non-cancel case);
  no other letter decreases the Busemann value.
* If `m < n` (off-ray): the unique letter is the one that cancels, i.e.
  `ℓ = (last.1, !last.2)` where `last = x.toWord.getLast`.
-/

/-- On the on-ray case (m = n): if `ℓ` gives `busemann y = busemann x - 1`,
then `ℓ = φ.val n` and `NoLastCancel x ℓ`. -/
lemma letter_toward_on_ray_iff
    (x : F2) (ℓ : Fin 2 × Bool) (φ : ∂F2)
    (hm : common_prefix_length x φ = x.toWord.length) :
    busemann φ (x * _root_.FreeGroup.mk [ℓ]) = busemann φ x - 1 ↔
      (NoLastCancel x ℓ ∧ ℓ = φ.val x.toWord.length) := by
  constructor
  · intro h_dec
    by_cases hc : LastCancels x ℓ
    · -- cancel + on-ray gives +1, contradiction.
      have h_inc := busemann_diff_cancel_on_ray x ℓ φ hc hm
      rw [h_inc] at h_dec
      exfalso; omega
    · have hnc : NoLastCancel x ℓ := fun ℓ' hm hcontra => hc ⟨ℓ', hm, hcontra⟩
      refine ⟨hnc, ?_⟩
      by_contra hne
      have h_inc := busemann_diff_noCancel_on_ray_away x ℓ φ hnc hm hne
      rw [h_inc] at h_dec
      exfalso; omega
  · rintro ⟨hnc, hℓ⟩
    exact busemann_diff_noCancel_on_ray_toward x ℓ φ hnc hm hℓ

/-- On the off-ray case (m < n): if `ℓ` gives `busemann y = busemann x - 1`,
then `LastCancels x ℓ`. -/
lemma letter_toward_off_ray_iff
    (x : F2) (ℓ : Fin 2 × Bool) (φ : ∂F2)
    (hlt : common_prefix_length x φ < x.toWord.length) :
    busemann φ (x * _root_.FreeGroup.mk [ℓ]) = busemann φ x - 1 ↔
      LastCancels x ℓ := by
  constructor
  · intro h_dec
    by_cases hc : LastCancels x ℓ
    · exact hc
    · -- no cancel + off-ray gives +1.
      have hnc : NoLastCancel x ℓ := fun ℓ' hm hcontra => hc ⟨ℓ', hm, hcontra⟩
      have h_inc := busemann_diff_noCancel_off_ray x ℓ φ hnc hlt
      rw [h_inc] at h_dec
      exfalso; omega
  · intro hc
    exact busemann_diff_cancel_off_ray x ℓ φ hc hlt

/-! ### Injectivity: distinct letters give distinct vertices -/

/-- If `ℓ ≠ ℓ'`, then `x * mk [ℓ] ≠ x * mk [ℓ']`. -/
lemma mul_mk_letter_injective {x : F2} {ℓ ℓ' : Fin 2 × Bool}
    (hne : ℓ ≠ ℓ') :
    x * _root_.FreeGroup.mk [ℓ] ≠ x * _root_.FreeGroup.mk [ℓ'] := by
  intro heq
  have hcancel := mul_left_cancel heq
  apply hne
  -- mk [ℓ] = mk [ℓ'] implies toWord equal.
  have hred_ℓ : _root_.FreeGroup.reduce [ℓ] = [ℓ] := by
    have : _root_.FreeGroup.IsReduced [ℓ] := by
      rw [_root_.FreeGroup.IsReduced]; exact List.IsChain.singleton _
    exact this.reduce_eq
  have hred_ℓ' : _root_.FreeGroup.reduce [ℓ'] = [ℓ'] := by
    have : _root_.FreeGroup.IsReduced [ℓ'] := by
      rw [_root_.FreeGroup.IsReduced]; exact List.IsChain.singleton _
    exact this.reduce_eq
  have htw : (_root_.FreeGroup.mk [ℓ]).toWord = (_root_.FreeGroup.mk [ℓ']).toWord := by
    rw [hcancel]
  rw [_root_.FreeGroup.toWord_mk, _root_.FreeGroup.toWord_mk,
      hred_ℓ, hred_ℓ'] at htw
  exact List.singleton_inj.mp htw

/-! ### Existence and uniqueness of the toward-φ neighbour -/

/-- **Existence of a toward-φ neighbour.** -/
theorem exists_toward_phi_neighbour (φ : ∂F2) (x : F2) :
    ∃ y : F2, (cayley_graph F2_generating_set).Adj x y ∧
      busemann φ y = busemann φ x - 1 := by
  by_cases hray : common_prefix_length x φ = x.toWord.length
  · -- on-ray: take ℓ = φ.val n, with no cancellation.
    set n := x.toWord.length with hn_def
    set ℓ := φ.val n
    -- Need NoLastCancel x ℓ. Check: if cancel, last = (ℓ.1, !ℓ.2) = (φ.val n).1, !(φ.val n).2.
    -- But since on-ray, x.toWord's last letter = φ.val (n-1). For NonCancellation,
    -- φ.val (n-1) and φ.val n don't cancel.
    have hnc : NoLastCancel x ℓ := by
      intro ℓ' hmem hcontra
      rw [Option.mem_def] at hmem
      -- ℓ' = x.toWord.getLast? = some (x.toWord.getLast _)
      -- For on-ray, the last letter of x.toWord equals φ.val (n-1) (if n > 0).
      by_cases hn_pos : 0 < n
      · -- x.toWord.length > 0. So x.toWord.getLast = x.toWord[n-1] = φ.val (n-1).
        have hmatch : PrefixMatches x φ n := by
          have := prefixMatches_common_prefix_length x φ
          rw [hray] at this; exact this
        have hlast_eq : x.toWord[n-1]? = some (φ.val (n-1)) := hmatch.2 (n-1) (by omega)
        have hlast_eq2 : x.toWord.getLast? = some (φ.val (n-1)) := by
          rw [List.getLast?_eq_getElem?]
          have hlen_eq : x.toWord.length - 1 = n - 1 := by rw [hn_def]
          rw [hlen_eq, hlast_eq]
        rw [hmem] at hlast_eq2
        have : ℓ' = φ.val (n-1) := Option.some_injective _ hlast_eq2
        subst this
        -- hcontra : ℓ'.1 = ℓ.1 ∧ ℓ'.2 = !ℓ.2 where ℓ = φ.val n.
        -- So φ.val (n-1) cancels with φ.val n. But NonCancellation (φ.val (n-1)) (φ.val n).
        have h_nc := φ.property (n-1)
        have hn_sub : n - 1 + 1 = n := by omega
        rw [hn_sub] at h_nc
        rcases h_nc with h | h
        · exact h hcontra.1
        · -- h : (φ.val (n-1)).2 = (φ.val n).2. But hcontra.2 : (φ.val (n-1)).2 = !(φ.val n).2.
          rw [h] at hcontra
          have : (φ.val n).2 = !(φ.val n).2 := hcontra.2
          cases hb : (φ.val n).2 <;> rw [hb] at this <;> simp at this
      · -- n = 0: x.toWord = [], getLast? = none, hmem contradicts.
        push_neg at hn_pos
        have hn0 : n = 0 := Nat.le_zero.mp hn_pos
        have hempty : x.toWord = [] := List.length_eq_zero_iff.mp hn0
        rw [hempty] at hmem
        simp at hmem
    refine ⟨x * _root_.FreeGroup.mk [ℓ], ?_, ?_⟩
    · exact adj_mul_mk_letter x ℓ
    · exact busemann_diff_noCancel_on_ray_toward x ℓ φ hnc hray rfl
  · -- off-ray: take ℓ that cancels with x.toWord.getLast.
    have hlt : common_prefix_length x φ < x.toWord.length := by
      have := common_prefix_length_le x φ
      omega
    have hn_pos : 0 < x.toWord.length := by
      have := common_prefix_length_le x φ; omega
    have hne : x.toWord ≠ [] :=
      fun h => by rw [h] at hn_pos; simp at hn_pos
    set last := x.toWord.getLast hne
    set ℓ : Fin 2 × Bool := (last.1, !last.2)
    have hmem : last ∈ x.toWord.getLast? := by
      rw [List.getLast?_eq_getLast_of_ne_nil hne]
      rfl
    have hc : LastCancels x ℓ := ⟨last, hmem, by
      refine ⟨?_, ?_⟩
      · rfl
      · -- Goal: last.2 = !ℓ.2 where ℓ.2 = !last.2. So !ℓ.2 = last.2.
        show last.2 = !(!last.2)
        cases last.2 <;> rfl⟩
    refine ⟨x * _root_.FreeGroup.mk [ℓ], ?_, ?_⟩
    · exact adj_mul_mk_letter x ℓ
    · exact busemann_diff_cancel_off_ray x ℓ φ hc hlt

/-- **Uniqueness of the toward-φ neighbour.** -/
theorem busemann_neighbour_structure_thm (φ : ∂F2) (x : F2) :
    ∃! (y : F2), (cayley_graph F2_generating_set).Adj x y ∧
      busemann φ y = busemann φ x - 1 := by
  classical
  obtain ⟨y, hy_adj, hy_bus⟩ := exists_toward_phi_neighbour φ x
  refine ⟨y, ⟨hy_adj, hy_bus⟩, ?_⟩
  rintro y' ⟨hy'_adj, hy'_bus⟩
  -- Extract letters for y and y'.
  obtain ⟨ℓ, hy_eq⟩ := exists_letter_of_adj hy_adj
  obtain ⟨ℓ', hy'_eq⟩ := exists_letter_of_adj hy'_adj
  -- Dispatch on on-ray vs off-ray.
  by_cases hray : common_prefix_length x φ = x.toWord.length
  · -- on-ray: both ℓ and ℓ' must be φ.val n (and no cancel).
    have h_ℓ : ℓ = φ.val x.toWord.length := by
      have h := hy_bus
      rw [hy_eq] at h
      exact ((letter_toward_on_ray_iff x ℓ φ hray).mp h).2
    have h_ℓ' : ℓ' = φ.val x.toWord.length := by
      have h := hy'_bus
      rw [hy'_eq] at h
      exact ((letter_toward_on_ray_iff x ℓ' φ hray).mp h).2
    rw [hy_eq, hy'_eq, h_ℓ, h_ℓ']
  · -- off-ray: both ℓ and ℓ' must cancel. In the off-ray case, the unique
    -- cancelling letter is (last.1, !last.2).
    have hlt : common_prefix_length x φ < x.toWord.length := by
      have := common_prefix_length_le x φ; omega
    have hn_pos : 0 < x.toWord.length := by
      have := common_prefix_length_le x φ; omega
    have hne : x.toWord ≠ [] :=
      fun h => by rw [h] at hn_pos; simp at hn_pos
    have hc : LastCancels x ℓ := by
      have h := hy_bus
      rw [hy_eq] at h
      exact (letter_toward_off_ray_iff x ℓ φ hlt).mp h
    have hc' : LastCancels x ℓ' := by
      have h := hy'_bus
      rw [hy'_eq] at h
      exact (letter_toward_off_ray_iff x ℓ' φ hlt).mp h
    -- Both cancel: so ℓ.1 = last.1, ℓ.2 = !last.2, and similarly ℓ'. Hence ℓ = ℓ'.
    obtain ⟨a, ha_mem, ha_cancel⟩ := hc
    obtain ⟨a', ha'_mem, ha'_cancel⟩ := hc'
    -- a = a' = x.toWord.getLast (same last letter)
    have hlast := List.getLast?_eq_getLast_of_ne_nil hne
    rw [hlast] at ha_mem ha'_mem
    rw [Option.mem_def] at ha_mem ha'_mem
    have ha_eq : a = x.toWord.getLast hne := Option.some_injective _ ha_mem.symm
    have ha'_eq : a' = x.toWord.getLast hne := Option.some_injective _ ha'_mem.symm
    have ha_aa' : a = a' := ha_eq.trans ha'_eq.symm
    subst ha_aa'
    -- ℓ.1 = a.1, ℓ'.1 = a.1 ⇒ ℓ.1 = ℓ'.1
    -- ℓ.2 = !a.2, ℓ'.2 = !a.2 ⇒ ℓ.2 = ℓ'.2
    have hℓ_fst_eq_ℓ'_fst : ℓ.1 = ℓ'.1 := ha_cancel.1.symm.trans ha'_cancel.1
    have hℓ_snd' : ℓ.2 = ℓ'.2 := by
      have hA : a.2 = !ℓ.2 := ha_cancel.2
      have hB : a.2 = !ℓ'.2 := ha'_cancel.2
      have hAB : (!ℓ.2) = (!ℓ'.2) := hA.symm.trans hB
      cases hb : ℓ.2 <;> cases hb' : ℓ'.2 <;> rw [hb, hb'] at hAB <;> simp_all
    have hℓeq : ℓ = ℓ' := Prod.ext hℓ_fst_eq_ℓ'_fst hℓ_snd'
    rw [hy_eq, hy'_eq, hℓeq]

/-! ### Three-element away-set -/

/-- The four letters as a concrete Finset. -/
def fourLetters : Finset (Fin 2 × Bool) :=
  {((0, true) : Fin 2 × Bool), ((0, false) : Fin 2 × Bool),
   ((1, true) : Fin 2 × Bool), ((1, false) : Fin 2 × Bool)}

lemma fourLetters_card : fourLetters.card = 4 := by decide

lemma mem_fourLetters (ℓ : Fin 2 × Bool) : ℓ ∈ fourLetters := by
  rcases ℓ with ⟨i, b⟩
  fin_cases i <;> cases b <;> decide

/-- **Three-element away-set for `busemann_three_plus_neighbours`.** -/
theorem busemann_three_plus_neighbours_thm (φ : ∂F2) (x : F2) :
    ∃ T : Finset F2,
      T.card = 3 ∧
      (∀ y ∈ T, (cayley_graph F2_generating_set).Adj x y ∧
                busemann φ y = busemann φ x + 1) ∧
      (∀ y, (cayley_graph F2_generating_set).Adj x y →
          busemann φ y = busemann φ x - 1 ∨ y ∈ T) := by
  classical
  -- Get the unique toward-φ neighbour.
  obtain ⟨y_to, ⟨hy_to_adj, hy_to_bus⟩, hy_to_unique⟩ :=
    busemann_neighbour_structure_thm φ x
  -- Extract its letter.
  obtain ⟨ℓ_to, hy_to_eq⟩ := exists_letter_of_adj hy_to_adj
  -- Let the three other letters be `fourLetters \ {ℓ_to}`.
  let other_letters : Finset (Fin 2 × Bool) := fourLetters.erase ℓ_to
  have h_other_card : other_letters.card = 3 := by
    rw [Finset.card_erase_of_mem (mem_fourLetters ℓ_to), fourLetters_card]
  -- The three-element Finset `T`: image of these letters under `fun ℓ => x * mk [ℓ]`.
  let T : Finset F2 := other_letters.image (fun ℓ => x * _root_.FreeGroup.mk [ℓ])
  have h_inj :
      Set.InjOn (fun ℓ : Fin 2 × Bool => x * _root_.FreeGroup.mk [ℓ])
        other_letters := by
    intro ℓ₁ _ ℓ₂ _ heq
    by_contra hne
    exact mul_mk_letter_injective hne heq
  have h_T_card : T.card = 3 := by
    rw [Finset.card_image_of_injOn h_inj, h_other_card]
  refine ⟨T, h_T_card, ?_, ?_⟩
  · -- Each y in T has adj x y and b(y) = b(x) + 1.
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨ℓ, hℓ_mem, hyeq⟩ := hy
    rw [Finset.mem_erase] at hℓ_mem
    obtain ⟨hℓ_ne, _⟩ := hℓ_mem
    subst hyeq
    refine ⟨adj_mul_mk_letter x ℓ, ?_⟩
    -- b(x * mk [ℓ]) = b(x) + 1 since ℓ ≠ ℓ_to (the unique toward letter).
    -- Case: any y' ∼ x has b = b(x) - 1 ∨ b = b(x) + 1.
    have hobus := busemann_other_neighbours_thm φ x (x * _root_.FreeGroup.mk [ℓ])
      (adj_mul_mk_letter x ℓ)
    rcases hobus with hminus | hplus
    · exfalso
      -- Then x * mk [ℓ] = y_to by uniqueness.
      have : x * _root_.FreeGroup.mk [ℓ] = y_to := by
        have := hy_to_unique (x * _root_.FreeGroup.mk [ℓ])
          ⟨adj_mul_mk_letter x ℓ, hminus⟩
        exact this
      -- Then x * mk [ℓ] = x * mk [ℓ_to], so ℓ = ℓ_to (by injectivity).
      rw [hy_to_eq] at this
      exact hℓ_ne (by_contra fun h => mul_mk_letter_injective h this)
    · exact hplus
  · -- Every neighbour y ∼ x is either the toward-φ one or belongs to T.
    intro y hadj
    have hobus := busemann_other_neighbours_thm φ x y hadj
    rcases hobus with hminus | hplus
    · left; exact hminus
    · right
      -- y = x * mk [ℓ] for some letter ℓ.
      obtain ⟨ℓ, hy_eq⟩ := exists_letter_of_adj hadj
      -- ℓ ≠ ℓ_to, because ℓ_to gives -1 and ℓ gives +1.
      have hℓ_ne_to : ℓ ≠ ℓ_to := by
        intro h_eq
        subst h_eq
        -- Then y = y_to (from hy_eq and hy_to_eq).
        have : y = y_to := hy_eq.trans hy_to_eq.symm
        rw [this] at hplus
        rw [hy_to_bus] at hplus
        exfalso; omega
      rw [Finset.mem_image]
      refine ⟨ℓ, ?_, hy_eq.symm⟩
      rw [Finset.mem_erase]
      exact ⟨hℓ_ne_to, mem_fourLetters ℓ⟩

end BusemannLocal

end EnsX2026.FreeGroup
