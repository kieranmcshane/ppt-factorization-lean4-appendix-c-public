import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Data.Nat.Find
import Mathlib.Data.Set.Finite.List
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import EnsX2026.Cayley.Growth
import EnsX2026.Graphs.Laplacian_l2
import EnsX2026.FreeGroup.TreeAndGrowth
import EnsX2026.FreeGroup.ReduceConcat
import EnsX2026.FreeGroup.BusemannDef
import EnsX2026.FreeGroup.BusemannLocal

/-!
# ENS/Polytechnique 2026 Math A — The Busemann function on `F_2`
  and the Poisson kernel `p_φ(x) = 3^{-b_φ(x)}` (Q39–Q41)

Let `F_2 = FreeGroup (Fin 2)` with canonical generators
`a = FreeGroup.of 0` and `b = FreeGroup.of 1`. Its Cayley graph
`Γ = cayley_graph F2_generating_set` (with
`F2_generating_set = {a, b, a⁻¹, b⁻¹}`) is the 4-regular tree.

## Boundary

Infinite reduced words on the symmetric generating set
`Z = {a, b, a⁻¹, b⁻¹}` are exactly sequences
`φ : ℕ → (Fin 2) × Bool` such that no two consecutive letters cancel,
i.e. for every `n`,
`¬ (φ n).1 = (φ (n+1)).1 ∨ (φ n).2 = (φ (n+1)).2`.
The set of such sequences is the boundary `∂F₂`.

## Busemann function

For `x ∈ F_2` with reduced word `x_1 … x_k` and `φ ∈ ∂F₂`, set
`m(x, φ) := max { p ≤ k : the first p letters of x.toWord agree with
                  the first p letters of φ }`.
The **Busemann function** is
`b_φ(x) := k − 2 m(x, φ)`.
Its sign convention: `b_φ(x) < 0` means `x` lies on the ray towards `φ`,
and `b_φ(x) > 0` means `x` is "far" from `φ`.

## Admitted facts (from the exam)

The exam allows one to admit that for every vertex `x ∈ F_2`, among the
four neighbours in `Γ`,
* exactly one (the "neighbour toward `φ`") satisfies
  `b_φ(y) = b_φ(x) − 1`;
* the other three satisfy `b_φ(y) = b_φ(x) + 1`.

We record these as `axiom`s and use them to prove the harmonicity of the
Poisson kernel.

## Status

* **Q39** — `poisson_kernel_at_one` is proved. `poisson_kernel_harmonic_eq`
  (the pointwise "four-neighbour" harmonicity equation) is fully proved
  from the admitted axioms. The limit conditions along rays
  (`poisson_kernel_along_phi_blowup` and
  `poisson_kernel_along_other_vanish`) are now fully proved by linking
  `valPrefix` to `toWord` via the fact that `prefixList φ p` is already
  reduced; the Poisson kernel along `φ` itself equals `3^p`, and along
  any other ray it is eventually `3^(2q) · (1/3)^p` which tends to `0`.
* **Q40** — `poisson_kernel_unique` is *assembled* and sorry-free,
  closed via Route (a) in
  `EnsX2026.FreeGroup.TreeBoundedHarmonicVanish` (see
  `harmonic_vanishes_of_global_shell_decay`).  Finite-tree max
  principle on the ball (`sup_on_F2_ball_le_sup_on_shell` and its
  symmetric `neg_sup_on_F2_ball_le_sup_on_shell`) is fully proved in
  this file.  The local max/min propagation step
  (`harmonic_max_propagation_step` / `harmonic_min_propagation_step`:
  max/min over four neighbours propagates to each neighbour) is fully
  proved.  The Wave 15A companion axiom
  `tree_bounded_harmonic_vanishes` and the Wave 22F.2.2 axiom
  `translated_walk_limit_identification` (Cartwright-Soardi /
  Furstenberg) — previously required because the originally planned
  sub-lemma `sup_on_shell_tendsto_zero` is **not** provable from mere
  pointwise ray convergence (shells of cardinality `~4 · 3^{R-1}`
  need uniform-in-ψ control) — were both removed in Wave 22F.3 by
  strengthening the hypothesis of `poisson_kernel_unique` to
  uniform shell decay of `f − p_φ`.  Finite-ball infrastructure
  (`F2_ball`, `F2_ball_finset`, `F2_shell_finset`) is provided.
* **Q41** — `poisson_kernels_linearly_independent` is fully proved, by
  evaluating along each ray and using that only `p_{φ_i}` blows up
  while every other ratio vanishes.

Institut Fourier, Grenoble — Kieran McShane
-/

namespace EnsX2026.FreeGroup

open scoped Classical
open EnsX2026.Cayley

/-! ### Definitions moved to `EnsX2026.FreeGroup.BusemannDef`

`genA`, `genB`, `NonCancellation`, `F2_boundary` (notation `∂F2`),
`F2_boundary.eval`, `F2_boundary.prefixList`, `F2_boundary.valPrefix`,
`PrefixMatches`, `common_prefix_length`, and `busemann` now live in
`EnsX2026.FreeGroup.BusemannDef`, imported above. This split breaks a
circular dependency with `EnsX2026.FreeGroup.BusemannLocal`, which
proves the neighbour-structure facts stated below. -/

/-! ### Busemann neighbour structure (theorems forwarding to `BusemannLocal`)

In the Cayley graph `Γ = cayley_graph F2_generating_set` (a 4-regular tree),
every vertex has exactly four neighbours. Given `φ ∈ ∂F₂`, among the four
neighbours of a vertex `x ∈ F_2`, exactly one — the one "toward `φ`" — has
Busemann value `b_φ(x) − 1`, and the other three have Busemann value
`b_φ(x) + 1`.

These three facts were axioms in the exam statement. They are now proved
from first principles in `EnsX2026.FreeGroup.BusemannLocal` (via the
primitives of `EnsX2026.FreeGroup.ReduceConcat`). We retain the names
here as one-line forwarders so that downstream consumers written against
the exam-style axiom API keep compiling unchanged. -/

/-- For every `x ∈ F_2` and every `φ ∈ ∂F₂`, there is a unique neighbour
`y ∼ x` with `b_φ(y) = b_φ(x) − 1`. Proved in `BusemannLocal`. -/
theorem busemann_neighbour_structure (φ : ∂F2) (x : F2) :
    ∃! (y : F2), (cayley_graph F2_generating_set).Adj x y ∧
      busemann φ y = busemann φ x - 1 :=
  BusemannLocal.busemann_neighbour_structure_thm φ x

/-- Every neighbour `y ∼ x` has Busemann value `b_φ(x) ± 1`. Proved in
`BusemannLocal`. -/
theorem busemann_other_neighbours (φ : ∂F2) (x : F2) :
    ∀ (y : F2), (cayley_graph F2_generating_set).Adj x y →
      busemann φ y = busemann φ x - 1 ∨ busemann φ y = busemann φ x + 1 :=
  BusemannLocal.busemann_other_neighbours_thm φ x

/-- The Cayley graph of `F_2` is 4-regular: there is a three-element set
`T` of outward (b_φ + 1) neighbours, and every neighbour is either toward-φ
or in `T`. Proved in `BusemannLocal`. -/
theorem busemann_three_plus_neighbours (φ : ∂F2) (x : F2) :
    ∃ T : Finset F2,
      T.card = 3 ∧
      (∀ y ∈ T, (cayley_graph F2_generating_set).Adj x y ∧
                busemann φ y = busemann φ x + 1) ∧
      (∀ y, (cayley_graph F2_generating_set).Adj x y →
          busemann φ y = busemann φ x - 1 ∨ y ∈ T) :=
  BusemannLocal.busemann_three_plus_neighbours_thm φ x

/-! ### Busemann at the identity -/

/-- The reduced word of the identity is empty, hence `|1| = 0`. -/
@[simp] lemma toWord_length_one :
    ((1 : F2).toWord).length = 0 := by
  simp [_root_.FreeGroup.toWord_one]

/-- The only `p ≤ 0` is `p = 0`, and `PrefixMatches _ _ 0` always holds;
hence `common_prefix_length 1 φ = 0`. -/
@[simp] lemma common_prefix_length_one (φ : ∂F2) :
    common_prefix_length (1 : F2) φ = 0 := by
  unfold common_prefix_length
  rw [toWord_length_one]
  rfl

/-- `b_φ(1) = 0`. -/
@[simp] lemma busemann_one (φ : ∂F2) : busemann φ (1 : F2) = 0 := by
  simp [busemann]

/-! ### Q39 — The Poisson kernel `p_φ(x) = 3^{-b_φ(x)}` -/

/-- The **Poisson kernel** `p_φ(x) = 3^{−b_φ(x)} = (1/3)^{b_φ(x)}`,
as a real-valued function on `F_2`. Values live in `ℝ` because the
exponent is an integer. -/
noncomputable def poisson_kernel (φ : ∂F2) (x : F2) : ℝ :=
  (3 : ℝ) ^ (-(busemann φ x))

/-- **Q39(a).** At the identity, `p_φ(1) = 1` because `b_φ(1) = 0`. -/
theorem poisson_kernel_at_one (φ : ∂F2) :
    poisson_kernel φ (1 : F2) = 1 := by
  unfold poisson_kernel
  simp

/-! #### Harmonicity (pointwise, via the admitted neighbour structure)

The crucial calculation: at each vertex `x`, the 4 neighbours split into
one neighbour with Busemann value `b_φ(x) − 1` and three neighbours with
Busemann value `b_φ(x) + 1`. Hence

  `Σ_{y ∼ x} p_φ(y) = 3^{−(b−1)} + 3 · 3^{−(b+1)}
                    = 3 · 3^{−b} + 3^{−b} = 4 · 3^{−b} = 4 · p_φ(x)`,

i.e. `(Δp_φ)(x) = 4 · p_φ(x) − Σ_{y∼x} p_φ(y) = 0`. -/

/-- The sum of `p_φ` over the admitted "one toward + three outward"
neighbour configuration equals `4 · p_φ(x)`. This is the key identity. -/
theorem poisson_kernel_neighbour_sum (φ : ∂F2) (x : F2) :
    ∀ (yφ : F2) (T : Finset F2),
      busemann φ yφ = busemann φ x - 1 →
      (∀ y ∈ T, busemann φ y = busemann φ x + 1) →
      T.card = 3 →
      yφ ∉ T →
      poisson_kernel φ yφ + (∑ y ∈ T, poisson_kernel φ y)
        = 4 * poisson_kernel φ x := by
  intro yφ T hyφ hT hTcard hnotmem
  -- Denote b := b_φ(x) (as integer).
  set b : ℤ := busemann φ x with hb_def
  -- p_φ(yφ) = 3^{-(b-1)} = 3 · 3^{-b}
  have h_yφ : poisson_kernel φ yφ = 3 * poisson_kernel φ x := by
    unfold poisson_kernel
    rw [hyφ]
    have : (3 : ℝ) ^ (-(b - 1)) = (3 : ℝ) ^ (1 + (-b)) := by
      congr 1; ring
    rw [this, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  -- For each y in T, p_φ(y) = 3^{-(b+1)} = (1/3) · 3^{-b}
  have h_T_each : ∀ y ∈ T, poisson_kernel φ y = (1 / 3) * poisson_kernel φ x := by
    intro y hy
    unfold poisson_kernel
    rw [hT y hy]
    have h1 : (3 : ℝ) ^ (-(b + 1)) = (3 : ℝ) ^ ((-1) + (-b)) := by
      congr 1; ring
    rw [h1, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    have h2 : (3 : ℝ) ^ ((-1 : ℤ)) = 1 / 3 := by
      rw [zpow_neg, zpow_one]; ring
    rw [h2]
  -- Sum over T of 1/3 · p_φ(x) equals card(T) · (1/3) · p_φ(x) = 3 · (1/3) · p_φ(x)
  have h_T_sum : (∑ y ∈ T, poisson_kernel φ y) = poisson_kernel φ x := by
    calc (∑ y ∈ T, poisson_kernel φ y)
        = ∑ y ∈ T, (1 / 3) * poisson_kernel φ x := by
            apply Finset.sum_congr rfl
            intro y hy
            exact h_T_each y hy
      _ = (T.card : ℝ) * ((1 / 3) * poisson_kernel φ x) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ = 3 * ((1 / 3) * poisson_kernel φ x) := by
            rw [hTcard]; norm_num
      _ = poisson_kernel φ x := by ring
  -- Now combine:
  rw [h_yφ, h_T_sum]; ring

/-- **Q39(b) — pointwise harmonicity.** For every vertex `x`, the sum of
`p_φ` over the four neighbours of `x` equals `4 · p_φ(x)`. This is the
"harmonic equation" for `p_φ` w.r.t. the combinatorial Laplacian on a
4-regular graph.

More precisely, we state it in terms of the admitted neighbour structure:
the four neighbours split as `yφ + T` with `|T| = 3`, and the sum formula
`p_φ(yφ) + Σ_{y∈T} p_φ(y) = 4 · p_φ(x)` holds. -/
theorem poisson_kernel_harmonic_eq (φ : ∂F2) (x : F2) :
    ∃ (yφ : F2) (T : Finset F2),
      (cayley_graph F2_generating_set).Adj x yφ ∧
      busemann φ yφ = busemann φ x - 1 ∧
      T.card = 3 ∧
      (∀ y ∈ T, (cayley_graph F2_generating_set).Adj x y ∧
                busemann φ y = busemann φ x + 1) ∧
      yφ ∉ T ∧
      poisson_kernel φ yφ + (∑ y ∈ T, poisson_kernel φ y)
        = 4 * poisson_kernel φ x := by
  obtain ⟨yφ, ⟨hyφ_adj, hyφ_bus⟩, _hyφ_unique⟩ :=
    busemann_neighbour_structure φ x
  obtain ⟨T, hTcard, hT_mem, _hT_cover⟩ :=
    busemann_three_plus_neighbours φ x
  refine ⟨yφ, T, hyφ_adj, hyφ_bus, hTcard, hT_mem, ?_, ?_⟩
  · -- yφ ∉ T because yφ satisfies b(yφ) = b(x) - 1, while every y ∈ T has
    -- b(y) = b(x) + 1, and these are distinct integers.
    intro hmem
    have h1 : busemann φ yφ = busemann φ x - 1 := hyφ_bus
    have h2 : busemann φ yφ = busemann φ x + 1 := (hT_mem yφ hmem).2
    have : busemann φ x - 1 = busemann φ x + 1 := h1.symm.trans h2
    have : (-1 : ℤ) = 1 := by linarith
    exact absurd this (by decide)
  · apply poisson_kernel_neighbour_sum φ x yφ T hyφ_bus
    · intro y hy; exact (hT_mem y hy).2
    · exact hTcard
    · -- same as before
      intro hmem
      have h1 : busemann φ yφ = busemann φ x - 1 := hyφ_bus
      have h2 : busemann φ yφ = busemann φ x + 1 := (hT_mem yφ hmem).2
      have hx : busemann φ x - 1 = busemann φ x + 1 := h1.symm.trans h2
      have : (-1 : ℤ) = 1 := by linarith
      exact absurd this (by decide)

/-! #### Limit conditions along boundary rays

The Poisson kernel `p_φ` "blows up" along the ray to `φ` (because
`b_φ(φ.valPrefix p) = -p`) and vanishes along any other ray `ψ ≠ φ`
(because `common_prefix_length (ψ.valPrefix p) φ` is eventually equal
to the first-disagreement index `q` of `ψ` and `φ`, hence
`b_φ(ψ.valPrefix p) = p − 2·q → +∞` and `p_φ = 3^{-b} → 0`).

To formalise this we first link `valPrefix` to `toWord`, via the fact
that `prefixList φ p` is already reduced (an immediate consequence of
`φ`'s `NonCancellation` property). -/

section LimitAlongRays

open Filter Topology

/-- `getElem?` at index `i < p` of `prefixList φ p` is `some (φ.val i)`. -/
private lemma F2_boundary.prefixList_getElem? (φ : ∂F2) {p i : ℕ} (hi : i < p) :
    (F2_boundary.prefixList φ p)[i]? = some (φ.val i) := by
  unfold F2_boundary.prefixList
  rw [List.getElem?_map, List.getElem?_range hi]
  rfl

/-- The prefix word `prefixList φ p` has no two consecutive cancelling
letters: it is `IsReduced`. -/
lemma F2_boundary.prefixList_isReduced (φ : ∂F2) (p : ℕ) :
    _root_.FreeGroup.IsReduced (F2_boundary.prefixList φ p) := by
  -- `IsReduced L := L.IsChain (fun a b => a.1 = b.1 → a.2 = b.2)`.
  -- `NonCancellation p q := p.1 ≠ q.1 ∨ p.2 = q.2` is equivalent.
  -- Use `isChain_iff_forall_rel_of_append_cons_cons`.
  unfold _root_.FreeGroup.IsReduced
  rw [List.isChain_iff_forall_rel_of_append_cons_cons]
  -- Goal: ∀ a b l₁ l₂, prefixList φ p = l₁ ++ a :: b :: l₂ → (a.1 = b.1 → a.2 = b.2).
  intro a b l₁ l₂ heq
  -- Let `k := l₁.length`. Then in `prefixList φ p`, the entry at index `k` is `a`
  -- and at index `k+1` is `b`. Combine with `prefixList_getElem?`.
  have hlen_p : (F2_boundary.prefixList φ p).length = p :=
    F2_boundary.prefixList_length φ p
  have hk1_lt : l₁.length + 1 < p := by
    have hh := hlen_p
    rw [heq] at hh
    -- (l₁ ++ a :: b :: l₂).length = l₁.length + (2 + l₂.length) = p.
    have := hh
    rw [List.length_append] at this
    simp [List.length_cons] at this
    omega
  have hk_lt : l₁.length < p := Nat.lt_of_succ_lt hk1_lt
  -- Extract a = φ.val l₁.length.
  have ha : a = φ.val l₁.length := by
    have h1 : (F2_boundary.prefixList φ p)[l₁.length]? = some a := by
      rw [heq]
      rw [List.getElem?_append_right (Nat.le_refl _)]
      rw [Nat.sub_self]
      rfl
    have h2 := F2_boundary.prefixList_getElem? (φ := φ) hk_lt
    exact Option.some_injective _ (h1.symm.trans h2)
  -- Extract b = φ.val (l₁.length + 1).
  have hb : b = φ.val (l₁.length + 1) := by
    have h1 : (F2_boundary.prefixList φ p)[l₁.length + 1]? = some b := by
      rw [heq]
      rw [List.getElem?_append_right (Nat.le_succ _)]
      rw [show l₁.length + 1 - l₁.length = 1 from by omega]
      rfl
    have h2 := F2_boundary.prefixList_getElem? (φ := φ) hk1_lt
    exact Option.some_injective _ (h1.symm.trans h2)
  subst ha
  subst hb
  intro heq1
  -- Now apply NonCancellation (φ.val l₁.length) (φ.val (l₁.length + 1)).
  have hnc : NonCancellation (φ.val l₁.length) (φ.val (l₁.length + 1)) :=
    φ.property l₁.length
  rcases hnc with hne | heq2
  · exact absurd heq1 hne
  · exact heq2

/-- The reduced word of `valPrefix φ p` is exactly `prefixList φ p`. -/
lemma F2_boundary.toWord_valPrefix (φ : ∂F2) (p : ℕ) :
    (F2_boundary.valPrefix φ p).toWord = F2_boundary.prefixList φ p := by
  unfold F2_boundary.valPrefix
  rw [_root_.FreeGroup.toWord_mk]
  exact (F2_boundary.prefixList_isReduced φ p).reduce_eq

/-- The reduced-word length of `valPrefix φ p` equals `p`. -/
lemma F2_boundary.length_toWord_valPrefix (φ : ∂F2) (p : ℕ) :
    ((F2_boundary.valPrefix φ p).toWord).length = p := by
  rw [F2_boundary.toWord_valPrefix, F2_boundary.prefixList_length]

/-- At every index `i < p`, the `i`-th letter of `(valPrefix φ p).toWord`
is `φ.val i`. -/
lemma F2_boundary.toWord_valPrefix_getElem? (φ : ∂F2) (p i : ℕ) (hi : i < p) :
    ((F2_boundary.valPrefix φ p).toWord)[i]? = some (φ.val i) := by
  rw [F2_boundary.toWord_valPrefix]
  exact F2_boundary.prefixList_getElem? (φ := φ) hi

/-- Along `φ` itself, every prefix of length `p` matches `φ` to depth `p`. -/
lemma prefixMatches_valPrefix_self (φ : ∂F2) (p : ℕ) :
    PrefixMatches (F2_boundary.valPrefix φ p) φ p := by
  refine ⟨?_, ?_⟩
  · rw [F2_boundary.length_toWord_valPrefix]
  · intro i hi
    exact F2_boundary.toWord_valPrefix_getElem? φ p i hi

/-- Along `φ` itself, the common-prefix length is exactly `p`. -/
lemma common_prefix_length_valPrefix_self (φ : ∂F2) (p : ℕ) :
    common_prefix_length (F2_boundary.valPrefix φ p) φ = p := by
  unfold common_prefix_length
  rw [F2_boundary.length_toWord_valPrefix]
  exact Nat.findGreatest_eq (prefixMatches_valPrefix_self φ p)

/-- Busemann of `valPrefix φ p` w.r.t. `φ` itself equals `-p`. -/
lemma busemann_valPrefix_self (φ : ∂F2) (p : ℕ) :
    busemann φ (F2_boundary.valPrefix φ p) = -(p : ℤ) := by
  unfold busemann
  rw [F2_boundary.length_toWord_valPrefix, common_prefix_length_valPrefix_self]
  ring

/-- Along the ray toward `φ`, `p_φ` blows up to `+∞`. -/
theorem poisson_kernel_along_phi_blowup (φ : ∂F2) :
    Filter.Tendsto (fun p : ℕ => poisson_kernel φ (φ.valPrefix p))
      Filter.atTop Filter.atTop := by
  -- `b_φ(φ.valPrefix p) = -p` ⇒ `p_φ(φ.valPrefix p) = 3^p`. Apply
  -- `tendsto_pow_atTop_atTop_of_one_lt` at `r = 3`.
  have h_eq : ∀ p : ℕ, poisson_kernel φ (φ.valPrefix p) = (3 : ℝ) ^ p := by
    intro p
    unfold poisson_kernel
    rw [busemann_valPrefix_self]
    -- `(3 : ℝ) ^ (-(-(p : ℤ))) = (3 : ℝ) ^ (p : ℤ) = (3 : ℝ) ^ p`
    simp [zpow_natCast]
  refine Tendsto.congr (fun p => (h_eq p).symm) ?_
  exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 3)

/-! Now the vanishing case. For `ψ ≠ φ`, they differ at some first
index; call the smallest such index `q`. Then for `p ≥ q + 1`, the
word `(valPrefix ψ p).toWord = prefixList ψ p` agrees with `φ` on the
first `q` letters but disagrees at position `q`. Hence
`common_prefix_length (valPrefix ψ p) φ = q`, so
`busemann φ (valPrefix ψ p) = p − 2q`, and the Poisson kernel is
`3^(2q − p) = 3^(2q) · (1/3)^p → 0`. -/

/-- If `ψ ≠ φ` (as boundary points), there exists a smallest index at
which the two sequences disagree. -/
lemma exists_first_diff (φ ψ : ∂F2) (hne : ψ ≠ φ) :
    ∃ q : ℕ, (∀ i, i < q → ψ.val i = φ.val i) ∧ ψ.val q ≠ φ.val q := by
  -- The set `{n | ψ.val n ≠ φ.val n}` is nonempty (else `ψ.val = φ.val`,
  -- hence `ψ = φ` by subtype extensionality), so `Nat.find` picks its min.
  classical
  have h_exists : ∃ n, ψ.val n ≠ φ.val n := by
    by_contra h_all
    push_neg at h_all
    apply hne
    apply Subtype.ext
    funext n
    exact h_all n
  refine ⟨Nat.find h_exists, ?_, Nat.find_spec h_exists⟩
  intro i hi
  by_contra h_ne
  exact Nat.find_min h_exists hi h_ne

/-- For `p ≥ q + 1`, `common_prefix_length (valPrefix ψ p) φ = q`, where
`q` is the first index at which `ψ` and `φ` disagree. -/
lemma common_prefix_length_valPrefix_other
    (φ ψ : ∂F2) (q : ℕ) (hq_agree : ∀ i, i < q → ψ.val i = φ.val i)
    (hq_diff : ψ.val q ≠ φ.val q) {p : ℕ} (hp : q + 1 ≤ p) :
    common_prefix_length (F2_boundary.valPrefix ψ p) φ = q := by
  unfold common_prefix_length
  rw [F2_boundary.length_toWord_valPrefix]
  -- Use `findGreatest_eq_iff`.
  rw [Nat.findGreatest_eq_iff]
  refine ⟨?_, ?_, ?_⟩
  · -- q ≤ p
    exact Nat.le_of_succ_le hp
  · -- q ≠ 0 → PrefixMatches _ _ q
    intro _hqne
    refine ⟨?_, ?_⟩
    · rw [F2_boundary.length_toWord_valPrefix]
      exact Nat.le_of_succ_le hp
    · intro i hi
      rw [F2_boundary.toWord_valPrefix_getElem? ψ p i (lt_of_lt_of_le hi (Nat.le_of_succ_le hp))]
      rw [hq_agree i hi]
  · -- For n with q < n ≤ p, ¬ PrefixMatches _ _ n.
    intro n hqn hnp hP
    obtain ⟨_hle, hmatch⟩ := hP
    -- Apply hmatch at index q (which is < n).
    have hq_val : ((F2_boundary.valPrefix ψ p).toWord)[q]? = some (φ.val q) :=
      hmatch q hqn
    have hq_val' : ((F2_boundary.valPrefix ψ p).toWord)[q]? = some (ψ.val q) :=
      F2_boundary.toWord_valPrefix_getElem? ψ p q (lt_of_lt_of_le hqn hnp)
    have hsome : some (ψ.val q) = some (φ.val q) := hq_val'.symm.trans hq_val
    have h_eq : ψ.val q = φ.val q := Option.some_injective _ hsome
    exact hq_diff h_eq

/-- Busemann of `valPrefix ψ p` w.r.t. `φ` for `p ≥ q + 1`. -/
lemma busemann_valPrefix_other
    (φ ψ : ∂F2) (q : ℕ) (hq_agree : ∀ i, i < q → ψ.val i = φ.val i)
    (hq_diff : ψ.val q ≠ φ.val q) {p : ℕ} (hp : q + 1 ≤ p) :
    busemann φ (F2_boundary.valPrefix ψ p) = (p : ℤ) - 2 * (q : ℤ) := by
  unfold busemann
  rw [F2_boundary.length_toWord_valPrefix,
    common_prefix_length_valPrefix_other φ ψ q hq_agree hq_diff hp]

/-- Along any other ray `ψ ≠ φ`, `p_φ` tends to zero. -/
theorem poisson_kernel_along_other_vanish (φ ψ : ∂F2) (hψ : ψ ≠ φ) :
    Filter.Tendsto (fun p : ℕ => poisson_kernel φ (ψ.valPrefix p))
      Filter.atTop (nhds (0 : ℝ)) := by
  obtain ⟨q, hq_agree, hq_diff⟩ := exists_first_diff φ ψ hψ
  -- For p ≥ q + 1:
  --   poisson_kernel φ (ψ.valPrefix p) = 3^(-(p - 2q))
  --                                    = 3^(2q) · (1/3)^p.
  -- The factor `3^(2q)` is a constant; `(1/3)^p → 0`.
  set C : ℝ := (3 : ℝ) ^ (2 * q) with hC_def
  have h_eq : ∀ p : ℕ, q + 1 ≤ p →
      poisson_kernel φ (ψ.valPrefix p) = C * ((1 / 3 : ℝ) ^ p) := by
    intro p hp
    unfold poisson_kernel
    rw [busemann_valPrefix_other φ ψ q hq_agree hq_diff hp]
    -- Goal: (3 : ℝ) ^ (-((p : ℤ) - 2 * q)) = C * (1/3)^p.
    have h1 : (3 : ℝ) ^ (-((p : ℤ) - 2 * (q : ℤ)))
        = (3 : ℝ) ^ ((2 * (q : ℤ)) + (-(p : ℤ))) := by
      congr 1; ring
    rw [h1, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    have h2 : (3 : ℝ) ^ (2 * (q : ℤ)) = C := by
      rw [hC_def]
      rw [show (2 * (q : ℤ) : ℤ) = ((2 * q : ℕ) : ℤ) by push_cast; ring]
      rw [zpow_natCast]
    rw [h2]
    -- Goal: C * (3 : ℝ) ^ (-(p : ℤ)) = C * (1/3)^p.
    congr 1
    -- `(3 : ℝ) ^ (-(p : ℤ)) = ((3 : ℝ)^p)⁻¹ = (3⁻¹)^p = (1/3)^p`.
    rw [zpow_neg, zpow_natCast, ← inv_pow,
      show (3 : ℝ)⁻¹ = 1 / 3 by norm_num]
  -- Tendsto (1/3)^p atTop (nhds 0):
  have h_tend : Filter.Tendsto (fun p : ℕ => ((1 / 3 : ℝ)) ^ p)
      Filter.atTop (nhds 0) := by
    apply tendsto_pow_atTop_nhds_zero_of_lt_one
    · norm_num
    · norm_num
  have h_tend_mul : Filter.Tendsto
      (fun p : ℕ => C * ((1 / 3 : ℝ)) ^ p) Filter.atTop (nhds (C * 0)) :=
    h_tend.const_mul C
  rw [mul_zero] at h_tend_mul
  -- Use congruence on the tail `p ≥ q + 1`.
  refine Tendsto.congr' ?_ h_tend_mul
  refine Filter.eventually_atTop.mpr ⟨q + 1, ?_⟩
  intro p hp
  exact (h_eq p hp).symm

end LimitAlongRays

/-! ### Q40 — Uniqueness of the Poisson kernel

The Poisson kernel `p_φ` is uniquely characterised by its harmonicity,
its value at the identity, and the vanishing-along-other-rays condition.

The proof goes via the discrete maximum principle on finite truncations
of the tree `F_2`: for each truncation depth `q`, the difference
`f - p_φ` is harmonic on the truncation, bounded, and vanishes on the
boundary (except possibly in the direction of `φ`, where `f` and `p_φ`
have the same blow-up behaviour). Taking `q → ∞` forces `f = p_φ`
everywhere.

We state the theorem; its proof is assembled from the local
propagation step (fully proved) and the Wave 15A companion axiom
`tree_bounded_harmonic_vanishes` (see below). -/

/-- Auxiliary: "pointwise harmonicity" predicate for `f : F_2 → ℝ`,
expressed in terms of the admitted 1 + 3 neighbour structure.
This is the statement that `Δf(x) = 0` for every `x`, phrased without
reference to `laplacian_E` (so we do not need `LocallyFinite` or
`DecidableRel` instances on the Cayley graph of `F_2`). -/
def PointwiseHarmonic (φ : ∂F2) (f : F2 → ℝ) : Prop :=
  ∀ x : F2, ∃ (yφ : F2) (T : Finset F2),
    (cayley_graph F2_generating_set).Adj x yφ ∧
    busemann φ yφ = busemann φ x - 1 ∧
    T.card = 3 ∧
    (∀ y ∈ T, (cayley_graph F2_generating_set).Adj x y ∧
              busemann φ y = busemann φ x + 1) ∧
    yφ ∉ T ∧
    f yφ + (∑ y ∈ T, f y) = 4 * f x

/-- The Poisson kernel `p_φ` is pointwise harmonic, as a consequence of
`poisson_kernel_harmonic_eq`. -/
theorem poisson_kernel_pointwise_harmonic (φ : ∂F2) :
    PointwiseHarmonic φ (poisson_kernel φ) := by
  intro x
  exact poisson_kernel_harmonic_eq φ x

/-! #### Local max / min propagation: the algebraic core of the max principle

The discrete maximum principle rests on a purely algebraic fact: if `g`
is pointwise harmonic at `x` and all four neighbours `y` of `x` satisfy
`g(y) ≤ g(x)`, then all four neighbours have `g(y) = g(x)`. Indeed, using
`4 g(x) = g(yφ) + Σ_{y ∈ T} g(y)` and `|T| = 3`,

  `4 g(x) = g(yφ) + Σ_{y ∈ T} g(y) ≤ g(x) + 3 g(x) = 4 g(x)`

with equality throughout, forcing `g(yφ) = g(x)` and `g(y) = g(x)` for
every `y ∈ T`.

This local step is fully formalised below. Combined with the Wave 15A
companion axiom `tree_bounded_harmonic_vanishes` (which supplies the
global "bounded harmonic with vanishing boundary trace ⇒ zero" step,
cf. Cartwright–Soardi 1989; Woess 2000), it yields uniqueness via
`harmonic_vanishes_of_boundary_zero` and its truncation specialisation
`harmonic_vanish_on_Tq`. -/

/-- **Local max-propagation (proven).** Suppose `g yφ + Σ_{y ∈ T} g y =
4 · g x` with `|T| = 3`, and `g y ≤ g x` for every neighbour `y ∈ {yφ} ∪ T`.
Then `g yφ = g x` and `g y = g x` for every `y ∈ T`. -/
lemma harmonic_max_propagation_step (g : F2 → ℝ) (x : F2)
    (yφ : F2) (T : Finset F2)
    (h_card : T.card = 3)
    (h_sum : g yφ + (∑ y ∈ T, g y) = 4 * g x)
    (h_yφ_le : g yφ ≤ g x)
    (h_T_le : ∀ y ∈ T, g y ≤ g x) :
    g yφ = g x ∧ ∀ y ∈ T, g y = g x := by
  have h_term_nn : ∀ y ∈ T, 0 ≤ g x - g y :=
    fun y hy => sub_nonneg.mpr (h_T_le y hy)
  have h_T_sum_ge : 0 ≤ ∑ y ∈ T, (g x - g y) := Finset.sum_nonneg h_term_nn
  have h_yφ_ge : 0 ≤ g x - g yφ := sub_nonneg.mpr h_yφ_le
  have h_T_sum_eq : ∑ y ∈ T, (g x - g y) = (T.card : ℝ) * g x - ∑ y ∈ T, g y := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  have h_T_sum_val : ∑ y ∈ T, (g x - g y) = 3 * g x - ∑ y ∈ T, g y := by
    rw [h_T_sum_eq, h_card]; push_cast; ring
  have h_total : (g x - g yφ) + ∑ y ∈ T, (g x - g y) = 0 := by
    rw [h_T_sum_val]; linarith
  have h_yφ_zero : g x - g yφ = 0 := by linarith
  have h_T_zero : ∑ y ∈ T, (g x - g y) = 0 := by linarith
  refine ⟨by linarith, ?_⟩
  intro y hy
  have h_each : ∀ y' ∈ T, g x - g y' = 0 :=
    fun y' hy' => (Finset.sum_eq_zero_iff_of_nonneg h_term_nn).mp h_T_zero y' hy'
  have := h_each y hy; linarith

/-- **Local min-propagation (proven).** Symmetric of
`harmonic_max_propagation_step` for lower bounds on neighbours. -/
lemma harmonic_min_propagation_step (g : F2 → ℝ) (x : F2)
    (yφ : F2) (T : Finset F2)
    (h_card : T.card = 3)
    (h_sum : g yφ + (∑ y ∈ T, g y) = 4 * g x)
    (h_yφ_ge : g x ≤ g yφ)
    (h_T_ge : ∀ y ∈ T, g x ≤ g y) :
    g yφ = g x ∧ ∀ y ∈ T, g y = g x := by
  set h : F2 → ℝ := fun y => - g y with h_def
  have h_sum_neg : h yφ + (∑ y ∈ T, h y) = 4 * h x := by
    simp only [h_def, Finset.sum_neg_distrib]
    linarith
  have h_yφ_le_neg : h yφ ≤ h x := by simp only [h_def]; linarith
  have h_T_le_neg : ∀ y ∈ T, h y ≤ h x := by
    intro y hy; simp only [h_def]; linarith [h_T_ge y hy]
  obtain ⟨H1, H2⟩ :=
    harmonic_max_propagation_step h x yφ T h_card h_sum_neg h_yφ_le_neg h_T_le_neg
  refine ⟨?_, ?_⟩
  · have : -g yφ = -g x := H1; linarith
  · intro y hy; have : -g y = -g x := H2 y hy; linarith

/-! #### Q40 — assembly

`poisson_kernel_unique` is closed in
`EnsX2026.FreeGroup.TreeBoundedHarmonicVanish` via Route (a) directly
from `sup_on_F2_ball_le_sup_on_shell` + its negated variant plus a
uniform shell-decay hypothesis on `f − p_φ`.  The truncation
`T_q = {x : m(x, φ) ≤ q}` and the finset version `Tq_finset` are
kept here for downstream use (e.g. `f_minus_p_uniform_decay` below),
although the Wave 22F.3 Route (a) closure does not need the
restricted T_q max principle that was sketched in earlier waves. -/

/-- The truncation `T_q = { x ∈ F_2 : m(x, φ) ≤ q }`. -/
noncomputable def Tq (φ : ∂F2) (q : ℕ) : Set F2 :=
  { x : F2 | common_prefix_length x φ ≤ q }

/-- Every vertex of `F_2` belongs to some truncation. Indeed
`m(x, φ) ≤ |x|`, so `x ∈ T_{|x|}`. -/
lemma mem_Tq_of_toWord_length (φ : ∂F2) (x : F2) :
    x ∈ Tq φ x.toWord.length := by
  unfold Tq common_prefix_length
  exact Nat.findGreatest_le _

/-! #### Finite-ball max principle infrastructure

Below we introduce the finite-ball infrastructure — `F2_ball R : Set F2`
with its finiteness and `Finset` counterpart — together with the
max/min-propagation sub-lemmas:

1. `F2_ball_finite` / `F2_ball_finset` — the ball is a finset;
2. `sup_on_F2_ball_le_sup_on_shell` — the max-principle step:
   `sup_{B_R} g ≤ sup_{∂B_R} g` (finite-tree max principle);
3. `neg_sup_on_F2_ball_le_sup_on_shell` — symmetric min-principle step.

The global vanishing step — which cannot be derived from *pointwise*
ray convergence alone, since shells of cardinality `~4 · 3^{R-1}` need
uniform-in-ψ control — is handled in
`EnsX2026.FreeGroup.TreeBoundedHarmonicVanish` under a uniform
shell-decay hypothesis (Route (a)): see
`harmonic_vanishes_of_global_shell_decay`.  The previous Wave 15A
`tree_bounded_harmonic_vanishes` companion axiom and the Wave 22F.2.2
`translated_walk_limit_identification` axiom were both removed in Wave
22F.3 in favour of that Route (a) closure. -/

/-! ##### Finite-ball infrastructure -/

/-- The ball of radius `R` in the Cayley graph of `F_2`, centred at the
identity. Because `F_2` is a 4-regular tree whose graph distance coincides
with reduced-word length (`F2_dist_eq_toWord_length`), this is exactly the
set of group elements of word-length at most `R`. -/
def F2_ball (R : ℕ) : Set F2 := { x : F2 | x.toWord.length ≤ R }

/-- The ball `F2_ball R` is finite. This follows from the fact that the
map `x ↦ x.toWord` is injective (as reduced words determine the group
element via `FreeGroup.toWord_injective`), and the set of lists of length
`≤ R` over the finite alphabet `Fin 2 × Bool` is itself finite. -/
lemma F2_ball_finite (R : ℕ) : (F2_ball R).Finite := by
  classical
  -- The map `x ↦ x.toWord` injects `F2_ball R` into the finite set of
  -- lists of length ≤ R over the finite alphabet `Fin 2 × Bool`.
  have h_inj : Function.Injective (fun x : F2 => x.toWord) :=
    _root_.FreeGroup.toWord_injective
  have hL : {w : List (Fin 2 × Bool) | w.length ≤ R}.Finite :=
    List.finite_length_le _ R
  have hsub : F2_ball R ⊆ (fun x : F2 => x.toWord) ⁻¹' {w | w.length ≤ R} := by
    intro x hx
    exact hx
  exact (hL.preimage (h_inj.injOn)).subset hsub

/-- The finset version of `F2_ball R`. -/
noncomputable def F2_ball_finset (R : ℕ) : Finset F2 :=
  (F2_ball_finite R).toFinset

@[simp] lemma mem_F2_ball_finset (R : ℕ) (x : F2) :
    x ∈ F2_ball_finset R ↔ x.toWord.length ≤ R := by
  unfold F2_ball_finset
  rw [Set.Finite.mem_toFinset]
  rfl

/-- The boundary shell of the ball of radius `R`: elements of word-length
exactly `R`. -/
def F2_shell (R : ℕ) : Set F2 := { x : F2 | x.toWord.length = R }

lemma F2_shell_finite (R : ℕ) : (F2_shell R).Finite := by
  refine (F2_ball_finite R).subset ?_
  intro x hx
  unfold F2_shell at hx
  unfold F2_ball
  simp only [Set.mem_setOf_eq] at hx ⊢
  exact le_of_eq hx

noncomputable def F2_shell_finset (R : ℕ) : Finset F2 :=
  (F2_shell_finite R).toFinset

@[simp] lemma mem_F2_shell_finset (R : ℕ) (x : F2) :
    x ∈ F2_shell_finset R ↔ x.toWord.length = R := by
  unfold F2_shell_finset
  rw [Set.Finite.mem_toFinset]
  rfl

/-- The identity `1 ∈ F_2` lies in the ball `F2_ball R` for every `R`. -/
lemma one_mem_F2_ball (R : ℕ) : (1 : F2) ∈ F2_ball R := by
  unfold F2_ball
  simp only [Set.mem_setOf_eq, toWord_length_one]
  exact Nat.zero_le _

/-- The ball `F2_ball R` is nonempty (it contains the identity). -/
lemma F2_ball_finset_nonempty (R : ℕ) : (F2_ball_finset R).Nonempty :=
  ⟨(1 : F2), by rw [mem_F2_ball_finset]; simp⟩

/-! ##### `Tq` finset infrastructure (Wave 22F Commit 1)

Introduce the finite approximation `Tq_finset φ q R := Tq φ q ∩ B_R` as a
`Finset`, to be used in the restricted maximum-principle development
below. -/

/-- The finite intersection `Tq φ q ∩ F2_ball R`, as a `Finset F2`.
Defined as the filter of `F2_ball_finset R` by the predicate
`common_prefix_length · φ ≤ q`. -/
noncomputable def Tq_finset (φ : ∂F2) (q : ℕ) (R : ℕ) : Finset F2 := by
  classical
  exact (F2_ball_finset R).filter (fun x => common_prefix_length x φ ≤ q)

lemma mem_Tq_finset (φ : ∂F2) (q R : ℕ) (x : F2) :
    x ∈ Tq_finset φ q R ↔
      x.toWord.length ≤ R ∧ common_prefix_length x φ ≤ q := by
  classical
  unfold Tq_finset
  rw [Finset.mem_filter, mem_F2_ball_finset]

/-- If `m(x, φ) ≤ q` and `|x| ≤ R`, then `x ∈ F2_ball_finset R`. -/
lemma F2_ball_of_Tq_bound (φ : ∂F2) (q R : ℕ) (x : F2)
    (_hm : common_prefix_length x φ ≤ q) (hR : x.toWord.length ≤ R) :
    x ∈ F2_ball_finset R := by
  rw [mem_F2_ball_finset]; exact hR

/-- The identity lies in `Tq_finset φ q R` for all `q, R`. -/
lemma one_mem_Tq_finset (φ : ∂F2) (q R : ℕ) :
    (1 : F2) ∈ Tq_finset φ q R := by
  rw [mem_Tq_finset]
  refine ⟨?_, ?_⟩
  · rw [toWord_length_one]; exact Nat.zero_le _
  · rw [common_prefix_length_one]; exact Nat.zero_le _

/-- `Tq_finset φ q R` is nonempty. -/
lemma Tq_finset_nonempty (φ : ∂F2) (q R : ℕ) :
    (Tq_finset φ q R).Nonempty :=
  ⟨(1 : F2), one_mem_Tq_finset φ q R⟩

/-! ##### Max-principle step on the finite ball

The statement: for a pointwise harmonic `g`, the supremum of `g` over the
ball `B_R` is attained on the boundary shell `∂B_R = F2_shell R`.

Proof sketch: let `M := sup_{B_R} g`. If attained at some interior vertex
`x` with `|x| < R`, then all four neighbours of `x` also lie in `B_R`
(since the graph distance from `1` agrees with word-length, and
neighbours differ in word-length by ±1, so `|y| ≤ |x| + 1 ≤ R`). By
`harmonic_max_propagation_step` applied with these four neighbours, each
neighbour `y` has `g(y) = M`. Iterating: the max propagates outward along
each path to the boundary, forcing `g ≡ M` on some path from `x` to
`∂B_R`. Hence `M` is also attained on `∂B_R`.

The full Lean proof requires the following ingredients, each delicate:
* all four neighbours of an interior vertex lie in `B_R`;
* well-founded induction on the "distance to the boundary", i.e.
  `R − |x|`;
* dispatch on whether `x` is the identity (special case since the
  neighbour towards `φ` is arbitrary at the root) or has a unique
  inward neighbour.

We state the decomposition cleanly and leave the proof as a targeted
`sorry`. -/

/-! ##### Structural helpers for neighbour word-length control

To execute the propagation argument, we need two facts about neighbours
in the Cayley graph of `F_2`:

* **word-length bound on neighbours** — every neighbour `y ∼ x` has
  `|y| ≤ |x| + 1`;
* **existence of an outward neighbour** — at every vertex `x`, there is
  at least one neighbour `y` with `|y| = |x| + 1`.

Both are consequences of `F2_dist_eq_toWord_length` (graph distance from
`1` equals word length) combined with `Adj.diff_dist_adj` (adjacency
changes distance by at most `1`). We state them as targeted sub-sorrys
and use them to prove the finite-tree maximum principle below. -/

/-- Helper: every element of `F2_generating_set` has `toWord.length = 1`. -/
private lemma F2_generator_toWord_length (z : F2) (hz : z ∈ F2_generating_set) :
    z.toWord.length = 1 := by
  rcases hz with h | h | h | h
  · -- z = of 0
    rw [h, _root_.FreeGroup.toWord_of]; simp
  · -- z = of 1
    rw [h, _root_.FreeGroup.toWord_of]; simp
  · -- z = (of 0)⁻¹
    rw [h, _root_.FreeGroup.toWord_inv, _root_.FreeGroup.toWord_of,
        _root_.FreeGroup.invRev_length]; simp
  · -- z = (of 1)⁻¹
    rw [h, _root_.FreeGroup.toWord_inv, _root_.FreeGroup.toWord_of,
        _root_.FreeGroup.invRev_length]; simp

/-- Every neighbour of `x ∈ F_2` in the Cayley graph has word-length at
most `x.toWord.length + 1`.

**Proof.** If `y ∼ x` then either `y = x * z` or `x = y * z` for some
`z ∈ F2_generating_set`.  In the first case, by `toWord_mul_sublist`,
`y.toWord` is a sublist of `x.toWord ++ z.toWord`, so
`|y.toWord| ≤ |x.toWord| + |z.toWord| = |x.toWord| + 1`.  In the second
case, `y = x * z⁻¹` (by group algebra), and `z⁻¹ ∈ F2_generating_set` by
symmetry, so the same argument applies. -/
private lemma F2_neighbour_toWord_length_le (x y : F2)
    (h_adj : (cayley_graph F2_generating_set).Adj x y) :
    y.toWord.length ≤ x.toWord.length + 1 := by
  rw [EnsX2026.Cayley.cayley_graph_adj] at h_adj
  obtain ⟨_hne, hcase⟩ := h_adj
  rcases hcase with ⟨z, hz, hy⟩ | ⟨z, hz, hx⟩
  · -- `y = x * z` with `z ∈ F2_generating_set`.
    have h_sub : List.Sublist (x * z).toWord (x.toWord ++ z.toWord) :=
      _root_.FreeGroup.toWord_mul_sublist x z
    have h_len : (x * z).toWord.length ≤ (x.toWord ++ z.toWord).length :=
      h_sub.length_le
    have h_z_len : z.toWord.length = 1 := F2_generator_toWord_length z hz
    rw [hy]
    calc (x * z).toWord.length
        ≤ (x.toWord ++ z.toWord).length := h_len
      _ = x.toWord.length + z.toWord.length := List.length_append
      _ = x.toWord.length + 1 := by rw [h_z_len]
  · -- `x = y * z` with `z ∈ F2_generating_set`.  Then `y = x * z⁻¹`, and
    -- `z⁻¹ ∈ F2_generating_set` by symmetry.
    have hy_eq : y = x * z⁻¹ := by
      rw [hx]; group
    have hz_inv : z⁻¹ ∈ F2_generating_set := F2_generating_set_symmetric z hz
    have h_sub : List.Sublist (x * z⁻¹).toWord (x.toWord ++ z⁻¹.toWord) :=
      _root_.FreeGroup.toWord_mul_sublist x z⁻¹
    have h_len : (x * z⁻¹).toWord.length ≤ (x.toWord ++ z⁻¹.toWord).length :=
      h_sub.length_le
    have h_zinv_len : z⁻¹.toWord.length = 1 := F2_generator_toWord_length z⁻¹ hz_inv
    rw [hy_eq]
    calc (x * z⁻¹).toWord.length
        ≤ (x.toWord ++ z⁻¹.toWord).length := h_len
      _ = x.toWord.length + z⁻¹.toWord.length := List.length_append
      _ = x.toWord.length + 1 := by rw [h_zinv_len]

/-- Helper: when `x.toWord` is empty OR its last letter `(a, s)` does not
cancel with `ℓ` (i.e. `a ≠ ℓ.1 ∨ s = ℓ.2`), appending `ℓ` yields a
reduced word, hence `(x * FreeGroup.mk [ℓ]).toWord = x.toWord ++ [ℓ]`. -/
private lemma F2_mul_mk_single_length
    (x : F2) (ℓ : Fin 2 × Bool)
    (h_no_cancel : ∀ last ∈ x.toWord.getLast?,
      last.1 ≠ ℓ.1 ∨ last.2 = ℓ.2) :
    (x * _root_.FreeGroup.mk [ℓ]).toWord.length = x.toWord.length + 1 := by
  -- Establish the concatenation `x.toWord ++ [ℓ]` is reduced.
  have h_reduced : _root_.FreeGroup.IsReduced (x.toWord ++ [ℓ]) := by
    have hx_reduced : _root_.FreeGroup.IsReduced x.toWord :=
      _root_.FreeGroup.isReduced_toWord
    rw [_root_.FreeGroup.IsReduced] at hx_reduced ⊢
    -- The chain is `x.toWord ++ [ℓ]`; non-cancellation on consecutive pairs.
    rw [List.isChain_iff_forall_rel_of_append_cons_cons]
    intro a b l₁ l₂ heq
    -- Either (a, b) is entirely inside x.toWord, or (a, b) = (last of x.toWord, ℓ).
    -- Dispatch on the length of l₂.
    by_cases hl₂ : l₂ = []
    · -- l₂ = []: the pair (a, b) is the last two elements, so b = ℓ and
      -- a is the last of x.toWord.
      subst hl₂
      -- heq : x.toWord ++ [ℓ] = l₁ ++ [a, b]
      -- ℓ = b, and x.toWord = l₁ ++ [a].
      have h_len : (x.toWord ++ [ℓ]).length = (l₁ ++ [a, b]).length :=
        congrArg _ heq
      simp [List.length_append, List.length_cons] at h_len
      -- Show x.toWord.length ≥ 1.
      have hx_ne : x.toWord ≠ [] := by
        intro h_empty
        rw [h_empty] at h_len
        simp at h_len
      -- The last element of x.toWord ++ [ℓ] is ℓ; the last of l₁ ++ [a, b] is b.
      have h_ℓ_eq_b : ℓ = b := by
        have h1 : (x.toWord ++ [ℓ]).getLast? = some ℓ := by
          simp [List.getLast?_append]
        have h2 : (l₁ ++ [a, b]).getLast? = some b := by
          simp [List.getLast?_append]
        have h3 : (x.toWord ++ [ℓ]).getLast? = (l₁ ++ [a, b]).getLast? :=
          congrArg _ heq
        rw [h1, h2] at h3
        exact Option.some_injective _ h3
      -- x.toWord = l₁ ++ [a]: cancel [ℓ] from the right of both sides.
      have h_xlast : x.toWord = l₁ ++ [a] := by
        have heq' : x.toWord ++ [ℓ] = (l₁ ++ [a]) ++ [ℓ] := by
          rw [heq, h_ℓ_eq_b]
          simp [List.append_assoc]
        exact List.append_cancel_right heq'
      -- So x.toWord.getLast? = some a.
      have h_x_getLast : x.toWord.getLast? = some a := by
        rw [h_xlast]; simp [List.getLast?_append]
      -- Apply h_no_cancel: a.1 ≠ ℓ.1 ∨ a.2 = ℓ.2.
      have ha_mem : a ∈ x.toWord.getLast? := by rw [h_x_getLast]; rfl
      have h_nc := h_no_cancel a ha_mem
      -- Goal: a.1 = b.1 → a.2 = b.2, rewriting via ℓ = b.
      rw [← h_ℓ_eq_b]
      intro h_fst
      rcases h_nc with h | h
      · exact absurd h_fst h
      · exact h
    · -- l₂ ≠ []: the pair (a, b) is strictly inside x.toWord.
      -- Extract l₂ = l₂.dropLast ++ [ℓ] via reverse reasoning.
      have h_l₂_split : l₂ = l₂.dropLast ++ [ℓ] := by
        have h_rev : (x.toWord ++ [ℓ]).reverse = (l₁ ++ a :: b :: l₂).reverse :=
          congrArg List.reverse heq
        simp [List.reverse_append, List.reverse_cons] at h_rev
        have hl₂_rev_ne : l₂.reverse ≠ [] := by
          intro h; apply hl₂; exact List.reverse_eq_nil_iff.mp h
        obtain ⟨lhead, ltail, hl_split⟩ := List.exists_cons_of_ne_nil hl₂_rev_ne
        rw [hl_split] at h_rev
        simp at h_rev
        have h_head : ℓ = lhead := h_rev.1
        -- l₂.reverse = ℓ :: ltail, so l₂ = ltail.reverse ++ [ℓ].
        have h_l₂_eq : l₂ = ltail.reverse ++ [ℓ] := by
          have hrev_eq : l₂.reverse = ℓ :: ltail := by rw [hl_split, h_head]
          have := congrArg List.reverse hrev_eq
          simp at this
          exact this
        -- Show ltail.reverse = l₂.dropLast.
        have h_drop_eq : l₂.dropLast = ltail.reverse := by
          rw [h_l₂_eq]
          simp
        rw [h_drop_eq]
        exact h_l₂_eq
      have h_x_split : x.toWord = l₁ ++ a :: b :: l₂.dropLast := by
        have h1 : x.toWord ++ [ℓ] = l₁ ++ a :: b :: l₂.dropLast ++ [ℓ] := by
          rw [heq]
          conv_lhs => rw [h_l₂_split]
          simp [List.append_assoc, List.cons_append]
        exact List.append_cancel_right h1
      -- Apply hx_reduced on the split of x.toWord.
      have hx_chain := hx_reduced
      rw [List.isChain_iff_forall_rel_of_append_cons_cons] at hx_chain
      exact hx_chain h_x_split
  -- Use h_reduced to compute toWord.
  have h_mul_eq :
      (x * _root_.FreeGroup.mk [ℓ]) = _root_.FreeGroup.mk (x.toWord ++ [ℓ]) := by
    conv_lhs =>
      rw [show x = _root_.FreeGroup.mk x.toWord from (_root_.FreeGroup.mk_toWord).symm]
    rw [_root_.FreeGroup.mul_mk]
  rw [h_mul_eq, _root_.FreeGroup.toWord_mk, h_reduced.reduce_eq,
      List.length_append]
  simp

/-- **Structural helper.** For every `x ∈ F_2`, among its four neighbours
in the Cayley graph, there exists at least one neighbour `y` with
`|y| = |x| + 1`.

**Proof.** Consider the two candidate generators `of 0` (letter
`(0, true)`) and `of 1` (letter `(1, true)`).  Let `last := x.toWord.getLast?`:

* If `last = none` (x = 1), both candidates work — the appended letter
  has no preceding letter to cancel with.
* If `last = some (a, s)`, the letter `(ℓ₁, true)` cancels iff
  `(a, s) = (ℓ₁, false)`, i.e. `a = ℓ₁ ∧ s = false`.  For `ℓ₁ = 0` this
  requires `a = 0 ∧ s = false`; for `ℓ₁ = 1`, `a = 1 ∧ s = false`.
  These two conditions are mutually exclusive (disjoint values of `a`),
  so at least one of the two candidates does not cancel.

We pick `of 0` when it doesn't cancel, and `of 1` otherwise. -/
private lemma F2_exists_outward_neighbour (x : F2) :
    ∃ y : F2, (cayley_graph F2_generating_set).Adj x y ∧
      y.toWord.length = x.toWord.length + 1 := by
  classical
  -- Candidate 1: `z₀ := of 0`, letter `(0, true)`.
  -- Candidate 2: `z₁ := of 1`, letter `(1, true)`.
  -- At least one of the two has `|x * z| = |x| + 1`.
  set ℓ₀ : Fin 2 × Bool := (0, true)
  set ℓ₁ : Fin 2 × Bool := (1, true)
  -- The non-cancellation condition for `ℓ₀`: `∀ last ∈ x.toWord.getLast?,
  -- last.1 ≠ 0 ∨ last.2 = true`.  Similarly for `ℓ₁`.
  by_cases h0 : ∀ last ∈ x.toWord.getLast?, last.1 ≠ ℓ₀.1 ∨ last.2 = ℓ₀.2
  · -- Use `of 0` as the outward generator.
    refine ⟨x * _root_.FreeGroup.of 0, ?_, ?_⟩
    · -- Adjacency: `x ~ x * of 0` since `of 0 ∈ F2_generating_set` and `of 0 ≠ 1`.
      apply EnsX2026.Cayley.cayley_graph_adj_mul
      · -- `of 0 ∈ F2_generating_set`
        left; rfl
      · exact _root_.FreeGroup.of_ne_one 0
    · -- Length: via F2_mul_mk_single_length with ℓ = (0, true), using
      -- `of 0 = FreeGroup.mk [(0, true)]`.
      have h_of_eq : (_root_.FreeGroup.of (0 : Fin 2)) =
          _root_.FreeGroup.mk [(0, true)] := rfl
      rw [h_of_eq]
      exact F2_mul_mk_single_length x (0, true) h0
  · -- ¬ h0: there exists `last ∈ x.toWord.getLast?` with `last.1 = 0 ∧ last.2 = false`.
    push_neg at h0
    obtain ⟨last, hlast_mem, hlast_fst, hlast_snd⟩ := h0
    -- So last = (0, false). Then for ℓ₁ = (1, true): last.1 = 0 ≠ 1 = ℓ₁.1.
    have h1 : ∀ last' ∈ x.toWord.getLast?, last'.1 ≠ ℓ₁.1 ∨ last'.2 = ℓ₁.2 := by
      intro last' hlast'_mem
      left
      -- last' = last, so last'.1 = 0 ≠ 1 = ℓ₁.1.
      have h_eq : last' = last := by
        rw [Option.mem_def] at hlast_mem hlast'_mem
        rw [hlast_mem] at hlast'_mem
        exact (Option.some_injective _ hlast'_mem).symm
      rw [h_eq, hlast_fst]
      -- Goal: (0 : Fin 2) ≠ ℓ₁.1 = 1.
      decide
    refine ⟨x * _root_.FreeGroup.of 1, ?_, ?_⟩
    · apply EnsX2026.Cayley.cayley_graph_adj_mul
      · right; left; rfl
      · exact _root_.FreeGroup.of_ne_one 1
    · have h_of_eq : (_root_.FreeGroup.of (1 : Fin 2)) =
          _root_.FreeGroup.mk [(1, true)] := rfl
      rw [h_of_eq]
      exact F2_mul_mk_single_length x (1, true) h1

/-- **Finite-tree max principle.** The supremum of a pointwise
harmonic function `g : F_2 → ℝ` over the finite ball `F2_ball_finset R`
is bounded by its supremum over the shell `F2_shell_finset R`.

Together with the symmetric lower-bound version
(`neg_sup_on_F2_ball_le_sup_on_shell`), this gives
`sup_{B_R} |g| ≤ sup_{∂B_R} |g|`.

**Proof.** By contradiction: suppose `shell_sup < ball_sup`. Pick a
max-attaining vertex `x_max ∈ ball`. Inductively extend: at each step,
if the current max-attaining vertex `x` has `|x| < R`, apply
`harmonic_max_propagation_step` to propagate the max to all four
neighbours (which all lie in the ball by `F2_neighbour_toWord_length_le`);
by `F2_exists_outward_neighbour`, one of them has `|y| = |x| + 1`. After
at most `R` steps, we obtain a max-attaining vertex on the shell,
contradicting `shell_sup < ball_sup`. -/
lemma sup_on_F2_ball_le_sup_on_shell (φ : ∂F2) (g : F2 → ℝ)
    (h_harm : PointwiseHarmonic φ g) (R : ℕ) :
    ∀ x ∈ F2_ball_finset R,
      g x ≤ (F2_shell_finset R).sup' (by
        -- shell is nonempty for R = 0 via the identity, and for R > 0
        -- via `φ.valPrefix R` (whose word-length equals R).
        rcases Nat.eq_zero_or_pos R with hR | hR
        · subst hR
          exact ⟨(1 : F2), by rw [mem_F2_shell_finset]; simp⟩
        · exact ⟨φ.valPrefix R, by
            rw [mem_F2_shell_finset, F2_boundary.length_toWord_valPrefix]⟩) g := by
  classical
  -- Nonempty shell witness (reused below).
  have hne_shell : (F2_shell_finset R).Nonempty := by
    rcases Nat.eq_zero_or_pos R with hR | hR
    · subst hR
      exact ⟨(1 : F2), by rw [mem_F2_shell_finset]; simp⟩
    · exact ⟨φ.valPrefix R, by
        rw [mem_F2_shell_finset, F2_boundary.length_toWord_valPrefix]⟩
  set S : ℝ := (F2_shell_finset R).sup' hne_shell g with hS_def
  -- Proof by contradiction: suppose some `x ∈ F2_ball_finset R` violates
  -- `g x ≤ S`.  Pick the max-attaining vertex in the ball and derive a
  -- contradiction by propagating the maximum outward to the shell.
  by_contra h_neg
  push_neg at h_neg
  obtain ⟨x_bad, hx_bad_mem, hx_bad⟩ := h_neg
  -- Maximum of `g` over the ball.
  have hne_ball : (F2_ball_finset R).Nonempty := F2_ball_finset_nonempty R
  set M : ℝ := (F2_ball_finset R).sup' hne_ball g with hM_def
  -- `M ≥ g x_bad > S`, in particular `S < M`.
  have hM_ge_xbad : g x_bad ≤ M := Finset.le_sup' g hx_bad_mem
  have hS_lt_M : S < M := lt_of_lt_of_le hx_bad hM_ge_xbad
  -- Every vertex of the ball has `g y ≤ M`.
  have h_ball_le_M : ∀ y ∈ F2_ball_finset R, g y ≤ M :=
    fun y hy => Finset.le_sup' g hy
  -- Every shell vertex has `g y ≤ S < M`, so no shell vertex is max-attaining.
  have h_shell_lt_M : ∀ y ∈ F2_shell_finset R, g y < M := by
    intro y hy
    have : g y ≤ S := by
      rw [hS_def]; exact Finset.le_sup' g hy
    linarith
  -- Produce a max-attaining vertex in the ball.
  obtain ⟨x_max, hx_max_mem, hx_max_eq⟩ :
      ∃ x ∈ F2_ball_finset R, g x = M := by
    obtain ⟨y, hy_mem, hy_eq⟩ := (F2_ball_finset R).exists_mem_eq_sup' hne_ball g
    exact ⟨y, hy_mem, hy_eq.symm⟩
  -- Core claim: for every `k ≤ R`, there exists a max-attaining vertex
  -- `x` in `F2_ball_finset R` with `x.toWord.length ≥ k`. Taking `k = R`
  -- places a max-attaining vertex on the shell, contradiction.
  suffices h_chain : ∀ k : ℕ, k ≤ R →
      ∃ x : F2, x ∈ F2_ball_finset R ∧ g x = M ∧ k ≤ x.toWord.length by
    obtain ⟨x_shell, hx_shell_mem, hx_shell_eq, hx_shell_len⟩ := h_chain R le_rfl
    have h_le : x_shell.toWord.length ≤ R := by
      rw [mem_F2_ball_finset] at hx_shell_mem; exact hx_shell_mem
    have h_eq : x_shell.toWord.length = R := le_antisymm h_le hx_shell_len
    have hx_shell_shell : x_shell ∈ F2_shell_finset R := by
      rw [mem_F2_shell_finset]; exact h_eq
    have : g x_shell < M := h_shell_lt_M x_shell hx_shell_shell
    linarith
  -- Prove the chain claim by induction on `k`.
  intro k hkR
  induction k with
  | zero =>
    exact ⟨x_max, hx_max_mem, hx_max_eq, Nat.zero_le _⟩
  | succ k ih =>
    have hkR' : k ≤ R := Nat.le_of_succ_le hkR
    obtain ⟨x, hx_mem, hx_eq, hx_len⟩ := ih hkR'
    -- Dispatch: either `|x| ≥ k + 1` already, or `|x| = k`.
    by_cases hlen_ge : k + 1 ≤ x.toWord.length
    · exact ⟨x, hx_mem, hx_eq, hlen_ge⟩
    · push_neg at hlen_ge
      have hx_len_eq : x.toWord.length = k :=
        le_antisymm (Nat.le_of_lt_succ hlen_ge) hx_len
      -- `|x| = k < R`.
      have hx_lt_R : x.toWord.length < R := by
        rw [hx_len_eq]; exact hkR
      -- Unpack harmonicity at `x`.
      obtain ⟨yφ, T, h_yφ_adj, h_yφ_bus, h_Tcard, h_T_mem, _h_yφ_notmem, h_sum⟩ :=
        h_harm x
      -- All four neighbours lie in `F2_ball_finset R`.
      have hyφ_mem_ball : yφ ∈ F2_ball_finset R := by
        rw [mem_F2_ball_finset]
        have := F2_neighbour_toWord_length_le x yφ h_yφ_adj
        omega
      have hT_mem_ball : ∀ y ∈ T, y ∈ F2_ball_finset R := by
        intro y hy
        rw [mem_F2_ball_finset]
        have hadj := (h_T_mem y hy).1
        have := F2_neighbour_toWord_length_le x y hadj
        omega
      -- All four neighbours satisfy `g ≤ g x` (since `g x = M` is the ball max).
      have h_yφ_le : g yφ ≤ g x := by
        rw [hx_eq]; exact h_ball_le_M yφ hyφ_mem_ball
      have h_T_le : ∀ y ∈ T, g y ≤ g x := by
        intro y hy
        rw [hx_eq]; exact h_ball_le_M y (hT_mem_ball y hy)
      -- Apply `harmonic_max_propagation_step`: all four neighbours are max-attaining.
      obtain ⟨h_yφ_max, h_T_max⟩ :=
        harmonic_max_propagation_step g x yφ T h_Tcard h_sum h_yφ_le h_T_le
      -- Produce an outward neighbour `y_out` with `|y_out| = |x| + 1 = k + 1`.
      obtain ⟨y_out, hy_out_adj, hy_out_len⟩ := F2_exists_outward_neighbour x
      -- `y_out` is one of `{yφ} ∪ T` (all neighbours of `x`).
      have h_bus_cases := busemann_other_neighbours φ x y_out hy_out_adj
      -- Identify `y_out` with `yφ` or an element of `T`, using cover
      -- from `busemann_three_plus_neighbours` combined with uniqueness
      -- of the `φ`-neighbour from `busemann_neighbour_structure`.
      rcases h_bus_cases with h_out_phi | h_out_plus
      · -- Case `busemann φ y_out = busemann φ x - 1`: by uniqueness of
        -- the `φ`-neighbour, `y_out = yφ`.
        obtain ⟨yφ_uniq, _hyφ_uniq_prop, h_uniq⟩ := busemann_neighbour_structure φ x
        have hy_out_eq_uniq : y_out = yφ_uniq :=
          h_uniq y_out ⟨hy_out_adj, h_out_phi⟩
        have hyφ_eq_uniq : yφ = yφ_uniq :=
          h_uniq yφ ⟨h_yφ_adj, h_yφ_bus⟩
        have h_y_out_eq_yφ : y_out = yφ := by
          rw [hy_out_eq_uniq, ← hyφ_eq_uniq]
        refine ⟨y_out, ?_, ?_, ?_⟩
        · rw [mem_F2_ball_finset]
          have := F2_neighbour_toWord_length_le x y_out hy_out_adj
          omega
        · rw [h_y_out_eq_yφ, h_yφ_max, hx_eq]
        · rw [hy_out_len, hx_len_eq]
      · -- Case `busemann φ y_out = busemann φ x + 1`: show `y_out ∈ T`.
        -- Every neighbour `z` of `x` with `b z = b x + 1` lies in `T`, by
        -- `busemann_three_plus_neighbours` + the uniqueness argument.
        -- We use the cover property applied to `T` itself.
        obtain ⟨T_cov, hT_cov_card, hT_cov_mem, hT_cov_cover⟩ :=
          busemann_three_plus_neighbours φ x
        -- Show `T = T_cov` as Finsets.
        have h_T_sub : T ⊆ T_cov := by
          intro z hz
          have hz_adj : (cayley_graph F2_generating_set).Adj x z :=
            (h_T_mem z hz).1
          have hz_bus : busemann φ z = busemann φ x + 1 :=
            (h_T_mem z hz).2
          rcases hT_cov_cover z hz_adj with hz_phi | hz_in
          · -- z is the φ-neighbour: contradiction with `b z = b x + 1`.
            exfalso
            have h1 : busemann φ x + 1 = busemann φ x - 1 :=
              hz_bus.symm.trans hz_phi
            have : (2 : ℤ) = 0 := by linarith
            exact absurd this (by decide)
          · exact hz_in
        have h_T_eq : T = T_cov :=
          Finset.eq_of_subset_of_card_le h_T_sub (by rw [hT_cov_card, h_Tcard])
        -- `y_out ∈ T_cov` by cover, hence `y_out ∈ T`.
        have hy_out_in_T : y_out ∈ T := by
          rcases hT_cov_cover y_out hy_out_adj with hy_phi | hy_in
          · exfalso
            have h1 : busemann φ x + 1 = busemann φ x - 1 :=
              h_out_plus.symm.trans hy_phi
            have : (2 : ℤ) = 0 := by linarith
            exact absurd this (by decide)
          · rw [h_T_eq]; exact hy_in
        refine ⟨y_out, ?_, ?_, ?_⟩
        · rw [mem_F2_ball_finset]
          have := F2_neighbour_toWord_length_le x y_out hy_out_adj
          omega
        · rw [h_T_max y_out hy_out_in_T, hx_eq]
        · rw [hy_out_len, hx_len_eq]

/-- Symmetric lower-bound variant of `sup_on_F2_ball_le_sup_on_shell`.
Follows by applying the max principle to `-g`. -/
lemma neg_sup_on_F2_ball_le_sup_on_shell (φ : ∂F2) (g : F2 → ℝ)
    (h_harm : PointwiseHarmonic φ g) (R : ℕ) :
    ∀ x ∈ F2_ball_finset R,
      -((F2_shell_finset R).sup' (by
        rcases Nat.eq_zero_or_pos R with hR | _hR
        · subst hR
          exact ⟨(1 : F2), by rw [mem_F2_shell_finset]; simp⟩
        · exact ⟨φ.valPrefix R, by
            rw [mem_F2_shell_finset, F2_boundary.length_toWord_valPrefix]⟩)
        (fun y => -g y)) ≤ g x := by
  -- Reduce to the max principle applied to `-g`, which is also harmonic.
  have h_neg_harm : PointwiseHarmonic φ (fun x => -g x) := by
    intro x
    obtain ⟨yφ, T, h_adj, h_bus, h_card, h_T, h_notmem, h_sum⟩ := h_harm x
    refine ⟨yφ, T, h_adj, h_bus, h_card, h_T, h_notmem, ?_⟩
    show -g yφ + (∑ y ∈ T, -g y) = 4 * -g x
    rw [Finset.sum_neg_distrib]
    linarith
  intro x hx
  have h := sup_on_F2_ball_le_sup_on_shell φ (fun y => -g y) h_neg_harm R x hx
  linarith

/-! ##### L1 geometric lemma (Wave 22F Commit 2)

For adjacent `x, y` in Cayley(F₂), the common-prefix length with `φ`
grows by at most one under an edge:
`m(y, φ) ≤ m(x, φ) + 1`. Equality forces `y = x · (φ.val m(x))`, i.e.
`y` is the unique "forward" neighbour of `x` along the ray to `φ`.

Proof: use `exists_letter_of_adj` to write `y = x * mk [ℓ]`, then case
split on `LastCancels x ℓ` and on whether `x` is on the ray
(`m = |x|`). In each of the four cases, `m(y, φ)` is computed by the
corresponding `BusemannLocal` case-lemma and compared to `m(x, φ) + 1`. -/
lemma tree_prefix_adj_le (φ : ∂F2) {x y : F2}
    (hadj : (cayley_graph F2_generating_set).Adj x y) :
    common_prefix_length y φ ≤ common_prefix_length x φ + 1 ∧
    (common_prefix_length y φ = common_prefix_length x φ + 1 →
      y = x * _root_.FreeGroup.mk [φ.val (common_prefix_length x φ)]) := by
  obtain ⟨ℓ, rfl⟩ := BusemannLocal.exists_letter_of_adj hadj
  set m : ℕ := common_prefix_length x φ with hm_def
  set n : ℕ := x.toWord.length with hn_def
  have hm_le_n : m ≤ n := BusemannLocal.common_prefix_length_le x φ
  by_cases hc : BusemannLocal.LastCancels x ℓ
  · -- Cancellation case: m(y, φ) = n - 1 or m.
    by_cases hray : m = n
    · -- Case B.1 (cancel + on-ray): m' = n - 1 ≤ m + 1.
      have h_m' : common_prefix_length (x * _root_.FreeGroup.mk [ℓ]) φ = n - 1 :=
        BusemannLocal.common_prefix_length_cancel_on_ray x ℓ φ hc hray
      refine ⟨?_, ?_⟩
      · rw [h_m']; omega
      · intro heq
        rw [h_m'] at heq
        -- m' = n - 1 = m + 1, with m = n ⇒ n - 1 = n + 1, impossible.
        exfalso; omega
    · -- Case B.2 (cancel + off-ray): m' = m ≤ m + 1.
      have hlt : m < n := lt_of_le_of_ne hm_le_n hray
      have h_m' : common_prefix_length (x * _root_.FreeGroup.mk [ℓ]) φ = m :=
        BusemannLocal.common_prefix_length_cancel_off_ray x ℓ φ hc hlt
      refine ⟨?_, ?_⟩
      · rw [h_m']; omega
      · intro heq
        rw [h_m'] at heq
        exfalso; omega
  · -- Non-cancel case.
    have hnc : BusemannLocal.NoLastCancel x ℓ := by
      unfold BusemannLocal.NoLastCancel
      intro ℓ' hℓ'_mem ⟨h1, h2⟩
      apply hc
      exact ⟨ℓ', hℓ'_mem, h1, h2⟩
    by_cases hray : m = n
    · -- Case A.1 (noCancel + on-ray): m' = n + 1 if ℓ = φ.val n, else n.
      have h_m' :=
        BusemannLocal.common_prefix_length_noCancel_on_ray x ℓ φ hnc hray
      by_cases hℓ : ℓ = φ.val n
      · -- m' = n + 1 = m + 1 ⇒ equality, witness y = x * mk [ℓ] = x * mk [φ.val m].
        have h_m'_eq : common_prefix_length (x * _root_.FreeGroup.mk [ℓ]) φ = n + 1 := by
          rw [h_m']; exact if_pos hℓ
        refine ⟨?_, ?_⟩
        · rw [h_m'_eq]; omega
        · intro _
          -- Goal: x * mk [ℓ] = x * mk [φ.val m].
          -- Since m = n and ℓ = φ.val n = φ.val m, they agree.
          congr 2
          rw [hℓ, hray]
      · -- m' = n = m, strict inequality.
        have h_m'_eq : common_prefix_length (x * _root_.FreeGroup.mk [ℓ]) φ = n := by
          rw [h_m']; exact if_neg hℓ
        refine ⟨?_, ?_⟩
        · rw [h_m'_eq]; omega
        · intro heq
          rw [h_m'_eq] at heq
          -- heq : n = m + 1, hray : m = n ⇒ contradiction.
          exfalso; omega
    · -- Case A.2 (noCancel + off-ray): m' = m ≤ m + 1.
      have hlt : m < n := lt_of_le_of_ne hm_le_n hray
      have h_m' : common_prefix_length (x * _root_.FreeGroup.mk [ℓ]) φ = m :=
        BusemannLocal.common_prefix_length_noCancel_off_ray x ℓ φ hnc hlt
      refine ⟨?_, ?_⟩
      · rw [h_m']; omega
      · intro heq
        rw [h_m'] at heq
        exfalso; omega

/-! ##### Global max principle on the 4-regular tree (Wave 22F.3)

The finite-ball max principle
`sup_on_F2_ball_le_sup_on_shell` + `neg_sup_on_F2_ball_le_sup_on_shell`
above give `|g x| ≤ sup_{F2_shell R} |g|` for every `x ∈ F2_ball R`.
Combined with a uniform shell-decay hypothesis on `g`, this yields
`g ≡ 0` globally — the Route (a) closure of Q40.

The global step is carried out in
`EnsX2026.FreeGroup.TreeBoundedHarmonicVanish` as
`harmonic_vanishes_of_global_shell_decay`, and its application to the
Poisson-kernel uniqueness problem as `poisson_kernel_unique`.  The
Wave 15A companion axiom `tree_bounded_harmonic_vanishes` and the
Wave 22F.2.2 `translated_walk_limit_identification` axiom
(Cartwright-Soardi / Furstenberg) — both previously needed because
pointwise ray convergence does not imply uniform shell decay across
a shell of cardinality `~4 · 3^{R-1}` — were removed in Wave 22F.3
in favour of a Route (a) hypothesis strengthening.  Full discussion
in `mg26_en_solutions_corrected.tex`, §Q40. -/

/-! #### Uniform-decay lemma for `g = f − p_φ` (Wave 22F Commit 4)

This lemma packages the triangle-inequality calculation that converts a
uniform-decay hypothesis for `f` into a uniform-decay hypothesis for
`g = f − p_φ`, using the explicit bound
`|p_φ(x)| = 3^(−b_φ(x)) ≤ 3^(2q) · 3^(−|x|)` for `x ∈ T_q`. -/

/-- On the truncation `T_q`, the Poisson kernel admits the explicit
majorant `p_φ(x) ≤ 3^{2q} · 3^{−|x|}`. This follows from
`b_φ(x) = |x| − 2·m(x,φ) ≥ |x| − 2q`, hence
`p_φ(x) = 3^{−b_φ(x)} ≤ 3^{−(|x|−2q)} = 3^{2q} · 3^{−|x|}`. -/
lemma poisson_kernel_le_on_Tq (φ : ∂F2) (q : ℕ) (x : F2)
    (hx : common_prefix_length x φ ≤ q) :
    poisson_kernel φ x ≤ (3 : ℝ) ^ (2 * q) * ((1 / 3 : ℝ) ^ x.toWord.length) := by
  unfold poisson_kernel busemann
  -- Want: 3^(-(|x| - 2*m)) ≤ 3^{2q} * (1/3)^{|x|}
  set n : ℕ := x.toWord.length with hn_def
  set m : ℕ := common_prefix_length x φ with hm_def
  -- The exponent `-(n - 2m)` equals `2m - n`.
  have h_exp : -((n : ℤ) - 2 * (m : ℤ)) = 2 * (m : ℤ) - (n : ℤ) := by ring
  rw [h_exp]
  -- `3^(2m - n) = 3^(2m) * 3^(-n) = 3^(2m) * (1/3)^n`.
  have h3ne : (3 : ℝ) ≠ 0 := by norm_num
  have h_decomp : (3 : ℝ) ^ (2 * (m : ℤ) - (n : ℤ))
      = (3 : ℝ) ^ (2 * m : ℕ) * ((1 / 3 : ℝ) ^ n) := by
    have h1 : (3 : ℝ) ^ (2 * (m : ℤ) - (n : ℤ))
        = (3 : ℝ) ^ (2 * (m : ℤ)) * (3 : ℝ) ^ (-(n : ℤ)) := by
      rw [show 2 * (m : ℤ) - (n : ℤ) = 2 * (m : ℤ) + (-(n : ℤ)) from by ring,
          zpow_add₀ h3ne]
    have h2 : (3 : ℝ) ^ (2 * (m : ℤ)) = (3 : ℝ) ^ (2 * m : ℕ) := by
      rw [show (2 * (m : ℤ)) = ((2 * m : ℕ) : ℤ) from by push_cast; ring, zpow_natCast]
    have h3 : (3 : ℝ) ^ (-(n : ℤ)) = ((1 / 3 : ℝ) ^ n) := by
      rw [zpow_neg, zpow_natCast, ← inv_pow,
          show (3 : ℝ)⁻¹ = 1 / 3 from by norm_num]
    rw [h1, h2, h3]
  rw [h_decomp]
  -- Now show: 3^(2m) * (1/3)^n ≤ 3^(2q) * (1/3)^n.
  have h_13_nn : (0 : ℝ) ≤ (1 / 3 : ℝ) ^ n := by positivity
  have h_pow_mono : (3 : ℝ) ^ (2 * m) ≤ (3 : ℝ) ^ (2 * q) := by
    apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3)
    omega
  exact mul_le_mul_of_nonneg_right h_pow_mono h_13_nn

/-- `poisson_kernel` is nonnegative. (Purely algebraic fact, proved from
the definition `poisson_kernel φ x = 3^{-b_φ(x)}`. Supersedes the axiom
`poisson_kernel_nonneg` of `ExitMeasure.lean` for the
`(φ : ∂F2) (x : F2)` argument order.) -/
lemma poisson_kernel_nonneg_arg_flip (φ : ∂F2) (x : F2) :
    0 ≤ poisson_kernel φ x := by
  unfold poisson_kernel
  exact zpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _

/-- **Uniform-decay transport.** If `f` has uniform decay on each
truncation `T_q` (uniformly in `x ∈ T_q`), then so does `f − p_φ`.
This is the key "wiring" lemma feeding into the refactored Commit 5
form of `poisson_kernel_unique`. -/
lemma f_minus_p_uniform_decay (f : F2 → ℝ) (φ : ∂F2)
    (h_f_uniform :
      ∀ q : ℕ, ∀ ε : ℝ, 0 < ε → ∃ R : ℕ, ∀ x : F2,
        x.toWord.length ≥ R →
        common_prefix_length x φ ≤ q →
        |f x| < ε) :
    ∀ q : ℕ, ∀ ε : ℝ, 0 < ε → ∃ R : ℕ, ∀ x : F2,
      x.toWord.length ≥ R →
      common_prefix_length x φ ≤ q →
      |f x - poisson_kernel φ x| < ε := by
  intro q ε hε
  -- Step 1: pick R₁ from h_f_uniform with ε/2.
  obtain ⟨R₁, hR₁⟩ := h_f_uniform q (ε / 2) (by linarith)
  -- Step 2: pick R₂ so that 3^{2q} · (1/3)^R₂ < ε/2.
  -- (1/3)^p → 0 (for p : ℕ), so C · (1/3)^p < ε/2 eventually.
  set C : ℝ := (3 : ℝ) ^ (2 * q) with hC_def
  have hC_pos : 0 < C := by
    rw [hC_def]; exact pow_pos (by norm_num) _
  -- Use `tendsto_pow_atTop_nhds_zero_of_lt_one` to find R₂.
  have h_tend : Filter.Tendsto (fun p : ℕ => C * ((1 / 3 : ℝ)) ^ p)
      Filter.atTop (nhds (C * 0)) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one
      (show (0 : ℝ) ≤ 1 / 3 by norm_num) (show (1 / 3 : ℝ) < 1 by norm_num)
    exact this.const_mul C
  rw [mul_zero] at h_tend
  -- Extract R₂.
  have h_eventually : ∀ᶠ p : ℕ in Filter.atTop,
      C * ((1 / 3 : ℝ) ^ p) < ε / 2 := by
    have hhalf_pos : 0 < ε / 2 := by linarith
    have := h_tend.eventually (gt_mem_nhds hhalf_pos)
    simpa using this
  obtain ⟨R₂, hR₂⟩ := Filter.eventually_atTop.mp h_eventually
  refine ⟨max R₁ R₂, ?_⟩
  intro x hxlen hxm
  have hxR₁ : R₁ ≤ x.toWord.length := le_of_max_le_left hxlen
  have hxR₂ : R₂ ≤ x.toWord.length := le_of_max_le_right hxlen
  have hfx : |f x| < ε / 2 := hR₁ x hxR₁ hxm
  have hpbound : C * ((1 / 3 : ℝ) ^ x.toWord.length) < ε / 2 :=
    hR₂ x.toWord.length hxR₂
  have hp_nn : 0 ≤ poisson_kernel φ x := poisson_kernel_nonneg_arg_flip φ x
  have hp_le : poisson_kernel φ x ≤ C * ((1 / 3 : ℝ) ^ x.toWord.length) :=
    poisson_kernel_le_on_Tq φ q x hxm
  have hp_abs : |poisson_kernel φ x| = poisson_kernel φ x := abs_of_nonneg hp_nn
  have hp_lt : |poisson_kernel φ x| < ε / 2 := by
    rw [hp_abs]; exact lt_of_le_of_lt hp_le hpbound
  calc |f x - poisson_kernel φ x|
      ≤ |f x| + |poisson_kernel φ x| := abs_sub _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

/-! **Q40 — Uniqueness (`poisson_kernel_unique`):** hoisted to
`EnsX2026.FreeGroup.TreeBoundedHarmonicVanish` (Wave 22F.2.2). See that
file for the statement and proof. -/

/-! ### Q41 — The kernel of the Laplacian on `F_2` is infinite-dimensional -/

open Filter Topology in
/-- Along `φ` itself, `p_φ(φ.valPrefix p) / 3^p = 1` identically, since the
Poisson kernel along its own ray equals `3^p`. -/
private lemma poisson_kernel_ratio_self (φ : ∂F2) (p : ℕ) :
    poisson_kernel φ (φ.valPrefix p) / (3 : ℝ) ^ p = 1 := by
  have h_eq : poisson_kernel φ (φ.valPrefix p) = (3 : ℝ) ^ p := by
    unfold poisson_kernel
    rw [busemann_valPrefix_self]
    simp [zpow_natCast]
  rw [h_eq]
  have h3 : ((3 : ℝ) ^ p) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

open Filter Topology in
/-- For `ψ ≠ φ`, the ratio `p_φ(ψ.valPrefix p) / 3^p` tends to `0`. -/
private lemma poisson_kernel_ratio_other_tendsto_zero
    (φ ψ : ∂F2) (hψ : ψ ≠ φ) :
    Tendsto (fun p : ℕ => poisson_kernel φ (ψ.valPrefix p) / (3 : ℝ) ^ p)
      atTop (nhds (0 : ℝ)) := by
  -- For p ≥ q + 1, poisson_kernel φ (ψ.valPrefix p) = 3^(2q) · (1/3)^p,
  -- so the ratio equals 3^(2q) · (1/9)^p → 0.
  obtain ⟨q, hq_agree, hq_diff⟩ := exists_first_diff φ ψ hψ
  set C : ℝ := (3 : ℝ) ^ (2 * q) with hC_def
  have h_eq : ∀ p : ℕ, q + 1 ≤ p →
      poisson_kernel φ (ψ.valPrefix p) / (3 : ℝ) ^ p = C * ((1 / 9 : ℝ) ^ p) := by
    intro p hp
    unfold poisson_kernel
    rw [busemann_valPrefix_other φ ψ q hq_agree hq_diff hp]
    -- Goal: (3 : ℝ) ^ (-((p : ℤ) - 2 * q)) / 3^p = C * (1/9)^p.
    have h3ne : (3 : ℝ) ≠ 0 := by norm_num
    have h3pne : ((3 : ℝ) ^ p) ≠ 0 := pow_ne_zero _ h3ne
    have h1 : (3 : ℝ) ^ (-((p : ℤ) - 2 * (q : ℤ)))
        = (3 : ℝ) ^ ((2 * (q : ℤ)) + (-(p : ℤ))) := by
      congr 1; ring
    rw [h1, zpow_add₀ h3ne]
    have h2 : (3 : ℝ) ^ (2 * (q : ℤ)) = C := by
      rw [hC_def]
      rw [show (2 * (q : ℤ) : ℤ) = ((2 * q : ℕ) : ℤ) by push_cast; ring]
      rw [zpow_natCast]
    rw [h2]
    -- Goal: C * 3^(-p) / 3^p = C * (1/9)^p.
    rw [zpow_neg, zpow_natCast]
    -- C * (3^p)⁻¹ / 3^p = C * (1/9)^p.
    have h9 : ((1 : ℝ) / 9) ^ p = ((3 : ℝ) ^ p)⁻¹ * ((3 : ℝ) ^ p)⁻¹ := by
      rw [show ((1 : ℝ) / 9) = (1 / 3) * (1 / 3) by norm_num]
      rw [mul_pow]
      rw [show ((1 : ℝ) / 3) = (3 : ℝ)⁻¹ by norm_num]
      rw [inv_pow]
    rw [h9]
    field_simp
  -- (1/9)^p → 0.
  have h_tend : Tendsto (fun p : ℕ => ((1 / 9 : ℝ)) ^ p) atTop (nhds 0) := by
    apply tendsto_pow_atTop_nhds_zero_of_lt_one
    · norm_num
    · norm_num
  have h_tend_mul : Tendsto (fun p : ℕ => C * ((1 / 9 : ℝ)) ^ p) atTop (nhds (C * 0)) :=
    h_tend.const_mul C
  rw [mul_zero] at h_tend_mul
  refine Tendsto.congr' ?_ h_tend_mul
  refine Filter.eventually_atTop.mpr ⟨q + 1, ?_⟩
  intro p hp
  exact (h_eq p hp).symm

open Filter Topology in
/-- **Q41.** For any finite family of distinct boundary points
`φ_1, …, φ_N`, the corresponding Poisson kernels `p_{φ_1}, …, p_{φ_N}`
are linearly independent over `ℝ` in the space `F_2 → ℝ`.

Proof: suppose `∑ φ ∈ φs, c φ • p_φ = 0` as functions on `F_2`. Fix
`φ₀ ∈ φs` and evaluate at `x = φ₀.valPrefix p`, then divide by `3^p`:
the ratio `p_φ (φ₀.valPrefix p) / 3^p` equals `1` for `φ = φ₀` (blowup)
and tends to `0` for `φ ≠ φ₀` (vanish). The sum of finitely many such
ratios tends to `c φ₀`. But the sum is identically `0 / 3^p = 0`, so
`c φ₀ = 0`. -/
theorem poisson_kernels_linearly_independent (φs : Finset ∂F2) :
    LinearIndependent ℝ (fun φ : φs => poisson_kernel φ.val) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg φ₀
  -- `hg` says: the function `∑ φ, g φ • poisson_kernel φ.val` is zero.
  -- Evaluate at each `x`: `∀ x, ∑ φ, g φ * poisson_kernel φ.val x = 0`.
  have hg_pt : ∀ x : F2, ∑ φ : φs, g φ * poisson_kernel φ.val x = 0 := by
    intro x
    have := congrArg (fun f : F2 → ℝ => f x) hg
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    exact this
  -- Evaluate at `φ₀.val.valPrefix p` and divide by `3^p`.
  -- Let `u p := ∑ φ, g φ * (poisson_kernel φ.val (φ₀.val.valPrefix p) / 3^p)`.
  -- Then `u p = (∑ φ, g φ * poisson_kernel φ.val (φ₀.val.valPrefix p)) / 3^p = 0 / 3^p = 0`.
  have h3pos : ∀ p : ℕ, (0 : ℝ) < (3 : ℝ) ^ p := fun p => pow_pos (by norm_num) p
  have h3ne : ∀ p : ℕ, ((3 : ℝ) ^ p) ≠ 0 := fun p => (h3pos p).ne'
  have hu_zero : ∀ p : ℕ,
      ∑ φ : φs, g φ * (poisson_kernel φ.val (φ₀.val.valPrefix p) / (3 : ℝ) ^ p) = 0 := by
    intro p
    have h1 : ∑ φ : φs, g φ * (poisson_kernel φ.val (φ₀.val.valPrefix p) / (3 : ℝ) ^ p)
        = (∑ φ : φs, g φ * poisson_kernel φ.val (φ₀.val.valPrefix p)) / (3 : ℝ) ^ p := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro φ _
      ring
    rw [h1, hg_pt (φ₀.val.valPrefix p)]
    simp
  -- Now show `u p → g φ₀` as `p → ∞`.
  -- The `φ = φ₀` term is constantly `g φ₀ * 1 = g φ₀`.
  -- Every other term `g φ * (ratio → 0) → 0`.
  have h_tend_term : ∀ φ : φs,
      Tendsto (fun p : ℕ => g φ * (poisson_kernel φ.val (φ₀.val.valPrefix p) / (3 : ℝ) ^ p))
        atTop (nhds (if φ = φ₀ then g φ₀ else 0)) := by
    intro φ
    by_cases hφ : φ = φ₀
    · simp only [hφ, if_true]
      -- ratio = 1 identically
      have h_eq : ∀ p, g φ₀ * (poisson_kernel φ₀.val (φ₀.val.valPrefix p) / (3 : ℝ) ^ p)
          = g φ₀ := by
        intro p
        rw [poisson_kernel_ratio_self]
        ring
      exact (tendsto_const_nhds).congr (fun p => (h_eq p).symm)
    · simp only [hφ, if_false]
      have h_ne : φ₀.val ≠ φ.val := fun h => hφ (Subtype.ext h.symm)
      have h_tend :=
        poisson_kernel_ratio_other_tendsto_zero φ.val φ₀.val h_ne
      have := h_tend.const_mul (g φ)
      simp only [mul_zero] at this
      exact this
  -- Sum the tendstos:
  have h_tend_sum :
      Tendsto (fun p : ℕ =>
          ∑ φ : φs, g φ * (poisson_kernel φ.val (φ₀.val.valPrefix p) / (3 : ℝ) ^ p))
        atTop (nhds (∑ φ : φs, (if φ = φ₀ then g φ₀ else 0))) :=
    tendsto_finset_sum _ (fun φ _ => h_tend_term φ)
  -- The limit-sum equals `g φ₀`:
  have h_sum_eq : (∑ φ : φs, (if φ = φ₀ then g φ₀ else 0)) = g φ₀ := by
    rw [Finset.sum_ite_eq' Finset.univ φ₀ (fun _ => g φ₀)]
    simp
  rw [h_sum_eq] at h_tend_sum
  -- But the sum equals the constant `0`, so its limit is `0`:
  have h_tend_zero :
      Tendsto (fun p : ℕ =>
          ∑ φ : φs, g φ * (poisson_kernel φ.val (φ₀.val.valPrefix p) / (3 : ℝ) ^ p))
        atTop (nhds 0) := by
    exact (tendsto_const_nhds).congr (fun p => (hu_zero p).symm)
  -- Uniqueness of limit:
  exact tendsto_nhds_unique h_tend_sum h_tend_zero

/-- **Q41 — Consequence.** The kernel of the combinatorial Laplacian on
`F_2` contains an ℝ-linearly independent family of arbitrary finite
cardinality (one `p_φ` for each `φ ∈ ∂F₂`). In particular, it is not
finite-dimensional.

We phrase this abstractly: for every `N : ℕ`, there exists an
ℝ-linearly independent family of size `N` in the space of functions
`F_2 → ℝ`, each of which is pointwise harmonic (i.e. `Δf = 0` in the
sense of `PointwiseHarmonic φ f` for that function's associated `φ`).

The hypothesis `Infinite ∂F₂` provides `N` distinct boundary points via
`Infinite.natEmbedding`; we then apply
`poisson_kernels_linearly_independent` to their image. -/
theorem laplacian_kernel_infinite_dim
    (h_boundary_infinite : Infinite ∂F2) :
    ∀ N : ℕ, ∃ (F : Fin N → F2 → ℝ),
      LinearIndependent ℝ F ∧
      (∀ i, ∃ φ : ∂F2, F i = poisson_kernel φ ∧ PointwiseHarmonic φ (F i)) := by
  classical
  intro N
  -- Pick `N` distinct boundary points via `Infinite.natEmbedding`.
  let e : ℕ ↪ ∂F2 := Infinite.natEmbedding ∂F2
  let φ : Fin N → ∂F2 := fun i => e i.val
  have hφ_inj : Function.Injective φ := by
    intro i j hij
    have : e i.val = e j.val := hij
    have : i.val = j.val := e.injective this
    exact Fin.ext this
  refine ⟨fun i => poisson_kernel (φ i), ?_, ?_⟩
  · -- Linear independence: embed `Fin N → ∂F2` into a `Finset ∂F2` via `φs := Finset.image φ univ`.
    -- Easier route: build the `Finset` and transport via `LinearIndependent.comp`.
    set φs : Finset ∂F2 := Finset.univ.image φ with hφs
    have hφ_mem : ∀ i : Fin N, φ i ∈ φs := by
      intro i
      rw [hφs]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    -- Subtype map `Fin N → φs`.
    let ι : Fin N → φs := fun i => ⟨φ i, hφ_mem i⟩
    have hι_inj : Function.Injective ι := by
      intro i j hij
      have : φ i = φ j := by
        have := congrArg Subtype.val hij
        exact this
      exact hφ_inj this
    have h_base : LinearIndependent ℝ (fun φ' : φs => poisson_kernel φ'.val) :=
      poisson_kernels_linearly_independent φs
    have : LinearIndependent ℝ ((fun φ' : φs => poisson_kernel φ'.val) ∘ ι) :=
      h_base.comp ι hι_inj
    -- Simplify the composition to `fun i => poisson_kernel (φ i)`.
    convert this
  · -- Every `F i = poisson_kernel (φ i)` is pointwise harmonic.
    intro i
    exact ⟨φ i, rfl, poisson_kernel_pointwise_harmonic (φ i)⟩

end EnsX2026.FreeGroup
