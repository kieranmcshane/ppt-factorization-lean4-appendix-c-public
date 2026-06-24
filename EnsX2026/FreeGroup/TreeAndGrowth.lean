import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce
import EnsX2026.Cayley.Growth
import EnsX2026.Graphs.Laplacian_l2

/-!
# ENS/Polytechnique 2026 Math A — Free group `F_2`, tree, growth, Laplacian (Q34–Q38)

Section 7 of the paper studies the two-generator free group `F_2 = FreeGroup (Fin 2)`,
viewed as a Cayley graph with the canonical symmetric generating set
`{a, b, a⁻¹, b⁻¹}`. The main statements are:

* **Q34(a)** — Structural lemmas for a tree, both fully proven:
  every non-root vertex admits a unique neighbour closer to the root
  (`tree_neighbor_closer_unique`, via the penultimate vertex of the unique
  simple path); every non-trivial closed walk in a tree revisits some vertex
  (`tree_no_nontrivial_closed_path`, the "backtrack" property restated as
  "no non-trivial closed walk is a path").
* **Q34(b)** — Unique simple path between any two vertices
  (`tree_unique_simple_path`), a direct consequence of
  `SimpleGraph.isTree_iff_existsUnique_path`.
* **Q35** — The Cayley graph of `F_2 = FreeGroup (Fin 2)` with the canonical
  symmetric generating set is a tree (`F2_cayley_is_tree`). Connectedness is
  immediate from `Cayley.cayley_graph_connected`; acyclicity is now fully
  formalised by the reduced-word argument: the helper `walkWord` decodes a
  walk into a list of letters, and `walkWord_isReduced` shows that trails
  yield reduced words (consecutive-letter cancellation would repeat an edge).
  A cycle then gives a non-trivial reduced word representing `1`,
  contradicting `FreeGroup.toWord_eq_nil_iff`.
* **Q36** — Uniqueness of the reduced word representing a given element of
  `F_2` (`F2_reduced_word_unique`), a direct consequence of
  `FreeGroup.toWord_injective`.
* **Q37** — The growth function is exponential: `β(k) = 2 · 3^k − 1`
  (`F2_growth`). Both sub-lemmas are fully proven: graph distance equals
  reduced-word length (`F2_dist_eq_toWord_length`), and the combinatorial
  count of reduced words of length `≤ k` is exactly `2·3^k − 1`
  (`F2_card_toWord_length_le`), via an explicit Finset-level recurrence
  parametrized by a "forbidden first letter" (`redAvoid` / `redAll`).
* **Q38** — The Laplacian on `E = F_2 → ℝ` is surjective
  (`F2_laplacian_surjective`). The main theorem is now closed in terms of a
  general `tree_laplacian_lift` lemma (any locally finite tree lifts the
  combinatorial Laplacian); the internal tree recursion in
  `tree_laplacian_lift` itself is recorded as `sorry` with an explicit TODO.

Institut Fourier, Grenoble — Kieran McShane
-/

namespace EnsX2026.FreeGroup

open SimpleGraph

/-! ### Q34(a) — Tree: unique closer neighbour, and no non-trivial closed path -/

section Q34a

variable {V : Type*} {T : SimpleGraph V}

/-- **Q34(a), first part.** In a tree, every vertex `y ≠ x` admits a *unique*
neighbour `z` strictly closer to `x`. Existence uses the penultimate vertex of
a geodesic path from `x` to `y`; uniqueness follows from
`SimpleGraph.isTree_iff_existsUnique_path`.

**Proof.** Let `q` be the unique simple path from `x` to `y` (since `T.IsTree`).
Since `x ≠ y`, `q` has positive length; its penultimate vertex `z := q.penultimate`
is adjacent to `y` and `q.dropLast : T.Walk x z` has length `p - 1`, hence
`T.dist x z ≤ p - 1`; the reverse inequality uses the triangle inequality and
`T.dist z y = 1`. For uniqueness, a second neighbour `z'` of `y` at distance
`p − 1` admits a geodesic `p' : T.Walk x z'` of length `p - 1` that avoids `y`
(else the distance from `x` to `y` would be less than `p`). Then
`p'.concat hadj'.symm` is a path from `x` to `y` of length `p`, so by uniqueness
of simple paths in a tree it equals `q`, and penultimate-preservation under
`concat` forces `z' = z`. -/
theorem tree_neighbor_closer_unique (hT : T.IsTree)
    (x y : V) (hxy : x ≠ y) (p : ℕ) (hp : T.dist x y = p) :
    ∃! z, T.Adj y z ∧ T.dist x z = p - 1 := by
  classical
  -- (1) The unique simple path q : T.Walk x y.
  obtain ⟨q, hqPath, hqUniq⟩ := hT.existsUnique_path x y
  -- (2) A geodesic path q' from x to y has length p = dist x y.
  have hreach : T.Reachable x y := hT.connected x y
  obtain ⟨q', hq'Path, hq'Len⟩ := hreach.exists_path_of_dist
  -- q = q' by uniqueness of paths, hence q.length = p.
  have hqq' : q' = q := hqUniq q' hq'Path
  have hqLen : q.length = p := by rw [← hqq', hq'Len, hp]
  -- (3) p ≥ 1 since x ≠ y.
  have hp_pos : 1 ≤ p := by
    rw [← hp]; exact (hT.connected x y).pos_dist_of_ne hxy
  have hqNonNil : ¬ q.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length, hqLen]; omega
  -- (4) The penultimate vertex z := q.penultimate is adjacent to y.
  set z : V := q.penultimate with hzdef
  have hzy : T.Adj z y := q.adj_penultimate hqNonNil
  -- (5) dist x z = p - 1.
  have hdropLen : q.dropLast.length = p - 1 := by
    rw [SimpleGraph.Walk.length_dropLast, hqLen]
  have hdist_z_le : T.dist x z ≤ p - 1 := by
    rw [← hdropLen]; exact SimpleGraph.dist_le q.dropLast
  have hdist_z_ge : p - 1 ≤ T.dist x z := by
    -- triangle inequality: dist x y ≤ dist x z + dist z y = dist x z + 1
    have htri : T.dist x y ≤ T.dist x z + T.dist z y :=
      (hT.connected).dist_triangle
    have hzy_dist : T.dist z y = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hzy
    rw [hzy_dist, hp] at htri
    omega
  have hdist_z : T.dist x z = p - 1 := le_antisymm hdist_z_le hdist_z_ge
  -- (6) Existence.
  refine ⟨z, ⟨hzy.symm, hdist_z⟩, ?_⟩
  -- (7) Uniqueness.
  rintro z' ⟨hadj', hdist'⟩
  -- Take a geodesic path p' : T.Walk x z' of length p-1.
  have hreach' : T.Reachable x z' := hT.connected x z'
  obtain ⟨p', hp'Path, hp'Len⟩ := hreach'.exists_path_of_dist
  rw [hdist'] at hp'Len
  -- y ∉ p'.support, else a sub-path to y would have length < p.
  have hy_notin : y ∉ p'.support := by
    intro hy
    obtain ⟨r, s, hr, _, heq⟩ := hp'Path.mem_support_iff_exists_append.mp hy
    have hrs : r.length + s.length = p - 1 := by
      have hp'sum : (r.append s).length = p - 1 := heq ▸ hp'Len
      rw [SimpleGraph.Walk.length_append] at hp'sum
      exact hp'sum
    have hrlt : r.length ≤ p - 1 := by omega
    have : p ≤ p - 1 := by
      calc p = T.dist x y := hp.symm
        _ ≤ r.length := SimpleGraph.dist_le r
        _ ≤ p - 1 := hrlt
    omega
  -- p'.concat hadj'.symm is a path from x to y of length p.
  have hpath : (p'.concat hadj'.symm).IsPath := hp'Path.concat hy_notin hadj'.symm
  -- By uniqueness, p'.concat hadj'.symm = q.
  have hconcat_eq : p'.concat hadj'.symm = q := hqUniq _ hpath
  -- Penultimate of p'.concat hadj'.symm is z'.
  have hconcat_pen : (p'.concat hadj'.symm).penultimate = z' :=
    SimpleGraph.Walk.penultimate_concat p' hadj'.symm
  -- So z' = q.penultimate = z.
  rw [← hconcat_pen, hconcat_eq]

/-- **Q34(a), second part (restated).** In a tree, no non-trivial closed walk
is simple. Equivalently, every non-trivial loop has a backtrack / vertex
revisit. This is exactly the meaning of `SimpleGraph.IsAcyclic`: no walk `w : Walk x x`
of positive length is a cycle. We record the fact that a tree is acyclic, which
is precisely this statement.

We phrase it as "a tree has no non-trivial closed walk which is a path". The
trivial closed walk (the nil walk at `x`) *is* a path (of length 0), so the
non-triviality condition `w.length ≠ 0` is required. -/
theorem tree_no_nontrivial_closed_path (hT : T.IsTree) :
    ∀ {x : V} (w : T.Walk x x), w.IsPath → w.length = 0 := by
  intro x w hw
  -- In a tree, the unique simple path from `x` to `x` is the nil walk. Since
  -- `Walk.nil` also has `IsPath` and length `0`, uniqueness forces `w = .nil`
  -- and hence `w.length = 0`.
  have h := (SimpleGraph.isTree_iff_existsUnique_path.mp hT).2 x x
  obtain ⟨q, hqPath, hqUnique⟩ := h
  have h1 : w = q := hqUnique w hw
  have h2 : Walk.nil = q := hqUnique Walk.nil Walk.IsPath.nil
  have : w = (Walk.nil : T.Walk x x) := h1.trans h2.symm
  simp [this]

end Q34a

/-! ### Q34(b) — Unique simple path in a tree -/

section Q34b

variable {V : Type*} {T : SimpleGraph V}

/-- **Q34(b).** In a tree `T`, there is a unique simple path between any two
vertices `x` and `y`. Direct one-liner from
`SimpleGraph.isTree_iff_existsUnique_path`. -/
theorem tree_unique_simple_path (hT : T.IsTree) (x y : V) :
    ∃! p : T.Walk x y, p.IsPath :=
  (SimpleGraph.isTree_iff_existsUnique_path.mp hT).2 x y

end Q34b

/-! ### Q35 — `F_2 = FreeGroup (Fin 2)` and its Cayley graph -/

/-- **`F_2`** — the free group on two generators. -/
abbrev F2 : Type := _root_.FreeGroup (Fin 2)

/-- The canonical symmetric generating set `{a, b, a⁻¹, b⁻¹}` of `F_2`. -/
def F2_generating_set : Set F2 :=
  {_root_.FreeGroup.of (0 : Fin 2), _root_.FreeGroup.of (1 : Fin 2),
   (_root_.FreeGroup.of (0 : Fin 2))⁻¹, (_root_.FreeGroup.of (1 : Fin 2))⁻¹}

/-- The canonical generating set is symmetric: inverses of generators are
generators. -/
lemma F2_generating_set_symmetric :
    ∀ z ∈ F2_generating_set, z⁻¹ ∈ F2_generating_set := by
  intro z hz
  -- `F2_generating_set = {of 0, of 1, (of 0)⁻¹, (of 1)⁻¹}`: inverse of each
  -- lands back in the set.
  rcases hz with h | h | h | h
  · -- z = of 0, z⁻¹ = (of 0)⁻¹
    rw [h]; right; right; left; rfl
  · -- z = of 1, z⁻¹ = (of 1)⁻¹
    rw [h]; right; right; right; rfl
  · -- z = (of 0)⁻¹, z⁻¹ = of 0
    rw [h]; simp only [inv_inv]; left; rfl
  · -- z = (of 1)⁻¹, z⁻¹ = of 1
    rw [h]; simp only [inv_inv]; right; left; rfl

/-- The canonical generating set generates `F_2` as a subgroup. This follows
from the fact that `FreeGroup.of` generates `FreeGroup α` together with the
fact that inverses of a generating set do not enlarge the closure. -/
lemma F2_generating_set_generates :
    Subgroup.closure F2_generating_set = ⊤ := by
  -- The subset `{of 0, of 1}` already generates `F_2` (universal property of
  -- the free group on `Fin 2`), and `F2_generating_set` contains this subset.
  refine top_le_iff.mp ?_
  -- It suffices to show `⊤ ≤ closure F2_generating_set`. We use the fact that
  -- `closure (range of) = ⊤` for a free group; the standard name is
  -- `FreeGroup.closure_range_of`. If unavailable, fall back to a direct
  -- argument via the universal property.
  rw [← _root_.FreeGroup.closure_range_of (α := Fin 2)]
  apply Subgroup.closure_mono
  intro x hx
  rcases hx with ⟨i, hi⟩
  fin_cases i
  · rw [← hi]; left; rfl
  · rw [← hi]; right; left; rfl

/-- `mk [(a, true)] = of a`: by definition of `of`. -/
private lemma mk_singleton_true (a : Fin 2) :
    _root_.FreeGroup.mk [(a, true)] = _root_.FreeGroup.of a := rfl

/-- `mk [(a, false)] = (of a)⁻¹`: by `inv_mk` together with `invRev` on a singleton. -/
private lemma mk_singleton_false (a : Fin 2) :
    _root_.FreeGroup.mk [(a, false)] = (_root_.FreeGroup.of a)⁻¹ := by
  rw [← mk_singleton_true, _root_.FreeGroup.inv_mk]
  rfl

/-- From an adjacency `u ~ v` in the Cayley graph of `F_2`, we can extract a
letter `ℓ : Fin 2 × Bool` with `mk [ℓ] = u⁻¹ * v`. This is used to decode a
walk into a word of the same length. -/
private lemma exists_letter_of_adj {u v : F2}
    (hadj : (EnsX2026.Cayley.cayley_graph F2_generating_set).Adj u v) :
    ∃ ℓ : Fin 2 × Bool, _root_.FreeGroup.mk [ℓ] = u⁻¹ * v := by
  rw [EnsX2026.Cayley.cayley_graph_adj] at hadj
  obtain ⟨_hne, hcase⟩ := hadj
  have huv_mem : u⁻¹ * v ∈ F2_generating_set := by
    rcases hcase with ⟨z, hz, hv⟩ | ⟨z, hz, hu⟩
    · have : u⁻¹ * v = z := by rw [hv]; group
      rw [this]; exact hz
    · have : u⁻¹ * v = z⁻¹ := by rw [hu]; group
      rw [this]; exact F2_generating_set_symmetric z hz
  rcases huv_mem with h | h | h | h
  · exact ⟨(0, true), by rw [h]; exact mk_singleton_true 0⟩
  · exact ⟨(1, true), by rw [h]; exact mk_singleton_true 1⟩
  · exact ⟨(0, false), by rw [h]; exact mk_singleton_false 0⟩
  · exact ⟨(1, false), by rw [h]; exact mk_singleton_false 1⟩

/-- Noncomputable choice of a letter for each adjacency in the Cayley graph of
`F_2`. -/
private noncomputable def edgeLetter {u v : F2}
    (hadj : (EnsX2026.Cayley.cayley_graph F2_generating_set).Adj u v) :
    Fin 2 × Bool :=
  Classical.choose (exists_letter_of_adj hadj)

private lemma mk_edgeLetter {u v : F2}
    (hadj : (EnsX2026.Cayley.cayley_graph F2_generating_set).Adj u v) :
    _root_.FreeGroup.mk [edgeLetter hadj] = u⁻¹ * v :=
  Classical.choose_spec (exists_letter_of_adj hadj)

/-- Convert a walk in the Cayley graph of `F_2` to a list of letters (a word
in `Fin 2 × Bool`). Each step along the walk contributes the chosen `edgeLetter`
of its adjacency. -/
private noncomputable def walkWord : ∀ {a b : F2},
    (EnsX2026.Cayley.cayley_graph F2_generating_set).Walk a b →
      List (Fin 2 × Bool)
  | _, _, SimpleGraph.Walk.nil => []
  | _, _, SimpleGraph.Walk.cons h q => edgeLetter h :: walkWord q

@[simp] private lemma walkWord_nil {a : F2} :
    walkWord (SimpleGraph.Walk.nil : (EnsX2026.Cayley.cayley_graph
      F2_generating_set).Walk a a) = [] := rfl

@[simp] private lemma walkWord_cons {a b c : F2}
    (h : (EnsX2026.Cayley.cayley_graph F2_generating_set).Adj a b)
    (q : (EnsX2026.Cayley.cayley_graph F2_generating_set).Walk b c) :
    walkWord (SimpleGraph.Walk.cons h q) = edgeLetter h :: walkWord q := rfl

private lemma walkWord_length : ∀ {a b : F2}
    (q : (EnsX2026.Cayley.cayley_graph F2_generating_set).Walk a b),
    (walkWord q).length = q.length
  | _, _, SimpleGraph.Walk.nil => rfl
  | _, _, SimpleGraph.Walk.cons _ q => by
    simp [walkWord, SimpleGraph.Walk.length_cons, walkWord_length q]

private lemma mk_walkWord : ∀ {a b : F2}
    (q : (EnsX2026.Cayley.cayley_graph F2_generating_set).Walk a b),
    _root_.FreeGroup.mk (walkWord q) = a⁻¹ * b
  | _, _, SimpleGraph.Walk.nil => by
    rw [walkWord_nil,
      show _root_.FreeGroup.mk ([] : List (Fin 2 × Bool)) = (1 : F2)
        from (_root_.FreeGroup.one_eq_mk).symm, inv_mul_cancel]
  | _, _, @SimpleGraph.Walk.cons _ _ u v w hadj q => by
    rw [walkWord_cons]
    have hcons : _root_.FreeGroup.mk (edgeLetter hadj :: walkWord q)
        = _root_.FreeGroup.mk [edgeLetter hadj] * _root_.FreeGroup.mk (walkWord q) := by
      rw [show (edgeLetter hadj :: walkWord q)
          = [edgeLetter hadj] ++ walkWord q from rfl,
          ← _root_.FreeGroup.mul_mk]
    rw [hcons, mk_edgeLetter, mk_walkWord q]
    group

/-- Key lemma: if two letters `ℓ, ℓ'` cancel (same first component, opposite
second), then their `mk`-images are inverses. -/
private lemma mk_singleton_inv_of_cancel {ℓ ℓ' : Fin 2 × Bool}
    (hfst : ℓ.1 = ℓ'.1) (hsnd : ℓ.2 ≠ ℓ'.2) :
    _root_.FreeGroup.mk [ℓ'] = (_root_.FreeGroup.mk [ℓ] : F2)⁻¹ := by
  obtain ⟨a, b⟩ := ℓ
  obtain ⟨a', b'⟩ := ℓ'
  simp at hfst
  subst hfst
  have hb : b' = !b := by cases b <;> cases b' <;> simp_all
  subst hb
  cases b
  · simp only [Bool.not_false]
    rw [mk_singleton_true, mk_singleton_false, inv_inv]
  · simp only [Bool.not_true]
    rw [mk_singleton_false, mk_singleton_true]

/-- Key lemma: if the first two edges of a walk have "cancelling" letters,
the second vertex of the walk equals the starting vertex. Specifically, for
`cons hadj (cons hadj' q'')`, if `ℓ := edgeLetter hadj` and
`ℓ' := edgeLetter hadj'` cancel, then the endpoint of `hadj'` equals the
starting vertex. This forces an edge repetition. -/
private lemma walkWord_isReduced : ∀ {a b : F2}
    (q : (EnsX2026.Cayley.cayley_graph F2_generating_set).Walk a b),
    q.IsTrail → _root_.FreeGroup.IsReduced (walkWord q)
  | _, _, SimpleGraph.Walk.nil => fun _ => by
    rw [walkWord_nil]; exact _root_.FreeGroup.IsReduced.nil
  | _, _, @SimpleGraph.Walk.cons _ _ u v w hadj q => fun hq_trail => by
    rw [walkWord_cons]
    have hq_trail' : q.IsTrail := SimpleGraph.Walk.IsTrail.of_cons hq_trail
    have hedge_notin : s(u, v) ∉ q.edges := by
      have := (SimpleGraph.Walk.isTrail_cons hadj q).mp hq_trail
      exact this.2
    -- Recurse: the rest of the walk has a reduced word.
    have hq_red : _root_.FreeGroup.IsReduced (walkWord q) := walkWord_isReduced q hq_trail'
    -- Case on the shape of q.
    match q, hq_trail', hedge_notin, hq_red with
    | SimpleGraph.Walk.nil, _, _, _ =>
      rw [walkWord_nil]
      exact _root_.FreeGroup.IsReduced.singleton
    | @SimpleGraph.Walk.cons _ _ _ v' w' hadj' q'', hq_trail', hedge_notin, hq_red =>
      -- Walk is cons hadj (cons hadj' q''). Letters: ℓ = edgeLetter hadj,
      -- ℓ' = edgeLetter hadj'. We need: not (ℓ.1 = ℓ'.1 ∧ ℓ.2 ≠ ℓ'.2).
      rw [walkWord_cons]
      rw [_root_.FreeGroup.isReduced_cons_cons]
      refine ⟨?_, ?_⟩
      · -- ℓ, ℓ' do not cancel.
        intro hfst
        by_contra hsnd
        -- If they cancel, mk [ℓ'] = (mk [ℓ])⁻¹, so v⁻¹ * v' = (u⁻¹ * v)⁻¹ = v⁻¹ * u.
        have hinv := mk_singleton_inv_of_cancel hfst hsnd
        rw [mk_edgeLetter, mk_edgeLetter] at hinv
        have heq : v⁻¹ * v' = v⁻¹ * u := by
          rw [hinv]; rw [mul_inv_rev, inv_inv]
        have hv'_u : v' = u := mul_left_cancel heq
        -- Hence edge s(v, v') = s(v, u) = s(u, v), first edge of `cons hadj' q''`.
        apply hedge_notin
        show s(u, v) ∈ (SimpleGraph.Walk.cons hadj' q'').edges
        rw [SimpleGraph.Walk.edges_cons]
        -- Goal: s(u, v) ∈ s(v, v') :: q''.edges. Use hv'_u : v' = u.
        subst hv'_u
        simp [Sym2.eq_swap]
      · -- The tail `walkWord (cons hadj' q'') = ℓ' :: walkWord q''` is reduced
        -- (from hq_red).
        have : walkWord (SimpleGraph.Walk.cons hadj' q'')
            = edgeLetter hadj' :: walkWord q'' := rfl
        rw [this] at hq_red
        exact hq_red

/-- **Q35.** The Cayley graph of `F_2` with the canonical symmetric generating
set `{a, b, a⁻¹, b⁻¹}` is a tree.

* Connectedness follows from `Cayley.cayley_graph_connected` applied to
  `F2_generating_set_symmetric` and `F2_generating_set_generates`.
* Acyclicity: a cycle at `v` would yield a non-empty reduced word `w` with
  `mk w = v⁻¹ * v = 1`, contradicting `FreeGroup.toWord_eq_nil_iff` via
  `FreeGroup.toWord_mk` and `IsReduced.reduce_eq`. The reduction property
  comes from `walkWord_isReduced`: in a trail, consecutive letters cannot
  cancel because that would repeat an edge. -/
theorem F2_cayley_is_tree :
    (EnsX2026.Cayley.cayley_graph F2_generating_set).IsTree := by
  refine ⟨?_, ?_⟩
  · exact EnsX2026.Cayley.cayley_graph_connected F2_generating_set
      F2_generating_set_symmetric F2_generating_set_generates
  · -- Acyclicity: no cycle exists.
    intro v c hc
    -- A cycle is a trail (from IsCircuit).
    have hc_trail : c.IsTrail := hc.isCircuit.isTrail
    -- A cycle has length ≥ 3.
    have hc_len : 3 ≤ c.length := hc.three_le_length
    -- Apply the strengthened word extraction: cycle ⟹ reduced word of its length.
    set w := walkWord c
    have hred : _root_.FreeGroup.IsReduced w := walkWord_isReduced c hc_trail
    have hmk : _root_.FreeGroup.mk w = (v : F2)⁻¹ * v := mk_walkWord c
    have hwlen : w.length = c.length := walkWord_length c
    -- `mk w = v⁻¹ * v = 1`.
    have hmk1 : _root_.FreeGroup.mk w = (1 : F2) := by rw [hmk, inv_mul_cancel]
    -- `w.toWord = reduce w = w` (since reduced), and `(mk w).toWord = []` (since = 1).
    have h1 : (_root_.FreeGroup.mk w : F2).toWord = [] := by
      rw [hmk1]; exact _root_.FreeGroup.toWord_one
    rw [_root_.FreeGroup.toWord_mk, hred.reduce_eq] at h1
    -- So `w = []`, hence `w.length = 0`, contradicting `hwlen` and `hc_len`.
    rw [h1] at hwlen
    simp at hwlen
    omega

/-! ### Q36 — Uniqueness of reduced word -/

/-- **Q36.** Every element `x : F_2` admits a unique *reduced* word
representation. This is exactly `FreeGroup.toWord_injective` packaged as a
`∃!`: existence via `x.toWord` with `FreeGroup.mk_toWord` and
`FreeGroup.isReduced_toWord`; uniqueness via `FreeGroup.toWord_injective`. -/
theorem F2_reduced_word_unique (x : F2) :
    ∃! w : List (Fin 2 × Bool),
      _root_.FreeGroup.IsReduced w ∧ _root_.FreeGroup.mk w = x := by
  refine ⟨x.toWord, ⟨_root_.FreeGroup.isReduced_toWord, _root_.FreeGroup.mk_toWord⟩, ?_⟩
  rintro w ⟨hred, hmk⟩
  -- Apply `toWord` to both sides of `mk w = x`, and use `toWord_mk`.
  have h1 : (_root_.FreeGroup.mk w).toWord = x.toWord := by rw [hmk]
  rw [_root_.FreeGroup.toWord_mk] at h1
  -- `reduce w = w` because `w` is reduced.
  rw [_root_.FreeGroup.IsReduced.reduce_eq hred] at h1
  exact h1

/-! ### Q37 — Growth function `β(k) = 2 · 3^k - 1`

The Cayley graph of `F_2` with the four canonical generators is a 4-regular
tree. Counting vertices at each radius:

* `|sphere(0)| = 1` (just the identity).
* For `k ≥ 1`, `|sphere(k)| = 4 · 3^{k-1}`: each reduced word of length `k-1`
  has `3` extensions by a generator different from the inverse of the last
  letter.

Summing:
`β(k) = 1 + Σ_{j=1}^{k} 4 · 3^{j-1} = 1 + 4 · (3^k − 1)/2 = 2 · 3^k − 1`.
-/

/-- Number of reduced words of length exactly `k` over the alphabet
`Fin 2 × Bool` (with `4` letters, no immediate cancellation).

For `k = 0`: `1` (empty word).
For `k ≥ 1`: `4 · 3^(k-1)`. -/
def reducedWordCount : ℕ → ℕ
  | 0 => 1
  | k + 1 => if k = 0 then 4 else 4 * 3 ^ k

/-- Encode a letter `(a, b) : Fin 2 × Bool` as an element of `F_2` via
`mk [(a, b)]`: this is `of a` when `b = true`, and `(of a)⁻¹` when `b = false`.
In both cases the resulting element lies in `F2_generating_set`. -/
private lemma mk_singleton_mem_gen (p : Fin 2 × Bool) :
    _root_.FreeGroup.mk [p] ∈ F2_generating_set := by
  obtain ⟨a, b⟩ := p
  -- Two cases on `a : Fin 2` and two on `b : Bool`.
  fin_cases a <;> cases b
  · -- (0, false): mk [(0, false)] = (of 0)⁻¹
    rw [mk_singleton_false]; right; right; left; rfl
  · -- (0, true): mk [(0, true)] = of 0
    rw [mk_singleton_true]; left; rfl
  · -- (1, false): mk [(1, false)] = (of 1)⁻¹
    rw [mk_singleton_false]; right; right; right; rfl
  · -- (1, true): mk [(1, true)] = of 1
    rw [mk_singleton_true]; right; left; rfl

/-- A single letter `mk [(a, b)]` is never equal to `1 : F_2`. -/
private lemma mk_singleton_ne_one (p : Fin 2 × Bool) :
    _root_.FreeGroup.mk [p] ≠ (1 : F2) := by
  intro h
  -- If `mk [p] = 1`, then `toWord (mk [p]) = []`.
  have h1 : (_root_.FreeGroup.mk [p]).toWord = [] := by
    rw [h]; exact _root_.FreeGroup.toWord_one
  -- But `toWord (mk [p]) = reduce [p] = [p]`.
  rw [_root_.FreeGroup.toWord_mk] at h1
  -- A single-letter list is reduced.
  rw [_root_.FreeGroup.IsReduced.reduce_eq _root_.FreeGroup.IsReduced.singleton] at h1
  exact List.cons_ne_nil _ _ h1

/-- Existence of a walk of length `w.length` from `y` to `y * mk w`, for any
word `w : List (Fin 2 × Bool)`. We phrase as an existential so the length
equation is part of the statement, avoiding dependent-equation issues.
We use `Walk.copy` for endpoint casts, which has a dedicated
`length_copy : (p.copy hu hv).length = p.length` simp lemma. -/
private lemma exists_walk_of_word (y : F2) (w : List (Fin 2 × Bool)) :
    ∃ q : (EnsX2026.Cayley.cayley_graph F2_generating_set).Walk y
      (y * _root_.FreeGroup.mk w), q.length = w.length := by
  induction w generalizing y with
  | nil =>
    -- `y * mk [] = y`. Use `Walk.nil` copied to endpoint `y * mk []`.
    have h : y = y * _root_.FreeGroup.mk ([] : List (Fin 2 × Bool)) := by
      rw [show _root_.FreeGroup.mk ([] : List (Fin 2 × Bool))
          = (1 : F2) from (_root_.FreeGroup.one_eq_mk).symm, mul_one]
    refine ⟨((SimpleGraph.Walk.nil : (EnsX2026.Cayley.cayley_graph
        F2_generating_set).Walk y y)).copy rfl h, ?_⟩
    simp
  | cons p rest ih =>
    -- `mk (p :: rest) = mk [p] * mk rest`, so `y * mk (p :: rest) = (y * mk [p]) * mk rest`.
    have hmk : _root_.FreeGroup.mk (p :: rest) =
        _root_.FreeGroup.mk [p] * _root_.FreeGroup.mk rest := by
      rw [_root_.FreeGroup.mul_mk]; rfl
    -- Adjacency: y -- y * mk [p].
    have hadj : (EnsX2026.Cayley.cayley_graph F2_generating_set).Adj
        y (y * _root_.FreeGroup.mk [p]) :=
      EnsX2026.Cayley.cayley_graph_adj_mul F2_generating_set
        (mk_singleton_mem_gen p) (mk_singleton_ne_one p)
    -- Recurse from the new vertex.
    obtain ⟨qrec, hqlen⟩ := ih (y * _root_.FreeGroup.mk [p])
    -- Endpoints: (y * mk [p]) * mk rest = y * mk (p :: rest).
    have hend : (y * _root_.FreeGroup.mk [p]) * _root_.FreeGroup.mk rest
        = y * _root_.FreeGroup.mk (p :: rest) := by
      rw [hmk, mul_assoc]
    refine ⟨SimpleGraph.Walk.cons hadj (qrec.copy rfl hend), ?_⟩
    simp [hqlen]

/-- **Sub-lemma 1 for Q37.** The graph distance in the Cayley graph of `F_2`
from the identity to `x` equals the length of the (unique) reduced word
representing `x`.

**Proof.** (≤) Given `x : F_2`, build an explicit walk of length
`x.toWord.length` from `1` to `x` via `walkFromWord 1 x.toWord`: its endpoint is
`1 * mk x.toWord = x` by `mk_toWord`. Then `dist 1 x ≤ x.toWord.length`
by `dist_le`.

(≥) Any walk `p : Walk 1 x` of length `n` can be "read as a word":
each step `y → y * g` (with `g ∈ F2_generating_set`, i.e. `g = mk [ℓ]` for a
single letter `ℓ`) or `y → y * g⁻¹` contributes a letter to a list `w` with
`mk w = x` and `w.length = n`. Then `x.toWord.length = norm x ≤ w.length = n`
by `norm_mk_le`. Minimising over walks gives `x.toWord.length ≤ dist 1 x`. -/
private lemma F2_dist_eq_toWord_length (x : F2) :
    (EnsX2026.Cayley.cayley_graph F2_generating_set).dist 1 x = x.toWord.length := by
  -- (≤) direction: build an explicit walk from 1 to x of length x.toWord.length.
  have h_le : (EnsX2026.Cayley.cayley_graph F2_generating_set).dist 1 x
      ≤ x.toWord.length := by
    -- Obtain a walk from 1 to 1 * mk x.toWord = x of length x.toWord.length.
    obtain ⟨q, hqlen⟩ := exists_walk_of_word 1 x.toWord
    have hend : (1 : F2) * _root_.FreeGroup.mk x.toWord = x := by
      rw [one_mul, _root_.FreeGroup.mk_toWord]
    -- Transport endpoint using `Walk.copy` and conclude.
    let walk : (EnsX2026.Cayley.cayley_graph F2_generating_set).Walk 1 x :=
      q.copy rfl hend
    have hwalk_len : walk.length = x.toWord.length := by
      show (q.copy rfl hend).length = x.toWord.length
      rw [SimpleGraph.Walk.length_copy, hqlen]
    calc (EnsX2026.Cayley.cayley_graph F2_generating_set).dist 1 x
        ≤ walk.length := SimpleGraph.dist_le walk
      _ = x.toWord.length := hwalk_len
  -- (≥) direction: every walk from `y` to `y'` gives a word `w` with
  -- `mk w = y⁻¹ * y'` and `w.length = p.length`.
  -- Applied at `y = 1, y' = x`: a walk from 1 to x of length n gives a word
  -- `w` with `mk w = x` and `w.length = n`, so `x.toWord.length ≤ n`.
  have h_ge : x.toWord.length
      ≤ (EnsX2026.Cayley.cayley_graph F2_generating_set).dist 1 x := by
    -- Extract the shortest walk via `Reachable.exists_walk_length_eq_dist`.
    have hconn : (EnsX2026.Cayley.cayley_graph F2_generating_set).Connected :=
      EnsX2026.Cayley.cayley_graph_connected F2_generating_set
        F2_generating_set_symmetric F2_generating_set_generates
    obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist 1 x
    -- Prove the generic statement: given any walk `q : Walk a b`, there exists
    -- `w : List (Fin 2 × Bool)` with `mk w = a⁻¹ * b` and `w.length = q.length`.
    have key : ∀ {a b : F2}
        (q : (EnsX2026.Cayley.cayley_graph F2_generating_set).Walk a b),
        ∃ w : List (Fin 2 × Bool),
          _root_.FreeGroup.mk w = a⁻¹ * b ∧ w.length = q.length := by
      intro a b q
      induction q with
      | nil =>
        refine ⟨[], ?_, rfl⟩
        -- mk [] = 1 = a⁻¹ * a in the nil case.
        rw [show _root_.FreeGroup.mk ([] : List (Fin 2 × Bool)) = (1 : F2)
              from (_root_.FreeGroup.one_eq_mk).symm, inv_mul_cancel]
      | @cons u v w hadj q' ih =>
        -- hadj : Adj u v; q' : Walk v w; ih : ∃ w', mk w' = v⁻¹ * w ∧ w'.length = q'.length
        obtain ⟨w', hmk', hlen'⟩ := ih
        -- Decode the edge `u → v`: either v = u * z or u = v * z, for some z ∈ Z.
        rw [EnsX2026.Cayley.cayley_graph_adj] at hadj
        obtain ⟨_hne, hcase⟩ := hadj
        -- In either case, we can write `u⁻¹ * v = mk [ℓ]` for some letter `ℓ`.
        -- Case 1: v = u * z with z ∈ Z. Then u⁻¹ * v = z, and z is one of the
        -- four canonical generators, hence `z = mk [ℓ]` for the letter ℓ.
        -- Case 2: u = v * z with z ∈ Z. Then u⁻¹ * v = z⁻¹, and z⁻¹ is the
        -- inverse of a canonical generator, which is again one of the four
        -- canonical generators, hence `z⁻¹ = mk [ℓ']` for some letter ℓ'.
        -- Unified: u⁻¹ * v ∈ F2_generating_set, and each element of
        -- F2_generating_set is `mk [ℓ]` for a unique letter ℓ.
        have huv_mem : u⁻¹ * v ∈ F2_generating_set := by
          rcases hcase with ⟨z, hz, hv⟩ | ⟨z, hz, hu⟩
          · -- v = u * z ⟹ u⁻¹ * v = z
            have : u⁻¹ * v = z := by rw [hv]; group
            rw [this]; exact hz
          · -- u = v * z ⟹ u⁻¹ * v = z⁻¹
            have : u⁻¹ * v = z⁻¹ := by rw [hu]; group
            rw [this]; exact F2_generating_set_symmetric z hz
        -- Each element of F2_generating_set is `mk [ℓ]` for some letter ℓ.
        obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Fin 2 × Bool, _root_.FreeGroup.mk [ℓ] = u⁻¹ * v := by
          rcases huv_mem with h | h | h | h
          · exact ⟨(0, true), by rw [h]; exact mk_singleton_true 0⟩
          · exact ⟨(1, true), by rw [h]; exact mk_singleton_true 1⟩
          · exact ⟨(0, false), by rw [h]; exact mk_singleton_false 0⟩
          · exact ⟨(1, false), by rw [h]; exact mk_singleton_false 1⟩
        -- Prepend `ℓ` to `w'`: the word `ℓ :: w'` has length `q'.length + 1`
        -- and satisfies `mk (ℓ :: w') = mk [ℓ] * mk w' = (u⁻¹ * v) * (v⁻¹ * w)
        -- = u⁻¹ * w`.
        refine ⟨ℓ :: w', ?_, ?_⟩
        · -- `mk (ℓ :: w') = mk [ℓ] ++ mk w' = (u⁻¹ * v) * (v⁻¹ * w)`.
          have hcons : _root_.FreeGroup.mk (ℓ :: w')
              = _root_.FreeGroup.mk [ℓ] * _root_.FreeGroup.mk w' := by
            rw [_root_.FreeGroup.mul_mk]; rfl
          rw [hcons, hℓ, hmk']
          group
        · simp [hlen']
    obtain ⟨w, hmk, hwlen⟩ := key p
    -- `x.toWord.length = norm x ≤ w.length = p.length = dist 1 x`.
    have : x.toWord.length ≤ w.length := by
      have : _root_.FreeGroup.norm x ≤ w.length := by
        have hx : x = _root_.FreeGroup.mk w := by rw [hmk]; group
        rw [hx]; exact _root_.FreeGroup.norm_mk_le
      exact this
    omega
  exact le_antisymm h_le h_ge

/-! #### Sub-lemma 2 for Q37 — counting reduced words of length `≤ k`

We prove that the number of reduced words of length `≤ k` over the alphabet
`Fin 2 × Bool` (four letters, no immediate cancellation) is exactly
`2 · 3^k − 1`, and conclude the statement of `F2_card_toWord_length_le`
via the bijection `x ↦ x.toWord`.

The count uses an auxiliary family: for each "forbidden first letter"
`ℓfb : Fin 2 × Bool`, let `redAvoid ℓfb k` denote the Finset of reduced
words of length `≤ k` whose first letter (if any) is not `ℓfb`. Let
`redAll k` denote the Finset of all reduced words of length `≤ k`.

Recurrences (for `k ≥ 0`):
* `|redAll (k+1)|      = 1 + 4 · |redAvoid (invLetter ℓ) k|`;
* `|redAvoid ℓfb (k+1)| = 1 + 3 · |redAvoid (invLetter ℓ) k|`.

Both counts are invariant in the specific forbidden letter (only the count
depends, not the choice of `ℓfb`), so the recurrences close at the level
of cardinalities:

* `g(k+1) = 1 + 4 h(k)` with `g(k) = 2·3^k − 1`;
* `h(k+1) = 1 + 3 h(k)` with `h(k) = (3^(k+1) − 1)/2`.

The `F2`-subtype count follows by bijecting with `redAll k` via
`toWord` / `mk`. -/

/-- Count of reduced words of length ≤ k whose first letter (if any) is not
equal to the specified forbidden letter `ℓfb`. For `k = 0` this is `1`
(the empty word); for `k ≥ 1`, by the recurrence `h(k+1) = 1 + 3·h(k)` with
solution `h(k) = (3^(k+1) - 1)/2`. -/
private def redAvoidCount : ℕ → ℕ
  | 0 => 1
  | k+1 => 1 + 3 * redAvoidCount k

/-- Count of all reduced words of length ≤ k (no first-letter constraint).
`g(0) = 1`, `g(k+1) = 1 + 4 · redAvoidCount k = 2 * 3^k - 1` in closed form. -/
private def redAllCount : ℕ → ℕ
  | 0 => 1
  | k+1 => 1 + 4 * redAvoidCount k

/-- Closed form for `redAvoidCount`: `redAvoidCount k = (3^(k+1) - 1) / 2`.
We state it as `2 * redAvoidCount k = 3^(k+1) - 1` to avoid nat division. -/
private lemma redAvoidCount_formula (k : ℕ) : 2 * redAvoidCount k + 1 = 3 ^ (k+1) := by
  induction k with
  | zero => decide
  | succ k ih =>
    -- redAvoidCount (k+1) = 1 + 3 * redAvoidCount k
    -- Goal: 2 * (1 + 3 * redAvoidCount k) + 1 = 3 ^ (k+2)
    -- = 3 + 6 * redAvoidCount k + 1 = ... actually: 2 + 6 * redAvoidCount k + 1 = 3 + 6 * redAvoidCount k
    -- And 3 ^ (k+2) = 3 * 3 ^ (k+1) = 3 * (2 * redAvoidCount k + 1) = 6 * redAvoidCount k + 3. ✓
    show 2 * (1 + 3 * redAvoidCount k) + 1 = 3 ^ (k+2)
    have : 3 ^ (k+2) = 3 * 3 ^ (k+1) := by ring
    rw [this, ← ih]
    ring

/-- Closed form for `redAllCount`: `redAllCount k = 2 * 3^k - 1`. -/
private lemma redAllCount_formula (k : ℕ) : redAllCount k = 2 * 3 ^ k - 1 := by
  match k with
  | 0 => decide
  | k+1 =>
    -- redAllCount (k+1) = 1 + 4 * redAvoidCount k
    -- Target: 2 * 3^(k+1) - 1.
    -- 2 * redAvoidCount k + 1 = 3^(k+1), so 2 * redAvoidCount k = 3^(k+1) - 1.
    -- Thus 4 * redAvoidCount k = 2 * 3^(k+1) - 2, and 1 + 4 * redAvoidCount k = 2 * 3^(k+1) - 1.
    show 1 + 4 * redAvoidCount k = 2 * 3 ^ (k+1) - 1
    have h := redAvoidCount_formula k
    -- h : 2 * redAvoidCount k + 1 = 3 ^ (k+1).
    -- 3 ^ (k+1) ≥ 1.
    have h3 : 1 ≤ 3 ^ (k+1) := Nat.one_le_pow _ _ (by decide)
    omega

/-- The forbidden-letter count gives a clean recurrence useful for the
cardinality proof: `redAvoidCount (k+1) = 1 + 3 * redAvoidCount k`. -/
private lemma redAvoidCount_succ (k : ℕ) :
    redAvoidCount (k+1) = 1 + 3 * redAvoidCount k := rfl

/-- For `ℓ : Fin 2 × Bool`, the "inverse letter" `(ℓ.1, !ℓ.2)`. -/
private def invLetter (ℓ : Fin 2 × Bool) : Fin 2 × Bool := (ℓ.1, !ℓ.2)

/-- A `Finset` of reduced words of length `≤ k` whose first letter (if any) is
not equal to `ℓfb`. We work directly with `Finset.filter` and inductively
strengthen the count. -/
private noncomputable def redAvoid (ℓfb : Fin 2 × Bool) : ℕ → Finset (List (Fin 2 × Bool))
  | 0 => {([] : List (Fin 2 × Bool))}
  | k+1 =>
    let base : Finset (List (Fin 2 × Bool)) := {([] : List (Fin 2 × Bool))}
    -- non-empty words: pick a first letter ℓ ≠ ℓfb, then a tail of length ≤ k
    -- avoiding invLetter ℓ, and cons them.
    let extension : Finset (List (Fin 2 × Bool)) :=
      ((Finset.univ : Finset (Fin 2 × Bool)).filter (· ≠ ℓfb)).biUnion fun ℓ =>
        (redAvoid (invLetter ℓ) k).image (fun tail => ℓ :: tail)
    base ∪ extension

/-- `Finset` of all reduced words of length `≤ k` (no first-letter constraint).
Defined analogously. -/
private noncomputable def redAll : ℕ → Finset (List (Fin 2 × Bool))
  | 0 => {([] : List (Fin 2 × Bool))}
  | k+1 =>
    let base : Finset (List (Fin 2 × Bool)) := {([] : List (Fin 2 × Bool))}
    let extension : Finset (List (Fin 2 × Bool)) :=
      (Finset.univ : Finset (Fin 2 × Bool)).biUnion fun ℓ =>
        (redAvoid (invLetter ℓ) k).image (fun tail => ℓ :: tail)
    base ∪ extension

/-- Membership criterion for `redAvoid ℓfb k`: an element is a reduced word of
length ≤ k whose first letter (if any) is not `ℓfb`. -/
private lemma mem_redAvoid {ℓfb : Fin 2 × Bool} {k : ℕ} {w : List (Fin 2 × Bool)} :
    w ∈ redAvoid ℓfb k ↔
      _root_.FreeGroup.IsReduced w ∧ w.length ≤ k ∧
        (∀ ℓ', w.head? = some ℓ' → ℓ' ≠ ℓfb) := by
  induction k generalizing ℓfb w with
  | zero =>
    show w ∈ ({([] : List (Fin 2 × Bool))} : Finset _) ↔
      _root_.FreeGroup.IsReduced w ∧ w.length ≤ 0 ∧
      (∀ ℓ', w.head? = some ℓ' → ℓ' ≠ ℓfb)
    rw [Finset.mem_singleton]
    constructor
    · rintro rfl
      refine ⟨_root_.FreeGroup.IsReduced.nil, le_refl _, ?_⟩
      intro ℓ' h; simp at h
    · rintro ⟨_, hlen, _⟩
      exact List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
  | succ k ih =>
    simp only [redAvoid]
    constructor
    · intro hw
      rcases Finset.mem_union.mp hw with h | h
      · -- w = []
        simp at h
        subst h
        refine ⟨_root_.FreeGroup.IsReduced.nil, by simp, ?_⟩
        intro ℓ' h; simp at h
      · -- w ∈ biUnion of extensions
        rw [Finset.mem_biUnion] at h
        obtain ⟨ℓ, hℓmem, hℓ⟩ := h
        rw [Finset.mem_image] at hℓ
        obtain ⟨tail, htail, heq⟩ := hℓ
        rw [Finset.mem_filter] at hℓmem
        obtain ⟨_, hℓne⟩ := hℓmem
        have htail' := (ih (ℓfb := invLetter ℓ) (w := tail)).mp htail
        obtain ⟨hred_tail, hlen_tail, hhead_tail⟩ := htail'
        -- w = ℓ :: tail
        subst heq
        refine ⟨?_, by simp; omega, ?_⟩
        · -- IsReduced (ℓ :: tail)
          cases tail with
          | nil => exact _root_.FreeGroup.IsReduced.singleton
          | cons ℓ' rest =>
            rw [_root_.FreeGroup.isReduced_cons_cons]
            refine ⟨?_, hred_tail⟩
            -- ℓ.1 = ℓ'.1 → ℓ.2 = ℓ'.2
            intro hfst
            -- We have: (ℓ' :: rest).head? = some ℓ', so ℓ' ≠ invLetter ℓ = (ℓ.1, !ℓ.2).
            have hhd := hhead_tail ℓ' rfl
            -- Hence ¬ (ℓ'.1 = ℓ.1 ∧ ℓ'.2 = !ℓ.2).
            by_contra hne
            apply hhd
            -- Show ℓ' = invLetter ℓ = (ℓ.1, !ℓ.2).
            show ℓ' = (ℓ.1, !ℓ.2)
            refine Prod.ext hfst.symm ?_
            -- Goal: ℓ'.2 = !ℓ.2. Use hne : ¬ ℓ.2 = ℓ'.2.
            -- From ¬ℓ.2 = ℓ'.2 and Bool, ℓ'.2 = !ℓ.2.
            rcases ha : ℓ.2 with _ | _ <;> rcases hb : ℓ'.2 with _ | _ <;>
              simp [ha, hb] at hne ⊢
        · -- First letter of (ℓ :: tail) is ℓ; need ℓ ≠ ℓfb.
          intro ℓ' hhd
          simp at hhd
          subst hhd
          exact hℓne
    · rintro ⟨hred, hlen, hhead⟩
      cases hw_case : w with
      | nil =>
        exact Finset.mem_union.mpr (Or.inl (by simp))
      | cons ℓ tail =>
        apply Finset.mem_union.mpr; apply Or.inr
        rw [Finset.mem_biUnion]
        refine ⟨ℓ, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          exact hhead ℓ (by subst hw_case; rfl)
        · rw [Finset.mem_image]
          refine ⟨tail, ?_, rfl⟩
          rw [ih]
          refine ⟨?_, ?_, ?_⟩
          · -- tail is reduced (tail of a reduced list)
            subst hw_case
            exact (_root_.FreeGroup.IsReduced.infix hred
              ⟨[ℓ], [], by simp⟩)
          · subst hw_case
            simp at hlen
            omega
          · -- Head of tail (if any) is not invLetter ℓ
            intro ℓh htl
            subst hw_case
            cases tail with
            | nil => simp at htl
            | cons ℓ'' rest =>
              have hheq : ℓ'' = ℓh := by simp at htl; exact htl
              rw [_root_.FreeGroup.isReduced_cons_cons] at hred
              obtain ⟨hcancel, _⟩ := hred
              -- hcancel : ℓ.1 = ℓ''.1 → ℓ.2 = ℓ''.2
              -- Need: ℓh ≠ invLetter ℓ = (ℓ.1, !ℓ.2)
              intro hinv
              -- hinv : ℓh = invLetter ℓ
              have hinv' : ℓh = (ℓ.1, !ℓ.2) := hinv
              have h1 : ℓh.1 = ℓ.1 := by rw [hinv']
              have h2 : ℓh.2 = !ℓ.2 := by rw [hinv']
              rw [hheq] at hcancel
              have := hcancel h1.symm
              rw [h2] at this
              cases ℓ.2 <;> simp at this

/-- Membership criterion for `redAll k`. -/
private lemma mem_redAll {k : ℕ} {w : List (Fin 2 × Bool)} :
    w ∈ redAll k ↔ _root_.FreeGroup.IsReduced w ∧ w.length ≤ k := by
  induction k generalizing w with
  | zero =>
    show w ∈ ({([] : List (Fin 2 × Bool))} : Finset _) ↔
      _root_.FreeGroup.IsReduced w ∧ w.length ≤ 0
    rw [Finset.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨_root_.FreeGroup.IsReduced.nil, le_refl _⟩
    · rintro ⟨_, hlen⟩
      exact List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
  | succ k _ =>
    simp only [redAll]
    constructor
    · intro hw
      rcases Finset.mem_union.mp hw with h | h
      · simp at h
        subst h
        exact ⟨_root_.FreeGroup.IsReduced.nil, by simp⟩
      · rw [Finset.mem_biUnion] at h
        obtain ⟨ℓ, _, hℓ⟩ := h
        rw [Finset.mem_image] at hℓ
        obtain ⟨tail, htail, heq⟩ := hℓ
        have htail' := mem_redAvoid.mp htail
        obtain ⟨hred_tail, hlen_tail, hhead_tail⟩ := htail'
        subst heq
        refine ⟨?_, by simp; omega⟩
        cases tail with
        | nil => exact _root_.FreeGroup.IsReduced.singleton
        | cons ℓ' rest =>
          rw [_root_.FreeGroup.isReduced_cons_cons]
          refine ⟨?_, hred_tail⟩
          intro hfst
          have hhd := hhead_tail ℓ' rfl
          by_contra hne
          apply hhd
          -- Goal: ℓ' = invLetter ℓ, i.e., ℓ' = (ℓ.1, !ℓ.2).
          show ℓ' = (ℓ.1, !ℓ.2)
          refine Prod.ext hfst.symm ?_
          -- Goal: ℓ'.2 = !ℓ.2
          rcases ha : ℓ.2 with _ | _ <;> rcases hb : ℓ'.2 with _ | _ <;>
            simp [ha, hb] at hne ⊢
    · rintro ⟨hred, hlen⟩
      cases hw_case : w with
      | nil => exact Finset.mem_union.mpr (Or.inl (by simp))
      | cons ℓ tail =>
        apply Finset.mem_union.mpr; apply Or.inr
        rw [Finset.mem_biUnion]
        refine ⟨ℓ, Finset.mem_univ _, ?_⟩
        rw [Finset.mem_image]
        refine ⟨tail, ?_, rfl⟩
        rw [mem_redAvoid]
        refine ⟨?_, ?_, ?_⟩
        · subst hw_case
          exact (_root_.FreeGroup.IsReduced.infix hred
            ⟨[ℓ], [], by simp⟩)
        · subst hw_case
          simp at hlen
          omega
        · intro ℓh htl
          subst hw_case
          cases tail with
          | nil => simp at htl
          | cons ℓ'' rest =>
            -- htl : (ℓ'' :: rest).head? = some ℓh simplifies to ℓ'' = ℓh.
            have hheq : ℓ'' = ℓh := by simp at htl; exact htl
            rw [_root_.FreeGroup.isReduced_cons_cons] at hred
            obtain ⟨hcancel, _⟩ := hred
            intro hinv
            -- hinv : ℓh = invLetter ℓ. Unfold invLetter.
            have hinv' : ℓh = (ℓ.1, !ℓ.2) := hinv
            have h1 : ℓh.1 = ℓ.1 := by rw [hinv']
            have h2 : ℓh.2 = !ℓ.2 := by rw [hinv']
            -- From hheq : ℓ'' = ℓh, propagate to hcancel.
            rw [hheq] at hcancel
            have := hcancel h1.symm
            rw [h2] at this
            cases ℓ.2 <;> simp at this

/-- Injectivity of the cons map `tail ↦ ℓ :: tail`. -/
private lemma cons_injective (ℓ : Fin 2 × Bool) :
    Function.Injective (fun tail : List (Fin 2 × Bool) => ℓ :: tail) := by
  intro a b h
  exact (List.cons.injEq _ _ _ _).mp h |>.2

/-- Cardinality of `redAvoid ℓfb k`: equals `redAvoidCount k`, independent of
the specific forbidden letter. -/
private lemma card_redAvoid (ℓfb : Fin 2 × Bool) (k : ℕ) :
    (redAvoid ℓfb k).card = redAvoidCount k := by
  induction k generalizing ℓfb with
  | zero => simp [redAvoid, redAvoidCount]
  | succ k ih =>
    -- redAvoid ℓfb (k+1) = {[]} ∪ extension
    show (({([] : List (Fin 2 × Bool))} : Finset _) ∪
      (((Finset.univ : Finset (Fin 2 × Bool)).filter (· ≠ ℓfb)).biUnion fun ℓ =>
        (redAvoid (invLetter ℓ) k).image (fun tail => ℓ :: tail))).card =
      redAvoidCount (k+1)
    -- Step 1: disjointness of base and extension.
    have hdisj :
        Disjoint (({([] : List (Fin 2 × Bool))} : Finset _))
          (((Finset.univ : Finset (Fin 2 × Bool)).filter (· ≠ ℓfb)).biUnion fun ℓ =>
            (redAvoid (invLetter ℓ) k).image (fun tail => ℓ :: tail)) := by
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      simp at hw1
      subst hw1
      rw [Finset.mem_biUnion] at hw2
      obtain ⟨ℓ, _, hmem⟩ := hw2
      rw [Finset.mem_image] at hmem
      obtain ⟨_, _, heq⟩ := hmem
      exact (List.cons_ne_nil ℓ _) heq
    rw [Finset.card_union_of_disjoint hdisj]
    simp only [Finset.card_singleton]
    -- Step 2: count the biUnion (disjoint pieces, each of card = redAvoidCount k).
    have hpairs : ∀ ℓ₁ ∈ ((Finset.univ : Finset (Fin 2 × Bool)).filter (· ≠ ℓfb)),
        ∀ ℓ₂ ∈ ((Finset.univ : Finset (Fin 2 × Bool)).filter (· ≠ ℓfb)),
        ℓ₁ ≠ ℓ₂ →
        Disjoint ((redAvoid (invLetter ℓ₁) k).image (fun tail => ℓ₁ :: tail))
          ((redAvoid (invLetter ℓ₂) k).image (fun tail => ℓ₂ :: tail)) := by
      intro ℓ₁ _ ℓ₂ _ hne
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      rw [Finset.mem_image] at hw1 hw2
      obtain ⟨_, _, h1⟩ := hw1
      obtain ⟨_, _, h2⟩ := hw2
      rw [← h1] at h2
      simp at h2
      exact hne.symm h2.1
    rw [Finset.card_biUnion hpairs]
    -- Each image has card redAvoidCount k.
    have hsum_eq : ∑ ℓ ∈ ((Finset.univ : Finset (Fin 2 × Bool)).filter (· ≠ ℓfb)),
        ((redAvoid (invLetter ℓ) k).image (fun tail => ℓ :: tail)).card =
        ∑ _ℓ ∈ ((Finset.univ : Finset (Fin 2 × Bool)).filter (· ≠ ℓfb)),
          redAvoidCount k := by
      apply Finset.sum_congr rfl
      intro ℓ _
      rw [Finset.card_image_of_injective _ (cons_injective ℓ)]
      exact ih (invLetter ℓ)
    rw [hsum_eq, Finset.sum_const, smul_eq_mul]
    -- Count the filter: `Finset.univ.filter (· ≠ ℓfb)` has 3 elements (among 4).
    have hfilt : ((Finset.univ : Finset (Fin 2 × Bool)).filter (· ≠ ℓfb)).card = 3 := by
      -- By removing ℓfb from the 4-element universe.
      have hsub : (Finset.univ : Finset (Fin 2 × Bool)).filter (· ≠ ℓfb) =
          (Finset.univ : Finset (Fin 2 × Bool)).erase ℓfb := by
        ext x; simp [Finset.mem_erase]
      rw [hsub, Finset.card_erase_of_mem (Finset.mem_univ _)]
      decide
    rw [hfilt]
    rfl

/-- Cardinality of `redAll k`: equals `redAllCount k = 2 * 3^k - 1`. -/
private lemma card_redAll (k : ℕ) : (redAll k).card = redAllCount k := by
  cases k with
  | zero => simp [redAll, redAllCount]
  | succ k =>
    show (({([] : List (Fin 2 × Bool))} : Finset _) ∪
      ((Finset.univ : Finset (Fin 2 × Bool)).biUnion fun ℓ =>
        (redAvoid (invLetter ℓ) k).image (fun tail => ℓ :: tail))).card =
      redAllCount (k+1)
    have hdisj :
        Disjoint (({([] : List (Fin 2 × Bool))} : Finset _))
          ((Finset.univ : Finset (Fin 2 × Bool)).biUnion fun ℓ =>
            (redAvoid (invLetter ℓ) k).image (fun tail => ℓ :: tail)) := by
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      simp at hw1
      subst hw1
      rw [Finset.mem_biUnion] at hw2
      obtain ⟨ℓ, _, hmem⟩ := hw2
      rw [Finset.mem_image] at hmem
      obtain ⟨_, _, heq⟩ := hmem
      exact (List.cons_ne_nil ℓ _) heq
    rw [Finset.card_union_of_disjoint hdisj]
    simp only [Finset.card_singleton]
    have hpairs : ∀ ℓ₁ ∈ (Finset.univ : Finset (Fin 2 × Bool)),
        ∀ ℓ₂ ∈ (Finset.univ : Finset (Fin 2 × Bool)), ℓ₁ ≠ ℓ₂ →
        Disjoint ((redAvoid (invLetter ℓ₁) k).image (fun tail => ℓ₁ :: tail))
          ((redAvoid (invLetter ℓ₂) k).image (fun tail => ℓ₂ :: tail)) := by
      intro ℓ₁ _ ℓ₂ _ hne
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      rw [Finset.mem_image] at hw1 hw2
      obtain ⟨_, _, h1⟩ := hw1
      obtain ⟨_, _, h2⟩ := hw2
      rw [← h1] at h2
      simp at h2
      exact hne.symm h2.1
    rw [Finset.card_biUnion hpairs]
    have hsum_eq : ∑ ℓ ∈ (Finset.univ : Finset (Fin 2 × Bool)),
        ((redAvoid (invLetter ℓ) k).image (fun tail => ℓ :: tail)).card =
        ∑ _ℓ ∈ (Finset.univ : Finset (Fin 2 × Bool)), redAvoidCount k := by
      apply Finset.sum_congr rfl
      intro ℓ _
      rw [Finset.card_image_of_injective _ (cons_injective ℓ)]
      exact card_redAvoid (invLetter ℓ) k
    rw [hsum_eq, Finset.sum_const, smul_eq_mul]
    have huniv : (Finset.univ : Finset (Fin 2 × Bool)).card = 4 := by decide
    rw [huniv]
    rfl

private lemma F2_card_toWord_length_le (k : ℕ) :
    Nat.card {x : F2 // x.toWord.length ≤ k} = 2 * 3 ^ k - 1 := by
  -- Build a bijection between {x : F2 // x.toWord.length ≤ k} and redAll k.
  -- Forward: x ↦ x.toWord. Well-defined by isReduced_toWord and the hypothesis.
  -- Backward: w ↦ mk w. Length preserved via toWord_mk + IsReduced.reduce_eq.
  -- Apply Nat.subtype_card with the Finset image of redAll under `mk`.
  classical
  have hmk_inj_on :
      Set.InjOn (_root_.FreeGroup.mk : List (Fin 2 × Bool) → F2) (redAll k) := by
    intro w1 hw1 w2 hw2 hmkeq
    have h1 := (mem_redAll.mp hw1).1
    have h2 := (mem_redAll.mp hw2).1
    have e1 : (_root_.FreeGroup.mk w1).toWord = w1 := by
      rw [_root_.FreeGroup.toWord_mk]; exact h1.reduce_eq
    have e2 : (_root_.FreeGroup.mk w2).toWord = w2 := by
      rw [_root_.FreeGroup.toWord_mk]; exact h2.reduce_eq
    rw [← e1, ← e2, hmkeq]
  set fset : Finset F2 := (redAll k).image _root_.FreeGroup.mk with hfset_def
  have hfset_card : fset.card = (redAll k).card :=
    Finset.card_image_of_injOn hmk_inj_on
  have hmem : ∀ x : F2, x ∈ fset ↔ x.toWord.length ≤ k := by
    intro x
    rw [hfset_def, Finset.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have h := mem_redAll.mp hw
      have hred := h.1
      have hlen := h.2
      have : (_root_.FreeGroup.mk w).toWord = w := by
        rw [_root_.FreeGroup.toWord_mk]; exact hred.reduce_eq
      rw [this]; exact hlen
    · intro hx
      refine ⟨x.toWord, ?_, _root_.FreeGroup.mk_toWord⟩
      rw [mem_redAll]
      exact ⟨_root_.FreeGroup.isReduced_toWord, hx⟩
  rw [Nat.subtype_card fset hmem, hfset_card, card_redAll, redAllCount_formula]

/-- **Q37.** Growth function of `F_2` with the canonical generating set:
`β(k) = 2 · 3^k − 1`.

**Proof.** Combine the two sub-lemmas:

* `F2_dist_eq_toWord_length`: the graph distance from `1` equals the reduced
  word length. Hence the ball of radius `k` centred at `1` is the set of
  `x : F_2` with `x.toWord.length ≤ k`.
* `F2_card_toWord_length_le`: the cardinality of that set is `2 · 3^k − 1`.

Both sub-lemmas are fully proven. -/
theorem F2_growth (k : ℕ) :
    EnsX2026.Cayley.growth F2_generating_set k = 2 * 3 ^ k - 1 := by
  -- Unfold `growth` and rewrite the ball via `F2_dist_eq_toWord_length`.
  unfold EnsX2026.Cayley.growth EnsX2026.Cayley.cayley_ball
  have hset :
      {x : F2 | (EnsX2026.Cayley.cayley_graph F2_generating_set).dist 1 x ≤ k}
        = {x : F2 | x.toWord.length ≤ k} := by
    ext x
    simp [F2_dist_eq_toWord_length]
  rw [hset]
  -- The set `{x | x.toWord.length ≤ k}` has the same cardinality as its
  -- subtype, which is exactly `F2_card_toWord_length_le k`.
  exact F2_card_toWord_length_le k

/-! ### Q38 — Surjectivity of the Laplacian on `F_2 → ℝ`

The Cayley graph of `F_2` with the four canonical generators is a locally
finite 4-regular tree, so its combinatorial Laplacian
`Δ : (F_2 → ℝ) → (F_2 → ℝ)` is well-defined pointwise.

**Surjectivity.** Given `g : F_2 → ℝ`, we build `f : F_2 → ℝ` solving
`Δ f = g` by tree recursion from the root `1`:

* Fix `f(1)` arbitrarily (e.g. `0`), and fix `f(z)` for each neighbour `z` of
  `1` except one, say the neighbour `z_⋆`; this gives 4 free parameters at
  depth ≤ 1 after satisfying the single equation `Δf(1) = g(1)`.
* For every vertex `x ≠ 1`, the equation `Δf(x) = g(x)` determines `f` at the
  unique neighbour of `x` which is further from `1`, i.e. the neighbour on
  the "outward" side. This defines `f` at every vertex by induction on
  distance.

The construction works in any locally finite tree of degree ≥ 2.
-/

/-- The Cayley graph of `F_2` is locally finite: each vertex has exactly 4
neighbours (one per generator, all distinct because generators are
non-involutory in `F_2`). -/
noncomputable instance F2_cayley_locallyFinite :
    LocallyFinite (EnsX2026.Cayley.cayley_graph F2_generating_set) := by
  intro x
  -- The neighbour set is contained in `{x · z | z ∈ F2_generating_set}`, a
  -- finite set (of size ≤ 4). We exhibit the neighbourhood as a subset of a
  -- finite set.
  classical
  apply Set.Finite.fintype
  have hfin : ({_root_.FreeGroup.of (0 : Fin 2), _root_.FreeGroup.of (1 : Fin 2),
                (_root_.FreeGroup.of (0 : Fin 2))⁻¹, (_root_.FreeGroup.of (1 : Fin 2))⁻¹} :
                Set F2).Finite := by
    apply Set.Finite.insert
    apply Set.Finite.insert
    apply Set.Finite.insert
    exact Set.finite_singleton _
  refine Set.Finite.subset (hfin.image (fun z => x * z)) ?_
  intro y hy
  -- `y ∈ neighborSet x` means `(cayley_graph Z).Adj x y`.
  rw [SimpleGraph.mem_neighborSet, EnsX2026.Cayley.cayley_graph_adj] at hy
  obtain ⟨_hne, hcase⟩ := hy
  rcases hcase with ⟨z, hz, hyz⟩ | ⟨z, hz, hxz⟩
  · exact ⟨z, hz, hyz.symm⟩
  · -- y ∈ {x * z⁻¹}: x = y * z, so y = x * z⁻¹
    refine ⟨z⁻¹, ?_, ?_⟩
    · exact F2_generating_set_symmetric z hz
    · -- y = x * z⁻¹ from x = y * z
      have : y = x * z⁻¹ := by rw [hxz]; group
      exact this.symm

/-- The Cayley graph of `F_2` has decidable adjacency (needed for
`laplacian_E`). -/
noncomputable instance F2_cayley_decidableAdj :
    DecidableRel (EnsX2026.Cayley.cayley_graph F2_generating_set).Adj := by
  intro x y; exact Classical.dec _

/-- The two generators `of 0` and `of 1` are distinct in `F_2`. -/
private lemma F2_of_zero_ne_of_one :
    (_root_.FreeGroup.of (0 : Fin 2) : F2) ≠ _root_.FreeGroup.of 1 := by
  intro h
  have := _root_.FreeGroup.of_injective h
  exact absurd this (by decide)

/-- `of 0 ≠ 1` in `F_2`. -/
private lemma F2_of_zero_ne_one : (_root_.FreeGroup.of (0 : Fin 2) : F2) ≠ 1 := by
  intro h
  have hw : (_root_.FreeGroup.of (0 : Fin 2) : F2).toWord = (1 : F2).toWord := by
    rw [h]
  simp [_root_.FreeGroup.toWord_of, _root_.FreeGroup.toWord_one] at hw

/-- `of 1 ≠ 1` in `F_2`. -/
private lemma F2_of_one_ne_one : (_root_.FreeGroup.of (1 : Fin 2) : F2) ≠ 1 := by
  intro h
  have hw : (_root_.FreeGroup.of (1 : Fin 2) : F2).toWord = (1 : F2).toWord := by
    rw [h]
  simp [_root_.FreeGroup.toWord_of, _root_.FreeGroup.toWord_one] at hw

/-- The Cayley graph of `F_2` has degree at least 2 at every vertex: the
neighbours include at least `x · a` and `x · b`, which are distinct. -/
lemma F2_cayley_degree_ge_two (x : F2) :
    2 ≤ (EnsX2026.Cayley.cayley_graph F2_generating_set).degree x := by
  classical
  set T := EnsX2026.Cayley.cayley_graph F2_generating_set
  have h_of0_mem : (_root_.FreeGroup.of (0 : Fin 2) : F2) ∈ F2_generating_set := by
    left; rfl
  have h_of1_mem : (_root_.FreeGroup.of (1 : Fin 2) : F2) ∈ F2_generating_set := by
    right; left; rfl
  have hadj0 : T.Adj x (x * _root_.FreeGroup.of (0 : Fin 2)) :=
    EnsX2026.Cayley.cayley_graph_adj_mul F2_generating_set h_of0_mem F2_of_zero_ne_one
  have hadj1 : T.Adj x (x * _root_.FreeGroup.of (1 : Fin 2)) :=
    EnsX2026.Cayley.cayley_graph_adj_mul F2_generating_set h_of1_mem F2_of_one_ne_one
  have h0_mem : x * _root_.FreeGroup.of (0 : Fin 2) ∈ T.neighborFinset x := by
    rw [mem_neighborFinset]; exact hadj0
  have h1_mem : x * _root_.FreeGroup.of (1 : Fin 2) ∈ T.neighborFinset x := by
    rw [mem_neighborFinset]; exact hadj1
  have hne : (x * _root_.FreeGroup.of (0 : Fin 2)) ≠
             (x * _root_.FreeGroup.of (1 : Fin 2)) := by
    intro heq
    exact F2_of_zero_ne_of_one (mul_left_cancel heq)
  have hsub : ({x * _root_.FreeGroup.of (0 : Fin 2),
                x * _root_.FreeGroup.of (1 : Fin 2)} : Finset F2)
      ⊆ T.neighborFinset x := by
    intro y hy
    rcases Finset.mem_insert.mp hy with h | h
    · rw [h]; exact h0_mem
    · rw [Finset.mem_singleton] at h; rw [h]; exact h1_mem
  have hcard :
      (({x * _root_.FreeGroup.of (0 : Fin 2),
         x * _root_.FreeGroup.of (1 : Fin 2)} : Finset F2).card) = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
  have := Finset.card_le_card hsub
  rw [hcard] at this
  rw [← card_neighborFinset_eq_degree]
  exact this

/-! #### General tree-Laplacian lift

The construction of a pre-image of the Laplacian on a locally finite tree is a
standard tree recursion from a chosen root. We isolate it here as a general
lemma, parameterised by the tree `T`, a root `v₀`, and a right-hand side `g`.
Its proof (well-founded recursion on `T.dist v₀ ·` with a designated
outward-neighbour selector) is modular and does not depend on anything specific
to `F_2`; we state it once and re-use it to close Q38.

Mathematical content (recalled from §7 of the paper):

* At the root `v₀`: `f(v₀) := 0`. The equation `Δf(v₀) = g(v₀)` reads
  `deg(v₀)·0 − Σ_{w ∈ N(v₀)} f(w) = g(v₀)`, so
  `Σ_{w ∈ N(v₀)} f(w) = − g(v₀)`. Choose all neighbours but one (pick one
  canonically via `Classical.choice`) to be `0`; the last one is `− g(v₀)`.
* At any other vertex `p` (with `f(p)` already defined at depth `n`), the
  equation `Δf(p) = g(p)` reads
  `deg(p)·f(p) − f(p⁻) − Σ_{x : children of p} f(x) = g(p)`
  where `p⁻` is the unique inward neighbour of `p`
  (`tree_neighbor_closer_unique` with roles swapped) and the "children" are
  the other `deg(p) − 1` outward neighbours. Choose all but one child to have
  `f` value `0`; the remaining child's `f` value is determined.

The Lean encoding uses well-founded recursion on `T.dist v₀ ·` with a
designated outward-neighbour selector, under the additional hypothesis
`h_noleaf : ∀ v, 2 ≤ T.degree v` which is satisfied by the 4-regular Cayley
graph of `F_2`. The leafless hypothesis is *necessary* for the statement:
for a finite tree, `∑_v (Δf)(v) = 0` always, so `∑_v g(v) = 0` would be
needed — which cannot be derived from the hypotheses above. Under
`h_noleaf`, every non-root `x` has at least one *outward* neighbour (strictly
farther from `v₀`), allowing a recursive construction where `f(x) = 0` for
all but a designated "sacrificial" outward child of each vertex, whose value
is forced by `Δf(p) = g(p)` at the parent `p`. Cf. Serre, *Arbres,
amalgames, $SL_2$*, Ch. I §3, for the classical proof. -/

section TreeLaplacianLift

variable {V : Type*} (T : SimpleGraph V) [LocallyFinite T] [DecidableRel T.Adj]

/-- The **outward neighbours** of `x` from root `v₀`: neighbours `w` of `x`
with `T.dist v₀ w = T.dist v₀ x + 1`. -/
noncomputable def outward (v₀ x : V) : Finset V :=
  (T.neighborFinset x).filter (fun w => T.dist v₀ w = T.dist v₀ x + 1)

lemma mem_outward {v₀ x w : V} :
    w ∈ outward T v₀ x ↔ T.Adj x w ∧ T.dist v₀ w = T.dist v₀ x + 1 := by
  simp [outward, mem_neighborFinset]

/-- In a tree, adjacent vertices have graph-distance (from any fixed root)
differing by exactly `1`. -/
lemma tree_dist_neighbour_pm_one (hT : T.IsTree) (v₀ v w : V) (hvw : T.Adj v w) :
    T.dist v₀ w = T.dist v₀ v + 1 ∨ T.dist v₀ w + 1 = T.dist v₀ v := by
  classical
  -- By Adj.diff_dist_adj, dist v₀ w ∈ {dist v₀ v, dist v₀ v + 1, dist v₀ v - 1}.
  rcases hvw.diff_dist_adj (u := v₀) with h0 | h1 | hm1
  · -- Equal distances: contradiction via tree uniqueness of paths.
    exfalso
    -- Geodesic paths v₀ → v and v₀ → w of length dist v₀ v.
    obtain ⟨p, hp_path, hp_len⟩ := (hT.connected v₀ v).exists_path_of_dist
    obtain ⟨q, hq_path, hq_len⟩ := (hT.connected v₀ w).exists_path_of_dist
    -- w ∉ p.support: else a sub-walk v₀ → w has length < dist v₀ w.
    have hw_notin : w ∉ p.support := by
      intro hw
      obtain ⟨r, s, hr, _, heq⟩ := hp_path.mem_support_iff_exists_append.mp hw
      have hrs : r.length + s.length = T.dist v₀ v := by
        have hsum : (r.append s).length = T.dist v₀ v := heq ▸ hp_len
        rw [SimpleGraph.Walk.length_append] at hsum
        exact hsum
      have hr_ge : T.dist v₀ w ≤ r.length := SimpleGraph.dist_le r
      -- From h0 : dist v₀ w = dist v₀ v, get r.length = dist v₀ v and s.length = 0.
      have hrE : r.length = T.dist v₀ v := by omega
      have hsE : s.length = 0 := by omega
      -- s is nil, so its endpoints are equal: w = v.
      have hs_nil : s.Nil := SimpleGraph.Walk.nil_iff_length_eq.mpr hsE
      have hwv : w = v := hs_nil.eq
      -- Now Adj v w with w = v: contradicts loopless.
      exact T.irrefl (hwv ▸ hvw)
    -- p.concat hvw : Walk v₀ w, and it is a path of length dist v₀ v + 1.
    have hpath_ext : (p.concat hvw).IsPath := hp_path.concat hw_notin hvw
    have hpath_ext_len : (p.concat hvw).length = T.dist v₀ v + 1 := by
      rw [SimpleGraph.Walk.length_concat, hp_len]
    -- Use uniqueness of simple paths in the tree.
    obtain ⟨q', _hq'_path, hq'_uniq⟩ := hT.existsUnique_path v₀ w
    have h_eq1 : q = q' := hq'_uniq q hq_path
    have h_eq2 : p.concat hvw = q' := hq'_uniq _ hpath_ext
    have hlen_eq : q.length = (p.concat hvw).length := by
      rw [h_eq1, ← h_eq2]
    rw [hq_len, hpath_ext_len, h0] at hlen_eq
    omega
  · left; exact h1
  · -- hm1 : T.dist v₀ w = T.dist v₀ v - 1. We need dist v₀ v ≥ 1.
    right
    -- Triangle: dist v₀ v ≤ dist v₀ w + dist w v = dist v₀ w + 1.
    have hwv : T.dist w v = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hvw.symm
    have htri : T.dist v₀ v ≤ T.dist v₀ w + T.dist w v :=
      hvw.symm.reachable.dist_triangle_right v₀
    -- Also need dist v₀ v ≥ 1: else v₀ = v, so dist v₀ w = dist v w = 1, but hm1 = 0.
    have hvv_pos : 1 ≤ T.dist v₀ v := by
      by_contra hle
      push_neg at hle
      have hdv0 : T.dist v₀ v = 0 := by omega
      have hreach : T.Reachable v₀ v := (hT.connected v₀ v)
      have h_eq : v₀ = v := by
        rcases (SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable
          (G := T) (u := v₀) (v := v)).mp hdv0 with heq | hnr
        · exact heq
        · exact absurd hreach hnr
      -- With v₀ = v, we have dist v₀ w = dist v w = 1, but hm1 says dist v₀ w = 0 - 1 = 0.
      have hvw_one' : T.dist v₀ w = 1 := by
        rw [h_eq]; exact SimpleGraph.dist_eq_one_iff_adj.mpr hvw
      rw [hdv0] at hm1
      rw [hvw_one'] at hm1
      omega
    omega

/-- Under the no-leaf hypothesis `∀ v, 2 ≤ T.degree v`, every vertex in a
tree has at least one *outward* neighbour (strictly farther from the root). -/
lemma outward_nonempty (hT : T.IsTree) (h_noleaf : ∀ v, 2 ≤ T.degree v)
    (v₀ x : V) : (outward T v₀ x).Nonempty := by
  classical
  -- Case 1: x = v₀. Then every neighbour is outward (dist v₀ · = 1 = 0+1).
  by_cases hxv0 : x = v₀
  · -- Don't subst; rewrite via hxv0 instead.
    have hdeg : 2 ≤ T.degree x := h_noleaf x
    have hne : (T.neighborFinset x).Nonempty := by
      rw [← card_neighborFinset_eq_degree] at hdeg
      exact Finset.card_pos.mp (by omega)
    obtain ⟨w, hw⟩ := hne
    rw [mem_neighborFinset] at hw
    refine ⟨w, ?_⟩
    rw [mem_outward]
    refine ⟨hw, ?_⟩
    -- dist v₀ w = 1 (since x = v₀ and Adj x w).
    have hxw : T.Adj v₀ w := hxv0 ▸ hw
    have h1 : T.dist v₀ w = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hxw
    have h0 : T.dist v₀ x = 0 := by
      rw [hxv0]; exact SimpleGraph.dist_self
    rw [h1, h0]
  · -- Case 2: x ≠ v₀. There is a *unique* closer neighbour z.
    obtain ⟨z, ⟨hzadj, hzdist⟩, hzuniq⟩ :=
      tree_neighbor_closer_unique hT v₀ x (Ne.symm hxv0) _ rfl
    have hdeg : 2 ≤ T.degree x := h_noleaf x
    have hcard : 2 ≤ (T.neighborFinset x).card := by
      rw [card_neighborFinset_eq_degree]; exact hdeg
    have hz_mem : z ∈ T.neighborFinset x := by
      rw [mem_neighborFinset]; exact hzadj
    have hcard_erase : 1 ≤ ((T.neighborFinset x).erase z).card := by
      rw [Finset.card_erase_of_mem hz_mem]; omega
    have hne_erase : ((T.neighborFinset x).erase z).Nonempty :=
      Finset.card_pos.mp (by omega)
    obtain ⟨w, hw_erase⟩ := hne_erase
    rw [Finset.mem_erase, mem_neighborFinset] at hw_erase
    obtain ⟨hwne, hwadj⟩ := hw_erase
    refine ⟨w, ?_⟩
    rw [mem_outward]
    refine ⟨hwadj, ?_⟩
    rcases tree_dist_neighbour_pm_one T hT v₀ x w hwadj with h_out | h_in
    · exact h_out
    · -- h_in: T.dist v₀ w + 1 = T.dist v₀ x; so w is a closer neighbour.
      -- By uniqueness, w = z, contradicting hwne.
      exfalso
      apply hwne
      -- Need T.dist v₀ w = T.dist v₀ x - 1.
      have hx_pos : 1 ≤ T.dist v₀ x := by
        have : 0 < T.dist v₀ x := (hT.connected v₀ x).pos_dist_of_ne (Ne.symm hxv0)
        omega
      have hwd : T.dist v₀ w = T.dist v₀ x - 1 := by omega
      exact hzuniq w ⟨hwadj, hwd⟩

/-- The **parent pointer** `p : V → V` in a tree, from a fixed root `v₀`.
For `x ≠ v₀`, `p x` is the unique neighbour of `x` closer to `v₀`; for `v₀`
itself we use the junk default `p v₀ := v₀`. -/
noncomputable def parent (hT : T.IsTree) (v₀ : V) (x : V) : V := by
  classical
  exact if hx : x = v₀ then v₀
  else Classical.choose
    (tree_neighbor_closer_unique hT v₀ x (Ne.symm hx) _ rfl).exists

lemma parent_spec (hT : T.IsTree) (v₀ x : V) (hx : x ≠ v₀) :
    T.Adj x (parent T hT v₀ x) ∧
    T.dist v₀ (parent T hT v₀ x) = T.dist v₀ x - 1 := by
  classical
  simp only [parent, dif_neg hx]
  exact Classical.choose_spec
    (tree_neighbor_closer_unique hT v₀ x (Ne.symm hx) _ rfl).exists

lemma parent_root (hT : T.IsTree) (v₀ : V) :
    parent T hT v₀ v₀ = v₀ := by
  classical
  simp [parent]

/-- The **sacrificial child** `c x`: a chosen outward neighbour of `x` (exists
under `h_noleaf`). -/
noncomputable def sacrificial (hT : T.IsTree) (h_noleaf : ∀ v, 2 ≤ T.degree v)
    (v₀ : V) (x : V) : V :=
  (outward_nonempty T hT h_noleaf v₀ x).choose

lemma sacrificial_spec (hT : T.IsTree) (h_noleaf : ∀ v, 2 ≤ T.degree v)
    (v₀ x : V) :
    sacrificial T hT h_noleaf v₀ x ∈ outward T v₀ x :=
  (outward_nonempty T hT h_noleaf v₀ x).choose_spec

lemma sacrificial_adj (hT : T.IsTree) (h_noleaf : ∀ v, 2 ≤ T.degree v)
    (v₀ x : V) : T.Adj x (sacrificial T hT h_noleaf v₀ x) := by
  have := sacrificial_spec T hT h_noleaf v₀ x
  rw [mem_outward] at this
  exact this.1

lemma sacrificial_dist (hT : T.IsTree) (h_noleaf : ∀ v, 2 ≤ T.degree v)
    (v₀ x : V) :
    T.dist v₀ (sacrificial T hT h_noleaf v₀ x) = T.dist v₀ x + 1 := by
  have := sacrificial_spec T hT h_noleaf v₀ x
  rw [mem_outward] at this
  exact this.2

/-! #### The level-by-level function `F`

We define `FLevel : ℕ → V → ℝ` by plain `Nat.rec`, then set
`fLift x := FLevel (T.dist v₀ x) x`. At level `0`, `FLevel` is identically
zero. At level `n+1`, for a vertex `x` at distance `n+1`, we compute the
forced value determined by the Laplacian equation at `parent x`; all other
values are preserved from level `n`.
-/

open Classical in
/-- **The forced value** at vertex `x` at level `n+1`, assuming `x` is the
sacrificial child of its parent `p = parent x`. This is the value dictated by
the Laplacian equation `(Δf)(p) = g(p)` once the values at `p` (depth `n`) and
`parent p` (depth `n-1`) are known. -/
noncomputable def forcedValue (hT : T.IsTree) (v₀ : V) (g : V → ℝ)
    (Fn : V → ℝ) (x : V) : ℝ :=
  let p := parent T hT v₀ x
  (T.degree p : ℝ) * Fn p
    - (if p = v₀ then 0 else Fn (parent T hT v₀ p))
    - g p

open Classical in
/-- **Level-by-level function** `FLevel : ℕ → V → ℝ`. -/
noncomputable def FLevel (hT : T.IsTree) (h_noleaf : ∀ v, 2 ≤ T.degree v)
    (v₀ : V) (g : V → ℝ) : ℕ → V → ℝ
  | 0, _ => 0
  | n + 1, x =>
      if T.dist v₀ x = n + 1 then
        if x = sacrificial T hT h_noleaf v₀ (parent T hT v₀ x) then
          forcedValue T hT v₀ g (FLevel hT h_noleaf v₀ g n) x
        else 0
      else FLevel hT h_noleaf v₀ g n x

/-- **Stabilization.** If `x` is at distance `≤ n` from the root, its value is
unchanged at level `n+1`. -/
lemma FLevel_stable (hT : T.IsTree) (h_noleaf : ∀ v, 2 ≤ T.degree v)
    (v₀ : V) (g : V → ℝ) (n : ℕ) (x : V) (h : T.dist v₀ x ≤ n) :
    FLevel T hT h_noleaf v₀ g (n + 1) x = FLevel T hT h_noleaf v₀ g n x := by
  classical
  have hne : T.dist v₀ x ≠ n + 1 := by omega
  show (if T.dist v₀ x = n + 1 then _ else FLevel T hT h_noleaf v₀ g n x)
      = FLevel T hT h_noleaf v₀ g n x
  rw [if_neg hne]

/-- **Zero at distance `> n`.** For vertices too far from the root, `F n x = 0`. -/
lemma FLevel_zero_of_dist_gt (hT : T.IsTree) (h_noleaf : ∀ v, 2 ≤ T.degree v)
    (v₀ : V) (g : V → ℝ) (n : ℕ) (x : V) (h : n < T.dist v₀ x) :
    FLevel T hT h_noleaf v₀ g n x = 0 := by
  classical
  induction n with
  | zero => rfl
  | succ n ih =>
      have hne : T.dist v₀ x ≠ n + 1 := by omega
      show (if T.dist v₀ x = n + 1 then _ else FLevel T hT h_noleaf v₀ g n x) = 0
      rw [if_neg hne]
      exact ih (by omega)

open Classical in
/-- **Value at the exact level `n+1`.** For `x` at distance `n+1`, the value is
either the forced value (if `x` is sacrificial child of `parent x`) or `0`. -/
lemma FLevel_at_succ_level (hT : T.IsTree) (h_noleaf : ∀ v, 2 ≤ T.degree v)
    (v₀ : V) (g : V → ℝ) (n : ℕ) (x : V) (h : T.dist v₀ x = n + 1) :
    FLevel T hT h_noleaf v₀ g (n + 1) x =
      if x = sacrificial T hT h_noleaf v₀ (parent T hT v₀ x) then
        forcedValue T hT v₀ g (FLevel T hT h_noleaf v₀ g n) x
      else 0 := by
  show (if T.dist v₀ x = n + 1 then
          (if x = sacrificial T hT h_noleaf v₀ (parent T hT v₀ x) then _ else 0)
        else _) = _
  rw [if_pos h]

/-- **Value at level `0`.** `FLevel 0` is identically zero. -/
lemma FLevel_zero (hT : T.IsTree) (h_noleaf : ∀ v, 2 ≤ T.degree v)
    (v₀ : V) (g : V → ℝ) (x : V) : FLevel T hT h_noleaf v₀ g 0 x = 0 := rfl

/-- **Iterated stabilization.** For any `m ≥ n ≥ T.dist v₀ x`,
`FLevel m x = FLevel n x`. -/
lemma FLevel_stable_ge (hT : T.IsTree) (h_noleaf : ∀ v, 2 ≤ T.degree v)
    (v₀ : V) (g : V → ℝ) (n : ℕ) (x : V) (h : T.dist v₀ x ≤ n) :
    ∀ m, n ≤ m → FLevel T hT h_noleaf v₀ g m x = FLevel T hT h_noleaf v₀ g n x := by
  intro m hnm
  induction m with
  | zero =>
      interval_cases n
      rfl
  | succ m ih =>
      rcases Nat.lt_or_ge n (m + 1) with hlt | hge
      · have hnm' : n ≤ m := by omega
        have hx_le_m : T.dist v₀ x ≤ m := le_trans h hnm'
        rw [FLevel_stable T hT h_noleaf v₀ g m x hx_le_m, ih hnm']
      · have : n = m + 1 := by omega
        rw [this]

/-- **The final function.** `fLift x := FLevel (T.dist v₀ x) x` — evaluated at
the "right" level where the value has stabilized. -/
noncomputable def fLift (hT : T.IsTree) (h_noleaf : ∀ v, 2 ≤ T.degree v)
    (v₀ : V) (g : V → ℝ) (x : V) : ℝ :=
  FLevel T hT h_noleaf v₀ g (T.dist v₀ x) x

/-- **Convenient rewrite.** For any `n ≥ T.dist v₀ x`, `fLift x = FLevel n x`. -/
lemma fLift_eq (hT : T.IsTree) (h_noleaf : ∀ v, 2 ≤ T.degree v)
    (v₀ : V) (g : V → ℝ) (x : V) (n : ℕ) (h : T.dist v₀ x ≤ n) :
    fLift T hT h_noleaf v₀ g x = FLevel T hT h_noleaf v₀ g n x := by
  unfold fLift
  exact (FLevel_stable_ge T hT h_noleaf v₀ g _ x le_rfl n h).symm

/-- **`fLift` at the root.** `fLift v₀ = 0` by construction. -/
lemma fLift_v₀ (hT : T.IsTree) (h_noleaf : ∀ v, 2 ≤ T.degree v)
    (v₀ : V) (g : V → ℝ) :
    fLift T hT h_noleaf v₀ g v₀ = 0 := by
  unfold fLift
  rw [SimpleGraph.dist_self]
  rfl

/-- **Parent of a sacrificial child is the vertex itself.** Key identity tying
`parent` and `sacrificial` together via `tree_neighbor_closer_unique`. -/
lemma parent_sacrificial (hT : T.IsTree) (h_noleaf : ∀ v, 2 ≤ T.degree v)
    (v₀ y : V) :
    parent T hT v₀ (sacrificial T hT h_noleaf v₀ y) = y := by
  classical
  set x := sacrificial T hT h_noleaf v₀ y with hx_def
  -- x is outward from y: adjacency and distance.
  have hxy_adj : T.Adj y x := sacrificial_adj T hT h_noleaf v₀ y
  have hx_dist : T.dist v₀ x = T.dist v₀ y + 1 := sacrificial_dist T hT h_noleaf v₀ y
  -- x ≠ v₀ since T.dist v₀ x ≥ 1.
  have hx_ne : x ≠ v₀ := by
    intro hxv0
    have h0 : T.dist v₀ x = 0 := by rw [hxv0]; exact SimpleGraph.dist_self
    omega
  -- The parent spec: parent x is adjacent to x and at distance T.dist v₀ x - 1.
  obtain ⟨hp_adj, hp_dist⟩ := parent_spec T hT v₀ x hx_ne
  -- Uniqueness of closer neighbour.
  obtain ⟨w, _hw_spec, hu⟩ :=
    tree_neighbor_closer_unique hT v₀ x (Ne.symm hx_ne) _ rfl
  -- Candidate 1: parent x.
  have h1 : T.Adj x (parent T hT v₀ x) ∧ T.dist v₀ (parent T hT v₀ x) = T.dist v₀ x - 1 :=
    ⟨hp_adj, hp_dist⟩
  -- Candidate 2: y.
  have h2 : T.Adj x y ∧ T.dist v₀ y = T.dist v₀ x - 1 := by
    refine ⟨hxy_adj.symm, ?_⟩
    rw [hx_dist]; omega
  -- Both equal the canonical witness w.
  have hpx : parent T hT v₀ x = w := hu (parent T hT v₀ x) h1
  have hy : y = w := hu y h2
  rw [hpx, ← hy]

/-- **Non-sacrificial branch: `fLift = 0`.** For `x ≠ v₀` which is not the
sacrificial child of its parent, `fLift x = 0`. -/
lemma fLift_nonsacrificial (hT : T.IsTree) (h_noleaf : ∀ v, 2 ≤ T.degree v)
    (v₀ : V) (g : V → ℝ) (x : V) (hx_ne : x ≠ v₀)
    (h_nonsac : x ≠ sacrificial T hT h_noleaf v₀ (parent T hT v₀ x)) :
    fLift T hT h_noleaf v₀ g x = 0 := by
  classical
  unfold fLift
  -- T.dist v₀ x ≥ 1, so write as m + 1.
  have hpos : 1 ≤ T.dist v₀ x :=
    (hT.connected v₀ x).pos_dist_of_ne (Ne.symm hx_ne)
  set n := T.dist v₀ x with hn_def
  have hn_succ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨m, hm⟩ := hn_succ
  rw [hm]
  rw [FLevel_at_succ_level T hT h_noleaf v₀ g m x (hn_def ▸ hm)]
  rw [if_neg h_nonsac]

open Classical in
/-- **Sacrificial branch: the forced value.** For any `y : V`, `fLift` at the
sacrificial child of `y` is the value forced by the Laplacian equation at `y`. -/
lemma fLift_sacrificial (hT : T.IsTree) (h_noleaf : ∀ v, 2 ≤ T.degree v)
    (v₀ : V) (g : V → ℝ) (y : V) :
    fLift T hT h_noleaf v₀ g (sacrificial T hT h_noleaf v₀ y) =
      (T.degree y : ℝ) * fLift T hT h_noleaf v₀ g y
        - (if y = v₀ then (0 : ℝ) else fLift T hT h_noleaf v₀ g (parent T hT v₀ y))
        - g y := by
  classical
  set x := sacrificial T hT h_noleaf v₀ y with hx_def
  -- Distance.
  have hx_dist : T.dist v₀ x = T.dist v₀ y + 1 :=
    sacrificial_dist T hT h_noleaf v₀ y
  -- Parent of x is y.
  have hpxy : parent T hT v₀ x = y := parent_sacrificial T hT h_noleaf v₀ y
  -- Sacrificial child of parent x = sacrificial y = x.
  have hs : sacrificial T hT h_noleaf v₀ (parent T hT v₀ x) = x := by
    rw [hpxy]
  -- Unfold fLift x.
  unfold fLift
  rw [hx_dist]
  rw [FLevel_at_succ_level T hT h_noleaf v₀ g (T.dist v₀ y) x hx_dist]
  rw [if_pos hs.symm]
  -- Now the LHS is forcedValue T hT v₀ g (FLevel T hT h_noleaf v₀ g (T.dist v₀ y)) x.
  unfold forcedValue
  -- Rewrite parent x = y everywhere on LHS.
  rw [hpxy]
  -- FLevel at (T.dist v₀ y) at y is fLift y.
  show (T.degree y : ℝ) * FLevel T hT h_noleaf v₀ g (T.dist v₀ y) y
        - (if y = v₀ then (0 : ℝ) else FLevel T hT h_noleaf v₀ g (T.dist v₀ y) (parent T hT v₀ y))
        - g y = _
  have hFy : FLevel T hT h_noleaf v₀ g (T.dist v₀ y) y
      = fLift T hT h_noleaf v₀ g y := rfl
  rw [hFy]
  -- Case split: y = v₀ or not.
  by_cases hy : y = v₀
  · rw [if_pos hy, if_pos hy]
  · rw [if_neg hy, if_neg hy]
    -- Parent y: need FLevel (T.dist v₀ y) (parent y) = fLift (parent y).
    have hpy_dist : T.dist v₀ (parent T hT v₀ y) = T.dist v₀ y - 1 :=
      (parent_spec T hT v₀ y hy).2
    have hpy_le : T.dist v₀ (parent T hT v₀ y) ≤ T.dist v₀ y := by
      rw [hpy_dist]; omega
    -- Both sides are equal by `fLift_eq` and the definitional unfolding of `fLift`.
    have hFp : FLevel T hT h_noleaf v₀ g (T.dist v₀ y) (parent T hT v₀ y)
        = fLift T hT h_noleaf v₀ g (parent T hT v₀ y) :=
      (fLift_eq T hT h_noleaf v₀ g (parent T hT v₀ y) (T.dist v₀ y) hpy_le).symm
    rw [hFp]
    show (T.degree y : ℝ) * fLift T hT h_noleaf v₀ g y
          - fLift T hT h_noleaf v₀ g (parent T hT v₀ y) - g y = _
    rfl

/-! #### Structure of the neighbour finset relative to `v₀` -/

/-- For `v ≠ v₀`, `parent v` lies in `T.neighborFinset v`. -/
lemma parent_mem_neighborFinset (hT : T.IsTree) (v₀ v : V) (hv : v ≠ v₀) :
    parent T hT v₀ v ∈ T.neighborFinset v := by
  rw [mem_neighborFinset]; exact (parent_spec T hT v₀ v hv).1

/-- For `v ≠ v₀`, `parent v` is *not* an outward neighbour of `v`. -/
lemma parent_not_mem_outward (hT : T.IsTree) (v₀ v : V) (hv : v ≠ v₀) :
    parent T hT v₀ v ∉ outward T v₀ v := by
  intro h
  rw [mem_outward] at h
  have hpd : T.dist v₀ (parent T hT v₀ v) = T.dist v₀ v - 1 :=
    (parent_spec T hT v₀ v hv).2
  have hvpos : 1 ≤ T.dist v₀ v :=
    (hT.connected v₀ v).pos_dist_of_ne (Ne.symm hv)
  omega

open Classical in
/-- **Decomposition of the neighbour finset (non-root case).** For `v ≠ v₀`,
the neighbour finset of `v` decomposes as `outward v ∪ {parent v}`, where the
two pieces are disjoint. -/
lemma neighborFinset_eq_outward_insert_parent (hT : T.IsTree) (v₀ v : V)
    (hv : v ≠ v₀) :
    T.neighborFinset v = insert (parent T hT v₀ v) (outward T v₀ v) := by
  classical
  ext w
  simp only [Finset.mem_insert, mem_outward, mem_neighborFinset]
  constructor
  · intro hw
    -- w adjacent to v ⇒ dist v₀ w = dist v₀ v ± 1.
    rcases tree_dist_neighbour_pm_one T hT v₀ v w hw with h_out | h_in
    · exact Or.inr ⟨hw, h_out⟩
    · -- h_in: dist v₀ w + 1 = dist v₀ v, so w is a closer neighbour.
      left
      have hvpos : 1 ≤ T.dist v₀ v :=
        (hT.connected v₀ v).pos_dist_of_ne (Ne.symm hv)
      have hwd : T.dist v₀ w = T.dist v₀ v - 1 := by omega
      obtain ⟨z, _hz_spec, hzuniq⟩ :=
        tree_neighbor_closer_unique hT v₀ v (Ne.symm hv) _ rfl
      have h1 : parent T hT v₀ v = z :=
        hzuniq (parent T hT v₀ v)
          ⟨(parent_spec T hT v₀ v hv).1, (parent_spec T hT v₀ v hv).2⟩
      have h2 : w = z := hzuniq w ⟨hw, hwd⟩
      rw [h1, h2]
  · rintro (rfl | ⟨hw, _⟩)
    · exact (parent_spec T hT v₀ v hv).1
    · exact hw

/-- **Decomposition of the neighbour finset (root case).** At `v₀`, every
neighbour is outward. -/
lemma neighborFinset_v₀_eq_outward (hT : T.IsTree) (v₀ : V) :
    T.neighborFinset v₀ = outward T v₀ v₀ := by
  classical
  ext w
  simp only [mem_outward, mem_neighborFinset]
  constructor
  · intro hw
    refine ⟨hw, ?_⟩
    have hwne : w ≠ v₀ := fun heq => T.irrefl (heq ▸ hw)
    have hd0 : T.dist v₀ v₀ = 0 := SimpleGraph.dist_self
    have h1 : T.dist v₀ w = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hw
    omega
  · rintro ⟨hw, _⟩; exact hw

open Classical in
/-- **Decomposition of `outward`.** `outward v = insert (sacrificial v)
(outward v \ {sacrificial v})`. -/
lemma outward_eq_insert_sacrificial (hT : T.IsTree)
    (h_noleaf : ∀ v, 2 ≤ T.degree v) (v₀ v : V) :
    outward T v₀ v =
      insert (sacrificial T hT h_noleaf v₀ v)
        ((outward T v₀ v).erase (sacrificial T hT h_noleaf v₀ v)) := by
  classical
  rw [Finset.insert_erase (sacrificial_spec T hT h_noleaf v₀ v)]

/-! #### The Laplacian verification -/

open Classical EnsX2026.Graphs in
/-- **Main theorem.** `fLift` satisfies the Laplacian equation: for every
vertex `v`, `Δ(fLift)(v) = g(v)`. -/
theorem fLift_laplacian_eq_g (hT : T.IsTree) (h_noleaf : ∀ v, 2 ≤ T.degree v)
    (v₀ : V) (g : V → ℝ) (v : V) :
    laplacian_E T (fLift T hT h_noleaf v₀ g) v = g v := by
  classical
  -- Shorthand.
  set f := fLift T hT h_noleaf v₀ g with hf_def
  set s := sacrificial T hT h_noleaf v₀ v with hs_def
  -- The sacrificial child of v is a neighbour of v (not in outward-erase, since
  -- we remove it).
  have hs_mem_out : s ∈ outward T v₀ v := sacrificial_spec T hT h_noleaf v₀ v
  have hs_adj : T.Adj v s := sacrificial_adj T hT h_noleaf v₀ v
  have hs_dist : T.dist v₀ s = T.dist v₀ v + 1 := sacrificial_dist T hT h_noleaf v₀ v
  have hs_ne_v₀ : s ≠ v₀ := by
    intro heq
    have : T.dist v₀ s = 0 := by rw [heq]; exact SimpleGraph.dist_self
    omega
  -- sacrificial is the sacrificial child of its parent (= v).
  have hps : parent T hT v₀ s = v := parent_sacrificial T hT h_noleaf v₀ v
  -- fLift at sacrificial = forcedValue.
  have hf_s : f s =
      (T.degree v : ℝ) * f v
        - (if v = v₀ then (0 : ℝ) else f (parent T hT v₀ v))
        - g v := by
    rw [hf_def]; exact fLift_sacrificial T hT h_noleaf v₀ g v
  -- Case split on v = v₀.
  by_cases hvv₀ : v = v₀
  · -- Root case. neighborFinset v = outward v.
    -- f v = 0.
    have hf_v : f v = 0 := by
      rw [hf_def, hvv₀]; exact fLift_v₀ T hT h_noleaf v₀ g
    -- Reduce sum over neighborFinset to sum over outward.
    have hNv : T.neighborFinset v = outward T v₀ v := by
      rw [hvv₀]; exact neighborFinset_v₀_eq_outward T hT v₀
    -- Split outward into {s} ∪ (outward \ {s}).
    have hsum :
        ∑ w ∈ T.neighborFinset v, f w
          = f s + ∑ w ∈ (outward T v₀ v).erase s, f w := by
      rw [hNv]
      conv_lhs => rw [outward_eq_insert_sacrificial T hT h_noleaf v₀ v]
      rw [Finset.sum_insert (Finset.notMem_erase _ _)]
    -- Every w ∈ outward \ {s} is non-sacrificial, so f w = 0.
    have herase_zero : ∀ w ∈ (outward T v₀ v).erase s, f w = 0 := by
      intro w hw
      rw [Finset.mem_erase] at hw
      obtain ⟨hw_ne_s, hw_out⟩ := hw
      rw [mem_outward] at hw_out
      obtain ⟨hw_adj, hw_dist⟩ := hw_out
      have hw_ne_v₀ : w ≠ v₀ := by
        intro heq
        have : T.dist v₀ w = 0 := by rw [heq]; exact SimpleGraph.dist_self
        omega
      -- parent w = v (since v is a closer neighbour of w).
      have hdv : T.dist v₀ v = 0 := by rw [hvv₀]; exact SimpleGraph.dist_self
      have hdw1 : T.dist v₀ w = 1 := by rw [hw_dist, hdv]
      have hpw : parent T hT v₀ w = v := by
        obtain ⟨z, _hz_spec, hzuniq⟩ :=
          tree_neighbor_closer_unique hT v₀ w (Ne.symm hw_ne_v₀) _ rfl
        have h1 : parent T hT v₀ w = z :=
          hzuniq (parent T hT v₀ w)
            ⟨(parent_spec T hT v₀ w hw_ne_v₀).1, (parent_spec T hT v₀ w hw_ne_v₀).2⟩
        have hvd : T.dist v₀ v = T.dist v₀ w - 1 := by rw [hdw1, hdv]
        have h2 : v = z := hzuniq v ⟨hw_adj.symm, hvd⟩
        rw [h1, ← h2]
      -- Now w ≠ sacrificial (parent w) = sacrificial v = s.
      have hw_ne_sac : w ≠ sacrificial T hT h_noleaf v₀ (parent T hT v₀ w) := by
        rw [hpw]; exact hw_ne_s
      rw [hf_def]
      exact fLift_nonsacrificial T hT h_noleaf v₀ g w hw_ne_v₀ hw_ne_sac
    have hsum_erase_zero : ∑ w ∈ (outward T v₀ v).erase s, f w = 0 :=
      Finset.sum_eq_zero herase_zero
    -- Compute f s at the root case.
    have hf_s_root : f s = -g v := by
      rw [hf_s, if_pos hvv₀, hf_v]; ring
    -- Assemble the Laplacian.
    show (T.degree v : ℝ) * f v - ∑ w ∈ T.neighborFinset v, f w = g v
    rw [hf_v, hsum, hf_s_root, hsum_erase_zero]
    ring
  · -- Non-root case. neighborFinset v = insert (parent v) (outward v).
    have hNv : T.neighborFinset v = insert (parent T hT v₀ v) (outward T v₀ v) :=
      neighborFinset_eq_outward_insert_parent T hT v₀ v hvv₀
    have hp_not_out : parent T hT v₀ v ∉ outward T v₀ v :=
      parent_not_mem_outward T hT v₀ v hvv₀
    -- Split: sum over neighborFinset = f (parent v) + sum over outward.
    have hsum1 :
        ∑ w ∈ T.neighborFinset v, f w
          = f (parent T hT v₀ v) + ∑ w ∈ outward T v₀ v, f w := by
      rw [hNv, Finset.sum_insert hp_not_out]
    -- Split outward: sum = f s + sum over outward \ {s}.
    have hsum2 :
        ∑ w ∈ outward T v₀ v, f w
          = f s + ∑ w ∈ (outward T v₀ v).erase s, f w := by
      conv_lhs => rw [outward_eq_insert_sacrificial T hT h_noleaf v₀ v]
      rw [Finset.sum_insert (Finset.notMem_erase _ _)]
    -- Every w ∈ outward \ {s} has parent v, and is non-sacrificial.
    have herase_zero : ∀ w ∈ (outward T v₀ v).erase s, f w = 0 := by
      intro w hw
      rw [Finset.mem_erase] at hw
      obtain ⟨hw_ne_s, hw_out⟩ := hw
      rw [mem_outward] at hw_out
      obtain ⟨hw_adj, hw_dist⟩ := hw_out
      have hw_ne_v₀ : w ≠ v₀ := by
        intro heq
        have : T.dist v₀ w = 0 := by rw [heq]; exact SimpleGraph.dist_self
        omega
      -- parent w = v.
      have hpw : parent T hT v₀ w = v := by
        obtain ⟨z, _hz_spec, hzuniq⟩ :=
          tree_neighbor_closer_unique hT v₀ w (Ne.symm hw_ne_v₀) _ rfl
        have h1 : parent T hT v₀ w = z :=
          hzuniq (parent T hT v₀ w)
            ⟨(parent_spec T hT v₀ w hw_ne_v₀).1, (parent_spec T hT v₀ w hw_ne_v₀).2⟩
        have hvd : T.dist v₀ v = T.dist v₀ w - 1 := by omega
        have h2 : v = z := hzuniq v ⟨hw_adj.symm, hvd⟩
        rw [h1, ← h2]
      have hw_ne_sac : w ≠ sacrificial T hT h_noleaf v₀ (parent T hT v₀ w) := by
        rw [hpw]; exact hw_ne_s
      rw [hf_def]
      exact fLift_nonsacrificial T hT h_noleaf v₀ g w hw_ne_v₀ hw_ne_sac
    have hsum_erase_zero : ∑ w ∈ (outward T v₀ v).erase s, f w = 0 :=
      Finset.sum_eq_zero herase_zero
    -- Compute f s (non-root case): = (deg v) * f v - f (parent v) - g v.
    have hf_s_nonroot : f s =
        (T.degree v : ℝ) * f v - f (parent T hT v₀ v) - g v := by
      rw [hf_s, if_neg hvv₀]
    -- Assemble.
    show (T.degree v : ℝ) * f v - ∑ w ∈ T.neighborFinset v, f w = g v
    rw [hsum1, hsum2, hsum_erase_zero, hf_s_nonroot]
    ring

end TreeLaplacianLift

/-- **Tree Laplacian lift.** On a leafless tree `T`, the combinatorial
Laplacian `Δ : (V → ℝ) → (V → ℝ)` is surjective. The witness is
`fLift T hT h_noleaf v₀ g`, constructed level-by-level from the root `v₀`,
with the Laplacian equation verified by `fLift_laplacian_eq_g`. The
`h_noleaf` hypothesis is necessary: on a finite tree with leaves,
`∑_v (Δf)(v) = 0` holds identically, so `∑_v g(v) = 0` would be required
— but this cannot follow from the hypotheses, and under `h_noleaf` there
is always a "sacrificial" outward child of every vertex that can absorb
the forced value. -/
theorem tree_laplacian_lift
    {V : Type*} (T : SimpleGraph V) [LocallyFinite T] [DecidableRel T.Adj]
    (hT : T.IsTree) (h_noleaf : ∀ v, 2 ≤ T.degree v) (v₀ : V) (g : V → ℝ) :
    ∃ f : V → ℝ, EnsX2026.Graphs.laplacian_E T f = g :=
  ⟨fLift T hT h_noleaf v₀ g, funext (fLift_laplacian_eq_g T hT h_noleaf v₀ g)⟩

/-- **Q38.** The combinatorial Laplacian `Δ : (F_2 → ℝ) → (F_2 → ℝ)` on the
Cayley graph of `F_2` is surjective.

**Proof.** Direct consequence of the general `tree_laplacian_lift` applied to
the tree `F2_cayley_is_tree` at the root `1`. The construction of a pre-image
is a tree recursion from `1`:

* Fix `f(1) := 0`, and assign three of its four neighbours the value `0`. The
  fourth neighbour is forced by `Δf(1) = g(1)`.
* For every vertex `x ≠ 1`, the equation `Δf(x) = g(x)` involves `f(x)`,
  `f` at the unique inward neighbour `p(x)` (already defined), and `f` at the
  three outward neighbours. Assign two outward neighbours the value `0`; the
  third is forced.

This produces `f : F_2 → ℝ` with `Δ f = g`, proving surjectivity. -/
theorem F2_laplacian_surjective :
    Function.Surjective
      (EnsX2026.Graphs.laplacian_E (EnsX2026.Cayley.cayley_graph F2_generating_set)) := by
  intro g
  obtain ⟨f, hf⟩ :=
    tree_laplacian_lift (EnsX2026.Cayley.cayley_graph F2_generating_set)
      F2_cayley_is_tree F2_cayley_degree_ge_two (1 : F2) g
  exact ⟨f, hf⟩

end EnsX2026.FreeGroup
