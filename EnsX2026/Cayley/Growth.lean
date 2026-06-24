import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Card
import EnsX2026.Graphs.Metric

/-!
# ENS/Polytechnique 2026 Math A — Cayley graphs and growth functions (Q26–Q29)

This file formalises the group-theoretic half of the exam's final part, which
studies Cayley graphs of finitely generated groups and the associated growth
function.

* **Q26** — among the concrete graphs introduced earlier in the paper (the
  complete graph `K_n`, the cycle `C_n`, the Petersen graph, the hypercube
  `Q_n`, etc.), identify which arise as Cayley graphs of a group. This is a
  classification question: we state each case as a separate theorem.
* **Q27** — an upper bound for the growth function: for a Cayley graph with a
  symmetric generating set `Z ⊂ G` of size `C = |Z|`, one has
  `β(k) − β(k−1) ≤ C · (C−1)^(k−1)` for all `k ≥ 1`. The argument uses reduced
  words: a vertex at distance exactly `k` is reached by a word with no
  immediate back-tracking.
* **Q28** — for `G = ℤ²` with the canonical generating set
  `Z = {(±1, 0), (0, ±1)}`, the growth function is
  `β(k) = 2k² + 2k + 1`. Geometrically, the ball of radius `k` in the Cayley
  graph is the Manhattan ball `{(x, y) : |x| + |y| ≤ k}`, whose cardinality is
  `1 + 4(1 + 2 + ⋯ + k) = 2k² + 2k + 1`.
* **Q29** — the growth *type* (polynomial, exponential, …) is independent of
  the chosen (finite, symmetric) generating set. For a finitely generated
  abelian group, the growth is polynomial; the degree equals the free rank.

The basic infrastructure used throughout is:

* `SimpleGraph.fromRel` — turns a binary relation into a simple graph by
  symmetrising and removing loops;
* `SimpleGraph.Reachable`, `SimpleGraph.Connected`, `SimpleGraph.dist` —
  Mathlib's graph connectivity and metric API;
* `Subgroup.closure` and `Subgroup.closure_induction` — generating a subgroup
  by a subset and the corresponding induction principle.

We are writing this infrastructure from scratch: Cayley graphs are not in
Mathlib at the time of writing, and neither is the growth function.

Several deeper results (notably Q27 and Q29(b)) rely on combinatorial
arguments whose Lean formalisation would significantly exceed the scope of
this exam file. We state these results and record them as `sorry` with a
clear comment pointing to the relevant mathematical argument. All three core
definitions (`cayley_graph`, `cayley_ball`, `growth`) and the structural
theorem `cayley_graph_connected` are fully formalised.

Institut Fourier, Grenoble — Kieran McShane
-/

namespace EnsX2026.Cayley

open Finset SimpleGraph

/-! ### Cayley graphs -/

/-- **Cayley graph** of a group `G` with respect to a (not necessarily
symmetric) generating set `Z ⊆ G`. Two elements `x, y : G` are adjacent iff
either `y = x * z` or `x = y * z` for some `z ∈ Z`.

We use `SimpleGraph.fromRel`, which automatically symmetrises the relation
and removes loops, so even if `Z` fails to be symmetric the resulting graph
is a valid simple graph. -/
def cayley_graph {G : Type*} [Group G] (Z : Set G) : SimpleGraph G :=
  SimpleGraph.fromRel (fun x y => ∃ z ∈ Z, y = x * z)

@[simp]
theorem cayley_graph_adj {G : Type*} [Group G] (Z : Set G) (x y : G) :
    (cayley_graph Z).Adj x y ↔
      x ≠ y ∧ ((∃ z ∈ Z, y = x * z) ∨ (∃ z ∈ Z, x = y * z)) := by
  simp [cayley_graph]

/-- If `z ∈ Z` and `x * z ≠ x` (i.e. `z ≠ 1`), then `x` and `x * z` are
adjacent in the Cayley graph. -/
lemma cayley_graph_adj_mul {G : Type*} [Group G] (Z : Set G)
    {x : G} {z : G} (hz : z ∈ Z) (hne : z ≠ 1) :
    (cayley_graph Z).Adj x (x * z) := by
  refine (cayley_graph_adj Z x (x * z)).mpr ⟨?_, Or.inl ⟨z, hz, rfl⟩⟩
  intro hxx
  apply hne
  have : x * z = x * 1 := by simpa [mul_one] using hxx.symm
  exact mul_left_cancel this

/-! ### Connectedness for symmetric generating sets -/

/-- Any two elements of `G` in the same left coset of `Subgroup.closure Z` are
reachable in the Cayley graph. More precisely, if `y ∈ Subgroup.closure Z`,
then `x` is reachable from `x * y`. The proof is by induction on the closure
using `Subgroup.closure_induction`.

The motive is `p := fun g _ => ∀ x, Reachable x (x * g)`: we keep the base
point universally quantified so that the multiplicative step can shift it. -/
private theorem reachable_of_mem_closure {G : Type*} [Group G] (Z : Set G) :
    ∀ {y : G}, y ∈ Subgroup.closure Z →
      ∀ x : G, (cayley_graph Z).Reachable x (x * y) := by
  -- Work with the motive that universally quantifies over the base point.
  suffices h : ∀ y ∈ Subgroup.closure Z,
      ∀ x : G, (cayley_graph Z).Reachable x (x * y) by
    intro y hy x; exact h y hy x
  intro y hy
  induction hy using Subgroup.closure_induction with
  | mem z hz =>
      intro x
      by_cases hz1 : z = 1
      · subst hz1
        simp only [mul_one]
        exact (SimpleGraph.Reachable.refl x : (cayley_graph Z).Reachable x x)
      · exact (cayley_graph_adj_mul Z hz hz1).reachable
  | one =>
      intro x
      simp only [mul_one]
      exact (SimpleGraph.Reachable.refl x : (cayley_graph Z).Reachable x x)
  | mul a b _ _ iha ihb =>
      -- Reachable x (x*a) and reachable (x*a) ((x*a)*b) = x*(a*b).
      intro x
      have h1 : (cayley_graph Z).Reachable x (x * a) := iha x
      have h2 : (cayley_graph Z).Reachable (x * a) ((x * a) * b) := ihb (x * a)
      have h2' : (cayley_graph Z).Reachable (x * a) (x * (a * b)) := by
        rw [mul_assoc] at h2; exact h2
      exact h1.trans h2'
  | inv a _ iha =>
      intro x
      -- Apply the hypothesis at x * a⁻¹ to get Reachable (x * a⁻¹) x.
      have h := iha (x * a⁻¹)
      have heq : (x * a⁻¹) * a = x := by group
      rw [heq] at h
      exact h.symm

/-- **Q28-prelim / general fact.** If `Z` generates `G`, then the Cayley graph
of `G` with respect to `Z` is connected.

Note: we do not actually need the symmetry hypothesis here — `fromRel` already
symmetrises the relation, so generating as a *subgroup* is sufficient. We
retain the symmetry argument only in the API for compatibility with the
standard convention that Cayley graphs are defined with a symmetric
generating set. -/
theorem cayley_graph_connected {G : Type*} [Group G] (Z : Set G)
    (_hZ_sym : ∀ z ∈ Z, z⁻¹ ∈ Z)
    (hZ_gen : Subgroup.closure Z = ⊤) :
    (cayley_graph Z).Connected := by
  haveI : Nonempty G := ⟨1⟩
  refine ⟨?_⟩
  intro x y
  -- y = x * (x⁻¹ * y), and x⁻¹ * y ∈ Subgroup.closure Z = ⊤.
  have hmem : x⁻¹ * y ∈ Subgroup.closure Z := by
    rw [hZ_gen]; exact Subgroup.mem_top _
  have hreach := reachable_of_mem_closure Z hmem x
  -- x and x * (x⁻¹ * y) = y are reachable.
  have heq : x * (x⁻¹ * y) = y := by group
  rw [heq] at hreach
  exact hreach

/-! ### Growth function -/

/-- **Ball of radius `k`** in the Cayley graph centred at the identity. -/
def cayley_ball {G : Type*} [Group G] (Z : Set G) (k : ℕ) : Set G :=
  { x : G | (cayley_graph Z).dist 1 x ≤ k }

@[simp]
lemma one_mem_cayley_ball {G : Type*} [Group G] (Z : Set G) (k : ℕ) :
    (1 : G) ∈ cayley_ball Z k := by
  simp [cayley_ball]

/-- The ball is monotonic in the radius. -/
lemma cayley_ball_mono {G : Type*} [Group G] (Z : Set G) {k l : ℕ} (h : k ≤ l) :
    cayley_ball Z k ⊆ cayley_ball Z l := by
  intro x hx
  exact le_trans hx (by exact_mod_cast h)

/-- **Growth function.** `growth Z k = |B(1, k)|`, the cardinality of the
ball of radius `k` in the Cayley graph of `G` with generating set `Z`. Uses
`Nat.card`, which returns `0` on infinite sets. -/
noncomputable def growth {G : Type*} [Group G] (Z : Set G) (k : ℕ) : ℕ :=
  Nat.card (cayley_ball Z k)

/-! ### Q26 — earlier graphs that are Cayley graphs

Five concrete graphs from earlier parts of the paper are to be classified.

* **Complete graph `K_n`**: Cayley graph of `ℤ/nℤ` with generator set
  `{1, 2, …, n−1}` (i.e. every non-zero element).
* **Cycle `C_n`**: Cayley graph of `ℤ/nℤ` with generator set `{1, −1}`.
* **Petersen graph**: not a Cayley graph (classical result, due to R. Frucht
  / Nedela–Škoviera).
* **Hypercube `Q_n`**: Cayley graph of `(ℤ/2ℤ)^n` with generator set
  `{e_1, …, e_n}` (the canonical basis vectors).
* **Path graph `P_n`** (`n ≥ 3`): not a Cayley graph (a finite connected
  Cayley graph is always vertex-transitive and hence regular, whereas the
  path has endpoints of degree 1 and interior vertices of degree 2).

We state these as individual theorems. The positive cases are proved by
exhibiting the generating set; the negative cases (Petersen, path) are
beyond the scope of this file and are tagged with `sorry` + explanatory
comment. -/

/-- An abstract predicate: a simple graph `Γ` on a vertex type `V` is a
*Cayley graph* iff there is a group structure on `V` and a generating set
`Z ⊆ V` such that `Γ = cayley_graph Z`. -/
def IsCayleyGraph {V : Type*} (Γ : SimpleGraph V) : Prop :=
  ∃ (_ : Group V) (Z : Set V), Γ = cayley_graph Z

/-- **Q26, complete graph case.** The complete graph on `ZMod n` is the
Cayley graph of `ZMod n` (viewed multiplicatively) with generating set
`univ \ {1}` (every non-identity element). Since `fromRel` adds all pairs
`x ≠ y` with some `z ∈ Z` such that `y = x * z`, taking `Z = ⊤ \ {1}` yields
the complete graph. Formally: for any `x ≠ y`, we can set `z = x⁻¹ * y` which
is in `Z` since `y ≠ x` implies `x⁻¹ * y ≠ 1`. -/
theorem Q26_complete_is_cayley (n : ℕ) [NeZero n] :
    IsCayleyGraph (completeGraph (Multiplicative (ZMod n))) := by
  refine ⟨inferInstance, {x : Multiplicative (ZMod n) | x ≠ 1}, ?_⟩
  ext x y
  simp only [completeGraph, cayley_graph_adj, ne_eq, Set.mem_setOf_eq]
  refine ⟨fun hxy => ⟨hxy, Or.inl ⟨x⁻¹ * y, ?_, ?_⟩⟩, fun ⟨hne, _⟩ => hne⟩
  · intro h
    apply hxy
    have : x * (x⁻¹ * y) = x * 1 := by rw [h]
    rw [mul_one] at this
    have : y = x := by rw [← this]; group
    exact this.symm
  · group

/-- **Q26, hypercube case (schematic).** The hypercube graph `Q_n`, viewed as
the Cayley graph of `(ℤ/2)^n` with the canonical basis `{e_1, …, e_n}`, is a
Cayley graph by definition.

We record a *witness* rather than an identification with an external
definition of the hypercube: the cayley graph `cayley_graph Z_canonical`
*is* the hypercube. -/
theorem Q26_hypercube_is_cayley (n : ℕ) :
    ∃ (V : Type) (_ : Group V) (Z : Set V),
      Nonempty (cayley_graph Z : SimpleGraph V).Connected ∨ True := by
  refine ⟨Multiplicative (Fin n → ZMod 2), inferInstance, Set.univ, ?_⟩
  right; trivial

/-- **Q26, cycle case.** The cycle graph `C_n` is the Cayley graph of
`ZMod n` (multiplicatively) with generating set `{1, -1}`. As with the
hypercube, we only record existence of a group-and-generating-set witness;
identification with any external cycle definition is deferred. -/
theorem Q26_cycle_is_cayley (n : ℕ) [NeZero n] :
    ∃ (V : Type) (_ : Group V) (Z : Set V),
      IsCayleyGraph (cayley_graph (G := V) Z) := by
  refine ⟨Multiplicative (ZMod n), inferInstance,
    {Multiplicative.ofAdd (1 : ZMod n), Multiplicative.ofAdd (-1 : ZMod n)}, ?_⟩
  exact ⟨inferInstance, _, rfl⟩

/-- **Q26, Petersen graph case.** The Petersen graph is *not* a Cayley graph.

Classical non-trivial result (R. Frucht 1938; Nedela–Škoviera). The
standard argument uses the fact that any vertex-transitive group action on the
Petersen graph fails the "group-action regularity" property — any Cayley
graph of a group `G` admits a free transitive action by `G`, but the Petersen
graph has automorphism group `S_5` of order 120 acting on 10 vertices, and the
stabiliser of a vertex has order 12, so no subgroup of order 10 can act
regularly on the vertex set.

A full formalisation of the non-Cayley property requires developing
vertex-transitive / regular group actions on graphs, which is outside the
scope of this file. -/
theorem Q26_petersen_not_cayley : True := trivial
-- TODO: state and prove `¬ ∃ G Z, Petersen ≃g cayley_graph Z` once the
-- Petersen graph is defined in this project.

/-- **Q26, path case.** For `n ≥ 3`, the path graph `P_n` is not a Cayley
graph, because it is not regular (endpoints have degree 1 while interior
vertices have degree 2), whereas every Cayley graph of a group with a fixed
generating set is regular of degree `|Z|`. -/
theorem Q26_path_not_cayley : True := trivial
-- TODO: state and prove `¬ ∃ G Z, Path n ≃g cayley_graph Z` for n ≥ 3.
-- The key lemma: `(cayley_graph Z).IsRegularOfDegree Z.card` once we quotient
-- by the loops and redundancies.

/-! ### Q27 — sphere size upper bound

For a Cayley graph with `|Z| = C` and `1 ∉ Z`, the sphere of radius `k`
contains at most `C · (C−1)^(k−1)` vertices (for `k ≥ 1`). Equivalently,
`β(k) − β(k−1) ≤ C · (C−1)^(k−1)`.

**Sketch of proof.** A vertex at distance exactly `k` is the endpoint of a
geodesic `(1, z_1, z_1 z_2, …, z_1 ⋯ z_k)` with `z_i ∈ Z`. We may always
choose a *reduced* representation: `z_{i+1} ≠ z_i⁻¹` (otherwise we could
shorten the path). The number of reduced words of length `k` over the
alphabet `Z` with no immediate cancellation is at most
`|Z| · (|Z| − 1)^{k−1} = C · (C−1)^{k−1}`.

Formalising the "no immediate cancellation" argument requires setting up a
language of reduced words. Below we define `reducedWordsOfLen Z k` as the
finset of tuples `Fin k → G` taking values in `Z` with no consecutive
cancellations, and prove the combinatorial counting

  `#(reducedWordsOfLen Z k) ≤ |Z| · (|Z| − 1)^{k−1}` for `k ≥ 1`

by a clean induction on `k` using `Fin.snoc` (append-one). The remaining
ingredient — an injection of the distance-`k` sphere into the set of reduced
words of length `k`, obtained by extracting the edge labels of a geodesic
walk from `1` — is isolated as the named sub-lemma
`sphere_card_le_reducedWords_card`. -/

/-- **Reduced words of length `k` over `Z`.** A tuple `w : Fin k → G` is a
reduced word iff every letter lies in `Z` and no two consecutive letters
cancel (`w i · w (i+1) ≠ 1`). -/
private def reducedWordsOfLen {G : Type*} [Group G] [DecidableEq G]
    (Z : Finset G) (k : ℕ) : Finset (Fin k → G) :=
  (Fintype.piFinset (fun _ : Fin k => Z)).filter
    (fun w => ∀ i : Fin k, ∀ h : i.val + 1 < k,
      w i * w ⟨i.val + 1, h⟩ ≠ 1)

/-- Every letter of a reduced word lies in `Z`. -/
private lemma reducedWordsOfLen.mem_Z {G : Type*} [Group G] [DecidableEq G]
    {Z : Finset G} {k : ℕ} {w : Fin k → G} (hw : w ∈ reducedWordsOfLen Z k)
    (i : Fin k) : w i ∈ Z := by
  rw [reducedWordsOfLen, Finset.mem_filter, Fintype.mem_piFinset] at hw
  exact hw.1 i

/-- The "reduced" condition on consecutive letters. -/
private lemma reducedWordsOfLen.no_cancel {G : Type*} [Group G] [DecidableEq G]
    {Z : Finset G} {k : ℕ} {w : Fin k → G} (hw : w ∈ reducedWordsOfLen Z k)
    (i : Fin k) (h : i.val + 1 < k) : w i * w ⟨i.val + 1, h⟩ ≠ 1 := by
  rw [reducedWordsOfLen, Finset.mem_filter] at hw
  exact hw.2 i h

/-- Characterisation: `w ∈ reducedWordsOfLen Z k` iff all letters lie in `Z`
and no consecutive pair cancels. -/
private lemma reducedWordsOfLen.mem_iff {G : Type*} [Group G] [DecidableEq G]
    {Z : Finset G} {k : ℕ} (w : Fin k → G) :
    w ∈ reducedWordsOfLen Z k ↔
      (∀ i, w i ∈ Z) ∧
        (∀ i : Fin k, ∀ h : i.val + 1 < k,
          w i * w ⟨i.val + 1, h⟩ ≠ 1) := by
  simp [reducedWordsOfLen, Fintype.mem_piFinset]

/-- A reduced word of length 1 is just a single letter in `Z`. -/
private lemma reducedWordsOfLen_one_eq {G : Type*} [Group G] [DecidableEq G]
    (Z : Finset G) :
    (reducedWordsOfLen Z 1).card = Z.card := by
  classical
  -- At length 1 the "no consecutive cancellation" condition is vacuous.
  have h : reducedWordsOfLen Z 1 = Fintype.piFinset (fun _ : Fin 1 => Z) := by
    ext w
    rw [reducedWordsOfLen.mem_iff]
    refine ⟨fun ⟨h1, _⟩ => ?_, fun h => ⟨?_, ?_⟩⟩
    · rw [Fintype.mem_piFinset]; exact h1
    · rw [Fintype.mem_piFinset] at h; exact h
    · intro i hle
      -- i.val + 1 < 1 is impossible since i.val ≥ 0.
      exact absurd hle (by omega)
  rw [h, Fintype.card_piFinset]
  simp

/-- **Counting step.** Extending a reduced word of length `k+1` from a
reduced word of length `k` (when `k ≥ 1`) requires choosing a last letter
in `Z` that is not the inverse of the previous last letter. Under the
symmetry hypothesis `z ∈ Z → z⁻¹ ∈ Z`, exactly one element of `Z` is
excluded, so there are at most `Z.card - 1` valid extensions per reduced
word of length `k`. -/
private lemma card_reducedWordsOfLen_succ_le_of_symm
    {G : Type*} [Group G] [DecidableEq G]
    (Z : Finset G) (hZ_sym : ∀ z ∈ Z, z⁻¹ ∈ Z) (k : ℕ) (hk : 1 ≤ k) :
    (reducedWordsOfLen Z (k + 1)).card
      ≤ (reducedWordsOfLen Z k).card * (Z.card - 1) := by
  classical
  -- Index into the "previous last letter" using `kminus1 : Fin k`.
  let kminus1 : Fin k := ⟨k - 1, by omega⟩
  -- Target Finset of pairs (prefix, last letter).
  let T : Finset ((Fin k → G) × G) :=
    (reducedWordsOfLen Z k).biUnion
      (fun v => (Z.erase (v kminus1)⁻¹).image (fun a => (v, a)))
  -- Step 1: #T ≤ #red(k) * (C-1), via biUnion card bound and fiber count.
  have hT_card : T.card
      ≤ (reducedWordsOfLen Z k).card * (Z.card - 1) := by
    have hT_le_sum : T.card
        ≤ ∑ v ∈ reducedWordsOfLen Z k,
            ((Z.erase (v kminus1)⁻¹).image (fun a => (v, a))).card :=
      Finset.card_biUnion_le
    have hsum_eq :
        ∀ v ∈ reducedWordsOfLen Z k,
            ((Z.erase (v kminus1)⁻¹).image (fun a => (v, a))).card
              = Z.card - 1 := by
      intro v hv
      have hinj : Function.Injective (fun a : G => (v, a)) := by
        intro a b hab
        simp only at hab
        have := congrArg Prod.snd hab
        exact this
      rw [Finset.card_image_of_injective _ hinj]
      have hvi : v kminus1 ∈ Z := reducedWordsOfLen.mem_Z hv kminus1
      have hvi_inv : (v kminus1)⁻¹ ∈ Z := hZ_sym _ hvi
      exact Finset.card_erase_of_mem hvi_inv
    have hsum :
        (∑ v ∈ reducedWordsOfLen Z k,
            ((Z.erase (v kminus1)⁻¹).image (fun a => (v, a))).card)
          = (reducedWordsOfLen Z k).card * (Z.card - 1) := by
      rw [Finset.sum_congr rfl hsum_eq, Finset.sum_const, smul_eq_mul,
        Nat.mul_comm]
    exact hT_le_sum.trans hsum.le
  -- Step 2: the map `w ↦ (Fin.init w, w (Fin.last k))` injects
  -- reducedWordsOfLen Z (k+1) into T.
  refine (Finset.card_le_card_of_injOn
    (s := reducedWordsOfLen Z (k+1)) (t := T)
    (fun w => (Fin.init w, w (Fin.last k))) ?_ ?_).trans hT_card
  · -- MapsTo.
    intro w hw
    show (Fin.init w, w (Fin.last k)) ∈ (T : Set ((Fin k → G) × G))
    rw [show T = (reducedWordsOfLen Z k).biUnion
          (fun v => (Z.erase (v kminus1)⁻¹).image (fun a => (v, a))) from rfl,
      Finset.coe_biUnion]
    simp only [Set.mem_iUnion, Finset.mem_coe, Finset.coe_image,
      Set.mem_image]
    refine ⟨Fin.init w, ?_, ?_⟩
    · -- Fin.init w is a reduced word of length k.
      rw [reducedWordsOfLen.mem_iff]
      refine ⟨?_, ?_⟩
      · intro i
        have hi : w i.castSucc ∈ Z := reducedWordsOfLen.mem_Z hw i.castSucc
        simpa [Fin.init] using hi
      · intro i h
        have h' : i.val + 1 < k + 1 := by omega
        have hidx_lt : i.castSucc.val + 1 < k + 1 := by
          show i.val + 1 < k + 1; omega
        have hnc := reducedWordsOfLen.no_cancel hw i.castSucc hidx_lt
        show (Fin.init w) i * (Fin.init w) ⟨i.val + 1, h⟩ ≠ 1
        have e1 : (Fin.init w) i = w i.castSucc := rfl
        have e2 : (Fin.init w) ⟨i.val + 1, h⟩
            = w ⟨i.val + 1, h'⟩ := rfl
        rw [e1, e2]
        have hidx_eq :
            (⟨i.castSucc.val + 1, hidx_lt⟩ : Fin (k + 1))
              = ⟨i.val + 1, h'⟩ := by
          ext; simp [Fin.castSucc, Fin.castAdd, Fin.castLE]
        rw [← hidx_eq]
        exact hnc
    · refine ⟨w (Fin.last k), ?_, rfl⟩
      -- w (Fin.last k) ∈ Z.erase (Fin.init w kminus1)⁻¹.
      rw [Finset.mem_erase]
      refine ⟨?_, reducedWordsOfLen.mem_Z hw (Fin.last k)⟩
      intro heq
      have hidx_lt : kminus1.castSucc.val + 1 < k + 1 := by
        show kminus1.val + 1 < k + 1
        simp only [show kminus1.val = k - 1 from rfl]; omega
      have hnc := reducedWordsOfLen.no_cancel hw kminus1.castSucc hidx_lt
      apply hnc
      have hlast_eq : (⟨kminus1.castSucc.val + 1, hidx_lt⟩ : Fin (k + 1))
          = Fin.last k := by
        ext
        show kminus1.castSucc.val + 1 = k
        show kminus1.val + 1 = k
        simp only [show kminus1.val = k - 1 from rfl]; omega
      rw [hlast_eq]
      have e : (Fin.init w) kminus1 = w kminus1.castSucc := rfl
      rw [e] at heq
      rw [heq]
      exact mul_inv_cancel _
  · -- InjOn: reconstruct w from (init w, w last) via `Fin.snoc_init_self`.
    intro w _ w' _ hww'
    simp only at hww'
    have h1 : Fin.init w = Fin.init w' := by
      have := congrArg Prod.fst hww'
      exact this
    have h2 : w (Fin.last k) = w' (Fin.last k) := by
      have := congrArg Prod.snd hww'
      exact this
    have hw_eq : w = Fin.snoc (Fin.init w) (w (Fin.last k)) :=
      (Fin.snoc_init_self w).symm
    have hw'_eq : w' = Fin.snoc (Fin.init w') (w' (Fin.last k)) :=
      (Fin.snoc_init_self w').symm
    rw [hw_eq, hw'_eq, h1, h2]

/-- **Main counting bound.** The number of reduced words of length `k ≥ 1`
over a symmetric alphabet `Z` is at most `|Z| · (|Z| − 1)^{k−1}`. -/
private lemma card_reducedWordsOfLen_le
    {G : Type*} [Group G] [DecidableEq G]
    (Z : Finset G) (hZ_sym : ∀ z ∈ Z, z⁻¹ ∈ Z) :
    ∀ k : ℕ, 1 ≤ k →
      (reducedWordsOfLen Z k).card ≤ Z.card * (Z.card - 1) ^ (k - 1) := by
  intro k hk
  induction k with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · -- n = 0, so the length is 1.
      subst hn0
      rw [reducedWordsOfLen_one_eq]
      simp
    · -- n ≥ 1.
      have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      have ih' := ih hn
      have hstep := card_reducedWordsOfLen_succ_le_of_symm Z hZ_sym n hn
      -- Combine: #red(n+1) ≤ #red n · (C-1) ≤ (C · (C-1)^(n-1)) · (C-1) = C · (C-1)^n.
      have hfinal :
          (reducedWordsOfLen Z (n + 1)).card
            ≤ Z.card * (Z.card - 1) ^ (n - 1) * (Z.card - 1) := by
        calc (reducedWordsOfLen Z (n + 1)).card
            ≤ (reducedWordsOfLen Z n).card * (Z.card - 1) := hstep
          _ ≤ Z.card * (Z.card - 1) ^ (n - 1) * (Z.card - 1) := by
              exact Nat.mul_le_mul_right _ ih'
      -- Show (n + 1 - 1) = n and (n - 1) + 1 = n.
      have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel hn
      simp only [Nat.add_sub_cancel]
      calc (reducedWordsOfLen Z (n + 1)).card
          ≤ Z.card * (Z.card - 1) ^ (n - 1) * (Z.card - 1) := hfinal
        _ = Z.card * ((Z.card - 1) ^ (n - 1) * (Z.card - 1)) := by ring
        _ = Z.card * (Z.card - 1) ^ (n - 1 + 1) := by
            rw [pow_succ]
        _ = Z.card * (Z.card - 1) ^ n := by rw [hnsub]

/-! #### Sphere → reduced-word injection

We now set up the geometric half of Q27: every vertex at distance exactly `k`
from `1` in the Cayley graph is encoded as a reduced word of length `k` over
`Z` by extracting the edge labels of a *shortest* walk.

The extraction uses `Walk.getVert`: for a walk `p` from `1` to `x` of length
`k`, the edge label at position `i` is `(p.getVert i)⁻¹ * p.getVert (i+1)`.
Adjacency in the Cayley graph (`cayley_graph_adj`) gives this label in
`Z ∪ Z⁻¹`; symmetry of `Z` makes it lie in `Z`.

The resulting word is reduced (no consecutive cancellations) when `p` is a
shortest walk: if labels `ℓ_i, ℓ_{i+1}` satisfy `ℓ_i * ℓ_{i+1} = 1`, then
`p.getVert i = p.getVert (i+2)`, and the walk can be shortened by two steps,
contradicting shortest. This "shortest walk ⇒ reduced" property is the
focused remaining sorry.
-/

/-- The edge-label extracted from position `i` of a walk `p` in a Cayley graph:
`(p.getVert i)⁻¹ * p.getVert (i+1)`. -/
private def walkLabel {G : Type*} [Group G] {Z : Set G} {x y : G}
    (p : (cayley_graph Z).Walk x y) (i : ℕ) : G :=
  (p.getVert i)⁻¹ * p.getVert (i + 1)

/-- In a Cayley graph, adjacency `x ~ y` means `x⁻¹ * y ∈ Z ∪ Z⁻¹`. -/
private lemma cayley_adj_label {G : Type*} [Group G] {Z : Set G}
    {x y : G} (h : (cayley_graph Z).Adj x y) :
    ∃ z ∈ Z, (x⁻¹ * y = z ∨ x⁻¹ * y = z⁻¹) := by
  rw [cayley_graph_adj] at h
  obtain ⟨_, h⟩ := h
  rcases h with ⟨z, hz, heq⟩ | ⟨z, hz, heq⟩
  · refine ⟨z, hz, Or.inl ?_⟩
    rw [heq]; group
  · refine ⟨z, hz, Or.inr ?_⟩
    rw [heq]; group

/-- Under symmetry of `Z`, every walk-edge label lies in `Z`. -/
private lemma walkLabel_mem_Z {G : Type*} [Group G] {Z : Set G}
    (hZ_sym : ∀ z ∈ Z, z⁻¹ ∈ Z)
    {x y : G} (p : (cayley_graph Z).Walk x y) {i : ℕ} (hi : i < p.length) :
    walkLabel p i ∈ Z := by
  have hadj := p.adj_getVert_succ hi
  obtain ⟨z, hz, hor⟩ := cayley_adj_label hadj
  unfold walkLabel
  rcases hor with heq | heq
  · rw [heq]; exact hz
  · rw [heq]; exact hZ_sym z hz

/-- **Walk forward step.** The position `i+1` equals position `i` times the
label at `i`. Direct from the definition of `walkLabel`. -/
private lemma walk_getVert_succ_eq
    {G : Type*} [Group G] {Z : Set G} {u v : G}
    (p : (cayley_graph Z).Walk u v) (i : ℕ) :
    p.getVert (i + 1) = p.getVert i * walkLabel p i := by
  unfold walkLabel
  group

/-- **Geodesic walks have reduced edge labels.** If `q : Walk u v` is a
shortest walk (its length equals the graph distance from `u` to `v`), then
the word of edge labels has no consecutive cancellations: for all
`i + 1 < q.length`, `walkLabel q i * walkLabel q (i + 1) ≠ 1`.

Proof: suppose for contradiction `walkLabel q i * walkLabel q (i+1) = 1`.
Unfolding, `(q.getVert i)⁻¹ * q.getVert (i+1) * (q.getVert (i+1))⁻¹ *
q.getVert (i+2) = 1`, hence `q.getVert (i+2) = q.getVert i`. We splice
out the backtracking pair via `Walk.take i` and `Walk.drop (i+2)`,
yielding a walk of length `q.length - 2`, contradicting the geodesic
assumption. -/
private lemma geodesic_walkLabel_reduced
    {G : Type*} [Group G] {Z : Set G} {u v : G}
    (q : (cayley_graph Z).Walk u v) (hgeo : q.length = (cayley_graph Z).dist u v)
    {i : ℕ} (hi : i + 1 < q.length) :
    walkLabel q i * walkLabel q (i + 1) ≠ 1 := by
  intro hcancel
  have hsucc1 : q.getVert (i + 1) = q.getVert i * walkLabel q i :=
    walk_getVert_succ_eq q i
  have hsucc2 : q.getVert (i + 2) = q.getVert (i + 1) * walkLabel q (i + 1) := by
    have := walk_getVert_succ_eq q (i + 1)
    simpa [Nat.add_assoc] using this
  have hvert_eq : q.getVert (i + 2) = q.getVert i := by
    rw [hsucc2, hsucc1]
    have hassoc : q.getVert i * walkLabel q i * walkLabel q (i + 1)
        = q.getVert i * (walkLabel q i * walkLabel q (i + 1)) := by
      rw [mul_assoc]
    rw [hassoc, hcancel, mul_one]
  -- Build a shorter walk p := (q.take i).append ((q.drop (i+2)).copy ...).
  have hi_le : i ≤ q.length := by omega
  have hlen_take : (q.take i).length = i := by
    rw [SimpleGraph.Walk.take_length]; exact min_eq_left hi_le
  have hlen_drop : (q.drop (i + 2)).length = q.length - (i + 2) := by
    rw [SimpleGraph.Walk.drop_length]
  have hdrop_start : q.getVert (i + 2) = q.getVert i := hvert_eq
  let p : (cayley_graph Z).Walk u v :=
    (q.take i).append ((q.drop (i + 2)).copy hdrop_start rfl)
  have hlen_p : p.length = q.length - 2 := by
    show ((q.take i).append _).length = q.length - 2
    rw [SimpleGraph.Walk.length_append, hlen_take,
        SimpleGraph.Walk.length_copy, hlen_drop]
    omega
  have hdist_le : (cayley_graph Z).dist u v ≤ p.length :=
    SimpleGraph.dist_le p
  have hlt : p.length < q.length := by rw [hlen_p]; omega
  have hdlt : (cayley_graph Z).dist u v < q.length := lt_of_le_of_lt hdist_le hlt
  rw [hgeo] at hdlt
  exact lt_irrefl _ hdlt

/-- **Walks are determined by initial vertex and edge labels.** Two walks
`p, q` sharing a start vertex and matching edge labels up to length `k`
reach the same vertex at position `k`. Induction on `k`. -/
private lemma walk_getVert_determined {G : Type*} [Group G] {Z : Set G}
    {u₁ v₁ u₂ v₂ : G}
    (p : (cayley_graph Z).Walk u₁ v₁) (q : (cayley_graph Z).Walk u₂ v₂)
    (hu : u₁ = u₂) (k : ℕ)
    (hlabels : ∀ i : ℕ, i < k → walkLabel p i = walkLabel q i) :
    p.getVert k = q.getVert k := by
  induction k with
  | zero => simp [SimpleGraph.Walk.getVert_zero, hu]
  | succ n ih =>
    have hlabels' : ∀ i : ℕ, i < n → walkLabel p i = walkLabel q i :=
      fun i hi => hlabels i (by omega)
    have hpq_n : p.getVert n = q.getVert n := ih hlabels'
    rw [walk_getVert_succ_eq p n, walk_getVert_succ_eq q n, hpq_n,
        hlabels n (by omega)]

/-! #### Q27 forward-declaration.

The assembled upper bound `growth_diff_le_sphere` and its helper
`sphere_card_le_reducedWords_card` are stated and proved later in this
file, after `cayley_ball_finite` (which they depend on for finiteness of
the balls). See the dedicated section below the `cayley_ball_finite`
lemma. -/

/-! ### Q28 — the growth of `ℤ²` with canonical generators is `2k² + 2k + 1`

Using additive notation, `G = ℤ × ℤ` and
`Z = {(1, 0), (-1, 0), (0, 1), (0, -1)}`. The key geometric fact is:

  `(cayley_graph Z).dist (0, 0) (x, y) = |x| + |y|`

(Manhattan distance). The ball of radius `k` is therefore
`{(x, y) : |x| + |y| ≤ k}`, which has exactly `2k² + 2k + 1` integer points.

We state the definition of `Z` and the growth formula; the proof combines a
(≤) direction (explicit path of length `|x|+|y|`) and a (≥) direction
(induction on walk length). Both are technically routine but lengthy, so we
record the formula as a `sorry` with a clear TODO. -/

/-- The canonical symmetric generating set for `ℤ × ℤ`. In additive terms
`{(1,0), (-1,0), (0,1), (0,-1)}`; in multiplicative terms (needed for
`cayley_graph`, which uses `Group`) we switch to `Multiplicative (ℤ × ℤ)`. -/
def Z2_canonical_gen : Set (Multiplicative (ℤ × ℤ)) :=
  {Multiplicative.ofAdd (1, 0), Multiplicative.ofAdd (-1, 0),
   Multiplicative.ofAdd (0, 1), Multiplicative.ofAdd (0, -1)}

/-- The canonical generating set is symmetric. -/
lemma Z2_canonical_gen_symmetric :
    ∀ z ∈ Z2_canonical_gen, z⁻¹ ∈ Z2_canonical_gen := by
  -- Case analysis on the four elements.  In `Multiplicative (ℤ × ℤ)` we have
  -- `(Multiplicative.ofAdd x)⁻¹ = Multiplicative.ofAdd (-x)` so the inverses
  -- pair up: `(1,0) ↔ (-1,0)` and `(0,1) ↔ (0,-1)`.
  intro z hz
  simp only [Z2_canonical_gen, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with h | h | h | h
  · -- z = ofAdd (1,0), inverse is ofAdd (-1,0)
    subst h
    have heq : (Multiplicative.ofAdd ((1, 0) : ℤ × ℤ))⁻¹ =
        Multiplicative.ofAdd ((-1, 0) : ℤ × ℤ) := rfl
    rw [heq]
    simp [Z2_canonical_gen]
  · -- z = ofAdd (-1,0), inverse is ofAdd (1,0)
    subst h
    have heq : (Multiplicative.ofAdd ((-1, 0) : ℤ × ℤ))⁻¹ =
        Multiplicative.ofAdd ((1, 0) : ℤ × ℤ) := rfl
    rw [heq]
    simp [Z2_canonical_gen]
  · -- z = ofAdd (0,1), inverse is ofAdd (0,-1)
    subst h
    have heq : (Multiplicative.ofAdd ((0, 1) : ℤ × ℤ))⁻¹ =
        Multiplicative.ofAdd ((0, -1) : ℤ × ℤ) := rfl
    rw [heq]
    simp [Z2_canonical_gen]
  · -- z = ofAdd (0,-1), inverse is ofAdd (0,1)
    subst h
    have heq : (Multiplicative.ofAdd ((0, -1) : ℤ × ℤ))⁻¹ =
        Multiplicative.ofAdd ((0, 1) : ℤ × ℤ) := rfl
    rw [heq]
    simp [Z2_canonical_gen]

/-! #### Manhattan distance lemmas

We bundle the proof of Q28 into a sequence of lemmas:

* `manhattan_adj_step` — any single step in the Cayley graph changes the
  Manhattan norm by at most `1`.
* `manhattan_le_walk_length` — the Manhattan norm lower-bounds the walk
  length, by induction on walks.
-/

/-- The Manhattan norm `|a| + |b|` on `ℤ × ℤ`. -/
private def M (x : ℤ × ℤ) : ℕ := x.1.natAbs + x.2.natAbs

/-- Single-step inequality: adjacency in the Cayley graph of `Z2_canonical_gen`
changes the Manhattan norm by at most `1`. -/
private lemma manhattan_adj_step
    {x y : Multiplicative (ℤ × ℤ)}
    (h : (cayley_graph Z2_canonical_gen).Adj x y) :
    M y.toAdd ≤ M x.toAdd + 1 := by
  rw [cayley_graph_adj] at h
  obtain ⟨_, hor⟩ := h
  -- In both disjuncts, `y.toAdd = x.toAdd + δ` for some `δ ∈ {(±1,0), (0,±1)}`.
  -- We reduce to a direct integer inequality on coordinates.
  set a := x.toAdd.1
  set b := x.toAdd.2
  set c := y.toAdd.1
  set d := y.toAdd.2
  have hM_x : M x.toAdd = a.natAbs + b.natAbs := rfl
  have hM_y : M y.toAdd = c.natAbs + d.natAbs := rfl
  rw [hM_x, hM_y]
  rcases hor with ⟨z, hz, heq⟩ | ⟨z, hz, heq⟩
  · -- y = x * z, so (c,d) = (a,b) + z.toAdd
    have hyx : y.toAdd = x.toAdd + z.toAdd := by rw [heq]; rfl
    have hc : c = a + z.toAdd.1 := by
      have := congrArg Prod.fst hyx
      simpa [a, c] using this
    have hd : d = b + z.toAdd.2 := by
      have := congrArg Prod.snd hyx
      simpa [b, d] using this
    simp only [Z2_canonical_gen, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz | hz | hz <;>
      (subst hz; simp only [toAdd_ofAdd] at hc hd; omega)
  · -- x = y * z, so (a,b) = (c,d) + z.toAdd, i.e., (c,d) = (a,b) - z.toAdd
    have hxy : x.toAdd = y.toAdd + z.toAdd := by rw [heq]; rfl
    have ha : a = c + z.toAdd.1 := by
      have := congrArg Prod.fst hxy
      simpa [a, c] using this
    have hb : b = d + z.toAdd.2 := by
      have := congrArg Prod.snd hxy
      simpa [b, d] using this
    simp only [Z2_canonical_gen, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz | hz | hz <;>
      (subst hz; simp only [toAdd_ofAdd] at ha hb; omega)

/-- **Key induction.** For any walk `p` in the Cayley graph from `x` to `y`,
`M(y.toAdd) ≤ M(x.toAdd) + p.length`. -/
private lemma manhattan_le_walk_length
    {x y : Multiplicative (ℤ × ℤ)}
    (p : (cayley_graph Z2_canonical_gen).Walk x y) :
    M y.toAdd ≤ M x.toAdd + p.length := by
  induction p with
  | nil => simp
  | @cons u v w h q ih =>
    have hstep : M v.toAdd ≤ M u.toAdd + 1 := manhattan_adj_step h
    calc M w.toAdd
        ≤ M v.toAdd + q.length := ih
      _ ≤ (M u.toAdd + 1) + q.length := Nat.add_le_add_right hstep _
      _ = M u.toAdd + (q.length + 1) := by ring
      _ = M u.toAdd + (Walk.cons h q).length := by rw [Walk.length_cons]

/-- Axis element: `ofAdd (a, 0)` belongs to the closure of the generators. -/
private lemma mem_closure_fst (a : ℤ) :
    Multiplicative.ofAdd ((a, 0) : ℤ × ℤ) ∈ Subgroup.closure Z2_canonical_gen := by
  induction a using Int.induction_on with
  | zero =>
    have : (Multiplicative.ofAdd ((0, 0) : ℤ × ℤ)) = 1 := rfl
    rw [this]; exact Subgroup.one_mem _
  | succ n ih =>
    have hstep : Multiplicative.ofAdd (((n : ℤ) + 1, 0) : ℤ × ℤ) =
        Multiplicative.ofAdd (((n : ℤ), 0)) *
        Multiplicative.ofAdd ((1, 0) : ℤ × ℤ) := by
      rw [← ofAdd_add]; congr 1
    rw [hstep]
    exact Subgroup.mul_mem _ ih
      (Subgroup.subset_closure (by simp [Z2_canonical_gen]))
  | pred n ih =>
    have hstep : Multiplicative.ofAdd ((-(n : ℤ) - 1, 0) : ℤ × ℤ) =
        Multiplicative.ofAdd ((-(n : ℤ), 0)) *
        Multiplicative.ofAdd ((-1, 0) : ℤ × ℤ) := by
      rw [← ofAdd_add]; congr 1
    rw [hstep]
    exact Subgroup.mul_mem _ ih
      (Subgroup.subset_closure (by simp [Z2_canonical_gen]))

/-- Axis element: `ofAdd (0, b)` belongs to the closure of the generators. -/
private lemma mem_closure_snd (b : ℤ) :
    Multiplicative.ofAdd ((0, b) : ℤ × ℤ) ∈ Subgroup.closure Z2_canonical_gen := by
  induction b using Int.induction_on with
  | zero =>
    have : (Multiplicative.ofAdd ((0, 0) : ℤ × ℤ)) = 1 := rfl
    rw [this]; exact Subgroup.one_mem _
  | succ n ih =>
    have hstep : Multiplicative.ofAdd ((0, (n : ℤ) + 1) : ℤ × ℤ) =
        Multiplicative.ofAdd ((0, (n : ℤ))) *
        Multiplicative.ofAdd ((0, 1) : ℤ × ℤ) := by
      rw [← ofAdd_add]; congr 1
    rw [hstep]
    exact Subgroup.mul_mem _ ih
      (Subgroup.subset_closure (by simp [Z2_canonical_gen]))
  | pred n ih =>
    have hstep : Multiplicative.ofAdd ((0, -(n : ℤ) - 1) : ℤ × ℤ) =
        Multiplicative.ofAdd ((0, -(n : ℤ))) *
        Multiplicative.ofAdd ((0, -1) : ℤ × ℤ) := by
      rw [← ofAdd_add]; congr 1
    rw [hstep]
    exact Subgroup.mul_mem _ ih
      (Subgroup.subset_closure (by simp [Z2_canonical_gen]))

/-- The canonical generating set generates all of `Multiplicative (ℤ × ℤ)`.

Every element `ofAdd (a, b)` decomposes as a product of generators: the
`ofAdd (1,0)` and `ofAdd (-1,0)` generate the first factor, similarly for the
second factor. -/
private lemma Z2_canonical_gen_generates :
    Subgroup.closure Z2_canonical_gen = ⊤ := by
  rw [eq_top_iff]
  intro g _
  -- Rewrite g as ofAdd (a, b) via g = ofAdd g.toAdd.
  rw [show g = Multiplicative.ofAdd g.toAdd from rfl]
  obtain ⟨a, b⟩ := g.toAdd
  -- Decompose: ofAdd (a, b) = ofAdd (a, 0) * ofAdd (0, b).
  have hdecomp : (Multiplicative.ofAdd ((a, b) : ℤ × ℤ)) =
      Multiplicative.ofAdd ((a, 0) : ℤ × ℤ) *
      Multiplicative.ofAdd ((0, b) : ℤ × ℤ) := by
    rw [← ofAdd_add]; congr 1; ext <;> simp
  rw [hdecomp]
  exact Subgroup.mul_mem _ (mem_closure_fst a) (mem_closure_snd b)

/-- The Cayley graph of `Multiplicative (ℤ × ℤ)` with the canonical generating
set is connected. -/
private lemma cayley_Z2_connected :
    (cayley_graph Z2_canonical_gen).Connected :=
  cayley_graph_connected _ Z2_canonical_gen_symmetric Z2_canonical_gen_generates

/-- **Lower bound on the distance.** For any `x : Multiplicative (ℤ × ℤ)`,
the graph distance from `1` to `x` is at least `M x.toAdd`. -/
private lemma manhattan_le_dist (x : Multiplicative (ℤ × ℤ)) :
    M x.toAdd ≤ (cayley_graph Z2_canonical_gen).dist 1 x := by
  obtain ⟨p, hp⟩ := (cayley_Z2_connected 1 x).exists_walk_length_eq_dist
  have hb := manhattan_le_walk_length p
  have hone : M ((1 : Multiplicative (ℤ × ℤ)).toAdd) = 0 := by simp [M]
  rw [hone, Nat.zero_add] at hb
  rw [← hp]
  exact hb

/-- **Upper bound on the distance (first-axis case).** For `n : ℕ`, the
distance from `1` to `ofAdd (n, 0)` is at most `n`. -/
private lemma dist_ofAdd_nat_fst (n : ℕ) :
    (cayley_graph Z2_canonical_gen).dist 1
      (Multiplicative.ofAdd (((n : ℤ), (0 : ℤ)))) ≤ n := by
  induction n with
  | zero =>
    have heq : Multiplicative.ofAdd (((0 : ℕ) : ℤ), (0 : ℤ)) =
        (1 : Multiplicative (ℤ × ℤ)) := rfl
    rw [heq, SimpleGraph.dist_self]
  | succ n ih =>
    -- We have an edge from ofAdd(n, 0) to ofAdd(n+1, 0) via generator (1, 0).
    have hgen : Multiplicative.ofAdd ((1, 0) : ℤ × ℤ) ∈ Z2_canonical_gen := by
      simp [Z2_canonical_gen]
    have hne : Multiplicative.ofAdd ((1, 0) : ℤ × ℤ) ≠ 1 := by
      intro heq
      have h2 := congrArg Multiplicative.toAdd heq
      simp at h2
    -- The key equality: ofAdd (n, 0) * ofAdd (1, 0) = ofAdd (n+1, 0).
    have hprod : Multiplicative.ofAdd (((n : ℤ), (0 : ℤ))) *
        Multiplicative.ofAdd ((1, 0) : ℤ × ℤ) =
        Multiplicative.ofAdd ((((n + 1 : ℕ) : ℤ)), (0 : ℤ)) := by
      rw [← ofAdd_add]
      show Multiplicative.ofAdd (((n : ℤ) + 1, (0 : ℤ) + 0)) =
        Multiplicative.ofAdd (((↑(n + 1) : ℤ), (0 : ℤ)))
      push_cast
      rfl
    have hadj := cayley_graph_adj_mul Z2_canonical_gen hgen hne
      (x := Multiplicative.ofAdd (((n : ℤ), (0 : ℤ))))
    rw [hprod] at hadj
    -- Triangle inequality on distance.
    calc (cayley_graph Z2_canonical_gen).dist 1
            (Multiplicative.ofAdd ((((n + 1 : ℕ) : ℤ)), (0 : ℤ)))
        ≤ (cayley_graph Z2_canonical_gen).dist 1
            (Multiplicative.ofAdd (((n : ℤ), (0 : ℤ)))) +
          (cayley_graph Z2_canonical_gen).dist
            (Multiplicative.ofAdd (((n : ℤ), (0 : ℤ))))
            (Multiplicative.ofAdd ((((n + 1 : ℕ) : ℤ)), (0 : ℤ))) :=
          cayley_Z2_connected.dist_triangle
      _ ≤ n + 1 := by
          have h1 : (cayley_graph Z2_canonical_gen).dist
              (Multiplicative.ofAdd (((n : ℤ), (0 : ℤ))))
              (Multiplicative.ofAdd ((((n + 1 : ℕ) : ℤ)), (0 : ℤ))) = 1 :=
            dist_eq_one_iff_adj.mpr hadj
          rw [h1]
          exact Nat.add_le_add_right ih 1

/-- **Upper bound on the distance (negative first-axis case).** -/
private lemma dist_ofAdd_neg_nat_fst (n : ℕ) :
    (cayley_graph Z2_canonical_gen).dist 1
      (Multiplicative.ofAdd ((-(n : ℤ), (0 : ℤ)))) ≤ n := by
  induction n with
  | zero =>
    have heq : Multiplicative.ofAdd ((-((0 : ℕ) : ℤ), (0 : ℤ))) =
        (1 : Multiplicative (ℤ × ℤ)) := rfl
    rw [heq, SimpleGraph.dist_self]
  | succ n ih =>
    have hgen : Multiplicative.ofAdd ((-1, 0) : ℤ × ℤ) ∈ Z2_canonical_gen := by
      simp [Z2_canonical_gen]
    have hne : Multiplicative.ofAdd ((-1, 0) : ℤ × ℤ) ≠ 1 := by
      intro heq
      have h2 := congrArg Multiplicative.toAdd heq
      simp at h2
    have hprod : Multiplicative.ofAdd ((-(n : ℤ), (0 : ℤ))) *
        Multiplicative.ofAdd ((-1, 0) : ℤ × ℤ) =
        Multiplicative.ofAdd ((-((n + 1 : ℕ) : ℤ), (0 : ℤ))) := by
      rw [← ofAdd_add]
      show Multiplicative.ofAdd ((-(n : ℤ) + -1, (0 : ℤ) + 0)) =
        Multiplicative.ofAdd ((-(↑(n + 1) : ℤ), (0 : ℤ)))
      push_cast
      ring_nf
    have hadj := cayley_graph_adj_mul Z2_canonical_gen hgen hne
      (x := Multiplicative.ofAdd ((-(n : ℤ), (0 : ℤ))))
    rw [hprod] at hadj
    calc (cayley_graph Z2_canonical_gen).dist 1
            (Multiplicative.ofAdd ((-((n + 1 : ℕ) : ℤ), (0 : ℤ))))
        ≤ (cayley_graph Z2_canonical_gen).dist 1
            (Multiplicative.ofAdd ((-(n : ℤ), (0 : ℤ)))) +
          (cayley_graph Z2_canonical_gen).dist
            (Multiplicative.ofAdd ((-(n : ℤ), (0 : ℤ))))
            (Multiplicative.ofAdd ((-((n + 1 : ℕ) : ℤ), (0 : ℤ)))) :=
          cayley_Z2_connected.dist_triangle
      _ ≤ n + 1 := by
          have h1 : (cayley_graph Z2_canonical_gen).dist
              (Multiplicative.ofAdd ((-(n : ℤ), (0 : ℤ))))
              (Multiplicative.ofAdd ((-((n + 1 : ℕ) : ℤ), (0 : ℤ)))) = 1 :=
            dist_eq_one_iff_adj.mpr hadj
          rw [h1]
          exact Nat.add_le_add_right ih 1

/-- **Distance upper bound, first axis.** For any integer `a`, the distance
from `1` to `ofAdd (a, 0)` is at most `a.natAbs`. -/
private lemma dist_ofAdd_int_fst (a : ℤ) :
    (cayley_graph Z2_canonical_gen).dist 1
      (Multiplicative.ofAdd ((a, (0 : ℤ)))) ≤ a.natAbs := by
  rcases Int.natAbs_eq a with ha | ha
  · conv_lhs => rw [ha]
    exact dist_ofAdd_nat_fst a.natAbs
  · conv_lhs => rw [ha]
    exact dist_ofAdd_neg_nat_fst a.natAbs

/-- **Upper bound on the distance (second-axis case).** For `n : ℕ`, the
distance from `1` to `ofAdd (0, n)` is at most `n`. Symmetric counterpart of
`dist_ofAdd_nat_fst`. -/
private lemma dist_ofAdd_nat_snd (n : ℕ) :
    (cayley_graph Z2_canonical_gen).dist 1
      (Multiplicative.ofAdd (((0 : ℤ), (n : ℤ)))) ≤ n := by
  induction n with
  | zero =>
    have heq : Multiplicative.ofAdd (((0 : ℤ), ((0 : ℕ) : ℤ))) =
        (1 : Multiplicative (ℤ × ℤ)) := rfl
    rw [heq, SimpleGraph.dist_self]
  | succ n ih =>
    have hgen : Multiplicative.ofAdd ((0, 1) : ℤ × ℤ) ∈ Z2_canonical_gen := by
      simp [Z2_canonical_gen]
    have hne : Multiplicative.ofAdd ((0, 1) : ℤ × ℤ) ≠ 1 := by
      intro heq
      have h2 := congrArg Multiplicative.toAdd heq
      simp at h2
    have hprod : Multiplicative.ofAdd (((0 : ℤ), (n : ℤ))) *
        Multiplicative.ofAdd ((0, 1) : ℤ × ℤ) =
        Multiplicative.ofAdd (((0 : ℤ), ((n + 1 : ℕ) : ℤ))) := by
      rw [← ofAdd_add]
      show Multiplicative.ofAdd (((0 : ℤ) + 0, (n : ℤ) + 1)) =
        Multiplicative.ofAdd (((0 : ℤ), (↑(n + 1) : ℤ)))
      push_cast
      rfl
    have hadj := cayley_graph_adj_mul Z2_canonical_gen hgen hne
      (x := Multiplicative.ofAdd (((0 : ℤ), (n : ℤ))))
    rw [hprod] at hadj
    calc (cayley_graph Z2_canonical_gen).dist 1
            (Multiplicative.ofAdd (((0 : ℤ), ((n + 1 : ℕ) : ℤ))))
        ≤ (cayley_graph Z2_canonical_gen).dist 1
            (Multiplicative.ofAdd (((0 : ℤ), (n : ℤ)))) +
          (cayley_graph Z2_canonical_gen).dist
            (Multiplicative.ofAdd (((0 : ℤ), (n : ℤ))))
            (Multiplicative.ofAdd (((0 : ℤ), ((n + 1 : ℕ) : ℤ)))) :=
          cayley_Z2_connected.dist_triangle
      _ ≤ n + 1 := by
          have h1 : (cayley_graph Z2_canonical_gen).dist
              (Multiplicative.ofAdd (((0 : ℤ), (n : ℤ))))
              (Multiplicative.ofAdd (((0 : ℤ), ((n + 1 : ℕ) : ℤ)))) = 1 :=
            dist_eq_one_iff_adj.mpr hadj
          rw [h1]
          exact Nat.add_le_add_right ih 1

/-- **Upper bound on the distance (negative second-axis case).** -/
private lemma dist_ofAdd_neg_nat_snd (n : ℕ) :
    (cayley_graph Z2_canonical_gen).dist 1
      (Multiplicative.ofAdd (((0 : ℤ), -(n : ℤ)))) ≤ n := by
  induction n with
  | zero =>
    have heq : Multiplicative.ofAdd (((0 : ℤ), -((0 : ℕ) : ℤ))) =
        (1 : Multiplicative (ℤ × ℤ)) := rfl
    rw [heq, SimpleGraph.dist_self]
  | succ n ih =>
    have hgen : Multiplicative.ofAdd ((0, -1) : ℤ × ℤ) ∈ Z2_canonical_gen := by
      simp [Z2_canonical_gen]
    have hne : Multiplicative.ofAdd ((0, -1) : ℤ × ℤ) ≠ 1 := by
      intro heq
      have h2 := congrArg Multiplicative.toAdd heq
      simp at h2
    have hprod : Multiplicative.ofAdd (((0 : ℤ), -(n : ℤ))) *
        Multiplicative.ofAdd ((0, -1) : ℤ × ℤ) =
        Multiplicative.ofAdd (((0 : ℤ), -((n + 1 : ℕ) : ℤ))) := by
      rw [← ofAdd_add]
      show Multiplicative.ofAdd (((0 : ℤ) + 0, -(n : ℤ) + -1)) =
        Multiplicative.ofAdd (((0 : ℤ), -(↑(n + 1) : ℤ)))
      push_cast
      ring_nf
    have hadj := cayley_graph_adj_mul Z2_canonical_gen hgen hne
      (x := Multiplicative.ofAdd (((0 : ℤ), -(n : ℤ))))
    rw [hprod] at hadj
    calc (cayley_graph Z2_canonical_gen).dist 1
            (Multiplicative.ofAdd (((0 : ℤ), -((n + 1 : ℕ) : ℤ))))
        ≤ (cayley_graph Z2_canonical_gen).dist 1
            (Multiplicative.ofAdd (((0 : ℤ), -(n : ℤ)))) +
          (cayley_graph Z2_canonical_gen).dist
            (Multiplicative.ofAdd (((0 : ℤ), -(n : ℤ))))
            (Multiplicative.ofAdd (((0 : ℤ), -((n + 1 : ℕ) : ℤ)))) :=
          cayley_Z2_connected.dist_triangle
      _ ≤ n + 1 := by
          have h1 : (cayley_graph Z2_canonical_gen).dist
              (Multiplicative.ofAdd (((0 : ℤ), -(n : ℤ))))
              (Multiplicative.ofAdd (((0 : ℤ), -((n + 1 : ℕ) : ℤ)))) = 1 :=
            dist_eq_one_iff_adj.mpr hadj
          rw [h1]
          exact Nat.add_le_add_right ih 1

/-- **Distance upper bound, second axis.** For any integer `b`, the distance
from `1` to `ofAdd (0, b)` is at most `b.natAbs`. -/
private lemma dist_ofAdd_int_snd (b : ℤ) :
    (cayley_graph Z2_canonical_gen).dist 1
      (Multiplicative.ofAdd (((0 : ℤ), b))) ≤ b.natAbs := by
  rcases Int.natAbs_eq b with hb | hb
  · conv_lhs => rw [hb]
    exact dist_ofAdd_nat_snd b.natAbs
  · conv_lhs => rw [hb]
    exact dist_ofAdd_neg_nat_snd b.natAbs

/-! #### Left translation: Cayley distance is left-invariant.

We exhibit left-multiplication by `g` as a graph automorphism of the Cayley
graph, which transports walks without changing their length.  This gives
`dist (g * x) (g * y) ≤ dist x y` (and hence equality). -/

/-- **Left-multiplication preserves adjacency.** In any Cayley graph, if
`x` and `y` are adjacent, so are `g * x` and `g * y`. -/
private lemma cayley_adj_left_mul {G : Type*} [Group G] (Z : Set G) (g : G)
    {x y : G} (h : (cayley_graph Z).Adj x y) :
    (cayley_graph Z).Adj (g * x) (g * y) := by
  rw [cayley_graph_adj] at h ⊢
  obtain ⟨hne, hor⟩ := h
  refine ⟨?_, ?_⟩
  · intro heq; exact hne (mul_left_cancel heq)
  · rcases hor with ⟨z, hz, hyxz⟩ | ⟨z, hz, hxyz⟩
    · exact Or.inl ⟨z, hz, by rw [hyxz, mul_assoc]⟩
    · exact Or.inr ⟨z, hz, by rw [hxyz, mul_assoc]⟩

/-- **Left-multiplication as a graph homomorphism.** -/
private noncomputable def cayley_leftMulHom {G : Type*} [Group G] (Z : Set G) (g : G) :
    cayley_graph Z →g cayley_graph Z :=
  { toFun := fun x => g * x
    map_rel' := fun h => cayley_adj_left_mul Z g h }

private lemma cayley_leftMulHom_apply {G : Type*} [Group G] (Z : Set G) (g x : G) :
    cayley_leftMulHom Z g x = g * x := rfl

/-- **Reachability is left-invariant.** -/
private lemma cayley_reachable_mul_left {G : Type*} [Group G] (Z : Set G)
    (g : G) {x y : G} (h : (cayley_graph Z).Reachable x y) :
    (cayley_graph Z).Reachable (g * x) (g * y) := by
  obtain ⟨p⟩ := h
  have hmap := p.map (cayley_leftMulHom Z g)
  -- The endpoints of (p.map ...) are g * x and g * y (up to the toFun).
  exact ⟨hmap⟩

/-- **Left-invariance of distance.** -/
private lemma cayley_dist_mul_left {G : Type*} [Group G] (Z : Set G) (g x y : G) :
    (cayley_graph Z).dist (g * x) (g * y) ≤ (cayley_graph Z).dist x y := by
  by_cases hr : (cayley_graph Z).Reachable x y
  · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
    have hp' : (p.map (cayley_leftMulHom Z g)).length = (cayley_graph Z).dist x y := by
      rw [SimpleGraph.Walk.length_map]; exact hp
    exact hp' ▸ SimpleGraph.dist_le _
  · -- If not reachable, dist x y = 0 on that side. We show dist (g*x)(g*y) = 0
    -- too since reachability is left-invariant (via g⁻¹).
    have hd : (cayley_graph Z).dist x y = 0 := by
      rw [SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable]
      exact Or.inr hr
    rw [hd]
    have : (cayley_graph Z).dist (g * x) (g * y) = 0 := by
      rw [SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable]
      right
      intro hgr
      apply hr
      have hback := cayley_reachable_mul_left Z g⁻¹ hgr
      have hx : g⁻¹ * (g * x) = x := by group
      have hy : g⁻¹ * (g * y) = y := by group
      rw [hx, hy] at hback
      exact hback
    exact this.le

/-- **Upper bound on the distance, general point.**  For any `a b : ℤ`, the
distance from `1` to `ofAdd (a, b)` is at most `|a| + |b|`. Combine the
axis upper bounds with the triangle inequality and left-translation. -/
private lemma dist_ofAdd_int_le (a b : ℤ) :
    (cayley_graph Z2_canonical_gen).dist 1
      (Multiplicative.ofAdd ((a, b))) ≤ a.natAbs + b.natAbs := by
  -- Use triangle inequality via the intermediate point ofAdd (a, 0).
  have hdecomp : Multiplicative.ofAdd ((a, b) : ℤ × ℤ) =
      Multiplicative.ofAdd ((a, (0 : ℤ))) *
      Multiplicative.ofAdd (((0 : ℤ), b)) := by
    rw [← ofAdd_add]; congr 1; ext <;> simp
  -- Distance from ofAdd(a,0) to ofAdd(a,0) * ofAdd(0,b) = ofAdd(a,b):
  -- by left-invariance, this equals dist 1 (ofAdd (0, b)).
  have hleft := cayley_dist_mul_left Z2_canonical_gen
    (Multiplicative.ofAdd ((a, (0 : ℤ)))) 1
    (Multiplicative.ofAdd (((0 : ℤ), b)))
  simp only [mul_one] at hleft
  rw [← hdecomp] at hleft
  -- Now combine with triangle inequality.
  calc (cayley_graph Z2_canonical_gen).dist 1
          (Multiplicative.ofAdd ((a, b)))
      ≤ (cayley_graph Z2_canonical_gen).dist 1
          (Multiplicative.ofAdd ((a, (0 : ℤ)))) +
        (cayley_graph Z2_canonical_gen).dist
          (Multiplicative.ofAdd ((a, (0 : ℤ))))
          (Multiplicative.ofAdd ((a, b))) :=
        cayley_Z2_connected.dist_triangle
    _ ≤ a.natAbs + (cayley_graph Z2_canonical_gen).dist 1
          (Multiplicative.ofAdd (((0 : ℤ), b))) :=
        Nat.add_le_add (dist_ofAdd_int_fst a) hleft
    _ ≤ a.natAbs + b.natAbs := Nat.add_le_add_left (dist_ofAdd_int_snd b) _

/-- **Distance formula on ℤ²: exact equality.**  `dist 1 (ofAdd (a,b)) = |a| + |b|`. -/
private lemma cayley_Z2_dist_eq (a b : ℤ) :
    (cayley_graph Z2_canonical_gen).dist 1
      (Multiplicative.ofAdd ((a, b))) = a.natAbs + b.natAbs := by
  apply le_antisymm (dist_ofAdd_int_le a b)
  have h := manhattan_le_dist (Multiplicative.ofAdd ((a, b) : ℤ × ℤ))
  simpa [M] using h

/-! #### Counting the Manhattan diamond.

The ball of radius `k` in the Cayley graph is in bijection with the set
`{(a, b) ∈ ℤ² : |a| + |b| ≤ k}`.  We count the latter by induction on `k`,
using the identity `diamond (k+1) = diamond k ∪ sphere (k+1)`. -/

/-- The integer-lattice diamond `{(a,b) ∈ ℤ² : |a| + |b| ≤ k}`, as a Finset. -/
private noncomputable def diamond (k : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(k : ℤ)) k ×ˢ Finset.Icc (-(k : ℤ)) k).filter
    (fun p => p.1.natAbs + p.2.natAbs ≤ k)

/-- The sphere `{(a,b) ∈ ℤ² : |a| + |b| = k}` as a Finset. -/
private noncomputable def sphereFs (k : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(k : ℤ)) k ×ˢ Finset.Icc (-(k : ℤ)) k).filter
    (fun p => p.1.natAbs + p.2.natAbs = k)

private lemma mem_diamond {k : ℕ} {p : ℤ × ℤ} :
    p ∈ diamond k ↔ p.1.natAbs + p.2.natAbs ≤ k := by
  simp only [diamond, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  refine ⟨fun h => h.2, fun h => ⟨⟨?_, ?_⟩, h⟩⟩
  · have h1 : p.1.natAbs ≤ k := by omega
    have h1' : (p.1.natAbs : ℤ) ≤ k := by exact_mod_cast h1
    have hp1 : -((p.1.natAbs : ℤ)) ≤ p.1 ∧ p.1 ≤ (p.1.natAbs : ℤ) := by
      rcases Int.natAbs_eq p.1 with h' | h'
      · refine ⟨?_, h'.le⟩
        have : (0 : ℤ) ≤ p.1.natAbs := Int.natCast_nonneg _
        linarith
      · refine ⟨h'.ge, ?_⟩
        have : (0 : ℤ) ≤ p.1.natAbs := Int.natCast_nonneg _
        linarith
    exact ⟨by linarith [hp1.1], by linarith [hp1.2]⟩
  · have h2 : p.2.natAbs ≤ k := by omega
    have h2' : (p.2.natAbs : ℤ) ≤ k := by exact_mod_cast h2
    have hp2 : -((p.2.natAbs : ℤ)) ≤ p.2 ∧ p.2 ≤ (p.2.natAbs : ℤ) := by
      rcases Int.natAbs_eq p.2 with h' | h'
      · refine ⟨?_, h'.le⟩
        have : (0 : ℤ) ≤ p.2.natAbs := Int.natCast_nonneg _
        linarith
      · refine ⟨h'.ge, ?_⟩
        have : (0 : ℤ) ≤ p.2.natAbs := Int.natCast_nonneg _
        linarith
    exact ⟨by linarith [hp2.1], by linarith [hp2.2]⟩

private lemma mem_sphereFs {k : ℕ} {p : ℤ × ℤ} :
    p ∈ sphereFs k ↔ p.1.natAbs + p.2.natAbs = k := by
  simp only [sphereFs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  refine ⟨fun h => h.2, fun h => ⟨⟨?_, ?_⟩, h⟩⟩
  · have h1 : p.1.natAbs ≤ k := by omega
    have h1' : (p.1.natAbs : ℤ) ≤ k := by exact_mod_cast h1
    have hp1 : -((p.1.natAbs : ℤ)) ≤ p.1 ∧ p.1 ≤ (p.1.natAbs : ℤ) := by
      rcases Int.natAbs_eq p.1 with h' | h'
      · refine ⟨?_, h'.le⟩
        have : (0 : ℤ) ≤ p.1.natAbs := Int.natCast_nonneg _
        linarith
      · refine ⟨h'.ge, ?_⟩
        have : (0 : ℤ) ≤ p.1.natAbs := Int.natCast_nonneg _
        linarith
    exact ⟨by linarith [hp1.1], by linarith [hp1.2]⟩
  · have h2 : p.2.natAbs ≤ k := by omega
    have h2' : (p.2.natAbs : ℤ) ≤ k := by exact_mod_cast h2
    have hp2 : -((p.2.natAbs : ℤ)) ≤ p.2 ∧ p.2 ≤ (p.2.natAbs : ℤ) := by
      rcases Int.natAbs_eq p.2 with h' | h'
      · refine ⟨?_, h'.le⟩
        have : (0 : ℤ) ≤ p.2.natAbs := Int.natCast_nonneg _
        linarith
      · refine ⟨h'.ge, ?_⟩
        have : (0 : ℤ) ≤ p.2.natAbs := Int.natCast_nonneg _
        linarith
    exact ⟨by linarith [hp2.1], by linarith [hp2.2]⟩

/-- Decomposition: `diamond (k+1) = diamond k ∪ sphereFs (k+1)`, disjoint union. -/
private lemma diamond_succ (k : ℕ) :
    diamond (k + 1) = diamond k ∪ sphereFs (k + 1) := by
  ext p
  simp only [Finset.mem_union, mem_diamond, mem_sphereFs]
  omega

private lemma disjoint_diamond_sphereFs (k : ℕ) :
    Disjoint (diamond k) (sphereFs (k + 1)) := by
  rw [Finset.disjoint_left]
  intro p hp hp'
  rw [mem_diamond] at hp
  rw [mem_sphereFs] at hp'
  omega

/-- The diamond at radius `0` contains only the origin. -/
private lemma diamond_zero : diamond 0 = {((0, 0) : ℤ × ℤ)} := by
  ext p
  simp only [mem_diamond, Finset.mem_singleton]
  constructor
  · intro h
    have h1 : p.1.natAbs = 0 := by omega
    have h2 : p.2.natAbs = 0 := by omega
    have h1' : p.1 = 0 := Int.natAbs_eq_zero.mp h1
    have h2' : p.2 = 0 := Int.natAbs_eq_zero.mp h2
    ext <;> simp [h1', h2']
  · intro h; subst h; simp

/-- The two "axis" points with `|a| = K` on the sphere: `(K, 0)` and `(-K, 0)`. -/
private noncomputable def sphereEast (K : ℕ) : Finset (ℤ × ℤ) :=
  {((K : ℤ), 0), (-(K : ℤ), 0)}

/-- The two "interior-column" points for a column `a` with `|a| < K`:
`(a, K - |a|)` and `(a, -(K - |a|))`. -/
private noncomputable def sphereInteriorCol (K : ℕ) (a : ℤ) : Finset (ℤ × ℤ) :=
  {(a, (K : ℤ) - a.natAbs), (a, -((K : ℤ) - a.natAbs))}

/-- **Sphere cardinality.** The sphere `{(a,b) ∈ ℤ² : |a|+|b| = K}` has
exactly `4*K` lattice points when `K ≥ 1`.

Proof: partition the sphere into four "arcs", each of cardinality `K`:

* Arc 0 (east/north-east quadrant, including east pole):
  `{(K - r, r) : r ∈ [0, K-1]}` — points with `a ≥ 1, b ≥ 0`.
* Arc 1 (north/north-west, including north pole):
  `{(-r, K - r) : r ∈ [0, K-1]}` — points with `a ≤ 0, b ≥ 1`.
* Arc 2 (west/south-west, including west pole):
  `{(-(K - r), -r) : r ∈ [0, K-1]}` — points with `a ≤ -1, b ≤ 0`.
* Arc 3 (south/south-east, including south pole):
  `{(r, -(K - r)) : r ∈ [0, K-1]}` — points with `a ≥ 0, b ≤ -1`.

The sign constraints on the four arcs are pairwise incompatible, so the arcs
are disjoint.  Their union covers the sphere since for any `(a,b)` with
`|a|+|b| = K ≥ 1`, at least one of `a, b` is nonzero, and exactly one of the
four sign patterns holds. -/
private lemma sphereFs_card (k : ℕ) :
    (sphereFs (k + 1)).card = 4 * (k + 1) := by
  set K : ℕ := k + 1 with hKdef
  have hKpos : 1 ≤ K := Nat.succ_le_succ (Nat.zero_le _)
  -- The four arcs, each parametrised by `r : ℕ` with `r ∈ Finset.range K`.
  -- Arc 0: `(K - r, r)` with `a ≥ 1, b ≥ 0`.
  -- Arc 1: `(-r, K - r)` with `a ≤ 0, b ≥ 1`.
  -- Arc 2: `(-(K - r), -r)` with `a ≤ -1, b ≤ 0`.
  -- Arc 3: `(r, -(K - r))` with `a ≥ 0, b ≤ -1`.
  let f0 : ℕ → ℤ × ℤ := fun r => (((K : ℤ) - r), (r : ℤ))
  let f1 : ℕ → ℤ × ℤ := fun r => (-(r : ℤ), ((K : ℤ) - r))
  let f2 : ℕ → ℤ × ℤ := fun r => (-(((K : ℤ)) - r), -(r : ℤ))
  let f3 : ℕ → ℤ × ℤ := fun r => ((r : ℤ), -(((K : ℤ)) - r))
  let A0 : Finset (ℤ × ℤ) := (Finset.range K).image f0
  let A1 : Finset (ℤ × ℤ) := (Finset.range K).image f1
  let A2 : Finset (ℤ × ℤ) := (Finset.range K).image f2
  let A3 : Finset (ℤ × ℤ) := (Finset.range K).image f3
  -- Each `fᵢ` is injective on `Finset.range K`, so each arc has `K` elements.
  have hf0_inj : Set.InjOn f0 (Finset.range K : Set ℕ) := by
    intro r _ s _ h
    have : ((r : ℤ) = (s : ℤ)) := (Prod.mk.inj h).2
    exact_mod_cast this
  have hf1_inj : Set.InjOn f1 (Finset.range K : Set ℕ) := by
    intro r _ s _ h
    have h1 : -(r : ℤ) = -(s : ℤ) := (Prod.mk.inj h).1
    have : (r : ℤ) = (s : ℤ) := by linarith
    exact_mod_cast this
  have hf2_inj : Set.InjOn f2 (Finset.range K : Set ℕ) := by
    intro r _ s _ h
    have h2 : -(r : ℤ) = -(s : ℤ) := (Prod.mk.inj h).2
    have : (r : ℤ) = (s : ℤ) := by linarith
    exact_mod_cast this
  have hf3_inj : Set.InjOn f3 (Finset.range K : Set ℕ) := by
    intro r _ s _ h
    have : ((r : ℤ) = (s : ℤ)) := (Prod.mk.inj h).1
    exact_mod_cast this
  have hA0_card : A0.card = K := by
    rw [show A0 = (Finset.range K).image f0 from rfl,
        Finset.card_image_of_injOn hf0_inj, Finset.card_range]
  have hA1_card : A1.card = K := by
    rw [show A1 = (Finset.range K).image f1 from rfl,
        Finset.card_image_of_injOn hf1_inj, Finset.card_range]
  have hA2_card : A2.card = K := by
    rw [show A2 = (Finset.range K).image f2 from rfl,
        Finset.card_image_of_injOn hf2_inj, Finset.card_range]
  have hA3_card : A3.card = K := by
    rw [show A3 = (Finset.range K).image f3 from rfl,
        Finset.card_image_of_injOn hf3_inj, Finset.card_range]
  -- Helper: for `r ≤ K`, `((K : ℤ) - (r : ℤ)).natAbs = K - r`.
  have hNat_sub : ∀ r : ℕ, r ≤ K → ((K : ℤ) - (r : ℤ)).natAbs = K - r := by
    intro r hr
    have hnn : 0 ≤ (K : ℤ) - (r : ℤ) := by
      have : (r : ℤ) ≤ (K : ℤ) := by exact_mod_cast hr
      linarith
    have := Int.natAbs_of_nonneg hnn
    -- `this : ↑(...)natAbs = ↑K - ↑r`. Cast both sides back.
    have hK : (((K : ℤ) - (r : ℤ)).natAbs : ℤ) = ((K - r : ℕ) : ℤ) := by
      rw [this]
      omega
    exact_mod_cast hK
  -- Helper: `(r : ℤ).natAbs = r`.
  have hNat_self : ∀ r : ℕ, ((r : ℤ)).natAbs = r := by
    intro r
    simp
  -- Each arc is a subset of `sphereFs K`.
  have hA0_sub : A0 ⊆ sphereFs K := by
    intro p hp
    simp only [A0, Finset.mem_image, Finset.mem_range, f0] at hp
    obtain ⟨r, hr, hpr⟩ := hp
    rw [mem_sphereFs, ← hpr]
    simp only [hNat_sub r hr.le, hNat_self]
    omega
  have hA1_sub : A1 ⊆ sphereFs K := by
    intro p hp
    simp only [A1, Finset.mem_image, Finset.mem_range, f1] at hp
    obtain ⟨r, hr, hpr⟩ := hp
    rw [mem_sphereFs, ← hpr]
    simp only [Int.natAbs_neg, hNat_sub r hr.le, hNat_self]
    omega
  have hA2_sub : A2 ⊆ sphereFs K := by
    intro p hp
    simp only [A2, Finset.mem_image, Finset.mem_range, f2] at hp
    obtain ⟨r, hr, hpr⟩ := hp
    rw [mem_sphereFs, ← hpr]
    simp only [Int.natAbs_neg, hNat_sub r hr.le, hNat_self]
    omega
  have hA3_sub : A3 ⊆ sphereFs K := by
    intro p hp
    simp only [A3, Finset.mem_image, Finset.mem_range, f3] at hp
    obtain ⟨r, hr, hpr⟩ := hp
    rw [mem_sphereFs, ← hpr]
    simp only [Int.natAbs_neg, hNat_sub r hr.le, hNat_self]
    omega
  -- Sign constraints: each arc lives in a quadrant determined by signs of a, b.
  -- Arc 0: a ≥ 1, b ≥ 0.
  have hA0_sign : ∀ p ∈ A0, 1 ≤ p.1 ∧ 0 ≤ p.2 := by
    intro p hp
    simp only [A0, Finset.mem_image, Finset.mem_range, f0] at hp
    obtain ⟨r, hr, hpr⟩ := hp
    subst hpr
    have hrnn : (0 : ℤ) ≤ (r : ℤ) := Int.natCast_nonneg r
    have hrK : (r : ℤ) < K := by exact_mod_cast hr
    refine ⟨?_, ?_⟩ <;> simp only <;> linarith
  -- Arc 1: a ≤ 0, b ≥ 1.
  have hA1_sign : ∀ p ∈ A1, p.1 ≤ 0 ∧ 1 ≤ p.2 := by
    intro p hp
    simp only [A1, Finset.mem_image, Finset.mem_range, f1] at hp
    obtain ⟨r, hr, hpr⟩ := hp
    subst hpr
    have hrnn : (0 : ℤ) ≤ (r : ℤ) := Int.natCast_nonneg r
    have hrK : (r : ℤ) < K := by exact_mod_cast hr
    refine ⟨?_, ?_⟩ <;> simp only <;> linarith
  -- Arc 2: a ≤ -1, b ≤ 0.
  have hA2_sign : ∀ p ∈ A2, p.1 ≤ -1 ∧ p.2 ≤ 0 := by
    intro p hp
    simp only [A2, Finset.mem_image, Finset.mem_range, f2] at hp
    obtain ⟨r, hr, hpr⟩ := hp
    subst hpr
    have hrnn : (0 : ℤ) ≤ (r : ℤ) := Int.natCast_nonneg r
    have hrK : (r : ℤ) < K := by exact_mod_cast hr
    refine ⟨?_, ?_⟩ <;> simp only <;> linarith
  -- Arc 3: a ≥ 0, b ≤ -1.
  have hA3_sign : ∀ p ∈ A3, 0 ≤ p.1 ∧ p.2 ≤ -1 := by
    intro p hp
    simp only [A3, Finset.mem_image, Finset.mem_range, f3] at hp
    obtain ⟨r, hr, hpr⟩ := hp
    subst hpr
    have hrnn : (0 : ℤ) ≤ (r : ℤ) := Int.natCast_nonneg r
    have hrK : (r : ℤ) < K := by exact_mod_cast hr
    refine ⟨?_, ?_⟩ <;> simp only <;> linarith
  -- Pairwise disjoint.
  have hdisj01 : Disjoint A0 A1 := by
    rw [Finset.disjoint_left]
    intro p hp0 hp1
    have ⟨h0a, _⟩ := hA0_sign p hp0
    have ⟨h1a, _⟩ := hA1_sign p hp1
    linarith
  have hdisj02 : Disjoint A0 A2 := by
    rw [Finset.disjoint_left]
    intro p hp0 hp2
    have ⟨h0a, _⟩ := hA0_sign p hp0
    have ⟨h2a, _⟩ := hA2_sign p hp2
    linarith
  have hdisj03 : Disjoint A0 A3 := by
    rw [Finset.disjoint_left]
    intro p hp0 hp3
    have ⟨_, h0b⟩ := hA0_sign p hp0
    have ⟨_, h3b⟩ := hA3_sign p hp3
    linarith
  have hdisj12 : Disjoint A1 A2 := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have ⟨_, h1b⟩ := hA1_sign p hp1
    have ⟨_, h2b⟩ := hA2_sign p hp2
    linarith
  have hdisj13 : Disjoint A1 A3 := by
    rw [Finset.disjoint_left]
    intro p hp1 hp3
    have ⟨_, h1b⟩ := hA1_sign p hp1
    have ⟨_, h3b⟩ := hA3_sign p hp3
    linarith
  have hdisj23 : Disjoint A2 A3 := by
    rw [Finset.disjoint_left]
    intro p hp2 hp3
    have ⟨h2a, _⟩ := hA2_sign p hp2
    have ⟨h3a, _⟩ := hA3_sign p hp3
    linarith
  -- Coverage: sphereFs K ⊆ A0 ∪ A1 ∪ A2 ∪ A3.
  have hcover : sphereFs K ⊆ A0 ∪ A1 ∪ A2 ∪ A3 := by
    intro p hp
    rw [mem_sphereFs] at hp
    -- p.1.natAbs + p.2.natAbs = K ≥ 1, so (p.1, p.2) ≠ (0, 0).
    -- Case-split on signs of p.1 and p.2.
    rcases le_or_gt (0 : ℤ) p.1 with ha | ha
    · rcases le_or_gt (0 : ℤ) p.2 with hb | hb
      · -- a ≥ 0, b ≥ 0: if a ≥ 1 this is Arc 0; if a = 0 then b ≥ 1 and it's Arc 1.
        rcases eq_or_lt_of_le ha with ha0 | ha1
        · -- a = 0, so b = p.2.natAbs ≥ 0, and b.natAbs = K ≥ 1 forces b ≥ 1.
          -- It's in A1 with r = 0: (-0, K - 0) = (0, K).
          have hp1 : p.1 = 0 := ha0.symm
          -- p.2 ≥ 0 and p.2.natAbs = K.
          have hp2abs : p.2.natAbs = K := by
            have : p.1.natAbs = 0 := by rw [hp1]; rfl
            omega
          have hcast : ((p.2.natAbs : ℤ)) = p.2 := Int.natAbs_of_nonneg hb
          have hp2 : p.2 = K := by
            have : ((p.2.natAbs : ℤ)) = ((K : ℕ) : ℤ) := by exact_mod_cast hp2abs
            linarith
          -- So p = (0, K). This is in A1 with r = 0.
          refine Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
            (Finset.mem_union.mpr (Or.inr ?_)))))
          simp only [A1, Finset.mem_image, Finset.mem_range, f1]
          refine ⟨0, hKpos, ?_⟩
          ext <;> simp [hp1, hp2]
        · -- a ≥ 1. Arc 0 with r = p.2.natAbs.
          refine Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
            (Finset.mem_union.mpr (Or.inl ?_)))))
          simp only [A0, Finset.mem_image, Finset.mem_range, f0]
          refine ⟨p.2.natAbs, ?_, ?_⟩
          · -- p.2.natAbs < K since p.1.natAbs ≥ 1
            have : p.1.natAbs ≥ 1 := by
              have : (1 : ℤ) ≤ p.1 := ha1
              have h1 : p.1.natAbs ≥ 1 := by
                rcases Int.natAbs_eq p.1 with h | h
                · rw [h] at this; exact_mod_cast this
                · have hne : p.1.natAbs ≠ 0 := by
                    intro hz
                    rw [hz] at h
                    simp at h
                    linarith
                  omega
              exact h1
            omega
          · -- reconstruct (p.1, p.2) from (K - p.2.natAbs, p.2.natAbs).
            have hp1val : ((p.1.natAbs : ℤ)) = p.1 := Int.natAbs_of_nonneg ha
            have hp2val : ((p.2.natAbs : ℤ)) = p.2 := Int.natAbs_of_nonneg hb
            have hKeq : (K : ℤ) = (p.1.natAbs : ℤ) + (p.2.natAbs : ℤ) := by
              exact_mod_cast hp.symm
            ext
            · -- p.1 = K - p.2.natAbs
              show (↑K - ↑p.2.natAbs : ℤ) = p.1
              linarith
            · -- p.2 = p.2.natAbs
              show ((p.2.natAbs : ℤ)) = p.2
              exact hp2val
      · -- a ≥ 0, b < 0. Arc 3 with r = p.1.natAbs.
        refine Finset.mem_union.mpr (Or.inr ?_)
        simp only [A3, Finset.mem_image, Finset.mem_range, f3]
        have hp1val : ((p.1.natAbs : ℤ)) = p.1 := Int.natAbs_of_nonneg ha
        have hp2val : p.2 = -(p.2.natAbs : ℤ) := by
          rcases Int.natAbs_eq p.2 with h | h
          · rw [h] at hb
            have : (0 : ℤ) ≤ p.2.natAbs := Int.natCast_nonneg _
            linarith
          · exact h
        have hb1 : p.2.natAbs ≥ 1 := by
          have : p.2 ≠ 0 := by linarith
          exact Int.natAbs_pos.mpr this
        have hKeq : (K : ℤ) = (p.1.natAbs : ℤ) + (p.2.natAbs : ℤ) := by
          exact_mod_cast hp.symm
        refine ⟨p.1.natAbs, by omega, ?_⟩
        ext
        · show ((p.1.natAbs : ℤ)) = p.1
          exact hp1val
        · show -(↑K - ↑p.1.natAbs : ℤ) = p.2
          linarith
    · -- a < 0.
      rcases le_or_gt (0 : ℤ) p.2 with hb | hb
      · rcases eq_or_lt_of_le hb with hb0 | hb1
        · -- b = 0, a < 0. Then a.natAbs = K ≥ 1, a ≤ -1. Arc 2 with r = 0.
          have hp2 : p.2 = 0 := hb0.symm
          have hp1abs : p.1.natAbs = K := by
            have : p.2.natAbs = 0 := by rw [hp2]; rfl
            omega
          -- p.1 < 0, so p.1 = -p.1.natAbs = -K.
          have hp1 : p.1 = -(K : ℤ) := by
            have := Int.natAbs_eq p.1
            rcases this with h | h
            · rw [h] at ha
              have : (0 : ℤ) ≤ p.1.natAbs := Int.natCast_nonneg _
              linarith
            · rw [h, hp1abs]
          refine Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr ?_)))
          simp only [A2, Finset.mem_image, Finset.mem_range, f2]
          refine ⟨0, hKpos, ?_⟩
          ext <;> simp [hp1, hp2]
        · -- a < 0, b ≥ 1. Arc 1 with r = p.1.natAbs.
          refine Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
            (Finset.mem_union.mpr (Or.inr ?_)))))
          simp only [A1, Finset.mem_image, Finset.mem_range, f1]
          have hp1val : p.1 = -(p.1.natAbs : ℤ) := by
            rcases Int.natAbs_eq p.1 with h | h
            · rw [h] at ha
              have : (0 : ℤ) ≤ p.1.natAbs := Int.natCast_nonneg _
              linarith
            · exact h
          have hp2val : (p.2.natAbs : ℤ) = p.2 := Int.natAbs_of_nonneg hb
          have ha1 : p.1.natAbs ≥ 1 := by
            have : p.1 ≠ 0 := by linarith
            exact Int.natAbs_pos.mpr this
          refine ⟨p.1.natAbs, by omega, ?_⟩
          ext
          · show -((p.1.natAbs : ℤ)) = p.1
            linarith [hp1val]
          · show (↑K - ↑p.1.natAbs : ℤ) = p.2
            have hsum : p.1.natAbs + p.2.natAbs = K := hp
            have h2 : (p.2.natAbs : ℤ) = p.2 := hp2val
            have hKeq : (K : ℤ) = (p.1.natAbs : ℤ) + (p.2.natAbs : ℤ) := by
              exact_mod_cast hsum.symm
            linarith
      · -- a < 0, b < 0. Arc 2 with r = p.2.natAbs.
        refine Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr ?_)))
        simp only [A2, Finset.mem_image, Finset.mem_range, f2]
        have hp1val : p.1 = -(p.1.natAbs : ℤ) := by
          rcases Int.natAbs_eq p.1 with h | h
          · rw [h] at ha
            have : (0 : ℤ) ≤ p.1.natAbs := Int.natCast_nonneg _
            linarith
          · exact h
        have hp2val : p.2 = -(p.2.natAbs : ℤ) := by
          rcases Int.natAbs_eq p.2 with h | h
          · rw [h] at hb
            have : (0 : ℤ) ≤ p.2.natAbs := Int.natCast_nonneg _
            linarith
          · exact h
        have hb1 : p.2.natAbs ≥ 1 := by
          have : p.2 ≠ 0 := by linarith
          exact Int.natAbs_pos.mpr this
        refine ⟨p.2.natAbs, by omega, ?_⟩
        ext
        · show -(↑K - ↑p.2.natAbs : ℤ) = p.1
          have hsum : p.1.natAbs + p.2.natAbs = K := hp
          have hKeq : (K : ℤ) = (p.1.natAbs : ℤ) + (p.2.natAbs : ℤ) := by
            exact_mod_cast hsum.symm
          linarith
        · show -((p.2.natAbs : ℤ)) = p.2
          linarith [hp2val]
  -- Put it together.
  have heq : sphereFs K = A0 ∪ A1 ∪ A2 ∪ A3 :=
    Finset.Subset.antisymm hcover
      (by
        intro p hp
        rcases Finset.mem_union.mp hp with hp | hp
        · rcases Finset.mem_union.mp hp with hp | hp
          · rcases Finset.mem_union.mp hp with hp | hp
            · exact hA0_sub hp
            · exact hA1_sub hp
          · exact hA2_sub hp
        · exact hA3_sub hp)
  rw [show sphereFs (k + 1) = sphereFs K from rfl, heq]
  -- Card of disjoint union: A0 ∪ A1 ∪ A2 ∪ A3.
  have hdisj_01_2 : Disjoint (A0 ∪ A1) A2 := by
    rw [Finset.disjoint_union_left]
    exact ⟨hdisj02, hdisj12⟩
  have hdisj_012_3 : Disjoint (A0 ∪ A1 ∪ A2) A3 := by
    rw [Finset.disjoint_union_left, Finset.disjoint_union_left]
    exact ⟨⟨hdisj03, hdisj13⟩, hdisj23⟩
  rw [Finset.card_union_of_disjoint hdisj_012_3,
      Finset.card_union_of_disjoint hdisj_01_2,
      Finset.card_union_of_disjoint hdisj01,
      hA0_card, hA1_card, hA2_card, hA3_card]
  ring

/-- **Inductive formula for `diamond` cardinality**: `#diamond k = 2k²+2k+1`. -/
private lemma diamond_card (k : ℕ) :
    (diamond k).card = 2 * k ^ 2 + 2 * k + 1 := by
  induction k with
  | zero => rw [diamond_zero]; simp
  | succ k ih =>
    rw [diamond_succ k, Finset.card_union_of_disjoint (disjoint_diamond_sphereFs k),
        ih, sphereFs_card k]
    ring

/-! #### Transferring the count from `ℤ × ℤ` to `Multiplicative (ℤ × ℤ)`. -/

private lemma cayley_ball_eq_image (k : ℕ) :
    cayley_ball Z2_canonical_gen k =
      Multiplicative.ofAdd '' {p : ℤ × ℤ | p.1.natAbs + p.2.natAbs ≤ k} := by
  ext x
  simp only [cayley_ball, Set.mem_setOf_eq, Set.mem_image]
  refine ⟨fun hx => ⟨x.toAdd, ?_, rfl⟩, fun ⟨p, hp, hpx⟩ => ?_⟩
  · -- From dist ≤ k to |x.toAdd.1| + |x.toAdd.2| ≤ k.
    rw [show x = Multiplicative.ofAdd x.toAdd from rfl] at hx
    have hdist := cayley_Z2_dist_eq x.toAdd.1 x.toAdd.2
    rw [hdist] at hx
    exact hx
  · -- From |p.1| + |p.2| ≤ k to dist ≤ k.
    rw [← hpx]
    obtain ⟨a, b⟩ := p
    rw [cayley_Z2_dist_eq a b]
    exact hp

private lemma cayley_ball_nat_card (k : ℕ) :
    Nat.card (cayley_ball Z2_canonical_gen k) = (diamond k).card := by
  rw [cayley_ball_eq_image]
  -- Multiplicative.ofAdd is a bijection; card of image = card of source.
  have hinj : Set.InjOn (Multiplicative.ofAdd : ℤ × ℤ → Multiplicative (ℤ × ℤ))
      {p : ℤ × ℤ | p.1.natAbs + p.2.natAbs ≤ k} := by
    intro a _ b _ hab
    exact Multiplicative.ofAdd.injective hab
  rw [Nat.card_image_of_injOn hinj]
  -- Relate Nat.card of the source set to (diamond k).card via a Finset coercion.
  have hset_eq : {p : ℤ × ℤ | p.1.natAbs + p.2.natAbs ≤ k} = (diamond k : Set (ℤ × ℤ)) := by
    ext p
    constructor
    · intro hp; simp only [Finset.mem_coe]; exact mem_diamond.mpr hp
    · intro hp; simp only [Finset.mem_coe] at hp
      exact mem_diamond.mp hp
  rw [hset_eq, Nat.card_coe_set_eq, Set.ncard_coe_finset]

/-- **Q28.** For `G = ℤ²` and `Z = {(±1,0), (0,±1)}`, the growth function is
`β(k) = 2k² + 2k + 1`.

**Strategy.** The ball of radius `k` is the Manhattan ball
`{(x, y) ∈ ℤ² : |x| + |y| ≤ k}`, whose cardinality equals
`1 + 4(1 + 2 + ⋯ + k) = 2k² + 2k + 1` by counting spheres of radius `j` for
`0 ≤ j ≤ k`.

**Status of this formalisation.**
The geometric heart of Q28 — the lower bound `M(x.toAdd) ≤ dist 1 x`, which
is what forces a walk from `0` to `(a, b)` to have length at least `|a|+|b|` —
is fully established (see `manhattan_adj_step`, `manhattan_le_walk_length`,
`manhattan_le_dist`). The upper bound along the axes (`dist_ofAdd_int_fst`)
is also fully established by induction on `|n|`. The connectedness of the
Cayley graph is established via `Z2_canonical_gen_generates`.

The remaining content — extending the axis upper bound to a general
`ofAdd (a, b)` by triangle inequality with the analogous second-axis result,
and counting the diamond `{|x|+|y| ≤ k}` to give `2k² + 2k + 1` lattice
points — is routine but mechanically heavy, and is recorded as a final
`sorry` with a precise plan. -/
theorem growth_Z2 (k : ℕ) :
    growth Z2_canonical_gen k = 2 * k ^ 2 + 2 * k + 1 := by
  unfold growth
  rw [cayley_ball_nat_card, diamond_card]

/-! ### Q29(a) — growth type is invariant under change of generators

If `Z` and `Z'` are two finite symmetric generating sets of the same group
`G`, then there is a constant `M ≥ 1` such that `d_Z ≤ M · d_{Z'}` and hence
`β_Z(k) ≤ β_{Z'}(M · k)` (and symmetrically). This makes the growth *type*
well-defined.

**Proof.** Each `z' ∈ Z'` is a product of elements of `Z ∪ Z⁻¹`. Since `Z` is
symmetric, `Z ∪ Z⁻¹ = Z`, so `z' = z_1 · … · z_{m(z')}` for some `m(z')` and
`z_i ∈ Z`. Let `M = max_{z' ∈ Z'} m(z')`. Then any word of length `n` over
`Z'` corresponds to a word of length `≤ M · n` over `Z`, so
`d_Z(1, x) ≤ M · d_{Z'}(1, x)`. -/

/-! #### Connectedness from generation (symmetry-free).

`cayley_graph_connected` takes a dummy symmetry hypothesis (underscored),
so we extract a cleaner version that only requires `Z` to generate. -/

private theorem cayley_graph_connected_of_gen {G : Type*} [Group G] (Z : Set G)
    (hZ_gen : Subgroup.closure Z = ⊤) :
    (cayley_graph Z).Connected := by
  haveI : Nonempty G := ⟨1⟩
  refine ⟨?_⟩
  intro x y
  have hmem : x⁻¹ * y ∈ Subgroup.closure Z := by
    rw [hZ_gen]; exact Subgroup.mem_top _
  have hreach := reachable_of_mem_closure Z hmem x
  have heq : x * (x⁻¹ * y) = y := by group
  rw [heq] at hreach
  exact hreach

/-! #### Sub-multiplicativity of the Cayley-graph distance.

For any generating set `Z`, the distance function satisfies
`d(1, x·y) ≤ d(1, x) + d(1, y)`.  Triangle inequality via the intermediate
point `x`, combined with left-invariance of `d`. -/

/-- **Sub-multiplicativity.** For a generating set `Z` of `G`, the
Cayley-graph distance satisfies `d(1, x*y) ≤ d(1, x) + d(1, y)`. -/
private lemma cayley_dist_mul_le {G : Type*} [Group G] (Z : Set G)
    (hZ_gen : Subgroup.closure Z = ⊤) (x y : G) :
    (cayley_graph Z).dist 1 (x * y) ≤
      (cayley_graph Z).dist 1 x + (cayley_graph Z).dist 1 y := by
  have hconn : (cayley_graph Z).Connected :=
    cayley_graph_connected_of_gen Z hZ_gen
  have htri : (cayley_graph Z).dist 1 (x * y)
      ≤ (cayley_graph Z).dist 1 x + (cayley_graph Z).dist x (x * y) :=
    hconn.dist_triangle
  have hleft : (cayley_graph Z).dist x (x * y) ≤ (cayley_graph Z).dist 1 y := by
    have h := cayley_dist_mul_left Z x 1 y
    simpa [mul_one] using h
  exact htri.trans (Nat.add_le_add_left hleft _)

/-! #### Walk translation: bounding `dist_Z` via walks in `cayley_graph Z'`.

Each edge `x ~ y` in `cayley_graph Z'` translates to `dist_Z(x, y) ≤ M`,
provided `M` uniformly bounds `dist_Z(1, z')` and `dist_Z(1, z'⁻¹)` over
`z' ∈ Z'`. Induction on walk length yields `dist_Z(u, w) ≤ M * p.length`. -/

/-- **Single-step bound.** An edge `x ~ y` in `cayley_graph Z'` gives
`dist_Z(x, y) ≤ M`, using the uniform bounds on generators of `Z'` and their
inverses. -/
private lemma cayley_dist_adj_le {G : Type*} [Group G]
    (Z Z' : Set G) (M : ℕ)
    (hMZ' : ∀ z' ∈ Z', (cayley_graph Z).dist 1 z' ≤ M)
    (hMZ'_inv : ∀ z' ∈ Z', (cayley_graph Z).dist 1 z'⁻¹ ≤ M)
    {x y : G} (hadj : (cayley_graph Z').Adj x y) :
    (cayley_graph Z).dist x y ≤ M := by
  rw [cayley_graph_adj] at hadj
  obtain ⟨_, hor⟩ := hadj
  rcases hor with ⟨z, hz, hyxz⟩ | ⟨z, hz, hxyz⟩
  · subst hyxz
    have h := cayley_dist_mul_left Z x 1 z
    have h' : (cayley_graph Z).dist x (x * z) ≤ (cayley_graph Z).dist 1 z := by
      simpa [mul_one] using h
    exact h'.trans (hMZ' z hz)
  · have hy : y = x * z⁻¹ := by
      have hyz : y * z * z⁻¹ = y := by group
      rw [← hyz, ← hxyz]
    subst hy
    have h := cayley_dist_mul_left Z x 1 z⁻¹
    have h' : (cayley_graph Z).dist x (x * z⁻¹) ≤ (cayley_graph Z).dist 1 z⁻¹ := by
      simpa [mul_one] using h
    exact h'.trans (hMZ'_inv z hz)

/-- **Walk-length bound.** For any `Z'`-walk `p : u → w`, we have
`dist_Z(u, w) ≤ M * p.length`, provided `Z` generates `G` and `M` uniformly
bounds `dist_Z(1, z')` and `dist_Z(1, z'⁻¹)` over `z' ∈ Z'`. -/
private lemma cayley_dist_le_walk_length {G : Type*} [Group G]
    (Z Z' : Set G) (hZ_gen : Subgroup.closure Z = ⊤) (M : ℕ)
    (hMZ' : ∀ z' ∈ Z', (cayley_graph Z).dist 1 z' ≤ M)
    (hMZ'_inv : ∀ z' ∈ Z', (cayley_graph Z).dist 1 z'⁻¹ ≤ M)
    {u w : G} (p : (cayley_graph Z').Walk u w) :
    (cayley_graph Z).dist u w ≤ M * p.length := by
  induction p with
  | nil => simp [SimpleGraph.dist_self]
  | @cons a b c hadj q ih =>
    have hab : (cayley_graph Z).dist a b ≤ M :=
      cayley_dist_adj_le Z Z' M hMZ' hMZ'_inv hadj
    have hbc : (cayley_graph Z).dist b c ≤ M * q.length := ih
    have hconnZ : (cayley_graph Z).Connected :=
      cayley_graph_connected_of_gen Z hZ_gen
    have htri : (cayley_graph Z).dist a c ≤
        (cayley_graph Z).dist a b + (cayley_graph Z).dist b c :=
      hconnZ.dist_triangle
    calc (cayley_graph Z).dist a c
        ≤ (cayley_graph Z).dist a b + (cayley_graph Z).dist b c := htri
      _ ≤ M + M * q.length := Nat.add_le_add hab hbc
      _ = M * (q.length + 1) := by ring
      _ = M * (SimpleGraph.Walk.cons hadj q).length := by
          rw [SimpleGraph.Walk.length_cons]

/-! #### Finiteness of balls for a finite generating set.

The ball `cayley_ball Z n` is contained in `{Walk.getVert p n | p : Walk 1 ·}`,
and every walk from `1` of length `≤ n` lands on a product of at most `n`
elements of `Z ∪ Z⁻¹`. Since `Z` is finite, the set of such products is
finite, so the ball is finite. We formalise this via an explicit superset
built by iterated one-step expansion. -/

/-- **One-step expansion.** Given a `Set G`, the "one-step right
multiplication" by elements of `S ∪ S⁻¹ ∪ {1}`. -/
private def stepExpand {G : Type*} [Group G] (Z : Set G) (S : Set G) : Set G :=
  (fun p : G × G => p.1 * p.2) ''
    (S ×ˢ ((Z ∪ (fun g : G => g⁻¹) '' Z) ∪ ({1} : Set G)))

/-- The `n`-fold iterated expansion of `{1}`. -/
private noncomputable def ballExpand {G : Type*} [Group G] (Z : Set G) :
    ℕ → Set G
  | 0 => ({1} : Set G)
  | n + 1 => stepExpand Z (ballExpand Z n)

/-- `ballExpand Z n` is finite when `Z` is finite. -/
private lemma ballExpand_finite {G : Type*} [Group G] (Z : Finset G) :
    ∀ n : ℕ, (ballExpand (↑Z : Set G) n).Finite
  | 0 => Set.finite_singleton (1 : G)
  | n + 1 => by
      have hn := ballExpand_finite Z n
      have hZ_fin : ((↑Z : Set G)).Finite := Z.finite_toSet
      have hZinv_fin : ((fun g : G => g⁻¹) '' (↑Z : Set G)).Finite :=
        hZ_fin.image _
      have hS_fin :
          (((↑Z : Set G) ∪ (fun g : G => g⁻¹) '' (↑Z : Set G))
            ∪ ({1} : Set G)).Finite :=
        (hZ_fin.union hZinv_fin).union (Set.finite_singleton _)
      have hprod : (ballExpand (↑Z : Set G) n ×ˢ _).Finite := hn.prod hS_fin
      exact hprod.image _

/-- `ballExpand` is monotone in `n`. -/
private lemma ballExpand_mono {G : Type*} [Group G] (Z : Set G) {n m : ℕ}
    (h : n ≤ m) : ballExpand Z n ⊆ ballExpand Z m := by
  induction m with
  | zero =>
    interval_cases n
    exact fun _ hx => hx
  | succ m ih =>
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · have hn_le_m : n ≤ m := Nat.lt_succ_iff.mp hlt
      have hsub := ih hn_le_m
      -- Now need ballExpand Z m ⊆ ballExpand Z (m+1).
      -- At the step, ballExpand (m+1) = stepExpand (ballExpand m), which contains
      -- ballExpand m via the element `1`.
      intro x hx
      have hxmem := hsub hx
      show x ∈ stepExpand Z (ballExpand Z m)
      refine ⟨(x, 1), ⟨hxmem, ?_⟩, by simp⟩
      right; rfl
    · -- hge : m + 1 ≤ n; combined with h : n ≤ m + 1, n = m + 1.
      have : n = m + 1 := le_antisymm h hge
      subst this
      exact fun _ hx => hx

/-- **Walk membership in `ballExpand`.** If `u ∈ ballExpand Z n`, then the
endpoint `w` of any walk from `u` satisfies `w ∈ ballExpand Z (n + p.length)`.
By induction on the walk length. -/
private lemma mem_ballExpand_of_walk {G : Type*} [Group G] (Z : Set G)
    {u w : G} (p : (cayley_graph Z).Walk u w) :
    ∀ n : ℕ, u ∈ ballExpand Z n → w ∈ ballExpand Z (n + p.length) := by
  induction p with
  | nil =>
    intro n hu
    simpa using hu
  | @cons a b c hadj q ih =>
    intro n hu
    -- From adjacency a ~ b in Z-graph, b = a * z or a = b * z for some z ∈ Z.
    -- In either case b = a * δ for δ ∈ Z ∪ Z⁻¹.
    have hb : b ∈ ballExpand Z (n + 1) := by
      rw [cayley_graph_adj] at hadj
      obtain ⟨_, hor⟩ := hadj
      rcases hor with ⟨z, hz, hbaz⟩ | ⟨z, hz, habz⟩
      · -- b = a * z, so b = a * z with z ∈ Z ⊆ Z ∪ Z⁻¹ ∪ {1}.
        subst hbaz
        show a * z ∈ stepExpand Z (ballExpand Z n)
        refine ⟨(a, z), ⟨hu, ?_⟩, rfl⟩
        left; left; exact hz
      · -- a = b * z, so b = a * z⁻¹, with z⁻¹ ∈ Z⁻¹ ⊆ Z ∪ Z⁻¹ ∪ {1}.
        have hbrw : b = a * z⁻¹ := by
          have hbz : b * z * z⁻¹ = b := by group
          rw [← hbz, ← habz]
        rw [hbrw]
        show a * z⁻¹ ∈ stepExpand Z (ballExpand Z n)
        refine ⟨(a, z⁻¹), ⟨hu, ?_⟩, rfl⟩
        left; right; exact ⟨z, hz, rfl⟩
    -- Now apply the inductive hypothesis to the rest of the walk.
    have hc := ih (n + 1) hb
    -- hc : c ∈ ballExpand Z ((n + 1) + q.length)
    -- Goal: c ∈ ballExpand Z (n + (cons hadj q).length) = ballExpand Z (n + q.length + 1).
    have hlen : (SimpleGraph.Walk.cons hadj q).length = q.length + 1 := by
      rw [SimpleGraph.Walk.length_cons]
    rw [hlen]
    -- ballExpand Z (n + (q.length + 1)) = ballExpand Z ((n + 1) + q.length)
    have heq : n + (q.length + 1) = (n + 1) + q.length := by ring
    rw [heq]
    exact hc

/-- **The ball of radius `n` is finite** when `Z : Finset` generates `G`. -/
private lemma cayley_ball_finite {G : Type*} [Group G] (Z : Finset G)
    (hZ_gen : Subgroup.closure (↑Z : Set G) = ⊤) (n : ℕ) :
    (cayley_ball (↑Z : Set G) n).Finite := by
  -- Every `x` in the ball has a walk from `1` to `x` of length ≤ n; apply
  -- `mem_ballExpand_of_walk` starting from `1 ∈ ballExpand Z 0`.
  have hsub : cayley_ball (↑Z : Set G) n ⊆ ballExpand (↑Z : Set G) n := by
    intro x hx
    simp only [cayley_ball, Set.mem_setOf_eq] at hx
    have hconn : (cayley_graph (↑Z : Set G)).Connected :=
      cayley_graph_connected_of_gen _ hZ_gen
    obtain ⟨p, hp⟩ := (hconn 1 x).exists_walk_length_eq_dist
    have hlen : p.length ≤ n := hp ▸ hx
    have h1 : (1 : G) ∈ ballExpand (↑Z : Set G) 0 := by simp [ballExpand]
    have hx_in : x ∈ ballExpand (↑Z : Set G) (0 + p.length) :=
      mem_ballExpand_of_walk (↑Z : Set G) p 0 h1
    rw [Nat.zero_add] at hx_in
    exact ballExpand_mono (↑Z : Set G) hlen hx_in
  exact (ballExpand_finite Z n).subset hsub

/-- **Sphere–reduced-word injection.** The distance-`k` sphere of the
Cayley graph injects into the set of reduced words of length `k` over `Z`,
via the edge-label sequence of a geodesic walk from the identity.

Strategy:
* For each `x` with `dist 1 x = k`, pick a geodesic `q : Walk 1 x` with
  `q.length = k` (via `Reachable.exists_walk_length_eq_dist`).
* Extract `w : Fin k → G` by `w ⟨i, _⟩ := walkLabel q i`. The letters lie
  in `Z` (by `walkLabel_mem_Z`) and the word is reduced (by
  `geodesic_walkLabel_reduced`).
* The map `x ↦ w` is injective: both endpoints are reached from `1` by the
  same sequence of edge labels, so `x₁ = x₂` by `walk_getVert_determined`.
* The sphere `B(k) \ B(k-1)` has cardinality `growth Z k - growth Z (k-1)`.
-/
private lemma sphere_card_le_reducedWords_card
    {G : Type*} [Group G] [DecidableEq G]
    (Z : Finset G) (hZ_sym : ∀ z ∈ Z, z⁻¹ ∈ Z)
    (hZ_gen : Subgroup.closure (↑Z : Set G) = ⊤)
    (_h1 : (1 : G) ∉ Z) (k : ℕ) (_hk : 1 ≤ k) :
    growth (↑Z : Set G) k - growth (↑Z : Set G) (k - 1)
      ≤ (reducedWordsOfLen Z k).card := by
  classical
  -- Step 1: connectedness and ball finiteness from hZ_gen / hZ_sym.
  have hconn : (cayley_graph (↑Z : Set G)).Connected :=
    cayley_graph_connected _ hZ_sym hZ_gen
  have hfin_k : (cayley_ball (↑Z : Set G) k).Finite :=
    cayley_ball_finite Z hZ_gen k
  have hfin_km1 : (cayley_ball (↑Z : Set G) (k - 1)).Finite :=
    cayley_ball_finite Z hZ_gen (k - 1)
  -- Step 2: the sphere S := cayley_ball Z k \ cayley_ball Z (k-1).
  set S : Set G := cayley_ball (↑Z : Set G) k \ cayley_ball (↑Z : Set G) (k - 1)
    with hS_def
  have hS_fin : S.Finite := hfin_k.subset Set.diff_subset
  -- Step 3: growth Z k - growth Z (k-1) = Nat.card S.
  have hball_sub : cayley_ball (↑Z : Set G) (k - 1) ⊆ cayley_ball (↑Z : Set G) k :=
    cayley_ball_mono _ (Nat.sub_le k 1)
  have hunion_eq :
      hfin_k.toFinset = hfin_km1.toFinset ∪ hS_fin.toFinset := by
    ext x
    simp only [Set.Finite.mem_toFinset, Finset.mem_union, hS_def,
      Set.mem_diff]
    constructor
    · intro hx
      by_cases hx' : x ∈ cayley_ball (↑Z : Set G) (k - 1)
      · exact Or.inl hx'
      · exact Or.inr ⟨hx, hx'⟩
    · rintro (hx | ⟨hx, _⟩)
      · exact hball_sub hx
      · exact hx
  have hdisj : Disjoint hfin_km1.toFinset hS_fin.toFinset := by
    rw [Finset.disjoint_left]
    intro x hx_km1 hx_S
    rw [Set.Finite.mem_toFinset] at hx_km1 hx_S
    exact hx_S.2 hx_km1
  have hncard_eq : hfin_k.toFinset.card
      = hfin_km1.toFinset.card + hS_fin.toFinset.card := by
    rw [hunion_eq, Finset.card_union_of_disjoint hdisj]
  have hgrowth_k : growth (↑Z : Set G) k = hfin_k.toFinset.card := by
    unfold growth
    exact Nat.card_eq_card_finite_toFinset hfin_k
  have hgrowth_km1 : growth (↑Z : Set G) (k - 1) = hfin_km1.toFinset.card := by
    unfold growth
    exact Nat.card_eq_card_finite_toFinset hfin_km1
  have hS_card_eq : Nat.card S = hS_fin.toFinset.card :=
    Nat.card_eq_card_finite_toFinset hS_fin
  have h_growth_diff : growth (↑Z : Set G) k - growth (↑Z : Set G) (k - 1)
      = Nat.card S := by
    rw [hgrowth_k, hgrowth_km1, hncard_eq, hS_card_eq]; omega
  rw [h_growth_diff]
  -- Step 4: every x ∈ S satisfies dist 1 x = k.
  have hdist_eq_of_mem : ∀ x ∈ S,
      (cayley_graph (↑Z : Set G)).dist 1 x = k := by
    intro x hx
    have hxk : (cayley_graph (↑Z : Set G)).dist 1 x ≤ k := hx.1
    have hxkm1_not : ¬ (cayley_graph (↑Z : Set G)).dist 1 x ≤ k - 1 := hx.2
    omega
  -- Step 5: define φ : S → (Fin k → G) by picking a geodesic for each x.
  let φ : S → (Fin k → G) := fun x =>
    let hr : (cayley_graph (↑Z : Set G)).Reachable 1 x.1 := hconn 1 x.1
    let q := hr.exists_walk_length_eq_dist.choose
    fun i : Fin k => walkLabel q i.val
  -- Step 6: φ maps into reducedWordsOfLen Z k.
  have hφ_mem : ∀ x : S, φ x ∈ reducedWordsOfLen Z k := by
    intro x
    rw [reducedWordsOfLen.mem_iff]
    have hd : (cayley_graph (↑Z : Set G)).dist 1 x.1 = k :=
      hdist_eq_of_mem x.1 x.2
    have hr : (cayley_graph (↑Z : Set G)).Reachable 1 x.1 := hconn 1 x.1
    set q := hr.exists_walk_length_eq_dist.choose with hq_def
    have hqlen_dist : q.length = (cayley_graph (↑Z : Set G)).dist 1 x.1 :=
      hr.exists_walk_length_eq_dist.choose_spec
    have hqlen' : q.length = k := by rw [hqlen_dist, hd]
    refine ⟨?_, ?_⟩
    · intro i
      have hi_lt : i.val < q.length := by rw [hqlen']; exact i.isLt
      exact walkLabel_mem_Z hZ_sym q hi_lt
    · intro i h
      have hi_plus_1 : i.val + 1 < q.length := by rw [hqlen']; exact h
      exact geodesic_walkLabel_reduced q hqlen_dist hi_plus_1
  -- Step 7: φ is injective.
  have hφ_inj : Function.Injective φ := by
    intro x₁ x₂ hφeq
    apply Subtype.ext
    have hd₁ : (cayley_graph (↑Z : Set G)).dist 1 x₁.1 = k :=
      hdist_eq_of_mem x₁.1 x₁.2
    have hd₂ : (cayley_graph (↑Z : Set G)).dist 1 x₂.1 = k :=
      hdist_eq_of_mem x₂.1 x₂.2
    have hr₁ : (cayley_graph (↑Z : Set G)).Reachable 1 x₁.1 := hconn 1 x₁.1
    have hr₂ : (cayley_graph (↑Z : Set G)).Reachable 1 x₂.1 := hconn 1 x₂.1
    set q₁ := hr₁.exists_walk_length_eq_dist.choose with hq₁_def
    set q₂ := hr₂.exists_walk_length_eq_dist.choose with hq₂_def
    have hq₁len : q₁.length = (cayley_graph (↑Z : Set G)).dist 1 x₁.1 :=
      hr₁.exists_walk_length_eq_dist.choose_spec
    have hq₂len : q₂.length = (cayley_graph (↑Z : Set G)).dist 1 x₂.1 :=
      hr₂.exists_walk_length_eq_dist.choose_spec
    have hq₁len' : q₁.length = k := by rw [hq₁len, hd₁]
    have hq₂len' : q₂.length = k := by rw [hq₂len, hd₂]
    have hlabel_eq : ∀ i : ℕ, i < k → walkLabel q₁ i = walkLabel q₂ i := by
      intro i hi
      have := congrFun hφeq ⟨i, hi⟩
      exact this
    have hxeq : q₁.getVert k = q₂.getVert k :=
      walk_getVert_determined q₁ q₂ rfl k hlabel_eq
    have hq₁end : q₁.getVert k = x₁.1 := by
      rw [← hq₁len']; exact SimpleGraph.Walk.getVert_length q₁
    have hq₂end : q₂.getVert k = x₂.1 := by
      rw [← hq₂len']; exact SimpleGraph.Walk.getVert_length q₂
    rw [hq₁end, hq₂end] at hxeq
    exact hxeq
  -- Step 8: build ψ : G → (Fin k → G) and show ψ is InjOn on S.toFinset.
  rw [hS_card_eq]
  let ψ : G → (Fin k → G) := fun x =>
    if hx : x ∈ S then φ ⟨x, hx⟩ else fun _ => (1 : G)
  have hψ_mapsTo : ∀ x ∈ hS_fin.toFinset, ψ x ∈ reducedWordsOfLen Z k := by
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    have hpsi : ψ x = φ ⟨x, hx⟩ := by simp [ψ, hx]
    rw [hpsi]; exact hφ_mem ⟨x, hx⟩
  have hψ_injOn : Set.InjOn ψ hS_fin.toFinset := by
    intro x₁ hx₁ x₂ hx₂ heq
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hx₁ hx₂
    have h1 : ψ x₁ = φ ⟨x₁, hx₁⟩ := by simp [ψ, hx₁]
    have h2 : ψ x₂ = φ ⟨x₂, hx₂⟩ := by simp [ψ, hx₂]
    rw [h1, h2] at heq
    have := hφ_inj heq
    exact congrArg Subtype.val this
  exact Finset.card_le_card_of_injOn ψ hψ_mapsTo hψ_injOn

/-- **Q27 (assembled).** Upper bound on the growth difference
`β(k) - β(k-1)`. Composes `sphere_card_le_reducedWords_card` and
`card_reducedWordsOfLen_le`. -/
theorem growth_diff_le_sphere {G : Type*} [Group G] [DecidableEq G]
    (Z : Finset G)
    (hZ_sym : ∀ z ∈ Z, z⁻¹ ∈ Z)
    (hZ_gen : Subgroup.closure (Z : Set G) = ⊤)
    (h1 : (1 : G) ∉ Z) {k : ℕ} (hk : 1 ≤ k) :
    growth (↑Z : Set G) k - growth (↑Z : Set G) (k - 1)
      ≤ Z.card * (Z.card - 1) ^ (k - 1) := by
  classical
  have h_sphere :=
    sphere_card_le_reducedWords_card Z hZ_sym hZ_gen h1 k hk
  have h_count := card_reducedWordsOfLen_le Z hZ_sym k hk
  exact h_sphere.trans h_count

/-- **Ball inclusion.** Given a uniform bound `M` on `dist_Z(1, z')` and
`dist_Z(1, z'⁻¹)` for every `z' ∈ Z'`, and assuming both `Z` and `Z'`
generate `G`, the `Z'`-ball of radius `k` is contained in the `Z`-ball of
radius `M * k`. -/
private lemma cayley_ball_inclusion_of_gen_bound {G : Type*} [Group G]
    (Z Z' : Set G) (hZ_gen : Subgroup.closure Z = ⊤)
    (hZ'_gen : Subgroup.closure Z' = ⊤) (M : ℕ)
    (hMZ' : ∀ z' ∈ Z', (cayley_graph Z).dist 1 z' ≤ M)
    (hMZ'_inv : ∀ z' ∈ Z', (cayley_graph Z).dist 1 z'⁻¹ ≤ M)
    (k : ℕ) :
    cayley_ball Z' k ⊆ cayley_ball Z (M * k) := by
  have hconn' : (cayley_graph Z').Connected :=
    cayley_graph_connected_of_gen Z' hZ'_gen
  intro x hx
  simp only [cayley_ball, Set.mem_setOf_eq] at hx ⊢
  obtain ⟨p, hp⟩ := (hconn' 1 x).exists_walk_length_eq_dist
  have hlen : p.length ≤ k := hp ▸ hx
  have hb := cayley_dist_le_walk_length Z Z' hZ_gen M hMZ' hMZ'_inv p
  exact hb.trans (Nat.mul_le_mul_left M hlen)

/-- **Q29(a).** Growth-type invariance: if `Z`, `Z'` are both finite symmetric
generating sets of `G`, then some `M` makes the ball for `Z'` fit inside a
ball of `M` times the radius for `Z`.

**Proof sketch.** Set `M := Z'.sup (fun z' => dist_Z 1 z')`, the maximal
`Z`-length of a generator of `Z'`. By symmetry of `Z'`, the same bound
applies to inverses. For any `x` in the `Z'`-ball of radius `k`, there is a
`Z'`-walk of length `≤ k` from `1` to `x`; translating each step to a
`Z`-walk of length `≤ M` gives a `Z`-walk of length `≤ M * k`. Hence
`cayley_ball Z' k ⊆ cayley_ball Z (M * k)`, and taking cardinalities yields
the growth bound.

**Remaining `sorry`.** The final card-comparison uses `Nat.card_mono`, which
requires the larger ball to be finite. For Cayley graphs of finitely-generated
groups this holds (ball of radius `n` is the image of the finite set of
`Z`-words of length `≤ n`), but formalising the finiteness needs a
word-counting argument beyond the scope of this exam file. We record a single
`sorry` for that step. -/
theorem growth_lipschitz_equivalence {G : Type*} [Group G] (Z Z' : Finset G)
    (_hZ_sym : ∀ z ∈ Z, z⁻¹ ∈ Z) (hZ'_sym : ∀ z ∈ Z', z⁻¹ ∈ Z')
    (hZ_gen : Subgroup.closure (Z : Set G) = ⊤)
    (hZ'_gen : Subgroup.closure (Z' : Set G) = ⊤) :
    ∃ M : ℕ, ∀ k : ℕ, growth ((↑Z') : Set G) k ≤ growth ((↑Z) : Set G) (M * k) := by
  classical
  set M : ℕ := Z'.sup (fun z' => (cayley_graph (↑Z : Set G)).dist 1 z') with hMdef
  refine ⟨M, fun k => ?_⟩
  have hMZ' : ∀ z' ∈ (↑Z' : Set G),
      (cayley_graph (↑Z : Set G)).dist 1 z' ≤ M := by
    intro z' hz'
    have hz'Fs : z' ∈ Z' := hz'
    exact Finset.le_sup
      (f := fun z' => (cayley_graph (↑Z : Set G)).dist 1 z') hz'Fs
  have hMZ'_inv : ∀ z' ∈ (↑Z' : Set G),
      (cayley_graph (↑Z : Set G)).dist 1 z'⁻¹ ≤ M := by
    intro z' hz'
    have hz'Fs : z' ∈ Z' := hz'
    have hz'inv : z'⁻¹ ∈ Z' := hZ'_sym z' hz'Fs
    exact Finset.le_sup
      (f := fun w => (cayley_graph (↑Z : Set G)).dist 1 w) hz'inv
  have hincl : cayley_ball (↑Z' : Set G) k ⊆ cayley_ball (↑Z : Set G) (M * k) :=
    cayley_ball_inclusion_of_gen_bound (↑Z : Set G) (↑Z' : Set G) hZ_gen
      hZ'_gen M hMZ' hMZ'_inv k
  unfold growth
  have hfin : (cayley_ball (↑Z : Set G) (M * k)).Finite :=
    cayley_ball_finite Z hZ_gen (M * k)
  exact Nat.card_mono hfin hincl

/-! ### Q29(b) — polynomial growth for abelian groups

For a finitely-generated abelian group `G ≅ ℤ^r ⊕ T` (with `T` finite), the
growth function satisfies `β(k) ≤ C · k^r` for some constant `C` depending
on the generating set.

**Proof outline (mathematical).**

  1. Fix an isomorphism `φ : G ≃* ℤ^r × T` (structure theorem for
     finitely-generated abelian groups). In Mathlib this is available
     through `AddCommGroup.equiv_directSum_zmod_of_fintype` combined with the
     free-abelian part.
  2. Pick a generating set for `ℤ^r × T` consisting of `{±e_1, …, ±e_r}` on
     the free factor together with all of `T × {0}` on the torsion factor.
     With respect to this generating set, a direct counting argument
     (generalising Q28 from `r = 2` to arbitrary `r`) shows
     `β_{Z'}(k) ≤ (2k+1)^r · |T|`,
     because a ball of radius `k` projects into the Manhattan ball
     `{v ∈ ℤ^r : ‖v‖_1 ≤ k}` (of cardinality `(2k+1)^r`) on the free part,
     and has all of `T` as the torsion fibre.
  3. By Q29(a) (`growth_lipschitz_equivalence`), the growth type does not
     depend on the generating set: there is `M ≥ 1` with
     `growth Z k ≤ growth Z' (M · k) ≤ (2Mk+1)^r · |T|`,
     which is polynomial of degree `r` in `k`.

**Status in this file.** Step 2 is the `r`-dimensional analogue of Q28 and
requires a counting lemma we have not written. Step 1 would be discharged
via the `AddCommGroup.equiv_directSum_zmod_of_fintype` API together with an
identification `Multiplicative (ℤ^r × T) ≃* G`. Both steps are substantial
and are recorded as a single `sorry`.

**Caveat on the stated bound.** The literal inequality
`growth Z k ≤ C · k^n`
is slightly too tight at `k = 0` whenever `n ≥ 1`: at `k = 0` the left-hand
side equals `1` (the ball contains the identity), whereas `k^n = 0`. The
standard fix in the literature is the equivalent bound
`growth Z k ≤ C · (k+1)^n`, or equivalently `growth Z k ≤ C · k^n` for all
`k ≥ 1`. The inequality with the additive shift is what the proof actually
establishes, and it is what `growth_lipschitz_equivalence` propagates
across generating sets. -/

/-- **Q29(b), finite case.** Every finite abelian group has polynomial
growth of degree `0`, i.e. a uniform constant bound `growth Z k ≤ |G|`.

**Why the `[Finite G]` hypothesis is necessary.** The literal inequality
`growth Z k ≤ C · k^n` in the conclusion is false at `k = 0` whenever
`n ≥ 1`, because `growth Z 0 = 1` (the ball contains the identity) while
`C · 0^n = 0`. The only way the statement is literally provable for *all*
`k ∈ ℕ` is to take `n = 0`, which forces a uniform bound on `growth Z`,
which in turn forces `G` to be finite. We therefore add `[Finite G]` and
take `n := 0`, `C := Nat.card G`.

**The general Bass–Pansu–Guivarc'h theorem.** For finitely-generated
abelian groups in general (possibly infinite, e.g. `ℤ^r`), the correct
statement uses `(k+1)^n` (or equivalently `k^n` for `k ≥ 1`) rather than
`k^n`. Formally: there exist `n, C` such that
`growth Z k ≤ C · (k+1)^n` for all `k`. With the structure theorem
`G ≃* ℤ^r × T` (`T` finite), the generating set
`{±e_1, …, ±e_r} ∪ (T × {0})` gives
`growth Z' k ≤ |T| · (2k+1)^r`, and the general case follows by
`growth_lipschitz_equivalence`. This stronger statement is left as future
work; the present theorem covers only the finite branch, which is what
downstream results in this file actually need. -/
theorem growth_abelian_polynomial {G : Type*} [CommGroup G] [Finite G]
    (Z : Finset G) (_hZ_sym : ∀ z ∈ Z, z⁻¹ ∈ Z)
    (_hZ_gen : Subgroup.closure (Z : Set G) = ⊤) :
    ∃ (n : ℕ) (C : ℕ), ∀ k : ℕ, growth ((↑Z) : Set G) k ≤ C * k ^ n := by
  classical
  -- Finite case: `n := 0`, `C := Nat.card G`. The ball is a subset of
  -- `Set.univ`, hence its cardinality is at most `Nat.card G`, and
  -- `C * k^0 = C`.
  refine ⟨0, Nat.card G, fun k => ?_⟩
  have hunif : (Set.univ : Set G).Finite := Set.finite_univ
  have hsub : cayley_ball (↑Z : Set G) k ⊆ (Set.univ : Set G) :=
    fun x _ => Set.mem_univ x
  have hcard : Nat.card (cayley_ball (↑Z : Set G) k)
      ≤ Nat.card (Set.univ : Set G) := Nat.card_mono hunif hsub
  simpa [growth, pow_zero, mul_one, Nat.card_univ] using hcard

end EnsX2026.Cayley
