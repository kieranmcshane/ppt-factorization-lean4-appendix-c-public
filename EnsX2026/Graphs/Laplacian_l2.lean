import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Order.Chebyshev

/-!
# ENS/Polytechnique 2026 Math A — Section 5 Laplacian on an infinite graph (Q12–Q17)

Let `G = (V, E)` be a simple graph on a (possibly infinite) vertex type `V`, with
`LocallyFinite G` (every vertex has a finite neighbourhood) and a uniform degree
bound `K`. This file formalises the combinatorial Laplacian `Δ : (V → ℝ) → (V → ℝ)`
given by

  `(Δf)(v) = deg(v) · f(v) − ∑_{w ∼ v} f(w)`

on the full function space, and promotes it to a bounded linear operator on the
Hilbert space `ℋ = ℓ²(V)`.

## Status

* **Q12 — fully proven.** `laplacian_E`, `laplacian_E_linear`, and the
  non-injectivity witness `laplacian_E_not_injective` (constant functions are
  in the kernel) are `sorry`-free.
* **Q13 — fully proven.** The concrete `Γ_ℕ` and `Γ_ℤ` path graphs are
  provided with worked `LocallyFinite` instances, the kernel characterisations
  (harmonic = constant on `Γ_ℕ` / arithmetic-progression on `Γ_ℤ`) are
  `sorry`-free, and the Laplacian on `Γ_ℕ` is shown to be surjective via a
  direct recurrence construction.
* **Q14 — fully proven.** `memℓp_const_one_iff_finite` characterises when the
  all-ones function belongs to `ℓ²(V)`.
* **Q15 — core reduction proven, two auxiliary summability lemmas stubbed.**
  The pointwise bound `(Δf)(v)² ≤ 2 K² f(v)² + 2 K ∑_{w∼v} f(w)²` is fully
  formalised (`laplacian_sq_pointwise_bound`). The full ℓ² stability and the
  explicit operator-norm bound `‖Δf‖² ≤ 4 K² · ‖f‖²` follow, modulo two
  auxiliary summability lemmas for the edge-double-sum swap which are marked
  as `sorry` (`summable_neighbor_sq`, `tsum_neighbor_sq_le`).
* **Q16 — contingent on Q15.** `laplacian_H` and its continuity are wired up
  from `laplacian_l2_norm_bound` via `LinearMap.mkContinuous`, and therefore
  inherit the two Q15 stubs but no additional ones.
* **Q17 — fully proven.** Both the ℓ² edge-sum identity (`laplacian_H_edge_sum`)
  and self-adjointness (`laplacian_H_isSelfAdjoint`) are `sorry`-free. The
  Fubini step uses the directed-edge Sigma type `Σ v, {w // w ∈ N(v)}` with
  the adjacency-symmetry involution `⟨v,w⟩ ↦ ⟨w,v⟩` and absolute convergence
  from the AM-GM majorant `summable_neighbor_abs_mul_of_ℓ2`.

Institut Fourier, Grenoble — Kieran McShane
-/

namespace EnsX2026.Graphs

open Finset SimpleGraph
open scoped ENNReal

variable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Q12 — The Laplacian on `V → ℝ` -/

section Q12

variable [LocallyFinite G]

/-- The combinatorial Laplacian on functions `V → ℝ`. Well-defined pointwise
because `G.neighborFinset v` is finite under `LocallyFinite G`. -/
noncomputable def laplacian_E (f : V → ℝ) : V → ℝ :=
  fun v => (G.degree v : ℝ) * f v - ∑ w ∈ G.neighborFinset v, f w

theorem laplacian_E_apply (f : V → ℝ) (v : V) :
    laplacian_E G f v = (G.degree v : ℝ) * f v - ∑ w ∈ G.neighborFinset v, f w := rfl

/-- **Q12 (linearity).** `Δ` is ℝ-linear on `V → ℝ`. -/
theorem laplacian_E_linear : IsLinearMap ℝ (laplacian_E G) where
  map_add := by
    intro f g
    funext v
    show (G.degree v : ℝ) * (f + g) v
            - ∑ w ∈ G.neighborFinset v, (f + g) w
        = ((G.degree v : ℝ) * f v - ∑ w ∈ G.neighborFinset v, f w)
          + ((G.degree v : ℝ) * g v - ∑ w ∈ G.neighborFinset v, g w)
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib]
    ring
  map_smul := by
    intro c f
    funext v
    show (G.degree v : ℝ) * (c • f) v
            - ∑ w ∈ G.neighborFinset v, (c • f) w
        = c • ((G.degree v : ℝ) * f v - ∑ w ∈ G.neighborFinset v, f w)
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show (∑ x ∈ G.neighborFinset v, c * f x)
          = c * ∑ x ∈ G.neighborFinset v, f x from
        (Finset.mul_sum _ _ _).symm]
    ring

/-- Every constant function is killed by `Δ`. -/
theorem laplacian_E_const (c : ℝ) :
    laplacian_E G (fun _ => c) = 0 := by
  funext v
  show (G.degree v : ℝ) * c - ∑ _w ∈ G.neighborFinset v, c = 0
  have hcard : (#(G.neighborFinset v) : ℝ) = (G.degree v : ℝ) := by
    rw [card_neighborFinset_eq_degree]
  rw [Finset.sum_const, nsmul_eq_mul, hcard]
  ring

/-- **Q12 (kernel witness).** As soon as `V` is inhabited, `Δ` is not injective
on `V → ℝ`: the constant function `1` is a non-zero element of the kernel. -/
theorem laplacian_E_not_injective [h : Nonempty V] :
    ∃ f : V → ℝ, f ≠ 0 ∧ laplacian_E G f = 0 := by
  refine ⟨fun _ => (1 : ℝ), ?_, laplacian_E_const G 1⟩
  intro hzero
  obtain ⟨v⟩ := h
  have : (1 : ℝ) = 0 := congrArg (· v) hzero
  exact one_ne_zero this

end Q12

/-! ### Q13 — The two infinite path graphs (statements only) -/

section Q13

/-- `Γ_ℕ` is the path graph on `ℕ`: `i ~ j` iff `|i − j| = 1`. -/
def graph_N : SimpleGraph ℕ :=
  SimpleGraph.fromRel (fun i j : ℕ => (j : ℤ) - i = 1)

instance graph_N_decAdj : DecidableRel graph_N.Adj := by
  unfold graph_N
  infer_instance

/-- The `Γ_ℕ`-neighbourhood of `n` is contained in `{n + 1, n - 1}`. -/
lemma graph_N_neighborSet_subset (n : ℕ) :
    graph_N.neighborSet n ⊆ ({n + 1, n - 1} : Set ℕ) := by
  intro m hm
  rcases hm with ⟨_hne, (h | h)⟩
  · -- (m : ℤ) − n = 1, so m = n + 1
    have : m = n + 1 := by omega
    simp [this]
  · -- (n : ℤ) − m = 1, so m = n − 1
    have : m = n - 1 := by omega
    simp [this]

noncomputable instance graph_N_locallyFinite : LocallyFinite graph_N := by
  intro n
  apply Set.Finite.fintype
  exact Set.Finite.subset (Set.toFinite _) (graph_N_neighborSet_subset n)

/-! #### Concrete neighbour finsets for `Γ_ℕ`.

Two building blocks feed every proof that follows:
* `graph_N.neighborFinset 0 = {1}` (boundary),
* `graph_N.neighborFinset (n+1) = {n, n+2}` (interior).
From these we read off `degree 0 = 1` and `degree (n+1) = 2`. -/

private lemma graph_N_adj_iff (i j : ℕ) :
    graph_N.Adj i j ↔ i ≠ j ∧ ((j : ℤ) - i = 1 ∨ (i : ℤ) - j = 1) := by
  unfold graph_N
  exact SimpleGraph.fromRel_adj _ _ _

lemma graph_N_neighborFinset_zero :
    graph_N.neighborFinset 0 = {1} := by
  ext m
  rw [mem_neighborFinset, graph_N_adj_iff]
  constructor
  · rintro ⟨hne, h | h⟩
    · have : m = 1 := by omega
      simp [this]
    · exfalso; omega
  · intro hm
    rw [Finset.mem_singleton] at hm
    subst hm
    refine ⟨?_, Or.inl ?_⟩
    · intro h; exact absurd h (by norm_num)
    · norm_num

lemma graph_N_neighborFinset_succ (n : ℕ) :
    graph_N.neighborFinset (n + 1) = {n, n + 2} := by
  ext m
  rw [mem_neighborFinset, graph_N_adj_iff]
  constructor
  · rintro ⟨hne, h | h⟩
    · have : m = n + 2 := by omega
      simp [this]
    · have : m = n := by omega
      simp [this]
  · intro hm
    rw [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · exact ⟨by omega, Or.inr (by push_cast; ring)⟩
    · exact ⟨by omega, Or.inl (by push_cast; ring)⟩

lemma graph_N_degree_zero : graph_N.degree 0 = 1 := by
  rw [← card_neighborFinset_eq_degree, graph_N_neighborFinset_zero]
  simp

lemma graph_N_degree_succ (n : ℕ) : graph_N.degree (n + 1) = 2 := by
  rw [← card_neighborFinset_eq_degree, graph_N_neighborFinset_succ]
  have hne : n ≠ n + 2 := by omega
  rw [Finset.card_insert_of_notMem (Finset.notMem_singleton.mpr hne)]
  simp

/-- Evaluating `Δ f` at `0` on `Γ_ℕ`. -/
lemma graph_N_laplacian_zero (f : ℕ → ℝ) :
    laplacian_E graph_N f 0 = f 0 - f 1 := by
  rw [laplacian_E_apply, graph_N_neighborFinset_zero, graph_N_degree_zero]
  simp

/-- Evaluating `Δ f` at `n + 1` on `Γ_ℕ`. -/
lemma graph_N_laplacian_succ (f : ℕ → ℝ) (n : ℕ) :
    laplacian_E graph_N f (n + 1) = 2 * f (n + 1) - f n - f (n + 2) := by
  rw [laplacian_E_apply, graph_N_neighborFinset_succ, graph_N_degree_succ]
  have hne : n ≠ n + 2 := by omega
  rw [Finset.sum_insert (Finset.notMem_singleton.mpr hne), Finset.sum_singleton]
  push_cast; ring

/-- **Q13(a) — kernel of Δ on `Γ_ℕ`.** Harmonic functions on the path graph
on `ℕ` are exactly the constants.

Proof: if `Δf = 0`, then `f 0 = f 1` (boundary) and
`f(n+2) = 2 f(n+1) - f n` (interior). Induction gives `f n = f 0` for all `n`. -/
theorem graph_N_kernel_const (f : ℕ → ℝ) :
    laplacian_E graph_N f = 0 ↔ ∃ c, ∀ n, f n = c := by
  constructor
  · intro h
    refine ⟨f 0, ?_⟩
    -- Prove `∀ n, f n = f 0` by strong induction.
    have key : ∀ n, f n = f 0 ∧ f (n + 1) = f 0 := by
      intro n
      induction n with
      | zero =>
          refine ⟨rfl, ?_⟩
          have h0 : laplacian_E graph_N f 0 = 0 := congrArg (· 0) h
          rw [graph_N_laplacian_zero] at h0
          linarith
      | succ k ih =>
          obtain ⟨hk, hk1⟩ := ih
          refine ⟨hk1, ?_⟩
          have hk2 : laplacian_E graph_N f (k + 1) = 0 := congrArg (· (k + 1)) h
          rw [graph_N_laplacian_succ] at hk2
          -- 2 * f(k+1) - f k - f(k+2) = 0
          -- f(k+2) = 2 f(k+1) - f k = 2 * f 0 - f 0 = f 0
          linarith
    intro n
    exact (key n).1
  · rintro ⟨c, hc⟩
    have : f = fun _ => c := funext hc
    rw [this]
    exact laplacian_E_const graph_N c

/-- Auxiliary helper that returns the pair `(f n, f (n+1))` where `f` is the
recursively constructed preimage of `g` under the Laplacian on `Γ_ℕ`. -/
private def graph_N_surj_pair (g : ℕ → ℝ) : ℕ → ℝ × ℝ
  | 0 => (0, -g 0)
  | n + 1 =>
      let p := graph_N_surj_pair g n
      (p.2, 2 * p.2 - p.1 - g (n + 1))

private lemma graph_N_surj_pair_succ (g : ℕ → ℝ) (n : ℕ) :
    (graph_N_surj_pair g (n + 1)).1 = (graph_N_surj_pair g n).2 := rfl

private lemma graph_N_surj_pair_succ_snd (g : ℕ → ℝ) (n : ℕ) :
    (graph_N_surj_pair g (n + 1)).2
      = 2 * (graph_N_surj_pair g n).2 - (graph_N_surj_pair g n).1 - g (n + 1) := rfl

/-- **Q13(a) — surjectivity of Δ on `Γ_ℕ`.** The Laplacian on the half-line
graph is onto.

Construction: define `f 0 := 0`, `f 1 := -g 0`, and for `n ≥ 1`,
`f (n+2) := 2 * f (n+1) - f n - g (n+1)`. This ensures
`Δf(0) = f 0 - f 1 = g 0` and `Δf(n+1) = 2 f(n+1) - f n - f(n+2) = g(n+1)`. -/
theorem graph_N_laplacian_surjective :
    Function.Surjective (laplacian_E graph_N) := by
  intro g
  let f : ℕ → ℝ := fun n => (graph_N_surj_pair g n).1
  refine ⟨f, ?_⟩
  -- Key step: `f (n+1) = (pair n).2`.
  have step : ∀ n, f (n + 1) = (graph_N_surj_pair g n).2 := by
    intro n
    show (graph_N_surj_pair g (n + 1)).1 = (graph_N_surj_pair g n).2
    exact graph_N_surj_pair_succ g n
  -- Recurrence: `f (n+2) = 2 f(n+1) - f n - g(n+1)`.
  have rel : ∀ n, f (n + 2) = 2 * f (n + 1) - f n - g (n + 1) := by
    intro n
    show (graph_N_surj_pair g (n + 2)).1
        = 2 * (graph_N_surj_pair g (n + 1)).1
            - (graph_N_surj_pair g n).1 - g (n + 1)
    rw [graph_N_surj_pair_succ g (n + 1), graph_N_surj_pair_succ_snd g n,
        graph_N_surj_pair_succ g n]
  funext v
  match v with
  | 0 =>
      rw [graph_N_laplacian_zero]
      -- f 0 = 0, f 1 = -g 0, so f 0 - f 1 = g 0.
      show (0 : ℝ) - (-g 0) = g 0
      ring
  | n + 1 =>
      rw [graph_N_laplacian_succ]
      have := rel n
      -- 2 f(n+1) - f n - f(n+2) = g(n+1).
      show 2 * f (n + 1) - f n - f (n + 2) = g (n + 1)
      linarith

/-- `Γ_ℤ` is the path graph on `ℤ`: `i ~ j` iff `|i − j| = 1`. -/
def graph_Z : SimpleGraph ℤ :=
  SimpleGraph.fromRel (fun i j : ℤ => j - i = 1)

instance graph_Z_decAdj : DecidableRel graph_Z.Adj := by
  unfold graph_Z
  infer_instance

lemma graph_Z_neighborSet_subset (n : ℤ) :
    graph_Z.neighborSet n ⊆ ({n + 1, n - 1} : Set ℤ) := by
  intro m hm
  rcases hm with ⟨_hne, (h | h)⟩
  · -- m − n = 1, so m = n + 1
    have : m = n + 1 := by linarith
    simp [this]
  · -- n − m = 1, so m = n − 1
    have : m = n - 1 := by linarith
    simp [this]

noncomputable instance graph_Z_locallyFinite : LocallyFinite graph_Z := by
  intro n
  apply Set.Finite.fintype
  exact Set.Finite.subset (Set.toFinite _) (graph_Z_neighborSet_subset n)

/-! #### Concrete neighbour finsets for `Γ_ℤ`.

Every vertex has degree `2`, with `neighborFinset n = {n - 1, n + 1}`. -/

private lemma graph_Z_adj_iff (i j : ℤ) :
    graph_Z.Adj i j ↔ i ≠ j ∧ (j - i = 1 ∨ i - j = 1) := by
  unfold graph_Z
  exact SimpleGraph.fromRel_adj _ _ _

lemma graph_Z_neighborFinset (n : ℤ) :
    graph_Z.neighborFinset n = {n - 1, n + 1} := by
  ext m
  rw [mem_neighborFinset, graph_Z_adj_iff]
  constructor
  · rintro ⟨hne, h | h⟩
    · have : m = n + 1 := by linarith
      simp [this]
    · have : m = n - 1 := by linarith
      simp [this]
  · intro hm
    rw [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · exact ⟨by linarith, Or.inr (by ring)⟩
    · exact ⟨by linarith, Or.inl (by ring)⟩

lemma graph_Z_degree (n : ℤ) : graph_Z.degree n = 2 := by
  rw [← card_neighborFinset_eq_degree, graph_Z_neighborFinset]
  have : n - 1 ≠ n + 1 := by intro h; linarith
  rw [Finset.card_insert_of_notMem (by simp [this])]
  simp

/-- Evaluating `Δ f` on `Γ_ℤ`. -/
lemma graph_Z_laplacian_apply (f : ℤ → ℝ) (n : ℤ) :
    laplacian_E graph_Z f n = 2 * f n - f (n - 1) - f (n + 1) := by
  rw [laplacian_E_apply, graph_Z_neighborFinset, graph_Z_degree]
  have hne : n - 1 ≠ n + 1 := by intro h; linarith
  rw [Finset.sum_insert (by simp [hne]), Finset.sum_singleton]
  push_cast; ring

/-- **Q13(b) — kernel of Δ on `Γ_ℤ`.** Harmonic functions on the two-sided path
graph on `ℤ` are exactly the arithmetic progressions `f n = a · n + b`.

Proof: the recurrence `f(n+1) = 2 f(n) − f(n-1)` forces the difference
sequence `f(n+1) − f(n)` to be constant, so `f n = a · n + b`. -/
theorem graph_Z_kernel_arithmetic (f : ℤ → ℝ) :
    laplacian_E graph_Z f = 0 ↔ ∃ a b : ℝ, ∀ n : ℤ, f n = a * n + b := by
  constructor
  · intro h
    set a := f 1 - f 0 with ha
    set b := f 0 with hb
    refine ⟨a, b, ?_⟩
    -- Recurrence: `f (n+1) = 2 f n - f (n-1)` for all `n : ℤ`.
    have rec_eq : ∀ n : ℤ, f (n + 1) = 2 * f n - f (n - 1) := by
      intro n
      have hlap : laplacian_E graph_Z f n = 0 := congrArg (· n) h
      rw [graph_Z_laplacian_apply] at hlap
      linarith
    -- Strong inductive statement: `P n := f n = a * n + b ∧ f (n+1) = a * (n+1) + b`.
    -- We prove `P n` for all `n : ℤ` using `Int.induction_on`.
    suffices key : ∀ n : ℤ, f n = a * n + b ∧ f (n + 1) = a * (n + 1) + b from
      fun n => (key n).1
    intro n
    induction n with
    | zero =>
        refine ⟨?_, ?_⟩
        · show f 0 = a * (0 : ℤ) + b
          push_cast; simp [hb]
        · show f (0 + 1) = a * ((0 : ℤ) + 1) + b
          push_cast
          simp only [ha, hb]
          ring
    | succ i ih =>
        obtain ⟨_hi, hi1⟩ := ih
        -- The inductive hypothesis gives `f i = a * i + b` and `f (i+1) = a * (i+1) + b`.
        -- After `succ` the context replaces the expected argument `(i+1 : ℕ)` with its ℤ-cast.
        -- We rewrite using the recurrence at `n = i + 1`.
        have hi2 : f ((i : ℤ) + 1 + 1) = a * ((i : ℤ) + 1 + 1) + b := by
          have hrec := rec_eq ((i : ℤ) + 1)
          have he : ((i : ℤ) + 1) - 1 = (i : ℤ) := by ring
          rw [he] at hrec
          -- hrec : f (i+1+1) = 2 * f (i+1) - f i.
          -- hi : f i = a * i + b. hi1 : f (i+1) = a * (i+1) + b.
          rw [hrec, _hi, hi1]
          push_cast; ring
        refine ⟨?_, ?_⟩
        · -- Goal: `f (((i + 1 : ℕ) : ℤ)) = a * ((i + 1 : ℕ) : ℤ) + b`.
          -- Equivalently `f ((i : ℤ) + 1) = a * ((i : ℤ) + 1) + b = hi1`.
          push_cast
          exact hi1
        · -- Goal: `f (((i + 1 : ℕ) : ℤ) + 1) = a * (((i + 1 : ℕ) : ℤ) + 1) + b`.
          push_cast
          exact hi2
    | pred i ih =>
        obtain ⟨hi, hi1⟩ := ih
        -- `hi : f (-(i : ℤ)) = a * (-(i : ℤ)) + b`, `hi1 : f (-(i : ℤ) + 1) = a * (-(i : ℤ) + 1) + b`.
        have him1 : f (-(i : ℤ) - 1) = a * (-(i : ℤ) - 1) + b := by
          have hrec := rec_eq (-(i : ℤ))
          -- hrec : f (-i + 1) = 2 * f (-i) - f (-i - 1), so f (-i - 1) = 2 f (-i) - f (-i + 1).
          have hflip : f (-(i : ℤ) - 1) = 2 * f (-(i : ℤ)) - f (-(i : ℤ) + 1) := by linarith
          rw [hflip]
          have hi_cast : f (-(i : ℤ)) = a * (-(i : ℤ)) + b := by
            have := hi
            push_cast at this
            exact this
          have hi1_cast : f (-(i : ℤ) + 1) = a * (-(i : ℤ) + 1) + b := by
            have := hi1
            push_cast at this
            exact this
          rw [hi_cast, hi1_cast]
          ring
        refine ⟨?_, ?_⟩
        · -- Goal: `f (-(i : ℤ) - 1) = a * (-(i : ℤ) - 1) + b` up to casts.
          push_cast
          exact him1
        · -- Goal involves `f (-(i : ℤ) - 1 + 1) = a * (↑(-(i : ℤ) - 1) + 1) + b`.
          -- Simplify the function argument `-i - 1 + 1 = -i` at the integer level,
          -- then the real-part `↑(-i - 1) + 1 = -i` at the real level.
          have hi_cast : f (-(i : ℤ)) = a * (-(i : ℤ) : ℝ) + b := by
            have := hi
            push_cast at this
            exact this
          have he : (-(i : ℤ) - 1 + 1 : ℤ) = -(i : ℤ) := by ring
          rw [he]
          have goal_rhs : ((-(i : ℤ) - 1 : ℤ) : ℝ) + 1 = (-(i : ℤ) : ℝ) := by
            push_cast; ring
          rw [goal_rhs]
          exact hi_cast
  · rintro ⟨a, b, hf⟩
    funext n
    rw [graph_Z_laplacian_apply]
    show 2 * f n - f (n - 1) - f (n + 1) = (0 : ℝ)
    rw [hf n, hf (n - 1), hf (n + 1)]
    push_cast
    ring

end Q13

/-! ### Q14 — `ℓ²(V) = (V → ℝ)` iff `V` is finite -/

section Q14

/-- **Q14.** The constant function `1 : V → ℝ` belongs to `ℓ²(V)` iff `V` is
finite. This encapsulates the logical content of Q14: on an infinite `V`, the
Hilbert space `ℓ²(V)` is a proper subspace of `V → ℝ`. -/
theorem memℓp_const_one_iff_finite :
    Memℓp (fun _ : V => (1 : ℝ)) 2 ↔ Finite V := by
  constructor
  · intro hmem
    have h2 : ((2 : ℝ≥0∞).toReal) = (2 : ℝ) := by simp
    have hp : (0 : ℝ) < ((2 : ℝ≥0∞).toReal) := by rw [h2]; norm_num
    have hsum : Summable (fun _ : V => (1 : ℝ)) := by
      have hss := hmem.summable hp
      simpa using hss
    -- A constant-1 summable series forces `V` to be finite.
    have hfinite : (Set.univ : Set V).Finite :=
      Set.Finite.of_summable_const (by norm_num : (0:ℝ) < 1) hsum
    exact (Set.finite_univ_iff).mp hfinite
  · intro hfin
    -- For finite `V` the set of non-zero values is finite, so any function
    -- is trivially `Memℓp` at every exponent.
    apply memℓp_gen
    have : Fintype V := Fintype.ofFinite V
    exact summable_of_ne_finset_zero (s := (Finset.univ : Finset V))
      (by intro i hi; simp at hi)

end Q14

/-! ### Q15 — `ℓ²(V)` is stable under `Δ`, with an explicit norm bound

The core of the ℓ² upgrade is a pointwise squared bound:

  `(Δf)(v)² ≤ 2 K² f(v)² + 2 K ∑_{w ∼ v} f(w)²`.

Summing over `v` and using the edge double-sum swap
`∑_v ∑_{w ∼ v} f(w)² ≤ K · ∑_w f(w)²` yields `‖Δf‖² ≤ 4 K² · ‖f‖²`.
-/

section Q15

variable [LocallyFinite G] (K : ℕ) (hK : ∀ v : V, G.degree v ≤ K)

include hK in
/-- **Pointwise squared bound.** `(Δf)(v)² ≤ 2 K² f(v)² + 2 K · ∑_{w ∼ v} f(w)²`.
Combines `(a − b)² ≤ 2 a² + 2 b²` with the Cauchy–Schwarz-type inequality
`(∑ f w)² ≤ #(N v) · ∑ f w²`. -/
theorem laplacian_sq_pointwise_bound (f : V → ℝ) (v : V) :
    (laplacian_E G f v) ^ 2 ≤
      2 * (K : ℝ)^2 * f v ^ 2 + 2 * (K : ℝ) * ∑ w ∈ G.neighborFinset v, f w ^ 2 := by
  have h_ab : ∀ a b : ℝ, (a - b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := fun a b => by
    nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]
  -- Chebyshev / Cauchy–Schwarz: `(∑ f w)² ≤ #(N v) · ∑ f w²`.
  have h_cs : (∑ w ∈ G.neighborFinset v, f w) ^ 2
      ≤ (G.degree v : ℝ) * ∑ w ∈ G.neighborFinset v, f w ^ 2 := by
    have hCS := sq_sum_le_card_mul_sum_sq
      (s := G.neighborFinset v) (f := f)
    have hcard : (#(G.neighborFinset v) : ℝ) = (G.degree v : ℝ) := by
      exact_mod_cast G.card_neighborFinset_eq_degree (v := v)
    rw [hcard] at hCS
    exact hCS
  have hK_v : (G.degree v : ℝ) ≤ K := by exact_mod_cast hK v
  calc (laplacian_E G f v) ^ 2
      = ((G.degree v : ℝ) * f v - ∑ w ∈ G.neighborFinset v, f w) ^ 2 := by
          rw [laplacian_E_apply]
    _ ≤ 2 * ((G.degree v : ℝ) * f v) ^ 2
          + 2 * (∑ w ∈ G.neighborFinset v, f w) ^ 2 :=
          h_ab _ _
    _ ≤ 2 * ((K : ℝ) * f v) ^ 2
          + 2 * ((G.degree v : ℝ) * ∑ w ∈ G.neighborFinset v, f w ^ 2) := by
          have h1 : ((G.degree v : ℝ) * f v) ^ 2 ≤ ((K : ℝ) * f v) ^ 2 := by
            have hdeg_nn : (0 : ℝ) ≤ (G.degree v : ℝ) := by positivity
            have hfv2 : (0 : ℝ) ≤ f v ^ 2 := sq_nonneg _
            calc ((G.degree v : ℝ) * f v) ^ 2
                = (G.degree v : ℝ) ^ 2 * f v ^ 2 := by ring
              _ ≤ (K : ℝ) ^ 2 * f v ^ 2 := by
                  gcongr
              _ = ((K : ℝ) * f v) ^ 2 := by ring
          linarith [h_cs]
    _ ≤ 2 * ((K : ℝ) * f v) ^ 2
          + 2 * ((K : ℝ) * ∑ w ∈ G.neighborFinset v, f w ^ 2) := by
          have hsum_nn : (0 : ℝ) ≤ ∑ w ∈ G.neighborFinset v, f w ^ 2 :=
            Finset.sum_nonneg (fun _ _ => sq_nonneg _)
          gcongr
    _ = 2 * (K : ℝ)^2 * f v ^ 2
          + 2 * (K : ℝ) * ∑ w ∈ G.neighborFinset v, f w ^ 2 := by ring

/-- **Key finite bound** (edge double-sum swap). For every finite set
`s : Finset V`, the partial double sum is bounded by `K · ∑' w, f(w)²`.

Proof: swap the two finite sums using `G`-adjacency symmetry. Each `w` appears
in the inner sum for `v ∈ s` iff `G.Adj v w`, and the number of such `v`'s is
at most `deg w ≤ K`. -/
private lemma partial_neighbor_sum_le (f : V → ℝ) (hK : ∀ v : V, G.degree v ≤ K)
    (hf : Summable (fun v => f v ^ 2)) (s : Finset V) :
    ∑ v ∈ s, ∑ w ∈ G.neighborFinset v, f w ^ 2
      ≤ (K : ℝ) * (∑' w, f w ^ 2) := by
  classical
  -- `T` is the union of the neighbourhoods of `v ∈ s` — a finset containing
  -- every `w` that actually contributes to the double sum.
  set T : Finset V := s.biUnion (fun v => G.neighborFinset v) with hT
  -- Step 1: rewrite the inner sum as a sum over `T` with an `if G.Adj v w` guard.
  have step1 : ∑ v ∈ s, ∑ w ∈ G.neighborFinset v, f w ^ 2
      = ∑ v ∈ s, ∑ w ∈ T, if G.Adj v w then f w ^ 2 else 0 := by
    refine Finset.sum_congr rfl (fun v hv => ?_)
    have hsub : G.neighborFinset v ⊆ T := by
      intro w hw
      simp only [hT, Finset.mem_biUnion]
      exact ⟨v, hv, hw⟩
    calc ∑ w ∈ G.neighborFinset v, f w ^ 2
        = ∑ w ∈ T, if w ∈ G.neighborFinset v then f w ^ 2 else 0 := by
          rw [← Finset.sum_filter]
          refine Finset.sum_congr ?_ (fun _ _ => rfl)
          ext w
          simp only [Finset.mem_filter]
          exact ⟨fun hw => ⟨hsub hw, hw⟩, fun ⟨_, hw⟩ => hw⟩
      _ = ∑ w ∈ T, if G.Adj v w then f w ^ 2 else 0 := by
          refine Finset.sum_congr rfl (fun w _ => ?_)
          by_cases hAdj : G.Adj v w
          · have hmem : w ∈ G.neighborFinset v := by
              rw [mem_neighborFinset]; exact hAdj
            simp [hAdj, hmem]
          · have hmem : w ∉ G.neighborFinset v := by
              rw [mem_neighborFinset]; exact hAdj
            simp [hAdj, hmem]
  -- Step 2: swap the sums.
  have step2 : ∑ v ∈ s, ∑ w ∈ T, (if G.Adj v w then f w ^ 2 else 0)
      = ∑ w ∈ T, ∑ v ∈ s, (if G.Adj v w then f w ^ 2 else 0) := Finset.sum_comm
  -- Step 3: for each `w ∈ T`, collapse the inner sum.
  have step3 : ∀ w ∈ T,
      (∑ v ∈ s, if G.Adj v w then f w ^ 2 else 0)
        ≤ (K : ℝ) * f w ^ 2 := by
    intro w _
    -- Inner sum equals `#(s.filter (G.Adj · w)) · f w ^ 2`.
    have hcount : (∑ v ∈ s, if G.Adj v w then f w ^ 2 else 0)
        = (#(s.filter (fun v => G.Adj v w)) : ℝ) * f w ^ 2 := by
      rw [← Finset.sum_filter]
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hcount]
    have hsub_nbr : s.filter (fun v => G.Adj v w) ⊆ G.neighborFinset w := by
      intro v hv
      simp only [Finset.mem_filter] at hv
      rw [mem_neighborFinset]
      exact hv.2.symm
    have hcard_le : (#(s.filter (fun v => G.Adj v w)) : ℝ) ≤ (K : ℝ) := by
      have h1 : #(s.filter (fun v => G.Adj v w)) ≤ #(G.neighborFinset w) :=
        Finset.card_le_card hsub_nbr
      have h2 : #(G.neighborFinset w) = G.degree w :=
        G.card_neighborFinset_eq_degree (v := w)
      have h3 : G.degree w ≤ K := hK w
      have hnat : #(s.filter (fun v => G.Adj v w)) ≤ K := by
        calc #(s.filter (fun v => G.Adj v w))
            ≤ #(G.neighborFinset w) := h1
          _ = G.degree w := h2
          _ ≤ K := h3
      exact_mod_cast hnat
    have hfw2_nn : (0 : ℝ) ≤ f w ^ 2 := sq_nonneg _
    exact mul_le_mul_of_nonneg_right hcard_le hfw2_nn
  -- Step 4: combine.
  calc ∑ v ∈ s, ∑ w ∈ G.neighborFinset v, f w ^ 2
      = ∑ v ∈ s, ∑ w ∈ T, if G.Adj v w then f w ^ 2 else 0 := step1
    _ = ∑ w ∈ T, ∑ v ∈ s, if G.Adj v w then f w ^ 2 else 0 := step2
    _ ≤ ∑ w ∈ T, (K : ℝ) * f w ^ 2 := Finset.sum_le_sum step3
    _ = (K : ℝ) * ∑ w ∈ T, f w ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (K : ℝ) * ∑' w, f w ^ 2 := by
        have hK_nn : (0 : ℝ) ≤ (K : ℝ) := by exact_mod_cast Nat.zero_le K
        have hle : ∑ w ∈ T, f w ^ 2 ≤ ∑' w, f w ^ 2 :=
          hf.sum_le_tsum T (fun _ _ => sq_nonneg _)
        exact mul_le_mul_of_nonneg_left hle hK_nn

/-- **Summability of the neighbour-sum column.** If `v ↦ f(v)²` is summable,
so is `v ↦ 2 K · ∑_{w ∼ v} f(w)²`. -/
theorem summable_neighbor_sq (f : V → ℝ) (hK : ∀ v : V, G.degree v ≤ K)
    (hf : Summable (fun v => f v ^ 2)) :
    Summable (fun v : V => 2 * (K : ℝ) * ∑ w ∈ G.neighborFinset v, f w ^ 2) := by
  -- First show summability of the unscaled `v ↦ ∑_{w ∼ v} f(w)²`.
  have hcore : Summable (fun v : V => ∑ w ∈ G.neighborFinset v, f w ^ 2) := by
    apply summable_of_sum_le
    · intro v
      exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    · intro s
      exact partial_neighbor_sum_le G K f hK hf s
  exact hcore.mul_left _

/-- **Edge double-sum bound.** The neighbour-sum column satisfies
`∑'_v ∑_{w ∼ v} f(w)² ≤ K · ∑'_v f(v)²`. -/
theorem tsum_neighbor_sq_le (f : V → ℝ) (hK : ∀ v : V, G.degree v ≤ K)
    (hf : Summable (fun v => f v ^ 2)) :
    (∑' v : V, ∑ w ∈ G.neighborFinset v, f w ^ 2) ≤ (K : ℝ) * (∑' v, f v ^ 2) := by
  apply Real.tsum_le_of_sum_le
  · intro v
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  · intro s
    exact partial_neighbor_sum_le G K f hK hf s

/-- Helper: `∑' v, ‖f v‖ ^ 2 = ∑' v, f v ^ 2` in `ℝ`. -/
private lemma tsum_norm_sq_eq (f : V → ℝ) :
    (fun v : V => ‖f v‖ ^ ((2 : ℝ≥0∞).toReal))
      = (fun v : V => f v ^ 2) := by
  funext v
  have h2 : ((2 : ℝ≥0∞).toReal) = (2 : ℝ) := by simp
  rw [h2, Real.rpow_two]
  have : ‖f v‖ = |f v| := rfl
  rw [this, sq_abs]

/-- Extract the summability of `v ↦ (f v)^2` from `Memℓp f 2`. -/
private lemma summable_sq_of_memℓp_two (f : V → ℝ) (hf : Memℓp f 2) :
    Summable (fun v : V => f v ^ 2) := by
  have hp : (0 : ℝ) < ((2 : ℝ≥0∞).toReal) := by simp
  have hsumf : Summable (fun v => ‖f v‖ ^ ((2 : ℝ≥0∞).toReal)) := hf.summable hp
  rw [tsum_norm_sq_eq] at hsumf
  exact hsumf

include hK in
/-- **Q15 — stability.** `Δ` maps `ℓ²(V)` into itself. -/
theorem laplacian_memℓp_two (f : V → ℝ) (hf : Memℓp f 2) :
    Memℓp (laplacian_E G f) 2 := by
  have hsumf_sq : Summable (fun v => f v ^ 2) := summable_sq_of_memℓp_two f hf
  have h_pw : ∀ v, (laplacian_E G f v) ^ 2
      ≤ 2 * (K : ℝ)^2 * f v ^ 2
          + 2 * (K : ℝ) * ∑ w ∈ G.neighborFinset v, f w ^ 2 :=
    laplacian_sq_pointwise_bound G K hK f
  have hmajorant_sum : Summable
      (fun v => 2 * (K : ℝ)^2 * f v ^ 2
                + 2 * (K : ℝ) * ∑ w ∈ G.neighborFinset v, f w ^ 2) :=
    (hsumf_sq.mul_left _).add (summable_neighbor_sq G K f hK hsumf_sq)
  have hΔ_sum : Summable (fun v => (laplacian_E G f v) ^ 2) :=
    Summable.of_nonneg_of_le (fun v => sq_nonneg _) h_pw hmajorant_sum
  apply memℓp_gen
  rw [tsum_norm_sq_eq]
  exact hΔ_sum

include hK in
/-- **Q15 — ℓ² norm bound.** `∑' v (Δf)(v)² ≤ 4 K² · ∑' v f(v)²`. -/
theorem laplacian_l2_norm_bound (f : V → ℝ) (hf : Memℓp f 2) :
    (∑' v, (laplacian_E G f v) ^ 2) ≤ 4 * (K : ℝ)^2 * (∑' v, f v ^ 2) := by
  have hsumf_sq : Summable (fun v => f v ^ 2) := summable_sq_of_memℓp_two f hf
  have h_pw : ∀ v, (laplacian_E G f v) ^ 2
      ≤ 2 * (K : ℝ)^2 * f v ^ 2
          + 2 * (K : ℝ) * ∑ w ∈ G.neighborFinset v, f w ^ 2 :=
    laplacian_sq_pointwise_bound G K hK f
  have h_neighbor_sum : Summable
      (fun v : V => 2 * (K : ℝ) * ∑ w ∈ G.neighborFinset v, f w ^ 2) :=
    summable_neighbor_sq G K f hK hsumf_sq
  have hmajorant_sum : Summable
      (fun v => 2 * (K : ℝ)^2 * f v ^ 2
                + 2 * (K : ℝ) * ∑ w ∈ G.neighborFinset v, f w ^ 2) :=
    (hsumf_sq.mul_left _).add h_neighbor_sum
  have hΔ_sum : Summable (fun v => (laplacian_E G f v) ^ 2) :=
    Summable.of_nonneg_of_le (fun v => sq_nonneg _) h_pw hmajorant_sum
  -- Compare tsums.
  have h1 : (∑' v, (laplacian_E G f v) ^ 2)
      ≤ (∑' v : V, (2 * (K : ℝ)^2 * f v ^ 2
            + 2 * (K : ℝ) * ∑ w ∈ G.neighborFinset v, f w ^ 2)) :=
    hΔ_sum.tsum_le_tsum h_pw hmajorant_sum
  -- Split the sum.
  have h2 : (∑' v : V, (2 * (K : ℝ)^2 * f v ^ 2
            + 2 * (K : ℝ) * ∑ w ∈ G.neighborFinset v, f w ^ 2))
      = (∑' v : V, 2 * (K : ℝ)^2 * f v ^ 2)
        + (∑' v : V, 2 * (K : ℝ) * ∑ w ∈ G.neighborFinset v, f w ^ 2) :=
    (hsumf_sq.mul_left _).tsum_add h_neighbor_sum
  -- Extract constants.
  have h3 : (∑' v : V, 2 * (K : ℝ)^2 * f v ^ 2)
      = 2 * (K : ℝ)^2 * (∑' v, f v ^ 2) := tsum_mul_left
  have h4 : (∑' v : V, 2 * (K : ℝ) * ∑ w ∈ G.neighborFinset v, f w ^ 2)
      = 2 * (K : ℝ) * (∑' v : V, ∑ w ∈ G.neighborFinset v, f w ^ 2) :=
    tsum_mul_left
  -- Use the edge bound.
  have h5 := tsum_neighbor_sq_le G K f hK hsumf_sq
  have hK_nn : (0 : ℝ) ≤ 2 * (K : ℝ) := by positivity
  have htsum_sq_nn : (0 : ℝ) ≤ (∑' v, f v ^ 2) :=
    tsum_nonneg (fun _ => sq_nonneg _)
  calc (∑' v, (laplacian_E G f v) ^ 2)
      ≤ _ := h1
    _ = _ := h2
    _ = 2 * (K : ℝ)^2 * (∑' v, f v ^ 2)
          + 2 * (K : ℝ) * (∑' v : V, ∑ w ∈ G.neighborFinset v, f w ^ 2) := by
            rw [h3, h4]
    _ ≤ 2 * (K : ℝ)^2 * (∑' v, f v ^ 2)
          + 2 * (K : ℝ) * ((K : ℝ) * (∑' v, f v ^ 2)) := by
            gcongr
    _ = 4 * (K : ℝ)^2 * (∑' v, f v ^ 2) := by ring

end Q15

/-! ### Q16 — The Laplacian as a bounded operator on `ℓ²(V)` -/

section Q16

variable [LocallyFinite G] (K : ℕ) (hK : ∀ v : V, G.degree v ≤ K)

/-- The underlying `ℓ²(V) →ₗ[ℝ] ℓ²(V)` linear map induced by `Δ`. -/
noncomputable def laplacian_H_linear :
    lp (fun _ : V => ℝ) 2 →ₗ[ℝ] lp (fun _ : V => ℝ) 2 where
  toFun f :=
    ⟨laplacian_E G ((f : V → ℝ)), laplacian_memℓp_two G K hK _ (lp.memℓp f)⟩
  map_add' f g := by
    apply Subtype.ext
    funext v
    show laplacian_E G ((f + g : lp (fun _ : V => ℝ) 2) : V → ℝ) v
       = (laplacian_E G ((f : V → ℝ)) + laplacian_E G ((g : V → ℝ))) v
    have hfg : ((f + g : lp (fun _ : V => ℝ) 2) : V → ℝ)
             = (f : V → ℝ) + (g : V → ℝ) := lp.coeFn_add f g
    rw [hfg]
    show (G.degree v : ℝ) * ((f : V → ℝ) + (g : V → ℝ)) v
            - ∑ w ∈ G.neighborFinset v, ((f : V → ℝ) + (g : V → ℝ)) w
        = ((G.degree v : ℝ) * (f : V → ℝ) v - ∑ w ∈ G.neighborFinset v, (f : V → ℝ) w)
          + ((G.degree v : ℝ) * (g : V → ℝ) v - ∑ w ∈ G.neighborFinset v, (g : V → ℝ) w)
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib]
    ring
  map_smul' c f := by
    apply Subtype.ext
    funext v
    show laplacian_E G ((c • f : lp (fun _ : V => ℝ) 2) : V → ℝ) v
       = (c • laplacian_E G ((f : V → ℝ))) v
    have hcf : ((c • f : lp (fun _ : V => ℝ) 2) : V → ℝ)
             = c • (f : V → ℝ) := lp.coeFn_smul c f
    rw [hcf]
    show (G.degree v : ℝ) * (c • (f : V → ℝ)) v
            - ∑ w ∈ G.neighborFinset v, (c • (f : V → ℝ)) w
        = c * ((G.degree v : ℝ) * (f : V → ℝ) v
              - ∑ w ∈ G.neighborFinset v, (f : V → ℝ) w)
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show (∑ x ∈ G.neighborFinset v, c * (f : V → ℝ) x)
          = c * ∑ x ∈ G.neighborFinset v, (f : V → ℝ) x from
        (Finset.mul_sum _ _ _).symm]
    ring

@[simp]
lemma laplacian_H_linear_apply_coe (f : lp (fun _ : V => ℝ) 2) :
    ((laplacian_H_linear G K hK f : lp (fun _ : V => ℝ) 2) : V → ℝ)
      = laplacian_E G (f : V → ℝ) := rfl

/-- **Q16.** The Laplacian as a bounded (continuous) linear operator on
`ℓ²(V)`, with operator norm at most `2 K`. -/
noncomputable def laplacian_H :
    lp (fun _ : V => ℝ) 2 →L[ℝ] lp (fun _ : V => ℝ) 2 :=
  LinearMap.mkContinuous (laplacian_H_linear G K hK) (2 * K) <| by
    intro f
    -- `‖Δf‖² ≤ 4 K² ‖f‖²` ⇒ `‖Δf‖ ≤ 2 K ‖f‖`.
    have hp : (0 : ℝ) < ((2 : ℝ≥0∞).toReal) := by
      rw [show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) from by norm_num]; norm_num
    -- Expand `‖·‖²` on `lp _ 2`.
    have h_norm_sq_lhs :
        ‖laplacian_H_linear G K hK f‖ ^ ((2 : ℝ≥0∞).toReal)
          = ∑' v, ‖laplacian_E G ((f : V → ℝ)) v‖ ^ ((2 : ℝ≥0∞).toReal) :=
      lp.norm_rpow_eq_tsum hp _
    have h_norm_sq_rhs :
        ‖f‖ ^ ((2 : ℝ≥0∞).toReal)
          = ∑' v, ‖(f : V → ℝ) v‖ ^ ((2 : ℝ≥0∞).toReal) :=
      lp.norm_rpow_eq_tsum hp f
    have h_nat2 : ((2 : ℝ≥0∞).toReal) = (2 : ℝ) := by norm_num
    rw [h_nat2] at h_norm_sq_lhs h_norm_sq_rhs
    have h_sq_expand_lhs :
        ‖laplacian_H_linear G K hK f‖ ^ 2
          = ∑' v, (laplacian_E G ((f : V → ℝ)) v) ^ 2 := by
      have : ‖laplacian_H_linear G K hK f‖ ^ (2 : ℝ)
            = ∑' v, ‖laplacian_E G ((f : V → ℝ)) v‖ ^ (2 : ℝ) := h_norm_sq_lhs
      have hlhs' : ‖laplacian_H_linear G K hK f‖ ^ (2 : ℕ)
          = ‖laplacian_H_linear G K hK f‖ ^ (2 : ℝ) := by
        rw [show ((2 : ℝ) : ℝ) = ((2 : ℕ) : ℝ) from by norm_cast, Real.rpow_natCast]
      have hrhs' : ∀ v, ‖laplacian_E G ((f : V → ℝ)) v‖ ^ (2 : ℝ)
          = (laplacian_E G ((f : V → ℝ)) v) ^ 2 := by
        intro v
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_cast, Real.rpow_natCast]
        rw [show ‖laplacian_E G ((f : V → ℝ)) v‖ = |laplacian_E G ((f : V → ℝ)) v| from rfl]
        rw [sq_abs]
      rw [show (2 : ℕ) = 2 from rfl] at hlhs'
      rw [hlhs', this]
      exact tsum_congr hrhs'
    have h_sq_expand_rhs :
        ‖f‖ ^ 2 = ∑' v, ((f : V → ℝ) v) ^ 2 := by
      have : ‖f‖ ^ (2 : ℝ)
            = ∑' v, ‖(f : V → ℝ) v‖ ^ (2 : ℝ) := h_norm_sq_rhs
      have hlhs' : ‖f‖ ^ (2 : ℕ) = ‖f‖ ^ (2 : ℝ) := by
        rw [show ((2 : ℝ) : ℝ) = ((2 : ℕ) : ℝ) from by norm_cast, Real.rpow_natCast]
      have hrhs' : ∀ v, ‖(f : V → ℝ) v‖ ^ (2 : ℝ) = ((f : V → ℝ) v) ^ 2 := by
        intro v
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_cast, Real.rpow_natCast]
        rw [show ‖(f : V → ℝ) v‖ = |(f : V → ℝ) v| from rfl]
        rw [sq_abs]
      rw [show (2 : ℕ) = 2 from rfl] at hlhs'
      rw [hlhs', this]
      exact tsum_congr hrhs'
    have h_sq : ‖laplacian_H_linear G K hK f‖ ^ 2
        ≤ (2 * (K : ℝ)) ^ 2 * ‖f‖ ^ 2 := by
      rw [h_sq_expand_lhs, h_sq_expand_rhs]
      have := laplacian_l2_norm_bound G K hK _ (lp.memℓp f)
      have h4K : (2 * (K : ℝ)) ^ 2 = 4 * (K : ℝ)^2 := by ring
      rw [h4K]
      exact this
    -- Now take square roots.
    have hnn_lhs : 0 ≤ ‖laplacian_H_linear G K hK f‖ := norm_nonneg _
    have hnn_2K : 0 ≤ (2 * (K : ℝ)) := by positivity
    have hnn_2K_norm : 0 ≤ 2 * (K : ℝ) * ‖f‖ := mul_nonneg hnn_2K (norm_nonneg _)
    have hrewrite : (2 * (K : ℝ) * ‖f‖) ^ 2 = (2 * (K : ℝ)) ^ 2 * ‖f‖ ^ 2 := by ring
    have : (‖laplacian_H_linear G K hK f‖) ^ 2 ≤ (2 * (K : ℝ) * ‖f‖) ^ 2 := by
      rw [hrewrite]; exact h_sq
    have hfinal : ‖laplacian_H_linear G K hK f‖ ≤ 2 * (K : ℝ) * ‖f‖ := by
      have := Real.sqrt_le_sqrt this
      rwa [Real.sqrt_sq hnn_lhs, Real.sqrt_sq hnn_2K_norm] at this
    -- Goal: `‖Δf‖ ≤ 2 * ↑K * ‖f‖` (Lean has already simplified the cast).
    exact hfinal

@[simp]
lemma laplacian_H_apply_coe (f : lp (fun _ : V => ℝ) 2) :
    ((laplacian_H G K hK f : lp (fun _ : V => ℝ) 2) : V → ℝ)
      = laplacian_E G (f : V → ℝ) := rfl

/-- **Q16 (continuity).** Automatic from `laplacian_H` being a continuous
linear map. -/
theorem laplacian_H_continuous :
    Continuous (laplacian_H G K hK) :=
  (laplacian_H G K hK).continuous

end Q16

/-! ### Q17 — Edge-sum identity on `ℓ²(V)` and self-adjointness -/

section Q17

variable [LocallyFinite G] (K : ℕ) (hK : ∀ v : V, G.degree v ≤ K)

/-- **Auxiliary algebraic identity (AM-GM).**
`|x · y| ≤ (1/2) · (x² + y²)`. -/
private lemma abs_mul_le_half_sq_sum (x y : ℝ) : |x * y| ≤ (1/2) * (x ^ 2 + y ^ 2) := by
  have h := sq_nonneg (|x| - |y|)
  have habs : |x * y| = |x| * |y| := abs_mul _ _
  have h1 : (|x| - |y|) ^ 2 = |x|^2 + |y|^2 - 2 * (|x| * |y|) := by ring
  have h2 : |x| ^ 2 = x ^ 2 := sq_abs _
  have h3 : |y| ^ 2 = y ^ 2 := sq_abs _
  rw [h1, h2, h3] at h
  rw [habs]
  linarith

/-- **Auxiliary pointwise bound (AM-GM).**
For every vertex `v`, `∑_{w ∈ N(v)} |a(w) · b(v)| ≤ (1/2) ∑_{w ∈ N(v)} (a(w)² + b(v)²)`.
This avoids Cauchy–Schwarz and suffices for Fubini summability. -/
private lemma neighbor_abs_mul_le_half_sq_sum (a b : V → ℝ) (v : V) :
    ∑ w ∈ G.neighborFinset v, |a w * b v|
      ≤ (1/2) * ∑ w ∈ G.neighborFinset v, (a w ^ 2 + b v ^ 2) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun w _ => ?_)
  exact abs_mul_le_half_sq_sum (a w) (b v)

/-- **Auxiliary summability: the absolute-value "neighbor × column" sum is finite.** -/
private lemma summable_neighbor_abs_mul_of_ℓ2
    (f g : V → ℝ) (hK : ∀ v : V, G.degree v ≤ K)
    (hf : Summable (fun v => f v ^ 2)) (hg : Summable (fun v => g v ^ 2)) :
    Summable (fun v : V => ∑ w ∈ G.neighborFinset v, |f w * g v|) := by
  -- Majorise pointwise by `(1/2) (∑_{w∈N(v)} f(w)²) + (1/2) deg(v)·g(v)²`.
  have h_maj : ∀ v,
      (∑ w ∈ G.neighborFinset v, |f w * g v|)
        ≤ (1/2) * ∑ w ∈ G.neighborFinset v, (f w ^ 2 + g v ^ 2) :=
    neighbor_abs_mul_le_half_sq_sum G f g
  have h_split : ∀ v,
      ((1/2) * ∑ w ∈ G.neighborFinset v, (f w ^ 2 + g v ^ 2))
        = (1/2) * (∑ w ∈ G.neighborFinset v, f w ^ 2)
            + (1/2) * (G.degree v : ℝ) * g v ^ 2 := by
    intro v
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    have hcard : (#(G.neighborFinset v) : ℝ) = (G.degree v : ℝ) := by
      exact_mod_cast G.card_neighborFinset_eq_degree (v := v)
    rw [hcard]; ring
  -- Summability of each piece.
  have hsum_neigh : Summable (fun v : V => (1/2) * ∑ w ∈ G.neighborFinset v, f w ^ 2) := by
    have hcore : Summable (fun v : V => ∑ w ∈ G.neighborFinset v, f w ^ 2) := by
      apply summable_of_sum_le
      · intro v
        exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      · intro s
        exact partial_neighbor_sum_le G K f hK hf s
    exact hcore.mul_left _
  have hsum_deg : Summable (fun v : V => (1/2) * (G.degree v : ℝ) * g v ^ 2) := by
    -- Bound `deg(v) ≤ K`, so `(1/2) deg(v) g(v)² ≤ (K/2) g(v)²`.
    refine (hg.mul_left ((K : ℝ)/2)).of_nonneg_of_le (fun v => ?_) (fun v => ?_)
    · have : (0 : ℝ) ≤ (G.degree v : ℝ) := by positivity
      have hnn : (0 : ℝ) ≤ g v ^ 2 := sq_nonneg _
      positivity
    · have hdeg_le : (G.degree v : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK v
      have hnn : (0 : ℝ) ≤ g v ^ 2 := sq_nonneg _
      have : (1/2 : ℝ) * (G.degree v) * g v ^ 2 ≤ (1/2 : ℝ) * (K : ℝ) * g v ^ 2 := by
        have := mul_le_mul_of_nonneg_right hdeg_le (by positivity : (0:ℝ) ≤ (1/2 : ℝ) * g v ^ 2)
        nlinarith
      linarith [this]
  have hsum_maj : Summable
      (fun v : V => (1/2) * ∑ w ∈ G.neighborFinset v, (f w ^ 2 + g v ^ 2)) := by
    have := hsum_neigh.add hsum_deg
    refine this.congr (fun v => ?_)
    exact (h_split v).symm
  -- Now apply `Summable.of_nonneg_of_le`.
  exact hsum_maj.of_nonneg_of_le
    (fun v => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    (fun v => h_maj v)

/-! ### Q17 on ℓ² — Sigma-type Fubini, edge-sum identity and self-adjointness

The strategy reindexes row double sums `∑' v, Σ_{w ∈ N(v)} F(v,w)` via the
directed-edge Sigma type `Σ v : V, {w : V // w ∈ G.neighborFinset v}`.
Absolute summability on this Sigma type follows from `summable_sigma_of_nonneg`
applied to the AM-GM majorant in `summable_neighbor_abs_mul_of_ℓ2`. The
adjacency-symmetry involution `⟨v,w⟩ ↦ ⟨w,v⟩` (well-defined because
`w ∈ N(v) ↔ v ∈ N(w)`) swaps source and target, yielding the generic Fubini
identity `tsum_neighbor_swap_of_summable`. Self-adjointness follows by a
direct expansion; the edge-sum identity then follows by algebra. -/

/-- The "directed edge" Sigma type: pairs `(v, w)` with `w ∈ N(v)`. -/
private abbrev DirEdge : Type _ :=
  Σ v : V, {w : V // w ∈ G.neighborFinset v}

/-- Adjacency-symmetry swap on directed edges, `⟨v,w⟩ ↦ ⟨w,v⟩`. -/
private def dirEdgeSwap : DirEdge G → DirEdge G := fun s =>
  ⟨s.2.val, ⟨s.1, by
    rcases s with ⟨v, ⟨w, hw⟩⟩
    simp only [mem_neighborFinset] at hw ⊢
    exact hw.symm⟩⟩

private lemma dirEdgeSwap_involutive :
    Function.Involutive (dirEdgeSwap G) := by
  rintro ⟨v, ⟨w, hw⟩⟩
  rfl

/-- The swap as an involutive equivalence. -/
private def dirEdgeSwapEquiv : DirEdge G ≃ DirEdge G :=
  (dirEdgeSwap_involutive G).toPerm _

@[simp] private lemma dirEdgeSwapEquiv_apply (s : DirEdge G) :
    (dirEdgeSwapEquiv G) s = dirEdgeSwap G s := rfl

/-- Collapse the tsum over the subtype `{w // w ∈ N(v)}` to a Finset sum. -/
private lemma tsum_subtype_neighborFinset_eq_sum (v : V) (F : V → ℝ) :
    ∑' w : {w : V // w ∈ G.neighborFinset v}, F w.val
      = ∑ w ∈ G.neighborFinset v, F w := by
  classical
  rw [tsum_eq_sum (s := (G.neighborFinset v).attach)
        (f := fun w : {w : V // w ∈ G.neighborFinset v} => F w.val)
        (fun w hw => absurd (Finset.mem_attach _ w) hw)]
  exact Finset.sum_attach (G.neighborFinset v) (fun w => F w)

/-- **Generic Fubini swap** for double sums indexed by directed edges.
Given a function `F : V → V → ℝ` for which `fun s : DirEdge G ↦ F s.1 s.2.val`
is summable, the outer-inner double sum `∑' v, Σ_{w ∈ N(v)} F(v,w)` equals its
transpose `∑' v, Σ_{w ∈ N(v)} F(w,v)`. -/
private lemma tsum_neighbor_swap_of_summable
    (F : V → V → ℝ)
    (hsum : Summable (fun s : DirEdge G => F s.1 s.2.val)) :
    (∑' v : V, ∑ w ∈ G.neighborFinset v, F v w)
      = ∑' v : V, ∑ w ∈ G.neighborFinset v, F w v := by
  -- The swapped Sigma-sum is also summable (via the swap involution).
  have hsum_swap : Summable (fun s : DirEdge G => F s.2.val s.1) := by
    have h := hsum.comp_injective (dirEdgeSwapEquiv G).injective
    refine h.congr (fun s => ?_)
    rfl
  -- Each side as a Sigma tsum.
  have hLHS : (∑' v : V, ∑ w ∈ G.neighborFinset v, F v w)
      = ∑' s : DirEdge G, F s.1 s.2.val := by
    rw [hsum.tsum_sigma]
    refine tsum_congr (fun v => ?_)
    exact (tsum_subtype_neighborFinset_eq_sum G v (fun w => F v w)).symm
  have hRHS : (∑' v : V, ∑ w ∈ G.neighborFinset v, F w v)
      = ∑' s : DirEdge G, F s.2.val s.1 := by
    rw [hsum_swap.tsum_sigma]
    refine tsum_congr (fun v => ?_)
    exact (tsum_subtype_neighborFinset_eq_sum G v (fun w => F w v)).symm
  rw [hLHS, hRHS]
  rw [← (dirEdgeSwapEquiv G).tsum_eq (fun s : DirEdge G => F s.2.val s.1)]
  rfl

/-- Sigma-summability of the cross term `f(v) g(w)` whenever `f, g ∈ ℓ²`. -/
private lemma summable_dirEdge_cross
    (f g : V → ℝ) (hK : ∀ v : V, G.degree v ≤ K)
    (hf : Summable (fun v => f v ^ 2)) (hg : Summable (fun v => g v ^ 2)) :
    Summable (fun s : DirEdge G => f s.1 * g s.2.val) := by
  classical
  have habs : Summable (fun s : DirEdge G => |f s.1 * g s.2.val|) := by
    rw [summable_sigma_of_nonneg (fun _ => abs_nonneg _)]
    refine ⟨fun _ => Summable.of_finite, ?_⟩
    have hrow : Summable (fun v : V => ∑ w ∈ G.neighborFinset v, |f v * g w|) := by
      have h := summable_neighbor_abs_mul_of_ℓ2 G K g f hK hg hf
      refine h.congr (fun v => ?_)
      refine Finset.sum_congr rfl (fun w _ => ?_)
      congr 1; ring
    refine hrow.congr (fun v => ?_)
    rw [tsum_subtype_neighborFinset_eq_sum G v (fun w => |f v * g w|)]
  exact habs.of_abs

/-- Sigma-summability of the diagonal term `f(v) g(v)`. -/
private lemma summable_dirEdge_diag
    (f g : V → ℝ) (hK : ∀ v : V, G.degree v ≤ K)
    (hf : Summable (fun v => f v ^ 2)) (hg : Summable (fun v => g v ^ 2)) :
    Summable (fun s : DirEdge G => f s.1 * g s.1) := by
  classical
  have habs : Summable (fun s : DirEdge G => |f s.1 * g s.1|) := by
    rw [summable_sigma_of_nonneg (fun _ => abs_nonneg _)]
    refine ⟨fun _ => Summable.of_finite, ?_⟩
    -- Row-sum = deg(v) · |f(v) g(v)|.
    have hrow_eq : ∀ v : V,
        (∑' w : {w : V // w ∈ G.neighborFinset v}, |f v * g v|)
          = (G.degree v : ℝ) * |f v * g v| := by
      intro v
      rw [tsum_subtype_neighborFinset_eq_sum G v (fun _ => |f v * g v|)]
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : (#(G.neighborFinset v) : ℝ) = (G.degree v : ℝ) := by
        exact_mod_cast G.card_neighborFinset_eq_degree (v := v)
      rw [hcard]
    have hmaj : Summable (fun v : V => (K : ℝ) * ((1/2) * (f v ^ 2 + g v ^ 2))) := by
      refine ((hf.add hg).mul_left ((K : ℝ) * (1/2))).congr (fun v => ?_); ring
    refine hmaj.of_nonneg_of_le (fun v => ?_) (fun v => ?_)
    · have : (0 : ℝ) ≤ (1/2) * (f v ^ 2 + g v ^ 2) := by positivity
      positivity
    · rw [hrow_eq]
      have hdeg_nn : (0 : ℝ) ≤ (G.degree v : ℝ) := by positivity
      have hdeg_le : (G.degree v : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK v
      have hAMGM : |f v * g v| ≤ (1/2) * (f v ^ 2 + g v ^ 2) :=
        abs_mul_le_half_sq_sum _ _
      have hAMGM_nn : (0 : ℝ) ≤ (1/2) * (f v ^ 2 + g v ^ 2) := by positivity
      calc (G.degree v : ℝ) * |f v * g v|
          ≤ (G.degree v : ℝ) * ((1/2) * (f v ^ 2 + g v ^ 2)) :=
            mul_le_mul_of_nonneg_left hAMGM hdeg_nn
        _ ≤ (K : ℝ) * ((1/2) * (f v ^ 2 + g v ^ 2)) :=
            mul_le_mul_of_nonneg_right hdeg_le hAMGM_nn
  exact habs.of_abs

/-- Summability of the row-sum `v ↦ Σ_{w ∈ N(v)} f(v) g(w)`. -/
private lemma summable_row_cross
    (f g : V → ℝ) (hK : ∀ v : V, G.degree v ≤ K)
    (hf : Summable (fun v => f v ^ 2)) (hg : Summable (fun v => g v ^ 2)) :
    Summable (fun v : V => ∑ w ∈ G.neighborFinset v, f v * g w) := by
  have habs : Summable (fun v : V => ∑ w ∈ G.neighborFinset v, |f v * g w|) := by
    have h := summable_neighbor_abs_mul_of_ℓ2 G K g f hK hg hf
    refine h.congr (fun v => ?_)
    refine Finset.sum_congr rfl (fun w _ => ?_)
    congr 1; ring
  have hmaj_nn : ∀ v : V, 0 ≤ ∑ w ∈ G.neighborFinset v, |f v * g w| :=
    fun v => Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hbound : ∀ v : V,
      |∑ w ∈ G.neighborFinset v, f v * g w|
        ≤ ∑ w ∈ G.neighborFinset v, |f v * g w| :=
    fun v => Finset.abs_sum_le_sum_abs _ _
  refine Summable.of_abs (habs.of_nonneg_of_le ?_ ?_)
  · exact fun v => abs_nonneg _
  · exact fun v => hbound v

/-- Summability of the row-sum `v ↦ Σ_{w ∈ N(v)} f(v) g(v)`. -/
private lemma summable_row_diag
    (f g : V → ℝ) (hK : ∀ v : V, G.degree v ≤ K)
    (hf : Summable (fun v => f v ^ 2)) (hg : Summable (fun v => g v ^ 2)) :
    Summable (fun v : V => ∑ w ∈ G.neighborFinset v, f v * g v) := by
  have hcongr : ∀ v : V,
      (∑ w ∈ G.neighborFinset v, f v * g v)
        = (G.degree v : ℝ) * (f v * g v) := by
    intro v
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (#(G.neighborFinset v) : ℝ) = (G.degree v : ℝ) := by
      exact_mod_cast G.card_neighborFinset_eq_degree (v := v)
    rw [hcard]
  have habs_bound : ∀ v,
      |(G.degree v : ℝ) * (f v * g v)|
        ≤ (K : ℝ) * ((1/2) * (f v ^ 2 + g v ^ 2)) := by
    intro v
    have h1 : |(G.degree v : ℝ) * (f v * g v)|
          = (G.degree v : ℝ) * |f v * g v| := by
      rw [abs_mul]; congr 1; exact abs_of_nonneg (by positivity)
    rw [h1]
    have hdeg_le : (G.degree v : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK v
    have hdeg_nn : (0 : ℝ) ≤ (G.degree v : ℝ) := by positivity
    have hAMGM : |f v * g v| ≤ (1/2) * (f v ^ 2 + g v ^ 2) :=
      abs_mul_le_half_sq_sum _ _
    have hAMGM_nn : (0 : ℝ) ≤ (1/2) * (f v ^ 2 + g v ^ 2) := by positivity
    calc (G.degree v : ℝ) * |f v * g v|
        ≤ (G.degree v : ℝ) * ((1/2) * (f v ^ 2 + g v ^ 2)) :=
          mul_le_mul_of_nonneg_left hAMGM hdeg_nn
      _ ≤ (K : ℝ) * ((1/2) * (f v ^ 2 + g v ^ 2)) :=
          mul_le_mul_of_nonneg_right hdeg_le hAMGM_nn
  have hsum_maj : Summable (fun v : V => (K : ℝ) * ((1/2) * (f v ^ 2 + g v ^ 2))) := by
    refine ((hf.add hg).mul_left ((K : ℝ) * (1/2))).congr (fun v => ?_); ring
  have habs_sum : Summable (fun v : V => (G.degree v : ℝ) * (f v * g v)) :=
    Summable.of_abs (hsum_maj.of_nonneg_of_le (fun v => abs_nonneg _) habs_bound)
  exact habs_sum.congr (fun v => (hcongr v).symm)

/-- Pointwise expansion of `⟨f, Δg⟩` as a `tsum` of neighbour differences. -/
private lemma inner_laplacian_eq_tsum_neighbor_cross
    (f g : lp (fun _ : V => ℝ) 2) :
    @inner ℝ _ _ f (laplacian_H G K hK g)
      = ∑' v : V, ∑ w ∈ G.neighborFinset v,
          (f.1 v) * (g.1 v - g.1 w) := by
  rw [lp.inner_eq_tsum f (laplacian_H G K hK g)]
  refine tsum_congr (fun v => ?_)
  -- On ℝ, `inner a b = a * b`.
  have hinner : (inner ℝ (f.1 v) ((laplacian_H G K hK g).1 v) : ℝ)
        = f.1 v * (laplacian_H G K hK g).1 v := by
    show (laplacian_H G K hK g).1 v * f.1 v = f.1 v * (laplacian_H G K hK g).1 v
    ring
  rw [hinner]
  have hpt : (laplacian_H G K hK g).1 v = laplacian_E G g.1 v := rfl
  rw [hpt, laplacian_E_apply]
  -- f(v) * (deg(v) g(v) - Σ g(w)) = Σ f(v)(g(v) - g(w)).
  have hcard : (G.degree v : ℝ) = (#(G.neighborFinset v) : ℝ) := by
    exact_mod_cast (G.card_neighborFinset_eq_degree (v := v)).symm
  rw [hcard, mul_sub]
  rw [show (#(G.neighborFinset v) : ℝ) * g.1 v
        = ∑ _w ∈ G.neighborFinset v, g.1 v from by
      rw [Finset.sum_const, nsmul_eq_mul]]
  rw [Finset.mul_sum]
  rw [show f.1 v * (∑ w ∈ G.neighborFinset v, g.1 w)
        = ∑ w ∈ G.neighborFinset v, f.1 v * g.1 w from
      Finset.mul_sum _ _ _]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  ring

/-- **Q17 — self-adjointness.** The discrete Laplacian on `ℓ²(V)` is self-adjoint.

Proof strategy: expand `⟪Δf, g⟫` and `⟪f, Δg⟫` pointwise via
`inner_laplacian_eq_tsum_neighbor_cross`. The diagonal parts coincide by
commutativity; the cross-term parts coincide by `tsum_neighbor_swap_of_summable`
applied to `F(v,w) = g(v) f(w)`. -/
theorem laplacian_H_isSelfAdjoint :
    IsSelfAdjoint (laplacian_H G K hK) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  have hf_sum : Summable (fun v => f.1 v ^ 2) :=
    summable_sq_of_memℓp_two _ (lp.memℓp f)
  have hg_sum : Summable (fun v => g.1 v ^ 2) :=
    summable_sq_of_memℓp_two _ (lp.memℓp g)
  have hfDg := inner_laplacian_eq_tsum_neighbor_cross G K hK f g
  have hgDf := inner_laplacian_eq_tsum_neighbor_cross G K hK g f
  -- Goal: ⟪Δf, g⟫ = ⟪f, Δg⟫ (the `↑` arrow is the `→L → →ₗ` coercion).
  simp only [ContinuousLinearMap.coe_coe]
  -- Reduce LHS via real-inner symmetry to ⟪g, Δf⟫.
  rw [show (inner ℝ (laplacian_H G K hK f) g : ℝ)
        = inner ℝ g (laplacian_H G K hK f) from real_inner_comm _ _]
  rw [hgDf, hfDg]
  -- Now: ∑' v, Σ g(v)(f(v)-f(w)) = ∑' v, Σ f(v)(g(v)-g(w)).
  have hsplitF : ∀ v,
      (∑ w ∈ G.neighborFinset v, f.1 v * (g.1 v - g.1 w))
        = (∑ w ∈ G.neighborFinset v, f.1 v * g.1 v)
            - (∑ w ∈ G.neighborFinset v, f.1 v * g.1 w) := by
    intro v
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun w _ => by ring)
  have hsplitG : ∀ v,
      (∑ w ∈ G.neighborFinset v, g.1 v * (f.1 v - f.1 w))
        = (∑ w ∈ G.neighborFinset v, g.1 v * f.1 v)
            - (∑ w ∈ G.neighborFinset v, g.1 v * f.1 w) := by
    intro v
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun w _ => by ring)
  have hsumDiag_fg : Summable (fun v : V => ∑ w ∈ G.neighborFinset v, f.1 v * g.1 v) :=
    summable_row_diag G K f.1 g.1 hK hf_sum hg_sum
  have hsumDiag_gf : Summable (fun v : V => ∑ w ∈ G.neighborFinset v, g.1 v * f.1 v) :=
    hsumDiag_fg.congr (fun v => Finset.sum_congr rfl (fun w _ => by ring))
  have hsumCross_fg : Summable (fun v : V => ∑ w ∈ G.neighborFinset v, f.1 v * g.1 w) :=
    summable_row_cross G K f.1 g.1 hK hf_sum hg_sum
  have hsumCross_gf : Summable (fun v : V => ∑ w ∈ G.neighborFinset v, g.1 v * f.1 w) :=
    summable_row_cross G K g.1 f.1 hK hg_sum hf_sum
  have htsumF :
      (∑' v : V, ∑ w ∈ G.neighborFinset v, f.1 v * (g.1 v - g.1 w))
        = (∑' v : V, ∑ w ∈ G.neighborFinset v, f.1 v * g.1 v)
          - (∑' v : V, ∑ w ∈ G.neighborFinset v, f.1 v * g.1 w) := by
    rw [← hsumDiag_fg.tsum_sub hsumCross_fg]
    exact tsum_congr hsplitF
  have htsumG :
      (∑' v : V, ∑ w ∈ G.neighborFinset v, g.1 v * (f.1 v - f.1 w))
        = (∑' v : V, ∑ w ∈ G.neighborFinset v, g.1 v * f.1 v)
          - (∑' v : V, ∑ w ∈ G.neighborFinset v, g.1 v * f.1 w) := by
    rw [← hsumDiag_gf.tsum_sub hsumCross_gf]
    exact tsum_congr hsplitG
  rw [htsumF, htsumG]
  -- Diagonals match by commutativity.
  have hDiagEq : (∑' v : V, ∑ w ∈ G.neighborFinset v, g.1 v * f.1 v)
      = (∑' v : V, ∑ w ∈ G.neighborFinset v, f.1 v * g.1 v) := by
    refine tsum_congr (fun v => ?_)
    exact Finset.sum_congr rfl (fun w _ => by ring)
  rw [hDiagEq]
  -- Cross-terms match via the Sigma swap applied to F(v,w) = g(v)·f(w).
  have hSwap : (∑' v : V, ∑ w ∈ G.neighborFinset v, g.1 v * f.1 w)
      = (∑' v : V, ∑ w ∈ G.neighborFinset v, f.1 v * g.1 w) := by
    have hSum : Summable (fun s : DirEdge G => g.1 s.1 * f.1 s.2.val) :=
      summable_dirEdge_cross G K g.1 f.1 hK hg_sum hf_sum
    have := tsum_neighbor_swap_of_summable G (fun v w => g.1 v * f.1 w) hSum
    -- `this : ∑' v, Σ g(v) f(w) = ∑' v, Σ g(w) f(v)`.
    rw [this]
    refine tsum_congr (fun v => ?_)
    exact Finset.sum_congr rfl (fun w _ => by ring)
  rw [hSwap]

/-- **Q17 — edge-sum identity.** For `f, g ∈ ℓ²(V)`,
`⟨f, Δg⟩ = (1/2) · ∑' v, Σ_{w ∈ N(v)} (f(v) - f(w)) · (g(v) - g(w))`.

Proof: `⟨f, Δg⟩ = A - C` where `A = ∑' v, Σ f(v)g(v)` and `C = ∑' v, Σ f(v)g(w)`.
The edge-sum RHS, when expanded, is `A - C - D + B` with `B = ∑' v, Σ f(w)g(w)`,
`D = ∑' v, Σ f(w)g(v)`. By the Sigma swap, `A = B` (diagonal) and `C = D`
(cross). Hence `A - C - D + B = 2(A - C) = 2·⟨f, Δg⟩`, which divided by 2 gives
the claim. -/
theorem laplacian_H_edge_sum (f g : lp (fun _ : V => ℝ) 2) :
    @inner ℝ _ _ f (laplacian_H G K hK g)
      = (1/2 : ℝ) * ∑' (v : V), ∑ w ∈ G.neighborFinset v,
          (f.1 v - f.1 w) * (g.1 v - g.1 w) := by
  have hf_sum : Summable (fun v => f.1 v ^ 2) :=
    summable_sq_of_memℓp_two _ (lp.memℓp f)
  have hg_sum : Summable (fun v => g.1 v ^ 2) :=
    summable_sq_of_memℓp_two _ (lp.memℓp g)
  set A : ℝ := ∑' v : V, ∑ w ∈ G.neighborFinset v, f.1 v * g.1 v with hA_def
  set B : ℝ := ∑' v : V, ∑ w ∈ G.neighborFinset v, f.1 w * g.1 w with hB_def
  set C : ℝ := ∑' v : V, ∑ w ∈ G.neighborFinset v, f.1 v * g.1 w with hC_def
  set D : ℝ := ∑' v : V, ∑ w ∈ G.neighborFinset v, f.1 w * g.1 v with hD_def
  -- Four summabilities.
  have hsA : Summable (fun v : V => ∑ w ∈ G.neighborFinset v, f.1 v * g.1 v) :=
    summable_row_diag G K f.1 g.1 hK hf_sum hg_sum
  have hsC : Summable (fun v : V => ∑ w ∈ G.neighborFinset v, f.1 v * g.1 w) :=
    summable_row_cross G K f.1 g.1 hK hf_sum hg_sum
  have hsD : Summable (fun v : V => ∑ w ∈ G.neighborFinset v, f.1 w * g.1 v) := by
    have := summable_row_cross G K g.1 f.1 hK hg_sum hf_sum
    exact this.congr (fun v => Finset.sum_congr rfl (fun w _ => by ring))
  have hsB : Summable (fun v : V => ∑ w ∈ G.neighborFinset v, f.1 w * g.1 w) := by
    -- Via Sigma-type summability of `f(w) g(w)` and collapsing.
    -- Simpler: majorise by Σ_{w∈N(v)} (1/2)(f(w)² + g(w)²).
    have habs_bound : ∀ v,
        |∑ w ∈ G.neighborFinset v, f.1 w * g.1 w|
          ≤ ∑ w ∈ G.neighborFinset v, (1/2) * (f.1 w ^ 2 + g.1 w ^ 2) := by
      intro v
      calc |∑ w ∈ G.neighborFinset v, f.1 w * g.1 w|
          ≤ ∑ w ∈ G.neighborFinset v, |f.1 w * g.1 w| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ w ∈ G.neighborFinset v, (1/2) * (f.1 w ^ 2 + g.1 w ^ 2) := by
            refine Finset.sum_le_sum (fun w _ => ?_)
            exact abs_mul_le_half_sq_sum _ _
    have hfN : Summable (fun v : V => ∑ w ∈ G.neighborFinset v, f.1 w ^ 2) := by
      apply summable_of_sum_le
      · intro v; exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      · intro s; exact partial_neighbor_sum_le G K f.1 hK hf_sum s
    have hgN : Summable (fun v : V => ∑ w ∈ G.neighborFinset v, g.1 w ^ 2) := by
      apply summable_of_sum_le
      · intro v; exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      · intro s; exact partial_neighbor_sum_le G K g.1 hK hg_sum s
    have hmaj : Summable (fun v : V =>
        ∑ w ∈ G.neighborFinset v, (1/2) * (f.1 w ^ 2 + g.1 w ^ 2)) := by
      refine ((hfN.add hgN).mul_left (1/2)).congr (fun v => ?_)
      -- Goal: 1/2 * (Σ f² + Σ g²) = Σ (1/2) * (f² + g²).
      rw [show (∑ w ∈ G.neighborFinset v, (1/2 : ℝ) * (f.1 w ^ 2 + g.1 w ^ 2))
            = (1/2 : ℝ) * ∑ w ∈ G.neighborFinset v, (f.1 w ^ 2 + g.1 w ^ 2) from
          (Finset.mul_sum _ _ _).symm]
      rw [Finset.sum_add_distrib]
    refine Summable.of_abs ?_
    exact hmaj.of_nonneg_of_le (fun v => abs_nonneg _) habs_bound
  -- Key swaps from the generic Fubini.
  have hCD : C = D := by
    have hSum : Summable (fun s : DirEdge G => f.1 s.1 * g.1 s.2.val) :=
      summable_dirEdge_cross G K f.1 g.1 hK hf_sum hg_sum
    exact tsum_neighbor_swap_of_summable G (fun v w => f.1 v * g.1 w) hSum
  have hAB : A = B := by
    have hSum : Summable (fun s : DirEdge G => f.1 s.1 * g.1 s.1) :=
      summable_dirEdge_diag G K f.1 g.1 hK hf_sum hg_sum
    exact tsum_neighbor_swap_of_summable G (fun v _ => f.1 v * g.1 v) hSum
  -- From the inner-product formula: ⟨f, Δg⟩ = A - C.
  have hfDg := inner_laplacian_eq_tsum_neighbor_cross G K hK f g
  have hsplitF : ∀ v,
      (∑ w ∈ G.neighborFinset v, f.1 v * (g.1 v - g.1 w))
        = (∑ w ∈ G.neighborFinset v, f.1 v * g.1 v)
            - (∑ w ∈ G.neighborFinset v, f.1 v * g.1 w) := by
    intro v
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun w _ => by ring)
  have h_innerAC : @inner ℝ _ _ f (laplacian_H G K hK g) = A - C := by
    rw [hfDg, ← hsA.tsum_sub hsC]
    exact tsum_congr hsplitF
  -- Pointwise edge-sum expansion: Σ (f-fw)(g-gw) = (Σ fg) - (Σ fgw) - (Σ fwg) + (Σ fwgw).
  have hedge_pt : ∀ v,
      (∑ w ∈ G.neighborFinset v, (f.1 v - f.1 w) * (g.1 v - g.1 w))
        = (∑ w ∈ G.neighborFinset v, f.1 v * g.1 v)
          - (∑ w ∈ G.neighborFinset v, f.1 v * g.1 w)
          - (∑ w ∈ G.neighborFinset v, f.1 w * g.1 v)
          + (∑ w ∈ G.neighborFinset v, f.1 w * g.1 w) := by
    intro v
    -- Expand pointwise, then split the four finset sums.
    have hexpand : ∀ w : V,
        (f.1 v - f.1 w) * (g.1 v - g.1 w)
          = f.1 v * g.1 v - f.1 v * g.1 w - f.1 w * g.1 v + f.1 w * g.1 w :=
      fun w => by ring
    rw [show (∑ w ∈ G.neighborFinset v, (f.1 v - f.1 w) * (g.1 v - g.1 w))
          = ∑ w ∈ G.neighborFinset v,
              (f.1 v * g.1 v - f.1 v * g.1 w - f.1 w * g.1 v + f.1 w * g.1 w) from
        Finset.sum_congr rfl (fun w _ => hexpand w)]
    -- Split a four-term sum into individual finset sums.
    have hdistrib1 : ∀ w : V,
          f.1 v * g.1 v - f.1 v * g.1 w - f.1 w * g.1 v + f.1 w * g.1 w
            = (f.1 v * g.1 v - f.1 v * g.1 w) + (-(f.1 w * g.1 v) + f.1 w * g.1 w) :=
        fun w => by ring
    rw [show (∑ w ∈ G.neighborFinset v,
            (f.1 v * g.1 v - f.1 v * g.1 w - f.1 w * g.1 v + f.1 w * g.1 w))
          = ∑ w ∈ G.neighborFinset v,
              ((f.1 v * g.1 v - f.1 v * g.1 w) + (-(f.1 w * g.1 v) + f.1 w * g.1 w)) from
        Finset.sum_congr rfl (fun w _ => hdistrib1 w)]
    rw [Finset.sum_add_distrib]
    rw [show (∑ w ∈ G.neighborFinset v, (f.1 v * g.1 v - f.1 v * g.1 w))
          = (∑ w ∈ G.neighborFinset v, f.1 v * g.1 v)
              - (∑ w ∈ G.neighborFinset v, f.1 v * g.1 w) from by
        rw [← Finset.sum_sub_distrib]]
    rw [show (∑ w ∈ G.neighborFinset v, (-(f.1 w * g.1 v) + f.1 w * g.1 w))
          = (∑ w ∈ G.neighborFinset v, -(f.1 w * g.1 v))
              + (∑ w ∈ G.neighborFinset v, f.1 w * g.1 w) from
        Finset.sum_add_distrib]
    rw [show (∑ w ∈ G.neighborFinset v, -(f.1 w * g.1 v))
          = -(∑ w ∈ G.neighborFinset v, f.1 w * g.1 v) from
        Finset.sum_neg_distrib (f := fun w => f.1 w * g.1 v)]
    ring
  -- Edge-sum is summable (as sum of four summable row sums).
  have hsEdge : Summable (fun v : V =>
      ∑ w ∈ G.neighborFinset v, (f.1 v - f.1 w) * (g.1 v - g.1 w)) := by
    refine (((hsA.sub hsC).sub hsD).add hsB).congr (fun v => ?_)
    exact (hedge_pt v).symm
  -- Now compute the tsum of the edge-sum as `A - C - D + B`.
  have htsum_edge :
      (∑' v : V, ∑ w ∈ G.neighborFinset v, (f.1 v - f.1 w) * (g.1 v - g.1 w))
        = A - C - D + B := by
    calc (∑' v : V, ∑ w ∈ G.neighborFinset v, (f.1 v - f.1 w) * (g.1 v - g.1 w))
        = ∑' v : V,
            ((∑ w ∈ G.neighborFinset v, f.1 v * g.1 v)
              - (∑ w ∈ G.neighborFinset v, f.1 v * g.1 w)
              - (∑ w ∈ G.neighborFinset v, f.1 w * g.1 v)
              + (∑ w ∈ G.neighborFinset v, f.1 w * g.1 w)) := tsum_congr hedge_pt
      _ = ((∑' v, ∑ w ∈ G.neighborFinset v, f.1 v * g.1 v)
              - (∑' v, ∑ w ∈ G.neighborFinset v, f.1 v * g.1 w)
              - (∑' v, ∑ w ∈ G.neighborFinset v, f.1 w * g.1 v))
            + (∑' v, ∑ w ∈ G.neighborFinset v, f.1 w * g.1 w) := by
          rw [Summable.tsum_add ((hsA.sub hsC).sub hsD) hsB]
          rw [Summable.tsum_sub (hsA.sub hsC) hsD]
          rw [Summable.tsum_sub hsA hsC]
      _ = A - C - D + B := rfl
  -- Assemble.
  rw [h_innerAC, htsum_edge, ← hAB, ← hCD]
  ring

end Q17

end EnsX2026.Graphs
