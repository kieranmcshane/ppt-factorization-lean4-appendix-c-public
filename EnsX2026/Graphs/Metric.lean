import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import EnsX2026.Graphs.LaplacianMatrix

/-!
# ENS/Polytechnique 2026 Math A — Section 4 Graph metric and Section 5 Laplacian
structure (Q9, Q10, Q11, Q18, Q20)

This file collects five questions of the 2026 ENS/X Math A exam that concern the
metric and spectral structure of a simple graph `G = (V, E)`:

* **Q9** — the reachability relation `G.Reachable` is an equivalence relation;
* **Q10** — on a connected graph, the graph distance `G.dist` satisfies the
  pseudo-metric axioms (zero iff equal, symmetry, triangle inequality);
* **Q11** — on a connected graph with distinct vertices, `1 ≤ G.dist u v`;
  hence every open ball of radius `< 1` is a singleton and the topology
  induced by the distance is discrete;
* **Q18** — the Laplacian `L` of a finite graph is Hermitian (i.e. symmetric
  for `ℝ`-valued coefficients), so it is diagonalisable by an orthonormal
  basis; on a finite connected graph with at least two vertices it is not
  surjective because its kernel contains the constant functions;
* **Q20** — the image of the Laplacian on a finite connected graph is exactly
  the hyperplane `{f : V → ℝ | ∑ v, f v = 0}`.

The bulk of the combinatorial work (edge-sum identity, Dirichlet quadratic
form, kernel = constants on connected graphs) is already handled in
`EnsX2026.Graphs.LaplacianMatrix` and in Mathlib's
`Mathlib/Combinatorics/SimpleGraph/LapMatrix.lean` and
`Mathlib/Combinatorics/SimpleGraph/Metric.lean`; this file only bundles the
results into the form requested by the exam.

Institut Fourier, Grenoble — Kieran McShane
-/

namespace EnsX2026.Graphs

open Finset Matrix SimpleGraph Module

/-! ### Q9 — reachability is an equivalence relation -/

/-- **Q9.** For any simple graph, the reachability relation is an equivalence
relation. This is a direct consequence of the Mathlib lemmas
`SimpleGraph.Reachable.refl`, `.symm`, and `.trans`. -/
theorem reachable_is_equivalence (V : Type*) (G : SimpleGraph V) :
    Equivalence G.Reachable :=
  G.reachable_is_equivalence

/-! ### Q10 — graph distance is a pseudo-metric -/

/-- **Q10.** On a connected graph, the graph distance `G.dist` satisfies the
three pseudo-metric axioms: it separates points, is symmetric, and satisfies
the triangle inequality. -/
theorem dist_is_pseudoMetric (V : Type*) (G : SimpleGraph V) (hG : G.Connected) :
    (∀ u v : V, G.dist u v = 0 ↔ u = v) ∧
    (∀ u v : V, G.dist u v = G.dist v u) ∧
    (∀ u v w : V, G.dist u w ≤ G.dist u v + G.dist v w) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v; exact hG.dist_eq_zero_iff
  · intro u v; exact SimpleGraph.dist_comm
  · intro u v w; exact hG.dist_triangle

/-! ### Q11 — induced topology is discrete -/

/-- **Q11.** On a connected graph, distinct vertices have distance at least `1`.
Equivalently, the open ball of radius `1/2` around any vertex is a singleton,
so the topology induced by viewing `G.dist` as an `ℝ`-valued distance (via the
canonical cast `ℕ ↪ ℝ`) is discrete.

We state the key combinatorial fact (`1 ≤ G.dist u v` for `u ≠ v`) which is the
content of the exam question; the passage to discreteness of the induced
topology is then immediate from the standard fact that every subset is open
whenever every singleton is open. -/
theorem graph_topology_is_discrete (V : Type*) (G : SimpleGraph V)
    (hG : G.Connected) :
    ∀ u v : V, u ≠ v → 1 ≤ G.dist u v := by
  intro u v huv
  exact hG.pos_dist_of_ne huv

/-! ### Q18 — Laplacian is Hermitian and (on ≥ 2 vertices) not surjective -/

/-- **Q18 (diagonalisability).** The Laplacian matrix of a finite graph is
Hermitian; for a real coefficient ring this means it is symmetric, hence
diagonalisable by an orthonormal basis via the real spectral theorem. -/
theorem laplacian_is_diagonalisable (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.lapMatrix ℝ).IsHermitian :=
  G.isHermitian_lapMatrix ℝ

/-- **Q18 (non-surjectivity).** On a finite connected graph with at least two
vertices, the Laplacian is not surjective as a map `(V → ℝ) → (V → ℝ)`.
The argument is rank-nullity: the kernel of `L` consists of constant functions
and is therefore at least one-dimensional; since the ambient space has
dimension `Fintype.card V ≥ 2`, the rank is at most `n - 1 < n`. -/
theorem laplacian_not_surjective (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (_hn : 2 ≤ Fintype.card V) :
    ¬ Function.Surjective (G.lapMatrix ℝ).mulVec := by
  haveI : Nonempty V := hG.nonempty
  -- Abbreviate the linear map.
  set L : (V → ℝ) →ₗ[ℝ] (V → ℝ) := (G.lapMatrix ℝ).mulVecLin with hL
  -- The constant function `1` is a nonzero element of `ker L`.
  have hconst_mem : (fun _ : V => (1 : ℝ)) ∈ LinearMap.ker L := by
    rw [LinearMap.mem_ker, hL, Matrix.mulVecLin_apply]
    exact G.lapMatrix_mulVec_const_eq_zero
  have hconst_ne : (fun _ : V => (1 : ℝ)) ≠ 0 := by
    intro h
    have h1 : (1 : ℝ) = 0 := congrFun h (Classical.arbitrary V)
    exact one_ne_zero h1
  -- Hence the kernel is not the zero submodule.
  have hker_ne_bot : LinearMap.ker L ≠ ⊥ := by
    intro hbot
    apply hconst_ne
    have hmem0 : (fun _ : V => (1 : ℝ)) ∈ (⊥ : Submodule ℝ (V → ℝ)) := hbot ▸ hconst_mem
    rwa [Submodule.mem_bot] at hmem0
  have hker_pos : 1 ≤ finrank ℝ (LinearMap.ker L) :=
    Submodule.one_le_finrank_iff.mpr hker_ne_bot
  -- Apply rank-nullity: `dim range + dim ker = dim (V → ℝ) = Fintype.card V`.
  have hrk : finrank ℝ (LinearMap.range L) + finrank ℝ (LinearMap.ker L) =
      Fintype.card V := by
    rw [L.finrank_range_add_finrank_ker]
    exact Module.finrank_fintype_fun_eq_card ℝ
  -- Therefore `dim range ≤ n - 1 < n`, so `range ≠ ⊤`.
  intro hsurj
  have hrange_top : LinearMap.range L = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    exact ⟨x, hx⟩
  have hrange_dim : finrank ℝ (LinearMap.range L) = Fintype.card V := by
    rw [hrange_top, finrank_top]
    exact Module.finrank_fintype_fun_eq_card ℝ
  -- Combine with rank-nullity: `n + dim ker = n`, forcing `dim ker = 0`.
  rw [hrange_dim] at hrk
  have hker_zero : finrank ℝ (LinearMap.ker L) = 0 := by lia
  lia

/-! ### Q20 — image of the Laplacian = functions summing to zero -/

/-- Auxiliary linear map sending `f : V → ℝ` to the scalar `∑ v, f v`. Its
kernel is exactly the hyperplane of sum-zero functions. -/
private noncomputable def sumLinearMap (V : Type*) [Fintype V] :
    (V → ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∑ v, f v
  map_add' f g := by simp [Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.mul_sum]

/-- The sum functional is surjective: given any `r : ℝ`, pick a vertex `v₀`
and take `f = r • single v₀ 1`; more simply, for nonempty `V` pick any `v₀`
and use the function that is `r` at `v₀` and zero elsewhere. -/
private lemma sumLinearMap_surjective (V : Type*) [Fintype V] [DecidableEq V]
    [Nonempty V] : Function.Surjective (sumLinearMap V) := by
  intro r
  obtain ⟨v₀⟩ := ‹Nonempty V›
  refine ⟨fun v => if v = v₀ then r else 0, ?_⟩
  simp [sumLinearMap]

/-- The sum-zero hyperplane as a submodule of `V → ℝ`. -/
private noncomputable def sumZeroSubmodule (V : Type*) [Fintype V] :
    Submodule ℝ (V → ℝ) :=
  LinearMap.ker (sumLinearMap V)

private lemma mem_sumZeroSubmodule {V : Type*} [Fintype V] (f : V → ℝ) :
    f ∈ sumZeroSubmodule V ↔ ∑ v, f v = 0 := by
  simp [sumZeroSubmodule, sumLinearMap, LinearMap.mem_ker]

/-- Dimension of the sum-zero hyperplane on a nonempty finite index type. -/
private lemma finrank_sumZeroSubmodule (V : Type*) [Fintype V] [DecidableEq V]
    [Nonempty V] :
    finrank ℝ (sumZeroSubmodule V) = Fintype.card V - 1 := by
  have hrk : finrank ℝ (LinearMap.range (sumLinearMap V)) +
      finrank ℝ (LinearMap.ker (sumLinearMap V)) = Fintype.card V := by
    rw [(sumLinearMap V).finrank_range_add_finrank_ker]
    exact Module.finrank_fintype_fun_eq_card ℝ
  have hrange : finrank ℝ (LinearMap.range (sumLinearMap V)) = 1 := by
    have hsurj := sumLinearMap_surjective V
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top]
    exact finrank_self ℝ
  rw [hrange] at hrk
  have hV : 1 ≤ Fintype.card V := Fintype.card_pos
  -- `1 + dim ker = n`, so `dim ker = n - 1`.
  change finrank ℝ (sumZeroSubmodule V) = Fintype.card V - 1
  unfold sumZeroSubmodule
  lia

/-- On a finite connected graph, the kernel of the Laplacian has dimension `1`.
This follows from Mathlib's
`SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix`
combined with the fact that a connected graph has a unique connected
component. -/
private lemma finrank_ker_lapMatrix_connected (V : Type*) [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) :
    finrank ℝ (LinearMap.ker (G.lapMatrix ℝ).toLin') = 1 := by
  classical
  rw [← G.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix]
  -- `G.Connected` gives `Preconnected`, which gives `Subsingleton ConnectedComponent`,
  -- plus `Nonempty ConnectedComponent` from `Nonempty V`, so the card is `1`.
  haveI : Subsingleton G.ConnectedComponent :=
    hG.preconnected.subsingleton_connectedComponent
  haveI : Nonempty V := hG.nonempty
  haveI : Nonempty G.ConnectedComponent :=
    ⟨G.connectedComponentMk (Classical.arbitrary V)⟩
  haveI : Unique G.ConnectedComponent := uniqueOfSubsingleton (Classical.arbitrary _)
  exact Fintype.card_unique

/-- A consequence of the previous lemma: the range of the Laplacian, viewed
through `mulVecLin`, has dimension `Fintype.card V - 1`. -/
private lemma finrank_range_lapMatrix_connected (V : Type*) [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) :
    finrank ℝ (LinearMap.range (G.lapMatrix ℝ).mulVecLin) =
      Fintype.card V - 1 := by
  -- `toLin'` and `mulVecLin` agree on a square matrix over `ℝ` up to the
  -- canonical identification `(V → ℝ) = (V →₀ ℝ).Basis` ; use the
  -- rank–nullity version on `mulVecLin` directly.
  have hrk : finrank ℝ (LinearMap.range (G.lapMatrix ℝ).mulVecLin) +
      finrank ℝ (LinearMap.ker (G.lapMatrix ℝ).mulVecLin) = Fintype.card V := by
    rw [(G.lapMatrix ℝ).mulVecLin.finrank_range_add_finrank_ker]
    exact Module.finrank_fintype_fun_eq_card ℝ
  -- The kernels of `toLin'` and `mulVecLin` coincide since both send `x ↦ M *ᵥ x`.
  have hker_eq :
      LinearMap.ker (G.lapMatrix ℝ).toLin' = LinearMap.ker (G.lapMatrix ℝ).mulVecLin := by
    ext x
    simp [LinearMap.mem_ker, Matrix.toLin'_apply]
  have hker : finrank ℝ (LinearMap.ker (G.lapMatrix ℝ).mulVecLin) = 1 := by
    rw [← hker_eq]; exact finrank_ker_lapMatrix_connected V G hG
  rw [hker] at hrk
  have hV : 1 ≤ Fintype.card V := Fintype.card_pos (h := hG.nonempty)
  lia

/-- **Key column-sum identity.** Every column of the Laplacian sums to zero.
This is the transposed version of the row-sum identity `L · 1 = 0`. -/
private lemma sum_lapMatrix_column (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    ∑ v, G.lapMatrix ℝ v u = 0 := by
  -- Use `L · 1 = 0` at vertex `u`, and transpose.
  have h : (G.lapMatrix ℝ) *ᵥ (fun _ : V => (1 : ℝ)) = 0 :=
    G.lapMatrix_mulVec_const_eq_zero
  have hu := congrFun h u
  -- `((L · 1) u) = ∑ v, L u v * 1 = ∑ v, L u v`.
  have hrow : ∑ v, G.lapMatrix ℝ u v = 0 := by
    simpa [Matrix.mulVec, dotProduct] using hu
  -- Symmetry: `L u v = L v u`.
  have hsym : (G.lapMatrix (R := ℝ)).IsSymm := G.isSymm_lapMatrix (R := ℝ)
  calc ∑ v, G.lapMatrix ℝ v u
      = ∑ v, G.lapMatrix ℝ u v := by
        refine Finset.sum_congr rfl (fun v _ => ?_)
        exact hsym.apply u v
    _ = 0 := hrow

/-- **Q20 (⊆).** Every vector in the image of the Laplacian has sum zero. -/
private lemma range_lapMatrix_subset_sumZero (V : Type*) [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    LinearMap.range (G.lapMatrix ℝ).mulVecLin ≤ sumZeroSubmodule V := by
  intro g hg
  rw [mem_sumZeroSubmodule]
  obtain ⟨f, hf⟩ := hg
  subst hf
  -- `∑ v (L f) v = ∑ v ∑ u, L v u * f u = ∑ u, (∑ v, L v u) * f u = 0`.
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero ?_
  intro u _
  rw [← Finset.sum_mul, sum_lapMatrix_column V G u, zero_mul]

/-- **Q20.** On a finite connected graph, the image of the Laplacian equals
the hyperplane of functions summing to zero. -/
theorem laplacian_range_eq_sum_zero (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) :
    Set.range (G.lapMatrix ℝ).mulVec = {f : V → ℝ | ∑ v, f v = 0} := by
  -- Work with submodules.
  have hrange_sub : LinearMap.range (G.lapMatrix ℝ).mulVecLin = sumZeroSubmodule V := by
    haveI : Nonempty V := hG.nonempty
    apply Submodule.eq_of_le_of_finrank_eq
    · exact range_lapMatrix_subset_sumZero V G
    · rw [finrank_range_lapMatrix_connected V G hG, finrank_sumZeroSubmodule V]
  -- Cast to `Set`.
  ext g
  constructor
  · rintro ⟨f, rfl⟩
    have : (G.lapMatrix ℝ).mulVecLin f ∈ sumZeroSubmodule V := by
      rw [← hrange_sub]
      exact ⟨f, rfl⟩
    rw [mem_sumZeroSubmodule] at this
    exact this
  · intro hg
    have hg' : g ∈ sumZeroSubmodule V := by
      rw [mem_sumZeroSubmodule]; exact hg
    rw [← hrange_sub] at hg'
    obtain ⟨f, hf⟩ := hg'
    exact ⟨f, hf⟩

end EnsX2026.Graphs
