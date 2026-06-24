import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm

/-!
# ENS/Polytechnique 2026 Math A — Section 5 Laplacian identities (Q17, Q19)

Let `G = (V, E)` be a finite simple graph with Laplacian matrix `L = D - A`,
where `D` is the diagonal degree matrix and `A` the adjacency matrix. This file
records the two keystone identities used in Section 5 of the exam.

## Q17 — edge-sum bilinear form

For every pair of real-valued functions `f, g : V → ℝ`,

  `⟨f, L g⟩ = (1/2) · ∑ u, ∑ v ∈ N(u), (f u - f v) · (g u - g v)`,

i.e. the Dirichlet bilinear form associated with the Laplacian is a sum over
ordered adjacent pairs. The factor `1/2` corrects for the double counting of
each unordered edge `{u, v}`. Specialising to `g = f` yields the usual
positive-semidefinite quadratic form.

## Q19 — kernel characterisation on connected graphs

If `G` is connected then the kernel of `L` (acting by left multiplication on
`V → ℝ`) consists exactly of the constant functions. The forward direction is
the Dirichlet-energy argument: `⟨f, L f⟩ = 0` forces `f u = f v` whenever
`u ∼ v`, hence `f` is constant along every walk; connectedness then forces
`f` to be globally constant. The reverse direction is the elementary fact
that every row of `L` sums to zero.

We reuse Mathlib's `SimpleGraph.lapMatrix` (in
`Mathlib/Combinatorics/SimpleGraph/LapMatrix.lean`) rather than redefining it;
the quadratic identity `lapMatrix_toLinearMap₂'` and the reachability
characterisation `lapMatrix_mulVec_eq_zero_iff_forall_reachable` do the heavy
lifting. The statements below therefore reduce to light rewrites plus the
passage from `Reachable` to `Connected`.

Institut Fourier, Grenoble — Kieran McShane
-/

namespace EnsX2026.Graphs

open Finset Matrix SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Q17 — bilinear edge-sum identity -/

/-- **Q17 (bilinear form).** The Dirichlet bilinear form attached to the graph
Laplacian `L = D - A` equals the half-sum of `(f u - f v)(g u - g v)` over all
ordered adjacent pairs `(u, v)`. -/
theorem laplacian_dotProduct_eq_sum_edges (f g : V → ℝ) :
    f ⬝ᵥ (G.lapMatrix ℝ *ᵥ g)
      = (1 / 2) * ∑ u, ∑ v ∈ G.neighborFinset u, (f u - f v) * (g u - g v) := by
  -- Expand `(L g) u = deg(u) · g u - ∑_{v ∼ u} g v` and split the dot product.
  have h1 : f ⬝ᵥ (G.lapMatrix ℝ *ᵥ g)
      = ∑ u, f u * (G.degree u * g u - ∑ v ∈ G.neighborFinset u, g v) := by
    simp_rw [dotProduct, lapMatrix_mulVec_apply]
  -- Polarisation: expand the symmetric identity
  -- `2·(f u - f v)(g u - g v) = 2 f u g u - f u g v - f v g u - f v g u + 2 f v g v + …`
  -- by summing over ordered neighbours.  The double sum is symmetric in `u, v`
  -- (because adjacency is), which lets us rewrite the off-diagonal pieces.
  have h_deg : ∀ u, (G.degree u : ℝ) = ∑ _v ∈ G.neighborFinset u, (1 : ℝ) := by
    intro u; simp [card_neighborFinset_eq_degree]
  -- LHS as an explicit double sum.
  have hLHS : f ⬝ᵥ (G.lapMatrix ℝ *ᵥ g)
      = ∑ u, ∑ v ∈ G.neighborFinset u, (f u * g u - f u * g v) := by
    rw [h1]
    refine Finset.sum_congr rfl ?_
    intro u _
    rw [h_deg u, Finset.sum_mul, one_mul, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro v _
    ring
  -- RHS expansion.
  have hRHS :
      ∑ u, ∑ v ∈ G.neighborFinset u, (f u - f v) * (g u - g v)
        = 2 * ∑ u, ∑ v ∈ G.neighborFinset u, (f u * g u - f u * g v) := by
    -- Expand `(f u - f v)(g u - g v)` and use adjacency symmetry to swap
    -- the cross terms.
    have expand :
        ∀ u v, (f u - f v) * (g u - g v)
          = f u * g u - f u * g v - f v * g u + f v * g v := by
      intros; ring
    -- Symmetry of the double sum over ordered adjacent pairs: swap `u ↔ v`.
    have hswap :
        ∀ h : V → V → ℝ,
          ∑ u, ∑ v ∈ G.neighborFinset u, h u v
            = ∑ u, ∑ v ∈ G.neighborFinset u, h v u := by
      intro h
      -- Rewrite both sides via an `if G.Adj · ·` predicate so we can swap
      -- indices using `Finset.sum_comm` and `adj_comm`.
      have hl : ∑ u, ∑ v ∈ G.neighborFinset u, h u v
          = ∑ u, ∑ v, if G.Adj u v then h u v else 0 := by
        refine Finset.sum_congr rfl ?_
        intro u _
        rw [← Finset.sum_filter]
        refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext v; simp [mem_neighborFinset]
      have hr : ∑ u, ∑ v ∈ G.neighborFinset u, h v u
          = ∑ u, ∑ v, if G.Adj u v then h v u else 0 := by
        refine Finset.sum_congr rfl ?_
        intro u _
        rw [← Finset.sum_filter]
        refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext v; simp [mem_neighborFinset]
      rw [hl, hr, Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro u _
      refine Finset.sum_congr rfl ?_
      intro v _
      by_cases hAdj : G.Adj u v
      · have hAdj' : G.Adj v u := hAdj.symm
        simp [hAdj, hAdj']
      · have hAdj' : ¬ G.Adj v u := fun h' => hAdj h'.symm
        simp [hAdj, hAdj']
    -- Now combine: `f u g u` and `f v g v` terms, plus the cross terms.
    calc ∑ u, ∑ v ∈ G.neighborFinset u, (f u - f v) * (g u - g v)
        = ∑ u, ∑ v ∈ G.neighborFinset u,
            (f u * g u - f u * g v - f v * g u + f v * g v) := by
          refine Finset.sum_congr rfl ?_; intros u _
          refine Finset.sum_congr rfl ?_; intros v _
          exact expand u v
      _ = (∑ u, ∑ v ∈ G.neighborFinset u, (f u * g u - f u * g v))
          + (∑ u, ∑ v ∈ G.neighborFinset u, (f v * g v - f v * g u)) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro u _
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intros v _
          ring
      _ = (∑ u, ∑ v ∈ G.neighborFinset u, (f u * g u - f u * g v))
          + (∑ u, ∑ v ∈ G.neighborFinset u, (f u * g u - f u * g v)) := by
          congr 1
          -- swap `u ↔ v` in the second sum
          have := hswap (fun u v => f v * g v - f v * g u)
          simpa using this
      _ = 2 * ∑ u, ∑ v ∈ G.neighborFinset u, (f u * g u - f u * g v) := by ring
  -- Assemble LHS = (1/2) · RHS.
  rw [hLHS, hRHS]
  ring

/-! ### Q17 specialisation — quadratic Dirichlet form -/

/-- **Q17 (quadratic form).** Specialising `f = g` in the bilinear identity
gives the classical Dirichlet energy
`⟨f, L f⟩ = (1/2) · ∑ u, ∑ v ∈ N(u), (f u - f v)^2`. -/
theorem laplacian_quadratic_form (f : V → ℝ) :
    f ⬝ᵥ (G.lapMatrix ℝ *ᵥ f)
      = (1 / 2) * ∑ u, ∑ v ∈ G.neighborFinset u, (f u - f v) ^ 2 := by
  have := laplacian_dotProduct_eq_sum_edges G f f
  simp_rw [← sq] at this
  exact this

/-- **Q17 corollary.** The Dirichlet energy is nonnegative, i.e. the Laplacian
is positive semidefinite on `V → ℝ`. -/
theorem laplacian_quadratic_form_nonneg (f : V → ℝ) :
    0 ≤ f ⬝ᵥ (G.lapMatrix ℝ *ᵥ f) := by
  rw [laplacian_quadratic_form]
  have hsum : 0 ≤ ∑ u, ∑ v ∈ G.neighborFinset u, (f u - f v) ^ 2 := by
    refine Finset.sum_nonneg (fun u _ => ?_)
    refine Finset.sum_nonneg (fun v _ => ?_)
    exact sq_nonneg _
  have h2 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  exact mul_nonneg h2 hsum

/-! ### Q19 — kernel characterisation on connected graphs -/

/-- **Q19.** On a connected graph, `L f = 0` iff `f` is constant. -/
theorem laplacian_mulVec_eq_zero_iff_const (hG : G.Connected) (f : V → ℝ) :
    G.lapMatrix ℝ *ᵥ f = 0 ↔ ∃ c, ∀ v, f v = c := by
  constructor
  · -- Forward: use the Mathlib reachability characterisation, then pick a
    -- basepoint using `Connected.nonempty` and propagate along reachability.
    intro hLf
    have hreach : ∀ i j : V, G.Reachable i j → f i = f j :=
      (lapMatrix_mulVec_eq_zero_iff_forall_reachable G).mp hLf
    -- Connectedness gives us a basepoint `v₀` with `∀ w, G.Reachable v₀ w`.
    obtain ⟨v₀, hv₀⟩ := (connected_iff_exists_forall_reachable G).mp hG
    refine ⟨f v₀, fun v => ?_⟩
    exact (hreach v₀ v (hv₀ v)).symm
  · -- Reverse: constants are killed by `L` since every row of `L` sums to 0.
    rintro ⟨c, hc⟩
    have hfconst : f = fun _ => c := funext hc
    subst hfconst
    -- `L · (fun _ => c) = c • (L · (fun _ => 1)) = 0`.
    have hone : G.lapMatrix ℝ *ᵥ (fun _ : V => (1 : ℝ)) = 0 :=
      lapMatrix_mulVec_const_eq_zero G
    have hscalar : (fun _ : V => c) = c • (fun _ : V => (1 : ℝ)) := by
      funext v; simp
    rw [hscalar, mulVec_smul, hone, smul_zero]

end EnsX2026.Graphs
