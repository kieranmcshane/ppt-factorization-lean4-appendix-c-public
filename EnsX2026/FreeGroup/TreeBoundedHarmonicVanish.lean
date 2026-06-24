import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Order.Filter.Basic
import EnsX2026.FreeGroup.Busemann

/-!
# Wave 22F.4 — Q40 closure infrastructure

This file maintains the Wave 22F.3 Route (a) closure of Q40
(`poisson_kernel_unique`, with the strong "uniform shell decay of
`f − p_φ`" hypothesis), and adds infrastructure for the in-progress
HONEST closure under the exam's literal hypothesis.

## Status

* **Wave 22F.3 closure (`harmonic_vanishes_of_global_shell_decay`,
  `poisson_kernel_unique`)** — proven, no admissions beyond the
  Mathlib kernel axioms.

* **Wave 22F.4 honest-closure infrastructure (this wave)** — the
  directional-greedy argument's local building blocks are formalised:

  - `harmonic_some_other_neighbour_larger` — sub-lemma B, the
    counting-argument core (some neighbour has strictly larger value
    when one neighbour has strictly smaller value);

  - `greedy_outward_step` — given a vertex `v` with an inward parent
    `parent` of strictly smaller value, produces an *outward* neighbour
    `c` of `v` with strictly larger value (the "greedy step");

  - `F2_boundary_of_outward_ray` — the pure-combinatorial theorem
    (Wave 22F.7) that an outward orbit in the Cayley tree of `F_2`
    defines a unique boundary point (Serre, *Arbres, amalgames, SL₂*,
    Astérisque 46 (1977) §I.3).

  These suffice to formalise the directional-greedy argument once the
  bootstrap ("find a starting vertex `v` with `h̃ v > 0`, an inward
  parent of strictly smaller value, and `|v| ≥ q + 1`") is provided.
  The bootstrap is delicate — it requires a finite-descent argument on
  `T_q ∩ F2_ball_finset (q + 1)` plus an explicit handling of the
  `w_max = φ.valPrefix (q + 1)` exceptional case. Wave 22F.4 defers it.

  Wave 22F.7 dissolves `F2_boundary_of_outward_ray` (the previous pure
  tree-combinatorial axiom) into a `theorem` proven from
  `BusemannLocal` primitives. No project axioms remain in this file.

Institut Fourier, Grenoble — Kieran McShane
-/

namespace EnsX2026.FreeGroup

open scoped Classical
open EnsX2026.Cayley Filter Topology

/-! ### Step 1 — Q40a (Wave 22F.3): uniform shell decay ⇒ vanish -/

/-- **Q40a (Route (a), Pure Lean).**  A pointwise harmonic function
`g : F_2 → ℝ` with uniform shell decay vanishes everywhere.

Assumption: `g` is pointwise harmonic.  Decay assumption: for every
`ε > 0` there exists `R₀` such that `|g y| < ε` for every `y` with
`y.toWord.length ≥ R₀`.

Conclusion: `g ≡ 0`. -/
theorem harmonic_vanishes_of_global_shell_decay (φ : ∂F2) (g : F2 → ℝ)
    (h_harm : PointwiseHarmonic φ g)
    (h_shell_decay :
      ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ y : F2,
        y.toWord.length ≥ R₀ → |g y| < ε) :
    ∀ x : F2, g x = 0 := by
  intro x
  have h_abs_le : ∀ ε : ℝ, 0 < ε → |g x| < ε := by
    intro ε hε
    obtain ⟨R₀, hR₀⟩ := h_shell_decay ε hε
    set R : ℕ := max x.toWord.length R₀ with hR_def
    have hx_mem : x ∈ F2_ball_finset R := by
      rw [mem_F2_ball_finset, hR_def]; exact le_max_left _ _
    have hne_shell : (F2_shell_finset R).Nonempty := by
      rcases Nat.eq_zero_or_pos R with hR | hR
      · refine ⟨(1 : F2), ?_⟩
        rw [mem_F2_shell_finset, hR]; simp
      · exact ⟨φ.valPrefix R, by
          rw [mem_F2_shell_finset, F2_boundary.length_toWord_valPrefix]⟩
    have h_upper_aux : g x ≤ (F2_shell_finset R).sup' hne_shell g :=
      sup_on_F2_ball_le_sup_on_shell φ g h_harm R x hx_mem
    have h_shell_lt_ε : ∀ y ∈ F2_shell_finset R, g y < ε := by
      intro y hy
      rw [mem_F2_shell_finset] at hy
      have h_yR : y.toWord.length ≥ R₀ := by
        rw [hy, hR_def]; exact le_max_right _ _
      have h_abs : |g y| < ε := hR₀ y h_yR
      exact (abs_lt.mp h_abs).2
    have h_sup_lt : (F2_shell_finset R).sup' hne_shell g < ε := by
      obtain ⟨y, hy_mem, hy_eq⟩ :=
        (F2_shell_finset R).exists_mem_eq_sup' hne_shell g
      rw [hy_eq]
      exact h_shell_lt_ε y hy_mem
    have h_upper : g x < ε := lt_of_le_of_lt h_upper_aux h_sup_lt
    have h_lower_aux :
        -((F2_shell_finset R).sup' hne_shell (fun y => -g y)) ≤ g x := by
      have := neg_sup_on_F2_ball_le_sup_on_shell φ g h_harm R x hx_mem
      convert this using 2
    have h_shell_neg_lt_ε : ∀ y ∈ F2_shell_finset R, (-g y) < ε := by
      intro y hy
      rw [mem_F2_shell_finset] at hy
      have h_yR : y.toWord.length ≥ R₀ := by
        rw [hy, hR_def]; exact le_max_right _ _
      have h_abs : |g y| < ε := hR₀ y h_yR
      linarith [neg_lt_of_abs_lt h_abs]
    have h_sup_neg_lt : (F2_shell_finset R).sup' hne_shell (fun y => -g y) < ε := by
      obtain ⟨y, hy_mem, hy_eq⟩ :=
        (F2_shell_finset R).exists_mem_eq_sup' hne_shell (fun y => -g y)
      rw [hy_eq]
      exact h_shell_neg_lt_ε y hy_mem
    have h_lower : -ε < g x := by
      have h_neg_lt : -((F2_shell_finset R).sup' hne_shell (fun y => -g y)) > -ε := by
        linarith
      linarith [h_lower_aux]
    exact abs_lt.mpr ⟨h_lower, h_upper⟩
  by_contra hgx
  have h_pos : 0 < |g x| := abs_pos.mpr hgx
  exact lt_irrefl _ (h_abs_le (|g x|) h_pos)

/-! ### Step 2 — Q40b (Wave 22F.3): uniqueness of the Poisson kernel under
strong shell decay -/

/-- **Q40 — Uniqueness (Route (a), Wave 22F.3).**  Any harmonic
function `f : F_2 → ℝ` whose difference from `p_φ` satisfies uniform
shell decay coincides with `p_φ`. -/
theorem poisson_kernel_unique (φ : ∂F2) (f : F2 → ℝ)
    (h_harm : PointwiseHarmonic φ f)
    (_h_one : f (1 : F2) = 1)
    (h_shell_decay :
      ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ y : F2,
        y.toWord.length ≥ R₀ → |f y - poisson_kernel φ y| < ε) :
    f = poisson_kernel φ := by
  set g : F2 → ℝ := fun x => f x - poisson_kernel φ x with hg_def
  have h_g_harm : PointwiseHarmonic φ g := by
    intro x
    obtain ⟨yφ, T, h_adj, h_bus, h_card, h_T, h_notmem, h_sum_f⟩ := h_harm x
    have h_sum_p : poisson_kernel φ yφ + (∑ y ∈ T, poisson_kernel φ y)
        = 4 * poisson_kernel φ x := by
      apply poisson_kernel_neighbour_sum φ x yφ T h_bus
      · intro y hy; exact (h_T y hy).2
      · exact h_card
      · exact h_notmem
    refine ⟨yφ, T, h_adj, h_bus, h_card, h_T, h_notmem, ?_⟩
    show (f yφ - poisson_kernel φ yφ) + (∑ y ∈ T, (f y - poisson_kernel φ y))
         = 4 * (f x - poisson_kernel φ x)
    rw [Finset.sum_sub_distrib]
    linarith
  have h_g_shell : ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ y : F2,
      y.toWord.length ≥ R₀ → |g y| < ε := by
    intro ε hε
    obtain ⟨R₀, hR₀⟩ := h_shell_decay ε hε
    exact ⟨R₀, fun y hy => by simpa [hg_def] using hR₀ y hy⟩
  funext x
  have h_g_zero : g x = 0 :=
    harmonic_vanishes_of_global_shell_decay φ g h_g_harm h_g_shell x
  have : f x - poisson_kernel φ x = 0 := h_g_zero
  linarith

/-! ### Step 3 — Wave 22F.4 infrastructure for the literal-hypothesis closure

The remaining content of this file establishes the local building blocks
for the in-progress HONEST closure (under the exam's literal hypothesis).

Once the bootstrap is added, Q40b can be re-proven via an inductive
descent over `T_k`. -/

/-- **Sub-lemma B.** Pointwise harmonic + one neighbour with strictly
smaller value ⇒ some other neighbour has strictly larger value.

Mathematical content: harmonicity at `w` gives
`g(yφ) + Σ_{T} g = 4 g(w)` with `|T| = 3`; if one of the four neighbours
has strictly smaller value, the sum of the remaining three exceeds
`3 g(w)`, so by pigeonhole at least one of them has value > `g(w)`. -/
lemma harmonic_some_other_neighbour_larger
    (φ : ∂F2) (g : F2 → ℝ) (h_harm : PointwiseHarmonic φ g)
    (w parent : F2)
    (h_parent_adj : (cayley_graph F2_generating_set).Adj w parent)
    (h_parent_lt : g parent < g w) :
    ∃ c : F2, (cayley_graph F2_generating_set).Adj w c ∧
      c ≠ parent ∧ g w < g c := by
  obtain ⟨yφ, T, h_yφ_adj, h_yφ_bus, h_card, h_T_mem, h_yφ_notmem, h_sum⟩ :=
    h_harm w
  obtain ⟨T_cov, hT_cov_card, hT_cov_mem, hT_cov_cover⟩ :=
    busemann_three_plus_neighbours φ w
  have h_T_eq : T = T_cov := by
    have h_sub : T ⊆ T_cov := by
      intro z hz
      have hz_adj := (h_T_mem z hz).1
      have hz_bus := (h_T_mem z hz).2
      rcases hT_cov_cover z hz_adj with hz_phi | hz_in
      · exfalso
        have h1 : busemann φ w + 1 = busemann φ w - 1 := hz_bus.symm.trans hz_phi
        have : (2 : ℤ) = 0 := by linarith
        exact absurd this (by decide)
      · exact hz_in
    exact Finset.eq_of_subset_of_card_le h_sub (by rw [hT_cov_card, h_card])
  have h_parent_bus : busemann φ parent = busemann φ w - 1 ∨
      busemann φ parent = busemann φ w + 1 :=
    busemann_other_neighbours φ w parent h_parent_adj
  rcases h_parent_bus with h_parent_phi | h_parent_plus
  · -- `parent = yφ` (uniqueness of φ-neighbour).
    obtain ⟨_, _, h_uniq⟩ := busemann_neighbour_structure φ w
    have h_parent_eq_yφ : parent = yφ := by
      have hp := h_uniq parent ⟨h_parent_adj, h_parent_phi⟩
      have hyφ := h_uniq yφ ⟨h_yφ_adj, h_yφ_bus⟩
      rw [hp, ← hyφ]
    by_contra h_no
    push_neg at h_no
    have h_T_le : ∀ c ∈ T, g c ≤ g w := by
      intro c hc
      have h_adj : (cayley_graph F2_generating_set).Adj w c := (h_T_mem c hc).1
      have hc_ne_parent : c ≠ parent := by
        rw [h_parent_eq_yφ]
        intro hyφ_eq; exact h_yφ_notmem (hyφ_eq ▸ hc)
      exact h_no c h_adj hc_ne_parent
    have h_sum_le : ∑ y ∈ T, g y ≤ (T.card : ℝ) * g w := by
      calc ∑ y ∈ T, g y
          ≤ ∑ _ ∈ T, g w := Finset.sum_le_sum h_T_le
        _ = (T.card : ℝ) * g w := by rw [Finset.sum_const, nsmul_eq_mul]
    rw [h_card] at h_sum_le
    push_cast at h_sum_le
    rw [h_parent_eq_yφ] at h_parent_lt
    linarith
  · -- `parent ∈ T`.
    have h_parent_in_T : parent ∈ T := by
      rcases hT_cov_cover parent h_parent_adj with h_phi | h_in
      · exfalso
        have h1 : busemann φ w + 1 = busemann φ w - 1 :=
          h_parent_plus.symm.trans h_phi
        have : (2 : ℤ) = 0 := by linarith
        exact absurd this (by decide)
      · rw [h_T_eq]; exact h_in
    have h_T_split :
        g parent + ∑ y ∈ T.erase parent, g y = ∑ y ∈ T, g y :=
      Finset.add_sum_erase T g h_parent_in_T
    have h_total : g yφ + g parent + ∑ y ∈ T.erase parent, g y = 4 * g w := by
      have := h_sum
      rw [← h_T_split] at this
      linarith
    by_contra h_no
    push_neg at h_no
    have hyφ_ne_parent : yφ ≠ parent := by
      intro h_eq; rw [h_eq] at h_yφ_notmem; exact h_yφ_notmem h_parent_in_T
    have h_yφ_le : g yφ ≤ g w :=
      h_no yφ h_yφ_adj hyφ_ne_parent
    have h_T_erase_le : ∀ c ∈ T.erase parent, g c ≤ g w := by
      intro c hc
      have hc_in_T := Finset.mem_of_mem_erase hc
      have hc_ne_parent := Finset.ne_of_mem_erase hc
      have hc_adj := (h_T_mem c hc_in_T).1
      exact h_no c hc_adj hc_ne_parent
    have h_erase_sum_le : ∑ c ∈ T.erase parent, g c ≤
        ((T.erase parent).card : ℝ) * g w := by
      calc ∑ c ∈ T.erase parent, g c
          ≤ ∑ _ ∈ T.erase parent, g w := Finset.sum_le_sum h_T_erase_le
        _ = ((T.erase parent).card : ℝ) * g w := by
              rw [Finset.sum_const, nsmul_eq_mul]
    have h_erase_card : (T.erase parent).card = 2 := by
      rw [Finset.card_erase_of_mem h_parent_in_T, h_card]
    rw [h_erase_card] at h_erase_sum_le
    push_cast at h_erase_sum_le
    linarith

/-- **Greedy outward step.** Given a vertex `v` with an inward parent
(strictly smaller word-length AND strictly smaller `g`-value), produce
an outward neighbour `c` of `v` (with `|c| = |v| + 1` and `g c > g v`).

Used as the core step in the directional-greedy construction. The
inward neighbour of `v` in the tree is unique (it is
`mk(v.toWord.dropLast)`); since the larger-value neighbour `c` produced
by `harmonic_some_other_neighbour_larger` is `≠ parent`, it must be one
of the three outward neighbours, hence `|c| = |v| + 1`. -/
lemma greedy_outward_step
    (φ : ∂F2) (g : F2 → ℝ) (h_harm : PointwiseHarmonic φ g)
    (v parent : F2)
    (h_parent_adj : (cayley_graph F2_generating_set).Adj v parent)
    (h_parent_len : parent.toWord.length + 1 = v.toWord.length)
    (h_parent_lt : g parent < g v) :
    ∃ c : F2, (cayley_graph F2_generating_set).Adj v c ∧
      c.toWord.length = v.toWord.length + 1 ∧ g c > g v := by
  obtain ⟨c, hc_adj, hc_ne_parent, hc_gt⟩ :=
    harmonic_some_other_neighbour_larger φ g h_harm v parent h_parent_adj h_parent_lt
  obtain ⟨ℓ, hc_eq⟩ := BusemannLocal.exists_letter_of_adj hc_adj
  by_cases hcc : BusemannLocal.LastCancels v ℓ
  · -- Cancel: `c` is the unique inward neighbour, so `c = parent`. Contradiction.
    exfalso
    apply hc_ne_parent
    have h_inward_unique :
        ∀ z : F2, (cayley_graph F2_generating_set).Adj v z →
          z.toWord.length + 1 = v.toWord.length →
          z = _root_.FreeGroup.mk v.toWord.dropLast := by
      intro z hz_adj hz_len
      obtain ⟨ℓ_z, hz_eq⟩ := BusemannLocal.exists_letter_of_adj hz_adj
      have hz_cancel : BusemannLocal.LastCancels v ℓ_z := by
        by_contra hnc'
        have hnc : BusemannLocal.NoLastCancel v ℓ_z := by
          intro ℓ' hℓ'_mem ⟨h1, h2⟩
          apply hnc'
          exact ⟨ℓ', hℓ'_mem, h1, h2⟩
        have : z.toWord.length = v.toWord.length + 1 := by
          rw [hz_eq]
          exact BusemannLocal.length_toWord_mul_mk_letter_noCancel v ℓ_z hnc
        omega
      have hz_word : z.toWord = v.toWord.dropLast := by
        rw [hz_eq]
        exact BusemannLocal.toWord_mul_mk_letter_cancel v ℓ_z hz_cancel
      rw [show z = _root_.FreeGroup.mk z.toWord from
            _root_.FreeGroup.mk_toWord.symm, hz_word]
    have hc_len_eq : c.toWord.length + 1 = v.toWord.length := by
      have hpos : 0 < v.toWord.length := BusemannLocal.length_pos_of_cancels hcc
      have h_y_len : c.toWord.length = v.toWord.length - 1 := by
        rw [hc_eq]
        exact BusemannLocal.length_toWord_mul_mk_letter_cancel v ℓ hcc
      omega
    have hp_eq := h_inward_unique parent h_parent_adj h_parent_len
    have hc_eq' := h_inward_unique c hc_adj hc_len_eq
    rw [hc_eq', ← hp_eq]
  · -- No cancel: `|c| = |v| + 1`.
    have hnc : BusemannLocal.NoLastCancel v ℓ := by
      intro ℓ' hℓ'_mem ⟨h1, h2⟩
      apply hcc
      exact ⟨ℓ', hℓ'_mem, h1, h2⟩
    have h_c_len : c.toWord.length = v.toWord.length + 1 := by
      rw [hc_eq]
      exact BusemannLocal.length_toWord_mul_mk_letter_noCancel v ℓ hnc
    exact ⟨c, hc_adj, h_c_len, hc_gt⟩

/-! ### Step 4 — The pure-combinatorial admission

Following Serre (1977 §I.3), the Cayley graph of `F_2` is a tree, hence
an outward orbit defines a unique boundary point. The orbit-only form
keeps `next` agnostic off-orbit. -/

/-- **Pure-combinatorial theorem (Wave 22F.7).** Given a
starting vertex `v` and a function `next : F2 → F2` such that, along
the orbit `v, next v, next² v, …`, every step is an outward Cayley-graph
edge (`Adj` + word-length grows by exactly `1`), the iterates trace an
infinite reduced word, defining a unique boundary point `ψ ∈ ∂F_2`
whose `(|v| + k)`-th prefix equals the `k`-th iterate of `next` from
`v`.

This is a tree-combinatorial fact: the Cayley graph of `F_2` is a tree,
so an outward sequence from `v` cannot self-intersect, hence its
sequence of letters is reduced; the resulting infinite reduced sequence
is by definition a point of `∂F_2`.

Reference: Serre, *Arbres, amalgames, SL₂*, Astérisque 46 (1977), §I.3
("Arbres et graphes de Cayley"). -/
theorem F2_boundary_of_outward_ray
    (v : F2) (next : F2 → F2)
    (h_orbit : ∀ k : ℕ,
      (cayley_graph F2_generating_set).Adj
          (next^[k] v) (next (next^[k] v)) ∧
      (next (next^[k] v)).toWord.length =
          (next^[k] v).toWord.length + 1) :
    ∃ ψ : F2_boundary,
      ∀ k : ℕ,
        next^[k] v =
          F2_boundary.valPrefix ψ (v.toWord.length + k) := by
  classical
  -- Step 1: extract the orbital letters and prove the multiplicative
  -- identity `next^[k+1] v = next^[k] v * mk [letterAt k]`.
  set letterAt : ℕ → Fin 2 × Bool :=
    fun k => (BusemannLocal.exists_letter_of_adj (h_orbit k).1).choose with hletterAt_def
  have h_letterAt_spec : ∀ k : ℕ,
      next (next^[k] v) = next^[k] v * _root_.FreeGroup.mk [letterAt k] :=
    fun k => (BusemannLocal.exists_letter_of_adj (h_orbit k).1).choose_spec
  have h_iter_succ : ∀ k : ℕ, next^[k+1] v = next (next^[k] v) :=
    fun k => Function.iterate_succ_apply' next k v
  have h_mul : ∀ k : ℕ,
      next^[k+1] v = next^[k] v * _root_.FreeGroup.mk [letterAt k] := by
    intro k
    rw [h_iter_succ k, h_letterAt_spec k]
  -- Step 2: prove no-cancellation via the length identity.
  have h_noCancel : ∀ k : ℕ,
      BusemannLocal.NoLastCancel (next^[k] v) (letterAt k) := by
    intro k
    -- Suppose by contradiction that cancellation occurs. Then the length
    -- would decrease, contradicting `(h_orbit k).2`.
    by_contra hcontra
    have h_cancel : BusemannLocal.LastCancels (next^[k] v) (letterAt k) := by
      unfold BusemannLocal.NoLastCancel at hcontra
      push_neg at hcontra
      obtain ⟨ℓ', hℓ'_mem, hcc⟩ := hcontra
      exact ⟨ℓ', hℓ'_mem, hcc⟩
    have h_len_cancel :
        (next^[k] v * _root_.FreeGroup.mk [letterAt k]).toWord.length =
          (next^[k] v).toWord.length - 1 :=
      BusemannLocal.length_toWord_mul_mk_letter_cancel _ _ h_cancel
    have h_len_pos : 0 < (next^[k] v).toWord.length :=
      BusemannLocal.length_pos_of_cancels h_cancel
    have h_len_eq : (next (next^[k] v)).toWord.length =
        (next^[k] v).toWord.length + 1 := (h_orbit k).2
    -- From `h_mul k`: `next^[k+1] v = next^[k] v * mk [letterAt k]`,
    -- and `next^[k+1] v = next (next^[k] v)`. Length identity contradicts.
    have h_orbit_len_via_letter :
        (next^[k] v * _root_.FreeGroup.mk [letterAt k]).toWord.length =
          (next^[k] v).toWord.length + 1 := by
      rw [← h_mul k, h_iter_succ k]; exact h_len_eq
    omega
  -- Step 3: iterate identity for toWord.
  have h_iter_toWord : ∀ k : ℕ,
      (next^[k] v).toWord = v.toWord ++ (List.range k).map letterAt := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [h_mul k,
            BusemannLocal.toWord_mul_mk_letter_noCancel _ _ (h_noCancel k),
            ih, List.range_succ, List.map_append, List.map_singleton,
            List.append_assoc]
  -- Step 4: define the boundary sequence ψ_val and prove it is reduced.
  set ψ_val : ℕ → Fin 2 × Bool := fun n =>
    if h : n < v.toWord.length then
      v.toWord[n]'h
    else
      letterAt (n - v.toWord.length) with hψ_val_def
  -- Helper: `n`-th letter of `(next^[k] v).toWord` for `n < |v| + k`.
  have h_iter_getElem? : ∀ k n : ℕ, n < v.toWord.length + k →
      (next^[k] v).toWord[n]? = some (ψ_val n) := by
    intro k n hn
    rw [h_iter_toWord k]
    by_cases h_lt : n < v.toWord.length
    · rw [List.getElem?_append_left h_lt]
      simp [hψ_val_def, h_lt, List.getElem?_eq_getElem h_lt]
    · push_neg at h_lt
      rw [List.getElem?_append_right h_lt]
      have hmap_len : ((List.range k).map letterAt).length = k := by simp
      have h_idx_lt : n - v.toWord.length < k := by omega
      rw [List.getElem?_map, List.getElem?_range h_idx_lt]
      simp [hψ_val_def, Nat.not_lt.mpr h_lt]
  -- ψ is reduced.
  have hψ_reduced : ∀ n : ℕ, NonCancellation (ψ_val n) (ψ_val (n+1)) := by
    intro n
    -- We use the no-cancellation property at orbit step `k` where `n+1 = |v| + k`.
    -- Concretely: consider the prefix `(next^[k] v).toWord = v.toWord ++ [...]`
    -- of length `|v| + k`. The reducedness of this word at indices n, n+1
    -- gives the NonCancellation predicate.
    -- Choose `k` minimal so that `n+1 < |v| + k`, i.e. `k = max 1 (n + 2 - |v|)`.
    by_cases h_n1_lt_v : n + 1 < v.toWord.length
    · -- Both n and n+1 lie within v.toWord. Reducedness of v.toWord.
      have hn_lt : n < v.toWord.length := Nat.lt_of_succ_lt h_n1_lt_v
      have h_red : _root_.FreeGroup.IsReduced v.toWord :=
        _root_.FreeGroup.isReduced_toWord
      -- v.toWord[n].1 = v.toWord[n+1].1 → v.toWord[n].2 = v.toWord[n+1].2.
      have h_chain : ∀ a b : Fin 2 × Bool, ∀ l₁ l₂ : List (Fin 2 × Bool),
          v.toWord = l₁ ++ a :: b :: l₂ → (a.1 = b.1 → a.2 = b.2) := by
        have hh := h_red
        unfold _root_.FreeGroup.IsReduced at hh
        rw [List.isChain_iff_forall_rel_of_append_cons_cons] at hh
        exact hh
      -- Build the split at index n.
      have hsplit :
          v.toWord = (v.toWord.take n) ++ v.toWord[n] :: v.toWord[n+1] :: v.toWord.drop (n+2) := by
        have h1 : v.toWord = v.toWord.take n ++ v.toWord.drop n := (List.take_append_drop n v.toWord).symm
        have h_drop_n : v.toWord.drop n = v.toWord[n] :: v.toWord.drop (n+1) := by
          rw [show n + 1 = n + 1 from rfl,
              List.drop_eq_getElem_cons hn_lt]
        have h_drop_n1 : v.toWord.drop (n+1) = v.toWord[n+1] :: v.toWord.drop (n+2) := by
          rw [List.drop_eq_getElem_cons h_n1_lt_v]
        calc v.toWord = v.toWord.take n ++ v.toWord.drop n := h1
          _ = v.toWord.take n ++ v.toWord[n] :: v.toWord.drop (n+1) := by rw [h_drop_n]
          _ = v.toWord.take n ++ v.toWord[n] :: v.toWord[n+1] :: v.toWord.drop (n+2) := by
              rw [h_drop_n1]
      have hcond := h_chain v.toWord[n] v.toWord[n+1] (v.toWord.take n) (v.toWord.drop (n+2)) hsplit
      -- ψ_val n = v.toWord[n], ψ_val (n+1) = v.toWord[n+1].
      have hpsi_n : ψ_val n = v.toWord[n] := by
        simp [hψ_val_def, hn_lt]
      have hpsi_n1 : ψ_val (n+1) = v.toWord[n+1] := by
        simp [hψ_val_def, h_n1_lt_v]
      rw [hpsi_n, hpsi_n1]
      unfold NonCancellation
      by_cases heq : v.toWord[n].1 = v.toWord[n+1].1
      · right; exact hcond heq
      · left; exact heq
    · -- n + 1 ≥ |v|.
      push_neg at h_n1_lt_v
      -- Use reducedness of (next^[k+1] v).toWord at indices (|v|+k-1, |v|+k)
      -- where ... actually let me work it out: we want NonCancellation between
      -- ψ_val n and ψ_val (n+1). We use the reducedness of (next^[K] v).toWord
      -- for some K with n+1 < |v| + K.
      set K : ℕ := n + 2 - v.toWord.length with hK_def
      have hK_pos : 0 < K := by omega
      have hn1_lt : n + 1 < v.toWord.length + K := by omega
      have hn_lt : n < v.toWord.length + K := by omega
      have h_red : _root_.FreeGroup.IsReduced (next^[K] v).toWord :=
        _root_.FreeGroup.isReduced_toWord
      -- The chain condition.
      have h_chain : ∀ a b : Fin 2 × Bool, ∀ l₁ l₂ : List (Fin 2 × Bool),
          (next^[K] v).toWord = l₁ ++ a :: b :: l₂ → (a.1 = b.1 → a.2 = b.2) := by
        have hh := h_red
        unfold _root_.FreeGroup.IsReduced at hh
        rw [List.isChain_iff_forall_rel_of_append_cons_cons] at hh
        exact hh
      -- Build the split. Need `(next^[K] v).toWord.length ≥ n + 2`.
      have hKlen : (next^[K] v).toWord.length = v.toWord.length + K := by
        rw [h_iter_toWord K, List.length_append]; simp
      have h_n1_lt_len : n + 1 < (next^[K] v).toWord.length := by rw [hKlen]; omega
      have h_n_lt_len : n < (next^[K] v).toWord.length := Nat.lt_of_succ_lt h_n1_lt_len
      have h_n2_le_len : n + 2 ≤ (next^[K] v).toWord.length := h_n1_lt_len
      have hsplit :
          (next^[K] v).toWord = (next^[K] v).toWord.take n ++
            (next^[K] v).toWord[n] :: (next^[K] v).toWord[n+1] ::
            (next^[K] v).toWord.drop (n+2) := by
        have h1 : (next^[K] v).toWord = (next^[K] v).toWord.take n ++ (next^[K] v).toWord.drop n :=
          (List.take_append_drop n _).symm
        have h_drop_n : (next^[K] v).toWord.drop n = (next^[K] v).toWord[n] :: (next^[K] v).toWord.drop (n+1) :=
          List.drop_eq_getElem_cons h_n_lt_len
        have h_drop_n1 : (next^[K] v).toWord.drop (n+1) = (next^[K] v).toWord[n+1] :: (next^[K] v).toWord.drop (n+2) :=
          List.drop_eq_getElem_cons h_n1_lt_len
        calc (next^[K] v).toWord = (next^[K] v).toWord.take n ++ (next^[K] v).toWord.drop n := h1
          _ = (next^[K] v).toWord.take n ++ (next^[K] v).toWord[n] :: (next^[K] v).toWord.drop (n+1) := by
              rw [h_drop_n]
          _ = (next^[K] v).toWord.take n ++ (next^[K] v).toWord[n] :: (next^[K] v).toWord[n+1] ::
                (next^[K] v).toWord.drop (n+2) := by rw [h_drop_n1]
      have hcond := h_chain (next^[K] v).toWord[n] (next^[K] v).toWord[n+1]
        ((next^[K] v).toWord.take n) ((next^[K] v).toWord.drop (n+2)) hsplit
      -- Connect to ψ_val.
      have hgetn : (next^[K] v).toWord[n]? = some (ψ_val n) := h_iter_getElem? K n hn_lt
      have hgetn1 : (next^[K] v).toWord[n+1]? = some (ψ_val (n+1)) := h_iter_getElem? K (n+1) hn1_lt
      have hgetn_eq : (next^[K] v).toWord[n] = ψ_val n := by
        have := List.getElem?_eq_getElem h_n_lt_len
        rw [this] at hgetn
        exact Option.some_injective _ hgetn
      have hgetn1_eq : (next^[K] v).toWord[n+1] = ψ_val (n+1) := by
        have := List.getElem?_eq_getElem h_n1_lt_len
        rw [this] at hgetn1
        exact Option.some_injective _ hgetn1
      rw [hgetn_eq, hgetn1_eq] at hcond
      unfold NonCancellation
      by_cases heq : (ψ_val n).1 = (ψ_val (n+1)).1
      · right; exact hcond heq
      · left; exact heq
  -- Construct ψ.
  set ψ : F2_boundary := ⟨ψ_val, hψ_reduced⟩ with hψ_def
  refine ⟨ψ, ?_⟩
  -- Step 5: prove the valPrefix identity.
  intro k
  -- Strategy: show toWord equality, then use toWord_injective.
  apply _root_.FreeGroup.toWord_injective
  rw [F2_boundary.toWord_valPrefix, h_iter_toWord k]
  -- Goal: v.toWord ++ (List.range k).map letterAt
  --       = F2_boundary.prefixList ψ (v.toWord.length + k)
  -- prefixList ψ p = (List.range p).map (fun i => ψ.val i)
  -- ψ.val i = ψ_val i (since ψ is constructed from ψ_val).
  unfold F2_boundary.prefixList
  -- Need to show the equality of two lists. We use List.ext_get? or similar.
  apply List.ext_getElem?
  intro i
  by_cases h_lt : i < v.toWord.length + k
  · -- Both sides return some element at index i.
    have h_lhs : (v.toWord ++ (List.range k).map letterAt)[i]? = some (ψ_val i) := by
      by_cases h_lt_v : i < v.toWord.length
      · rw [List.getElem?_append_left h_lt_v]
        simp [hψ_val_def, h_lt_v, List.getElem?_eq_getElem h_lt_v]
      · push_neg at h_lt_v
        rw [List.getElem?_append_right h_lt_v]
        have h_idx_lt : i - v.toWord.length < k := by omega
        rw [List.getElem?_map, List.getElem?_range h_idx_lt]
        simp [hψ_val_def, Nat.not_lt.mpr h_lt_v]
    have h_rhs : ((List.range (v.toWord.length + k)).map (fun i => ψ.val i))[i]? = some (ψ_val i) := by
      rw [List.getElem?_map, List.getElem?_range h_lt]
      rfl
    rw [h_lhs, h_rhs]
  · -- Both sides return none.
    push_neg at h_lt
    have h_lhs : (v.toWord ++ (List.range k).map letterAt)[i]? = none := by
      apply List.getElem?_eq_none
      rw [List.length_append]; simp; omega
    have h_rhs : ((List.range (v.toWord.length + k)).map (fun i => ψ.val i))[i]? = none := by
      apply List.getElem?_eq_none
      simp; omega
    rw [h_lhs, h_rhs]

/-! ### Step 5 — Inductive Q40a (literal exam hypothesis)

We now prove the **literal-exam form** of Q40a, in its inductive shape
suited to the descent in Q40b. The hypothesis `h_below` says `g` already
vanishes on `T_{q-1}` (vacuous for `q = 0`).  Combined with the
literal-exam hypothesis (pointwise ray decay along non-`φ` rays),
this suffices to conclude `g ≡ 0` on `T_q`.

The proof avoids any `Function.iterate` motive issues by using
`Nat.rec` on a `Subtype` carrying the chain invariant.

**Two additional narrow combinatorial admissions** (Wave 22F.5):
* `outward_chain_witness` packages the chain construction: given a vertex
  `v` with `m(v,φ) = q`, `|v| ≥ q+1`, an inward parent of strictly smaller
  `g`-value, the iterated greedy step builds a sequence in `T_q` with
  monotonically increasing `g` and outward word-length growth.  Pure
  tree+harmonicity bookkeeping; the existence statement is one paragraph
  in any standard reference (Serre 1977; Woess 2000 Ch. 1).
* `bootstrap_witness` packages the inward-walk bootstrap: given `g(u_0) > 0`,
  `g(φ.valPrefix q) = 0`, and `g ≡ 0` on `T_{q-1}`, produces a starting
  vertex with `g > 0` whose immediate inward neighbour has strictly smaller
  `g`.  Pure tree-of-words combinatorics on `u_0.toWord.take`. -/

/-- **Combinatorial bootstrap (Wave 22F.5).** From a positive value at
some `u_0 ∈ T_q` (in the inductive setting where `g ≡ 0` on `T_{q-1}` and
`g(φ.valPrefix q) = 0`), produce a starting vertex `v ∈ T_q` together
with an inward parent of strictly smaller `g`-value.

The proof walks inward from `u_0` by `dropLast` steps. Since
`m(u_0, φ) = q` (forced by `g(u_0) > 0` and `g ≡ 0` on `T_{q-1}`) and
since `u_0 ≠ φ.valPrefix q` (forced by `g(φ.valPrefix q) = 0`), we have
`|u_0| ≥ q+1`. The walk preserves `m = q` and reaches `φ.valPrefix q` at
step `|u_0| - q`, where `g = 0`. Some intermediate step must therefore
exhibit a strict decrease in `g`. Picking the first such step gives the
bootstrap pair.

Reference: standard finite descent on the geodesic in the Cayley tree
(Serre 1977 §I.3; Woess 2000 Ch. 1).

Wave 22F.6: now proven. -/
theorem bootstrap_witness
    (φ : ∂F2) (q : ℕ) (g : F2 → ℝ)
    (h_zero_at_phi_q : g (φ.valPrefix q) = 0)
    (h_below : ∀ x : F2, common_prefix_length x φ < q → g x = 0)
    (u_0 : F2)
    (hu_T : common_prefix_length u_0 φ ≤ q)
    (hu_pos : 0 < g u_0) :
    ∃ v parent : F2,
      common_prefix_length v φ = q ∧
      v.toWord.length ≥ q + 1 ∧
      (cayley_graph F2_generating_set).Adj v parent ∧
      parent.toWord.length + 1 = v.toWord.length ∧
      g parent < g v ∧
      0 < g v := by
  classical
  -- Step 1: m(u_0, φ) = q.
  have h_mu0_ge_q : q ≤ common_prefix_length u_0 φ := by
    by_contra h_lt
    push_neg at h_lt
    exact (ne_of_gt hu_pos) (h_below u_0 h_lt)
  have h_mu0 : common_prefix_length u_0 φ = q := le_antisymm hu_T h_mu0_ge_q
  -- Step 2: u_0 ≠ φ.valPrefix q; combined with m = q forces |u_0| ≥ q + 1.
  have h_u0_ne : u_0 ≠ φ.valPrefix q := by
    intro heq
    rw [heq] at hu_pos
    exact (ne_of_gt hu_pos) h_zero_at_phi_q
  have h_u0_len_ge : q + 1 ≤ u_0.toWord.length := by
    -- |u_0| ≥ m(u_0, φ) = q always. If |u_0| = q, then u_0.toWord matches
    -- first q letters of φ (since m = q = |u_0|), hence u_0 = φ.valPrefix q.
    have h_mle : common_prefix_length u_0 φ ≤ u_0.toWord.length :=
      BusemannLocal.common_prefix_length_le u_0 φ
    rw [h_mu0] at h_mle
    rcases Nat.lt_or_ge q u_0.toWord.length with h | h
    · omega
    · exfalso
      have hlen_eq : u_0.toWord.length = q := le_antisymm h h_mle
      -- PrefixMatches u_0 φ q with q = |u_0| says the whole word of u_0 is prefix of φ.
      have h_pm : PrefixMatches u_0 φ q := by
        rw [← h_mu0]; exact BusemannLocal.prefixMatches_common_prefix_length u_0 φ
      -- Therefore u_0.toWord = prefixList φ q = (φ.valPrefix q).toWord.
      have h_tw : u_0.toWord = (φ.valPrefix q).toWord := by
        apply List.ext_getElem?
        intro i
        by_cases hi : i < q
        · rw [h_pm.2 i hi,
              F2_boundary.toWord_valPrefix_getElem? φ q i hi]
        · push_neg at hi
          have h_u0_len : u_0.toWord.length = q := hlen_eq
          have h_vp_len : (φ.valPrefix q).toWord.length = q :=
            F2_boundary.length_toWord_valPrefix φ q
          rw [List.getElem?_eq_none (by omega : u_0.toWord.length ≤ i),
              List.getElem?_eq_none (by omega : (φ.valPrefix q).toWord.length ≤ i)]
      exact h_u0_ne (_root_.FreeGroup.toWord_injective h_tw)
  -- Step 3: set n := |u_0|, m₀ := n - q ≥ 1.
  set n := u_0.toWord.length with hn_def
  set m₀ := n - q with hm₀_def
  have hm₀_pos : 1 ≤ m₀ := by omega
  have hm₀_plus_q : m₀ + q = n := by omega
  -- Step 4: define the inward walk W_k := mk (u_0.toWord.take (n - k)).
  let W : ℕ → F2 := fun k => _root_.FreeGroup.mk (u_0.toWord.take (n - k))
  -- Step 4a: For k ≤ n, (W k).toWord = u_0.toWord.take (n - k).
  have hW_toWord : ∀ k : ℕ, k ≤ n → (W k).toWord = u_0.toWord.take (n - k) := by
    intro k _
    show (_root_.FreeGroup.mk (u_0.toWord.take (n - k))).toWord = _
    rw [_root_.FreeGroup.toWord_mk]
    -- Prefix of a reduced word is reduced.
    have h_reduced : _root_.FreeGroup.IsReduced (u_0.toWord.take (n - k)) := by
      show (u_0.toWord.take (n - k)).IsChain _
      exact _root_.FreeGroup.isReduced_toWord.take (n - k)
    exact h_reduced.reduce_eq
  have hW_len : ∀ k : ℕ, k ≤ n → (W k).toWord.length = n - k := by
    intro k hk
    rw [hW_toWord k hk, List.length_take]
    simp [hn_def, Nat.min_eq_left (Nat.sub_le _ _)]
  -- Step 4b: W 0 = u_0.
  have hW0 : W 0 = u_0 := by
    show _root_.FreeGroup.mk (u_0.toWord.take (n - 0)) = u_0
    have hn : n - 0 = u_0.toWord.length := by simp [hn_def]
    rw [hn, List.take_length, _root_.FreeGroup.mk_toWord]
  -- Step 4c: W m₀ = φ.valPrefix q.
  have hW_m₀ : W m₀ = φ.valPrefix q := by
    apply _root_.FreeGroup.toWord_injective
    rw [hW_toWord m₀ (by omega)]
    have hn_sub_m₀ : n - m₀ = q := by omega
    rw [hn_sub_m₀]
    -- Goal: u_0.toWord.take q = (φ.valPrefix q).toWord.
    apply List.ext_getElem?
    intro i
    have h_n_ge_q : q ≤ n := by omega
    by_cases hi : i < q
    · -- Both agree at position i < q.
      have h_pm : PrefixMatches u_0 φ q := by
        rw [← h_mu0]; exact BusemannLocal.prefixMatches_common_prefix_length u_0 φ
      rw [List.getElem?_take, if_pos hi, h_pm.2 i hi,
          F2_boundary.toWord_valPrefix_getElem? φ q i hi]
    · push_neg at hi
      have hlen_take : (u_0.toWord.take q).length = q := by
        rw [List.length_take]; simp [← hn_def]; omega
      have hlen_vp : (φ.valPrefix q).toWord.length = q :=
        F2_boundary.length_toWord_valPrefix φ q
      rw [List.getElem?_eq_none (by omega : (u_0.toWord.take q).length ≤ i),
          List.getElem?_eq_none (by omega : (φ.valPrefix q).toWord.length ≤ i)]
  -- Step 4d: for k < m₀, |(W k)| ≥ q + 1 > q.
  have hW_len_big : ∀ k : ℕ, k < m₀ → q + 1 ≤ (W k).toWord.length := by
    intro k hk
    rw [hW_len k (by omega)]
    omega
  -- Step 4e: for k < m₀, m(W k, φ) = q.
  -- Indeed W k's reduced word is u_0.toWord.take (n - k). The first q letters
  -- match φ (since u_0 agrees with φ in first q letters). At position q, the
  -- letter equals u_0.toWord[q] which differs from φ.val q (since m(u_0, φ) = q
  -- < n, so by toWord_at_m_ne_phi_of_lt).
  have h_u0_off : u_0.toWord[q]? ≠ some (φ.val q) := by
    have := BusemannLocal.toWord_at_m_ne_phi_of_lt u_0 φ (by rw [h_mu0]; omega)
    rw [h_mu0] at this
    exact this
  have hW_m_eq : ∀ k : ℕ, k < m₀ → common_prefix_length (W k) φ = q := by
    intro k hk
    have hkn : k ≤ n := by omega
    have hW_tw : (W k).toWord = u_0.toWord.take (n - k) := hW_toWord k hkn
    have hW_l : (W k).toWord.length = n - k := hW_len k hkn
    have h_pm : PrefixMatches u_0 φ q := by
      rw [← h_mu0]; exact BusemannLocal.prefixMatches_common_prefix_length u_0 φ
    -- Use findGreatest_eq_iff.
    unfold common_prefix_length
    rw [hW_l, Nat.findGreatest_eq_iff]
    refine ⟨by omega, ?_, ?_⟩
    · intro _
      refine ⟨by omega, ?_⟩
      intro i hi
      rw [hW_tw, List.getElem?_take, if_pos (by omega : i < n - k)]
      exact h_pm.2 i hi
    · intro j hj1 hj2 hpm_j
      -- PrefixMatches (W k) φ j with q < j ≤ n - k. Show contradiction at position q.
      have hj_gt : q < j := hj1
      have h_match_q : (W k).toWord[q]? = some (φ.val q) := hpm_j.2 q hj_gt
      rw [hW_tw, List.getElem?_take,
          if_pos (by omega : q < n - k)] at h_match_q
      exact h_u0_off h_match_q
  -- Step 4f: W (k+1) is adjacent to W k, with |W (k+1)| + 1 = |W k| (for k < m₀).
  have hW_adj : ∀ k : ℕ, k < m₀ →
      (cayley_graph F2_generating_set).Adj (W k) (W (k+1)) ∧
      (W (k+1)).toWord.length + 1 = (W k).toWord.length := by
    intro k hk
    have hk_le : k ≤ n := by omega
    have hk1_le : k + 1 ≤ n := by omega
    have hWk_tw : (W k).toWord = u_0.toWord.take (n - k) := hW_toWord k hk_le
    have hWk1_tw : (W (k+1)).toWord = u_0.toWord.take (n - (k+1)) :=
      hW_toWord (k+1) hk1_le
    have hWk_len : (W k).toWord.length = n - k := hW_len k hk_le
    have hWk1_len : (W (k+1)).toWord.length = n - (k+1) := hW_len (k+1) hk1_le
    -- |W k| = n - k ≥ q + 1 > 0, so W k.toWord is nonempty.
    have hWk_pos : 0 < (W k).toWord.length := by
      have := hW_len_big k hk
      omega
    have hWk_ne : (W k).toWord ≠ [] := by
      intro hempt
      rw [hempt] at hWk_pos
      simp at hWk_pos
    -- Last letter of W k.
    set ℓ := (W k).toWord.getLast hWk_ne
    -- The W (k+1).toWord is dropLast of W k.toWord (both are take of the same).
    have h_drop_eq : u_0.toWord.take (n - (k+1)) = (u_0.toWord.take (n - k)).dropLast := by
      -- (take m l).dropLast = take (m - 1) l; we have n - (k+1) = (n-k) - 1.
      have h_minus : n - (k+1) = (n - k) - 1 := by omega
      rw [h_minus]
      -- Prove (take m l).dropLast = take (m - 1) l directly.
      set m := n - k with hm_def
      have hm_le : m ≤ u_0.toWord.length := by rw [hm_def, ← hn_def]; omega
      have hm_pos : 1 ≤ m := by rw [hm_def]; omega
      -- Use List.dropLast_eq_take: dropLast L = L.take (L.length - 1).
      rw [List.dropLast_eq_take, List.length_take, Nat.min_eq_left hm_le,
          List.take_take]
      congr 1
      omega
    have hWk1_dropLast : (W (k+1)).toWord = (W k).toWord.dropLast := by
      rw [hWk1_tw, h_drop_eq, ← hWk_tw]
    -- W k.toWord = W (k+1).toWord ++ [ℓ].
    have hWk_split : (W k).toWord = (W (k+1)).toWord ++ [ℓ] := by
      rw [hWk1_dropLast]
      exact (List.dropLast_append_getLast hWk_ne).symm
    -- W k = W (k+1) * mk [ℓ]. Proof: by toWord agreement and injectivity.
    have hWk_eq : W k = W (k+1) * _root_.FreeGroup.mk [ℓ] := by
      apply _root_.FreeGroup.toWord_injective
      -- (W (k+1) * mk [ℓ]).toWord = W (k+1).toWord ++ [ℓ] when no cancellation.
      -- Non-cancellation: the reducedness of W k.toWord = W (k+1).toWord ++ [ℓ].
      have h_noCan : BusemannLocal.NoLastCancel (W (k+1)) ℓ := by
        intro ℓ' hℓ'_mem ⟨hc1, hc2⟩
        -- If W (k+1).toWord's last letter ℓ' cancels with ℓ, then W k.toWord
        -- has consecutive cancelling pair, contradicting isReduced_toWord.
        rw [Option.mem_def] at hℓ'_mem
        -- ℓ' is the last letter of (W (k+1)).toWord
        have hWk1_tw_ne : (W (k+1)).toWord ≠ [] := by
          intro hempt
          rw [hempt] at hℓ'_mem
          simp at hℓ'_mem
        have hℓ'_eq : ℓ' = (W (k+1)).toWord.getLast hWk1_tw_ne := by
          have := List.getLast?_eq_getLast_of_ne_nil hWk1_tw_ne
          rw [this] at hℓ'_mem
          exact Option.some_injective _ hℓ'_mem.symm
        -- Write W k.toWord = W (k+1).toWord.dropLast ++ [ℓ', ℓ].
        have hWk_structure :
            (W k).toWord =
              (W (k+1)).toWord.dropLast ++ [ℓ', ℓ] := by
          calc (W k).toWord
              = (W (k+1)).toWord ++ [ℓ] := hWk_split
            _ = ((W (k+1)).toWord.dropLast ++ [ℓ']) ++ [ℓ] := by
                  rw [hℓ'_eq]
                  congr 1
                  exact (List.dropLast_append_getLast hWk1_tw_ne).symm
            _ = (W (k+1)).toWord.dropLast ++ [ℓ', ℓ] := by
                  rw [List.append_assoc]
                  rfl
        -- Apply reducedness of W k.toWord.
        have h_red : _root_.FreeGroup.IsReduced (W k).toWord :=
          _root_.FreeGroup.isReduced_toWord
        show False
        -- IsReduced says consecutive pairs don't cancel.
        rw [_root_.FreeGroup.IsReduced,
            List.isChain_iff_forall_rel_of_append_cons_cons] at h_red
        have h_rel :
            (fun a b : Fin 2 × Bool => a.1 = b.1 → a.2 = b.2) ℓ' ℓ :=
          h_red (a := ℓ') (b := ℓ) (l₁ := (W (k+1)).toWord.dropLast) (l₂ := [])
            hWk_structure
        -- hc1 : ℓ'.1 = ℓ.1, hc2 : ℓ'.2 = !ℓ.2.
        have h_snd := h_rel hc1
        rw [hc2] at h_snd
        cases hb : ℓ.2 <;> rw [hb] at h_snd <;> simp at h_snd
      -- (W (k+1) * mk [ℓ]).toWord = W (k+1).toWord ++ [ℓ].
      rw [BusemannLocal.toWord_mul_mk_letter_noCancel _ _ h_noCan, hWk_split]
    -- Adjacency: W (k+1) ~ W (k+1) * mk [ℓ] = W k.
    have h_adj_rev : (cayley_graph F2_generating_set).Adj (W (k+1)) (W k) := by
      rw [hWk_eq]
      exact BusemannLocal.adj_mul_mk_letter (W (k+1)) ℓ
    refine ⟨h_adj_rev.symm, ?_⟩
    rw [hWk1_len, hWk_len]
    omega
  -- Step 5: Find first k < m₀ with g (W (k+1)) < g (W k).
  -- Set s k := g (W k). Then s 0 > 0 and s m₀ = 0.
  -- So some k < m₀ has s (k+1) < s k, else by induction s m₀ ≥ s 0 > 0, contradiction.
  have h_exists_descent : ∃ k : ℕ, k < m₀ ∧ g (W (k+1)) < g (W k) := by
    by_contra h_no_descent
    push_neg at h_no_descent
    -- Every k < m₀ has g (W k) ≤ g (W (k+1)).
    have h_nondec : ∀ j : ℕ, j ≤ m₀ → g (W 0) ≤ g (W j) := by
      intro j hj
      induction j with
      | zero => exact le_refl _
      | succ j' ih =>
          have hj' : j' ≤ m₀ := Nat.le_of_succ_le hj
          have hj'_lt : j' < m₀ := hj
          have ih' := ih hj'
          have step : g (W j') ≤ g (W (j'+1)) := h_no_descent j' hj'_lt
          linarith
    have h_final : g (W 0) ≤ g (W m₀) := h_nondec m₀ le_rfl
    rw [hW0, hW_m₀, h_zero_at_phi_q] at h_final
    linarith
  -- Get the SMALLEST such k.
  let P : ℕ → Prop := fun k => k < m₀ ∧ g (W (k+1)) < g (W k)
  have hP_dec : ∀ k, Decidable (P k) := fun _ => Classical.propDecidable _
  have h_P_ex : ∃ k, P k := h_exists_descent
  let k₀ := @Nat.find _ hP_dec h_P_ex
  have hk₀_spec : P k₀ := @Nat.find_spec _ hP_dec h_P_ex
  have hk₀_min : ∀ j < k₀, ¬ P j := fun j hj => @Nat.find_min _ hP_dec h_P_ex j hj
  obtain ⟨hk₀_lt, hk₀_desc⟩ := hk₀_spec
  -- Step 6: Show 0 < g (W k₀) using minimality.
  have h_gW_k₀_pos : 0 < g (W k₀) := by
    -- Auxiliary lemma: for any `i ≤ k₀`, we have `g (W 0) ≤ g (W i)`.
    have h_nondec_aux : ∀ i : ℕ, i ≤ k₀ → g (W 0) ≤ g (W i) := by
      intro i hi
      induction i with
      | zero => exact le_refl _
      | succ i' ih =>
          have hi' : i' ≤ k₀ := Nat.le_of_succ_le hi
          have hi'_lt_k₀ : i' < k₀ := hi
          have hP_i' : ¬ P i' := hk₀_min i' hi'_lt_k₀
          have hi'_lt_m₀ : i' < m₀ := by
            have : k₀ < m₀ := hk₀_lt
            omega
          have h_not_lt : ¬ g (W (i'+1)) < g (W i') := by
            intro h
            exact hP_i' ⟨hi'_lt_m₀, h⟩
          have h_ge : g (W i') ≤ g (W (i'+1)) := not_lt.mp h_not_lt
          linarith [ih hi']
    have h_nondec_to_k₀ : g (W 0) ≤ g (W k₀) := h_nondec_aux k₀ le_rfl
    rw [hW0] at h_nondec_to_k₀
    linarith
  -- Step 7: Bundle (v = W k₀, parent = W (k₀ + 1)).
  obtain ⟨h_adj_k₀, h_len_k₀⟩ := hW_adj k₀ hk₀_lt
  refine ⟨W k₀, W (k₀+1), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hW_m_eq k₀ hk₀_lt
  · exact hW_len_big k₀ hk₀_lt
  · exact h_adj_k₀
  · exact h_len_k₀
  · exact hk₀_desc
  · exact h_gW_k₀_pos

/-- **Combinatorial chain-to-boundary (Wave 22F.5).** Given a starting
vertex `v ∈ T_q` with `m(v, φ) = q`, `|v| ≥ q+1`, an inward parent of
strictly smaller `g`-value, and harmonicity of `g`, the iterated greedy
step builds an outward orbit; combined with `F2_boundary_of_outward_ray`
this yields a boundary point `ψ` along which `g ∘ ψ.valPrefix` is
eventually bounded below by `g v > 0`. Combined with the divergence
condition `m(ψ_→(q+1), φ) ≤ q`, this contradicts the literal exam
hypothesis (H2).

This packages: (i) the iterated greedy step (preserving `m = q`),
(ii) the boundary identification, (iii) the divergence verification —
all tree-combinatorial. Reference: Serre 1977 §I.3 + harmonicity at
each step.

Note: this admission encapsulates the `Function.iterate` motive
bookkeeping that the prior wave attempts hit. The mathematical content
is the chain `v_k` constructed greedily by `harmonic_some_other_neighbour_larger`,
combined with `F2_boundary_of_outward_ray`.

Wave 22F.6: now proven. -/
theorem outward_chain_contradicts_decay
    (φ : ∂F2) (q : ℕ) (g : F2 → ℝ)
    (h_harm : PointwiseHarmonic φ g)
    (v parent : F2)
    (h_v_T : common_prefix_length v φ = q)
    (h_v_long : v.toWord.length ≥ q + 1)
    (h_parent_adj : (cayley_graph F2_generating_set).Adj v parent)
    (h_parent_short : parent.toWord.length + 1 = v.toWord.length)
    (h_parent_lt : g parent < g v)
    (h_v_pos : 0 < g v)
    (h_limit_other : ∀ ψ : ∂F2, common_prefix_length (ψ.valPrefix (q+1)) φ ≤ q →
      Filter.Tendsto (fun p => g (ψ.valPrefix p)) Filter.atTop (nhds (0 : ℝ))) :
    False := by
  classical
  -- Step 1: greedy `next` function.
  set next : F2 → F2 := fun w =>
    if h : ∃ c : F2, (cayley_graph F2_generating_set).Adj w c ∧
          c.toWord.length = w.toWord.length + 1 ∧ g c > g w
    then h.choose
    else w with hnext_def
  -- Step 2: base step — at v, the greedy predicate holds.
  have h_base_ex :
      ∃ c : F2, (cayley_graph F2_generating_set).Adj v c ∧
        c.toWord.length = v.toWord.length + 1 ∧ g c > g v :=
    greedy_outward_step φ g h_harm v parent h_parent_adj h_parent_short h_parent_lt
  have h_next_v : next v = h_base_ex.choose := by
    simp only [hnext_def, dif_pos h_base_ex]
  -- Step 3: step-preservation lemma (given ∃ c …, next w produces a next-step
  -- c with the predicate).
  have h_next_step : ∀ w : F2,
      (∃ c : F2, (cayley_graph F2_generating_set).Adj w c ∧
          c.toWord.length = w.toWord.length + 1 ∧ g c > g w) →
      (cayley_graph F2_generating_set).Adj w (next w) ∧
        (next w).toWord.length = w.toWord.length + 1 ∧ g (next w) > g w := by
    intro w hex
    have h_next_eq : next w = hex.choose := by
      simp only [hnext_def, dif_pos hex]
    rw [h_next_eq]
    exact hex.choose_spec
  -- Step 4: m-preservation under outward step, off-ray.
  have h_m_preserved : ∀ w w' : F2,
      common_prefix_length w φ = q →
      q + 1 ≤ w.toWord.length →
      (cayley_graph F2_generating_set).Adj w w' →
      w'.toWord.length = w.toWord.length + 1 →
      common_prefix_length w' φ = q := by
    intro w w' hm_w h_w_long h_adj h_w'_len
    obtain ⟨ℓ, hw'_eq⟩ := BusemannLocal.exists_letter_of_adj h_adj
    -- Non-cancel: length of w * mk [ℓ] would be |w| - 1 if cancel, |w| + 1 if no cancel.
    have h_noCancel : BusemannLocal.NoLastCancel w ℓ := by
      by_contra h_cancel
      have h_cancel_W : BusemannLocal.LastCancels w ℓ := by
        unfold BusemannLocal.NoLastCancel at h_cancel
        push_neg at h_cancel
        obtain ⟨ℓ', h_mem, hc⟩ := h_cancel
        exact ⟨ℓ', h_mem, hc⟩
      have h_len_cancel : w'.toWord.length = w.toWord.length - 1 := by
        rw [hw'_eq]
        exact BusemannLocal.length_toWord_mul_mk_letter_cancel w ℓ h_cancel_W
      omega
    -- Off-ray: m(w, φ) = q < q + 1 ≤ |w|.
    have h_off_ray : common_prefix_length w φ < w.toWord.length := by
      rw [hm_w]; omega
    rw [hw'_eq]
    rw [BusemannLocal.common_prefix_length_noCancel_off_ray w ℓ φ h_noCancel h_off_ray, hm_w]
  -- Wait: our NoLastCancel definition requires careful handling. Let me retry.
  -- We need to convert ¬ LastCancels w ℓ into NoLastCancel w ℓ.
  -- NoLastCancel := ∀ ℓ' ∈ w.toWord.getLast?, ¬ (ℓ'.1 = ℓ.1 ∧ ℓ'.2 = !ℓ.2).
  -- LastCancels := ∃ ℓ' ∈ w.toWord.getLast?, ℓ'.1 = ℓ.1 ∧ ℓ'.2 = !ℓ.2.
  -- These are de-Morgan dual. Already handled above.
  -- Step 5: invariant I k.
  -- I k := Adj (next^[k] v) (next^[k+1] v) ∧
  --         (next^[k+1] v).toWord.length = (next^[k] v).toWord.length + 1 ∧
  --         g (next^[k+1] v) > g (next^[k] v) ∧
  --         common_prefix_length (next^[k] v) φ = q ∧
  --         (next^[k] v).toWord.length = v.toWord.length + k
  let I : ℕ → Prop := fun k =>
    (cayley_graph F2_generating_set).Adj (next^[k] v) (next^[k+1] v) ∧
    (next^[k+1] v).toWord.length = (next^[k] v).toWord.length + 1 ∧
    g (next^[k+1] v) > g (next^[k] v) ∧
    common_prefix_length (next^[k] v) φ = q ∧
    (next^[k] v).toWord.length = v.toWord.length + k
  have h_I : ∀ k : ℕ, I k := by
    intro k
    induction k with
    | zero =>
        -- next^[0] v = v, next^[1] v = next v.
        have h_iter0 : next^[0] v = v := Function.iterate_zero_apply next v
        have h_iter1 : next^[1] v = next v := by
          rw [Function.iterate_one]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [h_iter0, h_iter1]
          exact (h_next_step v h_base_ex).1
        · rw [h_iter0, h_iter1]
          exact (h_next_step v h_base_ex).2.1
        · rw [h_iter0, h_iter1]
          exact (h_next_step v h_base_ex).2.2
        · rw [h_iter0]; exact h_v_T
        · rw [h_iter0]; simp
    | succ k ih =>
        obtain ⟨ih_adj, ih_len, ih_g, ih_m, ih_wlen⟩ := ih
        -- v_k, v_{k+1}, v_{k+2} are next^[k] v, next^[k+1] v, next^[k+2] v.
        -- Rewrite next^[k+1+1] as next (next^[k+1] v).
        have h_iter_succ : next^[(k+1)+1] v = next (next^[k+1] v) := by
          rw [Function.iterate_succ_apply']
        -- To apply greedy_outward_step at v_{k+1} with parent v_k:
        -- Adj v_{k+1} v_k (symmetric), |v_k| + 1 = |v_{k+1}|, g v_k < g v_{k+1}.
        have h_adj_sym : (cayley_graph F2_generating_set).Adj (next^[k+1] v) (next^[k] v) :=
          ih_adj.symm
        have h_parent_len_step : (next^[k] v).toWord.length + 1 = (next^[k+1] v).toWord.length :=
          ih_len.symm
        have h_parent_lt_step : g (next^[k] v) < g (next^[k+1] v) := ih_g
        obtain ⟨c, hc_adj, hc_len, hc_gt⟩ := greedy_outward_step φ g h_harm
            (next^[k+1] v) (next^[k] v) h_adj_sym h_parent_len_step h_parent_lt_step
        have h_ex : ∃ c' : F2, (cayley_graph F2_generating_set).Adj (next^[k+1] v) c' ∧
            c'.toWord.length = (next^[k+1] v).toWord.length + 1 ∧ g c' > g (next^[k+1] v) :=
          ⟨c, hc_adj, hc_len, hc_gt⟩
        obtain ⟨h_next_adj, h_next_len, h_next_g⟩ := h_next_step (next^[k+1] v) h_ex
        -- Derive m(v_{k+1}, φ) = q.
        have ih_wlen_succ : (next^[k+1] v).toWord.length = v.toWord.length + k + 1 := by
          rw [ih_len, ih_wlen]
        have h_m_kp1 : common_prefix_length (next^[k+1] v) φ = q :=
          h_m_preserved (next^[k] v) (next^[k+1] v) ih_m
            (by rw [ih_wlen]; omega) ih_adj ih_len
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [h_iter_succ]; exact h_next_adj
        · rw [h_iter_succ]; exact h_next_len
        · rw [h_iter_succ]; exact h_next_g
        · exact h_m_kp1
        · rw [ih_wlen_succ]; ring
  -- Step 6: apply F2_boundary_of_outward_ray.
  have h_orbit : ∀ k : ℕ,
      (cayley_graph F2_generating_set).Adj (next^[k] v) (next (next^[k] v)) ∧
      (next (next^[k] v)).toWord.length = (next^[k] v).toWord.length + 1 := by
    intro k
    obtain ⟨h_adj_k, h_len_k, _, _, _⟩ := h_I k
    have h_eq : next^[k+1] v = next (next^[k] v) := Function.iterate_succ_apply' _ _ _
    rw [h_eq] at h_adj_k h_len_k
    exact ⟨h_adj_k, h_len_k⟩
  obtain ⟨ψ, hψ_orbit⟩ := F2_boundary_of_outward_ray v next h_orbit
  -- Step 7: show m(ψ.valPrefix (q+1), φ) ≤ q.
  -- Use: next^[0] v = v = ψ.valPrefix (|v| + 0) = ψ.valPrefix |v|.
  have hψ_v : v = ψ.valPrefix v.toWord.length := by
    have := hψ_orbit 0
    simpa [Function.iterate_zero_apply] using this
  -- ψ.valPrefix |v| = v means (ψ.valPrefix |v|).toWord = v.toWord.
  have hψ_v_tw : (ψ.valPrefix v.toWord.length).toWord = v.toWord := by
    rw [← hψ_v]
  -- For any i < |v|, ψ.val i = v.toWord[i].
  have hψ_val_at : ∀ i : ℕ, i < v.toWord.length →
      v.toWord[i]? = some (ψ.val i) := by
    intro i hi
    have := F2_boundary.toWord_valPrefix_getElem? ψ v.toWord.length i hi
    rw [hψ_v_tw] at this
    exact this
  -- v.toWord[q]? ≠ some (φ.val q), since m(v, φ) = q < |v|.
  have h_v_off_q : v.toWord[q]? ≠ some (φ.val q) := by
    have := BusemannLocal.toWord_at_m_ne_phi_of_lt v φ (by rw [h_v_T]; omega)
    rw [h_v_T] at this
    exact this
  -- Hence ψ.val q ≠ φ.val q (as elements of Fin 2 × Bool).
  have h_ψ_val_q : v.toWord[q]? = some (ψ.val q) :=
    hψ_val_at q (by omega)
  have h_ψ_val_q_ne : (some (ψ.val q) : Option (Fin 2 × Bool)) ≠ some (φ.val q) := by
    rw [← h_ψ_val_q]; exact h_v_off_q
  -- common_prefix_length (ψ.valPrefix (q+1)) φ ≤ q.
  have h_m_bound : common_prefix_length (ψ.valPrefix (q+1)) φ ≤ q := by
    -- Suppose m ≥ q + 1. Then PrefixMatches (ψ.valPrefix (q+1)) φ (q+1), which
    -- forces (ψ.valPrefix (q+1)).toWord[q]? = some (φ.val q).
    -- But (ψ.valPrefix (q+1)).toWord[q]? = some (ψ.val q). Contradiction.
    by_contra h_gt
    push_neg at h_gt
    have h_pm : PrefixMatches (ψ.valPrefix (q+1)) φ (q+1) := by
      -- Actually we need PrefixMatches at common_prefix_length.
      have h_cpl := BusemannLocal.prefixMatches_common_prefix_length (ψ.valPrefix (q+1)) φ
      -- PrefixMatches is monotone decreasing in p: if PrefixMatches at m, then at k ≤ m.
      refine ⟨?_, ?_⟩
      · rw [F2_boundary.length_toWord_valPrefix]
      · intro i hi
        have hi' : i < common_prefix_length (ψ.valPrefix (q+1)) φ := by omega
        exact h_cpl.2 i hi'
    have h_at_q : (ψ.valPrefix (q+1)).toWord[q]? = some (φ.val q) :=
      h_pm.2 q (Nat.lt_succ_self _)
    have h_at_q_ψ : (ψ.valPrefix (q+1)).toWord[q]? = some (ψ.val q) :=
      F2_boundary.toWord_valPrefix_getElem? ψ (q+1) q (Nat.lt_succ_self _)
    exact h_ψ_val_q_ne (h_at_q_ψ.symm.trans h_at_q)
  -- Step 8: apply h_limit_other.
  have h_lim := h_limit_other ψ h_m_bound
  -- Step 9: orbit identity g(next^[k] v) = g (ψ.valPrefix (|v| + k)).
  have h_g_eq_along : ∀ k : ℕ, g (next^[k] v) = g (ψ.valPrefix (v.toWord.length + k)) := by
    intro k
    rw [hψ_orbit k]
  -- Step 10: g (next^[k] v) ≥ g v for all k ≥ 0. Actually > 0, but we just need a positive lower bound.
  have h_g_lower : ∀ k : ℕ, g v ≤ g (next^[k] v) := by
    intro k
    induction k with
    | zero => simp [Function.iterate_zero_apply]
    | succ k' ih =>
        have hI := h_I k'
        have h_step : g (next^[k'] v) < g (next^[k'+1] v) := hI.2.2.1
        linarith
  -- Step 11: from Tendsto, derive eventual upper bound and contradict.
  -- Let ε := g v / 2 > 0. Eventually g (ψ.valPrefix p) < ε < g v.
  have h_gv_pos : 0 < g v := h_v_pos
  have h_ε_pos : 0 < g v / 2 := by linarith
  -- Eventually |g (ψ.valPrefix p)| < g v / 2.
  have h_lim_ε := h_lim.eventually (eventually_abs_sub_lt (0 : ℝ) h_ε_pos)
  rw [Filter.eventually_atTop] at h_lim_ε
  obtain ⟨N, hN⟩ := h_lim_ε
  -- Pick k := N (so |v| + k ≥ N ≥ N).
  set k := N with hk_def
  have hN_val : N ≤ v.toWord.length + k := by rw [hk_def]; omega
  have := hN (v.toWord.length + k) hN_val
  -- this : |g (ψ.valPrefix (|v| + k)) - 0| < g v / 2.
  simp at this
  -- So g (ψ.valPrefix (|v| + k)) ∈ (- g v / 2, g v / 2).
  -- But g (next^[k] v) = g (ψ.valPrefix (|v| + k)) ≥ g v > g v / 2, contradiction.
  have h_orbit_val : g (next^[k] v) = g (ψ.valPrefix (v.toWord.length + k)) :=
    h_g_eq_along k
  have h_orbit_lb : g v ≤ g (next^[k] v) := h_g_lower k
  rw [h_orbit_val] at h_orbit_lb
  -- Combine: |x| < g v / 2 and x ≥ g v > 0 ⇒ contradiction via x ≥ g v > g v / 2 ≥ x.
  have h_abs : |g (ψ.valPrefix (v.toWord.length + k))| < g v / 2 := this
  have h_lt : g (ψ.valPrefix (v.toWord.length + k)) < g v / 2 :=
    (abs_lt.mp h_abs).2
  linarith

/-- **Q40a — Inductive form (Wave 22F.5).**  Pointwise harmonic `g` with
`g(φ.valPrefix q) = 0`, with `g ≡ 0` already on `T_{q-1}`, and with
literal-exam pointwise ray decay along non-`φ` rays, vanishes on `T_q`.

For `q = 0` the inductive `h_below` hypothesis is vacuous and this is
the literal Q40a base case. -/
theorem harmonic_vanish_on_Tq_inductive
    (φ : ∂F2) (q : ℕ) (g : F2 → ℝ)
    (h_harm : PointwiseHarmonic φ g)
    (h_zero_at_phi_q : g (φ.valPrefix q) = 0)
    (h_below : ∀ x : F2, common_prefix_length x φ < q → g x = 0)
    (h_limit_other : ∀ ψ : ∂F2, common_prefix_length (ψ.valPrefix (q+1)) φ ≤ q →
      Filter.Tendsto (fun p : ℕ => g (ψ.valPrefix p))
        Filter.atTop (nhds (0 : ℝ))) :
    ∀ x : F2, common_prefix_length x φ ≤ q → g x = 0 := by
  -- Strategy: by contradiction; use the bootstrap to produce (v, parent),
  -- then `outward_chain_contradicts_decay` closes the contradiction.
  -- The g(x) > 0 case and g(x) < 0 case are handled symmetrically.
  intro x hx_T
  by_contra h_ne
  rcases lt_or_gt_of_ne h_ne with h_neg | h_pos
  · -- Case g x < 0: apply the bootstrap to -g.
    set g' : F2 → ℝ := fun y => -g y with g'_def
    have h_harm' : PointwiseHarmonic φ g' := by
      intro y
      obtain ⟨yφ, T, h_adj, h_bus, h_card, h_T_mem, h_yφ_notmem, h_sum⟩ := h_harm y
      refine ⟨yφ, T, h_adj, h_bus, h_card, h_T_mem, h_yφ_notmem, ?_⟩
      show -g yφ + (∑ z ∈ T, -g z) = 4 * -g y
      rw [Finset.sum_neg_distrib]
      linarith
    have h_zero' : g' (φ.valPrefix q) = 0 := by simp [g'_def, h_zero_at_phi_q]
    have h_below' : ∀ y : F2, common_prefix_length y φ < q → g' y = 0 := by
      intro y hy; simp [g'_def, h_below y hy]
    have h_limit' : ∀ ψ : ∂F2,
        common_prefix_length (ψ.valPrefix (q+1)) φ ≤ q →
        Filter.Tendsto (fun p : ℕ => g' (ψ.valPrefix p))
          Filter.atTop (nhds (0 : ℝ)) := by
      intro ψ hψ
      have h := h_limit_other ψ hψ
      simpa [g'_def] using h.neg
    have hx_pos' : 0 < g' x := by simp [g'_def]; linarith
    obtain ⟨v, parent, h_v_T, h_v_long, h_p_adj, h_p_short, h_p_lt, h_v_pos⟩ :=
      bootstrap_witness φ q g' h_zero' h_below' x hx_T hx_pos'
    exact outward_chain_contradicts_decay φ q g' h_harm' v parent
      h_v_T h_v_long h_p_adj h_p_short h_p_lt h_v_pos h_limit'
  · -- Case g x > 0: direct application of the bootstrap.
    obtain ⟨v, parent, h_v_T, h_v_long, h_p_adj, h_p_short, h_p_lt, h_v_pos⟩ :=
      bootstrap_witness φ q g h_zero_at_phi_q h_below x hx_T h_pos
    exact outward_chain_contradicts_decay φ q g h_harm v parent
      h_v_T h_v_long h_p_adj h_p_short h_p_lt h_v_pos h_limit_other

/-! ### Step 6 — Q40b (literal exam hypothesis)

The exam-literal uniqueness of `p_φ`: any harmonic `f` with `f(1) = 1`
and pointwise ray decay along non-`φ` rays equals `p_φ`.  Proved by
inductive descent over `T_k` using `harmonic_vanish_on_Tq_inductive`. -/

/-- **Q40b — Literal exam hypothesis form (Wave 22F.5).**  Any pointwise
harmonic `f : F_2 → ℝ` with `f(1) = 1` and pointwise ray decay
`lim_p f(ψ_→p) = 0` for every `ψ ≠ φ` equals the Poisson kernel `p_φ`. -/
theorem poisson_kernel_unique_literal (φ : ∂F2) (f : F2 → ℝ)
    (h_harm : PointwiseHarmonic φ f)
    (h_one : f (1 : F2) = 1)
    (h_limit_other : ∀ ψ : ∂F2, ψ ≠ φ →
      Filter.Tendsto (fun p : ℕ => f (ψ.valPrefix p))
        Filter.atTop (nhds (0 : ℝ))) :
    f = poisson_kernel φ := by
  -- Set g := f - p_φ. Then g harmonic, g(1) = 0, lim g(ψ_→p) = 0 for ψ ≠ φ.
  set g : F2 → ℝ := fun x => f x - poisson_kernel φ x with hg_def
  have h_g_harm : PointwiseHarmonic φ g := by
    intro x
    obtain ⟨yφ, T, h_adj, h_bus, h_card, h_T_mem, h_yφ_notmem, h_sum_f⟩ :=
      h_harm x
    have h_sum_p : poisson_kernel φ yφ + (∑ y ∈ T, poisson_kernel φ y)
        = 4 * poisson_kernel φ x :=
      poisson_kernel_neighbour_sum φ x yφ T h_bus
        (fun y hy => (h_T_mem y hy).2) h_card h_yφ_notmem
    refine ⟨yφ, T, h_adj, h_bus, h_card, h_T_mem, h_yφ_notmem, ?_⟩
    show (f yφ - poisson_kernel φ yφ) + (∑ y ∈ T, (f y - poisson_kernel φ y))
         = 4 * (f x - poisson_kernel φ x)
    rw [Finset.sum_sub_distrib]
    linarith
  have h_g_one : g (1 : F2) = 0 := by
    simp [hg_def, poisson_kernel_at_one, h_one]
  -- Inductive claim: g ≡ 0 on T_k for every k.  We prove it by strong
  -- induction on k via `Nat.strong_induction_on`.
  have h_g_zero_on_Tk : ∀ k : ℕ, ∀ x : F2,
      common_prefix_length x φ ≤ k → g x = 0 := by
    intro k
    induction k with
    | zero =>
        -- Base: g(φ.valPrefix 0) = g(1) = 0; literal-exam hypothesis applies
        -- with q = 0 (h_below vacuous, since common_prefix_length is a Nat).
        intro x hx_T
        have h_zero_phi_0 : g (φ.valPrefix 0) = 0 := by
          have h_eq : φ.valPrefix 0 = (1 : F2) := by
            unfold F2_boundary.valPrefix F2_boundary.prefixList
            rfl
          rw [h_eq, h_g_one]
        have h_below_0 : ∀ y : F2, common_prefix_length y φ < 0 → g y = 0 := by
          intro y hy; exact absurd hy (Nat.not_lt_zero _)
        have h_limit_g_0 : ∀ ψ : ∂F2,
            common_prefix_length (ψ.valPrefix (0+1)) φ ≤ 0 →
            Filter.Tendsto (fun p : ℕ => g (ψ.valPrefix p))
              Filter.atTop (nhds (0 : ℝ)) := by
          intro ψ hψ
          -- common_prefix_length(ψ.valPrefix 1, φ) ≤ 0 forces ψ ≠ φ.
          have hne : ψ ≠ φ := by
            intro h_eq
            -- if ψ = φ, then ψ.valPrefix 1 = φ.valPrefix 1, so
            -- common_prefix_length (ψ.valPrefix 1) φ = 1, contradicting hψ.
            rw [h_eq] at hψ
            rw [common_prefix_length_valPrefix_self φ 1] at hψ
            omega
          have h_f := h_limit_other ψ hne
          have h_p := poisson_kernel_along_other_vanish φ ψ hne
          have h_sub : Filter.Tendsto
              (fun p : ℕ => f (ψ.valPrefix p) - poisson_kernel φ (ψ.valPrefix p))
              Filter.atTop (nhds (0 - 0 : ℝ)) := h_f.sub h_p
          simpa [hg_def] using h_sub
        exact harmonic_vanish_on_Tq_inductive φ 0 g h_g_harm
          h_zero_phi_0 h_below_0 h_limit_g_0 x hx_T
    | succ k ih =>
        -- Step: assume g ≡ 0 on T_k; show g ≡ 0 on T_{k+1}.
        -- 1. From harmonicity at φ.valPrefix k, deduce g(φ.valPrefix (k+1)) = 0.
        have h_zero_phi_k : g (φ.valPrefix k) = 0 := by
          apply ih
          rw [common_prefix_length_valPrefix_self φ k]
        have h_zero_phi_k_succ : g (φ.valPrefix (k+1)) = 0 := by
          obtain ⟨yφ, T, h_adj, h_bus, h_card, h_T_mem, h_yφ_notmem, h_sum⟩ :=
            h_g_harm (φ.valPrefix k)
          -- The "toward-φ" neighbour `yφ` is φ.valPrefix (k+1).
          -- The 3 "away-from-φ" neighbours have m ≤ k (lateral or the
          -- backward-cancellation), all in T_k; ih gives g = 0 on them.
          -- Combined with g(φ.valPrefix k) = 0, harmonicity gives
          -- g(φ.valPrefix (k+1)) = 0 *if* yφ = φ.valPrefix (k+1), which we
          -- know by uniqueness of the toward-φ neighbour.
          obtain ⟨yφ_phi, ⟨h_yφ_phi_adj, h_yφ_phi_bus⟩, h_yφ_phi_uniq⟩ :=
            busemann_neighbour_structure φ (φ.valPrefix k)
          have h_yφ_eq_phi : yφ = φ.valPrefix (k+1) := by
            -- φ.valPrefix (k+1) is also a "toward-φ" neighbour of φ.valPrefix k.
            have h_step_adj :
                (cayley_graph F2_generating_set).Adj
                  (φ.valPrefix k) (φ.valPrefix (k+1)) := by
              -- φ.valPrefix (k+1) = φ.valPrefix k * mk[φ.val k]
              -- (no cancellation since φ is reduced).
              have hmk :
                  φ.valPrefix (k+1)
                    = φ.valPrefix k * _root_.FreeGroup.mk [φ.val k] := by
                unfold F2_boundary.valPrefix F2_boundary.prefixList
                rw [show List.range (k+1) = List.range k ++ [k] from by
                      rw [List.range_succ]]
                rw [List.map_append, List.map_singleton]
                rw [← _root_.FreeGroup.mul_mk]
              rw [hmk]
              apply BusemannLocal.adj_mul_mk_letter
            have h_step_bus :
                busemann φ (φ.valPrefix (k+1))
                  = busemann φ (φ.valPrefix k) - 1 := by
              rw [busemann_valPrefix_self φ (k+1), busemann_valPrefix_self φ k]
              push_cast; ring
            have h_yφ_uniq_phi := h_yφ_phi_uniq (φ.valPrefix (k+1))
              ⟨h_step_adj, h_step_bus⟩
            have h_yφ_uniq_yφ := h_yφ_phi_uniq yφ ⟨h_adj, h_bus⟩
            exact h_yφ_uniq_yφ.trans h_yφ_uniq_phi.symm
          -- Each y ∈ T has `m(y, φ) ≤ k` (lateral or cancellation), hence g y = 0.
          have h_T_in_Tk : ∀ y ∈ T, common_prefix_length y φ ≤ k := by
            intro y hy
            -- y is adjacent to φ.valPrefix k with b_φ y = b_φ(φ.valPrefix k) + 1.
            -- The lateral & cancellation neighbours all satisfy m(y,φ) ≤ k.
            have hy_adj := (h_T_mem y hy).1
            have hy_bus := (h_T_mem y hy).2
            -- m(y, φ) ≤ k follows from: |y| - 2 m(y,φ) = b_φ(φ.valPrefix k) + 1
            --                                       = -k + 1 = 1 - k.
            -- Combined with |y| ≥ |m(y,φ)| somehow... let me approach differently:
            -- Since y is a neighbour of φ.valPrefix k and y ≠ yφ = φ.valPrefix (k+1),
            -- y's word does NOT extend along φ at position k+1; hence m(y, φ) ≤ k.
            have hy_ne_yφ : y ≠ yφ := fun heq => h_yφ_notmem (heq ▸ hy)
            -- Use common_prefix_length_le and the relation b_φ y = ... to bound.
            -- A cleaner route: m(y, φ) ≤ |y|, and since y has b_φ = -k + 1,
            -- |y| = b_φ y + 2 m(y, φ) = (1-k) + 2 m(y,φ).
            -- But |y| is a non-negative integer, and m(y, φ) ≤ |y|, so
            -- 2 m(y, φ) ≤ b_φ y + 2 m(y,φ) means b_φ y ≥ 0, i.e., 1-k ≥ 0,
            -- i.e., k ≤ 1. That's not tight enough.
            -- Direct argument: y ≠ yφ AND y is a neighbour of φ.valPrefix k.
            -- The 3 non-yφ neighbours of φ.valPrefix k each have m ≤ k:
            -- - The cancellation neighbour `φ.valPrefix (k-1)` has m = k-1.
            -- - The 2 lateral extensions `φ.valPrefix k * t` (t ≠ φ.val k, t ≠ inv)
            --   have first k letters = φ_→k, then t ≠ φ_{k+1}, so m = k.
            -- Either way m(y, φ) ≤ k. Formalising via `common_prefix_length_le`
            -- combined with the Busemann equation.
            -- Use the Busemann equation: |y| = b_φ y + 2 m(y, φ), so
            --   m(y, φ) = (|y| - b_φ y) / 2 = (|y| - (-k + 1)) / 2 = (|y| + k - 1) / 2.
            -- Combined with |y| ∈ {k-1, k+1} (1 step from |·| = k, must change by ±1):
            --   |y| = k - 1: m(y, φ) = (k-1+k-1)/2 = k - 1 ≤ k.
            --   |y| = k + 1: m(y, φ) = (k+1+k-1)/2 = k.
            -- Either way m ≤ k.
            have h_y_len : y.toWord.length = k - 1 ∨ y.toWord.length = k + 1 := by
              -- Two neighbours of φ.valPrefix k differ in word length by ±1.
              obtain ⟨ℓ, hℓ_eq⟩ := BusemannLocal.exists_letter_of_adj hy_adj
              by_cases hcc : BusemannLocal.LastCancels (φ.valPrefix k) ℓ
              · left
                have h_phi_k_len : (φ.valPrefix k).toWord.length = k :=
                  F2_boundary.length_toWord_valPrefix φ k
                rw [hℓ_eq, BusemannLocal.length_toWord_mul_mk_letter_cancel _ _ hcc,
                    h_phi_k_len]
              · right
                have h_phi_k_len : (φ.valPrefix k).toWord.length = k :=
                  F2_boundary.length_toWord_valPrefix φ k
                have hnc : BusemannLocal.NoLastCancel (φ.valPrefix k) ℓ := by
                  intro ℓ' hℓ'_mem ⟨h1, h2⟩
                  exact hcc ⟨ℓ', hℓ'_mem, h1, h2⟩
                rw [hℓ_eq, BusemannLocal.length_toWord_mul_mk_letter_noCancel _ _ hnc,
                    h_phi_k_len]
            -- The Busemann equation: |y| = b_φ y + 2 m(y, φ).
            have h_bus_eq : (y.toWord.length : ℤ)
                = busemann φ y + 2 * (common_prefix_length y φ : ℤ) := by
              unfold busemann; ring
            have h_bus_y : busemann φ y = busemann φ (φ.valPrefix k) + 1 := hy_bus
            have h_bus_phi_k : busemann φ (φ.valPrefix k) = -(k : ℤ) :=
              busemann_valPrefix_self φ k
            rcases h_y_len with hlen | hlen
            · -- |y| = k - 1: m = k - 1 ≤ k (provided k ≥ 1).
              have hk_pos : k ≥ 1 := by
                rcases Nat.eq_zero_or_pos k with hk0 | hk
                · exfalso; rw [hk0] at hlen; omega
                · exact hk
              have h_m : (common_prefix_length y φ : ℤ) = (k : ℤ) - 1 := by
                have hh := h_bus_eq
                rw [hlen, h_bus_y, h_bus_phi_k] at hh
                push_cast [Nat.cast_sub hk_pos] at hh
                linarith
              have : (common_prefix_length y φ : ℤ) ≤ (k : ℤ) := by linarith
              exact_mod_cast this
            · -- |y| = k + 1: m = k.
              have h_m : (common_prefix_length y φ : ℤ) = (k : ℤ) := by
                have hh := h_bus_eq
                rw [hlen, h_bus_y, h_bus_phi_k] at hh
                push_cast at hh
                linarith
              have : (common_prefix_length y φ : ℤ) ≤ (k : ℤ) := by linarith
              exact_mod_cast this
          have h_T_zero : ∀ y ∈ T, g y = 0 := fun y hy => ih y (h_T_in_Tk y hy)
          have h_sum_T_zero : (∑ y ∈ T, g y) = 0 := by
            calc (∑ y ∈ T, g y) = (∑ _ ∈ T, (0 : ℝ)) :=
                  Finset.sum_congr rfl (fun y hy => h_T_zero y hy)
              _ = 0 := Finset.sum_const_zero
          have h_4g_phi_k : 4 * g (φ.valPrefix k) = 0 := by rw [h_zero_phi_k]; ring
          rw [← h_yφ_eq_phi]
          linarith
        -- 2. Apply the inductive Q40a at q = k+1.
        intro x hx_T
        apply harmonic_vanish_on_Tq_inductive φ (k+1) g h_g_harm
          h_zero_phi_k_succ
          (fun y hy => ih y (Nat.lt_succ_iff.mp hy))
          ?_
          x hx_T
        intro ψ hψ
        -- common_prefix_length (ψ.valPrefix (k+2)) φ ≤ k+1 forces ψ ≠ φ.
        have hne : ψ ≠ φ := by
          intro h_eq
          rw [h_eq] at hψ
          rw [common_prefix_length_valPrefix_self φ (k+2)] at hψ
          omega
        have h_f := h_limit_other ψ hne
        have h_p := poisson_kernel_along_other_vanish φ ψ hne
        have h_sub : Filter.Tendsto
            (fun p : ℕ => f (ψ.valPrefix p) - poisson_kernel φ (ψ.valPrefix p))
            Filter.atTop (nhds (0 - 0 : ℝ)) := h_f.sub h_p
        simpa [hg_def] using h_sub
  -- Conclude: every x has m(x,φ) ≤ |x|, so g x = 0.
  funext x
  have hx_T : common_prefix_length x φ ≤ x.toWord.length := by
    unfold common_prefix_length
    exact Nat.findGreatest_le _
  have h_g_zero : g x = 0 :=
    h_g_zero_on_Tk x.toWord.length x hx_T
  show f x = poisson_kernel φ x
  have : f x - poisson_kernel φ x = 0 := h_g_zero
  linarith

end EnsX2026.FreeGroup
