import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.StrongLaw
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.SetTheory.Cardinal.Free
import EnsX2026.Cayley.Growth
import EnsX2026.FreeGroup.Busemann

/-!
# ENS/Polytechnique 2026 Math A — Random walk on `F_2` (Q42, Q43, Q44)

We formalise the final probabilistic block of the exam: the simple random walk
on the free group `F_2` of rank two, with steps drawn i.i.d. uniformly from
the symmetric generating set `Z = {a, b, a⁻¹, b⁻¹}`. The three questions are:

* **Q42** — for a fixed boundary point `φ ∈ ∂F_2`, the Busemann function
  `b_φ(X_n)` satisfies `(b_φ(X_n) + n)/2 ~ Binomial(n, 3/4)`. As a
  consequence of Hoeffding's inequality,
  `P(|b_φ(X_n)/n − 1/2| ≥ ε) ≤ 2 · exp(−n ε² / 2)`.
* **Q43** — almost-sure rate of escape: `d(1, X_n) / n → 1/2`.
* **Q44** — transience: for any finite set `E ⊂ F_2`, the walk eventually
  leaves `E` almost surely.

## Prerequisite files

* `EnsX2026.FreeGroup.Busemann` provides `F2`, `∂F2`, `busemann`, the
  generating set `F2_generating_set`, and the two exam axioms
  `busemann_neighbour_structure` (uniqueness of the "toward-φ" neighbour)
  and `busemann_other_neighbours` (all neighbours are at Busemann distance
  `±1`).
* `EnsX2026.Cayley.Growth` provides the generic `cayley_graph`
  construction for a generating set.

## Mathlib gaps worked around

* **No `RandomWalk` API** — we build the walk `X_walk n Y = Y_0 · Y_1 · ⋯ · Y_{n−1}`
  by recursion on the sample path `Y : ℕ → F_2`.
* **Binomial mean `𝔼[Bin(n, p)] = np` is a `proof_wanted` stub** in
  `Mathlib/Probability/Distributions/Binomial.lean` (line 70). We therefore
  do not use the pre-packaged binomial measure in the Hoeffding step; we
  instead apply `HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun` directly to the
  i.i.d. Bernoulli increments `ξ_i = (b_φ(X_{i+1}) − b_φ(X_i) + 1)/2`, which
  are bounded in `{0, 1}` and hence sub-Gaussian with parameter `1/4`.
* **Measurability on `F_2`** — `F_2` is countable (discrete), so we endow it
  with the top σ-algebra, making every function measurable.

Proof obligations that would require substantial probabilistic plumbing
(independence of the increments under the infinite product measure,
identification with a `Binomial(n, 3/4)` law, application of Borel–Cantelli
to transfer an a.s. limit from each fixed `φ` to the supremum over `φ`) are
left as explicit `sorry` with TODO comments. The pragmatic scope of
Q42–Q44 is to state the three theorems correctly against Mathlib's
measure-theoretic infrastructure, and to close the easy reductions (here,
Q44 is fully proved from `walk_dist_tendsto_atTop`).

## Wave 16 — Azuma architecture (errata note E3)

An earlier draft of this file attempted to use Hoeffding's inequality for
**i.i.d.** centred indicators, via
`HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun` applied to the
variables `ξ_i - 3/4`. This is **mathematically incorrect**: the centred
indicators are *not* i.i.d. — they depend on the entire walk history
`Y_0, …, Y_{i-1}` (through the current walk position). They ARE a bounded
martingale-difference sequence with respect to the natural filtration
`F_n := σ(Y_0, …, Y_{n-1})`:

* each `ξ_i := away_indicator φ i Y - 3/4` is `F_{i+1}`-measurable;
* conditionally on `F_i` (i.e., given the walk so far), the next step `Y_i`
  is uniform over the 4 generators, and exactly 3 of 4 choices give
  `ξ_i + 3/4 = 1` ("away"), 1 gives `ξ_i + 3/4 = 0` ("toward"). Hence
  `E[ξ_i | F_i] = 0` and `ξ_i | F_i` has range `[-3/4, 1/4]`, i.e. is
  conditionally sub-Gaussian with parameter `1/4` (the range-half-width
  squared).

The Hoeffding bound then follows from **Azuma's inequality** for
sub-Gaussian martingale differences (Williams, *Probability with
Martingales*, §14.6; Mathlib's
`ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF`).

Rather than construct the full natural-filtration plumbing (filtration,
strong adaptation, conditional MGF computations) inline — which would
require ~200 lines of measure-theoretic bookkeeping to verify the clean
bound that a calculus text takes as "obvious" — we follow the established
**companion-axiom pattern** used for the Busemann lemmas
(`busemann_neighbour_structure`, `busemann_other_neighbours`,
`busemann_three_plus_neighbours` in `EnsX2026.FreeGroup.Busemann`). We
admit the Azuma tail bound directly as
`centred_away_azuma_tail`, cited in the paper to Williams' martingale
Hoeffding. This replaces the pair of now-removed lemmas
`iIndepFun_centred_away` (literally false) and
`centred_away_subgaussian` (structurally incomplete — required a
conditional, not unconditional, sub-Gaussian fact).

Institut Fourier, Grenoble — Kieran McShane
-/

noncomputable section

namespace EnsX2026.FreeGroup

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Function
open EnsX2026.Cayley

/-! ### Measurable-space structure on `F_2` -/

/-- `F_2 = FreeGroup (Fin 2)` is countable, so we take the top σ-algebra.
With this measurable structure every function out of `F_2` is measurable. -/
instance : MeasurableSpace F2 := ⊤

instance : DiscreteMeasurableSpace F2 := ⟨fun _ => trivial⟩

/-! ### The uniform step distribution on `Z = {a, b, a⁻¹, b⁻¹}` -/

/-- The uniform probability measure on the symmetric generating set
`F2_generating_set = {a, b, a⁻¹, b⁻¹}`: each of the four generators has
mass `1/4`. -/
noncomputable def Z_uniform : Measure F2 :=
  (1/4 : ℝ≥0∞) •
    (Measure.dirac genA + Measure.dirac genB +
      Measure.dirac genA⁻¹ + Measure.dirac genB⁻¹)

/-- `Z_uniform` has total mass `1` (proof obligation for
`IsProbabilityMeasure`). The proof is a direct `1/4 + 1/4 + 1/4 + 1/4 = 1`
computation. We omit the structural instance and provide `Z_uniform` a
bundled `IsProbabilityMeasure` fact via a dedicated lemma used downstream. -/
lemma Z_uniform_univ : Z_uniform Set.univ = 1 := by
  simp [Z_uniform, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply, Set.mem_univ]
  -- Goal: `4⁻¹ + 4⁻¹ + 4⁻¹ + 4⁻¹ = 1` in `ℝ≥0∞`.
  -- Rewrite `4⁻¹ + 4⁻¹ + 4⁻¹ + 4⁻¹ = 4 * 4⁻¹ = 1`.
  have h4 : (4 : ℝ≥0∞) ≠ 0 := by norm_num
  have h4' : (4 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have step : (4 : ℝ≥0∞)⁻¹ + (4 : ℝ≥0∞)⁻¹ + (4 : ℝ≥0∞)⁻¹ + (4 : ℝ≥0∞)⁻¹
                = (4 : ℝ≥0∞) * (4 : ℝ≥0∞)⁻¹ := by
    rw [show (4 : ℝ≥0∞) = 1 + 1 + 1 + 1 from by norm_num]
    ring
  rw [step, ENNReal.mul_inv_cancel h4 h4']

instance : IsProbabilityMeasure Z_uniform := ⟨Z_uniform_univ⟩

/-! ### The i.i.d. sequence `(Y_n)` and the random walk `(X_n)` -/

/-- The product probability measure on `ℕ → F_2` representing the i.i.d.
sequence `(Y_n)` of steps, each distributed as `Z_uniform`. -/
noncomputable def step_measure : Measure (ℕ → F2) :=
  Measure.infinitePi (fun _ : ℕ => Z_uniform)

instance : IsProbabilityMeasure step_measure := by
  unfold step_measure; infer_instance

/-! ### Wave 35.2a — i.i.d. shift invariance and first-`n` factorisation

Two structural facts about `step_measure` that are otherwise absent from
Mathlib's `infinitePi` API:

* `step_measure_shift_invariant`: the pushforward of `step_measure` under
  the left-shift `Y ↦ Y ∘ Nat.succ` equals `step_measure` itself.
* `step_measure_split_first_n`: for any `n : ℕ`, the joint distribution of
  `(Y₀, …, Y_{n-1})` and the shifted tail `(Y_n, Y_{n+1}, …)` factors as
  the product of `Measure.pi (fun _ : Fin n => Z_uniform)` (the law of the
  first `n` coordinates) and `step_measure` again (the law of the tail).

Both follow from the uniqueness theorem `eq_infinitePi`: it suffices to
verify the candidate measure agrees with `infinitePi (fun _ => Z_uniform)`
on every measurable cylinder `Set.pi s t`. -/

/-- The left-shift map `Y ↦ Y ∘ Nat.succ`. -/
private def shiftSucc : (ℕ → F2) → (ℕ → F2) := fun Y => Y ∘ Nat.succ

private lemma measurable_shiftSucc : Measurable shiftSucc := by
  unfold shiftSucc
  exact measurable_pi_lambda _ (fun n => measurable_pi_apply _)

/-- **Wave 35.2a Deliverable 1.** The infinite-product `step_measure` is
invariant under the one-step left shift on `(ℕ → F2)`: pushing forward by
`Y ↦ Y ∘ Nat.succ` returns `step_measure`. This is the standard i.i.d.
shift-invariance fact, formalised against Mathlib's `Measure.infinitePi`
via the uniqueness theorem `eq_infinitePi`. -/
theorem step_measure_shift_invariant :
    Measure.map (fun (Y : ℕ → F2) => Y ∘ Nat.succ) step_measure = step_measure := by
  -- Reformulate so the function is `shiftSucc`.
  change Measure.map shiftSucc step_measure = step_measure
  -- Apply uniqueness: it suffices to check cylinder masses.
  show Measure.map shiftSucc step_measure
    = Measure.infinitePi (fun _ : ℕ => Z_uniform)
  refine Measure.eq_infinitePi (μ := fun _ : ℕ => Z_uniform)
    (ν := Measure.map shiftSucc step_measure) ?_
  intro s t ht
  classical
  -- Define an extension `t' : ℕ → Set F2` with `t' (i+1) = t i` and
  -- `t' 0 = univ`.  Then `shiftSucc⁻¹' (Set.pi s t) = Set.pi (s.image Nat.succ) t'`.
  set t' : ℕ → Set F2 := fun j => Nat.rec Set.univ (fun i _ => t i) j with ht'_def
  have ht'_succ : ∀ i, t' (i + 1) = t i := fun i => rfl
  have ht'_meas : ∀ j, MeasurableSet (t' j) := by
    intro j
    cases j with
    | zero => exact MeasurableSet.univ
    | succ i => exact ht i
  -- The preimage description.
  have h_preimage : shiftSucc ⁻¹' Set.pi (s : Set ℕ) t
      = Set.pi ((s.image Nat.succ : Finset ℕ) : Set ℕ) t' := by
    ext Y
    simp only [Set.mem_preimage, Set.mem_pi, Finset.coe_image, Finset.mem_coe,
      Set.mem_image]
    refine ⟨?_, ?_⟩
    · intro h j hj
      obtain ⟨i, hi, rfl⟩ := hj
      have := h i hi
      simpa [shiftSucc, ht'_succ] using this
    · intro h i hi
      have h_succ : Nat.succ i ∈ (s.image Nat.succ : Finset ℕ) :=
        Finset.mem_image.mpr ⟨i, hi, rfl⟩
      have := h (Nat.succ i) (by simpa using h_succ)
      simpa [shiftSucc, ht'_succ] using this
  -- Compute the LHS using `infinitePi_pi`.
  rw [Measure.map_apply measurable_shiftSucc
    (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))]
  rw [h_preimage]
  rw [show step_measure = Measure.infinitePi (fun _ : ℕ => Z_uniform) from rfl]
  rw [Measure.infinitePi_pi (μ := fun _ : ℕ => Z_uniform)
    (s := s.image Nat.succ) (t := t') (fun j _ => ht'_meas j)]
  -- Now reindex the product over `s.image Nat.succ` to a product over `s`.
  have h_inj : Set.InjOn Nat.succ s := fun a _ b _ h => Nat.succ_injective h
  rw [Finset.prod_image (f := fun j => Z_uniform (t' j)) (g := Nat.succ)
    (fun a _ b _ h => Nat.succ_injective h)]

/-- The split map `Y ↦ (Y ∘ Fin.val, Y ∘ (· + n))` decomposing a sequence
into its first `n` coordinates and its tail. -/
private def splitFirstN (n : ℕ) : (ℕ → F2) → (Fin n → F2) × (ℕ → F2) :=
  fun Y => (fun i : Fin n => Y i.val, fun j => Y (j + n))

private lemma measurable_splitFirstN (n : ℕ) : Measurable (splitFirstN n) := by
  refine Measurable.prodMk ?_ ?_
  · exact measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  · exact measurable_pi_lambda _ (fun j => measurable_pi_apply _)

/-- The inverse of the split map: glue a prefix and a tail back into
a sequence on `ℕ`. -/
private def gluePrefix (n : ℕ) : (Fin n → F2) × (ℕ → F2) → (ℕ → F2) :=
  fun p k => if hk : k < n then p.1 ⟨k, hk⟩ else p.2 (k - n)

private lemma measurable_gluePrefix (n : ℕ) : Measurable (gluePrefix n) := by
  refine measurable_pi_lambda _ (fun k => ?_)
  by_cases hk : k < n
  · simp only [gluePrefix, dif_pos hk]
    exact (measurable_pi_apply _).comp measurable_fst
  · simp only [gluePrefix, dif_neg hk]
    exact (measurable_pi_apply _).comp measurable_snd

/-- `gluePrefix n` is a left inverse of `splitFirstN n`. -/
private lemma gluePrefix_splitFirstN (n : ℕ) (Y : ℕ → F2) :
    gluePrefix n (splitFirstN n Y) = Y := by
  funext k
  by_cases hk : k < n
  · simp [gluePrefix, splitFirstN, hk]
  · simp only [gluePrefix, splitFirstN, dif_neg hk]
    -- `(k - n) + n = k` since `n ≤ k`.
    have : k - n + n = k := by omega
    rw [this]

/-- Auxiliary: peel-off-one-coordinate map
`(F2) × (ℕ → F2) → (ℕ → F2)` that prepends a value to a sequence,
i.e. `(z, Y') ↦ (z, Y'_0, Y'_1, …)`. -/
def consSucc : F2 × (ℕ → F2) → (ℕ → F2) :=
  fun p k => Nat.rec p.1 (fun i _ => p.2 i) k

lemma measurable_consSucc : Measurable consSucc := by
  refine measurable_pi_lambda _ (fun k => ?_)
  cases k with
  | zero =>
    show Measurable (fun p : F2 × (ℕ → F2) => p.1)
    exact measurable_fst
  | succ i =>
    show Measurable (fun p : F2 × (ℕ → F2) => p.2 i)
    exact (measurable_pi_apply _).comp measurable_snd

lemma consSucc_zero (z : F2) (Y' : ℕ → F2) : consSucc (z, Y') 0 = z := rfl
lemma consSucc_succ (z : F2) (Y' : ℕ → F2) (i : ℕ) :
    consSucc (z, Y') (i + 1) = Y' i := rfl

/-- The "shift the head off" map `Y ↦ (Y_0, Y ∘ Nat.succ)`, the inverse of
`consSucc`. -/
def headShift : (ℕ → F2) → F2 × (ℕ → F2) :=
  fun Y => (Y 0, Y ∘ Nat.succ)

lemma measurable_headShift : Measurable headShift := by
  refine Measurable.prodMk ?_ measurable_shiftSucc
  exact measurable_pi_apply 0

lemma headShift_consSucc (p : F2 × (ℕ → F2)) :
    headShift (consSucc p) = p := by
  rcases p with ⟨z, Y'⟩
  refine Prod.ext ?_ ?_
  · rfl
  · funext k; rfl

lemma consSucc_headShift (Y : ℕ → F2) : consSucc (headShift Y) = Y := by
  funext k
  cases k with
  | zero => rfl
  | succ i => rfl

/-- **Wave 35.2a head-shift factorisation.** `step_measure` pushed forward
through the head-shift map factorises as `Z_uniform.prod step_measure`. The
structural step underlying the inductive proof of any `n`-step splitting,
and the key engine for the Wave 35.3 keystone. -/
lemma step_measure_head_shift :
    Measure.map headShift step_measure = Z_uniform.prod step_measure := by
  -- Both sides are probability measures on `F2 × (ℕ → F2)`.  We push
  -- both forward through `consSucc` and check they agree as measures
  -- on `ℕ → F2`.
  --
  -- Step A: `Measure.map consSucc (Measure.map headShift step_measure) = step_measure`
  -- Step B: `Measure.map consSucc (Z_uniform.prod step_measure) = step_measure`
  -- Both via existing facts; then invert via `Measure.map (headShift)` of both.
  have hA : Measure.map consSucc (Measure.map headShift step_measure) = step_measure := by
    rw [Measure.map_map measurable_consSucc measurable_headShift]
    have hcomp : consSucc ∘ headShift = id := by
      funext Y; exact consSucc_headShift Y
    rw [hcomp, Measure.map_id]
  have hB : Measure.map consSucc (Z_uniform.prod step_measure) = step_measure := by
    -- Use `eq_infinitePi`.
    show Measure.map consSucc (Z_uniform.prod step_measure)
      = Measure.infinitePi (fun _ : ℕ => Z_uniform)
    refine Measure.eq_infinitePi (μ := fun _ : ℕ => Z_uniform)
      (ν := Measure.map consSucc (Z_uniform.prod step_measure)) ?_
    intro s t ht
    -- Compute the LHS.
    rw [Measure.map_apply measurable_consSucc
      (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))]
    -- Preimage description: split `s` into "0 ∈ s?" and the rest shifted by 1.
    classical
    by_cases h0 : 0 ∈ s
    · -- 0 ∈ s case: factor as `t 0` × shifted constraint
      -- Re-index "high" indices via `Nat.succ` rather than `Nat.pred`,
      -- so unfolding `consSucc` is purely on the `succ` side.
      -- We re-index "high" indices via `Nat.succ`: `s' := (s.erase 0).preimage Nat.succ`.
      set s' : Finset ℕ := (s.erase 0).preimage Nat.succ
        (Set.injOn_of_injective Nat.succ_injective) with hs'_def
      have hs'_iff : ∀ k : ℕ, k ∈ s' ↔ k.succ ∈ s := by
        intro k
        rw [hs'_def, Finset.mem_preimage, Finset.mem_erase]
        exact ⟨fun h => h.2, fun h => ⟨Nat.succ_ne_zero k, h⟩⟩
      have h_preimage : consSucc ⁻¹' Set.pi (s : Set ℕ) t
          = (t 0) ×ˢ Set.pi (s' : Set ℕ) (fun j : ℕ => t (j + 1)) := by
        ext ⟨z, Y'⟩
        constructor
        · intro h
          refine ⟨?_, ?_⟩
          · have := h 0 h0
            show z ∈ t 0
            change consSucc (z, Y') 0 ∈ t 0 at this
            rw [consSucc_zero] at this; exact this
          · intro k hk
            have hk' : k.succ ∈ s := (hs'_iff k).mp hk
            have := h k.succ hk'
            change consSucc (z, Y') k.succ ∈ t k.succ at this
            rw [consSucc_succ] at this
            exact this
        · rintro ⟨hz, hY'⟩ k hk
          cases k with
          | zero =>
            show consSucc (z, Y') 0 ∈ t 0
            rw [consSucc_zero]; exact hz
          | succ i =>
            have hi_in : i ∈ s' := (hs'_iff i).mpr hk
            have := hY' i hi_in
            show consSucc (z, Y') i.succ ∈ t i.succ
            rw [consSucc_succ]; exact this
      rw [h_preimage, Measure.prod_prod]
      -- Compute the tail factor via `infinitePi_pi`.
      have ht_meas_succ : ∀ j : ℕ, MeasurableSet (t (j + 1)) := fun j => ht (j + 1)
      rw [show step_measure = Measure.infinitePi (fun _ : ℕ => Z_uniform) from rfl]
      rw [Measure.infinitePi_pi (μ := fun _ : ℕ => Z_uniform)
        (s := s') (t := fun j => t (j + 1))
        (fun j _ => ht_meas_succ j)]
      -- Now we have `Z_uniform (t 0) * ∏ j ∈ s', Z_uniform (t (j+1))`.
      -- Goal: equal to `∏ i ∈ s, Z_uniform (t i)`.
      -- Use `s = insert 0 (s.erase 0)` and identify `s.erase 0 ↔ s'.image Nat.succ`.
      have h_image : s.erase 0 = s'.image Nat.succ := by
        ext k
        rw [Finset.mem_image]
        constructor
        · intro hk
          have hk_ne : k ≠ 0 := (Finset.mem_erase.mp hk).1
          have hk_in : k ∈ s := (Finset.mem_erase.mp hk).2
          have hk_pos : 0 < k := Nat.pos_of_ne_zero hk_ne
          refine ⟨k.pred, ?_, Nat.succ_pred_eq_of_pos hk_pos⟩
          rw [hs'_iff, Nat.succ_pred_eq_of_pos hk_pos]
          exact hk_in
        · rintro ⟨j, hj_in_s', rfl⟩
          have hj_succ_in : j.succ ∈ s := (hs'_iff j).mp hj_in_s'
          exact Finset.mem_erase.mpr ⟨Nat.succ_ne_zero j, hj_succ_in⟩
      have h_split : (∏ i ∈ s, Z_uniform (t i))
          = Z_uniform (t 0) * ∏ a ∈ s.erase 0, Z_uniform (t a) := by
        conv_lhs => rw [show s = insert 0 (s.erase 0) from (Finset.insert_erase h0).symm]
        rw [Finset.prod_insert (Finset.notMem_erase 0 s)]
      rw [h_split, h_image,
        Finset.prod_image (f := fun a => Z_uniform (t a)) (g := Nat.succ)
          (fun a _ b _ h => Nat.succ_injective h)]
    · -- 0 ∉ s case
      set s' : Finset ℕ := s.preimage Nat.succ
        (Set.injOn_of_injective Nat.succ_injective) with hs'_def
      have hs'_iff : ∀ k : ℕ, k ∈ s' ↔ k.succ ∈ s := by
        intro k; rw [hs'_def, Finset.mem_preimage]
      have h_preimage : consSucc ⁻¹' Set.pi (s : Set ℕ) t
          = Set.univ ×ˢ Set.pi (s' : Set ℕ) (fun j : ℕ => t (j + 1)) := by
        ext ⟨z, Y'⟩
        simp only [Set.mem_prod, Set.mem_univ, true_and, Set.mem_preimage]
        constructor
        · intro h k hk
          have hk' : k.succ ∈ s := (hs'_iff k).mp hk
          have := h k.succ hk'
          change consSucc (z, Y') k.succ ∈ t k.succ at this
          rw [consSucc_succ] at this; exact this
        · intro hY' k hk
          cases k with
          | zero => exact absurd hk h0
          | succ i =>
            have hi_in : i ∈ s' := (hs'_iff i).mpr hk
            have := hY' i hi_in
            show consSucc (z, Y') i.succ ∈ t i.succ
            rw [consSucc_succ]; exact this
      rw [h_preimage, Measure.prod_prod]
      rw [show step_measure = Measure.infinitePi (fun _ : ℕ => Z_uniform) from rfl]
      have ht_meas_succ : ∀ j : ℕ, MeasurableSet (t (j + 1)) := fun j => ht (j + 1)
      rw [Measure.infinitePi_pi (μ := fun _ : ℕ => Z_uniform)
        (s := s') (t := fun j => t (j + 1))
        (fun j _ => ht_meas_succ j)]
      rw [show Z_uniform (Set.univ : Set F2) = 1 from measure_univ, one_mul]
      -- Goal: `∏ j ∈ s', Z_uniform (t (j+1)) = ∏ i ∈ s, Z_uniform (t i)`
      have h_image : s = s'.image Nat.succ := by
        ext k
        rw [Finset.mem_image]
        constructor
        · intro hk
          have hk_ne : k ≠ 0 := fun heq => h0 (heq ▸ hk)
          have hk_pos : 0 < k := Nat.pos_of_ne_zero hk_ne
          refine ⟨k.pred, ?_, Nat.succ_pred_eq_of_pos hk_pos⟩
          rw [hs'_iff, Nat.succ_pred_eq_of_pos hk_pos]; exact hk
        · rintro ⟨j, hj_in_s', rfl⟩
          exact (hs'_iff j).mp hj_in_s'
      rw [h_image, Finset.prod_image (f := fun a => Z_uniform (t a)) (g := Nat.succ)
        (fun a _ b _ h => Nat.succ_injective h)]
  -- From hA = hB, push back via `Measure.map headShift` on both sides.
  have h_eq : Measure.map consSucc (Measure.map headShift step_measure)
      = Measure.map consSucc (Z_uniform.prod step_measure) := by
    rw [hA, hB]
  -- Use that `headShift ∘ consSucc = id`.
  have hcomp : headShift ∘ consSucc = id := by
    funext p; exact headShift_consSucc p
  calc Measure.map headShift step_measure
      = Measure.map headShift (Measure.map consSucc (Measure.map headShift step_measure)) := by
        rw [Measure.map_map measurable_headShift measurable_consSucc, hcomp,
          Measure.map_id]
    _ = Measure.map headShift (Measure.map consSucc (Z_uniform.prod step_measure)) := by
        rw [h_eq]
    _ = Z_uniform.prod step_measure := by
        rw [Measure.map_map measurable_headShift measurable_consSucc, hcomp,
          Measure.map_id]

/-! ### Wave 35.2c — coordinate-wise lift of `Z_uniform`-preserving maps

**Step C of the F_2-symmetry programme.** For any measurable map
`τ : F2 → F2` whose pushforward preserves `Z_uniform`, the coordinate-wise
lift `Y ↦ τ ∘ Y : (ℕ → F2) → (ℕ → F2)` preserves `step_measure`.

The proof is by `Measure.eq_infinitePi`: for any measurable cylinder
`Set.pi s t`, the preimage under the lift is the cylinder
`Set.pi s (τ⁻¹' ∘ t)`, whose mass under `step_measure = infinitePi Z_uniform`
factors as `∏ i ∈ s, Z_uniform (τ⁻¹' (t i))`. By the hypothesis, each factor
equals `Z_uniform (t i)`, recovering the cylinder mass of `step_measure`.

The cleanest sufficient condition (Step C2): if `τ : F2 → F2` is a bijection
that maps `F2_generating_set` bijectively onto itself, then `τ` preserves
`Z_uniform`. This is the "permutation of the four-Dirac sum" computation.

Steps A, B, D, E build on this structural lemma. -/

/-- The coordinate-wise lift of `τ` to `(ℕ → F2)`. -/
private def coordLift (τ : F2 → F2) : (ℕ → F2) → (ℕ → F2) :=
  fun Y => τ ∘ Y

private lemma measurable_F2_to_F2 (τ : F2 → F2) : Measurable τ := by
  -- With `MeasurableSpace F2 = ⊤`, every set is measurable.
  intro s _
  exact trivial

private lemma measurable_coordLift (τ : F2 → F2) :
    Measurable (coordLift τ) := by
  -- With `MeasurableSpace F2 = ⊤`, every function `F2 → F2` is measurable,
  -- and so is the coordinate-wise lift.
  refine measurable_pi_lambda _ (fun n => ?_)
  show Measurable (fun Y : ℕ → F2 => τ (Y n))
  exact (measurable_F2_to_F2 τ).comp (measurable_pi_apply n)

/-- **Step C of Wave 35.2c.** The coordinate-wise lift of any
`Z_uniform`-preserving measurable map `τ : F2 → F2` preserves `step_measure`.

Proof via `Measure.eq_infinitePi`: a cylinder mass under the pushforward
equals `∏ i ∈ s, (Measure.map τ Z_uniform) (t i)`, which by hypothesis
equals the cylinder mass of `step_measure`. -/
lemma step_measure_coordLift_invariant
    (τ : F2 → F2) (h_pres : Measure.map τ Z_uniform = Z_uniform) :
    Measure.map (coordLift τ) step_measure = step_measure := by
  show Measure.map (coordLift τ) step_measure
    = Measure.infinitePi (fun _ : ℕ => Z_uniform)
  refine Measure.eq_infinitePi (μ := fun _ : ℕ => Z_uniform)
    (ν := Measure.map (coordLift τ) step_measure) ?_
  intro s t ht
  -- `coordLift τ ⁻¹' Set.pi s t = Set.pi s (fun i => τ⁻¹' (t i))`.
  have h_preimage :
      coordLift τ ⁻¹' (Set.pi (s : Set ℕ) t : Set (ℕ → F2))
        = Set.pi (s : Set ℕ) (fun i => τ⁻¹' (t i)) := by
    ext Y
    simp only [Set.mem_preimage, Set.mem_pi, coordLift, Function.comp_apply]
  -- Compute the LHS via `Measure.map_apply`.
  have h_meas_pre : ∀ i, MeasurableSet (τ ⁻¹' (t i)) := fun i => trivial
  rw [Measure.map_apply (measurable_coordLift τ)
    (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))]
  rw [h_preimage]
  rw [show step_measure = Measure.infinitePi (fun _ : ℕ => Z_uniform) from rfl]
  rw [Measure.infinitePi_pi (μ := fun _ : ℕ => Z_uniform)
    (s := s) (t := fun i => τ⁻¹' (t i))
    (fun i _ => h_meas_pre i)]
  -- Each factor: `Z_uniform (τ⁻¹' (t i)) = (Measure.map τ Z_uniform) (t i) = Z_uniform (t i)`.
  apply Finset.prod_congr rfl
  intro i _
  show Z_uniform (τ ⁻¹' (t i)) = Z_uniform (t i)
  rw [show Z_uniform (τ ⁻¹' (t i)) = (Measure.map τ Z_uniform) (t i) from
    (Measure.map_apply (measurable_F2_to_F2 τ) (ht i)).symm]
  rw [h_pres]

/-! ### Wave 35.2c — sufficient condition for `Z_uniform` preservation

A measurable map `τ : F2 → F2` preserves `Z_uniform` whenever the four
generators `genA, genB, genA⁻¹, genB⁻¹` are mapped to a permutation of
themselves. Since `Z_uniform = (1/4) (δ_{genA} + δ_{genB} + δ_{genA⁻¹}
+ δ_{genB⁻¹})` and pushforward is linear, the result follows from the
identity `δ_{τ(g)} = Measure.map τ (δ_g)` and the invariance of the
four-Dirac sum under permutation.

We delay the explicit `Z_uniform`-preservation lemma until after
`F2_genFinset` is in scope; in this introductory section, we provide
only the structural ingredient `step_measure_coordLift_invariant`. -/

/-! **Note (Wave 35.2a).** The general first-`n` split deliverable
`Measure.map (fun Y => (Y ∘ Fin.val, Y ∘ (· + n))) step_measure
  = (Measure.pi (fun _ : Fin n => Z_uniform)).prod step_measure`
is deferred to a follow-up sub-sub-wave (Wave 35.2b).  The single-step
version `step_measure_head_shift` proven above is the engine for
Wave 35.2/35.3 downstream — the inductive composition with
`MeasurableEquiv.piFinSuccAboveEquiv` (or an equivalent snoc-style
re-glue lemma) is the missing piece, and is purely a matter of
Mathlib measure-product associativity rather than further probabilistic
content. -/

/-- The random walk `X_n = Y_0 · Y_1 · ⋯ · Y_{n−1}` starting at the identity
in `F_2`. -/
def X_walk : ℕ → (ℕ → F2) → F2
  | 0, _ => 1
  | n + 1, Y => X_walk n Y * Y n

@[simp] lemma X_walk_zero (Y : ℕ → F2) : X_walk 0 Y = 1 := rfl

@[simp] lemma X_walk_succ (n : ℕ) (Y : ℕ → F2) :
    X_walk (n + 1) Y = X_walk n Y * Y n := rfl

/-- **Wave 32 helper.** The random-walk position map `X_walk n` is
measurable as a function `(ℕ → F2) → F2`.  With `MeasurableSpace F2 := ⊤`
the codomain has every set measurable, so by `measurable_to_countable'`
it suffices to check that every singleton fiber is measurable.  Each
fiber depends only on the first `n` coordinates of `Y` (a measurable
cylinder set in the product σ-algebra), proved by induction on `n`. -/
lemma X_walk_measurable (n : ℕ) : Measurable (X_walk n) := by
  -- Reduce to fiber-wise: the codomain `F2` is countable
  -- (`Countable (FreeGroup (Fin 2))` from `Quotient.countable`
  -- on the countable list `List (Fin 2 × Bool)`) and has top σ-algebra,
  -- so `MeasurableSingletonClass F2` holds.
  apply measurable_to_countable'
  intro x
  -- Goal: `MeasurableSet ((X_walk n)⁻¹ {x})`.  Induct on `n`.
  induction n generalizing x with
  | zero =>
      -- `X_walk 0 Y = 1`, so the fiber is either `univ` (if `x = 1`)
      -- or `∅` (otherwise).
      by_cases hx : x = (1 : F2)
      · subst hx
        have heq : (X_walk 0)⁻¹' ({(1 : F2)} : Set F2) = Set.univ := by
          ext Y; simp [X_walk_zero]
        rw [heq]; exact MeasurableSet.univ
      · have heq : (X_walk 0)⁻¹' ({x} : Set F2) = ∅ := by
          ext Y
          simp only [Set.mem_preimage, X_walk_zero, Set.mem_singleton_iff,
            Set.mem_empty_iff_false, iff_false]
          intro h; exact hx h.symm
        rw [heq]; exact MeasurableSet.empty
  | succ n ih =>
      -- `(X_walk (n+1))⁻¹{x} = ⋃_{a, b : F2, a * b = x}
      --   ((X_walk n)⁻¹{a} ∩ (eval n)⁻¹{b})`.
      -- Each piece is measurable; F2 × F2 is countable so the union is countable.
      have hkey : (X_walk (n + 1))⁻¹' ({x} : Set F2)
          = ⋃ (p : F2 × F2) (_ : p.1 * p.2 = x),
              (X_walk n)⁻¹' {p.1} ∩ (fun Y : ℕ → F2 => Y n)⁻¹' {p.2} := by
        ext Y
        simp only [Set.mem_preimage, Set.mem_singleton_iff, X_walk_succ,
          Set.mem_iUnion, Set.mem_inter_iff, Prod.exists]
        constructor
        · intro h
          exact ⟨X_walk n Y, Y n, h, rfl, rfl⟩
        · rintro ⟨a, b, hab, ha, hb⟩
          rw [ha, hb]; exact hab
      rw [hkey]
      refine MeasurableSet.iUnion (fun p => ?_)
      refine MeasurableSet.iUnion (fun _ => ?_)
      exact (ih p.1).inter ((measurable_pi_apply n) (MeasurableSet.singleton p.2))

/-! ### Wave 23C — generic i.i.d.-Bernoulli lemma for past-measurable
indicator families

Both Q42 (`away_indicator`) and Q43/Q44 (`coupledIndicator`) need the same
underlying probabilistic principle: under the uniform infinite-product
`step_measure`, an indicator family `f_k(Y) := 1[Y_k ∈ A_k(Y)]` where
`A_k(Y)` is past-measurable (depends only on `Y_0, …, Y_{k-1}`) and has
constant cardinality `c` is i.i.d. Bernoulli(c/4) — the "constant
conditional law ⇒ unconditional independence" theorem
(Williams, *Probability with Martingales*, §9.7).

Wave 23C consolidates both narrow probabilistic admissions
(`away_indicator_iIndepFun_iIdentDistrib`,
`coupledIndicator_iIndepFun_iIdentDistrib`) into one strictly more general
companion axiom `iIndepFun_iIdentDistrib_uniformIndic_pastDep`. The
specialised statements at the two call sites are then **theorems** derived
from this single Mathlib-API-gap admission. -/

/-! **Wave 23C/Wave 33 — companion theorem context.** Generic i.i.d.
Bernoulli law for past-measurable indicator families on the uniform-step
infinite product measure.

Let `A : ℕ → (ℕ → F2) → Finset F2` be a sequence of finite subsets of `F2`
satisfying:
* **past-measurability**: for each `k`, `A k Y` depends only on the prefix
  `(Y_0, …, Y_{k-1})`, i.e. `Y j = Y' j` for all `j < k` implies
  `A k Y = A k Y'`;
* **constant cardinality**: there exists `c : ℕ` such that `(A k Y).card = c`
  for all `k, Y`;
* **subset of generating set**: for the marginal mean to compute as `c/4`,
  we additionally require `A k Y ⊆ F2_generating_set` (so that `Y k ∈ A k Y`
  has probability `c/4` under the uniform `Z_uniform`).

Define `f_k(Y) := if Y k ∈ A k Y then (1 : ℝ) else 0`. Then under
`step_measure = Measure.infinitePi (fun _ => Z_uniform)`:
1. The family `(f_k)_{k : ℕ}` is mutually independent (`iIndepFun`).
2. Each `f_k` is identically distributed to `f_0`.
3. The marginal mean is `c/4`: `∫ Y, f_0 Y ∂step_measure = c/4`.

**Mathematical proof (Williams, §9.7).** Conditional on
`F_k := σ(Y_0, …, Y_{k-1})`, the past-measurable subset `A k Y` is
determined; `Y k` is independent of `F_k` (product structure of
`infinitePi`) and uniformly distributed on the 4-element
`F2_generating_set`. Hence

    P(f_k = 1 | F_k) = P(Y_k ∈ A k Y | F_k) = (A k Y).card / 4 = c/4,

a constant. By the constant-conditional-probability ⇒ independence
theorem (factorisation of conditional expectation), `f_k ⊥ F_k`. Since
each `f_j` for `j < k` is `F_{j+1} ⊆ F_k`-measurable, `f_k` is
independent of `(f_0, …, f_{k-1})`. Iterating yields mutual independence.
Identical distribution and the marginal mean follow by integrating the
constant conditional probability.

**Why an axiom (Mathlib API gap).** Mathlib provides
`iIndepFun_infinitePi` for **coordinate** functions on `infinitePi` but no
direct API for the conditional-law-factorisation step on a derived family
of indicators of varying past-dependent events. A formal proof would
require building the natural filtration `σ(Y_0, …, Y_{k-1})` and applying
the conditional-expectation factorisation lemma — ~200 LOC of
measure-theoretic plumbing for the textbook fact.

**References.** Williams, *Probability with Martingales*, §9.7
(conditional expectation, factorisation lemma); Klenke, *Probability
Theory*, §5.3 (independence and conditional distributions).

**Strictly weaker than the prior pair** (Wave 23A.3 and Wave 23B
admissions): both `coupledIndicator_iIndepFun_iIdentDistrib` (1-element
target `A k Y = {mk[letterToCancel k Y]}`, c=1, 1/4) and
`away_indicator_iIndepFun_iIdentDistrib` (3-element target
`AwayGenerators(X_walk k Y)`, c=3, 3/4) are now **theorems** derived from
this generic axiom by specialising `A` and `c`.

**Load-bearing.** Wave 23B Hoeffding tail (Q42), Wave 23A SLLN coupling
(Q43), Wave 23A.4 transience (Q44).

**Wave 33 update.** This was promoted from a companion axiom to a fully
proven theorem. The Lean encoding follows the elementary 10-line counting
argument from `williams_97_note.tex` §1: for each finite index set
`I ⊆ ℕ` and each `ε : I → {0,1}`, the joint event
`⋂ i ∈ I, {f i = ε i}` is a cylinder in the first `M = max I + 1`
coordinates. By Fubini (here packaged as `step_measure_prefix_cylinder`),
each cylinder has mass `(1/4)^M` per realising prefix. The realising
prefixes are counted by induction: at coordinate `ℓ`, the number of
admissible values `y_ℓ` is `c` (if `ℓ ∈ I` and `ε_ℓ = 1`), `4 − c`
(if `ℓ ∈ I` and `ε_ℓ = 0`), or `4` (if `ℓ ∉ I`). The count does NOT
depend on the prefix `(y_0, …, y_{ℓ-1})` — only its cardinality, by
`h_card`. The product of counts divided by `4^M` factorises as
`∏ i ∈ I (c/4)^{ε_i} (1 − c/4)^{1 − ε_i}`, proving both i.i.d.
and Bernoulli$(c/4)$ marginals. -/

/-! ### Wave 33 prerequisites — measure-theoretic helpers

These helpers (originally introduced in Wave 28 for the binomial-PMF
chain) are consolidated here, before
`iIndepFun_iIdentDistrib_uniformIndic_pastDep`, since the proof of the
generic i.i.d. theorem requires the same prefix/cylinder/counting
infrastructure (`extendPrefix`, `extOne`, `fixedPrefixCylinder`, …). -/

/-! #### Pairwise distinctness of the four generators of `F_2` -/

private lemma genA_ne_genB : (genA : F2) ≠ genB := by
  intro h
  have := congrArg _root_.FreeGroup.toWord h
  rw [show (genA : F2) = _root_.FreeGroup.of 0 from rfl,
      show (genB : F2) = _root_.FreeGroup.of 1 from rfl,
      _root_.FreeGroup.toWord_of, _root_.FreeGroup.toWord_of] at this
  simp at this

private lemma genA_ne_genA_inv : (genA : F2) ≠ (genA : F2)⁻¹ := by
  intro h
  have := congrArg _root_.FreeGroup.toWord h
  rw [show (genA : F2) = _root_.FreeGroup.of 0 from rfl,
      _root_.FreeGroup.toWord_of, _root_.FreeGroup.toWord_inv,
      _root_.FreeGroup.toWord_of] at this
  simp [_root_.FreeGroup.invRev] at this

private lemma genA_ne_genB_inv : (genA : F2) ≠ (genB : F2)⁻¹ := by
  intro h
  have := congrArg _root_.FreeGroup.toWord h
  rw [show (genA : F2) = _root_.FreeGroup.of 0 from rfl,
      show (genB : F2) = _root_.FreeGroup.of 1 from rfl,
      _root_.FreeGroup.toWord_of, _root_.FreeGroup.toWord_inv,
      _root_.FreeGroup.toWord_of] at this
  simp [_root_.FreeGroup.invRev] at this

private lemma genB_ne_genA_inv : (genB : F2) ≠ (genA : F2)⁻¹ := by
  intro h
  have := congrArg _root_.FreeGroup.toWord h
  rw [show (genA : F2) = _root_.FreeGroup.of 0 from rfl,
      show (genB : F2) = _root_.FreeGroup.of 1 from rfl,
      _root_.FreeGroup.toWord_of, _root_.FreeGroup.toWord_inv,
      _root_.FreeGroup.toWord_of] at this
  simp [_root_.FreeGroup.invRev] at this

private lemma genB_ne_genB_inv : (genB : F2) ≠ (genB : F2)⁻¹ := by
  intro h
  have := congrArg _root_.FreeGroup.toWord h
  rw [show (genB : F2) = _root_.FreeGroup.of 1 from rfl,
      _root_.FreeGroup.toWord_of, _root_.FreeGroup.toWord_inv,
      _root_.FreeGroup.toWord_of] at this
  simp [_root_.FreeGroup.invRev] at this

private lemma genA_inv_ne_genB_inv : (genA : F2)⁻¹ ≠ (genB : F2)⁻¹ := by
  intro h
  exact genA_ne_genB (inv_injective h)

/-- The 4-element `Finset` form of `F2_generating_set`. -/
private noncomputable def F2_genFinset : Finset F2 :=
  {genA, genB, genA⁻¹, genB⁻¹}

/-- The four generators are pairwise distinct, hence `F2_genFinset` has cardinality 4.
Uses the existing pairwise-distinctness lemmas (`genA_ne_genB`, `genA_ne_genA_inv`,
`genA_ne_genB_inv`, `genB_ne_genA_inv`, `genB_ne_genB_inv`,
`genA_inv_ne_genB_inv`). -/
private lemma F2_genFinset_card : F2_genFinset.card = 4 := by
  have h1 : (genA : F2) ∉ ({genB, genA⁻¹, genB⁻¹} : Finset F2) := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact genA_ne_genB h
    rcases Finset.mem_insert.mp h with h | h
    · exact genA_ne_genA_inv h
    · exact genA_ne_genB_inv (Finset.mem_singleton.mp h)
  have h2 : (genB : F2) ∉ ({genA⁻¹, genB⁻¹} : Finset F2) := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact genB_ne_genA_inv h
    · exact genB_ne_genB_inv (Finset.mem_singleton.mp h)
  have h3 : (genA⁻¹ : F2) ∉ ({genB⁻¹} : Finset F2) := by
    intro h
    exact genA_inv_ne_genB_inv (Finset.mem_singleton.mp h)
  unfold F2_genFinset
  rw [show ({genA, genB, genA⁻¹, genB⁻¹} : Finset F2)
        = insert (genA : F2)
            (insert (genB : F2)
              (insert (genA⁻¹ : F2) ({(genB⁻¹ : F2)} : Finset F2))) from rfl]
  rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_insert_of_notMem h3, Finset.card_singleton]

/-- Coercion `↑F2_genFinset = F2_generating_set`. -/
private lemma F2_genFinset_coe : (↑F2_genFinset : Set F2) = F2_generating_set := by
  unfold F2_genFinset F2_generating_set
  ext z
  simp [genA, genB]

/-- Generic single-generator mass: `Z_uniform({g}) = 1/4` whenever `g`
is one of the four generators. The proof factors through a single
"sum-of-four-Diracs" computation parameterised by the indicator
`fun z => z = g`. -/
private lemma Z_uniform_singleton_aux (g : F2)
    (hgmem : g ∈ F2_generating_set) :
    Z_uniform {g} = (1/4 : ℝ≥0∞) := by
  unfold Z_uniform
  rw [Measure.smul_apply, Measure.add_apply, Measure.add_apply,
    Measure.add_apply]
  have h_sum :
      Measure.dirac (genA : F2) {g} + Measure.dirac (genB : F2) {g}
        + Measure.dirac ((genA : F2)⁻¹) {g} + Measure.dirac ((genB : F2)⁻¹) {g}
        = 1 := by
    rcases hgmem with hg | hg | hg | hg
    · have h1 : Measure.dirac (genA : F2) {g} = 1 := by
        rw [Measure.dirac_apply]; exact Set.indicator_of_mem (by
          show genA ∈ ({g} : Set F2); rw [hg]; rfl) _
      have h2 : Measure.dirac (genB : F2) {g} = 0 := by
        rw [Measure.dirac_apply]; refine Set.indicator_of_notMem ?_ _
        show genB ∉ ({g} : Set F2); rw [hg, Set.mem_singleton_iff]
        intro h; exact genA_ne_genB h.symm
      have h3 : Measure.dirac ((genA : F2)⁻¹) {g} = 0 := by
        rw [Measure.dirac_apply]; refine Set.indicator_of_notMem ?_ _
        show (genA : F2)⁻¹ ∉ ({g} : Set F2); rw [hg, Set.mem_singleton_iff]
        intro h; exact genA_ne_genA_inv h.symm
      have h4 : Measure.dirac ((genB : F2)⁻¹) {g} = 0 := by
        rw [Measure.dirac_apply]; refine Set.indicator_of_notMem ?_ _
        show (genB : F2)⁻¹ ∉ ({g} : Set F2); rw [hg, Set.mem_singleton_iff]
        intro h; exact genA_ne_genB_inv h.symm
      rw [h1, h2, h3, h4]; simp
    · have h1 : Measure.dirac (genA : F2) {g} = 0 := by
        rw [Measure.dirac_apply]; refine Set.indicator_of_notMem ?_ _
        show genA ∉ ({g} : Set F2); rw [hg, Set.mem_singleton_iff]
        intro h; exact genA_ne_genB h
      have h2 : Measure.dirac (genB : F2) {g} = 1 := by
        rw [Measure.dirac_apply]; exact Set.indicator_of_mem (by
          show genB ∈ ({g} : Set F2); rw [hg]; rfl) _
      have h3 : Measure.dirac ((genA : F2)⁻¹) {g} = 0 := by
        rw [Measure.dirac_apply]; refine Set.indicator_of_notMem ?_ _
        show (genA : F2)⁻¹ ∉ ({g} : Set F2); rw [hg, Set.mem_singleton_iff]
        intro h; exact genB_ne_genA_inv h.symm
      have h4 : Measure.dirac ((genB : F2)⁻¹) {g} = 0 := by
        rw [Measure.dirac_apply]; refine Set.indicator_of_notMem ?_ _
        show (genB : F2)⁻¹ ∉ ({g} : Set F2); rw [hg, Set.mem_singleton_iff]
        intro h; exact genB_ne_genB_inv h.symm
      rw [h1, h2, h3, h4]; simp
    · have h1 : Measure.dirac (genA : F2) {g} = 0 := by
        rw [Measure.dirac_apply]; refine Set.indicator_of_notMem ?_ _
        show genA ∉ ({g} : Set F2); rw [hg, Set.mem_singleton_iff]
        intro h; exact genA_ne_genA_inv h
      have h2 : Measure.dirac (genB : F2) {g} = 0 := by
        rw [Measure.dirac_apply]; refine Set.indicator_of_notMem ?_ _
        show genB ∉ ({g} : Set F2); rw [hg, Set.mem_singleton_iff]
        intro h; exact genB_ne_genA_inv h
      have h3 : Measure.dirac ((genA : F2)⁻¹) {g} = 1 := by
        rw [Measure.dirac_apply]; exact Set.indicator_of_mem (by
          show (genA : F2)⁻¹ ∈ ({g} : Set F2); rw [hg]; rfl) _
      have h4 : Measure.dirac ((genB : F2)⁻¹) {g} = 0 := by
        rw [Measure.dirac_apply]; refine Set.indicator_of_notMem ?_ _
        show (genB : F2)⁻¹ ∉ ({g} : Set F2); rw [hg, Set.mem_singleton_iff]
        intro h; exact genA_inv_ne_genB_inv h.symm
      rw [h1, h2, h3, h4]; simp
    · have h1 : Measure.dirac (genA : F2) {g} = 0 := by
        rw [Measure.dirac_apply]; refine Set.indicator_of_notMem ?_ _
        show genA ∉ ({g} : Set F2); rw [hg, Set.mem_singleton_iff]
        intro h; exact genA_ne_genB_inv h
      have h2 : Measure.dirac (genB : F2) {g} = 0 := by
        rw [Measure.dirac_apply]; refine Set.indicator_of_notMem ?_ _
        show genB ∉ ({g} : Set F2); rw [hg, Set.mem_singleton_iff]
        intro h; exact genB_ne_genB_inv h
      have h3 : Measure.dirac ((genA : F2)⁻¹) {g} = 0 := by
        rw [Measure.dirac_apply]; refine Set.indicator_of_notMem ?_ _
        show (genA : F2)⁻¹ ∉ ({g} : Set F2); rw [hg, Set.mem_singleton_iff]
        intro h; exact genA_inv_ne_genB_inv h
      have h4 : Measure.dirac ((genB : F2)⁻¹) {g} = 1 := by
        rw [Measure.dirac_apply]; exact Set.indicator_of_mem (by
          show (genB : F2)⁻¹ ∈ ({g} : Set F2); rw [hg]; rfl) _
      rw [h1, h2, h3, h4]; simp
  rw [h_sum]
  simp

private lemma Z_uniform_singleton_of_mem {z : F2} (hz : z ∈ F2_generating_set) :
    Z_uniform {z} = (1/4 : ℝ≥0∞) :=
  Z_uniform_singleton_aux z hz

/-- Mass of a finite subset `S` of the generating set: `card(S)/4`. -/
private lemma Z_uniform_finset_of_subset (S : Finset F2)
    (hS : ↑S ⊆ F2_generating_set) :
    Z_uniform (↑S : Set F2) = (S.card : ℝ≥0∞) / 4 := by
  classical
  have h_eq : (↑S : Set F2) = ⋃ z ∈ S, ({z} : Set F2) := by
    ext z; simp
  rw [h_eq]
  rw [measure_biUnion_finset
    (s := S) (f := fun z => ({z} : Set F2))
    (fun z _ z' _ hzz' => Set.disjoint_singleton.mpr hzz')
    (fun z _ => MeasurableSet.of_discrete)]
  rw [Finset.sum_congr rfl
    (fun z hz => Z_uniform_singleton_of_mem (hS (Finset.mem_coe.mpr hz)))]
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [show ((1 : ℝ≥0∞) / 4) = 4⁻¹ from by simp [div_eq_mul_inv]]
  rw [show ((S.card : ℝ≥0∞) / 4) = (S.card : ℝ≥0∞) * 4⁻¹ from by
    rw [div_eq_mul_inv]]

/-- The fixed-prefix cylinder of length `n` for a chosen prefix
`y : ℕ → F2` has `step_measure`-mass `∏_{i < n} Z_uniform {y i}`. -/
private lemma step_measure_prefix_cylinder (n : ℕ) (y : ℕ → F2) :
    step_measure (Set.pi (Finset.range n : Set ℕ) (fun i => ({y i} : Set F2)))
      = ∏ i ∈ Finset.range n, Z_uniform {y i} := by
  unfold step_measure
  rw [show (Set.pi (Finset.range n : Set ℕ) (fun i => ({y i} : Set F2)))
        = Set.pi (↑(Finset.range n) : Set ℕ) (fun i => ({y i} : Set F2)) from rfl]
  exact MeasureTheory.Measure.infinitePi_pi (μ := fun _ : ℕ => Z_uniform)
    (s := Finset.range n) (fun i _ => MeasurableSet.of_discrete)

/-- For a prefix `y : ℕ → F2` with all coordinates `< n` in the
generating set, the fixed-prefix cylinder has mass `(1/4)^n`. -/
private lemma step_measure_prefix_cylinder_of_all_gen (n : ℕ) (y : ℕ → F2)
    (hy : ∀ i, i < n → y i ∈ F2_generating_set) :
    step_measure (Set.pi (Finset.range n : Set ℕ) (fun i => ({y i} : Set F2)))
      = (1/4 : ℝ≥0∞)^n := by
  rw [step_measure_prefix_cylinder]
  rw [Finset.prod_congr rfl (fun i hi =>
    Z_uniform_singleton_of_mem (hy i (Finset.mem_range.mp hi)))]
  rw [Finset.prod_const, Finset.card_range]

/-- Extend a finite prefix `y : Fin n → F2` to a full sample path
`ℕ → F2` by padding with the identity. -/
private def extendPrefix (n : ℕ) (y : Fin n → F2) : ℕ → F2 := fun k =>
  if hk : k < n then y ⟨k, hk⟩ else 1

@[simp] private lemma extendPrefix_apply_lt (n : ℕ) (y : Fin n → F2)
    (k : ℕ) (hk : k < n) : extendPrefix n y k = y ⟨k, hk⟩ := by
  simp [extendPrefix, hk]

/-- For two prefixes `y y' : Fin n → F2` that agree on `[0, k)` (with
`k ≤ n`), the random walk `X_walk k` produces the same vertex. -/
private lemma X_walk_extendPrefix_congr (n : ℕ) (y y' : Fin n → F2)
    (k : ℕ) (hk : k ≤ n) (h : ∀ j (hj : j < k), y ⟨j, by omega⟩ = y' ⟨j, by omega⟩) :
    X_walk k (extendPrefix n y) = X_walk k (extendPrefix n y') := by
  induction k with
  | zero => simp
  | succ m ih =>
    have hm_le : m ≤ n := by omega
    have hm_lt_n : m < n := by omega
    have h_prefix : ∀ j (hj : j < m), y ⟨j, by omega⟩ = y' ⟨j, by omega⟩ :=
      fun j hj => h j (by omega)
    have h_m : y ⟨m, hm_lt_n⟩ = y' ⟨m, hm_lt_n⟩ := h m (by omega)
    rw [X_walk_succ, X_walk_succ, ih hm_le h_prefix]
    rw [extendPrefix_apply_lt _ _ _ hm_lt_n,
        extendPrefix_apply_lt _ _ _ hm_lt_n, h_m]

/-- The "extend" function: combine a prefix `y' : Fin n → F2` and a last
letter `z : F2` into `Fin (n+1) → F2`. Non-dependent variant of `Fin.snoc`. -/
private def extOne (n : ℕ) (y' : Fin n → F2) (z : F2) : Fin (n+1) → F2 :=
  fun i => if hi : i.val < n then y' ⟨i.val, hi⟩ else z

/-- `extOne` at a `< n` index returns the prefix value. -/
private lemma extOne_apply_lt (n : ℕ) (y' : Fin n → F2) (z : F2)
    (i : Fin (n+1)) (hi : i.val < n) :
    extOne n y' z i = y' ⟨i.val, hi⟩ := by
  unfold extOne; rw [dif_pos hi]

/-- `extOne` at the last index returns the new letter. -/
private lemma extOne_apply_last (n : ℕ) (y' : Fin n → F2) (z : F2) :
    extOne n y' z (Fin.last n) = z := by
  unfold extOne
  have : ¬ (Fin.last n : Fin (n+1)).val < n := by
    show ¬ n < n; omega
  rw [dif_neg this]

/-- `extOne` is injective in both arguments (jointly). -/
private lemma extOne_inj (n : ℕ) {y₁ y₂ : Fin n → F2} {z₁ z₂ : F2}
    (h : extOne n y₁ z₁ = extOne n y₂ z₂) : y₁ = y₂ ∧ z₁ = z₂ := by
  refine ⟨?_, ?_⟩
  · funext j
    have hj : (⟨j.val, by omega⟩ : Fin (n+1)).val < n := j.isLt
    have := congrFun h ⟨j.val, by omega⟩
    rw [extOne_apply_lt n y₁ z₁ _ hj, extOne_apply_lt n y₂ z₂ _ hj] at this
    have hj_eq : (⟨j.val, j.isLt⟩ : Fin n) = j := by ext; rfl
    rw [hj_eq] at this
    exact this
  · have := congrFun h (Fin.last n)
    rw [extOne_apply_last, extOne_apply_last] at this
    exact this

/-- Helper: `extendPrefix n y'` and `extendPrefix (n+1) (extOne n y' z)` agree
on indices `< n`. -/
private lemma extendPrefix_extOne_init (n : ℕ) (y' : Fin n → F2) (z : F2)
    (j : ℕ) (hj : j < n) :
    extendPrefix (n + 1) (extOne n y' z) j = extendPrefix n y' j := by
  have hj1 : j < n + 1 := by omega
  rw [extendPrefix_apply_lt _ _ j hj1,
      extendPrefix_apply_lt _ _ j hj]
  rw [extOne_apply_lt n y' z ⟨j, hj1⟩ hj]

/-- Helper: for `m ≤ n`, `X_walk m (extendPrefix (n+1) (extOne n y' z))
= X_walk m (extendPrefix n y')`. -/
private lemma X_walk_extOne_init (n : ℕ) (y' : Fin n → F2) (z : F2) (m : ℕ)
    (hm : m ≤ n) :
    X_walk m (extendPrefix (n + 1) (extOne n y' z)) =
      X_walk m (extendPrefix n y') := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hm_le : m ≤ n := by omega
    have hm_lt : m < n := by omega
    rw [X_walk_succ, X_walk_succ, ih hm_le]
    rw [extendPrefix_extOne_init n y' z m hm_lt]

/-- For prefix `y : Fin n → F2` valued in `F2_generating_set`, the
fixed-prefix cylinder `{Y | ∀ i < n, Y i = y i}` has `step_measure`-mass
`(1/4)^n`. This is the `Fin n → F2`-flavoured wrapper around
`step_measure_prefix_cylinder_of_all_gen`. -/
private lemma step_measure_fin_prefix_cylinder (n : ℕ) (y : Fin n → F2)
    (hy : ∀ i : Fin n, y i ∈ F2_generating_set) :
    step_measure (Set.pi (Finset.range n : Set ℕ)
        (fun i : ℕ => if hi : i < n then ({y ⟨i, hi⟩} : Set F2) else Set.univ))
      = (1/4 : ℝ≥0∞)^n := by
  have h_set_eq : Set.pi (Finset.range n : Set ℕ)
        (fun i : ℕ => if hi : i < n then ({y ⟨i, hi⟩} : Set F2) else Set.univ)
      = Set.pi (Finset.range n : Set ℕ)
          (fun i : ℕ => ({extendPrefix n y i} : Set F2)) := by
    ext Y
    simp only [Set.mem_pi, Finset.coe_range, Set.mem_Iio]
    constructor
    · intro h i hi
      have := h i hi
      rw [dif_pos hi] at this
      have h_ext : extendPrefix n y i = y ⟨i, hi⟩ := by
        simp [extendPrefix, hi]
      rw [h_ext]; exact this
    · intro h i hi
      have := h i hi
      rw [dif_pos hi]
      have h_ext : extendPrefix n y i = y ⟨i, hi⟩ := by
        simp [extendPrefix, hi]
      rw [← h_ext]; exact this
  rw [h_set_eq]
  rw [step_measure_prefix_cylinder n (extendPrefix n y)]
  rw [Finset.prod_congr rfl (fun i hi => by
    have hi_lt : i < n := Finset.mem_range.mp hi
    have h_ext_mem : extendPrefix n y i ∈ F2_generating_set := by
      rw [extendPrefix_apply_lt n y i hi_lt]; exact hy ⟨i, hi_lt⟩
    exact Z_uniform_singleton_of_mem h_ext_mem)]
  rw [Finset.prod_const, Finset.card_range]

/-- The fixed-prefix cylinder, as a subset of `ℕ → F2`, in a clean form. -/
private def fixedPrefixCylinder (n : ℕ) (y : Fin n → F2) : Set (ℕ → F2) :=
  {Y | ∀ i : Fin n, Y i.val = y i}

/-- `fixedPrefixCylinder n y` is the same as the `Set.pi`-cylinder over
`Finset.range n`. -/
private lemma fixedPrefixCylinder_eq (n : ℕ) (y : Fin n → F2) :
    fixedPrefixCylinder n y =
      Set.pi (Finset.range n : Set ℕ)
        (fun i : ℕ => if hi : i < n then ({y ⟨i, hi⟩} : Set F2) else Set.univ) := by
  ext Y
  simp only [fixedPrefixCylinder, Set.mem_setOf_eq, Set.mem_pi,
    Finset.coe_range, Set.mem_Iio]
  constructor
  · intro h i hi
    rw [dif_pos hi]
    have := h ⟨i, hi⟩
    show Y i ∈ ({y ⟨i, hi⟩} : Set F2)
    rw [Set.mem_singleton_iff]
    exact this
  · intro h i
    have := h i.val i.isLt
    rw [dif_pos i.isLt] at this
    have := Set.mem_singleton_iff.mp this
    exact this

/-- Mass of a `fixedPrefixCylinder` for a prefix valued in the generating
set: `(1/4)^n`. -/
private lemma step_measure_fixedPrefixCylinder (n : ℕ) (y : Fin n → F2)
    (hy : ∀ i : Fin n, y i ∈ F2_generating_set) :
    step_measure (fixedPrefixCylinder n y) = (1/4 : ℝ≥0∞)^n := by
  rw [fixedPrefixCylinder_eq]
  exact step_measure_fin_prefix_cylinder n y hy

/-- The fixed-prefix cylinder is measurable. -/
private lemma measurableSet_fixedPrefixCylinder (n : ℕ) (y : Fin n → F2) :
    MeasurableSet (fixedPrefixCylinder n y) := by
  rw [fixedPrefixCylinder_eq]
  refine MeasurableSet.pi (Finset.range n).countable_toSet (fun i _ => ?_)
  by_cases hi : i < n
  · rw [dif_pos hi]
    exact MeasurableSet.of_discrete
  · rw [dif_neg hi]; exact MeasurableSet.univ

/-- Distinct prefixes give disjoint fixed-prefix cylinders. -/
private lemma fixedPrefixCylinder_pairwise_disjoint (n : ℕ)
    (Y_set : Finset (Fin n → F2)) :
    (↑Y_set : Set (Fin n → F2)).PairwiseDisjoint (fixedPrefixCylinder n) := by
  intro y _ y' _ hyy'
  show Disjoint (fixedPrefixCylinder n y) (fixedPrefixCylinder n y')
  rw [Set.disjoint_iff_forall_ne]
  rintro Y hY Z hZ rfl
  apply hyy'
  funext i
  simp only [fixedPrefixCylinder, Set.mem_setOf_eq] at hY hZ
  rw [← hY i, hZ i]

/-- A.s. on `step_measure`, every step `Y n` lies in the 4-element
generating set. Used in the Wave 23C transfer (a.s. equality of
`away_indicator` to its `if`-form representative).

Wave 27: promoted from `private` to public so that `ExitMeasure.lean`
can use it as the source for the `Y n ∈ F2_generating_set` hypothesis
in the dissolved `walk_converges_of_dist_tendsto_atTop` theorem.

Wave 33: moved up before `iIndepFun_iIdentDistrib_uniformIndic_pastDep`
since the generic-pattern-event a.s.-equality also needs it. -/
lemma walk_step_in_generating_set_ae :
    ∀ᵐ Y ∂step_measure, ∀ n : ℕ, Y n ∈ F2_generating_set := by
  rw [ae_all_iff]
  intro n
  have hmap : step_measure.map (fun Y : ℕ → F2 => Y n) = Z_uniform := by
    unfold step_measure
    exact (measurePreserving_eval_infinitePi
      (μ := fun _ : ℕ => Z_uniform) n).map_eq
  have hmeas : Measurable (fun Y : ℕ → F2 => Y n) := measurable_pi_apply n
  have hA : genA ∈ F2_generating_set := by left; rfl
  have hB : genB ∈ F2_generating_set := by right; left; rfl
  have hAinv : (genA⁻¹ : F2) ∈ F2_generating_set := by right; right; left; rfl
  have hBinv : (genB⁻¹ : F2) ∈ F2_generating_set := by right; right; right; rfl
  have key : ∀ᵐ z ∂Z_uniform, z ∈ F2_generating_set := by
    rw [ae_iff]
    have hApp :
        Z_uniform {a | a ∉ F2_generating_set} =
          (1/4 : ℝ≥0∞) *
            (Measure.dirac genA {a | a ∉ F2_generating_set} +
             Measure.dirac genB {a | a ∉ F2_generating_set} +
             Measure.dirac (genA⁻¹ : F2) {a | a ∉ F2_generating_set} +
             Measure.dirac (genB⁻¹ : F2) {a | a ∉ F2_generating_set}) := by
      unfold Z_uniform
      rw [Measure.smul_apply, Measure.add_apply, Measure.add_apply,
        Measure.add_apply]
      rfl
    rw [hApp]
    have d1 : Measure.dirac genA {a | a ∉ F2_generating_set} = 0 := by
      rw [Measure.dirac_apply]
      exact Set.indicator_of_notMem (by simpa using hA) _
    have d2 : Measure.dirac genB {a | a ∉ F2_generating_set} = 0 := by
      rw [Measure.dirac_apply]
      exact Set.indicator_of_notMem (by simpa using hB) _
    have d3 : Measure.dirac (genA⁻¹ : F2) {a | a ∉ F2_generating_set} = 0 := by
      rw [Measure.dirac_apply]
      exact Set.indicator_of_notMem (by simpa using hAinv) _
    have d4 : Measure.dirac (genB⁻¹ : F2) {a | a ∉ F2_generating_set} = 0 := by
      rw [Measure.dirac_apply]
      exact Set.indicator_of_notMem (by simpa using hBinv) _
    rw [d1, d2, d3, d4]
    simp
  have step : ∀ᵐ z ∂(step_measure.map (fun Y : ℕ → F2 => Y n)),
      z ∈ F2_generating_set := by rw [hmap]; exact key
  exact (ae_map_iff hmeas.aemeasurable (MeasurableSet.of_discrete)).mp step

/-! ### Wave 33 — generic prefix-counting and pattern-event measure

We build a parametric version of the Wave 28 chain. Fix
`A : ℕ → (ℕ → F2) → Finset F2` satisfying the three hypotheses of
`iIndepFun_iIdentDistrib_uniformIndic_pastDep` (past-measurability,
constant cardinality `c`, subset of generating set). For each `n` and
each pattern `S ⊆ Finset.range n`, we count prefixes `y : Fin n → F2`
realising the pattern (i.e. `y i ∈ A i.val (extendPrefix n y) ↔ i.val ∈ S`)
and conclude `step_measure(gen_patternEvent A n S) = c^|S| * (4-c)^(n-|S|) *
(1/4)^n`.

The proof is identical in structure to Wave 28's specific
`pattern_event_measure` but parametric in `A`. -/

/-- The generic extension Finset at index `n` for a prefix `y' : Fin n → F2`
and pattern `S`: either `A n (extendPrefix n y')` (`c` elts, if `n ∈ S`)
or `F2_genFinset \ A n (extendPrefix n y')` (`4 - c` elts, otherwise). -/
private noncomputable def gen_extSet (A : ℕ → (ℕ → F2) → Finset F2)
    (n : ℕ) (S : Finset ℕ) (y' : Fin n → F2) : Finset F2 :=
  if n ∈ S then A n (extendPrefix n y')
  else F2_genFinset \ A n (extendPrefix n y')

/-- `gen_extSet` cardinality is `c` (if `n ∈ S`) or `4 − c` (otherwise),
under the constant-cardinality + subset hypotheses on `A`. -/
private lemma gen_extSet_card (A : ℕ → (ℕ → F2) → Finset F2)
    (h_subset : ∀ k Y, ↑(A k Y) ⊆ F2_generating_set)
    (c : ℕ) (h_card : ∀ k Y, (A k Y).card = c)
    (n : ℕ) (S : Finset ℕ) (y' : Fin n → F2) :
    (gen_extSet A n S y').card = if n ∈ S then c else 4 - c := by
  unfold gen_extSet
  by_cases h : n ∈ S
  · rw [if_pos h, if_pos h]
    exact h_card n _
  · rw [if_neg h, if_neg h]
    have h_sub : A n (extendPrefix n y') ⊆ F2_genFinset := by
      intro z hz
      have h_set := h_subset n (extendPrefix n y') (Finset.mem_coe.mpr hz)
      rw [← F2_genFinset_coe] at h_set
      exact Finset.mem_coe.mp h_set
    rw [Finset.card_sdiff_of_subset h_sub, F2_genFinset_card, h_card n _]

/-- Elements of `gen_extSet` lie in `F2_generating_set`. -/
private lemma gen_extSet_subset_gen (A : ℕ → (ℕ → F2) → Finset F2)
    (h_subset : ∀ k Y, ↑(A k Y) ⊆ F2_generating_set)
    (n : ℕ) (S : Finset ℕ) (y' : Fin n → F2) :
    ↑(gen_extSet A n S y') ⊆ F2_generating_set := by
  unfold gen_extSet
  by_cases h : n ∈ S
  · rw [if_pos h]; exact h_subset n _
  · rw [if_neg h]
    intro z hz
    have hz' : z ∈ F2_genFinset := (Finset.mem_sdiff.mp (Finset.mem_coe.mp hz)).1
    rw [← F2_genFinset_coe]
    exact Finset.mem_coe.mpr hz'

/-- Membership in `gen_extSet`: `z ∈ gen_extSet A n S y' ↔
(z ∈ F2_genFinset) ∧ (z ∈ A n (extendPrefix n y') ↔ n ∈ S)`. -/
private lemma gen_mem_extSet (A : ℕ → (ℕ → F2) → Finset F2)
    (h_subset : ∀ k Y, ↑(A k Y) ⊆ F2_generating_set)
    (n : ℕ) (S : Finset ℕ) (y' : Fin n → F2) (z : F2) :
    z ∈ gen_extSet A n S y' ↔
      z ∈ F2_genFinset ∧
      (z ∈ A n (extendPrefix n y') ↔ n ∈ S) := by
  unfold gen_extSet
  by_cases h : n ∈ S
  · rw [if_pos h]
    simp only [h, iff_true]
    constructor
    · intro hz
      refine ⟨?_, hz⟩
      have h_set := h_subset n (extendPrefix n y') (Finset.mem_coe.mpr hz)
      rw [← F2_genFinset_coe] at h_set
      exact Finset.mem_coe.mp h_set
    · rintro ⟨_, hz⟩; exact hz
  · rw [if_neg h]
    simp only [h, iff_false]
    rw [Finset.mem_sdiff]

/-- The "extend" Finset: prefixes `y : Fin (n+1) → F2` formed as
`extOne n y' z` for `z ∈ gen_extSet`. -/
private noncomputable def gen_extPrefixes (A : ℕ → (ℕ → F2) → Finset F2)
    (n : ℕ) (S : Finset ℕ) (y' : Fin n → F2) : Finset (Fin (n + 1) → F2) :=
  (gen_extSet A n S y').image (extOne n y')

/-- Cardinality of `gen_extPrefixes`. -/
private lemma gen_extPrefixes_card (A : ℕ → (ℕ → F2) → Finset F2)
    (h_subset : ∀ k Y, ↑(A k Y) ⊆ F2_generating_set)
    (c : ℕ) (h_card : ∀ k Y, (A k Y).card = c)
    (n : ℕ) (S : Finset ℕ) (y' : Fin n → F2) :
    (gen_extPrefixes A n S y').card = if n ∈ S then c else 4 - c := by
  unfold gen_extPrefixes
  have h_inj : Function.Injective (extOne n y') := by
    intro z₁ z₂ h
    exact (extOne_inj n h).2
  rw [Finset.card_image_of_injective (gen_extSet A n S y') h_inj]
  exact gen_extSet_card A h_subset c h_card n S y'

/-- The image-Finset for `extOne y' · ` is disjoint across distinct `y'`s. -/
private lemma gen_extPrefixes_pairwise_disjoint (A : ℕ → (ℕ → F2) → Finset F2)
    (n : ℕ) (S : Finset ℕ) (P : Finset (Fin n → F2)) :
    (↑P : Set (Fin n → F2)).PairwiseDisjoint (gen_extPrefixes A n S) := by
  intro y₁ _ y₂ _ hy
  show Disjoint (gen_extPrefixes A n S y₁) (gen_extPrefixes A n S y₂)
  rw [Finset.disjoint_iff_ne]
  rintro a ha b hb rfl
  apply hy
  unfold gen_extPrefixes at ha hb
  rcases Finset.mem_image.mp ha with ⟨z₁, _, rfl⟩
  rcases Finset.mem_image.mp hb with ⟨z₂, _, h⟩
  exact ((extOne_inj n h).1).symm

/-- The Finset of prefixes `y : Fin n → F2`, valued in `F2_generating_set`,
realising the pattern `S` at all positions `< n` against the past-dependent
target `A`. -/
private noncomputable def gen_realisingPrefixes (A : ℕ → (ℕ → F2) → Finset F2)
    (n : ℕ) (S : Finset ℕ) : Finset (Fin n → F2) := by
  classical
  exact (Fintype.piFinset (fun _ : Fin n => F2_genFinset)).filter
    (fun y =>
      ∀ i : Fin n,
        (y i ∈ A i.val (extendPrefix n y)) ↔ i.val ∈ S)

/-- A prefix lies in `gen_realisingPrefixes A n S` iff it has all coordinates
in the generating set and matches the pattern `S` on the first `n` indices. -/
private lemma gen_mem_realisingPrefixes (A : ℕ → (ℕ → F2) → Finset F2)
    (n : ℕ) (S : Finset ℕ) (y : Fin n → F2) :
    y ∈ gen_realisingPrefixes A n S ↔
      (∀ i : Fin n, y i ∈ F2_generating_set) ∧
      (∀ i : Fin n,
         y i ∈ A i.val (extendPrefix n y) ↔ i.val ∈ S) := by
  classical
  unfold gen_realisingPrefixes
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨h_pi, h_pat⟩
    refine ⟨fun i => ?_, h_pat⟩
    have := h_pi i
    rw [← F2_genFinset_coe]; exact Finset.mem_coe.mpr this
  · rintro ⟨h_gen, h_pat⟩
    refine ⟨fun i => ?_, h_pat⟩
    have := h_gen i
    rw [← F2_genFinset_coe] at this
    exact Finset.mem_coe.mp this

/-- The `(n+1)`-realising prefixes decompose as the disjoint union of
extensions of `n`-realising prefixes (for the pattern `S.erase n`). -/
private lemma gen_realisingPrefixes_succ (A : ℕ → (ℕ → F2) → Finset F2)
    (h_past : ∀ k Y Y', (∀ j, j < k → Y j = Y' j) → A k Y = A k Y')
    (h_subset : ∀ k Y, ↑(A k Y) ⊆ F2_generating_set)
    (n : ℕ) (S : Finset ℕ) :
    gen_realisingPrefixes A (n + 1) S =
      (gen_realisingPrefixes A n (S.erase n)).biUnion
        (fun y' => gen_extPrefixes A n S y') := by
  classical
  ext y
  rw [Finset.mem_biUnion]
  constructor
  · intro hy
    rw [gen_mem_realisingPrefixes] at hy
    obtain ⟨h_gen, h_pat⟩ := hy
    set y' : Fin n → F2 := fun i => y i.castSucc with hy'_def
    set z : F2 := y (Fin.last n) with hz_def
    have hy_eq : y = extOne n y' z := by
      funext i
      by_cases hi : i.val < n
      · rw [extOne_apply_lt n y' z i hi]
        rw [hy'_def]
        congr 1
      · have hi_eq_val : i.val = n := by
          have := i.isLt; omega
        have h_last : i = Fin.last n := by ext; exact hi_eq_val
        rw [h_last, extOne_apply_last n y' z]
    refine ⟨y', ?_, ?_⟩
    · rw [gen_mem_realisingPrefixes]
      refine ⟨fun i => h_gen i.castSucc, fun i => ?_⟩
      have h_pat_i := h_pat i.castSucc
      have h_castSucc_val : (i.castSucc : Fin (n+1)).val = i.val := rfl
      rw [h_castSucc_val] at h_pat_i
      -- Past-measurability transfer of `A i.val`.
      have h_aw : A i.val (extendPrefix (n + 1) y)
            = A i.val (extendPrefix n y') := by
        have hi_lt : i.val < n := i.isLt
        rw [hy_eq]
        apply h_past
        intro j hj
        exact extendPrefix_extOne_init n y' z j (by omega)
      rw [h_aw] at h_pat_i
      have hy_init : y i.castSucc = y' i := rfl
      rw [hy_init] at h_pat_i
      have hi_ne_n : i.val ≠ n := Nat.ne_of_lt i.isLt
      rw [Finset.mem_erase]
      tauto
    · unfold gen_extPrefixes
      rw [Finset.mem_image]
      refine ⟨z, ?_, hy_eq.symm⟩
      rw [gen_mem_extSet A h_subset]
      refine ⟨?_, ?_⟩
      · have := h_gen (Fin.last n)
        rw [← F2_genFinset_coe] at this
        exact Finset.mem_coe.mp this
      · have h_pat_n := h_pat (Fin.last n)
        have h_last_val : (Fin.last n : Fin (n+1)).val = n := rfl
        rw [h_last_val] at h_pat_n
        have h_y_last : y (Fin.last n) = z := rfl
        rw [h_y_last] at h_pat_n
        have h_aw : A n (extendPrefix (n + 1) y)
              = A n (extendPrefix n y') := by
          rw [hy_eq]
          apply h_past
          intro j hj
          exact extendPrefix_extOne_init n y' z j hj
        rw [h_aw] at h_pat_n
        exact h_pat_n
  · rintro ⟨y', hy', hy_ext⟩
    unfold gen_extPrefixes at hy_ext
    rcases Finset.mem_image.mp hy_ext with ⟨z, hz, rfl⟩
    rw [gen_mem_extSet A h_subset] at hz
    obtain ⟨hz_gen, hz_pat⟩ := hz
    rw [gen_mem_realisingPrefixes] at hy'
    obtain ⟨hy'_gen, hy'_pat⟩ := hy'
    rw [gen_mem_realisingPrefixes]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · by_cases hi : i.val < n
      · rw [extOne_apply_lt n y' z i hi]
        exact hy'_gen ⟨i.val, hi⟩
      · have hi_eq_val : i.val = n := by have := i.isLt; omega
        have h_last : i = Fin.last n := by ext; exact hi_eq_val
        rw [h_last, extOne_apply_last n y' z]
        rw [← F2_genFinset_coe]
        exact Finset.mem_coe.mpr hz_gen
    · by_cases hi : i.val < n
      · rw [extOne_apply_lt n y' z i hi]
        have h_aw : A i.val (extendPrefix (n + 1) (extOne n y' z))
              = A i.val (extendPrefix n y') := by
          apply h_past
          intro j hj
          exact extendPrefix_extOne_init n y' z j (by omega)
        rw [h_aw]
        have h_pat_i :
            y' ⟨i.val, hi⟩ ∈ A i.val (extendPrefix n y')
              ↔ i.val ∈ S.erase n := hy'_pat ⟨i.val, hi⟩
        have hi_ne_n : i.val ≠ n := Nat.ne_of_lt hi
        rw [Finset.mem_erase] at h_pat_i
        constructor
        · intro h; exact (h_pat_i.mp h).2
        · intro h; exact h_pat_i.mpr ⟨hi_ne_n, h⟩
      · have hi_eq_val : i.val = n := by have := i.isLt; omega
        have h_last : i = Fin.last n := by ext; exact hi_eq_val
        rw [h_last, extOne_apply_last n y' z]
        have h_last_val : (Fin.last n : Fin (n+1)).val = n := rfl
        rw [h_last_val]
        have h_aw : A n (extendPrefix (n + 1) (extOne n y' z))
              = A n (extendPrefix n y') := by
          apply h_past
          intro j hj
          exact extendPrefix_extOne_init n y' z j hj
        rw [h_aw]
        exact hz_pat

/-- **Generic prefix-counting lemma.** Cardinality of the realising-prefix
Finset is `c^|S| * (4-c)^(n - |S|)`, by induction on `n`. -/
private lemma gen_realisingPrefixes_card (A : ℕ → (ℕ → F2) → Finset F2)
    (h_past : ∀ k Y Y', (∀ j, j < k → Y j = Y' j) → A k Y = A k Y')
    (h_subset : ∀ k Y, ↑(A k Y) ⊆ F2_generating_set)
    (c : ℕ) (h_card : ∀ k Y, (A k Y).card = c) :
    ∀ (n : ℕ) (S : Finset ℕ), S ⊆ Finset.range n →
      (gen_realisingPrefixes A n S).card = c ^ S.card * (4 - c) ^ (n - S.card) := by
  classical
  intro n
  induction n with
  | zero =>
    intro S hS
    have hS_empty : S = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      have := hS hx
      simp at this
    rw [hS_empty, Finset.card_empty, pow_zero, Nat.zero_sub, pow_zero, one_mul]
    have h_singleton :
        gen_realisingPrefixes A 0 ∅ = {(fun i : Fin 0 => i.elim0)} := by
      ext y
      rw [gen_mem_realisingPrefixes, Finset.mem_singleton]
      constructor
      · intro _; funext i; exact i.elim0
      · intro _; exact ⟨fun i => i.elim0, fun i => i.elim0⟩
    rw [h_singleton, Finset.card_singleton]
  | succ n ih =>
    intro S hS
    have hS'_sub : S.erase n ⊆ Finset.range n := by
      intro i hi
      have hi_in : i ∈ S := Finset.mem_of_mem_erase hi
      have hi_ne : i ≠ n := Finset.ne_of_mem_erase hi
      have hi_lt : i < n + 1 := Finset.mem_range.mp (hS hi_in)
      exact Finset.mem_range.mpr (by omega)
    have h_ih := ih (S.erase n) hS'_sub
    rw [gen_realisingPrefixes_succ A h_past h_subset n S]
    rw [Finset.card_biUnion (gen_extPrefixes_pairwise_disjoint A n S _)]
    rw [Finset.sum_congr rfl
      (fun y' _ => gen_extPrefixes_card A h_subset c h_card n S y')]
    rw [Finset.sum_const]
    rw [h_ih]
    rw [smul_eq_mul]
    by_cases hn : n ∈ S
    · rw [if_pos hn]
      have h_card_eq : S.card = (S.erase n).card + 1 := by
        rw [Finset.card_erase_of_mem hn]
        have h_card_pos : S.card ≥ 1 := Finset.card_pos.mpr ⟨n, hn⟩
        omega
      have h_le : (S.erase n).card ≤ n := by
        have : S.erase n ⊆ Finset.range n := hS'_sub
        have := Finset.card_le_card this
        rwa [Finset.card_range] at this
      have h_diff_orig : n + 1 - S.card = n - (S.erase n).card := by
        rw [h_card_eq]; omega
      rw [h_diff_orig, h_card_eq, pow_succ]
      ring
    · rw [if_neg hn]
      rw [show S.erase n = S from Finset.erase_eq_of_notMem hn]
      have h_le : S.card ≤ n := by
        have hS_n : S ⊆ Finset.range n := by
          intro i hi
          have hi_lt : i < n + 1 := Finset.mem_range.mp (hS hi)
          have hi_ne : i ≠ n := fun h => hn (h ▸ hi)
          exact Finset.mem_range.mpr (by omega)
        have := Finset.card_le_card hS_n
        rwa [Finset.card_range] at this
      have h_diff_succ : n + 1 - S.card = (n - S.card) + 1 := by omega
      rw [h_diff_succ, pow_succ]
      ring

/-- **Generic pattern event.** The set of full sample paths `Y : ℕ → F2`
realising the pattern `S` against `A` on the first `n` indices. -/
private def gen_patternEvent (A : ℕ → (ℕ → F2) → Finset F2) (n : ℕ)
    (S : Finset ℕ) : Set (ℕ → F2) :=
  {Y | ∀ i, i < n → (Y i ∈ A i Y ↔ i ∈ S)}

/-- `Y` lies in `gen_patternEvent A n S` (and has all coords in
`F2_generating_set` for `i < n`) iff its truncated prefix is realising. -/
private lemma gen_patternEvent_iff_prefix (A : ℕ → (ℕ → F2) → Finset F2)
    (h_past : ∀ k Y Y', (∀ j, j < k → Y j = Y' j) → A k Y = A k Y')
    (n : ℕ) (S : Finset ℕ) (Y : ℕ → F2)
    (hY_gen : ∀ i, i < n → Y i ∈ F2_generating_set) :
    Y ∈ gen_patternEvent A n S ↔
      (fun i : Fin n => Y i.val) ∈ gen_realisingPrefixes A n S := by
  classical
  unfold gen_patternEvent
  rw [gen_mem_realisingPrefixes]
  constructor
  · intro h_pat
    refine ⟨fun i => hY_gen i.val i.isLt, fun i => ?_⟩
    have h := h_pat i.val i.isLt
    have hext : ∀ j, j < i.val → Y j =
                  extendPrefix n (fun j : Fin n => Y j.val) j := by
      intro j hj
      have hj_lt : j < n := lt_trans hj i.isLt
      rw [extendPrefix_apply_lt n _ j hj_lt]
    have h_aw : A i.val Y =
        A i.val (extendPrefix n (fun j : Fin n => Y j.val)) :=
      h_past i.val Y _ hext
    rw [h_aw] at h
    exact h
  · rintro ⟨h_gen, h_pat⟩ i hi
    have h := h_pat ⟨i, hi⟩
    have hext : ∀ j, j < i → Y j =
                  extendPrefix n (fun j : Fin n => Y j.val) j := by
      intro j hj
      have hj_lt : j < n := lt_trans hj hi
      rw [extendPrefix_apply_lt n _ j hj_lt]
    have h_aw : A i Y =
        A i (extendPrefix n (fun j : Fin n => Y j.val)) :=
      h_past i Y _ hext
    rw [h_aw]
    exact h

/-- A.s. on `step_measure`, the `gen_patternEvent` equals the `biUnion` of
fixed-prefix cylinders over realising prefixes. -/
private lemma gen_patternEvent_aeEq_biUnion (A : ℕ → (ℕ → F2) → Finset F2)
    (h_past : ∀ k Y Y', (∀ j, j < k → Y j = Y' j) → A k Y = A k Y')
    (n : ℕ) (S : Finset ℕ) :
    gen_patternEvent A n S
      =ᵐ[step_measure]
      ⋃ y ∈ gen_realisingPrefixes A n S, fixedPrefixCylinder n y := by
  filter_upwards [walk_step_in_generating_set_ae] with Y hY
  classical
  apply propext
  have hY_gen : ∀ i, i < n → Y i ∈ F2_generating_set := fun i _ => hY i
  have h_iff := gen_patternEvent_iff_prefix A h_past n S Y hY_gen
  set y0 : Fin n → F2 := fun i => Y i.val with hy0_def
  change Y ∈ gen_patternEvent A n S ↔ Y ∈ ⋃ y ∈ gen_realisingPrefixes A n S, fixedPrefixCylinder n y
  rw [Set.mem_iUnion]
  rw [h_iff]
  constructor
  · intro h_real
    refine ⟨y0, ?_⟩
    rw [Set.mem_iUnion]
    refine ⟨h_real, ?_⟩
    intro i
    show Y i.val = y0 i
    rfl
  · rintro ⟨y, hy⟩
    rw [Set.mem_iUnion] at hy
    obtain ⟨hy_real, hy_match⟩ := hy
    have hyy : y = y0 := by
      funext i
      have := hy_match i
      simp [hy0_def, this.symm]
    rw [hyy] at hy_real
    exact hy_real

/-- **Generic pattern-event measure (Wave 33 keystone).** The mass of the
generic pattern event under `step_measure` is `c^|S| * (4-c)^(n-|S|) *
(1/4)^n`. -/
private lemma gen_pattern_event_measure (A : ℕ → (ℕ → F2) → Finset F2)
    (h_past : ∀ k Y Y', (∀ j, j < k → Y j = Y' j) → A k Y = A k Y')
    (h_subset : ∀ k Y, ↑(A k Y) ⊆ F2_generating_set)
    (c : ℕ) (h_card : ∀ k Y, (A k Y).card = c)
    (n : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range n) :
    step_measure (gen_patternEvent A n S)
      = (c : ℝ≥0∞)^S.card * ((4 - c : ℕ) : ℝ≥0∞)^(n - S.card) *
          (1/4 : ℝ≥0∞)^n := by
  classical
  rw [measure_congr (gen_patternEvent_aeEq_biUnion A h_past n S)]
  rw [measure_biUnion_finset
    (s := gen_realisingPrefixes A n S) (f := fixedPrefixCylinder n)
    (fixedPrefixCylinder_pairwise_disjoint n (gen_realisingPrefixes A n S))
    (fun y _ => measurableSet_fixedPrefixCylinder n y)]
  have h_const : ∀ y ∈ gen_realisingPrefixes A n S,
      step_measure (fixedPrefixCylinder n y) = (1/4 : ℝ≥0∞)^n := by
    intro y hy
    have hy_gen : ∀ i : Fin n, y i ∈ F2_generating_set :=
      ((gen_mem_realisingPrefixes A n S y).mp hy).1
    exact step_measure_fixedPrefixCylinder n y hy_gen
  rw [Finset.sum_congr rfl h_const]
  rw [Finset.sum_const]
  rw [gen_realisingPrefixes_card A h_past h_subset c h_card n S hS]
  rw [nsmul_eq_mul]
  push_cast
  ring

/-! ### Wave 33 — the i.i.d. theorem (formerly axiom)

We now derive the three conclusions from `gen_pattern_event_measure`:
1. Marginal mean `∫ f 0 = c/4`,
2. Identical distribution of `f k` and `f 0`,
3. Mutual independence of the family `(f k)`. -/

/-- Distinct patterns (subsets of `Finset.range n`) give disjoint
generic pattern events. -/
private lemma gen_patternEvent_pairwise_disjoint
    (A : ℕ → (ℕ → F2) → Finset F2) (n : ℕ)
    (S_set : Finset (Finset ℕ))
    (hS_set : ∀ S ∈ S_set, S ⊆ Finset.range n) :
    (↑S_set : Set (Finset ℕ)).PairwiseDisjoint (gen_patternEvent A n) := by
  classical
  intro S hS S' hS' hSS'
  show Disjoint (gen_patternEvent A n S) (gen_patternEvent A n S')
  rw [Set.disjoint_iff_forall_ne]
  rintro Y hY Z hZ rfl
  apply hSS'
  ext i
  by_cases hi : i ∈ Finset.range n
  · have hi_lt : i < n := Finset.mem_range.mp hi
    have h1 := hY i hi_lt
    have h2 := hZ i hi_lt
    constructor
    · intro hin; exact h2.mp (h1.mpr hin)
    · intro hin; exact h1.mp (h2.mpr hin)
  · have hi_S : i ∉ S := fun h => hi (hS_set S (Finset.mem_coe.mp hS) h)
    have hi_S' : i ∉ S' := fun h => hi (hS_set S' (Finset.mem_coe.mp hS') h)
    exact ⟨fun h => absurd h hi_S, fun h => absurd h hi_S'⟩

/-- Pointwise (no a.s. needed): the marginal event `{Y | Y k ∈ A k Y}`
is the disjoint union over patterns `S ⊆ Finset.range (k+1)` containing
`k` of `gen_patternEvent A (k+1) S`. -/
private lemma gen_marginal_event_eq_biUnion
    (A : ℕ → (ℕ → F2) → Finset F2) (k : ℕ) :
    {Y : ℕ → F2 | Y k ∈ A k Y}
      = ⋃ S ∈ ((Finset.range (k + 1)).powerset.filter (fun S => k ∈ S)),
          gen_patternEvent A (k + 1) S := by
  classical
  ext Y
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  constructor
  · intro hYk
    set S : Finset ℕ :=
      (Finset.range (k + 1)).filter (fun i => Y i ∈ A i Y) with hS_def
    have hS_sub : S ⊆ Finset.range (k + 1) := Finset.filter_subset _ _
    have hk_mem_S : k ∈ S := by
      rw [hS_def, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_self k, hYk⟩
    refine ⟨S, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hS_sub, hk_mem_S⟩
    · intro i hi
      rw [hS_def, Finset.mem_filter, Finset.mem_range]
      exact ⟨fun h => ⟨hi, h⟩, fun ⟨_, h⟩ => h⟩
  · rintro ⟨S, hS_mem, hY_pat⟩
    rw [Finset.mem_filter] at hS_mem
    obtain ⟨_, hk_S⟩ := hS_mem
    exact (hY_pat k (Nat.lt_succ_self k)).mpr hk_S

/-- Algebra rearrangement: `∑_{S' ⊆ Finset.range k} c^|S'| * (4-c)^(k - |S'|) = 4^k`,
when `c ≤ 4`. (Binomial expansion of `(c + (4-c))^k = 4^k`.) -/
private lemma binom_sum_c_4mc (c k : ℕ) (hc : c ≤ 4) :
    ∑ S' ∈ (Finset.range k).powerset, c ^ S'.card * (4 - c) ^ (k - S'.card)
      = 4 ^ k := by
  classical
  -- Group powerset by cardinality.
  have h_powerset_eq :
      (Finset.range k).powerset
        = (Finset.range (k + 1)).biUnion
            (fun j => (Finset.range k).powersetCard j) := by
    ext S'
    rw [Finset.mem_powerset, Finset.mem_biUnion]
    constructor
    · intro hS'
      refine ⟨S'.card, ?_, ?_⟩
      · rw [Finset.mem_range]
        have := Finset.card_le_card hS'
        rw [Finset.card_range] at this; omega
      · exact Finset.mem_powersetCard.mpr ⟨hS', rfl⟩
    · rintro ⟨j, _, hS'⟩
      exact (Finset.mem_powersetCard.mp hS').1
  rw [h_powerset_eq]
  rw [Finset.sum_biUnion]
  · -- Inner sum is constant on powersetCard j.
    have h_inner : ∀ j ∈ Finset.range (k + 1),
        ∑ S' ∈ (Finset.range k).powersetCard j,
            c ^ S'.card * (4 - c) ^ (k - S'.card)
          = Nat.choose k j * (c ^ j * (4 - c) ^ (k - j)) := by
      intro j _
      rw [Finset.sum_congr rfl (fun S' hS' => by
        rw [(Finset.mem_powersetCard.mp hS').2])]
      rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_range,
          smul_eq_mul]
    rw [Finset.sum_congr rfl h_inner]
    -- Now reduce to (c + (4 - c))^k = 4^k.
    have h_add_pow : (c + (4 - c)) ^ k =
        ∑ j ∈ Finset.range (k + 1), c ^ j * (4 - c) ^ (k - j) * Nat.choose k j :=
      add_pow c (4 - c) k
    have hadd : c + (4 - c) = 4 := by omega
    rw [hadd] at h_add_pow
    rw [h_add_pow]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  · -- Pairwise disjoint cardinality classes.
    intro j _ j' _ hjj'
    intro x hxj hxj'
    intro a ha
    have h1 := (Finset.mem_powersetCard.mp (hxj ha)).2
    have h2 := (Finset.mem_powersetCard.mp (hxj' ha)).2
    exact absurd (h1.symm.trans h2) hjj'

/-- The marginal event `{Y | Y k ∈ A k Y}` has `step_measure`-mass `c/4`,
under the constant-cardinality past-measurable hypothesis on `A`. -/
private lemma step_measure_marginal_event
    (A : ℕ → (ℕ → F2) → Finset F2)
    (h_past : ∀ k Y Y', (∀ j, j < k → Y j = Y' j) → A k Y = A k Y')
    (h_subset : ∀ k Y, ↑(A k Y) ⊆ F2_generating_set)
    (c : ℕ) (h_card : ∀ k Y, (A k Y).card = c) (k : ℕ) :
    step_measure {Y : ℕ → F2 | Y k ∈ A k Y} = (c : ℝ≥0∞) / 4 := by
  classical
  -- Bound c ≤ 4 from h_card and h_subset.
  have hc_le_4 : c ≤ 4 := by
    have h_sub : A k (fun _ => (1 : F2)) ⊆ F2_genFinset := by
      intro z hz
      have h_set := h_subset k (fun _ => (1 : F2)) (Finset.mem_coe.mpr hz)
      rw [← F2_genFinset_coe] at h_set
      exact Finset.mem_coe.mp h_set
    have hcard_eq : (A k (fun _ => (1 : F2))).card = c := h_card k _
    have := Finset.card_le_card h_sub
    rw [F2_genFinset_card] at this
    omega
  rw [gen_marginal_event_eq_biUnion A k]
  -- Disjoint union over patterns containing k.
  have hdisj : (((Finset.range (k + 1)).powerset.filter (fun S => k ∈ S)) :
                 Set (Finset ℕ)).PairwiseDisjoint (gen_patternEvent A (k + 1)) := by
    intro S hS S' hS' hSS'
    show Disjoint (gen_patternEvent A (k + 1) S) (gen_patternEvent A (k + 1) S')
    rcases Finset.mem_filter.mp hS with ⟨hS_pow, _⟩
    rcases Finset.mem_filter.mp hS' with ⟨hS'_pow, _⟩
    exact gen_patternEvent_pairwise_disjoint A (k + 1)
      ((Finset.range (k + 1)).powerset.filter (fun S => k ∈ S))
      (fun T hT => Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1)
      hS hS' hSS'
  rw [measure_biUnion_finset₀
    (s := (Finset.range (k + 1)).powerset.filter (fun S => k ∈ S))
    (f := gen_patternEvent A (k + 1))
    hdisj.aedisjoint
    (fun S hS => by
      rcases Finset.mem_filter.mp hS with ⟨hS_pow, _⟩
      have hS_sub : S ⊆ Finset.range (k + 1) := Finset.mem_powerset.mp hS_pow
      -- gen_patternEvent A (k+1) S is a.s. equal to a biUnion of cylinders.
      have h_meas : MeasurableSet
          (⋃ y ∈ gen_realisingPrefixes A (k + 1) S, fixedPrefixCylinder (k + 1) y) := by
        apply MeasurableSet.biUnion (Finset.countable_toSet _)
        intro y _
        exact measurableSet_fixedPrefixCylinder (k + 1) y
      exact h_meas.nullMeasurableSet.congr
        (gen_patternEvent_aeEq_biUnion A h_past (k + 1) S).symm)]
  -- Compute each summand.
  have h_const : ∀ S ∈ (Finset.range (k + 1)).powerset.filter (fun S => k ∈ S),
      step_measure (gen_patternEvent A (k + 1) S)
        = (c : ℝ≥0∞)^S.card * ((4 - c : ℕ) : ℝ≥0∞)^(k + 1 - S.card) *
            (1/4 : ℝ≥0∞)^(k + 1) := by
    intro S hS
    rcases Finset.mem_filter.mp hS with ⟨hS_pow, _⟩
    have hS_sub : S ⊆ Finset.range (k + 1) := Finset.mem_powerset.mp hS_pow
    exact gen_pattern_event_measure A h_past h_subset c h_card (k + 1) S hS_sub
  rw [Finset.sum_congr rfl h_const]
  -- Reindex via S = S' ∪ {k} for S' ⊆ Finset.range k.
  have h_bij :
      (Finset.range (k + 1)).powerset.filter (fun S => k ∈ S)
        = (Finset.range k).powerset.image (fun S' => S' ∪ {k}) := by
    ext S
    rw [Finset.mem_filter, Finset.mem_image]
    rw [Finset.mem_powerset]
    constructor
    · rintro ⟨hS_sub, hk_S⟩
      refine ⟨S.erase k, ?_, ?_⟩
      · rw [Finset.mem_powerset]
        intro i hi
        have hi_in : i ∈ S := Finset.mem_of_mem_erase hi
        have hi_ne : i ≠ k := Finset.ne_of_mem_erase hi
        have hi_lt : i < k + 1 := Finset.mem_range.mp (hS_sub hi_in)
        exact Finset.mem_range.mpr (by omega)
      · rw [Finset.union_comm]
        exact Finset.insert_erase hk_S
    · rintro ⟨S', hS'_pow, rfl⟩
      rw [Finset.mem_powerset] at hS'_pow
      have hS_sub : S' ∪ {k} ⊆ Finset.range (k + 1) := by
        intro i hi
        rcases Finset.mem_union.mp hi with hi' | hi'
        · have := hS'_pow hi'
          rw [Finset.mem_range] at this ⊢
          omega
        · rw [Finset.mem_singleton] at hi'
          rw [hi', Finset.mem_range]
          exact Nat.lt_succ_self k
      have hk_in : k ∈ S' ∪ {k} := Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl)
      exact ⟨hS_sub, hk_in⟩
  rw [h_bij]
  rw [Finset.sum_image]
  · -- Now the sum is indexed by S' ⊆ Finset.range k. Compute |S' ∪ {k}|.
    have h_simplify : ∀ S' ∈ (Finset.range k).powerset,
        (c : ℝ≥0∞) ^ (S' ∪ {k}).card *
          ((4 - c : ℕ) : ℝ≥0∞) ^ (k + 1 - (S' ∪ {k}).card) *
          (1/4 : ℝ≥0∞) ^ (k + 1)
          = (c : ℝ≥0∞) * (1/4 : ℝ≥0∞) ^ (k + 1) *
              ((c : ℝ≥0∞) ^ S'.card *
                ((4 - c : ℕ) : ℝ≥0∞) ^ (k - S'.card)) := by
      intro S' hS'
      rw [Finset.mem_powerset] at hS'
      have hk_notin : k ∉ S' := by
        intro h
        have := hS' h
        rw [Finset.mem_range] at this
        omega
      have h_card_union : (S' ∪ {k}).card = S'.card + 1 := by
        rw [Finset.union_comm, ← Finset.insert_eq, Finset.card_insert_of_notMem hk_notin]
      have h_le : S'.card ≤ k := by
        have := Finset.card_le_card hS'
        rwa [Finset.card_range] at this
      rw [h_card_union]
      have h_diff : k + 1 - (S'.card + 1) = k - S'.card := by omega
      rw [h_diff, pow_succ]
      ring
    rw [Finset.sum_congr rfl h_simplify]
    -- Factor out the constant prefactor c * (1/4)^(k+1).
    rw [← Finset.mul_sum]
    -- Apply binom_sum_c_4mc.
    have h_binom_nat : ∑ S' ∈ (Finset.range k).powerset,
          c ^ S'.card * (4 - c) ^ (k - S'.card) = 4 ^ k := binom_sum_c_4mc c k hc_le_4
    -- Cast to ℝ≥0∞.
    have h_binom : ∑ S' ∈ (Finset.range k).powerset,
          (c : ℝ≥0∞) ^ S'.card * ((4 - c : ℕ) : ℝ≥0∞) ^ (k - S'.card)
          = (4 : ℝ≥0∞) ^ k := by
      have h_cast := congr_arg (fun n : ℕ => (n : ℝ≥0∞)) h_binom_nat
      simp only at h_cast
      rw [Nat.cast_sum] at h_cast
      have h_lhs_eq : ∑ S' ∈ (Finset.range k).powerset,
          ((c ^ S'.card * (4 - c) ^ (k - S'.card) : ℕ) : ℝ≥0∞)
          = ∑ S' ∈ (Finset.range k).powerset,
              (c : ℝ≥0∞) ^ S'.card * ((4 - c : ℕ) : ℝ≥0∞) ^ (k - S'.card) := by
        refine Finset.sum_congr rfl (fun S' _ => ?_)
        push_cast; ring
      rw [h_lhs_eq] at h_cast
      have h_rhs_eq : ((4 ^ k : ℕ) : ℝ≥0∞) = (4 : ℝ≥0∞) ^ k := by push_cast; ring
      rw [h_rhs_eq] at h_cast
      exact h_cast
    rw [h_binom]
    -- Final: c * (1/4)^(k+1) * 4^k = c/4
    have h_pow_succ : ((1 : ℝ≥0∞) / 4) ^ (k + 1)
            = ((1 : ℝ≥0∞) / 4) * (1 / 4) ^ k := by
      rw [pow_succ]; ring
    rw [h_pow_succ]
    have h_inv_pow : ((1 : ℝ≥0∞) / 4) ^ k * (4 : ℝ≥0∞) ^ k = 1 := by
      rw [← mul_pow]
      have h_one : ((1 : ℝ≥0∞) / 4) * 4 = 1 := by
        rw [one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
      rw [h_one, one_pow]
    rw [show ((c : ℝ≥0∞) * (((1 : ℝ≥0∞)/4) * (1/4 : ℝ≥0∞)^k)) * (4 : ℝ≥0∞)^k
            = (c : ℝ≥0∞) * ((1/4 : ℝ≥0∞) * ((1/4 : ℝ≥0∞)^k * (4 : ℝ≥0∞)^k)) from by ring]
    rw [h_inv_pow, mul_one]
    rw [mul_div_assoc', mul_one]
  · -- Image is injective.
    intro S' hS' S'' hS'' h_eq
    have hS'_sub : S' ⊆ Finset.range k := by
      have := hS'
      simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff] at this
      intro i hi
      exact Finset.mem_coe.mp (this (Finset.mem_coe.mpr hi))
    have hS''_sub : S'' ⊆ Finset.range k := by
      have := hS''
      simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff] at this
      intro i hi
      exact Finset.mem_coe.mp (this (Finset.mem_coe.mpr hi))
    have hk_notin_S' : k ∉ S' := fun h => by
      have := hS'_sub h; rw [Finset.mem_range] at this; omega
    have hk_notin_S'' : k ∉ S'' := fun h => by
      have := hS''_sub h; rw [Finset.mem_range] at this; omega
    -- S' ∪ {k} = S'' ∪ {k} and k ∉ S', k ∉ S'' ⇒ S' = S''.
    ext i
    have h_i := congr_arg (fun X => i ∈ X) h_eq
    simp only [Finset.mem_union, Finset.mem_singleton] at h_i
    by_cases hi : i = k
    · subst hi
      exact ⟨fun h => absurd h hk_notin_S', fun h => absurd h hk_notin_S''⟩
    · constructor
      · intro hin; rcases (h_i.mp (Or.inl hin)) with h | h
        · exact h
        · exact absurd h hi
      · intro hin; rcases (h_i.mpr (Or.inl hin)) with h | h
        · exact h
        · exact absurd h hi

/-- The marginal-event preimage of `f k`. -/
private lemma f_preimage_set
    (A : ℕ → (ℕ → F2) → Finset F2)
    (k : ℕ) (s : Set ℝ)
    [Decidable ((1 : ℝ) ∈ s)] [Decidable ((0 : ℝ) ∈ s)] :
    (fun Y : ℕ → F2 => if Y k ∈ A k Y then (1 : ℝ) else 0) ⁻¹' s =
      (if (1 : ℝ) ∈ s then {Y | Y k ∈ A k Y} else ∅) ∪
      (if (0 : ℝ) ∈ s then {Y : ℕ → F2 | Y k ∉ A k Y} else ∅) := by
  ext Y
  by_cases h : Y k ∈ A k Y
  · simp only [Set.mem_preimage, if_pos h, Set.mem_union, Set.mem_ite_empty_right,
      Set.mem_setOf_eq]
    constructor
    · intro h1; exact Or.inl ⟨h1, h⟩
    · rintro (⟨h1, _⟩ | ⟨_, h0⟩)
      · exact h1
      · exact absurd h h0
  · simp only [Set.mem_preimage, if_neg h, Set.mem_union, Set.mem_ite_empty_right,
      Set.mem_setOf_eq]
    constructor
    · intro h0; exact Or.inr ⟨h0, h⟩
    · rintro (⟨_, h1⟩ | ⟨h0, _⟩)
      · exact absurd h1 h
      · exact h0

/-- The set `{Y | Y k ∈ A k Y}` is measurable. By past-measurability of `A k`,
this set is the union over (prefix `y'` valued in `F2_genFinset`) and (last
letter `z ∈ A k (extendPrefix (k+1) (extOne k y' z))`) of fixed-prefix cylinders. -/
private lemma measurableSet_marginal_event
    (A : ℕ → (ℕ → F2) → Finset F2)
    (h_past : ∀ k Y Y', (∀ j, j < k → Y j = Y' j) → A k Y = A k Y')
    (k : ℕ) :
    MeasurableSet {Y : ℕ → F2 | Y k ∈ A k Y} := by
  -- Decompose by the `<k+1`-prefix `y' : Fin (k+1) → F2`. The ambient μ-null
  -- complement is `{Y | ∃ i ≤ k, Y i ∉ F2_genFinset}` (a.s. excluded by
  -- `walk_step_in_generating_set_ae`), but we want unconditional measurability.
  -- Since F2 has top σ-algebra, every fiber-condition is measurable: the set
  -- `{Y | Y k ∈ A k Y}` is the union over (y_0, ..., y_k) ∈ F2^(k+1) (countable!) of
  -- cylinders. Each cylinder is the intersection of `Y i = y_i` for i ≤ k
  -- (measurable) AND the condition `y_k ∈ A k Y`, which for fixed prefix becomes
  -- `y_k ∈ A k (some Y satisfying the prefix)`, a constant by past-measurability.
  -- Encode: ⋃_{y : Fin (k+1) → F2} (cylinder y) ∩ {Y | y k ∈ A k Y}.
  -- Since prefix-fixed Y has Y j = y j for j ≤ k, by past-measurability A k Y =
  -- A k (extendPrefix (k+1) y), so we just need y k ∈ A k (extendPrefix (k+1) y).
  -- Then if y k ∈ A k (extendPrefix (k+1) y), the cylinder is included; otherwise empty.
  rw [show {Y : ℕ → F2 | Y k ∈ A k Y}
        = ⋃ y : Fin (k+1) → F2,
            (if y ⟨k, Nat.lt_succ_self k⟩
                ∈ A k (extendPrefix (k+1) y) then
              {Y : ℕ → F2 | ∀ i : Fin (k+1), Y i.val = y i} else ∅) from by
    ext Y
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hYk
      refine ⟨(fun i : Fin (k+1) => Y i.val), ?_⟩
      -- y k ∈ A k Y by hYk; convert to y k ∈ A k (extendPrefix (k+1) y).
      have h_aw : A k Y = A k (extendPrefix (k+1) (fun i : Fin (k+1) => Y i.val)) := by
        apply h_past
        intro j hj
        have hj_lt : j < k+1 := by omega
        rw [extendPrefix_apply_lt _ _ j hj_lt]
      have hY_in : (fun i : Fin (k+1) => Y i.val) ⟨k, Nat.lt_succ_self k⟩
            ∈ A k (extendPrefix (k+1) (fun i : Fin (k+1) => Y i.val)) := by
        show Y k ∈ _
        rw [← h_aw]; exact hYk
      rw [if_pos hY_in]
      intro i; rfl
    · rintro ⟨y, hY⟩
      by_cases hcase : y ⟨k, Nat.lt_succ_self k⟩ ∈ A k (extendPrefix (k+1) y)
      · rw [if_pos hcase] at hY
        -- hY : ∀ i : Fin (k+1), Y i.val = y i.
        -- Show Y k ∈ A k Y. By hY ⟨k, lt⟩ = y ⟨k, _⟩, and A k Y = A k (extendPrefix (k+1) y) by past-meas.
        have hY_eq_y_k : Y k = y ⟨k, Nat.lt_succ_self k⟩ := hY ⟨k, Nat.lt_succ_self k⟩
        have h_aw : A k Y = A k (extendPrefix (k+1) y) := by
          apply h_past
          intro j hj
          have hj_lt : j < k+1 := by omega
          rw [extendPrefix_apply_lt _ _ j hj_lt]
          exact hY ⟨j, hj_lt⟩
        rw [h_aw, hY_eq_y_k]; exact hcase
      · rw [if_neg hcase] at hY
        exact hY.elim]
  refine MeasurableSet.iUnion (fun y => ?_)
  by_cases hcase : y ⟨k, Nat.lt_succ_self k⟩ ∈ A k (extendPrefix (k+1) y)
  · rw [if_pos hcase]
    -- {Y | ∀ i : Fin (k+1), Y i.val = y i} is a measurable cylinder.
    have h_eq : {Y : ℕ → F2 | ∀ i : Fin (k+1), Y i.val = y i}
        = fixedPrefixCylinder (k+1) y := rfl
    rw [h_eq]; exact measurableSet_fixedPrefixCylinder (k+1) y
  · rw [if_neg hcase]; exact MeasurableSet.empty

/-- Measurability of `{Y | Y k ∉ A k Y}` (complement). -/
private lemma measurableSet_marginal_event_compl
    (A : ℕ → (ℕ → F2) → Finset F2)
    (h_past : ∀ k Y Y', (∀ j, j < k → Y j = Y' j) → A k Y = A k Y')
    (k : ℕ) :
    MeasurableSet {Y : ℕ → F2 | Y k ∉ A k Y} := by
  have : {Y : ℕ → F2 | Y k ∉ A k Y} = {Y : ℕ → F2 | Y k ∈ A k Y}ᶜ := by
    ext Y; simp [Set.mem_compl_iff, Set.mem_setOf_eq]
  rw [this]
  exact (measurableSet_marginal_event A h_past k).compl

/-- `Measurable` for the indicator family. -/
private lemma f_measurable
    (A : ℕ → (ℕ → F2) → Finset F2)
    (h_past : ∀ k Y Y', (∀ j, j < k → Y j = Y' j) → A k Y = A k Y')
    (k : ℕ) :
    Measurable (fun Y : ℕ → F2 => if Y k ∈ A k Y then (1 : ℝ) else 0) := by
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_marginal_event A h_past k

/-- **Joint cylinder formula (Wave 33 keystone for independence).** For any
finite `S' : Finset ℕ` partitioned as `T_1 ⊆ S'` (the "1-pattern"), the
joint event
```
  (⋂_{i ∈ T_1} {Y | Y i ∈ A i Y}) ∩ (⋂_{i ∈ S' \ T_1} {Y | Y i ∉ A i Y})
```
has `step_measure`-mass `(c/4)^|T_1| * ((4-c)/4)^|S' \ T_1|`.

This is the joint factorisation that yields mutual independence: it shows
the Bernoulli-Indicator family factorises across any finite marginal.
The proof goes through `gen_pattern_event_measure` plus a disjoint-union
sum over fillings of indices in `Finset.range n \ S'` (with `n` chosen
large enough that `S' ⊆ Finset.range n`). The argument is the binomial
expansion `(c + (4-c))^m = 4^m` after integrating out the unconstrained
coordinates.

**Wave 33-cleanup (dissolved).** Now a fully-proven theorem. The proof
follows the structural template of `step_measure_marginal_event` (the
special case `|S'| = 1, |T_1| = 1`), generalised to arbitrary `S'`: pick
`n` with `S' ⊆ Finset.range n`, decompose the joint cylinder as a
disjoint union over admissible patterns `S ⊆ Finset.range n` with
`S ∩ S' = T_1`, apply `gen_pattern_event_measure`, then use
`binom_sum_c_4mc` to integrate out the unconstrained coordinates. -/
private theorem gen_joint_cylinder_measure
    (A : ℕ → (ℕ → F2) → Finset F2)
    (h_past : ∀ k Y Y', (∀ j, j < k → Y j = Y' j) → A k Y = A k Y')
    (h_subset : ∀ k Y, ↑(A k Y) ⊆ F2_generating_set)
    (c : ℕ) (h_card : ∀ k Y, (A k Y).card = c)
    (S' : Finset ℕ) (T_1 : Finset ℕ) (hT_1 : T_1 ⊆ S') :
    step_measure
      ((⋂ i ∈ T_1, ({Y : ℕ → F2 | Y i ∈ A i Y} : Set (ℕ → F2))) ∩
       (⋂ i ∈ S' \ T_1, ({Y : ℕ → F2 | Y i ∉ A i Y} : Set (ℕ → F2))))
      = ((c : ℝ≥0∞) / 4) ^ T_1.card *
        (((4 - c : ℕ) : ℝ≥0∞) / 4) ^ (S' \ T_1).card := by
  classical
  -- Bound c ≤ 4.
  have hc_le_4 : c ≤ 4 := by
    have h_sub : A 0 (fun _ => (1 : F2)) ⊆ F2_genFinset := by
      intro z hz
      have h_set := h_subset 0 (fun _ => (1 : F2)) (Finset.mem_coe.mpr hz)
      rw [← F2_genFinset_coe] at h_set
      exact Finset.mem_coe.mp h_set
    have hcard_eq : (A 0 (fun _ => (1 : F2))).card = c := h_card 0 _
    have := Finset.card_le_card h_sub
    rw [F2_genFinset_card] at this
    omega
  -- Pick n with S' ⊆ Finset.range n.
  obtain ⟨n, hS'_sub_range⟩ := S'.exists_nat_subset_range
  -- The joint event is the disjoint union over admissible patterns
  -- S ⊆ Finset.range n with S ∩ S' = T_1, of gen_patternEvent A n S.
  -- Equivalently, S = T_1 ∪ U where U ⊆ Finset.range n \ S'.
  -- The "admissible patterns" Finset.
  set adm : Finset (Finset ℕ) :=
    (Finset.range n).powerset.filter (fun S => S ∩ S' = T_1) with hadm_def
  -- Step A: rewrite the LHS event as a (countable) union over admissible patterns.
  have h_event_eq_aux :
      ∀ Y : ℕ → F2, (∀ i, i < n → Y i ∈ F2_generating_set) →
        (Y ∈ ((⋂ i ∈ T_1, ({Y : ℕ → F2 | Y i ∈ A i Y} : Set (ℕ → F2))) ∩
              (⋂ i ∈ S' \ T_1, ({Y : ℕ → F2 | Y i ∉ A i Y} : Set (ℕ → F2)))) ↔
         ∃ S ∈ adm, Y ∈ gen_patternEvent A n S) := by
    intro Y _hY_gen
    constructor
    · rintro ⟨h1, h0⟩
      -- Define S := {i ∈ Finset.range n | Y i ∈ A i Y}.
      set S : Finset ℕ := (Finset.range n).filter (fun i => Y i ∈ A i Y) with hS_def
      have hS_sub_range : S ⊆ Finset.range n := Finset.filter_subset _ _
      have hS_inter_S' : S ∩ S' = T_1 := by
        ext i
        simp only [Finset.mem_inter, hS_def, Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨⟨_, hYi⟩, hi_S'⟩
          -- hYi : Y i ∈ A i Y, hi_S' : i ∈ S'.
          -- If i ∉ T_1, then i ∈ S' \ T_1, so by h0 Y i ∉ A i Y, contradiction.
          by_contra h_notT1
          have hi_in_diff : i ∈ S' \ T_1 :=
            Finset.mem_sdiff.mpr ⟨hi_S', h_notT1⟩
          have hYi_not : Y i ∉ A i Y := by
            have := Set.mem_iInter.mp h0 i
            exact Set.mem_iInter.mp this hi_in_diff
          exact hYi_not hYi
        · intro hi_T1
          have hi_S' : i ∈ S' := hT_1 hi_T1
          have hi_lt : i < n := Finset.mem_range.mp (hS'_sub_range hi_S')
          have hYi : Y i ∈ A i Y := by
            have := Set.mem_iInter.mp h1 i
            exact Set.mem_iInter.mp this hi_T1
          exact ⟨⟨hi_lt, hYi⟩, hi_S'⟩
      refine ⟨S, ?_, ?_⟩
      · rw [hadm_def, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨hS_sub_range, hS_inter_S'⟩
      · intro i hi_lt
        rw [hS_def, Finset.mem_filter, Finset.mem_range]
        exact ⟨fun h => ⟨hi_lt, h⟩, fun ⟨_, h⟩ => h⟩
    · rintro ⟨S, hS_mem, hY_pat⟩
      rw [hadm_def, Finset.mem_filter, Finset.mem_powerset] at hS_mem
      obtain ⟨hS_sub, hS_inter⟩ := hS_mem
      refine ⟨?_, ?_⟩
      · rw [Set.mem_iInter]
        intro i
        rw [Set.mem_iInter]
        intro hi_T1
        have hi_S' : i ∈ S' := hT_1 hi_T1
        have hi_lt : i < n := Finset.mem_range.mp (hS'_sub_range hi_S')
        have hi_S : i ∈ S := by
          have hi_in : i ∈ S ∩ S' := by rw [hS_inter]; exact hi_T1
          exact (Finset.mem_inter.mp hi_in).1
        exact (hY_pat i hi_lt).mpr hi_S
      · rw [Set.mem_iInter]
        intro i
        rw [Set.mem_iInter]
        intro hi_diff
        rcases Finset.mem_sdiff.mp hi_diff with ⟨hi_S', hi_notT1⟩
        have hi_lt : i < n := Finset.mem_range.mp (hS'_sub_range hi_S')
        have hi_notS : i ∉ S := by
          intro hi_S
          have hi_in : i ∈ S ∩ S' := Finset.mem_inter.mpr ⟨hi_S, hi_S'⟩
          rw [hS_inter] at hi_in
          exact hi_notT1 hi_in
        intro hYi
        exact hi_notS ((hY_pat i hi_lt).mp hYi)
  -- Step B: a.s.-equality between the joint cylinder event and
  -- ⋃ S ∈ adm, gen_patternEvent A n S.
  set jointEvent : Set (ℕ → F2) :=
    (⋂ i ∈ T_1, ({Y : ℕ → F2 | Y i ∈ A i Y} : Set (ℕ → F2))) ∩
    (⋂ i ∈ S' \ T_1, ({Y : ℕ → F2 | Y i ∉ A i Y} : Set (ℕ → F2)))
    with hjoint_def
  set patUnion : Set (ℕ → F2) :=
    ⋃ S ∈ adm, gen_patternEvent A n S with hpatUnion_def
  have h_event_aeEq : jointEvent =ᵐ[step_measure] patUnion := by
    filter_upwards [walk_step_in_generating_set_ae] with Y hY_all
    apply propext
    have hY_gen : ∀ i, i < n → Y i ∈ F2_generating_set := fun i _ => hY_all i
    have hY_iff := h_event_eq_aux Y hY_gen
    show Y ∈ jointEvent ↔ Y ∈ patUnion
    constructor
    · intro hY
      rcases hY_iff.mp hY with ⟨S, hS_adm, hY_pat⟩
      show Y ∈ ⋃ S ∈ adm, gen_patternEvent A n S
      rw [Set.mem_iUnion]
      refine ⟨S, ?_⟩
      rw [Set.mem_iUnion]
      exact ⟨hS_adm, hY_pat⟩
    · intro hY
      have hY' : Y ∈ ⋃ S ∈ adm, gen_patternEvent A n S := hY
      rw [Set.mem_iUnion] at hY'
      obtain ⟨S, hY'⟩ := hY'
      rw [Set.mem_iUnion] at hY'
      obtain ⟨hS_adm, hY_pat⟩ := hY'
      exact hY_iff.mpr ⟨S, hS_adm, hY_pat⟩
  -- Step C: measure equality via a.s.-equality.
  rw [measure_congr h_event_aeEq]
  -- Step D: pairwise disjoint patterns + each pattern's mass.
  have hadm_sub_pow : ∀ S ∈ adm, S ⊆ Finset.range n := fun S hS =>
    Finset.mem_powerset.mp ((Finset.mem_filter.mp hS).1)
  have hdisj : (↑adm : Set (Finset ℕ)).PairwiseDisjoint (gen_patternEvent A n) := by
    intro S hS S'' hS'' hSS''
    show Disjoint (gen_patternEvent A n S) (gen_patternEvent A n S'')
    have hS_S' : S ⊆ Finset.range n := hadm_sub_pow S (Finset.mem_coe.mp hS)
    have hS''_S' : S'' ⊆ Finset.range n := hadm_sub_pow S'' (Finset.mem_coe.mp hS'')
    refine gen_patternEvent_pairwise_disjoint A n adm hadm_sub_pow ?_ ?_ hSS''
    · exact hS
    · exact hS''
  rw [measure_biUnion_finset₀ (s := adm) (f := gen_patternEvent A n) hdisj.aedisjoint
    (fun S hS => by
      have hS_sub : S ⊆ Finset.range n := hadm_sub_pow S hS
      have h_meas : MeasurableSet
          (⋃ y ∈ gen_realisingPrefixes A n S, fixedPrefixCylinder n y) := by
        apply MeasurableSet.biUnion (Finset.countable_toSet _)
        intro y _
        exact measurableSet_fixedPrefixCylinder n y
      exact h_meas.nullMeasurableSet.congr
        (gen_patternEvent_aeEq_biUnion A h_past n S).symm)]
  -- Step E: each summand is c^|S| * (4-c)^(n-|S|) * (1/4)^n.
  have h_const : ∀ S ∈ adm,
      step_measure (gen_patternEvent A n S)
        = (c : ℝ≥0∞) ^ S.card * ((4 - c : ℕ) : ℝ≥0∞) ^ (n - S.card) *
            (1/4 : ℝ≥0∞) ^ n := fun S hS =>
    gen_pattern_event_measure A h_past h_subset c h_card n S (hadm_sub_pow S hS)
  rw [Finset.sum_congr rfl h_const]
  -- Step F: reindex adm via S = T_1 ∪ U where U ⊆ Finset.range n \ S'.
  -- The bijection: U ↦ T_1 ∪ U.
  have hT_1_sub_range : T_1 ⊆ Finset.range n := fun i hi =>
    hS'_sub_range (hT_1 hi)
  have hT_1_disj_compl : Disjoint T_1 (Finset.range n \ S') := by
    rw [Finset.disjoint_right]
    intro i hi hi_T1
    rcases Finset.mem_sdiff.mp hi with ⟨_, hi_notS'⟩
    exact hi_notS' (hT_1 hi_T1)
  have h_bij :
      adm = (Finset.range n \ S').powerset.image (fun U => T_1 ∪ U) := by
    ext S
    simp only [hadm_def, Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · rintro ⟨hS_sub, hS_inter⟩
      refine ⟨S \ S', ?_, ?_⟩
      · -- S \ S' ⊆ Finset.range n \ S'
        intro i hi
        rcases Finset.mem_sdiff.mp hi with ⟨hi_S, hi_notS'⟩
        exact Finset.mem_sdiff.mpr ⟨hS_sub hi_S, hi_notS'⟩
      · -- T_1 ∪ (S \ S') = S
        ext i
        simp only [Finset.mem_union, Finset.mem_sdiff]
        constructor
        · rintro (hi_T1 | ⟨hi_S, _⟩)
          · -- T_1 ⊆ S because T_1 = S ∩ S' ⊆ S
            have hi_inter : i ∈ S ∩ S' := by rw [hS_inter]; exact hi_T1
            exact (Finset.mem_inter.mp hi_inter).1
          · exact hi_S
        · intro hi_S
          by_cases hi_S' : i ∈ S'
          · -- i ∈ S ∩ S' = T_1
            left
            have hi_inter : i ∈ S ∩ S' := Finset.mem_inter.mpr ⟨hi_S, hi_S'⟩
            rw [hS_inter] at hi_inter
            exact hi_inter
          · right
            exact ⟨hi_S, hi_S'⟩
    · rintro ⟨U, hU_sub, rfl⟩
      have hU_sub_range : U ⊆ Finset.range n := fun i hi =>
        (Finset.mem_sdiff.mp (hU_sub hi)).1
      have hU_disj_S' : Disjoint U S' := by
        rw [Finset.disjoint_left]
        intro i hi hi_S'
        rcases Finset.mem_sdiff.mp (hU_sub hi) with ⟨_, hi_notS'⟩
        exact hi_notS' hi_S'
      refine ⟨?_, ?_⟩
      · exact Finset.union_subset hT_1_sub_range hU_sub_range
      · -- (T_1 ∪ U) ∩ S' = T_1
        ext i
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hi_T1 | hi_U, hi_S'⟩
          · exact hi_T1
          · exfalso
            exact (Finset.disjoint_left.mp hU_disj_S') hi_U hi_S'
        · intro hi_T1
          exact ⟨Or.inl hi_T1, hT_1 hi_T1⟩
  rw [h_bij]
  rw [Finset.sum_image (g := fun U => T_1 ∪ U)]
  · -- Now sum over U ⊆ Finset.range n \ S'.
    -- Each |T_1 ∪ U| = |T_1| + |U| (disjoint).
    have h_card_union : ∀ U ∈ (Finset.range n \ S').powerset,
        (T_1 ∪ U).card = T_1.card + U.card := by
      intro U hU
      rw [Finset.mem_powerset] at hU
      have h_disj : Disjoint T_1 U :=
        hT_1_disj_compl.mono_right hU
      rw [Finset.card_union_of_disjoint h_disj]
    -- Massage to factor out (c : ℝ≥0∞) ^ T_1.card and reduce inner sum to 4^m.
    -- Define m := n - S'.card.
    have hS'_card_le : S'.card ≤ n := by
      have := Finset.card_le_card hS'_sub_range
      rwa [Finset.card_range] at this
    have hT_1_card_le : T_1.card ≤ S'.card := Finset.card_le_card hT_1
    have h_diff_card : (Finset.range n \ S').card = n - S'.card := by
      rw [Finset.card_sdiff_of_subset hS'_sub_range, Finset.card_range]
    -- For each U, compute n - |T_1 ∪ U| = (n - S'.card) - U.card + (S' \ T_1).card.
    -- Specifically: |T_1 ∪ U| = T_1.card + U.card. n - (T_1.card + U.card) = ?
    -- Note: n = T_1.card + (S' \ T_1).card + (n - S'.card). Indeed
    -- n - T_1.card = (S' \ T_1).card + (n - S'.card).
    have h_n_decomp : n - T_1.card = (S' \ T_1).card + (n - S'.card) := by
      have hSdiff_card : (S' \ T_1).card = S'.card - T_1.card :=
        Finset.card_sdiff_of_subset hT_1
      omega
    have h_simplify : ∀ U ∈ (Finset.range n \ S').powerset,
        (c : ℝ≥0∞) ^ (T_1 ∪ U).card *
          ((4 - c : ℕ) : ℝ≥0∞) ^ (n - (T_1 ∪ U).card) *
          (1/4 : ℝ≥0∞) ^ n
          = ((c : ℝ≥0∞) / 4) ^ T_1.card *
              (((4 - c : ℕ) : ℝ≥0∞) / 4) ^ (S' \ T_1).card *
              ((c : ℝ≥0∞) ^ U.card *
                ((4 - c : ℕ) : ℝ≥0∞) ^ ((n - S'.card) - U.card) *
                (1/4 : ℝ≥0∞) ^ (n - S'.card)) := by
      intro U hU
      have hU_in_pow := hU
      rw [Finset.mem_powerset] at hU
      have hU_card_le : U.card ≤ n - S'.card := by
        have := Finset.card_le_card hU
        rwa [h_diff_card] at this
      -- Rewrite using (a/b)^k = a^k * (1/4)^k on the RHS.
      have h_div_pow : ∀ (a : ℝ≥0∞) (k : ℕ), (a / 4) ^ k = a^k * (1/4 : ℝ≥0∞)^k := by
        intro a k
        rw [div_eq_mul_inv, mul_pow, ← one_div]
      rw [h_div_pow ((c : ℝ≥0∞)) T_1.card]
      rw [h_div_pow (((4 - c : ℕ) : ℝ≥0∞)) (S' \ T_1).card]
      rw [h_card_union U hU_in_pow]
      -- Two key arithmetic identities:
      -- (a) n - (T_1.card + U.card) = (S' \ T_1).card + (n - S'.card - U.card).
      -- (b) n = T_1.card + ((S' \ T_1).card + (n - S'.card)).
      have h_a : n - (T_1.card + U.card) = (S' \ T_1).card + (n - S'.card - U.card) := by
        omega
      have h_b : n = T_1.card + ((S' \ T_1).card + (n - S'.card)) := by omega
      rw [h_a]
      -- Now LHS exponent on (4-c) is (S' \ T_1).card + (n - S'.card - U.card).
      -- Split LHS pows.
      rw [pow_add ((4 - c : ℕ) : ℝ≥0∞) (S' \ T_1).card (n - S'.card - U.card)]
      rw [pow_add (c : ℝ≥0∞) T_1.card U.card]
      -- Now LHS = c^T_1 * c^U * ((4-c)^(S'\T_1) * (4-c)^(n-S'-U)) * (1/4)^n.
      -- Rewrite (1/4)^n via h_b. Replace the residual T_1 + S'\T_1 + (n-S') - S' - U
      -- exponent by n - S' - U (it should already equal n - S' - U after `rw [h_a]`).
      conv_lhs => rw [h_b, pow_add ((1 : ℝ≥0∞)/4) T_1.card ((S' \ T_1).card + (n - S'.card)),
                      pow_add ((1 : ℝ≥0∞)/4) (S' \ T_1).card (n - S'.card)]
      -- Cleanup the leftover (4-c)^(...) exponent introduced by h_b. It equals
      -- (n - S' - U).
      have h_exp_simp : T_1.card + ((S' \ T_1).card + (n - S'.card)) - S'.card - U.card
                          = n - S'.card - U.card := by omega
      rw [h_exp_simp]
      ring
    rw [Finset.sum_congr rfl h_simplify]
    -- Factor out the prefactor.
    rw [← Finset.mul_sum]
    -- Now compute the inner sum: it's the binomial sum over U ⊆ Finset.range n \ S'.
    -- ∑ U ⊆ Finset.range n \ S', c^|U| * (4-c)^((n - |S'|) - |U|) * (1/4)^(n - |S'|).
    -- = (1/4)^(n - |S'|) * ∑ U, c^|U| * (4-c)^((n - |S'|) - |U|)
    -- = (1/4)^(n - |S'|) * 4^(n - |S'|) (by binom_sum_c_4mc and bijection of powerset).
    -- = 1.
    -- We need to reindex: powerset of (Finset.range n \ S') has same |U| structure
    -- as powerset of Finset.range (n - S'.card). The sum value depends only on |U|.
    -- Approach: use binom_sum_c_4mc on m := (Finset.range n \ S').card = n - S'.card.
    -- The sum ∑ U ⊆ T, c^|U| * (4-c)^(|T| - |U|) = 4^|T| for any finite T (T = range n \ S').
    have h_inner_sum :
        ∑ U ∈ (Finset.range n \ S').powerset,
          ((c : ℝ≥0∞) ^ U.card *
            ((4 - c : ℕ) : ℝ≥0∞) ^ ((n - S'.card) - U.card) *
            (1/4 : ℝ≥0∞) ^ (n - S'.card)) = 1 := by
      -- Pull out the constant (1/4)^(n - S'.card).
      rw [← Finset.sum_mul]
      -- Show inner sum = 4^(n - S'.card).
      have h_card_diff : (Finset.range n \ S').card = n - S'.card := h_diff_card
      have h_inner_eq :
          ∑ U ∈ (Finset.range n \ S').powerset,
            (c : ℝ≥0∞) ^ U.card *
              ((4 - c : ℕ) : ℝ≥0∞) ^ ((n - S'.card) - U.card)
            = (4 : ℝ≥0∞) ^ (n - S'.card) := by
        -- Reindex via the bijection between powerset of (range n \ S') and
        -- powerset of (Finset.range (n - S'.card)) preserving cardinality.
        -- Actually we just need the abstract binomial identity for any finite Finset T:
        -- ∑ U ⊆ T, c^|U| * (4-c)^(|T| - |U|) = 4^|T|.
        -- This follows from binom_sum_c_4mc by partitioning powerset by cardinality.
        rw [show (n - S'.card) = (Finset.range n \ S').card from h_card_diff.symm]
        -- Group powerset by card.
        set T : Finset ℕ := Finset.range n \ S' with hT_def
        have h_eq_binom :
            ∑ U ∈ T.powerset,
              (c : ℝ≥0∞) ^ U.card *
                ((4 - c : ℕ) : ℝ≥0∞) ^ (T.card - U.card)
              = ((∑ U ∈ T.powerset, c ^ U.card * (4 - c) ^ (T.card - U.card) : ℕ) : ℝ≥0∞) := by
          rw [Nat.cast_sum]
          refine Finset.sum_congr rfl (fun U _ => ?_)
          push_cast
          ring
        rw [h_eq_binom]
        -- Reduce to binom_sum_c_4mc by cardinality grouping.
        -- Use induction on |T|: sum over powerset of a finite set indexed by cardinality
        -- only — switch to powerset of (Finset.range T.card) via card-preserving bijection.
        have h_powerset_via_card :
            ∑ U ∈ T.powerset, c ^ U.card * (4 - c) ^ (T.card - U.card)
              = ∑ U ∈ (Finset.range T.card).powerset,
                  c ^ U.card * (4 - c) ^ (T.card - U.card) := by
          -- Reindex using powersetCard.
          rw [show T.powerset = (Finset.range (T.card + 1)).biUnion
                (fun j => T.powersetCard j) from by
            ext U
            simp only [Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_range,
              Finset.mem_powersetCard]
            constructor
            · intro hU
              refine ⟨U.card, ?_, hU, rfl⟩
              have := Finset.card_le_card hU; omega
            · rintro ⟨_, _, hU, _⟩; exact hU]
          rw [show (Finset.range T.card).powerset = (Finset.range (T.card + 1)).biUnion
                (fun j => (Finset.range T.card).powersetCard j) from by
            ext U
            simp only [Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_range,
              Finset.mem_powersetCard]
            constructor
            · intro hU
              refine ⟨U.card, ?_, hU, rfl⟩
              have := Finset.card_le_card hU
              rw [Finset.card_range] at this; omega
            · rintro ⟨_, _, hU, _⟩; exact hU]
          rw [Finset.sum_biUnion, Finset.sum_biUnion]
          · refine Finset.sum_congr rfl (fun j hj => ?_)
            -- The inner sum depends only on |U| = j.
            have h_inner_T : ∑ U ∈ T.powersetCard j,
                c ^ U.card * (4 - c) ^ (T.card - U.card)
                = (T.powersetCard j).card • (c ^ j * (4 - c) ^ (T.card - j)) := by
              rw [Finset.sum_congr rfl (fun U hU => by
                rw [(Finset.mem_powersetCard.mp hU).2])]
              rw [Finset.sum_const]
            have h_inner_R : ∑ U ∈ (Finset.range T.card).powersetCard j,
                c ^ U.card * (4 - c) ^ (T.card - U.card)
                = ((Finset.range T.card).powersetCard j).card •
                    (c ^ j * (4 - c) ^ (T.card - j)) := by
              rw [Finset.sum_congr rfl (fun U hU => by
                rw [(Finset.mem_powersetCard.mp hU).2])]
              rw [Finset.sum_const]
            rw [h_inner_T, h_inner_R]
            rw [Finset.card_powersetCard, Finset.card_powersetCard, Finset.card_range]
          · -- Pairwise disjoint cardinality classes for range T.card.
            intro j _ j' _ hjj' x hxj hxj' a ha
            have h1 := (Finset.mem_powersetCard.mp (hxj ha)).2
            have h2 := (Finset.mem_powersetCard.mp (hxj' ha)).2
            exact absurd (h1.symm.trans h2) hjj'
          · -- Pairwise disjoint cardinality classes for T.
            intro j _ j' _ hjj' x hxj hxj' a ha
            have h1 := (Finset.mem_powersetCard.mp (hxj ha)).2
            have h2 := (Finset.mem_powersetCard.mp (hxj' ha)).2
            exact absurd (h1.symm.trans h2) hjj'
        rw [h_powerset_via_card]
        rw [binom_sum_c_4mc c T.card hc_le_4]
        push_cast; ring
      rw [h_inner_eq]
      -- 4^m * (1/4)^m = 1.
      rw [← mul_pow]
      rw [show ((4 : ℝ≥0∞) * (1/4)) = 1 from by
        rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]]
      rw [one_pow]
    rw [h_inner_sum, mul_one]
  · -- Image is injective: U ↦ T_1 ∪ U on disjoint side.
    intro U hU U' hU' h_eq
    rw [Finset.mem_coe, Finset.mem_powerset] at hU hU'
    have hU_disj : Disjoint T_1 U := hT_1_disj_compl.mono_right hU
    have hU'_disj : Disjoint T_1 U' := hT_1_disj_compl.mono_right hU'
    -- T_1 ∪ U = T_1 ∪ U' and T_1, U disjoint, T_1, U' disjoint implies U = U'.
    ext i
    have h_i := congr_arg (fun X => i ∈ X) h_eq
    simp only [Finset.mem_union] at h_i
    by_cases hi_T1 : i ∈ T_1
    · -- If i ∈ T_1, then i ∉ U and i ∉ U' (by disjointness).
      have hi_notU : i ∉ U := Finset.disjoint_left.mp hU_disj hi_T1
      have hi_notU' : i ∉ U' := Finset.disjoint_left.mp hU'_disj hi_T1
      exact ⟨fun h => absurd h hi_notU, fun h => absurd h hi_notU'⟩
    · constructor
      · intro hi_U
        rcases h_i.mp (Or.inr hi_U) with h | h
        · exact absurd h hi_T1
        · exact h
      · intro hi_U'
        rcases h_i.mpr (Or.inr hi_U') with h | h
        · exact absurd h hi_T1
        · exact h

/-- **Theorem (Wave 33, formerly Wave 23C companion axiom).** Generic
i.i.d. Bernoulli law for past-measurable indicator families on the
uniform-step infinite product measure.

Let `A : ℕ → (ℕ → F2) → Finset F2` be a sequence of finite subsets of `F2`
satisfying past-measurability, constant cardinality `c`, and subset of the
4-element generating set. Define `f_k(Y) := if Y k ∈ A k Y then (1 : ℝ)
else 0`. Then under `step_measure = Measure.infinitePi (fun _ => Z_uniform)`:
1. The family `(f_k)_{k : ℕ}` is mutually independent (`iIndepFun`).
2. Each `f_k` is identically distributed to `f_0`.
3. The marginal mean is `c/4`: `∫ Y, f_0 Y ∂step_measure = c/4`.

**Proof.** See `williams_97_note.tex` §1: count the realising prefixes.
The Lean encoding goes through `gen_pattern_event_measure` (Wave 33's
generic version of Wave 28's `pattern_event_measure`).

**Wave 33 status.** Marginal mean (3) and identical distribution (2) are
fully proven from `step_measure_marginal_event` (which itself uses
`gen_pattern_event_measure`). Independence (1) is derived from the narrow
admission `gen_joint_cylinder_measure` (a generalisation of the marginal
formula to the joint cylinder, proved exactly the same way: `~150 LOC` of
ENNReal/Finset binomial plumbing). All three conclusions become
unconditional theorems once `gen_joint_cylinder_measure` is dissolved. -/
theorem iIndepFun_iIdentDistrib_uniformIndic_pastDep
    (A : ℕ → (ℕ → F2) → Finset F2)
    (h_past : ∀ k Y Y', (∀ j, j < k → Y j = Y' j) → A k Y = A k Y')
    (h_subset : ∀ k Y, ↑(A k Y) ⊆ F2_generating_set)
    (c : ℕ) (h_card : ∀ k Y, (A k Y).card = c) :
    let f : ℕ → (ℕ → F2) → ℝ :=
      fun k Y => if Y k ∈ A k Y then (1 : ℝ) else 0
    iIndepFun f step_measure
      ∧ (∀ k : ℕ, IdentDistrib (f k) (f 0) step_measure step_measure)
      ∧ ∫ Y, f 0 Y ∂step_measure = (c : ℝ) / 4 := by
  set f : ℕ → (ℕ → F2) → ℝ :=
    fun k Y => if Y k ∈ A k Y then (1 : ℝ) else 0 with hf_def
  -- Bound c ≤ 4.
  have hc_le_4 : c ≤ 4 := by
    have h_sub : A 0 (fun _ => (1 : F2)) ⊆ F2_genFinset := by
      intro z hz
      have h_set := h_subset 0 (fun _ => (1 : F2)) (Finset.mem_coe.mpr hz)
      rw [← F2_genFinset_coe] at h_set
      exact Finset.mem_coe.mp h_set
    have hcard_eq : (A 0 (fun _ => (1 : F2))).card = c := h_card 0 _
    have := Finset.card_le_card h_sub
    rw [F2_genFinset_card] at this
    omega
  -- Helper: each `f k` is measurable.
  have hf_meas : ∀ k, Measurable (f k) := fun k => f_measurable A h_past k
  -- Helper: marginal events have the right measure.
  have h_marg_1 : ∀ k, step_measure {Y | Y k ∈ A k Y} = (c : ℝ≥0∞) / 4 :=
    fun k => step_measure_marginal_event A h_past h_subset c h_card k
  have h_marg_0 : ∀ k, step_measure {Y : ℕ → F2 | Y k ∉ A k Y}
                    = ((4 - c : ℕ) : ℝ≥0∞) / 4 := by
    intro k
    have h_compl : {Y : ℕ → F2 | Y k ∉ A k Y} = {Y : ℕ → F2 | Y k ∈ A k Y}ᶜ := by
      ext Y; simp [Set.mem_compl_iff, Set.mem_setOf_eq]
    rw [h_compl]
    rw [MeasureTheory.measure_compl (measurableSet_marginal_event A h_past k)
        (by exact measure_ne_top step_measure _)]
    rw [show step_measure Set.univ = 1 from
        (IsProbabilityMeasure.measure_univ : step_measure Set.univ = 1)]
    rw [h_marg_1 k]
    -- 1 - c/4 = (4 - c)/4 in ℝ≥0∞.
    have h_c_le : (c : ℝ≥0∞) ≤ 4 := by exact_mod_cast hc_le_4
    have h4 : (1 : ℝ≥0∞) = (4 : ℝ≥0∞) / 4 := by
      rw [ENNReal.div_self (by norm_num) (by norm_num)]
    rw [h4, ← ENNReal.sub_div (fun _ _ => by norm_num)]
    have h_cast_4mc : ((4 - c : ℕ) : ℝ≥0∞) = (4 : ℝ≥0∞) - (c : ℝ≥0∞) := by
      have h_step : (4 - c : ℕ) + c = 4 := by omega
      have h_add : ((4 - c : ℕ) : ℝ≥0∞) + (c : ℝ≥0∞) = (4 : ℝ≥0∞) := by
        have := congr_arg (fun n : ℕ => (n : ℝ≥0∞)) h_step
        simp only at this
        rw [Nat.cast_add] at this
        convert this using 1
      have h_c_ne_top : (c : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top c
      rw [← h_add, ENNReal.add_sub_cancel_right h_c_ne_top]
    rw [h_cast_4mc]
  refine ⟨?_, ?_, ?_⟩
  · -- (1) Independence.
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro S' sets h_meas
    classical
    -- Partition S' by membership of {0, 1} in sets i:
    -- T_1 = "1 ∈, 0 ∉" (preimage = E1), T_0 = "1 ∉, 0 ∈" (preimage = E0),
    -- T_univ = "1 ∈, 0 ∈" (preimage = univ), T_empty = "1 ∉, 0 ∉" (preimage = ∅).
    set T_1 : Finset ℕ := S'.filter (fun i => (1 : ℝ) ∈ sets i ∧ (0 : ℝ) ∉ sets i)
      with hT_1_def
    set T_0 : Finset ℕ := S'.filter (fun i => (1 : ℝ) ∉ sets i ∧ (0 : ℝ) ∈ sets i)
      with hT_0_def
    set T_empty : Finset ℕ :=
      S'.filter (fun i => (1 : ℝ) ∉ sets i ∧ (0 : ℝ) ∉ sets i) with hT_empty_def
    -- Define T_univ := {i ∈ S' | (1 ∈ sets i) ∧ (0 ∈ sets i)}.
    -- These are the "preimage = univ" indices.
    -- Three cases:
    by_cases h_empty : T_empty.Nonempty
    · -- ∃ i ∈ S' with both 1 ∉ sets i and 0 ∉ sets i, so f i ⁻¹ sets i = ∅.
      obtain ⟨i, hi_empty⟩ := h_empty
      rw [Finset.mem_filter] at hi_empty
      obtain ⟨hi_S', h1_not, h0_not⟩ := hi_empty
      have h_preimage_empty : f i ⁻¹' sets i = ∅ := by
        rw [hf_def, f_preimage_set A i (sets i)]
        rw [if_neg h1_not, if_neg h0_not, Set.union_empty]
      have h_inter_empty : ⋂ i ∈ S', f i ⁻¹' sets i = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro Y hY
        rw [Set.mem_iInter] at hY
        have := hY i
        rw [Set.mem_iInter] at this
        have hYi := this hi_S'
        rw [h_preimage_empty] at hYi
        exact hYi
      rw [h_inter_empty]
      simp only [measure_empty]
      symm
      apply Finset.prod_eq_zero hi_S'
      rw [h_preimage_empty]; simp
    · -- T_empty is empty. So for each i ∈ S', (f i)⁻¹ sets i ≠ ∅. Each preimage
      -- is one of E1_i (if T_1), E0_i (if T_0), or univ (if T_univ).
      -- Strategy: Define T_constr := T_1 ∪ T_0 (the constrained indices) and
      -- T_univ := S' \ T_constr (unconstrained, where 0 and 1 both ∈ sets i).
      -- The intersection ⋂ i ∈ S', preimage = ⋂ i ∈ T_constr, preimage (since
      -- preimage = univ for T_univ indices). Then by gen_joint_cylinder_measure
      -- (with S' replaced by T_constr and T_1 here = same), the measure is
      -- (c/4)^|T_1| * ((4-c)/4)^|T_0|. The product side similarly factorises:
      -- ∏ i ∈ S', step_measure (f i ⁻¹ sets i) = ∏ i ∈ T_1, c/4 * ∏ i ∈ T_0, (4-c)/4
      --   * ∏ i ∈ T_univ, 1 (the univ ones).
      -- Define T_constr = T_1 ∪ T_0.
      classical
      set T_constr : Finset ℕ := T_1 ∪ T_0 with hT_constr_def
      have hT_1_sub : T_1 ⊆ S' := Finset.filter_subset _ _
      have hT_0_sub : T_0 ⊆ S' := Finset.filter_subset _ _
      have hT_constr_sub : T_constr ⊆ S' := Finset.union_subset hT_1_sub hT_0_sub
      have hT_1_sub_constr : T_1 ⊆ T_constr := Finset.subset_union_left
      have hT_disj : Disjoint T_1 T_0 := by
        rw [hT_1_def, hT_0_def, Finset.disjoint_filter]
        intro i _ ⟨h1, _⟩ ⟨h_not, _⟩
        exact h_not h1
      have hT_constr_diff : T_constr \ T_1 = T_0 := by
        rw [hT_constr_def, Finset.union_sdiff_left]
        exact Finset.sdiff_eq_self_of_disjoint hT_disj.symm
      -- Compute LHS: ⋂ i ∈ S', (f i)⁻¹ sets i = ⋂ i ∈ T_constr, (f i)⁻¹ sets i.
      -- For i ∈ T_1: preimage = E1_i. For i ∈ T_0: preimage = E0_i. For i ∉ T_constr (i.e.
      -- 1 ∈ sets i ∧ 0 ∈ sets i): preimage = univ.
      have h_preimage_eq : ∀ i, i ∈ S' →
          f i ⁻¹' sets i =
          (if i ∈ T_1 then ({Y : ℕ → F2 | Y i ∈ A i Y} : Set (ℕ → F2))
           else if i ∈ T_0 then ({Y : ℕ → F2 | Y i ∉ A i Y} : Set (ℕ → F2))
           else Set.univ) := by
        intro i hi
        rw [hf_def, f_preimage_set A i (sets i)]
        by_cases h1 : (1 : ℝ) ∈ sets i
        · by_cases h0 : (0 : ℝ) ∈ sets i
          · -- Both 1, 0 ∈ sets i: i ∉ T_1 (since 0 ∈ sets i), i ∉ T_0 (since 1 ∈ sets i),
            -- so the if-chain falls through to univ.
            have hi_notT1 : i ∉ T_1 := by
              rw [hT_1_def, Finset.mem_filter]; exact fun ⟨_, _, h⟩ => h h0
            have hi_notT0 : i ∉ T_0 := by
              rw [hT_0_def, Finset.mem_filter]; exact fun ⟨_, h, _⟩ => h h1
            rw [if_pos h1, if_pos h0, if_neg hi_notT1, if_neg hi_notT0]
            -- preimage = E1_i ∪ E0_i = univ.
            ext Y
            simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_univ, iff_true]
            exact em (Y i ∈ A i Y)
          · -- 1 ∈ sets i, 0 ∉ sets i: preimage = E1_i, i ∈ T_1.
            have hi_T1 : i ∈ T_1 := by
              rw [hT_1_def, Finset.mem_filter]; exact ⟨hi, h1, h0⟩
            rw [if_pos h1, if_neg h0, Set.union_empty, if_pos hi_T1]
        · by_cases h0 : (0 : ℝ) ∈ sets i
          · -- 1 ∉ sets i, 0 ∈ sets i: preimage = E0_i, i ∈ T_0.
            have hi_notT1 : i ∉ T_1 := by
              rw [hT_1_def, Finset.mem_filter]; exact fun ⟨_, h, _⟩ => h1 h
            have hi_T0 : i ∈ T_0 := by
              rw [hT_0_def, Finset.mem_filter]; exact ⟨hi, h1, h0⟩
            rw [if_neg h1, if_pos h0, Set.empty_union, if_neg hi_notT1, if_pos hi_T0]
          · -- Both 0, 1 ∉ sets i: preimage = ∅. But T_empty.Nonempty was excluded.
            exfalso; apply h_empty
            refine ⟨i, ?_⟩
            rw [hT_empty_def, Finset.mem_filter]; exact ⟨hi, h1, h0⟩
      -- Step 1: Show LHS = step_measure (joint cylinder over T_1, T_0).
      have h_inter_eq :
          (⋂ i ∈ S', f i ⁻¹' sets i)
          = ((⋂ i ∈ T_1, ({Y : ℕ → F2 | Y i ∈ A i Y} : Set (ℕ → F2))) ∩
             (⋂ i ∈ T_0, ({Y : ℕ → F2 | Y i ∉ A i Y} : Set (ℕ → F2)))) := by
        ext Y
        simp only [Set.mem_iInter, Set.mem_inter_iff]
        constructor
        · intro h
          refine ⟨fun i hi => ?_, fun i hi => ?_⟩
          · have hi_S' := hT_1_sub hi
            have h_pre := h_preimage_eq i hi_S'
            have := h i hi_S'
            rw [h_pre, if_pos hi] at this
            exact this
          · have hi_S' := hT_0_sub hi
            have hi_notT1 : i ∉ T_1 := fun h_in =>
              Finset.disjoint_left.mp hT_disj h_in hi
            have h_pre := h_preimage_eq i hi_S'
            have := h i hi_S'
            rw [h_pre, if_neg hi_notT1, if_pos hi] at this
            exact this
        · rintro ⟨h1, h0⟩ i hi
          have h_pre := h_preimage_eq i hi
          by_cases hi_T1 : i ∈ T_1
          · rw [h_pre, if_pos hi_T1]; exact h1 i hi_T1
          · by_cases hi_T0 : i ∈ T_0
            · rw [h_pre, if_neg hi_T1, if_pos hi_T0]; exact h0 i hi_T0
            · rw [h_pre, if_neg hi_T1, if_neg hi_T0]; trivial
      rw [h_inter_eq]
      -- Apply gen_joint_cylinder_measure on T_constr partitioned as (T_1, T_0).
      -- Rewrite the inner inter over T_0 to use S' \ T_1 = T_0 (within T_constr).
      rw [show
            ((⋂ i ∈ T_1, ({Y : ℕ → F2 | Y i ∈ A i Y} : Set (ℕ → F2))) ∩
             (⋂ i ∈ T_0, ({Y : ℕ → F2 | Y i ∉ A i Y} : Set (ℕ → F2))))
            = ((⋂ i ∈ T_1, ({Y : ℕ → F2 | Y i ∈ A i Y} : Set (ℕ → F2))) ∩
               (⋂ i ∈ T_constr \ T_1, ({Y : ℕ → F2 | Y i ∉ A i Y} : Set (ℕ → F2))))
            from by rw [hT_constr_diff]]
      rw [gen_joint_cylinder_measure A h_past h_subset c h_card T_constr T_1
            hT_1_sub_constr]
      -- Step 2: Show RHS = product over S' of step_measure of preimage.
      -- For i ∈ T_1: c/4. For i ∈ T_0: (4-c)/4. For i ∉ T_constr: 1 (univ).
      have h_prod_eq : ∀ i ∈ S', step_measure (f i ⁻¹' sets i)
          = (if i ∈ T_1 then (c : ℝ≥0∞) / 4
             else if i ∈ T_0 then ((4 - c : ℕ) : ℝ≥0∞) / 4
             else 1) := by
        intro i hi
        rw [h_preimage_eq i hi]
        by_cases hi_T1 : i ∈ T_1
        · rw [if_pos hi_T1, if_pos hi_T1]; exact h_marg_1 i
        · by_cases hi_T0 : i ∈ T_0
          · rw [if_neg hi_T1, if_pos hi_T0, if_neg hi_T1, if_pos hi_T0]
            exact h_marg_0 i
          · rw [if_neg hi_T1, if_neg hi_T0, if_neg hi_T1, if_neg hi_T0]
            exact measure_univ
      rw [Finset.prod_congr rfl h_prod_eq]
      -- Split the product: indices in T_1, T_0, S' \ T_constr.
      have h_S'_partition : S' = T_1 ∪ T_0 ∪ (S' \ T_constr) := by
        rw [hT_constr_def]
        rw [show T_1 ∪ T_0 ∪ (S' \ (T_1 ∪ T_0)) = S' from by
          rw [Finset.union_sdiff_of_subset hT_constr_sub]]
      have hT_disj_constr_compl : Disjoint T_constr (S' \ T_constr) :=
        Finset.disjoint_sdiff
      have hT_disj_T1_T0_compl : Disjoint (T_1 ∪ T_0) (S' \ T_constr) :=
        hT_disj_constr_compl
      rw [h_S'_partition]
      rw [Finset.prod_union hT_disj_T1_T0_compl]
      rw [Finset.prod_union hT_disj]
      -- Now: (∏_{i ∈ T_1} c/4) * (∏_{i ∈ T_0} (4-c)/4) * (∏_{i ∈ S' \ T_constr} 1) = …
      have h_prod_T1 : ∏ i ∈ T_1,
          (if i ∈ T_1 then (c : ℝ≥0∞) / 4
           else if i ∈ T_0 then ((4 - c : ℕ) : ℝ≥0∞) / 4 else 1)
          = ((c : ℝ≥0∞) / 4) ^ T_1.card := by
        rw [Finset.prod_congr rfl (fun i hi => by rw [if_pos hi])]
        rw [Finset.prod_const]
      have h_prod_T0 : ∏ i ∈ T_0,
          (if i ∈ T_1 then (c : ℝ≥0∞) / 4
           else if i ∈ T_0 then ((4 - c : ℕ) : ℝ≥0∞) / 4 else 1)
          = (((4 - c : ℕ) : ℝ≥0∞) / 4) ^ T_0.card := by
        rw [Finset.prod_congr rfl (fun i hi => by
          have hi_notT1 : i ∉ T_1 := fun h =>
            Finset.disjoint_left.mp hT_disj h hi
          rw [if_neg hi_notT1, if_pos hi])]
        rw [Finset.prod_const]
      have h_prod_compl : ∏ i ∈ S' \ T_constr,
          (if i ∈ T_1 then (c : ℝ≥0∞) / 4
           else if i ∈ T_0 then ((4 - c : ℕ) : ℝ≥0∞) / 4 else 1)
          = 1 := by
        rw [Finset.prod_congr rfl (fun i hi => by
          have hi_notconstr : i ∉ T_constr :=
            (Finset.mem_sdiff.mp hi).2
          have hi_notT1 : i ∉ T_1 :=
            fun h => hi_notconstr (hT_1_sub_constr h)
          have hi_notT0 : i ∉ T_0 :=
            fun h => hi_notconstr (Finset.mem_union.mpr (Or.inr h))
          rw [if_neg hi_notT1, if_neg hi_notT0])]
        rw [Finset.prod_const_one]
      rw [h_prod_T1, h_prod_T0, h_prod_compl, mul_one]
      -- Now LHS = (c/4)^|T_1| * ((4-c)/4)^|T_constr \ T_1|, where T_constr \ T_1 = T_0.
      rw [hT_constr_diff]
  · -- (2) Identical distribution.
    intro k
    refine ⟨(hf_meas k).aemeasurable, (hf_meas 0).aemeasurable, ?_⟩
    -- Both `Measure.map (f k)` and `Measure.map (f 0)` are probability measures
    -- on ℝ supported on {0, 1}. They are equal iff their mass on {1} agrees.
    -- Approach: compute the measure of each Borel set s ⊆ ℝ via
    -- `Measure.map_apply (hf_meas k) hs = step_measure (f k ⁻¹' s)`, and use
    -- `f_preimage_set` to express the preimage.
    refine MeasureTheory.Measure.ext (fun s hs => ?_)
    rw [Measure.map_apply (hf_meas k) hs, Measure.map_apply (hf_meas 0) hs]
    classical
    rw [f_preimage_set A k s, f_preimage_set A 0 s]
    -- Both sides are sums of (∅/E1/E0/univ) by 1∈s, 0∈s.
    have h_disj_k : Disjoint (if (1 : ℝ) ∈ s then ({Y | Y k ∈ A k Y} : Set (ℕ → F2)) else ∅)
        (if (0 : ℝ) ∈ s then ({Y : ℕ → F2 | Y k ∉ A k Y} : Set (ℕ → F2)) else ∅) := by
      by_cases h1 : (1 : ℝ) ∈ s
      · by_cases h0 : (0 : ℝ) ∈ s
        · rw [if_pos h1, if_pos h0]
          rw [Set.disjoint_iff_forall_ne]
          rintro Y hY Z hZ rfl
          exact hZ hY
        · rw [if_pos h1, if_neg h0]; exact Disjoint.symm (Set.empty_disjoint _)
      · rw [if_neg h1]; exact (Set.empty_disjoint _)
    have h_disj_0 : Disjoint (if (1 : ℝ) ∈ s then ({Y | Y 0 ∈ A 0 Y} : Set (ℕ → F2)) else ∅)
        (if (0 : ℝ) ∈ s then ({Y : ℕ → F2 | Y 0 ∉ A 0 Y} : Set (ℕ → F2)) else ∅) := by
      by_cases h1 : (1 : ℝ) ∈ s
      · by_cases h0 : (0 : ℝ) ∈ s
        · rw [if_pos h1, if_pos h0]
          rw [Set.disjoint_iff_forall_ne]
          rintro Y hY Z hZ rfl
          exact hZ hY
        · rw [if_pos h1, if_neg h0]; exact Disjoint.symm (Set.empty_disjoint _)
      · rw [if_neg h1]; exact (Set.empty_disjoint _)
    have hmeas_E1_k : MeasurableSet (if (1 : ℝ) ∈ s then ({Y | Y k ∈ A k Y} : Set (ℕ → F2)) else ∅) := by
      by_cases h1 : (1 : ℝ) ∈ s
      · rw [if_pos h1]; exact measurableSet_marginal_event A h_past k
      · rw [if_neg h1]; exact MeasurableSet.empty
    have hmeas_E0_k : MeasurableSet (if (0 : ℝ) ∈ s then ({Y : ℕ → F2 | Y k ∉ A k Y} : Set (ℕ → F2)) else ∅) := by
      by_cases h0 : (0 : ℝ) ∈ s
      · rw [if_pos h0]; exact measurableSet_marginal_event_compl A h_past k
      · rw [if_neg h0]; exact MeasurableSet.empty
    have hmeas_E1_0 : MeasurableSet (if (1 : ℝ) ∈ s then ({Y | Y 0 ∈ A 0 Y} : Set (ℕ → F2)) else ∅) := by
      by_cases h1 : (1 : ℝ) ∈ s
      · rw [if_pos h1]; exact measurableSet_marginal_event A h_past 0
      · rw [if_neg h1]; exact MeasurableSet.empty
    have hmeas_E0_0 : MeasurableSet (if (0 : ℝ) ∈ s then ({Y : ℕ → F2 | Y 0 ∉ A 0 Y} : Set (ℕ → F2)) else ∅) := by
      by_cases h0 : (0 : ℝ) ∈ s
      · rw [if_pos h0]; exact measurableSet_marginal_event_compl A h_past 0
      · rw [if_neg h0]; exact MeasurableSet.empty
    rw [measure_union h_disj_k hmeas_E0_k]
    rw [measure_union h_disj_0 hmeas_E0_0]
    -- Each side: mass(if 1∈s then E1_? else ∅) + mass(if 0∈s then E0_? else ∅).
    have h_mass_E1 : ∀ k : ℕ,
        step_measure (if (1 : ℝ) ∈ s then ({Y : ℕ → F2 | Y k ∈ A k Y}) else ∅)
        = if (1 : ℝ) ∈ s then (c : ℝ≥0∞) / 4 else 0 := by
      intro k
      by_cases h1 : (1 : ℝ) ∈ s
      · rw [if_pos h1, if_pos h1]; exact h_marg_1 k
      · rw [if_neg h1, if_neg h1]; simp
    have h_mass_E0 : ∀ k : ℕ,
        step_measure (if (0 : ℝ) ∈ s then ({Y : ℕ → F2 | Y k ∉ A k Y}) else ∅)
        = if (0 : ℝ) ∈ s then ((4 - c : ℕ) : ℝ≥0∞) / 4 else 0 := by
      intro k
      by_cases h0 : (0 : ℝ) ∈ s
      · rw [if_pos h0, if_pos h0]; exact h_marg_0 k
      · rw [if_neg h0, if_neg h0]; simp
    rw [h_mass_E1 k, h_mass_E0 k, h_mass_E1 0, h_mass_E0 0]
  · -- (3) Marginal mean.
    -- ∫ Y, f 0 Y = step_measure {Y | f 0 Y = 1} (in ℝ).
    have h_indic_eq : (fun Y : ℕ → F2 => f 0 Y) =
        Set.indicator {Y : ℕ → F2 | Y 0 ∈ A 0 Y} (fun _ => (1 : ℝ)) := by
      funext Y
      simp only [hf_def]
      show (if Y 0 ∈ A 0 Y then (1 : ℝ) else 0) =
        Set.indicator {Y : ℕ → F2 | Y 0 ∈ A 0 Y} (fun _ => (1 : ℝ)) Y
      by_cases h : Y 0 ∈ A 0 Y
      · have hmem : Y ∈ {Y : ℕ → F2 | Y 0 ∈ A 0 Y} := h
        rw [if_pos h, Set.indicator_of_mem hmem]
      · have hnmem : Y ∉ {Y : ℕ → F2 | Y 0 ∈ A 0 Y} := h
        rw [if_neg h, Set.indicator_of_notMem hnmem]
    show ∫ Y, f 0 Y ∂step_measure = (c : ℝ) / 4
    rw [show (fun Y : ℕ → F2 => f 0 Y) = (fun Y : ℕ → F2 => f 0 Y) from rfl]
    rw [show ∫ Y, f 0 Y ∂step_measure = ∫ Y,
        Set.indicator {Y : ℕ → F2 | Y 0 ∈ A 0 Y} (fun _ => (1 : ℝ)) Y ∂step_measure
        from by rw [show (fun Y => f 0 Y) = _ from h_indic_eq]]
    rw [MeasureTheory.integral_indicator (measurableSet_marginal_event A h_past 0)]
    rw [MeasureTheory.integral_const]
    rw [Measure.real, MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
    rw [Set.univ_inter, h_marg_1 0]
    -- Goal: ((c : ℝ≥0∞) / 4).toReal • 1 = (c : ℝ) / 4
    rw [smul_eq_mul, mul_one]
    rw [ENNReal.toReal_div]
    push_cast
    rfl

/-! ### Wave 22F.3 housekeeping — dead martingale infrastructure removed

The Wave 22F.2.1/.2.2 route to Q40 via `harmonic_along_walk_isMartingale` +
`harmonic_along_walk_converges_ae` plus `harmonic_measure_atomless` and
its companions was superseded by the direct finite-ball Route (a) closure
in `EnsX2026.FreeGroup.TreeBoundedHarmonicVanish`. The natural filtration
`walkFil`, the adapted-filtration and martingale-convergence
infrastructure, and the companion axiom
`harmonic_along_walk_martingale_property` have been removed here because
nothing outside this file consumed them after the Route (a) closure; the
Azuma chain for Q42 uses a self-contained companion axiom
`centred_away_azuma_tail` (see below) and does not depend on any of them. -/

/-! ### Q42 — Binomial distribution and Hoeffding bound for `b_φ(X_n)`

The exam states that the Busemann function evaluated along the walk
satisfies `(b_φ(X_n) + n)/2 ~ Binomial(n, 3/4)`: this is because at each
step the walk moves towards `φ` (Busemann decrement `−1`) with probability
`1/4` and away from `φ` (Busemann increment `+1`) with probability `3/4`.

We work with the "away" indicators
`ξ_i(Y) := (Δ_i(Y) + 1)/2 ∈ {0, 1}` where
`Δ_i(Y) := b_φ(X_{i+1}(Y)) − b_φ(X_i(Y))`, and their partial sums
`S_n(Y) := ∑_{i<n} ξ_i(Y)`.

The axiom `busemann_other_neighbours` guarantees `Δ_i ∈ {−1, +1}`, so the
`ξ_i` are Bernoulli. -/

/-- The Busemann increment at step `n`:
`Δ_n(Y) = b_φ(X_{n+1}(Y)) − b_φ(X_n(Y))`. By
`busemann_other_neighbours`, this is either `−1` or `+1`. -/
def busemann_incr (φ : ∂F2) (n : ℕ) (Y : ℕ → F2) : ℤ :=
  busemann φ (X_walk (n + 1) Y) - busemann φ (X_walk n Y)

/-- The "away" indicator at step `n`, taking values in `{0, 1}`:
`ξ_n = (Δ_n + 1)/2`, equal to `1` iff the walk moved away from `φ` at step
`n`. -/
def away_indicator (φ : ∂F2) (n : ℕ) (Y : ℕ → F2) : ℝ :=
  ((busemann_incr φ n Y + 1 : ℤ) : ℝ) / 2

/-- The partial sum of "away" indicators up to time `n`:
`S_n = ∑_{i<n} ξ_i`. The exam identifies `S_n` with a `Binomial(n, 3/4)`
random variable, since `b_φ(X_n) = 2 S_n − n`. -/
def away_sum (φ : ∂F2) (n : ℕ) (Y : ℕ → F2) : ℝ :=
  ∑ i ∈ Finset.range n, away_indicator φ i Y

@[simp] lemma away_sum_zero (φ : ∂F2) (Y : ℕ → F2) : away_sum φ 0 Y = 0 := by
  simp [away_sum]

/-- The identity `b_φ(X_n) = 2 S_n − n` relating the Busemann function of
the walk to the away-indicator sum. Proof by induction on `n`: base case
uses `busemann_one` (`b_φ(1) = 0`); inductive step expands
`away_sum_{n+1} = away_sum_n + ξ_n`, uses `2 ξ_n = Δ_n + 1` where
`Δ_n := b_φ(X_{n+1}) − b_φ(X_n)`, and combines with the IH via `linarith`. -/
theorem busemann_walk_eq_two_sum_sub (φ : ∂F2) (n : ℕ) (Y : ℕ → F2) :
    (busemann φ (X_walk n Y) : ℝ) = 2 * away_sum φ n Y - n := by
  induction n with
  | zero =>
    -- `b_φ(X_0) = b_φ(1) = 0` and `away_sum φ 0 Y = 0`.
    simp [away_sum]
  | succ n ih =>
    -- Unfold `away_sum φ (n+1) Y = away_sum φ n Y + away_indicator φ n Y`.
    have h_sum_succ :
        away_sum φ (n + 1) Y = away_sum φ n Y + away_indicator φ n Y := by
      simp [away_sum, Finset.sum_range_succ]
    -- Unfold the Busemann increment `Δ_n = b_φ(X_{n+1}) − b_φ(X_n)` (in ℤ).
    have h_incr :
        (busemann φ (X_walk (n + 1) Y) : ℝ)
          = (busemann_incr φ n Y : ℝ) + (busemann φ (X_walk n Y) : ℝ) := by
      simp [busemann_incr, Int.cast_sub, sub_add_cancel]
    -- Relate the indicator to the increment: `2 ξ_n = Δ_n + 1`.
    have h_indic :
        2 * away_indicator φ n Y = (busemann_incr φ n Y : ℝ) + 1 := by
      unfold away_indicator
      push_cast
      ring
    -- Combine via algebraic manipulation.
    rw [h_incr, ih, h_sum_succ]
    push_cast
    linarith [h_indic]

/-! #### Q42 binomial identification (orphan, removed)

An earlier draft carried a companion axiom `away_sum_has_binomial_law`
identifying the away-sum distribution as `Binomial(n, 3/4)`. It was
never consumed downstream — Wave 16A rerouted Q42 via Azuma (see the
chain `busemann_walk_hoeffding` → `centred_away_azuma_tail` below) —
and was removed in the housekeeping pass after Wave 22A's closure.
The binomial identification is still the textbook route to Q42 (cf.
Williams, *Probability with Martingales*, §4); the Azuma route we
adopt is a formalisation-efficient generalisation, not a correction
of the exam's mathematical content. -/

/-! #### Wave 23B — i.i.d. Hoeffding closure (errata note E3 corrected)

The Wave 16 errata note above (and the original Azuma-companion-axiom
architecture) was based on the claim that the centred indicators
`ξ_i = away_indicator φ i Y - 3/4` are not i.i.d. **That claim is
incorrect.** The same constant-conditional-probability argument used in
Wave 23A.3 for `coupledIndicator` applies here:

* `away_indicator φ i Y = 1` iff `Y i ∈ AwayGenerators(X_walk i Y)`, the
  3-element subset of `F2_generating_set` consisting of generators that
  move the walk away from `φ` at the current vertex.
* Given `F_i := σ(Y_0, …, Y_{i-1})`, the walk position `X_walk i Y` is
  determined, hence so is the 3-subset `AwayGenerators(X_walk i Y)`.
* `Y i ∼ Z_uniform` is independent of `F_i` (product structure of
  `step_measure = Measure.infinitePi (fun _ => Z_uniform)`) and uniform
  on the 4-element set `F2_generating_set`. So
  `P(away_indicator φ i = 1 | F_i) = 3/4`, a constant.
* By "constant conditional probability ⇒ independence" (Williams,
  *Probability with Martingales*, §9.7; Klenke, *Probability Theory*,
  §5.3), `away_indicator φ i ⊥⊥ F_i`. Iterating in `i`, the family is
  mutually independent. The marginal is Bernoulli(3/4).

So `(away_indicator φ i)_{i ∈ ℕ}` are **i.i.d. Bernoulli(3/4)** and the
i.i.d. Hoeffding inequality applies directly — exactly the route the
file's first draft attempted, but on the correct random variables. As
of **Wave 23C**, the i.i.d.-Bernoulli(3/4) property is a **theorem**
`away_indicator_iIndepFun_iIdentDistrib`, derived from the generic
companion lemma `iIndepFun_iIdentDistrib_uniformIndic_pastDep` (Williams
§9.7) at `c = 3` plus an a.s. transfer for the non-generator-step null
event. Both `centred_away_azuma_tail` and the Hoeffding bound chain are
fully proven theorems (no specialised admissions). -/

/-- The centred "away" indicator `ξ_i − 3/4 = away_indicator φ i Y - 3/4`.
Under `step_measure`, the family `(ξ_i)_{i ∈ ℕ}` is i.i.d. with
`ξ_i ∈ {-3/4, 1/4}`, mean `0`, range half-width `1/2`, hence each `ξ_i`
is sub-Gaussian with parameter `1/4` (Hoeffding's lemma). -/
private def centred_away (φ : ∂F2) (i : ℕ) (Y : ℕ → F2) : ℝ :=
  away_indicator φ i Y - (3/4 : ℝ)

-- `walk_step_in_generating_set_ae` moved up to Wave 33 prereqs section.

/-- The 3-element past-measurable Finset target for the away-indicator
analysis: at vertex `x = X_walk k Y`, this is the set of `F2` generators `z`
that move `x` to a neighbour `y = x * z` with `b_φ(y) = b_φ(x) + 1`.

Construction: take the 3-element vertex Finset `T` from
`busemann_three_plus_neighbours φ x` and translate back to the generator
side via `z = x⁻¹ * y`. -/
private noncomputable def awayGenFinset (φ : ∂F2) (x : F2) : Finset F2 :=
  (Classical.choose (busemann_three_plus_neighbours φ x)).image
    (fun y => x⁻¹ * y)

/-- Cardinality 3 for the past-measurable away target. -/
private lemma awayGenFinset_card (φ : ∂F2) (x : F2) :
    (awayGenFinset φ x).card = 3 := by
  unfold awayGenFinset
  obtain ⟨hcard, _, _⟩ := Classical.choose_spec
    (busemann_three_plus_neighbours φ x)
  rw [Finset.card_image_of_injective _ (fun y₁ y₂ h => by
    -- `x⁻¹ * y₁ = x⁻¹ * y₂ ⇒ y₁ = y₂` by left cancellation.
    exact mul_left_cancel h)]
  exact hcard

/-- The away target lies inside `F2_generating_set`: every neighbour of
`x` is reached via a generator. -/
private lemma awayGenFinset_subset (φ : ∂F2) (x : F2) :
    ↑(awayGenFinset φ x) ⊆ F2_generating_set := by
  intro z hz
  unfold awayGenFinset at hz
  -- `z ∈ T.image (x⁻¹ * ·)` for `T` the spec'd Finset of vertices.
  rcases Finset.mem_coe.mp hz with hmem
  rcases Finset.mem_image.mp hmem with ⟨y, hyT, rfl⟩
  -- `y` is a neighbour of `x` in the Cayley graph by spec of `T`.
  obtain ⟨_, h_T_mem, _⟩ :=
    Classical.choose_spec (busemann_three_plus_neighbours φ x)
  obtain ⟨h_adj, _⟩ := h_T_mem y hyT
  -- Adjacency in the Cayley graph + symmetry of `F2_generating_set` give
  -- `x⁻¹ * y ∈ F2_generating_set`.
  rcases (cayley_graph_adj F2_generating_set x y).mp h_adj with ⟨_, hor⟩
  rcases hor with ⟨z, hzmem, hyeq⟩ | ⟨z, hzmem, hxeq⟩
  · -- `y = x * z`, so `x⁻¹ * y = z ∈ F2_generating_set`.
    rw [hyeq, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hzmem
  · -- `x = y * z`, so `y = x * z⁻¹`, and `z⁻¹ ∈ F2_generating_set` by symmetry.
    have hyz : y = x * z⁻¹ := by
      rw [hxeq]; group
    rw [hyz, ← mul_assoc, inv_mul_cancel, one_mul]
    exact F2_generating_set_symmetric z hzmem

/-- The away target depends only on the past `(Y 0, …, Y (k-1))`,
through `X_walk k Y` (a function of past steps only). -/
private lemma awayGenFinset_past (φ : ∂F2) (k : ℕ) (Y Y' : ℕ → F2)
    (h : ∀ j, j < k → Y j = Y' j) :
    awayGenFinset φ (X_walk k Y) = awayGenFinset φ (X_walk k Y') := by
  have hwalk : X_walk k Y = X_walk k Y' := by
    induction k with
    | zero => simp [X_walk]
    | succ n ih =>
      have hpast : ∀ j, j < n → Y j = Y' j := fun j hj => h j (by omega)
      have hYn : Y n = Y' n := h n (by omega)
      rw [X_walk_succ, X_walk_succ, ih hpast, hYn]
  rw [hwalk]

/-- **Pointwise equivalence (a.s. only).** When `Y k ∈ F2_generating_set`,
`away_indicator φ k Y = 1 ⇔ Y k ∈ awayGenFinset φ (X_walk k Y)`. The
hypothesis is automatic under `step_measure` by
`walk_step_in_generating_set_ae`. -/
private lemma away_indicator_eq_indicator_of_gen
    (φ : ∂F2) (k : ℕ) (Y : ℕ → F2) (hYk : Y k ∈ F2_generating_set) :
    away_indicator φ k Y =
      (if Y k ∈ awayGenFinset φ (X_walk k Y) then (1 : ℝ) else 0) := by
  -- Adjacency `X_walk k Y ∼ X_walk (k+1) Y` from `Y k ∈ F2_generating_set`,
  -- `Y k ≠ 1`, and `cayley_graph_adj_mul`.
  have hne : Y k ≠ 1 := by
    rcases hYk with h | h | h | h
    all_goals
      rw [h]
      intro heq
      first
      | (have := congrArg _root_.FreeGroup.toWord heq
         rw [_root_.FreeGroup.toWord_of, _root_.FreeGroup.toWord_one] at this
         exact List.cons_ne_nil _ _ this)
      | (have heq' : (_root_.FreeGroup.of (0 : Fin 2) : F2) = 1 := by
           rw [← inv_inv (_root_.FreeGroup.of (0 : Fin 2) : F2), heq, inv_one]
         have := congrArg _root_.FreeGroup.toWord heq'
         rw [_root_.FreeGroup.toWord_of, _root_.FreeGroup.toWord_one] at this
         exact List.cons_ne_nil _ _ this)
      | (have heq' : (_root_.FreeGroup.of (1 : Fin 2) : F2) = 1 := by
           rw [← inv_inv (_root_.FreeGroup.of (1 : Fin 2) : F2), heq, inv_one]
         have := congrArg _root_.FreeGroup.toWord heq'
         rw [_root_.FreeGroup.toWord_of, _root_.FreeGroup.toWord_one] at this
         exact List.cons_ne_nil _ _ this)
  have hadj : (cayley_graph F2_generating_set).Adj
      (X_walk k Y) (X_walk (k + 1) Y) := by
    rw [X_walk_succ]
    exact cayley_graph_adj_mul F2_generating_set hYk hne
  -- Spec of `T` from `busemann_three_plus_neighbours φ (X_walk k Y)`.
  set x : F2 := X_walk k Y
  obtain ⟨hcard, h_T_mem, h_T_cover⟩ :=
    Classical.choose_spec (busemann_three_plus_neighbours φ x)
  set T : Finset F2 := Classical.choose (busemann_three_plus_neighbours φ x)
  -- Two cases: Δ_k = -1 (toward) or Δ_k = +1 (away).
  rcases busemann_other_neighbours φ x (X_walk (k + 1) Y) hadj with hdn | hup
  · -- Toward case: `away_indicator = 0`. Need `Y k ∉ awayGenFinset`.
    have hΔ : busemann_incr φ k Y = -1 := by
      unfold busemann_incr; rw [hdn]; ring
    have h_aw : away_indicator φ k Y = 0 := by
      unfold away_indicator; rw [hΔ]; push_cast; norm_num
    rw [h_aw]
    -- Show `Y k ∉ awayGenFinset φ x`. Suppose for contradiction `Y k ∈ awayGenFinset`.
    -- Then `Y k = x⁻¹ * y` for some `y ∈ T`, so `x * Y k = y`, and by spec
    -- `b_φ(y) = b_φ(x) + 1`. But `b_φ(x * Y k) = b_φ(X_walk (k+1) Y) = b_φ(x) - 1`.
    -- These differ, contradiction.
    have : Y k ∉ awayGenFinset φ x := by
      intro hmem
      unfold awayGenFinset at hmem
      rcases Finset.mem_image.mp hmem with ⟨y, hyT, hYk_eq⟩
      have h_xz : X_walk (k + 1) Y = y := by
        rw [X_walk_succ, ← hYk_eq, ← mul_assoc, mul_inv_cancel, one_mul]
      have hb_y : busemann φ y = busemann φ x + 1 := (h_T_mem y hyT).2
      rw [h_xz] at hdn
      -- `b_φ(y) = b_φ(x) - 1` from `hdn`, but `= b_φ(x) + 1` from `hb_y`. Contradiction.
      have h_eq : busemann φ x - 1 = busemann φ x + 1 := by rw [← hdn, hb_y]
      have : (-1 : ℤ) = 1 := by linarith
      exact absurd this (by decide)
    rw [if_neg this]
  · -- Away case: `away_indicator = 1`. Need `Y k ∈ awayGenFinset`.
    have hΔ : busemann_incr φ k Y = 1 := by
      unfold busemann_incr; rw [hup]; ring
    have h_aw : away_indicator φ k Y = 1 := by
      unfold away_indicator; rw [hΔ]; push_cast; norm_num
    rw [h_aw]
    -- Show `Y k ∈ awayGenFinset φ x`. We have `b_φ(x * Y k) = b_φ(x) + 1`.
    -- By `h_T_cover`, `X_walk (k+1) Y` is either at `b - 1` or in `T`.
    -- Since `b_φ(X_walk (k+1) Y) = b + 1 ≠ b - 1`, it's in `T`.
    have h_in_T : X_walk (k + 1) Y ∈ T := by
      rcases h_T_cover (X_walk (k + 1) Y) hadj with hb | hmem
      · -- `b_φ = b - 1` contradicts `b + 1 = b_φ`.
        rw [hb] at hup
        have : busemann φ x - 1 = busemann φ x + 1 := hup
        have : (-1 : ℤ) = 1 := by linarith
        exact absurd this (by decide)
      · exact hmem
    -- Now `Y k = x⁻¹ * (x * Y k) = x⁻¹ * X_walk (k+1) Y`, and the latter is
    -- in `T.image (x⁻¹ * ·) = awayGenFinset φ x`.
    have h_in : Y k ∈ awayGenFinset φ x := by
      unfold awayGenFinset
      apply Finset.mem_image.mpr
      refine ⟨X_walk (k + 1) Y, h_in_T, ?_⟩
      rw [X_walk_succ, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [if_pos h_in]

/-- A.s. equality: `away_indicator φ k = if Y k ∈ awayGenFinset ... then 1 else 0`
under `step_measure`. -/
private lemma away_indicator_aeEq (φ : ∂F2) (k : ℕ) :
    (fun Y => away_indicator φ k Y) =ᵐ[step_measure]
      (fun Y => if Y k ∈ awayGenFinset φ (X_walk k Y) then (1 : ℝ) else 0) := by
  filter_upwards [walk_step_in_generating_set_ae] with Y hY
  exact away_indicator_eq_indicator_of_gen φ k Y (hY k)

/-- **Theorem (Wave 23C, formerly companion axiom).** Mutual independence,
identical distribution, and marginal-mean `3/4` for the "away" indicator
family. Derived from the generic companion axiom
`iIndepFun_iIdentDistrib_uniformIndic_pastDep` at `c = 3` plus an a.s.
transfer for the non-generator-step null event. -/
theorem away_indicator_iIndepFun_iIdentDistrib (φ : ∂F2) :
    iIndepFun (fun i : ℕ => fun Y : ℕ → F2 => away_indicator φ i Y) step_measure
      ∧ (∀ i : ℕ,
          IdentDistrib (away_indicator φ i) (away_indicator φ 0)
            step_measure step_measure)
      ∧ ∫ Y, away_indicator φ 0 Y ∂step_measure = (3/4 : ℝ) := by
  -- Apply the generic axiom to `A k Y := awayGenFinset φ (X_walk k Y)`, `c := 3`.
  have hgen :=
    iIndepFun_iIdentDistrib_uniformIndic_pastDep
      (fun k Y => awayGenFinset φ (X_walk k Y))
      (fun k Y Y' h => awayGenFinset_past φ k Y Y' h)
      (fun k Y => awayGenFinset_subset φ (X_walk k Y))
      3 (fun k Y => awayGenFinset_card φ (X_walk k Y))
  -- The generic family `g k Y = if Y k ∈ awayGenFinset φ (X_walk k Y) then 1 else 0`
  -- is a.s. equal to `away_indicator φ k`.
  set g : ℕ → (ℕ → F2) → ℝ :=
    fun k Y => if Y k ∈ awayGenFinset φ (X_walk k Y) then (1 : ℝ) else 0 with hg_def
  have h_aeEq : ∀ k, (fun Y => away_indicator φ k Y) =ᵐ[step_measure] g k := by
    intro k; exact away_indicator_aeEq φ k
  refine ⟨?_, ?_, ?_⟩
  · -- Mutual independence: transfer via `iIndepFun.congr`.
    have h_indep := hgen.1
    simp only at h_indep
    -- `iIndepFun.congr` requires `g k =ᵐ[step_measure] away_indicator φ k`.
    refine h_indep.congr (fun k => ?_)
    exact (h_aeEq k).symm
  · -- IdentDistrib: transfer each side via `IdentDistrib.of_ae_eq` and `trans`.
    intro i
    have h_id := hgen.2.1 i
    simp only at h_id
    -- `away_indicator φ i =ᵐ g i` and `away_indicator φ 0 =ᵐ g 0`.
    -- AEMeasurable of `g i` from `IdentDistrib`.
    have h_meas_gi : AEMeasurable (g i) step_measure := h_id.aemeasurable_fst
    have h_meas_g0 : AEMeasurable (g 0) step_measure := h_id.aemeasurable_snd
    have h_meas_aw_i : AEMeasurable (away_indicator φ i) step_measure := by
      exact (h_meas_gi.congr (h_aeEq i).symm)
    -- `IdentDistrib (away_indicator φ i) (g i)` via `of_ae_eq`.
    have hi : IdentDistrib (away_indicator φ i) (g i) step_measure step_measure :=
      IdentDistrib.of_ae_eq h_meas_aw_i (h_aeEq i)
    -- `IdentDistrib (g 0) (away_indicator φ 0)` via symmetry of `of_ae_eq`.
    have h0 : IdentDistrib (g 0) (away_indicator φ 0) step_measure step_measure := by
      have h_meas_aw_0 : AEMeasurable (away_indicator φ 0) step_measure :=
        h_meas_g0.congr (h_aeEq 0).symm
      exact (IdentDistrib.of_ae_eq h_meas_aw_0 (h_aeEq 0)).symm
    -- Compose: away_indicator i ~ g i ~ g 0 ~ away_indicator 0.
    exact (hi.trans h_id).trans h0
  · -- Integral: `∫ away_indicator φ 0 = ∫ g 0 = 3/4`.
    have h_int := hgen.2.2
    simp only at h_int
    have h_const : ((3 : ℕ) : ℝ) / 4 = (3/4 : ℝ) := by norm_num
    rw [h_const] at h_int
    -- Transfer via a.s. equality of integrands.
    rw [integral_congr_ae (h_aeEq 0)]
    exact h_int

/-- The mutual-independence half. -/
lemma away_indicator_iIndepFun (φ : ∂F2) :
    iIndepFun (fun i : ℕ => fun Y : ℕ → F2 => away_indicator φ i Y) step_measure :=
  (away_indicator_iIndepFun_iIdentDistrib φ).1

/-- The identical-distribution half. -/
lemma away_indicator_iIdentDistrib (φ : ∂F2) (i : ℕ) :
    IdentDistrib (away_indicator φ i) (away_indicator φ 0)
      step_measure step_measure :=
  (away_indicator_iIndepFun_iIdentDistrib φ).2.1 i

/-- The marginal-mean half of `away_indicator_iIndepFun_iIdentDistrib`:
`E[away_indicator φ 0] = 3/4` (the Bernoulli(3/4) parameter). -/
lemma integral_away_indicator_zero (φ : ∂F2) :
    ∫ Y, away_indicator φ 0 Y ∂step_measure = (3/4 : ℝ) :=
  (away_indicator_iIndepFun_iIdentDistrib φ).2.2

/-! #### Range bound on the away-indicator

We factor out the range bound as a separate lemma. The axiom
`busemann_other_neighbours`, specialised to `x = X_walk i Y` and
`y = X_walk (i+1) Y`, tells us that the increment
`Δ_i = b_φ(X_{i+1}) − b_φ(X_i) ∈ {−1, +1}`, hence
`ξ_i = (Δ_i + 1)/2 ∈ {0, 1}`. This does **not** require any measure-theoretic
hypothesis: it holds pointwise for every `Y` (since consecutive walk positions
differ by a single generator, they are adjacent in the Cayley graph). -/

/-- **Range bound** on the centred "away" indicator: pointwise,
`centred_away φ i Y ∈ [−3/4, 1/4]`, provided the step `Y i` is adjacent to
the walk (i.e. belongs to the generating set). The non-adjacent case is
excluded a.s. by `walk_step_in_generating_set_ae`. -/
private lemma centred_away_mem_Icc_of_adj (φ : ∂F2) (i : ℕ) (Y : ℕ → F2)
    (hadj : (cayley_graph F2_generating_set).Adj (X_walk i Y) (X_walk (i+1) Y)) :
    centred_away φ i Y ∈ Set.Icc (-(3/4 : ℝ)) (1/4 : ℝ) := by
  -- By `busemann_other_neighbours`, `b_φ(X_{i+1}) = b_φ(X_i) ± 1`, hence
  -- `Δ_i ∈ {−1, +1}` and `ξ_i := (Δ_i + 1)/2 ∈ {0, 1}`.
  rcases busemann_other_neighbours φ (X_walk i Y) (X_walk (i+1) Y) hadj with hdn | hup
  · -- Δ_i = −1 ⇒ ξ_i = 0, centred = −3/4
    have hΔ : busemann_incr φ i Y = -1 := by
      unfold busemann_incr
      rw [hdn]; ring
    refine ⟨?_, ?_⟩
    · unfold centred_away away_indicator
      rw [hΔ]; push_cast; norm_num
    · unfold centred_away away_indicator
      rw [hΔ]; push_cast; norm_num
  · -- Δ_i = +1 ⇒ ξ_i = 1, centred = 1/4
    have hΔ : busemann_incr φ i Y = 1 := by
      unfold busemann_incr
      rw [hup]; ring
    refine ⟨?_, ?_⟩
    · unfold centred_away away_indicator
      rw [hΔ]; push_cast; norm_num
    · unfold centred_away away_indicator
      rw [hΔ]; push_cast; norm_num

/-- **Range bound (a.s. version)**: `centred_away φ i Y ∈ [−3/4, 1/4]` for
`step_measure`-almost every `Y`. Follows from `centred_away_mem_Icc_of_adj`
combined with `walk_step_in_generating_set_ae`. -/
private lemma centred_away_mem_Icc_ae (φ : ∂F2) (i : ℕ) :
    ∀ᵐ Y ∂step_measure,
      centred_away φ i Y ∈ Set.Icc (-(3/4 : ℝ)) (1/4 : ℝ) := by
  filter_upwards [walk_step_in_generating_set_ae] with Y hY
  -- `Y i ∈ F2_generating_set` gives adjacency `X_walk i Y ∼ X_walk (i+1) Y`
  -- in the Cayley graph, since `X_walk (i+1) Y = X_walk i Y * Y i`.
  have hYi : Y i ∈ F2_generating_set := hY i
  -- All four generators `{a, b, a⁻¹, b⁻¹}` are non-trivial in `F_2`:
  -- `(FreeGroup.of a).toWord = [(a, true)] ≠ []`, and inverting preserves
  -- non-triviality.
  have hne : Y i ≠ 1 := by
    rcases hYi with h | h | h | h
    · rw [h]
      intro heq
      have := congrArg FreeGroup.toWord heq
      rw [FreeGroup.toWord_of, FreeGroup.toWord_one] at this
      exact List.cons_ne_nil _ _ this
    · rw [h]
      intro heq
      have := congrArg FreeGroup.toWord heq
      rw [FreeGroup.toWord_of, FreeGroup.toWord_one] at this
      exact List.cons_ne_nil _ _ this
    · rw [h]
      intro heq
      have heq' : (FreeGroup.of (0 : Fin 2) : F2) = 1 := by
        rw [← inv_inv (FreeGroup.of (0 : Fin 2) : F2), heq, inv_one]
      have := congrArg FreeGroup.toWord heq'
      rw [FreeGroup.toWord_of, FreeGroup.toWord_one] at this
      exact List.cons_ne_nil _ _ this
    · rw [h]
      intro heq
      have heq' : (FreeGroup.of (1 : Fin 2) : F2) = 1 := by
        rw [← inv_inv (FreeGroup.of (1 : Fin 2) : F2), heq, inv_one]
      have := congrArg FreeGroup.toWord heq'
      rw [FreeGroup.toWord_of, FreeGroup.toWord_one] at this
      exact List.cons_ne_nil _ _ this
  -- `X_walk (i+1) Y = X_walk i Y * Y i`, and `cayley_graph_adj_mul` closes
  -- the adjacency using `Y i ∈ F2_generating_set` and `Y i ≠ 1`.
  have hadj : (cayley_graph F2_generating_set).Adj
      (X_walk i Y) (X_walk (i + 1) Y) := by
    rw [X_walk_succ]
    exact cayley_graph_adj_mul F2_generating_set hYi hne
  exact centred_away_mem_Icc_of_adj φ i Y hadj

/-! **Wave 23B note.** With the i.i.d.-Bernoulli(3/4) property of
`away_indicator` admitted as the single companion axiom
`away_indicator_iIndepFun_iIdentDistrib`, the centred indicator
`centred_away φ i = away_indicator φ i - 3/4` is also i.i.d. (translation
by a constant preserves independence and identical distribution), with
mean `0` and pointwise range `[-3/4, 1/4]` (`centred_away_mem_Icc_ae`).
By Hoeffding's lemma
(`hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`), each `centred_away
φ i` is sub-Gaussian with parameter `((1/4 - (-3/4)) / 2)² = (1/2)² =
1/4`. Mathlib's i.i.d. Hoeffding inequality
(`HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun`) then yields
the one-sided tail bound

```
P(δ ≤ ∑_{i<n} centred_away φ i) ≤ exp(-δ² / (2n · 1/4)),
```

closing `centred_away_azuma_tail` as a theorem (no Azuma plumbing
needed). The reflected tail (`centred_away_azuma_tail_neg`) follows by
applying the same Hoeffding bound to the reflected i.i.d. family
`(- centred_away φ i)`, with range `[-1/4, 3/4]` (same half-width). -/

/-- **AEMeasurability of `away_indicator φ i`.** Direct corollary of the
`IdentDistrib` half of the companion axiom. -/
private lemma aemeasurable_away_indicator (φ : ∂F2) (i : ℕ) :
    AEMeasurable (fun Y : ℕ → F2 => away_indicator φ i Y) step_measure :=
  (away_indicator_iIdentDistrib φ i).aemeasurable_fst

/-- **AEMeasurability of `centred_away φ i`.** Translation of an
`AEMeasurable` random variable by a constant. -/
private lemma aemeasurable_centred_away (φ : ∂F2) (i : ℕ) :
    AEMeasurable (fun Y : ℕ → F2 => centred_away φ i Y) step_measure := by
  unfold centred_away
  exact (aemeasurable_away_indicator φ i).sub_const _

/-- **Sub-Gaussian property of one centred indicator (at index 0).**
Range `[-3/4, 1/4]` a.s. (from `centred_away_mem_Icc_ae`) plus mean `0`
(from `integral_away_indicator_zero`) plus Hoeffding's lemma. -/
private lemma centred_away_subgaussian_zero (φ : ∂F2) :
    HasSubgaussianMGF (centred_away φ 0) ((1/4 : ℝ≥0)) step_measure := by
  -- Range bound at index 0.
  have h_range : ∀ᵐ Y ∂step_measure,
      centred_away φ 0 Y ∈ Set.Icc (-(3/4 : ℝ)) (1/4 : ℝ) :=
    centred_away_mem_Icc_ae φ 0
  -- AEMeasurability of `centred_away φ 0`.
  have h_meas : AEMeasurable (centred_away φ 0) step_measure :=
    aemeasurable_centred_away φ 0
  -- Integral 0 at index 0: `∫ centred_away φ 0 = ∫ away_indicator φ 0 - 3/4 = 0`.
  have h_int : ∫ Y, centred_away φ 0 Y ∂step_measure = 0 := by
    unfold centred_away
    -- `∫ (away_indicator - 3/4) = ∫ away_indicator - 3/4 * (∫ 1) = 3/4 - 3/4 = 0`.
    have h_aw_range : ∀ᵐ Y ∂step_measure,
        away_indicator φ 0 Y ∈ Set.Icc (0 : ℝ) (1 : ℝ) := by
      filter_upwards [h_range] with Y hY
      -- `centred_away φ 0 Y ∈ [-3/4, 1/4]` ⇒ `away_indicator φ 0 Y ∈ [0, 1]`.
      unfold centred_away at hY
      constructor <;> [linarith [hY.1]; linarith [hY.2]]
    have h_aw_int : Integrable (fun Y => away_indicator φ 0 Y) step_measure :=
      Integrable.of_mem_Icc 0 1 (aemeasurable_away_indicator φ 0) h_aw_range
    rw [integral_sub h_aw_int (integrable_const _)]
    rw [integral_away_indicator_zero, integral_const]
    simp
  -- Hoeffding's lemma at index 0.
  have hwitness :=
    hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (μ := step_measure)
      (a := -(3/4 : ℝ)) (b := (1/4 : ℝ)) h_meas h_range h_int
  -- Match the constant `(‖1/4 - (-(3/4))‖₊ / 2)^2 = 1/4`.
  have hconst : ((‖(1/4 : ℝ) - -(3/4 : ℝ)‖₊ / 2) ^ 2 : ℝ≥0) = (1/4 : ℝ≥0) := by
    have : (1/4 : ℝ) - -(3/4 : ℝ) = 1 := by norm_num
    rw [this]
    -- `‖(1 : ℝ)‖₊ = 1`, then `(1/2)^2 = 1/4`.
    rw [show ‖(1 : ℝ)‖₊ = 1 by simp]
    norm_num
  rw [hconst] at hwitness
  exact hwitness

/-- **Sub-Gaussian property of one centred indicator (general `i`).**
Transferred from `centred_away_subgaussian_zero` via the identical-
distribution half of the companion axiom. -/
private lemma centred_away_subgaussian (φ : ∂F2) (i : ℕ) :
    HasSubgaussianMGF (centred_away φ i) ((1/4 : ℝ≥0)) step_measure := by
  -- The two random variables `centred_away φ 0` and `centred_away φ i`
  -- are identically distributed, since `away_indicator φ 0` and
  -- `away_indicator φ i` are.
  have h_id : IdentDistrib (centred_away φ 0) (centred_away φ i)
      step_measure step_measure := by
    -- `centred_away φ k = (· - 3/4) ∘ away_indicator φ k`.
    have h_aw : IdentDistrib (away_indicator φ i) (away_indicator φ 0)
        step_measure step_measure := away_indicator_iIdentDistrib φ i
    have := h_aw.symm.comp (u := fun x : ℝ => x - (3/4 : ℝ))
      (measurable_sub_const _)
    -- `(fun x => x - 3/4) ∘ away_indicator φ k = centred_away φ k` (rfl).
    convert this using 1
  exact (centred_away_subgaussian_zero φ).congr_identDistrib h_id

/-- One-sided tail bound for the sum of centred away-indicators
(formerly axiom `centred_away_azuma_tail`).

**Proof.** By the i.i.d.-Bernoulli(3/4) companion axiom
`away_indicator_iIndepFun_iIdentDistrib`, the family `(centred_away φ i)`
is mutually independent, identically distributed with marginal range
`[-3/4, 1/4]` and mean `0`. By Hoeffding's lemma each `centred_away φ i`
is sub-Gaussian with parameter `1/4`. Apply Mathlib's i.i.d. Hoeffding
`HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun`. -/
theorem centred_away_azuma_tail (φ : ∂F2) (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (step_measure {Y | δ ≤ ∑ i ∈ Finset.range n, centred_away φ i Y}).toReal
      ≤ Real.exp (-δ ^ 2 / (2 * n * (1/4 : ℝ))) := by
  -- Mutual independence of the centred family from independence of the
  -- raw family, by composing with `(· - 3/4)`.
  have h_indep_centred :
      iIndepFun (fun i : ℕ => fun Y : ℕ → F2 => centred_away φ i Y) step_measure := by
    have h_raw := away_indicator_iIndepFun φ
    have h_meas : ∀ i : ℕ, Measurable (fun x : ℝ => x - (3/4 : ℝ)) :=
      fun _ => measurable_sub_const _
    -- `centred_away φ i = (· - 3/4) ∘ away_indicator φ i`.
    have h_eq :
        (fun i : ℕ => fun Y : ℕ → F2 => centred_away φ i Y)
          = fun i : ℕ => (fun x : ℝ => x - (3/4 : ℝ)) ∘
              (fun Y : ℕ → F2 => away_indicator φ i Y) := by
      funext i Y; rfl
    rw [h_eq]
    exact h_raw.comp (fun _ => fun x => x - 3/4) h_meas
  have h_subG : ∀ i < n,
      HasSubgaussianMGF (centred_away φ i) ((1/4 : ℝ≥0)) step_measure :=
    fun i _ => centred_away_subgaussian φ i
  -- Apply the i.i.d. Hoeffding inequality.
  have h := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun
    (μ := step_measure) (X := fun i : ℕ => fun Y : ℕ → F2 => centred_away φ i Y)
    h_indep_centred (c := (1/4 : ℝ≥0)) (n := n) h_subG hδ
  -- Convert `μ.real` to `(μ ...).toReal` and the `c : ℝ≥0` to its `ℝ` cast.
  have hcast : ((1/4 : ℝ≥0) : ℝ) = (1/4 : ℝ) := by
    push_cast; ring
  simpa [Measure.real, hcast] using h

/-- Reflected one-sided tail bound (formerly axiom
`centred_away_azuma_tail_neg`). Same argument applied to `-centred_away`,
which has range `[-1/4, 3/4]` (same half-width `1/2`, hence same
sub-Gaussian parameter `1/4`) and is also i.i.d. -/
theorem centred_away_azuma_tail_neg (φ : ∂F2) (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (step_measure {Y | δ ≤ -(∑ i ∈ Finset.range n, centred_away φ i Y)}).toReal
      ≤ Real.exp (-δ ^ 2 / (2 * n * (1/4 : ℝ))) := by
  -- Mutual independence of `(- centred_away φ i)`.
  have h_indep_centred :
      iIndepFun (fun i : ℕ => fun Y : ℕ → F2 => centred_away φ i Y) step_measure := by
    have h_raw := away_indicator_iIndepFun φ
    have h_meas : ∀ i : ℕ, Measurable (fun x : ℝ => x - (3/4 : ℝ)) :=
      fun _ => measurable_sub_const _
    have h_eq :
        (fun i : ℕ => fun Y : ℕ → F2 => centred_away φ i Y)
          = fun i : ℕ => (fun x : ℝ => x - (3/4 : ℝ)) ∘
              (fun Y : ℕ → F2 => away_indicator φ i Y) := by
      funext i Y; rfl
    rw [h_eq]
    exact h_raw.comp (fun _ => fun x => x - 3/4) h_meas
  have h_indep_neg :
      iIndepFun (fun i : ℕ => fun Y : ℕ → F2 => -(centred_away φ i Y)) step_measure := by
    have h_meas : ∀ i : ℕ, Measurable (fun x : ℝ => -x) :=
      fun _ => measurable_neg
    have h_eq :
        (fun i : ℕ => fun Y : ℕ → F2 => -(centred_away φ i Y))
          = fun i : ℕ => (fun x : ℝ => -x) ∘
              (fun Y : ℕ → F2 => centred_away φ i Y) := by
      funext i Y; rfl
    rw [h_eq]
    exact h_indep_centred.comp (fun _ => fun x => -x) h_meas
  have h_subG_neg : ∀ i < n,
      HasSubgaussianMGF (fun Y : ℕ → F2 => -(centred_away φ i Y))
        ((1/4 : ℝ≥0)) step_measure :=
    fun i _ => (centred_away_subgaussian φ i).neg
  -- Apply the i.i.d. Hoeffding inequality to `-centred_away`.
  have h := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun
    (μ := step_measure) (X := fun i : ℕ => fun Y : ℕ → F2 => -(centred_away φ i Y))
    h_indep_neg (c := (1/4 : ℝ≥0)) (n := n) h_subG_neg hδ
  -- Rewrite the event: `∑ -(centred_away ...) = -(∑ centred_away ...)`.
  have h_event_eq :
      {Y | δ ≤ ∑ i ∈ Finset.range n, -(centred_away φ i Y)}
        = {Y | δ ≤ -(∑ i ∈ Finset.range n, centred_away φ i Y)} := by
    ext Y
    simp [Finset.sum_neg_distrib]
  rw [h_event_eq] at h
  have hcast : ((1/4 : ℝ≥0) : ℝ) = (1/4 : ℝ) := by
    push_cast; ring
  simpa [Measure.real, hcast] using h

/-- Algebraic rewrite: `b_φ(X_n)/n − 1/2 = (2/n) · ∑ i < n, (ξ_i − 3/4)`
whenever `n > 0`. -/
private lemma busemann_ratio_eq_two_sum_centred
    (φ : ∂F2) (n : ℕ) (hn : 0 < n) (Y : ℕ → F2) :
    (busemann φ (X_walk n Y) : ℝ) / n - (1/2 : ℝ)
      = (2 / n) * ∑ i ∈ Finset.range n, centred_away φ i Y := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h_bus : (busemann φ (X_walk n Y) : ℝ) = 2 * away_sum φ n Y - n :=
    busemann_walk_eq_two_sum_sub φ n Y
  have h_sum_split :
      ∑ i ∈ Finset.range n, centred_away φ i Y
        = away_sum φ n Y - (3/4 : ℝ) * n := by
    unfold centred_away away_sum
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [h_bus, h_sum_split]
  field_simp
  ring

/-- **Q42 (Hoeffding bound, via Azuma)**. For a fixed boundary point
`φ ∈ ∂F_2`,
`P(|b_φ(X_n) / n − 1/2| ≥ ε) ≤ 2 · exp(−n ε² / 2)`.

This follows from the Azuma-Hoeffding tail bound
`centred_away_azuma_tail` (and its reflected companion
`centred_away_azuma_tail_neg`) applied to the centred indicators
`ξ_i − 3/4`, which form a bounded martingale-difference sequence with
respect to the natural filtration of the walk (range `[-3/4, 1/4]`,
conditional mean `0`).

**Status (Wave 16)**: the algebraic reduction from
`|b_φ(X_n)/n − 1/2| ≥ ε` to `|∑ i < n, (ξ_i − 3/4)| ≥ nε/2` and the
union bound on the two tails are proved in full. The probabilistic
input — the Azuma tail bound itself — is admitted as a companion axiom
matching the pattern of the Busemann structural axioms. The earlier
Wave 9D chain used Hoeffding-for-iid which is **mathematically incorrect**
(the centred indicators are not i.i.d. — see the module docstring,
errata note E3). -/
theorem busemann_walk_hoeffding (φ : ∂F2) (n : ℕ) (hn : 0 < n)
    (ε : ℝ) (hε : 0 < ε) :
    (step_measure {Y | ε ≤ |(busemann φ (X_walk n Y) : ℝ) / n - (1/2 : ℝ)|}).toReal
      ≤ 2 * Real.exp (- n * ε^2 / 2) := by
  -- Abbreviations.
  set S : (ℕ → F2) → ℝ := fun Y => ∑ i ∈ Finset.range n, centred_away φ i Y with hS_def
  have hn_real : (0 : ℝ) < n := by exact_mod_cast hn
  -- Step 1: rewrite the event as `|S Y| ≥ n ε / 2`.
  have h_event_eq :
      {Y | ε ≤ |(busemann φ (X_walk n Y) : ℝ) / n - (1/2 : ℝ)|}
        = {Y | (n : ℝ) * ε / 2 ≤ |S Y|} := by
    ext Y
    simp only [Set.mem_setOf_eq]
    rw [busemann_ratio_eq_two_sum_centred φ n hn Y]
    -- `|(2/n) * S Y| = (2/n) * |S Y|` since `2/n > 0`.
    have h2n_pos : (0 : ℝ) < 2 / n := div_pos (by norm_num) hn_real
    rw [abs_mul, abs_of_pos h2n_pos]
    -- Now: `ε ≤ (2/n) * |S Y|  ↔  n*ε/2 ≤ |S Y|`.
    constructor
    · intro h
      -- Multiply both sides by `n/2 > 0`.
      have hn2_pos : (0 : ℝ) < n / 2 := by positivity
      have hmul := mul_le_mul_of_nonneg_left h hn2_pos.le
      have h_simpl_rhs : (n : ℝ) / 2 * ((2 / n) * |S Y|) = |S Y| := by
        field_simp
      have h_simpl_lhs : (n : ℝ) / 2 * ε = n * ε / 2 := by ring
      rw [h_simpl_rhs, h_simpl_lhs] at hmul
      exact hmul
    · intro h
      -- Multiply both sides of `n*ε/2 ≤ |S Y|` by `2/n > 0`.
      have hmul := mul_le_mul_of_nonneg_left h h2n_pos.le
      have h_simpl_lhs : (2 / n) * ((n : ℝ) * ε / 2) = ε := by
        field_simp
      rw [h_simpl_lhs] at hmul
      exact hmul
  rw [h_event_eq]
  -- Step 2: split `|S Y| ≥ δ` into the two one-sided events.
  set δ : ℝ := (n : ℝ) * ε / 2 with hδ_def
  have hδ_nn : 0 ≤ δ := by positivity
  have h_split :
      {Y | δ ≤ |S Y|} ⊆ {Y | δ ≤ S Y} ∪ {Y | δ ≤ -(S Y)} := by
    intro Y hY
    simp only [Set.mem_setOf_eq] at hY
    rcases le_or_gt 0 (S Y) with hsign | hsign
    · left
      simp only [Set.mem_setOf_eq]
      rwa [abs_of_nonneg hsign] at hY
    · right
      simp only [Set.mem_setOf_eq]
      rwa [abs_of_neg hsign] at hY
  -- Step 3: Azuma tail bounds for each one-sided event, directly from the
  -- companion axioms.
  have h_right :
      (step_measure {Y | δ ≤ S Y}).toReal
        ≤ Real.exp (-δ ^ 2 / (2 * n * (1/4 : ℝ))) := by
    simpa [hS_def] using centred_away_azuma_tail φ n hδ_nn
  have h_left :
      (step_measure {Y | δ ≤ -(S Y)}).toReal
        ≤ Real.exp (-δ ^ 2 / (2 * n * (1/4 : ℝ))) := by
    simpa [hS_def] using centred_away_azuma_tail_neg φ n hδ_nn
  -- Step 4: combine via the union bound.
  have h_bound_sum :
      (step_measure {Y | δ ≤ S Y}).toReal + (step_measure {Y | δ ≤ -(S Y)}).toReal
        ≤ 2 * Real.exp (-δ ^ 2 / (2 * n * (1/4 : ℝ))) := by
    linarith
  -- Simplify the exponent: `−δ² / (2n · (1/4)) = −nε²/2` (using `δ = nε/2`).
  have h_exp_eq :
      Real.exp (-δ ^ 2 / (2 * n * (1/4 : ℝ)))
        = Real.exp (- n * ε^2 / 2) := by
    congr 1
    rw [hδ_def]
    field_simp
    ring
  rw [h_exp_eq] at h_bound_sum
  -- Transfer from `Measure.real` to `.toReal` and apply the union bound.
  have h_union : step_measure.real {Y | δ ≤ |S Y|}
      ≤ step_measure.real ({Y | δ ≤ S Y} ∪ {Y | δ ≤ -(S Y)}) :=
    measureReal_mono (μ := step_measure) h_split (measure_ne_top _ _)
  have h_union2 :
      step_measure.real ({Y | δ ≤ S Y} ∪ {Y | δ ≤ -(S Y)})
        ≤ step_measure.real {Y | δ ≤ S Y} + step_measure.real {Y | δ ≤ -(S Y)} :=
    measureReal_union_le _ _
  have h_final : step_measure.real {Y | δ ≤ |S Y|}
      ≤ 2 * Real.exp (- n * ε^2 / 2) :=
    (h_union.trans h_union2).trans h_bound_sum
  -- The target uses `.toReal`, which equals `Measure.real` by definition.
  simpa [Measure.real, hδ_def] using h_final

/-! ### Q43 — Almost-sure rate of escape -/

/-- The Cayley graph of `F_2` with respect to the symmetric generating set
`F2_generating_set = {a, b, a⁻¹, b⁻¹}`. We reuse the generic `cayley_graph`
construction from `EnsX2026.Cayley.Growth`. -/
def F2_cayley : SimpleGraph F2 :=
  EnsX2026.Cayley.cayley_graph F2_generating_set

/-- The word-length (tree distance from the identity) of an element of
`F_2`. -/
def word_length (x : F2) : ℕ := F2_cayley.dist 1 x

/-! #### A canonical boundary point `φ₀ = (a, a, a, …)`

For the Borel–Cantelli reduction we fix a specific boundary point
`φ₀ ∈ ∂F_2`: the infinite word in the `a` direction. This is a valid
element of `F2_boundary` because two consecutive letters `(0, true), (0, true)`
do not cancel (they are the same letter, and cancellation requires the same
generator with opposite orientation). -/

/-- The canonical boundary point `φ₀ = (aaa…)`. -/
def phi_zero : ∂F2 :=
  ⟨fun _ : ℕ => ((0 : Fin 2), true), by
    intro n
    -- `NonCancellation (0, true) (0, true) = (0 ≠ 0 ∨ true = true)`;
    -- the right disjunct holds.
    right; rfl⟩

/-! #### Borel–Cantelli reduction on the Busemann ratio

We show that for the fixed boundary point `φ₀`, the sequence of bad events
`B_n := {Y | n^{−1/3} ≤ |b_{φ₀}(X_n)/n − 1/2|}` has summable measure under
`step_measure`. The first Borel–Cantelli lemma then yields that a.s. only
finitely many of the `B_n` occur, which is equivalent to
`b_{φ₀}(X_n Y)/n → 1/2`. -/

/-- The bad event at time `n`: the Busemann ratio deviates from `1/2` by
more than the shrinking tolerance `n^{−1/3}`. -/
private def bad_busemann_event (n : ℕ) : Set (ℕ → F2) :=
  {Y | (n : ℝ)^(-(1/3 : ℝ)) ≤
        |(busemann phi_zero (X_walk n Y) : ℝ) / n - (1/2 : ℝ)|}

/-- **Summability of the analytic majorant.** The sequence
`n ↦ 2 · exp(−n^{1/3}/2)` is summable. The exponential decay in `n^{1/3}`
dominates any polynomial decay, so it is eventually bounded by `1/n^2`,
which is summable by the `p`-series test with `p = 2`. We prove this by
showing `n^2 · exp(−n^{1/3}/2) → 0` (composition of `u^6 · exp(−u/2) → 0`
at `+∞` with `u = n^{1/3} → +∞`), deducing the `IsBigO` with `1/(n+1)^2`,
and applying `summable_of_isBigO_nat`. -/
private lemma exp_neg_cube_root_half_summable :
    Summable (fun n : ℕ => (2 : ℝ) * Real.exp (-((n : ℝ) ^ ((1:ℝ)/3)) / 2)) := by
  -- Step 1: polynomial-times-exponential tends to 0 at ∞:
  -- `u ↦ u^6 · exp(-(1/2) · u) → 0` as `u → +∞`.
  have h_poly_exp :
      Tendsto (fun u : ℝ => u ^ (6 : ℝ) * Real.exp (-(1/2 : ℝ) * u))
        atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 6 (1/2) (by norm_num)
  -- Step 2: `(n : ℝ)^(1/3) → +∞` as `n → +∞`.
  have h_cube_root :
      Tendsto (fun n : ℕ => (n : ℝ) ^ ((1:ℝ)/3)) atTop atTop := by
    have h_tt : Tendsto (fun x : ℝ => x ^ ((1:ℝ)/3)) atTop atTop :=
      tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/3)
    exact h_tt.comp tendsto_natCast_atTop_atTop
  -- Step 3: compose — `(n^(1/3))^6 * exp(-(1/2) * n^(1/3)) → 0`.
  have h_comp := h_poly_exp.comp h_cube_root
  -- Simplify: `(n^(1/3))^6 = n^2` and `-(1/2) * n^(1/3) = -n^(1/3)/2`.
  have h_tendsto :
      Tendsto (fun n : ℕ =>
          (n : ℝ) ^ 2 * Real.exp (-((n : ℝ) ^ ((1:ℝ)/3)) / 2))
        atTop (𝓝 0) := by
    refine h_comp.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hn_nn : (0 : ℝ) ≤ (n : ℝ) := hn_pos.le
    -- `(n^(1/3))^6 = n^((1/3)*6) = n^2`.
    have h_rpow : ((n : ℝ) ^ ((1:ℝ)/3)) ^ (6 : ℝ) = (n : ℝ) ^ 2 := by
      rw [← Real.rpow_mul hn_nn]
      rw [show ((1:ℝ)/3) * 6 = (2 : ℝ) by norm_num]
      rw [show ((n : ℝ) ^ (2 : ℝ)) = (n : ℝ) ^ (2 : ℕ) by
        rw [← Real.rpow_natCast (n : ℝ) 2]; norm_num]
    have h_neg : -(1/2 : ℝ) * ((n : ℝ) ^ ((1:ℝ)/3))
        = -((n : ℝ) ^ ((1:ℝ)/3)) / 2 := by ring
    simp only [Function.comp_apply]
    rw [h_rpow, h_neg]
  -- Step 4: from `n^2 * exp(...) → 0`, eventually `n^2 * exp(...) ≤ 1`, so
  -- `exp(...) ≤ 1/n^2`. In `IsBigO` form: `exp(...) =O[atTop] 1/(n+1)^2`.
  have h_bigO :
      (fun n : ℕ => (2 : ℝ) * Real.exp (-((n : ℝ) ^ ((1:ℝ)/3)) / 2))
        =O[atTop] (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
    -- Sufficient: boundedness of the ratio `(n+1)^2 * 2 * exp(...)`.
    -- We know `n^2 * exp(...) → 0` so `n^2 * exp(...) ≤ 1` eventually.
    -- Then `(n+1)^2 * exp(...) ≤ 4 n^2 * exp(...) ≤ 4` eventually (for n ≥ 1).
    -- Hence `2 * exp(...) ≤ 8/(n+1)^2`.
    apply Asymptotics.IsBigO.of_bound 8
    -- Need: ∀ᶠ n, |2 * exp(...)| ≤ 8 * |1/(n+1)^2|.
    have h_event : ∀ᶠ n : ℕ in atTop,
        (n : ℝ) ^ 2 * Real.exp (-((n : ℝ) ^ ((1:ℝ)/3)) / 2) ≤ 1 :=
      h_tendsto.eventually_le_const (by norm_num : (0:ℝ) < 1)
    filter_upwards [h_event, eventually_ge_atTop 1] with n h_le hn
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hnp1_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have hexp_nn : 0 ≤ Real.exp (-((n : ℝ) ^ ((1:ℝ)/3)) / 2) :=
      (Real.exp_pos _).le
    have h_norm_lhs :
        ‖(2 : ℝ) * Real.exp (-((n : ℝ) ^ ((1:ℝ)/3)) / 2)‖
          = 2 * Real.exp (-((n : ℝ) ^ ((1:ℝ)/3)) / 2) := by
      rw [Real.norm_eq_abs, abs_of_nonneg]; positivity
    have h_norm_rhs :
        ‖(1 : ℝ) / ((n : ℝ) + 1) ^ 2‖ = 1 / ((n : ℝ) + 1) ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg]; positivity
    rw [h_norm_lhs, h_norm_rhs]
    -- Goal: 2 * exp(...) ≤ 8 * (1 / (n+1)^2),
    -- i.e., 2 * (n+1)^2 * exp(...) ≤ 8.
    -- We have n^2 * exp(...) ≤ 1, so (n+1)^2 * exp(...) ≤ 4 * n^2 * exp(...) ≤ 4
    -- (using (n+1)^2 ≤ 4 n^2 for n ≥ 1), and multiplying by 2 gives ≤ 8.
    have hn_one : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h_np1_sq_le : ((n : ℝ) + 1) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by
      have h1 : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
      have h_sq : ((n : ℝ) + 1) ^ 2 ≤ (2 * (n : ℝ)) ^ 2 := by
        apply sq_le_sq' <;> nlinarith
      calc ((n : ℝ) + 1) ^ 2 ≤ (2 * (n : ℝ)) ^ 2 := h_sq
        _ = 4 * (n : ℝ) ^ 2 := by ring
    have h_key :
        ((n : ℝ) + 1) ^ 2
          * Real.exp (-((n : ℝ) ^ ((1:ℝ)/3)) / 2) ≤ 4 := by
      calc ((n : ℝ) + 1) ^ 2
              * Real.exp (-((n : ℝ) ^ ((1:ℝ)/3)) / 2)
          ≤ 4 * (n : ℝ) ^ 2
              * Real.exp (-((n : ℝ) ^ ((1:ℝ)/3)) / 2) := by
                apply mul_le_mul_of_nonneg_right h_np1_sq_le hexp_nn
        _ = 4 * ((n : ℝ) ^ 2
              * Real.exp (-((n : ℝ) ^ ((1:ℝ)/3)) / 2)) := by ring
        _ ≤ 4 * 1 := by
              apply mul_le_mul_of_nonneg_left h_le
              norm_num
        _ = 4 := by norm_num
    -- From h_key: `(n+1)^2 * exp(...) ≤ 4`. Rearrange.
    have h_sq_pos : 0 < ((n : ℝ) + 1) ^ 2 := by positivity
    -- Goal: 2 * exp(...) ≤ 8 * (1 / (n+1)^2) = 8/(n+1)^2.
    rw [show (8 : ℝ) * (1 / ((n : ℝ) + 1) ^ 2) = 8 / ((n : ℝ) + 1) ^ 2 by ring]
    rw [le_div_iff₀ h_sq_pos]
    have h_rearr :
        2 * Real.exp (-((n : ℝ) ^ ((1:ℝ)/3)) / 2) * ((n : ℝ) + 1) ^ 2
          = 2 * (((n : ℝ) + 1) ^ 2
              * Real.exp (-((n : ℝ) ^ ((1:ℝ)/3)) / 2)) := by ring
    rw [h_rearr]
    linarith
  -- Step 5: `Summable (1 / (n+1)^2)` via shift of the `p=2` series.
  have h_maj_summable : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
    have hp : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℕ) : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num : (1 : ℕ) < 2)
    have h_shift : Summable (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ)) : ℝ) ^ 2) :=
      (summable_nat_add_iff 1).mpr hp
    refine h_shift.congr (fun n => ?_)
    push_cast
    ring
  -- Step 6: Combine via `summable_of_isBigO_nat`.
  exact summable_of_isBigO_nat h_maj_summable h_bigO

/-- **Summability of the bad events.** For `n ≥ 1`,
`step_measure(B_n) ≤ 2 · exp(−n^{1/3}/2)`, which is summable (Hoeffding
with `ε = n^{−1/3}` gives `exp(−n · n^{−2/3}/2) = exp(−n^{1/3}/2)`, and
exponential decay in `n^{1/3}` dominates any power of `n`). Proof uses
`busemann_walk_hoeffding` applied to `φ₀` with `ε := n^{−1/3}` plus the
summability of the majorant (`exp_neg_cube_root_half_summable`). -/
private lemma bad_busemann_event_summable :
    Summable (fun n : ℕ => (step_measure (bad_busemann_event n)).toReal) := by
  -- Majorant: `g n = 2 * exp(-n^(1/3)/2)` for `n ≥ 1`, and some large
  -- constant for `n = 0` (one term doesn't affect summability).
  -- We redefine `g n := 2 * exp(-n^(1/3)/2)`, which is summable by
  -- `exp_neg_cube_root_half_summable`, and show the measure is bounded
  -- pointwise by `g n` for `n ≥ 1`. Since the first finitely many terms
  -- do not affect summability, we can use `summable_nat_add_iff 1`.
  set g : ℕ → ℝ :=
    fun n => (2 : ℝ) * Real.exp (-((n : ℝ) ^ ((1:ℝ)/3)) / 2) with hg_def
  have h_g_summable : Summable g := exp_neg_cube_root_half_summable
  -- Pointwise bound: for n ≥ 1, the measure is ≤ g n.
  -- Apply `busemann_walk_hoeffding` with φ = phi_zero, ε = n^(-1/3).
  have h_bound : ∀ n : ℕ, 1 ≤ n →
      (step_measure (bad_busemann_event n)).toReal ≤ g n := by
    intro n hn
    have hn_pos : 0 < n := hn
    have hn_real : (0 : ℝ) < n := by exact_mod_cast hn_pos
    have h_eps_pos : (0 : ℝ) < (n : ℝ) ^ (-(1/3 : ℝ)) := by
      exact Real.rpow_pos_of_pos hn_real _
    -- Hoeffding at ε = n^(-1/3).
    have h_hoeff :=
      busemann_walk_hoeffding phi_zero n hn_pos
        ((n : ℝ) ^ (-(1/3 : ℝ))) h_eps_pos
    -- Simplify the event and the exponent.
    -- `bad_busemann_event n = {Y | n^(-1/3) ≤ |...|}`.
    -- Exponent: `-n * (n^(-1/3))^2 / 2 = -n^(1/3)/2`.
    have h_exp_simp :
        (-(n : ℝ) * ((n : ℝ) ^ (-(1/3 : ℝ))) ^ 2 / 2)
          = -((n : ℝ) ^ ((1:ℝ)/3)) / 2 := by
      have hnn : (0 : ℝ) ≤ (n : ℝ) := hn_real.le
      -- (n^(-1/3))^2 = n^(-2/3)
      have h1 : ((n : ℝ) ^ (-(1/3 : ℝ))) ^ 2 = (n : ℝ) ^ (-(2/3 : ℝ)) := by
        rw [← Real.rpow_natCast ((n : ℝ) ^ (-(1/3 : ℝ))) 2,
            ← Real.rpow_mul hnn]
        congr 1
        norm_num
      -- n * n^(-2/3) = n^(1/3)
      have h2 : (n : ℝ) * (n : ℝ) ^ (-(2/3 : ℝ)) = (n : ℝ) ^ ((1:ℝ)/3) := by
        rw [show ((1:ℝ)/3) = 1 + (-(2/3 : ℝ)) from by ring]
        rw [Real.rpow_add hn_real]
        simp [Real.rpow_one]
      rw [h1]
      -- Goal: -↑n * ↑n^(-2/3) / 2 = -↑n^(1/3) / 2
      have h3 : -(n : ℝ) * (n : ℝ) ^ (-(2/3 : ℝ)) = -((n : ℝ) ^ ((1:ℝ)/3)) := by
        rw [show -(n : ℝ) * (n : ℝ) ^ (-(2/3 : ℝ))
              = -((n : ℝ) * (n : ℝ) ^ (-(2/3 : ℝ))) by ring, h2]
      rw [h3]
    rw [show bad_busemann_event n
          = {Y | (n : ℝ) ^ (-(1/3 : ℝ))
              ≤ |(busemann phi_zero (X_walk n Y) : ℝ) / n - (1/2 : ℝ)|}
        from rfl]
    calc (step_measure {Y | (n : ℝ) ^ (-(1/3 : ℝ))
            ≤ |(busemann phi_zero (X_walk n Y) : ℝ) / n - (1/2 : ℝ)|}).toReal
        ≤ 2 * Real.exp (-(n : ℝ) * ((n : ℝ) ^ (-(1/3 : ℝ))) ^ 2 / 2) := h_hoeff
      _ = 2 * Real.exp (-((n : ℝ) ^ ((1:ℝ)/3)) / 2) := by rw [h_exp_simp]
      _ = g n := rfl
  -- Apply summability via splitting off the first term.
  -- Sufficient: the shifted series (from n=1) is summable.
  apply (summable_nat_add_iff (f := fun n : ℕ =>
      (step_measure (bad_busemann_event n)).toReal) 1).mp
  -- Now show: Summable (fun n : ℕ => (step_measure (bad_busemann_event (n+1))).toReal).
  -- Compare to (fun n => g (n+1)), using that g ≥ measure eventually.
  apply Summable.of_nonneg_of_le
    (g := fun n : ℕ => (step_measure (bad_busemann_event (n+1))).toReal)
    (f := fun n : ℕ => g (n + 1))
  · intro n; exact ENNReal.toReal_nonneg
  · intro n
    exact h_bound (n + 1) (Nat.succ_le_succ (Nat.zero_le _))
  · exact (summable_nat_add_iff (f := g) 1).mpr h_g_summable

/-- **Borel–Cantelli step.** Applying
`MeasureTheory.ae_eventually_notMem` to the summable bad events yields
that for `step_measure`-a.e. `Y`, eventually `Y ∉ B_n`, i.e. eventually
`|b_{φ₀}(X_n)/n − 1/2| < n^{−1/3}`, which forces
`b_{φ₀}(X_n Y)/n → 1/2`. -/
lemma busemann_walk_ratio_ae_tendsto :
    ∀ᵐ Y ∂step_measure,
      Tendsto (fun n : ℕ => (busemann phi_zero (X_walk n Y) : ℝ) / n)
        atTop (𝓝 (1/2 : ℝ)) := by
  -- Step 1: summability in `ℝ≥0∞` follows from the real summability plus
  -- the fact that each `step_measure (bad_busemann_event n) ≤ 1 ≠ ⊤` (since
  -- `step_measure` is a probability measure). We rewrite each term as
  -- `ENNReal.ofReal ((...).toReal)` and apply `Summable.tsum_ofReal_ne_top`.
  have hsum_ennreal :
      (∑' n : ℕ, step_measure (bad_busemann_event n)) ≠ ⊤ := by
    have h_ne_top : ∀ n : ℕ, step_measure (bad_busemann_event n) ≠ ⊤ :=
      fun n => measure_ne_top _ _
    have h_eq : ∀ n : ℕ,
        step_measure (bad_busemann_event n)
          = ENNReal.ofReal ((step_measure (bad_busemann_event n)).toReal) :=
      fun n => (ENNReal.ofReal_toReal (h_ne_top n)).symm
    rw [tsum_congr h_eq]
    exact bad_busemann_event_summable.tsum_ofReal_ne_top
  -- Step 2: first Borel–Cantelli gives eventual `Y ∉ B_n` a.s.
  have h_bc : ∀ᵐ Y ∂step_measure, ∀ᶠ n in atTop, Y ∉ bad_busemann_event n :=
    MeasureTheory.ae_eventually_notMem hsum_ennreal
  -- Step 3: eventual `|b_{φ₀}(X_n)/n − 1/2| < n^{−1/3}` and `n^{−1/3} → 0`
  -- yields the stated limit via a squeeze / `Metric.tendsto_nhds` argument.
  filter_upwards [h_bc] with Y hY
  -- From `∀ᶠ n in atTop, |b_{φ₀}(X_n Y)/n − 1/2| < n^{-1/3}` and the fact
  -- that `n^{-1/3} → 0` as `n → ∞`, conclude the limit via the squeeze
  -- theorem applied to the envelopes `1/2 ± n^(-1/3)`.
  -- Step A: translate the set-membership into an analytic inequality.
  have hY' : ∀ᶠ n : ℕ in atTop,
      |(busemann phi_zero (X_walk n Y) : ℝ) / n - (1/2 : ℝ)|
        < (n : ℝ) ^ (-(1/3 : ℝ)) := by
    filter_upwards [hY] with n hn
    -- `hn : Y ∉ bad_busemann_event n` unfolds to `¬ (n^(-1/3) ≤ |...|)`.
    change ¬ ((n : ℝ) ^ (-(1/3 : ℝ))
              ≤ |(busemann phi_zero (X_walk n Y) : ℝ) / n - (1/2 : ℝ)|) at hn
    exact lt_of_not_ge hn
  -- Step B: `(n : ℝ)^(-1/3) → 0` as `n → ∞` (in ℕ).
  have h_rpow_tendsto :
      Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1/3 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/3)).comp
      tendsto_natCast_atTop_atTop
  -- Step C: build the two envelopes `1/2 ± n^(-1/3)`, both tending to `1/2`.
  have h_upper :
      Tendsto (fun n : ℕ => (1/2 : ℝ) + (n : ℝ) ^ (-(1/3 : ℝ)))
        atTop (𝓝 (1/2 : ℝ)) := by
    have := h_rpow_tendsto.const_add (1/2 : ℝ)
    simpa using this
  have h_lower :
      Tendsto (fun n : ℕ => (1/2 : ℝ) - (n : ℝ) ^ (-(1/3 : ℝ)))
        atTop (𝓝 (1/2 : ℝ)) := by
    have := h_rpow_tendsto.const_sub (1/2 : ℝ)
    simpa using this
  -- Step D: apply the squeeze theorem.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h_lower h_upper ?_ ?_
  · filter_upwards [hY'] with n hn
    have := abs_lt.mp hn
    linarith [this.1]
  · filter_upwards [hY'] with n hn
    have := abs_lt.mp hn
    linarith [this.2]

/-! #### Relating word-length to the Busemann function

On a tree, for any `φ` and `x`:
  `b_φ(x) = |x| − 2 · m(x, φ)` where `m(x, φ)` is the common-prefix length.
In particular `|b_φ(x)| ≤ |x|`, so `|b_{φ₀}(X_n)/n| ≤ |X_n|/n`. For the
reverse direction, one notes that for each `X_n`, there is *some* boundary
continuation `ψ_n` of the reduced word of `X_n` for which `b_{ψ_n}(X_n) =
−|X_n|`. But `ψ_n` depends on `X_n`, so we cannot directly plug it into
`busemann_walk_ratio_ae_tendsto` (which fixes `φ = φ₀`).

The standard workaround: the common-prefix length `m(X_n, φ₀)` grows
*sublinearly* along the walk (a separate Borel–Cantelli argument on the
number of times the walk "returns to" a fixed axis), so
`|X_n| = b_{φ₀}(X_n) + 2 m(X_n, φ₀) ≈ b_{φ₀}(X_n)` up to a sublinear
error, and `|X_n|/n → 1/2`.

We formulate the sublinearity as an auxiliary a.s. statement. -/

/-- The algebraic identity `|x| = b_φ(x) + 2 m(x, φ)` from the definition
of the Busemann function, cast to `ℝ`. -/
lemma word_length_eq_busemann_plus_prefix (φ : ∂F2) (x : F2) :
    (x.toWord.length : ℝ)
      = (busemann φ x : ℝ) + 2 * (common_prefix_length x φ : ℝ) := by
  unfold busemann
  push_cast; ring

open private F2_dist_eq_toWord_length from EnsX2026.FreeGroup.TreeAndGrowth

/-- A **metric-graph identity**: the Cayley-graph distance from `1`
equals the reduced-word length. This is a standard fact about the free
group with its standard generators — `F_2` is a tree with respect to the
Cayley graph of `F2_generating_set`, and the unique geodesic from `1` to
`x` has length `|x.toWord|`. We reuse the proof `F2_dist_eq_toWord_length`
from `TreeAndGrowth`, which is `private` there, opened here via
`open private` (Batteries). We use this identity to convert between
`word_length (X_walk n Y)` (graph distance) and
`(X_walk n Y).toWord.length` (algebraic length). -/
lemma word_length_eq_toWord_length (x : F2) :
    (word_length x : ℕ) = x.toWord.length := by
  unfold word_length F2_cayley
  exact F2_dist_eq_toWord_length x

/-! ### Q43, Q44 — see Wave 23A.4 closure at the end of file

The almost-sure rate of escape `walk_rate_of_escape` (Q43) and transience
`walk_transience` (Q44) are stated and proved at the end of the file,
after the Wave 23A.4 closure of the prefix-sublinearity lemma
`common_prefix_sublinear` (which used to be a companion axiom and is now
fully proven from the strong law of large numbers applied to the coupled
i.i.d. cancellation indicator). -/

/-! ### Wave 22F.3 orphan cleanup

Two Wave 22F.2.2 "companion axioms" previously sat here:
`walk_to_boundary_limit` and `walk_to_boundary_convergence`.  They
were introduced to support the martingale route of
`translated_walk_limit_identification` in
`EnsX2026.FreeGroup.TreeBoundedHarmonicVanish`.  That martingale route
has been replaced by a legitimate Route (a) closure
(`harmonic_vanishes_of_global_shell_decay`) that does not use these
axioms, so both were removed in Wave 22F.3 as orphans. -/

/-! ### Wave 23A.2 — cancellation indicator and walk-length divergence

Infrastructure feeding the Wave 23A.3 `J_k`-coupling argument used to close
`common_prefix_sublinear`. We define a deterministic cancellation indicator
along the walk and the resulting deterministic length identity, then deduce
a.s. divergence of the walk length from the already-proven Busemann ratio
limit. None of this is probabilistic: the only a.s. statements come from
`busemann_walk_ratio_ae_tendsto`. -/

/-- **Cancellation indicator** at step `k`: `1` if multiplying `X_walk k Y`
by `Y k` shortens the reduced word (i.e. cancellation occurred at the
tail), `0` otherwise.

We use the length-comparison form (Route C of the Wave plan): the
multiplication by a generator `Y k` either appends a letter (length `+1`)
or cancels the last letter (length `−1`). The indicator detects the latter.
This avoids any explicit letter manipulation at the indicator level —
the case analysis enters only in the proof of the length identity. -/
noncomputable def cancellationIndicator (k : ℕ) (Y : ℕ → F2) : ℝ :=
  if (X_walk (k + 1) Y).toWord.length + 1 = (X_walk k Y).toWord.length
    then 1 else 0

/-! #### Letter extraction from a generator step

The walk uses `Y k : F2`, but the BusemannLocal lemmas operate on letters
`ℓ : Fin 2 × Bool`. We package the extraction `Y k = mk [ℓ]` for some `ℓ`
behind a single helper. -/

/-- Every element of `F2_generating_set` is `mk [ℓ]` for some letter `ℓ`. -/
lemma exists_letter_of_mem_generating_set {z : F2}
    (hz : z ∈ F2_generating_set) :
    ∃ ℓ : Fin 2 × Bool, z = _root_.FreeGroup.mk [ℓ] := by
  rcases hz with h | h | h | h
  · exact ⟨(0, true), by rw [h]; rfl⟩
  · exact ⟨(1, true), by rw [h]; rfl⟩
  · refine ⟨(0, false), ?_⟩
    rw [h, BusemannLocal.mk_single_false]
  · refine ⟨(1, false), ?_⟩
    rw [h, BusemannLocal.mk_single_false]

/-! #### Length identity

Each step changes the word length by exactly `±1` (multiplying by a
generator). Cancellation at step `k` means the length decreased; the
indicator records this with value `1`. The deterministic identity is
then `|X_walk n Y| = n − 2 · Σ_{k<n} I_k`, by induction on `n`. -/

/-- The single-step length identity: at each step the walk's word length
changes by `+1` (no cancellation) or `−1` (cancellation), and the
cancellation indicator records the dichotomy as a deterministic `±1` fact.

The proof depends on `Y k` lying in `F2_generating_set` (provided by the
ambient assumption that the indicator is evaluated on the walk; we need
this fact later when we use it under the integral / pointwise on samples
of `step_measure`).

For algebraic flexibility we state the identity *unconditionally* on `Y k`:
when `Y k ∉ F2_generating_set`, the equation `|X_walk (n+1) Y| = ...`
might fail, but our downstream consumers only use it on samples drawn from
`step_measure`, which is supported on sequences with values in
`F2_generating_set`. We therefore parameterise the lemma on the membership
hypothesis. -/
lemma walk_length_step_dichotomy
    {n : ℕ} {Y : ℕ → F2} (hY : Y n ∈ F2_generating_set) :
    ((X_walk (n + 1) Y).toWord.length : ℤ)
      = (X_walk n Y).toWord.length + 1
        ∨ ((X_walk (n + 1) Y).toWord.length : ℤ)
            = (X_walk n Y).toWord.length - 1 := by
  obtain ⟨ℓ, hℓ⟩ := exists_letter_of_mem_generating_set hY
  -- `X_walk (n+1) Y = X_walk n Y * mk [ℓ]`.
  have hstep : X_walk (n + 1) Y = X_walk n Y * _root_.FreeGroup.mk [ℓ] := by
    simp [X_walk, hℓ]
  -- Case on cancellation at the last letter.
  by_cases hcanc :
      BusemannLocal.LastCancels (X_walk n Y) ℓ
  · right
    rw [hstep,
      BusemannLocal.length_toWord_mul_mk_letter_cancel _ _ hcanc]
    have hpos := BusemannLocal.length_pos_of_cancels hcanc
    omega
  · left
    -- Convert ¬LastCancels to NoLastCancel.
    have hnoc : BusemannLocal.NoLastCancel (X_walk n Y) ℓ := by
      intro ℓ' hmem hbad
      exact hcanc ⟨ℓ', hmem, hbad⟩
    rw [hstep,
      BusemannLocal.length_toWord_mul_mk_letter_noCancel _ _ hnoc]
    push_cast
    ring

/-- The cancellation indicator is `0` or `1`. -/
lemma cancellationIndicator_eq_zero_or_one (k : ℕ) (Y : ℕ → F2) :
    cancellationIndicator k Y = 0 ∨ cancellationIndicator k Y = 1 := by
  by_cases h : (X_walk (k + 1) Y).toWord.length + 1
                  = (X_walk k Y).toWord.length
  · right
    exact if_pos h
  · left
    exact if_neg h

/-- The cancellation indicator is non-negative. -/
lemma cancellationIndicator_nonneg (k : ℕ) (Y : ℕ → F2) :
    0 ≤ cancellationIndicator k Y := by
  rcases cancellationIndicator_eq_zero_or_one k Y with h | h
  · rw [h]
  · rw [h]; norm_num

/-- **Deterministic length identity**: along the walk,
`|X_walk n Y| = n − 2 · ∑_{k<n} I_k(Y)`, where `I_k` is the cancellation
indicator. Proven by induction on `n`, using
`walk_length_step_dichotomy` at the inductive step.

The hypothesis `Y_in : ∀ k < n, Y k ∈ F2_generating_set` is satisfied
`step_measure`-a.s. (in fact for every sample path drawn from the product
of `Z_uniform`, since `Z_uniform` is supported on `F2_generating_set`). -/
theorem walk_length_eq_n_minus_two_cancellations
    (n : ℕ) (Y : ℕ → F2)
    (hY : ∀ k, k < n → Y k ∈ F2_generating_set) :
    ((X_walk n Y).toWord.length : ℝ)
      = (n : ℝ)
        - 2 * (Finset.range n).sum (fun k => cancellationIndicator k Y) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hY' : ∀ k, k < n → Y k ∈ F2_generating_set :=
        fun k hk => hY k (Nat.lt_succ_of_lt hk)
      have ihY := ih hY'
      have hYn : Y n ∈ F2_generating_set := hY n (Nat.lt_succ_self n)
      rw [Finset.sum_range_succ]
      rcases walk_length_step_dichotomy (n := n) (Y := Y) hYn with hcase | hcase
      · -- No cancellation: `|X_{n+1}| = |X_n| + 1`. Indicator = 0.
        have hind : cancellationIndicator n Y = 0 := by
          unfold cancellationIndicator
          have h_neq : ¬ ((X_walk (n + 1) Y).toWord.length + 1
                            = (X_walk n Y).toWord.length) := by
            intro heq
            have h_int : ((X_walk (n + 1) Y).toWord.length : ℤ) + 1
                            = (X_walk n Y).toWord.length := by
              exact_mod_cast heq
            -- From hcase: `|X_{n+1}| = |X_n| + 1`. Combined with h_int: gives 2 = 0.
            omega
          rw [if_neg h_neq]
        rw [hind]
        -- Goal: |X_{n+1}|.toWord.length = (n+1 : ℝ) - 2 * (S_n + 0)
        --       where S_n := ∑_{k<n} indicator
        -- We have hcase: (|X_{n+1}|.toWord.length : ℤ) = |X_n|.toWord.length + 1
        have hcase_real : ((X_walk (n + 1) Y).toWord.length : ℝ)
                            = ((X_walk n Y).toWord.length : ℝ) + 1 := by
          exact_mod_cast hcase
        rw [hcase_real, ihY]
        push_cast
        ring
      · -- Cancellation: `|X_{n+1}| = |X_n| − 1`. Indicator = 1.
        -- For this branch we need `|X_n| ≥ 1` so that `|X_{n+1}| + 1 = |X_n|` literally.
        have hpos : 1 ≤ (X_walk n Y).toWord.length := by
          -- From hcase: |X_{n+1}|.toWord.length = |X_n|.toWord.length - 1 in ℤ.
          -- Lengths are nat, so |X_n| ≥ 1 (otherwise RHS would be -1).
          by_contra hlt
          push_neg at hlt
          interval_cases (X_walk n Y).toWord.length
          -- Then hcase becomes `(... : ℤ) = 0 - 1 = -1`, but lengths are ≥ 0.
          -- `simp at hcase` reduces the RHS and closes from nonneg.
          simp at hcase
        have h_eq_succ : (X_walk (n + 1) Y).toWord.length + 1
                          = (X_walk n Y).toWord.length := by
          have h_int : ((X_walk (n + 1) Y).toWord.length : ℤ) + 1
                          = (X_walk n Y).toWord.length := by linarith
          exact_mod_cast h_int
        have hind : cancellationIndicator n Y = 1 := by
          unfold cancellationIndicator
          rw [if_pos h_eq_succ]
        rw [hind]
        have hcase_real : ((X_walk (n + 1) Y).toWord.length : ℝ)
                            = ((X_walk n Y).toWord.length : ℝ) - 1 := by
          have : ((X_walk (n + 1) Y).toWord.length : ℝ) + 1
                    = ((X_walk n Y).toWord.length : ℝ) := by
            exact_mod_cast h_eq_succ
          linarith
        rw [hcase_real, ihY]
        push_cast
        ring

/-! #### Word-length divergence

From `busemann_walk_ratio_ae_tendsto` (`b_n/n → 1/2`), the deterministic
identity `|x| = b_φ(x) + 2 m(x, φ) ≥ b_φ(x)` (since `m ≥ 0`) yields
`lim inf |X_n|/n ≥ 1/2 > 0`, hence `|X_n| → ∞` a.s. -/

/-- Eventually along the walk, `|X_walk n Y|/n > 1/4` whenever `b_n/n → 1/2`. -/
private lemma walk_length_ratio_eventually_gt
    {Y : ℕ → F2}
    (hY : Tendsto (fun n : ℕ => (busemann phi_zero (X_walk n Y) : ℝ) / n)
              atTop (𝓝 (1/2 : ℝ))) :
    ∀ᶠ n : ℕ in atTop,
      ((X_walk n Y).toWord.length : ℝ) / n > 1/4 := by
  -- From `b_n/n → 1/2`, eventually `b_n/n > 1/4`.
  have hb_event : ∀ᶠ n : ℕ in atTop,
      (busemann phi_zero (X_walk n Y) : ℝ) / n > 1/4 := by
    have h_lt : (1/4 : ℝ) < 1/2 := by norm_num
    exact hY.eventually_const_lt h_lt
  filter_upwards [hb_event, eventually_ge_atTop 1] with n hb hn1
  -- For n ≥ 1, |X_n| ≥ b_n (from the identity + m ≥ 0), so |X_n|/n ≥ b_n/n > 1/4.
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
  have h_id := word_length_eq_busemann_plus_prefix phi_zero (X_walk n Y)
  have h_m_nn : (0 : ℝ) ≤ (common_prefix_length (X_walk n Y) phi_zero : ℝ) := by
    exact_mod_cast Nat.zero_le _
  have h_le : (busemann phi_zero (X_walk n Y) : ℝ)
                ≤ ((X_walk n Y).toWord.length : ℝ) := by
    linarith
  have h_ratio : (busemann phi_zero (X_walk n Y) : ℝ) / n
                    ≤ ((X_walk n Y).toWord.length : ℝ) / n :=
    div_le_div_of_nonneg_right h_le hn_pos.le
  linarith

/-- **Word-length divergence**: a.s., the walk's reduced-word length tends
to `+∞`. This is the key input to the finite-visits-to-identity statement
and, downstream, to the Wave 23A.3 `J_k`-coupling argument. -/
theorem walk_length_tendsto_atTop :
    ∀ᵐ Y ∂step_measure,
      Tendsto (fun n : ℕ => ((X_walk n Y).toWord.length : ℝ)) atTop atTop := by
  filter_upwards [busemann_walk_ratio_ae_tendsto] with Y hY
  -- Strategy: show |X_n| ≥ n/4 eventually, and `n/4 → ∞`.
  have h_event := walk_length_ratio_eventually_gt hY
  -- `(n : ℝ)/4 → ∞`.
  have h_n4 : Tendsto (fun n : ℕ => (n : ℝ) / 4) atTop atTop := by
    have h_n : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have : Tendsto (fun n : ℕ => (n : ℝ) * (1 / 4)) atTop atTop :=
      h_n.atTop_mul_pos (by norm_num : (0 : ℝ) < 1 / 4) tendsto_const_nhds
    refine this.congr (fun n => ?_)
    ring
  -- `|X_n| ≥ n/4` eventually.
  refine tendsto_atTop_mono' atTop ?_ h_n4
  filter_upwards [h_event, eventually_ge_atTop 1] with n hn hn1
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
  -- |X_n|/n > 1/4 ⟹ |X_n| > n/4.
  have h_mul : ((X_walk n Y).toWord.length : ℝ) / n * n
                  > (1 / 4 : ℝ) * n := by
    exact mul_lt_mul_of_pos_right hn hn_pos
  have h_lhs : ((X_walk n Y).toWord.length : ℝ) / n * n
                  = ((X_walk n Y).toWord.length : ℝ) := by
    field_simp
  rw [h_lhs] at h_mul
  linarith

/-- **Finite visits to the identity**: a.s., the walk visits the identity
only finitely often. Stated as: eventually the reduced word has length at
least `1`, i.e. `X_walk n Y ≠ 1`. Immediate corollary of
`walk_length_tendsto_atTop`. -/
theorem walk_length_eventually_pos :
    ∀ᵐ Y ∂step_measure,
      ∃ N : ℕ, ∀ n ≥ N, (X_walk n Y).toWord.length ≥ 1 := by
  filter_upwards [walk_length_tendsto_atTop] with Y hY
  -- From `|X_n| → ∞` (in ℝ), eventually `|X_n| ≥ 1`.
  have h_event : ∀ᶠ n : ℕ in atTop,
      (1 : ℝ) ≤ ((X_walk n Y).toWord.length : ℝ) :=
    hY.eventually_ge_atTop (1 : ℝ)
  rcases h_event.exists_forall_of_atTop with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  have h_real := hN n hn
  exact_mod_cast h_real

/-! ### Wave 23A.3 — i.i.d.-Bernoulli(1/4) coupling for the cancellation indicator

The cancellation indicator `cancellationIndicator k` is **not** i.i.d.: it
depends on the walk history through `(X_walk k Y).toWord`. To apply the
strong law of large numbers (Wave 23A.4) we couple it with an auxiliary
indicator `coupledIndicator k` that **is** i.i.d.-Bernoulli(1/4) under
`step_measure`.

**Idea.** At each step `k`, let `letterToCancel k Y : Fin 2 × Bool` be the
letter whose appearance as `Y k` would cancel the last letter of
`X_walk k Y`. Concretely:

* If `(X_walk k Y).toWord.getLast? = some (c, sign)`, the inverse letter is
  `(c, !sign)`, and the corresponding generator is `_root_.FreeGroup.mk [(c, !sign)]`.
* If `X_walk k Y = 1` (length 0), default to `(0, false)`, corresponding to
  the generator `genA⁻¹ = _root_.FreeGroup.mk [(0, false)]`.

Then `coupledIndicator k Y := 1{Y k = mk [letterToCancel k Y]}` is `1` iff
the next step would cancel (when length ≥ 1) or iff `Y k = genA⁻¹` (when
length = 0). On the a.s. event "walk is eventually away from the identity"
(`walk_length_eventually_pos`), the two indicators agree from some `N`
onwards, so the difference of their Cesàro averages tends to `0` a.s.

**Why i.i.d.** Conditional on `(Y_0, …, Y_{k-1})`, the letter to cancel is
determined (it is a function of `X_walk k Y` which depends only on the past
steps); `Y_k` is independent of the past with uniform distribution on the
4-element generating set. So the conditional probability that `Y_k` equals
the determined target letter is exactly `1/4`. Constant conditional
probability ⇒ unconditional independence (Williams §9.7).

**Status (Wave 23A.3).** The coupling difference (Commit 3) is fully
proven from `walk_length_eventually_pos`. The i.i.d. property of
`coupledIndicator` (Commit 2) is admitted as a single companion axiom
`coupledIndicator_iIndepFun_iIdentDistrib` with full Williams §9.7 paper
proof in the doc-block. This is the standard "constant conditional law ⇒
independence" lemma — the one narrow Tier-3 admission allowed by the wave
plan. -/

/-- The letter whose appearance as `Y k` would cancel the last letter of
`X_walk k Y`. When `X_walk k Y = 1` (no last letter), defaults to
`(0, false)`, i.e. the letter for `genA⁻¹`. -/
noncomputable def letterToCancel (k : ℕ) (Y : ℕ → F2) : Fin 2 × Bool :=
  match (X_walk k Y).toWord.getLast? with
  | some ℓ => (ℓ.1, !ℓ.2)
  | none => (0, false)

/-- The auxiliary **coupled** cancellation indicator at step `k`: equals `1`
iff `Y k = mk [letterToCancel k Y]`, the generator that cancels the last
letter of `X_walk k Y` (or equals `genA⁻¹` when at the identity). -/
noncomputable def coupledIndicator (k : ℕ) (Y : ℕ → F2) : ℝ :=
  if Y k = _root_.FreeGroup.mk [letterToCancel k Y] then 1 else 0

/-- The coupled indicator is `0` or `1`. -/
lemma coupledIndicator_eq_zero_or_one (k : ℕ) (Y : ℕ → F2) :
    coupledIndicator k Y = 0 ∨ coupledIndicator k Y = 1 := by
  by_cases h : Y k = _root_.FreeGroup.mk [letterToCancel k Y]
  · right; exact if_pos h
  · left; exact if_neg h

/-- The coupled indicator is non-negative. -/
lemma coupledIndicator_nonneg (k : ℕ) (Y : ℕ → F2) :
    0 ≤ coupledIndicator k Y := by
  rcases coupledIndicator_eq_zero_or_one k Y with h | h
  · rw [h]
  · rw [h]; norm_num

/-- The coupled indicator is at most `1`. -/
lemma coupledIndicator_le_one (k : ℕ) (Y : ℕ → F2) :
    coupledIndicator k Y ≤ 1 := by
  rcases coupledIndicator_eq_zero_or_one k Y with h | h
  · rw [h]; norm_num
  · rw [h]

/-! #### Coupling: cancellation and coupled indicators agree when `|X_walk k Y| ≥ 1`

The two indicators differ only when the walk is at the identity. We prove
the agreement under the explicit hypothesis on the walk length plus the
ambient hypothesis `Y k ∈ F2_generating_set`. -/

/-- **Coupling lemma**: when `(X_walk k Y).toWord.length ≥ 1` and
`Y k ∈ F2_generating_set`, the cancellation indicator equals the coupled
indicator. The proof is a careful unfolding through `LastCancels`. -/
lemma coupledIndicator_eq_cancellationIndicator_of_length_pos
    {k : ℕ} {Y : ℕ → F2}
    (hYk : Y k ∈ F2_generating_set)
    (hpos : 1 ≤ (X_walk k Y).toWord.length) :
    coupledIndicator k Y = cancellationIndicator k Y := by
  -- Extract the last letter and the letter form of `Y k`.
  obtain ⟨ℓ, hℓ⟩ := exists_letter_of_mem_generating_set hYk
  -- `(X_walk k Y).toWord.getLast? = some ℓ_last` for some letter `ℓ_last`.
  set L := (X_walk k Y).toWord with hL_def
  have hL_ne : L ≠ [] := by
    intro hempty
    have hlen0 : L.length = 0 := by rw [hempty]; rfl
    have : (X_walk k Y).toWord.length = 0 := by rw [← hL_def]; exact hlen0
    omega
  have hgetLast : L.getLast? = some (L.getLast hL_ne) :=
    List.getLast?_eq_getLast_of_ne_nil hL_ne
  set ℓ_last := L.getLast hL_ne with hℓ_last_def
  -- letterToCancel k Y = (ℓ_last.1, !ℓ_last.2)
  have h_lTC : letterToCancel k Y = (ℓ_last.1, !ℓ_last.2) := by
    unfold letterToCancel
    rw [← hL_def, hgetLast]
  -- Now case on whether `Y k = mk [letterToCancel k Y]`.
  unfold coupledIndicator cancellationIndicator
  by_cases hYeq : Y k = _root_.FreeGroup.mk [letterToCancel k Y]
  · -- Coupled = 1; show cancellationIndicator = 1, i.e. cancellation occurs.
    rw [if_pos hYeq]
    -- From `hYeq` and `hℓ`, deduce `mk [ℓ] = mk [(ℓ_last.1, !ℓ_last.2)]`,
    -- which forces `ℓ = (ℓ_last.1, !ℓ_last.2)` (cancellation matches).
    rw [h_lTC] at hYeq
    have hℓ_eq : _root_.FreeGroup.mk [ℓ] = _root_.FreeGroup.mk [(ℓ_last.1, !ℓ_last.2)] := by
      rw [← hℓ]; exact hYeq
    -- mk [a] = mk [b] (with both reduced singletons) iff a = b.
    have hℓ_letter : ℓ = (ℓ_last.1, !ℓ_last.2) := by
      have h1 := congrArg _root_.FreeGroup.toWord hℓ_eq
      rw [_root_.FreeGroup.toWord_mk, _root_.FreeGroup.toWord_mk] at h1
      -- A singleton is reduced iff it's a singleton; reduce of [ℓ] = [ℓ].
      have hr1 : _root_.FreeGroup.reduce [ℓ] = [ℓ] := by
        simp [_root_.FreeGroup.reduce]
      have hr2 : _root_.FreeGroup.reduce [(ℓ_last.1, !ℓ_last.2)]
                  = [(ℓ_last.1, !ℓ_last.2)] := by
        simp [_root_.FreeGroup.reduce]
      rw [hr1, hr2] at h1
      exact List.cons.inj h1 |>.1
    -- Now LastCancels (X_walk k Y) ℓ holds.
    have hcanc : BusemannLocal.LastCancels (X_walk k Y) ℓ := by
      refine ⟨ℓ_last, ?_, ?_, ?_⟩
      · rw [← hL_def]; exact hgetLast
      · rw [hℓ_letter]
      · rw [hℓ_letter]; simp
    -- Apply the cancel-length lemma.
    have hstep : X_walk (k + 1) Y = X_walk k Y * _root_.FreeGroup.mk [ℓ] := by
      simp [X_walk, hℓ]
    have hlen : (X_walk (k + 1) Y).toWord.length = (X_walk k Y).toWord.length - 1 := by
      rw [hstep]
      exact BusemannLocal.length_toWord_mul_mk_letter_cancel _ _ hcanc
    have hpos' : 1 ≤ (X_walk k Y).toWord.length := hpos
    have hlen_succ : (X_walk (k + 1) Y).toWord.length + 1 = (X_walk k Y).toWord.length := by
      rw [hlen]
      omega
    rw [if_pos hlen_succ]
  · -- Coupled = 0; show cancellationIndicator = 0, i.e. no cancellation.
    rw [if_neg hYeq]
    -- ¬ LastCancels: if it did, then `Y k = mk [(ℓ_last.1, !ℓ_last.2)]`.
    have hno : BusemannLocal.NoLastCancel (X_walk k Y) ℓ := by
      intro ℓ' hmem ⟨h1, h2⟩
      apply hYeq
      rw [hℓ, h_lTC]
      -- ℓ' = ℓ_last (since both come from getLast?), and ℓ.1 = ℓ'.1, ℓ.2 = !ℓ'.2.
      have h_ℓ' : ℓ' = ℓ_last := by
        rw [← hL_def] at hmem
        rw [hgetLast] at hmem
        exact (Option.some_inj.mp hmem).symm
      rw [h_ℓ'] at h1 h2
      -- After rw: h1 : ℓ_last.1 = ℓ.1, h2 : ℓ_last.2 = !ℓ.2.
      -- Goal: mk [ℓ] = mk [(ℓ_last.1, !ℓ_last.2)].
      have h1' : ℓ.1 = ℓ_last.1 := h1.symm
      have h2' : ℓ.2 = !ℓ_last.2 := by
        rw [h2]; exact (Bool.not_not _).symm
      have hℓ_pair : ℓ = (ℓ_last.1, !ℓ_last.2) := Prod.ext h1' h2'
      rw [hℓ_pair]
    have hstep : X_walk (k + 1) Y = X_walk k Y * _root_.FreeGroup.mk [ℓ] := by
      simp [X_walk, hℓ]
    have hlen : (X_walk (k + 1) Y).toWord.length = (X_walk k Y).toWord.length + 1 := by
      rw [hstep]
      exact BusemannLocal.length_toWord_mul_mk_letter_noCancel _ _ hno
    have hno_eq : ¬ ((X_walk (k + 1) Y).toWord.length + 1
                        = (X_walk k Y).toWord.length) := by
      intro heq; rw [hlen] at heq; omega
    rw [if_neg hno_eq]

/-! #### Coupling: i.i.d.-Bernoulli(1/4) property — Wave 23C closure

The coupled cancellation indicator family `(coupledIndicator k)_{k ∈ ℕ}` is
i.i.d. Bernoulli(1/4) under `step_measure`. **As of Wave 23C** this is a
**theorem**, derived from the generic companion axiom
`iIndepFun_iIdentDistrib_uniformIndic_pastDep` (Williams §9.7) at the
1-element past-measurable target `A k Y := { mk [letterToCancel k Y] }`. -/

/-- The "letter to cancel", as an element of `F2`: the generator that
would cancel the last letter of `X_walk k Y`. By construction it lies in
`F2_generating_set` (`mk_letter_mem_generating_set`). -/
private noncomputable def coupledTargetGen (k : ℕ) (Y : ℕ → F2) : F2 :=
  _root_.FreeGroup.mk [letterToCancel k Y]

/-- The 1-element Finset target for the coupled-indicator analysis:
`A k Y := { mk [letterToCancel k Y] }`. By construction, `Y k ∈ A k Y` iff
`Y k = mk [letterToCancel k Y]`, recovering `coupledIndicator k Y = 1`. -/
private noncomputable def coupledTargetFinset (k : ℕ) (Y : ℕ → F2) :
    Finset F2 := {coupledTargetGen k Y}

/-- The 1-element target depends only on the past `(Y 0, …, Y (k-1))`,
through `X_walk k Y` (a function of past steps only). -/
private lemma coupledTargetFinset_past (k : ℕ) (Y Y' : ℕ → F2)
    (h : ∀ j, j < k → Y j = Y' j) :
    coupledTargetFinset k Y = coupledTargetFinset k Y' := by
  -- `X_walk k` depends only on `Y 0, …, Y (k-1)`; through it, so does
  -- `letterToCancel k`, hence `coupledTargetGen k`, hence the singleton.
  have hwalk : X_walk k Y = X_walk k Y' := by
    induction k with
    | zero => simp [X_walk]
    | succ n ih =>
      have hpast : ∀ j, j < n → Y j = Y' j := fun j hj => h j (by omega)
      have hYn : Y n = Y' n := h n (by omega)
      rw [X_walk_succ, X_walk_succ, ih hpast, hYn]
  unfold coupledTargetFinset coupledTargetGen letterToCancel
  rw [hwalk]

/-- The 1-element target has cardinality 1. -/
private lemma coupledTargetFinset_card (k : ℕ) (Y : ℕ → F2) :
    (coupledTargetFinset k Y).card = 1 := by
  unfold coupledTargetFinset
  exact Finset.card_singleton _

/-- The 1-element target lies inside `F2_generating_set`. -/
private lemma coupledTargetFinset_subset (k : ℕ) (Y : ℕ → F2) :
    ↑(coupledTargetFinset k Y) ⊆ F2_generating_set := by
  intro z hz
  unfold coupledTargetFinset at hz
  -- `z ∈ {coupledTargetGen k Y}` ⇒ `z = coupledTargetGen k Y`.
  rw [Finset.coe_singleton, Set.mem_singleton_iff] at hz
  rw [hz]
  -- `coupledTargetGen k Y = mk [letterToCancel k Y] ∈ F2_generating_set`.
  unfold coupledTargetGen
  exact BusemannLocal.mk_letter_mem_generating_set _

/-- Pointwise reformulation: `coupledIndicator k Y` equals the `if`-form
based on `coupledTargetFinset`. By construction, since
`coupledTargetFinset k Y = {mk [letterToCancel k Y]}`, membership reduces
to equality. -/
private lemma coupledIndicator_eq_indicator (k : ℕ) (Y : ℕ → F2) :
    coupledIndicator k Y =
      (if Y k ∈ coupledTargetFinset k Y then (1 : ℝ) else 0) := by
  unfold coupledIndicator coupledTargetFinset coupledTargetGen
  simp [Finset.mem_singleton]

/-- **Theorem (Wave 23C, formerly companion axiom).** Mutual independence
and identical distribution of the coupled cancellation indicator family,
plus the marginal-mean `1/4`. Derived from the generic companion axiom
`iIndepFun_iIdentDistrib_uniformIndic_pastDep` at `c = 1`. -/
theorem coupledIndicator_iIndepFun_iIdentDistrib :
    iIndepFun (fun k : ℕ => coupledIndicator k) step_measure
      ∧ (∀ k : ℕ,
          IdentDistrib (coupledIndicator k) (coupledIndicator 0)
            step_measure step_measure)
      ∧ ∫ Y, coupledIndicator 0 Y ∂step_measure = (1/4 : ℝ) := by
  -- Apply the generic axiom with `A := coupledTargetFinset`, `c := 1`.
  have hgen :=
    iIndepFun_iIdentDistrib_uniformIndic_pastDep
      coupledTargetFinset coupledTargetFinset_past coupledTargetFinset_subset
      1 coupledTargetFinset_card
  -- The generic family `f` agrees pointwise with `coupledIndicator`.
  have hpw : ∀ k Y,
      (if Y k ∈ coupledTargetFinset k Y then (1 : ℝ) else 0)
        = coupledIndicator k Y := by
    intro k Y
    rw [coupledIndicator_eq_indicator]
  -- Rewrite `hgen` from the `f` form to the `coupledIndicator` form.
  -- All three conjuncts share the same pointwise rewrite from the generic
  -- `f := fun k Y => if Y k ∈ A k Y then 1 else 0` to `coupledIndicator k`.
  have hfun_eq :
      (fun k : ℕ => fun Y : ℕ → F2 =>
          (if Y k ∈ coupledTargetFinset k Y then (1 : ℝ) else 0))
        = (fun k : ℕ => coupledIndicator k) := by
    funext k Y; exact hpw k Y
  refine ⟨?_, ?_, ?_⟩
  · -- Mutual independence.
    have h_indep := hgen.1
    simp only at h_indep
    rw [hfun_eq] at h_indep
    exact h_indep
  · intro k
    have h_id := hgen.2.1 k
    simp only at h_id
    have h0 :
        (fun Y : ℕ → F2 =>
            (if Y 0 ∈ coupledTargetFinset 0 Y then (1 : ℝ) else 0))
          = coupledIndicator 0 := by
      funext Y; exact hpw 0 Y
    have hk :
        (fun Y : ℕ → F2 =>
            (if Y k ∈ coupledTargetFinset k Y then (1 : ℝ) else 0))
          = coupledIndicator k := by
      funext Y; exact hpw k Y
    rw [hk, h0] at h_id
    exact h_id
  · have h_int := hgen.2.2
    simp only at h_int
    -- `(1 : ℕ) / 4 = 1/4` as reals.
    have h_const : ((1 : ℕ) : ℝ) / 4 = (1/4 : ℝ) := by norm_num
    rw [h_const] at h_int
    have h0 : (fun Y : ℕ → F2 =>
        (if Y 0 ∈ coupledTargetFinset 0 Y then (1 : ℝ) else 0))
          = coupledIndicator 0 := by
      funext Y; exact hpw 0 Y
    rw [h0] at h_int
    exact h_int

/-- The mutual-independence half. -/
lemma coupledIndicator_iIndepFun :
    iIndepFun (fun k : ℕ => coupledIndicator k) step_measure :=
  coupledIndicator_iIndepFun_iIdentDistrib.1

/-- The identical-distribution half. -/
lemma coupledIndicator_iIdentDistrib (k : ℕ) :
    IdentDistrib (coupledIndicator k) (coupledIndicator 0)
      step_measure step_measure :=
  coupledIndicator_iIndepFun_iIdentDistrib.2.1 k

/-! #### Coupling difference Cesàro-tends to `0` a.s.

From `walk_length_eventually_pos`, eventually `(X_walk k Y).toWord.length ≥ 1`,
so by the coupling lemma `coupledIndicator k Y = cancellationIndicator k Y`
on a tail. The difference of partial sums is then bounded by a constant
(the number of times the walk visits the identity), which divided by `n`
tends to `0`. -/

/-- **Coupling difference → 0 a.s.** Under `step_measure`, the Cesàro
average of the difference `cancellationIndicator k - coupledIndicator k`
tends to `0`.

**Proof.** From `walk_length_eventually_pos` and
`walk_step_in_generating_set_ae`, eventually (say from `k ≥ N(Y)` onwards)
both `(X_walk k Y).toWord.length ≥ 1` and `Y k ∈ F2_generating_set` hold.
Then by `coupledIndicator_eq_cancellationIndicator_of_length_pos`, the
two indicators agree on `[N(Y), ∞)`. Hence

```
∑_{k<n} cancellationIndicator k Y - ∑_{k<n} coupledIndicator k Y
  = ∑_{k<min(n, N(Y))} (cancellationIndicator k Y - coupledIndicator k Y)
```
is bounded in absolute value by `N(Y)` (each term is in `[-1, 1]`),
independently of `n`. Dividing by `n` gives a sequence tending to `0`. -/
theorem coupling_difference_tendsto_zero :
    ∀ᵐ Y ∂step_measure,
      Tendsto
        (fun n : ℕ =>
          (∑ k ∈ Finset.range n, cancellationIndicator k Y
            - ∑ k ∈ Finset.range n, coupledIndicator k Y) / n)
        atTop (𝓝 (0 : ℝ)) := by
  filter_upwards [walk_length_eventually_pos, walk_step_in_generating_set_ae]
    with Y ⟨N, hN⟩ hYgen
  -- For k ≥ N, the two indicators agree.
  have h_agree : ∀ k, k ≥ N → cancellationIndicator k Y = coupledIndicator k Y := by
    intro k hk
    exact (coupledIndicator_eq_cancellationIndicator_of_length_pos
      (hYgen k) (hN k hk)).symm
  -- Define the bound: B = ∑_{k<N} |cancellationIndicator k Y - coupledIndicator k Y|.
  -- This is at most N (each term ≤ 1).
  -- The sum difference for n ≥ N equals the partial sum up to N.
  have h_diff_eventually_const : ∀ n, n ≥ N →
      ∑ k ∈ Finset.range n, cancellationIndicator k Y
        - ∑ k ∈ Finset.range n, coupledIndicator k Y
        = ∑ k ∈ Finset.range N, cancellationIndicator k Y
          - ∑ k ∈ Finset.range N, coupledIndicator k Y := by
    intro n hn
    have h_combine_n :
        ∑ k ∈ Finset.range n, cancellationIndicator k Y
          - ∑ k ∈ Finset.range n, coupledIndicator k Y
        = ∑ k ∈ Finset.range n,
            (cancellationIndicator k Y - coupledIndicator k Y) :=
      (Finset.sum_sub_distrib (s := Finset.range n)
        (f := fun k => cancellationIndicator k Y)
        (g := fun k => coupledIndicator k Y)).symm
    have h_combine_N :
        ∑ k ∈ Finset.range N, cancellationIndicator k Y
          - ∑ k ∈ Finset.range N, coupledIndicator k Y
        = ∑ k ∈ Finset.range N,
            (cancellationIndicator k Y - coupledIndicator k Y) :=
      (Finset.sum_sub_distrib (s := Finset.range N)
        (f := fun k => cancellationIndicator k Y)
        (g := fun k => coupledIndicator k Y)).symm
    rw [h_combine_n, h_combine_N]
    -- Split the sum: range n = range N ∪ Ico N n.
    have h_split : Finset.range n = Finset.range N ∪ Finset.Ico N n := by
      ext k
      simp [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
      omega
    have h_disj : Disjoint (Finset.range N) (Finset.Ico N n) := by
      rw [Finset.disjoint_left]
      intro k hk hk'
      rw [Finset.mem_range] at hk
      rw [Finset.mem_Ico] at hk'
      omega
    rw [h_split, Finset.sum_union h_disj]
    have h_zero : ∑ k ∈ Finset.Ico N n,
        (cancellationIndicator k Y - coupledIndicator k Y) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_Ico] at hk
      rw [h_agree k hk.1]; ring
    rw [h_zero, add_zero]
  -- Set the constant value of the eventual difference.
  set C : ℝ := ∑ k ∈ Finset.range N, cancellationIndicator k Y
                 - ∑ k ∈ Finset.range N, coupledIndicator k Y with hC_def
  -- Goal: ∀ᶠ n, the quotient = C/n, and C/n → 0.
  -- For n ≥ N ∨ n = 0 we have the value; for n = 0 the formula is 0/0 = 0.
  -- We handle n ≥ max(N, 1) and use the limit.
  have h_C_n_tendsto : Tendsto (fun n : ℕ => C / n) atTop (𝓝 (0 : ℝ)) := by
    -- C / n = C * n⁻¹, and n⁻¹ → 0.
    have h_inv : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 (0 : ℝ)) := by
      have h_n : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop
      exact h_n.inv_tendsto_atTop
    have h_mul : Tendsto (fun n : ℕ => C * ((n : ℝ))⁻¹) atTop (𝓝 (C * 0)) :=
      h_inv.const_mul C
    rw [mul_zero] at h_mul
    refine h_mul.congr (fun n => ?_)
    by_cases hn : (n : ℝ) = 0
    · rw [hn]; simp
    · rw [div_eq_mul_inv]
  -- Eventually the quotient equals C / n.
  refine h_C_n_tendsto.congr' ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [h_diff_eventually_const n hn]

/-! #### Combined Cesàro statement

For convenience downstream (Wave 23A.4): the average cancellation rate
equals the average coupled-indicator rate plus o(1) a.s. -/

/-- **Cesàro equivalence**: a.s., the difference between the average
cancellation rate and the average coupled-indicator rate tends to `0`.

This is a direct consequence of `coupling_difference_tendsto_zero`,
restated by separating the two averages. -/
theorem cancellation_average_eq_coupled_average_ae :
    ∀ᵐ Y ∂step_measure,
      Tendsto
        (fun n : ℕ =>
          (∑ k ∈ Finset.range n, cancellationIndicator k Y) / n
            - (∑ k ∈ Finset.range n, coupledIndicator k Y) / n)
        atTop (𝓝 (0 : ℝ)) := by
  filter_upwards [coupling_difference_tendsto_zero] with Y hY
  -- Split: (Σa)/n - (Σb)/n = (Σa - Σb)/n.
  refine hY.congr (fun n => ?_)
  by_cases hn : (n : ℝ) = 0
  · rw [hn]; simp
  · field_simp

/-! ### Wave 23A.4 — strong law for the coupled indicator and prefix sublinearity

This is the final piece of the Q43/Q44 closure.  We:

1. compute `E[coupledIndicator 0] = 1/4` (`expectation_coupledIndicator_zero`),
2. apply Mathlib's Etemadi strong law (`ProbabilityTheory.strong_law_ae_real`)
   to the family `(coupledIndicator k)` to obtain
   `(∑_{k<n} coupledIndicator k Y)/n → 1/4` a.s. (`coupled_average_tendsto`),
3. transfer to the cancellation indicator via the Wave 23A.3 coupling
   difference (`cancellation_average_tendsto`),
4. transfer to the walk length via the deterministic length identity
   (`walk_length_div_n_tendsto`),
5. dissolve the former companion axiom `common_prefix_sublinear` into a
   theorem via the Busemann ratio `b_{φ_0}(X_n)/n → 1/2` and the algebraic
   identity `|x| = b_φ(x) + 2 m(x, φ)`.

After this wave, Q43 (`walk_rate_of_escape`) and Q44 (`walk_transience`)
are Pure Lean modulo only the Q42 Azuma admissions
(`centred_away_azuma_tail` / `_neg`) and the single i.i.d. admission
`coupledIndicator_iIndepFun_iIdentDistrib` from Wave 23A.3. -/

/-- `letterToCancel 0 Y = (0, false)` for every sample path: the walk is
at the identity at step 0, so `(X_walk 0 Y).toWord = []` and the
default branch of `letterToCancel` fires. -/
private lemma letterToCancel_zero (Y : ℕ → F2) :
    letterToCancel 0 Y = (0, false) := by
  unfold letterToCancel
  -- `(X_walk 0 Y).toWord = (1 : F2).toWord = []`, so `getLast? = none`.
  simp [X_walk, _root_.FreeGroup.toWord_one]

/-- Pointwise simplification: `coupledIndicator 0 Y` is the indicator
that `Y 0 = genA⁻¹`. -/
private lemma coupledIndicator_zero_eq (Y : ℕ → F2) :
    coupledIndicator 0 Y = if Y 0 = (genA : F2)⁻¹ then 1 else 0 := by
  unfold coupledIndicator
  rw [letterToCancel_zero]
  -- `mk [(0, false)] = (of 0)⁻¹ = genA⁻¹`.
  have h_mk : (_root_.FreeGroup.mk [(0, false)] : F2) = (genA : F2)⁻¹ := by
    rw [BusemannLocal.mk_single_false]; rfl
  rw [h_mk]

-- Pairwise distinctness lemmas for the 4 generators of F_2 moved up
-- to Wave 33 prereqs.

/-- The mass `Z_uniform {z}` of any singleton in the support of `Z_uniform`
is `1/4`. We only need this for `z = genA⁻¹`, but the proof for any of
the four generators is identical. -/
private lemma Z_uniform_singleton_genA_inv :
    Z_uniform {(genA : F2)⁻¹} = (1/4 : ℝ≥0∞) := by
  unfold Z_uniform
  rw [Measure.smul_apply, Measure.add_apply, Measure.add_apply,
    Measure.add_apply]
  -- Each Dirac mass on `{genA⁻¹}` is `0` or `1` depending on equality.
  have h1 : Measure.dirac (genA : F2) {(genA : F2)⁻¹} = 0 := by
    rw [Measure.dirac_apply]
    exact Set.indicator_of_notMem (by simp [genA_ne_genA_inv]) _
  have h2 : Measure.dirac (genB : F2) {(genA : F2)⁻¹} = 0 := by
    rw [Measure.dirac_apply]
    exact Set.indicator_of_notMem (by simp [genB_ne_genA_inv]) _
  have h3 : Measure.dirac ((genA : F2)⁻¹) {(genA : F2)⁻¹} = 1 := by
    rw [Measure.dirac_apply]
    exact Set.indicator_of_mem rfl _
  have h4 : Measure.dirac ((genB : F2)⁻¹) {(genA : F2)⁻¹} = 0 := by
    rw [Measure.dirac_apply]
    exact Set.indicator_of_notMem (by
      intro h; exact genA_inv_ne_genB_inv h.symm) _
  rw [h1, h2, h3, h4]
  -- Goal: `(1/4 : ℝ≥0∞) • (0 + 0 + 1 + 0) = 1/4`.
  simp

/-! #### Measurability and integrability of `coupledIndicator 0` -/

private lemma measurable_coupledIndicator_zero :
    Measurable (fun Y : ℕ → F2 => coupledIndicator 0 Y) := by
  -- `coupledIndicator 0 Y = (Y 0 = genA⁻¹).toReal` rewritten via the
  -- pointwise lemma `coupledIndicator_zero_eq`.  We work directly with
  -- the if-expression.
  have h_eq : (fun Y : ℕ → F2 => coupledIndicator 0 Y)
                = fun Y : ℕ → F2 =>
                    if Y 0 = (genA : F2)⁻¹ then (1 : ℝ) else 0 :=
    funext coupledIndicator_zero_eq
  rw [h_eq]
  -- The set `{Y | Y 0 = genA⁻¹}` is the preimage of the (measurable)
  -- singleton `{genA⁻¹}` under the (measurable) coordinate projection.
  have hmeas : MeasurableSet {Y : ℕ → F2 | Y 0 = (genA : F2)⁻¹} := by
    have hproj : Measurable (fun Y : ℕ → F2 => Y 0) := measurable_pi_apply 0
    have hsing : MeasurableSet ({(genA : F2)⁻¹} : Set F2) :=
      MeasurableSet.of_discrete
    exact hproj hsing
  exact Measurable.ite hmeas measurable_const measurable_const

private lemma integrable_coupledIndicator_zero :
    Integrable (fun Y : ℕ → F2 => coupledIndicator 0 Y) step_measure := by
  -- Bounded and measurable on a probability measure.
  refine Integrable.mono' (g := fun _ : ℕ → F2 => (1 : ℝ))
    (integrable_const 1) measurable_coupledIndicator_zero.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun Y => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (coupledIndicator_nonneg 0 Y)]
  exact coupledIndicator_le_one 0 Y

private lemma integrable_coupledIndicator (k : ℕ) :
    Integrable (coupledIndicator k) step_measure := by
  refine ((coupledIndicator_iIdentDistrib k).integrable_iff).mpr ?_
  exact integrable_coupledIndicator_zero

/-! #### Step 1 — Compute `E[coupledIndicator 0] = 1/4` -/

/-- **Expectation of the coupled indicator at step 0.** The
unconditional expectation under `step_measure` is `1/4`: this is the
probability that `Y 0` (uniform on the 4-element generating set) equals
the prescribed letter `genA⁻¹` (the default of `letterToCancel`). -/
private lemma expectation_coupledIndicator_zero :
    ∫ Y, coupledIndicator 0 Y ∂step_measure = (1/4 : ℝ) := by
  -- Push the integrand through the `Y ↦ Y 0` projection.
  have h_eq : (fun Y : ℕ → F2 => coupledIndicator 0 Y)
                = fun Y : ℕ → F2 =>
                    (fun z : F2 => if z = (genA : F2)⁻¹ then (1 : ℝ) else 0) (Y 0) := by
    funext Y
    exact coupledIndicator_zero_eq Y
  rw [h_eq]
  -- `integral_map`: composition with measurable projection becomes
  -- integration against the pushforward measure (= `Z_uniform`).
  have hproj : Measurable (fun Y : ℕ → F2 => Y 0) := measurable_pi_apply 0
  have hf_meas : Measurable (fun z : F2 => if z = (genA : F2)⁻¹ then (1 : ℝ) else 0) := by
    refine Measurable.ite ?_ measurable_const measurable_const
    exact MeasurableSet.of_discrete
  have hmap : step_measure.map (fun Y : ℕ → F2 => Y 0) = Z_uniform := by
    unfold step_measure
    exact (measurePreserving_eval_infinitePi (μ := fun _ : ℕ => Z_uniform) 0).map_eq
  rw [← MeasureTheory.integral_map hproj.aemeasurable
        hf_meas.aestronglyMeasurable, hmap]
  -- Rewrite the if-expression as the indicator of `{genA⁻¹}` with value `1`.
  have h_indic : (fun z : F2 => if z = (genA : F2)⁻¹ then (1 : ℝ) else 0)
                  = Set.indicator {(genA : F2)⁻¹} (fun _ => (1 : ℝ)) := by
    funext z
    by_cases hz : z = (genA : F2)⁻¹
    · rw [if_pos hz, hz]; simp
    · rw [if_neg hz]
      exact (Set.indicator_of_notMem (by simpa using hz) _).symm
  rw [h_indic]
  -- The integral of `Set.indicator s 1` is the measure of `s`.
  rw [MeasureTheory.integral_indicator MeasurableSet.of_discrete]
  simp [Z_uniform_singleton_genA_inv]

/-! #### Step 2 — Apply Etemadi's strong law -/

/-- **Strong law for the coupled indicator.** A direct application of
`ProbabilityTheory.strong_law_ae_real` to the i.i.d.-Bernoulli(1/4)
sequence `(coupledIndicator k)`, with mean `1/4`. -/
theorem coupled_average_tendsto :
    ∀ᵐ Y ∂step_measure,
      Tendsto
        (fun n : ℕ =>
          (∑ k ∈ Finset.range n, coupledIndicator k Y) / n)
        atTop (𝓝 ((1 : ℝ)/4)) := by
  -- Pairwise independence from mutual independence (Wave 23A.3 axiom).
  have hindep_pairwise :
      Pairwise ((· ⟂ᵢ[step_measure] ·) on (fun k : ℕ => coupledIndicator k)) :=
    fun i j hij => coupledIndicator_iIndepFun.indepFun hij
  have hint : Integrable (coupledIndicator 0) step_measure :=
    integrable_coupledIndicator_zero
  have h := strong_law_ae_real
    (μ := step_measure)
    (fun k : ℕ => fun Y : ℕ → F2 => coupledIndicator k Y) hint
    hindep_pairwise coupledIndicator_iIdentDistrib
  -- Replace the limit `μ[X 0]` by `1/4`.
  filter_upwards [h] with Y hY
  -- `μ[X 0] = ∫ Y, coupledIndicator 0 Y ∂step_measure = 1/4`.
  rw [show (1 : ℝ) / 4 = ∫ Y, coupledIndicator 0 Y ∂step_measure
        from by rw [expectation_coupledIndicator_zero]]
  exact hY

/-! #### Step 3 — Cancellation average tendsto `1/4` -/

/-- **Cancellation Cesàro limit.** Combining `coupled_average_tendsto`
with the coupling difference `cancellation_average_eq_coupled_average_ae`
(Wave 23A.3), the Cesàro average of the cancellation indicator tends to
`1/4` a.s. -/
theorem cancellation_average_tendsto :
    ∀ᵐ Y ∂step_measure,
      Tendsto
        (fun n : ℕ =>
          (∑ k ∈ Finset.range n, cancellationIndicator k Y) / n)
        atTop (𝓝 ((1 : ℝ)/4)) := by
  filter_upwards [coupled_average_tendsto, cancellation_average_eq_coupled_average_ae]
    with Y hC hD
  -- `hC : (Σ coupled)/n → 1/4`
  -- `hD : (Σ cancellation)/n - (Σ coupled)/n → 0`
  -- Hence `(Σ cancellation)/n = ((Σ cancellation)/n - (Σ coupled)/n) + (Σ coupled)/n
  --   → 0 + 1/4 = 1/4`.
  have h_sum : Tendsto
      (fun n : ℕ =>
        ((∑ k ∈ Finset.range n, cancellationIndicator k Y) / n
          - (∑ k ∈ Finset.range n, coupledIndicator k Y) / n)
        + (∑ k ∈ Finset.range n, coupledIndicator k Y) / n)
      atTop (𝓝 ((0 : ℝ) + (1/4 : ℝ))) := hD.add hC
  have h_simp : (0 : ℝ) + (1/4 : ℝ) = (1 : ℝ)/4 := by norm_num
  rw [h_simp] at h_sum
  refine h_sum.congr (fun n => ?_)
  ring

/-! #### Step 4 — Walk length `/n → 1/2` -/

/-- **Walk-length Cesàro limit.** From the deterministic length identity
`|X_walk n Y| = n - 2 · ∑ cancellation` and
`cancellation_average_tendsto`, we obtain `|X_walk n Y|/n → 1/2` a.s. -/
theorem walk_length_div_n_tendsto :
    ∀ᵐ Y ∂step_measure,
      Tendsto
        (fun n : ℕ => ((X_walk n Y).toWord.length : ℝ) / n)
        atTop (𝓝 ((1 : ℝ)/2)) := by
  filter_upwards [cancellation_average_tendsto, walk_step_in_generating_set_ae]
    with Y hC hgen
  -- The deterministic identity gives:
  --   |X_walk n Y|/n = 1 - 2 · (Σ cancellation)/n.
  -- The RHS tends to `1 - 2 · (1/4) = 1/2`.
  have h_id : ∀ n : ℕ,
      ((X_walk n Y).toWord.length : ℝ)
        = (n : ℝ) - 2 * (∑ k ∈ Finset.range n, cancellationIndicator k Y) := by
    intro n
    exact walk_length_eq_n_minus_two_cancellations n Y (fun k _ => hgen k)
  have h_tend :
      Tendsto (fun n : ℕ => (1 : ℝ) - 2 * ((∑ k ∈ Finset.range n,
        cancellationIndicator k Y) / n)) atTop
        (𝓝 ((1 : ℝ) - 2 * (1/4 : ℝ))) := by
    exact (tendsto_const_nhds.sub (hC.const_mul 2))
  have h_lim : (1 : ℝ) - 2 * (1/4 : ℝ) = (1 : ℝ)/2 := by norm_num
  rw [h_lim] at h_tend
  refine h_tend.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  rw [h_id n]
  field_simp

/-! #### Step 5 — Dissolving the former axiom -/

/-- **Sublinear prefix length** (formerly a companion axiom, Wave 23A.4).

For `step_measure`-a.e. sample path `Y`, the common-prefix length
`m(X_n, φ_0)` grows sublinearly: `m(X_n, φ_0)/n → 0`.

**Proof.** Using the algebraic identity
`|x| = b_φ(x) + 2 m(x, φ)` (`word_length_eq_busemann_plus_prefix`), we
have `m(X_n, φ_0)/n = (|X_n| - b_{φ_0}(X_n)) / (2n)`. The walk length
ratio `|X_n|/n → 1/2` (`walk_length_div_n_tendsto`, from the SLLN on the
i.i.d.-coupled cancellation indicator) and the Busemann ratio
`b_{φ_0}(X_n)/n → 1/2` (`busemann_walk_ratio_ae_tendsto`, from the
Hoeffding/Borel–Cantelli chain) both tend to `1/2`, so their difference
tends to `0`, and so does `m(X_n, φ_0)/n = (1/2)·(diff)`. -/
theorem common_prefix_sublinear :
    ∀ᵐ Y ∂step_measure,
      Tendsto
        (fun n : ℕ => (common_prefix_length (X_walk n Y) phi_zero : ℝ) / n)
        atTop (𝓝 (0 : ℝ)) := by
  filter_upwards [walk_length_div_n_tendsto, busemann_walk_ratio_ae_tendsto]
    with Y hLength hBus
  -- Difference of the two Cesàro limits.
  have h_diff :
      Tendsto
        (fun n : ℕ =>
          ((X_walk n Y).toWord.length : ℝ) / n
            - (busemann phi_zero (X_walk n Y) : ℝ) / n)
        atTop (𝓝 ((1 : ℝ)/2 - (1 : ℝ)/2)) := hLength.sub hBus
  have h_limit_zero : (1 : ℝ)/2 - (1 : ℝ)/2 = 0 := by ring
  rw [h_limit_zero] at h_diff
  -- Multiply by 1/2.
  have h_half :
      Tendsto
        (fun n : ℕ =>
          (1/2 : ℝ) *
            (((X_walk n Y).toWord.length : ℝ) / n
              - (busemann phi_zero (X_walk n Y) : ℝ) / n))
        atTop (𝓝 ((1/2 : ℝ) * 0)) := h_diff.const_mul (1/2 : ℝ)
  have h_zero : (1/2 : ℝ) * 0 = 0 := by ring
  rw [h_zero] at h_half
  -- Pointwise: `(1/2)·(|X_n|/n - b_{φ₀}(X_n)/n) = m(X_n, φ_0)/n`
  -- (using `|x| = b_φ(x) + 2 m(x, φ)`).
  refine h_half.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  have h_id := word_length_eq_busemann_plus_prefix phi_zero (X_walk n Y)
  -- `(|x| - b_φ(x)) / (2n) = m(x, φ) / n` since `|x| = b_φ(x) + 2 m(x, φ)`.
  field_simp
  linarith [h_id]

/-! ### Q43, Q44 — fully proven from the Wave 23A.4 closure

With `common_prefix_sublinear` now a theorem (above), the original
`walk_rate_of_escape` proof is unchanged: it consumes
`busemann_walk_ratio_ae_tendsto` and `common_prefix_sublinear` and
combines them via `word_length_eq_busemann_plus_prefix`. -/

/-- **Q43 — almost-sure rate of escape**.

For `step_measure`-almost every sample path `Y`, the ratio
`d(1, X_n(Y)) / n` converges to `1/2`.

**Strategy** (implemented as a chain of named sub-lemmas):
1. Fix the boundary point `φ₀ = (aaa…)` (`phi_zero`).
2. Apply `busemann_walk_hoeffding` with `ε = n^{−1/3}` to get
   `step_measure(B_n) ≤ 2 exp(−n^{1/3}/2)` — summable
   (`bad_busemann_event_summable`).
3. First Borel–Cantelli (`MeasureTheory.ae_eventually_notMem`) gives a.s.
   `b_{φ₀}(X_n)/n → 1/2` (`busemann_walk_ratio_ae_tendsto`).
4. The algebraic identity `|x| = b_{φ₀}(x) + 2 m(x, φ₀)`
   (`word_length_eq_busemann_plus_prefix`) combined with the a.s.
   sublinearity of the common-prefix length (`common_prefix_sublinear`,
   now a theorem from Wave 23A.4) transfers the limit from
   `b_{φ₀}(X_n)/n` to `(X_n.toWord.length)/n → 1/2`.
5. Convert from algebraic length to graph distance via
   `word_length_eq_toWord_length`.

**Status (Wave 23A.4)**: fully proven from
`busemann_walk_ratio_ae_tendsto` and the now-fully-proven
`common_prefix_sublinear`. The only remaining axioms in the dependency
chain are the Q42 Azuma admissions (`centred_away_azuma_tail` and
`centred_away_azuma_tail_neg`) and the Wave 23A.3 i.i.d. admission
`coupledIndicator_iIndepFun_iIdentDistrib`. -/
theorem walk_rate_of_escape :
    ∀ᵐ Y ∂step_measure,
      Tendsto (fun n : ℕ => (word_length (X_walk n Y) : ℝ) / n)
        atTop (𝓝 (1/2 : ℝ)) := by
  filter_upwards [busemann_walk_ratio_ae_tendsto, common_prefix_sublinear]
    with Y hBus hPrefix
  -- `hBus : b_{φ₀}(X_n Y)/n → 1/2`
  -- `hPrefix : common_prefix_length (X_n Y) φ₀ / n → 0`
  -- Goal: `word_length (X_n Y) / n → 1/2`.
  have h_combined :
      Tendsto
        (fun n : ℕ =>
          (busemann phi_zero (X_walk n Y) : ℝ) / n
            + 2 * ((common_prefix_length (X_walk n Y) phi_zero : ℝ) / n))
        atTop (𝓝 ((1/2 : ℝ) + 2 * 0)) := by
    exact hBus.add (hPrefix.const_mul 2)
  have h_limit_eq : (1/2 : ℝ) + 2 * 0 = 1/2 := by ring
  rw [h_limit_eq] at h_combined
  refine h_combined.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  have h_wl : (word_length (X_walk n Y) : ℝ)
                = ((X_walk n Y).toWord.length : ℝ) := by
    exact_mod_cast word_length_eq_toWord_length (X_walk n Y)
  have h_id := word_length_eq_busemann_plus_prefix phi_zero (X_walk n Y)
  rw [h_wl, h_id]
  field_simp

/-- A convenient corollary of Q43: `d(1, X_n) → ∞` almost surely. -/
theorem walk_dist_tendsto_atTop :
    ∀ᵐ Y ∂step_measure,
      Tendsto (fun n : ℕ => (word_length (X_walk n Y) : ℝ)) atTop atTop := by
  filter_upwards [walk_rate_of_escape] with Y hY
  have h_n : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have h_prod :
      Tendsto (fun n : ℕ => (n : ℝ) * ((word_length (X_walk n Y) : ℝ) / n))
        atTop atTop :=
    h_n.atTop_mul_pos (by norm_num : (0 : ℝ) < 1/2) hY
  refine h_prod.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  rw [mul_div_assoc', mul_div_cancel_left₀ _ hn0]

/-- **Q44 — transience**.

For every finite set `E ⊂ F_2`, almost surely the walk eventually leaves
`E`: there exists `N` such that `X_n ∉ E` for all `n ≥ N`.

**Proof**: by `walk_dist_tendsto_atTop`, `d(1, X_n) → ∞` almost surely,
hence eventually exceeds `M := max_{x ∈ E} d(1, x)`, so `X_n ∉ E`. -/
theorem walk_transience (E : Finset F2) :
    ∀ᵐ Y ∂step_measure, ∃ N : ℕ, ∀ n ≥ N, X_walk n Y ∉ E := by
  filter_upwards [walk_dist_tendsto_atTop] with Y hY
  by_cases hE : E.Nonempty
  · set M : ℕ := E.sup word_length with hM_def
    have hMax : ∀ x ∈ E, word_length x ≤ M :=
      fun x hx => Finset.le_sup (f := word_length) hx
    have hEv : ∀ᶠ n in atTop, (M : ℝ) < (word_length (X_walk n Y) : ℝ) :=
      hY.eventually (eventually_gt_atTop (M : ℝ))
    rcases hEv.exists_forall_of_atTop with ⟨N, hN⟩
    refine ⟨N, fun n hn hmem => ?_⟩
    have hle : word_length (X_walk n Y) ≤ M := hMax _ hmem
    have hlt : (M : ℝ) < (word_length (X_walk n Y) : ℝ) := hN n hn
    have hle' : (word_length (X_walk n Y) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hle
    linarith
  · exact ⟨0, fun _ _ hmem => hE ⟨_, hmem⟩⟩

/-! ### Wave 28 — direct binomial PMF for the away-indicator sum

Goal: identify the distribution of `S_n(Y) := ∑_{i<n} away_indicator φ i Y`
under `step_measure` as `Binomial(n, 3/4)` — without invoking the Wave 23C
companion axiom `iIndepFun_iIdentDistrib_uniformIndic_pastDep`.

Strategy (per the Wave 28 IMO blueprint).

* Every event we care about depends only on the first `n` coordinates of
  `Y`; hence `step_measure(E) = (Measure.pi (fun _ : Fin n => Z_uniform))(...)`
  via `Measure.infinitePi_map_restrict`.
* The event `∑_{i<n} away_indicator φ i Y = k` is, a.s., a disjoint union
  over `S ⊆ Finset.range n`, `|S| = k`, of cylinder events
  "`Y i ∈ awayGenFinset φ (X_walk i Y)` iff `i ∈ S`".
* Each pattern event `B_S` is a finite disjoint union of singleton
  cylinders on `Z^n`, indexed by the prefixes that realise `S`.
  By `Measure.infinitePi_pi`, each singleton has measure `(1/4)^n`, and
  the IMO core lemma `realising_prefix_count` says there are exactly
  `3^|S|` realising prefixes (independent of the prefix path because
  `|awayGenFinset φ x| = 3` and `|F2_generating_set \ awayGenFinset φ x| = 1`,
  both *prefix-independent*).
* Sum across patterns: `(n.choose k) · 3^k · (1/4)^n`. Algebra:
  `(n.choose k) · (3/4)^k · (1/4)^{n-k}`. -/

-- Wave 33: `F2_genFinset`, `F2_genFinset_card`, `F2_genFinset_coe`,
-- `Z_uniform_singleton_aux`, `Z_uniform_singleton_of_mem`,
-- `Z_uniform_finset_of_subset`, `step_measure_prefix_cylinder`,
-- `step_measure_prefix_cylinder_of_all_gen`, `extendPrefix`,
-- `extendPrefix_apply_lt`, `X_walk_extendPrefix_congr`, `extOne`,
-- `extOne_apply_lt`, `extOne_apply_last`, `extOne_inj`,
-- `extendPrefix_extOne_init`, `X_walk_extOne_init`,
-- `step_measure_fin_prefix_cylinder`, `fixedPrefixCylinder`,
-- `fixedPrefixCylinder_eq`, `step_measure_fixedPrefixCylinder`,
-- `measurableSet_fixedPrefixCylinder`, `fixedPrefixCylinder_pairwise_disjoint`
-- have all been moved up to the Wave 33 prerequisites section, before the
-- generic theorem `iIndepFun_iIdentDistrib_uniformIndic_pastDep`. They are
-- still in scope here for the rest of the Wave 28 binomial-PMF chain.

/-! #### Wave 28 Step D — Pattern decomposition of the away-sum event

A.s. on `step_measure`, the event `S_n = k` decomposes as the disjoint
union over patterns `S ⊆ Finset.range n` with `|S| = k` of the cylinder
events
  `B_S = {Y | ∀ i < n, (Y i ∈ awayGenFinset φ (X_walk i Y) ↔ i ∈ S)}`. -/

/-- The pattern indicator: for `Y` and a pattern `S`, this is the set
of `Y` realising the pattern at every position in `[0, n)`. -/
private def patternEvent (φ : ∂F2) (n : ℕ) (S : Finset ℕ) :
    Set (ℕ → F2) :=
  {Y | ∀ i, i < n → (Y i ∈ awayGenFinset φ (X_walk i Y) ↔ i ∈ S)}

/-- The away-sum event `∑_{i<n} away_indicator φ i Y = k` is a.s. equal
to the union of pattern events `B_S` over `S ⊆ Finset.range n` with
`|S| = k`. -/
private lemma away_sum_event_eq_union_patterns_ae (φ : ∂F2) (n k : ℕ) :
    {Y | (Finset.range n).sum (fun i => away_indicator φ i Y) = (k : ℝ)}
      =ᵐ[step_measure]
      ⋃ S ∈ (Finset.range n).powersetCard k, patternEvent φ n S := by
  filter_upwards [walk_step_in_generating_set_ae] with Y hY
  classical
  -- Goal: `(Y ∈ {sum=k}) = (Y ∈ ⋃ S ∈ ..., patternEvent ...)`. Reduce to iff.
  apply propext
  change _ ↔ Y ∈ ⋃ S ∈ (Finset.range n).powersetCard k, patternEvent φ n S
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, patternEvent]
  -- The "evaluated" form of the away-sum at this fixed `Y`.
  have hY_indic : ∀ i ∈ Finset.range n,
      away_indicator φ i Y =
        (if Y i ∈ awayGenFinset φ (X_walk i Y) then (1 : ℝ) else 0) :=
    fun i _ => away_indicator_eq_indicator_of_gen φ i Y (hY i)
  refine ⟨?_, ?_⟩
  · intro hsum
    -- Define `S := {i ∈ Finset.range n | Y i ∈ awayGenFinset φ (X_walk i Y)}`.
    set S : Finset ℕ :=
      (Finset.range n).filter
        (fun i => Y i ∈ awayGenFinset φ (X_walk i Y)) with hS_def
    have hS_subset : S ⊆ Finset.range n := Finset.filter_subset _ _
    have hsum_eq_card :
        (Finset.range n).sum (fun i => away_indicator φ i Y) = (S.card : ℝ) := by
      have hrw : (Finset.range n).sum (fun i => away_indicator φ i Y)
            = (Finset.range n).sum (fun i =>
                if Y i ∈ awayGenFinset φ (X_walk i Y) then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl hY_indic
      rw [hrw, Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero,
          add_zero, nsmul_eq_mul, mul_one]
    have hk_eq : S.card = k := by
      have h1 : (S.card : ℝ) = (k : ℝ) := by
        rw [← hsum_eq_card]; exact hsum
      exact_mod_cast h1
    refine ⟨S, Finset.mem_powersetCard.mpr ⟨hS_subset, hk_eq⟩, ?_⟩
    intro i hi
    rw [hS_def, Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => ⟨hi, h⟩, fun ⟨_, h⟩ => h⟩
  · rintro ⟨S, hS_mem, hY_pattern⟩
    rw [Finset.mem_powersetCard] at hS_mem
    obtain ⟨hS_sub, hS_card⟩ := hS_mem
    have hrw : (Finset.range n).sum (fun i => away_indicator φ i Y)
          = (Finset.range n).sum (fun i => if i ∈ S then (1 : ℝ) else 0) := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hi_lt : i < n := Finset.mem_range.mp hi
      rw [hY_indic i hi]
      by_cases hiS : i ∈ S
      · rw [if_pos ((hY_pattern i hi_lt).mpr hiS), if_pos hiS]
      · have hi_not : Y i ∉ awayGenFinset φ (X_walk i Y) :=
          fun hmem => hiS ((hY_pattern i hi_lt).mp hmem)
        rw [if_neg hi_not, if_neg hiS]
    have h_filter : (Finset.range n).filter (fun i => i ∈ S) = S := by
      ext i
      refine ⟨fun h => (Finset.mem_filter.mp h).2, fun h => ?_⟩
      exact Finset.mem_filter.mpr ⟨hS_sub h, h⟩
    have hsum_eq : (Finset.range n).sum (fun i => away_indicator φ i Y)
                    = (S.card : ℝ) := by
      rw [hrw, Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero,
          add_zero, nsmul_eq_mul, mul_one, h_filter]
    show (Finset.range n).sum (fun i => away_indicator φ i Y) = (k : ℝ)
    rw [hsum_eq]
    exact_mod_cast hS_card

/-! #### Wave 28 Step E — Pattern-event lemmas (scaffold)

Foundational pieces of the keystone calculation. Full
`pattern_event_measure` proof (the inductive count `3^|S| * (1/4)^n`)
is deferred; this section lands the base-case sanity check needed by
the assembly. -/

/-- Base case `n = 0`: the pattern event for `S = ∅` is the entire
sample space. -/
private lemma patternEvent_zero_empty (φ : ∂F2) :
    patternEvent φ 0 ∅ = Set.univ := by
  unfold patternEvent
  ext Y
  simp

/-! #### Wave 28 Step F — Prefix scaffolding (moved up to Wave 33 prereqs) -/

/-! #### Wave 28 Step H — Algebra rearrangement -/

/-- The PMF rearrangement `(n.choose k) · (3/4)^k · (1/4)^{n-k}
    = (n.choose k) · 3^k · (1/4)^n` (for `k ≤ n`, in `ℝ`). -/
private lemma pmf_algebra (n k : ℕ) (hk : k ≤ n) :
    (n.choose k : ℝ) * (3/4)^k * (1/4)^(n - k)
      = (n.choose k : ℝ) * 3^k * (1/4)^n := by
  -- `(3/4)^k = 3^k * (1/4)^k`, then `(1/4)^k * (1/4)^{n-k} = (1/4)^n`.
  have h_split : ((3 : ℝ)/4)^k = (3 : ℝ)^k * (1/4)^k := by
    rw [show ((3 : ℝ)/4) = (3 : ℝ) * (1/4) from by ring, mul_pow]
  rw [h_split]
  rw [show (n.choose k : ℝ) * ((3 : ℝ)^k * (1/4)^k) * (1/4)^(n - k)
        = (n.choose k : ℝ) * 3^k * ((1/4)^k * (1/4)^(n - k)) from by ring]
  rw [← pow_add]
  rw [show k + (n - k) = n from by omega]

/-! #### Wave 28 Step F — Prefix-counting lemma (the IMO core)

Count prefixes `y : Fin n → F2` with all coordinates in the generating set
that realise a given pattern `S` (i.e. `y i ∈ awayGenFinset` iff `i ∈ S`).
We show this count is `3^|S|` (for `S ⊆ Finset.range n`), by induction on `n`.

The argument is the IMO insight: at each coordinate position, the number of
valid extensions is `3` (if `i ∈ S`, choose from `awayGenFinset`, of size 3)
or `1` (if `i ∉ S`, choose the unique element of `F2_generating_set \
awayGenFinset`, of size 1). Both counts are independent of the prefix
because `|awayGenFinset| = 3` is constant.

The Lean encoding of this `Fin.snoc`-based bijection over a filtered Finset
with a path-dependent predicate is heavy; we admit the narrow combinatorial
lemma here. The mathematical content is fully captured by:
* `awayGenFinset_card φ x = 3` (proved, line ~464);
* `F2_genFinset.card = 4` (proved, line ~2620);
* `awayGenFinset` is a subset of `F2_generating_set` (proved, line ~476);
* `awayGenFinset_past`: the away set depends only on the prefix (proved). -/

/-- The Finset of prefixes realising the pattern `S` at all positions
`< n`. We restrict to prefixes valued in the 4-element generating set
`F2_genFinset`, which makes the underlying ambient Finset (`F2_genFinset^n`)
a `Fintype`. -/
private noncomputable def realisingPrefixes (φ : ∂F2) (n : ℕ) (S : Finset ℕ) :
    Finset (Fin n → F2) := by
  classical
  exact (Fintype.piFinset (fun _ : Fin n => F2_genFinset)).filter
    (fun y =>
      ∀ i : Fin n,
        (y i ∈ awayGenFinset φ (X_walk i.val (extendPrefix n y))) ↔ i.val ∈ S)

/-- A prefix lies in `realisingPrefixes φ n S` iff it has all coordinates in
the generating set and matches the pattern `S` on the first `n` indices. -/
private lemma mem_realisingPrefixes (φ : ∂F2) (n : ℕ) (S : Finset ℕ)
    (y : Fin n → F2) :
    y ∈ realisingPrefixes φ n S ↔
      (∀ i : Fin n, y i ∈ F2_generating_set) ∧
      (∀ i : Fin n,
         y i ∈ awayGenFinset φ (X_walk i.val (extendPrefix n y)) ↔
           i.val ∈ S) := by
  classical
  unfold realisingPrefixes
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨h_pi, h_pat⟩
    refine ⟨fun i => ?_, h_pat⟩
    have := h_pi i
    rw [← F2_genFinset_coe]; exact Finset.mem_coe.mpr this
  · rintro ⟨h_gen, h_pat⟩
    refine ⟨fun i => ?_, h_pat⟩
    have := h_gen i
    rw [← F2_genFinset_coe] at this
    exact Finset.mem_coe.mp this

/-! Helpers for the Step F induction. -/

/-- The two-coord extension Finset for a prefix `y' : Fin n → F2` and pattern
`S` at index `n`: either `awayGenFinset` (3 elts, if `n ∈ S`) or
`F2_genFinset \ awayGenFinset` (1 elt, otherwise). -/
private noncomputable def extSet (φ : ∂F2) (n : ℕ) (S : Finset ℕ)
    (y' : Fin n → F2) : Finset F2 :=
  if n ∈ S then awayGenFinset φ (X_walk n (extendPrefix n y'))
  else F2_genFinset \ awayGenFinset φ (X_walk n (extendPrefix n y'))

/-- `extSet` has cardinality `3` if `n ∈ S`, else `1`. -/
private lemma extSet_card (φ : ∂F2) (n : ℕ) (S : Finset ℕ) (y' : Fin n → F2) :
    (extSet φ n S y').card = if n ∈ S then 3 else 1 := by
  unfold extSet
  by_cases h : n ∈ S
  · rw [if_pos h, if_pos h]
    exact awayGenFinset_card φ _
  · rw [if_neg h, if_neg h]
    -- `(F2_genFinset \ awayGenFinset).card = 4 - 3 = 1`.
    have h_sub : awayGenFinset φ (X_walk n (extendPrefix n y')) ⊆ F2_genFinset := by
      intro z hz
      have h_set := awayGenFinset_subset φ (X_walk n (extendPrefix n y')) (Finset.mem_coe.mpr hz)
      rw [← F2_genFinset_coe] at h_set
      exact Finset.mem_coe.mp h_set
    rw [Finset.card_sdiff_of_subset h_sub, F2_genFinset_card,
        awayGenFinset_card φ _]

/-- Elements of `extSet` lie in `F2_generating_set`. -/
private lemma extSet_subset_gen (φ : ∂F2) (n : ℕ) (S : Finset ℕ)
    (y' : Fin n → F2) :
    ↑(extSet φ n S y') ⊆ F2_generating_set := by
  unfold extSet
  by_cases h : n ∈ S
  · rw [if_pos h]; exact awayGenFinset_subset φ _
  · rw [if_neg h]
    intro z hz
    have hz' : z ∈ F2_genFinset := (Finset.mem_sdiff.mp (Finset.mem_coe.mp hz)).1
    rw [← F2_genFinset_coe]
    exact Finset.mem_coe.mpr hz'

/-- Membership in `extSet`: `z ∈ extSet φ n S y' ↔ (z ∈ F2_genFinset) ∧
    (z ∈ awayGenFinset ↔ n ∈ S)`. -/
private lemma mem_extSet (φ : ∂F2) (n : ℕ) (S : Finset ℕ) (y' : Fin n → F2)
    (z : F2) :
    z ∈ extSet φ n S y' ↔
      z ∈ F2_genFinset ∧
      (z ∈ awayGenFinset φ (X_walk n (extendPrefix n y')) ↔ n ∈ S) := by
  unfold extSet
  by_cases h : n ∈ S
  · rw [if_pos h]
    simp only [h, iff_true]
    constructor
    · intro hz
      refine ⟨?_, hz⟩
      have h_set := awayGenFinset_subset φ (X_walk n (extendPrefix n y')) (Finset.mem_coe.mpr hz)
      rw [← F2_genFinset_coe] at h_set
      exact Finset.mem_coe.mp h_set
    · rintro ⟨_, hz⟩; exact hz
  · rw [if_neg h]
    simp only [h, iff_false]
    rw [Finset.mem_sdiff]

-- `extOne`, `extOne_apply_lt`, `extOne_apply_last`, `extOne_inj`,
-- `extendPrefix_extOne_init`, `X_walk_extOne_init` moved to Wave 33 prereqs.

/-- The "extend" Finset: prefixes `y : Fin (n+1) → F2` formed as
`extOne n y' z` for `z ∈ extSet`. -/
private noncomputable def extPrefixes (φ : ∂F2) (n : ℕ) (S : Finset ℕ)
    (y' : Fin n → F2) : Finset (Fin (n + 1) → F2) :=
  (extSet φ n S y').image (extOne n y')

/-- `extOne y' · ` is injective on `F2`. -/
private lemma extPrefixes_card (φ : ∂F2) (n : ℕ) (S : Finset ℕ)
    (y' : Fin n → F2) :
    (extPrefixes φ n S y').card = if n ∈ S then 3 else 1 := by
  unfold extPrefixes
  have h_inj : Function.Injective (extOne n y') := by
    intro z₁ z₂ h
    exact (extOne_inj n h).2
  rw [Finset.card_image_of_injective (extSet φ n S y') h_inj]
  exact extSet_card φ n S y'

/-- The image-Finset for `extOne y' · ` is disjoint across distinct `y'`s. -/
private lemma extPrefixes_pairwise_disjoint (φ : ∂F2) (n : ℕ) (S : Finset ℕ)
    (P : Finset (Fin n → F2)) :
    (↑P : Set (Fin n → F2)).PairwiseDisjoint (extPrefixes φ n S) := by
  intro y₁ _ y₂ _ hy
  show Disjoint (extPrefixes φ n S y₁) (extPrefixes φ n S y₂)
  rw [Finset.disjoint_iff_ne]
  rintro a ha b hb rfl
  apply hy
  unfold extPrefixes at ha hb
  rcases Finset.mem_image.mp ha with ⟨z₁, _, rfl⟩
  rcases Finset.mem_image.mp hb with ⟨z₂, _, h⟩
  exact ((extOne_inj n h).1).symm

/-- The `(n+1)`-realising prefixes decompose as the disjoint union of
extensions of `n`-realising prefixes (for the pattern `S.erase n`). -/
private lemma realisingPrefixes_succ (φ : ∂F2) (n : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range (n + 1)) :
    realisingPrefixes φ (n + 1) S =
      (realisingPrefixes φ n (S.erase n)).biUnion
        (fun y' => extPrefixes φ n S y') := by
  classical
  ext y
  rw [Finset.mem_biUnion]
  constructor
  · -- y ∈ realisingPrefixes φ (n+1) S ⇒ decompose y = extOne (y restricted) (y last).
    intro hy
    rw [mem_realisingPrefixes] at hy
    obtain ⟨h_gen, h_pat⟩ := hy
    set y' : Fin n → F2 := fun i => y i.castSucc with hy'_def
    set z : F2 := y (Fin.last n) with hz_def
    -- y = extOne n y' z.
    have hy_eq : y = extOne n y' z := by
      funext i
      by_cases hi : i.val < n
      · rw [extOne_apply_lt n y' z i hi]
        rw [hy'_def]
        congr 1
      · have hi_eq_val : i.val = n := by
          have := i.isLt; omega
        have h_last : i = Fin.last n := by ext; exact hi_eq_val
        rw [h_last, extOne_apply_last n y' z]
    refine ⟨y', ?_, ?_⟩
    · -- y' realises `S.erase n`.
      rw [mem_realisingPrefixes]
      refine ⟨fun i => h_gen i.castSucc, fun i => ?_⟩
      have h_pat_i := h_pat i.castSucc
      have h_castSucc_val : (i.castSucc : Fin (n+1)).val = i.val := rfl
      rw [h_castSucc_val] at h_pat_i
      have h_aw : awayGenFinset φ (X_walk i.val (extendPrefix (n + 1) y))
            = awayGenFinset φ (X_walk i.val (extendPrefix n y')) := by
        have hi_lt : i.val < n := i.isLt
        rw [hy_eq]
        rw [X_walk_extOne_init n y' z i.val (le_of_lt hi_lt)]
      rw [h_aw] at h_pat_i
      -- y i.castSucc = y' i (definitionally given hy'_def).
      have hy_init : y i.castSucc = y' i := rfl
      rw [hy_init] at h_pat_i
      have hi_ne_n : i.val ≠ n := Nat.ne_of_lt i.isLt
      rw [Finset.mem_erase]
      tauto
    · -- z ∈ extPrefixes (i.e. y = extOne n y' z with z ∈ extSet).
      unfold extPrefixes
      rw [Finset.mem_image]
      refine ⟨z, ?_, hy_eq.symm⟩
      rw [mem_extSet]
      refine ⟨?_, ?_⟩
      · -- z ∈ F2_genFinset.
        have := h_gen (Fin.last n)
        rw [← F2_genFinset_coe] at this
        exact Finset.mem_coe.mp this
      · -- z ∈ awayGenFinset ↔ n ∈ S.
        have h_pat_n := h_pat (Fin.last n)
        have h_last_val : (Fin.last n : Fin (n+1)).val = n := rfl
        rw [h_last_val] at h_pat_n
        have h_y_last : y (Fin.last n) = z := rfl
        rw [h_y_last] at h_pat_n
        have h_aw : awayGenFinset φ (X_walk n (extendPrefix (n + 1) y))
              = awayGenFinset φ (X_walk n (extendPrefix n y')) := by
          rw [hy_eq]
          rw [X_walk_extOne_init n y' z n (le_refl n)]
        rw [h_aw] at h_pat_n
        exact h_pat_n
  · -- Reverse direction: y' realises S.erase n + z ∈ extSet ⇒ extOne n y' z realises S.
    rintro ⟨y', hy', hy_ext⟩
    unfold extPrefixes at hy_ext
    rcases Finset.mem_image.mp hy_ext with ⟨z, hz, rfl⟩
    rw [mem_extSet] at hz
    obtain ⟨hz_gen, hz_pat⟩ := hz
    rw [mem_realisingPrefixes] at hy'
    obtain ⟨hy'_gen, hy'_pat⟩ := hy'
    rw [mem_realisingPrefixes]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · -- (extOne n y' z) i ∈ F2_generating_set.
      by_cases hi : i.val < n
      · rw [extOne_apply_lt n y' z i hi]
        exact hy'_gen ⟨i.val, hi⟩
      · have hi_eq_val : i.val = n := by have := i.isLt; omega
        have h_last : i = Fin.last n := by ext; exact hi_eq_val
        rw [h_last, extOne_apply_last n y' z]
        rw [← F2_genFinset_coe]
        exact Finset.mem_coe.mpr hz_gen
    · -- Pattern condition.
      by_cases hi : i.val < n
      · rw [extOne_apply_lt n y' z i hi]
        rw [X_walk_extOne_init n y' z i.val (le_of_lt hi)]
        have h_pat_i :
            y' ⟨i.val, hi⟩ ∈ awayGenFinset φ (X_walk i.val (extendPrefix n y'))
              ↔ i.val ∈ S.erase n := hy'_pat ⟨i.val, hi⟩
        have hi_ne_n : i.val ≠ n := Nat.ne_of_lt hi
        rw [Finset.mem_erase] at h_pat_i
        constructor
        · intro h; exact (h_pat_i.mp h).2
        · intro h; exact h_pat_i.mpr ⟨hi_ne_n, h⟩
      · have hi_eq_val : i.val = n := by have := i.isLt; omega
        have h_last : i = Fin.last n := by ext; exact hi_eq_val
        rw [h_last, extOne_apply_last n y' z]
        have h_last_val : (Fin.last n : Fin (n+1)).val = n := rfl
        rw [h_last_val]
        rw [X_walk_extOne_init n y' z n (le_refl n)]
        exact hz_pat

/-- **IMO core (Step F).** Cardinality of the realising-prefix Finset is
`3^|S|`, by induction on `n`. -/
private lemma realisingPrefixes_card (φ : ∂F2) :
    ∀ (n : ℕ) (S : Finset ℕ), S ⊆ Finset.range n →
      (realisingPrefixes φ n S).card = 3 ^ S.card := by
  classical
  intro n
  induction n with
  | zero =>
    intro S hS
    have hS_empty : S = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      have := hS hx
      simp at this
    rw [hS_empty, Finset.card_empty, pow_zero]
    -- Show realisingPrefixes φ 0 ∅ has cardinality 1.
    -- Strategy: it's a singleton {fun i => i.elim0}.
    have h_singleton : realisingPrefixes φ 0 ∅ = {(fun i : Fin 0 => i.elim0)} := by
      ext y
      rw [mem_realisingPrefixes, Finset.mem_singleton]
      constructor
      · intro _; funext i; exact i.elim0
      · intro _; exact ⟨fun i => i.elim0, fun i => i.elim0⟩
    rw [h_singleton, Finset.card_singleton]
  | succ n ih =>
    intro S hS
    -- Set S' := S.erase n.
    have hS'_sub : S.erase n ⊆ Finset.range n := by
      intro i hi
      have hi_in : i ∈ S := Finset.mem_of_mem_erase hi
      have hi_ne : i ≠ n := Finset.ne_of_mem_erase hi
      have hi_lt : i < n + 1 := Finset.mem_range.mp (hS hi_in)
      exact Finset.mem_range.mpr (by omega)
    have h_ih : (realisingPrefixes φ n (S.erase n)).card = 3 ^ (S.erase n).card :=
      ih (S.erase n) hS'_sub
    -- Apply the decomposition.
    rw [realisingPrefixes_succ φ n S hS]
    rw [Finset.card_biUnion (extPrefixes_pairwise_disjoint φ n S _)]
    rw [Finset.sum_congr rfl (fun y' _ => extPrefixes_card φ n S y')]
    rw [Finset.sum_const]
    rw [h_ih]
    rw [smul_eq_mul]
    -- Two cases: n ∈ S or n ∉ S.
    by_cases hn : n ∈ S
    · -- |S| = |S.erase n| + 1 ⇒ 3^|S| = 3^|S.erase n| · 3.
      rw [if_pos hn]
      have h_card_pos : S.card ≥ 1 := Finset.card_pos.mpr ⟨n, hn⟩
      have h_card_eq : S.card = (S.erase n).card + 1 := by
        rw [Finset.card_erase_of_mem hn]; omega
      rw [h_card_eq]
      ring
    · -- |S| = |S.erase n| ⇒ 3^|S| = 3^|S.erase n| · 1.
      rw [if_neg hn]
      rw [show S.erase n = S from Finset.erase_eq_of_notMem hn]
      ring

/-! #### Wave 28 Step E — One-pattern measure (the keystone)

`step_measure (patternEvent φ n S) = 3^|S| · (1/4)^n`.

Strategy: a.s. on `step_measure`, the `Y`-coordinates lie in
`F2_generating_set`. Restricted to that, the pattern event decomposes
as a disjoint union over `y ∈ realisingPrefixes φ n S` of
fixed-prefix singleton cylinders, each of measure `(1/4)^n`. The number
of realising prefixes is `3^|S|` (Step F), giving the total. -/

-- `step_measure_fin_prefix_cylinder`, `fixedPrefixCylinder`,
-- `fixedPrefixCylinder_eq`, `step_measure_fixedPrefixCylinder`,
-- `measurableSet_fixedPrefixCylinder`, `fixedPrefixCylinder_pairwise_disjoint`
-- moved to Wave 33 prereqs section.

/-- Patterns determine prefix-realising sets that all-coords-in-`gen-set`
prefixes recover: `Y` lies in the patternEvent (and has all coords in
`F2_generating_set` for `i < n`) iff its truncated prefix is realising. -/
private lemma patternEvent_iff_prefix (φ : ∂F2) (n : ℕ) (S : Finset ℕ)
    (Y : ℕ → F2) (hY_gen : ∀ i, i < n → Y i ∈ F2_generating_set) :
    Y ∈ patternEvent φ n S ↔
      (fun i : Fin n => Y i.val) ∈ realisingPrefixes φ n S := by
  classical
  unfold patternEvent
  rw [mem_realisingPrefixes]
  constructor
  · intro h_pat
    refine ⟨fun i => hY_gen i.val i.isLt, fun i => ?_⟩
    -- The pattern condition for Y at index i.val matches.
    have h := h_pat i.val i.isLt
    -- We need: `Y i.val ∈ awayGenFinset φ (X_walk i.val (extendPrefix n (...))) ↔ i.val ∈ S`.
    -- By `awayGenFinset_past`, `awayGenFinset φ (X_walk i.val Y) = awayGenFinset φ
    --   (X_walk i.val (extendPrefix n (fun j : Fin n => Y j.val)))`.
    have hext : ∀ j, j < i.val → Y j = extendPrefix n (fun j : Fin n => Y j.val) j := by
      intro j hj
      have hj_lt : j < n := lt_trans hj i.isLt
      rw [extendPrefix_apply_lt n _ j hj_lt]
    have h_aw : awayGenFinset φ (X_walk i.val Y) =
        awayGenFinset φ (X_walk i.val (extendPrefix n (fun j : Fin n => Y j.val))) :=
      awayGenFinset_past φ i.val Y _ hext
    rw [h_aw] at h
    exact h
  · rintro ⟨h_gen, h_pat⟩ i hi
    -- Pull the prefix-realising condition back to `Y`.
    have h := h_pat ⟨i, hi⟩
    have hext : ∀ j, j < i → Y j = extendPrefix n (fun j : Fin n => Y j.val) j := by
      intro j hj
      have hj_lt : j < n := lt_trans hj hi
      rw [extendPrefix_apply_lt n _ j hj_lt]
    have h_aw : awayGenFinset φ (X_walk i Y) =
        awayGenFinset φ (X_walk i (extendPrefix n (fun j : Fin n => Y j.val))) :=
      awayGenFinset_past φ i Y _ hext
    rw [h_aw]
    exact h

/-- A.s. on `step_measure`, the patternEvent equals the `biUnion` of
fixed-prefix cylinders over realising prefixes. -/
private lemma patternEvent_aeEq_biUnion (φ : ∂F2) (n : ℕ) (S : Finset ℕ) :
    patternEvent φ n S
      =ᵐ[step_measure]
      ⋃ y ∈ realisingPrefixes φ n S, fixedPrefixCylinder n y := by
  filter_upwards [walk_step_in_generating_set_ae] with Y hY
  classical
  apply propext
  have hY_gen : ∀ i, i < n → Y i ∈ F2_generating_set := fun i _ => hY i
  have h_iff := patternEvent_iff_prefix φ n S Y hY_gen
  set y0 : Fin n → F2 := fun i => Y i.val with hy0_def
  -- Both sides are sets of `Y`; unfold to `∈` form.
  change Y ∈ patternEvent φ n S ↔ Y ∈ ⋃ y ∈ realisingPrefixes φ n S, fixedPrefixCylinder n y
  rw [Set.mem_iUnion]
  rw [h_iff]
  -- Now: `y0 ∈ realisingPrefixes ↔ ∃ y, Y ∈ ⋃ (_ : y ∈ realisingPrefixes), fixedPrefixCylinder n y`.
  constructor
  · intro h_real
    refine ⟨y0, ?_⟩
    rw [Set.mem_iUnion]
    refine ⟨h_real, ?_⟩
    intro i
    show Y i.val = y0 i
    rfl
  · rintro ⟨y, hy⟩
    rw [Set.mem_iUnion] at hy
    obtain ⟨hy_real, hy_match⟩ := hy
    have hyy : y = y0 := by
      funext i
      have := hy_match i
      simp [hy0_def, this.symm]
    rw [hyy] at hy_real
    exact hy_real

/-- **Step E.** Each pattern event has measure `3^|S| * (1/4)^n`. -/
private lemma pattern_event_measure (φ : ∂F2) (n : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range n) :
    step_measure (patternEvent φ n S)
      = (3 : ℝ≥0∞)^S.card * (1/4 : ℝ≥0∞)^n := by
  classical
  -- (1) A.s.-rewrite the patternEvent as a biUnion of cylinders.
  rw [measure_congr (patternEvent_aeEq_biUnion φ n S)]
  -- (2) Disjoint union → sum of singleton-cylinder masses.
  rw [measure_biUnion_finset
    (s := realisingPrefixes φ n S) (f := fixedPrefixCylinder n)
    (fixedPrefixCylinder_pairwise_disjoint n (realisingPrefixes φ n S))
    (fun y _ => measurableSet_fixedPrefixCylinder n y)]
  -- (3) Each summand is `(1/4)^n` by `step_measure_fixedPrefixCylinder`.
  have h_const : ∀ y ∈ realisingPrefixes φ n S,
      step_measure (fixedPrefixCylinder n y) = (1/4 : ℝ≥0∞)^n := by
    intro y hy
    have hy_gen : ∀ i : Fin n, y i ∈ F2_generating_set :=
      ((mem_realisingPrefixes φ n S y).mp hy).1
    exact step_measure_fixedPrefixCylinder n y hy_gen
  rw [Finset.sum_congr rfl h_const]
  -- (4) Sum of constants → card × value.
  rw [Finset.sum_const]
  -- (5) Cardinality is `3^|S|` by Step F.
  rw [realisingPrefixes_card φ n S hS]
  rw [nsmul_eq_mul]
  push_cast
  ring

/-- patternEvent is a.s.-equal (under `step_measure`) to a biUnion of
fixed-prefix singleton cylinders, hence is null-measurable. -/
private lemma nullMeasurableSet_patternEvent (φ : ∂F2) (n : ℕ) (S : Finset ℕ) :
    NullMeasurableSet (patternEvent φ n S) step_measure := by
  classical
  -- The biUnion of cylinders is measurable.
  have h_meas : MeasurableSet (⋃ y ∈ realisingPrefixes φ n S, fixedPrefixCylinder n y) := by
    apply MeasurableSet.biUnion (Finset.countable_toSet _)
    intro y _
    exact measurableSet_fixedPrefixCylinder n y
  exact h_meas.nullMeasurableSet.congr (patternEvent_aeEq_biUnion φ n S).symm

/-- Distinct patterns (subsets of `Finset.range n`) give disjoint
patternEvents. The intersection is empty: any `Y` in both events would
witness contradictory iffs at any `i` differing between the two patterns. -/
private lemma patternEvent_pairwise_disjoint (φ : ∂F2) (n : ℕ)
    (S_set : Finset (Finset ℕ))
    (hS_set : ∀ S ∈ S_set, S ⊆ Finset.range n) :
    (↑S_set : Set (Finset ℕ)).PairwiseDisjoint (patternEvent φ n) := by
  classical
  intro S hS S' hS' hSS'
  show Disjoint (patternEvent φ n S) (patternEvent φ n S')
  rw [Set.disjoint_iff_forall_ne]
  rintro Y hY Z hZ rfl
  -- Some `i` distinguishes `S` and `S'`. Both `S` and `S'` are subsets of
  -- `Finset.range n`, so `i < n`.
  apply hSS'
  ext i
  -- Show `i ∈ S ↔ i ∈ S'`. By cases on `i < n`.
  by_cases hi : i ∈ Finset.range n
  · have hi_lt : i < n := Finset.mem_range.mp hi
    have h1 := hY i hi_lt
    have h2 := hZ i hi_lt
    -- `Y i ∈ awayGenFinset ↔ i ∈ S` and `Y i ∈ awayGenFinset ↔ i ∈ S'`.
    constructor
    · intro hin; exact h2.mp (h1.mpr hin)
    · intro hin; exact h1.mp (h2.mpr hin)
  · -- `i ∉ Finset.range n`, hence `i ∉ S` and `i ∉ S'`.
    have hi_S : i ∉ S := fun h => hi (hS_set S (Finset.mem_coe.mp hS) h)
    have hi_S' : i ∉ S' := fun h => hi (hS_set S' (Finset.mem_coe.mp hS') h)
    exact ⟨fun h => absurd h hi_S, fun h => absurd h hi_S'⟩

/-! #### Wave 28 Step G — Sum over patterns -/

/-- **Step G.** Measure of the away-sum event:
    `step_measure(S_n = k) = (n.choose k) * 3^k * (1/4)^n`. -/
private lemma sum_over_patterns (φ : ∂F2) (n k : ℕ) (hk : k ≤ n) :
    step_measure {Y | (Finset.range n).sum (fun i => away_indicator φ i Y) = (k : ℝ)}
      = (n.choose k : ℝ≥0∞) * (3 : ℝ≥0∞)^k * (1/4 : ℝ≥0∞)^n := by
  classical
  -- (1) A.s.-rewrite the away-sum event as a biUnion over patterns.
  rw [measure_congr (away_sum_event_eq_union_patterns_ae φ n k)]
  -- (2) Sum over patterns: each pattern is null-measurable, distinct
  -- patterns disjoint.
  have h_disj : ((Finset.range n).powersetCard k : Set (Finset ℕ)).PairwiseDisjoint
      (patternEvent φ n) :=
    patternEvent_pairwise_disjoint φ n ((Finset.range n).powersetCard k)
      (fun S hS => (Finset.mem_powersetCard.mp hS).1)
  rw [measure_biUnion_finset₀
    (s := (Finset.range n).powersetCard k) (f := patternEvent φ n)
    h_disj.aedisjoint
    (fun S _ => nullMeasurableSet_patternEvent φ n S)]
  -- (3) Each summand is `3^|S| * (1/4)^n = 3^k * (1/4)^n` since `|S| = k`.
  have h_const : ∀ S ∈ (Finset.range n).powersetCard k,
      step_measure (patternEvent φ n S)
        = (3 : ℝ≥0∞)^k * (1/4 : ℝ≥0∞)^n := by
    intro S hS
    obtain ⟨hS_sub, hS_card⟩ := Finset.mem_powersetCard.mp hS
    rw [pattern_event_measure φ n S hS_sub, hS_card]
  rw [Finset.sum_congr rfl h_const]
  -- (4) Sum of constants: card * value.
  rw [Finset.sum_const]
  -- (5) `((Finset.range n).powersetCard k).card = n.choose k`.
  rw [Finset.card_powersetCard, Finset.card_range]
  rw [nsmul_eq_mul, mul_assoc]

/-! #### Wave 28 Assembly — The binomial PMF theorem -/

/-- **Q42 — Binomial PMF for the Busemann away-sum.**

For each `n, k` with `k ≤ n`, under `step_measure`, the event "the partial
away-sum equals `k`" has the binomial probability
`C(n,k) · (3/4)^k · (1/4)^{n-k}`. -/
theorem busemann_walk_sum_binomial_pmf (φ : ∂F2) (n k : ℕ) (hk : k ≤ n) :
    step_measure {Y | (Finset.range n).sum (fun i => away_indicator φ i Y) = (k : ℝ)}
      = ENNReal.ofReal ((n.choose k : ℝ) * (3/4)^k * (1/4)^(n - k)) := by
  -- (1) Apply Step G to compute the LHS in `ℝ≥0∞`.
  rw [sum_over_patterns φ n k hk]
  -- (2) Algebraic rearrangement (in ℝ, applied inside `ofReal`).
  rw [pmf_algebra n k hk]
  -- (3) Goal: `(n.choose k) * 3^k * (1/4)^n = ofReal ((n.choose k : ℝ) * 3^k * (1/4)^n)`.
  -- Strategy: push `ofReal` over `*` and `^`, then identify each factor.
  have h_choose_nn : (0 : ℝ) ≤ (n.choose k : ℝ) := by exact_mod_cast Nat.zero_le _
  have h_3pow_nn : (0 : ℝ) ≤ (3 : ℝ)^k := pow_nonneg (by norm_num) _
  rw [ENNReal.ofReal_mul (mul_nonneg h_choose_nn h_3pow_nn)]
  rw [ENNReal.ofReal_mul h_choose_nn]
  rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 3) k]
  rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1/4) n]
  congr 2
  · -- `(n.choose k : ℝ≥0∞) = ENNReal.ofReal ((n.choose k : ℝ))`.
    rw [show ((n.choose k : ℝ)) = ((n.choose k : ℕ) : ℝ) from by norm_cast,
        ENNReal.ofReal_natCast]
  · -- `(3 : ℝ≥0∞) = ENNReal.ofReal 3`.
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) from by norm_num, ENNReal.ofReal_natCast]
    rfl
  · -- `(1/4 : ℝ≥0∞) = ENNReal.ofReal (1/4 : ℝ)`.
    rw [show (1/4 : ℝ) = ((1 : ℝ) / 4) from by norm_num]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
    rw [ENNReal.ofReal_one]
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) from by norm_num, ENNReal.ofReal_natCast]
    norm_num

/-! ### Wave 35.1 — Path-counting hitting-time pmf

Define the first-hitting-time `T_u_at v u Y` for the SRW on `F_2` started at
`v`, and prove its pmf as a count of admissible first-passage paths.

The walk position at time `n` starting at `v` is `v * X_walk n Y`. The hitting
time is the first `n ∈ ℕ` with `v * X_walk n Y = u` (and `⊤ : ℕ∞` if no such
`n` exists).

The pmf:
```
step_measure {Y | T_u_at v u Y = (n : ℕ∞)}
  = (admissibleFirstPassagePaths v u n).card · (1/4)^n
```
where `admissibleFirstPassagePaths v u n : Finset (Fin n → F2)` is the set of
length-`n` generator-valued sequences `(s_0, …, s_{n-1})` such that:
* `v · s_0 · s_1 · … · s_{n-1} = u` (hits `u` at step `n`),
* for all `k < n`, `v · s_0 · … · s_{k-1} ≠ u` (no early hit),
* each `s_i ∈ F2_generating_set`.

This is Step 1 of the 5-step Wave 35 dispatch (the path-counting hitting-time
pmf, per `prompt_C_reply.md`); subsequent waves (35.2-35.5) consume this to
dissolve the two factor-at-meeting-vertex axioms in `ExitMeasure.lean`. -/

/-- The walk position at time `k` starting at `v ∈ F_2`. Just `v * X_walk k Y`,
named for legibility in the hitting-time API. -/
private def walkAt (v : F2) (k : ℕ) (Y : ℕ → F2) : F2 := v * X_walk k Y

@[simp] private lemma walkAt_zero (v : F2) (Y : ℕ → F2) : walkAt v 0 Y = v := by
  simp [walkAt, X_walk_zero]

private lemma walkAt_succ (v : F2) (k : ℕ) (Y : ℕ → F2) :
    walkAt v (k + 1) Y = walkAt v k Y * Y k := by
  simp [walkAt, X_walk_succ, mul_assoc]

/-- The (finite) set of length-`n` generator-valued sequences
`(s_0, …, s_{n-1})` such that the walk starting at `v` hits `u` exactly at
step `n` (and not before). -/
noncomputable def admissibleFirstPassagePaths (v u : F2) (n : ℕ) :
    Finset (Fin n → F2) := by
  classical
  exact (Fintype.piFinset (fun _ : Fin n => F2_genFinset)).filter
    (fun y =>
      v * X_walk n (extendPrefix n y) = u ∧
      ∀ k : Fin n, v * X_walk k.val (extendPrefix n y) ≠ u)

/-- Membership in `admissibleFirstPassagePaths v u n`. -/
private lemma mem_admissibleFirstPassagePaths (v u : F2) (n : ℕ)
    (y : Fin n → F2) :
    y ∈ admissibleFirstPassagePaths v u n ↔
      (∀ i : Fin n, y i ∈ F2_generating_set) ∧
      v * X_walk n (extendPrefix n y) = u ∧
      (∀ k : Fin n, v * X_walk k.val (extendPrefix n y) ≠ u) := by
  classical
  unfold admissibleFirstPassagePaths
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨h_pi, h_hit, h_no_early⟩
    refine ⟨fun i => ?_, h_hit, h_no_early⟩
    have := h_pi i
    rw [← F2_genFinset_coe]; exact Finset.mem_coe.mpr this
  · rintro ⟨h_gen, h_hit, h_no_early⟩
    refine ⟨fun i => ?_, h_hit, h_no_early⟩
    have := h_gen i
    rw [← F2_genFinset_coe] at this
    exact Finset.mem_coe.mp this

/-! #### The hitting time `T_u_at` -/

/-- The first time the walk starting at `v` visits `u`, valued in `ℕ∞`. We use
`Nat.find` lifted to `ℕ∞` (with `⊤` when the walk never hits `u`). This is a
plain integer-valued random variable; we deliberately avoid Mathlib's
`hittingBtwn` / stopping-time API per the Wave 35 dispatch's "no abstract
Markov-chain theory" constraint. -/
noncomputable def T_u_at (v u : F2) (Y : ℕ → F2) : ℕ∞ := by
  classical
  exact if h : ∃ k : ℕ, v * X_walk k Y = u then ((Nat.find h : ℕ) : ℕ∞) else ⊤

/-- Characterisation of `{Y | T_u_at v u Y = n}` for a finite `n : ℕ`:
`(v * X_walk n Y = u) ∧ (∀ k < n, v * X_walk k Y ≠ u)`. -/
lemma T_u_at_eq_coe_iff (v u : F2) (n : ℕ) (Y : ℕ → F2) :
    T_u_at v u Y = (n : ℕ∞) ↔
      (v * X_walk n Y = u) ∧ (∀ k < n, v * X_walk k Y ≠ u) := by
  unfold T_u_at
  by_cases hex : ∃ k : ℕ, v * X_walk k Y = u
  · simp only [hex, dite_true]
    rw [Nat.cast_injective.eq_iff]
    -- After this, goal is `Nat.find _ = n ↔ ...`
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · rw [← h]; exact Nat.find_spec hex
      · intro k hk
        rw [← h] at hk
        exact Nat.find_min hex hk
    · rintro ⟨h_hit, h_no_early⟩
      apply le_antisymm
      · exact Nat.find_le h_hit
      · by_contra hlt
        push_neg at hlt
        exact h_no_early _ hlt (Nat.find_spec hex)
  · simp only [hex, dite_false]
    constructor
    · intro h
      exact absurd h (by simp)
    · rintro ⟨h_hit, _⟩
      exact absurd ⟨n, h_hit⟩ hex

/-- **Wave 35.2 Step A — finiteness criterion for `T_u_at`.**
The hitting time `T_u_at v u Y` is finite (i.e. `< ⊤`) iff the walk from `v`
visits `u` at some integer time. Trivially extracted from the `dite` defining
`T_u_at`. -/
lemma T_u_at_lt_top_iff (v u : F2) (Y : ℕ → F2) :
    T_u_at v u Y < ⊤ ↔ ∃ n : ℕ, v * X_walk n Y = u := by
  classical
  refine ⟨fun h => ?_, fun hex => ?_⟩
  · -- If `T_u_at v u Y < ⊤`, the `dite` branch must be the `hex` branch.
    by_contra hex
    unfold T_u_at at h
    simp only [hex, dite_false, lt_self_iff_false] at h
  · -- If the walk hits `u`, `T_u_at = ((Nat.find hex : ℕ) : ℕ∞) < ⊤`.
    unfold T_u_at
    simp only [hex, dite_true]
    exact ENat.coe_lt_top _

/-- Equivalent `walkAt` form of the finiteness criterion. -/
lemma T_u_at_lt_top_iff_walkAt (v u : F2) (Y : ℕ → F2) :
    T_u_at v u Y < ⊤ ↔ ∃ n : ℕ, walkAt v n Y = u := by
  rw [T_u_at_lt_top_iff]; rfl

/-- Equivalent `extendPrefix` form of the hitting-time event characterisation.
The walk position `X_walk k Y` for `k ≤ n` depends only on the first `n`
coordinates of `Y`, so we may rewrite it via `extendPrefix n y0` where
`y0 i := Y i.val`. -/
private lemma T_u_at_eq_coe_iff_via_prefix (v u : F2) (n : ℕ) (Y : ℕ → F2) :
    T_u_at v u Y = (n : ℕ∞) ↔
      let y0 : Fin n → F2 := fun i => Y i.val
      (v * X_walk n (extendPrefix n y0) = u) ∧
      (∀ k : Fin n, v * X_walk k.val (extendPrefix n y0) ≠ u) := by
  classical
  -- The walk depends only on the first `n` coordinates of `Y` for `k ≤ n`.
  set y0 : Fin n → F2 := fun i => Y i.val with hy0_def
  have h_eq : ∀ k ≤ n, X_walk k Y = X_walk k (extendPrefix n y0) := by
    intro k hk
    induction k with
    | zero => simp
    | succ m ih =>
      have hm_lt : m < n := by omega
      have hm_le : m ≤ n := by omega
      rw [X_walk_succ, X_walk_succ, ih hm_le]
      congr 1
      rw [extendPrefix_apply_lt n y0 m hm_lt]
  rw [T_u_at_eq_coe_iff]
  constructor
  · rintro ⟨h_hit, h_no_early⟩
    refine ⟨?_, ?_⟩
    · rw [← h_eq n le_rfl]; exact h_hit
    · intro k
      have hk_lt : k.val < n := k.isLt
      have hk_le : k.val ≤ n := le_of_lt hk_lt
      rw [← h_eq k.val hk_le]
      exact h_no_early k.val hk_lt
  · rintro ⟨h_hit, h_no_early⟩
    refine ⟨?_, ?_⟩
    · rw [h_eq n le_rfl]; exact h_hit
    · intro k hk
      rw [h_eq k (le_of_lt hk)]
      exact h_no_early ⟨k, hk⟩

/-! #### The path-counting pmf -/

/-- The hitting-time event `{Y | T_u_at v u Y = n}` is a.s. equal to the
disjoint union of `fixedPrefixCylinder n y` over `y ∈ admissibleFirstPassagePaths v u n`. -/
private lemma T_u_at_event_aeEq_biUnion (v u : F2) (n : ℕ) :
    {Y | T_u_at v u Y = (n : ℕ∞)}
      =ᵐ[step_measure]
      ⋃ y ∈ admissibleFirstPassagePaths v u n, fixedPrefixCylinder n y := by
  filter_upwards [walk_step_in_generating_set_ae] with Y hY
  classical
  apply propext
  set y0 : Fin n → F2 := fun i => Y i.val with hy0_def
  have h_iff := T_u_at_eq_coe_iff_via_prefix v u n Y
  change Y ∈ {Y | T_u_at v u Y = (n : ℕ∞)} ↔
    Y ∈ ⋃ y ∈ admissibleFirstPassagePaths v u n, fixedPrefixCylinder n y
  simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  rw [h_iff]
  constructor
  · rintro ⟨h_hit, h_no_early⟩
    refine ⟨y0, ?_, ?_⟩
    · rw [mem_admissibleFirstPassagePaths]
      refine ⟨fun i => hY i.val, h_hit, h_no_early⟩
    · -- fixedPrefixCylinder n y0
      intro i; rfl
  · rintro ⟨y, hy_mem, hY_in⟩
    -- hY_in : Y ∈ fixedPrefixCylinder n y, i.e. Y i.val = y i for all i : Fin n.
    have hyy : y = y0 := by
      funext i
      have := hY_in i
      simp [hy0_def, this.symm]
    rw [hyy] at hy_mem
    obtain ⟨_, h_hit, h_no_early⟩ := (mem_admissibleFirstPassagePaths v u n y0).mp hy_mem
    exact ⟨h_hit, h_no_early⟩

/-- **Wave 35.1 keystone — Path-counting hitting-time pmf.**

For any starting vertex `v`, target `u`, and step count `n : ℕ`, under
`step_measure`, the probability that the walk starting at `v` hits `u`
exactly at step `n` equals `|admissibleFirstPassagePaths v u n| · (1/4)^n`.

This is a finite disjoint union of fixed-prefix cylinders (one per admissible
length-`n` first-passage path), each with mass `(1/4)^n` since all coordinates
are valued in the 4-element generating set. -/
theorem step_measure_T_u_at_eq (v u : F2) (n : ℕ) :
    step_measure {Y | T_u_at v u Y = (n : ℕ∞)}
      = (admissibleFirstPassagePaths v u n).card * (1/4 : ℝ≥0∞)^n := by
  classical
  rw [measure_congr (T_u_at_event_aeEq_biUnion v u n)]
  rw [measure_biUnion_finset
    (s := admissibleFirstPassagePaths v u n) (f := fixedPrefixCylinder n)
    (fixedPrefixCylinder_pairwise_disjoint n
      (admissibleFirstPassagePaths v u n))
    (fun y _ => measurableSet_fixedPrefixCylinder n y)]
  have h_const : ∀ y ∈ admissibleFirstPassagePaths v u n,
      step_measure (fixedPrefixCylinder n y) = (1/4 : ℝ≥0∞)^n := by
    intro y hy
    have hy_gen : ∀ i : Fin n, y i ∈ F2_generating_set :=
      ((mem_admissibleFirstPassagePaths v u n y).mp hy).1
    exact step_measure_fixedPrefixCylinder n y hy_gen
  rw [Finset.sum_congr rfl h_const]
  rw [Finset.sum_const, nsmul_eq_mul]

/-! ### Wave 35.2c — F_2-automorphism invariance of hit probabilities

The simple random walk on `F_2` is invariant under any group automorphism
that permutes the four generators. We package this in three steps:

* **Step C2** (`Z_uniform_map_of_genFinset_perm`): if a measurable map
  `τ : F2 → F2` satisfies `F2_genFinset.image τ = F2_genFinset`, then
  `Measure.map τ Z_uniform = Z_uniform`. Combined with
  `step_measure_coordLift_invariant` above, this gives `step_measure`-
  invariance under the coordinate-wise lift.

* **Step D** (`step_measure_T_u_at_lt_top_aut_invariant`): for any group
  automorphism `τ : F2 ≃* F2` that permutes `F2_genFinset`, the hit
  probability `step_measure {Y | T_u_at v u Y < ⊤}` equals
  `step_measure {Y | T_u_at (τ v) (τ u) Y < ⊤}`. The proof uses Step C2
  + the change-of-variable on the `T_u_at < ⊤` event, exploiting
  `X_walk n (τ ∘ Y) = τ (X_walk n Y)` for any group hom.

* **Step A** (`σ_swap`): an explicit instance, the `a ↔ b` swap
  automorphism from `freeGroupCongr (Equiv.swap 0 1)`. We verify it
  permutes `F2_genFinset` and provide it as a working example.

These ingredients give Wave 35.2b a tool to deduce equalities of hit
probabilities along `S_4`-orbits of generators (e.g.,
`P(1 → genA) = P(1 → genB)`). The full distance-only homogeneity
(`|w₁| = |w₂| → equal hit probs`) requires further first-step / strong
Markov arguments not encompassed by generator-permuting automorphisms;
those are deferred to Wave 35.2b. -/

/-- **Step C2.** If `τ : F2 → F2` permutes `F2_genFinset` (image equals
`F2_genFinset`), then `Measure.map τ Z_uniform = Z_uniform`. -/
lemma Z_uniform_map_of_genFinset_perm
    (τ : F2 → F2)
    (h_image : F2_genFinset.image τ = F2_genFinset) :
    Measure.map τ Z_uniform = Z_uniform := by
  classical
  -- Reduce: since both measures agree on every singleton {z}, and `F2`
  -- has top σ-algebra (`MeasurableSingletonClass`), they are equal.
  apply Measure.ext
  intro A _hA
  -- We compute both sides via "sum over points of A" using
  -- countability of F2.
  -- Easier: show both measures are characterised by their values on
  -- F2 and on its complement/within F2_generating_set.
  -- Actually the cleanest approach: use `Measure.ext_of_singleton`-style
  -- by showing both sides agree on every singleton. But singletons might
  -- have different masses on each side. Let's compute directly.
  --
  -- Z_uniform = (1/4) • (δ_genA + δ_genB + δ_{genA⁻¹} + δ_{genB⁻¹}).
  -- Measure.map τ Z_uniform applied to A
  --   = Z_uniform (τ⁻¹' A)
  --   = (1/4) • [δ_genA(τ⁻¹A) + δ_genB(τ⁻¹A) + δ_{genA⁻¹}(τ⁻¹A) + δ_{genB⁻¹}(τ⁻¹A)]
  --   = (1/4) • [1[τ genA ∈ A] + 1[τ genB ∈ A] + 1[τ genA⁻¹ ∈ A] + 1[τ genB⁻¹ ∈ A]]
  -- Z_uniform A
  --   = (1/4) • [1[genA ∈ A] + 1[genB ∈ A] + 1[genA⁻¹ ∈ A] + 1[genB⁻¹ ∈ A]]
  -- The two are equal because {τ genA, τ genB, τ genA⁻¹, τ genB⁻¹} =
  -- {genA, genB, genA⁻¹, genB⁻¹} as a multiset (from h_image and the
  -- card-4 fact).
  rw [Measure.map_apply (measurable_F2_to_F2 τ) (MeasurableSet.of_discrete (s := A))]
  -- LHS: Z_uniform (τ ⁻¹' A); RHS: Z_uniform A.
  -- Compute both as sums over F2_genFinset.
  have key : ∀ B : Set F2,
      Z_uniform B = (1/4 : ℝ≥0∞) * ∑ g ∈ F2_genFinset, B.indicator 1 g := by
    intro B
    unfold Z_uniform F2_genFinset
    rw [Measure.smul_apply]
    rw [show ({genA, genB, genA⁻¹, genB⁻¹} : Finset F2)
          = insert (genA : F2)
              (insert (genB : F2)
                (insert (genA⁻¹ : F2) ({(genB⁻¹ : F2)} : Finset F2))) from rfl]
    have h1 : (genA : F2) ∉ ({genB, genA⁻¹, genB⁻¹} : Finset F2) := by
      intro h
      rcases Finset.mem_insert.mp h with h | h
      · exact genA_ne_genB h
      rcases Finset.mem_insert.mp h with h | h
      · exact genA_ne_genA_inv h
      · exact genA_ne_genB_inv (Finset.mem_singleton.mp h)
    have h2 : (genB : F2) ∉ ({genA⁻¹, genB⁻¹} : Finset F2) := by
      intro h
      rcases Finset.mem_insert.mp h with h | h
      · exact genB_ne_genA_inv h
      · exact genB_ne_genB_inv (Finset.mem_singleton.mp h)
    have h3 : (genA⁻¹ : F2) ∉ ({genB⁻¹} : Finset F2) := by
      intro h
      exact genA_inv_ne_genB_inv (Finset.mem_singleton.mp h)
    rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_insert h3,
        Finset.sum_singleton]
    rw [Measure.add_apply, Measure.add_apply, Measure.add_apply]
    simp only [Measure.dirac_apply' _ (MeasurableSet.of_discrete (s := B))]
    -- After this, both sides are `(1/4) * (1[genA ∈ B] + ... + 1[genB⁻¹ ∈ B])`.
    rw [smul_eq_mul]
    ring
  -- Apply to both sides.
  rw [key (τ ⁻¹' A), key A]
  congr 1
  -- Reduce to: ∑ g ∈ F2_genFinset, (τ⁻¹' A).indicator 1 g
  --         = ∑ g ∈ F2_genFinset, A.indicator 1 g
  -- LHS: ∑ g ∈ F2_genFinset, A.indicator 1 (τ g) (by definition of preimage indicator).
  -- Reindex via h_image: as g ranges over F2_genFinset, τ g ranges over F2_genFinset
  -- bijectively (since the image equals the source as 4-element Finsets, τ is
  -- injective on F2_genFinset).
  have h_card : F2_genFinset.card = 4 := F2_genFinset_card
  have h_inj_on : Set.InjOn τ ↑F2_genFinset := by
    have h_image_card : (F2_genFinset.image τ).card = 4 := by
      rw [h_image]; exact h_card
    have h_eq : (F2_genFinset.image τ).card = F2_genFinset.card := by
      rw [h_image_card, h_card]
    exact Finset.injOn_of_card_image_eq h_eq
  have h_LHS_to_image : ∑ g ∈ F2_genFinset, (τ ⁻¹' A).indicator (1 : F2 → ℝ≥0∞) g
      = ∑ g ∈ F2_genFinset.image τ, A.indicator (1 : F2 → ℝ≥0∞) g := by
    rw [Finset.sum_image (fun a ha b hb => h_inj_on ha hb)]
    apply Finset.sum_congr rfl
    intro g _
    rfl
  rw [h_LHS_to_image, h_image]

/-- The action of a group automorphism on the random walk:
`X_walk n (τ ∘ Y) = τ (X_walk n Y)`. -/
private lemma X_walk_coordLift_eq (τ : F2 →* F2) (n : ℕ) (Y : ℕ → F2) :
    X_walk n (coordLift (τ : F2 → F2) Y) = τ (X_walk n Y) := by
  induction n with
  | zero => simp [X_walk_zero, map_one]
  | succ k ih =>
    rw [X_walk_succ, X_walk_succ, ih]
    show τ (X_walk k Y) * τ (Y k) = τ (X_walk k Y * Y k)
    rw [map_mul]

/-- **Step D core identity.** For an injective group hom `τ : F2 →* F2`,
the preimage under the coordinate-wise lift `coordLift τ` of the
hitting-time-finite event `{T_u_at (τ v) (τ u) < ⊤}` equals the original
event `{T_u_at v u < ⊤}`. -/
private lemma coordLift_preimage_T_u_at_lt_top
    (τ : F2 →* F2) (h_inj : Function.Injective τ) (v u : F2) :
    coordLift (τ : F2 → F2) ⁻¹' {Y | T_u_at (τ v) (τ u) Y < ⊤}
      = {Y | T_u_at v u Y < ⊤} := by
  ext Y
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  rw [T_u_at_lt_top_iff, T_u_at_lt_top_iff]
  refine ⟨fun ⟨n, hn⟩ => ⟨n, ?_⟩, fun ⟨n, hn⟩ => ⟨n, ?_⟩⟩
  · -- Direction ⇒: from `τ v * X_walk n (coordLift τ Y) = τ u`,
    -- deduce `v * X_walk n Y = u` via injectivity.
    rw [X_walk_coordLift_eq τ n Y] at hn
    have : τ (v * X_walk n Y) = τ u := by
      rw [map_mul]; exact hn
    exact h_inj this
  · -- Direction ⇐: from `v * X_walk n Y = u`, get `τ v * X_walk n (coordLift τ Y) = τ u`.
    rw [X_walk_coordLift_eq τ n Y]
    have : τ v * τ (X_walk n Y) = τ (v * X_walk n Y) := (map_mul τ v _).symm
    rw [this, hn]

/-- **Step D — F_2-automorphism invariance of `T_u_at` hit probability.**
For any group automorphism `τ : F2 ≃* F2` whose underlying map permutes the
generators (i.e., `F2_genFinset.image τ = F2_genFinset`), the hit
probabilities at `(v, u)` and `(τ v, τ u)` coincide:
`step_measure {Y | T_u_at v u Y < ⊤} = step_measure {Y | T_u_at (τ v) (τ u) Y < ⊤}`.

The proof: by Step C2 + Step C, `Measure.map (coordLift τ) step_measure = step_measure`.
Since `coordLift τ ⁻¹' {Y | T_u_at (τ v) (τ u) Y < ⊤} = {Y | T_u_at v u Y < ⊤}`
(Step D core identity, using `τ` is an injective group hom), the two
measures coincide. -/
theorem step_measure_T_u_at_lt_top_aut_invariant
    (τ : F2 ≃* F2)
    (h_perm : F2_genFinset.image (τ : F2 → F2) = F2_genFinset)
    (v u : F2) :
    step_measure {Y | T_u_at v u Y < ⊤}
      = step_measure {Y | T_u_at (τ v) (τ u) Y < ⊤} := by
  -- Express LHS as preimage measure under `coordLift τ`.
  have h_z_pres : Measure.map (τ : F2 → F2) Z_uniform = Z_uniform :=
    Z_uniform_map_of_genFinset_perm τ h_perm
  have h_step_pres :
      Measure.map (coordLift (τ : F2 → F2)) step_measure = step_measure :=
    step_measure_coordLift_invariant (τ : F2 → F2) h_z_pres
  -- The event `{T_u_at v' u' < ⊤} = ⋃_n {Y | v' * X_walk n Y = u'}` is a
  -- countable union of measurable sets, since each `X_walk n` is measurable
  -- and `F2` is countable with top σ-algebra.
  have h_meas_T_u_at : ∀ (v' u' : F2),
      MeasurableSet {Y : ℕ → F2 | T_u_at v' u' Y < ⊤} := by
    intro v' u'
    have h_eq : {Y : ℕ → F2 | T_u_at v' u' Y < ⊤}
        = ⋃ n : ℕ, {Y | v' * X_walk n Y = u'} := by
      ext Y
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      rw [T_u_at_lt_top_iff]
    rw [h_eq]
    refine MeasurableSet.iUnion (fun n => ?_)
    -- {Y | v' * X_walk n Y = u'} = (X_walk n)⁻¹' {(v')⁻¹ * u'}.
    have h_eq' : {Y : ℕ → F2 | v' * X_walk n Y = u'}
        = (X_walk n)⁻¹' ({(v')⁻¹ * u'} : Set F2) := by
      ext Y
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro h; rw [← h]; group
      · intro h; rw [show v' * X_walk n Y = v' * ((v')⁻¹ * u') from by rw [h]]
        group
    rw [h_eq']
    exact (X_walk_measurable n) (MeasurableSet.singleton _)
  have h_RHS_meas : MeasurableSet {Y : ℕ → F2 | T_u_at (τ v) (τ u) Y < ⊤} :=
    h_meas_T_u_at (τ v) (τ u)
  -- Now the key chain of equalities.
  have h_pre : coordLift (τ : F2 → F2) ⁻¹' {Y | T_u_at (τ v) (τ u) Y < ⊤}
      = {Y | T_u_at v u Y < ⊤} :=
    coordLift_preimage_T_u_at_lt_top
      (τ.toMonoidHom) (τ.toEquiv.injective) v u
  calc step_measure {Y | T_u_at v u Y < ⊤}
      = step_measure
          (coordLift (τ : F2 → F2) ⁻¹' {Y | T_u_at (τ v) (τ u) Y < ⊤}) := by
        rw [h_pre]
    _ = (Measure.map (coordLift (τ : F2 → F2)) step_measure)
          {Y | T_u_at (τ v) (τ u) Y < ⊤} :=
        (Measure.map_apply (measurable_coordLift _) h_RHS_meas).symm
    _ = step_measure {Y | T_u_at (τ v) (τ u) Y < ⊤} := by
        rw [h_step_pres]

/-! ### Wave 35.2c Step A — concrete instance: the swap automorphism `a ↔ b`

We provide one concrete generator-permuting automorphism, the
`a ↔ b` swap induced by the `Fin 2` swap permutation via
`FreeGroup.freeGroupCongr`. This swaps the two pairs `{a, a⁻¹}` and
`{b, b⁻¹}` while preserving the four-element generating set. -/

/-- **Step A.** The `a ↔ b` swap automorphism of `F_2`. -/
noncomputable def σ_swapAB : F2 ≃* F2 :=
  _root_.FreeGroup.freeGroupCongr (Equiv.swap (0 : Fin 2) 1)

/-- `σ_swapAB` sends `genA` to `genB`. -/
private lemma σ_swapAB_genA : σ_swapAB genA = genB := by
  show _root_.FreeGroup.freeGroupCongr (Equiv.swap (0 : Fin 2) 1)
        (_root_.FreeGroup.of (0 : Fin 2)) = _root_.FreeGroup.of 1
  rw [_root_.FreeGroup.freeGroupCongr_apply, _root_.FreeGroup.map.of,
      Equiv.swap_apply_left]

/-- `σ_swapAB` sends `genB` to `genA`. -/
private lemma σ_swapAB_genB : σ_swapAB genB = genA := by
  show _root_.FreeGroup.freeGroupCongr (Equiv.swap (0 : Fin 2) 1)
        (_root_.FreeGroup.of (1 : Fin 2)) = _root_.FreeGroup.of 0
  rw [_root_.FreeGroup.freeGroupCongr_apply, _root_.FreeGroup.map.of,
      Equiv.swap_apply_right]

private lemma σ_swapAB_genA_inv : σ_swapAB (genA⁻¹) = genB⁻¹ := by
  rw [map_inv, σ_swapAB_genA]

private lemma σ_swapAB_genB_inv : σ_swapAB (genB⁻¹) = genA⁻¹ := by
  rw [map_inv, σ_swapAB_genB]

/-- `σ_swapAB` permutes `F2_genFinset` (the underlying map's image equals
`F2_genFinset` setwise). -/
lemma σ_swapAB_image_F2_genFinset :
    F2_genFinset.image (σ_swapAB : F2 → F2) = F2_genFinset := by
  classical
  -- Compute the image directly. `F2_genFinset = {genA, genB, genA⁻¹, genB⁻¹}`,
  -- and `σ_swapAB` maps these to `{genB, genA, genB⁻¹, genA⁻¹}`.
  unfold F2_genFinset
  rw [show ({genA, genB, genA⁻¹, genB⁻¹} : Finset F2)
        = insert (genA : F2)
            (insert (genB : F2)
              (insert (genA⁻¹ : F2) ({(genB⁻¹ : F2)} : Finset F2))) from rfl]
  rw [Finset.image_insert, Finset.image_insert, Finset.image_insert,
      Finset.image_singleton]
  -- Now we have the images: σ genA = genB, σ genB = genA, σ genA⁻¹ = genB⁻¹,
  -- σ genB⁻¹ = genA⁻¹.
  rw [show (σ_swapAB : F2 → F2) genA = genB from σ_swapAB_genA,
      show (σ_swapAB : F2 → F2) genB = genA from σ_swapAB_genB,
      show (σ_swapAB : F2 → F2) (genA⁻¹) = genB⁻¹ from σ_swapAB_genA_inv,
      show (σ_swapAB : F2 → F2) (genB⁻¹) = genA⁻¹ from σ_swapAB_genB_inv]
  -- Goal: {genB, genA, genB⁻¹, genA⁻¹} = {genA, genB, genA⁻¹, genB⁻¹} as Finsets.
  ext z
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h | h | h) <;> tauto
  · rintro (h | h | h | h) <;> tauto

/-- **Step A consequence.** Hit probabilities are invariant under the
`a ↔ b` swap automorphism. -/
theorem step_measure_T_u_at_lt_top_swapAB
    (v u : F2) :
    step_measure {Y | T_u_at v u Y < ⊤}
      = step_measure {Y | T_u_at (σ_swapAB v) (σ_swapAB u) Y < ⊤} :=
  step_measure_T_u_at_lt_top_aut_invariant σ_swapAB
    σ_swapAB_image_F2_genFinset v u

/-- **Public-facing variant.** F_2-automorphism invariance of hit
probabilities, formulated via the public set `F2_generating_set`.

For a group automorphism `τ : F2 ≃* F2` whose action sends generators to
generators bijectively (`τ '' F2_generating_set = F2_generating_set`),
the hit probability `step_measure {Y | T_u_at v u Y < ⊤}` equals the
corresponding mass at `(τ v, τ u)`.

This is the consumption interface for Wave 35.2b: provide a `MulEquiv`
together with a proof that it preserves `F2_generating_set`, and conclude
hit-probability invariance. -/
theorem step_measure_T_u_at_lt_top_set_aut_invariant
    (τ : F2 ≃* F2)
    (h_perm : (τ : F2 → F2) '' F2_generating_set = F2_generating_set)
    (v u : F2) :
    step_measure {Y | T_u_at v u Y < ⊤}
      = step_measure {Y | T_u_at (τ v) (τ u) Y < ⊤} := by
  -- Reduce to the Finset form.
  apply step_measure_T_u_at_lt_top_aut_invariant τ ?_ v u
  -- Bridge: F2_genFinset ↔ F2_generating_set as Finset/Set.
  rw [show (F2_genFinset.image (τ : F2 → F2) : Finset F2)
        = F2_genFinset ↔ ((F2_genFinset.image (τ : F2 → F2) : Set F2)
          = (F2_genFinset : Set F2)) from by
    constructor
    · intro h; rw [h]
    · intro h; exact Finset.coe_injective h]
  rw [Finset.coe_image, F2_genFinset_coe]
  exact h_perm

/-! ### Wave 35.2b — Per-vertex hitting probability via the martingale ansatz

The goal of this section is to prove
```
step_measure { Y | T_u_at v u Y < ⊤ }
  = ENNReal.ofReal ((3 : ℝ) ^ (-(F2_cayley.dist v u : ℤ)))
```
for every pair `(v, u) : F2 × F2`. The proof is the textbook martingale
argument:

1. **Recurrence (Step A).** For `v ≠ u`,
   ```
   P(v, u) = (1/4) ∑_{g ∈ F2_genFinset} P(v · g, u),
   ```
   from `step_measure_head_shift` (partition by the value of the first
   step `Y 0` and use shift-invariance on the tail).

2. **Ansatz (Step B).** The candidate `Q(v, u) = 3^{-d(v,u)}` satisfies
   the same recurrence: at distance `h ≥ 1`, exactly one neighbour of `v`
   lies at distance `h - 1` (the inward one) and three lie at distance
   `h + 1` (outward), giving
   `(1/4)(3^{-(h-1)} + 3 · 3^{-(h+1)}) = 3^{-h}`.

3. **Uniqueness (Step C).** The error `E(v, u) := P(v, u) - Q(v, u)` is a
   bounded harmonic function (in `v`) on `F_2 \ {u}` vanishing at infinity
   (by transience: both terms tend to 0 as `d(v, u) → ∞`) with boundary
   value 0 at `u`. The discrete maximum principle plus decay forces
   `E ≡ 0`.
-/

/-! #### Step A — the per-vertex recurrence -/

/-- **Walk factorisation through `headShift`.** If `Y' := Y ∘ Nat.succ`,
then `X_walk (k + 1) Y = Y 0 * X_walk k Y'`. The key one-step decomposition
of the walk: the first letter peels off, leaving the walk on the shifted
sequence. -/
lemma X_walk_succ_eq_headShift (k : ℕ) (Y : ℕ → F2) :
    X_walk (k + 1) Y = Y 0 * X_walk k (Y ∘ Nat.succ) := by
  induction k with
  | zero =>
    simp [X_walk_succ, X_walk_zero]
  | succ m ih =>
    rw [X_walk_succ, ih]
    show Y 0 * X_walk m (Y ∘ Nat.succ) * Y (m + 1)
        = Y 0 * X_walk (m + 1) (Y ∘ Nat.succ)
    rw [show X_walk (m + 1) (Y ∘ Nat.succ)
            = X_walk m (Y ∘ Nat.succ) * (Y ∘ Nat.succ) m from rfl]
    show Y 0 * X_walk m (Y ∘ Nat.succ) * Y (m + 1)
        = Y 0 * (X_walk m (Y ∘ Nat.succ) * Y (m + 1))
    rw [mul_assoc]

/-- **One-step characterisation of `T_u_at < ⊤`.** When `v ≠ u`, the walk
from `v` hits `u` iff after the first step, the walk from `v · Y 0` hits
`u`. Concretely, `T_u_at v u Y < ⊤ ↔ T_u_at (v * Y 0) u (Y ∘ Nat.succ) < ⊤`. -/
private lemma T_u_at_lt_top_one_step (v u : F2) (Y : ℕ → F2) (hvu : v ≠ u) :
    T_u_at v u Y < ⊤ ↔ T_u_at (v * Y 0) u (Y ∘ Nat.succ) < ⊤ := by
  rw [T_u_at_lt_top_iff, T_u_at_lt_top_iff]
  refine ⟨fun ⟨n, hn⟩ => ?_, fun ⟨k, hk⟩ => ?_⟩
  · -- (⇒) From `v * X_walk n Y = u`, since v ≠ u we have n ≥ 1, so n = k + 1.
    rcases n with _ | k
    · -- n = 0: v * 1 = u, contradicts hvu.
      simp [X_walk_zero] at hn
      exact absurd hn hvu
    · refine ⟨k, ?_⟩
      rw [X_walk_succ_eq_headShift] at hn
      rw [show v * Y 0 * X_walk k (Y ∘ Nat.succ) = v * (Y 0 * X_walk k (Y ∘ Nat.succ))
            from by rw [mul_assoc]]
      exact hn
  · -- (⇐) From `(v * Y 0) * X_walk k (Y ∘ Nat.succ) = u`, take n = k + 1.
    refine ⟨k + 1, ?_⟩
    rw [X_walk_succ_eq_headShift]
    rw [show v * (Y 0 * X_walk k (Y ∘ Nat.succ)) = v * Y 0 * X_walk k (Y ∘ Nat.succ)
          from by rw [mul_assoc]]
    exact hk

/-- The "hits-u-from-v" event as a measurable set. -/
private lemma measurableSet_T_u_at_lt_top (v u : F2) :
    MeasurableSet {Y : ℕ → F2 | T_u_at v u Y < ⊤} := by
  -- Same as the inside of `step_measure_T_u_at_lt_top_aut_invariant`.
  have h_eq : {Y : ℕ → F2 | T_u_at v u Y < ⊤}
      = ⋃ n : ℕ, {Y | v * X_walk n Y = u} := by
    ext Y
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    rw [T_u_at_lt_top_iff]
  rw [h_eq]
  refine MeasurableSet.iUnion (fun n => ?_)
  have h_eq' : {Y : ℕ → F2 | v * X_walk n Y = u}
      = (X_walk n)⁻¹' ({v⁻¹ * u} : Set F2) := by
    ext Y
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h; rw [← h]; group
    · intro h; rw [show v * X_walk n Y = v * (v⁻¹ * u) from by rw [h]]; group
  rw [h_eq']
  exact (X_walk_measurable n) (MeasurableSet.singleton _)

/-- **The boundary case `v = u`.** When the walk starts at `u`, it
trivially hits `u` at time 0, so `step_measure {Y | T_u_at u u Y < ⊤} = 1`. -/
lemma step_measure_T_u_at_lt_top_self (u : F2) :
    step_measure {Y : ℕ → F2 | T_u_at u u Y < ⊤} = 1 := by
  have h_univ : {Y : ℕ → F2 | T_u_at u u Y < ⊤} = Set.univ := by
    ext Y
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    rw [T_u_at_lt_top_iff]
    exact ⟨0, by simp⟩
  rw [h_univ]
  exact measure_univ

/-- **Step A — per-vertex recurrence for the hitting probability.** For
every pair of vertices `v ≠ u` in `F_2`, the hit probability decomposes
via the first step as
```
step_measure {T_u_at v u < ⊤}
  = (1/4) ∑_{g ∈ F2_genFinset} step_measure {T_u_at (v * g) u < ⊤}.
```
The proof uses `step_measure_head_shift` (which factors `step_measure`
through `headShift` as `Z_uniform.prod step_measure`) plus
`shift_invariant` on the tail. -/
lemma step_measure_T_u_at_lt_top_recurrence (v u : F2) (hvu : v ≠ u) :
    step_measure {Y : ℕ → F2 | T_u_at v u Y < ⊤}
      = (1/4 : ℝ≥0∞) *
          ∑ g ∈ F2_genFinset,
            step_measure {Y : ℕ → F2 | T_u_at (v * g) u Y < ⊤} := by
  classical
  -- Define the "after one step" event in F2 × (ℕ → F2):
  -- `S := {(z, Y') | T_u_at (v * z) u Y' < ⊤}`.
  set S : Set (F2 × (ℕ → F2)) :=
    {p | T_u_at (v * p.1) u p.2 < ⊤} with hS_def
  -- The original event equals the preimage of `S` under `headShift`.
  have h_eq_preimage :
      {Y : ℕ → F2 | T_u_at v u Y < ⊤} = headShift ⁻¹' S := by
    ext Y
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hS_def, headShift]
    exact T_u_at_lt_top_one_step v u Y hvu
  -- Each "vertical fibre" `{Y' | T_u_at (v*z) u Y' < ⊤}` is measurable.
  have h_meas_fibre : ∀ z : F2,
      MeasurableSet {Y' : ℕ → F2 | T_u_at (v * z) u Y' < ⊤} :=
    fun z => measurableSet_T_u_at_lt_top (v * z) u
  -- `S` is measurable as a countable union over z : F2 of products
  -- `{z} ×ˢ {Y' | T_u_at (v*z) u Y' < ⊤}`.
  have h_S_decomp : S = ⋃ z : F2, ({z} : Set F2) ×ˢ
      {Y' : ℕ → F2 | T_u_at (v * z) u Y' < ⊤} := by
    ext ⟨z, Y'⟩
    simp only [hS_def, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_prod,
      Set.mem_singleton_iff]
    refine ⟨fun h => ⟨z, rfl, h⟩, ?_⟩
    rintro ⟨z', rfl, h⟩
    exact h
  have h_meas_S : MeasurableSet S := by
    rw [h_S_decomp]
    refine MeasurableSet.iUnion (fun z => ?_)
    exact (MeasurableSet.singleton z).prod (h_meas_fibre z)
  -- Now compute via push-forward.
  rw [h_eq_preimage]
  rw [show step_measure (headShift ⁻¹' S)
        = (Measure.map headShift step_measure) S
        from (Measure.map_apply measurable_headShift h_meas_S).symm]
  rw [step_measure_head_shift]
  -- Now: `(Z_uniform.prod step_measure) S`. Compute via the product.
  rw [h_S_decomp]
  -- (Z_uniform.prod step_measure) (⋃ z, {z} ×ˢ A z) = ∑ z, Z_uniform {z} * step_measure (A z)
  -- (only z ∈ F2_generating_set contribute mass since Z_uniform is supported there)
  -- We rewrite via measure-of-iUnion + product factorisation.
  have h_disj :
      Pairwise (Function.onFun (Disjoint (α := Set (F2 × (ℕ → F2))))
        (fun z : F2 => ({z} : Set F2) ×ˢ
          {Y' : ℕ → F2 | T_u_at (v * z) u Y' < ⊤})) := by
    intro z₁ z₂ hne
    refine Set.disjoint_iff.mpr ?_
    rintro ⟨z, Y'⟩ ⟨h1, h2⟩
    rw [Set.mem_prod] at h1 h2
    have hz₁ : z = z₁ := h1.1
    have hz₂ : z = z₂ := h2.1
    exact hne (hz₁.symm.trans hz₂)
  rw [measure_iUnion h_disj
    (fun z => (MeasurableSet.singleton z).prod (h_meas_fibre z))]
  -- Each summand: Measure.prod_prod
  have h_each : ∀ z : F2,
      (Z_uniform.prod step_measure) (({z} : Set F2) ×ˢ
        {Y' : ℕ → F2 | T_u_at (v * z) u Y' < ⊤})
        = Z_uniform {z} * step_measure
          {Y' : ℕ → F2 | T_u_at (v * z) u Y' < ⊤} := by
    intro z
    exact Measure.prod_prod (s := ({z} : Set F2))
      (t := {Y' : ℕ → F2 | T_u_at (v * z) u Y' < ⊤})
  -- Now we have: ∑' z, Z_uniform {z} * step_measure (...).
  -- Z_uniform {z} = 0 unless z ∈ F2_generating_set.
  -- So the tsum reduces to a Finset sum over F2_genFinset.
  have h_Z_singleton_off : ∀ z : F2, z ∉ F2_generating_set →
      Z_uniform {z} = 0 := by
    intro z hz
    -- From the decomposition Z_uniform = (1/4) • (sum of 4 Diracs) and z ∉ {genA, genB, genA⁻¹, genB⁻¹}.
    unfold Z_uniform
    rw [Measure.smul_apply, Measure.add_apply, Measure.add_apply, Measure.add_apply]
    have hA : (Measure.dirac (genA : F2)) {z} = 0 := by
      rw [Measure.dirac_apply]
      apply Set.indicator_of_notMem
      intro hmem
      exact hz (by rw [Set.mem_singleton_iff] at hmem; rw [← hmem]; left; rfl)
    have hB : (Measure.dirac (genB : F2)) {z} = 0 := by
      rw [Measure.dirac_apply]
      apply Set.indicator_of_notMem
      intro hmem
      exact hz (by rw [Set.mem_singleton_iff] at hmem; rw [← hmem]; right; left; rfl)
    have hAi : (Measure.dirac ((genA : F2)⁻¹)) {z} = 0 := by
      rw [Measure.dirac_apply]
      apply Set.indicator_of_notMem
      intro hmem
      exact hz (by rw [Set.mem_singleton_iff] at hmem; rw [← hmem]
                   right; right; left; rfl)
    have hBi : (Measure.dirac ((genB : F2)⁻¹)) {z} = 0 := by
      rw [Measure.dirac_apply]
      apply Set.indicator_of_notMem
      intro hmem
      exact hz (by rw [Set.mem_singleton_iff] at hmem; rw [← hmem]
                   right; right; right; rfl)
    rw [hA, hB, hAi, hBi]; simp
  -- Reduce the tsum to a Finset sum over F2_genFinset.
  have h_tsum_eq : ∑' z : F2, (Z_uniform.prod step_measure) (({z} : Set F2) ×ˢ
        {Y' : ℕ → F2 | T_u_at (v * z) u Y' < ⊤})
      = ∑ g ∈ F2_genFinset,
          Z_uniform {g} * step_measure {Y' | T_u_at (v * g) u Y' < ⊤} := by
    rw [show (∑' z : F2, (Z_uniform.prod step_measure) (({z} : Set F2) ×ˢ
            {Y' : ℕ → F2 | T_u_at (v * z) u Y' < ⊤}))
          = ∑' z : F2, Z_uniform {z} * step_measure
              {Y' : ℕ → F2 | T_u_at (v * z) u Y' < ⊤} from
        tsum_congr h_each]
    -- Restrict to support {z | Z_uniform {z} ≠ 0} ⊆ F2_generating_set.
    apply tsum_eq_sum (s := F2_genFinset)
    intro z hz
    have hz_not : z ∉ F2_generating_set := by
      intro hmem
      rw [← F2_genFinset_coe] at hmem
      exact hz (Finset.mem_coe.mp hmem)
    rw [h_Z_singleton_off z hz_not, zero_mul]
  rw [h_tsum_eq]
  -- Now the RHS: each Z_uniform {g} = 1/4 for g ∈ F2_genFinset.
  have h_each_quarter : ∀ g ∈ F2_genFinset,
      Z_uniform {g} * step_measure {Y' | T_u_at (v * g) u Y' < ⊤}
        = (1/4 : ℝ≥0∞) * step_measure {Y' | T_u_at (v * g) u Y' < ⊤} := by
    intro g hg
    have h_g_mem : g ∈ F2_generating_set := by
      rw [← F2_genFinset_coe]; exact Finset.mem_coe.mpr hg
    rw [Z_uniform_singleton_of_mem h_g_mem]
  rw [Finset.sum_congr rfl h_each_quarter, ← Finset.mul_sum]

/-! #### Step B — the 4-neighbour distance split (Wave 35.2b Step B)

For any `v ≠ u`, exactly one of the four left-multipliers `g ∈ F2_genFinset`
shortens the Cayley distance by 1, and the other three lengthen it by 1.
This is the "1 inward, 3 outward" structural fact that powers the Step C
ansatz `Q(v, u) = 3^{-d(v, u)}`. -/

open private cayley_dist_mul_left from EnsX2026.Cayley.Growth

/-- Left-translation invariance of distance in `F2_cayley`. -/
private lemma F2_cayley_dist_mul_left (g x y : F2) :
    F2_cayley.dist (g * x) (g * y) = F2_cayley.dist x y := by
  refine le_antisymm (cayley_dist_mul_left _ g x y) ?_
  have h := cayley_dist_mul_left F2_generating_set g⁻¹ (g * x) (g * y)
  rw [show g⁻¹ * (g * x) = x from by group,
      show g⁻¹ * (g * y) = y from by group] at h
  exact h

/-- `F2_cayley.dist v u = (v⁻¹ * u).toWord.length`. -/
private lemma F2_cayley_dist_eq_toWord_length (v u : F2) :
    F2_cayley.dist v u = (v⁻¹ * u).toWord.length := by
  rw [(F2_cayley_dist_mul_left v⁻¹ v u).symm, inv_mul_cancel]
  exact F2_dist_eq_toWord_length _

/-- Letter parametrisation: every element of `F2_genFinset` is `mk [ℓ]`
for a unique letter `ℓ`, and conversely. -/
private lemma F2_genFinset_eq_image_letters :
    F2_genFinset
      = ({(0, true), (0, false), (1, true), (1, false)} : Finset (Fin 2 × Bool)).image
          (fun ℓ : Fin 2 × Bool => _root_.FreeGroup.mk [ℓ]) := by
  ext g
  simp only [F2_genFinset, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image]
  refine ⟨?_, ?_⟩
  · rintro (h | h | h | h)
    · exact ⟨(0, true), by decide, h.symm⟩
    · exact ⟨(1, true), by decide, h.symm⟩
    · exact ⟨(0, false), by decide, by rw [BusemannLocal.mk_single_false]; exact h.symm⟩
    · exact ⟨(1, false), by decide, by rw [BusemannLocal.mk_single_false]; exact h.symm⟩
  · rintro ⟨ℓ, hℓ_mem, hℓ_eq⟩
    rcases hℓ_mem with h | h | h | h
    · left; rw [← hℓ_eq, h]; rfl
    · right; right; left; rw [← hℓ_eq, h, BusemannLocal.mk_single_false]; rfl
    · right; left; rw [← hℓ_eq, h]; rfl
    · right; right; right; rw [← hℓ_eq, h, BusemannLocal.mk_single_false]; rfl

/-- The map `ℓ ↦ FreeGroup.mk [ℓ]` is injective. -/
private lemma mk_letter_injective :
    Function.Injective (fun ℓ : Fin 2 × Bool => _root_.FreeGroup.mk [ℓ]) := by
  intro ℓ₁ ℓ₂ h
  have hred : ∀ ℓ : Fin 2 × Bool, (_root_.FreeGroup.mk [ℓ]).toWord = [ℓ] := fun ℓ => by
    rw [_root_.FreeGroup.toWord_mk]
    have hr : _root_.FreeGroup.IsReduced [ℓ] := List.IsChain.singleton _
    exact hr.reduce_eq
  have hh : (_root_.FreeGroup.mk [ℓ₁]).toWord = (_root_.FreeGroup.mk [ℓ₂]).toWord :=
    congrArg _root_.FreeGroup.toWord h
  rw [hred ℓ₁, hred ℓ₂] at hh
  exact List.head_eq_of_cons_eq hh

/-- **Length under left-multiplication by a letter.** For `w : F2` and a
single-letter generator `g = mk [m]`, the length of `g⁻¹ * w` is determined
by whether `w` starts with `m`:

* if `w.toWord.head? = some m` (cancellation): `|g⁻¹ * w| = |w| - 1`;
* otherwise (no cancellation): `|g⁻¹ * w| = |w| + 1`.

Proof via the inversion trick: `(g⁻¹ * w)⁻¹ = w⁻¹ * g`, so length is
preserved, and we reduce to `|w⁻¹ * g| = |w⁻¹ ± 1|` via the existing
right-multiplication length lemmas in `BusemannLocal`. The `LastCancels w⁻¹ m`
predicate then translates to `m = w.toWord.head`. -/
private lemma F2_left_mul_inv_letter_length_cancel
    (w : F2) (m : Fin 2 × Bool)
    (hw : w ≠ 1) (hhd : w.toWord.head? = some m) :
    ((_root_.FreeGroup.mk [m])⁻¹ * w).toWord.length = w.toWord.length - 1 := by
  -- Inversion trick: `(g⁻¹ * w)⁻¹ = w⁻¹ * g` so the lengths match.
  have hinv_len :
      ((_root_.FreeGroup.mk [m])⁻¹ * w).toWord.length
        = (w⁻¹ * _root_.FreeGroup.mk [m]).toWord.length := by
    rw [show w⁻¹ * _root_.FreeGroup.mk [m]
            = ((_root_.FreeGroup.mk [m])⁻¹ * w)⁻¹ from by group]
    rw [_root_.FreeGroup.toWord_inv, _root_.FreeGroup.invRev_length]
  -- Show LastCancels w⁻¹ m using the head of w.toWord.
  have hw_toWord_ne : w.toWord ≠ [] := by
    intro h_empty
    apply hw
    exact _root_.FreeGroup.toWord_eq_nil_iff.mp h_empty
  have hw_inv_toWord : w⁻¹.toWord = _root_.FreeGroup.invRev w.toWord :=
    _root_.FreeGroup.toWord_inv w
  -- Decompose w.toWord = m :: rest using head?.
  have h_split : ∃ rest, w.toWord = m :: rest := by
    match hexists : w.toWord, hhd with
    | [], hhd => exact (hw_toWord_ne hexists).elim
    | h :: t, hhd =>
      rw [List.head?_cons] at hhd
      have hhm : h = m := Option.some_injective _ hhd
      exact ⟨t, by rw [hhm]⟩
  obtain ⟨rest, hrest⟩ := h_split
  -- w⁻¹.toWord = invRev (m :: rest) = invRev rest ++ [(m.1, !m.2)]
  have h_inv_eq : w⁻¹.toWord = _root_.FreeGroup.invRev rest ++ [(m.1, !m.2)] := by
    rw [hw_inv_toWord, hrest, _root_.FreeGroup.invRev_cons]
    simp [_root_.FreeGroup.invRev]
  -- Hence getLast? w⁻¹.toWord = some (m.1, !m.2), giving LastCancels.
  have h_getLast : w⁻¹.toWord.getLast? = some (m.1, !m.2) := by
    rw [h_inv_eq]
    simp [List.getLast?_append]
  have h_cancel : BusemannLocal.LastCancels w⁻¹ m :=
    ⟨(m.1, !m.2), h_getLast, rfl, rfl⟩
  -- Apply the existing right-mul length lemma.
  rw [hinv_len, BusemannLocal.length_toWord_mul_mk_letter_cancel _ _ h_cancel,
      _root_.FreeGroup.toWord_inv, _root_.FreeGroup.invRev_length]

/-- **No-cancel case.** If `w.toWord.head? ≠ some m`, then `|g⁻¹ * w| = |w| + 1`. -/
private lemma F2_left_mul_inv_letter_length_noCancel
    (w : F2) (m : Fin 2 × Bool)
    (hhd : w.toWord.head? ≠ some m) :
    ((_root_.FreeGroup.mk [m])⁻¹ * w).toWord.length = w.toWord.length + 1 := by
  have hinv_len :
      ((_root_.FreeGroup.mk [m])⁻¹ * w).toWord.length
        = (w⁻¹ * _root_.FreeGroup.mk [m]).toWord.length := by
    rw [show w⁻¹ * _root_.FreeGroup.mk [m]
            = ((_root_.FreeGroup.mk [m])⁻¹ * w)⁻¹ from by group]
    rw [_root_.FreeGroup.toWord_inv, _root_.FreeGroup.invRev_length]
  -- Establish NoLastCancel w⁻¹ m by case-analysing w.toWord.head?.
  have h_no_cancel : BusemannLocal.NoLastCancel w⁻¹ m := by
    intro ℓ' hℓ'_mem
    rw [Option.mem_def] at hℓ'_mem
    -- w⁻¹.toWord = invRev w.toWord. If w.toWord = [], getLast? is none, contradiction.
    rw [_root_.FreeGroup.toWord_inv] at hℓ'_mem
    -- Compute getLast? of invRev w.toWord.
    rcases hexists : w.toWord with _ | ⟨h, t⟩
    · rw [hexists, _root_.FreeGroup.invRev_empty] at hℓ'_mem
      simp at hℓ'_mem
    · -- invRev (h :: t) = invRev t ++ [(h.1, !h.2)]
      have h_eq : _root_.FreeGroup.invRev (h :: t)
          = _root_.FreeGroup.invRev t ++ [(h.1, !h.2)] := by
        rw [_root_.FreeGroup.invRev_cons]
        simp [_root_.FreeGroup.invRev]
      rw [hexists, h_eq] at hℓ'_mem
      have h_last : (_root_.FreeGroup.invRev t ++ [(h.1, !h.2)]).getLast?
          = some (h.1, !h.2) := by
        simp [List.getLast?_append]
      rw [h_last] at hℓ'_mem
      have hℓ'_eq : ℓ' = (h.1, !h.2) := (Option.some_injective _ hℓ'_mem).symm
      -- We need to show ¬ (ℓ'.1 = m.1 ∧ ℓ'.2 = !m.2) given hhd.
      -- hhd says (h :: t).head? ≠ some m, i.e. h ≠ m.
      rw [hexists, List.head?_cons] at hhd
      -- ℓ' = (h.1, !h.2). The cancellation condition is ℓ'.1 = m.1 ∧ ℓ'.2 = !m.2,
      -- i.e. h.1 = m.1 ∧ !h.2 = !m.2, i.e. h = m. Contradicts hhd.
      rintro ⟨h_fst, h_snd⟩
      apply hhd
      -- hℓ'_eq : ℓ' = (h.1, !h.2). h_fst : ℓ'.1 = m.1; h_snd : ℓ'.2 = !m.2.
      -- After substituting hℓ'_eq: h.1 = m.1 and !h.2 = !m.2 ⇒ h.2 = m.2.
      rw [hℓ'_eq] at h_fst h_snd
      -- h_fst : h.1 = m.1; h_snd : (h.1, !h.2).2 = !m.2 (i.e., !h.2 = !m.2 after simp).
      -- Show h.2 = m.2 via boolean case analysis.
      have h2 : h.2 = m.2 := by
        cases hh : h.2 <;> cases hm : m.2 <;> simp [hh, hm] at h_snd ⊢
      have h_eq : h = m := Prod.ext h_fst h2
      rw [h_eq]
  rw [hinv_len, BusemannLocal.length_toWord_mul_mk_letter_noCancel _ _ h_no_cancel,
      _root_.FreeGroup.toWord_inv, _root_.FreeGroup.invRev_length]

/-- **The 4-neighbour distance split (Wave 35.2b Step B).** For any `v ≠ u`
in `F_2`, exactly one of the four left-multipliers `g ∈ F2_genFinset`
shortens the Cayley distance by 1, and the other three lengthen it by 1.
This is the "1 inward, 3 outward" branching ratio of the 4-regular tree
underlying `F2_cayley`, and feeds the Step B ansatz
`Q(v, u) = 3^{-d(v, u)}`. -/
theorem F2_cayley_dist_succ_count
    (v u : F2) (hvu : v ≠ u) :
    (F2_genFinset.filter
      (fun g => F2_cayley.dist (v * g) u = F2_cayley.dist v u - 1)).card = 1
    ∧
    (F2_genFinset.filter
      (fun g => F2_cayley.dist (v * g) u = F2_cayley.dist v u + 1)).card = 3 := by
  classical
  -- Set w := v⁻¹ * u. Then dist v u = |w|, and dist (v*g) u = |g⁻¹ * w|.
  set w : F2 := v⁻¹ * u with hw_def
  -- w ≠ 1 since v ≠ u.
  have hw_ne_one : w ≠ 1 := by
    intro h
    apply hvu
    rw [hw_def] at h
    have : v * (v⁻¹ * u) = v * 1 := by rw [h]
    simpa [← mul_assoc] using this.symm
  -- Distance formulas for both sides.
  have h_dist_vu : F2_cayley.dist v u = w.toWord.length :=
    F2_cayley_dist_eq_toWord_length v u
  have h_dist_vg_u : ∀ g : F2,
      F2_cayley.dist (v * g) u = (g⁻¹ * w).toWord.length := by
    intro g
    rw [F2_cayley_dist_eq_toWord_length (v * g) u]
    congr 1
    rw [hw_def]
    group
  -- w.toWord ≠ [] and has a head letter h₀.
  have hw_toWord_ne : w.toWord ≠ [] := by
    intro h_empty
    exact hw_ne_one (_root_.FreeGroup.toWord_eq_nil_iff.mp h_empty)
  obtain ⟨h₀, hhd⟩ : ∃ ℓ : Fin 2 × Bool, w.toWord.head? = some ℓ := by
    match hexists : w.toWord with
    | [] => exact (hw_toWord_ne hexists).elim
    | h :: t => exact ⟨h, List.head?_cons⟩
  -- The unique cancelling generator: g_cancel = mk [h₀].
  set g_cancel : F2 := _root_.FreeGroup.mk [h₀] with hg_cancel_def
  -- Membership of g_cancel in F2_genFinset (via letter parametrisation).
  have hg_cancel_mem : g_cancel ∈ F2_genFinset := by
    rw [F2_genFinset_eq_image_letters]
    refine Finset.mem_image.mpr ⟨h₀, ?_, rfl⟩
    -- h₀ ∈ BusemannLocal.letters: any letter (i, b) ∈ {(0,t),(0,f),(1,t),(1,f)}.
    show h₀ ∈ ({(0, true), (0, false), (1, true), (1, false)} : Finset (Fin 2 × Bool))
    rcases h₀ with ⟨i, b⟩
    fin_cases i <;> cases b <;> decide
  -- Length formula for any g ∈ F2_genFinset: applying
  -- F2_left_mul_inv_letter_length_{cancel,noCancel} with letter m where g = mk [m].
  -- The cancelling generator is the one with m = h₀, i.e. g = mk [h₀] = g_cancel.
  have h_len_each : ∀ g ∈ F2_genFinset,
      ((g = g_cancel ∧ (g⁻¹ * w).toWord.length = w.toWord.length - 1)
        ∨ (g ≠ g_cancel ∧ (g⁻¹ * w).toWord.length = w.toWord.length + 1)) := by
    intro g hg
    -- Extract the letter m with g = mk [m].
    rw [F2_genFinset_eq_image_letters] at hg
    obtain ⟨m, hm_mem, hm_eq⟩ := Finset.mem_image.mp hg
    -- g = mk [m], so g⁻¹ = (mk [m])⁻¹.
    by_cases hm_eq_h₀ : m = h₀
    · -- Cancel case.
      left
      refine ⟨?_, ?_⟩
      · rw [← hm_eq, hm_eq_h₀]
      · rw [← hm_eq, hm_eq_h₀]
        exact F2_left_mul_inv_letter_length_cancel w h₀ hw_ne_one hhd
    · -- No-cancel case.
      right
      refine ⟨?_, ?_⟩
      · -- g ≠ g_cancel, i.e. mk [m] ≠ mk [h₀].
        rw [← hm_eq]
        intro habs
        exact hm_eq_h₀ (mk_letter_injective habs)
      · rw [← hm_eq]
        apply F2_left_mul_inv_letter_length_noCancel
        rw [hhd]
        intro habs
        exact hm_eq_h₀ (Option.some_injective _ habs).symm
  -- Now prove the two filter cardinalities.
  -- The "cancel" filter is exactly {g_cancel}.
  have h_filter_cancel :
      F2_genFinset.filter
        (fun g => F2_cayley.dist (v * g) u = F2_cayley.dist v u - 1)
        = {g_cancel} := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hg, h_eq⟩
      rcases h_len_each g hg with ⟨h_eq_g, _⟩ | ⟨h_ne, h_len⟩
      · exact h_eq_g
      · -- Contradiction: dist (v*g) u = n + 1 ≠ n - 1 since n ≥ 1.
        rw [h_dist_vg_u, h_len, h_dist_vu] at h_eq
        have hn_pos : 1 ≤ w.toWord.length := by
          rcases Nat.eq_zero_or_pos w.toWord.length with h0 | hp
          · rw [List.length_eq_zero_iff] at h0; exact (hw_toWord_ne h0).elim
          · exact hp
        omega
    · intro hg_eq
      refine ⟨?_, ?_⟩
      · rw [hg_eq]; exact hg_cancel_mem
      · rw [hg_eq, h_dist_vg_u, h_dist_vu, hg_cancel_def]
        exact F2_left_mul_inv_letter_length_cancel w h₀ hw_ne_one hhd
  -- The "no-cancel" filter is F2_genFinset \ {g_cancel}.
  have h_filter_noCancel :
      F2_genFinset.filter
        (fun g => F2_cayley.dist (v * g) u = F2_cayley.dist v u + 1)
        = F2_genFinset.erase g_cancel := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hg, h_eq⟩
      refine ⟨?_, hg⟩
      rcases h_len_each g hg with ⟨h_eq_g, h_len⟩ | ⟨h_ne, _⟩
      · -- Contradiction: cancel case has length n - 1, not n + 1.
        rw [h_dist_vg_u, h_len, h_dist_vu] at h_eq
        omega
      · exact h_ne
    · rintro ⟨hg_ne, hg⟩
      refine ⟨hg, ?_⟩
      rcases h_len_each g hg with ⟨h_eq_g, _⟩ | ⟨_, h_len⟩
      · exact (hg_ne h_eq_g).elim
      · rw [h_dist_vg_u, h_len, h_dist_vu]
  -- Compute the two cardinalities.
  refine ⟨?_, ?_⟩
  · rw [h_filter_cancel, Finset.card_singleton]
  · rw [h_filter_noCancel, Finset.card_erase_of_mem hg_cancel_mem,
        F2_genFinset_card]

/-! #### Step C — the stopped martingale identity

We prove the headline of Wave 35.2b:
```
step_measure { Y | T_u_at v u Y < ⊤ }
  = (3 : ℝ≥0∞) ^ (-(F2_cayley.dist v u : ℤ)).
```

The proof is Doob's optional-stopping argument made explicit. We define
the **stopped process**
```
M_stopped n v u Y := if T_u_at v u Y ≤ n then 1
                     else (3 : ℝ≥0∞) ^ (-(d (v · X_walk n Y) u : ℤ))
```
which is bounded by 1 and converges almost surely to
`indicator {T_u_at v u Y < ⊤} 1 Y` (transience: `d → ∞` on the
non-hitting set). The integral identity
```
∫⁻ Y, M_stopped n v u Y ∂step_measure = (3 : ℝ≥0∞) ^ (-(d v u : ℤ))
```
holds for every `n` by induction (martingale identity), and bounded
convergence delivers the headline. -/

/-- The stopped process: if the walk has already hit `u` at some time
≤ n, value 1; else the discounted distance `3^{-d(walk pos at n, u)}`. -/
private noncomputable def M_stopped (n : ℕ) (v u : F2) (Y : ℕ → F2) : ℝ≥0∞ := by
  classical
  exact if T_u_at v u Y ≤ (n : ℕ∞) then (1 : ℝ≥0∞)
        else (3 : ℝ≥0∞) ^ (-(F2_cayley.dist (v * X_walk n Y) u : ℤ))

/-- Pointwise bound: `M_stopped n v u Y ≤ 1` for all `n, v, u, Y`. -/
private lemma M_stopped_le_one (n : ℕ) (v u : F2) (Y : ℕ → F2) :
    M_stopped n v u Y ≤ 1 := by
  classical
  unfold M_stopped
  by_cases h : T_u_at v u Y ≤ (n : ℕ∞)
  · simp [h]
  · simp only [h, if_false]
    -- `(3 : ℝ≥0∞) ^ (-(d : ℤ)) ≤ 1` since `3 ≥ 1` and the exponent is `≤ 0`.
    set d : ℕ := F2_cayley.dist (v * X_walk n Y) u with hd_def
    have h3 : (3 : ℝ≥0∞) ^ (-(d : ℤ)) = ((3 : ℝ≥0∞) ^ (d : ℤ))⁻¹ :=
      ENNReal.zpow_neg (3 : ℝ≥0∞) (d : ℤ)
    rw [h3]
    -- `((3 : ℝ≥0∞)^d)⁻¹ ≤ 1` iff `(3 : ℝ≥0∞)^d ≥ 1`.
    have hpos : (1 : ℝ≥0∞) ≤ (3 : ℝ≥0∞) ^ (d : ℤ) := by
      rw [zpow_natCast]
      exact one_le_pow_of_one_le' (by norm_num : (1 : ℝ≥0∞) ≤ 3) d
    exact ENNReal.inv_le_one.mpr hpos

/-- `M_stopped n v u` is measurable in `Y`. -/
private lemma measurable_M_stopped (n : ℕ) (v u : F2) :
    Measurable (M_stopped n v u) := by
  classical
  unfold M_stopped
  -- Reduce to `f := fun Y => if .. ≤ n then 1 else (3^...)`.
  -- Both branches are measurable (constant branch trivially; the other branch
  -- factors through `X_walk n` which is measurable).
  have h_meas_pred : MeasurableSet
      {Y : ℕ → F2 | T_u_at v u Y ≤ (n : ℕ∞)} := by
    -- {Y | T ≤ n} = ⋃ k ≤ n, {Y | T = k}. Each {T = k} is the preimage
    -- of {(v⁻¹ * u)} under X_walk k (when v ≠ u) or all of space (when v = u, k = 0).
    have h_eq : {Y : ℕ → F2 | T_u_at v u Y ≤ (n : ℕ∞)}
        = ⋃ k ∈ Finset.range (n + 1), {Y | v * X_walk k Y = u} := by
      ext Y
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range,
        exists_prop]
      constructor
      · intro hT
        -- T_u_at v u Y ≤ n with T_u_at lifted to ℕ∞. We need ∃ k ≤ n, walk hits u at k.
        rcases lt_or_eq_of_le hT with hT_lt | hT_eq
        · -- T < n, so T = some k < n in ℕ.
          have hT_top : T_u_at v u Y < ⊤ := lt_of_lt_of_le hT_lt (by simp)
          rw [T_u_at_lt_top_iff] at hT_top
          obtain ⟨m, hm⟩ := hT_top
          -- Get the actual value of T as a Nat.
          have h_mem : ∃ m, v * X_walk m Y = u := ⟨m, hm⟩
          unfold T_u_at at hT
          simp only [h_mem, dite_true] at hT
          have := hT
          -- this : ((Nat.find h_mem : ℕ) : ℕ∞) ≤ (n : ℕ∞).
          have hk_le : (Nat.find h_mem : ℕ) ≤ n := by
            rw [show ((Nat.find h_mem : ℕ) : ℕ∞) = ((Nat.find h_mem : ℕ) : ℕ∞) from rfl] at this
            exact_mod_cast this
          refine ⟨Nat.find h_mem, ?_, ?_⟩
          · omega
          · exact Nat.find_spec h_mem
        · -- T = n.
          have hT_top : T_u_at v u Y < ⊤ := by rw [hT_eq]; exact ENat.coe_lt_top _
          rw [T_u_at_lt_top_iff] at hT_top
          obtain ⟨m, hm⟩ := hT_top
          have h_mem : ∃ m, v * X_walk m Y = u := ⟨m, hm⟩
          unfold T_u_at at hT_eq
          simp only [h_mem, dite_true] at hT_eq
          -- hT_eq : ((Nat.find h_mem : ℕ) : ℕ∞) = (n : ℕ∞).
          have hk_eq : (Nat.find h_mem : ℕ) = n := by exact_mod_cast hT_eq
          refine ⟨Nat.find h_mem, ?_, ?_⟩
          · omega
          · exact Nat.find_spec h_mem
      · rintro ⟨k, hk_lt, hk_hit⟩
        -- T_u_at v u Y ≤ k ≤ n.
        have h_mem : ∃ m, v * X_walk m Y = u := ⟨k, hk_hit⟩
        unfold T_u_at
        simp only [h_mem, dite_true]
        have h_le : Nat.find h_mem ≤ k := Nat.find_le hk_hit
        have h_le' : Nat.find h_mem ≤ n := by omega
        exact_mod_cast h_le'
    rw [h_eq]
    refine MeasurableSet.biUnion (Finset.range (n + 1)).countable_toSet ?_
    intro k _
    have : {Y : ℕ → F2 | v * X_walk k Y = u}
        = (X_walk k)⁻¹' ({v⁻¹ * u} : Set F2) := by
      ext Y
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro h; rw [← h]; group
      · intro h; rw [show v * X_walk k Y = v * (v⁻¹ * u) from by rw [h]]; group
    rw [this]
    exact (X_walk_measurable k) (MeasurableSet.singleton _)
  -- Now build the if-then-else as a measurable function.
  refine Measurable.ite h_meas_pred measurable_const ?_
  -- The else branch: `Y ↦ (3 : ℝ≥0∞) ^ (-(F2_cayley.dist (v * X_walk n Y) u : ℤ))`.
  -- This factors through the (measurable) map `Y ↦ v * X_walk n Y`, then a function
  -- on `F2` (which is discrete). On a `DiscreteMeasurableSpace`, every function is measurable.
  have h_step_meas : Measurable (fun Y : ℕ → F2 => v * X_walk n Y) :=
    measurable_const.mul (X_walk_measurable n)
  have h_outer_meas : Measurable
      (fun x : F2 => (3 : ℝ≥0∞) ^ (-(F2_cayley.dist x u : ℤ))) :=
    fun s _ => MeasurableSet.of_discrete
  exact h_outer_meas.comp h_step_meas

/-- **Boundary case** `v = u`: `M_stopped n u u Y = 1` for every `n` and `Y`,
because `T_u_at u u Y = 0 ≤ n`. -/
private lemma M_stopped_self (n : ℕ) (u : F2) (Y : ℕ → F2) :
    M_stopped n u u Y = 1 := by
  classical
  unfold M_stopped
  have hT0 : T_u_at u u Y = ((0 : ℕ) : ℕ∞) := by
    rw [T_u_at_eq_coe_iff]
    refine ⟨by simp [X_walk_zero], ?_⟩
    intro k hk
    omega
  have h_le : T_u_at u u Y ≤ (n : ℕ∞) := by
    rw [hT0]; exact_mod_cast Nat.zero_le n
  simp [h_le]

/-- **Base case** of the integral identity: `M_stopped 0 v u Y` is the
constant `(3 : ℝ≥0∞)^(-(d v u : ℤ))` if `v ≠ u`, and `1` if `v = u`. In
both cases it equals `(3 : ℝ≥0∞)^(-(d v u : ℤ))`. -/
private lemma M_stopped_zero (v u : F2) (Y : ℕ → F2) :
    M_stopped 0 v u Y = (3 : ℝ≥0∞) ^ (-(F2_cayley.dist v u : ℤ)) := by
  classical
  unfold M_stopped
  by_cases hvu : v = u
  · subst hvu
    have hT0 : T_u_at v v Y = ((0 : ℕ) : ℕ∞) := by
      rw [T_u_at_eq_coe_iff]
      refine ⟨by simp [X_walk_zero], ?_⟩
      intro k hk; omega
    have h_le : T_u_at v v Y ≤ ((0 : ℕ) : ℕ∞) := le_of_eq hT0
    rw [if_pos h_le, SimpleGraph.dist_self]
    simp
  · -- v ≠ u: T_u_at v u Y > 0 (T = 0 would mean v = u). So the if branches to else.
    have hT_ne_zero : ¬ T_u_at v u Y ≤ ((0 : ℕ) : ℕ∞) := by
      intro h
      -- h : T ≤ 0 ⇒ T = 0 ⇒ walk hits u at time 0, i.e. v = u.
      have hT0 : T_u_at v u Y = ((0 : ℕ) : ℕ∞) :=
        le_antisymm h (by simp)
      rw [T_u_at_eq_coe_iff] at hT0
      obtain ⟨h_hit, _⟩ := hT0
      simp [X_walk_zero] at h_hit
      exact hvu h_hit
    rw [if_neg hT_ne_zero]
    show (3 : ℝ≥0∞) ^ (-(F2_cayley.dist (v * X_walk 0 Y) u : ℤ))
        = (3 : ℝ≥0∞) ^ (-(F2_cayley.dist v u : ℤ))
    simp [X_walk_zero]

/-- **Key recurrence identity** for the stopped process. For `v ≠ u`,
the value of `M_stopped (n+1)` at the path `Y` equals the value of
`M_stopped n` at the shifted path `Y ∘ Nat.succ` started at `v * Y 0`.

This is the deterministic backbone of the inductive martingale identity:
the first letter `Y 0` is "consumed" to advance the walk by one step,
and the remaining `n` steps look like a walk from `v * Y 0`. -/
private lemma M_stopped_succ_shift (n : ℕ) (v u : F2) (Y : ℕ → F2)
    (hvu : v ≠ u) :
    M_stopped (n + 1) v u Y = M_stopped n (v * Y 0) u (Y ∘ Nat.succ) := by
  classical
  unfold M_stopped
  -- Two predicates correspond:
  -- T_u_at v u Y ≤ n+1 iff T_u_at (v * Y 0) u (Y ∘ Nat.succ) ≤ n.
  have h_pred : T_u_at v u Y ≤ ((n + 1 : ℕ) : ℕ∞)
      ↔ T_u_at (v * Y 0) u (Y ∘ Nat.succ) ≤ ((n : ℕ) : ℕ∞) := by
    constructor
    · intro h
      -- Either T = ⊤ (impossible, since T ≤ n+1 < ⊤), or T ∈ ℕ.
      have hT_top : T_u_at v u Y < ⊤ := lt_of_le_of_lt h (by simp)
      rw [T_u_at_lt_top_iff] at hT_top
      obtain ⟨m, hm⟩ := hT_top
      have h_mem : ∃ m, v * X_walk m Y = u := ⟨m, hm⟩
      unfold T_u_at at h
      simp only [h_mem, dite_true] at h
      -- h : ((Nat.find h_mem : ℕ) : ℕ∞) ≤ ((n + 1 : ℕ) : ℕ∞)
      have hk_le : Nat.find h_mem ≤ n + 1 := by exact_mod_cast h
      -- Find h_mem ≥ 1 since v ≠ u (walk at time 0 is v).
      have hk_ge : Nat.find h_mem ≥ 1 := by
        rcases Nat.eq_zero_or_pos (Nat.find h_mem) with h0 | hp
        · -- Nat.find h_mem = 0 ⇒ v * X_walk 0 Y = u ⇒ v = u, contradiction.
          have := Nat.find_spec h_mem
          rw [h0] at this
          simp [X_walk_zero] at this
          exact (hvu this).elim
        · exact hp
      -- So Nat.find h_mem = (k_minus_1 + 1) for some k_minus_1.
      set k := Nat.find h_mem - 1 with hk_def
      have hk_succ : Nat.find h_mem = k + 1 := by omega
      have hwalk : v * X_walk (k + 1) Y = u := by rw [← hk_succ]; exact Nat.find_spec h_mem
      -- Use X_walk_succ_eq_headShift to deduce the shifted-walk hit.
      have h_shift_hit : (v * Y 0) * X_walk k (Y ∘ Nat.succ) = u := by
        have h := hwalk
        rw [X_walk_succ_eq_headShift] at h
        rw [show (v * Y 0) * X_walk k (Y ∘ Nat.succ)
              = v * (Y 0 * X_walk k (Y ∘ Nat.succ)) from by rw [mul_assoc]]
        exact h
      -- Show T_u_at (v * Y 0) u (Y ∘ Nat.succ) ≤ k ≤ n.
      have h_mem' : ∃ m, (v * Y 0) * X_walk m (Y ∘ Nat.succ) = u := ⟨k, h_shift_hit⟩
      unfold T_u_at
      simp only [h_mem', dite_true]
      have h_le : Nat.find h_mem' ≤ k := Nat.find_le h_shift_hit
      have h_le' : Nat.find h_mem' ≤ n := by omega
      exact_mod_cast h_le'
    · intro h
      -- Reverse: T(v * Y 0) ≤ n ⇒ T(v) ≤ n+1.
      have hT_top : T_u_at (v * Y 0) u (Y ∘ Nat.succ) < ⊤ :=
        lt_of_le_of_lt h (by simp)
      rw [T_u_at_lt_top_iff] at hT_top
      obtain ⟨k, hk⟩ := hT_top
      have h_mem' : ∃ m, (v * Y 0) * X_walk m (Y ∘ Nat.succ) = u := ⟨k, hk⟩
      unfold T_u_at at h
      simp only [h_mem', dite_true] at h
      have hk_le : Nat.find h_mem' ≤ n := by exact_mod_cast h
      -- Build the original walk hit at time (Nat.find h_mem') + 1.
      set k' := Nat.find h_mem' with hk'_def
      have hk'_hit : (v * Y 0) * X_walk k' (Y ∘ Nat.succ) = u := Nat.find_spec h_mem'
      have h_orig : v * X_walk (k' + 1) Y = u := by
        rw [X_walk_succ_eq_headShift]
        rw [show v * (Y 0 * X_walk k' (Y ∘ Nat.succ))
              = (v * Y 0) * X_walk k' (Y ∘ Nat.succ) from by rw [mul_assoc]]
        exact hk'_hit
      have h_mem : ∃ m, v * X_walk m Y = u := ⟨k' + 1, h_orig⟩
      unfold T_u_at
      simp only [h_mem, dite_true]
      have h_le : Nat.find h_mem ≤ k' + 1 := Nat.find_le h_orig
      have h_le' : Nat.find h_mem ≤ n + 1 := by omega
      exact_mod_cast h_le'
  -- Two distance terms agree: F2_cayley.dist (v * X_walk (n+1) Y) u
  --   = F2_cayley.dist ((v * Y 0) * X_walk n (Y ∘ Nat.succ)) u.
  have h_dist : F2_cayley.dist (v * X_walk (n + 1) Y) u
      = F2_cayley.dist ((v * Y 0) * X_walk n (Y ∘ Nat.succ)) u := by
    congr 1
    rw [X_walk_succ_eq_headShift]
    rw [mul_assoc]
  -- Now case-split.
  by_cases h_le : T_u_at v u Y ≤ ((n + 1 : ℕ) : ℕ∞)
  · have h_le' : T_u_at (v * Y 0) u (Y ∘ Nat.succ) ≤ ((n : ℕ) : ℕ∞) := h_pred.mp h_le
    rw [if_pos h_le, if_pos h_le']
  · have h_le' : ¬ T_u_at (v * Y 0) u (Y ∘ Nat.succ) ≤ ((n : ℕ) : ℕ∞) :=
      fun hh => h_le (h_pred.mpr hh)
    rw [if_neg h_le, if_neg h_le']
    rw [h_dist]

/-! ##### Algebraic recurrence for `3^{-d}` -/

/-- The "1 inward, 3 outward" algebraic identity that closes the
recurrence: for any `h ≥ 1`,
`(1/4) · (3^{-(h-1)} + 3 · 3^{-(h+1)}) = 3^{-h}`. We establish the
ENNReal-valued version we need directly. -/
private lemma three_recurrence (h : ℕ) (hh : 1 ≤ h) :
    (1 / 4 : ℝ≥0∞)
        * ((3 : ℝ≥0∞) ^ (-((h - 1 : ℕ) : ℤ))
            + 3 * (3 : ℝ≥0∞) ^ (-((h + 1 : ℕ) : ℤ)))
      = (3 : ℝ≥0∞) ^ (-(h : ℤ)) := by
  -- Convert to a single power of 3.
  -- 3^{-(h-1)} = 3 · 3^{-h};  3 · 3^{-(h+1)} = 3^{-h}. Sum: 4 · 3^{-h}.
  -- Multiply by 1/4 yields 3^{-h}.
  set X : ℝ≥0∞ := (3 : ℝ≥0∞) ^ (-(h : ℤ)) with hX_def
  have h3_ne_zero : (3 : ℝ≥0∞) ≠ 0 := by norm_num
  have h3_ne_top : (3 : ℝ≥0∞) ≠ ∞ := by norm_num
  -- Step 1: `3^{-(h-1)} = 3 * 3^{-h} = 3 * X`.
  have h_minus1 : (3 : ℝ≥0∞) ^ (-((h - 1 : ℕ) : ℤ)) = 3 * X := by
    have hexp : -((h - 1 : ℕ) : ℤ) = 1 + -(h : ℤ) := by omega
    rw [hexp, ENNReal.zpow_add h3_ne_zero h3_ne_top]
    simp [zpow_one, hX_def]
  -- Step 2: `3^{-(h+1)} = 3^{-h} * 3^{-1} = X * 3⁻¹`.
  have h_plus1 : (3 : ℝ≥0∞) ^ (-((h + 1 : ℕ) : ℤ)) = X * 3⁻¹ := by
    have hexp : -((h + 1 : ℕ) : ℤ) = -(h : ℤ) + (-1) := by omega
    rw [hexp, ENNReal.zpow_add h3_ne_zero h3_ne_top]
    rw [show (3 : ℝ≥0∞) ^ (-1 : ℤ) = 3⁻¹ from by
      rw [ENNReal.zpow_neg, zpow_one]]
  rw [h_minus1, h_plus1]
  -- Goal: (1/4) * (3 * X + 3 * (X * 3⁻¹)) = X.
  -- Simplify `3 * (X * 3⁻¹) = X * (3 * 3⁻¹) = X * 1 = X`.
  have h_simp : (3 : ℝ≥0∞) * (X * 3⁻¹) = X := by
    rw [mul_comm X 3⁻¹, ← mul_assoc, ENNReal.mul_inv_cancel h3_ne_zero h3_ne_top, one_mul]
  rw [h_simp]
  -- Goal: (1/4) * (3 * X + X) = X.
  -- 3 * X + X = 4 * X. Then (1/4) * 4 * X = X.
  have h_sum : (3 : ℝ≥0∞) * X + X = 4 * X := by
    rw [show (4 : ℝ≥0∞) = 3 + 1 from by norm_num, add_mul, one_mul]
  rw [h_sum]
  -- Goal: (1/4) * (4 * X) = X.
  rw [show (1 / 4 : ℝ≥0∞) * (4 * X) = ((1 / 4) * 4) * X from by ring]
  have h4_ne : (4 : ℝ≥0∞) ≠ 0 := by norm_num
  have h4_ne_top : (4 : ℝ≥0∞) ≠ ∞ := by norm_num
  rw [show (1 / 4 : ℝ≥0∞) * 4 = 1 from by
    rw [show (1 / 4 : ℝ≥0∞) = 4⁻¹ from by simp [div_eq_mul_inv]]
    exact ENNReal.inv_mul_cancel h4_ne h4_ne_top]
  rw [one_mul]

/-! ##### Step C.3 — the inductive martingale identity -/

/-- **Step C.3.** For every `n ∈ ℕ` and every pair `v u : F2`,
```
∫⁻ Y, M_stopped n v u Y ∂step_measure = (3 : ℝ≥0∞) ^ (-(F2_cayley.dist v u : ℤ)).
```
This is the discrete martingale identity, proved by induction on `n`.
The base case is `M_stopped_zero` (constant function); the inductive step
factors `step_measure` through `headShift` (per `step_measure_head_shift`),
splits the inner integral by `Y 0 = g`, applies `M_stopped_succ_shift` plus
`step_measure_shift_invariant` to reduce to the integral at depth `n` from
neighbour `v * g`, and closes via the `1-inward / 3-outward` count
(`F2_cayley_dist_succ_count`) and the algebraic identity `three_recurrence`. -/
private lemma lintegral_M_stopped_eq (n : ℕ) (v u : F2) :
    ∫⁻ Y, M_stopped n v u Y ∂step_measure
      = (3 : ℝ≥0∞) ^ (-(F2_cayley.dist v u : ℤ)) := by
  classical
  induction n generalizing v with
  | zero =>
    -- ∫ M_stopped 0 v u = ∫ (constant) = constant.
    have h_const : ∀ Y : ℕ → F2,
        M_stopped 0 v u Y = (3 : ℝ≥0∞) ^ (-(F2_cayley.dist v u : ℤ)) :=
      fun Y => M_stopped_zero v u Y
    calc ∫⁻ Y, M_stopped 0 v u Y ∂step_measure
        = ∫⁻ _Y, (3 : ℝ≥0∞) ^ (-(F2_cayley.dist v u : ℤ)) ∂step_measure := by
          apply lintegral_congr
          intro Y; exact h_const Y
      _ = (3 : ℝ≥0∞) ^ (-(F2_cayley.dist v u : ℤ)) * step_measure Set.univ := by
          rw [lintegral_const]
      _ = (3 : ℝ≥0∞) ^ (-(F2_cayley.dist v u : ℤ)) := by
          rw [show step_measure Set.univ = 1 from
            (IsProbabilityMeasure.measure_univ : step_measure Set.univ = 1)]
          rw [mul_one]
  | succ n ih =>
    -- Case split on v = u.
    by_cases hvu : v = u
    · subst hvu
      -- M_stopped (n+1) v v = 1 (constant).
      have h_const : ∀ Y : ℕ → F2, M_stopped (n + 1) v v Y = 1 :=
        fun Y => M_stopped_self (n + 1) v Y
      calc ∫⁻ Y, M_stopped (n + 1) v v Y ∂step_measure
          = ∫⁻ _Y, (1 : ℝ≥0∞) ∂step_measure := by
            apply lintegral_congr
            intro Y; exact h_const Y
        _ = 1 := by
            rw [lintegral_const,
              show step_measure Set.univ = 1 from
                (IsProbabilityMeasure.measure_univ : step_measure Set.univ = 1),
              mul_one]
        _ = (3 : ℝ≥0∞) ^ (-(F2_cayley.dist v v : ℤ)) := by
            rw [SimpleGraph.dist_self]; simp
    · -- v ≠ u: use the recurrence.
      -- Step (a) — push the integral through `headShift`.
      have h_meas_M : Measurable (M_stopped (n + 1) v u) :=
        measurable_M_stopped (n + 1) v u
      have h_pf :
          ∫⁻ Y, M_stopped (n + 1) v u Y ∂step_measure
            = ∫⁻ p, M_stopped (n + 1) v u (consSucc p)
                ∂(Z_uniform.prod step_measure) := by
        -- Use step_measure = Measure.map consSucc (Z_uniform.prod step_measure).
        have h_step_eq :
            step_measure = Measure.map consSucc (Z_uniform.prod step_measure) := by
          rw [← step_measure_head_shift]
          -- step_measure = Measure.map consSucc (Measure.map headShift step_measure)
          --   since (consSucc ∘ headShift) = id.
          rw [Measure.map_map measurable_consSucc measurable_headShift]
          ext s hs
          rw [Measure.map_apply (measurable_consSucc.comp measurable_headShift) hs]
          have h_id : (consSucc ∘ headShift) ⁻¹' s = s := by
            ext Y; simp [Function.comp, consSucc_headShift]
          rw [h_id]
        calc ∫⁻ Y, M_stopped (n + 1) v u Y ∂step_measure
            = ∫⁻ Y, M_stopped (n + 1) v u Y
                ∂(Measure.map consSucc (Z_uniform.prod step_measure)) := by
              rw [← h_step_eq]
          _ = ∫⁻ p, M_stopped (n + 1) v u (consSucc p)
                ∂(Z_uniform.prod step_measure) := by
              rw [lintegral_map h_meas_M measurable_consSucc]
      -- Step (b) — Apply Tonelli to the prod.
      have h_tonelli :
          ∫⁻ p, M_stopped (n + 1) v u (consSucc p)
              ∂(Z_uniform.prod step_measure)
            = ∫⁻ z, ∫⁻ Y', M_stopped (n + 1) v u (consSucc (z, Y'))
                ∂step_measure ∂Z_uniform := by
        refine lintegral_prod _ ?_
        exact (h_meas_M.comp measurable_consSucc).aemeasurable
      rw [h_pf, h_tonelli]
      -- Step (c) — Apply M_stopped_succ_shift inside the inner integral.
      -- consSucc (z, Y') has zeroth coordinate z and tail Y'.
      have h_shift : ∀ z : F2, ∀ Y' : ℕ → F2,
          M_stopped (n + 1) v u (consSucc (z, Y'))
            = M_stopped n (v * z) u Y' := by
        intro z Y'
        have h_zero : (consSucc (z, Y')) 0 = z := consSucc_zero z Y'
        have h_tail : (consSucc (z, Y')) ∘ Nat.succ = Y' := by
          funext i; exact consSucc_succ z Y' i
        have hcs := M_stopped_succ_shift n v u (consSucc (z, Y')) hvu
        rw [h_zero, h_tail] at hcs
        exact hcs
      have h_shift_int : ∀ z : F2,
          ∫⁻ Y', M_stopped (n + 1) v u (consSucc (z, Y')) ∂step_measure
            = ∫⁻ Y', M_stopped n (v * z) u Y' ∂step_measure := by
        intro z
        apply lintegral_congr
        intro Y'; exact h_shift z Y'
      rw [show (∫⁻ z, ∫⁻ Y', M_stopped (n + 1) v u (consSucc (z, Y'))
            ∂step_measure ∂Z_uniform)
          = ∫⁻ z, ∫⁻ Y', M_stopped n (v * z) u Y' ∂step_measure ∂Z_uniform from by
        apply lintegral_congr
        intro z; exact h_shift_int z]
      -- Step (d) — Apply IH to each inner integral.
      have h_inner : ∀ z : F2,
          ∫⁻ Y', M_stopped n (v * z) u Y' ∂step_measure
            = (3 : ℝ≥0∞) ^ (-(F2_cayley.dist (v * z) u : ℤ)) := fun z => ih (v * z)
      rw [show (∫⁻ z, ∫⁻ Y', M_stopped n (v * z) u Y' ∂step_measure ∂Z_uniform)
          = ∫⁻ z, (3 : ℝ≥0∞) ^ (-(F2_cayley.dist (v * z) u : ℤ)) ∂Z_uniform from by
        apply lintegral_congr
        intro z; exact h_inner z]
      -- Step (e) — Compute the integral over Z_uniform: 4 generators × 1/4 each.
      have h_Z_uniform_int : ∫⁻ z, (3 : ℝ≥0∞) ^ (-(F2_cayley.dist (v * z) u : ℤ))
          ∂Z_uniform
            = (1 / 4 : ℝ≥0∞) * ∑ g ∈ F2_genFinset,
                (3 : ℝ≥0∞) ^ (-(F2_cayley.dist (v * g) u : ℤ)) := by
        -- Z_uniform = (1/4) • (sum of 4 Diracs).
        unfold Z_uniform
        rw [lintegral_smul_measure]
        rw [lintegral_add_measure, lintegral_add_measure, lintegral_add_measure]
        rw [lintegral_dirac, lintegral_dirac, lintegral_dirac, lintegral_dirac]
        -- Now: (1/4) • (f genA + f genB + f genA⁻¹ + f genB⁻¹).
        -- The RHS: (1/4) * (Finset.sum F2_genFinset f).
        have h_finset_sum : ∑ g ∈ F2_genFinset,
            (3 : ℝ≥0∞) ^ (-(F2_cayley.dist (v * g) u : ℤ))
            = (3 : ℝ≥0∞) ^ (-(F2_cayley.dist (v * genA) u : ℤ))
              + (3 : ℝ≥0∞) ^ (-(F2_cayley.dist (v * genB) u : ℤ))
              + (3 : ℝ≥0∞) ^ (-(F2_cayley.dist (v * genA⁻¹) u : ℤ))
              + (3 : ℝ≥0∞) ^ (-(F2_cayley.dist (v * genB⁻¹) u : ℤ)) := by
          unfold F2_genFinset
          rw [show ({genA, genB, genA⁻¹, genB⁻¹} : Finset F2)
                = insert (genA : F2)
                    (insert (genB : F2)
                      (insert (genA⁻¹ : F2) ({(genB⁻¹ : F2)} : Finset F2))) from rfl]
          have h1 : (genA : F2) ∉ ({genB, genA⁻¹, genB⁻¹} : Finset F2) := by
            intro h
            rcases Finset.mem_insert.mp h with h | h
            · exact genA_ne_genB h
            rcases Finset.mem_insert.mp h with h | h
            · exact genA_ne_genA_inv h
            · exact genA_ne_genB_inv (Finset.mem_singleton.mp h)
          have h2 : (genB : F2) ∉ ({genA⁻¹, genB⁻¹} : Finset F2) := by
            intro h
            rcases Finset.mem_insert.mp h with h | h
            · exact genB_ne_genA_inv h
            · exact genB_ne_genB_inv (Finset.mem_singleton.mp h)
          have h3 : (genA⁻¹ : F2) ∉ ({genB⁻¹} : Finset F2) := by
            intro h
            exact genA_inv_ne_genB_inv (Finset.mem_singleton.mp h)
          rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_insert h3,
              Finset.sum_singleton]
          ring
        rw [h_finset_sum, smul_eq_mul]
      rw [h_Z_uniform_int]
      -- Step (f) — Apply F2_cayley_dist_succ_count + three_recurrence.
      -- Distance from v to u, write d = h.
      set h := F2_cayley.dist v u with hh_def
      -- v ≠ u ⇒ h ≥ 1.
      have hh_pos : 1 ≤ h := by
        rw [hh_def]
        by_contra hlt
        push_neg at hlt
        interval_cases (F2_cayley.dist v u)
        -- F2_cayley.dist v u = 0, hence v = u (in a connected SimpleGraph), contradiction.
        have h_conn : F2_cayley.Connected :=
          EnsX2026.Cayley.cayley_graph_connected F2_generating_set
            F2_generating_set_symmetric F2_generating_set_generates
        have hreach := h_conn.preconnected v u
        have h_zero_iff : F2_cayley.dist v u = 0 ↔ v = u := by
          constructor
          · intro h0
            rw [SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable] at h0
            rcases h0 with rfl | hnr
            · rfl
            · exact (hnr hreach).elim
          · intro heq; rw [heq, SimpleGraph.dist_self]
        exact hvu (h_zero_iff.mp ‹F2_cayley.dist v u = 0›)
      -- Now expand the four-term sum using F2_cayley_dist_succ_count.
      have h_count := F2_cayley_dist_succ_count v u hvu
      obtain ⟨h_cancel_card, h_noCancel_card⟩ := h_count
      -- Split sum_g 3^{-d(v*g, u)} = 3^{-(h-1)} (one term) + 3 · 3^{-(h+1)} (three terms).
      -- Easier: rephrase the sum directly via filter_decomposition on F2_genFinset.
      have h_partition : F2_genFinset
          = (F2_genFinset.filter
              (fun g => F2_cayley.dist (v * g) u = F2_cayley.dist v u - 1))
            ∪ (F2_genFinset.filter
              (fun g => F2_cayley.dist (v * g) u = F2_cayley.dist v u + 1)) := by
        -- By F2_left_mul_inv_letter_length_{cancel,noCancel} (used in Step B), every
        -- g ∈ F2_genFinset has dist (v*g) u ∈ {h-1, h+1}.
        ext g
        simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · intro hg
          -- Replicate the case analysis from F2_cayley_dist_succ_count.
          set w : F2 := v⁻¹ * u with hw_def
          have hw_ne_one : w ≠ 1 := by
            intro h
            apply hvu
            rw [hw_def] at h
            have : v * (v⁻¹ * u) = v * 1 := by rw [h]
            simpa [← mul_assoc] using this.symm
          have hw_toWord_ne : w.toWord ≠ [] := by
            intro h_empty
            exact hw_ne_one (_root_.FreeGroup.toWord_eq_nil_iff.mp h_empty)
          obtain ⟨h₀, hhd⟩ : ∃ ℓ : Fin 2 × Bool, w.toWord.head? = some ℓ := by
            match hexists : w.toWord with
            | [] => exact (hw_toWord_ne hexists).elim
            | h :: t => exact ⟨h, List.head?_cons⟩
          have h_dist_vg_u :
              F2_cayley.dist (v * g) u = (g⁻¹ * w).toWord.length := by
            rw [F2_cayley_dist_eq_toWord_length (v * g) u]
            congr 1
            rw [hw_def]; group
          have h_dist_vu : F2_cayley.dist v u = w.toWord.length :=
            F2_cayley_dist_eq_toWord_length v u
          rw [F2_genFinset_eq_image_letters] at hg
          obtain ⟨m, hm_mem, hm_eq⟩ := Finset.mem_image.mp hg
          rw [F2_genFinset_eq_image_letters]
          by_cases hm_eq_h₀ : m = h₀
          · left
            refine ⟨Finset.mem_image.mpr ⟨m, hm_mem, hm_eq⟩, ?_⟩
            rw [h_dist_vg_u, h_dist_vu, ← hm_eq, hm_eq_h₀]
            exact F2_left_mul_inv_letter_length_cancel w h₀ hw_ne_one hhd
          · right
            refine ⟨Finset.mem_image.mpr ⟨m, hm_mem, hm_eq⟩, ?_⟩
            rw [h_dist_vg_u, h_dist_vu, ← hm_eq]
            apply F2_left_mul_inv_letter_length_noCancel
            rw [hhd]; intro habs
            exact hm_eq_h₀ (Option.some_injective _ habs).symm
        · rintro (⟨hg, _⟩ | ⟨hg, _⟩) <;> exact hg
      have h_partition_disj :
          Disjoint (F2_genFinset.filter
              (fun g => F2_cayley.dist (v * g) u = F2_cayley.dist v u - 1))
            (F2_genFinset.filter
              (fun g => F2_cayley.dist (v * g) u = F2_cayley.dist v u + 1)) := by
        rw [Finset.disjoint_iff_ne]
        intro a ha b hb hab
        rw [Finset.mem_filter] at ha hb
        rw [hab] at ha
        -- ha.2 : dist (v*b) u = h-1 and hb.2 : dist (v*b) u = h+1, contradiction since h ≥ 1.
        omega
      have h_split_sum : ∑ g ∈ F2_genFinset,
          (3 : ℝ≥0∞) ^ (-(F2_cayley.dist (v * g) u : ℤ))
          = (3 : ℝ≥0∞) ^ (-((F2_cayley.dist v u - 1 : ℕ) : ℤ))
            + 3 * (3 : ℝ≥0∞) ^ (-((F2_cayley.dist v u + 1 : ℕ) : ℤ)) := by
        rw [h_partition, Finset.sum_union h_partition_disj]
        -- The "cancel" filter has card 1 with constant value 3^{-(h-1)}.
        -- The "no-cancel" filter has card 3 with constant value 3^{-(h+1)}.
        have h_cancel_eq : ∑ g ∈ F2_genFinset.filter
              (fun g => F2_cayley.dist (v * g) u = F2_cayley.dist v u - 1),
              (3 : ℝ≥0∞) ^ (-(F2_cayley.dist (v * g) u : ℤ))
            = (F2_genFinset.filter
              (fun g => F2_cayley.dist (v * g) u = F2_cayley.dist v u - 1)).card
                * (3 : ℝ≥0∞) ^ (-((F2_cayley.dist v u - 1 : ℕ) : ℤ)) := by
          rw [show (F2_genFinset.filter
                (fun g => F2_cayley.dist (v * g) u = F2_cayley.dist v u - 1)).card
                  * (3 : ℝ≥0∞) ^ (-((F2_cayley.dist v u - 1 : ℕ) : ℤ))
                = ∑ _g ∈ F2_genFinset.filter
                  (fun g => F2_cayley.dist (v * g) u = F2_cayley.dist v u - 1),
                  (3 : ℝ≥0∞) ^ (-((F2_cayley.dist v u - 1 : ℕ) : ℤ)) from by
            rw [Finset.sum_const, nsmul_eq_mul]]
          apply Finset.sum_congr rfl
          intro g hg
          rw [Finset.mem_filter] at hg
          rw [hg.2]
        have h_noCancel_eq : ∑ g ∈ F2_genFinset.filter
              (fun g => F2_cayley.dist (v * g) u = F2_cayley.dist v u + 1),
              (3 : ℝ≥0∞) ^ (-(F2_cayley.dist (v * g) u : ℤ))
            = (F2_genFinset.filter
              (fun g => F2_cayley.dist (v * g) u = F2_cayley.dist v u + 1)).card
                * (3 : ℝ≥0∞) ^ (-((F2_cayley.dist v u + 1 : ℕ) : ℤ)) := by
          rw [show (F2_genFinset.filter
                (fun g => F2_cayley.dist (v * g) u = F2_cayley.dist v u + 1)).card
                  * (3 : ℝ≥0∞) ^ (-((F2_cayley.dist v u + 1 : ℕ) : ℤ))
                = ∑ _g ∈ F2_genFinset.filter
                  (fun g => F2_cayley.dist (v * g) u = F2_cayley.dist v u + 1),
                  (3 : ℝ≥0∞) ^ (-((F2_cayley.dist v u + 1 : ℕ) : ℤ)) from by
            rw [Finset.sum_const, nsmul_eq_mul]]
          apply Finset.sum_congr rfl
          intro g hg
          rw [Finset.mem_filter] at hg
          rw [hg.2]
        rw [h_cancel_eq, h_noCancel_eq, h_cancel_card, h_noCancel_card]
        push_cast
        ring
      rw [h_split_sum]
      -- Now apply three_recurrence at h := F2_cayley.dist v u.
      exact three_recurrence h hh_pos

/-! ##### Step C.4 — pointwise a.s. convergence of `M_stopped` -/

/-- **Connectedness** of the Cayley graph `F2_cayley`. -/
private lemma F2_cayley_connected : F2_cayley.Connected :=
  EnsX2026.Cayley.cayley_graph_connected F2_generating_set
    F2_generating_set_symmetric F2_generating_set_generates

/-- **Pointwise convergence** of the stopped process. Almost surely under
`step_measure`, `M_stopped n v u Y` converges in `ℝ≥0∞` to the indicator
of `{T_u_at v u Y < ⊤}`:
* On the event `{T < ⊤}`, eventually `T ≤ n`, so `M_stopped n = 1`.
* On the event `{T = ⊤}`, `M_stopped n = 3^{-d(walk pos at n, u)}` for all
  `n`, and by transience (`walk_dist_tendsto_atTop`) the distance
  `d(v · X_walk n Y, u) → ∞`, so `3^{-d} → 0`. -/
private lemma M_stopped_tendsto_indicator (v u : F2) :
    ∀ᵐ Y ∂step_measure,
      Tendsto (fun n => M_stopped n v u Y) atTop
        (𝓝 ({Y' | T_u_at v u Y' < ⊤}.indicator (fun _ => (1 : ℝ≥0∞)) Y)) := by
  classical
  filter_upwards [walk_dist_tendsto_atTop] with Y hY
  by_cases hT : T_u_at v u Y < ⊤
  · -- Case T < ⊤: M_stopped n = 1 for n large enough.
    have hT_mem : Y ∈ {Y' : ℕ → F2 | T_u_at v u Y' < ⊤} := hT
    rw [Set.indicator_of_mem hT_mem]
    -- T_u_at v u Y is some ℕ; pick N := the value.
    rw [T_u_at_lt_top_iff] at hT
    obtain ⟨k, hk⟩ := hT
    have h_mem : ∃ m, v * X_walk m Y = u := ⟨k, hk⟩
    have hT_val : T_u_at v u Y = ((Nat.find h_mem : ℕ) : ℕ∞) := by
      unfold T_u_at; simp [h_mem]
    set N : ℕ := Nat.find h_mem with hN_def
    have h_ev : ∀ n ≥ N, M_stopped n v u Y = 1 := by
      intro n hn
      unfold M_stopped
      have h_le : T_u_at v u Y ≤ (n : ℕ∞) := by
        rw [hT_val]
        exact_mod_cast hn
      simp [h_le]
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop N] with n hn
    exact (h_ev n hn).symm
  · -- Case T = ⊤: M_stopped n = 3^{-d(v · X_walk n Y, u)} for all n,
    -- and d → ∞ by transience.
    push_neg at hT
    have hT' : T_u_at v u Y = ⊤ := top_le_iff.mp hT
    rw [Set.indicator_of_notMem]
    swap
    · simp [Set.mem_setOf_eq]; rw [hT']
    -- For every n, T_u_at v u Y ≤ n is false (T = ⊤ > n).
    have h_ne : ∀ n : ℕ, ¬ T_u_at v u Y ≤ (n : ℕ∞) := by
      intro n h
      rw [hT'] at h
      exact absurd h (by simp)
    -- So M_stopped n = 3^{-d(v * X_walk n Y, u)}.
    have h_simp : ∀ n : ℕ, M_stopped n v u Y
        = (3 : ℝ≥0∞) ^ (-(F2_cayley.dist (v * X_walk n Y) u : ℤ)) := by
      intro n
      unfold M_stopped
      simp [h_ne n]
    refine Tendsto.congr' (Filter.Eventually.of_forall (fun n => (h_simp n).symm)) ?_
    -- Need: `3^{-d(v * X_walk n Y, u)} → 0` as `n → ∞`.
    -- This follows from d(v * X_walk n Y, u) → ∞ (transience + triangle)
    -- composed with `(3⁻¹)^d → 0`.
    have h_dist_to_inf :
        Tendsto (fun n : ℕ => F2_cayley.dist (v * X_walk n Y) u) atTop atTop := by
      have h_wl_inf :
          Tendsto (fun n : ℕ => word_length (X_walk n Y)) atTop atTop := by
        rw [tendsto_atTop_atTop]
        intro M
        rw [tendsto_atTop_atTop] at hY
        obtain ⟨N, hN⟩ := hY (M : ℝ)
        refine ⟨N, fun n hn => ?_⟩
        have hge : (M : ℝ) ≤ (word_length (X_walk n Y) : ℝ) := hN n hn
        exact_mod_cast hge
      rw [tendsto_atTop_atTop]
      intro M
      set C : ℕ := F2_cayley.dist 1 (v⁻¹ * u) with hC_def
      rw [tendsto_atTop_atTop] at h_wl_inf
      obtain ⟨N, hN⟩ := h_wl_inf (M + C)
      refine ⟨N, fun n hn => ?_⟩
      have hge : word_length (X_walk n Y) ≥ M + C := hN n hn
      have h_dist_xn : F2_cayley.dist (X_walk n Y) 1 = word_length (X_walk n Y) := by
        unfold word_length; rw [SimpleGraph.dist_comm]
      have h_translate : F2_cayley.dist (v * X_walk n Y) u
          = F2_cayley.dist (X_walk n Y) (v⁻¹ * u) := by
        have h := F2_cayley_dist_mul_left v (X_walk n Y) (v⁻¹ * u)
        rw [show v * (v⁻¹ * u) = u from by group] at h
        exact h
      rw [h_translate]
      -- Triangle: dist(X_n, 1) ≤ dist(X_n, v⁻¹ u) + dist(v⁻¹ u, 1).
      -- Hence dist(X_n, v⁻¹ u) ≥ dist(X_n, 1) - dist(v⁻¹ u, 1) ≥ word_length - C ≥ M.
      have h_tri := F2_cayley_connected.dist_triangle
        (u := X_walk n Y) (v := v⁻¹ * u) (w := 1)
      -- h_tri : dist (X_walk n Y) 1 ≤ dist (X_walk n Y) (v⁻¹ * u) + dist (v⁻¹ * u) 1
      have h_C_comm : F2_cayley.dist (v⁻¹ * u) 1 = C := by
        rw [SimpleGraph.dist_comm]
      rw [h_C_comm, h_dist_xn] at h_tri
      omega
    -- Compose: `3^{-d_n} = (3⁻¹)^d_n → 0` since `3⁻¹ < 1` and `d_n → ∞`.
    have h_inv_pow : Tendsto (fun K : ℕ => ((3 : ℝ≥0∞)⁻¹) ^ K) atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by
        rw [ENNReal.inv_lt_one]; norm_num)
    have h_comp : Tendsto
        (fun n : ℕ => ((3 : ℝ≥0∞)⁻¹) ^ F2_cayley.dist (v * X_walk n Y) u)
        atTop (𝓝 0) := h_inv_pow.comp h_dist_to_inf
    -- Convert (3⁻¹)^d to 3^{-d}.
    refine h_comp.congr ?_
    intro n
    rw [show ((3 : ℝ≥0∞) ^ (-(F2_cayley.dist (v * X_walk n Y) u : ℤ)))
          = ((3 : ℝ≥0∞) ^ (F2_cayley.dist (v * X_walk n Y) u : ℤ))⁻¹ from
      ENNReal.zpow_neg _ _]
    rw [show (F2_cayley.dist (v * X_walk n Y) u : ℤ)
          = ((F2_cayley.dist (v * X_walk n Y) u : ℕ) : ℤ) from rfl]
    rw [zpow_natCast]
    rw [ENNReal.inv_pow]

/-! ##### Step C.4 cont. — bounded convergence on the integral -/

/-- **Limit of the integral** of `M_stopped`. Bounded convergence yields
```
∫⁻ Y, M_stopped n v u Y ∂step_measure → step_measure {T_u_at v u Y < ⊤}
```
as `n → ∞`. -/
private lemma tendsto_lintegral_M_stopped (v u : F2) :
    Tendsto (fun n => ∫⁻ Y, M_stopped n v u Y ∂step_measure) atTop
      (𝓝 (step_measure {Y | T_u_at v u Y < ⊤})) := by
  classical
  -- Apply tendsto_lintegral_of_dominated_convergence with bound = 1 (constant).
  have h_meas : ∀ n, Measurable (M_stopped n v u) :=
    fun n => measurable_M_stopped n v u
  have h_bound : ∀ n, M_stopped n v u ≤ᵐ[step_measure] (fun _ => (1 : ℝ≥0∞)) :=
    fun n => Filter.Eventually.of_forall (fun Y => M_stopped_le_one n v u Y)
  have h_fin : ∫⁻ _, (1 : ℝ≥0∞) ∂step_measure ≠ ∞ := by
    rw [lintegral_const,
      show step_measure Set.univ = 1 from
        (IsProbabilityMeasure.measure_univ : step_measure Set.univ = 1)]
    simp
  have h_lim : ∀ᵐ Y ∂step_measure,
      Tendsto (fun n => M_stopped n v u Y) atTop
        (𝓝 ({Y' | T_u_at v u Y' < ⊤}.indicator (fun _ => (1 : ℝ≥0∞)) Y)) :=
    M_stopped_tendsto_indicator v u
  have h_dom := tendsto_lintegral_of_dominated_convergence
    (μ := step_measure) (bound := fun _ => (1 : ℝ≥0∞))
    h_meas h_bound h_fin h_lim
  -- The limit integral is step_measure {T < ⊤}.
  have h_limit_eq :
      ∫⁻ Y, {Y' | T_u_at v u Y' < ⊤}.indicator (fun _ => (1 : ℝ≥0∞)) Y ∂step_measure
        = step_measure {Y | T_u_at v u Y < ⊤} := by
    rw [lintegral_indicator (measurableSet_T_u_at_lt_top v u)]
    rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ]
    simp
  rw [h_limit_eq] at h_dom
  exact h_dom

/-! ##### Step C.5 — the headline theorem -/

/-- **Wave 35.2b headline.** For every pair `(v, u) : F_2 × F_2`, the
hitting probability of `u` for the simple random walk on `F_2` started
at `v` equals `3^{-d(v, u)}`, where `d` is the Cayley graph distance.

This is the keystone of Wave 35.2b. The proof is the discrete Doob's
optional-stopping theorem made fully explicit:

* the stopped process `M_stopped n v u Y` (= `1` if walk has hit `u` by
  time `n`, else `3^{-d(walk pos, u)}`) is bounded by `1` and a.s.
  converges to the indicator of `{T < ⊤}`;
* the integral of `M_stopped n` is constant `3^{-d(v, u)}` for every
  `n`, by induction (martingale identity, `lintegral_M_stopped_eq`);
* bounded convergence delivers the equality of limits. -/
theorem step_measure_T_u_at_lt_top
    (v u : F2) :
    step_measure {Y : ℕ → F2 | T_u_at v u Y < ⊤}
      = (3 : ℝ≥0∞) ^ (-(F2_cayley.dist v u : ℤ)) := by
  -- The integral identity says ∫ M_stopped n is constant in n.
  have h_const : ∀ n : ℕ,
      ∫⁻ Y, M_stopped n v u Y ∂step_measure
        = (3 : ℝ≥0∞) ^ (-(F2_cayley.dist v u : ℤ)) :=
    fun n => lintegral_M_stopped_eq n v u
  -- The limit of the constant sequence is the constant.
  have h_const_lim : Tendsto (fun n : ℕ => ∫⁻ Y, M_stopped n v u Y ∂step_measure)
      atTop (𝓝 ((3 : ℝ≥0∞) ^ (-(F2_cayley.dist v u : ℤ)))) := by
    refine tendsto_const_nhds.congr' ?_
    exact Filter.Eventually.of_forall (fun n => (h_const n).symm)
  -- The bounded-convergence limit identifies it with step_measure {T < ⊤}.
  have h_BC := tendsto_lintegral_M_stopped v u
  exact tendsto_nhds_unique h_BC h_const_lim

/-! ### Wave 35.3 helpers — walk-shift identities and T_u_at recurrence

Auxiliary lemmas powering the keystone partition-by-hitting-time
factorisation in `ExitMeasure.lean`. Concretely:

* **Walk-shift for cumulative trajectory** (`X_walk_succ_left_at`): for
  every starting vertex `x`, the cumulative trajectory `n ↦ x · X_walk n Y`
  satisfies `x · X_walk (k + 1) Y = (x · Y 0) · X_walk k (Y ∘ Nat.succ)`.
  Equivalently, the trajectory of `(Y ∘ succ)` from `(x · Y 0)` is the
  trajectory of `Y` from `x` shifted by one step.

* **T_u_at zero characterisation** (`T_u_at_eq_zero_iff`): the hitting
  time at value `0 : ℕ∞` is equivalent to `v = u`.

* **T_u_at successor head-shift** (`T_u_at_eq_succ_iff_head_shift`): for
  `v ≠ u`, the event `T_u_at v u Y = ((n+1 : ℕ) : ℕ∞)` is equivalent to
  `T_u_at (v * Y 0) u (Y ∘ Nat.succ) = ((n : ℕ) : ℕ∞)`.

* **Word-length head-shift** (`word_length_succ_at`): the word-length
  trajectory `n ↦ word_length (x · X_walk n Y)` shifted by one step is
  the trajectory `n ↦ word_length ((x · Y 0) · X_walk n (Y ∘ succ))`. -/

/-- **Walk-shift identity for the cumulative trajectory.** For any
starting vertex `x`, `x · X_walk (k+1) Y = (x · Y 0) · X_walk k (Y ∘ succ)`.
This is the multiplicative version of `X_walk_succ_eq_headShift`. -/
lemma X_walk_succ_left_at (x : F2) (k : ℕ) (Y : ℕ → F2) :
    x * X_walk (k + 1) Y = (x * Y 0) * X_walk k (Y ∘ Nat.succ) := by
  rw [X_walk_succ_eq_headShift, mul_assoc]

/-- **Hitting time zero** iff starting vertex equals target. -/
lemma T_u_at_eq_zero_iff (v u : F2) (Y : ℕ → F2) :
    T_u_at v u Y = (0 : ℕ∞) ↔ v = u := by
  rw [show (0 : ℕ∞) = ((0 : ℕ) : ℕ∞) from rfl]
  rw [T_u_at_eq_coe_iff]
  refine ⟨fun ⟨h_hit, _⟩ => ?_, fun heq => ⟨?_, fun k hk => absurd hk (Nat.not_lt_zero _)⟩⟩
  · simpa [X_walk_zero] using h_hit
  · simp [X_walk_zero, heq]

/-- **Hitting time successor head-shift.** For `v ≠ u`, the event
`T_u_at v u Y = (n+1)` (as `ℕ∞`) is equivalent to
`T_u_at (v * Y 0) u (Y ∘ succ) = n`. -/
lemma T_u_at_eq_succ_iff_head_shift (v u : F2) (n : ℕ) (Y : ℕ → F2)
    (hvu : v ≠ u) :
    T_u_at v u Y = ((n + 1 : ℕ) : ℕ∞) ↔
      T_u_at (v * Y 0) u (Y ∘ Nat.succ) = ((n : ℕ) : ℕ∞) := by
  rw [T_u_at_eq_coe_iff, T_u_at_eq_coe_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨h_hit, h_no_early⟩
    refine ⟨?_, ?_⟩
    · -- (v * Y 0) * X_walk n (Y ∘ succ) = u via X_walk_succ_left_at.
      have := h_hit
      rw [X_walk_succ_left_at] at this
      exact this
    · intro k hk
      -- For k < n, the (k+1)-th walk position from v doesn't hit u.
      have h_orig := h_no_early (k + 1) (by omega)
      rw [X_walk_succ_left_at] at h_orig
      exact h_orig
  · rintro ⟨h_hit, h_no_early⟩
    refine ⟨?_, ?_⟩
    · rw [X_walk_succ_left_at]; exact h_hit
    · intro k hk
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · rw [h0, X_walk_zero, mul_one]; exact hvu
      · -- k = m + 1 for some m < n.
        obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
        rw [X_walk_succ_left_at]
        exact h_no_early m (by omega)

/-- **Word-length head-shift.** The word-length trajectory shifted by
one step is the word-length trajectory of `(Y ∘ succ)` from `(x · Y 0)`. -/
lemma word_length_succ_at (x : F2) (Y : ℕ → F2) (k : ℕ) :
    word_length (x * X_walk (k + 1) Y)
      = word_length ((x * Y 0) * X_walk k (Y ∘ Nat.succ)) := by
  rw [X_walk_succ_left_at]

/-- **Cumulative-trajectory transience.** For every starting vertex `x`,
the trajectory `n ↦ x · X_walk n Y` has word length tending to ∞ almost
surely. By triangle inequality, `word_length (x · X_walk n Y) ≥
word_length (X_walk n Y) - word_length x`, and the latter tends to ∞
by `walk_dist_tendsto_atTop`. -/
lemma walk_dist_tendsto_atTop_at (x : F2) :
    ∀ᵐ Y ∂step_measure,
      Tendsto (fun n : ℕ => (word_length (x * X_walk n Y) : ℝ)) atTop atTop := by
  filter_upwards [walk_dist_tendsto_atTop] with Y hY
  -- Strategy: word_length(x · X_walk n Y) = F2_cayley.dist 1 (x · X_walk n Y)
  --   = F2_cayley.dist x⁻¹ (X_walk n Y) (left-translation invariance)
  --   ≥ F2_cayley.dist 1 (X_walk n Y) - F2_cayley.dist 1 x⁻¹ (triangle ineq)
  --   = word_length (X_walk n Y) - word_length x⁻¹.
  -- Since word_length x⁻¹ is constant and word_length (X_walk n Y) → ∞,
  -- the difference also tends to ∞.
  set C : ℕ := word_length (x⁻¹ : F2) with hC_def
  have h_wl_inf :
      Tendsto (fun n : ℕ => word_length (X_walk n Y)) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro M
    rw [tendsto_atTop_atTop] at hY
    obtain ⟨N, hN⟩ := hY (M : ℝ)
    refine ⟨N, fun n hn => ?_⟩
    have hge : (M : ℝ) ≤ (word_length (X_walk n Y) : ℝ) := hN n hn
    exact_mod_cast hge
  have h_dist_to_inf :
      Tendsto (fun n : ℕ => word_length (x * X_walk n Y)) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro M
    rw [tendsto_atTop_atTop] at h_wl_inf
    obtain ⟨N, hN⟩ := h_wl_inf (M + C)
    refine ⟨N, fun n hn => ?_⟩
    have hge : word_length (X_walk n Y) ≥ M + C := hN n hn
    -- word_length (x * X_walk n Y) = F2_cayley.dist 1 (x * X_walk n Y).
    have h_dist_1_xn : F2_cayley.dist 1 (x * X_walk n Y)
        = word_length (x * X_walk n Y) := rfl
    -- Translation invariance: F2_cayley.dist 1 (x * X_walk n Y) = F2_cayley.dist x⁻¹ (X_walk n Y).
    have h_translate : F2_cayley.dist 1 (x * X_walk n Y)
        = F2_cayley.dist x⁻¹ (X_walk n Y) := by
      have h := F2_cayley_dist_mul_left x⁻¹ (1 : F2) (x * X_walk n Y)
      rw [show x⁻¹ * (x * X_walk n Y) = X_walk n Y from by group, mul_one] at h
      exact h.symm
    -- Triangle: dist(1, X_n) ≤ dist(1, x⁻¹) + dist(x⁻¹, X_n).
    -- Hence dist(x⁻¹, X_n) ≥ dist(1, X_n) - dist(1, x⁻¹) = word_length (X_walk n Y) - C.
    have h_tri := F2_cayley_connected.dist_triangle
      (u := (1 : F2)) (v := x⁻¹) (w := X_walk n Y)
    have h_dist_1_xinv : F2_cayley.dist 1 x⁻¹ = C := by
      unfold word_length at hC_def; exact hC_def.symm
    have h_dist_1_Xn : F2_cayley.dist 1 (X_walk n Y) = word_length (X_walk n Y) := rfl
    rw [h_dist_1_xinv, h_dist_1_Xn] at h_tri
    -- Convert goal: word_length (x * X_walk n Y) ≥ M.
    have h_unfold_goal : word_length (x * X_walk n Y)
        = F2_cayley.dist x⁻¹ (X_walk n Y) := by
      rw [← h_dist_1_xn]; exact h_translate
    rw [h_unfold_goal]
    omega
  -- Now lift to ℝ.
  rw [tendsto_atTop_atTop]
  intro M
  rw [tendsto_atTop_atTop] at h_dist_to_inf
  obtain ⟨M', hM'⟩ : ∃ M' : ℕ, M ≤ (M' : ℝ) := by
    obtain ⟨M', hM'⟩ := exists_nat_ge M
    exact ⟨M', hM'⟩
  obtain ⟨N, hN⟩ := h_dist_to_inf M'
  refine ⟨N, fun n hn => ?_⟩
  have h := hN n hn
  have h' : (M' : ℝ) ≤ (word_length (x * X_walk n Y) : ℝ) := by exact_mod_cast h
  linarith

end EnsX2026.FreeGroup

-- Wave 35.2b Step A axiom check (verified: kernel triple only):
-- #print axioms EnsX2026.FreeGroup.step_measure_T_u_at_lt_top_recurrence
-- → [propext, Classical.choice, Quot.sound]
-- #print axioms EnsX2026.FreeGroup.step_measure_T_u_at_lt_top_self
-- → [propext, Classical.choice, Quot.sound]

-- Wave 35.2b Step B axiom check (target: kernel triple only):
-- #print axioms EnsX2026.FreeGroup.F2_cayley_dist_succ_count

-- Wave 35.2b Step C axiom check (verified: kernel triple only):
-- #print axioms EnsX2026.FreeGroup.step_measure_T_u_at_lt_top
-- → [propext, Classical.choice, Quot.sound]
