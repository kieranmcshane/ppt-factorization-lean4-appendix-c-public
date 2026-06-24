import PptFactorization.NCPartition
import PptFactorization.MomentCumulant

/-!
# Moment–cumulant identity as a Finset sum over `NCPart n`

Starts the proof of the moment-cumulant formula

    cMC_k(λ, d₁) = Σ_{π ∈ NC(k)} ∏_{B ∈ π.parts} κ_{|B|}

as a real theorem (no axioms), using the Kreweras block-type card lemmas from
`NCPartition.lean`.  The current file completes the identity for `k = 1, 2`;
the `k = 3, 4` Kreweras counts are already available in `NCPartition.lean`,
but the corresponding fiber splits have not yet been written here.

The proof strategy is fiberwise: `∑_{π : NC k} ∏ κ_{|B|}` partitions into
fibers over `blockSizes π : Multiset ℕ`.  On each fiber the summand is
constant (since `κ` only sees block cardinalities), so the fiber sum is
`|fiber| · ∏_{s ∈ μ} κ_s`.  Substituting the Kreweras cardinalities and
matching the `cMC_k` polynomial closes the proof.

Extending past `k = 4` needs the `n ≥ 5` Kreweras lemmas, which are
blocked by the memory wall in `native_decide`; see the scope note in
`NCPartition.lean`.
-/

namespace NCPartition

open Finset MomentCumulant

variable (k : ℕ) (lam d₁ : ℝ)

/-- Moment–cumulant sum: sum over non-crossing partitions of `[k]` of
    the product of `κ` applied to block sizes. -/
noncomputable def momentCumulantSum : ℝ :=
  ∑ π : NCPart k, (π.1.parts.val.map (fun B : Finset ℕ => κ lam d₁ B.card)).prod

/-- The per-partition summand depends only on `blockSizes π`. -/
lemma prod_eq_map_blockSizes (π : NCPart k) :
    (π.1.parts.val.map (fun B : Finset ℕ => κ lam d₁ B.card)).prod
      = ((π.blockSizes).map (κ lam d₁)).prod := by
  unfold NCPart.blockSizes
  rw [Multiset.map_map]
  rfl

-- ═══════════════════════════════════════════════════════════════════
-- k = 1
-- ═══════════════════════════════════════════════════════════════════

/-- The unique non-crossing partition of `[1]`: the indiscrete block `{0}`. -/
noncomputable def NCPart.one : NCPart 1 := NCPart.indiscrete 1 (by decide)

/-- `NCPart 1` is a subsingleton: every partition equals `NCPart.one`. -/
theorem NCPart.eq_one (π : NCPart 1) : π = NCPart.one := by
  have hcard : Fintype.card (NCPart 1) = 1 := card_NCPart_one
  -- `Fintype.card = 1` implies `Subsingleton`, so `π = NCPart.one`.
  haveI : Subsingleton (NCPart 1) := Fintype.card_le_one_iff_subsingleton.mp hcard.le
  exact Subsingleton.elim _ _

/-- Moment–cumulant identity for `k = 1`:
    `momentCumulantSum 1 = κ₁ = cMC_1`. -/
theorem momentCumulantSum_eq_cMC_1 :
    momentCumulantSum 1 lam d₁ = cMC_1 lam d₁ := by
  -- Rewrite `univ` as the singleton `{NCPart.one}` via uniqueness.
  have hu : (Finset.univ : Finset (NCPart 1)) = {NCPart.one} := by
    ext π; simp [NCPart.eq_one π]
  rw [momentCumulantSum, hu, Finset.sum_singleton]
  -- Goal: (NCPart.one.1.parts.val.map ...).prod = cMC_1
  -- `NCPart.one.1 = Finpartition.indiscrete _` has parts `{range 1}`.
  simp only [NCPart.one, NCPart.indiscrete, Finpartition.indiscrete_parts,
             Finset.singleton_val, Multiset.map_singleton, Multiset.prod_singleton,
             Finset.card_range]
  simp [cMC_1]

-- ═══════════════════════════════════════════════════════════════════
-- k = 2
-- ═══════════════════════════════════════════════════════════════════

/-- Every `π : NCPart 2` has block-size multiset `{2}` or `{1, 1}`. -/
theorem blockSizes_NCPart_2 (π : NCPart 2) :
    π.blockSizes = ({2} : Multiset ℕ) ∨ π.blockSizes = ({1, 1} : Multiset ℕ) := by
  revert π; native_decide

/-- Reinterpret a block-type Fintype cardinality as the cardinality of the
    corresponding `Finset.univ.filter` on `NCPart n`. -/
lemma card_filter_blockSizes_eq {n : ℕ} (μ : Multiset ℕ) :
    ((Finset.univ : Finset (NCPart n)).filter (fun π => π.blockSizes = μ)).card
      = Fintype.card {π : NCPart n // π.blockSizes = μ} := by
  rw [Fintype.card_subtype]

/-- **Per-fiber reduction.**  The sum over the `blockSizes = μ` fiber of
    `∏ κ_{|B|}` equals `N • (μ.map κ).prod`, where `N` is the fiber
    cardinality.  Closes one fiber in a fiberwise moment–cumulant proof. -/
lemma sumFiber (k : ℕ) (μ : Multiset ℕ) (N : ℕ)
    (hcard : Fintype.card {π : NCPart k // π.blockSizes = μ} = N) :
    ∑ π ∈ (Finset.univ : Finset (NCPart k)).filter (fun π => π.blockSizes = μ),
      (π.1.parts.val.map (fun B : Finset ℕ => κ lam d₁ B.card)).prod
      = N • (μ.map (κ lam d₁)).prod := by
  have h : ∀ π ∈ (Finset.univ : Finset (NCPart k)).filter
              (fun π => π.blockSizes = μ),
      (π.1.parts.val.map (fun B : Finset ℕ => κ lam d₁ B.card)).prod
        = (μ.map (κ lam d₁)).prod := by
    intro π hπ
    rw [Finset.mem_filter] at hπ
    rw [prod_eq_map_blockSizes, hπ.2]
  rw [Finset.sum_congr rfl h, Finset.sum_const, card_filter_blockSizes_eq, hcard]

/-- Moment–cumulant identity for `k = 2`:
    `momentCumulantSum 2 = κ₂ + κ₁² = cMC_2`. -/
theorem momentCumulantSum_eq_cMC_2 :
    momentCumulantSum 2 lam d₁ = cMC_2 lam d₁ := by
  -- Split `univ` into the two fibers `bs = {2}` and `bs = {1,1}`.
  rw [momentCumulantSum, ← Finset.sum_filter_add_sum_filter_not
        (Finset.univ : Finset (NCPart 2))
        (fun π => π.blockSizes = ({2} : Multiset ℕ))]
  -- First fiber: `bs = {2}`, summand ≡ κ₂; card = 1 by `kreweras_2_2`.
  have h1 : ∀ π ∈ (Finset.univ : Finset (NCPart 2)).filter
              (fun π => π.blockSizes = ({2} : Multiset ℕ)),
      (π.1.parts.val.map (fun B : Finset ℕ => κ lam d₁ B.card)).prod
        = κ lam d₁ 2 := by
    intro π hπ
    rw [Finset.mem_filter] at hπ
    rw [prod_eq_map_blockSizes, hπ.2]
    simp
  rw [Finset.sum_congr rfl h1, Finset.sum_const, card_filter_blockSizes_eq,
      kreweras_2_2]
  -- Second fiber: `¬(bs = {2})`, hence `bs = {1,1}`; summand ≡ κ₁²; card = 1.
  have h2 : ∀ π ∈ (Finset.univ : Finset (NCPart 2)).filter
              (fun π => ¬ π.blockSizes = ({2} : Multiset ℕ)),
      (π.1.parts.val.map (fun B : Finset ℕ => κ lam d₁ B.card)).prod
        = κ lam d₁ 1 * κ lam d₁ 1 := by
    intro π hπ
    rw [Finset.mem_filter] at hπ
    have hbs : π.blockSizes = ({1, 1} : Multiset ℕ) :=
      (blockSizes_NCPart_2 π).resolve_left hπ.2
    rw [prod_eq_map_blockSizes, hbs]
    simp
  have hfilter : (Finset.univ : Finset (NCPart 2)).filter
      (fun π => ¬ π.blockSizes = ({2} : Multiset ℕ))
      = (Finset.univ : Finset (NCPart 2)).filter
        (fun π => π.blockSizes = ({1, 1} : Multiset ℕ)) := by
    ext π
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact (blockSizes_NCPart_2 π).resolve_left h
    · intro h hne; rw [h] at hne; exact absurd hne (by decide)
  rw [Finset.sum_congr rfl h2, Finset.sum_const, hfilter,
      card_filter_blockSizes_eq, kreweras_2_1_1]
  -- Now: `1 • κ 2 + 1 • (κ 1 * κ 1) = cMC_2`.
  simp only [one_nsmul]
  simp [cMC_2, sq]

end NCPartition
