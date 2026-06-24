# Wave 28 — IMO-style blueprint for the Q42 binomial PMF identification

**Target theorem.**

```lean
theorem busemann_walk_sum_binomial_pmf (φ : ∂F2) (n k : ℕ) (hk : k ≤ n) :
    step_measure
        {Y | (Finset.range n).sum (fun i => away_indicator φ i Y) = k}
      = ENNReal.ofReal ((n.choose k : ℝ) * (3/4)^k * (1/4)^(n - k))
```

No new admissions. Built on the existing 1+3 Busemann fact
`busemann_three_plus_neighbours` (proved theorem in `BusemannLocal.lean`)
and the pointwise `away_indicator_eq_indicator_of_gen` (already a private
lemma in `RandomWalk.lean`, lines 514–602). Uses `Measure.infinitePi`
and the projection lemma `Measure.infinitePi_map_restrict`.

---

## 1. The IMO insight (3 sentences)

At step `i` of the walk, given the *prefix* `(Y_0, …, Y_{i-1})`, the current
position `X_i = Y_0 · Y_1 · … · Y_{i-1}` is a deterministic function of
that prefix. The exam's stipulated 1+3 Busemann fact says that of the
4 generators in `Z = {a,b,a⁻¹,b⁻¹}`, **exactly 3** push `X_i` to a
neighbour with `b_φ = b_φ(X_i)+1` (the "away" set `A(X_i)`) and **exactly 1**
gives `b_φ = b_φ(X_i)−1`, regardless of `X_i`. Therefore the number of
prefix-completions `(y_0,…,y_{n-1}) ∈ Z^n` that realise a given pattern
of `away`/`toward` flips `(ε_0,…,ε_{n-1}) ∈ {0,1}^n` is *exactly*
`∏_i (3 if ε_i=1 else 1) = 3^{|ε|}` — independent of the prefix because the
multiplicity is constant. Sum over all `ε` with `|ε|=k` and divide by
`|Z|^n = 4^n` to get `C(n,k) · 3^k / 4^n = C(n,k)·(3/4)^k·(1/4)^{n-k}`.

The "homogeneity" is what removes the need for any conditional-expectation
machinery: we never have to invoke independence as a named theorem; we
only count points in `F2_generating_set^n`.

---

## 2. The Mathlib `Measure.infinitePi → finite-product → counting` chain

All references rooted at
`/Users/kieranmcshane/Documents/Claude/Projects/Article PPT/ppt_factorization_lean4/.lake/packages/mathlib/Mathlib/Probability/`.

| # | Mathlib lemma | File:line | Role |
|---|---|---|---|
| L1 | `MeasureTheory.Measure.infinitePi_map_restrict` | `ProductMeasure.lean:374` | `(infinitePi μ).map (Finset.restrict I) = Measure.pi (fun i:I ↦ μ i)` — pushforward to a finite prefix is the finite product. |
| L2 | `MeasureTheory.Measure.infinitePi_pi` | `ProductMeasure.lean:402` | `infinitePi μ (Set.pi s t) = ∏ i ∈ s, μ i (t i)` — the cylinder formula. **This is the lemma we use directly.** |
| L3 | `MeasureTheory.Measure.pi_pi` | `Mathlib/MeasureTheory/Constructions/Pi.lean` (Mathlib core) | `Measure.pi μ (Set.univ.pi t) = ∏ i, μ i (t i)` — the finite product formula. (Backup if `infinitePi_pi` does not match cleanly.) |
| L4 | `MeasureTheory.Measure.infinitePi_pi_univ` | `ProductMeasure.lean:449` | Countable-`ι` variant: `infinitePi μ (Set.univ.pi t) = ∏' i, μ i (t i)`. (Not needed: we work with a finite cylinder.) |
| L5 | `MeasureTheory.measurePreserving_eval_infinitePi` | `ProductMeasure.lean:467` | (Already used in `walk_step_in_generating_set_ae`.) Not load-bearing for the binomial PMF, but cited by `away_indicator_aeEq`. |
| L6 | `Finset.sum_pow_eq_sum_pi` / `Finset.sum_powerset` / `Finset.card_filter` | Mathlib/Combinatorics/Choose/Sum.lean | Standard — to expand a sum of indicators. We avoid this; we use the simpler `Set.pi` decomposition. |
| L7 | `Nat.choose_eq_card` (for `Finset.powersetCard`) | `Mathlib/Combinatorics/Choose/Basic.lean` | `(Finset.range n).powersetCard k |>.card = n.choose k`. |

**No Mathlib gap is identified.** `infinitePi_pi` (L2) and the standard
`Finset.powersetCard` API close everything.

---

## 3. The exact count

Set `Z := F2_generating_set` (carrier type `Set F2`, 4 elements). For the
event under analysis, only the first `n` coordinates of `Y` matter; we
work on `(Fin n → F2)` via `Finset.restrict (Finset.range n)`.

### 3.1 The "good prefix" set

For a pattern `S ⊆ Finset.range n` of "away" indices (think `S = {i : ε_i = 1}`),
define recursively (depending on the prefix `y₀, …, y_{i-1}`)

```
G S = { (y_0, …, y_{n-1}) ∈ Z^n :
        ∀ i < n, y_i ∈ A_i(y_0, …, y_{i-1}) iff i ∈ S }
```

where `A_i(y_0,…,y_{i-1}) := awayGenFinset φ (X_walk i (extend y))` is the
3-element subset of `Z` of "away" generators at the current vertex
`X_walk i (extend y) = y_0 · y_1 · … · y_{i-1}`.

### 3.2 The count

**Claim.** For every `S ⊆ Finset.range n`,

```
|G S| = 3^|S| · 1^{n - |S|} = 3^|S|.
```

**Proof (induction on `n`).** Trivial for `n = 0`. For the step, fix the
length-`(n-1)` prefix and write
`G S = G (S ∩ [0,n-1)) × A_{n-1}(prefix)` if `n-1 ∈ S`,
else `G S = G (S ∩ [0,n-1)) × (Z \ A_{n-1}(prefix))`. By the 1+3 fact,
`|A_{n-1}(prefix)| = 3` and `|Z \ A_{n-1}(prefix)| = 1`, **independent of
the prefix**. Multiply.

### 3.3 Sum over patterns with `|S| = k`

```
|⋃_{|S|=k} G S| = (Finset.range n).powersetCard k |>.card · 3^k
                 = n.choose k · 3^k.
```

Divide by `|Z|^n = 4^n`:

```
P(S_n = k) = n.choose k · 3^k / 4^n
           = n.choose k · (3/4)^k · (1/4)^{n-k}.
```

---

## 4. Step-by-step Lean blueprint

### Step A — The "first-`n` projection" lemma  *[~25 LOC]*

```lean
lemma step_measure_finset_event (n : ℕ) (E : (Fin n → F2) → Prop)
    [DecidablePred E] :
    step_measure {Y | E (fun i : Fin n => Y i.val)}
      = (Measure.pi (fun _ : Fin n => Z_uniform)) {y | E y} := by
  -- Apply L1 (`infinitePi_map_restrict`) to `I = Finset.range n` and
  -- compose with the equiv `Fin n ≃ (Finset.range n : Finset ℕ)`.
  ...
```

**Tactic sketch.** Treat the event as the preimage of `{y | E y}` under
the restriction map. Apply `Measure.map_apply` (Mathlib's `Measure.map_apply
(measurable_restrict _) hE`), then `infinitePi_map_restrict`. Convert
`Π i : Finset.range n, F2` to `Fin n → F2` via the canonical equivalence
`Finset.equivFin` / `Finset.range_equiv`.

**Mathlib lemmas used.**
- `Measure.map_apply`
- `MeasureTheory.Measure.infinitePi_map_restrict` (L1)
- `Finset.restrict` (definitional)
- `MeasurableSet.of_discrete` (since `F2` has top σ-algebra; any set is measurable)

**Watchpoint.** `Finset.restrict` and the `Fin n` re-indexing carry a
`Subtype.val`-vs-`Fin.val` mismatch. Use `MeasurableEquiv.finsetRangeEquiv`
or, more simply, work directly with `Finset.range n` indexed sets and avoid
the `Fin n` conversion.

### Step B — Cylinder formula on the finite product  *[~20 LOC]*

```lean
lemma pi_Z_uniform_singleton (y : Fin n → F2) :
    (Measure.pi (fun _ : Fin n => Z_uniform)) {y}
      = ∏ i, Z_uniform {y i} := by
  exact Measure.pi_pi_singleton _ _   -- standard
```

A singleton `{y}` in `Π i, F2` is `Set.univ.pi (fun i => {y i})`, and
`Measure.pi_pi` collapses the product. Equivalently, use
`Measure.pi_pi_singleton` if that exists, or manually rewrite.

### Step C — Single-step probabilities for `Z_uniform`  *[~30 LOC]*

```lean
lemma Z_uniform_singleton_of_mem {z : F2} (hz : z ∈ F2_generating_set) :
    Z_uniform {z} = (1/4 : ℝ≥0∞) := by
  -- Direct from the definition of `Z_uniform` and `Measure.dirac_apply`.
  rcases hz with h | h | h | h <;> [rw [h]; rw [h]; rw [h]; rw [h]] <;>
    simp [Z_uniform, Measure.dirac_apply, Set.indicator_of_mem, ...]

lemma Z_uniform_finset_card_le (S : Finset F2) (hS : ↑S ⊆ F2_generating_set) :
    Z_uniform (S : Set F2) = (S.card : ℝ≥0∞) / 4 := by
  rw [show (S : Set F2) = ⋃ z ∈ S, ({z} : Set F2) from ...]
  rw [measure_biUnion_finset (fun z _ z' _ hzz' => Set.disjoint_singleton.mpr hzz') ...]
  simp [Z_uniform_singleton_of_mem (hS · ·)]
```

The two key computations:
- `Z_uniform({z}) = 1/4` for any `z ∈ F2_generating_set`;
- `Z_uniform(awayGenFinset φ x) = 3/4` (since the Finset has 3 elements);
- `Z_uniform(F2_generating_set \ awayGenFinset φ x) = 1/4`.

**Mathlib lemmas used.**
- `Measure.dirac_apply`
- `measure_biUnion_finset` (or `measure_iUnion_eq_tsum_of_disjoint`)
- `ENNReal.div_eq_inv_mul`

### Step D — Decompose the event by pattern `S`  *[~15 LOC]*

```lean
private lemma event_eq_disjUnion (φ : ∂F2) (n k : ℕ) :
    {Y | ∑ i ∈ Finset.range n, away_indicator φ i Y = (k : ℝ)}
      =ᵐ[step_measure]
        ⋃ S ∈ (Finset.range n).powersetCard k,
          {Y | ∀ i ∈ Finset.range n, (Y i ∈ awayGenFinset φ (X_walk i Y) ↔ i ∈ S)} := by
  filter_upwards [walk_step_in_generating_set_ae] with Y hY
  ...
```

**Insight.** A.s. on `step_measure`, `away_indicator φ i Y ∈ {0,1}` and
equals `1` iff `Y i ∈ awayGenFinset φ (X_walk i Y)`
(via `away_indicator_eq_indicator_of_gen`). Therefore the event
`∑ = k` is, a.s., the disjoint union over patterns `S` with `|S| = k`
of the joint events "`Y i ∈ awayGenFinset φ (X_walk i Y)` iff `i ∈ S`".

**Mathlib lemmas used.**
- `Finset.sum_boole` / `Finset.sum_ite` (sum of 0/1 indicators = `card` of the support)
- `Finset.powersetCard_eq_filter` if needed
- `Finset.mem_powersetCard`

### Step E — Each pattern event has measure `(1/4)^n · 3^|S|` *[~50 LOC, the keystone]*

```lean
lemma pattern_event_measure (φ : ∂F2) (n : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range n) :
    step_measure
        {Y | ∀ i ∈ Finset.range n,
              (Y i ∈ awayGenFinset φ (X_walk i Y) ↔ i ∈ S)}
      = (3 : ℝ≥0∞)^S.card * (1 : ℝ≥0∞)^(n - S.card) * (1/4 : ℝ≥0∞)^n := by
  -- This is the keystone IMO computation. Induction on n.
  induction n with
  | zero => ...
  | succ n ih =>
    -- Disintegrate the `(n+1)`-product as `n`-product times the last factor.
    -- Conditioning on the prefix `(Y 0, …, Y (n-1))`, the last factor
    -- `Y n` is uniform on `Z` (4 elements) and `awayGenFinset φ (X_walk n Y)`
    -- is determined by the prefix and has cardinality 3.
    ...
```

**Tactic sketch — the inductive step.**

1. Apply Step A (`step_measure_finset_event`) to reduce to a measure on
   `Π i ∈ Finset.range (n+1), F2`.
2. Decompose `Finset.range (n+1) = Finset.range n ∪ {n}`. Use the
   measurable equivalence
   `(Π i ∈ Finset.range (n+1), F2) ≃ᵐ (Π i ∈ Finset.range n, F2) × F2`
   to write the `(n+1)`-product as a `Measure.prod` of the `n`-product
   and `Z_uniform`.
3. Use **Tonelli** (`MeasureTheory.lintegral_prod`) to write
   `μ_{n+1}(E) = ∫⁻ y : prefix, ∫⁻ z : F2, [(y,z) ∈ E] ∂Z_uniform ∂μ_n`.
4. The pattern condition splits cleanly:
   - For `i < n`: `Y i ∈ awayGenFinset φ (X_walk i Y) ↔ i ∈ S` is determined by the prefix `y`.
   - For `i = n`: `z ∈ awayGenFinset φ (X_walk n y) ↔ n ∈ S`.
5. The inner integral over `z`:
   - if `n ∈ S`: `Z_uniform(awayGenFinset φ (X_walk n y)) = 3/4`;
   - if `n ∉ S`: `Z_uniform(F2_generating_set \ awayGenFinset φ (X_walk n y)) = 1/4`,
     with the a.s. caveat that `Y n ∈ F2_generating_set` (handled by
     `walk_step_in_generating_set_ae`).
6. The inner integral is **a constant** (depends only on whether `n ∈ S`), so
   it factors out, and we apply IH for `μ_n` on the prefix event.

**Equivalent phrasing avoiding `Measure.prod` — direct approach via `infinitePi_pi`.**

Alternatively (this is the "no Tonelli" route), define for each `S ⊆ Finset.range n`
the cylinder sets:

```
B_S := { Y : ℕ → F2 | ∀ i < n,
         (i ∈ S → Y i ∈ awayGenFinset φ (X_walk i Y))
       ∧ (i ∉ S → Y i ∈ F2_generating_set \ awayGenFinset φ (X_walk i Y)) }.
```

`B_S` is **not** a `Set.pi`-cylinder because `awayGenFinset φ (X_walk i Y)` depends on
`Y_0, …, Y_{i-1}`. To handle this, parameterise by the prefix:

For each `(y_0, …, y_{n-1}) ∈ Z^n`, define
`A_i(y) := awayGenFinset φ (X_walk i (extend y))`. The event `B_S` equals
the **disjoint union over prefixes**:

```
B_S = ⋃_{(y_0,…,y_{n-1}) realising S}
        { Y | (Y 0, …, Y (n-1)) = (y_0,…,y_{n-1}) }.
```

Each fixed-prefix event is a singleton-cylinder, with measure
`(1/4)^n` by `infinitePi_pi` (L2). The number of realising prefixes is
`3^{|S|}` (Step F below). So `step_measure(B_S) = 3^{|S|} · (1/4)^n`.

**This second formulation is the cleaner one — it directly uses
`infinitePi_pi` (L2) on a singleton cylinder.**

### Step F — Prefix-counting lemma (the IMO core)  *[~40 LOC]*

```lean
lemma realising_prefix_count (φ : ∂F2) (n : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range n) :
    ((Finset.univ : Finset (Fin n → F2)).filter
        (fun y => (∀ i, y i ∈ F2_generating_set) ∧
                  (∀ i : Fin n,
                     y i ∈ awayGenFinset φ (X_walk i.val (extend y)) ↔ i.val ∈ S))).card
      = 3 ^ S.card := by
  -- Induction on n. Base case: empty product is one prefix.
  -- Step: for the (n+1)-st letter, multiply by 3 if n ∈ S else by 1.
  induction n with
  | zero => simp [Finset.filter_eq_empty_iff]
  | succ n ih =>
    -- Project away the last coordinate: |G_S^{(n+1)}| =
    --   |G_{S \ {n}}^{(n)}| · (3 if n ∈ S else 1).
    -- The "(3 if … else 1)" is the keystone count `|awayGenFinset| = 3`,
    -- `|F2_generating_set \ awayGenFinset| = 1` — both **independent of
    -- the prefix**, by `awayGenFinset_card φ x = 3` and the fact that
    -- `F2_generating_set` is a 4-element set.
    ...
```

**Mathlib lemmas used.**
- `awayGenFinset_card φ x = 3` (already proved, `RandomWalk.lean:464`)
- `awayGenFinset_subset φ x` (already proved, `RandomWalk.lean:476`)
- `Finset.card_filter`
- `Finset.card_image_of_injective`
- `F2_generating_set` is finite with 4 elements (need a small auxiliary
  `F2_generating_set_card : (F2_generating_set.toFinset).card = 4`)

**Watchpoints.**
- `F2_generating_set : Set F2`, not a `Finset`. Need `.toFinset` or
  carry an explicit `Finset` representation `F2_genFinset := {genA, genB, genA⁻¹, genB⁻¹}`.
- The four generators are **distinct** in `F_2`: this needs a small lemma
  (use `FreeGroup.toWord` injectivity, as in `walk_step_in_generating_set_ae`'s
  `hne` block).

### Step G — Sum over patterns of size `k`  *[~15 LOC]*

```lean
lemma sum_over_patterns (φ : ∂F2) (n k : ℕ) (hk : k ≤ n) :
    step_measure
        {Y | ∀ i ∈ Finset.range n,
              ∃ S, S ∈ (Finset.range n).powersetCard k ∧
                   (Y i ∈ awayGenFinset φ (X_walk i Y) ↔ i ∈ S)}
      = ((Finset.range n).powersetCard k).card * (3 : ℝ≥0∞)^k * (1/4 : ℝ≥0∞)^n
```

(or, more simply, sum the disjoint events from Step D):

```
P(∑ = k) = ∑ S ∈ powersetCard n k, P(B_S)
         = (n.choose k) · 3^k · (1/4)^n.
```

**Mathlib lemmas used.**
- `Finset.card_powersetCard`: `(Finset.range n).powersetCard k |>.card = n.choose k`
- `measure_biUnion_finset` (disjoint patterns ⇒ measure adds)
- `Finset.sum_const`, `Finset.card_powersetCard`

### Step H — Algebra: `(3/4)^k · (1/4)^{n-k} = 3^k · (1/4)^n`  *[~10 LOC]*

```lean
lemma pmf_algebra (n k : ℕ) (hk : k ≤ n) :
    (n.choose k : ℝ) * (3/4)^k * (1/4)^(n - k)
      = (n.choose k : ℝ) * 3^k * (1/4)^n := by
  rw [show ((3:ℝ)/4)^k = (3:ℝ)^k * (1/4)^k from by rw [div_pow]; ring]
  rw [← pow_add]
  congr; omega
```

Then the final theorem assembles by chaining Steps A → G plus the
algebra `pmf_algebra` and the `ENNReal.ofReal` cast:

```lean
theorem busemann_walk_sum_binomial_pmf (φ : ∂F2) (n k : ℕ) (hk : k ≤ n) :
    step_measure
        {Y | (Finset.range n).sum (fun i => away_indicator φ i Y) = k}
      = ENNReal.ofReal ((n.choose k : ℝ) * (3/4)^k * (1/4)^(n - k)) := by
  -- 1. A.s.-rewrite the event via `event_eq_disjUnion` (Step D).
  -- 2. Apply `sum_over_patterns` (Step G).
  -- 3. Cast `n.choose k * 3^k * (1/4)^n` between `ℕ`, `ℝ`, `ℝ≥0∞`.
  -- 4. Apply `pmf_algebra` (Step H) to match the target form.
  ...
```

---

## 5. LOC budget

| Step | Description | LOC |
|---|---|---|
| A | First-`n` projection lemma | 25 |
| B | Cylinder formula on finite product | 20 |
| C | `Z_uniform({z}) = 1/4` and `Z_uniform(F)` for `F ⊆ Z` | 30 |
| D | Event = a.s.-disjoint union over patterns | 15 |
| E | One-pattern measure (singleton-cylinder route) | 50 |
| F | **Prefix-counting lemma** (the IMO core) | 40 |
| G | Sum over patterns | 15 |
| H | Algebra rearrangement | 10 |
| Assembly | Final theorem | 15 |
| Auxiliary: `F2_generating_set_card = 4` and `_finset` form | 20 |
| **Total** | | **240 LOC** |

---

## 6. Watchpoints for the implementer

1. **`F2_generating_set : Set F2`, not `Finset`.** Need to introduce a
   `F2_genFinset : Finset F2` or use `F2_generating_set.toFinset` (requires
   `[Fintype F2_generating_set]`). The 4 elements
   `{genA, genB, genA⁻¹, genB⁻¹}` are pairwise distinct — see the existing
   `hne : Y i ≠ 1` block in `RandomWalk.lean:740` for the proof template.
   **Recommended:** add at the top of the new section:
   ```lean
   private noncomputable def F2_genFinset : Finset F2 :=
     {genA, genB, genA⁻¹, genB⁻¹}
   private lemma F2_genFinset_card : F2_genFinset.card = 4 := ...
   private lemma F2_genFinset_coe : ↑F2_genFinset = F2_generating_set := ...
   ```

2. **`away_indicator` returns `ℝ`, not `ℕ` or `ENNReal`.** The event
   `∑ i, away_indicator φ i Y = k` mixes `ℝ` and `ℕ`. Cast `(k : ℝ)` and
   reason via `Finset.sum_eq_card_iff_eq_one`-style lemmas a.s.

3. **`ENNReal` vs `ℝ`.** `step_measure` returns `ℝ≥0∞`. The PMF target is
   `ENNReal.ofReal (...)`. Convert via `ENNReal.ofReal_mul` (for non-negative
   reals), `ENNReal.ofReal_pow`, `ENNReal.ofReal_natCast`. **Watchpoint:**
   `ENNReal.ofReal x = x.toNNReal` only for `x ≥ 0` — verify positivity
   pre-conditions.

4. **`Nat.cast` chain `n.choose k → ℝ → ℝ≥0∞`.** Use
   `ENNReal.ofReal_natCast (n.choose k)` and
   `Nat.cast_injective` for the converse direction.

5. **`Finset.range n` vs `Fin n` re-indexing.** Mathlib's
   `Measure.infinitePi_map_restrict` produces a measure on
   `Π i : (Finset.range n : Finset ℕ), F2`. The natural way to work is
   to keep that subtype throughout, *not* convert to `Fin n`. The
   coordinate access `Y i.val` for `i : Finset.range n` is what
   `awayGenFinset φ (X_walk i.val Y)` needs.

6. **A.s. caveat for `away_indicator`.** The pointwise-vs-`if` equivalence
   `away_indicator_eq_indicator_of_gen` requires `Y k ∈ F2_generating_set`,
   which holds a.s. by `walk_step_in_generating_set_ae`. **Use
   `filter_upwards [walk_step_in_generating_set_ae]` everywhere this is
   needed, just as `away_indicator_aeEq` does.**

7. **`X_walk i Y` only depends on `Y_0, …, Y_{i-1}`** (already proved in
   `awayGenFinset_past`, `RandomWalk.lean:502`). This is the formal version
   of the IMO insight "multiplicity is constant on the prefix" — re-use
   the existing lemma.

8. **The "1" generator that goes toward `φ`.** The 1+3 decomposition
   means `awayGenFinset φ x` has cardinality 3 and lies in the 4-element
   `F2_generating_set`, so the "toward" generator is the unique element
   of `F2_generating_set \ awayGenFinset φ x`. We don't need to name it,
   only know `|F2_generating_set \ awayGenFinset φ x| = 1`.

9. **Disjointness of the patterns `B_S`.** Two distinct subsets `S, S' ⊆
   Finset.range n` give disjoint cylinder events: there is some `i`
   with (WLOG) `i ∈ S \ S'`, so on `B_S` we have `Y i ∈ awayGenFinset` and
   on `B_{S'}` we have `Y i ∉ awayGenFinset` — incompatible. This is a
   one-line `Set.disjoint_iff_forall_ne` argument; the implementer should
   not over-engineer it.

10. **Measurability of all events.** `F2` has the top σ-algebra
    (`MeasurableSpace F2 := ⊤`), so every set in `F2` and every set in
    `(Finset.range n) → F2` (top-σ-algebra products are top) is
    measurable. The events under consideration are all measurable for
    free; `MeasurableSet.of_discrete` closes any obligation. **Don't
    spend time on measurability proofs.**

---

## 7. No Mathlib gap

All required Mathlib pieces exist. The two load-bearing lemmas
`Measure.infinitePi_map_restrict` and `Measure.infinitePi_pi` (and the
finite `Measure.pi_pi`) handle the "infinite product → finite cylinder →
counting" reduction completely. No new admission and no auxiliary
Mathlib-API lemma is required.

If, during implementation, the `Π i : Finset.range n, F2` subtype
proves clunky compared to `Fin n → F2`, the small auxiliary
`measurePreserving_finsetRangeEquiv : MeasurePreserving (Π i : Finset.range n, F2) (Fin n → F2)`
can be built in ~10 LOC using `MeasurableEquiv.piCongrLeft`. This is
a convenience, not a gap.

---

## 8. Decoupling from Wave 28's existing parallel work

Wave 28 (the parallel implementer) is working on the i.i.d.-Bernoulli
identification via `iIndepFun_iIdentDistrib_uniformIndic_pastDep`. The
binomial PMF `busemann_walk_sum_binomial_pmf` proved here is **strictly
stronger** than the i.i.d.-Bernoulli identity at the marginal level:
joint distribution = product of marginals, with the marginal
identified as Bernoulli(3/4). Once this PMF is in hand, the i.i.d.
property is its corollary by inverting `iIndepFun_iff_map_fun_eq_infinitePi_map`
(`Mathlib/Probability/Independence/InfinitePi.lean:77`).

**Recommendation:** merge the two waves by closing the binomial PMF
first (this blueprint), then deriving `iIndepFun` and `IdentDistrib` as
corollaries. This **eliminates the companion axiom
`iIndepFun_iIdentDistrib_uniformIndic_pastDep`** and brings Q42 to
zero admissions.

---

**Status.** Blueprint complete. No code modified, no commits made.
Estimated implementation effort: ~240 LOC, 4–6 hours for an experienced
Lean/Mathlib developer.
