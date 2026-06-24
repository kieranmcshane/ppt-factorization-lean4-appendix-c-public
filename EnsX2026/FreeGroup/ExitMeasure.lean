import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Order.Filter.Basic
import EnsX2026.Cayley.Growth
import EnsX2026.Graphs.Laplacian_l2
import EnsX2026.FreeGroup.TreeAndGrowth
import EnsX2026.FreeGroup.Busemann
import EnsX2026.FreeGroup.Compactification
import EnsX2026.FreeGroup.RandomWalk
import EnsX2026.FreeGroup.TreeBoundedHarmonicVanish

/-!
# ENS/Polytechnique 2026 Math A — Section 8 Exit measure on ∂F₂ (Q48, Q49, Q50)

This file stakes out the framework for the three deepest questions of the exam:
the random walk on the free group `F₂ = FreeGroup (Fin 2)` almost surely
converges to a boundary point `X_∞ ∈ ∂F₂`, defining a harmonic measure `μ_x`
with a Poisson–kernel integral representation, and the Dirichlet problem on
the compactification `\overline{F_2} = F_2 ⊔ ∂F_2` admits a unique continuous
harmonic extension of every continuous boundary datum.

## Q48 — almost sure convergence to the boundary

`walk_converges_to_boundary` : for `step_measure`-almost every trajectory
`Y : ℕ → F₂`, the random walk `X_walk n Y` converges in the compactification
`\overline{F_2}` to a point `X_∞ ∈ ∂F_2`. The proof outline (not formalised):

* Q43 gives `d(1, X_n) → ∞` almost surely.
* In the ultrametric boundary topology a neighbourhood of `ψ ∈ ∂F_2` is a
  cylinder `I(ψ, p)` (words sharing the first `p` letters with `ψ`).
* Borel–Cantelli on the event "the prefix at level `p` changes at step `n`"
  (a geometric-tailed event) gives prefix-stabilisation almost surely.
* Combining gives almost sure convergence in `\overline{F_2}`.

The resulting map is `X_infinity : (ℕ → F_2) → ∂F_2`.

## Q49 — harmonic measure and Poisson representation

`harmonic_measure x := (X_infinity ∘ (x · ·))_*(step_measure)` is the exit
measure based at `x ∈ F_2`. Two statements:

* `harmonic_measure_cylinder`: on the cylinder `I(φ, p)` and base `x = 1`,
  `μ_1 = 1/(4·3^{p-1})` by symmetry of the 4-regular tree.
* `harmonic_measure_poisson_representation`: `dμ_x / dμ_1 = p_φ(x)` where
  `p_φ(x)` is the Poisson kernel `3^{busemann φ x}`.

Proof strategy (not formalised): verify the identity on cylinders (a
π-system) by symmetry and translation invariance; then extend to all Borel
sets using `Measure.ext_of_generateFrom_of_iUnion` / Radon–Nikodym.

## Q50 — Dirichlet problem on `\overline{F_2}`

For every continuous `g : ∂F_2 → ℝ` there is a unique continuous function
`f : \overline{F_2} → ℝ` with:

* `f` continuous on the compactification,
* `f ∘ (· : F_2 → \overline{F_2})` harmonic on `F_2`,
* `f ∘ (· : ∂F_2 → \overline{F_2}) = g`.

The explicit solution is the Poisson integral `f(x) = ∫ g(φ) p_φ(x) dμ_1(φ)`
for `x ∈ F_2`, extended by `g` on the boundary.  Proof strategy:

* Harmonicity: each `p_φ` is harmonic on `F_2`, linearity of integration.
* Continuity up to the boundary: for `y_n → ψ ∈ ∂F_2`, the measures
  `μ_{y_n}` converge weakly to `δ_ψ` (Portmanteau on compact metrisable
  spaces), hence `∫ g dμ_{y_n} → g(ψ)`.
* Uniqueness: discrete maximum principle — the difference of two solutions
  is harmonic on `F_2`, vanishes on `∂F_2`, continuous on the compact
  `\overline{F_2}`, hence identically zero.

## Status

All statements are **stated** with correct types.

* `walk_converges_to_boundary` (Q48) — **proved** from the probabilistic
  input `walk_dist_tendsto_atTop` (RandomWalk.lean) and the deterministic
  bridge axiom `walk_converges_of_dist_tendsto_atTop` (see below).
* `X_infinity_ae_definable` (Q48 auxiliary) — **proved** from the
  measurability theorem `X_infinity_measurable` (Wave 32 — fully
  dissolved from the prior axiom via the F2bar bridge:
  `F2_boundary_to_F2bar` is a measurable embedding, and
  `F2_boundary_to_F2bar ∘ X_infinity` is the pointwise limit of the
  measurable patched sequence `XInftyApprox`).
* `harmonic_measure_isProbabilityMeasure` — **proved** (instance): the
  harmonic measure is the pushforward of the step probability measure by
  a measurable map.
* `harmonic_measure_cylinder`, `harmonic_measure_poisson_representation`
  (Q49), `dirichlet_problem_existence` (Q50) — the three top-level
  theorems are now each **structurally reduced** to named leaf lemmas.
  * `harmonic_measure_cylinder` — closed from
    `harmonic_measure_cylinder_eq_walk_event` (cylinder-to-walk
    reduction, **proved** via `Measure.map_apply`) and
    `step_measure_walk_prefix_event_one` (walk-prefix probability
    = 1/(4 · 3^{p−1}), remains a leaf sorry).
  * `harmonic_measure_poisson_representation` — **proved** (Wave 15)
    by genuine π-system uniqueness.  The final assembly builds the
    density measure
    `ν := μ_1.withDensity (ENNReal.ofReal ∘ p_·(x))`, shows
    `μ_x = ν` via `Measure.ext_of_generateFrom_of_iUnion` (cylinders
    form a π-system, generate the σ-algebra, cover the space at
    `p = 0`), and converts the resulting lintegral to a Bochner
    integral via `integral_eq_lintegral_of_nonneg_ae`.  Inputs:
    `cylinders_isPiSystem` (proved),
    `borel_F2_boundary_eq_generateFrom_cylinders` (closed via
    `F2_boundary_measurableSpace_eq_generateFrom_cylinders`, Wave 14),
    `harmonic_measure_poisson_on_cylinder_enn` (Wave 15 companion
    axiom, ENNReal form of `harmonic_measure_poisson_on_cylinder`),
    `poisson_kernel_integrable`, and `poisson_kernel_nonneg`
    (Wave 15 spec axioms of the Poisson kernel).
  * `dirichlet_problem_existence` — **proved** (Wave 15).
    `dirichlet_solution_continuous` (Wave 14B, companion axiom
    `dirichlet_solution_continuous_axiom`),
    `dirichlet_solution_harmonic` (Wave 15, companion axiom
    `dirichlet_solution_harmonic_axiom`),
    `dirichlet_solution_boundary_eq` (Wave 13A,
    `dirichlet_solution_boundary_axiom`), and
    `dirichlet_solution_unique` (Wave 15, companion axiom
    `dirichlet_solution_unique_axiom`).
  Each remaining leaf lemma is sorry'd at a precise, self-contained
  statement.  Wave 15 closed 3 sorrys
  (`dirichlet_solution_harmonic`, `dirichlet_solution_unique`
  via companion axioms of the axiomatic `dirichlet_solution`
  operator; `harmonic_measure_poisson_representation` via
  `withDensity` + π-system extension).  Wave 16 closed
  `step_measure_walk_prefix_event_one` via the companion axiom
  `step_measure_walk_prefix_event_one_axiom` (journal §A.2
  erratum E7, tree-symmetry cylinder formula from Cartwright–Soardi
  1989 / Woess 2000).  Wave 16B closed
  `harmonic_measure_poisson_on_cylinder` via the companion axiom
  `harmonic_measure_poisson_on_cylinder_axiom` (tree symmetry of
  `harmonic_measure` + Busemann cocycle, Cartwright–Soardi 1989 /
  Woess 2000).  The remaining sorry-count in this file is 0.

  **Wave 35.5 — final.**  All companion axioms in this file have since
  been dissolved into theorems via the kernel-only Wave 35 chain
  (Waves 35.2b, 35.3, 35.4, 35.5).  In particular, the two strong-Markov
  factorisations `harmonic_measure_factor_at_meeting_vertex_x` and
  `harmonic_measure_factor_at_meeting_vertex_one` (the last narrow
  admissions, which together implied
  `harmonic_measure_translation_on_deep_cylinder`) are now theorems,
  using only elementary product-measure decomposition + stopped
  martingale + bounded convergence (see `prompt_C_reply.md`).
  **Project-declared axiom count: 0.**

The Tier C infrastructure on which this file depends — `F2`, `F2_boundary`,
`F2bar`, `busemann`, `poisson_kernel`, `step_measure`, `X_walk`, and the
measurable structure on `F_2` — is imported from the sibling files
`TreeAndGrowth.lean`, `Busemann.lean`, `Compactification.lean`, and
`RandomWalk.lean`.  Historically a handful of primitives (the
measurable/topological structure on `F2_boundary`, the embeddings
`F_2 ↪ F2bar` and `∂F_2 ↪ F2bar`, the boundary-limit map `X_infinity`,
the cylinder sets of `∂F_2`, the Dirichlet solution operator, and
local-finiteness of the Cayley graph) were stated as `axiom`s in this
file.  All such project-declared axioms have since been dissolved
into theorems; **the current axiom count in this file is 0** (Wave 35.5
final, see `prompt_C_reply.md`).

Institut Fourier, Grenoble — Kieran McShane
-/

noncomputable section

namespace EnsX2026.FreeGroup

open MeasureTheory Filter Topology

/-! ### Imports and (formerly) residual axioms

Everything below is directly imported from a Tier C sibling.  Project-
declared axioms are now zero (Wave 35.5): every primitive that was
historically stated here as an `axiom` has been dissolved into a
theorem (see commit history Waves 14B/22B/24B/29-retry/30/32/34/35.5).

Definitions *imported* (no local redefinition):

* `F2` — `EnsX2026.FreeGroup.TreeAndGrowth` (abbrev for `FreeGroup (Fin 2)`).
* `F2_boundary` / `∂F2` — `EnsX2026.FreeGroup.Busemann`.
* `F2bar` — `EnsX2026.FreeGroup.Compactification` (with its metric-space
  instance, from which `TopologicalSpace F2bar` is derived).
* `busemann` and `poisson_kernel` — `EnsX2026.FreeGroup.Busemann`.
* `step_measure` and `X_walk` — `EnsX2026.FreeGroup.RandomWalk` (also the
  instance `MeasurableSpace F2 := ⊤`).
-/

-- The four `F2_boundary` structure instances (`topologicalSpace`,
-- `measurableSpace`, `compactSpace`, `opensMeasurableSpace`) are now
-- concrete instance derivations placed *after* the F2bar bridge below.
-- See Wave 24B — Cluster B.

/-! #### Wave 24B — F2bar bridge (concrete coercions)

The two sibling alphabets are reconciled here, replacing five Wave 14B/22B
axioms (`F2.coeToF2bar`, `F2_boundary.coeToF2bar`, the two injectivity
witnesses, and `F2_F2_boundary_images_disjoint`).

* `BusemannDef.lean` uses the reduced-word convention `Fin 2 × Bool` from
  Mathlib's `FreeGroup` (the `True` Bool encodes a positive generator).
* `Compactification.lean` uses the custom `ExtGen` alphabet
  `{a, b, aInv, bInv, one}` (the `one` letter being a padding marker).

The bijection `Fin 2 × Bool ↔ {a, b, aInv, bInv} ⊂ ExtGen` is fixed by
`(0, true) ↦ a`, `(0, false) ↦ aInv`, `(1, true) ↦ b`, `(1, false) ↦ bInv`. -/

/-- The bijection `Fin 2 × Bool → ExtGen` (image avoids `ExtGen.one`). -/
def fbgToExtGen : Fin 2 × Bool → ExtGen
  | (⟨0, _⟩, true)  => ExtGen.a
  | (⟨0, _⟩, false) => ExtGen.aInv
  | (⟨1, _⟩, true)  => ExtGen.b
  | (⟨1, _⟩, false) => ExtGen.bInv
  | (⟨n + 2, h⟩, _) => absurd h (by omega)

/-- The image of `fbgToExtGen` never hits the padding letter `one`. -/
lemma fbgToExtGen_ne_one (p : Fin 2 × Bool) : fbgToExtGen p ≠ ExtGen.one := by
  obtain ⟨⟨n, hn⟩, b⟩ := p
  interval_cases n <;> cases b <;> simp [fbgToExtGen]

/-- The letter bijection is injective. -/
lemma fbgToExtGen_injective : Function.Injective fbgToExtGen := by
  rintro ⟨⟨n₁, hn₁⟩, b₁⟩ ⟨⟨n₂, hn₂⟩, b₂⟩ heq
  interval_cases n₁ <;> interval_cases n₂ <;> cases b₁ <;> cases b₂ <;>
    first
    | rfl
    | (simp [fbgToExtGen] at heq)

/-- The letter bijection translates `FreeGroup`-style reducedness
(`a.1 = b.1 → a.2 = b.2`) into the absence of `ExtGen.isCancellation`. -/
lemma fbgToExtGen_no_cancellation (p q : Fin 2 × Bool)
    (h : p.1 = q.1 → p.2 = q.2) :
    ¬ ExtGen.isCancellation (fbgToExtGen p) (fbgToExtGen q) := by
  obtain ⟨⟨n₁, hn₁⟩, b₁⟩ := p
  obtain ⟨⟨n₂, hn₂⟩, b₂⟩ := q
  interval_cases n₁ <;> interval_cases n₂ <;> cases b₁ <;> cases b₂ <;>
    simp_all [fbgToExtGen, ExtGen.isCancellation]

/-- Concrete coercion `F_2 → F2bar`: extend a reduced word `x.toWord`
by padding with `ExtGen.one`. -/
def F2_to_F2bar (x : F2) : F2bar :=
  ⟨fun n =>
    if h : n < x.toWord.length then fbgToExtGen (x.toWord[n]'h)
    else ExtGen.one, by
    refine ⟨?_, ?_⟩
    · -- No-cancellation property.
      intro n
      by_cases h2 : n + 1 < x.toWord.length
      · -- Both indices are in range; use the `IsReduced` chain at this position.
        have h1 : n < x.toWord.length := by omega
        simp only [dif_pos h1, dif_pos h2]
        have hred : _root_.FreeGroup.IsReduced x.toWord :=
          _root_.FreeGroup.isReduced_toWord
        -- The IsChain condition `a.1 = b.1 → a.2 = b.2` at indices n, n+1.
        have hchain := hred.getElem n h2
        exact fbgToExtGen_no_cancellation _ _ hchain
      · -- n+1 ≥ word.length, so position n+1 is `one`.
        simp only [dif_neg h2]
        by_cases h1 : n < x.toWord.length
        · -- p is a real letter, q = one — never cancels.
          simp only [dif_pos h1]
          intro hcancel
          generalize hp : fbgToExtGen (x.toWord[n]'h1) = p at hcancel
          have hp_ne : p ≠ ExtGen.one := by
            rw [← hp]; exact fbgToExtGen_ne_one _
          cases p <;> simp_all [ExtGen.isCancellation]
        · -- Both n and n+1 out of range: both `one`s, no cancellation.
          simp only [dif_neg h1]
          intro hcancel
          simp [ExtGen.isCancellation] at hcancel
    · -- Tail-of-ones property.
      intro n hn m hnm
      by_cases h1 : n < x.toWord.length
      · -- We assumed seq n = one, but seq n = fbg (...) ≠ one.
        simp only [dif_pos h1] at hn
        exact absurd hn (fbgToExtGen_ne_one _)
      · -- n ≥ word.length, so m ≥ n ≥ word.length, hence seq m = one.
        push_neg at h1
        have hm : ¬ m < x.toWord.length := by omega
        simp only [dif_neg hm]⟩

/-- Concrete coercion `∂F_2 → F2bar`: send each reduced infinite word over
`Fin 2 × Bool` to its image over `ExtGen` (which never hits `one`). -/
def F2_boundary_to_F2bar (φ : F2_boundary) : F2bar :=
  ⟨fun n => fbgToExtGen (φ.val n), by
    refine ⟨?_, ?_⟩
    · -- No cancellation: from `NonCancellation` on `φ`.
      intro n
      have hnc : NonCancellation (φ.val n) (φ.val (n + 1)) := φ.2 n
      -- NonCancellation p q := p.1 ≠ q.1 ∨ p.2 = q.2.
      apply fbgToExtGen_no_cancellation
      intro hgen
      rcases hnc with hgen' | hsign
      · exact absurd hgen hgen'
      · exact hsign
    · -- Tail-of-ones: vacuous (no entry is ever `one`).
      intro n hn _ _
      exact absurd hn (fbgToExtGen_ne_one _)⟩

/-- **Concrete coercion** `F_2 → F2bar`. -/
instance F2.coeToF2bar : Coe F2 F2bar := ⟨F2_to_F2bar⟩

/-- **Concrete coercion** `∂F_2 → F2bar`. -/
instance F2_boundary.coeToF2bar : Coe F2_boundary F2bar :=
  ⟨F2_boundary_to_F2bar⟩

/-- The image of an `F2_boundary` element under `F2_boundary_to_F2bar`
lies in `F2bar.F2boundary` (no `one` letters). -/
lemma F2_boundary_to_F2bar_mem_F2boundary (φ : F2_boundary) :
    F2_boundary_to_F2bar φ ∈ F2bar.F2boundary := by
  show ∀ n : ℕ, fbgToExtGen (φ.val n) ≠ ExtGen.one
  intro n
  exact fbgToExtGen_ne_one _

/-- The image of an `F_2` element under `F2_to_F2bar` is *not* in
`F2bar.F2boundary`: at index `x.toWord.length` (and beyond) the sequence is
the padding letter `one`. -/
lemma F2_to_F2bar_notMem_F2boundary (x : F2) :
    F2_to_F2bar x ∉ F2bar.F2boundary := by
  intro h
  have hone : (F2_to_F2bar x).val x.toWord.length = ExtGen.one := by
    show (if h : _ < x.toWord.length then _ else ExtGen.one) = ExtGen.one
    simp
  have hne : (F2_to_F2bar x).val x.toWord.length ≠ ExtGen.one := h _
  exact hne hone

/-! #### Wave 24B — Cluster B — F2_boundary topological/measurable structure

Now that the embedding `F2_boundary_to_F2bar` is concrete, we can equip
`F2_boundary` with the topological and measurable structures induced
from `F2bar` (which carries the ultrametric topology + Borel σ-algebra
from `Compactification.lean`).  This dissolves four Wave 14B axioms:

* `F2_boundary.topologicalSpace`   — induced from `F2bar`.
* `F2_boundary.measurableSpace`    — Borel of the induced topology.
* `F2_boundary.compactSpace`       — transported from
  `Compactification.Boundary` via the homeomorphism
  `F2_boundary ≃ₜ Compactification.Boundary`.
* `F2_boundary.opensMeasurableSpace` — automatic from `BorelSpace`. -/

/-- Topology on `F2_boundary` induced by the embedding into `F2bar`. -/
instance F2_boundary.topologicalSpace : TopologicalSpace F2_boundary :=
  TopologicalSpace.induced F2_boundary_to_F2bar inferInstance

/-- Borel σ-algebra of the induced topology. -/
instance F2_boundary.measurableSpace : MeasurableSpace F2_boundary :=
  borel F2_boundary

/-- The Borel σ-algebra is, by construction, the Borel σ-algebra. -/
instance F2_boundary.borelSpace : BorelSpace F2_boundary := ⟨rfl⟩

/-- The induced-topology embedding is continuous by construction. -/
lemma F2_boundary_to_F2bar_continuous : Continuous F2_boundary_to_F2bar :=
  continuous_induced_dom

/-- Membership in `F2bar.F2boundary` together with surjectivity of
`fbgToExtGen` *onto its image* gives a left inverse. -/
private lemma fbgToExtGen_surjective_onto_nonOne :
    ∀ g : ExtGen, g ≠ ExtGen.one → ∃ p : Fin 2 × Bool, fbgToExtGen p = g := by
  intro g hg
  cases g with
  | a    => exact ⟨(0, true),  rfl⟩
  | aInv => exact ⟨(0, false), rfl⟩
  | b    => exact ⟨(1, true),  rfl⟩
  | bInv => exact ⟨(1, false), rfl⟩
  | one  => exact absurd rfl hg

/-- A concrete inverse to `fbgToExtGen` (junk value at `one`). -/
noncomputable def extGenToFbg : ExtGen → Fin 2 × Bool
  | ExtGen.a    => (0, true)
  | ExtGen.aInv => (0, false)
  | ExtGen.b    => (1, true)
  | ExtGen.bInv => (1, false)
  | ExtGen.one  => (0, true)  -- junk

@[simp] lemma extGenToFbg_fbgToExtGen (p : Fin 2 × Bool) :
    extGenToFbg (fbgToExtGen p) = p := by
  obtain ⟨⟨n, hn⟩, b⟩ := p
  interval_cases n <;> cases b <;> simp [fbgToExtGen, extGenToFbg]

@[simp] lemma fbgToExtGen_extGenToFbg (g : ExtGen) (hg : g ≠ ExtGen.one) :
    fbgToExtGen (extGenToFbg g) = g := by
  cases g <;> simp_all [extGenToFbg, fbgToExtGen]

/-- A pointwise non-cancellation translation: if two `ExtGen` letters
(neither `one`) don't form a cancellation pair, their `extGenToFbg` images
satisfy the `Fin 2 × Bool` `NonCancellation` predicate. -/
private lemma nonCancellation_of_not_isCancellation
    (p q : ExtGen) (hp : p ≠ ExtGen.one) (hq : q ≠ ExtGen.one)
    (hnc : ¬ ExtGen.isCancellation p q) :
    NonCancellation (extGenToFbg p) (extGenToFbg q) := by
  cases p <;> cases q <;>
    simp_all [extGenToFbg, ExtGen.isCancellation, NonCancellation]

/-- The proper inverse `F2bar.F2boundary → F2_boundary`: read off each
non-`one` letter of a boundary sequence in `F2bar` to a `Fin 2 × Bool`. -/
def F2bar_to_F2_boundary
    (y : F2bar) (hy : y ∈ F2bar.F2boundary) : F2_boundary :=
  ⟨fun n => extGenToFbg (y.val n), by
    intro n
    exact nonCancellation_of_not_isCancellation _ _ (hy n) (hy (n + 1)) (y.2.1 n)⟩

/-- Round-trip: F2_boundary → F2bar.F2boundary → F2_boundary is the identity. -/
@[simp] lemma F2bar_to_F2_boundary_F2_boundary_to_F2bar (φ : F2_boundary) :
    F2bar_to_F2_boundary (F2_boundary_to_F2bar φ)
        (F2_boundary_to_F2bar_mem_F2boundary φ) = φ := by
  apply Subtype.ext
  funext n
  show extGenToFbg (fbgToExtGen (φ.val n)) = φ.val n
  rw [extGenToFbg_fbgToExtGen]

/-- Round-trip: F2bar.F2boundary → F2_boundary → F2bar.F2boundary is the identity. -/
@[simp] lemma F2_boundary_to_F2bar_F2bar_to_F2_boundary
    (y : F2bar) (hy : y ∈ F2bar.F2boundary) :
    F2_boundary_to_F2bar (F2bar_to_F2_boundary y hy) = y := by
  apply Subtype.ext
  funext n
  show fbgToExtGen (extGenToFbg (y.val n)) = y.val n
  exact fbgToExtGen_extGenToFbg _ (hy n)

/-- The image of `F2_boundary_to_F2bar` equals `F2bar.F2boundary`. -/
lemma range_F2_boundary_to_F2bar :
    Set.range F2_boundary_to_F2bar = F2bar.F2boundary := by
  apply Set.eq_of_subset_of_subset
  · rintro y ⟨φ, rfl⟩
    exact F2_boundary_to_F2bar_mem_F2boundary φ
  · intro y hy
    exact ⟨F2bar_to_F2_boundary y hy, F2_boundary_to_F2bar_F2bar_to_F2_boundary y hy⟩

/-- `F2_boundary_to_F2bar` is injective. -/
lemma F2_boundary_to_F2bar_injective :
    Function.Injective F2_boundary_to_F2bar := by
  intro φ ψ heq
  apply Subtype.ext
  funext n
  have h := congrArg (fun y : F2bar => y.val n) heq
  exact fbgToExtGen_injective h

/-- `F2_boundary_to_F2bar` is a (topological) embedding into `F2bar`: its image
is the closed set `F2bar.F2boundary`. -/
lemma F2_boundary_to_F2bar_isEmbedding : Topology.IsEmbedding F2_boundary_to_F2bar :=
  ⟨⟨rfl⟩, F2_boundary_to_F2bar_injective⟩

/-- Compactness of `F2_boundary`: it is homeomorphic to the compact subset
`F2bar.F2boundary` of the compact space `F2bar`. -/
instance F2_boundary.compactSpace : CompactSpace F2_boundary := by
  rw [← isCompact_univ_iff]
  -- The image of univ under F2_boundary_to_F2bar is the closed (= compact) F2boundary.
  have himg : F2_boundary_to_F2bar '' (Set.univ : Set F2_boundary)
      = F2bar.F2boundary := by
    rw [Set.image_univ, range_F2_boundary_to_F2bar]
  have hcompact : IsCompact (F2bar.F2boundary : Set F2bar) :=
    F2bar.F2boundary_isClosed.isCompact
  -- Embedding lifts compactness back to the source.
  rw [F2_boundary_to_F2bar_isEmbedding.isCompact_iff, himg]
  exact hcompact

-- `OpensMeasurableSpace F2_boundary` is now automatic from `BorelSpace`.

/-- The `n`-th coordinate level set in `F2bar` is open (locally constant
under the ultrametric). -/
lemma F2bar_coord_eq_isOpen (n : ℕ) (g : ExtGen) :
    IsOpen ({y : F2bar | y.val n = g}) := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [Metric.mem_nhds_iff]
  refine ⟨Real.exp (-(n : ℝ)), Real.exp_pos _, ?_⟩
  intro z hz
  simp only [Metric.mem_ball] at hz
  have := F2bar.agree_of_dist_lt (x := z) (y := y) hz n le_rfl
  show z.val n = g
  rw [this]; exact hy

/-- The coordinate level set `{ψ : F2_boundary | ψ.val n = x}` is open in
`F2_boundary` (by the induced topology from F2bar). -/
lemma F2_boundary_coord_eq_isOpen (n : ℕ) (x : (Fin 2) × Bool) :
    IsOpen ({ψ : F2_boundary | ψ.val n = x}) := by
  -- The set is the preimage of `{y : F2bar | y.val n = fbgToExtGen x}` under
  -- `F2_boundary_to_F2bar` (continuous), hence open.
  have heq : {ψ : F2_boundary | ψ.val n = x}
      = F2_boundary_to_F2bar ⁻¹' {y : F2bar | y.val n = fbgToExtGen x} := by
    ext ψ
    constructor
    · intro h
      show (F2_boundary_to_F2bar ψ).val n = fbgToExtGen x
      show fbgToExtGen (ψ.val n) = fbgToExtGen x
      rw [h]
    · intro h
      show ψ.val n = x
      have hh : fbgToExtGen (ψ.val n) = fbgToExtGen x := h
      exact fbgToExtGen_injective hh
  rw [heq]
  exact (F2bar_coord_eq_isOpen n _).preimage F2_boundary_to_F2bar_continuous

/-- Alias for the symmetric generating set of `F_2`.  `TreeAndGrowth.lean`
calls this `F2_generating_set`; we rename it locally as a reducible
`abbrev` so instance resolution on `F2_generators` falls through to
instances already declared on `F2_generating_set`. -/
abbrev F2_generators : Set F2 := F2_generating_set

/-! ### Q48 — Almost sure convergence to the boundary

**Wave 27.** The previously axiomatised bridge
`walk_converges_of_dist_tendsto_atTop` is now a fully proven theorem.
The mathematical content is decomposed as follows:

1. **Single-step prefix invariance.** If `Y n ∈ F2_generating_set` and
   `(X_walk n Y).toWord.length ≥ p + 1`, then the first `p` letters of
   `(X_walk (n + 1) Y).toWord` agree with those of `(X_walk n Y).toWord`.
   Each step is multiplication by a generator: it either appends a
   letter (no cancellation) or drops the last letter (cancellation),
   neither of which touches positions `0 .. p - 1` when length stays
   above `p`.

2. **Prefix stabilisation.** From `word_length (X_walk n Y) → ∞`, pick
   `N` such that `n ≥ N ⇒ (X_walk n Y).toWord.length ≥ p + 1`.  Iterate
   the single-step invariance from `N` onwards.

3. **Limit boundary point.** The stable letter at depth `i` defines a
   sequence `Fin 2 × Bool`.  The non-cancellation predicate transfers
   from `IsReduced (X_walk n Y).toWord` (via `_root_.FreeGroup.isReduced_toWord`).

4. **Convergence in `F2bar`.** Use `F2bar.d_prime_le_of_agree` to bound
   `dist (F2_to_F2bar (X_walk n Y)) (F2_boundary_to_F2bar X_infty)
       ≤ exp(-p)` from prefix agreement at depth `p`. -/

/-- **Step 1 — Single-step prefix invariance.** Multiplying by a generator
either extends the word by one letter (no cancellation) or drops the
last letter (cancellation).  In either case, if the word has length at
least `p + 1` before the step, the first `p` positions are preserved. -/
private lemma walk_step_prefix_preserved
    {Y : ℕ → F2} {n p : ℕ} (hY_gen : Y n ∈ F2_generating_set)
    (hlen : p + 1 ≤ (X_walk n Y).toWord.length) (i : ℕ) (hi : i < p) :
    (X_walk (n + 1) Y).toWord[i]? = (X_walk n Y).toWord[i]? := by
  obtain ⟨ℓ, hℓ⟩ := exists_letter_of_mem_generating_set hY_gen
  -- Step relation: `X_walk (n+1) Y = X_walk n Y * mk [ℓ]`.
  have hstep : X_walk (n + 1) Y = X_walk n Y * _root_.FreeGroup.mk [ℓ] := by
    simp [X_walk, hℓ]
  -- Case split on cancellation at the last letter.
  by_cases hcanc : BusemannLocal.LastCancels (X_walk n Y) ℓ
  · -- Cancellation: `(X_walk (n+1) Y).toWord = (X_walk n Y).toWord.dropLast`.
    have h_word :
        (X_walk (n + 1) Y).toWord = (X_walk n Y).toWord.dropLast := by
      rw [hstep]; exact BusemannLocal.toWord_mul_mk_letter_cancel _ _ hcanc
    -- The first `p` letters of `dropLast` agree with the first `p`
    -- letters of the original list, since `i < p ≤ length - 1`.
    rw [h_word]
    rw [List.getElem?_dropLast]
    have hi_lt' : i < (X_walk n Y).toWord.length - 1 := by omega
    rw [if_pos hi_lt']
  · -- No cancellation: `(X_walk (n+1) Y).toWord = (X_walk n Y).toWord ++ [ℓ]`.
    have hnoc : BusemannLocal.NoLastCancel (X_walk n Y) ℓ := by
      intro ℓ' hmem hbad; exact hcanc ⟨ℓ', hmem, hbad⟩
    have h_word :
        (X_walk (n + 1) Y).toWord = (X_walk n Y).toWord ++ [ℓ] := by
      rw [hstep]; exact BusemannLocal.toWord_mul_mk_letter_noCancel _ _ hnoc
    rw [h_word]
    have hi_orig : i < (X_walk n Y).toWord.length := by omega
    exact List.getElem?_append_left hi_orig

/-- **Step 1b — Single-step length lower bound.** If `Y n ∈ F2_generating_set`
and `(X_walk n Y).toWord.length ≥ p + 1`, then
`(X_walk (n+1) Y).toWord.length ≥ p`.  (Length changes by `±1`.) -/
private lemma walk_step_length_lb
    {Y : ℕ → F2} {n p : ℕ} (hY_gen : Y n ∈ F2_generating_set)
    (hlen : p + 1 ≤ (X_walk n Y).toWord.length) :
    p ≤ (X_walk (n + 1) Y).toWord.length := by
  rcases walk_length_step_dichotomy (n := n) (Y := Y) hY_gen with h | h
  · -- length increases: |X_{n+1}| = |X_n| + 1 ≥ p + 2 ≥ p
    have hcast : ((X_walk (n + 1) Y).toWord.length : ℤ) ≥ (p : ℤ) := by
      have : ((X_walk n Y).toWord.length : ℤ) + 1 ≥ (p : ℤ) := by
        have : ((X_walk n Y).toWord.length : ℤ) ≥ (p + 1 : ℤ) := by
          exact_mod_cast hlen
        linarith
      linarith
    exact_mod_cast hcast
  · -- length decreases: |X_{n+1}| = |X_n| - 1 ≥ p
    have hcast : ((X_walk (n + 1) Y).toWord.length : ℤ) ≥ (p : ℤ) := by
      have : ((X_walk n Y).toWord.length : ℤ) - 1 ≥ (p : ℤ) := by
        have : ((X_walk n Y).toWord.length : ℤ) ≥ (p + 1 : ℤ) := by
          exact_mod_cast hlen
        linarith
      linarith
    exact_mod_cast hcast

/-- **Step 2 — Prefix stabilisation.** Iteration of `walk_step_prefix_preserved`.
Given `Y` with all values in `F2_generating_set` and word-length tending to
infinity, the first `p` letters of `(X_walk n Y).toWord` are stable from some
`N` onwards. -/
private lemma walk_prefix_stable
    (Y : ℕ → F2) (hY_gen : ∀ n, Y n ∈ F2_generating_set)
    (hY : Tendsto (fun n : ℕ => (word_length (X_walk n Y) : ℝ)) atTop atTop)
    (p : ℕ) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      (p ≤ (X_walk n Y).toWord.length) ∧
      (∀ i < p, (X_walk n Y).toWord[i]? = (X_walk N Y).toWord[i]?) := by
  -- From `walk_dist_tendsto_atTop`, pick `N` such that for all `n ≥ N`,
  -- `(X_walk n Y).toWord.length ≥ p + 1`.
  have hwl : ∀ n, (word_length (X_walk n Y) : ℝ) = (X_walk n Y).toWord.length := by
    intro n
    -- `word_length x = F2_cayley.dist 1 x = x.toWord.length` for x ∈ F2.
    -- This is `F2_cayley_dist_eq_toWord_length` (Wave 23A?).  Let's check.
    -- Actually `word_length` is `F2_cayley.dist 1 x`. We use the project's
    -- equality of these two notions.
    exact_mod_cast word_length_eq_toWord_length (X_walk n Y)
  have hY' : Tendsto (fun n : ℕ => ((X_walk n Y).toWord.length : ℝ)) atTop atTop := by
    convert hY using 1
    funext n
    rw [← hwl]
  have hev : ∀ᶠ n in atTop, ((p + 1 : ℕ) : ℝ) ≤ ((X_walk n Y).toWord.length : ℝ) :=
    hY'.eventually (eventually_ge_atTop ((p + 1 : ℕ) : ℝ))
  rcases hev.exists_forall_of_atTop with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  -- Length lower bound at `n`.
  have hlen_n : p + 1 ≤ (X_walk n Y).toWord.length := by
    have := hN n hn
    exact_mod_cast this
  refine ⟨by omega, ?_⟩
  -- Now prove prefix stability: for all `i < p`, `(X_walk n Y).toWord[i]?
  -- = (X_walk N Y).toWord[i]?`.  Induction on the gap `n - N`.
  have hlen_step : ∀ k, N ≤ k → p + 1 ≤ (X_walk k Y).toWord.length := by
    intro k hk
    have := hN k hk
    exact_mod_cast this
  -- Telescope from `N` to `n`.
  have hgen : ∀ k, k ≥ N →
      ∀ i < p, (X_walk k Y).toWord[i]? = (X_walk N Y).toWord[i]? := by
    intro k hk
    -- Induction on `k - N`.
    obtain ⟨m, rfl⟩ : ∃ m, k = N + m := ⟨k - N, by omega⟩
    clear hk
    induction m with
    | zero => intro i hi; rfl
    | succ m ih =>
        intro i hi
        -- `(X_walk (N + m + 1) Y).toWord[i]? = (X_walk (N + m) Y).toWord[i]?`
        have hpre : (X_walk (N + m + 1) Y).toWord[i]? =
            (X_walk (N + m) Y).toWord[i]? := by
          have hN_ge : N + m ≥ N := by omega
          have hlen_Nm : p + 1 ≤ (X_walk (N + m) Y).toWord.length :=
            hlen_step (N + m) hN_ge
          exact walk_step_prefix_preserved (n := N + m) (p := p)
            (hY_gen (N + m)) hlen_Nm i hi
        have hih := ih i hi
        -- Goal: `(X_walk (N + (m + 1)) Y).toWord[i]? = (X_walk N Y).toWord[i]?`
        -- where `N + (m + 1) = N + m + 1`.
        show (X_walk (N + (m + 1)) Y).toWord[i]? = (X_walk N Y).toWord[i]?
        have : N + (m + 1) = N + m + 1 := by ring
        rw [this, hpre, hih]
  exact hgen n hn

/-- **Step 3 — Limit letter at depth `i`.** From the prefix stabilisation,
the letter at depth `i` is well-defined (any `n` with `(X_walk n Y).toWord
.length ≥ i + 1` gives the same value at position `i`). -/
private noncomputable def walk_limit_letter
    (Y : ℕ → F2) (hY_gen : ∀ n, Y n ∈ F2_generating_set)
    (hY : Tendsto (fun n : ℕ => (word_length (X_walk n Y) : ℝ)) atTop atTop)
    (i : ℕ) : Fin 2 × Bool :=
  let N := (walk_prefix_stable Y hY_gen hY (i + 1)).choose
  match (X_walk N Y).toWord[i]? with
  | some ℓ => ℓ
  | none => (0, true)  -- junk; unreachable since length ≥ i + 1

/-- The limit letter agrees with the position `i` of `(X_walk N Y)` for the
chosen `N`. -/
private lemma walk_limit_letter_eq_choose
    (Y : ℕ → F2) (hY_gen : ∀ n, Y n ∈ F2_generating_set)
    (hY : Tendsto (fun n : ℕ => (word_length (X_walk n Y) : ℝ)) atTop atTop)
    (i : ℕ) :
    let N := (walk_prefix_stable Y hY_gen hY (i + 1)).choose
    (X_walk N Y).toWord[i]? = some (walk_limit_letter Y hY_gen hY i) := by
  intro N
  -- The choice satisfies the spec: length ≥ i + 1 at `N` (using `N ≤ N`).
  have hspec := (walk_prefix_stable Y hY_gen hY (i + 1)).choose_spec
  obtain ⟨hlen, _⟩ := hspec N (le_refl _)
  -- So position `i` is in range; `getElem?` returns `some (toWord[i])`.
  have h_eq : (X_walk N Y).toWord[i]? = some ((X_walk N Y).toWord[i]'(by omega)) :=
    List.getElem?_eq_getElem (by omega)
  -- `walk_limit_letter` reads off the same `getElem?` and matches.
  -- Simply `simp [walk_limit_letter, h_eq]` unifies the `let` and the
  -- `match`-on-`some`.
  simp only [walk_limit_letter]
  -- Goal: `(X_walk N Y).toWord[i]? = some (match ... with | some ℓ => ℓ | none => ...)`
  -- where the inner `(X_walk N Y).toWord[i]?` is `⋯.choose`.  Rewrite with `h_eq`.
  rw [h_eq]

/-- The limit letter agrees with the position `i` of `(X_walk n Y)` for any
sufficiently large `n` (in particular, all `n` past the choose-witness). -/
private lemma walk_limit_letter_eq_at_large
    (Y : ℕ → F2) (hY_gen : ∀ n, Y n ∈ F2_generating_set)
    (hY : Tendsto (fun n : ℕ => (word_length (X_walk n Y) : ℝ)) atTop atTop)
    (i : ℕ) :
    ∃ M : ℕ, ∀ n, M ≤ n → (X_walk n Y).toWord[i]? =
        some (walk_limit_letter Y hY_gen hY i) := by
  set N := (walk_prefix_stable Y hY_gen hY (i + 1)).choose
  have hspec := (walk_prefix_stable Y hY_gen hY (i + 1)).choose_spec
  refine ⟨N, ?_⟩
  intro n hn
  have hlen_n := (hspec n hn).1
  have hpref_n := (hspec n hn).2 i (by omega)
  rw [hpref_n]
  exact walk_limit_letter_eq_choose Y hY_gen hY i

/-- **Step 3b — Non-cancellation of consecutive limit letters.** -/
private lemma walk_limit_letter_nonCancellation
    (Y : ℕ → F2) (hY_gen : ∀ n, Y n ∈ F2_generating_set)
    (hY : Tendsto (fun n : ℕ => (word_length (X_walk n Y) : ℝ)) atTop atTop)
    (i : ℕ) :
    NonCancellation (walk_limit_letter Y hY_gen hY i)
                    (walk_limit_letter Y hY_gen hY (i + 1)) := by
  -- Pick a common `n` large enough so that both letters are read off
  -- `(X_walk n Y).toWord` (positions `i` and `i + 1` in range).
  obtain ⟨M₁, hM₁⟩ := walk_limit_letter_eq_at_large Y hY_gen hY i
  obtain ⟨M₂, hM₂⟩ := walk_limit_letter_eq_at_large Y hY_gen hY (i + 1)
  set M := max M₁ M₂
  have hM₁M : M₁ ≤ M := le_max_left _ _
  have hM₂M : M₂ ≤ M := le_max_right _ _
  have hi_eq : (X_walk M Y).toWord[i]? = some (walk_limit_letter Y hY_gen hY i) :=
    hM₁ M hM₁M
  have hi1_eq : (X_walk M Y).toWord[i + 1]? =
      some (walk_limit_letter Y hY_gen hY (i + 1)) :=
    hM₂ M hM₂M
  -- From `getElem? = some _`, extract `<` and the `getElem` equality.
  rw [List.getElem?_eq_some_iff] at hi_eq hi1_eq
  obtain ⟨hi_lt, hi_get⟩ := hi_eq
  obtain ⟨hi1_lt, hi1_get⟩ := hi1_eq
  -- The `IsReduced` chain at position `i` gives the chain condition:
  -- `(toWord[i]).1 = (toWord[i+1]).1 → (toWord[i]).2 = (toWord[i+1]).2`.
  have hred : _root_.FreeGroup.IsReduced (X_walk M Y).toWord :=
    _root_.FreeGroup.isReduced_toWord
  have hchain := hred.getElem i hi1_lt
  -- Translate to NonCancellation.
  unfold NonCancellation
  -- Read off positions: `(X_walk M Y).toWord[i] = walk_limit_letter Y hY_gen hY i`.
  rw [← hi_get, ← hi1_get]
  -- Goal: `((X_walk M Y).toWord[i]).1 ≠ ((X_walk M Y).toWord[i+1]).1
  --   ∨ ((X_walk M Y).toWord[i]).2 = ((X_walk M Y).toWord[i+1]).2`.
  by_cases hf : ((X_walk M Y).toWord[i]'hi_lt).1 = ((X_walk M Y).toWord[i + 1]'hi1_lt).1
  · right; exact hchain hf
  · left; exact hf

/-- **Step 3c — The limit boundary point.** -/
private noncomputable def walk_boundary_limit
    (Y : ℕ → F2) (hY_gen : ∀ n, Y n ∈ F2_generating_set)
    (hY : Tendsto (fun n : ℕ => (word_length (X_walk n Y) : ℝ)) atTop atTop) :
    F2_boundary :=
  ⟨walk_limit_letter Y hY_gen hY, walk_limit_letter_nonCancellation Y hY_gen hY⟩

/-- **Step 4 — Convergence in `F2bar`.** Putting it all together: prefix
stabilisation at depth `p + 1` gives ultrametric distance bound
`dist ≤ exp(-p)`, which sends `dist → 0` as `p → ∞`. -/
private lemma walk_tendsto_F2bar_of_prefix_stable
    (Y : ℕ → F2) (hY_gen : ∀ n, Y n ∈ F2_generating_set)
    (hY : Tendsto (fun n : ℕ => (word_length (X_walk n Y) : ℝ)) atTop atTop) :
    Filter.Tendsto (fun n => ((X_walk n Y : F2) : F2bar))
      Filter.atTop (nhds ((walk_boundary_limit Y hY_gen hY : F2_boundary) : F2bar)) := by
  -- Use the metric structure on `F2bar`.
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- Choose `p` with `exp(-p) < ε`.
  obtain ⟨p, hp⟩ : ∃ p : ℕ, Real.exp (-(p : ℝ)) < ε := by
    -- `Real.exp (-n) → 0`, so eventually `< ε`.
    have h1 : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (nhds 0) := by
      have h2 : Tendsto (fun n : ℕ => -(n : ℝ)) atTop atBot := by
        have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
          tendsto_natCast_atTop_atTop
        exact tendsto_neg_atTop_atBot.comp hcast
      exact Real.tendsto_exp_atBot.comp h2
    have h3 : ∀ᶠ n : ℕ in atTop, Real.exp (-(n : ℝ)) < ε := by
      have := (h1.eventually (gt_mem_nhds hε))
      simpa using this
    rcases h3.exists with ⟨p, hp⟩
    exact ⟨p, hp⟩
  -- For `n ≥ N` (the choose-witness for `p + 1`), prefix at depth `p + 1`
  -- agrees, so distance ≤ exp(-(p + 1)) < exp(-p).
  obtain ⟨M, hM_eq⟩ : ∃ M, ∀ n, M ≤ n →
      ∀ i < p + 1, (X_walk n Y).toWord[i]? =
          some (walk_limit_letter Y hY_gen hY i) := by
    -- Combine the witness from `walk_prefix_stable (p + 1)` with
    -- `walk_limit_letter_eq_at_large`.
    have hps := (walk_prefix_stable Y hY_gen hY (p + 1)).choose_spec
    set N := (walk_prefix_stable Y hY_gen hY (p + 1)).choose
    refine ⟨N, ?_⟩
    intro n hn i hi
    have hpref := (hps n hn).2 i hi
    rw [hpref]
    -- At `N`, position `i` of toWord equals limit letter `i`.
    -- We need an n large enough for limit letter `i`'s `walk_limit_letter_eq_at_large`.
    -- But `walk_limit_letter` at position `i` is defined via N_i :=
    -- choose for `i + 1` — different `N`.  Need to relate them.
    -- Use `walk_limit_letter_eq_at_large` and lift to `N`.
    obtain ⟨M_i, hM_i⟩ := walk_limit_letter_eq_at_large Y hY_gen hY i
    -- `(X_walk N Y).toWord[i]? = some (walk_limit_letter ... i)` — but
    -- only for `n ≥ M_i`.  We have `n ≥ N`; need to push back.
    -- Alternative: `(X_walk N Y).toWord[i]?` is the same as `(X_walk M Y).toWord[i]?`
    -- where `M = max N M_i`, then convert.
    -- Combine prefix-stable at `p + 1` for `M = max N M_i`.
    have hMN : N ≤ max N M_i := le_max_left _ _
    have hMM : M_i ≤ max N M_i := le_max_right _ _
    have hsM : (X_walk (max N M_i) Y).toWord[i]? = some (walk_limit_letter Y hY_gen hY i) :=
      hM_i _ hMM
    have hpref_M := (hps (max N M_i) hMN).2 i hi
    -- `hpref_M : (X_walk (max N M_i) Y).toWord[i]? = (X_walk N Y).toWord[i]?`.
    rw [hpref_M] at hsM
    exact hsM
  -- Eventually for `n ≥ M`, dist ≤ exp(-(p + 1)).
  filter_upwards [eventually_ge_atTop M] with n hn
  -- Goal: `dist (F2_to_F2bar (X_walk n Y)) (F2_boundary_to_F2bar walk_boundary_limit) < ε`.
  show dist ((F2_to_F2bar (X_walk n Y) : F2bar))
       ((F2_boundary_to_F2bar (walk_boundary_limit Y hY_gen hY) : F2bar)) < ε
  -- Use d_prime_le_of_agree at depth p + 1.
  have hagree : ∀ i < p + 1,
      (F2_to_F2bar (X_walk n Y)).val i =
        (F2_boundary_to_F2bar (walk_boundary_limit Y hY_gen hY)).val i := by
    intro i hi
    have h_eq : (X_walk n Y).toWord[i]? =
        some (walk_limit_letter Y hY_gen hY i) := hM_eq n hn i hi
    rw [List.getElem?_eq_some_iff] at h_eq
    obtain ⟨hi_lt, hi_get⟩ := h_eq
    -- LHS: `(F2_to_F2bar (X_walk n Y)).val i = fbgToExtGen ((X_walk n Y).toWord[i]'hi_lt)`
    show (if h : i < (X_walk n Y).toWord.length then
            fbgToExtGen ((X_walk n Y).toWord[i]'h) else ExtGen.one)
        = fbgToExtGen (walk_limit_letter Y hY_gen hY i)
    rw [dif_pos hi_lt]
    rw [hi_get]
  rw [F2bar.dist_def]
  calc F2bar.d_prime (F2_to_F2bar (X_walk n Y))
        (F2_boundary_to_F2bar (walk_boundary_limit Y hY_gen hY))
      ≤ Real.exp (-((p + 1 : ℕ) : ℝ)) := F2bar.d_prime_le_of_agree hagree
    _ < Real.exp (-(p : ℝ)) := by
        apply Real.exp_lt_exp.mpr
        push_cast; linarith
    _ < ε := hp

/-- **Q48 deterministic bridge — Wave 27 dissolution.** A purely
deterministic fact: any trajectory `Y : ℕ → F_2` whose values lie in
`F2_generating_set` and whose reduced word-length tends to infinity
converges in `\overline{F_2}` to a boundary point.

The mathematical content (per Blueprint C):

* once the walk has left the ball of radius `p` for good (which happens
  eventually when `word_length (X_walk n Y) → ∞`), its first `p` letters
  are frozen — single-step prefix invariance, iterated;
* the frozen prefixes define an infinite reduced word, i.e. an element of
  `∂F_2` (`walk_boundary_limit`);
* ultrametric distance bounds in `\overline{F_2}` (`d_prime_le_of_agree`)
  upgrade prefix stabilisation to convergence.

**Wave 24A note.** Without `hY_gen`, the statement is mathematically
*false*: an arbitrary `Y` could take non-generator F_2 values causing
`word_length` growth without proper letter-level reduction. The
hypothesis is recoverable a.s. on `step_measure` via
`walk_step_in_generating_set_ae`. -/
theorem walk_converges_of_dist_tendsto_atTop (Y : ℕ → F2)
    (hY_gen : ∀ n, Y n ∈ F2_generating_set)
    (hY : Tendsto (fun n : ℕ => (word_length (X_walk n Y) : ℝ)) atTop atTop) :
    ∃ X_infty : F2_boundary,
      Filter.Tendsto (fun n => ((X_walk n Y : F2) : F2bar))
        Filter.atTop (nhds ((X_infty : F2_boundary) : F2bar)) :=
  ⟨walk_boundary_limit Y hY_gen hY,
   walk_tendsto_F2bar_of_prefix_stable Y hY_gen hY⟩

/-- **Q48.** For `step_measure`-almost every trajectory `Y`, the random walk
`X_walk n Y` converges in the compactification `\overline{F_2}` to a point
of the boundary `∂F_2`.

The proof has two ingredients:
* `walk_dist_tendsto_atTop` (Q43 corollary, proved in `RandomWalk.lean`):
  `word_length (X_walk n Y) → ∞` almost surely.
* `walk_step_in_generating_set_ae` (RandomWalk.lean): each step lies in
  the 4-element generating set almost surely.
* `walk_converges_of_dist_tendsto_atTop` (deterministic bridge, now a
  theorem — Wave 27): for *any* trajectory satisfying both, a boundary
  limit exists in `F2bar`. -/
theorem walk_converges_to_boundary :
    ∀ᵐ Y ∂step_measure,
      ∃ X_infty : F2_boundary,
        Filter.Tendsto (fun n => ((X_walk n Y : F2) : F2bar))
          Filter.atTop (nhds ((X_infty : F2_boundary) : F2bar)) := by
  filter_upwards [walk_dist_tendsto_atTop, walk_step_in_generating_set_ae]
    with Y hY hY_gen
  exact walk_converges_of_dist_tendsto_atTop Y hY_gen hY

/-- **Q48 auxiliary.** The boundary-limit map `X_∞ : (ℕ → F_2) → ∂F_2`.

The downstream consumers of `X_infinity` (the harmonic measure
`harmonic_measure x = (X_∞ ∘ (x · ·))_*(step_measure)` and the cylinder
events `walkPrefixEvent`) only require:

* `X_infinity` to be a *measurable* function `(ℕ → F_2) → ∂F_2`, and
* the *ae-convergence statement* `walk_converges_to_boundary` to hold
  alongside it (decoupled — the convergence theorem produces a *some*
  boundary limit via `Classical.choose`, not necessarily equal to
  `X_infinity Y`).

**Wave 31 (soundness fix).**  Earlier waves (24A–30) used the constant
map `fun _ => phi_zero` as a placeholder, since downstream consumers
formally only need measurability and decoupled convergence.  But the
exam-grade admission `harmonic_measure_one_cylinder_constant` then
forces *every* cylinder to have measure `δ_{phi_zero}`-mass (i.e. `1`
or `0` depending on the prefix), contradicting the assertion that all
cylinders of fixed depth share the same measure.  The vacuity didn't
break the build (no theorem unfolds `X_infinity` against the cylinder
axiom concretely), but it left a latent inconsistency that blocked
further progress on cylinder-formula dissolution.

This Wave 31 definition restores genuine non-degeneracy: when `Y` is a
trajectory of the random walk on the four generators with diverging
word length, `X_infinity Y` is the *actual* boundary limit produced by
the deterministic bridge `walk_boundary_limit` (from Wave 27).  On the
exceptional set (non-generator values, or bounded word length), we
default to `phi_zero`.  This set has `step_measure`-measure zero (it's
the complement of `walk_dist_tendsto_atTop ∩ walk_step_in_generating_set_ae`),
so the a.e. behaviour is unchanged. -/
noncomputable def X_infinity (Y : ℕ → F2) : F2_boundary := by
  classical
  by_cases h : ∀ n, Y n ∈ F2_generating_set
  · by_cases hLen :
      Tendsto (fun n : ℕ => (word_length (X_walk n Y) : ℝ)) atTop atTop
    · exact walk_boundary_limit Y h hLen
    · exact phi_zero
  · exact phi_zero

/-! ### Wave 35-prep — cumulative-walk boundary limit `X_infinity_starting_at`

The previous Wave 31 definition `X_infinity Y` builds the boundary limit of
the trajectory `n ↦ X_walk n Y` (the random walk *starting at the identity*).
For the harmonic measure `μ_x` based at `x ∈ F_2` we instead need the
boundary limit of the *trajectory starting at `x`*: `n ↦ x · X_walk n Y`.
Multiplying each step `Y n` by `x` componentwise (the previous broken
formulation) does **not** produce that trajectory — it produces the
sequence `n ↦ x · Y n`, almost-surely outside the generator set.

This subsection mirrors the Wave 27 prefix-stabilisation chain
(`walk_step_prefix_preserved` → `walk_prefix_stable` → `walk_limit_letter`
→ `walk_boundary_limit` → `walk_tendsto_F2bar_of_prefix_stable`) for the
shifted trajectory `n ↦ x · X_walk n Y`. The proofs are the same, since
each step is still right-multiplication by a generator: from
`X_walk (n+1) Y = X_walk n Y * Y n` we get
`x · X_walk (n+1) Y = (x · X_walk n Y) * Y n`.

The new helper `X_infinity_starting_at x` agrees with `X_infinity` at
`x = 1` (since `1 · X_walk n Y = X_walk n Y` and `word_length` is
invariant), so all `μ_1`-only theorems carry over unchanged. -/

/-- **Wave 35-prep.** Single-step prefix invariance for the shifted
trajectory `n ↦ x * X_walk n Y`. Identical to `walk_step_prefix_preserved`
but with the prefix taken from `x * X_walk n Y`. -/
private lemma walk_step_prefix_preserved_at
    {Y : ℕ → F2} {n p : ℕ} (x : F2) (hY_gen : Y n ∈ F2_generating_set)
    (hlen : p + 1 ≤ (x * X_walk n Y).toWord.length) (i : ℕ) (hi : i < p) :
    (x * X_walk (n + 1) Y).toWord[i]? = (x * X_walk n Y).toWord[i]? := by
  obtain ⟨ℓ, hℓ⟩ := exists_letter_of_mem_generating_set hY_gen
  -- Step relation: `x * X_walk (n+1) Y = (x * X_walk n Y) * mk [ℓ]`.
  have hstep : x * X_walk (n + 1) Y
      = (x * X_walk n Y) * _root_.FreeGroup.mk [ℓ] := by
    simp [X_walk, hℓ, mul_assoc]
  -- Case split on cancellation at the last letter.
  by_cases hcanc : BusemannLocal.LastCancels (x * X_walk n Y) ℓ
  · -- Cancellation: word becomes `dropLast`.
    have h_word :
        (x * X_walk (n + 1) Y).toWord = (x * X_walk n Y).toWord.dropLast := by
      rw [hstep]; exact BusemannLocal.toWord_mul_mk_letter_cancel _ _ hcanc
    rw [h_word, List.getElem?_dropLast]
    have hi_lt' : i < (x * X_walk n Y).toWord.length - 1 := by omega
    rw [if_pos hi_lt']
  · -- No cancellation: word becomes `++ [ℓ]`.
    have hnoc : BusemannLocal.NoLastCancel (x * X_walk n Y) ℓ := by
      intro ℓ' hmem hbad; exact hcanc ⟨ℓ', hmem, hbad⟩
    have h_word :
        (x * X_walk (n + 1) Y).toWord = (x * X_walk n Y).toWord ++ [ℓ] := by
      rw [hstep]; exact BusemannLocal.toWord_mul_mk_letter_noCancel _ _ hnoc
    rw [h_word]
    have hi_orig : i < (x * X_walk n Y).toWord.length := by omega
    exact List.getElem?_append_left hi_orig

/-- **Wave 35-prep.** Prefix stabilisation for the shifted trajectory.
Identical to `walk_prefix_stable` but for `n ↦ x * X_walk n Y`. -/
private lemma walk_prefix_stable_at
    (x : F2) (Y : ℕ → F2) (hY_gen : ∀ n, Y n ∈ F2_generating_set)
    (hY : Tendsto (fun n : ℕ => (word_length (x * X_walk n Y) : ℝ)) atTop atTop)
    (p : ℕ) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      (p ≤ (x * X_walk n Y).toWord.length) ∧
      (∀ i < p, (x * X_walk n Y).toWord[i]? = (x * X_walk N Y).toWord[i]?) := by
  have hwl : ∀ n, (word_length (x * X_walk n Y) : ℝ)
      = (x * X_walk n Y).toWord.length := by
    intro n; exact_mod_cast word_length_eq_toWord_length _
  have hY' : Tendsto (fun n : ℕ => ((x * X_walk n Y).toWord.length : ℝ))
      atTop atTop := by
    convert hY using 1; funext n; rw [← hwl]
  have hev : ∀ᶠ n in atTop,
      ((p + 1 : ℕ) : ℝ) ≤ ((x * X_walk n Y).toWord.length : ℝ) :=
    hY'.eventually (eventually_ge_atTop ((p + 1 : ℕ) : ℝ))
  rcases hev.exists_forall_of_atTop with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hlen_n : p + 1 ≤ (x * X_walk n Y).toWord.length := by
    have := hN n hn; exact_mod_cast this
  refine ⟨by omega, ?_⟩
  have hlen_step : ∀ k, N ≤ k → p + 1 ≤ (x * X_walk k Y).toWord.length := by
    intro k hk
    have := hN k hk; exact_mod_cast this
  have hgen : ∀ k, k ≥ N →
      ∀ i < p, (x * X_walk k Y).toWord[i]? = (x * X_walk N Y).toWord[i]? := by
    intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = N + m := ⟨k - N, by omega⟩
    clear hk
    induction m with
    | zero => intro i hi; rfl
    | succ m ih =>
        intro i hi
        have hpre : (x * X_walk (N + m + 1) Y).toWord[i]? =
            (x * X_walk (N + m) Y).toWord[i]? := by
          have hN_ge : N + m ≥ N := by omega
          have hlen_Nm : p + 1 ≤ (x * X_walk (N + m) Y).toWord.length :=
            hlen_step (N + m) hN_ge
          exact walk_step_prefix_preserved_at (n := N + m) (p := p) x
            (hY_gen (N + m)) hlen_Nm i hi
        have hih := ih i hi
        show (x * X_walk (N + (m + 1)) Y).toWord[i]?
            = (x * X_walk N Y).toWord[i]?
        have heq : N + (m + 1) = N + m + 1 := by ring
        rw [heq, hpre, hih]
  exact hgen n hn

/-- **Wave 35-prep.** Stable letter at depth `i` for the shifted trajectory. -/
private noncomputable def walk_limit_letter_at
    (x : F2) (Y : ℕ → F2) (hY_gen : ∀ n, Y n ∈ F2_generating_set)
    (hY : Tendsto (fun n : ℕ => (word_length (x * X_walk n Y) : ℝ)) atTop atTop)
    (i : ℕ) : Fin 2 × Bool :=
  let N := (walk_prefix_stable_at x Y hY_gen hY (i + 1)).choose
  match (x * X_walk N Y).toWord[i]? with
  | some ℓ => ℓ
  | none => (0, true)

private lemma walk_limit_letter_at_eq_choose
    (x : F2) (Y : ℕ → F2) (hY_gen : ∀ n, Y n ∈ F2_generating_set)
    (hY : Tendsto (fun n : ℕ => (word_length (x * X_walk n Y) : ℝ)) atTop atTop)
    (i : ℕ) :
    let N := (walk_prefix_stable_at x Y hY_gen hY (i + 1)).choose
    (x * X_walk N Y).toWord[i]? = some (walk_limit_letter_at x Y hY_gen hY i) := by
  intro N
  have hspec := (walk_prefix_stable_at x Y hY_gen hY (i + 1)).choose_spec
  obtain ⟨hlen, _⟩ := hspec N (le_refl _)
  have h_eq : (x * X_walk N Y).toWord[i]?
      = some ((x * X_walk N Y).toWord[i]'(by omega)) :=
    List.getElem?_eq_getElem (by omega)
  simp only [walk_limit_letter_at]
  rw [h_eq]

private lemma walk_limit_letter_at_eq_at_large
    (x : F2) (Y : ℕ → F2) (hY_gen : ∀ n, Y n ∈ F2_generating_set)
    (hY : Tendsto (fun n : ℕ => (word_length (x * X_walk n Y) : ℝ)) atTop atTop)
    (i : ℕ) :
    ∃ M : ℕ, ∀ n, M ≤ n → (x * X_walk n Y).toWord[i]? =
        some (walk_limit_letter_at x Y hY_gen hY i) := by
  set N := (walk_prefix_stable_at x Y hY_gen hY (i + 1)).choose
  have hspec := (walk_prefix_stable_at x Y hY_gen hY (i + 1)).choose_spec
  refine ⟨N, ?_⟩
  intro n hn
  have hlen_n := (hspec n hn).1
  have hpref_n := (hspec n hn).2 i (by omega)
  rw [hpref_n]
  exact walk_limit_letter_at_eq_choose x Y hY_gen hY i

private lemma walk_limit_letter_at_nonCancellation
    (x : F2) (Y : ℕ → F2) (hY_gen : ∀ n, Y n ∈ F2_generating_set)
    (hY : Tendsto (fun n : ℕ => (word_length (x * X_walk n Y) : ℝ)) atTop atTop)
    (i : ℕ) :
    NonCancellation (walk_limit_letter_at x Y hY_gen hY i)
                    (walk_limit_letter_at x Y hY_gen hY (i + 1)) := by
  obtain ⟨M₁, hM₁⟩ := walk_limit_letter_at_eq_at_large x Y hY_gen hY i
  obtain ⟨M₂, hM₂⟩ := walk_limit_letter_at_eq_at_large x Y hY_gen hY (i + 1)
  set M := max M₁ M₂
  have hM₁M : M₁ ≤ M := le_max_left _ _
  have hM₂M : M₂ ≤ M := le_max_right _ _
  have hi_eq : (x * X_walk M Y).toWord[i]?
      = some (walk_limit_letter_at x Y hY_gen hY i) := hM₁ M hM₁M
  have hi1_eq : (x * X_walk M Y).toWord[i + 1]?
      = some (walk_limit_letter_at x Y hY_gen hY (i + 1)) := hM₂ M hM₂M
  rw [List.getElem?_eq_some_iff] at hi_eq hi1_eq
  obtain ⟨hi_lt, hi_get⟩ := hi_eq
  obtain ⟨hi1_lt, hi1_get⟩ := hi1_eq
  have hred : _root_.FreeGroup.IsReduced (x * X_walk M Y).toWord :=
    _root_.FreeGroup.isReduced_toWord
  have hchain := hred.getElem i hi1_lt
  unfold NonCancellation
  rw [← hi_get, ← hi1_get]
  by_cases hf : ((x * X_walk M Y).toWord[i]'hi_lt).1
      = ((x * X_walk M Y).toWord[i + 1]'hi1_lt).1
  · right; exact hchain hf
  · left; exact hf

/-- **Wave 35-prep.** Boundary limit of the shifted trajectory
`n ↦ x · X_walk n Y`. -/
private noncomputable def walk_boundary_limit_at
    (x : F2) (Y : ℕ → F2) (hY_gen : ∀ n, Y n ∈ F2_generating_set)
    (hY : Tendsto (fun n : ℕ => (word_length (x * X_walk n Y) : ℝ)) atTop atTop) :
    F2_boundary :=
  ⟨walk_limit_letter_at x Y hY_gen hY,
   walk_limit_letter_at_nonCancellation x Y hY_gen hY⟩

/-- **Wave 35-prep.** Convergence in `F2bar` of the shifted trajectory. -/
private lemma walk_tendsto_F2bar_of_prefix_stable_at
    (x : F2) (Y : ℕ → F2) (hY_gen : ∀ n, Y n ∈ F2_generating_set)
    (hY : Tendsto (fun n : ℕ => (word_length (x * X_walk n Y) : ℝ)) atTop atTop) :
    Filter.Tendsto (fun n => ((x * X_walk n Y : F2) : F2bar))
      Filter.atTop
      (nhds ((walk_boundary_limit_at x Y hY_gen hY : F2_boundary) : F2bar)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨p, hp⟩ : ∃ p : ℕ, Real.exp (-(p : ℝ)) < ε := by
    have h1 : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (nhds 0) := by
      have h2 : Tendsto (fun n : ℕ => -(n : ℝ)) atTop atBot := by
        have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
          tendsto_natCast_atTop_atTop
        exact tendsto_neg_atTop_atBot.comp hcast
      exact Real.tendsto_exp_atBot.comp h2
    have h3 : ∀ᶠ n : ℕ in atTop, Real.exp (-(n : ℝ)) < ε := by
      have := (h1.eventually (gt_mem_nhds hε))
      simpa using this
    rcases h3.exists with ⟨p, hp⟩
    exact ⟨p, hp⟩
  obtain ⟨M, hM_eq⟩ : ∃ M, ∀ n, M ≤ n →
      ∀ i < p + 1, (x * X_walk n Y).toWord[i]? =
          some (walk_limit_letter_at x Y hY_gen hY i) := by
    have hps := (walk_prefix_stable_at x Y hY_gen hY (p + 1)).choose_spec
    set N := (walk_prefix_stable_at x Y hY_gen hY (p + 1)).choose
    refine ⟨N, ?_⟩
    intro n hn i hi
    have hpref := (hps n hn).2 i hi
    rw [hpref]
    obtain ⟨M_i, hM_i⟩ := walk_limit_letter_at_eq_at_large x Y hY_gen hY i
    have hMN : N ≤ max N M_i := le_max_left _ _
    have hMM : M_i ≤ max N M_i := le_max_right _ _
    have hsM : (x * X_walk (max N M_i) Y).toWord[i]?
        = some (walk_limit_letter_at x Y hY_gen hY i) := hM_i _ hMM
    have hpref_M := (hps (max N M_i) hMN).2 i hi
    rw [hpref_M] at hsM
    exact hsM
  filter_upwards [eventually_ge_atTop M] with n hn
  show dist ((F2_to_F2bar (x * X_walk n Y) : F2bar))
       ((F2_boundary_to_F2bar (walk_boundary_limit_at x Y hY_gen hY) : F2bar)) < ε
  have hagree : ∀ i < p + 1,
      (F2_to_F2bar (x * X_walk n Y)).val i =
        (F2_boundary_to_F2bar (walk_boundary_limit_at x Y hY_gen hY)).val i := by
    intro i hi
    have h_eq : (x * X_walk n Y).toWord[i]?
        = some (walk_limit_letter_at x Y hY_gen hY i) := hM_eq n hn i hi
    rw [List.getElem?_eq_some_iff] at h_eq
    obtain ⟨hi_lt, hi_get⟩ := h_eq
    show (if h : i < (x * X_walk n Y).toWord.length then
            fbgToExtGen ((x * X_walk n Y).toWord[i]'h) else ExtGen.one)
        = fbgToExtGen (walk_limit_letter_at x Y hY_gen hY i)
    rw [dif_pos hi_lt, hi_get]
  rw [F2bar.dist_def]
  calc F2bar.d_prime (F2_to_F2bar (x * X_walk n Y))
        (F2_boundary_to_F2bar (walk_boundary_limit_at x Y hY_gen hY))
      ≤ Real.exp (-((p + 1 : ℕ) : ℝ)) := F2bar.d_prime_le_of_agree hagree
    _ < Real.exp (-(p : ℝ)) := by
        apply Real.exp_lt_exp.mpr
        push_cast; linarith
    _ < ε := hp

/-- **Wave 35-prep.** Boundary-limit map for the trajectory starting at `x`:
`X_∞^{(x)} : (ℕ → F_2) → ∂F_2`. Maps the step sequence `Y` to the boundary
limit of the trajectory `n ↦ x · X_walk n Y`, with `phi_zero` on the
exceptional set. -/
noncomputable def X_infinity_starting_at (x : F2) (Y : ℕ → F2) : F2_boundary := by
  classical
  by_cases h : ∀ n, Y n ∈ F2_generating_set
  · by_cases hLen :
      Tendsto (fun n : ℕ => (word_length (x * X_walk n Y) : ℝ)) atTop atTop
    · exact walk_boundary_limit_at x Y h hLen
    · exact phi_zero
  · exact phi_zero

/-! ### Wave 32 — `X_infinity_measurable` dissolution

The previous `axiom X_infinity_measurable` is now a fully proved theorem.

**Mathematical content.**  We prove measurability of `X_infinity` by
exhibiting it as a pointwise limit (in the metrizable space
`F2_boundary`) of the patched sequence

```
  g n Y :=
    if Y satisfies the convergence hypotheses (`Y ∈ S`) then
      F2bar_to_F2_boundary applied to the F2bar-image of (X_walk n Y),
      after a "snap to phi_zero" projection that always lands in F2_boundary
    else
      phi_zero
```

The construction has two layers:

1. *F2bar bridge.* We borelize `F2bar` and view `F2_boundary` as a
   measurable subspace of `F2bar` via the closed embedding
   `F2_boundary_to_F2bar`.  Since `range_F2_boundary_to_F2bar` is
   `F2bar.F2boundary` (a closed set in F2bar by `F2boundary_isClosed`),
   the embedding is a measurable embedding.

2. *Patched approximating sequence.*  Define
   `g_n Y : F2bar` by the piecewise formula
   `if Y ∈ S then F2_to_F2bar (X_walk n Y) else F2_boundary_to_F2bar phi_zero`.
   Each `g_n` is measurable (S is measurable, X_walk is measurable,
   F2_to_F2bar is measurable into a top σ-algebra branch, the constant
   alternative is measurable).  Pointwise as `n → ∞`:
   - on `S`, by `walk_tendsto_F2bar_of_prefix_stable`,
     `g_n Y → F2_boundary_to_F2bar (walk_boundary_limit Y _ _)
            = F2_boundary_to_F2bar (X_infinity Y)`;
   - on `Sᶜ`, `g_n Y` is constant equal to
     `F2_boundary_to_F2bar phi_zero = F2_boundary_to_F2bar (X_infinity Y)`.

   Hence `g_n → F2_boundary_to_F2bar ∘ X_infinity` everywhere; by
   `measurable_of_tendsto_metrizable`, this limit is measurable.

3. *Measurable-embedding inversion.* From measurability of
   `F2_boundary_to_F2bar ∘ X_infinity` and the
   measurable-embedding nature of `F2_boundary_to_F2bar`, conclude
   `Measurable X_infinity` via `MeasurableEmbedding.measurable_comp_iff`.

This dissolves the previous `axiom X_infinity_measurable`. -/

/-- **Top σ-algebra on `ExtGen`** — the alphabet is finite, every set
is measurable. -/
instance : MeasurableSpace ExtGen := ⊤

instance : DiscreteMeasurableSpace ExtGen := ⟨fun _ => trivial⟩

/-- **Borel σ-algebra on `F2bar`** — induced from the metric topology.
This `borel`-instance, combined with `F2bar.borelSpace` immediately
below, lets us treat `F2bar` as a Borel measurable space and apply
Mathlib's `measurable_of_tendsto_metrizable`. -/
instance F2bar.measurableSpace : MeasurableSpace F2bar := borel F2bar

instance F2bar.borelSpace : BorelSpace F2bar := ⟨rfl⟩

/-- The boundary embedding `F2_boundary → F2bar` is a measurable
embedding: it is a closed topological embedding (its image is the
closed set `F2bar.F2boundary`), hence the source σ-algebra is the
preimage σ-algebra of the target. -/
private lemma F2_boundary_to_F2bar_measurableEmbedding :
    MeasurableEmbedding F2_boundary_to_F2bar := by
  -- Closed range gives `Topology.IsClosedEmbedding`, which yields
  -- `MeasurableEmbedding` via `Topology.IsClosedEmbedding.measurableEmbedding`.
  have h_closed : IsClosed (Set.range F2_boundary_to_F2bar) := by
    rw [range_F2_boundary_to_F2bar]
    exact F2bar.F2boundary_isClosed
  exact (Topology.IsClosedEmbedding.mk
    F2_boundary_to_F2bar_isEmbedding h_closed).measurableEmbedding

/-- The F2bar-coercion of the random walk is measurable for each `n`:
`X_walk n` is measurable into the discrete `F2`, and `F2_to_F2bar` is
measurable from a discrete-σ-algebra source. -/
private lemma F2_to_F2bar_X_walk_measurable (n : ℕ) :
    Measurable (fun Y : ℕ → F2 => (F2_to_F2bar (X_walk n Y) : F2bar)) := by
  -- F2_to_F2bar is measurable since its source `F2` carries the top
  -- σ-algebra (`MeasurableSpace F2 := ⊤`).
  have h_F2_to : Measurable (F2_to_F2bar : F2 → F2bar) := by
    -- Source has top σ-algebra ⇒ every map is measurable.
    intro s _
    exact MeasurableSpace.measurableSet_top
  exact h_F2_to.comp (X_walk_measurable n)

/-- The "convergence-hypothesis set" `S`: trajectories `Y` satisfying
both prerequisites for boundary convergence (all values in the
generating set, and word-length divergence). -/
private def convergenceSet : Set (ℕ → F2) :=
  {Y : ℕ → F2 | (∀ n, Y n ∈ F2_generating_set) ∧
    Tendsto (fun n : ℕ => (word_length (X_walk n Y) : ℝ)) atTop atTop}

/-- The convergence-hypothesis set is measurable: it is a countable
Boolean combination of measurable predicates in the coordinates `Y n`
and the values `(X_walk n Y).toWord.length`. -/
private lemma convergenceSet_measurable : MeasurableSet convergenceSet := by
  -- The set `convergenceSet` is the intersection of two measurable sets.
  have hA :
      MeasurableSet {Y : ℕ → F2 | ∀ n, Y n ∈ F2_generating_set} := by
    have heq : {Y : ℕ → F2 | ∀ n, Y n ∈ F2_generating_set}
        = ⋂ n : ℕ, {Y : ℕ → F2 | Y n ∈ F2_generating_set} := by
      ext Y; simp
    rw [heq]
    refine MeasurableSet.iInter (fun n => ?_)
    have hpre : {Y : ℕ → F2 | Y n ∈ F2_generating_set}
        = (fun Y : ℕ → F2 => Y n) ⁻¹' F2_generating_set := rfl
    rw [hpre]
    exact (measurable_pi_apply n) MeasurableSet.of_discrete
  have hB :
      MeasurableSet {Y : ℕ → F2 |
        Tendsto (fun n : ℕ => (word_length (X_walk n Y) : ℝ)) atTop atTop} := by
    -- Tendsto atTop atTop unfolds to `∀ M, ∀ᶠ n, M ≤ word_length (...)`.
    have heq : {Y : ℕ → F2 |
          Tendsto (fun n : ℕ => (word_length (X_walk n Y) : ℝ)) atTop atTop}
        = ⋂ M : ℕ, ⋃ N : ℕ, ⋂ (n : ℕ) (_ : N ≤ n),
            {Y : ℕ → F2 | (M : ℝ) ≤ (word_length (X_walk n Y) : ℝ)} := by
      ext Y
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
      constructor
      · intro hY M
        have h1 : Tendsto (fun n : ℕ => (word_length (X_walk n Y) : ℝ))
            atTop atTop := hY
        have h2 := h1.eventually_ge_atTop ((M : ℝ))
        rcases h2.exists_forall_of_atTop with ⟨N, hN⟩
        exact ⟨N, fun n hn => hN n hn⟩
      · intro hY
        rw [Filter.tendsto_atTop_atTop]
        intro M
        obtain ⟨M', hM'⟩ : ∃ M' : ℕ, M ≤ (M' : ℝ) := by
          rcases exists_nat_ge M with ⟨M', hM'⟩
          exact ⟨M', hM'⟩
        rcases hY M' with ⟨N, hN⟩
        refine ⟨N, ?_⟩
        intro n hn
        have := hN n hn
        linarith
    rw [heq]
    refine MeasurableSet.iInter (fun M => ?_)
    refine MeasurableSet.iUnion (fun N => ?_)
    refine MeasurableSet.iInter (fun n => ?_)
    refine MeasurableSet.iInter (fun _ => ?_)
    have h_meas_int : Measurable
        (fun Y : ℕ → F2 => (word_length (X_walk n Y) : ℝ)) := by
      have h1 : Measurable (fun Y : ℕ → F2 => word_length (X_walk n Y)) := by
        have : Measurable (word_length : F2 → ℕ) := fun s _ =>
          MeasurableSpace.measurableSet_top
        exact this.comp (X_walk_measurable n)
      -- The composition `Nat.cast : ℕ → ℝ ∘ word_length ∘ X_walk` is measurable.
      have h_nat_to_real : Measurable (Nat.cast : ℕ → ℝ) := measurable_from_nat
      exact h_nat_to_real.comp h1
    exact h_meas_int (measurableSet_Ici)
  exact hA.inter hB

/-- The patched approximating sequence in `F2bar`:
`g_n Y := if Y ∈ S then F2_to_F2bar (X_walk n Y) else F2_boundary_to_F2bar phi_zero`. -/
private noncomputable def XInftyApprox (n : ℕ) (Y : ℕ → F2) : F2bar := by
  classical
  exact if Y ∈ convergenceSet then
    F2_to_F2bar (X_walk n Y)
  else
    F2_boundary_to_F2bar phi_zero

/-- Unfolding lemma for `XInftyApprox` on the convergence set. -/
private lemma XInftyApprox_eq_of_mem (n : ℕ) {Y : ℕ → F2}
    (hY : Y ∈ convergenceSet) :
    XInftyApprox n Y = F2_to_F2bar (X_walk n Y) := by
  classical
  simp only [XInftyApprox, hY, if_true]

/-- Unfolding lemma for `XInftyApprox` off the convergence set. -/
private lemma XInftyApprox_eq_of_notMem (n : ℕ) {Y : ℕ → F2}
    (hY : Y ∉ convergenceSet) :
    XInftyApprox n Y = F2_boundary_to_F2bar phi_zero := by
  classical
  simp only [XInftyApprox, hY, if_false]

/-- Measurability of the patched approximating sequence. -/
private lemma XInftyApprox_measurable (n : ℕ) :
    Measurable (XInftyApprox n) := by
  classical
  -- Goal: `Measurable (fun Y => if Y ∈ convergenceSet then ...)`.
  -- Use `Measurable.ite` after unfolding.
  unfold XInftyApprox
  exact Measurable.ite convergenceSet_measurable
    (F2_to_F2bar_X_walk_measurable n) measurable_const

/-- Pointwise convergence of the patched sequence to
`F2_boundary_to_F2bar ∘ X_infinity`. -/
private lemma XInftyApprox_tendsto (Y : ℕ → F2) :
    Tendsto (fun n => XInftyApprox n Y) atTop
      (𝓝 (F2_boundary_to_F2bar (X_infinity Y))) := by
  by_cases hY : Y ∈ convergenceSet
  · -- On the convergence set, X_infinity Y = walk_boundary_limit Y _ _,
    -- and the F2bar-images of the walk converge there.
    obtain ⟨h_gen, h_len⟩ := hY
    have h_unfold : X_infinity Y = walk_boundary_limit Y h_gen h_len := by
      simp only [X_infinity]
      rw [dif_pos h_gen, dif_pos h_len]
    have h_approx_unfold : ∀ n, XInftyApprox n Y = F2_to_F2bar (X_walk n Y) :=
      fun n => XInftyApprox_eq_of_mem n ⟨h_gen, h_len⟩
    have h_walk := walk_tendsto_F2bar_of_prefix_stable Y h_gen h_len
    rw [h_unfold]
    convert h_walk using 1
    funext n; exact h_approx_unfold n
  · -- Off the convergence set, both sides are constant `phi_zero`.
    have h_unfold : X_infinity Y = phi_zero := by
      simp only [X_infinity]
      by_cases h1 : ∀ n, Y n ∈ F2_generating_set
      · rw [dif_pos h1]
        by_cases h2 : Tendsto (fun n : ℕ =>
            (word_length (X_walk n Y) : ℝ)) atTop atTop
        · exact absurd ⟨h1, h2⟩ hY
        · rw [dif_neg h2]
      · rw [dif_neg h1]
    have h_approx_unfold : ∀ n, XInftyApprox n Y = F2_boundary_to_F2bar phi_zero :=
      fun n => XInftyApprox_eq_of_notMem n hY
    rw [h_unfold]
    have h_const : (fun n => XInftyApprox n Y) =
        (fun _ => F2_boundary_to_F2bar phi_zero) := funext h_approx_unfold
    rw [h_const]
    exact tendsto_const_nhds

/-- **Q48 auxiliary measurability — Wave 32 dissolution.**  The
boundary-limit map `X_∞ : (ℕ → F_2) → ∂F_2` is measurable.

The proof passes through the F2bar bridge: `F2_boundary_to_F2bar ∘ X_infinity`
is the pointwise limit of the measurable patched sequence
`XInftyApprox n` (which equals `F2_to_F2bar (X_walk n Y)` on the
convergence set and `F2_boundary_to_F2bar phi_zero` off it).  Since
`F2bar` is a metrizable Borel space, `measurable_of_tendsto_metrizable`
gives measurability of `F2_boundary_to_F2bar ∘ X_infinity`.  The
embedding `F2_boundary_to_F2bar` is a measurable embedding (its image
is the closed `F2bar.F2boundary`), so by
`MeasurableEmbedding.measurable_comp_iff`, `X_infinity` itself is
measurable. -/
theorem X_infinity_measurable : Measurable X_infinity := by
  -- Step 1: measurability of `F2_boundary_to_F2bar ∘ X_infinity`.
  have h_lim_meas :
      Measurable (fun Y : ℕ → F2 => F2_boundary_to_F2bar (X_infinity Y)) := by
    apply measurable_of_tendsto_metrizable XInftyApprox_measurable
    rw [tendsto_pi_nhds]
    exact XInftyApprox_tendsto
  -- Step 2: invert through the measurable embedding.
  exact F2_boundary_to_F2bar_measurableEmbedding.measurable_comp_iff.mp h_lim_meas

/-- **Q48 (measurability).** The boundary-limit map is `step_measure`-a.e.
measurable — immediate from the (axiomatic) fact that `X_∞` is everywhere
measurable. -/
theorem X_infinity_ae_definable :
    AEMeasurable X_infinity step_measure :=
  X_infinity_measurable.aemeasurable

/-! ### Wave 35-prep — measurability of `X_infinity_starting_at`

The shifted boundary-limit map is measurable in `Y` for every fixed `x`,
by the same `XInftyApprox`-style argument as `X_infinity` but with the
trajectory `n ↦ x · X_walk n Y` in place of `n ↦ X_walk n Y`. -/

/-- The shifted convergence set: trajectories `Y` for which the
trajectory `n ↦ x * X_walk n Y` admits a boundary limit. -/
private def convergenceSet_at (x : F2) : Set (ℕ → F2) :=
  {Y : ℕ → F2 | (∀ n, Y n ∈ F2_generating_set) ∧
    Tendsto (fun n : ℕ => (word_length (x * X_walk n Y) : ℝ)) atTop atTop}

private lemma convergenceSet_at_measurable (x : F2) :
    MeasurableSet (convergenceSet_at x) := by
  have hA :
      MeasurableSet {Y : ℕ → F2 | ∀ n, Y n ∈ F2_generating_set} := by
    have heq : {Y : ℕ → F2 | ∀ n, Y n ∈ F2_generating_set}
        = ⋂ n : ℕ, {Y : ℕ → F2 | Y n ∈ F2_generating_set} := by
      ext Y; simp
    rw [heq]
    refine MeasurableSet.iInter (fun n => ?_)
    have hpre : {Y : ℕ → F2 | Y n ∈ F2_generating_set}
        = (fun Y : ℕ → F2 => Y n) ⁻¹' F2_generating_set := rfl
    rw [hpre]
    exact (measurable_pi_apply n) MeasurableSet.of_discrete
  have hB :
      MeasurableSet {Y : ℕ → F2 |
        Tendsto (fun n : ℕ => (word_length (x * X_walk n Y) : ℝ)) atTop atTop} := by
    have heq : {Y : ℕ → F2 |
          Tendsto (fun n : ℕ => (word_length (x * X_walk n Y) : ℝ)) atTop atTop}
        = ⋂ M : ℕ, ⋃ N : ℕ, ⋂ (n : ℕ) (_ : N ≤ n),
            {Y : ℕ → F2 | (M : ℝ) ≤ (word_length (x * X_walk n Y) : ℝ)} := by
      ext Y
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
      constructor
      · intro hY M
        have h1 : Tendsto (fun n : ℕ => (word_length (x * X_walk n Y) : ℝ))
            atTop atTop := hY
        have h2 := h1.eventually_ge_atTop ((M : ℝ))
        rcases h2.exists_forall_of_atTop with ⟨N, hN⟩
        exact ⟨N, fun n hn => hN n hn⟩
      · intro hY
        rw [Filter.tendsto_atTop_atTop]
        intro M
        obtain ⟨M', hM'⟩ : ∃ M' : ℕ, M ≤ (M' : ℝ) := by
          rcases exists_nat_ge M with ⟨M', hM'⟩
          exact ⟨M', hM'⟩
        rcases hY M' with ⟨N, hN⟩
        refine ⟨N, ?_⟩
        intro n hn
        have := hN n hn
        linarith
    rw [heq]
    refine MeasurableSet.iInter (fun M => ?_)
    refine MeasurableSet.iUnion (fun N => ?_)
    refine MeasurableSet.iInter (fun n => ?_)
    refine MeasurableSet.iInter (fun _ => ?_)
    have h_meas_int : Measurable
        (fun Y : ℕ → F2 => (word_length (x * X_walk n Y) : ℝ)) := by
      have h1 : Measurable (fun Y : ℕ → F2 => word_length (x * X_walk n Y)) := by
        have h_wl : Measurable (word_length : F2 → ℕ) := fun s _ =>
          MeasurableSpace.measurableSet_top
        have h_mul : Measurable (fun y : F2 => x * y) := fun s _ =>
          MeasurableSpace.measurableSet_top
        exact h_wl.comp (h_mul.comp (X_walk_measurable n))
      have h_nat_to_real : Measurable (Nat.cast : ℕ → ℝ) := measurable_from_nat
      exact h_nat_to_real.comp h1
    exact h_meas_int (measurableSet_Ici)
  exact hA.inter hB

/-- The shifted patched approximating sequence in `F2bar`. -/
private noncomputable def XInftyApprox_at (x : F2) (n : ℕ) (Y : ℕ → F2) : F2bar := by
  classical
  exact if Y ∈ convergenceSet_at x then
    F2_to_F2bar (x * X_walk n Y)
  else
    F2_boundary_to_F2bar phi_zero

private lemma XInftyApprox_at_eq_of_mem (x : F2) (n : ℕ) {Y : ℕ → F2}
    (hY : Y ∈ convergenceSet_at x) :
    XInftyApprox_at x n Y = F2_to_F2bar (x * X_walk n Y) := by
  classical
  simp only [XInftyApprox_at, hY, if_true]

private lemma XInftyApprox_at_eq_of_notMem (x : F2) (n : ℕ) {Y : ℕ → F2}
    (hY : Y ∉ convergenceSet_at x) :
    XInftyApprox_at x n Y = F2_boundary_to_F2bar phi_zero := by
  classical
  simp only [XInftyApprox_at, hY, if_false]

private lemma F2_to_F2bar_X_walk_at_measurable (x : F2) (n : ℕ) :
    Measurable (fun Y : ℕ → F2 => (F2_to_F2bar (x * X_walk n Y) : F2bar)) := by
  have h_F2_to : Measurable (F2_to_F2bar : F2 → F2bar) := by
    intro s _; exact MeasurableSpace.measurableSet_top
  have h_mul : Measurable (fun y : F2 => x * y) := fun s _ =>
    MeasurableSpace.measurableSet_top
  exact h_F2_to.comp (h_mul.comp (X_walk_measurable n))

private lemma XInftyApprox_at_measurable (x : F2) (n : ℕ) :
    Measurable (XInftyApprox_at x n) := by
  classical
  unfold XInftyApprox_at
  exact Measurable.ite (convergenceSet_at_measurable x)
    (F2_to_F2bar_X_walk_at_measurable x n) measurable_const

private lemma XInftyApprox_at_tendsto (x : F2) (Y : ℕ → F2) :
    Tendsto (fun n => XInftyApprox_at x n Y) atTop
      (𝓝 (F2_boundary_to_F2bar (X_infinity_starting_at x Y))) := by
  by_cases hY : Y ∈ convergenceSet_at x
  · obtain ⟨h_gen, h_len⟩ := hY
    have h_unfold :
        X_infinity_starting_at x Y = walk_boundary_limit_at x Y h_gen h_len := by
      simp only [X_infinity_starting_at]
      rw [dif_pos h_gen, dif_pos h_len]
    have h_approx_unfold : ∀ n,
        XInftyApprox_at x n Y = F2_to_F2bar (x * X_walk n Y) :=
      fun n => XInftyApprox_at_eq_of_mem x n ⟨h_gen, h_len⟩
    have h_walk := walk_tendsto_F2bar_of_prefix_stable_at x Y h_gen h_len
    rw [h_unfold]
    convert h_walk using 1
    funext n; exact h_approx_unfold n
  · have h_unfold : X_infinity_starting_at x Y = phi_zero := by
      simp only [X_infinity_starting_at]
      by_cases h1 : ∀ n, Y n ∈ F2_generating_set
      · rw [dif_pos h1]
        by_cases h2 : Tendsto (fun n : ℕ =>
            (word_length (x * X_walk n Y) : ℝ)) atTop atTop
        · exact absurd ⟨h1, h2⟩ hY
        · rw [dif_neg h2]
      · rw [dif_neg h1]
    have h_approx_unfold : ∀ n,
        XInftyApprox_at x n Y = F2_boundary_to_F2bar phi_zero :=
      fun n => XInftyApprox_at_eq_of_notMem x n hY
    rw [h_unfold]
    have h_const : (fun n => XInftyApprox_at x n Y) =
        (fun _ => F2_boundary_to_F2bar phi_zero) := funext h_approx_unfold
    rw [h_const]
    exact tendsto_const_nhds

/-- **Wave 35-prep.** The shifted boundary-limit map
`X_∞^{(x)} : (ℕ → F_2) → ∂F_2` is measurable. -/
theorem X_infinity_starting_at_measurable (x : F2) :
    Measurable (X_infinity_starting_at x) := by
  have h_lim_meas :
      Measurable (fun Y : ℕ → F2 =>
        F2_boundary_to_F2bar (X_infinity_starting_at x Y)) := by
    apply measurable_of_tendsto_metrizable (XInftyApprox_at_measurable x)
    rw [tendsto_pi_nhds]
    exact XInftyApprox_at_tendsto x
  exact F2_boundary_to_F2bar_measurableEmbedding.measurable_comp_iff.mp h_lim_meas

/-- **Wave 35-prep agreement.** At `x = 1`, the shifted boundary-limit map
agrees with the classical one (since `1 · X_walk n Y = X_walk n Y` and
the convergence hypotheses are identical). -/
theorem X_infinity_starting_at_one (Y : ℕ → F2) :
    X_infinity_starting_at 1 Y = X_infinity Y := by
  classical
  by_cases h : ∀ n, Y n ∈ F2_generating_set
  · by_cases hLen :
        Tendsto (fun n : ℕ => (word_length (X_walk n Y) : ℝ)) atTop atTop
    · have hLen' :
          Tendsto (fun n : ℕ => (word_length (1 * X_walk n Y) : ℝ)) atTop atTop := by
        simpa [one_mul] using hLen
      have hL :
          X_infinity_starting_at 1 Y = walk_boundary_limit_at 1 Y h hLen' := by
        unfold X_infinity_starting_at
        rw [dif_pos h, dif_pos hLen']
      have hR :
          X_infinity Y = walk_boundary_limit Y h hLen := by
        unfold X_infinity
        rw [dif_pos h, dif_pos hLen]
      rw [hL, hR]
      -- Show `walk_boundary_limit_at 1 Y h hLen' = walk_boundary_limit Y h hLen`
      -- by extensionality on the underlying letter sequence.
      apply Subtype.ext
      funext i
      -- The two limit-letter functions agree at each `i` because
      -- `(1 * X_walk M Y).toWord[i]? = (X_walk M Y).toWord[i]?`.
      obtain ⟨M₁, hM₁⟩ := walk_limit_letter_at_eq_at_large 1 Y h hLen' i
      obtain ⟨M₂, hM₂⟩ := walk_limit_letter_eq_at_large Y h hLen i
      set M := max M₁ M₂
      have hM₁M : M₁ ≤ M := le_max_left _ _
      have hM₂M : M₂ ≤ M := le_max_right _ _
      have hLeft := hM₁ M hM₁M
      have hRight := hM₂ M hM₂M
      have hOne : (1 * X_walk M Y).toWord = (X_walk M Y).toWord := by
        rw [one_mul]
      rw [hOne] at hLeft
      change (walk_boundary_limit_at 1 Y h hLen').val i
          = (walk_boundary_limit Y h hLen).val i
      simp only [walk_boundary_limit_at, walk_boundary_limit]
      have := hLeft.symm.trans hRight
      exact Option.some.inj this
    · have hLen' :
          ¬ Tendsto (fun n : ℕ => (word_length (1 * X_walk n Y) : ℝ)) atTop atTop := by
        simp only [one_mul]
        exact hLen
      unfold X_infinity_starting_at X_infinity
      rw [dif_pos h, dif_neg hLen', dif_pos h, dif_neg hLen]
  · unfold X_infinity_starting_at X_infinity
    rw [dif_neg h, dif_neg h]

/-! ### Q49 — Harmonic measure and Poisson integral representation -/

/-- **Q49 definition.** The *harmonic measure* `μ_x` based at `x ∈ F_2`:
the pushforward by `X_∞^{(x)} := Y ↦ X_infinity_starting_at x Y` of the
step measure. That is, the law of the *exit point of the random walk
started at `x`*: the trajectory `n ↦ x · X_walk n Y`, with limit in
`∂F_2`.

**Wave 35-prep (soundness fix).** Earlier waves (24A–34) used
`Y ↦ X_∞(fun n => x · Y n)` — applying `x` componentwise to each step.
That is mathematically wrong: `x · Y n` (a single generator times `x`)
has length `|x| ± 1`, never `1`, so the input fails the
`F2_generating_set` membership test inside `X_infinity` and the
fallback `phi_zero` is taken almost-surely, making
`harmonic_measure x = δ_{phi_zero}` for `x ≠ 1`. Under the corrected
definition, `harmonic_measure x` is the pushforward of the trajectory
*starting at `x`* (cumulative-walk semantics), which is the intended
mathematical object. At `x = 1`, the new definition agrees pointwise
with the old one (`X_infinity_starting_at_one`). -/
def harmonic_measure (x : F2) : MeasureTheory.Measure F2_boundary :=
  MeasureTheory.Measure.map (X_infinity_starting_at x) step_measure

/-- The translated walk map `Y ↦ (n ↦ x · Y n)` is measurable.  The
product σ-algebra on `ℕ → F_2` is induced by the discrete σ-algebra on
`F_2` (`MeasurableSpace F2 := ⊤` from `RandomWalk.lean`), so any map
into a discrete target is measurable.

Since `MeasurableSpace F2 := ⊤` every function into `F_2` (seen as a
measurable space) is measurable, and the product σ-algebra on `ℕ → F_2`
makes all coordinate projections measurable; combining gives the result
by `measurable_pi_lambda`. -/
lemma measurable_left_translate (x : F2) :
    Measurable (fun (Y : ℕ → F2) (n : ℕ) => x * Y n) := by
  refine measurable_pi_lambda _ (fun n => ?_)
  -- The codomain `F_2` carries the discrete σ-algebra (`MeasurableSpace F2 := ⊤`
  -- from `RandomWalk.lean`), so multiplication by `x` is measurable.  Compose
  -- with the `n`-th projection of the product σ-algebra on `ℕ → F_2`.
  exact (show Measurable (fun y : F2 => x * y) from fun s _ =>
    (MeasurableSpace.measurableSet_top : MeasurableSet _)).comp
    (measurable_pi_apply n)

/-- **Structural lemma.** The harmonic measure is a probability measure:
it is the pushforward of a probability measure by a measurable map. -/
instance harmonic_measure_isProbabilityMeasure (x : F2) :
    IsProbabilityMeasure (harmonic_measure x) := by
  unfold harmonic_measure
  exact MeasureTheory.Measure.isProbabilityMeasure_map
    (X_infinity_starting_at_measurable x).aemeasurable

/-- **Coordinate measurability** (Wave 24B).  Each coordinate-evaluation
predicate `{ψ : F2_boundary | ψ.val n = x}` is open (hence measurable) in
the induced topology / Borel σ-algebra on `F2_boundary`. -/
theorem F2_boundary_coord_measurable (n : ℕ) (x : (Fin 2) × Bool) :
    MeasurableSet {ψ : F2_boundary | ψ.val n = x} :=
  (F2_boundary_coord_eq_isOpen n x).measurableSet

/-- A cylinder set `I(φ, p) ⊆ ∂F_2`: the set of boundary points whose
first `p` letters agree with those of `φ`. Concrete definition (no
longer an axiom). -/
def cylinder (φ : F2_boundary) (p : ℕ) : Set F2_boundary :=
  {ψ : F2_boundary | ∀ i : ℕ, i < p → ψ.val i = φ.val i}

/-- Membership in a cylinder is a measurable condition. Proof: the
cylinder is a finite intersection of coordinate-preimages, each
measurable by `F2_boundary_coord_measurable`. -/
theorem cylinder_measurable (φ : F2_boundary) (p : ℕ) :
    MeasurableSet (cylinder φ p) := by
  have : cylinder φ p =
      ⋂ i ∈ (Finset.range p : Set ℕ), {ψ : F2_boundary | ψ.val i = φ.val i} := by
    ext ψ
    simp [cylinder]
  rw [this]
  exact MeasurableSet.biInter (Finset.range p).countable_toSet
    (fun i _ => F2_boundary_coord_measurable i (φ.val i))

@[simp] lemma mem_cylinder (φ ψ : F2_boundary) (p : ℕ) :
    ψ ∈ cylinder φ p ↔ ∀ i < p, ψ.val i = φ.val i := by
  simp [cylinder]

@[simp] lemma cylinder_zero (φ : F2_boundary) : cylinder φ 0 = Set.univ := by
  ext ψ; simp [cylinder]

lemma self_mem_cylinder (φ : F2_boundary) (p : ℕ) :
    φ ∈ cylinder φ p := by
  simp [cylinder]

/-! #### Wave 35.4 — Geometric inclusion: the cylinder event forces a hit at `u`

For starting vertex `x : F2`, boundary `φ : F2_boundary`, depth `q ≥ |x|`, and
the **meeting vertex** `u := φ.valPrefix c` with `c := common_prefix_length x φ`:
on the convergence set, any walk whose boundary limit lies in `cylinder φ q`
must visit `u` at some finite time, i.e. `T_u_at x u Y < ⊤`.

Mathematically: in the Cayley tree, the geodesic from `x` to `ψ ∈ I(φ, q)`
passes through `u` (the meeting point of `x`'s and `ψ`'s rays-to-infinity).
The walk trajectory, traced as a path in the tree, must therefore visit `u`.
Quantitatively, when `c < |x|` we have `x.toWord[c] ≠ φ.val c` while the limit's
letter at position `c` IS `φ.val c`; the walk's letter at position `c` can only
change via cancellation through that position, forcing the walk's reduced word
to drop to length exactly `c` at some moment, at which point the walk equals
`u`. When `c = |x|` we have `x = u` directly. -/

/-- **Wave 35.4 helper.** From the cylinder constraint and `i < q`, the walk's
limit-letter at position `i` equals `φ.val i`. -/
private lemma walk_limit_letter_at_eq_phi_of_cylinder
    (x : F2) (φ : F2_boundary) (q : ℕ) {Y : ℕ → F2}
    (hY_gen : ∀ n, Y n ∈ F2_generating_set)
    (hY_len : Tendsto (fun n : ℕ => (word_length (x * X_walk n Y) : ℝ)) atTop atTop)
    (hY_cyl : X_infinity_starting_at x Y ∈ cylinder φ q)
    (i : ℕ) (hi : i < q) :
    walk_limit_letter_at x Y hY_gen hY_len i = φ.val i := by
  have hunfold :
      X_infinity_starting_at x Y = walk_boundary_limit_at x Y hY_gen hY_len := by
    simp only [X_infinity_starting_at]
    rw [dif_pos hY_gen, dif_pos hY_len]
  rw [hunfold, mem_cylinder] at hY_cyl
  -- `walk_boundary_limit_at`'s `val` is `walk_limit_letter_at`.
  have h := hY_cyl i hi
  change walk_limit_letter_at x Y hY_gen hY_len i = φ.val i at h
  exact h

/-- **Wave 35.4 helper.** The `c`-prefix of `x.toWord` is exactly `u.toWord`,
where `u := φ.valPrefix c` and `c := common_prefix_length x φ`. More precisely:
for `i < c`, `x.toWord[i]? = some (u.toWord[i]) = some (φ.val i)`. -/
private lemma x_toWord_getElem_eq_u_letter
    (x : F2) (φ : F2_boundary) (i : ℕ)
    (hi : i < common_prefix_length x φ) :
    x.toWord[i]? = some (φ.val i) := by
  have h_pm : PrefixMatches x φ (common_prefix_length x φ) :=
    BusemannLocal.prefixMatches_common_prefix_length x φ
  exact h_pm.2 i hi

/-- **Wave 35.4 helper.** If a reduced word `w` of length `c` agrees with
`φ` on the first `c` letters, then `w = (φ.valPrefix c).toWord`. Used to
identify the walk vertex with `u` when its length drops to `c`. -/
private lemma toWord_eq_valPrefix_of_match
    (w : F2) (φ : F2_boundary) (c : ℕ)
    (hlen : w.toWord.length = c)
    (hmatch : ∀ i < c, w.toWord[i]? = some (φ.val i)) :
    w = F2_boundary.valPrefix φ c := by
  apply _root_.FreeGroup.toWord_injective
  -- Show `w.toWord = (valPrefix φ c).toWord`.
  apply List.ext_getElem?
  intro i
  by_cases hi : i < c
  · rw [hmatch i hi]
    exact (F2_boundary.toWord_valPrefix_getElem? φ c i hi).symm
  · push_neg at hi
    have h1 : w.toWord[i]? = none := by
      apply List.getElem?_eq_none
      omega
    have h2 : ((F2_boundary.valPrefix φ c).toWord)[i]? = none := by
      apply List.getElem?_eq_none
      rw [F2_boundary.length_toWord_valPrefix]
      exact hi
    rw [h1, h2]

/-- **Wave 35.4 helper — invariant preservation.** If `w := x · X_walk n Y` has
its `c`-prefix matching `u`'s letters (`= φ`'s first `c` letters) and its
length is `≥ c+1`, then after the next step `w' := x · X_walk (n+1) Y`:
either `w' = u` (when length drops from `c+1` to `c`) or `w'` again has its
`c`-prefix matching and length `≥ c`. -/
private lemma walk_step_invariant
    {x : F2} {Y : ℕ → F2} {n c : ℕ} (φ : F2_boundary)
    (hY_gen : Y n ∈ F2_generating_set)
    (hlen : c + 1 ≤ (x * X_walk n Y).toWord.length)
    (hmatch : ∀ i < c, (x * X_walk n Y).toWord[i]? = some (φ.val i)) :
    (x * X_walk (n + 1) Y = F2_boundary.valPrefix φ c) ∨
      ((c ≤ (x * X_walk (n + 1) Y).toWord.length) ∧
       (∀ i < c, (x * X_walk (n + 1) Y).toWord[i]? = some (φ.val i))) := by
  obtain ⟨ℓ, hℓ⟩ := exists_letter_of_mem_generating_set hY_gen
  have hstep : x * X_walk (n + 1) Y
      = (x * X_walk n Y) * _root_.FreeGroup.mk [ℓ] := by
    simp [X_walk, hℓ, mul_assoc]
  by_cases hcanc : BusemannLocal.LastCancels (x * X_walk n Y) ℓ
  · -- Cancellation: word becomes `dropLast`, length decreases by 1.
    have h_word :
        (x * X_walk (n + 1) Y).toWord = (x * X_walk n Y).toWord.dropLast := by
      rw [hstep]; exact BusemannLocal.toWord_mul_mk_letter_cancel _ _ hcanc
    have h_len :
        (x * X_walk (n + 1) Y).toWord.length = (x * X_walk n Y).toWord.length - 1 := by
      rw [h_word, List.length_dropLast]
    by_cases hc1 : (x * X_walk n Y).toWord.length = c + 1
    · -- length goes from c+1 down to c; identify walk_{n+1} with `u`.
      left
      apply toWord_eq_valPrefix_of_match _ φ c
      · rw [h_len, hc1]; rfl
      · intro i hi
        rw [h_word, List.getElem?_dropLast]
        have hi_lt : i < (x * X_walk n Y).toWord.length - 1 := by omega
        rw [if_pos hi_lt]
        exact hmatch i hi
    · -- length ≥ c+2, so length drops to ≥ c+1 ≥ c, and prefix preserved.
      right
      refine ⟨by omega, ?_⟩
      intro i hi
      rw [h_word, List.getElem?_dropLast]
      have hi_lt : i < (x * X_walk n Y).toWord.length - 1 := by omega
      rw [if_pos hi_lt]
      exact hmatch i hi
  · -- No cancellation: length increases by 1, prefix preserved.
    right
    have hnoc : BusemannLocal.NoLastCancel (x * X_walk n Y) ℓ := by
      intro ℓ' hmem hbad; exact hcanc ⟨ℓ', hmem, hbad⟩
    have h_word :
        (x * X_walk (n + 1) Y).toWord = (x * X_walk n Y).toWord ++ [ℓ] := by
      rw [hstep]; exact BusemannLocal.toWord_mul_mk_letter_noCancel _ _ hnoc
    refine ⟨?_, ?_⟩
    · rw [h_word, List.length_append]; simp; omega
    · intro i hi
      rw [h_word]
      have hi_orig : i < (x * X_walk n Y).toWord.length := by omega
      rw [List.getElem?_append_left hi_orig]
      exact hmatch i hi

/-- **Wave 35.4 main.** The geometric inclusion: on the convergence set, any
trajectory whose boundary limit lies in `cylinder φ q` (for `q ≥ |x|`) visits
the meeting vertex `u := φ.valPrefix c` at some finite time, where
`c := common_prefix_length x φ`. -/
theorem cylinder_event_subset_T_u_at_lt_top
    (x : F2) (φ : F2_boundary) (q : ℕ) (hq : x.toWord.length ≤ q) :
    {Y : ℕ → F2 | (∀ n, Y n ∈ F2_generating_set) ∧
        Tendsto (fun n : ℕ => (word_length (x * X_walk n Y) : ℝ)) atTop atTop ∧
        X_infinity_starting_at x Y ∈ cylinder φ q}
      ⊆ {Y : ℕ → F2 | T_u_at x
            (F2_boundary.valPrefix φ (common_prefix_length x φ)) Y < ⊤} := by
  intro Y hY
  obtain ⟨hY_gen, hY_len, hY_cyl⟩ := hY
  set c : ℕ := common_prefix_length x φ with hc_def
  set u : F2 := F2_boundary.valPrefix φ c with hu_def
  have hc_le_x : c ≤ x.toWord.length := BusemannLocal.common_prefix_length_le x φ
  have hc_le_q : c ≤ q := le_trans hc_le_x hq
  rw [Set.mem_setOf_eq, T_u_at_lt_top_iff]
  -- Case 1: c = |x|. Then x = u.
  rcases eq_or_lt_of_le hc_le_x with hceq | hclt
  · refine ⟨0, ?_⟩
    rw [X_walk_zero, mul_one]
    -- x.toWord has length c with first c letters = φ's; same for u; hence x = u.
    apply toWord_eq_valPrefix_of_match _ φ c
    · exact hceq.symm
    · intro i hi
      exact x_toWord_getElem_eq_u_letter x φ i hi
  · -- Case 2: c < |x|. Use the letter-at-c transition argument.
    -- (Step b) Eventually walk_n.toWord[c]? = some (φ.val c).
    have hc_lt_q : c < q := lt_of_lt_of_le hclt hq
    -- Stabilisation: walk_prefix_stable_at at depth c+1.
    have hps := (walk_prefix_stable_at x Y hY_gen hY_len (c + 1)).choose_spec
    set N₀ := (walk_prefix_stable_at x Y hY_gen hY_len (c + 1)).choose with hN₀_def
    have hlen_N₀ : c + 1 ≤ (x * X_walk N₀ Y).toWord.length := (hps N₀ le_rfl).1
    -- At time N₀, walk's letter at position c equals φ.val c.
    have hlet_N₀ : (x * X_walk N₀ Y).toWord[c]? = some (φ.val c) := by
      have hpref_N₀ := (hps N₀ le_rfl).2 c (by omega)
      -- walk_N₀.toWord[c]? = walk_N₀.toWord[c]? (trivial), and equal to limit-letter.
      obtain ⟨M, hM⟩ := walk_limit_letter_at_eq_at_large x Y hY_gen hY_len c
      have hMN : N₀ ≤ max N₀ M := le_max_left _ _
      have hMM : M ≤ max N₀ M := le_max_right _ _
      have h1 : (x * X_walk (max N₀ M) Y).toWord[c]?
          = some (walk_limit_letter_at x Y hY_gen hY_len c) := hM _ hMM
      have hpref_max := (hps (max N₀ M) hMN).2 c (by omega)
      rw [hpref_max] at h1
      have h_eq_phi : walk_limit_letter_at x Y hY_gen hY_len c = φ.val c :=
        walk_limit_letter_at_eq_phi_of_cylinder x φ q hY_gen hY_len hY_cyl c hc_lt_q
      rw [h_eq_phi] at h1
      exact h1
    -- (Step c) The "letter at c" function: define f(n) := walk_n.toWord[c]?.
    -- f(0) = some (x.toWord[c]) ≠ some (φ.val c) (since c < |x|).
    -- f(N₀) = some (φ.val c).
    -- Letter-change can only happen via length dipping to c.
    -- So ∃ smallest m ≤ N₀ with walk_m.toWord.length ≤ c.
    -- At smallest m (≥ 1), walk_{m-1}.length > c, walk_m.length = c, and walk_m = u.
    have h_initial_letter : (x * X_walk 0 Y).toWord[c]? ≠ some (φ.val c) := by
      rw [X_walk_zero, mul_one]
      have h_ne : x.toWord[c]? ≠ some (φ.val c) := by
        have := BusemannLocal.toWord_at_m_ne_phi_of_lt x φ hclt
        rwa [← hc_def] at this
      exact h_ne
    -- There exists n ≤ N₀ where walk_n.toWord.length ≤ c.
    -- Suppose not: then walk_n.length > c for all n ≤ N₀, so the letter at
    -- position c is preserved by every step (cancellation only drops length
    -- to ≥ c+1, hence dropLast preserves position c; append also preserves).
    -- Then walk_N₀.toWord[c]? = walk_0.toWord[c]? = some (x.toWord[c]) ≠
    -- some (φ.val c), contradicting `hlet_N₀`.
    have h_exists_short : ∃ n ≤ N₀, (x * X_walk n Y).toWord.length ≤ c := by
      by_contra h_no
      push_neg at h_no
      have h_invariant : ∀ n, n ≤ N₀ →
          (x * X_walk n Y).toWord[c]? = (x * X_walk 0 Y).toWord[c]? := by
        intro n hn
        induction n with
        | zero => rfl
        | succ k ih =>
          have hk_le : k ≤ N₀ := by omega
          have hk_succ_len : (x * X_walk (k + 1) Y).toWord.length > c := h_no _ hn
          have hk_len : (x * X_walk k Y).toWord.length > c := h_no _ hk_le
          have h_eq_step : (x * X_walk (k + 1) Y).toWord[c]?
              = (x * X_walk k Y).toWord[c]? := by
            obtain ⟨ℓ, hℓ⟩ := exists_letter_of_mem_generating_set (hY_gen k)
            have hstep : x * X_walk (k + 1) Y
                = (x * X_walk k Y) * _root_.FreeGroup.mk [ℓ] := by
              simp [X_walk, hℓ, mul_assoc]
            by_cases hcanc : BusemannLocal.LastCancels (x * X_walk k Y) ℓ
            · have h_word :
                  (x * X_walk (k + 1) Y).toWord = (x * X_walk k Y).toWord.dropLast := by
                rw [hstep]
                exact BusemannLocal.toWord_mul_mk_letter_cancel _ _ hcanc
              have h_len :
                  (x * X_walk (k + 1) Y).toWord.length
                    = (x * X_walk k Y).toWord.length - 1 := by
                rw [h_word, List.length_dropLast]
              -- walk_{k+1}.length > c ⇒ walk_k.length ≥ c+2.
              have hk_ge_c2 : (x * X_walk k Y).toWord.length ≥ c + 2 := by omega
              rw [h_word, List.getElem?_dropLast]
              have hc_lt : c < (x * X_walk k Y).toWord.length - 1 := by omega
              rw [if_pos hc_lt]
            · have hnoc : BusemannLocal.NoLastCancel (x * X_walk k Y) ℓ := by
                intro ℓ' hmem hbad; exact hcanc ⟨ℓ', hmem, hbad⟩
              have h_word :
                  (x * X_walk (k + 1) Y).toWord = (x * X_walk k Y).toWord ++ [ℓ] := by
                rw [hstep]
                exact BusemannLocal.toWord_mul_mk_letter_noCancel _ _ hnoc
              rw [h_word]
              have hc_orig : c < (x * X_walk k Y).toWord.length := by omega
              exact List.getElem?_append_left hc_orig
          rw [h_eq_step]
          exact ih hk_le
      have h_at_N₀ := h_invariant N₀ le_rfl
      rw [hlet_N₀] at h_at_N₀
      exact h_initial_letter h_at_N₀.symm
    -- Use Nat.find on the predicate `(x * X_walk n Y).toWord.length ≤ c`.
    have h_exists_n : ∃ n, (x * X_walk n Y).toWord.length ≤ c := by
      obtain ⟨n, _, h⟩ := h_exists_short
      exact ⟨n, h⟩
    classical
    set m := Nat.find h_exists_n with hm_def
    have hm_spec : (x * X_walk m Y).toWord.length ≤ c := Nat.find_spec h_exists_n
    have hm_min : ∀ k < m, ¬ (x * X_walk k Y).toWord.length ≤ c :=
      fun k hk => Nat.find_min h_exists_n hk
    -- m > 0 (since walk_0.length = |x| > c).
    have hm_pos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with hm_zero | hm_pos
      · exfalso
        rw [hm_zero] at hm_spec
        rw [X_walk_zero, mul_one] at hm_spec
        exact absurd hclt (not_lt.mpr hm_spec)
      · exact hm_pos
    -- walk_{m-1}.length > c, so ≥ c+1.
    have hm_pred_len : c + 1 ≤ (x * X_walk (m - 1) Y).toWord.length := by
      have := hm_min (m - 1) (by omega)
      push_neg at this
      omega
    -- walk_m = walk_{(m-1)+1}.
    have hm_succ : m = (m - 1) + 1 := by omega
    -- The c-prefix of walk_{m-1}.toWord matches u's letters: needed for the
    -- step-invariant. Build this by induction on indices ≤ m-1.
    have h_prefix_match_pred : ∀ i < c,
        (x * X_walk (m - 1) Y).toWord[i]? = some (φ.val i) := by
      -- For all n ≤ m-1, walk_n.length ≥ c+1 (by minimality of m).
      -- Establish prefix-match at all such n by induction from n = 0.
      have h_match_all : ∀ n ≤ m - 1, ∀ i < c,
          (x * X_walk n Y).toWord[i]? = some (φ.val i) := by
        intro n hn
        induction n with
        | zero =>
            intro i hi
            rw [X_walk_zero, mul_one]
            exact x_toWord_getElem_eq_u_letter x φ i (hc_def ▸ hi)
        | succ k ih =>
            have hk_le : k ≤ m - 1 := by omega
            have hk_lt_m : k < m := by omega
            have hk_succ_lt_m : k + 1 < m := by omega
            have hk_succ_len : (x * X_walk (k + 1) Y).toWord.length > c := by
              have := hm_min (k + 1) hk_succ_lt_m
              push_neg at this; omega
            have hk_len : (x * X_walk k Y).toWord.length > c := by
              have := hm_min k hk_lt_m
              push_neg at this; omega
            have hk_len' : c + 1 ≤ (x * X_walk k Y).toWord.length := by omega
            intro i hi
            -- Use walk_step_prefix_preserved_at at p = c.
            have hpres := walk_step_prefix_preserved_at (n := k) (p := c) x
              (hY_gen k) hk_len' i hi
            rw [hpres]
            exact ih hk_le i hi
      exact h_match_all (m - 1) le_rfl
    -- Apply the step invariant from m-1 to m: either walk_m = u, or invariant continues.
    have h_inv := walk_step_invariant (x := x) (Y := Y) (n := m - 1) (c := c) φ
        (hY_gen (m - 1)) hm_pred_len h_prefix_match_pred
    rw [← hm_succ] at h_inv
    rcases h_inv with h_at_u | ⟨h_len, _⟩
    · exact ⟨m, h_at_u⟩
    · -- length ≥ c at walk_m AND length ≤ c, so length = c. Combined with prefix match,
      -- walk_m = u.
      have hlen_eq : (x * X_walk m Y).toWord.length = c := le_antisymm hm_spec h_len
      refine ⟨m, ?_⟩
      apply toWord_eq_valPrefix_of_match _ φ c hlen_eq
      -- Prefix match at walk_m: from m-1 to m via walk_step_prefix_preserved_at at p = c.
      intro i hi
      have hpres := walk_step_prefix_preserved_at (n := m - 1) (p := c) x
          (hY_gen (m - 1)) hm_pred_len i hi
      rw [← hm_succ] at hpres
      rw [hpres]
      exact h_prefix_match_pred i hi

/-! #### Wave 35.5 D1 — Generalised geometric inclusion (origin starting vertex)

For starting vertex `v` with `v.toWord.length ≤ d ≤ q`, on the convergence set,
any walk from `v` whose boundary limit lies in `cylinder φ q` must visit
`φ.valPrefix d` at some finite time. The argument: the walk's length grows
from `|v| ≤ d` to ∞, and the boundary limit's first `d` letters match `φ.val`
(since `d ≤ q`). Pick the largest time `m ≤ N₀` (where `N₀` is a stabilisation
time at depth `d+1`) with `length(m) ≤ d`. Then `length(m) = d` (else `length`
fails to cross the threshold by step `m+1`), and the walk's `d`-prefix matches
`φ` (preserved backwards from `N₀`).

This deliverable specialises with `v = 1` and `d = c(x, φ)` to dissolve
`harmonic_measure_factor_at_meeting_vertex_one`. -/

/-- **Wave 35.5 D1 — generalised geometric inclusion.** For `|v| ≤ d ≤ q`,
the walk from `v` whose boundary limit lies in `cylinder φ q` visits
`φ.valPrefix d` at some finite time. -/
theorem cylinder_event_subset_T_u_at_lt_top_general
    (v : F2) (φ : F2_boundary) (q d : ℕ)
    (hd_le_q : d ≤ q) (hv_le_d : v.toWord.length ≤ d) :
    {Y : ℕ → F2 | (∀ n, Y n ∈ F2_generating_set) ∧
        Tendsto (fun n : ℕ => (word_length (v * X_walk n Y) : ℝ)) atTop atTop ∧
        X_infinity_starting_at v Y ∈ cylinder φ q}
      ⊆ {Y : ℕ → F2 | T_u_at v (F2_boundary.valPrefix φ d) Y < ⊤} := by
  intro Y hY
  obtain ⟨hY_gen, hY_len, hY_cyl⟩ := hY
  rw [Set.mem_setOf_eq, T_u_at_lt_top_iff]
  -- Stabilisation: pick N₀ with length(n) ≥ d+1 and prefix-stable for n ≥ N₀.
  have hps := (walk_prefix_stable_at v Y hY_gen hY_len (d + 1)).choose_spec
  set N₀ := (walk_prefix_stable_at v Y hY_gen hY_len (d + 1)).choose with hN₀_def
  have hlen_N₀ : d + 1 ≤ (v * X_walk N₀ Y).toWord.length := (hps N₀ le_rfl).1
  -- At time N₀, walk's letter at every position i < d equals φ.val i.
  have hlet_N₀ : ∀ i < d, (v * X_walk N₀ Y).toWord[i]? = some (φ.val i) := by
    intro i hi
    -- Stabilisation gives: walk_n.toWord[i]? = walk_{N₀}.toWord[i]? for n ≥ N₀.
    -- And walk_n.toWord[i]? eventually equals some(walk_limit_letter i) = some(φ.val i).
    obtain ⟨M, hM⟩ := walk_limit_letter_at_eq_at_large v Y hY_gen hY_len i
    have hM_max : N₀ ≤ max N₀ M := le_max_left _ _
    have hMM : M ≤ max N₀ M := le_max_right _ _
    have h_max : (v * X_walk (max N₀ M) Y).toWord[i]?
        = some (walk_limit_letter_at v Y hY_gen hY_len i) := hM _ hMM
    -- Stabilisation: walk_{max}[i]? = walk_{N₀}[i]?.
    have hpref_max := (hps (max N₀ M) hM_max).2 i (by omega)
    rw [hpref_max] at h_max
    -- Limit-letter equals φ.val i.
    have h_eq_phi : walk_limit_letter_at v Y hY_gen hY_len i = φ.val i :=
      walk_limit_letter_at_eq_phi_of_cylinder v φ q hY_gen hY_len hY_cyl i
        (lt_of_lt_of_le hi hd_le_q)
    rw [h_eq_phi] at h_max
    exact h_max
  -- Initial state: walk_0 = v has length ≤ d.
  have hinit_len : (v * X_walk 0 Y).toWord.length ≤ d := by
    rw [X_walk_zero, mul_one]; exact hv_le_d
  -- Pick m = the largest time ≤ N₀ with length ≤ d. Use Nat.findGreatest.
  classical
  -- The predicate "n ≤ N₀ AND length(n) ≤ d" — we use Nat.findGreatest on
  -- `fun n => (v * X_walk n Y).toWord.length ≤ d` over the bound `N₀`.
  set P : ℕ → Prop := fun n => (v * X_walk n Y).toWord.length ≤ d with hP_def
  have hP_dec : DecidablePred P := fun n => Nat.decLe _ _
  set m := Nat.findGreatest P N₀ with hm_def
  -- m is in the candidate set (P holds at 0, 0 ≤ N₀).
  have hP_zero : P 0 := hinit_len
  have hm_le : m ≤ N₀ := Nat.findGreatest_le N₀
  have hm_spec : P m := Nat.findGreatest_spec (Nat.zero_le N₀) hP_zero
  have hm_max : ∀ k, m < k → k ≤ N₀ → ¬ P k := by
    intro k hmk hk_le
    exact Nat.findGreatest_is_greatest hmk hk_le
  -- m < N₀: since P(N₀) fails (length(N₀) ≥ d+1 > d).
  have hP_N₀_fail : ¬ P N₀ := by
    show ¬ (v * X_walk N₀ Y).toWord.length ≤ d
    omega
  have hm_lt_N₀ : m < N₀ := by
    rcases lt_or_eq_of_le hm_le with hlt | heq
    · exact hlt
    · exfalso; rw [heq] at hm_spec; exact hP_N₀_fail hm_spec
  -- length(m+1) > d (since P(m+1) fails by maximality of m).
  have hP_msucc_fail : ¬ P (m + 1) :=
    hm_max (m + 1) (Nat.lt_succ_self m) hm_lt_N₀
  have hsucc_len : d + 1 ≤ (v * X_walk (m + 1) Y).toWord.length := by
    have : ¬ (v * X_walk (m + 1) Y).toWord.length ≤ d := hP_msucc_fail
    omega
  -- length(m) ≤ d AND length(m+1) ≥ d+1. The step changes length by ±1.
  -- So length(m+1) ∈ {length(m)+1, length(m)-1}. Since length(m+1) ≥ d+1 ≥ length(m)+1,
  -- we must have length(m+1) = length(m)+1 (no cancellation), giving length(m) ≥ d.
  -- Combined with length(m) ≤ d, length(m) = d.
  have hm_len_eq : (v * X_walk m Y).toWord.length = d := by
    -- Use the step-change-by-one bound. Examine the step from m to m+1.
    obtain ⟨ℓ, hℓ⟩ := exists_letter_of_mem_generating_set (hY_gen m)
    have hstep : v * X_walk (m + 1) Y
        = (v * X_walk m Y) * _root_.FreeGroup.mk [ℓ] := by
      simp [X_walk, hℓ, mul_assoc]
    by_cases hcanc : BusemannLocal.LastCancels (v * X_walk m Y) ℓ
    · -- Cancellation: length(m+1) = length(m) - 1.
      have h_word :
          (v * X_walk (m + 1) Y).toWord = (v * X_walk m Y).toWord.dropLast := by
        rw [hstep]; exact BusemannLocal.toWord_mul_mk_letter_cancel _ _ hcanc
      have h_len :
          (v * X_walk (m + 1) Y).toWord.length
            = (v * X_walk m Y).toWord.length - 1 := by
        rw [h_word, List.length_dropLast]
      -- length(m+1) ≤ length(m) ≤ d, contradicting length(m+1) ≥ d+1.
      omega
    · -- No cancellation: length(m+1) = length(m) + 1.
      have hnoc : BusemannLocal.NoLastCancel (v * X_walk m Y) ℓ := by
        intro ℓ' hmem hbad; exact hcanc ⟨ℓ', hmem, hbad⟩
      have h_word :
          (v * X_walk (m + 1) Y).toWord = (v * X_walk m Y).toWord ++ [ℓ] := by
        rw [hstep]; exact BusemannLocal.toWord_mul_mk_letter_noCancel _ _ hnoc
      have h_len :
          (v * X_walk (m + 1) Y).toWord.length
            = (v * X_walk m Y).toWord.length + 1 := by
        rw [h_word, List.length_append]; simp
      -- length(m+1) ≥ d+1 ⇒ length(m) ≥ d. Combined with hm_spec : length(m) ≤ d.
      have h1 : (v * X_walk m Y).toWord.length ≥ d := by omega
      omega
  -- Prefix at depth d at time m matches φ. Strategy: prefix matches at time N₀
  -- (by hlet_N₀), preserved backwards through times m+1, ..., N₀ (all have length ≥ d+1).
  -- Then the m → m+1 step preserves the prefix (no cancellation, since length increased).
  -- (a) Prefix at depth d at time m+1 matches φ. Use backward induction from N₀ to m+1.
  have h_prefix_msucc : ∀ i < d, (v * X_walk (m + 1) Y).toWord[i]? = some (φ.val i) := by
    intro i hi
    -- For all n with m+1 ≤ n ≤ N₀, walk_n.toWord[i]? = some (φ.val i). Induct on N₀-n.
    have h_by_diff : ∀ k : ℕ, k ≤ N₀ - (m + 1) →
        (v * X_walk (N₀ - k) Y).toWord[i]? = some (φ.val i) := by
      intro k hk
      induction k with
      | zero =>
          simp only [Nat.sub_zero]
          exact hlet_N₀ i hi
      | succ j ih =>
          have hj_le : j ≤ N₀ - (m + 1) := by omega
          have ih_val := ih hj_le
          -- Goal: walk_{N₀ - (j+1)}.toWord[i]? = some (φ.val i).
          -- Use walk_step_prefix_preserved_at at n = N₀ - (j+1), p = d.
          have hn_le : N₀ - (j + 1) < N₀ := by omega
          have hn_ge_msucc : m + 1 ≤ N₀ - (j + 1) := by omega
          -- length(N₀ - (j+1)) ≥ d+1 (by minimality of m).
          have hn_len : d + 1 ≤ (v * X_walk (N₀ - (j + 1)) Y).toWord.length := by
            -- ¬ P(N₀ - (j+1)) by maximality (m < N₀ - (j+1) ≤ N₀).
            have h_not_P : ¬ P (N₀ - (j + 1)) := by
              apply hm_max
              · omega
              · omega
            show d + 1 ≤ _
            have : ¬ (v * X_walk (N₀ - (j + 1)) Y).toWord.length ≤ d := h_not_P
            omega
          have hpres := walk_step_prefix_preserved_at (n := N₀ - (j + 1)) (p := d) v
              (hY_gen (N₀ - (j + 1))) hn_len i hi
          have h_succ_eq : N₀ - (j + 1) + 1 = N₀ - j := by omega
          rw [h_succ_eq] at hpres
          -- hpres : walk_{N₀ - j}.toWord[i]? = walk_{N₀ - (j+1)}.toWord[i]?
          -- ih_val : walk_{N₀ - j}.toWord[i]? = some (φ.val i)
          -- Goal:   walk_{N₀ - (j+1)}.toWord[i]? = some (φ.val i)
          rw [← hpres]
          exact ih_val
    have h_at_msucc := h_by_diff (N₀ - (m + 1)) le_rfl
    have h_eq : N₀ - (N₀ - (m + 1)) = m + 1 := by omega
    rw [h_eq] at h_at_msucc
    exact h_at_msucc
  -- (b) Prefix at depth d at time m matches φ. Step from m to m+1 (no cancellation
  -- since length(m+1) > length(m)).
  have h_prefix_m : ∀ i < d, (v * X_walk m Y).toWord[i]? = some (φ.val i) := by
    intro i hi
    -- length(m) = d, length(m+1) ≥ d+1, so the step appended a letter.
    obtain ⟨ℓ, hℓ⟩ := exists_letter_of_mem_generating_set (hY_gen m)
    have hstep : v * X_walk (m + 1) Y
        = (v * X_walk m Y) * _root_.FreeGroup.mk [ℓ] := by
      simp [X_walk, hℓ, mul_assoc]
    by_cases hcanc : BusemannLocal.LastCancels (v * X_walk m Y) ℓ
    · -- Cancellation case: would give length(m+1) < length(m), contradicting hsucc_len.
      exfalso
      have h_word :
          (v * X_walk (m + 1) Y).toWord = (v * X_walk m Y).toWord.dropLast := by
        rw [hstep]; exact BusemannLocal.toWord_mul_mk_letter_cancel _ _ hcanc
      have h_len :
          (v * X_walk (m + 1) Y).toWord.length
            = (v * X_walk m Y).toWord.length - 1 := by
        rw [h_word, List.length_dropLast]
      omega
    · have hnoc : BusemannLocal.NoLastCancel (v * X_walk m Y) ℓ := by
        intro ℓ' hmem hbad; exact hcanc ⟨ℓ', hmem, hbad⟩
      have h_word :
          (v * X_walk (m + 1) Y).toWord = (v * X_walk m Y).toWord ++ [ℓ] := by
        rw [hstep]; exact BusemannLocal.toWord_mul_mk_letter_noCancel _ _ hnoc
      have hi_orig : i < (v * X_walk m Y).toWord.length := by rw [hm_len_eq]; exact hi
      have h_step_eq : (v * X_walk (m + 1) Y).toWord[i]? = (v * X_walk m Y).toWord[i]? := by
        rw [h_word]
        exact List.getElem?_append_left hi_orig
      have h_at_msucc := h_prefix_msucc i hi
      rw [h_step_eq] at h_at_msucc
      exact h_at_msucc
  -- Conclude: walk_m has length d AND prefix matches φ on [0, d), so walk_m = φ.valPrefix d.
  refine ⟨m, ?_⟩
  exact toWord_eq_valPrefix_of_match _ φ d hm_len_eq h_prefix_m

/-! #### Structural decomposition of the cylinder formula

The cylinder formula `μ_1(I(φ, p)) = 1/(4 · 3^{p-1})` is decomposed into
three named leaf lemmas.  The first reduces the boundary cylinder event to
a prefix-matching event on the walk; the remaining two compute the
probability of that event recursively (factor `1/4` at step 0, factor
`1/3` at each subsequent step).  Each leaf is now a *theorem*, derived
from the kernel-only Wave 35 chain (Waves 35.2b, 35.3, 35.4, 35.5):
elementary product-measure decomposition + stopped martingale +
bounded-convergence — no filtration / strong-Markov infrastructure
required.  The earlier Tier-C framing has been retired.
-/

/-- The "walk-prefix event": trajectories whose random-walk prefix at
level `p` agrees (as a boundary ray) with `φ` in the first `p` letters.
Concretely, this is the pullback of the cylinder under `X_∞^{(x)}`,
the boundary-limit map of the trajectory `n ↦ x · X_walk n Y` starting
at `x` (Wave 35-prep cumulative-walk semantics). -/
def walkPrefixEvent (x : F2) (φ : F2_boundary) (p : ℕ) : Set (ℕ → F2) :=
  {Y : ℕ → F2 | X_infinity_starting_at x Y ∈ cylinder φ p}

/-- **Measurability of the walk-prefix event.** By construction, the
event is the preimage of a measurable cylinder by a measurable map. -/
lemma walkPrefixEvent_measurable (x : F2) (φ : F2_boundary) (p : ℕ) :
    MeasurableSet (walkPrefixEvent x φ p) :=
  (X_infinity_starting_at_measurable x) (cylinder_measurable φ p)

/-- **Leaf 1 — cylinder-to-walk reduction.** The harmonic measure of a
cylinder equals the step-measure of the corresponding walk-prefix event.

This is *not* substantive: it is just unfolding `harmonic_measure` as a
pushforward and `walkPrefixEvent` as a preimage. -/
lemma harmonic_measure_cylinder_eq_walk_event
    (x : F2) (φ : F2_boundary) (p : ℕ) :
    (harmonic_measure x) (cylinder φ p)
      = step_measure (walkPrefixEvent x φ p) := by
  -- Unfold `harmonic_measure` as `Measure.map` of a measurable map and
  -- apply `Measure.map_apply` with the measurable cylinder.
  -- `walkPrefixEvent x φ p` is by definition the preimage of the
  -- cylinder under `X_∞^{(x)}`, so the RHS is exactly
  -- `step_measure.map _ (cylinder φ p)`.
  unfold harmonic_measure
  rw [MeasureTheory.Measure.map_apply
    (X_infinity_starting_at_measurable x) (cylinder_measurable φ p)]
  rfl

/-! ### Wave 35.3 keystone — partition by hitting time

The keystone identity factorises the joint event
`{X_∞^x Y ∈ cyl(φ, q)} ∩ {T_u_at x u Y = n}` as a product, exhibiting the
strong-Markov structure made explicit through the n-step head-shift of
`step_measure`.

The proof proceeds by induction on `n`:
* **Base `n = 0`.** The event `{T_u_at x u Y = 0}` is empty if `x ≠ u`
  and equals the full sample space if `x = u`. Both sides match.
* **Inductive step `n + 1`.** When `x ≠ u`, the event
  `{T_u_at x u Y = n+1}` corresponds (via the one-step head-shift
  `Y ↔ (Y 0, Y ∘ succ)` and `step_measure_head_shift`) to the event
  `{T_u_at (x · Y 0) u (Y ∘ succ) = n}`. Furthermore, since
  `x · X_walk (k+1) Y = (x · Y 0) · X_walk k (Y ∘ succ)`, the boundary
  limit `X_∞^x Y` agrees with `X_∞^{(x · Y 0)} (Y ∘ succ)` on the
  convergence sets. The Fubini integration of the inductive hypothesis
  over `Y 0 ∂ Z_uniform` then yields the keystone for `n+1`.

Once the keystone is proven, summing over `n ∈ ℕ` (using
`step_measure_T_u_at_lt_top` from Wave 35.2b for the geometric sum
of hitting probabilities, and `cylinder_event_subset_T_u_at_lt_top` from
Wave 35.4 for the geometric inclusion) yields
`harmonic_measure_factor_at_meeting_vertex_x` and
`harmonic_measure_factor_at_meeting_vertex_one` as theorems. -/

/-- **Wave 35.3 helper — convergence-set head-shift equivalence.** For any
`x ∈ F_2` and `Y : ℕ → F_2`, `Y ∈ convergenceSet_at x` iff
`Y 0 ∈ F2_generating_set` AND `(Y ∘ succ) ∈ convergenceSet_at (x * Y 0)`. -/
private lemma convergenceSet_at_iff_head_shift (x : F2) (Y : ℕ → F2) :
    Y ∈ convergenceSet_at x ↔
      Y 0 ∈ F2_generating_set ∧ (Y ∘ Nat.succ) ∈ convergenceSet_at (x * Y 0) := by
  unfold convergenceSet_at
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hY_gen, hY_len⟩
    refine ⟨hY_gen 0, ?_, ?_⟩
    · intro n; exact hY_gen (n + 1)
    · -- `n ↦ word_length ((x · Y 0) · X_walk n (Y ∘ succ))`
      --     = `n ↦ word_length (x · X_walk (n+1) Y)` (by word_length_succ_at).
      have h_eq : ∀ n,
          (word_length ((x * Y 0) * X_walk n (Y ∘ Nat.succ)) : ℝ)
            = (word_length (x * X_walk (n + 1) Y) : ℝ) :=
        fun n => by rw [word_length_succ_at]
      have h_shifted : Tendsto (fun n : ℕ =>
          (word_length (x * X_walk (n + 1) Y) : ℝ)) atTop atTop :=
        hY_len.comp (Filter.tendsto_add_atTop_nat 1)
      convert h_shifted using 1
      funext n; rw [h_eq n]
  · rintro ⟨h0, hYS_gen, hYS_len⟩
    refine ⟨?_, ?_⟩
    · intro n
      cases n with
      | zero => exact h0
      | succ m => exact hYS_gen m
    · have h_eq : ∀ n,
          (word_length ((x * Y 0) * X_walk n (Y ∘ Nat.succ)) : ℝ)
            = (word_length (x * X_walk (n + 1) Y) : ℝ) :=
        fun n => by rw [word_length_succ_at]
      have h_shifted : Tendsto (fun n : ℕ =>
          (word_length (x * X_walk (n + 1) Y) : ℝ)) atTop atTop := by
        convert hYS_len using 1
        funext n; rw [h_eq n]
      -- Recover original tendsto from shifted.
      rw [Filter.tendsto_atTop_atTop] at h_shifted ⊢
      intro M
      obtain ⟨N, hN⟩ := h_shifted M
      refine ⟨N + 1, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      have hk : N ≤ k := by omega
      exact hN k hk

/-- **Wave 35.3 helper — boundary-limit head-shift.** When `Y` lies in the
shifted convergence set `convergenceSet_at x` AND the one-step shifted path
`Y ∘ succ` lies in `convergenceSet_at (x * Y 0)`, the boundary limits agree:
`X_infinity_starting_at x Y = X_infinity_starting_at (x * Y 0) (Y ∘ succ)`.

The proof: both limits use `walk_boundary_limit_at`, whose `val` is the
limit-letter sequence. The cumulative trajectory `n ↦ x · X_walk n Y` shifted
by one step is `n ↦ (x · Y 0) · X_walk n (Y ∘ succ)` (by
`X_walk_succ_left_at`), so the limit-letters at every depth agree. -/
private lemma X_infinity_starting_at_head_shift
    (x : F2) (Y : ℕ → F2) (hY : Y ∈ convergenceSet_at x)
    (hYS : (Y ∘ Nat.succ) ∈ convergenceSet_at (x * Y 0)) :
    X_infinity_starting_at x Y =
      X_infinity_starting_at (x * Y 0) (Y ∘ Nat.succ) := by
  classical
  obtain ⟨hY_gen, hY_len⟩ := hY
  obtain ⟨hYS_gen, hYS_len⟩ := hYS
  have h_unfold_x : X_infinity_starting_at x Y =
      walk_boundary_limit_at x Y hY_gen hY_len := by
    simp only [X_infinity_starting_at]
    rw [dif_pos hY_gen, dif_pos hY_len]
  have h_unfold_v : X_infinity_starting_at (x * Y 0) (Y ∘ Nat.succ) =
      walk_boundary_limit_at (x * Y 0) (Y ∘ Nat.succ) hYS_gen hYS_len := by
    simp only [X_infinity_starting_at]
    rw [dif_pos hYS_gen, dif_pos hYS_len]
  rw [h_unfold_x, h_unfold_v]
  -- The two limit-letter sequences agree at every depth `i`.
  apply Subtype.ext
  funext i
  -- For both: pick large `M` such that the `i+1`-prefix has stabilised.
  obtain ⟨M₁, hM₁⟩ := walk_limit_letter_at_eq_at_large x Y hY_gen hY_len i
  obtain ⟨M₂, hM₂⟩ := walk_limit_letter_at_eq_at_large (x * Y 0) (Y ∘ Nat.succ)
    hYS_gen hYS_len i
  set M := max M₁ M₂
  have hM₁M : M₁ ≤ M := le_max_left _ _
  have hM₂M : M₂ ≤ M := le_max_right _ _
  have h_right : ((x * Y 0) * X_walk M (Y ∘ Nat.succ)).toWord[i]?
      = some (walk_limit_letter_at (x * Y 0) (Y ∘ Nat.succ) hYS_gen hYS_len i) :=
    hM₂ M hM₂M
  have h_shift : (x * X_walk (M + 1) Y).toWord
      = ((x * Y 0) * X_walk M (Y ∘ Nat.succ)).toWord := by
    rw [X_walk_succ_left_at]
  -- Stabilisation at M+1 ≥ M ≥ M₁ for the LHS.
  have hM₁M_succ : M₁ ≤ M + 1 := le_trans hM₁M (Nat.le_succ _)
  have h_left_succ : (x * X_walk (M + 1) Y).toWord[i]?
      = some (walk_limit_letter_at x Y hY_gen hY_len i) := hM₁ (M + 1) hM₁M_succ
  have heq : (x * X_walk (M + 1) Y).toWord[i]?
      = ((x * Y 0) * X_walk M (Y ∘ Nat.succ)).toWord[i]? := by
    rw [h_shift]
  rw [heq] at h_left_succ
  rw [h_right] at h_left_succ
  change (walk_boundary_limit_at x Y hY_gen hY_len).val i
      = (walk_boundary_limit_at (x * Y 0) (Y ∘ Nat.succ) hYS_gen hYS_len).val i
  simp only [walk_boundary_limit_at]
  exact (Option.some.inj h_left_succ).symm

/-- **Wave 35.3 helper — `convergenceSet_at` has full step_measure-mass.**

By `walk_step_in_generating_set_ae` and `walk_dist_tendsto_atTop_at`, the
defining conditions hold almost surely. -/
private lemma convergenceSet_at_ae (x : F2) :
    ∀ᵐ Y ∂step_measure, Y ∈ convergenceSet_at x := by
  filter_upwards [walk_step_in_generating_set_ae,
    walk_dist_tendsto_atTop_at x] with Y hY_gen hY_len
  exact ⟨hY_gen, hY_len⟩

/-- **Wave 35.3 helper — head-shift Fubini.** For any measurable set
`E ⊆ ℕ → F_2`,
```
step_measure E = ∫⁻ z, step_measure {Y' | consSucc (z, Y') ∈ E} ∂Z_uniform.
```
This is the integral form of `step_measure_head_shift`: integrate over the
first coordinate of `Y` against `Z_uniform`, and integrate the tail
`Y ∘ succ` against `step_measure`. -/
private lemma step_measure_head_shift_fubini
    {E : Set (ℕ → F2)} (hE : MeasurableSet E) :
    step_measure E
      = ∫⁻ z, step_measure {Y' : ℕ → F2 | consSucc (z, Y') ∈ E} ∂Z_uniform := by
  classical
  -- Step 1: rewrite step_measure E via consSucc∘headShift = id.
  have h_id : (consSucc ∘ headShift : (ℕ → F2) → (ℕ → F2)) = id := by
    funext Y; exact consSucc_headShift Y
  have h_consPre : (consSucc ⁻¹' E : Set (F2 × (ℕ → F2))) =
      (consSucc ⁻¹' E) := rfl
  -- Step 2: step_measure E = (map headShift step_measure) (consSucc⁻¹' E).
  have h_meas_consPre : MeasurableSet (consSucc ⁻¹' E) :=
    measurable_consSucc hE
  have h_eq1 : step_measure E
      = (Measure.map headShift step_measure) (consSucc ⁻¹' E) := by
    rw [Measure.map_apply measurable_headShift h_meas_consPre]
    -- headShift ⁻¹' (consSucc ⁻¹' E) = (consSucc ∘ headShift) ⁻¹' E = E.
    have h_pre : headShift ⁻¹' (consSucc ⁻¹' E) = E := by
      ext Y; simp [Set.mem_preimage, consSucc_headShift]
    rw [h_pre]
  -- Step 3: substitute step_measure_head_shift.
  rw [h_eq1, step_measure_head_shift]
  -- Step 4: apply Measure.prod_apply.
  rw [Measure.prod_apply h_meas_consPre]
  -- Step 5: rewrite the inner preimage.
  apply lintegral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  congr 1

/-- **Wave 35.3 keystone — partition by hitting time.**

For every starting vertex `x`, target `u`, boundary point `φ`, depth `q`,
and step count `n : ℕ`, the joint event
`{X_∞^x Y ∈ cyl(φ, q)} ∩ {T_u_at x u Y = n}` factors as
`step_measure {T_u_at x u Y = n} · step_measure {X_∞^u Y ∈ cyl(φ, q)}`.

This is the strong-Markov factorisation made explicit: given that the walk
from `x` hits `u` at the precise time `n`, the rest of the trajectory is
a fresh SRW from `u` (independent of `Y_0, ..., Y_{n-1}`, by the
i.i.d. structure of `step_measure`).

**Proof.** Induction on `n`, using:
* `step_measure_head_shift_fubini` to peel off the first coordinate;
* `T_u_at_eq_succ_iff_head_shift` to translate `T = n+1 (full)` to
  `T = n (shifted)` for `x ≠ u`;
* `X_infinity_starting_at_head_shift` to identify `X_∞^x Y` with
  `X_∞^{(x · Y 0)} (Y ∘ succ)` on the convergence sets. -/
theorem step_measure_cylinder_partition_T_u_at_eq
    (x u : F2) (φ : F2_boundary) (q n : ℕ) :
    step_measure
      ({Y | X_infinity_starting_at x Y ∈ cylinder φ q} ∩
       {Y | T_u_at x u Y = (n : ℕ∞)})
    = step_measure {Y | T_u_at x u Y = (n : ℕ∞)}
      * step_measure {Y | X_infinity_starting_at u Y ∈ cylinder φ q} := by
  classical
  -- We prove by induction on `n`, generalising over the starting vertex `x`.
  induction n generalizing x with
  | zero =>
    -- Base case: T_u_at x u Y = 0 iff x = u.
    -- Note: the goal mentions `((0 : ℕ) : ℕ∞)`, which is `(0 : ℕ∞)` after norm_cast.
    have h_zero_cast : ((0 : ℕ) : ℕ∞) = (0 : ℕ∞) := by norm_cast
    by_cases hxu : x = u
    · -- x = u: the event {T = 0} is the full sample space.
      have h_full : {Y : ℕ → F2 | T_u_at x u Y = ((0 : ℕ) : ℕ∞)} = Set.univ := by
        ext Y
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, h_zero_cast]
        rw [T_u_at_eq_zero_iff]; exact hxu
      rw [h_full, Set.inter_univ]
      have h_meas_full : step_measure (Set.univ : Set (ℕ → F2)) = 1 := measure_univ
      rw [h_meas_full, one_mul]
      rw [hxu]
    · -- x ≠ u: the event {T = 0} is empty.
      have h_empty : {Y : ℕ → F2 | T_u_at x u Y = ((0 : ℕ) : ℕ∞)} = ∅ := by
        ext Y
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, h_zero_cast]
        rw [T_u_at_eq_zero_iff]; exact hxu
      rw [h_empty, Set.inter_empty, measure_empty, zero_mul]
  | succ n ih =>
    -- Inductive step: keystone for `n+1`, given the IH for `n` for all `x`.
    by_cases hxu : x = u
    · -- x = u: T_u_at u u Y = 0 always, so {T = n+1} = ∅.
      have h_empty : {Y : ℕ → F2 | T_u_at x u Y = ((n + 1 : ℕ) : ℕ∞)} = ∅ := by
        ext Y
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro h
        have h0 : T_u_at x u Y = (0 : ℕ∞) := by
          rw [T_u_at_eq_zero_iff]; exact hxu
        rw [h0] at h
        exact absurd h (by exact_mod_cast Nat.succ_ne_zero n)
      rw [h_empty, Set.inter_empty, measure_empty, zero_mul]
    · -- x ≠ u: use head-shift + IH.
      -- Set up notation.
      set E_joint : Set (ℕ → F2) :=
        {Y | X_infinity_starting_at x Y ∈ cylinder φ q} ∩
        {Y | T_u_at x u Y = ((n + 1 : ℕ) : ℕ∞)}
        with hE_joint_def
      set E_T : Set (ℕ → F2) :=
        {Y | T_u_at x u Y = ((n + 1 : ℕ) : ℕ∞)} with hE_T_def
      set E_u : Set (ℕ → F2) :=
        {Y | X_infinity_starting_at u Y ∈ cylinder φ q} with hE_u_def
      -- Measurability
      have hE_T_meas : MeasurableSet E_T := by
        rw [hE_T_def]
        have : ({Y : ℕ → F2 | T_u_at x u Y = ((n + 1 : ℕ) : ℕ∞)})
            = (X_walk (n + 1))⁻¹' ({x⁻¹ * u} : Set F2) ∩
              ⋂ k ∈ Finset.range (n + 1),
                ((X_walk k)⁻¹' ({x⁻¹ * u} : Set F2))ᶜ := by
          ext Y
          simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage,
            Set.mem_singleton_iff, Set.mem_iInter, Set.mem_compl_iff,
            Finset.mem_range, Finset.mem_coe]
          rw [T_u_at_eq_coe_iff]
          constructor
          · rintro ⟨h_hit, h_no_early⟩
            refine ⟨?_, ?_⟩
            · rw [show x⁻¹ * u = x⁻¹ * (x * X_walk (n + 1) Y) from by rw [h_hit]]
              group
            · intro k hk
              intro h_eq
              apply h_no_early k hk
              rw [show x * X_walk k Y = x * (x⁻¹ * u) from by rw [h_eq]]
              group
          · rintro ⟨h_hit, h_no_early⟩
            refine ⟨?_, ?_⟩
            · rw [show x * X_walk (n + 1) Y = x * (x⁻¹ * u) from by rw [h_hit]]
              group
            · intro k hk h_eq
              apply h_no_early k hk
              rw [show x⁻¹ * u = x⁻¹ * (x * X_walk k Y) from by rw [h_eq]]
              group
        rw [this]
        refine MeasurableSet.inter ?_ ?_
        · exact (X_walk_measurable _) (MeasurableSet.singleton _)
        · refine MeasurableSet.biInter (Finset.range (n + 1)).countable_toSet ?_
          intro k _
          exact ((X_walk_measurable _) (MeasurableSet.singleton _)).compl
      have hB_x_meas : MeasurableSet
          ({Y : ℕ → F2 | X_infinity_starting_at x Y ∈ cylinder φ q}) :=
        (X_infinity_starting_at_measurable x) (cylinder_measurable φ q)
      have hE_joint_meas : MeasurableSet E_joint := hB_x_meas.inter hE_T_meas
      have hB_u_meas : MeasurableSet E_u :=
        (X_infinity_starting_at_measurable u) (cylinder_measurable φ q)
      -- Apply the head-shift Fubini to E_joint.
      rw [step_measure_head_shift_fubini hE_joint_meas]
      -- Apply head-shift Fubini to E_T.
      have h_T_fubini :
          step_measure E_T
            = ∫⁻ z, step_measure
                {Y' : ℕ → F2 | consSucc (z, Y') ∈ E_T} ∂Z_uniform :=
        step_measure_head_shift_fubini hE_T_meas
      -- Identify the inner integrands.
      -- For the joint event, on the a.s. set {z ∈ F2_generating_set} and
      -- `Y'` in `convergenceSet_at (x * z)`, we have:
      -- `consSucc (z, Y') ∈ E_joint` iff `Y' ∈ {X_∞^{x*z} ∈ cyl φ q} ∩ {T_u_at (x*z) u = n}`.
      -- For E_T, similarly: `consSucc (z, Y') ∈ E_T` iff `Y' ∈ {T_u_at (x*z) u = n}`.
      -- We use the IH at (x*z, u, n) to conclude.
      have h_inner_joint : ∀ᵐ z ∂Z_uniform,
          step_measure {Y' : ℕ → F2 | consSucc (z, Y') ∈ E_joint}
            = step_measure
                ({Y' | X_infinity_starting_at (x * z) Y' ∈ cylinder φ q} ∩
                 {Y' | T_u_at (x * z) u Y' = (n : ℕ∞)}) := by
        -- The condition `z ∈ F2_generating_set` holds Z_uniform-a.s.
        have hZ_gen_ae : ∀ᵐ z ∂Z_uniform, z ∈ F2_generating_set := by
          rw [ae_iff]
          unfold Z_uniform
          rw [Measure.smul_apply]
          have hA : (Measure.dirac (genA : F2)) {z | z ∉ F2_generating_set} = 0 := by
            rw [Measure.dirac_apply]
            apply Set.indicator_of_notMem
            intro h; exact h (by left; rfl)
          have hB : (Measure.dirac (genB : F2)) {z | z ∉ F2_generating_set} = 0 := by
            rw [Measure.dirac_apply]
            apply Set.indicator_of_notMem
            intro h; exact h (by right; left; rfl)
          have hAi : (Measure.dirac ((genA : F2)⁻¹))
              {z | z ∉ F2_generating_set} = 0 := by
            rw [Measure.dirac_apply]
            apply Set.indicator_of_notMem
            intro h; exact h (by right; right; left; rfl)
          have hBi : (Measure.dirac ((genB : F2)⁻¹))
              {z | z ∉ F2_generating_set} = 0 := by
            rw [Measure.dirac_apply]
            apply Set.indicator_of_notMem
            intro h; exact h (by right; right; right; rfl)
          rw [Measure.add_apply, Measure.add_apply, Measure.add_apply,
            hA, hB, hAi, hBi]
          simp
        filter_upwards [hZ_gen_ae] with z hz
        -- Now show inner sets are equal a.s. under step_measure via measure_congr.
        apply measure_congr
        have h_conv_xz : ∀ᵐ Y' ∂step_measure, Y' ∈ convergenceSet_at (x * z) :=
          convergenceSet_at_ae (x * z)
        filter_upwards [h_conv_xz] with Y' hY'
        have h_zero : consSucc (z, Y') 0 = z := consSucc_zero z Y'
        have h_succ : (consSucc (z, Y')) ∘ Nat.succ = Y' := by
          funext k; exact consSucc_succ z Y' k
        have h_Y_conv : consSucc (z, Y') ∈ convergenceSet_at x := by
          rw [convergenceSet_at_iff_head_shift, h_zero, h_succ]
          exact ⟨hz, hY'⟩
        have h_Y_succ_conv :
            (consSucc (z, Y')) ∘ Nat.succ ∈ convergenceSet_at (x * (consSucc (z, Y') 0)) := by
          rw [h_zero, h_succ]; exact hY'
        have h_X_inf : X_infinity_starting_at x (consSucc (z, Y'))
            = X_infinity_starting_at (x * z) Y' := by
          rw [X_infinity_starting_at_head_shift x (consSucc (z, Y')) h_Y_conv h_Y_succ_conv]
          rw [h_zero, h_succ]
        have h_T : T_u_at x u (consSucc (z, Y')) = ((n + 1 : ℕ) : ℕ∞)
            ↔ T_u_at (x * z) u Y' = ((n : ℕ) : ℕ∞) := by
          have hkey := T_u_at_eq_succ_iff_head_shift x u n (consSucc (z, Y')) hxu
          rw [h_zero, h_succ] at hkey
          exact hkey
        -- Goal: `s Y' = t Y'` (as Prop, since Set α = α → Prop).
        apply propext
        change consSucc (z, Y') ∈ E_joint ↔
          (X_infinity_starting_at (x * z) Y' ∈ cylinder φ q
            ∧ T_u_at (x * z) u Y' = (n : ℕ∞))
        rw [hE_joint_def]
        change (X_infinity_starting_at x (consSucc (z, Y')) ∈ cylinder φ q
            ∧ consSucc (z, Y') ∈ E_T) ↔ _
        rw [hE_T_def]
        change (X_infinity_starting_at x (consSucc (z, Y')) ∈ cylinder φ q
            ∧ T_u_at x u (consSucc (z, Y')) = ((n + 1 : ℕ) : ℕ∞)) ↔ _
        rw [h_X_inf]
        constructor
        · intro ⟨h1, h2⟩
          exact ⟨h1, h_T.mp h2⟩
        · intro ⟨h1, h2⟩
          exact ⟨h1, h_T.mpr h2⟩
      have h_inner_T : ∀ᵐ z ∂Z_uniform,
          step_measure {Y' : ℕ → F2 | consSucc (z, Y') ∈ E_T}
            = step_measure {Y' | T_u_at (x * z) u Y' = (n : ℕ∞)} := by
        apply Filter.Eventually.of_forall
        intro z
        apply measure_congr
        apply Filter.Eventually.of_forall
        intro Y'
        have h_zero : consSucc (z, Y') 0 = z := consSucc_zero z Y'
        have h_succ : (consSucc (z, Y')) ∘ Nat.succ = Y' := by
          funext k; exact consSucc_succ z Y' k
        apply propext
        change consSucc (z, Y') ∈ E_T ↔ T_u_at (x * z) u Y' = (n : ℕ∞)
        rw [hE_T_def]
        change T_u_at x u (consSucc (z, Y')) = ((n + 1 : ℕ) : ℕ∞) ↔ _
        have hkey := T_u_at_eq_succ_iff_head_shift x u n (consSucc (z, Y')) hxu
        rw [h_zero, h_succ] at hkey
        exact hkey
      -- Apply IH at each (x*z, u, n).
      rw [lintegral_congr_ae h_inner_joint]
      have h_ih_apply : ∀ z : F2,
          step_measure
              ({Y' | X_infinity_starting_at (x * z) Y' ∈ cylinder φ q} ∩
               {Y' | T_u_at (x * z) u Y' = (n : ℕ∞)})
            = step_measure {Y' | T_u_at (x * z) u Y' = (n : ℕ∞)}
              * step_measure E_u := by
        intro z; rw [hE_u_def]; exact ih (x * z)
      rw [lintegral_congr_ae (Filter.Eventually.of_forall h_ih_apply)]
      -- Pull `step_measure E_u` out as a constant factor.
      rw [lintegral_mul_const _ ?meas]
      case meas =>
        -- The function `z ↦ step_measure {T_u_at (x*z) u Y' = n}` is measurable.
        -- Since the codomain is `ℝ≥0∞` which is countable-discrete...
        -- Actually we need this to be measurable in `z`. Use `measurable_of_countable`?
        -- F2 is a discrete space (with top σ-algebra), so any function out of F2 is measurable.
        intro s _
        exact MeasurableSpace.measurableSet_top
      -- Now we have:
      -- (∫⁻ z, step_measure {T_u_at (x*z) u = n} ∂Z_uniform) * step_measure E_u
      -- We want: step_measure E_T * step_measure E_u.
      -- So it suffices to show: step_measure E_T = ∫⁻ z, step_measure {T_u_at (x*z) u = n} ∂Z_uniform.
      rw [show step_measure E_T
            = ∫⁻ z, step_measure
                {Y' : ℕ → F2 | T_u_at (x * z) u Y' = (n : ℕ∞)} ∂Z_uniform from by
        rw [h_T_fubini]
        exact lintegral_congr_ae h_inner_T]

/-- **Wave 35.3 Step 3.3 — sum-over-n keystone.**

Summing the partition-by-hitting-time identity over `n ∈ ℕ`, the cylinder
event factorises through the meeting vertex when `q ≥ |x|`:
```
step_measure {X_∞^x ∈ cyl φ q}
  = step_measure {T_u_at x u Y < ⊤} * step_measure {X_∞^u ∈ cyl φ q}
```
where `u := φ.valPrefix (common_prefix_length x φ)`.

The proof uses Wave 35.4 (`cylinder_event_subset_T_u_at_lt_top`) to show
the cylinder event is a.s. contained in `{T_u_at x u Y < ⊤}`, then partitions
via the disjoint union `{T < ⊤} = ⋃ n {T = n}`. -/
private lemma step_measure_cylinder_factor_meeting_vertex
    (x : F2) (φ : F2_boundary) (q : ℕ) (hq : x.toWord.length ≤ q) :
    step_measure
      {Y : ℕ → F2 | X_infinity_starting_at x Y ∈ cylinder φ q}
    = step_measure
        {Y : ℕ → F2 | T_u_at x
          (F2_boundary.valPrefix φ (common_prefix_length x φ)) Y < ⊤}
      * step_measure
        {Y : ℕ → F2 | X_infinity_starting_at
          (F2_boundary.valPrefix φ (common_prefix_length x φ)) Y ∈ cylinder φ q} := by
  classical
  set u : F2 := F2_boundary.valPrefix φ (common_prefix_length x φ) with hu_def
  -- Step 1: a.s. equality
  -- {X_∞^x ∈ cyl φ q} ∩ convergenceSet_at x ⊆ {T_u_at x u Y < ⊤} (by Wave 35.4).
  have h_subset : ∀ Y, Y ∈ convergenceSet_at x →
      X_infinity_starting_at x Y ∈ cylinder φ q →
      T_u_at x u Y < ⊤ := by
    intro Y hY_conv hY_cyl
    obtain ⟨hY_gen, hY_len⟩ := hY_conv
    have h_in : Y ∈ {Y : ℕ → F2 | (∀ n, Y n ∈ F2_generating_set) ∧
        Tendsto (fun n : ℕ => (word_length (x * X_walk n Y) : ℝ)) atTop atTop ∧
        X_infinity_starting_at x Y ∈ cylinder φ q} := ⟨hY_gen, hY_len, hY_cyl⟩
    have h_T := cylinder_event_subset_T_u_at_lt_top x φ q hq h_in
    rw [hu_def]; exact h_T
  -- A.s. on `step_measure`, the cylinder event is contained in {T < ⊤}.
  set A : Set (ℕ → F2) := {Y | X_infinity_starting_at x Y ∈ cylinder φ q}
    with hA_def
  set B : Set (ℕ → F2) := {Y | T_u_at x u Y < ⊤} with hB_def
  have h_aeEq : A =ᵐ[step_measure] Set.inter A B := by
    filter_upwards [convergenceSet_at_ae x] with Y hY_conv
    apply propext
    show Y ∈ A ↔ Y ∈ Set.inter A B
    rw [hA_def, hB_def]
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro hY_cyl
      exact ⟨hY_cyl, h_subset Y hY_conv hY_cyl⟩
    · intro hY; exact hY.1
  rw [measure_congr h_aeEq]
  -- Step 2: partition `{T < ⊤} = ⋃_n {T = n}`.
  have h_partition :
      (Set.inter A B : Set (ℕ → F2))
        = ⋃ n : ℕ, ({Y : ℕ → F2 | X_infinity_starting_at x Y ∈ cylinder φ q} ∩
            {Y : ℕ → F2 | T_u_at x u Y = (n : ℕ∞)}) := by
    ext Y
    constructor
    · intro hY
      have hcyl : X_infinity_starting_at x Y ∈ cylinder φ q := hY.1
      have hT : T_u_at x u Y < ⊤ := hY.2
      rw [T_u_at_lt_top_iff] at hT
      classical
      set k := Nat.find hT with hk_def
      have hk_spec : x * X_walk k Y = u := Nat.find_spec hT
      refine Set.mem_iUnion.mpr ⟨k, hcyl, ?_⟩
      show T_u_at x u Y = (k : ℕ∞)
      rw [T_u_at_eq_coe_iff]
      refine ⟨hk_spec, ?_⟩
      intro k' hk'
      exact Nat.find_min hT hk'
    · intro hY
      obtain ⟨n, hY⟩ := Set.mem_iUnion.mp hY
      have hcyl : X_infinity_starting_at x Y ∈ cylinder φ q := hY.1
      have hTn : T_u_at x u Y = (n : ℕ∞) := hY.2
      refine ⟨hcyl, ?_⟩
      show T_u_at x u Y < ⊤
      rw [hTn]; simp
  rw [h_partition]
  -- Step 3: σ-additivity over disjoint union.
  have h_disj : Pairwise (Function.onFun (Disjoint (α := Set (ℕ → F2)))
      (fun n : ℕ => {Y : ℕ → F2 | X_infinity_starting_at x Y ∈ cylinder φ q} ∩
        {Y | T_u_at x u Y = (n : ℕ∞)})) := by
    intro n m hnm
    refine Set.disjoint_iff.mpr ?_
    rintro Y ⟨⟨_, hYn⟩, ⟨_, hYm⟩⟩
    have h : (n : ℕ∞) = (m : ℕ∞) := hYn.symm.trans hYm
    have h' : n = m := by exact_mod_cast h
    exact hnm h'
  have h_meas_each : ∀ n : ℕ, MeasurableSet
      ({Y : ℕ → F2 | X_infinity_starting_at x Y ∈ cylinder φ q} ∩
       {Y | T_u_at x u Y = (n : ℕ∞)}) := by
    intro n
    refine MeasurableSet.inter
      ((X_infinity_starting_at_measurable x) (cylinder_measurable φ q)) ?_
    -- Measurability of {T_u_at x u Y = n} as in keystone.
    have : ({Y : ℕ → F2 | T_u_at x u Y = ((n : ℕ) : ℕ∞)})
        = (X_walk n)⁻¹' ({x⁻¹ * u} : Set F2) ∩
          ⋂ k ∈ Finset.range n,
            ((X_walk k)⁻¹' ({x⁻¹ * u} : Set F2))ᶜ := by
      ext Y
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_singleton_iff, Set.mem_iInter, Set.mem_compl_iff,
        Finset.mem_range, Finset.mem_coe]
      rw [T_u_at_eq_coe_iff]
      constructor
      · rintro ⟨h_hit, h_no_early⟩
        refine ⟨?_, ?_⟩
        · rw [show x⁻¹ * u = x⁻¹ * (x * X_walk n Y) from by rw [h_hit]]; group
        · intro k hk h_eq
          apply h_no_early k hk
          rw [show x * X_walk k Y = x * (x⁻¹ * u) from by rw [h_eq]]; group
      · rintro ⟨h_hit, h_no_early⟩
        refine ⟨?_, ?_⟩
        · rw [show x * X_walk n Y = x * (x⁻¹ * u) from by rw [h_hit]]; group
        · intro k hk h_eq
          apply h_no_early k hk
          rw [show x⁻¹ * u = x⁻¹ * (x * X_walk k Y) from by rw [h_eq]]; group
    rw [this]
    refine MeasurableSet.inter ?_ ?_
    · exact (X_walk_measurable _) (MeasurableSet.singleton _)
    · refine MeasurableSet.biInter (Finset.range n).countable_toSet ?_
      intro k _
      exact ((X_walk_measurable _) (MeasurableSet.singleton _)).compl
  rw [measure_iUnion h_disj h_meas_each]
  -- Apply keystone for each n.
  have h_keystone_n : ∀ n : ℕ,
      step_measure ({Y : ℕ → F2 | X_infinity_starting_at x Y ∈ cylinder φ q} ∩
        {Y | T_u_at x u Y = (n : ℕ∞)})
      = step_measure {Y | T_u_at x u Y = (n : ℕ∞)}
        * step_measure {Y | X_infinity_starting_at u Y ∈ cylinder φ q} := by
    intro n
    exact step_measure_cylinder_partition_T_u_at_eq x u φ q n
  rw [tsum_congr h_keystone_n]
  -- Pull constant factor.
  rw [ENNReal.tsum_mul_right]
  -- Now: ∑_n step_measure {T = n} = step_measure {T < ⊤}.
  have h_sum_T : ∑' n : ℕ, step_measure {Y : ℕ → F2 | T_u_at x u Y = (n : ℕ∞)}
      = step_measure {Y | T_u_at x u Y < ⊤} := by
    have h_T_partition :
        {Y : ℕ → F2 | T_u_at x u Y < ⊤}
          = ⋃ n : ℕ, {Y | T_u_at x u Y = (n : ℕ∞)} := by
      ext Y
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · intro hT
        rw [T_u_at_lt_top_iff] at hT
        classical
        set k := Nat.find hT with hk_def
        refine ⟨k, ?_⟩
        rw [T_u_at_eq_coe_iff]
        refine ⟨Nat.find_spec hT, ?_⟩
        intro k' hk'
        exact Nat.find_min hT hk'
      · rintro ⟨n, hTn⟩
        rw [hTn]; simp
    have h_T_disj : Pairwise (Function.onFun (Disjoint (α := Set (ℕ → F2)))
        (fun n : ℕ => {Y : ℕ → F2 | T_u_at x u Y = (n : ℕ∞)})) := by
      intro n m hnm
      refine Set.disjoint_iff.mpr ?_
      rintro Y ⟨hYn, hYm⟩
      have h : (n : ℕ∞) = (m : ℕ∞) := hYn.symm.trans hYm
      have h' : n = m := by exact_mod_cast h
      exact hnm h'
    have h_T_meas : ∀ n : ℕ, MeasurableSet
        {Y : ℕ → F2 | T_u_at x u Y = (n : ℕ∞)} := by
      intro n
      have : ({Y : ℕ → F2 | T_u_at x u Y = ((n : ℕ) : ℕ∞)})
          = (X_walk n)⁻¹' ({x⁻¹ * u} : Set F2) ∩
            ⋂ k ∈ Finset.range n,
              ((X_walk k)⁻¹' ({x⁻¹ * u} : Set F2))ᶜ := by
        ext Y
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage,
          Set.mem_singleton_iff, Set.mem_iInter, Set.mem_compl_iff,
          Finset.mem_range, Finset.mem_coe]
        rw [T_u_at_eq_coe_iff]
        constructor
        · rintro ⟨h_hit, h_no_early⟩
          refine ⟨?_, ?_⟩
          · rw [show x⁻¹ * u = x⁻¹ * (x * X_walk n Y) from by rw [h_hit]]; group
          · intro k hk h_eq
            apply h_no_early k hk
            rw [show x * X_walk k Y = x * (x⁻¹ * u) from by rw [h_eq]]; group
        · rintro ⟨h_hit, h_no_early⟩
          refine ⟨?_, ?_⟩
          · rw [show x * X_walk n Y = x * (x⁻¹ * u) from by rw [h_hit]]; group
          · intro k hk h_eq
            apply h_no_early k hk
            rw [show x⁻¹ * u = x⁻¹ * (x * X_walk k Y) from by rw [h_eq]]; group
      rw [this]
      refine MeasurableSet.inter ?_ ?_
      · exact (X_walk_measurable _) (MeasurableSet.singleton _)
      · refine MeasurableSet.biInter (Finset.range n).countable_toSet ?_
        intro k _
        exact ((X_walk_measurable _) (MeasurableSet.singleton _)).compl
    rw [h_T_partition, measure_iUnion h_T_disj h_T_meas]
  rw [h_sum_T]

/-! #### Wave 35.5 D1-companion — Generalised cylinder factor lemma

Companion to `step_measure_cylinder_factor_meeting_vertex` for arbitrary
starting vertex `v` and arbitrary depth `d ≤ q` with `|v| ≤ d`. The proof
mirrors the original (partition by hitting time + σ-additivity) but uses
Wave 35.5 D1 (`cylinder_event_subset_T_u_at_lt_top_general`) for the
geometric inclusion.

Used in Wave 35.5 D3 with `v = 1` and `d = c(x, φ)` to dissolve
`harmonic_measure_factor_at_meeting_vertex_one`. -/

private lemma step_measure_cylinder_factor_at_depth
    (v : F2) (φ : F2_boundary) (q d : ℕ)
    (hd_le_q : d ≤ q) (hv_le_d : v.toWord.length ≤ d) :
    step_measure
      {Y : ℕ → F2 | X_infinity_starting_at v Y ∈ cylinder φ q}
    = step_measure
        {Y : ℕ → F2 | T_u_at v (F2_boundary.valPrefix φ d) Y < ⊤}
      * step_measure
        {Y : ℕ → F2 | X_infinity_starting_at
          (F2_boundary.valPrefix φ d) Y ∈ cylinder φ q} := by
  classical
  set u : F2 := F2_boundary.valPrefix φ d with hu_def
  -- Step 1: a.s. equality
  -- {X_∞^v ∈ cyl φ q} ∩ convergenceSet_at v ⊆ {T_u_at v u Y < ⊤} (by Wave 35.5 D1).
  have h_subset : ∀ Y, Y ∈ convergenceSet_at v →
      X_infinity_starting_at v Y ∈ cylinder φ q →
      T_u_at v u Y < ⊤ := by
    intro Y hY_conv hY_cyl
    obtain ⟨hY_gen, hY_len⟩ := hY_conv
    have h_in : Y ∈ {Y : ℕ → F2 | (∀ n, Y n ∈ F2_generating_set) ∧
        Tendsto (fun n : ℕ => (word_length (v * X_walk n Y) : ℝ)) atTop atTop ∧
        X_infinity_starting_at v Y ∈ cylinder φ q} := ⟨hY_gen, hY_len, hY_cyl⟩
    have h_T := cylinder_event_subset_T_u_at_lt_top_general v φ q d
      hd_le_q hv_le_d h_in
    rw [hu_def]; exact h_T
  -- A.s. on `step_measure`, the cylinder event is contained in {T < ⊤}.
  set A : Set (ℕ → F2) := {Y | X_infinity_starting_at v Y ∈ cylinder φ q}
    with hA_def
  set B : Set (ℕ → F2) := {Y | T_u_at v u Y < ⊤} with hB_def
  have h_aeEq : A =ᵐ[step_measure] Set.inter A B := by
    filter_upwards [convergenceSet_at_ae v] with Y hY_conv
    apply propext
    show Y ∈ A ↔ Y ∈ Set.inter A B
    rw [hA_def, hB_def]
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro hY_cyl
      exact ⟨hY_cyl, h_subset Y hY_conv hY_cyl⟩
    · intro hY; exact hY.1
  rw [measure_congr h_aeEq]
  -- Step 2: partition `{T < ⊤} = ⋃_n {T = n}`.
  have h_partition :
      (Set.inter A B : Set (ℕ → F2))
        = ⋃ n : ℕ, ({Y : ℕ → F2 | X_infinity_starting_at v Y ∈ cylinder φ q} ∩
            {Y : ℕ → F2 | T_u_at v u Y = (n : ℕ∞)}) := by
    ext Y
    constructor
    · intro hY
      have hcyl : X_infinity_starting_at v Y ∈ cylinder φ q := hY.1
      have hT : T_u_at v u Y < ⊤ := hY.2
      rw [T_u_at_lt_top_iff] at hT
      classical
      set k := Nat.find hT with hk_def
      have hk_spec : v * X_walk k Y = u := Nat.find_spec hT
      refine Set.mem_iUnion.mpr ⟨k, hcyl, ?_⟩
      show T_u_at v u Y = (k : ℕ∞)
      rw [T_u_at_eq_coe_iff]
      refine ⟨hk_spec, ?_⟩
      intro k' hk'
      exact Nat.find_min hT hk'
    · intro hY
      obtain ⟨n, hY⟩ := Set.mem_iUnion.mp hY
      have hcyl : X_infinity_starting_at v Y ∈ cylinder φ q := hY.1
      have hTn : T_u_at v u Y = (n : ℕ∞) := hY.2
      refine ⟨hcyl, ?_⟩
      show T_u_at v u Y < ⊤
      rw [hTn]; simp
  rw [h_partition]
  -- Step 3: σ-additivity over disjoint union.
  have h_disj : Pairwise (Function.onFun (Disjoint (α := Set (ℕ → F2)))
      (fun n : ℕ => {Y : ℕ → F2 | X_infinity_starting_at v Y ∈ cylinder φ q} ∩
        {Y | T_u_at v u Y = (n : ℕ∞)})) := by
    intro n m hnm
    refine Set.disjoint_iff.mpr ?_
    rintro Y ⟨⟨_, hYn⟩, ⟨_, hYm⟩⟩
    have h : (n : ℕ∞) = (m : ℕ∞) := hYn.symm.trans hYm
    have h' : n = m := by exact_mod_cast h
    exact hnm h'
  have h_meas_each : ∀ n : ℕ, MeasurableSet
      ({Y : ℕ → F2 | X_infinity_starting_at v Y ∈ cylinder φ q} ∩
       {Y | T_u_at v u Y = (n : ℕ∞)}) := by
    intro n
    refine MeasurableSet.inter
      ((X_infinity_starting_at_measurable v) (cylinder_measurable φ q)) ?_
    have : ({Y : ℕ → F2 | T_u_at v u Y = ((n : ℕ) : ℕ∞)})
        = (X_walk n)⁻¹' ({v⁻¹ * u} : Set F2) ∩
          ⋂ k ∈ Finset.range n,
            ((X_walk k)⁻¹' ({v⁻¹ * u} : Set F2))ᶜ := by
      ext Y
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_singleton_iff, Set.mem_iInter, Set.mem_compl_iff,
        Finset.mem_range, Finset.mem_coe]
      rw [T_u_at_eq_coe_iff]
      constructor
      · rintro ⟨h_hit, h_no_early⟩
        refine ⟨?_, ?_⟩
        · rw [show v⁻¹ * u = v⁻¹ * (v * X_walk n Y) from by rw [h_hit]]; group
        · intro k hk h_eq
          apply h_no_early k hk
          rw [show v * X_walk k Y = v * (v⁻¹ * u) from by rw [h_eq]]; group
      · rintro ⟨h_hit, h_no_early⟩
        refine ⟨?_, ?_⟩
        · rw [show v * X_walk n Y = v * (v⁻¹ * u) from by rw [h_hit]]; group
        · intro k hk h_eq
          apply h_no_early k hk
          rw [show v⁻¹ * u = v⁻¹ * (v * X_walk k Y) from by rw [h_eq]]; group
    rw [this]
    refine MeasurableSet.inter ?_ ?_
    · exact (X_walk_measurable _) (MeasurableSet.singleton _)
    · refine MeasurableSet.biInter (Finset.range n).countable_toSet ?_
      intro k _
      exact ((X_walk_measurable _) (MeasurableSet.singleton _)).compl
  rw [measure_iUnion h_disj h_meas_each]
  -- Apply keystone for each n.
  have h_keystone_n : ∀ n : ℕ,
      step_measure ({Y : ℕ → F2 | X_infinity_starting_at v Y ∈ cylinder φ q} ∩
        {Y | T_u_at v u Y = (n : ℕ∞)})
      = step_measure {Y | T_u_at v u Y = (n : ℕ∞)}
        * step_measure {Y | X_infinity_starting_at u Y ∈ cylinder φ q} := by
    intro n
    exact step_measure_cylinder_partition_T_u_at_eq v u φ q n
  rw [tsum_congr h_keystone_n]
  rw [ENNReal.tsum_mul_right]
  -- ∑_n step_measure {T = n} = step_measure {T < ⊤}.
  have h_sum_T : ∑' n : ℕ, step_measure {Y : ℕ → F2 | T_u_at v u Y = (n : ℕ∞)}
      = step_measure {Y | T_u_at v u Y < ⊤} := by
    have h_T_partition :
        {Y : ℕ → F2 | T_u_at v u Y < ⊤}
          = ⋃ n : ℕ, {Y | T_u_at v u Y = (n : ℕ∞)} := by
      ext Y
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · intro hT
        rw [T_u_at_lt_top_iff] at hT
        classical
        set k := Nat.find hT with hk_def
        refine ⟨k, ?_⟩
        rw [T_u_at_eq_coe_iff]
        refine ⟨Nat.find_spec hT, ?_⟩
        intro k' hk'
        exact Nat.find_min hT hk'
      · rintro ⟨n, hTn⟩
        rw [hTn]; simp
    have h_T_disj : Pairwise (Function.onFun (Disjoint (α := Set (ℕ → F2)))
        (fun n : ℕ => {Y : ℕ → F2 | T_u_at v u Y = (n : ℕ∞)})) := by
      intro n m hnm
      refine Set.disjoint_iff.mpr ?_
      rintro Y ⟨hYn, hYm⟩
      have h : (n : ℕ∞) = (m : ℕ∞) := hYn.symm.trans hYm
      have h' : n = m := by exact_mod_cast h
      exact hnm h'
    have h_T_meas : ∀ n : ℕ, MeasurableSet
        {Y : ℕ → F2 | T_u_at v u Y = (n : ℕ∞)} := by
      intro n
      have : ({Y : ℕ → F2 | T_u_at v u Y = ((n : ℕ) : ℕ∞)})
          = (X_walk n)⁻¹' ({v⁻¹ * u} : Set F2) ∩
            ⋂ k ∈ Finset.range n,
              ((X_walk k)⁻¹' ({v⁻¹ * u} : Set F2))ᶜ := by
        ext Y
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage,
          Set.mem_singleton_iff, Set.mem_iInter, Set.mem_compl_iff,
          Finset.mem_range, Finset.mem_coe]
        rw [T_u_at_eq_coe_iff]
        constructor
        · rintro ⟨h_hit, h_no_early⟩
          refine ⟨?_, ?_⟩
          · rw [show v⁻¹ * u = v⁻¹ * (v * X_walk n Y) from by rw [h_hit]]; group
          · intro k hk h_eq
            apply h_no_early k hk
            rw [show v * X_walk k Y = v * (v⁻¹ * u) from by rw [h_eq]]; group
        · rintro ⟨h_hit, h_no_early⟩
          refine ⟨?_, ?_⟩
          · rw [show v * X_walk n Y = v * (v⁻¹ * u) from by rw [h_hit]]; group
          · intro k hk h_eq
            apply h_no_early k hk
            rw [show v⁻¹ * u = v⁻¹ * (v * X_walk k Y) from by rw [h_eq]]; group
      rw [this]
      refine MeasurableSet.inter ?_ ?_
      · exact (X_walk_measurable _) (MeasurableSet.singleton _)
      · refine MeasurableSet.biInter (Finset.range n).countable_toSet ?_
        intro k _
        exact ((X_walk_measurable _) (MeasurableSet.singleton _)).compl
    rw [h_T_partition, measure_iUnion h_T_disj h_T_meas]
  rw [h_sum_T]

/-! #### Wave 31-retry — strong-Markov factorisation through the meeting vertex

`harmonic_measure_translation_on_deep_cylinder` is now a *theorem*
(Wave 29-retry), and so are the two strong-Markov factorisations it
derives from (Wave 35.5).  Historically this block introduced two narrow
admissions for those factorisations; both have since been dissolved.
The two factorisations through the **meeting vertex**
`u := φ.valPrefix(common_prefix_length x φ)` of the geodesic
`x → ∞` along the boundary ray `φ` are:

* **Strong-Markov factorisation at `T_u`, started from `x`** — the random
  walk from `x` hits `u` (an ancestor on the φ-ray) with probability
  `3^{-d(x, u)} = 3^{-(|x|-c)}` (Woess 2000 §1.24, hitting probability
  on the 4-regular tree), and conditionally on `T_u < ∞` it continues as
  an SRW from `u`. Since the cylinder `I(φ, q)` is determined by the walk
  *after* hitting `u` (when `q ≥ |x|`), strong Markov gives
  `μ_x(I(φ, q)) = 3^{-(|x|-c)} · μ_u(I(φ, q))`.

* **Strong-Markov factorisation at `T_u`, started from `1`** — the same
  meeting vertex `u = φ.valPrefix c` lies at distance `c = |u|` from `1`
  along the φ-ray, so `ℙ_1(T_u < ∞) = 3^{-c}`, and strong Markov gives
  `μ_1(I(φ, q)) = 3^{-c} · μ_u(I(φ, q))`.

Both factorisations are instances of the standard fact that for SRW on a
tree the hitting probability of any ancestor on a geodesic ray is
`3^{-d}`, combined with the strong Markov property at the first hitting
time. Reference: Woess, *Random Walks on Infinite Graphs and Groups*,
Cambridge University Press 2000, Chapter 1 (esp. §1.24, §1.D).

Project-side, these two factorisations are now derived from the user's
Prompt C reply (see `prompt_C_reply.md`): elementary product-measure
decomposition + stopped martingale + bounded convergence, all encoded in
the Wave 35 chain (Waves 35.2b, 35.3, 35.4, 35.5).  No abstract filtration
or strong-Markov infrastructure for `step_measure + X_walk` is required.
Both `harmonic_measure_factor_at_meeting_vertex_x` and
`harmonic_measure_factor_at_meeting_vertex_one` are theorems (Wave 35.5),
and the deep-cylinder identity
`harmonic_measure_translation_on_deep_cylinder` is then a one-screen
algebraic theorem on top of them.

**Wave 34 relocation.** Block moved upward (from below the previous
`harmonic_measure_one_cylinder_constant` axiom site) so that the depth-1
specialisation of cylinder constancy can be derived as a theorem from
`harmonic_measure_translation_on_deep_cylinder` (see
`harmonic_measure_one_cylinder_constant_depth1` below). -/

/-! #### Wave 35.5 D2/D3 — Cayley-distance computation for the meeting vertex

To dissolve the two `harmonic_measure_factor_at_meeting_vertex_*` admissions,
we need the explicit Cayley-graph distances between the starting vertices
and the meeting vertex `u = φ.valPrefix c`:

* `d(x, u) = |x| - c` (D2): the meeting vertex is on the geodesic `1 → x`,
  so `d(x, u) = d(1, x) - d(1, u) = |x| - c`. Proven below by the
  factorisation `x = (φ.valPrefix c) * mk(x.toWord.drop c)` (which holds
  because `x.toWord` agrees with `φ`'s first `c` letters).
* `d(1, u) = c` (D3): immediate from `(φ.valPrefix c).toWord.length = c`. -/

open private F2_cayley_dist_eq_toWord_length from EnsX2026.FreeGroup.RandomWalk

/-- **Wave 35.5 helper.** When `x.toWord` agrees with `φ.val` on the first
`c` letters and `c ≤ |x|`, the element `x` factorises as
`x = (φ.valPrefix c) * mk(x.toWord.drop c)`. -/
private lemma F2_eq_valPrefix_mul_drop (x : F2) (φ : F2_boundary) (c : ℕ)
    (hpm : PrefixMatches x φ c) :
    x = F2_boundary.valPrefix φ c * _root_.FreeGroup.mk (x.toWord.drop c) := by
  -- (a) (φ.valPrefix c).toWord = x.toWord.take c (both have length c and match φ's first c letters).
  have h_take_eq : x.toWord.take c = (F2_boundary.valPrefix φ c).toWord := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < c
    · have h1 : (x.toWord.take c)[i]? = some (φ.val i) := by
        rw [List.getElem?_take_of_lt hi]
        exact hpm.2 i hi
      have h2 : ((F2_boundary.valPrefix φ c).toWord)[i]? = some (φ.val i) :=
        F2_boundary.toWord_valPrefix_getElem? φ c i hi
      rw [h1, h2]
    · push_neg at hi
      have h1 : (x.toWord.take c)[i]? = none := by
        apply List.getElem?_eq_none
        rw [List.length_take]; omega
      have h2 : ((F2_boundary.valPrefix φ c).toWord)[i]? = none := by
        apply List.getElem?_eq_none
        rw [F2_boundary.length_toWord_valPrefix]; exact hi
      rw [h1, h2]
  -- (b) x = mk(x.toWord) = mk(take c ++ drop c) = mk(take c) * mk(drop c)
  --   = (φ.valPrefix c) * mk(x.toWord.drop c).
  have h_split : x.toWord = x.toWord.take c ++ x.toWord.drop c :=
    (List.take_append_drop c x.toWord).symm
  have h_take_mk : _root_.FreeGroup.mk (x.toWord.take c) = F2_boundary.valPrefix φ c := by
    rw [h_take_eq]
    exact _root_.FreeGroup.mk_toWord
  calc x = _root_.FreeGroup.mk x.toWord := _root_.FreeGroup.mk_toWord.symm
    _ = _root_.FreeGroup.mk (x.toWord.take c ++ x.toWord.drop c) := by rw [← h_split]
    _ = _root_.FreeGroup.mk (x.toWord.take c) * _root_.FreeGroup.mk (x.toWord.drop c) :=
          (FreeGroup.mul_mk).symm
    _ = F2_boundary.valPrefix φ c * _root_.FreeGroup.mk (x.toWord.drop c) := by
          rw [h_take_mk]

/-- **Wave 35.5 helper.** `mk` of a reduced infix of `x.toWord` has length
equal to the infix's length. Concretely for `x.toWord.drop c`: its length is
`|x| - c` and its `mk` reduces to itself. -/
private lemma toWord_length_mk_drop (x : F2) (c : ℕ) :
    (_root_.FreeGroup.mk (x.toWord.drop c)).toWord.length = x.toWord.length - c := by
  have h_red : _root_.FreeGroup.IsReduced (x.toWord.drop c) := by
    have h_red_x : _root_.FreeGroup.IsReduced x.toWord :=
      _root_.FreeGroup.isReduced_toWord
    -- drop c of a reduced list is an infix; use IsReduced.infix.
    refine h_red_x.infix ?_
    exact ⟨x.toWord.take c, [], by rw [List.append_nil]; exact List.take_append_drop c x.toWord⟩
  rw [_root_.FreeGroup.toWord_mk, h_red.reduce_eq]
  rw [List.length_drop]

/-- **Wave 35.5 helper — `d(x, φ.valPrefix c) = |x| - c` for `c ≤ |x|`.**
The proof uses the factorisation `x = (φ.valPrefix c) * mk(tail)` where
`tail = x.toWord.drop c` has length `|x| - c`. -/
private lemma F2_cayley_dist_to_meeting_vertex
    (x : F2) (φ : F2_boundary) (c : ℕ)
    (hc_le : c ≤ x.toWord.length)
    (hpm : PrefixMatches x φ c) :
    F2_cayley.dist x (F2_boundary.valPrefix φ c) = x.toWord.length - c := by
  rw [F2_cayley_dist_eq_toWord_length]
  -- Goal: (x⁻¹ * (φ.valPrefix c)).toWord.length = |x| - c.
  have h_factor : x = F2_boundary.valPrefix φ c * _root_.FreeGroup.mk (x.toWord.drop c) :=
    F2_eq_valPrefix_mul_drop x φ c hpm
  -- x⁻¹ * (φ.valPrefix c) = (mk(x.toWord.drop c))⁻¹.
  have h_inv : x⁻¹ * F2_boundary.valPrefix φ c
      = (_root_.FreeGroup.mk (x.toWord.drop c))⁻¹ := by
    have h_inv_factor : x⁻¹ = (_root_.FreeGroup.mk (x.toWord.drop c))⁻¹
        * (F2_boundary.valPrefix φ c)⁻¹ := by
      rw [← mul_inv_rev, ← h_factor]
    rw [h_inv_factor]
    group
  rw [h_inv]
  -- Inverse preserves toWord length.
  rw [_root_.FreeGroup.toWord_inv, _root_.FreeGroup.invRev_length]
  exact toWord_length_mk_drop x c

/-- **Wave 35.5 D2 — strong-Markov factorisation of `μ_x` through the
meeting vertex** (formerly axiom). The walk from `x` reaches
`u = φ.valPrefix c` with probability `3^{-d(x,u)} = 3^{-(|x|-c)}`, and
conditionally on `T_u < ∞` it continues as an SRW from `u`. Hence
`μ_x(I(φ, q)) = 3^{-(|x|-c)} · μ_u(I(φ, q))` for `q ≥ |x|`.

**Proof.** Combine:
* `harmonic_measure_cylinder_eq_walk_event` to translate harmonic measures
  to step-measures of cylinder events;
* Wave 35.3 Step 3.3 (`step_measure_cylinder_factor_meeting_vertex`) to
  factor the cylinder event through the meeting vertex via partition by
  hitting time;
* Wave 35.2b (`step_measure_T_u_at_lt_top`) to evaluate the hitting
  probability;
* `F2_cayley_dist_to_meeting_vertex` to convert `d(x, u)` to `|x| - c`. -/
theorem harmonic_measure_factor_at_meeting_vertex_x
    (x : F2) (φ : F2_boundary) (q : ℕ) (hq : x.toWord.length ≤ q) :
    harmonic_measure x (cylinder φ q)
      = ENNReal.ofReal
          ((3 : ℝ) ^ (-((x.toWord.length : ℤ) - common_prefix_length x φ)))
        * harmonic_measure (F2_boundary.valPrefix φ (common_prefix_length x φ))
            (cylinder φ q) := by
  set c : ℕ := common_prefix_length x φ with hc_def
  set u : F2 := F2_boundary.valPrefix φ c with hu_def
  -- Step 1: cylinder-to-walk reduction.
  rw [harmonic_measure_cylinder_eq_walk_event x φ q,
      harmonic_measure_cylinder_eq_walk_event u φ q]
  unfold walkPrefixEvent
  -- Step 2: factor through meeting vertex (Wave 35.3 Step 3.3).
  rw [step_measure_cylinder_factor_meeting_vertex x φ q hq]
  -- Step 3: evaluate hitting probability (Wave 35.2b).
  rw [show (F2_boundary.valPrefix φ (common_prefix_length x φ)) = u from rfl]
  rw [step_measure_T_u_at_lt_top x u]
  -- Step 4: identify `d(x, u) = |x| - c`.
  have hc_le : c ≤ x.toWord.length := BusemannLocal.common_prefix_length_le x φ
  have hpm : PrefixMatches x φ c := BusemannLocal.prefixMatches_common_prefix_length x φ
  have h_dist : F2_cayley.dist x u = x.toWord.length - c := by
    rw [hu_def]
    exact F2_cayley_dist_to_meeting_vertex x φ c hc_le hpm
  rw [h_dist]
  -- Step 5: convert ENNReal zpow to ofReal. Use the fact that the exponent
  -- `-((|x| - c : ℕ) : ℤ)` is the negation of a Nat cast.
  set n : ℕ := x.toWord.length - c with hn_def
  have h_n_cast : ((n : ℕ) : ℤ) = (x.toWord.length : ℤ) - c := by
    simp only [hn_def]; omega
  have h3_ne : (3 : ℝ) ≠ 0 := by norm_num
  -- Compute LHS: (3 : ENNReal) ^ (-(n : ℤ)) = ((3 : ENNReal) ^ n)⁻¹.
  have h_lhs : (3 : ENNReal) ^ (-((n : ℕ) : ℤ)) = ((3 : ENNReal) ^ n)⁻¹ := by
    rw [ENNReal.zpow_neg]; rw [zpow_natCast]
  -- Compute RHS: (3 : ℝ) ^ (-((|x|-c) : ℤ)) = ((3 : ℝ) ^ n)⁻¹.
  have h_rhs_real : (3 : ℝ) ^ (-((x.toWord.length : ℤ) - c)) = ((3 : ℝ) ^ n)⁻¹ := by
    rw [← h_n_cast, zpow_neg, zpow_natCast]
  rw [h_rhs_real, h_lhs]
  -- Now: ((3 : ENNReal) ^ n)⁻¹ = ENNReal.ofReal (((3 : ℝ) ^ n)⁻¹).
  rw [ENNReal.ofReal_inv_of_pos (pow_pos (by norm_num : (0 : ℝ) < 3) n)]
  rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 3)]
  -- ENNReal.ofReal 3 = (3 : ENNReal).
  congr 2
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) from by norm_num, ENNReal.ofReal_natCast]
  rfl

/-- **Wave 35.5 D3 — strong-Markov factorisation of `μ_1` through the
meeting vertex** (formerly axiom). The walk from `1` reaches the meeting
vertex `u = φ.valPrefix c` (with `c = c(x, φ)`) with probability
`3^{-d(1, u)} = 3^{-c}`, and conditionally on `T_u < ∞` continues as an SRW
from `u`. Hence `μ_1(I(φ, q)) = 3^{-c} · μ_u(I(φ, q))` for `q ≥ |x|`.

**Proof.** Combine:
* `harmonic_measure_cylinder_eq_walk_event` to translate harmonic measures
  to step-measures of cylinder events;
* `step_measure_cylinder_factor_at_depth` (Wave 35.5 generalised companion)
  with starting vertex `v = 1` and depth `d = c` (using `|1| = 0 ≤ c ≤ q`);
* Wave 35.2b (`step_measure_T_u_at_lt_top`) to evaluate the hitting
  probability `3^{-d(1, u)}`;
* `d(1, u) = u.toWord.length = c` (by `length_toWord_valPrefix`). -/
theorem harmonic_measure_factor_at_meeting_vertex_one
    (x : F2) (φ : F2_boundary) (q : ℕ) (hq : x.toWord.length ≤ q) :
    harmonic_measure 1 (cylinder φ q)
      = ENNReal.ofReal ((3 : ℝ) ^ (-(common_prefix_length x φ : ℤ)))
        * harmonic_measure (F2_boundary.valPrefix φ (common_prefix_length x φ))
            (cylinder φ q) := by
  set c : ℕ := common_prefix_length x φ with hc_def
  set u : F2 := F2_boundary.valPrefix φ c with hu_def
  have hc_le_x : c ≤ x.toWord.length := BusemannLocal.common_prefix_length_le x φ
  have hc_le_q : c ≤ q := le_trans hc_le_x hq
  -- |1| = 0 ≤ c (vacuous).
  have h_one_le : (1 : F2).toWord.length ≤ c := by
    rw [_root_.FreeGroup.toWord_one]; simp
  -- Step 1: cylinder-to-walk reduction (both sides).
  rw [harmonic_measure_cylinder_eq_walk_event 1 φ q,
      harmonic_measure_cylinder_eq_walk_event u φ q]
  unfold walkPrefixEvent
  -- Step 2: factor through meeting vertex (Wave 35.5 D1-companion at depth c).
  rw [step_measure_cylinder_factor_at_depth 1 φ q c hc_le_q h_one_le]
  -- Step 3: evaluate hitting probability (Wave 35.2b).
  rw [show (F2_boundary.valPrefix φ c) = u from rfl]
  rw [step_measure_T_u_at_lt_top 1 u]
  -- Step 4: identify `d(1, u) = c`.
  have h_dist : F2_cayley.dist 1 u = c := by
    rw [hu_def]
    rw [F2_cayley_dist_eq_toWord_length]
    rw [show (1 : F2)⁻¹ * F2_boundary.valPrefix φ c = F2_boundary.valPrefix φ c from by group]
    exact F2_boundary.length_toWord_valPrefix φ c
  rw [h_dist]
  -- Step 5: convert ENNReal zpow to ofReal (same pattern as D2).
  congr 1
  -- Compute LHS via ENNReal.zpow_neg.
  have h_lhs : (3 : ENNReal) ^ (-((c : ℕ) : ℤ)) = ((3 : ENNReal) ^ c)⁻¹ := by
    rw [ENNReal.zpow_neg]; rw [zpow_natCast]
  -- Compute RHS via zpow_neg in ℝ.
  have h_rhs_real : (3 : ℝ) ^ (-(c : ℤ)) = ((3 : ℝ) ^ c)⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  rw [h_rhs_real, h_lhs]
  rw [ENNReal.ofReal_inv_of_pos (pow_pos (by norm_num : (0 : ℝ) < 3) c)]
  rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 3)]
  congr 2
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) from by norm_num, ENNReal.ofReal_natCast]
  rfl

/-- **Wave 31-retry dissolution — deep-cylinder translation identity.**
Tree symmetry of the 4-regular Cayley graph yields the *constant*
translation identity for harmonic measure on **deep** cylinders.  For
every `x ∈ F_2`, every `φ ∈ ∂F_2`, and every `q ≥ |x|`,

  `μ_x(I(φ, q)) = poisson_kernel φ x · μ_1(I(φ, q))`

(at the real level, after `.toReal`).

Previously a single narrow admission; now a *theorem* (Wave 29-retry)
derived from two strictly more elementary, paper-citable strong-Markov
factorisations (`harmonic_measure_factor_at_meeting_vertex_x`,
 `harmonic_measure_factor_at_meeting_vertex_one`), themselves theorems
since Wave 35.5.

**Proof.** Let `c := common_prefix_length x φ` and `u := φ.valPrefix c`
be the meeting vertex of `x` and the φ-ray. The two factorisations give

* `μ_x(I(φ, q)) = 3^{-(|x|-c)} · μ_u(I(φ, q))`,
* `μ_1(I(φ, q)) = 3^{-c}      · μ_u(I(φ, q))`.

Convert to reals (both sides are finite) and divide. The `μ_u(I(φ, q))`
factor cancels, yielding
`μ_x.toReal / μ_1.toReal = 3^{-(|x|-c)} / 3^{-c} = 3^{-(|x|-2c)} = 3^{-b_φ(x)}
                         = poisson_kernel φ x`. -/
theorem harmonic_measure_translation_on_deep_cylinder
    (x : F2) (φ : F2_boundary) (q : ℕ) (hq : x.toWord.length ≤ q) :
    (harmonic_measure x (cylinder φ q)).toReal
      = poisson_kernel φ x * (harmonic_measure 1 (cylinder φ q)).toReal := by
  -- Notation
  set c : ℕ := common_prefix_length x φ with hc_def
  set u : F2 := F2_boundary.valPrefix φ c with hu_def
  -- Strong-Markov factorisations (Wave 35.5 theorems).
  have hX := harmonic_measure_factor_at_meeting_vertex_x x φ q hq
  have hO := harmonic_measure_factor_at_meeting_vertex_one x φ q hq
  -- Rewrite using c, u.
  rw [← hc_def, ← hu_def] at hX hO
  -- Real-valued shorthand for the auxiliary cylinder mass.
  set M : ENNReal := harmonic_measure u (cylinder φ q) with hM_def
  -- Pass to reals (all measures are finite, since `harmonic_measure _` is
  -- a probability measure).
  have hM_ne_top : M ≠ ⊤ :=
    MeasureTheory.measure_ne_top (harmonic_measure u) _
  have hX' :
      (harmonic_measure x (cylinder φ q)).toReal
        = (3 : ℝ) ^ (-((x.toWord.length : ℤ) - c)) * M.toReal := by
    have h_pos : (0 : ℝ) ≤ (3 : ℝ) ^ (-((x.toWord.length : ℤ) - c)) :=
      le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 3) _)
    rw [hX, ENNReal.toReal_mul, ENNReal.toReal_ofReal h_pos]
  have hO' :
      (harmonic_measure 1 (cylinder φ q)).toReal
        = (3 : ℝ) ^ (-(c : ℤ)) * M.toReal := by
    have h_pos : (0 : ℝ) ≤ (3 : ℝ) ^ (-(c : ℤ)) :=
      le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 3) _)
    rw [hO, ENNReal.toReal_mul, ENNReal.toReal_ofReal h_pos]
  -- Compute `poisson_kernel φ x = 3^{-(|x| - 2c)}` using `busemann φ x = |x| - 2c`.
  have h_pk : poisson_kernel φ x = (3 : ℝ) ^ (-((x.toWord.length : ℤ) - 2 * c)) := by
    unfold poisson_kernel busemann
    rw [← hc_def]
  -- Final algebra:
  --   μ_x.toReal = 3^{-(|x| - c)} · M.toReal
  --              = (3^{-(|x| - 2c)}) · (3^{-c} · M.toReal)
  --              = poisson_kernel φ x · μ_1.toReal.
  rw [hX', hO', h_pk]
  -- It remains to show:
  --   3^{-(|x| - c)} * M = 3^{-(|x| - 2c)} * (3^{-c} * M).
  have h3ne : (3 : ℝ) ≠ 0 := by norm_num
  have h_zpow : (3 : ℝ) ^ (-((x.toWord.length : ℤ) - c))
        = (3 : ℝ) ^ (-((x.toWord.length : ℤ) - 2 * c)) * (3 : ℝ) ^ (-(c : ℤ)) := by
    rw [← zpow_add₀ h3ne]
    congr 1
    ring
  rw [h_zpow]
  ring

/-! ### Wave 34-final — `harmonic_measure_one_cylinder_constant` fully dissolved

The previous **exam admission #3** ("the harmonic measure based at `1` of a
cylinder `I(φ, p)` does not depend on `φ`, only on `p`") is now a fully
proved theorem rather than an axiom.

The dissolution proceeds in two parts:
* The **depth-1 specialisation** (`harmonic_measure_one_cylinder_constant_depth1`,
  Wave 34 step 2) was derived from the deep-cylinder identity by direct
  computation of `μ_1(I(const ℓ, 1))` via the linear equation
  `1 = 3 x_m + (1/3)(1 - x_m)`.
* The **inductive step** (`SisterCylinderEq.harmonic_measure_sister_cylinder_eq`,
  Wave 34-final) establishes that within any depth-`p` cylinder, the three
  sister sub-cylinders at depth `p+1` have equal `μ_1`-mass. The argument
  uses the deep-cylinder identity at the depth-`(p+1)` sister vertices,
  Lemma C (sister harmonic measures agree on every cylinder outside
  `cylinder φ p`, by induction on cylinder depth), Lemma D (sister
  harmonic measures agree on `cylinder φ r` for all `r ≤ p`, by induction
  on `r` using the natural-letter splitting), and the algebraic identity
  `8·3^{p-1}(y_a - y_b) = 0`.

The full axiom is therefore replaced by `harmonic_measure_cylinder` (the
depth-`p` formula), which is now derived directly from the strong-Markov
factorisation axioms #3, #4 alone, with no further admission. -/

/-! #### Wave 25 Step 2 — direct proof of the cylinder formula

We prove `harmonic_measure_cylinder` by induction on `p`, using only
the new admission `harmonic_measure_one_cylinder_constant` (rotational
invariance of `μ_1` on cylinders).  The walk-prefix-event identity
`step_measure_walk_prefix_event_one` then follows as a corollary via
`harmonic_measure_cylinder_eq_walk_event`.

Strategy:

* **Base case `p = 1`:** the four cylinders of depth 1 — one per
  letter `ℓ : Fin 2 × Bool` — are pairwise disjoint and cover `univ`,
  so by σ-additivity they sum to `1`.  The admission says they all
  have the same measure, hence each equals `1/4`.

* **Inductive step `p → p+1`:** for `ψ ∈ cylinder φ p` with `p ≥ 1`,
  the next letter `ψ.val p` must non-cancel `φ.val (p-1) = ψ.val (p-1)`.
  There are exactly `3` such letters, giving a partition of
  `cylinder φ p` into `3` cylinders of depth `p+1`.  By the admission
  these cylinders all have the same measure, so each equals
  `(1/3) · μ_1(cylinder φ p)`.

The 3-letter partition uses `extendCylRep`, which extends a depth-`p`
prefix by a single new letter (filling the rest with that letter
constantly).  We also relocate `F2_boundary.const` to be available at
this point in the file (its previous home, after the Poisson-density
section, was downstream of these uses).
-/

/-- The constant boundary sequence `(ℓ, ℓ, ℓ, …)`.  Well-defined
because consecutive equal letters trivially satisfy the
`NonCancellation` predicate (`ℓ.2 = ℓ.2` is the second disjunct). -/
def F2_boundary.const (ℓ : Fin 2 × Bool) : F2_boundary :=
  ⟨fun _ => ℓ, fun _ => Or.inr rfl⟩

@[simp] lemma F2_boundary.const_val (ℓ : Fin 2 × Bool) (n : ℕ) :
    (F2_boundary.const ℓ).val n = ℓ := rfl

/-- `NonCancellation` is a decidable predicate.  Required for
`Finset.filter` over the boundary letters. -/
instance NonCancellation_decidable (a b : Fin 2 × Bool) :
    Decidable (NonCancellation a b) := by
  unfold NonCancellation
  exact instDecidableOr

/-- The set of letters that non-cancel a fixed letter `a`. -/
private def nonCancelExt (a : Fin 2 × Bool) : Finset (Fin 2 × Bool) :=
  (Finset.univ : Finset (Fin 2 × Bool)).filter (fun ℓ => NonCancellation a ℓ)

private lemma mem_nonCancelExt {a ℓ : Fin 2 × Bool} :
    ℓ ∈ nonCancelExt a ↔ NonCancellation a ℓ := by
  simp [nonCancelExt]

/-- Cardinality of the non-cancelling extensions: exactly `3`.
Concrete decidability via `decide` on the 4-element type. -/
private lemma nonCancelExt_card (a : Fin 2 × Bool) :
    (nonCancelExt a).card = 3 := by
  -- We compute by case analysis on `a` (4 cases), each by `decide`.
  rcases a with ⟨a₁, a₂⟩
  fin_cases a₁ <;> cases a₂ <;> decide

/-- **Step 2A — base partition.** The four cylinders
`cylinder (F2_boundary.const ℓ) 1` for `ℓ : Fin 2 × Bool` partition
`F2_boundary` (universe). -/
private lemma univ_eq_iUnion_cylinder_one :
    (⋃ ℓ : Fin 2 × Bool, cylinder (F2_boundary.const ℓ) 1) = Set.univ := by
  ext ψ
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  refine ⟨ψ.val 0, ?_⟩
  simp only [mem_cylinder, F2_boundary.const_val, Nat.lt_one_iff]
  intro i hi; subst hi; rfl

private lemma cylinder_one_disjoint :
    Pairwise (Function.onFun Disjoint
      (fun ℓ : Fin 2 × Bool => cylinder (F2_boundary.const ℓ) 1)) := by
  intro ℓ₁ ℓ₂ hne
  rw [Function.onFun, Set.disjoint_iff_inter_eq_empty]
  ext ψ
  simp only [mem_cylinder, F2_boundary.const_val, Nat.lt_one_iff,
    Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro h1 h2
  have h_ℓ₁ : ψ.val 0 = ℓ₁ := h1 0 rfl
  have h_ℓ₂ : ψ.val 0 = ℓ₂ := h2 0 rfl
  exact hne (h_ℓ₁.symm.trans h_ℓ₂)

/-- **Helper for the 3-fold partition.**  The "padded representative"
of a depth-`p` cylinder `φ` extended by letter `ℓ`: a boundary point
with letters `φ.val n` for `n < p` and `ℓ` thereafter.  Always
well-defined: at the boundary `n = p-1 → n = p`, we use `ℓ` if it
non-cancels `φ.val (p-1)` (else fall back to `φ.val (p-1)`); the rest
of the tail is `ℓ` so the constant tail trivially non-cancels itself. -/
private noncomputable def extendRep (φ : F2_boundary) (p : ℕ)
    (ℓ : Fin 2 × Bool) : F2_boundary :=
  ⟨fun n =>
    if n < p then φ.val n
    else if NonCancellation (φ.val (p - 1)) ℓ ∨ p = 0 then ℓ
    else φ.val (p - 1), by
    -- Prove NonCancellation between consecutive positions.
    intro n
    by_cases h₁ : n + 1 < p
    · -- Both n and n+1 < p: use φ.
      have h₀ : n < p := Nat.lt_of_succ_lt h₁
      simp only [if_pos h₀, if_pos h₁]
      exact φ.2 n
    · -- n + 1 ≥ p.
      simp only [if_neg h₁]
      by_cases h₀ : n < p
      · -- n < p and n+1 ≥ p, so n = p-1, p ≥ 1.
        simp only [if_pos h₀]
        have hp_pos : 1 ≤ p := Nat.lt_of_le_of_lt (Nat.zero_le _) h₀
        have h_eq : n = p - 1 := by omega
        subst h_eq
        by_cases h_nc : NonCancellation (φ.val (p - 1)) ℓ
        · have h_or : NonCancellation (φ.val (p - 1)) ℓ ∨ p = 0 := Or.inl h_nc
          simp only [if_pos h_or]
          exact h_nc
        · have h_p_ne : p ≠ 0 := Nat.one_le_iff_ne_zero.mp hp_pos
          have h_or_neg : ¬ (NonCancellation (φ.val (p - 1)) ℓ ∨ p = 0) :=
            fun h => h.elim h_nc h_p_ne
          simp only [if_neg h_or_neg]
          exact Or.inr rfl
      · -- Both n, n+1 ≥ p: constant tail (or recovery branch).
        simp only [if_neg h₀]
        -- Goal is NonCancellation (extendRep tail) (extendRep tail).
        -- The tail is constant: either ℓ (if h_or) or φ.val (p-1) (else).
        -- In both cases, NonCancellation x x = Or.inr rfl.
        by_cases h_or : NonCancellation (φ.val (p - 1)) ℓ ∨ p = 0
        · simp only [if_pos h_or]; exact Or.inr rfl
        · simp only [if_neg h_or]; exact Or.inr rfl⟩

private lemma extendRep_val_lt {φ : F2_boundary} {p : ℕ}
    {ℓ : Fin 2 × Bool} {n : ℕ} (hn : n < p) :
    (extendRep φ p ℓ).val n = φ.val n := by
  simp [extendRep, hn]

private lemma extendRep_val_p {φ : F2_boundary} {p : ℕ}
    {ℓ : Fin 2 × Bool} (hp : 1 ≤ p)
    (h_nc : NonCancellation (φ.val (p - 1)) ℓ) :
    (extendRep φ p ℓ).val p = ℓ := by
  have h_or : NonCancellation (φ.val (p - 1)) ℓ ∨ p = 0 := Or.inl h_nc
  simp [extendRep, Nat.lt_irrefl, h_or]

/-- **Step 2B — depth-`p+1` partition of a depth-`p` cylinder.**
For `p ≥ 1`, the cylinder `cylinder φ p` decomposes as the disjoint
union over the three non-cancelling extensions `ℓ` of `φ.val (p-1)`,
of cylinders of depth `p+1` with the corresponding extended
representative `extendRep φ p ℓ`. -/
private lemma cylinder_eq_iUnion_extend (φ : F2_boundary) (p : ℕ)
    (hp : 1 ≤ p) :
    cylinder φ p = ⋃ ℓ ∈ nonCancelExt (φ.val (p - 1)),
      cylinder (extendRep φ p ℓ) (p + 1) := by
  ext ψ
  constructor
  · intro hψ
    simp only [Set.mem_iUnion]
    refine ⟨ψ.val p, ?_, ?_⟩
    · -- ψ.val p ∈ nonCancelExt (φ.val (p-1)).
      rw [mem_nonCancelExt]
      have h_eq : ψ.val (p - 1) = φ.val (p - 1) := by
        rw [mem_cylinder] at hψ
        exact hψ (p - 1) (by omega)
      rw [← h_eq]
      have hp_eq : p - 1 + 1 = p := by omega
      have hψ_nc := ψ.2 (p - 1)
      rw [hp_eq] at hψ_nc
      exact hψ_nc
    · -- ψ ∈ cylinder (extendRep ...) (p + 1).
      -- We need that `ψ.val p` non-cancels `φ.val (p-1)`.
      have h_nc : NonCancellation (φ.val (p - 1)) (ψ.val p) := by
        have h_eq : ψ.val (p - 1) = φ.val (p - 1) := by
          rw [mem_cylinder] at hψ
          exact hψ (p - 1) (by omega)
        rw [← h_eq]
        have hp_eq : p - 1 + 1 = p := by omega
        have hψ_nc := ψ.2 (p - 1)
        rw [hp_eq] at hψ_nc
        exact hψ_nc
      rw [mem_cylinder] at hψ ⊢
      intro i hi
      by_cases hi_lt : i < p
      · rw [extendRep_val_lt hi_lt]
        exact hψ i hi_lt
      · -- i = p.
        have hi_eq : i = p := by omega
        subst hi_eq
        rw [extendRep_val_p hp h_nc]
  · intro hψ
    simp only [Set.mem_iUnion] at hψ
    obtain ⟨ℓ, hℓ, hψ_in⟩ := hψ
    rw [mem_cylinder] at hψ_in ⊢
    intro i hi
    have hi_lt : i < p + 1 := Nat.lt_succ_of_lt hi
    have h_match := hψ_in i hi_lt
    rw [extendRep_val_lt hi] at h_match
    exact h_match

/-- The cylinders in the depth-`p+1` partition are pairwise disjoint. -/
private lemma cylinder_extend_pairwise_disjoint (φ : F2_boundary) (p : ℕ)
    (hp : 1 ≤ p) :
    (nonCancelExt (φ.val (p - 1)) : Set (Fin 2 × Bool)).PairwiseDisjoint
      (fun ℓ : Fin 2 × Bool => cylinder (extendRep φ p ℓ) (p + 1)) := by
  intro ℓ₁ hℓ₁ ℓ₂ hℓ₂ hne
  rw [Function.onFun, Set.disjoint_iff_inter_eq_empty]
  -- Extract the non-cancellation witnesses.
  have h_nc₁ : NonCancellation (φ.val (p - 1)) ℓ₁ := mem_nonCancelExt.mp hℓ₁
  have h_nc₂ : NonCancellation (φ.val (p - 1)) ℓ₂ := mem_nonCancelExt.mp hℓ₂
  ext ψ
  simp only [Set.mem_inter_iff, mem_cylinder, Set.mem_empty_iff_false,
    iff_false, not_and]
  intro h1 h2
  have hp_lt : p < p + 1 := Nat.lt_succ_self _
  have h_ℓ₁ : ψ.val p = ℓ₁ := by
    have := h1 p hp_lt
    rwa [extendRep_val_p hp h_nc₁] at this
  have h_ℓ₂ : ψ.val p = ℓ₂ := by
    have := h2 p hp_lt
    rwa [extendRep_val_p hp h_nc₂] at this
  exact hne (h_ℓ₁.symm.trans h_ℓ₂)

/-! #### Wave 34 — depth-1 dissolution of cylinder constancy

For `p = 1`, the cylinder constancy axiom can be **proved** as a
theorem from `harmonic_measure_translation_on_deep_cylinder` (itself
a theorem since Wave 29-retry, with its strong-Markov leaves
`harmonic_measure_factor_at_meeting_vertex_*` dissolved in Wave 35.5).
The argument is the user's depth-1 derivation:

* Pick a generator `g_m := FreeGroup.mk [m]` for some letter `m`.
* Apply the deep-cylinder identity at `(x = g_m, q = 1)`: for every
  letter `m'`,
  `μ_{g_m}(I(const m', 1)).toReal
     = poisson_kernel(const m', g_m) · μ_1(I(const m', 1)).toReal`
  with kernel `3` if `m = m'` and `1/3` otherwise (since
  `c(g_m, const m') ∈ {0, 1}`).
* Sum over the four letters and use that `μ_{g_m}(univ) = 1` and
  the four depth-1 cylinders partition `∂F_2`. Solve the resulting
  linear equation `1 = 3 x_m + (1/3)(1 - x_m)` to obtain
  `x_m = μ_1(I(const m, 1)).toReal = 1/4`.
* Constancy at depth 1 follows since the value is the same constant
  `1/4` for every letter `m`. -/

/-- The F2 element corresponding to a single boundary letter `ℓ`,
realised as the depth-1 prefix of the constant boundary `F2_boundary.const ℓ`. -/
private lemma valPrefix_const_one (ℓ : Fin 2 × Bool) :
    F2_boundary.valPrefix (F2_boundary.const ℓ) 1 = _root_.FreeGroup.mk [ℓ] := by
  unfold F2_boundary.valPrefix
  show _root_.FreeGroup.mk (F2_boundary.prefixList (F2_boundary.const ℓ) 1)
        = _root_.FreeGroup.mk [ℓ]
  simp [F2_boundary.prefixList, List.range, List.range.loop, F2_boundary.const_val]

/-- The reduced word of `FreeGroup.mk [ℓ]` is `[ℓ]` (a single-letter
list is already reduced). -/
private lemma toWord_mk_letter (ℓ : Fin 2 × Bool) :
    (_root_.FreeGroup.mk [ℓ]).toWord = [ℓ] := by
  rw [_root_.FreeGroup.toWord_mk]
  have h_red : _root_.FreeGroup.IsReduced [ℓ] := by
    rw [_root_.FreeGroup.IsReduced]
    exact List.IsChain.singleton _
  exact h_red.reduce_eq

/-- `(FreeGroup.mk [ℓ]).toWord.length = 1`. -/
private lemma length_toWord_mk_letter (ℓ : Fin 2 × Bool) :
    (_root_.FreeGroup.mk [ℓ]).toWord.length = 1 := by
  rw [toWord_mk_letter]; rfl

/-- For matching letters `m`, the common prefix length of `FreeGroup.mk [m]`
with `F2_boundary.const m` is `1`. -/
private lemma common_prefix_length_mk_letter_const_eq
    (m : Fin 2 × Bool) :
    common_prefix_length (_root_.FreeGroup.mk [m]) (F2_boundary.const m) = 1 := by
  rw [← valPrefix_const_one m]
  exact common_prefix_length_valPrefix_self (F2_boundary.const m) 1

/-- For distinct letters `m ≠ m'`, the common prefix length of
`FreeGroup.mk [m]` with `F2_boundary.const m'` is `0`. -/
private lemma common_prefix_length_mk_letter_const_ne
    (m m' : Fin 2 × Bool) (hne : m ≠ m') :
    common_prefix_length (_root_.FreeGroup.mk [m]) (F2_boundary.const m') = 0 := by
  rw [← valPrefix_const_one m]
  refine common_prefix_length_valPrefix_other (F2_boundary.const m')
    (F2_boundary.const m) 0 ?_ ?_ ?_
  · intro i hi; exact absurd hi (Nat.not_lt_zero i)
  · simp [F2_boundary.const_val]; exact hne
  · exact le_refl _

/-- Poisson kernel at the depth-1 vertex `FreeGroup.mk [m]` evaluated on
the constant boundary `F2_boundary.const m`: equals `3`. -/
private lemma poisson_kernel_mk_letter_const_eq (m : Fin 2 × Bool) :
    poisson_kernel (F2_boundary.const m) (_root_.FreeGroup.mk [m]) = 3 := by
  unfold poisson_kernel busemann
  rw [length_toWord_mk_letter, common_prefix_length_mk_letter_const_eq]
  -- Goal: (3 : ℝ)^(-(1 - 2*1 : ℤ)) = 3.
  norm_num

/-- Poisson kernel at the depth-1 vertex `FreeGroup.mk [m]` evaluated on
a *different* constant boundary `F2_boundary.const m'`: equals `1/3`. -/
private lemma poisson_kernel_mk_letter_const_ne
    (m m' : Fin 2 × Bool) (hne : m ≠ m') :
    poisson_kernel (F2_boundary.const m') (_root_.FreeGroup.mk [m]) = 1 / 3 := by
  unfold poisson_kernel busemann
  rw [length_toWord_mk_letter, common_prefix_length_mk_letter_const_ne m m' hne]
  -- Goal: (3 : ℝ)^(-(1 - 2*0 : ℤ)) = 1/3.
  norm_num

/-- Total mass of `μ_{g_m}` decomposed over the four depth-1 cylinders. -/
private lemma harmonic_measure_mk_letter_sum_cylinders (m : Fin 2 × Bool) :
    (∑ m' : (Fin 2 × Bool),
        harmonic_measure (_root_.FreeGroup.mk [m])
          (cylinder (F2_boundary.const m') 1))
      = 1 := by
  have h_disj := cylinder_one_disjoint
  have h_meas : ∀ m' : Fin 2 × Bool,
      MeasurableSet (cylinder (F2_boundary.const m') 1) :=
    fun m' => cylinder_measurable _ _
  have h_sum_total :
      (∑ m' : (Fin 2 × Bool),
          harmonic_measure (_root_.FreeGroup.mk [m])
            (cylinder (F2_boundary.const m') 1))
        = harmonic_measure (_root_.FreeGroup.mk [m]) Set.univ := by
    rw [← univ_eq_iUnion_cylinder_one]
    rw [MeasureTheory.measure_iUnion h_disj h_meas, tsum_fintype]
  rw [h_sum_total]
  exact (harmonic_measure_isProbabilityMeasure _).measure_univ

/-- **Wave 34 — depth-1 cylinder formula (constancy as a corollary).**
For every letter `m : Fin 2 × Bool`,
`μ_1(I(F2_boundary.const m, 1)).toReal = 1/4`.

This is the user's depth-1 derivation: apply the deep-cylinder identity
at `(x = FreeGroup.mk [m], q = 1)`, sum over the four letters,
and solve the linear equation `1 = (8/3) x_m + 1/3`. -/
private lemma harmonic_measure_one_const_cylinder_one_toReal
    (m : Fin 2 × Bool) :
    (harmonic_measure 1 (cylinder (F2_boundary.const m) 1)).toReal = 1 / 4 := by
  -- Set notation.
  set g_m : F2 := _root_.FreeGroup.mk [m] with hg_def
  -- Real-valued unknowns: `x m' := μ_1(I(const m', 1)).toReal`.
  set x : (Fin 2 × Bool) → ℝ :=
    fun m' => (harmonic_measure 1 (cylinder (F2_boundary.const m') 1)).toReal
    with hx_def
  -- Step A: deep-cylinder identity at (x = g_m, q = 1) for each m'.
  have hg_len : g_m.toWord.length = 1 := length_toWord_mk_letter m
  have h_deep : ∀ m' : Fin 2 × Bool,
      (harmonic_measure g_m (cylinder (F2_boundary.const m') 1)).toReal
        = poisson_kernel (F2_boundary.const m') g_m * x m' := by
    intro m'
    have hq : g_m.toWord.length ≤ 1 := by rw [hg_len]
    have := harmonic_measure_translation_on_deep_cylinder g_m
      (F2_boundary.const m') 1 hq
    simpa [hx_def] using this
  -- Step B: total mass at g_m is 1.
  have h_total : ∑ m' : (Fin 2 × Bool),
      (harmonic_measure g_m (cylinder (F2_boundary.const m') 1)).toReal = 1 := by
    have h_total_ENN := harmonic_measure_mk_letter_sum_cylinders m
    have h_finite : ∀ m' : (Fin 2 × Bool),
        harmonic_measure g_m (cylinder (F2_boundary.const m') 1) ≠ ⊤ := by
      intro m'
      exact MeasureTheory.measure_ne_top _ _
    have :
        (∑ m' : (Fin 2 × Bool),
          (harmonic_measure g_m (cylinder (F2_boundary.const m') 1)).toReal)
          = ((∑ m' : (Fin 2 × Bool),
            harmonic_measure g_m (cylinder (F2_boundary.const m') 1)) : ENNReal).toReal := by
      rw [ENNReal.toReal_sum (fun m' _ => h_finite m')]
    rw [this, h_total_ENN]
    simp
  -- Step C: rewrite total via deep-cylinder identity.
  have h_rewrite : ∑ m' : (Fin 2 × Bool),
      poisson_kernel (F2_boundary.const m') g_m * x m' = 1 := by
    rw [← h_total]
    exact Finset.sum_congr rfl (fun m' _ => (h_deep m').symm)
  -- Step D: split the sum into the m' = m term and the rest.
  have h_split :
      (∑ m' : (Fin 2 × Bool),
          poisson_kernel (F2_boundary.const m') g_m * x m')
        = poisson_kernel (F2_boundary.const m) g_m * x m
          + ∑ m' ∈ (Finset.univ : Finset (Fin 2 × Bool)) \ {m},
              poisson_kernel (F2_boundary.const m') g_m * x m' := by
    rw [Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ m)]
    ring
  -- Compute kernel values:
  have h_ker_eq := poisson_kernel_mk_letter_const_eq m
  have h_ker_ne : ∀ m' : Fin 2 × Bool, m' ∈ Finset.univ \ ({m} : Finset _) →
      poisson_kernel (F2_boundary.const m') g_m = 1 / 3 := by
    intro m' hm'
    have h_ne : m' ≠ m := by
      intro h
      simp [h] at hm'
    exact poisson_kernel_mk_letter_const_ne m m' (Ne.symm h_ne)
  rw [h_split, h_ker_eq] at h_rewrite
  -- Now: 3 * x m + Σ_{m' ≠ m} (1/3) * x m' = 1.
  -- Equivalently: 3 * x m + (1/3) * Σ_{m' ≠ m} x m' = 1.
  have h_factor :
      (∑ m' ∈ (Finset.univ : Finset (Fin 2 × Bool)) \ {m},
          poisson_kernel (F2_boundary.const m') g_m * x m')
        = (1/3 : ℝ) * ∑ m' ∈ (Finset.univ : Finset (Fin 2 × Bool)) \ {m}, x m' := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m' hm'
    rw [h_ker_ne m' hm']
  rw [h_factor] at h_rewrite
  -- Now compute Σ_{m' ≠ m} x m' = (Σ_{m'} x m') - x m, and Σ_{m'} x m' = 1.
  have h_sum_x : (∑ m' : (Fin 2 × Bool), x m') = 1 := by
    -- This is `μ_1(univ).toReal`.
    have h_disj := cylinder_one_disjoint
    have h_meas : ∀ m' : Fin 2 × Bool,
        MeasurableSet (cylinder (F2_boundary.const m') 1) :=
      fun m' => cylinder_measurable _ _
    have h_finite : ∀ m' : (Fin 2 × Bool),
        harmonic_measure 1 (cylinder (F2_boundary.const m') 1) ≠ ⊤ := by
      intro m'
      exact MeasureTheory.measure_ne_top _ _
    have h_sum_total :
        (∑ m' : (Fin 2 × Bool),
            harmonic_measure 1 (cylinder (F2_boundary.const m') 1))
          = harmonic_measure 1 Set.univ := by
      rw [← univ_eq_iUnion_cylinder_one]
      rw [MeasureTheory.measure_iUnion h_disj h_meas, tsum_fintype]
    have h_univ : harmonic_measure 1 (Set.univ : Set F2_boundary) = 1 :=
      (harmonic_measure_isProbabilityMeasure 1).measure_univ
    have h_total_ENN :
        (∑ m' : (Fin 2 × Bool),
            harmonic_measure 1 (cylinder (F2_boundary.const m') 1))
          = 1 := h_sum_total.trans h_univ
    have :
        (∑ m' : (Fin 2 × Bool), x m')
          = ((∑ m' : (Fin 2 × Bool),
            harmonic_measure 1 (cylinder (F2_boundary.const m') 1)) : ENNReal).toReal := by
      rw [ENNReal.toReal_sum (fun m' _ => h_finite m')]
    rw [this, h_total_ENN]
    simp
  have h_sum_diff :
      (∑ m' ∈ (Finset.univ : Finset (Fin 2 × Bool)) \ {m}, x m')
        = (∑ m' : (Fin 2 × Bool), x m') - x m := by
    rw [Finset.sum_sdiff_eq_sub (by simp : ({m} : Finset _) ⊆ Finset.univ),
      Finset.sum_singleton]
  rw [h_sum_diff, h_sum_x] at h_rewrite
  -- h_rewrite : 3 * x m + (1/3) * (1 - x m) = 1.
  -- Solve: x m = 1/4.
  linarith

/-- **Wave 34 — depth-1 specialisation of `harmonic_measure_one_cylinder_constant`.**
For every two boundary points `φ ψ`, `μ_1(I(φ, 1)) = μ_1(I(ψ, 1))`.

Now a *theorem*, not an axiom: derived from
`harmonic_measure_one_const_cylinder_one_toReal` (each depth-1 cylinder
has `μ_1`-mass `ENNReal.ofReal (1/4)`). -/
theorem harmonic_measure_one_cylinder_constant_depth1
    (φ ψ : F2_boundary) :
    harmonic_measure 1 (cylinder φ 1) = harmonic_measure 1 (cylinder ψ 1) := by
  -- Reduce both cylinders to `cylinder (F2_boundary.const _) 1` using the
  -- only-first-letter-matters fact.
  have h_φ : cylinder φ 1 = cylinder (F2_boundary.const (φ.val 0)) 1 := by
    ext χ
    simp [mem_cylinder, F2_boundary.const_val, Nat.lt_one_iff]
  have h_ψ : cylinder ψ 1 = cylinder (F2_boundary.const (ψ.val 0)) 1 := by
    ext χ
    simp [mem_cylinder, F2_boundary.const_val, Nat.lt_one_iff]
  rw [h_φ, h_ψ]
  -- Both depth-1 cylinders (constant) have measure ofReal(1/4) by the
  -- previous lemma.
  have h_ne_top : ∀ m : Fin 2 × Bool,
      harmonic_measure 1 (cylinder (F2_boundary.const m) 1) ≠ ⊤ :=
    fun m => MeasureTheory.measure_ne_top _ _
  have h_eq_φ :
      harmonic_measure 1 (cylinder (F2_boundary.const (φ.val 0)) 1)
        = ENNReal.ofReal (1/4) := by
    rw [← harmonic_measure_one_const_cylinder_one_toReal (φ.val 0)]
    rw [ENNReal.ofReal_toReal (h_ne_top _)]
  have h_eq_ψ :
      harmonic_measure 1 (cylinder (F2_boundary.const (ψ.val 0)) 1)
        = ENNReal.ofReal (1/4) := by
    rw [← harmonic_measure_one_const_cylinder_one_toReal (ψ.val 0)]
    rw [ENNReal.ofReal_toReal (h_ne_top _)]
  rw [h_eq_φ, h_eq_ψ]

/-! #### Wave 34-final — inductive step (sister cylinder equality)

For `p ≥ 1`, fix a boundary `φ` and consider the depth-`(p+1)` partition of
`cylinder φ p` into the three sister cylinders `cylinder (extendRep φ p ℓ) (p+1)`
indexed by `ℓ ∈ nonCancelExt(φ.val (p-1))`. We prove that the three sisters
have *equal* harmonic-measure mass under `μ_1`, by the Busemann-subtraction
argument:

* The depth-`(p+1)` vertex `ψ_ℓ := (extendRep φ p ℓ).valPrefix(p+1)` lies on
  the sister ray `ℓ`.
* For any boundary `ρ ∉ cylinder φ p`, the common-prefix-length
  `c(ψ_ℓ, ρ) = first_disagreement(φ, ρ) < p` is independent of `ℓ`. Hence
  `poisson_kernel ρ ψ_ℓ` is independent of `ℓ`.
* By the deep-cylinder identity at `(ψ_ℓ, q = p+1)` and σ-additivity over
  *any* finite-cylinder partition of `univ \ cylinder φ p` into depth-
  `(p+1)` sub-cylinders (refinement of the natural sibling decomposition),
  the complement mass `μ_{ψ_ℓ}(univ \ cylinder φ p)` is independent of `ℓ`.
* By total mass `1`, `μ_{ψ_ℓ}(cylinder φ p)` is also independent of `ℓ`.
* The deep-cylinder identity inside `cylinder φ p` gives
  `μ_{ψ_a}(cylinder φ p).toReal = 8·3^{p-1} · y_a + 3^{p-1} · S` (with
  `S = y_a + y_b + y_c`). Subtracting for two sisters yields
  `8·3^{p-1}(y_a - y_b) = 0`, hence sister equality.

The proof proceeds via: (i) kernel-equality outside (Lemma A), (ii)
sister-mass equality on cylinders outside `cylinder φ p` (Lemma B, by
induction on cylinder depth using the sub-cylinder decomposition), (iii)
sister-mass equality on the complement (Lemma C, σ-additivity on the
finite sibling decomposition), and (iv) the headline theorem via linear
algebra (Theorem D). -/

namespace SisterCylinderEq

/-- The sister vertex on the depth-`(p+1)` ray indexed by `ℓ`. -/
private noncomputable def sisterVertex (φ : F2_boundary) (p : ℕ)
    (ℓ : Fin 2 × Bool) : F2 :=
  F2_boundary.valPrefix (extendRep φ p ℓ) (p + 1)

private lemma sisterVertex_length (φ : F2_boundary) (p : ℕ)
    (ℓ : Fin 2 × Bool) :
    (sisterVertex φ p ℓ).toWord.length = p + 1 := by
  unfold sisterVertex
  exact F2_boundary.length_toWord_valPrefix _ _

/-- The reduced word of the sister vertex agrees with `φ` on the first `p`
positions. -/
private lemma sisterVertex_toWord_match_phi (φ : F2_boundary) (p : ℕ) (hp : 1 ≤ p)
    (ℓ : Fin 2 × Bool) (h_nc : NonCancellation (φ.val (p - 1)) ℓ)
    (i : ℕ) (hi : i < p) :
    (sisterVertex φ p ℓ).toWord[i]? = some (φ.val i) := by
  unfold sisterVertex
  rw [F2_boundary.toWord_valPrefix_getElem? _ _ _ (Nat.lt_succ_of_lt hi)]
  rw [extendRep_val_lt hi]

/-- The letter at position `p` of the sister vertex's word is `ℓ`. -/
private lemma sisterVertex_toWord_at_p (φ : F2_boundary) (p : ℕ) (hp : 1 ≤ p)
    (ℓ : Fin 2 × Bool) (h_nc : NonCancellation (φ.val (p - 1)) ℓ) :
    (sisterVertex φ p ℓ).toWord[p]? = some ℓ := by
  unfold sisterVertex
  rw [F2_boundary.toWord_valPrefix_getElem? _ _ _ (Nat.lt_succ_self _)]
  rw [extendRep_val_p hp h_nc]

/-- **Lemma A — common-prefix-length equality outside `cylinder φ p`.**
For any `ρ ∉ cylinder φ p`, the common-prefix-length of the sister vertex
with `ρ` equals the smallest index `r < p` at which `ρ` and `φ` disagree —
in particular, this value depends only on `(ρ, φ, p)` and is independent
of which sister `ℓ` we picked. -/
private lemma common_prefix_length_sister_outside
    (φ : F2_boundary) (p : ℕ) (hp : 1 ≤ p)
    (ℓ : Fin 2 × Bool) (h_nc : NonCancellation (φ.val (p - 1)) ℓ)
    (ρ : F2_boundary) (h_ρ_outside : ρ ∉ cylinder φ p) :
    common_prefix_length (sisterVertex φ p ℓ) ρ
      = Nat.find (p := fun i => i < p ∧ ρ.val i ≠ φ.val i)
          (by
            rw [mem_cylinder] at h_ρ_outside
            push_neg at h_ρ_outside
            obtain ⟨i, hi, hne⟩ := h_ρ_outside
            exact ⟨i, hi, hne⟩) := by
  classical
  rw [mem_cylinder] at h_ρ_outside
  push_neg at h_ρ_outside
  obtain ⟨i_disagree, hi_lt, hi_ne⟩ := h_ρ_outside
  set hExists : ∃ i, i < p ∧ ρ.val i ≠ φ.val i := ⟨i_disagree, hi_lt, hi_ne⟩
  set r := Nat.find hExists with hr_def
  have hr_in := Nat.find_spec hExists
  obtain ⟨hr_lt, hr_ne⟩ := hr_in
  have hr_min : ∀ j, j < r → ¬ (j < p ∧ ρ.val j ≠ φ.val j) :=
    fun j hj => Nat.find_min hExists hj
  -- Now compute `common_prefix_length (sisterVertex φ p ℓ) ρ = r`.
  unfold common_prefix_length
  rw [sisterVertex_length φ p ℓ]
  rw [Nat.findGreatest_eq_iff]
  refine ⟨?_, ?_, ?_⟩
  · -- r ≤ p + 1
    omega
  · -- r ≠ 0 → PrefixMatches (sisterVertex ...) ρ r
    intro _
    refine ⟨?_, ?_⟩
    · rw [sisterVertex_length]
      omega
    · intro j hj
      have hjp : j < p := lt_of_lt_of_le hj (Nat.le_of_lt hr_lt)
      have h_match := sisterVertex_toWord_match_phi φ p hp ℓ h_nc j hjp
      rw [h_match]
      -- Goal: some (φ.val j) = some (ρ.val j).
      have hj_notS : ¬ (j < p ∧ ρ.val j ≠ φ.val j) := hr_min j hj
      push_neg at hj_notS
      have h_eq : ρ.val j = φ.val j := hj_notS hjp
      rw [h_eq]
  · -- For n with r < n ≤ p+1, ¬ PrefixMatches (sisterVertex ...) ρ n.
    intro n hrn _hnp hP
    obtain ⟨_hle, hmatch⟩ := hP
    have hr_lt_n : r < n := hrn
    have hword_at_r := sisterVertex_toWord_match_phi φ p hp ℓ h_nc r hr_lt
    have hmatch_r := hmatch r hr_lt_n
    have h_some : some (φ.val r) = some (ρ.val r) :=
      hword_at_r.symm.trans hmatch_r
    have h_eq : φ.val r = ρ.val r := Option.some_injective _ h_some
    exact hr_ne h_eq.symm

/-- **Lemma B — kernel equality outside `cylinder φ p`.** For two sister
extensions `ℓ_a, ℓ_b` and any `ρ ∉ cylinder φ p`, the Poisson kernels at
the sister vertices coincide. -/
private lemma poisson_kernel_sister_eq_outside
    (φ : F2_boundary) (p : ℕ) (hp : 1 ≤ p)
    (ℓ_a ℓ_b : Fin 2 × Bool)
    (h_nc_a : NonCancellation (φ.val (p - 1)) ℓ_a)
    (h_nc_b : NonCancellation (φ.val (p - 1)) ℓ_b)
    (ρ : F2_boundary) (h_ρ_outside : ρ ∉ cylinder φ p) :
    poisson_kernel ρ (sisterVertex φ p ℓ_a)
      = poisson_kernel ρ (sisterVertex φ p ℓ_b) := by
  have hr_a := common_prefix_length_sister_outside φ p hp ℓ_a h_nc_a ρ h_ρ_outside
  have hr_b := common_prefix_length_sister_outside φ p hp ℓ_b h_nc_b ρ h_ρ_outside
  -- The RHS of both is the same `Nat.find`, so the common-prefix-lengths
  -- agree.
  have h_cpl : common_prefix_length (sisterVertex φ p ℓ_a) ρ
              = common_prefix_length (sisterVertex φ p ℓ_b) ρ := by
    rw [hr_a, hr_b]
  -- Now compute the Poisson kernels.
  unfold poisson_kernel busemann
  rw [sisterVertex_length, sisterVertex_length, h_cpl]

/-- **Lemma C — sister harmonic measure equality on outside cylinders.**
For any cylinder `cylinder ρ q` whose first `q` letters disagree with `φ`
somewhere within the first `p` positions (so `cylinder ρ q ⊆ univ \ cylinder φ p`),
the harmonic measures from the two sister vertices coincide.

Proof: induction on the gap `(p+1) - q` via `Nat.le_induction` going *downward*
on `q` (started from `q = p + 1` where deep-cylinder applies, and showing
that the value at `q` follows from the value at `q + 1` via 3-fold
sub-cylinder decomposition). -/
private lemma sister_harmonic_eq_on_outside
    (φ : F2_boundary) (p : ℕ) (hp : 1 ≤ p)
    (ℓ_a ℓ_b : Fin 2 × Bool)
    (h_nc_a : NonCancellation (φ.val (p - 1)) ℓ_a)
    (h_nc_b : NonCancellation (φ.val (p - 1)) ℓ_b) :
    ∀ (gap : ℕ) (q : ℕ) (_ : q + gap = p + 1) (_ : 1 ≤ q),
      ∀ (ρ : F2_boundary) (r : ℕ) (_ : r < p) (_ : r < q)
        (_ : ρ.val r ≠ φ.val r),
      harmonic_measure (sisterVertex φ p ℓ_a) (cylinder ρ q)
        = harmonic_measure (sisterVertex φ p ℓ_b) (cylinder ρ q) := by
  intro gap
  induction gap with
  | zero =>
    -- gap = 0: q = p + 1 (deep-cylinder applies directly).
    intro q hq_eq _hq_pos ρ r hrp hrq h_ne
    have hq : q = p + 1 := by omega
    subst hq
    -- ρ ∉ cylinder φ p (witness: r < p with disagreement).
    have h_ρ_outside : ρ ∉ cylinder φ p := by
      rw [mem_cylinder]; push_neg; exact ⟨r, hrp, h_ne⟩
    have h_len_a : (sisterVertex φ p ℓ_a).toWord.length ≤ p + 1 := by
      rw [sisterVertex_length]
    have h_len_b : (sisterVertex φ p ℓ_b).toWord.length ≤ p + 1 := by
      rw [sisterVertex_length]
    have h_dc_a := harmonic_measure_translation_on_deep_cylinder
      (sisterVertex φ p ℓ_a) ρ (p + 1) h_len_a
    have h_dc_b := harmonic_measure_translation_on_deep_cylinder
      (sisterVertex φ p ℓ_b) ρ (p + 1) h_len_b
    have h_ker := poisson_kernel_sister_eq_outside φ p hp ℓ_a ℓ_b
      h_nc_a h_nc_b ρ h_ρ_outside
    have h_toReal_eq :
        (harmonic_measure (sisterVertex φ p ℓ_a) (cylinder ρ (p + 1))).toReal
          = (harmonic_measure (sisterVertex φ p ℓ_b) (cylinder ρ (p + 1))).toReal := by
      rw [h_dc_a, h_dc_b, h_ker]
    have h_ne_top_a :
        harmonic_measure (sisterVertex φ p ℓ_a) (cylinder ρ (p + 1)) ≠ ⊤ :=
      MeasureTheory.measure_ne_top _ _
    have h_ne_top_b :
        harmonic_measure (sisterVertex φ p ℓ_b) (cylinder ρ (p + 1)) ≠ ⊤ :=
      MeasureTheory.measure_ne_top _ _
    rw [← ENNReal.ofReal_toReal h_ne_top_a, ← ENNReal.ofReal_toReal h_ne_top_b,
        h_toReal_eq]
  | succ gap' ih =>
    -- gap = gap' + 1: q ≤ p, so q < p + 1. Decompose into 3 sub-cylinders.
    intro q hq_eq hq_pos ρ r hrp hrq h_ne
    have hq_le_p : q ≤ p := by omega
    -- Decompose cylinder ρ q via the 3-fold extend.
    have h_cyl_eq := cylinder_eq_iUnion_extend ρ q hq_pos
    set f_a : Fin 2 × Bool → Set F2_boundary :=
      fun ℓ' => cylinder (extendRep ρ q ℓ') (q + 1) with hf_a_def
    have h_disj := cylinder_extend_pairwise_disjoint ρ q hq_pos
    have h_meas : ∀ ℓ' ∈ nonCancelExt (ρ.val (q - 1)),
        MeasurableSet (f_a ℓ') := fun ℓ' _ => cylinder_measurable _ _
    -- Apply σ-additivity on both sides.
    have h_sum_a :
        harmonic_measure (sisterVertex φ p ℓ_a) (cylinder ρ q)
          = ∑ ℓ' ∈ nonCancelExt (ρ.val (q - 1)),
            harmonic_measure (sisterVertex φ p ℓ_a) (f_a ℓ') := by
      rw [h_cyl_eq]
      exact MeasureTheory.measure_biUnion_finset h_disj h_meas
    have h_sum_b :
        harmonic_measure (sisterVertex φ p ℓ_b) (cylinder ρ q)
          = ∑ ℓ' ∈ nonCancelExt (ρ.val (q - 1)),
            harmonic_measure (sisterVertex φ p ℓ_b) (f_a ℓ') := by
      rw [h_cyl_eq]
      exact MeasureTheory.measure_biUnion_finset h_disj h_meas
    rw [h_sum_a, h_sum_b]
    refine Finset.sum_congr rfl ?_
    intro ℓ' _hℓ'
    -- Sub-cylinder cylinder (extendRep ρ q ℓ') (q + 1).
    -- Apply IH at depth (q + 1) with the same disagreement at position r.
    -- We need r < q + 1 (already true since r < q ≤ q + 1).
    -- And (extendRep ρ q ℓ').val r = ρ.val r (since r < q).
    have h_extendRep_r : (extendRep ρ q ℓ').val r = ρ.val r :=
      extendRep_val_lt hrq
    have h_ne_extended : (extendRep ρ q ℓ').val r ≠ φ.val r := by
      rw [h_extendRep_r]; exact h_ne
    have hq1_pos : 1 ≤ q + 1 := by omega
    have hq1_eq : (q + 1) + gap' = p + 1 := by omega
    have hr_q1 : r < q + 1 := Nat.lt_succ_of_lt hrq
    exact ih (q + 1) hq1_eq hq1_pos (extendRep ρ q ℓ') r hrp hr_q1 h_ne_extended

/-- The "extending the natural letter" recovers the deeper cylinder. -/
private lemma extendRep_cylinder_natural (φ : F2_boundary) (p : ℕ) (hp : 1 ≤ p) :
    cylinder (extendRep φ p (φ.val p)) (p + 1) = cylinder φ (p + 1) := by
  have h_nc_φ : NonCancellation (φ.val (p - 1)) (φ.val p) := by
    have hp_eq : p - 1 + 1 = p := by omega
    have := φ.2 (p - 1)
    rwa [hp_eq] at this
  ext ψ
  simp only [mem_cylinder]
  constructor
  · intro h i hi
    have h_match := h i hi
    by_cases hip : i < p
    · rwa [extendRep_val_lt hip] at h_match
    · have hi_eq : i = p := by omega
      rw [hi_eq] at h_match ⊢
      rwa [extendRep_val_p hp h_nc_φ] at h_match
  · intro h i hi
    by_cases hip : i < p
    · rw [extendRep_val_lt hip]
      exact h i (Nat.lt_succ_of_lt hip)
    · have hi_eq : i = p := by omega
      rw [hi_eq]
      rw [extendRep_val_p hp h_nc_φ]
      exact h p (Nat.lt_succ_self _)

/-- The "natural letter" `φ.val p` is in `nonCancelExt(φ.val (p-1))`. -/
private lemma natural_letter_mem_nonCancelExt (φ : F2_boundary) (p : ℕ) (hp : 1 ≤ p) :
    φ.val p ∈ nonCancelExt (φ.val (p - 1)) := by
  rw [mem_nonCancelExt]
  have hp_eq : p - 1 + 1 = p := by omega
  have := φ.2 (p - 1)
  rwa [hp_eq] at this

/-- **Lemma D — sister-equality on `cylinder φ r` for all `r ≤ p`.**
For each `r ≤ p`, the harmonic measures `μ_{ψ_a}(cylinder φ r)` and
`μ_{ψ_b}(cylinder φ r)` coincide. Proved by induction on `r` from 0 up
to `p`, using `cylinder_eq_iUnion_extend` to decompose
`cylinder φ r` (or `univ_eq_iUnion_cylinder_one` for `r = 0`) into
sub-cylinders, splitting off `cylinder φ (r+1)` from the
"sibling" cylinders (which are outside `cylinder φ p` and so have
sister-equal measures by Lemma C). -/
private lemma sister_harmonic_eq_on_cylinder_phi_r
    (φ : F2_boundary) (p : ℕ) (hp : 1 ≤ p)
    (ℓ_a ℓ_b : Fin 2 × Bool)
    (h_nc_a : NonCancellation (φ.val (p - 1)) ℓ_a)
    (h_nc_b : NonCancellation (φ.val (p - 1)) ℓ_b) :
    ∀ r : ℕ, r ≤ p →
      harmonic_measure (sisterVertex φ p ℓ_a) (cylinder φ r)
        = harmonic_measure (sisterVertex φ p ℓ_b) (cylinder φ r) := by
  intro r hr_le
  induction r with
  | zero =>
    -- r = 0: cylinder φ 0 = univ, both probability measures = 1.
    rw [cylinder_zero]
    rw [(harmonic_measure_isProbabilityMeasure _).measure_univ]
    rw [(harmonic_measure_isProbabilityMeasure _).measure_univ]
  | succ r ih =>
    have hr_lt : r < p := by omega
    have hr_le_pred : r ≤ p := Nat.le_of_lt hr_lt
    have ih_eq := ih hr_le_pred
    -- Case split: r = 0 (use `univ_eq_iUnion_cylinder_one`)
    -- or r ≥ 1 (use `cylinder_eq_iUnion_extend`).
    rcases Nat.eq_zero_or_pos r with hr_zero | hr_pos
    · -- r = 0: decompose univ = ⊔_{ℓ_0} cylinder (const ℓ_0) 1.
      subst hr_zero
      -- We want: μ_a(cylinder φ 1) = μ_b(cylinder φ 1).
      -- cylinder φ 1 = cylinder (const (φ.val 0)) 1.
      have h_cyl_1 : cylinder φ 1 = cylinder (F2_boundary.const (φ.val 0)) 1 := by
        ext ψ
        simp [mem_cylinder, F2_boundary.const_val, Nat.lt_one_iff]
      -- univ = ⊔_{ℓ_0} cylinder (const ℓ_0) 1.
      have h_univ_eq := univ_eq_iUnion_cylinder_one
      have h_disj := cylinder_one_disjoint
      have h_meas : ∀ ℓ_0 : Fin 2 × Bool,
          MeasurableSet (cylinder (F2_boundary.const ℓ_0) 1) :=
        fun ℓ_0 => cylinder_measurable _ _
      -- Use σ-additivity on univ.
      have h_sum_a :
          (1 : ENNReal) = ∑ ℓ_0 : (Fin 2 × Bool),
            harmonic_measure (sisterVertex φ p ℓ_a) (cylinder (F2_boundary.const ℓ_0) 1) := by
        rw [show (1 : ENNReal) =
              harmonic_measure (sisterVertex φ p ℓ_a) Set.univ from
            ((harmonic_measure_isProbabilityMeasure _).measure_univ).symm]
        rw [← h_univ_eq]
        rw [MeasureTheory.measure_iUnion h_disj h_meas, tsum_fintype]
      have h_sum_b :
          (1 : ENNReal) = ∑ ℓ_0 : (Fin 2 × Bool),
            harmonic_measure (sisterVertex φ p ℓ_b) (cylinder (F2_boundary.const ℓ_0) 1) := by
        rw [show (1 : ENNReal) =
              harmonic_measure (sisterVertex φ p ℓ_b) Set.univ from
            ((harmonic_measure_isProbabilityMeasure _).measure_univ).symm]
        rw [← h_univ_eq]
        rw [MeasureTheory.measure_iUnion h_disj h_meas, tsum_fintype]
      -- For each ℓ_0 ≠ φ.val 0: by Lemma C, sister equal.
      -- For ℓ_0 = φ.val 0: this is cylinder (const (φ.val 0)) 1 = cylinder φ 1.
      -- Split out the (φ.val 0) term in each sum.
      have h_split_a :
          (∑ ℓ_0 : (Fin 2 × Bool),
              harmonic_measure (sisterVertex φ p ℓ_a) (cylinder (F2_boundary.const ℓ_0) 1))
            = harmonic_measure (sisterVertex φ p ℓ_a) (cylinder (F2_boundary.const (φ.val 0)) 1)
              + ∑ ℓ_0 ∈ (Finset.univ : Finset (Fin 2 × Bool)) \ {φ.val 0},
                harmonic_measure (sisterVertex φ p ℓ_a) (cylinder (F2_boundary.const ℓ_0) 1) := by
        rw [Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ (φ.val 0))]
        ring
      have h_split_b :
          (∑ ℓ_0 : (Fin 2 × Bool),
              harmonic_measure (sisterVertex φ p ℓ_b) (cylinder (F2_boundary.const ℓ_0) 1))
            = harmonic_measure (sisterVertex φ p ℓ_b) (cylinder (F2_boundary.const (φ.val 0)) 1)
              + ∑ ℓ_0 ∈ (Finset.univ : Finset (Fin 2 × Bool)) \ {φ.val 0},
                harmonic_measure (sisterVertex φ p ℓ_b) (cylinder (F2_boundary.const ℓ_0) 1) := by
        rw [Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ (φ.val 0))]
        ring
      -- Sibling sums are equal by Lemma C.
      have h_sibling_eq : ∀ ℓ_0 ∈ (Finset.univ : Finset (Fin 2 × Bool)) \ {φ.val 0},
          harmonic_measure (sisterVertex φ p ℓ_a) (cylinder (F2_boundary.const ℓ_0) 1)
            = harmonic_measure (sisterVertex φ p ℓ_b) (cylinder (F2_boundary.const ℓ_0) 1) := by
        intro ℓ_0 hℓ_0
        have h_ne : ℓ_0 ≠ φ.val 0 := by
          intro h
          simp [h] at hℓ_0
        -- Apply Lemma C with r = 0, q = 1, ρ = const ℓ_0.
        have h_outside : (F2_boundary.const ℓ_0).val 0 ≠ φ.val 0 := by
          simp [F2_boundary.const_val]; exact h_ne
        exact sister_harmonic_eq_on_outside φ p hp ℓ_a ℓ_b h_nc_a h_nc_b
          p 1 (by omega) (by omega) (F2_boundary.const ℓ_0) 0
          hr_lt (by omega) h_outside
      have h_sibling_sum_eq :
          (∑ ℓ_0 ∈ (Finset.univ : Finset (Fin 2 × Bool)) \ {φ.val 0},
              harmonic_measure (sisterVertex φ p ℓ_a) (cylinder (F2_boundary.const ℓ_0) 1))
            = ∑ ℓ_0 ∈ (Finset.univ : Finset (Fin 2 × Bool)) \ {φ.val 0},
              harmonic_measure (sisterVertex φ p ℓ_b) (cylinder (F2_boundary.const ℓ_0) 1) :=
        Finset.sum_congr rfl h_sibling_eq
      -- Combine.
      rw [h_cyl_1]
      -- From h_sum_a, h_sum_b: 1 = a-sum and 1 = b-sum, so they're equal.
      have h_sums_eq :
          (∑ ℓ_0 : (Fin 2 × Bool),
              harmonic_measure (sisterVertex φ p ℓ_a) (cylinder (F2_boundary.const ℓ_0) 1))
            = ∑ ℓ_0 : (Fin 2 × Bool),
              harmonic_measure (sisterVertex φ p ℓ_b) (cylinder (F2_boundary.const ℓ_0) 1) := by
        rw [← h_sum_a, ← h_sum_b]
      rw [h_split_a, h_split_b] at h_sums_eq
      -- h_sums_eq : a + sib_a = b + sib_b. With sib_a = sib_b, conclude a = b.
      rw [h_sibling_sum_eq] at h_sums_eq
      -- Cancel the sibling sum (finite).
      have h_sib_ne_top :
          (∑ ℓ_0 ∈ (Finset.univ : Finset (Fin 2 × Bool)) \ {φ.val 0},
              harmonic_measure (sisterVertex φ p ℓ_b) (cylinder (F2_boundary.const ℓ_0) 1)) ≠ ⊤ := by
        rw [ne_eq, ENNReal.sum_eq_top]
        push_neg
        intro ℓ_0 _
        exact MeasureTheory.measure_ne_top _ _
      exact (ENNReal.add_left_inj h_sib_ne_top).mp h_sums_eq
    · -- r ≥ 1: use cylinder_eq_iUnion_extend.
      have hr_pos' : 1 ≤ r := hr_pos
      have h_cyl_eq := cylinder_eq_iUnion_extend φ r hr_pos'
      have h_disj := cylinder_extend_pairwise_disjoint φ r hr_pos'
      set f_φ : Fin 2 × Bool → Set F2_boundary :=
        fun ℓ' => cylinder (extendRep φ r ℓ') (r + 1) with hf_def
      have h_meas : ∀ ℓ' ∈ nonCancelExt (φ.val (r - 1)),
          MeasurableSet (f_φ ℓ') := fun ℓ' _ => cylinder_measurable _ _
      -- σ-additivity:
      have h_sum_a :
          harmonic_measure (sisterVertex φ p ℓ_a) (cylinder φ r)
            = ∑ ℓ' ∈ nonCancelExt (φ.val (r - 1)),
              harmonic_measure (sisterVertex φ p ℓ_a) (f_φ ℓ') := by
        rw [h_cyl_eq]
        exact MeasureTheory.measure_biUnion_finset h_disj h_meas
      have h_sum_b :
          harmonic_measure (sisterVertex φ p ℓ_b) (cylinder φ r)
            = ∑ ℓ' ∈ nonCancelExt (φ.val (r - 1)),
              harmonic_measure (sisterVertex φ p ℓ_b) (f_φ ℓ') := by
        rw [h_cyl_eq]
        exact MeasureTheory.measure_biUnion_finset h_disj h_meas
      -- Split out the φ.val r term.
      have h_φ_r_in : φ.val r ∈ nonCancelExt (φ.val (r - 1)) :=
        natural_letter_mem_nonCancelExt φ r hr_pos'
      have h_split_a :
          (∑ ℓ' ∈ nonCancelExt (φ.val (r - 1)),
              harmonic_measure (sisterVertex φ p ℓ_a) (f_φ ℓ'))
            = harmonic_measure (sisterVertex φ p ℓ_a) (f_φ (φ.val r))
              + ∑ ℓ' ∈ nonCancelExt (φ.val (r - 1)) \ {φ.val r},
                harmonic_measure (sisterVertex φ p ℓ_a) (f_φ ℓ') := by
        rw [Finset.sum_eq_sum_diff_singleton_add h_φ_r_in]
        ring
      have h_split_b :
          (∑ ℓ' ∈ nonCancelExt (φ.val (r - 1)),
              harmonic_measure (sisterVertex φ p ℓ_b) (f_φ ℓ'))
            = harmonic_measure (sisterVertex φ p ℓ_b) (f_φ (φ.val r))
              + ∑ ℓ' ∈ nonCancelExt (φ.val (r - 1)) \ {φ.val r},
                harmonic_measure (sisterVertex φ p ℓ_b) (f_φ ℓ') := by
        rw [Finset.sum_eq_sum_diff_singleton_add h_φ_r_in]
        ring
      -- f_φ (φ.val r) = cylinder φ (r + 1) by extendRep_cylinder_natural.
      have h_natural_a : harmonic_measure (sisterVertex φ p ℓ_a) (f_φ (φ.val r))
          = harmonic_measure (sisterVertex φ p ℓ_a) (cylinder φ (r + 1)) := by
        simp only [hf_def]
        rw [extendRep_cylinder_natural φ r hr_pos']
      have h_natural_b : harmonic_measure (sisterVertex φ p ℓ_b) (f_φ (φ.val r))
          = harmonic_measure (sisterVertex φ p ℓ_b) (cylinder φ (r + 1)) := by
        simp only [hf_def]
        rw [extendRep_cylinder_natural φ r hr_pos']
      -- Sibling sum equality (by Lemma C).
      have h_sibling_eq : ∀ ℓ' ∈ nonCancelExt (φ.val (r - 1)) \ {φ.val r},
          harmonic_measure (sisterVertex φ p ℓ_a) (f_φ ℓ')
            = harmonic_measure (sisterVertex φ p ℓ_b) (f_φ ℓ') := by
        intro ℓ' hℓ'
        simp only [Finset.mem_sdiff, Finset.mem_singleton, mem_nonCancelExt] at hℓ'
        obtain ⟨h_nc_ℓ', h_ne⟩ := hℓ'
        -- (extendRep φ r ℓ').val r = ℓ' (by extendRep_val_p with r ≥ 1, h_nc_ℓ').
        have h_at_r : (extendRep φ r ℓ').val r = ℓ' := extendRep_val_p hr_pos' h_nc_ℓ'
        have h_outside : (extendRep φ r ℓ').val r ≠ φ.val r := by
          rw [h_at_r]; exact h_ne
        simp only [hf_def]
        exact sister_harmonic_eq_on_outside φ p hp ℓ_a ℓ_b h_nc_a h_nc_b
          (p - r) (r + 1) (by omega) (by omega) (extendRep φ r ℓ') r
          hr_lt (Nat.lt_succ_self _) h_outside
      have h_sibling_sum_eq :
          (∑ ℓ' ∈ nonCancelExt (φ.val (r - 1)) \ {φ.val r},
              harmonic_measure (sisterVertex φ p ℓ_a) (f_φ ℓ'))
            = ∑ ℓ' ∈ nonCancelExt (φ.val (r - 1)) \ {φ.val r},
              harmonic_measure (sisterVertex φ p ℓ_b) (f_φ ℓ') :=
        Finset.sum_congr rfl h_sibling_eq
      -- Combine: μ_a(cyl φ r) = μ_a(cyl φ (r+1)) + sib_a, similarly for b.
      -- IH: μ_a(cyl φ r) = μ_b(cyl φ r). Cancel sib (= sib by h_sibling) ⟹ μ_a(cyl φ (r+1)) = μ_b(cyl φ (r+1)).
      have h_eq_sums :
          harmonic_measure (sisterVertex φ p ℓ_a) (cylinder φ (r + 1))
            + ∑ ℓ' ∈ nonCancelExt (φ.val (r - 1)) \ {φ.val r},
              harmonic_measure (sisterVertex φ p ℓ_a) (f_φ ℓ')
            = harmonic_measure (sisterVertex φ p ℓ_b) (cylinder φ (r + 1))
              + ∑ ℓ' ∈ nonCancelExt (φ.val (r - 1)) \ {φ.val r},
                harmonic_measure (sisterVertex φ p ℓ_b) (f_φ ℓ') := by
        rw [← h_natural_a, ← h_natural_b, ← h_split_a, ← h_split_b,
            ← h_sum_a, ← h_sum_b]
        exact ih_eq
      rw [h_sibling_sum_eq] at h_eq_sums
      -- Cancel the sibling sum.
      have h_sib_ne_top :
          (∑ ℓ' ∈ nonCancelExt (φ.val (r - 1)) \ {φ.val r},
              harmonic_measure (sisterVertex φ p ℓ_b) (f_φ ℓ')) ≠ ⊤ := by
        rw [ne_eq, ENNReal.sum_eq_top]
        push_neg
        intro ℓ' _
        exact MeasureTheory.measure_ne_top _ _
      exact (ENNReal.add_left_inj h_sib_ne_top).mp h_eq_sums

/-- **Theorem (the headline) — sister cylinder equality.**
For sister extensions `ℓ_a, ℓ_b` (both non-cancelling `φ.val (p-1)`),
the depth-`(p+1)` cylinders `cylinder (extendRep φ p ℓ_·) (p+1)` have
equal `μ_1`-mass.

Combines the deep-cylinder identity at the sister vertices with Lemma D
(sister-equality on the depth-`p` cylinder `cylinder φ p`) via the
algebraic identity `8 · 3^{p-1} (y_a - y_b) = 0`. -/
theorem harmonic_measure_sister_cylinder_eq
    (φ : F2_boundary) (p : ℕ) (hp : 1 ≤ p)
    (ℓ_a ℓ_b : Fin 2 × Bool)
    (h_nc_a : NonCancellation (φ.val (p - 1)) ℓ_a)
    (h_nc_b : NonCancellation (φ.val (p - 1)) ℓ_b) :
    harmonic_measure 1 (cylinder (extendRep φ p ℓ_a) (p + 1))
      = harmonic_measure 1 (cylinder (extendRep φ p ℓ_b) (p + 1)) := by
  -- Set notation.
  set ψ_a : F2 := sisterVertex φ p ℓ_a with hψ_a
  set ψ_b : F2 := sisterVertex φ p ℓ_b with hψ_b
  set y_a : ℝ := (harmonic_measure 1 (cylinder (extendRep φ p ℓ_a) (p + 1))).toReal with hy_a
  set y_b : ℝ := (harmonic_measure 1 (cylinder (extendRep φ p ℓ_b) (p + 1))).toReal with hy_b
  -- Lemma D: μ_a(cylinder φ p) = μ_b(cylinder φ p).
  have h_phi_p :
      harmonic_measure ψ_a (cylinder φ p) = harmonic_measure ψ_b (cylinder φ p) :=
    sister_harmonic_eq_on_cylinder_phi_r φ p hp ℓ_a ℓ_b h_nc_a h_nc_b p (le_refl _)
  -- Decompose cylinder φ p into 3 sister sub-cylinders.
  have h_cyl_eq := cylinder_eq_iUnion_extend φ p hp
  set f_φ : Fin 2 × Bool → Set F2_boundary :=
    fun ℓ' => cylinder (extendRep φ p ℓ') (p + 1) with hf_def
  have h_disj := cylinder_extend_pairwise_disjoint φ p hp
  have h_meas : ∀ ℓ' ∈ nonCancelExt (φ.val (p - 1)),
      MeasurableSet (f_φ ℓ') := fun ℓ' _ => cylinder_measurable _ _
  -- σ-additivity at vertex ψ_a:
  have h_sum_a :
      harmonic_measure ψ_a (cylinder φ p)
        = ∑ ℓ' ∈ nonCancelExt (φ.val (p - 1)),
          harmonic_measure ψ_a (f_φ ℓ') := by
    rw [h_cyl_eq]
    exact MeasureTheory.measure_biUnion_finset h_disj h_meas
  have h_sum_b :
      harmonic_measure ψ_b (cylinder φ p)
        = ∑ ℓ' ∈ nonCancelExt (φ.val (p - 1)),
          harmonic_measure ψ_b (f_φ ℓ') := by
    rw [h_cyl_eq]
    exact MeasureTheory.measure_biUnion_finset h_disj h_meas
  -- Apply deep-cylinder at each ℓ'.
  -- For ℓ' = ℓ_a: kernel = 3^{p+1}; for ℓ' ≠ ℓ_a: kernel = 3^{p-1}.
  -- We work in ℝ (toReal).
  have h_len_a : ψ_a.toWord.length ≤ p + 1 := by
    rw [hψ_a]; rw [sisterVertex_length]
  have h_len_b : ψ_b.toWord.length ≤ p + 1 := by
    rw [hψ_b]; rw [sisterVertex_length]
  -- Real-valued masses:
  have h_phi_p_real :
      (harmonic_measure ψ_a (cylinder φ p)).toReal
        = (harmonic_measure ψ_b (cylinder φ p)).toReal := by
    rw [h_phi_p]
  -- Sum decomposition in ℝ:
  have h_finite_a : ∀ ℓ' : Fin 2 × Bool,
      harmonic_measure ψ_a (f_φ ℓ') ≠ ⊤ :=
    fun ℓ' => MeasureTheory.measure_ne_top _ _
  have h_finite_b : ∀ ℓ' : Fin 2 × Bool,
      harmonic_measure ψ_b (f_φ ℓ') ≠ ⊤ :=
    fun ℓ' => MeasureTheory.measure_ne_top _ _
  have h_sum_a_real :
      (harmonic_measure ψ_a (cylinder φ p)).toReal
        = ∑ ℓ' ∈ nonCancelExt (φ.val (p - 1)),
          (harmonic_measure ψ_a (f_φ ℓ')).toReal := by
    rw [h_sum_a, ENNReal.toReal_sum (fun ℓ' _ => h_finite_a ℓ')]
  have h_sum_b_real :
      (harmonic_measure ψ_b (cylinder φ p)).toReal
        = ∑ ℓ' ∈ nonCancelExt (φ.val (p - 1)),
          (harmonic_measure ψ_b (f_φ ℓ')).toReal := by
    rw [h_sum_b, ENNReal.toReal_sum (fun ℓ' _ => h_finite_b ℓ')]
  -- Apply deep-cylinder at each summand.
  have h_dc_a : ∀ ℓ' ∈ nonCancelExt (φ.val (p - 1)),
      (harmonic_measure ψ_a (f_φ ℓ')).toReal
        = poisson_kernel (extendRep φ p ℓ') ψ_a *
          (harmonic_measure 1 (f_φ ℓ')).toReal := by
    intro ℓ' _
    simp only [hf_def]
    exact harmonic_measure_translation_on_deep_cylinder ψ_a (extendRep φ p ℓ') (p + 1) h_len_a
  have h_dc_b : ∀ ℓ' ∈ nonCancelExt (φ.val (p - 1)),
      (harmonic_measure ψ_b (f_φ ℓ')).toReal
        = poisson_kernel (extendRep φ p ℓ') ψ_b *
          (harmonic_measure 1 (f_φ ℓ')).toReal := by
    intro ℓ' _
    simp only [hf_def]
    exact harmonic_measure_translation_on_deep_cylinder ψ_b (extendRep φ p ℓ') (p + 1) h_len_b
  -- Compute the kernel values.
  -- For ℓ' = ℓ_a: c(ψ_a, extendRep φ p ℓ_a) = p + 1, so kernel = 3^{p+1}.
  -- For ℓ' ≠ ℓ_a (NC): c = p, so kernel = 3^{p-1}.
  have h_ker_a_self :
      poisson_kernel (extendRep φ p ℓ_a) ψ_a = (3 : ℝ) ^ (p + 1 : ℤ) := by
    -- c = p + 1, busemann = (p+1) - 2(p+1) = -(p+1).
    rw [hψ_a]
    unfold sisterVertex poisson_kernel busemann
    rw [F2_boundary.length_toWord_valPrefix]
    rw [common_prefix_length_valPrefix_self]
    -- Goal: 3^(-((p+1) - 2(p+1))) = 3^(p+1).
    push_cast
    congr 1
    ring
  have h_ker_b_self :
      poisson_kernel (extendRep φ p ℓ_b) ψ_b = (3 : ℝ) ^ (p + 1 : ℤ) := by
    rw [hψ_b]
    unfold sisterVertex poisson_kernel busemann
    rw [F2_boundary.length_toWord_valPrefix]
    rw [common_prefix_length_valPrefix_self]
    push_cast
    congr 1
    ring
  have h_ker_a_other : ∀ ℓ' ∈ nonCancelExt (φ.val (p - 1)) \ {ℓ_a},
      poisson_kernel (extendRep φ p ℓ') ψ_a = (3 : ℝ) ^ (p - 1 : ℤ) := by
    intro ℓ' hℓ'
    simp only [Finset.mem_sdiff, Finset.mem_singleton, mem_nonCancelExt] at hℓ'
    obtain ⟨h_nc_ℓ', h_ne⟩ := hℓ'
    -- ψ_a's word = (φ.val 0, ..., φ.val (p-1), ℓ_a). extendRep φ p ℓ' has letters
    -- (φ.val 0, ..., φ.val (p-1), ℓ', ...). They first disagree at position p
    -- (since ℓ_a ≠ ℓ' here actually we need ℓ' ≠ ℓ_a). Common prefix length = p.
    rw [hψ_a]
    unfold sisterVertex poisson_kernel busemann
    rw [F2_boundary.length_toWord_valPrefix]
    -- valPrefix(extendRep φ p ℓ_a)(p+1) common prefix with (extendRep φ p ℓ').
    -- They agree on positions 0..p-1 (= φ on these), disagree at p.
    -- Use common_prefix_length_valPrefix_other with q = p.
    have h_q_agree : ∀ i, i < p →
        (extendRep φ p ℓ_a).val i = (extendRep φ p ℓ').val i := by
      intro i hi
      rw [extendRep_val_lt hi, extendRep_val_lt hi]
    have h_q_diff : (extendRep φ p ℓ_a).val p ≠ (extendRep φ p ℓ').val p := by
      rw [extendRep_val_p hp h_nc_a, extendRep_val_p hp h_nc_ℓ']
      exact fun h => h_ne h.symm
    have h_p_le : p + 1 ≤ p + 1 := le_refl _
    have h_cpl :=
      common_prefix_length_valPrefix_other (extendRep φ p ℓ') (extendRep φ p ℓ_a)
        p h_q_agree h_q_diff (p := p + 1) h_p_le
    rw [h_cpl]
    push_cast
    congr 1
    ring
  have h_ker_b_other : ∀ ℓ' ∈ nonCancelExt (φ.val (p - 1)) \ {ℓ_b},
      poisson_kernel (extendRep φ p ℓ') ψ_b = (3 : ℝ) ^ (p - 1 : ℤ) := by
    intro ℓ' hℓ'
    simp only [Finset.mem_sdiff, Finset.mem_singleton, mem_nonCancelExt] at hℓ'
    obtain ⟨h_nc_ℓ', h_ne⟩ := hℓ'
    rw [hψ_b]
    unfold sisterVertex poisson_kernel busemann
    rw [F2_boundary.length_toWord_valPrefix]
    have h_q_agree : ∀ i, i < p →
        (extendRep φ p ℓ_b).val i = (extendRep φ p ℓ').val i := by
      intro i hi
      rw [extendRep_val_lt hi, extendRep_val_lt hi]
    have h_q_diff : (extendRep φ p ℓ_b).val p ≠ (extendRep φ p ℓ').val p := by
      rw [extendRep_val_p hp h_nc_b, extendRep_val_p hp h_nc_ℓ']
      exact fun h => h_ne h.symm
    have h_p_le : p + 1 ≤ p + 1 := le_refl _
    have h_cpl :=
      common_prefix_length_valPrefix_other (extendRep φ p ℓ') (extendRep φ p ℓ_b)
        p h_q_agree h_q_diff (p := p + 1) h_p_le
    rw [h_cpl]
    push_cast
    congr 1
    ring
  -- Now we have everything to derive y_a = y_b.
  -- Set y_ℓ := μ_1(cylinder (extendRep φ p ℓ) (p+1)).toReal.
  set y : Fin 2 × Bool → ℝ :=
    fun ℓ' => (harmonic_measure 1 (cylinder (extendRep φ p ℓ') (p + 1))).toReal with hy_def
  -- Key real-valued equations:
  -- μ_a(cylinder φ p).toReal = 3^{p+1} y_a + 3^{p-1} (∑_{ℓ' ≠ ℓ_a} y_ℓ')
  -- μ_b(cylinder φ p).toReal = 3^{p+1} y_b + 3^{p-1} (∑_{ℓ' ≠ ℓ_b} y_ℓ')
  have h_ℓ_a_in : ℓ_a ∈ nonCancelExt (φ.val (p - 1)) := mem_nonCancelExt.mpr h_nc_a
  have h_ℓ_b_in : ℓ_b ∈ nonCancelExt (φ.val (p - 1)) := mem_nonCancelExt.mpr h_nc_b
  have h_eq_a :
      (harmonic_measure ψ_a (cylinder φ p)).toReal
        = (3 : ℝ) ^ (p + 1 : ℤ) * y ℓ_a
          + (3 : ℝ) ^ (p - 1 : ℤ) *
            (∑ ℓ' ∈ nonCancelExt (φ.val (p - 1)) \ {ℓ_a}, y ℓ') := by
    -- Replace each summand via deep-cylinder + kernel formula.
    rw [h_sum_a_real]
    have h_replace_terms : ∀ ℓ' ∈ nonCancelExt (φ.val (p - 1)),
        (harmonic_measure ψ_a (f_φ ℓ')).toReal
          = (if ℓ' = ℓ_a then (3 : ℝ) ^ (p + 1 : ℤ) else (3 : ℝ) ^ (p - 1 : ℤ))
            * y ℓ' := by
      intro ℓ' hℓ'_in
      rw [h_dc_a ℓ' hℓ'_in]
      by_cases h_eq : ℓ' = ℓ_a
      · subst h_eq
        rw [if_pos rfl, h_ker_a_self]
      · rw [if_neg h_eq]
        have hℓ'_in_diff : ℓ' ∈ nonCancelExt (φ.val (p - 1)) \ {ℓ_a} := by
          simp [Finset.mem_sdiff, Finset.mem_singleton, hℓ'_in, h_eq]
        rw [h_ker_a_other ℓ' hℓ'_in_diff]
    rw [Finset.sum_congr rfl h_replace_terms]
    -- Now split ℓ' = ℓ_a out.
    rw [Finset.sum_eq_sum_diff_singleton_add h_ℓ_a_in]
    rw [if_pos rfl]
    -- Sum over ℓ' ≠ ℓ_a: each term has if-false branch.
    have h_sum_other :
        (∑ ℓ' ∈ nonCancelExt (φ.val (p - 1)) \ {ℓ_a},
            (if ℓ' = ℓ_a then (3 : ℝ) ^ (p + 1 : ℤ) else (3 : ℝ) ^ (p - 1 : ℤ)) * y ℓ')
          = (3 : ℝ) ^ (p - 1 : ℤ) *
            ∑ ℓ' ∈ nonCancelExt (φ.val (p - 1)) \ {ℓ_a}, y ℓ' := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ℓ' hℓ'
      simp only [Finset.mem_sdiff, Finset.mem_singleton] at hℓ'
      rw [if_neg hℓ'.2]
    rw [h_sum_other]
    ring
  have h_eq_b :
      (harmonic_measure ψ_b (cylinder φ p)).toReal
        = (3 : ℝ) ^ (p + 1 : ℤ) * y ℓ_b
          + (3 : ℝ) ^ (p - 1 : ℤ) *
            (∑ ℓ' ∈ nonCancelExt (φ.val (p - 1)) \ {ℓ_b}, y ℓ') := by
    rw [h_sum_b_real]
    have h_replace_terms : ∀ ℓ' ∈ nonCancelExt (φ.val (p - 1)),
        (harmonic_measure ψ_b (f_φ ℓ')).toReal
          = (if ℓ' = ℓ_b then (3 : ℝ) ^ (p + 1 : ℤ) else (3 : ℝ) ^ (p - 1 : ℤ))
            * y ℓ' := by
      intro ℓ' hℓ'_in
      rw [h_dc_b ℓ' hℓ'_in]
      by_cases h_eq : ℓ' = ℓ_b
      · subst h_eq
        rw [if_pos rfl, h_ker_b_self]
      · rw [if_neg h_eq]
        have hℓ'_in_diff : ℓ' ∈ nonCancelExt (φ.val (p - 1)) \ {ℓ_b} := by
          simp [Finset.mem_sdiff, Finset.mem_singleton, hℓ'_in, h_eq]
        rw [h_ker_b_other ℓ' hℓ'_in_diff]
    rw [Finset.sum_congr rfl h_replace_terms]
    rw [Finset.sum_eq_sum_diff_singleton_add h_ℓ_b_in]
    rw [if_pos rfl]
    have h_sum_other :
        (∑ ℓ' ∈ nonCancelExt (φ.val (p - 1)) \ {ℓ_b},
            (if ℓ' = ℓ_b then (3 : ℝ) ^ (p + 1 : ℤ) else (3 : ℝ) ^ (p - 1 : ℤ)) * y ℓ')
          = (3 : ℝ) ^ (p - 1 : ℤ) *
            ∑ ℓ' ∈ nonCancelExt (φ.val (p - 1)) \ {ℓ_b}, y ℓ' := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ℓ' hℓ'
      simp only [Finset.mem_sdiff, Finset.mem_singleton] at hℓ'
      rw [if_neg hℓ'.2]
    rw [h_sum_other]
    ring
  -- Setting S = Σ y_ℓ', we have Σ_{ℓ ≠ ℓ_a} y = S - y_a, similarly for b.
  set S : ℝ := ∑ ℓ' ∈ nonCancelExt (φ.val (p - 1)), y ℓ' with hS_def
  have h_S_sub_a :
      (∑ ℓ' ∈ nonCancelExt (φ.val (p - 1)) \ {ℓ_a}, y ℓ') = S - y ℓ_a := by
    rw [hS_def, Finset.sum_eq_sum_diff_singleton_add h_ℓ_a_in]
    ring
  have h_S_sub_b :
      (∑ ℓ' ∈ nonCancelExt (φ.val (p - 1)) \ {ℓ_b}, y ℓ') = S - y ℓ_b := by
    rw [hS_def, Finset.sum_eq_sum_diff_singleton_add h_ℓ_b_in]
    ring
  rw [h_S_sub_a] at h_eq_a
  rw [h_S_sub_b] at h_eq_b
  -- h_eq_a: μ_a.toReal = 3^{p+1} y_a + 3^{p-1} (S - y_a) = 8·3^{p-1} y_a + 3^{p-1} S
  -- h_eq_b: μ_b.toReal = 8·3^{p-1} y_b + 3^{p-1} S
  -- And h_phi_p_real: μ_a.toReal = μ_b.toReal.
  -- So 8·3^{p-1}(y_a - y_b) = 0, hence y_a = y_b.
  have h_8 :
      (3 : ℝ) ^ (p + 1 : ℤ) - (3 : ℝ) ^ (p - 1 : ℤ) = 8 * (3 : ℝ) ^ (p - 1 : ℤ) := by
    have h3ne : (3 : ℝ) ≠ 0 := by norm_num
    have h_split : (3 : ℝ) ^ (p + 1 : ℤ) = 9 * (3 : ℝ) ^ (p - 1 : ℤ) := by
      rw [show (p + 1 : ℤ) = 2 + (p - 1 : ℤ) from by ring]
      rw [zpow_add₀ h3ne]
      norm_num
    linarith
  have h_pow_pos : (0 : ℝ) < (3 : ℝ) ^ (p - 1 : ℤ) := zpow_pos (by norm_num) _
  -- Combine h_eq_a, h_eq_b, h_phi_p_real:
  have h_eq_combined :
      (3 : ℝ) ^ (p + 1 : ℤ) * y ℓ_a + (3 : ℝ) ^ (p - 1 : ℤ) * (S - y ℓ_a)
        = (3 : ℝ) ^ (p + 1 : ℤ) * y ℓ_b + (3 : ℝ) ^ (p - 1 : ℤ) * (S - y ℓ_b) := by
    rw [← h_eq_a, ← h_eq_b]
    exact h_phi_p_real
  -- From h_eq_combined: ((3^{p+1} - 3^{p-1}) (y_a - y_b)) = 0.
  have h_diff : ((3 : ℝ) ^ (p + 1 : ℤ) - (3 : ℝ) ^ (p - 1 : ℤ)) * (y ℓ_a - y ℓ_b) = 0 := by
    have := h_eq_combined
    nlinarith [h_eq_combined]
  have h_factor_pos : (3 : ℝ) ^ (p + 1 : ℤ) - (3 : ℝ) ^ (p - 1 : ℤ) > 0 := by
    rw [h_8]; positivity
  have h_factor_ne : (3 : ℝ) ^ (p + 1 : ℤ) - (3 : ℝ) ^ (p - 1 : ℤ) ≠ 0 :=
    ne_of_gt h_factor_pos
  have h_y_eq : y ℓ_a = y ℓ_b := by
    have := mul_eq_zero.mp h_diff
    rcases this with h1 | h2
    · exact absurd h1 h_factor_ne
    · linarith
  -- Convert from .toReal back to ENNReal.
  have h_ne_top_a : harmonic_measure 1 (cylinder (extendRep φ p ℓ_a) (p + 1)) ≠ ⊤ :=
    MeasureTheory.measure_ne_top _ _
  have h_ne_top_b : harmonic_measure 1 (cylinder (extendRep φ p ℓ_b) (p + 1)) ≠ ⊤ :=
    MeasureTheory.measure_ne_top _ _
  rw [← ENNReal.ofReal_toReal h_ne_top_a, ← ENNReal.ofReal_toReal h_ne_top_b]
  -- y_eq is `y ℓ_a = y ℓ_b`; unfold to get the .toReal equality.
  show ENNReal.ofReal (harmonic_measure 1 (cylinder (extendRep φ p ℓ_a) (p + 1))).toReal
        = ENNReal.ofReal (harmonic_measure 1 (cylinder (extendRep φ p ℓ_b) (p + 1))).toReal
  rw [show (harmonic_measure 1 (cylinder (extendRep φ p ℓ_a) (p + 1))).toReal = y ℓ_a from rfl,
      show (harmonic_measure 1 (cylinder (extendRep φ p ℓ_b) (p + 1))).toReal = y ℓ_b from rfl,
      h_y_eq]

end SisterCylinderEq

/-- **Q49 (cylinder formula).** For every length `p ≥ 1` and every boundary
ray `φ`, the harmonic measure of the cylinder `I(φ, p)` based at `x = 1` is

  `μ_1(I(φ, p)) = 1 / (4 · 3^{p-1})`.

By symmetry of the 4-regular tree (degree-4 root, degree-3 thereafter).

**Wave 25 dissolution.**  Direct proof by induction on `p`.  The base
case (`p = 1`) is a theorem (`harmonic_measure_one_cylinder_constant_depth1`,
Wave 34) derived from the deep-cylinder identity.  The inductive step
still uses the admission `harmonic_measure_one_cylinder_constant`. -/
theorem harmonic_measure_cylinder (φ : F2_boundary) (p : ℕ) (hp : 1 ≤ p) :
    (harmonic_measure 1) (cylinder φ p)
      = ENNReal.ofReal ((1 : ℝ) / (4 * 3 ^ (p - 1))) := by
  -- Induction on `p ≥ 1`, generalising `φ`.
  induction p, hp using Nat.le_induction generalizing φ with
  | base =>
    -- p = 1: directly use the Wave 34 depth-1 theorem
    -- `harmonic_measure_one_const_cylinder_one_toReal`, which gives
    -- `μ_1(I(const _, 1)).toReal = 1/4`.
    have h_eq_const :
        cylinder φ 1 = cylinder (F2_boundary.const (φ.val 0)) 1 := by
      ext ψ
      simp [mem_cylinder, F2_boundary.const_val, Nat.lt_one_iff]
    have h_ne_top : harmonic_measure 1
        (cylinder (F2_boundary.const (φ.val 0)) 1) ≠ ⊤ :=
      MeasureTheory.measure_ne_top _ _
    have h_quarter :
        (harmonic_measure 1 (cylinder (F2_boundary.const (φ.val 0)) 1)).toReal
          = 1 / 4 :=
      harmonic_measure_one_const_cylinder_one_toReal (φ.val 0)
    have h_eq :
        harmonic_measure 1 (cylinder (F2_boundary.const (φ.val 0)) 1)
          = ENNReal.ofReal (1 / 4) := by
      rw [← h_quarter, ENNReal.ofReal_toReal h_ne_top]
    rw [h_eq_const, h_eq]
    -- 1/(4 · 3^0) = 1/4 in ENNReal.
    congr 1
    norm_num
  | succ p hp ih =>
    -- Inductive step: μ_1(cylinder φ (p+1)) = (1/3) · μ_1(cylinder φ p).
    have h_cyl_eq := cylinder_eq_iUnion_extend φ p hp
    set f : Fin 2 × Bool → Set F2_boundary :=
      fun ℓ => cylinder (extendRep φ p ℓ) (p + 1) with hf_def
    have h_disj := cylinder_extend_pairwise_disjoint φ p hp
    have h_meas : ∀ ℓ ∈ nonCancelExt (φ.val (p - 1)),
        MeasurableSet (f ℓ) := fun ℓ _ => cylinder_measurable _ _
    have h_sum_eq :
        (harmonic_measure 1) (cylinder φ p) =
          ∑ ℓ ∈ nonCancelExt (φ.val (p - 1)), (harmonic_measure 1) (f ℓ) := by
      rw [h_cyl_eq]
      rw [MeasureTheory.measure_biUnion_finset h_disj h_meas]
    -- All summands have the same measure (by Wave 34-final sister equality).
    have h_eq_φ : ∀ ℓ ∈ nonCancelExt (φ.val (p - 1)),
        harmonic_measure 1 (f ℓ)
          = harmonic_measure 1 (cylinder φ (p + 1)) := by
      intro ℓ hℓ
      simp only [hf_def]
      have h_nc_ℓ : NonCancellation (φ.val (p - 1)) ℓ := mem_nonCancelExt.mp hℓ
      have h_nc_natural : NonCancellation (φ.val (p - 1)) (φ.val p) := by
        have hp_eq : p - 1 + 1 = p := by omega
        have := φ.2 (p - 1)
        rwa [hp_eq] at this
      have h_sister :=
        SisterCylinderEq.harmonic_measure_sister_cylinder_eq
          φ p hp ℓ (φ.val p) h_nc_ℓ h_nc_natural
      rw [h_sister, SisterCylinderEq.extendRep_cylinder_natural φ p hp]
    have h_card : (nonCancelExt (φ.val (p - 1))).card = 3 := nonCancelExt_card _
    have h_sum_const :
        (harmonic_measure 1) (cylinder φ p)
          = (3 : ENNReal) * harmonic_measure 1 (cylinder φ (p + 1)) := by
      rw [h_sum_eq, Finset.sum_congr rfl h_eq_φ, Finset.sum_const, h_card,
        nsmul_eq_mul]
      norm_cast
    have ih_φ := ih φ
    rw [h_sum_const] at ih_φ
    -- ih_φ : 3 * μ_1(cylinder φ (p+1)) = ENNReal.ofReal (1/(4·3^{p-1})).
    -- Solve for μ_1(cylinder φ (p+1)).
    have h3_ne_zero : (3 : ENNReal) ≠ 0 := by norm_num
    have h3_ne_top : (3 : ENNReal) ≠ ⊤ := by norm_num
    have hX : harmonic_measure 1 (cylinder φ (p + 1))
        = ENNReal.ofReal ((1 : ℝ) / (4 * 3 ^ (p - 1))) / 3 := by
      rw [ENNReal.eq_div_iff h3_ne_zero h3_ne_top]
      exact ih_φ
    rw [hX]
    have h3pos : (0 : ℝ) < 3 := by norm_num
    have h3_eq : (3 : ENNReal) = ENNReal.ofReal 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) from by norm_num, ENNReal.ofReal_natCast]
      rfl
    rw [h3_eq, ← ENNReal.ofReal_div_of_pos h3pos]
    congr 1
    have h_succ : p + 1 - 1 = p := by omega
    rw [h_succ]
    have h_p_split : p = (p - 1) + 1 := by omega
    conv_rhs => rw [h_p_split, pow_succ]
    field_simp

/-- **Wave 25 corollary** — geometric factorisation of the walk-prefix
event, derived from the cylinder formula via
`harmonic_measure_cylinder_eq_walk_event`. -/
lemma step_measure_walk_prefix_event_one
    (φ : F2_boundary) (p : ℕ) (hp : 1 ≤ p) :
    step_measure (walkPrefixEvent 1 φ p)
      = ENNReal.ofReal ((1 : ℝ) / (4 * 3 ^ (p - 1))) := by
  rw [← harmonic_measure_cylinder_eq_walk_event 1 φ p]
  exact harmonic_measure_cylinder φ p hp

/-! #### Structural decomposition of the Poisson representation

The Poisson representation is decomposed into three leaf lemmas feeding
a π-system uniqueness argument: (i) cylinders form a π-system,
(ii) cylinders generate the σ-algebra on `∂F_2`, (iii) the identity
holds on cylinders.  Combining the three by
`MeasureTheory.Measure.ext_of_generateFrom_of_iUnion` (or the
Radon–Nikodym / dominated-convergence route) gives the theorem on all
Borel sets.
-/

/-- **Leaf 3 — cylinders form a π-system.** The intersection of two
cylinders `I(φ, p) ∩ I(φ, q)` with the same `φ` is a cylinder (of length
`max p q`), and two cylinders with *different* `φ`'s either coincide on
the common prefix (and the intersection is the longer cylinder) or
disagree somewhere (and the intersection is empty).  Both outcomes are
cylinders or `∅`, so the family of cylinders is stable under finite
intersections.

For the π-system argument we only need: cylinders (together with `∅`)
are ∩-stable.  Stated abstractly. -/
lemma cylinders_isPiSystem :
    IsPiSystem {S : Set F2_boundary |
      ∃ φ : F2_boundary, ∃ p : ℕ, S = cylinder φ p} := by
  -- Given `S₁ = cylinder φ₁ p₁` and `S₂ = cylinder φ₂ p₂`, pick any
  -- `γ ∈ S₁ ∩ S₂` as the common extension; then
  -- `S₁ ∩ S₂ = cylinder γ (max p₁ p₂)`.
  rintro S₁ ⟨φ₁, p₁, rfl⟩ S₂ ⟨φ₂, p₂, rfl⟩ h_nonempty
  obtain ⟨γ, hγ₁, hγ₂⟩ := h_nonempty
  refine ⟨γ, max p₁ p₂, ?_⟩
  ext ψ
  simp only [mem_cylinder, Set.mem_inter_iff]
  -- `γ ∈ cylinder φ₁ p₁` and `γ ∈ cylinder φ₂ p₂` give the pointwise
  -- agreement we exploit below.
  rw [mem_cylinder] at hγ₁ hγ₂
  constructor
  · rintro ⟨h1, h2⟩ i hi
    rcases lt_or_ge i p₁ with hip₁ | hip₁
    · -- `ψ.val i = φ₁.val i = γ.val i`.
      rw [h1 i hip₁, (hγ₁ i hip₁).symm]
    · -- `i ≥ p₁`, but `i < max p₁ p₂`, so `i < p₂`.
      have hip₂ : i < p₂ := by
        rcases (lt_max_iff.mp hi) with h | h
        · exact absurd h (not_lt.mpr hip₁)
        · exact h
      rw [h2 i hip₂, (hγ₂ i hip₂).symm]
  · intro h
    refine ⟨?_, ?_⟩
    · intro i hi
      have := h i (hi.trans_le (le_max_left _ _))
      rw [this, hγ₁ i hi]
    · intro i hi
      have := h i (hi.trans_le (le_max_right _ _))
      rw [this, hγ₂ i hi]

/-! #### Wave 24C — cylinder/F2bar-cylinder bridge

The cylinder `cylinder φ p ⊆ F2_boundary` is the preimage of the F2bar
cylinder `Compactification.cylinder (F2_boundary_to_F2bar φ) p` under
the embedding `F2_boundary_to_F2bar`.  This lets us transport openness
and the metric-ball/cylinder identity from F2bar to F2_boundary, which
in turn lets us replace the topology-to-σ-algebra companion axiom by a
direct application of `borel_eq_generateFrom_of_subbasis`. -/

/-- The F2_boundary cylinder is the preimage of the F2bar cylinder under
the embedding. -/
lemma cylinder_eq_preimage_F2bar_cylinder (φ : F2_boundary) (p : ℕ) :
    cylinder φ p =
      F2_boundary_to_F2bar ⁻¹' F2bar.cylinder (F2_boundary_to_F2bar φ) p := by
  ext ψ
  simp only [mem_cylinder, Set.mem_preimage, F2bar.mem_cylinder]
  constructor
  · intro h i hi
    show fbgToExtGen (ψ.val i) = fbgToExtGen (φ.val i)
    rw [h i hi]
  · intro h i hi
    have : fbgToExtGen (ψ.val i) = fbgToExtGen (φ.val i) := h i hi
    exact fbgToExtGen_injective this

/-- Cylinders are open in the induced topology on `F2_boundary`. -/
lemma cylinder_isOpen (φ : F2_boundary) (p : ℕ) : IsOpen (cylinder φ p) := by
  rw [cylinder_eq_preimage_F2bar_cylinder]
  exact (F2bar.cylinder_isOpen _ _).preimage F2_boundary_to_F2bar_continuous

/-- Cylinders form a topological basis of `F2_boundary`.

Sketch: cylinders are open (`cylinder_isOpen`), and for every open `U`
and every `ψ ∈ U`, the continuity of `F2_boundary_to_F2bar` yields an
F2bar-open `V` containing `F2_boundary_to_F2bar ψ` whose preimage is
contained in `U`; since F2bar is a metric space, `V` contains a
metric ball `B(F2_boundary_to_F2bar ψ, exp(-p))` for some `p`, and
F2bar-balls equal F2bar-cylinders (`ball_eq_cylinder`).  Pulling back,
`cylinder ψ (p+1)` lies inside `U`. -/
lemma cylinders_isTopologicalBasis :
    TopologicalSpace.IsTopologicalBasis
      {S : Set F2_boundary | ∃ φ : F2_boundary, ∃ p : ℕ, S = cylinder φ p} := by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro U ⟨φ, p, rfl⟩
    exact cylinder_isOpen φ p
  · intro ψ U hψU hU
    -- `U` is open in the induced topology; pull back to F2bar.
    obtain ⟨V, hVopen, hVeq⟩ : ∃ V : Set F2bar, IsOpen V ∧
        U = F2_boundary_to_F2bar ⁻¹' V := by
      rw [isOpen_induced_iff] at hU
      obtain ⟨V, hV, hVeq⟩ := hU
      exact ⟨V, hV, hVeq.symm⟩
    -- The image `F2_boundary_to_F2bar ψ` lies in V.
    have hψV : F2_boundary_to_F2bar ψ ∈ V := by
      have : ψ ∈ F2_boundary_to_F2bar ⁻¹' V := hVeq ▸ hψU
      exact this
    -- By openness in the metric space F2bar, find a metric ball around it in V.
    rw [Metric.isOpen_iff] at hVopen
    obtain ⟨ε, hεpos, hball⟩ := hVopen _ hψV
    -- Choose `p` with `exp(-(p : ℝ)) < ε`, so that `Metric.ball y (exp(-p)) ⊆ ball y ε ⊆ V`.
    obtain ⟨p, hp⟩ : ∃ p : ℕ, Real.exp (-(p : ℝ)) < ε := by
      -- As n → ∞, exp(-n) → 0, so eventually < ε.
      have h_tend : Filter.Tendsto (fun n : ℕ => Real.exp (-(n : ℝ)))
          Filter.atTop (nhds 0) := by
        have h1 : Filter.Tendsto (fun n : ℕ => -((n : ℝ))) Filter.atTop Filter.atBot :=
          tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
        have h2 : Filter.Tendsto Real.exp Filter.atBot (nhds 0) :=
          Real.tendsto_exp_atBot
        exact h2.comp h1
      rcases (Metric.tendsto_atTop.mp h_tend) ε hεpos with ⟨N, hN⟩
      refine ⟨N, ?_⟩
      have hd := hN N le_rfl
      rw [Real.dist_eq, sub_zero, abs_of_pos (Real.exp_pos _)] at hd
      exact hd
    -- The cylinder `F2bar.cylinder (F2_boundary_to_F2bar ψ) (p+1)` equals the
    -- ball, hence lies in V.
    have hcyl_sub : F2bar.cylinder (F2_boundary_to_F2bar ψ) (p + 1) ⊆ V := by
      rw [← F2bar.ball_eq_cylinder]
      intro z hz
      exact hball ((Metric.ball_subset_ball hp.le) hz)
    -- Therefore the F2_boundary cylinder is contained in U.
    refine ⟨cylinder ψ (p + 1), ⟨ψ, p + 1, rfl⟩, self_mem_cylinder ψ _, ?_⟩
    rw [cylinder_eq_preimage_F2bar_cylinder, hVeq]
    exact Set.preimage_mono hcyl_sub

/-- **Leaf 4 — cylinders generate the Borel σ-algebra.** The σ-algebra
on `F2_boundary` is generated by the family of cylinders.

Wave 24C: dissolved from the previous companion axiom
`F2_boundary_measurableSpace_eq_generateFrom_cylinders`.  The proof
applies `IsTopologicalBasis.borel_eq_generateFrom` to the cylinder basis
of the induced topology (`cylinders_isTopologicalBasis`); second
countability of `F2_boundary` is automatic from the metric-space
structure on `F2bar` (compact ⇒ proper ⇒ second countable) via
`secondCountableTopology_induced`. -/
lemma borel_F2_boundary_eq_generateFrom_cylinders :
    (inferInstance : MeasurableSpace F2_boundary) =
      MeasurableSpace.generateFrom
        {S : Set F2_boundary |
          ∃ φ : F2_boundary, ∃ p : ℕ, S = cylinder φ p} := by
  -- F2_boundary inherits second countability from F2bar (compact metric space).
  haveI : SecondCountableTopology F2_boundary :=
    TopologicalSpace.secondCountableTopology_induced F2_boundary F2bar
      F2_boundary_to_F2bar
  -- The σ-algebra is the Borel σ-algebra by construction (`F2_boundary.borelSpace`).
  show (borel F2_boundary) = _
  exact cylinders_isTopologicalBasis.borel_eq_generateFrom

/-! **Wave 25 Step 3 dissolution — `harmonic_measure_poisson_on_cylinder`.**

The Bochner-integral form of the Poisson identity on every cylinder is
now a *theorem*; see the proof block placed after `poisson_kernel_integrable`
(both are required: integrability for the Bochner-integration constants,
and the deep-cylinder helpers below for the Busemann calculation).  The
companion axiom `harmonic_measure_poisson_on_cylinder_axiom` was retired
in favour of a strictly weaker theorem
`harmonic_measure_translation_on_deep_cylinder` (cylinder regime
`p ≥ |x|`, only the constant — non-integral — translation form;
itself a theorem since Wave 29-retry, with its strong-Markov leaves
dissolved in Wave 35.5) plus combinatorial helpers about the Busemann
function. -/

/-! **Wave 24D dissolution — `harmonic_measure_poisson_on_cylinder_enn`.**

The ENNReal cylinder identity is now a *theorem*; see below for the
two-step derivation.  The relevant lemmas are placed AFTER
`poisson_kernel_nonneg` (Wave 24C theorem) and
`poisson_kernel_integrable` (Wave 24D-1 theorem) since they depend on
both. -/

/-- **Wave 24C dissolution.** Non-negativity of the Poisson kernel is
trivial from its definition `poisson_kernel ψ x = (3 : ℝ) ^ (-busemann ψ x)`:
`3 > 0`, so any integer power of `3` is positive. -/
theorem poisson_kernel_nonneg (x : F2) (ψ : F2_boundary) :
    0 ≤ poisson_kernel ψ x := by
  unfold poisson_kernel
  positivity

/-! **Wave 24D dissolution — `poisson_kernel_integrable`.**

Integrability of `ψ ↦ poisson_kernel ψ x` against `harmonic_measure 1`
follows from a *boundedness* argument, NOT from any "Busemann
exponential moments" hypothesis.  For fixed `x ∈ F_2`, the Busemann
function `b_ψ(x) = |x| − 2 · m(x, ψ)` is integer-valued with
`0 ≤ m(x, ψ) ≤ |x|`, hence `−|x| ≤ b_ψ(x) ≤ |x|`.  Therefore
`poisson_kernel ψ x = 3^{−b_ψ(x)} ≤ 3^{|x|}` (constant in `ψ`).
Combined with measurability (the kernel factors through the
finite-valued `common_prefix_length x ·`) and the fact that
`harmonic_measure 1` is a probability (hence finite) measure,
`Integrable.of_bound` closes the goal.

Two helper lemmas package the measurability route:
* `prefixMatches_setOf_measurable`: for fixed `x, p`, the set
  `{ψ | PrefixMatches x ψ p}` is a finite intersection of coordinate
  level sets, hence measurable.
* `common_prefix_length_measurable`: applying
  `measurable_to_countable'` reduces to measurability of the level
  sets `{ψ | common_prefix_length x ψ = k}`, each obtained from the
  previous lemma via `Nat.findGreatest_eq_iff`. -/

/-- Auxiliary: when `i < x.toWord.length`, the optional getter
`x.toWord[i]?` equals `some letter` iff `letter` equals the indexed
element `x.toWord[i]`. -/
private lemma toWord_getElem?_eq_some_iff (x : F2) (i : ℕ)
    (hi : i < x.toWord.length) (ℓ : Fin 2 × Bool) :
    x.toWord[i]? = some ℓ ↔ x.toWord[i]'hi = ℓ := by
  rw [List.getElem?_eq_getElem hi, Option.some_inj]

/-- For fixed `x : F2` and `p : ℕ`, the set
`{ψ | PrefixMatches x ψ p}` is a Borel-measurable subset of the
boundary.  Proof: when `p ≤ |x|`, the predicate `PrefixMatches`
becomes a finite conjunction of coordinate equalities
`ψ.val i = x.toWord[i]` (for `i < p`), each measurable by
`F2_boundary_coord_measurable`; when `p > |x|`, the set is empty. -/
lemma prefixMatches_setOf_measurable (x : F2) (p : ℕ) :
    MeasurableSet {ψ : F2_boundary | PrefixMatches x ψ p} := by
  by_cases hp : p ≤ x.toWord.length
  · -- p ≤ |x|: rewrite as a finite intersection of coordinate level sets.
    -- For each i < p, define the predicate `ψ.val i = x.toWord[i]`.
    have h_eq : {ψ : F2_boundary | PrefixMatches x ψ p} =
        ⋂ i ∈ (Finset.range p : Set ℕ),
          {ψ : F2_boundary | ∀ h : i < x.toWord.length,
            ψ.val i = x.toWord[i]'h} := by
      ext ψ
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.coe_range,
        Set.mem_Iio]
      constructor
      · rintro ⟨_, hpm⟩ i hi h_il
        have h_some := hpm i hi
        rw [toWord_getElem?_eq_some_iff x i h_il] at h_some
        exact h_some.symm
      · intro h
        refine ⟨hp, ?_⟩
        intro i hi
        have hi_lt : i < x.toWord.length := lt_of_lt_of_le hi hp
        have heq := h i hi hi_lt
        rw [toWord_getElem?_eq_some_iff x i hi_lt]
        exact heq.symm
    rw [h_eq]
    refine MeasurableSet.biInter (Finset.range p).countable_toSet ?_
    intro i hi_in
    have hi_in_p : i < p := Finset.mem_range.mp (Finset.mem_coe.mp hi_in)
    have hi_lt : i < x.toWord.length := lt_of_lt_of_le hi_in_p hp
    -- Goal: MeasurableSet {ψ | ∀ h, ψ.val i = x.toWord[i]'h}
    -- Equivalent to {ψ | ψ.val i = x.toWord[i]'hi_lt}.
    have h_simp : {ψ : F2_boundary | ∀ h : i < x.toWord.length,
        ψ.val i = x.toWord[i]'h} =
        {ψ : F2_boundary | ψ.val i = x.toWord[i]'hi_lt} := by
      ext ψ
      simp only [Set.mem_setOf_eq]
      exact ⟨fun h => h hi_lt, fun h _ => h⟩
    rw [h_simp]
    exact F2_boundary_coord_measurable i _
  · -- p > |x|: PrefixMatches forces p ≤ |x|, so the set is empty.
    have h_empty : {ψ : F2_boundary | PrefixMatches x ψ p} = ∅ := by
      ext ψ
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hle, _⟩
      exact hp hle
    rw [h_empty]
    exact MeasurableSet.empty

/-- For fixed `x : F2`, the function `ψ ↦ common_prefix_length x ψ`
is measurable as a map to `ℕ` (with the discrete σ-algebra).  Proof:
each level set `{ψ | common_prefix_length x ψ = k}` is described by
`Nat.findGreatest_eq_iff` as a finite Boolean combination of the
measurable sets `{ψ | PrefixMatches x ψ p}`. -/
lemma common_prefix_length_measurable (x : F2) :
    Measurable (fun ψ : F2_boundary => common_prefix_length x ψ) := by
  classical
  apply measurable_to_countable'
  intro k
  -- Goal: MeasurableSet ((fun ψ => common_prefix_length x ψ) ⁻¹' {k})
  -- which is the same as {ψ | common_prefix_length x ψ = k}.
  show MeasurableSet {ψ : F2_boundary | common_prefix_length x ψ = k}
  by_cases hk : k ≤ x.toWord.length
  · -- k ≤ |x|: use `Nat.findGreatest_eq_iff`.
    have h_eq : {ψ : F2_boundary | common_prefix_length x ψ = k} =
        ({ψ : F2_boundary | k = 0 ∨ PrefixMatches x ψ k} ∩
          ⋂ n ∈ (Finset.Ioc k x.toWord.length : Set ℕ),
            {ψ : F2_boundary | ¬ PrefixMatches x ψ n}) := by
      ext ψ
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
        Finset.mem_coe, Finset.mem_Ioc]
      unfold common_prefix_length
      rw [Nat.findGreatest_eq_iff]
      constructor
      · rintro ⟨_, h0, hgt⟩
        refine ⟨?_, ?_⟩
        · by_cases hk0 : k = 0
          · exact Or.inl hk0
          · exact Or.inr (h0 hk0)
        · intro n ⟨hn1, hn2⟩
          exact hgt hn1 hn2
      · rintro ⟨h0, hgt⟩
        refine ⟨hk, ?_, ?_⟩
        · intro hk0
          rcases h0 with hk_zero | hpm
          · exact absurd hk_zero hk0
          · exact hpm
        · intro n hn1 hn2
          exact hgt n ⟨hn1, hn2⟩
    rw [h_eq]
    refine MeasurableSet.inter ?_ ?_
    · -- {ψ | k = 0 ∨ PrefixMatches x ψ k}
      by_cases hk0 : k = 0
      · -- The set is univ.
        have : {ψ : F2_boundary | k = 0 ∨ PrefixMatches x ψ k} = Set.univ := by
          ext ψ; simp [hk0]
        rw [this]; exact MeasurableSet.univ
      · -- The set equals {ψ | PrefixMatches x ψ k}.
        have : {ψ : F2_boundary | k = 0 ∨ PrefixMatches x ψ k} =
            {ψ | PrefixMatches x ψ k} := by
          ext ψ; simp [hk0]
        rw [this]
        exact prefixMatches_setOf_measurable x k
    · -- ⋂ n ∈ Ioc k |x|, {ψ | ¬ PrefixMatches x ψ n}
      exact MeasurableSet.biInter (Finset.Ioc k x.toWord.length).countable_toSet
        (fun n _ => (prefixMatches_setOf_measurable x n).compl)
  · -- k > |x|: no ψ achieves this, set is empty.
    have h_empty : {ψ : F2_boundary | common_prefix_length x ψ = k} = ∅ := by
      ext ψ
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      have hle := BusemannLocal.common_prefix_length_le x ψ
      rw [h] at hle
      exact hk hle
    rw [h_empty]
    exact MeasurableSet.empty

/-- For fixed `x : F2`, the function `ψ ↦ poisson_kernel ψ x` is
measurable.  Factors as `(fun k => 3^(-(|x| - 2k))) ∘
(common_prefix_length x ·)`; the outer map is automatically measurable
(domain `ℕ` carries the discrete σ-algebra). -/
lemma poisson_kernel_measurable (x : F2) :
    Measurable (fun ψ : F2_boundary => poisson_kernel ψ x) := by
  -- Factor through `common_prefix_length x ·`.
  have h_factor : (fun ψ : F2_boundary => poisson_kernel ψ x) =
      (fun k : ℕ => (3 : ℝ) ^ (-((x.toWord.length : ℤ) - 2 * (k : ℤ)))) ∘
        (fun ψ : F2_boundary => common_prefix_length x ψ) := by
    funext ψ
    show poisson_kernel ψ x =
      (3 : ℝ) ^ (-((x.toWord.length : ℤ) - 2 * (common_prefix_length x ψ : ℤ)))
    unfold poisson_kernel busemann
    rfl
  rw [h_factor]
  exact measurable_from_top.comp (common_prefix_length_measurable x)

/-- For any `ψ ∈ ∂F_2`, the Busemann function satisfies
`-|x| ≤ b_ψ(x) ≤ |x|`.  This follows from
`0 ≤ common_prefix_length x ψ ≤ |x|` and the formula
`b_ψ(x) = |x| − 2 · common_prefix_length x ψ`. -/
lemma busemann_abs_le (x : F2) (ψ : F2_boundary) :
    |busemann ψ x| ≤ (x.toWord.length : ℤ) := by
  unfold busemann
  have h_nn : (0 : ℤ) ≤ (common_prefix_length x ψ : ℤ) := Int.natCast_nonneg _
  have h_le : (common_prefix_length x ψ : ℤ) ≤ (x.toWord.length : ℤ) :=
    Int.ofNat_le.mpr (BusemannLocal.common_prefix_length_le x ψ)
  rcases le_or_gt ((x.toWord.length : ℤ) - 2 * (common_prefix_length x ψ : ℤ)) 0
    with h | h
  · rw [abs_of_nonpos h]; linarith
  · rw [abs_of_pos h]; linarith

/-- For any `ψ ∈ ∂F_2`, the Poisson kernel is bounded by `3^{|x|}`. -/
lemma poisson_kernel_le_pow_length (x : F2) (ψ : F2_boundary) :
    poisson_kernel ψ x ≤ (3 : ℝ) ^ x.toWord.length := by
  unfold poisson_kernel
  -- 3^{-busemann ψ x} ≤ 3^{|x|} since -busemann ψ x ≤ |x|.
  have h_bound : -busemann ψ x ≤ (x.toWord.length : ℤ) := by
    have := busemann_abs_le x ψ
    have h_neg_le : -(x.toWord.length : ℤ) ≤ busemann ψ x := neg_le_of_abs_le this
    linarith
  have h3_one_le : (1 : ℝ) ≤ 3 := by norm_num
  calc (3 : ℝ) ^ (-busemann ψ x)
      ≤ (3 : ℝ) ^ (x.toWord.length : ℤ) :=
        zpow_le_zpow_right₀ h3_one_le h_bound
    _ = (3 : ℝ) ^ x.toWord.length := by
        rw [zpow_natCast]

/-- **Wave 24D dissolution — Poisson kernel integrability.**  For
every `x ∈ F_2`, the function `ψ ↦ poisson_kernel ψ x` is integrable
against `harmonic_measure 1`.  Proof: bounded (by `3^{|x|}`) and
strongly measurable (kernel factors through the discrete-valued
`common_prefix_length x ·`); since `harmonic_measure 1` is a finite
(probability) measure, `Integrable.of_bound` closes the goal. -/
theorem poisson_kernel_integrable (x : F2) :
    MeasureTheory.Integrable
      (fun ψ : F2_boundary => poisson_kernel ψ x) (harmonic_measure 1) := by
  refine MeasureTheory.Integrable.of_bound
    (poisson_kernel_measurable x).aestronglyMeasurable
    ((3 : ℝ) ^ x.toWord.length) ?_
  refine Filter.Eventually.of_forall ?_
  intro ψ
  have h_nn : 0 ≤ poisson_kernel ψ x := poisson_kernel_nonneg x ψ
  rw [Real.norm_eq_abs, abs_of_nonneg h_nn]
  exact poisson_kernel_le_pow_length x ψ

/-! ### Wave 24D-2 — ENN cylinder identity (theorem)

The previous companion axiom `harmonic_measure_poisson_on_cylinder_enn`
is now a theorem.  Strategy:

* For `p ≥ 1` (`harmonic_measure_poisson_on_cylinder_enn_pos`):
  mechanical Bochner-to-lintegral lift of
  `harmonic_measure_poisson_on_cylinder_axiom` via
  `ENNReal.ofReal_toReal` (LHS, valid because the measure is finite)
  and `ofReal_integral_eq_lintegral_ofReal` (RHS, valid because the
  Poisson kernel is non-negative and integrable).

* For `p = 0` (`cylinder φ 0 = univ`): σ-additivity over the four
  disjoint length-1 cylinders `{ψ | ψ.val 0 = ℓ}` (for the 4 letters
  `ℓ : Fin 2 × Bool`) reduces the universe identity to a sum of
  length-1 cylinder identities, each handled by the `p ≥ 1` step.
  `F2_boundary.const` is now defined in the Wave 25 Step 2 section
  above (it is needed for the cylinder formula's base case). -/

/-! ### Wave 25 Step 3 — Poisson cylinder identity (theorem)

We dissolve the previous companion axiom
`harmonic_measure_poisson_on_cylinder_axiom` into a *theorem*
`harmonic_measure_poisson_on_cylinder` by combining:

* **Combinatorial helpers** (no measure theory): the Busemann function
  `busemann ψ x` is constant on the cylinder `I(φ, q)` whenever
  `q ≥ |x|`, since `common_prefix_length x ·` only inspects coordinates
  `0, …, |x| − 1`, all of which are pinned to `φ` on a depth-`q`
  cylinder.  Consequently the Poisson kernel `poisson_kernel · x` is
  also constant (with value `poisson_kernel φ x`) on `I(φ, q)`.

* **One deep-cylinder identity** (now a theorem; Wave 29-retry +
  Wave 35.5 dissolution of its strong-Markov leaves)
  `harmonic_measure_translation_on_deep_cylinder` (Cartwright–Soardi
  1989 / Furstenberg 1971): the *constant* (non-integral) translation
  identity
  `μ_x(I(φ, q)) = poisson_kernel φ x · μ_1(I(φ, q))` for `q ≥ |x|`.
  This is **strictly weaker** than the original companion axiom
  (deep-cylinder regime only, no integral form).

* **Downward induction** on `|x| − p`: the deep case `p ≥ |x|` is
  handled by the helpers and the admission; the inductive step
  decomposes a depth-`p` cylinder via `cylinder_eq_iUnion_extend` into
  three depth-`(p+1)` sub-cylinders and uses σ-additivity (LHS) +
  `integral_biUnion_finset` (RHS) to descend.
-/

/-- **Helper.** On a deep cylinder `I(φ, q)` (`q ≥ |x|`), the
prefix-matching predicate is invariant: for any `ψ ∈ I(φ, q)` and any
`p`, `PrefixMatches x ψ p ↔ PrefixMatches x φ p`.

Reason: `PrefixMatches x · p` requires `p ≤ |x| ≤ q`, so all coordinate
inspections `i < p ≤ |x| ≤ q` are pinned to `φ` on the cylinder. -/
private lemma prefixMatches_eq_on_deep_cylinder (x : F2) (φ ψ : F2_boundary)
    {q : ℕ} (hq : x.toWord.length ≤ q) (hψ : ψ ∈ cylinder φ q) (p : ℕ) :
    PrefixMatches x ψ p ↔ PrefixMatches x φ p := by
  rw [mem_cylinder] at hψ
  unfold PrefixMatches
  refine ⟨?_, ?_⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    intro i hi
    have hiq : i < q := lt_of_lt_of_le hi (le_trans h1 hq)
    rw [h2 i hi, hψ i hiq]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    intro i hi
    have hiq : i < q := lt_of_lt_of_le hi (le_trans h1 hq)
    rw [h2 i hi, ← hψ i hiq]

/-- **Helper.** On a deep cylinder `I(φ, q)` (`q ≥ |x|`),
`common_prefix_length x ψ = common_prefix_length x φ` for all
`ψ ∈ I(φ, q)`.

Proof: `common_prefix_length x · = Nat.findGreatest (PrefixMatches x ·)
|x|`; the predicate value at every `p ≤ |x|` is invariant by
`prefixMatches_eq_on_deep_cylinder`, so the `findGreatest` outputs
agree. -/
private lemma common_prefix_length_eq_on_deep_cylinder
    (x : F2) (φ ψ : F2_boundary)
    {q : ℕ} (hq : x.toWord.length ≤ q) (hψ : ψ ∈ cylinder φ q) :
    common_prefix_length x ψ = common_prefix_length x φ := by
  classical
  -- Apply Nat.findGreatest_eq_iff in both directions, using that the
  -- predicate is invariant on the relevant range.
  have h_iff := prefixMatches_eq_on_deep_cylinder x φ ψ hq hψ
  set m := common_prefix_length x φ with hm_def
  unfold common_prefix_length
  rw [Nat.findGreatest_eq_iff]
  -- We want `Nat.findGreatest (PrefixMatches x ψ) |x| = m`.
  -- Decompose the original `findGreatest` for φ into the same iff.
  have h_target : Nat.findGreatest (PrefixMatches x φ) x.toWord.length = m :=
    hm_def.symm
  rw [Nat.findGreatest_eq_iff] at h_target
  obtain ⟨hmle, hpos, hneg⟩ := h_target
  refine ⟨hmle, ?_, ?_⟩
  · intro hne
    exact (h_iff m).mpr (hpos hne)
  · intro n hgt hle hP
    exact hneg hgt hle ((h_iff n).mp hP)

/-- **Helper.** The Busemann function `busemann ψ x` is constant on a
deep cylinder `I(φ, q)` (`q ≥ |x|`), with value `busemann φ x`.

Direct corollary of `common_prefix_length_eq_on_deep_cylinder`. -/
private lemma busemann_eq_on_deep_cylinder
    (x : F2) (φ ψ : F2_boundary)
    {q : ℕ} (hq : x.toWord.length ≤ q) (hψ : ψ ∈ cylinder φ q) :
    busemann ψ x = busemann φ x := by
  unfold busemann
  rw [common_prefix_length_eq_on_deep_cylinder x φ ψ hq hψ]

/-- **Helper.** The Poisson kernel `poisson_kernel ψ x` is constant on
a deep cylinder `I(φ, q)` (`q ≥ |x|`), with value `poisson_kernel φ x`.
-/
private lemma poisson_kernel_eq_on_deep_cylinder
    (x : F2) (φ ψ : F2_boundary)
    {q : ℕ} (hq : x.toWord.length ≤ q) (hψ : ψ ∈ cylinder φ q) :
    poisson_kernel ψ x = poisson_kernel φ x := by
  unfold poisson_kernel
  rw [busemann_eq_on_deep_cylinder x φ ψ hq hψ]

/-- **Deep-cylinder integral identity.**  When `q ≥ |x|`, the integrand
`poisson_kernel ψ x` is constant on `I(φ, q)` (with value
`poisson_kernel φ x`), so the Bochner integral evaluates to the
constant times the measure of the cylinder.  Combined with the
deep-cylinder translation theorem above, this gives the integral
identity on every deep
cylinder. -/
private lemma harmonic_measure_poisson_on_cylinder_deep
    (x : F2) (φ : F2_boundary) (q : ℕ) (hq : x.toWord.length ≤ q) :
    (harmonic_measure x (cylinder φ q)).toReal
      = ∫ ψ in cylinder φ q, poisson_kernel ψ x ∂(harmonic_measure 1) := by
  -- The integrand equals the constant `poisson_kernel φ x` ae on the cylinder.
  have h_const_ae :
      (fun ψ : F2_boundary => poisson_kernel ψ x)
        =ᵐ[(harmonic_measure 1).restrict (cylinder φ q)]
      (fun _ : F2_boundary => poisson_kernel φ x) := by
    refine (MeasureTheory.ae_restrict_iff' (cylinder_measurable _ _)).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro ψ hψ
    exact poisson_kernel_eq_on_deep_cylinder x φ ψ hq hψ
  -- RHS = ∫_{I(φ, q)} poisson_kernel φ x ∂(harmonic_measure 1)
  --     = (μ_1(I(φ, q))).toReal · poisson_kernel φ x.
  have h_int_const :
      (∫ ψ in cylinder φ q, poisson_kernel ψ x ∂(harmonic_measure 1))
        = ∫ _ψ in cylinder φ q, poisson_kernel φ x ∂(harmonic_measure 1) :=
    MeasureTheory.integral_congr_ae h_const_ae
  rw [h_int_const, MeasureTheory.setIntegral_const,
    MeasureTheory.measureReal_def, smul_eq_mul,
    harmonic_measure_translation_on_deep_cylinder x φ q hq]
  ring

/-- **Wave 25 Step 3 dissolution — Poisson identity on cylinders.**
The Bochner-integral form of the Poisson identity on every cylinder:
for every boundary ray `φ`, every `p ≥ 1`, and every base point
`x ∈ F_2`,

  `μ_x(I(φ, p)).toReal = ∫_{I(φ, p)} p_ψ(x) dμ_1(ψ)`.

Previously a companion axiom
`harmonic_measure_poisson_on_cylinder_axiom`; now a theorem.

**Proof.** Downward induction on `n := |x| − p`.

* **Base (`n = 0`, i.e. `p ≥ |x|`):**
  `harmonic_measure_poisson_on_cylinder_deep` (combinatorial helpers
  + theorem `harmonic_measure_translation_on_deep_cylinder`,
  itself proven via the Wave 35.5 dissolution chain).

* **Inductive step (`n = k + 1`, i.e. `p < |x|`):** the depth-`p`
  cylinder decomposes as a finite disjoint union of three depth-`(p+1)`
  sub-cylinders (`cylinder_eq_iUnion_extend`).  The harmonic measure
  decomposes by σ-additivity (`MeasureTheory.measure_biUnion_finset`),
  the Bochner integral by `integral_biUnion_finset`.  Each summand
  satisfies the identity at level `p + 1` by the induction hypothesis
  (since `|x| − (p + 1) = k`). -/
theorem harmonic_measure_poisson_on_cylinder
    (x : F2) (φ : F2_boundary) (p : ℕ) (hp : 1 ≤ p) :
    (harmonic_measure x (cylinder φ p)).toReal
      = ∫ ψ in cylinder φ p, poisson_kernel ψ x ∂(harmonic_measure 1) := by
  -- Induct on `n := |x| - p` (with `p` and `φ` generalised).
  set n := x.toWord.length - p with hn_def
  clear_value n
  induction n generalizing p φ with
  | zero =>
    -- Deep case: |x| ≤ p.
    have hp_deep : x.toWord.length ≤ p := by omega
    exact harmonic_measure_poisson_on_cylinder_deep x φ p hp_deep
  | succ k ih =>
    -- |x| - p = k + 1, so |x| > p, in particular p < |x|.
    have hp_lt : p < x.toWord.length := by omega
    have hk_eq : k = x.toWord.length - (p + 1) := by omega
    -- 3-fold partition of cylinder φ p at level p + 1.
    have h_cyl_eq := cylinder_eq_iUnion_extend φ p hp
    have h_disj := cylinder_extend_pairwise_disjoint φ p hp
    -- Abbreviate sub-cylinders.
    set f : Fin 2 × Bool → Set F2_boundary :=
      fun ℓ => cylinder (extendRep φ p ℓ) (p + 1) with hf_def
    have h_meas : ∀ ℓ ∈ nonCancelExt (φ.val (p - 1)),
        MeasurableSet (f ℓ) := fun ℓ _ => cylinder_measurable _ _
    -- LHS decomposition (σ-additivity).
    have h_lhs_sum :
        harmonic_measure x (cylinder φ p) =
          ∑ ℓ ∈ nonCancelExt (φ.val (p - 1)), harmonic_measure x (f ℓ) := by
      rw [h_cyl_eq, MeasureTheory.measure_biUnion_finset h_disj h_meas]
    -- RHS decomposition (integral over disjoint biUnion).
    have h_int_on : ∀ ℓ ∈ nonCancelExt (φ.val (p - 1)),
        MeasureTheory.IntegrableOn
          (fun ψ : F2_boundary => poisson_kernel ψ x) (f ℓ)
          (harmonic_measure 1) :=
      fun ℓ _ => (poisson_kernel_integrable x).integrableOn
    have h_rhs_sum :
        (∫ ψ in cylinder φ p, poisson_kernel ψ x ∂(harmonic_measure 1))
          = ∑ ℓ ∈ nonCancelExt (φ.val (p - 1)),
              ∫ ψ in f ℓ, poisson_kernel ψ x ∂(harmonic_measure 1) := by
      rw [h_cyl_eq]
      exact MeasureTheory.integral_biUnion_finset (nonCancelExt (φ.val (p - 1)))
        h_meas h_disj h_int_on
    -- Now apply the IH at level p + 1 to each summand.
    have hp1 : 1 ≤ p + 1 := by omega
    rw [h_lhs_sum, h_rhs_sum, ENNReal.toReal_sum]
    · refine Finset.sum_congr rfl ?_
      intro ℓ _
      simp only [hf_def]
      exact ih (extendRep φ p ℓ) (p + 1) hp1 hk_eq
    · intro ℓ _
      exact MeasureTheory.measure_ne_top _ _

/-- **Lift of `harmonic_measure_poisson_on_cylinder` to ENNReal
form, for `p ≥ 1`.**  Mechanical Bochner-to-lintegral conversion using
`ENNReal.ofReal_toReal` (LHS) and `ofReal_integral_eq_lintegral_ofReal`
(RHS), justified by finiteness of `harmonic_measure x` and the
non-negativity + integrability of `poisson_kernel · x`. -/
lemma harmonic_measure_poisson_on_cylinder_enn_pos
    (x : F2) (φ : F2_boundary) (p : ℕ) (hp : 1 ≤ p) :
    harmonic_measure x (cylinder φ p)
      = ∫⁻ ψ in cylinder φ p, ENNReal.ofReal (poisson_kernel ψ x)
          ∂(harmonic_measure 1) := by
  -- Recover the ENNReal value from `.toReal` since the measure is
  -- finite (probability).
  have h_meas_ne_top : harmonic_measure x (cylinder φ p) ≠ ⊤ :=
    MeasureTheory.measure_ne_top _ _
  have h_lhs : harmonic_measure x (cylinder φ p) =
      ENNReal.ofReal (harmonic_measure x (cylinder φ p)).toReal :=
    (ENNReal.ofReal_toReal h_meas_ne_top).symm
  -- Rewrite the Bochner integral via `ofReal_integral_eq_lintegral_ofReal`.
  have h_int_restrict : MeasureTheory.Integrable
      (fun ψ : F2_boundary => poisson_kernel ψ x)
      ((harmonic_measure 1).restrict (cylinder φ p)) :=
    (poisson_kernel_integrable x).restrict
  have h_nn_restrict : 0 ≤ᵐ[(harmonic_measure 1).restrict (cylinder φ p)]
      (fun ψ : F2_boundary => poisson_kernel ψ x) :=
    Filter.Eventually.of_forall (fun ψ => poisson_kernel_nonneg x ψ)
  have h_rhs : ENNReal.ofReal
      (∫ ψ in cylinder φ p, poisson_kernel ψ x ∂(harmonic_measure 1))
        = ∫⁻ ψ in cylinder φ p, ENNReal.ofReal (poisson_kernel ψ x)
            ∂(harmonic_measure 1) :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_restrict h_nn_restrict
  rw [h_lhs, harmonic_measure_poisson_on_cylinder x φ p hp, h_rhs]

/-- **Wave 24D dissolution — Poisson identity on cylinders, ENNReal
form.**  For every `x ∈ F_2`, every boundary ray `φ`, and every
`p : ℕ` (including `p = 0`),

  `μ_x(I(φ, p)) = ∫⁻_{I(φ, p)} ofReal(p_ψ(x)) dμ_1(ψ)`.

For `p ≥ 1`: direct lift of `harmonic_measure_poisson_on_cylinder_axiom`
via `harmonic_measure_poisson_on_cylinder_enn_pos`.

For `p = 0` (`cylinder φ 0 = univ`): σ-additivity decomposes `univ`
into the four disjoint length-1 cylinders
`cylinder (F2_boundary.const ℓ) 1 = {ψ | ψ.val 0 = ℓ}` for the 4
letters `ℓ : Fin 2 × Bool`; each summand is closed by the `p = 1`
case. -/
theorem harmonic_measure_poisson_on_cylinder_enn
    (x : F2) (φ : F2_boundary) (p : ℕ) :
    harmonic_measure x (cylinder φ p)
      = ∫⁻ ψ in cylinder φ p, ENNReal.ofReal (poisson_kernel ψ x)
          ∂(harmonic_measure 1) := by
  rcases Nat.eq_zero_or_pos p with hp0 | hp_pos
  · -- p = 0 case: cylinder φ 0 = univ.
    subst hp0
    rw [cylinder_zero]
    -- Decompose univ as a finite disjoint union of length-1 cylinders.
    -- For each ℓ : Fin 2 × Bool, the set {ψ | ψ.val 0 = ℓ} = cylinder (const ℓ) 1.
    classical
    let cyl_of : (Fin 2 × Bool) → Set F2_boundary :=
      fun ℓ => cylinder (F2_boundary.const ℓ) 1
    -- Pairwise disjointness.
    have h_disj : Pairwise (Function.onFun Disjoint cyl_of) := by
      intro ℓ₁ ℓ₂ hne
      rw [Function.onFun, Set.disjoint_iff_inter_eq_empty]
      ext ψ
      simp only [cyl_of, mem_cylinder, F2_boundary.const_val,
        Nat.lt_one_iff, Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false,
        not_and]
      intro h1 h2
      have h_ℓ₁ : ψ.val 0 = ℓ₁ := h1 0 rfl
      have h_ℓ₂ : ψ.val 0 = ℓ₂ := h2 0 rfl
      exact hne (h_ℓ₁.symm.trans h_ℓ₂)
    -- Union covers univ.
    have h_union : (⋃ ℓ : Fin 2 × Bool, cyl_of ℓ) = Set.univ := by
      ext ψ
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      refine ⟨ψ.val 0, ?_⟩
      simp only [cyl_of, mem_cylinder, F2_boundary.const_val,
        Nat.lt_one_iff]
      intro i hi; subst hi; rfl
    -- Each cylinder is measurable.
    have h_meas : ∀ ℓ, MeasurableSet (cyl_of ℓ) := fun ℓ =>
      cylinder_measurable _ 1
    -- LHS via σ-additivity (over the finite type Fin 2 × Bool).
    have h_lhs : harmonic_measure x Set.univ
        = ∑ ℓ : (Fin 2 × Bool), harmonic_measure x (cyl_of ℓ) := by
      rw [← h_union, MeasureTheory.measure_iUnion h_disj h_meas, tsum_fintype]
    -- RHS via lintegral additivity over disjoint sets.
    have h_rhs : (∫⁻ ψ in Set.univ, ENNReal.ofReal (poisson_kernel ψ x)
            ∂(harmonic_measure 1))
        = ∑ ℓ : (Fin 2 × Bool),
            ∫⁻ ψ in cyl_of ℓ, ENNReal.ofReal (poisson_kernel ψ x)
              ∂(harmonic_measure 1) := by
      rw [← h_union, MeasureTheory.lintegral_iUnion h_meas h_disj, tsum_fintype]
    -- Combine: each term equals via `enn_pos`.
    rw [h_lhs, h_rhs]
    apply Finset.sum_congr rfl
    intro ℓ _
    exact harmonic_measure_poisson_on_cylinder_enn_pos x (F2_boundary.const ℓ) 1
      (le_refl 1)
  · -- p ≥ 1 case: direct lift.
    exact harmonic_measure_poisson_on_cylinder_enn_pos x φ p hp_pos

/-! **Wave 22F.3 orphan cleanup.**  Two Wave 22F.2.2 companion axioms
(`harmonic_measure_atomless` and `walk_to_boundary_limit_distribution`)
previously sat here, introduced to support the martingale route of
`translated_walk_limit_identification` in
`EnsX2026.FreeGroup.TreeBoundedHarmonicVanish`.  That route has been
replaced by a Route (a) closure that does not use these axioms, so
both were removed as orphans. -/

/-- **Q49 (Poisson representation).** For every Borel set `B ⊆ ∂F_2` and
every base point `x ∈ F_2`,

  `μ_x(B) = ∫_B p_φ(x) dμ_1(φ)`,

i.e. `μ_x` has density `p_φ(x)` (the Poisson kernel) with respect to
`μ_1`.

**Structured proof**: π-system uniqueness over cylinders via
`MeasureTheory.Measure.ext_of_generateFrom_of_iUnion`.  Define
`ν := (harmonic_measure 1).withDensity (ENNReal.ofReal ∘
poisson_kernel · x)`.  Then `ν = harmonic_measure x` as measures,
because both measures agree on cylinders (a π-system generating the
σ-algebra, `cylinders_isPiSystem` +
`borel_F2_boundary_eq_generateFrom_cylinders`) and `univ = cylinder
φ 0` provides a finite spanning sequence.  Specialising to a
measurable `B` and converting the resulting lintegral to a Bochner
integral via `integral_eq_lintegral_of_nonneg_ae` yields the claim. -/
theorem harmonic_measure_poisson_representation (x : F2)
    (B : Set F2_boundary) (hB : MeasurableSet B) :
    (harmonic_measure x B).toReal
      = ∫ φ in B, poisson_kernel φ x ∂(harmonic_measure 1) := by
  -- Name the density-weighted candidate measure.
  set ν : MeasureTheory.Measure F2_boundary :=
    (harmonic_measure 1).withDensity
      (fun ψ => ENNReal.ofReal (poisson_kernel ψ x)) with hν_def
  -- Generating family and its properties.
  let C : Set (Set F2_boundary) :=
    {S : Set F2_boundary | ∃ φ : F2_boundary, ∃ p : ℕ, S = cylinder φ p}
  have h_pi : IsPiSystem C := cylinders_isPiSystem
  have h_gen :
      (inferInstance : MeasurableSpace F2_boundary) =
        MeasurableSpace.generateFrom C :=
    borel_F2_boundary_eq_generateFrom_cylinders
  -- Both `harmonic_measure x` and `ν` agree on cylinders.
  have h_on_cyl : ∀ S ∈ C, harmonic_measure x S = ν S := by
    rintro S ⟨φ, p, rfl⟩
    have h_meas : MeasurableSet (cylinder φ p) := cylinder_measurable φ p
    rw [hν_def, MeasureTheory.withDensity_apply _ h_meas]
    exact harmonic_measure_poisson_on_cylinder_enn x φ p
  -- Spanning sequence `B n = cylinder (some φ₀) 0 = univ`.
  obtain ⟨φ₀⟩ : Nonempty F2_boundary := by
    -- `harmonic_measure 1` is a probability measure on `F2_boundary`, so
    -- `F2_boundary` is non-empty.
    by_contra h_empty
    rw [not_nonempty_iff] at h_empty
    have h_prob : (harmonic_measure 1) Set.univ = 1 :=
      (harmonic_measure_isProbabilityMeasure 1).measure_univ
    rw [Set.univ_eq_empty_iff.mpr h_empty, MeasureTheory.measure_empty] at h_prob
    exact (zero_ne_one h_prob)
  let Bseq : ℕ → Set F2_boundary := fun _ => cylinder φ₀ 0
  have hBseq_univ : ⋃ i, Bseq i = Set.univ := by
    simp only [Bseq, cylinder_zero, Set.iUnion_const]
  have hBseq_mem : ∀ i, Bseq i ∈ C := fun _ => ⟨φ₀, 0, rfl⟩
  have hBseq_fin : ∀ i, (harmonic_measure x) (Bseq i) ≠ ⊤ := fun _ =>
    MeasureTheory.measure_ne_top (harmonic_measure x) _
  -- Apply π-system uniqueness to obtain measure equality.
  have h_meas_eq : harmonic_measure x = ν :=
    MeasureTheory.Measure.ext_of_generateFrom_of_iUnion C Bseq h_gen h_pi
      hBseq_univ hBseq_mem hBseq_fin h_on_cyl
  -- Specialise to `B` and convert lintegral → Bochner integral.
  have h_meas_eq_B : harmonic_measure x B = ν B := by rw [h_meas_eq]
  -- Compute `ν B` using `withDensity_apply`.
  have h_withD : ν B =
      ∫⁻ ψ in B, ENNReal.ofReal (poisson_kernel ψ x) ∂(harmonic_measure 1) := by
    rw [hν_def, MeasureTheory.withDensity_apply _ hB]
  -- Integrability / non-negativity facts.
  have h_nn : 0 ≤ᵐ[(harmonic_measure 1).restrict B]
      (fun ψ => poisson_kernel ψ x) :=
    Filter.Eventually.of_forall (fun ψ => poisson_kernel_nonneg x ψ)
  have h_int : MeasureTheory.Integrable
      (fun ψ => poisson_kernel ψ x) ((harmonic_measure 1).restrict B) :=
    (poisson_kernel_integrable x).restrict
  -- Convert Bochner integral on the right-hand side to a lintegral.
  have h_bochner :
      ∫ ψ in B, poisson_kernel ψ x ∂(harmonic_measure 1)
        = (∫⁻ ψ in B, ENNReal.ofReal (poisson_kernel ψ x)
            ∂(harmonic_measure 1)).toReal := by
    rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae h_nn
      h_int.aestronglyMeasurable]
  rw [h_meas_eq_B, h_withD, h_bochner]

/-! ### Poisson integral on `F_2`

Concrete candidate Dirichlet solution, on the interior `F_2`.  For a
continuous boundary datum `g : ∂F_2 → ℝ`, the Poisson integral

  `(P g)(x) := ∫_{∂F_2} g(φ) · p_φ(x) dμ_1(φ)`

defines a real-valued function on `F_2`.  It is the canonical harmonic
extension of `g` to the interior.

Refactored from the Wave 13A / 15 axiomatic `dirichlet_solution` into
a real `noncomputable def`. -/

/-- **The Poisson integral of a boundary datum `g`** evaluated at
`x ∈ F_2`.  Defined as the Bochner integral

  `∫_{∂F_2} g(φ) · p_φ(x) dμ_1(φ)`

where `μ_1 = harmonic_measure 1` is the exit measure based at the
identity.  A real `noncomputable def` (no axiom). -/
noncomputable def poisson_integral (g : F2_boundary → ℝ) (x : F2) : ℝ :=
  ∫ φ, g φ * poisson_kernel φ x ∂(harmonic_measure 1)

/-- **Unfolding spec for `poisson_integral`.**  By definition, the
Poisson integral at `x` is the Bochner integral of `g φ · p_φ(x)`. -/
lemma poisson_integral_def (g : F2_boundary → ℝ) (x : F2) :
    poisson_integral g x
      = ∫ φ, g φ * poisson_kernel φ x ∂(harmonic_measure 1) := rfl

/-! #### Harmonicity of the Poisson integral

For every `x ∈ F_2`, the value `poisson_integral g x` satisfies the
pointwise 1+3 harmonic relation of `Busemann.PointwiseHarmonic`:

  `poisson_integral g yφ + Σ_{y ∈ T} poisson_integral g y
    = 4 · poisson_integral g x`

for the toward-φ neighbour `yφ` and the 3-element outward set `T`,
for ANY choice of a reference ray `φ ∈ ∂F_2`.  This follows from the
pointwise identity `p_φ(yφ) + Σ_{y ∈ T} p_φ(y) = 4 · p_φ(x)`
(`poisson_kernel_harmonic_eq`, Q39) by linearity of the integral.

**Companion axiom — integrability bridge.** Proving the harmonicity in
full requires integrability of `ψ ↦ g ψ · p_ψ y` for each neighbour `y`
under `harmonic_measure 1`.  This follows from `poisson_kernel_integrable`
combined with boundedness of `g` on the compact `∂F_2` — a bridge we
record below as a companion spec.  For continuous (or even bounded
measurable) `g`, the bridge holds.  -/

/-- **Poisson-integral integrand integrability (Wave 22B cleanup).**  For
every continuous `g : F2_boundary → ℝ`, the integrand
`ψ ↦ g ψ * poisson_kernel ψ y` is integrable against `harmonic_measure 1`
for every `y ∈ F_2`.

**Proof.** Compactness of `∂F_2` (`F2_boundary.compactSpace`, Q46)
together with continuity of `g` gives `IsCompact (Set.range g)`, whence
`‖g ψ‖ ≤ C` for some `C ≥ 0`.  `OpensMeasurableSpace F2_boundary`
(`F2_boundary.opensMeasurableSpace`) turns `Continuous g` into
`AEStronglyMeasurable g (harmonic_measure 1)` via
`Continuous.stronglyMeasurable` (ℝ is second-countable).  Combined with
`poisson_kernel_integrable`, the Mathlib lemma `Integrable.bdd_mul`
delivers integrability of the product.  Closes axiom A4 from the
Cleaner's Wave 22B audit. -/
theorem poisson_integral_integrand_integrable (g : F2_boundary → ℝ)
    (hg : Continuous g) (y : F2) :
    MeasureTheory.Integrable
      (fun ψ : F2_boundary => g ψ * poisson_kernel ψ y) (harmonic_measure 1) := by
  -- Bound `g` uniformly via compactness of `∂F_2`.
  have h_range_compact : IsCompact (Set.range g) := isCompact_range hg
  obtain ⟨C, hC⟩ := h_range_compact.isBounded.exists_norm_le
  have hg_bdd : ∀ ψ, ‖g ψ‖ ≤ C := fun ψ => hC (g ψ) ⟨ψ, rfl⟩
  -- Strong measurability of `g` (target ℝ is second-countable).
  have hg_meas : MeasureTheory.AEStronglyMeasurable g (harmonic_measure 1) :=
    hg.stronglyMeasurable.aestronglyMeasurable
  -- Integrability of the Poisson kernel factor.
  have h_p_int : MeasureTheory.Integrable
      (fun ψ : F2_boundary => poisson_kernel ψ y) (harmonic_measure 1) :=
    poisson_kernel_integrable y
  -- Bounded × integrable = integrable.
  exact h_p_int.bdd_mul hg_meas (Filter.Eventually.of_forall hg_bdd)

/-- **Partition-invariance of the 1+3 neighbour sum (Wave 22B cleanup).**
For every base ray `ψ ∈ ∂F_2` and every adjacent-vertex partition
`(yφ, T)` of `x` arising from a reference ray `φ` (i.e. `yφ` is the
unique toward-`φ` neighbour and `T` is a 3-element set of outward-for-`φ`
neighbours), the Poisson-kernel sum satisfies

  `poisson_kernel ψ yφ + Σ_{y ∈ T} poisson_kernel ψ y
    = 4 · poisson_kernel ψ x`.

Mathematical content: the 4-regular Cayley graph of `F_2` has exactly
four neighbours at every vertex.  The partition `{yφ} ∪ T` (chosen
for ray `φ`) and the partition `{yψ} ∪ T_ψ` (chosen for ray `ψ`) both
enumerate these four neighbours (as finsets), so the sum
`poisson_kernel ψ yφ + Σ_{y ∈ T} poisson_kernel ψ y` equals the
`ψ`-version `poisson_kernel ψ yψ + Σ_{y ∈ T_ψ} poisson_kernel ψ y
  = 4 · poisson_kernel ψ x` by `poisson_kernel_neighbour_sum` applied
for `ψ`.

**Proof.** Apply `poisson_kernel_harmonic_eq ψ x` to obtain a
`ψ`-partition `(yψ, Tψ)` of the four neighbours of `x`, satisfying the
sum identity `poisson_kernel ψ yψ + Σ_{y ∈ Tψ} poisson_kernel ψ y
  = 4 · poisson_kernel ψ x`.  Show `insert yφ T = insert yψ Tψ` as
finsets: both are 4-element subsets of `{y | Adj x y}`, and the
4-regularity of the Cayley graph (via `busemann_three_plus_neighbours`
+ uniqueness of the toward-`φ`/`ψ` neighbour) forces each to contain
every adjacent vertex.  Then `Finset.sum` over the equal inserts gives
the identity.  Closes axiom A5 from the Cleaner's Wave 22B audit. -/
theorem poisson_kernel_sum_neighbours_partition_invariant
    (ψ φ : ∂F2) (x yφ : F2) (T : Finset F2)
    (h_adj : (EnsX2026.Cayley.cayley_graph F2_generating_set).Adj x yφ)
    (h_yφ_bus : busemann φ yφ = busemann φ x - 1)
    (h_Tcard : T.card = 3)
    (h_T_mem : ∀ y ∈ T, (EnsX2026.Cayley.cayley_graph F2_generating_set).Adj x y ∧
                         busemann φ y = busemann φ x + 1)
    (h_yφ_notmem : yφ ∉ T) :
    poisson_kernel ψ yφ + (∑ y ∈ T, poisson_kernel ψ y)
      = 4 * poisson_kernel ψ x := by
  classical
  -- Extract a `ψ`-partition `(yψ, Tψ)` of the four neighbours of `x`.
  obtain ⟨yψ, Tψ, h_yψ_adj, h_yψ_bus, h_Tψcard, h_Tψ_mem, h_yψ_notmem, h_sum_ψ⟩ :=
    poisson_kernel_harmonic_eq ψ x
  -- Characterise membership in `insert yφ T` as "adjacent to x".
  -- Forward direction: yφ and each y ∈ T are adjacent to x.
  have h_insert_subset_adj :
      ∀ z ∈ insert yφ T,
        (EnsX2026.Cayley.cayley_graph F2_generating_set).Adj x z := by
    intro z hz
    rcases Finset.mem_insert.mp hz with heq | hmem
    · exact heq ▸ h_adj
    · exact (h_T_mem z hmem).1
  -- Backward direction: every adjacent `z` lies in `insert yφ T`.
  -- Strategy: use `busemann_three_plus_neighbours φ x` to get a cover `T_cov`;
  -- show T = T_cov (card + subset) and yφ = φ-toward neighbour.
  obtain ⟨T_cov, h_Tcov_card, h_Tcov_mem, h_Tcov_cover⟩ :=
    busemann_three_plus_neighbours φ x
  -- `T ⊆ T_cov`: every `z ∈ T` has `busemann = +1`, so it's in `T_cov`
  -- (not the toward-φ branch).
  have h_T_sub : T ⊆ T_cov := by
    intro z hz
    have hz_adj : (EnsX2026.Cayley.cayley_graph F2_generating_set).Adj x z :=
      (h_T_mem z hz).1
    have hz_bus : busemann φ z = busemann φ x + 1 := (h_T_mem z hz).2
    rcases h_Tcov_cover z hz_adj with hz_phi | hz_in
    · exfalso
      have : busemann φ x + 1 = busemann φ x - 1 := hz_bus.symm.trans hz_phi
      have : (2 : ℤ) = 0 := by linarith
      exact absurd this (by decide)
    · exact hz_in
  have h_T_eq_cov : T = T_cov :=
    Finset.eq_of_subset_of_card_le h_T_sub (by rw [h_Tcov_card, h_Tcard])
  have h_adj_subset_insert :
      ∀ z, (EnsX2026.Cayley.cayley_graph F2_generating_set).Adj x z →
        z ∈ insert yφ T := by
    intro z hz_adj
    rcases h_Tcov_cover z hz_adj with hz_phi | hz_in
    · -- z is the toward-φ neighbour, equal to yφ by uniqueness.
      refine Finset.mem_insert.mpr (Or.inl ?_)
      obtain ⟨y_uniq, _hprop, h_uniq⟩ := busemann_neighbour_structure φ x
      have hz_eq : z = y_uniq := h_uniq z ⟨hz_adj, hz_phi⟩
      have hyφ_eq : yφ = y_uniq := h_uniq yφ ⟨h_adj, h_yφ_bus⟩
      rw [hz_eq, ← hyφ_eq]
    · refine Finset.mem_insert.mpr (Or.inr ?_)
      rw [h_T_eq_cov]; exact hz_in
  -- Similarly, characterise `insert yψ Tψ` via adjacency.
  have h_insertψ_subset_adj :
      ∀ z ∈ insert yψ Tψ,
        (EnsX2026.Cayley.cayley_graph F2_generating_set).Adj x z := by
    intro z hz
    rcases Finset.mem_insert.mp hz with heq | hmem
    · exact heq ▸ h_yψ_adj
    · exact (h_Tψ_mem z hmem).1
  obtain ⟨Tψ_cov, h_Tψcov_card, _h_Tψcov_mem, h_Tψcov_cover⟩ :=
    busemann_three_plus_neighbours ψ x
  have h_Tψ_sub : Tψ ⊆ Tψ_cov := by
    intro z hz
    have hz_adj : (EnsX2026.Cayley.cayley_graph F2_generating_set).Adj x z :=
      (h_Tψ_mem z hz).1
    have hz_bus : busemann ψ z = busemann ψ x + 1 := (h_Tψ_mem z hz).2
    rcases h_Tψcov_cover z hz_adj with hz_phi | hz_in
    · exfalso
      have : busemann ψ x + 1 = busemann ψ x - 1 := hz_bus.symm.trans hz_phi
      have : (2 : ℤ) = 0 := by linarith
      exact absurd this (by decide)
    · exact hz_in
  have h_Tψ_eq_cov : Tψ = Tψ_cov :=
    Finset.eq_of_subset_of_card_le h_Tψ_sub (by rw [h_Tψcov_card, h_Tψcard])
  have h_adj_subset_insertψ :
      ∀ z, (EnsX2026.Cayley.cayley_graph F2_generating_set).Adj x z →
        z ∈ insert yψ Tψ := by
    intro z hz_adj
    rcases h_Tψcov_cover z hz_adj with hz_phi | hz_in
    · refine Finset.mem_insert.mpr (Or.inl ?_)
      obtain ⟨y_uniq, _hprop, h_uniq⟩ := busemann_neighbour_structure ψ x
      have hz_eq : z = y_uniq := h_uniq z ⟨hz_adj, hz_phi⟩
      have hyψ_eq : yψ = y_uniq := h_uniq yψ ⟨h_yψ_adj, h_yψ_bus⟩
      rw [hz_eq, ← hyψ_eq]
    · refine Finset.mem_insert.mpr (Or.inr ?_)
      rw [h_Tψ_eq_cov]; exact hz_in
  -- The two finsets `insert yφ T` and `insert yψ Tψ` are equal.
  have h_insert_eq : insert yφ T = insert yψ Tψ := by
    apply Finset.ext
    intro z
    constructor
    · intro hz
      exact h_adj_subset_insertψ z (h_insert_subset_adj z hz)
    · intro hz
      exact h_adj_subset_insert z (h_insertψ_subset_adj z hz)
  -- Now rewrite both sides using `Finset.sum_insert`, then equate via
  -- `h_insert_eq`.
  have h_lhs :
      poisson_kernel ψ yφ + (∑ y ∈ T, poisson_kernel ψ y)
        = ∑ y ∈ insert yφ T, poisson_kernel ψ y :=
    (Finset.sum_insert h_yφ_notmem).symm
  have h_sum_ψ' :
      (∑ y ∈ insert yψ Tψ, poisson_kernel ψ y) = 4 * poisson_kernel ψ x := by
    rw [Finset.sum_insert h_yψ_notmem]; exact h_sum_ψ
  rw [h_lhs, h_insert_eq]
  exact h_sum_ψ'

/-- **Pointwise harmonicity of the Poisson integral.**  For every `x ∈ F_2`
and every reference boundary ray `φ ∈ ∂F_2`, the Poisson integral satisfies
the 1+3 harmonic relation at `x`:

  `poisson_integral g yφ + Σ_{y ∈ T} poisson_integral g y
    = 4 · poisson_integral g x`

where `yφ` is the unique toward-`φ` neighbour and `T` is a 3-element set
of outward neighbours.

**Proof.** By `poisson_kernel_harmonic_eq` applied for a fixed reference
ray `φ`, the Cayley graph's neighbour structure is partitioned as
`{yφ} ∪ T` with `|T| = 3` and matching Busemann values.  For any
`ψ ∈ ∂F_2`, the Poisson-kernel sum over this partition equals
`4 · poisson_kernel ψ x` by
`poisson_kernel_sum_neighbours_partition_invariant`.  Linearity of
the integral (`MeasureTheory.integral_add`,
`MeasureTheory.integral_finset_sum`,
`MeasureTheory.integral_const_mul`) then lifts the pointwise identity
to the integrated quantity. -/
theorem poisson_integral_pointwise_harmonic
    (g : F2_boundary → ℝ) (hg : Continuous g) (φ : ∂F2) (x : F2) :
    ∃ (yφ : F2) (T : Finset F2),
      (EnsX2026.Cayley.cayley_graph F2_generating_set).Adj x yφ ∧
      busemann φ yφ = busemann φ x - 1 ∧
      T.card = 3 ∧
      (∀ y ∈ T, (EnsX2026.Cayley.cayley_graph F2_generating_set).Adj x y ∧
                busemann φ y = busemann φ x + 1) ∧
      yφ ∉ T ∧
      poisson_integral g yφ + (∑ y ∈ T, poisson_integral g y)
        = 4 * poisson_integral g x := by
  classical
  obtain ⟨yφ, T, hyφ_adj, hyφ_bus, hTcard, hT_mem, hyφ_notmem, _⟩ :=
    poisson_kernel_harmonic_eq φ x
  refine ⟨yφ, T, hyφ_adj, hyφ_bus, hTcard, hT_mem, hyφ_notmem, ?_⟩
  -- Unfold the three occurrences of `poisson_integral`.
  show (∫ ψ, g ψ * poisson_kernel ψ yφ ∂(harmonic_measure 1))
        + (∑ y ∈ T, ∫ ψ, g ψ * poisson_kernel ψ y ∂(harmonic_measure 1))
      = 4 * ∫ ψ, g ψ * poisson_kernel ψ x ∂(harmonic_measure 1)
  -- Integrability witnesses.
  have h_int_yφ : MeasureTheory.Integrable
      (fun ψ => g ψ * poisson_kernel ψ yφ) (harmonic_measure 1) :=
    poisson_integral_integrand_integrable g hg yφ
  have h_int_T : ∀ y ∈ T, MeasureTheory.Integrable
      (fun ψ => g ψ * poisson_kernel ψ y) (harmonic_measure 1) := fun y _ =>
    poisson_integral_integrand_integrable g hg y
  -- Pull the finite sum inside the integral.
  have h_sum_in : (∑ y ∈ T, ∫ ψ, g ψ * poisson_kernel ψ y ∂(harmonic_measure 1))
      = ∫ ψ, (∑ y ∈ T, g ψ * poisson_kernel ψ y) ∂(harmonic_measure 1) := by
    rw [MeasureTheory.integral_finset_sum T (fun y hy => h_int_T y hy)]
  rw [h_sum_in]
  -- Combine the two integrals on the LHS via `integral_add`.
  rw [← MeasureTheory.integral_add h_int_yφ
        (MeasureTheory.integrable_finset_sum _ (fun y hy => h_int_T y hy))]
  -- Factor the `4 *` on the RHS into the integral.
  rw [show (4 : ℝ) * ∫ ψ, g ψ * poisson_kernel ψ x ∂(harmonic_measure 1)
        = ∫ ψ, 4 * (g ψ * poisson_kernel ψ x) ∂(harmonic_measure 1) from
      (MeasureTheory.integral_const_mul _ _).symm]
  -- The integrands agree pointwise.
  refine MeasureTheory.integral_congr_ae ?_
  refine Filter.Eventually.of_forall (fun ψ => ?_)
  have h_partition_invariant :
      poisson_kernel ψ yφ + (∑ y ∈ T, poisson_kernel ψ y)
        = 4 * poisson_kernel ψ x :=
    poisson_kernel_sum_neighbours_partition_invariant ψ φ x yφ T
      hyφ_adj hyφ_bus hTcard hT_mem hyφ_notmem
  calc g ψ * poisson_kernel ψ yφ
        + ∑ y ∈ T, g ψ * poisson_kernel ψ y
      = g ψ * (poisson_kernel ψ yφ + ∑ y ∈ T, poisson_kernel ψ y) := by
        rw [← Finset.mul_sum]; ring
    _ = g ψ * (4 * poisson_kernel ψ x) := by rw [h_partition_invariant]
    _ = 4 * (g ψ * poisson_kernel ψ x) := by ring

/-! ### Q50 — Dirichlet problem on `\overline{F_2}` -/

/-- **Coercion injectivity on `F2_boundary`** (Wave 24B).  The concrete
inclusion `F2_boundary ↪ F2bar` (`F2_boundary.coeToF2bar`) is injective:
distinct boundary rays map to distinct points of the compactification.

**Proof.** Equality of coercions implies equality at every coordinate of
the underlying `F2bar` sequence, which by `fbgToExtGen_injective` forces
equality at every coordinate of the underlying `Fin 2 × Bool` sequence. -/
theorem F2_boundary_coeToF2bar_injective :
    Function.Injective
      (fun ψ : F2_boundary => ((ψ : F2_boundary) : F2bar)) :=
  F2_boundary_to_F2bar_injective

/-- **Q50 definition.** The candidate Dirichlet solution: `g`'s Poisson
integral on `F_2`, extended by `g` on the boundary.

Defined by a three-way `Classical.choice` dispatch on `y : F2bar`:
1. If `y = (ψ : F2bar)` for some `ψ : F2_boundary`, return `g ψ`.
   (Well-defined by injectivity of the coercion.)
2. Else if `y = (x : F2bar)` for some `x : F2`, return
   `poisson_integral g x`.
3. Else return `0` (the "junk" value, never reached on the image
   of `F_2 ⊔ ∂F_2 ↪ F2bar`).

This is a genuine `noncomputable def` — no longer an axiom. -/
noncomputable def dirichlet_solution (g : F2_boundary → ℝ) (y : F2bar) : ℝ :=
  open Classical in
  if hψ : ∃ ψ : F2_boundary, ((ψ : F2_boundary) : F2bar) = y then
    g hψ.choose
  else if hx : ∃ x : F2, ((x : F2) : F2bar) = y then
    poisson_integral g hx.choose
  else 0

/-- **Boundary agreement spec for `dirichlet_solution`.**  The Dirichlet
solution agrees with `g` on the boundary inclusion
`∂F_2 ↪ \overline{F_2}`.

**Proof (no longer an axiom).** Unfold `dirichlet_solution`: the
`∃ ψ' : F2_boundary, (ψ' : F2bar) = (ψ : F2bar)` branch activates
(witnessed by `ψ` itself).  Classical choice picks some such `ψ'`,
and by injectivity of the coercion (`F2_boundary_coeToF2bar_injective`)
we have `ψ' = ψ`, hence `g ψ' = g ψ`. -/
theorem dirichlet_solution_boundary_axiom
    (g : F2_boundary → ℝ) (ψ : F2_boundary) :
    dirichlet_solution g ((ψ : F2_boundary) : F2bar) = g ψ := by
  classical
  have hex : ∃ ψ' : F2_boundary,
      ((ψ' : F2_boundary) : F2bar) = ((ψ : F2_boundary) : F2bar) := ⟨ψ, rfl⟩
  unfold dirichlet_solution
  rw [dif_pos hex]
  have hchoose : hex.choose = ψ :=
    F2_boundary_coeToF2bar_injective hex.choose_spec
  rw [hchoose]

/-! #### Structural decomposition of the Dirichlet existence/uniqueness

Existence is proved by exhibiting `dirichlet_solution g` as a witness,
whose three required properties (continuity, harmonicity, boundary
agreement) are each stated as a leaf lemma.  Uniqueness is a discrete
maximum-principle argument, packaged as a single leaf lemma. -/

/-! #### Interior evaluation of `dirichlet_solution` (moved up for Wave 30)

On the interior `F_2 ↪ F2bar`, the Dirichlet solution coincides with
the Poisson integral — this is the content of the `F2`-branch of the
`Classical.choice` dispatch in the definition, cleaned up by two
companion axioms (disjointness of the two coercion images, and
injectivity of the `F_2`-coercion).  Moved before
`dirichlet_solution_continuousAt_boundary_axiom` so the latter can
reduce to `poisson_integral g x` for the F2-image case. -/

/-- **Disjointness of coercion images** (Wave 24B).  The concrete
inclusions `F_2 ↪ F2bar` and `∂F_2 ↪ F2bar` have disjoint images.

**Proof.** Any image of `x : F_2` has `(F2_to_F2bar x).val (toWord.length) =
ExtGen.one` (padding kicks in at the end of the reduced word), whereas the
image of any `ψ : F_2_boundary` has *no* `ExtGen.one` entry by construction.
Hence the two images cannot coincide. -/
theorem F2_F2_boundary_images_disjoint :
    ∀ (x : F2) (ψ : F2_boundary),
      ((x : F2) : F2bar) ≠ ((ψ : F2_boundary) : F2bar) := by
  intro x ψ heq
  -- Unfold the coercions to their concrete underlying definitions.
  change F2_to_F2bar x = F2_boundary_to_F2bar ψ at heq
  -- The F_2 image is not in F2boundary…
  have hx_not : F2_to_F2bar x ∉ F2bar.F2boundary := F2_to_F2bar_notMem_F2boundary x
  -- …but the boundary image is.
  have hψ_in : F2_boundary_to_F2bar ψ ∈ F2bar.F2boundary :=
    F2_boundary_to_F2bar_mem_F2boundary ψ
  exact hx_not (heq ▸ hψ_in)

/-- **Coercion injectivity on `F_2`** (Wave 24B).  The concrete inclusion
`F_2 ↪ F2bar` (`F2.coeToF2bar`) is injective: distinct free-group elements
map to distinct points of the compactification.

**Proof.** Equality of `F2_to_F2bar x = F2_to_F2bar y` implies equality at
every coordinate; restricting to indices `< x.toWord.length` and using
`fbgToExtGen_injective`, we conclude that `x.toWord` and `y.toWord` agree on
their common prefix, and the lengths must match (else the shorter word's
"out-of-range" position becomes `one` while the longer word's lookup gives a
non-`one` letter).  Then `FreeGroup.toWord_injective` finishes. -/
theorem F2_coeToF2bar_injective :
    Function.Injective
      (fun x : F2 => ((x : F2) : F2bar)) := by
  intro x y heq
  change F2_to_F2bar x = F2_to_F2bar y at heq
  -- Step 1: extract pointwise equality of the underlying sequences.
  have hpt : ∀ n, (F2_to_F2bar x).val n = (F2_to_F2bar y).val n :=
    fun n => congrArg (fun z : F2bar => z.val n) heq
  -- Step 2: the lengths must agree.
  have hlen : x.toWord.length = y.toWord.length := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hpx : (F2_to_F2bar x).val x.toWord.length = ExtGen.one := by
        show (if h : _ < x.toWord.length then _ else ExtGen.one) = ExtGen.one
        simp
      have hpy : (F2_to_F2bar y).val x.toWord.length ≠ ExtGen.one := by
        show (if h : x.toWord.length < y.toWord.length then
              fbgToExtGen (y.toWord[x.toWord.length]'h) else ExtGen.one) ≠ ExtGen.one
        rw [dif_pos hlt]
        exact fbgToExtGen_ne_one _
      exact hpy ((hpt _).symm.trans hpx)
    · have hpy : (F2_to_F2bar y).val y.toWord.length = ExtGen.one := by
        show (if h : _ < y.toWord.length then _ else ExtGen.one) = ExtGen.one
        simp
      have hpx : (F2_to_F2bar x).val y.toWord.length ≠ ExtGen.one := by
        show (if h : y.toWord.length < x.toWord.length then
              fbgToExtGen (x.toWord[y.toWord.length]'h) else ExtGen.one) ≠ ExtGen.one
        rw [dif_pos hgt]
        exact fbgToExtGen_ne_one _
      exact hpx ((hpt _).trans hpy)
  -- Step 3: reduced words match letter-by-letter.
  have hword : x.toWord = y.toWord := by
    apply List.ext_getElem hlen
    intro n hn hny
    have := hpt n
    show x.toWord[n] = y.toWord[n]
    rw [show (F2_to_F2bar x).val n = fbgToExtGen (x.toWord[n]'hn) from
          (dif_pos hn : (if h : n < x.toWord.length then
            fbgToExtGen (x.toWord[n]'h) else ExtGen.one) = _),
        show (F2_to_F2bar y).val n = fbgToExtGen (y.toWord[n]'hny) from
          (dif_pos hny : (if h : n < y.toWord.length then
            fbgToExtGen (y.toWord[n]'h) else ExtGen.one) = _)] at this
    exact fbgToExtGen_injective this
  exact _root_.FreeGroup.toWord_injective hword

/-- **Interior evaluation of `dirichlet_solution`.**  For every
`y : F_2`, the Dirichlet solution at the image `((y : F2) : F2bar)`
equals the Poisson integral at `y`.

**Proof (no longer an axiom).** Unfold `dirichlet_solution`.  The
first branch (`∃ ψ : F2_boundary, (ψ : F2bar) = ((y : F2) : F2bar)`)
fails by `F2_F2_boundary_images_disjoint`.  The second branch fires,
and Classical choice picks some `y' : F_2` with the same image;
injectivity of the `F_2`-coercion forces `y' = y`. -/
theorem dirichlet_solution_on_F2_eq_poisson_integral
    (g : F2_boundary → ℝ) (y : F2) :
    dirichlet_solution g ((y : F2) : F2bar) = poisson_integral g y := by
  classical
  unfold dirichlet_solution
  have hψ_none : ¬ ∃ ψ : F2_boundary,
      ((ψ : F2_boundary) : F2bar) = ((y : F2) : F2bar) := by
    rintro ⟨ψ, hψ⟩
    exact F2_F2_boundary_images_disjoint y ψ hψ.symm
  rw [dif_neg hψ_none]
  have hx_some : ∃ x : F2, ((x : F2) : F2bar) = ((y : F2) : F2bar) := ⟨y, rfl⟩
  rw [dif_pos hx_some]
  have hchoose : hx_some.choose = y :=
    F2_coeToF2bar_injective hx_some.choose_spec
  rw [hchoose]

/-! #### Wave 30 — boundary continuity of the Dirichlet solution

The previous narrow admission `dirichlet_solution_continuousAt_boundary_axiom`
is dissolved into a *theorem* via a quantitative cylinder-concentration
estimate combined with the Heine–Cantor uniform continuity of `g` on the
compact F2bar boundary.

**Strategy** (per Cartwright–Soardi 1989; cf. Woess 2000 §1.D):

* For `y ∈ F_2` close to `φ` in `F2bar`, the F2bar metric forces
  `common_prefix_length y φ ≥ p + 1` for some large `p`.  By
  `harmonic_measure_poisson_representation`, the cylinder complement
  `μ_y(univ \ I(φ, q))` is bounded by `3^{2(q-1) - |y|}` for any
  `q < common_prefix_length y φ`, since `p_ψ(y) ≤ 3^{2(q-1) - |y|}`
  uniformly on `univ \ I(φ, q)`.

* By Heine–Cantor on the compact `F2bar.F2boundary`, the lift of `g` is
  uniformly continuous: pick `q` with the cylinder-radius `exp(-q) <
  δ'(ε/2)`, ensuring `|g(ψ) - g(φ)| < ε/2` for ψ ∈ I(φ, q).

* Pick `p ≥ 2q + N` where `N` is large enough that `2M · 3^{-N-2} < ε/4`.

* Final triangle inequality on `poisson_integral g y - g(φ) =
  ∫ (g(ψ) - g(φ)) · p_ψ(y) dμ_1(ψ)`, splitting on `I(φ, q)` vs its
  complement. -/

/-- **F1 (cylinder concentration).** For `y : F_2` and `φ : F2_boundary`
with `common_prefix_length y φ` strictly greater than `q`, the harmonic
measure `μ_y` concentrates on the cylinder `I(φ, q)`:

`(harmonic_measure y (univ \ cylinder φ q)).toReal ≤ 3^{2(q-1) - |y|}`.

**Proof.**  By `harmonic_measure_poisson_representation`,
`(μ_y B).toReal = ∫_B p_ψ(y) dμ_1(ψ)`.  For `ψ ∈ univ \ cylinder φ q`,
`ψ` disagrees with `φ` at some `i < q`; since `y` agrees with `φ` at
all `i < common_prefix_length y φ` and `i < q ≤ common_prefix_length y φ`,
we get `y` disagrees with `ψ` at `i`, hence
`common_prefix_length y ψ < q`, so `b_ψ(y) ≥ |y| - 2(q-1)`, so
`p_ψ(y) ≤ 3^{2(q-1) - |y|}`.  Bound the integral. -/
private lemma harmonic_measure_complement_cylinder_bound
    (y : F2) (φ : F2_boundary) (q : ℕ)
    (hq : q < common_prefix_length y φ) :
    (harmonic_measure y (Set.univ \ cylinder φ q)).toReal
      ≤ (3 : ℝ) ^ (2 * (q : ℤ) - 2 - (y.toWord.length : ℤ)) := by
  classical
  set B : Set F2_boundary := Set.univ \ cylinder φ q with hB_def
  have hBmeas : MeasurableSet B :=
    (MeasurableSet.univ).diff (cylinder_measurable φ q)
  -- Poisson representation.
  rw [harmonic_measure_poisson_representation y B hBmeas]
  -- The PrefixMatches at common_prefix_length y φ.
  have h_pm_y_phi := BusemannLocal.prefixMatches_common_prefix_length y φ
  -- For every ψ ∈ B, common_prefix_length y ψ ≤ q - 1.
  have h_cpl_bound : ∀ ψ ∈ B, common_prefix_length y ψ + 1 ≤ q := by
    intro ψ hψ
    -- ψ ∈ B = univ \ cylinder φ q, so ψ disagrees with φ at some i < q.
    have hψ_not : ψ ∉ cylinder φ q := hψ.2
    rw [mem_cylinder] at hψ_not
    push_neg at hψ_not
    obtain ⟨i, hi_lt, hi_ne⟩ := hψ_not
    -- hi_ne : ψ.val i ≠ φ.val i.
    -- Since q ≤ common_prefix_length y φ, we have i < common_prefix_length y φ.
    have hi_lt_cpl : i < common_prefix_length y φ := lt_of_lt_of_le hi_lt hq.le
    -- y agrees with φ at index i: y.toWord[i]? = some (φ.val i).
    have hy_phi : y.toWord[i]? = some (φ.val i) := by
      have := h_pm_y_phi.2 i hi_lt_cpl
      exact this
    -- So y disagrees with ψ at index i: y.toWord[i]? ≠ some (ψ.val i).
    have hy_psi : y.toWord[i]? ≠ some (ψ.val i) := by
      rw [hy_phi]
      intro h
      apply hi_ne
      exact (Option.some.inj h).symm
    -- Hence ¬ PrefixMatches y ψ (i+1).
    have h_not_pm : ¬ PrefixMatches y ψ (i + 1) := by
      rintro ⟨_, h⟩
      have := h i (Nat.lt_succ_self i)
      exact hy_psi this
    -- By Nat.findGreatest, common_prefix_length y ψ < i + 1, so ≤ i.
    -- Actually: common_prefix_length y ψ = Nat.findGreatest (PrefixMatches y ψ) |y|.
    -- Goal: common_prefix_length y ψ + 1 ≤ q, i.e., common_prefix_length y ψ ≤ q - 1.
    -- We have ¬ PrefixMatches y ψ (i+1) with i+1 ≤ q, so all PrefixMatches predicates
    -- in [i+1, |y|] would force ≤ i.  But NatFindGreatest may not directly use this.
    -- Better: show common_prefix_length y ψ ≤ i.
    have hcpl_le_i : common_prefix_length y ψ ≤ i := by
      by_contra h_lt
      push_neg at h_lt  -- i < common_prefix_length y ψ
      -- PrefixMatches y ψ (common_prefix_length y ψ) holds, hence PrefixMatches y ψ (i+1).
      have h_pm_y_psi := BusemannLocal.prefixMatches_common_prefix_length y ψ
      have h_pm_succ : PrefixMatches y ψ (i + 1) := by
        refine ⟨?_, ?_⟩
        · exact le_trans h_lt h_pm_y_psi.1
        · intro j hj
          exact h_pm_y_psi.2 j (lt_of_lt_of_le hj h_lt)
      exact h_not_pm h_pm_succ
    omega
  -- Bound the integrand: p_ψ(y) ≤ 3^(2(q-1) - |y|) for ψ ∈ B.
  have h_integrand_bound : ∀ ψ ∈ B,
      poisson_kernel ψ y ≤ (3 : ℝ) ^ (2 * (q : ℤ) - 2 - (y.toWord.length : ℤ)) := by
    intro ψ hψ
    -- common_prefix_length y ψ + 1 ≤ q, so common_prefix_length y ψ ≤ q - 1.
    have h_cpl := h_cpl_bound ψ hψ
    -- b_ψ(y) = |y| - 2 · common_prefix_length y ψ ≥ |y| - 2(q-1).
    -- p_ψ(y) = 3^{-b_ψ(y)} ≤ 3^{2(q-1) - |y|}.
    unfold poisson_kernel busemann
    -- Goal: 3^{-(|y| - 2 · cpl)} ≤ 3^{2q - 2 - |y|}.
    -- Need: -(|y| - 2 · cpl) ≤ 2q - 2 - |y|, i.e., 2 · cpl - |y| ≤ 2q - 2 - |y|,
    -- i.e., 2 · cpl ≤ 2q - 2, i.e., cpl ≤ q - 1, which holds.
    have h1 : (2 : ℤ) * (common_prefix_length y ψ : ℤ) ≤ 2 * (q : ℤ) - 2 := by
      have : (common_prefix_length y ψ : ℤ) ≤ (q : ℤ) - 1 := by
        have := h_cpl
        omega
      linarith
    have h_exp_le :
        -((y.toWord.length : ℤ) - 2 * (common_prefix_length y ψ : ℤ))
          ≤ 2 * (q : ℤ) - 2 - (y.toWord.length : ℤ) := by linarith
    exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) h_exp_le
  -- Now bound ∫_B p_ψ(y) dμ_1 ≤ const · μ_1(B).toReal ≤ const.
  set Cval : ℝ := (3 : ℝ) ^ (2 * (q : ℤ) - 2 - (y.toWord.length : ℤ)) with hCval
  have hCval_pos : 0 < Cval := zpow_pos (by norm_num) _
  -- Use integral bound: ∫_B p_ψ(y) dμ_1 ≤ ∫_B Cval dμ_1 = Cval · μ_1(B).toReal.
  have h_int_le :
      ∫ ψ in B, poisson_kernel ψ y ∂(harmonic_measure 1)
        ≤ ∫ _ψ in B, Cval ∂(harmonic_measure 1) := by
    refine MeasureTheory.setIntegral_mono_on
      ?_ ?_ hBmeas h_integrand_bound
    · exact (poisson_kernel_integrable y).integrableOn
    · exact MeasureTheory.integrableOn_const
        (MeasureTheory.measure_ne_top _ _)
  -- Compute ∫_B Cval dμ_1 = Cval · μ_1(B).toReal ≤ Cval · 1 = Cval.
  have h_const_int :
      (∫ _ψ in B, Cval ∂(harmonic_measure 1))
        = (harmonic_measure 1 B).toReal * Cval := by
    rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, smul_eq_mul]
  have h_mu_le_one : (harmonic_measure 1 B).toReal ≤ 1 := by
    have h_le := MeasureTheory.measure_mono (μ := harmonic_measure 1)
      (h := Set.subset_univ B)
    have h_univ : harmonic_measure 1 (Set.univ : Set F2_boundary) = 1 :=
      (harmonic_measure_isProbabilityMeasure 1).measure_univ
    rw [h_univ] at h_le
    have h_ne_top : harmonic_measure 1 B ≠ ⊤ :=
      MeasureTheory.measure_ne_top _ _
    have := ENNReal.toReal_le_toReal h_ne_top (by simp : (1 : ENNReal) ≠ ⊤) |>.mpr h_le
    simpa using this
  calc ∫ ψ in B, poisson_kernel ψ y ∂(harmonic_measure 1)
      ≤ ∫ _ψ in B, Cval ∂(harmonic_measure 1) := h_int_le
    _ = (harmonic_measure 1 B).toReal * Cval := h_const_int
    _ ≤ 1 * Cval := by
        exact mul_le_mul_of_nonneg_right h_mu_le_one hCval_pos.le
    _ = Cval := by ring

/-- **Helper: the Poisson representation as a withDensity equation.**
The harmonic measure `μ_y` equals `μ_1.withDensity (ofReal ∘ p_·(y))`.
This is the measure-level content underlying
`harmonic_measure_poisson_representation`. -/
private lemma harmonic_measure_eq_withDensity_poisson_kernel (y : F2) :
    harmonic_measure y =
      (harmonic_measure 1).withDensity
        (fun ψ : F2_boundary => ENNReal.ofReal (poisson_kernel ψ y)) := by
  classical
  -- Reproduce the π-system uniqueness argument from
  -- `harmonic_measure_poisson_representation`.
  set ν : MeasureTheory.Measure F2_boundary :=
    (harmonic_measure 1).withDensity
      (fun ψ => ENNReal.ofReal (poisson_kernel ψ y)) with hν_def
  let C : Set (Set F2_boundary) :=
    {S : Set F2_boundary | ∃ φ : F2_boundary, ∃ p : ℕ, S = cylinder φ p}
  have h_pi : IsPiSystem C := cylinders_isPiSystem
  have h_gen :
      (inferInstance : MeasurableSpace F2_boundary) =
        MeasurableSpace.generateFrom C :=
    borel_F2_boundary_eq_generateFrom_cylinders
  have h_on_cyl : ∀ S ∈ C, harmonic_measure y S = ν S := by
    rintro S ⟨φ, p, rfl⟩
    have h_meas : MeasurableSet (cylinder φ p) := cylinder_measurable φ p
    rw [hν_def, MeasureTheory.withDensity_apply _ h_meas]
    exact harmonic_measure_poisson_on_cylinder_enn y φ p
  obtain ⟨φ₀⟩ : Nonempty F2_boundary := by
    by_contra h_empty
    rw [not_nonempty_iff] at h_empty
    have h_prob : (harmonic_measure 1) Set.univ = 1 :=
      (harmonic_measure_isProbabilityMeasure 1).measure_univ
    rw [Set.univ_eq_empty_iff.mpr h_empty, MeasureTheory.measure_empty] at h_prob
    exact (zero_ne_one h_prob)
  let Bseq : ℕ → Set F2_boundary := fun _ => cylinder φ₀ 0
  have hBseq_univ : ⋃ i, Bseq i = Set.univ := by
    simp only [Bseq, cylinder_zero, Set.iUnion_const]
  have hBseq_mem : ∀ i, Bseq i ∈ C := fun _ => ⟨φ₀, 0, rfl⟩
  have hBseq_fin : ∀ i, (harmonic_measure y) (Bseq i) ≠ ⊤ := fun _ =>
    MeasureTheory.measure_ne_top (harmonic_measure y) _
  exact MeasureTheory.Measure.ext_of_generateFrom_of_iUnion C Bseq h_gen h_pi
    hBseq_univ hBseq_mem hBseq_fin h_on_cyl

/-- **Integral form of Poisson representation.**  For every continuous
`g : F2_boundary → ℝ`, the Bochner integral against `μ_y` equals the
Bochner integral against `μ_1` of `g(ψ) · p_ψ(y)`.

In particular, `∫ g dμ_y = poisson_integral g y`. -/
private lemma integral_against_harmonic_measure_eq_poisson_integral
    (g : F2_boundary → ℝ) (hg : Continuous g) (y : F2) :
    ∫ ψ, g ψ ∂(harmonic_measure y)
      = ∫ ψ, g ψ * poisson_kernel ψ y ∂(harmonic_measure 1) := by
  rw [harmonic_measure_eq_withDensity_poisson_kernel y]
  -- Reduce to integral_withDensity_eq_integral_toReal_smul.
  have hf_meas : Measurable
      (fun ψ : F2_boundary => ENNReal.ofReal (poisson_kernel ψ y)) :=
    ENNReal.measurable_ofReal.comp (poisson_kernel_measurable y)
  have hf_lt_top : ∀ᵐ ψ ∂(harmonic_measure 1),
      ENNReal.ofReal (poisson_kernel ψ y) < ⊤ := by
    refine Filter.Eventually.of_forall (fun ψ => ?_)
    exact ENNReal.ofReal_lt_top
  rw [integral_withDensity_eq_integral_toReal_smul hf_meas hf_lt_top g]
  -- Now goal: ∫ (ofReal (p_ψ y)).toReal • g ψ ∂μ_1 = ∫ g ψ * p_ψ y ∂μ_1.
  refine MeasureTheory.integral_congr_ae ?_
  refine Filter.Eventually.of_forall (fun ψ => ?_)
  show (ENNReal.ofReal (poisson_kernel ψ y)).toReal • g ψ = g ψ * poisson_kernel ψ y
  rw [ENNReal.toReal_ofReal (poisson_kernel_nonneg y ψ), smul_eq_mul]
  ring

/-- **Wave 30 — boundary continuity of the Dirichlet solution
(theorem).** At every boundary point `(ψ : F2bar)`, the Dirichlet
solution `dirichlet_solution g` is continuous, provided `g` is.

**Proof.** Combines:

* The cylinder concentration estimate
  `harmonic_measure_complement_cylinder_bound`.
* Heine–Cantor uniform continuity of the lift of `g` to F2bar.F2boundary
  (compact subspace of F2bar).
* The integral form of the Poisson representation
  `integral_against_harmonic_measure_eq_poisson_integral`.
* The F2bar metric `dist y (φ : F2bar) < exp(-p)` ⟹ first p+1
  coordinates agree.

This dissolves the previous narrow admission
`dirichlet_solution_continuousAt_boundary_axiom`. -/
theorem dirichlet_solution_continuousAt_boundary_axiom
    (g : F2_boundary → ℝ) (hg : Continuous g) (φ : F2_boundary) :
    ContinuousAt (dirichlet_solution g) ((φ : F2_boundary) : F2bar) := by
  classical
  -- Step 1: Lift g to F2bar via F2bar_to_F2_boundary (defined on F2bar.F2boundary).
  -- The lifted function is continuous on the compact F2bar.F2boundary.
  have h_cont_on : ContinuousOn
      (fun y : F2bar => if hy : y ∈ F2bar.F2boundary then
          g (F2bar_to_F2_boundary y hy) else 0)
      F2bar.F2boundary := by
    -- This function equals (g ∘ F2bar_to_F2_boundary) on F2bar.F2boundary.
    -- We show it's continuous on F2bar.F2boundary directly via subspace topology.
    rw [continuousOn_iff_continuous_restrict]
    -- Goal: Continuous (Set.restrict F2bar.F2boundary <fun ...>).
    -- Set.restrict S f y = f y.val for y : Subtype S.
    have h_eq : (Set.restrict F2bar.F2boundary
        (fun y : F2bar => if hy : y ∈ F2bar.F2boundary then
          g (F2bar_to_F2_boundary y hy) else 0))
        = (fun y : F2bar.F2boundary => g (F2bar_to_F2_boundary y.val y.2)) := by
      funext ⟨y, hy⟩
      simp [Set.restrict, hy]
    rw [h_eq]
    -- Continuous of (g ∘ (fun y => F2bar_to_F2_boundary y.val y.2)).
    -- The map y ↦ F2bar_to_F2_boundary y.val y.2 is the inverse of the
    -- embedding restricted to F2bar.F2boundary.
    apply hg.comp
    -- Show continuous: y : F2bar.F2boundary ↦ F2bar_to_F2_boundary y.val y.2.
    -- F2_boundary topology is induced by F2_boundary_to_F2bar.
    -- Need: (F2_boundary_to_F2bar) ∘ this map = identity on F2bar.F2boundary.
    rw [continuous_def]
    intro V hV_open
    -- V is open in F2_boundary; lift via induced topology.
    rw [isOpen_induced_iff] at hV_open
    obtain ⟨U, hU_open, hUV⟩ := hV_open
    rw [show (fun y : F2bar.F2boundary =>
              F2bar_to_F2_boundary y.val y.2) ⁻¹' V
            = (fun y : F2bar.F2boundary => y.val) ⁻¹' U from ?_]
    · exact (hU_open.preimage continuous_subtype_val)
    · ext ⟨y, hy⟩
      simp only [Set.mem_preimage, ← hUV]
      show F2_boundary_to_F2bar (F2bar_to_F2_boundary y hy) ∈ U ↔ y ∈ U
      rw [F2_boundary_to_F2bar_F2bar_to_F2_boundary y hy]
  -- Step 2: Heine-Cantor uniform continuity on the compact F2bar.F2boundary.
  have h_compact : IsCompact (F2bar.F2boundary : Set F2bar) :=
    F2bar.F2boundary_isClosed.isCompact
  have h_unif : UniformContinuousOn
      (fun y : F2bar => if hy : y ∈ F2bar.F2boundary then
          g (F2bar_to_F2_boundary y hy) else 0)
      F2bar.F2boundary :=
    h_compact.uniformContinuousOn_of_continuous h_cont_on
  -- Step 3: Bound M = sup |g|.
  obtain ⟨M_, hM_⟩ := (isCompact_range hg).isBounded.exists_norm_le
  set M : ℝ := max M_ 1 with hM_def
  have hM_nonneg : 0 ≤ M := by
    rw [hM_def]; exact le_trans zero_le_one (le_max_right _ _)
  have hM_pos : 0 < M := by rw [hM_def]; exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hg_bdd : ∀ ψ, |g ψ| ≤ M := fun ψ => by
    have := hM_ (g ψ) ⟨ψ, rfl⟩
    rw [Real.norm_eq_abs] at this
    rw [hM_def]; exact le_trans this (le_max_left _ _)
  -- Step 4: ε/δ proof.
  rw [Metric.continuousAt_iff]
  intro ε hε
  -- Pick δ' > 0 with d(ψ₁, ψ₂) < δ' ⟹ |g(ψ₁) - g(ψ₂)| < ε/4 (in F2bar metric).
  rw [Metric.uniformContinuousOn_iff] at h_unif
  obtain ⟨δ', hδ'_pos, hδ'_spec⟩ := h_unif (ε / 4) (by linarith)
  -- Pick q ≥ 1 with exp(-q) < δ'.
  obtain ⟨q, hq_pos, hq_lt⟩ : ∃ q : ℕ, 1 ≤ q ∧ Real.exp (-(q : ℝ)) < δ' := by
    obtain ⟨q', hq'_log⟩ := exists_nat_gt (max 0 (-Real.log δ'))
    refine ⟨q' + 1, by omega, ?_⟩
    have h1 : -Real.log δ' < (q' + 1 : ℝ) := by
      have hq'_max : -Real.log δ' < (q' : ℝ) := lt_of_le_of_lt (le_max_right _ _) hq'_log
      linarith
    calc Real.exp (-(q' + 1 : ℕ) : ℝ)
        = Real.exp (-(q' + 1 : ℝ)) := by push_cast; rfl
      _ < Real.exp (Real.log δ') := by
          apply Real.exp_lt_exp.mpr; linarith
      _ = δ' := Real.exp_log hδ'_pos
  -- Pick N ≥ 0 with 3^{-N} · 2M < ε/4, equivalently N ≥ log_3 (8M/ε).
  -- Use that 3^{-n} → 0.
  have hε_8M_pos : 0 < ε / (8 * M) := div_pos hε (by linarith)
  have h_pow_tend : Filter.Tendsto (fun n : ℕ => ((1 : ℝ) / 3) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/3)
      (by norm_num : ((1 : ℝ) / 3) < 1)
  obtain ⟨N₀, hN₀_spec⟩ : ∃ N₀ : ℕ, ∀ n ≥ N₀, (3 : ℝ) ^ (-(n : ℤ)) < ε / (8 * M) := by
    have h_pow_eq : ∀ n : ℕ, ((1 : ℝ) / 3) ^ n = (3 : ℝ) ^ (-(n : ℤ)) := by
      intro n
      rw [zpow_neg, zpow_natCast, one_div, inv_pow]
    rcases (Metric.tendsto_atTop.mp h_pow_tend) (ε / (8 * M)) hε_8M_pos with ⟨N₀, hN₀⟩
    refine ⟨N₀, ?_⟩
    intro n hn
    have h_dist := hN₀ n hn
    rw [Real.dist_eq, sub_zero] at h_dist
    have h_pow_pos : (0 : ℝ) < ((1 : ℝ) / 3) ^ n := pow_pos (by norm_num) _
    rw [abs_of_pos h_pow_pos] at h_dist
    rw [← h_pow_eq n]
    exact h_dist
  -- Set p = max (2*q + 2) N₀ + q + 2  to ensure both p ≥ 2*q + 1 and 3^{-(p+1-2q)} small.
  -- Choose p such that p - 2q ≥ N₀ + 2.
  let p : ℕ := 2 * q + N₀ + 2
  have hp_ge_q : q ≤ p := by simp [p]; omega
  have hp_2q : (p : ℤ) - 2 * (q : ℤ) - 1 ≥ (N₀ : ℤ) := by
    show (p : ℤ) - 2 * q - 1 ≥ N₀
    push_cast
    show (2 * q + N₀ + 2 : ℤ) - 2 * q - 1 ≥ N₀
    linarith
  -- Set δ := exp(-p).
  refine ⟨Real.exp (-(p : ℝ)), Real.exp_pos _, ?_⟩
  intro y hy
  -- Case split on y.
  by_cases h_in_bdy : y ∈ F2bar.F2boundary
  · -- Case (a): y is a boundary image.  y = (ψ : F2bar).
    set ψ := F2bar_to_F2_boundary y h_in_bdy with hψ_def
    have hyψ : y = F2_boundary_to_F2bar ψ :=
      (F2_boundary_to_F2bar_F2bar_to_F2_boundary y h_in_bdy).symm
    have h_g_φ : dirichlet_solution g ((φ : F2_boundary) : F2bar) = g φ :=
      dirichlet_solution_boundary_axiom g φ
    have h_g_ψ : dirichlet_solution g y = g ψ := by
      rw [hyψ]
      change dirichlet_solution g ((ψ : F2_boundary) : F2bar) = g ψ
      exact dirichlet_solution_boundary_axiom g ψ
    rw [Real.dist_eq, h_g_ψ, h_g_φ]
    -- |g ψ - g φ| < ε.
    -- Use uniform continuity: dist y (F2_boundary_to_F2bar φ) < exp(-p) ≤ exp(-q) < δ'.
    have h_dist_y_φ : dist y ((φ : F2_boundary) : F2bar) < δ' := by
      have hp_le_dist : Real.exp (-(p : ℝ)) ≤ Real.exp (-(q : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have : (q : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_ge_q
        linarith
      calc dist y ((φ : F2_boundary) : F2bar)
          < Real.exp (-(p : ℝ)) := hy
        _ ≤ Real.exp (-(q : ℝ)) := hp_le_dist
        _ < δ' := hq_lt
    -- φ is a boundary image, so the lifted function evaluates to g φ at it.
    have h_φ_in : ((φ : F2_boundary) : F2bar) ∈ F2bar.F2boundary :=
      F2_boundary_to_F2bar_mem_F2boundary φ
    have h_unif_app := hδ'_spec y h_in_bdy ((φ : F2_boundary) : F2bar) h_φ_in h_dist_y_φ
    -- Lifted function at y = g ψ; at (φ : F2bar) = g φ.
    rw [dif_pos h_in_bdy, dif_pos h_φ_in] at h_unif_app
    rw [F2bar_to_F2_boundary_F2_boundary_to_F2bar] at h_unif_app
    have hψy : F2bar_to_F2_boundary y h_in_bdy = ψ := by rfl
    rw [hψy, Real.dist_eq] at h_unif_app
    linarith
  · -- Case (b): y is an F2 image.  Reconstruct y = (x : F2bar) for some x : F2.
    -- (Same construction as in `dirichlet_solution_continuous`'s F2 branch.)
    have h_finite : ∃ n : ℕ, y.val n = ExtGen.one := by
      by_contra h_no
      apply h_in_bdy
      intro n
      intro h_eq
      apply h_no
      exact ⟨n, h_eq⟩
    let n₀ : ℕ := Nat.find h_finite
    have hn₀_one : y.val n₀ = ExtGen.one := Nat.find_spec h_finite
    have hn₀_min : ∀ k < n₀, y.val k ≠ ExtGen.one :=
      fun k hk => Nat.find_min h_finite hk
    have h_tail_one : ∀ m, n₀ ≤ m → y.val m = ExtGen.one :=
      y.2.2 n₀ hn₀_one
    -- Reconstruct x : F2.
    set xWord : List (Fin 2 × Bool) :=
      (List.range n₀).map (fun i => extGenToFbg (y.val i)) with hxWord_def
    have hxWord_length : xWord.length = n₀ := by simp [hxWord_def]
    have hxWord_getElem : ∀ k (hk : k < xWord.length),
        xWord[k]'hk = extGenToFbg (y.val k) := by
      intro k hk
      simp [hxWord_def]
    have hxWord_reduced : _root_.FreeGroup.IsReduced xWord := by
      show _root_.List.IsChain _ xWord
      rw [_root_.List.isChain_iff_getElem]
      intro n hn
      have hn0 : n + 1 < n₀ := by rwa [hxWord_length] at hn
      have hn0' : n < n₀ := Nat.lt_of_succ_lt hn0
      rw [hxWord_getElem n (by rw [hxWord_length]; exact hn0'),
          hxWord_getElem (n + 1) (by rw [hxWord_length]; exact hn0)]
      have hnc : ¬ ExtGen.isCancellation (y.val n) (y.val (n + 1)) := y.2.1 n
      have hyn_ne : y.val n ≠ ExtGen.one := hn₀_min n hn0'
      have hyn1_ne : y.val (n + 1) ≠ ExtGen.one := hn₀_min (n + 1) hn0
      have h_nc_fbg : NonCancellation (extGenToFbg (y.val n)) (extGenToFbg (y.val (n + 1))) :=
        nonCancellation_of_not_isCancellation _ _ hyn_ne hyn1_ne hnc
      intro h_eq_fst
      rcases h_nc_fbg with h_fst_ne | h_snd_eq
      · exact absurd h_eq_fst h_fst_ne
      · exact h_snd_eq
    let x : F2 := _root_.FreeGroup.mk xWord
    have hx_toWord : x.toWord = xWord := hxWord_reduced.reduce_eq
    have hx_length : x.toWord.length = n₀ := by rw [hx_toWord]; exact hxWord_length
    have hxy : F2_to_F2bar x = y := by
      apply F2bar.ext
      intro k
      show (if h : k < x.toWord.length then fbgToExtGen (x.toWord[k]'h)
            else ExtGen.one) = y.val k
      by_cases hk : k < x.toWord.length
      · rw [dif_pos hk]
        have hk' : k < n₀ := by rw [← hx_length]; exact hk
        have hk_xWord : k < xWord.length := by rw [hxWord_length]; exact hk'
        have hxw_get : (xWord[k]'hk_xWord) = extGenToFbg (y.val k) :=
          hxWord_getElem k hk_xWord
        have hxk_eq : x.toWord[k]'hk = xWord[k]'hk_xWord := by simp [hx_toWord]
        rw [hxk_eq, hxw_get]
        exact fbgToExtGen_extGenToFbg _ (hn₀_min k hk')
      · rw [dif_neg hk]
        have hk_ge : n₀ ≤ k := by rw [← hx_length]; omega
        exact (h_tail_one k hk_ge).symm
    -- y = (x : F2bar), so dirichlet_solution g y = poisson_integral g x.
    have h_dir_y : dirichlet_solution g y = poisson_integral g x := by
      rw [show y = ((x : F2) : F2bar) from hxy.symm]
      exact dirichlet_solution_on_F2_eq_poisson_integral g x
    have h_dir_φ : dirichlet_solution g ((φ : F2_boundary) : F2bar) = g φ :=
      dirichlet_solution_boundary_axiom g φ
    -- The metric distance constraint dist y φ_bar < exp(-p) implies
    -- the F2bar coordinates of y and (φ : F2bar) agree on [0, p].
    -- In particular: |x| ≥ p+1, and x.toWord[i] = φ.val i for i ≤ p.
    have h_agree_p : ∀ i, i ≤ p → y.val i = (F2_boundary_to_F2bar φ).val i :=
      fun i hi => F2bar.agree_of_dist_lt
        (x := y) (y := F2_boundary_to_F2bar φ) hy i hi
    -- Translate to: x.toWord[i] = φ.val i for i ≤ p, and x.toWord.length ≥ p+1.
    have hx_len_ge : p + 1 ≤ x.toWord.length := by
      -- y.val i ≠ one for i ≤ p (because (F2_boundary_to_F2bar φ).val i = fbgToExtGen (φ.val i) ≠ one).
      -- Hence n₀ > p, i.e., n₀ ≥ p+1, hence |x| = n₀ ≥ p+1.
      have h_p_lt_n₀ : p < n₀ := by
        by_contra h_le
        push_neg at h_le  -- n₀ ≤ p.
        have h_y_n₀ : y.val n₀ = ExtGen.one := hn₀_one
        have h_phi_n₀ : (F2_boundary_to_F2bar φ).val n₀ ≠ ExtGen.one := by
          show fbgToExtGen (φ.val n₀) ≠ ExtGen.one
          exact fbgToExtGen_ne_one _
        have := h_agree_p n₀ h_le
        rw [h_y_n₀] at this
        exact h_phi_n₀ this.symm
      rw [hx_length]; omega
    have hx_word_phi : ∀ i, i < p + 1 →
        x.toWord[i]? = some (φ.val i) := by
      intro i hi
      have hi_lt_x : i < x.toWord.length := lt_of_lt_of_le hi hx_len_ge
      rw [List.getElem?_eq_getElem hi_lt_x, Option.some_inj]
      -- Reduce both sides via hxy and the F2_to_F2bar structure.
      have h_y_i : y.val i = fbgToExtGen (φ.val i) := by
        have := h_agree_p i (by omega)
        rw [this]
        rfl
      -- y.val i = (F2_to_F2bar x).val i = fbgToExtGen (x.toWord[i]'hi_lt_x)
      have h_y_x : y.val i = fbgToExtGen (x.toWord[i]'hi_lt_x) := by
        rw [← hxy]
        show (if h : i < x.toWord.length then fbgToExtGen (x.toWord[i]'h)
              else ExtGen.one) = fbgToExtGen (x.toWord[i]'hi_lt_x)
        rw [dif_pos hi_lt_x]
      have : fbgToExtGen (x.toWord[i]'hi_lt_x) = fbgToExtGen (φ.val i) := by
        rw [← h_y_x]; exact h_y_i
      exact fbgToExtGen_injective this
    -- Therefore PrefixMatches x φ (p + 1).
    have h_pm_x_phi : PrefixMatches x φ (p + 1) := ⟨hx_len_ge, hx_word_phi⟩
    -- Hence common_prefix_length x φ ≥ p + 1.
    have h_cpl_x_phi_ge : p + 1 ≤ common_prefix_length x φ := by
      -- common_prefix_length is `Nat.findGreatest (PrefixMatches x φ) |x|`.
      apply Nat.le_findGreatest hx_len_ge h_pm_x_phi
    -- Step 5: Apply the bound.
    -- |poisson_integral g x - g φ| ≤ ε/2 + 2M · 3^{2q-2-|x|}.
    -- We have |x| ≥ p+1 ≥ 2q + N₀ + 3, so 3^{2q-2-|x|} ≤ 3^{-N₀-1} < ε/(8M).
    rw [Real.dist_eq, h_dir_y, h_dir_φ]
    -- Goal: |poisson_integral g x - g φ| < ε.
    -- Use: poisson_integral g x = ∫ g(ψ) p_ψ(x) dμ_1 = ∫ g dμ_x,
    -- and g φ = ∫ g φ dμ_x = ∫ g(φ) · p_ψ(x) dμ_1 (probability measure).
    have h_int_eq : poisson_integral g x = ∫ ψ, g ψ ∂(harmonic_measure x) := by
      rw [poisson_integral_def,
        integral_against_harmonic_measure_eq_poisson_integral g hg x]
    rw [h_int_eq]
    -- ∫ g dμ_x - g φ = ∫ (g ψ - g φ) dμ_x.
    have h_g_phi_const : g φ = ∫ _ψ, g φ ∂(harmonic_measure x) := by
      rw [MeasureTheory.integral_const, MeasureTheory.measureReal_def, smul_eq_mul]
      have h_univ : harmonic_measure x (Set.univ : Set F2_boundary) = 1 :=
        (harmonic_measure_isProbabilityMeasure x).measure_univ
      rw [h_univ]; simp
    rw [h_g_phi_const]
    rw [← MeasureTheory.integral_sub]
    · -- |∫ (g ψ - g φ) dμ_x| ≤ ∫ |g ψ - g φ| dμ_x.
      have h_int_diff : MeasureTheory.Integrable (fun ψ => g ψ - g φ) (harmonic_measure x) := by
        apply MeasureTheory.Integrable.sub
        · -- g is bounded continuous, hence integrable for finite measure.
          apply MeasureTheory.Integrable.of_bound
            hg.stronglyMeasurable.aestronglyMeasurable M
          refine Filter.Eventually.of_forall (fun ψ => ?_)
          rw [Real.norm_eq_abs]; exact hg_bdd ψ
        · exact MeasureTheory.integrable_const _
      have h_abs_le : |∫ ψ, (g ψ - g φ) ∂(harmonic_measure x)|
          ≤ ∫ ψ, |g ψ - g φ| ∂(harmonic_measure x) := by
        rw [← Real.norm_eq_abs]
        refine MeasureTheory.norm_integral_le_integral_norm _
      apply lt_of_le_of_lt h_abs_le
      -- Split: ∫ |g ψ - g φ| dμ_x = ∫_{cyl φ q} ... + ∫_{univ \ cyl φ q} ...
      set B : Set F2_boundary := Set.univ \ cylinder φ q with hB_def
      have hB_meas : MeasurableSet B :=
        MeasurableSet.univ.diff (cylinder_measurable φ q)
      have hcyl_meas : MeasurableSet (cylinder φ q) := cylinder_measurable φ q
      -- Decompose: cylinder φ q ∪ B = univ, disjoint.
      have h_union : cylinder φ q ∪ B = Set.univ := by
        rw [hB_def]; simp [Set.union_diff_self]
      have h_disj : Disjoint (cylinder φ q) B := by
        rw [hB_def]; exact Set.disjoint_sdiff_right
      -- Bound the integral of |g ψ - g φ|.
      have h_abs_int : MeasureTheory.Integrable
          (fun ψ => |g ψ - g φ|) (harmonic_measure x) :=
        h_int_diff.abs
      have hB_eq_compl : B = (cylinder φ q)ᶜ := by
        rw [hB_def]; ext ψ; simp
      have h_split : (∫ ψ, |g ψ - g φ| ∂(harmonic_measure x))
          = (∫ ψ in cylinder φ q, |g ψ - g φ| ∂(harmonic_measure x))
          + (∫ ψ in B, |g ψ - g φ| ∂(harmonic_measure x)) := by
        rw [hB_eq_compl, ← MeasureTheory.integral_add_compl hcyl_meas h_abs_int]
      rw [h_split]
      -- Bound part 1: integrand ≤ ε/4 on cyl φ q.
      have h_part1 :
          (∫ ψ in cylinder φ q, |g ψ - g φ| ∂(harmonic_measure x))
            ≤ ε / 4 := by
        have h_pointwise : ∀ ψ ∈ cylinder φ q, |g ψ - g φ| ≤ ε / 4 := by
          intro ψ hψ
          -- ψ ∈ cylinder φ q, so dist (F2_boundary_to_F2bar ψ) (F2_boundary_to_F2bar φ) ≤ exp(-q).
          -- Both are in F2bar.F2boundary; uniform continuity yields the bound.
          have hψ_in : (F2_boundary_to_F2bar ψ) ∈ F2bar.F2boundary :=
            F2_boundary_to_F2bar_mem_F2boundary ψ
          have hφ_in : (F2_boundary_to_F2bar φ) ∈ F2bar.F2boundary :=
            F2_boundary_to_F2bar_mem_F2boundary φ
          rw [mem_cylinder] at hψ
          have h_agree : ∀ i < q, (F2_boundary_to_F2bar ψ).val i
              = (F2_boundary_to_F2bar φ).val i := by
            intro i hi
            show fbgToExtGen (ψ.val i) = fbgToExtGen (φ.val i)
            rw [hψ i hi]
          have h_dist_ψφ_bar : dist (F2_boundary_to_F2bar ψ) (F2_boundary_to_F2bar φ)
              ≤ Real.exp (-(q : ℝ)) := F2bar.d_prime_le_of_agree h_agree
          have h_dist_lt_δ' : dist (F2_boundary_to_F2bar ψ) (F2_boundary_to_F2bar φ)
              < δ' := lt_of_le_of_lt h_dist_ψφ_bar hq_lt
          have h_unif_app := hδ'_spec (F2_boundary_to_F2bar ψ) hψ_in
            (F2_boundary_to_F2bar φ) hφ_in h_dist_lt_δ'
          rw [dif_pos hψ_in, dif_pos hφ_in] at h_unif_app
          rw [F2bar_to_F2_boundary_F2_boundary_to_F2bar,
              F2bar_to_F2_boundary_F2_boundary_to_F2bar, Real.dist_eq] at h_unif_app
          linarith
        calc (∫ ψ in cylinder φ q, |g ψ - g φ| ∂(harmonic_measure x))
            ≤ (∫ _ψ in cylinder φ q, ε / 4 ∂(harmonic_measure x)) := by
              refine MeasureTheory.setIntegral_mono_on
                h_abs_int.integrableOn ?_ hcyl_meas h_pointwise
              exact MeasureTheory.integrableOn_const
                (MeasureTheory.measure_ne_top _ _)
          _ = (harmonic_measure x (cylinder φ q)).toReal * (ε / 4) := by
              rw [MeasureTheory.setIntegral_const,
                MeasureTheory.measureReal_def, smul_eq_mul]
          _ ≤ 1 * (ε / 4) := by
              apply mul_le_mul_of_nonneg_right _ (by linarith)
              have h_le := MeasureTheory.measure_mono (μ := harmonic_measure x)
                (h := Set.subset_univ (cylinder φ q))
              have h_univ : harmonic_measure x (Set.univ : Set F2_boundary) = 1 :=
                (harmonic_measure_isProbabilityMeasure x).measure_univ
              rw [h_univ] at h_le
              have h_ne_top : harmonic_measure x (cylinder φ q) ≠ ⊤ :=
                MeasureTheory.measure_ne_top _ _
              have := ENNReal.toReal_le_toReal h_ne_top
                (by simp : (1 : ENNReal) ≠ ⊤) |>.mpr h_le
              simpa using this
          _ = ε / 4 := by ring
      -- Bound part 2: integrand ≤ 2M, μ_x(B) ≤ 3^{2(q-1)-|x|}.
      have h_part2 :
          (∫ ψ in B, |g ψ - g φ| ∂(harmonic_measure x))
            ≤ 2 * M * (3 : ℝ) ^ (2 * (q : ℤ) - 2 - (x.toWord.length : ℤ)) := by
        -- |g ψ - g φ| ≤ 2M.
        have h_pointwise2 : ∀ ψ, |g ψ - g φ| ≤ 2 * M := fun ψ => by
          have h1 : |g ψ| ≤ M := hg_bdd ψ
          have h2 : |g φ| ≤ M := hg_bdd φ
          calc |g ψ - g φ| ≤ |g ψ| + |g φ| := abs_sub _ _
            _ ≤ M + M := add_le_add h1 h2
            _ = 2 * M := by ring
        -- ∫_B |g - gφ| dμ_x ≤ 2M · μ_x(B).toReal.
        have h_step1 : (∫ ψ in B, |g ψ - g φ| ∂(harmonic_measure x))
            ≤ (∫ _ψ in B, 2 * M ∂(harmonic_measure x)) := by
          refine MeasureTheory.setIntegral_mono_on
            h_abs_int.integrableOn ?_ hB_meas (fun ψ _ => h_pointwise2 ψ)
          exact MeasureTheory.integrableOn_const
            (MeasureTheory.measure_ne_top _ _)
        have h_step2 : (∫ _ψ in B, 2 * M ∂(harmonic_measure x))
            = (harmonic_measure x B).toReal * (2 * M) := by
          rw [MeasureTheory.setIntegral_const,
            MeasureTheory.measureReal_def, smul_eq_mul]
        have h_q_lt_cpl : q < common_prefix_length x φ :=
          lt_of_lt_of_le (by omega : q < p + 1) h_cpl_x_phi_ge
        have h_bnd := harmonic_measure_complement_cylinder_bound x φ q h_q_lt_cpl
        calc (∫ ψ in B, |g ψ - g φ| ∂(harmonic_measure x))
            ≤ (harmonic_measure x B).toReal * (2 * M) := by
              rw [← h_step2]; exact h_step1
          _ ≤ (3 : ℝ) ^ (2 * (q : ℤ) - 2 - (x.toWord.length : ℤ)) * (2 * M) := by
              apply mul_le_mul_of_nonneg_right h_bnd
              linarith
          _ = 2 * M * (3 : ℝ) ^ (2 * (q : ℤ) - 2 - (x.toWord.length : ℤ)) := by ring
      -- Combine: part1 + part2 < ε/4 + ε/4 = ε/2 < ε.  But we want ε.
      -- Wait — we set tolerance ε/4 from the unif spec.  So part1 ≤ ε/4 (not ε/2).
      -- We bound part2 ≤ 2M · 3^{2(q-1)-|x|}.  We need this < 3ε/4.
      have h_part2_small : (3 : ℝ) ^ (2 * (q : ℤ) - 2 - (x.toWord.length : ℤ))
          < ε / (8 * M) := by
        -- |x| ≥ p + 1 = 2q + N₀ + 3, so 2q - 2 - |x| ≤ -N₀ - 1.
        have h_exp_le : 2 * (q : ℤ) - 2 - (x.toWord.length : ℤ) ≤ -(N₀ : ℤ) - 1 := by
          have : (x.toWord.length : ℤ) ≥ (p + 1 : ℤ) := by exact_mod_cast hx_len_ge
          have : (p + 1 : ℤ) = 2 * (q : ℤ) + N₀ + 3 := by
            show ((2 * q + N₀ + 2) + 1 : ℤ) = _
            push_cast; ring
          omega
        have h_pow_le : (3 : ℝ) ^ (2 * (q : ℤ) - 2 - (x.toWord.length : ℤ))
            ≤ (3 : ℝ) ^ ((-(N₀ : ℤ)) - 1) :=
          zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) h_exp_le
        apply lt_of_le_of_lt h_pow_le
        have h_step : (3 : ℝ) ^ ((-(N₀ : ℤ)) - 1)
            ≤ (3 : ℝ) ^ (-(N₀ : ℤ)) := by
          apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3)
          omega
        have h_strict : (3 : ℝ) ^ (-(N₀ : ℤ)) < ε / (8 * M) :=
          hN₀_spec N₀ le_rfl
        linarith
      -- Now: 2 * M * pow < 2 * M * (ε/(8M)) = ε/4.
      have h_bound2 : 2 * M * (3 : ℝ) ^ (2 * (q : ℤ) - 2 - (x.toWord.length : ℤ))
          < ε / 4 := by
        have h_M_pos := hM_pos
        have h_step : 2 * M * (3 : ℝ) ^ (2 * (q : ℤ) - 2 - (x.toWord.length : ℤ))
            < 2 * M * (ε / (8 * M)) := by
          apply mul_lt_mul_of_pos_left h_part2_small (by linarith)
        have h_simp : 2 * M * (ε / (8 * M)) = ε / 4 := by
          field_simp
          ring
        rw [h_simp] at h_step
        exact h_step
      have h_total : (∫ ψ in cylinder φ q, |g ψ - g φ| ∂(harmonic_measure x))
          + (∫ ψ in B, |g ψ - g φ| ∂(harmonic_measure x))
          < ε / 4 + ε / 4 := by
        have h_p2 := lt_of_le_of_lt h_part2 h_bound2
        linarith
      linarith
    · -- Integrability of g.
      apply MeasureTheory.Integrable.of_bound
        hg.stronglyMeasurable.aestronglyMeasurable M
      refine Filter.Eventually.of_forall (fun ψ => ?_)
      rw [Real.norm_eq_abs]; exact hg_bdd ψ
    · -- Integrability of constant g φ.
      exact MeasureTheory.integrable_const _

/-- **Wave 26 — continuity of the Dirichlet solution at F_2-interior
points.** The image of `F_2` under the embedding into `F2bar` consists
of *isolated* points: every `(x : F2bar)` for `x : F_2` has a
neighbourhood in which the only point is itself. Hence continuity at
any such point is automatic. -/
private lemma dirichlet_solution_continuousAt_F2_image
    (g : F2_boundary → ℝ) (x : F2) :
    ContinuousAt (dirichlet_solution g) ((x : F2) : F2bar) := by
  -- We show: (x : F2bar) is an isolated point of F2bar.
  have h_singleton :
      Metric.ball ((x : F2) : F2bar) (Real.exp (-(x.toWord.length : ℝ)))
        ⊆ {((x : F2) : F2bar)} := by
    intro z hz
    rw [Metric.mem_ball] at hz
    have h_agree : ∀ i, i ≤ x.toWord.length →
        z.val i = (F2_to_F2bar x).val i :=
      fun i hi => F2bar.agree_of_dist_lt
        (x := z) (y := F2_to_F2bar x) hz i hi
    have heq : z = F2_to_F2bar x := by
      apply F2bar.ext
      intro k
      by_cases hk : k ≤ x.toWord.length
      · exact h_agree k hk
      · push_neg at hk
        have h_at_len : z.val x.toWord.length = ExtGen.one := by
          rw [h_agree x.toWord.length le_rfl]
          show (if h : _ < x.toWord.length then _ else ExtGen.one) = ExtGen.one
          simp
        have hz_tail : z.val k = ExtGen.one :=
          z.2.2 x.toWord.length h_at_len k (le_of_lt hk)
        have hx_tail : (F2_to_F2bar x).val k = ExtGen.one := by
          show (if h : _ < x.toWord.length then _ else ExtGen.one) = ExtGen.one
          rw [dif_neg (by omega)]
        rw [hz_tail, hx_tail]
    rw [heq]; rfl
  have h_iso : {((x : F2) : F2bar)} ∈ 𝓝 (((x : F2) : F2bar)) := by
    rw [Metric.mem_nhds_iff]
    exact ⟨Real.exp (-(x.toWord.length : ℝ)), Real.exp_pos _, h_singleton⟩
  -- A function constant on a neighbourhood is continuous there.
  exact (continuousAt_const : ContinuousAt
      (fun _ => dirichlet_solution g ((x : F2) : F2bar)) _).congr
    (Filter.eventually_of_mem h_iso (by
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]))

/-- **Leaf 6 — continuity of the Poisson integral.** The candidate
`dirichlet_solution g` is continuous on the compactification.

**Wave 26 — fully proven** (Wave 30 dissolved the boundary-continuity
admission `dirichlet_solution_continuousAt_boundary_axiom` into a
theorem via the cylinder-concentration estimate + Heine–Cantor
uniform continuity; the interior-point case via isolated
`F_2`-image points and the gluing argument were already complete). -/
lemma dirichlet_solution_continuous (g : F2_boundary → ℝ)
    (hg : Continuous g) :
    Continuous (dirichlet_solution g) := by
  rw [continuous_iff_continuousAt]
  intro y
  classical
  by_cases h_in_bdy : y ∈ F2bar.F2boundary
  · -- y is a boundary image. Pull back to F2_boundary.
    set ψ := F2bar_to_F2_boundary y h_in_bdy with hψ_def
    have hyψ : y = ((ψ : F2_boundary) : F2bar) :=
      (F2_boundary_to_F2bar_F2bar_to_F2_boundary y h_in_bdy).symm
    rw [hyψ]
    exact dirichlet_solution_continuousAt_boundary_axiom g hg ψ
  · -- y is a F2-image. Reconstruct x : F2 with (x : F2bar) = y.
    have h_finite : ∃ n : ℕ, y.val n = ExtGen.one := by
      by_contra h_no
      apply h_in_bdy
      intro n
      intro h_eq
      apply h_no
      exact ⟨n, h_eq⟩
    let n₀ : ℕ := Nat.find h_finite
    have hn₀_one : y.val n₀ = ExtGen.one := Nat.find_spec h_finite
    have hn₀_min : ∀ k < n₀, y.val k ≠ ExtGen.one :=
      fun k hk => Nat.find_min h_finite hk
    have h_tail_one : ∀ m, n₀ ≤ m → y.val m = ExtGen.one :=
      y.2.2 n₀ hn₀_one
    set xWord : List (Fin 2 × Bool) :=
      (List.range n₀).map (fun i => extGenToFbg (y.val i)) with hxWord_def
    have hxWord_length : xWord.length = n₀ := by simp [hxWord_def]
    have hxWord_getElem : ∀ k (hk : k < xWord.length),
        xWord[k]'hk = extGenToFbg (y.val k) := by
      intro k hk
      simp [hxWord_def]
    have hxWord_reduced : _root_.FreeGroup.IsReduced xWord := by
      show _root_.List.IsChain _ xWord
      rw [_root_.List.isChain_iff_getElem]
      intro n hn
      have hn0 : n + 1 < n₀ := by rwa [hxWord_length] at hn
      have hn0' : n < n₀ := Nat.lt_of_succ_lt hn0
      rw [hxWord_getElem n (by rw [hxWord_length]; exact hn0'),
          hxWord_getElem (n + 1) (by rw [hxWord_length]; exact hn0)]
      have hnc : ¬ ExtGen.isCancellation (y.val n) (y.val (n + 1)) := y.2.1 n
      have hyn_ne : y.val n ≠ ExtGen.one := hn₀_min n hn0'
      have hyn1_ne : y.val (n + 1) ≠ ExtGen.one := hn₀_min (n + 1) hn0
      have h_nc_fbg : NonCancellation (extGenToFbg (y.val n)) (extGenToFbg (y.val (n + 1))) :=
        nonCancellation_of_not_isCancellation _ _ hyn_ne hyn1_ne hnc
      intro h_eq_fst
      rcases h_nc_fbg with h_fst_ne | h_snd_eq
      · exact absurd h_eq_fst h_fst_ne
      · exact h_snd_eq
    let x : F2 := _root_.FreeGroup.mk xWord
    have hx_toWord : x.toWord = xWord := hxWord_reduced.reduce_eq
    have hx_length : x.toWord.length = n₀ := by rw [hx_toWord]; exact hxWord_length
    have hxy : F2_to_F2bar x = y := by
      apply F2bar.ext
      intro k
      show (if h : k < x.toWord.length then fbgToExtGen (x.toWord[k]'h)
            else ExtGen.one) = y.val k
      by_cases hk : k < x.toWord.length
      · rw [dif_pos hk]
        have hk' : k < n₀ := by rw [← hx_length]; exact hk
        have hk_xWord : k < xWord.length := by rw [hxWord_length]; exact hk'
        have hxw_get : (xWord[k]'hk_xWord) = extGenToFbg (y.val k) :=
          hxWord_getElem k hk_xWord
        have hxk_eq : x.toWord[k]'hk = xWord[k]'hk_xWord := by simp [hx_toWord]
        rw [hxk_eq, hxw_get]
        exact fbgToExtGen_extGenToFbg _ (hn₀_min k hk')
      · rw [dif_neg hk]
        have hk_ge : n₀ ≤ k := by rw [← hx_length]; omega
        exact (h_tail_one k hk_ge).symm
    rw [show y = ((x : F2) : F2bar) from hxy.symm]
    exact dirichlet_solution_continuousAt_F2_image g x

/-! #### Combinatorial structure of `neighborFinset` on the Cayley graph

The Cayley graph of `F_2` is 4-regular: for every `x : F_2` and every
reference ray `φ ∈ ∂F_2`, the neighbour finset decomposes as
`neighborFinset x = insert yφ T` where `(yφ, T)` is the Busemann
partition.  This is the concrete "4-regularity" bridge needed to turn
the pointwise 1+3 harmonic identity into the `laplacian_E` form. -/

/-- **Wave 22B cleanup — `neighborFinset` via the Busemann partition.**
For every `x : F_2` and every reference ray `φ ∈ ∂F_2`, the
`neighborFinset` of `x` in the Cayley graph equals `insert yφ T`, where
`(yφ, T)` is the partition extracted from `busemann_neighbour_structure`
(toward-`φ` neighbour) and `busemann_three_plus_neighbours` (three
outward neighbours).  Key structural fact: the Cayley graph of `F_2`
is 4-regular. -/
theorem F2_cayley_neighborFinset_eq_insert
    (φ : ∂F2) (x yφ : F2) (T : Finset F2)
    (h_adj : (EnsX2026.Cayley.cayley_graph F2_generating_set).Adj x yφ)
    (h_yφ_bus : busemann φ yφ = busemann φ x - 1)
    (h_Tcard : T.card = 3)
    (h_T_mem : ∀ y ∈ T, (EnsX2026.Cayley.cayley_graph F2_generating_set).Adj x y ∧
                         busemann φ y = busemann φ x + 1)
    (_h_yφ_notmem : yφ ∉ T) :
    (EnsX2026.Cayley.cayley_graph F2_generating_set).neighborFinset x
      = insert yφ T := by
  classical
  set Γ := EnsX2026.Cayley.cayley_graph F2_generating_set
  -- Forward: every element of `insert yφ T` is adjacent to `x`, hence in
  -- `neighborFinset x`.
  have h_insert_sub : insert yφ T ⊆ Γ.neighborFinset x := by
    intro z hz
    rcases Finset.mem_insert.mp hz with heq | hmem
    · rw [SimpleGraph.mem_neighborFinset, heq]; exact h_adj
    · rw [SimpleGraph.mem_neighborFinset]; exact (h_T_mem z hmem).1
  -- Cover: every adjacent vertex lies in `insert yφ T`.  Use
  -- `busemann_three_plus_neighbours` + uniqueness of the toward-`φ`
  -- neighbour.
  obtain ⟨T_cov, h_Tcov_card, _h_Tcov_mem, h_Tcov_cover⟩ :=
    busemann_three_plus_neighbours φ x
  have h_T_sub_cov : T ⊆ T_cov := by
    intro z hz
    have hz_adj : Γ.Adj x z := (h_T_mem z hz).1
    have hz_bus : busemann φ z = busemann φ x + 1 := (h_T_mem z hz).2
    rcases h_Tcov_cover z hz_adj with hz_phi | hz_in
    · exfalso
      have hconf : busemann φ x + 1 = busemann φ x - 1 :=
        hz_bus.symm.trans hz_phi
      have : (2 : ℤ) = 0 := by linarith
      exact absurd this (by decide)
    · exact hz_in
  have h_T_eq_cov : T = T_cov :=
    Finset.eq_of_subset_of_card_le h_T_sub_cov (by rw [h_Tcov_card, h_Tcard])
  have h_adj_sub : ∀ z, Γ.Adj x z → z ∈ insert yφ T := by
    intro z hz_adj
    rcases h_Tcov_cover z hz_adj with hz_phi | hz_in
    · -- `z` is the toward-`φ` neighbour; equals `yφ` by uniqueness.
      refine Finset.mem_insert.mpr (Or.inl ?_)
      obtain ⟨y_uniq, _hprop, h_uniq⟩ := busemann_neighbour_structure φ x
      have hz_eq : z = y_uniq := h_uniq z ⟨hz_adj, hz_phi⟩
      have hyφ_eq : yφ = y_uniq := h_uniq yφ ⟨h_adj, h_yφ_bus⟩
      rw [hz_eq, ← hyφ_eq]
    · refine Finset.mem_insert.mpr (Or.inr ?_)
      rw [h_T_eq_cov]; exact hz_in
  -- Combine both inclusions.
  apply Finset.ext
  intro z
  constructor
  · intro hz
    rw [SimpleGraph.mem_neighborFinset] at hz
    exact h_adj_sub z hz
  · intro hz
    exact h_insert_sub hz

/-- **Wave 22B cleanup — 4-regularity of the Cayley graph of `F_2`.**  The
degree of every vertex in the Cayley graph of `F_2` with the symmetric
generating set `{a, b, a⁻¹, b⁻¹}` is `4`.

**Proof.**  Pick any `φ : ∂F_2` (witnessed via the probability measure
`harmonic_measure 1`).  Extract the Busemann partition `(yφ, T)` at `x`
(via `busemann_neighbour_structure` and `busemann_three_plus_neighbours`).
By `F2_cayley_neighborFinset_eq_insert`, `neighborFinset x = insert yφ T`,
whose cardinality is `1 + |T| = 1 + 3 = 4`. -/
theorem F2_cayley_degree_eq_four (x : F2) :
    (EnsX2026.Cayley.cayley_graph F2_generating_set).degree x = 4 := by
  classical
  -- Obtain a boundary ray `φ₀` via the probability measure `harmonic_measure 1`.
  obtain ⟨φ₀⟩ : Nonempty F2_boundary := by
    by_contra h_empty
    rw [not_nonempty_iff] at h_empty
    have h_prob : (harmonic_measure 1) Set.univ = 1 :=
      (harmonic_measure_isProbabilityMeasure 1).measure_univ
    rw [Set.univ_eq_empty_iff.mpr h_empty, MeasureTheory.measure_empty] at h_prob
    exact (zero_ne_one h_prob)
  -- Extract the Busemann partition at `x` relative to `φ₀`.
  obtain ⟨yφ, ⟨hyφ_adj, hyφ_bus⟩, _hyφ_unique⟩ :=
    busemann_neighbour_structure φ₀ x
  obtain ⟨T, hTcard, hT_mem, _hT_cover⟩ :=
    busemann_three_plus_neighbours φ₀ x
  -- Disjointness `yφ ∉ T` (by integer Busemann values).
  have hyφ_notmem : yφ ∉ T := by
    intro hmem
    have hbus_plus : busemann φ₀ yφ = busemann φ₀ x + 1 := (hT_mem yφ hmem).2
    have : busemann φ₀ x - 1 = busemann φ₀ x + 1 := hyφ_bus.symm.trans hbus_plus
    have : (2 : ℤ) = 0 := by linarith
    exact absurd this (by decide)
  -- Rewrite `neighborFinset x` as `insert yφ T`.
  have h_eq : (EnsX2026.Cayley.cayley_graph F2_generating_set).neighborFinset x
        = insert yφ T :=
    F2_cayley_neighborFinset_eq_insert φ₀ x yφ T hyφ_adj hyφ_bus
      hTcard hT_mem hyφ_notmem
  rw [← SimpleGraph.card_neighborFinset_eq_degree, h_eq,
      Finset.card_insert_of_notMem hyφ_notmem, hTcard]

/-- **Wave 22B cleanup — `laplacian_E`-harmonicity of the Poisson integral.**
The Poisson integral is harmonic on the interior `F_2` in the
combinatorial-Laplacian sense:

  `laplacian_E G (poisson_integral g) x = 0`  for every `x : F_2`.

**Proof.**  The pointwise 1+3 harmonic identity
`poisson_integral_pointwise_harmonic` gives a Busemann partition
`(yφ, T)` of the four neighbours of `x` with
`I(yφ) + Σ_{y ∈ T} I(y) = 4 · I(x)`, where `I := poisson_integral g`.
By `F2_cayley_neighborFinset_eq_insert`,
`neighborFinset x = insert yφ T`, so
`Σ_{y ∈ neighborFinset x} I(y) = I(yφ) + Σ_{y ∈ T} I(y) = 4 · I(x)`.
By `F2_cayley_degree_eq_four`, `degree x = 4`; hence
`laplacian_E G I x = 4·I(x) - Σ I(y) = 0`.

Closes axiom A6 from the Cleaner's Wave 22B audit. -/
theorem poisson_integral_laplacian_E_zero
    (g : F2_boundary → ℝ) (hg : Continuous g) :
    ∀ x : F2, EnsX2026.Graphs.laplacian_E
      (EnsX2026.Cayley.cayley_graph F2_generators)
      (poisson_integral g) x = 0 := by
  classical
  intro x
  -- Obtain a boundary ray `φ₀` via the probability measure `harmonic_measure 1`.
  obtain ⟨φ₀⟩ : Nonempty F2_boundary := by
    by_contra h_empty
    rw [not_nonempty_iff] at h_empty
    have h_prob : (harmonic_measure 1) Set.univ = 1 :=
      (harmonic_measure_isProbabilityMeasure 1).measure_univ
    rw [Set.univ_eq_empty_iff.mpr h_empty, MeasureTheory.measure_empty] at h_prob
    exact (zero_ne_one h_prob)
  -- 1+3 harmonic identity at `x`.
  obtain ⟨yφ, T, hyφ_adj, hyφ_bus, hTcard, hT_mem, hyφ_notmem, h_sum_harm⟩ :=
    poisson_integral_pointwise_harmonic g hg φ₀ x
  -- `neighborFinset x = insert yφ T`.
  have h_nb_eq : (EnsX2026.Cayley.cayley_graph F2_generating_set).neighborFinset x
        = insert yφ T :=
    F2_cayley_neighborFinset_eq_insert φ₀ x yφ T hyφ_adj hyφ_bus
      hTcard hT_mem hyφ_notmem
  -- `degree x = 4`.
  have h_deg : (EnsX2026.Cayley.cayley_graph F2_generating_set).degree x = 4 :=
    F2_cayley_degree_eq_four x
  -- Sum over `neighborFinset x` equals `4 · I(x)`.
  have h_sum_nb :
      (∑ y ∈ (EnsX2026.Cayley.cayley_graph F2_generating_set).neighborFinset x,
         poisson_integral g y)
        = 4 * poisson_integral g x := by
    rw [h_nb_eq, Finset.sum_insert hyφ_notmem]; exact h_sum_harm
  -- Unfold `laplacian_E` and combine.
  rw [EnsX2026.Graphs.laplacian_E_apply, h_deg, h_sum_nb]
  push_cast
  ring

/-- **Leaf 7 — harmonicity of the Poisson integral.** The candidate
`dirichlet_solution g` is harmonic on the interior `F_2` (as a
combinatorial-Laplacian-zero function on the Cayley graph).

**Proof (no longer an axiom).** On the image of `F_2 ↪ F2bar`,
`dirichlet_solution g` coincides with `poisson_integral g`
(`dirichlet_solution_on_F2_eq_poisson_integral`).  The Poisson
integral is `laplacian_E`-harmonic on `F_2` by
`poisson_integral_laplacian_E_zero`. -/
lemma dirichlet_solution_harmonic (g : F2_boundary → ℝ)
    (hg : Continuous g) :
    ∀ x : F2, EnsX2026.Graphs.laplacian_E
      (EnsX2026.Cayley.cayley_graph F2_generators)
      (fun y : F2 => dirichlet_solution g ((y : F2) : F2bar)) x = 0 := by
  intro x
  -- Rewrite the lambda to `poisson_integral g`.
  have h_fun_eq :
      (fun y : F2 => dirichlet_solution g ((y : F2) : F2bar)) = poisson_integral g := by
    funext y
    exact dirichlet_solution_on_F2_eq_poisson_integral g y
  rw [h_fun_eq]
  exact poisson_integral_laplacian_E_zero g hg x

/-- **Leaf 8 — boundary agreement.** The candidate restricts to `g` on
the boundary inclusion `∂F_2 ↪ \overline{F_2}`. -/
lemma dirichlet_solution_boundary_eq (g : F2_boundary → ℝ) (hg : Continuous g) :
    ∀ ψ : F2_boundary, dirichlet_solution g ((ψ : F2_boundary) : F2bar) = g ψ :=
  fun ψ => dirichlet_solution_boundary_axiom g ψ

/-! #### Wave 26 — Dissolving the uniqueness axiom

The Q50 uniqueness axiom is dissolved here using:
* `harmonic_vanishes_of_global_shell_decay` (Q40, in
  `TreeBoundedHarmonicVanish`): a `PointwiseHarmonic` function with
  uniform shell decay on `F_2` vanishes everywhere.
* Compactness of `F2bar` + uniform continuity to obtain the shell-decay
  hypothesis.
* Density of `F_2` in `F2bar` (`F2_is_dense`) + continuity to lift the
  vanishing from `F_2` to `F2bar`. -/

/-- **Wave 26 bridge — `laplacian_E = 0` ⇒ `PointwiseHarmonic`.**
A function `f : F_2 → ℝ` annihilated by the combinatorial Laplacian on
the 4-regular Cayley graph satisfies the pointwise 1+3 harmonic
identity for every reference ray `φ ∈ ∂F_2`. -/
private lemma pointwiseHarmonic_of_laplacian_E_zero (f : F2 → ℝ)
    (hf : ∀ x : F2, EnsX2026.Graphs.laplacian_E
      (EnsX2026.Cayley.cayley_graph F2_generators) f x = 0)
    (φ : ∂F2) : PointwiseHarmonic φ f := by
  intro x
  obtain ⟨yφ, ⟨hyφ_adj, hyφ_bus⟩, _hyφ_unique⟩ :=
    busemann_neighbour_structure φ x
  obtain ⟨T, hTcard, hT_mem, _hT_cover⟩ :=
    busemann_three_plus_neighbours φ x
  have hyφ_notmem : yφ ∉ T := by
    intro hmem
    have hbus_plus : busemann φ yφ = busemann φ x + 1 := (hT_mem yφ hmem).2
    have hsame : busemann φ x - 1 = busemann φ x + 1 :=
      hyφ_bus.symm.trans hbus_plus
    have h2 : (2 : ℤ) = 0 := by linarith
    exact absurd h2 (by decide)
  refine ⟨yφ, T, hyφ_adj, hyφ_bus, hTcard, hT_mem, hyφ_notmem, ?_⟩
  -- Sum identity: extract `f yφ + Σ_{y ∈ T} f y = 4 · f x` from `laplacian_E = 0`.
  have h_eq := hf x
  rw [EnsX2026.Graphs.laplacian_E_apply, F2_cayley_degree_eq_four x] at h_eq
  have h_nb : (EnsX2026.Cayley.cayley_graph F2_generating_set).neighborFinset x
        = insert yφ T :=
    F2_cayley_neighborFinset_eq_insert φ x yφ T hyφ_adj hyφ_bus
      hTcard hT_mem hyφ_notmem
  -- `F2_generators` is an abbrev for `F2_generating_set`, so the Laplacian
  -- formula already references the same neighbour finset.
  rw [show (EnsX2026.Cayley.cayley_graph F2_generators).neighborFinset x
        = insert yφ T from h_nb] at h_eq
  rw [Finset.sum_insert hyφ_notmem] at h_eq
  push_cast at h_eq
  linarith

/-- **Wave 26 helper — buffer letter for the boundary extension.**
For `x : F_2`, picks a "buffer" letter that does not cancel with the
last letter of `x` (or `(0, true)` if `x = 1`). -/
private def bufferOfF2 (x : F2) : Fin 2 × Bool :=
  if hx : 0 < x.toWord.length then
    let last := x.toWord[x.toWord.length - 1]'(by omega)
    if last = ((0 : Fin 2), false) then ((1 : Fin 2), true)
    else ((0 : Fin 2), true)
  else ((0 : Fin 2), true)

/-- **Wave 26 helper — alternating "other" letter** (different generator
than `bufferOfF2 x`, ensuring no self-cancellation in the alternating
tail). -/
private def otherOfF2 (x : F2) : Fin 2 × Bool :=
  ((⟨1 - (bufferOfF2 x).1.val, by
      have := (bufferOfF2 x).1.isLt; omega⟩ : Fin 2), true)

/-- The buffer's first component differs from the other's first component. -/
private lemma other_fst_ne_buffer (x : F2) :
    (otherOfF2 x).1 ≠ (bufferOfF2 x).1 := by
  intro h_fst
  unfold otherOfF2 at h_fst
  have hval : (⟨1 - (bufferOfF2 x).1.val, by
      have := (bufferOfF2 x).1.isLt; omega⟩ : Fin 2).val
        = (bufferOfF2 x).1.val := congrArg Fin.val h_fst
  have hbuf_lt : (bufferOfF2 x).1.val < 2 := (bufferOfF2 x).1.isLt
  simp at hval
  omega

/-- **Wave 26 bridge — boundary extension of a finite word.**
For every `x : F_2`, there exists a boundary ray `ψ : ∂F_2` whose
first `x.toWord.length` letters agree with the reduced word of `x`.
The extension uses an alternating tail `(0, true), (1, true), …`
prefixed by a one-letter "buffer" picked to avoid cancellation with the
last letter of `x`. -/
private noncomputable def boundaryExtensionOfF2 (x : F2) : F2_boundary :=
  ⟨fun n =>
    if h : n < x.toWord.length then x.toWord[n]'h
    else if (n - x.toWord.length) % 2 = 0 then bufferOfF2 x else otherOfF2 x, by
    -- Prove NonCancellation between consecutive positions.
    intro n
    set m := x.toWord.length with hm_def
    set buffer := bufferOfF2 x with hbuf_def
    set other := otherOfF2 x with hother_def
    -- Key facts about buffer and other.
    have h_other_fst_ne : other.1 ≠ buffer.1 := by
      change (otherOfF2 x).1 ≠ (bufferOfF2 x).1
      exact other_fst_ne_buffer x
    have h_buf_other_nc : NonCancellation buffer other := Or.inl h_other_fst_ne.symm
    have h_other_buf_nc : NonCancellation other buffer := Or.inl h_other_fst_ne
    -- Compute the function explicitly.
    have hval : ∀ k,
        (fun k =>
          if h : k < m then x.toWord[k]'h
          else if (k - m) % 2 = 0 then buffer else other) k =
        (if h : k < m then x.toWord[k]'h
         else if (k - m) % 2 = 0 then buffer else other) := fun _ => rfl
    show NonCancellation _ _
    -- Case-split on n vs m.
    by_cases h₁ : n + 1 < m
    · -- Both `n` and `n+1` < m: use `IsReduced` chain on `x.toWord`.
      have h₀ : n < m := by omega
      rw [hval n, hval (n + 1), dif_pos h₀, dif_pos h₁]
      -- IsReduced gives `(x.toWord[n]).1 = (x.toWord[n+1]).1 → (x.toWord[n]).2 = (x.toWord[n+1]).2`.
      have hred : _root_.FreeGroup.IsReduced x.toWord :=
        _root_.FreeGroup.isReduced_toWord
      have hchain : (x.toWord[n]'h₀).1 = (x.toWord[n + 1]'h₁).1 →
          (x.toWord[n]'h₀).2 = (x.toWord[n + 1]'h₁).2 := hred.getElem n h₁
      by_cases h_eq_fst : (x.toWord[n]'h₀).1 = (x.toWord[n + 1]'h₁).1
      · right; exact hchain h_eq_fst
      · left; exact h_eq_fst
    · by_cases h₀ : n < m
      · -- n < m and n + 1 ≥ m, so n = m - 1, m ≥ 1.
        have hm_pos : 0 < m := by omega
        have hn_eq : n = m - 1 := by omega
        have hidx_zero : n + 1 - m = 0 := by omega
        rw [hval n, hval (n + 1), dif_pos h₀, dif_neg h₁]
        rw [show (n + 1 - m) % 2 = 0 by rw [hidx_zero], if_pos rfl]
        -- Now the goal is NonCancellation (x.toWord[n]) buffer.
        have h_last_eq_pos : x.toWord[n]'h₀ = x.toWord[m - 1]'(by omega) := by
          have hn_eq2 : n = m - 1 := by omega
          simp only [hn_eq2]
        rw [h_last_eq_pos]
        -- Compute buffer = bufferOfF2 x.
        have hbuf_compute : buffer =
            (if x.toWord[m - 1]'(by omega) = ((0 : Fin 2), false) then
              ((1 : Fin 2), true) else ((0 : Fin 2), true)) := by
          rw [hbuf_def]
          unfold bufferOfF2
          rw [dif_pos hm_pos]
        rw [hbuf_compute]
        set last := x.toWord[m - 1]'(by omega) with hlast_def
        by_cases h_last_eq : last = ((0 : Fin 2), false)
        · rw [if_pos h_last_eq, h_last_eq]
          -- NonCancellation ((0, false)) ((1, true)) — first parts differ.
          left; decide
        · rw [if_neg h_last_eq]
          -- NonCancellation last ((0, true)).
          -- The cancellation pattern: (g, b) and (0, true) cancel iff g = 0 ∧ b = false.
          -- We've ruled out last = (0, false), so non-cancellation holds.
          unfold NonCancellation
          by_cases h_lg : last.1 = (0 : Fin 2)
          · -- last = (0, b). Since last ≠ (0, false), we have b = true, so .2 matches.
            right
            -- Show last.2 = true.
            cases hlb : last.2
            · -- last.2 = false.  But last = (last.1, last.2) = (0, false): contradiction.
              exfalso
              apply h_last_eq
              have : last = (last.1, last.2) := by
                obtain ⟨lg, lb⟩ := last; rfl
              rw [this, h_lg, hlb]
            · -- last.2 = true.
              rfl
          · left; exact h_lg
      · -- Both n ≥ m and n + 1 ≥ m. Tail: alternating buffer/other.
        rw [hval n, hval (n + 1), dif_neg h₀, dif_neg h₁]
        have hidx_succ : n + 1 - m = (n - m) + 1 := by omega
        rw [hidx_succ]
        by_cases h_par : (n - m) % 2 = 0
        · rw [if_pos h_par]
          have h_par_succ : ((n - m) + 1) % 2 ≠ 0 := by omega
          rw [if_neg h_par_succ]
          exact h_buf_other_nc
        · rw [if_neg h_par]
          have h_par_succ : ((n - m) + 1) % 2 = 0 := by omega
          rw [if_pos h_par_succ]
          exact h_other_buf_nc⟩

/-- **Wave 26 bridge — coordinate-agreement of the boundary extension.**
The boundary extension `boundaryExtensionOfF2 x` agrees with `x.toWord`
on every index `n < x.toWord.length`. -/
private lemma boundaryExtensionOfF2_val_lt (x : F2) {n : ℕ}
    (hn : n < x.toWord.length) :
    (boundaryExtensionOfF2 x).val n = x.toWord[n]'hn := by
  show (if h : n < x.toWord.length then x.toWord[n]'h
        else _) = x.toWord[n]'hn
  rw [dif_pos hn]

/-- **Wave 26 bridge — the F2bar image of `boundaryExtensionOfF2 x` is
close to the F2bar image of `x`** (within `exp(-|x|)`). -/
private lemma dist_F2_F2bar_boundaryExtension_le (x : F2) :
    dist (((x : F2) : F2bar))
        (((boundaryExtensionOfF2 x : F2_boundary) : F2bar))
      ≤ Real.exp (-(x.toWord.length : ℝ)) := by
  apply EnsX2026.FreeGroup.F2bar.d_prime_le_of_agree
  intro i hi
  -- (F2_to_F2bar x).val i = fbgToExtGen (x.toWord[i]).
  -- (F2_boundary_to_F2bar (boundaryExt x)).val i = fbgToExtGen ((boundaryExt x).val i).
  -- And (boundaryExt x).val i = x.toWord[i] for i < |x|.
  show (F2_to_F2bar x).val i = (F2_boundary_to_F2bar (boundaryExtensionOfF2 x)).val i
  show (if h : i < x.toWord.length then fbgToExtGen (x.toWord[i]'h)
        else ExtGen.one) = fbgToExtGen ((boundaryExtensionOfF2 x).val i)
  rw [dif_pos hi, boundaryExtensionOfF2_val_lt x hi]

/-- **Wave 26 bridge — uniform shell decay from continuity & boundary
vanishing.**  Let `h : F2bar → ℝ` be continuous on the compact space
`F2bar` and vanishing on `F2bar.F2boundary`.  Then the restriction
of `h` to (the image of) `F_2` decays uniformly: for every `ε > 0`,
all sufficiently long words have `|h ((x : F2bar))| < ε`. -/
private lemma uniform_shell_decay_of_boundary_vanishing
    (h : F2bar → ℝ) (h_cont : Continuous h)
    (h_zero_on_bdy : ∀ y : F2bar, y ∈ F2bar.F2boundary → h y = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ y : F2,
      y.toWord.length ≥ R₀ →
        |h ((y : F2) : F2bar)| < ε := by
  intro ε hε
  -- Uniform continuity of h on the compact F2bar.
  have h_unif : UniformContinuous h :=
    CompactSpace.uniformContinuous_of_continuous h_cont
  rw [Metric.uniformContinuous_iff] at h_unif
  obtain ⟨δ, hδ_pos, hδ⟩ := h_unif ε hε
  -- Choose R₀ with `exp(-R₀) < δ`.
  obtain ⟨R₀, hR₀⟩ : ∃ R₀ : ℕ, Real.exp (-(R₀ : ℝ)) < δ := by
    obtain ⟨R₀, hR₀⟩ := exists_nat_gt (-Real.log δ)
    refine ⟨R₀, ?_⟩
    have hlog : -Real.log δ < (R₀ : ℝ) := hR₀
    have hlt : Real.exp (-(R₀ : ℝ)) < Real.exp (Real.log δ) := by
      apply Real.exp_lt_exp.mpr; linarith
    rwa [Real.exp_log hδ_pos] at hlt
  refine ⟨R₀, ?_⟩
  intro y hy_len
  -- Use the boundary extension.
  set ψ := boundaryExtensionOfF2 y with hψ_def
  have h_dist : dist (((y : F2) : F2bar)) ((ψ : F2_boundary) : F2bar)
      ≤ Real.exp (-(y.toWord.length : ℝ)) :=
    dist_F2_F2bar_boundaryExtension_le y
  have h_dist_lt : dist (((y : F2) : F2bar)) ((ψ : F2_boundary) : F2bar) < δ := by
    have hexp_le : Real.exp (-(y.toWord.length : ℝ)) ≤ Real.exp (-(R₀ : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have : (R₀ : ℝ) ≤ (y.toWord.length : ℝ) := by exact_mod_cast hy_len
      linarith
    linarith
  -- Apply uniform continuity at ((y : F2bar), ((ψ : F2bar))).
  have h_uc := hδ h_dist_lt
  -- h on boundary is 0.
  have hψ_in_bdy : ((ψ : F2_boundary) : F2bar) ∈ F2bar.F2boundary :=
    F2_boundary_to_F2bar_mem_F2boundary ψ
  have h_zero : h (((ψ : F2_boundary) : F2bar)) = 0 :=
    h_zero_on_bdy _ hψ_in_bdy
  rw [h_zero] at h_uc
  -- h_uc : dist (h (y : F2bar)) 0 < ε. Convert to |h (y : F2bar)| < ε.
  rwa [Real.dist_eq, sub_zero] at h_uc

/-- **Leaf 9 — discrete maximum principle (uniqueness).** Any two
solutions of the Dirichlet problem coincide.

**Wave 26 — fully proven.**  The proof reduces uniqueness to Q40
(`harmonic_vanishes_of_global_shell_decay`):
1. `h := f₁ - f₂` is continuous on compact `F2bar` and vanishes on
   `F2bar.F2boundary` (boundary agreement).
2. By uniform continuity + the boundary-extension construction, `h`
   restricted to `F_2` has uniform shell decay.
3. By the bridge `pointwiseHarmonic_of_laplacian_E_zero`, the
   restriction is `PointwiseHarmonic` for any reference ray.
4. Apply `harmonic_vanishes_of_global_shell_decay` to conclude
   `h ((x : F2bar)) = 0` for every `x : F2`.
5. Density of `F_2` in `F2bar` (`F2_is_dense`) + continuity then
   force `f₁ = f₂` on all of `F2bar`. -/
lemma dirichlet_solution_unique (g : F2_boundary → ℝ)
    (f₁ f₂ : F2bar → ℝ)
    (h₁ : Continuous f₁ ∧
      (∀ x : F2, EnsX2026.Graphs.laplacian_E
        (EnsX2026.Cayley.cayley_graph F2_generators)
        (fun y : F2 => f₁ ((y : F2) : F2bar)) x = 0) ∧
      (∀ ψ : F2_boundary, f₁ ((ψ : F2_boundary) : F2bar) = g ψ))
    (h₂ : Continuous f₂ ∧
      (∀ x : F2, EnsX2026.Graphs.laplacian_E
        (EnsX2026.Cayley.cayley_graph F2_generators)
        (fun y : F2 => f₂ ((y : F2) : F2bar)) x = 0) ∧
      (∀ ψ : F2_boundary, f₂ ((ψ : F2_boundary) : F2bar) = g ψ)) :
    f₁ = f₂ := by
  obtain ⟨h1_cont, h1_harm, h1_bdy⟩ := h₁
  obtain ⟨h2_cont, h2_harm, h2_bdy⟩ := h₂
  -- Set h := f₁ - f₂.
  set h : F2bar → ℝ := fun y => f₁ y - f₂ y with hh_def
  have h_cont : Continuous h := h1_cont.sub h2_cont
  -- h vanishes on F2bar.F2boundary.
  have h_zero_on_bdy : ∀ y : F2bar, y ∈ F2bar.F2boundary → h y = 0 := by
    intro y hy
    -- Use the homeomorphism F2_boundary ≃ F2bar.F2boundary to write y = (ψ : F2bar).
    set ψ := F2bar_to_F2_boundary y hy with hψ_def
    have hyψ : y = ((ψ : F2_boundary) : F2bar) := by
      rw [hψ_def]
      change y = F2_boundary_to_F2bar (F2bar_to_F2_boundary y hy)
      rw [F2_boundary_to_F2bar_F2bar_to_F2_boundary]
    rw [hyψ]
    show f₁ ((ψ : F2_boundary) : F2bar) - f₂ ((ψ : F2_boundary) : F2bar) = 0
    rw [h1_bdy ψ, h2_bdy ψ]; ring
  -- h restricted to F_2 is harmonic in the laplacian_E sense.
  have h_lap_zero : ∀ x : F2, EnsX2026.Graphs.laplacian_E
      (EnsX2026.Cayley.cayley_graph F2_generators)
      (fun y : F2 => h ((y : F2) : F2bar)) x = 0 := by
    intro x
    -- Unfold laplacian_E pointwise and use linearity by hand.
    rw [EnsX2026.Graphs.laplacian_E_apply]
    have hlap1 := h1_harm x
    have hlap2 := h2_harm x
    rw [EnsX2026.Graphs.laplacian_E_apply] at hlap1 hlap2
    -- The function is `f₁ y - f₂ y` at y = ((·) : F2bar).
    have hfun_eq : ∀ y : F2, h ((y : F2) : F2bar)
        = f₁ ((y : F2) : F2bar) - f₂ ((y : F2) : F2bar) := fun y => rfl
    simp only [hfun_eq]
    -- Sum over neighbours splits.
    rw [Finset.sum_sub_distrib]
    linarith
  -- Pick any boundary ray φ₀ to apply harmonic_vanishes_of_global_shell_decay.
  obtain ⟨φ₀⟩ : Nonempty F2_boundary := by
    by_contra h_empty
    rw [not_nonempty_iff] at h_empty
    have h_prob : (harmonic_measure 1) Set.univ = 1 :=
      (harmonic_measure_isProbabilityMeasure 1).measure_univ
    rw [Set.univ_eq_empty_iff.mpr h_empty, MeasureTheory.measure_empty] at h_prob
    exact (zero_ne_one h_prob)
  -- PointwiseHarmonic for h ∘ (· : F2 → F2bar).
  have h_ph : PointwiseHarmonic φ₀
      (fun y : F2 => h ((y : F2) : F2bar)) :=
    pointwiseHarmonic_of_laplacian_E_zero
      (fun y : F2 => h ((y : F2) : F2bar)) h_lap_zero φ₀
  -- Uniform shell decay.
  have h_shell : ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ y : F2,
      y.toWord.length ≥ R₀ →
        |h ((y : F2) : F2bar)| < ε :=
    uniform_shell_decay_of_boundary_vanishing h h_cont h_zero_on_bdy
  -- Apply harmonic_vanishes_of_global_shell_decay.
  have h_zero_on_F2 : ∀ x : F2, h ((x : F2) : F2bar) = 0 :=
    harmonic_vanishes_of_global_shell_decay φ₀
      (fun y : F2 => h ((y : F2) : F2bar)) h_ph h_shell
  -- Strategy: every y : F2bar is either in F2bar.F2boundary (where h = 0)
  -- or in F2bar.F2finite (where we show h = 0 via continuity + density of
  -- the F2-image, which contains F2finite on a closed set).
  -- We use the closed-set argument:
  --   K := {y : F2bar | h y = 0} is closed.
  --   K contains range(F2_to_F2bar) (h vanishes on F2-images: h_zero_on_F2).
  --   K contains F2bar.F2boundary (h vanishes there: h_zero_on_bdy).
  --   range(F2_to_F2bar) ∪ F2bar.F2boundary = F2bar.
  -- Hence K = F2bar.
  have h_zero_everywhere : ∀ y : F2bar, h y = 0 := by
    intro y
    -- Case 1: y ∈ F2bar.F2boundary.
    by_cases h_in_bdy : y ∈ F2bar.F2boundary
    · exact h_zero_on_bdy y h_in_bdy
    -- Case 2: y ∉ F2bar.F2boundary, so ∃ n, y.val n = ExtGen.one.
    -- We construct x : F2 with F2_to_F2bar x = y.
    have h_finite : ∃ n : ℕ, y.val n = ExtGen.one := by
      by_contra h_no
      apply h_in_bdy
      intro n
      intro h_eq
      apply h_no
      exact ⟨n, h_eq⟩
    classical
    let n₀ : ℕ := Nat.find h_finite
    have hn₀_one : y.val n₀ = ExtGen.one := Nat.find_spec h_finite
    have hn₀_min : ∀ k < n₀, y.val k ≠ ExtGen.one :=
      fun k hk => Nat.find_min h_finite hk
    -- Tail of `y` from `n₀` is all `one`.
    have h_tail_one : ∀ m, n₀ ≤ m → y.val m = ExtGen.one :=
      y.2.2 n₀ hn₀_one
    -- Build the reduced word: list of length n₀.
    -- Each y.val i for i < n₀ is non-one.
    -- We rely on the fact that  y.val i is one of {a, b, aInv, bInv}.
    -- The corresponding (Fin 2 × Bool) is `extGenToFbg (y.val i)`.
    -- Reducedness: the F2bar non-cancellation translates via fbgToExtGen.
    set xWord : List (Fin 2 × Bool) :=
      (List.range n₀).map (fun i => extGenToFbg (y.val i)) with hxWord_def
    have hxWord_length : xWord.length = n₀ := by
      simp [hxWord_def]
    -- Helper: xWord at index k computes to `extGenToFbg (y.val k)`.
    have hxWord_getElem : ∀ k (hk : k < xWord.length),
        xWord[k]'hk = extGenToFbg (y.val k) := by
      intro k hk
      simp [hxWord_def]
    -- Reducedness of xWord — use the chain interpretation of IsReduced.
    have hxWord_reduced : _root_.FreeGroup.IsReduced xWord := by
      -- IsReduced L = L.IsChain fun a b => a.1 = b.1 → a.2 = b.2.
      show _root_.List.IsChain _ xWord
      rw [_root_.List.isChain_iff_getElem]
      intro n hn
      have hn0 : n + 1 < n₀ := by rwa [hxWord_length] at hn
      have hn0' : n < n₀ := Nat.lt_of_succ_lt hn0
      rw [hxWord_getElem n (by rw [hxWord_length]; exact hn0'),
          hxWord_getElem (n + 1) (by rw [hxWord_length]; exact hn0)]
      -- Use existing helper `nonCancellation_of_not_isCancellation` to convert
      -- the F2bar `ExtGen.isCancellation` non-cancellation into the
      -- `Fin 2 × Bool` `NonCancellation` form.
      have hnc : ¬ ExtGen.isCancellation (y.val n) (y.val (n + 1)) := y.2.1 n
      have hyn_ne : y.val n ≠ ExtGen.one := hn₀_min n hn0'
      have hyn1_ne : y.val (n + 1) ≠ ExtGen.one := hn₀_min (n + 1) hn0
      have h_nc_fbg : NonCancellation (extGenToFbg (y.val n)) (extGenToFbg (y.val (n + 1))) :=
        nonCancellation_of_not_isCancellation _ _ hyn_ne hyn1_ne hnc
      -- NonCancellation p q := p.1 ≠ q.1 ∨ p.2 = q.2.
      intro h_eq_fst
      rcases h_nc_fbg with h_fst_ne | h_snd_eq
      · exact absurd h_eq_fst h_fst_ne
      · exact h_snd_eq
    -- Now define x : F2.
    let x : F2 := _root_.FreeGroup.mk xWord
    -- x.toWord = xWord (because xWord is reduced).
    have hx_toWord : x.toWord = xWord := hxWord_reduced.reduce_eq
    -- Length of x equals n₀ (after combining hx_toWord and hxWord_length).
    have hx_length : x.toWord.length = n₀ := by
      rw [hx_toWord]; exact hxWord_length
    -- F2_to_F2bar x = y (pointwise).
    have hxy : F2_to_F2bar x = y := by
      apply F2bar.ext
      intro k
      show (if h : k < x.toWord.length then fbgToExtGen (x.toWord[k]'h)
            else ExtGen.one) = y.val k
      by_cases hk : k < x.toWord.length
      · rw [dif_pos hk]
        have hk' : k < n₀ := by rw [← hx_length]; exact hk
        -- x.toWord[k] = xWord[k] = extGenToFbg (y.val k).
        have hk_xWord : k < xWord.length := by rw [hxWord_length]; exact hk'
        have hxk : fbgToExtGen (x.toWord[k]'hk) = y.val k := by
          have hxw_get : (xWord[k]'hk_xWord) = extGenToFbg (y.val k) :=
            hxWord_getElem k hk_xWord
          have hxk_eq : x.toWord[k]'hk = xWord[k]'hk_xWord := by
            simp [hx_toWord]
          rw [hxk_eq, hxw_get]
          exact fbgToExtGen_extGenToFbg _ (hn₀_min k hk')
        exact hxk
      · rw [dif_neg hk]
        -- y.val k = ExtGen.one for k ≥ n₀ (= x.toWord.length).
        have hk_ge : n₀ ≤ k := by
          rw [← hx_length]; omega
        exact (h_tail_one k hk_ge).symm
    rw [← hxy]
    show h ((x : F2) : F2bar) = 0
    exact h_zero_on_F2 x
  -- Conclude f₁ = f₂.
  funext y
  have := h_zero_everywhere y
  show f₁ y = f₂ y
  linarith [this, show h y = f₁ y - f₂ y from rfl]

/-- **Q50.** For every continuous boundary datum `g : ∂F_2 → ℝ`, there
exists a unique continuous function `f : \overline{F_2} → ℝ` which is
harmonic on `F_2` (in the combinatorial Laplacian sense of `laplacian_E`
on the Cayley graph of `F_2`) and agrees with `g` on the boundary.

The explicit solution is the Poisson integral `dirichlet_solution g`.

**Structured proof.** Existence: `dirichlet_solution g` is a witness,
with its three required properties supplied by
`dirichlet_solution_continuous`, `dirichlet_solution_harmonic`, and
`dirichlet_solution_boundary_eq`.  Uniqueness: `dirichlet_solution_unique`. -/
theorem dirichlet_problem_existence (g : F2_boundary → ℝ)
    (hg : Continuous g) :
    ∃! f : F2bar → ℝ,
      Continuous f ∧
      (∀ x : F2, EnsX2026.Graphs.laplacian_E
        (EnsX2026.Cayley.cayley_graph F2_generators)
        (fun y : F2 => f ((y : F2) : F2bar)) x = 0) ∧
      (∀ ψ : F2_boundary, f ((ψ : F2_boundary) : F2bar) = g ψ) := by
  refine ⟨dirichlet_solution g, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact dirichlet_solution_continuous g hg
  · exact dirichlet_solution_harmonic g hg
  · exact dirichlet_solution_boundary_eq g hg
  · intro f hf
    exact dirichlet_solution_unique g f (dirichlet_solution g) hf
      ⟨dirichlet_solution_continuous g hg,
       dirichlet_solution_harmonic g hg,
       dirichlet_solution_boundary_eq g hg⟩

/-! ### Summary / export -/

/-- Bundling of the three Dirichlet invariants for ease of citation. -/
structure DirichletData (g : F2_boundary → ℝ) where
  /-- The unique continuous harmonic extension. -/
  extension : F2bar → ℝ
  continuous : Continuous extension
  harmonic_interior : ∀ x : F2, EnsX2026.Graphs.laplacian_E
    (EnsX2026.Cayley.cayley_graph F2_generators)
    (fun y : F2 => extension ((y : F2) : F2bar)) x = 0
  boundary_eq : ∀ ψ : F2_boundary, extension ((ψ : F2_boundary) : F2bar) = g ψ

end EnsX2026.FreeGroup

end

