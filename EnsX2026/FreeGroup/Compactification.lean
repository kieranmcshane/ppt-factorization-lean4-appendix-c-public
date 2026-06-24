import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# ENS/Polytechnique 2026 Math A — Q45, Q46, Q47

Compactification of the rank‑2 free group `F₂ = ⟨a, b⟩`.

We represent an element of the compactification `\overline{F₂} = F₂ ∪ ∂F₂` by an
infinite sequence over the extended alphabet `ExtGen = {a, b, a⁻¹, b⁻¹, 1}`
subject to two conditions:

* **No cancellation.** We never have an adjacent pair `(g, g⁻¹)` among the
  generators. (Two consecutive `1`s or a generator next to a `1` are allowed.)
* **Tail of ones.** As soon as some entry is `1`, every subsequent entry is
  also `1` (so finite reduced words of length `n` correspond to sequences
  whose first `n` entries are generators and whose tail is `1`).

The **boundary** `∂F₂` consists of sequences with no `1` anywhere: infinite
reduced words.

The ultrametric is

`d'(x, y) = exp(−p(x, y))`

where `p(x, y)` is the length of the longest common prefix of `x` and `y`
(with the convention that `d'(x, x) = 0`).

**Main statements.**

* `d_prime_ultrametric` (Q45) — `d'` satisfies the strong triangle inequality,
  so `\overline{F₂}` is an ultrametric space.
* `MetricSpace F2bar`, `IsUltrametricDist F2bar` — the induced structure.
* `cylinder_isOpen`, `cylinder_isClosed` — cylinder sets are clopen.
* `F2bar.compactSpace` (Q46) — `\overline{F₂}` is compact.
* `F2_is_dense` (Q46) — `F₂` (the finite words) is dense.
* `boundary_no_isolated_points` (Q47) — no point of `∂F₂` is isolated.
* `boundary_totally_disconnected` (Q47) — `∂F₂` is totally disconnected (its
  connected components are singletons), inherited from the ultrametric.

Institut Fourier, Grenoble — Kieran McShane
-/

namespace EnsX2026.FreeGroup

open Classical
open scoped Topology

noncomputable section

/-- Extended alphabet: the four generators of `F₂` together with the
identity `1` used for padding. -/
inductive ExtGen
  | a : ExtGen
  | b : ExtGen
  | aInv : ExtGen
  | bInv : ExtGen
  | one : ExtGen
  deriving DecidableEq

namespace ExtGen

instance : Fintype ExtGen :=
  ⟨{a, b, aInv, bInv, one}, by intro x; cases x <;> decide⟩

/-- Adjacent letters that would cancel in the free group. -/
def isCancellation : ExtGen → ExtGen → Prop
  | a, aInv => True
  | aInv, a => True
  | b, bInv => True
  | bInv, b => True
  | _, _    => False

instance : DecidablePred (Function.uncurry isCancellation) := by
  intro ⟨x, y⟩
  cases x <;> cases y <;> simp [Function.uncurry, isCancellation] <;> infer_instance

instance (x y : ExtGen) : Decidable (isCancellation x y) := by
  cases x <;> cases y <;> simp [isCancellation] <;> infer_instance

end ExtGen

/-- The compactification `\overline{F₂}`: infinite sequences in the extended
alphabet satisfying no-cancellation and the tail-of-ones condition. -/
def F2bar : Type :=
  { y : ℕ → ExtGen //
    (∀ n : ℕ, ¬ ExtGen.isCancellation (y n) (y (n + 1))) ∧
    (∀ n : ℕ, y n = ExtGen.one → ∀ m, n ≤ m → y m = ExtGen.one) }

namespace F2bar

instance : CoeFun F2bar (fun _ => ℕ → ExtGen) := ⟨fun y => y.val⟩

@[ext]
theorem ext {x y : F2bar} (h : ∀ n, x.val n = y.val n) : x = y :=
  Subtype.ext (funext h)

/-- Two sequences are equal iff they agree on every index. -/
theorem eq_iff {x y : F2bar} : x = y ↔ ∀ n, x.val n = y.val n :=
  ⟨fun h n => by subst h; rfl, ext⟩

/-! ## Common-prefix length and the ultrametric `d_prime` -/

/-- The common prefix length: the least `n` such that `x n ≠ y n`,
    if such an `n` exists (i.e. `x ≠ y`); otherwise `0`. We only invoke it
    when `x ≠ y`, hiding it inside the definition of `d_prime`. -/
def commonPrefixLen (x y : F2bar) : ℕ :=
  if h : ∃ n, x.val n ≠ y.val n then Nat.find h else 0

lemma commonPrefixLen_spec {x y : F2bar} (h : x ≠ y) :
    x.val (commonPrefixLen x y) ≠ y.val (commonPrefixLen x y) ∧
    ∀ i < commonPrefixLen x y, x.val i = y.val i := by
  have hex : ∃ n, x.val n ≠ y.val n := by
    by_contra hne
    push_neg at hne
    exact h (ext hne)
  refine ⟨?_, ?_⟩
  · unfold commonPrefixLen; rw [dif_pos hex]; exact Nat.find_spec hex
  · intro i hi
    unfold commonPrefixLen at hi
    rw [dif_pos hex] at hi
    have := Nat.find_min hex hi
    simpa using this

lemma commonPrefixLen_comm (x y : F2bar) : commonPrefixLen x y = commonPrefixLen y x := by
  by_cases h : x = y
  · subst h; rfl
  have hex : ∃ n, x.val n ≠ y.val n := by
    by_contra hne; push_neg at hne; exact h (ext hne)
  have hey : ∃ n, y.val n ≠ x.val n := by
    obtain ⟨n, hn⟩ := hex; exact ⟨n, hn.symm⟩
  unfold commonPrefixLen
  rw [dif_pos hex, dif_pos hey]
  apply le_antisymm
  · apply Nat.find_le; exact (Nat.find_spec hey).symm
  · apply Nat.find_le; exact (Nat.find_spec hex).symm

/-- The ultrametric distance:
    `d'(x, y) = 0` if `x = y`, else `exp(-commonPrefixLen x y)`. -/
def d_prime (x y : F2bar) : ℝ :=
  if x = y then 0 else Real.exp (-(commonPrefixLen x y : ℝ))

/-! ## Q45 — basic metric axioms -/

theorem d_prime_self (x : F2bar) : d_prime x x = 0 := by
  unfold d_prime; rw [if_pos rfl]

theorem d_prime_nonneg (x y : F2bar) : 0 ≤ d_prime x y := by
  unfold d_prime
  split_ifs with h
  · exact le_refl 0
  · exact (Real.exp_pos _).le

theorem d_prime_comm (x y : F2bar) : d_prime x y = d_prime y x := by
  unfold d_prime
  by_cases h : x = y
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h), commonPrefixLen_comm]

theorem d_prime_eq_zero_iff (x y : F2bar) : d_prime x y = 0 ↔ x = y := by
  unfold d_prime
  constructor
  · intro h
    by_contra hxy
    rw [if_neg hxy] at h
    exact (Real.exp_pos _).ne' h
  · intro h; rw [if_pos h]

/-- The strong (ultrametric) triangle inequality. -/
theorem d_prime_ultrametric (x y z : F2bar) :
    d_prime x z ≤ max (d_prime x y) (d_prime y z) := by
  by_cases hxz : x = z
  · subst hxz
    have h1 : d_prime x x = 0 := d_prime_self x
    have h2 : 0 ≤ max (d_prime x y) (d_prime y x) :=
      le_max_of_le_left (d_prime_nonneg x y)
    linarith
  by_cases hxy : x = y
  · subst hxy
    have h1 : d_prime x x = 0 := d_prime_self x
    have h2 : d_prime x z ≤ max (d_prime x x) (d_prime x z) := le_max_right _ _
    exact h2
  by_cases hyz : y = z
  · subst hyz
    have h1 : d_prime y y = 0 := d_prime_self y
    have h2 : d_prime x y ≤ max (d_prime x y) (d_prime y y) := le_max_left _ _
    exact h2
  -- Now all three are distinct. Let n_xz = commonPrefixLen x z, etc.
  set nxy := commonPrefixLen x y with hnxy_def
  set nyz := commonPrefixLen y z with hnyz_def
  set nxz := commonPrefixLen x z with hnxz_def
  have hxy_agree : ∀ i < nxy, x.val i = y.val i := (commonPrefixLen_spec hxy).2
  have hyz_agree : ∀ i < nyz, y.val i = z.val i := (commonPrefixLen_spec hyz).2
  have hxz_disagree : x.val nxz ≠ z.val nxz := (commonPrefixLen_spec hxz).1
  have key : min nxy nyz ≤ nxz := by
    by_contra hlt
    push_neg at hlt
    have h1 : nxz < nxy := lt_of_lt_of_le hlt (min_le_left _ _)
    have h2 : nxz < nyz := lt_of_lt_of_le hlt (min_le_right _ _)
    exact hxz_disagree ((hxy_agree nxz h1).trans (hyz_agree nxz h2))
  unfold d_prime
  rw [if_neg hxz, if_neg hxy, if_neg hyz]
  -- Goal: exp(-nxz) ≤ max (exp(-nxy)) (exp(-nyz)).
  rcases le_total nxy nyz with hle | hle
  · -- min = nxy, so nxy ≤ nxz, hence exp(-nxz) ≤ exp(-nxy).
    rw [min_eq_left hle] at key
    have hcast : -(nxz : ℝ) ≤ -(nxy : ℝ) := by
      have : (nxy : ℝ) ≤ (nxz : ℝ) := by exact_mod_cast key
      linarith
    have := Real.exp_le_exp.mpr hcast
    exact this.trans (le_max_left _ _)
  · rw [min_eq_right hle] at key
    have hcast : -(nxz : ℝ) ≤ -(nyz : ℝ) := by
      have : (nyz : ℝ) ≤ (nxz : ℝ) := by exact_mod_cast key
      linarith
    have := Real.exp_le_exp.mpr hcast
    exact this.trans (le_max_right _ _)

/-! ## The metric space instance -/

instance : Dist F2bar := ⟨d_prime⟩

@[simp] lemma dist_def (x y : F2bar) : dist x y = d_prime x y := rfl

instance instMetricSpace : MetricSpace F2bar where
  dist := d_prime
  dist_self := d_prime_self
  dist_comm := d_prime_comm
  dist_triangle x y z := by
    -- standard triangle inequality from ultrametric + nonneg
    have h := d_prime_ultrametric x y z
    have hxy := d_prime_nonneg x y
    have hyz := d_prime_nonneg y z
    calc d_prime x z
        ≤ max (d_prime x y) (d_prime y z) := h
      _ ≤ d_prime x y + d_prime y z := by
          rcases le_total (d_prime x y) (d_prime y z) with H | H
          · rw [max_eq_right H]; linarith
          · rw [max_eq_left H]; linarith
  eq_of_dist_eq_zero := by
    intro x y h
    exact (d_prime_eq_zero_iff x y).mp h

instance instIsUltrametricDist : IsUltrametricDist F2bar where
  dist_triangle_max := d_prime_ultrametric

/-! ## Cylinder sets -/

/-- The cylinder set of `y` at level `p`: all sequences agreeing with `y` on
`[0, p)`. -/
def cylinder (y : F2bar) (p : ℕ) : Set F2bar :=
  { z | ∀ i < p, z.val i = y.val i }

lemma mem_cylinder {y z : F2bar} {p : ℕ} :
    z ∈ cylinder y p ↔ ∀ i < p, z.val i = y.val i := Iff.rfl

lemma self_mem_cylinder (y : F2bar) (p : ℕ) : y ∈ cylinder y p := fun _ _ => rfl

/-- Two sequences that agree on `[0, p)` are at ultrametric distance at most
`exp(-p)`. -/
lemma d_prime_le_of_agree {x y : F2bar} {p : ℕ}
    (h : ∀ i < p, x.val i = y.val i) :
    d_prime x y ≤ Real.exp (-(p : ℝ)) := by
  unfold d_prime
  by_cases hxy : x = y
  · subst hxy; simp; exact (Real.exp_pos _).le
  · rw [if_neg hxy]
    have hle : (p : ℝ) ≤ commonPrefixLen x y := by
      -- `commonPrefixLen x y` is at least `p`.
      have := (commonPrefixLen_spec hxy).1
      by_contra hlt
      push_neg at hlt
      -- then commonPrefixLen < p, so h at position commonPrefixLen says they agree
      have : commonPrefixLen x y < p := by exact_mod_cast hlt
      exact (commonPrefixLen_spec hxy).1 (h _ this)
    have : -(commonPrefixLen x y : ℝ) ≤ -(p : ℝ) := by linarith
    exact Real.exp_le_exp.mpr this

/-- If `x ≠ y` and `dist x y < exp(-p)`, then `x` and `y` agree on `[0, p]`.
    (Equivalently `commonPrefixLen ≥ p + 1`.) -/
lemma agree_of_dist_lt {x y : F2bar} {p : ℕ}
    (h : dist x y < Real.exp (-(p : ℝ))) (i : ℕ) (hi : i ≤ p) : x.val i = y.val i := by
  by_cases hxy : x = y
  · subst hxy; rfl
  -- dist x y = exp(-commonPrefixLen), so commonPrefixLen > p, i.e. ≥ p+1.
  rw [dist_def, d_prime, if_neg hxy] at h
  have : (p : ℝ) < commonPrefixLen x y := by
    have : -(commonPrefixLen x y : ℝ) < -(p : ℝ) := by
      by_contra hc; push_neg at hc
      have := Real.exp_le_exp.mpr hc
      exact not_lt.mpr this h
    linarith
  have hp : p < commonPrefixLen x y := by exact_mod_cast this
  have : i < commonPrefixLen x y := lt_of_le_of_lt hi hp
  exact (commonPrefixLen_spec hxy).2 i this

/-- Q45 (geometric formulation): the open ball of radius `exp(-p)` around `y`
equals the cylinder at level `p + 1`. -/
theorem ball_eq_cylinder (y : F2bar) (p : ℕ) :
    Metric.ball y (Real.exp (-(p : ℝ))) = cylinder y (p + 1) := by
  ext z
  simp only [Metric.mem_ball, mem_cylinder]
  constructor
  · intro hz i hi
    -- dist z y < exp(-p), so by agree_of_dist_lt (applied with x=z, y=y) agree at i ≤ p
    exact agree_of_dist_lt (x := z) (y := y) hz i (by omega)
  · intro hi
    have hzy : ∀ i < (p + 1), z.val i = y.val i := hi
    have hle : dist z y ≤ Real.exp (-((p + 1 : ℕ) : ℝ)) :=
      d_prime_le_of_agree hzy
    calc dist z y
        ≤ Real.exp (-((p + 1 : ℕ) : ℝ)) := hle
      _ < Real.exp (-(p : ℝ)) := by
          apply Real.exp_lt_exp.mpr
          push_cast; linarith

/-- Cylinders are open (they are balls). -/
theorem cylinder_isOpen (y : F2bar) (p : ℕ) : IsOpen (cylinder y p) := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    -- cylinder y 0 = univ
    convert isOpen_univ
    ext z; simp [cylinder]
  · -- cylinder y p = ball y (exp(-(p-1)))
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [← ball_eq_cylinder y q]
    exact Metric.isOpen_ball

/-- Cylinders are closed. -/
theorem cylinder_isClosed (y : F2bar) (p : ℕ) : IsClosed (cylinder y p) := by
  -- complement is a union of (disjoint) cylinders, hence open; or directly:
  -- cylinder y p = closed ball of radius exp(-p).
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    convert isClosed_univ
    ext z; simp [cylinder]
  · -- Show cylinder y p ⊇ its closure. We prove: complement is open.
    rw [← isOpen_compl_iff]
    rw [isOpen_iff_mem_nhds]
    intro z hz
    -- z ∉ cylinder y p : ∃ i < p, z.val i ≠ y.val i
    simp only [Set.mem_compl_iff, mem_cylinder, not_forall] at hz
    obtain ⟨i, hi, hne⟩ := hz
    -- On a small ball around z (radius exp(-(p-1))), every point agrees with z on [0,p),
    -- hence still disagrees with y at position i.
    rw [Metric.mem_nhds_iff]
    refine ⟨Real.exp (-((p - 1 : ℕ) : ℝ)), Real.exp_pos _, ?_⟩
    intro w hw
    simp only [Metric.mem_ball] at hw
    simp only [Set.mem_compl_iff, mem_cylinder, not_forall]
    refine ⟨i, hi, ?_⟩
    have hwz : w.val i = z.val i := by
      have := agree_of_dist_lt (x := w) (y := z) hw i (by omega)
      exact this
    rw [hwz]; exact hne

lemma cylinder_isClopen (y : F2bar) (p : ℕ) : IsClopen (cylinder y p) :=
  ⟨cylinder_isClosed y p, cylinder_isOpen y p⟩

/-! ## Q46 — Compactness and density of `F₂` -/

/-- The "finite" subset of `F2bar`: sequences that eventually hit `one`.
    These correspond exactly to elements of the free group `F₂`. -/
def F2finite : Set F2bar :=
  { y : F2bar | ∃ n : ℕ, y.val n = ExtGen.one }

/-- Padding construction: given any sequence `y ∈ F2bar` and a level `p`,
    replace all entries from index `p` onwards by `one`. The resulting
    sequence is in `F2finite` and in `cylinder y p`. -/
def padAt (y : F2bar) (p : ℕ) : F2bar :=
  ⟨fun n => if n < p then y.val n else ExtGen.one, by
    refine ⟨?_, ?_⟩
    · -- No cancellation.
      intro n
      by_cases h1 : n + 1 < p
      · -- both positions in the "y" region, so inherit from y's property.
        have hn : n < p := by omega
        simp [hn, h1]
        exact y.2.1 n
      · by_cases h2 : n < p
        · -- n < p ≤ n+1: entry n is y n, entry n+1 is one — no cancellation (one doesn't cancel).
          simp [h2, h1]
          intro h
          cases (y.val n) <;> simp [ExtGen.isCancellation] at h
        · simp [h2, h1]
          intro h; simp [ExtGen.isCancellation] at h
    · -- tail-of-ones.
      intro n hn m hnm
      by_cases hnp : n < p
      · -- y.val n = one implies (by y's tail-of-ones) y.val k = one for k ≥ n.
        -- But we've replaced the tail with one anyway.
        simp [hnp] at hn
        have := y.2.2 n hn
        by_cases hmp : m < p
        · simp [hmp]; exact this m hnm
        · simp [hmp]
      · simp
        -- m ≥ n ≥ p, so n is in the "one" region.
        by_cases hmp : m < p
        · -- but then m < p ≤ n ≤ m, contradiction.
          omega
        · simp [hmp]⟩

lemma padAt_mem_cylinder (y : F2bar) (p : ℕ) : padAt y p ∈ cylinder y p := by
  intro i hi; simp [padAt, hi]

lemma padAt_mem_F2finite (y : F2bar) (p : ℕ) : padAt y p ∈ F2finite := by
  refine ⟨p, ?_⟩
  simp [padAt]

/-- **Q46 (part 2).** `F₂` (the set of finite words, padded with ones) is
dense in `\overline{F₂}`. -/
theorem F2_is_dense : Dense F2finite := by
  rw [Metric.dense_iff]
  intro y ε hε
  -- choose p with exp(-p) < ε.
  obtain ⟨p, hp⟩ : ∃ p : ℕ, Real.exp (-(p : ℝ)) < ε := by
    -- Take p large enough that -log ε < p, i.e. -p < log ε, i.e. exp(-p) < ε.
    obtain ⟨p, hp⟩ := exists_nat_gt (-Real.log ε)
    refine ⟨p, ?_⟩
    have hlog : -Real.log ε < (p : ℝ) := hp
    have hlt : Real.exp (-(p : ℝ)) < Real.exp (Real.log ε) := by
      apply Real.exp_lt_exp.mpr; linarith
    rw [Real.exp_log hε] at hlt
    exact hlt
  -- padAt y (p+1) is in F2finite and at distance ≤ exp(-(p+1)) < exp(-p) < ε.
  refine ⟨padAt y (p + 1), ?_, padAt_mem_F2finite _ _⟩
  have agree : ∀ i < (p + 1), (padAt y (p + 1)).val i = y.val i := by
    intro i hi
    show (if i < p + 1 then y.val i else ExtGen.one) = y.val i
    rw [if_pos hi]
  have hle : dist (padAt y (p + 1)) y ≤ Real.exp (-((p + 1 : ℕ) : ℝ)) :=
    d_prime_le_of_agree agree
  rw [Metric.mem_ball]
  calc dist (padAt y (p + 1)) y
      ≤ Real.exp (-((p + 1 : ℕ) : ℝ)) := hle
    _ < Real.exp (-(p : ℝ)) := by
        apply Real.exp_lt_exp.mpr; push_cast; linarith
    _ < ε := hp

/-- `F2bar` is totally bounded: for any `ε > 0`, finitely many balls of
radius `ε` cover the space. The discretisation sends a point to its
first `p` entries, where `p` is large enough that `exp(-p) < ε`. -/
theorem F2bar_totallyBounded : TotallyBounded (Set.univ : Set F2bar) := by
  apply Metric.totallyBounded_of_finite_discretization
  intro ε hε
  -- Choose p with exp(-p) < ε.
  obtain ⟨p, hp⟩ : ∃ p : ℕ, Real.exp (-(p : ℝ)) < ε := by
    obtain ⟨p, hp⟩ := exists_nat_gt (-Real.log ε)
    refine ⟨p, ?_⟩
    have : Real.exp (-(p : ℝ)) < Real.exp (Real.log ε) := by
      apply Real.exp_lt_exp.mpr; linarith
    rw [Real.exp_log hε] at this
    exact this
  -- Discretisation via prefixes.
  refine ⟨Fin p → ExtGen, inferInstance,
          fun x => fun i : Fin p => x.val.val i, ?_⟩
  intro x y hxy
  have hagree : ∀ i < p, x.val.val i = y.val.val i := by
    intro i hi
    have := congr_fun hxy ⟨i, hi⟩
    simpa using this
  have := d_prime_le_of_agree (x := x.val) (y := y.val) hagree
  exact lt_of_le_of_lt this hp

/-- `F2bar` is a complete metric space: every Cauchy sequence converges.

For each coordinate `k`, the Cauchy property forces the sequence
`n ↦ u n .val k` to become eventually constant; the limit of the
sequence is the pointwise limit of its coordinates. -/
instance instCompleteSpace : CompleteSpace F2bar := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  rw [Metric.cauchySeq_iff] at hu
  -- For each k, there's N(k) such that m, n ≥ N(k) ⇒ u m . val k = u n . val k.
  have hStab : ∀ k : ℕ, ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
      (u m).val k = (u n).val k := by
    intro k
    have hpos : (0 : ℝ) < Real.exp (-((k + 1 : ℕ) : ℝ)) := Real.exp_pos _
    obtain ⟨N, hN⟩ := hu _ hpos
    refine ⟨N, ?_⟩
    intro m n hm hn
    have hdist : dist (u m) (u n) < Real.exp (-((k + 1 : ℕ) : ℝ)) := hN _ hm _ hn
    exact agree_of_dist_lt (x := u m) (y := u n) hdist k (by omega)
  -- Choose the stabilisation index for each k.
  choose N hN using hStab
  -- Candidate limit sequence: take the value at index N k.
  let a : ℕ → ExtGen := fun k => (u (N k)).val k
  -- Verify `a` satisfies the F2bar conditions.
  have ha_noCancel : ∀ n : ℕ, ¬ ExtGen.isCancellation (a n) (a (n + 1)) := by
    intro n
    -- Pick an index M ≥ N n, N (n+1). Then a n = (u M).val n and a (n+1) = (u M).val (n+1).
    set M := max (N n) (N (n + 1))
    have hMn : N n ≤ M := le_max_left _ _
    have hMn1 : N (n + 1) ≤ M := le_max_right _ _
    have e1 : a n = (u M).val n := hN n _ _ (le_refl _) hMn
    have e2 : a (n + 1) = (u M).val (n + 1) := hN (n + 1) _ _ (le_refl _) hMn1
    rw [e1, e2]
    exact (u M).2.1 n
  have ha_oneAbs : ∀ n : ℕ, a n = ExtGen.one → ∀ m, n ≤ m → a m = ExtGen.one := by
    intro n hn m hnm
    -- Pick index M ≥ N n, N m.
    set M := max (N n) (N m)
    have hMn : N n ≤ M := le_max_left _ _
    have hMm : N m ≤ M := le_max_right _ _
    have e1 : a n = (u M).val n := hN n _ _ (le_refl _) hMn
    have e2 : a m = (u M).val m := hN m _ _ (le_refl _) hMm
    rw [e2]
    have hn' : (u M).val n = ExtGen.one := e1 ▸ hn
    exact (u M).2.2 n hn' m hnm
  let limit : F2bar := ⟨a, ha_noCancel, ha_oneAbs⟩
  refine ⟨limit, ?_⟩
  -- Show u → limit.
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Choose p with exp(-p) < ε.
  obtain ⟨p, hp⟩ : ∃ p : ℕ, Real.exp (-(p : ℝ)) < ε := by
    obtain ⟨p, hp⟩ := exists_nat_gt (-Real.log ε)
    refine ⟨p, ?_⟩
    have : Real.exp (-(p : ℝ)) < Real.exp (Real.log ε) := by
      apply Real.exp_lt_exp.mpr; linarith
    rw [Real.exp_log hε] at this
    exact this
  -- Use stabilisation at level p: take M₀ = max (N 0) (N 1) … (N (p-1)).
  -- Simpler: take the max of N k for k < p+1 using a Finset.
  let M₀ : ℕ := (Finset.range (p + 1)).sup N
  refine ⟨M₀, ?_⟩
  intro n hn
  -- For all k ≤ p, (u n).val k = a k, since n ≥ M₀ ≥ N k.
  have hagree : ∀ k < p + 1, (u n).val k = limit.val k := by
    intro k hk
    have hkN : N k ≤ M₀ := by
      apply Finset.le_sup (f := N) (s := Finset.range (p + 1))
      exact Finset.mem_range.mpr hk
    have hnN : N k ≤ n := le_trans hkN hn
    -- limit.val k = a k = (u (N k)).val k = (u n).val k
    have h1 : (u n).val k = (u (N k)).val k := hN k _ _ hnN (le_refl _)
    show (u n).val k = a k
    rw [h1]
  have hle : dist (u n) limit ≤ Real.exp (-((p + 1 : ℕ) : ℝ)) :=
    d_prime_le_of_agree hagree
  calc dist (u n) limit
      ≤ Real.exp (-((p + 1 : ℕ) : ℝ)) := hle
    _ < Real.exp (-(p : ℝ)) := by
        apply Real.exp_lt_exp.mpr; push_cast; linarith
    _ < ε := hp

/-- **Q46 (part 1).** `\overline{F₂}` is compact.

Proof. We show `F2bar` is totally bounded (finitely many prefixes up to
level `p`, giving a finite `ε`-cover) and complete (each coordinate of a
Cauchy sequence is eventually constant; glue). Then apply
`TotallyBounded.isCompact_of_isComplete`. -/
instance compactSpace : CompactSpace F2bar := by
  rw [← isCompact_univ_iff]
  exact F2bar_totallyBounded.isCompact_of_isComplete
    (isClosed_univ.isComplete)

/-! ## Q47 — the boundary `∂F₂` -/

/-- The boundary of `F2bar`: sequences that never take value `one`. -/
def F2boundary : Set F2bar :=
  { y : F2bar | ∀ n : ℕ, y.val n ≠ ExtGen.one }

lemma F2boundary_isClosed : IsClosed F2boundary := by
  -- complement: ∃ n, y.val n = one. That's an open condition, hence the
  -- complement of the boundary is open.
  rw [← isOpen_compl_iff]
  rw [isOpen_iff_mem_nhds]
  intro z hz
  simp only [Set.mem_compl_iff, F2boundary, Set.mem_setOf_eq, not_forall,
    not_not] at hz
  obtain ⟨n, hn⟩ := hz
  rw [Metric.mem_nhds_iff]
  -- small ball around z: any point agreeing with z on [0, n+1) has value one at n too.
  refine ⟨Real.exp (-(n : ℝ)), Real.exp_pos _, ?_⟩
  intro w hw
  simp only [Metric.mem_ball] at hw
  simp only [Set.mem_compl_iff, F2boundary, Set.mem_setOf_eq, not_forall,
    not_not]
  refine ⟨n, ?_⟩
  have := agree_of_dist_lt (x := w) (y := z) hw n le_rfl
  rw [this]; exact hn

/-- The boundary, viewed as a subtype. -/
def Boundary : Type := { y : F2bar // y ∈ F2boundary }

namespace Boundary

instance : TopologicalSpace Boundary := inferInstanceAs (TopologicalSpace (Subtype _))
instance : MetricSpace Boundary := inferInstanceAs (MetricSpace (Subtype _))
instance : IsUltrametricDist Boundary := inferInstanceAs (IsUltrametricDist (Subtype _))

/-- `∂F₂` is compact (as a closed subset of the compact space `F2bar`). -/
instance : CompactSpace Boundary :=
  isCompact_iff_compactSpace.mp F2boundary_isClosed.isCompact

/-- `∂F₂` is totally disconnected: it inherits this from being an ultrametric
    space. -/
instance : TotallyDisconnectedSpace Boundary := inferInstance

/-- **Q47** (totally disconnected formulation): each singleton in `∂F₂` is
connected (trivially so) — which, combined with total disconnectedness, is
the exam's phrasing that connected components are singletons. -/
theorem singleton_isConnected (y : Boundary) : IsConnected ({y} : Set Boundary) :=
  isConnected_singleton

end Boundary

/-- The key combinatorial fact: at each index, at least three letters
  extend a given reduced prefix without cancellation. This is what
  drives "no isolated points" on the boundary. -/
lemma exists_three_admissible (g : ExtGen) (hg : g ≠ ExtGen.one) :
    ∃ h₁ h₂ h₃ : ExtGen,
      h₁ ≠ h₂ ∧ h₁ ≠ h₃ ∧ h₂ ≠ h₃ ∧
      h₁ ≠ ExtGen.one ∧ h₂ ≠ ExtGen.one ∧ h₃ ≠ ExtGen.one ∧
      ¬ ExtGen.isCancellation g h₁ ∧
      ¬ ExtGen.isCancellation g h₂ ∧
      ¬ ExtGen.isCancellation g h₃ := by
  -- For each non-`one` generator `g`, exactly one of the four generators
  -- cancels with `g`, so three survive.
  cases g with
  | a => exact ⟨.a, .b, .bInv, by decide, by decide, by decide,
          by decide, by decide, by decide, by decide, by decide, by decide⟩
  | b => exact ⟨.a, .aInv, .b, by decide, by decide, by decide,
          by decide, by decide, by decide, by decide, by decide, by decide⟩
  | aInv => exact ⟨.aInv, .b, .bInv, by decide, by decide, by decide,
          by decide, by decide, by decide, by decide, by decide, by decide⟩
  | bInv => exact ⟨.a, .aInv, .bInv, by decide, by decide, by decide,
          by decide, by decide, by decide, by decide, by decide, by decide⟩
  | one => exact absurd rfl hg

/-- A specific non-`one` letter that does not cancel with the given one. It
is used to produce an admissible non-`one` tail. -/
def nextLetter : ExtGen → ExtGen
  | ExtGen.a => ExtGen.b
  | ExtGen.b => ExtGen.a
  | ExtGen.aInv => ExtGen.b
  | ExtGen.bInv => ExtGen.a
  | ExtGen.one => ExtGen.a

lemma nextLetter_ne_one (g : ExtGen) : nextLetter g ≠ ExtGen.one := by
  cases g <;> (unfold nextLetter; decide)

lemma nextLetter_no_cancel (g : ExtGen) (hg : g ≠ ExtGen.one) :
    ¬ ExtGen.isCancellation g (nextLetter g) := by
  cases g
  · decide
  · decide
  · decide
  · decide
  · exact (hg rfl).elim

/-- Iterate `nextLetter` starting from a seed. Used to manufacture a
concrete admissible non-`one` tail. -/
def tailSeq (seed : ExtGen) : ℕ → ExtGen
  | 0 => seed
  | n + 1 => nextLetter (tailSeq seed n)

lemma tailSeq_ne_one (seed : ExtGen) (hseed : seed ≠ ExtGen.one) (n : ℕ) :
    tailSeq seed n ≠ ExtGen.one := by
  induction n with
  | zero => exact hseed
  | succ n _ => simp [tailSeq]; exact nextLetter_ne_one _

lemma tailSeq_no_cancel (seed : ExtGen) (hseed : seed ≠ ExtGen.one) (n : ℕ) :
    ¬ ExtGen.isCancellation (tailSeq seed n) (tailSeq seed (n + 1)) := by
  simp only [tailSeq]
  exact nextLetter_no_cancel _ (tailSeq_ne_one seed hseed n)

/-- **Q47.** No point of the boundary is isolated. Formally: the singleton
`{y}` is not a neighbourhood of `y` in the ambient space `F2bar` when `y`
is in the boundary. (Equivalently, every open set containing `y` contains a
second boundary point.)

Proof. Given `y ∈ ∂F₂` and `ε > 0`, pick `p` with `exp(-(p+1)) < ε`. Using
`exists_three_admissible` applied to `y.val p` (non-`one` since `y` is in the
boundary), choose among the three admissible successors one, `alt`, that
differs from `y.val (p+1)`. Build `z` agreeing with `y` on `[0, p+1)`, equal
to `alt` at `p+1`, and continued by iterating `nextLetter` afterwards. Then
`z ∈ ∂F₂`, `z ≠ y`, and `dist z y ≤ exp(-(p+1)) < ε`. -/
theorem boundary_no_isolated_points :
    ∀ y : F2bar, y ∈ F2boundary → ¬ ({y} : Set F2bar) ∈ 𝓝 y := by
  intro y hy hmem
  rw [Metric.mem_nhds_iff] at hmem
  obtain ⟨ε, hε, hsub⟩ := hmem
  -- Choose p with exp(-(p+1)) < ε.
  obtain ⟨p, hp⟩ : ∃ p : ℕ, Real.exp (-((p + 1 : ℕ) : ℝ)) < ε := by
    obtain ⟨p, hp⟩ := exists_nat_gt (-Real.log ε)
    refine ⟨p, ?_⟩
    have hlog : -Real.log ε < (p : ℝ) := hp
    have : Real.exp (-((p + 1 : ℕ) : ℝ)) < Real.exp (Real.log ε) := by
      apply Real.exp_lt_exp.mpr
      push_cast; linarith
    rw [Real.exp_log hε] at this
    exact this
  -- `y.val p` is not `one`.
  have hyp_ne_one : y.val p ≠ ExtGen.one := hy p
  -- Get three admissible successors of `y.val p`.
  obtain ⟨h₁, h₂, h₃, h12, h13, h23, h1one, h2one, h3one,
          hc1, hc2, hc3⟩ := exists_three_admissible (y.val p) hyp_ne_one
  -- Pick an `alt ∈ {h₁, h₂, h₃}` with `alt ≠ y.val (p+1)`.
  have hpick : ∃ alt : ExtGen, alt ≠ y.val (p + 1) ∧ alt ≠ ExtGen.one ∧
      ¬ ExtGen.isCancellation (y.val p) alt := by
    by_cases e1 : h₁ = y.val (p + 1)
    · by_cases e2 : h₂ = y.val (p + 1)
      · -- then h₃ ≠ y.val (p+1) since h₂ ≠ h₃ but h₂ = y.val (p+1).
        exact ⟨h₃, fun h => h23 (e2.trans h.symm), h3one, hc3⟩
      · exact ⟨h₂, e2, h2one, hc2⟩
    · exact ⟨h₁, e1, h1one, hc1⟩
  obtain ⟨alt, halt_ne, halt_one, halt_cancel⟩ := hpick
  -- Build the perturbed sequence.
  let zseq : ℕ → ExtGen := fun i =>
    if i ≤ p then y.val i
    else if i = p + 1 then alt
    else tailSeq alt (i - (p + 2))
  -- Verify membership in F2bar.
  have hz_noCancel : ∀ n : ℕ, ¬ ExtGen.isCancellation (zseq n) (zseq (n + 1)) := by
    intro n
    by_cases hn : n + 1 ≤ p
    · -- both positions in [0, p].
      have hn0 : n ≤ p := by omega
      simp only [zseq, if_pos hn0, if_pos hn]
      exact y.2.1 n
    · by_cases hn2 : n ≤ p
      · -- n ≤ p, n+1 > p, so n = p, n+1 = p+1.
        have hnp : n = p := by omega
        have hsucc : n + 1 = p + 1 := by omega
        simp only [zseq, if_pos hn2, if_neg hn]
        rw [if_pos hsucc, hnp]
        exact halt_cancel
      · -- n > p.
        push_neg at hn2
        by_cases hneq : n = p + 1
        · -- n = p+1, n+1 = p+2.
          have hngt : ¬ n ≤ p := by omega
          have hnsuccgt : ¬ n + 1 ≤ p := by omega
          have hnsuccne : n + 1 ≠ p + 1 := by omega
          simp only [zseq, if_neg hngt, if_neg hnsuccgt, if_pos hneq, if_neg hnsuccne]
          -- zseq (p+2) = tailSeq alt ((p+2) - (p+2)) = tailSeq alt 0 = alt.
          -- But wait, we want isCancellation alt (tailSeq alt ((p+2) - (p+2))) = isCancellation alt alt.
          -- Actually we want isCancellation alt (tailSeq alt 0 .next) = isCancellation alt (tailSeq alt 1).
          -- Hmm: zseq (n+1) where n = p+1, so n+1 = p+2, and (p+2) - (p+2) = 0, so zseq(p+2) = tailSeq alt 0 = alt.
          -- Wait, then isCancellation alt alt should be false.
          have : n + 1 - (p + 2) = 0 := by omega
          rw [this]
          show ¬ ExtGen.isCancellation alt (tailSeq alt 0)
          simp [tailSeq]
          -- ¬ isCancellation alt alt: always true since isCancellation g g = False for all g.
          cases alt <;> simp [ExtGen.isCancellation]
        · -- n ≥ p + 2.
          have hnge : p + 2 ≤ n := by omega
          have hngt : ¬ n ≤ p := by omega
          have hnsuccgt : ¬ n + 1 ≤ p := by omega
          have hneq2 : n + 1 ≠ p + 1 := by omega
          simp only [zseq, if_neg hngt, if_neg hnsuccgt, if_neg hneq, if_neg hneq2]
          -- zseq n = tailSeq alt (n - (p+2)); zseq (n+1) = tailSeq alt (n+1 - (p+2)).
          have hidx : n + 1 - (p + 2) = (n - (p + 2)) + 1 := by omega
          rw [hidx]
          exact tailSeq_no_cancel alt halt_one _
  have hz_oneAbs : ∀ n : ℕ, zseq n = ExtGen.one →
      ∀ m, n ≤ m → zseq m = ExtGen.one := by
    intro n hn m hnm
    -- zseq n never equals one.
    exfalso
    by_cases hnp : n ≤ p
    · simp only [zseq, if_pos hnp] at hn
      exact hy n hn
    · by_cases heq : n = p + 1
      · simp only [zseq, if_neg hnp, if_pos heq] at hn
        exact halt_one hn
      · have hngt : ¬ n ≤ p := hnp
        simp only [zseq, if_neg hngt, if_neg heq] at hn
        exact tailSeq_ne_one alt halt_one _ hn
  let z : F2bar := ⟨zseq, hz_noCancel, hz_oneAbs⟩
  -- z and y agree on [0, p+1).
  have hagree : ∀ i < p + 1, z.val i = y.val i := by
    intro i hi
    have : i ≤ p := by omega
    show zseq i = y.val i
    simp only [zseq, if_pos this]
  -- z differs from y at p+1.
  have hdiff : z.val (p + 1) ≠ y.val (p + 1) := by
    show zseq (p + 1) ≠ y.val (p + 1)
    have hnle : ¬ p + 1 ≤ p := by omega
    simp only [zseq, if_neg hnle]
    exact halt_ne
  -- So z ≠ y.
  have hzy : z ≠ y := fun h => hdiff (by rw [h])
  -- dist z y ≤ exp(-(p+1)).
  have hdist : dist z y ≤ Real.exp (-((p + 1 : ℕ) : ℝ)) :=
    d_prime_le_of_agree hagree
  -- So dist z y < ε, hence z ∈ Metric.ball y ε ⊆ {y}, forcing z = y: contradiction.
  have hzball : z ∈ Metric.ball y ε := by
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt hdist hp
  have : z = y := hsub hzball
  exact hzy this

/-- **Q47** (connectedness form): connected components in `F2bar` are
singletons. -/
theorem connectedComponent_singleton (y : F2bar) : connectedComponent y = {y} := by
  exact connectedComponent_eq_singleton y

end F2bar

end

end EnsX2026.FreeGroup
