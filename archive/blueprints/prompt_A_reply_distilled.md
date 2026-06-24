# Prompt A — User's self-contained proof, distilled for Lean encoding

> **Source.** Reply from the user to `wave_problem_asker_A.md`.
> Conversation JSONL message at:
> `/Users/kieranmcshane/.claude/projects/-Users-kieranmcshane-Documents-Claude-Projects-Article-PPT-ppt-factorization-lean4/670854ae-84c8-4de8-9f8d-e3c6fc601ce8.jsonl`,
> opening with the line `here is an answer to Prompt A.` (verified
> located at line 2614 of the JSONL via `rg -n "Prompt A"`).
> Verbatim transcription where possible; minor formatting cleanup
> only (LaTeX kept; math notation harmonised with the project's Lean
> encoding when introducing the encoding map).

## Statement (matches `harmonic_measure_translation_on_deep_cylinder`)

For every vertex `x : F2`, every boundary point `φ : F2_boundary`,
and every integer `q ≥ x.toWord.length`,
```
μ_x(I(φ, q)) = p_φ(x) · μ_1(I(φ, q))
```
where `p_φ(x) = 3^{−b_φ(x)} = 3^{−(|x| − 2 c(x, φ))}` and
`c(x, φ) = common_prefix_length x φ`.

In Lean it is currently stated as:
```
theorem harmonic_measure_translation_on_deep_cylinder
    (x : F2) (φ : F2_boundary) (q : ℕ) (hq : x.toWord.length ≤ q) :
    (harmonic_measure x (cylinder φ q)).toReal
      = poisson_kernel φ x * (harmonic_measure 1 (cylinder φ q)).toReal
```
(at the `.toReal` level; both ENNReal sides are finite as harmonic
measures of cylinders on a probability space).

The current proof in `EnsX2026/FreeGroup/ExitMeasure.lean` (lines
2066+, post-Wave-29-retry) derives this from two project axioms,
`harmonic_measure_factor_at_meeting_vertex_x` (line 2021) and
`harmonic_measure_factor_at_meeting_vertex_one` (line 2035).
**Both of those axioms are dissolvable** — the user's reply is a
self-contained proof from project primitives plus a single hitting-
probability lemma (Lemma 1 below) and a single strong-Markov
invocation. No Mathlib gap need be admitted as an axiom.

## Proof (verbatim from user)

We prove the identity by computing the hitting probabilities of the
simple random walk on the 4-regular tree and applying the strong
Markov property at the common prefix of the walk's starting point and
the fixed end.

---

### 1.  Hitting probabilities on the 4-regular tree

Let `T` be the infinite 4-regular tree. For a vertex `v`, let `P_v`
be the law of the simple random walk `(W_n)_{n ≥ 0}` started at
`W_0 = v`. For a vertex `w`, let
```
T_w = inf{n ≥ 0 : W_n = w}
```
be the first hitting time. Because `T` is vertex-transitive, the
quantity
```
f(k) := P_a(T_b < ∞),  where d(a, b) = k,
```
depends only on the graph distance `k`.

**Lemma 1.** `f(k) = 3^{−k}` for every `k ≥ 0`.

*Proof.* Clearly `f(0) = 1`. First compute `f(1)`. Let `a, b` be
neighbours. From `a` the walk moves to `b` with probability `1/4`;
with probability `3/4` it moves to one of the three other neighbours.
If it moves to such a neighbour `z`, then the unique path from `z` to
`b` passes through `a`; hence `T_b < ∞` forces `T_a < T_b < ∞`. By
the strong Markov property at `T_a`,
```
P_z(T_b < ∞) = P_z(T_a < ∞) · P_a(T_b < ∞) = f(1)^2.
```
Therefore
```
f(1) = (1/4) · 1 + (3/4) · f(1)^2.
```
The quadratic `3 f(1)^2 − 4 f(1) + 1 = 0` has roots `1` and `1/3`.
The simple random walk on a regular tree of degree 4 is transient
(the distance from the starting point is a birth-death chain with
positive drift `p = 3/4` for outward steps when not at the root), so
`f(1) < 1`. Hence `f(1) = 1/3`.

Now proceed by induction on `k ≥ 2`. Assume `f(k − 1) = 3^{−(k−1)}`.
Let `a, b` satisfy `d(a, b) = k` and let `a₁` be the neighbour of `a`
on the unique geodesic to `b`. From `a` the walk steps to `a₁` with
probability `1/4`, reducing the distance to `k − 1`. With probability
`3/4` it steps to a vertex `z` that lies off the geodesic; then
`d(z, b) = k + 1` and the unique path from `z` to `b` again goes
through `a`. Hence
```
P_z(T_b < ∞) = P_z(T_a < ∞) · P_a(T_b < ∞) = f(1) · f(k) = (1/3) · f(k).
```
Using the strong Markov property at `T_a` (or directly the Markov
property for the first step) we obtain
```
f(k) = (1/4) · f(k − 1) + (3/4) · (1/3) · f(k)
     = (1/4) · 3^{−(k−1)} + (1/4) · f(k).
```
Rearranging gives `(3/4) f(k) = (1/4) · 3^{−(k−1)}`, so
`f(k) = (1/3) · 3^{−(k−1)} = 3^{−k}`. ∎

---

### 2.  Geometric decomposition of the cylinder event

Fix an end `φ ∈ ∂T` and an integer `q ≥ 0`. Let `v_q` be the vertex
on the ray `φ` at distance `q` from the root `o`; it is the reduced
word of length `q` that is the prefix of `φ`. The cylinder
```
I(φ, q) = {ψ ∈ ∂T : ψ_i = φ_i ∀ i < q}
```
is exactly the set of ends whose rays start at `o` and pass through
`v_q` (and then continue without backtracking). In particular, any
end in `I(φ, q)` contains the whole segment from `o` to `v_q`.

Now fix a starting vertex `x ∈ T` and let `c = c(x, φ)` be the length
of the longest common prefix of the reduced word for `x` and the ray
`φ`. Let `u` be the vertex on `φ` at distance `c` from `o`. By
definition, the geodesic from `o` to `x` coincides with `φ` up to `u`
and then branches away; therefore
```
d(x, u) = |x| − c,   d(o, u) = c.
```
The assumption `q ≥ |x|` guarantees `q ≥ c`, so `u` lies between `o`
and `v_q` on `φ`.

Let `X^x_∞` denote the random end to which the walk from `x` converges
almost surely, and set `μ_x = P_x(X^x_∞ ∈ ·)`. If `X^x_∞ ∈ I(φ, q)`,
then the ray from `o` to the limit end contains `v_q`, and therefore
it contains `u`. Because the walk converges to that end, it must
eventually visit `u`. Hence
```
{X^x_∞ ∈ I(φ, q)} ⊆ {T_u < ∞}.
```
Apply the strong Markov property at the stopping time `T_u`. On the
event `{T_u < ∞}`, the process after `T_u` is a simple random walk
started at `u`, independent of the past. The event
`{X_∞ ∈ I(φ, q)}` is a tail event, so
```
P_x(X_∞ ∈ I(φ, q) | T_u < ∞) = P_u(X_∞ ∈ I(φ, q)).
```
Consequently,
```
μ_x(I(φ, q)) = P_x(T_u < ∞) · P_u(X_∞ ∈ I(φ, q)).        (1)
```
The same reasoning starting from the root `o` (with its own first
hitting time of `u`) yields
```
μ_o(I(φ, q)) = P_o(T_u < ∞) · P_u(X_∞ ∈ I(φ, q)).        (2)
```

---

### 3.  Evaluation and conclusion

From Lemma 1 and the distances computed above,
```
P_x(T_u < ∞) = f(d(x, u)) = 3^{−(|x|−c)},
P_o(T_u < ∞) = f(c)       = 3^{−c}.
```
Insert these into (1) and (2) and take the ratio (or eliminate the
common factor `P_u`):
```
μ_x(I(φ, q)) = 3^{−(|x|−c)} · P_u(X_∞ ∈ I(φ, q))
             = (3^{−(|x|−c)} / 3^{−c}) · μ_o(I(φ, q))
             = 3^{−(|x| − 2c)} · μ_o(I(φ, q)).
```
The Busemann function of `φ` is `b_φ(x) = |x| − 2 c(x, φ)`. Since
`c = c(x, φ)`,
```
μ_x(I(φ, q)) = 3^{−b_φ(x)} · μ_o(I(φ, q))
```
for every `x ∈ T`, every `φ ∈ ∂T`, and every integer `q ≥ |x|`.
This completes the proof. ∎

---

## Lean encoding map — step by step

The user's proof has **three substantive ingredients** that must be
encoded in Lean:

1. The **hitting-probability lemma** (Lemma 1, `f(k) = 3^{−k}`).
2. The **inclusion** `{X_∞ ∈ I(φ, q)} ⊆ {T_u < ∞}` (geometric, no
   probability).
3. The **strong-Markov factorisation** at `T_u` (the technical heart).

Two derived facts close the proof:

4. `d(x, u) = |x| − c` and `d(o, u) = c` (combinatorial).
5. Algebraic combination of (1), (2), (3), (4) into the deep-cylinder
   identity.

Each ingredient maps to one or more Lean sub-lemmas. **No new axioms
needed** — every step decomposes into either project primitives
(`step_measure`, `X_walk`, `X_infinity`, `harmonic_measure`) or
Mathlib infrastructure that exists (Markov property of
`Measure.infinitePi`, hitting times of countable-state chains).

The two existing project axioms #3
(`harmonic_measure_factor_at_meeting_vertex_x`) and #4
(`harmonic_measure_factor_at_meeting_vertex_one`) are exactly equation
(1) with `x` and (2) with `o = 1`, respectively. So the dissolution
plan is: derive (1) and (2) as theorems from sub-lemmas below, and
the existing top-level
`harmonic_measure_translation_on_deep_cylinder` becomes axiom-free.

### Step 1 — Hitting time as a stopping time
**User's claim.** *"`T_w = inf{n ≥ 0 : W_n = w}` is a stopping time."*
**Lean sub-lemma needed.**
```
noncomputable def hittingTime (x w : F2) (Y : ℕ → F2) : ℕ∞ :=
  sInf {n : ℕ | x * X_walk n Y = w}
        -- (or `⊤` if the set is empty)

lemma hittingTime_isStoppingTime (x w : F2) :
    IsStoppingTime (Filtration.natural ...)
                   (fun Y => hittingTime x w Y)
```
**Existing infrastructure.** `step_measure`, `X_walk`, the natural
filtration `σ(Y_0, …, Y_{n−1})` (Mathlib has `Filtration.natural` for
discrete-time stochastic processes; can be specialised to
`Measure.infinitePi`).
**New infrastructure.** Need to instantiate `Filtration.natural` for
the random-walk position process `n ↦ x · X_walk n Y` on the
discrete-target space `F2`. Each `X_walk n` is already proved
measurable (`X_walk_measurable` in `RandomWalk.lean:177`).
**Estimated LOC.** ~30 (definition + stopping-time lemma).

### Step 2 — Hitting probability `f(k) = 3^{−k}` (Lemma 1)
**User's claim.** *"`f(k) = 3^{−k}` for every `k ≥ 0`."*
**Lean sub-lemma needed.**
```
lemma hittingProb_eq (a b : F2) (k : ℕ) (h : F2_distance a b = k) :
    step_measure {Y | hittingTime a b Y < ∞}
      = ENNReal.ofReal (3 ^ (-(k : ℤ)))
```
**Substeps.**

* (a) `f(0) = 1`: trivial; `hittingTime a a Y = 0` since
  `X_walk 0 Y = 1`, so `a * 1 = a`.
* (b) `f(1) = 1/3`: solve quadratic. Requires the strong Markov
  property at `T_a` for an off-geodesic neighbour, plus transience
  (used to discard the spurious root `1`).
* (c) Induction `k ≥ 2`: one Markov step + strong Markov at `T_a`,
  algebra.

**Existing infrastructure.** Vertex-transitivity of the 4-regular
tree (the project hasn't formalised this directly but it follows from
the `F2`-action by left multiplication; should already be implicit in
the use of `harmonic_measure x` for general `x`).

**New infrastructure required from Mathlib / project.**

* **Strong Markov for the i.i.d.-step random walk on `F2`.** This is
  the only genuinely heavy dependency. The walk is the canonical SRW
  driven by `step_measure = Measure.infinitePi (fun _ => Z_uniform)`,
  so strong Markov reduces to:

  *Sub-lemma SM.* For any stopping time `τ : (ℕ → F2) → ℕ∞` w.r.t. the
  natural filtration of `step_measure`, and any measurable
  `g : (ℕ → F2) → ℝ≥0∞` depending only on the post-`τ` shift,
  ```
  ∫ Y, g(shift_τ Y) ∂step_measure
    = ∫ Y, [τ < ∞] · (∫ Y', g(Y') ∂step_measure) ∂step_measure
  ```
  where `shift_τ Y n = Y (τ + n)`.

  Mathlib has `MeasureTheory.Martingale.OptionalStopping`-style
  infrastructure, and for i.i.d. product measures the strong Markov
  property is essentially the **shift-invariance of**
  `Measure.infinitePi` combined with **measurable selection** of the
  τ-th coordinate. It is *not* yet available as a packaged lemma but
  can be built in ~80–120 LOC as a sibling helper file
  `EnsX2026/FreeGroup/StrongMarkov.lean`.

  **NB.** Because `step_measure` is the *infinite product* of i.i.d.
  steps, strong Markov here is strictly weaker than the general
  Markov-chain strong Markov theorem: it is just the statement that
  i.i.d. sequences are exchangeable across stopping times, which is
  Galmarino-style (see Mathlib's `Measure.IsIIDProcess` /
  `Measure.infinitePi.shift_eq`). A direct combinatorial proof using
  `Measure.infinitePi_apply` and partition over `{τ = n}` events is
  feasible in ~50 LOC.

**Estimated LOC.** ~60 (Lemma 1 itself, given strong Markov as a
black box) + ~80–120 (the strong-Markov helper).

### Step 3 — Inclusion of the cylinder event in `{T_u < ∞}`
**User's claim.** *"If `X^x_∞ ∈ I(φ, q)`, the ray from `o` to the
limit end contains `u`. Because the walk converges to that end, it
must eventually visit `u`."*
**Lean sub-lemma needed.**
```
lemma cylinder_event_subset_hits_meeting_vertex
    (x : F2) (φ : F2_boundary) (q : ℕ) (hq : x.toWord.length ≤ q) :
  let c := common_prefix_length x φ
  let u := F2_boundary.valPrefix φ c
  walkPrefixEvent x φ q
    ⊆ {Y | hittingTime x u Y < ∞}
```
**Reasoning.** A walk converging to a boundary point `ψ ∈ I(φ, q)`
has its image eventually in any ball around `ψ`'s ray; in particular,
since the geodesic to `ψ` passes through `u` (which is at depth
`c ≤ q`), the walk must visit `u`. This uses convergence
`X_walk n → X_infinity` in the boundary topology, which the project
has already encoded.
**Existing infrastructure.** `X_infinity` definition + the fact that
the walk visits every prefix of its limit (this should already be
part of the construction; needs verification in
`X_infinity` definition at `ExitMeasure.lean:908`).
**New infrastructure.** Likely a small helper on
`F2_boundary.valPrefix` and `X_walk` showing that for any `Y` with
`X_infinity Y ∈ cylinder φ q`, the trajectory `(X_walk n Y)_n`
contains `F2_boundary.valPrefix φ c` for any `c ≤ q`. Roughly
30–50 LOC; should compose existing lemmas.
**Estimated LOC.** ~40.

### Step 4 — Strong Markov at `T_u` for the cylinder event
**User's claim.** *"On the event `{T_u < ∞}`, the process after `T_u`
is a simple random walk started at `u`, independent of the past. The
event `{X_∞ ∈ I(φ, q)}` is a tail event, so
`P_x(X_∞ ∈ I(φ, q) | T_u < ∞) = P_u(X_∞ ∈ I(φ, q))`."*
**Lean sub-lemma needed.**
```
lemma harmonic_measure_strong_markov_at_hittingTime
    (x u : F2) :
  step_measure (walkPrefixEvent x φ q ∩ {Y | hittingTime x u Y < ∞})
    = step_measure {Y | hittingTime x u Y < ∞}
      * harmonic_measure u (cylinder φ q)
```
**Reasoning.** Direct application of strong Markov (Step 2's helper)
with `g(Y) = walkPrefixEvent u φ q Y` (the indicator of the cylinder
event under a walk starting at `u`).
**Existing infrastructure.** Same as Step 2: the project's
`harmonic_measure u (cylinder φ q) = step_measure (walkPrefixEvent u φ q)`
(via `harmonic_measure_cylinder_eq_walk_event`, ExitMeasure.lean:1281).
**New infrastructure.** Strong-Markov helper from Step 2.
**Estimated LOC.** ~40.

### Step 5 — Equation (1): factorisation from `x` (=axiom #3)
**User's claim.** *"`μ_x(I(φ, q)) = P_x(T_u < ∞) · μ_u(I(φ, q))`."*
**Lean sub-lemma needed.** Exactly the body of axiom #3:
```
theorem harmonic_measure_factor_at_meeting_vertex_x
    (x : F2) (φ : F2_boundary) (q : ℕ) (hq : x.toWord.length ≤ q) :
    harmonic_measure x (cylinder φ q)
      = ENNReal.ofReal
          ((3 : ℝ) ^ (-((x.toWord.length : ℤ) - common_prefix_length x φ)))
        * harmonic_measure (F2_boundary.valPrefix φ (common_prefix_length x φ))
            (cylinder φ q)
```
**Reasoning.** Combine Step 3 (`cylinder event ⊆ T_u < ∞`, so the
intersection in Step 4 simplifies to `walkPrefixEvent x φ q`), Step 4
(strong-Markov factorisation), and Step 2 with `k = |x| − c`
(`step_measure {T_u < ∞} = 3^{−(|x|−c)}`).
**Existing infrastructure.** All Steps 1–4 above, plus
`harmonic_measure_cylinder_eq_walk_event` (ExitMeasure.lean:1281) to
convert from `harmonic_measure x` to `step_measure (walkPrefixEvent
x …)`.
**New infrastructure.** None new beyond Steps 1–4.
**Estimated LOC.** ~30 (assembly).

### Step 6 — Equation (2): factorisation from `1` (=axiom #4)
**User's claim.** *"`μ_o(I(φ, q)) = P_o(T_u < ∞) · μ_u(I(φ, q))`."*
**Lean sub-lemma needed.** Exactly the body of axiom #4:
```
theorem harmonic_measure_factor_at_meeting_vertex_one
    (x : F2) (φ : F2_boundary) (q : ℕ) (hq : x.toWord.length ≤ q) :
    harmonic_measure 1 (cylinder φ q)
      = ENNReal.ofReal ((3 : ℝ) ^ (-(common_prefix_length x φ : ℤ)))
        * harmonic_measure (F2_boundary.valPrefix φ (common_prefix_length x φ))
            (cylinder φ q)
```
**Reasoning.** Specialisation of Step 5 with `x ↦ 1`, except the
hitting-probability exponent is `c = |u|` instead of `|x| − c`.
Re-uses Steps 3–4 (with start `1` instead of `x`) and Step 2 with
`k = c`.
**Existing infrastructure.** Same as Step 5.
**New infrastructure.** None.
**Estimated LOC.** ~25 (mostly cut-and-paste from Step 5; the only
substitution is the start-vertex of the walk).

### Step 7 — Algebraic conclusion
**User's claim.** *"Insert these into (1) and (2) and take the ratio:
`μ_x(I(φ, q)) = 3^{−(|x|−2c)} · μ_o(I(φ, q)) = p_φ(x) · μ_o(I(φ, q))`."*
**Lean sub-lemma needed.** The existing
`harmonic_measure_translation_on_deep_cylinder` (ExitMeasure.lean:2066)
already does this — once Steps 5 and 6 are theorems instead of axioms,
it becomes axiom-free.
**Existing infrastructure.** The current proof body of
`harmonic_measure_translation_on_deep_cylinder`. No changes needed.
**Estimated LOC.** 0 (existing proof body is already correct; just
delete the `axiom` declarations once Steps 5 and 6 land as theorems).

---

## Total budget estimate

| Step | LOC |
|------|-----|
| Step 1 — hitting time as stopping time | ~30 |
| Step 2 — Lemma 1 (`f(k) = 3^{−k}`) | ~60 |
| Strong-Markov helper (`StrongMarkov.lean`, sibling file) | ~80–120 |
| Step 3 — cylinder event ⊆ `{T_u < ∞}` | ~40 |
| Step 4 — strong-Markov at `T_u` for cylinder | ~40 |
| Step 5 — equation (1) (=axiom #3 dissolved) | ~30 |
| Step 6 — equation (2) (=axiom #4 dissolved) | ~25 |
| Step 7 — algebraic glue | 0 |
| **Total** | **~305–345 LOC** |

For comparison, the current Wave 29-retry approach has **2 axioms**
(~50 LOC of axiom statements + docstrings) plus the ~130-LOC algebra
of `harmonic_measure_translation_on_deep_cylinder`. Dissolving them
costs ~250–290 net additional LOC; the project trades 2 axioms for
~300 LOC of strong-Markov infrastructure that is reusable elsewhere
(it would also dissolve later infrastructure axioms if any appear).

---

## Open Mathlib API gaps

The single non-trivial gap is the **strong Markov property for the
i.i.d.-step random walk on `F2` driven by
`step_measure = Measure.infinitePi (fun _ => Z_uniform)`**.

**Status.** Mathlib has:
* `MeasureTheory.Measure.infinitePi` (exists).
* `MeasureTheory.IsStoppingTime` (exists, in `Probability.Process.Stopping`).
* `MeasureTheory.Filtration.natural` (exists).
* But: no packaged strong-Markov-at-stopping-time lemma for *i.i.d.
  product processes* on a discrete state space.

**Recommended path.** Build inline as a sibling file
`EnsX2026/FreeGroup/StrongMarkov.lean` with one statement:

```
theorem step_measure_strongMarkov
    (τ : (ℕ → F2) → ℕ∞)
    (hτ : IsStoppingTime (Filtration.natural step_measure) τ)
    (B : Set (ℕ → F2)) (hB : MeasurableSet B)
    (hB_shift_inv : ∀ Y, B Y ↔ B (shift τ Y)) :
  step_measure ({Y | τ Y < ∞} ∩ B)
    = step_measure {Y | τ Y < ∞} * step_measure B
```

The proof is a partition over `{τ = n}`: each piece factorises by
the Tonelli-Fubini structure of `Measure.infinitePi` and the
i.i.d. assumption (each `Y_k` independent of `Y_0, …, Y_{k−1}`).
Concrete combinatorial proof, ~80–120 LOC.

**No new axioms required.** Strictly: this can be derived from
`Measure.infinitePi_apply` plus `Measure.infinitePi.measure_inter_pi`
and standard product-measure manipulations. The user has already
admitted (correctly) that the project does *not* yet have
filtration / stopping-time infrastructure for `step_measure`; the
honest fix is to build a small targeted helper file, not admit
strong-Markov as an axiom.

If this 80–120 LOC budget is judged too high for a single wave, the
implementer may prefer to **build a narrow specialisation** — strong
Markov *only at* the hitting time of a fixed vertex, factorising
*only* the cylinder event. That trims the helper to ~50 LOC at the
cost of generality. Either is acceptable.

---

## How to dispatch the eventual #3 + #4 wave

**Suggested implementer brief** (skeleton):

> **Wave goal.** Dissolve project axioms #3
> (`harmonic_measure_factor_at_meeting_vertex_x`) and #4
> (`harmonic_measure_factor_at_meeting_vertex_one`) by encoding the
> user's self-contained proof (see `prompt_A_reply_distilled.md` at
> project root) directly in Lean, replacing the axioms with theorems.
>
> **Reference proof.** Read `prompt_A_reply_distilled.md` in full —
> it contains the user's verbatim proof + a Lean-encoding map step
> by step.
>
> **Plan.**
> 1. Create sibling file `EnsX2026/FreeGroup/StrongMarkov.lean` with
>    `step_measure_strongMarkov` (Step 2 / Step 4 of the encoding
>    map). Budget ~80–120 LOC.
> 2. Inline in `ExitMeasure.lean` (just before the existing axioms #3
>    and #4):
>    * `hittingTime` definition + `hittingTime_isStoppingTime` lemma
>      (Step 1, ~30 LOC).
>    * `hittingProb_eq` lemma — Lemma 1, `f(k) = 3^{−k}` (Step 2,
>      ~60 LOC; uses `step_measure_strongMarkov` at `T_a` for
>      neighbours and induction on `k`).
>    * `cylinder_event_subset_hits_meeting_vertex` lemma (Step 3,
>      ~40 LOC).
>    * `harmonic_measure_strong_markov_at_hittingTime` lemma (Step 4,
>      ~40 LOC).
> 3. Replace the two `axiom` declarations at lines 1341 and 1355 with
>    `theorem` declarations whose bodies assemble Steps 1–4 (Step 5
>    ≈ ~30 LOC, Step 6 ≈ ~25 LOC).
> 4. The existing
>    `harmonic_measure_translation_on_deep_cylinder` (line 2066) is
>    *unchanged* — it reads the same two facts (now theorems instead
>    of axioms).
>
> **Forbidden.** Do **not** introduce new axioms. If a sub-lemma
> seems to require Mathlib infrastructure that doesn't exist, build a
> targeted helper inline — the user has explicitly flagged that
> admitting strong-Markov as an axiom is a non-starter (see
> `feedback_user_provided_proofs.md` and the Wave 29-retry
> retrospective).
>
> **Build-green discipline.** After Steps 1–2 land, run
> `lake build EnsX2026.FreeGroup.ExitMeasure` to check; no `sorry`
> intermediate states. If a step blocks, file a question to the user
> rather than admitting a sub-step as an axiom.
>
> **Expected axiom count after wave.** 5 → 3 (axioms #3 and #4
> dissolved; remaining: `iIndepFun_iIdentDistrib_uniformIndic_pastDep`,
> `X_infinity_measurable`, `harmonic_measure_one_cylinder_constant`).
