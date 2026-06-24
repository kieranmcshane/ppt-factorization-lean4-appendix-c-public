# User-provided self-contained proofs

This index records every elementary proof the user has supplied in
this project so future dispatches can encode them directly instead
of re-deriving from scratch. Maintained by the User-Proof Cataloguer
sub-agent.

## How to use this index

Before dispatching any axiom-dissolution wave:

1. Look up the axiom in the index table below.
2. If a user-provided proof exists, the implementer brief MUST encode
   that proof verbatim (or transcribed), not a re-derivation.
3. If the user's proof uses tools the project hasn't formalised
   (e.g., strong Markov), the brief encodes each tool as a Lean
   sub-lemma derived from project primitives, not a new axiom.
4. If you cannot find a user-provided proof for a given axiom and
   the axiom looks dissolvable, ASK the user before dispatching:
   "did you give me a solution for this one? I want to avoid re-deriving."

The matching memory file
`/Users/kieranmcshane/.claude/projects/-Users-kieranmcshane-Documents-Claude-Projects-Article-PPT-ppt-factorization-lean4/memory/feedback_user_provided_proofs.md`
restates this discipline and should be checked first.

## Index (axiom → proof location)

| Axiom (current or historical) | Status | User-proof location | One-line summary |
|---|---|---|---|
| `iIndepFun_iIdentDistrib_uniformIndic_pastDep` | dissolved (Wave 33) | `williams_97_note.tex` (full doc) + JSONL 2026-04-25T11:35Z (counting argument) | 10-line direct counting on `S^M`: at each step the # admissible values is `c`, `n−c`, or `n` independently of the prefix; product gives the i.i.d. Bernoulli law |
| `harmonic_measure_translation_on_deep_cylinder` | dissolved (Wave 29-retry) into the two `..._factor_at_meeting_vertex_*` axioms | JSONL 2026-04-25T12:10:23Z (reply to Prompt A) + `archive/blueprints/wave_problem_asker_A.md` + `archive/blueprints/wave29_blueprint.md` | Hitting probability `f(k) = 3^{-k}` for SRW on the 4-regular tree, then strong Markov at the meeting vertex `u = φ.valPrefix c`; ratio yields `μ_x(I(φ,q))/μ_o(I(φ,q)) = 3^{-b_φ(x)}` |
| `harmonic_measure_factor_at_meeting_vertex_x` | **dissolved (Wave 35.5 D2)** | `archive/blueprints/prompt_C_reply.md` (paste from external LLM via `archive/blueprints/wave_problem_asker_C.md`) | Direct product-measure decomposition: partition over `{T_u^x = n}`, use `μ_∞ = ν^{⊗n} ⊗ μ_∞` (Tool 1) + Tonelli (Tool 2) to get keystone `μ_x(I(φ,q)) = μ_∞{T_u^x<∞}·μ_u(I(φ,q))`; evaluate hitting probability via linear recurrence + transience as `3^{-(|x|-c)}`. NO strong-Markov by name; NO stopping-time API. |
| `harmonic_measure_factor_at_meeting_vertex_one` | **dissolved (Wave 35.5 D3)** | `archive/blueprints/prompt_C_reply.md` (same proof, specialised to `x = o`) | Same proof, with `x := o`, gives `μ_o(I(φ,q)) = 3^{-c}·μ_u(I(φ,q))` |
| `harmonic_measure_one_cylinder_constant` | **dissolved (Wave 34-final v2)** | reconstructed sister-subtraction argument (depth-1 + Busemann at sister vertices); see Wave 34-final v2 commits `40217b9`, `1777ce2`, `43a3f70`, `2a6f53b` | Sister equality at depth `p+1` via Busemann subtraction: `8·3^{p-1}(y_i − y_j) = 0` from the difference of the two equations `1 = μ_{ψ_i}(univ)` and `1 = μ_{ψ_j}(univ)`, where the "outside" contribution cancels because it depends only on the parent cylinder |
| `dirichlet_solution_continuousAt_boundary_axiom` | dissolved (Wave 30) | JSONL 2026-04-25T12:23:14Z (reply to Prompt B) + `archive/blueprints/wave_problem_asker_B.md` | ε/δ argument: choose `q` so `e^{-q} < δ'(ε/2)` from uniform continuity of `g`; choose `p ≥ q` so `2MC·3^{-(p+1−q)} < ε/2`; set `δ = e^{-p}`; split integral over `I(φ,p)` and complement, bound via (F1) and uniform continuity |
| `X_infinity_measurable` | dissolved (Wave 32) | n/a — no user proof needed (Mathlib measurability bookkeeping) | not in scope of this index |
| **Q40a (greedy directional argument)** | exam result, not a project axiom — used to sidestep the heavy `tree_bounded_harmonic_vanishes` route | JSONL 2026-04-24T21:11:58Z | Define `D(v) = h(v) − h(p(v))`; if `h(u_0) > 0`, telescope along geodesic from root, find last vertex with `D > 0`, build infinite ray of strict increase, contradict `lim h(ψ_→p) = 0` along that ray |
| **Q43 cancellation coupling** | exam result; underlies the Wave 23C application of Williams §9.7 (i.i.d. Bernoulli(1/4)) | JSONL 2026-04-24T23:15:47Z + `williams_97_note.tex` §5.2 | Define `J_k = 1{Y_k = s_{k-1}^{-1}}` with arbitrary default at the origin; `J_k` i.i.d. Bernoulli(1/4) since `Y_k` independent of past and uniform; differs from `I_k` only on the finite set of returns to identity (since `L_n → ∞` a.s.); apply classical SLLN |

## Detailed proof entries

---

### `iIndepFun_iIdentDistrib_uniformIndic_pastDep`

**Statement.** Let `(Y_k)_{k≥0}` be i.i.d. uniform on a finite set `S` with
`|S| = n`. Let `A_k : Ω → 2^S` be `σ(Y_0,…,Y_{k−1})`-measurable with constant
cardinality `|A_k(ω)| = c` for every `ω`. Then `f_k := 1{Y_k ∈ A_k}` is
i.i.d. Bernoulli(c/n).

**Status.** Dissolved in Wave 33 / 33-cleanup; now a theorem in
`EnsX2026/FreeGroup/RandomWalk.lean` line 2078.

**User-provided proof location.** `williams_97_note.tex` (full
companion document, 399 lines, project root). The note was authored
after the user's external-LLM reply (transcribed in conversation;
shorter version at JSONL 2026-04-25T11:35:28Z covers the equivalent
"realising-prefixes" counting argument with sets `G_R^{(n)}` and
`|G_R^{(n)}| = 3^{|R|}`).

**Proof transcribed (direct counting form, from `williams_97_note.tex` §2).**
For any finite `I = {i_1 < ⋯ < i_r}` and `ε : I → {0,1}`, the event
`⋂_{i∈I} {f_i = ε_i}` depends only on the first `M := max(I)+1`
coordinates. Count realising tuples in `S^M`: at each step
`ℓ ∈ {0,…,M−1}`,

* if `ℓ ∉ I`: every value is admissible, so `c_ℓ = n`;
* if `ℓ ∈ I` with `ε_ℓ = 1`: `y_ℓ ∈ A_ℓ(prefix)` has `c` admissible values;
* if `ℓ ∈ I` with `ε_ℓ = 0`: complement has `n − c` admissible values.

Crucially `c_ℓ` does *not* depend on the prefix (only on whether `ℓ ∈ I`
and on `ε_ℓ`), because `|A_ℓ| = c` is constant. Total count
`N = ∏_ℓ c_ℓ`; probability is `N / n^M = ∏_{i∈I} p_{ε_i}` with
`p_1 = c/n`, `p_0 = 1 − c/n`. This establishes mutual independence and
identical Bernoulli(c/n) distribution.

**Encoding obligations for Lean.**

* Project the infinite-product measure `step_measure = Measure.infinitePi
  Z_uniform` to a finite-prefix measure `Measure.pi (Z_uniform^{[0,M)})`.
* Mathlib gap (the Lean obstacle): no finite-prefix split for
  `Measure.infinitePi` over `ℕ`. The pure-counting argument is
  ~10 lines; the Lean dissolution required ~200 LOC of measure-
  theoretic plumbing on top.
* Once the prefix-suffix split is in place, the proof transcribes
  directly: count `N = ∏ c_ℓ`, divide by `n^M`.

**History.** Wave 33 used `williams_97_note.tex` verbatim. The two
project applications (Q42 binomial law and Q43 cancellation
coupling) are documented in §5 of the note.

---

### `harmonic_measure_translation_on_deep_cylinder` (historical) → `harmonic_measure_factor_at_meeting_vertex_{x,one}` (current)

**Statement (deep-cylinder identity, Wave 29 form).** For every
`x ∈ F_2`, every `φ ∈ ∂F_2`, every `q ≥ |x|`:
`μ_x(I(φ,q)) = p_φ(x) · μ_o(I(φ,q))` where `p_φ(x) = 3^{-b_φ(x)}` and
`b_φ(x) = |x| − 2c(x,φ)`.

**Status.** The deep-cylinder identity is a theorem
(`harmonic_measure_translation_on_deep_cylinder`, ExitMeasure.lean:1386),
derived from two axioms: `harmonic_measure_factor_at_meeting_vertex_x`
(line 1341) and `harmonic_measure_factor_at_meeting_vertex_one`
(line 1355). Both axioms are still in flight for Wave 34.

**User-provided proof location.**
* Prompt: `archive/blueprints/wave_problem_asker_A.md` (83 lines, archived post-W35.5).
* Reply: JSONL transcript message at `2026-04-25T12:10:23.466Z`,
  from session `670854ae-84c8-4de8-9f8d-e3c6fc601ce8`, opens with
  "here is an answer to Prompt A."
* Project blueprint capturing the reply: `archive/blueprints/wave29_blueprint.md`
  (84 lines, archived post-W35.5; "External LLM proof (paste-verbatim
  from user submission)").

**Proof transcribed (verbatim from JSONL reply).**

**Lemma 1 (hitting probability `f(k) = 3^{-k}`).** Let `T` be the
infinite 4-regular tree, `f(k) := ℙ_a(T_b < ∞)` with `d(a,b) = k`
(well-defined by vertex transitivity).

* `f(0) = 1` trivially.
* `f(1)`: from `a`, walk steps to `b` w.p. 1/4; w.p. 3/4 it steps to
  one of three other neighbours `z`. Unique path `z → b` passes
  through `a`, so `T_b < ∞ ⇒ T_a < T_b`. Strong Markov at `T_a`:
  `ℙ_z(T_b < ∞) = ℙ_z(T_a < ∞) · ℙ_a(T_b < ∞) = f(1)^2`. Hence
  `f(1) = 1/4 + (3/4) f(1)^2`. Quadratic `3 f^2 − 4 f + 1 = 0`,
  roots `1` and `1/3`. Transience of SRW on the 4-regular tree
  selects `f(1) = 1/3`.
* Inductive step: assume `f(k−1) = 3^{-(k−1)}`. Let `a, b` with
  `d(a,b) = k`, `a_1` the neighbour of `a` on the `a → b` geodesic.
  From `a`: step to `a_1` w.p. 1/4, distance becomes `k−1`. Step to
  another neighbour `z` w.p. 3/4, then `d(z,b) = k+1`, unique path
  `z → b` passes through `a`, so `ℙ_z(T_b < ∞) = (1/3) · f(k)`.
  Markov: `f(k) = (1/4) f(k−1) + (3/4)(1/3) f(k) = (1/4) 3^{-(k−1)}
  + (1/4) f(k)`. Solve: `f(k) = (1/3) · 3^{-(k−1)} = 3^{-k}`. ∎

**Step 2 (geometric decomposition + strong Markov at the meeting
vertex).** Fix `φ ∈ ∂T`, `q ≥ 0`. `I(φ,q)` is the set of ends
agreeing with `φ` on the first `q` letters; equivalently, ends
whose ray passes through `v_q := φ_→q`.

Fix `x ∈ T`, `c := c(x,φ)`, `u := φ_→c` (meeting vertex of `o → x`
geodesic and the φ-ray). Then `d(x,u) = |x| − c`, `d(o,u) = c`.
Hypothesis `q ≥ |x|` gives `q ≥ c`, so `u` lies between `o` and
`v_q` on `φ`. Any end in `I(φ,q)` contains `u`, so the walk must
visit `u` (because the walk converges to its end). Hence
`{X_∞ ∈ I(φ,q)} ⊆ {T_u < ∞}`.

Strong Markov at the stopping time `T_u`: on `{T_u < ∞}`, the
post-`T_u` process is a fresh SRW from `u`, independent of the past;
the cylinder event `{X_∞ ∈ I(φ,q)}` is tail. Therefore
```
μ_x(I(φ,q)) = ℙ_x(T_u < ∞) · μ_u(I(φ,q))    ...(1)
μ_o(I(φ,q)) = ℙ_o(T_u < ∞) · μ_u(I(φ,q))    ...(2)
```

**Step 3 (algebra).** From Lemma 1: `ℙ_x(T_u < ∞) = f(|x|−c) =
3^{-(|x|−c)}` and `ℙ_o(T_u < ∞) = f(c) = 3^{-c}`. Insert in (1),(2)
and divide:
```
μ_x(I(φ,q)) = 3^{-(|x|−c)} / 3^{-c} · μ_o(I(φ,q))
            = 3^{-(|x|−2c)} · μ_o(I(φ,q))
            = 3^{-b_φ(x)} · μ_o(I(φ,q)) = p_φ(x) · μ_o(I(φ,q)).
```
∎

**Encoding obligations for Lean.**

* Lemma 1 needs: (a) SRW transience on the 4-regular tree (already
  available, project name `walk_transience` / Q44), (b) strong Markov
  property at the first hitting time of an arbitrary vertex (NOT a new
  axiom — must be derived from `step_measure + X_walk` filtration
  infrastructure; project does not yet have this).
* Step 2 needs: `walkFil` filtration on `step_measure` (Wave 22F.2.1
  hand-rolled this, code is dead but resurrectable per
  `archive/blueprints/wave29_blueprint.md`); first-hitting-time stopping-time property;
  strong Markov at a stopping time.
* The Lean encoding therefore decomposes into the two factor axioms:
  `..._factor_at_meeting_vertex_x` (line 1341) and `..._factor_at_meeting_vertex_one`
  (line 1355). The deep-cylinder theorem (lines 1386–1434) is then
  pure algebra.

**History.**
* Wave 29-retry consumed the user's proof to carve the original
  single axiom into the two factor axioms; the algebra step
  `harmonic_measure_translation_on_deep_cylinder` is fully proved.
* Wave 34 attempt to dissolve the two factor axioms via an
  automorphism-transfer plan **missed** this user proof and burned
  ~150–250 LOC of dispatch effort on a re-derivation. The user's
  flag at JSONL 2026-04-25T13:31:09Z and 14:38:24Z explicitly called
  this out: "I gave you self contained elementary proofs … but i
  provided you elementary proofs of these #3 and #4". This is the
  triggering event for the User-Proof Cataloguer role.

---

### `dirichlet_solution_continuousAt_boundary_axiom`

**Statement.** Let `T̄ = T ⊔ ∂T` be the end-compactification of the
4-regular tree with the standard ultrametric `d(y,z) = e^{-p(y,z)}`.
Given continuous `g : ∂T → ℝ`, define
`h : T̄ → ℝ` by `h(y) = g(y)` for `y ∈ ∂T` and `h(y) =
∫_{∂T} g(ψ) p_ψ(y) dμ_o(ψ)` for `y ∈ T`. Then `h` is continuous at
every `φ ∈ ∂T`.

**Status.** Dissolved in Wave 30; now a theorem
`dirichlet_solution_continuousAt_boundary_axiom` (theorem, kept the
old name) at ExitMeasure.lean:3567.

**User-provided proof location.**
* Prompt: `archive/blueprints/wave_problem_asker_B.md` (109 lines, archived post-W35.5).
* Reply: JSONL transcript message at `2026-04-25T12:23:14.240Z`,
  opens with "Here is the answer for prompt B".

**Proof transcribed.**

Fix `ε > 0`. Let `M = sup_{∂T} |g|`. By uniform continuity of `g` on
the compact `∂T`, choose `δ' > 0` such that
`d(ψ_1,ψ_2) < δ'  ⇒  |g(ψ_1) − g(ψ_2)| < ε/2`.

Choose `q ≥ 1` with `e^{-q} < δ'`; then any two ends with
`p(ψ_1,ψ_2) ≥ q` have `|g(ψ_1) − g(ψ_2)| < ε/2`. In particular for
`ψ ∈ I(φ,q)`:
```
|g(ψ) − g(φ)| < ε/2.    (*)
```

By (F1) (cylinder concentration), if `y ∈ T` with `d(y,φ) < e^{-p}`
for some integer `p ≥ q`, then `p(y,φ) ≥ p+1`, so `|y| ≥ p+1 ≥ q+1`
and `y` shares the first `q` letters with `φ`; therefore
```
μ_y(∂T \ I(φ,q)) ≤ C · 3^{-(|y|−q)} ≤ C · 3^{-(p+1−q)}.
```

Choose integer `p ≥ q` with `2 M C · 3^{-(p+1−q)} < ε/2`. Set
`δ := e^{-p} > 0`.

For `y ∈ T̄` with `d(y,φ) < δ`:

* **Case `y ∈ ∂T`:** then `h(y) = g(y)`, `h(φ) = g(φ)`,
  `p(y,φ) ≥ p+1 ≥ q+1`, so `y ∈ I(φ,q)` and (*) gives
  `|h(y) − h(φ)| < ε/2 < ε`.
* **Case `y ∈ T`:** by (F2) Poisson representation,
  `h(y) = ∫_{∂T} g(ψ) dμ_y(ψ)` and
  `h(φ) = g(φ) = ∫_{∂T} g(φ) dμ_y(ψ)` (since `μ_y` is a probability
  measure). Therefore
  ```
  |h(y) − h(φ)| ≤ ∫_{I(φ,q)} |g(ψ) − g(φ)| dμ_y
                 + ∫_{∂T \ I(φ,q)} |g(ψ) − g(φ)| dμ_y
              ≤ (ε/2) · 1 + 2M · μ_y(∂T \ I(φ,q))
              ≤ ε/2 + 2 M C · 3^{-(p+1−q)} < ε/2 + ε/2 = ε. ∎
  ```

**Encoding obligations for Lean.**

* Uniform continuity of `g` on compact `∂T`: standard Mathlib.
* Cylinder concentration (F1) is a project lemma that must be
  available; in Lean it appears in `harmonic_measure_cylinder`-shaped
  identities (used the actual cylinder formula `μ_y(I(φ,p)) ≥ 1 − C
  3^{-(|y|−p)}`).
* Splitting integrals on the cylinder vs. complement: standard.
* The Lean dissolution is now visible at ExitMeasure.lean:3567 ff.

**History.** Wave 30 used the user's reply directly. This is one of
the success stories where the user's proof was found and used.

---

### Q40a — greedy directional argument (exam result, not an axiom)

**Statement (mg26 Q40a).** Let `q ∈ ℕ`, `h` harmonic on `F_2` with
`h(φ_→q) = 0` and `lim_p h(ψ_→p) = 0` for every `ψ ∈ ∂F_2` with
`ψ_→(q+1) ≠ φ_→(q+1)`. Then `h ≡ 0` on `T_q := {x ∈ F_2 : m(x,φ) ≤ q}`.

**Status.** Exam result, used to sidestep the heavy
`tree_bounded_harmonic_vanishes` route in Q40b. Catalogued here
because it's a self-contained user-provided graduate-level argument
the project may want to reuse later.

**User-provided proof location.** JSONL transcript at
`2026-04-24T21:11:58.397Z` ("Corrected proof of Q40a").

**Proof transcribed.** Root `T_q` at `r := φ_→q`. (H1) gives
`h(r) = 0`. The induced subgraph on `T_q` is a tree where `r` has
exactly 3 children `z_1,z_2,z_3` and every other vertex `v ≠ r` has
exactly one parent `p(v)` and three children. Full harmonicity at
`v ≠ r`:
```
4 h(v) = h(p(v)) + Σ_{c child of v} h(c).
```
Define directional difference `D(v) := h(v) − h(p(v)) ∈ ℝ`.
Rearranging:
```
Σ_{c child of v} h(c) = 3 h(v) + D(v),
```
so the average of `h` over the three children of `v` is
`h(v) + D(v)/3`.

Assume for contradiction `h ≢ 0` on `T_q`; WLOG `h(u_0) > 0` for some
`u_0 ∈ T_q`. (`u_0 ≠ r` since `h(r) = 0`.) Let `r = w_0,…,w_m = u_0`
be the geodesic. Telescoping:
```
h(u_0) = Σ_{j=1}^m D(w_j),
```
so `D(w_j) > 0` for some `j`. Let `v := w_l` be the LAST such vertex
(largest `l` with `D(w_l) > 0`). Then `Σ_{j=l+1}^m D(w_j) ≤ 0`, so
`h(u_0) − h(v) ≤ 0`, i.e. `h(v) ≥ h(u_0) > 0`. Also `D(v) > 0`.

Build an infinite ray `(v_k)_{k≥0}` with `v_0 := v` and inductively:
since `D(v_k) > 0`, the average over children of `v_k` is `h(v_k) +
D(v_k)/3 > h(v_k)`, so at least one child `c` has `h(c) > h(v_k)`;
set `v_{k+1} := c`. Then `D(v_{k+1}) > 0`, and `h(v_k)` is strictly
increasing in `k`. The ray stays in `T_q` (never returns toward `r`),
so it corresponds to some `ψ ∈ ∂F_2` with `ψ_→(q+1) ≠ φ_→(q+1)`,
along which `lim h(ψ_→p) = 0` by (H2). But `h(v_k) > h(v) > 0` for
all `k ≥ 1`, contradicting `lim h(v_k) = 0`. Hence no such `u_0`
exists; symmetric argument on `−h` rules out `h < 0`. So `h ≡ 0` on
`T_q`. ∎

**Encoding obligations for Lean.**

* Tree structure of `T_q` (root with 3 children, every other vertex
  with parent + 3 children): standard combinatorics on the
  Cayley graph of `F_2`.
* Telescoping identity over a finite geodesic: routine.
* Choice of the "last positive `D`" index: Finset.max of a finite set.
* Building the infinite ray: well-founded `Nat`-recursion choosing
  one child of `v_k` with `h(c) > h(v_k)`; non-emptiness from the
  averaging inequality.
* Identification of the ray with an end `ψ ∈ ∂F_2` with the required
  prefix property: standard.

**History.** Used as the de-facto exam answer in Q40-related
discussions. The Wave 22F-era plan to dissolve `tree_bounded_harmonic_vanishes`
via uniform shell-decay was eventually abandoned in favour of the
direct-uniqueness route through the martingale + bounded convergence
plan, but the greedy directional argument remains the cleanest
graduate-level proof should the project choose to encode it.

---

### Q43 cancellation coupling (exam result, not an axiom)

**Statement (mg26 Q43).** Let `(X_n)` be the SRW on `F_2`,
`L_n = |X_n|`. Then `L_n / n → 1/2` a.s.

**Status.** Exam result. Wave 23C / Wave 33 implemented the cancellation
indicator `coupledIndicator` and applied
`iIndepFun_iIdentDistrib_uniformIndic_pastDep` at `c = 1`, so this
proof underlies the project's Q43 closure.

**User-provided proof location.** JSONL transcript at
`2026-04-24T23:15:47.533Z` and again at `2026-04-25T05:23:15.471Z`
(both labelled "answer to problem for Q43" / "Problem for Q43 answer
…", with identical content). Captured also in `williams_97_note.tex`
§5.2.

**Proof transcribed.** Write `L_n = n − 2 C_n` where `C_n = Σ_{k=1}^n I_k`
and the cancellation indicator at step `k` is
```
I_k = 0 if L_{k-1} = 0,    1{Y_k = s_{k-1}^{-1}} if L_{k-1} ≥ 1,
```
with `s_{k-1}` the last letter of the reduced word `X_{k-1}`.

From Q42 we have `b_n / n → 1/2` a.s. (`b_n := b_{φ_0}(X_n)`). The
deterministic identity `L_n = b_n + 2 m(X_n, φ_0) ≥ b_n` yields
`liminf L_n / n ≥ 1/2` a.s. In particular `L_n → ∞` a.s., so the walk
visits identity only finitely often a.s.

**Construct the auxiliary i.i.d. sequence.** For `k ≥ 1`, set
`s_{k-1} := a` (arbitrary default) when `L_{k-1} = 0`, the true last
letter otherwise. Define
```
J_k := 1{Y_k = s_{k-1}^{-1}}.
```
Since `Y_k` is independent of `F_{k-1}` and uniform on the four
generators, `ℙ(J_k = 1 | F_{k-1}) = 1/4` regardless of `s_{k-1}`.
Therefore `(J_k)_{k≥1}` is i.i.d. Bernoulli(1/4). (This is the
specific application of `iIndepFun_iIdentDistrib_uniformIndic_pastDep`
at `c = 1`, `n = 4`.)

**Compare `I_k` and `J_k`.** They agree when `L_{k-1} ≥ 1`. Since
`L_n → ∞` a.s., `I_k = J_k` for all but finitely many `k` a.s. So
`Σ(I_k − J_k)` is a.s. bounded; dividing by `n`,
`(1/n) Σ I_k = (1/n) Σ J_k + o(1)` a.s. By the classical SLLN,
`(1/n) Σ J_k → 1/4` a.s., hence `C_n / n → 1/4` a.s. and
`L_n / n = 1 − 2 C_n / n → 1/2` a.s. Finally,
`m(X_n, φ_0)/n = (L_n − b_n)/(2n) → 0` a.s. ∎

**Encoding obligations for Lean.**

* Q42 SLLN `b_n / n → 1/2` (project-side; via Hoeffding + Borel–Cantelli).
* Definition of `coupledIndicator` aligned with `J_k` (project-side).
* `iIndepFun_iIdentDistrib_uniformIndic_pastDep` at `c = 1, n = 4`
  (now a theorem, RandomWalk.lean:2078).
* SLLN for i.i.d. sequence of bounded random variables (Mathlib).
* "Differs only on finite a.s. set" → ratios converge: routine.

**History.** Wave 23C consolidated this with Q42 under the single
generic axiom (now theorem). Wave 33 dissolved the axiom; the
coupling argument here is the operative `c = 1` instance.

---

### Q42 binomial law (exam result, not an axiom)

**Statement.** `(b_φ(X_n) + n)/2 ∼ Binomial(n, 3/4)`.

**Status.** Exam result; used in Q42 closure (Wave 23C / `busemann_walk_sum_binomial_pmf`).

**User-provided proof location.** Implicit in `williams_97_note.tex` §5.1,
combined with the realising-prefixes counting at JSONL
`2026-04-25T11:35:28.950Z` ("here is the answer. quite easily found").

**Proof transcribed.** Write the LHS as `Σ_{i<n} ξ_i` with
`ξ_i := (b_φ(X_{i+1}) − b_φ(X_i) + 1)/2`. By the `1+3` neighbour
structure of the Busemann function (project axiom
`busemann_other_neighbours`), exactly 1 of the 4 generators decreases
`b_φ` by 1 and 3 increase it by 1. So `ξ_i = 1{Y_i ∈ A_i}` with
`A_i(ω) := {s ∈ S : b_φ(X_i(ω) · s) = b_φ(X_i(ω)) + 1}` of constant
cardinality `|A_i| = 3`. Apply
`iIndepFun_iIdentDistrib_uniformIndic_pastDep` at `c = 3, n = 4`:
`(ξ_i)` is i.i.d. Bernoulli(3/4), so `Σ ξ_i ∼ Binomial(n, 3/4)`. ∎

**Encoding obligations for Lean.**

* Same as for `iIndepFun_iIdentDistrib_uniformIndic_pastDep` at `c = 3`.
* Plus the Mathlib bridge "sum of i.i.d. Bernoullis is Binomial" —
  the project built `busemann_walk_sum_binomial_pmf` (Pure Lean) as
  this bridge.

**History.** Same as Q43 (Wave 23C / Wave 33).

---

### `harmonic_measure_one_cylinder_constant` — DISSOLVED (Wave 34-final v2)

**Statement.** For every `φ, ψ ∈ ∂F_2` and every `p ∈ ℕ`:
`μ_1(I(φ,p)) = μ_1(I(ψ,p))`. Equivalently, `μ_1` is invariant under
the natural rotational action of `F_2` on `∂F_2`.

**Status.** Dissolved in Wave 34-final v2; now a theorem in
`EnsX2026/FreeGroup/ExitMeasure.lean`. The four-step micro-wave
sequence is in commits `40217b9`, `1777ce2`, `43a3f70`, `2a6f53b`
(Lemma A, B, C, D + headline replacement of the axiom invocation).

**User-provided proof location.** Reconstructed from project context
(no clean transcript copy was located by an earlier cataloguing
pass; the user had flagged JSONL `2026-04-25T14:38:24Z` "but i
provided you elementary proofs of these #3 and #4" suggesting the
proof was supplied earlier). The Wave 34-final v2 implementation
encoded the sister-subtraction argument that the project docstring
had hinted at as one of two viable routes.

**Proof transcribed (Wave 34-final v2 form).**

The depth-1 specialisation is the deep-cylinder identity at `q = 1`:
all four depth-1 cylinders have equal `μ_1`-mass `1/4` because
`μ_1(I(φ,1)) = 3^{-c}·μ_u(I(φ,1))` with `c = 0, |u| = 0`, and the
four cylinders partition `∂F_2`.

The depth-`p+1` inductive step (Lemma D / sister equality):
fix a parent cylinder `I(ψ,p)` and consider the three sister
extensions `ψ_i, ψ_j` differing only in their `(p+1)`-th letter.
Write each end's mass as `μ_{ψ_i}(univ) = 1` and apply the
deep-cylinder factorisation through the two parent meeting vertices.
The "outside" contribution (the part of `∂F_2 \ I(ψ_i, p+1)` shared
with the parent cylinder) depends only on the parent cylinder, so it
cancels in the difference `μ_1(I(ψ_i, p+1)) − μ_1(I(ψ_j, p+1))`.
The Busemann factor at the sister vertices then yields
`8·3^{p-1}(y_i − y_j) = 0`, forcing `y_i = y_j`.

**Encoding obligations for Lean (carried out in Wave 34-final v2).**

* **Lemma A** (commit `40217b9`): kernel equality outside the
  cylinder `φ p` — equality of the harmonic-measure kernel on the
  complement of a fixed cylinder, derived from the two factor axioms
  via the deep-cylinder identity at all but the cylinder's own depth.
* **Lemma B** (same commit): symmetric form for the sister
  cylinder — the kernel equality on the complement of the sister
  cylinder.
* **Lemma C** (commit `1777ce2`): sister harmonic-measure equality
  on outside cylinders — combines A and B to subtract the common
  "outside" contribution.
* **Lemma D** (commit `43a3f70`): the headline sister equality
  `harmonic_measure_sister_cylinder_eq` together with the depth-`p+1`
  Busemann-at-sister-vertices subtraction.
* **Step 4** (commit `2a6f53b`): replace the axiom invocation in
  `harmonic_measure_cylinder` with the new theorem; remove the
  axiom declaration.

**History.**
* Pre-Wave-34-final: the axiom was used in the inductive step of
  `harmonic_measure_cylinder`, asserting equality among the three
  sister cylinders inside a depth-`p` cylinder. The depth-1
  specialisation `harmonic_measure_one_cylinder_constant_depth1` had
  already been a theorem.
* Wave 34 step 2 (commit `2cf3ec9`) made depth-1 a theorem.
* Wave 34 step 3 (commit `cd7af8e`) documented this as a partial
  dissolution (depth-1 only) and labelled the wave "partial".
* Wave 34-final v2 (the four commits above) carried out the full
  inductive dissolution and removed the axiom.

---

## Notes on cataloguing methodology and gaps

**Method.** The cataloguer (this pass) used:

* `find` + `grep` over the project root for `.md`, `.tex`, `.lean`
  files referencing `wave_problem_asker_*`, `*_note.tex`, "self
  contained", "elementary proof".
* `jq` extraction of the conversation JSONL transcript at
  `/Users/kieranmcshane/.claude/projects/-Users-kieranmcshane-Documents-Claude-Projects-Article-PPT-ppt-factorization-lean4/670854ae-84c8-4de8-9f8d-e3c6fc601ce8.jsonl`,
  filtered on `type=="user"`, content type `array` (i.e., real
  user-typed messages, not task notifications), text length > 1000
  characters.
* For each candidate, transcription of the first 100 lines and
  identification of which axiom the proof targets via the
  problem-asker prompt or Lean docstring linkage.

**Statistics.**
* User messages with substantial (>1000 chars) array content:
  6, of which 4 are full proof submissions, 1 is a Mathlib doc paste,
  and 1 is a session-continuation summary.
* Long `string`-typed user messages: all are tool-system task
  notifications, not user authored.
* Project-root `.md` and `.tex` files with embedded user proofs:
  3 (`williams_97_note.tex`, `archive/blueprints/wave29_blueprint.md`,
  and the prompt files `archive/blueprints/wave_problem_asker_A.md`,
  `archive/blueprints/wave_problem_asker_B.md` are prompts not proofs).

**Verbatim transcripts.** All four user proofs above (Prompt A,
Prompt B, Q40a, Q43 cancellation coupling) have been preserved in
faithful prose form. The Williams §9.7 proof is captured both by
`williams_97_note.tex` (full document) and by the realising-prefixes
counting form at JSONL 2026-04-25T11:35Z.

**Known unfound proofs.**
* (none currently flagged) — `harmonic_measure_one_cylinder_constant`
  was previously flagged in this slot; Wave 34-final v2 reconstructed
  the sister-subtraction argument and dissolved the axiom (see the
  detailed entry above).

**In flight.**
* (none) — Wave 35.5 dissolved both
  `harmonic_measure_factor_at_meeting_vertex_x` and
  `harmonic_measure_factor_at_meeting_vertex_one`. The user-provided
  proof captured verbatim in `archive/blueprints/prompt_C_reply.md`
  (path-counting + stopped martingale) drove the encoding;
  project-declared axiom budget is **0**.

**Future cataloguer runs** should:
1. Re-scan for any new user proof submissions after the date stamp
   of the latest entry here.
2. Cross-check any new project axiom against this file before brief
   drafting.
3. Update the index table when a previously-flagged proof is
   located or when a new axiom is admitted.
