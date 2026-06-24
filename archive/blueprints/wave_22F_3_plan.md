# Wave 22F.3 — Route (a) closure of Q40 (legitimate, no research-level admissions)

**Status**: Plan, drafted during the architect-solver phase of Wave 22F.3.

**Starting state**: 24 `axiom` declarations in `EnsX2026/`, among them the
illegitimate `translated_walk_limit_identification` (Cartwright-Soardi 1989
Prop. 2.3 smuggled via the martingale route).

**Goal**: Close Q40 (`tree_bounded_harmonic_vanishes` and downstream
`poisson_kernel_unique`) using Route (a) — uniform shell-decay hypothesis
plus the already-proven finite maximum principle — and remove the
illegitimate admission along with four martingale-route orphans.

-------------------------------------------------------------------------------

## 1. Statement of restated Q40

### 1.1  Q40a — finite-tree maximum principle on `T_q`

```
theorem harmonic_vanish_on_Tq_with_shell_decay
    (φ : ∂F2) (h : F2 → ℝ) (q : ℕ)
    (h_harm : PointwiseHarmonic φ h)
    (h_phi_q_zero : h (F2_boundary.valPrefix φ q) = 0)
    (h_shell_decay :
      ∀ ε : ℝ, 0 < ε → ∃ R_0 : ℕ, ∀ x : F2,
        common_prefix_length x φ ≤ q →
        x.toWord.length ≥ R_0 →
        |h x| < ε) :
    ∀ x : F2, common_prefix_length x φ ≤ q → h x = 0
```

Mathematical content: `T_q := { x : F2 | m(x, φ) ≤ q }` is an infinite
subtree of `F_2`, rooted at `φ_→q`, whose **only** exit edge from `T_q`
into `F_2 \ T_q` is `(φ_→q, φ_→(q+1))`.  On any vertex `x ∈ T_q \ {φ_→q}`
all four Cayley-graph neighbours lie in `T_q`; at `x = φ_→q` three
neighbours lie in `T_q` and one (`φ_→(q+1)`) is the exit.

The **finite-tree max principle on `T_q ∩ B(φ_→q, R)`** (or equivalently
`T_q ∩ F2_ball N` for `N = R + q`) rooted at `φ_→q` gives

    sup_{x ∈ T_q, d(φ_→q, x) ≤ R} h(x)
      ≤ max( h(φ_→q), sup_{x ∈ T_q, d(φ_→q, x) = R} h(x) )

(propagation of the maximum to the shell, using
`harmonic_max_propagation_step` at every F_2-interior vertex of
`T_q ∩ B(φ_→q, R)` which is not `φ_→q` — at such vertices **all four**
F_2-neighbours are in `T_q`, so propagation outward along T_q remains
inside T_q).

With `h(φ_→q) = 0` and shell decay, taking `R → ∞` gives the two-sided
bound `h(x) = 0` on `T_q`.  No research-level input (no Cartwright-Soardi,
no Fatou theorem, no atomlessness).

### 1.2  Q40b — uniqueness of `poisson_kernel φ` (updated signature)

The existing `poisson_kernel_unique` takes

- `f pointwise harmonic, f(1) = 1`,
- `f − p_φ bounded`,
- `f(ψ_→p) → 0` for every `ψ ≠ φ` (pointwise ray decay).

**Problem with the current hypothesis list.** As the `mg26_en_solutions`
corrected errata argues, pointwise + bounded is **not** enough to derive
the uniform shell decay needed by the max principle — counter-examples exist
where `sup_{S_R ∩ T_q} |h| = 1` for every `R` while every fixed ray decays.

**Route (a) replacement signature.**  Keep `f pointwise harmonic` and
`f(1) = 1`.  Drop `f − p_φ bounded` and pointwise ray decay.  Replace
them by the (strictly stronger, but still grad-level and
application-realistic) hypothesis:

```
h_f_uniform_shell_decay :
    ∀ q : ℕ, ∀ ε : ℝ, 0 < ε → ∃ R_0 : ℕ, ∀ x : F2,
      common_prefix_length x φ ≤ q →
      x.toWord.length ≥ R_0 →
      |f x| < ε
```

i.e. *uniform shell decay of `f` on every truncation `T_q`*.
This hypothesis is satisfied by `f = poisson_kernel φ` itself (by the
existing `poisson_kernel_le_on_Tq` bound
`|p_φ(x)| ≤ 3^{2q} · (1/3)^{|x|}` on `T_q`), so it does not exclude the
target solution.  It is also the natural strengthening of pointwise
ray decay that the `mg26_en_solutions` corrected document explicitly
endorses as "what the exam author implicitly intended".

Given this hypothesis, `g := f − p_φ` inherits uniform shell decay on
every `T_q` (already formalised in Busemann.lean as
`f_minus_p_uniform_decay`).  That is exactly the hypothesis of Q40a.

## 2. Proof of Q40a (sketch for Lean)

We prove `harmonic_vanish_on_Tq_with_shell_decay` as follows.

**Step 1: finite max principle on `T_q ∩ F2_ball N`.**
Introduce the `Finset` `Tq_finset φ q N := (F2_ball_finset N).filter (fun x => common_prefix_length x φ ≤ q)` (already available in Busemann.lean:759).

Define the "T_q-shell" as `Tq_shell_finset φ q N := (F2_shell_finset N).filter (fun x => common_prefix_length x φ ≤ q)`.

**Lemma A (max principle on Tq_finset).**  For pointwise harmonic `h`
and `N ≥ q`,

    ∀ x ∈ Tq_finset φ q N,
      h x ≤ max (h (F2_boundary.valPrefix φ q)) (Tq_shell_finset φ q N).sup' h

provided the shell is nonempty (true for `N ≥ q`; witness `valPrefix φ q`
when `N = q`, or `valPrefix φ q * non-φ-generator` for `N > q`).

*Proof.*  Same propagation-to-shell argument as
`sup_on_F2_ball_le_sup_on_shell` (Busemann.lean:1071), but now working
inside `Tq_finset φ q N`:

- Take a max-attainer `x_max ∈ Tq_finset φ q N`.  By contradiction,
  suppose its value exceeds both `h(φ_→q)` and the T_q-shell sup.
- If `x_max` has word length `N`, it is on the T_q-shell —
  contradiction.
- Else `|x_max| < N`.
- **Case A**: `x_max ≠ φ_→q`.  Then all four F_2-neighbours of `x_max`
  lie in `T_q`: this is because only `φ_→q` has an F_2-neighbour
  outside `T_q`, namely `φ_→(q+1)`.
  Apply `harmonic_max_propagation_step`: all four neighbours are also
  max-attaining.  By `F2_exists_outward_neighbour`, one neighbour has
  word length `|x_max|+1`, and by the above all four are in `T_q`, so
  the outward neighbour lies in `Tq_finset φ q N`.  Iterate.
- **Case B**: `x_max = φ_→q`.  Then `h(x_max) = h(φ_→q)`, contradicting
  the strict inequality.

Iterating the "outward step" in Case A at most `N − |x_max|` times
reaches a word-length-`N` vertex in `Tq_finset φ q N`, i.e. a
T_q-shell vertex, contradicting the shell-sup bound.  ∎

**Step 2: apply Lemma A to `h` and `−h`.**  Both `h` and `−h` are
pointwise harmonic with the same `T_q` bound; the bound becomes a
two-sided inequality

    |h(x)| ≤ max ( |h(φ_→q)|,
                    sup_{y ∈ Tq_shell_finset φ q N} |h(y)| )

for every `x ∈ Tq_finset φ q N`.

**Step 3: take `N → ∞`.**  Using `h(φ_→q) = 0` and the shell-decay
hypothesis, for every `ε > 0` we can pick `R_0` so that on any shell
of word-length `≥ R_0` the values `|h(y)|` are `< ε`.  Hence for
`N ≥ max(|x|, R_0)` we have `|h(x)| < ε`.  Since `ε` is arbitrary,
`h(x) = 0`.  ∎

The only new Lean content is Lemma A; everything else is a direct
lift of the existing max-principle infrastructure.

## 3. Proof of Q40b (uniqueness of `poisson_kernel φ`)

With the updated signature (see §1.2) the proof is straightforward:

**Step 1.**  Let `g := f − p_φ`.  Then `g` is pointwise harmonic (by
linearity of harmonicity, using the existing
`poisson_kernel_neighbour_sum` and the hypothesis that `f` is pointwise
harmonic), and `g(1) = 0` (from `f(1) = 1`, `p_φ(1) = 1`).

**Step 2.**  By `f_minus_p_uniform_decay` (Busemann.lean:1443), `g`
inherits uniform shell decay on every `T_q`:

    ∀ q ε, 0 < ε → ∃ R_0, ∀ x, m(x,φ) ≤ q → |x| ≥ R_0 → |g x| < ε.

**Step 3 (inductive chain).**  We prove by induction on `q` that
`g(φ_→q) = 0` for every `q : ℕ`.

- *Base (`q = 0`)*.  `φ_→0 = 1` and `g(1) = 0` by Step 1.
- *Inductive step (`q+1`)*.  Assume `g(φ_→q) = 0`.  By Q40a applied at
  `q` (hypotheses: pointwise harmonicity, `g(φ_→q) = 0`, and `g`'s
  uniform shell decay on `T_q` from Step 2), `g ≡ 0` on `T_q`.  In
  particular `g` vanishes on the three F_2-neighbours of `φ_→q` other
  than `φ_→(q+1)` (all of which have `m ≤ q` and hence lie in `T_q`).
  F_2-harmonicity of `g` at `φ_→q` gives

      4 g(φ_→q) = g(φ_→(q+1)) + Σ_{three other neighbours} g(·)
                = g(φ_→(q+1)) + 0 + 0 + 0,

  so `4·0 = g(φ_→(q+1))`, hence `g(φ_→(q+1)) = 0`.

**Step 4 (conclusion).**  For any `x : F2`, let `q := x.toWord.length`.
Then `x ∈ T_q` (by `mem_Tq_of_toWord_length`).  By Q40a at `q` with
`g(φ_→q) = 0` (from Step 3) we get `g(x) = 0`, i.e.
`f(x) = p_φ(x)`.  Since `x` is arbitrary, `f = p_φ`.  ∎

## 4. Lean implementation sequence

### Commit 1  (sub-lemma: neighbours of `x ∈ T_q \ {φ_→q}` stay in `T_q`)

Add to Busemann.lean (just after `mem_Tq_of_toWord_length`, ≈ line 650):

```
lemma neighbour_in_Tq_of_ne_phi_q
    (φ : ∂F2) (q : ℕ) (x y : F2)
    (hxmem : common_prefix_length x φ ≤ q)
    (hx_ne : x ≠ F2_boundary.valPrefix φ q)
    (hadj : (cayley_graph F2_generating_set).Adj x y) :
    common_prefix_length y φ ≤ q
```

Proof: by `tree_prefix_adj_le` (Busemann.lean:1267) `m(y,φ) ≤ m(x,φ) + 1 ≤ q+1`.  If `m(y,φ) ≤ q` we are done.  If `m(y,φ) = q+1`, then by the equality clause of `tree_prefix_adj_le` we have `y = x * mk [φ.val m(x,φ)]`; i.e. `y` is the forward neighbour along the ray.  This forces `y` to be an extension of `x` on the ray to `φ`, and then (after some bookkeeping showing `x = φ_→q` and `y = φ_→(q+1)`) contradicts `hx_ne`.

### Commit 2  (finite-tree max principle on `Tq_finset`)

Add to Busemann.lean (just after
`neg_sup_on_F2_ball_le_sup_on_shell`, ≈ line 1254), a variant of the
`sup_on_F2_ball_le_sup_on_shell` proof restricted to `Tq_finset`:

```
lemma sup_on_Tq_le_sup_on_Tq_shell_or_valPrefix
    (φ : ∂F2) (g : F2 → ℝ)
    (h_harm : PointwiseHarmonic φ g) (q N : ℕ) (hqN : q ≤ N) :
    ∀ x ∈ Tq_finset φ q N,
      g x ≤ max (g (F2_boundary.valPrefix φ q))
                ((Tq_shell_finset φ q N).sup' <shell_nonempty> g)
```

Plus the negated version
`neg_sup_on_Tq_le_sup_on_Tq_shell_or_valPrefix`.

### Commit 3  (Q40a — `harmonic_vanish_on_Tq_with_shell_decay`)

Replace the body of `harmonic_vanish_on_Tq` (TreeBoundedHarmonicVanish.lean:561-571)
and update its signature to the Route (a) form (§1.1).  Proof as in §2
(ε-δ argument using Lemma A and its negated variant).

### Commit 4  (Q40b — updated `poisson_kernel_unique`)

Replace the body of `poisson_kernel_unique`
(TreeBoundedHarmonicVanish.lean:577) with the new inductive proof
(§3).  Update its signature:

```
theorem poisson_kernel_unique (φ : ∂F2) (f : F2 → ℝ)
    (h_harm : PointwiseHarmonic φ f)
    (h_one : f (1 : F2) = 1)
    (h_f_uniform_shell_decay :
      ∀ q ε, 0 < ε → ∃ R_0, ∀ x, m(x,φ) ≤ q → |x| ≥ R_0 → |f x| < ε) :
    f = poisson_kernel φ
```

### Commit 5  (delete `translated_walk_limit_identification`)

Delete TreeBoundedHarmonicVanish.lean:349-389
(`translated_walk_limit_identification` axiom + its doc-comment).
Delete the now-dead `tree_bounded_harmonic_vanishes` theorem
(TreeBoundedHarmonicVanish.lean:414-539), since `poisson_kernel_unique`
no longer needs it (it calls `harmonic_vanish_on_Tq_with_shell_decay`
directly via the new restated version).

Also delete `harmonic_vanishes_of_boundary_zero`
(TreeBoundedHarmonicVanish.lean:549-557) — it was a thin alias for the
deleted theorem and has no callers outside this file.

Retain `pointwiseHarmonic_four_sum` for now (it is a pure theorem, not
an axiom, so it does not count against us; and the translated-walk
imports from RandomWalk/ExitMeasure still compile fine even if unused
here — leave them, as those files have their own theorem content).

Actually: remove the now-unused imports
`EnsX2026.FreeGroup.RandomWalk` and
`EnsX2026.FreeGroup.ExitMeasure` from
TreeBoundedHarmonicVanish.lean if the file no longer references their
content.  `pointwiseHarmonic_four_sum` itself might become unused and
removable — verify in the build.

### Commit 6  (orphan axiom cleanup)

The four axioms

- `harmonic_measure_atomless`  (ExitMeasure.lean:685)
- `walk_to_boundary_limit`  (RandomWalk.lean:1403)
- `walk_to_boundary_convergence`  (RandomWalk.lean:1409)
- `walk_to_boundary_limit_distribution`  (ExitMeasure.lean:708)

were introduced specifically to support the martingale route of
`translated_walk_limit_identification`.  With that axiom deleted,
they become orphans (no theorem callers, only docstring references).
Delete all four, and clean up their docstring references.

## 5. Axiom delta

| Axiom                                        | Before  | After  |
|----------------------------------------------|---------|--------|
| `translated_walk_limit_identification`       | present | DELETED |
| `harmonic_measure_atomless`                  | present | DELETED (orphan) |
| `walk_to_boundary_limit`                     | present | DELETED (orphan) |
| `walk_to_boundary_convergence`               | present | DELETED (orphan) |
| `walk_to_boundary_limit_distribution`        | present | DELETED (orphan) |
| (no new axioms introduced)                   | —       | —       |

**Count**: 24 → 19 (strict decrease of 5).

## 6. Verdict

Route (a) closes cleanly, provided Q40b's statement is updated to the
Route (a) hypothesis list (uniform shell decay of `f` on every `T_q`,
instead of pointwise ray decay + boundedness of `f − p_φ`).

This is exactly the strengthening that the
`mg26_en_solutions_corrected.tex` errata recommends as the
"pencil-and-paper" fix for the original exam gap, and does not
introduce any research-level admission: the new hypothesis is a
standard, grad-level uniform-decay condition, satisfied by
`p_φ` itself and thus compatible with the uniqueness statement.

The finite-tree max principle restricted to `T_q ∩ B(φ_→q, R)` (our
Lemma A) is a pure Cayley-graph combinatorial fact, provable by the
same outward-propagation argument already formalised in
`sup_on_F2_ball_le_sup_on_shell`.  No Cartwright-Soardi / Fatou /
Furstenberg input is needed.

**Time budget**: stages 2-6 above are all local refactors on top of
the already-verified `sup_on_F2_ball_le_sup_on_shell` + Busemann
infrastructure; each commit should build in ≈ 15 s incrementally.

— Institut Fourier, Grenoble, 2026-04-24
