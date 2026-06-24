# Prompt C — User's external-LLM reply, verbatim

> **Source.** Reply from the user to `wave_problem_asker_C.md`,
> delivered in conversation. The point of Prompt C was to circumvent
> the missing `Mathlib.Probability.IID.StrongMarkov` lemma by getting
> a sur-mesure proof of the two factor axioms (#3 and #4) using ONLY
> Mathlib-boundary API: `Measure.infinitePi`-style factorisation +
> Tonelli + path counting + σ-additivity + ratio-of-measures
> conditional probability + elementary `3^k` identities + transience.
> The forbidden list explicitly banned strong Markov by name, stopping
> times as formal API objects, filtrations as objects, and abstract
> Markov-chain theory.
>
> The reply below succeeded: it never invokes "the strong Markov
> property", treats the hitting time as a plain integer-valued random
> variable, and decomposes "shift invariance" inline via Tool 1 (the
> i.i.d. product-measure factorisation `μ_∞ = ν^{⊗ n} ⊗ μ_∞`).
>
> This file is the input blueprint for **Wave 35 final** (the joint
> dissolution of `harmonic_measure_factor_at_meeting_vertex_x` and
> `harmonic_measure_factor_at_meeting_vertex_one`).

---

**Proof of the two cylinder identities**

Fix \(x \in T\), \(\varphi \in \partial T\), and integer \(q \geq |x|\). Let \(c = c(x,\varphi)\) and let \(u\) be the vertex at distance \(c\) from \(o\) along the \(\varphi\)-ray, so \(|u|=c\) and \(\operatorname{dist}(x,u)=d:=|x|-c\).

For any vertices \(v,w \in T\) and any sequence \(Y \in \Omega\), define the integer-valued function
\[
T_w^v(Y) := \inf\{n \in \mathbb{N}\cup\{0\} : W_n^v(Y)=w\}
\]
(with the convention \(\inf\emptyset=\infty\)).

### 1. First-passage path counting (Tool 3)

Let \(\Pi_{v,w}^{(n)}\subset S^n\) be the (finite) set of generator sequences \((s_0,\dots,s_{n-1})\) such that the walk starting at \(v\) ends at \(w\) exactly at step \(n\) and does not visit \(w\) at any earlier step. By Tool 3 the event \(\{T_w^v=n\}\) depends only on the first \(n\) coordinates. Under the identification \(\Omega\simeq S^n\times S^\mathbb{N}\) (Tool 1) we have the Cartesian product
\[
\{T_w^v=n\}=\Pi_{v,w}^{(n)}\times S^\mathbb{N}.
\]
Since the law of the first \(n\) coordinates is \(\nu^{\otimes n}\),
\[
\mu_\infty\{T_w^v=n\}=|\Pi_{v,w}^{(n)}|\cdot(1/4)^n.
\]

### 2. Necessary visitation of \(u\)

The cylinder \(I(\varphi,q)\) consists of all ends whose first \(q\) edge labels agree with those of \(\varphi\). Because \(q\geq|x|\geq c\), every \(\psi\in I(\varphi,q)\) has \(u\) as a prefix; the unique geodesic ray from \(o\) to \(\psi\) therefore passes through \(u\). Since \(T\) is a tree, any walk starting at \(x\) whose limit end lies in \(I(\varphi,q)\) must occupy every initial segment of that ray, hence must visit \(u\) at some finite time. Equivalently,
\[
\{X_\infty^x\in I(\varphi,q)\}\subseteq\{T_u^x<\infty\}.
\]
(The complementary event \(\{T_u^x=\infty\}\) keeps the walk forever inside the connected component of \(T\setminus\{u\}\) containing \(x\), whose boundary is disjoint from \(I(\varphi,q)\).)

### 3. Keystone decomposition via product-measure factorisation (Tools 1, 2, 4)

We have
\[
\mu_x(I(\varphi,q))=\mu_\infty(\{X_\infty^x\in I(\varphi,q)\}).
\]
By Tool 4 the sets \(\{T_u^x=n\}\) (\(n=0,1,2,\dots\)) and \(\{T_u^x=\infty\}\) form a measurable partition of \(\Omega\), so
\[
\mu_x(I(\varphi,q))=\sum_{n=0}^\infty\mu_\infty\bigl(\{X_\infty^x\in I(\varphi,q)\}\cap\{T_u^x=n\}\bigr)
\]
(the \(\{T_u^x=\infty\}\) term vanishes by Step 2). Fix \(n\geq0\). Apply Tool 1 to split \(\Omega\simeq S^n\times S^\mathbb{N}\). On \(\{T_u^x=n\}\) the prefix \((Y_0,\dots,Y_{n-1})\) lies in \(\Pi_{x,u}^{(n)}\) and \(W_n^x(Y)=u\); for all \(k\geq0\),
\[
W_{n+k}^x(Y)=u\cdot Y_n\cdots Y_{n+k-1}=W_k^u(Y^{(n)}),
\]
where \(Y^{(n)}=(Y_n,Y_{n+1},\dots)\) is the tail. Thus
\[
X_\infty^x(Y)=X_\infty^u(Y^{(n)}).
\]
The intersection event therefore factors as the Cartesian product
\[
\{X_\infty^x\in I(\varphi,q)\}\cap\{T_u^x=n\}=\Pi_{x,u}^{(n)}\times\{y\in S^\mathbb{N}:X_\infty^u(y)\in I(\varphi,q)\}.
\]
By Tool 2 (Fubini/Tonelli for the product measure \(\nu^{\otimes n}\otimes\mu_\infty\)) its measure is
\[
\mu_\infty\bigl(\{X_\infty^x\in I(\varphi,q)\}\cap\{T_u^x=n\}\bigr)=\nu^{\otimes n}(\Pi_{x,u}^{(n)})\cdot\mu_u(I(\varphi,q))=\mu_\infty\{T_u^x=n\}\cdot\mu_u(I(\varphi,q)).
\]
Substituting into the sum and factoring out the constant \(\mu_u(I(\varphi,q))\) yields the keystone identity
\[
\mu_x(I(\varphi,q))=\mu_\infty\{T_u^x<\infty\}\cdot\mu_u(I(\varphi,q)).
\]

### 4. Evaluation of the hitting probability (Tools 1, 3, 5, 6, 7)

Let \(d=|x|-c\geq0\). For any vertex \(y\) with \(\operatorname{dist}(y,u)=h\) define
\[
f(h):=\mu_\infty\{T_u^y<\infty\}.
\]
Tree homogeneity (Tool 3) implies \(f\) depends only on \(h\); clearly \(f(0)=1\) (Tool 5). For \(h\geq1\) apply Tool 1 with \(n=1\): split \(\Omega\simeq S\times S^\mathbb{N}\). The first increment \(Y_0\) is uniform on \(S\) (\(|S|=4\)). Exactly one choice moves to the unique neighbor of \(y\) at distance \(h-1\) from \(u\); the other three choices move to neighbors at distance \(h+1\) (Tool 3 and Tool 6). On each of these four events of probability \(1/4\) the tail is an independent copy of the original product measure (Tool 1), so the walk after the first step is a fresh SRW started from the new vertex. Hence
\[
f(h)=\frac14 f(h-1)+\frac34 f(h+1).
\]
Rearrangement gives the linear homogeneous recurrence
\[
3f(h+1)-4f(h)+f(h-1)=0\qquad(h\geq1).
\]
The characteristic equation (Tool 6) \(3\lambda^2-4\lambda+1=0\) factors as \((3\lambda-1)(\lambda-1)=0\) with roots \(\lambda=1\) and \(\lambda=1/3\). The general solution on \(\{h\geq0\}\) is
\[
f(h)=A+B\cdot3^{-h}.
\]
The condition \(f(0)=1\) forces \(A+B=1\). The constant solution \(A=1\), \(B=0\) (i.e. \(f(h)\equiv1\)) is excluded by Tool 7: the SRW is transient, so it visits any fixed vertex (in particular \(u\)) only finitely often a.s. If \(f(h)=1\) for all \(h\), then from any neighbor of \(u\) the walk would hit \(u\) a.s., then leave and hit \(u\) again a.s., and so on, producing infinitely many visits a.s., a contradiction. Thus \(A=0\), \(B=1\), and
\[
f(h)=3^{-h}.
\]
In particular, \(\mu_\infty\{T_u^x<\infty\}=3^{-d}=3^{-(|x|-c)}\).

### 5. Synthesis of the claims

**Claim 1.** Substitute the value computed in Step 4 into the keystone identity of Step 3:
\[
\mu_x(I(\varphi,q))=3^{-(|x|-c)}\cdot\mu_u(I(\varphi,q)).
\]
**Claim 2.** Repeat the entire argument with starting vertex \(x:=o\). The inclusion of Step 2 still holds (since \(q\geq c\)), the keystone factorisation is verbatim, and \(\operatorname{dist}(o,u)=c\), so
\[
\mu_o(I(\varphi,q))=\mu_\infty\{T_u^o<\infty\}\cdot\mu_u(I(\varphi,q))=3^{-c}\cdot\mu_u(I(\varphi,q)).
\]

All steps invoke the allowed tools explicitly where used. The cylinder sets \(I(\varphi,q)\) form a \(\pi\)-system generating the Borel \(\sigma\)-algebra (given), so the identities determine the exit measures completely.

---

## Lean encoding map (for Wave 35 final)

This proof transcribes to Lean 4 against Mathlib's existing `Measure.infinitePi` API, with NO new admissions and NO new abstract probability infrastructure. The 5 sections map to the following Lean obligations:

### Step 1 → Path-counting hitting-time pmf
**Lean obligation.** Define `T_u_at (v : F2) (Y : ℕ → F2) : ℕ∞` (first time the walk from `v` hits `u`). Prove
```
step_measure {Y | T_u_at v Y = n}
  = (admissibleFirstPassagePaths v u n).card · (1/4)^n
```
where `admissibleFirstPassagePaths v u n : Finset (Fin n → F2)` enumerates the length-`n` reduced-word paths from `v` to `u` not visiting `u` early.
**Existing infrastructure.** `Measure.infinitePi_pi` (already used in the project), `Measure.pi_singleton`. Estimated 60–80 LOC.

### Step 2 → Geometric inclusion
**Lean obligation.** `walkPrefixEvent x φ q ⊆ {Y | T_u_at x Y < ⊤}` where `u = φ.valPrefix(c(x, φ))`.
**Existing infrastructure.** `walk_boundary_limit_at` (Wave 35-prep). The proof uses the existing `walk_prefix_stable_at` / `walk_limit_letter_at` chain. Estimated 50–80 LOC.

### Step 3 → Keystone via product-measure factorisation (NO strong Markov)
**Lean obligation.** Prove
```
step_measure ({Y | X_infinity_starting_at x Y ∈ cylinder φ q} ∩ {T_u_at x Y = n})
  = step_measure {T_u_at x Y = n} · step_measure {Y | X_infinity_starting_at u Y ∈ cylinder φ q}
```
**Encoding.** This is the keystone. Use `Measure.infinitePi`'s split-off-first-`n` factorisation:
1. Identify `(ℕ → F2) ≃ (Fin n → F2) × (ℕ → F2)` via the shift `Y ↦ (Y∘Fin.castSucc, Y ∘ (· + n))`.
2. Under this identification, `step_measure = (Measure.pi (fun _ => Z_uniform)) ⊗ step_measure` (the Mathlib lemma, name TBD — may be `Measure.infinitePi_split_at` or constructed via two applications of `Measure.infinitePi_apply_cyl`).
3. The event factors as a Cartesian product because (a) `{T_u_at x Y = n}` depends only on the first `n` coordinates, (b) `X_infinity_starting_at x Y = X_infinity_starting_at u (Y ∘ (· + n))` on `{T_u_at x Y = n}` (since `W_n^x = u`).
4. Apply Tonelli (`MeasureTheory.lintegral_prod` or `setLIntegral_prod`).
**Estimated 120–180 LOC.** This is the load-bearing step. The Mathlib API for "split off first n coords from infinitePi" may need a small helper if it's not directly available; but it's NOT a new admission — it's a Mathlib-API derivation from `Measure.infinitePi_pi` + `Measure.pi.eval_pi`.

### Step 4 → Linear recurrence + transience
**Lean obligation.** Prove
```
step_measure {Y | T_u_at v Y < ⊤} = 3^(-(d(v, u)))
```
by induction on `h = d(v, u)`, using the recurrence `f(h) = (1/4) f(h-1) + (3/4) f(h+1)` and transience.
**Existing infrastructure.** Project has `walk_dist_tendsto_atTop` (transience as `|X_walk| → ∞`). Need to extract from it that "the walk visits any fixed vertex only finitely often", which follows from `|X_walk_n Y| → ∞` (a vertex's distance from origin is bounded, so the walk can be at the vertex only when its distance equals that bound; eventually `|X_walk n Y| > bound`).
**Estimated 60–100 LOC.** The linear recurrence + characteristic equation is straightforward Lean.

### Step 5 → Synthesis
**Lean obligation.** Combine Steps 3 and 4 to prove the two axioms as theorems. Specialise Step 3 + Step 4 with `x` and `o = 1`.
**Estimated 30–50 LOC.** Mostly algebraic glue + ENNReal/Real bookkeeping.

## Total LOC budget

| Step | LOC |
|---|---|
| 1 (path-counting hitting pmf) | 60-80 |
| 2 (geometric inclusion) | 50-80 |
| 3 (keystone factorisation) | 120-180 |
| 4 (recurrence + transience) | 60-100 |
| 5 (synthesis) | 30-50 |
| **Total** | **~320-490 LOC** |

Likely doubled by Lean engineering overhead (per Wave 34-final v2 calibration: ~2x). Realistic budget: **600-1000 LOC**. NO new admissions of any kind; NO new abstract probability infrastructure (no `IsStoppingTime`, no filtration, no general strong-Markov theorem).

## Mathlib API gap status

The Distiller's earlier blueprint identified one gap: "strong Markov on `infinitePi`". This is **circumvented** by the Step 3 encoding above, which uses only `Measure.infinitePi`'s split-off-first-n factorisation (already in Mathlib) + Tonelli (already in Mathlib). The "shift invariance" reasoning of strong Markov is replicated **inline** via the i.i.d. product-measure structure. No abstract Markov theorem invoked.

The path-counting lemma in Step 1 may need a small helper: counting reduced-word paths between fixed vertices on a 4-regular tree. This is project-internal combinatorics, not a Mathlib gap.
