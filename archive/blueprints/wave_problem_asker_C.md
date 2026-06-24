# Problem: Two cylinder identities for the SRW exit measure on the 4-regular tree, via direct product-measure decomposition

You are required to give a **rigorous, self-contained, graduate-level proof**
of the two claims below. There is no opt-out. **Strict tool restrictions
apply** — see the **Forbidden** section. The point of this prompt is *not*
to find any proof; the point is to find an **elementary proof using only the
listed allowed tools**. A proof that ignores the restrictions is useless to
us.

## Setup (all given)

Let `T` be the infinite 4-regular tree, with a distinguished root `o`.
Equivalently, `T` is the Cayley graph of the free group `F_2 = ⟨a, b⟩` with
respect to the symmetric generating set `S = {a, b, a⁻¹, b⁻¹}`. Each vertex
`x ∈ T` is a reduced word over `S`; let `|x|` denote its length (graph
distance from `o`). The root `o` is the empty word, `|o| = 0`.

Let `∂T` denote the space of ends (geodesic rays from `o`); a ray `φ` is
identified with the infinite sequence `(φ_0, φ_1, φ_2, …)` of its consecutive
edge labels (each `φ_i ∈ S`, with `φ_{i+1} ≠ φ_i⁻¹` to enforce no
backtracking). For `x ∈ T` and `φ ∈ ∂T`, write `c(x, φ)` for the length of
the longest common prefix of `x` (read as a reduced word) and `φ`.

For an integer `q ≥ 0`, the **cylinder**
```
I(φ, q) = { ψ ∈ ∂T : ψ_i = φ_i ∀ i < q }
```
is the set of ends sharing the first `q` edge-labels with `φ`. (`I(φ, 0) = ∂T`.)

### Concrete probabilistic construction (this is the key)

The SRW from `x` is realised by an **i.i.d. sequence of generator-valued
increments**. Let
```
(Ω, μ_∞) = (S^ℕ, ⊗_{n ∈ ℕ} ν),
```
where `ν` is the uniform probability on the 4-element set `S = {a, b, a⁻¹, b⁻¹}`.
A point of `Ω` is a sequence `Y = (Y_0, Y_1, Y_2, …) ∈ S^ℕ`. Each `Y_n` has
law `ν` (uniform on `S`), and the `Y_n` are mutually independent.

The walk position from starting vertex `x` is:
```
W^x_n(Y)  =  x · Y_0 · Y_1 · … · Y_{n−1}    ∈ T          (product in F_2),
```
with `W^x_0 = x`. Almost surely (under `μ_∞`), `|W^x_n| → ∞` and
`W^x_n` converges to a random end `X^x_∞(Y) ∈ ∂T`. We define the
**exit measure based at `x`** as the pushforward
```
μ_x  =  (X^x_∞)_∗ μ_∞    on    ∂T.
```

You may assume (these are standard / already established):
* `μ_x` is a probability measure on `∂T`.
* Cylinders are Borel, and form a π-system generating the Borel σ-algebra.
* `Y ↦ X^x_∞(Y)` is `μ_∞`-a.e.-defined and measurable.

## The claims to prove

For every `x ∈ T`, every `φ ∈ ∂T`, and every integer `q ≥ |x|`, let
`c := c(x, φ)` and let `u` be the vertex at distance `c` from `o` along
the φ-ray (so `|u| = c`, `u` is a prefix of `φ`, and `u` is the "meeting
vertex" of `x`'s reduced word and the φ-ray).

**Claim 1 (factorisation from `x`).**
```
μ_x(I(φ, q))  =  3^{−(|x| − c)}  ·  μ_u(I(φ, q)).
```

**Claim 2 (factorisation from `o`).**
```
μ_o(I(φ, q))  =  3^{−c}  ·  μ_u(I(φ, q)).
```

## Allowed tools (use only these)

1. **Product-measure factorisation of `μ_∞`.** For any `n ∈ ℕ`,
   `μ_∞ = ν^{⊗ n} ⊗ μ_∞` under the natural identification
   `S^ℕ ≃ S^{Fin n} × S^ℕ` (split off the first `n` coordinates; the
   "first-`n`" factor and the "shifted-tail" factor are independent
   product factors with the stated marginals). This is the
   `Measure.infinitePi`-style decomposition; you may use it freely.
2. **Tonelli/Fubini** for σ-finite product measures.
3. **Path counting on `T`.** The number of reduced-word paths
   of length `n` between any two specified vertices, etc.
4. **σ-additivity / countable disjoint partitions.** In particular,
   for any random integer `T : Ω → ℕ ∪ {∞}` you may decompose any
   event `E ⊆ Ω` as `E = (E ∩ {T = ∞}) ⊔ ⨆_{n ∈ ℕ} (E ∩ {T = n})`.
5. **Conditional probability as a ratio of measures.** You may write
   `P(A | B) := P(A ∩ B) / P(B)` whenever `P(B) > 0`. You may NOT use
   any `MeasureTheory.condExp`-style abstract conditional expectation.
6. **Elementary identities** for `3^k`, geometric series, `S`-cardinality
   (`|S| = 4`, "non-cancelling neighbours" = 3 in the interior of `T`),
   induction on `|x|` or on `|x| − c`.
7. **The simple random walk on `T` is transient** (you may take this as a
   given fact: from any vertex, the walk visits the root only finitely
   often a.s.).

## Forbidden (these are the load-bearing constraints)

- **Do not invoke "the strong Markov property" by name.** It is what
  this prompt is trying to avoid.
- **Do not use stopping times as formalised objects.** You may informally
  refer to "the first time `n` such that `W^x_n = u`" as an integer-valued
  random variable `T_u(Y)`, but you may not invoke any general theorem
  *about* stopping times — no `IsStoppingTime` API, no "stopped sigma-algebra",
  no Doob optional stopping, no strong-Markov-at-stopping-time theorem.
  Specifically: you may compute `μ_∞{T_u = n}` by direct path-counting
  (count the number of reduced-word paths of length `n` from `x` to `u`
  that don't hit `u` before step `n`), but you may not say "by the strong
  Markov property".
- **Do not invoke filtrations** `σ(Y_0, …, Y_{n−1})` as objects with API.
  You may speak informally about "events depending only on the first `n`
  coordinates" and decompose them using Tool 1.
- **Do not appeal to abstract Markov-chain theory** (Kolmogorov, Chapman–
  Kolmogorov in operator form, etc.) — only the i.i.d. product structure
  of `μ_∞` is allowed.
- Do not say "this is standard" or flag any step as needing further work.

## What to deliver

A complete, self-contained proof of both Claim 1 and Claim 2. Aim for a
careful **two-to-three-page** graduate-booklet exposition:

1. State the path-counting / first-passage computation you use to
   evaluate `μ_∞{T_u = n}` directly, and prove the key identity:
   ```
   μ_∞{T_u = n}  =  (number of reduced-word paths of length n from x to u
                     that avoid u in the first n−1 steps)  ·  (1/4)^n.
   ```
   (The "shape" of these paths — biased outward/inward random walk on a
   single geodesic — is computable from the 4-regularity of `T`.)
2. Show that the event `{X^x_∞ ∈ I(φ, q)}` is contained in `{T_u < ∞}`
   (any walk that converges to a ray through `u` must visit `u`).
3. **The keystone step.** On the event `{T_u = n}`, decompose the walk
   `(W^x_0, W^x_1, …)` as a deterministic-up-to-step-`n` segment from
   `x` to `u`, followed by a *fresh* SRW from `u` (this is the i.i.d.
   shift, formalised via Tool 1: the tail `(Y_n, Y_{n+1}, …)` is
   independent of `(Y_0, …, Y_{n−1})` with the same product law, so the
   shifted walk `W^u_k(Y_n, Y_{n+1}, …) := u · Y_n · … · Y_{n+k−1}` is
   independent of the prefix and has the law of a SRW from `u`).
   Conclude that
   ```
   μ_∞ ({X^x_∞ ∈ I(φ, q)} ∩ {T_u = n})  =  μ_∞{T_u = n} · μ_u(I(φ, q)).
   ```
   Sum over `n ∈ ℕ` and use Tool 4 (σ-additivity over the partition
   `{T_u = 0}, {T_u = 1}, …, {T_u = ∞}`) to obtain
   ```
   μ_x(I(φ, q))  =  μ_∞{T_u < ∞} · μ_u(I(φ, q)).
   ```
4. Compute `μ_∞{T_u < ∞} = 3^{−(|x| − c)}` by induction on `|x| − c`,
   using a quadratic equation derived from the first step (paths of
   length 1) plus transience (Tool 7) to discard the spurious root.
5. Combine to give Claim 1. Specialise to `x = o`, where `c(o, φ) = 0`
   and the meeting vertex is still the same `u = φ_{0}φ_1 … φ_{c−1}`,
   to give Claim 2.

Be explicit about *which* allowed tool you invoke at each step. The goal
is a proof such that an implementer working in Lean 4 against Mathlib's
existing `Measure.infinitePi` API can transcribe it into ~200-400 lines
of Lean code without needing to first build any new abstract probability
infrastructure (no `IsStoppingTime`, no filtration, no general-purpose
strong-Markov theorem).

## Why the constraints are load-bearing

This problem has a *direct* strong-Markov proof (we already have it). The
purpose of this prompt is to find a **second proof**, sur-mesure for the
specific i.i.d. setup, that uses only the `Measure.infinitePi`-style
factorisation as its "Markov input". Mathlib has that factorisation but
does not yet have a strong-Markov-at-stopping-time theorem for product
measures; the path forward for the formalisation is to find a proof that
sidesteps the gap by computing things directly.

If your proof essentially reproves the strong-Markov property (and it
will, in some form — that is what step 3 above is) but does so using
**only Tool 1's product-measure factorisation + Tool 4's σ-additivity +
Tool 3's path counting**, with all "shift invariance" reasoning done
*inline* via the i.i.d. structure, you have succeeded.
