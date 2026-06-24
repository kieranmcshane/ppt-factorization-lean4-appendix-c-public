# Problem: Translation identity for the exit measure of the simple random walk on the 4-regular tree, on a deep cylinder

You are required to give a **rigorous, self-contained, graduate-level proof**
of the claim below. There is no opt-out. Use only the listed tools.

## Setup (all given)

Let `T` be the infinite 4-regular tree, with a distinguished vertex `o` (the
"root"). Equivalently, `T` is the Cayley graph of the free group `F_2` on two
generators with respect to the four generators (so every vertex has degree 4,
including the root). Each vertex `x` is a reduced word in the generators; let
`|x|` be its length (graph distance from `o`).

Let `∂T` be the space of ends (geodesic rays from `o`); a ray `φ` is identified
with the infinite sequence `(φ_0, φ_1, …)` of its consecutive edge labels (each
`φ_i` is one of the four generators, with no immediate cancellation
`φ_{i+1} ≠ φ_i^{-1}`).

For a vertex `x ∈ T` and an end `φ ∈ ∂T`, write `c(x, φ)` for the length of
the longest common prefix of `x` (read as a reduced word) and `φ`. The
**Busemann function** is
```
b_φ(x) = |x| − 2 c(x, φ) ∈ ℤ.
```
(So `b_φ(x) ≥ 0` when `x` lies "off" the ray `φ`, and `b_φ(x) = −|x|` when `x`
is a prefix of `φ`.) Set the **Poisson kernel** `p_φ(x) = 3^{−b_φ(x)}`.

For a vertex `x`, let `(W_n^x)_{n ≥ 0}` be the simple random walk on `T`
started at `x`: at each step, jump to a uniformly chosen neighbour
(probability `1/4` to each of the 4 neighbours). It is a standard fact that
`|W_n^x| → ∞` almost surely, and that `W_n^x` converges almost surely to a
random end `X^x_∞ ∈ ∂T`. Let `μ_x` be the law of `X^x_∞` on `∂T`.

For an end `φ ∈ ∂T` and an integer `q ≥ 0`, the **cylinder**
```
I(φ, q) = { ψ ∈ ∂T : ψ_i = φ_i for all i < q }
```
is the set of ends sharing the first `q` letters with `φ`. (For `q = 0`,
`I(φ, 0) = ∂T`.)

You may assume: `μ_x` is a probability measure on `∂T`; cylinders are Borel.

## The claim to prove

For every vertex `x ∈ T`, every end `φ ∈ ∂T`, and every integer `q ≥ |x|`,
```
μ_x(I(φ, q)) = p_φ(x) · μ_o(I(φ, q)).
```

## Allowed tools

- Strong Markov property of the simple random walk on `T` and elementary
  combinatorics on `T` (path counting, neighbour decomposition).
- Symmetry of `T`: any automorphism of `T` (rooted or not) pushes the walk
  forward to a walk of the same law (after relabelling start/end).
- The fact that on a 3-regular subtree (i.e. the tree `T` viewed away from
  the root, where every vertex has degree 3 once we condition on a "back"
  edge), the random walk is biased outward in a precise way computable from
  3-step transition probabilities.
- Coupling / first-passage decomposition: the walk from `x` first reaches
  the prefix of `φ` at depth `c(x, φ)`, then must travel out along `φ`
  to depth `q` while never backtracking past depth `q`.
- Elementary identities for `3^k`, geometric series, and induction on
  `|x|` or on `q − |x|`.

## Forbidden

- **Do not cite "Cartwright–Soardi 1989" or "Furstenberg 1971"** as a black
  box, or any named theorem about translation invariance of harmonic measure
  on trees / hyperbolic groups.
- **Do not invoke "the Busemann cocycle" as a heavy abstract tool** —
  treat `b_φ(x)` purely as the integer `|x| − 2 c(x, φ)`.
- Do not appeal to Martin / Poisson boundary theory as a black box.
- Do not say "this is standard" or flag any step as needing further work.

## What to deliver

A complete, self-contained proof. Aim for a careful one-to-two-page
graduate-booklet exposition: state the path-counting / first-passage
identity you use, justify it, then derive the factor `3^{−b_φ(x)}`
explicitly. The argument should make it clear *why* the multiplier is
exactly `3^{−b_φ(x)}` and not some other function of `x` and `φ`.
