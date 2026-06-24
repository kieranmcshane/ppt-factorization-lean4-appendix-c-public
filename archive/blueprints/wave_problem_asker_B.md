# Problem: Boundary continuity of a Poisson-type integral on a compact ultrametric end-compactification

You are required to give a **rigorous, self-contained, graduate-level proof**
of the claim below. There is no opt-out. Use only the listed tools.

## Setup (all given)

Let `T` be the infinite 4-regular tree with a distinguished root `o`. Each
vertex `x ∈ T` is a reduced word; let `|x|` denote its length. Let `∂T`
denote the space of ends of `T`; an end `φ` is the infinite sequence of
generator-letters along its geodesic from `o`.

Let `\bar T = T ⊔ ∂T` be the standard end-compactification, equipped with
the ultrametric
```
d(y, z) = e^{−p(y,z)},
```
where `p(y, z)` is the largest integer `p ≥ 0` such that `y` and `z`
share the first `p` letters of their reduced-word / end representations
(with the convention that vertices of `T` are extended by an "end-of-word"
symbol). Two key features:

- `\bar T` is a compact metric space; vertices `x ∈ T` are isolated points;
  ends `φ ∈ ∂T` are accumulation points.
- For an end `φ ∈ ∂T` and an integer `p ≥ 1`, the open ball of radius
  `e^{−p}` around `φ` in `\bar T` is exactly the set of points (vertices
  *and* ends) sharing the first `p` letters with `φ`. In particular, if
  `x ∈ T` has `|x| ≥ p` and shares the first `p` letters of `φ`, then
  `x` lies in this ball.

For each `x ∈ T`, let `μ_x` be a probability measure on `∂T` (the **exit
measure** of the simple random walk on `T` started at `x`). Define, for
each end `ψ ∈ ∂T` and vertex `x ∈ T`,
```
p_ψ(x) = 3^{−(|x| − 2 c(x, ψ))},
```
where `c(x, ψ)` is the length of the longest common prefix of `x` and `ψ`.

## Given facts (you may use these)

(F1) **Cylinder concentration of the exit measure.** For every end `φ ∈ ∂T`
and every integer `p ≥ 1`, if `x ∈ T` has `|x| ≥ p` and shares the first
`p` letters of `φ`, then
```
μ_x(I(φ, p)) ≥ 1 − C · 3^{−(|x| − p)},
```
where `I(φ, p) = { ψ ∈ ∂T : first p letters of ψ agree with those of φ }`,
and `C` is an absolute constant (you may take `C = 3`). Equivalently,
`μ_x(∂T \ I(φ, p)) → 0` as `|x| → ∞` along the prefix of `φ`.

(F2) **Poisson representation.** For every continuous `g : ∂T → ℝ` and
every vertex `x ∈ T`,
```
∫_{∂T} g(ψ) p_ψ(x) dμ_o(ψ) = ∫_{∂T} g(ψ) dμ_x(ψ).
```

(F3) **Compactness.** `∂T` is compact (in the subspace topology from `\bar T`),
hence every continuous `g : ∂T → ℝ` is bounded and uniformly continuous on
`∂T`.

Now, given a continuous `g : ∂T → ℝ`, define `h : \bar T → ℝ` by
```
h(y) = g(y)                         if y ∈ ∂T,
h(y) = ∫_{∂T} g(ψ) p_ψ(y) dμ_o(ψ)   if y ∈ T.
```

## The claim to prove

For every continuous `g : ∂T → ℝ` and every end `φ ∈ ∂T`, the function `h`
is continuous at the point `φ ∈ \bar T`, i.e.
```
∀ ε > 0, ∃ δ > 0, ∀ y ∈ \bar T, d(y, φ) < δ ⟹ |h(y) − h(φ)| < ε.
```

## Allowed tools

- The given facts (F1), (F2), (F3) above, used directly.
- ε / δ arguments and uniform continuity of `g` on `∂T`.
- Splitting an integral `∫_{∂T} = ∫_{I(φ,p)} + ∫_{∂T \ I(φ,p)}` and
  bounding each piece.
- Total mass of probability measures (`μ_x(∂T) = 1`).
- Elementary inequalities: `|∫ f dμ| ≤ ‖f‖_∞ · μ(supp)` for bounded `f`,
  triangle inequality.

## Forbidden

- **Do not cite "weak convergence", the "Portmanteau theorem", or
  "tightness of a family of measures" as a black box.**
- **Do not invoke a generic "cylinder concentration ⇒ weak convergence"
  framework.**
- Do not reference any abstract Martin-boundary, Poisson-boundary, or
  potential-theoretic apparatus by name.
- Do not say "by standard measure theory" or flag any step as
  needing further work.

## What to deliver

A complete, self-contained ε/δ proof. Aim for a careful one-to-two-page
graduate-booklet exposition. Two cases must both be handled:

1. `y ∈ ∂T` near `φ`: use uniform continuity of `g` and `h(y) = g(y)`.
2. `y ∈ T` near `φ` (so `y` is a vertex of `T` whose word extends `φ`'s
   prefix to a large depth): use (F2) to rewrite `h(y)`, split the integral
   over `I(φ, p)` and its complement, bound the complement using (F1),
   and bound the cylinder piece using uniform continuity of `g`.

Be explicit about the choice of `p` and `δ` in terms of `ε` and the
modulus of continuity of `g`.
