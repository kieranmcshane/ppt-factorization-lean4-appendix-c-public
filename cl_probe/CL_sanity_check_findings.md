# Is (CL) false? — exact small-case sanity checks

Picking up the interrupted computation: after the referee disproved the connected
enumeration lemma **(EL)**, the open question became whether the lemma it was meant
to prove — **(CL)** — is itself false, or whether it survives sanity checks.

**(CL).** With `N = d²`, `s = λN`, `a_d = d^(2+2/k)`, and rising factorial `(s)_q = s(s+1)···(s+q−1)`,
the active permutation sum must satisfy, uniformly for `0 ≤ r ≤ C·a_d`,

```
R_{r,d}  ≤  exp(o(a_d)) · B_{r,d},     B_{r,d} = N^(−r) (s)_{kr} / s^{kr}.
```

Here `R_{r,d} = Σ_{π active} λ^(#π−kr) d^(−E_r(π))`, and the **exact centering identity**
`R_{m,d} = E[(Ẑ − b_d)^m]` lets us also compute it as a centered moment of the
unnormalized observable `Ẑ`, with `b_d = Σ_{σ∈𝒢_k} λ^(#σ−k)`.

## What was computed (exact, rational arithmetic)

Full enumeration of `S_{kr}`: `k=2` for `r = 1..5` (up to 10! permutations),
`k=4` for `r = 1,2`. Two values of `λ` (1 and 2). All quantities exact (Fraction),
so the centered moments are free of the floating-point cancellation that wrecks them
at large `d`.

## Results

**1. The rigorous backbone checks out exactly.** `R` computed two independent ways —
directly as the active-permutation sum, and via the binomial centering identity from
the `M_r = E[Ẑ^r]` moments — agree to the last bit in every case. And `b_d = m_k`
*exactly* (`m_2 = 1+1/λ`, `m_4 = 1+6/λ+2/λ²`), for all `d`, both `k`. The code
faithfully reproduces the paper objects.

**2. (CL) holds in every reachable case.** For each fixed moment order `r`, the ratio
`R_{r,d}/B_{r,d}` converges, as `d→∞`, to a finite constant `c_r` (even `r`); odd-`r`
central moments →0. So `(1/a_d)·log(R/B) → 0` — exactly what (CL) predicts.

```
k=2, λ=1:   c_2 → 18,    c_4 → 972          (d = 10⁴, exact)
k=2, λ=2:   c_2 → 5,     c_4 → 75
k=4, λ=1:   c_2 → ~1648
```

**3. The (EL) disproof mechanism is visible.** Among permutations with ⟨γ,π⟩
transitive (which is the typical case — 82–84% already at these tiny sizes,
consistent with `1−O(1/ℓ)`), the cycle-excess `t` is **not** rare: its mean grows
with `q = kr` (1.00, 1.80, 2.46, 3.01 for `q = 2,4,6,8`), tracking the predicted
`t ≈ 2 ln q`. This is the heart of the referee's refutation of (EL): logarithmic
cycle-excess is typical, not penalized away.

## Verdict

**(CL) is not disproved, and it passes every sanity check we can compute.** But the
checks only reach the *easy* regime `r ≪ a_d` — precisely the range the crude bound
already handles. The regime that decides (CL), `r ≍ a_d = d^(2+2/k)`, requires
enumerating `(k·a_d)!` permutations with `d` large, and is exponentially out of reach
of exact computation or Monte Carlo (the events are large-deviation rare).

**One caution.** The `d→∞` limiting constant `c_r = lim_d R_{r,d}/B_{r,d}` grows at
least exponentially in `r` (≈ `e^(1.7r)` for `k=2, λ=1`, faster for larger `k`), and
`(log c_r)/r` is *increasing*. This is the `d→∞`-first limit, **not** the diagonal
`r ≍ a_d`, so it does not bound (CL) either way — but it shows the one-spike scale
`B_{r,d}` undershoots `R_{r,d}` by a factor that grows with `r`. Whether that factor
stays `exp(o(a_d))` on the diagonal is *exactly* the open content of (CL) — and it is
the same entropy question the (EL) disproof showed we had underestimated once already.

**Bottom line:** simulations support (CL) wherever they can see, cannot see where it
might break, and give one mild reason for caution. (CL) remains a valid *sufficient*
condition for the sharp upper bound, genuinely open, and — since (EL) is dead — with
no current proof route.
