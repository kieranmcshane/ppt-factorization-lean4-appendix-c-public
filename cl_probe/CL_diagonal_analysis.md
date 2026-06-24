# Diagonal analysis of (CL): what is proved, and a retraction

This note records what can be proved rigorously about (CL) on the diagonal
`r ≍ a_d`, and **retracts** the earlier numerical claim that the genus-graded data
"leans toward (CL) false." On careful analysis the data does no such thing.

Throughout: even `k ≥ 2`, `N = d²`, `s = λN`, `a_d = N^{1+1/k}`, `λ = 1` for the
display (general `λ` identical). `(s)_q = s(s+1)···(s+q−1)`. For an active permutation
`π ∈ S_{kr}` (no trivial block) write `E_r(π) = 4(r−c) + 2(g+g') ≥ 0` for the energy.

## 1. Exact diagonal reduction (rigorous)

Let `N_r(E) = #{active π ∈ S_{kr} : E_r(π) = E}` (taking `λ = 1`). From the exact
active-sum form `R_{r,d} = Σ_{active π} d^{−E_r(π)}` and `B_{r,d} = N^{−r}(s)_{kr}/s^{kr}`,
and using `d^{−E} = N^{−E/2}`,

```
R_{r,d} / B_{r,d}  =  ( Σ_E N_r(E) N^{−E/2} ) · s^{kr}/(s)_{kr} .            (★)
```

This is an identity. (CL) — `R_{r,d} ≤ exp(o(a_d)) B_{r,d}` uniformly for `r ≤ C a_d`
— is therefore **equivalent** to the variational bound

```
sup_E [ log N_r(E) − (E/2) log N ]  ≤  log[(s)_{kr}/s^{kr}] + o(a_d)            (CL′)
```

uniformly on `r ≤ C a_d`. The whole problem is the entropy–penalty competition in (CL′).

## 2. The rising-factorial penalty (rigorous)

**Lemma.** On the diagonal `r = ρ a_d`,
`log[(s)_{kr}/s^{kr}] = r log N · (1 + o(1))`.

*Proof.* `log[(s)_{kr}/s^{kr}] = Σ_{i=0}^{kr−1} log(1 + i/s)`. With `u := kr/s =
kρ N^{1/k}/λ → ∞`, the sum is `s∫_0^{u}log(1+x)dx·(1+o(1)) = s[(1+u)log(1+u)−u](1+o(1))
= s·u log u·(1+o(1)) = kr·log u·(1+o(1)) = kr·(1/k)log N·(1+o(1)) = r log N (1+o(1))`,
since `log u = (1/k)log N + O(1)`. ∎

Numerically verified: for `k=2`, `r = ⌊a_d⌋`, the ratio
`log[(s)_{kr}/s^{kr}] / (r log N)` is 0.976, 0.942, 0.935, 0.937 at `N = 50,200,1000,4000`
(→ 1, slowly).

## 3. The minimal-energy ("spike") family is (CL)-consistent — RETRACTION of the alarm

The smallest active energy for even `r` is `E = 2r` (the planar, single-outlier band);
its count is `A_r := N_r(2r)`. Exact/MC values (`k=2`): `A_2=18, A_4=972, A_6=85668,
A_8≈8.7×10⁶`, with `A_{2m}/m!` ≈ constant (≈27), i.e. **factorial growth**
`A_{2m} ∼ C·m!·μ^m`, `μ ≈ 27`. So `log A_r ∼ (r/2)log(r/2) ∼ ½(1+1/k) r log N`
(for `k=2`, exponent `→ 0.75`).

Its contribution to (★) is `A_r · s^{kr}/(s)_{kr}`, with diagonal exponent

```
(1/a_d) log[ A_r · s^{kr}/(s)_{kr} ]  =  (1/a_d)( log A_r − r log N (1+o(1)) )
     →  ( ½(1+1/k) − 1 ) · ρ log N  =  −(1/2)(1−1/k) ρ log N  →  −∞ .
```

For `k = 2` this is `−¼ ρ log N → −∞`. **Verified numerically** (k=2, `r=⌊a_d⌋`):
the exponent `(log A_r − log[(s)_{kr}/s^{kr}])/a_d` is `−0.215, −0.475, −0.751, −1.108`
at `N = 200,1000,4000,20000` — decreasing without bound.

**Consequence.** The minimal-energy / spike family contributes `R/B → 0` on the
diagonal: it is fully consistent with (CL), not against it. The factorial growth of
`c_r = lim_d R_{r,d}/B_{r,d}` is a `d→∞`-**first** artifact; it does not transfer to
the diagonal because the rising-factorial penalty (`∼ r log N`, §2) strictly
dominates the planar entropy (`∼ ½(1+1/k) r log N < r log N` for all finite `k`).

**Retraction.** The earlier statement that the genus-graded numerics "lean toward
(CL) false" was wrong. They establish factorial entropy in the `d→∞`-first slice,
which is the wrong order of limits; on the diagonal the spike band obeys (CL). No
rigorous evidence currently points either way.

## 4. What is genuinely open

(CL) reduces to (CL′): control of `sup_E [ log N_r(E) − (E/2) log N ]` against
`r log N`. §3 settles only the bottom of the spectrum (`E = 2r`). The open question
is whether some **higher-energy** band — more merges `j`, higher genus `h`, hence
more permutations `N_r(E)` but a larger penalty `N^{−E/2}` — overtakes it and breaches
(CL′). Equivalently: does the genus-resolved active count `N_r(E)` satisfy
`log N_r(E) ≤ (E/2)log N + r log N + o(a_d)` uniformly on the diagonal?

This is exactly a **topological-recursion / constellation-enumeration** statement for
the partial-transpose bipartite maps, and is the precise remaining content of the
sharp upper bound. It is not settled here (nor by any prior attempt; the external
`(EL)` reduction to it was false).

## Honest status

- **Lower bound** `λ(τ−m_k)^{1/k}`: proved (independent), unaffected.
- **(CL) / upper bound**: open. The natural spike mechanism is (CL)-consistent
  (§3). No rigorous argument for or against (CL) on the diagonal.
- A complete proof of (CL) is **not** achieved here; it requires the energy-resolved
  enumeration (§4). Claims to the contrary — including the retracted numerical
  "evidence against" — do not survive the diagonal exponent computation.
