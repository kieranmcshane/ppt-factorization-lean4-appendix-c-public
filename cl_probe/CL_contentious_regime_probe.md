# Challenging (CL) in the contentious regime — two workarounds

The contentious regime for (CL) is the **diagonal** `r ≍ a_d = d^(2+2/k)` with `d` large:
exact enumeration dies ((kr)! superfactorial) and naive Monte Carlo dies (the
tail has probability `~exp(−a_d·rate)`). Two workarounds were attempted.

## Workaround 1 — exact genus-graded enumeration (SUCCEEDED, gives a real challenge)

Tabulate the **active** permutations of `S_{kr}` (no trivial block) by
`(j = r − c(π), h = g(π)+g'(π))`, with `E_r(π) = 4j + 2h`. The `d→∞` ratio
`c_r := lim_d R_{r,d}/B_{r,d}` is carried entirely by the **minimal-energy band**.

Finding (k=2, λ=1):
- For **even** `r`, the minimum active energy is exactly `E = 2r`, all of it in the
  **planar** band `h = 0`, `j = r/2`. Then `c_r = #{active π with E = 2r}`.
- For **odd** `r`, `E_min > 2r`, so `c_r = 0` (centering kills it).

Exact / MC values of the planar active count:

| r=2m | c_r | c_r / m! | ratio of (c_r/m!) |
|------|-----|----------|--------------------|
| 2 (m=1) | 18 (exact) | 18 | — |
| 4 (m=2) | 972 (exact) | 486 | 27.0 |
| 6 (m=3) | 85 668 (MC, ±3%) | 14 278 | 29.4 |
| 8 (m=4) | ≈ 8.7×10⁶ (MC, 3 hits, ±~58%) | ≈ 363 000 | ≈ 25 |

(The MC estimator was validated against the exact value at r=4: 958.7 vs 972; a
vectorized cycle-counter pushed the sample counts to reach r=8.)

**The challenge — the growth is factorial.** `c_r / m!` has a *constant* ratio
(~27), not a decaying one, which rules out geometric growth `c_r ~ ν^r` and pins
the law to

```
c_{2m} ~ C · m! · μ^m ,   μ ≈ 27.
```

Hence `(1/r) log c_r ~ (1/2) log(r/2) → ∞`. In the `d→∞`-first order of limits the
active sum `R_{r,d}` exceeds the one-spike scale `B_{r,d}` by a **factorial** factor
— i.e. it carries the full `(kr)! = exp(Θ(a_d log d))` entropy, the exact fatal
log-factor the whole upper-bound problem is about. If this carried over to the
diagonal `r ≍ a_d`, then `(1/a_d) log(R/B) ~ (1/2) log a_d → ∞` and **(CL) would
fail — not by a constant, but by the log factor.**

**The escape hatch (why this is not yet a disproof).** `c_r` is the `d→∞`-first
slice; (CL) lives on the diagonal, the opposite order of limits. On the diagonal,
the finite-`d` penalty `d^(−E)` on higher-merge / higher-genus bands must suppress
the planar proliferation. The enumeration cannot settle this, but it localizes the
entire fight precisely: **planar active entropy vs. the `d^(−E)` penalty at
`r ≍ a_d`.** This is the same entropy-vs-penalty mechanism that killed (EL); here it
is quantified, and it leans *against* (CL).

## Workaround 2 — spike-tilted importance sampling (FAILED; instructive)

To probe the actual tail of `Z` (the end that (CL) serves) at moderate `d`, two
importance samplers were built:
1. Gaussian rank-one tilt `G → G + tM`, reweight by `exp(−2t Re⟨M,G⟩ + t²)`.
2. Beta-tilt of the spike mass `R ~ Beta(α, Ns−1)` with `α ≈ a_d·x^{1/k}`,
   reweight by the exact density ratio `w ∝ R^{1−α}`.

**Both fail with the same pathology:** exponential weight variance (`Var(w) ~ e^{2t²}`
for #1; `w ∝ R^{1−α}` with `α ≈ a_d` for #2). Effective sample size ≈ 0; the IS
estimate of `P(Z ≥ 9.5)` at `d=6` came out `~10^{−18}` against the true `~0.28`.

**Lesson.** The rare event constrains the *whole* spike-plus-bulk configuration;
matching one marginal (the Gaussian shift, or the `R`-marginal) leaves the reweight
wild. Reaching this tail needs real rare-event machinery — **subset simulation /
multilevel splitting, cross-entropy adaptive IS, or sequential Monte Carlo** — or a
proposal equal to the full conditional law `· | Z ≥ τ`. A single-parameter tilt is
provably insufficient. (Naive MC, for the record, only ever sees the CLT/finite-size
window at accessible `d ≤ 8`, with rates 15–30× below `λx^{1/k}` — nowhere near the
asymptotics.)

## Bottom line

**CORRECTION (see `CL_diagonal_analysis.md`).** The factorial growth of `c_r` is a
`d→∞`-**first** artifact and does **not** transfer to a diagonal violation. On the
genuine diagonal `r = ρa_d`, the minimal-energy (planar/spike, `E=2r`) family's
contribution to `(1/a_d)log(R/B)` is `(½(1+1/k) − 1)·ρ log N → −∞` — verified
numerically (k=2): `−0.215, −0.475, −0.751, −1.108` at `N=200,1000,4000,20000`. The
reason: the rising factorial in `B_{r,d}` has exponent `∼ r log N`, which strictly
dominates the family's factorial entropy exponent `∼ ½(1+1/k) r log N < r log N`. So
the spike family is **(CL)-consistent**, not against it.

Net, honestly: the exact route did **not** disprove (CL); my earlier "leans toward
false" is retracted. (CL) reduces exactly to controlling the full energy spectrum
`sup_E [log N_r(E) − (E/2)log N] ≤ r log N + o(a_d)`; only the bottom band `E=2r` is
settled (it's fine). Whether a higher-energy (more-merged, higher-genus) band
overtakes it is the genuine open problem — a constellation / topological-recursion
question for the partial-transpose bipartite maps. No rigorous evidence currently
points either way.

Tooling: `genus_grade.py` (exact (j,h) tables), `c6_mc.py` (MC for larger r),
`beta_is.py` (the importance sampler and its failure mode).
