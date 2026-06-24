# Wave 29 blueprint — dissolve `harmonic_measure_translation_on_deep_cylinder`

## External LLM proof (paste-verbatim from user submission)

The external LLM proved the deep-cylinder factorisation via:

### Lemma 1: Hitting probability `f(k) = 3^{-k}`

For SRW on F_2, `ℙ_a(T_b < ∞) = 3^{-d(a,b)}`.

Proof:
- `f(0) = 1`.
- `f(1)`: from `a` move to `b` w.p. `1/4`, else to `z` (one of 3 non-b neighbours) where `d(z,b) = 2` and unique path z→b passes through a. Strong Markov: `ℙ_z(T_b < ∞) = ℙ_z(T_a < ∞) · ℙ_a(T_b < ∞) = f(1)^2`. So `f(1) = 1/4 + (3/4) f(1)^2`. Quadratic `3f^2 - 4f + 1 = 0`, roots `1, 1/3`. Transience of SRW on F_2 (Q44 in our codebase) selects `f(1) = 1/3`.
- Inductive step on k: `f(k) = 1/4 · f(k-1) + (3/4) · (1/3) · f(k)`, gives `f(k) = (1/3) · f(k-1) = 3^{-k}`.

### Step 2: Cylinder factorisation via strong Markov

Fix `x ∈ F_2`, `φ ∈ ∂F_2`, `q ≥ |x|`. Let `c = c(x, φ)` (common-prefix length) and `u = φ.valPrefix c` (vertex at depth c on φ's ray).

Both `o` and `x` are at distance `c` (resp. `|x|-c`) from `u`. Any walk reaching `I(φ, q)` must pass through `u` (since q ≥ |x| ≥ c, and `I(φ, q)` consists of ends extending through u).

By strong Markov at `T_u`:
- `μ_x(I(φ,q)) = ℙ_x(T_u < ∞) · μ_u(I(φ,q)) = 3^{-(|x|-c)} · μ_u(I(φ,q))`
- `μ_o(I(φ,q)) = ℙ_o(T_u < ∞) · μ_u(I(φ,q)) = 3^{-c} · μ_u(I(φ,q))`

Take ratio:
```
μ_x(I(φ,q)) / μ_o(I(φ,q)) = 3^{-(|x|-c)} / 3^{-c} = 3^{-(|x|-2c)} = 3^{-b_φ(x)} = p_φ(x)
```

Hence `μ_x(I(φ,q)) = p_φ(x) · μ_o(I(φ,q))`. ∎

## Lean implementation plan

### Helper 1: hitting probability lemma `f(k) = 3^{-k}`

```lean
private lemma hitting_probability_eq_three_inv_pow
    (a b : F2) (k : ℕ) (hd : (a⁻¹ * b).toWord.length = k) :
    step_measure {Y | ∃ n : ℕ, X_walk n Y * a = b} = ENNReal.ofReal (3^(-k : ℤ))
```

(Or formulated more directly via SRW on F_2 hitting times — Mathlib's `IsHittingTime` API + transience.)

Proof: induction on k via the LLM's argument. Use Q44's transience (`walk_transience` already in codebase) for the f(1) selection.

Estimated: ~120 LOC.

### Helper 2: strong Markov decomposition at first hitting time

Given `q ≥ |x|`, `c = common_prefix_length x φ`, `u = φ.valPrefix c`:
```lean
private lemma harmonic_measure_factor_at_hitting_vertex
    (x : F2) (φ : ∂F2) (q : ℕ) (hq : q ≥ x.toWord.length) :
    harmonic_measure x (cylinder φ q)
      = ENNReal.ofReal (3^(-(x.toWord.length - common_prefix_length x φ : ℤ)))
        * harmonic_measure (φ.valPrefix (common_prefix_length x φ)) (cylinder φ q)
```

Strong Markov property at the stopping time `T_u`. Mathlib has filtration + stopping time API, but the F_2 walk needs glue. Use `walkFil` (exists from Wave 22F.2.1, dead but resurrectable) or define afresh.

Estimated: ~70 LOC.

### Helper 3: dissolve the admission

The admission says `(harmonic_measure x (cylinder φ q)).toReal = poisson_kernel φ x * (harmonic_measure 1 (cylinder φ q)).toReal`. Combine Helpers 1+2:

```lean
theorem harmonic_measure_translation_on_deep_cylinder
    (x : F2) (φ : ∂F2) (q : ℕ) (hq : q ≥ x.toWord.length) :
    (harmonic_measure x (cylinder φ q)).toReal
      = poisson_kernel φ x * (harmonic_measure 1 (cylinder φ q)).toReal := by
  -- Apply Helper 2 to both sides (with x, and with o = 1).
  -- Take ratio: p_φ(x) emerges as 3^{-b_φ(x)} = 3^{-(|x|-2c)}.
  -- Algebra to match the target.
  ...
```

Estimated: ~30 LOC.

### Total

~220 LOC. Single focused wave.
