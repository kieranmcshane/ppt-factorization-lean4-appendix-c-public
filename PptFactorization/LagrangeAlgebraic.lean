import PptFactorization.HankelBridge
import PptFactorization.RemainderBound
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Algebraic Lagrange coefficients via Chebyshev polynomials

## Overview

The implicit function `ψ` solving `d(m+1, ψ(δ)) = δ · d(m, ψ(δ))` has
Taylor coefficients `cₙ` that are **rational functions of `cos θ` and `sin θ`**
where `θ = π/(m+2)`.

This module computes these coefficients **algebraically**, working with
Chebyshev polynomials `U_n ∈ ℝ[X]` rather than real-analytic functions `ℝ → ℝ`.

### Key substitution

Setting `x = √λ/2`, the tridiagonal sequence becomes:
  `d(n, 4x²) = (2x)ⁿ · U_n(x)`

and the threshold is `x₀ = cos(π/(m+2))`, a root of `U_{m+1}`.

### Algebraic structure

Since `U_{m+1}(x₀) = 0`, Euclidean division gives:
  `U_{m+1} = (X − x₀) · Q_m`    in `ℝ[X]`

where `Q_m(x₀) = U'_{m+1}(x₀) = (m+2)/sin²θ ≠ 0`.

The **Lagrange kernel** is then:
  `h(x) = U_m(x) / Q_m(x)`

which is a well-defined rational function at `x₀`, with value
  `h(x₀) = U_m(x₀) / Q_m(x₀) = 1 / Q_m(x₀)`

(since `U_m(x₀) = 1`). No limits, no L'Hôpital — just polynomial evaluation.

### What this replaces

This module provides algebraic proofs of results that `LagrangeCoefficients.lean`
proves analytically (via `HasDerivAt`, `Tendsto`, `iteratedDeriv`).

## Structure

- §1. Chebyshev root: `U_{m+1}` has `IsRoot` at `cos θ`
- §2. Root factoring: `(X − C x₀) ∣ U_{m+1}` and the quotient `Q_m`
- §3. Quotient evaluation: `Q_m(x₀) = U'_{m+1}(x₀)`
- §4. Algebraic first-order coefficient: `c₁ = U_m(x₀) / Q_m(x₀)`
- §5. Polynomial derivative recursion for higher coefficients

Institut Fourier, Grenoble — Kieran McShane / Cécilia Lancien
-/

open Real Polynomial
open Polynomial.Chebyshev (U)

namespace LagrangeAlgebraic

-- ═══════════════════════════════════════════════════════════════════
-- §0. Bridge: Mathlib Chebyshev derivative ↔ ChristoffelDarboux.chebU_deriv
-- ═══════════════════════════════════════════════════════════════════

/-- The custom `chebU_deriv` equals the Mathlib polynomial derivative of `U`.
    Both satisfy `f(0) = 0`, `f(1) = 2`, `f(n+2) = 2U_{n+1} + 2x·f(n+1) − f(n)`.
    Proof by pair induction. -/
theorem chebU_deriv_eq_poly_derivative (n : ℕ) (x : ℝ) :
    ChristoffelDarboux.chebU_deriv n x =
    (U ℝ (↑n : ℤ)).derivative.eval x := by
  suffices h : ∀ k : ℕ,
    ChristoffelDarboux.chebU_deriv k x = (U ℝ (↑k : ℤ)).derivative.eval x ∧
    ChristoffelDarboux.chebU_deriv (k + 1) x = (U ℝ (↑(k + 1) : ℤ)).derivative.eval x
    from (h n).1
  intro k; induction k with
  | zero =>
    constructor
    · -- chebU_deriv 0 = 0, derivative of U_0 = derivative of 1 = 0
      simp [ChristoffelDarboux.chebU_deriv_zero, Chebyshev.U_zero]
    · -- chebU_deriv 1 = 2, derivative of U_1 = derivative of 2X = 2
      simp [ChristoffelDarboux.chebU_deriv_one, Chebyshev.U_one]
  | succ m ih =>
    exact ⟨ih.2, by
      rw [ChristoffelDarboux.chebU_deriv_succ_succ, ih.2, ih.1]
      rw [HankelBridge.chebU_eq_poly]
      -- derivative of U_{m+2} = derivative of (2X · U_{m+1} − U_m)
      rw [show (↑(m + 1 + 1) : ℤ) = (↑m : ℤ) + 2 from by push_cast; ring]
      rw [Chebyshev.U_add_two ℝ (↑m : ℤ)]
      simp only [derivative_sub, derivative_mul, derivative_ofNat, derivative_X,
                  eval_sub, eval_add, eval_mul, eval_ofNat, eval_X,
                  eval_zero, eval_one]
      push_cast; ring⟩

-- ═══════════════════════════════════════════════════════════════════
-- §1. Chebyshev root: U_{m+1} has IsRoot at cos θ
-- ═══════════════════════════════════════════════════════════════════

/-- The Chebyshev evaluation point: `x₀ = cos(π/(m+2))`. -/
noncomputable def x₀ (m : ℕ) : ℝ := cos (π / (↑m + 2))

/-- The angle `θ = π/(m+2)`. -/
noncomputable def θ (m : ℕ) : ℝ := π / (↑m + 2)

@[simp] theorem x₀_eq_cos_θ (m : ℕ) : x₀ m = cos (θ m) := rfl

/-- `x₀` relates to the threshold `α_m = 4x₀²`. -/
theorem α_eq_four_x₀_sq (m : ℕ) : UniversalScalingLaw.α m = 4 * x₀ m ^ 2 := by
  unfold UniversalScalingLaw.α x₀; ring

/-- `U_{m+1}(x₀) = 0`: the Chebyshev polynomial vanishes at the threshold.
    This is the **polynomial root** that drives the entire factorization. -/
theorem U_isRoot (m : ℕ) :
    (U ℝ (↑(m + 1) : ℤ)).IsRoot (x₀ m) := by
  rw [Polynomial.IsRoot, ← HankelBridge.chebU_eq_poly]
  exact ChristoffelDarboux.chebU_vanishes_at_root m

/-- `U_m(x₀) = 1`: the adjacent Chebyshev polynomial equals 1 at the root. -/
theorem U_at_vertex (m : ℕ) :
    (U ℝ (↑m : ℤ)).eval (x₀ m) = 1 := by
  rw [← HankelBridge.chebU_eq_poly]
  exact ChristoffelDarboux.chebU_at_root_vertex m

/-- `sin θ > 0` for the threshold angle. -/
theorem sin_θ_pos (m : ℕ) : 0 < sin (θ m) :=
  ChristoffelDarboux.sin_pi_div_pos m

/-- `x₀ > 0` for `m ≥ 1`. -/
theorem x₀_pos (m : ℕ) (hm : 0 < m) : 0 < x₀ m := by
  unfold x₀
  exact cos_pos_of_mem_Ioo ⟨by
    linarith [div_pos pi_pos (show (0:ℝ) < ↑m + 2 from by positivity),
              div_pos pi_pos two_pos],
    by rw [div_lt_div_iff₀ (show (0:ℝ) < ↑m + 2 from by positivity) two_pos]
       nlinarith [pi_pos, show (1:ℝ) ≤ ↑m from Nat.one_le_cast.mpr hm]⟩

-- ═══════════════════════════════════════════════════════════════════
-- §2. Root factoring: (X − C x₀) ∣ U_{m+1}
-- ═══════════════════════════════════════════════════════════════════

/-- `(X − C x₀)` divides `U_{m+1}` as polynomials over `ℝ`.
    This is the algebraic core: `dvd_iff_isRoot` turns a polynomial root
    into a divisibility statement, with no limits needed. -/
theorem X_sub_x₀_dvd_U (m : ℕ) :
    (X - C (x₀ m)) ∣ (U ℝ (↑(m + 1) : ℤ)) :=
  dvd_iff_isRoot.mpr (U_isRoot m)

/-- The quotient polynomial `Q_m = U_{m+1} /ₘ (X − x₀)`.
    This is well-defined since `(X − x₀)` is monic and divides `U_{m+1}`.
    We have `U_{m+1} = (X − x₀) · Q_m` as polynomials.

    **This is the algebraic replacement for the "slope" or "L'Hôpital" step:**
    instead of taking a limit of `U_{m+1}(x) / (x − x₀)`, we simply
    divide polynomials. -/
noncomputable def Q (m : ℕ) : Polynomial ℝ :=
  (U ℝ (↑(m + 1) : ℤ)) /ₘ (X - C (x₀ m))

/-- The factoring identity: `U_{m+1} = (X − x₀) · Q_m`. -/
theorem U_eq_factor_mul_Q (m : ℕ) :
    U ℝ (↑(m + 1) : ℤ) = (X - C (x₀ m)) * Q m := by
  rw [Q, mul_divByMonic_eq_iff_isRoot.mpr (U_isRoot m)]

-- ═══════════════════════════════════════════════════════════════════
-- §3. Quotient evaluation: Q_m(x₀) = U'_{m+1}(x₀)
-- ═══════════════════════════════════════════════════════════════════

/-- `Q_m(x₀) = U'_{m+1}(x₀)`: evaluating the quotient at the root gives the
    polynomial derivative. This is the algebraic fact underlying L'Hôpital:
    if `p = (X − a) · q`, then `p'(a) = q(a)`.

    Combined with the Christoffel–Darboux identity:
      `Q_m(x₀) = (m+2) / sin²θ`

    **Status**: the identity `p'(a) = q(a)` for simple roots needs a small
    Mathlib lemma (derivative of product + evaluation). -/
theorem Q_eval_eq_deriv (m : ℕ) :
    (Q m).eval (x₀ m) = (U ℝ (↑(m + 1) : ℤ)).derivative.eval (x₀ m) := by
  have hfact := U_eq_factor_mul_Q m
  -- U_{m+1} = (X - C x₀) * Q_m, so U'_{m+1} = Q_m + (X - C x₀) * Q'_m
  have hderiv : (U ℝ (↑(m + 1) : ℤ)).derivative =
      Q m + (X - C (x₀ m)) * (Q m).derivative := by
    rw [hfact, derivative_mul, derivative_X_sub_C, one_mul, add_comm]
  -- Evaluating at x₀: (X - C x₀) vanishes, leaving Q_m(x₀)
  rw [hderiv, eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero]

/-- **Bridge lemma.** The polynomial derivative of Chebyshev U evaluates to
    the same value as the evaluation-level algebraic derivative `chebU_deriv`.
    Both satisfy the same recurrence `D'(n+2) = 2U(n+1) + 2x·D'(n+1) − D'(n)`,
    so they agree by pair induction. -/
theorem U_derivative_eval_eq_chebU_deriv (n : ℕ) (x : ℝ) :
    (U ℝ (↑n : ℤ)).derivative.eval x = ChristoffelDarboux.chebU_deriv n x := by
  suffices h : ∀ k : ℕ,
    (U ℝ (↑k : ℤ)).derivative.eval x = ChristoffelDarboux.chebU_deriv k x ∧
    (U ℝ (↑(k + 1) : ℤ)).derivative.eval x = ChristoffelDarboux.chebU_deriv (k + 1) x
    from (h n).1
  intro k; induction k with
  | zero =>
    constructor
    · -- n = 0: U(0) = 1, derivative = 0
      simp [Polynomial.Chebyshev.U_zero, ChristoffelDarboux.chebU_deriv_zero]
    · -- n = 1: U(1) = 2X, derivative = 2
      simp [Polynomial.Chebyshev.U_one, derivative_mul, derivative_ofNat, derivative_X,
            ChristoffelDarboux.chebU_deriv_one]
  | succ m ih =>
    exact ⟨ih.2, by
      -- U(m+2) = 2X · U(m+1) - U(m), differentiate
      rw [show (↑(m + 1 + 1) : ℤ) = (↑m : ℤ) + 2 from by push_cast; ring,
          Polynomial.Chebyshev.U_add_two]
      simp only [derivative_sub, derivative_mul, derivative_ofNat, derivative_X,
                  eval_sub, eval_add, eval_mul, eval_ofNat, eval_X,
                  zero_mul, mul_one]
      -- Normalize ↑(m+1) to ↑m + 1 in the goal
      rw [show (↑(m + 1) : ℤ) = (↑m : ℤ) + 1 from by push_cast; ring] at ih
      rw [ih.1, ih.2]
      -- Bridge chebU_eq_poly for U evaluations (with cast normalization)
      conv_lhs => rw [show (↑m + 1 : ℤ) = ↑(m + 1) from by push_cast; ring]
      rw [← HankelBridge.chebU_eq_poly (m + 1) x]
      rw [ChristoffelDarboux.chebU_deriv_succ_succ]
      simp [eval_zero]⟩

/-- `Q_m(x₀) = (m+2) / sin²θ`: the explicit value. -/
theorem Q_eval_explicit (m : ℕ) :
    (Q m).eval (x₀ m) = (↑m + 2) / sin (θ m) ^ 2 := by
  rw [Q_eval_eq_deriv, U_derivative_eval_eq_chebU_deriv]
  exact ChristoffelDarboux.chebU_deriv_at_root m

/-- `Q_m(x₀) ≠ 0`: the quotient is nonzero at the root.
    Equivalently, `x₀` is a **simple** root of `U_{m+1}`.
    Proof: `Q_m(x₀) = (m+2)/sin²θ > 0`. -/
theorem Q_eval_ne_zero (m : ℕ) : (Q m).eval (x₀ m) ≠ 0 := by
  rw [Q_eval_explicit]
  exact ne_of_gt (div_pos (by positivity) (sq_pos_of_pos (sin_θ_pos m)))

-- ═══════════════════════════════════════════════════════════════════
-- §4. Algebraic first-order coefficient
-- ═══════════════════════════════════════════════════════════════════

/-- **Algebraic first-order coefficient.**

    In the Chebyshev variable `x = √λ/2`:
      `c₁ = U_m(x₀) / Q_m(x₀) = 1 / Q_m(x₀)`

    since `U_m(x₀) = 1`.

    Converting back to the `λ` variable requires the Jacobian `dλ/dx = 4x`,
    giving `c₁(λ) = 4x₀ · c₁(x) = 4x₀ / Q_m(x₀)`, which equals
    `first_order_coeff m` from `RemainderBound`. -/
noncomputable def c₁_chebyshev (m : ℕ) : ℝ :=
  (U ℝ (↑m : ℤ)).eval (x₀ m) / (Q m).eval (x₀ m)

/-- `c₁ = 1 / Q_m(x₀)` since `U_m(x₀) = 1`. -/
theorem c₁_eq_inv_Q (m : ℕ) :
    c₁_chebyshev m = 1 / (Q m).eval (x₀ m) := by
  unfold c₁_chebyshev; rw [U_at_vertex]

/-- `c₁ = sin²θ / (m+2)`: the explicit formula via `Q_m(x₀)`. -/
theorem c₁_explicit (m : ℕ) :
    c₁_chebyshev m = sin (θ m) ^ 2 / (↑m + 2) := by
  rw [c₁_eq_inv_Q, Q_eval_explicit]
  field_simp

-- ═══════════════════════════════════════════════════════════════════
-- §5. Algebraic recursion for all Lagrange coefficients
-- ═══════════════════════════════════════════════════════════════════

/-  The **polynomial Lagrange kernel** in the Chebyshev variable.

    `H_m(X) = U_m(X) / Q_m(X)`

    where `Q_m = U_{m+1} / (X − x₀)`. Since `Q_m(x₀) ≠ 0`, the
    ratio `H_m` is a well-defined formal power series at `x₀`.

    The n-th Lagrange coefficient is:
      `cₙ = (1/n) · [coeff of tⁿ⁻¹ in h(x₀ + t)ⁿ]`

    where `h_k` are the Taylor coefficients of `H_m` at `x₀`, computed
    by the **division recursion** from `Q_m · H_m = U_m`:
      `h_k = (u_k − Σ_{j<k} q_{k−j} · h_j) / q₀`

    Each `cₙ ∈ ℚ(cos θ, sin θ)` because `U_m`, `Q_m` have integer
    coefficients and the only denominator is `Q_m(x₀) = (m+2)/sin²θ`. -/

-- §5a. Power series infrastructure
-- ─────────────────────────────────

/-- `k`-fold derivative of a polynomial. -/
noncomputable def polyNthDeriv : ℕ → Polynomial ℝ → Polynomial ℝ
  | 0, p => p
  | k + 1, p => (polyNthDeriv k p).derivative

/-- Taylor coefficient of polynomial `p` at point `a`:
    `polyTaylorAt p a k = p⁽ᵏ⁾(a) / k!`. -/
noncomputable def polyTaylorAt (p : Polynomial ℝ) (a : ℝ) (k : ℕ) : ℝ :=
  (polyNthDeriv k p).eval a / ↑(Nat.factorial k)

@[simp] theorem polyTaylorAt_zero (p : Polynomial ℝ) (a : ℝ) :
    polyTaylorAt p a 0 = p.eval a := by
  simp [polyTaylorAt, polyNthDeriv]

/-- Cauchy product (discrete convolution) of two sequences. -/
noncomputable def cauchyMul (f g : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), f k * g (n - k)

/-- `n`-fold convolution power of a sequence:
    `convPow f 0 = δ₀`, `convPow f (n+1) = f * convPow f n`. -/
noncomputable def convPow (f : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, k => if k = 0 then 1 else 0
  | n + 1, k => cauchyMul f (convPow f n) k

theorem convPow_one_zero (f : ℕ → ℝ) : convPow f 1 0 = f 0 := by
  simp [convPow, cauchyMul]

-- §5b. Lagrange kernel coefficients
-- ──────────────────────────────────

/-- Taylor coefficients of the **Lagrange kernel** `H_m = U_m / Q_m` at `x₀`.

    From the identity `Q_m · H_m = U_m`, matching the `k`-th coefficient:
      `q₀ · h_k + Σ_{j<k} q_{k−j} · h_j = u_k`
    gives the recursion:
      `h_k = (u_k − Σ_{j<k} q_{k−j} · h_j) / q₀`

    Since `q₀ = Q_m(x₀) ≠ 0` (`Q_eval_ne_zero`), each `h_k` is well-defined. -/
noncomputable def hCoeff (m : ℕ) : ℕ → ℝ
  | 0 => (U ℝ (↑m : ℤ)).eval (x₀ m) / (Q m).eval (x₀ m)
  | k + 1 =>
    (polyTaylorAt (U ℝ (↑m : ℤ)) (x₀ m) (k + 1) -
     ∑ j : Fin (k + 1),
       polyTaylorAt (Q m) (x₀ m) (k + 1 - ↑j) * hCoeff m ↑j) /
    (Q m).eval (x₀ m)

theorem hCoeff_zero_eq (m : ℕ) : hCoeff m 0 = c₁_chebyshev m := by
  simp only [hCoeff.eq_1, c₁_chebyshev]

-- §5c. Lagrange inversion coefficients
-- ─────────────────────────────────────

/-- The `n`-th Taylor coefficient of `ψ` in the Chebyshev variable,
    computed via **Lagrange inversion**:

      `cₙ = (1/n) · [coeff of tⁿ⁻¹ in h(x₀ + t)ⁿ]`

    where `h_k = hCoeff m k` are the Taylor coefficients of the
    Lagrange kernel `H_m = U_m / Q_m` at `x₀`.

    - `c 0 = 0` (convention: `ψ(0) = x₀`)
    - `c 1 = h₀ = U_m(x₀) / Q_m(x₀) = sin²θ / (m+2)`
    - `c n` for `n ≥ 2`: `n`-fold convolution of `hCoeff`, degree `n−1` -/
noncomputable def taylorCoeffCheb (m : ℕ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => convPow (hCoeff m) (n + 1) n / ↑(n + 1)

/-- The `n = 1` coefficient agrees with `c₁_chebyshev`. -/
theorem taylorCoeffCheb_one (m : ℕ) :
    taylorCoeffCheb m 1 = c₁_chebyshev m := by
  show convPow (hCoeff m) 1 0 / (↑(1 : ℕ) : ℝ) = c₁_chebyshev m
  rw [convPow_one_zero, hCoeff_zero_eq, Nat.cast_one, div_one]

-- ═══════════════════════════════════════════════════════════════════
-- §6. Connection to the analytic module
-- ═══════════════════════════════════════════════════════════════════

/-- The algebraic `c₁` equals the analytic `first_order_coeff` from
    `RemainderBound`, up to the Jacobian factor from `λ = 4x²`.

    `first_order_coeff m = 4 sin²θ / (m+2) = 4 · c₁_chebyshev m`

    The factor 4 comes from the Jacobian of the change of variable
    `λ = 4x²`: the `λ`-derivative of the implicit function is 4 times
    the `x`-derivative at `x₀ = cos θ`. -/
theorem c₁_eq_first_order_coeff (m : ℕ) (hm : 0 < m) :
    RemainderBound.first_order_coeff m = 4 * c₁_chebyshev m := by
  rw [c₁_explicit]
  -- LHS = first_order_coeff m, RHS = 4 * sin²θ / (m+2)
  rw [RemainderBound.first_order_coeff_eq m hm]
  unfold SpectralGeometric.root_amplitude_sq
  simp only [θ]
  ring

-- ═══════════════════════════════════════════════════════════════════
-- §7. Spectral partial fraction of the Chebyshev resolvent
-- ═══════════════════════════════════════════════════════════════════

/-  **Uniform partial-fraction decomposition.**

    The ratio of consecutive Chebyshev U polynomials has a remarkable
    partial-fraction expansion where **every residue has the same form**:

      `U_m(x) / U_{m+1}(x) = (1/(m+2)) Σ_{j=1}^{m+1} sin²(jπ/(m+2)) / (x − cos(jπ/(m+2)))`

    This is the **spectral decomposition** of the resolvent of the
    `(m+1) × (m+1)` tridiagonal matrix with `2x` on the diagonal and
    `−1` on the off-diagonals.

    **Why uniform?**  The residue at the root `ξ_j = cos(jπ/(m+2))` of `U_{m+1}` is:

      `Res = U_m(ξ_j) / U'_{m+1}(ξ_j)`

    Using the trigonometric evaluations:
    - `U_m(cos(jπ/p)) = sin((m+1)jπ/p)/sin(jπ/p) = (−1)^{j+1}`
    - `U'_{m+1}(cos(jπ/p)) = (−1)^{j+1} · p / sin²(jπ/p)`

    The signs cancel:  `Res = sin²(jπ/p) / p`.

    **Consistency check**: `Σ Res = (1/p) Σ sin²(jπ/p) = (1/p)(p/2) = 1/2`,
    matching the leading coefficient ratio `2^m / (2^{m+1} · x) → 1/(2x)` at infinity.

    **Consequence for the Lagrange kernel.**  Since `H_m = U_m/Q_m = (x−x₀)·U_m/U_{m+1}`,
    the Taylor coefficients `hCoeff m k` decompose as:

      `h_k = (1/(m+2)) Σ_{j=2}^{m+1} sin²(jπ/(m+2)) / (cos(jπ/(m+2)) − cos(π/(m+2)))^k`

    Each `h_k` is a **finite sum of geometric progressions** in the spectral
    variable `1/(cos(jπ/p) − cos(π/p))`.  The bases live in the maximal real
    subfield of the cyclotomic field `ℚ(ζ_{2(m+2)})`. -/

/-- `U_{m+1}` vanishes at all roots `cos(jπ/(m+2))` for `1 ≤ j ≤ m+1`.
    Generalises `chebU_vanishes_at_root` (which is the `j = 1` case). -/
private lemma sin_jpi_div_pos (m j : ℕ) (hj : 1 ≤ j) (hj' : j ≤ m + 1) :
    0 < sin (↑j * π / (↑m + 2)) := by
  apply sin_pos_of_pos_of_lt_pi
  · positivity
  · rw [div_lt_iff₀ (show (0 : ℝ) < ↑m + 2 from by positivity)]
    have : (↑j : ℝ) ≤ ↑m + 1 := by exact_mod_cast hj'
    nlinarith [pi_pos]

theorem chebU_vanishes_at_general_root (m j : ℕ) (hj : 1 ≤ j) (hj' : j ≤ m + 1) :
    ChristoffelDarboux.chebU (m + 1) (cos (↑j * π / (↑m + 2))) = 0 := by
  have hsin : sin (↑j * π / (↑m + 2)) ≠ 0 := ne_of_gt (sin_jpi_div_pos m j hj hj')
  rw [ChristoffelDarboux.chebU_cos _ _ hsin]
  rw [show (↑(m + 1) + 1) * (↑j * π / (↑m + 2)) = ↑j * π from by push_cast; field_simp; ring]
  simp [sin_nat_mul_pi]

/-- `U_m` evaluated at `cos(jπ/(m+2))` equals `(-1)^{j+1}`.
    Uses `sin((m+1)·jπ/(m+2)) = sin(jπ − jπ/(m+2)) = (-1)^{j+1} sin(jπ/(m+2))`. -/
theorem chebU_at_general_root (m j : ℕ) (hj : 1 ≤ j) (hj' : j ≤ m + 1) :
    ChristoffelDarboux.chebU m (cos (↑j * π / (↑m + 2))) = (-1 : ℝ) ^ (j + 1) := by
  have hsin : sin (↑j * π / (↑m + 2)) ≠ 0 := ne_of_gt (sin_jpi_div_pos m j hj hj')
  rw [ChristoffelDarboux.chebU_cos _ _ hsin]
  have harg : (↑m + 1) * (↑j * π / (↑m + 2)) = ↑j * π - ↑j * π / (↑m + 2) := by
    field_simp; ring
  rw [harg, sin_sub, sin_nat_mul_pi, cos_nat_mul_pi]
  field_simp
  ring

/-- Generalised cosine sum: `Σ_{k=0}^{n-1} cos(2jkπ/n) = 0` when `1 ≤ j < n`.
    Same telescoping as `cos_sum_eq_zero` with frequency `j`. -/
private lemma cos_sum_general (n j : ℕ) (hn : 2 ≤ n) (hj : 1 ≤ j) (hj' : j < n) :
    ∑ k ∈ Finset.range n, cos (2 * ↑j * ↑k * π / ↑n) = 0 := by
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
  have hsin_pos : 0 < sin (↑j * π / ↑n) := by
    apply sin_pos_of_pos_of_lt_pi
    · positivity
    · rw [div_lt_iff₀ hn_pos]
      have : (↑j : ℝ) < ↑n := by exact_mod_cast hj'
      nlinarith [pi_pos]
  suffices hmul : 2 * sin (↑j * π / ↑n) *
      ∑ k ∈ Finset.range n, cos (2 * ↑j * ↑k * π / ↑n) = 0 by
    exact (mul_eq_zero.mp hmul).resolve_left (ne_of_gt (by positivity))
  rw [Finset.mul_sum]
  -- Telescoping: 2sin(jπ/n)·cos(2jkπ/n) = g(k+1) − g(k)
  -- where g(k) = sin((2jk−j)π/n). Uses product-to-sum: 2cos(a)sin(b) = sin(a+b) - sin(a-b).
  set g : ℕ → ℝ := fun k => sin ((2 * ↑j * ↑k - ↑j) * π / ↑n)
  have two_cos_sin : ∀ a b : ℝ, 2 * cos a * sin b = sin (a + b) - sin (a - b) := by
    intro a b; rw [sin_add, sin_sub]; ring
  have term_eq : ∀ k ∈ Finset.range n,
      2 * sin (↑j * π / ↑n) * cos (2 * ↑j * ↑k * π / ↑n) = g (k + 1) - g k := by
    intro k _; simp only [g]
    have h := two_cos_sin (2 * ↑j * ↑k * π / ↑n) (↑j * π / ↑n)
    rw [show 2 * ↑j * ↑k * π / ↑n + ↑j * π / ↑n =
      (2 * ↑j * (↑k + 1) - ↑j) * π / ↑n from by ring] at h
    rw [show 2 * ↑j * ↑k * π / ↑n - ↑j * π / ↑n =
      (2 * ↑j * ↑k - ↑j) * π / ↑n from by ring] at h
    rw [show (↑(k + 1) : ℝ) = ↑k + 1 from by push_cast; ring]
    linarith
  rw [Finset.sum_congr rfl term_eq, Finset.sum_range_sub]
  -- g(n) − g(0): sin((2jn−j)π/n) − sin(−jπ/n)
  simp only [g, Nat.cast_zero, mul_zero, zero_sub]
  -- sin((2jn−j)π/n) = sin(2jπ − jπ/n) = −sin(jπ/n)  [by sin_nat_mul_two_pi_sub]
  have h1 : sin ((2 * ↑j * ↑n - ↑j) * π / ↑n) = -sin (↑j * π / ↑n) := by
    have h := sin_nat_mul_two_pi_sub (↑j * π / ↑n) j
    convert h using 1; field_simp
  rw [h1, show (-↑j) * π / ↑n = -(↑j * π / ↑n) from by ring, sin_neg, sub_self]

/-- Generalised shifted cosine sum:
    `Σ_{k=0}^m cos(2j(k+1)π/(m+2)) = -1` for `1 ≤ j ≤ m+1`. -/
private lemma cos_sum_shifted_general (m j : ℕ) (hj : 1 ≤ j) (hj' : j ≤ m + 1) :
    ∑ k ∈ Finset.range (m + 1), cos (2 * ↑j * (↑k + 1) * π / (↑m + 2)) = -1 := by
  have h := cos_sum_general (m + 2) j (by omega) hj (by omega)
  simp only [show (↑(m + 2) : ℝ) = ↑m + 2 from by push_cast; ring] at h
  rw [Finset.sum_range_succ'] at h
  simp only [Nat.cast_zero, mul_zero, zero_mul, zero_div, cos_zero] at h
  have : ∑ k ∈ Finset.range (m + 1), cos (2 * ↑j * (↑k + 1) * π / (↑m + 2)) =
      ∑ k ∈ Finset.range (m + 1), cos (2 * ↑j * ↑(k + 1) * π / (↑m + 2)) := by
    apply Finset.sum_congr rfl; intro k _; congr 1; push_cast; ring
  rw [this]; linarith

/-- Generalised sine-square sum:
    `Σ_{k=0}^m sin²((k+1)jπ/(m+2)) = (m+2)/2` for `1 ≤ j ≤ m+1`. -/
private lemma sin_sq_sum_general (m j : ℕ) (hj : 1 ≤ j) (hj' : j ≤ m + 1) :
    ∑ k ∈ Finset.range (m + 1), sin ((↑k + 1) * ↑j * π / (↑m + 2)) ^ 2 =
    (↑m + 2) / 2 := by
  have sq_eq : ∀ k ∈ Finset.range (m + 1),
      sin ((↑k + 1) * ↑j * π / (↑m + 2 : ℝ)) ^ 2 =
      (1 - cos (2 * ↑j * (↑k + 1) * π / (↑m + 2))) / 2 := by
    intro k _
    have h := cos_two_mul ((↑k + 1) * ↑j * π / (↑m + 2 : ℝ))
    have := sin_sq_add_cos_sq ((↑k + 1) * ↑j * π / (↑m + 2 : ℝ))
    rw [show 2 * ((↑k + 1) * ↑j * π / (↑m + 2 : ℝ)) =
      2 * ↑j * (↑k + 1) * π / (↑m + 2) from by ring] at h
    nlinarith
  rw [Finset.sum_congr rfl sq_eq, ← Finset.sum_div, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [cos_sum_shifted_general m j hj hj']
  push_cast; ring

/-- Generalised sum of Chebyshev U squares at any root of `U_{m+1}`:
    `Σ_{k=0}^m U_k(cos(jπ/(m+2)))² = (m+2)/(2sin²(jπ/(m+2)))`. -/
private lemma sum_chebU_sq_general (m j : ℕ) (hj : 1 ≤ j) (hj' : j ≤ m + 1) :
    ∑ k ∈ Finset.range (m + 1),
      ChristoffelDarboux.chebU k (cos (↑j * π / (↑m + 2))) ^ 2 =
    (↑m + 2) / (2 * (sin (↑j * π / (↑m + 2))) ^ 2) := by
  set θ := ↑j * π / (↑m + 2 : ℝ)
  have hsin : sin θ ≠ 0 := ne_of_gt (sin_jpi_div_pos m j hj hj')
  have step : ∀ k ∈ Finset.range (m + 1),
      ChristoffelDarboux.chebU k (cos θ) ^ 2 = sin ((↑k + 1) * θ) ^ 2 / sin θ ^ 2 := by
    intro k _; rw [ChristoffelDarboux.chebU_cos k θ hsin, div_pow]
  rw [Finset.sum_congr rfl step, ← Finset.sum_div]
  -- The numerator sum: Σ sin²((k+1)θ) where θ = jπ/(m+2)
  -- = Σ sin²((k+1)jπ/(m+2)) = (m+2)/2
  have hconv : ∀ k ∈ Finset.range (m + 1),
      sin ((↑k + 1) * θ) ^ 2 = sin ((↑k + 1) * ↑j * π / (↑m + 2)) ^ 2 := by
    intro k _; congr 1; simp only [θ]; ring
  rw [Finset.sum_congr rfl hconv, sin_sq_sum_general m j hj hj']
  ring

theorem spectral_residue (m : ℕ) (j : ℕ) (hj : 1 ≤ j) (hj' : j ≤ m + 1) :
    let p := m + 2
    let ξ := cos (↑j * π / ↑p)
    ChristoffelDarboux.chebU m ξ /
      ChristoffelDarboux.chebU_deriv (m + 1) ξ =
    sin (↑j * π / ↑p) ^ 2 / ↑p := by
  -- Use confluent_cd at ξ = cos(jπ/(m+2)) where U_{m+1}(ξ) = 0
  set ξ := cos (↑j * π / (↑m + 2 : ℝ))
  have hvan := chebU_vanishes_at_general_root m j hj hj'
  have hcd := ChristoffelDarboux.confluent_cd m ξ
  rw [hvan, zero_mul, sub_zero] at hcd
  -- hcd: chebU m ξ * chebU_deriv (m+1) ξ = 2 * Σ chebU k ξ ^ 2
  rw [sum_chebU_sq_general m j hj hj'] at hcd
  -- hcd: chebU m ξ * chebU_deriv (m+1) ξ = 2 * ((m+2) / (2 * sin(jπ/(m+2))²))
  -- = (m+2) / sin²(jπ/(m+2))
  have hsin : sin (↑j * π / (↑m + 2 : ℝ)) ≠ 0 := ne_of_gt (sin_jpi_div_pos m j hj hj')
  have heval := chebU_at_general_root m j hj hj'
  have hUm_ne : ChristoffelDarboux.chebU m ξ ≠ 0 := by
    rw [heval]; exact pow_ne_zero _ (by norm_num)
  -- hcd simplifies to: U_m · U' = (m+2) / sin²
  have key : ChristoffelDarboux.chebU m ξ *
      ChristoffelDarboux.chebU_deriv (m + 1) ξ =
      (↑m + 2) / sin (↑j * π / (↑m + 2)) ^ 2 := by
    have : 2 * ((↑m + 2) / (2 * sin (↑j * π / (↑m + 2)) ^ 2)) =
        (↑m + 2) / sin (↑j * π / (↑m + 2)) ^ 2 := by field_simp
    linarith
  -- U_m² = 1 (since U_m = (-1)^{j+1})
  have hUm_sq : ChristoffelDarboux.chebU m ξ ^ 2 = 1 := by
    rw [heval]
    rcases Nat.even_or_odd (j + 1) with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [hk]; simp
    · rw [hk]; simp [pow_succ]
  -- U' ≠ 0 (from key and U_m ≠ 0)
  have hU'_ne : ChristoffelDarboux.chebU_deriv (m + 1) ξ ≠ 0 := by
    intro h; rw [h, mul_zero] at key
    have : (0 : ℝ) < (↑m + 2) / sin (↑j * π / (↑m + 2)) ^ 2 :=
      div_pos (by positivity) (sq_pos_of_ne_zero hsin)
    linarith
  -- Unfold the let bindings and normalise ↑(m+2) → ↑m + 2
  simp only
  rw [show (↑(m + 2) : ℝ) = ↑m + 2 from by push_cast; ring]
  -- Goal: U_m(ξ) / U'(ξ) = sin² / (m+2)
  -- Strategy: show U_m(ξ)² / (U_m(ξ) · U'(ξ)) = sin²/(m+2), using U_m² = 1 and key.
  rw [show ChristoffelDarboux.chebU m ξ / ChristoffelDarboux.chebU_deriv (m + 1) ξ =
    ChristoffelDarboux.chebU m ξ ^ 2 /
      (ChristoffelDarboux.chebU m ξ * ChristoffelDarboux.chebU_deriv (m + 1) ξ) from by
    rw [sq]; field_simp]
  rw [hUm_sq, key, one_div_div]

/-- **Spectral form of `hCoeff`.**

    The Lagrange kernel Taylor coefficients satisfy:

      `hCoeff m 0 = sin²(π/(m+2)) / (m+2)`    (= c₁_chebyshev)
      `hCoeff m k = −(1/(m+2)) Σ_{j=2}^{m+1} sin²(jπ/(m+2)) · γ_j^k`    (k ≥ 1)

    where `γ_j = −1/(cos(π/(m+2)) − cos(jπ/(m+2)))`.

    This decomposes each `h_k` as a **finite sum of exponentials** in `k`,
    whose bases `γ_j` are explicit trigonometric constants.

    **Key consequence**: The `hCoeff` recursion (§5b) and this spectral form
    compute the same sequence.  The spectral form avoids the recursion entirely:
    each `h_k` is directly computable from the spectral data. -/
noncomputable def hCoeffSpectral (m : ℕ) (k : ℕ) : ℝ :=
  let p : ℝ := ↑m + 2
  if k = 0 then
    sin (π / p) ^ 2 / p
  else
    -(1 / p) * ∑ j ∈ Finset.Icc 2 (m + 1),
      sin (↑j * π / p) ^ 2 * (-1 / (cos (π / p) - cos (↑j * π / p))) ^ k

-- ═══════════════════════════════════════════════════════════════════
-- §8. Abel–Ruffini: why the algebraic approach is canonical
-- ═══════════════════════════════════════════════════════════════════

/-  **Abel–Ruffini obstruction.**

    For `m ≤ 2`, `U_{m+1}` has degree ≤ 3, so the implicit function
    `ψ(δ)` is expressible in radicals.

    For `m ≥ 3`, `U_{m+1}` has degree ≥ 4 in `x`, and the equation
    `2x · (x − x₀) · Q_m(x) = δ · U_m(x)` has degree ≥ 5 in `x`.
    By Abel–Ruffini, there is no closed-form radical expression for `ψ(δ)`.

    The **algebraic Lagrange recursion** (matching polynomial coefficients)
    is therefore the canonical way to compute `cₙ` for `m ≥ 3`. -/

end LagrangeAlgebraic
