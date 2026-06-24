import PptFactorization.General

/-!
# Step 6: Leading-order expansion of `detB_m(α·d₁, d₁)`

Concrete instantiation of Step 6 for `m = 1, 2`.  The goal is the
paper's identity

    detB_m(α·d₁, d₁) = d₁^{N(m)} · (d_{m+1}(α) − δ·d_m(α) + δ·H_m(δ, α))

where `δ := 1/d₁²` is the small parameter inherited from the
`ψ(1/d₁²)` parameterisation in `lambda_star_asymptotic`, and `H_m` is
the residual ("higher-order") piece.

This file takes the simplest honest route (option **(b) + (i)** in the
planning conversation):

* **(b)** We restrict to `m = 1, 2`, where `detB₁` and `detB₂` already
  exist in `General` with closed-form factorisations
  (`detB₁_eq`, `detB₂_eq`).  No generic `detB_m` is required.

* **(i)** `H_m` is defined by subtraction, so the decomposition
  identity is a tautology (a `ring` fact).  The research content is
  the **closed form** of `detB_m(α·d₁, d₁)` as a polynomial in
  `(α, δ)`, which is what we prove here.  Any subsequent bound on
  `H_m` — or any claim that `H_m(0, α) = 0` — is an orthogonal
  statement to be developed on top.

## Main results

* `detB₁_at_alpha` : `detB₁(α·d₁, d₁) = α² · ((α − 1) + δ)`.
* `detB₂_at_alpha` : `detB₂(α·d₁, d₁) = α⁴ · (α(α−2) + (3α−4)·δ + (4−α)·δ²)`.
* `detB₁_leading_vanishes` : at the A-type threshold `α = 1 = α_A(1)`,
  the `δ⁰` part vanishes.
* `detB₂_leading_vanishes` : at the A-type threshold `α = 2 = α_A(2)`,
  the `δ⁰` part vanishes.
* `detB₁_decomposition`, `detB₂_decomposition` : the tautological
  `(d_{m+1} − δ·d_m + δ·H_m)` rewriting, parameterised over a
  user-supplied sequence `dSeq` so the caller chooses the naming of
  the "`d_k(α)`" factors.

## Remark on `N(m)`

With `δ := 1/d₁²`, the d₁-dependence of `detB_m(α·d₁, d₁)` is
**entirely absorbed into δ** — that is, `N(m) = 0` under this
convention.  The paper's `d₁^{N(m)}` prefactor corresponds to pulling
α-powers (`α²`, `α⁴`, …) into the `d_{m+1}(α)` factor; that is a
naming choice handled by the caller via `dSeq`, not an algebraic
identity this file needs to commit to.
-/

namespace PptFactorization.Step6

open General

-- ═══════════════════════════════════════════════════════════════════
-- §1. Closed form of `detB_m(α·d₁, d₁)` as a polynomial in `(α, δ)`
-- ═══════════════════════════════════════════════════════════════════

/-- **Leading-order expansion, m = 1.**

    `detB₁(α·d₁, d₁) = α² · ((α − 1) + 1/d₁²)`.

    Setting `δ := 1/d₁²`, this reads
    `detB₁(α·d₁, d₁) = α²·(α − 1) + δ·α²`.

    The `δ⁰` term `α²·(α − 1)` vanishes at the A-type threshold
    `α = α_A(1) = 4cos²(π/3) = 1`. -/
theorem detB₁_at_alpha (α d₁ : ℝ) (hd : d₁ ≠ 0) :
    detB₁ (α * d₁) d₁ = α ^ 2 * ((α - 1) + 1 / d₁ ^ 2) := by
  rw [detB₁_eq _ _ hd]
  field_simp

/-- **Leading-order expansion, m = 2.**

    `detB₂(α·d₁, d₁) = α⁴ · (α(α−2) + (3α−4)/d₁² + (4−α)/d₁⁴)`.

    Setting `δ := 1/d₁²`, this reads
    `detB₂(α·d₁, d₁) = α⁵·(α − 2) + δ·α⁴·(3α − 4) + δ²·α⁴·(4 − α)`.

    The `δ⁰` term `α⁵·(α − 2)` vanishes at the A-type threshold
    `α = α_A(2) = 4cos²(π/4) = 2`. -/
theorem detB₂_at_alpha (α d₁ : ℝ) (hd : d₁ ≠ 0) :
    detB₂ (α * d₁) d₁ =
      α ^ 4 * (α * (α - 2) + (3 * α - 4) / d₁ ^ 2 + (4 - α) / d₁ ^ 4) := by
  rw [detB₂_eq _ _ hd]
  simp only [Q₂]
  field_simp
  ring

-- ═══════════════════════════════════════════════════════════════════
-- §2. Leading-order vanishing at the A-type thresholds
-- ═══════════════════════════════════════════════════════════════════

/-- **m = 1.**  At `α = 1`, the full value of `detB₁(α·d₁, d₁)` reduces
    to the pure `δ = 1/d₁²` correction, confirming that the `δ⁰` part
    vanishes at the A-type threshold `α_A(1) = 1`. -/
theorem detB₁_leading_vanishes (d₁ : ℝ) (hd : d₁ ≠ 0) :
    detB₁ (1 * d₁) d₁ = 1 / d₁ ^ 2 := by
  rw [detB₁_at_alpha 1 d₁ hd]; ring

/-- **m = 2.**  At `α = 2`, the full value of `detB₂(α·d₁, d₁)` reduces
    to `32/d₁² + 32/d₁⁴`, confirming that the `δ⁰` part vanishes at
    the A-type threshold `α_A(2) = 2`. -/
theorem detB₂_leading_vanishes (d₁ : ℝ) (hd : d₁ ≠ 0) :
    detB₂ (2 * d₁) d₁ = 32 / d₁ ^ 2 + 32 / d₁ ^ 4 := by
  rw [detB₂_at_alpha 2 d₁ hd]; ring

-- ═══════════════════════════════════════════════════════════════════
-- §3. The `(d_{m+1} − δ·d_m + δ·H_m)` decomposition  (option (i))
-- ═══════════════════════════════════════════════════════════════════

/-- **Residual `H_m` defined by subtraction.**

    Given any user-supplied sequence `dSeq : ℕ → ℝ → ℝ` (typically a
    Chebyshev-like sequence `d_k(α)`), define `residualH m dSeq δ α`
    to be whatever makes the decomposition

        P_m(δ, α) = d_{m+1}(α) − δ·d_m(α) + δ·H_m(δ, α)

    hold, where `P_m(δ, α)` is the normalised polynomial form of
    `detB_m(α·d₁, d₁)` with `δ := 1/d₁²`.

    Since `H_m` is defined by subtraction, the decomposition identity
    (below) is tautological; the **content** lives in §1 (the closed
    forms) and in any further analysis of `H_m` the user wishes to
    develop (e.g. `H_m(0, α) = 0`, polynomial bounds, etc.).  -/
noncomputable def residualH (m : ℕ) (dSeq : ℕ → ℝ → ℝ) (P : ℝ → ℝ → ℝ)
    (δ α : ℝ) : ℝ :=
  if δ = 0 then 0
  else (P δ α - dSeq (m + 1) α + δ * dSeq m α) / δ

/-- **Decomposition identity.**  For any `δ ≠ 0`, any choice of
    `dSeq`, and any `P`,

        P(δ, α) = dSeq (m+1) α − δ · dSeq m α + δ · residualH m dSeq P δ α.

    Tautological — follows from the definition of `residualH`. -/
theorem residualH_decomp (m : ℕ) (dSeq : ℕ → ℝ → ℝ) (P : ℝ → ℝ → ℝ)
    (δ α : ℝ) (hδ : δ ≠ 0) :
    P δ α = dSeq (m + 1) α - δ * dSeq m α + δ * residualH m dSeq P δ α := by
  unfold residualH
  rw [if_neg hδ]
  field_simp
  ring

/-- The m=1 normalised polynomial `P₁(δ, α) = α²·((α−1) + δ)`. -/
noncomputable def P₁ : ℝ → ℝ → ℝ := fun δ α => α ^ 2 * ((α - 1) + δ)

/-- **m = 1 packaged decomposition.**  Combines `detB₁_at_alpha` with
    the tautological `residualH_decomp` at `δ = 1/d₁²`.  The caller
    chooses `dSeq` to fix the naming of `d_2(α)` and `d_1(α)`; the
    residual `H_1` is determined. -/
theorem detB₁_decomposition (dSeq : ℕ → ℝ → ℝ) (α d₁ : ℝ) (hd : d₁ ≠ 0) :
    detB₁ (α * d₁) d₁ =
      dSeq 2 α - (1 / d₁ ^ 2) * dSeq 1 α
        + (1 / d₁ ^ 2) * residualH 1 dSeq P₁ (1 / d₁ ^ 2) α := by
  have hδ : (1 : ℝ) / d₁ ^ 2 ≠ 0 :=
    div_ne_zero one_ne_zero (pow_ne_zero 2 hd)
  rw [detB₁_at_alpha α d₁ hd]
  have h := residualH_decomp 1 dSeq P₁ (1 / d₁ ^ 2) α hδ
  simpa [P₁] using h

/-- The m=2 normalised polynomial
    `P₂(δ, α) = α⁴·(α(α−2) + (3α−4)·δ + (4−α)·δ²)`. -/
noncomputable def P₂ : ℝ → ℝ → ℝ := fun δ α =>
  α ^ 4 * (α * (α - 2) + (3 * α - 4) * δ + (4 - α) * δ ^ 2)

/-- **m = 2 packaged decomposition.**  Combines `detB₂_at_alpha` with
    the tautological `residualH_decomp` at `δ = 1/d₁²`. -/
theorem detB₂_decomposition (dSeq : ℕ → ℝ → ℝ) (α d₁ : ℝ) (hd : d₁ ≠ 0) :
    detB₂ (α * d₁) d₁ =
      dSeq 3 α - (1 / d₁ ^ 2) * dSeq 2 α
        + (1 / d₁ ^ 2) * residualH 2 dSeq P₂ (1 / d₁ ^ 2) α := by
  have hδ : (1 : ℝ) / d₁ ^ 2 ≠ 0 :=
    div_ne_zero one_ne_zero (pow_ne_zero 2 hd)
  rw [detB₂_at_alpha α d₁ hd]
  have hP : P₂ (1 / d₁ ^ 2) α =
      α ^ 4 * (α * (α - 2) + (3 * α - 4) / d₁ ^ 2 + (4 - α) / d₁ ^ 4) := by
    unfold P₂
    field_simp
  rw [← hP]
  exact residualH_decomp 2 dSeq P₂ (1 / d₁ ^ 2) α hδ

end PptFactorization.Step6
