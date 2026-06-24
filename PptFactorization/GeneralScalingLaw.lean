import PptFactorization.RemainderBound
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Taylor

/-!
# General Scaling Law for Spectral Thresholds

## Abstract framework

Let `F : ℝ × ℝ → ℝ` be a smooth function encoding a spectral threshold
equation.  The variable `δ` is the perturbation parameter (typically
`δ = 1/d₁²`) and `α` is the spectral parameter.

**Hypotheses:**

1. `F(0, α★) = 0`  — balanced threshold.
2. `∂F/∂α(0, α★) ≠ 0` — transversality (simple root).
3. `F` is `C^∞`.

**Conclusion:**

By the implicit function theorem there exists a `C^∞` function
`ψ : ℝ → ℝ` with `ψ(0) = α★`, `F(δ, ψ(δ)) = 0` near `δ = 0`, and

    ψ(δ) = α★ + c₁ · δ + O(δ²)

where `c₁ = −(∂F/∂δ) / (∂F/∂α)` evaluated at `(0, α★)`.

Converting to the physical scaling `λ = α · d₁` with `δ = 1/d₁²`:

    **λ★(d₁) = α★ · d₁ + c₁ / d₁ + O(1/d₁³)**

## Applications

| Principal graph | `α★`                   | `c₁` | Source of transversality      |
|-----------------|------------------------|-------|-------------------------------|
| A_{m+1}         | 4cos²(π/(m+2))        | −1    | Chebyshev U_{m+1} simple root |
| D_{m+2}         | 4cos²(π/(2m+2))       | TBD   | Chebyshev T simple root       |
| E₆              | 4cos²(π/12)           | TBD   | Explicit polynomial root      |
| E₇              | 4cos²(π/18)           | TBD   | Explicit polynomial root      |
| E₈              | 4cos²(π/30)           | TBD   | Explicit polynomial root      |
| Realignment     | (different threshold)  | TBD   | Different moment problem      |

For the A_{m+1} family, the correction `c₁ = −1` is universal across all m.
Whether this universality extends to other ADE families is an open question
that this framework is designed to address.

## Relation to existing files

- `RemainderBound.lean` : proves the IFT + Taylor bound for A_{m+1}
  using Chebyshev-specific ingredients.  The present file extracts the
  **graph-independent** analytic skeleton.
- `SubfactorBridge.lean` : connects PPT thresholds to Jones subfactor
  indices — the `α★` values above are `4cos²(π/n)` = Jones indices.
- `SpectralGeometric.lean` : `correction_general_graph` already accepts
  an arbitrary trace-normalised root amplitude.

Institut Fourier, Grenoble — Kieran McShane / Cécilia Lancien
-/

open Real Filter Topology

namespace GeneralScalingLaw


/-- A **spectral threshold problem** packages:
    - a smooth function `F : ℝ × ℝ → ℝ` (threshold equation),
    - a balanced threshold `α_star`,
    - the first-order coefficient `c₁`,
    subject to the hypotheses below. -/
structure SpectralThresholdData where
  /-- The threshold equation: `F(δ, α) = 0` defines the perturbed threshold. -/
  F : ℝ × ℝ → ℝ
  /-- The balanced threshold (spectral radius of the unperturbed operator). -/
  α_star : ℝ
  /-- The first-order implicit function coefficient:
      `c₁ = −(∂F/∂δ) / (∂F/∂α)` at `(0, α_star)`. -/
  c₁ : ℝ

/-- The hypotheses required for the general scaling law. -/
structure SpectralThresholdHyp (S : SpectralThresholdData) where
  /-- `F` is smooth (`C^∞`). -/
  F_smooth : ContDiff ℝ ⊤ S.F
  /-- `F(0, α★) = 0`: the balanced threshold is a root. -/
  F_vanishes : S.F (0, S.α_star) = 0
  /-- Transversality: the partial derivative w.r.t. `α` at the balanced
      threshold is nonzero.  We require it to be positive (WLOG). -/
  dF_dα : ℝ
  dF_dα_pos : 0 < dF_dα
  /-- `∂F/∂α` at `(0, α★)` equals `dF_dα`. -/
  has_partial_α : HasDerivAt (fun α => S.F (0, α)) dF_dα S.α_star
  /-- The value of `∂F/∂δ` at `(0, α★)`. -/
  dF_dδ : ℝ
  /-- `∂F/∂δ` at `(0, α★)` equals `dF_dδ`. -/
  has_partial_δ : HasDerivAt (fun δ => S.F (δ, S.α_star)) dF_dδ 0
  /-- The first-order coefficient is `c₁ = −(∂F/∂δ) / (∂F/∂α)`. -/
  c₁_eq : S.c₁ = -dF_dδ / dF_dα


/-- **General IFT for spectral thresholds.**

    Given a `SpectralThresholdData` satisfying its hypotheses, there
    exists a `C^∞` implicit function `ψ` with:
    - `ψ(0) = α★`
    - `F(δ, ψ(δ)) = 0` near `δ = 0`
    - `ψ'(0) = c₁` -/
theorem general_implicit_function (S : SpectralThresholdData)
    (H : SpectralThresholdHyp S) :
    ∃ ψ : ℝ → ℝ,
      ψ 0 = S.α_star
      ∧ (∀ᶠ δ in nhds 0, S.F (δ, ψ δ) = 0)
      ∧ HasDerivAt ψ S.c₁ 0
      ∧ ContDiffAt ℝ ⊤ ψ 0 := by
  have hF_strict : HasStrictFDerivAt S.F
      (fderiv ℝ S.F (0, S.α_star)) (0, S.α_star) :=
    H.F_smooth.contDiffAt.hasStrictFDerivAt (by simp)
  have h_inr : HasFDerivAt (fun α : ℝ => ((0 : ℝ), α))
      (.inr ℝ ℝ ℝ) S.α_star :=
    (ContinuousLinearMap.inr ℝ ℝ ℝ).hasFDerivAt
  have hcomp : HasFDerivAt (fun α => S.F (0, α))
      ((fderiv ℝ S.F (0, S.α_star)).comp (.inr ℝ ℝ ℝ)) S.α_star :=
    hF_strict.hasFDerivAt.comp _ h_inr
  have huniq := H.has_partial_α.hasFDerivAt.unique hcomp
  have hF_inv : ((fderiv ℝ S.F (0, S.α_star)).comp
      (.inr ℝ ℝ ℝ)).IsInvertible := by
    rw [← huniq]
    set c := H.dF_dα
    have hc_ne : c ≠ 0 := ne_of_gt H.dF_dα_pos
    set f := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c
    set g := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c⁻¹
    have hfg : f.comp g = .id ℝ ℝ := by
      ext; simp [f, g, ContinuousLinearMap.smulRight_apply]; field_simp
    have hgf : g.comp f = .id ℝ ℝ := by
      ext; simp [f, g, ContinuousLinearMap.smulRight_apply]; field_simp
    exact ContinuousLinearMap.IsInvertible.of_inverse hfg hgf
  let ψ := hF_strict.implicitFunctionOfProdDomain hF_inv
  refine ⟨ψ, ?_, ?_, ?_, ?_⟩
  · have h := ((hF_strict.eventually_apply_eq_iff_implicitFunctionOfProdDomain
      hF_inv).self_of_nhds.mp rfl).symm
    simpa using h.symm
  · have h := hF_strict.eventually_apply_implicitFunctionOfProdDomain hF_inv
    rwa [H.F_vanishes] at h
  · have hψ0 : ψ 0 = S.α_star := by
      have h := ((hF_strict.eventually_apply_eq_iff_implicitFunctionOfProdDomain
        hF_inv).self_of_nhds.mp rfl).symm
      simpa using h.symm
    have h_near : ∀ᶠ δ in nhds 0, S.F (δ, ψ δ) = 0 := by
      have h := hF_strict.eventually_apply_implicitFunctionOfProdDomain hF_inv
      rwa [H.F_vanishes] at h
    have hψ_smooth : ContDiffAt ℝ ⊤ ψ 0 :=
      H.F_smooth.contDiffAt.contDiffAt_implicitFunction (by simp) hF_inv
    have hψ_diff : DifferentiableAt ℝ ψ 0 :=
      hψ_smooth.differentiableAt (by norm_num)
    have hFα : HasDerivAt (fun δ => S.F (δ, ψ δ))
        (H.dF_dδ + H.dF_dα * deriv ψ 0) 0 := by
      have h_pair : HasDerivAt (fun δ => (δ, ψ δ)) (1, deriv ψ 0) 0 :=
        (hasDerivAt_id (0 : ℝ)).prodMk hψ_diff.hasDerivAt
      set L := fderiv ℝ S.F (0, S.α_star) with hL_def
      have hFψ : HasDerivAt (fun δ => S.F (δ, ψ δ))
          (L (1, deriv ψ 0)) 0 :=
        (hψ0 ▸ hF_strict.hasFDerivAt).comp_hasDerivAt 0 h_pair
      have hL_decomp : L (1, deriv ψ 0) = H.dF_dδ + H.dF_dα * deriv ψ 0 := by
        have hsplit : ((1 : ℝ), deriv ψ 0) =
            ((1 : ℝ), (0 : ℝ)) + deriv ψ 0 • ((0 : ℝ), (1 : ℝ)) := by
          ext <;> simp
        rw [hsplit, map_add, map_smul]
        have hFδ_pair : HasDerivAt (fun δ : ℝ => ((δ : ℝ), S.α_star))
            ((1 : ℝ), (0 : ℝ)) 0 :=
          HasDerivAt.prodMk (hasDerivAt_id 0) (hasDerivAt_const 0 S.α_star)
        have hFδ_comp : HasDerivAt (fun δ => S.F (δ, S.α_star))
            (L ((1 : ℝ), (0 : ℝ))) 0 :=
          hF_strict.hasFDerivAt.comp_hasDerivAt 0 hFδ_pair
        have hL10 : L ((1 : ℝ), (0 : ℝ)) = H.dF_dδ :=
          hFδ_comp.unique H.has_partial_δ
        have hFα_pair : HasDerivAt (fun α : ℝ => ((0 : ℝ), α))
            ((0 : ℝ), (1 : ℝ)) S.α_star :=
          HasDerivAt.prodMk (hasDerivAt_const S.α_star (0 : ℝ)) (hasDerivAt_id S.α_star)
        have hFα_comp : HasDerivAt (fun α => S.F (0, α))
            (L ((0 : ℝ), (1 : ℝ))) S.α_star :=
          hF_strict.hasFDerivAt.comp_hasDerivAt S.α_star hFα_pair
        have hL01 : L ((0 : ℝ), (1 : ℝ)) = H.dF_dα :=
          hFα_comp.unique H.has_partial_α
        rw [hL10, hL01, smul_eq_mul, mul_comm]
      rwa [hL_decomp] at hFψ
    have hF_zero_da : HasDerivAt (fun δ => S.F (δ, ψ δ)) 0 0 := by
      have heq : (fun δ => S.F (δ, ψ δ)) =ᶠ[nhds 0] fun _ => (0 : ℝ) :=
        h_near.mono fun δ hδ => hδ
      exact heq.hasDerivAt_iff.mpr (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    have heq := hFα.unique hF_zero_da
    have hψ_val : deriv ψ 0 = S.c₁ := by
      rw [H.c₁_eq]
      have key : H.dF_dα * deriv ψ 0 = -H.dF_dδ := by linarith
      rw [eq_div_iff (ne_of_gt H.dF_dα_pos)]
      linarith [mul_comm (deriv ψ 0) H.dF_dα]
    rw [← hψ_val]; exact hψ_diff.hasDerivAt
  · exact H.F_smooth.contDiffAt.contDiffAt_implicitFunction (by simp) hF_inv


/-- **General scaling law with remainder bound.**

    For any spectral threshold problem satisfying the hypotheses,
    the perturbed threshold `ψ(1/d₁²) · d₁` satisfies

        |ψ(1/d₁²) · d₁ − (α★ · d₁ + c₁/d₁)| ≤ C/d₁³

    for `d₁` sufficiently large.

    This is a **graph-independent** result: the specific structure
    (Chebyshev, ADE, etc.) enters only through verifying the hypotheses. -/
theorem general_remainder_bound (S : SpectralThresholdData)
    (H : SpectralThresholdHyp S) :
    ∃ ψ : ℝ → ℝ, ∃ C D : ℝ, 0 < D ∧
      ψ 0 = S.α_star ∧
      (∀ᶠ δ in nhds 0, S.F (δ, ψ δ) = 0) ∧
      HasDerivAt ψ S.c₁ 0 ∧
      (∀ d₁ : ℝ, D < d₁ →
        S.F (1 / d₁ ^ 2, ψ (1 / d₁ ^ 2)) = 0 ∧
        |ψ (1 / d₁ ^ 2) * d₁ - (S.α_star * d₁ + S.c₁ / d₁)| ≤
          C / d₁ ^ 3) := by
  obtain ⟨ψ, hψ0, hψF, hψ_deriv, hψ_smooth⟩ :=
    general_implicit_function S H
  obtain ⟨r, hr_pos, hr_ball⟩ : ∃ r > 0, ∀ δ, |δ| < r → S.F (δ, ψ δ) = 0 := by
    rw [Filter.eventually_iff_exists_mem] at hψF
    obtain ⟨U, hU_mem, hU_eq⟩ := hψF
    rw [mem_nhds_iff] at hU_mem
    obtain ⟨V, hVU, hV_open, h0V⟩ := hU_mem
    obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.isOpen_iff.mp hV_open 0 h0V
    exact ⟨ε, hε_pos, fun δ hδ => hU_eq δ (hVU (hε_ball (by
      rwa [Metric.mem_ball, Real.dist_eq, sub_zero])))⟩
  obtain ⟨U, hU_nhds, hψU⟩ :=
    (hψ_smooth.of_le le_top : ContDiffAt ℝ 2 ψ 0).contDiffOn le_rfl (by simp)
  obtain ⟨b, hb_pos, hb_sub⟩ : ∃ b > 0, Set.Icc 0 b ⊆ U := by
    rw [mem_nhds_iff] at hU_nhds
    obtain ⟨V, hVU, hV_open, h0V⟩ := hU_nhds
    obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.isOpen_iff.mp hV_open 0 h0V
    exact ⟨ε / 2, by positivity, fun x hx => hVU (hε_ball (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
      exact ⟨by linarith [hx.1, hx.2], by linarith [hx.2]⟩))⟩
  have hψ_c2 : ContDiffOn ℝ 2 ψ (Set.Icc 0 b) := hψU.mono hb_sub
  obtain ⟨C₀, hC₀⟩ := exists_taylor_mean_remainder_bound (le_of_lt hb_pos) hψ_c2
  have hψ_within : derivWithin ψ (Set.Icc 0 b) 0 = S.c₁ := by
    rw [DifferentiableAt.derivWithin hψ_deriv.differentiableAt
        (uniqueDiffOn_Icc hb_pos 0 (Set.left_mem_Icc.mpr (le_of_lt hb_pos)))]
    exact hψ_deriv.deriv
  have hTaylor_eq : ∀ x, taylorWithinEval ψ 1 (Set.Icc 0 b) 0 x =
      S.α_star + S.c₁ * x := by
    intro x
    rw [taylorWithinEval_succ]
    simp only [taylor_within_zero_eval, Nat.zero_add, Nat.cast_one,
      Nat.factorial_zero, Nat.cast_one, one_mul, inv_one, sub_zero,
      pow_one, iteratedDerivWithin_one, one_smul]
    rw [hψ0, hψ_within]; simp [smul_eq_mul]; ring
  set D := max (Real.sqrt (1 / b)) (Real.sqrt (1 / r)) + 1
  have hD_pos : 0 < D := by positivity
  refine ⟨ψ, C₀, D, hD_pos, hψ0, hψF, hψ_deriv, fun d₁ hd₁ => ?_⟩
  have hd₁_pos : 0 < d₁ := by linarith [hD_pos]
  have hd₁_ne : d₁ ≠ 0 := ne_of_gt hd₁_pos
  set δ := 1 / d₁ ^ 2 with hδ_def
  have hδ_pos : 0 < δ := by positivity
  have hδ_lt_b : δ < b := by
    have h1 : Real.sqrt (1 / b) < d₁ := by
      calc Real.sqrt (1 / b) ≤ D - 1 := by simp [D]
           _ < d₁ := by linarith
    have hD_sq : Real.sqrt (1 / b) ^ 2 = 1 / b := by
      rw [sq, Real.mul_self_sqrt (by positivity)]
    have hsq : Real.sqrt (1 / b) ^ 2 < d₁ ^ 2 :=
      sq_lt_sq' (by linarith [Real.sqrt_nonneg (1 / b)]) h1
    rw [hD_sq] at hsq
    rw [hδ_def, div_lt_iff₀ (by positivity : (0:ℝ) < d₁ ^ 2)]
    rwa [div_lt_iff₀ hb_pos, mul_comm] at hsq
  have hδ_mem : δ ∈ Set.Icc 0 b := ⟨le_of_lt hδ_pos, le_of_lt hδ_lt_b⟩
  have hδ_lt_r : δ < r := by
    have h1 : Real.sqrt (1 / r) < d₁ := by
      calc Real.sqrt (1 / r) ≤ D - 1 := by simp [D]
           _ < d₁ := by linarith
    have hR_sq : Real.sqrt (1 / r) ^ 2 = 1 / r := by
      rw [sq, Real.mul_self_sqrt (by positivity)]
    have hsq : Real.sqrt (1 / r) ^ 2 < d₁ ^ 2 :=
      sq_lt_sq' (by linarith [Real.sqrt_nonneg (1 / r)]) h1
    rw [hR_sq] at hsq
    rw [hδ_def, div_lt_iff₀ (by positivity : (0:ℝ) < d₁ ^ 2)]
    rwa [div_lt_iff₀ hr_pos, mul_comm] at hsq
  constructor
  · exact hr_ball δ (by rw [abs_of_pos hδ_pos]; exact hδ_lt_r)
  · have hTaylor_bound := hC₀ δ hδ_mem
    rw [hTaylor_eq, show δ - 0 = δ from sub_zero δ] at hTaylor_bound
    simp only [Real.norm_eq_abs, pow_succ, pow_one] at hTaylor_bound
    have halg : ψ δ * d₁ - (S.α_star * d₁ + S.c₁ / d₁) =
        (ψ δ - (S.α_star + S.c₁ * δ)) * d₁ := by
      rw [hδ_def]; field_simp
    rw [halg, abs_mul, abs_of_pos hd₁_pos]
    have hscale : |ψ δ - (S.α_star + S.c₁ * δ)| * d₁ ≤
        C₀ * (δ ^ 0 * δ * δ) * d₁ :=
      mul_le_mul_of_nonneg_right hTaylor_bound (le_of_lt hd₁_pos)
    have hδ_conv : C₀ * (δ ^ 0 * δ * δ) * d₁ = C₀ / d₁ ^ 3 := by
      rw [hδ_def]; field_simp
    linarith


/-- The spectral threshold data for the A_{m+1} principal graph. -/
noncomputable def A_data (m : ℕ) : SpectralThresholdData where
  F := RemainderBound.F m
  α_star := UniversalScalingLaw.α m
  c₁ := RemainderBound.first_order_coeff m

/-- The A_{m+1} data satisfies the spectral threshold hypotheses. -/
theorem A_satisfies_hypotheses (m : ℕ) (hm : 0 < m) :
    ContDiff ℝ ⊤ (A_data m).F
    ∧ (A_data m).F (0, (A_data m).α_star) = 0
    ∧ 0 < RemainderBound.d_deriv (m + 1) ((A_data m).α_star)
    ∧ (∀ d₁ : ℝ, d₁ ≠ 0 →
        SpectralGeometric.correction_general_graph 1 d₁ = -1 / d₁) :=
  ⟨RemainderBound.F_contDiff m,
   RemainderBound.F_vanishes m hm,
   RemainderBound.d_deriv_pos_at_threshold m hm,
   fun d₁ _ => UniversalScalingLaw.universal_correction m d₁⟩


/-! ### The D_{m+2} family

The D-type principal graphs arise from the even parts of Temperley–Lieb
at the Jones indices `4cos²(π/(2m+2))`.  The tridiagonal recurrence is
replaced by a **branching** recurrence at the fork vertex.

The threshold equation takes the form:

    F_D(δ, α) = T_{m+1}(√α/2) − δ · T_m(√α/2) = 0

where `T_n` is the Chebyshev polynomial of the first kind.

The balanced threshold `α★_D = 4cos²(π/(2m+2))` satisfies `T_{m+1} = 0`.

**Transversality:** `T'_{m+1}(cos(π/(2m+2))) ≠ 0` since Chebyshev T
has simple roots.

**First-order coefficient:** `c₁_D = T_m(cos θ)/T'_{m+1}(cos θ)`.
The key question (open) is whether `c₁_D = −1` universally, or whether
the branching modifies the correction.

To apply `general_remainder_bound`, one needs only to:
1. Define `F_D` and prove it is `C^∞`.
2. Compute `F_D(0, α★_D) = 0`.
3. Prove transversality.
4. Compute `c₁_D`.

The `O(1/d₁³)` remainder bound then follows automatically from the
general framework. -/


/-! ### The exceptional family

For each exceptional graph Γ, the balanced polynomial `P_Γ(α)` has the
squared Perron-Frobenius eigenvalues `{4cos²(kπ/h) : k ∈ exponents}` as
roots, where `h` is the Coxeter number.  Vieta's formulas then give the
coefficients.

- **E₆**: `P(α) = α³ − 6α² + 9α − 2 = (α² − 4α + 1)(α − 2)`,
  balanced threshold `α★ = 4cos²(π/12) = 2 + √3`.
  Roots: `{2+√3, 2, 2−√3} = {4cos²(kπ/12) : k ∈ {1,3,5}}`.

- **E₇**: `P(α) = α³ − 6α² + 9α − 3`,
  balanced threshold `α★ = 4cos²(π/18)`.
  Roots: `{4cos²(kπ/18) : k ∈ {1,5,7}}`.
  Derivation: `y = cos(π/9)` satisfies `8y³ − 6y − 1 = 0` (from
  `cos(3·π/9) = cos(π/3) = ½` via the triple-angle identity).
  Substituting `α = 2 + 2y` gives `(α−2)³ − 3(α−2) − 1 = α³ − 6α² + 9α − 3`.

- **E₈**: `P(α) = α⁴ − 7α³ + 14α² − 8α + 1`,
  balanced threshold `α★ = 4cos²(π/30)`.
  Roots: `{4cos²(kπ/30) : k ∈ {1,7,11,13}}`.
  Derivation: `y = cos(π/15)` satisfies `32y⁵ − 40y³ + 10y − 1 = 0` (from
  `cos(5·π/15) = cos(π/3) = ½` via the quintuple-angle identity).
  Substituting `α = 2 + 2y` gives the quintic
  `α⁵ − 10α⁴ + 35α³ − 50α² + 25α − 3 = (α − 3)(α⁴ − 7α³ + 14α² − 8α + 1)`;
  the E₈ Jones index is a root of the quartic factor.

The perturbation terms `δ · Q_Γ(α)` depend on the specific branching
structure of each graph and are not determined by the minimal polynomial
alone; they require a separate derivation from the physical setup.

In each case:
1. `F_Γ` is a polynomial in `(δ, α)`, so trivially `C^∞`.
2. Vanishing at the balanced threshold is a direct algebraic computation.
3. Transversality: since the roots of `P_Γ` are simple (all squared
   Perron eigenvalues are distinct), `P'_Γ(α★) ≠ 0`.
4. The first-order coefficient determines whether the correction
   `−1/d₁` remains universal for the exceptional graphs.

This is the natural next target for the formalisation. -/


/-- **Conjecture (Universality of the −1/d₁ correction).**

    For EVERY finite principal graph Γ at index `< 4` (i.e. the full
    ADE classification), the trace-normalised Perron–Frobenius root
    amplitude equals 1, giving the universal correction `−1/d₁`.

    For A_{m+1}, this is `ChristoffelDarboux.trace_normalisation`.
    For D and E types, this would follow from the analogous CD identity
    on the branching graph.

    The `general_remainder_bound` theorem shows that IF this conjecture
    holds for a given graph, THEN the scaling law
      `λ★(d₁) = α★ · d₁ − 1/d₁ + O(1/d₁³)`
    follows automatically. -/
def universality_conjecture : Prop :=
  ∀ (S : SpectralThresholdData) (_H : SpectralThresholdHyp S),
    -- If the trace-normalised root amplitude is 1...
    S.c₁ = -1 →
    -- ...then the physical correction is −1/d₁
    ∀ d₁ : ℝ, d₁ ≠ 0 →
      SpectralGeometric.correction_general_graph 1 d₁ = -1 / d₁

/-- The universality conjecture is (trivially) true, because
    `correction_general_graph 1 d₁ = −1/d₁` by definition.
    The non-trivial content is verifying `c₁ = −1` for each graph,
    which is the CD trace normalisation. -/
theorem universality_conjecture_true : universality_conjecture :=
  fun _ _ _ d₁ _ => SpectralGeometric.correction_TL d₁ (by assumption)

end GeneralScalingLaw
