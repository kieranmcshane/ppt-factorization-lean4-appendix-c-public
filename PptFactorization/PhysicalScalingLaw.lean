import PptFactorization.SelfContainedProof
import PptFactorization.PhysicalThresholdM3
import PptFactorization.General

/-!
# Universal physical scaling law (conditional ∀m form)

For every `m ≥ 1`, **if** there exists a smooth physical threshold function
`ψ_m : ℝ → ℝ` with `ψ_m(0) = α_m`, `ψ_m'(0) = −1`, and `ψ_m` of class `C²`
at `0`, **then** the physical scaling law

    | ψ_m(1/d₁²) · d₁  −  (α_m · d₁  −  1/d₁) |  ≤  C / d₁³

holds for every `d₁ > D₀`.

This is a `∀m` theorem whose only per-`m` input is the hypothesis
`PhysicalThresholdExists m`.  That hypothesis is discharged concretely for
`m = 3` via `PhysicalThresholdM3.physical_scaling_m3`; for general `m` it
corresponds to the subleading-moment / non-crossing-partition analysis of
`detB_m(λ, d₁)`, which is the missing research-level content.

The proof is a direct Taylor bound on `ψ_m` using Mathlib's
`exists_taylor_mean_remainder_bound`, mirroring the analogous step in
`PhysicalThresholdM3.physical_scaling_m3`.
-/

open Real Filter Topology SelfContainedProof

namespace PhysicalScalingLaw

/-- Hypothesis that a smooth physical threshold function with the universal
    `−1` first-order behaviour exists for the given `m ≥ 1`.  It packages
    exactly what Taylor's theorem needs to produce the physical scaling law. -/
def PhysicalThresholdExists (m : ℕ) : Prop :=
  ∃ ψ : ℝ → ℝ, ψ 0 = α m ∧ HasDerivAt ψ (-1) 0 ∧ ContDiffAt ℝ 2 ψ 0

/-- **Universal physical scaling law (∀ m ≥ 1), conditional form.**

    For every `m ≥ 1`, if a smooth physical threshold function exists with
    the universal first-order coefficient `−1`, then the scaling law

        | ψ_m(1/d₁²) · d₁  −  (α_m · d₁  −  1/d₁) |  ≤  C / d₁³

    holds for all `d₁` large enough.

    The hypothesis `PhysicalThresholdExists m` is the place where the
    subleading-moment correction structure enters: it is satisfied by the
    physical root of `detB_m(·, d₁)` and, per the paper, can be argued for
    all `m` via the NCP expansion.  This file formalises the implication
    once and for all; discharging the hypothesis is per-`m`. -/
theorem physical_scaling_law_conditional (m : ℕ) (hm : 0 < m)
    (h : PhysicalThresholdExists m) :
    ∃ ψ : ℝ → ℝ, ∃ C D₀ : ℝ,
      0 < D₀ ∧ ψ 0 = α m ∧ HasDerivAt ψ (-1) 0 ∧
      (∀ d₁ : ℝ, D₀ < d₁ →
        |ψ (1 / d₁ ^ 2) * d₁ - (α m * d₁ - 1 / d₁)| ≤ C / d₁ ^ 3) := by
  obtain ⟨ψ, hψ0, hψ_deriv, hψ_C2⟩ := h
  -- C² neighbourhood on [0, b].
  obtain ⟨U, hU_nhds, hψU⟩ := hψ_C2.contDiffOn le_rfl (by simp)
  obtain ⟨b, hb_pos, hb_sub⟩ : ∃ b > 0, Set.Icc 0 b ⊆ U := by
    rw [mem_nhds_iff] at hU_nhds
    obtain ⟨V, hVU, hV_open, h0V⟩ := hU_nhds
    obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.isOpen_iff.mp hV_open 0 h0V
    exact ⟨ε / 2, by positivity, fun x hx => hVU (hε_ball (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
      exact ⟨by linarith [hx.1, hx.2], by linarith [hx.2]⟩))⟩
  have hψ_c2 : ContDiffOn ℝ 2 ψ (Set.Icc 0 b) := hψU.mono hb_sub
  obtain ⟨C₀, hC₀⟩ := exists_taylor_mean_remainder_bound (le_of_lt hb_pos) hψ_c2
  have hψ_within : derivWithin ψ (Set.Icc 0 b) 0 = -1 := by
    rw [DifferentiableAt.derivWithin hψ_deriv.differentiableAt
        (uniqueDiffOn_Icc hb_pos 0 (Set.left_mem_Icc.mpr (le_of_lt hb_pos)))]
    exact hψ_deriv.deriv
  have hTaylor_eq : ∀ x, taylorWithinEval ψ 1 (Set.Icc 0 b) 0 x = α m - x := by
    intro x
    rw [taylorWithinEval_succ]
    simp only [taylor_within_zero_eval, Nat.zero_add, Nat.cast_one,
      Nat.factorial_zero, Nat.cast_one, sub_zero, pow_one, iteratedDerivWithin_one]
    rw [hψ0, hψ_within]
    simp [smul_eq_mul]
    ring
  set D₀ := Real.sqrt (1 / b)
  have hD₀_pos : 0 < D₀ := Real.sqrt_pos.mpr (by positivity)
  have hD₀_sq : D₀ ^ 2 = 1 / b := by
    show Real.sqrt (1 / b) ^ 2 = 1 / b
    rw [sq, Real.mul_self_sqrt (by positivity)]
  refine ⟨ψ, C₀, D₀, hD₀_pos, hψ0, hψ_deriv, fun d₁ hd₁ => ?_⟩
  have hd₁_pos : 0 < d₁ := lt_trans hD₀_pos hd₁
  set δ := 1 / d₁ ^ 2 with hδ_def
  have hδ_pos : 0 < δ := by positivity
  have hδ_le_b : δ ≤ b := by
    show 1 / d₁ ^ 2 ≤ b
    rw [div_le_iff₀ (by positivity : (0:ℝ) < d₁ ^ 2)]
    have : 1 / b < d₁ ^ 2 := by nlinarith [hD₀_sq]
    rw [div_lt_iff₀ hb_pos] at this; linarith
  have hδ_mem : δ ∈ Set.Icc 0 b := ⟨le_of_lt hδ_pos, hδ_le_b⟩
  have hTaylor_bound := hC₀ δ hδ_mem
  rw [hTaylor_eq, show δ - 0 = δ from sub_zero δ] at hTaylor_bound
  simp only [Real.norm_eq_abs] at hTaylor_bound
  have hδ_sq_eq : δ ^ (1 + 1) = δ * δ := by ring
  rw [hδ_sq_eq] at hTaylor_bound
  have halg : ψ (1 / d₁ ^ 2) * d₁ - (α m * d₁ - 1 / d₁) =
      (ψ δ - (α m - δ)) * d₁ := by
    show ψ (1 / d₁ ^ 2) * d₁ - (α m * d₁ - 1 / d₁) =
      (ψ (1 / d₁ ^ 2) - (α m - 1 / d₁ ^ 2)) * d₁
    field_simp
  rw [halg, abs_mul, abs_of_pos hd₁_pos]
  have hfinal : C₀ * (δ * δ) * d₁ = C₀ / d₁ ^ 3 := by
    show C₀ * (1 / d₁ ^ 2 * (1 / d₁ ^ 2)) * d₁ = C₀ / d₁ ^ 3
    have hd_ne : d₁ ≠ 0 := ne_of_gt hd₁_pos
    field_simp
  nlinarith [hTaylor_bound]

-- ═══════════════════════════════════════════════════════════════════
-- §. Taylor-level hypothesis: only small-order data needed
-- ═══════════════════════════════════════════════════════════════════

/-- **Taylor-level data** for the physical-threshold bridge at order `m`.

    No explicit `detB_m` required — only the small-order Taylor coefficients
    of some smooth ambient function `G : ℝ × ℝ → ℝ` at the base point
    `(0, α_m)`:

    * `G(0, α_m) = 0`
    * `∂_α G(0, α_m) = dα ≠ 0` (transversality)
    * `∂_δ G(0, α_m) = dδ`
    * `dδ = dα` (universality — this is what forces `ψ_G'(0) = −1`)

    Given this data, the implicit function theorem produces a smooth ψ with
    `ψ(0) = α_m` and `ψ'(0) = −1`, which discharges `PhysicalThresholdExists m`. -/
structure PhysicalThresholdTaylorData (m : ℕ) where
  /-- The ambient smooth function whose zero-set defines the physical root. -/
  G : ℝ × ℝ → ℝ
  /-- `G` is smooth. -/
  smooth : ContDiff ℝ ⊤ G
  /-- `G` vanishes at the base point `(0, α_m)`. -/
  vanishes : G (0, α m) = 0
  /-- Value of `∂_α G` at `(0, α_m)`. -/
  dα : ℝ
  /-- `∂_α G(0, α_m) = dα` as a `HasDerivAt` statement. -/
  hα : HasDerivAt (fun a => G (0, a)) dα (α m)
  /-- `∂_δ G(0, α_m) = dα` (universality condition — equal, not just related). -/
  hδ : HasDerivAt (fun d => G (d, α m)) dα 0
  /-- Transversality: the α-partial does not vanish. -/
  transversal : dα ≠ 0

/-- **Abstract IFT bridge: Taylor data produces `PhysicalThresholdExists`.**

    Given a smooth `G` with `G(0, α_m) = 0`, transversal `∂_α G(0, α_m) = dα ≠ 0`,
    and the universality condition `∂_δ G(0, α_m) = dα`, the implicit function
    theorem yields a smooth `ψ : ℝ → ℝ` with `ψ(0) = α_m` and `ψ'(0) = −1`.

    The proof is Mathlib's `HasStrictFDerivAt.implicitFunctionOfProdDomain`
    (for existence) plus a chain-rule step (for the derivative value).  The
    chain rule uses only the abstract `HasFDerivAt G` — no explicit
    decomposition of `G` is needed. -/
theorem thresholdExists_of_taylorData (m : ℕ) (_hm : 0 < m)
    (h : PhysicalThresholdTaylorData m) : PhysicalThresholdExists m := by
  set G := h.G
  set α_m := α m
  have hG_smooth : ContDiff ℝ ⊤ G := h.smooth
  have hG_zero : G (0, α_m) = 0 := h.vanishes
  have hG_dα : HasDerivAt (fun a => G (0, a)) h.dα α_m := h.hα
  have hG_dδ : HasDerivAt (fun d => G (d, α_m)) h.dα 0 := h.hδ
  have hdα_ne : h.dα ≠ 0 := h.transversal
  -- Step 1: apply the implicit function theorem.
  have hG_strict : HasStrictFDerivAt G (fderiv ℝ G (0, α_m)) (0, α_m) :=
    hG_smooth.contDiffAt.hasStrictFDerivAt (by simp)
  have h_inr : HasFDerivAt (fun α₁ : ℝ => ((0:ℝ), α₁)) (.inr ℝ ℝ ℝ) α_m :=
    (ContinuousLinearMap.inr ℝ ℝ ℝ).hasFDerivAt
  have hcomp : HasFDerivAt (fun a => G (0, a))
      ((fderiv ℝ G (0, α_m)).comp (.inr ℝ ℝ ℝ)) α_m :=
    hG_strict.hasFDerivAt.comp _ h_inr
  have huniq := hG_dα.hasFDerivAt.unique hcomp
  have hG_inv : ((fderiv ℝ G (0, α_m)).comp (.inr ℝ ℝ ℝ)).IsInvertible := by
    rw [← huniq]
    set f := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) h.dα
    set g := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) h.dα⁻¹
    have hfg : f.comp g = .id ℝ ℝ := by
      ext; simp [f, g, ContinuousLinearMap.smulRight_apply]; field_simp
    have hgf : g.comp f = .id ℝ ℝ := by
      ext; simp [f, g, ContinuousLinearMap.smulRight_apply]; field_simp
    exact ContinuousLinearMap.IsInvertible.of_inverse hfg hgf
  let ψ := hG_strict.implicitFunctionOfProdDomain hG_inv
  -- Step 2: the usual ψ properties.
  have hψ0 : ψ 0 = α_m := by
    have h := ((hG_strict.eventually_apply_eq_iff_implicitFunctionOfProdDomain
      hG_inv).self_of_nhds.mp rfl).symm
    simpa using h.symm
  have h_near : ∀ᶠ δ in nhds 0, G (δ, ψ δ) = 0 := by
    have h := hG_strict.eventually_apply_implicitFunctionOfProdDomain hG_inv
    rwa [hG_zero] at h
  have hψ_smooth : ContDiffAt ℝ ⊤ ψ 0 :=
    hG_smooth.contDiffAt.contDiffAt_implicitFunction (by simp) hG_inv
  have hψ_diff : DifferentiableAt ℝ ψ 0 :=
    hψ_smooth.differentiableAt (by norm_num)
  -- Step 3: chain rule — compute ψ'(0) = −1 via the composition.
  -- The curve δ ↦ (δ, ψ δ) has HasDerivAt (1, deriv ψ 0) at 0.
  have hcurve : HasDerivAt (fun δ : ℝ => ((δ, ψ δ) : ℝ × ℝ))
      ((1 : ℝ), deriv ψ 0) 0 :=
    (hasDerivAt_id 0).prodMk hψ_diff.hasDerivAt
  -- Compose with G at (0, α_m) using HasFDerivAt.comp_hasDerivAt.
  have hG_fd : HasFDerivAt G (fderiv ℝ G (0, α_m)) (0, ψ 0) := by
    rw [hψ0]; exact hG_strict.hasFDerivAt
  have hchain : HasDerivAt (fun δ => G (δ, ψ δ))
      (fderiv ℝ G (0, α_m) ((1 : ℝ), deriv ψ 0)) 0 :=
    hG_fd.comp_hasDerivAt 0 hcurve
  -- Compute fderiv G (0, α_m) (1, deriv ψ 0) via bilinearity:
  -- fderiv G (0, α_m) (u, v) = dδ·u + dα·v (where dδ = dα by universality).
  -- Extract fderiv G (0, α_m) (1, 0) = dα from hG_dδ, via composition with
  -- the affine curve d ↦ (d, α_m).
  have happly_1_0 : fderiv ℝ G (0, α_m) (1, 0) = h.dα := by
    have hcurve_δ : HasDerivAt (fun d : ℝ => ((d, α_m) : ℝ × ℝ))
        ((1, 0) : ℝ × ℝ) 0 :=
      (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 α_m)
    have hG_fd0 : HasFDerivAt G (fderiv ℝ G (0, α_m)) (0, α_m) :=
      hG_strict.hasFDerivAt
    have hcomp_δ : HasDerivAt (fun d : ℝ => G (d, α_m))
        (fderiv ℝ G (0, α_m) ((1, 0) : ℝ × ℝ)) 0 :=
      hG_fd0.comp_hasDerivAt 0 hcurve_δ
    exact (hG_dδ.unique hcomp_δ).symm
  -- Extract fderiv G (0, α_m) (0, 1) = dα from hG_dα, via composition with
  -- the affine curve a ↦ (0, a).
  have happly_0_1 : fderiv ℝ G (0, α_m) (0, 1) = h.dα := by
    have hcurve_α : HasDerivAt (fun a : ℝ => ((0 : ℝ), a))
        ((0, 1) : ℝ × ℝ) α_m :=
      (hasDerivAt_const α_m (0:ℝ)).prodMk (hasDerivAt_id α_m)
    have hG_fd0 : HasFDerivAt G (fderiv ℝ G (0, α_m)) (0, α_m) :=
      hG_strict.hasFDerivAt
    have hcomp_α : HasDerivAt (fun a : ℝ => G (0, a))
        (fderiv ℝ G (0, α_m) ((0, 1) : ℝ × ℝ)) α_m :=
      hG_fd0.comp_hasDerivAt α_m hcurve_α
    exact (hG_dα.unique hcomp_α).symm
  -- Now (1, deriv ψ 0) = (1, 0) + (0, deriv ψ 0), and the fderiv is linear.
  have hval : fderiv ℝ G (0, α_m) (1, deriv ψ 0) =
      h.dα + h.dα * deriv ψ 0 := by
    have hsplit : ((1 : ℝ), deriv ψ 0) = ((1, 0) : ℝ × ℝ) + (0, deriv ψ 0) := by
      ext <;> simp
    rw [hsplit, map_add]
    have hscale : ((0 : ℝ), deriv ψ 0) = (deriv ψ 0 : ℝ) • ((0, 1) : ℝ × ℝ) := by
      ext <;> simp
    rw [hscale, map_smul, happly_1_0, happly_0_1]
    show h.dα + deriv ψ 0 • h.dα = h.dα + h.dα * deriv ψ 0
    rw [smul_eq_mul, mul_comm]
  rw [hval] at hchain
  -- Now use `fun δ => G (δ, ψ δ) = 0 eventually` to force the derivative to 0.
  have hchain_zero : HasDerivAt (fun δ => G (δ, ψ δ)) 0 0 := by
    have heq : (fun δ => G (δ, ψ δ)) =ᶠ[nhds 0] fun _ => (0 : ℝ) :=
      h_near.mono fun δ hδ => hδ
    exact heq.hasDerivAt_iff.mpr (hasDerivAt_const 0 0)
  have heq_deriv := hchain.unique hchain_zero
  -- h.dα + h.dα * deriv ψ 0 = 0 ⟹ deriv ψ 0 = −1
  have hderiv_val : deriv ψ 0 = -1 := by
    have : h.dα + h.dα * deriv ψ 0 = 0 := heq_deriv
    have : h.dα * (1 + deriv ψ 0) = 0 := by linarith
    have h1 : 1 + deriv ψ 0 = 0 := by
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hdα_ne
      · exact h
    linarith
  -- Package the result.
  refine ⟨ψ, hψ0, ?_, hψ_smooth.of_le le_top⟩
  rw [← hderiv_val]; exact hψ_diff.hasDerivAt

-- ═══════════════════════════════════════════════════════════════════
-- §. Discharge the hypothesis for m = 3 via PhysicalThresholdM3
-- ═══════════════════════════════════════════════════════════════════

/-- `SelfContainedProof.α 3 = PhysicalThresholdM3.α₃ = (3 + √5)/2`. -/
theorem α_three_eq : α 3 = PhysicalThresholdM3.α₃ := by
  unfold SelfContainedProof.α PhysicalThresholdM3.α₃
  -- Goal: 4 * cos (π / (↑3 + 2)) ^ 2 = (3 + √5) / 2
  -- Use cos (π/5) = (1 + √5)/4 (Mathlib: Real.cos_pi_div_five)
  have hcos : cos (π / 5) = (1 + Real.sqrt 5) / 4 := Real.cos_pi_div_five
  have h5 : ((3 : ℕ) : ℝ) + 2 = 5 := by norm_num
  rw [h5, hcos]
  have hs : Real.sqrt 5 ^ 2 = 5 := by
    rw [sq]; exact Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 5)
  nlinarith [hs]

/-- The physical-threshold hypothesis is discharged for `m = 3` using the
    implicit function constructed in `PhysicalThresholdM3.ift_m3`. -/
theorem physical_threshold_exists_m3 : PhysicalThresholdExists 3 := by
  obtain ⟨ψ, hψ0, _, hψ_deriv, hψ_smooth⟩ := PhysicalThresholdM3.ift_m3
  refine ⟨ψ, ?_, hψ_deriv, hψ_smooth.of_le le_top⟩
  rw [hψ0, α_three_eq]

-- ═══════════════════════════════════════════════════════════════════
-- §. Discharge the hypothesis for m = 1 via the exact detB₁ root
-- ═══════════════════════════════════════════════════════════════════

/-- `SelfContainedProof.α 1 = 1 = 4 cos²(π/3)`. -/
theorem α_one_eq : α 1 = 1 := by
  unfold SelfContainedProof.α
  have h3 : ((1 : ℕ) : ℝ) + 2 = 3 := by norm_num
  rw [h3, Real.cos_pi_div_three]
  norm_num

/-- The explicit physical root for `m = 1`: `ψ₁(δ) = 1 − δ`, which gives
    `ψ₁(1/d₁²)·d₁ = d₁ − 1/d₁`, the exact physical PPT threshold.

    Non-vacuousness: for all `d₁ ≠ 0`, `detB₁((1 − 1/d₁²)·d₁, d₁) = 0`,
    verifying that this `ψ₁` is genuinely a root of the physical Hankel
    determinant (not just a convenient affine stub). -/
theorem physical_root_m1 (d₁ : ℝ) (hd : d₁ ≠ 0) :
    General.detB₁ ((1 - 1 / d₁ ^ 2) * d₁) d₁ = 0 := by
  rw [General.detB₁_eq _ _ hd]
  field_simp
  ring

/-- The physical-threshold hypothesis is discharged for `m = 1` using the
    affine `ψ₁(δ) = 1 − δ`.  Unlike the generic affine witness
    `α_m − δ`, this one **is** the physical root of `detB₁` (see
    `physical_root_m1`), so the discharge is genuine.  -/
theorem physical_threshold_exists_m1 : PhysicalThresholdExists 1 := by
  refine ⟨fun δ => 1 - δ, ?_, ?_, ?_⟩
  · show (1 : ℝ) - 0 = α 1
    rw [sub_zero, α_one_eq]
  · simpa using (hasDerivAt_const (0:ℝ) (1:ℝ)).sub (hasDerivAt_id 0)
  · exact (contDiff_const.sub contDiff_id).contDiffAt

/-- **Physical scaling law at m = 1, via the universal conditional theorem.**
    Corollary of `physical_scaling_law_conditional` with `m = 1` discharge.
    The witness `ψ₁(δ) = 1 − δ` is the exact physical root of `detB₁`, so the
    Taylor bound holds with `C = 0` and the scaling law is exact:
    `ψ₁(1/d₁²)·d₁ = d₁ − 1/d₁`. -/
theorem physical_scaling_law_m1 :
    ∃ ψ : ℝ → ℝ, ∃ C D₀ : ℝ,
      0 < D₀ ∧ ψ 0 = α 1 ∧ HasDerivAt ψ (-1) 0 ∧
      (∀ d₁ : ℝ, D₀ < d₁ →
        |ψ (1 / d₁ ^ 2) * d₁ - (α 1 * d₁ - 1 / d₁)| ≤ C / d₁ ^ 3) :=
  physical_scaling_law_conditional 1 (by norm_num) physical_threshold_exists_m1

-- ═══════════════════════════════════════════════════════════════════
-- §. Discharge the hypothesis for m = 2 via General.Q₂ / detB₂
-- ═══════════════════════════════════════════════════════════════════

/-- Normalised physical polynomial for `m = 2`.
    `G₂_phys(δ, α) = α(2 − α) + δ(4 − 3α) + δ²(α − 4)`.
    Derived from `General.Q₂_at_slope` via `Q₂(α·d₁, d₁) = d₁⁵ · G₂_phys(1/d₁², α)`. -/
noncomputable def G₂_phys : ℝ × ℝ → ℝ :=
  fun p => p.2 * (2 - p.2) + p.1 * (4 - 3 * p.2) + p.1 ^ 2 * (p.2 - 4)

theorem G₂_phys_contDiff : ContDiff ℝ ⊤ G₂_phys := by
  unfold G₂_phys
  fun_prop

/-- `SelfContainedProof.α 2 = 2 = 4 cos²(π/4)`. -/
theorem α_two_eq : α 2 = 2 := by
  unfold SelfContainedProof.α
  have h4 : ((2 : ℕ) : ℝ) + 2 = 4 := by norm_num
  rw [h4, Real.cos_pi_div_four, div_pow,
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

theorem G₂_phys_vanishes : G₂_phys (0, α 2) = 0 := by
  unfold G₂_phys
  rw [α_two_eq]
  norm_num

theorem G₂_phys_hasDerivAt_α :
    HasDerivAt (fun a => G₂_phys (0, a)) (-2) (α 2) := by
  rw [α_two_eq]
  have heq : (fun a : ℝ => G₂_phys (0, a)) = fun a => a * (2 - a) := by
    funext a; unfold G₂_phys; ring
  rw [heq]
  have h1 : HasDerivAt (fun a : ℝ => a) 1 (2 : ℝ) := hasDerivAt_id 2
  have h2 : HasDerivAt (fun a : ℝ => (2 : ℝ) - a) (-1) 2 := by
    have := (hasDerivAt_const (2:ℝ) (2:ℝ)).sub (hasDerivAt_id 2)
    simpa using this
  have hm := h1.mul h2
  convert hm using 1; ring

theorem G₂_phys_hasDerivAt_δ :
    HasDerivAt (fun d => G₂_phys (d, α 2)) (-2) 0 := by
  rw [α_two_eq]
  have heq : (fun d : ℝ => G₂_phys (d, 2)) =
      fun d => d * (-2 : ℝ) + d ^ 2 * (-2 : ℝ) := by
    funext d; unfold G₂_phys; ring
  rw [heq]
  have h1 : HasDerivAt (fun d : ℝ => d * (-2 : ℝ)) (-2) 0 := by
    have := (hasDerivAt_id (0:ℝ)).mul_const (-2 : ℝ)
    simpa using this
  have h2 : HasDerivAt (fun d : ℝ => d ^ 2 * (-2 : ℝ)) 0 0 := by
    have := (hasDerivAt_pow 2 (0:ℝ)).mul_const (-2 : ℝ)
    simpa using this
  have := h1.add h2
  simpa using this

/-- Taylor data for `m = 2`, using the physical polynomial from `Q₂_at_slope`. -/
noncomputable def physicalTaylorData_m2 : PhysicalThresholdTaylorData 2 where
  G := G₂_phys
  smooth := G₂_phys_contDiff
  vanishes := G₂_phys_vanishes
  dα := -2
  hα := G₂_phys_hasDerivAt_α
  hδ := G₂_phys_hasDerivAt_δ
  transversal := by norm_num

/-- **Non-vacuous `m = 2` discharge** using the physical `G₂` from `Q₂_at_slope`. -/
theorem physical_threshold_exists_m2 : PhysicalThresholdExists 2 :=
  thresholdExists_of_taylorData 2 (by norm_num) physicalTaylorData_m2

/-- Bridge: `detB₂(α·d₁, d₁) = −α⁴ · G₂_phys(1/d₁², α)`. -/
theorem detB₂_eq_G₂_phys (α d₁ : ℝ) (hd : d₁ ≠ 0) :
    General.detB₂ (α * d₁) d₁ = - α ^ 4 * G₂_phys (1 / d₁ ^ 2, α) := by
  rw [General.detB₂_eq _ _ hd, General.Q₂_at_slope]
  unfold G₂_phys
  field_simp
  ring

/-- If `G₂_phys(1/d₁², α) = 0`, then `α·d₁` is a root of `detB₂`. -/
theorem detB₂_vanishes_of_G₂_phys (α d₁ : ℝ) (hd : d₁ ≠ 0)
    (hG : G₂_phys (1 / d₁ ^ 2, α) = 0) :
    General.detB₂ (α * d₁) d₁ = 0 := by
  rw [detB₂_eq_G₂_phys _ _ hd, hG, mul_zero]

/-- **Physical scaling law at m = 2, via the universal conditional theorem.**
    Non-vacuous: the witness comes from `G₂_phys`, which is the normalised
    physical polynomial of `detB₂`. -/
theorem physical_scaling_law_m2 :
    ∃ ψ : ℝ → ℝ, ∃ C D₀ : ℝ,
      0 < D₀ ∧ ψ 0 = α 2 ∧ HasDerivAt ψ (-1) 0 ∧
      (∀ d₁ : ℝ, D₀ < d₁ →
        |ψ (1 / d₁ ^ 2) * d₁ - (α 2 * d₁ - 1 / d₁)| ≤ C / d₁ ^ 3) :=
  physical_scaling_law_conditional 2 (by norm_num) physical_threshold_exists_m2

/-- **Physical scaling law at m = 3, via the universal conditional theorem.**
    This is a corollary of `physical_scaling_law_conditional` and
    `physical_threshold_exists_m3`.  It demonstrates that the ∀m schema is
    non-vacuous: the hypothesis can be discharged for m = 3 by supplying the
    explicit physical threshold function from `PhysicalThresholdM3`. -/
theorem physical_scaling_law_m3 :
    ∃ ψ : ℝ → ℝ, ∃ C D₀ : ℝ,
      0 < D₀ ∧ ψ 0 = α 3 ∧ HasDerivAt ψ (-1) 0 ∧
      (∀ d₁ : ℝ, D₀ < d₁ →
        |ψ (1 / d₁ ^ 2) * d₁ - (α 3 * d₁ - 1 / d₁)| ≤ C / d₁ ^ 3) :=
  physical_scaling_law_conditional 3 (by norm_num) physical_threshold_exists_m3

-- ═══════════════════════════════════════════════════════════════════
-- §. Universal closed form for the canonical correction c_m
-- ═══════════════════════════════════════════════════════════════════

/-- **Canonical correction constant** for the `G_canonical m` construction:
    `c_m := d(α_m, m) + d'(m+1, α_m)`. -/
noncomputable def c_coeff (m : ℕ) : ℝ :=
  d (α m) m + d_deriv (m + 1) (α m)

/-- Helper: `d_deriv (m+1) (α m)` has a closed form in terms of `cos`, `sin`, `m`.
    Derived from `d_at_threshold` and `first_order_coeff_eq`. -/
theorem d_deriv_at_threshold_closed (m : ℕ) (hm : 0 < m) :
    d_deriv (m + 1) (α m) =
      (2 * cos (π / (↑m + 2))) ^ m * (↑m + 2) /
        (4 * sin (π / (↑m + 2)) ^ 2) := by
  have hd : d (α m) m = (2 * cos (π / (↑m + 2))) ^ m :=
    SelfContainedProof.d_at_threshold m hm
  have hfoc : first_order_coeff m = d (α m) m / d_deriv (m + 1) (α m) := rfl
  have hfoc_eq : first_order_coeff m =
      4 * sin (π / (↑m + 2)) ^ 2 / (↑m + 2) :=
    first_order_coeff_eq m hm
  have hne : d_deriv (m + 1) (α m) ≠ 0 :=
    ne_of_gt (d_deriv_pos_at_threshold m hm)
  have hsin_pos := sin_pi_div_pos m
  have hsin_ne : sin (π / (↑m + 2)) ≠ 0 := ne_of_gt hsin_pos
  have hsin_sq_ne : sin (π / (↑m + 2)) ^ 2 ≠ 0 := pow_ne_zero 2 hsin_ne
  have hm2 : (0 : ℝ) < (↑m + 2 : ℝ) := by positivity
  have hm2_ne : (↑m + 2 : ℝ) ≠ 0 := ne_of_gt hm2
  -- (2 cos θ)^m > 0 from dBal_minor_pos + d_at_threshold.
  have h2cm_pos : 0 < (2 * cos (π / (↑m + 2))) ^ m := by
    have h := dBal_minor_pos m hm
    show 0 < (2 * cos (π / (↑m + 2))) ^ m
    rw [← hd]; exact h
  have h2cm_ne : (2 * cos (π / (↑m + 2))) ^ m ≠ 0 := ne_of_gt h2cm_pos
  have hkey : d (α m) m / d_deriv (m + 1) (α m) =
      4 * sin (π / (↑m + 2)) ^ 2 / (↑m + 2) := by
    rw [← hfoc]; exact hfoc_eq
  rw [hd] at hkey
  field_simp at hkey
  field_simp
  linarith

/-- **Closed form for `c_m := d(α_m, m) + d'(m+1, α_m)`, universal in `m ≥ 1`.**

    `c_m = (2 cos θ)^m · (4 sin²θ + m + 2) / (4 sin²θ)`, where `θ = π/(m+2)`.

    This is the *exact algebraic identity* that the physical detB_m
    subleading correction must match for the universal `−1` scaling law
    to hold.  Proved here for all `m ≥ 1` using only the existing
    trigonometric / Chebyshev infrastructure in `SelfContainedProof`. -/
theorem c_coeff_closed_form (m : ℕ) (hm : 0 < m) :
    c_coeff m =
      (2 * cos (π / (↑m + 2))) ^ m *
        (4 * sin (π / (↑m + 2)) ^ 2 + (↑m + 2)) /
        (4 * sin (π / (↑m + 2)) ^ 2) := by
  unfold c_coeff
  rw [SelfContainedProof.d_at_threshold m hm,
      d_deriv_at_threshold_closed m hm]
  have hsin_pos := sin_pi_div_pos m
  have hsin_ne : sin (π / (↑m + 2)) ≠ 0 := ne_of_gt hsin_pos
  have hsin_sq_ne : sin (π / (↑m + 2)) ^ 2 ≠ 0 := pow_ne_zero 2 hsin_ne
  field_simp

theorem c_coeff_pos (m : ℕ) (hm : 0 < m) : 0 < c_coeff m := by
  unfold c_coeff
  have h1 : 0 < d (α m) m := dBal_minor_pos m hm
  have h2 : 0 < d_deriv (m + 1) (α m) := d_deriv_pos_at_threshold m hm
  linarith

-- ═══════════════════════════════════════════════════════════════════
-- §. Unconditional ∀m: canonical G_m from SelfContainedProof.d
-- ═══════════════════════════════════════════════════════════════════

/-- **Canonical ambient function for the physical scaling law at order `m`.**

    `G_canonical m (δ, β) := d(β, m+1) − δ·d(β, m) + δ·c_m`, where
    `c_m := d(α_m, m) + d'(m+1, α_m)` is a constant in `β`.

    This is the balanced `F` perturbed by a `δ·constant` term chosen so that
    `∂_δ G(0, α_m) = ∂_β G(0, α_m) = d'(m+1, α_m)`.  The construction uses
    only `SelfContainedProof`'s `d`, `d_deriv`, and the already-proven
    facts `dBal_vanishes`, `d_deriv_pos_at_threshold`. -/
noncomputable def G_canonical (m : ℕ) : ℝ × ℝ → ℝ :=
  fun p => d p.2 (m + 1) - p.1 * d p.2 m +
           p.1 * (d (α m) m + d_deriv (m + 1) (α m))

theorem G_canonical_contDiff (m : ℕ) : ContDiff ℝ ⊤ (G_canonical m) := by
  unfold G_canonical
  exact (((d_contDiff (m + 1)).comp contDiff_snd).sub
    (contDiff_fst.mul ((d_contDiff m).comp contDiff_snd))).add
    (contDiff_fst.mul contDiff_const)

theorem G_canonical_vanishes (m : ℕ) (hm : 0 < m) :
    G_canonical m (0, α m) = 0 := by
  unfold G_canonical
  simp only [zero_mul, sub_zero, add_zero]
  exact dBal_vanishes m hm

theorem G_canonical_hasDerivAt_β (m : ℕ) (hm : 0 < m) :
    HasDerivAt (fun a => G_canonical m (0, a)) (d_deriv (m + 1) (α m)) (α m) := by
  have : (fun a : ℝ => G_canonical m (0, a)) = fun a => d a (m + 1) := by
    funext a; unfold G_canonical; simp
  rw [this]; exact d_hasDerivAt (m + 1) (α m)

theorem G_canonical_hasDerivAt_δ (m : ℕ) (hm : 0 < m) :
    HasDerivAt (fun δ => G_canonical m (δ, α m)) (d_deriv (m + 1) (α m)) 0 := by
  -- `G_canonical m (δ, α m) = d (α m) (m+1) + δ · d_deriv (m+1) (α m)`
  -- since `d(α_m, m+1) = 0` and the δ-terms combine.
  have hvan : d (α m) (m + 1) = 0 := dBal_vanishes m hm
  have heq : (fun δ : ℝ => G_canonical m (δ, α m)) =
      fun δ => δ * d_deriv (m + 1) (α m) := by
    funext δ
    unfold G_canonical
    show d (α m) (m + 1) - δ * d (α m) m +
         δ * (d (α m) m + d_deriv (m + 1) (α m)) = δ * d_deriv (m + 1) (α m)
    rw [hvan]; ring
  rw [heq]
  have h := (hasDerivAt_id (0 : ℝ)).mul_const (d_deriv (m + 1) (α m))
  simpa using h

/-- **Taylor-level data for the canonical `G_m`, for every `m ≥ 1`.** -/
noncomputable def canonicalTaylorData (m : ℕ) (hm : 0 < m) :
    PhysicalThresholdTaylorData m where
  G := G_canonical m
  smooth := G_canonical_contDiff m
  vanishes := G_canonical_vanishes m hm
  dα := d_deriv (m + 1) (α m)
  hα := G_canonical_hasDerivAt_β m hm
  hδ := G_canonical_hasDerivAt_δ m hm
  transversal := ne_of_gt (d_deriv_pos_at_threshold m hm)

/-- **Unconditional `∀m` existence of a canonical threshold function with the
    universal `−1` first-order behaviour.**

    This is the threshold for the engineered canonical ambient function
    `G_canonical`, not the all-`m` physical `detB_m` threshold. -/
theorem canonical_threshold_exists_all (m : ℕ) (hm : 0 < m) :
    PhysicalThresholdExists m :=
  thresholdExists_of_taylorData m hm (canonicalTaylorData m hm)

/-- Compatibility alias for older files.

    Despite the historical name, this is the canonical threshold-existence
    theorem above, not a proof that the physical determinant branch has been
    identified for every `m`.  New code should use
    `canonical_threshold_exists_all`. -/
theorem physical_threshold_exists_all (m : ℕ) (hm : 0 < m) :
    PhysicalThresholdExists m :=
  canonical_threshold_exists_all m hm

/-- **Universal canonical scaling law — unconditional `∀ m ≥ 1`.**

    For every `m ≥ 1` there exists a smooth function `ψ_m : ℝ → ℝ` with
    `ψ_m(0) = α_m`, `ψ_m'(0) = −1`, and

        | ψ_m(1/d₁²) · d₁  −  (α_m · d₁  −  1/d₁) |  ≤  C / d₁³

    for every `d₁ > D₀`, with constants `C, D₀ > 0` depending on `m`.

    **What this ψ_m is.**  It is the root of the canonical ambient function
    `G_canonical m := d(·, m+1) − δ·d(·, m) + δ·(d(α_m,m) + d'(m+1, α_m))`,
    i.e. the balanced tridiagonal `F` perturbed by a constant-in-β `δ·c_m`
    term engineered so that `∂_δ G = ∂_β G` at the base point.  This makes
    the IFT first-order coefficient exactly `−1`.

    **What this ψ_m is NOT.**  It is *not* claimed to be the root of the
    physical PPT Hankel determinant `detB_m(·, d₁)` for general `m`.  That
    identification requires verifying that the canonical correction
    `c_m = d(α_m,m) + d'(m+1, α_m)` matches the subleading-moment
    correction coming from the NCP expansion — which holds for `m=1, 2, 3`
    (verified by hand) and is argued in the paper for all `m`, but is not
    formalised here.  For `m = 1, 2, 3` the identification is recovered by
    `physical_threshold_exists_m1` / `m3` using the concrete `detB_m`. -/
theorem canonical_universal_scaling_law :
    ∀ m : ℕ, 0 < m →
      ∃ ψ : ℝ → ℝ, ∃ C D₀ : ℝ,
        0 < D₀ ∧ ψ 0 = α m ∧ HasDerivAt ψ (-1) 0 ∧
        (∀ d₁ : ℝ, D₀ < d₁ →
          |ψ (1 / d₁ ^ 2) * d₁ - (α m * d₁ - 1 / d₁)| ≤ C / d₁ ^ 3) := by
  intro m hm
  exact physical_scaling_law_conditional m hm (canonical_threshold_exists_all m hm)

/-- Compatibility alias for older files.

    Despite the historical name, this theorem is the canonical engineered
    all-`m` scaling law, not the all-`m` physical determinant theorem.  New code
    should use `canonical_universal_scaling_law`; physical determinant claims
    should use the concrete `physical_scaling_law_m1/m2/m3` endpoints or the
    conditional theorem `physical_scaling_law_conditional`. -/
theorem universal_physical_scaling_law :
    ∀ m : ℕ, 0 < m →
      ∃ ψ : ℝ → ℝ, ∃ C D₀ : ℝ,
        0 < D₀ ∧ ψ 0 = α m ∧ HasDerivAt ψ (-1) 0 ∧
        (∀ d₁ : ℝ, D₀ < d₁ →
          |ψ (1 / d₁ ^ 2) * d₁ - (α m * d₁ - 1 / d₁)| ≤ C / d₁ ^ 3) :=
  canonical_universal_scaling_law

end PhysicalScalingLaw
