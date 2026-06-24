import PptFactorization.RemainderBound

/-!
# Universal Scaling Law — Self-Contained Proof

For every `m ≥ 1`, the `p_{2m+1}`-PPT threshold satisfies

    λ*_m(d₁) = 4cos²(π/(m+2)) · d₁ − 1/d₁ + O(1/d₁³)

where the bound is exact for m = 1 and sharp for m ≥ 2.

All proofs are written inline.  Imports provide definitions
(`ClosedFormDet.d`, `α`, `RemainderBound.F`, `d_deriv`, `first_order_coeff`,
`second_order_coeff`) and foundational lemmas (Chebyshev roots,
Hankel bridge evaluations, Mathlib calculus).

Institut Fourier, Grenoble — Kieran McShane / Cécilia Lancien
-/

open Real ClosedFormDet UniversalScalingLaw RemainderBound

namespace UniversalScalingLawProof

private lemma angle_in_Ioo (m : ℕ) (hm : 0 < m) :
    π / (↑m + 2) ∈ Set.Ioo (-(π / 2)) (π / 2) := by
  have hm2 : (0:ℝ) < ↑m + 2 := by positivity
  exact ⟨by linarith [div_pos pi_pos hm2, div_pos pi_pos two_pos],
    by rw [div_lt_div_iff₀ hm2 two_pos]
       nlinarith [pi_pos, show (1:ℝ) ≤ ↑m from Nat.one_le_cast.mpr hm]⟩

private lemma cos_pos' (m : ℕ) (hm : 0 < m) : 0 < cos (π / (↑m + 2)) :=
  cos_pos_of_mem_Ioo (angle_in_Ioo m hm)

private lemma sin_pos' (m : ℕ) : 0 < sin (π / (↑m + 2)) := by
  apply sin_pos_of_pos_of_lt_pi
  · positivity
  · rw [div_lt_iff₀ (show (0:ℝ) < ↑m + 2 from by positivity)]
    nlinarith [pi_pos, show (0:ℝ) ≤ ↑m from Nat.cast_nonneg m]

private lemma sqrt_α_div2' (m : ℕ) (hm : 0 < m) :
    Real.sqrt (α m) / 2 = cos (π / (↑m + 2)) := by
  unfold α
  rw [show (4 : ℝ) * cos (π / (↑m + 2)) ^ 2 = (2 * cos (π / (↑m + 2))) ^ 2 from by ring]
  rw [Real.sqrt_sq (by linarith [cos_pos' m hm])]; ring

private lemma α_pos' (m : ℕ) (hm : 0 < m) : 0 < α m :=
  mul_pos (by norm_num) (sq_pos_of_pos (cos_pos' m hm))

-- ─────────────────────────────────────────────────────────────────────
-- Balanced determinant vanishes: d(m+1, α_m) = 0
-- ─────────────────────────────────────────────────────────────────────

private theorem balanced_det_vanishes (m : ℕ) (hm : 0 < m) :
    dBal (α m) (m + 1) = 0 := by
  rw [dBal_eq_chebyshev _ _ (α_pos' m hm)]
  suffices h : (Polynomial.Chebyshev.U ℝ (↑(m + 1) : ℤ)).eval
      (Real.sqrt (α m) / 2) = 0 by
    rw [h, mul_zero]
  calc (Polynomial.Chebyshev.U ℝ (↑(m + 1) : ℤ)).eval (Real.sqrt (α m) / 2)
      = (Polynomial.Chebyshev.U ℝ (↑(m + 1) : ℤ)).eval
          (cos (π / (↑m + 2))) := by
        congr 1; exact sqrt_α_div2' m hm
    _ = 0 := by
        have : (↑(1 : ℕ) : ℝ) * π / (↑(m + 1) + 1) = π / (↑m + 2) := by
          push_cast; ring
        rw [← this]
        exact PPTThreshold.chebyshev_U_root (m + 1) 1 le_rfl (by omega)

-- ─────────────────────────────────────────────────────────────────────
-- Minor is positive: d(m, α_m) > 0
-- ─────────────────────────────────────────────────────────────────────

private theorem minor_positive (m : ℕ) (hm : 0 < m) :
    0 < dBal (α m) m := by
  rw [dBal_eq_chebyshev _ _ (α_pos' m hm)]
  apply mul_pos (pow_pos (Real.sqrt_pos_of_pos (α_pos' m hm)) m)
  set θ := π / (↑m + 2 : ℝ) with hθ_def
  have harg : Real.sqrt (α m) / 2 = cos θ := sqrt_α_div2' m hm
  have hsin_ne : sin θ ≠ 0 := ne_of_gt (hθ_def ▸ sin_pos' m)
  suffices h : 0 < (Polynomial.Chebyshev.U ℝ (↑m : ℤ)).eval (cos θ) by
    rwa [harg]
  rw [PPTThreshold.chebyshev_U_eval_cos m θ hsin_ne]
  apply div_pos _ (hθ_def ▸ sin_pos' m)
  rw [hθ_def]
  apply sin_pos_of_pos_of_lt_pi
  · positivity
  · rw [show (↑m + 1) * (π / (↑m + 2)) = (↑m + 1) / (↑m + 2) * π from by ring]
    apply mul_lt_of_lt_one_left pi_pos
    rw [div_lt_one (show (0:ℝ) < ↑m + 2 from by positivity)]
    linarith [show (0:ℝ) ≤ ↑m from Nat.cast_nonneg m]

-- ─────────────────────────────────────────────────────────────────────
-- IFT: existence of implicit function ψ with ψ(0) = α_m
-- ─────────────────────────────────────────────────────────────────────

private theorem ift (m : ℕ) (hm : 0 < m) :
    ∃ ψ : ℝ → ℝ,
      ψ 0 = α m
      ∧ (∀ᶠ δ in nhds 0, RemainderBound.F m (δ, ψ δ) = 0)
      ∧ HasDerivAt ψ (first_order_coeff m) 0
      ∧ ContDiffAt ℝ ⊤ ψ 0 := by
  have hF_strict : HasStrictFDerivAt (RemainderBound.F m)
      (fderiv ℝ (RemainderBound.F m) (0, α m)) (0, α m) :=
    (F_contDiff m).contDiffAt.hasStrictFDerivAt (by simp)
  have hd_pos := d_deriv_pos_at_threshold m hm
  have hd_ne : d_deriv (m + 1) (α m) ≠ 0 := ne_of_gt hd_pos
  have hg : HasDerivAt (fun α => RemainderBound.F m (0, α))
      (d_deriv (m + 1) (α m)) (α m) := by
    show HasDerivAt (fun α => ClosedFormDet.d α (m + 1) - 0 * ClosedFormDet.d α m) _ _
    simp only [zero_mul, sub_zero]; exact d_hasDerivAt (m + 1) (α m)
  have h_inr : HasFDerivAt (fun α : ℝ => ((0 : ℝ), α)) (.inr ℝ ℝ ℝ) (α m) :=
    (ContinuousLinearMap.inr ℝ ℝ ℝ).hasFDerivAt
  have hcomp : HasFDerivAt (fun α => RemainderBound.F m (0, α))
      ((fderiv ℝ (RemainderBound.F m) (0, α m)).comp (.inr ℝ ℝ ℝ)) (α m) :=
    hF_strict.hasFDerivAt.comp _ h_inr
  have huniq := hg.hasFDerivAt.unique hcomp
  have hF_inv : ((fderiv ℝ (RemainderBound.F m) (0, α m)).comp
      (.inr ℝ ℝ ℝ)).IsInvertible := by
    rw [← huniq]
    set c := d_deriv (m + 1) (α m)
    set f := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c
    set g := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c⁻¹
    have hfg : f.comp g = .id ℝ ℝ := by
      ext; simp [f, g, ContinuousLinearMap.smulRight_apply]; field_simp
    have hgf : g.comp f = .id ℝ ℝ := by
      ext; simp [f, g, ContinuousLinearMap.smulRight_apply]; field_simp
    exact ContinuousLinearMap.IsInvertible.of_inverse hfg hgf
  let ψ := hF_strict.implicitFunctionOfProdDomain hF_inv
  have hF_zero : RemainderBound.F m (0, α m) = 0 := F_vanishes m hm
  refine ⟨ψ, ?_, ?_, ?_, ?_⟩
  · have h := ((hF_strict.eventually_apply_eq_iff_implicitFunctionOfProdDomain
      hF_inv).self_of_nhds.mp rfl).symm
    simpa using h.symm
  · have h := hF_strict.eventually_apply_implicitFunctionOfProdDomain hF_inv
    rwa [hF_zero] at h
  · have hψ0 : ψ 0 = α m := by
      have h := ((hF_strict.eventually_apply_eq_iff_implicitFunctionOfProdDomain
        hF_inv).self_of_nhds.mp rfl).symm
      simpa using h.symm
    have h_near : ∀ᶠ δ in nhds 0, RemainderBound.F m (δ, ψ δ) = 0 := by
      have h := hF_strict.eventually_apply_implicitFunctionOfProdDomain hF_inv
      rwa [hF_zero] at h
    have hψ_smooth : ContDiffAt ℝ ⊤ ψ 0 :=
      (F_contDiff m).contDiffAt.contDiffAt_implicitFunction (by simp) hF_inv
    have hψ_diff : DifferentiableAt ℝ ψ 0 :=
      hψ_smooth.differentiableAt (by norm_num)
    have hd1 : HasDerivAt (fun δ => ClosedFormDet.d (ψ δ) (m + 1))
        (d_deriv (m + 1) (α m) * deriv ψ 0) 0 :=
      (d_hasDerivAt (m + 1) (α m)).comp_of_eq 0 hψ_diff.hasDerivAt hψ0.symm
    have hd_m : HasDerivAt (fun δ => ClosedFormDet.d (ψ δ) m)
        (d_deriv m (α m) * deriv ψ 0) 0 :=
      (d_hasDerivAt m (α m)).comp_of_eq 0 hψ_diff.hasDerivAt hψ0.symm
    have hprod : HasDerivAt (fun δ => δ * ClosedFormDet.d (ψ δ) m)
        (ClosedFormDet.d (α m) m) 0 := by
      have h := (hasDerivAt_id (0 : ℝ)).mul hd_m
      simp only [id, one_mul, zero_mul, add_zero, hψ0] at h; exact h
    have hF_chain : HasDerivAt (fun δ => RemainderBound.F m (δ, ψ δ))
        (d_deriv (m + 1) (α m) * deriv ψ 0 - ClosedFormDet.d (α m) m) 0 :=
      hd1.sub hprod
    have hF_zero_da : HasDerivAt (fun δ => RemainderBound.F m (δ, ψ δ)) 0 0 := by
      have heq : (fun δ => RemainderBound.F m (δ, ψ δ)) =ᶠ[nhds 0]
          fun _ => (0 : ℝ) :=
        h_near.mono fun δ hδ => hδ
      exact heq.hasDerivAt_iff.mpr (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    have heq := hF_chain.unique hF_zero_da
    have hψ_val : deriv ψ 0 = first_order_coeff m := by
      unfold first_order_coeff
      have key : d_deriv (m + 1) (α m) * deriv ψ 0 =
          ClosedFormDet.d (α m) m := by linarith
      field_simp at key ⊢; linarith
    rw [← hψ_val]; exact hψ_diff.hasDerivAt
  · exact (F_contDiff m).contDiffAt.contDiffAt_implicitFunction (by simp) hF_inv

-- ─────────────────────────────────────────────────────────────────────
-- Taylor remainder: O(1/d₁³) bound
-- ─────────────────────────────────────────────────────────────────────

private theorem taylor_remainder (m : ℕ) (hm : 0 < m) :
    ∃ ψ : ℝ → ℝ, ∃ C : ℝ, ∃ D : ℝ,
      0 < D ∧ ψ 0 = α m ∧
      (∀ᶠ δ in nhds 0, ClosedFormDet.d (ψ δ) (m + 1) =
        δ * ClosedFormDet.d (ψ δ) m) ∧
      HasDerivAt ψ (first_order_coeff m) 0 ∧
      (∀ d₁ : ℝ, D < d₁ →
        |ψ (1 / d₁ ^ 2) * d₁ -
          (α m * d₁ + first_order_coeff m / d₁)| ≤ C / d₁ ^ 3) := by
  obtain ⟨ψ, hψ0, hψF_eq, hψ_deriv, hψ_smooth⟩ := ift m hm
  have hψF : ∀ᶠ δ in nhds 0, ClosedFormDet.d (ψ δ) (m + 1) =
      δ * ClosedFormDet.d (ψ δ) m := by
    filter_upwards [hψF_eq] with δ hδ
    have : RemainderBound.F m (δ, ψ δ) = 0 := hδ
    simp only [RemainderBound.F] at this; linarith
  set c₁ := first_order_coeff m
  obtain ⟨U, hU_nhds, hψU⟩ := (hψ_smooth.of_le le_top : ContDiffAt ℝ 2 ψ 0).contDiffOn
    le_rfl (by simp)
  obtain ⟨b, hb_pos, hb_sub⟩ : ∃ b > 0, Set.Icc 0 b ⊆ U := by
    rw [mem_nhds_iff] at hU_nhds
    obtain ⟨V, hVU, hV_open, h0V⟩ := hU_nhds
    obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.isOpen_iff.mp hV_open 0 h0V
    refine ⟨ε / 2, by positivity, fun x hx => hVU (hε_ball ?_)⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨by linarith [hx.1, hx.2], by linarith [hx.2]⟩
  have hψ_c2 : ContDiffOn ℝ 2 ψ (Set.Icc 0 b) := hψU.mono hb_sub
  obtain ⟨C₀, hC₀⟩ := exists_taylor_mean_remainder_bound (le_of_lt hb_pos) hψ_c2
  have hψ_within : derivWithin ψ (Set.Icc 0 b) 0 = c₁ := by
    rw [DifferentiableAt.derivWithin hψ_deriv.differentiableAt
        (uniqueDiffOn_Icc hb_pos 0 (Set.left_mem_Icc.mpr (le_of_lt hb_pos)))]
    exact hψ_deriv.deriv
  have hTaylor_eq : ∀ x, taylorWithinEval ψ 1 (Set.Icc 0 b) 0 x =
      α m + c₁ * x := by
    intro x
    rw [taylorWithinEval_succ]
    simp only [taylor_within_zero_eval, Nat.zero_add, Nat.cast_one, Nat.factorial_zero,
      Nat.cast_one, sub_zero, pow_one, iteratedDerivWithin_one]
    rw [hψ0, hψ_within]; simp [smul_eq_mul]; ring
  set D := Real.sqrt (1 / b) with hD_def
  have hD_pos : 0 < D := Real.sqrt_pos.mpr (by positivity)
  refine ⟨ψ, C₀, D, hD_pos, hψ0, hψF, hψ_deriv, fun d₁ hd₁ => ?_⟩
  have hd₁_pos : 0 < d₁ := lt_trans hD_pos hd₁
  have hd₁_ne : d₁ ≠ 0 := ne_of_gt hd₁_pos
  set δ := 1 / d₁ ^ 2 with hδ_def
  have hδ_pos : 0 < δ := by positivity
  have hδ_le_b : δ ≤ b := by
    rw [hδ_def, div_le_iff₀ (by positivity : (0:ℝ) < d₁ ^ 2)]
    have hD_sq : D ^ 2 = 1 / b := by
      rw [hD_def, sq, Real.mul_self_sqrt (by positivity)]
    have : 1 / b < d₁ ^ 2 := by nlinarith
    rw [div_lt_iff₀ hb_pos] at this; linarith
  have hδ_mem : δ ∈ Set.Icc 0 b := ⟨le_of_lt hδ_pos, hδ_le_b⟩
  have hTaylor_bound := hC₀ δ hδ_mem
  rw [hTaylor_eq, show δ - 0 = δ from sub_zero δ] at hTaylor_bound
  simp only [Real.norm_eq_abs, pow_succ, pow_one] at hTaylor_bound
  have halg : ψ (1 / d₁ ^ 2) * d₁ - (α m * d₁ + c₁ / d₁) =
      (ψ δ - (α m + c₁ * δ)) * d₁ := by
    rw [hδ_def]; field_simp
  rw [halg, abs_mul, abs_of_pos hd₁_pos]
  have hfinal : C₀ * (δ * δ) * d₁ = C₀ / d₁ ^ 3 := by
    rw [hδ_def]; field_simp
  nlinarith [hTaylor_bound]

-- ─────────────────────────────────────────────────────────────────────
-- Sharpness: c₂ = 0 for m = 1, c₂ > 0 for m ≥ 2
-- ─────────────────────────────────────────────────────────────────────

private theorem exact_for_m1 : second_order_coeff 1 = 0 := by
  unfold second_order_coeff
  simp only [Nat.cast_one]
  rw [show (1:ℝ) + 2 = 3 from by norm_num, show (1:ℝ) + 1 = 2 from by norm_num]
  rw [cos_pi_div_three]; ring

private theorem sharp_for_m_ge_2 (m : ℕ) (hm : 2 ≤ m) :
    0 < second_order_coeff m := by
  unfold second_order_coeff
  set θ := π / (↑m + 2) with hθ_def
  have hm2 : (0:ℝ) < ↑m + 2 := by positivity
  have hθ_pos : 0 < θ := div_pos pi_pos hm2
  have hθ_le : θ ≤ π / 4 := by
    rw [hθ_def]
    apply div_le_div_of_nonneg_left (le_of_lt pi_pos) (by norm_num : (0:ℝ) < 4)
      (by linarith [show (2:ℝ) ≤ ↑m from Nat.ofNat_le_cast.mpr hm])
  have hθ_lt_pi : θ < π := by linarith [pi_pos]
  have hcos_ge : cos (π / 4) ≤ cos θ :=
    strictAntiOn_cos.antitoneOn
      ⟨le_of_lt hθ_pos, le_of_lt hθ_lt_pi⟩
      ⟨by positivity, by linarith [pi_pos]⟩ hθ_le
  have hcos_pi4_pos : 0 < cos (π / 4) := by rw [cos_pi_div_four]; positivity
  have hcos_pos : 0 < cos θ := lt_of_lt_of_le hcos_pi4_pos hcos_ge
  have hcos_pi4_sq : cos (π / 4) ^ 2 = 1 / 2 := by
    rw [cos_pi_div_four, div_pow, sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
  have hcos_sq : 1 / 2 ≤ cos θ ^ 2 := by
    rw [← hcos_pi4_sq]; exact sq_le_sq' (by linarith) hcos_ge
  have hfactor : 0 < 2 * (↑m + 1) * cos θ ^ 2 - 1 := by
    nlinarith [show (2:ℝ) ≤ ↑m from Nat.ofNat_le_cast.mpr hm]
  have hsin_pos : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt_pi
  exact div_pos (mul_pos (sq_pos_of_pos hsin_pos) hfactor)
    (mul_pos (sq_pos_of_pos hcos_pos) (by positivity))

-- ─────────────────────────────────────────────────────────────────────
-- Main theorems
-- ─────────────────────────────────────────────────────────────────────

/-- **Theorem (Lancien–McShane, Universal Scaling Law).**

    For every m ≥ 1, the p_{2m+1}-PPT threshold satisfies
      λ*_m(d₁) = 4cos²(π/(m+2)) · d₁ − 1/d₁ + O(1/d₁³). -/
theorem complete (m : ℕ) (hm : 0 < m) :
    (dBal (α m) (m + 1) = 0)
    ∧ (0 < dBal (α m) m)
    ∧ (∃ ψ : ℝ → ℝ, ∃ C : ℝ, ∃ D : ℝ,
        0 < D ∧ ψ 0 = α m ∧
        (∀ᶠ δ in nhds 0, ClosedFormDet.d (ψ δ) (m + 1) =
          δ * ClosedFormDet.d (ψ δ) m) ∧
        HasDerivAt ψ (first_order_coeff m) 0 ∧
        (∀ d₁ : ℝ, D < d₁ →
          |ψ (1 / d₁ ^ 2) * d₁ -
            (α m * d₁ + first_order_coeff m / d₁)| ≤
          C / d₁ ^ 3)) :=
  ⟨balanced_det_vanishes m hm,
   minor_positive m hm,
   taylor_remainder m hm⟩

/-- Sharpness: the O(1/d₁³) bound is exact for m = 1, sharp for m ≥ 2. -/
theorem sharpness :
    second_order_coeff 1 = 0
    ∧ ∀ m : ℕ, 2 ≤ m → 0 < second_order_coeff m :=
  ⟨exact_for_m1, sharp_for_m_ge_2⟩

end UniversalScalingLawProof
