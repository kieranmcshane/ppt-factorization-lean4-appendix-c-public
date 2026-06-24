import PptFactorization.AubrunAlternative
import PptFactorization.AppendixBRadialSpherical
import PptFactorization.AppendixBNormalizedExpectations
import PptFactorization.RandomMatrixModel
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Model bridge for the alternative Aubrun route

This file connects the abstract high-moment adapters in
`AubrunAlternative.lean` to the concrete finite-dimensional partial-transpose
model in `RandomMatrixModel.lean`.
-/

namespace AubrunAlternative

open MeasureTheory
open scoped BigOperators
open PptFactorization.RandomMatrixModel
open scoped ComplexOrder

variable {p q σ Ω : Type*}
variable [Fintype p] [Fintype q] [Fintype σ]

omit [Fintype σ] in
/-- The positive-semidefinite cone is closed in the finite-dimensional
bipartite matrix space. -/
theorem isClosed_setOf_bipMatrix_posSemidef :
    IsClosed {A : BipMatrix p q | A.PosSemidef} := by
  change IsClosed {A : BipMatrix p q |
    A.IsHermitian ∧ ∀ x : (BipIndex p q →₀ ℂ),
      0 ≤ Finsupp.sum x fun i xi => Finsupp.sum x fun j xj => star xi * A i j * xj}
  apply IsClosed.inter
  · exact isClosed_eq (continuous_id.matrix_conjTranspose) continuous_id
  · change IsClosed {A : BipMatrix p q | ∀ x : (BipIndex p q →₀ ℂ),
        0 ≤ Finsupp.sum x fun i xi => Finsupp.sum x fun j xj => star xi * A i j * xj}
    rw [Set.setOf_forall]
    exact isClosed_iInter fun x : (BipIndex p q →₀ ℂ) => by
      have hEq : (fun A : BipMatrix p q =>
          Finsupp.sum x fun i xi => Finsupp.sum x fun j xj => star xi * A i j * xj) =
          (fun A : BipMatrix p q => ∑ i : BipIndex p q, ∑ j : BipIndex p q,
            star (x i) * A i j * x j) := by
        funext A
        rw [Finsupp.sum_fintype]
        · congr with i
          rw [Finsupp.sum_fintype]
          intro j
          simp
        · intro i
          simp
      have hcont_fin : Continuous fun A : BipMatrix p q => ∑ i : BipIndex p q,
          ∑ j : BipIndex p q, star (x i) * A i j * x j := by
        apply continuous_finset_sum
        intro i _hi
        apply continuous_finset_sum
        intro j _hj
        fun_prop
      have hcont : Continuous fun A : BipMatrix p q =>
          Finsupp.sum x fun i xi => Finsupp.sum x fun j xj => star xi * A i j * xj := by
        rw [hEq]
        exact hcont_fin
      exact (isClosed_Ici (a := (0 : ℂ))).preimage hcont

omit [Fintype σ] in
/-- The positive-semidefinite cone is measurable in the finite-dimensional
bipartite matrix space. -/
theorem measurableSet_bipMatrix_posSemidef :
    MeasurableSet {A : BipMatrix p q | A.PosSemidef} :=
  (isClosed_setOf_bipMatrix_posSemidef (p := p) (q := q)).measurableSet

/-- The concrete sample map `G ↦ ρ^Γ(G)` is measurable. -/
theorem measurable_rhoGamma_sample :
    Measurable (fun G : SampleMatrix p q σ => rhoGamma (p := p) (q := q) (σ := σ) G) := by
  have hDensity :
      Continuous (fun X : SampleMatrix p q σ => densityMatrix (p := p) (q := q) (σ := σ) X) := by
    unfold densityMatrix
    fun_prop
  have hRho : Measurable (fun G : SampleMatrix p q σ => rho (p := p) (q := q) (σ := σ) G) := by
    simpa [rho] using hDensity.measurable.comp
      (PptFactorization.AppendixB.measurable_normalizedSample (p := p) (q := q) (σ := σ))
  simpa [rhoGamma] using
    (PptFactorization.AppendixB.continuous_gamma (p := p) (q := q)).measurable.comp hRho

/-- A measurable random sample matrix has a measurable PPT event. -/
theorem measurableSet_rhoGamma_posSemidef_of_measurable
    [MeasurableSpace Ω] {G : RandomSampleMatrix Ω p q σ} (hG : Measurable G) :
    MeasurableSet {ω : Ω | (rhoGamma (G ω)).PosSemidef} :=
  measurableSet_bipMatrix_posSemidef.preimage (measurable_rhoGamma_sample.comp hG)

section TraceMoment

variable [DecidableEq p] [DecidableEq q]

/-- The centered trace power of `D ρ^Γ - I` is the corresponding centered
power sum of the scaled Hermitian eigenvalue coordinates. -/
theorem rhoGamma_centered_trace_re_eq_sum_scaledRhoGammaEigenvalues
    (D : ℝ) (G : SampleMatrix p q σ) (m : ℕ) :
    RCLike.re ((((D : ℂ) • rhoGamma (p := p) (q := q) (σ := σ) G - 1) ^ m).trace) =
      ∑ i : BipIndex p q, (scaledRhoGammaEigenvalues D G i - 1) ^ m := by
  let A : BipMatrix p q := rhoGamma (p := p) (q := q) (σ := σ) G
  let hA : A.IsHermitian := rhoGamma_isHermitian G
  let φ := (Unitary.conjStarAlgAut ℂ (Matrix (BipIndex p q) (BipIndex p q) ℂ))
    hA.eigenvectorUnitary
  let E : BipMatrix p q := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  have hAeq : A = φ E := by
    simpa [A, hA, E, φ] using hA.spectral_theorem
  have hCentered : ((D : ℂ) • A - 1) = φ ((D : ℂ) • E - 1) := by
    calc
      (D : ℂ) • A - 1 = (D : ℂ) • φ E - 1 := by rw [hAeq]
      _ = φ ((D : ℂ) • E) - φ 1 := by rw [map_smul, map_one]
      _ = φ ((D : ℂ) • E - 1) := by rw [map_sub]
  have hpow : ((D : ℂ) • A - 1) ^ m = φ (((D : ℂ) • E - 1) ^ m) := by
    rw [hCentered]
    exact (map_pow φ ((D : ℂ) • E - 1) m).symm
  calc
    RCLike.re ((((D : ℂ) • rhoGamma (p := p) (q := q) (σ := σ) G - 1) ^ m).trace)
        = RCLike.re ((((D : ℂ) • A - 1) ^ m).trace) := by rfl
    _ = RCLike.re ((φ (((D : ℂ) • E - 1) ^ m)).trace) := by rw [hpow]
    _ = RCLike.re (((((D : ℂ) • E - 1) ^ m)).trace) := by
      exact congrArg RCLike.re
        (PptFactorization.HighProbabilityBounds.matrix_trace_conjStarAlgAut
          hA.eigenvectorUnitary (((D : ℂ) • E - 1) ^ m))
    _ = ∑ i : BipIndex p q, (scaledRhoGammaEigenvalues D G i - 1) ^ m := by
      have hDiag : ((D : ℂ) • E - 1) =
          Matrix.diagonal (fun i : BipIndex p q => ((D * hA.eigenvalues i - 1 : ℝ) : ℂ)) := by
        ext i j
        rw [Matrix.sub_apply, Matrix.smul_apply]
        by_cases hij : i = j
        · subst j
          simp [E, Matrix.diagonal, Complex.ofReal_mul]
        · simp [E, Matrix.diagonal, hij]
      rw [hDiag]
      rw [Matrix.diagonal_pow, Matrix.trace_diagonal]
      change (∑ i : BipIndex p q, (((D * hA.eigenvalues i - 1 : ℝ) : ℂ) ^ m)).re =
        ∑ i : BipIndex p q, (scaledRhoGammaEigenvalues D G i - 1) ^ m
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      have hterm :
          RCLike.re ((((D * hA.eigenvalues i - 1 : ℝ) : ℂ) ^ m)) =
            (D * hA.eigenvalues i - 1) ^ m := by
        have hp : (((D * hA.eigenvalues i - 1 : ℝ) ^ m : ℝ) : ℂ) =
            (((D * hA.eigenvalues i - 1 : ℝ) : ℂ) ^ m) :=
          Complex.ofReal_pow (D * hA.eigenvalues i - 1) m
        exact (congrArg RCLike.re hp.symm).trans
          (RCLike.ofReal_re (K := ℂ) ((D * hA.eigenvalues i - 1) ^ m))
      simpa [scaledRhoGammaEigenvalues, rhoGammaEigenvalues, A, Complex.ofReal_mul] using hterm

/-- The centered trace-power observable `G ↦ Re Tr((Dρ^Γ(G)-I)^m)` is
measurable. -/
theorem measurable_traceCenteredRhoGammaMoment
    (D : ℝ) (m : ℕ) :
    Measurable (fun G : SampleMatrix p q σ =>
      RCLike.re ((((D : ℂ) • rhoGamma (p := p) (q := q) (σ := σ) G - 1) ^ m).trace)) := by
  have hCont : Continuous (fun A : BipMatrix p q =>
      RCLike.re ((((D : ℂ) • A - 1) ^ m).trace)) := by
    fun_prop
  exact hCont.measurable.comp measurable_rhoGamma_sample

/-- A measurable sample map makes the scaled-eigenvalue centered power sum
a.e. measurable.  The proof routes through the trace observable, avoiding any
separate measurability theorem for Hermitian eigenvalue coordinates. -/
theorem aemeasurable_scaledRhoGammaEigenvalueCenteredPowerSum_of_measurable
    [MeasurableSpace Ω] (μ : Measure Ω) {G : RandomSampleMatrix Ω p q σ}
    (hG : Measurable G) (D : ℝ) (m : ℕ) :
    AEMeasurable
      (fun ω : Ω => ENNReal.ofReal
        (∑ i : BipIndex p q, (scaledRhoGammaEigenvalues D (G ω) i - 1) ^ m)) μ := by
  have hTrace : Measurable (fun ω : Ω => ENNReal.ofReal
      (RCLike.re ((((D : ℂ) • rhoGamma (G ω) - 1) ^ m).trace))) := by
    exact ((measurable_traceCenteredRhoGammaMoment
      (p := p) (q := q) (σ := σ) D m).comp hG).ennreal_ofReal
  have hfun :
      (fun ω : Ω => ENNReal.ofReal
        (∑ i : BipIndex p q, (scaledRhoGammaEigenvalues D (G ω) i - 1) ^ m)) =
      (fun ω : Ω => ENNReal.ofReal
        (RCLike.re ((((D : ℂ) • rhoGamma (G ω) - 1) ^ m).trace))) := by
    funext ω
    rw [← rhoGamma_centered_trace_re_eq_sum_scaledRhoGammaEigenvalues D (G ω) m]
  simpa [hfun] using hTrace.aemeasurable

end TraceMoment

/-- Concrete model-facing eventual finite-rate bridge for the `λ > 4`
high-moment route.

If the paper-shape centered moment bound holds eventually for the scaled
eigenvalue coordinates of `ρ^Γ`, then the concrete non-PPT event
`¬ (ρ^Γ).PosSemidef` has the same eventual paper-shape probability bound.  The
genuine random-matrix content is exactly the visible `hBound` hypothesis. -/
theorem eventually_not_rhoGamma_posSemidef_measure_le_of_eventually_lintegral_bound_scaledRhoGamma
    {Ω : Type*} {σ : ℕ → Type*} [MeasurableSpace Ω] [∀ d : ℕ, Fintype (σ d)]
    (μ : ℕ → Measure Ω)
    (G : (d : ℕ) → RandomSampleMatrix Ω (Fin d) (Fin d) (σ d))
    (D : ℕ → ℝ) (m : ℕ → ℕ) (C α q c : ℝ)
    (hD : ∀ᶠ d : ℕ in Filter.atTop, 0 < D d)
    (hMeas : ∀ d : ℕ, AEMeasurable
      (fun ω : Ω => ENNReal.ofReal
        (∑ i : BipIndex (Fin d) (Fin d),
          (scaledRhoGammaEigenvalues (D d) (G d ω) i - 1) ^ (2 * m d))) (μ d))
    (hBound : ∀ᶠ d : ℕ in Filter.atTop,
      (∫⁻ ω, ENNReal.ofReal
        (∑ i : BipIndex (Fin d) (Fin d),
          (scaledRhoGammaEigenvalues (D d) (G d ω) i - 1) ^ (2 * m d)) ∂(μ d)) ≤
        ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
          ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))) :
    ∀ᶠ d : ℕ in Filter.atTop,
      μ d {ω : Ω | ¬ (rhoGamma (G d ω)).PosSemidef} ≤
        ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
          ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ))))) := by
  have hNeg : ∀ᶠ d : ℕ in Filter.atTop,
      μ d {ω : Ω |
          ∃ i : BipIndex (Fin d) (Fin d),
            scaledRhoGammaEigenvalues (D d) (G d ω) i < 0} ≤
        ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
          ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ))))) :=
    eventually_negative_event_measure_le_of_eventually_lintegral_bound_log_quadratic_rpow_log_dependent
      (μ := μ)
      (F := fun d ω => scaledRhoGammaEigenvalues (D d) (G d ω))
      (m := m) C α q c hMeas hBound
  filter_upwards [hD, hNeg] with d hDpos hNegd
  exact le_trans
    (measure_not_rhoGamma_posSemidef_le_exists_scaled_eigenvalue_neg
      (μ d) hDpos (G d)) hNegd

/-- Concrete model-facing finite-rate bridge at the paper scale `D = d^2`.

This is the endpoint a future growing-moment supplier should target for the
balanced model: an eventual paper-shape centered-moment bound for the
eigenvalues of `d^2 ρ^Γ - I` gives the same eventual paper-shape probability
bound for the concrete non-PPT event. -/
theorem eventually_not_rhoGamma_posSemidef_measure_le_of_eventually_lintegral_bound_dSquared_scaledRhoGamma
    {Ω : Type*} {σ : ℕ → Type*} [MeasurableSpace Ω] [∀ d : ℕ, Fintype (σ d)]
    (μ : ℕ → Measure Ω)
    (G : (d : ℕ) → RandomSampleMatrix Ω (Fin d) (Fin d) (σ d))
    (m : ℕ → ℕ) (C α q c : ℝ)
    (hMeas : ∀ d : ℕ, AEMeasurable
      (fun ω : Ω => ENNReal.ofReal
        (∑ i : BipIndex (Fin d) (Fin d),
          (scaledRhoGammaEigenvalues ((d : ℝ) ^ 2) (G d ω) i - 1) ^ (2 * m d))) (μ d))
    (hBound : ∀ᶠ d : ℕ in Filter.atTop,
      (∫⁻ ω, ENNReal.ofReal
        (∑ i : BipIndex (Fin d) (Fin d),
          (scaledRhoGammaEigenvalues ((d : ℝ) ^ 2) (G d ω) i - 1) ^ (2 * m d))
        ∂(μ d)) ≤
        ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
          ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))) :
    ∀ᶠ d : ℕ in Filter.atTop,
      μ d {ω : Ω | ¬ (rhoGamma (G d ω)).PosSemidef} ≤
        ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
          ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ))))) := by
  refine eventually_not_rhoGamma_posSemidef_measure_le_of_eventually_lintegral_bound_scaledRhoGamma
    (μ := μ) (G := G) (D := fun d : ℕ => (d : ℝ) ^ 2)
    (m := m) C α q c ?_ hMeas hBound
  filter_upwards [Filter.eventually_gt_atTop 0] with d hd
  exact sq_pos_of_pos (by exact_mod_cast hd : 0 < (d : ℝ))

/-- Concrete model-facing asymptotic bridge at the paper scale `D = d^2`.

If the eventual paper-shape centered-moment bound holds with a logarithmic
order constant satisfying `c log(1/q) > 2`, then the concrete non-PPT
probability tends to zero.  The theorem keeps the growing-moment estimate as
the visible `hBound` hypothesis. -/
theorem tendsto_not_rhoGamma_posSemidef_measure_zero_of_eventually_lintegral_bound_dSquared_scaledRhoGamma
    {Ω : Type*} {σ : ℕ → Type*} [MeasurableSpace Ω] [∀ d : ℕ, Fintype (σ d)]
    (μ : ℕ → Measure Ω)
    (G : (d : ℕ) → RandomSampleMatrix Ω (Fin d) (Fin d) (σ d))
    (m : ℕ → ℕ) (C α q c : ℝ)
    (hq : 0 < q) (hc : 2 < c * Real.log q⁻¹)
    (hMeas : ∀ d : ℕ, AEMeasurable
      (fun ω : Ω => ENNReal.ofReal
        (∑ i : BipIndex (Fin d) (Fin d),
          (scaledRhoGammaEigenvalues ((d : ℝ) ^ 2) (G d ω) i - 1) ^ (2 * m d))) (μ d))
    (hBound : ∀ᶠ d : ℕ in Filter.atTop,
      (∫⁻ ω, ENNReal.ofReal
        (∑ i : BipIndex (Fin d) (Fin d),
          (scaledRhoGammaEigenvalues ((d : ℝ) ^ 2) (G d ω) i - 1) ^ (2 * m d))
        ∂(μ d)) ≤
        ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
          ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))) :
    Filter.Tendsto
      (fun d : ℕ => μ d {ω : Ω | ¬ (rhoGamma (G d ω)).PosSemidef})
      Filter.atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hRate :
      Filter.Tendsto
        (fun d : ℕ => ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
          ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ))))))
        Filter.atTop (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal
      (const_mul_log_rpow_mul_quadratic_rpow_const_mul_log_tendsto_zero_of_two_lt_mul_log_inv
        C α q c hq hc)
  have hRateEvent : ∀ᶠ d : ℕ in Filter.atTop,
      ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
        ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ))))) ≤ ε :=
    (ENNReal.tendsto_nhds_zero.mp hRate) ε hε
  have hProbEvent :=
    eventually_not_rhoGamma_posSemidef_measure_le_of_eventually_lintegral_bound_dSquared_scaledRhoGamma
      (μ := μ) (G := G) (m := m) C α q c hMeas hBound
  filter_upwards [hProbEvent, hRateEvent] with d hProb hRateLe
  exact le_trans hProb hRateLe

/-- Concrete `λ > 4` model-facing asymptotic endpoint at the paper scale
`D = d^2`.

For every `λ > 4`, Lean chooses the edge slack `eps`, the decay ratio `q`, and
the logarithmic moment-order constant `c`.  The only random-matrix content left
visible is the eventual paper-shape centered-moment bound for the eigenvalues
of `d^2 ρ^Γ - I`. -/
theorem exists_log_order_constants_and_tendsto_not_rhoGamma_posSemidef_measure_zero_of_four_lt_dSquared_scaledRhoGamma
    {Ω : Type*} {σ : ℕ → Type*} [MeasurableSpace Ω] [∀ d : ℕ, Fintype (σ d)]
    (μ : ℕ → Measure Ω)
    (G : (d : ℕ) → RandomSampleMatrix Ω (Fin d) (Fin d) (σ d))
    (m : ℕ → ℕ) (lam C α : ℝ) (hlam : 4 < lam)
    (hMeas : ∀ d : ℕ, AEMeasurable
      (fun ω : Ω => ENNReal.ofReal
        (∑ i : BipIndex (Fin d) (Fin d),
          (scaledRhoGammaEigenvalues ((d : ℝ) ^ 2) (G d ω) i - 1) ^ (2 * m d))) (μ d)) :
    ∃ eps q c : ℝ,
      0 < eps ∧ q = (4 + eps) / lam ∧ 0 < q ∧ q < 1 ∧
        0 < c ∧ 2 < c * Real.log q⁻¹ ∧
          ((∀ᶠ d : ℕ in Filter.atTop,
            (∫⁻ ω, ENNReal.ofReal
              (∑ i : BipIndex (Fin d) (Fin d),
                (scaledRhoGammaEigenvalues ((d : ℝ) ^ 2) (G d ω) i - 1) ^
                  (2 * m d))
              ∂(μ d)) ≤
              ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
                ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))) →
            Filter.Tendsto
              (fun d : ℕ => μ d {ω : Ω | ¬ (rhoGamma (G d ω)).PosSemidef})
              Filter.atTop (nhds 0)) := by
  rcases exists_log_order_constants_of_four_lt hlam with
    ⟨eps, q, c, heps, hq_def, hq_pos, hq_lt_one, hc_pos, hc⟩
  refine ⟨eps, q, c, heps, hq_def, hq_pos, hq_lt_one, hc_pos, hc, ?_⟩
  intro hBound
  exact
    tendsto_not_rhoGamma_posSemidef_measure_zero_of_eventually_lintegral_bound_dSquared_scaledRhoGamma
      (μ := μ) (G := G) (m := m) C α q c hq_pos hc hMeas hBound

/-- Concrete `λ > 4` model-facing PPT endpoint at the paper scale `D = d^2`.

This is the article-facing complement form of
`exists_log_order_constants_and_tendsto_not_rhoGamma_posSemidef_measure_zero_of_four_lt_dSquared_scaledRhoGamma`:
under probability laws and measurability of the PPT event, the same visible
eventual centered-moment supplier implies that the real probability of PPT
tends to one. -/
theorem exists_log_order_constants_and_tendsto_rhoGamma_posSemidef_measureReal_one_of_four_lt_dSquared_scaledRhoGamma
    {Ω : Type*} {σ : ℕ → Type*} [MeasurableSpace Ω] [∀ d : ℕ, Fintype (σ d)]
    (μ : ℕ → Measure Ω)
    (G : (d : ℕ) → RandomSampleMatrix Ω (Fin d) (Fin d) (σ d))
    (m : ℕ → ℕ) (lam C α : ℝ) (hlam : 4 < lam)
    (hProb : ∀ d : ℕ, IsProbabilityMeasure (μ d))
    (hPPTMeas : ∀ d : ℕ, MeasurableSet
      {ω : Ω | (rhoGamma (G d ω)).PosSemidef})
    (hMeas : ∀ d : ℕ, AEMeasurable
      (fun ω : Ω => ENNReal.ofReal
        (∑ i : BipIndex (Fin d) (Fin d),
          (scaledRhoGammaEigenvalues ((d : ℝ) ^ 2) (G d ω) i - 1) ^ (2 * m d))) (μ d)) :
    ∃ eps q c : ℝ,
      0 < eps ∧ q = (4 + eps) / lam ∧ 0 < q ∧ q < 1 ∧
        0 < c ∧ 2 < c * Real.log q⁻¹ ∧
          ((∀ᶠ d : ℕ in Filter.atTop,
            (∫⁻ ω, ENNReal.ofReal
              (∑ i : BipIndex (Fin d) (Fin d),
                (scaledRhoGammaEigenvalues ((d : ℝ) ^ 2) (G d ω) i - 1) ^
                  (2 * m d))
              ∂(μ d)) ≤
              ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
                ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))) →
            Filter.Tendsto
              (fun d : ℕ => (μ d).real
                {ω : Ω | (rhoGamma (G d ω)).PosSemidef})
              Filter.atTop (nhds 1)) := by
  rcases
    exists_log_order_constants_and_tendsto_not_rhoGamma_posSemidef_measure_zero_of_four_lt_dSquared_scaledRhoGamma
      (μ := μ) (G := G) (m := m) (lam := lam) (C := C) (α := α) hlam hMeas
    with ⟨eps, q, c, heps, hq_def, hq_pos, hq_lt_one, hc_pos, hc, hNot⟩
  refine ⟨eps, q, c, heps, hq_def, hq_pos, hq_lt_one, hc_pos, hc, ?_⟩
  intro hBound
  have hNotTendsto := hNot hBound
  have hNotReal :
      Filter.Tendsto
        (fun d : ℕ =>
          (μ d {ω : Ω | ¬ (rhoGamma (G d ω)).PosSemidef}).toReal)
        Filter.atTop (nhds 0) := by
    simpa using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hNotTendsto
  have hTarget :
      Filter.Tendsto
        (fun d : ℕ =>
          1 - (μ d {ω : Ω | ¬ (rhoGamma (G d ω)).PosSemidef}).toReal)
        Filter.atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.sub hNotReal : Filter.Tendsto
      (fun d : ℕ =>
        (1 : ℝ) - (μ d {ω : Ω | ¬ (rhoGamma (G d ω)).PosSemidef}).toReal)
      Filter.atTop (nhds (1 - 0)))
  refine hTarget.congr' ?_
  filter_upwards with d
  letI : IsProbabilityMeasure (μ d) := hProb d
  have hFinite : IsFiniteMeasure (μ d) := inferInstance
  have hcompl := measureReal_compl (μ := μ d) (hPPTMeas d)
  have hUniv : (μ d).real Set.univ = 1 := by
    simp [Measure.real, IsProbabilityMeasure.measure_univ]
  have hNotSet :
      {ω : Ω | ¬ (rhoGamma (G d ω)).PosSemidef} =
        {ω : Ω | (rhoGamma (G d ω)).PosSemidef}ᶜ := rfl
  have hNotRealEq :
      (μ d {ω : Ω | ¬ (rhoGamma (G d ω)).PosSemidef}).toReal =
        (μ d).real {ω : Ω | (rhoGamma (G d ω)).PosSemidef}ᶜ := by
    rw [hNotSet]
    rfl
  linarith

/-- Concrete `λ > 4` PPT endpoint with sample-map measurability instead of a
raw PPT-event measurability hypothesis. -/
theorem exists_log_order_constants_and_tendsto_rhoGamma_posSemidef_measureReal_one_of_four_lt_dSquared_scaledRhoGamma_of_measurable
    {Ω : Type*} {σ : ℕ → Type*} [MeasurableSpace Ω] [∀ d : ℕ, Fintype (σ d)]
    (μ : ℕ → Measure Ω)
    (G : (d : ℕ) → RandomSampleMatrix Ω (Fin d) (Fin d) (σ d))
    (m : ℕ → ℕ) (lam C α : ℝ) (hlam : 4 < lam)
    (hProb : ∀ d : ℕ, IsProbabilityMeasure (μ d))
    (hGMeas : ∀ d : ℕ, Measurable (G d))
    (hMeas : ∀ d : ℕ, AEMeasurable
      (fun ω : Ω => ENNReal.ofReal
        (∑ i : BipIndex (Fin d) (Fin d),
          (scaledRhoGammaEigenvalues ((d : ℝ) ^ 2) (G d ω) i - 1) ^ (2 * m d))) (μ d)) :
    ∃ eps q c : ℝ,
      0 < eps ∧ q = (4 + eps) / lam ∧ 0 < q ∧ q < 1 ∧
        0 < c ∧ 2 < c * Real.log q⁻¹ ∧
          ((∀ᶠ d : ℕ in Filter.atTop,
            (∫⁻ ω, ENNReal.ofReal
              (∑ i : BipIndex (Fin d) (Fin d),
                (scaledRhoGammaEigenvalues ((d : ℝ) ^ 2) (G d ω) i - 1) ^
                  (2 * m d))
              ∂(μ d)) ≤
              ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
                ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))) →
            Filter.Tendsto
              (fun d : ℕ => (μ d).real
                {ω : Ω | (rhoGamma (G d ω)).PosSemidef})
              Filter.atTop (nhds 1)) := by
  exact
    exists_log_order_constants_and_tendsto_rhoGamma_posSemidef_measureReal_one_of_four_lt_dSquared_scaledRhoGamma
      (μ := μ) (G := G) (m := m) (lam := lam) (C := C) (α := α) hlam
      hProb
      (fun d => measurableSet_rhoGamma_posSemidef_of_measurable (G := G d) (hGMeas d))
      hMeas

/-- Concrete `λ > 4` PPT endpoint whose growing-moment supplier is stated as
the matrix trace moment `Re Tr((d^2 ρ^Γ - I)^(2m))`.

This keeps the a.e. measurability input for the eigenvalue-centered observable
visible, but lets the hard random-matrix estimate be supplied in the usual
trace-moment form. -/
theorem exists_log_order_constants_and_tendsto_rhoGamma_posSemidef_measureReal_one_of_four_lt_dSquared_traceMomentBound
    {Ω : Type*} {σ : ℕ → Type*} [MeasurableSpace Ω] [∀ d : ℕ, Fintype (σ d)]
    (μ : ℕ → Measure Ω)
    (G : (d : ℕ) → RandomSampleMatrix Ω (Fin d) (Fin d) (σ d))
    (m : ℕ → ℕ) (lam C α : ℝ) (hlam : 4 < lam)
    (hProb : ∀ d : ℕ, IsProbabilityMeasure (μ d))
    (hGMeas : ∀ d : ℕ, Measurable (G d))
    (hMeas : ∀ d : ℕ, AEMeasurable
      (fun ω : Ω => ENNReal.ofReal
        (∑ i : BipIndex (Fin d) (Fin d),
          (scaledRhoGammaEigenvalues ((d : ℝ) ^ 2) (G d ω) i - 1) ^ (2 * m d))) (μ d)) :
    ∃ eps q c : ℝ,
      0 < eps ∧ q = (4 + eps) / lam ∧ 0 < q ∧ q < 1 ∧
        0 < c ∧ 2 < c * Real.log q⁻¹ ∧
          ((∀ᶠ d : ℕ in Filter.atTop,
            (∫⁻ ω, ENNReal.ofReal
              (RCLike.re (((((d : ℝ) ^ 2 : ℂ) • rhoGamma (G d ω) - 1) ^
                (2 * m d)).trace))
              ∂(μ d)) ≤
              ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
                ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))) →
            Filter.Tendsto
              (fun d : ℕ => (μ d).real
                {ω : Ω | (rhoGamma (G d ω)).PosSemidef})
              Filter.atTop (nhds 1)) := by
  rcases
    exists_log_order_constants_and_tendsto_rhoGamma_posSemidef_measureReal_one_of_four_lt_dSquared_scaledRhoGamma_of_measurable
      (μ := μ) (G := G) (m := m) (lam := lam) (C := C) (α := α) hlam
      hProb hGMeas hMeas
    with ⟨eps, q, c, heps, hq_def, hq_pos, hq_lt_one, hc_pos, hc, hEndpoint⟩
  refine ⟨eps, q, c, heps, hq_def, hq_pos, hq_lt_one, hc_pos, hc, ?_⟩
  intro hTraceBound
  refine hEndpoint ?_
  filter_upwards [hTraceBound] with d hd
  have hfun :
      (fun ω : Ω => ENNReal.ofReal
        (∑ i : BipIndex (Fin d) (Fin d),
          (scaledRhoGammaEigenvalues ((d : ℝ) ^ 2) (G d ω) i - 1) ^ (2 * m d))) =
      (fun ω : Ω => ENNReal.ofReal
        (RCLike.re (((((d : ℝ) ^ 2 : ℂ) • rhoGamma (G d ω) - 1) ^
          (2 * m d)).trace))) := by
    funext ω
    rw [← rhoGamma_centered_trace_re_eq_sum_scaledRhoGammaEigenvalues
      (((d : ℝ) ^ 2)) (G d ω) (2 * m d)]
    simp [Complex.ofReal_pow]
  simpa [hfun] using hd

/-- Sharp concrete `λ > 4` PPT endpoint for the trace-moment route.

Compared with
`exists_log_order_constants_and_tendsto_rhoGamma_posSemidef_measureReal_one_of_four_lt_dSquared_traceMomentBound`,
this endpoint discharges the eigenvalue-sum a.e. measurability input from the
sample-map measurability hypothesis.  The only mathematical supplier left
visible is the usual trace-moment estimate
`Re Tr((d^2 ρ^Γ - I)^(2m))`. -/
theorem exists_log_order_constants_and_tendsto_rhoGamma_posSemidef_measureReal_one_of_four_lt_dSquared_traceMomentBound_of_measurable
    {Ω : Type*} {σ : ℕ → Type*} [MeasurableSpace Ω] [∀ d : ℕ, Fintype (σ d)]
    (μ : ℕ → Measure Ω)
    (G : (d : ℕ) → RandomSampleMatrix Ω (Fin d) (Fin d) (σ d))
    (m : ℕ → ℕ) (lam C α : ℝ) (hlam : 4 < lam)
    (hProb : ∀ d : ℕ, IsProbabilityMeasure (μ d))
    (hGMeas : ∀ d : ℕ, Measurable (G d)) :
    ∃ eps q c : ℝ,
      0 < eps ∧ q = (4 + eps) / lam ∧ 0 < q ∧ q < 1 ∧
        0 < c ∧ 2 < c * Real.log q⁻¹ ∧
          ((∀ᶠ d : ℕ in Filter.atTop,
            (∫⁻ ω, ENNReal.ofReal
              (RCLike.re (((((d : ℝ) ^ 2 : ℂ) • rhoGamma (G d ω) - 1) ^
                (2 * m d)).trace))
              ∂(μ d)) ≤
              ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
                ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))) →
            Filter.Tendsto
              (fun d : ℕ => (μ d).real
                {ω : Ω | (rhoGamma (G d ω)).PosSemidef})
              Filter.atTop (nhds 1)) := by
  refine
    exists_log_order_constants_and_tendsto_rhoGamma_posSemidef_measureReal_one_of_four_lt_dSquared_traceMomentBound
      (μ := μ) (G := G) (m := m) (lam := lam) (C := C) (α := α) hlam
      hProb hGMeas ?_
  intro d
  exact
    aemeasurable_scaledRhoGammaEigenvalueCenteredPowerSum_of_measurable
      (μ d) (hGMeas d) ((d : ℝ) ^ 2) (2 * m d)

/-- Finite-rate controlled trace-moment concrete endpoint at the paper scale
`D = d^2`.

Any eventual upper bound `δ d` for the unnormalised centered trace moment
directly bounds the concrete non-PPT probability by the same `δ d`. -/
theorem eventually_not_rhoGamma_posSemidef_measure_le_of_eventually_traceMoment_bound
    {Ω : Type*} {σ : ℕ → Type*} [MeasurableSpace Ω] [∀ d : ℕ, Fintype (σ d)]
    (μ : ℕ → Measure Ω)
    (G : (d : ℕ) → RandomSampleMatrix Ω (Fin d) (Fin d) (σ d))
    (m : ℕ → ℕ) (δ : ℕ → ENNReal)
    (hGMeas : ∀ d : ℕ, Measurable (G d))
    (hBound : ∀ᶠ d : ℕ in Filter.atTop,
      (∫⁻ ω, ENNReal.ofReal
        (RCLike.re (((((d : ℝ) ^ 2 : ℂ) • rhoGamma (G d ω) - 1) ^
          (2 * m d)).trace)) ∂(μ d)) ≤ δ d) :
    ∀ᶠ d : ℕ in Filter.atTop,
      μ d {ω : Ω | ¬ (rhoGamma (G d ω)).PosSemidef} ≤ δ d := by
  filter_upwards [Filter.eventually_gt_atTop 0, hBound] with d hd hTraceLe
  have hDpos : 0 < ((d : ℝ) ^ 2) :=
    sq_pos_of_pos (by exact_mod_cast hd : 0 < (d : ℝ))
  have hMeas :
      AEMeasurable
        (fun ω : Ω => ENNReal.ofReal
          (∑ i : BipIndex (Fin d) (Fin d),
            (scaledRhoGammaEigenvalues ((d : ℝ) ^ 2) (G d ω) i - 1) ^ (2 * m d)))
        (μ d) :=
    aemeasurable_scaledRhoGammaEigenvalueCenteredPowerSum_of_measurable
      (μ d) (hGMeas d) ((d : ℝ) ^ 2) (2 * m d)
  have hTraceAsSum :
      (fun ω : Ω => ENNReal.ofReal
        (∑ i : BipIndex (Fin d) (Fin d),
          (scaledRhoGammaEigenvalues ((d : ℝ) ^ 2) (G d ω) i - 1) ^ (2 * m d))) =
      (fun ω : Ω => ENNReal.ofReal
        (RCLike.re (((((d : ℝ) ^ 2 : ℂ) • rhoGamma (G d ω) - 1) ^
          (2 * m d)).trace))) := by
    funext ω
    rw [← rhoGamma_centered_trace_re_eq_sum_scaledRhoGammaEigenvalues
      (((d : ℝ) ^ 2)) (G d ω) (2 * m d)]
    simp [Complex.ofReal_pow]
  have hSumBound :
      (∫⁻ ω, ENNReal.ofReal
        (∑ i : BipIndex (Fin d) (Fin d),
          (scaledRhoGammaEigenvalues ((d : ℝ) ^ 2) (G d ω) i - 1) ^ (2 * m d))
        ∂(μ d)) ≤ δ d := by
    simpa [hTraceAsSum] using hTraceLe
  have hNeg :
      μ d {ω : Ω |
          ∃ i : BipIndex (Fin d) (Fin d),
            scaledRhoGammaEigenvalues ((d : ℝ) ^ 2) (G d ω) i < 0} ≤ δ d :=
    negative_event_measure_le_of_lintegral_centered_even_moment_le
      (μ d)
      (fun ω : Ω => scaledRhoGammaEigenvalues ((d : ℝ) ^ 2) (G d ω))
      (m d) hMeas hSumBound
  exact le_trans
    (measure_not_rhoGamma_posSemidef_le_exists_scaled_eigenvalue_neg
      (μ d) hDpos (G d)) hNeg

/-- Real-valued finite-rate controlled trace-moment concrete endpoint at the
paper scale `D = d^2`.

Most moment estimates are stated with an ordinary real rate `δ d`.  This
wrapper keeps that supplier shape and lifts the rate to `ENNReal` only at the
probability endpoint. -/
theorem eventually_not_rhoGamma_posSemidef_measure_le_of_eventually_traceMoment_bound_ofReal
    {Ω : Type*} {σ : ℕ → Type*} [MeasurableSpace Ω] [∀ d : ℕ, Fintype (σ d)]
    (μ : ℕ → Measure Ω)
    (G : (d : ℕ) → RandomSampleMatrix Ω (Fin d) (Fin d) (σ d))
    (m : ℕ → ℕ) (δ : ℕ → ℝ)
    (hGMeas : ∀ d : ℕ, Measurable (G d))
    (hBound : ∀ᶠ d : ℕ in Filter.atTop,
      (∫⁻ ω, ENNReal.ofReal
        (RCLike.re (((((d : ℝ) ^ 2 : ℂ) • rhoGamma (G d ω) - 1) ^
          (2 * m d)).trace)) ∂(μ d)) ≤ ENNReal.ofReal (δ d)) :
    ∀ᶠ d : ℕ in Filter.atTop,
      μ d {ω : Ω | ¬ (rhoGamma (G d ω)).PosSemidef} ≤ ENNReal.ofReal (δ d) := by
  exact
    eventually_not_rhoGamma_posSemidef_measure_le_of_eventually_traceMoment_bound
      (μ := μ) (G := G) (m := m)
      (δ := fun d : ℕ => ENNReal.ofReal (δ d)) hGMeas hBound

/-- Real-valued asymptotic controlled trace-moment endpoint at the paper scale
`D = d^2`.

If a real rate `δ d` tends to zero and eventually bounds the lifted centered
trace moment, then the concrete non-PPT probability tends to zero. -/
theorem tendsto_not_rhoGamma_posSemidef_measure_zero_of_eventually_traceMoment_bound_ofReal
    {Ω : Type*} {σ : ℕ → Type*} [MeasurableSpace Ω] [∀ d : ℕ, Fintype (σ d)]
    (μ : ℕ → Measure Ω)
    (G : (d : ℕ) → RandomSampleMatrix Ω (Fin d) (Fin d) (σ d))
    (m : ℕ → ℕ) (δ : ℕ → ℝ)
    (hGMeas : ∀ d : ℕ, Measurable (G d))
    (hBound : ∀ᶠ d : ℕ in Filter.atTop,
      (∫⁻ ω, ENNReal.ofReal
        (RCLike.re (((((d : ℝ) ^ 2 : ℂ) • rhoGamma (G d ω) - 1) ^
          (2 * m d)).trace)) ∂(μ d)) ≤ ENNReal.ofReal (δ d))
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun d : ℕ => μ d {ω : Ω | ¬ (rhoGamma (G d ω)).PosSemidef})
      Filter.atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hFinite :=
    eventually_not_rhoGamma_posSemidef_measure_le_of_eventually_traceMoment_bound_ofReal
      (μ := μ) (G := G) (m := m) (δ := δ) hGMeas hBound
  have hδenn : Filter.Tendsto (fun d : ℕ => ENNReal.ofReal (δ d))
      Filter.atTop (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal hδ
  have hδevent : ∀ᶠ d : ℕ in Filter.atTop, ENNReal.ofReal (δ d) ≤ ε :=
    (ENNReal.tendsto_nhds_zero.mp hδenn) ε hε
  filter_upwards [hFinite, hδevent] with d hProbLe hδle
  exact le_trans hProbLe hδle

/-- Real-valued asymptotic controlled trace-moment concrete PPT endpoint.

Under probability laws and measurable sample maps, an eventual real-rate trace
bound with `δ d → 0` implies that the real probability of PPT tends to one. -/
theorem tendsto_rhoGamma_posSemidef_measureReal_one_of_eventually_traceMoment_bound_ofReal
    {Ω : Type*} {σ : ℕ → Type*} [MeasurableSpace Ω] [∀ d : ℕ, Fintype (σ d)]
    (μ : ℕ → Measure Ω)
    (G : (d : ℕ) → RandomSampleMatrix Ω (Fin d) (Fin d) (σ d))
    (m : ℕ → ℕ) (δ : ℕ → ℝ)
    (hProb : ∀ d : ℕ, IsProbabilityMeasure (μ d))
    (hGMeas : ∀ d : ℕ, Measurable (G d))
    (hBound : ∀ᶠ d : ℕ in Filter.atTop,
      (∫⁻ ω, ENNReal.ofReal
        (RCLike.re (((((d : ℝ) ^ 2 : ℂ) • rhoGamma (G d ω) - 1) ^
          (2 * m d)).trace)) ∂(μ d)) ≤ ENNReal.ofReal (δ d))
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun d : ℕ => (μ d).real {ω : Ω | (rhoGamma (G d ω)).PosSemidef})
      Filter.atTop (nhds 1) := by
  have hNotTendsto :=
    tendsto_not_rhoGamma_posSemidef_measure_zero_of_eventually_traceMoment_bound_ofReal
      (μ := μ) (G := G) (m := m) (δ := δ) hGMeas hBound hδ
  have hNotReal :
      Filter.Tendsto
        (fun d : ℕ =>
          (μ d {ω : Ω | ¬ (rhoGamma (G d ω)).PosSemidef}).toReal)
        Filter.atTop (nhds 0) := by
    simpa using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hNotTendsto
  have hTarget :
      Filter.Tendsto
        (fun d : ℕ =>
          1 - (μ d {ω : Ω | ¬ (rhoGamma (G d ω)).PosSemidef}).toReal)
        Filter.atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.sub hNotReal : Filter.Tendsto
      (fun d : ℕ =>
        (1 : ℝ) - (μ d {ω : Ω | ¬ (rhoGamma (G d ω)).PosSemidef}).toReal)
      Filter.atTop (nhds (1 - 0)))
  refine hTarget.congr' ?_
  filter_upwards with d
  letI : IsProbabilityMeasure (μ d) := hProb d
  have hPPTMeas :
      MeasurableSet {ω : Ω | (rhoGamma (G d ω)).PosSemidef} :=
    measurableSet_rhoGamma_posSemidef_of_measurable (G := G d) (hGMeas d)
  have hcompl := measureReal_compl (μ := μ d) hPPTMeas
  have hUniv : (μ d).real Set.univ = 1 := by
    simp [Measure.real, IsProbabilityMeasure.measure_univ]
  have hNotSet :
      {ω : Ω | ¬ (rhoGamma (G d ω)).PosSemidef} =
        {ω : Ω | (rhoGamma (G d ω)).PosSemidef}ᶜ := rfl
  have hNotRealEq :
      (μ d {ω : Ω | ¬ (rhoGamma (G d ω)).PosSemidef}).toReal =
        (μ d).real {ω : Ω | (rhoGamma (G d ω)).PosSemidef}ᶜ := by
    rw [hNotSet]
    rfl
  linarith

/-- Wishart/radial real-rate PPT endpoint.

This is the same article-facing conclusion as
`tendsto_rhoGamma_posSemidef_measureReal_one_of_eventually_traceMoment_bound_ofReal`,
but the hard supplier is stated in the natural Wishart normalization:
the centered trace moment of
`((d^2 * #σ_d / frobeniusMass G_d) • W_d^Γ - I)`. -/
theorem tendsto_rhoGamma_posSemidef_measureReal_one_of_eventually_wishartGamma_frobeniusMass_traceMoment_bound_ofReal
    {Ω : Type*} {σ : ℕ → Type*} [MeasurableSpace Ω] [∀ d : ℕ, Fintype (σ d)]
    (μ : ℕ → Measure Ω)
    (G : (d : ℕ) → RandomSampleMatrix Ω (Fin d) (Fin d) (σ d))
    (m : ℕ → ℕ) (δ : ℕ → ℝ)
    (hProb : ∀ d : ℕ, IsProbabilityMeasure (μ d))
    (hGMeas : ∀ d : ℕ, Measurable (G d))
    (hσ : ∀ᶠ d : ℕ in Filter.atTop, 0 < Fintype.card (σ d))
    (hBound : ∀ᶠ d : ℕ in Filter.atTop,
      (∫⁻ ω, ENNReal.ofReal
        (RCLike.re
          (((((((d : ℝ) ^ 2 * (Fintype.card (σ d) : ℝ) /
            frobeniusMass (G d ω) : ℝ) : ℂ) •
            wishartGamma (G d ω) - 1) ^ (2 * m d)).trace))) ∂(μ d)) ≤
        ENNReal.ofReal (δ d))
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun d : ℕ => (μ d).real {ω : Ω | (rhoGamma (G d ω)).PosSemidef})
      Filter.atTop (nhds 1) := by
  refine
    tendsto_rhoGamma_posSemidef_measureReal_one_of_eventually_traceMoment_bound_ofReal
      (μ := μ) (G := G) (m := m) (δ := δ) hProb hGMeas ?_ hδ
  filter_upwards [hσ, hBound] with d hdσ hdBound
  calc
    (∫⁻ ω, ENNReal.ofReal
      (RCLike.re (((((d : ℝ) ^ 2 : ℂ) • rhoGamma (G d ω) - 1) ^
        (2 * m d)).trace)) ∂(μ d))
        = (∫⁻ ω, ENNReal.ofReal
          (RCLike.re
            (((((((d : ℝ) ^ 2 * (Fintype.card (σ d) : ℝ) /
              frobeniusMass (G d ω) : ℝ) : ℂ) •
              wishartGamma (G d ω) - 1) ^ (2 * m d)).trace))) ∂(μ d)) := by
          apply lintegral_congr_ae
          filter_upwards with ω
          rw [rhoGamma_eq_card_div_frobeniusMass_smul_wishartGamma hdσ (G d ω)]
          simp [smul_smul, div_eq_mul_inv, mul_assoc]
    _ ≤ ENNReal.ofReal (δ d) := hdBound

/-- Varying-space finite-rate Wishart/radial non-PPT endpoint.

This is the dimension-dependent probability-space analogue of the fixed-space
finite-rate bridge.  A native Wishart/Frobenius-mass trace-moment bound over
`Ω d` directly gives the same rate for the concrete non-PPT event over `Ω d`.
The trace-moment estimate itself remains the visible random-matrix input. -/
theorem eventually_not_rhoGamma_posSemidef_measure_le_of_eventually_varying_wishartGamma_frobeniusMass_traceMoment_bound_ofReal
    {Ω σ : ℕ → Type*}
    [∀ d : ℕ, MeasurableSpace (Ω d)] [∀ d : ℕ, Fintype (σ d)]
    (μ : (d : ℕ) → Measure (Ω d))
    (G : (d : ℕ) → RandomSampleMatrix (Ω d) (Fin d) (Fin d) (σ d))
    (m : ℕ → ℕ) (δ : ℕ → ℝ)
    (hGMeas : ∀ d : ℕ, Measurable (G d))
    (hσ : ∀ᶠ d : ℕ in Filter.atTop, 0 < Fintype.card (σ d))
    (hBound : ∀ᶠ d : ℕ in Filter.atTop,
      (∫⁻ ω, ENNReal.ofReal
        (RCLike.re
          (((((((d : ℝ) ^ 2 * (Fintype.card (σ d) : ℝ) /
            frobeniusMass (G d ω) : ℝ) : ℂ) •
            wishartGamma (G d ω) - 1) ^ (2 * m d)).trace))) ∂(μ d)) ≤
        ENNReal.ofReal (δ d)) :
    ∀ᶠ d : ℕ in Filter.atTop,
      μ d {ω : Ω d | ¬ (rhoGamma (G d ω)).PosSemidef} ≤
        ENNReal.ofReal (δ d) := by
  filter_upwards [Filter.eventually_gt_atTop 0, hσ, hBound] with d hd hdσ hdBound
  have hDpos : 0 < ((d : ℝ) ^ 2) :=
    sq_pos_of_pos (by exact_mod_cast hd : 0 < (d : ℝ))
  have hMeas :
      AEMeasurable
        (fun ω : Ω d => ENNReal.ofReal
          (∑ i : BipIndex (Fin d) (Fin d),
            (scaledRhoGammaEigenvalues ((d : ℝ) ^ 2) (G d ω) i - 1) ^
              (2 * m d)))
        (μ d) :=
    aemeasurable_scaledRhoGammaEigenvalueCenteredPowerSum_of_measurable
      (μ d) (hGMeas d) ((d : ℝ) ^ 2) (2 * m d)
  have hTraceAsRho :
      (fun ω : Ω d => ENNReal.ofReal
        (∑ i : BipIndex (Fin d) (Fin d),
          (scaledRhoGammaEigenvalues ((d : ℝ) ^ 2) (G d ω) i - 1) ^
            (2 * m d))) =
      (fun ω : Ω d => ENNReal.ofReal
        (RCLike.re (((((d : ℝ) ^ 2 : ℂ) • rhoGamma (G d ω) - 1) ^
          (2 * m d)).trace))) := by
    funext ω
    rw [← rhoGamma_centered_trace_re_eq_sum_scaledRhoGammaEigenvalues
      (((d : ℝ) ^ 2)) (G d ω) (2 * m d)]
    simp [Complex.ofReal_pow]
  have hRhoTraceEqWishartTrace :
      (∫⁻ ω, ENNReal.ofReal
        (RCLike.re (((((d : ℝ) ^ 2 : ℂ) • rhoGamma (G d ω) - 1) ^
          (2 * m d)).trace)) ∂(μ d)) =
      (∫⁻ ω, ENNReal.ofReal
        (RCLike.re
          (((((((d : ℝ) ^ 2 * (Fintype.card (σ d) : ℝ) /
            frobeniusMass (G d ω) : ℝ) : ℂ) •
            wishartGamma (G d ω) - 1) ^ (2 * m d)).trace))) ∂(μ d)) := by
    apply lintegral_congr_ae
    filter_upwards with ω
    rw [rhoGamma_eq_card_div_frobeniusMass_smul_wishartGamma hdσ (G d ω)]
    simp [smul_smul, div_eq_mul_inv, mul_assoc]
  have hMomentLe :
      (∫⁻ ω, ENNReal.ofReal
        (∑ i : BipIndex (Fin d) (Fin d),
          (scaledRhoGammaEigenvalues ((d : ℝ) ^ 2) (G d ω) i - 1) ^
            (2 * m d))
        ∂(μ d)) ≤ ENNReal.ofReal (δ d) := by
    calc
      (∫⁻ ω, ENNReal.ofReal
        (∑ i : BipIndex (Fin d) (Fin d),
          (scaledRhoGammaEigenvalues ((d : ℝ) ^ 2) (G d ω) i - 1) ^
            (2 * m d))
        ∂(μ d))
          = (∫⁻ ω, ENNReal.ofReal
            (RCLike.re (((((d : ℝ) ^ 2 : ℂ) • rhoGamma (G d ω) - 1) ^
              (2 * m d)).trace)) ∂(μ d)) := by
              simp [hTraceAsRho]
      _ = (∫⁻ ω, ENNReal.ofReal
            (RCLike.re
              (((((((d : ℝ) ^ 2 * (Fintype.card (σ d) : ℝ) /
                frobeniusMass (G d ω) : ℝ) : ℂ) •
                wishartGamma (G d ω) - 1) ^ (2 * m d)).trace))) ∂(μ d)) :=
              hRhoTraceEqWishartTrace
      _ ≤ ENNReal.ofReal (δ d) := hdBound
  have hNeg :
      μ d {ω : Ω d |
          ∃ i : BipIndex (Fin d) (Fin d),
            scaledRhoGammaEigenvalues ((d : ℝ) ^ 2) (G d ω) i < 0} ≤
        ENNReal.ofReal (δ d) :=
    negative_event_measure_le_of_lintegral_centered_even_moment_le
      (μ d)
      (fun ω : Ω d => scaledRhoGammaEigenvalues ((d : ℝ) ^ 2) (G d ω))
      (m d) hMeas hMomentLe
  exact le_trans
    (measure_not_rhoGamma_posSemidef_le_exists_scaled_eigenvalue_neg
      (μ d) hDpos (G d)) hNeg

/-- Direct controlled-moment concrete endpoint at the paper scale `D = d^2`.

If the unnormalised centered trace moment
`∫⁻ ω, ofReal (Re Tr((d^2ρ^Γ-I)^(2m_d)))` tends to zero, then the concrete
non-PPT probability tends to zero.  This is the clean asymptotic form behind
the finite-rate `λ > 4` package. -/
theorem tendsto_not_rhoGamma_posSemidef_measure_zero_of_traceMoment_tendsto_zero
    {Ω : Type*} {σ : ℕ → Type*} [MeasurableSpace Ω] [∀ d : ℕ, Fintype (σ d)]
    (μ : ℕ → Measure Ω)
    (G : (d : ℕ) → RandomSampleMatrix Ω (Fin d) (Fin d) (σ d))
    (m : ℕ → ℕ)
    (hGMeas : ∀ d : ℕ, Measurable (G d))
    (hMoment : Filter.Tendsto
      (fun d : ℕ =>
        ∫⁻ ω, ENNReal.ofReal
          (RCLike.re (((((d : ℝ) ^ 2 : ℂ) • rhoGamma (G d ω) - 1) ^
            (2 * m d)).trace)) ∂(μ d))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun d : ℕ => μ d {ω : Ω | ¬ (rhoGamma (G d ω)).PosSemidef})
      Filter.atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero] at hMoment ⊢
  intro ε hε
  have hMomentEv := hMoment ε hε
  filter_upwards [Filter.eventually_gt_atTop 0, hMomentEv] with d hd hTraceLe
  have hDpos : 0 < ((d : ℝ) ^ 2) :=
    sq_pos_of_pos (by exact_mod_cast hd : 0 < (d : ℝ))
  have hMeas :
      AEMeasurable
        (fun ω : Ω => ENNReal.ofReal
          (∑ i : BipIndex (Fin d) (Fin d),
            (scaledRhoGammaEigenvalues ((d : ℝ) ^ 2) (G d ω) i - 1) ^ (2 * m d)))
        (μ d) :=
    aemeasurable_scaledRhoGammaEigenvalueCenteredPowerSum_of_measurable
      (μ d) (hGMeas d) ((d : ℝ) ^ 2) (2 * m d)
  have hNeg :
      μ d {ω : Ω |
          ∃ i : BipIndex (Fin d) (Fin d),
            scaledRhoGammaEigenvalues ((d : ℝ) ^ 2) (G d ω) i < 0} ≤
        ∫⁻ ω, ENNReal.ofReal
          (∑ i : BipIndex (Fin d) (Fin d),
            (scaledRhoGammaEigenvalues ((d : ℝ) ^ 2) (G d ω) i - 1) ^ (2 * m d))
          ∂(μ d) :=
    negative_event_measure_le_lintegral_centered_even_moment
      (μ d)
      (fun ω : Ω => scaledRhoGammaEigenvalues ((d : ℝ) ^ 2) (G d ω))
      (m d) hMeas
  have hTraceAsSum :
      (fun ω : Ω => ENNReal.ofReal
        (∑ i : BipIndex (Fin d) (Fin d),
          (scaledRhoGammaEigenvalues ((d : ℝ) ^ 2) (G d ω) i - 1) ^ (2 * m d))) =
      (fun ω : Ω => ENNReal.ofReal
        (RCLike.re (((((d : ℝ) ^ 2 : ℂ) • rhoGamma (G d ω) - 1) ^
          (2 * m d)).trace))) := by
    funext ω
    rw [← rhoGamma_centered_trace_re_eq_sum_scaledRhoGammaEigenvalues
      (((d : ℝ) ^ 2)) (G d ω) (2 * m d)]
    simp [Complex.ofReal_pow]
  have hMomentLe :
      (∫⁻ ω, ENNReal.ofReal
        (∑ i : BipIndex (Fin d) (Fin d),
          (scaledRhoGammaEigenvalues ((d : ℝ) ^ 2) (G d ω) i - 1) ^ (2 * m d))
        ∂(μ d)) ≤ ε := by
    simpa [hTraceAsSum] using hTraceLe
  exact le_trans
    (le_trans
      (measure_not_rhoGamma_posSemidef_le_exists_scaled_eigenvalue_neg
        (μ d) hDpos (G d)) hNeg)
    hMomentLe

/-- Direct controlled-moment concrete PPT endpoint.

Under probability laws and measurable sample maps, a centered trace moment
tending to zero implies that the real probability of PPT tends to one. -/
theorem tendsto_rhoGamma_posSemidef_measureReal_one_of_traceMoment_tendsto_zero
    {Ω : Type*} {σ : ℕ → Type*} [MeasurableSpace Ω] [∀ d : ℕ, Fintype (σ d)]
    (μ : ℕ → Measure Ω)
    (G : (d : ℕ) → RandomSampleMatrix Ω (Fin d) (Fin d) (σ d))
    (m : ℕ → ℕ)
    (hProb : ∀ d : ℕ, IsProbabilityMeasure (μ d))
    (hGMeas : ∀ d : ℕ, Measurable (G d))
    (hMoment : Filter.Tendsto
      (fun d : ℕ =>
        ∫⁻ ω, ENNReal.ofReal
          (RCLike.re (((((d : ℝ) ^ 2 : ℂ) • rhoGamma (G d ω) - 1) ^
            (2 * m d)).trace)) ∂(μ d))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun d : ℕ => (μ d).real {ω : Ω | (rhoGamma (G d ω)).PosSemidef})
      Filter.atTop (nhds 1) := by
  have hNotTendsto :=
    tendsto_not_rhoGamma_posSemidef_measure_zero_of_traceMoment_tendsto_zero
      (μ := μ) (G := G) (m := m) hGMeas hMoment
  have hNotReal :
      Filter.Tendsto
        (fun d : ℕ =>
          (μ d {ω : Ω | ¬ (rhoGamma (G d ω)).PosSemidef}).toReal)
        Filter.atTop (nhds 0) := by
    simpa using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hNotTendsto
  have hTarget :
      Filter.Tendsto
        (fun d : ℕ =>
          1 - (μ d {ω : Ω | ¬ (rhoGamma (G d ω)).PosSemidef}).toReal)
        Filter.atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.sub hNotReal : Filter.Tendsto
      (fun d : ℕ =>
        (1 : ℝ) - (μ d {ω : Ω | ¬ (rhoGamma (G d ω)).PosSemidef}).toReal)
      Filter.atTop (nhds (1 - 0)))
  refine hTarget.congr' ?_
  filter_upwards with d
  letI : IsProbabilityMeasure (μ d) := hProb d
  have hPPTMeas :
      MeasurableSet {ω : Ω | (rhoGamma (G d ω)).PosSemidef} :=
    measurableSet_rhoGamma_posSemidef_of_measurable (G := G d) (hGMeas d)
  have hcompl := measureReal_compl (μ := μ d) hPPTMeas
  have hUniv : (μ d).real Set.univ = 1 := by
    simp [Measure.real, IsProbabilityMeasure.measure_univ]
  have hNotSet :
      {ω : Ω | ¬ (rhoGamma (G d ω)).PosSemidef} =
        {ω : Ω | (rhoGamma (G d ω)).PosSemidef}ᶜ := rfl
  have hNotRealEq :
      (μ d {ω : Ω | ¬ (rhoGamma (G d ω)).PosSemidef}).toReal =
        (μ d).real {ω : Ω | (rhoGamma (G d ω)).PosSemidef}ᶜ := by
    rw [hNotSet]
    rfl
  linarith

/-- Direct Wishart/radial controlled-moment concrete PPT endpoint.

This is the source-explicit asymptotic form of the logarithmic-moment route:
if the unnormalised centered trace moment of the Frobenius-mass-scaled
Wishart partial transpose tends to zero, then the real PPT probability tends
to one.  The remaining hard input is exactly the displayed moment convergence. -/
theorem tendsto_rhoGamma_posSemidef_measureReal_one_of_wishartGamma_frobeniusMass_traceMoment_tendsto_zero
    {Ω : Type*} {σ : ℕ → Type*} [MeasurableSpace Ω] [∀ d : ℕ, Fintype (σ d)]
    (μ : ℕ → Measure Ω)
    (G : (d : ℕ) → RandomSampleMatrix Ω (Fin d) (Fin d) (σ d))
    (m : ℕ → ℕ)
    (hProb : ∀ d : ℕ, IsProbabilityMeasure (μ d))
    (hGMeas : ∀ d : ℕ, Measurable (G d))
    (hσ : ∀ᶠ d : ℕ in Filter.atTop, 0 < Fintype.card (σ d))
    (hMoment : Filter.Tendsto
      (fun d : ℕ =>
        ∫⁻ ω, ENNReal.ofReal
          (RCLike.re
            (((((((d : ℝ) ^ 2 * (Fintype.card (σ d) : ℝ) /
              frobeniusMass (G d ω) : ℝ) : ℂ) •
              wishartGamma (G d ω) - 1) ^ (2 * m d)).trace))) ∂(μ d))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun d : ℕ => (μ d).real {ω : Ω | (rhoGamma (G d ω)).PosSemidef})
      Filter.atTop (nhds 1) := by
  refine
    tendsto_rhoGamma_posSemidef_measureReal_one_of_traceMoment_tendsto_zero
      (μ := μ) (G := G) (m := m) hProb hGMeas ?_
  refine hMoment.congr' ?_
  filter_upwards [hσ] with d hdσ
  apply lintegral_congr_ae
  filter_upwards with ω
  rw [rhoGamma_eq_card_div_frobeniusMass_smul_wishartGamma hdσ (G d ω)]
  simp [smul_smul, div_eq_mul_inv, mul_assoc]

/-- Direct Wishart/radial controlled-moment PPT endpoint with varying
probability spaces.

This is the form suited to the canonical Gaussian model, whose coordinate
space depends on `d`.  The theorem is still only an adapter: the displayed
Frobenius-mass-scaled Wishart trace-moment convergence is the remaining hard
random-matrix input. -/
theorem tendsto_rhoGamma_posSemidef_measureReal_one_of_varying_wishartGamma_frobeniusMass_traceMoment_tendsto_zero
    {Ω : ℕ → Type*} {σ : ℕ → Type*}
    [∀ d : ℕ, MeasurableSpace (Ω d)] [∀ d : ℕ, Fintype (σ d)]
    (μ : (d : ℕ) → Measure (Ω d))
    (G : (d : ℕ) → RandomSampleMatrix (Ω d) (Fin d) (Fin d) (σ d))
    (m : ℕ → ℕ)
    (hProb : ∀ d : ℕ, IsProbabilityMeasure (μ d))
    (hGMeas : ∀ d : ℕ, Measurable (G d))
    (hσ : ∀ᶠ d : ℕ in Filter.atTop, 0 < Fintype.card (σ d))
    (hMoment : Filter.Tendsto
      (fun d : ℕ =>
        ∫⁻ ω, ENNReal.ofReal
          (RCLike.re
            (((((((d : ℝ) ^ 2 * (Fintype.card (σ d) : ℝ) /
              frobeniusMass (G d ω) : ℝ) : ℂ) •
              wishartGamma (G d ω) - 1) ^ (2 * m d)).trace))) ∂(μ d))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun d : ℕ => (μ d).real {ω : Ω d | (rhoGamma (G d ω)).PosSemidef})
      Filter.atTop (nhds 1) := by
  have hNotTendsto :
      Filter.Tendsto
        (fun d : ℕ => μ d {ω : Ω d | ¬ (rhoGamma (G d ω)).PosSemidef})
        Filter.atTop (nhds 0) := by
    rw [ENNReal.tendsto_nhds_zero] at hMoment ⊢
    intro ε hε
    have hMomentEv := hMoment ε hε
    filter_upwards [Filter.eventually_gt_atTop 0, hσ, hMomentEv] with d hd hdσ hTraceLe
    have hDpos : 0 < ((d : ℝ) ^ 2) :=
      sq_pos_of_pos (by exact_mod_cast hd : 0 < (d : ℝ))
    have hMeas :
        AEMeasurable
          (fun ω : Ω d => ENNReal.ofReal
            (∑ i : BipIndex (Fin d) (Fin d),
              (scaledRhoGammaEigenvalues ((d : ℝ) ^ 2) (G d ω) i - 1) ^
                (2 * m d)))
          (μ d) :=
      aemeasurable_scaledRhoGammaEigenvalueCenteredPowerSum_of_measurable
        (μ d) (hGMeas d) ((d : ℝ) ^ 2) (2 * m d)
    have hNeg :
        μ d {ω : Ω d |
            ∃ i : BipIndex (Fin d) (Fin d),
              scaledRhoGammaEigenvalues ((d : ℝ) ^ 2) (G d ω) i < 0} ≤
          ∫⁻ ω, ENNReal.ofReal
            (∑ i : BipIndex (Fin d) (Fin d),
              (scaledRhoGammaEigenvalues ((d : ℝ) ^ 2) (G d ω) i - 1) ^
                (2 * m d))
            ∂(μ d) :=
      negative_event_measure_le_lintegral_centered_even_moment
        (μ d)
        (fun ω : Ω d => scaledRhoGammaEigenvalues ((d : ℝ) ^ 2) (G d ω))
        (m d) hMeas
    have hTraceAsRho :
        (fun ω : Ω d => ENNReal.ofReal
          (∑ i : BipIndex (Fin d) (Fin d),
            (scaledRhoGammaEigenvalues ((d : ℝ) ^ 2) (G d ω) i - 1) ^
              (2 * m d))) =
        (fun ω : Ω d => ENNReal.ofReal
          (RCLike.re (((((d : ℝ) ^ 2 : ℂ) • rhoGamma (G d ω) - 1) ^
            (2 * m d)).trace))) := by
      funext ω
      rw [← rhoGamma_centered_trace_re_eq_sum_scaledRhoGammaEigenvalues
        (((d : ℝ) ^ 2)) (G d ω) (2 * m d)]
      simp [Complex.ofReal_pow]
    have hRhoTraceEqWishartTrace :
        (∫⁻ ω, ENNReal.ofReal
          (RCLike.re (((((d : ℝ) ^ 2 : ℂ) • rhoGamma (G d ω) - 1) ^
            (2 * m d)).trace)) ∂(μ d)) =
        (∫⁻ ω, ENNReal.ofReal
          (RCLike.re
            (((((((d : ℝ) ^ 2 * (Fintype.card (σ d) : ℝ) /
              frobeniusMass (G d ω) : ℝ) : ℂ) •
              wishartGamma (G d ω) - 1) ^ (2 * m d)).trace))) ∂(μ d)) := by
      apply lintegral_congr_ae
      filter_upwards with ω
      rw [rhoGamma_eq_card_div_frobeniusMass_smul_wishartGamma hdσ (G d ω)]
      simp [smul_smul, div_eq_mul_inv, mul_assoc]
    have hMomentLe :
        (∫⁻ ω, ENNReal.ofReal
          (∑ i : BipIndex (Fin d) (Fin d),
            (scaledRhoGammaEigenvalues ((d : ℝ) ^ 2) (G d ω) i - 1) ^
              (2 * m d))
          ∂(μ d)) ≤ ε := by
      calc
        (∫⁻ ω, ENNReal.ofReal
          (∑ i : BipIndex (Fin d) (Fin d),
            (scaledRhoGammaEigenvalues ((d : ℝ) ^ 2) (G d ω) i - 1) ^
              (2 * m d))
          ∂(μ d))
            = (∫⁻ ω, ENNReal.ofReal
              (RCLike.re (((((d : ℝ) ^ 2 : ℂ) • rhoGamma (G d ω) - 1) ^
                (2 * m d)).trace)) ∂(μ d)) := by
                simp [hTraceAsRho]
        _ = (∫⁻ ω, ENNReal.ofReal
              (RCLike.re
                (((((((d : ℝ) ^ 2 * (Fintype.card (σ d) : ℝ) /
                  frobeniusMass (G d ω) : ℝ) : ℂ) •
                  wishartGamma (G d ω) - 1) ^ (2 * m d)).trace))) ∂(μ d)) :=
                hRhoTraceEqWishartTrace
        _ ≤ ε := hTraceLe
    exact le_trans
      (le_trans
        (measure_not_rhoGamma_posSemidef_le_exists_scaled_eigenvalue_neg
          (μ d) hDpos (G d)) hNeg)
      hMomentLe
  have hNotReal :
      Filter.Tendsto
        (fun d : ℕ =>
          (μ d {ω : Ω d | ¬ (rhoGamma (G d ω)).PosSemidef}).toReal)
        Filter.atTop (nhds 0) := by
    simpa using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hNotTendsto
  have hTarget :
      Filter.Tendsto
        (fun d : ℕ =>
          1 - (μ d {ω : Ω d | ¬ (rhoGamma (G d ω)).PosSemidef}).toReal)
        Filter.atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.sub hNotReal : Filter.Tendsto
      (fun d : ℕ =>
        (1 : ℝ) - (μ d {ω : Ω d | ¬ (rhoGamma (G d ω)).PosSemidef}).toReal)
      Filter.atTop (nhds (1 - 0)))
  refine hTarget.congr' ?_
  filter_upwards with d
  letI : IsProbabilityMeasure (μ d) := hProb d
  have hPPTMeas :
      MeasurableSet {ω : Ω d | (rhoGamma (G d ω)).PosSemidef} :=
    measurableSet_rhoGamma_posSemidef_of_measurable (G := G d) (hGMeas d)
  have hcompl := measureReal_compl (μ := μ d) hPPTMeas
  have hUniv : (μ d).real Set.univ = 1 := by
    simp [Measure.real, IsProbabilityMeasure.measure_univ]
  have hNotSet :
      {ω : Ω d | ¬ (rhoGamma (G d ω)).PosSemidef} =
        {ω : Ω d | (rhoGamma (G d ω)).PosSemidef}ᶜ := rfl
  have hNotRealEq :
      (μ d {ω : Ω d | ¬ (rhoGamma (G d ω)).PosSemidef}).toReal =
        (μ d).real {ω : Ω d | (rhoGamma (G d ω)).PosSemidef}ᶜ := by
    rw [hNotSet]
    rfl
  linarith

/-- If the environment size has a positive quadratic ratio limit, then the
sample index is eventually nonempty.  This discharges the routine `0 < s d`
input of the canonical Gaussian endpoint from the usual scaling hypothesis. -/
theorem eventually_pos_of_tendsto_natCast_div_sq_pos
    {s : ℕ → ℕ} {lam : ℝ} (hlam : 0 < lam)
    (hRatio : Filter.Tendsto
      (fun d : ℕ => (s d : ℝ) / (d : ℝ) ^ 2)
      Filter.atTop (nhds lam)) :
    ∀ᶠ d : ℕ in Filter.atTop, 0 < s d := by
  have hposRatio :
      ∀ᶠ d : ℕ in Filter.atTop, 0 < (s d : ℝ) / (d : ℝ) ^ 2 := by
    exact hRatio.eventually (eventually_gt_nhds hlam)
  filter_upwards [hposRatio, Filter.eventually_gt_atTop (0 : ℕ)] with d hd hdpos
  have hden_pos : 0 < (d : ℝ) ^ 2 := by
    exact pow_pos (Nat.cast_pos.mpr hdpos) 2
  have hs_pos_real : 0 < (s d : ℝ) := by
    exact (div_pos_iff_of_pos_right hden_pos).mp hd
  exact Nat.cast_pos.mp hs_pos_real

/-- Canonical Gaussian finite-sample Wishart/radial controlled-moment PPT
endpoint.

This specializes the varying-space endpoint to the repository's concrete
Gaussian coordinate model with sample index `Fin (s d)`.  The only remaining
random-matrix input is the displayed growing trace-moment convergence. -/
theorem tendsto_rhoGamma_posSemidef_measureReal_one_of_canonicalGaussian_finSample_wishartGamma_frobeniusMass_traceMoment_tendsto_zero
    (s m : ℕ → ℕ)
    (hs : ∀ᶠ d : ℕ in Filter.atTop, 0 < s d)
    (hMoment : Filter.Tendsto
      (fun d : ℕ =>
        ∫⁻ ω, ENNReal.ofReal
          (RCLike.re
            (((((((d : ℝ) ^ 2 * (Fintype.card (Fin (s d)) : ℝ) /
              frobeniusMass
                (PptFactorization.HighProbabilityBounds.gaussianMatrix
                  (Fin d) (Fin d) (Fin (s d)) ω) : ℝ) : ℂ) •
              wishartGamma
                (PptFactorization.HighProbabilityBounds.gaussianMatrix
                  (Fin d) (Fin d) (Fin (s d)) ω) - 1) ^
              (2 * m d)).trace))) ∂
          (PptFactorization.HighProbabilityBounds.gaussianMeasure
            (Fin d) (Fin d) (Fin (s d))))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun d : ℕ =>
        (PptFactorization.HighProbabilityBounds.gaussianMeasure
          (Fin d) (Fin d) (Fin (s d))).real
          {ω : PptFactorization.HighProbabilityBounds.Ω
              (Fin d) (Fin d) (Fin (s d)) |
            (rhoGamma
              (PptFactorization.HighProbabilityBounds.gaussianMatrix
                (Fin d) (Fin d) (Fin (s d)) ω)).PosSemidef})
      Filter.atTop (nhds 1) := by
  refine
    tendsto_rhoGamma_posSemidef_measureReal_one_of_varying_wishartGamma_frobeniusMass_traceMoment_tendsto_zero
      (Ω := fun d : ℕ =>
        PptFactorization.HighProbabilityBounds.Ω (Fin d) (Fin d) (Fin (s d)))
      (σ := fun d : ℕ => Fin (s d))
      (μ := fun d : ℕ =>
        PptFactorization.HighProbabilityBounds.gaussianMeasure
          (Fin d) (Fin d) (Fin (s d)))
      (G := fun d : ℕ =>
        PptFactorization.HighProbabilityBounds.gaussianMatrix
          (Fin d) (Fin d) (Fin (s d)))
      (m := m) ?_ ?_ ?_ hMoment
  · intro d
    change IsProbabilityMeasure
      (PptFactorization.HighProbabilityBounds.gaussianMeasure (Fin d) (Fin d) (Fin (s d)))
    rw [PptFactorization.HighProbabilityBounds.gaussianMeasure_eq]
    infer_instance
  · intro d
    exact PptFactorization.AppendixB.measurable_gaussianMatrix
      (p := Fin d) (q := Fin d) (σ := Fin (s d))
  · filter_upwards [hs] with d hd
    simpa using hd

/-- Canonical Gaussian finite-sample endpoint with the nonempty-environment
condition supplied by the usual positive quadratic ratio limit.  The only
remaining theorem-strength input is the displayed Frobenius-mass-scaled
growing trace-moment convergence. -/
theorem tendsto_rhoGamma_posSemidef_measureReal_one_of_canonicalGaussian_finSample_wishartGamma_frobeniusMass_traceMoment_tendsto_zero_of_ratio_tendsto_pos
    (s m : ℕ → ℕ) {lam : ℝ} (hlam : 0 < lam)
    (hRatio : Filter.Tendsto
      (fun d : ℕ => (s d : ℝ) / (d : ℝ) ^ 2)
      Filter.atTop (nhds lam))
    (hMoment : Filter.Tendsto
      (fun d : ℕ =>
        ∫⁻ ω, ENNReal.ofReal
          (RCLike.re
            (((((((d : ℝ) ^ 2 * (Fintype.card (Fin (s d)) : ℝ) /
              frobeniusMass
                (PptFactorization.HighProbabilityBounds.gaussianMatrix
                  (Fin d) (Fin d) (Fin (s d)) ω) : ℝ) : ℂ) •
              wishartGamma
                (PptFactorization.HighProbabilityBounds.gaussianMatrix
                  (Fin d) (Fin d) (Fin (s d)) ω) - 1) ^
              (2 * m d)).trace))) ∂
          (PptFactorization.HighProbabilityBounds.gaussianMeasure
            (Fin d) (Fin d) (Fin (s d))))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun d : ℕ =>
        (PptFactorization.HighProbabilityBounds.gaussianMeasure
          (Fin d) (Fin d) (Fin (s d))).real
          {ω : PptFactorization.HighProbabilityBounds.Ω
              (Fin d) (Fin d) (Fin (s d)) |
            (rhoGamma
              (PptFactorization.HighProbabilityBounds.gaussianMatrix
                (Fin d) (Fin d) (Fin (s d)) ω)).PosSemidef})
      Filter.atTop (nhds 1) := by
  exact
    tendsto_rhoGamma_posSemidef_measureReal_one_of_canonicalGaussian_finSample_wishartGamma_frobeniusMass_traceMoment_tendsto_zero
      s m (eventually_pos_of_tendsto_natCast_div_sq_pos hlam hRatio) hMoment

/-- Canonical Gaussian finite-sample endpoint from an eventual paper-shape
logarithmic moment envelope.

This is still only an adapter: the hypothesis `hBound` is exactly the future
growing-moment estimate for the Frobenius-mass-scaled Wishart trace moment. -/
theorem tendsto_rhoGamma_posSemidef_measureReal_one_of_canonicalGaussian_finSample_wishartGamma_frobeniusMass_eventually_log_bound_of_ratio_tendsto_pos
    (s m : ℕ → ℕ) {lam C α q c : ℝ} (hlam : 0 < lam)
    (hRatio : Filter.Tendsto
      (fun d : ℕ => (s d : ℝ) / (d : ℝ) ^ 2)
      Filter.atTop (nhds lam))
    (hq : 0 < q) (hc : 2 < c * Real.log q⁻¹)
    (hBound : ∀ᶠ d : ℕ in Filter.atTop,
      (∫⁻ ω, ENNReal.ofReal
        (RCLike.re
          (((((((d : ℝ) ^ 2 * (Fintype.card (Fin (s d)) : ℝ) /
            frobeniusMass
              (PptFactorization.HighProbabilityBounds.gaussianMatrix
                (Fin d) (Fin d) (Fin (s d)) ω) : ℝ) : ℂ) •
            wishartGamma
              (PptFactorization.HighProbabilityBounds.gaussianMatrix
                (Fin d) (Fin d) (Fin (s d)) ω) - 1) ^
            (2 * m d)).trace))) ∂
        (PptFactorization.HighProbabilityBounds.gaussianMeasure
          (Fin d) (Fin d) (Fin (s d)))) ≤
        ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
          ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))) :
    Filter.Tendsto
      (fun d : ℕ =>
        (PptFactorization.HighProbabilityBounds.gaussianMeasure
          (Fin d) (Fin d) (Fin (s d))).real
          {ω : PptFactorization.HighProbabilityBounds.Ω
              (Fin d) (Fin d) (Fin (s d)) |
            (rhoGamma
              (PptFactorization.HighProbabilityBounds.gaussianMatrix
                (Fin d) (Fin d) (Fin (s d)) ω)).PosSemidef})
      Filter.atTop (nhds 1) := by
  have hδ : Filter.Tendsto
      (fun d : ℕ => C * ((Real.log (d : ℝ)) ^ α *
        ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))
      Filter.atTop (nhds 0) :=
    const_mul_log_rpow_mul_quadratic_rpow_const_mul_log_tendsto_zero_of_two_lt_mul_log_inv
      C α q c hq hc
  have hMoment : Filter.Tendsto
      (fun d : ℕ =>
        ∫⁻ ω, ENNReal.ofReal
          (RCLike.re
            (((((((d : ℝ) ^ 2 * (Fintype.card (Fin (s d)) : ℝ) /
              frobeniusMass
                (PptFactorization.HighProbabilityBounds.gaussianMatrix
                  (Fin d) (Fin d) (Fin (s d)) ω) : ℝ) : ℂ) •
              wishartGamma
                (PptFactorization.HighProbabilityBounds.gaussianMatrix
                  (Fin d) (Fin d) (Fin (s d)) ω) - 1) ^
              (2 * m d)).trace))) ∂
          (PptFactorization.HighProbabilityBounds.gaussianMeasure
            (Fin d) (Fin d) (Fin (s d))))
      Filter.atTop (nhds 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    have hδenn : Filter.Tendsto
        (fun d : ℕ => ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
          ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ))))))
        Filter.atTop (nhds 0) := by
      simpa using ENNReal.tendsto_ofReal hδ
    have hδevent : ∀ᶠ d : ℕ in Filter.atTop,
        ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
          ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ))))) ≤ ε :=
      (ENNReal.tendsto_nhds_zero.mp hδenn) ε hε
    filter_upwards [hBound, hδevent] with d hdBound hdδ
    exact le_trans hdBound hdδ
  exact
    tendsto_rhoGamma_posSemidef_measureReal_one_of_canonicalGaussian_finSample_wishartGamma_frobeniusMass_traceMoment_tendsto_zero_of_ratio_tendsto_pos
      s m hlam hRatio hMoment

/-- Canonical Gaussian finite-sample `λ > 4` paper-shape endpoint.

Lean chooses an edge slack and logarithmic moment order constants.  The only
remaining theorem-strength input is the eventual paper-shape Frobenius-mass
trace-moment estimate with those constants. -/
theorem exists_log_order_constants_and_tendsto_rhoGamma_posSemidef_measureReal_one_of_canonicalGaussian_finSample_wishartGamma_frobeniusMass_eventually_log_bound_of_ratio_tendsto
    (s m : ℕ → ℕ) {lam C α : ℝ} (hlam : 4 < lam)
    (hRatio : Filter.Tendsto
      (fun d : ℕ => (s d : ℝ) / (d : ℝ) ^ 2)
      Filter.atTop (nhds lam)) :
    ∃ eps q c : ℝ,
      0 < eps ∧ q = (4 + eps) / lam ∧ 0 < q ∧ q < 1 ∧
        0 < c ∧ 2 < c * Real.log q⁻¹ ∧
          ((∀ᶠ d : ℕ in Filter.atTop,
            (∫⁻ ω, ENNReal.ofReal
              (RCLike.re
                (((((((d : ℝ) ^ 2 * (Fintype.card (Fin (s d)) : ℝ) /
                  frobeniusMass
                    (PptFactorization.HighProbabilityBounds.gaussianMatrix
                      (Fin d) (Fin d) (Fin (s d)) ω) : ℝ) : ℂ) •
                  wishartGamma
                    (PptFactorization.HighProbabilityBounds.gaussianMatrix
                      (Fin d) (Fin d) (Fin (s d)) ω) - 1) ^
                  (2 * m d)).trace))) ∂
              (PptFactorization.HighProbabilityBounds.gaussianMeasure
                (Fin d) (Fin d) (Fin (s d)))) ≤
              ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
                ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))) →
            Filter.Tendsto
              (fun d : ℕ =>
                (PptFactorization.HighProbabilityBounds.gaussianMeasure
                  (Fin d) (Fin d) (Fin (s d))).real
                  {ω : PptFactorization.HighProbabilityBounds.Ω
                      (Fin d) (Fin d) (Fin (s d)) |
                    (rhoGamma
                      (PptFactorization.HighProbabilityBounds.gaussianMatrix
                        (Fin d) (Fin d) (Fin (s d)) ω)).PosSemidef})
              Filter.atTop (nhds 1)) := by
  rcases exists_log_order_constants_of_four_lt hlam with
    ⟨eps, q, c, heps, hq_def, hq_pos, hq_lt_one, hc_pos, hc⟩
  refine ⟨eps, q, c, heps, hq_def, hq_pos, hq_lt_one, hc_pos, hc, ?_⟩
  intro hBound
  exact
    tendsto_rhoGamma_posSemidef_measureReal_one_of_canonicalGaussian_finSample_wishartGamma_frobeniusMass_eventually_log_bound_of_ratio_tendsto_pos
      s m (by linarith) hRatio hq_pos hc hBound

/-- Canonical Gaussian endpoint from the same paper-shape envelope, but with the
sample count written as the ordinary natural number `s d` instead of
`Fintype.card (Fin (s d))`.

This is the statement shape expected from a future random-matrix supplier. -/
theorem tendsto_rhoGamma_posSemidef_measureReal_one_of_canonicalGaussian_natSample_wishartGamma_frobeniusMass_eventually_log_bound_of_ratio_tendsto_pos
    (s m : ℕ → ℕ) {lam C α q c : ℝ} (hlam : 0 < lam)
    (hRatio : Filter.Tendsto
      (fun d : ℕ => (s d : ℝ) / (d : ℝ) ^ 2)
      Filter.atTop (nhds lam))
    (hq : 0 < q) (hc : 2 < c * Real.log q⁻¹)
    (hBound : ∀ᶠ d : ℕ in Filter.atTop,
      (∫⁻ ω, ENNReal.ofReal
        (RCLike.re
          (((((((d : ℝ) ^ 2 * (s d : ℝ) /
            frobeniusMass
              (PptFactorization.HighProbabilityBounds.gaussianMatrix
                (Fin d) (Fin d) (Fin (s d)) ω) : ℝ) : ℂ) •
            wishartGamma
              (PptFactorization.HighProbabilityBounds.gaussianMatrix
                (Fin d) (Fin d) (Fin (s d)) ω) - 1) ^
            (2 * m d)).trace))) ∂
        (PptFactorization.HighProbabilityBounds.gaussianMeasure
          (Fin d) (Fin d) (Fin (s d)))) ≤
        ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
          ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))) :
    Filter.Tendsto
      (fun d : ℕ =>
        (PptFactorization.HighProbabilityBounds.gaussianMeasure
          (Fin d) (Fin d) (Fin (s d))).real
          {ω : PptFactorization.HighProbabilityBounds.Ω
              (Fin d) (Fin d) (Fin (s d)) |
            (rhoGamma
              (PptFactorization.HighProbabilityBounds.gaussianMatrix
                (Fin d) (Fin d) (Fin (s d)) ω)).PosSemidef})
      Filter.atTop (nhds 1) := by
  refine
    tendsto_rhoGamma_posSemidef_measureReal_one_of_canonicalGaussian_finSample_wishartGamma_frobeniusMass_eventually_log_bound_of_ratio_tendsto_pos
      s m (C := C) (α := α) hlam hRatio hq hc ?_
  filter_upwards [hBound] with d hd
  simpa using hd

/-- Canonical Gaussian finite-rate non-PPT endpoint from the fixed-base
paper envelope `q^(c log d)`, with sample count written as `s d`.

This is the dimensionwise version of the preceding asymptotic PPT endpoint:
the trace-moment estimate is still the hard random-matrix input, and Lean
transfers it to the same eventual bound on the concrete non-PPT event. -/
theorem eventually_not_rhoGamma_posSemidef_measure_le_of_canonicalGaussian_natSample_wishartGamma_frobeniusMass_eventually_log_bound_of_ratio_tendsto_pos
    (s m : ℕ → ℕ) {lam C α q c : ℝ} (hlam : 0 < lam)
    (hRatio : Filter.Tendsto
      (fun d : ℕ => (s d : ℝ) / (d : ℝ) ^ 2)
      Filter.atTop (nhds lam))
    (hBound : ∀ᶠ d : ℕ in Filter.atTop,
      (∫⁻ ω, ENNReal.ofReal
        (RCLike.re
          (((((((d : ℝ) ^ 2 * (s d : ℝ) /
            frobeniusMass
              (PptFactorization.HighProbabilityBounds.gaussianMatrix
                (Fin d) (Fin d) (Fin (s d)) ω) : ℝ) : ℂ) •
            wishartGamma
              (PptFactorization.HighProbabilityBounds.gaussianMatrix
                (Fin d) (Fin d) (Fin (s d)) ω) - 1) ^
            (2 * m d)).trace))) ∂
        (PptFactorization.HighProbabilityBounds.gaussianMeasure
          (Fin d) (Fin d) (Fin (s d)))) ≤
        ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
          ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))) :
    ∀ᶠ d : ℕ in Filter.atTop,
      PptFactorization.HighProbabilityBounds.gaussianMeasure
        (Fin d) (Fin d) (Fin (s d))
        {ω : PptFactorization.HighProbabilityBounds.Ω
            (Fin d) (Fin d) (Fin (s d)) |
          ¬ (rhoGamma
            (PptFactorization.HighProbabilityBounds.gaussianMatrix
              (Fin d) (Fin d) (Fin (s d)) ω)).PosSemidef} ≤
        ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
          ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ))))) := by
  refine
    eventually_not_rhoGamma_posSemidef_measure_le_of_eventually_varying_wishartGamma_frobeniusMass_traceMoment_bound_ofReal
      (Ω := fun d : ℕ =>
        PptFactorization.HighProbabilityBounds.Ω (Fin d) (Fin d) (Fin (s d)))
      (σ := fun d : ℕ => Fin (s d))
      (μ := fun d : ℕ =>
        PptFactorization.HighProbabilityBounds.gaussianMeasure
          (Fin d) (Fin d) (Fin (s d)))
      (G := fun d : ℕ =>
        PptFactorization.HighProbabilityBounds.gaussianMatrix
          (Fin d) (Fin d) (Fin (s d)))
      (m := m)
      (δ := fun d : ℕ =>
        C * ((Real.log (d : ℝ)) ^ α *
          ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))
      ?_ ?_ ?_
  · intro d
    exact PptFactorization.AppendixB.measurable_gaussianMatrix
      (p := Fin d) (q := Fin d) (σ := Fin (s d))
  · filter_upwards [eventually_pos_of_tendsto_natCast_div_sq_pos hlam hRatio] with d hd
    simpa using hd
  · filter_upwards [hBound] with d hd
    simpa using hd

/-- `λ > 4` canonical Gaussian finite-rate non-PPT endpoint with the sample
count written as `s d`.

Lean chooses the fixed-base paper-envelope constants.  The remaining
theorem-strength input is the eventual Frobenius-mass trace-moment bound for
those constants; the conclusion keeps the same dimensionwise rate for the
concrete non-PPT event. -/
theorem exists_log_order_constants_and_eventually_not_rhoGamma_posSemidef_measure_le_of_canonicalGaussian_natSample_wishartGamma_frobeniusMass_eventually_log_bound_of_ratio_tendsto
    (s m : ℕ → ℕ) {lam C α : ℝ} (hlam : 4 < lam)
    (hRatio : Filter.Tendsto
      (fun d : ℕ => (s d : ℝ) / (d : ℝ) ^ 2)
      Filter.atTop (nhds lam)) :
    ∃ eps q c : ℝ,
      0 < eps ∧ q = (4 + eps) / lam ∧ 0 < q ∧ q < 1 ∧
        0 < c ∧ 2 < c * Real.log q⁻¹ ∧
          ((∀ᶠ d : ℕ in Filter.atTop,
            (∫⁻ ω, ENNReal.ofReal
              (RCLike.re
                (((((((d : ℝ) ^ 2 * (s d : ℝ) /
                  frobeniusMass
                    (PptFactorization.HighProbabilityBounds.gaussianMatrix
                      (Fin d) (Fin d) (Fin (s d)) ω) : ℝ) : ℂ) •
                  wishartGamma
                    (PptFactorization.HighProbabilityBounds.gaussianMatrix
                      (Fin d) (Fin d) (Fin (s d)) ω) - 1) ^
                  (2 * m d)).trace))) ∂
              (PptFactorization.HighProbabilityBounds.gaussianMeasure
                (Fin d) (Fin d) (Fin (s d)))) ≤
              ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
                ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))) →
            ∀ᶠ d : ℕ in Filter.atTop,
              PptFactorization.HighProbabilityBounds.gaussianMeasure
                (Fin d) (Fin d) (Fin (s d))
                {ω : PptFactorization.HighProbabilityBounds.Ω
                    (Fin d) (Fin d) (Fin (s d)) |
                  ¬ (rhoGamma
                    (PptFactorization.HighProbabilityBounds.gaussianMatrix
                      (Fin d) (Fin d) (Fin (s d)) ω)).PosSemidef} ≤
                ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
                  ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))) := by
  rcases exists_log_order_constants_of_four_lt hlam with
    ⟨eps, q, c, heps, hq_def, hq_pos, hq_lt_one, hc_pos, hc⟩
  refine ⟨eps, q, c, heps, hq_def, hq_pos, hq_lt_one, hc_pos, hc, ?_⟩
  intro hBound
  exact
    eventually_not_rhoGamma_posSemidef_measure_le_of_canonicalGaussian_natSample_wishartGamma_frobeniusMass_eventually_log_bound_of_ratio_tendsto_pos
      s m (by linarith) hRatio hBound

/-- `λ > 4` canonical Gaussian paper-shape endpoint with the sample count
written as `s d`.

The only remaining theorem-strength input is the eventual paper-shape
Frobenius-mass trace-moment bound in this natural sample-count notation. -/
theorem exists_log_order_constants_and_tendsto_rhoGamma_posSemidef_measureReal_one_of_canonicalGaussian_natSample_wishartGamma_frobeniusMass_eventually_log_bound_of_ratio_tendsto
    (s m : ℕ → ℕ) {lam C α : ℝ} (hlam : 4 < lam)
    (hRatio : Filter.Tendsto
      (fun d : ℕ => (s d : ℝ) / (d : ℝ) ^ 2)
      Filter.atTop (nhds lam)) :
    ∃ eps q c : ℝ,
      0 < eps ∧ q = (4 + eps) / lam ∧ 0 < q ∧ q < 1 ∧
        0 < c ∧ 2 < c * Real.log q⁻¹ ∧
          ((∀ᶠ d : ℕ in Filter.atTop,
            (∫⁻ ω, ENNReal.ofReal
              (RCLike.re
                (((((((d : ℝ) ^ 2 * (s d : ℝ) /
                  frobeniusMass
                    (PptFactorization.HighProbabilityBounds.gaussianMatrix
                      (Fin d) (Fin d) (Fin (s d)) ω) : ℝ) : ℂ) •
                  wishartGamma
                    (PptFactorization.HighProbabilityBounds.gaussianMatrix
                      (Fin d) (Fin d) (Fin (s d)) ω) - 1) ^
                  (2 * m d)).trace))) ∂
              (PptFactorization.HighProbabilityBounds.gaussianMeasure
                (Fin d) (Fin d) (Fin (s d)))) ≤
              ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
                ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))) →
            Filter.Tendsto
              (fun d : ℕ =>
                (PptFactorization.HighProbabilityBounds.gaussianMeasure
                  (Fin d) (Fin d) (Fin (s d))).real
                  {ω : PptFactorization.HighProbabilityBounds.Ω
                      (Fin d) (Fin d) (Fin (s d)) |
                    (rhoGamma
                      (PptFactorization.HighProbabilityBounds.gaussianMatrix
                        (Fin d) (Fin d) (Fin (s d)) ω)).PosSemidef})
              Filter.atTop (nhds 1)) := by
  rcases exists_log_order_constants_of_four_lt hlam with
    ⟨eps, q, c, heps, hq_def, hq_pos, hq_lt_one, hc_pos, hc⟩
  refine ⟨eps, q, c, heps, hq_def, hq_pos, hq_lt_one, hc_pos, hc, ?_⟩
  intro hBound
  exact
    tendsto_rhoGamma_posSemidef_measureReal_one_of_canonicalGaussian_natSample_wishartGamma_frobeniusMass_eventually_log_bound_of_ratio_tendsto_pos
      s m (C := C) (α := α) (by linarith) hRatio hq_pos hc hBound

/-- A ratio-dependent paper envelope is eventually bounded by a fixed-`q`
envelope.

If `s d / d^2 → lam` and `4 + eta < lam`, then eventually
`(4 + eta) / (s d / d^2)` is bounded by the fixed number
`(4 + eta) / ((lam + (4 + eta)) / 2) < 1`. -/
theorem eventually_ratioDependent_log_envelope_le_fixed_of_tendsto_ratio
    (s : ℕ → ℕ) {lam eta C α c : ℝ}
    (hnum_pos : 0 < 4 + eta) (heta_lt : 4 + eta < lam)
    (hC : 0 ≤ C) (hc_nonneg : 0 ≤ c)
    (hRatio : Filter.Tendsto
      (fun d : ℕ => (s d : ℝ) / (d : ℝ) ^ 2)
      Filter.atTop (nhds lam)) :
    ∀ᶠ d : ℕ in Filter.atTop,
      C * ((Real.log (d : ℝ)) ^ α *
        ((d : ℝ) ^ 2 * (((4 + eta) / ((s d : ℝ) / (d : ℝ) ^ 2)) ^
          (c * Real.log (d : ℝ))))) ≤
      C * ((Real.log (d : ℝ)) ^ α *
        ((d : ℝ) ^ 2 * (((4 + eta) / ((lam + (4 + eta)) / 2)) ^
          (c * Real.log (d : ℝ))))) := by
  let r : ℝ := (lam + (4 + eta)) / 2
  have hr_lt : r < lam := by
    dsimp [r]
    linarith
  have hr_pos : 0 < r := by
    dsimp [r]
    linarith
  have hden_event : ∀ᶠ d : ℕ in Filter.atTop, r ≤ (s d : ℝ) / (d : ℝ) ^ 2 :=
    hRatio.eventually (eventually_ge_nhds hr_lt)
  filter_upwards [hden_event, Filter.eventually_gt_atTop (0 : ℕ)] with d hden_ge hdpos
  have hlog_nonneg : 0 ≤ Real.log (d : ℝ) := by
    exact Real.log_nonneg (by
      exact_mod_cast (Nat.succ_le_of_lt hdpos) : (1 : ℝ) ≤ d)
  have hexp_nonneg : 0 ≤ c * Real.log (d : ℝ) :=
    mul_nonneg hc_nonneg hlog_nonneg
  have hL_nonneg : 0 ≤ (Real.log (d : ℝ)) ^ α :=
    Real.rpow_nonneg hlog_nonneg α
  have hd2_nonneg : 0 ≤ (d : ℝ) ^ 2 := sq_nonneg (d : ℝ)
  have hnum_nonneg : 0 ≤ 4 + eta := le_of_lt hnum_pos
  have hden_pos : 0 < (s d : ℝ) / (d : ℝ) ^ 2 :=
    lt_of_lt_of_le hr_pos hden_ge
  have hbase_nonneg : 0 ≤ (4 + eta) / ((s d : ℝ) / (d : ℝ) ^ 2) :=
    div_nonneg hnum_nonneg (le_of_lt hden_pos)
  have hbase_le :
      (4 + eta) / ((s d : ℝ) / (d : ℝ) ^ 2) ≤ (4 + eta) / r :=
    div_le_div_of_nonneg_left hnum_nonneg hr_pos hden_ge
  have hpow_le :
      ((4 + eta) / ((s d : ℝ) / (d : ℝ) ^ 2)) ^ (c * Real.log (d : ℝ)) ≤
        ((4 + eta) / r) ^ (c * Real.log (d : ℝ)) :=
    Real.rpow_le_rpow hbase_nonneg hbase_le hexp_nonneg
  have h1 := mul_le_mul_of_nonneg_left hpow_le hd2_nonneg
  have h2 := mul_le_mul_of_nonneg_left h1 hL_nonneg
  have h3 := mul_le_mul_of_nonneg_left h2 hC
  simpa [r, mul_assoc] using h3

/-- Canonical Gaussian endpoint from the ratio-dependent paper envelope
`((4 + eta) / (s d / d^2))^(c log d)`.

This is often the most natural shape of the future growing-moment estimate. -/
theorem tendsto_rhoGamma_posSemidef_measureReal_one_of_canonicalGaussian_natSample_wishartGamma_frobeniusMass_ratioDependent_log_bound_of_ratio_tendsto_pos
    (s m : ℕ → ℕ) {lam eta C α c : ℝ}
    (hnum_pos : 0 < 4 + eta) (heta_lt : 4 + eta < lam)
    (hC : 0 ≤ C) (hc_nonneg : 0 ≤ c)
    (hc : 2 < c * Real.log (((4 + eta) / ((lam + (4 + eta)) / 2))⁻¹))
    (hRatio : Filter.Tendsto
      (fun d : ℕ => (s d : ℝ) / (d : ℝ) ^ 2)
      Filter.atTop (nhds lam))
    (hBound : ∀ᶠ d : ℕ in Filter.atTop,
      (∫⁻ ω, ENNReal.ofReal
        (RCLike.re
          (((((((d : ℝ) ^ 2 * (s d : ℝ) /
            frobeniusMass
              (PptFactorization.HighProbabilityBounds.gaussianMatrix
                (Fin d) (Fin d) (Fin (s d)) ω) : ℝ) : ℂ) •
            wishartGamma
              (PptFactorization.HighProbabilityBounds.gaussianMatrix
                (Fin d) (Fin d) (Fin (s d)) ω) - 1) ^
            (2 * m d)).trace))) ∂
        (PptFactorization.HighProbabilityBounds.gaussianMeasure
          (Fin d) (Fin d) (Fin (s d)))) ≤
        ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
          ((d : ℝ) ^ 2 *
            (((4 + eta) / ((s d : ℝ) / (d : ℝ) ^ 2)) ^
              (c * Real.log (d : ℝ))))))) :
    Filter.Tendsto
      (fun d : ℕ =>
        (PptFactorization.HighProbabilityBounds.gaussianMeasure
          (Fin d) (Fin d) (Fin (s d))).real
          {ω : PptFactorization.HighProbabilityBounds.Ω
              (Fin d) (Fin d) (Fin (s d)) |
            (rhoGamma
              (PptFactorization.HighProbabilityBounds.gaussianMatrix
                (Fin d) (Fin d) (Fin (s d)) ω)).PosSemidef})
      Filter.atTop (nhds 1) := by
  let q : ℝ := (4 + eta) / ((lam + (4 + eta)) / 2)
  have hq_pos : 0 < q := by
    dsimp [q]
    have hden_pos : 0 < (lam + (4 + eta)) / 2 := by linarith
    exact div_pos hnum_pos hden_pos
  refine
    tendsto_rhoGamma_posSemidef_measureReal_one_of_canonicalGaussian_natSample_wishartGamma_frobeniusMass_eventually_log_bound_of_ratio_tendsto_pos
      s m (C := C) (α := α) (q := q) (c := c) (by linarith) hRatio hq_pos ?_ ?_
  · simpa [q] using hc
  · have hEnvelope :=
      eventually_ratioDependent_log_envelope_le_fixed_of_tendsto_ratio
        (s := s) (lam := lam) (eta := eta) (C := C) (α := α) (c := c)
        hnum_pos heta_lt hC hc_nonneg hRatio
    filter_upwards [hBound, hEnvelope] with d hdBound hdEnvelope
    exact le_trans hdBound (ENNReal.ofReal_le_ofReal hdEnvelope)

/-- Canonical Gaussian finite-rate non-PPT endpoint from the ratio-dependent
paper envelope `((4 + eta) / (s d / d^2))^(c log d)`.

This is a pure transfer statement: the displayed trace-moment estimate is
still the hard growing-moment input, and the conclusion keeps exactly the same
dimensionwise rate for the concrete non-PPT event. -/
theorem eventually_not_rhoGamma_posSemidef_measure_le_of_canonicalGaussian_natSample_wishartGamma_frobeniusMass_ratioDependent_log_bound_of_ratio_tendsto_pos
    (s m : ℕ → ℕ) {lam eta C α c : ℝ} (hlam : 0 < lam)
    (hRatio : Filter.Tendsto
      (fun d : ℕ => (s d : ℝ) / (d : ℝ) ^ 2)
      Filter.atTop (nhds lam))
    (hBound : ∀ᶠ d : ℕ in Filter.atTop,
      (∫⁻ ω, ENNReal.ofReal
        (RCLike.re
          (((((((d : ℝ) ^ 2 * (s d : ℝ) /
            frobeniusMass
              (PptFactorization.HighProbabilityBounds.gaussianMatrix
                (Fin d) (Fin d) (Fin (s d)) ω) : ℝ) : ℂ) •
            wishartGamma
              (PptFactorization.HighProbabilityBounds.gaussianMatrix
                (Fin d) (Fin d) (Fin (s d)) ω) - 1) ^
            (2 * m d)).trace))) ∂
        (PptFactorization.HighProbabilityBounds.gaussianMeasure
          (Fin d) (Fin d) (Fin (s d)))) ≤
        ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
          ((d : ℝ) ^ 2 *
            (((4 + eta) / ((s d : ℝ) / (d : ℝ) ^ 2)) ^
              (c * Real.log (d : ℝ))))))) :
    ∀ᶠ d : ℕ in Filter.atTop,
      PptFactorization.HighProbabilityBounds.gaussianMeasure
        (Fin d) (Fin d) (Fin (s d))
        {ω : PptFactorization.HighProbabilityBounds.Ω
            (Fin d) (Fin d) (Fin (s d)) |
          ¬ (rhoGamma
            (PptFactorization.HighProbabilityBounds.gaussianMatrix
              (Fin d) (Fin d) (Fin (s d)) ω)).PosSemidef} ≤
        ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
          ((d : ℝ) ^ 2 *
            (((4 + eta) / ((s d : ℝ) / (d : ℝ) ^ 2)) ^
              (c * Real.log (d : ℝ)))))) := by
  refine
    eventually_not_rhoGamma_posSemidef_measure_le_of_eventually_varying_wishartGamma_frobeniusMass_traceMoment_bound_ofReal
      (Ω := fun d : ℕ =>
        PptFactorization.HighProbabilityBounds.Ω (Fin d) (Fin d) (Fin (s d)))
      (σ := fun d : ℕ => Fin (s d))
      (μ := fun d : ℕ =>
        PptFactorization.HighProbabilityBounds.gaussianMeasure
          (Fin d) (Fin d) (Fin (s d)))
      (G := fun d : ℕ =>
        PptFactorization.HighProbabilityBounds.gaussianMatrix
          (Fin d) (Fin d) (Fin (s d)))
      (m := m)
      (δ := fun d : ℕ =>
        C * ((Real.log (d : ℝ)) ^ α *
          ((d : ℝ) ^ 2 *
            (((4 + eta) / ((s d : ℝ) / (d : ℝ) ^ 2)) ^
              (c * Real.log (d : ℝ))))))
      ?_ ?_ ?_
  · intro d
    exact PptFactorization.AppendixB.measurable_gaussianMatrix
      (p := Fin d) (q := Fin d) (σ := Fin (s d))
  · filter_upwards [eventually_pos_of_tendsto_natCast_div_sq_pos hlam hRatio] with d hd
    simpa using hd
  · filter_upwards [hBound] with d hd
    simpa using hd

/-- For every `λ > 4`, one can choose a ratio slack `eta` and a logarithmic
moment-order constant `c` for the ratio-dependent paper envelope
`((4 + eta) / (s d / d^2))^(c log d)`.

This is the scalar constant-choice companion to
`exists_log_order_constants_of_four_lt`, but in the ratio-dependent
normalization used by the canonical Gaussian endpoint. -/
theorem exists_ratioDependent_log_order_constants_of_four_lt {lam : ℝ}
    (hlam : 4 < lam) :
    ∃ eta c : ℝ,
      0 < 4 + eta ∧ 4 + eta < lam ∧ 0 ≤ c ∧
        2 < c * Real.log (((4 + eta) / ((lam + (4 + eta)) / 2))⁻¹) := by
  let eta : ℝ := (lam - 4) / 2
  have hnum_pos : 0 < 4 + eta := by
    dsimp [eta]
    linarith
  have heta_lt : 4 + eta < lam := by
    dsimp [eta]
    linarith
  let q : ℝ := (4 + eta) / ((lam + (4 + eta)) / 2)
  have hden_pos : 0 < (lam + (4 + eta)) / 2 := by
    linarith
  have hq_pos : 0 < q := by
    dsimp [q]
    exact div_pos hnum_pos hden_pos
  have hq_lt_one : q < 1 := by
    dsimp [q]
    rw [div_lt_one hden_pos]
    linarith
  rcases exists_two_lt_mul_log_inv_of_pos_lt_one hq_pos hq_lt_one with
    ⟨c, hc_pos, hc⟩
  refine ⟨eta, c, hnum_pos, heta_lt, le_of_lt hc_pos, ?_⟩
  simpa [q] using hc

/-- Canonical Gaussian finite-rate `λ > 4` non-PPT endpoint from the natural
ratio-dependent paper envelope, with the ratio slack and logarithmic moment
order chosen by Lean.

This is the finite-rate sibling of the asymptotic ratio-dependent endpoint:
the hard trace-moment estimate remains visible, and Lean transfers it to the
same dimensionwise bound on the concrete non-PPT event. -/
theorem exists_ratioDependent_log_order_constants_and_eventually_not_rhoGamma_posSemidef_measure_le_of_canonicalGaussian_natSample_wishartGamma_frobeniusMass_ratioDependent_log_bound_of_ratio_tendsto
    (s m : ℕ → ℕ) {lam C α : ℝ} (hlam : 4 < lam)
    (hRatio : Filter.Tendsto
      (fun d : ℕ => (s d : ℝ) / (d : ℝ) ^ 2)
      Filter.atTop (nhds lam)) :
    ∃ eta c : ℝ,
      0 < 4 + eta ∧ 4 + eta < lam ∧ 0 ≤ c ∧
        2 < c * Real.log (((4 + eta) / ((lam + (4 + eta)) / 2))⁻¹) ∧
          ((∀ᶠ d : ℕ in Filter.atTop,
            (∫⁻ ω, ENNReal.ofReal
              (RCLike.re
                (((((((d : ℝ) ^ 2 * (s d : ℝ) /
                  frobeniusMass
                    (PptFactorization.HighProbabilityBounds.gaussianMatrix
                      (Fin d) (Fin d) (Fin (s d)) ω) : ℝ) : ℂ) •
                  wishartGamma
                    (PptFactorization.HighProbabilityBounds.gaussianMatrix
                      (Fin d) (Fin d) (Fin (s d)) ω) - 1) ^
                  (2 * m d)).trace))) ∂
              (PptFactorization.HighProbabilityBounds.gaussianMeasure
                (Fin d) (Fin d) (Fin (s d)))) ≤
              ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
                ((d : ℝ) ^ 2 *
                  (((4 + eta) / ((s d : ℝ) / (d : ℝ) ^ 2)) ^
                    (c * Real.log (d : ℝ))))))) →
            ∀ᶠ d : ℕ in Filter.atTop,
              PptFactorization.HighProbabilityBounds.gaussianMeasure
                (Fin d) (Fin d) (Fin (s d))
                {ω : PptFactorization.HighProbabilityBounds.Ω
                    (Fin d) (Fin d) (Fin (s d)) |
                  ¬ (rhoGamma
                    (PptFactorization.HighProbabilityBounds.gaussianMatrix
                      (Fin d) (Fin d) (Fin (s d)) ω)).PosSemidef} ≤
                ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
                  ((d : ℝ) ^ 2 *
                    (((4 + eta) / ((s d : ℝ) / (d : ℝ) ^ 2)) ^
                      (c * Real.log (d : ℝ))))))) := by
  rcases exists_ratioDependent_log_order_constants_of_four_lt hlam with
    ⟨eta, c, hnum_pos, heta_lt, hc_nonneg, hc⟩
  refine ⟨eta, c, hnum_pos, heta_lt, hc_nonneg, hc, ?_⟩
  intro hBound
  exact
    eventually_not_rhoGamma_posSemidef_measure_le_of_canonicalGaussian_natSample_wishartGamma_frobeniusMass_ratioDependent_log_bound_of_ratio_tendsto_pos
      s m (by linarith) hRatio hBound

/-- Canonical Gaussian `λ > 4` endpoint from the natural ratio-dependent
paper envelope, with the ratio slack and logarithmic moment order chosen by
Lean.

The only theorem-strength supplier left visible is the eventual
ratio-dependent Frobenius-mass trace-moment bound for the chosen `eta` and
`c`. -/
theorem exists_ratioDependent_log_order_constants_and_tendsto_rhoGamma_posSemidef_measureReal_one_of_canonicalGaussian_natSample_wishartGamma_frobeniusMass_ratioDependent_log_bound_of_ratio_tendsto
    (s m : ℕ → ℕ) {lam C α : ℝ} (hlam : 4 < lam) (hC : 0 ≤ C)
    (hRatio : Filter.Tendsto
      (fun d : ℕ => (s d : ℝ) / (d : ℝ) ^ 2)
      Filter.atTop (nhds lam)) :
    ∃ eta c : ℝ,
      0 < 4 + eta ∧ 4 + eta < lam ∧ 0 ≤ c ∧
        2 < c * Real.log (((4 + eta) / ((lam + (4 + eta)) / 2))⁻¹) ∧
          ((∀ᶠ d : ℕ in Filter.atTop,
            (∫⁻ ω, ENNReal.ofReal
              (RCLike.re
                (((((((d : ℝ) ^ 2 * (s d : ℝ) /
                  frobeniusMass
                    (PptFactorization.HighProbabilityBounds.gaussianMatrix
                      (Fin d) (Fin d) (Fin (s d)) ω) : ℝ) : ℂ) •
                  wishartGamma
                    (PptFactorization.HighProbabilityBounds.gaussianMatrix
                      (Fin d) (Fin d) (Fin (s d)) ω) - 1) ^
                  (2 * m d)).trace))) ∂
              (PptFactorization.HighProbabilityBounds.gaussianMeasure
                (Fin d) (Fin d) (Fin (s d)))) ≤
              ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
                ((d : ℝ) ^ 2 *
                  (((4 + eta) / ((s d : ℝ) / (d : ℝ) ^ 2)) ^
                    (c * Real.log (d : ℝ))))))) →
            Filter.Tendsto
              (fun d : ℕ =>
                (PptFactorization.HighProbabilityBounds.gaussianMeasure
                  (Fin d) (Fin d) (Fin (s d))).real
                  {ω : PptFactorization.HighProbabilityBounds.Ω
                      (Fin d) (Fin d) (Fin (s d)) |
                    (rhoGamma
                      (PptFactorization.HighProbabilityBounds.gaussianMatrix
                        (Fin d) (Fin d) (Fin (s d)) ω)).PosSemidef})
              Filter.atTop (nhds 1)) := by
  rcases exists_ratioDependent_log_order_constants_of_four_lt hlam with
    ⟨eta, c, hnum_pos, heta_lt, hc_nonneg, hc⟩
  refine ⟨eta, c, hnum_pos, heta_lt, hc_nonneg, hc, ?_⟩
  intro hBound
  exact
    tendsto_rhoGamma_posSemidef_measureReal_one_of_canonicalGaussian_natSample_wishartGamma_frobeniusMass_ratioDependent_log_bound_of_ratio_tendsto_pos
      s m hnum_pos heta_lt hC hc_nonneg hc hRatio hBound

end AubrunAlternative
