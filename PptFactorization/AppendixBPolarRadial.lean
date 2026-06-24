import PptFactorization.AppendixBConcreteModel
import PptFactorization.AppendixBRadialSpherical
import PptFactorization.AppendixBNormalizedExpectations
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Appendix B: radial Gaussian estimates for the concrete model

This file proves the no-input radial estimates currently available from the
repo's concrete Gaussian model:

* `E R² = d² s`;
* an explicit lower bound on `E R`, obtained from the already proved lower
  tail for `R²`.

The full polar decomposition theorem
`R` independent of `G / ‖G‖₂` and the identification of the direction law with
surface-uniform measure on the Hilbert--Schmidt sphere is not asserted here:
that still requires a genuine polar-coordinate/spherical-Haar measure theorem.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal

noncomputable section

namespace PptFactorization
namespace AppendixB

open RandomMatrixModel GaussianModel HighProbabilityBounds

variable {p q σ : Type*}
variable [Fintype p] [Fintype q] [Fintype σ]
variable [DecidableEq p] [DecidableEq q]

/-! ## General radial integrability and lower bound -/

omit [DecidableEq p] [DecidableEq q] in
/-- The total Gaussian mass is measurable. -/
@[measurability]
theorem measurable_gaussianMass :
    Measurable (gaussianMass p q σ) := by
  classical
  rw [show gaussianMass p q σ =
      (fun ω : Ω p q σ => ∑ α : σ, ‖gaussianColumn p q σ α ω‖ ^ 2) by
        funext ω
        exact gaussianMass_eq_sum_gaussianColumn_normSq
          (p := p) (q := q) (σ := σ) ω]
  fun_prop

/-- The Gaussian Frobenius radius is integrable. -/
theorem gaussianRadius_integrable :
    Integrable (gaussianRadius (p := p) (q := q) (σ := σ))
      (gaussianMeasure p q σ) := by
  haveI : IsProbabilityMeasure (gaussianMeasure p q σ) := by
    rw [gaussianMeasure_eq]
    infer_instance
  refine integrable_of_le_of_le
    (measurable_gaussianRadius (p := p) (q := q) (σ := σ)).aestronglyMeasurable
    ?_ ?_ (integrable_const (0 : ℝ))
    ((gaussianMass_integrable (p := p) (q := q) (σ := σ)).add
      (integrable_const (1 : ℝ)))
  · exact Filter.Eventually.of_forall fun ω => by
      unfold gaussianRadius frobeniusNorm
      positivity
  · exact Filter.Eventually.of_forall fun ω => by
      have hsq :
          gaussianRadius (p := p) (q := q) (σ := σ) ω ^ 2 =
            gaussianMass p q σ ω := by
        rw [← gaussianRadiusSq_eq_gaussianMass (p := p) (q := q) (σ := σ) ω]
        rfl
      have hnonneg :
          0 ≤ gaussianRadius (p := p) (q := q) (σ := σ) ω := by
        unfold gaussianRadius frobeniusNorm
        positivity
      have hsquare :
          0 ≤ (gaussianRadius (p := p) (q := q) (σ := σ) ω - 1 / 2) ^ 2 :=
        sq_nonneg _
      calc
        gaussianRadius (p := p) (q := q) (σ := σ) ω
            ≤ gaussianRadius (p := p) (q := q) (σ := σ) ω ^ 2 + 1 := by
              nlinarith
        _ = gaussianMass p q σ ω + 1 := by rw [hsq]

/-- If a nonnegative random variable exceeds `a` on an event, its expectation
dominates `a` times the probability of that event.  This form is tuned for the
Gaussian radius. -/
theorem gaussianRadius_integral_ge_const_mul_measureReal
    {a : ℝ} :
    a *
        (gaussianMeasure p q σ).real
          {ω : Ω p q σ | a ≤ gaussianRadius (p := p) (q := q) (σ := σ) ω}
      ≤
    ∫ ω : Ω p q σ,
      gaussianRadius (p := p) (q := q) (σ := σ) ω
      ∂gaussianMeasure p q σ := by
  haveI : IsProbabilityMeasure (gaussianMeasure p q σ) := by
    rw [gaussianMeasure_eq]
    infer_instance
  let E : Set (Ω p q σ) :=
    {ω | a ≤ gaussianRadius (p := p) (q := q) (σ := σ) ω}
  have hE : MeasurableSet E := by
    exact measurableSet_le measurable_const
      (measurable_gaussianRadius (p := p) (q := q) (σ := σ))
  have hIndicator :
      Integrable (fun ω : Ω p q σ => E.indicator (fun _ => a) ω)
        (gaussianMeasure p q σ) :=
    (integrable_const a).indicator hE
  have hRadius :
      Integrable (gaussianRadius (p := p) (q := q) (σ := σ))
        (gaussianMeasure p q σ) :=
    gaussianRadius_integrable (p := p) (q := q) (σ := σ)
  have hpoint :
      (fun ω : Ω p q σ => E.indicator (fun _ => a) ω) ≤
        gaussianRadius (p := p) (q := q) (σ := σ) := by
    intro ω
    by_cases hω : ω ∈ E
    · have hEa :
          a ≤ gaussianRadius (p := p) (q := q) (σ := σ) ω := by
        simpa [E] using hω
      change E.indicator (fun _ => a) ω ≤
        gaussianRadius (p := p) (q := q) (σ := σ) ω
      rw [Set.indicator_of_mem hω]
      exact hEa
    · have hnonneg :
          0 ≤ gaussianRadius (p := p) (q := q) (σ := σ) ω := by
        unfold gaussianRadius frobeniusNorm
        positivity
      change E.indicator (fun _ => a) ω ≤
        gaussianRadius (p := p) (q := q) (σ := σ) ω
      rw [Set.indicator_of_notMem hω]
      exact hnonneg
  have hmono := integral_mono hIndicator hRadius hpoint
  have hIntegralIndicator :
      ∫ ω : Ω p q σ, E.indicator (fun _ => a) ω ∂gaussianMeasure p q σ =
        (gaussianMeasure p q σ).real E * a := by
    simpa using
      (integral_indicator_const (μ := gaussianMeasure p q σ) (e := a) hE)
  calc
    a * (gaussianMeasure p q σ).real E =
        (gaussianMeasure p q σ).real E * a := by ring
    _ = ∫ ω : Ω p q σ, E.indicator (fun _ => a) ω ∂gaussianMeasure p q σ := by
        rw [hIntegralIndicator]
    _ ≤ ∫ ω : Ω p q σ,
          gaussianRadius (p := p) (q := q) (σ := σ) ω
          ∂gaussianMeasure p q σ := hmono

omit [DecidableEq p] [DecidableEq q] in
/-- Exact no-input value of the quadratic radial mean:
`E R² = D s`. -/
theorem gaussianRadiusSq_integral_eq :
    ∫ ω : Ω p q σ,
        gaussianRadius (p := p) (q := q) (σ := σ) ω ^ 2
        ∂gaussianMeasure p q σ =
      bipartiteDimension p q * sampleDimension σ := by
  simpa [gaussianRadiusSq_eq_gaussianMass] using
    gaussianMass_integral_eq (p := p) (q := q) (σ := σ)

/-- Lower bound for the Gaussian radial mean from the mass lower tail.

The right-hand side is explicit and no-input.  In the nondegenerate concrete
regime `D s ≥ 1`, it is a fixed positive fraction of `sqrt (D s)`. -/
theorem gaussianRadialMean_lower_bound_from_mass_tail :
    Real.sqrt ((1 / 2 : ℝ) * bipartiteDimension p q * sampleDimension σ) *
        (1 -
          Real.exp
            (-((1 / 6 : ℝ) * bipartiteDimension p q * sampleDimension σ)))
      ≤
    ∫ ω : Ω p q σ,
      gaussianRadius (p := p) (q := q) (σ := σ) ω
      ∂gaussianMeasure p q σ := by
  classical
  let μ := gaussianMeasure p q σ
  let N : ℝ := bipartiteDimension p q * sampleDimension σ
  let a : ℝ := Real.sqrt ((1 / 2 : ℝ) * N)
  let EMass : Set (Ω p q σ) :=
    gaussianMassLowerEvent (p := p) (q := q) (σ := σ) (1 / 2 : ℝ)
  let ERadius : Set (Ω p q σ) :=
    {ω | a ≤ gaussianRadius (p := p) (q := q) (σ := σ) ω}
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ, gaussianMeasure]
    infer_instance
  have hN_nonneg : 0 ≤ N := by
    dsimp [N, bipartiteDimension, sampleDimension]
    positivity
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact Real.sqrt_nonneg _
  have hEMass_meas : MeasurableSet EMass := by
    dsimp [EMass, gaussianMassLowerEvent]
    exact measurableSet_le measurable_const
      (measurable_gaussianMass (p := p) (q := q) (σ := σ))
  have hERadius_meas : MeasurableSet ERadius := by
    dsimp [ERadius]
    exact measurableSet_le measurable_const
      (measurable_gaussianRadius (p := p) (q := q) (σ := σ))
  have hsubset : EMass ⊆ ERadius := by
    intro ω hω
    dsimp [EMass, ERadius, gaussianMassLowerEvent] at hω ⊢
    have hmass :
        (1 / 2 : ℝ) * N ≤ gaussianMass p q σ ω := by
      simpa [N, mul_assoc] using hω
    have hsq :
        gaussianRadius (p := p) (q := q) (σ := σ) ω ^ 2 =
          gaussianMass p q σ ω := by
      rw [← gaussianRadiusSq_eq_gaussianMass (p := p) (q := q) (σ := σ) ω]
      rfl
    have ha_sq :
        a ^ 2 = (1 / 2 : ℝ) * N := by
      dsimp [a]
      rw [Real.sq_sqrt]
      positivity
    have hsq_le :
        a ^ 2 ≤ gaussianRadius (p := p) (q := q) (σ := σ) ω ^ 2 := by
      nlinarith
    have hR_nonneg :
        0 ≤ gaussianRadius (p := p) (q := q) (σ := σ) ω := by
      unfold gaussianRadius frobeniusNorm
      positivity
    have ha_le_sqrt :
        a ≤
          Real.sqrt (gaussianRadius (p := p) (q := q) (σ := σ) ω ^ 2) :=
      (Real.le_sqrt ha_nonneg
        (sq_nonneg (gaussianRadius (p := p) (q := q) (σ := σ) ω))).mpr hsq_le
    simpa [Real.sqrt_sq hR_nonneg] using ha_le_sqrt
  have hmeasure_mono :
      μ.real EMass ≤ μ.real ERadius :=
    measureReal_mono (μ := μ) (h₂ := (measure_lt_top μ ERadius).ne) hsubset
  have htail := gaussianMass_lower_tail (p := p) (q := q) (σ := σ)
  have hEMass_lower :
      1 - Real.exp (-((1 / 6 : ℝ) * N)) ≤ μ.real EMass := by
    have hcompl :
        μ.real EMassᶜ ≤ Real.exp (-((1 / 6 : ℝ) * N)) := by
      simpa [μ, EMass, N, mul_assoc] using htail
    have hcompl_eq : μ.real EMassᶜ = 1 - μ.real EMass := by
      simpa [μ] using measureReal_compl (μ := μ) hEMass_meas
    linarith
  have hERadius_lower :
      1 - Real.exp (-((1 / 6 : ℝ) * N)) ≤ μ.real ERadius :=
    le_trans hEMass_lower hmeasure_mono
  have hmain :=
    gaussianRadius_integral_ge_const_mul_measureReal
      (p := p) (q := q) (σ := σ) (a := a)
  have hmul :
      a * (1 - Real.exp (-((1 / 6 : ℝ) * N))) ≤
        a * μ.real ERadius := by
    exact mul_le_mul_of_nonneg_left hERadius_lower ha_nonneg
  calc
    Real.sqrt ((1 / 2 : ℝ) * bipartiteDimension p q * sampleDimension σ) *
        (1 -
          Real.exp
            (-((1 / 6 : ℝ) * bipartiteDimension p q * sampleDimension σ)))
        =
      a * (1 - Real.exp (-((1 / 6 : ℝ) * N))) := by
        simp [a, N, mul_assoc]
    _ ≤ a * μ.real ERadius := hmul
    _ ≤ ∫ ω : Ω p q σ,
          gaussianRadius (p := p) (q := q) (σ := σ) ω
          ∂gaussianMeasure p q σ := by
        simpa [μ, ERadius] using hmain

/-! ## Concrete `Fin d, Fin d, Fin s` radial statements -/

namespace ConcreteModel

open ConcreteModel

/-- In the canonical Appendix B model, `E R² = d² s`. -/
theorem gaussianRadiusSq_integral_eq (d s : ℕ) :
    ∫ ω : ConcreteModel.Ω d s,
        gaussianRadius
          (p := LeftIndex d) (q := RightIndex d) (σ := SampleIndex s) ω ^ 2
        ∂ConcreteModel.gaussianMeasure d s =
      (d : ℝ) ^ 2 * (s : ℝ) := by
  have hD :
      bipartiteDimension (LeftIndex d) (RightIndex d) = (d : ℝ) ^ 2 := by
    simpa [ConcreteModel.D] using (ConcreteModel.D_eq d)
  have hS : sampleDimension (SampleIndex s) = (s : ℝ) := by
    simpa [ConcreteModel.S] using (ConcreteModel.S_eq s)
  simpa [ConcreteModel.gaussianMeasure, hD, hS] using
    AppendixB.gaussianRadiusSq_integral_eq
      (p := LeftIndex d) (q := RightIndex d) (σ := SampleIndex s)

/-- In the canonical Appendix B model, the radial mean has an explicit
dimension-scale lower bound. -/
theorem gaussianRadialMean_lower_bound_from_mass_tail (d s : ℕ) :
    Real.sqrt ((1 / 2 : ℝ) * (d : ℝ) ^ 2 * (s : ℝ)) *
        (1 -
          Real.exp (-((1 / 6 : ℝ) * (d : ℝ) ^ 2 * (s : ℝ))))
      ≤
    ∫ ω : ConcreteModel.Ω d s,
      gaussianRadius
        (p := LeftIndex d) (q := RightIndex d) (σ := SampleIndex s) ω
      ∂ConcreteModel.gaussianMeasure d s := by
  have hD :
      bipartiteDimension (LeftIndex d) (RightIndex d) = (d : ℝ) ^ 2 := by
    simpa [ConcreteModel.D] using (ConcreteModel.D_eq d)
  have hS : sampleDimension (SampleIndex s) = (s : ℝ) := by
    simpa [ConcreteModel.S] using (ConcreteModel.S_eq s)
  simpa [ConcreteModel.gaussianMeasure, hD, hS, mul_assoc] using
    AppendixB.gaussianRadialMean_lower_bound_from_mass_tail
      (p := LeftIndex d) (q := RightIndex d) (σ := SampleIndex s)

end ConcreteModel

end AppendixB
end PptFactorization
