import PptFactorization.AppendixB
import PptFactorization.AppendixBRadialSpherical
import PptFactorization.AppendixBWishartBridge
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Normalized expectation bounds for Appendix B

This file gives the appendix-facing normalized expectation estimates obtained
from the radial/spherical factorization.

The genuine analytic inputs are kept visible:

* the radius-direction independence statements,
* a Gaussian sample-operator estimate at the radial scale,
* a quadratic Wishart/Gamma lift estimate at the squared-radial scale.

Once those inputs are supplied, the normalized spherical expectations cancel
the radial factors with no remaining hidden argument.
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

/-! ## Named means -/

/-- Gaussian mean of the rectangular sample operator norm. -/
def gaussianSampleOpNormMean : ℝ :=
  ∫ ω : Ω p q σ,
    sampleOpNorm (p := p) (q := q) (σ := σ)
      (gaussianMatrix p q σ ω) ∂gaussianMeasure p q σ

/-- Radial mean `E R`, where `R = ‖G‖₂`. -/
def gaussianRadialMean : ℝ :=
  ∫ ω : Ω p q σ,
    gaussianRadius (p := p) (q := q) (σ := σ) ω
    ∂gaussianMeasure p q σ

/-- Spherical mean `E ‖X‖∞` for `X = G / ‖G‖₂`. -/
def sphericalSampleOpNormMean : ℝ :=
  ∫ X : SampleMatrix p q σ,
    sampleOpNorm (p := p) (q := q) (σ := σ) X
    ∂gaussianSphericalSampleMeasure (p := p) (q := q) (σ := σ)

/-- Quadratic radial mean `E R² = E ‖G‖₂²`. -/
def gaussianQuadraticRadialMean : ℝ :=
  ∫ ω : Ω p q σ,
    gaussianMass p q σ ω ∂gaussianMeasure p q σ

/-- The normalized partially transposed density observable on the spherical
sample variable. -/
def sphericalGammaOpNorm (X : SampleMatrix p q σ) : ℝ :=
  opNorm (gamma (densityMatrix X))

/-- Spherical mean `E ‖(XX*)^Γ‖∞` for the normalized sample. -/
def sphericalGammaOpNormMean : ℝ :=
  ∫ X : SampleMatrix p q σ,
    sphericalGammaOpNorm (p := p) (q := q) (σ := σ) X
    ∂gaussianSphericalSampleMeasure (p := p) (q := q) (σ := σ)

/-- Gaussian quadratic lift of the spherical Gamma observable:
`E[R² ‖(XX*)^Γ‖∞]`. -/
def gaussianQuadraticGammaLiftMean : ℝ :=
  ∫ ω : Ω p q σ,
    gaussianMass p q σ ω *
      sphericalGammaOpNorm (p := p) (q := q) (σ := σ)
        (gaussianDirection (p := p) (q := q) (σ := σ) ω)
    ∂gaussianMeasure p q σ

/-- Gaussian mean of the concrete Wishart-Gamma operator norm
`E ‖W^Γ‖∞`, where `W = GG*/s`. -/
def gaussianWishartGammaOpNormMean : ℝ :=
  ∫ ω : Ω p q σ,
    opNorm
      (wishartGamma (p := p) (q := q) (σ := σ)
        (gaussianMatrix p q σ ω))
    ∂gaussianMeasure p q σ

/-! ## Measurability of the Gamma spherical observable -/

omit [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Partial transpose as a complex-linear map on bipartite matrices. -/
def gammaLinearMap : BipMatrix p q →ₗ[ℂ] BipMatrix p q where
  toFun := gamma
  map_add' := by
    intro A B
    simp [gamma]
  map_smul' := by
    intro c A
    simp [gamma]

omit [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Continuity of partial transpose in the finite-dimensional topology. -/
theorem continuous_gamma :
    Continuous (fun A : BipMatrix p q => gamma A) := by
  simpa [gammaLinearMap] using
    (gammaLinearMap (p := p) (q := q)).continuous_of_finiteDimensional

/-- Continuity of the spherical Gamma observable. -/
theorem continuous_sphericalGammaOpNorm :
    Continuous (sphericalGammaOpNorm (p := p) (q := q) (σ := σ)) := by
  have hToEuclidean :
      Continuous (fun A : BipMatrix p q =>
        Matrix.toEuclideanCLM (n := BipIndex p q) (𝕜 := ℂ) A) := by
    exact
      (Matrix.toEuclideanCLM (n := BipIndex p q) (𝕜 := ℂ)).toAlgEquiv.toLinearMap
        |>.continuous_of_finiteDimensional
  have hDensity :
      Continuous (fun X : SampleMatrix p q σ => densityMatrix X) := by
    unfold densityMatrix
    fun_prop
  unfold sphericalGammaOpNorm opNorm
  exact continuous_norm.comp
    (hToEuclidean.comp
      ((continuous_gamma (p := p) (q := q)).comp hDensity))

/-! ## Radial/spherical expectation factorization -/

omit [DecidableEq p] [DecidableEq q] in
/-- Exact factorization
`E ‖G‖∞ = (E R) (E ‖X‖∞)` from radius-direction independence. -/
theorem gaussianSampleOpNormMean_factorization_of_indep
    (hIndep :
      gaussianRadius (p := p) (q := q) (σ := σ) ⟂ᵢ[gaussianMeasure p q σ]
        gaussianDirection (p := p) (q := q) (σ := σ)) :
    gaussianSampleOpNormMean (p := p) (q := q) (σ := σ) =
      gaussianRadialMean (p := p) (q := q) (σ := σ) *
        sphericalSampleOpNormMean (p := p) (q := q) (σ := σ) := by
  simpa [gaussianSampleOpNormMean, gaussianRadialMean, sphericalSampleOpNormMean]
    using
      gaussian_sampleOpNorm_expectation_factorization_of_indep
        (p := p) (q := q) (σ := σ) hIndep

/-- Exact factorization
`E[R² ‖(XX*)^Γ‖∞] = (E R²) (E ‖(XX*)^Γ‖∞)` from
radius-squared/direction independence. -/
theorem gaussianQuadraticGammaLiftMean_factorization_of_indep
    (hIndep :
      gaussianRadiusSq (p := p) (q := q) (σ := σ) ⟂ᵢ[gaussianMeasure p q σ]
        gaussianDirection (p := p) (q := q) (σ := σ)) :
    gaussianQuadraticGammaLiftMean (p := p) (q := q) (σ := σ) =
      gaussianQuadraticRadialMean (p := p) (q := q) (σ := σ) *
        sphericalGammaOpNormMean (p := p) (q := q) (σ := σ) := by
  simpa [gaussianQuadraticGammaLiftMean, gaussianQuadraticRadialMean,
    sphericalGammaOpNormMean] using
      gaussian_quadratic_radial_spherical_factorization_of_indep
        (p := p) (q := q) (σ := σ)
        (F := sphericalGammaOpNorm (p := p) (q := q) (σ := σ))
        hIndep
        (continuous_sphericalGammaOpNorm (p := p) (q := q) (σ := σ)
          |>.aestronglyMeasurable)

/-! ## Concrete radial bridge back from Wishart to the sphere -/

/-- Pointwise identity behind the squared-radial normalization:
`R² ‖(XX*)^Γ‖∞ = s ‖W^Γ‖∞`, with `X = G / ‖G‖₂` and
`W = GG*/s`.  The zero sample is handled by Lean's total inverse convention. -/
theorem gaussianQuadraticGammaLift_integrand_eq_sampleDimension_mul_wishartGammaOpNorm
    (hs : Fintype.card σ ≠ 0) (ω : Ω p q σ) :
    gaussianMass p q σ ω *
        sphericalGammaOpNorm (p := p) (q := q) (σ := σ)
          (gaussianDirection (p := p) (q := q) (σ := σ) ω) =
      sampleDimension σ *
        opNorm
          (wishartGamma (p := p) (q := q) (σ := σ)
            (gaussianMatrix p q σ ω)) := by
  let G : SampleMatrix p q σ := gaussianMatrix p q σ ω
  let T : ℝ := frobeniusMass G
  have hTnonneg : 0 ≤ T := by
    dsimp [T, frobeniusMass, frobeniusNorm]
    positivity
  by_cases hTpos : 0 < T
  · have hρ :=
      rhoGamma_opNorm_eq_sampleDimension_div_mass_mul_wishartGamma
        (p := p) (q := q) (σ := σ) (G := G) hs hTpos
    calc
      gaussianMass p q σ ω *
          sphericalGammaOpNorm (p := p) (q := q) (σ := σ)
            (gaussianDirection (p := p) (q := q) (σ := σ) ω)
          = T * opNorm (rhoGamma G) := by
              simp [G, T, gaussianMass, gaussianDirection, sphericalGammaOpNorm,
                rhoGamma, rho]
      _ = T * ((sampleDimension σ / T) *
          opNorm (wishartGamma (p := p) (q := q) (σ := σ) G)) := by
              rw [hρ]
      _ = sampleDimension σ *
          opNorm (wishartGamma (p := p) (q := q) (σ := σ) G) := by
              field_simp [ne_of_gt hTpos]
      _ = sampleDimension σ *
          opNorm
            (wishartGamma (p := p) (q := q) (σ := σ)
              (gaussianMatrix p q σ ω)) := by
              rfl
  · have hTzero : T = 0 := le_antisymm (not_lt.mp hTpos) hTnonneg
    have hnormsq : frobeniusNorm G ^ 2 = 0 := by
      simpa [T, frobeniusMass] using hTzero
    have hnorm : frobeniusNorm G = 0 :=
      sq_eq_zero_iff.mp hnormsq
    have hGzero : G = 0 := by
      simpa [frobeniusNorm] using (norm_eq_zero.mp hnorm)
    have hMassZero : gaussianMass p q σ ω = 0 := by
      simpa [G, T, gaussianMass] using hTzero
    have hWzero :
        wishartGamma (p := p) (q := q) (σ := σ)
          (gaussianMatrix p q σ ω) = 0 := by
      change wishartGamma (p := p) (q := q) (σ := σ) G = 0
      simp [hGzero, wishartGamma, wishart, densityMatrix,
        RandomMatrixModel.gamma]
    calc
      gaussianMass p q σ ω *
          sphericalGammaOpNorm (p := p) (q := q) (σ := σ)
            (gaussianDirection (p := p) (q := q) (σ := σ) ω)
          = 0 := by
              rw [hMassZero]
              simp
      _ = sampleDimension σ *
          opNorm
            (wishartGamma (p := p) (q := q) (σ := σ)
              (gaussianMatrix p q σ ω)) := by
              rw [hWzero]
              simp [opNorm]

/-- Integral form of `R² ‖(XX*)^Γ‖∞ = s ‖W^Γ‖∞`. -/
theorem gaussianQuadraticGammaLiftMean_eq_sampleDimension_mul_wishartGammaMean
    (hs : Fintype.card σ ≠ 0) :
    gaussianQuadraticGammaLiftMean (p := p) (q := q) (σ := σ) =
      sampleDimension σ *
        gaussianWishartGammaOpNormMean (p := p) (q := q) (σ := σ) := by
  rw [gaussianQuadraticGammaLiftMean, gaussianWishartGammaOpNormMean]
  rw [show (fun ω : Ω p q σ =>
        gaussianMass p q σ ω *
          sphericalGammaOpNorm (p := p) (q := q) (σ := σ)
            (gaussianDirection (p := p) (q := q) (σ := σ) ω)) =
      fun ω : Ω p q σ =>
        sampleDimension σ *
          opNorm
            (wishartGamma (p := p) (q := q) (σ := σ)
              (gaussianMatrix p q σ ω)) by
    funext ω
    exact
      gaussianQuadraticGammaLift_integrand_eq_sampleDimension_mul_wishartGammaOpNorm
        (p := p) (q := q) (σ := σ) hs ω]
  rw [integral_const_mul]

/-! ## Normalized expectation bounds -/

omit [DecidableEq p] [DecidableEq q] in
/-- Normalized sample expectation bound obtained by cancelling the positive
radial factor. -/
theorem sphericalSampleOpNormMean_le_of_gaussian_bound
    {C d : ℝ}
    (hIndep :
      gaussianRadius (p := p) (q := q) (σ := σ) ⟂ᵢ[gaussianMeasure p q σ]
        gaussianDirection (p := p) (q := q) (σ := σ))
    (hRadialPos : 0 < gaussianRadialMean (p := p) (q := q) (σ := σ))
    (hGaussianBound :
      gaussianSampleOpNormMean (p := p) (q := q) (σ := σ) ≤
        gaussianRadialMean (p := p) (q := q) (σ := σ) * (C / d)) :
    sphericalSampleOpNormMean (p := p) (q := q) (σ := σ) ≤ C / d := by
  exact _root_.AppendixB.spherical_expectation_bound_from_radial_factorization
    (hRadialMean := hRadialPos)
    (hFactor :=
      gaussianSampleOpNormMean_factorization_of_indep
        (p := p) (q := q) (σ := σ) hIndep)
    (hBound := hGaussianBound)

omit [DecidableEq p] [DecidableEq q] in
/-- The same normalized sample expectation bound, with the repo's already
proved Gaussian sample-operator expectation estimate plugged in.  The single
remaining scalar hypothesis is the expected comparison between that Gaussian
estimate and the radial scale. -/
theorem sphericalSampleOpNormMean_le_of_standard_gaussian_estimate
    {C d : ℝ}
    (hIndep :
      gaussianRadius (p := p) (q := q) (σ := σ) ⟂ᵢ[gaussianMeasure p q σ]
        gaussianDirection (p := p) (q := q) (σ := σ))
    (hRadialPos : 0 < gaussianRadialMean (p := p) (q := q) (σ := σ))
    (hScale :
      17 * Real.sqrt (bipartiteDimension p q + sampleDimension σ + 1) ≤
        gaussianRadialMean (p := p) (q := q) (σ := σ) * (C / d)) :
    sphericalSampleOpNormMean (p := p) (q := q) (σ := σ) ≤ C / d := by
  refine sphericalSampleOpNormMean_le_of_gaussian_bound
    (p := p) (q := q) (σ := σ) hIndep hRadialPos ?_
  calc
    gaussianSampleOpNormMean (p := p) (q := q) (σ := σ)
        ≤ 17 * Real.sqrt (bipartiteDimension p q + sampleDimension σ + 1) := by
          simpa [gaussianSampleOpNormMean] using
            sampleOpNorm_integral_le (p := p) (q := q) (σ := σ)
    _ ≤ gaussianRadialMean (p := p) (q := q) (σ := σ) * (C / d) := hScale

/-- Normalized Wishart/Gamma expectation bound obtained by cancelling the
positive squared-radial factor. -/
theorem sphericalGammaOpNormMean_le_of_quadratic_lift_bound
    {C d : ℝ}
    (hIndep :
      gaussianRadiusSq (p := p) (q := q) (σ := σ) ⟂ᵢ[gaussianMeasure p q σ]
        gaussianDirection (p := p) (q := q) (σ := σ))
    (hQuadraticRadialPos :
      0 < gaussianQuadraticRadialMean (p := p) (q := q) (σ := σ))
    (hQuadraticLiftBound :
      gaussianQuadraticGammaLiftMean (p := p) (q := q) (σ := σ) ≤
        gaussianQuadraticRadialMean (p := p) (q := q) (σ := σ) * (C / d ^ 2)) :
    sphericalGammaOpNormMean (p := p) (q := q) (σ := σ) ≤ C / d ^ 2 := by
  exact _root_.AppendixB.spherical_gamma_expectation_bound_from_radial_factorization
    (hRadialSecondMean := hQuadraticRadialPos)
    (hFactor :=
      gaussianQuadraticGammaLiftMean_factorization_of_indep
        (p := p) (q := q) (σ := σ) hIndep)
    (hBound := hQuadraticLiftBound)

/-- Appendix-facing pair of normalized expectation bounds.

This is the clean wiring theorem: the two normalized estimates follow from
the two radius-direction factorization statements and the two Gaussian lift
bounds at the matching radial scales. -/
theorem normalized_expectation_bounds_of_radial_independence_and_lift_bounds
    {C₁ C₂ d : ℝ}
    (hIndepR :
      gaussianRadius (p := p) (q := q) (σ := σ) ⟂ᵢ[gaussianMeasure p q σ]
        gaussianDirection (p := p) (q := q) (σ := σ))
    (hIndepR2 :
      gaussianRadiusSq (p := p) (q := q) (σ := σ) ⟂ᵢ[gaussianMeasure p q σ]
        gaussianDirection (p := p) (q := q) (σ := σ))
    (hRadialPos : 0 < gaussianRadialMean (p := p) (q := q) (σ := σ))
    (hQuadraticRadialPos :
      0 < gaussianQuadraticRadialMean (p := p) (q := q) (σ := σ))
    (hSampleLiftBound :
      gaussianSampleOpNormMean (p := p) (q := q) (σ := σ) ≤
        gaussianRadialMean (p := p) (q := q) (σ := σ) * (C₁ / d))
    (hGammaLiftBound :
      gaussianQuadraticGammaLiftMean (p := p) (q := q) (σ := σ) ≤
        gaussianQuadraticRadialMean (p := p) (q := q) (σ := σ) *
          (C₂ / d ^ 2)) :
    sphericalSampleOpNormMean (p := p) (q := q) (σ := σ) ≤ C₁ / d ∧
      sphericalGammaOpNormMean (p := p) (q := q) (σ := σ) ≤ C₂ / d ^ 2 := by
  constructor
  · exact sphericalSampleOpNormMean_le_of_gaussian_bound
      (p := p) (q := q) (σ := σ)
      hIndepR hRadialPos hSampleLiftBound
  · exact sphericalGammaOpNormMean_le_of_quadratic_lift_bound
      (p := p) (q := q) (σ := σ)
      hIndepR2 hQuadraticRadialPos hGammaLiftBound

/-- Same normalized expectation bounds, with the squared-radius independence
derived automatically from the radius-direction independence. -/
theorem normalized_expectation_bounds_of_radius_independence_and_lift_bounds
    {C₁ C₂ d : ℝ}
    (hIndepR :
      gaussianRadius (p := p) (q := q) (σ := σ) ⟂ᵢ[gaussianMeasure p q σ]
        gaussianDirection (p := p) (q := q) (σ := σ))
    (hRadialPos : 0 < gaussianRadialMean (p := p) (q := q) (σ := σ))
    (hQuadraticRadialPos :
      0 < gaussianQuadraticRadialMean (p := p) (q := q) (σ := σ))
    (hSampleLiftBound :
      gaussianSampleOpNormMean (p := p) (q := q) (σ := σ) ≤
        gaussianRadialMean (p := p) (q := q) (σ := σ) * (C₁ / d))
    (hGammaLiftBound :
      gaussianQuadraticGammaLiftMean (p := p) (q := q) (σ := σ) ≤
        gaussianQuadraticRadialMean (p := p) (q := q) (σ := σ) *
          (C₂ / d ^ 2)) :
    sphericalSampleOpNormMean (p := p) (q := q) (σ := σ) ≤ C₁ / d ∧
      sphericalGammaOpNormMean (p := p) (q := q) (σ := σ) ≤ C₂ / d ^ 2 := by
  exact normalized_expectation_bounds_of_radial_independence_and_lift_bounds
    (p := p) (q := q) (σ := σ)
    hIndepR
    (gaussianRadiusSq_indep_gaussianDirection_of_gaussianRadius_indep
      (p := p) (q := q) (σ := σ) hIndepR)
    hRadialPos hQuadraticRadialPos hSampleLiftBound hGammaLiftBound

omit [DecidableEq p] [DecidableEq q] in
/-- Concrete no-input value of the squared-radial mean, in terms of the two
finite dimensions already used throughout the high-probability package. -/
theorem gaussianQuadraticRadialMean_eq :
    gaussianQuadraticRadialMean (p := p) (q := q) (σ := σ) =
      bipartiteDimension p q * sampleDimension σ := by
  simpa [gaussianQuadraticRadialMean] using
    gaussianMass_integral_eq (p := p) (q := q) (σ := σ)

omit [DecidableEq p] [DecidableEq q] in
/-- Positivity of the squared-radial mean under the natural nondegeneracy
assumptions. -/
theorem gaussianQuadraticRadialMean_pos
    (hD : 0 < bipartiteDimension p q)
    (hs : 0 < sampleDimension σ) :
    0 < gaussianQuadraticRadialMean (p := p) (q := q) (σ := σ) := by
  simpa [gaussianQuadraticRadialMean] using
    gaussianMass_expectation_pos (p := p) (q := q) (σ := σ) hD hs

/-- Radialize the concrete Gaussian Wishart-Gamma expectation bound back to
the Hilbert--Schmidt sphere.  Under the paper normalization `D = d²`,
`E ‖W^Γ‖∞ ≤ Cλ` implies
`E_sphere ‖(XX*)^Γ‖∞ ≤ Cλ / d²`. -/
theorem sphericalGammaOpNormMean_le_of_wishartGamma_mean_bound
    {C_lam d : ℝ}
    (hIndep :
      gaussianRadiusSq (p := p) (q := q) (σ := σ) ⟂ᵢ[gaussianMeasure p q σ]
        gaussianDirection (p := p) (q := q) (σ := σ))
    (hQuadraticRadialPos :
      0 < gaussianQuadraticRadialMean (p := p) (q := q) (σ := σ))
    (hd : 0 < d)
    (hD : bipartiteDimension p q = d ^ 2)
    (hWishartMean :
      gaussianWishartGammaOpNormMean (p := p) (q := q) (σ := σ) ≤ C_lam) :
    sphericalGammaOpNormMean (p := p) (q := q) (σ := σ) ≤ C_lam / d ^ 2 := by
  have hs : Fintype.card σ ≠ 0 := by
    intro hzero
    have hRadialZero :
        gaussianQuadraticRadialMean (p := p) (q := q) (σ := σ) = 0 := by
      rw [gaussianQuadraticRadialMean_eq (p := p) (q := q) (σ := σ)]
      simp [sampleDimension, hzero]
    exact (ne_of_gt hQuadraticRadialPos) hRadialZero
  refine sphericalGammaOpNormMean_le_of_quadratic_lift_bound
    (p := p) (q := q) (σ := σ)
    (C := C_lam) (d := d) hIndep hQuadraticRadialPos ?_
  calc
    gaussianQuadraticGammaLiftMean (p := p) (q := q) (σ := σ)
        = sampleDimension σ *
            gaussianWishartGammaOpNormMean (p := p) (q := q) (σ := σ) := by
            exact
              gaussianQuadraticGammaLiftMean_eq_sampleDimension_mul_wishartGammaMean
                (p := p) (q := q) (σ := σ) hs
    _ ≤ sampleDimension σ * C_lam := by
            exact mul_le_mul_of_nonneg_left hWishartMean sampleDimension_nonneg
    _ = gaussianQuadraticRadialMean (p := p) (q := q) (σ := σ) *
          (C_lam / d ^ 2) := by
            rw [gaussianQuadraticRadialMean_eq (p := p) (q := q) (σ := σ), hD]
            field_simp [pow_ne_zero 2 (ne_of_gt hd)]

end AppendixB
end PptFactorization
