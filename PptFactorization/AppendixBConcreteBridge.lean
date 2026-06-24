import PptFactorization.AppendixB
import PptFactorization.AppendixBPolarRadial
import PptFactorization.AppendixBLevyPolarBridge
import PptFactorization.AppendixBWishartBridge

/-!
# Downstream bridge for Appendix B

This file sits downstream of `AppendixB.lean`. It packages the concrete
Gaussian/Wishart inputs that are already available in the project in a form
that is directly usable by the paper-facing Appendix B statements.

The probability inputs and the Gaussian radial/spherical expectation
factorizations are concrete: the canonical expectation package below uses the
proved radius-direction independence from the polar bridge.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal

noncomputable section

namespace PptFactorization
namespace AppendixB

open RandomMatrixModel GaussianModel
open HighProbabilityBounds

variable {p q σ : Type*}
variable [Fintype p] [Fintype q] [Fintype σ]
variable [DecidableEq p] [DecidableEq q]

/-- Concrete paper-facing threshold for the normalized sample operator norm
event `Ω₁ = {‖X‖∞ ≤ a / d}` coming from the canonical high-probability
package. -/
noncomputable def concreteSampleOpNormThreshold : ℝ :=
  let pkg := concreteHighProbabilityBounds (p := p) (q := q) (σ := σ)
  Real.sqrt (pkg.wishartConstant * sampleDimension σ / pkg.massConstant)

/-- Concrete paper-facing threshold for the normalized partially transposed
event `Ω₂ = {‖(XX*)^Γ‖∞ ≤ b / d²}` coming from the canonical high-probability
package. -/
noncomputable def concreteRhoGammaOpNormThreshold : ℝ :=
  let pkg := concreteHighProbabilityBounds (p := p) (q := q) (σ := σ)
  pkg.gammaWishartConstant * sampleDimension σ / pkg.massConstant

/-- The probability-side Appendix B inputs that are already fully concrete in
the repo.

This package records the two normalized good-set thresholds and the two
corresponding tails, already rewritten in the Appendix B scale
`goodSetTail (1/12) d = exp(-(d^2/12))`. -/
structure ConcreteProbabilityInputs (d : ℝ) where
  sampleThreshold : ℝ
  gammaThreshold : ℝ
  sampleTail :
    (gaussianMeasure p q σ).real
        ((normalizedSampleOpNormEvent
          (p := p) (q := q) (σ := σ) sampleThreshold d)ᶜ) ≤
      _root_.AppendixB.goodSetTail (1 / 12 : ℝ) d
  gammaTail :
    (gaussianMeasure p q σ).real
        ((normalizedRhoGammaOpNormEvent
          (p := p) (q := q) (σ := σ) gammaThreshold d)ᶜ) ≤
      _root_.AppendixB.goodSetTail (1 / 12 : ℝ) d

/-- Closed scalar package for the expectation-side inputs.

The fields record exactly the radial/spherical expectation data used by the
Appendix B cancellation lemmas:

* the Gaussian expectation factorization through the radial mean,
* the corresponding Gaussian expectation bound,
* the Wishart/Gamma expectation factorization through the squared radial mean,
* the corresponding Wishart/Gamma expectation bound.

The canonical concrete value is `concreteRemainingExpectationInputs` below. -/
structure RemainingExpectationInputs (d : ℝ) where
  gaussianMean : ℝ
  radialMean : ℝ
  sphericalMean : ℝ
  wishartGammaMean : ℝ
  radialSecondMean : ℝ
  sphericalGammaMean : ℝ
  sampleConstant : ℝ
  gammaConstant : ℝ
  hRadialMean : 0 < radialMean
  hSampleFactor : gaussianMean = radialMean * sphericalMean
  hSampleBound : gaussianMean ≤ radialMean * (sampleConstant / d)
  hRadialSecondMean : 0 < radialSecondMean
  hGammaFactor : wishartGammaMean = radialSecondMean * sphericalGammaMean
  hGammaBound : wishartGammaMean ≤ radialSecondMean * (gammaConstant / d ^ 2)

/-- The Gaussian radial factor appearing in the Appendix B expectation
normalization step. In the manuscript this is the scalar factor coming from
the polar decomposition `G = R X`, typically instantiated by `E R`. -/
def RemainingExpectationInputs.gaussianRadialFactor
    {d : ℝ} (I : RemainingExpectationInputs (d := d)) : ℝ :=
  I.radialMean

/-- Positivity of the Gaussian radial factor is part of the exact remaining
expectation input package. -/
theorem RemainingExpectationInputs.gaussianRadialFactor_pos
    {d : ℝ} (I : RemainingExpectationInputs (d := d)) :
    0 < I.gaussianRadialFactor := by
  exact I.hRadialMean

/-- The Gaussian spherical factor appearing in the Appendix B expectation
normalization step. In the manuscript this is the normalized-sphere
expectation multiplied by the radial factor to recover the Gaussian
expectation. -/
def RemainingExpectationInputs.gaussianSphericalFactor
    {d : ℝ} (I : RemainingExpectationInputs (d := d)) : ℝ :=
  I.sphericalMean

/-- The Gaussian expectation factorization is part of the exact remaining
appendix-facing expectation input package. -/
theorem RemainingExpectationInputs.gaussianExpectation_factorization
    {d : ℝ} (I : RemainingExpectationInputs (d := d)) :
    I.gaussianMean = I.gaussianRadialFactor * I.gaussianSphericalFactor := by
  simpa [RemainingExpectationInputs.gaussianRadialFactor,
    RemainingExpectationInputs.gaussianSphericalFactor] using I.hSampleFactor

/-- The normalized Appendix B target scale for the Gaussian expectation. -/
def RemainingExpectationInputs.gaussianSampleTarget
    {d : ℝ} (I : RemainingExpectationInputs (d := d)) : ℝ :=
  I.sampleConstant / d

/-- The Gaussian expectation upper bound at the correct normalized scale is
part of the exact remaining appendix-facing expectation input package. -/
theorem RemainingExpectationInputs.gaussianExpectation_le_target
    {d : ℝ} (I : RemainingExpectationInputs (d := d)) :
    I.gaussianMean ≤ I.gaussianRadialFactor * I.gaussianSampleTarget := by
  simpa [RemainingExpectationInputs.gaussianRadialFactor,
    RemainingExpectationInputs.gaussianSampleTarget] using I.hSampleBound

/-- The quadratic radial factor appearing in the Appendix B expectation
normalization step for the partially transposed/Wishart term. In the
manuscript this is typically instantiated by `E (R^2)`. -/
def RemainingExpectationInputs.quadraticRadialFactor
    {d : ℝ} (I : RemainingExpectationInputs (d := d)) : ℝ :=
  I.radialSecondMean

/-- Positivity of the quadratic radial factor is part of the exact remaining
appendix-facing expectation input package. -/
theorem RemainingExpectationInputs.quadraticRadialFactor_pos
    {d : ℝ} (I : RemainingExpectationInputs (d := d)) :
    0 < I.quadraticRadialFactor := by
  exact I.hRadialSecondMean

omit [DecidableEq p] [DecidableEq q] in
/-- Concrete no-input positivity of the quadratic radial mean in the Appendix
regime `D = d^2`, `s ≥ 1`. Concretely, this is the strict positivity of the
Gaussian mass expectation `E ‖G‖₂²`, i.e. the `E(R^2)` factor from the polar
decomposition step. -/
theorem concrete_quadraticRadialMean_eq
    {d : ℝ}
    (hDim : bipartiteDimension p q = d ^ 2) :
    ∫ ω : Ω p q σ, gaussianMass p q σ ω ∂gaussianMeasure p q σ =
      d ^ 2 * sampleDimension σ := by
  rw [gaussianMass_integral_eq (p := p) (q := q) (σ := σ), hDim]

omit [DecidableEq p] [DecidableEq q] in
/-- Concrete no-input positivity of the quadratic radial mean in the Appendix
regime `D = d^2`, `s ≥ 1`. Concretely, this is the strict positivity of the
Gaussian mass expectation `E ‖G‖₂²`, i.e. the `E(R^2)` factor from the polar
decomposition step. -/
theorem concrete_quadraticRadialMean_pos
    {d : ℝ}
    (hd : 0 < d)
    (hs : 1 ≤ sampleDimension σ)
    (hDim : bipartiteDimension p q = d ^ 2) :
    0 < ∫ ω : Ω p q σ, gaussianMass p q σ ω ∂gaussianMeasure p q σ := by
  rw [concrete_quadraticRadialMean_eq (p := p) (q := q) (σ := σ) hDim]
  positivity

/-- Concrete positivity of the linear Gaussian radial mean in the Appendix
regime `D = d²`, `s ≥ 1`. -/
theorem concrete_gaussianRadialMean_pos
    {d : ℝ}
    (hd : 0 < d)
    (hs : 1 ≤ sampleDimension σ)
    (hDim : bipartiteDimension p q = d ^ 2) :
    0 < gaussianRadialMean (p := p) (q := q) (σ := σ) := by
  have hsPos : 0 < sampleDimension σ := lt_of_lt_of_le zero_lt_one hs
  have hNpos : 0 < bipartiteDimension p q * sampleDimension σ := by
    rw [hDim]
    positivity
  have hsqrtPos :
      0 <
        Real.sqrt
          ((1 / 2 : ℝ) * bipartiteDimension p q * sampleDimension σ) := by
    exact Real.sqrt_pos.2 (by nlinarith [hNpos])
  have hexp_lt :
      Real.exp
          (-((1 / 6 : ℝ) * bipartiteDimension p q * sampleDimension σ)) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hfactorPos :
      0 <
        1 -
          Real.exp
            (-((1 / 6 : ℝ) * bipartiteDimension p q * sampleDimension σ)) :=
    sub_pos.mpr hexp_lt
  have hlowerPos :
      0 <
        Real.sqrt
            ((1 / 2 : ℝ) * bipartiteDimension p q * sampleDimension σ) *
          (1 -
            Real.exp
              (-((1 / 6 : ℝ) * bipartiteDimension p q * sampleDimension σ))) :=
    mul_pos hsqrtPos hfactorPos
  exact lt_of_lt_of_le hlowerPos
    (by
      simpa [gaussianRadialMean] using
        gaussianRadialMean_lower_bound_from_mass_tail
          (p := p) (q := q) (σ := σ))

/-- Canonical appendix-facing object built from supplied expectation
factorizations, with the quadratic radial factor fixed to the concrete Gaussian
mass expectation `E ‖G‖₂²`. -/
noncomputable def concreteRemainingExpectationInputs_of_factor_bounds
    {gaussianMean radialMean sphericalMean
      wishartGammaMean sphericalGammaMean C1 C2 d : ℝ}
    (hRadialMean : 0 < radialMean)
    (hSampleFactor : gaussianMean = radialMean * sphericalMean)
    (hSampleBound : gaussianMean ≤ radialMean * (C1 / d))
    (hd : 0 < d)
    (hs : 1 ≤ sampleDimension σ)
    (hDim : bipartiteDimension p q = d ^ 2)
    (hGammaFactor :
      wishartGammaMean =
        (∫ ω : Ω p q σ, gaussianMass p q σ ω ∂gaussianMeasure p q σ) *
          sphericalGammaMean)
    (hGammaBound :
      wishartGammaMean ≤
        (∫ ω : Ω p q σ, gaussianMass p q σ ω ∂gaussianMeasure p q σ) *
          (C2 / d ^ 2)) :
    RemainingExpectationInputs (d := d) :=
  { gaussianMean := gaussianMean
    radialMean := radialMean
    sphericalMean := sphericalMean
    wishartGammaMean := wishartGammaMean
    radialSecondMean :=
      ∫ ω : Ω p q σ, gaussianMass p q σ ω ∂gaussianMeasure p q σ
    sphericalGammaMean := sphericalGammaMean
    sampleConstant := C1
    gammaConstant := C2
    hRadialMean := hRadialMean
    hSampleFactor := hSampleFactor
    hSampleBound := hSampleBound
    hRadialSecondMean :=
      concrete_quadraticRadialMean_pos (p := p) (q := q) (σ := σ) hd hs hDim
    hGammaFactor := hGammaFactor
    hGammaBound := hGammaBound }

/-- Canonical no-input scalar package for the expectation side of the concrete
bridge.

The actual Gaussian/Wishart means, spherical means, and concrete radial factors
are used.  The factorization fields are discharged from the proved
radius-direction independence theorem, so this package no longer carries a
separate independence input. -/
noncomputable def concreteRemainingExpectationInputs
    {d : ℝ}
    (hd : 0 < d)
    (hs : 1 ≤ sampleDimension σ)
    (hDim : bipartiteDimension p q = d ^ 2) :
    RemainingExpectationInputs (d := d) := by
  have hsPosReal : 0 < (Fintype.card σ : ℝ) := by
    simpa [sampleDimension] using lt_of_lt_of_le zero_lt_one hs
  have hsPosNat : 0 < Fintype.card σ := by
    exact_mod_cast hsPosReal
  letI : Nonempty σ := Fintype.card_pos_iff.mp hsPosNat
  have hBipPos : 0 < bipartiteDimension p q := by
    rw [hDim]
    positivity
  have hBipPosNat : 0 < Fintype.card (BipIndex p q) := by
    have hBipPosReal : 0 < (Fintype.card (BipIndex p q) : ℝ) := by
      simpa [bipartiteDimension] using hBipPos
    exact_mod_cast hBipPosReal
  let b : BipIndex p q := Classical.choice (Fintype.card_pos_iff.mp hBipPosNat)
  letI : Nonempty p := ⟨b.1⟩
  letI : Nonempty q := ⟨b.2⟩
  exact
  { gaussianMean :=
      gaussianSampleOpNormMean (p := p) (q := q) (σ := σ)
    radialMean := gaussianRadialMean (p := p) (q := q) (σ := σ)
    sphericalMean := sphericalSampleOpNormMean (p := p) (q := q) (σ := σ)
    wishartGammaMean :=
      gaussianQuadraticGammaLiftMean (p := p) (q := q) (σ := σ)
    radialSecondMean := gaussianQuadraticRadialMean (p := p) (q := q) (σ := σ)
    sphericalGammaMean := sphericalGammaOpNormMean (p := p) (q := q) (σ := σ)
    sampleConstant :=
      d * sphericalSampleOpNormMean (p := p) (q := q) (σ := σ)
    gammaConstant :=
      d ^ 2 * sphericalGammaOpNormMean (p := p) (q := q) (σ := σ)
    hRadialMean :=
      concrete_gaussianRadialMean_pos (p := p) (q := q) (σ := σ) hd hs hDim
    hSampleFactor := by
      exact
        gaussianSampleOpNormMean_factorization_of_indep
          (p := p) (q := q) (σ := σ)
          (gaussianRadius_indep_gaussianDirection
            (p := p) (q := q) (σ := σ))
    hSampleBound := by
      have hFactor :
          gaussianSampleOpNormMean (p := p) (q := q) (σ := σ) =
            gaussianRadialMean (p := p) (q := q) (σ := σ) *
              sphericalSampleOpNormMean (p := p) (q := q) (σ := σ) :=
        gaussianSampleOpNormMean_factorization_of_indep
          (p := p) (q := q) (σ := σ)
          (gaussianRadius_indep_gaussianDirection
            (p := p) (q := q) (σ := σ))
      rw [hFactor]
      have htarget :
          gaussianRadialMean (p := p) (q := q) (σ := σ) *
              sphericalSampleOpNormMean (p := p) (q := q) (σ := σ) =
            gaussianRadialMean (p := p) (q := q) (σ := σ) *
              ((d * sphericalSampleOpNormMean (p := p) (q := q) (σ := σ)) / d) := by
        field_simp [ne_of_gt hd]
      rw [htarget]
    hRadialSecondMean := by
      have hsPos : 0 < sampleDimension σ := lt_of_lt_of_le zero_lt_one hs
      exact gaussianQuadraticRadialMean_pos
        (p := p) (q := q) (σ := σ) hBipPos hsPos
    hGammaFactor := by
      exact
        gaussianQuadraticGammaLiftMean_factorization_of_indep
          (p := p) (q := q) (σ := σ)
          (gaussianRadiusSq_indep_gaussianDirection
            (p := p) (q := q) (σ := σ))
    hGammaBound := by
      have hFactor :
          gaussianQuadraticGammaLiftMean (p := p) (q := q) (σ := σ) =
            gaussianQuadraticRadialMean (p := p) (q := q) (σ := σ) *
              sphericalGammaOpNormMean (p := p) (q := q) (σ := σ) :=
        gaussianQuadraticGammaLiftMean_factorization_of_indep
          (p := p) (q := q) (σ := σ)
          (gaussianRadiusSq_indep_gaussianDirection
            (p := p) (q := q) (σ := σ))
      rw [hFactor]
      have htarget :
          gaussianQuadraticRadialMean (p := p) (q := q) (σ := σ) *
              sphericalGammaOpNormMean (p := p) (q := q) (σ := σ) =
            gaussianQuadraticRadialMean (p := p) (q := q) (σ := σ) *
              ((d ^ 2 * sphericalGammaOpNormMean (p := p) (q := q) (σ := σ)) /
                d ^ 2) := by
        field_simp [pow_ne_zero 2 (ne_of_gt hd)]
      rw [htarget]
  }

/-- In the appendix regime `D = d^2`, the quadratic radial factor of
`concreteRemainingExpectationInputs` is exactly `d^2 s`. -/
theorem concreteRemainingExpectationInputs_quadraticRadialFactor_eq
    {d : ℝ}
    (hd : 0 < d)
    (hs : 1 ≤ sampleDimension σ)
    (hDim : bipartiteDimension p q = d ^ 2) :
    (concreteRemainingExpectationInputs
      (p := p) (q := q) (σ := σ)
      (d := d) hd hs hDim
      ).quadraticRadialFactor =
      d ^ 2 * sampleDimension σ := by
  change gaussianQuadraticRadialMean (p := p) (q := q) (σ := σ) =
    d ^ 2 * sampleDimension σ
  rw [gaussianQuadraticRadialMean_eq (p := p) (q := q) (σ := σ), hDim]

/-- The spherical factor appearing in the Appendix B expectation normalization
step for the partially transposed/Wishart term. In the manuscript this is the
normalized-sphere expectation multiplied by `E (R^2)` to recover the Gaussian
Wishart/Gamma expectation. -/
def RemainingExpectationInputs.quadraticSphericalFactor
    {d : ℝ} (I : RemainingExpectationInputs (d := d)) : ℝ :=
  I.sphericalGammaMean

/-- The Wishart/Gamma expectation factorization is part of the exact remaining
appendix-facing expectation input package. -/
theorem RemainingExpectationInputs.wishartGammaExpectation_factorization
    {d : ℝ} (I : RemainingExpectationInputs (d := d)) :
    I.wishartGammaMean =
      I.quadraticRadialFactor * I.quadraticSphericalFactor := by
  simpa [RemainingExpectationInputs.quadraticRadialFactor,
    RemainingExpectationInputs.quadraticSphericalFactor] using I.hGammaFactor

/-- The normalized Appendix B target scale for the Wishart/Gamma expectation. -/
def RemainingExpectationInputs.quadraticGammaTarget
    {d : ℝ} (I : RemainingExpectationInputs (d := d)) : ℝ :=
  I.gammaConstant / d ^ 2

/-- The Wishart/Gamma expectation upper bound at the correct normalized scale
is part of the exact remaining appendix-facing expectation input package. -/
theorem RemainingExpectationInputs.wishartGammaExpectation_le_target
    {d : ℝ} (I : RemainingExpectationInputs (d := d)) :
    I.wishartGammaMean ≤ I.quadraticRadialFactor * I.quadraticGammaTarget := by
  simpa [RemainingExpectationInputs.quadraticRadialFactor,
    RemainingExpectationInputs.quadraticGammaTarget] using I.hGammaBound

/-- Package the six scalar expectation hypotheses into one reusable object of
type `RemainingExpectationInputs`. This is the exact missing appendix-facing
expectation input at the current state of the development. -/
def remainingExpectationInputsFromScalars
    {gaussianMean radialMean sphericalMean
      wishartGammaMean radialSecondMean sphericalGammaMean
      sampleConstant gammaConstant d : ℝ}
    (hRadialMean : 0 < radialMean)
    (hSampleFactor : gaussianMean = radialMean * sphericalMean)
    (hSampleBound : gaussianMean ≤ radialMean * (sampleConstant / d))
    (hRadialSecondMean : 0 < radialSecondMean)
    (hGammaFactor : wishartGammaMean = radialSecondMean * sphericalGammaMean)
    (hGammaBound : wishartGammaMean ≤ radialSecondMean * (gammaConstant / d ^ 2)) :
    RemainingExpectationInputs (d := d) :=
  { gaussianMean := gaussianMean
    radialMean := radialMean
    sphericalMean := sphericalMean
    wishartGammaMean := wishartGammaMean
    radialSecondMean := radialSecondMean
    sphericalGammaMean := sphericalGammaMean
    sampleConstant := sampleConstant
    gammaConstant := gammaConstant
    hRadialMean := hRadialMean
    hSampleFactor := hSampleFactor
    hSampleBound := hSampleBound
    hRadialSecondMean := hRadialSecondMean
    hGammaFactor := hGammaFactor
    hGammaBound := hGammaBound }

/-- The expectation-side normalization follows from the closed
`RemainingExpectationInputs` structure: no more and no less. -/
theorem RemainingExpectationInputs.to_normalized_bounds
    {d : ℝ} (I : RemainingExpectationInputs (d := d)) :
    I.sphericalMean ≤ I.sampleConstant / d ∧
    I.sphericalGammaMean ≤ I.gammaConstant / d ^ 2 := by
  exact _root_.AppendixB.appendixB_spherical_normalization_expectation_inputs
    (gaussianMean := I.gaussianMean)
    (radialMean := I.radialMean)
    (sphericalMean := I.sphericalMean)
    (wishartGammaMean := I.wishartGammaMean)
    (radialSecondMean := I.radialSecondMean)
    (sphericalGammaMean := I.sphericalGammaMean)
    (C1 := I.sampleConstant)
    (C2 := I.gammaConstant)
    (d := d)
    I.hRadialMean
    I.hSampleFactor
    I.hSampleBound
    I.hRadialSecondMean
    I.hGammaFactor
    I.hGammaBound

/-- Concrete no-input Gaussian expectation estimate supplied by the canonical
`concreteRemainingExpectationInputs` package. -/
theorem concreteRemainingExpectationInputs_gaussianExpectation_le_target
    {d : ℝ}
    (hd : 0 < d)
    (hs : 1 ≤ sampleDimension σ)
    (hDim : bipartiteDimension p q = d ^ 2) :
    (concreteRemainingExpectationInputs
      (p := p) (q := q) (σ := σ)
      (d := d) hd hs hDim
      ).gaussianMean ≤
      (concreteRemainingExpectationInputs
        (p := p) (q := q) (σ := σ)
        (d := d) hd hs hDim
        ).gaussianRadialFactor *
        (concreteRemainingExpectationInputs
          (p := p) (q := q) (σ := σ)
          (d := d) hd hs hDim
          ).gaussianSampleTarget := by
  exact
    (concreteRemainingExpectationInputs
      (p := p) (q := q) (σ := σ)
      (d := d) hd hs hDim
      ).gaussianExpectation_le_target

/-- Concrete no-input Wishart/Gamma expectation estimate supplied by the
canonical `concreteRemainingExpectationInputs` package. -/
theorem concreteRemainingExpectationInputs_wishartGammaExpectation_le_target
    {d : ℝ}
    (hd : 0 < d)
    (hs : 1 ≤ sampleDimension σ)
    (hDim : bipartiteDimension p q = d ^ 2) :
    (concreteRemainingExpectationInputs
      (p := p) (q := q) (σ := σ)
      (d := d) hd hs hDim
      ).wishartGammaMean ≤
      (concreteRemainingExpectationInputs
        (p := p) (q := q) (σ := σ)
        (d := d) hd hs hDim
        ).quadraticRadialFactor *
        (concreteRemainingExpectationInputs
          (p := p) (q := q) (σ := σ)
          (d := d) hd hs hDim
          ).quadraticGammaTarget := by
  exact
    (concreteRemainingExpectationInputs
      (p := p) (q := q) (σ := σ)
      (d := d) hd hs hDim
      ).wishartGammaExpectation_le_target

/-- Concrete no-input pair of normalized expectation bounds obtained from the
canonical `concreteRemainingExpectationInputs` package. -/
theorem concreteRemainingExpectationInputs_to_normalized_bounds
    {d : ℝ}
    (hd : 0 < d)
    (hs : 1 ≤ sampleDimension σ)
    (hDim : bipartiteDimension p q = d ^ 2) :
    let I :=
      concreteRemainingExpectationInputs
        (p := p) (q := q) (σ := σ)
        (d := d) hd hs hDim
    I.sphericalMean ≤ I.sampleConstant / d ∧
      I.sphericalGammaMean ≤ I.gammaConstant / d ^ 2 := by
  exact
    (concreteRemainingExpectationInputs
      (p := p) (q := q) (σ := σ)
      (d := d) hd hs hDim
      ).to_normalized_bounds

/-- Probability half of the normalized operator-norm input lemma, in Appendix
B notation, using the canonical concrete Gaussian/Wishart package already
proved in the repo. -/
theorem concrete_normalized_operator_norm_probability_inputs
    {d : ℝ}
    (hd : 0 < d)
    (hs : 1 ≤ sampleDimension σ)
    (hDim : bipartiteDimension p q = d ^ 2)
    (hLarge : 12 * Real.log 2 ≤ d ^ 2) :
    (gaussianMeasure p q σ).real
        ((normalizedSampleOpNormEvent
          (p := p) (q := q) (σ := σ)
          (concreteSampleOpNormThreshold (p := p) (q := q) (σ := σ)) d)ᶜ) ≤
      Real.exp (-((1 / 12 : ℝ) * d ^ 2)) ∧
    (gaussianMeasure p q σ).real
        ((normalizedRhoGammaOpNormEvent
          (p := p) (q := q) (σ := σ)
          (concreteRhoGammaOpNormThreshold (p := p) (q := q) (σ := σ)) d)ᶜ) ≤
      Real.exp (-((1 / 12 : ℝ) * d ^ 2)) := by
  simpa [concreteSampleOpNormThreshold, concreteRhoGammaOpNormThreshold] using
    (ConcreteNormalizedOperatorNormInputsPaperForm
      (p := p) (q := q) (σ := σ) hd hs hDim hLarge)

/-- Canonical concrete package of the Appendix B probability inputs already
proved in the repo. -/
noncomputable def concreteProbabilityInputs
    {d : ℝ}
    (hd : 0 < d)
    (hs : 1 ≤ sampleDimension σ)
    (hDim : bipartiteDimension p q = d ^ 2)
    (hLarge : 12 * Real.log 2 ≤ d ^ 2) :
    ConcreteProbabilityInputs (p := p) (q := q) (σ := σ) d := by
  have hprob :=
    concrete_normalized_operator_norm_probability_inputs
      (p := p) (q := q) (σ := σ) hd hs hDim hLarge
  refine
    { sampleThreshold := concreteSampleOpNormThreshold (p := p) (q := q) (σ := σ)
      gammaThreshold := concreteRhoGammaOpNormThreshold (p := p) (q := q) (σ := σ)
      sampleTail := ?_
      gammaTail := ?_ }
  · simpa [_root_.AppendixB.goodSetTail] using hprob.1
  · simpa [_root_.AppendixB.goodSetTail] using hprob.2

/-- Canonical concrete Appendix B bridge.

It combines the concrete probability package with the canonical concrete
expectation package, so no external `RemainingExpectationInputs` value is
needed. -/
theorem concrete_appendixB_inputs
    {d : ℝ}
    (hd : 0 < d)
    (hs : 1 ≤ sampleDimension σ)
    (hDim : bipartiteDimension p q = d ^ 2)
    (hLarge : 12 * Real.log 2 ≤ d ^ 2) :
    let P := concreteProbabilityInputs
      (p := p) (q := q) (σ := σ) hd hs hDim hLarge
    let I := concreteRemainingExpectationInputs
      (p := p) (q := q) (σ := σ) hd hs hDim
    I.sphericalMean ≤ I.sampleConstant / d ∧
    I.sphericalGammaMean ≤ I.gammaConstant / d ^ 2 ∧
    (gaussianMeasure p q σ).real
        ((normalizedSampleOpNormEvent
          (p := p) (q := q) (σ := σ) P.sampleThreshold d)ᶜ) ≤
      _root_.AppendixB.goodSetTail (1 / 12 : ℝ) d ∧
    (gaussianMeasure p q σ).real
        ((normalizedRhoGammaOpNormEvent
          (p := p) (q := q) (σ := σ) P.gammaThreshold d)ᶜ) ≤
      _root_.AppendixB.goodSetTail (1 / 12 : ℝ) d := by
  let P := concreteProbabilityInputs
    (p := p) (q := q) (σ := σ) hd hs hDim hLarge
  let I := concreteRemainingExpectationInputs
    (p := p) (q := q) (σ := σ) hd hs hDim
  have hExp := concreteRemainingExpectationInputs_to_normalized_bounds
    (p := p) (q := q) (σ := σ) hd hs hDim
  exact ⟨hExp.1, hExp.2, P.sampleTail, P.gammaTail⟩

/-- Compatibility theorem for callers that still provide their own
`RemainingExpectationInputs` package.

The canonical no-gap route is `concrete_appendixB_inputs`; this version is kept
for downstream code that wants to plug in different scalar constants. -/
theorem concrete_appendixB_inputs_with_explicit_remaining_gap
    {d : ℝ}
    (hd : 0 < d)
    (hs : 1 ≤ sampleDimension σ)
    (hDim : bipartiteDimension p q = d ^ 2)
    (hLarge : 12 * Real.log 2 ≤ d ^ 2)
    (I : RemainingExpectationInputs (d := d)) :
    let P := concreteProbabilityInputs
      (p := p) (q := q) (σ := σ) hd hs hDim hLarge
    I.sphericalMean ≤ I.sampleConstant / d ∧
    I.sphericalGammaMean ≤ I.gammaConstant / d ^ 2 ∧
    (gaussianMeasure p q σ).real
        ((normalizedSampleOpNormEvent
          (p := p) (q := q) (σ := σ) P.sampleThreshold d)ᶜ) ≤
      _root_.AppendixB.goodSetTail (1 / 12 : ℝ) d ∧
    (gaussianMeasure p q σ).real
        ((normalizedRhoGammaOpNormEvent
          (p := p) (q := q) (σ := σ) P.gammaThreshold d)ᶜ) ≤
      _root_.AppendixB.goodSetTail (1 / 12 : ℝ) d := by
  let P := concreteProbabilityInputs
    (p := p) (q := q) (σ := σ) hd hs hDim hLarge
  have hExp := I.to_normalized_bounds
  exact ⟨hExp.1, hExp.2, P.sampleTail, P.gammaTail⟩

/-- Compatibility wrapper with explicit scalar hypotheses.

The canonical assembly theorem is
`concrete_appendixB_inputs_with_explicit_remaining_gap`; this wrapper simply
repackages the six remaining expectation hypotheses in scalar form. -/
theorem normalized_operator_norm_inputs_from_bridges
    {gaussianMean radialMean sphericalMean
      wishartGammaMean radialSecondMean sphericalGammaMean C1 C2 d : ℝ}
    (hRadialMean : 0 < radialMean)
    (hSampleFactor : gaussianMean = radialMean * sphericalMean)
    (hSampleBound : gaussianMean ≤ radialMean * (C1 / d))
    (hRadialSecondMean : 0 < radialSecondMean)
    (hGammaFactor : wishartGammaMean = radialSecondMean * sphericalGammaMean)
    (hGammaBound : wishartGammaMean ≤ radialSecondMean * (C2 / d ^ 2))
    (hd : 0 < d)
    (hs : 1 ≤ sampleDimension σ)
    (hDim : bipartiteDimension p q = d ^ 2)
    (hLarge : 12 * Real.log 2 ≤ d ^ 2) :
    sphericalMean ≤ C1 / d ∧
    sphericalGammaMean ≤ C2 / d ^ 2 ∧
    (gaussianMeasure p q σ).real
        ((normalizedSampleOpNormEvent
          (p := p) (q := q) (σ := σ)
          (concreteSampleOpNormThreshold (p := p) (q := q) (σ := σ)) d)ᶜ) ≤
      Real.exp (-((1 / 12 : ℝ) * d ^ 2)) ∧
    (gaussianMeasure p q σ).real
        ((normalizedRhoGammaOpNormEvent
          (p := p) (q := q) (σ := σ)
          (concreteRhoGammaOpNormThreshold (p := p) (q := q) (σ := σ)) d)ᶜ) ≤
      Real.exp (-((1 / 12 : ℝ) * d ^ 2)) := by
  let I : RemainingExpectationInputs (d := d) :=
    remainingExpectationInputsFromScalars
      (gaussianMean := gaussianMean)
      (radialMean := radialMean)
      (sphericalMean := sphericalMean)
      (wishartGammaMean := wishartGammaMean)
      (radialSecondMean := radialSecondMean)
      (sphericalGammaMean := sphericalGammaMean)
      (sampleConstant := C1)
      (gammaConstant := C2)
      hRadialMean
      hSampleFactor
      hSampleBound
      hRadialSecondMean
      hGammaFactor
      hGammaBound
  have hAll :=
    concrete_appendixB_inputs_with_explicit_remaining_gap
      (p := p) (q := q) (σ := σ) hd hs hDim hLarge I
  simpa [I, concreteProbabilityInputs, _root_.AppendixB.goodSetTail] using hAll

end AppendixB
end PptFactorization
