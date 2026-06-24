import PptFactorization.AppendixBConcreteBridge
import PptFactorization.AppendixBSphericalLevy

/-!
# Appendix B conditional assembly

This downstream file assembles the Appendix B-facing conclusions without
carrying theorem-core assumptions inside input structures.  The remaining
analytic assumptions are stated directly in the theorem interface, while the
constants used in the final paper-style tail are explicit.

The word "assembly" is important: this file does not prove the global Levy
inequality, local Lipschitz estimate, good-set/bad-set mass estimate,
median/range/integrability hypotheses, radial/spherical expectation inputs, or
localized tail-smallness estimate from first principles.  When these appear as
hypotheses below, they are still theorem-level obligations for the concrete
spherical model.
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

/-- Appendix B assembly with no structure-valued theorem-core inputs.

The theorem simultaneously exposes the normalized operator-norm expectation
inputs, the already-proved Gaussian/Wishart probability inputs, and the final
localized spherical concentration estimate.  The constants in the final tail
are fixed explicitly as

* good-set exponent constant `1 / 12`,
* front constant `4`,
* localized exponent constant `cDim / (64 * C ^ 2)`.

The hypotheses that are still analytic are deliberately direct hypotheses:

* radial/spherical expectation factorizations and expectation bounds;
* median, range, and integrability data for the observable;
* local Lipschitz control on the good set;
* localized tail-smallness;
* the global spherical Levy inequality for the exact concrete spherical law;
* the bad-set mass estimate for the good set.

Thus this theorem is a checked reduction/assembly endpoint, not a closed proof
that all Appendix B analytic estimates hold for the concrete model. -/
theorem final_appendixB_assembly_no_structure_inputs
    {f : SampleMatrix p q σ → ℝ}
    {gaussianMean radialMean sphericalMean
      wishartGammaMean radialSecondMean sphericalGammaMean C1 C2 : ℝ}
    {mean median range bad a b C cDim d eps momentParameter : ℝ}
    {r : ℕ}
    (hRadialMean : 0 < radialMean)
    (hSampleFactor : gaussianMean = radialMean * sphericalMean)
    (hSampleBound : gaussianMean ≤ radialMean * (C1 / d))
    (hRadialSecondMean : 0 < radialSecondMean)
    (hGammaFactor : wishartGammaMean = radialSecondMean * sphericalGammaMean)
    (hGammaBound : wishartGammaMean ≤ radialSecondMean * (C2 / d ^ 2))
    (hd : 0 < d)
    (hs : 1 ≤ sampleDimension σ)
    (hDim : bipartiteDimension p q = d ^ 2)
    (hLarge : 12 * Real.log 2 ≤ d ^ 2)
    (hC : C ≠ 0)
    (hmoment : momentParameter ≠ 0)
    (hScalePos : 0 < _root_.AppendixB.naturalDeviationScale d eps r)
    (hmean :
      mean =
        ∫ X : SampleMatrix p q σ, f X
          ∂sphericalModelMeasure (p := p) (q := q) (σ := σ))
    (hf :
      Integrable f
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)))
    (hRange :
      (fun X : SampleMatrix p q σ => |f X - median|) ≤ᵐ[
        sphericalModelMeasure (p := p) (q := q) (σ := σ)] fun _ => range)
    (hRangeNonneg : 0 ≤ range)
    (hL :
      0 < _root_.AppendixB.localLipschitzScale C momentParameter d r)
    (hn : 0 < cDim * d ^ 4)
    (hSmall :
      _root_.AppendixB.localizedTailIntegralBound
          range bad
          (_root_.AppendixB.localLipschitzScale C momentParameter d r)
          (cDim * d ^ 4) ≤
        _root_.AppendixB.naturalDeviationScale d eps r / 2)
    (hLip :
      _root_.AppendixB.LipschitzOn
        (fun X Y : SampleMatrix p q σ => dist X Y)
        (sphericalOperatorNormGoodSet (p := p) (q := q) (σ := σ) a b d)
        f (_root_.AppendixB.localLipschitzScale C momentParameter d r))
    (hMedian :
      _root_.AppendixB.IsMedian
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)) f median)
    (hGlobalLevy :
      ∀ {g : SampleMatrix p q σ → ℝ} {K : ℝ≥0},
        LipschitzWith K g →
        ∀ {u : ℝ}, 0 < u →
          ∃ Mg,
            _root_.AppendixB.IsMedian
              (sphericalModelMeasure (p := p) (q := q) (σ := σ)) g Mg ∧
              (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
                  {X | u ≤ |g X - Mg|} ≤
                2 * Real.exp (-((cDim * d ^ 4) * u ^ 2 / (4 * K ^ 2))))
    (hBad :
      (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
          (sphericalOperatorNormGoodSet
            (p := p) (q := q) (σ := σ) a b d)ᶜ ≤ bad)
    (hGood : bad ≤ 2 * _root_.AppendixB.goodSetTail (1 / 12 : ℝ) d) :
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
      Real.exp (-((1 / 12 : ℝ) * d ^ 2)) ∧
    (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
        {X | _root_.AppendixB.naturalDeviationScale d eps r ≤ |f X - mean|} ≤
      _root_.AppendixB.paperTailBound
        4 (1 / 12 : ℝ) (cDim / (64 * C ^ 2)) d eps momentParameter := by
  have hNormalized :=
    normalized_operator_norm_inputs_from_bridges
      (p := p) (q := q) (σ := σ)
      (gaussianMean := gaussianMean)
      (radialMean := radialMean)
      (sphericalMean := sphericalMean)
      (wishartGammaMean := wishartGammaMean)
      (radialSecondMean := radialSecondMean)
      (sphericalGammaMean := sphericalGammaMean)
      (C1 := C1) (C2 := C2) (d := d)
      hRadialMean hSampleFactor hSampleBound
      hRadialSecondMean hGammaFactor hGammaBound
      hd hs hDim hLarge
  have hConcentration :=
    spherical_paper_concentration_from_localized_levy_exact_good_set
      (p := p) (q := q) (σ := σ) (f := f)
      (mean := mean) (median := median) (range := range)
      (bad := bad) (a := a) (b := b) (C := C)
      (cDim := cDim) (cSphere := (1 / 12 : ℝ))
      (cLocal := cDim / (64 * C ^ 2)) (d := d)
      (eps := eps) (momentParameter := momentParameter)
      (K := (4 : ℝ)) (r := r)
      (ne_of_gt hd) hC hmoment le_rfl hScalePos
      hmean hf hRange hRangeNonneg hL hn hSmall hLip hMedian
      hGlobalLevy hBad hGood (by norm_num)
  exact ⟨hNormalized.1, hNormalized.2.1, hNormalized.2.2.1,
    hNormalized.2.2.2, hConcentration⟩

end AppendixB
end PptFactorization
