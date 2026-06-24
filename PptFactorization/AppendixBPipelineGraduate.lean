import PptFactorization.AppendixBPipeline
import PptFactorization.AppendixBAubrunGraduate
import PptFactorization.AppendixBGaussianIntegrability
import PptFactorization.AppendixBLevyPolarBridge
import PptFactorization.AppendixBDiagonalGamma

/-!
# Appendix B: graduate-counting bridge into the pipeline

This file connects the checked graduate Aubrun relation-counting interface to
the already-formalized expectation and spherical-normalization pipeline.

It does not assert the graduate relation-counting theorem, the Gaussian
integrability inputs, or the scalar envelope comparison unconditionally.
Instead, it removes the intermediate
`AubrunOffDiagonalExpectationDerivation` package when those inputs are supplied.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal

noncomputable section

namespace PptFactorization
namespace AppendixB

open RandomMatrixModel GaussianModel HighProbabilityBounds
open TraceWickExpansion
open TraceWickExpansion.AubrunSurvivingCounting

/-- Direct graduate-counting entry point into the Appendix B expectation
pipeline.

The abstract off-diagonal expectation derivation is supplied internally from
the graduate relation count, the chosen even moment, and the scalar envelope
comparison.  The remaining hypotheses are exactly the concrete relation count,
the finite Gaussian integrability inputs, the diagonal expectation estimate,
and the radial/spherical normalization inputs already consumed by the pipeline.
-/
theorem gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting
    {dNat sNat : ℕ} {Q : ℕ → ℝ} {d s CDiag COff : ℝ}
    (hsPos : 0 < (sNat : ℝ))
    (hdQ :
      0 ≤ (dNat : ℝ) + Q (aubrunEvenMomentParameter dNat))
    (hsQ :
      0 ≤ Real.sqrt (sNat : ℝ) + Q (aubrunEvenMomentParameter dNat))
    (hMemLp :
      MemLp
        (fun ω : Ω (Fin dNat) (Fin dNat) (Fin sNat) =>
          opNorm
            (wishartGammaOffDiagonal
              (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat)
              (gaussianMatrix (Fin dNat) (Fin dNat) (Fin sNat) ω)))
        (aubrunEvenMomentParameter dNat : ℝ≥0∞)
        (gaussianMeasure (Fin dNat) (Fin dNat) (Fin sNat)))
    (hTraceComplexIntegrable :
      Integrable
        (fun ω : Ω (Fin dNat) (Fin dNat) (Fin sNat) =>
          ((wishartGammaOffDiagonal
              (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat)
              (gaussianMatrix (Fin dNat) (Fin dNat) (Fin sNat) ω)) ^
            aubrunEvenMomentParameter dNat).trace)
        (gaussianMeasure (Fin dNat) (Fin dNat) (Fin sNat)))
    (hRel :
      AubrunGraduateRelationCounting
        Q (dNat : ℝ) (sNat : ℝ)
          (aubrunEvenMomentParameter dNat - 1))
    (hEnvelope :
      aubrunOffDiagonalExpectationEnvelope Q d s
          (aubrunEvenMomentParameter dNat) ≤ COff)
    (hEnvelopeModel :
      aubrunOffDiagonalExpectationEnvelope Q (dNat : ℝ) (sNat : ℝ)
          (aubrunEvenMomentParameter dNat) ≤
        aubrunOffDiagonalExpectationEnvelope Q d s
          (aubrunEvenMomentParameter dNat))
    (hFull :
      Integrable
        (fun ω : Ω (Fin dNat) (Fin dNat) (Fin sNat) =>
          opNorm
            (wishartGamma
              (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat)
              (gaussianMatrix (Fin dNat) (Fin dNat) (Fin sNat) ω)))
        (gaussianMeasure (Fin dNat) (Fin dNat) (Fin sNat)))
    (hDiagInt :
      Integrable
        (fun ω : Ω (Fin dNat) (Fin dNat) (Fin sNat) =>
          opNorm
            (diagonalPart
              (wishartGamma
                (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat)
                (gaussianMatrix (Fin dNat) (Fin dNat) (Fin sNat) ω))))
        (gaussianMeasure (Fin dNat) (Fin dNat) (Fin sNat)))
    (hOffInt :
      Integrable
        (fun ω : Ω (Fin dNat) (Fin dNat) (Fin sNat) =>
          opNorm
            (wishartGammaOffDiagonal
              (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat)
              (gaussianMatrix (Fin dNat) (Fin dNat) (Fin sNat) ω)))
        (gaussianMeasure (Fin dNat) (Fin dNat) (Fin sNat)))
    (hDiag :
      gaussianWishartGammaDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤ CDiag)
    (hIndepR2 :
      gaussianRadiusSq (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ⟂ᵢ[
        gaussianMeasure (Fin dNat) (Fin dNat) (Fin sNat)]
        gaussianDirection (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat))
    (hQuadraticRadialPos :
      0 < gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat))
    (hd : 0 < d)
    (hs : 1 ≤ sampleDimension (Fin sNat))
    (hDim : bipartiteDimension (Fin dNat) (Fin dNat) = d ^ 2) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤ COff ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        CDiag + COff ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        ((CDiag + COff) / d ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      (CDiag + COff) / d ^ 2 := by
  let H :
      AubrunOffDiagonalExpectationDerivation
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat)
        Q dNat d s COff :=
    AubrunOffDiagonalExpectationDerivation_concrete_of_graduate_relation_counting
      (dNat := dNat) (sNat := sNat) (Q := Q)
      (d := d) (s := s) (C_lam := COff)
      hsPos hdQ hsQ hMemLp hTraceComplexIntegrable hRel
      hEnvelope hEnvelopeModel
  exact
    gammaExpectation_pipeline_to_spherical_bound
      (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat)
      (Q := Q) (dNat := dNat) (d := d) (s := s)
      (CDiag := CDiag) (COff := COff)
      H hFull hDiagInt hOffInt hDiag hIndepR2 hQuadraticRadialPos hd hs hDim

/-- Direct graduate-counting entry point with the downstream L¹ Gaussian
operator-norm integrability inputs discharged by the closed integrability
file.  The remaining moment-side `MemLp` and trace-integrability assumptions
are still explicit because they are part of the Aubrun high-moment extraction,
not the elementary diagonal/off-diagonal expectation split. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_with_integrability_closed
    {dNat sNat : ℕ} {Q : ℕ → ℝ} {d s CDiag COff : ℝ}
    (hsPos : 0 < (sNat : ℝ))
    (hdQ :
      0 ≤ (dNat : ℝ) + Q (aubrunEvenMomentParameter dNat))
    (hsQ :
      0 ≤ Real.sqrt (sNat : ℝ) + Q (aubrunEvenMomentParameter dNat))
    (hMemLp :
      MemLp
        (fun ω : Ω (Fin dNat) (Fin dNat) (Fin sNat) =>
          opNorm
            (wishartGammaOffDiagonal
              (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat)
              (gaussianMatrix (Fin dNat) (Fin dNat) (Fin sNat) ω)))
        (aubrunEvenMomentParameter dNat : ℝ≥0∞)
        (gaussianMeasure (Fin dNat) (Fin dNat) (Fin sNat)))
    (hTraceComplexIntegrable :
      Integrable
        (fun ω : Ω (Fin dNat) (Fin dNat) (Fin sNat) =>
          ((wishartGammaOffDiagonal
              (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat)
              (gaussianMatrix (Fin dNat) (Fin dNat) (Fin sNat) ω)) ^
            aubrunEvenMomentParameter dNat).trace)
        (gaussianMeasure (Fin dNat) (Fin dNat) (Fin sNat)))
    (hRel :
      AubrunGraduateRelationCounting
        Q (dNat : ℝ) (sNat : ℝ)
          (aubrunEvenMomentParameter dNat - 1))
    (hEnvelope :
      aubrunOffDiagonalExpectationEnvelope Q d s
          (aubrunEvenMomentParameter dNat) ≤ COff)
    (hEnvelopeModel :
      aubrunOffDiagonalExpectationEnvelope Q (dNat : ℝ) (sNat : ℝ)
          (aubrunEvenMomentParameter dNat) ≤
        aubrunOffDiagonalExpectationEnvelope Q d s
          (aubrunEvenMomentParameter dNat))
    (hDiag :
      gaussianWishartGammaDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤ CDiag)
    (hIndepR2 :
      gaussianRadiusSq (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ⟂ᵢ[
        gaussianMeasure (Fin dNat) (Fin dNat) (Fin sNat)]
        gaussianDirection (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat))
    (hQuadraticRadialPos :
      0 < gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat))
    (hd : 0 < d)
    (hs : 1 ≤ sampleDimension (Fin sNat))
    (hDim : bipartiteDimension (Fin dNat) (Fin dNat) = d ^ 2) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤ COff ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        CDiag + COff ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        ((CDiag + COff) / d ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      (CDiag + COff) / d ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting
      (dNat := dNat) (sNat := sNat) (Q := Q)
      (d := d) (s := s) (CDiag := CDiag) (COff := COff)
      hsPos hdQ hsQ hMemLp hTraceComplexIntegrable hRel hEnvelope
      hEnvelopeModel
      (gaussianWishartGammaOpNorm_integrable
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat))
      (gaussianWishartGammaDiagonalOpNorm_integrable
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat))
      (gaussianWishartGammaOffDiagonalOpNorm_integrable
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat))
      hDiag hIndepR2 hQuadraticRadialPos hd hs hDim

/-- Direct graduate-counting entry point with both the downstream L¹
integrability inputs and the off-diagonal high-moment `MemLp` input discharged
from Gaussian domination.  The complex trace-integrability hypothesis remains
explicit: it is the remaining analytic input needed to turn the relation count
into a real trace-moment bound. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_with_memLp_closed
    {dNat sNat : ℕ} {Q : ℕ → ℝ} {d s CDiag COff : ℝ}
    (hsPos : 0 < (sNat : ℝ))
    (hdQ :
      0 ≤ (dNat : ℝ) + Q (aubrunEvenMomentParameter dNat))
    (hsQ :
      0 ≤ Real.sqrt (sNat : ℝ) + Q (aubrunEvenMomentParameter dNat))
    (hTraceComplexIntegrable :
      Integrable
        (fun ω : Ω (Fin dNat) (Fin dNat) (Fin sNat) =>
          ((wishartGammaOffDiagonal
              (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat)
              (gaussianMatrix (Fin dNat) (Fin dNat) (Fin sNat) ω)) ^
            aubrunEvenMomentParameter dNat).trace)
        (gaussianMeasure (Fin dNat) (Fin dNat) (Fin sNat)))
    (hRel :
      AubrunGraduateRelationCounting
        Q (dNat : ℝ) (sNat : ℝ)
          (aubrunEvenMomentParameter dNat - 1))
    (hEnvelope :
      aubrunOffDiagonalExpectationEnvelope Q d s
          (aubrunEvenMomentParameter dNat) ≤ COff)
    (hEnvelopeModel :
      aubrunOffDiagonalExpectationEnvelope Q (dNat : ℝ) (sNat : ℝ)
          (aubrunEvenMomentParameter dNat) ≤
        aubrunOffDiagonalExpectationEnvelope Q d s
          (aubrunEvenMomentParameter dNat))
    (hDiag :
      gaussianWishartGammaDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤ CDiag)
    (hIndepR2 :
      gaussianRadiusSq (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ⟂ᵢ[
        gaussianMeasure (Fin dNat) (Fin dNat) (Fin sNat)]
        gaussianDirection (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat))
    (hQuadraticRadialPos :
      0 < gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat))
    (hd : 0 < d)
    (hs : 1 ≤ sampleDimension (Fin sNat))
    (hDim : bipartiteDimension (Fin dNat) (Fin dNat) = d ^ 2) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤ COff ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        CDiag + COff ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        ((CDiag + COff) / d ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      (CDiag + COff) / d ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_with_integrability_closed
      (dNat := dNat) (sNat := sNat) (Q := Q)
      (d := d) (s := s) (CDiag := CDiag) (COff := COff)
      hsPos hdQ hsQ
      (gaussianWishartGammaOffDiagonalOpNorm_memLp_nat
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat)
        (n := aubrunEvenMomentParameter dNat)
        (Nat.ne_of_gt (aubrunEvenMomentParameter_pos dNat)))
      hTraceComplexIntegrable hRel hEnvelope hEnvelopeModel
      hDiag hIndepR2 hQuadraticRadialPos hd hs hDim

/-- Direct graduate-counting entry point with the finite Gaussian
integrability inputs discharged, including the off-diagonal trace-power
integrability used by the Aubrun moment extraction.  The remaining hypotheses
are now the real theorem-strength and scalar-normalization inputs: graduate
relation counting, scalar envelope/model comparison, diagonal expectation, and
radial/spherical normalization. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_with_trace_integrability_closed
    {dNat sNat : ℕ} {Q : ℕ → ℝ} {d s CDiag COff : ℝ}
    (hsPos : 0 < (sNat : ℝ))
    (hdQ :
      0 ≤ (dNat : ℝ) + Q (aubrunEvenMomentParameter dNat))
    (hsQ :
      0 ≤ Real.sqrt (sNat : ℝ) + Q (aubrunEvenMomentParameter dNat))
    (hRel :
      AubrunGraduateRelationCounting
        Q (dNat : ℝ) (sNat : ℝ)
          (aubrunEvenMomentParameter dNat - 1))
    (hEnvelope :
      aubrunOffDiagonalExpectationEnvelope Q d s
          (aubrunEvenMomentParameter dNat) ≤ COff)
    (hEnvelopeModel :
      aubrunOffDiagonalExpectationEnvelope Q (dNat : ℝ) (sNat : ℝ)
          (aubrunEvenMomentParameter dNat) ≤
        aubrunOffDiagonalExpectationEnvelope Q d s
          (aubrunEvenMomentParameter dNat))
    (hDiag :
      gaussianWishartGammaDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤ CDiag)
    (hIndepR2 :
      gaussianRadiusSq (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ⟂ᵢ[
        gaussianMeasure (Fin dNat) (Fin dNat) (Fin sNat)]
        gaussianDirection (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat))
    (hQuadraticRadialPos :
      0 < gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat))
    (hd : 0 < d)
    (hs : 1 ≤ sampleDimension (Fin sNat))
    (hDim : bipartiteDimension (Fin dNat) (Fin dNat) = d ^ 2) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤ COff ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        CDiag + COff ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        ((CDiag + COff) / d ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      (CDiag + COff) / d ^ 2 := by
  let k := aubrunEvenMomentParameter dNat
  have hkpos : 0 < k := aubrunEvenMomentParameter_pos dNat
  have hkSub : k - 1 + 1 = k := Nat.sub_add_cancel hkpos
  have hTraceComplexIntegrable :
      Integrable
        (fun ω : Ω (Fin dNat) (Fin dNat) (Fin sNat) =>
          ((wishartGammaOffDiagonal
              (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat)
              (gaussianMatrix (Fin dNat) (Fin dNat) (Fin sNat) ω)) ^
            aubrunEvenMomentParameter dNat).trace)
        (gaussianMeasure (Fin dNat) (Fin dNat) (Fin sNat)) := by
    simpa [k, gaussianMeasure_eq, gaussianMatrix_apply, hkSub] using
      TraceWickExpansion.trace_pow_succ_wishartGammaOffDiagonal_integrable
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) (k - 1)
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_with_memLp_closed
      (dNat := dNat) (sNat := sNat) (Q := Q)
      (d := d) (s := s) (CDiag := CDiag) (COff := COff)
      hsPos hdQ hsQ hTraceComplexIntegrable hRel hEnvelope hEnvelopeModel
      hDiag hIndepR2 hQuadraticRadialPos hd hs hDim

/-- Canonical-scale graduate-counting bridge for the concrete `Fin d, Fin d,
Fin s` model.  This specializes the scale parameters to `dNat` and `sNat`,
so the model-comparison inequality, dimension identity, and sample-size side
condition are supplied internally. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical
    {dNat sNat : ℕ} {Q : ℕ → ℝ} {CDiag COff : ℝ}
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hdQ :
      0 ≤ (dNat : ℝ) + Q (aubrunEvenMomentParameter dNat))
    (hsQ :
      0 ≤ Real.sqrt (sNat : ℝ) + Q (aubrunEvenMomentParameter dNat))
    (hRel :
      AubrunGraduateRelationCounting
        Q (dNat : ℝ) (sNat : ℝ)
          (aubrunEvenMomentParameter dNat - 1))
    (hEnvelope :
      aubrunOffDiagonalExpectationEnvelope Q (dNat : ℝ) (sNat : ℝ)
          (aubrunEvenMomentParameter dNat) ≤ COff)
    (hDiag :
      gaussianWishartGammaDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤ CDiag)
    (hIndepR2 :
      gaussianRadiusSq (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ⟂ᵢ[
        gaussianMeasure (Fin dNat) (Fin dNat) (Fin sNat)]
        gaussianDirection (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat))
    (hQuadraticRadialPos :
      0 < gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat)) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤ COff ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        CDiag + COff ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        ((CDiag + COff) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      (CDiag + COff) / (dNat : ℝ) ^ 2 := by
  have hsSample : 1 ≤ sampleDimension (Fin sNat) := by
    rw [show sampleDimension (Fin sNat) = (sNat : ℝ) by simp [sampleDimension]]
    exact_mod_cast (Nat.succ_le_of_lt (Nat.cast_pos.mp hsPos))
  have hDim :
      bipartiteDimension (Fin dNat) (Fin dNat) = (dNat : ℝ) ^ 2 := by
    simp [bipartiteDimension, BipIndex]
    ring
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_with_trace_integrability_closed
      (dNat := dNat) (sNat := sNat) (Q := Q)
      (d := (dNat : ℝ)) (s := (sNat : ℝ))
      (CDiag := CDiag) (COff := COff)
      hsPos hdQ hsQ hRel hEnvelope (le_refl _)
      hDiag hIndepR2 hQuadraticRadialPos hdPos hsSample hDim

/-- Canonical-scale graduate-counting bridge with the polar/radial
normalization inputs discharged from the no-input Gaussian polar bridge.

The remaining inputs are the scalar positivity side conditions, graduate
relation counting, the scalar envelope bound, and the diagonal expectation
bound.  In particular, this wrapper no longer exposes radius-direction
independence or positivity of the squared radial mean. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_polar_closed
    {dNat sNat : ℕ} {Q : ℕ → ℝ} {CDiag COff : ℝ}
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hdQ :
      0 ≤ (dNat : ℝ) + Q (aubrunEvenMomentParameter dNat))
    (hsQ :
      0 ≤ Real.sqrt (sNat : ℝ) + Q (aubrunEvenMomentParameter dNat))
    (hRel :
      AubrunGraduateRelationCounting
        Q (dNat : ℝ) (sNat : ℝ)
          (aubrunEvenMomentParameter dNat - 1))
    (hEnvelope :
      aubrunOffDiagonalExpectationEnvelope Q (dNat : ℝ) (sNat : ℝ)
          (aubrunEvenMomentParameter dNat) ≤ COff)
    (hDiag :
      gaussianWishartGammaDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤ CDiag) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤ COff ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        CDiag + COff ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        ((CDiag + COff) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      (CDiag + COff) / (dNat : ℝ) ^ 2 := by
  have hdNat : 0 < dNat := Nat.cast_pos.mp hdPos
  have hsNat : 0 < sNat := Nat.cast_pos.mp hsPos
  letI : Nonempty (Fin dNat) := Fin.pos_iff_nonempty.mp hdNat
  letI : Nonempty (Fin sNat) := Fin.pos_iff_nonempty.mp hsNat
  have hIndepR2 :
      gaussianRadiusSq (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ⟂ᵢ[
        gaussianMeasure (Fin dNat) (Fin dNat) (Fin sNat)]
        gaussianDirection (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) :=
    gaussianRadiusSq_indep_gaussianDirection
      (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat)
  have hQuadraticRadialPos :
      0 < gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) := by
    have hsSample : 0 < sampleDimension (Fin sNat) := by
      rw [show sampleDimension (Fin sNat) = (sNat : ℝ) by simp [sampleDimension]]
      exact hsPos
    have hBip : 0 < bipartiteDimension (Fin dNat) (Fin dNat) := by
      rw [show bipartiteDimension (Fin dNat) (Fin dNat) =
          (dNat : ℝ) * (dNat : ℝ) by simp [bipartiteDimension, BipIndex]]
      exact mul_pos hdPos hdPos
    exact gaussianQuadraticRadialMean_pos
      (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) hBip hsSample
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical
      (dNat := dNat) (sNat := sNat) (Q := Q)
      (CDiag := CDiag) (COff := COff)
      hdPos hsPos hdQ hsQ hRel hEnvelope hDiag hIndepR2 hQuadraticRadialPos

/-- Canonical-scale graduate-counting bridge with the diagonal Gamma estimate
also discharged.

The diagonal contribution is bounded by the explicit Appendix B estimate
`2 log 2 + 4 / λ` under the canonical sample-ratio assumption
`λ dNat² ≤ sNat`.  The remaining theorem-strength upper inputs are the
graduate relation count and the scalar off-diagonal envelope bound. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_polar_diagonal_closed
    {dNat sNat : ℕ} {Q : ℕ → ℝ} {lam COff : ℝ}
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatio : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hdQ :
      0 ≤ (dNat : ℝ) + Q (aubrunEvenMomentParameter dNat))
    (hsQ :
      0 ≤ Real.sqrt (sNat : ℝ) + Q (aubrunEvenMomentParameter dNat))
    (hRel :
      AubrunGraduateRelationCounting
        Q (dNat : ℝ) (sNat : ℝ)
          (aubrunEvenMomentParameter dNat - 1))
    (hEnvelope :
      aubrunOffDiagonalExpectationEnvelope Q (dNat : ℝ) (sNat : ℝ)
          (aubrunEvenMomentParameter dNat) ≤ COff) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤ COff ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) + COff ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) + COff) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) + COff) / (dNat : ℝ) ^ 2 := by
  have hRatioModel :
      lam * bipartiteDimension (Fin dNat) (Fin dNat) ≤
        sampleDimension (Fin sNat) := by
    rw [show bipartiteDimension (Fin dNat) (Fin dNat) = (dNat : ℝ) ^ 2 by
      simp [bipartiteDimension, BipIndex]
      ring]
    rw [show sampleDimension (Fin sNat) = (sNat : ℝ) by simp [sampleDimension]]
    exact hRatio
  have hDiag :
      gaussianWishartGammaDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
          2 * Real.log 2 + 4 / lam :=
    gaussianWishartGammaDiagonalOpNormMean_le_C_lambda
      (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) hlam hRatioModel
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_polar_closed
      (dNat := dNat) (sNat := sNat) (Q := Q)
      (CDiag := 2 * Real.log 2 + 4 / lam) (COff := COff)
      hdPos hsPos hdQ hsQ hRel hEnvelope hDiag

/-- Canonical-scale graduate-counting bridge with the off-diagonal constant
chosen to be Aubrun's explicit expectation envelope.

This removes the auxiliary comparison `envelope ≤ COff`.  It does not assert
that the envelope is small; the remaining hard upper input is the graduate
relation-counting estimate that produces this envelope. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_envelope
    {dNat sNat : ℕ} {Q : ℕ → ℝ} {lam : ℝ}
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatio : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hdQ :
      0 ≤ (dNat : ℝ) + Q (aubrunEvenMomentParameter dNat))
    (hsQ :
      0 ≤ Real.sqrt (sNat : ℝ) + Q (aubrunEvenMomentParameter dNat))
    (hRel :
      AubrunGraduateRelationCounting
        Q (dNat : ℝ) (sNat : ℝ)
          (aubrunEvenMomentParameter dNat - 1)) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope Q (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope Q (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope Q (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope Q (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_polar_diagonal_closed
      (dNat := dNat) (sNat := sNat) (Q := Q) (lam := lam)
      (COff :=
        aubrunOffDiagonalExpectationEnvelope Q (dNat : ℝ) (sNat : ℝ)
          (aubrunEvenMomentParameter dNat))
      hdPos hsPos hlam hRatio hdQ hsQ hRel (le_refl _)

/-- Canonical-scale graduate-counting bridge for Aubrun's explicit polynomial
`Q(k) = C₀ k (2k)^36`.

The scalar nonnegativity side conditions needed by real powers are discharged
from `C₀ ≥ 0`.  The only theorem-strength upper input left in this wrapper is
the graduate relation-counting estimate for this explicit polynomial. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
    {dNat sNat : ℕ} {C0 lam : ℝ}
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatio : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hC0 : 0 ≤ C0)
    (hRel :
      AubrunGraduateRelationCounting
        (aubrunProposition71Q C0) (dNat : ℝ) (sNat : ℝ)
          (aubrunEvenMomentParameter dNat - 1)) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q C0) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q C0) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q C0) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q C0) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  let k := aubrunEvenMomentParameter dNat
  have hQnonneg : 0 ≤ aubrunProposition71Q C0 k :=
    aubrunProposition71Q_nonneg (C0 := C0) hC0 k
  have hdQ :
      0 ≤ (dNat : ℝ) + aubrunProposition71Q C0 k := by
    exact add_nonneg hdPos.le hQnonneg
  have hsQ :
      0 ≤ Real.sqrt (sNat : ℝ) + aubrunProposition71Q C0 k := by
    exact add_nonneg (Real.sqrt_nonneg _) hQnonneg
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_envelope
      (dNat := dNat) (sNat := sNat) (Q := aubrunProposition71Q C0)
      (lam := lam) hdPos hsPos hlam hRatio hdQ hsQ hRel

/-- Canonical pipeline entry point for the bidefect route.

This replaces the opaque graduate relation-counting hypothesis by the exact two
inputs exposed by the corrected bidefect strategy: termwise domination by the
separated bidefect monomial, and the resulting bidefect double-sum budget with
the graduate target constant. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_biDefectDoubleSum_canonical_explicitQ
    {dNat sNat : ℕ} {C0 lam : ℝ}
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatio : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hC0 : 0 ≤ C0)
    (hTerm :
      ∀ π : Equiv.Perm (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
        (dNat : ℝ) ^ wickLeftClassCount π *
            (dNat : ℝ) ^ wickRightClassCount π *
              Real.sqrt (sNat : ℝ) ^ (2 * wickColumnClassCount π) ≤
          (dNat : ℝ) ^
              ((aubrunEvenMomentParameter dNat - 1) + 3 -
                wickPlusDefect π) *
            Real.sqrt (sNat : ℝ) ^
              ((aubrunEvenMomentParameter dNat - 1) + 1 -
                wickMinusDefect π))
    (hDouble :
      aubrunBiDefectCountDoubleSum
          (aubrunEvenMomentParameter dNat - 1)
          (dNat : ℝ) (Real.sqrt (sNat : ℝ)) ≤
        (2 : ℝ) ^ ((aubrunEvenMomentParameter dNat - 1) + 1) *
          ((dNat : ℝ) +
            aubrunProposition71Q C0
              ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
            ((aubrunEvenMomentParameter dNat - 1) + 3) *
          (Real.sqrt (sNat : ℝ) +
            aubrunProposition71Q C0
              ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
            ((aubrunEvenMomentParameter dNat - 1) + 1)) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q C0) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q C0) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q C0) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q C0) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := C0) (lam := lam)
      hdPos hsPos hlam hRatio hC0
      (aubrunGraduateRelationCounting_of_biDefectDoubleSumBound_and_term_le
        (Q := aubrunProposition71Q C0)
        (d := (dNat : ℝ)) (s := (sNat : ℝ))
        (m := aubrunEvenMomentParameter dNat - 1)
        hTerm hDouble)

/-- Canonical explicit-`Q` upper bridge with the hard input exposed as the
finite profile-count sum.

This is the smaller combinatorial frontier below
`AubrunGraduateRelationCounting`: once the displayed profile-count estimate is
proved, the existing graduate-counting bridge supplies the relation-counting
interface consumed by the expectation pipeline. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_profile_count_sum_canonical_explicitQ
    {dNat sNat : ℕ} {C0 lam : ℝ}
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatio : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hC0 : 0 ≤ C0)
    (hProfile :
      Finset.sum
          (Finset.range (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 1))
          (fun l1 =>
            Finset.sum
              (Finset.range ((aubrunEvenMomentParameter dNat - 1) + 2))
              (fun l2 =>
                (wickRelationProfileCount
                    (m := aubrunEvenMomentParameter dNat - 1) l1 l2 : ℝ) *
                  (dNat : ℝ) ^ l1 * Real.sqrt (sNat : ℝ) ^ (2 * l2))) ≤
        (2 : ℝ) ^ ((aubrunEvenMomentParameter dNat - 1) + 1) *
          ((dNat : ℝ) +
              aubrunProposition71Q C0
                ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
            ((aubrunEvenMomentParameter dNat - 1) + 3) *
            (Real.sqrt (sNat : ℝ) +
                aubrunProposition71Q C0
                  ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              ((aubrunEvenMomentParameter dNat - 1) + 1)) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q C0) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q C0) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q C0) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q C0) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := C0) (lam := lam)
      hdPos hsPos hlam hRatio hC0
      (aubrunGraduateRelationCounting_of_profileCountSumBound
        (Q := aubrunProposition71Q C0) (d := (dNat : ℝ))
        (s := (sNat : ℝ)) (m := aubrunEvenMomentParameter dNat - 1)
        hProfile)

/-- Canonical explicit-`Q` upper bridge with the hard input exposed as a
defect-sliced Wick sum.

This is the sharper form of the Aubrun combinatorial frontier: the remaining
input is now grouped by the defect parameter used by the fixed-defect counting
theorem. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_defect_sum_canonical_Qone
    {dNat sNat : ℕ} {lam : ℝ}
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatio : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hDefect :
      Finset.sum
          (Finset.range (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 3))
          (fun Δ =>
            Finset.sum
              (Finset.univ.filter fun π : Equiv.Perm
                (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)) =>
                  AubrunSurvivingCounting.wickDefect π = Δ)
              (fun π =>
                (dNat : ℝ) ^
                    (AubrunSurvivingCounting.wickLeftClassCount π +
                      AubrunSurvivingCounting.wickRightClassCount π) *
                  Real.sqrt (sNat : ℝ) ^
                    (2 * AubrunSurvivingCounting.wickColumnClassCount π))) ≤
        (2 : ℝ) ^ ((aubrunEvenMomentParameter dNat - 1) + 1) *
          ((dNat : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
            ((aubrunEvenMomentParameter dNat - 1) + 3) *
            (Real.sqrt (sNat : ℝ) +
                aubrunProposition71Q 1
                  ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              ((aubrunEvenMomentParameter dNat - 1) + 1)) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatio (by norm_num)
      (aubrunGraduateRelationCounting_of_defectSumBound
        (Q := aubrunProposition71Q 1) (d := (dNat : ℝ))
        (s := (sNat : ℝ)) (m := aubrunEvenMomentParameter dNat - 1)
        hDefect)

/-- Canonical `Q=1` endpoint with the Aubrun combinatorial input split into
the Proposition 7.3 count envelope, a per-defect term envelope, and the final
scalar summation bound. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_count_term_canonical_Qone
    {dNat sNat : ℕ} {lam : ℝ} {B : ℕ → ℝ}
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatio : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hCount : ∀ Δ ∈
      Finset.range (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 3),
        (wickPermutationDefectCount (aubrunEvenMomentParameter dNat - 1) Δ :
          ℝ) ≤
          aubrunFixedDefectCountEnvelope
            (aubrunEvenMomentParameter dNat - 1) Δ)
    (hBnonneg : ∀ Δ ∈
      Finset.range (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 3),
        0 ≤ B Δ)
    (hTerm : ∀ Δ ∈
      Finset.range (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 3),
      ∀ π : Equiv.Perm (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
        TraceWickExpansion.AubrunSurvivingCounting.wickDefect π = Δ →
          (dNat : ℝ) ^
              (TraceWickExpansion.AubrunSurvivingCounting.wickLeftClassCount π +
                TraceWickExpansion.AubrunSurvivingCounting.wickRightClassCount π) *
            Real.sqrt (sNat : ℝ) ^
              (2 * TraceWickExpansion.AubrunSurvivingCounting.wickColumnClassCount π) ≤
            B Δ)
    (hEnvelope :
      Finset.sum
          (Finset.range (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 3))
          (fun Δ =>
            aubrunFixedDefectCountEnvelope
              (aubrunEvenMomentParameter dNat - 1) Δ * B Δ) ≤
        (2 : ℝ) ^ ((aubrunEvenMomentParameter dNat - 1) + 1) *
          ((dNat : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
            ((aubrunEvenMomentParameter dNat - 1) + 3) *
            (Real.sqrt (sNat : ℝ) +
                aubrunProposition71Q 1
                  ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              ((aubrunEvenMomentParameter dNat - 1) + 1)) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatio (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73CountAndTermBounds
        (Q := aubrunProposition71Q 1) (d := (dNat : ℝ))
        (s := (sNat : ℝ)) (m := aubrunEvenMomentParameter dNat - 1)
        (B := B) hCount hBnonneg hTerm hEnvelope)

/-- Canonical `Q=1` endpoint using the defect-sensitive common-base term
envelope.

This is the sharp replacement interface for the crude maximum-exponent route.
The remaining theorem-strength inputs are a weighted-rank budget for Wick
permutations, the fixed-defect count bound, and one scalar defect-sum envelope. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_common_base_defect_canonical_Qone
    {dNat sNat : ℕ} {D lam : ℝ}
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatio : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hdD : (dNat : ℝ) ≤ D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (hRank : ∀ π : Equiv.Perm
      (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
        wickWeightedRank π ≤
          2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 2)
    (hCount : ∀ Δ ∈
      Finset.range (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 3),
        (wickPermutationDefectCount (aubrunEvenMomentParameter dNat - 1) Δ :
          ℝ) ≤
          aubrunFixedDefectCountEnvelope
            (aubrunEvenMomentParameter dNat - 1) Δ)
    (hEnvelope :
      Finset.sum
          (Finset.range (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 3))
          (fun Δ =>
            aubrunFixedDefectCountEnvelope
              (aubrunEvenMomentParameter dNat - 1) Δ *
              D ^ (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 2 - Δ)) ≤
        (2 : ℝ) ^ ((aubrunEvenMomentParameter dNat - 1) + 1) *
          ((dNat : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
            ((aubrunEvenMomentParameter dNat - 1) + 3) *
            (Real.sqrt (sNat : ℝ) +
                aubrunProposition71Q 1
                  ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              ((aubrunEvenMomentParameter dNat - 1) + 1)) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatio (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73CountAndCommonBaseDefectEnvelope
        (Q := aubrunProposition71Q 1) (d := (dNat : ℝ))
        (s := (sNat : ℝ)) (D := D)
        (m := aubrunEvenMomentParameter dNat - 1)
        hdPos.le (Real.sqrt_nonneg _) hdD hsqrtD hRank hCount hEnvelope)

/-- Canonical `Q=1` endpoint with the rank budget exposed as the two standard
cycle-count inequalities for the long cycle and its inverse. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_cycle_pair_canonical_Qone
    {dNat sNat : ℕ} {D lam : ℝ}
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatio : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hdD : (dNat : ℝ) ≤ D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (hCycleLeft : ∀ π : Equiv.Perm
      (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
        permCycleClassCount π +
          permCycleClassCount
            (finRotate ((aubrunEvenMomentParameter dNat - 1) + 1) * π) ≤
          ((aubrunEvenMomentParameter dNat - 1) + 1) + 1)
    (hCycleRight : ∀ π : Equiv.Perm
      (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
        permCycleClassCount π +
          permCycleClassCount
            (π * (finRotate ((aubrunEvenMomentParameter dNat - 1) + 1)).symm) ≤
          ((aubrunEvenMomentParameter dNat - 1) + 1) + 1)
    (hCount : ∀ Δ ∈
      Finset.range (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 3),
        (wickPermutationDefectCount (aubrunEvenMomentParameter dNat - 1) Δ :
          ℝ) ≤
          aubrunFixedDefectCountEnvelope
            (aubrunEvenMomentParameter dNat - 1) Δ)
    (hEnvelope :
      Finset.sum
          (Finset.range (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 3))
          (fun Δ =>
            aubrunFixedDefectCountEnvelope
              (aubrunEvenMomentParameter dNat - 1) Δ *
              D ^ (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 2 - Δ)) ≤
        (2 : ℝ) ^ ((aubrunEvenMomentParameter dNat - 1) + 1) *
          ((dNat : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
            ((aubrunEvenMomentParameter dNat - 1) + 3) *
            (Real.sqrt (sNat : ℝ) +
                aubrunProposition71Q 1
                  ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              ((aubrunEvenMomentParameter dNat - 1) + 1)) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatio (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73CountAndCyclePairBounds
        (Q := aubrunProposition71Q 1) (d := (dNat : ℝ))
        (s := (sNat : ℝ)) (D := D)
        (m := aubrunEvenMomentParameter dNat - 1)
        hdPos.le (Real.sqrt_nonneg _) hdD hsqrtD
        hCycleLeft hCycleRight hCount hEnvelope)

/-- Canonical `Q=1` endpoint after closing the Aubrun weighted-rank budget by
the Cayley cycle-count inequalities.  The remaining Aubrun inputs are the
fixed-defect count envelope and the scalar defect-sum envelope. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_cayley_rank_canonical_Qone
    {dNat sNat : ℕ} {D lam : ℝ}
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatio : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hdD : (dNat : ℝ) ≤ D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (hCount : ∀ Δ ∈
      Finset.range (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 3),
        (wickPermutationDefectCount (aubrunEvenMomentParameter dNat - 1) Δ :
          ℝ) ≤
          aubrunFixedDefectCountEnvelope
            (aubrunEvenMomentParameter dNat - 1) Δ)
    (hEnvelope :
      Finset.sum
          (Finset.range (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 3))
          (fun Δ =>
            aubrunFixedDefectCountEnvelope
              (aubrunEvenMomentParameter dNat - 1) Δ *
              D ^ (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 2 - Δ)) ≤
        (2 : ℝ) ^ ((aubrunEvenMomentParameter dNat - 1) + 1) *
          ((dNat : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
            ((aubrunEvenMomentParameter dNat - 1) + 3) *
            (Real.sqrt (sNat : ℝ) +
                aubrunProposition71Q 1
                  ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              ((aubrunEvenMomentParameter dNat - 1) + 1)) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatio (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73CountAndCayleyRankBudget
        (Q := aubrunProposition71Q 1) (d := (dNat : ℝ))
        (s := (sNat : ℝ)) (D := D)
        (m := aubrunEvenMomentParameter dNat - 1)
        (hd0 := hdPos.le) (hsqrt0 := Real.sqrt_nonneg _)
        (hdD := hdD) (hsqrtD := hsqrtD)
        (hCount := hCount) (hEnvelope := hEnvelope))

/-- Public compatibility wrapper: the old coarse scalar envelope can be paired
with the sharper support-restricted count hypothesis, since non-supported
defect values have zero count. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_support_count_coarse_cayley_rank_canonical_Qone
    {dNat sNat : ℕ} {D lam : ℝ}
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatio : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hdD : (dNat : ℝ) ≤ D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (hCount : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        (wickPermutationDefectCount (aubrunEvenMomentParameter dNat - 1) Δ :
          ℝ) ≤
          aubrunFixedDefectCountEnvelope
            (aubrunEvenMomentParameter dNat - 1) Δ)
    (hEnvelope :
      Finset.sum
          (Finset.range (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 3))
          (fun Δ =>
            aubrunFixedDefectCountEnvelope
              (aubrunEvenMomentParameter dNat - 1) Δ *
              D ^ (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 2 - Δ)) ≤
        (2 : ℝ) ^ ((aubrunEvenMomentParameter dNat - 1) + 1) *
          ((dNat : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
            ((aubrunEvenMomentParameter dNat - 1) + 3) *
            (Real.sqrt (sNat : ℝ) +
                aubrunProposition71Q 1
                  ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              ((aubrunEvenMomentParameter dNat - 1) + 1)) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_prop73_cayley_rank_canonical_Qone
      (dNat := dNat) (sNat := sNat) (D := D) (lam := lam)
      hdPos hsPos hlam hRatio hdD hsqrtD
      (wickPermutationDefectCount_range_bound_of_support_bound
        (m := aubrunEvenMomentParameter dNat - 1)
        (C := aubrunFixedDefectCountEnvelope
          (aubrunEvenMomentParameter dNat - 1))
        (fun Δ =>
          aubrunFixedDefectCountEnvelope_nonneg
            (aubrunEvenMomentParameter dNat - 1) Δ)
        hCount)
      hEnvelope

/-- Canonical `Q=1` Cayley-rank endpoint with the count and scalar budgets
restricted to actual defect support.

This is the sharp public split for the remaining Aubrun input: prove the
support-restricted fixed-defect count estimate, and prove the displayed
support-restricted scalar defect-sum envelope. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_support_count_cayley_rank_canonical_Qone
    {dNat sNat : ℕ} {D lam : ℝ}
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatio : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hdD : (dNat : ℝ) ≤ D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (hCount : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        (wickPermutationDefectCount (aubrunEvenMomentParameter dNat - 1) Δ :
          ℝ) ≤
          aubrunFixedDefectCountEnvelope
            (aubrunEvenMomentParameter dNat - 1) Δ)
    (hEnvelope :
      Finset.sum (wickDefectSupport (aubrunEvenMomentParameter dNat - 1))
          (fun Δ =>
            aubrunFixedDefectCountEnvelope
              (aubrunEvenMomentParameter dNat - 1) Δ *
              D ^ (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 2 - Δ)) ≤
        (2 : ℝ) ^ ((aubrunEvenMomentParameter dNat - 1) + 1) *
          ((dNat : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
            ((aubrunEvenMomentParameter dNat - 1) + 3) *
            (Real.sqrt (sNat : ℝ) +
                aubrunProposition71Q 1
                  ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              ((aubrunEvenMomentParameter dNat - 1) + 1)) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatio (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73SupportCountAndCommonBaseDefectEnvelope
        (Q := aubrunProposition71Q 1) (d := (dNat : ℝ))
        (s := (sNat : ℝ)) (D := D)
        (m := aubrunEvenMomentParameter dNat - 1)
        (hd0 := hdPos.le) (hsqrt0 := Real.sqrt_nonneg _)
        (hdD := hdD) (hsqrtD := hsqrtD)
        (hRank := fun π => wickWeightedRank_le_two_mul_add_two π)
        (hCount := hCount) (hEnvelope := hEnvelope))

/-- Canonical `Q=1` Cayley-rank endpoint with the fixed-defect count supplied
directly by Aubrun innovation-fiber data.

This removes the separate fixed-defect count hypothesis from the sharp
Cayley-rank public frontier.  The remaining scalar input is the displayed
defect-sum envelope over the common base `D`. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_fiber_data_cayley_rank_canonical_Qone
    {dNat sNat : ℕ} {D lam : ℝ}
    {Fiber LeftCouples RightCouples :
      ℕ → Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)) → Type*}
    [∀ Δ I, Fintype (Fiber Δ I)]
    [∀ Δ I, Fintype (LeftCouples Δ I)]
    [∀ Δ I, Fintype (RightCouples Δ I)]
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatio : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hdD : (dNat : ℝ) ≤ D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (defectEncode : ∀ Δ ∈
      Finset.range (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 3),
        WickPermutationDefectClass (aubrunEvenMomentParameter dNat - 1) Δ ↪
          Sigma (Fiber Δ))
    (encode : ∀ Δ ∈
      Finset.range (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 3),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fiber Δ I ↪ LeftCouples Δ I × RightCouples Δ I)
    (hLeft : ∀ Δ ∈
      Finset.range (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 3),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (LeftCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hRight : ∀ Δ ∈
      Finset.range (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 3),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (RightCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hLarge : ∀ Δ ∈
      Finset.range (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 3),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (Fiber Δ I) ≠ 0 →
            ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
              2 * I.card + 2 * Δ)
    (hEnvelope :
      Finset.sum
          (Finset.range (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 3))
          (fun Δ =>
            aubrunFixedDefectCountEnvelope
              (aubrunEvenMomentParameter dNat - 1) Δ *
              D ^ (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 2 - Δ)) ≤
        (2 : ℝ) ^ ((aubrunEvenMomentParameter dNat - 1) + 1) *
          ((dNat : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
            ((aubrunEvenMomentParameter dNat - 1) + 3) *
            (Real.sqrt (sNat : ℝ) +
                aubrunProposition71Q 1
                  ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              ((aubrunEvenMomentParameter dNat - 1) + 1)) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatio (by norm_num)
        (aubrunGraduateRelationCounting_of_prop73FiberDataAndCayleyRankBudget
          (Q := aubrunProposition71Q 1) (d := (dNat : ℝ))
          (s := (sNat : ℝ)) (D := D)
          (m := aubrunEvenMomentParameter dNat - 1)
          hdPos.le (Real.sqrt_nonneg _) hdD hsqrtD
          defectEncode encode hLeft hRight hLarge hEnvelope)

/-- Canonical `Q=1` Cayley-rank endpoint with Aubrun fiber data and scalar
budget required only on the actual defect support. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_fiber_support_cayley_rank_canonical_Qone
    {dNat sNat : ℕ} {D lam : ℝ}
    {Fiber LeftCouples RightCouples :
      ℕ → Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)) → Type*}
    [∀ Δ I, Fintype (Fiber Δ I)]
    [∀ Δ I, Fintype (LeftCouples Δ I)]
    [∀ Δ I, Fintype (RightCouples Δ I)]
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatio : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hdD : (dNat : ℝ) ≤ D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (defectEncode : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        WickPermutationDefectClass (aubrunEvenMomentParameter dNat - 1) Δ ↪
          Sigma (Fiber Δ))
    (encode : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fiber Δ I ↪ LeftCouples Δ I × RightCouples Δ I)
    (hLeft : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (LeftCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hRight : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (RightCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hLarge : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (Fiber Δ I) ≠ 0 →
            ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
              2 * I.card + 2 * Δ)
    (hEnvelope :
      Finset.sum (wickDefectSupport (aubrunEvenMomentParameter dNat - 1))
          (fun Δ =>
            aubrunFixedDefectCountEnvelope
              (aubrunEvenMomentParameter dNat - 1) Δ *
              D ^ (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 2 - Δ)) ≤
        (2 : ℝ) ^ ((aubrunEvenMomentParameter dNat - 1) + 1) *
          ((dNat : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
            ((aubrunEvenMomentParameter dNat - 1) + 3) *
            (Real.sqrt (sNat : ℝ) +
                aubrunProposition71Q 1
                  ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              ((aubrunEvenMomentParameter dNat - 1) + 1)) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatio (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73FiberDataSupportAndCayleyRankBudget
        (Q := aubrunProposition71Q 1) (d := (dNat : ℝ))
        (s := (sNat : ℝ)) (D := D)
        (m := aubrunEvenMomentParameter dNat - 1)
        hdPos.le (Real.sqrt_nonneg _) hdD hsqrtD
        defectEncode encode hLeft hRight hLarge hEnvelope)

/-- Canonical `Q=1` support/fiber endpoint with the tightened support count
sum already compressed to one crude common-base scalar comparison. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_fiber_support_cayley_rank_tightCountCrudeCommonBase_canonical_Qone
    {dNat sNat : ℕ} {D lam : ℝ}
    {Fiber LeftCouples RightCouples :
      ℕ → Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)) → Type*}
    [∀ Δ I, Fintype (Fiber Δ I)]
    [∀ Δ I, Fintype (LeftCouples Δ I)]
    [∀ Δ I, Fintype (RightCouples Δ I)]
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatio : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hdD : (dNat : ℝ) ≤ D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (hD : 1 ≤ D)
    (defectEncode : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        WickPermutationDefectClass (aubrunEvenMomentParameter dNat - 1) Δ ↪
          Sigma (Fiber Δ))
    (encode : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fiber Δ I ↪ LeftCouples Δ I × RightCouples Δ I)
    (hLeft : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (LeftCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hRight : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (RightCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hLarge : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (Fiber Δ I) ≠ 0 →
            ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
              2 * I.card + 2 * Δ)
    (hEnvelope :
      (((2 : ℝ) * ((aubrunEvenMomentParameter dNat - 1 : ℕ) : ℝ) + 1) *
        ((2 : ℝ) ^ ((aubrunEvenMomentParameter dNat - 1) + 1) *
          aubrunProposition73P
              ((aubrunEvenMomentParameter dNat - 1) + 1) ^
            (2 * (aubrunEvenMomentParameter dNat - 1)))) *
          D ^ (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 2) ≤
        (2 : ℝ) ^ ((aubrunEvenMomentParameter dNat - 1) + 1) *
          ((dNat : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
            ((aubrunEvenMomentParameter dNat - 1) + 3) *
            (Real.sqrt (sNat : ℝ) +
                aubrunProposition71Q 1
                  ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              ((aubrunEvenMomentParameter dNat - 1) + 1)) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatio (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73FiberDataSupportAndCayleyRankBudget_tightCountCrudeCommonBase
        (Q := aubrunProposition71Q 1) (d := (dNat : ℝ))
        (s := (sNat : ℝ)) (D := D)
        (m := aubrunEvenMomentParameter dNat - 1)
        hdPos.le (Real.sqrt_nonneg _) hdD hsqrtD hD
        defectEncode encode hLeft hRight hLarge hEnvelope)

/-- Canonical `Q=1` support/fiber endpoint with the common `2^k` factor
cancelled from the crude common-base scalar comparison. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_fiber_support_cayley_rank_tightCountCrudeCommonBase_cancelTwo_canonical_Qone
    {dNat sNat : ℕ} {D lam : ℝ}
    {Fiber LeftCouples RightCouples :
      ℕ → Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)) → Type*}
    [∀ Δ I, Fintype (Fiber Δ I)]
    [∀ Δ I, Fintype (LeftCouples Δ I)]
    [∀ Δ I, Fintype (RightCouples Δ I)]
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatio : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hdD : (dNat : ℝ) ≤ D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (hD : 1 ≤ D)
    (defectEncode : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        WickPermutationDefectClass (aubrunEvenMomentParameter dNat - 1) Δ ↪
          Sigma (Fiber Δ))
    (encode : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fiber Δ I ↪ LeftCouples Δ I × RightCouples Δ I)
    (hLeft : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (LeftCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hRight : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (RightCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hLarge : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (Fiber Δ I) ≠ 0 →
            ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
              2 * I.card + 2 * Δ)
    (hEnvelope :
      (((2 : ℝ) * ((aubrunEvenMomentParameter dNat - 1 : ℕ) : ℝ) + 1) *
          aubrunProposition73P
              ((aubrunEvenMomentParameter dNat - 1) + 1) ^
            (2 * (aubrunEvenMomentParameter dNat - 1))) *
          D ^ (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 2) ≤
        ((dNat : ℝ) +
            aubrunProposition71Q 1
              ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
          ((aubrunEvenMomentParameter dNat - 1) + 3) *
          (Real.sqrt (sNat : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
            ((aubrunEvenMomentParameter dNat - 1) + 1)) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatio (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73FiberDataSupportAndCayleyRankBudget_tightCountCrudeCommonBase_cancelTwo
        (Q := aubrunProposition71Q 1) (d := (dNat : ℝ))
        (s := (sNat : ℝ)) (D := D)
        (m := aubrunEvenMomentParameter dNat - 1)
        hdPos.le (Real.sqrt_nonneg _) hdD hsqrtD hD
        defectEncode encode hLeft hRight hLarge hEnvelope)

/-- Canonical `Q=1` support/fiber endpoint where the fixed-defect polynomial
loss is absorbed into the common base `D`.  The displayed scalar leaf is now
`(2m+1)D^(2k+2)` against the Aubrun product envelope. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_fiber_support_cayley_rank_absorbPCommonBase_cancelTwo_canonical_Qone
    {dNat sNat : ℕ} {D lam : ℝ}
    {Fiber LeftCouples RightCouples :
      ℕ → Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)) → Type*}
    [∀ Δ I, Fintype (Fiber Δ I)]
    [∀ Δ I, Fintype (LeftCouples Δ I)]
    [∀ Δ I, Fintype (RightCouples Δ I)]
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatio : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hdD : (dNat : ℝ) ≤ D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (hD : 1 ≤ D)
    (hP_D :
      aubrunProposition73P ((aubrunEvenMomentParameter dNat - 1) + 1) ≤ D)
    (defectEncode : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        WickPermutationDefectClass (aubrunEvenMomentParameter dNat - 1) Δ ↪
          Sigma (Fiber Δ))
    (encode : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fiber Δ I ↪ LeftCouples Δ I × RightCouples Δ I)
    (hLeft : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (LeftCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hRight : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (RightCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hLarge : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (Fiber Δ I) ≠ 0 →
            ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
              2 * I.card + 2 * Δ)
    (hEnvelope :
      (((2 : ℝ) * ((aubrunEvenMomentParameter dNat - 1 : ℕ) : ℝ) + 1) *
          D ^ (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 2)) ≤
        ((dNat : ℝ) +
            aubrunProposition71Q 1
              ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
          ((aubrunEvenMomentParameter dNat - 1) + 3) *
          (Real.sqrt (sNat : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
            ((aubrunEvenMomentParameter dNat - 1) + 1)) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatio (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73FiberDataSupportAndCayleyRankBudget_absorbPCommonBase_cancelTwo
        (Q := aubrunProposition71Q 1) (d := (dNat : ℝ))
        (s := (sNat : ℝ)) (D := D)
        (m := aubrunEvenMomentParameter dNat - 1)
        hdPos.le (Real.sqrt_nonneg _) hdD hsqrtD hD hP_D
        defectEncode encode hLeft hRight hLarge hEnvelope)

/-- Canonical `Q=1` support/fiber endpoint with a natural common-base side
condition: `D` bounds `d`, `sqrt s`, and `Q(k)`.  The polynomial bound
`P(k) ≤ D` is discharged internally from `P(k) ≤ Q(k)`. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_fiber_support_cayley_rank_absorbQCommonBase_cancelTwo_canonical_Qone
    {dNat sNat : ℕ} {D lam : ℝ}
    {Fiber LeftCouples RightCouples :
      ℕ → Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)) → Type*}
    [∀ Δ I, Fintype (Fiber Δ I)]
    [∀ Δ I, Fintype (LeftCouples Δ I)]
    [∀ Δ I, Fintype (RightCouples Δ I)]
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatio : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hdD : (dNat : ℝ) ≤ D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (hD : 1 ≤ D)
    (hQ_D :
      aubrunProposition71Q 1 ((aubrunEvenMomentParameter dNat - 1) + 1) ≤ D)
    (defectEncode : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        WickPermutationDefectClass (aubrunEvenMomentParameter dNat - 1) Δ ↪
          Sigma (Fiber Δ))
    (encode : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fiber Δ I ↪ LeftCouples Δ I × RightCouples Δ I)
    (hLeft : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (LeftCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hRight : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (RightCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hLarge : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (Fiber Δ I) ≠ 0 →
            ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
              2 * I.card + 2 * Δ)
    (hEnvelope :
      (((2 : ℝ) * ((aubrunEvenMomentParameter dNat - 1 : ℕ) : ℝ) + 1) *
          D ^ (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 2)) ≤
        ((dNat : ℝ) +
            aubrunProposition71Q 1
              ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
          ((aubrunEvenMomentParameter dNat - 1) + 3) *
          (Real.sqrt (sNat : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
            ((aubrunEvenMomentParameter dNat - 1) + 1)) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatio (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73FiberDataSupportAndCayleyRankBudget_absorbQCommonBase_cancelTwo
        (d := (dNat : ℝ)) (s := (sNat : ℝ)) (D := D)
        (m := aubrunEvenMomentParameter dNat - 1)
        hdPos.le (Real.sqrt_nonneg _) hdD hsqrtD hD hQ_D
        defectEncode encode hLeft hRight hLarge hEnvelope)

/-- Canonical `Q=1` support/fiber endpoint where the absorbed-`Q` scalar leaf
is discharged from two transparent common-base margins:
`D ≤ d+Q(k)` and `(2m+1)D ≤ sqrt(s)+Q(k)`. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_fiber_support_cayley_rank_absorbQCommonBase_cancelTwo_margins_canonical_Qone
    {dNat sNat : ℕ} {D lam : ℝ}
    {Fiber LeftCouples RightCouples :
      ℕ → Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)) → Type*}
    [∀ Δ I, Fintype (Fiber Δ I)]
    [∀ Δ I, Fintype (LeftCouples Δ I)]
    [∀ Δ I, Fintype (RightCouples Δ I)]
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatio : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hdD : (dNat : ℝ) ≤ D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (hD : 1 ≤ D)
    (hQ_D :
      aubrunProposition71Q 1 ((aubrunEvenMomentParameter dNat - 1) + 1) ≤ D)
    (hFirst :
      D ≤ (dNat : ℝ) +
        aubrunProposition71Q 1
          ((aubrunEvenMomentParameter dNat - 1) + 1))
    (hSecond :
      (((2 : ℝ) * ((aubrunEvenMomentParameter dNat - 1 : ℕ) : ℝ) + 1) *
          D) ≤
        Real.sqrt (sNat : ℝ) +
          aubrunProposition71Q 1
            ((aubrunEvenMomentParameter dNat - 1) + 1))
    (defectEncode : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        WickPermutationDefectClass (aubrunEvenMomentParameter dNat - 1) Δ ↪
          Sigma (Fiber Δ))
    (encode : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fiber Δ I ↪ LeftCouples Δ I × RightCouples Δ I)
    (hLeft : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (LeftCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hRight : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (RightCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hLarge : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (Fiber Δ I) ≠ 0 →
            ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
              2 * I.card + 2 * Δ) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatio (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73FiberDataSupportAndCayleyRankBudget_absorbQCommonBase_cancelTwo_of_margins
        (d := (dNat : ℝ)) (s := (sNat : ℝ)) (D := D)
        (m := aubrunEvenMomentParameter dNat - 1)
        hdPos.le (Real.sqrt_nonneg _) hdD hsqrtD hD hQ_D hFirst
        hSecond defectEncode encode hLeft hRight hLarge)

/-- Public-endpoint form of the absorbed-`Q` margin obstruction.

For the concrete logarithmic even moment choice, `m = aubrunEvenMomentParameter d
- 1` is always at least one.  Hence the margin endpoint above has inconsistent
common-base hypotheses as soon as `D > 0`: the assumptions `sqrt(s)≤D`,
`Q(k)≤D`, and `(2m+1)D≤sqrt(s)+Q(k)` cannot hold simultaneously. -/
theorem aubrun_absorbedQ_commonBaseMargins_impossible_for_evenMoment
    {dNat sNat : ℕ} {D : ℝ}
    (hDpos : 0 < D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (hQ_D :
      aubrunProposition71Q 1 ((aubrunEvenMomentParameter dNat - 1) + 1) ≤ D)
    (hSecond :
      (((2 : ℝ) * ((aubrunEvenMomentParameter dNat - 1 : ℕ) : ℝ) + 1) *
          D) ≤
        Real.sqrt (sNat : ℝ) +
          aubrunProposition71Q 1
            ((aubrunEvenMomentParameter dNat - 1) + 1)) :
    False := by
  have hm : 1 ≤ aubrunEvenMomentParameter dNat - 1 := by
    have htwo := two_le_aubrunEvenMomentParameter dNat
    omega
  exact
    aubrun_absorbedQ_commonBaseMargins_impossible_of_one_le_m
      (s := (sNat : ℝ)) (D := D)
      (m := aubrunEvenMomentParameter dNat - 1)
      hm hDpos hsqrtD hQ_D (by simpa [mul_assoc] using hSecond)

/-- Canonical `Q=1` support-count endpoint with the defect-sensitive finite
ratio scalar leaf.  The count theorem is visible as a support-restricted
fixed-defect estimate, separate from the scalar ratio comparison. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_support_count_cayley_rank_ratioCommonBase_cancelTwo_canonical_Qone
    {dNat sNat : ℕ} {D ρ lam : ℝ}
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatioModel : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hdD : (dNat : ℝ) ≤ D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (hρ0 : 0 ≤ ρ)
    (hP_ρD :
      aubrunProposition73P ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
        ρ * D)
    (hCount : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        (wickPermutationDefectCount (aubrunEvenMomentParameter dNat - 1) Δ :
          ℝ) ≤
          aubrunFixedDefectCountEnvelope
            (aubrunEvenMomentParameter dNat - 1) Δ)
    (hEnvelope :
      aubrunDefectRatioSupportSum (aubrunEvenMomentParameter dNat - 1) ρ *
          D ^ (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 2) ≤
        ((dNat : ℝ) +
            aubrunProposition71Q 1
              ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
          ((aubrunEvenMomentParameter dNat - 1) + 3) *
          (Real.sqrt (sNat : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
            ((aubrunEvenMomentParameter dNat - 1) + 1)) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatioModel (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73SupportCountAndCayleyRankBudget_ratioCommonBase_cancelTwo
        (Q := aubrunProposition71Q 1) (d := (dNat : ℝ))
        (s := (sNat : ℝ)) (D := D) (ρ := ρ)
        (m := aubrunEvenMomentParameter dNat - 1)
        hdPos.le (Real.sqrt_nonneg _) hdD hsqrtD (le_trans hdPos.le hdD)
        hρ0 hP_ρD hCount hEnvelope)

/-- Canonical `Q=1` support-count endpoint with the finite ratio sum bounded
by `1 + 2mρ`.

This is the public variable-ratio scalar route: unlike the fixed geometric
constant branch, it can still be useful when the ratio parameter depends on
`d` and tends to zero. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_support_count_cayley_rank_linearRatioCommonBase_cancelTwo_canonical_Qone
    {dNat sNat : ℕ} {D ρ lam : ℝ}
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatioModel : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hdD : (dNat : ℝ) ≤ D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1)
    (hP_ρD :
      aubrunProposition73P ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
        ρ * D)
    (hCount : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        (wickPermutationDefectCount (aubrunEvenMomentParameter dNat - 1) Δ :
          ℝ) ≤
          aubrunFixedDefectCountEnvelope
            (aubrunEvenMomentParameter dNat - 1) Δ)
    (hEnvelope :
      (1 + 2 * ((aubrunEvenMomentParameter dNat - 1 : ℕ) : ℝ) * ρ) *
          D ^ (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 2) ≤
        ((dNat : ℝ) +
            aubrunProposition71Q 1
              ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
          ((aubrunEvenMomentParameter dNat - 1) + 3) *
          (Real.sqrt (sNat : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
            ((aubrunEvenMomentParameter dNat - 1) + 1)) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatioModel (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73SupportCountAndCayleyRankBudget_linearRatioCommonBase_cancelTwo
        (Q := aubrunProposition71Q 1) (d := (dNat : ℝ))
        (s := (sNat : ℝ)) (D := D) (ρ := ρ)
        (m := aubrunEvenMomentParameter dNat - 1)
        hdPos.le (Real.sqrt_nonneg _) hdD hsqrtD (le_trans hdPos.le hdD)
        hρ0 hρ1 hP_ρD hCount hEnvelope)

/-- Canonical `Q=1` support-count endpoint with the variable-ratio scalar
leaf stated as a normalized-product target.

This is the public form of the live scalar branch: after division by the
common-base power, the two shifted analytic bases must pay for `1+2mρ`. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_support_count_cayley_rank_linearRatioNormalizedProduct_cancelTwo_canonical_Qone
    {dNat sNat : ℕ} {D ρ lam : ℝ}
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatioModel : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hdD : (dNat : ℝ) ≤ D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (hDpos : 0 < D)
    (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1)
    (hP_ρD :
      aubrunProposition73P ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
        ρ * D)
    (hCount : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        (wickPermutationDefectCount (aubrunEvenMomentParameter dNat - 1) Δ :
          ℝ) ≤
          aubrunFixedDefectCountEnvelope
            (aubrunEvenMomentParameter dNat - 1) Δ)
    (hNormalized :
      1 + 2 * ((aubrunEvenMomentParameter dNat - 1 : ℕ) : ℝ) * ρ ≤
        (((dNat : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
            ((aubrunEvenMomentParameter dNat - 1) + 3) *
          (Real.sqrt (sNat : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
            ((aubrunEvenMomentParameter dNat - 1) + 1)) /
          D ^ (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 2)) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatioModel (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73SupportCountAndCayleyRankBudget_linearRatioNormalizedProduct_cancelTwo
        (Q := aubrunProposition71Q 1) (d := (dNat : ℝ))
        (s := (sNat : ℝ)) (D := D) (ρ := ρ)
        (m := aubrunEvenMomentParameter dNat - 1)
        hdPos.le (Real.sqrt_nonneg _) hdD hsqrtD hDpos
        hρ0 hρ1 hP_ρD hCount hNormalized)

/-- Canonical `Q=1` support-count endpoint with the variable-ratio scalar
leaf stated as a product of shifted base ratios.

This is the most readable current scalar frontier: the two factors
`(d+Q)/D` and `(sqrt(s)+Q)/D` must pay for the finite correction `1+2mρ`. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_support_count_cayley_rank_linearRatioRatioPowers_cancelTwo_canonical_Qone
    {dNat sNat : ℕ} {D ρ lam : ℝ}
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatioModel : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hdD : (dNat : ℝ) ≤ D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (hDpos : 0 < D)
    (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1)
    (hP_ρD :
      aubrunProposition73P ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
        ρ * D)
    (hCount : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        (wickPermutationDefectCount (aubrunEvenMomentParameter dNat - 1) Δ :
          ℝ) ≤
          aubrunFixedDefectCountEnvelope
            (aubrunEvenMomentParameter dNat - 1) Δ)
    (hRatio :
      1 + 2 * ((aubrunEvenMomentParameter dNat - 1 : ℕ) : ℝ) * ρ ≤
        (((dNat : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter dNat - 1) + 1)) / D) ^
            ((aubrunEvenMomentParameter dNat - 1) + 3) *
          ((Real.sqrt (sNat : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter dNat - 1) + 1)) / D) ^
            ((aubrunEvenMomentParameter dNat - 1) + 1)) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatioModel (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73SupportCountAndCayleyRankBudget_linearRatioRatioPowers_cancelTwo
        (Q := aubrunProposition71Q 1) (d := (dNat : ℝ))
        (s := (sNat : ℝ)) (D := D) (ρ := ρ)
        (m := aubrunEvenMomentParameter dNat - 1)
        hdPos.le (Real.sqrt_nonneg _) hdD hsqrtD hDpos
        hρ0 hρ1 hP_ρD hCount hRatio)

/-- Canonical `Q=1` tight-range count endpoint with the variable-ratio scalar
leaf stated as a product of shifted base ratios.

This is the same scalar frontier as
`...support_count...linearRatioRatioPowers...`, but the count theorem is stated
over the numerical tight range `Δ≤2m` instead of the image support set. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_tight_count_cayley_rank_linearRatioRatioPowers_cancelTwo_canonical_Qone
    {dNat sNat : ℕ} {D ρ lam : ℝ}
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatioModel : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hdD : (dNat : ℝ) ≤ D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (hDpos : 0 < D)
    (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1)
    (hP_ρD :
      aubrunProposition73P ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
        ρ * D)
    (hCount : ∀ Δ ∈
      Finset.range (2 * (aubrunEvenMomentParameter dNat - 1) + 1),
        (wickPermutationDefectCount (aubrunEvenMomentParameter dNat - 1) Δ :
          ℝ) ≤
          aubrunFixedDefectCountEnvelope
            (aubrunEvenMomentParameter dNat - 1) Δ)
    (hRatio :
      1 + 2 * ((aubrunEvenMomentParameter dNat - 1 : ℕ) : ℝ) * ρ ≤
        (((dNat : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter dNat - 1) + 1)) / D) ^
            ((aubrunEvenMomentParameter dNat - 1) + 3) *
          ((Real.sqrt (sNat : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter dNat - 1) + 1)) / D) ^
            ((aubrunEvenMomentParameter dNat - 1) + 1)) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatioModel (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73TightCountAndCayleyRankBudget_linearRatioRatioPowers_cancelTwo
        (Q := aubrunProposition71Q 1) (d := (dNat : ℝ))
        (s := (sNat : ℝ)) (D := D) (ρ := ρ)
        (m := aubrunEvenMomentParameter dNat - 1)
        hdPos.le (Real.sqrt_nonneg _) hdD hsqrtD hDpos
        hρ0 hρ1 hP_ρD hCount hRatio)

/-- Canonical `Q=1` tight-count endpoint where the first shifted ratio pays
the finite correction by a Bernoulli gain. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_tight_count_cayley_rank_firstBernoulliGain_cancelTwo_canonical_Qone
    {dNat sNat : ℕ} {D α ρ lam : ℝ}
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatioModel : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hdD : (dNat : ℝ) ≤ D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (hDpos : 0 < D)
    (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1)
    (hP_ρD :
      aubrunProposition73P ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
        ρ * D)
    (hCount : ∀ Δ ∈
      Finset.range (2 * (aubrunEvenMomentParameter dNat - 1) + 1),
        (wickPermutationDefectCount (aubrunEvenMomentParameter dNat - 1) Δ :
          ℝ) ≤
          aubrunFixedDefectCountEnvelope
            (aubrunEvenMomentParameter dNat - 1) Δ)
    (hα0 : 0 ≤ α)
    (hFirst :
      1 + α ≤
        (((dNat : ℝ) +
            aubrunProposition71Q 1
              ((aubrunEvenMomentParameter dNat - 1) + 1)) / D))
    (hSecond :
      1 ≤
        ((Real.sqrt (sNat : ℝ) +
            aubrunProposition71Q 1
              ((aubrunEvenMomentParameter dNat - 1) + 1)) / D))
    (hgain :
      (2 * ((aubrunEvenMomentParameter dNat - 1 : ℕ) : ℝ)) * ρ ≤
        (((aubrunEvenMomentParameter dNat - 1 : ℕ) : ℝ) + 3) * α) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatioModel (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73TightCountAndCayleyRankBudget_firstBernoulliGain_cancelTwo
        (Q := aubrunProposition71Q 1) (d := (dNat : ℝ))
        (s := (sNat : ℝ)) (D := D) (α := α) (ρ := ρ)
        (m := aubrunEvenMomentParameter dNat - 1)
        hdPos.le (Real.sqrt_nonneg _) hdD hsqrtD hDpos
        hρ0 hρ1 hP_ρD hCount hα0 hFirst hSecond hgain)

/-- Canonical `Q=1` tight-count endpoint where the second shifted ratio pays
the finite correction by a Bernoulli gain. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_tight_count_cayley_rank_secondBernoulliGain_cancelTwo_canonical_Qone
    {dNat sNat : ℕ} {D β ρ lam : ℝ}
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatioModel : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hdD : (dNat : ℝ) ≤ D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (hDpos : 0 < D)
    (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1)
    (hP_ρD :
      aubrunProposition73P ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
        ρ * D)
    (hCount : ∀ Δ ∈
      Finset.range (2 * (aubrunEvenMomentParameter dNat - 1) + 1),
        (wickPermutationDefectCount (aubrunEvenMomentParameter dNat - 1) Δ :
          ℝ) ≤
          aubrunFixedDefectCountEnvelope
            (aubrunEvenMomentParameter dNat - 1) Δ)
    (hβ0 : 0 ≤ β)
    (hFirst :
      1 ≤
        (((dNat : ℝ) +
            aubrunProposition71Q 1
              ((aubrunEvenMomentParameter dNat - 1) + 1)) / D))
    (hSecond :
      1 + β ≤
        ((Real.sqrt (sNat : ℝ) +
            aubrunProposition71Q 1
              ((aubrunEvenMomentParameter dNat - 1) + 1)) / D))
    (hgain :
      (2 * ((aubrunEvenMomentParameter dNat - 1 : ℕ) : ℝ)) * ρ ≤
        (((aubrunEvenMomentParameter dNat - 1 : ℕ) : ℝ) + 1) * β) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatioModel (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73TightCountAndCayleyRankBudget_secondBernoulliGain_cancelTwo
        (Q := aubrunProposition71Q 1) (d := (dNat : ℝ))
        (s := (sNat : ℝ)) (D := D) (β := β) (ρ := ρ)
        (m := aubrunEvenMomentParameter dNat - 1)
        hdPos.le (Real.sqrt_nonneg _) hdD hsqrtD hDpos
        hρ0 hρ1 hP_ρD hCount hβ0 hFirst hSecond hgain)

/-- Canonical `Q=1` tight-count close-window endpoint on the branch
`sqrt(s)≤d`.  The scalar leaf is supplied with `D=d` and
`ρ=P(k)/d`, so no abstract Bernoulli parameters remain visible. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_tight_count_cayley_rank_firstDimensionBase_Qone
    {dNat sNat : ℕ} {lam : ℝ}
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatioModel : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hsqrt_le_d : Real.sqrt (sNat : ℝ) ≤ (dNat : ℝ))
    (hcloseBelow :
      (dNat : ℝ) ≤ Real.sqrt (sNat : ℝ) +
        aubrunProposition71Q 1
          ((aubrunEvenMomentParameter dNat - 1) + 1))
    (hP_le_d :
      aubrunProposition73P
          ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
        (dNat : ℝ))
    (hCount : ∀ Δ ∈
      Finset.range (2 * (aubrunEvenMomentParameter dNat - 1) + 1),
        (wickPermutationDefectCount (aubrunEvenMomentParameter dNat - 1) Δ :
          ℝ) ≤
          aubrunFixedDefectCountEnvelope
            (aubrunEvenMomentParameter dNat - 1) Δ) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatioModel (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73TightCountAndCayleyRankBudget_firstDimensionBase_Qone
        (d := (dNat : ℝ)) (s := (sNat : ℝ))
        (m := aubrunEvenMomentParameter dNat - 1)
        hdPos.le (Real.sqrt_nonneg _) hdPos hsqrt_le_d hcloseBelow
        hP_le_d hCount)

/-- Canonical `Q=1` tight-count close-window endpoint on the branch
`d≤sqrt(s)`.  The scalar leaf is supplied with `D=sqrt(s)` and
`ρ=P(k)/sqrt(s)`, so no abstract Bernoulli parameters remain visible. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_tight_count_cayley_rank_secondSqrtBase_Qone
    {dNat sNat : ℕ} {lam : ℝ}
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatioModel : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hd_le_sqrt : (dNat : ℝ) ≤ Real.sqrt (sNat : ℝ))
    (hcloseAbove :
      Real.sqrt (sNat : ℝ) ≤ (dNat : ℝ) +
        aubrunProposition71Q 1
          ((aubrunEvenMomentParameter dNat - 1) + 1))
    (hP_le_sqrt :
      aubrunProposition73P
          ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
        Real.sqrt (sNat : ℝ))
    (hCount : ∀ Δ ∈
      Finset.range (2 * (aubrunEvenMomentParameter dNat - 1) + 1),
        (wickPermutationDefectCount (aubrunEvenMomentParameter dNat - 1) Δ :
          ℝ) ≤
          aubrunFixedDefectCountEnvelope
            (aubrunEvenMomentParameter dNat - 1) Δ) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  have hsqrtPos : 0 < Real.sqrt (sNat : ℝ) :=
    Real.sqrt_pos.mpr hsPos
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatioModel (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73TightCountAndCayleyRankBudget_secondSqrtBase_Qone
        (d := (dNat : ℝ)) (s := (sNat : ℝ))
        (m := aubrunEvenMomentParameter dNat - 1)
        hdPos.le (Real.sqrt_nonneg _) hsqrtPos hd_le_sqrt hcloseAbove
        hP_le_sqrt hCount)

/-- Canonical `Q=1` tight-count endpoint in the `Q(k)`-close window.

This wrapper case-splits internally on whether `sqrt(s)≤d` or `d≤sqrt(s)`;
the scalar leaf is no longer exposed as an abstract ratio-power hypothesis. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_tight_count_cayley_rank_closeWindow_Qone
    {dNat sNat : ℕ} {lam : ℝ}
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatioModel : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hclose :
      |(dNat : ℝ) - Real.sqrt (sNat : ℝ)| ≤
        aubrunProposition71Q 1
          ((aubrunEvenMomentParameter dNat - 1) + 1))
    (hP_le_d :
      aubrunProposition73P
          ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
        (dNat : ℝ))
    (hCount : ∀ Δ ∈
      Finset.range (2 * (aubrunEvenMomentParameter dNat - 1) + 1),
        (wickPermutationDefectCount (aubrunEvenMomentParameter dNat - 1) Δ :
          ℝ) ≤
          aubrunFixedDefectCountEnvelope
            (aubrunEvenMomentParameter dNat - 1) Δ) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatioModel (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73TightCountAndCayleyRankBudget_closeWindow_Qone
        (d := (dNat : ℝ)) (s := (sNat : ℝ))
        (m := aubrunEvenMomentParameter dNat - 1)
        hdPos.le (Real.sqrt_nonneg _) hdPos hclose hP_le_d hCount)

/-- Eventual public tight-count endpoint in the `Q(k)`-close window.

The automatic side condition `P(k(d))≤d` is consumed internally; callers only
need eventual positivity, the model lower-ratio inequality, the close-window
condition, and the tight-range fixed-defect count estimate. -/
theorem eventually_gammaExpectation_pipeline_to_spherical_bound_of_prop73_tight_count_cayley_rank_closeWindow_Qone
    {sNat : ℕ → ℕ} {lam : ℝ}
    (hlam : 0 < lam)
    (hsPos : ∀ᶠ d : ℕ in Filter.atTop, 0 < ((sNat d : ℕ) : ℝ))
    (hRatioModel : ∀ᶠ d : ℕ in Filter.atTop,
      lam * (d : ℝ) ^ 2 ≤ ((sNat d : ℕ) : ℝ))
    (hclose : ∀ᶠ d : ℕ in Filter.atTop,
      |(d : ℝ) - Real.sqrt ((sNat d : ℕ) : ℝ)| ≤
        aubrunProposition71Q 1 ((aubrunEvenMomentParameter d - 1) + 1))
    (hCount : ∀ᶠ d : ℕ in Filter.atTop,
      ∀ Δ ∈ Finset.range (2 * (aubrunEvenMomentParameter d - 1) + 1),
        (wickPermutationDefectCount (aubrunEvenMomentParameter d - 1) Δ : ℝ) ≤
          aubrunFixedDefectCountEnvelope (aubrunEvenMomentParameter d - 1) Δ) :
    ∀ᶠ d : ℕ in Filter.atTop,
      gaussianWishartGammaOffDiagonalOpNormMean
          (p := Fin d) (q := Fin d) (σ := Fin (sNat d)) ≤
        aubrunOffDiagonalExpectationEnvelope
          (aubrunProposition71Q 1) (d : ℝ) (sNat d : ℝ)
          (aubrunEvenMomentParameter d) ∧
      gaussianWishartGammaOpNormMean
          (p := Fin d) (q := Fin d) (σ := Fin (sNat d)) ≤
          (2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (d : ℝ) (sNat d : ℝ)
              (aubrunEvenMomentParameter d) ∧
      gaussianQuadraticGammaLiftMean
          (p := Fin d) (q := Fin d) (σ := Fin (sNat d)) ≤
        gaussianQuadraticRadialMean
          (p := Fin d) (q := Fin d) (σ := Fin (sNat d)) *
          (((2 * Real.log 2 + 4 / lam) +
              aubrunOffDiagonalExpectationEnvelope
                (aubrunProposition71Q 1) (d : ℝ) (sNat d : ℝ)
                (aubrunEvenMomentParameter d)) / (d : ℝ) ^ 2) ∧
      sphericalGammaOpNormMean
          (p := Fin d) (q := Fin d) (σ := Fin (sNat d)) ≤
        ((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (d : ℝ) (sNat d : ℝ)
              (aubrunEvenMomentParameter d)) / (d : ℝ) ^ 2 := by
  have hP := eventually_aubrunProposition73P_evenMoment_le_natCast
  have hdpos : ∀ᶠ d : ℕ in Filter.atTop, 0 < (d : ℝ) := by
    rw [Filter.eventually_atTop]
    exact ⟨1, fun d hd => by exact_mod_cast hd⟩
  filter_upwards [hdpos, hsPos, hRatioModel, hclose, hP, hCount] with
    d hd_d hs_d hRatio_d hclose_d hP_d hCount_d
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_prop73_tight_count_cayley_rank_closeWindow_Qone
      (dNat := d) (sNat := sNat d) (lam := lam)
      hd_d hs_d hlam hRatio_d hclose_d hP_d hCount_d

/-- Along the exact square-balanced path `s(d)=d^2`, the sample dimension is
eventually positive. -/
theorem eventually_exactSquare_sample_pos :
    ∀ᶠ d : ℕ in Filter.atTop, 0 < (((d * d : ℕ) : ℝ)) := by
  rw [Filter.eventually_atTop]
  refine ⟨1, ?_⟩
  intro d hd
  exact_mod_cast Nat.mul_pos hd hd

/-- Along the exact square-balanced path `s(d)=d^2`, the model lower-ratio
hypothesis holds with `λ=1`. -/
theorem eventually_exactSquare_ratioModel_one :
    ∀ᶠ d : ℕ in Filter.atTop,
      (1 : ℝ) * (d : ℝ) ^ 2 ≤ (((d * d : ℕ) : ℝ)) := by
  filter_upwards with d
  rw [Nat.cast_mul]
  nlinarith

/-- Along the exact square-balanced path `s(d)=d^2`, the `Q(k)`-close window is
automatic because `sqrt(d^2)=d`. -/
theorem eventually_exactSquare_closeWindow_Qone :
    ∀ᶠ d : ℕ in Filter.atTop,
      |(d : ℝ) - Real.sqrt (((d * d : ℕ) : ℝ))| ≤
        aubrunProposition71Q 1 ((aubrunEvenMomentParameter d - 1) + 1) := by
  filter_upwards with d
  have hsqrt : Real.sqrt (((d * d : ℕ) : ℝ)) = (d : ℝ) := by
    rw [Nat.cast_mul, ← pow_two, Real.sqrt_sq]
    positivity
  have hQ : 0 ≤
      aubrunProposition71Q 1 ((aubrunEvenMomentParameter d - 1) + 1) :=
    aubrunProposition71Q_nonneg (by norm_num) _
  simpa [hsqrt] using hQ

/-- Eventual public tight-count endpoint on the exact square-balanced path
`s(d)=d^2`.

This is the close-window endpoint with the window, positivity, lower-ratio, and
`P(k(d))≤d` side conditions all supplied internally.  The remaining
theorem-strength input is the tight-range fixed-defect count estimate. -/
theorem eventually_gammaExpectation_pipeline_to_spherical_bound_of_prop73_tight_count_cayley_rank_exactSquare_Qone
    (hCount : ∀ᶠ d : ℕ in Filter.atTop,
      ∀ Δ ∈ Finset.range (2 * (aubrunEvenMomentParameter d - 1) + 1),
        (wickPermutationDefectCount (aubrunEvenMomentParameter d - 1) Δ : ℝ) ≤
          aubrunFixedDefectCountEnvelope (aubrunEvenMomentParameter d - 1) Δ) :
    ∀ᶠ d : ℕ in Filter.atTop,
      gaussianWishartGammaOffDiagonalOpNormMean
          (p := Fin d) (q := Fin d) (σ := Fin (d * d)) ≤
        aubrunOffDiagonalExpectationEnvelope
          (aubrunProposition71Q 1) (d : ℝ) (d * d : ℝ)
          (aubrunEvenMomentParameter d) ∧
      gaussianWishartGammaOpNormMean
          (p := Fin d) (q := Fin d) (σ := Fin (d * d)) ≤
          (2 * Real.log 2 + 4 / (1 : ℝ)) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (d : ℝ) (d * d : ℝ)
              (aubrunEvenMomentParameter d) ∧
      gaussianQuadraticGammaLiftMean
          (p := Fin d) (q := Fin d) (σ := Fin (d * d)) ≤
        gaussianQuadraticRadialMean
          (p := Fin d) (q := Fin d) (σ := Fin (d * d)) *
          (((2 * Real.log 2 + 4 / (1 : ℝ)) +
              aubrunOffDiagonalExpectationEnvelope
                (aubrunProposition71Q 1) (d : ℝ) (d * d : ℝ)
                (aubrunEvenMomentParameter d)) / (d : ℝ) ^ 2) ∧
      sphericalGammaOpNormMean
          (p := Fin d) (q := Fin d) (σ := Fin (d * d)) ≤
        ((2 * Real.log 2 + 4 / (1 : ℝ)) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (d : ℝ) (d * d : ℝ)
              (aubrunEvenMomentParameter d)) / (d : ℝ) ^ 2 := by
  simpa using
    eventually_gammaExpectation_pipeline_to_spherical_bound_of_prop73_tight_count_cayley_rank_closeWindow_Qone
      (sNat := fun d => d * d) (lam := (1 : ℝ))
      (by norm_num) eventually_exactSquare_sample_pos
      eventually_exactSquare_ratioModel_one eventually_exactSquare_closeWindow_Qone
      hCount

/-- Canonical `Q=1` support-count endpoint where the first shifted ratio pays
the finite correction by a Bernoulli gain. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_support_count_cayley_rank_firstBernoulliGain_cancelTwo_canonical_Qone
    {dNat sNat : ℕ} {D α ρ lam : ℝ}
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatioModel : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hdD : (dNat : ℝ) ≤ D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (hDpos : 0 < D)
    (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1)
    (hP_ρD :
      aubrunProposition73P ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
        ρ * D)
    (hCount : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        (wickPermutationDefectCount (aubrunEvenMomentParameter dNat - 1) Δ :
          ℝ) ≤
          aubrunFixedDefectCountEnvelope
            (aubrunEvenMomentParameter dNat - 1) Δ)
    (hα0 : 0 ≤ α)
    (hFirst :
      1 + α ≤
        (((dNat : ℝ) +
            aubrunProposition71Q 1
              ((aubrunEvenMomentParameter dNat - 1) + 1)) / D))
    (hSecond :
      1 ≤
        ((Real.sqrt (sNat : ℝ) +
            aubrunProposition71Q 1
              ((aubrunEvenMomentParameter dNat - 1) + 1)) / D))
    (hgain :
      (2 * ((aubrunEvenMomentParameter dNat - 1 : ℕ) : ℝ)) * ρ ≤
        (((aubrunEvenMomentParameter dNat - 1 : ℕ) : ℝ) + 3) * α) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatioModel (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73SupportCountAndCayleyRankBudget_firstBernoulliGain_cancelTwo
        (Q := aubrunProposition71Q 1) (d := (dNat : ℝ))
        (s := (sNat : ℝ)) (D := D) (α := α) (ρ := ρ)
        (m := aubrunEvenMomentParameter dNat - 1)
        hdPos.le (Real.sqrt_nonneg _) hdD hsqrtD hDpos
        hρ0 hρ1 hP_ρD hCount hα0 hFirst hSecond hgain)

/-- Canonical `Q=1` support-count endpoint where the second shifted ratio pays
the finite correction by a Bernoulli gain. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_support_count_cayley_rank_secondBernoulliGain_cancelTwo_canonical_Qone
    {dNat sNat : ℕ} {D β ρ lam : ℝ}
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatioModel : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hdD : (dNat : ℝ) ≤ D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (hDpos : 0 < D)
    (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1)
    (hP_ρD :
      aubrunProposition73P ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
        ρ * D)
    (hCount : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        (wickPermutationDefectCount (aubrunEvenMomentParameter dNat - 1) Δ :
          ℝ) ≤
          aubrunFixedDefectCountEnvelope
            (aubrunEvenMomentParameter dNat - 1) Δ)
    (hβ0 : 0 ≤ β)
    (hFirst :
      1 ≤
        (((dNat : ℝ) +
            aubrunProposition71Q 1
              ((aubrunEvenMomentParameter dNat - 1) + 1)) / D))
    (hSecond :
      1 + β ≤
        ((Real.sqrt (sNat : ℝ) +
            aubrunProposition71Q 1
              ((aubrunEvenMomentParameter dNat - 1) + 1)) / D))
    (hgain :
      (2 * ((aubrunEvenMomentParameter dNat - 1 : ℕ) : ℝ)) * ρ ≤
        (((aubrunEvenMomentParameter dNat - 1 : ℕ) : ℝ) + 1) * β) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatioModel (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73SupportCountAndCayleyRankBudget_secondBernoulliGain_cancelTwo
        (Q := aubrunProposition71Q 1) (d := (dNat : ℝ))
        (s := (sNat : ℝ)) (D := D) (β := β) (ρ := ρ)
        (m := aubrunEvenMomentParameter dNat - 1)
        hdPos.le (Real.sqrt_nonneg _) hdD hsqrtD hDpos
        hρ0 hρ1 hP_ρD hCount hβ0 hFirst hSecond hgain)

/-- Canonical `Q=1` support-count endpoint with the finite ratio sum bounded
by the geometric-series constant `(1-ρ)⁻¹`. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_support_count_cayley_rank_geometricRatioCommonBase_cancelTwo_canonical_Qone
    {dNat sNat : ℕ} {D ρ lam : ℝ}
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatioModel : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hdD : (dNat : ℝ) ≤ D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1)
    (hP_ρD :
      aubrunProposition73P ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
        ρ * D)
    (hCount : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        (wickPermutationDefectCount (aubrunEvenMomentParameter dNat - 1) Δ :
          ℝ) ≤
          aubrunFixedDefectCountEnvelope
            (aubrunEvenMomentParameter dNat - 1) Δ)
    (hEnvelope :
      (1 - ρ)⁻¹ *
          D ^ (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 2) ≤
        ((dNat : ℝ) +
            aubrunProposition71Q 1
              ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
          ((aubrunEvenMomentParameter dNat - 1) + 3) *
          (Real.sqrt (sNat : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
            ((aubrunEvenMomentParameter dNat - 1) + 1)) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatioModel (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73SupportCountAndCayleyRankBudget_geometricRatioCommonBase_cancelTwo
        (Q := aubrunProposition71Q 1) (d := (dNat : ℝ))
        (s := (sNat : ℝ)) (D := D) (ρ := ρ)
        (m := aubrunEvenMomentParameter dNat - 1)
        hdPos.le (Real.sqrt_nonneg _) hdD hsqrtD (le_trans hdPos.le hdD)
        hρ0 hρ1 hP_ρD hCount hEnvelope)

/-- Canonical `Q=1` support-count endpoint with the scalar envelope reduced
to one quadratic gain condition. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_support_count_cayley_rank_quadraticGain_canonical_Qone
    {dNat sNat : ℕ} {D ρ lam : ℝ}
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatioModel : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hdD : (dNat : ℝ) ≤ D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (hD_dQ :
      D ≤ (dNat : ℝ) +
        aubrunProposition71Q 1
          ((aubrunEvenMomentParameter dNat - 1) + 1))
    (hD_sqrtQ :
      D ≤ Real.sqrt (sNat : ℝ) +
        aubrunProposition71Q 1
          ((aubrunEvenMomentParameter dNat - 1) + 1))
    (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1)
    (hP_ρD :
      aubrunProposition73P ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
        ρ * D)
    (hCount : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        (wickPermutationDefectCount (aubrunEvenMomentParameter dNat - 1) Δ :
          ℝ) ≤
          aubrunFixedDefectCountEnvelope
            (aubrunEvenMomentParameter dNat - 1) Δ)
    (hQuad :
      (1 - ρ)⁻¹ * D ^ 2 ≤
        ((dNat : ℝ) +
          aubrunProposition71Q 1
            ((aubrunEvenMomentParameter dNat - 1) + 1)) ^ 2) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatioModel (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73SupportCountAndCayleyRankBudget_quadraticGain
        (Q := aubrunProposition71Q 1) (d := (dNat : ℝ))
        (s := (sNat : ℝ)) (D := D) (ρ := ρ)
        (m := aubrunEvenMomentParameter dNat - 1)
        hdPos.le (Real.sqrt_nonneg _) hdD hsqrtD hD_dQ hD_sqrtQ
        hρ0 hρ1 hP_ρD hCount hQuad)

/-- Canonical `Q=1` support/fiber endpoint with the defect-sensitive finite
ratio scalar leaf.  The remaining scalar comparison keeps
`Σ_{Δ∈support} ρ^Δ` instead of replacing it by a support-card factor. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_fiber_support_cayley_rank_ratioCommonBase_cancelTwo_canonical_Qone
    {dNat sNat : ℕ} {D ρ lam : ℝ}
    {Fiber LeftCouples RightCouples :
      ℕ → Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)) → Type*}
    [∀ Δ I, Fintype (Fiber Δ I)]
    [∀ Δ I, Fintype (LeftCouples Δ I)]
    [∀ Δ I, Fintype (RightCouples Δ I)]
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatioModel : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hdD : (dNat : ℝ) ≤ D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (hρ0 : 0 ≤ ρ)
    (hP_ρD :
      aubrunProposition73P ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
        ρ * D)
    (defectEncode : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        WickPermutationDefectClass (aubrunEvenMomentParameter dNat - 1) Δ ↪
          Sigma (Fiber Δ))
    (encode : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fiber Δ I ↪ LeftCouples Δ I × RightCouples Δ I)
    (hLeft : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (LeftCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hRight : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (RightCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hLarge : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (Fiber Δ I) ≠ 0 →
            ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
              2 * I.card + 2 * Δ)
    (hEnvelope :
      aubrunDefectRatioSupportSum (aubrunEvenMomentParameter dNat - 1) ρ *
          D ^ (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 2) ≤
        ((dNat : ℝ) +
            aubrunProposition71Q 1
              ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
          ((aubrunEvenMomentParameter dNat - 1) + 3) *
          (Real.sqrt (sNat : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
            ((aubrunEvenMomentParameter dNat - 1) + 1)) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatioModel (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73FiberDataSupportAndCayleyRankBudget_ratioCommonBase_cancelTwo
        (Q := aubrunProposition71Q 1) (d := (dNat : ℝ))
        (s := (sNat : ℝ)) (D := D) (ρ := ρ)
        (m := aubrunEvenMomentParameter dNat - 1)
        hdPos.le (Real.sqrt_nonneg _) hdD hsqrtD (le_trans hdPos.le hdD)
        hρ0 hP_ρD defectEncode encode hLeft hRight hLarge hEnvelope)

/-- Canonical `Q=1` support/fiber endpoint with the finite ratio sum bounded
by `1 + 2mρ`.

This is the public fiber-data version of the variable-ratio scalar route: the
innovation-fiber package supplies the support-restricted count estimate, while
the scalar side keeps only the finite correction `1+2mρ`. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_fiber_support_cayley_rank_linearRatioCommonBase_cancelTwo_canonical_Qone
    {dNat sNat : ℕ} {D ρ lam : ℝ}
    {Fiber LeftCouples RightCouples :
      ℕ → Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)) → Type*}
    [∀ Δ I, Fintype (Fiber Δ I)]
    [∀ Δ I, Fintype (LeftCouples Δ I)]
    [∀ Δ I, Fintype (RightCouples Δ I)]
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatioModel : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hdD : (dNat : ℝ) ≤ D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1)
    (hP_ρD :
      aubrunProposition73P ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
        ρ * D)
    (defectEncode : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        WickPermutationDefectClass (aubrunEvenMomentParameter dNat - 1) Δ ↪
          Sigma (Fiber Δ))
    (encode : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fiber Δ I ↪ LeftCouples Δ I × RightCouples Δ I)
    (hLeft : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (LeftCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hRight : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (RightCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hLarge : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (Fiber Δ I) ≠ 0 →
            ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
              2 * I.card + 2 * Δ)
    (hEnvelope :
      (1 + 2 * ((aubrunEvenMomentParameter dNat - 1 : ℕ) : ℝ) * ρ) *
          D ^ (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 2) ≤
        ((dNat : ℝ) +
            aubrunProposition71Q 1
              ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
          ((aubrunEvenMomentParameter dNat - 1) + 3) *
          (Real.sqrt (sNat : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
            ((aubrunEvenMomentParameter dNat - 1) + 1)) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatioModel (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73FiberDataSupportAndCayleyRankBudget_linearRatioCommonBase_cancelTwo
        (Q := aubrunProposition71Q 1) (d := (dNat : ℝ))
        (s := (sNat : ℝ)) (D := D) (ρ := ρ)
        (m := aubrunEvenMomentParameter dNat - 1)
        hdPos.le (Real.sqrt_nonneg _) hdD hsqrtD (le_trans hdPos.le hdD)
        hρ0 hρ1 hP_ρD defectEncode encode hLeft hRight hLarge hEnvelope)

/-- Canonical `Q=1` support/fiber endpoint with the variable-ratio scalar leaf
stated as a normalized-product target.

This is the public fiber-data counterpart of
`...support_count...linearRatioNormalizedProduct...`: the innovation-fiber
package supplies the support-restricted count estimate, and the remaining
scalar target is the normalized product inequality. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_fiber_support_cayley_rank_linearRatioNormalizedProduct_cancelTwo_canonical_Qone
    {dNat sNat : ℕ} {D ρ lam : ℝ}
    {Fiber LeftCouples RightCouples :
      ℕ → Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)) → Type*}
    [∀ Δ I, Fintype (Fiber Δ I)]
    [∀ Δ I, Fintype (LeftCouples Δ I)]
    [∀ Δ I, Fintype (RightCouples Δ I)]
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatioModel : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hdD : (dNat : ℝ) ≤ D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (hDpos : 0 < D)
    (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1)
    (hP_ρD :
      aubrunProposition73P ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
        ρ * D)
    (defectEncode : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        WickPermutationDefectClass (aubrunEvenMomentParameter dNat - 1) Δ ↪
          Sigma (Fiber Δ))
    (encode : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fiber Δ I ↪ LeftCouples Δ I × RightCouples Δ I)
    (hLeft : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (LeftCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hRight : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (RightCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hLarge : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (Fiber Δ I) ≠ 0 →
            ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
              2 * I.card + 2 * Δ)
    (hNormalized :
      1 + 2 * ((aubrunEvenMomentParameter dNat - 1 : ℕ) : ℝ) * ρ ≤
        (((dNat : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
            ((aubrunEvenMomentParameter dNat - 1) + 3) *
          (Real.sqrt (sNat : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
            ((aubrunEvenMomentParameter dNat - 1) + 1)) /
          D ^ (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 2)) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatioModel (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73FiberDataSupportAndCayleyRankBudget_linearRatioNormalizedProduct_cancelTwo
        (Q := aubrunProposition71Q 1) (d := (dNat : ℝ))
        (s := (sNat : ℝ)) (D := D) (ρ := ρ)
      (m := aubrunEvenMomentParameter dNat - 1)
      hdPos.le (Real.sqrt_nonneg _) hdD hsqrtD hDpos
      hρ0 hρ1 hP_ρD defectEncode encode hLeft hRight hLarge hNormalized)

/-- Canonical `Q=1` support/fiber endpoint with the variable-ratio scalar leaf
stated as a product of shifted base ratios. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_fiber_support_cayley_rank_linearRatioRatioPowers_cancelTwo_canonical_Qone
    {dNat sNat : ℕ} {D ρ lam : ℝ}
    {Fiber LeftCouples RightCouples :
      ℕ → Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)) → Type*}
    [∀ Δ I, Fintype (Fiber Δ I)]
    [∀ Δ I, Fintype (LeftCouples Δ I)]
    [∀ Δ I, Fintype (RightCouples Δ I)]
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatioModel : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hdD : (dNat : ℝ) ≤ D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (hDpos : 0 < D)
    (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1)
    (hP_ρD :
      aubrunProposition73P ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
        ρ * D)
    (defectEncode : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        WickPermutationDefectClass (aubrunEvenMomentParameter dNat - 1) Δ ↪
          Sigma (Fiber Δ))
    (encode : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fiber Δ I ↪ LeftCouples Δ I × RightCouples Δ I)
    (hLeft : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (LeftCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hRight : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (RightCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hLarge : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (Fiber Δ I) ≠ 0 →
            ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
              2 * I.card + 2 * Δ)
    (hRatio :
      1 + 2 * ((aubrunEvenMomentParameter dNat - 1 : ℕ) : ℝ) * ρ ≤
        (((dNat : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter dNat - 1) + 1)) / D) ^
            ((aubrunEvenMomentParameter dNat - 1) + 3) *
          ((Real.sqrt (sNat : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter dNat - 1) + 1)) / D) ^
            ((aubrunEvenMomentParameter dNat - 1) + 1)) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatioModel (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73FiberDataSupportAndCayleyRankBudget_linearRatioRatioPowers_cancelTwo
        (Q := aubrunProposition71Q 1) (d := (dNat : ℝ))
        (s := (sNat : ℝ)) (D := D) (ρ := ρ)
      (m := aubrunEvenMomentParameter dNat - 1)
      hdPos.le (Real.sqrt_nonneg _) hdD hsqrtD hDpos
      hρ0 hρ1 hP_ρD defectEncode encode hLeft hRight hLarge hRatio)

/-- Canonical `Q=1` tight-range fiber endpoint with the variable-ratio scalar
leaf stated as a product of shifted base ratios.

This is the fiber-data counterpart of the tight-count endpoint: the innovation
fiber package is required only for the numerical range `Δ≤2m`. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_fiber_tight_cayley_rank_linearRatioRatioPowers_cancelTwo_canonical_Qone
    {dNat sNat : ℕ} {D ρ lam : ℝ}
    {Fiber LeftCouples RightCouples :
      ℕ → Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)) → Type*}
    [∀ Δ I, Fintype (Fiber Δ I)]
    [∀ Δ I, Fintype (LeftCouples Δ I)]
    [∀ Δ I, Fintype (RightCouples Δ I)]
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatioModel : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hdD : (dNat : ℝ) ≤ D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (hDpos : 0 < D)
    (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1)
    (hP_ρD :
      aubrunProposition73P ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
        ρ * D)
    (defectEncode : ∀ Δ ∈
      Finset.range (2 * (aubrunEvenMomentParameter dNat - 1) + 1),
        WickPermutationDefectClass (aubrunEvenMomentParameter dNat - 1) Δ ↪
          Sigma (Fiber Δ))
    (encode : ∀ Δ ∈
      Finset.range (2 * (aubrunEvenMomentParameter dNat - 1) + 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fiber Δ I ↪ LeftCouples Δ I × RightCouples Δ I)
    (hLeft : ∀ Δ ∈
      Finset.range (2 * (aubrunEvenMomentParameter dNat - 1) + 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (LeftCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hRight : ∀ Δ ∈
      Finset.range (2 * (aubrunEvenMomentParameter dNat - 1) + 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (RightCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hLarge : ∀ Δ ∈
      Finset.range (2 * (aubrunEvenMomentParameter dNat - 1) + 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (Fiber Δ I) ≠ 0 →
            ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
              2 * I.card + 2 * Δ)
    (hRatio :
      1 + 2 * ((aubrunEvenMomentParameter dNat - 1 : ℕ) : ℝ) * ρ ≤
        (((dNat : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter dNat - 1) + 1)) / D) ^
            ((aubrunEvenMomentParameter dNat - 1) + 3) *
          ((Real.sqrt (sNat : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter dNat - 1) + 1)) / D) ^
            ((aubrunEvenMomentParameter dNat - 1) + 1)) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatioModel (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73FiberDataTightAndCayleyRankBudget_linearRatioRatioPowers_cancelTwo
        (Q := aubrunProposition71Q 1) (d := (dNat : ℝ))
        (s := (sNat : ℝ)) (D := D) (ρ := ρ)
      (m := aubrunEvenMomentParameter dNat - 1)
      hdPos.le (Real.sqrt_nonneg _) hdD hsqrtD hDpos
      hρ0 hρ1 hP_ρD defectEncode encode hLeft hRight hLarge hRatio)

/-- Canonical `Q=1` tight-range fiber endpoint where the first shifted ratio
pays the finite correction by a Bernoulli gain. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_fiber_tight_cayley_rank_firstBernoulliGain_cancelTwo_canonical_Qone
    {dNat sNat : ℕ} {D α ρ lam : ℝ}
    {Fiber LeftCouples RightCouples :
      ℕ → Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)) → Type*}
    [∀ Δ I, Fintype (Fiber Δ I)]
    [∀ Δ I, Fintype (LeftCouples Δ I)]
    [∀ Δ I, Fintype (RightCouples Δ I)]
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatioModel : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hdD : (dNat : ℝ) ≤ D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (hDpos : 0 < D)
    (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1)
    (hP_ρD :
      aubrunProposition73P ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
        ρ * D)
    (defectEncode : ∀ Δ ∈
      Finset.range (2 * (aubrunEvenMomentParameter dNat - 1) + 1),
        WickPermutationDefectClass (aubrunEvenMomentParameter dNat - 1) Δ ↪
          Sigma (Fiber Δ))
    (encode : ∀ Δ ∈
      Finset.range (2 * (aubrunEvenMomentParameter dNat - 1) + 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fiber Δ I ↪ LeftCouples Δ I × RightCouples Δ I)
    (hLeft : ∀ Δ ∈
      Finset.range (2 * (aubrunEvenMomentParameter dNat - 1) + 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (LeftCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hRight : ∀ Δ ∈
      Finset.range (2 * (aubrunEvenMomentParameter dNat - 1) + 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (RightCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hLarge : ∀ Δ ∈
      Finset.range (2 * (aubrunEvenMomentParameter dNat - 1) + 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (Fiber Δ I) ≠ 0 →
            ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
              2 * I.card + 2 * Δ)
    (hα0 : 0 ≤ α)
    (hFirst :
      1 + α ≤
        (((dNat : ℝ) +
            aubrunProposition71Q 1
              ((aubrunEvenMomentParameter dNat - 1) + 1)) / D))
    (hSecond :
      1 ≤
        ((Real.sqrt (sNat : ℝ) +
            aubrunProposition71Q 1
              ((aubrunEvenMomentParameter dNat - 1) + 1)) / D))
    (hgain :
      (2 * ((aubrunEvenMomentParameter dNat - 1 : ℕ) : ℝ)) * ρ ≤
        (((aubrunEvenMomentParameter dNat - 1 : ℕ) : ℝ) + 3) * α) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_prop73_fiber_tight_cayley_rank_linearRatioRatioPowers_cancelTwo_canonical_Qone
      (dNat := dNat) (sNat := sNat) (D := D) (ρ := ρ) (lam := lam)
      (Fiber := Fiber) (LeftCouples := LeftCouples) (RightCouples := RightCouples)
      hdPos hsPos hlam hRatioModel hdD hsqrtD hDpos hρ0 hρ1 hP_ρD
      defectEncode encode hLeft hRight hLarge
      (aubrun_linearRatio_ratioPowers_of_first_bernoulli_gain
        (Q := aubrunProposition71Q 1) (d := (dNat : ℝ))
        (s := (sNat : ℝ)) (D := D) (α := α) (ρ := ρ)
        (m := aubrunEvenMomentParameter dNat - 1)
        hα0 hFirst hSecond hgain)

/-- Canonical `Q=1` tight-range fiber endpoint where the second shifted ratio
pays the finite correction by a Bernoulli gain. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_fiber_tight_cayley_rank_secondBernoulliGain_cancelTwo_canonical_Qone
    {dNat sNat : ℕ} {D β ρ lam : ℝ}
    {Fiber LeftCouples RightCouples :
      ℕ → Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)) → Type*}
    [∀ Δ I, Fintype (Fiber Δ I)]
    [∀ Δ I, Fintype (LeftCouples Δ I)]
    [∀ Δ I, Fintype (RightCouples Δ I)]
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatioModel : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hdD : (dNat : ℝ) ≤ D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (hDpos : 0 < D)
    (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1)
    (hP_ρD :
      aubrunProposition73P ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
        ρ * D)
    (defectEncode : ∀ Δ ∈
      Finset.range (2 * (aubrunEvenMomentParameter dNat - 1) + 1),
        WickPermutationDefectClass (aubrunEvenMomentParameter dNat - 1) Δ ↪
          Sigma (Fiber Δ))
    (encode : ∀ Δ ∈
      Finset.range (2 * (aubrunEvenMomentParameter dNat - 1) + 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fiber Δ I ↪ LeftCouples Δ I × RightCouples Δ I)
    (hLeft : ∀ Δ ∈
      Finset.range (2 * (aubrunEvenMomentParameter dNat - 1) + 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (LeftCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hRight : ∀ Δ ∈
      Finset.range (2 * (aubrunEvenMomentParameter dNat - 1) + 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (RightCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hLarge : ∀ Δ ∈
      Finset.range (2 * (aubrunEvenMomentParameter dNat - 1) + 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (Fiber Δ I) ≠ 0 →
            ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
              2 * I.card + 2 * Δ)
    (hβ0 : 0 ≤ β)
    (hFirst :
      1 ≤
        (((dNat : ℝ) +
            aubrunProposition71Q 1
              ((aubrunEvenMomentParameter dNat - 1) + 1)) / D))
    (hSecond :
      1 + β ≤
        ((Real.sqrt (sNat : ℝ) +
            aubrunProposition71Q 1
              ((aubrunEvenMomentParameter dNat - 1) + 1)) / D))
    (hgain :
      (2 * ((aubrunEvenMomentParameter dNat - 1 : ℕ) : ℝ)) * ρ ≤
        (((aubrunEvenMomentParameter dNat - 1 : ℕ) : ℝ) + 1) * β) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_prop73_fiber_tight_cayley_rank_linearRatioRatioPowers_cancelTwo_canonical_Qone
      (dNat := dNat) (sNat := sNat) (D := D) (ρ := ρ) (lam := lam)
      (Fiber := Fiber) (LeftCouples := LeftCouples) (RightCouples := RightCouples)
      hdPos hsPos hlam hRatioModel hdD hsqrtD hDpos hρ0 hρ1 hP_ρD
      defectEncode encode hLeft hRight hLarge
      (aubrun_linearRatio_ratioPowers_of_second_bernoulli_gain
        (Q := aubrunProposition71Q 1) (d := (dNat : ℝ))
        (s := (sNat : ℝ)) (D := D) (β := β) (ρ := ρ)
        (m := aubrunEvenMomentParameter dNat - 1)
        hβ0 hFirst hSecond hgain)

/-- Canonical `Q=1` tight-range fiber close-window endpoint on the branch
`sqrt(s)≤d`.  The scalar leaf is supplied with `D=d` and
`ρ=P(k)/d`, so no abstract Bernoulli parameters remain visible. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_fiber_tight_cayley_rank_firstDimensionBase_Qone
    {dNat sNat : ℕ} {lam : ℝ}
    {Fiber LeftCouples RightCouples :
      ℕ → Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)) → Type*}
    [∀ Δ I, Fintype (Fiber Δ I)]
    [∀ Δ I, Fintype (LeftCouples Δ I)]
    [∀ Δ I, Fintype (RightCouples Δ I)]
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatioModel : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hsqrt_le_d : Real.sqrt (sNat : ℝ) ≤ (dNat : ℝ))
    (hcloseBelow :
      (dNat : ℝ) ≤ Real.sqrt (sNat : ℝ) +
        aubrunProposition71Q 1
          ((aubrunEvenMomentParameter dNat - 1) + 1))
    (hP_le_d :
      aubrunProposition73P
          ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
        (dNat : ℝ))
    (defectEncode : ∀ Δ ∈
      Finset.range (2 * (aubrunEvenMomentParameter dNat - 1) + 1),
        WickPermutationDefectClass (aubrunEvenMomentParameter dNat - 1) Δ ↪
          Sigma (Fiber Δ))
    (encode : ∀ Δ ∈
      Finset.range (2 * (aubrunEvenMomentParameter dNat - 1) + 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fiber Δ I ↪ LeftCouples Δ I × RightCouples Δ I)
    (hLeft : ∀ Δ ∈
      Finset.range (2 * (aubrunEvenMomentParameter dNat - 1) + 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (LeftCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hRight : ∀ Δ ∈
      Finset.range (2 * (aubrunEvenMomentParameter dNat - 1) + 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (RightCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hLarge : ∀ Δ ∈
      Finset.range (2 * (aubrunEvenMomentParameter dNat - 1) + 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (Fiber Δ I) ≠ 0 →
            ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
              2 * I.card + 2 * Δ) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatioModel (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73FiberDataTightAndCayleyRankBudget_firstDimensionBase_Qone
        (d := (dNat : ℝ)) (s := (sNat : ℝ))
        (m := aubrunEvenMomentParameter dNat - 1)
        hdPos.le (Real.sqrt_nonneg _) hdPos hsqrt_le_d hcloseBelow
        hP_le_d defectEncode encode hLeft hRight hLarge)

/-- Canonical `Q=1` tight-range fiber close-window endpoint on the branch
`d≤sqrt(s)`.  The scalar leaf is supplied with `D=sqrt(s)` and
`ρ=P(k)/sqrt(s)`, so no abstract Bernoulli parameters remain visible. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_fiber_tight_cayley_rank_secondSqrtBase_Qone
    {dNat sNat : ℕ} {lam : ℝ}
    {Fiber LeftCouples RightCouples :
      ℕ → Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)) → Type*}
    [∀ Δ I, Fintype (Fiber Δ I)]
    [∀ Δ I, Fintype (LeftCouples Δ I)]
    [∀ Δ I, Fintype (RightCouples Δ I)]
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatioModel : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hd_le_sqrt : (dNat : ℝ) ≤ Real.sqrt (sNat : ℝ))
    (hcloseAbove :
      Real.sqrt (sNat : ℝ) ≤ (dNat : ℝ) +
        aubrunProposition71Q 1
          ((aubrunEvenMomentParameter dNat - 1) + 1))
    (hP_le_sqrt :
      aubrunProposition73P
          ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
        Real.sqrt (sNat : ℝ))
    (defectEncode : ∀ Δ ∈
      Finset.range (2 * (aubrunEvenMomentParameter dNat - 1) + 1),
        WickPermutationDefectClass (aubrunEvenMomentParameter dNat - 1) Δ ↪
          Sigma (Fiber Δ))
    (encode : ∀ Δ ∈
      Finset.range (2 * (aubrunEvenMomentParameter dNat - 1) + 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fiber Δ I ↪ LeftCouples Δ I × RightCouples Δ I)
    (hLeft : ∀ Δ ∈
      Finset.range (2 * (aubrunEvenMomentParameter dNat - 1) + 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (LeftCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hRight : ∀ Δ ∈
      Finset.range (2 * (aubrunEvenMomentParameter dNat - 1) + 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (RightCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hLarge : ∀ Δ ∈
      Finset.range (2 * (aubrunEvenMomentParameter dNat - 1) + 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (Fiber Δ I) ≠ 0 →
            ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
              2 * I.card + 2 * Δ) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  have hsqrtPos : 0 < Real.sqrt (sNat : ℝ) :=
    Real.sqrt_pos.mpr hsPos
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatioModel (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73FiberDataTightAndCayleyRankBudget_secondSqrtBase_Qone
        (d := (dNat : ℝ)) (s := (sNat : ℝ))
        (m := aubrunEvenMomentParameter dNat - 1)
        hdPos.le (Real.sqrt_nonneg _) hsqrtPos hd_le_sqrt hcloseAbove
        hP_le_sqrt defectEncode encode hLeft hRight hLarge)

/-- Canonical `Q=1` tight-range fiber endpoint in the `Q(k)`-close window.

This wrapper case-splits internally on whether `sqrt(s)≤d` or `d≤sqrt(s)`;
the scalar leaf is no longer exposed as an abstract ratio-power hypothesis. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_fiber_tight_cayley_rank_closeWindow_Qone
    {dNat sNat : ℕ} {lam : ℝ}
    {Fiber LeftCouples RightCouples :
      ℕ → Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)) → Type*}
    [∀ Δ I, Fintype (Fiber Δ I)]
    [∀ Δ I, Fintype (LeftCouples Δ I)]
    [∀ Δ I, Fintype (RightCouples Δ I)]
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatioModel : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hclose :
      |(dNat : ℝ) - Real.sqrt (sNat : ℝ)| ≤
        aubrunProposition71Q 1
          ((aubrunEvenMomentParameter dNat - 1) + 1))
    (hP_le_d :
      aubrunProposition73P
          ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
        (dNat : ℝ))
    (defectEncode : ∀ Δ ∈
      Finset.range (2 * (aubrunEvenMomentParameter dNat - 1) + 1),
        WickPermutationDefectClass (aubrunEvenMomentParameter dNat - 1) Δ ↪
          Sigma (Fiber Δ))
    (encode : ∀ Δ ∈
      Finset.range (2 * (aubrunEvenMomentParameter dNat - 1) + 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fiber Δ I ↪ LeftCouples Δ I × RightCouples Δ I)
    (hLeft : ∀ Δ ∈
      Finset.range (2 * (aubrunEvenMomentParameter dNat - 1) + 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (LeftCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hRight : ∀ Δ ∈
      Finset.range (2 * (aubrunEvenMomentParameter dNat - 1) + 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (RightCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hLarge : ∀ Δ ∈
      Finset.range (2 * (aubrunEvenMomentParameter dNat - 1) + 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (Fiber Δ I) ≠ 0 →
            ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
              2 * I.card + 2 * Δ) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatioModel (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73FiberDataTightAndCayleyRankBudget_closeWindow_Qone
        (d := (dNat : ℝ)) (s := (sNat : ℝ))
        (m := aubrunEvenMomentParameter dNat - 1)
        hdPos.le (Real.sqrt_nonneg _) hdPos hclose hP_le_d
        defectEncode encode hLeft hRight hLarge)

/-- Eventual public tight-range fiber endpoint in the `Q(k)`-close window.

The automatic side condition `P(k(d))≤d` is consumed internally.  Because the
fiber and couple types may vary with `d`, their construction data is supplied
as eventual nonempty packages and chosen pointwise inside the proof. -/
theorem eventually_gammaExpectation_pipeline_to_spherical_bound_of_prop73_fiber_tight_cayley_rank_closeWindow_Qone
    {sNat : ℕ → ℕ} {lam : ℝ}
    {Fiber LeftCouples RightCouples :
      (d : ℕ) → ℕ → Finset (Fin ((aubrunEvenMomentParameter d - 1) + 1)) → Type*}
    [∀ d Δ I, Fintype (Fiber d Δ I)]
    [∀ d Δ I, Fintype (LeftCouples d Δ I)]
    [∀ d Δ I, Fintype (RightCouples d Δ I)]
    (hlam : 0 < lam)
    (hsPos : ∀ᶠ d : ℕ in Filter.atTop, 0 < ((sNat d : ℕ) : ℝ))
    (hRatioModel : ∀ᶠ d : ℕ in Filter.atTop,
      lam * (d : ℝ) ^ 2 ≤ ((sNat d : ℕ) : ℝ))
    (hclose : ∀ᶠ d : ℕ in Filter.atTop,
      |(d : ℝ) - Real.sqrt ((sNat d : ℕ) : ℝ)| ≤
        aubrunProposition71Q 1 ((aubrunEvenMomentParameter d - 1) + 1))
    (defectEncode : ∀ᶠ d : ℕ in Filter.atTop,
      Nonempty (∀ Δ ∈ Finset.range (2 * (aubrunEvenMomentParameter d - 1) + 1),
        WickPermutationDefectClass (aubrunEvenMomentParameter d - 1) Δ ↪
          Sigma (Fiber d Δ)))
    (encode : ∀ᶠ d : ℕ in Filter.atTop,
      Nonempty (∀ Δ ∈ Finset.range (2 * (aubrunEvenMomentParameter d - 1) + 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter d - 1) + 1)),
          Fiber d Δ I ↪ LeftCouples d Δ I × RightCouples d Δ I))
    (hLeft : ∀ᶠ d : ℕ in Filter.atTop,
      ∀ Δ ∈ Finset.range (2 * (aubrunEvenMomentParameter d - 1) + 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter d - 1) + 1)),
          Fintype.card (LeftCouples d Δ I) ≤
            (2 * ((aubrunEvenMomentParameter d - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter d - 1) + 1) I))
    (hRight : ∀ᶠ d : ℕ in Filter.atTop,
      ∀ Δ ∈ Finset.range (2 * (aubrunEvenMomentParameter d - 1) + 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter d - 1) + 1)),
          Fintype.card (RightCouples d Δ I) ≤
            (2 * ((aubrunEvenMomentParameter d - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter d - 1) + 1) I))
    (hLarge : ∀ᶠ d : ℕ in Filter.atTop,
      ∀ Δ ∈ Finset.range (2 * (aubrunEvenMomentParameter d - 1) + 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter d - 1) + 1)),
          Fintype.card (Fiber d Δ I) ≠ 0 →
            ((aubrunEvenMomentParameter d - 1) + 1) ≤
              2 * I.card + 2 * Δ) :
    ∀ᶠ d : ℕ in Filter.atTop,
      gaussianWishartGammaOffDiagonalOpNormMean
          (p := Fin d) (q := Fin d) (σ := Fin (sNat d)) ≤
        aubrunOffDiagonalExpectationEnvelope
          (aubrunProposition71Q 1) (d : ℝ) (sNat d : ℝ)
          (aubrunEvenMomentParameter d) ∧
      gaussianWishartGammaOpNormMean
          (p := Fin d) (q := Fin d) (σ := Fin (sNat d)) ≤
          (2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (d : ℝ) (sNat d : ℝ)
              (aubrunEvenMomentParameter d) ∧
      gaussianQuadraticGammaLiftMean
          (p := Fin d) (q := Fin d) (σ := Fin (sNat d)) ≤
        gaussianQuadraticRadialMean
          (p := Fin d) (q := Fin d) (σ := Fin (sNat d)) *
          (((2 * Real.log 2 + 4 / lam) +
              aubrunOffDiagonalExpectationEnvelope
                (aubrunProposition71Q 1) (d : ℝ) (sNat d : ℝ)
                (aubrunEvenMomentParameter d)) / (d : ℝ) ^ 2) ∧
      sphericalGammaOpNormMean
          (p := Fin d) (q := Fin d) (σ := Fin (sNat d)) ≤
        ((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (d : ℝ) (sNat d : ℝ)
              (aubrunEvenMomentParameter d)) / (d : ℝ) ^ 2 := by
  have hP := eventually_aubrunProposition73P_evenMoment_le_natCast
  have hdpos : ∀ᶠ d : ℕ in Filter.atTop, 0 < (d : ℝ) := by
    rw [Filter.eventually_atTop]
    exact ⟨1, fun d hd => by exact_mod_cast hd⟩
  filter_upwards [hdpos, hsPos, hRatioModel, hclose, hP,
    defectEncode, encode, hLeft, hRight, hLarge] with
    d hd_d hs_d hRatio_d hclose_d hP_d
      defectEncode_d encode_d hLeft_d hRight_d hLarge_d
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_prop73_fiber_tight_cayley_rank_closeWindow_Qone
      (dNat := d) (sNat := sNat d) (lam := lam)
      (Fiber := Fiber d) (LeftCouples := LeftCouples d)
      (RightCouples := RightCouples d)
      hd_d hs_d hlam hRatio_d hclose_d hP_d
      (Classical.choice defectEncode_d) (Classical.choice encode_d)
      hLeft_d hRight_d hLarge_d

/-- Eventual public tight-range fiber endpoint on the exact square-balanced path
`s(d)=d^2`.

This is the close-window endpoint with the window, positivity, lower-ratio, and
`P(k(d))≤d` side conditions all supplied internally.  The remaining
theorem-strength input is the tight-range Aubrun innovation-fiber package. -/
theorem eventually_gammaExpectation_pipeline_to_spherical_bound_of_prop73_fiber_tight_cayley_rank_exactSquare_Qone
    {Fiber LeftCouples RightCouples :
      (d : ℕ) → ℕ → Finset (Fin ((aubrunEvenMomentParameter d - 1) + 1)) → Type*}
    [∀ d Δ I, Fintype (Fiber d Δ I)]
    [∀ d Δ I, Fintype (LeftCouples d Δ I)]
    [∀ d Δ I, Fintype (RightCouples d Δ I)]
    (defectEncode : ∀ᶠ d : ℕ in Filter.atTop,
      Nonempty (∀ Δ ∈ Finset.range (2 * (aubrunEvenMomentParameter d - 1) + 1),
        WickPermutationDefectClass (aubrunEvenMomentParameter d - 1) Δ ↪
          Sigma (Fiber d Δ)))
    (encode : ∀ᶠ d : ℕ in Filter.atTop,
      Nonempty (∀ Δ ∈ Finset.range (2 * (aubrunEvenMomentParameter d - 1) + 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter d - 1) + 1)),
          Fiber d Δ I ↪ LeftCouples d Δ I × RightCouples d Δ I))
    (hLeft : ∀ᶠ d : ℕ in Filter.atTop,
      ∀ Δ ∈ Finset.range (2 * (aubrunEvenMomentParameter d - 1) + 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter d - 1) + 1)),
          Fintype.card (LeftCouples d Δ I) ≤
            (2 * ((aubrunEvenMomentParameter d - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter d - 1) + 1) I))
    (hRight : ∀ᶠ d : ℕ in Filter.atTop,
      ∀ Δ ∈ Finset.range (2 * (aubrunEvenMomentParameter d - 1) + 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter d - 1) + 1)),
          Fintype.card (RightCouples d Δ I) ≤
            (2 * ((aubrunEvenMomentParameter d - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter d - 1) + 1) I))
    (hLarge : ∀ᶠ d : ℕ in Filter.atTop,
      ∀ Δ ∈ Finset.range (2 * (aubrunEvenMomentParameter d - 1) + 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter d - 1) + 1)),
          Fintype.card (Fiber d Δ I) ≠ 0 →
            ((aubrunEvenMomentParameter d - 1) + 1) ≤
              2 * I.card + 2 * Δ) :
    ∀ᶠ d : ℕ in Filter.atTop,
      gaussianWishartGammaOffDiagonalOpNormMean
          (p := Fin d) (q := Fin d) (σ := Fin (d * d)) ≤
        aubrunOffDiagonalExpectationEnvelope
          (aubrunProposition71Q 1) (d : ℝ) (d * d : ℝ)
          (aubrunEvenMomentParameter d) ∧
      gaussianWishartGammaOpNormMean
          (p := Fin d) (q := Fin d) (σ := Fin (d * d)) ≤
          (2 * Real.log 2 + 4 / (1 : ℝ)) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (d : ℝ) (d * d : ℝ)
              (aubrunEvenMomentParameter d) ∧
      gaussianQuadraticGammaLiftMean
          (p := Fin d) (q := Fin d) (σ := Fin (d * d)) ≤
        gaussianQuadraticRadialMean
          (p := Fin d) (q := Fin d) (σ := Fin (d * d)) *
          (((2 * Real.log 2 + 4 / (1 : ℝ)) +
              aubrunOffDiagonalExpectationEnvelope
                (aubrunProposition71Q 1) (d : ℝ) (d * d : ℝ)
                (aubrunEvenMomentParameter d)) / (d : ℝ) ^ 2) ∧
      sphericalGammaOpNormMean
          (p := Fin d) (q := Fin d) (σ := Fin (d * d)) ≤
        ((2 * Real.log 2 + 4 / (1 : ℝ)) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (d : ℝ) (d * d : ℝ)
              (aubrunEvenMomentParameter d)) / (d : ℝ) ^ 2 := by
  simpa using
    eventually_gammaExpectation_pipeline_to_spherical_bound_of_prop73_fiber_tight_cayley_rank_closeWindow_Qone
      (sNat := fun d => d * d) (lam := (1 : ℝ))
      (Fiber := Fiber) (LeftCouples := LeftCouples)
      (RightCouples := RightCouples)
      (by norm_num) eventually_exactSquare_sample_pos
      eventually_exactSquare_ratioModel_one eventually_exactSquare_closeWindow_Qone
      defectEncode encode hLeft hRight hLarge

/-- Canonical `Q=1` support/fiber endpoint where the first shifted ratio pays
the finite correction by a Bernoulli gain. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_fiber_support_cayley_rank_firstBernoulliGain_cancelTwo_canonical_Qone
    {dNat sNat : ℕ} {D α ρ lam : ℝ}
    {Fiber LeftCouples RightCouples :
      ℕ → Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)) → Type*}
    [∀ Δ I, Fintype (Fiber Δ I)]
    [∀ Δ I, Fintype (LeftCouples Δ I)]
    [∀ Δ I, Fintype (RightCouples Δ I)]
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatioModel : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hdD : (dNat : ℝ) ≤ D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (hDpos : 0 < D)
    (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1)
    (hP_ρD :
      aubrunProposition73P ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
        ρ * D)
    (defectEncode : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        WickPermutationDefectClass (aubrunEvenMomentParameter dNat - 1) Δ ↪
          Sigma (Fiber Δ))
    (encode : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fiber Δ I ↪ LeftCouples Δ I × RightCouples Δ I)
    (hLeft : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (LeftCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hRight : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (RightCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hLarge : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (Fiber Δ I) ≠ 0 →
            ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
              2 * I.card + 2 * Δ)
    (hα0 : 0 ≤ α)
    (hFirst :
      1 + α ≤
        (((dNat : ℝ) +
            aubrunProposition71Q 1
              ((aubrunEvenMomentParameter dNat - 1) + 1)) / D))
    (hSecond :
      1 ≤
        ((Real.sqrt (sNat : ℝ) +
            aubrunProposition71Q 1
              ((aubrunEvenMomentParameter dNat - 1) + 1)) / D))
    (hgain :
      (2 * ((aubrunEvenMomentParameter dNat - 1 : ℕ) : ℝ)) * ρ ≤
        (((aubrunEvenMomentParameter dNat - 1 : ℕ) : ℝ) + 3) * α) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_prop73_fiber_support_cayley_rank_linearRatioRatioPowers_cancelTwo_canonical_Qone
      (dNat := dNat) (sNat := sNat) (D := D) (ρ := ρ) (lam := lam)
      (Fiber := Fiber) (LeftCouples := LeftCouples) (RightCouples := RightCouples)
      hdPos hsPos hlam hRatioModel hdD hsqrtD hDpos hρ0 hρ1 hP_ρD
      defectEncode encode hLeft hRight hLarge
      (aubrun_linearRatio_ratioPowers_of_first_bernoulli_gain
        (Q := aubrunProposition71Q 1) (d := (dNat : ℝ))
        (s := (sNat : ℝ)) (D := D) (α := α) (ρ := ρ)
        (m := aubrunEvenMomentParameter dNat - 1)
        hα0 hFirst hSecond hgain)

/-- Canonical `Q=1` support/fiber endpoint where the second shifted ratio pays
the finite correction by a Bernoulli gain. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_fiber_support_cayley_rank_secondBernoulliGain_cancelTwo_canonical_Qone
    {dNat sNat : ℕ} {D β ρ lam : ℝ}
    {Fiber LeftCouples RightCouples :
      ℕ → Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)) → Type*}
    [∀ Δ I, Fintype (Fiber Δ I)]
    [∀ Δ I, Fintype (LeftCouples Δ I)]
    [∀ Δ I, Fintype (RightCouples Δ I)]
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatioModel : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hdD : (dNat : ℝ) ≤ D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (hDpos : 0 < D)
    (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1)
    (hP_ρD :
      aubrunProposition73P ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
        ρ * D)
    (defectEncode : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        WickPermutationDefectClass (aubrunEvenMomentParameter dNat - 1) Δ ↪
          Sigma (Fiber Δ))
    (encode : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fiber Δ I ↪ LeftCouples Δ I × RightCouples Δ I)
    (hLeft : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (LeftCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hRight : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (RightCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hLarge : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (Fiber Δ I) ≠ 0 →
            ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
              2 * I.card + 2 * Δ)
    (hβ0 : 0 ≤ β)
    (hFirst :
      1 ≤
        (((dNat : ℝ) +
            aubrunProposition71Q 1
              ((aubrunEvenMomentParameter dNat - 1) + 1)) / D))
    (hSecond :
      1 + β ≤
        ((Real.sqrt (sNat : ℝ) +
            aubrunProposition71Q 1
              ((aubrunEvenMomentParameter dNat - 1) + 1)) / D))
    (hgain :
      (2 * ((aubrunEvenMomentParameter dNat - 1 : ℕ) : ℝ)) * ρ ≤
        (((aubrunEvenMomentParameter dNat - 1 : ℕ) : ℝ) + 1) * β) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_prop73_fiber_support_cayley_rank_linearRatioRatioPowers_cancelTwo_canonical_Qone
      (dNat := dNat) (sNat := sNat) (D := D) (ρ := ρ) (lam := lam)
      (Fiber := Fiber) (LeftCouples := LeftCouples) (RightCouples := RightCouples)
      hdPos hsPos hlam hRatioModel hdD hsqrtD hDpos hρ0 hρ1 hP_ρD
      defectEncode encode hLeft hRight hLarge
      (aubrun_linearRatio_ratioPowers_of_second_bernoulli_gain
        (Q := aubrunProposition71Q 1) (d := (dNat : ℝ))
        (s := (sNat : ℝ)) (D := D) (β := β) (ρ := ρ)
        (m := aubrunEvenMomentParameter dNat - 1)
        hβ0 hFirst hSecond hgain)

/-- Canonical `Q=1` support/fiber endpoint with the finite ratio sum bounded
by the geometric-series constant `(1-ρ)⁻¹`. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_fiber_support_cayley_rank_geometricRatioCommonBase_cancelTwo_canonical_Qone
    {dNat sNat : ℕ} {D ρ lam : ℝ}
    {Fiber LeftCouples RightCouples :
      ℕ → Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)) → Type*}
    [∀ Δ I, Fintype (Fiber Δ I)]
    [∀ Δ I, Fintype (LeftCouples Δ I)]
    [∀ Δ I, Fintype (RightCouples Δ I)]
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatioModel : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hdD : (dNat : ℝ) ≤ D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1)
    (hP_ρD :
      aubrunProposition73P ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
        ρ * D)
    (defectEncode : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        WickPermutationDefectClass (aubrunEvenMomentParameter dNat - 1) Δ ↪
          Sigma (Fiber Δ))
    (encode : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fiber Δ I ↪ LeftCouples Δ I × RightCouples Δ I)
    (hLeft : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (LeftCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hRight : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (RightCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hLarge : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (Fiber Δ I) ≠ 0 →
            ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
              2 * I.card + 2 * Δ)
    (hEnvelope :
      (1 - ρ)⁻¹ *
          D ^ (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 2) ≤
        ((dNat : ℝ) +
            aubrunProposition71Q 1
              ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
          ((aubrunEvenMomentParameter dNat - 1) + 3) *
          (Real.sqrt (sNat : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
            ((aubrunEvenMomentParameter dNat - 1) + 1)) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatioModel (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73FiberDataSupportAndCayleyRankBudget_geometricRatioCommonBase_cancelTwo
        (Q := aubrunProposition71Q 1) (d := (dNat : ℝ))
        (s := (sNat : ℝ)) (D := D) (ρ := ρ)
        (m := aubrunEvenMomentParameter dNat - 1)
        hdPos.le (Real.sqrt_nonneg _) hdD hsqrtD (le_trans hdPos.le hdD)
        hρ0 hρ1 hP_ρD defectEncode encode hLeft hRight hLarge hEnvelope)

/-- Canonical `Q=1` geometric-ratio endpoint with the scalar envelope reduced
to one quadratic gain condition. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_fiber_support_cayley_rank_quadraticGain_canonical_Qone
    {dNat sNat : ℕ} {D ρ lam : ℝ}
    {Fiber LeftCouples RightCouples :
      ℕ → Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)) → Type*}
    [∀ Δ I, Fintype (Fiber Δ I)]
    [∀ Δ I, Fintype (LeftCouples Δ I)]
    [∀ Δ I, Fintype (RightCouples Δ I)]
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatioModel : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hdD : (dNat : ℝ) ≤ D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (hD_dQ :
      D ≤ (dNat : ℝ) +
        aubrunProposition71Q 1
          ((aubrunEvenMomentParameter dNat - 1) + 1))
    (hD_sqrtQ :
      D ≤ Real.sqrt (sNat : ℝ) +
        aubrunProposition71Q 1
          ((aubrunEvenMomentParameter dNat - 1) + 1))
    (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1)
    (hP_ρD :
      aubrunProposition73P ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
        ρ * D)
    (defectEncode : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        WickPermutationDefectClass (aubrunEvenMomentParameter dNat - 1) Δ ↪
          Sigma (Fiber Δ))
    (encode : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fiber Δ I ↪ LeftCouples Δ I × RightCouples Δ I)
    (hLeft : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (LeftCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hRight : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (RightCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hLarge : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (Fiber Δ I) ≠ 0 →
            ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
              2 * I.card + 2 * Δ)
    (hQuad :
      (1 - ρ)⁻¹ * D ^ 2 ≤
        ((dNat : ℝ) +
          aubrunProposition71Q 1
            ((aubrunEvenMomentParameter dNat - 1) + 1)) ^ 2) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_prop73_fiber_support_cayley_rank_geometricRatioCommonBase_cancelTwo_canonical_Qone
      (dNat := dNat) (sNat := sNat) (D := D) (ρ := ρ) (lam := lam)
      (Fiber := Fiber) (LeftCouples := LeftCouples) (RightCouples := RightCouples)
      hdPos hsPos hlam hRatioModel hdD hsqrtD hρ0 hρ1 hP_ρD
      defectEncode encode hLeft hRight hLarge
      (aubrun_geometricRatio_scalarEnvelope_of_quadraticGain
        (m := aubrunEvenMomentParameter dNat - 1) (ρ := ρ) (D := D)
      (d := (dNat : ℝ)) (s := (sNat : ℝ))
      (Q := aubrunProposition71Q 1
        ((aubrunEvenMomentParameter dNat - 1) + 1))
        hρ1 (le_trans hdPos.le hdD) hD_dQ hD_sqrtQ hQuad)

/-- Diagnostic for the max-base scalar route: its two cross-base comparisons
force `d` and `sqrt(s)` to be `Q(k)`-close. -/
theorem aubrun_maxBase_crossComparisons_imply_Qclose_canonical_Qone
    {dNat sNat : ℕ}
    (hCrossLeft :
      Real.sqrt (sNat : ℝ) ≤ (dNat : ℝ) +
        aubrunProposition71Q 1
          ((aubrunEvenMomentParameter dNat - 1) + 1))
    (hCrossRight :
      (dNat : ℝ) ≤ Real.sqrt (sNat : ℝ) +
        aubrunProposition71Q 1
          ((aubrunEvenMomentParameter dNat - 1) + 1)) :
    |(dNat : ℝ) - Real.sqrt (sNat : ℝ)| ≤
      aubrunProposition71Q 1
        ((aubrunEvenMomentParameter dNat - 1) + 1) :=
  crossBaseComparisons_imply_abs_sub_le hCrossLeft hCrossRight

/-- Public diagnostic for the first-ratio Bernoulli endpoint: its base
feasibility hypotheses force the same `Q(k)`-close condition as the max-base
cross-comparison branch. -/
theorem aubrun_firstBernoulliGain_implies_Qclose_canonical_Qone
    {dNat sNat : ℕ} {D α : ℝ}
    (hDpos : 0 < D)
    (hdD : (dNat : ℝ) ≤ D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (hα0 : 0 ≤ α)
    (hFirst :
      1 + α ≤
        (((dNat : ℝ) +
            aubrunProposition71Q 1
              ((aubrunEvenMomentParameter dNat - 1) + 1)) / D))
    (hSecond :
      1 ≤
        ((Real.sqrt (sNat : ℝ) +
            aubrunProposition71Q 1
              ((aubrunEvenMomentParameter dNat - 1) + 1)) / D)) :
    |(dNat : ℝ) - Real.sqrt (sNat : ℝ)| ≤
      aubrunProposition71Q 1
        ((aubrunEvenMomentParameter dNat - 1) + 1) :=
  aubrun_linearRatio_firstBernoulliGain_implies_Qclose
    (Q := aubrunProposition71Q 1) (d := (dNat : ℝ)) (s := (sNat : ℝ))
    (D := D) (α := α) (m := aubrunEvenMomentParameter dNat - 1)
    hDpos hdD hsqrtD hα0 hFirst hSecond

/-- Public diagnostic for the second-ratio Bernoulli endpoint: its base
feasibility hypotheses force the same `Q(k)`-close condition as the max-base
cross-comparison branch. -/
theorem aubrun_secondBernoulliGain_implies_Qclose_canonical_Qone
    {dNat sNat : ℕ} {D β : ℝ}
    (hDpos : 0 < D)
    (hdD : (dNat : ℝ) ≤ D)
    (hsqrtD : Real.sqrt (sNat : ℝ) ≤ D)
    (hβ0 : 0 ≤ β)
    (hFirst :
      1 ≤
        (((dNat : ℝ) +
            aubrunProposition71Q 1
              ((aubrunEvenMomentParameter dNat - 1) + 1)) / D))
    (hSecond :
      1 + β ≤
        ((Real.sqrt (sNat : ℝ) +
            aubrunProposition71Q 1
              ((aubrunEvenMomentParameter dNat - 1) + 1)) / D)) :
    |(dNat : ℝ) - Real.sqrt (sNat : ℝ)| ≤
      aubrunProposition71Q 1
        ((aubrunEvenMomentParameter dNat - 1) + 1) :=
  aubrun_linearRatio_secondBernoulliGain_implies_Qclose
    (Q := aubrunProposition71Q 1) (d := (dNat : ℝ)) (s := (sNat : ℝ))
    (D := D) (β := β) (m := aubrunEvenMomentParameter dNat - 1)
    hDpos hdD hsqrtD hβ0 hFirst hSecond

/-- Converse form of the max-base diagnostic: if the two analytic bases are
`Q(k)`-close, then the endpoint's two cross-base comparisons hold. -/
theorem aubrun_Qclose_imply_maxBase_crossComparisons_canonical_Qone
    {dNat sNat : ℕ}
    (hclose :
      |(dNat : ℝ) - Real.sqrt (sNat : ℝ)| ≤
        aubrunProposition71Q 1
          ((aubrunEvenMomentParameter dNat - 1) + 1)) :
    Real.sqrt (sNat : ℝ) ≤ (dNat : ℝ) +
        aubrunProposition71Q 1
          ((aubrunEvenMomentParameter dNat - 1) + 1) ∧
      (dNat : ℝ) ≤ Real.sqrt (sNat : ℝ) +
        aubrunProposition71Q 1
          ((aubrunEvenMomentParameter dNat - 1) + 1) := by
  rw [abs_sub_le_iff] at hclose
  constructor <;> linarith

/-- The max-base endpoint's two cross-base comparisons are exactly the
statement that the analytic bases are `Q(k)`-close. -/
theorem aubrun_maxBase_crossComparisons_iff_Qclose_canonical_Qone
    {dNat sNat : ℕ} :
    (Real.sqrt (sNat : ℝ) ≤ (dNat : ℝ) +
          aubrunProposition71Q 1
            ((aubrunEvenMomentParameter dNat - 1) + 1) ∧
        (dNat : ℝ) ≤ Real.sqrt (sNat : ℝ) +
          aubrunProposition71Q 1
            ((aubrunEvenMomentParameter dNat - 1) + 1)) ↔
      |(dNat : ℝ) - Real.sqrt (sNat : ℝ)| ≤
        aubrunProposition71Q 1
          ((aubrunEvenMomentParameter dNat - 1) + 1) := by
  constructor
  · intro h
    exact aubrun_maxBase_crossComparisons_imply_Qclose_canonical_Qone
      (dNat := dNat) (sNat := sNat) h.1 h.2
  · intro h
    exact aubrun_Qclose_imply_maxBase_crossComparisons_canonical_Qone
      (dNat := dNat) (sNat := sNat) h

/-- If the max-base cross-comparison branch is eventually impossible, then so
is the first-ratio Bernoulli feasibility branch. -/
theorem eventually_aubrun_firstBernoulliGain_impossible_of_crossComparisons_impossible
    {sNat : ℕ → ℕ}
    (hNoCross : ∀ᶠ d : ℕ in Filter.atTop,
      ¬ (Real.sqrt ((sNat d : ℕ) : ℝ) ≤ (d : ℝ) +
            aubrunProposition71Q 1 ((aubrunEvenMomentParameter d - 1) + 1) ∧
          (d : ℝ) ≤ Real.sqrt ((sNat d : ℕ) : ℝ) +
            aubrunProposition71Q 1 ((aubrunEvenMomentParameter d - 1) + 1))) :
    ∀ᶠ d : ℕ in Filter.atTop,
      ¬ ∃ D α : ℝ,
        0 < D ∧
        (d : ℝ) ≤ D ∧
        Real.sqrt ((sNat d : ℕ) : ℝ) ≤ D ∧
        0 ≤ α ∧
        1 + α ≤
          ((d : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter d - 1) + 1)) / D ∧
        1 ≤
          (Real.sqrt ((sNat d : ℕ) : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter d - 1) + 1)) / D := by
  filter_upwards [hNoCross] with d hNoCross_d hFeasible
  rcases hFeasible with
    ⟨D, α, hDpos, hdD, hsqrtD, hα0, hFirst, hSecond⟩
  have hclose :
      |(d : ℝ) - Real.sqrt ((sNat d : ℕ) : ℝ)| ≤
        aubrunProposition71Q 1
          ((aubrunEvenMomentParameter d - 1) + 1) :=
    aubrun_firstBernoulliGain_implies_Qclose_canonical_Qone
      (dNat := d) (sNat := sNat d) (D := D) (α := α)
      hDpos hdD hsqrtD hα0 hFirst hSecond
  have hCross :=
    aubrun_Qclose_imply_maxBase_crossComparisons_canonical_Qone
      (dNat := d) (sNat := sNat d) hclose
  exact hNoCross_d hCross

/-- If the max-base cross-comparison branch is eventually impossible, then so
is the second-ratio Bernoulli feasibility branch. -/
theorem eventually_aubrun_secondBernoulliGain_impossible_of_crossComparisons_impossible
    {sNat : ℕ → ℕ}
    (hNoCross : ∀ᶠ d : ℕ in Filter.atTop,
      ¬ (Real.sqrt ((sNat d : ℕ) : ℝ) ≤ (d : ℝ) +
            aubrunProposition71Q 1 ((aubrunEvenMomentParameter d - 1) + 1) ∧
          (d : ℝ) ≤ Real.sqrt ((sNat d : ℕ) : ℝ) +
            aubrunProposition71Q 1 ((aubrunEvenMomentParameter d - 1) + 1))) :
    ∀ᶠ d : ℕ in Filter.atTop,
      ¬ ∃ D β : ℝ,
        0 < D ∧
        (d : ℝ) ≤ D ∧
        Real.sqrt ((sNat d : ℕ) : ℝ) ≤ D ∧
        0 ≤ β ∧
        1 ≤
          ((d : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter d - 1) + 1)) / D ∧
        1 + β ≤
          (Real.sqrt ((sNat d : ℕ) : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter d - 1) + 1)) / D := by
  filter_upwards [hNoCross] with d hNoCross_d hFeasible
  rcases hFeasible with
    ⟨D, β, hDpos, hdD, hsqrtD, hβ0, hFirst, hSecond⟩
  have hclose :
      |(d : ℝ) - Real.sqrt ((sNat d : ℕ) : ℝ)| ≤
        aubrunProposition71Q 1
          ((aubrunEvenMomentParameter d - 1) + 1) :=
    aubrun_secondBernoulliGain_implies_Qclose_canonical_Qone
      (dNat := d) (sNat := sNat d) (D := D) (β := β)
      hDpos hdD hsqrtD hβ0 hFirst hSecond
  have hCross :=
    aubrun_Qclose_imply_maxBase_crossComparisons_canonical_Qone
      (dNat := d) (sNat := sNat d) hclose
  exact hNoCross_d hCross

/-- Linear base gaps eventually rule out first-ratio Bernoulli feasibility. -/
theorem eventually_aubrun_firstBernoulliGain_impossible_of_linear_gap
    {sNat : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hgap : ∀ᶠ d : ℕ in Filter.atTop,
      c * (d : ℝ) ≤ |(d : ℝ) - Real.sqrt ((sNat d : ℕ) : ℝ)|) :
    ∀ᶠ d : ℕ in Filter.atTop,
      ¬ ∃ D α : ℝ,
        0 < D ∧
        (d : ℝ) ≤ D ∧
        Real.sqrt ((sNat d : ℕ) : ℝ) ≤ D ∧
        0 ≤ α ∧
        1 + α ≤
          ((d : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter d - 1) + 1)) / D ∧
        1 ≤
          (Real.sqrt ((sNat d : ℕ) : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter d - 1) + 1)) / D :=
  eventually_aubrun_firstBernoulliGain_impossible_of_crossComparisons_impossible
    (sNat := sNat)
    (eventually_aubrun_maxBase_crossComparisons_impossible_of_linear_gap
      (sNat := sNat) hc hgap)

/-- Linear base gaps eventually rule out second-ratio Bernoulli feasibility. -/
theorem eventually_aubrun_secondBernoulliGain_impossible_of_linear_gap
    {sNat : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hgap : ∀ᶠ d : ℕ in Filter.atTop,
      c * (d : ℝ) ≤ |(d : ℝ) - Real.sqrt ((sNat d : ℕ) : ℝ)|) :
    ∀ᶠ d : ℕ in Filter.atTop,
      ¬ ∃ D β : ℝ,
        0 < D ∧
        (d : ℝ) ≤ D ∧
        Real.sqrt ((sNat d : ℕ) : ℝ) ≤ D ∧
        0 ≤ β ∧
        1 ≤
          ((d : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter d - 1) + 1)) / D ∧
        1 + β ≤
          (Real.sqrt ((sNat d : ℕ) : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter d - 1) + 1)) / D :=
  eventually_aubrun_secondBernoulliGain_impossible_of_crossComparisons_impossible
    (sNat := sNat)
    (eventually_aubrun_maxBase_crossComparisons_impossible_of_linear_gap
      (sNat := sNat) hc hgap)

/-- A limiting ratio `sqrt(s(d))/d → L ≠ 1` eventually rules out first-ratio
Bernoulli feasibility. -/
theorem eventually_aubrun_firstBernoulliGain_impossible_of_sqrt_ratio_ne_one
    {sNat : ℕ → ℕ} {L : ℝ} (hL : L ≠ 1)
    (hT : Filter.Tendsto
      (fun d : ℕ => Real.sqrt ((sNat d : ℕ) : ℝ) / (d : ℝ))
      Filter.atTop (nhds L)) :
    ∀ᶠ d : ℕ in Filter.atTop,
      ¬ ∃ D α : ℝ,
        0 < D ∧
        (d : ℝ) ≤ D ∧
        Real.sqrt ((sNat d : ℕ) : ℝ) ≤ D ∧
        0 ≤ α ∧
        1 + α ≤
          ((d : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter d - 1) + 1)) / D ∧
        1 ≤
          (Real.sqrt ((sNat d : ℕ) : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter d - 1) + 1)) / D :=
  eventually_aubrun_firstBernoulliGain_impossible_of_crossComparisons_impossible
    (sNat := sNat)
    (eventually_aubrun_maxBase_crossComparisons_impossible_of_sqrt_ratio_ne_one
      (sNat := sNat) hL hT)

/-- A limiting ratio `sqrt(s(d))/d → L ≠ 1` eventually rules out second-ratio
Bernoulli feasibility. -/
theorem eventually_aubrun_secondBernoulliGain_impossible_of_sqrt_ratio_ne_one
    {sNat : ℕ → ℕ} {L : ℝ} (hL : L ≠ 1)
    (hT : Filter.Tendsto
      (fun d : ℕ => Real.sqrt ((sNat d : ℕ) : ℝ) / (d : ℝ))
      Filter.atTop (nhds L)) :
    ∀ᶠ d : ℕ in Filter.atTop,
      ¬ ∃ D β : ℝ,
        0 < D ∧
        (d : ℝ) ≤ D ∧
        Real.sqrt ((sNat d : ℕ) : ℝ) ≤ D ∧
        0 ≤ β ∧
        1 ≤
          ((d : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter d - 1) + 1)) / D ∧
        1 + β ≤
          (Real.sqrt ((sNat d : ℕ) : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter d - 1) + 1)) / D :=
  eventually_aubrun_secondBernoulliGain_impossible_of_crossComparisons_impossible
    (sNat := sNat)
    (eventually_aubrun_maxBase_crossComparisons_impossible_of_sqrt_ratio_ne_one
      (sNat := sNat) hL hT)

/-- Away from the square-balanced case, the first-ratio Bernoulli feasibility
hypotheses eventually cannot hold.

The proof is just the checked scalar chain: first-ratio Bernoulli feasibility
forces `Q(k(d))`-closeness of `d` and `sqrt(s(d))`; a non-square balanced
sample ratio makes that closeness eventually impossible. -/
theorem eventually_aubrun_firstBernoulliGain_impossible_of_sample_ratio_ne_one
    {sNat : ℕ → ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam : lam ≠ 1)
    (hRatio : Filter.Tendsto
      (fun d : ℕ => ((sNat d : ℕ) : ℝ) / (d : ℝ) ^ 2)
      Filter.atTop (nhds lam)) :
    ∀ᶠ d : ℕ in Filter.atTop,
      ¬ ∃ D α : ℝ,
        0 < D ∧
        (d : ℝ) ≤ D ∧
        Real.sqrt ((sNat d : ℕ) : ℝ) ≤ D ∧
        0 ≤ α ∧
        1 + α ≤
          ((d : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter d - 1) + 1)) / D ∧
        1 ≤
          (Real.sqrt ((sNat d : ℕ) : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter d - 1) + 1)) / D := by
  exact
    eventually_aubrun_firstBernoulliGain_impossible_of_crossComparisons_impossible
      (sNat := sNat)
      (eventually_aubrun_maxBase_crossComparisons_impossible_of_sample_ratio_ne_one
        (sNat := sNat) hlam0 hlam hRatio)

/-- Away from the square-balanced case, the second-ratio Bernoulli feasibility
hypotheses eventually cannot hold. -/
theorem eventually_aubrun_secondBernoulliGain_impossible_of_sample_ratio_ne_one
    {sNat : ℕ → ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam : lam ≠ 1)
    (hRatio : Filter.Tendsto
      (fun d : ℕ => ((sNat d : ℕ) : ℝ) / (d : ℝ) ^ 2)
      Filter.atTop (nhds lam)) :
    ∀ᶠ d : ℕ in Filter.atTop,
      ¬ ∃ D β : ℝ,
        0 < D ∧
        (d : ℝ) ≤ D ∧
        Real.sqrt ((sNat d : ℕ) : ℝ) ≤ D ∧
        0 ≤ β ∧
        1 ≤
          ((d : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter d - 1) + 1)) / D ∧
        1 + β ≤
          (Real.sqrt ((sNat d : ℕ) : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter d - 1) + 1)) / D := by
  exact
    eventually_aubrun_secondBernoulliGain_impossible_of_crossComparisons_impossible
      (sNat := sNat)
      (eventually_aubrun_maxBase_crossComparisons_impossible_of_sample_ratio_ne_one
        (sNat := sNat) hlam0 hlam hRatio)

/-- The quadratic-gain assumption forces strict slack in the first analytic
base whenever `0<ρ<1`. -/
theorem quadraticGain_requires_strict_base_slack
    {D A ρ : ℝ}
    (hDpos : 0 < D) (hA0 : 0 ≤ A)
    (hρpos : 0 < ρ) (hρ1 : ρ < 1)
    (hQuad : (1 - ρ)⁻¹ * D ^ 2 ≤ A ^ 2) :
    D < A := by
  have hdenpos : 0 < 1 - ρ := by linarith
  have hdenlt : 1 - ρ < 1 := by linarith
  have hone_lt_inv : 1 < (1 - ρ)⁻¹ := by
    exact (one_lt_inv₀ hdenpos).mpr hdenlt
  have hDsqpos : 0 < D ^ 2 := sq_pos_of_pos hDpos
  have hDsq_lt : D ^ 2 < A ^ 2 := by nlinarith
  have habs : |D| < |A| := sq_lt_sq.mp hDsq_lt
  rwa [abs_of_pos hDpos, abs_of_nonneg hA0] at habs

/-- In the canonical max-base endpoint, the quadratic-gain hypothesis is a
strict-slack requirement: the target base `d+Q(k)` must be strictly larger than
`max(d,sqrt(s))`. -/
theorem aubrun_maxBase_quadraticGain_requires_strict_dQ_slack_canonical_Qone
    {dNat sNat : ℕ} {ρ : ℝ}
    (hdPos : 0 < (dNat : ℝ))
    (hρpos : 0 < ρ) (hρ1 : ρ < 1)
    (hQuad :
      (1 - ρ)⁻¹ * max (dNat : ℝ) (Real.sqrt (sNat : ℝ)) ^ 2 ≤
        ((dNat : ℝ) +
          aubrunProposition71Q 1
            ((aubrunEvenMomentParameter dNat - 1) + 1)) ^ 2) :
    max (dNat : ℝ) (Real.sqrt (sNat : ℝ)) <
      (dNat : ℝ) +
        aubrunProposition71Q 1
          ((aubrunEvenMomentParameter dNat - 1) + 1) := by
  have hDpos : 0 < max (dNat : ℝ) (Real.sqrt (sNat : ℝ)) :=
    lt_of_lt_of_le hdPos (le_max_left _ _)
  have hA0 :
      0 ≤ (dNat : ℝ) +
        aubrunProposition71Q 1
          ((aubrunEvenMomentParameter dNat - 1) + 1) := by
    exact add_nonneg hdPos.le
      (aubrunProposition71Q_nonneg (by norm_num)
        ((aubrunEvenMomentParameter dNat - 1) + 1))
  exact quadraticGain_requires_strict_base_slack
    hDpos hA0 hρpos hρ1 hQuad

/-- Eventual public-shape no-go for the max-base quadratic-gain hypothesis.

For any sample-size path and every fixed `0<ρ<1`, the exact quadratic-gain
hypothesis used by the max-base public endpoints eventually fails. -/
theorem eventually_aubrun_maxBase_quadraticGain_dimension_sqrt_sample_impossible
    {sNat : ℕ → ℕ} {ρ : ℝ} (hρpos : 0 < ρ) (hρ1 : ρ < 1) :
    ∀ᶠ d : ℕ in Filter.atTop,
      ¬ ((1 - ρ)⁻¹ * max (d : ℝ) (Real.sqrt (sNat d : ℝ)) ^ 2 ≤
        ((d : ℝ) +
          aubrunProposition71Q 1
            ((aubrunEvenMomentParameter d - 1) + 1)) ^ 2) :=
  eventually_aubrun_maxBase_quadraticGain_impossible
    (S := fun d => Real.sqrt (sNat d : ℝ)) hρpos hρ1

/-- Contrapositive diagnostic for the max-base scalar route. -/
theorem aubrun_maxBase_crossComparisons_impossible_of_Qgap_canonical_Qone
    {dNat sNat : ℕ}
    (hCrossLeft :
      Real.sqrt (sNat : ℝ) ≤ (dNat : ℝ) +
        aubrunProposition71Q 1
          ((aubrunEvenMomentParameter dNat - 1) + 1))
    (hCrossRight :
      (dNat : ℝ) ≤ Real.sqrt (sNat : ℝ) +
        aubrunProposition71Q 1
          ((aubrunEvenMomentParameter dNat - 1) + 1))
    (hgap :
      aubrunProposition71Q 1
          ((aubrunEvenMomentParameter dNat - 1) + 1) <
        |(dNat : ℝ) - Real.sqrt (sNat : ℝ)|) : False :=
  crossBaseComparisons_impossible_of_abs_gt hCrossLeft hCrossRight hgap

/-- Canonical `Q=1` support-count quadratic-gain endpoint with the common base
fixed to `max(d, sqrt s)`. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_support_count_cayley_rank_maxBase_quadraticGain_canonical_Qone
    {dNat sNat : ℕ} {ρ lam : ℝ}
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatioModel : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hCrossLeft :
      Real.sqrt (sNat : ℝ) ≤ (dNat : ℝ) +
        aubrunProposition71Q 1
          ((aubrunEvenMomentParameter dNat - 1) + 1))
    (hCrossRight :
      (dNat : ℝ) ≤ Real.sqrt (sNat : ℝ) +
        aubrunProposition71Q 1
          ((aubrunEvenMomentParameter dNat - 1) + 1))
    (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1)
    (hP_ρD :
      aubrunProposition73P ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
        ρ * max (dNat : ℝ) (Real.sqrt (sNat : ℝ)))
    (hCount : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        (wickPermutationDefectCount (aubrunEvenMomentParameter dNat - 1) Δ :
          ℝ) ≤
          aubrunFixedDefectCountEnvelope
            (aubrunEvenMomentParameter dNat - 1) Δ)
    (hQuad :
      (1 - ρ)⁻¹ * max (dNat : ℝ) (Real.sqrt (sNat : ℝ)) ^ 2 ≤
        ((dNat : ℝ) +
          aubrunProposition71Q 1
            ((aubrunEvenMomentParameter dNat - 1) + 1)) ^ 2) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  let k := (aubrunEvenMomentParameter dNat - 1) + 1
  have hQ0 : 0 ≤ aubrunProposition71Q 1 k :=
    aubrunProposition71Q_nonneg (by norm_num) k
  have hD_dQ :
      max (dNat : ℝ) (Real.sqrt (sNat : ℝ)) ≤
        (dNat : ℝ) + aubrunProposition71Q 1 k := by
    exact max_le (by linarith) hCrossLeft
  have hD_sqrtQ :
      max (dNat : ℝ) (Real.sqrt (sNat : ℝ)) ≤
        Real.sqrt (sNat : ℝ) + aubrunProposition71Q 1 k := by
    exact max_le hCrossRight (by linarith)
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_prop73_support_count_cayley_rank_quadraticGain_canonical_Qone
      (dNat := dNat) (sNat := sNat)
      (D := max (dNat : ℝ) (Real.sqrt (sNat : ℝ))) (ρ := ρ) (lam := lam)
      hdPos hsPos hlam hRatioModel (le_max_left _ _) (le_max_right _ _)
      hD_dQ hD_sqrtQ hρ0 hρ1 hP_ρD hCount hQuad

/-- Canonical support-count max-base endpoint with the two cross-base
comparisons replaced by the equivalent single closeness condition
`|d - sqrt(s)|≤Q(k)`. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_support_count_cayley_rank_maxBase_quadraticGain_Qclose_canonical_Qone
    {dNat sNat : ℕ} {ρ lam : ℝ}
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatioModel : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hclose :
      |(dNat : ℝ) - Real.sqrt (sNat : ℝ)| ≤
        aubrunProposition71Q 1
          ((aubrunEvenMomentParameter dNat - 1) + 1))
    (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1)
    (hP_ρD :
      aubrunProposition73P ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
        ρ * max (dNat : ℝ) (Real.sqrt (sNat : ℝ)))
    (hCount : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        (wickPermutationDefectCount (aubrunEvenMomentParameter dNat - 1) Δ :
          ℝ) ≤
          aubrunFixedDefectCountEnvelope
            (aubrunEvenMomentParameter dNat - 1) Δ)
    (hQuad :
      (1 - ρ)⁻¹ * max (dNat : ℝ) (Real.sqrt (sNat : ℝ)) ^ 2 ≤
        ((dNat : ℝ) +
          aubrunProposition71Q 1
            ((aubrunEvenMomentParameter dNat - 1) + 1)) ^ 2) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  have hCross :=
    aubrun_Qclose_imply_maxBase_crossComparisons_canonical_Qone
      (dNat := dNat) (sNat := sNat) hclose
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_prop73_support_count_cayley_rank_maxBase_quadraticGain_canonical_Qone
      (dNat := dNat) (sNat := sNat) (ρ := ρ) (lam := lam)
      hdPos hsPos hlam hRatioModel hCross.1 hCross.2 hρ0 hρ1 hP_ρD
      hCount hQuad

/-- Canonical `Q=1` quadratic-gain endpoint with the common base fixed to
`max(d, sqrt s)`. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_fiber_support_cayley_rank_maxBase_quadraticGain_canonical_Qone
    {dNat sNat : ℕ} {ρ lam : ℝ}
    {Fiber LeftCouples RightCouples :
      ℕ → Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)) → Type*}
    [∀ Δ I, Fintype (Fiber Δ I)]
    [∀ Δ I, Fintype (LeftCouples Δ I)]
    [∀ Δ I, Fintype (RightCouples Δ I)]
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatioModel : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hCrossLeft :
      Real.sqrt (sNat : ℝ) ≤ (dNat : ℝ) +
        aubrunProposition71Q 1
          ((aubrunEvenMomentParameter dNat - 1) + 1))
    (hCrossRight :
      (dNat : ℝ) ≤ Real.sqrt (sNat : ℝ) +
        aubrunProposition71Q 1
          ((aubrunEvenMomentParameter dNat - 1) + 1))
    (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1)
    (hP_ρD :
      aubrunProposition73P ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
        ρ * max (dNat : ℝ) (Real.sqrt (sNat : ℝ)))
    (defectEncode : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        WickPermutationDefectClass (aubrunEvenMomentParameter dNat - 1) Δ ↪
          Sigma (Fiber Δ))
    (encode : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fiber Δ I ↪ LeftCouples Δ I × RightCouples Δ I)
    (hLeft : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (LeftCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hRight : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (RightCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hLarge : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (Fiber Δ I) ≠ 0 →
            ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
      2 * I.card + 2 * Δ)
    (hQuad :
      (1 - ρ)⁻¹ * max (dNat : ℝ) (Real.sqrt (sNat : ℝ)) ^ 2 ≤
        ((dNat : ℝ) +
          aubrunProposition71Q 1
            ((aubrunEvenMomentParameter dNat - 1) + 1)) ^ 2) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  let k := (aubrunEvenMomentParameter dNat - 1) + 1
  have hQ0 : 0 ≤ aubrunProposition71Q 1 k :=
    aubrunProposition71Q_nonneg (by norm_num) k
  have hD_dQ :
      max (dNat : ℝ) (Real.sqrt (sNat : ℝ)) ≤
        (dNat : ℝ) + aubrunProposition71Q 1 k := by
    exact max_le (by linarith) hCrossLeft
  have hD_sqrtQ :
      max (dNat : ℝ) (Real.sqrt (sNat : ℝ)) ≤
        Real.sqrt (sNat : ℝ) + aubrunProposition71Q 1 k := by
    exact max_le hCrossRight (by linarith)
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_prop73_fiber_support_cayley_rank_quadraticGain_canonical_Qone
      (dNat := dNat) (sNat := sNat)
      (D := max (dNat : ℝ) (Real.sqrt (sNat : ℝ))) (ρ := ρ) (lam := lam)
      (Fiber := Fiber) (LeftCouples := LeftCouples) (RightCouples := RightCouples)
      hdPos hsPos hlam hRatioModel (le_max_left _ _) (le_max_right _ _)
      hD_dQ hD_sqrtQ hρ0 hρ1 hP_ρD defectEncode encode hLeft hRight hLarge
      hQuad

/-- Canonical max-base endpoint with the two cross-base comparisons replaced
by the equivalent single closeness condition
`|d - sqrt(s)|≤Q(k)`.  This is the clean special-regime form of the max-base
route. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_fiber_support_cayley_rank_maxBase_quadraticGain_Qclose_canonical_Qone
    {dNat sNat : ℕ} {ρ lam : ℝ}
    {Fiber LeftCouples RightCouples :
      ℕ → Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)) → Type*}
    [∀ Δ I, Fintype (Fiber Δ I)]
    [∀ Δ I, Fintype (LeftCouples Δ I)]
    [∀ Δ I, Fintype (RightCouples Δ I)]
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatioModel : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hclose :
      |(dNat : ℝ) - Real.sqrt (sNat : ℝ)| ≤
        aubrunProposition71Q 1
          ((aubrunEvenMomentParameter dNat - 1) + 1))
    (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1)
    (hP_ρD :
      aubrunProposition73P ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
        ρ * max (dNat : ℝ) (Real.sqrt (sNat : ℝ)))
    (defectEncode : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        WickPermutationDefectClass (aubrunEvenMomentParameter dNat - 1) Δ ↪
          Sigma (Fiber Δ))
    (encode : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fiber Δ I ↪ LeftCouples Δ I × RightCouples Δ I)
    (hLeft : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (LeftCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hRight : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (RightCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hLarge : ∀ Δ ∈
      wickDefectSupport (aubrunEvenMomentParameter dNat - 1),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (Fiber Δ I) ≠ 0 →
            ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
              2 * I.card + 2 * Δ)
    (hQuad :
      (1 - ρ)⁻¹ * max (dNat : ℝ) (Real.sqrt (sNat : ℝ)) ^ 2 ≤
        ((dNat : ℝ) +
          aubrunProposition71Q 1
            ((aubrunEvenMomentParameter dNat - 1) + 1)) ^ 2) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  have hCross :=
    aubrun_Qclose_imply_maxBase_crossComparisons_canonical_Qone
      (dNat := dNat) (sNat := sNat) hclose
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_prop73_fiber_support_cayley_rank_maxBase_quadraticGain_canonical_Qone
      (dNat := dNat) (sNat := sNat) (ρ := ρ) (lam := lam)
      (Fiber := Fiber) (LeftCouples := LeftCouples) (RightCouples := RightCouples)
      hdPos hsPos hlam hRatioModel hCross.1 hCross.2 hρ0 hρ1 hP_ρD
      defectEncode encode hLeft hRight hLarge hQuad

/-- Eventual supplier for the max-base defect-ratio hypothesis in the
canonical public endpoint.

For any sample-size path `sNat(d)`, the scalar limit `P(k(d))/d→0` implies
the pointwise max-base condition
`P(k(d))≤ρ max(d,sqrt(sNat(d)))` eventually. -/
theorem eventually_aubrunProposition73P_evenMoment_le_rho_mul_max_dimension_sqrt_sample
    {sNat : ℕ → ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (hRatio :
      Filter.Tendsto
        (fun d : ℕ =>
          aubrunProposition73P ((aubrunEvenMomentParameter d - 1) + 1) /
            (d : ℝ))
        Filter.atTop (nhds 0)) :
    ∀ᶠ d in Filter.atTop,
      aubrunProposition73P ((aubrunEvenMomentParameter d - 1) + 1) ≤
        ρ * max (d : ℝ) (Real.sqrt (sNat d : ℝ)) :=
  eventually_aubrunProposition73P_evenMoment_le_rho_mul_max_natCast_of_tendsto_div_natCast_zero
    (S := fun d => Real.sqrt (sNat d : ℝ)) hρ hRatio

/-- Closed eventual supplier for the max-base defect-ratio hypothesis in the
canonical public endpoint.

For any sample-size path `sNat(d)` and any fixed `ρ>0`, the concrete
logarithmic even-moment choice gives
`P(k(d))≤ρ max(d,sqrt(sNat(d)))` eventually. -/
theorem eventually_aubrunProposition73P_evenMoment_le_rho_mul_max_dimension_sqrt_sample_closed
    {sNat : ℕ → ℕ} {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ d in Filter.atTop,
      aubrunProposition73P ((aubrunEvenMomentParameter d - 1) + 1) ≤
        ρ * max (d : ℝ) (Real.sqrt (sNat d : ℝ)) :=
  eventually_aubrunProposition73P_evenMoment_le_rho_mul_max_natCast
    (S := fun d => Real.sqrt (sNat d : ℝ)) hρ

/-- Canonical `Q=1` endpoint using the crude maximum-exponent term envelope.

This is a diagnostic specialization of
`gammaExpectation_pipeline_to_spherical_bound_of_prop73_count_term_canonical_Qone`:
the arbitrary per-defect term envelope is replaced by the class-count bound
`d^{2k} (sqrt s)^{2k}`, and the base assumptions are discharged from the
positive natural dimensions. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_crude_term_canonical_Qone
    {dNat sNat : ℕ} {lam : ℝ}
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatio : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hCount : ∀ Δ ∈
      Finset.range (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 3),
        (wickPermutationDefectCount (aubrunEvenMomentParameter dNat - 1) Δ :
          ℝ) ≤
          aubrunFixedDefectCountEnvelope
            (aubrunEvenMomentParameter dNat - 1) Δ)
    (hEnvelope :
      Finset.sum
          (Finset.range (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 3))
          (fun Δ =>
            aubrunFixedDefectCountEnvelope
              (aubrunEvenMomentParameter dNat - 1) Δ *
              ((dNat : ℝ) ^ (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) *
                Real.sqrt (sNat : ℝ) ^
                  (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)))) ≤
        (2 : ℝ) ^ ((aubrunEvenMomentParameter dNat - 1) + 1) *
          ((dNat : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
            ((aubrunEvenMomentParameter dNat - 1) + 3) *
            (Real.sqrt (sNat : ℝ) +
                aubrunProposition71Q 1
                  ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              ((aubrunEvenMomentParameter dNat - 1) + 1)) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatio (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73CountAndCrudeTermEnvelope
        (Q := aubrunProposition71Q 1) (d := (dNat : ℝ))
        (s := (sNat : ℝ)) (m := aubrunEvenMomentParameter dNat - 1)
        (one_le_natCast_of_pos hdPos)
        (one_le_sqrt_natCast_of_pos hsPos)
        hCount hEnvelope)

/-- Factored scalar version of
`gammaExpectation_pipeline_to_spherical_bound_of_prop73_crude_term_canonical_Qone`.

The crude term envelope is independent of `Δ`, so the scalar hypothesis is
written as `(sum fixedDefectEnvelope) * crudeTermEnvelope`. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_crude_term_factored_canonical_Qone
    {dNat sNat : ℕ} {lam : ℝ}
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatio : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hCount : ∀ Δ ∈
      Finset.range (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 3),
        (wickPermutationDefectCount (aubrunEvenMomentParameter dNat - 1) Δ :
          ℝ) ≤
          aubrunFixedDefectCountEnvelope
            (aubrunEvenMomentParameter dNat - 1) Δ)
    (hEnvelope :
      (Finset.sum
          (Finset.range (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 3))
          (fun Δ =>
            aubrunFixedDefectCountEnvelope
              (aubrunEvenMomentParameter dNat - 1) Δ)) *
          ((dNat : ℝ) ^ (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) *
            Real.sqrt (sNat : ℝ) ^
              (2 * ((aubrunEvenMomentParameter dNat - 1) + 1))) ≤
        (2 : ℝ) ^ ((aubrunEvenMomentParameter dNat - 1) + 1) *
          ((dNat : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
            ((aubrunEvenMomentParameter dNat - 1) + 3) *
            (Real.sqrt (sNat : ℝ) +
                aubrunProposition71Q 1
                  ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              ((aubrunEvenMomentParameter dNat - 1) + 1)) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatio (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73CountAndCrudeTermEnvelope_factored
        (Q := aubrunProposition71Q 1) (d := (dNat : ℝ))
        (s := (sNat : ℝ)) (m := aubrunEvenMomentParameter dNat - 1)
        (one_le_natCast_of_pos hdPos)
        (one_le_sqrt_natCast_of_pos hsPos)
        hCount hEnvelope)

/-- Last-envelope scalar version of the crude Prop 7.3 endpoint.

The finite sum of fixed-defect envelopes is bounded by the number of defect
values times the largest envelope in the range, so the public scalar input is a
single product instead of an explicit finite sum. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_crude_term_last_canonical_Qone
    {dNat sNat : ℕ} {lam : ℝ}
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatio : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hCount : ∀ Δ ∈
      Finset.range (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 3),
        (wickPermutationDefectCount (aubrunEvenMomentParameter dNat - 1) Δ :
          ℝ) ≤
          aubrunFixedDefectCountEnvelope
            (aubrunEvenMomentParameter dNat - 1) Δ)
    (hEnvelope :
      (((2 : ℝ) * (((aubrunEvenMomentParameter dNat - 1 : ℕ) : ℝ) + 1) + 3) *
        ((2 : ℝ) ^ ((aubrunEvenMomentParameter dNat - 1) + 1) *
          aubrunProposition73P ((aubrunEvenMomentParameter dNat - 1) + 1) ^
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 2))) *
          ((dNat : ℝ) ^ (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) *
            Real.sqrt (sNat : ℝ) ^
              (2 * ((aubrunEvenMomentParameter dNat - 1) + 1))) ≤
        (2 : ℝ) ^ ((aubrunEvenMomentParameter dNat - 1) + 1) *
          ((dNat : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
            ((aubrunEvenMomentParameter dNat - 1) + 3) *
            (Real.sqrt (sNat : ℝ) +
                aubrunProposition71Q 1
                  ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              ((aubrunEvenMomentParameter dNat - 1) + 1)) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatio (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73CountAndCrudeTermEnvelope_last
        (Q := aubrunProposition71Q 1) (d := (dNat : ℝ))
        (s := (sNat : ℝ)) (m := aubrunEvenMomentParameter dNat - 1)
        (one_le_natCast_of_pos hdPos)
        (one_le_sqrt_natCast_of_pos hsPos)
        hCount hEnvelope)

/-- Last-envelope crude Prop 7.3 endpoint with the fixed-defect count supplied
directly by Aubrun innovation-fiber data.

Compared with
`gammaExpectation_pipeline_to_spherical_bound_of_prop73_crude_term_last_canonical_Qone`,
this removes the separate fixed-defect count hypothesis from the public
pipeline frontier: the count side is now expressed by per-defect embeddings
into the innovation fibers and their compatible-couple bounds. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_prop73_fiber_data_crude_term_last_canonical_Qone
    {dNat sNat : ℕ} {lam : ℝ}
    {Fiber LeftCouples RightCouples :
      ℕ → Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)) → Type*}
    [∀ Δ I, Fintype (Fiber Δ I)]
    [∀ Δ I, Fintype (LeftCouples Δ I)]
    [∀ Δ I, Fintype (RightCouples Δ I)]
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatio : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (defectEncode : ∀ Δ ∈
      Finset.range (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 3),
        WickPermutationDefectClass (aubrunEvenMomentParameter dNat - 1) Δ ↪
          Sigma (Fiber Δ))
    (encode : ∀ Δ ∈
      Finset.range (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 3),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fiber Δ I ↪ LeftCouples Δ I × RightCouples Δ I)
    (hLeft : ∀ Δ ∈
      Finset.range (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 3),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (LeftCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hRight : ∀ Δ ∈
      Finset.range (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 3),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (RightCouples Δ I) ≤
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              (9 * compatibilityDefect
                ((aubrunEvenMomentParameter dNat - 1) + 1) I))
    (hLarge : ∀ Δ ∈
      Finset.range (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 3),
        ∀ I : Finset (Fin ((aubrunEvenMomentParameter dNat - 1) + 1)),
          Fintype.card (Fiber Δ I) ≠ 0 →
            ((aubrunEvenMomentParameter dNat - 1) + 1) ≤
              2 * I.card + 2 * Δ)
    (hEnvelope :
      (((2 : ℝ) * (((aubrunEvenMomentParameter dNat - 1 : ℕ) : ℝ) + 1) + 3) *
        ((2 : ℝ) ^ ((aubrunEvenMomentParameter dNat - 1) + 1) *
          aubrunProposition73P ((aubrunEvenMomentParameter dNat - 1) + 1) ^
            (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 2))) *
          ((dNat : ℝ) ^ (2 * ((aubrunEvenMomentParameter dNat - 1) + 1)) *
            Real.sqrt (sNat : ℝ) ^
              (2 * ((aubrunEvenMomentParameter dNat - 1) + 1))) ≤
        (2 : ℝ) ^ ((aubrunEvenMomentParameter dNat - 1) + 1) *
          ((dNat : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
            ((aubrunEvenMomentParameter dNat - 1) + 3) *
            (Real.sqrt (sNat : ℝ) +
                aubrunProposition71Q 1
                  ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              ((aubrunEvenMomentParameter dNat - 1) + 1)) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatio (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73FiberDataAndCrudeTermEnvelope_last
        (Q := aubrunProposition71Q 1) (d := (dNat : ℝ))
        (s := (sNat : ℝ)) (m := aubrunEvenMomentParameter dNat - 1)
        (one_le_natCast_of_pos hdPos)
        (one_le_sqrt_natCast_of_pos hsPos)
        defectEncode encode hLeft hRight hLarge hEnvelope)

/-- Canonical explicit-`Q` profile-count endpoint with the paper-facing
constant fixed to `C0 = 1`.

This removes the scalar nonnegativity hypothesis from the public frontier.  The
remaining theorem-strength input is still exactly the displayed finite
profile-count inequality, now with `Q(k)=k(2k)^36`. -/
theorem gammaExpectation_pipeline_to_spherical_bound_of_profile_count_sum_canonical_Qone
    {dNat sNat : ℕ} {lam : ℝ}
    (hdPos : 0 < (dNat : ℝ))
    (hsPos : 0 < (sNat : ℝ))
    (hlam : 0 < lam)
    (hRatio : lam * (dNat : ℝ) ^ 2 ≤ (sNat : ℝ))
    (hProfile :
      Finset.sum
          (Finset.range (2 * ((aubrunEvenMomentParameter dNat - 1) + 1) + 1))
          (fun l1 =>
            Finset.sum
              (Finset.range ((aubrunEvenMomentParameter dNat - 1) + 2))
              (fun l2 =>
                (wickRelationProfileCount
                    (m := aubrunEvenMomentParameter dNat - 1) l1 l2 : ℝ) *
                  (dNat : ℝ) ^ l1 * Real.sqrt (sNat : ℝ) ^ (2 * l2))) ≤
        (2 : ℝ) ^ ((aubrunEvenMomentParameter dNat - 1) + 1) *
          ((dNat : ℝ) +
              aubrunProposition71Q 1
                ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
            ((aubrunEvenMomentParameter dNat - 1) + 3) *
            (Real.sqrt (sNat : ℝ) +
                aubrunProposition71Q 1
                  ((aubrunEvenMomentParameter dNat - 1) + 1)) ^
              ((aubrunEvenMomentParameter dNat - 1) + 1)) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      aubrunOffDiagonalExpectationEnvelope
        (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
        (aubrunEvenMomentParameter dNat) ∧
    gaussianWishartGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
        (2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat) ∧
    gaussianQuadraticGammaLiftMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      gaussianQuadraticRadialMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) *
        (((2 * Real.log 2 + 4 / lam) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
              (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2) ∧
    sphericalGammaOpNormMean
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) ≤
      ((2 * Real.log 2 + 4 / lam) +
          aubrunOffDiagonalExpectationEnvelope
            (aubrunProposition71Q 1) (dNat : ℝ) (sNat : ℝ)
            (aubrunEvenMomentParameter dNat)) / (dNat : ℝ) ^ 2 := by
  exact
    gammaExpectation_pipeline_to_spherical_bound_of_profile_count_sum_canonical_explicitQ
      (dNat := dNat) (sNat := sNat) (C0 := 1) (lam := lam)
      hdPos hsPos hlam hRatio (by norm_num) hProfile

end AppendixB
end PptFactorization
