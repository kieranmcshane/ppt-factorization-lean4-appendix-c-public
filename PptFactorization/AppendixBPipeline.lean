import PptFactorization.AppendixBAubrunProposition71
import PptFactorization.AppendixBFinal

/-!
# Appendix B: canonical proof pipeline

This file is deliberately a wiring file.  It records the clean downstream
composition

`moments → off-diagonal expectation → diagonal gamma → spherical normalization
→ localized Levy → conditional assembly endpoint`.

It does not manufacture the still-missing analytic cores.  The Aubrun moment
extraction/counting estimate, the diagonal gamma expectation estimate, and the
global/local Levy inputs remain explicit hypotheses at the exact points where
the paper uses them.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal

noncomputable section

namespace PptFactorization
namespace AppendixB

open RandomMatrixModel GaussianModel HighProbabilityBounds
open TraceWickExpansion

variable {p q σ : Type*}
variable [Fintype p] [Fintype q] [Fintype σ]
variable [DecidableEq p] [DecidableEq q]

/-! ## Diagonal/off-diagonal split at operator norm level -/

/-- Gaussian mean of the diagonal part of the concrete normalized
partially-transposed Wishart matrix. -/
def gaussianWishartGammaDiagonalOpNormMean : ℝ :=
  ∫ ω : Ω p q σ,
    opNorm
      (diagonalPart
        (wishartGamma (p := p) (q := q) (σ := σ)
          (gaussianMatrix p q σ ω)))
      ∂gaussianMeasure p q σ

/-- Pointwise triangle inequality for the paper split
`W^Γ = diag(W^Γ) + Z`. -/
theorem wishartGamma_opNorm_le_diagonal_add_offDiagonal
    (G : SampleMatrix p q σ) :
    opNorm (wishartGamma (p := p) (q := q) (σ := σ) G) ≤
      opNorm
        (diagonalPart
          (wishartGamma (p := p) (q := q) (σ := σ) G)) +
        opNorm (wishartGammaOffDiagonal (p := p) (q := q) (σ := σ) G) := by
  classical
  let A : BipMatrix p q :=
    diagonalPart (wishartGamma (p := p) (q := q) (σ := σ) G)
  let B : BipMatrix p q :=
    wishartGammaOffDiagonal (p := p) (q := q) (σ := σ) G
  have hSplit :
      wishartGamma (p := p) (q := q) (σ := σ) G = A + B := by
    simpa [A, B] using
      wishartGamma_eq_diagonalPart_add_offDiagonal
        (p := p) (q := q) (σ := σ) G
  have hMapAdd :
      Matrix.toEuclideanCLM (n := BipIndex p q) (𝕜 := ℂ) (A + B) =
        Matrix.toEuclideanCLM (n := BipIndex p q) (𝕜 := ℂ) A +
          Matrix.toEuclideanCLM (n := BipIndex p q) (𝕜 := ℂ) B := by
    exact map_add (Matrix.toEuclideanCLM (n := BipIndex p q) (𝕜 := ℂ)) A B
  calc
    opNorm (wishartGamma (p := p) (q := q) (σ := σ) G)
        = ‖Matrix.toEuclideanCLM (n := BipIndex p q) (𝕜 := ℂ)
            (wishartGamma (p := p) (q := q) (σ := σ) G)‖ := rfl
    _ = ‖Matrix.toEuclideanCLM (n := BipIndex p q) (𝕜 := ℂ) (A + B)‖ := by
            rw [hSplit]
    _ = ‖Matrix.toEuclideanCLM (n := BipIndex p q) (𝕜 := ℂ) A +
          Matrix.toEuclideanCLM (n := BipIndex p q) (𝕜 := ℂ) B‖ := by
            rw [hMapAdd]
    _ ≤ opNorm A + opNorm B := by
            simpa [opNorm] using
              norm_add_le
                (Matrix.toEuclideanCLM (n := BipIndex p q) (𝕜 := ℂ)
                  A)
                (Matrix.toEuclideanCLM (n := BipIndex p q) (𝕜 := ℂ)
                  B)

/-- Expectation-level diagonal/off-diagonal operator-norm split.  The
integrability assumptions are exactly what is needed to pass the pointwise
triangle inequality under the Bochner integral. -/
theorem gaussianWishartGammaOpNormMean_le_diagonal_add_offDiagonal_mean
    [DecidableEq σ]
    (hFull :
      Integrable
        (fun ω : Ω p q σ =>
          opNorm
            (wishartGamma (p := p) (q := q) (σ := σ)
              (gaussianMatrix p q σ ω)))
        (gaussianMeasure p q σ))
    (hDiag :
      Integrable
        (fun ω : Ω p q σ =>
          opNorm
            (diagonalPart
              (wishartGamma (p := p) (q := q) (σ := σ)
                (gaussianMatrix p q σ ω))))
        (gaussianMeasure p q σ))
    (hOff :
      Integrable
        (fun ω : Ω p q σ =>
          opNorm
            (wishartGammaOffDiagonal (p := p) (q := q) (σ := σ)
              (gaussianMatrix p q σ ω)))
        (gaussianMeasure p q σ)) :
    gaussianWishartGammaOpNormMean (p := p) (q := q) (σ := σ) ≤
      gaussianWishartGammaDiagonalOpNormMean (p := p) (q := q) (σ := σ) +
        gaussianWishartGammaOffDiagonalOpNormMean (p := p) (q := q) (σ := σ) := by
  classical
  let μ := gaussianMeasure p q σ
  let full : Ω p q σ → ℝ := fun ω =>
    opNorm
      (wishartGamma (p := p) (q := q) (σ := σ)
        (gaussianMatrix p q σ ω))
  let diag : Ω p q σ → ℝ := fun ω =>
    opNorm
      (diagonalPart
        (wishartGamma (p := p) (q := q) (σ := σ)
          (gaussianMatrix p q σ ω)))
  let off : Ω p q σ → ℝ := fun ω =>
    opNorm
      (wishartGammaOffDiagonal (p := p) (q := q) (σ := σ)
        (gaussianMatrix p q σ ω))
  have hMono :
      ∫ ω, full ω ∂μ ≤ ∫ ω, diag ω + off ω ∂μ := by
    exact integral_mono hFull (hDiag.add hOff) fun ω =>
      wishartGamma_opNorm_le_diagonal_add_offDiagonal
        (p := p) (q := q) (σ := σ) (gaussianMatrix p q σ ω)
  calc
    gaussianWishartGammaOpNormMean (p := p) (q := q) (σ := σ)
        = ∫ ω, full ω ∂μ := by
            rfl
    _ ≤ ∫ ω, diag ω + off ω ∂μ := hMono
    _ = (∫ ω, diag ω ∂μ) + ∫ ω, off ω ∂μ := by
            rw [integral_add hDiag hOff]
    _ =
        gaussianWishartGammaDiagonalOpNormMean (p := p) (q := q) (σ := σ) +
          gaussianWishartGammaOffDiagonalOpNormMean
            (p := p) (q := q) (σ := σ) := by
            rfl

/-! ## Moments to off-diagonal expectation -/

/-- The moment side of the pipeline: once the Aubrun high-moment extraction and
the scalar envelope estimate have been proved, the off-diagonal expectation
bound follows. -/
theorem offDiagonalExpectation_from_moment_pipeline
    [DecidableEq σ] {Q : ℕ → ℝ} {dNat : ℕ} {d s COff : ℝ}
    (H :
      AubrunOffDiagonalExpectationDerivation
        (p := p) (q := q) (σ := σ) Q dNat d s COff) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := p) (q := q) (σ := σ) ≤ COff :=
  H.bound

/-- Diagonal plus off-diagonal expectation bound for the full
partially-transposed Wishart operator norm. -/
theorem wishartGammaExpectation_from_diagonal_and_offDiagonal
    [DecidableEq σ] {Q : ℕ → ℝ} {dNat : ℕ} {d s CDiag COff : ℝ}
    (H :
      AubrunOffDiagonalExpectationDerivation
        (p := p) (q := q) (σ := σ) Q dNat d s COff)
    (hFull :
      Integrable
        (fun ω : Ω p q σ =>
          opNorm
            (wishartGamma (p := p) (q := q) (σ := σ)
              (gaussianMatrix p q σ ω)))
        (gaussianMeasure p q σ))
    (hDiagInt :
      Integrable
        (fun ω : Ω p q σ =>
          opNorm
            (diagonalPart
              (wishartGamma (p := p) (q := q) (σ := σ)
                (gaussianMatrix p q σ ω))))
        (gaussianMeasure p q σ))
    (hOffInt :
      Integrable
        (fun ω : Ω p q σ =>
          opNorm
            (wishartGammaOffDiagonal (p := p) (q := q) (σ := σ)
              (gaussianMatrix p q σ ω)))
        (gaussianMeasure p q σ))
    (hDiag :
      gaussianWishartGammaDiagonalOpNormMean (p := p) (q := q) (σ := σ) ≤
        CDiag) :
    gaussianWishartGammaOpNormMean (p := p) (q := q) (σ := σ) ≤
      CDiag + COff := by
  have hSplit :=
    gaussianWishartGammaOpNormMean_le_diagonal_add_offDiagonal_mean
      (p := p) (q := q) (σ := σ) hFull hDiagInt hOffInt
  have hOff :=
    offDiagonalExpectation_from_moment_pipeline
      (p := p) (q := q) (σ := σ) H
  calc
    gaussianWishartGammaOpNormMean (p := p) (q := q) (σ := σ)
        ≤ gaussianWishartGammaDiagonalOpNormMean
            (p := p) (q := q) (σ := σ) +
          gaussianWishartGammaOffDiagonalOpNormMean
            (p := p) (q := q) (σ := σ) := hSplit
    _ ≤ CDiag + COff := add_le_add hDiag hOff

/-! ## Wishart expectation to spherical normalization -/

/-- Convert a concrete Gaussian Wishart-Gamma expectation bound into the
quadratic Gaussian lift bound used by the spherical normalization step. -/
theorem gaussianQuadraticGammaLiftMean_le_of_wishartGamma_mean_bound
    {C d : ℝ}
    (hd : 0 < d)
    (hs : 1 ≤ sampleDimension σ)
    (hDim : bipartiteDimension p q = d ^ 2)
    (hWishartMean :
      gaussianWishartGammaOpNormMean (p := p) (q := q) (σ := σ) ≤ C) :
    gaussianQuadraticGammaLiftMean (p := p) (q := q) (σ := σ) ≤
      gaussianQuadraticRadialMean (p := p) (q := q) (σ := σ) *
        (C / d ^ 2) := by
  have hsCard : Fintype.card σ ≠ 0 := by
    intro hzero
    have hbad : (1 : ℝ) ≤ 0 := by
      simpa [sampleDimension, hzero] using hs
    norm_num at hbad
  calc
    gaussianQuadraticGammaLiftMean (p := p) (q := q) (σ := σ)
        = sampleDimension σ *
            gaussianWishartGammaOpNormMean (p := p) (q := q) (σ := σ) := by
            exact
              gaussianQuadraticGammaLiftMean_eq_sampleDimension_mul_wishartGammaMean
                (p := p) (q := q) (σ := σ) hsCard
    _ ≤ sampleDimension σ * C := by
            exact mul_le_mul_of_nonneg_left hWishartMean sampleDimension_nonneg
    _ = gaussianQuadraticRadialMean (p := p) (q := q) (σ := σ) *
          (C / d ^ 2) := by
            rw [gaussianQuadraticRadialMean_eq (p := p) (q := q) (σ := σ), hDim]
            field_simp [pow_ne_zero 2 (ne_of_gt hd)]

/-- The expectation pipeline through spherical normalization. -/
theorem gammaExpectation_pipeline_to_spherical_bound
    [DecidableEq σ] {Q : ℕ → ℝ} {dNat : ℕ} {d s CDiag COff : ℝ}
    (H :
      AubrunOffDiagonalExpectationDerivation
        (p := p) (q := q) (σ := σ) Q dNat d s COff)
    (hFull :
      Integrable
        (fun ω : Ω p q σ =>
          opNorm
            (wishartGamma (p := p) (q := q) (σ := σ)
              (gaussianMatrix p q σ ω)))
        (gaussianMeasure p q σ))
    (hDiagInt :
      Integrable
        (fun ω : Ω p q σ =>
          opNorm
            (diagonalPart
              (wishartGamma (p := p) (q := q) (σ := σ)
                (gaussianMatrix p q σ ω))))
        (gaussianMeasure p q σ))
    (hOffInt :
      Integrable
        (fun ω : Ω p q σ =>
          opNorm
            (wishartGammaOffDiagonal (p := p) (q := q) (σ := σ)
              (gaussianMatrix p q σ ω)))
        (gaussianMeasure p q σ))
    (hDiag :
      gaussianWishartGammaDiagonalOpNormMean (p := p) (q := q) (σ := σ) ≤
        CDiag)
    (hIndepR2 :
      gaussianRadiusSq (p := p) (q := q) (σ := σ) ⟂ᵢ[gaussianMeasure p q σ]
        gaussianDirection (p := p) (q := q) (σ := σ))
    (hQuadraticRadialPos :
      0 < gaussianQuadraticRadialMean (p := p) (q := q) (σ := σ))
    (hd : 0 < d)
    (hs : 1 ≤ sampleDimension σ)
    (hDim : bipartiteDimension p q = d ^ 2) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := p) (q := q) (σ := σ) ≤ COff ∧
    gaussianWishartGammaOpNormMean (p := p) (q := q) (σ := σ) ≤
        CDiag + COff ∧
    gaussianQuadraticGammaLiftMean (p := p) (q := q) (σ := σ) ≤
      gaussianQuadraticRadialMean (p := p) (q := q) (σ := σ) *
        ((CDiag + COff) / d ^ 2) ∧
    sphericalGammaOpNormMean (p := p) (q := q) (σ := σ) ≤
      (CDiag + COff) / d ^ 2 := by
  have hOff :=
    offDiagonalExpectation_from_moment_pipeline
      (p := p) (q := q) (σ := σ) H
  have hWishart :=
    wishartGammaExpectation_from_diagonal_and_offDiagonal
      (p := p) (q := q) (σ := σ)
      (Q := Q) (dNat := dNat) (d := d) (s := s)
      (CDiag := CDiag) (COff := COff)
      H hFull hDiagInt hOffInt hDiag
  have hLift :=
    gaussianQuadraticGammaLiftMean_le_of_wishartGamma_mean_bound
      (p := p) (q := q) (σ := σ)
      (C := CDiag + COff) (d := d) hd hs hDim hWishart
  have hSphere :=
    sphericalGammaOpNormMean_le_of_quadratic_lift_bound
      (p := p) (q := q) (σ := σ)
      (C := CDiag + COff) (d := d)
      hIndepR2 hQuadraticRadialPos hLift
  exact ⟨hOff, hWishart, hLift, hSphere⟩

/-! ## Full pipeline to the current final Appendix B theorem -/

/-- Canonical downstream assembly of the presently formalized Appendix B
pipeline.

The theorem starts from the two genuine expectation cores still used by the
paper, namely the Aubrun off-diagonal moment pipeline and the diagonal gamma
expectation estimate, then wires them through spherical normalization and the
localized Levy theorem already present in the repository. -/
theorem appendixB_pipeline_to_final_theorem
    [DecidableEq σ]
    {Q : ℕ → ℝ} {dNat : ℕ}
    {f : SampleMatrix p q σ → ℝ}
    {gaussianMean radialMean sphericalMean C1 CDiag COff : ℝ}
    {mean median range bad a b C cDim d eps momentParameter s : ℝ}
    {r : ℕ}
    (H :
      AubrunOffDiagonalExpectationDerivation
        (p := p) (q := q) (σ := σ) Q dNat d s COff)
    (hFull :
      Integrable
        (fun ω : Ω p q σ =>
          opNorm
            (wishartGamma (p := p) (q := q) (σ := σ)
              (gaussianMatrix p q σ ω)))
        (gaussianMeasure p q σ))
    (hDiagInt :
      Integrable
        (fun ω : Ω p q σ =>
          opNorm
            (diagonalPart
              (wishartGamma (p := p) (q := q) (σ := σ)
                (gaussianMatrix p q σ ω))))
        (gaussianMeasure p q σ))
    (hOffInt :
      Integrable
        (fun ω : Ω p q σ =>
          opNorm
            (wishartGammaOffDiagonal (p := p) (q := q) (σ := σ)
              (gaussianMatrix p q σ ω)))
        (gaussianMeasure p q σ))
    (hDiag :
      gaussianWishartGammaDiagonalOpNormMean (p := p) (q := q) (σ := σ) ≤
        CDiag)
    (hIndepR2 :
      gaussianRadiusSq (p := p) (q := q) (σ := σ) ⟂ᵢ[gaussianMeasure p q σ]
        gaussianDirection (p := p) (q := q) (σ := σ))
    (hRadialMean : 0 < radialMean)
    (hSampleFactor : gaussianMean = radialMean * sphericalMean)
    (hSampleBound : gaussianMean ≤ radialMean * (C1 / d))
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
    sphericalGammaOpNormMean (p := p) (q := q) (σ := σ) ≤
      (CDiag + COff) / d ^ 2 ∧
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
  have hsPos : 0 < sampleDimension σ := lt_of_lt_of_le zero_lt_one hs
  have hBipPos : 0 < bipartiteDimension p q := by
    rw [hDim]
    positivity
  have hQuadraticRadialPos :
      0 < gaussianQuadraticRadialMean (p := p) (q := q) (σ := σ) :=
    gaussianQuadraticRadialMean_pos (p := p) (q := q) (σ := σ) hBipPos hsPos
  have hGammaPipeline :=
    gammaExpectation_pipeline_to_spherical_bound
      (p := p) (q := q) (σ := σ)
      (Q := Q) (dNat := dNat) (d := d) (s := s)
      (CDiag := CDiag) (COff := COff)
      H hFull hDiagInt hOffInt hDiag hIndepR2
      hQuadraticRadialPos hd hs hDim
  have hGammaFactor :
      gaussianQuadraticGammaLiftMean (p := p) (q := q) (σ := σ) =
        gaussianQuadraticRadialMean (p := p) (q := q) (σ := σ) *
          sphericalGammaOpNormMean (p := p) (q := q) (σ := σ) :=
    gaussianQuadraticGammaLiftMean_factorization_of_indep
      (p := p) (q := q) (σ := σ) hIndepR2
  exact
    final_appendixB_assembly_no_structure_inputs
      (p := p) (q := q) (σ := σ)
      (f := f)
      (gaussianMean := gaussianMean)
      (radialMean := radialMean)
      (sphericalMean := sphericalMean)
      (wishartGammaMean :=
        gaussianQuadraticGammaLiftMean (p := p) (q := q) (σ := σ))
      (radialSecondMean :=
        gaussianQuadraticRadialMean (p := p) (q := q) (σ := σ))
      (sphericalGammaMean :=
        sphericalGammaOpNormMean (p := p) (q := q) (σ := σ))
      (C1 := C1) (C2 := CDiag + COff)
      (mean := mean) (median := median) (range := range)
      (bad := bad) (a := a) (b := b) (C := C)
      (cDim := cDim) (d := d) (eps := eps)
      (momentParameter := momentParameter) (r := r)
      hRadialMean hSampleFactor hSampleBound
      hQuadraticRadialPos hGammaFactor hGammaPipeline.2.2.1
      hd hs hDim hLarge hC hmoment hScalePos
      hmean hf hRange hRangeNonneg hL hn hSmall hLip hMedian
      hGlobalLevy hBad hGood

end AppendixB
end PptFactorization
