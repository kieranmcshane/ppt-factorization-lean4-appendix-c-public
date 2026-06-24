import PptFactorization.AppendixBPipeline

/-!
# Appendix B: Gaussian integrability inputs

This file closes the Gaussian integrability assumptions used by the Appendix B
pipeline.  The proof is intentionally elementary: all three observables are
dominated by the Gaussian mass `T = ‖G‖₂²`, up to the harmless factor `2` for
the off-diagonal part.
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

omit [Fintype σ] in
/-- The custom bipartite operator norm is continuous. -/
theorem continuous_bipOpNorm :
    Continuous (fun A : BipMatrix p q => opNorm A) := by
  have hToEuclidean :
      Continuous (fun A : BipMatrix p q =>
        Matrix.toEuclideanCLM (n := BipIndex p q) (𝕜 := ℂ) A) := by
    exact
      (Matrix.toEuclideanCLM (n := BipIndex p q) (𝕜 := ℂ)).toAlgEquiv.toLinearMap
        |>.continuous_of_finiteDimensional
  unfold opNorm
  exact continuous_norm.comp hToEuclidean

omit [Fintype σ] in
/-- The diagonal projection as a complex-linear map. -/
def diagonalPartLinearMap : BipMatrix p q →ₗ[ℂ] BipMatrix p q where
  toFun := diagonalPart
  map_add' := by
    intro A B
    ext i j
    by_cases h : i = j <;> simp [h]
  map_smul' := by
    intro c A
    ext i j
    by_cases h : i = j <;> simp [h]

omit [Fintype σ] in
/-- The diagonal projection is continuous. -/
theorem continuous_diagonalPart :
    Continuous (fun A : BipMatrix p q => diagonalPart A) := by
  simpa [diagonalPartLinearMap] using
    (diagonalPartLinearMap (p := p) (q := q)).continuous_of_finiteDimensional

omit [DecidableEq p] [DecidableEq q] in
/-- The concrete `G ↦ W^Γ(G)` map is continuous. -/
theorem continuous_wishartGamma_sample :
    Continuous (fun G : SampleMatrix p q σ =>
      wishartGamma (p := p) (q := q) (σ := σ) G) := by
  have hDensity :
      Continuous (fun G : SampleMatrix p q σ => densityMatrix G) := by
    unfold densityMatrix
    fun_prop
  have hWishart :
      Continuous (fun G : SampleMatrix p q σ =>
        ((Fintype.card σ : ℂ)⁻¹) • densityMatrix G) :=
    hDensity.const_smul _
  simpa [RandomMatrixModel.wishartGamma, RandomMatrixModel.wishart] using
    (continuous_gamma (p := p) (q := q)).comp hWishart

/-- Continuity of the full Wishart-Gamma operator-norm observable on samples. -/
theorem continuous_wishartGamma_opNorm_sample :
    Continuous (fun G : SampleMatrix p q σ =>
      opNorm (wishartGamma (p := p) (q := q) (σ := σ) G)) :=
  continuous_bipOpNorm.comp
    (continuous_wishartGamma_sample (p := p) (q := q) (σ := σ))

/-- Continuity of the diagonal Wishart-Gamma operator-norm observable. -/
theorem continuous_wishartGamma_diagonal_opNorm_sample :
    Continuous (fun G : SampleMatrix p q σ =>
      opNorm
        (diagonalPart
          (wishartGamma (p := p) (q := q) (σ := σ) G))) :=
  continuous_bipOpNorm.comp
    (continuous_diagonalPart.comp
      (continuous_wishartGamma_sample (p := p) (q := q) (σ := σ)))

/-- Continuity of the off-diagonal Wishart-Gamma operator-norm observable. -/
theorem continuous_wishartGamma_offDiagonal_opNorm_sample :
    Continuous (fun G : SampleMatrix p q σ =>
      opNorm
        (wishartGammaOffDiagonal (p := p) (q := q) (σ := σ) G)) := by
  simpa [wishartGammaOffDiagonal] using
    continuous_bipOpNorm.comp
      ((continuous_offDiagonal (p := p) (q := q)).comp
        (continuous_wishartGamma_sample (p := p) (q := q) (σ := σ)))

omit [Fintype σ] in
/-- The Frobenius norm of the diagonal projection is bounded by the Frobenius
norm of the original matrix. -/
theorem diagonalPart_frobeniusNorm_le (A : BipMatrix p q) :
    frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) (diagonalPart A) ≤
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) A := by
  classical
  have hDiagSq :
      ‖diagonalPart A‖ ^ 2 = ∑ i : BipIndex p q, ‖A i i‖ ^ 2 := by
    rw [matrix_frobenius_norm_sq_eq_re_trace_conjTranspose_mul_self,
      matrix_re_trace_conjTranspose_mul_self_eq_sum_norm_sq]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.sum_eq_single i]
    · simp [diagonalPart]
    · intro j _ hji
      have hij : i ≠ j := fun h => hji h.symm
      simp [diagonalPart, hij]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  have hFullSq :
      ‖A‖ ^ 2 = ∑ i : BipIndex p q, ∑ j : BipIndex p q, ‖A i j‖ ^ 2 := by
    rw [matrix_frobenius_norm_sq_eq_re_trace_conjTranspose_mul_self,
      matrix_re_trace_conjTranspose_mul_self_eq_sum_norm_sq]
  have hsum :
      (∑ i : BipIndex p q, ‖A i i‖ ^ 2) ≤
        ∑ i : BipIndex p q, ∑ j : BipIndex p q, ‖A i j‖ ^ 2 := by
    refine Finset.sum_le_sum ?_
    intro i _
    exact Finset.single_le_sum
      (fun j _ => sq_nonneg ‖A i j‖)
      (Finset.mem_univ i)
  have hsq : ‖diagonalPart A‖ ^ 2 ≤ ‖A‖ ^ 2 := by
    rw [hDiagSq, hFullSq]
    exact hsum
  exact le_of_sq_le_sq hsq (norm_nonneg A)

omit [Fintype σ] in
/-- Operator norm of the diagonal projection is bounded by the original
Frobenius norm. -/
theorem diagonalPart_opNorm_le_frobeniusNorm (A : BipMatrix p q) :
    opNorm (diagonalPart A) ≤
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) A := by
  calc
    opNorm (diagonalPart A)
        ≤ frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
            (diagonalPart A) :=
          opNorm_le_frobeniusNorm (p := p) (q := q) (A := diagonalPart A)
    _ ≤ frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) A :=
          diagonalPart_frobeniusNorm_le (p := p) (q := q) A

/-- Frobenius domination for the normalized partially transposed Wishart
matrix. -/
theorem wishartGamma_frobeniusNorm_le_gaussianMass (ω : Ω p q σ) :
    frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
        (wishartGamma (p := p) (q := q) (σ := σ)
          (gaussianMatrix p q σ ω)) ≤
      gaussianMass p q σ ω := by
  let G : SampleMatrix p q σ := gaussianMatrix p q σ ω
  calc
    frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
        (wishartGamma (p := p) (q := q) (σ := σ) G)
        = ‖((Fintype.card σ : ℂ)⁻¹) •
            rawWishartGamma (p := p) (q := q) (σ := σ) G‖ := by
            simp [frobeniusNorm, wishartGamma_eq_card_inv_smul_rawWishartGamma]
    _ = ‖((Fintype.card σ : ℂ)⁻¹)‖ *
          frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
            (rawWishartGamma (p := p) (q := q) (σ := σ) G) := by
            simp [frobeniusNorm, norm_smul]
    _ ≤ frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
          (rawWishartGamma (p := p) (q := q) (σ := σ) G) := by
            exact mul_le_of_le_one_left (norm_nonneg _)
              (sampleDimension_inv_norm_le_one (σ := σ))
    _ = frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
          (rawWishart (p := p) (q := q) (σ := σ) G) := by
            simp [rawWishartGamma]
    _ ≤ gaussianMass p q σ ω := by
      have hmul :
          ‖G * Gᴴ‖ ≤ ‖G‖ * ‖Gᴴ‖ := Matrix.frobenius_norm_mul G Gᴴ
      have hstar : ‖Gᴴ‖ = ‖G‖ := Matrix.frobenius_norm_conjTranspose G
      calc
        frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
            (rawWishart (p := p) (q := q) (σ := σ) G) = ‖G * Gᴴ‖ := by
              simp [frobeniusNorm, rawWishart, RandomMatrixModel.densityMatrix]
        _ ≤ ‖G‖ * ‖Gᴴ‖ := hmul
        _ = ‖G‖ ^ 2 := by rw [hstar]; ring
        _ = gaussianMass p q σ ω := by
              simp [G, gaussianMass, frobeniusMass, frobeniusNorm]

/-- Pointwise domination of the diagonal part by the Gaussian mass. -/
theorem wishartGamma_diagonal_opNorm_le_gaussianMass (ω : Ω p q σ) :
    opNorm
        (diagonalPart
          (wishartGamma (p := p) (q := q) (σ := σ)
            (gaussianMatrix p q σ ω))) ≤
      gaussianMass p q σ ω := by
  calc
    opNorm
        (diagonalPart
          (wishartGamma (p := p) (q := q) (σ := σ)
            (gaussianMatrix p q σ ω)))
        ≤ frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
            (wishartGamma (p := p) (q := q) (σ := σ)
              (gaussianMatrix p q σ ω)) :=
          diagonalPart_opNorm_le_frobeniusNorm (p := p) (q := q) _
    _ ≤ gaussianMass p q σ ω :=
          wishartGamma_frobeniusNorm_le_gaussianMass
            (p := p) (q := q) (σ := σ) ω

/-- Pointwise domination of the off-diagonal part by twice the Gaussian mass. -/
theorem wishartGamma_offDiagonal_opNorm_le_two_mul_gaussianMass (ω : Ω p q σ) :
    opNorm
        (wishartGammaOffDiagonal (p := p) (q := q) (σ := σ)
          (gaussianMatrix p q σ ω)) ≤
      2 * gaussianMass p q σ ω := by
  let A : BipMatrix p q :=
    wishartGamma (p := p) (q := q) (σ := σ) (gaussianMatrix p q σ ω)
  let B : BipMatrix p q := diagonalPart A
  have hMapSub :
      Matrix.toEuclideanCLM (n := BipIndex p q) (𝕜 := ℂ) (A - B) =
        Matrix.toEuclideanCLM (n := BipIndex p q) (𝕜 := ℂ) A -
          Matrix.toEuclideanCLM (n := BipIndex p q) (𝕜 := ℂ) B := by
    exact map_sub (Matrix.toEuclideanCLM (n := BipIndex p q) (𝕜 := ℂ)) A B
  have hoff :
      wishartGammaOffDiagonal (p := p) (q := q) (σ := σ)
          (gaussianMatrix p q σ ω) = A - B := by
    rfl
  calc
    opNorm
        (wishartGammaOffDiagonal (p := p) (q := q) (σ := σ)
          (gaussianMatrix p q σ ω))
        = ‖Matrix.toEuclideanCLM (n := BipIndex p q) (𝕜 := ℂ) (A - B)‖ := by
            rw [hoff]
            rfl
    _ = ‖Matrix.toEuclideanCLM (n := BipIndex p q) (𝕜 := ℂ) A -
          Matrix.toEuclideanCLM (n := BipIndex p q) (𝕜 := ℂ) B‖ := by
            rw [hMapSub]
    _ ≤ opNorm A + opNorm B := by
            simpa [opNorm] using
              norm_sub_le
                (Matrix.toEuclideanCLM (n := BipIndex p q) (𝕜 := ℂ) A)
                (Matrix.toEuclideanCLM (n := BipIndex p q) (𝕜 := ℂ) B)
    _ ≤ gaussianMass p q σ ω + gaussianMass p q σ ω := by
            exact add_le_add
              (by
                simpa [A, wishartGammaOpNorm_apply] using
                  wishartGammaOpNorm_le_gaussianMass
                    (p := p) (q := q) (σ := σ) ω)
              (by
                simpa [A, B] using
                  wishartGamma_diagonal_opNorm_le_gaussianMass
                    (p := p) (q := q) (σ := σ) ω)
    _ = 2 * gaussianMass p q σ ω := by ring

/-- The full Wishart-Gamma operator-norm observable is integrable. -/
theorem gaussianWishartGammaOpNorm_integrable :
    Integrable
      (fun ω : Ω p q σ =>
        opNorm
          (wishartGamma (p := p) (q := q) (σ := σ)
            (gaussianMatrix p q σ ω)))
      (gaussianMeasure p q σ) := by
  have hGcont : Continuous (fun ω : Ω p q σ => gaussianMatrix p q σ ω) := by
    unfold gaussianMatrix GaussianModel.gaussianSampleMatrix
      GaussianModel.sampleMatrixOfRealCoordinates
    exact continuous_pi fun _ => continuous_pi fun _ => by fun_prop
  have hmeas :
      AEStronglyMeasurable
        (fun ω : Ω p q σ =>
          opNorm
            (wishartGamma (p := p) (q := q) (σ := σ)
              (gaussianMatrix p q σ ω)))
        (gaussianMeasure p q σ) :=
    (continuous_wishartGamma_opNorm_sample (p := p) (q := q) (σ := σ)).comp_aestronglyMeasurable
      hGcont.aestronglyMeasurable
  refine (gaussianMass_integrable (p := p) (q := q) (σ := σ)).mono' hmeas ?_
  refine Filter.Eventually.of_forall ?_
  intro ω
  simpa [wishartGammaOpNorm_apply] using
    wishartGammaOpNorm_le_gaussianMass (p := p) (q := q) (σ := σ) ω

/-- The diagonal Wishart-Gamma operator-norm observable is integrable. -/
theorem gaussianWishartGammaDiagonalOpNorm_integrable :
    Integrable
      (fun ω : Ω p q σ =>
        opNorm
          (diagonalPart
            (wishartGamma (p := p) (q := q) (σ := σ)
              (gaussianMatrix p q σ ω))))
      (gaussianMeasure p q σ) := by
  have hGcont : Continuous (fun ω : Ω p q σ => gaussianMatrix p q σ ω) := by
    unfold gaussianMatrix GaussianModel.gaussianSampleMatrix
      GaussianModel.sampleMatrixOfRealCoordinates
    exact continuous_pi fun _ => continuous_pi fun _ => by fun_prop
  have hmeas :
      AEStronglyMeasurable
        (fun ω : Ω p q σ =>
          opNorm
            (diagonalPart
              (wishartGamma (p := p) (q := q) (σ := σ)
                (gaussianMatrix p q σ ω))))
        (gaussianMeasure p q σ) :=
    (continuous_wishartGamma_diagonal_opNorm_sample
        (p := p) (q := q) (σ := σ)).comp_aestronglyMeasurable
      hGcont.aestronglyMeasurable
  refine (gaussianMass_integrable (p := p) (q := q) (σ := σ)).mono' hmeas ?_
  refine Filter.Eventually.of_forall ?_
  intro ω
  rw [Real.norm_of_nonneg (by unfold opNorm; positivity)]
  exact wishartGamma_diagonal_opNorm_le_gaussianMass
    (p := p) (q := q) (σ := σ) ω

/-- The off-diagonal Wishart-Gamma operator-norm observable is integrable. -/
theorem gaussianWishartGammaOffDiagonalOpNorm_integrable :
    Integrable
      (fun ω : Ω p q σ =>
        opNorm
          (wishartGammaOffDiagonal (p := p) (q := q) (σ := σ)
            (gaussianMatrix p q σ ω)))
      (gaussianMeasure p q σ) := by
  have hGcont : Continuous (fun ω : Ω p q σ => gaussianMatrix p q σ ω) := by
    unfold gaussianMatrix GaussianModel.gaussianSampleMatrix
      GaussianModel.sampleMatrixOfRealCoordinates
    exact continuous_pi fun _ => continuous_pi fun _ => by fun_prop
  have hmeas :
      AEStronglyMeasurable
        (fun ω : Ω p q σ =>
          opNorm
            (wishartGammaOffDiagonal (p := p) (q := q) (σ := σ)
              (gaussianMatrix p q σ ω)))
        (gaussianMeasure p q σ) :=
    (continuous_wishartGamma_offDiagonal_opNorm_sample
        (p := p) (q := q) (σ := σ)).comp_aestronglyMeasurable
      hGcont.aestronglyMeasurable
  have hdom :
      Integrable
        (fun ω : Ω p q σ => 2 * gaussianMass p q σ ω)
        (gaussianMeasure p q σ) :=
    (gaussianMass_integrable (p := p) (q := q) (σ := σ)).const_mul 2
  refine hdom.mono' hmeas ?_
  refine Filter.Eventually.of_forall ?_
  intro ω
  rw [Real.norm_of_nonneg (by unfold opNorm; positivity)]
  exact wishartGamma_offDiagonal_opNorm_le_two_mul_gaussianMass
    (p := p) (q := q) (σ := σ) ω

/-- Every finite power of the total Gaussian mass is integrable. -/
theorem gaussianMass_pow_integrable (n : ℕ) :
    Integrable
      (fun ω : Ω p q σ => (gaussianMass p q σ ω) ^ n)
      (gaussianMeasure p q σ) := by
  let N : ℝ := bipartiteDimension p q * sampleDimension σ
  have hIntPosCentered :
      Integrable
        (fun ω : Ω p q σ =>
          Real.exp ((1 / 2 : ℝ) * (gaussianMass p q σ ω - N)))
        (gaussianMeasure p q σ) := by
    simpa [N] using
      HighProbabilityBounds.gaussianMass_centered_integrable_exp_mul
        (p := p) (q := q) (σ := σ) (θ := (1 / 2 : ℝ)) (by norm_num)
  have hIntNegCentered :
      Integrable
        (fun ω : Ω p q σ =>
          Real.exp ((-1 / 2 : ℝ) * (gaussianMass p q σ ω - N)))
        (gaussianMeasure p q σ) := by
    simpa [N] using
      HighProbabilityBounds.gaussianMass_centered_integrable_exp_mul
        (p := p) (q := q) (σ := σ) (θ := (-1 / 2 : ℝ)) (by norm_num)
  have hIntPos :
      Integrable
        (fun ω : Ω p q σ => Real.exp ((1 / 2 : ℝ) * gaussianMass p q σ ω))
        (gaussianMeasure p q σ) := by
    have hfun :
        (fun ω : Ω p q σ => Real.exp ((1 / 2 : ℝ) * gaussianMass p q σ ω)) =
          fun ω : Ω p q σ =>
            Real.exp ((1 / 2 : ℝ) * (gaussianMass p q σ ω - N)) *
              Real.exp (N / 2) := by
      funext ω
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hfun]
    exact hIntPosCentered.mul_const (Real.exp (N / 2))
  have hIntNeg :
      Integrable
        (fun ω : Ω p q σ => Real.exp (-(1 / 2 : ℝ) * gaussianMass p q σ ω))
        (gaussianMeasure p q σ) := by
    have hfun :
        (fun ω : Ω p q σ =>
          Real.exp (-(1 / 2 : ℝ) * gaussianMass p q σ ω)) =
          fun ω : Ω p q σ =>
            Real.exp ((-1 / 2 : ℝ) * (gaussianMass p q σ ω - N)) *
              Real.exp (-(N / 2)) := by
      funext ω
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hfun]
    exact hIntNegCentered.mul_const (Real.exp (-(N / 2)))
  exact
    ProbabilityTheory.integrable_pow_of_integrable_exp_mul
      (X := fun ω : Ω p q σ => gaussianMass p q σ ω)
      (μ := gaussianMeasure p q σ)
      (t := (1 / 2 : ℝ)) (by norm_num) hIntPos hIntNeg n

/-- The off-diagonal Wishart-Gamma operator-norm observable lies in every
finite positive `L^n`, by domination by twice the Gaussian mass. -/
theorem gaussianWishartGammaOffDiagonalOpNorm_memLp_nat
    {n : ℕ} (hn : n ≠ 0) :
    MemLp
      (fun ω : Ω p q σ =>
        opNorm
          (wishartGammaOffDiagonal (p := p) (q := q) (σ := σ)
            (gaussianMatrix p q σ ω)))
      (n : ℝ≥0∞)
      (gaussianMeasure p q σ) := by
  let μ := gaussianMeasure p q σ
  let f : Ω p q σ → ℝ := fun ω =>
    opNorm
      (wishartGammaOffDiagonal (p := p) (q := q) (σ := σ)
        (gaussianMatrix p q σ ω))
  have hGcont : Continuous (fun ω : Ω p q σ => gaussianMatrix p q σ ω) := by
    unfold gaussianMatrix GaussianModel.gaussianSampleMatrix
      GaussianModel.sampleMatrixOfRealCoordinates
    exact continuous_pi fun _ => continuous_pi fun _ => by fun_prop
  have hfCont : Continuous f :=
    (continuous_wishartGamma_offDiagonal_opNorm_sample
        (p := p) (q := q) (σ := σ)).comp hGcont
  have hfAES : AEStronglyMeasurable f μ :=
    hfCont.aestronglyMeasurable
  have hMassPow :
      Integrable
        (fun ω : Ω p q σ => (2 * gaussianMass p q σ ω) ^ n)
        μ := by
    have hbase :
        Integrable
          (fun ω : Ω p q σ => (2 : ℝ) ^ n * (gaussianMass p q σ ω) ^ n)
          μ :=
      (gaussianMass_pow_integrable (p := p) (q := q) (σ := σ) n).const_mul
        ((2 : ℝ) ^ n)
    convert hbase using 1
    funext ω
    ring
  have hPowInt :
      Integrable (fun ω : Ω p q σ => ‖f ω‖ ^ n) μ := by
    refine hMassPow.mono' ?_ ?_
    · exact (hfCont.norm.pow n).aestronglyMeasurable
    · refine Filter.Eventually.of_forall ?_
      intro ω
      have hf_nonneg : 0 ≤ f ω := by
        unfold f opNorm
        positivity
      have hmass_nonneg : 0 ≤ gaussianMass p q σ ω := by
        unfold gaussianMass frobeniusMass frobeniusNorm
        positivity
      have hbase :
          ‖f ω‖ ≤ 2 * gaussianMass p q σ ω := by
        simpa [f, Real.norm_of_nonneg hf_nonneg] using
          wishartGamma_offDiagonal_opNorm_le_two_mul_gaussianMass
            (p := p) (q := q) (σ := σ) ω
      rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg (f ω)) n)]
      exact pow_le_pow_left₀ (by positivity) hbase n
  have hMem :
      MemLp f (n : ℝ≥0∞) μ := by
    rw [← integrable_norm_rpow_iff hfAES]
    · simpa [ENNReal.toReal_natCast] using hPowInt
    · exact_mod_cast hn
    · exact ENNReal.coe_ne_top
  simpa [f, μ] using hMem

/-- Pipeline wrapper with the Gaussian integrability assumptions discharged
separately. -/
theorem appendixB_pipeline_to_final_theorem_with_integrability_closed
    [DecidableEq σ]
    {Q : ℕ → ℝ} {dNat : ℕ}
    {f : SampleMatrix p q σ → ℝ}
    {gaussianMean radialMean sphericalMean C1 CDiag COff : ℝ}
    {mean median range bad a b C cDim d eps momentParameter s : ℝ}
    {r : ℕ}
    (H :
      AubrunOffDiagonalExpectationDerivation
        (p := p) (q := q) (σ := σ) Q dNat d s COff)
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
  exact
    appendixB_pipeline_to_final_theorem
      (p := p) (q := q) (σ := σ)
      (Q := Q) (dNat := dNat) (f := f)
      (gaussianMean := gaussianMean)
      (radialMean := radialMean)
      (sphericalMean := sphericalMean)
      (C1 := C1) (CDiag := CDiag) (COff := COff)
      (mean := mean) (median := median) (range := range)
      (bad := bad) (a := a) (b := b) (C := C)
      (cDim := cDim) (d := d) (eps := eps)
      (momentParameter := momentParameter) (s := s) (r := r)
      H
      (gaussianWishartGammaOpNorm_integrable
        (p := p) (q := q) (σ := σ))
      (gaussianWishartGammaDiagonalOpNorm_integrable
        (p := p) (q := q) (σ := σ))
      (gaussianWishartGammaOffDiagonalOpNorm_integrable
        (p := p) (q := q) (σ := σ))
      hDiag hIndepR2 hRadialMean hSampleFactor hSampleBound
      hd hs hDim hLarge hC hmoment hScalePos
      hmean hf hRange hRangeNonneg hL hn hSmall hLip hMedian
      hGlobalLevy hBad hGood

end AppendixB
end PptFactorization
