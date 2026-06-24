import PptFactorization.AppendixBPipeline
import PptFactorization.AppendixBGaussianIntegrability

/-!
# Appendix B: diagonal Gamma bridge

This file isolates the deterministic diagonal part of the partially
transposed Wishart matrix.  The diagonal is not affected by the partial
transpose, so it is exactly the diagonal matrix with entries

`s⁻¹ ∑ α ‖G i α‖²`.

Consequently, the diagonal contribution in the Appendix B pipeline is the
Gaussian expectation of the operator norm of this explicit diagonal Gamma-max
observable.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.Frobenius

noncomputable section

namespace PptFactorization
namespace AppendixB

open RandomMatrixModel GaussianModel HighProbabilityBounds
open TraceWickExpansion

variable {p q σ : Type*}
variable [Fintype p] [Fintype q] [Fintype σ]
variable [DecidableEq p] [DecidableEq q]

/-- The diagonal Gamma averages
`s⁻¹ ∑_α |G_{iα}|²` attached to the sample matrix `G`. -/
def diagonalGammaAverages (G : SampleMatrix p q σ) :
    BipIndex p q → ℝ :=
  fun i => (sampleDimension σ)⁻¹ * ∑ α : σ, ‖G i α‖ ^ 2

/-- The explicit diagonal matrix whose diagonal entries are the Gamma averages. -/
def diagonalGammaMatrix (G : SampleMatrix p q σ) : BipMatrix p q :=
  Matrix.diagonal fun i : BipIndex p q =>
    ((diagonalGammaAverages (p := p) (q := q) (σ := σ) G i : ℝ) : ℂ)

/-- The diagonal Gamma max observable, written as the norm of the finite
coordinate vector of diagonal averages. -/
def diagonalGammaMaxObservable (G : SampleMatrix p q σ) : ℝ :=
  ‖diagonalGammaAverages (p := p) (q := q) (σ := σ) G‖

/-- Gaussian mean of the explicit diagonal Gamma-max observable. -/
def gaussianDiagonalGammaMaxMean : ℝ :=
  ∫ ω : Ω p q σ,
    diagonalGammaMaxObservable (p := p) (q := q) (σ := σ)
      (gaussianMatrix p q σ ω)
    ∂gaussianMeasure p q σ

omit [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] in
@[simp] theorem diagonalGammaAverages_nonneg
    (G : SampleMatrix p q σ) (i : BipIndex p q) :
    0 ≤ diagonalGammaAverages (p := p) (q := q) (σ := σ) G i := by
  unfold diagonalGammaAverages sampleDimension
  positivity

set_option linter.unusedSectionVars false in
/-- Partial transposition does not change the diagonal of the Wishart matrix,
and the diagonal entries are the normalized squared row masses. -/
theorem diagonalPart_wishartGamma_eq_diagonalGammaMatrix
    (G : SampleMatrix p q σ) :
    diagonalPart
        (wishartGamma (p := p) (q := q) (σ := σ) G) =
      diagonalGammaMatrix (p := p) (q := q) (σ := σ) G := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [diagonalPart, diagonalGammaMatrix, diagonalGammaAverages,
      wishartGamma, gamma, wishart, densityMatrix, Matrix.mul_apply,
      Finset.mul_sum, sampleDimension, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
  · simp [diagonalPart, diagonalGammaMatrix, hij]

/-- Operator norm of a real diagonal matrix, in the Euclidean CLM model, is the
finite sup norm of its diagonal vector. -/
theorem opNorm_diagonal_real_eq_pi_norm (a : BipIndex p q → ℝ) :
    opNorm (p := p) (q := q)
        (Matrix.diagonal fun i : BipIndex p q => ((a i : ℝ) : ℂ)) =
      ‖a‖ := by
  rw [opNorm]
  rw [← Matrix.cstar_norm_def
    (A := Matrix.diagonal fun i : BipIndex p q => ((a i : ℝ) : ℂ))]
  rw [Matrix.l2_opNorm_diagonal]
  simp [Pi.norm_def]

/-- The diagonal part of `W^Γ` has operator norm exactly equal to the explicit
Gamma-max observable. -/
theorem opNorm_diagonalPart_wishartGamma_eq_diagonalGammaMaxObservable
    (G : SampleMatrix p q σ) :
    opNorm
        (diagonalPart
          (wishartGamma (p := p) (q := q) (σ := σ) G)) =
      diagonalGammaMaxObservable (p := p) (q := q) (σ := σ) G := by
  rw [diagonalPart_wishartGamma_eq_diagonalGammaMatrix]
  exact opNorm_diagonal_real_eq_pi_norm
    (p := p) (q := q)
    (a := diagonalGammaAverages (p := p) (q := q) (σ := σ) G)

/-- The diagonal term in the canonical Appendix B pipeline is exactly the
Gaussian mean of the concrete Gamma-max observable. -/
theorem gaussianWishartGammaDiagonalOpNormMean_eq_diagonalGammaMaxMean :
    gaussianWishartGammaDiagonalOpNormMean
        (p := p) (q := q) (σ := σ) =
      gaussianDiagonalGammaMaxMean (p := p) (q := q) (σ := σ) := by
  unfold gaussianWishartGammaDiagonalOpNormMean gaussianDiagonalGammaMaxMean
  congr with ω
  exact opNorm_diagonalPart_wishartGamma_eq_diagonalGammaMaxObservable
    (p := p) (q := q) (σ := σ) (gaussianMatrix p q σ ω)

/-- Appendix-facing diagonal Gamma bound interface: any proved bound on the
explicit Gamma-max observable immediately supplies the diagonal input expected
by the pipeline. -/
theorem gaussianWishartGammaDiagonalOpNormMean_le_of_diagonalGammaMaxMean_le
    {CDiag : ℝ}
    (hGamma :
      gaussianDiagonalGammaMaxMean (p := p) (q := q) (σ := σ) ≤ CDiag) :
    gaussianWishartGammaDiagonalOpNormMean (p := p) (q := q) (σ := σ) ≤
      CDiag := by
  rwa [gaussianWishartGammaDiagonalOpNormMean_eq_diagonalGammaMaxMean]

/-- Probabilistic upper tail for the explicit diagonal Gamma-max observable.

The diagonal Gamma-max is pointwise dominated by the Gaussian mass, so it
inherits the same exponential upper tail at the `2 D s` scale. -/
theorem gaussianDiagonalGammaMax_upper_tail :
    (gaussianMeasure p q σ).real
        {ω | 2 * bipartiteDimension p q * sampleDimension σ ≤
          diagonalGammaMaxObservable (p := p) (q := q) (σ := σ)
            (gaussianMatrix p q σ ω)} ≤
      Real.exp (-((1 / 6 : ℝ) * bipartiteDimension p q * sampleDimension σ)) := by
  haveI : IsProbabilityMeasure (gaussianMeasure p q σ) := by
    rw [gaussianMeasure_eq]
    infer_instance
  have hsubset :
      {ω | 2 * bipartiteDimension p q * sampleDimension σ ≤
          diagonalGammaMaxObservable (p := p) (q := q) (σ := σ)
            (gaussianMatrix p q σ ω)} ⊆
        {ω | 2 * bipartiteDimension p q * sampleDimension σ ≤ gaussianMass p q σ ω} := by
    intro ω hω
    have hdiag :
        diagonalGammaMaxObservable (p := p) (q := q) (σ := σ)
          (gaussianMatrix p q σ ω) ≤ gaussianMass p q σ ω := by
      rw [← opNorm_diagonalPart_wishartGamma_eq_diagonalGammaMaxObservable
        (p := p) (q := q) (σ := σ) (G := gaussianMatrix p q σ ω)]
      exact wishartGamma_diagonal_opNorm_le_gaussianMass
        (p := p) (q := q) (σ := σ) ω
    exact le_trans hω hdiag
  calc
    (gaussianMeasure p q σ).real
        {ω | 2 * bipartiteDimension p q * sampleDimension σ ≤
          diagonalGammaMaxObservable (p := p) (q := q) (σ := σ)
            (gaussianMatrix p q σ ω)} ≤
        (gaussianMeasure p q σ).real
          {ω | 2 * bipartiteDimension p q * sampleDimension σ ≤ gaussianMass p q σ ω} := by
            exact measureReal_mono hsubset
              (h₂ := (measure_lt_top (gaussianMeasure p q σ) _).ne)
    _ ≤ Real.exp (-((1 / 6 : ℝ) * bipartiteDimension p q * sampleDimension σ)) :=
        gaussianMass_upper_tail (p := p) (q := q) (σ := σ)

omit [DecidableEq p] [DecidableEq q] in
/-- Sharp one-row Gamma-average tail. -/
theorem gaussianDiagonalGammaAverage_upper_tail
    (i : RandomMatrixModel.BipIndex p q) {t : ℝ} (ht : 0 < t) :
    (gaussianMeasure p q σ).real
        {ω | t ≤ diagonalGammaAverages (p := p) (q := q) (σ := σ)
          (gaussianMatrix p q σ ω) i} ≤
      Real.exp (-(1 / 2 : ℝ) * (t * sampleDimension σ) +
        Real.log 2 * sampleDimension σ) := by
  classical
  haveI : IsProbabilityMeasure (gaussianMeasure p q σ) := by
    rw [gaussianMeasure_eq]
    infer_instance
  by_cases hs0 : sampleDimension σ = 0
  · have hle1 : (gaussianMeasure p q σ).real
        {ω | t ≤ diagonalGammaAverages (p := p) (q := q) (σ := σ)
          (gaussianMatrix p q σ ω) i} ≤ 1 := by
        exact measureReal_le_one
    have hRHS :
        (Real.exp (-(1 / 2 : ℝ) * (t * sampleDimension σ) +
          Real.log 2 * sampleDimension σ)) = 1 := by
      have hs0' : (Fintype.card σ : ℝ) = 0 := by
        simpa [sampleDimension] using hs0
      rw [sampleDimension, hs0']
      simpa using Real.exp_zero
    calc
      (gaussianMeasure p q σ).real
          {ω | t ≤ diagonalGammaAverages (p := p) (q := q) (σ := σ)
            (gaussianMatrix p q σ ω) i} ≤ 1 := hle1
      _ = Real.exp (-(1 / 2 : ℝ) * (t * sampleDimension σ) +
          Real.log 2 * sampleDimension σ) := by
        symm
        exact hRHS
  · have hspos : 0 < sampleDimension σ := by
      have hsnonneg : 0 ≤ sampleDimension σ := sampleDimension_nonneg
      have hsne : 0 ≠ sampleDimension σ := by
        intro h
        exact hs0 h.symm
      exact lt_of_le_of_ne hsnonneg hsne
    let S : Set (EuclideanSpace ℂ σ) := {z : EuclideanSpace ℂ σ | t * sampleDimension σ ≤ ‖z‖ ^ 2}
    have hrowSet :
        {ω : Ω p q σ | t ≤ diagonalGammaAverages (p := p) (q := q) (σ := σ)
          (gaussianMatrix p q σ ω) i} =
          gaussianRow (p := p) (q := q) (σ := σ) i ⁻¹' S := by
      ext ω
      unfold S
      have hnorm :
          ‖rowVector (p := p) (q := q) (σ := σ)
              (sampleMatrixOfRealCoordinates ω) i‖ ^ 2 =
            ∑ α : σ, ‖sampleMatrixOfRealCoordinates ω i α‖ ^ 2 := by
        simpa [rowVector, EuclideanSpace.norm_sq_eq]
      constructor
      · intro h
        have hsum : t ≤ (∑ α : σ, ‖sampleMatrixOfRealCoordinates ω i α‖ ^ 2) *
            (sampleDimension σ)⁻¹ := by
          simpa [diagonalGammaAverages, div_eq_mul_inv, mul_comm] using h
        have hmul : t * sampleDimension σ ≤ ∑ α : σ,
            ‖sampleMatrixOfRealCoordinates ω i α‖ ^ 2 :=
          (le_div_iff₀ hspos).1 hsum
        simpa [hnorm] using hmul
      · intro h
        have hsum : t * sampleDimension σ ≤ ∑ α : σ,
            ‖sampleMatrixOfRealCoordinates ω i α‖ ^ 2 := by
          simpa [hnorm] using h
        have hdiv : t ≤ (∑ α : σ, ‖sampleMatrixOfRealCoordinates ω i α‖ ^ 2) *
            (sampleDimension σ)⁻¹ := by
          simpa [div_eq_mul_inv, mul_comm] using (le_div_iff₀ hspos).2 hsum
        simpa [diagonalGammaAverages, div_eq_mul_inv, mul_comm] using hdiv
    have hSmeas : MeasurableSet S := by
      unfold S
      exact measurableSet_le measurable_const (by fun_prop)
    have hrowMeas : Measurable (gaussianRow (p := p) (q := q) (σ := σ) i) := by
      rw [gaussianRow_eq_complexVectorOfRealCoordinates_comp_rowRealCoordinates
        (p := p) (q := q) (σ := σ) i]
      exact (measurable_complexVectorOfRealCoordinates (ι := σ)).comp
        (measurable_rowRealCoordinates (p := p) (q := q) (σ := σ) i)
    have hmapS :
        (Measure.map (gaussianRow (p := p) (q := q) (σ := σ) i)
          (gaussianMeasure p q σ)) S =
        (gaussianMeasure p q σ) (gaussianRow (p := p) (q := q) (σ := σ) i ⁻¹' S) := by
      simpa using (Measure.map_apply hrowMeas hSmeas :
        (Measure.map (gaussianRow (p := p) (q := q) (σ := σ) i)
          (gaussianMeasure p q σ)) S =
        (gaussianMeasure p q σ) (gaussianRow (p := p) (q := q) (σ := σ) i ⁻¹' S))
    have hreal :
        (gaussianMeasure p q σ).real
            {ω | t ≤ diagonalGammaAverages (p := p) (q := q) (σ := σ)
              (gaussianMatrix p q σ ω) i} =
          (Measure.map (gaussianRow (p := p) (q := q) (σ := σ) i)
            (gaussianMeasure p q σ)).real S := by
      calc
        (gaussianMeasure p q σ).real
            {ω | t ≤ diagonalGammaAverages (p := p) (q := q) (σ := σ)
              (gaussianMatrix p q σ ω) i} =
            (gaussianMeasure p q σ).real (gaussianRow (p := p) (q := q) (σ := σ) i ⁻¹' S) := by
              rw [hrowSet]
        _ = (Measure.map (gaussianRow (p := p) (q := q) (σ := σ) i)
              (gaussianMeasure p q σ)).real S := by
              simpa [Measure.real] using congrArg ENNReal.toReal hmapS.symm
    rw [hreal, gaussianRow_map_gaussianMeasure]
    simpa [S] using
      (standardComplexGaussianVectorMeasure_norm_sq_upper_tail
        (ι := σ) (R := t * sampleDimension σ))

omit [DecidableEq p] [DecidableEq q] in
/-- Sharp finite-union upper tail for the diagonal Gamma max observable. -/
theorem gaussianDiagonalGammaMax_upper_tail_sharp
    {t : ℝ} (ht : 0 < t) :
    (gaussianMeasure p q σ).real
        {ω | t ≤ diagonalGammaMaxObservable (p := p) (q := q) (σ := σ)
          (gaussianMatrix p q σ ω)} ≤
      bipartiteDimension p q *
        Real.exp (-(1 / 2 : ℝ) * (t * sampleDimension σ) +
          Real.log 2 * sampleDimension σ) := by
  classical
  haveI : IsProbabilityMeasure (gaussianMeasure p q σ) := by
    rw [gaussianMeasure_eq]
    infer_instance
  by_cases hDzero : bipartiteDimension p q = 0
  · have hcard : Fintype.card (RandomMatrixModel.BipIndex p q) = 0 := by
      have : bipartiteDimension p q = 0 := hDzero
      unfold bipartiteDimension at this
      exact_mod_cast this
    haveI : IsEmpty (RandomMatrixModel.BipIndex p q) :=
      Fintype.card_eq_zero_iff.mp hcard
    have hset :
        {ω : Ω p q σ | t ≤ diagonalGammaMaxObservable (p := p) (q := q) (σ := σ)
          (gaussianMatrix p q σ ω)} = ∅ := by
      ext ω
      constructor
      · intro hω
        have hzero :
            diagonalGammaMaxObservable (p := p) (q := q) (σ := σ)
              (sampleMatrixOfRealCoordinates ω) = 0 := by
          have hfun :
              diagonalGammaAverages (p := p) (q := q) (σ := σ)
                (sampleMatrixOfRealCoordinates ω) = 0 := by
            funext i
            exact False.elim (IsEmpty.false i)
          rw [diagonalGammaMaxObservable, hfun]
          simp
        have ht0 : t ≤ (0 : ℝ) := by simpa [hzero] using hω
        exact (not_le_of_gt ht) ht0
      · intro hω
        exact False.elim hω
    have hgoal :
        (gaussianMeasure p q σ).real
          {ω : Ω p q σ | t ≤ diagonalGammaMaxObservable (p := p) (q := q) (σ := σ)
            (gaussianMatrix p q σ ω)} = 0 := by
      rw [hset]
      simpa using
        (measureReal_empty : (gaussianMeasure p q σ).real (∅ : Set (Ω p q σ)) = 0)
    have hRHS : bipartiteDimension p q * Real.exp
        (-(1 / 2 : ℝ) * (t * sampleDimension σ) + Real.log 2 * sampleDimension σ) = 0 := by
      simp [hDzero]
    nlinarith [hgoal, hRHS]
  · have hDpos : 0 < bipartiteDimension p q := by
      have hDnonneg : 0 ≤ bipartiteDimension p q := bipartiteDimension_nonneg
      have hDne : 0 ≠ bipartiteDimension p q := by
        intro h
        exact hDzero h.symm
      exact lt_of_le_of_ne hDnonneg hDne
    have hsubset :
        {ω | t ≤ diagonalGammaMaxObservable (p := p) (q := q) (σ := σ)
          (gaussianMatrix p q σ ω)} ⊆
          ⋃ i : RandomMatrixModel.BipIndex p q,
            {ω | t ≤ diagonalGammaAverages (p := p) (q := q) (σ := σ)
              (gaussianMatrix p q σ ω) i} := by
      intro ω hω
      by_contra hnot
      have hforall : ∀ i : RandomMatrixModel.BipIndex p q,
          diagonalGammaAverages (p := p) (q := q) (σ := σ)
            (gaussianMatrix p q σ ω) i < t := by
        intro i
        by_contra hlt
        have hle : t ≤ diagonalGammaAverages (p := p) (q := q) (σ := σ)
            (gaussianMatrix p q σ ω) i := le_of_not_gt hlt
        exact hnot (by
          exact Set.mem_iUnion.2 ⟨i, hle⟩)
      have hnormlt :
          ‖diagonalGammaAverages (p := p) (q := q) (σ := σ)
            (gaussianMatrix p q σ ω)‖ < t := by
        have hforall' : ∀ i : RandomMatrixModel.BipIndex p q,
            ‖diagonalGammaAverages (p := p) (q := q) (σ := σ)
              (gaussianMatrix p q σ ω) i‖ < t := by
          intro i
          have hnonneg :
              0 ≤ diagonalGammaAverages (p := p) (q := q) (σ := σ)
                (gaussianMatrix p q σ ω) i :=
            diagonalGammaAverages_nonneg
              (p := p) (q := q) (σ := σ) (gaussianMatrix p q σ ω) i
          have habs : |diagonalGammaAverages (p := p) (q := q) (σ := σ)
              (gaussianMatrix p q σ ω) i| < t := by
            rw [abs_of_nonneg hnonneg]
            exact hforall i
          simpa [Real.norm_eq_abs] using habs
        exact (pi_norm_lt_iff
          (ι := RandomMatrixModel.BipIndex p q)
          (G := fun _ => ℝ)
          (x := diagonalGammaAverages (p := p) (q := q) (σ := σ)
            (gaussianMatrix p q σ ω)) ht).2 hforall'
      exact (not_lt_of_ge hω) hnormlt
    have hunion :
        (gaussianMeasure p q σ).real
          (⋃ i : RandomMatrixModel.BipIndex p q,
            {ω | t ≤ diagonalGammaAverages (p := p) (q := q) (σ := σ)
              (gaussianMatrix p q σ ω) i}) ≤
        ∑ i : RandomMatrixModel.BipIndex p q,
          (gaussianMeasure p q σ).real
            {ω | t ≤ diagonalGammaAverages (p := p) (q := q) (σ := σ)
              (gaussianMatrix p q σ ω) i} := by
      exact measureReal_iUnion_fintype_le (μ := gaussianMeasure p q σ)
        (fun i : RandomMatrixModel.BipIndex p q =>
          {ω | t ≤ diagonalGammaAverages (p := p) (q := q) (σ := σ)
            (gaussianMatrix p q σ ω) i})
    have hrowBound :
        ∀ i : RandomMatrixModel.BipIndex p q,
          (gaussianMeasure p q σ).real
            {ω | t ≤ diagonalGammaAverages (p := p) (q := q) (σ := σ)
              (gaussianMatrix p q σ ω) i} ≤
            Real.exp (-(1 / 2 : ℝ) * (t * sampleDimension σ) +
              Real.log 2 * sampleDimension σ) := by
      intro i
      exact gaussianDiagonalGammaAverage_upper_tail
        (p := p) (q := q) (σ := σ) i ht
    calc
      (gaussianMeasure p q σ).real
          {ω | t ≤ diagonalGammaMaxObservable (p := p) (q := q) (σ := σ)
            (gaussianMatrix p q σ ω)} ≤
        (gaussianMeasure p q σ).real
          (⋃ i : RandomMatrixModel.BipIndex p q,
            {ω | t ≤ diagonalGammaAverages (p := p) (q := q) (σ := σ)
              (gaussianMatrix p q σ ω) i}) := by
          exact measureReal_mono hsubset
            (h₂ := (measure_lt_top (gaussianMeasure p q σ) _).ne)
      _ ≤ ∑ i : RandomMatrixModel.BipIndex p q,
          (gaussianMeasure p q σ).real
            {ω | t ≤ diagonalGammaAverages (p := p) (q := q) (σ := σ)
              (gaussianMatrix p q σ ω) i} := hunion
      _ ≤ ∑ i : RandomMatrixModel.BipIndex p q,
          Real.exp (-(1 / 2 : ℝ) * (t * sampleDimension σ) +
            Real.log 2 * sampleDimension σ) := by
          gcongr with i
          exact hrowBound i
      _ = bipartiteDimension p q *
          Real.exp (-(1 / 2 : ℝ) * (t * sampleDimension σ) +
            Real.log 2 * sampleDimension σ) := by
          simp [bipartiteDimension, Finset.sum_const, mul_comm, mul_left_comm, mul_assoc]

/-- The Gaussian mean of the diagonal Gamma-max observable admits an explicit
tail-to-expectation bound at positive sample dimension.

This is the no-input probabilistic estimate for
`E max_i s⁻¹ ∑α |Gᵢα|²` coming from the sharp finite-union tail bound and a
layer-cake integration. -/
theorem gaussianDiagonalGammaMaxMean_le_of_sampleDimension_pos
    (hs : 0 < sampleDimension σ) :
    gaussianDiagonalGammaMaxMean (p := p) (q := q) (σ := σ) ≤
      2 * Real.log 2 +
        2 * bipartiteDimension p q / sampleDimension σ +
        2 / sampleDimension σ := by
  classical
  haveI : IsProbabilityMeasure (gaussianMeasure p q σ) := by
    rw [gaussianMeasure_eq]
    infer_instance
  let D : ℝ := bipartiteDimension p q
  let s : ℝ := sampleDimension σ
  let A : ℝ := 2 * Real.log 2 + 2 * D / s
  let X : Ω p q σ → ℝ := fun ω =>
    diagonalGammaMaxObservable (p := p) (q := q) (σ := σ)
      (gaussianMatrix p q σ ω)
  let tail : ℝ → ℝ := fun t =>
    (gaussianMeasure p q σ).real {ω : Ω p q σ | t < X ω}
  let upper : ℝ → ℝ :=
    (Set.Ioc (0 : ℝ) A).indicator (fun _ => (1 : ℝ)) +
      (Set.Ioi A).indicator
        (fun t => Real.exp ((s * A) / 2) * Real.exp (-(s / 2 : ℝ) * t))
  have hD_nonneg : 0 ≤ D := by
    simpa [D] using (bipartiteDimension_nonneg (p := p) (q := q))
  have hs_nonneg : 0 ≤ s := le_of_lt hs
  have hs_ne : s ≠ 0 := ne_of_gt hs
  have hA_pos : 0 < A := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hfrac : 0 ≤ 2 * D / s := by
      positivity
    dsimp [A, D, s]
    nlinarith
  have hA_nonneg : 0 ≤ A := le_of_lt hA_pos
  have hXeq :
      X = fun ω : Ω p q σ =>
        opNorm
          (diagonalPart
            (wishartGamma (p := p) (q := q) (σ := σ)
              (gaussianMatrix p q σ ω))) := by
    funext ω
    exact (opNorm_diagonalPart_wishartGamma_eq_diagonalGammaMaxObservable
      (p := p) (q := q) (σ := σ) (gaussianMatrix p q σ ω)
      ).symm
  have hIntX : Integrable X (gaussianMeasure p q σ) := by
    simpa [X, hXeq] using
      (gaussianWishartGammaDiagonalOpNorm_integrable
        (p := p) (q := q) (σ := σ))
  have hNonnegX : 0 ≤ᵐ[gaussianMeasure p q σ] X := by
    exact Filter.Eventually.of_forall fun ω => by
      rw [hXeq]
      unfold opNorm
      exact norm_nonneg _
  have hLayer :
      ∫ ω : Ω p q σ, X ω ∂gaussianMeasure p q σ =
        ∫ t in Set.Ioi (0 : ℝ), tail t := by
    simpa [X, tail] using
      (Integrable.integral_eq_integral_meas_lt
        (μ := gaussianMeasure p q σ) (f := X) hIntX hNonnegX)
  have hFirstOn :
      IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc (0 : ℝ) A) volume := by
    exact integrableOn_const (by simp [Real.volume_Ioc])
  have hFirst :
      Integrable
        (fun t : ℝ =>
          (Set.Ioc (0 : ℝ) A).indicator (fun _ => (1 : ℝ)) t)
        volume := by
    have hFirstOn' :
        IntegrableOn
          (fun t : ℝ =>
            (Set.Ioc (0 : ℝ) A).indicator (fun _ => (1 : ℝ)) t)
          (Set.univ : Set ℝ) volume := by
      rw [MeasureTheory.integrableOn_indicator_iff measurableSet_Ioc]
      simpa using hFirstOn
    simpa [Measure.restrict_univ] using hFirstOn'.integrable
  have hs2neg : (-(s / 2 : ℝ)) < 0 := by
    linarith
  have hExpOn :
      IntegrableOn (fun t : ℝ => Real.exp (-(s / 2 : ℝ) * t))
        (Set.Ioi A) volume := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (integrableOn_exp_mul_Ioi (a := -(s / 2 : ℝ)) hs2neg A)
  have hSecondOn :
      IntegrableOn
        (fun t : ℝ =>
          Real.exp ((s * A) / 2) * Real.exp (-(s / 2 : ℝ) * t))
        (Set.Ioi A) volume := by
    exact hExpOn.const_mul (Real.exp ((s * A) / 2))
  have hSecond :
      Integrable
        (fun t : ℝ =>
          (Set.Ioi A).indicator
            (fun t => Real.exp ((s * A) / 2) * Real.exp (-(s / 2 : ℝ) * t))
            t)
        volume := by
    have hSecondOn' :
        IntegrableOn
          (fun t : ℝ =>
            (Set.Ioi A).indicator
              (fun t => Real.exp ((s * A) / 2) * Real.exp (-(s / 2 : ℝ) * t))
              t)
          (Set.univ : Set ℝ) volume := by
      rw [MeasureTheory.integrableOn_indicator_iff measurableSet_Ioi]
      simpa using hSecondOn
    simpa [Measure.restrict_univ] using hSecondOn'.integrable
  have hUpper : Integrable upper volume := by
    dsimp [upper]
    exact hFirst.add hSecond
  have hNonnegTail :
      0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        tail := by
    exact Filter.Eventually.of_forall fun _ => by
      dsimp [tail]
      positivity
  have hUpperRestr :
      Integrable upper (volume.restrict (Set.Ioi (0 : ℝ))) := by
    exact hUpper.integrableOn.integrable
  have hPointwise :
      tail ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] upper := by
    rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall ?_
    intro t ht0
    by_cases htA : t ≤ A
    · have hind1 :
          (Set.Ioc (0 : ℝ) A).indicator (fun _ => (1 : ℝ)) t = 1 := by
          rw [Set.indicator_of_mem]
          exact ⟨ht0, htA⟩
      have hind2 :
          (Set.Ioi A).indicator
            (fun t => Real.exp ((s * A) / 2) * Real.exp (-(s / 2 : ℝ) * t))
            t = 0 := by
        rw [Set.indicator_of_notMem]
        intro hmem
        exact not_lt_of_ge htA hmem
      have hupper_eq : upper t = 1 := by
        dsimp [upper]
        rw [hind1, hind2]
        norm_num
      calc
        tail t ≤ 1 := MeasureTheory.measureReal_le_one
        _ = upper t := by
          symm
          exact hupper_eq
    · have hAt : A < t := lt_of_not_ge htA
      have hind1 :
          (Set.Ioc (0 : ℝ) A).indicator (fun _ => (1 : ℝ)) t = 0 := by
        rw [Set.indicator_of_notMem]
        intro hmem
        exact htA hmem.2
      have hind2 :
          (Set.Ioi A).indicator
            (fun t => Real.exp ((s * A) / 2) * Real.exp (-(s / 2 : ℝ) * t))
            t =
          Real.exp ((s * A) / 2) * Real.exp (-(s / 2 : ℝ) * t) := by
        rw [Set.indicator_of_mem]
        exact hAt
      have hsubset : {ω : Ω p q σ | t < X ω} ⊆
          {ω : Ω p q σ | t ≤ X ω} := by
        intro ω hω
        exact le_of_lt (by simpa using hω)
      have htail :
          tail t ≤ D * Real.exp (-(1 / 2 : ℝ) * (t * s) + Real.log 2 * s) := by
        calc
          tail t = (gaussianMeasure p q σ).real {ω : Ω p q σ | t < X ω} := rfl
          _ ≤ (gaussianMeasure p q σ).real {ω : Ω p q σ | t ≤ X ω} := by
            exact measureReal_mono hsubset
              (h₂ := (measure_lt_top (gaussianMeasure p q σ) _).ne)
          _ ≤ D * Real.exp (-(1 / 2 : ℝ) * (t * s) + Real.log 2 * s) := by
            simpa [D, X, s] using
              (gaussianDiagonalGammaMax_upper_tail_sharp
                (p := p) (q := q) (σ := σ) (t := t) ht0)
      have hAeq :
          (s * A) / 2 = s * Real.log 2 + D := by
        dsimp [A, D, s]
        field_simp [hs_ne]
      have hAexp :
          Real.exp ((s * A) / 2) =
            Real.exp D * Real.exp (Real.log 2 * s) := by
        rw [hAeq, Real.exp_add]
        simp [mul_comm, mul_left_comm, mul_assoc]
      have hupper_eq :
          upper t =
            Real.exp ((s * A) / 2) * Real.exp (-(s / 2 : ℝ) * t) := by
        dsimp [upper]
        rw [hind1, hind2]
        ring
      have hExpBound :
          D * Real.exp (-(1 / 2 : ℝ) * (t * s) + Real.log 2 * s) ≤
            upper t := by
        have hDexp : D ≤ Real.exp D := by
          linarith [Real.add_one_le_exp D]
        have hExpNeg : (-(1 / 2 : ℝ) * (t * s)) = -(s / 2 : ℝ) * t := by
          ring
        calc
          D * Real.exp (-(1 / 2 : ℝ) * (t * s) + Real.log 2 * s)
              = D * (Real.exp (Real.log 2 * s) *
                  Real.exp (-(s / 2 : ℝ) * t)) := by
                  rw [hExpNeg, Real.exp_add]
                  simp [mul_comm, mul_left_comm, mul_assoc]
          _ = (D * Real.exp (Real.log 2 * s)) *
                Real.exp (-(s / 2 : ℝ) * t) := by
                ring
          _ ≤ (Real.exp D * Real.exp (Real.log 2 * s)) *
                Real.exp (-(s / 2 : ℝ) * t) := by
                have hEnonneg :
                    0 ≤ Real.exp (Real.log 2 * s) * Real.exp (-(s / 2 : ℝ) * t) := by
                  positivity
                simpa [mul_comm, mul_left_comm, mul_assoc] using
                  (mul_le_mul_of_nonneg_left hDexp hEnonneg)
          _ = Real.exp ((s * A) / 2) * Real.exp (-(s / 2 : ℝ) * t) := by
                rw [hAexp]
          _ = upper t := by
                symm
                exact hupper_eq
      calc
        tail t ≤ D * Real.exp (-(1 / 2 : ℝ) * (t * s) +
            Real.log 2 * s) := htail
        _ ≤ upper t := hExpBound
  have hTailIntegral :
      ∫ t in Set.Ioi (0 : ℝ), tail t ≤
        ∫ t in Set.Ioi (0 : ℝ), upper t := by
    simpa [tail, upper] using
      (integral_mono_of_nonneg
        (μ := volume.restrict (Set.Ioi (0 : ℝ)))
        (f := tail) (g := upper) hNonnegTail hUpperRestr hPointwise)
  have hFirstIntegral :
      ∫ t : ℝ, (Set.Ioc (0 : ℝ) A).indicator (fun _ => (1 : ℝ)) t = A := by
    rw [MeasureTheory.integral_indicator measurableSet_Ioc]
    rw [MeasureTheory.setIntegral_const]
    simp [Real.volume_Ioc, hA_nonneg]
  have hSecondIntegral :
      ∫ t : ℝ,
          (Set.Ioi A).indicator
            (fun t =>
              Real.exp ((s * A) / 2) * Real.exp (-(s / 2 : ℝ) * t)) t =
        2 / s := by
    calc
      ∫ t : ℝ,
          (Set.Ioi A).indicator
            (fun t =>
              Real.exp ((s * A) / 2) * Real.exp (-(s / 2 : ℝ) * t)) t
          = ∫ t : ℝ,
              Real.exp ((s * A) / 2) *
                (Set.Ioi A).indicator
                  (fun t => Real.exp (-(s / 2 : ℝ) * t)) t := by
              congr with t
              by_cases ht : t ∈ Set.Ioi A <;>
                simp [Set.indicator, ht, mul_comm, mul_left_comm, mul_assoc]
      _ = Real.exp ((s * A) / 2) *
            ∫ t : ℝ,
              (Set.Ioi A).indicator
                (fun t => Real.exp (-(s / 2 : ℝ) * t)) t := by
            rw [MeasureTheory.integral_const_mul]
      _ = Real.exp ((s * A) / 2) *
            ∫ t in Set.Ioi A, Real.exp (-(s / 2 : ℝ) * t) := by
            rw [MeasureTheory.integral_indicator measurableSet_Ioi]
      _ = Real.exp ((s * A) / 2) *
            (-Real.exp (-(s / 2 : ℝ) * A) / (-(s / 2 : ℝ))) := by
            rw [integral_exp_mul_Ioi (a := -(s / 2 : ℝ)) hs2neg A]
      _ = Real.exp ((s * A) / 2) * Real.exp (-(s / 2 : ℝ) * A) * (2 / s) := by
            field_simp [hs_ne]
      _ = 2 / s := by
            have hCancel :
                Real.exp ((s * A) / 2) * Real.exp (-(s / 2 : ℝ) * A) = 1 := by
              have hsum :
                  ((s * A) / 2) + (-(s / 2 : ℝ) * A) = 0 := by
                dsimp [A, D, s]
                field_simp [hs_ne]
                ring
              rw [← Real.exp_add, hsum, Real.exp_zero]
            rw [hCancel]
            ring
  have hUpperSet :
      ∫ t in Set.Ioi (0 : ℝ), upper t = ∫ t : ℝ, upper t := by
    rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
    have hsupport : (Set.Ioi (0 : ℝ)).indicator upper = upper := by
      funext t
      by_cases ht : 0 < t
      · simp [upper, ht]
      · have htle0 : t ≤ 0 := le_of_not_gt ht
        have hnot : t ∉ Set.Ioi A := by
          intro hmem
          have hAt : A < t := hmem
          linarith [hA_nonneg, htle0, hAt]
        simp [upper, ht, hnot]
    simpa [hsupport]
  have hUpperFull :
      ∫ t : ℝ, upper t = A + 2 / s := by
    dsimp [upper]
    rw [integral_add hFirst hSecond]
    rw [hFirstIntegral, hSecondIntegral]
  calc
    gaussianDiagonalGammaMaxMean (p := p) (q := q) (σ := σ)
        = ∫ t in Set.Ioi (0 : ℝ), tail t := hLayer
    _ ≤ ∫ t in Set.Ioi (0 : ℝ), upper t := hTailIntegral
    _ = A + 2 / s := by
          rw [hUpperSet, hUpperFull]
    _ = 2 * Real.log 2 +
        2 * bipartiteDimension p q / sampleDimension σ +
        2 / sampleDimension σ := by
          simp [A, D, s, mul_comm, mul_left_comm, mul_assoc]

/-- A fully explicit `C_λ`-style bound for the diagonal Gamma-max mean. -/
theorem gaussianDiagonalGammaMaxMean_le_C_lambda
    {lam : ℝ} (hlam : 0 < lam)
    (hRatio : lam * bipartiteDimension p q ≤ sampleDimension σ) :
    gaussianDiagonalGammaMaxMean (p := p) (q := q) (σ := σ) ≤
      2 * Real.log 2 + 4 / lam := by
  classical
  by_cases hD0 : bipartiteDimension p q = 0
  · have hcard : Fintype.card (RandomMatrixModel.BipIndex p q) = 0 := by
      have : bipartiteDimension p q = 0 := hD0
      unfold bipartiteDimension at this
      exact_mod_cast this
    haveI : IsEmpty (RandomMatrixModel.BipIndex p q) :=
      Fintype.card_eq_zero_iff.mp hcard
    have hzero :
        ∀ ω : Ω p q σ,
          diagonalGammaMaxObservable (p := p) (q := q) (σ := σ)
            (gaussianMatrix p q σ ω) = 0 := by
      intro ω
      unfold diagonalGammaMaxObservable
      rw [Pi.norm_def]
      simp [hcard]
    rw [gaussianDiagonalGammaMaxMean]
    have hfun :
        (fun ω : Ω p q σ =>
          diagonalGammaMaxObservable (p := p) (q := q) (σ := σ)
            (gaussianMatrix p q σ ω)) = fun _ => 0 := by
      funext ω
      exact hzero ω
    have hconst : 0 ≤ 2 * Real.log 2 + 4 / lam := by
      have hlog2 : 0 ≤ Real.log 2 := le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
      have hnonneg2 : 0 ≤ 4 / lam := by
        positivity
      nlinarith
    rw [hfun]
    simp
    exact hconst
  · have hDpos : 0 < bipartiteDimension p q := by
      have hDnonneg : 0 ≤ bipartiteDimension p q := bipartiteDimension_nonneg
      have hDne : bipartiteDimension p q ≠ 0 := hD0
      exact lt_of_le_of_ne hDnonneg (ne_comm.mp hDne)
    have hDge1 : (1 : ℝ) ≤ bipartiteDimension p q := by
      have hcardpos : 0 < Fintype.card (RandomMatrixModel.BipIndex p q) := by
        have hcardne : Fintype.card (RandomMatrixModel.BipIndex p q) ≠ 0 := by
          intro hzero
          exact hD0 (by simpa [bipartiteDimension, hzero])
        exact Nat.pos_of_ne_zero hcardne
      have hnat : 1 ≤ Fintype.card (RandomMatrixModel.BipIndex p q) :=
        Nat.succ_le_of_lt hcardpos
      unfold bipartiteDimension
      exact_mod_cast hnat
    have hsle : lam ≤ sampleDimension σ := by
      have hmul : lam ≤ lam * bipartiteDimension p q := by
        have hnonneg : 0 ≤ lam := le_of_lt hlam
        have hmul' : lam * 1 ≤ lam * bipartiteDimension p q := by
          exact mul_le_mul_of_nonneg_left hDge1 hnonneg
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul'
      exact le_trans hmul hRatio
    have hspos : 0 < sampleDimension σ := lt_of_lt_of_le hlam hsle
    have hGen :=
      gaussianDiagonalGammaMaxMean_le_of_sampleDimension_pos
        (p := p) (q := q) (σ := σ) hspos
    have hDover : bipartiteDimension p q / sampleDimension σ ≤ 1 / lam := by
      rw [div_le_div_iff₀ hspos hlam]
      simpa [mul_comm] using hRatio
    have hTwoDover : 2 * bipartiteDimension p q / sampleDimension σ ≤ 2 / lam := by
      have hnonneg : 0 ≤ (2 : ℝ) := by positivity
      have hmul : 2 * (bipartiteDimension p q / sampleDimension σ) ≤
          2 * (1 / lam) := by
        exact mul_le_mul_of_nonneg_left hDover hnonneg
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
    have hTwoOver : 2 / sampleDimension σ ≤ 2 / lam := by
      have h1 : 1 / sampleDimension σ ≤ 1 / lam := one_div_le_one_div_of_le hlam hsle
      have hnonneg : 0 ≤ (2 : ℝ) := by positivity
      have hmul : 2 * (1 / sampleDimension σ) ≤ 2 * (1 / lam) := by
        exact mul_le_mul_of_nonneg_left h1 hnonneg
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
    have hsum :
        2 * bipartiteDimension p q / sampleDimension σ +
          2 / sampleDimension σ ≤
        4 / lam := by
      have hsum' :
          2 * bipartiteDimension p q / sampleDimension σ +
            2 / sampleDimension σ ≤
          2 / lam + 2 / lam := by
        exact add_le_add hTwoDover hTwoOver
      have hsumEq : (2 / lam + 2 / lam) = 4 / lam := by
        field_simp [ne_of_gt hlam]
        ring
      calc
        2 * bipartiteDimension p q / sampleDimension σ +
            2 / sampleDimension σ ≤
          2 / lam + 2 / lam := hsum'
        _ = 4 / lam := hsumEq
    calc
      gaussianDiagonalGammaMaxMean (p := p) (q := q) (σ := σ)
          ≤ 2 * Real.log 2 +
              2 * bipartiteDimension p q / sampleDimension σ +
              2 / sampleDimension σ := hGen
      _ ≤ 2 * Real.log 2 + 4 / lam := by
          nlinarith [hsum]

/-- The corresponding Appendix-facing diagonal Wishart/Gamma expectation bound. -/
theorem gaussianWishartGammaDiagonalOpNormMean_le_C_lambda
    {lam : ℝ} (hlam : 0 < lam)
    (hRatio : lam * bipartiteDimension p q ≤ sampleDimension σ) :
    gaussianWishartGammaDiagonalOpNormMean (p := p) (q := q) (σ := σ) ≤
      2 * Real.log 2 + 4 / lam := by
  rw [gaussianWishartGammaDiagonalOpNormMean_eq_diagonalGammaMaxMean]
  exact gaussianDiagonalGammaMaxMean_le_C_lambda
    (p := p) (q := q) (σ := σ) hlam hRatio

/-- Diagonal Gamma bound plugged into the full diagonal/off-diagonal Wishart
expectation pipeline. -/
theorem wishartGammaExpectation_from_diagonalGammaMax_and_offDiagonal
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
    (hGamma :
      gaussianDiagonalGammaMaxMean (p := p) (q := q) (σ := σ) ≤ CDiag) :
    gaussianWishartGammaOpNormMean (p := p) (q := q) (σ := σ) ≤
      CDiag + COff := by
  exact wishartGammaExpectation_from_diagonal_and_offDiagonal
    (p := p) (q := q) (σ := σ) (Q := Q) (dNat := dNat)
    (d := d) (s := s) H hFull hDiagInt hOffInt
    (gaussianWishartGammaDiagonalOpNormMean_le_of_diagonalGammaMaxMean_le
      (p := p) (q := q) (σ := σ) hGamma)

end AppendixB
end PptFactorization
