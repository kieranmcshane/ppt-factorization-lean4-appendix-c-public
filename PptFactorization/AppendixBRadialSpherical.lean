import PptFactorization.HighProbabilityBounds
import Mathlib.Probability.Independence.Integration

/-!
# Radial/spherical factorization interface for Appendix B

This file isolates the radial/spherical normalization step used in Appendix B.

It proves the algebraic radial decompositions for the concrete Gaussian sample
matrix and the exact integral factorization that follows from independence of
the radius and direction.  The remaining genuinely analytic statement is the
Gaussian polar independence theorem itself; it is intentionally not hidden here.
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

instance instSampleMatrixMeasurableSpace :
    MeasurableSpace (SampleMatrix p q σ) :=
  borel (SampleMatrix p q σ)

instance instSampleMatrixBorelSpace :
    BorelSpace (SampleMatrix p q σ) :=
  ⟨rfl⟩

/-! ## Concrete radius and direction -/

omit [DecidableEq p] [DecidableEq q] in
/-- Flatten a sample matrix into the corresponding complex Euclidean vector of
all its entries, with the Frobenius norm on matrices matching the Euclidean
norm on the flattened vector. -/
def sampleMatrixComplexLinearIsometryEquiv :
    SampleMatrix p q σ ≃ₗᵢ[ℂ] EuclideanSpace ℂ (SampleCoord p q σ) := by
  refine LinearIsometryEquiv.mk ?_ ?_
  · refine
      { toFun := fun G => WithLp.toLp 2 (fun a : SampleCoord p q σ => G a.1 a.2)
        invFun := fun z i α => z (i, α)
        left_inv := by
          intro G
          exact Matrix.ext fun i α => rfl
        right_inv := by
          intro z
          ext a
          rfl
        map_add' := by
          intro G H
          ext a
          rfl
        map_smul' := by
          intro c G
          ext a
          rfl }
  · intro G
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
    rw [EuclideanSpace.norm_sq_eq, Matrix.frobenius_norm_def]
    rw [← Real.sqrt_eq_rpow]
    rw [Real.sq_sqrt]
    · rw [← Finset.univ_product_univ]
      rw [Finset.sum_product]
      simp
    · exact Finset.sum_nonneg fun i _ =>
        Finset.sum_nonneg fun α _ => by positivity

/-- Gaussian Frobenius radius `R = ‖G‖₂`. -/
def gaussianRadius : Ω p q σ → ℝ :=
  fun ω => frobeniusNorm (gaussianMatrix p q σ ω)

/-- Squared Gaussian radius `R² = ‖G‖₂² = T`. -/
def gaussianRadiusSq : Ω p q σ → ℝ :=
  fun ω => gaussianRadius (p := p) (q := q) (σ := σ) ω ^ 2

/-- Gaussian direction `X = G / ‖G‖₂`, using the repo's total normalization at
the zero sample. -/
def gaussianDirection : Ω p q σ → SampleMatrix p q σ :=
  fun ω => normalizedSample (gaussianMatrix p q σ ω)

/-- The spherical law induced by the Gaussian direction.  This is the concrete
probability law of `G / ‖G‖₂` in the repo model. -/
def gaussianSphericalSampleMeasure : Measure (SampleMatrix p q σ) :=
  (gaussianMeasure p q σ).map
    (gaussianDirection (p := p) (q := q) (σ := σ))

omit [DecidableEq p] [DecidableEq q] in
theorem measurable_normalizedSample :
    Measurable (normalizedSample (p := p) (q := q) (σ := σ)) := by
  unfold normalizedSample frobeniusNorm
  fun_prop

omit [DecidableEq p] [DecidableEq q] in
theorem measurable_gaussianRadius :
    Measurable (gaussianRadius (p := p) (q := q) (σ := σ)) := by
  unfold gaussianRadius frobeniusNorm gaussianMatrix GaussianModel.gaussianSampleMatrix
    GaussianModel.sampleMatrixOfRealCoordinates
  fun_prop

omit [DecidableEq p] [DecidableEq q] in
theorem measurable_gaussianRadiusSq :
    Measurable (gaussianRadiusSq (p := p) (q := q) (σ := σ)) := by
  unfold gaussianRadiusSq
  exact measurable_gaussianRadius.pow_const 2

omit [DecidableEq p] [DecidableEq q] in
theorem measurable_gaussianDirection :
    Measurable (gaussianDirection (p := p) (q := q) (σ := σ)) := by
  unfold gaussianDirection normalizedSample frobeniusNorm gaussianMatrix
    GaussianModel.gaussianSampleMatrix GaussianModel.sampleMatrixOfRealCoordinates
  measurability

omit [DecidableEq p] [DecidableEq q] in
theorem measurable_gaussianMatrix :
    Measurable (gaussianMatrix p q σ) := by
  have hcont : Continuous (gaussianMatrix p q σ) := by
    unfold gaussianMatrix GaussianModel.gaussianSampleMatrix
      GaussianModel.sampleMatrixOfRealCoordinates
    exact continuous_pi fun i => continuous_pi fun α => by
      fun_prop
  exact hcont.measurable

omit [DecidableEq p] [DecidableEq q] in
/-- Complex linear isometries commute with radial normalization. -/
theorem normalizedSample_map_complexLinearIsometryEquiv
    (U : SampleMatrix p q σ ≃ₗᵢ[ℂ] SampleMatrix p q σ)
    (G : SampleMatrix p q σ) :
    normalizedSample (p := p) (q := q) (σ := σ) (U G) =
      U (normalizedSample (p := p) (q := q) (σ := σ) G) := by
  unfold normalizedSample frobeniusNorm
  simp

omit [DecidableEq p] [DecidableEq q] in
/-- Any complex-linear isometric action preserving a measure on sample matrices
also preserves its pushforward by radial normalization.  This is the exact
intertwining statement used in the Gaussian direction-law invariance argument. -/
theorem normalizedSample_pushforward_map_complexLinearIsometryEquiv_of_map_eq
    {μ : Measure (SampleMatrix p q σ)}
    (U : SampleMatrix p q σ ≃ₗᵢ[ℂ] SampleMatrix p q σ)
    (hU : Measure.map U μ = μ) :
    Measure.map U
        ((μ).map (normalizedSample (p := p) (q := q) (σ := σ))) =
      (μ).map (normalizedSample (p := p) (q := q) (σ := σ)) := by
  calc
    Measure.map U
        ((μ).map (normalizedSample (p := p) (q := q) (σ := σ))) =
      Measure.map U
        ((μ).map (normalizedSample (p := p) (q := q) (σ := σ))) := rfl
    _ =
      Measure.map
        ((fun G : SampleMatrix p q σ =>
            U (normalizedSample (p := p) (q := q) (σ := σ) G)))
        μ := by
        simpa [Function.comp] using
          (Measure.map_map
            (μ := μ)
            (f := normalizedSample (p := p) (q := q) (σ := σ))
            (g := U)
            U.continuous.measurable
            (measurable_normalizedSample (p := p) (q := q) (σ := σ)))
    _ =
      Measure.map
        ((fun G : SampleMatrix p q σ =>
            normalizedSample (p := p) (q := q) (σ := σ) (U G)))
        μ := by
        congr 1
        ext G i j
        exact congrArg (fun M => M i j)
          ((normalizedSample_map_complexLinearIsometryEquiv
            (p := p) (q := q) (σ := σ) U G).symm)
    _ =
      Measure.map
        (normalizedSample (p := p) (q := q) (σ := σ))
        (Measure.map U μ) := by
        simpa [Function.comp] using
          (Measure.map_map
            (μ := μ)
            (f := U)
            (g := normalizedSample (p := p) (q := q) (σ := σ))
            (measurable_normalizedSample (p := p) (q := q) (σ := σ))
            U.continuous.measurable).symm
    _ =
      Measure.map
        (normalizedSample (p := p) (q := q) (σ := σ))
        μ := by
        rw [hU]

omit [DecidableEq p] [DecidableEq q] in
/-- The Gaussian direction law is a probability measure: it is the push-forward
of the concrete Gaussian sample measure by `G ↦ G / ‖G‖₂`. -/
theorem gaussianDirection_law_isProbabilityMeasure :
    IsProbabilityMeasure
      (gaussianSphericalSampleMeasure (p := p) (q := q) (σ := σ)) := by
  haveI : IsProbabilityMeasure (gaussianMeasure p q σ) := by
    rw [gaussianMeasure_eq]
    infer_instance
  exact Measure.isProbabilityMeasure_map
    (measurable_gaussianDirection (p := p) (q := q) (σ := σ)).aemeasurable

omit [DecidableEq p] [DecidableEq q] in
/-- The ambient law of the concrete Gaussian sample matrix is invariant under
every complex linear isometric equivalence of the sample-matrix Hilbert space. -/
theorem gaussianMatrixLaw_map_complexLinearIsometryEquiv
    (U : SampleMatrix p q σ ≃ₗᵢ[ℂ] SampleMatrix p q σ) :
    Measure.map U
        ((gaussianMeasure p q σ).map (gaussianMatrix p q σ)) =
      (gaussianMeasure p q σ).map (gaussianMatrix p q σ) := by
  let μG : Measure (SampleMatrix p q σ) :=
    (gaussianMeasure p q σ).map (gaussianMatrix p q σ)
  let Φ : SampleMatrix p q σ ≃ₗᵢ[ℂ] EuclideanSpace ℂ (SampleCoord p q σ) :=
    sampleMatrixComplexLinearIsometryEquiv (p := p) (q := q) (σ := σ)
  let V : EuclideanSpace ℂ (SampleCoord p q σ) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (SampleCoord p q σ) :=
    (Φ.symm.trans U).trans Φ
  have hLaw :
      μG =
        Measure.map Φ.symm
          (standardComplexGaussianVectorMeasure (SampleCoord p q σ)) := by
    unfold μG
    have hflat :
        sampleMatrixOfRealCoordinates =
          (fun ω : GaussianSampleSpace p q σ =>
            Φ.symm (complexVectorOfRealCoordinates (ι := SampleCoord p q σ) ω)) := by
      funext ω
      exact Matrix.ext fun i α => rfl
    rw [gaussianMeasure_eq]
    unfold gaussianMatrix GaussianModel.gaussianSampleMeasure
      GaussianModel.gaussianSampleMatrix GaussianModel.sampleMatrixOfRealCoordinates
      standardComplexGaussianVectorMeasure
    calc
      Measure.map sampleMatrixOfRealCoordinates
          (ProbabilityTheory.stdGaussian (GaussianSampleSpace p q σ)) =
        Measure.map
          (fun ω =>
            Φ.symm
              (complexVectorOfRealCoordinates (ι := SampleCoord p q σ) ω))
          (ProbabilityTheory.stdGaussian (GaussianSampleSpace p q σ)) := by
            rw [hflat]
      _ =
        Measure.map Φ.symm
          (Measure.map
            (complexVectorOfRealCoordinates (ι := SampleCoord p q σ))
            (ProbabilityTheory.stdGaussian (GaussianSampleSpace p q σ))) := by
            symm
            simpa [Function.comp] using
              (Measure.map_map
                (μ := ProbabilityTheory.stdGaussian (GaussianSampleSpace p q σ))
                (f := complexVectorOfRealCoordinates (ι := SampleCoord p q σ))
                (g := Φ.symm)
                Φ.symm.continuous.measurable
                (measurable_complexVectorOfRealCoordinates (ι := SampleCoord p q σ)))
      _ =
        Measure.map Φ.symm
          (standardComplexGaussianVectorMeasure (SampleCoord p q σ)) := by
            rfl
  calc
    Measure.map U ((gaussianMeasure p q σ).map (gaussianMatrix p q σ)) =
      Measure.map U
        (Measure.map Φ.symm
          (standardComplexGaussianVectorMeasure (SampleCoord p q σ))) := by
            simpa [μG] using congrArg (Measure.map U) hLaw
    _ =
      Measure.map (U ∘ Φ.symm)
        (standardComplexGaussianVectorMeasure (SampleCoord p q σ)) := by
          simpa [Function.comp] using
            (Measure.map_map
              (μ := standardComplexGaussianVectorMeasure (SampleCoord p q σ))
              (f := Φ.symm)
              (g := U)
              U.continuous.measurable
              Φ.symm.continuous.measurable)
    _ =
      Measure.map (Φ.symm ∘ V)
        (standardComplexGaussianVectorMeasure (SampleCoord p q σ)) := by
          rfl
    _ =
      Measure.map Φ.symm
        (Measure.map V
          (standardComplexGaussianVectorMeasure (SampleCoord p q σ))) := by
          symm
          simpa [Function.comp] using
            (Measure.map_map
              (μ := standardComplexGaussianVectorMeasure (SampleCoord p q σ))
              (f := V)
              (g := Φ.symm)
              Φ.symm.continuous.measurable
              V.continuous.measurable)
    _ =
      Measure.map Φ.symm
        (standardComplexGaussianVectorMeasure (SampleCoord p q σ)) := by
          rw [standardComplexGaussianVectorMeasure_map_complexLinearIsometryEquiv V]
    _ = (gaussianMeasure p q σ).map (gaussianMatrix p q σ) := by
          simpa [μG] using hLaw.symm

omit [DecidableEq p] [DecidableEq q] in
/-- The Gaussian direction law is invariant under the same complex-linear
isometric action as the canonical surface law. -/
theorem gaussianDirection_law_map_complexLinearIsometryEquiv
    (U : SampleMatrix p q σ ≃ₗᵢ[ℂ] SampleMatrix p q σ) :
    Measure.map U
        (gaussianSphericalSampleMeasure (p := p) (q := q) (σ := σ)) =
      gaussianSphericalSampleMeasure (p := p) (q := q) (σ := σ) := by
  let μG : Measure (SampleMatrix p q σ) :=
    (gaussianMeasure p q σ).map (gaussianMatrix p q σ)
  let νG : Measure (SampleMatrix p q σ) :=
    gaussianSphericalSampleMeasure (p := p) (q := q) (σ := σ)
  have hSphere :
      νG =
        Measure.map (normalizedSample (p := p) (q := q) (σ := σ)) μG := by
    unfold νG μG
    unfold gaussianSphericalSampleMeasure gaussianDirection
    symm
    simpa [Function.comp] using
      (Measure.map_map
        (μ := gaussianMeasure p q σ)
        (f := gaussianMatrix p q σ)
        (g := normalizedSample (p := p) (q := q) (σ := σ))
        (measurable_normalizedSample (p := p) (q := q) (σ := σ))
        (measurable_gaussianMatrix (p := p) (q := q) (σ := σ)))
  calc
    Measure.map U
        (gaussianSphericalSampleMeasure (p := p) (q := q) (σ := σ)) =
      Measure.map U
        (Measure.map (normalizedSample (p := p) (q := q) (σ := σ)) μG) := by
          simpa [νG] using congrArg (Measure.map U) hSphere
    _ =
      Measure.map (normalizedSample (p := p) (q := q) (σ := σ)) μG := by
          exact
            normalizedSample_pushforward_map_complexLinearIsometryEquiv_of_map_eq
              (p := p) (q := q) (σ := σ) (μ := μG) U (by
                simpa [μG] using
                  gaussianMatrixLaw_map_complexLinearIsometryEquiv
                    (p := p) (q := q) (σ := σ) U)
    _ = gaussianSphericalSampleMeasure (p := p) (q := q) (σ := σ) := by
          simpa [νG] using hSphere.symm

omit [DecidableEq p] [DecidableEq q] in
theorem stdGaussian_noAtoms
    {ι : Type*} [Fintype ι] [Nonempty ι] :
    MeasureTheory.NoAtoms (stdGaussian (EuclideanSpace ℝ ι)) := by
  classical
  rw [← map_pi_eq_stdGaussian (ι := ι)]
  let ν : ι → Measure ℝ := fun _ => gaussianReal 0 (1 : NNReal)
  have hν : ∀ i, MeasureTheory.NoAtoms (ν i) := by
    intro i
    simpa [ν] using
      (ProbabilityTheory.noAtoms_gaussianReal
        (μ := (0 : ℝ)) (v := (1 : NNReal)) (by norm_num))
  haveI : MeasureTheory.NoAtoms (Measure.pi ν) := by
    let i0 : ι := Classical.choice ‹Nonempty ι›
    letI : MeasureTheory.NoAtoms (ν i0) := hν i0
    exact Measure.pi_noAtoms (μ := ν) i0
  refine ⟨fun x => ?_⟩
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton x)]
  have hpre :
      (WithLp.toLp 2) ⁻¹' ({x} : Set (EuclideanSpace ℝ ι)) =
        {WithLp.ofLp x} := by
    ext y
    simp [Set.mem_preimage]
    constructor
    · intro hy
      exact congrArg WithLp.ofLp hy
    · intro hy
      simp [hy]
  rw [hpre]
  simp

omit [DecidableEq p] [DecidableEq q] in
theorem complexVectorOfRealCoordinates_injective
    {ι : Type*} [Fintype ι] :
    Function.Injective (complexVectorOfRealCoordinates (ι := ι)) := by
  intro x y hxy
  have hscale : ((complexGaussianScale : ℝ) : ℂ) ≠ 0 := by
    simp [GaussianModel.complexGaussianScale]
  have hxy' :
      ((complexGaussianScale : ℝ) : ℂ) • unscaledComplexVectorOfRealCoordinates x =
        ((complexGaussianScale : ℝ) : ℂ) •
          unscaledComplexVectorOfRealCoordinates y := by
    simpa [complexVectorOfRealCoordinates_eq_smul_unscaled] using hxy
  have hunscaled :
      unscaledComplexVectorOfRealCoordinates x =
        unscaledComplexVectorOfRealCoordinates y := by
    let c : ℂ := ((complexGaussianScale : ℝ) : ℂ)
    have hmul : c⁻¹ * c = 1 := by
      dsimp [c]
      field_simp [hscale]
    have hxy'' :
        c⁻¹ • (c • unscaledComplexVectorOfRealCoordinates x) =
          unscaledComplexVectorOfRealCoordinates y := by
      simpa [c] using (inv_smul_eq_iff₀ hscale).2 hxy'
    calc
      unscaledComplexVectorOfRealCoordinates x =
          (1 : ℂ) • unscaledComplexVectorOfRealCoordinates x := by simp
      _ = (c⁻¹ * c) • unscaledComplexVectorOfRealCoordinates x := by rw [hmul]
      _ = c⁻¹ • (c • unscaledComplexVectorOfRealCoordinates x) := by rw [smul_smul]
      _ = unscaledComplexVectorOfRealCoordinates y := hxy''
  exact (complexRealCoordLinearIsometryEquiv ι).injective hunscaled

omit [DecidableEq p] [DecidableEq q] in
theorem sampleMatrixOfRealCoordinates_injective :
    Function.Injective
      (sampleMatrixOfRealCoordinates (p := p) (q := q) (σ := σ)) := by
  let Φ : SampleMatrix p q σ ≃ₗᵢ[ℂ] EuclideanSpace ℂ (SampleCoord p q σ) :=
    sampleMatrixComplexLinearIsometryEquiv (p := p) (q := q) (σ := σ)
  have hflat :
      sampleMatrixOfRealCoordinates (p := p) (q := q) (σ := σ) =
        fun ω => Φ.symm (complexVectorOfRealCoordinates (ι := SampleCoord p q σ) ω) := by
    funext ω
    exact Matrix.ext fun i α => rfl
  intro x y hxy
  apply complexVectorOfRealCoordinates_injective (ι := SampleCoord p q σ)
  have hxy' := congrArg Φ hxy
  simpa [hflat] using hxy'

omit [DecidableEq p] [DecidableEq q] in
theorem gaussianMeasure_noAtoms
    [Nonempty p] [Nonempty q] [Nonempty σ] :
    MeasureTheory.NoAtoms (gaussianMeasure p q σ) := by
  rw [gaussianMeasure_eq, GaussianModel.gaussianSampleMeasure]
  simpa [GaussianModel.GaussianSampleSpace, GaussianModel.ComplexRealCoordSpace] using
    (stdGaussian_noAtoms (ι := SampleCoord p q σ × Fin 2))

omit [DecidableEq p] [DecidableEq q] in
theorem gaussianMatrix_injective :
    Function.Injective (gaussianMatrix p q σ) := by
  simpa [gaussianMatrix, GaussianModel.gaussianSampleMatrix] using
    sampleMatrixOfRealCoordinates_injective (p := p) (q := q) (σ := σ)

omit [DecidableEq p] [DecidableEq q] in
theorem normalizedSample_mem_sphere_of_ne_zero
    {G : SampleMatrix p q σ} (hG : G ≠ 0) :
    normalizedSample (p := p) (q := q) (σ := σ) G ∈
      Metric.sphere (0 : SampleMatrix p q σ) 1 := by
  have hpos : 0 < ‖G‖ := norm_pos_iff.mpr hG
  rw [Metric.mem_sphere, normalizedSample, frobeniusNorm]
  rw [dist_eq_norm]
  simp only [sub_zero]
  rw [norm_smul]
  have hnorm : ‖((((‖G‖ : ℝ) : ℂ)⁻¹) : ℂ)‖ = (‖G‖)⁻¹ := by
    simp
  rw [hnorm]
  field_simp [hpos.ne']

omit [DecidableEq p] [DecidableEq q] in
theorem gaussianDirection_preimage_sphere_compl_subset :
    (gaussianDirection (p := p) (q := q) (σ := σ)) ⁻¹'
        (Metric.sphere (0 : SampleMatrix p q σ) 1)ᶜ ⊆
      {ω : Ω p q σ | gaussianMatrix p q σ ω = 0} := by
  intro ω hω
  by_contra hω0
  exact hω (normalizedSample_mem_sphere_of_ne_zero
    (p := p) (q := q) (σ := σ) hω0)

omit [DecidableEq p] [DecidableEq q] in
theorem gaussianDirection_law_sphere
    [Nonempty p] [Nonempty q] [Nonempty σ] :
    gaussianSphericalSampleMeasure (p := p) (q := q) (σ := σ)
        (Metric.sphere (0 : SampleMatrix p q σ) 1) = 1 := by
  have hcomp :
      gaussianSphericalSampleMeasure (p := p) (q := q) (σ := σ)
          (Metric.sphere (0 : SampleMatrix p q σ) 1)ᶜ = 0 := by
    have hzeroMatrix :
        sampleMatrixOfRealCoordinates (p := p) (q := q) (σ := σ) 0 = 0 := by
      ext i α
      simp [GaussianModel.sampleMatrixOfRealCoordinates, GaussianModel.complexGaussianScale]
    have hsingleton :
        {ω : Ω p q σ | gaussianMatrix p q σ ω = 0} = {0} := by
      ext ω
      constructor
      · intro hω
        have : ω = 0 := by
          have h0 : gaussianMatrix p q σ 0 = 0 := by
            simpa [gaussianMatrix, GaussianModel.gaussianSampleMatrix] using hzeroMatrix
          exact gaussianMatrix_injective (p := p) (q := q) (σ := σ) (hω.trans h0.symm)
        simp [this]
      · intro hω
        rcases Set.mem_singleton_iff.mp hω with rfl
        simpa [gaussianMatrix, GaussianModel.gaussianSampleMatrix] using hzeroMatrix
    unfold gaussianSphericalSampleMeasure
    rw [Measure.map_apply
      (measurable_gaussianDirection (p := p) (q := q) (σ := σ))
      (Metric.isClosed_sphere.measurableSet.compl)]
    haveI : MeasureTheory.NoAtoms (gaussianMeasure p q σ) :=
      gaussianMeasure_noAtoms (p := p) (q := q) (σ := σ)
    have hnull :
        gaussianMeasure p q σ {ω : Ω p q σ | gaussianMatrix p q σ ω = 0} = 0 := by
      have hsingleton' :
          ({ω : Ω p q σ | sampleMatrixOfRealCoordinates (p := p) (q := q) (σ := σ) ω = 0} :
            Set (Ω p q σ)) = {0} := by
        simpa [gaussianMatrix, GaussianModel.gaussianSampleMatrix] using hsingleton
      simpa [gaussianMeasure_eq, GaussianModel.gaussianSampleMeasure, gaussianMatrix,
        GaussianModel.gaussianSampleMatrix, hsingleton'] using
        (MeasureTheory.measure_singleton (μ := gaussianMeasure p q σ) (0 : Ω p q σ))
    exact measure_mono_null
      (gaussianDirection_preimage_sphere_compl_subset
        (p := p) (q := q) (σ := σ))
      hnull
  haveI :
      IsProbabilityMeasure
        (gaussianSphericalSampleMeasure (p := p) (q := q) (σ := σ)) :=
    gaussianDirection_law_isProbabilityMeasure (p := p) (q := q) (σ := σ)
  simpa using measure_of_measure_compl_eq_zero hcomp

omit [DecidableEq p] [DecidableEq q] in
/-- The Gaussian direction law, viewed directly as a probability measure on the
unit-sphere subtype. -/
def gaussianSphericalSubtypeMeasure :
    Measure (Metric.sphere (0 : SampleMatrix p q σ) 1) :=
  (gaussianSphericalSampleMeasure (p := p) (q := q) (σ := σ)).comap Subtype.val

omit [DecidableEq p] [DecidableEq q] in
/-- The subtype Gaussian direction law has total mass one. -/
theorem gaussianSphericalSubtypeMeasure_apply_univ
    [Nonempty p] [Nonempty q] [Nonempty σ] :
    gaussianSphericalSubtypeMeasure (p := p) (q := q) (σ := σ) Set.univ = 1 := by
  unfold gaussianSphericalSubtypeMeasure
  rw [Measure.comap_apply Subtype.val Subtype.val_injective]
  · simpa [Metric.sphere] using gaussianDirection_law_sphere (p := p) (q := q) (σ := σ)
  · intro s hs
    have himage :
        MeasurableSet
          (((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ) '' s) :=
      (MeasurableEmbedding.subtype_coe
        (Metric.isClosed_sphere.measurableSet :
          MeasurableSet (Metric.sphere (0 : SampleMatrix p q σ) 1))).measurableSet_image' hs
    exact himage
  · simp

omit [DecidableEq p] [DecidableEq q] in
/-- The Gaussian direction law on the sphere subtype is a probability measure. -/
theorem gaussianSphericalSubtypeMeasure_isProbabilityMeasure
    [Nonempty p] [Nonempty q] [Nonempty σ] :
    IsProbabilityMeasure
      (gaussianSphericalSubtypeMeasure (p := p) (q := q) (σ := σ)) := by
  refine ⟨gaussianSphericalSubtypeMeasure_apply_univ
    (p := p) (q := q) (σ := σ)⟩

omit [DecidableEq p] [DecidableEq q] in
@[simp] theorem gaussianRadiusSq_eq_gaussianMass
    (ω : Ω p q σ) :
    gaussianRadiusSq (p := p) (q := q) (σ := σ) ω =
      gaussianMass p q σ ω := by
  simp [gaussianRadiusSq, gaussianRadius, gaussianMass, frobeniusMass]

/-! ## Deterministic radial algebra -/

omit [DecidableEq p] [DecidableEq q] in
/-- Homogeneity of the rectangular operator norm. -/
theorem sampleOpNorm_smul (c : ℂ) (G : SampleMatrix p q σ) :
    sampleOpNorm (p := p) (q := q) (σ := σ) (c • G) =
      ‖c‖ * sampleOpNorm (p := p) (q := q) (σ := σ) G := by
  simp [sampleOpNorm, Matrix.toEuclideanLin, norm_smul]

omit [DecidableEq p] [DecidableEq q] in
/-- Pointwise radial decomposition of the sample operator norm:
`‖G‖∞ = R ‖G/R‖∞`. -/
theorem sampleOpNorm_eq_radius_mul_normalized
    (G : SampleMatrix p q σ) :
    sampleOpNorm (p := p) (q := q) (σ := σ) G =
      frobeniusNorm G *
        sampleOpNorm (p := p) (q := q) (σ := σ) (normalizedSample G) := by
  by_cases hG : G = 0
  · simp [hG, normalizedSample, frobeniusNorm, sampleOpNorm]
  · have hnorm_ne : frobeniusNorm G ≠ 0 := by
      simp [frobeniusNorm, hG]
    have hnorm_nonneg : 0 ≤ frobeniusNorm G := by
      unfold frobeniusNorm
      positivity
    have hnorm_inv :
        ‖((frobeniusNorm G : ℂ)⁻¹)‖ = (frobeniusNorm G)⁻¹ := by
      have h := Complex.norm_of_nonneg (inv_nonneg.mpr hnorm_nonneg)
      simpa using h
    rw [normalizedSample, sampleOpNorm_smul, hnorm_inv]
    field_simp [hnorm_ne]

omit [DecidableEq p] [DecidableEq q] in
/-- Pointwise sample-operator radial factorization for the concrete Gaussian
matrix. -/
theorem gaussian_sampleOpNorm_pointwise_radial
    (ω : Ω p q σ) :
    sampleOpNorm (p := p) (q := q) (σ := σ)
        (gaussianMatrix p q σ ω) =
      gaussianRadius (p := p) (q := q) (σ := σ) ω *
        sampleOpNorm (p := p) (q := q) (σ := σ)
          (gaussianDirection (p := p) (q := q) (σ := σ) ω) := by
  simpa [gaussianRadius, gaussianDirection] using
    sampleOpNorm_eq_radius_mul_normalized
      (p := p) (q := q) (σ := σ) (gaussianMatrix p q σ ω)

/-! ## Integral factorization from radius-direction independence -/

/-- Generic radial/spherical integral factorization.

This is the exact probabilistic step used by Appendix B: once `R` and `X`
are independent, expectations of products `R * F(X)` split. -/
theorem radial_spherical_integral_factorization_of_indep
    {Ω₀ S : Type*} [MeasurableSpace Ω₀] [MeasurableSpace S]
    {μ : Measure Ω₀} {R : Ω₀ → ℝ} {X : Ω₀ → S} {F : S → ℝ}
    (hIndep : R ⟂ᵢ[μ] X)
    (hR : AEMeasurable R μ)
    (hX : AEMeasurable X μ)
    (hF : AEStronglyMeasurable F (μ.map X)) :
    ∫ ω, R ω * F (X ω) ∂μ =
      (∫ ω, R ω ∂μ) * (∫ x, F x ∂(μ.map X)) := by
  rw [MeasureTheory.integral_map hX hF]
  have h := hIndep.integral_fun_comp_mul_comp hR hX
    (aestronglyMeasurable_id :
      AEStronglyMeasurable (fun x : ℝ => x) (μ.map R)) hF
  simpa using h

omit [DecidableEq p] [DecidableEq q] in
/-- Radius-direction independence automatically gives the corresponding
radius-squared/direction independence by composing the radial variable with
`r ↦ r^2`. -/
theorem gaussianRadiusSq_indep_gaussianDirection_of_gaussianRadius_indep
    (hIndep :
      gaussianRadius (p := p) (q := q) (σ := σ) ⟂ᵢ[gaussianMeasure p q σ]
        gaussianDirection (p := p) (q := q) (σ := σ)) :
    gaussianRadiusSq (p := p) (q := q) (σ := σ) ⟂ᵢ[gaussianMeasure p q σ]
      gaussianDirection (p := p) (q := q) (σ := σ) := by
  have h :=
    hIndep.comp
      ((measurable_id : Measurable (fun r : ℝ => r)).pow_const 2)
      measurable_id
  simpa [gaussianRadiusSq, Function.comp_def] using h

omit [DecidableEq p] [DecidableEq q] in
/-- Sample-operator expectation factorization, conditional only on the genuine
Gaussian polar-independence statement `R ⟂ X`. -/
theorem gaussian_sampleOpNorm_expectation_factorization_of_indep
    (hIndep :
      gaussianRadius (p := p) (q := q) (σ := σ) ⟂ᵢ[gaussianMeasure p q σ]
        gaussianDirection (p := p) (q := q) (σ := σ)) :
    ∫ ω : Ω p q σ,
        sampleOpNorm (p := p) (q := q) (σ := σ)
          (gaussianMatrix p q σ ω) ∂gaussianMeasure p q σ =
      (∫ ω : Ω p q σ,
          gaussianRadius (p := p) (q := q) (σ := σ) ω
          ∂gaussianMeasure p q σ) *
        (∫ X : SampleMatrix p q σ,
          sampleOpNorm (p := p) (q := q) (σ := σ) X
          ∂gaussianSphericalSampleMeasure (p := p) (q := q) (σ := σ)) := by
  have hpoint :
      (fun ω : Ω p q σ =>
        sampleOpNorm (p := p) (q := q) (σ := σ)
          (gaussianMatrix p q σ ω)) =
        fun ω =>
          gaussianRadius (p := p) (q := q) (σ := σ) ω *
            sampleOpNorm (p := p) (q := q) (σ := σ)
              (gaussianDirection (p := p) (q := q) (σ := σ) ω) := by
    funext ω
    exact gaussian_sampleOpNorm_pointwise_radial (p := p) (q := q) (σ := σ) ω
  rw [hpoint]
  exact radial_spherical_integral_factorization_of_indep
    (μ := gaussianMeasure p q σ)
    (R := gaussianRadius (p := p) (q := q) (σ := σ))
    (X := gaussianDirection (p := p) (q := q) (σ := σ))
    (F := sampleOpNorm (p := p) (q := q) (σ := σ))
    hIndep
    measurable_gaussianRadius.aemeasurable
    measurable_gaussianDirection.aemeasurable
    (sampleOpNorm_continuous (p := p) (q := q) (σ := σ)).aestronglyMeasurable

omit [DecidableEq p] [DecidableEq q] in
/-- Quadratic radial/spherical factorization.  This is the form needed for
Wishart/Gamma observables, whose Gaussian lift is homogeneous of degree two. -/
theorem gaussian_quadratic_radial_spherical_factorization_of_indep
    {F : SampleMatrix p q σ → ℝ}
    (hIndep :
      gaussianRadiusSq (p := p) (q := q) (σ := σ) ⟂ᵢ[gaussianMeasure p q σ]
        gaussianDirection (p := p) (q := q) (σ := σ))
    (hF :
      AEStronglyMeasurable F
        (gaussianSphericalSampleMeasure (p := p) (q := q) (σ := σ))) :
    ∫ ω : Ω p q σ,
        gaussianMass p q σ ω *
          F (gaussianDirection (p := p) (q := q) (σ := σ) ω)
        ∂gaussianMeasure p q σ =
      (∫ ω : Ω p q σ, gaussianMass p q σ ω ∂gaussianMeasure p q σ) *
        (∫ X : SampleMatrix p q σ,
          F X ∂gaussianSphericalSampleMeasure (p := p) (q := q) (σ := σ)) := by
  have hmass :
      (fun ω : Ω p q σ => gaussianMass p q σ ω) =
        gaussianRadiusSq (p := p) (q := q) (σ := σ) := by
    funext ω
    exact (gaussianRadiusSq_eq_gaussianMass (p := p) (q := q) (σ := σ) ω).symm
  rw [hmass]
  exact radial_spherical_integral_factorization_of_indep
    (μ := gaussianMeasure p q σ)
    (R := gaussianRadiusSq (p := p) (q := q) (σ := σ))
    (X := gaussianDirection (p := p) (q := q) (σ := σ))
    (F := F)
    hIndep
    measurable_gaussianRadiusSq.aemeasurable
    measurable_gaussianDirection.aemeasurable
    hF

end AppendixB
end PptFactorization
