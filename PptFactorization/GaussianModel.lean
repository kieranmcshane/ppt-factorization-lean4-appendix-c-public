import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import PptFactorization.RandomMatrixModel

/-!
# Concrete Gaussian probability model for the PPT matrix sample

This file builds the finite-dimensional probability space used by the
high-dimensional-probability argument from Mathlib's real multivariate
Gaussian measure.

Convention: a standard complex Gaussian has real and imaginary parts with
variance `1/2`.  We realize this using real Gaussian coordinates indexed by
`ι × Fin 2`, scaled by `1 / sqrt 2`; coordinate `0` is the real part and
coordinate `1` is the imaginary part.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.Frobenius RealInnerProductSpace

noncomputable section

namespace PptFactorization
namespace GaussianModel

open RandomMatrixModel

/-- The real scale turning two real `N(0,1)` coordinates into one standard
complex Gaussian coordinate with real/imaginary variances `1/2`. -/
def complexGaussianScale : ℝ :=
  (Real.sqrt 2)⁻¹

/-- Real coordinate space used to realize a standard complex Gaussian vector. -/
abbrev ComplexRealCoordSpace (ι : Type*) :=
  EuclideanSpace ℝ (ι × Fin 2)

/-- Convert real coordinates `(x₀, x₁)` into the complex coordinate
`(x₀ + i x₁) / sqrt 2`. -/
def complexVectorOfRealCoordinates {ι : Type*} [Fintype ι]
    (x : ComplexRealCoordSpace ι) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2
    (fun i : ι =>
      ((complexGaussianScale * x (i, 0) : ℝ) : ℂ) +
        ((complexGaussianScale * x (i, 1) : ℝ) : ℂ) * Complex.I)

@[fun_prop]
theorem measurable_complexVectorOfRealCoordinates
    (ι : Type*) [Fintype ι] :
    Measurable (complexVectorOfRealCoordinates (ι := ι)) := by
  unfold complexVectorOfRealCoordinates
  fun_prop

/-- Standard complex Gaussian vector measure, constructed as the push-forward
of Mathlib's real standard Gaussian on real/imaginary coordinates. -/
def standardComplexGaussianVectorMeasure (ι : Type*) [Fintype ι] :
    Measure (EuclideanSpace ℂ ι) :=
  (stdGaussian (ComplexRealCoordSpace ι)).map
    (complexVectorOfRealCoordinates (ι := ι))

instance instIsProbabilityMeasureStandardComplexGaussianVectorMeasure
    (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (standardComplexGaussianVectorMeasure ι) := by
  unfold standardComplexGaussianVectorMeasure
  exact Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))

/-- Flattened coordinate index for all entries of the sample matrix. -/
abbrev SampleCoord (p q σ : Type*) :=
  RandomMatrixModel.BipIndex p q × σ

/-- Real coordinate space carrying all real and imaginary parts of the sample matrix. -/
abbrev GaussianSampleSpace (p q σ : Type*) :=
  ComplexRealCoordSpace (SampleCoord p q σ)

/-- The concrete probability measure for the Gaussian sample matrix. -/
def gaussianSampleMeasure (p q σ : Type*) [Fintype p] [Fintype q] [Fintype σ] :
    Measure (GaussianSampleSpace p q σ) :=
  stdGaussian (GaussianSampleSpace p q σ)

instance instIsProbabilityMeasureGaussianSampleMeasure
    (p q σ : Type*) [Fintype p] [Fintype q] [Fintype σ] :
    IsProbabilityMeasure (gaussianSampleMeasure p q σ) := by
  unfold gaussianSampleMeasure
  infer_instance

/-- Turn real Gaussian coordinates into the corresponding complex sample matrix. -/
def sampleMatrixOfRealCoordinates
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    (x : GaussianSampleSpace p q σ) :
    SampleMatrix p q σ :=
  fun i α =>
    ((complexGaussianScale * x ((i, α), 0) : ℝ) : ℂ) +
      ((complexGaussianScale * x ((i, α), 1) : ℝ) : ℂ) * Complex.I

/-- The random Gaussian sample matrix `G` on the canonical probability space. -/
def gaussianSampleMatrix
    (p q σ : Type*) [Fintype p] [Fintype q] [Fintype σ] :
    RandomSampleMatrix (GaussianSampleSpace p q σ) p q σ :=
  sampleMatrixOfRealCoordinates

/-- Column `α` of a sample matrix, as a vector in `ℂ^(p×q)`. -/
def columnVector
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    (G : SampleMatrix p q σ) (α : σ) :
    EuclideanSpace ℂ (RandomMatrixModel.BipIndex p q) :=
  WithLp.toLp 2 (fun i => G i α)

/-- The random column `g_α` of the canonical Gaussian sample matrix. -/
def gaussianColumn
    (p q σ : Type*) [Fintype p] [Fintype q] [Fintype σ] (α : σ) :
    GaussianSampleSpace p q σ → EuclideanSpace ℂ (RandomMatrixModel.BipIndex p q) :=
  fun x => columnVector (gaussianSampleMatrix p q σ x) α

@[simp] theorem complexVectorOfRealCoordinates_apply
    {ι : Type*} [Fintype ι] (x : ComplexRealCoordSpace ι) (i : ι) :
    complexVectorOfRealCoordinates (ι := ι) x i =
      ((complexGaussianScale * x (i, 0) : ℝ) : ℂ) +
        ((complexGaussianScale * x (i, 1) : ℝ) : ℂ) * Complex.I :=
  rfl

@[simp] theorem sampleMatrixOfRealCoordinates_apply
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    (x : GaussianSampleSpace p q σ) (i : RandomMatrixModel.BipIndex p q) (α : σ) :
    sampleMatrixOfRealCoordinates (p := p) (q := q) (σ := σ) x i α =
      ((complexGaussianScale * x ((i, α), 0) : ℝ) : ℂ) +
        ((complexGaussianScale * x ((i, α), 1) : ℝ) : ℂ) * Complex.I :=
  rfl

@[simp] theorem gaussianSampleMatrix_apply
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    (x : GaussianSampleSpace p q σ) :
    gaussianSampleMatrix p q σ x =
      sampleMatrixOfRealCoordinates (p := p) (q := q) (σ := σ) x :=
  rfl

@[simp] theorem columnVector_apply
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    (G : SampleMatrix p q σ) (α : σ)
    (i : RandomMatrixModel.BipIndex p q) :
    columnVector G α i = G i α :=
  rfl

/-- The ambient probability space and random matrix packaged together. -/
structure ComplexGaussianMatrixModel (p q σ : Type*) [Fintype p] [Fintype q] [Fintype σ] where
  Ω : Type*
  measurableSpace : MeasurableSpace Ω
  μ : Measure Ω
  isProbability : IsProbabilityMeasure μ
  G : RandomSampleMatrix Ω p q σ

attribute [instance] ComplexGaussianMatrixModel.measurableSpace
attribute [instance] ComplexGaussianMatrixModel.isProbability

/-- The canonical concrete model with real Gaussian coordinates and the induced
complex matrix-valued random variable. -/
def canonicalComplexGaussianMatrixModel
    (p q σ : Type*) [Fintype p] [Fintype q] [Fintype σ] :
    ComplexGaussianMatrixModel p q σ where
  Ω := GaussianSampleSpace p q σ
  measurableSpace := inferInstance
  μ := gaussianSampleMeasure p q σ
  isProbability := inferInstance
  G := gaussianSampleMatrix p q σ

end GaussianModel
end PptFactorization
