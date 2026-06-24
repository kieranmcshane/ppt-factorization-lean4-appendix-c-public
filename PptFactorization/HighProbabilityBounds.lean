import PptFactorization.GaussianModel
import PptFactorization.HighDimensionalProbability
import PptFactorization.PartialTranspose
import PptFactorization.ProbabilityTools
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Data.Complex.BigOperators
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Probability.ProductMeasure
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# High-probability bound interface for the concrete Gaussian model

This file fixes the exact finite-dimensional probability space and events used
by the PPT high-dimensional-probability proof.

The public path is no-input: the fixed-vector MGF, fixed-vector Bernstein
tail, general Gaussian quadratic-form Bernstein estimate, net lifts, and final
`ConcreteHighProbabilityBounds` package are all proved inside this file.  The
historical `_of_estimate` names are retained below as no-input aliases of the
proved theorems, not as placeholders.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal

noncomputable section

namespace PptFactorization
namespace HighProbabilityBounds

open RandomMatrixModel GaussianModel HighDimensionalProbability

variable {p q σ : Type*}
variable [Fintype p] [Fintype q] [Fintype σ]
variable [DecidableEq p] [DecidableEq q]

/-! ## Block 1: Concrete Model Setup and Public Interfaces -/

/-- The canonical Gaussian sample space for the `(p,q,σ)` model. -/
abbrev Ω (p q σ : Type*) :=
  GaussianSampleSpace p q σ

/-- The canonical Gaussian probability measure. -/
def gaussianMeasure (p q σ : Type*) [Fintype p] [Fintype q] [Fintype σ] :
    Measure (Ω p q σ) :=
  gaussianSampleMeasure p q σ

/-- The canonical Gaussian sample matrix random variable. -/
def gaussianMatrix (p q σ : Type*) [Fintype p] [Fintype q] [Fintype σ] :
    RandomSampleMatrix (Ω p q σ) p q σ :=
  gaussianSampleMatrix p q σ

/-- Ambient bipartite dimension `D = |p × q|`, coerced to `ℝ`. -/
def bipartiteDimension (p q : Type*) [Fintype p] [Fintype q] : ℝ :=
  Fintype.card (RandomMatrixModel.BipIndex p q)

omit [DecidableEq p] [DecidableEq q] in
@[simp] theorem bipartiteDimension_nonneg : 0 ≤ bipartiteDimension p q := by
  unfold bipartiteDimension
  positivity

/-- Number of Gaussian columns/samples, coerced to `ℝ`. -/
def sampleDimension (σ : Type*) [Fintype σ] : ℝ :=
  Fintype.card σ

@[simp] theorem sampleDimension_nonneg : 0 ≤ sampleDimension σ := by
  unfold sampleDimension
  positivity

/-- Total Gaussian mass `T = ‖G‖₂²`. -/
def gaussianMass
    (p q σ : Type*) [Fintype p] [Fintype q] [Fintype σ] :
    Ω p q σ → ℝ :=
  fun ω => frobeniusMass (gaussianMatrix p q σ ω)

/-- Raw Wishart matrix `G Gᴴ`, before the `1 / s` normalization. -/
def rawWishart (G : SampleMatrix p q σ) : BipMatrix p q :=
  densityMatrix G

/-- Partial transpose of the raw Wishart matrix. -/
def rawWishartGamma (G : SampleMatrix p q σ) : BipMatrix p q :=
  gamma (rawWishart (p := p) (q := q) (σ := σ) G)

/-- Raw Wishart operator norm observable. -/
def rawWishartOpNorm
    (p q σ : Type*) [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] :
    Ω p q σ → ℝ :=
  fun ω => opNorm (rawWishart (p := p) (q := q) (σ := σ)
    (gaussianMatrix p q σ ω))

/-- Partial-transposed raw Wishart operator norm observable. -/
def rawWishartGammaOpNorm
    (p q σ : Type*) [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] :
    Ω p q σ → ℝ :=
  fun ω => opNorm (rawWishartGamma (p := p) (q := q) (σ := σ)
    (gaussianMatrix p q σ ω))

/-- Normalized Wishart operator norm observable.  Here
`RandomMatrixModel.wishart G = (1 / s) • G Gᴴ`. -/
def wishartOpNorm
    (p q σ : Type*) [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] :
    Ω p q σ → ℝ :=
  fun ω => opNorm (wishart (gaussianMatrix p q σ ω))

/-- Partial-transposed normalized Wishart operator norm observable. -/
def wishartGammaOpNorm
    (p q σ : Type*) [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] :
    Ω p q σ → ℝ :=
  fun ω => opNorm (wishartGamma (gaussianMatrix p q σ ω))

/-- The lower-tail good event `T ≥ c D s`. -/
def gaussianMassLowerEvent (c : ℝ) : Set (Ω p q σ) :=
  {ω | c * bipartiteDimension p q * sampleDimension σ ≤ gaussianMass p q σ ω}

/-- The event `‖W‖∞ ≤ K s` for the normalized Wishart convention in this file. -/
def wishartOpNormEvent (K : ℝ) : Set (Ω p q σ) :=
  {ω | wishartOpNorm p q σ ω ≤ K * sampleDimension σ}

/-- The event `‖W^Γ‖∞ ≤ K s` for the normalized Wishart convention in this file. -/
def wishartGammaOpNormEvent (K : ℝ) : Set (Ω p q σ) :=
  {ω | wishartGammaOpNorm p q σ ω ≤ K * sampleDimension σ}

/-- The good density-matrix event `Ω_M`. -/
def densityGoodEvent (M D : ℝ) : Set (Ω p q σ) :=
  goodSet M D (gaussianMatrix p q σ)

/-- Operator norm of a rectangular sample matrix, viewed as a linear map
between Euclidean spaces. -/
noncomputable def sampleOpNorm (G : SampleMatrix p q σ) : ℝ :=
  by
    classical
    exact ‖LinearMap.toContinuousLinearMap
        (Matrix.toEuclideanLin (𝕜 := ℂ) (m := RandomMatrixModel.BipIndex p q)
          (n := σ) G)‖

/-- Centered quadratic-form sum for the canonical Gaussian columns. -/
def canonicalCenteredQuadraticFormSum
    (H : BipMatrix p q) : Ω p q σ → ℝ :=
  fun ω =>
    ∑ α : σ,
      (quadraticForm H (gaussianColumn p q σ α ω) - RCLike.re H.trace)

/-- Vectors in the bipartite Hilbert space `ℂ^(p × q)`. -/
abbrev BipVector (p q : Type*) :=
  EuclideanSpace ℂ (RandomMatrixModel.BipIndex p q)

/-- The rank-one projector `|u⟩⟨u|`. -/
def rankOneProjector (u : BipVector p q) : BipMatrix p q :=
  fun i j => u i * star (u j)

/-- The partially transposed rank-one projector `H_u = (|u⟩⟨u|)^Γ`. -/
def rankOneProjectorGamma (u : BipVector p q) : BipMatrix p q :=
  gamma (rankOneProjector (p := p) (q := q) u)

/-- The fixed-vector centered observable used in the `W^Γ` net argument. -/
def fixedVectorWishartGammaCenteredSum
    (u : BipVector p q) : Ω p q σ → ℝ :=
  fun ω =>
    ∑ α : σ,
      (quadraticForm (rankOneProjectorGamma (p := p) (q := q) u)
        (gaussianColumn p q σ α ω) - 1)

/-- The exact Stage 4 high-probability bound package for the concrete model.
The canonical no-input inhabitant is `concreteHighProbabilityBounds`. -/
structure ConcreteHighProbabilityBounds where
  massConstant : ℝ
  wishartConstant : ℝ
  gammaWishartConstant : ℝ
  tailConstant : ℝ
  massConstant_pos : 0 < massConstant
  wishartConstant_pos : 0 < wishartConstant
  gammaWishartConstant_pos : 0 < gammaWishartConstant
  tailConstant_pos : 0 < tailConstant
  massLowerTail :
    (gaussianMeasure p q σ).real
        ((gaussianMassLowerEvent (p := p) (q := q) (σ := σ) massConstant)ᶜ) ≤
      Real.exp (-(tailConstant * bipartiteDimension p q * sampleDimension σ))
  wishartUpperTail :
    (gaussianMeasure p q σ).real
        ((wishartOpNormEvent (p := p) (q := q) (σ := σ) wishartConstant)ᶜ) ≤
      Real.exp (-(tailConstant * bipartiteDimension p q))
  wishartGammaUpperTail :
    (gaussianMeasure p q σ).real
        ((wishartGammaOpNormEvent (p := p) (q := q) (σ := σ) gammaWishartConstant)ᶜ) ≤
      Real.exp (-(tailConstant * bipartiteDimension p q))

omit [DecidableEq p] [DecidableEq q] in
@[simp] theorem gaussianMeasure_eq :
    gaussianMeasure p q σ = gaussianSampleMeasure p q σ :=
  rfl

omit [DecidableEq p] [DecidableEq q] in
@[simp] theorem gaussianMatrix_apply (ω : Ω p q σ) :
    gaussianMatrix p q σ ω = gaussianSampleMatrix p q σ ω :=
  rfl

omit [DecidableEq p] [DecidableEq q] in
@[simp] theorem gaussianMass_apply (ω : Ω p q σ) :
    gaussianMass p q σ ω = frobeniusMass (gaussianMatrix p q σ ω) :=
  rfl

omit [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] in
@[simp] theorem rawWishart_eq_densityMatrix (G : SampleMatrix p q σ) :
    rawWishart (p := p) (q := q) (σ := σ) G = densityMatrix G :=
  rfl

omit [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] in
@[simp] theorem rawWishartGamma_eq_gamma_rawWishart (G : SampleMatrix p q σ) :
    rawWishartGamma (p := p) (q := q) (σ := σ) G =
      gamma (rawWishart (p := p) (q := q) (σ := σ) G) :=
  rfl

omit [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] in
@[simp] theorem wishart_eq_card_inv_smul_rawWishart (G : SampleMatrix p q σ) :
    wishart G = ((Fintype.card σ : ℂ)⁻¹) •
      rawWishart (p := p) (q := q) (σ := σ) G :=
  rfl

omit [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] in
@[simp] theorem wishartGamma_eq_card_inv_smul_rawWishartGamma
    (G : SampleMatrix p q σ) :
    wishartGamma G = ((Fintype.card σ : ℂ)⁻¹) •
      rawWishartGamma (p := p) (q := q) (σ := σ) G := by
  ext i j
  simp [RandomMatrixModel.wishartGamma, RandomMatrixModel.wishart,
    rawWishartGamma, rawWishart, RandomMatrixModel.gamma]

@[simp] theorem rawWishartOpNorm_apply (ω : Ω p q σ) :
    rawWishartOpNorm p q σ ω =
      opNorm (rawWishart (p := p) (q := q) (σ := σ)
        (gaussianMatrix p q σ ω)) :=
  rfl

@[simp] theorem rawWishartGammaOpNorm_apply (ω : Ω p q σ) :
    rawWishartGammaOpNorm p q σ ω =
      opNorm (rawWishartGamma (p := p) (q := q) (σ := σ)
        (gaussianMatrix p q σ ω)) :=
  rfl

@[simp] theorem wishartOpNorm_apply (ω : Ω p q σ) :
    wishartOpNorm p q σ ω = opNorm (wishart (gaussianMatrix p q σ ω)) :=
  rfl

@[simp] theorem wishartGammaOpNorm_apply (ω : Ω p q σ) :
    wishartGammaOpNorm p q σ ω =
      opNorm (wishartGamma (gaussianMatrix p q σ ω)) :=
  rfl

@[simp] theorem opNorm_eq_toEuclideanCLM_norm (A : BipMatrix p q) :
    opNorm A =
      ‖Matrix.toEuclideanCLM (n := RandomMatrixModel.BipIndex p q) (𝕜 := ℂ) A‖ :=
  rfl

/-- Matrix-form quarter-net bridge written directly at the `opNorm` level. -/
theorem opNorm_le_two_mul_netQuadraticSup
    [Nonempty (RandomMatrixModel.BipIndex p q)]
    (A : BipMatrix p q) (hHerm : A.IsHermitian)
    {N : Set (Metric.sphere (0 : BipVector p q) 1)}
    (hnet :
      ∀ x : Metric.sphere (0 : BipVector p q) 1,
        ∃ u ∈ N, ‖(x : BipVector p q) - (u : BipVector p q)‖ ≤ (1 / 4 : ℝ)) :
    opNorm A ≤
      2 * HighDimensionalProbability.netQuadraticSup
        (Matrix.toEuclideanCLM (n := RandomMatrixModel.BipIndex p q) (𝕜 := ℂ) A) N := by
  simpa [opNorm] using
    (netToOperatorNorm (A := A) hHerm hnet)

@[simp] theorem canonicalCenteredQuadraticFormSum_apply
    (H : BipMatrix p q) (ω : Ω p q σ) :
    canonicalCenteredQuadraticFormSum (p := p) (q := q) (σ := σ) H ω =
      ∑ α : σ,
        (quadraticForm H (gaussianColumn p q σ α ω) - RCLike.re H.trace) :=
  rfl

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
@[simp] theorem rankOneProjector_apply
    (u : BipVector p q) (i j : RandomMatrixModel.BipIndex p q) :
    rankOneProjector (p := p) (q := q) u i j = u i * star (u j) :=
  rfl

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
@[simp] theorem rankOneProjectorGamma_apply
    (u : BipVector p q) (i j : RandomMatrixModel.BipIndex p q) :
    rankOneProjectorGamma (p := p) (q := q) u i j =
      u (i.1, j.2) * star (u (j.1, i.2)) :=
  rfl

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
theorem rankOneProjector_isHermitian (u : BipVector p q) :
    (rankOneProjector (p := p) (q := q) u).IsHermitian := by
  ext i j
  simp [rankOneProjector, mul_comm]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
theorem rankOneProjectorGamma_isHermitian (u : BipVector p q) :
    (rankOneProjectorGamma (p := p) (q := q) u).IsHermitian := by
  ext i j
  simp [rankOneProjectorGamma, rankOneProjector, RandomMatrixModel.gamma, mul_comm]

/-! ## Block 2: Deterministic Spectral and Algebraic Bridges -/

omit [Fintype σ] in
/-- Eigenvalues of `H_u = (|u⟩⟨u|)^Γ`, indexed by the ambient bipartite basis. -/
noncomputable def rankOneProjectorGammaEigenvalues
    (u : BipVector p q) : RandomMatrixModel.BipIndex p q → ℝ :=
  (rankOneProjectorGamma_isHermitian (p := p) (q := q) u).eigenvalues

omit [Fintype σ] in
/-- Spectral theorem specialized to `H_u = (|u⟩⟨u|)^Γ`. -/
theorem rankOneProjectorGamma_spectral_theorem (u : BipVector p q) :
    rankOneProjectorGamma (p := p) (q := q) u =
      Unitary.conjStarAlgAut ℂ _
        (rankOneProjectorGamma_isHermitian (p := p) (q := q) u).eigenvectorUnitary
        (diagonal
          (RCLike.ofReal ∘ rankOneProjectorGammaEigenvalues (p := p) (q := q) u)) := by
  exact (rankOneProjectorGamma_isHermitian (p := p) (q := q) u).spectral_theorem

omit [Fintype σ] [DecidableEq p] [DecidableEq q] in
@[simp] theorem rankOneProjectorGamma_trace_eq_rankOneProjector_trace
    (u : BipVector p q) :
    (rankOneProjectorGamma (p := p) (q := q) u).trace =
      (rankOneProjector (p := p) (q := q) u).trace := by
  simp [Matrix.trace, rankOneProjectorGamma, rankOneProjector, RandomMatrixModel.gamma]

omit [Fintype σ] [DecidableEq p] [DecidableEq q] in
theorem rankOneProjector_trace_eq_inner (u : BipVector p q) :
    (rankOneProjector (p := p) (q := q) u).trace = inner ℂ u u := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [Matrix.trace, dotProduct, rankOneProjector]

omit [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The Frobenius norm of the rank-one projector `|u⟩⟨u|` is `‖u‖²`. -/
theorem rankOneProjector_frobeniusNorm (u : BipVector p q) :
    frobeniusNorm (p := p) (q := q) (σ := RandomMatrixModel.BipIndex p q)
      (rankOneProjector (p := p) (q := q) u) = ‖u‖ ^ 2 := by
  unfold frobeniusNorm
  rw [Matrix.frobenius_norm_def]
  rw [EuclideanSpace.norm_sq_eq]
  let S : ℝ := ∑ i : RandomMatrixModel.BipIndex p q, ‖u i‖ ^ 2
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hstar_norm : ∀ z : ℂ, ‖(starRingEnd ℂ) z‖ = ‖z‖ := by
    intro z
    simp
  have hsum :
      (∑ i : RandomMatrixModel.BipIndex p q,
        ∑ j : RandomMatrixModel.BipIndex p q,
          ‖rankOneProjector (p := p) (q := q) u i j‖ ^ (2 : ℝ)) = S * S := by
    dsimp [S, rankOneProjector]
    simp only [norm_mul]
    simp_rw [hstar_norm]
    simp_rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _), Real.rpow_two]
    rw [Finset.sum_mul_sum]
  rw [hsum]
  have hSS : S * S = S ^ 2 := by ring
  rw [hSS]
  rw [← Real.sqrt_eq_rpow]
  exact Real.sqrt_sq hS_nonneg

omit [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The Frobenius norm of `H_u = (|u⟩⟨u|)^Γ` is still `‖u‖²`. -/
theorem rankOneProjectorGamma_frobeniusNorm (u : BipVector p q) :
    frobeniusNorm (p := p) (q := q) (σ := RandomMatrixModel.BipIndex p q)
      (rankOneProjectorGamma (p := p) (q := q) u) = ‖u‖ ^ 2 := by
  rw [rankOneProjectorGamma, RandomMatrixModel.frobeniusNorm_gamma,
    rankOneProjector_frobeniusNorm]

omit [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- For unit `u`, `H_u = (|u⟩⟨u|)^Γ` has Frobenius norm `1`. -/
theorem rankOneProjectorGamma_frobeniusNorm_unit
    (u : Metric.sphere (0 : BipVector p q) 1) :
    frobeniusNorm (p := p) (q := q) (σ := RandomMatrixModel.BipIndex p q)
      (rankOneProjectorGamma (p := p) (q := q) (u : BipVector p q)) = 1 := by
  have hnorm : ‖(u : BipVector p q)‖ = 1 := by
    have hdist : dist (u : BipVector p q) 0 = 1 := u.property
    rw [dist_eq_norm, sub_zero] at hdist
    exact hdist
  rw [rankOneProjectorGamma_frobeniusNorm, hnorm]
  norm_num

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The real part of `tr(Aᴴ A)` is the squared Frobenius norm written entrywise. -/
theorem matrix_re_trace_conjTranspose_mul_self_eq_sum_norm_sq
    {n : Type*} [Fintype n] (A : Matrix n n ℂ) :
    RCLike.re ((Aᴴ * A).trace) = ∑ i : n, ∑ j : n, ‖A i j‖ ^ 2 := by
  rw [← Matrix.star_vec_dotProduct_vec A A]
  simp only [dotProduct]
  rw [show RCLike.re (∑ i : n × n, star A.vec i * A.vec i) =
      ∑ i : n × n, RCLike.re (star A.vec i * A.vec i) by
    simp]
  simp only [Matrix.vec, Pi.star_apply]
  simp_rw [show ∀ z : ℂ, RCLike.re (star z * z) = ‖z‖ ^ 2 by
    intro z
    rw [show RCLike.re (star z * z) = Complex.normSq z by
      simp [Complex.normSq_apply]]
    rw [Complex.normSq_eq_norm_sq]]
  rw [← Finset.univ_product_univ]
  rw [Finset.sum_product_right]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The squared Frobenius norm of a complex square matrix is `re tr(Aᴴ A)`. -/
theorem matrix_frobenius_norm_sq_eq_re_trace_conjTranspose_mul_self
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    ‖A‖ ^ 2 = RCLike.re ((Aᴴ * A).trace) := by
  rw [matrix_re_trace_conjTranspose_mul_self_eq_sum_norm_sq]
  rw [Matrix.frobenius_norm_def]
  rw [← Real.sqrt_eq_rpow]
  rw [Real.sq_sqrt]
  · simp
  · exact Finset.sum_nonneg
      (fun i _ => Finset.sum_nonneg
        (fun j _ => Real.rpow_nonneg (norm_nonneg (A i j)) 2))

omit [Fintype p] [Fintype q] [Fintype σ] in
/-- Conjugating by a unitary matrix preserves trace. -/
theorem matrix_trace_conjStarAlgAut
    {n : Type*} [Fintype n] [DecidableEq n]
    (U : unitary (Matrix n n ℂ)) (X : Matrix n n ℂ) :
    (((Unitary.conjStarAlgAut ℂ (Matrix n n ℂ)) U) X).trace = X.trace := by
  rw [Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_cycle]
  rw [Unitary.coe_star_mul_self]
  simp

omit [Fintype p] [Fintype q] [Fintype σ] in
/-- The conjugation star-algebra automorphism transports `DᴴD` as expected. -/
theorem matrix_conjStarAlgAut_conjTranspose_mul_self
    {n : Type*} [Fintype n] [DecidableEq n]
    (U : unitary (Matrix n n ℂ)) (D : Matrix n n ℂ) :
    (((Unitary.conjStarAlgAut ℂ (Matrix n n ℂ)) U D)ᴴ *
      ((Unitary.conjStarAlgAut ℂ (Matrix n n ℂ)) U D)) =
        ((Unitary.conjStarAlgAut ℂ (Matrix n n ℂ)) U) (Dᴴ * D) := by
  rw [← Matrix.star_eq_conjTranspose]
  rw [← map_star]
  rw [← map_mul]
  rw [Matrix.star_eq_conjTranspose]

omit [Fintype p] [Fintype q] [Fintype σ] in
/-- For Hermitian matrices, `re tr(AᴴA)` is the sum of squared eigenvalues. -/
theorem matrix_hermitian_re_trace_conjTranspose_mul_self_eq_sum_eigenvalues_sq
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    RCLike.re ((Aᴴ * A).trace) = ∑ i : n, hA.eigenvalues i ^ 2 := by
  let φ := (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ)) hA.eigenvectorUnitary
  let D : Matrix n n ℂ := diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  have hAeq : A = φ D := by
    simpa [φ, D] using hA.spectral_theorem
  have hmul : (φ D)ᴴ * (φ D) = φ (Dᴴ * D) := by
    simpa [φ] using
      matrix_conjStarAlgAut_conjTranspose_mul_self hA.eigenvectorUnitary D
  calc
    RCLike.re ((Aᴴ * A).trace)
        = RCLike.re (((φ D)ᴴ * (φ D)).trace) := by rw [hAeq]
    _ = RCLike.re ((φ (Dᴴ * D)).trace) := by rw [hmul]
    _ = RCLike.re ((Dᴴ * D).trace) := by
      exact congrArg RCLike.re
        (matrix_trace_conjStarAlgAut hA.eigenvectorUnitary (Dᴴ * D))
    _ = ∑ i : n, hA.eigenvalues i ^ 2 := by
      simp [D, Matrix.diagonal_mul_diagonal, pow_two]

omit [Fintype σ] in
/-- Hermitian Frobenius-square/eigenvalue-square identity in the bipartite model. -/
theorem hermitian_frobeniusNorm_sq_eq_sum_eigenvalues_sq
    (A : BipMatrix p q) (hA : A.IsHermitian) :
    frobeniusNorm (p := p) (q := q) (σ := RandomMatrixModel.BipIndex p q) A ^ 2 =
      ∑ i : RandomMatrixModel.BipIndex p q, hA.eigenvalues i ^ 2 := by
  unfold frobeniusNorm
  rw [matrix_frobenius_norm_sq_eq_re_trace_conjTranspose_mul_self]
  exact matrix_hermitian_re_trace_conjTranspose_mul_self_eq_sum_eigenvalues_sq A hA

omit [Fintype σ] [DecidableEq p] [DecidableEq q] in
theorem rankOneProjectorGamma_trace_re_unit
    (u : Metric.sphere (0 : BipVector p q) 1) :
    RCLike.re ((rankOneProjectorGamma (p := p) (q := q)
      (u : BipVector p q)).trace) = 1 := by
  have hnorm : ‖(u : BipVector p q)‖ = 1 := by
    have hdist : dist (u : BipVector p q) 0 = 1 := u.property
    rw [dist_eq_norm, sub_zero] at hdist
    exact hdist
  rw [rankOneProjectorGamma_trace_eq_rankOneProjector_trace,
    rankOneProjector_trace_eq_inner, inner_self_eq_norm_sq_to_K]
  simp [hnorm]

omit [Fintype σ] [DecidableEq p] [DecidableEq q] in
theorem rankOneProjector_trace_re_unit
    (u : Metric.sphere (0 : BipVector p q) 1) :
    RCLike.re ((rankOneProjector (p := p) (q := q)
      (u : BipVector p q)).trace) = 1 := by
  have hnorm : ‖(u : BipVector p q)‖ = 1 := by
    have hdist : dist (u : BipVector p q) 0 = 1 := u.property
    rw [dist_eq_norm, sub_zero] at hdist
    exact hdist
  rw [rankOneProjector_trace_eq_inner, inner_self_eq_norm_sq_to_K]
  simp [hnorm]

omit [Fintype σ] [DecidableEq p] [DecidableEq q] in
theorem rankOneProjector_frobeniusNorm_unit
    (u : Metric.sphere (0 : BipVector p q) 1) :
    frobeniusNorm (p := p) (q := q) (σ := RandomMatrixModel.BipIndex p q)
      (rankOneProjector (p := p) (q := q) (u : BipVector p q)) = 1 := by
  have hnorm : ‖(u : BipVector p q)‖ = 1 := by
    have hdist : dist (u : BipVector p q) 0 = 1 := u.property
    rw [dist_eq_norm, sub_zero] at hdist
    exact hdist
  rw [rankOneProjector_frobeniusNorm]
  simp [hnorm]

omit [Fintype σ] in
/-- For unit `u`, the eigenvalues of `H_u` have sum `1`. -/
theorem rankOneProjectorGamma_eigenvalues_sum_unit
    (u : Metric.sphere (0 : BipVector p q) 1) :
    ∑ i : RandomMatrixModel.BipIndex p q,
        rankOneProjectorGammaEigenvalues (p := p) (q := q) (u : BipVector p q) i = 1 := by
  let A : BipMatrix p q := rankOneProjectorGamma (p := p) (q := q) (u : BipVector p q)
  let hA : A.IsHermitian :=
    rankOneProjectorGamma_isHermitian (p := p) (q := q) (u : BipVector p q)
  have htrace :
      A.trace = ∑ i : RandomMatrixModel.BipIndex p q, (hA.eigenvalues i : ℂ) :=
    hA.trace_eq_sum_eigenvalues
  have hre := congrArg RCLike.re htrace
  have hunit : RCLike.re A.trace = 1 := by
    simpa [A] using rankOneProjectorGamma_trace_re_unit (p := p) (q := q) (u := u)
  rw [hunit] at hre
  simpa [rankOneProjectorGammaEigenvalues, A, hA] using hre.symm

omit [Fintype σ] in
/-- For unit `u`, the eigenvalues of `H_u` have squared sum `1`. -/
theorem rankOneProjectorGamma_eigenvalues_sq_sum_unit
    (u : Metric.sphere (0 : BipVector p q) 1) :
    ∑ i : RandomMatrixModel.BipIndex p q,
        rankOneProjectorGammaEigenvalues (p := p) (q := q)
          (u : BipVector p q) i ^ 2 = 1 := by
  let A : BipMatrix p q :=
    rankOneProjectorGamma (p := p) (q := q) (u : BipVector p q)
  let hA : A.IsHermitian :=
    rankOneProjectorGamma_isHermitian (p := p) (q := q) (u : BipVector p q)
  have hbridge :=
    hermitian_frobeniusNorm_sq_eq_sum_eigenvalues_sq (p := p) (q := q) A hA
  have hnorm :
      frobeniusNorm (p := p) (q := q) (σ := RandomMatrixModel.BipIndex p q) A = 1 := by
    simpa [A] using rankOneProjectorGamma_frobeniusNorm_unit (p := p) (q := q) (u := u)
  rw [hnorm] at hbridge
  norm_num at hbridge
  simpa [rankOneProjectorGammaEigenvalues, A, hA] using hbridge.symm

omit [Fintype σ] in
/-- Once the squared-eigenvalue identity is available, every eigenvalue of `H_u`
has absolute value at most `1`.  This isolates the final elementary step from
the still-needed Frobenius/spectral bridge. -/
theorem rankOneProjectorGamma_eigenvalues_abs_le_one_of_sq_sum_unit
    (u : Metric.sphere (0 : BipVector p q) 1)
    (hsq :
      ∑ i : RandomMatrixModel.BipIndex p q,
          rankOneProjectorGammaEigenvalues (p := p) (q := q)
            (u : BipVector p q) i ^ 2 = 1)
    (i : RandomMatrixModel.BipIndex p q) :
    |rankOneProjectorGammaEigenvalues (p := p) (q := q)
      (u : BipVector p q) i| ≤ 1 := by
  have hle :
      rankOneProjectorGammaEigenvalues (p := p) (q := q)
        (u : BipVector p q) i ^ 2 ≤
        ∑ j : RandomMatrixModel.BipIndex p q,
          rankOneProjectorGammaEigenvalues (p := p) (q := q)
            (u : BipVector p q) j ^ 2 := by
    exact Finset.single_le_sum
      (fun j _ =>
        sq_nonneg
          (rankOneProjectorGammaEigenvalues (p := p) (q := q)
            (u : BipVector p q) j))
      (Finset.mem_univ i)
  rw [hsq] at hle
  exact (sq_le_one_iff_abs_le_one
      (rankOneProjectorGammaEigenvalues (p := p) (q := q)
        (u : BipVector p q) i)).mp hle

omit [Fintype σ] in
/-- Every eigenvalue of `H_u` has absolute value at most `1`. -/
theorem rankOneProjectorGamma_eigenvalues_abs_le_one
    (u : Metric.sphere (0 : BipVector p q) 1)
    (i : RandomMatrixModel.BipIndex p q) :
    |rankOneProjectorGammaEigenvalues (p := p) (q := q)
      (u : BipVector p q) i| ≤ 1 :=
  rankOneProjectorGamma_eigenvalues_abs_le_one_of_sq_sum_unit
    (p := p) (q := q) (u := u)
    (rankOneProjectorGamma_eigenvalues_sq_sum_unit (p := p) (q := q) u) i

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- A real diagonal matrix has quadratic form `∑ i h_i ‖z_i‖²`. -/
theorem quadraticForm_diagonal_real
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → ℝ) (z : EuclideanSpace ℂ ι) :
    quadraticForm (diagonal (fun i : ι => ((h i : ℝ) : ℂ))) z =
      ∑ i : ι, h i * ‖z i‖ ^ 2 := by
  unfold quadraticForm
  rw [ContinuousLinearMap.reApplyInnerSelf_apply]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  rw [Matrix.ofLp_toEuclideanCLM]
  simp only [Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply]
  ring

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Centering a real diagonal quadratic form by its trace gives
`∑ i h_i (‖z_i‖² - 1)`. -/
theorem quadraticForm_diagonal_real_sub_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → ℝ) (z : EuclideanSpace ℂ ι) :
    quadraticForm (diagonal (fun i : ι => ((h i : ℝ) : ℂ))) z - ∑ i : ι, h i =
      ∑ i : ι, h i * (‖z i‖ ^ 2 - 1) := by
  rw [quadraticForm_diagonal_real]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- If the diagonal weights sum to `1`, the centered diagonal quadratic form
is exactly `∑ i h_i (‖z_i‖² - 1)`. -/
theorem quadraticForm_diagonal_real_sub_one_of_sum_eq_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → ℝ) (z : EuclideanSpace ℂ ι)
    (hsum : ∑ i : ι, h i = 1) :
    quadraticForm (diagonal (fun i : ι => ((h i : ℝ) : ℂ))) z - 1 =
      ∑ i : ι, h i * (‖z i‖ ^ 2 - 1) := by
  calc
    quadraticForm (diagonal (fun i : ι => ((h i : ℝ) : ℂ))) z - 1 =
        quadraticForm (diagonal (fun i : ι => ((h i : ℝ) : ℂ))) z - ∑ i : ι, h i := by
          rw [hsum]
    _ = ∑ i : ι, h i * (‖z i‖ ^ 2 - 1) :=
        quadraticForm_diagonal_real_sub_sum h z

omit [Fintype σ] in
/-- Coordinate rewrite for the diagonalized `H_u` quadratic form: the
centered diagonal form is `∑ i h_i (‖z_i‖² - 1)`, where `h_i` are the
eigenvalues of `H_u`. -/
theorem rankOneProjectorGamma_diagonal_quadraticForm_centered
    (u : Metric.sphere (0 : BipVector p q) 1)
    (z : EuclideanSpace ℂ (RandomMatrixModel.BipIndex p q)) :
    quadraticForm
        (diagonal
          (RCLike.ofReal ∘
            rankOneProjectorGammaEigenvalues (p := p) (q := q) (u : BipVector p q)))
        z - 1 =
      ∑ i : RandomMatrixModel.BipIndex p q,
        rankOneProjectorGammaEigenvalues (p := p) (q := q) (u : BipVector p q) i *
          (‖z i‖ ^ 2 - 1) := by
  let h :=
    rankOneProjectorGammaEigenvalues (p := p) (q := q) (u : BipVector p q)
  have hsum : ∑ i : RandomMatrixModel.BipIndex p q, h i = 1 := by
    simpa [h] using rankOneProjectorGamma_eigenvalues_sum_unit (p := p) (q := q) u
  simpa [h] using
    quadraticForm_diagonal_real_sub_one_of_sum_eq_one
      (h := h) (z := z) hsum

@[simp] theorem fixedVectorWishartGammaCenteredSum_apply
    (u : BipVector p q) (ω : Ω p q σ) :
    fixedVectorWishartGammaCenteredSum (p := p) (q := q) (σ := σ) u ω =
      ∑ α : σ,
        (quadraticForm (rankOneProjectorGamma (p := p) (q := q) u)
          (gaussianColumn p q σ α ω) - 1) :=
  rfl

omit [DecidableEq p] [DecidableEq q] in
/-- Reindexing helper for the finite sums appearing in the partial-transpose
Wishart/rank-one duality identity. -/
private theorem sum_reorder_sigma_p_q_p_q
    (r : σ → p → q → p → q → ℂ) :
    (∑ α : σ, ∑ a : p, ∑ b : q, ∑ c : p, ∑ d : q, r α a b c d) =
      ∑ c : p, ∑ b : q, ∑ a : p, ∑ d : q, ∑ α : σ, r α a b c d := by
  calc
    (∑ α : σ, ∑ a : p, ∑ b : q, ∑ c : p, ∑ d : q, r α a b c d)
        = ∑ a : p, ∑ α : σ, ∑ b : q, ∑ c : p, ∑ d : q, r α a b c d := by
          rw [Finset.sum_comm]
    _ = ∑ a : p, ∑ b : q, ∑ α : σ, ∑ c : p, ∑ d : q, r α a b c d := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ = ∑ a : p, ∑ b : q, ∑ c : p, ∑ α : σ, ∑ d : q, r α a b c d := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          rw [Finset.sum_comm]
    _ = ∑ a : p, ∑ b : q, ∑ c : p, ∑ d : q, ∑ α : σ, r α a b c d := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          apply Finset.sum_congr rfl
          intro c _
          rw [Finset.sum_comm]
    _ = ∑ c : p, ∑ b : q, ∑ a : p, ∑ d : q, ∑ α : σ, r α a b c d := by
          calc
            (∑ a : p, ∑ b : q, ∑ c : p, ∑ d : q, ∑ α : σ, r α a b c d)
                = ∑ b : q, ∑ a : p, ∑ c : p, ∑ d : q, ∑ α : σ, r α a b c d := by
                  rw [Finset.sum_comm]
            _ = ∑ b : q, ∑ c : p, ∑ a : p, ∑ d : q, ∑ α : σ, r α a b c d := by
                  apply Finset.sum_congr rfl
                  intro b _
                  rw [Finset.sum_comm]
            _ = ∑ c : p, ∑ b : q, ∑ a : p, ∑ d : q, ∑ α : σ, r α a b c d := by
                  rw [Finset.sum_comm]

omit [DecidableEq p] [DecidableEq q] in
private theorem sum_reorder_sigma_p_q_p_q_full
    (r : σ → p → q → p → q → ℂ) :
    (∑ α : σ, ∑ a : p, ∑ b : q, ∑ c : p, ∑ d : q, r α a b c d) =
      ∑ c : p, ∑ d : q, ∑ a : p, ∑ b : q, ∑ α : σ, r α a b c d := by
  calc
    (∑ α : σ, ∑ a : p, ∑ b : q, ∑ c : p, ∑ d : q, r α a b c d)
        = ∑ a : p, ∑ α : σ, ∑ b : q, ∑ c : p, ∑ d : q, r α a b c d := by
          rw [Finset.sum_comm]
    _ = ∑ a : p, ∑ b : q, ∑ α : σ, ∑ c : p, ∑ d : q, r α a b c d := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ = ∑ a : p, ∑ b : q, ∑ c : p, ∑ α : σ, ∑ d : q, r α a b c d := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          rw [Finset.sum_comm]
    _ = ∑ a : p, ∑ b : q, ∑ c : p, ∑ d : q, ∑ α : σ, r α a b c d := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          apply Finset.sum_congr rfl
          intro c _
          rw [Finset.sum_comm]
    _ = ∑ c : p, ∑ b : q, ∑ a : p, ∑ d : q, ∑ α : σ, r α a b c d := by
          calc
            (∑ a : p, ∑ b : q, ∑ c : p, ∑ d : q, ∑ α : σ, r α a b c d)
                = ∑ b : q, ∑ a : p, ∑ c : p, ∑ d : q, ∑ α : σ, r α a b c d := by
                  rw [Finset.sum_comm]
            _ = ∑ b : q, ∑ c : p, ∑ a : p, ∑ d : q, ∑ α : σ, r α a b c d := by
                  apply Finset.sum_congr rfl
                  intro b _
                  rw [Finset.sum_comm]
            _ = ∑ c : p, ∑ b : q, ∑ a : p, ∑ d : q, ∑ α : σ, r α a b c d := by
                  rw [Finset.sum_comm]
    _ = ∑ c : p, ∑ d : q, ∑ a : p, ∑ b : q, ∑ α : σ, r α a b c d := by
          apply Finset.sum_congr rfl
          intro c _
          calc
            (∑ b : q, ∑ a : p, ∑ d : q, ∑ α : σ, r α a b c d)
                = ∑ b : q, ∑ d : q, ∑ a : p, ∑ α : σ, r α a b c d := by
                  apply Finset.sum_congr rfl
                  intro b _
                  rw [Finset.sum_comm]
            _ = ∑ d : q, ∑ b : q, ∑ a : p, ∑ α : σ, r α a b c d := by
                  rw [Finset.sum_comm]
            _ = ∑ d : q, ∑ a : p, ∑ b : q, ∑ α : σ, r α a b c d := by
                  apply Finset.sum_congr rfl
                  intro d _
                  rw [Finset.sum_comm]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Pulling a real scalar through a quadratic form. -/
theorem quadraticForm_real_smul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℝ) (A : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) :
    quadraticForm (((r : ℂ) • A)) x = r * quadraticForm A x := by
  unfold quadraticForm
  rw [map_smul]
  rw [ContinuousLinearMap.reApplyInnerSelf_apply]
  rw [ContinuousLinearMap.reApplyInnerSelf_apply]
  change RCLike.re
      (inner ℂ ((r : ℂ) •
        (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A x)) x) =
      r * RCLike.re
        (inner ℂ (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A x) x)
  rw [inner_smul_left]
  simp

/-- Algebraic duality between the partial-transposed raw Wishart quadratic
form and the sum of rank-one partial-transpose quadratic forms over columns. -/
theorem quadraticForm_rawWishartGamma_eq_sum_rankOneProjectorGamma
    (G : SampleMatrix p q σ) (u : BipVector p q) :
    quadraticForm (rawWishartGamma (p := p) (q := q) (σ := σ) G) u =
      ∑ α : σ,
        quadraticForm (rankOneProjectorGamma (p := p) (q := q) u)
          (GaussianModel.columnVector G α) := by
  simp only [quadraticForm]
  rw [ContinuousLinearMap.reApplyInnerSelf_apply]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  rw [Matrix.ofLp_toEuclideanCLM]
  simp only [ContinuousLinearMap.reApplyInnerSelf_apply]
  simp_rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp_rw [Matrix.ofLp_toEuclideanCLM]
  rw [← map_sum]
  apply congrArg RCLike.re
  simp [rawWishartGamma, rawWishart, densityMatrix, RandomMatrixModel.gamma,
    rankOneProjectorGamma, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  simp only [mul_assoc]
  conv_lhs =>
    simp only [Finset.mul_sum]
  trans
      ∑ a : p, ∑ b : q, ∑ c : p, ∑ d : q, ∑ α : σ,
        G (c, b) α * star (u (c, d)) * u (a, b) * star (G (a, d) α)
  · apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro α _
    simp only [starRingEnd_apply]
    ring_nf
  · symm
    have h := sum_reorder_sigma_p_q_p_q (p := p) (q := q) (σ := σ)
      (r := fun α a b c d =>
        G (a, b) α * star (u (a, d)) * u (c, b) * star (G (c, d) α))
    simpa [mul_assoc] using h

/-- Normalized version of the raw algebraic bridge for `W^Γ = s⁻¹(GGᴴ)^Γ`. -/
theorem quadraticForm_wishartGamma_eq_sampleDimension_inv_mul_sum_rankOneProjectorGamma
    (G : SampleMatrix p q σ) (u : BipVector p q) :
    quadraticForm (wishartGamma G) u =
      (sampleDimension σ)⁻¹ *
        ∑ α : σ,
          quadraticForm (rankOneProjectorGamma (p := p) (q := q) u)
            (GaussianModel.columnVector G α) := by
  rw [wishartGamma_eq_card_inv_smul_rawWishartGamma]
  calc
    quadraticForm (((Fintype.card σ : ℂ)⁻¹) •
        rawWishartGamma (p := p) (q := q) (σ := σ) G) u
        = (sampleDimension σ)⁻¹ *
            quadraticForm (rawWishartGamma (p := p) (q := q) (σ := σ) G) u := by
          simpa [sampleDimension] using
            quadraticForm_real_smul
              (r := (sampleDimension σ)⁻¹)
              (A := rawWishartGamma (p := p) (q := q) (σ := σ) G)
              (x := u)
    _ = (sampleDimension σ)⁻¹ *
        ∑ α : σ,
          quadraticForm (rankOneProjectorGamma (p := p) (q := q) u)
            (GaussianModel.columnVector G α) := by
          rw [quadraticForm_rawWishartGamma_eq_sum_rankOneProjectorGamma
            (p := p) (q := q) (σ := σ) G u]

/-- Deterministic centered-column bridge: the fixed-vector centered sum is
exactly `s * ⟪W^Γ u, u⟫ - s` for an arbitrary sample matrix. -/
theorem sum_rankOneProjectorGamma_quadraticForm_sub_one_eq
    (G : SampleMatrix p q σ) (u : BipVector p q) :
    (∑ α : σ,
      (quadraticForm (rankOneProjectorGamma (p := p) (q := q) u)
        (GaussianModel.columnVector G α) - 1)) =
      sampleDimension σ * quadraticForm (wishartGamma G) u - sampleDimension σ := by
  classical
  let S : ℝ := ∑ α : σ,
      quadraticForm (rankOneProjectorGamma (p := p) (q := q) u)
        (GaussianModel.columnVector G α)
  have hsum_sub :
      (∑ α : σ,
        (quadraticForm (rankOneProjectorGamma (p := p) (q := q) u)
          (GaussianModel.columnVector G α) - 1)) =
        S - sampleDimension σ := by
    simp [S, sampleDimension, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  have hQ :
      quadraticForm (wishartGamma G) u = (sampleDimension σ)⁻¹ * S := by
    simpa [S] using
      quadraticForm_wishartGamma_eq_sampleDimension_inv_mul_sum_rankOneProjectorGamma
        (p := p) (q := q) (σ := σ) G u
  rw [hsum_sub, hQ]
  by_cases hs : Fintype.card σ = 0
  · have hS : S = 0 := by
      haveI : IsEmpty σ := Fintype.card_eq_zero_iff.mp hs
      simp [S]
    simp [sampleDimension, hs, hS]
  · have hsreal : sampleDimension σ ≠ 0 := by
      unfold sampleDimension
      exact_mod_cast hs
    field_simp [hsreal]

/-- Algebraic duality between the raw Wishart quadratic form and the sum of
rank-one projector quadratic forms over columns. -/
theorem quadraticForm_rawWishart_eq_sum_rankOneProjector
    (G : SampleMatrix p q σ) (u : BipVector p q) :
    quadraticForm (rawWishart (p := p) (q := q) (σ := σ) G) u =
      ∑ α : σ,
        quadraticForm (rankOneProjector (p := p) (q := q) u)
          (GaussianModel.columnVector G α) := by
  simp only [quadraticForm]
  rw [ContinuousLinearMap.reApplyInnerSelf_apply]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  rw [Matrix.ofLp_toEuclideanCLM]
  simp only [ContinuousLinearMap.reApplyInnerSelf_apply]
  simp_rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp_rw [Matrix.ofLp_toEuclideanCLM]
  rw [← map_sum]
  apply congrArg RCLike.re
  simp [rawWishart, densityMatrix, rankOneProjector, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  simp only [mul_assoc]
  conv_lhs =>
    simp only [Finset.mul_sum]
  trans
      ∑ a : p, ∑ b : q, ∑ c : p, ∑ d : q, ∑ α : σ,
        G (c, d) α * star (u (c, d)) * u (a, b) * star (G (a, b) α)
  · apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro α _
    simp only [starRingEnd_apply]
    ring_nf
  · symm
    have h := sum_reorder_sigma_p_q_p_q_full (p := p) (q := q) (σ := σ)
      (r := fun α c d a b =>
        G (c, d) α * star (u (c, d)) * u (a, b) * star (G (a, b) α))
    simpa [mul_assoc] using h

/-- Normalized version of the raw algebraic bridge for `W = s⁻¹ G Gᴴ`. -/
theorem quadraticForm_wishart_eq_sampleDimension_inv_mul_sum_rankOneProjector
    (G : SampleMatrix p q σ) (u : BipVector p q) :
    quadraticForm (wishart G) u =
      (sampleDimension σ)⁻¹ *
        ∑ α : σ,
          quadraticForm (rankOneProjector (p := p) (q := q) u)
            (GaussianModel.columnVector G α) := by
  rw [wishart_eq_card_inv_smul_rawWishart]
  calc
    quadraticForm (((Fintype.card σ : ℂ)⁻¹) •
        rawWishart (p := p) (q := q) (σ := σ) G) u
        = (sampleDimension σ)⁻¹ *
            quadraticForm (rawWishart (p := p) (q := q) (σ := σ) G) u := by
          simpa [sampleDimension] using
            quadraticForm_real_smul
              (r := (sampleDimension σ)⁻¹)
              (A := rawWishart (p := p) (q := q) (σ := σ) G)
              (x := u)
    _ = (sampleDimension σ)⁻¹ *
        ∑ α : σ,
          quadraticForm (rankOneProjector (p := p) (q := q) u)
            (GaussianModel.columnVector G α) := by
          rw [quadraticForm_rawWishart_eq_sum_rankOneProjector
            (p := p) (q := q) (σ := σ) G u]

/-- Deterministic centered-column bridge for the ordinary Wishart quadratic
form. -/
theorem sum_rankOneProjector_quadraticForm_sub_one_eq
    (G : SampleMatrix p q σ) (u : Metric.sphere (0 : BipVector p q) 1) :
    (∑ α : σ,
      (quadraticForm (rankOneProjector (p := p) (q := q) (u : BipVector p q))
        (GaussianModel.columnVector G α) - 1)) =
      sampleDimension σ * quadraticForm (wishart G) (u : BipVector p q) - sampleDimension σ := by
  classical
  let S : ℝ := ∑ α : σ,
      quadraticForm (rankOneProjector (p := p) (q := q) (u : BipVector p q))
        (GaussianModel.columnVector G α)
  have hsum_sub :
      (∑ α : σ,
        (quadraticForm (rankOneProjector (p := p) (q := q) (u : BipVector p q))
          (GaussianModel.columnVector G α) - 1)) =
        S - sampleDimension σ := by
    simp [S, sampleDimension, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  have hQ :
      quadraticForm (wishart G) (u : BipVector p q) = (sampleDimension σ)⁻¹ * S := by
    simpa [S] using
      quadraticForm_wishart_eq_sampleDimension_inv_mul_sum_rankOneProjector
        (p := p) (q := q) (σ := σ) G (u : BipVector p q)
  rw [hsum_sub, hQ]
  by_cases hs : Fintype.card σ = 0
  · have hS : S = 0 := by
      haveI : IsEmpty σ := Fintype.card_eq_zero_iff.mp hs
      simp [S]
    simp [sampleDimension, hs, hS]
  · have hsreal : sampleDimension σ ≠ 0 := by
      unfold sampleDimension
      exact_mod_cast hs
    field_simp [hsreal]

/-- Exact bridge from the canonical centered quadratic-form sum with a rank-one
projector to the quadratic form of the normalized Wishart matrix. -/
theorem canonicalCenteredQuadraticFormSum_rankOneProjector_eq_sampleDimension_mul_quadraticForm_wishart_sub_one
    (u : Metric.sphere (0 : BipVector p q) 1) (ω : Ω p q σ) :
    canonicalCenteredQuadraticFormSum (p := p) (q := q) (σ := σ)
      (rankOneProjector (p := p) (q := q) (u : BipVector p q)) ω =
        sampleDimension σ *
          (quadraticForm (wishart (gaussianMatrix p q σ ω)) (u : BipVector p q) - 1) := by
  rw [canonicalCenteredQuadraticFormSum]
  have htrace :
      RCLike.re
          (rankOneProjector (p := p) (q := q) (u : BipVector p q)).trace = 1 := by
    exact rankOneProjector_trace_re_unit (p := p) (q := q) u
  have hsum :=
    sum_rankOneProjector_quadraticForm_sub_one_eq
      (p := p) (q := q) (σ := σ) (G := gaussianMatrix p q σ ω) (u := u)
  simpa [canonicalCenteredQuadraticFormSum, htrace, gaussianColumn, gaussianMatrix,
    sub_eq_add_neg, mul_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
    mul_assoc] using hsum

/-- Exact bridge from the canonical fixed-vector observable to the quadratic
form of the normalized partial-transposed Wishart matrix. -/
theorem fixedVectorWishartGammaCenteredSum_eq_sampleDimension_mul_quadraticForm_wishartGamma_sub
    (u : BipVector p q) (ω : Ω p q σ) :
    fixedVectorWishartGammaCenteredSum (p := p) (q := q) (σ := σ) u ω =
      sampleDimension σ *
        quadraticForm (wishartGamma (gaussianMatrix p q σ ω)) u - sampleDimension σ := by
  rw [fixedVectorWishartGammaCenteredSum_apply]
  simpa [gaussianColumn, gaussianMatrix] using
    sum_rankOneProjectorGamma_quadraticForm_sub_one_eq
      (p := p) (q := q) (σ := σ) (G := gaussianMatrix p q σ ω) (u := u)

/-- Equivalent centered bridge, factored as `s * (⟪W^Γu,u⟫ - 1)`. -/
theorem fixedVectorWishartGammaCenteredSum_eq_sampleDimension_mul_quadraticForm_wishartGamma_sub_one
    (u : BipVector p q) (ω : Ω p q σ) :
    fixedVectorWishartGammaCenteredSum (p := p) (q := q) (σ := σ) u ω =
      sampleDimension σ *
        (quadraticForm (wishartGamma (gaussianMatrix p q σ ω)) u - 1) := by
  rw [fixedVectorWishartGammaCenteredSum_eq_sampleDimension_mul_quadraticForm_wishartGamma_sub
    (p := p) (q := q) (σ := σ) (u := u) (ω := ω)]
  ring

/-! ## Block 3: Unitary-Coordinate Law Bridges and Net Preliminaries -/

omit [DecidableEq p] [DecidableEq q] in
/-- The real Gaussian coordinates underlying the canonical sample model are
invariant under every real linear isometric equivalence.  This is the reusable
Mathlib bridge needed before specializing to the realification of a complex
unitary action on the sample matrix. -/
theorem gaussianSampleMeasure_map_linearIsometryEquiv
    (U : GaussianSampleSpace p q σ ≃ₗᵢ[ℝ] GaussianSampleSpace p q σ) :
    Measure.map U (gaussianMeasure p q σ) = gaussianMeasure p q σ := by
  unfold gaussianMeasure GaussianModel.gaussianSampleMeasure
  simpa using ProbabilityTheory.stdGaussian_map U

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- A complex linear isometric equivalence of finite complex Euclidean space,
viewed as a real linear isometric equivalence.  This is the exact
realification step needed to invoke `stdGaussian_map`. -/
def complexEuclideanLinearIsometryEquivRestrictScalarsReal
    {ι : Type*} [Fintype ι]
    (U : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℂ ι := by
  refine LinearIsometryEquiv.mk ?e ?norm
  · refine
      { toFun := U
        invFun := U.symm
        left_inv := U.left_inv
        right_inv := U.right_inv
        map_add' := ?_
        map_smul' := ?_ }
    · intro x y
      exact U.map_add x y
    · intro a x
      change U (((a : ℂ) • x)) = ((a : ℂ) • U x)
      exact U.map_smul (a : ℂ) x
  · intro x
    exact U.norm_map x

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Mathlib's real standard Gaussian on complex Euclidean space is invariant
under every complex unitary/isometric equivalence, after realification. -/
theorem stdGaussian_complex_map_complexLinearIsometryEquiv
    {ι : Type*} [Fintype ι]
    (U : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι) :
    Measure.map U (ProbabilityTheory.stdGaussian (EuclideanSpace ℂ ι)) =
      ProbabilityTheory.stdGaussian (EuclideanSpace ℂ ι) := by
  simpa using ProbabilityTheory.stdGaussian_map
    (complexEuclideanLinearIsometryEquivRestrictScalarsReal U)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The unscaled real/imaginary-coordinate identification with complex
Euclidean space.  Unlike `complexVectorOfRealCoordinates`, this map does not
include the standard-complex-Gaussian factor `1 / sqrt 2`, and is therefore an
actual real linear isometry. -/
def unscaledComplexVectorOfRealCoordinates {ι : Type*} [Fintype ι]
    (x : ComplexRealCoordSpace ι) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2
    (fun i : ι => ((x (i, 0) : ℝ) : ℂ) + ((x (i, 1) : ℝ) : ℂ) * Complex.I)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Inverse real-coordinate map for the unscaled real/complex identification. -/
def unscaledRealCoordinatesOfComplexVector {ι : Type*} [Fintype ι]
    (z : EuclideanSpace ℂ ι) : ComplexRealCoordSpace ι :=
  WithLp.toLp 2
    (fun ik : ι × Fin 2 =>
      if ik.2 = 0 then Complex.re (z ik.1) else Complex.im (z ik.1))

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
@[simp] theorem unscaledComplexVectorOfRealCoordinates_apply
    {ι : Type*} [Fintype ι] (x : ComplexRealCoordSpace ι) (i : ι) :
    unscaledComplexVectorOfRealCoordinates x i =
      ((x (i, 0) : ℝ) : ℂ) + ((x (i, 1) : ℝ) : ℂ) * Complex.I :=
  rfl

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
@[simp] theorem unscaledRealCoordinatesOfComplexVector_apply_zero
    {ι : Type*} [Fintype ι] (z : EuclideanSpace ℂ ι) (i : ι) :
    unscaledRealCoordinatesOfComplexVector z (i, 0) = Complex.re (z i) := by
  simp [unscaledRealCoordinatesOfComplexVector]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
@[simp] theorem unscaledRealCoordinatesOfComplexVector_apply_one
    {ι : Type*} [Fintype ι] (z : EuclideanSpace ℂ ι) (i : ι) :
    unscaledRealCoordinatesOfComplexVector z (i, 1) = Complex.im (z i) := by
  simp [unscaledRealCoordinatesOfComplexVector]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Left inverse for the unscaled coordinate equivalence. -/
theorem unscaled_complex_real_left_inv {ι : Type*} [Fintype ι]
    (z : EuclideanSpace ℂ ι) :
    unscaledComplexVectorOfRealCoordinates (unscaledRealCoordinatesOfComplexVector z) = z := by
  ext i
  simp

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Right inverse for the unscaled coordinate equivalence. -/
theorem unscaled_complex_real_right_inv {ι : Type*} [Fintype ι]
    (x : ComplexRealCoordSpace ι) :
    unscaledRealCoordinatesOfComplexVector (unscaledComplexVectorOfRealCoordinates x) = x := by
  ext ik
  rcases ik with ⟨i, k⟩
  fin_cases k <;> simp

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The unscaled coordinate identification preserves the Euclidean norm. -/
theorem unscaledComplexVectorOfRealCoordinates_norm
    {ι : Type*} [Fintype ι] (x : ComplexRealCoordSpace ι) :
    ‖unscaledComplexVectorOfRealCoordinates x‖ = ‖x‖ := by
  have hterm : ∀ a b : ℝ, ‖((a : ℂ) + (b : ℂ) * Complex.I)‖ ^ 2 = a ^ 2 + b ^ 2 := by
    intro a b
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply]
    ring
  have hsq : ‖unscaledComplexVectorOfRealCoordinates x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp only [unscaledComplexVectorOfRealCoordinates_apply]
    simp_rw [hterm]
    rw [← Finset.univ_product_univ]
    rw [Finset.sum_product]
    simp [Finset.sum_add_distrib]
  nlinarith [norm_nonneg (unscaledComplexVectorOfRealCoordinates x), norm_nonneg x]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The unscaled real-coordinate/complex-vector identification as a real
linear isometric equivalence. -/
def complexRealCoordLinearIsometryEquiv (ι : Type*) [Fintype ι] :
    ComplexRealCoordSpace ι ≃ₗᵢ[ℝ] EuclideanSpace ℂ ι := by
  refine LinearIsometryEquiv.mk ?e ?norm
  · refine
      { toFun := unscaledComplexVectorOfRealCoordinates
        invFun := unscaledRealCoordinatesOfComplexVector
        left_inv := unscaled_complex_real_right_inv
        right_inv := unscaled_complex_real_left_inv
        map_add' := ?_
        map_smul' := ?_ }
    · intro x y
      ext i
      simp [unscaledComplexVectorOfRealCoordinates]
      ring_nf
    · intro a x
      ext i
      simp [unscaledComplexVectorOfRealCoordinates, smul_add, mul_assoc]
      change
        (a : ℂ) * (x (i, 0) : ℂ) + (a : ℂ) * ((x (i, 1) : ℂ) * Complex.I) =
          (a : ℂ) * (x (i, 0) : ℂ) + (a : ℂ) * ((x (i, 1) : ℂ) * Complex.I)
      rfl
  · exact unscaledComplexVectorOfRealCoordinates_norm

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Convert a standard-complex-Gaussian-scaled complex vector back to real
coordinates.  This is the inverse of `complexVectorOfRealCoordinates`; it is
not an isometry because the forward map contains the global factor
`1 / sqrt 2`. -/
def realCoordinatesOfComplexVector {ι : Type*} [Fintype ι]
    (z : EuclideanSpace ℂ ι) : ComplexRealCoordSpace ι :=
  WithLp.toLp 2
    (fun ik : ι × Fin 2 =>
      if ik.2 = 0 then Real.sqrt 2 * Complex.re (z ik.1)
      else Real.sqrt 2 * Complex.im (z ik.1))

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
@[simp] theorem realCoordinatesOfComplexVector_apply_zero
    {ι : Type*} [Fintype ι] (z : EuclideanSpace ℂ ι) (i : ι) :
    realCoordinatesOfComplexVector z (i, 0) = Real.sqrt 2 * Complex.re (z i) := by
  simp [realCoordinatesOfComplexVector]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
@[simp] theorem realCoordinatesOfComplexVector_apply_one
    {ι : Type*} [Fintype ι] (z : EuclideanSpace ℂ ι) (i : ι) :
    realCoordinatesOfComplexVector z (i, 1) = Real.sqrt 2 * Complex.im (z i) := by
  simp [realCoordinatesOfComplexVector]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The scaled real-coordinate map is a left inverse to the project concrete
complex-Gaussian coordinate map. -/
theorem complexVector_realCoordinates_left_inv
    {ι : Type*} [Fintype ι] (z : EuclideanSpace ℂ ι) :
    complexVectorOfRealCoordinates (ι := ι) (realCoordinatesOfComplexVector z) = z := by
  ext i
  simp [GaussianModel.complexGaussianScale]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The scaled real-coordinate map is a right inverse to the project concrete
complex-Gaussian coordinate map. -/
theorem complexVector_realCoordinates_right_inv
    {ι : Type*} [Fintype ι] (x : ComplexRealCoordSpace ι) :
    realCoordinatesOfComplexVector (complexVectorOfRealCoordinates (ι := ι) x) = x := by
  have hsqrt : Real.sqrt 2 * (Real.sqrt 2 / 2) = 1 := by
    have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := by
      rw [← sq, Real.sq_sqrt (by norm_num)]
    nlinarith
  ext ik
  rcases ik with ⟨i, k⟩
  fin_cases k
  · simp [GaussianModel.complexGaussianScale]
    rw [← mul_assoc, hsqrt, one_mul]
  · simp [GaussianModel.complexGaussianScale]
    rw [← mul_assoc, hsqrt, one_mul]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The project concrete complex-coordinate map is the unscaled coordinate
isometry followed by the scalar `1 / sqrt 2`. -/
theorem complexVectorOfRealCoordinates_eq_smul_unscaled
    {ι : Type*} [Fintype ι] (x : ComplexRealCoordSpace ι) :
    complexVectorOfRealCoordinates (ι := ι) x =
      ((complexGaussianScale : ℝ) : ℂ) • unscaledComplexVectorOfRealCoordinates x := by
  ext i
  simp [GaussianModel.complexGaussianScale, unscaledComplexVectorOfRealCoordinates]
  ring_nf

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Real-coordinate action corresponding to a complex unitary/isometric
equivalence on complex coordinates. -/
def complexUnitaryRealCoordinateIsometry
    {ι : Type*} [Fintype ι]
    (U : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι) :
    ComplexRealCoordSpace ι ≃ₗᵢ[ℝ] ComplexRealCoordSpace ι :=
  (complexRealCoordLinearIsometryEquiv ι).trans
    ((complexEuclideanLinearIsometryEquivRestrictScalarsReal U).trans
      (complexRealCoordLinearIsometryEquiv ι).symm)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The real-coordinate action is the correct lift of the complex unitary
action through the scaled concrete complex-Gaussian coordinate map. -/
theorem complexVectorOfRealCoordinates_complexUnitaryRealCoordinateIsometry
    {ι : Type*} [Fintype ι]
    (U : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι)
    (x : ComplexRealCoordSpace ι) :
    complexVectorOfRealCoordinates (ι := ι) (complexUnitaryRealCoordinateIsometry U x) =
      U (complexVectorOfRealCoordinates (ι := ι) x) := by
  let c : ℂ := ((complexGaussianScale : ℝ) : ℂ)
  have hscaled :
      complexVectorOfRealCoordinates (ι := ι) x =
        c • unscaledComplexVectorOfRealCoordinates x := by
    simpa [c] using complexVectorOfRealCoordinates_eq_smul_unscaled x
  have hscaledU :
      complexVectorOfRealCoordinates (ι := ι) (complexUnitaryRealCoordinateIsometry U x) =
        c • unscaledComplexVectorOfRealCoordinates
          (complexUnitaryRealCoordinateIsometry U x) := by
    simpa [c] using
      complexVectorOfRealCoordinates_eq_smul_unscaled
        (complexUnitaryRealCoordinateIsometry U x)
  have hunscaled :
      unscaledComplexVectorOfRealCoordinates (complexUnitaryRealCoordinateIsometry U x) =
        U (unscaledComplexVectorOfRealCoordinates x) := by
    change
      (complexRealCoordLinearIsometryEquiv ι)
          (complexUnitaryRealCoordinateIsometry U x) =
        U ((complexRealCoordLinearIsometryEquiv ι) x)
    simp [complexUnitaryRealCoordinateIsometry]
    rfl
  calc
    complexVectorOfRealCoordinates (ι := ι) (complexUnitaryRealCoordinateIsometry U x)
        = c • unscaledComplexVectorOfRealCoordinates
            (complexUnitaryRealCoordinateIsometry U x) := hscaledU
    _ = c • U (unscaledComplexVectorOfRealCoordinates x) := by rw [hunscaled]
    _ = U (c • unscaledComplexVectorOfRealCoordinates x) := by
      exact (U.map_smul c (unscaledComplexVectorOfRealCoordinates x)).symm
    _ = U (complexVectorOfRealCoordinates (ι := ι) x) := by rw [hscaled]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The project concrete standard complex Gaussian vector measure, with real
and imaginary parts of variance `1/2`, is invariant under every complex
unitary/isometric equivalence. -/
theorem standardComplexGaussianVectorMeasure_map_complexLinearIsometryEquiv
    {ι : Type*} [Fintype ι]
    (U : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι) :
    Measure.map U (standardComplexGaussianVectorMeasure ι) =
      standardComplexGaussianVectorMeasure ι := by
  let C : ComplexRealCoordSpace ι → EuclideanSpace ℂ ι :=
    complexVectorOfRealCoordinates (ι := ι)
  let R : ComplexRealCoordSpace ι ≃ₗᵢ[ℝ] ComplexRealCoordSpace ι :=
    complexUnitaryRealCoordinateIsometry U
  have hcomp : U ∘ C = C ∘ R := by
    funext x
    exact (complexVectorOfRealCoordinates_complexUnitaryRealCoordinateIsometry U x).symm
  unfold standardComplexGaussianVectorMeasure
  calc
    Measure.map U (Measure.map C (ProbabilityTheory.stdGaussian (ComplexRealCoordSpace ι)))
        = Measure.map (U ∘ C) (ProbabilityTheory.stdGaussian (ComplexRealCoordSpace ι)) := by
          rw [Measure.map_map]
          · exact U.continuous.measurable
          · exact measurable_complexVectorOfRealCoordinates ι
    _ = Measure.map (C ∘ R) (ProbabilityTheory.stdGaussian (ComplexRealCoordSpace ι)) := by
          rw [hcomp]
    _ = Measure.map C (Measure.map R (ProbabilityTheory.stdGaussian (ComplexRealCoordSpace ι))) := by
          rw [Measure.map_map]
          · exact measurable_complexVectorOfRealCoordinates ι
          · exact R.continuous.measurable
    _ = Measure.map C (ProbabilityTheory.stdGaussian (ComplexRealCoordSpace ι)) := by
          rw [ProbabilityTheory.stdGaussian_map R]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Sum-of-squared-complex-coordinate norm as the real part of the star dot
product. -/
theorem complex_vector_sum_norm_sq_eq_re_star_dot
    {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    ∑ i : ι, ‖v i‖ ^ 2 = RCLike.re (star v ⬝ᵥ v) := by
  simp only [dotProduct, Pi.star_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show RCLike.re (star (v i) * v i) = Complex.normSq (v i) by
    simp [Complex.normSq_apply]]
  rw [Complex.normSq_eq_norm_sq]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- A matrix unitary preserves the complex star dot product after `mulVec`. -/
theorem matrixUnitary_mulVec_star_dotProduct
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitary (Matrix ι ι ℂ)) (v : ι → ℂ) :
    star ((U : Matrix ι ι ℂ) *ᵥ v) ⬝ᵥ ((U : Matrix ι ι ℂ) *ᵥ v) =
      star v ⬝ᵥ v := by
  rw [Matrix.star_mulVec]
  rw [Matrix.dotProduct_mulVec]
  rw [Matrix.vecMul_vecMul]
  have hUU : ((U : Matrix ι ι ℂ)ᴴ * (U : Matrix ι ι ℂ)) = 1 := by
    rw [← star_eq_conjTranspose]
    exact Unitary.coe_star_mul_self U
  rw [hUU]
  simp

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- A matrix unitary acts isometrically on complex Euclidean coordinates. -/
theorem matrixUnitary_toEuclideanCLM_norm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitary (Matrix ι ι ℂ)) (x : EuclideanSpace ℂ ι) :
    ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (U : Matrix ι ι ℂ) x‖ = ‖x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  rw [complex_vector_sum_norm_sq_eq_re_star_dot,
    complex_vector_sum_norm_sq_eq_re_star_dot]
  rw [Matrix.ofLp_toEuclideanCLM]
  exact congrArg RCLike.re (matrixUnitary_mulVec_star_dotProduct U x.ofLp)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The linear equivalence on `EuclideanSpace` induced by a matrix unitary. -/
noncomputable def matrixUnitaryLinearEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitary (Matrix ι ι ℂ)) :
    EuclideanSpace ℂ ι ≃ₗ[ℂ] EuclideanSpace ℂ ι where
  toFun := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (U : Matrix ι ι ℂ)
  invFun := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
    ((star U : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ)
  left_inv := by
    intro x
    ext i
    simp [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_mulVec]
  right_inv := by
    intro x
    ext i
    simp [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_mulVec]
  map_add' := by
    intro x y
    exact map_add _ _ _
  map_smul' := by
    intro c x
    exact map_smul _ _ _

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
@[simp] theorem matrixUnitaryLinearEquiv_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitary (Matrix ι ι ℂ)) (x : EuclideanSpace ℂ ι) :
    matrixUnitaryLinearEquiv U x =
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (U : Matrix ι ι ℂ) x :=
  rfl

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
@[simp] theorem matrixUnitaryLinearEquiv_symm_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitary (Matrix ι ι ℂ)) (x : EuclideanSpace ℂ ι) :
    (matrixUnitaryLinearEquiv U).symm x =
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
        ((star U : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) x :=
  rfl

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The complex linear isometric equivalence induced by a matrix unitary. -/
noncomputable def matrixUnitaryLinearIsometryEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitary (Matrix ι ι ℂ)) :
    EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι where
  toLinearEquiv := matrixUnitaryLinearEquiv U
  norm_map' := matrixUnitary_toEuclideanCLM_norm U

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
@[simp] theorem matrixUnitaryLinearIsometryEquiv_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitary (Matrix ι ι ℂ)) (x : EuclideanSpace ℂ ι) :
    matrixUnitaryLinearIsometryEquiv U x =
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (U : Matrix ι ι ℂ) x :=
  rfl

omit [Fintype σ] in
/-- The spectral-theorem unitary for `H_u = (|u⟩⟨u|)^Γ` acts isometrically on
complex Euclidean coordinates. -/
theorem rankOneProjectorGamma_eigenvectorUnitary_toEuclideanCLM_norm
    (u : BipVector p q) (x : BipVector p q) :
    ‖Matrix.toEuclideanCLM (n := RandomMatrixModel.BipIndex p q) (𝕜 := ℂ)
        ((rankOneProjectorGamma_isHermitian (p := p) (q := q) u).eigenvectorUnitary :
          BipMatrix p q) x‖ = ‖x‖ := by
  exact matrixUnitary_toEuclideanCLM_norm
    ((rankOneProjectorGamma_isHermitian (p := p) (q := q) u).eigenvectorUnitary) x

omit [Fintype σ] in
/-- The adjoint spectral-theorem unitary for `H_u = (|u⟩⟨u|)^Γ` also acts
isometrically on complex Euclidean coordinates. -/
theorem rankOneProjectorGamma_star_eigenvectorUnitary_toEuclideanCLM_norm
    (u : BipVector p q) (x : BipVector p q) :
    ‖Matrix.toEuclideanCLM (n := RandomMatrixModel.BipIndex p q) (𝕜 := ℂ)
        (((star
            (rankOneProjectorGamma_isHermitian
              (p := p) (q := q) u).eigenvectorUnitary) :
            unitary (BipMatrix p q)) : BipMatrix p q) x‖ = ‖x‖ := by
  exact matrixUnitary_toEuclideanCLM_norm
    (star (rankOneProjectorGamma_isHermitian (p := p) (q := q) u).eigenvectorUnitary) x

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Existence of a finite internal `(1 / 4)`-net of the complex unit sphere,
with an explicit finite cardinality witness.

This is the compactness/totally-boundedness input needed by
`netToOperatorNorm`.  The sharper volumetric cardinality estimate is proved in
`exists_quarter_net_unit_sphere_card_le_pow` below. -/
theorem exists_finite_quarter_net_unit_sphere
    {ι : Type*} [Fintype ι] :
    ∃ N : Set (Metric.sphere (0 : EuclideanSpace ℂ ι) 1),
      N.Finite ∧
        (∀ x : Metric.sphere (0 : EuclideanSpace ℂ ι) 1,
          ∃ u ∈ N,
            ‖(x : EuclideanSpace ℂ ι) - (u : EuclideanSpace ℂ ι)‖ ≤
              (1 / 4 : ℝ)) ∧
        ∃ m : ℕ, N.encard = m := by
  classical
  let S := Metric.sphere (0 : EuclideanSpace ℂ ι) 1
  have hcompact : IsCompact (Set.univ : Set S) := isCompact_univ
  have hε : ((1 / 4 : ℝ≥0) : ℝ≥0) ≠ 0 := by norm_num
  rcases Metric.exists_finite_isCover_of_isCompact
      (X := S) (ε := (1 / 4 : ℝ≥0)) (s := Set.univ) hε hcompact with
    ⟨N, _hNsub, hNfinite, hcover⟩
  refine ⟨N, hNfinite, ?_, hNfinite.exists_encard_eq_coe⟩
  intro x
  rcases hcover (Set.mem_univ x) with ⟨u, huN, hxu⟩
  refine ⟨u, huN, ?_⟩
  have hnndist : nndist x u ≤ (1 / 4 : ℝ≥0) := edist_le_coe.mp hxu
  have hdist : dist x u ≤ (1 / 4 : ℝ) := by
    exact_mod_cast hnndist
  have hdist_ambient :
      dist (x : EuclideanSpace ℂ ι) (u : EuclideanSpace ℂ ι) ≤ (1 / 4 : ℝ) := by
    simpa [Subtype.dist_eq] using hdist
  simpa [dist_eq_norm] using hdist_ambient

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The real dimension of complex Euclidean `D`-space is `2D`. -/
theorem complex_euclidean_real_finrank
    {ι : Type*} [Fintype ι] :
    Module.finrank ℝ (EuclideanSpace ℂ ι) = 2 * Fintype.card ι := by
  rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ ι)]
  simp [Complex.finrank_real_complex, finrank_euclideanSpace, mul_comm]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Volume of Euclidean balls in complex coordinates, viewed as a real inner-product space. -/
theorem volume_complex_euclidean_ball
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : EuclideanSpace ℂ ι) (r : ℝ) :
    volume (Metric.ball x r) =
      ENNReal.ofReal r ^ (2 * Fintype.card ι) *
        ENNReal.ofReal
          (Real.sqrt Real.pi ^ (2 * Fintype.card ι) /
            Real.Gamma ((2 * Fintype.card ι : ℕ) / 2 + 1)) := by
  rw [InnerProductSpace.volume_ball, complex_euclidean_real_finrank]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- A `(1 / 4)`-separated finite subset of the complex unit sphere has at most
`81 ^ D` points, where `D` is the complex dimension.

This is the standard volumetric packing argument: balls of radius `1 / 8`
around separated sphere points are disjoint and lie in the ambient ball of
radius `9 / 8`.  The real dimension is `2D`, so the volume ratio is
`9 ^ (2D) = 81 ^ D`. -/
theorem complex_unit_sphere_quarter_separated_finset_card_le
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (F : Finset (EuclideanSpace ℂ ι))
    (hunit : ∀ x ∈ F, x ∈ Metric.sphere (0 : EuclideanSpace ℂ ι) 1)
    (hsep : ∀ x ∈ F, ∀ y ∈ F, x ≠ y →
      ((1 / 4 : ℝ≥0) : ℝ≥0∞) < edist x y) :
    F.card ≤ 81 ^ Fintype.card ι := by
  classical
  let E := EuclideanSpace ℂ ι
  let d : ℕ := 2 * Fintype.card ι
  let r : ℝ := 1 / 8
  let R : ℝ := 9 / 8
  let base : ℝ≥0∞ :=
    ENNReal.ofReal
      (Real.sqrt Real.pi ^ d /
        Real.Gamma ((d : ℕ) / 2 + 1))
  let small : ℝ≥0∞ := ENNReal.ofReal r ^ d * base
  let big : ℝ≥0∞ := ENNReal.ofReal R ^ d * base
  have hdisj : Set.PairwiseDisjoint (F : Set E) (fun x => Metric.ball x r) := by
    intro x hx y hy hxy
    refine Set.disjoint_left.mpr ?_
    intro z hzx hzy
    have hxz : dist x z < (1 / 8 : ℝ) := by
      simpa [r, dist_comm] using hzx
    have hzy' : dist z y < (1 / 8 : ℝ) := by
      simpa [r] using hzy
    have hdist_lt : dist x y < (1 / 4 : ℝ) := by
      calc
        dist x y ≤ dist x z + dist z y := dist_triangle x z y
        _ < (1 / 8 : ℝ) + (1 / 8 : ℝ) := add_lt_add hxz hzy'
        _ = (1 / 4 : ℝ) := by norm_num
    have hed_lt' : edist x y < ((1 / 4 : ℝ≥0) : ℝ≥0∞) := by
      rw [edist_lt_coe]
      exact_mod_cast hdist_lt
    have hsep_xy := hsep x hx y hy hxy
    exact (not_lt_of_ge hsep_xy.le) hed_lt'
  have hUnion_subset : (⋃ x ∈ F, Metric.ball x r) ⊆ Metric.ball (0 : E) R := by
    intro z hz
    rcases Set.mem_iUnion.mp hz with ⟨x, hz⟩
    rcases Set.mem_iUnion.mp hz with ⟨hxF, hzball⟩
    have hxnorm : ‖x‖ = 1 := by
      have hxSphere := hunit x hxF
      simpa [Metric.mem_sphere, dist_eq_norm] using hxSphere
    have hzdist : dist z x < (1 / 8 : ℝ) := by
      simpa [r] using hzball
    have hnorm_lt : ‖z‖ < (9 / 8 : ℝ) := by
      calc
        ‖z‖ = dist z (0 : E) := by rw [dist_zero_right]
        _ ≤ dist z x + dist x (0 : E) := dist_triangle z x 0
        _ = dist z x + ‖x‖ := by rw [dist_zero_right]
        _ < (1 / 8 : ℝ) + 1 := add_lt_add_of_lt_of_le hzdist (le_of_eq hxnorm)
        _ = (9 / 8 : ℝ) := by norm_num
    simpa [Metric.mem_ball, R, dist_zero_right] using hnorm_lt
  have hmeasure_union :
      volume (⋃ x ∈ F, Metric.ball x r) = ∑ x ∈ F, volume (Metric.ball x r) := by
    exact measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)
  have hvol_small (x : E) : volume (Metric.ball x r) = small := by
    simp [small, base, d, r, volume_complex_euclidean_ball (ι := ι) x]
  have hvol_big : volume (Metric.ball (0 : E) R) = big := by
    simp [big, base, d, R, volume_complex_euclidean_ball (ι := ι) (0 : E)]
  have hsum_small : (∑ x ∈ F, volume (Metric.ball x r)) = (F.card : ℝ≥0∞) * small := by
    simp [hvol_small]
  have hmeasure_le : (F.card : ℝ≥0∞) * small ≤ big := by
    calc
      (F.card : ℝ≥0∞) * small = ∑ x ∈ F, volume (Metric.ball x r) := hsum_small.symm
      _ = volume (⋃ x ∈ F, Metric.ball x r) := hmeasure_union.symm
      _ ≤ volume (Metric.ball (0 : E) R) := measure_mono hUnion_subset
      _ = big := hvol_big
  have hratio : big = ((81 : ℝ≥0∞) ^ Fintype.card ι) * small := by
    have hpow : ENNReal.ofReal R ^ d =
        ((81 : ℝ≥0∞) ^ Fintype.card ι) * ENNReal.ofReal r ^ d := by
      dsimp [R, r, d]
      have hreal : (9 / 8 : ℝ) ^ (2 * Fintype.card ι) =
          (81 : ℝ) ^ Fintype.card ι * (1 / 8 : ℝ) ^ (2 * Fintype.card ι) := by
        rw [pow_mul, pow_mul]
        have hb : (9 / 8 : ℝ) ^ 2 = (81 : ℝ) * (1 / 8 : ℝ) ^ 2 := by norm_num
        rw [hb, mul_pow]
      rw [← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 9 / 8) (2 * Fintype.card ι)]
      rw [← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 1 / 8) (2 * Fintype.card ι)]
      have h81 : (81 : ℝ≥0∞) ^ Fintype.card ι =
          ENNReal.ofReal ((81 : ℝ) ^ Fintype.card ι) := by
        rw [ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ (81 : ℝ))]
        norm_num
      rw [h81]
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (81 : ℝ) ^ Fintype.card ι)]
      rw [hreal]
    dsimp [big, small]
    rw [hpow]
    ring
  have hsmall_ne_zero : small ≠ 0 := by
    dsimp [small, base, r, d]
    have hbase_pos :
        0 < Real.sqrt Real.pi ^ (2 * Fintype.card ι) /
          Real.Gamma (((2 * Fintype.card ι : ℕ) : ℝ) / 2 + 1) := by
      exact div_pos
        (pow_pos (Real.sqrt_pos_of_pos Real.pi_pos) _)
        (Real.Gamma_pos_of_pos (by positivity))
    have hpow_ne_zero : ENNReal.ofReal (1 / 8 : ℝ) ^ (2 * Fintype.card ι) ≠ 0 :=
      ENNReal.pow_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr (by norm_num)) _
    have hbase_ne_zero :
        ENNReal.ofReal
          (Real.sqrt Real.pi ^ (2 * Fintype.card ι) /
            Real.Gamma (((2 * Fintype.card ι : ℕ) : ℝ) / 2 + 1)) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr hbase_pos
    exact ne_of_gt (ENNReal.mul_pos hpow_ne_zero hbase_ne_zero)
  have hsmall_ne_top : small ≠ ⊤ := by
    dsimp [small, base, r, d]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
  have hcard_le_enn : (F.card : ℝ≥0∞) ≤ (81 : ℝ≥0∞) ^ Fintype.card ι := by
    rw [hratio] at hmeasure_le
    exact (ENNReal.mul_le_mul_iff_left hsmall_ne_zero hsmall_ne_top).mp hmeasure_le
  exact_mod_cast hcard_le_enn

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- There is a `(1 / 4)`-net of the complex unit sphere with cardinality at
most `81 ^ D`, where `D` is the complex dimension. -/
theorem exists_quarter_net_unit_sphere_card_le_pow
    {ι : Type*} [Fintype ι] :
    ∃ N : Set (Metric.sphere (0 : EuclideanSpace ℂ ι) 1),
      N.Finite ∧
        (∀ x : Metric.sphere (0 : EuclideanSpace ℂ ι) 1,
          ∃ u ∈ N,
            ‖(x : EuclideanSpace ℂ ι) - (u : EuclideanSpace ℂ ι)‖ ≤
              (1 / 4 : ℝ)) ∧
        N.encard ≤ (81 : ℕ∞) ^ Fintype.card ι := by
  classical
  let E := EuclideanSpace ℂ ι
  by_cases hι : Nonempty ι
  · let A : Set E := Metric.sphere (0 : E) 1
    haveI : Nonempty ι := hι
    have hcompact : IsCompact A := isCompact_sphere (0 : E) 1
    have hε_eighth : ((1 / 8 : ℝ≥0) : ℝ≥0) ≠ 0 := by norm_num
    rcases Metric.exists_finite_isCover_of_isCompact
        (X := E) (ε := (1 / 8 : ℝ≥0)) (s := A) hε_eighth hcompact with
      ⟨C, _hCsub, hCfinite, hCcover⟩
    have hpack_le_ext :
        Metric.packingNumber (ε := (1 / 4 : ℝ≥0)) A ≤
          Metric.externalCoveringNumber (ε := (1 / 8 : ℝ≥0)) A := by
      have htwo : (2 * (8 : ℝ≥0)⁻¹ : ℝ≥0) = (4 : ℝ≥0)⁻¹ := by norm_num
      simpa [one_div, htwo] using Metric.packingNumber_two_mul_le_externalCoveringNumber
        (X := E) (ε := (1 / 8 : ℝ≥0)) (A := A)
    have hpack_lt_top : Metric.packingNumber (ε := (1 / 4 : ℝ≥0)) A < ⊤ := by
      exact lt_of_le_of_lt
        (hpack_le_ext.trans (Metric.IsCover.externalCoveringNumber_le_encard hCcover))
        hCfinite.encard_lt_top
    have hpack_ne_top : Metric.packingNumber (ε := (1 / 4 : ℝ≥0)) A ≠ ⊤ :=
      ne_of_lt hpack_lt_top
    let M : Set E := Metric.maximalSeparatedSet (ε := (1 / 4 : ℝ≥0)) A
    let N : Set (Metric.sphere (0 : E) 1) := {x | (x : E) ∈ M}
    have hMsubset : M ⊆ A :=
      Metric.maximalSeparatedSet_subset (ε := (1 / 4 : ℝ≥0)) (A := A)
    have hMfinite : M.Finite := by
      dsimp [M]
      rw [Metric.maximalSeparatedSet, dif_pos hpack_ne_top]
      exact (Metric.exists_set_encard_eq_packingNumber
        (X := E) (ε := (1 / 4 : ℝ≥0)) (A := A) hpack_ne_top).choose_spec.2.1
    have hMsep : Metric.IsSeparated ((1 / 4 : ℝ≥0) : ℝ≥0∞) M :=
      Metric.isSeparated_maximalSeparatedSet (ε := (1 / 4 : ℝ≥0)) (A := A)
    have hMcard : hMfinite.toFinset.card ≤ 81 ^ Fintype.card ι := by
      refine complex_unit_sphere_quarter_separated_finset_card_le
        (ι := ι) hMfinite.toFinset ?_ ?_
      · intro x hx
        exact hMsubset (by simpa using hx)
      · intro x hx y hy hxy
        exact hMsep (by simpa using hx) (by simpa using hy) hxy
    have hMencard_le : M.encard ≤ (81 : ℕ∞) ^ Fintype.card ι := by
      rw [hMfinite.encard_eq_coe_toFinset_card]
      exact_mod_cast hMcard
    have hNfinite : N.Finite := by
      exact hMfinite.preimage (Subtype.val_injective.injOn)
    have hNencard_eq : N.encard = M.encard := by
      have hrange : M ⊆ Set.range (fun x : Metric.sphere (0 : E) 1 => (x : E)) := by
        intro x hx
        exact ⟨⟨x, hMsubset hx⟩, rfl⟩
      simpa [N] using
        (Set.encard_preimage_of_injective_subset_range
          (f := fun x : Metric.sphere (0 : E) 1 => (x : E))
          Subtype.val_injective hrange)
    refine ⟨N, hNfinite, ?_, ?_⟩
    · intro x
      have hcoverM := Metric.isCover_maximalSeparatedSet
        (ε := (1 / 4 : ℝ≥0)) (A := A) hpack_ne_top
      rcases hcoverM x.property with ⟨u, huM, hxu⟩
      let u' : Metric.sphere (0 : E) 1 := ⟨u, hMsubset huM⟩
      refine ⟨u', huM, ?_⟩
      have hnndist : nndist (x : E) (u : E) ≤ (1 / 4 : ℝ≥0) := edist_le_coe.mp hxu
      have hdist : dist (x : E) (u : E) ≤ (1 / 4 : ℝ) := by
        exact_mod_cast hnndist
      simpa [dist_eq_norm, u'] using hdist
    · rw [hNencard_eq]
      exact hMencard_le
  · haveI : IsEmpty ι := not_nonempty_iff.mp hι
    have hsphere_empty : Metric.sphere (0 : E) 1 = (∅ : Set E) := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hx0 : x = 0 := by
        ext i
        exact isEmptyElim i
      have hdist : dist x (0 : E) = 1 := by
        simpa [Metric.mem_sphere] using hx
      simp [hx0] at hdist
    refine ⟨∅, Set.finite_empty, ?_, by simp⟩
    intro x
    exfalso
    have hx : (x : E) ∈ Metric.sphere (0 : E) 1 := x.property
    have hxempty : (x : E) ∈ (∅ : Set E) := by
      simp [hsphere_empty] at hx
    exact hxempty

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Standard complex Gaussian vectors are invariant under matrix-unitary
coordinates. -/
theorem standardComplexGaussianVectorMeasure_map_matrixUnitary
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitary (Matrix ι ι ℂ)) :
    Measure.map (matrixUnitaryLinearIsometryEquiv U)
        (standardComplexGaussianVectorMeasure ι) =
      standardComplexGaussianVectorMeasure ι := by
  exact standardComplexGaussianVectorMeasure_map_complexLinearIsometryEquiv
    (matrixUnitaryLinearIsometryEquiv U)

omit [DecidableEq p] [DecidableEq q] in
/-- The canonical real-coordinate sample measure is invariant under the
real-coordinate lift of any complex unitary/isometric equivalence on all
sample entries at once. -/
theorem gaussianSampleMeasure_map_complexUnitaryRealCoordinateIsometry
    (U :
      EuclideanSpace ℂ (SampleCoord p q σ) ≃ₗᵢ[ℂ]
        EuclideanSpace ℂ (SampleCoord p q σ)) :
    Measure.map (complexUnitaryRealCoordinateIsometry U) (gaussianMeasure p q σ) =
      gaussianMeasure p q σ :=
  gaussianSampleMeasure_map_linearIsometryEquiv (p := p) (q := q) (σ := σ)
    (complexUnitaryRealCoordinateIsometry U)

/-- Real coordinates of one Gaussian column extracted from the full sample
space.  This is the block projection used to state the column law before
applying `complexVectorOfRealCoordinates`. -/
def columnRealCoordinates (α : σ) :
    GaussianSampleSpace p q σ → ComplexRealCoordSpace (RandomMatrixModel.BipIndex p q) :=
  fun x => WithLp.toLp 2
    (fun ik : RandomMatrixModel.BipIndex p q × Fin 2 => x ((ik.1, α), ik.2))

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
@[simp] theorem columnRealCoordinates_apply (α : σ)
    (x : GaussianSampleSpace p q σ) (i : RandomMatrixModel.BipIndex p q) (k : Fin 2) :
    columnRealCoordinates (p := p) (q := q) (σ := σ) α x (i, k) = x ((i, α), k) :=
  rfl

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
@[fun_prop] theorem measurable_columnRealCoordinates (α : σ) :
    Measurable (columnRealCoordinates (p := p) (q := q) (σ := σ) α) := by
  unfold columnRealCoordinates
  fun_prop

omit [DecidableEq p] [DecidableEq q] in
/-- Each complex Gaussian column is exactly the concrete standard-complex
coordinate map applied to its real coordinate block. -/
theorem gaussianColumn_eq_complexVectorOfRealCoordinates_comp_columnRealCoordinates
    (α : σ) :
    gaussianColumn p q σ α =
      complexVectorOfRealCoordinates (ι := RandomMatrixModel.BipIndex p q) ∘
        columnRealCoordinates (p := p) (q := q) (σ := σ) α := by
  funext x
  ext i
  rfl

omit [DecidableEq p] [DecidableEq q] in
/-- Measurability of a concrete Gaussian column. -/
@[fun_prop] theorem measurable_gaussianColumn (α : σ) :
    Measurable (gaussianColumn p q σ α) := by
  rw [gaussianColumn_eq_complexVectorOfRealCoordinates_comp_columnRealCoordinates
    (p := p) (q := q) (σ := σ) α]
  exact (measurable_complexVectorOfRealCoordinates
      (RandomMatrixModel.BipIndex p q)).comp
    (measurable_columnRealCoordinates (p := p) (q := q) (σ := σ) α)

omit [DecidableEq p] [DecidableEq q] in
/-- At the raw product-coordinate level, projecting one column block of the
sample real Gaussian gives the product standard Gaussian on that block. -/
theorem raw_columnRealCoordinates_pi_map (α : σ) :
    Measure.map
        (fun x : (SampleCoord p q σ × Fin 2) → ℝ =>
          fun ik : RandomMatrixModel.BipIndex p q × Fin 2 => x ((ik.1, α), ik.2))
        (Measure.pi (fun _ : SampleCoord p q σ × Fin 2 =>
          ProbabilityTheory.gaussianReal 0 1)) =
      Measure.pi (fun _ : RandomMatrixModel.BipIndex p q × Fin 2 =>
        ProbabilityTheory.gaussianReal 0 1) := by
  let μ : Measure ((SampleCoord p q σ × Fin 2) → ℝ) :=
    Measure.pi (fun _ : SampleCoord p q σ × Fin 2 =>
      ProbabilityTheory.gaussianReal 0 1)
  let g : RandomMatrixModel.BipIndex p q × Fin 2 → SampleCoord p q σ × Fin 2 :=
    fun ik => ((ik.1, α), ik.2)
  have hg : Function.Injective g := by
    rintro ⟨i, k⟩ ⟨j, l⟩ h
    simpa [g] using h
  have hbase :
      iIndepFun
        (fun i : SampleCoord p q σ × Fin 2 =>
          fun x : (SampleCoord p q σ × Fin 2) → ℝ => x i) μ := by
    dsimp [μ]
    exact iIndepFun_pi
      (μ := fun _ : SampleCoord p q σ × Fin 2 =>
        ProbabilityTheory.gaussianReal 0 1)
      (X := fun _ => (id : ℝ → ℝ)) (fun _ => measurable_id.aemeasurable)
  have hsel :
      iIndepFun
        (fun ik : RandomMatrixModel.BipIndex p q × Fin 2 =>
          fun x : (SampleCoord p q σ × Fin 2) → ℝ => x (g ik)) μ := by
    simpa using hbase.precomp hg
  have hmeas :
      ∀ ik : RandomMatrixModel.BipIndex p q × Fin 2,
        AEMeasurable
          (fun x : (SampleCoord p q σ × Fin 2) → ℝ => x (g ik)) μ := by
    intro ik
    exact (measurable_pi_apply (g ik)).aemeasurable
  have hmap := (iIndepFun_iff_map_fun_eq_pi_map hmeas).1 hsel
  have heval (ik : RandomMatrixModel.BipIndex p q × Fin 2) :
      Measure.map (fun x : (SampleCoord p q σ × Fin 2) → ℝ => x (g ik)) μ =
        ProbabilityTheory.gaussianReal 0 1 := by
    dsimp [μ]
    simpa using
      (measurePreserving_eval
        (μ := fun _ : SampleCoord p q σ × Fin 2 =>
          ProbabilityTheory.gaussianReal 0 1) (g ik)).map_eq
  rw [hmap]
  simp_rw [heval]

omit [DecidableEq p] [DecidableEq q] in
/-- Each real column block has the standard finite-dimensional real Gaussian
law. -/
theorem columnRealCoordinates_map_gaussianMeasure (α : σ) :
    Measure.map (columnRealCoordinates (p := p) (q := q) (σ := σ) α)
        (gaussianMeasure p q σ) =
      ProbabilityTheory.stdGaussian
        (ComplexRealCoordSpace (RandomMatrixModel.BipIndex p q)) := by
  let rawProj : ((SampleCoord p q σ × Fin 2) → ℝ) →
      (RandomMatrixModel.BipIndex p q × Fin 2) → ℝ :=
    fun x ik => x ((ik.1, α), ik.2)
  have hcomp :
      columnRealCoordinates (p := p) (q := q) (σ := σ) α ∘
          (WithLp.toLp 2 :
            ((SampleCoord p q σ × Fin 2) → ℝ) → GaussianSampleSpace p q σ) =
        (WithLp.toLp 2 :
          ((RandomMatrixModel.BipIndex p q × Fin 2) → ℝ) →
            ComplexRealCoordSpace (RandomMatrixModel.BipIndex p q)) ∘ rawProj := by
    funext x
    ext ik
    rfl
  unfold gaussianMeasure GaussianModel.gaussianSampleMeasure
  rw [← ProbabilityTheory.map_pi_eq_stdGaussian
    (ι := SampleCoord p q σ × Fin 2)]
  calc
    Measure.map (columnRealCoordinates (p := p) (q := q) (σ := σ) α)
        (Measure.map (WithLp.toLp 2)
          (Measure.pi (fun _ : SampleCoord p q σ × Fin 2 =>
            ProbabilityTheory.gaussianReal 0 1)))
        =
      Measure.map
        (columnRealCoordinates (p := p) (q := q) (σ := σ) α ∘ WithLp.toLp 2)
          (Measure.pi (fun _ : SampleCoord p q σ × Fin 2 =>
            ProbabilityTheory.gaussianReal 0 1)) := by
          rw [Measure.map_map]
          · exact measurable_columnRealCoordinates (p := p) (q := q) (σ := σ) α
          · fun_prop
    _ = Measure.map
          ((WithLp.toLp 2 :
            ((RandomMatrixModel.BipIndex p q × Fin 2) → ℝ) →
              ComplexRealCoordSpace (RandomMatrixModel.BipIndex p q)) ∘ rawProj)
          (Measure.pi (fun _ : SampleCoord p q σ × Fin 2 =>
            ProbabilityTheory.gaussianReal 0 1)) := by
          rw [hcomp]
    _ = Measure.map (WithLp.toLp 2)
          (Measure.map rawProj
            (Measure.pi (fun _ : SampleCoord p q σ × Fin 2 =>
              ProbabilityTheory.gaussianReal 0 1))) := by
          rw [Measure.map_map]
          · fun_prop
          · fun_prop
    _ = Measure.map (WithLp.toLp 2)
          (Measure.pi (fun _ : RandomMatrixModel.BipIndex p q × Fin 2 =>
            ProbabilityTheory.gaussianReal 0 1)) := by
          rw [raw_columnRealCoordinates_pi_map
            (p := p) (q := q) (σ := σ) α]
    _ = ProbabilityTheory.stdGaussian
          (ComplexRealCoordSpace (RandomMatrixModel.BipIndex p q)) := by
          exact ProbabilityTheory.map_pi_eq_stdGaussian

omit [DecidableEq p] [DecidableEq q] in
/-- Each concrete Gaussian column has the project standard complex Gaussian
law. -/
theorem gaussianColumn_map_gaussianMeasure (α : σ) :
    Measure.map (gaussianColumn p q σ α) (gaussianMeasure p q σ) =
      standardComplexGaussianVectorMeasure (RandomMatrixModel.BipIndex p q) := by
  rw [gaussianColumn_eq_complexVectorOfRealCoordinates_comp_columnRealCoordinates
    (p := p) (q := q) (σ := σ) α]
  unfold standardComplexGaussianVectorMeasure
  calc
    Measure.map
        (complexVectorOfRealCoordinates ∘
          columnRealCoordinates (p := p) (q := q) (σ := σ) α)
        (gaussianMeasure p q σ)
        =
      Measure.map (complexVectorOfRealCoordinates
          (ι := RandomMatrixModel.BipIndex p q))
        (Measure.map (columnRealCoordinates (p := p) (q := q) (σ := σ) α)
          (gaussianMeasure p q σ)) := by
          exact (Measure.map_map
            (measurable_complexVectorOfRealCoordinates
              (RandomMatrixModel.BipIndex p q))
            (measurable_columnRealCoordinates
              (p := p) (q := q) (σ := σ) α)).symm
    _ = Measure.map (complexVectorOfRealCoordinates
          (ι := RandomMatrixModel.BipIndex p q))
        (ProbabilityTheory.stdGaussian
          (ComplexRealCoordSpace (RandomMatrixModel.BipIndex p q))) := by
          rw [columnRealCoordinates_map_gaussianMeasure
            (p := p) (q := q) (σ := σ) α]

omit [DecidableEq p] [DecidableEq q] in
/-- A concrete Gaussian row, viewed as a standard complex Gaussian vector in
`ℂ^σ`. -/
def rowVector
    (G : SampleMatrix p q σ) (i : RandomMatrixModel.BipIndex p q) :
    EuclideanSpace ℂ σ :=
  WithLp.toLp 2 (fun α : σ => G i α)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
@[simp] theorem rowVector_apply
    (G : SampleMatrix p q σ) (i : RandomMatrixModel.BipIndex p q) (α : σ) :
    rowVector (p := p) (q := q) (σ := σ) G i α = G i α :=
  rfl

omit [DecidableEq p] [DecidableEq q] in
/-- The random row `i` of the canonical Gaussian sample matrix. -/
def gaussianRow
    (p q σ : Type*) [Fintype p] [Fintype q] [Fintype σ]
    (i : RandomMatrixModel.BipIndex p q) :
    GaussianSampleSpace p q σ → EuclideanSpace ℂ σ :=
  fun x => rowVector (p := p) (q := q) (σ := σ)
    (gaussianSampleMatrix p q σ x) i

omit [DecidableEq p] [DecidableEq q] in
@[simp] theorem gaussianRow_apply
    (i : RandomMatrixModel.BipIndex p q) (x : GaussianSampleSpace p q σ) :
    gaussianRow (p := p) (q := q) (σ := σ) i x =
      rowVector (p := p) (q := q) (σ := σ)
        (gaussianSampleMatrix p q σ x) i :=
  rfl

omit [DecidableEq p] [DecidableEq q] in
/-- Real coordinates of one Gaussian row extracted from the full sample
space. -/
def rowRealCoordinates (i : RandomMatrixModel.BipIndex p q) :
    GaussianSampleSpace p q σ → ComplexRealCoordSpace σ :=
  fun x => WithLp.toLp 2
    (fun ak : σ × Fin 2 => x ((i, ak.1), ak.2))

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
@[simp] theorem rowRealCoordinates_apply (i : RandomMatrixModel.BipIndex p q)
    (x : GaussianSampleSpace p q σ) (α : σ) (k : Fin 2) :
    rowRealCoordinates (p := p) (q := q) (σ := σ) i x (α, k) = x ((i, α), k) :=
  rfl

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
@[fun_prop] theorem measurable_rowRealCoordinates (i : RandomMatrixModel.BipIndex p q) :
    Measurable (rowRealCoordinates (p := p) (q := q) (σ := σ) i) := by
  unfold rowRealCoordinates
  fun_prop

omit [DecidableEq p] [DecidableEq q] in
/-- Each concrete Gaussian row is exactly the standard complex coordinate map
applied to its real coordinate block. -/
theorem gaussianRow_eq_complexVectorOfRealCoordinates_comp_rowRealCoordinates
    (i : RandomMatrixModel.BipIndex p q) :
    gaussianRow (p := p) (q := q) (σ := σ) i =
      complexVectorOfRealCoordinates (ι := σ) ∘
        rowRealCoordinates (p := p) (q := q) (σ := σ) i := by
  funext x
  ext α
  rfl

omit [DecidableEq p] [DecidableEq q] in
/-- At the raw product-coordinate level, projecting one row block of the
sample real Gaussian gives the product standard Gaussian on that block. -/
theorem raw_rowRealCoordinates_pi_map (i : RandomMatrixModel.BipIndex p q) :
    Measure.map
        (fun x : (SampleCoord p q σ × Fin 2) → ℝ =>
          fun ak : σ × Fin 2 => x ((i, ak.1), ak.2))
        (Measure.pi (fun _ : SampleCoord p q σ × Fin 2 =>
          ProbabilityTheory.gaussianReal 0 1)) =
      Measure.pi (fun _ : σ × Fin 2 =>
        ProbabilityTheory.gaussianReal 0 1) := by
  let μ : Measure ((SampleCoord p q σ × Fin 2) → ℝ) :=
    Measure.pi (fun _ : SampleCoord p q σ × Fin 2 =>
      ProbabilityTheory.gaussianReal 0 1)
  let g : σ × Fin 2 → SampleCoord p q σ × Fin 2 :=
    fun ak => ((i, ak.1), ak.2)
  have hg : Function.Injective g := by
    rintro ⟨α, k⟩ ⟨β, l⟩ h
    simpa [g] using h
  have hbase :
      iIndepFun
        (fun z : SampleCoord p q σ × Fin 2 =>
          fun x : (SampleCoord p q σ × Fin 2) → ℝ => x z) μ := by
    dsimp [μ]
    exact iIndepFun_pi
      (μ := fun _ : SampleCoord p q σ × Fin 2 =>
        ProbabilityTheory.gaussianReal 0 1)
      (X := fun _ => (id : ℝ → ℝ)) (fun _ => measurable_id.aemeasurable)
  have hsel :
      iIndepFun
        (fun ak : σ × Fin 2 =>
          fun x : (SampleCoord p q σ × Fin 2) → ℝ => x (g ak)) μ := by
    simpa using hbase.precomp hg
  have hmeas :
      ∀ ak : σ × Fin 2,
        AEMeasurable
          (fun x : (SampleCoord p q σ × Fin 2) → ℝ => x (g ak)) μ := by
    intro ak
    exact (measurable_pi_apply (g ak)).aemeasurable
  have hmap := (iIndepFun_iff_map_fun_eq_pi_map hmeas).1 hsel
  have heval (ak : σ × Fin 2) :
      Measure.map
          (fun x : (SampleCoord p q σ × Fin 2) → ℝ => x (g ak)) μ =
        ProbabilityTheory.gaussianReal 0 1 := by
    dsimp [μ]
    simpa using
      (measurePreserving_eval
        (μ := fun _ : SampleCoord p q σ × Fin 2 =>
          ProbabilityTheory.gaussianReal 0 1) (g ak)).map_eq
  rw [hmap]
  simp_rw [heval]

omit [DecidableEq p] [DecidableEq q] in
/-- Each real row block has the standard finite-dimensional real Gaussian law. -/
theorem rowRealCoordinates_map_gaussianMeasure (i : RandomMatrixModel.BipIndex p q) :
    Measure.map (rowRealCoordinates (p := p) (q := q) (σ := σ) i)
        (gaussianMeasure p q σ) =
      ProbabilityTheory.stdGaussian
        (ComplexRealCoordSpace σ) := by
  let rawProj : ((SampleCoord p q σ × Fin 2) → ℝ) →
      (σ × Fin 2) → ℝ :=
    fun x ak => x ((i, ak.1), ak.2)
  have hcomp :
      rowRealCoordinates (p := p) (q := q) (σ := σ) i ∘
          (WithLp.toLp 2 :
            ((SampleCoord p q σ × Fin 2) → ℝ) → GaussianSampleSpace p q σ) =
        (WithLp.toLp 2 :
          ((σ × Fin 2) → ℝ) → ComplexRealCoordSpace σ) ∘ rawProj := by
    funext x
    ext ak
    rfl
  unfold gaussianMeasure GaussianModel.gaussianSampleMeasure
  rw [← ProbabilityTheory.map_pi_eq_stdGaussian
    (ι := SampleCoord p q σ × Fin 2)]
  calc
    Measure.map (rowRealCoordinates (p := p) (q := q) (σ := σ) i)
        (Measure.map (WithLp.toLp 2)
          (Measure.pi (fun _ : SampleCoord p q σ × Fin 2 =>
            ProbabilityTheory.gaussianReal 0 1)))
        =
      Measure.map
        (rowRealCoordinates (p := p) (q := q) (σ := σ) i ∘ WithLp.toLp 2)
        (Measure.pi (fun _ : SampleCoord p q σ × Fin 2 =>
          ProbabilityTheory.gaussianReal 0 1)) := by
          rw [Measure.map_map]
          · exact measurable_rowRealCoordinates
              (p := p) (q := q) (σ := σ) i
          · fun_prop
    _ = Measure.map
        ((WithLp.toLp 2 :
          ((σ × Fin 2) → ℝ) → ComplexRealCoordSpace σ) ∘ rawProj)
        (Measure.pi (fun _ : SampleCoord p q σ × Fin 2 =>
          ProbabilityTheory.gaussianReal 0 1)) := by
          rw [hcomp]
    _ = Measure.map (WithLp.toLp 2)
        (Measure.map rawProj
          (Measure.pi (fun _ : SampleCoord p q σ × Fin 2 =>
            ProbabilityTheory.gaussianReal 0 1))) := by
          rw [Measure.map_map]
          · fun_prop
          · fun_prop
    _ = Measure.map (WithLp.toLp 2)
        (Measure.pi (fun _ : σ × Fin 2 =>
          ProbabilityTheory.gaussianReal 0 1)) := by
          rw [raw_rowRealCoordinates_pi_map
            (p := p) (q := q) (σ := σ) i]
    _ = ProbabilityTheory.stdGaussian
        (ComplexRealCoordSpace σ) := by
          exact ProbabilityTheory.map_pi_eq_stdGaussian

omit [DecidableEq p] [DecidableEq q] in
/-- Each concrete Gaussian row has the project standard complex Gaussian
law. -/
theorem gaussianRow_map_gaussianMeasure (i : RandomMatrixModel.BipIndex p q) :
    Measure.map (gaussianRow (p := p) (q := q) (σ := σ) i) (gaussianMeasure p q σ) =
      standardComplexGaussianVectorMeasure σ := by
  rw [gaussianRow_eq_complexVectorOfRealCoordinates_comp_rowRealCoordinates
    (p := p) (q := q) (σ := σ) i]
  unfold standardComplexGaussianVectorMeasure
  calc
    Measure.map
        (complexVectorOfRealCoordinates ∘
          rowRealCoordinates (p := p) (q := q) (σ := σ) i)
        (gaussianMeasure p q σ)
        =
      Measure.map (complexVectorOfRealCoordinates
          (ι := σ))
        (Measure.map (rowRealCoordinates (p := p) (q := q) (σ := σ) i)
          (gaussianMeasure p q σ)) := by
          exact (Measure.map_map
            (measurable_complexVectorOfRealCoordinates (σ))
            (measurable_rowRealCoordinates
              (p := p) (q := q) (σ := σ) i)).symm
    _ = Measure.map (complexVectorOfRealCoordinates
          (ι := σ))
        (ProbabilityTheory.stdGaussian
          (ComplexRealCoordSpace σ)) := by
          rw [rowRealCoordinates_map_gaussianMeasure
            (p := p) (q := q) (σ := σ) i]
    _ = standardComplexGaussianVectorMeasure σ := by
          rfl

/-- Reindexing equivalence that groups the full sample coordinate set by
Gaussian column first and row/real-imaginary coordinate second. -/
def sampleColumnIndexEquiv :
    σ × (RandomMatrixModel.BipIndex p q × Fin 2) ≃ SampleCoord p q σ × Fin 2 where
  toFun a := ((a.2.1, a.1), a.2.2)
  invFun b := (b.1.2, (b.1.1, b.2))
  left_inv := by rintro ⟨α, ⟨i, k⟩⟩; rfl
  right_inv := by rintro ⟨⟨i, α⟩, k⟩; rfl

omit [DecidableEq p] [DecidableEq q] in
/-- The joint raw real-coordinate law of all column blocks is the product of
the individual raw block laws. -/
theorem raw_columnBlocks_pi_map :
    Measure.map
        (fun x : (SampleCoord p q σ × Fin 2) → ℝ =>
          fun α : σ =>
            fun ik : RandomMatrixModel.BipIndex p q × Fin 2 => x ((ik.1, α), ik.2))
        (Measure.pi (fun _ : SampleCoord p q σ × Fin 2 =>
          ProbabilityTheory.gaussianReal 0 1)) =
      Measure.pi (fun _ : σ =>
        Measure.pi (fun _ : RandomMatrixModel.BipIndex p q × Fin 2 =>
          ProbabilityTheory.gaussianReal 0 1)) := by
  let e := sampleColumnIndexEquiv (p := p) (q := q) (σ := σ)
  let μI : SampleCoord p q σ × Fin 2 → Measure ℝ :=
    fun _ => ProbabilityTheory.gaussianReal 0 1
  let μSJ : σ × (RandomMatrixModel.BipIndex p q × Fin 2) → Measure ℝ :=
    fun _ => ProbabilityTheory.gaussianReal 0 1
  have hreindex :
      Measure.map
          (fun x : (SampleCoord p q σ × Fin 2) → ℝ =>
            fun a : σ × (RandomMatrixModel.BipIndex p q × Fin 2) => x (e a))
          (Measure.pi μI) =
        Measure.pi μSJ := by
    have h := Measure.pi_map_piCongrLeft (e := e.symm) (μ := μSJ)
    convert h using 1
  have hcurry :
      Measure.map (MeasurableEquiv.curry σ
          (RandomMatrixModel.BipIndex p q × Fin 2) ℝ)
        (Measure.pi μSJ) =
      Measure.pi (fun _ : σ =>
        Measure.pi (fun _ : RandomMatrixModel.BipIndex p q × Fin 2 =>
          ProbabilityTheory.gaussianReal 0 1)) := by
    simpa [μSJ, Measure.infinitePi_eq_pi] using
      (Measure.infinitePi_map_curry
        (μ := fun _ : σ =>
          fun _ : RandomMatrixModel.BipIndex p q × Fin 2 =>
            ProbabilityTheory.gaussianReal 0 1)
        (X := ℝ))
  calc
    Measure.map
        (fun x : (SampleCoord p q σ × Fin 2) → ℝ =>
          fun α : σ =>
            fun ik : RandomMatrixModel.BipIndex p q × Fin 2 => x ((ik.1, α), ik.2))
        (Measure.pi μI)
        =
      Measure.map (MeasurableEquiv.curry σ
          (RandomMatrixModel.BipIndex p q × Fin 2) ℝ)
        (Measure.map
          (fun x : (SampleCoord p q σ × Fin 2) → ℝ =>
            fun a : σ × (RandomMatrixModel.BipIndex p q × Fin 2) => x (e a))
          (Measure.pi μI)) := by
          rw [Measure.map_map]
          · rfl
          · exact (MeasurableEquiv.curry σ
              (RandomMatrixModel.BipIndex p q × Fin 2) ℝ).measurable
          · exact measurable_pi_lambda _ fun a => measurable_pi_apply (e a)
    _ = Measure.map (MeasurableEquiv.curry σ
          (RandomMatrixModel.BipIndex p q × Fin 2) ℝ)
        (Measure.pi μSJ) := by
          rw [hreindex]
    _ = Measure.pi (fun _ : σ =>
        Measure.pi (fun _ : RandomMatrixModel.BipIndex p q × Fin 2 =>
          ProbabilityTheory.gaussianReal 0 1)) := hcurry

omit [DecidableEq p] [DecidableEq q] in
/-- The joint law of all real column-coordinate blocks is the product of the
standard real Gaussian block laws. -/
theorem columnRealCoordinates_joint_map_gaussianMeasure :
    Measure.map
        (fun x : GaussianSampleSpace p q σ =>
          fun α : σ => columnRealCoordinates (p := p) (q := q) (σ := σ) α x)
        (gaussianMeasure p q σ) =
      Measure.pi (fun _ : σ =>
        ProbabilityTheory.stdGaussian
          (ComplexRealCoordSpace (RandomMatrixModel.BipIndex p q))) := by
  let rawBlocks : ((SampleCoord p q σ × Fin 2) → ℝ) →
      σ → (RandomMatrixModel.BipIndex p q × Fin 2) → ℝ :=
    fun x α ik => x ((ik.1, α), ik.2)
  let blockToLp : (σ → (RandomMatrixModel.BipIndex p q × Fin 2) → ℝ) →
      σ → ComplexRealCoordSpace (RandomMatrixModel.BipIndex p q) :=
    fun x α => WithLp.toLp 2 (x α)
  have hcomp :
      (fun x : GaussianSampleSpace p q σ =>
          fun α : σ => columnRealCoordinates (p := p) (q := q) (σ := σ) α x) ∘
        (WithLp.toLp 2 :
          ((SampleCoord p q σ × Fin 2) → ℝ) → GaussianSampleSpace p q σ) =
      blockToLp ∘ rawBlocks := by
    funext x
    ext α ik
    rfl
  have hblock_map :
      Measure.map blockToLp
        (Measure.pi (fun _ : σ =>
          Measure.pi (fun _ : RandomMatrixModel.BipIndex p q × Fin 2 =>
            ProbabilityTheory.gaussianReal 0 1))) =
      Measure.pi (fun _ : σ =>
        ProbabilityTheory.stdGaussian
          (ComplexRealCoordSpace (RandomMatrixModel.BipIndex p q))) := by
    dsimp [blockToLp]
    have h := Measure.pi_map_pi
      (μ := fun _ : σ =>
        Measure.pi (fun _ : RandomMatrixModel.BipIndex p q × Fin 2 =>
          ProbabilityTheory.gaussianReal 0 1))
      (f := fun _ : σ =>
        (WithLp.toLp 2 :
          ((RandomMatrixModel.BipIndex p q × Fin 2) → ℝ) →
            ComplexRealCoordSpace (RandomMatrixModel.BipIndex p q)))
      (fun _ => (by fun_prop :
        AEMeasurable (WithLp.toLp 2)
          (Measure.pi (fun _ : RandomMatrixModel.BipIndex p q × Fin 2 =>
            ProbabilityTheory.gaussianReal 0 1))))
    rw [h]
    simp_rw [ProbabilityTheory.map_pi_eq_stdGaussian]
  unfold gaussianMeasure GaussianModel.gaussianSampleMeasure
  rw [← ProbabilityTheory.map_pi_eq_stdGaussian
    (ι := SampleCoord p q σ × Fin 2)]
  calc
    Measure.map
        (fun x : GaussianSampleSpace p q σ =>
          fun α : σ => columnRealCoordinates (p := p) (q := q) (σ := σ) α x)
        (Measure.map (WithLp.toLp 2)
          (Measure.pi (fun _ : SampleCoord p q σ × Fin 2 =>
            ProbabilityTheory.gaussianReal 0 1)))
        =
      Measure.map
        ((fun x : GaussianSampleSpace p q σ =>
          fun α : σ => columnRealCoordinates (p := p) (q := q) (σ := σ) α x) ∘
            WithLp.toLp 2)
        (Measure.pi (fun _ : SampleCoord p q σ × Fin 2 =>
          ProbabilityTheory.gaussianReal 0 1)) := by
          rw [Measure.map_map]
          · exact measurable_pi_lambda _ fun α =>
              measurable_columnRealCoordinates (p := p) (q := q) (σ := σ) α
          · fun_prop
    _ = Measure.map (blockToLp ∘ rawBlocks)
          (Measure.pi (fun _ : SampleCoord p q σ × Fin 2 =>
            ProbabilityTheory.gaussianReal 0 1)) := by
          rw [hcomp]
    _ = Measure.map blockToLp
          (Measure.map rawBlocks
            (Measure.pi (fun _ : SampleCoord p q σ × Fin 2 =>
              ProbabilityTheory.gaussianReal 0 1))) := by
          rw [Measure.map_map]
          · dsimp [blockToLp]
            exact measurable_pi_lambda _ fun _ => by fun_prop
          · dsimp [rawBlocks]
            exact measurable_pi_lambda _ fun α =>
              measurable_pi_lambda _ fun ik => measurable_pi_apply ((ik.1, α), ik.2)
    _ = Measure.map blockToLp
          (Measure.pi (fun _ : σ =>
            Measure.pi (fun _ : RandomMatrixModel.BipIndex p q × Fin 2 =>
              ProbabilityTheory.gaussianReal 0 1))) := by
          rw [raw_columnBlocks_pi_map (p := p) (q := q) (σ := σ)]
    _ = Measure.pi (fun _ : σ =>
        ProbabilityTheory.stdGaussian
          (ComplexRealCoordSpace (RandomMatrixModel.BipIndex p q))) := hblock_map

omit [DecidableEq p] [DecidableEq q] in
/-- The real coordinate blocks of the columns are jointly independent. -/
theorem columnRealCoordinates_iIndepFun :
    iIndepFun
      (fun α : σ => columnRealCoordinates (p := p) (q := q) (σ := σ) α)
      (gaussianMeasure p q σ) := by
  letI : IsProbabilityMeasure (gaussianMeasure p q σ) := by
    unfold gaussianMeasure
    infer_instance
  have hmeas :
      ∀ α : σ,
        AEMeasurable
          (columnRealCoordinates (p := p) (q := q) (σ := σ) α)
          (gaussianMeasure p q σ) := by
    intro α
    exact (measurable_columnRealCoordinates (p := p) (q := q) (σ := σ) α).aemeasurable
  rw [iIndepFun_iff_map_fun_eq_pi_map hmeas]
  rw [columnRealCoordinates_joint_map_gaussianMeasure (p := p) (q := q) (σ := σ)]
  simp_rw [columnRealCoordinates_map_gaussianMeasure (p := p) (q := q) (σ := σ)]

omit [DecidableEq p] [DecidableEq q] in
/-- The concrete Gaussian columns are jointly independent. Together with
`gaussianColumn_map_gaussianMeasure`, this gives the i.i.d. standard complex
Gaussian column law. -/
theorem gaussianColumn_iIndepFun :
    iIndepFun (fun α : σ => gaussianColumn p q σ α) (gaussianMeasure p q σ) := by
  have h := columnRealCoordinates_iIndepFun (p := p) (q := q) (σ := σ)
  have hcomp := h.comp
    (fun _ : σ =>
      complexVectorOfRealCoordinates (ι := RandomMatrixModel.BipIndex p q))
    (fun _ =>
      measurable_complexVectorOfRealCoordinates (RandomMatrixModel.BipIndex p q))
  convert hcomp using 1

/-- Applying matrix-unitary coordinates to one Gaussian column preserves its
standard complex Gaussian law. -/
theorem gaussianColumn_matrixUnitary_map_gaussianMeasure
    (U : unitary (BipMatrix p q)) (α : σ) :
    Measure.map
        (fun ω : Ω p q σ =>
          matrixUnitaryLinearIsometryEquiv U (gaussianColumn p q σ α ω))
        (gaussianMeasure p q σ) =
      standardComplexGaussianVectorMeasure (RandomMatrixModel.BipIndex p q) := by
  calc
    Measure.map
        (fun ω : Ω p q σ =>
          matrixUnitaryLinearIsometryEquiv U (gaussianColumn p q σ α ω))
        (gaussianMeasure p q σ)
        = Measure.map (matrixUnitaryLinearIsometryEquiv U)
            (Measure.map (gaussianColumn p q σ α) (gaussianMeasure p q σ)) := by
            rw [Measure.map_map]
            · rfl
            · exact (matrixUnitaryLinearIsometryEquiv U).continuous.measurable
            · exact measurable_gaussianColumn (p := p) (q := q) (σ := σ) α
    _ = Measure.map (matrixUnitaryLinearIsometryEquiv U)
          (standardComplexGaussianVectorMeasure (RandomMatrixModel.BipIndex p q)) := by
            rw [gaussianColumn_map_gaussianMeasure (p := p) (q := q) (σ := σ) α]
    _ = standardComplexGaussianVectorMeasure (RandomMatrixModel.BipIndex p q) := by
            exact standardComplexGaussianVectorMeasure_map_matrixUnitary U

/-- Applying the same matrix-unitary coordinates to every Gaussian column
preserves independence. -/
theorem gaussianColumn_matrixUnitary_iIndepFun
    (U : unitary (BipMatrix p q)) :
    iIndepFun
      (fun α : σ => fun ω : Ω p q σ =>
        matrixUnitaryLinearIsometryEquiv U (gaussianColumn p q σ α ω))
      (gaussianMeasure p q σ) := by
  have h := gaussianColumn_iIndepFun (p := p) (q := q) (σ := σ)
  have hcomp := h.comp
    (fun _ : σ => matrixUnitaryLinearIsometryEquiv U)
    (fun _ => (matrixUnitaryLinearIsometryEquiv U).continuous.measurable)
  simpa using hcomp

/-- Joint law of all matrix-unitarily rotated Gaussian columns. -/
theorem gaussianColumn_matrixUnitary_joint_map_gaussianMeasure
    (U : unitary (BipMatrix p q)) :
    Measure.map
        (fun ω : Ω p q σ => fun α : σ =>
          matrixUnitaryLinearIsometryEquiv U (gaussianColumn p q σ α ω))
        (gaussianMeasure p q σ) =
      Measure.pi (fun _ : σ =>
        standardComplexGaussianVectorMeasure (RandomMatrixModel.BipIndex p q)) := by
  letI : IsProbabilityMeasure (gaussianMeasure p q σ) := by
    unfold gaussianMeasure
    infer_instance
  have hmeas :
      ∀ α : σ,
        AEMeasurable
          (fun ω : Ω p q σ =>
            matrixUnitaryLinearIsometryEquiv U (gaussianColumn p q σ α ω))
          (gaussianMeasure p q σ) := by
    intro α
    exact (((matrixUnitaryLinearIsometryEquiv U).continuous.measurable).comp
      (measurable_gaussianColumn (p := p) (q := q) (σ := σ) α)).aemeasurable
  have hindep := gaussianColumn_matrixUnitary_iIndepFun (p := p) (q := q) (σ := σ) U
  rw [iIndepFun_iff_map_fun_eq_pi_map hmeas] at hindep
  rw [hindep]
  simp_rw [gaussianColumn_matrixUnitary_map_gaussianMeasure (p := p) (q := q) (σ := σ) U]

/-- Rotating one Gaussian column by the adjoint eigenvector unitary of
`H_u = (|u⟩⟨u|)^Γ` preserves the standard complex Gaussian law. -/
theorem gaussianColumn_rankOneProjectorGamma_star_eigenvectorUnitary_map_gaussianMeasure
    (u : BipVector p q) (α : σ) :
    Measure.map
        (fun ω : Ω p q σ =>
          matrixUnitaryLinearIsometryEquiv
            (star
              (rankOneProjectorGamma_isHermitian
                (p := p) (q := q) u).eigenvectorUnitary)
            (gaussianColumn p q σ α ω))
        (gaussianMeasure p q σ) =
      standardComplexGaussianVectorMeasure (RandomMatrixModel.BipIndex p q) := by
  simpa using
    gaussianColumn_matrixUnitary_map_gaussianMeasure
      (p := p) (q := q) (σ := σ)
      (U := star
        (rankOneProjectorGamma_isHermitian
          (p := p) (q := q) u).eigenvectorUnitary)
      α

/-- The same adjoint eigenvector-unitary rotation preserves independence of
the full Gaussian column family. -/
theorem gaussianColumn_rankOneProjectorGamma_star_eigenvectorUnitary_iIndepFun
    (u : BipVector p q) :
    iIndepFun
      (fun α : σ => fun ω : Ω p q σ =>
        matrixUnitaryLinearIsometryEquiv
          (star
            (rankOneProjectorGamma_isHermitian
              (p := p) (q := q) u).eigenvectorUnitary)
          (gaussianColumn p q σ α ω))
      (gaussianMeasure p q σ) := by
  simpa using
    gaussianColumn_matrixUnitary_iIndepFun
      (p := p) (q := q) (σ := σ)
      (U := star
        (rankOneProjectorGamma_isHermitian
          (p := p) (q := q) u).eigenvectorUnitary)

/-- Joint law preservation for all Gaussian columns after rotation by the
adjoint eigenvector unitary of `H_u = (|u⟩⟨u|)^Γ`. -/
theorem gaussianColumn_rankOneProjectorGamma_star_eigenvectorUnitary_joint_map_gaussianMeasure
    (u : BipVector p q) :
    Measure.map
        (fun ω : Ω p q σ => fun α : σ =>
          matrixUnitaryLinearIsometryEquiv
            (star
              (rankOneProjectorGamma_isHermitian
                (p := p) (q := q) u).eigenvectorUnitary)
            (gaussianColumn p q σ α ω))
        (gaussianMeasure p q σ) =
      Measure.pi (fun _ : σ =>
        standardComplexGaussianVectorMeasure (RandomMatrixModel.BipIndex p q)) := by
  simpa using
    gaussianColumn_matrixUnitary_joint_map_gaussianMeasure
      (p := p) (q := q) (σ := σ)
      (U := star
        (rankOneProjectorGamma_isHermitian
          (p := p) (q := q) u).eigenvectorUnitary)

/-- Reindex `SampleCoord = (p × q) × σ` as the corresponding constant-fiber
sigma type. -/
def sampleCoordProdSigmaEquiv :
    SampleCoord p q σ ≃ Σ _ : RandomMatrixModel.BipIndex p q, σ where
  toFun := Prod.toSigma
  invFun x := (x.1, x.2)
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    cases x
    rfl

/-- Coordinatewise complex conjugation on Euclidean space. -/
def conjEuclideanVector (x : EuclideanSpace ℂ σ) : EuclideanSpace ℂ σ :=
  WithLp.toLp 2 (fun i : σ => star (x i))

omit [Fintype σ] in
@[simp] theorem conjEuclideanVector_apply
    (x : EuclideanSpace ℂ σ) (i : σ) :
    conjEuclideanVector (σ := σ) x i = star (x i) :=
  rfl

omit [Fintype σ] in
@[simp] theorem conjEuclideanVector_involutive
    (x : EuclideanSpace ℂ σ) :
    conjEuclideanVector (σ := σ) (conjEuclideanVector (σ := σ) x) = x := by
  ext i
  simp [conjEuclideanVector]

@[simp] theorem conjEuclideanVector_norm
    (x : EuclideanSpace ℂ σ) :
    ‖conjEuclideanVector (σ := σ) x‖ = ‖x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp [conjEuclideanVector]

/-- Applying the same complex linear isometry on the sample-index factor of
every row defines a complex linear isometry on the full sample-coordinate
space. -/
def sampleCoordColumnLinearIsometryEquiv
    (V : EuclideanSpace ℂ σ ≃ₗᵢ[ℂ] EuclideanSpace ℂ σ) :
    EuclideanSpace ℂ (SampleCoord p q σ) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (SampleCoord p q σ) :=
  ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (sampleCoordProdSigmaEquiv (p := p) (q := q) (σ := σ))).trans
    (((LinearIsometryEquiv.piLpCurry ℂ 2
        (fun _ : RandomMatrixModel.BipIndex p q => fun _ : σ => ℂ)).trans
      (LinearIsometryEquiv.piLpCongrRight 2
        (fun _ : RandomMatrixModel.BipIndex p q => V))).trans
      (LinearIsometryEquiv.piLpCurry ℂ 2
        (fun _ : RandomMatrixModel.BipIndex p q => fun _ : σ => ℂ)).symm)).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (sampleCoordProdSigmaEquiv (p := p) (q := q) (σ := σ)).symm)

omit [DecidableEq p] [DecidableEq q] in
@[simp] theorem sampleCoordColumnLinearIsometryEquiv_apply
    (V : EuclideanSpace ℂ σ ≃ₗᵢ[ℂ] EuclideanSpace ℂ σ)
    (x : EuclideanSpace ℂ (SampleCoord p q σ)) :
    sampleCoordColumnLinearIsometryEquiv (p := p) (q := q) (σ := σ) V x =
      WithLp.toLp 2 (fun ik : SampleCoord p q σ =>
        V (WithLp.toLp 2 (fun α : σ => x (ik.1, α))) ik.2) := by
  rcases x with ⟨x⟩
  ext ik
  rcases ik with ⟨i, j⟩
  rfl

omit [DecidableEq p] [DecidableEq q] in
/-- Algebraic rewrite of `Gv` as the linear combination of Gaussian columns
with coefficients given by `v`. -/
theorem gaussianMatrix_mulVec_eq_sum_smul_gaussianColumn
    [DecidableEq σ] (v : EuclideanSpace ℂ σ) (ω : Ω p q σ) :
    (Matrix.toEuclideanLin (𝕜 := ℂ) (m := RandomMatrixModel.BipIndex p q)
      (n := σ) (gaussianMatrix p q σ ω)) v =
      ∑ α : σ, v α • gaussianColumn p q σ α ω := by
  ext i
  change (((Matrix.toEuclideanLin (𝕜 := ℂ) (m := RandomMatrixModel.BipIndex p q)
    (n := σ) (gaussianMatrix p q σ ω)) v).ofLp i) =
      (∑ α : σ, v α • gaussianColumn p q σ α ω) i
  rw [Matrix.ofLp_toLpLin]
  simp [gaussianColumn, GaussianModel.gaussianSampleMatrix,
    GaussianModel.sampleMatrixOfRealCoordinates, GaussianModel.columnVector,
    Matrix.mulVec, dotProduct, mul_comm]

omit [DecidableEq p] [DecidableEq q] in
/-- After rotating the sample-index coordinates by an orthonormal basis `b`,
the distinguished Gaussian column is exactly `G (star (b β))`. -/
theorem gaussianColumn_sampleCoordColumnLinearIsometryEquiv
    [DecidableEq σ]
    (b : OrthonormalBasis σ ℂ (EuclideanSpace ℂ σ)) (β : σ) (ω : Ω p q σ) :
    gaussianColumn p q σ β
      (complexUnitaryRealCoordinateIsometry
        (sampleCoordColumnLinearIsometryEquiv (p := p) (q := q) (σ := σ)
          (b.equiv (EuclideanSpace.basisFun σ ℂ) (Equiv.refl σ))) ω) =
      (Matrix.toEuclideanLin (𝕜 := ℂ) (m := RandomMatrixModel.BipIndex p q)
        (n := σ) (gaussianMatrix p q σ ω)) (conjEuclideanVector (σ := σ) (b β)) := by
  classical
  ext i
  let row : EuclideanSpace ℂ σ :=
    WithLp.toLp 2 (fun α : σ =>
      complexVectorOfRealCoordinates (ι := SampleCoord p q σ) ω (i, α))
  have hcoord :=
    congrArg (fun z : EuclideanSpace ℂ (SampleCoord p q σ) => z (i, β))
      (complexVectorOfRealCoordinates_complexUnitaryRealCoordinateIsometry
        (ι := SampleCoord p q σ)
        (U := sampleCoordColumnLinearIsometryEquiv (p := p) (q := q) (σ := σ)
          (b.equiv (EuclideanSpace.basisFun σ ℂ) (Equiv.refl σ)))
        ω)
  have hpi_refl :
      LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.refl σ) =
        LinearIsometryEquiv.refl ℂ (EuclideanSpace ℂ σ) := by
    ext y α
    rfl
  have hbasis_refl :
      (EuclideanSpace.basisFun σ ℂ).repr.symm =
        LinearIsometryEquiv.refl ℂ (EuclideanSpace ℂ σ) := by
    ext y α
    change ((EuclideanSpace.basisFun σ ℂ).repr.symm y).ofLp α = y.ofLp α
    have hrepy : (EuclideanSpace.basisFun σ ℂ).repr y = y := by
      ext i
      simp [EuclideanSpace.basisFun_repr]
    calc
      ((EuclideanSpace.basisFun σ ℂ).repr.symm y).ofLp α
          = ((EuclideanSpace.basisFun σ ℂ).repr.symm
              ((EuclideanSpace.basisFun σ ℂ).repr y)).ofLp α := by rw [hrepy]
      _ = y.ofLp α := by simp
  have hrepr :
      b.equiv (EuclideanSpace.basisFun σ ℂ) (Equiv.refl σ) = b.repr := by
    ext x α
    simp [OrthonormalBasis.equiv, hpi_refl, hbasis_refl]
  have hsum :=
    congrArg (fun z : EuclideanSpace ℂ (RandomMatrixModel.BipIndex p q) => z i)
      (gaussianMatrix_mulVec_eq_sum_smul_gaussianColumn
        (p := p) (q := q) (σ := σ)
        (v := conjEuclideanVector (σ := σ) (b β)) ω)
  have hcoord' :
      gaussianColumn p q σ β
        (complexUnitaryRealCoordinateIsometry
          (sampleCoordColumnLinearIsometryEquiv (p := p) (q := q) (σ := σ)
            (b.equiv (EuclideanSpace.basisFun σ ℂ) (Equiv.refl σ))) ω) i =
        ∑ x : σ,
          (↑complexGaussianScale * ↑(ω.ofLp ((i, x), 0)) +
              Complex.I * (↑complexGaussianScale * ↑(ω.ofLp ((i, x), 1)))) *
            conjEuclideanVector (σ := σ) (b β) x := by
    simpa [gaussianColumn, GaussianModel.gaussianSampleMatrix,
      GaussianModel.sampleMatrixOfRealCoordinates, GaussianModel.columnVector,
      sampleCoordColumnLinearIsometryEquiv_apply, row, hrepr,
      OrthonormalBasis.repr_apply_apply, EuclideanSpace.inner_eq_star_dotProduct,
      conjEuclideanVector, dotProduct, mul_comm, mul_left_comm, mul_assoc] using hcoord
  refine hcoord'.trans ?_
  symm
  simpa [gaussianColumn, GaussianModel.gaussianSampleMatrix,
    GaussianModel.sampleMatrixOfRealCoordinates, GaussianModel.columnVector,
    conjEuclideanVector, dotProduct, mul_comm, mul_left_comm, mul_assoc] using hsum

omit [DecidableEq p] [DecidableEq q] in
/-- For every unit vector `v` in the sample-index space, the random vector
`Gv` has the standard complex Gaussian law in `ℂ^(p×q)`. -/
theorem gaussianMatrix_unitVector_mul_map_gaussianMeasure
    [Nonempty σ] [DecidableEq σ]
    (v : Metric.sphere (0 : EuclideanSpace ℂ σ) 1) :
    Measure.map
        (fun ω : Ω p q σ =>
          (Matrix.toEuclideanLin (𝕜 := ℂ) (m := RandomMatrixModel.BipIndex p q)
            (n := σ) (gaussianMatrix p q σ ω)) (v : EuclideanSpace ℂ σ))
        (gaussianMeasure p q σ) =
      standardComplexGaussianVectorMeasure (RandomMatrixModel.BipIndex p q) := by
  classical
  let β : σ := Classical.choice ‹Nonempty σ›
  let w : σ → EuclideanSpace ℂ σ :=
    fun i => if i = β then conjEuclideanVector (σ := σ) (v : EuclideanSpace ℂ σ) else 0
  have hvnorm : ‖conjEuclideanVector (σ := σ) (v : EuclideanSpace ℂ σ)‖ = 1 := by
    have hv : ‖(v : EuclideanSpace ℂ σ)‖ = 1 := by
      rw [← dist_zero_right (a := (v : EuclideanSpace ℂ σ))]
      change (v : EuclideanSpace ℂ σ) ∈ Metric.sphere (0 : EuclideanSpace ℂ σ) 1
      exact v.property
    rw [conjEuclideanVector_norm]
    exact hv
  have hw_const :
      (Set.singleton β).restrict w =
        fun _ : Set.singleton β => conjEuclideanVector (σ := σ) (v : EuclideanSpace ℂ σ) := by
    funext i
    rcases i with ⟨i, hi⟩
    have hi' : i = β := by simpa using hi
    simp [w, hi']
  have hw : Orthonormal ℂ ((Set.singleton β).restrict w) := by
    rw [hw_const, orthonormal_iff_ite]
    intro i j
    by_cases hij : i = j
    · subst hij
      simp [hvnorm, inner_self_eq_norm_sq_to_K]
    · exfalso
      apply hij
      apply Subtype.ext
      rcases i with ⟨i, hi_mem⟩
      rcases j with ⟨j, hj_mem⟩
      have hi : i = β := by simpa using hi_mem
      have hj : j = β := by simpa using hj_mem
      simp [hi, hj]
  obtain ⟨b, hb⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (𝕜 := ℂ) (E := EuclideanSpace ℂ σ) (ι := σ)
      (card_ι := finrank_euclideanSpace (𝕜 := ℂ) (ι := σ))
      (v := w) (s := Set.singleton β) hw
  have hbβ' : b β = w β := hb β (by exact Set.mem_singleton β)
  have hwβ : w β = conjEuclideanVector (σ := σ) (v : EuclideanSpace ℂ σ) := by
    simp [w]
  have hbβ : b β = conjEuclideanVector (σ := σ) (v : EuclideanSpace ℂ σ) := by
    exact hbβ'.trans hwβ
  have hbconj : conjEuclideanVector (σ := σ) (b β) = (v : EuclideanSpace ℂ σ) := by
    rw [hbβ, conjEuclideanVector_involutive]
  let U :
      EuclideanSpace ℂ (SampleCoord p q σ) ≃ₗᵢ[ℂ]
        EuclideanSpace ℂ (SampleCoord p q σ) :=
    sampleCoordColumnLinearIsometryEquiv (p := p) (q := q) (σ := σ)
      (b.equiv (EuclideanSpace.basisFun σ ℂ) (Equiv.refl σ))
  have hfun :
      (fun ω : Ω p q σ =>
        (Matrix.toEuclideanLin (𝕜 := ℂ) (m := RandomMatrixModel.BipIndex p q)
          (n := σ) (gaussianMatrix p q σ ω)) (v : EuclideanSpace ℂ σ)) =
      (fun ω : Ω p q σ =>
        gaussianColumn p q σ β (complexUnitaryRealCoordinateIsometry U ω)) := by
    funext ω
    symm
    rw [gaussianColumn_sampleCoordColumnLinearIsometryEquiv
      (p := p) (q := q) (σ := σ) b β ω]
    rw [hbconj]
  rw [hfun]
  calc
    Measure.map
        (fun ω : Ω p q σ =>
          gaussianColumn p q σ β (complexUnitaryRealCoordinateIsometry U ω))
        (gaussianMeasure p q σ)
        = Measure.map (gaussianColumn p q σ β)
            (Measure.map (complexUnitaryRealCoordinateIsometry U)
              (gaussianMeasure p q σ)) := by
            rw [Measure.map_map]
            · rfl
            · exact (measurable_gaussianColumn (p := p) (q := q) (σ := σ) β)
            · exact (complexUnitaryRealCoordinateIsometry U).continuous.measurable
    _ = standardComplexGaussianVectorMeasure (RandomMatrixModel.BipIndex p q) := by
          rw [gaussianSampleMeasure_map_complexUnitaryRealCoordinateIsometry
            (p := p) (q := q) (σ := σ) U]
          exact gaussianColumn_map_gaussianMeasure (p := p) (q := q) (σ := σ) β

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Exact Laplace transform of the square of a real standard Gaussian, in the
range needed by the complex-coordinate MGF calculation. -/
theorem integral_exp_mul_sq_gaussianReal_zero_one {a : ℝ}
    (ha : a < (1 / 2 : ℝ)) :
    ∫ x : ℝ, Real.exp (a * x ^ 2) ∂(ProbabilityTheory.gaussianReal 0 1) =
      (Real.sqrt (1 - 2 * a))⁻¹ := by
  have hv : (1 : ℝ≥0) ≠ 0 := by norm_num
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul
    (μ := 0) (v := (1 : ℝ≥0))
    (f := fun x : ℝ => Real.exp (a * x ^ 2)) hv]
  unfold ProbabilityTheory.gaussianPDFReal
  simp only [NNReal.coe_one, sub_zero]
  simp_rw [smul_eq_mul]
  have hfun :
      (fun x : ℝ => (√(2 * Real.pi * 1))⁻¹ *
          Real.exp (-x ^ 2 / (2 * 1)) * Real.exp (a * x ^ 2)) =
        fun x : ℝ =>
          (√(2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 - a) * x ^ 2) := by
    funext x
    simp only [mul_one]
    calc
      (√(2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) * Real.exp (a * x ^ 2)
          = (√(2 * Real.pi))⁻¹ *
              (Real.exp (-x ^ 2 / 2) * Real.exp (a * x ^ 2)) := by
            ring_nf
      _ = (√(2 * Real.pi))⁻¹ *
            Real.exp (-(1 / 2 - a) * x ^ 2) := by
            rw [← Real.exp_add]
            congr 1
            ring_nf
  rw [hfun]
  rw [integral_const_mul]
  rw [integral_gaussian (1 / 2 - a)]
  have hA : 0 < 1 - 2 * a := by linarith
  have hB_eq : 1 / 2 - a = (1 - 2 * a) / 2 := by ring
  rw [hB_eq]
  have hsqrt_div :
      √(Real.pi / ((1 - 2 * a) / 2)) =
        √(2 * Real.pi / (1 - 2 * a)) := by
    congr 1
    field_simp [ne_of_gt hA]
  rw [hsqrt_div]
  have hmain :
      √(2 * Real.pi / (1 - 2 * a)) =
        √(2 * Real.pi) / √(1 - 2 * a) := by
    rw [Real.sqrt_div (by positivity : 0 ≤ 2 * Real.pi)]
  rw [hmain]
  have hsqrt_ne : √(2 * Real.pi) ≠ 0 := by positivity
  field_simp [hsqrt_ne]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Exact centered squared-modulus MGF for one standard complex Gaussian
coordinate, represented by two independent real `N(0,1)` coordinates scaled by
`1 / sqrt 2`.  The parameter is written as a single real number `b`; later one
specializes `b = θ * h`. -/
theorem complex_standard_normSq_mgf_real_coordinates {b : ℝ} (hb : b < 1) :
    ∫ x : Fin 2 → ℝ,
        Real.exp (b * (((x 0) ^ 2 + (x 1) ^ 2) / 2 - 1))
          ∂(Measure.pi (fun _ : Fin 2 => ProbabilityTheory.gaussianReal 0 1)) =
      Real.exp (-b) / (1 - b) := by
  have hbhalf : b / 2 < (1 / 2 : ℝ) := by linarith
  have hfactor :
      (fun x : Fin 2 → ℝ =>
          Real.exp (b * (((x 0) ^ 2 + (x 1) ^ 2) / 2 - 1))) =
        fun x =>
          Real.exp (-b) * ∏ k : Fin 2, Real.exp ((b / 2) * (x k) ^ 2) := by
    funext x
    simp [Fin.prod_univ_two]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring_nf
  rw [hfactor]
  rw [integral_const_mul]
  have hprod :
      ∫ a : Fin 2 → ℝ, ∏ k : Fin 2, Real.exp ((b / 2) * a k ^ 2)
          ∂(Measure.pi (fun _ : Fin 2 => ProbabilityTheory.gaussianReal 0 1)) =
        ∏ k : Fin 2, ∫ x : ℝ, Real.exp ((b / 2) * x ^ 2)
          ∂ProbabilityTheory.gaussianReal 0 1 := by
    exact integral_fintype_prod_eq_prod (ι := Fin 2) (E := fun _ => ℝ)
      (μ := fun _ : Fin 2 => ProbabilityTheory.gaussianReal 0 1)
      (fun _ x => Real.exp ((b / 2) * x ^ 2))
  rw [hprod]
  have hone (k : Fin 2) :
      ∫ x : ℝ, Real.exp ((b / 2) * x ^ 2)
          ∂ProbabilityTheory.gaussianReal 0 1 =
        (Real.sqrt (1 - b))⁻¹ := by
    simpa [show 1 - 2 * (b / 2) = 1 - b by ring] using
      integral_exp_mul_sq_gaussianReal_zero_one (a := b / 2) hbhalf
  have hprodval :
      (∏ k : Fin 2, ∫ x : ℝ, Real.exp ((b / 2) * x ^ 2)
          ∂ProbabilityTheory.gaussianReal 0 1) =
        ((Real.sqrt (1 - b))⁻¹) ^ 2 := by
    simp
    rw [hone 0]
    ring
  rw [hprodval]
  have hpos : 0 < 1 - b := by linarith
  have hsqrt_sq : (√(1 - b)) ^ 2 = 1 - b := by
    rw [Real.sq_sqrt hpos.le]
  have hsqrt_ne : √(1 - b) ≠ 0 := by positivity
  field_simp [hsqrt_ne]
  rw [hsqrt_sq]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Product MGF factorization for independent standard complex Gaussian
coordinates, written as real/imaginary coordinate blocks. -/
theorem complex_standard_diagonal_mgf_real_coordinate_blocks
    {ι : Type*} [Fintype ι]
    (θ : ℝ) (h : ι → ℝ) (hlt : ∀ i : ι, θ * h i < 1) :
    ∫ x : ι → Fin 2 → ℝ,
        Real.exp (θ * ∑ i : ι, h i * (((x i 0) ^ 2 + (x i 1) ^ 2) / 2 - 1))
          ∂(Measure.pi (fun _ : ι =>
            Measure.pi (fun _ : Fin 2 => ProbabilityTheory.gaussianReal 0 1))) =
      ∏ i : ι, Real.exp (-(θ * h i)) / (1 - θ * h i) := by
  have hfactor :
      (fun x : ι → Fin 2 → ℝ =>
        Real.exp (θ * ∑ i : ι, h i * (((x i 0) ^ 2 + (x i 1) ^ 2) / 2 - 1))) =
      fun x => ∏ i : ι,
        Real.exp ((θ * h i) * (((x i 0) ^ 2 + (x i 1) ^ 2) / 2 - 1)) := by
    funext x
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hfactor]
  rw [integral_fintype_prod_eq_prod
    (ι := ι)
    (E := fun _ => Fin 2 → ℝ)
    (μ := fun _ : ι =>
      Measure.pi (fun _ : Fin 2 => ProbabilityTheory.gaussianReal 0 1))
    (f := fun i xi =>
      Real.exp ((θ * h i) * (((xi 0) ^ 2 + (xi 1) ^ 2) / 2 - 1)))]
  apply Finset.prod_congr rfl
  intro i _
  exact complex_standard_normSq_mgf_real_coordinates (b := θ * h i) (hlt i)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Product MGF factorization over raw real coordinates indexed by
`ι × Fin 2`. -/
theorem complex_standard_diagonal_mgf_raw_real_coordinates
    {ι : Type*} [Fintype ι]
    (θ : ℝ) (h : ι → ℝ) (hlt : ∀ i : ι, θ * h i < 1) :
    ∫ x : ι × Fin 2 → ℝ,
        Real.exp (θ * ∑ i : ι, h i * (((x (i, 0)) ^ 2 + (x (i, 1)) ^ 2) / 2 - 1))
          ∂(Measure.pi (fun _ : ι × Fin 2 => ProbabilityTheory.gaussianReal 0 1)) =
      ∏ i : ι, Real.exp (-(θ * h i)) / (1 - θ * h i) := by
  let μraw : Measure ((ι × Fin 2) → ℝ) :=
    Measure.pi (fun _ : ι × Fin 2 => ProbabilityTheory.gaussianReal 0 1)
  have hcurry :
      Measure.map (MeasurableEquiv.curry ι (Fin 2) ℝ) μraw =
        Measure.pi (fun _ : ι =>
          Measure.pi (fun _ : Fin 2 => ProbabilityTheory.gaussianReal 0 1)) := by
    simpa [μraw, Measure.infinitePi_eq_pi] using
      (Measure.infinitePi_map_curry
        (μ := fun _ : ι =>
          fun _ : Fin 2 => ProbabilityTheory.gaussianReal 0 1)
        (X := ℝ))
  have hblock := complex_standard_diagonal_mgf_real_coordinate_blocks θ h hlt
  rw [← hcurry] at hblock
  rw [integral_map] at hblock
  · simpa [μraw] using hblock
  · exact (MeasurableEquiv.curry ι (Fin 2) ℝ).measurable.aemeasurable
  · fun_prop

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Squared norm of one concrete standard-complex-Gaussian coordinate in
terms of its two underlying real coordinates. -/
theorem norm_sq_complexVectorOfRealCoordinates_apply
    {ι : Type*} [Fintype ι]
    (x : ComplexRealCoordSpace ι) (i : ι) :
    ‖complexVectorOfRealCoordinates (ι := ι) x i‖ ^ 2 =
      ((x (i, 0)) ^ 2 + (x (i, 1)) ^ 2) / 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [GaussianModel.complexGaussianScale, Complex.normSq_apply]
  have hs : (√2) ^ 2 = (2 : ℝ) := by
    rw [Real.sq_sqrt (by norm_num)]
  field_simp [show (√2 : ℝ) ≠ 0 by positivity]
  ring_nf
  rw [hs]
  ring

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Product MGF factorization over standard complex Gaussian eigen-coordinates. -/
theorem complex_standard_diagonal_mgf_factorization
    {ι : Type*} [Fintype ι]
    (θ : ℝ) (h : ι → ℝ) (hlt : ∀ i : ι, θ * h i < 1) :
    ∫ z : EuclideanSpace ℂ ι,
        Real.exp (θ * ∑ i : ι, h i * (‖z i‖ ^ 2 - 1))
          ∂(standardComplexGaussianVectorMeasure ι) =
      ∏ i : ι, Real.exp (-(θ * h i)) / (1 - θ * h i) := by
  unfold standardComplexGaussianVectorMeasure
  rw [integral_map]
  rw [← ProbabilityTheory.map_pi_eq_stdGaussian (ι := ι × Fin 2)]
  rw [integral_map]
  · have hfun :
        (fun x : (ι × Fin 2) → ℝ =>
          Real.exp
            (θ * ∑ i : ι,
              h i * (‖complexVectorOfRealCoordinates (ι := ι) (WithLp.toLp 2 x) i‖ ^ 2 - 1))) =
        fun x : (ι × Fin 2) → ℝ =>
          Real.exp (θ * ∑ i : ι,
            h i * (((x (i, 0)) ^ 2 + (x (i, 1)) ^ 2) / 2 - 1)) := by
        funext x
        apply congrArg Real.exp
        apply congrArg (fun s : ℝ => θ * s)
        apply Finset.sum_congr rfl
        intro i _
        have hnorm := norm_sq_complexVectorOfRealCoordinates_apply
          (WithLp.toLp 2 x : ComplexRealCoordSpace ι) i
        simpa using congrArg (fun t : ℝ => h i * (t - 1)) hnorm
    rw [hfun]
    exact complex_standard_diagonal_mgf_raw_real_coordinates θ h hlt
  · fun_prop
  · fun_prop
  · exact (measurable_complexVectorOfRealCoordinates ι).aemeasurable
  · fun_prop

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Exact MGF factorization for the centered squared norm of a standard
complex Gaussian vector. -/
theorem standardComplexGaussianVectorMeasure_norm_sq_centered_mgf_factorization
    {ι : Type*} [Fintype ι]
    {θ : ℝ} (hθ : θ < 1) :
    ∫ z : EuclideanSpace ℂ ι,
        Real.exp (θ * (‖z‖ ^ 2 - Fintype.card ι))
          ∂(standardComplexGaussianVectorMeasure ι) =
      ∏ _i : ι, Real.exp (-θ) / (1 - θ) := by
  have hmgf :=
    complex_standard_diagonal_mgf_factorization
      (ι := ι) θ (fun _ : ι => (1 : ℝ)) (by intro _; simpa using hθ)
  have hfun :
      (fun z : EuclideanSpace ℂ ι =>
          Real.exp (θ * (‖z‖ ^ 2 - Fintype.card ι))) =
        fun z : EuclideanSpace ℂ ι =>
          Real.exp (θ * ∑ i : ι, (1 : ℝ) * (‖z i‖ ^ 2 - 1)) := by
    funext z
    rw [EuclideanSpace.norm_sq_eq]
    congr 1
    congr 1
    have hcard : (Fintype.card ι : ℝ) = ∑ _i : ι, (1 : ℝ) := by simp
    rw [hcard, ← Finset.sum_sub_distrib]
    simp
  rw [hfun]
  simpa using hmgf

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Exponential integrability of the centered squared norm of a standard
complex Gaussian vector, in the subcritical Laplace range. -/
theorem standardComplexGaussianVectorMeasure_norm_sq_centered_integrable_exp_mul
    {ι : Type*} [Fintype ι]
    {θ : ℝ} (hθ : θ < 1) :
    Integrable
      (fun z : EuclideanSpace ℂ ι =>
        Real.exp (θ * (‖z‖ ^ 2 - Fintype.card ι)))
      (standardComplexGaussianVectorMeasure ι) := by
  have hEq :=
    standardComplexGaussianVectorMeasure_norm_sq_centered_mgf_factorization
      (ι := ι) (θ := θ) hθ
  by_contra hnot
  rw [integral_undef hnot] at hEq
  have hpos :
      0 < ∏ _i : ι, Real.exp (-θ) / (1 - θ) := by
    refine Finset.prod_pos ?_
    intro i hi
    have hden : 0 < 1 - θ := by linarith
    exact div_pos (Real.exp_pos _) hden
  linarith

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Chernoff upper tail for the squared norm of a standard complex Gaussian
vector.  This form is tuned for later net union bounds: the threshold `R` is
left free. -/
theorem standardComplexGaussianVectorMeasure_norm_sq_upper_tail
    {ι : Type*} [Fintype ι] (R : ℝ) :
    (standardComplexGaussianVectorMeasure ι).real
        {z : EuclideanSpace ℂ ι | R ≤ ‖z‖ ^ 2} ≤
      Real.exp (-(1 / 2 : ℝ) * R + Real.log 2 * Fintype.card ι) := by
  let D : ℝ := Fintype.card ι
  let X : EuclideanSpace ℂ ι → ℝ := fun z => ‖z‖ ^ 2 - D
  haveI : IsProbabilityMeasure (standardComplexGaussianVectorMeasure ι) := by
    infer_instance
  have hθ_nonneg : 0 ≤ (1 / 2 : ℝ) := by positivity
  have hInt :
      Integrable (fun z : EuclideanSpace ℂ ι => Real.exp ((1 / 2 : ℝ) * X z))
        (standardComplexGaussianVectorMeasure ι) := by
    simpa [X, D] using
      standardComplexGaussianVectorMeasure_norm_sq_centered_integrable_exp_mul
        (ι := ι) (θ := (1 / 2 : ℝ)) (by norm_num)
  have hchern :=
    ProbabilityTheory.measure_ge_le_exp_mul_mgf
      (μ := standardComplexGaussianVectorMeasure ι)
      (X := X) (ε := R - D) hθ_nonneg hInt
  have hmgf :
      ProbabilityTheory.mgf X (standardComplexGaussianVectorMeasure ι) (1 / 2 : ℝ) =
        ∏ _i : ι, Real.exp (-(1 / 2 : ℝ)) / (1 - (1 / 2 : ℝ)) := by
    rw [ProbabilityTheory.mgf]
    simpa [X, D] using
      standardComplexGaussianVectorMeasure_norm_sq_centered_mgf_factorization
        (ι := ι) (θ := (1 / 2 : ℝ)) (by norm_num)
  have hprod :
      (∏ _i : ι, Real.exp (-(1 / 2 : ℝ)) / (1 - (1 / 2 : ℝ))) =
        Real.exp ((Real.log 2 - 1 / 2) * D) := by
    have hfac :
        Real.exp (-(1 / 2 : ℝ)) / (1 - (1 / 2 : ℝ)) =
          Real.exp (Real.log 2 - 1 / 2) := by
      have hhalf : (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by ring
      rw [hhalf]
      calc
        Real.exp (-(1 / 2 : ℝ)) / (1 / 2 : ℝ)
            = Real.exp (-(1 / 2 : ℝ)) * 2 := by
              norm_num [div_eq_mul_inv]
        _ = Real.exp (-(1 / 2 : ℝ)) * Real.exp (Real.log 2) := by
              rw [Real.exp_log (by positivity : (0 : ℝ) < 2)]
        _ = Real.exp (Real.log 2 - 1 / 2) := by
              rw [← Real.exp_add]
              congr 1
              ring
    rw [hfac]
    calc
      (∏ _i : ι, Real.exp (Real.log 2 - 1 / 2)) =
          Real.exp (∑ _i : ι, (Real.log 2 - 1 / 2)) := by
            rw [Real.exp_sum]
      _ = Real.exp ((Real.log 2 - 1 / 2) * D) := by
            congr 1
            simp [D, Finset.sum_const, nsmul_eq_mul]
            ring
  have hset :
      {z : EuclideanSpace ℂ ι | R ≤ ‖z‖ ^ 2} =
        {z : EuclideanSpace ℂ ι | R - D ≤ X z} := by
    ext z
    dsimp [X]
    constructor <;> intro hz <;> linarith
  calc
    (standardComplexGaussianVectorMeasure ι).real
        {z : EuclideanSpace ℂ ι | R ≤ ‖z‖ ^ 2}
        = (standardComplexGaussianVectorMeasure ι).real
            {z : EuclideanSpace ℂ ι | R - D ≤ X z} := by rw [hset]
    _ ≤ Real.exp (-(1 / 2 : ℝ) * (R - D)) *
          ProbabilityTheory.mgf X (standardComplexGaussianVectorMeasure ι)
            (1 / 2 : ℝ) := hchern
    _ = Real.exp (-(1 / 2 : ℝ) * (R - D)) *
          (∏ _i : ι, Real.exp (-(1 / 2 : ℝ)) / (1 - (1 / 2 : ℝ))) := by
            rw [hmgf]
    _ = Real.exp (-(1 / 2 : ℝ) * R + Real.log 2 * D) := by
          rw [hprod, ← Real.exp_add]
          congr 1
          ring

omit [DecidableEq p] [DecidableEq q] in
/-- Fixed unit-vector tail for the rectangular Gaussian image `Gv`, obtained
by transporting the standard complex Gaussian norm tail through the `Gv` law. -/
theorem gaussianMatrix_unitVector_mul_norm_sq_upper_tail
    [Nonempty σ] [DecidableEq σ]
    (v : Metric.sphere (0 : EuclideanSpace ℂ σ) 1) (R : ℝ) :
    (gaussianMeasure p q σ).real
        {ω : Ω p q σ |
          R ≤ ‖(Matrix.toEuclideanLin (𝕜 := ℂ) (m := RandomMatrixModel.BipIndex p q)
            (n := σ) (gaussianMatrix p q σ ω)) (v : EuclideanSpace ℂ σ)‖ ^ 2} ≤
      Real.exp (-(1 / 2 : ℝ) * R + Real.log 2 * bipartiteDimension p q) := by
  classical
  let f : Ω p q σ → EuclideanSpace ℂ (RandomMatrixModel.BipIndex p q) :=
    fun ω =>
      (Matrix.toEuclideanLin (𝕜 := ℂ) (m := RandomMatrixModel.BipIndex p q)
        (n := σ) (gaussianMatrix p q σ ω)) (v : EuclideanSpace ℂ σ)
  let S : Set (EuclideanSpace ℂ (RandomMatrixModel.BipIndex p q)) :=
    {z | R ≤ ‖z‖ ^ 2}
  have hmap :
      Measure.map f (gaussianMeasure p q σ) =
        standardComplexGaussianVectorMeasure (RandomMatrixModel.BipIndex p q) := by
    simpa [f] using
      gaussianMatrix_unitVector_mul_map_gaussianMeasure
        (p := p) (q := q) (σ := σ) v
  have hf : Measurable f := by
    have hfeq :
        f =
          fun ω : Ω p q σ =>
            ∑ α : σ, (v : EuclideanSpace ℂ σ) α •
              gaussianColumn p q σ α ω := by
      funext ω
      simpa [f] using
        gaussianMatrix_mulVec_eq_sum_smul_gaussianColumn
          (p := p) (q := q) (σ := σ)
          (v := (v : EuclideanSpace ℂ σ)) ω
    rw [hfeq]
    fun_prop
  have hS : MeasurableSet S := by
    unfold S
    exact measurableSet_le measurable_const (by fun_prop)
  have hreal :
      (gaussianMeasure p q σ).real
          {ω : Ω p q σ |
            R ≤ ‖(Matrix.toEuclideanLin (𝕜 := ℂ) (m := RandomMatrixModel.BipIndex p q)
              (n := σ) (gaussianMatrix p q σ ω)) (v : EuclideanSpace ℂ σ)‖ ^ 2} =
        (Measure.map f (gaussianMeasure p q σ)).real S := by
    change ((gaussianMeasure p q σ) (f ⁻¹' S)).toReal =
      ((Measure.map f (gaussianMeasure p q σ)) S).toReal
    rw [Measure.map_apply hf hS]
  calc
    (gaussianMeasure p q σ).real
        {ω : Ω p q σ |
          R ≤ ‖(Matrix.toEuclideanLin (𝕜 := ℂ) (m := RandomMatrixModel.BipIndex p q)
            (n := σ) (gaussianMatrix p q σ ω)) (v : EuclideanSpace ℂ σ)‖ ^ 2}
        = (Measure.map f (gaussianMeasure p q σ)).real S := hreal
    _ = (standardComplexGaussianVectorMeasure (RandomMatrixModel.BipIndex p q)).real S := by
          rw [hmap]
    _ ≤ Real.exp (-(1 / 2 : ℝ) * R + Real.log 2 * bipartiteDimension p q) := by
          simpa [S, bipartiteDimension] using
            standardComplexGaussianVectorMeasure_norm_sq_upper_tail
              (ι := RandomMatrixModel.BipIndex p q) R

omit [DecidableEq p] [DecidableEq q] in
/-- Fixed unit-vector upper tail for the norm `‖Gv‖`. -/
theorem gaussianMatrix_unitVector_mul_norm_upper_tail
    [Nonempty σ] [DecidableEq σ]
    (v : Metric.sphere (0 : EuclideanSpace ℂ σ) 1) {r : ℝ} (hr : 0 ≤ r) :
    (gaussianMeasure p q σ).real
        {ω : Ω p q σ |
          r ≤ ‖(Matrix.toEuclideanLin (𝕜 := ℂ) (m := RandomMatrixModel.BipIndex p q)
            (n := σ) (gaussianMatrix p q σ ω)) (v : EuclideanSpace ℂ σ)‖} ≤
      Real.exp (-(1 / 2 : ℝ) * r ^ 2 + Real.log 2 * bipartiteDimension p q) := by
  let f : Ω p q σ → EuclideanSpace ℂ (RandomMatrixModel.BipIndex p q) :=
    fun ω =>
      (Matrix.toEuclideanLin (𝕜 := ℂ) (m := RandomMatrixModel.BipIndex p q)
        (n := σ) (gaussianMatrix p q σ ω)) (v : EuclideanSpace ℂ σ)
  haveI : IsProbabilityMeasure (gaussianMeasure p q σ) := by
    rw [gaussianMeasure_eq]
    infer_instance
  have hsubset :
      {ω : Ω p q σ | r ≤ ‖f ω‖} ⊆
        {ω : Ω p q σ | r ^ 2 ≤ ‖f ω‖ ^ 2} := by
    intro ω hω
    dsimp at hω ⊢
    nlinarith [hr, norm_nonneg (f ω), hω]
  calc
    (gaussianMeasure p q σ).real
        {ω : Ω p q σ |
          r ≤ ‖(Matrix.toEuclideanLin (𝕜 := ℂ) (m := RandomMatrixModel.BipIndex p q)
            (n := σ) (gaussianMatrix p q σ ω)) (v : EuclideanSpace ℂ σ)‖}
        ≤ (gaussianMeasure p q σ).real
            {ω : Ω p q σ |
              r ^ 2 ≤ ‖(Matrix.toEuclideanLin (𝕜 := ℂ)
                (m := RandomMatrixModel.BipIndex p q)
                (n := σ) (gaussianMatrix p q σ ω)) (v : EuclideanSpace ℂ σ)‖ ^ 2} := by
            exact measureReal_mono
              (h₂ := (measure_lt_top (gaussianMeasure p q σ) _).ne)
              (by simpa [f] using hsubset)
    _ ≤ Real.exp (-(1 / 2 : ℝ) * r ^ 2 + Real.log 2 * bipartiteDimension p q) := by
          exact gaussianMatrix_unitVector_mul_norm_sq_upper_tail
            (p := p) (q := q) (σ := σ) v (r ^ 2)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Product MGF factorization in the bounded-parameter range used for
eigenvalues satisfying `|h_i| ≤ 1`. -/
theorem complex_standard_diagonal_mgf_factorization_mul
    {ι : Type*} [Fintype ι]
    {θ : ℝ} (h : ι → ℝ)
    (hθ : |θ| ≤ (1 / 2 : ℝ)) (hh : ∀ i : ι, |h i| ≤ 1) :
    ∫ z : EuclideanSpace ℂ ι,
        Real.exp (θ * ∑ i : ι, h i * (‖z i‖ ^ 2 - 1))
          ∂(standardComplexGaussianVectorMeasure ι) =
      ∏ i : ι, Real.exp (-(θ * h i)) / (1 - θ * h i) := by
  refine complex_standard_diagonal_mgf_factorization θ h ?_
  intro i
  have habs : |θ * h i| ≤ (1 / 2 : ℝ) := by
    rw [abs_mul]
    nlinarith [abs_nonneg θ, abs_nonneg (h i), hh i]
  have hle_abs : θ * h i ≤ |θ * h i| := le_abs_self _
  nlinarith

omit [Fintype σ] in
/-- Product MGF factorization for the eigen-coordinates of the diagonalized
`H_u = (|u⟩⟨u|)^Γ`. -/
theorem rankOneProjectorGamma_eigen_coordinate_mgf_factorization
    (u : Metric.sphere (0 : BipVector p q) 1)
    {θ : ℝ} (hθ : |θ| ≤ (1 / 2 : ℝ)) :
    ∫ z : EuclideanSpace ℂ (RandomMatrixModel.BipIndex p q),
        Real.exp
          (θ *
            ∑ i : RandomMatrixModel.BipIndex p q,
              rankOneProjectorGammaEigenvalues (p := p) (q := q) (u : BipVector p q) i *
                (‖z i‖ ^ 2 - 1))
          ∂(standardComplexGaussianVectorMeasure (RandomMatrixModel.BipIndex p q)) =
      ∏ i : RandomMatrixModel.BipIndex p q,
        Real.exp
            (-(θ *
              rankOneProjectorGammaEigenvalues (p := p) (q := q) (u : BipVector p q) i)) /
          (1 - θ *
            rankOneProjectorGammaEigenvalues (p := p) (q := q) (u : BipVector p q) i) := by
  exact complex_standard_diagonal_mgf_factorization_mul
    (h := rankOneProjectorGammaEigenvalues (p := p) (q := q) (u : BipVector p q))
    hθ
    (rankOneProjectorGamma_eigenvalues_abs_le_one (p := p) (q := q) u)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Measurability of the column-product diagonal MGF integrand. -/
theorem measurable_complex_standard_diagonal_column_mgf_integrand
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (θ : ℝ) (h : ι → ℝ) :
    Measurable (fun Z : κ → EuclideanSpace ℂ ι =>
      Real.exp (θ * ∑ α : κ, ∑ i : ι, h i * (‖Z α i‖ ^ 2 - 1))) := by
  fun_prop

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Product MGF factorization over independent standard complex Gaussian
columns. -/
theorem complex_standard_diagonal_mgf_independent_columns
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (θ : ℝ) (h : ι → ℝ) (hlt : ∀ i : ι, θ * h i < 1) :
    ∫ Z : κ → EuclideanSpace ℂ ι,
        Real.exp (θ * ∑ α : κ, ∑ i : ι, h i * (‖Z α i‖ ^ 2 - 1))
          ∂(Measure.pi (fun _ : κ => standardComplexGaussianVectorMeasure ι)) =
      ∏ _α : κ, ∏ i : ι, Real.exp (-(θ * h i)) / (1 - θ * h i) := by
  have hfactor :
      (fun Z : κ → EuclideanSpace ℂ ι =>
        Real.exp (θ * ∑ α : κ, ∑ i : ι, h i * (‖Z α i‖ ^ 2 - 1))) =
      fun Z => ∏ α : κ,
        Real.exp (θ * ∑ i : ι, h i * (‖Z α i‖ ^ 2 - 1)) := by
    funext Z
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum]
  rw [hfactor]
  rw [integral_fintype_prod_eq_prod
    (ι := κ)
    (E := fun _ => EuclideanSpace ℂ ι)
    (μ := fun _ : κ => standardComplexGaussianVectorMeasure ι)
    (f := fun _α z =>
      Real.exp (θ * ∑ i : ι, h i * (‖z i‖ ^ 2 - 1)))]
  apply Finset.prod_congr rfl
  intro _α _
  exact complex_standard_diagonal_mgf_factorization θ h hlt

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Product MGF factorization over independent standard complex Gaussian
columns in the bounded-parameter range `|θ| ≤ 1/2`, `|h_i| ≤ 1`. -/
theorem complex_standard_diagonal_mgf_independent_columns_mul
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    {θ : ℝ} (h : ι → ℝ)
    (hθ : |θ| ≤ (1 / 2 : ℝ)) (hh : ∀ i : ι, |h i| ≤ 1) :
    ∫ Z : κ → EuclideanSpace ℂ ι,
        Real.exp (θ * ∑ α : κ, ∑ i : ι, h i * (‖Z α i‖ ^ 2 - 1))
          ∂(Measure.pi (fun _ : κ => standardComplexGaussianVectorMeasure ι)) =
      ∏ _α : κ, ∏ i : ι, Real.exp (-(θ * h i)) / (1 - θ * h i) := by
  refine complex_standard_diagonal_mgf_independent_columns θ h ?_
  intro i
  have habs : |θ * h i| ≤ (1 / 2 : ℝ) := by
    rw [abs_mul]
    nlinarith [abs_nonneg θ, abs_nonneg (h i), hh i]
  have hle_abs : θ * h i ≤ |θ * h i| := le_abs_self _
  nlinarith

/-- Pullback of the independent-column product MGF factorization to the
concrete Gaussian sample space after applying a fixed matrix-unitary coordinate
change to every column. -/
theorem gaussianColumn_matrixUnitary_diagonal_mgf_independent_columns
    (U : unitary (BipMatrix p q))
    (θ : ℝ) (h : RandomMatrixModel.BipIndex p q → ℝ)
    (hlt : ∀ i : RandomMatrixModel.BipIndex p q, θ * h i < 1) :
    ∫ ω : Ω p q σ,
        Real.exp (θ * ∑ α : σ, ∑ i : RandomMatrixModel.BipIndex p q,
          h i * (‖matrixUnitaryLinearIsometryEquiv U
            (gaussianColumn p q σ α ω) i‖ ^ 2 - 1))
          ∂(gaussianMeasure p q σ) =
      ∏ _α : σ, ∏ i : RandomMatrixModel.BipIndex p q,
        Real.exp (-(θ * h i)) / (1 - θ * h i) := by
  have hprod :=
    complex_standard_diagonal_mgf_independent_columns
      (κ := σ) (ι := RandomMatrixModel.BipIndex p q) θ h hlt
  have hjoint :=
    gaussianColumn_matrixUnitary_joint_map_gaussianMeasure (p := p) (q := q) (σ := σ) U
  rw [← hjoint] at hprod
  rw [integral_map] at hprod
  · simpa using hprod
  · exact (measurable_pi_lambda _ fun α =>
      ((matrixUnitaryLinearIsometryEquiv U).continuous.measurable).comp
        (measurable_gaussianColumn (p := p) (q := q) (σ := σ) α)).aemeasurable
  · exact
      (measurable_complex_standard_diagonal_column_mgf_integrand
        (κ := σ) (ι := RandomMatrixModel.BipIndex p q) θ h).aestronglyMeasurable

/-- Concrete independent-column MGF factorization in the bounded-parameter
range `|θ| ≤ 1/2`, `|h_i| ≤ 1`. -/
theorem gaussianColumn_matrixUnitary_diagonal_mgf_independent_columns_mul
    (U : unitary (BipMatrix p q))
    {θ : ℝ} (h : RandomMatrixModel.BipIndex p q → ℝ)
    (hθ : |θ| ≤ (1 / 2 : ℝ))
    (hh : ∀ i : RandomMatrixModel.BipIndex p q, |h i| ≤ 1) :
    ∫ ω : Ω p q σ,
        Real.exp (θ * ∑ α : σ, ∑ i : RandomMatrixModel.BipIndex p q,
          h i * (‖matrixUnitaryLinearIsometryEquiv U
            (gaussianColumn p q σ α ω) i‖ ^ 2 - 1))
          ∂(gaussianMeasure p q σ) =
      ∏ _α : σ, ∏ i : RandomMatrixModel.BipIndex p q,
        Real.exp (-(θ * h i)) / (1 - θ * h i) := by
  refine gaussianColumn_matrixUnitary_diagonal_mgf_independent_columns
    (p := p) (q := q) (σ := σ) U θ h ?_
  intro i
  have habs : |θ * h i| ≤ (1 / 2 : ℝ) := by
    rw [abs_mul]
    nlinarith [abs_nonneg θ, abs_nonneg (h i), hh i]
  have hle_abs : θ * h i ≤ |θ * h i| := le_abs_self _
  nlinarith

/-- Product MGF factorization over sample columns and diagonal coordinates for
the Gaussian columns rotated by the adjoint eigenvector unitary of
`H_u = (|u⟩⟨u|)^Γ`. -/
theorem gaussianColumn_rankOneProjectorGamma_star_eigenvectorUnitary_diagonal_mgf_independent_columns
    (u : BipVector p q)
    (θ : ℝ) (h : RandomMatrixModel.BipIndex p q → ℝ)
    (hlt : ∀ i : RandomMatrixModel.BipIndex p q, θ * h i < 1) :
    ∫ ω : Ω p q σ,
        Real.exp (θ * ∑ α : σ, ∑ i : RandomMatrixModel.BipIndex p q,
          h i * (‖matrixUnitaryLinearIsometryEquiv
            (star
              (rankOneProjectorGamma_isHermitian
                (p := p) (q := q) u).eigenvectorUnitary)
            (gaussianColumn p q σ α ω) i‖ ^ 2 - 1))
          ∂(gaussianMeasure p q σ) =
      ∏ _α : σ, ∏ i : RandomMatrixModel.BipIndex p q,
        Real.exp (-(θ * h i)) / (1 - θ * h i) := by
  have hprod :=
    complex_standard_diagonal_mgf_independent_columns
      (κ := σ) (ι := RandomMatrixModel.BipIndex p q) θ h hlt
  have hjoint :=
    gaussianColumn_rankOneProjectorGamma_star_eigenvectorUnitary_joint_map_gaussianMeasure
      (p := p) (q := q) (σ := σ) u
  rw [← hjoint] at hprod
  rw [integral_map] at hprod
  · simpa using hprod
  · exact (measurable_pi_lambda _ fun α =>
      ((matrixUnitaryLinearIsometryEquiv
        (star
          (rankOneProjectorGamma_isHermitian
            (p := p) (q := q) u).eigenvectorUnitary)).continuous.measurable).comp
          (measurable_gaussianColumn (p := p) (q := q) (σ := σ) α)).aemeasurable
  · exact
      (measurable_complex_standard_diagonal_column_mgf_integrand
        (κ := σ) (ι := RandomMatrixModel.BipIndex p q) θ h).aestronglyMeasurable

/-- Independent-column product MGF factorization for the eigen-coordinates of
the diagonalized `H_u = (|u⟩⟨u|)^Γ`.  The unitary used here is `Uᴴ`, matching
the coordinate change from `U D Uᴴ` back to the diagonal matrix `D`. -/
theorem rankOneProjectorGamma_eigen_column_mgf_factorization
    (u : Metric.sphere (0 : BipVector p q) 1)
    {θ : ℝ} (hθ : |θ| ≤ (1 / 2 : ℝ)) :
    ∫ ω : Ω p q σ,
        Real.exp
          (θ * ∑ α : σ, ∑ i : RandomMatrixModel.BipIndex p q,
            rankOneProjectorGammaEigenvalues (p := p) (q := q) (u : BipVector p q) i *
              (‖matrixUnitaryLinearIsometryEquiv
                  (star
                    (rankOneProjectorGamma_isHermitian
                      (p := p) (q := q) (u : BipVector p q)).eigenvectorUnitary)
                  (gaussianColumn p q σ α ω) i‖ ^ 2 - 1))
          ∂(gaussianMeasure p q σ) =
      ∏ _α : σ, ∏ i : RandomMatrixModel.BipIndex p q,
        Real.exp
            (-(θ *
              rankOneProjectorGammaEigenvalues (p := p) (q := q) (u : BipVector p q) i)) /
          (1 - θ *
            rankOneProjectorGammaEigenvalues (p := p) (q := q) (u : BipVector p q) i) := by
  exact gaussianColumn_rankOneProjectorGamma_star_eigenvectorUnitary_diagonal_mgf_independent_columns
    (p := p) (q := q) (σ := σ)
    (u := (u : BipVector p q))
    θ
    (h := rankOneProjectorGammaEigenvalues (p := p) (q := q) (u : BipVector p q))
    (fun i => by
      have habs : |θ *
          rankOneProjectorGammaEigenvalues (p := p) (q := q) (u : BipVector p q) i|
            ≤ (1 / 2 : ℝ) := by
        rw [abs_mul]
        nlinarith [abs_nonneg θ, abs_nonneg
          (rankOneProjectorGammaEigenvalues (p := p) (q := q) (u : BipVector p q) i),
          rankOneProjectorGamma_eigenvalues_abs_le_one (p := p) (q := q) u i, hθ]
      have hle_abs :
          θ * rankOneProjectorGammaEigenvalues (p := p) (q := q) (u : BipVector p q) i ≤
            |θ * rankOneProjectorGammaEigenvalues (p := p) (q := q) (u : BipVector p q) i| :=
        le_abs_self _
      nlinarith)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Scalar logarithmic estimate used to bound each centered complex-chi-square
MGF factor. -/
theorem neg_self_sub_log_one_sub_le_two_mul_sq {x : ℝ}
    (hx : |x| ≤ (1 / 2 : ℝ)) :
    -x - Real.log (1 - x) ≤ 2 * x ^ 2 := by
  have hx_le_half : x ≤ (1 / 2 : ℝ) := le_trans (le_abs_self x) hx
  have hx_lt_one : x < 1 := by linarith
  have hpos : 0 < 1 - x := by linarith
  have hhalf : (1 / 2 : ℝ) ≤ 1 - x := by linarith
  have hlog := Real.log_le_sub_one_of_pos (show 0 < (1 - x)⁻¹ by positivity)
  rw [Real.log_inv] at hlog
  have hneglog : -Real.log (1 - x) ≤ (1 - x)⁻¹ - 1 := hlog
  have hmain : -x - Real.log (1 - x) ≤ x ^ 2 / (1 - x) := by
    calc
      -x - Real.log (1 - x) ≤ -x + ((1 - x)⁻¹ - 1) := by linarith
      _ = x ^ 2 / (1 - x) := by
        field_simp [ne_of_gt hpos]
        ring_nf
  have hdiv : x ^ 2 / (1 - x) ≤ 2 * x ^ 2 := by
    rw [div_le_iff₀ hpos]
    nlinarith [sq_nonneg x, hhalf]
  exact le_trans hmain hdiv

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Exponential form of the scalar coordinate MGF factor bound. -/
theorem exp_neg_div_one_sub_le_exp_two_mul_sq {x : ℝ}
    (hx : |x| ≤ (1 / 2 : ℝ)) :
    Real.exp (-x) / (1 - x) ≤ Real.exp (2 * x ^ 2) := by
  have hx_le_half : x ≤ (1 / 2 : ℝ) := le_trans (le_abs_self x) hx
  have hpos : 0 < 1 - x := by linarith
  have hrewrite :
      Real.exp (-x) / (1 - x) = Real.exp (-x - Real.log (1 - x)) := by
    rw [Real.exp_sub, Real.exp_log hpos]
  rw [hrewrite]
  exact Real.exp_le_exp.mpr (neg_self_sub_log_one_sub_le_two_mul_sq hx)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Nonnegativity of one scalar MGF factor in the bounded-parameter range. -/
theorem diagonal_mgf_coordinate_factor_nonneg
    {θ h : ℝ} (hθ : |θ| ≤ (1 / 2 : ℝ)) (hh : |h| ≤ 1) :
    0 ≤ Real.exp (-(θ * h)) / (1 - θ * h) := by
  have habs : |θ * h| ≤ (1 / 2 : ℝ) := by
    rw [abs_mul]
    nlinarith [abs_nonneg θ, abs_nonneg h, hθ, hh]
  have hle_half : θ * h ≤ (1 / 2 : ℝ) := le_trans (le_abs_self _) habs
  have hpos : 0 < 1 - θ * h := by linarith
  exact div_nonneg (Real.exp_pos _).le hpos.le

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Product over eigen-coordinates is bounded by `exp (2 θ²)` when
`∑ h_i² = 1` and `|h_i| ≤ 1`. -/
theorem diagonal_mgf_coordinate_product_bound
    {ι : Type*} [Fintype ι]
    {θ : ℝ} (h : ι → ℝ)
    (hθ : |θ| ≤ (1 / 2 : ℝ))
    (hh : ∀ i : ι, |h i| ≤ 1)
    (hsq : ∑ i : ι, h i ^ 2 = 1) :
    (∏ i : ι, Real.exp (-(θ * h i)) / (1 - θ * h i)) ≤
      Real.exp (2 * θ ^ 2) := by
  classical
  have hprod_le :
      (∏ i : ι, Real.exp (-(θ * h i)) / (1 - θ * h i)) ≤
        ∏ i : ι, Real.exp (2 * (θ * h i) ^ 2) := by
    refine Finset.prod_le_prod ?h0 ?hle
    · intro i _
      exact diagonal_mgf_coordinate_factor_nonneg hθ (hh i)
    · intro i _
      have habs : |θ * h i| ≤ (1 / 2 : ℝ) := by
        rw [abs_mul]
        nlinarith [abs_nonneg θ, abs_nonneg (h i), hθ, hh i]
      exact exp_neg_div_one_sub_le_exp_two_mul_sq (x := θ * h i) habs
  calc
    (∏ i : ι, Real.exp (-(θ * h i)) / (1 - θ * h i))
        ≤ ∏ i : ι, Real.exp (2 * (θ * h i) ^ 2) := hprod_le
    _ = Real.exp (∑ i : ι, 2 * (θ * h i) ^ 2) := by
      rw [Real.exp_sum]
    _ = Real.exp (2 * θ ^ 2 * ∑ i : ι, h i ^ 2) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring_nf
    _ = Real.exp (2 * θ ^ 2) := by
      rw [hsq]
      ring_nf

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Product over independent columns after the coordinate product bound. -/
theorem diagonal_mgf_column_product_bound
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    {θ : ℝ} (h : ι → ℝ)
    (hθ : |θ| ≤ (1 / 2 : ℝ))
    (hh : ∀ i : ι, |h i| ≤ 1)
    (hsq : ∑ i : ι, h i ^ 2 = 1) :
    (∏ _α : κ, ∏ i : ι, Real.exp (-(θ * h i)) / (1 - θ * h i)) ≤
      Real.exp (2 * (Fintype.card κ : ℝ) * θ ^ 2) := by
  classical
  have hcoord := diagonal_mgf_coordinate_product_bound (ι := ι) h hθ hh hsq
  have hcoord_nonneg :
      0 ≤ ∏ i : ι, Real.exp (-(θ * h i)) / (1 - θ * h i) := by
    refine Finset.prod_nonneg ?_
    intro i _
    exact diagonal_mgf_coordinate_factor_nonneg hθ (hh i)
  have hprod_le :
      (∏ _α : κ, ∏ i : ι, Real.exp (-(θ * h i)) / (1 - θ * h i)) ≤
        ∏ _α : κ, Real.exp (2 * θ ^ 2) := by
    refine Finset.prod_le_prod ?h0 ?hle
    · intro _α _
      exact hcoord_nonneg
    · intro _α _
      exact hcoord
  calc
    (∏ _α : κ, ∏ i : ι, Real.exp (-(θ * h i)) / (1 - θ * h i))
        ≤ ∏ _α : κ, Real.exp (2 * θ ^ 2) := hprod_le
    _ = Real.exp (∑ _α : κ, 2 * θ ^ 2) := by
      rw [Real.exp_sum]
    _ = Real.exp ((Fintype.card κ : ℝ) * (2 * θ ^ 2)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ = Real.exp (2 * (Fintype.card κ : ℝ) * θ ^ 2) := by
      ring_nf

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Full MGF bound for independent standard complex Gaussian columns after
factorization and the `∑ h_i² = 1`, `|h_i| ≤ 1` compression. -/
theorem complex_standard_diagonal_mgf_independent_columns_bound
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    {θ : ℝ} (h : ι → ℝ)
    (hθ : |θ| ≤ (1 / 2 : ℝ))
    (hh : ∀ i : ι, |h i| ≤ 1)
    (hsq : ∑ i : ι, h i ^ 2 = 1) :
    ∫ Z : κ → EuclideanSpace ℂ ι,
        Real.exp (θ * ∑ α : κ, ∑ i : ι, h i * (‖Z α i‖ ^ 2 - 1))
          ∂(Measure.pi (fun _ : κ => standardComplexGaussianVectorMeasure ι)) ≤
      Real.exp (2 * (Fintype.card κ : ℝ) * θ ^ 2) := by
  rw [complex_standard_diagonal_mgf_independent_columns_mul h hθ hh]
  exact diagonal_mgf_column_product_bound h hθ hh hsq

/-- Concrete pulled-back MGF bound for unitary coordinates of the Gaussian
columns. -/
theorem gaussianColumn_matrixUnitary_diagonal_mgf_independent_columns_bound
    (U : unitary (BipMatrix p q))
    {θ : ℝ} (h : RandomMatrixModel.BipIndex p q → ℝ)
    (hθ : |θ| ≤ (1 / 2 : ℝ))
    (hh : ∀ i : RandomMatrixModel.BipIndex p q, |h i| ≤ 1)
    (hsq : ∑ i : RandomMatrixModel.BipIndex p q, h i ^ 2 = 1) :
    ∫ ω : Ω p q σ,
        Real.exp (θ * ∑ α : σ, ∑ i : RandomMatrixModel.BipIndex p q,
          h i * (‖matrixUnitaryLinearIsometryEquiv U
            (gaussianColumn p q σ α ω) i‖ ^ 2 - 1))
          ∂(gaussianMeasure p q σ) ≤
      Real.exp (2 * sampleDimension σ * θ ^ 2) := by
  rw [gaussianColumn_matrixUnitary_diagonal_mgf_independent_columns_mul U h hθ hh]
  simpa [sampleDimension] using
    diagonal_mgf_column_product_bound (κ := σ) (ι := RandomMatrixModel.BipIndex p q)
      h hθ hh hsq

/-- Product MGF bound for the eigen-coordinates of
`H_u = (|u⟩⟨u|)^Γ`. -/
theorem rankOneProjectorGamma_eigen_column_product_mgf_bound
    (u : Metric.sphere (0 : BipVector p q) 1)
    {θ : ℝ} (hθ : |θ| ≤ (1 / 2 : ℝ)) :
    (∏ _α : σ, ∏ i : RandomMatrixModel.BipIndex p q,
        Real.exp
            (-(θ *
              rankOneProjectorGammaEigenvalues (p := p) (q := q) (u : BipVector p q) i)) /
          (1 - θ *
            rankOneProjectorGammaEigenvalues (p := p) (q := q) (u : BipVector p q) i)) ≤
      Real.exp (2 * sampleDimension σ * θ ^ 2) := by
  simpa [sampleDimension] using
    diagonal_mgf_column_product_bound (κ := σ) (ι := RandomMatrixModel.BipIndex p q)
      (h := rankOneProjectorGammaEigenvalues (p := p) (q := q) (u : BipVector p q))
      hθ
      (rankOneProjectorGamma_eigenvalues_abs_le_one (p := p) (q := q) u)
      (rankOneProjectorGamma_eigenvalues_sq_sum_unit (p := p) (q := q) u)

/-- MGF bound for the diagonalized eigen-coordinate form of the fixed-vector
partial-transpose Wishart observable. -/
theorem rankOneProjectorGamma_eigen_column_mgf_bound
    (u : Metric.sphere (0 : BipVector p q) 1)
    {θ : ℝ} (hθ : |θ| ≤ (1 / 2 : ℝ)) :
    ∫ ω : Ω p q σ,
        Real.exp
          (θ * ∑ α : σ, ∑ i : RandomMatrixModel.BipIndex p q,
            rankOneProjectorGammaEigenvalues (p := p) (q := q) (u : BipVector p q) i *
              (‖matrixUnitaryLinearIsometryEquiv
                  (star
                    (rankOneProjectorGamma_isHermitian
                      (p := p) (q := q) (u : BipVector p q)).eigenvectorUnitary)
                  (gaussianColumn p q σ α ω) i‖ ^ 2 - 1))
          ∂(gaussianMeasure p q σ) ≤
      Real.exp (2 * sampleDimension σ * θ ^ 2) := by
  rw [rankOneProjectorGamma_eigen_column_mgf_factorization u hθ]
  exact rankOneProjectorGamma_eigen_column_product_mgf_bound (p := p) (q := q) (σ := σ) u hθ

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The preceding one-coordinate formula in the `b = θ h` form used by the
diagonalized quadratic-form calculation. -/
theorem complex_standard_normSq_mgf_real_coordinates_mul
    {θ h : ℝ} (hθ : |θ| ≤ (1 / 2 : ℝ)) (hh : |h| ≤ 1) :
    ∫ x : Fin 2 → ℝ,
        Real.exp ((θ * h) * (((x 0) ^ 2 + (x 1) ^ 2) / 2 - 1))
          ∂(Measure.pi (fun _ : Fin 2 => ProbabilityTheory.gaussianReal 0 1)) =
      Real.exp (-(θ * h)) / (1 - θ * h) := by
  have habs : |θ * h| ≤ (1 / 2 : ℝ) := by
    rw [abs_mul]
    nlinarith [abs_nonneg θ, abs_nonneg h]
  have hlt : θ * h < 1 := by
    have hle_abs : θ * h ≤ |θ * h| := le_abs_self _
    nlinarith
  exact complex_standard_normSq_mgf_real_coordinates (b := θ * h) hlt

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Conjugating a diagonal matrix by a unitary transports its quadratic form
to the same diagonal form applied to the rotated coordinates. -/
theorem quadraticForm_conjStarAlgAut_diagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitary (Matrix ι ι ℂ)) (h : ι → ℝ)
    (z : EuclideanSpace ℂ ι) :
    quadraticForm
      (((Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ)) U)
        (diagonal (fun i : ι => ((h i : ℝ) : ℂ)))) z =
      quadraticForm (diagonal (fun i : ι => ((h i : ℝ) : ℂ)))
        (matrixUnitaryLinearIsometryEquiv (star U) z) := by
  let y := matrixUnitaryLinearIsometryEquiv (star U) z
  have hy : matrixUnitaryLinearIsometryEquiv U y = z := by
    ext i
    simp [y, matrixUnitaryLinearIsometryEquiv_apply, Matrix.ofLp_toEuclideanCLM,
      Matrix.mulVec_mulVec]
  have hy' : matrixUnitaryLinearIsometryEquiv (star U) (matrixUnitaryLinearIsometryEquiv U y) = y := by
    simpa [y] using congrArg (matrixUnitaryLinearIsometryEquiv (star U)) hy
  have hmap :
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
          (((Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ)) U)
            (diagonal (fun i : ι => ((h i : ℝ) : ℂ)))) z =
        matrixUnitaryLinearIsometryEquiv U
          (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
            (diagonal (fun i : ι => ((h i : ℝ) : ℂ))) y) := by
    ext i
    simp [y, Unitary.conjStarAlgAut_apply, matrixUnitaryLinearIsometryEquiv_apply,
      Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hinter :
      inner ℂ
        (matrixUnitaryLinearIsometryEquiv U
          (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
            (diagonal (fun i : ι => ((h i : ℝ) : ℂ))) y))
        (matrixUnitaryLinearIsometryEquiv U y) =
      inner ℂ
        (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
          (diagonal (fun i : ι => ((h i : ℝ) : ℂ))) y)
        y := by
    simpa using
      LinearIsometryEquiv.inner_map_map (matrixUnitaryLinearIsometryEquiv U)
        (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
          (diagonal (fun i : ι => ((h i : ℝ) : ℂ))) y) y
  unfold quadraticForm
  rw [ContinuousLinearMap.reApplyInnerSelf_apply,
    ContinuousLinearMap.reApplyInnerSelf_apply]
  rw [hmap, ← hy, hinter, hy']

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Quadratic-form identity for a unitary-diagonal-unitary-adjoint matrix. -/
theorem quadraticForm_unitary_diagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitary (Matrix ι ι ℂ)) (h : ι → ℝ)
    (z : EuclideanSpace ℂ ι) :
    quadraticForm
      ((U : Matrix ι ι ℂ) *
        diagonal (fun i : ι => ((h i : ℝ) : ℂ)) *
        (U : Matrix ι ι ℂ)ᴴ) z =
      quadraticForm (diagonal (fun i : ι => ((h i : ℝ) : ℂ)))
        (matrixUnitaryLinearIsometryEquiv (star U) z) := by
  simpa [Unitary.conjStarAlgAut_apply, Matrix.mul_assoc] using
    quadraticForm_conjStarAlgAut_diagonal U h z

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Coordinate form of the unitary-diagonal quadratic-form identity. -/
theorem quadraticForm_unitary_diagonal_real
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitary (Matrix ι ι ℂ)) (h : ι → ℝ)
    (z : EuclideanSpace ℂ ι) :
    quadraticForm
      ((U : Matrix ι ι ℂ) *
        diagonal (fun i : ι => ((h i : ℝ) : ℂ)) *
        (U : Matrix ι ι ℂ)ᴴ) z =
      ∑ i : ι,
        h i * ‖matrixUnitaryLinearIsometryEquiv (star U) z i‖ ^ 2 := by
  rw [quadraticForm_unitary_diagonal]
  exact quadraticForm_diagonal_real h (matrixUnitaryLinearIsometryEquiv (star U) z)

/-- Diagonalized matrix rewrite of the fixed-vector `W^Γ` centered observable.

This is the spectral-theorem substitution step only: it replaces
`H_u = (|u⟩⟨u|)^Γ` by its unitary diagonal form inside each column quadratic
form.  The further probabilistic step, which rewrites the law of the rotated
Gaussian coordinates and factors the MGF, is not encoded by this theorem. -/
theorem fixedVectorWishartGammaCenteredSum_diagonalized_rewrite
    (u : BipVector p q) (ω : Ω p q σ) :
    fixedVectorWishartGammaCenteredSum (p := p) (q := q) (σ := σ) u ω =
      ∑ α : σ,
        (quadraticForm
          (Unitary.conjStarAlgAut ℂ _
            (rankOneProjectorGamma_isHermitian (p := p) (q := q) u).eigenvectorUnitary
            (diagonal
              (RCLike.ofReal ∘
                rankOneProjectorGammaEigenvalues (p := p) (q := q) u)))
          (gaussianColumn p q σ α ω) - 1) := by
  rw [fixedVectorWishartGammaCenteredSum_apply]
  refine Finset.sum_congr rfl ?_
  intro α _
  exact congrArg
    (fun A : BipMatrix p q =>
      quadraticForm A (gaussianColumn p q σ α ω) - 1)
    (rankOneProjectorGamma_spectral_theorem (p := p) (q := q) u)

/-- Full eigen-coordinate rewrite of the fixed-vector centered observable. -/
theorem fixedVectorWishartGammaCenteredSum_eigen_coordinate_rewrite
    (u : Metric.sphere (0 : BipVector p q) 1) (ω : Ω p q σ) :
    fixedVectorWishartGammaCenteredSum (p := p) (q := q) (σ := σ)
        (u : BipVector p q) ω =
      ∑ α : σ, ∑ i : RandomMatrixModel.BipIndex p q,
        rankOneProjectorGammaEigenvalues (p := p) (q := q) (u : BipVector p q) i *
          (‖matrixUnitaryLinearIsometryEquiv
              (star
                (rankOneProjectorGamma_isHermitian
                  (p := p) (q := q) (u : BipVector p q)).eigenvectorUnitary)
              (gaussianColumn p q σ α ω) i‖ ^ 2 - 1) := by
  rw [fixedVectorWishartGammaCenteredSum_diagonalized_rewrite
    (p := p) (q := q) (σ := σ) (u := (u : BipVector p q)) (ω := ω)]
  refine Finset.sum_congr rfl ?_
  intro α _
  change quadraticForm
      (((Unitary.conjStarAlgAut ℂ
          (Matrix (RandomMatrixModel.BipIndex p q) (RandomMatrixModel.BipIndex p q) ℂ))
        (rankOneProjectorGamma_isHermitian
          (p := p) (q := q) (u : BipVector p q)).eigenvectorUnitary)
        (diagonal
          (fun i : RandomMatrixModel.BipIndex p q =>
            ((rankOneProjectorGammaEigenvalues
              (p := p) (q := q) (u : BipVector p q) i : ℝ) : ℂ))))
      (gaussianColumn p q σ α ω) - 1 =
    ∑ i : RandomMatrixModel.BipIndex p q,
      rankOneProjectorGammaEigenvalues (p := p) (q := q) (u : BipVector p q) i *
        (‖matrixUnitaryLinearIsometryEquiv
            (star
              (rankOneProjectorGamma_isHermitian
                (p := p) (q := q) (u : BipVector p q)).eigenvectorUnitary)
            (gaussianColumn p q σ α ω) i‖ ^ 2 - 1)
  rw [quadraticForm_conjStarAlgAut_diagonal]
  simpa using
    rankOneProjectorGamma_diagonal_quadraticForm_centered (p := p) (q := q)
      (u := u)
      (z := matrixUnitaryLinearIsometryEquiv
        (star
          (rankOneProjectorGamma_isHermitian
            (p := p) (q := q) (u : BipVector p q)).eigenvectorUnitary)
        (gaussianColumn p q σ α ω))

/-- Product MGF factorization for the fixed-vector centered observable. -/
theorem fixedVectorWishartGammaCenteredSum_mgf_factorization
    (u : Metric.sphere (0 : BipVector p q) 1)
    {θ : ℝ} (hθ : |θ| ≤ (1 / 2 : ℝ)) :
    ∫ ω : Ω p q σ,
        Real.exp
          (θ * fixedVectorWishartGammaCenteredSum (p := p) (q := q) (σ := σ)
            (u : BipVector p q) ω)
          ∂(gaussianMeasure p q σ) =
      ∏ _α : σ, ∏ i : RandomMatrixModel.BipIndex p q,
        Real.exp
            (-(θ *
              rankOneProjectorGammaEigenvalues (p := p) (q := q) (u : BipVector p q) i)) /
          (1 - θ *
            rankOneProjectorGammaEigenvalues (p := p) (q := q) (u : BipVector p q) i) := by
  refine integral_congr_ae ?_ |>.trans
    (rankOneProjectorGamma_eigen_column_mgf_factorization (p := p) (q := q) (σ := σ) u hθ)
  filter_upwards with ω
  exact congrArg
    (fun x : ℝ => Real.exp (θ * x))
    (fixedVectorWishartGammaCenteredSum_eigen_coordinate_rewrite (u := u) (ω := ω))

/-- Integrability of the fixed-vector exponential MGF integrand in the bounded
parameter range `|θ| ≤ 1/2`. -/
theorem fixedVectorWishartGammaCenteredSum_integrable_exp_mul
    (u : Metric.sphere (0 : BipVector p q) 1)
    {θ : ℝ} (hθ : |θ| ≤ (1 / 2 : ℝ)) :
    Integrable (fun ω : Ω p q σ =>
      Real.exp
        (θ * fixedVectorWishartGammaCenteredSum (p := p) (q := q) (σ := σ)
          (u : BipVector p q) ω))
      (gaussianMeasure p q σ) := by
  by_contra hnot
  have hEq := fixedVectorWishartGammaCenteredSum_mgf_factorization
    (p := p) (q := q) (σ := σ) u hθ
  have hzero :
      ∫ ω : Ω p q σ,
          Real.exp
            (θ * fixedVectorWishartGammaCenteredSum (p := p) (q := q) (σ := σ)
              (u : BipVector p q) ω)
            ∂(gaussianMeasure p q σ) = 0 := by
    rw [integral_undef hnot]
  rw [hEq] at hzero
  have hprod_pos :
      0 < ∏ _α : σ, ∏ i : RandomMatrixModel.BipIndex p q,
        Real.exp
            (-(θ *
              rankOneProjectorGammaEigenvalues (p := p) (q := q) (u : BipVector p q) i)) /
          (1 - θ *
            rankOneProjectorGammaEigenvalues (p := p) (q := q) (u : BipVector p q) i) := by
    refine Finset.prod_pos ?_
    intro α _
    refine Finset.prod_pos ?_
    intro i _
    have habs :
        |θ * rankOneProjectorGammaEigenvalues (p := p) (q := q) (u : BipVector p q) i|
          ≤ (1 / 2 : ℝ) := by
      rw [abs_mul]
      nlinarith [abs_nonneg θ,
        abs_nonneg (rankOneProjectorGammaEigenvalues (p := p) (q := q) (u : BipVector p q) i),
        hθ, rankOneProjectorGamma_eigenvalues_abs_le_one (p := p) (q := q) u i]
    have hle_half :
        θ * rankOneProjectorGammaEigenvalues (p := p) (q := q) (u : BipVector p q) i
          ≤ (1 / 2 : ℝ) :=
      le_trans (le_abs_self _) habs
    have hden :
        0 < 1 - θ * rankOneProjectorGammaEigenvalues (p := p) (q := q) (u : BipVector p q) i := by
      linarith
    exact div_pos (Real.exp_pos _) hden
  linarith

/-- Concrete MGF bound for the fixed-vector centered observable. -/
theorem fixedVectorWishartGammaCenteredSum_mgf_bound
    (u : Metric.sphere (0 : BipVector p q) 1)
    {θ : ℝ} (hθ : |θ| ≤ (1 / 2 : ℝ)) :
    ∫ ω : Ω p q σ,
        Real.exp
          (θ * fixedVectorWishartGammaCenteredSum (p := p) (q := q) (σ := σ)
            (u : BipVector p q) ω)
          ∂(gaussianMeasure p q σ) ≤
      Real.exp (2 * sampleDimension σ * θ ^ 2) := by
  rw [fixedVectorWishartGammaCenteredSum_mgf_factorization (p := p) (q := q) (σ := σ) u hθ]
  exact rankOneProjectorGamma_eigen_column_product_mgf_bound (p := p) (q := q) (σ := σ) u hθ

/-! ## Block 4: Fixed-Vector Concentration for `W^Γ` -/

/-- The requested no-input fixed-vector MGF statement now proved with the
explicit constant `C = 2`. -/
theorem FixedVectorWishartGammaMGFStatement :
    ∃ C > 0, ∀ u : Metric.sphere (0 : BipVector p q) 1,
      ∀ θ : ℝ, |θ| ≤ (1 / 2 : ℝ) →
        ∫ ω,
            Real.exp
              (θ * fixedVectorWishartGammaCenteredSum (p := p) (q := q) (σ := σ)
                (u : BipVector p q) ω) ∂gaussianMeasure p q σ ≤
          Real.exp (C * sampleDimension σ * θ ^ 2) := by
  refine ⟨2, by positivity, ?_⟩
  intro u θ hθ
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    fixedVectorWishartGammaCenteredSum_mgf_bound (p := p) (q := q) (σ := σ) u hθ

/-- Historical exported name for the fixed-vector MGF estimate.  This is now
the same no-input theorem as `FixedVectorWishartGammaMGFStatement`. -/
theorem FixedVectorWishartGammaMGFStatement_of_estimate :
    ∃ C > 0, ∀ u : Metric.sphere (0 : BipVector p q) 1,
      ∀ θ : ℝ, |θ| ≤ (1 / 2 : ℝ) →
        ∫ ω,
            Real.exp
              (θ * fixedVectorWishartGammaCenteredSum (p := p) (q := q) (σ := σ)
                (u : BipVector p q) ω) ∂gaussianMeasure p q σ ≤
          Real.exp (C * sampleDimension σ * θ ^ 2) := by
  exact FixedVectorWishartGammaMGFStatement (p := p) (q := q) (σ := σ)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Elementary Chernoff-parameter choice for the local MGF bound:
`θ = min (t / 4) (1 / 2)`. -/
theorem fixedVectorWishartGamma_chernoff_gain
    {t : ℝ} (ht : 0 < t) :
    let θ : ℝ := min (t / 4) (1 / 2)
    0 ≤ θ ∧ |θ| ≤ (1 / 2 : ℝ) ∧
      (1 / 8 : ℝ) * min (t ^ 2) t ≤ θ * t - 2 * θ ^ 2 := by
  dsimp
  by_cases ht2 : t ≤ 2
  · have hθeq : min (t / 4) (1 / 2 : ℝ) = t / 4 := by
      apply min_eq_left
      linarith
    constructor
    · rw [hθeq]
      positivity
    constructor
    · rw [hθeq, abs_of_nonneg]
      · linarith
      · positivity
    · rw [hθeq]
      have hmin : min (t ^ 2) t ≤ t ^ 2 := min_le_left _ _
      have hcoeff : 0 ≤ (1 / 8 : ℝ) := by positivity
      have hscaled : (1 / 8 : ℝ) * min (t ^ 2) t ≤ (1 / 8 : ℝ) * t ^ 2 :=
        mul_le_mul_of_nonneg_left hmin hcoeff
      nlinarith
  · have ht2' : 2 < t := lt_of_not_ge ht2
    have hθeq : min (t / 4) (1 / 2 : ℝ) = (1 / 2 : ℝ) := by
      apply min_eq_right
      linarith
    constructor
    · rw [hθeq]
      positivity
    constructor
    · rw [hθeq]
      norm_num
    · rw [hθeq]
      have hmin_eq : min (t ^ 2) t = t := by
        apply min_eq_right
        nlinarith [ht]
      rw [hmin_eq]
      nlinarith

/-- The requested no-input fixed-vector Bernstein tail proved by Chernoff
optimization with the explicit constant `c = 1 / 8`. -/
theorem FixedVectorWishartGammaBernsteinStatement :
    ∀ u : Metric.sphere (0 : BipVector p q) 1,
      ∀ t : ℝ, 0 < t →
        (gaussianMeasure p q σ).real
            {ω | t * sampleDimension σ ≤
              |fixedVectorWishartGammaCenteredSum (p := p) (q := q) (σ := σ)
                (u : BipVector p q) ω|} ≤
          2 * Real.exp (-((1 / 8 : ℝ) * sampleDimension σ * min (t ^ 2) t)) := by
  intro u t ht
  let θ : ℝ := min (t / 4) (1 / 2)
  let X : Ω p q σ → ℝ := fun ω =>
    fixedVectorWishartGammaCenteredSum (p := p) (q := q) (σ := σ)
      (u : BipVector p q) ω
  haveI : IsProbabilityMeasure (gaussianMeasure p q σ) := by
    rw [gaussianMeasure_eq]
    infer_instance
  have hθdata := fixedVectorWishartGamma_chernoff_gain ht
  have hθ_nonneg : 0 ≤ θ := hθdata.1
  have hθ_abs : |θ| ≤ (1 / 2 : ℝ) := hθdata.2.1
  have hgain : (1 / 8 : ℝ) * min (t ^ 2) t ≤ θ * t - 2 * θ ^ 2 := hθdata.2.2
  have hs_nonneg : 0 ≤ sampleDimension σ := by
    change (0 : ℝ) ≤ (Fintype.card σ : ℝ)
    positivity
  have hIntPos :
      Integrable (fun ω : Ω p q σ =>
        Real.exp (θ * X ω))
        (gaussianMeasure p q σ) :=
    fixedVectorWishartGammaCenteredSum_integrable_exp_mul
      (p := p) (q := q) (σ := σ) u hθ_abs
  have hθ_neg_abs : |(-θ : ℝ)| ≤ (1 / 2 : ℝ) := by
    simpa using hθ_abs
  have hIntNeg :
      Integrable (fun ω : Ω p q σ =>
        Real.exp ((-θ) * X ω))
        (gaussianMeasure p q σ) :=
    fixedVectorWishartGammaCenteredSum_integrable_exp_mul
      (p := p) (q := q) (σ := σ) u hθ_neg_abs
  have hUpper :
      (gaussianMeasure p q σ).real
          {ω | t * sampleDimension σ ≤ X ω} ≤
        Real.exp (-((1 / 8 : ℝ) * sampleDimension σ * min (t ^ 2) t)) := by
    have hchern :=
      ProbabilityTheory.measure_ge_le_exp_mul_mgf
        (μ := gaussianMeasure p q σ)
        (X := X)
        (ε := t * sampleDimension σ) hθ_nonneg hIntPos
    have hmgf :
        ProbabilityTheory.mgf X (gaussianMeasure p q σ) θ ≤
          Real.exp (2 * sampleDimension σ * θ ^ 2) := by
      rw [ProbabilityTheory.mgf]
      exact fixedVectorWishartGammaCenteredSum_mgf_bound
        (p := p) (q := q) (σ := σ) u hθ_abs
    calc
      (gaussianMeasure p q σ).real
          {ω | t * sampleDimension σ ≤ X ω} ≤
          Real.exp (-θ * (t * sampleDimension σ)) *
            ProbabilityTheory.mgf X (gaussianMeasure p q σ) θ := hchern
      _ ≤ Real.exp (-θ * (t * sampleDimension σ)) *
            Real.exp (2 * sampleDimension σ * θ ^ 2) := by
          gcongr
      _ = Real.exp (-(sampleDimension σ * (θ * t - 2 * θ ^ 2))) := by
          rw [← Real.exp_add]
          congr 1
          ring_nf
      _ ≤ Real.exp (-((1 / 8 : ℝ) * sampleDimension σ * min (t ^ 2) t)) := by
          apply Real.exp_le_exp.mpr
          have hscaled :
              (1 / 8 : ℝ) * sampleDimension σ * min (t ^ 2) t ≤
                sampleDimension σ * (θ * t - 2 * θ ^ 2) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              mul_le_mul_of_nonneg_left hgain hs_nonneg
          nlinarith

  have hLower :
      (gaussianMeasure p q σ).real
          {ω | X ω ≤ -(t * sampleDimension σ)} ≤
        Real.exp (-((1 / 8 : ℝ) * sampleDimension σ * min (t ^ 2) t)) := by
    have hchern :=
      ProbabilityTheory.measure_le_le_exp_mul_mgf
        (μ := gaussianMeasure p q σ)
        (X := X)
        (ε := -(t * sampleDimension σ)) (by linarith : -θ ≤ 0) hIntNeg
    have hmgf :
        ProbabilityTheory.mgf X (gaussianMeasure p q σ) (-θ) ≤
          Real.exp (2 * sampleDimension σ * θ ^ 2) := by
      rw [ProbabilityTheory.mgf]
      have := fixedVectorWishartGammaCenteredSum_mgf_bound
        (p := p) (q := q) (σ := σ) (u := u) (θ := -θ) hθ_neg_abs
      simpa [X, neg_mul, mul_assoc, mul_left_comm, mul_comm] using this
    calc
      (gaussianMeasure p q σ).real
          {ω | X ω ≤ -(t * sampleDimension σ)} ≤
          Real.exp (-(-θ) * (-(t * sampleDimension σ))) *
            ProbabilityTheory.mgf X (gaussianMeasure p q σ) (-θ) := hchern
      _ ≤ Real.exp (-(-θ) * (-(t * sampleDimension σ))) *
            Real.exp (2 * sampleDimension σ * θ ^ 2) := by
          gcongr
      _ = Real.exp (-(sampleDimension σ * (θ * t - 2 * θ ^ 2))) := by
          rw [← Real.exp_add]
          congr 1
          ring_nf
      _ ≤ Real.exp (-((1 / 8 : ℝ) * sampleDimension σ * min (t ^ 2) t)) := by
          apply Real.exp_le_exp.mpr
          have hscaled :
              (1 / 8 : ℝ) * sampleDimension σ * min (t ^ 2) t ≤
                sampleDimension σ * (θ * t - 2 * θ ^ 2) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              mul_le_mul_of_nonneg_left hgain hs_nonneg
          nlinarith
  have hAbsSubset :
      {ω | t * sampleDimension σ ≤
        |X ω|} ⊆
        {ω | t * sampleDimension σ ≤ X ω} ∪
        {ω | X ω ≤ -(t * sampleDimension σ)} := by
    intro ω hω
    by_cases hsum : 0 ≤ X ω
    · left
      simpa [abs_of_nonneg hsum] using hω
    · right
      have hneg : t * sampleDimension σ ≤ -X ω := by
        simpa [abs_of_neg (lt_of_not_ge hsum)] using hω
      show X ω ≤ -(t * sampleDimension σ)
      linarith
  calc
    (gaussianMeasure p q σ).real
        {ω | t * sampleDimension σ ≤ |X ω|} ≤
        (gaussianMeasure p q σ).real
          ({ω | t * sampleDimension σ ≤ X ω} ∪
            {ω | X ω ≤ -(t * sampleDimension σ)}) := by
          exact measureReal_mono
            (h₂ := (measure_lt_top (gaussianMeasure p q σ) _).ne) hAbsSubset
    _ ≤ (gaussianMeasure p q σ).real
          {ω | t * sampleDimension σ ≤ X ω} +
        (gaussianMeasure p q σ).real {ω | X ω ≤ -(t * sampleDimension σ)} := by
          exact measureReal_union_le _ _
    _ ≤ Real.exp (-((1 / 8 : ℝ) * sampleDimension σ * min (t ^ 2) t)) +
        Real.exp (-((1 / 8 : ℝ) * sampleDimension σ * min (t ^ 2) t)) := by
          gcongr
    _ = 2 * Real.exp (-(((1 / 8 : ℝ) * sampleDimension σ * min (t ^ 2) t))) := by
          ring

/-- Existential no-input fixed-vector Bernstein tail, matching the shape of
the legacy `_of_estimate` compatibility wrapper. -/
theorem FixedVectorWishartGammaBernsteinStatementExists :
    ∃ c > 0, ∀ u : Metric.sphere (0 : BipVector p q) 1,
      ∀ t : ℝ, 0 < t →
        (gaussianMeasure p q σ).real
            {ω | t * sampleDimension σ ≤
              |fixedVectorWishartGammaCenteredSum (p := p) (q := q) (σ := σ)
                (u : BipVector p q) ω|} ≤
          2 * Real.exp (-(c * sampleDimension σ * min (t ^ 2) t)) := by
  refine ⟨(1 / 8 : ℝ), by positivity, ?_⟩
  intro u t ht
  simpa using
    FixedVectorWishartGammaBernsteinStatement
      (p := p) (q := q) (σ := σ) (u := u) (t := t) ht

/-- Historical exported name for the fixed-vector Bernstein tail.  This is now
the same no-input theorem as `FixedVectorWishartGammaBernsteinStatementExists`. -/
theorem FixedVectorWishartGammaBernsteinStatement_of_estimate :
    ∃ c > 0, ∀ u : Metric.sphere (0 : BipVector p q) 1,
      ∀ t : ℝ, 0 < t →
        (gaussianMeasure p q σ).real
            {ω | t * sampleDimension σ ≤
              |fixedVectorWishartGammaCenteredSum (p := p) (q := q) (σ := σ)
                (u : BipVector p q) ω|} ≤
          2 * Real.exp (-(c * sampleDimension σ * min (t ^ 2) t)) := by
  exact FixedVectorWishartGammaBernsteinStatementExists
    (p := p) (q := q) (σ := σ)

omit [Fintype σ] in
/-- If a Hermitian bipartite matrix has Frobenius norm at most one, the sum of
the squares of its eigenvalues is at most one. -/
theorem hermitian_eigenvalues_sq_sum_le_one_of_frobeniusNorm_le_one
    (H : BipMatrix p q) (hH : H.IsHermitian)
    (hF :
      frobeniusNorm (p := p) (q := q) (σ := RandomMatrixModel.BipIndex p q) H ≤ 1) :
    ∑ i : RandomMatrixModel.BipIndex p q, hH.eigenvalues i ^ 2 ≤ 1 := by
  have hbridge :=
    hermitian_frobeniusNorm_sq_eq_sum_eigenvalues_sq (p := p) (q := q) H hH
  have hnonneg :
      0 ≤ frobeniusNorm (p := p) (q := q) (σ := RandomMatrixModel.BipIndex p q) H := by
    unfold frobeniusNorm
    positivity
  have hsq :
      frobeniusNorm (p := p) (q := q) (σ := RandomMatrixModel.BipIndex p q) H ^ 2 ≤
        (1 : ℝ) := by
    nlinarith
  simpa [hbridge.symm] using hsq

omit [Fintype σ] in
/-- Under the same Frobenius-one bound, every Hermitian eigenvalue has absolute
value at most one. -/
theorem hermitian_eigenvalues_abs_le_one_of_frobeniusNorm_le_one
    (H : BipMatrix p q) (hH : H.IsHermitian)
    (hF :
      frobeniusNorm (p := p) (q := q) (σ := RandomMatrixModel.BipIndex p q) H ≤ 1)
    (i : RandomMatrixModel.BipIndex p q) :
    |hH.eigenvalues i| ≤ 1 := by
  have hsum :=
    hermitian_eigenvalues_sq_sum_le_one_of_frobeniusNorm_le_one
      (p := p) (q := q) H hH hF
  have hsingle :
      hH.eigenvalues i ^ 2 ≤
        ∑ j : RandomMatrixModel.BipIndex p q, hH.eigenvalues j ^ 2 := by
    exact Finset.single_le_sum
      (fun j _ => sq_nonneg (hH.eigenvalues j))
      (Finset.mem_univ i)
  exact (sq_le_one_iff_abs_le_one (hH.eigenvalues i)).mp
    (le_trans hsingle hsum)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Product over eigen-coordinates is bounded by `exp (2 θ²)` when
`∑ h_i² ≤ 1` and `|h_i| ≤ 1`. -/
theorem diagonal_mgf_coordinate_product_bound_le_one
    {ι : Type*} [Fintype ι]
    {θ : ℝ} (h : ι → ℝ)
    (hθ : |θ| ≤ (1 / 2 : ℝ))
    (hh : ∀ i : ι, |h i| ≤ 1)
    (hsq : ∑ i : ι, h i ^ 2 ≤ 1) :
    (∏ i : ι, Real.exp (-(θ * h i)) / (1 - θ * h i)) ≤
      Real.exp (2 * θ ^ 2) := by
  classical
  have hprod_le :
      (∏ i : ι, Real.exp (-(θ * h i)) / (1 - θ * h i)) ≤
        ∏ i : ι, Real.exp (2 * (θ * h i) ^ 2) := by
    refine Finset.prod_le_prod ?h0 ?hle
    · intro i _
      exact diagonal_mgf_coordinate_factor_nonneg hθ (hh i)
    · intro i _
      have habs : |θ * h i| ≤ (1 / 2 : ℝ) := by
        rw [abs_mul]
        nlinarith [abs_nonneg θ, abs_nonneg (h i), hθ, hh i]
      exact exp_neg_div_one_sub_le_exp_two_mul_sq (x := θ * h i) habs
  calc
    (∏ i : ι, Real.exp (-(θ * h i)) / (1 - θ * h i))
        ≤ ∏ i : ι, Real.exp (2 * (θ * h i) ^ 2) := hprod_le
    _ = Real.exp (∑ i : ι, 2 * (θ * h i) ^ 2) := by
      rw [Real.exp_sum]
    _ = Real.exp (2 * θ ^ 2 * ∑ i : ι, h i ^ 2) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring_nf
    _ ≤ Real.exp (2 * θ ^ 2) := by
      apply Real.exp_le_exp.mpr
      have hcoeff : 0 ≤ 2 * θ ^ 2 := by positivity
      nlinarith

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Product over independent columns after the `∑ h_i² ≤ 1` coordinate bound. -/
theorem diagonal_mgf_column_product_bound_le_one
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    {θ : ℝ} (h : ι → ℝ)
    (hθ : |θ| ≤ (1 / 2 : ℝ))
    (hh : ∀ i : ι, |h i| ≤ 1)
    (hsq : ∑ i : ι, h i ^ 2 ≤ 1) :
    (∏ _α : κ, ∏ i : ι, Real.exp (-(θ * h i)) / (1 - θ * h i)) ≤
      Real.exp (2 * (Fintype.card κ : ℝ) * θ ^ 2) := by
  classical
  have hcoord := diagonal_mgf_coordinate_product_bound_le_one (ι := ι) h hθ hh hsq
  have hcoord_nonneg :
      0 ≤ ∏ i : ι, Real.exp (-(θ * h i)) / (1 - θ * h i) := by
    refine Finset.prod_nonneg ?_
    intro i _
    exact diagonal_mgf_coordinate_factor_nonneg hθ (hh i)
  have hprod_le :
      (∏ _α : κ, ∏ i : ι, Real.exp (-(θ * h i)) / (1 - θ * h i)) ≤
        ∏ _α : κ, Real.exp (2 * θ ^ 2) := by
    refine Finset.prod_le_prod ?h0 ?hle
    · intro _α _
      exact hcoord_nonneg
    · intro _α _
      exact hcoord
  calc
    (∏ _α : κ, ∏ i : ι, Real.exp (-(θ * h i)) / (1 - θ * h i))
        ≤ ∏ _α : κ, Real.exp (2 * θ ^ 2) := hprod_le
    _ = Real.exp (∑ _α : κ, 2 * θ ^ 2) := by
      rw [Real.exp_sum]
    _ = Real.exp ((Fintype.card κ : ℝ) * (2 * θ ^ 2)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ = Real.exp (2 * (Fintype.card κ : ℝ) * θ ^ 2) := by
      ring_nf

/-- Diagonalized coordinate rewrite for an arbitrary Hermitian quadratic-form
summand. -/
theorem hermitian_quadraticForm_centered_eigen_coordinate_rewrite
    (H : BipMatrix p q) (hH : H.IsHermitian)
    (z : BipVector p q) :
    quadraticForm H z - RCLike.re H.trace =
      ∑ i : RandomMatrixModel.BipIndex p q,
        hH.eigenvalues i *
          (‖matrixUnitaryLinearIsometryEquiv (star hH.eigenvectorUnitary) z i‖ ^ 2 - 1) := by
  let h : RandomMatrixModel.BipIndex p q → ℝ := hH.eigenvalues
  let D : BipMatrix p q := diagonal (fun i : RandomMatrixModel.BipIndex p q => ((h i : ℝ) : ℂ))
  have htrace : RCLike.re H.trace = ∑ i : RandomMatrixModel.BipIndex p q, h i := by
    have ht : H.trace = ∑ i : RandomMatrixModel.BipIndex p q, (hH.eigenvalues i : ℂ) :=
      hH.trace_eq_sum_eigenvalues
    simpa [h] using congrArg RCLike.re ht
  have hspec :
      H =
        (((Unitary.conjStarAlgAut ℂ
          (Matrix (RandomMatrixModel.BipIndex p q) (RandomMatrixModel.BipIndex p q) ℂ))
            hH.eigenvectorUnitary) D) := by
    simpa [D, h] using hH.spectral_theorem
  have hq :
      quadraticForm H z =
        quadraticForm
          (((Unitary.conjStarAlgAut ℂ
            (Matrix (RandomMatrixModel.BipIndex p q) (RandomMatrixModel.BipIndex p q) ℂ))
              hH.eigenvectorUnitary) D) z :=
    congrArg (fun A : BipMatrix p q => quadraticForm A z) hspec
  calc
    quadraticForm H z - RCLike.re H.trace =
        quadraticForm
          (((Unitary.conjStarAlgAut ℂ
            (Matrix (RandomMatrixModel.BipIndex p q) (RandomMatrixModel.BipIndex p q) ℂ))
              hH.eigenvectorUnitary) D) z - ∑ i : RandomMatrixModel.BipIndex p q, h i := by
          rw [htrace, hq]
    _ = quadraticForm D (matrixUnitaryLinearIsometryEquiv (star hH.eigenvectorUnitary) z) -
          ∑ i : RandomMatrixModel.BipIndex p q, h i := by
          rw [quadraticForm_conjStarAlgAut_diagonal]
    _ = ∑ i : RandomMatrixModel.BipIndex p q,
        hH.eigenvalues i *
          (‖matrixUnitaryLinearIsometryEquiv (star hH.eigenvectorUnitary) z i‖ ^ 2 - 1) := by
          simpa [D, h] using
            quadraticForm_diagonal_real_sub_sum
              (h := h)
              (z := matrixUnitaryLinearIsometryEquiv (star hH.eigenvectorUnitary) z)

/-- Full eigen-coordinate rewrite of the canonical centered quadratic-form
sum for an arbitrary Hermitian `H`. -/
theorem canonicalCenteredQuadraticFormSum_eigen_coordinate_rewrite
    (H : BipMatrix p q) (hH : H.IsHermitian) (ω : Ω p q σ) :
    canonicalCenteredQuadraticFormSum (p := p) (q := q) (σ := σ) H ω =
      ∑ α : σ, ∑ i : RandomMatrixModel.BipIndex p q,
        hH.eigenvalues i *
          (‖matrixUnitaryLinearIsometryEquiv (star hH.eigenvectorUnitary)
              (gaussianColumn p q σ α ω) i‖ ^ 2 - 1) := by
  rw [canonicalCenteredQuadraticFormSum_apply]
  refine Finset.sum_congr rfl ?_
  intro α _
  exact hermitian_quadraticForm_centered_eigen_coordinate_rewrite
    (p := p) (q := q) H hH (gaussianColumn p q σ α ω)

/-- Product MGF factorization for the canonical centered quadratic-form sum
of an arbitrary Hermitian `H`. -/
theorem canonicalCenteredQuadraticFormSum_mgf_factorization
    (H : BipMatrix p q) (hH : H.IsHermitian)
    (hF :
      frobeniusNorm (p := p) (q := q) (σ := RandomMatrixModel.BipIndex p q) H ≤ 1)
    {θ : ℝ} (hθ : |θ| ≤ (1 / 2 : ℝ)) :
    ∫ ω : Ω p q σ,
        Real.exp
          (θ * canonicalCenteredQuadraticFormSum (p := p) (q := q) (σ := σ) H ω)
          ∂(gaussianMeasure p q σ) =
      ∏ _α : σ, ∏ i : RandomMatrixModel.BipIndex p q,
        Real.exp (-(θ * hH.eigenvalues i)) /
          (1 - θ * hH.eigenvalues i) := by
  refine integral_congr_ae ?_ |>.trans
    (gaussianColumn_matrixUnitary_diagonal_mgf_independent_columns_mul
      (p := p) (q := q) (σ := σ)
      (U := star hH.eigenvectorUnitary)
      (h := hH.eigenvalues)
      hθ
      (hermitian_eigenvalues_abs_le_one_of_frobeniusNorm_le_one
        (p := p) (q := q) H hH hF))
  filter_upwards with ω
  exact congrArg
    (fun x : ℝ => Real.exp (θ * x))
    (canonicalCenteredQuadraticFormSum_eigen_coordinate_rewrite
      (p := p) (q := q) (σ := σ) H hH ω)

/-- Integrability of the exponential MGF integrand for the general centered
quadratic-form sum in the bounded parameter range. -/
theorem canonicalCenteredQuadraticFormSum_integrable_exp_mul
    (H : BipMatrix p q) (hH : H.IsHermitian)
    (hF :
      frobeniusNorm (p := p) (q := q) (σ := RandomMatrixModel.BipIndex p q) H ≤ 1)
    {θ : ℝ} (hθ : |θ| ≤ (1 / 2 : ℝ)) :
    Integrable
      (fun ω : Ω p q σ =>
        Real.exp
          (θ * canonicalCenteredQuadraticFormSum (p := p) (q := q) (σ := σ) H ω))
      (gaussianMeasure p q σ) := by
  by_contra hnot
  have hEq :=
    canonicalCenteredQuadraticFormSum_mgf_factorization
      (p := p) (q := q) (σ := σ) H hH hF hθ
  have hzero :
      ∫ ω : Ω p q σ,
          Real.exp
            (θ * canonicalCenteredQuadraticFormSum (p := p) (q := q) (σ := σ) H ω)
          ∂(gaussianMeasure p q σ) = 0 := by
    rw [integral_undef hnot]
  rw [hEq] at hzero
  have hprod_pos :
      0 < ∏ _α : σ, ∏ i : RandomMatrixModel.BipIndex p q,
        Real.exp (-(θ * hH.eigenvalues i)) /
          (1 - θ * hH.eigenvalues i) := by
    refine Finset.prod_pos ?_
    intro α _
    refine Finset.prod_pos ?_
    intro i _
    have hh :=
      hermitian_eigenvalues_abs_le_one_of_frobeniusNorm_le_one
        (p := p) (q := q) H hH hF i
    have habs : |θ * hH.eigenvalues i| ≤ (1 / 2 : ℝ) := by
      rw [abs_mul]
      nlinarith [abs_nonneg θ, abs_nonneg (hH.eigenvalues i), hθ, hh]
    have hle_half : θ * hH.eigenvalues i ≤ (1 / 2 : ℝ) :=
      le_trans (le_abs_self _) habs
    have hden : 0 < 1 - θ * hH.eigenvalues i := by linarith
    exact div_pos (Real.exp_pos _) hden
  linarith

/-- MGF bound for the general canonical centered quadratic-form sum. -/
theorem canonicalCenteredQuadraticFormSum_mgf_bound
    (H : BipMatrix p q) (hH : H.IsHermitian)
    (hF :
      frobeniusNorm (p := p) (q := q) (σ := RandomMatrixModel.BipIndex p q) H ≤ 1)
    {θ : ℝ} (hθ : |θ| ≤ (1 / 2 : ℝ)) :
    ∫ ω : Ω p q σ,
        Real.exp
          (θ * canonicalCenteredQuadraticFormSum (p := p) (q := q) (σ := σ) H ω)
          ∂(gaussianMeasure p q σ) ≤
      Real.exp (2 * sampleDimension σ * θ ^ 2) := by
  rw [canonicalCenteredQuadraticFormSum_mgf_factorization
    (p := p) (q := q) (σ := σ) H hH hF hθ]
  simpa [sampleDimension] using
    diagonal_mgf_column_product_bound_le_one
      (κ := σ) (ι := RandomMatrixModel.BipIndex p q)
      (h := hH.eigenvalues)
      hθ
      (hermitian_eigenvalues_abs_le_one_of_frobeniusNorm_le_one
        (p := p) (q := q) H hH hF)
      (hermitian_eigenvalues_sq_sum_le_one_of_frobeniusNorm_le_one
        (p := p) (q := q) H hH hF)

/-- The requested no-input general Gaussian quadratic-form Bernstein estimate
for the canonical concrete Gaussian model. -/
theorem GaussianQuadraticFormBernsteinStatement :
    ∃ c > 0, ∀ (H : BipMatrix p q),
      H.IsHermitian →
      opNorm H ≤ 1 →
      frobeniusNorm (p := p) (q := q) (σ := RandomMatrixModel.BipIndex p q) H ≤ 1 →
      ∀ t : ℝ, 0 < t →
        (gaussianMeasure p q σ).real
            {ω | t * sampleDimension σ ≤
              |canonicalCenteredQuadraticFormSum (p := p) (q := q) (σ := σ) H ω|} ≤
          2 * Real.exp (-(c * sampleDimension σ * min (t ^ 2) t)) := by
  refine ⟨(1 / 8 : ℝ), by positivity, ?_⟩
  intro H hH _hOp hF t ht
  let θ : ℝ := min (t / 4) (1 / 2)
  let X : Ω p q σ → ℝ := fun ω =>
    canonicalCenteredQuadraticFormSum (p := p) (q := q) (σ := σ) H ω
  haveI : IsProbabilityMeasure (gaussianMeasure p q σ) := by
    rw [gaussianMeasure_eq]
    infer_instance
  have hθdata := fixedVectorWishartGamma_chernoff_gain ht
  have hθ_nonneg : 0 ≤ θ := hθdata.1
  have hθ_abs : |θ| ≤ (1 / 2 : ℝ) := hθdata.2.1
  have hgain : (1 / 8 : ℝ) * min (t ^ 2) t ≤ θ * t - 2 * θ ^ 2 := hθdata.2.2
  have hs_nonneg : 0 ≤ sampleDimension σ := by
    change (0 : ℝ) ≤ (Fintype.card σ : ℝ)
    positivity
  have hIntPos :
      Integrable (fun ω : Ω p q σ => Real.exp (θ * X ω))
        (gaussianMeasure p q σ) := by
    simpa [X] using
      canonicalCenteredQuadraticFormSum_integrable_exp_mul
        (p := p) (q := q) (σ := σ) H hH hF hθ_abs
  have hθ_neg_abs : |(-θ : ℝ)| ≤ (1 / 2 : ℝ) := by
    simpa using hθ_abs
  have hIntNeg :
      Integrable (fun ω : Ω p q σ => Real.exp ((-θ) * X ω))
        (gaussianMeasure p q σ) := by
    simpa [X] using
      canonicalCenteredQuadraticFormSum_integrable_exp_mul
        (p := p) (q := q) (σ := σ) H hH hF hθ_neg_abs
  have hUpper :
      (gaussianMeasure p q σ).real
          {ω | t * sampleDimension σ ≤ X ω} ≤
        Real.exp (-((1 / 8 : ℝ) * sampleDimension σ * min (t ^ 2) t)) := by
    have hchern :=
      ProbabilityTheory.measure_ge_le_exp_mul_mgf
        (μ := gaussianMeasure p q σ)
        (X := X)
        (ε := t * sampleDimension σ) hθ_nonneg hIntPos
    have hmgf :
        ProbabilityTheory.mgf X (gaussianMeasure p q σ) θ ≤
          Real.exp (2 * sampleDimension σ * θ ^ 2) := by
      rw [ProbabilityTheory.mgf]
      simpa [X] using
        canonicalCenteredQuadraticFormSum_mgf_bound
          (p := p) (q := q) (σ := σ) H hH hF hθ_abs
    calc
      (gaussianMeasure p q σ).real
          {ω | t * sampleDimension σ ≤ X ω} ≤
          Real.exp (-θ * (t * sampleDimension σ)) *
            ProbabilityTheory.mgf X (gaussianMeasure p q σ) θ := hchern
      _ ≤ Real.exp (-θ * (t * sampleDimension σ)) *
            Real.exp (2 * sampleDimension σ * θ ^ 2) := by
          gcongr
      _ = Real.exp (-(sampleDimension σ * (θ * t - 2 * θ ^ 2))) := by
          rw [← Real.exp_add]
          congr 1
          ring_nf
      _ ≤ Real.exp (-((1 / 8 : ℝ) * sampleDimension σ * min (t ^ 2) t)) := by
          apply Real.exp_le_exp.mpr
          have hscaled :
              (1 / 8 : ℝ) * sampleDimension σ * min (t ^ 2) t ≤
                sampleDimension σ * (θ * t - 2 * θ ^ 2) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              mul_le_mul_of_nonneg_left hgain hs_nonneg
          nlinarith
  have hLower :
      (gaussianMeasure p q σ).real
          {ω | X ω ≤ -(t * sampleDimension σ)} ≤
        Real.exp (-((1 / 8 : ℝ) * sampleDimension σ * min (t ^ 2) t)) := by
    have hchern :=
      ProbabilityTheory.measure_le_le_exp_mul_mgf
        (μ := gaussianMeasure p q σ)
        (X := X)
        (ε := -(t * sampleDimension σ)) (by linarith : -θ ≤ 0) hIntNeg
    have hmgf :
        ProbabilityTheory.mgf X (gaussianMeasure p q σ) (-θ) ≤
          Real.exp (2 * sampleDimension σ * θ ^ 2) := by
      rw [ProbabilityTheory.mgf]
      have := canonicalCenteredQuadraticFormSum_mgf_bound
        (p := p) (q := q) (σ := σ) H hH hF hθ_neg_abs
      simpa [X, neg_mul, mul_assoc, mul_left_comm, mul_comm] using this
    calc
      (gaussianMeasure p q σ).real
          {ω | X ω ≤ -(t * sampleDimension σ)} ≤
          Real.exp (-(-θ) * (-(t * sampleDimension σ))) *
            ProbabilityTheory.mgf X (gaussianMeasure p q σ) (-θ) := hchern
      _ ≤ Real.exp (-(-θ) * (-(t * sampleDimension σ))) *
            Real.exp (2 * sampleDimension σ * θ ^ 2) := by
          gcongr
      _ = Real.exp (-(sampleDimension σ * (θ * t - 2 * θ ^ 2))) := by
          rw [← Real.exp_add]
          congr 1
          ring_nf
      _ ≤ Real.exp (-((1 / 8 : ℝ) * sampleDimension σ * min (t ^ 2) t)) := by
          apply Real.exp_le_exp.mpr
          have hscaled :
              (1 / 8 : ℝ) * sampleDimension σ * min (t ^ 2) t ≤
                sampleDimension σ * (θ * t - 2 * θ ^ 2) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              mul_le_mul_of_nonneg_left hgain hs_nonneg
          nlinarith
  have hAbsSubset :
      {ω | t * sampleDimension σ ≤ |X ω|} ⊆
        {ω | t * sampleDimension σ ≤ X ω} ∪
        {ω | X ω ≤ -(t * sampleDimension σ)} := by
    intro ω hω
    by_cases hsum : 0 ≤ X ω
    · left
      simpa [abs_of_nonneg hsum] using hω
    · right
      have hneg : t * sampleDimension σ ≤ -X ω := by
        simpa [abs_of_neg (lt_of_not_ge hsum)] using hω
      show X ω ≤ -(t * sampleDimension σ)
      linarith
  calc
    (gaussianMeasure p q σ).real
        {ω | t * sampleDimension σ ≤ |X ω|} ≤
        (gaussianMeasure p q σ).real
          ({ω | t * sampleDimension σ ≤ X ω} ∪
            {ω | X ω ≤ -(t * sampleDimension σ)}) := by
          exact measureReal_mono
            (h₂ := (measure_lt_top (gaussianMeasure p q σ) _).ne) hAbsSubset
    _ ≤ (gaussianMeasure p q σ).real
          {ω | t * sampleDimension σ ≤ X ω} +
        (gaussianMeasure p q σ).real {ω | X ω ≤ -(t * sampleDimension σ)} := by
          exact measureReal_union_le _ _
    _ ≤ Real.exp (-((1 / 8 : ℝ) * sampleDimension σ * min (t ^ 2) t)) +
        Real.exp (-((1 / 8 : ℝ) * sampleDimension σ * min (t ^ 2) t)) := by
          gcongr
    _ = 2 * Real.exp (-(((1 / 8 : ℝ) * sampleDimension σ * min (t ^ 2) t))) := by
          ring

/-- Historical exported name for Lemma A's Gaussian quadratic-form Bernstein
estimate.  This is now a genuine no-input theorem, with constant `1 / 8`,
proved from the diagonal MGF factorization and Chernoff optimization above. -/
theorem GaussianQuadraticFormBernsteinStatement_of_estimate :
    ∃ c > 0, ∀ (H : BipMatrix p q),
      H.IsHermitian →
      opNorm H ≤ 1 →
      frobeniusNorm (p := p) (q := q) (σ := RandomMatrixModel.BipIndex p q) H ≤ 1 →
      ∀ t : ℝ, 0 < t →
        (gaussianMeasure p q σ).real
            {ω | t * sampleDimension σ ≤
              |canonicalCenteredQuadraticFormSum (p := p) (q := q) (σ := σ) H ω|} ≤
          2 * Real.exp (-(c * sampleDimension σ * min (t ^ 2) t)) := by
  exact GaussianQuadraticFormBernsteinStatement
    (p := p) (q := q) (σ := σ)

/-- Explicit Bernstein tail for the canonical centered quadratic-form sum
attached to a unit rank-one projector. -/
theorem rankOneProjectorCenteredBernsteinStatement
    (u : Metric.sphere (0 : BipVector p q) 1) :
    ∀ t : ℝ, 0 < t →
      (gaussianMeasure p q σ).real
          {ω | t * sampleDimension σ ≤
            |canonicalCenteredQuadraticFormSum (p := p) (q := q) (σ := σ)
              (rankOneProjector (p := p) (q := q) (u : BipVector p q)) ω|} ≤
        2 * Real.exp (-((1 / 8 : ℝ) * sampleDimension σ * min (t ^ 2) t)) := by
  intro t ht
  let H : BipMatrix p q := rankOneProjector (p := p) (q := q) (u : BipVector p q)
  let θ : ℝ := min (t / 4) (1 / 2)
  let X : Ω p q σ → ℝ := fun ω =>
    canonicalCenteredQuadraticFormSum (p := p) (q := q) (σ := σ) H ω
  have hH : H.IsHermitian := rankOneProjector_isHermitian (p := p) (q := q) (u : BipVector p q)
  have hF :
      frobeniusNorm (p := p) (q := q) (σ := RandomMatrixModel.BipIndex p q) H ≤ 1 := by
    dsimp [H]
    rw [rankOneProjector_frobeniusNorm_unit (p := p) (q := q) u]
  haveI : IsProbabilityMeasure (gaussianMeasure p q σ) := by
    rw [gaussianMeasure_eq]
    infer_instance
  have hθdata := fixedVectorWishartGamma_chernoff_gain ht
  have hθ_nonneg : 0 ≤ θ := hθdata.1
  have hθ_abs : |θ| ≤ (1 / 2 : ℝ) := hθdata.2.1
  have hgain : (1 / 8 : ℝ) * min (t ^ 2) t ≤ θ * t - 2 * θ ^ 2 := hθdata.2.2
  have hs_nonneg : 0 ≤ sampleDimension σ := by
    change (0 : ℝ) ≤ (Fintype.card σ : ℝ)
    positivity
  have hIntPos :
      Integrable (fun ω : Ω p q σ => Real.exp (θ * X ω))
        (gaussianMeasure p q σ) := by
    simpa [X, H] using
      canonicalCenteredQuadraticFormSum_integrable_exp_mul
        (p := p) (q := q) (σ := σ)
        (rankOneProjector (p := p) (q := q) (u : BipVector p q)) hH hF hθ_abs
  have hθ_neg_abs : |(-θ : ℝ)| ≤ (1 / 2 : ℝ) := by
    simpa using hθ_abs
  have hIntNeg :
      Integrable (fun ω : Ω p q σ => Real.exp ((-θ) * X ω))
        (gaussianMeasure p q σ) := by
    simpa [X, H] using
      canonicalCenteredQuadraticFormSum_integrable_exp_mul
        (p := p) (q := q) (σ := σ)
        (rankOneProjector (p := p) (q := q) (u : BipVector p q)) hH hF hθ_neg_abs
  have hUpper :
      (gaussianMeasure p q σ).real
          {ω | t * sampleDimension σ ≤ X ω} ≤
        Real.exp (-((1 / 8 : ℝ) * sampleDimension σ * min (t ^ 2) t)) := by
    have hchern :=
      ProbabilityTheory.measure_ge_le_exp_mul_mgf
        (μ := gaussianMeasure p q σ)
        (X := X)
        (ε := t * sampleDimension σ) hθ_nonneg hIntPos
    have hmgf :
        ProbabilityTheory.mgf X (gaussianMeasure p q σ) θ ≤
          Real.exp (2 * sampleDimension σ * θ ^ 2) := by
      simpa [X, H] using
        canonicalCenteredQuadraticFormSum_mgf_bound
          (p := p) (q := q) (σ := σ)
          (rankOneProjector (p := p) (q := q) (u : BipVector p q)) hH hF hθ_abs
    calc
      (gaussianMeasure p q σ).real
          {ω | t * sampleDimension σ ≤ X ω} ≤
          Real.exp (-(θ * (t * sampleDimension σ))) *
            ProbabilityTheory.mgf X (gaussianMeasure p q σ) θ := by
              simpa [mul_assoc] using hchern
      _ ≤ Real.exp (-(θ * (t * sampleDimension σ))) *
            Real.exp (2 * sampleDimension σ * θ ^ 2) := by
              gcongr
      _ = Real.exp (sampleDimension σ * (-(θ * t) + 2 * θ ^ 2)) := by
            rw [← Real.exp_add]
            congr 1
            ring
      _ ≤ Real.exp (-((1 / 8 : ℝ) * sampleDimension σ * min (t ^ 2) t)) := by
            apply Real.exp_le_exp.mpr
            have hscaled :
                (1 / 8 : ℝ) * sampleDimension σ * min (t ^ 2) t ≤
                  sampleDimension σ * (θ * t - 2 * θ ^ 2) := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using
                mul_le_mul_of_nonneg_left hgain hs_nonneg
            nlinarith
  have hLower :
      (gaussianMeasure p q σ).real
          {ω | X ω ≤ -(t * sampleDimension σ)} ≤
        Real.exp (-((1 / 8 : ℝ) * sampleDimension σ * min (t ^ 2) t)) := by
    have hchern :=
      ProbabilityTheory.measure_le_le_exp_mul_mgf
        (μ := gaussianMeasure p q σ)
        (X := X)
        (ε := -(t * sampleDimension σ)) (by linarith : -θ ≤ 0) hIntNeg
    have hmgf :
        ProbabilityTheory.mgf X (gaussianMeasure p q σ) (-θ) ≤
          Real.exp (2 * sampleDimension σ * θ ^ 2) := by
      rw [ProbabilityTheory.mgf]
      have := canonicalCenteredQuadraticFormSum_mgf_bound
        (p := p) (q := q) (σ := σ)
        (rankOneProjector (p := p) (q := q) (u : BipVector p q)) hH hF hθ_neg_abs
      simpa [X, neg_mul, mul_comm, mul_left_comm, mul_assoc] using this
    calc
      (gaussianMeasure p q σ).real
          {ω | X ω ≤ -(t * sampleDimension σ)} ≤
          Real.exp (-(-θ) * (-(t * sampleDimension σ))) *
            ProbabilityTheory.mgf X (gaussianMeasure p q σ) (-θ) := hchern
      _ ≤ Real.exp (-(-θ) * (-(t * sampleDimension σ))) *
            Real.exp (2 * sampleDimension σ * θ ^ 2) := by
              gcongr
      _ = Real.exp (-(sampleDimension σ * (θ * t - 2 * θ ^ 2))) := by
            rw [← Real.exp_add]
            congr 1
            ring_nf
      _ ≤ Real.exp (-((1 / 8 : ℝ) * sampleDimension σ * min (t ^ 2) t)) := by
            apply Real.exp_le_exp.mpr
            have hscaled :
                (1 / 8 : ℝ) * sampleDimension σ * min (t ^ 2) t ≤
                  sampleDimension σ * (θ * t - 2 * θ ^ 2) := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using
                mul_le_mul_of_nonneg_left hgain hs_nonneg
            nlinarith
  have hAbsSubset :
      {ω | t * sampleDimension σ ≤ |X ω|} ⊆
        {ω | t * sampleDimension σ ≤ X ω} ∪
        {ω | X ω ≤ -(t * sampleDimension σ)} := by
    intro ω hω
    by_cases hsum : 0 ≤ X ω
    · left
      simpa [abs_of_nonneg hsum] using hω
    · right
      have hneg : t * sampleDimension σ ≤ -X ω := by
        simpa [abs_of_neg (lt_of_not_ge hsum)] using hω
      have hlt : X ω < 0 := lt_of_not_ge hsum
      have hneg' := neg_le_neg hneg
      simpa [neg_neg] using hneg'
  calc
    (gaussianMeasure p q σ).real
        {ω | t * sampleDimension σ ≤ |X ω|} ≤
        (gaussianMeasure p q σ).real
          ({ω | t * sampleDimension σ ≤ X ω} ∪
            {ω | X ω ≤ -(t * sampleDimension σ)}) := by
            exact measureReal_mono
              (h₂ := (measure_lt_top (gaussianMeasure p q σ) _).ne) hAbsSubset
    _ ≤ (gaussianMeasure p q σ).real
          {ω | t * sampleDimension σ ≤ X ω} +
        (gaussianMeasure p q σ).real {ω | X ω ≤ -(t * sampleDimension σ)} := by
            exact measureReal_union_le _ _
    _ ≤ Real.exp (-((1 / 8 : ℝ) * sampleDimension σ * min (t ^ 2) t)) +
        Real.exp (-((1 / 8 : ℝ) * sampleDimension σ * min (t ^ 2) t)) := by
          gcongr
    _ = 2 * Real.exp (-(((1 / 8 : ℝ) * sampleDimension σ * min (t ^ 2) t))) := by
          ring

/-! ## Block 5: General Hermitian Concentration and Mass Tails -/

omit [DecidableEq p] [DecidableEq q] in
/-- The Gaussian mass `T = ‖G‖₂²` is the sum of the squared norms of the
independent Gaussian columns. -/
theorem gaussianMass_eq_sum_gaussianColumn_normSq
    (ω : Ω p q σ) :
    gaussianMass p q σ ω =
      ∑ α : σ, ‖gaussianColumn p q σ α ω‖ ^ 2 := by
  classical
  let G : SampleMatrix p q σ := gaussianMatrix p q σ ω
  change ‖G‖ ^ 2 = ∑ α : σ, ‖gaussianColumn p q σ α ω‖ ^ 2
  rw [Matrix.frobenius_norm_def]
  rw [← Real.sqrt_eq_rpow]
  rw [Real.sq_sqrt]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro α hα
    rw [EuclideanSpace.norm_sq_eq]
    simp [G, gaussianColumn, GaussianModel.columnVector]
  · exact Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun α _ => by positivity

omit [DecidableEq p] [DecidableEq q] in
/-- Centering the Gaussian mass by its mean `D s` rewrites it as the sum of the
centered complex-chi-square coordinates of the Gaussian columns. -/
theorem gaussianMass_centered_rewrite
    (ω : Ω p q σ) :
    gaussianMass p q σ ω - bipartiteDimension p q * sampleDimension σ =
      ∑ α : σ, ∑ i : RandomMatrixModel.BipIndex p q,
        (‖gaussianColumn p q σ α ω i‖ ^ 2 - 1) := by
  classical
  rw [gaussianMass_eq_sum_gaussianColumn_normSq (p := p) (q := q) (σ := σ) ω]
  have hcard :
      (bipartiteDimension p q * sampleDimension σ : ℝ) =
        ∑ α : σ, ∑ i : RandomMatrixModel.BipIndex p q, (1 : ℝ) := by
    simp [bipartiteDimension, sampleDimension, Finset.sum_const, nsmul_eq_mul,
      mul_assoc, mul_comm]
  rw [hcard]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro α hα
  rw [EuclideanSpace.norm_sq_eq]
  rw [← Finset.sum_sub_distrib]

/-- Exact MGF factorization for the centered Gaussian mass. This is the
Gamma/chi-square Laplace transform of the total mass `T = ‖G‖₂²`. -/
theorem gaussianMass_centered_mgf_factorization
    {θ : ℝ} (hθ : θ < 1) :
    ∫ ω : Ω p q σ,
        Real.exp
          (θ *
            (gaussianMass p q σ ω - bipartiteDimension p q * sampleDimension σ))
          ∂gaussianMeasure p q σ =
      ∏ _α : σ, ∏ _i : RandomMatrixModel.BipIndex p q,
        Real.exp (-θ) / (1 - θ) := by
  have hprod :=
    gaussianColumn_matrixUnitary_diagonal_mgf_independent_columns
      (p := p) (q := q) (σ := σ)
      (U := (1 : unitary (BipMatrix p q))) (θ := θ)
      (h := fun _ : RandomMatrixModel.BipIndex p q => (1 : ℝ))
      (fun _ => by simpa using hθ)
  have hfun :
      (fun ω : Ω p q σ =>
        Real.exp
          (θ *
            (gaussianMass p q σ ω - bipartiteDimension p q * sampleDimension σ))) =
      fun ω : Ω p q σ =>
        Real.exp
          (θ * ∑ α : σ, ∑ i : RandomMatrixModel.BipIndex p q,
            (‖gaussianColumn p q σ α ω i‖ ^ 2 - 1)) := by
    funext ω
    rw [gaussianMass_centered_rewrite (p := p) (q := q) (σ := σ) ω]
  rw [hfun]
  simpa using hprod

/-- The lower-tail Chernoff parameter for the Gaussian mass is integrable
because its exact MGF is finite. -/
theorem gaussianMass_centered_integrable_exp_mul
    {θ : ℝ} (hθ : θ < 1) :
    Integrable
      (fun ω : Ω p q σ =>
        Real.exp
          (θ *
            (gaussianMass p q σ ω - bipartiteDimension p q * sampleDimension σ)))
      (gaussianMeasure p q σ) := by
  have hEq :=
    gaussianMass_centered_mgf_factorization
      (p := p) (q := q) (σ := σ) (θ := θ) hθ
  by_contra hnot
  rw [integral_undef hnot] at hEq
  have hpos :
      0 <
        ∏ _α : σ, ∏ _i : RandomMatrixModel.BipIndex p q,
          Real.exp (-θ) / (1 - θ) := by
    refine Finset.prod_pos ?_
    intro α hα
    refine Finset.prod_pos ?_
    intro i hi
    have hden : 0 < 1 - θ := by linarith
    exact div_pos (Real.exp_pos _) hden
  linarith

/-- Mass lower tail: with exponentially high probability, the total Gaussian
mass is at least `(1/2) D s`. -/
theorem gaussianMass_lower_tail :
    (gaussianMeasure p q σ).real
        ((gaussianMassLowerEvent (p := p) (q := q) (σ := σ) (1 / 2 : ℝ))ᶜ) ≤
      Real.exp
        (-((1 / 6 : ℝ) * bipartiteDimension p q * sampleDimension σ)) := by
  classical
  let N : ℝ := bipartiteDimension p q * sampleDimension σ
  let X : Ω p q σ → ℝ := fun ω => gaussianMass p q σ ω - N
  haveI : IsProbabilityMeasure (gaussianMeasure p q σ) := by
    rw [gaussianMeasure_eq]
    infer_instance
  have hN_nonneg : 0 ≤ N := by
    unfold N bipartiteDimension sampleDimension
    positivity
  have hInt :
      Integrable (fun ω : Ω p q σ => Real.exp ((-1 : ℝ) * X ω))
        (gaussianMeasure p q σ) := by
    simpa [X, N] using
      gaussianMass_centered_integrable_exp_mul
        (p := p) (q := q) (σ := σ) (θ := (-1 : ℝ)) (by norm_num)
  have hchern :=
    ProbabilityTheory.measure_le_le_exp_mul_mgf
      (μ := gaussianMeasure p q σ)
      (X := X) (ε := -(N / 2)) (by norm_num : (-1 : ℝ) ≤ 0) hInt
  have hmgf :
      ProbabilityTheory.mgf X (gaussianMeasure p q σ) (-1 : ℝ) =
        ∏ _α : σ, ∏ _i : RandomMatrixModel.BipIndex p q,
          Real.exp (1 : ℝ) / 2 := by
    rw [ProbabilityTheory.mgf]
    simpa [X, N, one_add_one_eq_two] using
      gaussianMass_centered_mgf_factorization
        (p := p) (q := q) (σ := σ) (θ := (-1 : ℝ)) (by norm_num)
  have hprod :
      (∏ _α : σ, ∏ _i : RandomMatrixModel.BipIndex p q,
          Real.exp (1 : ℝ) / 2) =
        Real.exp ((1 - Real.log 2) * N) := by
    have hfac : Real.exp (1 : ℝ) / 2 = Real.exp (1 - Real.log 2) := by
      rw [Real.exp_sub, Real.exp_log (by positivity : (0 : ℝ) < 2)]
    rw [hfac]
    calc
      (∏ _α : σ, ∏ _i : RandomMatrixModel.BipIndex p q, Real.exp (1 - Real.log 2))
          = ∏ _α : σ,
              Real.exp (∑ _i : RandomMatrixModel.BipIndex p q, (1 - Real.log 2)) := by
              apply Finset.prod_congr rfl
              intro α hα
              rw [← Real.exp_sum]
      _ = Real.exp
            (∑ _α : σ, ∑ _i : RandomMatrixModel.BipIndex p q, (1 - Real.log 2)) := by
            rw [← Real.exp_sum]
      _ = Real.exp ((1 - Real.log 2) * N) := by
            congr 1
            simp [N, bipartiteDimension, sampleDimension, Finset.sum_const,
              nsmul_eq_mul, mul_assoc, mul_comm]
            ring_nf
  have htail :
      (gaussianMeasure p q σ).real {ω | X ω ≤ -(N / 2)} ≤
        Real.exp (-((1 / 6 : ℝ) * N)) := by
    calc
      (gaussianMeasure p q σ).real {ω | X ω ≤ -(N / 2)} ≤
          Real.exp (-((-1 : ℝ) * (-(N / 2)))) *
            ProbabilityTheory.mgf X (gaussianMeasure p q σ) (-1 : ℝ) := by
              simpa using hchern
      _ = Real.exp (-(N / 2)) *
            ProbabilityTheory.mgf X (gaussianMeasure p q σ) (-1 : ℝ) := by
            congr 1
            ring_nf
      _ = Real.exp (-(N / 2)) *
            ∏ _α : σ, ∏ _i : RandomMatrixModel.BipIndex p q,
              Real.exp (1 : ℝ) / 2 := by rw [hmgf]
      _ = Real.exp (-(N * (Real.log 2 - 1 / 2))) := by
            rw [hprod]
            rw [← Real.exp_add]
            congr 1
            ring_nf
      _ ≤ Real.exp (-((1 / 6 : ℝ) * N)) := by
            apply Real.exp_le_exp.mpr
            have hlog' : (2 / (1 + 2 : ℝ)) < Real.log 2 := by
              simpa [one_add_one_eq_two] using
                Real.lt_log_one_add_of_pos (x := (1 : ℝ)) (by positivity)
            have hlog : (2 / 3 : ℝ) < Real.log 2 := by
              norm_num at hlog' ⊢
              exact hlog'
            have hconst : (1 / 6 : ℝ) ≤ Real.log 2 - 1 / 2 := by
              linarith
            have hscaled :
                (1 / 6 : ℝ) * N ≤ (Real.log 2 - 1 / 2) * N := by
              exact mul_le_mul_of_nonneg_right hconst hN_nonneg
            nlinarith
  have hsubset :
      ((gaussianMassLowerEvent (p := p) (q := q) (σ := σ) (1 / 2 : ℝ))ᶜ) ⊆
        {ω | X ω ≤ -(N / 2)} := by
    intro ω hω
    have hlt :
        gaussianMass p q σ ω < N / 2 := by
      have hlt' :
          gaussianMass p q σ ω <
            (1 / 2 : ℝ) * bipartiteDimension p q * sampleDimension σ := by
        simpa [gaussianMassLowerEvent] using hω
      have hhalf :
          (1 / 2 : ℝ) * bipartiteDimension p q * sampleDimension σ = N / 2 := by
        unfold N
        ring_nf
      rw [hhalf] at hlt'
      exact hlt'
    show X ω ≤ -(N / 2)
    have hltX : X ω < -(N / 2) := by
      have hsub : gaussianMass p q σ ω - N < N / 2 - N := sub_lt_sub_right hlt N
      have hhalf : N / 2 - N = -(N / 2) := by ring_nf
      simpa [X, hhalf] using hsub
    exact le_of_lt hltX
  calc
    (gaussianMeasure p q σ).real
        ((gaussianMassLowerEvent (p := p) (q := q) (σ := σ) (1 / 2 : ℝ))ᶜ) ≤
        (gaussianMeasure p q σ).real {ω | X ω ≤ -(N / 2)} := by
          exact measureReal_mono
            (h₂ := (measure_lt_top (gaussianMeasure p q σ) _).ne) hsubset
    _ ≤ Real.exp (-((1 / 6 : ℝ) * N)) := htail
    _ = Real.exp (-((1 / 6 : ℝ) * bipartiteDimension p q * sampleDimension σ)) := by
          simp [N, mul_assoc]

/-- The total Gaussian mass has a finite expectation. A convenient proof is to
dominate `T = ‖G‖₂²` by the exponential moment already controlled at
Chernoff parameter `θ = 1 / 2`. -/
theorem gaussianMass_integrable :
    Integrable (fun ω : Ω p q σ => gaussianMass p q σ ω) (gaussianMeasure p q σ) := by
  let N : ℝ := bipartiteDimension p q * sampleDimension σ
  have hIntExp :
      Integrable
        (fun ω : Ω p q σ =>
          Real.exp ((1 / 2 : ℝ) * (gaussianMass p q σ ω - N)))
        (gaussianMeasure p q σ) := by
    simpa [N] using
      gaussianMass_centered_integrable_exp_mul
        (p := p) (q := q) (σ := σ) (θ := (1 / 2 : ℝ)) (by norm_num)
  have hIntBound :
      Integrable
        (fun ω : Ω p q σ =>
          Real.exp ((1 / 2 : ℝ) * (gaussianMass p q σ ω - N)) *
            Real.exp (N / 2))
        (gaussianMeasure p q σ) :=
    hIntExp.mul_const (Real.exp (N / 2))
  have hmeasMass : Measurable (gaussianMass p q σ) := by
    classical
    rw [show gaussianMass p q σ =
        (fun ω : Ω p q σ => ∑ α : σ, ‖gaussianColumn p q σ α ω‖ ^ 2) by
          funext ω
          exact gaussianMass_eq_sum_gaussianColumn_normSq (p := p) (q := q) (σ := σ) ω]
    fun_prop
  refine hIntBound.mono' hmeasMass.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall ?_
  intro ω
  have hmass_nonneg : 0 ≤ gaussianMass p q σ ω := by
    unfold gaussianMass frobeniusMass frobeniusNorm
    positivity
  rw [Real.norm_of_nonneg hmass_nonneg]
  have hle_exp :
      gaussianMass p q σ ω ≤ Real.exp (gaussianMass p q σ ω / 2) := by
    simpa [two_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (Real.two_mul_le_exp (x := gaussianMass p q σ ω / 2))
  calc
    gaussianMass p q σ ω ≤ Real.exp (gaussianMass p q σ ω / 2) := hle_exp
    _ = Real.exp ((1 / 2 : ℝ) * (gaussianMass p q σ ω - N)) * Real.exp (N / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The second moment of a standard real Gaussian is `1`. -/
theorem integral_sq_gaussianReal_zero_one :
    ∫ x : ℝ, x ^ 2 ∂ProbabilityTheory.gaussianReal 0 1 = 1 := by
  have h :
      Var[(fun x : ℝ => x); ProbabilityTheory.gaussianReal 0 1] = (1 : ℝ) := by
    exact
      (ProbabilityTheory.variance_id_gaussianReal
        (μ := (0 : ℝ)) (v := (1 : ℝ≥0)))
  rw [variance_eq_integral measurable_id'.aemeasurable,
    ProbabilityTheory.integral_id_gaussianReal] at h
  simpa using h

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The squared Euclidean norm of a standard complex Gaussian vector is
integrable. -/
theorem standardComplexGaussianVectorMeasure_integrable_norm_sq
    {ι : Type*} [Fintype ι] :
    Integrable (fun z : EuclideanSpace ℂ ι => ‖z‖ ^ 2)
      (standardComplexGaussianVectorMeasure ι) := by
  let μ : Measure ((ι × Fin 2) → ℝ) :=
    Measure.pi (fun _ : ι × Fin 2 => ProbabilityTheory.gaussianReal 0 1)
  have hterm :
      ∀ i : ι,
        Integrable (fun x : (ι × Fin 2) → ℝ => (((x (i, 0)) ^ 2 + (x (i, 1)) ^ 2) / 2)) μ := by
    intro i
    have hsq :
        Integrable (fun x : ℝ => x ^ 2) (ProbabilityTheory.gaussianReal 0 1) := by
      simpa using
        (ProbabilityTheory.memLp_id_gaussianReal
          (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) 2).integrable_sq
    have h0 :
        Integrable (fun x : (ι × Fin 2) → ℝ => x (i, 0) ^ 2) μ := by
      simpa [μ] using
        (integrable_comp_eval
          (μ := fun _ : ι × Fin 2 => ProbabilityTheory.gaussianReal 0 1)
          (i := (i, 0)) hsq)
    have h1 :
        Integrable (fun x : (ι × Fin 2) → ℝ => x (i, 1) ^ 2) μ := by
      simpa [μ] using
        (integrable_comp_eval
          (μ := fun _ : ι × Fin 2 => ProbabilityTheory.gaussianReal 0 1)
          (i := (i, 1)) hsq)
    simpa [μ, div_eq_mul_inv, mul_add, mul_comm, mul_left_comm, mul_assoc] using
      (h0.add h1).const_mul ((1 / 2 : ℝ))
  have hsum :
      Integrable
        (fun x : (ι × Fin 2) → ℝ =>
          ∑ i : ι, (((x (i, 0)) ^ 2 + (x (i, 1)) ^ 2) / 2)) μ := by
    simpa [μ] using
      (integrable_finset_sum
        (μ := μ) (s := Finset.univ)
        (f := fun i x => (((x (i, 0)) ^ 2 + (x (i, 1)) ^ 2) / 2))
        (by intro i hi; exact hterm i))
  have hfuncomp :
      (((fun z : EuclideanSpace ℂ ι => ‖z‖ ^ 2) ∘
          complexVectorOfRealCoordinates (ι := ι)) ∘ WithLp.toLp 2) =
        fun x : (ι × Fin 2) → ℝ =>
          ∑ i : ι, (((x (i, 0)) ^ 2 + (x (i, 1)) ^ 2) / 2) := by
    funext x
    change ‖complexVectorOfRealCoordinates (ι := ι) (WithLp.toLp 2 x)‖ ^ 2 =
      ∑ i : ι, (((x (i, 0)) ^ 2 + (x (i, 1)) ^ 2) / 2)
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i hi
    exact norm_sq_complexVectorOfRealCoordinates_apply
      (x := (WithLp.toLp 2 x : ComplexRealCoordSpace ι)) i
  have hpre :
      Integrable
        ((((fun z : EuclideanSpace ℂ ι => ‖z‖ ^ 2) ∘
            complexVectorOfRealCoordinates (ι := ι)) ∘ WithLp.toLp 2)) μ := by
    rw [hfuncomp]
    exact hsum
  have hreal :
      Integrable
        (fun x : ComplexRealCoordSpace ι =>
          ‖complexVectorOfRealCoordinates (ι := ι) x‖ ^ 2)
        (ProbabilityTheory.stdGaussian (ComplexRealCoordSpace ι)) := by
    rw [← ProbabilityTheory.map_pi_eq_stdGaussian (ι := ι × Fin 2)]
    exact
      (integrable_map_measure
        (by
          have hmeas :
              Measurable
                (fun x : ComplexRealCoordSpace ι =>
                  ‖complexVectorOfRealCoordinates (ι := ι) x‖ ^ 2) := by
            fun_prop
          exact hmeas.aestronglyMeasurable)
        (by
          have hmeas : Measurable (WithLp.toLp 2 :
              ((ι × Fin 2) → ℝ) → ComplexRealCoordSpace ι) := by
            fun_prop
          exact hmeas.aemeasurable)).2
        hpre
  exact
    (integrable_map_measure
      (by
        have hmeas : Measurable (fun z : EuclideanSpace ℂ ι => ‖z‖ ^ 2) := by
          fun_prop
        exact hmeas.aestronglyMeasurable)
      ((measurable_complexVectorOfRealCoordinates ι).aemeasurable)).2 hreal

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The squared Euclidean norm of a standard complex Gaussian vector has mean
equal to the ambient complex dimension. -/
theorem standardComplexGaussianVectorMeasure_integral_norm_sq
    {ι : Type*} [Fintype ι] :
    ∫ z : EuclideanSpace ℂ ι, ‖z‖ ^ 2
      ∂standardComplexGaussianVectorMeasure ι = Fintype.card ι := by
  let μ : Measure ((ι × Fin 2) → ℝ) :=
    Measure.pi (fun _ : ι × Fin 2 => ProbabilityTheory.gaussianReal 0 1)
  have hterm_int :
      ∀ i : ι,
        Integrable (fun x : (ι × Fin 2) → ℝ => (((x (i, 0)) ^ 2 + (x (i, 1)) ^ 2) / 2)) μ := by
    intro i
    have hsq :
        Integrable (fun x : ℝ => x ^ 2) (ProbabilityTheory.gaussianReal 0 1) := by
      simpa using
        (ProbabilityTheory.memLp_id_gaussianReal
          (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) 2).integrable_sq
    have h0 :
        Integrable (fun x : (ι × Fin 2) → ℝ => x (i, 0) ^ 2) μ := by
      simpa [μ] using
        (integrable_comp_eval
          (μ := fun _ : ι × Fin 2 => ProbabilityTheory.gaussianReal 0 1)
          (i := (i, 0)) hsq)
    have h1 :
        Integrable (fun x : (ι × Fin 2) → ℝ => x (i, 1) ^ 2) μ := by
      simpa [μ] using
        (integrable_comp_eval
          (μ := fun _ : ι × Fin 2 => ProbabilityTheory.gaussianReal 0 1)
          (i := (i, 1)) hsq)
    simpa [μ, div_eq_mul_inv, mul_add, mul_comm, mul_left_comm, mul_assoc] using
      (h0.add h1).const_mul ((1 / 2 : ℝ))
  have hone :
      ∀ i : ι,
        ∫ x : (ι × Fin 2) → ℝ, (((x (i, 0)) ^ 2 + (x (i, 1)) ^ 2) / 2) ∂μ = 1 := by
    intro i
    have hsq :
        Integrable (fun x : ℝ => x ^ 2) (ProbabilityTheory.gaussianReal 0 1) := by
      simpa using
        (ProbabilityTheory.memLp_id_gaussianReal
          (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) 2).integrable_sq
    have h0int :
        Integrable (fun x : (ι × Fin 2) → ℝ => x (i, 0) ^ 2) μ := by
      simpa [μ] using
        (integrable_comp_eval
          (μ := fun _ : ι × Fin 2 => ProbabilityTheory.gaussianReal 0 1)
          (i := (i, 0)) hsq)
    have h1int :
        Integrable (fun x : (ι × Fin 2) → ℝ => x (i, 1) ^ 2) μ := by
      simpa [μ] using
        (integrable_comp_eval
          (μ := fun _ : ι × Fin 2 => ProbabilityTheory.gaussianReal 0 1)
          (i := (i, 1)) hsq)
    have h0 :
        ∫ x : (ι × Fin 2) → ℝ, x (i, 0) ^ 2 ∂μ = 1 := by
      simpa [μ] using
        (integral_comp_eval
          (μ := fun _ : ι × Fin 2 => ProbabilityTheory.gaussianReal 0 1)
          (i := (i, 0)) (f := fun y : ℝ => y ^ 2)
          (by
            have hmeas : Measurable (fun y : ℝ => y ^ 2) := by
              fun_prop
            exact hmeas.aestronglyMeasurable))
          ▸ integral_sq_gaussianReal_zero_one
    have h1 :
        ∫ x : (ι × Fin 2) → ℝ, x (i, 1) ^ 2 ∂μ = 1 := by
      simpa [μ] using
        (integral_comp_eval
          (μ := fun _ : ι × Fin 2 => ProbabilityTheory.gaussianReal 0 1)
          (i := (i, 1)) (f := fun y : ℝ => y ^ 2)
          (by
            have hmeas : Measurable (fun y : ℝ => y ^ 2) := by
              fun_prop
            exact hmeas.aestronglyMeasurable))
          ▸ integral_sq_gaussianReal_zero_one
    calc
      ∫ x : (ι × Fin 2) → ℝ, (((x (i, 0)) ^ 2 + (x (i, 1)) ^ 2) / 2) ∂μ
          =
        ∫ x : (ι × Fin 2) → ℝ,
          (1 / 2 : ℝ) * (x (i, 0) ^ 2 + x (i, 1) ^ 2) ∂μ := by
            congr with x
            ring
      _ = (1 / 2 : ℝ) * ∫ x : (ι × Fin 2) → ℝ, (x (i, 0) ^ 2 + x (i, 1) ^ 2) ∂μ := by
            rw [integral_const_mul]
      _ = (1 / 2 : ℝ) * ((∫ x : (ι × Fin 2) → ℝ, x (i, 0) ^ 2 ∂μ) +
            (∫ x : (ι × Fin 2) → ℝ, x (i, 1) ^ 2 ∂μ)) := by
            rw [integral_add h0int h1int]
      _ = 1 := by rw [h0, h1]; ring
  have hfuncomp :
      (((fun z : EuclideanSpace ℂ ι => ‖z‖ ^ 2) ∘
          complexVectorOfRealCoordinates (ι := ι)) ∘ WithLp.toLp 2) =
        fun x : (ι × Fin 2) → ℝ =>
          ∑ i : ι, (((x (i, 0)) ^ 2 + (x (i, 1)) ^ 2) / 2) := by
    funext x
    change ‖complexVectorOfRealCoordinates (ι := ι) (WithLp.toLp 2 x)‖ ^ 2 =
      ∑ i : ι, (((x (i, 0)) ^ 2 + (x (i, 1)) ^ 2) / 2)
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i hi
    exact norm_sq_complexVectorOfRealCoordinates_apply
      (x := (WithLp.toLp 2 x : ComplexRealCoordSpace ι)) i
  have hpi :
      ∫ x : (ι × Fin 2) → ℝ,
        (((fun z : EuclideanSpace ℂ ι => ‖z‖ ^ 2) ∘
            complexVectorOfRealCoordinates (ι := ι)) ∘ WithLp.toLp 2) x ∂μ =
        Fintype.card ι := by
    rw [hfuncomp]
    have hsum :
        ∫ x : (ι × Fin 2) → ℝ,
          ∑ i : ι, (((x (i, 0)) ^ 2 + (x (i, 1)) ^ 2) / 2) ∂μ
          =
        ∑ i : ι, ∫ x : (ι × Fin 2) → ℝ, (((x (i, 0)) ^ 2 + (x (i, 1)) ^ 2) / 2) ∂μ := by
      simpa [μ] using
        (integral_finset_sum
          (μ := μ) (s := Finset.univ)
          (f := fun i x => (((x (i, 0)) ^ 2 + (x (i, 1)) ^ 2) / 2))
          (by intro i hi; exact hterm_int i))
    rw [hsum]
    calc
      (∑ i : ι, ∫ x : (ι × Fin 2) → ℝ, (((x (i, 0)) ^ 2 + (x (i, 1)) ^ 2) / 2) ∂μ)
          = ∑ i : ι, (1 : ℝ) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact hone i
      _ = Fintype.card ι := by simp
  have hreal :
      ∫ x : ComplexRealCoordSpace ι,
        ‖complexVectorOfRealCoordinates (ι := ι) x‖ ^ 2
        ∂ProbabilityTheory.stdGaussian (ComplexRealCoordSpace ι) = Fintype.card ι := by
    rw [← ProbabilityTheory.map_pi_eq_stdGaussian (ι := ι × Fin 2)]
    calc
      ∫ x : ComplexRealCoordSpace ι,
          ‖complexVectorOfRealCoordinates (ι := ι) x‖ ^ 2
          ∂Measure.map (WithLp.toLp 2) μ
          =
        ∫ x : (ι × Fin 2) → ℝ,
          (((fun z : EuclideanSpace ℂ ι => ‖z‖ ^ 2) ∘
              complexVectorOfRealCoordinates (ι := ι)) ∘ WithLp.toLp 2) x ∂μ := by
            exact integral_map
              (μ := μ)
              (φ := (WithLp.toLp 2 : ((ι × Fin 2) → ℝ) → ComplexRealCoordSpace ι))
              (by
                have hmeas : Measurable (WithLp.toLp 2 :
                    ((ι × Fin 2) → ℝ) → ComplexRealCoordSpace ι) := by
                  fun_prop
                exact hmeas.aemeasurable)
              (by
                have hmeas :
                    Measurable
                      (fun x : ComplexRealCoordSpace ι =>
                        ‖complexVectorOfRealCoordinates (ι := ι) x‖ ^ 2) := by
                  fun_prop
                exact hmeas.aestronglyMeasurable)
      _ = Fintype.card ι := hpi
  unfold standardComplexGaussianVectorMeasure
  calc
    ∫ z : EuclideanSpace ℂ ι, ‖z‖ ^ 2
        ∂Measure.map (complexVectorOfRealCoordinates (ι := ι))
          (ProbabilityTheory.stdGaussian (ComplexRealCoordSpace ι))
        =
      ∫ x : ComplexRealCoordSpace ι,
        ‖complexVectorOfRealCoordinates (ι := ι) x‖ ^ 2
        ∂ProbabilityTheory.stdGaussian (ComplexRealCoordSpace ι) := by
          exact integral_map
            (μ := ProbabilityTheory.stdGaussian (ComplexRealCoordSpace ι))
            (φ := complexVectorOfRealCoordinates (ι := ι))
            ((measurable_complexVectorOfRealCoordinates ι).aemeasurable)
            (by
              have hmeas : Measurable (fun z : EuclideanSpace ℂ ι => ‖z‖ ^ 2) := by
                fun_prop
              exact hmeas.aestronglyMeasurable)
    _ = Fintype.card ι := hreal

omit [DecidableEq p] [DecidableEq q] in
/-- The squared norm of each concrete Gaussian column is integrable. -/
theorem gaussianColumn_integrable_norm_sq (α : σ) :
    Integrable
      (fun ω : Ω p q σ => ‖gaussianColumn p q σ α ω‖ ^ 2)
      (gaussianMeasure p q σ) := by
  have hstd :
      Integrable
        (fun z : EuclideanSpace ℂ (RandomMatrixModel.BipIndex p q) => ‖z‖ ^ 2)
        (Measure.map (gaussianColumn p q σ α) (gaussianMeasure p q σ)) := by
    rw [gaussianColumn_map_gaussianMeasure (p := p) (q := q) (σ := σ) α]
    exact standardComplexGaussianVectorMeasure_integrable_norm_sq
      (ι := RandomMatrixModel.BipIndex p q)
  exact
    (integrable_map_measure
      (by fun_prop :
        AEStronglyMeasurable
          (fun z : EuclideanSpace ℂ (RandomMatrixModel.BipIndex p q) => ‖z‖ ^ 2)
          (Measure.map (gaussianColumn p q σ α) (gaussianMeasure p q σ)))
      ((measurable_gaussianColumn (p := p) (q := q) (σ := σ) α).aemeasurable)).mp hstd

omit [DecidableEq p] [DecidableEq q] in
/-- The mean squared norm of each concrete Gaussian column is the bipartite
dimension `D`. -/
theorem gaussianColumn_integral_norm_sq (α : σ) :
    ∫ ω : Ω p q σ, ‖gaussianColumn p q σ α ω‖ ^ 2
      ∂gaussianMeasure p q σ = bipartiteDimension p q := by
  calc
    ∫ ω : Ω p q σ, ‖gaussianColumn p q σ α ω‖ ^ 2
        ∂gaussianMeasure p q σ
        =
      ∫ z : EuclideanSpace ℂ (RandomMatrixModel.BipIndex p q), ‖z‖ ^ 2
        ∂Measure.map (gaussianColumn p q σ α) (gaussianMeasure p q σ) := by
          exact (integral_map
            ((measurable_gaussianColumn (p := p) (q := q) (σ := σ) α).aemeasurable)
            (by fun_prop :
              AEStronglyMeasurable
                (fun z : EuclideanSpace ℂ (RandomMatrixModel.BipIndex p q) => ‖z‖ ^ 2)
                (Measure.map (gaussianColumn p q σ α) (gaussianMeasure p q σ)))).symm
    _ =
      ∫ z : EuclideanSpace ℂ (RandomMatrixModel.BipIndex p q), ‖z‖ ^ 2
        ∂standardComplexGaussianVectorMeasure (RandomMatrixModel.BipIndex p q) := by
          rw [gaussianColumn_map_gaussianMeasure (p := p) (q := q) (σ := σ) α]
    _ = bipartiteDimension p q := by
          simpa [bipartiteDimension] using
            (standardComplexGaussianVectorMeasure_integral_norm_sq
              (ι := RandomMatrixModel.BipIndex p q))

omit [DecidableEq p] [DecidableEq q] in
/-- Exact expectation formula for the total Gaussian mass:
`E(R^2) = E‖G‖₂² = D s`. -/
theorem gaussianMass_integral_eq :
    ∫ ω : Ω p q σ, gaussianMass p q σ ω ∂gaussianMeasure p q σ =
      bipartiteDimension p q * sampleDimension σ := by
  classical
  rw [show (fun ω : Ω p q σ => gaussianMass p q σ ω) =
      fun ω => ∑ α : σ, ‖gaussianColumn p q σ α ω‖ ^ 2 by
        funext ω
        exact gaussianMass_eq_sum_gaussianColumn_normSq (p := p) (q := q) (σ := σ) ω]
  rw [integral_finset_sum]
  · calc
      (∑ x : σ, ∫ a : Ω p q σ, ‖gaussianColumn p q σ x a‖ ^ 2 ∂gaussianMeasure p q σ)
          = ∑ x : σ, bipartiteDimension p q := by
              apply Finset.sum_congr rfl
              intro x hx
              exact gaussianColumn_integral_norm_sq (p := p) (q := q) (σ := σ) x
      _ = bipartiteDimension p q * sampleDimension σ := by
            simp [bipartiteDimension, sampleDimension, Finset.sum_const,
              nsmul_eq_mul, mul_assoc, mul_comm]
  · intro α hα
    exact gaussianColumn_integrable_norm_sq (p := p) (q := q) (σ := σ) α

omit [DecidableEq p] [DecidableEq q] in
/-- Concrete no-input positivity of the quadratic radial mean
`E(R^2) = E‖G‖₂²`, under the only nondegeneracy assumptions really needed:
positive ambient dimension and at least one sample column. -/
theorem gaussianMass_expectation_pos
    (hD : 0 < bipartiteDimension p q) (hs : 0 < sampleDimension σ) :
    0 < ∫ ω : Ω p q σ, gaussianMass p q σ ω ∂gaussianMeasure p q σ := by
  rw [gaussianMass_integral_eq (p := p) (q := q) (σ := σ)]
  positivity

omit [Fintype σ] in
/-! ## Block 6: Operator-Norm Lifts and Lipschitz Control -/

/-- The operator norm of a bipartite matrix is bounded by its Frobenius norm. -/
theorem opNorm_le_frobeniusNorm (A : BipMatrix p q) :
    opNorm A ≤ frobeniusNorm (p := p) (q := q) (σ := RandomMatrixModel.BipIndex p q) A := by
  unfold opNorm frobeniusNorm
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  intro x
  have hmul :
      ‖A * Matrix.replicateCol (Fin 1) (WithLp.ofLp x)‖ ≤
        ‖A‖ * ‖Matrix.replicateCol (Fin 1) (WithLp.ofLp x)‖ := by
    simpa using Matrix.frobenius_norm_mul A
      (Matrix.replicateCol (Fin 1) (WithLp.ofLp x))
  have hleft :
      ‖A * Matrix.replicateCol (Fin 1) (WithLp.ofLp x)‖ =
        ‖Matrix.toEuclideanCLM (n := RandomMatrixModel.BipIndex p q) (𝕜 := ℂ) A x‖ := by
    have hrep :
        A * Matrix.replicateCol (Fin 1) (WithLp.ofLp x) =
          Matrix.replicateCol (Fin 1) (A *ᵥ WithLp.ofLp x) := by
      ext i j
      fin_cases j
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    have hrepnorm : ‖A * Matrix.replicateCol (Fin 1) (WithLp.ofLp x)‖ =
        ‖Matrix.replicateCol (Fin 1) (A *ᵥ WithLp.ofLp x)‖ := by
      rw [hrep]
    have hcol :
        ‖Matrix.replicateCol (Fin 1) (A *ᵥ WithLp.ofLp x)‖ =
          ‖WithLp.toLp 2 (A *ᵥ WithLp.ofLp x)‖ := by
      change ‖Matrix.replicateCol (Fin 1) (A *ᵥ WithLp.ofLp x)‖ =
        ‖WithLp.toLp 2 (A *ᵥ WithLp.ofLp x)‖
      exact Matrix.frobenius_norm_replicateCol (ι := Fin 1) (v := A *ᵥ WithLp.ofLp x)
    have hvec :
        WithLp.toLp 2 (A *ᵥ WithLp.ofLp x) =
          Matrix.toEuclideanCLM (n := RandomMatrixModel.BipIndex p q) (𝕜 := ℂ) A x := by
      simpa using
        (Matrix.toEuclideanCLM_toLp
          (n := RandomMatrixModel.BipIndex p q) (𝕜 := ℂ) A (WithLp.ofLp x)).symm
    exact hrepnorm.trans (hcol.trans (by rw [hvec]))
  have hright :
      ‖Matrix.replicateCol (Fin 1) (WithLp.ofLp x)‖ = ‖x‖ := by
    calc
      ‖Matrix.replicateCol (Fin 1) (WithLp.ofLp x)‖ = ‖WithLp.toLp 2 (WithLp.ofLp x)‖ := by
        exact Matrix.frobenius_norm_replicateCol (ι := Fin 1) (v := WithLp.ofLp x)
      _ = ‖x‖ := by rw [WithLp.toLp_ofLp]
  have hmul' := hmul
  rw [hleft, hright] at hmul'
  exact hmul'

/-- A unit-vector rank-one projector has operator norm at most `1`. -/
theorem rankOneProjector_opNorm_le_one_unit
    (u : Metric.sphere (0 : BipVector p q) 1) :
    opNorm (rankOneProjector (p := p) (q := q) (u : BipVector p q)) ≤ 1 := by
  calc
    opNorm (rankOneProjector (p := p) (q := q) (u : BipVector p q)) ≤
        frobeniusNorm (p := p) (q := q) (σ := RandomMatrixModel.BipIndex p q)
          (rankOneProjector (p := p) (q := q) (u : BipVector p q)) := by
            exact opNorm_le_frobeniusNorm
              (p := p) (q := q)
              (A := rankOneProjector (p := p) (q := q) (u : BipVector p q))
    _ = 1 := rankOneProjector_frobeniusNorm_unit (p := p) (q := q) u

omit [DecidableEq p] [DecidableEq q] in
/-- The operator norm of a rectangular sample matrix is bounded by its
Frobenius norm. -/
theorem sampleOpNorm_le_frobeniusNorm (G : SampleMatrix p q σ) :
    sampleOpNorm (p := p) (q := q) (σ := σ) G ≤
      frobeniusNorm (p := p) (q := q) (σ := σ) G := by
  haveI : DecidableEq σ := Classical.decEq σ
  unfold sampleOpNorm frobeniusNorm
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  intro x
  have hmul :
      ‖G * Matrix.replicateCol (Fin 1) (WithLp.ofLp x)‖ ≤
        ‖G‖ * ‖Matrix.replicateCol (Fin 1) (WithLp.ofLp x)‖ := by
    simpa using Matrix.frobenius_norm_mul G
      (Matrix.replicateCol (Fin 1) (WithLp.ofLp x))
  have hrep :
      G * Matrix.replicateCol (Fin 1) (WithLp.ofLp x) =
        Matrix.replicateCol (Fin 1) (G *ᵥ WithLp.ofLp x) := by
    ext i j
    fin_cases j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hcol :
      ‖Matrix.replicateCol (Fin 1) (G *ᵥ WithLp.ofLp x)‖ =
        ‖WithLp.toLp 2 (G *ᵥ WithLp.ofLp x)‖ := by
    exact Matrix.frobenius_norm_replicateCol (ι := Fin 1)
      (v := G *ᵥ WithLp.ofLp x)
  have hvec :
      WithLp.toLp 2 (G *ᵥ WithLp.ofLp x) =
        (Matrix.toEuclideanLin (𝕜 := ℂ) (m := RandomMatrixModel.BipIndex p q)
          (n := σ) G) x := by
    simpa using
      (Matrix.toLpLin_apply (p := 2) (q := 2) (M := G) (v := x))
  have hright :
      ‖Matrix.replicateCol (Fin 1) (WithLp.ofLp x)‖ = ‖x‖ := by
    calc
      ‖Matrix.replicateCol (Fin 1) (WithLp.ofLp x)‖ =
          ‖WithLp.toLp 2 (WithLp.ofLp x)‖ := by
            exact Matrix.frobenius_norm_replicateCol (ι := Fin 1)
              (v := WithLp.ofLp x)
      _ = ‖x‖ := by rw [WithLp.toLp_ofLp]
  calc
    ‖(Matrix.toEuclideanLin (𝕜 := ℂ) (m := RandomMatrixModel.BipIndex p q)
        (n := σ) G) x‖
        = ‖WithLp.toLp 2 (G *ᵥ WithLp.ofLp x)‖ := by rw [hvec]
    _ = ‖Matrix.replicateCol (Fin 1) (G *ᵥ WithLp.ofLp x)‖ := by rw [← hcol]
    _ ≤ ‖G‖ * ‖Matrix.replicateCol (Fin 1) (WithLp.ofLp x)‖ := by
          simpa [hrep] using hmul
    _ = frobeniusNorm (p := p) (q := q) (σ := σ) G * ‖x‖ := by
          rw [hright]
          rfl

omit [DecidableEq p] [DecidableEq q] in
/-- Rectangular quarter-net lift for the sample operator norm.  If a
`(1 / 4)`-net of the domain unit sphere controls all vectors `‖G u‖` by `B`,
then it controls the full operator norm by `2 B`. -/
theorem sampleOpNorm_le_two_mul_of_forall_quarterNet_bound
    [Nonempty σ] [DecidableEq σ]
    (G : SampleMatrix p q σ)
    {N : Set (Metric.sphere (0 : EuclideanSpace ℂ σ) 1)}
    {B : ℝ} (hB : 0 ≤ B)
    (hnet :
      ∀ x : Metric.sphere (0 : EuclideanSpace ℂ σ) 1,
        ∃ u ∈ N, ‖(x : EuclideanSpace ℂ σ) - (u : EuclideanSpace ℂ σ)‖ ≤
          (1 / 4 : ℝ))
    (hbound :
      ∀ u ∈ N,
        ‖(Matrix.toEuclideanLin (𝕜 := ℂ) (m := RandomMatrixModel.BipIndex p q)
            (n := σ) G) (u : EuclideanSpace ℂ σ)‖ ≤ B) :
    sampleOpNorm (p := p) (q := q) (σ := σ) G ≤ 2 * B := by
  let T : EuclideanSpace ℂ σ →L[ℂ] EuclideanSpace ℂ (RandomMatrixModel.BipIndex p q) :=
    LinearMap.toContinuousLinearMap
      (Matrix.toEuclideanLin (𝕜 := ℂ) (m := RandomMatrixModel.BipIndex p q)
        (n := σ) G)
  have hC_nonneg : 0 ≤ B + ‖T‖ / 4 := by
    positivity
  have hstep : ‖T‖ ≤ B + ‖T‖ / 4 := by
    refine ContinuousLinearMap.opNorm_le_bound T hC_nonneg ?_
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · have hxnorm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      let r : ℝ := ‖x‖
      have hrpos : 0 < r := by
        simpa [r] using hxnorm_pos
      let x₁ : Metric.sphere (0 : EuclideanSpace ℂ σ) 1 :=
        ⟨((r⁻¹ : ℂ) • x), by simpa [r] using norm_smul_inv_norm hx⟩
      rcases hnet x₁ with ⟨u, huN, hxu⟩
      have hdiff :
          ‖T ((x₁ : EuclideanSpace ℂ σ) - (u : EuclideanSpace ℂ σ))‖ ≤
            ‖T‖ / 4 := by
        have hdiff₀ :
            ‖T ((x₁ : EuclideanSpace ℂ σ) - (u : EuclideanSpace ℂ σ))‖ ≤
              ‖T‖ *
                ‖(x₁ : EuclideanSpace ℂ σ) - (u : EuclideanSpace ℂ σ)‖ :=
          T.le_opNorm _
        nlinarith [hdiff₀, hxu, norm_nonneg T]
      have hx₁_bound : ‖T (x₁ : EuclideanSpace ℂ σ)‖ ≤ B + ‖T‖ / 4 := by
        calc
          ‖T (x₁ : EuclideanSpace ℂ σ)‖ =
              ‖T ((u : EuclideanSpace ℂ σ) +
                ((x₁ : EuclideanSpace ℂ σ) - (u : EuclideanSpace ℂ σ)))‖ := by
                congr 1
                abel_nf
          _ = ‖T (u : EuclideanSpace ℂ σ) +
                T ((x₁ : EuclideanSpace ℂ σ) - (u : EuclideanSpace ℂ σ))‖ := by
                rw [map_add]
          _ ≤ ‖T (u : EuclideanSpace ℂ σ)‖ +
                ‖T ((x₁ : EuclideanSpace ℂ σ) - (u : EuclideanSpace ℂ σ))‖ :=
                norm_add_le _ _
          _ ≤ B + ‖T‖ / 4 := by
                have hu_bound : ‖T (u : EuclideanSpace ℂ σ)‖ ≤ B := by
                  simpa [T] using hbound u huN
                linarith
      have hx_decomp : x = (r : ℂ) • (x₁ : EuclideanSpace ℂ σ) := by
        dsimp [x₁]
        have hrne : (r : ℂ) ≠ 0 := by
          exact_mod_cast (ne_of_gt hrpos)
        have hscalar : (r : ℂ) * (r⁻¹ : ℂ) = 1 := mul_inv_cancel₀ hrne
        calc
          x = (1 : ℂ) • x := by simp
          _ = ((r : ℂ) * (r⁻¹ : ℂ)) • x := by rw [hscalar]
          _ = (r : ℂ) • ((r⁻¹ : ℂ) • x) := by rw [smul_smul]
      calc
        ‖T x‖ = ‖T ((r : ℂ) • (x₁ : EuclideanSpace ℂ σ))‖ := by
          rw [hx_decomp]
        _ = ‖(r : ℂ) • T (x₁ : EuclideanSpace ℂ σ)‖ := by
          rw [map_smul]
        _ = r * ‖T (x₁ : EuclideanSpace ℂ σ)‖ := by
          rw [norm_smul]
          simp [abs_of_nonneg hrpos.le]
        _ ≤ r * (B + ‖T‖ / 4) := by
          exact mul_le_mul_of_nonneg_left hx₁_bound hrpos.le
        _ = (B + ‖T‖ / 4) * ‖x‖ := by
          simp [r, mul_comm]
  have hmain : ‖T‖ ≤ 2 * B := by
    nlinarith [hstep, norm_nonneg T, hB]
  simpa [sampleOpNorm, T] using hmain

omit [DecidableEq p] [DecidableEq q] in
/-- If the sample index type is empty, the rectangular sample operator norm
vanishes. -/
theorem sampleOpNorm_zero_of_isEmpty
    [IsEmpty σ] (G : SampleMatrix p q σ) :
    sampleOpNorm (p := p) (q := q) (σ := σ) G = 0 := by
  have hG : G = 0 := by
    ext i j
    exact isEmptyElim j
  apply le_antisymm
  · calc
      sampleOpNorm (p := p) (q := q) (σ := σ) G ≤
          frobeniusNorm (p := p) (q := q) (σ := σ) G :=
          sampleOpNorm_le_frobeniusNorm (p := p) (q := q) (σ := σ) G
      _ = 0 := by simp [frobeniusNorm, hG]
  · unfold sampleOpNorm
    positivity

omit [DecidableEq p] [DecidableEq q] in
/-- The rectangular sample operator norm is Lipschitz with respect to the
Frobenius norm. -/
theorem sampleOpNorm_sub_lipschitz (A B : SampleMatrix p q σ) :
    |sampleOpNorm (p := p) (q := q) (σ := σ) A -
       sampleOpNorm (p := p) (q := q) (σ := σ) B| ≤
      frobeniusNorm (p := p) (q := q) (σ := σ) (A - B) := by
  classical
  haveI : DecidableEq σ := Classical.decEq σ
  let TA : EuclideanSpace ℂ σ →L[ℂ] EuclideanSpace ℂ (RandomMatrixModel.BipIndex p q) :=
    LinearMap.toContinuousLinearMap
      (Matrix.toEuclideanLin (𝕜 := ℂ) (m := RandomMatrixModel.BipIndex p q) (n := σ) A)
  let TB : EuclideanSpace ℂ σ →L[ℂ] EuclideanSpace ℂ (RandomMatrixModel.BipIndex p q) :=
    LinearMap.toContinuousLinearMap
      (Matrix.toEuclideanLin (𝕜 := ℂ) (m := RandomMatrixModel.BipIndex p q) (n := σ) B)
  let TAB : EuclideanSpace ℂ σ →L[ℂ] EuclideanSpace ℂ (RandomMatrixModel.BipIndex p q) :=
    LinearMap.toContinuousLinearMap
      (Matrix.toEuclideanLin (𝕜 := ℂ) (m := RandomMatrixModel.BipIndex p q)
        (n := σ) (A - B))
  have hnorm : |‖TA‖ - ‖TB‖| ≤ ‖TA - TB‖ := abs_norm_sub_norm_le TA TB
  have hclm : TA - TB = TAB := by
    ext x i
    simp [TA, TB, TAB]
  have hsub :
      ‖TA - TB‖ = sampleOpNorm (p := p) (q := q) (σ := σ) (A - B) := by
    rw [hclm]
    rfl
  calc
    |sampleOpNorm (p := p) (q := q) (σ := σ) A -
       sampleOpNorm (p := p) (q := q) (σ := σ) B|
        = |‖TA‖ - ‖TB‖| := by rfl
    _ ≤ ‖TA - TB‖ := hnorm
    _ = sampleOpNorm (p := p) (q := q) (σ := σ) (A - B) := hsub
    _ ≤ frobeniusNorm (p := p) (q := q) (σ := σ) (A - B) :=
          sampleOpNorm_le_frobeniusNorm (p := p) (q := q) (σ := σ) (A - B)

omit [DecidableEq p] [DecidableEq q] in
/-- Continuity of the rectangular sample operator norm as a function of the
sample matrix. -/
theorem sampleOpNorm_continuous :
    Continuous (fun G : SampleMatrix p q σ =>
      sampleOpNorm (p := p) (q := q) (σ := σ) G) := by
  classical
  haveI : DecidableEq σ := Classical.decEq σ
  refine (LipschitzWith.of_dist_le' (K := (1 : ℝ≥0)) ?_).continuous
  intro A B
  have h := sampleOpNorm_sub_lipschitz (p := p) (q := q) (σ := σ) A B
  simpa [Real.dist_eq, frobeniusNorm, one_mul, dist_eq_norm] using h

omit [DecidableEq p] [DecidableEq q] in
/-- The Gaussian sample operator norm has finite expectation. -/
theorem sampleOpNorm_integrable :
    Integrable
      (fun ω : Ω p q σ =>
        sampleOpNorm (p := p) (q := q) (σ := σ)
          (gaussianMatrix p q σ ω))
      (gaussianMeasure p q σ) := by
  classical
  letI : DecidableEq p := Classical.decEq p
  letI : DecidableEq q := Classical.decEq q
  haveI : IsProbabilityMeasure (gaussianMeasure p q σ) := by
    rw [gaussianMeasure_eq]
    infer_instance
  have hGcont : Continuous (fun ω : Ω p q σ => gaussianMatrix p q σ ω) := by
    unfold gaussianMatrix GaussianModel.gaussianSampleMatrix
      GaussianModel.sampleMatrixOfRealCoordinates
    exact continuous_pi fun _ => continuous_pi fun _ => by fun_prop
  have hmeas :
      AEStronglyMeasurable
        (fun ω : Ω p q σ =>
          sampleOpNorm (p := p) (q := q) (σ := σ)
            (gaussianMatrix p q σ ω))
        (gaussianMeasure p q σ) := by
    exact (sampleOpNorm_continuous (p := p) (q := q) (σ := σ)).comp_aestronglyMeasurable
      hGcont.aestronglyMeasurable
  have hdom : Integrable (fun ω : Ω p q σ => gaussianMass p q σ ω + 1)
      (gaussianMeasure p q σ) :=
    (gaussianMass_integrable (p := p) (q := q) (σ := σ)).add (integrable_const 1)
  refine hdom.mono' hmeas ?_
  refine Filter.Eventually.of_forall ?_
  intro ω
  have hsample_nonneg :
      0 ≤ sampleOpNorm (p := p) (q := q) (σ := σ)
        (gaussianMatrix p q σ ω) := by
    unfold sampleOpNorm
    positivity
  rw [Real.norm_of_nonneg hsample_nonneg]
  have hle_frob :=
    sampleOpNorm_le_frobeniusNorm (p := p) (q := q) (σ := σ)
      (gaussianMatrix p q σ ω)
  have hfrob_le :
      frobeniusNorm (p := p) (q := q) (σ := σ)
          (gaussianMatrix p q σ ω) ≤ gaussianMass p q σ ω + 1 := by
    have hsq :
        frobeniusNorm (p := p) (q := q) (σ := σ)
            (gaussianMatrix p q σ ω) ^ 2 = gaussianMass p q σ ω := by
      simp [gaussianMass, frobeniusMass]
    nlinarith [sq_nonneg (frobeniusNorm (p := p) (q := q) (σ := σ)
      (gaussianMatrix p q σ ω))]
  exact le_trans hle_frob hfrob_le

/-- The rectangular operator norm controls Frobenius norms after right multiplication. -/
theorem sampleOpNorm_mul_frobeniusNorm_le
    (A : SampleMatrix p q σ)
    (B : Matrix σ (RandomMatrixModel.BipIndex p q) ℂ) :
    ‖A * B‖ ≤ sampleOpNorm (p := p) (q := q) (σ := σ) A * ‖B‖ := by
  classical
  haveI : DecidableEq σ := Classical.decEq σ
  let cAB : RandomMatrixModel.BipIndex p q → ℝ :=
    fun j => ‖WithLp.toLp 2 (fun i : RandomMatrixModel.BipIndex p q => (A * B) i j)‖
  let cB : RandomMatrixModel.BipIndex p q → ℝ :=
    fun j => ‖WithLp.toLp 2 (fun i : σ => B i j)‖
  have hcAB_nonneg : ∀ j, 0 ≤ cAB j := by
    intro j
    dsimp [cAB]
    positivity
  have hcB_nonneg : ∀ j, 0 ≤ cB j := by
    intro j
    dsimp [cB]
    positivity
  have hcol : ∀ j, cAB j ≤ sampleOpNorm (p := p) (q := q) (σ := σ) A * cB j := by
    intro j
    have hlin :
        ‖Matrix.toEuclideanLin (𝕜 := ℂ) (m := RandomMatrixModel.BipIndex p q) (n := σ) A
            (WithLp.toLp 2 (fun i : σ => B i j))‖ ≤
          sampleOpNorm (p := p) (q := q) (σ := σ) A *
            ‖WithLp.toLp 2 (fun i : σ => B i j)‖ := by
      simpa [sampleOpNorm] using
        ((LinearMap.toContinuousLinearMap
            (Matrix.toEuclideanLin (𝕜 := ℂ) (m := RandomMatrixModel.BipIndex p q)
              (n := σ) A)).le_opNorm
          (WithLp.toLp 2 (fun i : σ => B i j)))
    simpa [cAB, cB, Matrix.toLpLin_toLp, Matrix.mulVec,
      Matrix.mul_apply] using hlin
  have hABsq : ∀ j,
      cAB j ^ (2 : ℝ) = ∑ i : RandomMatrixModel.BipIndex p q, ‖(A * B) i j‖ ^ (2 : ℝ) := by
    intro j
    simpa [cAB] using
      (EuclideanSpace.norm_sq_eq
        (WithLp.toLp 2 (fun i : RandomMatrixModel.BipIndex p q => (A * B) i j)))
  have hBsq : ∀ j, cB j ^ (2 : ℝ) = ∑ i : σ, ‖B i j‖ ^ (2 : ℝ) := by
    intro j
    simpa [cB] using
      (EuclideanSpace.norm_sq_eq (WithLp.toLp 2 (fun i : σ => B i j)))
  have hABsum :
      ∑ j : RandomMatrixModel.BipIndex p q, cAB j ^ (2 : ℝ) =
        ∑ i : RandomMatrixModel.BipIndex p q, ∑ j : RandomMatrixModel.BipIndex p q,
          ‖(A * B) i j‖ ^ (2 : ℝ) := by
    rw [Finset.sum_comm]
    congr with j
    exact hABsq j
  have hBsum :
      ∑ j : RandomMatrixModel.BipIndex p q, cB j ^ (2 : ℝ) =
        ∑ i : σ, ∑ j : RandomMatrixModel.BipIndex p q, ‖B i j‖ ^ (2 : ℝ) := by
    rw [Finset.sum_comm]
    congr with j
    exact hBsq j
  have hAB :
      ‖A * B‖ = ‖WithLp.toLp 2 cAB‖ := by
    have hABnorm : √(∑ j : RandomMatrixModel.BipIndex p q, cAB j ^ (2 : ℝ)) =
        ‖WithLp.toLp 2 cAB‖ := by
      simpa [cAB, hcAB_nonneg] using
        (EuclideanSpace.norm_eq (WithLp.toLp 2 cAB)).symm
    have hABnorm' : (∑ j : RandomMatrixModel.BipIndex p q, cAB j ^ (2 : ℝ)) ^ (1 / 2 : ℝ) =
        ‖WithLp.toLp 2 cAB‖ := by
      rw [← Real.sqrt_eq_rpow]
      exact hABnorm
    calc
      ‖A * B‖ =
          (∑ i : RandomMatrixModel.BipIndex p q, ∑ j : RandomMatrixModel.BipIndex p q,
            ‖(A * B) i j‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
              rw [Matrix.frobenius_norm_def]
      _ = (∑ j : RandomMatrixModel.BipIndex p q, cAB j ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
            rw [hABsum]
      _ = ‖WithLp.toLp 2 cAB‖ := hABnorm'
  have hB :
      ‖B‖ = ‖WithLp.toLp 2 cB‖ := by
    have hBnorm : √(∑ j : RandomMatrixModel.BipIndex p q, cB j ^ (2 : ℝ)) =
        ‖WithLp.toLp 2 cB‖ := by
      simpa [cB, hcB_nonneg] using
        (EuclideanSpace.norm_eq (WithLp.toLp 2 cB)).symm
    have hBnorm' : (∑ j : RandomMatrixModel.BipIndex p q, cB j ^ (2 : ℝ)) ^ (1 / 2 : ℝ) =
        ‖WithLp.toLp 2 cB‖ := by
      rw [← Real.sqrt_eq_rpow]
      exact hBnorm
    calc
      ‖B‖ =
          (∑ i : σ, ∑ j : RandomMatrixModel.BipIndex p q, ‖B i j‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
              rw [Matrix.frobenius_norm_def]
      _ = (∑ j : RandomMatrixModel.BipIndex p q, cB j ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
            rw [hBsum]
      _ = ‖WithLp.toLp 2 cB‖ := hBnorm'
  have hvec :
      ‖WithLp.toLp 2 cAB‖ ≤ sampleOpNorm (p := p) (q := q) (σ := σ) A * ‖WithLp.toLp 2 cB‖ := by
    have hAnonneg : 0 ≤ sampleOpNorm (p := p) (q := q) (σ := σ) A := by
      unfold sampleOpNorm
      positivity
    have hBnonneg : 0 ≤ ‖WithLp.toLp 2 cB‖ := by
      exact norm_nonneg _
    have hconst : 0 ≤ sampleOpNorm (p := p) (q := q) (σ := σ) A * ‖WithLp.toLp 2 cB‖ :=
      mul_nonneg hAnonneg hBnonneg
    have hABsqnorm :
        ‖WithLp.toLp 2 cAB‖ ^ 2 = ∑ j : RandomMatrixModel.BipIndex p q, cAB j ^ 2 := by
      simpa [cAB] using
        (EuclideanSpace.norm_sq_eq (WithLp.toLp 2 cAB))
    have hBsqnorm :
        ‖WithLp.toLp 2 cB‖ ^ 2 = ∑ j : RandomMatrixModel.BipIndex p q, cB j ^ 2 := by
      simpa [cB] using
        (EuclideanSpace.norm_sq_eq (WithLp.toLp 2 cB))
    have hsqpoint : ∀ j : RandomMatrixModel.BipIndex p q,
        cAB j ^ 2 ≤ (sampleOpNorm (p := p) (q := q) (σ := σ) A * cB j) ^ 2 := by
      intro j
      have hAj : cAB j ≤ sampleOpNorm (p := p) (q := q) (σ := σ) A * cB j := hcol j
      have hA_nonneg : 0 ≤ sampleOpNorm (p := p) (q := q) (σ := σ) A := by
        unfold sampleOpNorm
        positivity
      have hB_nonneg : 0 ≤ cB j := hcB_nonneg j
      exact
        (sq_le_sq₀ (hcAB_nonneg j) (mul_nonneg hA_nonneg hB_nonneg)).2 hAj
    have hsq :
        ‖WithLp.toLp 2 cAB‖ ^ 2 ≤
          (sampleOpNorm (p := p) (q := q) (σ := σ) A * ‖WithLp.toLp 2 cB‖) ^ 2 := by
      calc
        ‖WithLp.toLp 2 cAB‖ ^ 2 = ∑ j : RandomMatrixModel.BipIndex p q, cAB j ^ 2 := hABsqnorm
        _ ≤ ∑ j : RandomMatrixModel.BipIndex p q,
              (sampleOpNorm (p := p) (q := q) (σ := σ) A * cB j) ^ 2 := by
            refine Finset.sum_le_sum ?_
            intro j hj
            exact hsqpoint j
        _ = sampleOpNorm (p := p) (q := q) (σ := σ) A *
              (sampleOpNorm (p := p) (q := q) (σ := σ) A * ∑ j : RandomMatrixModel.BipIndex p q,
                cB j ^ 2) := by
            simp [pow_two, Finset.mul_sum, mul_comm, mul_left_comm]
        _ = sampleOpNorm (p := p) (q := q) (σ := σ) A *
              (sampleOpNorm (p := p) (q := q) (σ := σ) A * ‖WithLp.toLp 2 cB‖ ^ 2) := by
            rw [← hBsqnorm]
        _ = (sampleOpNorm (p := p) (q := q) (σ := σ) A * ‖WithLp.toLp 2 cB‖) ^ 2 := by
            ring
    exact (sq_le_sq₀ (norm_nonneg _) hconst).1 hsq
  simpa [← hAB, ← hB] using hvec

/-- Pairwise Lipschitz estimate on the `Ω_M`-style operator-norm good set.
On the region where both sample matrices have operator norm at most `M / D`,
the partially transposed density operator norm varies at most linearly with
the Frobenius distance between the matrices. -/
theorem pairwiseLipschitz_on_OmegaM
    {M D : ℝ} :
    AppendixB.LipschitzOn
      (fun X Y : SampleMatrix p q σ => frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y))
      {X : SampleMatrix p q σ | sampleOpNorm (p := p) (q := q) (σ := σ) X ≤ M / D}
      (fun X => opNorm (gamma (densityMatrix X)))
      (2 * M / D) := by
  classical
  haveI : DecidableEq σ := Classical.decEq σ
  intro X Y hX hY
  have hX' : sampleOpNorm (p := p) (q := q) (σ := σ) X ≤ M / D := by
    simpa using hX
  have hY' : sampleOpNorm (p := p) (q := q) (σ := σ) Y ≤ M / D := by
    simpa using hY
  have hterm₁ :
      ‖X * (Xᴴ - Yᴴ)‖ ≤
        sampleOpNorm (p := p) (q := q) (σ := σ) X *
          frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) := by
    calc
      ‖X * (Xᴴ - Yᴴ)‖ ≤
          sampleOpNorm (p := p) (q := q) (σ := σ) X * ‖Xᴴ - Yᴴ‖ := by
              exact sampleOpNorm_mul_frobeniusNorm_le (p := p) (q := q) (σ := σ)
                X (Xᴴ - Yᴴ)
      _ = sampleOpNorm (p := p) (q := q) (σ := σ) X *
            frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) := by
              have hxy :
                  ‖Xᴴ - Yᴴ‖ = frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) := by
                calc
                  ‖Xᴴ - Yᴴ‖ = ‖(X - Y)ᴴ‖ := by simp
                  _ = frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) := by
                    simpa [frobeniusNorm] using (Matrix.frobenius_norm_conjTranspose (X - Y))
              rw [hxy]
  have hterm₂ :
      ‖(X - Y) * Yᴴ‖ ≤
        frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) *
          sampleOpNorm (p := p) (q := q) (σ := σ) Y := by
    calc
      ‖(X - Y) * Yᴴ‖ = ‖Y * (X - Y)ᴴ‖ := by
        have hct : (Y * (X - Y)ᴴ)ᴴ = (X - Y) * Yᴴ := by
          simp [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
        have hnorm := Matrix.frobenius_norm_conjTranspose (Y * (X - Y)ᴴ)
        have hnorm' : ‖(Y * (X - Y)ᴴ)ᴴ‖ = ‖Y * (X - Y)ᴴ‖ := by
          simpa using hnorm
        rw [← hct]
        exact hnorm'
      _ ≤ sampleOpNorm (p := p) (q := q) (σ := σ) Y *
            frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) := by
        have htmp := sampleOpNorm_mul_frobeniusNorm_le (p := p) (q := q) (σ := σ)
          Y ((X - Y)ᴴ)
        have hxy :
            ‖Xᴴ - Yᴴ‖ = frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) := by
          calc
            ‖Xᴴ - Yᴴ‖ = ‖(X - Y)ᴴ‖ := by simp
            _ = frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) := by
              simpa [frobeniusNorm] using (Matrix.frobenius_norm_conjTranspose (X - Y))
        simpa [hxy] using htmp
      _ = frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) *
          sampleOpNorm (p := p) (q := q) (σ := σ) Y := by
        ring
  have hidentity :
      X * (Xᴴ - Yᴴ) + (X - Y) * Yᴴ =
        densityMatrix X - densityMatrix Y := by
    have hraw :
        X * (Xᴴ - Yᴴ) + (X - Y) * Yᴴ = X * Xᴴ - Y * Yᴴ := by
      ext i j
      simp [Matrix.mul_apply, sub_eq_add_neg, mul_add, add_mul, mul_neg, neg_mul,
        add_left_comm, add_assoc, Finset.sum_add_distrib]
    simpa [RandomMatrixModel.densityMatrix] using hraw
  have hpair :
      ‖densityMatrix X - densityMatrix Y‖ ≤
        (sampleOpNorm (p := p) (q := q) (σ := σ) X +
          sampleOpNorm (p := p) (q := q) (σ := σ) Y) *
          frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) := by
    calc
      ‖densityMatrix X - densityMatrix Y‖
          = ‖X * (Xᴴ - Yᴴ) + (X - Y) * Yᴴ‖ := by
              rw [← hidentity]
      _ ≤ ‖X * (Xᴴ - Yᴴ)‖ + ‖(X - Y) * Yᴴ‖ := norm_add_le _ _
      _ ≤ sampleOpNorm (p := p) (q := q) (σ := σ) X *
            frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) +
            frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) *
              sampleOpNorm (p := p) (q := q) (σ := σ) Y := by
              exact add_le_add hterm₁ hterm₂
      _ = (sampleOpNorm (p := p) (q := q) (σ := σ) X +
            sampleOpNorm (p := p) (q := q) (σ := σ) Y) *
          frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) := by
              ring
  have hpairGamma :
      |opNorm (gamma (densityMatrix X)) - opNorm (gamma (densityMatrix Y))| ≤
        (sampleOpNorm (p := p) (q := q) (σ := σ) X +
          sampleOpNorm (p := p) (q := q) (σ := σ) Y) *
          frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) := by
    have habs :
        |opNorm (gamma (densityMatrix X)) - opNorm (gamma (densityMatrix Y))| ≤
          opNorm (gamma (densityMatrix X) - gamma (densityMatrix Y)) := by
      have h :=
        abs_norm_sub_norm_le
          (Matrix.toEuclideanCLM (n := RandomMatrixModel.BipIndex p q) (𝕜 := ℂ)
            (gamma (densityMatrix X)))
          (Matrix.toEuclideanCLM (n := RandomMatrixModel.BipIndex p q) (𝕜 := ℂ)
            (gamma (densityMatrix Y)))
      simpa [RandomMatrixModel.opNorm, map_sub] using h
    calc
      |opNorm (gamma (densityMatrix X)) - opNorm (gamma (densityMatrix Y))| ≤
          opNorm (gamma (densityMatrix X) - gamma (densityMatrix Y)) := habs
      _ = opNorm (gamma (densityMatrix X - densityMatrix Y)) := by
            simp [RandomMatrixModel.gamma]
      _ ≤ frobeniusNorm (p := p) (q := q) (σ := RandomMatrixModel.BipIndex p q)
            (gamma (densityMatrix X - densityMatrix Y)) := by
            exact opNorm_le_frobeniusNorm (p := p) (q := q)
              (A := gamma (densityMatrix X - densityMatrix Y))
      _ = ‖densityMatrix X - densityMatrix Y‖ := by
            change
              frobeniusNorm (p := p) (q := q) (σ := RandomMatrixModel.BipIndex p q)
                (gamma (densityMatrix X - densityMatrix Y)) =
              frobeniusNorm (p := p) (q := q) (σ := RandomMatrixModel.BipIndex p q)
                (densityMatrix X - densityMatrix Y)
            exact RandomMatrixModel.frobeniusNorm_gamma (densityMatrix X - densityMatrix Y)
      _ ≤ (sampleOpNorm (p := p) (q := q) (σ := σ) X +
          sampleOpNorm (p := p) (q := q) (σ := σ) Y) *
          frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) := hpair
  have hsum : sampleOpNorm (p := p) (q := q) (σ := σ) X +
      sampleOpNorm (p := p) (q := q) (σ := σ) Y ≤ 2 * M / D := by
    calc
      sampleOpNorm (p := p) (q := q) (σ := σ) X +
          sampleOpNorm (p := p) (q := q) (σ := σ) Y ≤
        M / D + M / D := by
          exact add_le_add hX' hY'
      _ = 2 * M / D := by
        ring
  have hnonneg : 0 ≤ frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) := by
    unfold frobeniusNorm
    positivity
  calc
    |opNorm (gamma (densityMatrix X)) - opNorm (gamma (densityMatrix Y))| ≤
        (sampleOpNorm (p := p) (q := q) (σ := σ) X +
          sampleOpNorm (p := p) (q := q) (σ := σ) Y) *
          frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) := hpairGamma
    _ ≤ (2 * M / D) * frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) := by
          exact mul_le_mul_of_nonneg_right hsum hnonneg

/-! ### Net-Lift Helper Lemmas -/

/-- The raw Wishart operator norm is bounded by the total Gaussian mass. -/
theorem rawWishartOpNorm_le_gaussianMass (ω : Ω p q σ) :
    rawWishartOpNorm p q σ ω ≤ gaussianMass p q σ ω := by
  let G : SampleMatrix p q σ := gaussianMatrix p q σ ω
  calc
    rawWishartOpNorm p q σ ω ≤
        frobeniusNorm (p := p) (q := q) (σ := RandomMatrixModel.BipIndex p q)
          (rawWishart (p := p) (q := q) (σ := σ) G) := by
          simpa [G, rawWishartOpNorm_apply] using
            opNorm_le_frobeniusNorm (p := p) (q := q)
              (A := rawWishart (p := p) (q := q) (σ := σ) G)
    _ ≤ gaussianMass p q σ ω := by
      have hmul :
          ‖G * Gᴴ‖ ≤ ‖G‖ * ‖Gᴴ‖ := Matrix.frobenius_norm_mul G Gᴴ
      have hstar : ‖Gᴴ‖ = ‖G‖ := Matrix.frobenius_norm_conjTranspose G
      calc
        frobeniusNorm (p := p) (q := q) (σ := RandomMatrixModel.BipIndex p q)
            (rawWishart (p := p) (q := q) (σ := σ) G) = ‖G * Gᴴ‖ := by
              simp [frobeniusNorm, rawWishart, RandomMatrixModel.densityMatrix]
        _ ≤ ‖G‖ * ‖Gᴴ‖ := hmul
        _ = ‖G‖ ^ 2 := by rw [hstar]; ring
        _ = gaussianMass p q σ ω := by simp [G, gaussianMass, frobeniusMass, frobeniusNorm]

/-- The raw partially transposed Wishart operator norm is bounded by the total
Gaussian mass. -/
theorem rawWishartGammaOpNorm_le_gaussianMass (ω : Ω p q σ) :
    rawWishartGammaOpNorm p q σ ω ≤ gaussianMass p q σ ω := by
  let G : SampleMatrix p q σ := gaussianMatrix p q σ ω
  calc
    rawWishartGammaOpNorm p q σ ω ≤
        frobeniusNorm (p := p) (q := q) (σ := RandomMatrixModel.BipIndex p q)
          (rawWishartGamma (p := p) (q := q) (σ := σ) G) := by
          simpa [G, rawWishartGammaOpNorm_apply] using
            opNorm_le_frobeniusNorm (p := p) (q := q)
              (A := rawWishartGamma (p := p) (q := q) (σ := σ) G)
    _ =
        frobeniusNorm (p := p) (q := q) (σ := RandomMatrixModel.BipIndex p q)
          (rawWishart (p := p) (q := q) (σ := σ) G) := by
          simp [G, rawWishartGamma]
    _ ≤ gaussianMass p q σ ω := by
      have hmul :
          ‖G * Gᴴ‖ ≤ ‖G‖ * ‖Gᴴ‖ := Matrix.frobenius_norm_mul G Gᴴ
      have hstar : ‖Gᴴ‖ = ‖G‖ := Matrix.frobenius_norm_conjTranspose G
      calc
        frobeniusNorm (p := p) (q := q) (σ := RandomMatrixModel.BipIndex p q)
            (rawWishart (p := p) (q := q) (σ := σ) G) = ‖G * Gᴴ‖ := by
              simp [frobeniusNorm, rawWishart, RandomMatrixModel.densityMatrix]
        _ ≤ ‖G‖ * ‖Gᴴ‖ := hmul
        _ = ‖G‖ ^ 2 := by rw [hstar]; ring
        _ = gaussianMass p q σ ω := by simp [G, gaussianMass, frobeniusMass, frobeniusNorm]

/-- The normalization factor `1 / s` in the Wishart matrix has norm at most `1`. -/
theorem sampleDimension_inv_norm_le_one :
    ‖((Fintype.card σ : ℂ)⁻¹)‖ ≤ (1 : ℝ) := by
  by_cases hs : Fintype.card σ = 0
  · simp [hs]
  · have hspos_nat : 0 < Fintype.card σ := Nat.pos_of_ne_zero hs
    have hspos : 0 < (Fintype.card σ : ℝ) := by exact_mod_cast hspos_nat
    have hsone : (1 : ℝ) ≤ Fintype.card σ := by exact_mod_cast hspos_nat
    have hinv : ((Fintype.card σ : ℝ)⁻¹) ≤ 1 := by
      simpa using (inv_le_inv₀ hspos zero_lt_one).2 hsone
    simpa using hinv

/-- The normalized Wishart operator norm is bounded by the total Gaussian mass. -/
theorem wishartOpNorm_le_gaussianMass (ω : Ω p q σ) :
    wishartOpNorm p q σ ω ≤ gaussianMass p q σ ω := by
  let G : SampleMatrix p q σ := gaussianMatrix p q σ ω
  calc
    wishartOpNorm p q σ ω =
        opNorm (((Fintype.card σ : ℂ)⁻¹) •
          rawWishart (p := p) (q := q) (σ := σ) G) := by
          simp [G, wishartOpNorm_apply, wishart_eq_card_inv_smul_rawWishart]
    _ = ‖((Fintype.card σ : ℂ)⁻¹)‖ *
          opNorm (rawWishart (p := p) (q := q) (σ := σ) G) := by
          rw [opNorm, map_smul, norm_smul, opNorm]
    _ ≤ opNorm (rawWishart (p := p) (q := q) (σ := σ) G) := by
          exact mul_le_of_le_one_left (norm_nonneg _)
            (sampleDimension_inv_norm_le_one (σ := σ))
    _ ≤ gaussianMass p q σ ω := by
          simpa [G, rawWishartOpNorm_apply] using
            rawWishartOpNorm_le_gaussianMass (p := p) (q := q) (σ := σ) ω

/-- The normalized partially transposed Wishart operator norm is bounded by the
total Gaussian mass. -/
theorem wishartGammaOpNorm_le_gaussianMass (ω : Ω p q σ) :
    wishartGammaOpNorm p q σ ω ≤ gaussianMass p q σ ω := by
  let G : SampleMatrix p q σ := gaussianMatrix p q σ ω
  calc
    wishartGammaOpNorm p q σ ω =
        opNorm (((Fintype.card σ : ℂ)⁻¹) •
          rawWishartGamma (p := p) (q := q) (σ := σ) G) := by
          simp [G, wishartGammaOpNorm_apply, wishartGamma_eq_card_inv_smul_rawWishartGamma]
    _ = ‖((Fintype.card σ : ℂ)⁻¹)‖ *
          opNorm (rawWishartGamma (p := p) (q := q) (σ := σ) G) := by
          rw [opNorm, map_smul, norm_smul, opNorm]
    _ ≤ opNorm (rawWishartGamma (p := p) (q := q) (σ := σ) G) := by
          exact mul_le_of_le_one_left (norm_nonneg _)
            (sampleDimension_inv_norm_le_one (σ := σ))
    _ ≤ gaussianMass p q σ ω := by
          simpa [G, rawWishartGammaOpNorm_apply] using
            rawWishartGammaOpNorm_le_gaussianMass (p := p) (q := q) (σ := σ) ω

omit [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] in
/-- Partial transpose preserves Hermitianity on the raw Wishart matrix. -/
theorem rawWishartGamma_isHermitian (G : SampleMatrix p q σ) :
    (rawWishartGamma (p := p) (q := q) (σ := σ) G).IsHermitian := by
  have hraw :
      (rawWishart (p := p) (q := q) (σ := σ) G).IsHermitian := by
    simpa [rawWishart, RandomMatrixModel.densityMatrix] using
      (Matrix.isHermitian_mul_conjTranspose_self (A := G))
  dsimp [rawWishartGamma, gamma]
  calc
    (partialTranspose (rawWishart (p := p) (q := q) (σ := σ) G))ᴴ =
        partialTranspose ((rawWishart (p := p) (q := q) (σ := σ) G)ᴴ) := by
          exact
            (partialTranspose_conjTranspose
              (M := rawWishart (p := p) (q := q) (σ := σ) G)).symm
    _ = partialTranspose (rawWishart (p := p) (q := q) (σ := σ) G) := by
          rw [hraw.eq]

omit [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] in
/-- The raw Wishart matrix is Hermitian. -/
theorem rawWishart_isHermitian (G : SampleMatrix p q σ) :
    (rawWishart (p := p) (q := q) (σ := σ) G).IsHermitian := by
  simpa [rawWishart, RandomMatrixModel.densityMatrix] using
    (Matrix.isHermitian_mul_conjTranspose_self (A := G))

omit [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] in
/-- The normalized Wishart matrix is Hermitian. -/
theorem wishart_isHermitian (G : SampleMatrix p q σ) :
    (wishart (p := p) (q := q) (σ := σ) G).IsHermitian := by
  have hraw :
      (rawWishart (p := p) (q := q) (σ := σ) G).IsHermitian :=
    rawWishart_isHermitian (p := p) (q := q) (σ := σ) G
  rw [wishart_eq_card_inv_smul_rawWishart]
  calc
    ((((Fintype.card σ : ℂ)⁻¹) • rawWishart (p := p) (q := q) (σ := σ) G))ᴴ =
        star ((Fintype.card σ : ℂ)⁻¹) •
          (rawWishart (p := p) (q := q) (σ := σ) G)ᴴ := by
            simp
    _ = ((Fintype.card σ : ℂ)⁻¹) •
          (rawWishart (p := p) (q := q) (σ := σ) G)ᴴ := by
            simp
    _ = ((Fintype.card σ : ℂ)⁻¹) •
          rawWishart (p := p) (q := q) (σ := σ) G := by
            rw [hraw.eq]

omit [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] in
/-- The normalized partially transposed Wishart matrix is Hermitian. -/
theorem wishartGamma_isHermitian (G : SampleMatrix p q σ) :
    (wishartGamma (p := p) (q := q) (σ := σ) G).IsHermitian := by
  have hrawGamma :
      (rawWishartGamma (p := p) (q := q) (σ := σ) G).IsHermitian :=
    rawWishartGamma_isHermitian (p := p) (q := q) (σ := σ) G
  rw [wishartGamma_eq_card_inv_smul_rawWishartGamma]
  calc
    ((((Fintype.card σ : ℂ)⁻¹) • rawWishartGamma (p := p) (q := q) (σ := σ) G) )ᴴ =
        star ((Fintype.card σ : ℂ)⁻¹) •
          (rawWishartGamma (p := p) (q := q) (σ := σ) G)ᴴ := by
            simp
    _ = ((Fintype.card σ : ℂ)⁻¹) •
          (rawWishartGamma (p := p) (q := q) (σ := σ) G)ᴴ := by
            simp
    _ = ((Fintype.card σ : ℂ)⁻¹) •
          rawWishartGamma (p := p) (q := q) (σ := σ) G := by
            rw [hrawGamma.eq]

/-- If there are no sample columns, then the normalized partially transposed
Wishart operator norm vanishes identically. -/
theorem wishartGammaOpNorm_zero_of_card_eq_zero
    (hs : Fintype.card σ = 0) (ω : Ω p q σ) :
    wishartGammaOpNorm p q σ ω = 0 := by
  simp [wishartGammaOpNorm, RandomMatrixModel.wishartGamma, RandomMatrixModel.wishart,
    RandomMatrixModel.densityMatrix, opNorm, RandomMatrixModel.gamma, hs]

/-- If there are no sample columns, then the normalized Wishart operator norm
vanishes identically. -/
theorem wishartOpNorm_zero_of_card_eq_zero
    (hs : Fintype.card σ = 0) (ω : Ω p q σ) :
    wishartOpNorm p q σ ω = 0 := by
  simp [wishartOpNorm, RandomMatrixModel.wishart, RandomMatrixModel.densityMatrix,
    opNorm, hs]

/-- In the zero-sample branch, every upper-tail event for `‖W‖∞` is empty. -/
theorem wishartOpNormEvent_compl_eq_empty_of_card_eq_zero
    (hs : Fintype.card σ = 0) {C : ℝ} (hC : 0 ≤ C) :
    ((wishartOpNormEvent (p := p) (q := q) (σ := σ) C)ᶜ) = ∅ := by
  have hCs_nonneg : 0 ≤ C * sampleDimension σ := mul_nonneg hC sampleDimension_nonneg
  ext ω
  simp [wishartOpNormEvent, wishartOpNorm, RandomMatrixModel.wishart,
    RandomMatrixModel.densityMatrix, opNorm, hs, hCs_nonneg]

/-- In the zero-sample branch, every upper-tail event for `‖W^Γ‖∞` is empty. -/
theorem wishartGammaOpNormEvent_compl_eq_empty_of_card_eq_zero
    (hs : Fintype.card σ = 0) {C : ℝ} (hC : 0 ≤ C) :
    ((wishartGammaOpNormEvent (p := p) (q := q) (σ := σ) C)ᶜ) = ∅ := by
  have hCs_nonneg : 0 ≤ C * sampleDimension σ := mul_nonneg hC sampleDimension_nonneg
  ext ω
  simp [wishartGammaOpNormEvent, wishartGammaOpNorm, RandomMatrixModel.wishartGamma,
    RandomMatrixModel.wishart, RandomMatrixModel.densityMatrix, opNorm,
    RandomMatrixModel.gamma, hs, hCs_nonneg]

/-- In the zero-dimensional bipartite space, every upper-tail event for `‖W‖∞`
is empty. -/
theorem wishartOpNormEvent_compl_eq_empty_of_isEmpty_bipIndex
    [IsEmpty (RandomMatrixModel.BipIndex p q)] {C : ℝ} (hC : 0 ≤ C) :
    ((wishartOpNormEvent (p := p) (q := q) (σ := σ) C)ᶜ) = ∅ := by
  have hCs_nonneg : 0 ≤ C * sampleDimension σ := mul_nonneg hC sampleDimension_nonneg
  ext ω
  simp [wishartOpNormEvent, wishartOpNorm, opNorm, sampleDimension]
  simpa [sampleDimension] using hCs_nonneg

/-- In the zero-dimensional bipartite space, every upper-tail event for
`‖W^Γ‖∞` is empty. -/
theorem wishartGammaOpNormEvent_compl_eq_empty_of_isEmpty_bipIndex
    [IsEmpty (RandomMatrixModel.BipIndex p q)] {C : ℝ} (hC : 0 ≤ C) :
    ((wishartGammaOpNormEvent (p := p) (q := q) (σ := σ) C)ᶜ) = ∅ := by
  have hCs_nonneg : 0 ≤ C * sampleDimension σ := mul_nonneg hC sampleDimension_nonneg
  ext ω
  simp [wishartGammaOpNormEvent, wishartGammaOpNorm, opNorm, sampleDimension]
  simpa [sampleDimension] using hCs_nonneg

/-- Numerical constant used in the quarter-net cardinality bound. -/
theorem exp_seven_ge_eighty_one : (81 : ℝ) ≤ Real.exp 7 := by
  have hpow : (2 : ℝ) ^ 7 < (Real.exp 1) ^ 7 := by
    exact pow_lt_pow_left₀ Real.exp_one_gt_two (by positivity) (by decide)
  have hrew : (Real.exp 1) ^ 7 = Real.exp 7 := by
    rw [← Real.exp_nat_mul]
    ring_nf
  have hgt128 : (128 : ℝ) < Real.exp 7 := by
    have h2pow : (2 : ℝ) ^ 7 = 128 := by norm_num
    nlinarith [hpow, h2pow, hrew]
  nlinarith [hgt128]

/-- Converts an `81^D` net cardinality estimate into the exponential form
`exp (7 D)`. -/
theorem finite_card_real_le_exp_seven_mul
    {α ι : Type*} [Fintype ι] {N : Set α}
    (hNfinite : N.Finite)
    (hNencard : N.encard ≤ 81 ^ Fintype.card ι) :
    (hNfinite.toFinset.card : ℝ) ≤ Real.exp (7 * (Fintype.card ι : ℝ)) := by
  have hcard_nat : hNfinite.toFinset.card ≤ (81 : ℕ) ^ Fintype.card ι := by
    rw [hNfinite.encard_eq_coe_toFinset_card] at hNencard
    exact_mod_cast hNencard
  calc
    (hNfinite.toFinset.card : ℝ) ≤ ((81 : ℕ) ^ Fintype.card ι : ℝ) := by
      exact_mod_cast hcard_nat
    _ = ((81 : ℝ) ^ Fintype.card ι) := by norm_num
    _ ≤ (Real.exp 7) ^ Fintype.card ι := by
      exact pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 81) exp_seven_ge_eighty_one _
    _ = Real.exp (7 * (Fintype.card ι : ℝ)) := by
      rw [← Real.exp_nat_mul]
      ring_nf

omit [DecidableEq p] [DecidableEq q] in
/-- Net-lifted upper tail for the rectangular Gaussian sample operator norm.

The fixed-vector tail for `‖Gv‖` is union-bounded over a `(1 / 4)`-net of the
domain sphere, and the deterministic rectangular net lemma upgrades the
finite-dimensional supremum to `sampleOpNorm`. -/
theorem sampleOpNorm_upper_tail_netLifted_of_nonempty
    [Nonempty σ] [DecidableEq σ] :
    (gaussianMeasure p q σ).real
        ({ω : Ω p q σ |
          sampleOpNorm (p := p) (q := q) (σ := σ)
            (gaussianMatrix p q σ ω) ≤
              8 * Real.sqrt (bipartiteDimension p q + sampleDimension σ + 1)}ᶜ) ≤
      Real.exp (-bipartiteDimension p q) := by
  classical
  haveI : IsProbabilityMeasure (gaussianMeasure p q σ) := by
    rw [gaussianMeasure_eq]
    infer_instance
  rcases exists_quarter_net_unit_sphere_card_le_pow
      (ι := σ) with
    ⟨N, hNfinite, hnet, hNencard⟩
  let D : ℝ := bipartiteDimension p q
  let s : ℝ := sampleDimension σ
  let R : ℝ := 4 * Real.sqrt (D + s + 1)
  have hD_nonneg : 0 ≤ D := by
    unfold D bipartiteDimension
    positivity
  have hs_nonneg : 0 ≤ s := by
    unfold s sampleDimension
    positivity
  have hrad_nonneg : 0 ≤ D + s + 1 := by
    nlinarith
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    positivity
  have hR_sq : R ^ 2 = 16 * (D + s + 1) := by
    dsimp [R]
    rw [mul_pow, Real.sq_sqrt hrad_nonneg]
    norm_num
  have hcard_le : (hNfinite.toFinset.card : ℝ) ≤ Real.exp (7 * s) := by
    simpa [s, sampleDimension, mul_comm, mul_left_comm, mul_assoc] using
      finite_card_real_le_exp_seven_mul
        (ι := σ) hNfinite hNencard
  have hfixed :
      ∀ u ∈ hNfinite.toFinset,
        (gaussianMeasure p q σ).real
          {ω : Ω p q σ |
            R ≤ ‖(Matrix.toEuclideanLin (𝕜 := ℂ)
              (m := RandomMatrixModel.BipIndex p q) (n := σ)
              (gaussianMatrix p q σ ω)) (u : EuclideanSpace ℂ σ)‖} ≤
          Real.exp (-(1 / 2 : ℝ) * R ^ 2 + Real.log 2 * D) := by
    intro u hu
    simpa [D, R, bipartiteDimension] using
      gaussianMatrix_unitVector_mul_norm_upper_tail
        (p := p) (q := q) (σ := σ) u (r := R) hR_nonneg
  have hunion :
      (gaussianMeasure p q σ).real
          (⋃ u ∈ hNfinite.toFinset,
            {ω : Ω p q σ |
              R ≤ ‖(Matrix.toEuclideanLin (𝕜 := ℂ)
                (m := RandomMatrixModel.BipIndex p q) (n := σ)
                (gaussianMatrix p q σ ω)) (u : EuclideanSpace ℂ σ)‖}) ≤
        Real.exp (-D) := by
    calc
      (gaussianMeasure p q σ).real
          (⋃ u ∈ hNfinite.toFinset,
            {ω : Ω p q σ |
              R ≤ ‖(Matrix.toEuclideanLin (𝕜 := ℂ)
                (m := RandomMatrixModel.BipIndex p q) (n := σ)
                (gaussianMatrix p q σ ω)) (u : EuclideanSpace ℂ σ)‖}) ≤
          ∑ u ∈ hNfinite.toFinset,
            (gaussianMeasure p q σ).real
              {ω : Ω p q σ |
                R ≤ ‖(Matrix.toEuclideanLin (𝕜 := ℂ)
                  (m := RandomMatrixModel.BipIndex p q) (n := σ)
                  (gaussianMatrix p q σ ω)) (u : EuclideanSpace ℂ σ)‖} := by
            simpa using
              (measureReal_biUnion_finset_le (μ := gaussianMeasure p q σ)
                (s := hNfinite.toFinset)
                (f := fun u : Metric.sphere (0 : EuclideanSpace ℂ σ) 1 =>
                  {ω : Ω p q σ |
                    R ≤ ‖(Matrix.toEuclideanLin (𝕜 := ℂ)
                      (m := RandomMatrixModel.BipIndex p q) (n := σ)
                      (gaussianMatrix p q σ ω)) (u : EuclideanSpace ℂ σ)‖}))
      _ ≤ ∑ u ∈ hNfinite.toFinset,
            Real.exp (-(1 / 2 : ℝ) * R ^ 2 + Real.log 2 * D) := by
            refine Finset.sum_le_sum ?_
            intro u hu
            exact hfixed u hu
      _ = (hNfinite.toFinset.card : ℝ) *
            Real.exp (-(1 / 2 : ℝ) * R ^ 2 + Real.log 2 * D) := by
            simp [Finset.sum_const, mul_comm]
      _ ≤ Real.exp (7 * s) *
            Real.exp (-(1 / 2 : ℝ) * R ^ 2 + Real.log 2 * D) := by
            exact mul_le_mul_of_nonneg_right hcard_le (by positivity)
      _ = Real.exp (7 * s + (-(1 / 2 : ℝ) * R ^ 2 + Real.log 2 * D)) := by
            rw [← Real.exp_add]
      _ ≤ Real.exp (-D) := by
            apply Real.exp_le_exp.mpr
            have hlog_le_one : Real.log 2 ≤ (1 : ℝ) := by
              linarith [Real.log_two_lt_d9]
            have hlogD : Real.log 2 * D ≤ 1 * D :=
              mul_le_mul_of_nonneg_right hlog_le_one hD_nonneg
            nlinarith
  have hgood :
      (gaussianMeasure p q σ).real
          ({ω : Ω p q σ |
            sampleOpNorm (p := p) (q := q) (σ := σ)
              (gaussianMatrix p q σ ω) ≤ 8 * Real.sqrt (D + s + 1)}ᶜ) ≤
        (gaussianMeasure p q σ).real
          (⋃ u ∈ hNfinite.toFinset,
            {ω : Ω p q σ |
              R ≤ ‖(Matrix.toEuclideanLin (𝕜 := ℂ)
                (m := RandomMatrixModel.BipIndex p q) (n := σ)
                (gaussianMatrix p q σ ω)) (u : EuclideanSpace ℂ σ)‖}) := by
    refine measureReal_mono (h₂ := (measure_lt_top (gaussianMeasure p q σ) _).ne) ?_
    intro ω hω
    by_contra hbad
    have hbound :
        ∀ u ∈ N,
          ‖(Matrix.toEuclideanLin (𝕜 := ℂ)
            (m := RandomMatrixModel.BipIndex p q) (n := σ)
            (gaussianMatrix p q σ ω)) (u : EuclideanSpace ℂ σ)‖ ≤ R := by
      intro u huN
      have huFin : u ∈ hNfinite.toFinset := by
        rw [Set.Finite.mem_toFinset]
        exact huN
      have hnot :
          ω ∉ {ω : Ω p q σ |
            R ≤ ‖(Matrix.toEuclideanLin (𝕜 := ℂ)
              (m := RandomMatrixModel.BipIndex p q) (n := σ)
              (gaussianMatrix p q σ ω)) (u : EuclideanSpace ℂ σ)‖} := by
        intro hmem
        have hmemUnion :
            ω ∈ ⋃ u ∈ hNfinite.toFinset,
              {ω : Ω p q σ |
                R ≤ ‖(Matrix.toEuclideanLin (𝕜 := ℂ)
                  (m := RandomMatrixModel.BipIndex p q) (n := σ)
                  (gaussianMatrix p q σ ω)) (u : EuclideanSpace ℂ σ)‖} :=
          Set.mem_biUnion huFin hmem
        exact hbad hmemUnion
      exact le_of_lt (lt_of_not_ge hnot)
    have hOp :
        sampleOpNorm (p := p) (q := q) (σ := σ)
          (gaussianMatrix p q σ ω) ≤ 2 * R :=
      sampleOpNorm_le_two_mul_of_forall_quarterNet_bound
        (p := p) (q := q) (σ := σ)
        (G := gaussianMatrix p q σ ω) (N := N) (B := R)
        hR_nonneg hnet hbound
    have hthreshold : 2 * R = 8 * Real.sqrt (D + s + 1) := by
      dsimp [R]
      ring
    have hOp' :
        sampleOpNorm (p := p) (q := q) (σ := σ)
          (gaussianMatrix p q σ ω) ≤ 8 * Real.sqrt (D + s + 1) := by
      linarith
    exact hω hOp'
  simpa [D, s] using le_trans hgood hunion

omit [DecidableEq p] [DecidableEq q] in
/-- No-input net-lifted upper tail for the rectangular Gaussian sample
operator norm.  The nonempty sample case is the quarter-net argument; the
empty sample case is closed by the deterministic zero-column identity. -/
theorem sampleOpNorm_upper_tail_netLifted :
    (gaussianMeasure p q σ).real
        ({ω : Ω p q σ |
          sampleOpNorm (p := p) (q := q) (σ := σ)
            (gaussianMatrix p q σ ω) ≤
              8 * Real.sqrt (bipartiteDimension p q + sampleDimension σ + 1)}ᶜ) ≤
      Real.exp (-bipartiteDimension p q) := by
  classical
  haveI : IsProbabilityMeasure (gaussianMeasure p q σ) := by
    rw [gaussianMeasure_eq]
    infer_instance
  by_cases hσ : Nonempty σ
  · letI : Nonempty σ := hσ
    letI : DecidableEq σ := Classical.decEq σ
    exact sampleOpNorm_upper_tail_netLifted_of_nonempty
      (p := p) (q := q) (σ := σ)
  · haveI : IsEmpty σ := not_nonempty_iff.mp hσ
    have hempty :
        ({ω : Ω p q σ |
          sampleOpNorm (p := p) (q := q) (σ := σ)
            (gaussianMatrix p q σ ω) ≤
              8 * Real.sqrt (bipartiteDimension p q + sampleDimension σ + 1)}ᶜ) = ∅ := by
      ext ω
      have hle :
          sampleOpNorm (p := p) (q := q) (σ := σ)
            (gaussianMatrix p q σ ω) ≤
              8 * Real.sqrt (bipartiteDimension p q + sampleDimension σ + 1) := by
        rw [sampleOpNorm_zero_of_isEmpty
          (p := p) (q := q) (σ := σ) (gaussianMatrix p q σ ω)]
        positivity
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false]
      constructor
      · intro h
        exact h (by simpa [gaussianMatrix] using hle)
      · intro h
        exact False.elim h
    rw [hempty]
    simpa using
      (show (0 : ℝ) ≤ Real.exp (-bipartiteDimension p q) from
        le_of_lt (Real.exp_pos _))

omit [DecidableEq p] [DecidableEq q] in
/-- Threshold-parametrized strict upper tail for the rectangular Gaussian
sample operator norm in the nonempty sample case. -/
theorem sampleOpNorm_upper_tail_netLifted_strict_of_nonempty
    [Nonempty σ] [DecidableEq σ] {R : ℝ} (hR : 0 ≤ R) :
    (gaussianMeasure p q σ).real
        {ω : Ω p q σ |
          R < sampleOpNorm (p := p) (q := q) (σ := σ)
            (gaussianMatrix p q σ ω)} ≤
      Real.exp (7 * sampleDimension σ +
        (-(1 / 8 : ℝ) * R ^ 2 + Real.log 2 * bipartiteDimension p q)) := by
  classical
  haveI : IsProbabilityMeasure (gaussianMeasure p q σ) := by
    rw [gaussianMeasure_eq]
    infer_instance
  rcases exists_quarter_net_unit_sphere_card_le_pow
      (ι := σ) with
    ⟨N, hNfinite, hnet, hNencard⟩
  let D : ℝ := bipartiteDimension p q
  let s : ℝ := sampleDimension σ
  let r : ℝ := R / 2
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    positivity
  have hr_sq : -(1 / 2 : ℝ) * r ^ 2 = -(1 / 8 : ℝ) * R ^ 2 := by
    dsimp [r]
    ring
  have hcard_le : (hNfinite.toFinset.card : ℝ) ≤ Real.exp (7 * s) := by
    simpa [s, sampleDimension, mul_comm, mul_left_comm] using
      finite_card_real_le_exp_seven_mul
        (ι := σ) hNfinite hNencard
  have hfixed :
      ∀ u ∈ hNfinite.toFinset,
        (gaussianMeasure p q σ).real
          {ω : Ω p q σ |
            r ≤ ‖(Matrix.toEuclideanLin (𝕜 := ℂ)
              (m := RandomMatrixModel.BipIndex p q) (n := σ)
              (gaussianMatrix p q σ ω)) (u : EuclideanSpace ℂ σ)‖} ≤
          Real.exp (-(1 / 8 : ℝ) * R ^ 2 + Real.log 2 * D) := by
    intro u _hu
    calc
      (gaussianMeasure p q σ).real
          {ω : Ω p q σ |
            r ≤ ‖(Matrix.toEuclideanLin (𝕜 := ℂ)
              (m := RandomMatrixModel.BipIndex p q) (n := σ)
              (gaussianMatrix p q σ ω)) (u : EuclideanSpace ℂ σ)‖}
          ≤ Real.exp (-(1 / 2 : ℝ) * r ^ 2 + Real.log 2 * D) := by
            simpa [D, bipartiteDimension] using
              gaussianMatrix_unitVector_mul_norm_upper_tail
                (p := p) (q := q) (σ := σ) u (r := r) hr_nonneg
      _ = Real.exp (-(1 / 8 : ℝ) * R ^ 2 + Real.log 2 * D) := by
            rw [hr_sq]
  have hunion :
      (gaussianMeasure p q σ).real
          (⋃ u ∈ hNfinite.toFinset,
            {ω : Ω p q σ |
              r ≤ ‖(Matrix.toEuclideanLin (𝕜 := ℂ)
                (m := RandomMatrixModel.BipIndex p q) (n := σ)
                (gaussianMatrix p q σ ω)) (u : EuclideanSpace ℂ σ)‖}) ≤
        Real.exp (7 * s + (-(1 / 8 : ℝ) * R ^ 2 + Real.log 2 * D)) := by
    calc
      (gaussianMeasure p q σ).real
          (⋃ u ∈ hNfinite.toFinset,
            {ω : Ω p q σ |
              r ≤ ‖(Matrix.toEuclideanLin (𝕜 := ℂ)
                (m := RandomMatrixModel.BipIndex p q) (n := σ)
                (gaussianMatrix p q σ ω)) (u : EuclideanSpace ℂ σ)‖}) ≤
          ∑ u ∈ hNfinite.toFinset,
            (gaussianMeasure p q σ).real
              {ω : Ω p q σ |
                r ≤ ‖(Matrix.toEuclideanLin (𝕜 := ℂ)
                  (m := RandomMatrixModel.BipIndex p q) (n := σ)
                  (gaussianMatrix p q σ ω)) (u : EuclideanSpace ℂ σ)‖} := by
            simpa using
              (measureReal_biUnion_finset_le (μ := gaussianMeasure p q σ)
                (s := hNfinite.toFinset)
                (f := fun u : Metric.sphere (0 : EuclideanSpace ℂ σ) 1 =>
                  {ω : Ω p q σ |
                    r ≤ ‖(Matrix.toEuclideanLin (𝕜 := ℂ)
                      (m := RandomMatrixModel.BipIndex p q)
                      (n := σ) (gaussianMatrix p q σ ω))
                        (u : EuclideanSpace ℂ σ)‖}))
      _ ≤ ∑ u ∈ hNfinite.toFinset,
            Real.exp (-(1 / 8 : ℝ) * R ^ 2 + Real.log 2 * D) := by
            refine Finset.sum_le_sum ?_
            intro u hu
            exact hfixed u hu
      _ = (hNfinite.toFinset.card : ℝ) *
            Real.exp (-(1 / 8 : ℝ) * R ^ 2 + Real.log 2 * D) := by
            simp [Finset.sum_const, mul_comm]
      _ ≤ Real.exp (7 * s) *
            Real.exp (-(1 / 8 : ℝ) * R ^ 2 + Real.log 2 * D) := by
            exact mul_le_mul_of_nonneg_right hcard_le (by positivity)
      _ = Real.exp (7 * s + (-(1 / 8 : ℝ) * R ^ 2 + Real.log 2 * D)) := by
            rw [← Real.exp_add]
  have hsubset :
      {ω : Ω p q σ |
          R < sampleOpNorm (p := p) (q := q) (σ := σ)
            (gaussianMatrix p q σ ω)} ⊆
        (⋃ u ∈ hNfinite.toFinset,
            {ω : Ω p q σ |
              r ≤ ‖(Matrix.toEuclideanLin (𝕜 := ℂ)
                (m := RandomMatrixModel.BipIndex p q) (n := σ)
                (gaussianMatrix p q σ ω)) (u : EuclideanSpace ℂ σ)‖}) := by
    intro ω hω
    by_contra hbad
    have hbound :
        ∀ u ∈ N,
          ‖(Matrix.toEuclideanLin (𝕜 := ℂ)
            (m := RandomMatrixModel.BipIndex p q) (n := σ)
            (gaussianMatrix p q σ ω)) (u : EuclideanSpace ℂ σ)‖ ≤ r := by
      intro u huN
      have huFin : u ∈ hNfinite.toFinset := by
        rw [Set.Finite.mem_toFinset]
        exact huN
      have hnot :
          ω ∉ {ω : Ω p q σ |
            r ≤ ‖(Matrix.toEuclideanLin (𝕜 := ℂ)
              (m := RandomMatrixModel.BipIndex p q) (n := σ)
              (gaussianMatrix p q σ ω)) (u : EuclideanSpace ℂ σ)‖} := by
        intro hmem
        have hmemUnion :
            ω ∈ ⋃ u ∈ hNfinite.toFinset,
              {ω : Ω p q σ |
                r ≤ ‖(Matrix.toEuclideanLin (𝕜 := ℂ)
                  (m := RandomMatrixModel.BipIndex p q) (n := σ)
                  (gaussianMatrix p q σ ω)) (u : EuclideanSpace ℂ σ)‖} :=
          Set.mem_biUnion huFin hmem
        exact hbad hmemUnion
      exact le_of_lt (lt_of_not_ge hnot)
    have hOp :
        sampleOpNorm (p := p) (q := q) (σ := σ)
          (gaussianMatrix p q σ ω) ≤ 2 * r :=
      sampleOpNorm_le_two_mul_of_forall_quarterNet_bound
        (p := p) (q := q) (σ := σ)
        (G := gaussianMatrix p q σ ω) (N := N) (B := r)
        hr_nonneg hnet hbound
    have hOp' :
        sampleOpNorm (p := p) (q := q) (σ := σ)
          (gaussianMatrix p q σ ω) ≤ R := by
      have hOp'' :
          sampleOpNorm (p := p) (q := q) (σ := σ)
            (gaussianMatrix p q σ ω) ≤ 2 * (R / 2) := by
        simpa [gaussianMatrix, GaussianModel.gaussianSampleMatrix, r] using hOp
      linarith
    exact not_lt_of_ge hOp' hω
  exact (measureReal_mono (h₂ := (measure_lt_top (gaussianMeasure p q σ) _).ne) hsubset).trans
    (by simpa [D, s] using hunion)

omit [DecidableEq p] [DecidableEq q] in
/-- Threshold-parametrized strict upper tail for the rectangular Gaussian
sample operator norm.  The empty sample case is deterministic. -/
theorem sampleOpNorm_upper_tail_netLifted_strict {R : ℝ} (hR : 0 ≤ R) :
    (gaussianMeasure p q σ).real
        {ω : Ω p q σ |
          R < sampleOpNorm (p := p) (q := q) (σ := σ)
            (gaussianMatrix p q σ ω)} ≤
      Real.exp (7 * sampleDimension σ +
        (-(1 / 8 : ℝ) * R ^ 2 + Real.log 2 * bipartiteDimension p q)) := by
  classical
  haveI : IsProbabilityMeasure (gaussianMeasure p q σ) := by
    rw [gaussianMeasure_eq]
    infer_instance
  by_cases hσ : Nonempty σ
  · letI : Nonempty σ := hσ
    letI : DecidableEq σ := Classical.decEq σ
    exact sampleOpNorm_upper_tail_netLifted_strict_of_nonempty
      (p := p) (q := q) (σ := σ) hR
  · haveI : IsEmpty σ := not_nonempty_iff.mp hσ
    have hempty :
        {ω : Ω p q σ |
          R < sampleOpNorm (p := p) (q := q) (σ := σ)
            (gaussianMatrix p q σ ω)} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
      rw [sampleOpNorm_zero_of_isEmpty
        (p := p) (q := q) (σ := σ) (gaussianMatrix p q σ ω)]
      exact ⟨fun h => by linarith, fun h => False.elim h⟩
    rw [hempty]
    simpa using
      (show (0 : ℝ) ≤ Real.exp (7 * sampleDimension σ +
        (-(1 / 8 : ℝ) * R ^ 2 + Real.log 2 * bipartiteDimension p q)) from
        le_of_lt (Real.exp_pos _))

omit [DecidableEq p] [DecidableEq q] in
/-- Once the threshold is above `16 sqrt(D+s+1)`, the net-lifted sample
operator-norm tail is bounded by `exp (-t)`. -/
theorem sampleOpNorm_tail_exponent_le_neg {t : ℝ}
    (ht :
      16 * Real.sqrt (bipartiteDimension p q + sampleDimension σ + 1) < t) :
    7 * sampleDimension σ +
        (-(1 / 8 : ℝ) * t ^ 2 + Real.log 2 * bipartiteDimension p q) ≤ -t := by
  let D : ℝ := bipartiteDimension p q
  let s : ℝ := sampleDimension σ
  let C : ℝ := D + s + 1
  let A : ℝ := 16 * Real.sqrt C
  have hD_nonneg : 0 ≤ D := by
    dsimp [D, bipartiteDimension]
    positivity
  have hs_nonneg : 0 ≤ s := by
    dsimp [s, sampleDimension]
    positivity
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    nlinarith
  have hC_ge_one : 1 ≤ C := by
    dsimp [C]
    nlinarith
  have hsqrtC_le_C : Real.sqrt C ≤ C := by
    rw [Real.sqrt_le_iff]
    constructor
    · nlinarith
    · nlinarith [hC_ge_one]
  have hA_ge_eight : 8 ≤ A := by
    dsimp [A]
    have hsqrt_ge_one : 1 ≤ Real.sqrt C := by
      simpa using (Real.one_le_sqrt.mpr hC_ge_one)
    nlinarith
  have hAt : A < t := by
    simpa [A, C, D, s] using ht
  have hmono : A ^ 2 / 8 - A ≤ t ^ 2 / 8 - t := by
    have hprod : 0 ≤ (t - A) * (t + A - 8) := by
      have h1 : 0 ≤ t - A := by linarith
      have h2 : 0 ≤ t + A - 8 := by linarith
      exact mul_nonneg h1 h2
    nlinarith
  have hA_sq : A ^ 2 = 256 * C := by
    dsimp [A]
    rw [mul_pow, Real.sq_sqrt hC_nonneg]
    norm_num
  have hlog_le_one : Real.log 2 ≤ (1 : ℝ) := by
    linarith [Real.log_two_lt_d9]
  have hlogD : Real.log 2 * D ≤ D := by
    simpa using mul_le_mul_of_nonneg_right hlog_le_one hD_nonneg
  have hbase : 7 * s + Real.log 2 * D ≤ A ^ 2 / 8 - A := by
    rw [hA_sq]
    nlinarith
  have hbase' : 7 * s + Real.log 2 * D ≤ t ^ 2 / 8 - t := le_trans hbase hmono
  dsimp [D, s] at hbase' ⊢
  nlinarith

omit [DecidableEq p] [DecidableEq q] in
/-- Integrated tail estimate for the rectangular Gaussian sample operator
norm. -/
theorem sampleOpNorm_tail_integral_le :
    (∫ t in Set.Ioi (0 : ℝ),
        (gaussianMeasure p q σ).real
          {ω : Ω p q σ |
            t < sampleOpNorm (p := p) (q := q) (σ := σ)
              (gaussianMatrix p q σ ω)}) ≤
      17 * Real.sqrt (bipartiteDimension p q + sampleDimension σ + 1) := by
  classical
  haveI : IsProbabilityMeasure (gaussianMeasure p q σ) := by
    rw [gaussianMeasure_eq]
    infer_instance
  let X : Ω p q σ → ℝ := fun ω =>
    sampleOpNorm (p := p) (q := q) (σ := σ)
      (gaussianMatrix p q σ ω)
  let D : ℝ := bipartiteDimension p q
  let s : ℝ := sampleDimension σ
  let C : ℝ := D + s + 1
  let A : ℝ := 16 * Real.sqrt C
  have hD_nonneg : 0 ≤ D := by
    dsimp [D, bipartiteDimension]
    positivity
  have hs_nonneg : 0 ≤ s := by
    dsimp [s, sampleDimension]
    positivity
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    nlinarith
  have hC_ge_one : 1 ≤ C := by
    dsimp [C]
    nlinarith
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hsqrt_ge_one : 1 ≤ Real.sqrt C := by
    simpa using (Real.one_le_sqrt.mpr hC_ge_one)
  have hIndicInt :
      IntegrableOn
        (fun t : ℝ => (Set.Ioc (0 : ℝ) A).indicator (fun _ => (1 : ℝ)) t)
        (Set.Ioi (0 : ℝ)) volume := by
    rw [integrableOn_indicator_iff measurableSet_Ioc]
    refine integrableOn_const ?_
    exact ((measure_mono Set.inter_subset_left).trans_lt (by simp [Real.volume_Ioc])).ne
  have hExpInt : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Set.Ioi (0 : ℝ)) volume :=
    integrableOn_exp_neg_Ioi 0
  have hUpperInt :
      IntegrableOn
        (fun t : ℝ =>
          (Set.Ioc (0 : ℝ) A).indicator (fun _ => (1 : ℝ)) t + Real.exp (-t))
        (Set.Ioi (0 : ℝ)) volume :=
    hIndicInt.add hExpInt
  have hExpTail :
      ∀ ⦃t : ℝ⦄, 0 < t → A < t →
        (gaussianMeasure p q σ).real {ω : Ω p q σ | t < X ω} ≤ Real.exp (-t) := by
    intro t ht0 hAt
    have hTail := sampleOpNorm_upper_tail_netLifted_strict
      (p := p) (q := q) (σ := σ) (R := t) (le_of_lt ht0)
    have hExpLe :
        Real.exp (7 * sampleDimension σ +
          (-(1 / 8 : ℝ) * t ^ 2 + Real.log 2 * bipartiteDimension p q)) ≤
          Real.exp (-t) := by
      apply Real.exp_le_exp.mpr
      apply sampleOpNorm_tail_exponent_le_neg (p := p) (q := q) (σ := σ)
      simpa [A, C, D, s] using hAt
    simpa [X] using hTail.trans hExpLe
  have hPointwise :
      (fun t : ℝ => (gaussianMeasure p q σ).real {ω : Ω p q σ | t < X ω}) ≤ᵐ[
          volume.restrict (Set.Ioi (0 : ℝ))]
        fun t : ℝ =>
          (Set.Ioc (0 : ℝ) A).indicator (fun _ => (1 : ℝ)) t + Real.exp (-t) := by
    rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall ?_
    intro t ht0
    by_cases htA : t ≤ A
    · have hind : (Set.Ioc (0 : ℝ) A).indicator (fun _ => (1 : ℝ)) t = 1 := by
        rw [Set.indicator_of_mem]
        exact ⟨ht0, htA⟩
      calc
        (gaussianMeasure p q σ).real {ω : Ω p q σ | t < X ω} ≤ 1 := by
          exact measureReal_le_one
        _ ≤ (Set.Ioc (0 : ℝ) A).indicator (fun _ => (1 : ℝ)) t + Real.exp (-t) := by
          rw [hind]
          linarith [Real.exp_pos (-t)]
    · have hAt : A < t := lt_of_not_ge htA
      have hind : (Set.Ioc (0 : ℝ) A).indicator (fun _ => (1 : ℝ)) t = 0 := by
        rw [Set.indicator_of_notMem]
        exact fun hmem => htA hmem.2
      calc
        (gaussianMeasure p q σ).real {ω : Ω p q σ | t < X ω} ≤ Real.exp (-t) :=
          hExpTail ht0 hAt
        _ ≤ (Set.Ioc (0 : ℝ) A).indicator (fun _ => (1 : ℝ)) t + Real.exp (-t) := by
          rw [hind]
          linarith
  have hNonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        fun t : ℝ => (gaussianMeasure p q σ).real {ω : Ω p q σ | t < X ω} := by
    exact Filter.Eventually.of_forall fun _ => by positivity
  have hTailIntegral :
      (∫ t in Set.Ioi (0 : ℝ),
          (gaussianMeasure p q σ).real {ω : Ω p q σ | t < X ω}) ≤
        ∫ t in Set.Ioi (0 : ℝ),
          ((Set.Ioc (0 : ℝ) A).indicator (fun _ => (1 : ℝ)) t + Real.exp (-t)) := by
    simpa [IntegrableOn] using
      (integral_mono_of_nonneg hNonneg hUpperInt hPointwise)
  have hUpperIntegral :
      (∫ t in Set.Ioi (0 : ℝ),
          ((Set.Ioc (0 : ℝ) A).indicator (fun _ => (1 : ℝ)) t + Real.exp (-t))) =
        A + 1 := by
    rw [integral_add hIndicInt hExpInt]
    have hi :
        (∫ t in Set.Ioi (0 : ℝ),
          (Set.Ioc (0 : ℝ) A).indicator (fun _ => (1 : ℝ)) t) = A := by
      rw [MeasureTheory.setIntegral_indicator measurableSet_Ioc]
      rw [MeasureTheory.setIntegral_const]
      have hset : Set.Ioi (0 : ℝ) ∩ Set.Ioc (0 : ℝ) A = Set.Ioc (0 : ℝ) A := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioc]
        constructor
        · intro hx
          exact hx.2
        · intro hx
          exact ⟨hx.1, hx⟩
      rw [hset]
      simp [hA_nonneg]
    have he : (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t)) = 1 := by
      simpa using integral_exp_neg_Ioi_zero
    rw [hi, he]
  have hA_plus : A + 1 ≤ 17 * Real.sqrt C := by
    dsimp [A]
    nlinarith
  calc
    (∫ t in Set.Ioi (0 : ℝ),
        (gaussianMeasure p q σ).real {ω : Ω p q σ | t < X ω})
        ≤ ∫ t in Set.Ioi (0 : ℝ),
          ((Set.Ioc (0 : ℝ) A).indicator (fun _ => (1 : ℝ)) t + Real.exp (-t)) :=
          hTailIntegral
    _ = A + 1 := hUpperIntegral
    _ ≤ 17 * Real.sqrt C := hA_plus

omit [DecidableEq p] [DecidableEq q] in
/-- Expectation bound obtained by integrating the net-lifted tail of the
rectangular Gaussian sample operator norm. -/
theorem sampleOpNorm_integral_le :
    (∫ ω : Ω p q σ,
        sampleOpNorm (p := p) (q := q) (σ := σ)
          (gaussianMatrix p q σ ω) ∂gaussianMeasure p q σ) ≤
      17 * Real.sqrt (bipartiteDimension p q + sampleDimension σ + 1) := by
  let X : Ω p q σ → ℝ := fun ω =>
    sampleOpNorm (p := p) (q := q) (σ := σ)
      (gaussianMatrix p q σ ω)
  have hLayer :
      (∫ ω : Ω p q σ, X ω ∂gaussianMeasure p q σ) =
        ∫ t in Set.Ioi (0 : ℝ),
          (gaussianMeasure p q σ).real {ω : Ω p q σ | t < X ω} := by
    exact Integrable.integral_eq_integral_meas_lt
      (μ := gaussianMeasure p q σ)
      (f := X)
      (by simpa [X] using sampleOpNorm_integrable (p := p) (q := q) (σ := σ))
      (Filter.Eventually.of_forall fun ω => by
        dsimp [X]
        unfold sampleOpNorm
        positivity)
  calc
    (∫ ω : Ω p q σ, X ω ∂gaussianMeasure p q σ)
        = ∫ t in Set.Ioi (0 : ℝ),
          (gaussianMeasure p q σ).real {ω : Ω p q σ | t < X ω} := hLayer
    _ ≤ 17 * Real.sqrt (bipartiteDimension p q + sampleDimension σ + 1) :=
          sampleOpNorm_tail_integral_le (p := p) (q := q) (σ := σ)

/-- Upper tail for the total Gaussian mass at level `2 D s`. -/
theorem gaussianMass_upper_tail :
    (gaussianMeasure p q σ).real
        {ω | 2 * bipartiteDimension p q * sampleDimension σ ≤ gaussianMass p q σ ω} ≤
      Real.exp (-((1 / 6 : ℝ) * bipartiteDimension p q * sampleDimension σ)) := by
  let N : ℝ := bipartiteDimension p q * sampleDimension σ
  let X : Ω p q σ → ℝ := fun ω => gaussianMass p q σ ω - N
  haveI : IsProbabilityMeasure (gaussianMeasure p q σ) := by
    rw [gaussianMeasure_eq]
    infer_instance
  have hθ_nonneg : 0 ≤ (1 / 2 : ℝ) := by positivity
  have hInt :
      Integrable (fun ω : Ω p q σ => Real.exp ((1 / 2 : ℝ) * X ω))
        (gaussianMeasure p q σ) := by
    simpa [X, N] using
      gaussianMass_centered_integrable_exp_mul
        (p := p) (q := q) (σ := σ) (θ := (1 / 2 : ℝ)) (by norm_num)
  have hchern :=
    ProbabilityTheory.measure_ge_le_exp_mul_mgf
      (μ := gaussianMeasure p q σ)
      (X := X) (ε := N) hθ_nonneg hInt
  have hmgf :
      ProbabilityTheory.mgf X (gaussianMeasure p q σ) (1 / 2 : ℝ) =
        ∏ _α : σ, ∏ _i : RandomMatrixModel.BipIndex p q,
          Real.exp (-(1 / 2 : ℝ)) / (1 - (1 / 2 : ℝ)) := by
    rw [ProbabilityTheory.mgf]
    exact gaussianMass_centered_mgf_factorization
      (p := p) (q := q) (σ := σ) (θ := (1 / 2 : ℝ)) (by norm_num)
  have hN_nonneg : 0 ≤ N := by
    unfold N bipartiteDimension sampleDimension
    positivity
  have hprod :
      (∏ _α : σ, ∏ _i : RandomMatrixModel.BipIndex p q,
          Real.exp (-(1 / 2 : ℝ)) / (1 - (1 / 2 : ℝ))) =
        Real.exp ((Real.log 2 - 1 / 2) * N) := by
    have hfac : Real.exp (-(1 / 2 : ℝ)) / (1 - (1 / 2 : ℝ)) =
        Real.exp (Real.log 2 - 1 / 2) := by
      have hhalf : (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by ring
      rw [hhalf]
      calc
        Real.exp (-(1 / 2 : ℝ)) / (1 / 2 : ℝ) = Real.exp (-(1 / 2 : ℝ)) * 2 := by
          rw [div_eq_mul_inv]
          norm_num
        _ = Real.exp (-(1 / 2 : ℝ)) * Real.exp (Real.log 2) := by
              rw [Real.exp_log (by positivity : (0 : ℝ) < 2)]
        _ = Real.exp (Real.log 2 - 1 / 2) := by
              rw [← Real.exp_add]
              congr 1
              ring
    rw [hfac]
    calc
      (∏ _α : σ, ∏ _i : RandomMatrixModel.BipIndex p q, Real.exp (Real.log 2 - 1 / 2))
          = ∏ _α : σ,
              Real.exp (∑ _i : RandomMatrixModel.BipIndex p q, (Real.log 2 - 1 / 2)) := by
              apply Finset.prod_congr rfl
              intro α hα
              rw [← Real.exp_sum]
      _ = Real.exp
            (∑ _α : σ, ∑ _i : RandomMatrixModel.BipIndex p q, (Real.log 2 - 1 / 2)) := by
            rw [← Real.exp_sum]
      _ = Real.exp ((Real.log 2 - 1 / 2) * N) := by
            congr 1
            simp [N, bipartiteDimension, sampleDimension, Finset.sum_const,
              nsmul_eq_mul, mul_assoc, mul_comm]
            ring_nf
  have hset :
      {ω | 2 * bipartiteDimension p q * sampleDimension σ ≤ gaussianMass p q σ ω} =
        {ω | N ≤ X ω} := by
    ext ω
    dsimp [X, N]
    constructor <;> intro h <;> linarith
  rw [hset]
  calc
    (gaussianMeasure p q σ).real {ω | N ≤ X ω} ≤
        Real.exp (-((1 / 2 : ℝ) * N)) *
          ProbabilityTheory.mgf X (gaussianMeasure p q σ) (1 / 2 : ℝ) := by
            simpa [mul_assoc] using hchern
    _ = Real.exp (-((1 / 2 : ℝ) * N)) *
          ∏ _α : σ, ∏ _i : RandomMatrixModel.BipIndex p q,
            Real.exp (-(1 / 2 : ℝ)) / (1 - (1 / 2 : ℝ)) := by rw [hmgf]
    _ = Real.exp (-((1 - Real.log 2) * N)) := by
          rw [hprod]
          rw [← Real.exp_add]
          congr 1
          ring_nf
    _ ≤ Real.exp (-((1 / 6 : ℝ) * N)) := by
          apply Real.exp_le_exp.mpr
          have hlog : Real.log 2 < (5 / 6 : ℝ) := by
            linarith [Real.log_two_lt_d9]
          have hconst : (1 / 6 : ℝ) ≤ 1 - Real.log 2 := by
            linarith
          have hscaled : (1 / 6 : ℝ) * N ≤ (1 - Real.log 2) * N := by
            exact mul_le_mul_of_nonneg_right hconst hN_nonneg
          nlinarith
    _ = Real.exp (-((1 / 6 : ℝ) * bipartiteDimension p q * sampleDimension σ)) := by
          congr 1
          simp [N]
          ring_nf

/-- A concrete operator-norm bound `‖W‖∞ ≲ s` obtained from the mass upper
tail. -/
theorem wishart_upper_tail :
    (gaussianMeasure p q σ).real
        ((wishartOpNormEvent (p := p) (q := q) (σ := σ)
          (1 + 2 * bipartiteDimension p q))ᶜ) ≤
      Real.exp (-((1 / 6 : ℝ) * bipartiteDimension p q)) := by
  haveI : IsProbabilityMeasure (gaussianMeasure p q σ) := by
    rw [gaussianMeasure_eq]
    infer_instance
  by_cases hs : Fintype.card σ = 0
  · have hempty :
      ((wishartOpNormEvent (p := p) (q := q) (σ := σ)
        (1 + 2 * bipartiteDimension p q))ᶜ) = ∅ := by
      have hC : 0 ≤ 1 + 2 * bipartiteDimension p q := by
        have hD : 0 ≤ bipartiteDimension p q := by
          unfold bipartiteDimension
          positivity
        nlinarith
      simpa using
        wishartOpNormEvent_compl_eq_empty_of_card_eq_zero
          (p := p) (q := q) (σ := σ) hs hC
    rw [hempty]
    simpa using (show (0 : ℝ) ≤ Real.exp (-((1 / 6 : ℝ) * bipartiteDimension p q)) from
      le_of_lt (Real.exp_pos _))
  have hsubset :
      ((wishartOpNormEvent (p := p) (q := q) (σ := σ)
        (1 + 2 * bipartiteDimension p q))ᶜ) ⊆
        {ω | 2 * bipartiteDimension p q * sampleDimension σ ≤ gaussianMass p q σ ω} := by
    intro ω hω
    have hw :
        (1 + 2 * bipartiteDimension p q) * sampleDimension σ < wishartOpNorm p q σ ω := by
      simpa [wishartOpNormEvent] using hω
    have hmass := wishartOpNorm_le_gaussianMass (p := p) (q := q) (σ := σ) ω
    have hsone : (1 : ℝ) ≤ sampleDimension σ := by
      unfold sampleDimension
      exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hs)
    have hscaled :
        2 * bipartiteDimension p q * sampleDimension σ ≤
          (1 + 2 * bipartiteDimension p q) * sampleDimension σ := by
      have hs_nonneg : 0 ≤ sampleDimension σ := by
        unfold sampleDimension
        positivity
      nlinarith
    exact le_trans hscaled (le_of_lt (lt_of_lt_of_le hw hmass))
  calc
    (gaussianMeasure p q σ).real
        ((wishartOpNormEvent (p := p) (q := q) (σ := σ)
          (1 + 2 * bipartiteDimension p q))ᶜ) ≤
        (gaussianMeasure p q σ).real
          {ω | 2 * bipartiteDimension p q * sampleDimension σ ≤ gaussianMass p q σ ω} := by
            exact measureReal_mono
              (h₂ := (measure_lt_top (gaussianMeasure p q σ) _).ne) hsubset
    _ ≤ Real.exp (-((1 / 6 : ℝ) * bipartiteDimension p q * sampleDimension σ)) :=
          gaussianMass_upper_tail (p := p) (q := q) (σ := σ)
    _ ≤ Real.exp (-((1 / 6 : ℝ) * bipartiteDimension p q)) := by
          apply Real.exp_le_exp.mpr
          have hsone : (1 : ℝ) ≤ sampleDimension σ := by
            unfold sampleDimension
            exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hs)
          have hD_nonneg : 0 ≤ bipartiteDimension p q := by
            unfold bipartiteDimension
            positivity
          have hscaled :
              (1 / 6 : ℝ) * bipartiteDimension p q ≤
                (1 / 6 : ℝ) * bipartiteDimension p q * sampleDimension σ := by
            nlinarith
          nlinarith

/-- The same crude mass comparison also yields a concrete upper tail for
`‖W^Γ‖∞`. -/
theorem wishartGamma_upper_tail :
    (gaussianMeasure p q σ).real
        ((wishartGammaOpNormEvent (p := p) (q := q) (σ := σ)
          (1 + 2 * bipartiteDimension p q))ᶜ) ≤
      Real.exp (-((1 / 6 : ℝ) * bipartiteDimension p q)) := by
  haveI : IsProbabilityMeasure (gaussianMeasure p q σ) := by
    rw [gaussianMeasure_eq]
    infer_instance
  by_cases hs : Fintype.card σ = 0
  · have hempty :
      ((wishartGammaOpNormEvent (p := p) (q := q) (σ := σ)
        (1 + 2 * bipartiteDimension p q))ᶜ) = ∅ := by
      have hC : 0 ≤ 1 + 2 * bipartiteDimension p q := by
        have hD : 0 ≤ bipartiteDimension p q := by
          unfold bipartiteDimension
          positivity
        nlinarith
      simpa using
        wishartGammaOpNormEvent_compl_eq_empty_of_card_eq_zero
          (p := p) (q := q) (σ := σ) hs hC
    rw [hempty]
    simpa using (show (0 : ℝ) ≤ Real.exp (-((1 / 6 : ℝ) * bipartiteDimension p q)) from
      le_of_lt (Real.exp_pos _))
  have hsubset :
      ((wishartGammaOpNormEvent (p := p) (q := q) (σ := σ)
        (1 + 2 * bipartiteDimension p q))ᶜ) ⊆
        {ω | 2 * bipartiteDimension p q * sampleDimension σ ≤ gaussianMass p q σ ω} := by
    intro ω hω
    have hw :
        (1 + 2 * bipartiteDimension p q) * sampleDimension σ < wishartGammaOpNorm p q σ ω := by
      simpa [wishartGammaOpNormEvent] using hω
    have hmass := wishartGammaOpNorm_le_gaussianMass (p := p) (q := q) (σ := σ) ω
    have hsone : (1 : ℝ) ≤ sampleDimension σ := by
      unfold sampleDimension
      exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hs)
    have hscaled :
        2 * bipartiteDimension p q * sampleDimension σ ≤
          (1 + 2 * bipartiteDimension p q) * sampleDimension σ := by
      have hs_nonneg : 0 ≤ sampleDimension σ := by
        unfold sampleDimension
        positivity
      nlinarith
    exact le_trans hscaled (le_of_lt (lt_of_lt_of_le hw hmass))
  calc
    (gaussianMeasure p q σ).real
        ((wishartGammaOpNormEvent (p := p) (q := q) (σ := σ)
          (1 + 2 * bipartiteDimension p q))ᶜ) ≤
        (gaussianMeasure p q σ).real
          {ω | 2 * bipartiteDimension p q * sampleDimension σ ≤ gaussianMass p q σ ω} := by
            exact measureReal_mono
              (h₂ := (measure_lt_top (gaussianMeasure p q σ) _).ne) hsubset
    _ ≤ Real.exp (-((1 / 6 : ℝ) * bipartiteDimension p q * sampleDimension σ)) :=
          gaussianMass_upper_tail (p := p) (q := q) (σ := σ)
    _ ≤ Real.exp (-((1 / 6 : ℝ) * bipartiteDimension p q)) := by
          apply Real.exp_le_exp.mpr
          have hsone : (1 : ℝ) ≤ sampleDimension σ := by
            unfold sampleDimension
            exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hs)
          have hD_nonneg : 0 ≤ bipartiteDimension p q := by
            unfold bipartiteDimension
            positivity
          have hscaled :
              (1 / 6 : ℝ) * bipartiteDimension p q ≤
                (1 / 6 : ℝ) * bipartiteDimension p q * sampleDimension σ := by
            nlinarith
          nlinarith

/-- Net-lifted operator-norm tail for the normalized Wishart matrix. -/
theorem wishart_upper_tail_netLifted :
    (gaussianMeasure p q σ).real
        ((wishartOpNormEvent (p := p) (q := q) (σ := σ)
          (2 + 128 * (bipartiteDimension p q + 1)))ᶜ) ≤
      Real.exp (-bipartiteDimension p q) := by
  classical
  haveI : IsProbabilityMeasure (gaussianMeasure p q σ) := by
    rw [gaussianMeasure_eq]
    infer_instance
  by_cases hs : Fintype.card σ = 0
  · have hempty :
      ((wishartOpNormEvent (p := p) (q := q) (σ := σ)
        (2 + 128 * (bipartiteDimension p q + 1)))ᶜ) = ∅ := by
      have hC : 0 ≤ 2 + 128 * (bipartiteDimension p q + 1) := by
        have hD : 0 ≤ bipartiteDimension p q := by
          unfold bipartiteDimension
          positivity
        nlinarith
      simpa using
        wishartOpNormEvent_compl_eq_empty_of_card_eq_zero
          (p := p) (q := q) (σ := σ) hs hC
    rw [hempty]
    simpa using (show (0 : ℝ) ≤ Real.exp (-bipartiteDimension p q) from
      le_of_lt (Real.exp_pos _))
  · have hsNat : Fintype.card σ ≠ 0 := by
      intro hzero
      apply hs
      simpa [sampleDimension] using hzero
    have hsone : (1 : ℝ) ≤ sampleDimension σ := by
      unfold sampleDimension
      exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hsNat)
    by_cases hι : Nonempty (RandomMatrixModel.BipIndex p q)
    · letI : Nonempty (RandomMatrixModel.BipIndex p q) := hι
      rcases exists_quarter_net_unit_sphere_card_le_pow
          (ι := RandomMatrixModel.BipIndex p q) with
        ⟨N, hNfinite, hnet, hNencard⟩
      let D : ℝ := bipartiteDimension p q
      let s : ℝ := sampleDimension σ
      let X : Metric.sphere (0 : BipVector p q) 1 → Ω p q σ → ℝ :=
        fun u ω =>
          canonicalCenteredQuadraticFormSum (p := p) (q := q) (σ := σ)
            (rankOneProjector (p := p) (q := q) (u : BipVector p q)) ω
      have hD_nonneg : 0 ≤ D := by
        unfold D bipartiteDimension
        positivity
      have hcard_le : (hNfinite.toFinset.card : ℝ) ≤ Real.exp (7 * D) := by
        simpa [D, bipartiteDimension, mul_comm, mul_left_comm, mul_assoc] using
          finite_card_real_le_exp_seven_mul
            (ι := RandomMatrixModel.BipIndex p q) hNfinite hNencard
      have hfixed :
          ∀ u ∈ hNfinite.toFinset,
            (gaussianMeasure p q σ).real
              {ω | 64 * (D + 1) * s ≤ |X u ω|} ≤
            2 * Real.exp (-((8 : ℝ) * (D + 1) * s)) := by
        intro u hu
        have htpos : 0 < 64 * (D + 1) := by
          nlinarith [hD_nonneg]
        have htail :=
          rankOneProjectorCenteredBernsteinStatement (p := p) (q := q) (σ := σ)
            u (t := 64 * (D + 1)) htpos
        have hmin : min ((64 * (D + 1)) ^ 2) (64 * (D + 1)) = 64 * (D + 1) := by
          apply min_eq_right
          have h64 : (1 : ℝ) ≤ 64 * (D + 1) := by nlinarith [hD_nonneg]
          nlinarith
        have htail' :
            (gaussianMeasure p q σ).real
                {ω | 64 * (D + 1) * s ≤ |X u ω|} ≤
              2 * Real.exp (-((8 : ℝ) * (D + 1) * s)) := by
          have htail1 :
              (gaussianMeasure p q σ).real
                  {ω | 64 * (D + 1) * s ≤ |X u ω|} ≤
                2 * Real.exp
                  (-(8⁻¹ * (64 * ((D + 1) * sampleDimension σ)))) := by
            simpa [X, D, s, hmin, mul_assoc, mul_left_comm, mul_comm] using htail
          have hrewrite :
              (8⁻¹ : ℝ) * (64 * ((D + 1) * sampleDimension σ)) =
                (8 : ℝ) * (D + 1) * s := by
            rw [show sampleDimension σ = s by rfl]
            have h8 : (1 / 8 : ℝ) * 64 = 8 := by norm_num
            nlinarith [h8]
          simpa [hrewrite, mul_assoc, mul_left_comm, mul_comm] using htail1
        exact htail'
      have hfixed_drop_s :
          ∀ u ∈ hNfinite.toFinset,
            (gaussianMeasure p q σ).real
              {ω | 64 * (D + 1) * s ≤ |X u ω|} ≤
            2 * Real.exp (-((8 : ℝ) * (D + 1))) := by
        intro u hu
        have htail := hfixed u hu
        have hdrop : 2 * Real.exp (-((8 : ℝ) * (D + 1) * s)) ≤
            2 * Real.exp (-((8 : ℝ) * (D + 1))) := by
          have hexp :
              Real.exp (-((8 : ℝ) * (D + 1) * s)) ≤
                Real.exp (-((8 : ℝ) * (D + 1))) := by
            apply Real.exp_le_exp.mpr
            nlinarith [hsone, hD_nonneg]
          exact mul_le_mul_of_nonneg_left hexp (by positivity)
        exact le_trans htail hdrop
      have hunion :
          (gaussianMeasure p q σ).real
              (⋃ u ∈ hNfinite.toFinset, {ω | 64 * (D + 1) * s ≤ |X u ω|}) ≤
            Real.exp (-D) := by
        calc
          (gaussianMeasure p q σ).real
              (⋃ u ∈ hNfinite.toFinset, {ω | 64 * (D + 1) * s ≤ |X u ω|}) ≤
              ∑ u ∈ hNfinite.toFinset,
                (gaussianMeasure p q σ).real
                  {ω | 64 * (D + 1) * s ≤ |X u ω|} := by
                simpa using
                  (measureReal_biUnion_finset_le (μ := gaussianMeasure p q σ)
                    (s := hNfinite.toFinset)
                    (f := fun u : Metric.sphere (0 : BipVector p q) 1 =>
                      {ω | 64 * (D + 1) * s ≤ |X u ω|}))
          _ ≤ ∑ u ∈ hNfinite.toFinset, 2 * Real.exp (-((8 : ℝ) * (D + 1))) := by
                refine Finset.sum_le_sum ?_
                intro u hu
                exact hfixed_drop_s u hu
          _ = (hNfinite.toFinset.card : ℝ) * (2 * Real.exp (-((8 : ℝ) * (D + 1)))) := by
                simp [Finset.sum_const, mul_assoc, mul_comm]
          _ ≤ Real.exp (7 * D) * (2 * Real.exp (-((8 : ℝ) * (D + 1)))) := by
                gcongr
          _ ≤ Real.exp (7 * D) * Real.exp 1 * Real.exp (-((8 : ℝ) * (D + 1))) := by
                have h2exp :
                    2 * Real.exp (-((8 : ℝ) * (D + 1))) ≤
                      Real.exp 1 * Real.exp (-((8 : ℝ) * (D + 1))) := by
                  have h2 : (2 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_two.le
                  have hnonneg : 0 ≤ Real.exp (-((8 : ℝ) * (D + 1))) := by positivity
                  nlinarith
                simpa [mul_assoc] using
                  (mul_le_mul_of_nonneg_left h2exp (Real.exp_pos _).le)
          _ = Real.exp (7 * D + 1 - (8 * (D + 1))) := by
                rw [← Real.exp_add, ← Real.exp_add]
                congr 1
          _ ≤ Real.exp (-D) := by
                apply Real.exp_le_exp.mpr
                nlinarith
      have hgood :
            (gaussianMeasure p q σ).real
                ((wishartOpNormEvent (p := p) (q := q) (σ := σ)
                  (2 + 128 * (D + 1)))ᶜ) ≤
              (gaussianMeasure p q σ).real
                (⋃ u ∈ hNfinite.toFinset, {ω | 64 * (D + 1) * s ≤ |X u ω|}) := by
          refine measureReal_mono (h₂ := (measure_lt_top (gaussianMeasure p q σ) _).ne) ?_
          intro ω hω
          by_contra hbad
          let A : BipMatrix p q := wishart (gaussianMatrix p q σ ω)
          have hHerm : A.IsHermitian := by
            simpa [A] using
              wishart_isHermitian (p := p) (q := q) (σ := σ)
                (gaussianMatrix p q σ ω)
          have hnetbound : ∀ u ∈ N, |quadraticForm A u| ≤ 1 + 64 * (D + 1) := by
            intro u huN
            have huFin : u ∈ hNfinite.toFinset := by
              rw [Set.Finite.mem_toFinset]
              exact huN
            have hnot : ω ∉ {ω | 64 * (D + 1) * s ≤ |X u ω|} := by
              intro hmem
              have hmemUnion : ω ∈ ⋃ u ∈ hNfinite.toFinset, {ω | 64 * (D + 1) * s ≤ |X u ω|} := by
                exact Set.mem_biUnion huFin hmem
              exact hbad hmemUnion
            have hltX : |X u ω| < 64 * (D + 1) * s := lt_of_not_ge hnot
            have hbridge :=
              canonicalCenteredQuadraticFormSum_rankOneProjector_eq_sampleDimension_mul_quadraticForm_wishart_sub_one
                (p := p) (q := q) (σ := σ) (u := u) (ω := ω)
            have hdiff : |quadraticForm A (u : BipVector p q) - 1| < 64 * (D + 1) := by
              have hspos : 0 < s := by linarith [hsone]
              have hXeq : X u ω = s * (quadraticForm A (u : BipVector p q) - 1) := by
                simpa [X, s, A, hbridge, mul_comm, mul_left_comm, mul_assoc] using hbridge
              have hmul :
                  |quadraticForm A (u : BipVector p q) - 1| * s <
                    64 * (D + 1) * s := by
                have htmp : |s * (quadraticForm A (u : BipVector p q) - 1)| <
                    64 * (D + 1) * s := by
                  simpa [hXeq] using hltX
                simpa [abs_mul, abs_of_nonneg (by positivity : 0 ≤ s), mul_comm, mul_left_comm,
                  mul_assoc] using htmp
              exact lt_of_mul_lt_mul_right hmul hspos.le
            have hnetbound_lt : |quadraticForm A (u : BipVector p q)| < 1 + 64 * (D + 1) := by
              calc
                |quadraticForm A (u : BipVector p q)| =
                    |(quadraticForm A (u : BipVector p q) - 1) + 1| := by ring_nf
                _ ≤ |quadraticForm A (u : BipVector p q) - 1| + 1 := by
                  have habs := abs_add_le (quadraticForm A (u : BipVector p q) - 1) (1 : ℝ)
                  simpa using habs
                _ < 64 * (D + 1) + 1 := by linarith
                _ = 1 + 64 * (D + 1) := by ring_nf
            exact le_of_lt hnetbound_lt
          have hN_nonempty : N.Nonempty := by
            obtain ⟨x₀⟩ :=
              NormedSpace.sphere_nonempty_rclike
                (𝕜 := ℂ) (E := BipVector p q) (r := (1 : ℝ)) zero_le_one
            rcases hnet x₀ with ⟨u, huN, _⟩
            exact ⟨u, huN⟩
          have hsup :
              HighDimensionalProbability.netQuadraticSup
                (Matrix.toEuclideanCLM (n := BipIndex p q) (𝕜 := ℂ) A) N ≤
                1 + 64 * (D + 1) := by
            refine HighDimensionalProbability.netQuadraticSup_le_of_forall_le
              (T := Matrix.toEuclideanCLM (n := BipIndex p q) (𝕜 := ℂ) A)
              (N := N) hN_nonempty ?_
            intro u huN
            simpa [quadraticForm] using hnetbound u huN
          have hOp :
              opNorm A ≤ 2 * (1 + 64 * (D + 1)) := by
            calc
              opNorm A ≤
                  2 * HighDimensionalProbability.netQuadraticSup
                    (Matrix.toEuclideanCLM (n := BipIndex p q) (𝕜 := ℂ) A) N := by
                    exact opNorm_le_two_mul_netQuadraticSup
                      (A := A) hHerm hnet
              _ ≤ 2 * (1 + 64 * (D + 1)) := by
                    exact mul_le_mul_of_nonneg_left hsup (by positivity)
          have hOpEvent :
              wishartOpNorm p q σ ω ≤
                (2 + 128 * (D + 1)) * sampleDimension σ := by
            have hOp' : wishartOpNorm p q σ ω ≤ 2 * (1 + 64 * (D + 1)) := by
              simpa [wishartOpNorm, opNorm, A, D] using hOp
            nlinarith [hsone, hOp']
          exact hω (by simpa [wishartOpNormEvent] using hOpEvent)
      calc
        (gaussianMeasure p q σ).real
            ((wishartOpNormEvent (p := p) (q := q) (σ := σ)
              (2 + 128 * (D + 1)))ᶜ) ≤
            (gaussianMeasure p q σ).real
              (⋃ u ∈ hNfinite.toFinset, {ω | 64 * (D + 1) * s ≤ |X u ω|}) := hgood
        _ ≤ Real.exp (-D) := hunion
    · haveI : IsEmpty (RandomMatrixModel.BipIndex p q) := by
        exact not_nonempty_iff.mp hι
      have hC_nonneg : 0 ≤ 2 + 128 * (bipartiteDimension p q + 1) := by
        unfold bipartiteDimension
        positivity
      have hempty :
          ((wishartOpNormEvent (p := p) (q := q) (σ := σ)
            (2 + 128 * (bipartiteDimension p q + 1)))ᶜ) = ∅ := by
        simpa using
          wishartOpNormEvent_compl_eq_empty_of_isEmpty_bipIndex
            (p := p) (q := q) (σ := σ) hC_nonneg
      rw [hempty]
      simpa using
        (show (0 : ℝ) ≤ Real.exp (-bipartiteDimension p q) from
          le_of_lt (Real.exp_pos _))

/-! ### Sharp Quarter-Net Lift -/

/-- Net-lifted operator-norm tail for the partial-transposed normalized Wishart
matrix.  This is the quarter-net upgrade of the fixed-vector Bernstein bound
with an explicit dimension-free exponent `exp(-D)` and a linear-in-`D`
operator threshold. -/
theorem wishartGamma_upper_tail_netLifted :
    (gaussianMeasure p q σ).real
        ((wishartGammaOpNormEvent (p := p) (q := q) (σ := σ)
          (2 + 128 * (bipartiteDimension p q + 1)))ᶜ) ≤
      Real.exp (-bipartiteDimension p q) := by
  classical
  haveI : IsProbabilityMeasure (gaussianMeasure p q σ) := by
    rw [gaussianMeasure_eq]
    infer_instance
  by_cases hs : Fintype.card σ = 0
  · have hempty :
        ((wishartGammaOpNormEvent (p := p) (q := q) (σ := σ)
          (2 + 128 * (bipartiteDimension p q + 1)))ᶜ) = ∅ := by
      have hC : 0 ≤ 2 + 128 * (bipartiteDimension p q + 1) := by
        have hD : 0 ≤ bipartiteDimension p q := by
          unfold bipartiteDimension
          positivity
        nlinarith
      simpa using
        wishartGammaOpNormEvent_compl_eq_empty_of_card_eq_zero
          (p := p) (q := q) (σ := σ) hs hC
    rw [hempty]
    simpa using (show (0 : ℝ) ≤ Real.exp (-bipartiteDimension p q) from
      le_of_lt (Real.exp_pos _))
  · have hsNat : Fintype.card σ ≠ 0 := by
      intro hzero
      apply hs
      simpa [sampleDimension] using hzero
    have hsone : (1 : ℝ) ≤ sampleDimension σ := by
      unfold sampleDimension
      exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hsNat)
    by_cases hι : Nonempty (RandomMatrixModel.BipIndex p q)
    · letI : Nonempty (RandomMatrixModel.BipIndex p q) := hι
      rcases exists_quarter_net_unit_sphere_card_le_pow
          (ι := RandomMatrixModel.BipIndex p q) with
        ⟨N, hNfinite, hnet, hNencard⟩
      let D : ℝ := bipartiteDimension p q
      let s : ℝ := sampleDimension σ
      let X : Metric.sphere (0 : BipVector p q) 1 → Ω p q σ → ℝ :=
        fun u ω =>
          fixedVectorWishartGammaCenteredSum (p := p) (q := q) (σ := σ)
            (u : BipVector p q) ω
      have hD_nonneg : 0 ≤ D := by
        unfold D bipartiteDimension
        positivity
      have hcard_le : (hNfinite.toFinset.card : ℝ) ≤ Real.exp (7 * D) := by
        simpa [D, bipartiteDimension, mul_comm, mul_left_comm, mul_assoc] using
          finite_card_real_le_exp_seven_mul
            (ι := RandomMatrixModel.BipIndex p q) hNfinite hNencard
      have hfixed :
          ∀ u ∈ hNfinite.toFinset,
            (gaussianMeasure p q σ).real
              {ω | 64 * (D + 1) * s ≤
                |X u ω|} ≤
            2 * Real.exp (-((8 : ℝ) * (D + 1) * s)) := by
        intro u hu
        have htpos : 0 < 64 * (D + 1) := by
          nlinarith [hD_nonneg]
        have htail :=
          FixedVectorWishartGammaBernsteinStatement (p := p) (q := q) (σ := σ)
            (u := u) (t := 64 * (D + 1)) htpos
        have hmin : min ((64 * (D + 1)) ^ 2) (64 * (D + 1)) = 64 * (D + 1) := by
          apply min_eq_right
          have h64 : (1 : ℝ) ≤ 64 * (D + 1) := by nlinarith [hD_nonneg]
          nlinarith
        have htail' :
            (gaussianMeasure p q σ).real
                {ω | 64 * (D + 1) * s ≤
                  |X u ω|} ≤
              2 * Real.exp (-((8 : ℝ) * (D + 1) * s)) := by
          have htail1 :
              (gaussianMeasure p q σ).real
                  {ω | 64 * (D + 1) * s ≤
                    |X u ω|} ≤
                2 * Real.exp
                  (-(8⁻¹ * (64 * ((D + 1) * sampleDimension σ)))) := by
            simpa [X, D, s, hmin, mul_assoc, mul_left_comm, mul_comm] using htail
          have hrewrite :
              (8⁻¹ : ℝ) * (64 * ((D + 1) * sampleDimension σ)) =
                (8 : ℝ) * (D + 1) * s := by
            rw [show sampleDimension σ = s by rfl]
            have h8 : (1 / 8 : ℝ) * 64 = 8 := by norm_num
            nlinarith [h8]
          simpa [hrewrite, mul_assoc, mul_left_comm, mul_comm] using htail1
        exact htail'
      have hfixed_drop_s :
          ∀ u ∈ hNfinite.toFinset,
            (gaussianMeasure p q σ).real
              {ω | 64 * (D + 1) * s ≤
                |X u ω|} ≤
            2 * Real.exp (-((8 : ℝ) * (D + 1))) := by
        intro u hu
        have htail := hfixed u hu
        have hdrop : 2 * Real.exp (-((8 : ℝ) * (D + 1) * s)) ≤
            2 * Real.exp (-((8 : ℝ) * (D + 1))) := by
          have hexp :
              Real.exp (-((8 : ℝ) * (D + 1) * s)) ≤
                Real.exp (-((8 : ℝ) * (D + 1))) := by
            apply Real.exp_le_exp.mpr
            nlinarith [hsone, hD_nonneg]
          exact mul_le_mul_of_nonneg_left hexp (by positivity)
        exact le_trans htail hdrop
      have hunion :
          (gaussianMeasure p q σ).real
              (⋃ u ∈ hNfinite.toFinset, {ω | 64 * (D + 1) * s ≤ |X u ω|}) ≤
            Real.exp (-D) := by
        calc
          (gaussianMeasure p q σ).real
              (⋃ u ∈ hNfinite.toFinset, {ω | 64 * (D + 1) * s ≤ |X u ω|}) ≤
              ∑ u ∈ hNfinite.toFinset,
                (gaussianMeasure p q σ).real
                  {ω | 64 * (D + 1) * s ≤ |X u ω|} := by
                simpa using
                  (measureReal_biUnion_finset_le (μ := gaussianMeasure p q σ)
                    (s := hNfinite.toFinset)
                    (f := fun u : Metric.sphere (0 : BipVector p q) 1 =>
                      {ω | 64 * (D + 1) * s ≤ |X u ω|}))
          _ ≤ ∑ u ∈ hNfinite.toFinset, 2 * Real.exp (-((8 : ℝ) * (D + 1))) := by
                refine Finset.sum_le_sum ?_
                intro u hu
                exact hfixed_drop_s u hu
          _ = (hNfinite.toFinset.card : ℝ) * (2 * Real.exp (-((8 : ℝ) * (D + 1)))) := by
                simp [Finset.sum_const, mul_assoc, mul_comm]
          _ ≤ Real.exp (7 * D) * (2 * Real.exp (-((8 : ℝ) * (D + 1)))) := by
                gcongr
          _ ≤ Real.exp (7 * D) * Real.exp 1 * Real.exp (-((8 : ℝ) * (D + 1))) := by
                have h2exp :
                    2 * Real.exp (-((8 : ℝ) * (D + 1))) ≤
                      Real.exp 1 * Real.exp (-((8 : ℝ) * (D + 1))) := by
                  have h2 : (2 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_two.le
                  have hnonneg : 0 ≤ Real.exp (-((8 : ℝ) * (D + 1))) := by positivity
                  nlinarith
                simpa [mul_assoc] using
                  (mul_le_mul_of_nonneg_left h2exp (Real.exp_pos _).le)
          _ = Real.exp (7 * D + 1 - (8 * (D + 1))) := by
                rw [← Real.exp_add, ← Real.exp_add]
                congr 1
          _ ≤ Real.exp (-D) := by
                apply Real.exp_le_exp.mpr
                nlinarith
      have hgood :
            (gaussianMeasure p q σ).real
                ((wishartGammaOpNormEvent (p := p) (q := q) (σ := σ)
                  (2 + 128 * (D + 1)))ᶜ) ≤
              (gaussianMeasure p q σ).real
                (⋃ u ∈ hNfinite.toFinset, {ω | 64 * (D + 1) * s ≤ |X u ω|}) := by
          refine measureReal_mono (h₂ := (measure_lt_top (gaussianMeasure p q σ) _).ne) ?_
          intro ω hω
          by_contra hbad
          let A : BipMatrix p q := wishartGamma (gaussianMatrix p q σ ω)
          have hHerm : A.IsHermitian := by
            simpa [A] using
              wishartGamma_isHermitian (p := p) (q := q) (σ := σ)
                (gaussianMatrix p q σ ω)
          have hnetbound : ∀ u ∈ N, |quadraticForm A u| ≤ 1 + 64 * (D + 1) := by
            intro u huN
            have huFin : u ∈ hNfinite.toFinset := by
              rw [Set.Finite.mem_toFinset]
              exact huN
            have hnot : ω ∉ {ω | 64 * (D + 1) * s ≤ |X u ω|} := by
              intro hmem
              have hmemUnion : ω ∈ ⋃ u ∈ hNfinite.toFinset, {ω | 64 * (D + 1) * s ≤ |X u ω|} := by
                exact Set.mem_biUnion huFin hmem
              exact hbad hmemUnion
            have hltX : |X u ω| < 64 * (D + 1) * s := lt_of_not_ge hnot
            have hbridge :=
              fixedVectorWishartGammaCenteredSum_eq_sampleDimension_mul_quadraticForm_wishartGamma_sub_one
                (p := p) (q := q) (σ := σ) (u := (u : BipVector p q)) (ω := ω)
            have hdiff : |quadraticForm A (u : BipVector p q) - 1| < 64 * (D + 1) := by
              have hspos : 0 < s := by linarith [hsone]
              have hXeq : X u ω = s * (quadraticForm A (u : BipVector p q) - 1) := by
                simpa [X, s, A, hbridge, mul_comm, mul_left_comm, mul_assoc] using hbridge
              have hmul :
                  |quadraticForm A (u : BipVector p q) - 1| * s <
                    64 * (D + 1) * s := by
                have htmp : |s * (quadraticForm A (u : BipVector p q) - 1)| <
                    64 * (D + 1) * s := by
                  simpa [hXeq] using hltX
                simpa [abs_mul, abs_of_nonneg (by positivity : 0 ≤ s), mul_comm, mul_left_comm,
                  mul_assoc] using htmp
              exact lt_of_mul_lt_mul_right hmul hspos.le
            have hnetbound_lt : |quadraticForm A (u : BipVector p q)| < 1 + 64 * (D + 1) := by
              calc
                |quadraticForm A (u : BipVector p q)| =
                    |(quadraticForm A (u : BipVector p q) - 1) + 1| := by ring_nf
                _ ≤ |quadraticForm A (u : BipVector p q) - 1| + 1 := by
                  have habs := abs_add_le (quadraticForm A (u : BipVector p q) - 1) (1 : ℝ)
                  simpa using habs
                _ < 64 * (D + 1) + 1 := by linarith
                _ = 1 + 64 * (D + 1) := by ring_nf
            exact le_of_lt hnetbound_lt
          have hN_nonempty : N.Nonempty := by
            obtain ⟨x₀⟩ :=
              NormedSpace.sphere_nonempty_rclike
                (𝕜 := ℂ) (E := BipVector p q) (r := (1 : ℝ)) zero_le_one
            rcases hnet x₀ with ⟨u, huN, _⟩
            exact ⟨u, huN⟩
          have hsup :
              HighDimensionalProbability.netQuadraticSup
                (Matrix.toEuclideanCLM (n := BipIndex p q) (𝕜 := ℂ) A) N ≤
                1 + 64 * (D + 1) := by
            refine HighDimensionalProbability.netQuadraticSup_le_of_forall_le
              (T := Matrix.toEuclideanCLM (n := BipIndex p q) (𝕜 := ℂ) A)
              (N := N) hN_nonempty ?_
            intro u huN
            simpa [quadraticForm] using hnetbound u huN
          have hOp :
              opNorm A ≤ 2 * (1 + 64 * (D + 1)) := by
            calc
              opNorm A ≤
                  2 * HighDimensionalProbability.netQuadraticSup
                    (Matrix.toEuclideanCLM (n := BipIndex p q) (𝕜 := ℂ) A) N := by
                    exact opNorm_le_two_mul_netQuadraticSup
                      (A := A) hHerm hnet
              _ ≤ 2 * (1 + 64 * (D + 1)) := by
                    exact mul_le_mul_of_nonneg_left hsup (by positivity)
          have hOpEvent :
              wishartGammaOpNorm p q σ ω ≤
                (2 + 128 * (D + 1)) * sampleDimension σ := by
            have hOp' : wishartGammaOpNorm p q σ ω ≤ 2 * (1 + 64 * (D + 1)) := by
              simpa [wishartGammaOpNorm, opNorm, A, D] using hOp
            nlinarith [hsone, hOp']
          exact hω (by simpa [wishartGammaOpNormEvent] using hOpEvent)
      calc
        (gaussianMeasure p q σ).real
            ((wishartGammaOpNormEvent (p := p) (q := q) (σ := σ)
              (2 + 128 * (D + 1)))ᶜ) ≤
            (gaussianMeasure p q σ).real
              (⋃ u ∈ hNfinite.toFinset, {ω | 64 * (D + 1) * s ≤ |X u ω|}) := hgood
        _ ≤ Real.exp (-D) := hunion
    · haveI : IsEmpty (RandomMatrixModel.BipIndex p q) := by
        exact not_nonempty_iff.mp hι
      have hC_nonneg : 0 ≤ 2 + 128 * (bipartiteDimension p q + 1) := by
        unfold bipartiteDimension
        positivity
      have hempty :
          ((wishartGammaOpNormEvent (p := p) (q := q) (σ := σ)
            (2 + 128 * (bipartiteDimension p q + 1)))ᶜ) = ∅ := by
        simpa using
          wishartGammaOpNormEvent_compl_eq_empty_of_isEmpty_bipIndex
            (p := p) (q := q) (σ := σ) hC_nonneg
      rw [hempty]
      simpa using
        (show (0 : ℝ) ≤ Real.exp (-bipartiteDimension p q) from
          le_of_lt (Real.exp_pos _))

/-! ## Block 7: Canonical Concrete Package Assembly -/

/-- Canonical concrete high-probability package.

At the current stage of the development, the canonical exported package is the
fully proved package with the sharp net-lifted operator-norm tails and the
mass lower tail at exponent constant `1 / 6`. -/
noncomputable def concreteHighProbabilityBounds :
    ConcreteHighProbabilityBounds (p := p) (q := q) (σ := σ) where
  massConstant := 1 / 2
  wishartConstant := 2 + 128 * (bipartiteDimension p q + 1)
  gammaWishartConstant := 2 + 128 * (bipartiteDimension p q + 1)
  tailConstant := 1 / 6
  massConstant_pos := by positivity
  wishartConstant_pos := by nlinarith [bipartiteDimension_nonneg (p := p) (q := q)]
  gammaWishartConstant_pos := by nlinarith [bipartiteDimension_nonneg (p := p) (q := q)]
  tailConstant_pos := by positivity
  massLowerTail := gaussianMass_lower_tail (p := p) (q := q) (σ := σ)
  wishartUpperTail := by
    refine le_trans (wishart_upper_tail_netLifted (p := p) (q := q) (σ := σ)) ?_
    apply Real.exp_le_exp.mpr
    nlinarith [bipartiteDimension_nonneg (p := p) (q := q)]
  wishartGammaUpperTail := by
    refine le_trans (wishartGamma_upper_tail_netLifted (p := p) (q := q) (σ := σ)) ?_
    apply Real.exp_le_exp.mpr
    nlinarith [bipartiteDimension_nonneg (p := p) (q := q)]

/-- No-input existence of the canonical concrete high-probability package. -/
theorem ConcreteHighProbabilityBoundsStatement :
    Nonempty (ConcreteHighProbabilityBounds (p := p) (q := q) (σ := σ)) :=
  ⟨concreteHighProbabilityBounds (p := p) (q := q) (σ := σ)⟩

/-- Expanded no-input theorem for the canonical concrete package, with the
sharp operator constants visible in the statement and prefactor `C = 1` in each
exponential tail. -/
theorem ConcreteHighProbabilityBoundsExplicit :
    0 < (1 / 2 : ℝ) ∧
    0 < (2 + 128 * (bipartiteDimension p q + 1) : ℝ) ∧
    0 < (2 + 128 * (bipartiteDimension p q + 1) : ℝ) ∧
    0 < (1 / 6 : ℝ) ∧
    (gaussianMeasure p q σ).real
        ((gaussianMassLowerEvent (p := p) (q := q) (σ := σ) (1 / 2 : ℝ))ᶜ) ≤
      Real.exp (-((1 / 6 : ℝ) * bipartiteDimension p q * sampleDimension σ)) ∧
    (gaussianMeasure p q σ).real
        ((wishartOpNormEvent (p := p) (q := q) (σ := σ)
          (2 + 128 * (bipartiteDimension p q + 1)))ᶜ) ≤
      Real.exp (-((1 / 6 : ℝ) * bipartiteDimension p q)) ∧
    (gaussianMeasure p q σ).real
        ((wishartGammaOpNormEvent (p := p) (q := q) (σ := σ)
          (2 + 128 * (bipartiteDimension p q + 1)))ᶜ) ≤
      Real.exp (-((1 / 6 : ℝ) * bipartiteDimension p q)) := by
  have hD := bipartiteDimension_nonneg (p := p) (q := q)
  refine ⟨by positivity, ?_, ?_, by positivity, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · exact gaussianMass_lower_tail (p := p) (q := q) (σ := σ)
  · refine le_trans (wishart_upper_tail_netLifted (p := p) (q := q) (σ := σ)) ?_
    apply Real.exp_le_exp.mpr
    nlinarith
  · refine le_trans (wishartGamma_upper_tail_netLifted (p := p) (q := q) (σ := σ)) ?_
    apply Real.exp_le_exp.mpr
    nlinarith

end HighProbabilityBounds
end PptFactorization
