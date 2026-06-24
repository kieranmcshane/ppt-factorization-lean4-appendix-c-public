import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Measure.MeasureSpace
import PptFactorization.PartialTranspose

/-!
# Concrete finite-dimensional random-matrix model

This file introduces the deterministic matrix objects used by the PPT
high-dimensional-probability argument.  A probabilistic sample is represented
by a map into these finite-dimensional matrix spaces; the law-specific
statement "standard complex Gaussian" is not hidden here as an axiom or
opaque predicate.
-/

open Matrix
open MeasureTheory
open scoped Matrix.Norms.Frobenius
open scoped ComplexOrder

noncomputable section

namespace PptFactorization
namespace RandomMatrixModel

variable {p q σ Ω : Type*}
variable [Fintype p] [Fintype q] [Fintype σ]
variable [DecidableEq p] [DecidableEq q]

/-- The Hilbert-space index for a bipartite system `ℂ^p ⊗ ℂ^q`. -/
abbrev BipIndex (p q : Type*) := p × q

/-- A rectangular data matrix with rows indexed by the bipartite system and columns by samples. -/
abbrev SampleMatrix (p q σ : Type*) := Matrix (BipIndex p q) σ ℂ

/-- A square operator on the bipartite system. -/
abbrev BipMatrix (p q : Type*) := Matrix (BipIndex p q) (BipIndex p q) ℂ

/-- A random sample matrix over a probability space `Ω`. -/
abbrev RandomSampleMatrix (Ω p q σ : Type*) := Ω → SampleMatrix p q σ

/-- Frobenius/Hilbert--Schmidt norm of a rectangular sample matrix. -/
def frobeniusNorm (G : SampleMatrix p q σ) : ℝ :=
  ‖G‖

/-- Squared Frobenius mass `T = ‖G‖₂²`. -/
def frobeniusMass (G : SampleMatrix p q σ) : ℝ :=
  frobeniusNorm G ^ 2

/-- Normalized sample matrix `X = G / ‖G‖₂`, using Lean's total inverse at `G = 0`. -/
def normalizedSample (G : SampleMatrix p q σ) : SampleMatrix p q σ :=
  ((frobeniusNorm G)⁻¹ : ℂ) • G

/-- Density matrix associated to a rectangular sample matrix. -/
def densityMatrix (X : SampleMatrix p q σ) : BipMatrix p q :=
  X * Xᴴ

/-- The normalized density matrix `ρ_X`. -/
def rho (G : SampleMatrix p q σ) : BipMatrix p q :=
  densityMatrix (normalizedSample G)

/-- Wishart matrix `W = (1 / s) G Gᴴ`, where `s` is the number of columns. -/
def wishart (G : SampleMatrix p q σ) : BipMatrix p q :=
  ((Fintype.card σ : ℂ)⁻¹) • densityMatrix G

/-- Partial transpose on the second tensor factor. -/
def gamma (A : BipMatrix p q) : BipMatrix p q :=
  Matrix.partialTranspose A

/-- Partial transpose of the normalized density matrix. -/
def rhoGamma (G : SampleMatrix p q σ) : BipMatrix p q :=
  gamma (rho G)

/-- Partial transpose of the Wishart matrix. -/
def wishartGamma (G : SampleMatrix p q σ) : BipMatrix p q :=
  gamma (wishart G)

omit [DecidableEq p] [DecidableEq q] in
/-- Normalized partial transpose as an explicit scalar multiple of the
Wishart partial transpose.

This is the deterministic normalization bridge behind the induced-state model:
`ρ = GGᴴ / ‖G‖₂²`, while `W = GGᴴ / #σ`. -/
theorem rhoGamma_eq_card_mul_inv_frobeniusNorm_sq_smul_wishartGamma
    (hσ : 0 < Fintype.card σ) (G : SampleMatrix p q σ) :
    rhoGamma G =
      (((Fintype.card σ : ℂ) * ((frobeniusNorm G)⁻¹ : ℂ) ^ 2)) • wishartGamma G := by
  simp [rhoGamma, rho, densityMatrix, normalizedSample, gamma, wishartGamma, wishart,
    pow_two, smul_smul, mul_assoc]
  field_simp [show (Fintype.card σ : ℂ) ≠ 0 by exact_mod_cast ne_of_gt hσ]

omit [DecidableEq p] [DecidableEq q] in
/-- Frobenius-mass form of the induced-state/Wishart normalization bridge.

This is the same identity as
`rhoGamma_eq_card_mul_inv_frobeniusNorm_sq_smul_wishartGamma`, but with the
scalar written as `#σ / ‖G‖₂²`, the form used by concentration estimates for
the radial part. -/
theorem rhoGamma_eq_card_div_frobeniusMass_smul_wishartGamma
    (hσ : 0 < Fintype.card σ) (G : SampleMatrix p q σ) :
    rhoGamma G = (((Fintype.card σ : ℂ) / (frobeniusMass G : ℂ))) • wishartGamma G := by
  rw [rhoGamma_eq_card_mul_inv_frobeniusNorm_sq_smul_wishartGamma hσ G]
  congr 1
  simp [frobeniusMass, div_eq_mul_inv, pow_two]

/-- Centered trace-power bridge from the induced-state normalization to the
Wishart normalization.

The hard growing-moment estimate is usually Wishart-facing.  This identity
rewrites the exact trace observable in the `d^2ρ^Γ - I` endpoint as the same
centered trace power of a Frobenius-mass-scaled `W^Γ`. -/
theorem rhoGamma_centered_trace_re_eq_wishartGamma_frobeniusMass
    (D : ℝ) (hσ : 0 < Fintype.card σ) (G : SampleMatrix p q σ) (m : ℕ) :
    RCLike.re ((((D : ℂ) • rhoGamma G - 1) ^ m).trace) =
      RCLike.re ((((((D * (Fintype.card σ : ℝ) / frobeniusMass G : ℝ) : ℂ) •
        wishartGamma G - 1) ^ m).trace)) := by
  have hscaled : (D : ℂ) • rhoGamma G =
      (((D * (Fintype.card σ : ℝ) / frobeniusMass G : ℝ) : ℂ)) • wishartGamma G := by
    rw [rhoGamma_eq_card_div_frobeniusMass_smul_wishartGamma hσ G]
    simp [smul_smul, div_eq_mul_inv, mul_assoc]
  rw [hscaled]

/-- `ENNReal.ofReal` form of
`rhoGamma_centered_trace_re_eq_wishartGamma_frobeniusMass`, useful for
`lintegral` rewrites. -/
theorem rhoGamma_centered_trace_ofReal_eq_wishartGamma_frobeniusMass
    (D : ℝ) (hσ : 0 < Fintype.card σ) (G : SampleMatrix p q σ) (m : ℕ) :
    ENNReal.ofReal (RCLike.re ((((D : ℂ) • rhoGamma G - 1) ^ m).trace)) =
      ENNReal.ofReal
        (RCLike.re ((((((D * (Fintype.card σ : ℝ) / frobeniusMass G : ℝ) : ℂ) •
          wishartGamma G - 1) ^ m).trace))) := by
  exact congrArg ENNReal.ofReal
    (rhoGamma_centered_trace_re_eq_wishartGamma_frobeniusMass D hσ G m)

/-- Operator norm of a square matrix acting on Euclidean space. -/
def opNorm (A : BipMatrix p q) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := BipIndex p q) (𝕜 := ℂ) A‖

/-- The good event `Ω_M = {‖ρ_X‖∞ ≤ M/D ∧ ‖ρ_X^Γ‖∞ ≤ M/D}` for one sample. -/
def goodEvent (M D : ℝ) (G : SampleMatrix p q σ) : Prop :=
  opNorm (rho G) ≤ M / D ∧ opNorm (rhoGamma G) ≤ M / D

/-- The good event as a subset of an ambient sample space. -/
def goodSet (M D : ℝ) (G : RandomSampleMatrix Ω p q σ) : Set Ω :=
  {ω | goodEvent M D (G ω)}

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Partial transpose preserves Hermitian matrices. -/
theorem gamma_isHermitian {A : BipMatrix p q} (hA : A.IsHermitian) :
    (gamma A).IsHermitian := by
  change (Matrix.partialTranspose A)ᴴ = Matrix.partialTranspose A
  rw [← Matrix.partialTranspose_conjTranspose, hA.eq]

omit [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] in
/-- A sample density matrix is Hermitian. -/
theorem densityMatrix_isHermitian (X : SampleMatrix p q σ) :
    (densityMatrix X).IsHermitian := by
  simpa [densityMatrix] using Matrix.isHermitian_mul_conjTranspose_self X

omit [DecidableEq p] [DecidableEq q] in
/-- The normalized density matrix is Hermitian. -/
theorem rho_isHermitian (G : SampleMatrix p q σ) :
    (rho G).IsHermitian := by
  simpa [rho] using densityMatrix_isHermitian (normalizedSample G)

omit [DecidableEq p] [DecidableEq q] in
/-- The normalized partial transpose is Hermitian. -/
theorem rhoGamma_isHermitian (G : SampleMatrix p q σ) :
    (rhoGamma G).IsHermitian := by
  simpa [rhoGamma] using gamma_isHermitian (rho_isHermitian G)

/-- Real eigenvalue coordinates of the normalized partial transpose. -/
noncomputable def rhoGammaEigenvalues (G : SampleMatrix p q σ) : BipIndex p q → ℝ :=
  (rhoGamma_isHermitian G).eigenvalues

/-- Positivity of the normalized partial transpose is exactly nonnegativity of
its real Hermitian eigenvalue coordinates. -/
theorem rhoGamma_posSemidef_iff_eigenvalues_nonneg (G : SampleMatrix p q σ) :
    (rhoGamma G).PosSemidef ↔
      ∀ i : BipIndex p q, 0 ≤ rhoGammaEigenvalues G i := by
  simpa [rhoGammaEigenvalues, Pi.le_def] using
    (rhoGamma_isHermitian G).posSemidef_iff_eigenvalues_nonneg

/-- Eigenvalue-coordinate nonnegativity implies PPT positivity of `ρ^Γ`. -/
theorem rhoGamma_posSemidef_of_eigenvalues_nonneg (G : SampleMatrix p q σ)
    (hEig : ∀ i : BipIndex p q, 0 ≤ rhoGammaEigenvalues G i) :
    (rhoGamma G).PosSemidef :=
  (rhoGamma_posSemidef_iff_eigenvalues_nonneg G).2 hEig

/-- Scaled real eigenvalue coordinates, used for the `d^2 ρ^Γ` moment route. -/
noncomputable def scaledRhoGammaEigenvalues (D : ℝ) (G : SampleMatrix p q σ) :
    BipIndex p q → ℝ :=
  fun i => D * rhoGammaEigenvalues G i

/-- If `D > 0`, nonnegativity of the scaled eigenvalue coordinates implies
PPT positivity of the unscaled partial transpose. -/
theorem rhoGamma_posSemidef_of_scaled_eigenvalues_nonneg {D : ℝ} (hD : 0 < D)
    (G : SampleMatrix p q σ)
    (hEig : ∀ i : BipIndex p q, 0 ≤ scaledRhoGammaEigenvalues D G i) :
    (rhoGamma G).PosSemidef :=
  rhoGamma_posSemidef_of_eigenvalues_nonneg G fun i =>
    nonneg_of_mul_nonneg_right (by simpa [scaledRhoGammaEigenvalues] using hEig i) hD

/-- Concrete event bridge from matrix non-PPT to a negative scaled eigenvalue.

This is the model-facing adapter needed after the abstract finite-spectrum
moment theorem has controlled the event `∃ i, F_i < 0`. -/
theorem not_rhoGamma_posSemidef_subset_exists_scaled_eigenvalue_neg {D : ℝ}
    (hD : 0 < D) (G : RandomSampleMatrix Ω p q σ) :
    {ω : Ω | ¬ (rhoGamma (G ω)).PosSemidef} ⊆
      {ω : Ω | ∃ i : BipIndex p q, scaledRhoGammaEigenvalues D (G ω) i < 0} := by
  intro ω hnot
  by_contra hno
  exact hnot (rhoGamma_posSemidef_of_scaled_eigenvalues_nonneg hD (G ω) fun i =>
    le_of_not_gt fun hlt => hno ⟨i, hlt⟩)

/-- Measure form of
`not_rhoGamma_posSemidef_subset_exists_scaled_eigenvalue_neg`. -/
theorem measure_not_rhoGamma_posSemidef_le_exists_scaled_eigenvalue_neg
    [MeasurableSpace Ω] (μ : Measure Ω) {D : ℝ} (hD : 0 < D)
    (G : RandomSampleMatrix Ω p q σ) :
    μ {ω : Ω | ¬ (rhoGamma (G ω)).PosSemidef} ≤
      μ {ω : Ω | ∃ i : BipIndex p q, scaledRhoGammaEigenvalues D (G ω) i < 0} :=
  measure_mono (not_rhoGamma_posSemidef_subset_exists_scaled_eigenvalue_neg hD G)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
@[simp] theorem gamma_apply (A : BipMatrix p q) (i j : BipIndex p q) :
    gamma A i j = A (i.1, j.2) (j.1, i.2) :=
  rfl

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
@[simp] theorem gamma_gamma (A : BipMatrix p q) :
    gamma (gamma A) = A := by
  simp [gamma]

omit [DecidableEq p] [DecidableEq q] in
@[simp] theorem frobeniusNorm_gamma (A : BipMatrix p q) :
    frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) (gamma A) =
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) A := by
  simp [frobeniusNorm, gamma]

omit [DecidableEq p] [DecidableEq q] in
/-- Away from the zero sample, normalization puts the sample on the Frobenius unit sphere. -/
theorem frobeniusNorm_normalizedSample {G : SampleMatrix p q σ} (hG : G ≠ 0) :
    frobeniusNorm (normalizedSample G) = 1 := by
  simpa [frobeniusNorm, normalizedSample] using
    (norm_smul_inv_norm (𝕜 := ℂ) hG)

@[simp] theorem goodEvent_rho_le {M D : ℝ} {G : SampleMatrix p q σ}
    (hG : goodEvent M D G) :
    opNorm (rho G) ≤ M / D :=
  hG.1

@[simp] theorem goodEvent_rhoGamma_le {M D : ℝ} {G : SampleMatrix p q σ}
    (hG : goodEvent M D G) :
    opNorm (rhoGamma G) ≤ M / D :=
  hG.2

end RandomMatrixModel
end PptFactorization
