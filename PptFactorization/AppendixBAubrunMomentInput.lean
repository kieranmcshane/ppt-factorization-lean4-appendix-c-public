import PptFactorization.AppendixBNormalizedExpectations
import PptFactorization.AubrunMomentSpine
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Appendix B: Aubrun off-diagonal moment input

This file isolates the final Aubrun moment estimate needed for the
off-diagonal part of the partially transposed Wishart matrix.

The repo already proves the exact closed-walk/Wick expansion for the trace
moments of

`Z = W^Γ - diag(W^Γ)`.

What is still mathematically external to this file is the final Aubrun
combinatorial/moment estimate converting those Wick sums into the operator
norm expectation bound at the appendix scale.  We package that input explicitly
and prove the downstream radial/spherical wiring from it.
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

/-! ## The off-diagonal Gamma observable on the spherical model -/

omit [Fintype σ] in
/-- Off-diagonal projection as a complex-linear map on bipartite matrices. -/
def offDiagonalLinearMap : BipMatrix p q →ₗ[ℂ] BipMatrix p q where
  toFun := offDiagonal
  map_add' := by
    intro A B
    ext i j
    by_cases h : i = j <;> simp [h]
  map_smul' := by
    intro c A
    ext i j
    by_cases h : i = j <;> simp [h]

omit [Fintype σ] in
/-- Continuity of the off-diagonal projection. -/
theorem continuous_offDiagonal :
    Continuous (fun A : BipMatrix p q => offDiagonal A) := by
  simpa [offDiagonalLinearMap] using
    (offDiagonalLinearMap (p := p) (q := q)).continuous_of_finiteDimensional

/-- Off-diagonal part of the partial transpose of the raw density `XX*`. -/
def densityGammaOffDiagonal (X : SampleMatrix p q σ) : BipMatrix p q :=
  offDiagonal (gamma (densityMatrix X))

/-- Operator norm of the off-diagonal part of `(XX*)^Γ`. -/
def densityGammaOffDiagonalOpNorm (X : SampleMatrix p q σ) : ℝ :=
  opNorm (densityGammaOffDiagonal (p := p) (q := q) (σ := σ) X)

/-- Spherical mean of the off-diagonal Gamma observable. -/
def sphericalOffDiagonalGammaOpNormMean : ℝ :=
  ∫ X : SampleMatrix p q σ,
    densityGammaOffDiagonalOpNorm (p := p) (q := q) (σ := σ) X
    ∂gaussianSphericalSampleMeasure (p := p) (q := q) (σ := σ)

/-- Gaussian quadratic lift of the off-diagonal spherical Gamma observable. -/
def gaussianQuadraticOffDiagonalGammaLiftMean : ℝ :=
  ∫ ω : Ω p q σ,
    gaussianMass p q σ ω *
      densityGammaOffDiagonalOpNorm (p := p) (q := q) (σ := σ)
        (gaussianDirection (p := p) (q := q) (σ := σ) ω)
    ∂gaussianMeasure p q σ

/-- Continuity of the off-diagonal spherical Gamma observable. -/
theorem continuous_densityGammaOffDiagonalOpNorm :
    Continuous (densityGammaOffDiagonalOpNorm (p := p) (q := q) (σ := σ)) := by
  have hToEuclidean :
      Continuous (fun A : BipMatrix p q =>
        Matrix.toEuclideanCLM (n := BipIndex p q) (𝕜 := ℂ) A) := by
    exact
      (Matrix.toEuclideanCLM (n := BipIndex p q) (𝕜 := ℂ)).toAlgEquiv.toLinearMap
        |>.continuous_of_finiteDimensional
  have hDensity :
      Continuous (fun X : SampleMatrix p q σ => densityMatrix X) := by
    unfold densityMatrix
    fun_prop
  unfold densityGammaOffDiagonalOpNorm densityGammaOffDiagonal opNorm
  exact continuous_norm.comp
    (hToEuclidean.comp
      ((continuous_offDiagonal (p := p) (q := q)).comp
        ((continuous_gamma (p := p) (q := q)).comp hDensity)))

/-- Exact radial/spherical factorization for the off-diagonal Gamma
observable. -/
theorem gaussianQuadraticOffDiagonalGammaLiftMean_factorization_of_indep
    (hIndep :
      gaussianRadiusSq (p := p) (q := q) (σ := σ) ⟂ᵢ[gaussianMeasure p q σ]
        gaussianDirection (p := p) (q := q) (σ := σ)) :
    gaussianQuadraticOffDiagonalGammaLiftMean (p := p) (q := q) (σ := σ) =
      gaussianQuadraticRadialMean (p := p) (q := q) (σ := σ) *
        sphericalOffDiagonalGammaOpNormMean (p := p) (q := q) (σ := σ) := by
  simpa [gaussianQuadraticOffDiagonalGammaLiftMean, gaussianQuadraticRadialMean,
    sphericalOffDiagonalGammaOpNormMean] using
      gaussian_quadratic_radial_spherical_factorization_of_indep
        (p := p) (q := q) (σ := σ)
        (F := densityGammaOffDiagonalOpNorm (p := p) (q := q) (σ := σ))
        hIndep
        (continuous_densityGammaOffDiagonalOpNorm
          (p := p) (q := q) (σ := σ) |>.aestronglyMeasurable)

/-! ## Concrete Wick moment side already proved in the repo -/

/-- The off-diagonal projection preserves Hermitian matrices. -/
theorem offDiagonal_isHermitian
    {ι : Type*} [DecidableEq ι] (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) :
    (offDiagonal A).IsHermitian := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [offDiagonal]
  · have hentry : star (A j i) = A i j := by
      have h := congrArg (fun M : Matrix ι ι ℂ => M i j) hA.eq
      simpa using h
    have hji : j ≠ i := fun h => hij h.symm
    simp [offDiagonal, hij, hji, hentry]

/-- The concrete off-diagonal partially transposed Wishart matrix is Hermitian. -/
theorem wishartGammaOffDiagonal_isHermitian
    [DecidableEq σ] (G : SampleMatrix p q σ) :
    (wishartGammaOffDiagonal (p := p) (q := q) (σ := σ) G).IsHermitian := by
  exact offDiagonal_isHermitian
    (wishartGamma (p := p) (q := q) (σ := σ) G)
    (wishartGamma_isHermitian (p := p) (q := q) (σ := σ) G)

/-- Trace-power moment of the concrete off-diagonal partially transposed
Wishart matrix. -/
def gaussianWishartGammaOffDiagonalTraceMoment
    [DecidableEq σ] (m : ℕ) : ℂ :=
  ∫ ω : Ω p q σ,
    ((wishartGammaOffDiagonal (p := p) (q := q) (σ := σ)
        (gaussianMatrix p q σ ω)) ^ (m + 1)).trace
      ∂gaussianMeasure p q σ

/-- Exact-power trace moment.  The older `...TraceMoment m` is indexed by
`m + 1` because it is wired directly to the closed-walk expansion. -/
def gaussianWishartGammaOffDiagonalTraceMomentPower
    [DecidableEq σ] (m : ℕ) : ℂ :=
  ∫ ω : Ω p q σ,
    ((wishartGammaOffDiagonal (p := p) (q := q) (σ := σ)
        (gaussianMatrix p q σ ω)) ^ m).trace
      ∂gaussianMeasure p q σ

/-- Real exact-power trace moment, the quantity used by the spectral
trace-moment extraction for even Hermitian moments. -/
def gaussianWishartGammaOffDiagonalTraceMomentPowerReal
    [DecidableEq σ] (m : ℕ) : ℝ :=
  ∫ ω : Ω p q σ,
    RCLike.re
      (((wishartGammaOffDiagonal (p := p) (q := q) (σ := σ)
          (gaussianMatrix p q σ ω)) ^ m).trace)
      ∂gaussianMeasure p q σ

/-- Compatibility between exact-power trace moments and the closed-walk
`m + 1` indexing used by the Wick expansion. -/
theorem gaussianWishartGammaOffDiagonalTraceMomentPower_succ
    [DecidableEq σ] (m : ℕ) :
    gaussianWishartGammaOffDiagonalTraceMomentPower
        (p := p) (q := q) (σ := σ) (m + 1) =
      gaussianWishartGammaOffDiagonalTraceMoment
        (p := p) (q := q) (σ := σ) m := by
  rfl

/-- Operator-norm expectation of the concrete off-diagonal partially
transposed Wishart matrix. -/
def gaussianWishartGammaOffDiagonalOpNormMean : ℝ :=
  ∫ ω : Ω p q σ,
    opNorm
      (wishartGammaOffDiagonal (p := p) (q := q) (σ := σ)
        (gaussianMatrix p q σ ω))
      ∂gaussianMeasure p q σ

/-- The repo's Wick expansion, restated in the appendix namespace and on the
canonical Gaussian space used by the high-probability package. -/
theorem gaussianWishartGammaOffDiagonal_traceMoment_eq_wickSum
    [DecidableEq σ] (m : ℕ) :
    gaussianWishartGammaOffDiagonalTraceMoment
        (p := p) (q := q) (σ := σ) m =
      closedWalkWickSum
        (gaussianWishartGammaOffDiagonal_closedWalkMonomialExpansion
          (p := p) (q := q) (σ := σ) m) := by
  simpa [gaussianWishartGammaOffDiagonalTraceMoment, gaussianMeasure_eq,
    gaussianMatrix_apply] using
      expected_trace_pow_succ_wishartGammaOffDiagonal_eq_wick_sum
        (p := p) (q := q) (σ := σ) m

/-- Exact no-input surviving-contraction form of the same trace moment.  This is
the finite Wick side of Aubrun's Proposition 7.1, before the specific
polynomial encoding/counting estimate. -/
theorem gaussianWishartGammaOffDiagonal_traceMoment_eq_survivingPairing_sum
    [DecidableEq σ] (m : ℕ) :
    gaussianWishartGammaOffDiagonalTraceMoment
        (p := p) (q := q) (σ := σ) m =
      ∑ w : ClosedWalk (BipIndex p q) m,
        ∑ α : Fin (m + 1) → σ,
          pathGammaCoeff (p := p) (q := q) (σ := σ) w.1 w.1 w.2 α *
            (Fintype.card
              (SurvivingClosedWalkPairing
                (p := p) (q := q) (σ := σ) w α) : ℂ) := by
  simpa [gaussianWishartGammaOffDiagonalTraceMoment, gaussianMeasure_eq,
    gaussianMatrix_apply] using
      expected_trace_pow_succ_wishartGammaOffDiagonal_eq_survivingPairing_sum
        (p := p) (q := q) (σ := σ) m

/-- Immediate finite absolute-value bound obtained from the exact surviving
contraction sum.  The sharp Aubrun bound is the stronger combinatorial estimate
that controls this finite sum by
`(2 / s)^m (d + Q(m))^(m+2) (sqrt s + Q(m))^m`. -/
theorem gaussianWishartGammaOffDiagonal_traceMoment_norm_le_survivingPairing_sum_norm
    [DecidableEq σ] (m : ℕ) :
    ‖gaussianWishartGammaOffDiagonalTraceMoment
        (p := p) (q := q) (σ := σ) m‖ ≤
      ∑ w : ClosedWalk (BipIndex p q) m,
        ∑ α : Fin (m + 1) → σ,
          ‖pathGammaCoeff (p := p) (q := q) (σ := σ) w.1 w.1 w.2 α *
            (Fintype.card
              (SurvivingClosedWalkPairing
                (p := p) (q := q) (σ := σ) w α) : ℂ)‖ := by
  classical
  rw [gaussianWishartGammaOffDiagonal_traceMoment_eq_survivingPairing_sum
    (p := p) (q := q) (σ := σ) m]
  calc
    ‖∑ w : ClosedWalk (BipIndex p q) m,
        ∑ α : Fin (m + 1) → σ,
          pathGammaCoeff (p := p) (q := q) (σ := σ) w.1 w.1 w.2 α *
            (Fintype.card
              (SurvivingClosedWalkPairing
                (p := p) (q := q) (σ := σ) w α) : ℂ)‖
        ≤ ∑ w : ClosedWalk (BipIndex p q) m,
            ‖∑ α : Fin (m + 1) → σ,
              pathGammaCoeff (p := p) (q := q) (σ := σ) w.1 w.1 w.2 α *
                (Fintype.card
                  (SurvivingClosedWalkPairing
                    (p := p) (q := q) (σ := σ) w α) : ℂ)‖ := by
          exact norm_sum_le _ _
    _ ≤ ∑ w : ClosedWalk (BipIndex p q) m,
          ∑ α : Fin (m + 1) → σ,
            ‖pathGammaCoeff (p := p) (q := q) (σ := σ) w.1 w.1 w.2 α *
              (Fintype.card
                (SurvivingClosedWalkPairing
                  (p := p) (q := q) (σ := σ) w α) : ℂ)‖ := by
          exact Finset.sum_le_sum fun w _ => norm_sum_le _ _

/-- A concrete scalar trace-moment envelope for the Aubrun input.  The
particular envelope is deliberately a parameter: the exact polynomial envelope
comes from the Aubrun counting argument. -/
def AubrunOffDiagonalTraceMomentBound
    [DecidableEq σ] (m : ℕ) (envelope : ℝ) : Prop :=
  ‖gaussianWishartGammaOffDiagonalTraceMoment
    (p := p) (q := q) (σ := σ) m‖ ≤ envelope

/-- Exact-power complex trace-moment envelope. -/
def AubrunOffDiagonalTraceMomentPowerBound
    [DecidableEq σ] (m : ℕ) (envelope : ℝ) : Prop :=
  ‖gaussianWishartGammaOffDiagonalTraceMomentPower
    (p := p) (q := q) (σ := σ) m‖ ≤ envelope

/-- Exact-power real trace-moment envelope.  This is the form directly consumed
by the spectral extraction theorem below. -/
def AubrunOffDiagonalTraceMomentPowerRealBound
    [DecidableEq σ] (m : ℕ) (envelope : ℝ) : Prop :=
  gaussianWishartGammaOffDiagonalTraceMomentPowerReal
    (p := p) (q := q) (σ := σ) m ≤ envelope

/-- Aubrun's polynomial trace-moment envelope before taking the `m`-th root. -/
def aubrunOffDiagonalTraceMomentEnvelope
    (Q : ℕ → ℝ) (d s : ℝ) (m : ℕ) : ℝ :=
  (2 / s) ^ m * (d + Q m) ^ (m + 2) * (Real.sqrt s + Q m) ^ m

/-- The exact finite-combinatorial statement needed to obtain Aubrun's sharp
trace-moment envelope from the already-proved Wick expansion.

This theorem is intentionally a downstream closure theorem: its hypothesis is
the specific finite sum over closed walks, sample-column words, and surviving
contractions.  The missing Aubrun combinatorics is precisely the proof of that
finite inequality with a polynomial `Q` independent of `d` and `s`. -/
theorem AubrunOffDiagonalTraceMomentBound_of_survivingPairing_sum_norm_bound
    [DecidableEq σ] {Q : ℕ → ℝ} {d s : ℝ} (m : ℕ)
    (hSharp :
      ∑ w : ClosedWalk (BipIndex p q) m,
        ∑ α : Fin (m + 1) → σ,
          ‖pathGammaCoeff (p := p) (q := q) (σ := σ) w.1 w.1 w.2 α *
            (Fintype.card
              (SurvivingClosedWalkPairing
                (p := p) (q := q) (σ := σ) w α) : ℂ)‖ ≤
        aubrunOffDiagonalTraceMomentEnvelope Q d s m) :
    AubrunOffDiagonalTraceMomentBound
      (p := p) (q := q) (σ := σ) m
      (aubrunOffDiagonalTraceMomentEnvelope Q d s m) := by
  exact
    (gaussianWishartGammaOffDiagonal_traceMoment_norm_le_survivingPairing_sum_norm
      (p := p) (q := q) (σ := σ) m).trans hSharp

/-- Exact-power version of
`AubrunOffDiagonalTraceMomentBound_of_survivingPairing_sum_norm_bound`.
The closed-walk expansion indexed by `m` computes the trace power `m + 1`. -/
theorem AubrunOffDiagonalTraceMomentPowerBound_succ_of_survivingPairing_sum_norm_bound
    [DecidableEq σ] {Q : ℕ → ℝ} {d s : ℝ} (m : ℕ)
    (hSharp :
      ∑ w : ClosedWalk (BipIndex p q) m,
        ∑ α : Fin (m + 1) → σ,
          ‖pathGammaCoeff (p := p) (q := q) (σ := σ) w.1 w.1 w.2 α *
            (Fintype.card
              (SurvivingClosedWalkPairing
                (p := p) (q := q) (σ := σ) w α) : ℂ)‖ ≤
        aubrunOffDiagonalTraceMomentEnvelope Q d s m) :
    AubrunOffDiagonalTraceMomentPowerBound
      (p := p) (q := q) (σ := σ) (m + 1)
      (aubrunOffDiagonalTraceMomentEnvelope Q d s m) := by
  simpa [AubrunOffDiagonalTraceMomentPowerBound,
    gaussianWishartGammaOffDiagonalTraceMomentPower_succ] using
    AubrunOffDiagonalTraceMomentBound_of_survivingPairing_sum_norm_bound
      (p := p) (q := q) (σ := σ) (Q := Q) (d := d) (s := s) m hSharp

/-- A matrix unitary has operator norm at most one after conversion to the
Euclidean continuous linear map model. -/
theorem unitary_toEuclideanCLM_norm_le_one
    {n : Type*} [Fintype n] [DecidableEq n]
    (U : unitary (Matrix n n ℂ)) :
    ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (U : Matrix n n ℂ)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro x
  rw [matrixUnitary_toEuclideanCLM_norm U x]
  simp

/-- A Hermitian matrix has Euclidean operator norm bounded by the sup norm of
its spectral-theorem eigenvalue list. -/
theorem hermitian_toEuclideanCLM_norm_le_eigenvalues_norm
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A‖ ≤ ‖hA.eigenvalues‖ := by
  let U := hA.eigenvectorUnitary
  let φ := (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ)) U
  let D : Matrix n n ℂ := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  have hAeq : A = φ D := by
    simpa [φ, D, U] using hA.spectral_theorem
  have hU :
      ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (U : Matrix n n ℂ)‖ ≤ 1 :=
    unitary_toEuclideanCLM_norm_le_one U
  have hUstar :
      ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) ((U : Matrix n n ℂ)ᴴ)‖ ≤ 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      unitary_toEuclideanCLM_norm_le_one (star U)
  have hDnorm :
      ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) D‖ = ‖hA.eigenvalues‖ := by
    rw [← Matrix.cstar_norm_def D]
    rw [Matrix.l2_opNorm_diagonal]
    simp [Pi.norm_def]
  have hmap :
      Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (φ D) =
        Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (U : Matrix n n ℂ) *
          Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) D *
          Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) ((U : Matrix n n ℂ)ᴴ) := by
    simp [φ, U, Unitary.conjStarAlgAut_apply, map_mul, Matrix.star_eq_conjTranspose]
  calc
    ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A‖
        = ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (φ D)‖ := by
            rw [hAeq]
    _ = ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (U : Matrix n n ℂ) *
          Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) D *
          Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) ((U : Matrix n n ℂ)ᴴ)‖ := by
            rw [hmap]
    _ ≤ (‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (U : Matrix n n ℂ)‖ *
          ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) D‖) *
          ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) ((U : Matrix n n ℂ)ᴴ)‖ := by
            exact (norm_mul_le _ _).trans
              (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 * ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) D‖) * 1 := by
            gcongr
    _ = ‖hA.eigenvalues‖ := by
            simp [hDnorm]

/-- For an even positive exponent, the sup norm of a finite real vector is
controlled by the corresponding sum of even powers. -/
theorem real_pi_norm_pow_even_le_sum_pow
    {ι : Type*} [Fintype ι] (f : ι → ℝ) {m : ℕ}
    (hmEven : Even m) (hmpos : 0 < m) :
    ‖f‖ ^ m ≤ ∑ i : ι, f i ^ m := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
      haveI := hempty
      have hf : f = 0 := Subsingleton.elim _ _
      rw [hf]
      simp [Nat.ne_of_gt hmpos]
  | inr hnonempty =>
      haveI := hnonempty
      obtain ⟨i, hi_mem, hi_max⟩ :=
        Finset.exists_max_image (Finset.univ : Finset ι) (fun i => ‖f i‖)
          Finset.univ_nonempty
      have hnorm_le : ‖f‖ ≤ ‖f i‖ := by
        refine (pi_norm_le_iff_of_nonneg (norm_nonneg (f i))).2 ?_
        intro j
        exact hi_max j (by simp)
      have hnorm_eq : ‖f‖ = ‖f i‖ :=
        le_antisymm hnorm_le (norm_le_pi_norm f i)
      have hterm_eq : ‖f i‖ ^ m = f i ^ m := by
        simpa [Real.norm_eq_abs] using hmEven.pow_abs (α := ℝ) (f i)
      have hsingle : f i ^ m ≤ ∑ j ∈ (Finset.univ : Finset ι), f j ^ m := by
        refine Finset.single_le_sum (s := (Finset.univ : Finset ι))
          (f := fun j : ι => f j ^ m) ?_ hi_mem
        intro j _hj
        change 0 ≤ f j ^ m
        have habs : |f j| ^ m = f j ^ m := hmEven.pow_abs (α := ℝ) (f j)
        rw [← habs]
        exact pow_nonneg (abs_nonneg (f j)) m
      calc
        ‖f‖ ^ m = f i ^ m := by
          rw [hnorm_eq, hterm_eq]
        _ ≤ ∑ j : ι, f j ^ m := by
          simpa using hsingle

/-- Hermitian spectral trace domination:
`‖A‖∞^m ≤ Re Tr(A^m)` for positive even `m`. -/
theorem hermitian_toEuclideanCLM_norm_pow_le_re_trace_pow
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) {m : ℕ}
    (hmEven : Even m) (hmpos : 0 < m) :
    ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A‖ ^ m ≤
      RCLike.re ((A ^ m).trace) := by
  have hnorm :
      ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A‖ ≤ ‖hA.eigenvalues‖ :=
    hermitian_toEuclideanCLM_norm_le_eigenvalues_norm A hA
  have hpow :
      ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A‖ ^ m ≤
        ‖hA.eigenvalues‖ ^ m :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm m
  have hsum :
      ‖hA.eigenvalues‖ ^ m ≤ ∑ i : n, hA.eigenvalues i ^ m :=
    real_pi_norm_pow_even_le_sum_pow hA.eigenvalues hmEven hmpos
  have htrace :
      RCLike.re ((A ^ m).trace) = ∑ i : n, hA.eigenvalues i ^ m := by
    let φ := (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ)) hA.eigenvectorUnitary
    let D : Matrix n n ℂ := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)
    have hAeq : A = φ D := by
      simpa [φ, D] using hA.spectral_theorem
    have hpowA : A ^ m = φ (D ^ m) := by
      rw [hAeq]
      exact (map_pow φ D m).symm
    calc
      RCLike.re ((A ^ m).trace)
          = RCLike.re (((φ (D ^ m))).trace) := by
              rw [hpowA]
      _ = RCLike.re ((D ^ m).trace) := by
              exact congrArg RCLike.re
                (matrix_trace_conjStarAlgAut hA.eigenvectorUnitary (D ^ m))
      _ = ∑ i : n, hA.eigenvalues i ^ m := by
              rw [Matrix.diagonal_pow, Matrix.trace_diagonal]
              simp only [Function.comp_apply, Pi.pow_apply]
              change (∑ x, ((hA.eigenvalues x : ℂ) ^ m)).re =
                ∑ i, hA.eigenvalues i ^ m
              rw [Complex.re_sum]
              refine Finset.sum_congr rfl ?_
              intro i _
              have hp :
                  ((hA.eigenvalues i ^ m : ℝ) : ℂ) =
                    (hA.eigenvalues i : ℂ) ^ m :=
                Complex.ofReal_pow (hA.eigenvalues i) m
              have h1 :
                  RCLike.re ((hA.eigenvalues i : ℂ) ^ m) =
                    RCLike.re (((hA.eigenvalues i ^ m : ℝ) : ℂ)) :=
                congrArg RCLike.re hp.symm
              exact h1.trans (RCLike.ofReal_re (K := ℂ) (hA.eigenvalues i ^ m))
  exact hpow.trans (htrace.symm ▸ hsum)

/-- Probability-space extraction from an `m`-th moment bound, for nonnegative
real observables and positive integer `m`. -/
theorem expectation_le_rpow_moment_bound_of_memLp
    {Ω₀ : Type*} [MeasurableSpace Ω₀] {μ : Measure Ω₀}
    [IsProbabilityMeasure μ] {X : Ω₀ → ℝ} {m : ℕ}
    (hmpos : 0 < m)
    (hX_nonneg : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (hAES : AEStronglyMeasurable X μ)
    (hMemLp : MemLp X (m : ℝ≥0∞) μ)
    {B : ℝ} (hMoment : (∫ ω, X ω ^ m ∂μ) ≤ B) :
    (∫ ω, X ω ∂μ) ≤ Real.rpow B ((m : ℝ)⁻¹) := by
  let pNN : ℝ≥0 := ⟨(m : ℝ), Nat.cast_nonneg m⟩
  have hpNN_pos : 0 < pNN := by
    change (0 : ℝ) < (m : ℝ)
    exact_mod_cast hmpos
  have hpNN_ne : pNN ≠ 0 := ne_of_gt hpNN_pos
  have hpq : (1 : ℝ≥0∞) ≤ (pNN : ℝ≥0∞) := by
    have h1m : (1 : ℕ) ≤ m := Nat.succ_le_of_lt hmpos
    have hpNN_one : (1 : ℝ≥0) ≤ pNN := by
      change (1 : ℝ) ≤ (m : ℝ)
      exact_mod_cast h1m
    exact_mod_cast hpNN_one
  have hELp : eLpNorm X 1 μ ≤ eLpNorm X (pNN : ℝ≥0∞) μ :=
    eLpNorm_le_eLpNorm_of_exponent_le (μ := μ) hpq hAES
  have hMemLp_pNN : MemLp X (pNN : ℝ≥0∞) μ := by
    simpa [pNN] using hMemLp
  have hLpMono : lpNorm X 1 μ ≤ lpNorm X (pNN : ℝ≥0∞) μ := by
    have hToReal := ENNReal.toReal_mono hMemLp_pNN.eLpNorm_ne_top hELp
    simpa [toReal_eLpNorm hAES] using hToReal
  have hMeanEqNorm : (∫ ω, X ω ∂μ) = ∫ ω, ‖X ω‖ ∂μ := by
    refine integral_congr_ae <| hX_nonneg.mono ?_
    intro ω hω
    simp [Real.norm_eq_abs, abs_of_nonneg hω]
  have hLpOne : lpNorm X 1 μ = ∫ ω, ‖X ω‖ ∂μ :=
    lpNorm_one_eq_integral_norm hAES
  have hLpPow :
      lpNorm X (pNN : ℝ≥0∞) μ =
        (∫ ω, ‖X ω‖ ^ (pNN : ℝ) ∂μ) ^ ((pNN⁻¹ : ℝ≥0) : ℝ) :=
    lpNorm_nnreal_eq_integral_norm_rpow hpNN_ne hAES
  have hNormPowEq :
      (∫ ω, ‖X ω‖ ^ (pNN : ℝ) ∂μ) = ∫ ω, X ω ^ m ∂μ := by
    refine integral_congr_ae <| hX_nonneg.mono ?_
    intro ω hω
    calc
      ‖X ω‖ ^ (pNN : ℝ) = ‖X ω‖ ^ m := by
        change ‖X ω‖ ^ (m : ℝ) = ‖X ω‖ ^ m
        rw [Real.rpow_natCast]
      _ = X ω ^ m := by
        simp [Real.norm_eq_abs, abs_of_nonneg hω]
  have hIntNonneg : 0 ≤ ∫ ω, ‖X ω‖ ^ (pNN : ℝ) ∂μ := by
    exact integral_nonneg
      (fun ω => Real.rpow_nonneg (norm_nonneg (X ω)) (pNN : ℝ))
  have hIntLeB : (∫ ω, ‖X ω‖ ^ (pNN : ℝ) ∂μ) ≤ B := by
    rw [hNormPowEq]
    exact hMoment
  have hRootLe :
      (∫ ω, ‖X ω‖ ^ (pNN : ℝ) ∂μ) ^ ((pNN⁻¹ : ℝ≥0) : ℝ) ≤
        Real.rpow B ((m : ℝ)⁻¹) := by
    have hpow := Real.rpow_le_rpow hIntNonneg hIntLeB
      (show 0 ≤ ((pNN⁻¹ : ℝ≥0) : ℝ) from by positivity)
    simpa [pNN] using hpow
  calc
    (∫ ω, X ω ∂μ) = ∫ ω, ‖X ω‖ ∂μ := hMeanEqNorm
    _ = lpNorm X 1 μ := hLpOne.symm
    _ ≤ lpNorm X (pNN : ℝ≥0∞) μ := hLpMono
    _ = (∫ ω, ‖X ω‖ ^ (pNN : ℝ) ∂μ) ^ ((pNN⁻¹ : ℝ≥0) : ℝ) := hLpPow
    _ ≤ Real.rpow B ((m : ℝ)⁻¹) := hRootLe

/-- Real trace-moment extraction for the concrete off-diagonal matrix:
an even trace moment bound gives the corresponding operator-norm expectation
bound after taking the `m`-th root. -/
theorem gaussianWishartGammaOffDiagonalOpNormMean_le_rpow_of_traceMomentPowerRealBound
    [DecidableEq σ] {m : ℕ} (hmEven : Even m) (hmpos : 0 < m)
    (hAES :
      AEStronglyMeasurable
        (fun ω : Ω p q σ =>
          opNorm
            (wishartGammaOffDiagonal (p := p) (q := q) (σ := σ)
              (gaussianMatrix p q σ ω)))
        (gaussianMeasure p q σ))
    (hMemLp :
      MemLp
        (fun ω : Ω p q σ =>
          opNorm
            (wishartGammaOffDiagonal (p := p) (q := q) (σ := σ)
              (gaussianMatrix p q σ ω)))
        (m : ℝ≥0∞) (gaussianMeasure p q σ))
    (hTraceIntegrable :
      Integrable
        (fun ω : Ω p q σ =>
          RCLike.re
            (((wishartGammaOffDiagonal (p := p) (q := q) (σ := σ)
                (gaussianMatrix p q σ ω)) ^ m).trace))
        (gaussianMeasure p q σ))
    {B : ℝ}
    (hTraceBound :
      AubrunOffDiagonalTraceMomentPowerRealBound
        (p := p) (q := q) (σ := σ) m B) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := p) (q := q) (σ := σ) ≤ Real.rpow B ((m : ℝ)⁻¹) := by
  let μ := gaussianMeasure p q σ
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  let X : Ω p q σ → ℝ := fun ω =>
    opNorm
      (wishartGammaOffDiagonal (p := p) (q := q) (σ := σ)
        (gaussianMatrix p q σ ω))
  have hX_nonneg : ∀ᵐ ω ∂μ, 0 ≤ X ω :=
    Filter.Eventually.of_forall fun ω => norm_nonneg _
  have hPowIntegrableNorm : Integrable (fun ω => ‖X ω‖ ^ m) μ :=
    hMemLp.integrable_norm_pow (Nat.ne_of_gt hmpos)
  have hPowIntegrable : Integrable (fun ω => X ω ^ m) μ := by
    refine hPowIntegrableNorm.congr <| hX_nonneg.mono ?_
    intro ω hω
    simp [Real.norm_eq_abs, abs_of_nonneg hω]
  have hPointwise :
      (fun ω : Ω p q σ => X ω ^ m) ≤
        fun ω : Ω p q σ =>
          RCLike.re
            (((wishartGammaOffDiagonal (p := p) (q := q) (σ := σ)
                (gaussianMatrix p q σ ω)) ^ m).trace) := by
    intro ω
    have hHerm :
        (wishartGammaOffDiagonal (p := p) (q := q) (σ := σ)
          (gaussianMatrix p q σ ω)).IsHermitian :=
      wishartGammaOffDiagonal_isHermitian
        (p := p) (q := q) (σ := σ) (gaussianMatrix p q σ ω)
    simpa [X, opNorm] using
      hermitian_toEuclideanCLM_norm_pow_le_re_trace_pow
        (wishartGammaOffDiagonal (p := p) (q := q) (σ := σ)
          (gaussianMatrix p q σ ω))
        hHerm hmEven hmpos
  have hPowLeTrace :
      (∫ ω : Ω p q σ, X ω ^ m ∂μ) ≤
        gaussianWishartGammaOffDiagonalTraceMomentPowerReal
          (p := p) (q := q) (σ := σ) m := by
    exact integral_mono hPowIntegrable hTraceIntegrable hPointwise
  have hPowLeB : (∫ ω : Ω p q σ, X ω ^ m ∂μ) ≤ B :=
    hPowLeTrace.trans hTraceBound
  simpa [gaussianWishartGammaOffDiagonalOpNormMean, X, μ] using
    expectation_le_rpow_moment_bound_of_memLp
      (μ := μ) (X := X) hmpos hX_nonneg hAES hMemLp hPowLeB

/-! ## Explicit even moment choice and expectation extraction -/

/-- Explicit even moment parameter used for the off-diagonal Aubrun extraction.

The choice `m(d) = 2 (⌈log(d+2)^2⌉ + 1)` is deliberately concrete: it is even,
nonzero, tends to infinity, and remains logarithmic in the matrix dimension.
The remaining scalar asymptotic estimate is the usual paper step showing that
the polynomial counting losses evaluated at this `m(d)` are absorbed when
`s / d^2 → λ`. -/
def aubrunEvenMomentParameter (d : ℕ) : ℕ :=
  2 * (⌈(Real.log ((d : ℝ) + 2)) ^ 2⌉₊ + 1)

/-- The chosen Aubrun moment parameter is even. -/
theorem aubrunEvenMomentParameter_even (d : ℕ) :
    Even (aubrunEvenMomentParameter d) := by
  unfold aubrunEvenMomentParameter
  exact ⟨⌈(Real.log ((d : ℝ) + 2)) ^ 2⌉₊ + 1, by ring⟩

/-- The chosen Aubrun moment parameter is strictly positive. -/
theorem aubrunEvenMomentParameter_pos (d : ℕ) :
    0 < aubrunEvenMomentParameter d := by
  unfold aubrunEvenMomentParameter
  exact Nat.mul_pos (by norm_num) (Nat.succ_pos _)

/-- The chosen Aubrun moment parameter is at least two. -/
theorem two_le_aubrunEvenMomentParameter (d : ℕ) :
    2 ≤ aubrunEvenMomentParameter d := by
  unfold aubrunEvenMomentParameter
  omega

/-- The chosen Aubrun moment parameter is nonzero as a real number. -/
theorem aubrunEvenMomentParameter_ne_zero_real (d : ℕ) :
    (aubrunEvenMomentParameter d : ℝ) ≠ 0 := by
  exact_mod_cast (ne_of_gt (aubrunEvenMomentParameter_pos d))

/-- The analytic envelope obtained after applying the even trace-moment method
to Aubrun's polynomial counting bound.

For a polynomial counting loss `Q`, this is the paper-scale expression
corresponding to
`(E Tr Z^m)^(1/m)` after the trace bound
`E Tr Z^m ≤ (2/s)^m (d + Q(m))^(m+2) (sqrt s + Q(m))^m`.
The exponent is written with `Real.rpow` because it is the genuine
real-valued `m`-th root expression. -/
def aubrunOffDiagonalExpectationEnvelope
    (Q : ℕ → ℝ) (d s : ℝ) (m : ℕ) : ℝ :=
  (2 / s) * Real.rpow (d + Q m) (1 + 2 / (m : ℝ)) *
    (Real.sqrt s + Q m)

/-- Downstream derivation of the off-diagonal expectation bound at the chosen
even moment.

This theorem intentionally exposes the two remaining mathematical obligations:

* the high-moment extraction from the concrete trace moment at the chosen even
  `m(d)`;
* the scalar asymptotic estimate bounding the resulting Aubrun envelope by the
  desired constant `Cλ`.

It does not assert Aubrun's Proposition 7.1 for free. -/
theorem gaussianWishartGammaOffDiagonalOpNormMean_le_of_chosen_even_moment
    [DecidableEq σ] {Q : ℕ → ℝ} {dNat : ℕ} {d s C_lam : ℝ}
    (hMomentExtraction :
      gaussianWishartGammaOffDiagonalOpNormMean
          (p := p) (q := q) (σ := σ) ≤
        aubrunOffDiagonalExpectationEnvelope Q d s
          (aubrunEvenMomentParameter dNat))
    (hEnvelope :
      aubrunOffDiagonalExpectationEnvelope Q d s
          (aubrunEvenMomentParameter dNat) ≤ C_lam) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := p) (q := q) (σ := σ) ≤ C_lam :=
  hMomentExtraction.trans hEnvelope

/-! The next structure is only a named bookkeeping package for the two explicit
obligations in the previous theorem.  It is useful downstream because it keeps
the final appendix statement from mentioning raw trace-moment algebra again. -/

/-- Appendix-facing package for deriving `E ‖Z‖∞ ≤ Cλ` from the explicit
logarithmic even moment choice. -/
structure AubrunOffDiagonalExpectationDerivation
    [DecidableEq σ] (Q : ℕ → ℝ) (dNat : ℕ) (d s C_lam : ℝ) where
  momentExtraction :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := p) (q := q) (σ := σ) ≤
      aubrunOffDiagonalExpectationEnvelope Q d s
        (aubrunEvenMomentParameter dNat)
  envelopeBound :
    aubrunOffDiagonalExpectationEnvelope Q d s
        (aubrunEvenMomentParameter dNat) ≤ C_lam

/-- The packaged off-diagonal expectation conclusion `E ‖Z‖∞ ≤ Cλ`. -/
theorem AubrunOffDiagonalExpectationDerivation.bound
    [DecidableEq σ] {Q : ℕ → ℝ} {dNat : ℕ} {d s C_lam : ℝ}
    (H :
      AubrunOffDiagonalExpectationDerivation
        (p := p) (q := q) (σ := σ) Q dNat d s C_lam) :
    gaussianWishartGammaOffDiagonalOpNormMean
        (p := p) (q := q) (σ := σ) ≤ C_lam :=
  gaussianWishartGammaOffDiagonalOpNormMean_le_of_chosen_even_moment
    (p := p) (q := q) (σ := σ)
    (Q := Q) (dNat := dNat) (d := d) (s := s) (C_lam := C_lam)
    H.momentExtraction H.envelopeBound

/-! ## Final Aubrun input and downstream normalized expectation bound -/

/-- Final appendix-facing Aubrun input for the off-diagonal part.

The first field records the trace-moment estimates obtained after expanding
the Wick sums.  The second field is the operator-norm expectation/lift
consequence at the exact spherical scale used by Appendix B.

No theorem in this file asserts this input unconditionally; it is the
remaining Aubrun moment estimate to be proved if one wants full analytic
autonomy. -/
structure AubrunOffDiagonalMomentInput
    [DecidableEq σ] (d : ℝ) where
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  momentEnvelope : ℕ → ℝ
  traceMomentBound :
    ∀ m,
      AubrunOffDiagonalTraceMomentBound
        (p := p) (q := q) (σ := σ) m (momentEnvelope m)
  quadraticLiftBound :
    gaussianQuadraticOffDiagonalGammaLiftMean
        (p := p) (q := q) (σ := σ) ≤
      gaussianQuadraticRadialMean (p := p) (q := q) (σ := σ) *
        (constant / d ^ 2)

/-- The off-diagonal normalized spherical expectation bound obtained from the
final Aubrun input by the exact radial/spherical cancellation. -/
theorem AubrunOffDiagonalMomentInput.to_spherical_offDiagonal_bound
    [DecidableEq σ] {d : ℝ}
    (I : AubrunOffDiagonalMomentInput (p := p) (q := q) (σ := σ) d)
    (hIndep :
      gaussianRadiusSq (p := p) (q := q) (σ := σ) ⟂ᵢ[gaussianMeasure p q σ]
        gaussianDirection (p := p) (q := q) (σ := σ))
    (hQuadraticRadialPos :
      0 < gaussianQuadraticRadialMean (p := p) (q := q) (σ := σ)) :
    sphericalOffDiagonalGammaOpNormMean (p := p) (q := q) (σ := σ) ≤
      I.constant / d ^ 2 := by
  exact _root_.AppendixB.spherical_gamma_expectation_bound_from_radial_factorization
    (hRadialSecondMean := hQuadraticRadialPos)
    (hFactor :=
      gaussianQuadraticOffDiagonalGammaLiftMean_factorization_of_indep
        (p := p) (q := q) (σ := σ) hIndep)
    (hBound := I.quadraticLiftBound)

end AppendixB
end PptFactorization
