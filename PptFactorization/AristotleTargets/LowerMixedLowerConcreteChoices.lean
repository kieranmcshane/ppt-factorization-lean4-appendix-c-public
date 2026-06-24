import PptFactorization.AppendixBLowerBoundClosure

/-!
Aristotle handoff for the lower-bound closure.

Target: close the concrete one-sided mixed-remainder lower supplier used as
`hMixedLower` in
`AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_concreteScalarChoices`.

Protected file: do not edit `PptFactorization/AppendixBSpikeLowerBound.lean`.

Allowed inputs/context: use existing local lemmas from
`PptFactorization.AppendixBLowerBoundClosure`,
`PptFactorization.AppendixBWishartBridge`, and mathlib.  Do not add axioms,
`opaque`, `unsafe`, new theorem parameters, or weaken the statement.

PROVIDED SOLUTION:
Use the local expansion/mixed-word estimates already present in the project if
available.  The desired estimate is one-sided:
`-errMix ≤ columnMixedRemainder` on the favourable event.  The center must be
the mean-centered deleted-background choice
`lowerConcreteDeletedBackgroundMean R k d`, not `0`.  If the concrete `O(1/d)`
mixed error is too small, report the exact replacement mixed-error definition
needed and the first missing mixed-word lemma.  Preserve the theorem statement
exactly.
-/
namespace AppendixB

open PptFactorization.RandomMatrixModel
open PptFactorization.HighProbabilityBounds
open Filter
open scoped Topology Matrix.Norms.Frobenius

theorem lower_columnMixedRemainder_eq_localExpansion_zeroLinear
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    (N : ℝ) (k : ℕ) (X : SampleMatrix p q σ) (α₀ : σ) :
    columnMixedRemainder (p := p) (q := q) (σ := σ) N k X α₀ =
      localExpansionMixedRemainder (p := p) (q := q) N k
        (columnBackgroundMatrix (p := p) (q := q) (σ := σ) X α₀)
        0
        (columnSpikeMatrix (p := p) (q := q) (σ := σ) X α₀) := by
  unfold columnMixedRemainder localExpansionMixedRemainder
    columnSpikeContribution columnBackgroundContribution
  rw [gamma_densityMatrix_eq_columnSpike_add_background
    (p := p) (q := q) (σ := σ) X α₀]
  have hadd :
      columnSpikeMatrix (p := p) (q := q) (σ := σ) X α₀ +
        columnBackgroundMatrix (p := p) (q := q) (σ := σ) X α₀ =
      columnBackgroundMatrix (p := p) (q := q) (σ := σ) X α₀ +
        columnSpikeMatrix (p := p) (q := q) (σ := σ) X α₀ := by
    abel
  rw [hadd]
  abel_nf

theorem lower_columnMixedRemainder_abs_le_of_localExpansion_zeroLinear
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    {N errMix : ℝ} {k : ℕ} {X : SampleMatrix p q σ} {α₀ : σ}
    (hLocal :
      |localExpansionMixedRemainder (p := p) (q := q) N k
          (columnBackgroundMatrix (p := p) (q := q) (σ := σ) X α₀)
          0
          (columnSpikeMatrix (p := p) (q := q) (σ := σ) X α₀)| ≤
        errMix) :
    |columnMixedRemainder (p := p) (q := q) (σ := σ) N k X α₀| ≤
      errMix := by
  rw [lower_columnMixedRemainder_eq_localExpansion_zeroLinear
    (p := p) (q := q) (σ := σ) N k X α₀]
  exact hLocal

/-! ### Norm facts for the spike letter in the mixed-word estimate -/

/-- The partial transpose of a unit rank-one projector has Frobenius norm one.

This is the spike-side input needed for mixed words.  It does not use the
projective cap/product-vector geometry; the cap is only needed for the pure
all-spike term. -/
theorem lower_rankOneProjectorGamma_frobeniusNorm_eq_one_of_norm_eq_one
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    (u : EuclideanSpace ℂ (BipIndex p q)) (hu : ‖u‖ = 1) :
    frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
      (rankOneProjectorGamma (p := p) (q := q) u) = 1 := by
  rw [rankOneProjectorGamma_frobeniusNorm]
  rw [hu]
  norm_num

/-- The partial transpose of a unit rank-one projector has operator norm at
most one.  This follows from the Frobenius bound, so it avoids any Schmidt
decomposition. -/
theorem lower_rankOneProjectorGamma_opNorm_le_one_of_norm_eq_one
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    (u : EuclideanSpace ℂ (BipIndex p q)) (hu : ‖u‖ = 1) :
    opNorm (p := p) (q := q)
      (rankOneProjectorGamma (p := p) (q := q) u) ≤ 1 := by
  calc
    opNorm (p := p) (q := q)
        (rankOneProjectorGamma (p := p) (q := q) u)
        ≤ frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
            (rankOneProjectorGamma (p := p) (q := q) u) := by
          exact opNorm_le_frobeniusNorm
            (p := p) (q := q)
            (A := rankOneProjectorGamma (p := p) (q := q) u)
    _ = 1 :=
          lower_rankOneProjectorGamma_frobeniusNorm_eq_one_of_norm_eq_one
            (p := p) (q := q) u hu

/-- Exact Frobenius norm of the concrete one-column spike matrix in
mass-direction coordinates. -/
theorem lower_columnSpikeMatrix_frobeniusNorm_eq_mass
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    (X : SampleMatrix p q σ) (α₀ : σ)
    (hdir :
      ‖sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀‖ = 1) :
    frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
        (columnSpikeMatrix (p := p) (q := q) (σ := σ) X α₀) =
      sampleColumnMass (p := p) (q := q) (σ := σ) X α₀ := by
  rw [columnSpikeMatrix_eq_mass_smul_rankOneProjectorGamma_direction
    (p := p) (q := q) (σ := σ) (α₀ := α₀) X]
  change
    ‖((sampleColumnMass (p := p) (q := q) (σ := σ) X α₀ : ℝ) : ℂ) •
        rankOneProjectorGamma (p := p) (q := q)
          (sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀)‖ =
      sampleColumnMass (p := p) (q := q) (σ := σ) X α₀
  rw [norm_smul]
  have hSpikeFrob :
      ‖rankOneProjectorGamma (p := p) (q := q)
          (sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀)‖ = 1 := by
    simpa [frobeniusNorm, hdir] using
      (rankOneProjectorGamma_frobeniusNorm
        (p := p) (q := q)
        (u := sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀))
  rw [hSpikeFrob]
  have hmass_nonneg :
      0 ≤ sampleColumnMass (p := p) (q := q) (σ := σ) X α₀ :=
    sampleColumnMass_nonneg (p := p) (q := q) (σ := σ) X α₀
  simp [abs_of_nonneg hmass_nonneg]

/-- Operator norm of the concrete one-column spike matrix is bounded by its
column mass. -/
theorem lower_columnSpikeMatrix_opNorm_le_mass
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    (X : SampleMatrix p q σ) (α₀ : σ)
    (hdir :
      ‖sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀‖ = 1) :
    opNorm (p := p) (q := q)
        (columnSpikeMatrix (p := p) (q := q) (σ := σ) X α₀) ≤
      sampleColumnMass (p := p) (q := q) (σ := σ) X α₀ := by
  calc
    opNorm (p := p) (q := q)
        (columnSpikeMatrix (p := p) (q := q) (σ := σ) X α₀)
        ≤ frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
            (columnSpikeMatrix (p := p) (q := q) (σ := σ) X α₀) := by
          exact opNorm_le_frobeniusNorm
            (p := p) (q := q)
            (A := columnSpikeMatrix (p := p) (q := q) (σ := σ) X α₀)
    _ = sampleColumnMass (p := p) (q := q) (σ := σ) X α₀ :=
          lower_columnSpikeMatrix_frobeniusNorm_eq_mass
            (p := p) (q := q) (σ := σ) X α₀ hdir

/-! ### Sharp two-letter trace estimates for the lower mixed route -/

/-- Left multiplication by a square matrix is controlled by the square
operator norm and the Frobenius norm of the right factor. -/
theorem lower_frobeniusNorm_mul_le_opNorm_mul_frobeniusNorm
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    (A B : BipMatrix p q) :
    frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) (A * B) ≤
      opNorm (p := p) (q := q) A *
        frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) B := by
  simpa [frobeniusNorm] using
    (sampleOpNorm_mul_frobeniusNorm_le
      (p := p) (q := q) (σ := BipIndex p q) A B)

/-- Operator norm is submultiplicative for the square bipartite matrices used
in the partial-transpose local expansion. -/
theorem lower_opNorm_mul_le
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    (A B : BipMatrix p q) :
    opNorm (p := p) (q := q) (A * B) ≤
      opNorm (p := p) (q := q) A * opNorm (p := p) (q := q) B := by
  unfold opNorm
  rw [map_mul]
  exact norm_mul_le _ _

/-- The identity matrix has operator norm at most one.  This total form avoids
nonemptiness side conditions on the finite index type. -/
theorem lower_opNorm_one_le
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q] :
    opNorm (p := p) (q := q) (1 : BipMatrix p q) ≤ 1 := by
  unfold opNorm
  rw [map_one]
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) ?_
  intro x
  simp

/-- Right multiplication is controlled by the operator norm of the right factor
and the Frobenius norm of the left factor. -/
theorem lower_frobeniusNorm_mul_le_frobeniusNorm_mul_opNorm
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    (A B : BipMatrix p q) :
    frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) (A * B) ≤
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) A *
        opNorm (p := p) (q := q) B := by
  have h :=
    lower_frobeniusNorm_mul_le_opNorm_mul_frobeniusNorm
      (p := p) (q := q) (star B) (star A)
  have hfrob_eq :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) (A * B) =
        frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
          (star B * star A) := by
    unfold frobeniusNorm
    calc
      ‖A * B‖ = ‖(A * B).conjTranspose‖ :=
        (Matrix.frobenius_norm_conjTranspose (A := A * B)).symm
      _ = ‖B.conjTranspose * A.conjTranspose‖ := by
        rw [Matrix.conjTranspose_mul]
      _ = ‖star B * star A‖ := by
        simp [Matrix.star_eq_conjTranspose]
  have hop :
      opNorm (p := p) (q := q) (star B) = opNorm (p := p) (q := q) B := by
    unfold opNorm
    rw [map_star]
    exact norm_star (Matrix.toEuclideanCLM (n := BipIndex p q) (𝕜 := ℂ) B)
  have hfrobA :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) (star A) =
        frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) A := by
    unfold frobeniusNorm
    simp [Matrix.star_eq_conjTranspose]
  calc
    frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) (A * B)
        = frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
            (star B * star A) := hfrob_eq
    _ ≤ opNorm (p := p) (q := q) (star B) *
          frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) (star A) := h
    _ = frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) A *
          opNorm (p := p) (q := q) B := by
        rw [hop, hfrobA, mul_comm]

/-- Frobenius norm of a positive-length power, with all but one factor
controlled in operator norm. -/
theorem lower_frobeniusNorm_pow_succ_le_opNorm_pow_mul_frobeniusNorm
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    (B : BipMatrix p q) (n : ℕ) :
    frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) (B ^ (n + 1)) ≤
      opNorm (p := p) (q := q) B ^ n *
        frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) B := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hmul :=
        lower_frobeniusNorm_mul_le_opNorm_mul_frobeniusNorm
          (p := p) (q := q) B (B ^ (n + 1))
      have hop_nonneg : 0 ≤ opNorm (p := p) (q := q) B := by
        unfold opNorm
        positivity
      calc
        frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
            (B ^ (n + 1 + 1))
            = frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
                (B * B ^ (n + 1)) := by
                rw [pow_succ']
        _ ≤ opNorm (p := p) (q := q) B *
              frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
                (B ^ (n + 1)) := hmul
        _ ≤ opNorm (p := p) (q := q) B *
              (opNorm (p := p) (q := q) B ^ n *
                frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) B) := by
              exact mul_le_mul_of_nonneg_left ih hop_nonneg
        _ = opNorm (p := p) (q := q) B ^ (n + 1) *
              frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) B := by
              ring

/-- The Frobenius norm of the partially-transposed density matrix is controlled
by the rectangular operator norm and the Frobenius norm of the sample matrix.

This is the deterministic source of the `M / sqrt N` background Frobenius
envelope used by the partial-transpose mixed-word estimate. -/
theorem lower_gamma_densityMatrix_frobeniusNorm_le_sampleOpNorm_mul_frobeniusNorm
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    (Y : SampleMatrix p q σ) :
    frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
        (gamma (densityMatrix Y)) ≤
      PptFactorization.HighProbabilityBounds.sampleOpNorm
        (p := p) (q := q) (σ := σ) Y *
        frobeniusNorm (p := p) (q := q) (σ := σ) Y := by
  calc
    frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
        (gamma (densityMatrix Y))
        = frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
            (densityMatrix Y) := by simp
    _ = ‖Y * Y.conjTranspose‖ := by rfl
    _ ≤ PptFactorization.HighProbabilityBounds.sampleOpNorm
          (p := p) (q := q) (σ := σ) Y * ‖Y.conjTranspose‖ := by
          exact
            PptFactorization.HighProbabilityBounds.sampleOpNorm_mul_frobeniusNorm_le
              (p := p) (q := q) (σ := σ) Y Y.conjTranspose
    _ = PptFactorization.HighProbabilityBounds.sampleOpNorm
          (p := p) (q := q) (σ := σ) Y *
          frobeniusNorm (p := p) (q := q) (σ := σ) Y := by
          rw [Matrix.frobenius_norm_conjTranspose]
          rfl

/-- Total normalization of the deleted-column background never increases its
Frobenius norm past one: it is either a unit vector or the zero fallback from
Lean's total inverse. -/
theorem lower_sampleColumnComplementNormalized_frobeniusNorm_le_one
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    (X : SampleMatrix p q σ) (α₀ : σ) :
    frobeniusNorm (p := p) (q := q) (σ := σ)
        (sampleColumnComplementNormalized
          (p := p) (q := q) (σ := σ) X α₀) ≤ 1 := by
  by_cases hzero :
      sampleColumnComplement (p := p) (q := q) (σ := σ) X α₀ = 0
  · simp [sampleColumnComplementNormalized, hzero, frobeniusNorm]
  · have hnorm :=
      frobeniusNorm_normalizedSample
        (p := p) (q := q) (σ := σ)
        (G := sampleColumnComplement (p := p) (q := q) (σ := σ) X α₀)
        hzero
    simpa [normalizedSample, sampleColumnComplementNormalized] using
      le_of_eq hnorm

/-- Entrywise square formula for the Frobenius norm, localized to the mixed
supplier to avoid importing the scale-loss target back into this file. -/
theorem lower_mixed_frobeniusNorm_sq_eq_entry_sum
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    (A : SampleMatrix p q σ) :
    frobeniusNorm (p := p) (q := q) (σ := σ) A ^ 2 =
      ∑ i : BipIndex p q, ∑ α : σ, ‖A i α‖ ^ 2 := by
  unfold frobeniusNorm
  rw [Matrix.frobenius_norm_def]
  rw [← Real.sqrt_eq_rpow]
  rw [Real.sq_sqrt]
  · simp_rw [Real.rpow_two]
  · exact Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => by positivity

/-- Orthogonal column split at the level of squared Frobenius masses. -/
theorem lower_mixed_sampleColumnMass_add_complement_frobeniusNorm_sq
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    (X : SampleMatrix p q σ) (α₀ : σ) :
    sampleColumnMass (p := p) (q := q) (σ := σ) X α₀ +
      frobeniusNorm (p := p) (q := q) (σ := σ)
        (sampleColumnComplement (p := p) (q := q) (σ := σ) X α₀) ^ 2 =
      frobeniusNorm (p := p) (q := q) (σ := σ) X ^ 2 := by
  unfold sampleColumnMass
  rw [lower_mixed_frobeniusNorm_sq_eq_entry_sum
        (p := p) (q := q) (σ := σ)
        (A := sampleColumnPart (p := p) (q := q) (σ := σ) X α₀)]
  rw [lower_mixed_frobeniusNorm_sq_eq_entry_sum
        (p := p) (q := q) (σ := σ)
        (A := sampleColumnComplement (p := p) (q := q) (σ := σ) X α₀)]
  rw [lower_mixed_frobeniusNorm_sq_eq_entry_sum
        (p := p) (q := q) (σ := σ) (A := X)]
  have hrow : ∀ i : BipIndex p q,
      (∑ α : σ, ‖sampleColumnPart (p := p) (q := q) (σ := σ) X α₀ i α‖ ^ 2) +
        (∑ α : σ,
          ‖sampleColumnComplement (p := p) (q := q) (σ := σ) X α₀ i α‖ ^ 2) =
      ∑ α : σ, ‖X i α‖ ^ 2 := by
    intro i
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro α _
    by_cases hα : α = α₀ <;>
      simp [sampleColumnPart, sampleColumnComplement, hα]
  calc
    (∑ i : BipIndex p q,
        ∑ α : σ,
          ‖sampleColumnPart (p := p) (q := q) (σ := σ) X α₀ i α‖ ^ 2) +
        (∑ i : BipIndex p q,
          ∑ α : σ,
            ‖sampleColumnComplement
                (p := p) (q := q) (σ := σ) X α₀ i α‖ ^ 2)
      = ∑ i : BipIndex p q,
          ((∑ α : σ,
              ‖sampleColumnPart (p := p) (q := q) (σ := σ) X α₀ i α‖ ^ 2) +
            (∑ α : σ,
              ‖sampleColumnComplement
                  (p := p) (q := q) (σ := σ) X α₀ i α‖ ^ 2)) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ i : BipIndex p q, ∑ α : σ, ‖X i α‖ ^ 2 := by
          exact Finset.sum_congr rfl fun i _ => hrow i

/-- On the Frobenius unit sphere, the deleted-column complement has squared
Frobenius mass at most one. -/
theorem lower_mixed_sampleColumnComplement_frobeniusNorm_sq_le_one_of_norm_one
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    {X : SampleMatrix p q σ} {α₀ : σ}
    (hX : frobeniusNorm (p := p) (q := q) (σ := σ) X = 1) :
    frobeniusNorm (p := p) (q := q) (σ := σ)
        (sampleColumnComplement (p := p) (q := q) (σ := σ) X α₀) ^ 2 ≤
      1 := by
  have hsum :=
    lower_mixed_sampleColumnMass_add_complement_frobeniusNorm_sq
      (p := p) (q := q) (σ := σ) X α₀
  have hmass_nonneg :
      0 ≤ sampleColumnMass (p := p) (q := q) (σ := σ) X α₀ :=
    sampleColumnMass_nonneg (p := p) (q := q) (σ := σ) X α₀
  rw [hX] at hsum
  nlinarith

/-- The sample-operator component of `backgroundTypicalSet` gives the
Frobenius envelope for the partially-transposed density matrix, provided the
background sample is on (or inside) the Frobenius unit sphere. -/
theorem lower_backgroundTypicalSet_gamma_densityMatrix_frobeniusNorm_bound
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    {N M τ mean : ℝ} {k : ℕ} {Y : SampleMatrix p q σ}
    (hY :
      Y ∈ backgroundTypicalSet
        (p := p) (q := q) (σ := σ) N M τ mean k)
    (hY_frob : frobeniusNorm (p := p) (q := q) (σ := σ) Y ≤ 1) :
    frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
        (gamma (densityMatrix Y)) ≤
      M / Real.sqrt N := by
  have hsample :
      PptFactorization.HighProbabilityBounds.sampleOpNorm
        (p := p) (q := q) (σ := σ) Y ≤ M / Real.sqrt N :=
    backgroundTypicalSet_sampleOpNorm_bound
      (p := p) (q := q) (σ := σ) (N := N) (M := M)
      (τ := τ) (mean := mean) (k := k) hY
  have hsample_nonneg :
      0 ≤ PptFactorization.HighProbabilityBounds.sampleOpNorm
        (p := p) (q := q) (σ := σ) Y := by
    unfold PptFactorization.HighProbabilityBounds.sampleOpNorm
    positivity
  have htarget_nonneg : 0 ≤ M / Real.sqrt N := le_trans hsample_nonneg hsample
  have hY_nonneg :
      0 ≤ frobeniusNorm (p := p) (q := q) (σ := σ) Y := by
    unfold frobeniusNorm
    positivity
  calc
    frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
        (gamma (densityMatrix Y))
        ≤ PptFactorization.HighProbabilityBounds.sampleOpNorm
            (p := p) (q := q) (σ := σ) Y *
          frobeniusNorm (p := p) (q := q) (σ := σ) Y :=
          lower_gamma_densityMatrix_frobeniusNorm_le_sampleOpNorm_mul_frobeniusNorm
            (p := p) (q := q) (σ := σ) Y
    _ ≤ (M / Real.sqrt N) * 1 := by
          exact mul_le_mul hsample hY_frob hY_nonneg htarget_nonneg
    _ = M / Real.sqrt N := by ring

/-- Specialization of the background Frobenius envelope to the total normalized
deleted-column background used in the lower one-column decomposition. -/
theorem lower_backgroundTypicalSet_normalizedDeleted_gamma_densityMatrix_frobeniusNorm_bound
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    {N M τ mean : ℝ} {k : ℕ}
    (X : SampleMatrix p q σ) (α₀ : σ)
    (hY :
      sampleColumnComplementNormalized
        (p := p) (q := q) (σ := σ) X α₀ ∈
        backgroundTypicalSet
          (p := p) (q := q) (σ := σ) N M τ mean k) :
    frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
        (gamma (densityMatrix
          (sampleColumnComplementNormalized
            (p := p) (q := q) (σ := σ) X α₀))) ≤
      M / Real.sqrt N :=
  lower_backgroundTypicalSet_gamma_densityMatrix_frobeniusNorm_bound
    (p := p) (q := q) (σ := σ) (N := N) (M := M)
    (τ := τ) (mean := mean) (k := k)
    (Y := sampleColumnComplementNormalized
      (p := p) (q := q) (σ := σ) X α₀)
    hY
    (lower_sampleColumnComplementNormalized_frobeniusNorm_le_one
      (p := p) (q := q) (σ := σ) X α₀)

/-- Background-coordinate projection of the one-column favourable event. -/
theorem lower_sphericalOneColumnFavorableEvent_background_mem
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    {α₀ : σ} {q₀ δ : ℝ}
    {directionSet : Set (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundSet : Set (SampleMatrix p q σ)}
    {X : SampleMatrix p q σ}
    (hX :
      X ∈ sphericalOneColumnFavorableEvent
        (p := p) (q := q) (σ := σ)
        α₀ q₀ δ directionSet backgroundSet) :
    sampleColumnComplementNormalized (p := p) (q := q) (σ := σ) X α₀ ∈
      backgroundSet := by
  simpa [sphericalOneColumnFavorableEvent, sphericalColumnRectEvent] using hX.2.2

/-- Mass-coordinate projection of the one-column favourable event. -/
theorem lower_sphericalOneColumnFavorableEvent_mass_mem
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    {α₀ : σ} {q₀ δ : ℝ}
    {directionSet : Set (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundSet : Set (SampleMatrix p q σ)}
    {X : SampleMatrix p q σ}
    (hX :
      X ∈ sphericalOneColumnFavorableEvent
        (p := p) (q := q) (σ := σ)
        α₀ q₀ δ directionSet backgroundSet) :
    sampleColumnMass (p := p) (q := q) (σ := σ) X α₀ ∈
      betaColumnIntervalSet q₀ δ := by
  simpa [sphericalOneColumnFavorableEvent, sphericalColumnRectEvent] using hX.1

/-- Right endpoint bound for the Beta column interval. -/
theorem lower_mixed_betaColumnIntervalSet_right_le {q₀ δ R : ℝ} :
    R ∈ betaColumnIntervalSet q₀ δ →
      R ≤ betaColumnIntervalUpper q₀ δ := by
  intro hR
  simpa [betaColumnIntervalSet] using hR.2

/-- Left endpoint bound for the Beta column interval. -/
theorem lower_mixed_betaColumnIntervalSet_left_le {q₀ δ R : ℝ} :
    R ∈ betaColumnIntervalSet q₀ δ → q₀ ≤ R := by
  intro hR
  simpa [betaColumnIntervalSet] using hR.1

/-- The favourable event bounds the concrete spike-mass coefficient by the Beta
interval's upper endpoint. -/
theorem lower_sphericalOneColumnFavorableEvent_sampleColumnMass_le_intervalUpper
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    {α₀ : σ} {q₀ δ : ℝ}
    {directionSet : Set (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundSet : Set (SampleMatrix p q σ)}
    {X : SampleMatrix p q σ}
    (hX :
      X ∈ sphericalOneColumnFavorableEvent
        (p := p) (q := q) (σ := σ)
        α₀ q₀ δ directionSet backgroundSet) :
    sampleColumnMass (p := p) (q := q) (σ := σ) X α₀ ≤
      betaColumnIntervalUpper q₀ δ :=
  lower_mixed_betaColumnIntervalSet_right_le
    (lower_sphericalOneColumnFavorableEvent_mass_mem
      (p := p) (q := q) (σ := σ) (α₀ := α₀)
      (q₀ := q₀) (δ := δ) (directionSet := directionSet)
      (backgroundSet := backgroundSet) hX)

/-- If the Beta interval's left endpoint is positive, the favourable event makes
the distinguished column mass positive. -/
theorem lower_sphericalOneColumnFavorableEvent_sampleColumnMass_pos
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    {α₀ : σ} {q₀ δ : ℝ}
    {directionSet : Set (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundSet : Set (SampleMatrix p q σ)}
    {X : SampleMatrix p q σ}
    (hq₀ : 0 < q₀)
    (hX :
      X ∈ sphericalOneColumnFavorableEvent
        (p := p) (q := q) (σ := σ)
        α₀ q₀ δ directionSet backgroundSet) :
    0 < sampleColumnMass (p := p) (q := q) (σ := σ) X α₀ :=
  lt_of_lt_of_le hq₀
    (lower_mixed_betaColumnIntervalSet_left_le
      (lower_sphericalOneColumnFavorableEvent_mass_mem
        (p := p) (q := q) (σ := σ) (α₀ := α₀)
        (q₀ := q₀) (δ := δ) (directionSet := directionSet)
        (backgroundSet := backgroundSet) hX))

/-- Spike-letter Frobenius envelope from the one-column favourable event. -/
theorem lower_sphericalOneColumnFavorableEvent_columnSpikeMatrix_frobeniusNorm_le_intervalUpper
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    {α₀ : σ} {q₀ δ : ℝ}
    {directionSet : Set (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundSet : Set (SampleMatrix p q σ)}
    {X : SampleMatrix p q σ}
    (hq₀ : 0 < q₀)
    (hX :
      X ∈ sphericalOneColumnFavorableEvent
        (p := p) (q := q) (σ := σ)
        α₀ q₀ δ directionSet backgroundSet) :
    frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
        (columnSpikeMatrix (p := p) (q := q) (σ := σ) X α₀) ≤
      betaColumnIntervalUpper q₀ δ := by
  have hdir :
      ‖sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀‖ = 1 :=
    sampleColumnDirection_norm_eq_one_of_columnMass_pos
      (p := p) (q := q) (σ := σ) (X := X) (α₀ := α₀)
      (lower_sphericalOneColumnFavorableEvent_sampleColumnMass_pos
        (p := p) (q := q) (σ := σ) (α₀ := α₀)
        (q₀ := q₀) (δ := δ) (directionSet := directionSet)
        (backgroundSet := backgroundSet) hq₀ hX)
  calc
    frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
        (columnSpikeMatrix (p := p) (q := q) (σ := σ) X α₀)
        = sampleColumnMass (p := p) (q := q) (σ := σ) X α₀ :=
          lower_columnSpikeMatrix_frobeniusNorm_eq_mass
            (p := p) (q := q) (σ := σ) X α₀ hdir
    _ ≤ betaColumnIntervalUpper q₀ δ :=
          lower_sphericalOneColumnFavorableEvent_sampleColumnMass_le_intervalUpper
            (p := p) (q := q) (σ := σ) (α₀ := α₀)
            (q₀ := q₀) (δ := δ) (directionSet := directionSet)
            (backgroundSet := backgroundSet) hX

/-- Spike-letter operator-norm envelope from the one-column favourable event. -/
theorem lower_sphericalOneColumnFavorableEvent_columnSpikeMatrix_opNorm_le_intervalUpper
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    {α₀ : σ} {q₀ δ : ℝ}
    {directionSet : Set (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundSet : Set (SampleMatrix p q σ)}
    {X : SampleMatrix p q σ}
    (hq₀ : 0 < q₀)
    (hX :
      X ∈ sphericalOneColumnFavorableEvent
        (p := p) (q := q) (σ := σ)
        α₀ q₀ δ directionSet backgroundSet) :
    opNorm (p := p) (q := q)
        (columnSpikeMatrix (p := p) (q := q) (σ := σ) X α₀) ≤
      betaColumnIntervalUpper q₀ δ := by
  have hdir :
      ‖sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀‖ = 1 :=
    sampleColumnDirection_norm_eq_one_of_columnMass_pos
      (p := p) (q := q) (σ := σ) (X := X) (α₀ := α₀)
      (lower_sphericalOneColumnFavorableEvent_sampleColumnMass_pos
        (p := p) (q := q) (σ := σ) (α₀ := α₀)
        (q₀ := q₀) (δ := δ) (directionSet := directionSet)
        (backgroundSet := backgroundSet) hq₀ hX)
  exact
    le_trans
      (lower_columnSpikeMatrix_opNorm_le_mass
        (p := p) (q := q) (σ := σ) X α₀ hdir)
      (lower_sphericalOneColumnFavorableEvent_sampleColumnMass_le_intervalUpper
        (p := p) (q := q) (σ := σ) (α₀ := α₀)
        (q₀ := q₀) (δ := δ) (directionSet := directionSet)
        (backgroundSet := backgroundSet) hX)

/-- On the one-column favourable event, the normalized deleted background
inherits the `M / sqrt N` Frobenius envelope for its partially-transposed density
matrix from the `backgroundTypicalSet` component. -/
theorem lower_sphericalOneColumnFavorableEvent_normalizedDeleted_gamma_densityMatrix_frobeniusNorm_bound
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    {α₀ : σ} {q₀ δ N M τ mean : ℝ} {k : ℕ}
    {directionSet : Set (EuclideanSpace ℂ (BipIndex p q))}
    {X : SampleMatrix p q σ}
    (hX :
      X ∈ sphericalOneColumnFavorableEvent
        (p := p) (q := q) (σ := σ)
        α₀ q₀ δ directionSet
        (backgroundTypicalSet
          (p := p) (q := q) (σ := σ) N M τ mean k)) :
    frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
        (gamma (densityMatrix
          (sampleColumnComplementNormalized
            (p := p) (q := q) (σ := σ) X α₀))) ≤
      M / Real.sqrt N := by
  exact
    lower_backgroundTypicalSet_normalizedDeleted_gamma_densityMatrix_frobeniusNorm_bound
      (p := p) (q := q) (σ := σ) (N := N) (M := M)
      (τ := τ) (mean := mean) (k := k) X α₀
      (lower_sphericalOneColumnFavorableEvent_background_mem
        (p := p) (q := q) (σ := σ) (α₀ := α₀)
        (q₀ := q₀) (δ := δ) (directionSet := directionSet)
        (backgroundSet := backgroundTypicalSet
          (p := p) (q := q) (σ := σ) N M τ mean k)
        hX)

/-- Scaling a matrix by a real coefficient in `[0,1]` preserves any Frobenius
upper bound. -/
theorem lower_frobeniusNorm_real_smul_le_of_nonneg_le_one
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    {c bound : ℝ} {A : BipMatrix p q}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hA :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) A ≤ bound) :
    frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
        (((c : ℝ) : ℂ) • A) ≤ bound := by
  calc
    frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
        (((c : ℝ) : ℂ) • A)
        = c * frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) A := by
          unfold frobeniusNorm
          rw [norm_smul]
          simp [abs_of_nonneg hc0]
    _ ≤ 1 * bound := by
          have hA_nonneg :
              0 ≤ frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) A := by
            unfold frobeniusNorm
            positivity
          exact mul_le_mul hc1 hA hA_nonneg (by norm_num)
    _ = bound := by ring

/-- Scaling a matrix by a real coefficient in `[0,1]` preserves any operator-norm
upper bound. -/
theorem lower_opNorm_real_smul_le_of_nonneg_le_one
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    {c bound : ℝ} {A : BipMatrix p q}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hA : opNorm (p := p) (q := q) A ≤ bound) :
    opNorm (p := p) (q := q) (((c : ℝ) : ℂ) • A) ≤ bound := by
  calc
    opNorm (p := p) (q := q) (((c : ℝ) : ℂ) • A)
        = c * opNorm (p := p) (q := q) A := by
          unfold opNorm
          rw [map_smul, norm_smul]
          simp [abs_of_nonneg hc0]
    _ ≤ 1 * bound := by
          have hA_nonneg : 0 ≤ opNorm (p := p) (q := q) A := by
            unfold opNorm
            positivity
          exact mul_le_mul hc1 hA hA_nonneg (by norm_num)
    _ = bound := by ring

/-- Transport the normalized-background Frobenius envelope to the actual
deleted-column background matrix, assuming only the explicit scale condition
`‖X_{≠α₀}‖₂² ≤ 1`. -/
theorem lower_columnBackgroundMatrix_frobeniusNorm_bound_of_scale_le_one
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    {N M : ℝ} (X : SampleMatrix p q σ) (α₀ : σ)
    (hscale :
      frobeniusNorm (p := p) (q := q) (σ := σ)
          (sampleColumnComplement (p := p) (q := q) (σ := σ) X α₀) ^ 2 ≤
        1)
    (hBg :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
          (gamma (densityMatrix
            (sampleColumnComplementNormalized
              (p := p) (q := q) (σ := σ) X α₀))) ≤
        M / Real.sqrt N) :
    frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
        (columnBackgroundMatrix (p := p) (q := q) (σ := σ) X α₀) ≤
      M / Real.sqrt N := by
  rw [columnBackgroundMatrix_eq_norm_sq_smul_normalized
    (p := p) (q := q) (σ := σ) (α₀ := α₀) X]
  exact
    lower_frobeniusNorm_real_smul_le_of_nonneg_le_one
      (p := p) (q := q)
      (c := frobeniusNorm (p := p) (q := q) (σ := σ)
          (sampleColumnComplement (p := p) (q := q) (σ := σ) X α₀) ^ 2)
      (bound := M / Real.sqrt N)
      (A := gamma (densityMatrix
        (sampleColumnComplementNormalized
          (p := p) (q := q) (σ := σ) X α₀)))
      (sq_nonneg _) hscale hBg

/-- Transport the normalized-background operator-norm envelope to the actual
deleted-column background matrix, again keeping the scale condition explicit. -/
theorem lower_columnBackgroundMatrix_opNorm_bound_of_scale_le_one
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    {N M : ℝ} (X : SampleMatrix p q σ) (α₀ : σ)
    (hscale :
      frobeniusNorm (p := p) (q := q) (σ := σ)
          (sampleColumnComplement (p := p) (q := q) (σ := σ) X α₀) ^ 2 ≤
        1)
    (hBg :
      opNorm (p := p) (q := q)
          (gamma (densityMatrix
            (sampleColumnComplementNormalized
              (p := p) (q := q) (σ := σ) X α₀))) ≤
        M / N) :
    opNorm (p := p) (q := q)
        (columnBackgroundMatrix (p := p) (q := q) (σ := σ) X α₀) ≤
      M / N := by
  rw [columnBackgroundMatrix_eq_norm_sq_smul_normalized
    (p := p) (q := q) (σ := σ) (α₀ := α₀) X]
  exact
    lower_opNorm_real_smul_le_of_nonneg_le_one
      (p := p) (q := q)
      (c := frobeniusNorm (p := p) (q := q) (σ := σ)
          (sampleColumnComplement (p := p) (q := q) (σ := σ) X α₀) ^ 2)
      (bound := M / N)
      (A := gamma (densityMatrix
        (sampleColumnComplementNormalized
          (p := p) (q := q) (σ := σ) X α₀)))
      (sq_nonneg _) hscale hBg

/-- Concrete Frobenius background-letter envelope on the favourable event,
including the sphere-supported scale transfer. -/
theorem lower_sphericalOneColumnFavorableEvent_columnBackgroundMatrix_frobeniusNorm_bound
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    {α₀ : σ} {q₀ δ N M τ mean : ℝ} {k : ℕ}
    {directionSet : Set (EuclideanSpace ℂ (BipIndex p q))}
    {X : SampleMatrix p q σ}
    (hX :
      X ∈ sphericalOneColumnFavorableEvent
        (p := p) (q := q) (σ := σ)
        α₀ q₀ δ directionSet
        (backgroundTypicalSet
          (p := p) (q := q) (σ := σ) N M τ mean k))
    (hSphere : frobeniusNorm (p := p) (q := q) (σ := σ) X = 1) :
    frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
        (columnBackgroundMatrix (p := p) (q := q) (σ := σ) X α₀) ≤
      M / Real.sqrt N := by
  exact
    lower_columnBackgroundMatrix_frobeniusNorm_bound_of_scale_le_one
      (p := p) (q := q) (σ := σ) (N := N) (M := M) X α₀
      (lower_mixed_sampleColumnComplement_frobeniusNorm_sq_le_one_of_norm_one
        (p := p) (q := q) (σ := σ) (X := X) (α₀ := α₀) hSphere)
      (lower_sphericalOneColumnFavorableEvent_normalizedDeleted_gamma_densityMatrix_frobeniusNorm_bound
        (p := p) (q := q) (σ := σ) (α₀ := α₀)
        (q₀ := q₀) (δ := δ) (N := N) (M := M)
        (τ := τ) (mean := mean) (k := k)
        (directionSet := directionSet) hX)

/-- Concrete operator-norm background-letter envelope on the favourable event,
including the sphere-supported scale transfer. -/
theorem lower_sphericalOneColumnFavorableEvent_columnBackgroundMatrix_opNorm_bound
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    {α₀ : σ} {q₀ δ N M τ mean : ℝ} {k : ℕ}
    {directionSet : Set (EuclideanSpace ℂ (BipIndex p q))}
    {X : SampleMatrix p q σ}
    (hX :
      X ∈ sphericalOneColumnFavorableEvent
        (p := p) (q := q) (σ := σ)
        α₀ q₀ δ directionSet
        (backgroundTypicalSet
          (p := p) (q := q) (σ := σ) N M τ mean k))
    (hSphere : frobeniusNorm (p := p) (q := q) (σ := σ) X = 1) :
    opNorm (p := p) (q := q)
        (columnBackgroundMatrix (p := p) (q := q) (σ := σ) X α₀) ≤
      M / N := by
  have hY :
      sampleColumnComplementNormalized
        (p := p) (q := q) (σ := σ) X α₀ ∈
        backgroundTypicalSet
          (p := p) (q := q) (σ := σ) N M τ mean k :=
    lower_sphericalOneColumnFavorableEvent_background_mem
      (p := p) (q := q) (σ := σ) (α₀ := α₀)
      (q₀ := q₀) (δ := δ) (directionSet := directionSet)
      (backgroundSet := backgroundTypicalSet
        (p := p) (q := q) (σ := σ) N M τ mean k)
      hX
  exact
    lower_columnBackgroundMatrix_opNorm_bound_of_scale_le_one
      (p := p) (q := q) (σ := σ) (N := N) (M := M) X α₀
      (lower_mixed_sampleColumnComplement_frobeniusNorm_sq_le_one_of_norm_one
        (p := p) (q := q) (σ := σ) (X := X) (α₀ := α₀) hSphere)
      (backgroundTypicalSet_gammaOpNorm_bound
        (p := p) (q := q) (σ := σ) (N := N) (M := M)
        (τ := τ) (mean := mean) (k := k)
        (Y := sampleColumnComplementNormalized
          (p := p) (q := q) (σ := σ) X α₀)
        hY)

/-- Sharp cyclic bound for a mixed word with exactly one spike factor.

This is the first lower-specific replacement for the older one-defect
trace-norm envelope.  It uses
`|Re Tr(S B^(k-1))| ≤ ‖S‖₂ ‖B^(k-1)‖₂`, so the spike contributes only its
Frobenius norm.  The dimension gain comes from the background envelope
`‖B‖op ≤ M / N` together with `‖B‖₂ ≤ M / sqrt N`. -/
theorem lower_trace_one_spike_cyclic_bound
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    {N M : ℝ} {k : ℕ} {S B : BipMatrix p q}
    (hk : 3 ≤ k)
    (hS_frob :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) S ≤ 1)
    (hB_op : opNorm (p := p) (q := q) B ≤ M / N)
    (hB_frob :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) B ≤
        M / Real.sqrt N) :
    |(Matrix.trace (S * B ^ (k - 1))).re| ≤
      (M / N) ^ (k - 2) * (M / Real.sqrt N) := by
  have hk2 : k - 1 = (k - 2) + 1 := by omega
  have htrace :=
    matrix_abs_re_trace_mul_le_frobenius_norm_mul
      (n := BipIndex p q) S (B ^ (k - 1))
  have hBop_nonneg : 0 ≤ opNorm (p := p) (q := q) B := by
    unfold opNorm
    positivity
  have hBfrob_nonneg :
      0 ≤ frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) B := by
    unfold frobeniusNorm
    positivity
  have hMN_nonneg : 0 ≤ M / N := le_trans hBop_nonneg hB_op
  have hpow_le :
      opNorm (p := p) (q := q) B ^ (k - 2) ≤
        (M / N) ^ (k - 2) :=
    pow_le_pow_left₀ hBop_nonneg hB_op (k - 2)
  have hfrob_pow :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
          (B ^ (k - 1)) ≤
        opNorm (p := p) (q := q) B ^ (k - 2) *
          frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) B := by
    simpa [hk2] using
      lower_frobeniusNorm_pow_succ_le_opNorm_pow_mul_frobeniusNorm
        (p := p) (q := q) B (k - 2)
  have hprod_le :
      opNorm (p := p) (q := q) B ^ (k - 2) *
          frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) B ≤
        (M / N) ^ (k - 2) * (M / Real.sqrt N) := by
    exact
      mul_le_mul hpow_le hB_frob hBfrob_nonneg
        (pow_nonneg hMN_nonneg _)
  have hfrob_pow' :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
          (B ^ (k - 1)) ≤
        (M / N) ^ (k - 2) * (M / Real.sqrt N) :=
    le_trans hfrob_pow hprod_le
  have hleft :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) S *
          frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
            (B ^ (k - 1)) ≤
        1 * ((M / N) ^ (k - 2) * (M / Real.sqrt N)) := by
    exact
      mul_le_mul hS_frob hfrob_pow'
        (by unfold frobeniusNorm; positivity) (by norm_num)
  calc
    |(Matrix.trace (S * B ^ (k - 1))).re| ≤
        frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) S *
          frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
            (B ^ (k - 1)) := by
          simpa [frobeniusNorm] using htrace
    _ ≤ 1 * ((M / N) ^ (k - 2) * (M / Real.sqrt N)) := hleft
    _ = (M / N) ^ (k - 2) * (M / Real.sqrt N) := by ring

/-- Generalized one-spike cyclic bound with an arbitrary Frobenius bound for
the spike letter.

This is the form used for the local-expansion `Q` letter, which already
contains the column-mass factor. -/
theorem lower_trace_one_spike_cyclic_bound_with_frobenius
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    {N M Sbound : ℝ} {k : ℕ} {S B : BipMatrix p q}
    (hk : 3 ≤ k)
    (hSbound_nonneg : 0 ≤ Sbound)
    (hS_frob :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) S ≤ Sbound)
    (hB_op : opNorm (p := p) (q := q) B ≤ M / N)
    (hB_frob :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) B ≤
        M / Real.sqrt N) :
    |(Matrix.trace (S * B ^ (k - 1))).re| ≤
      Sbound * ((M / N) ^ (k - 2) * (M / Real.sqrt N)) := by
  have hk2 : k - 1 = (k - 2) + 1 := by omega
  have htrace :=
    matrix_abs_re_trace_mul_le_frobenius_norm_mul
      (n := BipIndex p q) S (B ^ (k - 1))
  have hBop_nonneg : 0 ≤ opNorm (p := p) (q := q) B := by
    unfold opNorm
    positivity
  have hBfrob_nonneg :
      0 ≤ frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) B := by
    unfold frobeniusNorm
    positivity
  have hMN_nonneg : 0 ≤ M / N := le_trans hBop_nonneg hB_op
  have hpow_le :
      opNorm (p := p) (q := q) B ^ (k - 2) ≤
        (M / N) ^ (k - 2) :=
    pow_le_pow_left₀ hBop_nonneg hB_op (k - 2)
  have hfrob_pow :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
          (B ^ (k - 1)) ≤
        opNorm (p := p) (q := q) B ^ (k - 2) *
          frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) B := by
    simpa [hk2] using
      lower_frobeniusNorm_pow_succ_le_opNorm_pow_mul_frobeniusNorm
        (p := p) (q := q) B (k - 2)
  have hprod_le :
      opNorm (p := p) (q := q) B ^ (k - 2) *
          frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) B ≤
        (M / N) ^ (k - 2) * (M / Real.sqrt N) := by
    exact
      mul_le_mul hpow_le hB_frob hBfrob_nonneg
        (pow_nonneg hMN_nonneg _)
  have hfrob_pow' :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
          (B ^ (k - 1)) ≤
        (M / N) ^ (k - 2) * (M / Real.sqrt N) :=
    le_trans hfrob_pow hprod_le
  have hleft :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) S *
          frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
            (B ^ (k - 1)) ≤
        Sbound * ((M / N) ^ (k - 2) * (M / Real.sqrt N)) := by
    exact
      mul_le_mul hS_frob hfrob_pow'
        (by unfold frobeniusNorm; positivity) hSbound_nonneg
  calc
    |(Matrix.trace (S * B ^ (k - 1))).re| ≤
        frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) S *
          frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
            (B ^ (k - 1)) := by
          simpa [frobeniusNorm] using htrace
    _ ≤ Sbound * ((M / N) ^ (k - 2) * (M / Real.sqrt N)) := hleft

/-- Split trace bound for a word carrying at least two spike factors.

After cyclic rotation, such a word has the form `C*S*D*S`, where the operator
norms of `C` and `D` account for all background factors and any extra spike
factors.  This lemma is the finite-dimensional analytic estimate; the
remaining combinatorial task is to rotate/split an arbitrary two-letter mixed
word into this form and count its background factors. -/
theorem lower_trace_two_spike_split_bound
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    {c d : ℝ} {S C D : BipMatrix p q}
    (hS_frob :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) S ≤ 1)
    (hC_op : opNorm (p := p) (q := q) C ≤ c)
    (hD_op : opNorm (p := p) (q := q) D ≤ d) :
    |(Matrix.trace ((C * S) * (D * S))).re| ≤ c * d := by
  have htrace :=
    matrix_abs_re_trace_mul_le_frobenius_norm_mul
      (n := BipIndex p q) (C * S) (D * S)
  have hS_nonneg :
      0 ≤ frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) S := by
    unfold frobeniusNorm
    positivity
  have hC_nonneg : 0 ≤ opNorm (p := p) (q := q) C := by
    unfold opNorm
    positivity
  have hD_nonneg : 0 ≤ opNorm (p := p) (q := q) D := by
    unfold opNorm
    positivity
  have hc_nonneg : 0 ≤ c := le_trans hC_nonneg hC_op
  have hd_nonneg : 0 ≤ d := le_trans hD_nonneg hD_op
  have hCS :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) (C * S) ≤ c := by
    calc
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) (C * S)
          ≤ opNorm (p := p) (q := q) C *
              frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) S :=
            lower_frobeniusNorm_mul_le_opNorm_mul_frobeniusNorm
              (p := p) (q := q) C S
      _ ≤ c * 1 := by
            exact mul_le_mul hC_op hS_frob hS_nonneg hc_nonneg
      _ = c := by ring
  have hDS :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) (D * S) ≤ d := by
    calc
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) (D * S)
          ≤ opNorm (p := p) (q := q) D *
              frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) S :=
            lower_frobeniusNorm_mul_le_opNorm_mul_frobeniusNorm
              (p := p) (q := q) D S
      _ ≤ d * 1 := by
            exact mul_le_mul hD_op hS_frob hS_nonneg hd_nonneg
      _ = d := by ring
  have hDS_nonneg :
      0 ≤ frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) (D * S) := by
    unfold frobeniusNorm
    positivity
  calc
    |(Matrix.trace ((C * S) * (D * S))).re| ≤
        frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) (C * S) *
          frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) (D * S) := by
          simpa [frobeniusNorm] using htrace
    _ ≤ c * d := by
          exact mul_le_mul hCS hDS hDS_nonneg hc_nonneg

/-- Generalized two-spike split bound with an arbitrary Frobenius bound for the
distinguished spike letter.

This is the form used when the local-expansion `Q` letter already carries the
column-mass factor.  Any extra spike letters belong to `C` or `D` and are
accounted for by their operator-norm bounds. -/
theorem lower_trace_two_spike_split_bound_with_frobenius
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    {c d Sbound : ℝ} {S C D : BipMatrix p q}
    (hSbound_nonneg : 0 ≤ Sbound)
    (hS_frob :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) S ≤ Sbound)
    (hC_op : opNorm (p := p) (q := q) C ≤ c)
    (hD_op : opNorm (p := p) (q := q) D ≤ d) :
    |(Matrix.trace ((C * S) * (D * S))).re| ≤
      (c * Sbound) * (d * Sbound) := by
  have htrace :=
    matrix_abs_re_trace_mul_le_frobenius_norm_mul
      (n := BipIndex p q) (C * S) (D * S)
  have hS_nonneg :
      0 ≤ frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) S := by
    unfold frobeniusNorm
    positivity
  have hC_nonneg : 0 ≤ opNorm (p := p) (q := q) C := by
    unfold opNorm
    positivity
  have hD_nonneg : 0 ≤ opNorm (p := p) (q := q) D := by
    unfold opNorm
    positivity
  have hc_nonneg : 0 ≤ c := le_trans hC_nonneg hC_op
  have hd_nonneg : 0 ≤ d := le_trans hD_nonneg hD_op
  have hCS :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) (C * S) ≤
        c * Sbound := by
    calc
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) (C * S)
          ≤ opNorm (p := p) (q := q) C *
              frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) S :=
            lower_frobeniusNorm_mul_le_opNorm_mul_frobeniusNorm
              (p := p) (q := q) C S
      _ ≤ c * Sbound := by
            exact mul_le_mul hC_op hS_frob hS_nonneg hc_nonneg
  have hDS :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) (D * S) ≤
        d * Sbound := by
    calc
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) (D * S)
          ≤ opNorm (p := p) (q := q) D *
              frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) S :=
            lower_frobeniusNorm_mul_le_opNorm_mul_frobeniusNorm
              (p := p) (q := q) D S
      _ ≤ d * Sbound := by
            exact mul_le_mul hD_op hS_frob hS_nonneg hd_nonneg
  have hDS_nonneg :
      0 ≤ frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) (D * S) := by
    unfold frobeniusNorm
    positivity
  have hCSbound_nonneg : 0 ≤ c * Sbound :=
    mul_nonneg hc_nonneg hSbound_nonneg
  calc
    |(Matrix.trace ((C * S) * (D * S))).re| ≤
        frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) (C * S) *
          frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) (D * S) := by
          simpa [frobeniusNorm] using htrace
    _ ≤ (c * Sbound) * (d * Sbound) := by
          exact mul_le_mul hCS hDS hDS_nonneg hCSbound_nonneg

/-! ### Scalar envelope for partial-transpose mixed words -/

/-- Scalar envelope for partial-transpose mixed words after normalization by
`N^(k-1)`.

This is the envelope for the actual partial-transpose expansion.  It is not
the ordinary Gram/rank-one `O(R)` mixed estimate: the one-spike term uses a
Frobenius trace pairing and the background edge scale `‖B‖op ≤ M / N`, while
the terms with at least two spike letters use the cyclic two-spike split. -/
noncomputable def lowerPartialTransposeMixedErrorN
    (k : ℕ) (A M N : ℝ) : ℝ :=
  (k : ℝ) * A * M ^ (k - 1) *
      N ^ ((-1 / 2 : ℝ) + 1 / (k : ℝ)) +
    (Finset.Icc 2 (k - 1)).sum (fun j =>
      (Nat.choose k j : ℝ) * A ^ j * M ^ (k - j) *
        N ^ ((j : ℝ) / (k : ℝ) - 1))

/-- The partial-transpose mixed envelope is nonnegative for nonnegative scalar
parameters. -/
theorem lowerPartialTransposeMixedErrorN_nonneg
    {k : ℕ} {A M N : ℝ}
    (hA : 0 ≤ A) (hM : 0 ≤ M) (hN : 0 ≤ N) :
    0 ≤ lowerPartialTransposeMixedErrorN k A M N := by
  unfold lowerPartialTransposeMixedErrorN
  apply add_nonneg
  · positivity
  · exact Finset.sum_nonneg (fun j _ => by positivity)

/-- The same partial-transpose mixed envelope in the concrete `d`-scaling
`N = d^2`. -/
noncomputable def lowerPartialTransposeMixedErrorD
    (k : ℕ) (A M : ℝ) (d : ℕ) : ℝ :=
  lowerPartialTransposeMixedErrorN k A M ((d : ℝ) ^ 2)

/-- The concrete `d`-scaled partial-transpose mixed envelope is nonnegative for
nonnegative scalar parameters. -/
theorem lowerPartialTransposeMixedErrorD_nonneg
    {k d : ℕ} {A M : ℝ}
    (hA : 0 ≤ A) (hM : 0 ≤ M) :
    0 ≤ lowerPartialTransposeMixedErrorD k A M d := by
  unfold lowerPartialTransposeMixedErrorD
  exact lowerPartialTransposeMixedErrorN_nonneg
    (k := k) (A := A) (M := M) (N := (d : ℝ) ^ 2)
    hA hM (by positivity)

/-- Negative powers of the concrete dimension scale `d^2` tend to zero. -/
theorem lower_rpow_dsq_neg_tendsto_zero {y : ℝ} (hy : 0 < y) :
    Tendsto (fun d : ℕ => ((d : ℝ) ^ 2) ^ (-y)) atTop (nhds 0) := by
  have hbase : Tendsto (fun d : ℕ => ((d : ℝ) ^ 2 : ℝ)) atTop atTop := by
    simpa [Real.rpow_natCast] using
      ((tendsto_rpow_atTop (show (0 : ℝ) < 2 by norm_num)).comp
        (tendsto_natCast_atTop_atTop :
          Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop))
  exact (tendsto_rpow_neg_atTop hy).comp hbase

/-- The corrected partial-transpose mixed envelope is `o(1)` in the concrete
`d`-scaling for every fixed `A`, `M`, and `k ≥ 3`. -/
theorem lowerPartialTransposeMixedErrorD_tendsto_zero
    {k : ℕ} (hk3 : 3 ≤ k) (A M : ℝ) :
    Tendsto (fun d : ℕ => lowerPartialTransposeMixedErrorD k A M d)
      atTop (nhds 0) := by
  unfold lowerPartialTransposeMixedErrorD lowerPartialTransposeMixedErrorN
  have hkposN : 0 < k := Nat.lt_of_lt_of_le (by decide : 0 < 3) hk3
  have hkRpos : 0 < (k : ℝ) := by exact_mod_cast hkposN
  have hhalf_gap : 0 < (1 / 2 : ℝ) - 1 / (k : ℝ) := by
    have hkR_ge3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk3
    have hle : (1 : ℝ) / (k : ℝ) ≤ 1 / 3 := by
      exact one_div_le_one_div_of_le (by norm_num) hkR_ge3
    linarith
  have hfirst_pow :
      Tendsto
        (fun d : ℕ =>
          ((d : ℝ) ^ 2) ^ (-( (1 / 2 : ℝ) - 1 / (k : ℝ))))
        atTop (nhds 0) :=
    lower_rpow_dsq_neg_tendsto_zero hhalf_gap
  have hfirst :
      Tendsto
        (fun d : ℕ =>
          (k : ℝ) * A * M ^ (k - 1) *
            ((d : ℝ) ^ 2) ^ ((-1 / 2 : ℝ) + 1 / (k : ℝ)))
        atTop (nhds 0) := by
    have hmul :=
      (tendsto_const_nhds (x := (k : ℝ) * A * M ^ (k - 1))).mul
        hfirst_pow
    have hmul0 :
        Tendsto
          (fun d : ℕ =>
            (k : ℝ) * A * M ^ (k - 1) *
              ((d : ℝ) ^ 2) ^ (-( (1 / 2 : ℝ) - 1 / (k : ℝ))))
          atTop (nhds 0) := by
      simpa using hmul
    refine hmul0.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with d _hd
    have hexp :
        ((-1 / 2 : ℝ) + 1 / (k : ℝ)) =
          -((1 / 2 : ℝ) - 1 / (k : ℝ)) := by
      ring
    rw [hexp]
  have hsum0 :
      Tendsto
        (fun d : ℕ =>
          (Finset.Icc 2 (k - 1)).sum (fun j =>
            (Nat.choose k j : ℝ) * A ^ j * M ^ (k - j) *
              ((d : ℝ) ^ 2) ^ ((j : ℝ) / (k : ℝ) - 1)))
        atTop (nhds ((Finset.Icc 2 (k - 1)).sum (fun _j => (0 : ℝ)))) := by
    refine tendsto_finset_sum (Finset.Icc 2 (k - 1)) (fun j hj => ?_)
    have hj_le : j ≤ k - 1 := (Finset.mem_Icc.mp hj).2
    have hj_lt : j < k := by omega
    have hgap : 0 < (1 : ℝ) - (j : ℝ) / (k : ℝ) := by
      have hjR_lt : (j : ℝ) < (k : ℝ) := by exact_mod_cast hj_lt
      have hdiv : (j : ℝ) / (k : ℝ) < 1 := by
        rw [div_lt_one hkRpos]
        simpa using hjR_lt
      linarith
    have hjpow :
        Tendsto
          (fun d : ℕ =>
            ((d : ℝ) ^ 2) ^ (-( (1 : ℝ) - (j : ℝ) / (k : ℝ))))
          atTop (nhds 0) :=
      lower_rpow_dsq_neg_tendsto_zero hgap
    have hmul :=
      (tendsto_const_nhds
        (x := (Nat.choose k j : ℝ) * A ^ j * M ^ (k - j))).mul
        hjpow
    have hmul0 :
        Tendsto
          (fun d : ℕ =>
            (Nat.choose k j : ℝ) * A ^ j * M ^ (k - j) *
              ((d : ℝ) ^ 2) ^ (-( (1 : ℝ) - (j : ℝ) / (k : ℝ))))
          atTop (nhds 0) := by
      simpa using hmul
    refine hmul0.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with d _hd
    have hexp :
        ((j : ℝ) / (k : ℝ) - 1) =
          -((1 : ℝ) - (j : ℝ) / (k : ℝ)) := by
      ring
    rw [hexp]
  have hsum :
      Tendsto
        (fun d : ℕ =>
          (Finset.Icc 2 (k - 1)).sum (fun j =>
            (Nat.choose k j : ℝ) * A ^ j * M ^ (k - j) *
              ((d : ℝ) ^ 2) ^ ((j : ℝ) / (k : ℝ) - 1)))
        atTop (nhds 0) := by
    simpa using hsum0
  simpa using hfirst.add hsum

/-- Eventual smallness form of
`lowerPartialTransposeMixedErrorD_tendsto_zero`. -/
theorem lowerPartialTransposeMixedErrorD_eventually_le
    {k : ℕ} (hk3 : 3 ≤ k) (A M η : ℝ) (hη : 0 < η) :
    ∀ᶠ d in atTop, lowerPartialTransposeMixedErrorD k A M d ≤ η := by
  have hlim :
      Tendsto (fun d : ℕ => lowerPartialTransposeMixedErrorD k A M d)
        atTop (nhds 0) :=
    lowerPartialTransposeMixedErrorD_tendsto_zero (k := k) hk3 A M
  have hlt : ∀ᶠ d in atTop, lowerPartialTransposeMixedErrorD k A M d < η := by
    exact (tendsto_order.1 hlim).2 η hη
  filter_upwards [hlt] with d hd
  exact le_of_lt hd

/-- Paper-facing `d`-variable name for the corrected partial-transpose mixed
error.

This is the explicit endpoint error
`k A M^(k-1) d^(-1+2/k) + Σ_{j=2}^{k-1} choose k j A^j M^(k-j)
d^(-2+2j/k)`, represented through the already-verified `N = d^2`
normalization. -/
noncomputable def errMixPT (k : ℕ) (A M d : ℝ) : ℝ :=
  lowerPartialTransposeMixedErrorN k A M (d ^ 2)

/-- The paper-facing `errMixPT` agrees definitionally with the existing
natural-dimension envelope used by the lower-bound endpoint. -/
theorem errMixPT_natCast_eq_lowerPartialTransposeMixedErrorD
    (k : ℕ) (A M : ℝ) (d : ℕ) :
    errMixPT k A M (d : ℝ) = lowerPartialTransposeMixedErrorD k A M d := by
  rfl

/-- Endpoint-facing name for the smallness of the corrected PT mixed error. -/
theorem errMixPT_tendsto_zero
    {k : ℕ} (hk3 : 3 ≤ k) (A M : ℝ) :
    Tendsto (fun d : ℕ => errMixPT k A M (d : ℝ)) atTop (nhds 0) := by
  simpa [errMixPT, lowerPartialTransposeMixedErrorD] using
    (lowerPartialTransposeMixedErrorD_tendsto_zero (k := k) hk3 A M)

/-- Endpoint-facing eventual smallness form of `errMixPT_tendsto_zero`. -/
theorem errMixPT_eventually_le
    {k : ℕ} (hk3 : 3 ≤ k) (A M η : ℝ) (hη : 0 < η) :
    ∀ᶠ d : ℕ in atTop, errMixPT k A M (d : ℝ) ≤ η := by
  simpa [errMixPT, lowerPartialTransposeMixedErrorD] using
    (lowerPartialTransposeMixedErrorD_eventually_le
      (k := k) hk3 A M η hη)

/-!
The hard part of the mixed supplier is not the passage from an absolute mixed
envelope to the one-sided lower estimate required by the lower-bound endpoint.
That passage is already closed by `columnMixedRemainder_lower_of_abs_envelope`.
The theorem below makes the remaining debt explicit: it suffices to prove the
concrete absolute envelope on the one-column favourable event.
-/
theorem lower_mixedLower_pointwise_concreteChoices_of_absEnvelope
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (ε a slack : ℝ) (d : ℕ)
    (hs : 0 < R.sample d)
    (X : SampleMatrix (Fin d) (Fin d) (Fin (R.sample d)))
    (hEnvelope :
      |columnMixedRemainder
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        (lowerConcreteN d) k X (⟨0, hs⟩ : Fin (R.sample d))| ≤
          lowerConcreteMixedError R k ε a slack d) :
    -lowerConcreteMixedError R k ε a slack d ≤
      columnMixedRemainder
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        (lowerConcreteN d) k X (⟨0, hs⟩ : Fin (R.sample d)) := by
  exact
    columnMixedRemainder_lower_of_abs_envelope
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      (α₀ := (⟨0, hs⟩ : Fin (R.sample d)))
      (N := lowerConcreteN d)
      (errMix := lowerConcreteMixedError R k ε a slack d)
      (k := k) (X := X) hEnvelope

theorem lower_mixedLower_concreteChoices_of_eventual_absEnvelope
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ}
    (hEnvelope :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ hs : 0 < R.sample d,
              ∀ X : SampleMatrix (Fin d) (Fin d) (Fin (R.sample d)),
                X ∈
                  sphericalOneColumnFavorableEvent
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (⟨0, hs⟩ : Fin (R.sample d))
                    (betaColumnSpikeScale
                      (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                    (lowerConcreteDelta a slack d)
                    (lowerConcreteDirectionCapSet
                      lowerConcreteCanonicalDirection a slack d)
                    (backgroundTypicalSet
                      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                      (lowerConcreteN d) (lowerConcreteM R a slack d)
                      (lowerConcreteTau a slack d)
                      (lowerConcreteDeletedBackgroundMean R k d) k) →
                |columnMixedRemainder
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) k X
                    (⟨0, hs⟩ : Fin (R.sample d))| ≤
                  lowerConcreteMixedError R k ε a slack d) :
    lowerConcreteMixedLowerBound R lowerConcreteCanonicalDirection
      (lowerConcreteM R)
      lowerConcreteTau
      (fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
      (lowerConcreteMixedError R k ε) k ε := by
  intro a ha slack hslack
  filter_upwards [hEnvelope a ha slack hslack] with d hd
  intro hs X hFav
  exact
    lower_mixedLower_pointwise_concreteChoices_of_absEnvelope
      (R := R) (k := k) (ε := ε) (a := a) (slack := slack)
      (d := d) hs X (hd hs X hFav)

theorem lower_mixedLower_concreteChoices_of_eventual_localExpansionEnvelope
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ}
    (hEnvelope :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ hs : 0 < R.sample d,
              ∀ X : SampleMatrix (Fin d) (Fin d) (Fin (R.sample d)),
                X ∈
                  sphericalOneColumnFavorableEvent
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (⟨0, hs⟩ : Fin (R.sample d))
                    (betaColumnSpikeScale
                      (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                    (lowerConcreteDelta a slack d)
                    (lowerConcreteDirectionCapSet
                      lowerConcreteCanonicalDirection a slack d)
                    (backgroundTypicalSet
                      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                      (lowerConcreteN d) (lowerConcreteM R a slack d)
                      (lowerConcreteTau a slack d)
                      (lowerConcreteDeletedBackgroundMean R k d) k) →
                |localExpansionMixedRemainder (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k
                    (columnBackgroundMatrix
                      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                      X (⟨0, hs⟩ : Fin (R.sample d)))
                    0
                    (columnSpikeMatrix
                      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                      X (⟨0, hs⟩ : Fin (R.sample d)))| ≤
                  lowerConcreteMixedError R k ε a slack d) :
    lowerConcreteMixedLowerBound R lowerConcreteCanonicalDirection
      (lowerConcreteM R)
      lowerConcreteTau
      (fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
      (lowerConcreteMixedError R k ε) k ε := by
  refine
    lower_mixedLower_concreteChoices_of_eventual_absEnvelope
      (R := R) (k := k) (ε := ε) ?_
  intro a ha slack hslack
  filter_upwards [hEnvelope a ha slack hslack] with d hd
  intro hs X hFav
  exact
    lower_columnMixedRemainder_abs_le_of_localExpansion_zeroLinear
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      (N := lowerConcreteN d)
      (errMix := lowerConcreteMixedError R k ε a slack d)
      (k := k) (X := X) (α₀ := (⟨0, hs⟩ : Fin (R.sample d)))
      (hd hs X hFav)

/-- Exact remaining mixed-word frontier for the concrete lower endpoint.

The bridge from an absolute mixed envelope to the one-sided lower estimate is
already closed above.  This proposition names the remaining local-expansion
estimate on the spherical one-column favourable event. -/
def lowerConcreteMixedLocalExpansionEnvelope
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (ε : ℝ) : Prop :=
  ∀ a : ℝ, spikeRoot k ε < a →
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        ∀ hs : 0 < R.sample d,
          ∀ X : SampleMatrix (Fin d) (Fin d) (Fin (R.sample d)),
            X ∈
              sphericalOneColumnFavorableEvent
                (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                (⟨0, hs⟩ : Fin (R.sample d))
                (betaColumnSpikeScale
                  (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                (lowerConcreteDelta a slack d)
                (lowerConcreteDirectionCapSet
                  lowerConcreteCanonicalDirection a slack d)
                (backgroundTypicalSet
                  (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                  (lowerConcreteN d) (lowerConcreteM R a slack d)
                  (lowerConcreteTau a slack d)
                  (lowerConcreteDeletedBackgroundMean R k d) k) →
            |localExpansionMixedRemainder (p := Fin d) (q := Fin d)
                (lowerConcreteN d) k
                (columnBackgroundMatrix
                  (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                  X (⟨0, hs⟩ : Fin (R.sample d)))
                0
                (columnSpikeMatrix
                  (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                  X (⟨0, hs⟩ : Fin (R.sample d)))| ≤
              lowerConcreteMixedError R k ε a slack d

/-- Corrected mixed local-expansion frontier with an explicit error sequence.

The older concrete frontier above hard-codes
`lowerConcreteMixedError R k ε a slack d = 1 / d`.  That is stronger than what
the deterministic mixed-word envelope naturally supplies in general.  This
version exposes the mixed error sequence explicitly; downstream lower endpoints
only need this sequence to be eventually small. -/
def lowerConcreteMixedLocalExpansionEnvelopeWithError
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (ε : ℝ)
    (errMix : ℝ → ℝ → ℕ → ℝ) : Prop :=
  ∀ a : ℝ, spikeRoot k ε < a →
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        ∀ hs : 0 < R.sample d,
          ∀ X : SampleMatrix (Fin d) (Fin d) (Fin (R.sample d)),
            X ∈
              sphericalOneColumnFavorableEvent
                (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                (⟨0, hs⟩ : Fin (R.sample d))
                (betaColumnSpikeScale
                  (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                (lowerConcreteDelta a slack d)
                (lowerConcreteDirectionCapSet
                  lowerConcreteCanonicalDirection a slack d)
                (backgroundTypicalSet
                  (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                  (lowerConcreteN d) (lowerConcreteM R a slack d)
                  (lowerConcreteTau a slack d)
                  (lowerConcreteDeletedBackgroundMean R k d) k) →
            |localExpansionMixedRemainder (p := Fin d) (q := Fin d)
                (lowerConcreteN d) k
                (columnBackgroundMatrix
                  (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                  X (⟨0, hs⟩ : Fin (R.sample d)))
                0
                (columnSpikeMatrix
                  (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                  X (⟨0, hs⟩ : Fin (R.sample d)))| ≤
              errMix a slack d

/-- Sphere-supported mixed lower-bound predicate.

The deterministic mixed-word estimate uses the Frobenius-sphere identity that
the deleted background has scale `1 - R`.  Without this support hypothesis,
normalized-background typicality alone does not control the scale of the
deleted block. -/
def lowerConcreteMixedLowerBoundOnSphere
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)))
    (M τ center errMix : ℝ → ℝ → ℕ → ℝ) (k : ℕ) (ε : ℝ) : Prop :=
  ∀ a : ℝ, spikeRoot k ε < a →
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        ∀ hs : 0 < R.sample d,
          ∀ X : SampleMatrix (Fin d) (Fin d) (Fin (R.sample d)),
            X ∈
              sphericalOneColumnFavorableEvent
                (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                (⟨0, hs⟩ : Fin (R.sample d))
                (betaColumnSpikeScale
                  (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                (lowerConcreteDelta a slack d)
                (lowerConcreteDirectionCapSet e a slack d)
                (backgroundTypicalSet
                  (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                  (lowerConcreteN d) (M a slack d) (τ a slack d)
                  (center a slack d) k) →
            frobeniusNorm (p := Fin d) (q := Fin d)
                (σ := Fin (R.sample d)) X = 1 →
            -errMix a slack d ≤
              columnMixedRemainder
                (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                (lowerConcreteN d) k X (⟨0, hs⟩ : Fin (R.sample d))

/-- Corrected mixed local-expansion frontier on the Frobenius sphere.

This is the right deterministic target for the two-letter spike/background
word estimate. -/
def lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithError
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (ε : ℝ)
    (errMix : ℝ → ℝ → ℕ → ℝ) : Prop :=
  ∀ a : ℝ, spikeRoot k ε < a →
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        ∀ hs : 0 < R.sample d,
          ∀ X : SampleMatrix (Fin d) (Fin d) (Fin (R.sample d)),
            X ∈
              sphericalOneColumnFavorableEvent
                (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                (⟨0, hs⟩ : Fin (R.sample d))
                (betaColumnSpikeScale
                  (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                (lowerConcreteDelta a slack d)
                (lowerConcreteDirectionCapSet
                  lowerConcreteCanonicalDirection a slack d)
                (backgroundTypicalSet
                  (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                  (lowerConcreteN d) (lowerConcreteM R a slack d)
                  (lowerConcreteTau a slack d)
                  (lowerConcreteDeletedBackgroundMean R k d) k) →
            frobeniusNorm (p := Fin d) (q := Fin d)
                (σ := Fin (R.sample d)) X = 1 →
            |localExpansionMixedRemainder (p := Fin d) (q := Fin d)
                (lowerConcreteN d) k
                (columnBackgroundMatrix
                  (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                  X (⟨0, hs⟩ : Fin (R.sample d)))
                0
                (columnSpikeMatrix
                  (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                  X (⟨0, hs⟩ : Fin (R.sample d)))| ≤
              errMix a slack d

/-- The old fixed-budget mixed envelope is the special case of the explicit
error-sequence frontier with `errMix = lowerConcreteMixedError`. -/
theorem lowerConcreteMixedLocalExpansionEnvelopeWithError_lowerConcreteMixedError
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (ε : ℝ) :
    lowerConcreteMixedLocalExpansionEnvelope R k ε ↔
      lowerConcreteMixedLocalExpansionEnvelopeWithError R k ε
        (lowerConcreteMixedError R k ε) := by
  rfl

/-- A mixed envelope proved without using the Frobenius-sphere support
immediately supplies the repaired sphere-supported envelope. -/
theorem lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithError_of_withError
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ}
    (errMix : ℝ → ℝ → ℕ → ℝ)
    (hEnvelope :
      lowerConcreteMixedLocalExpansionEnvelopeWithError R k ε errMix) :
    lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithError R k ε errMix := by
  intro a ha slack hslack
  filter_upwards [hEnvelope a ha slack hslack] with d hd
  intro hs X hFav _hSphere
  exact hd hs X hFav

/-- The old fixed-budget mixed envelope also supplies the repaired
sphere-supported envelope with the same fixed budget. -/
theorem lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithError_lowerConcreteMixedError
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ}
    (hEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε) :
    lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithError R k ε
      (lowerConcreteMixedError R k ε) :=
  lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithError_of_withError
    R (lowerConcreteMixedError R k ε)
    ((lowerConcreteMixedLocalExpansionEnvelopeWithError_lowerConcreteMixedError
      R k ε).1 hEnvelope)

/-- Explicit-error mixed supplier.

This is the same absolute-envelope-to-one-sided-lower bridge as the concrete
wrapper above, but it keeps the mixed error sequence visible. -/
theorem lower_mixedLower_concreteChoices_of_localExpansionEnvelopeWithError
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ}
    (errMix : ℝ → ℝ → ℕ → ℝ)
    (hEnvelope :
      lowerConcreteMixedLocalExpansionEnvelopeWithError R k ε errMix) :
    lowerConcreteMixedLowerBound R lowerConcreteCanonicalDirection
      (lowerConcreteM R)
      lowerConcreteTau
      (fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
      errMix k ε := by
  intro a ha slack hslack
  filter_upwards [hEnvelope a ha slack hslack] with d hd
  intro hs X hFav
  have hAbs :
      |columnMixedRemainder
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (lowerConcreteN d) k X (⟨0, hs⟩ : Fin (R.sample d))| ≤
        errMix a slack d :=
    lower_columnMixedRemainder_abs_le_of_localExpansion_zeroLinear
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      (N := lowerConcreteN d)
      (errMix := errMix a slack d)
      (k := k) (X := X) (α₀ := (⟨0, hs⟩ : Fin (R.sample d)))
      (hd hs X hFav)
  exact
    columnMixedRemainder_lower_of_abs_envelope
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      (α₀ := (⟨0, hs⟩ : Fin (R.sample d)))
      (N := lowerConcreteN d)
      (errMix := errMix a slack d)
      (k := k) (X := X) hAbs

/-- Sphere-supported explicit-error mixed supplier. -/
theorem lower_mixedLowerOnSphere_concreteChoices_of_localExpansionEnvelopeOnSphereWithError
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ}
    (errMix : ℝ → ℝ → ℕ → ℝ)
    (hEnvelope :
      lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithError R k ε errMix) :
    lowerConcreteMixedLowerBoundOnSphere R lowerConcreteCanonicalDirection
      (lowerConcreteM R)
      lowerConcreteTau
      (fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
      errMix k ε := by
  intro a ha slack hslack
  filter_upwards [hEnvelope a ha slack hslack] with d hd
  intro hs X hFav hSphere
  have hAbs :
      |columnMixedRemainder
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (lowerConcreteN d) k X (⟨0, hs⟩ : Fin (R.sample d))| ≤
        errMix a slack d :=
    lower_columnMixedRemainder_abs_le_of_localExpansion_zeroLinear
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      (N := lowerConcreteN d)
      (errMix := errMix a slack d)
      (k := k) (X := X) (α₀ := (⟨0, hs⟩ : Fin (R.sample d)))
      (hd hs X hFav hSphere)
  exact
    columnMixedRemainder_lower_of_abs_envelope
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      (α₀ := (⟨0, hs⟩ : Fin (R.sample d)))
      (N := lowerConcreteN d)
      (errMix := errMix a slack d)
      (k := k) (X := X) hAbs

/-- Pointwise mixed-word control on the one-column favourable event. -/
def lowerConcreteMixedWordPointwiseBound
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (ε : ℝ)
    (bound : ℝ → ℝ → ℕ → (Fin k → LocalExpansionLetter) → ℝ) : Prop :=
  ∀ a : ℝ, spikeRoot k ε < a →
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        ∀ hs : 0 < R.sample d,
          ∀ X : SampleMatrix (Fin d) (Fin d) (Fin (R.sample d)),
            X ∈
              sphericalOneColumnFavorableEvent
                (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                (⟨0, hs⟩ : Fin (R.sample d))
                (betaColumnSpikeScale
                  (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                (lowerConcreteDelta a slack d)
                (lowerConcreteDirectionCapSet
                  lowerConcreteCanonicalDirection a slack d)
                (backgroundTypicalSet
                  (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                  (lowerConcreteN d) (lowerConcreteM R a slack d)
                  (lowerConcreteTau a slack d)
                  (lowerConcreteDeletedBackgroundMean R k d) k) →
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                |localWordScaledTraceTerm (p := Fin d) (q := Fin d)
                    (lowerConcreteN d)
                    (columnBackgroundMatrix
                      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                      X (⟨0, hs⟩ : Fin (R.sample d)))
                    0
                    (columnSpikeMatrix
                      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                      X (⟨0, hs⟩ : Fin (R.sample d)))
                    w| ≤
                  bound a slack d w

/-- Sphere-supported pointwise mixed-word control.

This is the word-by-word version compatible with the repaired lower route:
the deterministic two-letter estimate may use the full Frobenius-sphere
identity for `X`, so the sphere hypothesis is kept available at the word
level. -/
def lowerConcreteMixedWordPointwiseBoundOnSphere
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (ε : ℝ)
    (bound : ℝ → ℝ → ℕ → (Fin k → LocalExpansionLetter) → ℝ) : Prop :=
  ∀ a : ℝ, spikeRoot k ε < a →
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        ∀ hs : 0 < R.sample d,
          ∀ X : SampleMatrix (Fin d) (Fin d) (Fin (R.sample d)),
            X ∈
              sphericalOneColumnFavorableEvent
                (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                (⟨0, hs⟩ : Fin (R.sample d))
                (betaColumnSpikeScale
                  (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                (lowerConcreteDelta a slack d)
                (lowerConcreteDirectionCapSet
                  lowerConcreteCanonicalDirection a slack d)
                (backgroundTypicalSet
                  (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                  (lowerConcreteN d) (lowerConcreteM R a slack d)
                  (lowerConcreteTau a slack d)
                  (lowerConcreteDeletedBackgroundMean R k d) k) →
            frobeniusNorm (p := Fin d) (q := Fin d)
                (σ := Fin (R.sample d)) X = 1 →
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                |localWordScaledTraceTerm (p := Fin d) (q := Fin d)
                    (lowerConcreteN d)
                    (columnBackgroundMatrix
                      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                      X (⟨0, hs⟩ : Fin (R.sample d)))
                    0
                    (columnSpikeMatrix
                      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                      X (⟨0, hs⟩ : Fin (R.sample d)))
                    w| ≤
                  bound a slack d w

/-- In the concrete lower decomposition the linear letter is zero.  Therefore
any local-expansion word containing an `L` slot contributes the zero matrix. -/
theorem lower_localWordMatrixProduct_zero_of_exists_L
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    {k : ℕ} (A Q : BipMatrix p q) (w : Fin k → LocalExpansionLetter)
    (hL : ∃ i : Fin k, w i = LocalExpansionLetter.L) :
    localWordMatrixProduct (p := p) (q := q) A 0 Q w = 0 := by
  induction k with
  | zero =>
      rcases hL with ⟨i, _⟩
      exact Fin.elim0 i
  | succ k ih =>
      let x := w 0
      let wt : Fin k → LocalExpansionLetter := Fin.tail w
      by_cases hx : x = LocalExpansionLetter.L
      · simp [localWordMatrixProduct, localLetterMatrix, x, hx]
      · have htail : ∃ i : Fin k, wt i = LocalExpansionLetter.L := by
          rcases hL with ⟨i, hi⟩
          by_cases hi0 : i = 0
          · have : x = LocalExpansionLetter.L := by
              simpa [x, hi0] using hi
            contradiction
          · refine ⟨i.pred hi0, ?_⟩
            have hsucc : (i.pred hi0).succ = i := Fin.succ_pred i hi0
            change w ((i.pred hi0).succ) = LocalExpansionLetter.L
            simpa [hsucc] using hi
        have iht := ih wt htail
        change localLetterMatrix A 0 Q (w 0) *
            localWordMatrixProduct (p := p) (q := q) A 0 Q wt = 0
        rw [iht]
        simp

/-- Scaled trace version of
`lower_localWordMatrixProduct_zero_of_exists_L`. -/
theorem lower_localWordScaledTraceTerm_zero_of_exists_L
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    {N : ℝ} {k : ℕ} (A Q : BipMatrix p q)
    (w : Fin k → LocalExpansionLetter)
    (hL : ∃ i : Fin k, w i = LocalExpansionLetter.L) :
    localWordScaledTraceTerm (p := p) (q := q) N A 0 Q w = 0 := by
  simp [localWordScaledTraceTerm,
    lower_localWordMatrixProduct_zero_of_exists_L
      (p := p) (q := q) A Q w hL]

/-! ### Two-letter word bookkeeping -/

/-- If a local-expansion word contains a letter, the corresponding letter count
is positive. -/
theorem lower_localWordLetterCount_pos_of_exists
    {k : ℕ} {letter : LocalExpansionLetter}
    {w : Fin k → LocalExpansionLetter}
    (h : ∃ i : Fin k, w i = letter) :
    0 < localWordLetterCount letter w := by
  rcases h with ⟨i, hi⟩
  unfold localWordLetterCount
  have hle : (if w i = letter then 1 else 0) ≤
      ∑ x : Fin k, if w x = letter then 1 else 0 := by
    exact
      Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin k)))
        (f := fun x => if w x = letter then 1 else 0)
        (fun x _ => by by_cases hx : w x = letter <;> simp [hx])
        (Finset.mem_univ i)
  have hpos : 0 < (if w i = letter then 1 else 0) := by
    simp [hi]
  exact lt_of_lt_of_le hpos hle

/-- If the count of a letter is zero, that letter occurs nowhere in the word. -/
theorem lower_localWord_no_letter_of_count_zero
    {k : ℕ} {letter : LocalExpansionLetter}
    {w : Fin k → LocalExpansionLetter}
    (h : localWordLetterCount letter w = 0) :
    ∀ i : Fin k, w i ≠ letter := by
  intro i hi
  have hpos : 0 < localWordLetterCount letter w :=
    lower_localWordLetterCount_pos_of_exists
      (letter := letter) (w := w) ⟨i, hi⟩
  omega

/-- If a letter occurs nowhere in a word, its count is zero. -/
theorem lower_localWordLetterCount_zero_of_forall_ne
    {k : ℕ} {letter : LocalExpansionLetter}
    {w : Fin k → LocalExpansionLetter}
    (hNo : ∀ i : Fin k, w i ≠ letter) :
    localWordLetterCount letter w = 0 := by
  induction k with
  | zero =>
      simp [localWordLetterCount]
  | succ k ih =>
      let wt : Fin k → LocalExpansionLetter := Fin.tail w
      have hNo_tail : ∀ i : Fin k, wt i ≠ letter := by
        intro i
        exact hNo i.succ
      have hcount :
          localWordLetterCount letter w =
            (if w 0 = letter then 1 else 0) +
              localWordLetterCount letter wt := by
        simpa [wt, Fin.cons_self_tail] using
          localWordLetterCount_cons (k := k) letter (w 0) wt
      rw [hcount, ih hNo_tail]
      simp [hNo 0]

/-- A mixed word with no linear letter has at least one quadratic/spike letter. -/
theorem lower_localWord_mixed_noL_Q_count_pos
    {k : ℕ} {w : Fin k → LocalExpansionLetter}
    (hmix : localWordIsMixed w)
    (hNoL : ∀ i : Fin k, w i ≠ LocalExpansionLetter.L) :
    0 < localWordLetterCount LocalExpansionLetter.Q w := by
  by_contra hnot
  have hq0 : localWordLetterCount LocalExpansionLetter.Q w = 0 := by
    omega
  have hNoQ : ∀ i : Fin k, w i ≠ LocalExpansionLetter.Q :=
    lower_localWord_no_letter_of_count_zero hq0
  have hpureA : localWordIsPure LocalExpansionLetter.A w := by
    intro i
    cases hwi : w i with
    | A => rfl
    | L => exact False.elim (hNoL i hwi)
    | Q => exact False.elim (hNoQ i hwi)
  exact hmix.1 hpureA

/-- A mixed word with no linear letter is not the pure quadratic/spike word, so
its quadratic/spike count is strictly less than the word length. -/
theorem lower_localWord_mixed_noL_Q_count_lt_length
    {k : ℕ} {w : Fin k → LocalExpansionLetter}
    (hmix : localWordIsMixed w)
    (hNoL : ∀ i : Fin k, w i ≠ LocalExpansionLetter.L) :
    localWordLetterCount LocalExpansionLetter.Q w < k := by
  by_contra hnot
  have hge : k ≤ localWordLetterCount LocalExpansionLetter.Q w := by
    omega
  have htotal := localWordLetterCount_total w
  have hA0 : localWordLetterCount LocalExpansionLetter.A w = 0 := by
    omega
  have hNoA : ∀ i : Fin k, w i ≠ LocalExpansionLetter.A :=
    lower_localWord_no_letter_of_count_zero hA0
  have hpureQ : localWordIsPure LocalExpansionLetter.Q w := by
    intro i
    cases hwi : w i with
    | A => exact False.elim (hNoA i hwi)
    | L => exact False.elim (hNoL i hwi)
    | Q => rfl
  exact hmix.2 hpureQ

/-- Combined spike-count range for the surviving two-letter mixed words. -/
theorem lower_localWord_mixed_noL_Q_count_range
    {k : ℕ} {w : Fin k → LocalExpansionLetter}
    (hmix : localWordIsMixed w)
    (hNoL : ∀ i : Fin k, w i ≠ LocalExpansionLetter.L) :
    1 ≤ localWordLetterCount LocalExpansionLetter.Q w ∧
      localWordLetterCount LocalExpansionLetter.Q w ≤ k - 1 := by
  constructor
  · exact lower_localWord_mixed_noL_Q_count_pos hmix hNoL
  · have hlt :=
      lower_localWord_mixed_noL_Q_count_lt_length
        (k := k) (w := w) hmix hNoL
    omega

/-- A two-letter word with no spike/quadratic letter evaluates to the pure
background power. -/
theorem lower_localWordMatrixProduct_pow_A_of_noL_noQ
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    {k : ℕ} (A Q : BipMatrix p q) (w : Fin k → LocalExpansionLetter)
    (hNoL : ∀ i : Fin k, w i ≠ LocalExpansionLetter.L)
    (hNoQ : ∀ i : Fin k, w i ≠ LocalExpansionLetter.Q) :
    localWordMatrixProduct (p := p) (q := q) A 0 Q w = A ^ k := by
  induction k with
  | zero =>
      simp [localWordMatrixProduct]
  | succ k ih =>
      let wt : Fin k → LocalExpansionLetter := Fin.tail w
      have h0A : w 0 = LocalExpansionLetter.A := by
        cases h : w 0 with
        | A => rfl
        | L => exact False.elim (hNoL 0 h)
        | Q => exact False.elim (hNoQ 0 h)
      have hNoL_tail : ∀ i : Fin k, wt i ≠ LocalExpansionLetter.L := by
        intro i hi
        exact hNoL i.succ hi
      have hNoQ_tail : ∀ i : Fin k, wt i ≠ LocalExpansionLetter.Q := by
        intro i hi
        exact hNoQ i.succ hi
      have iht := ih wt hNoL_tail hNoQ_tail
      change localLetterMatrix A 0 Q (w 0) *
          localWordMatrixProduct (p := p) (q := q) A 0 Q wt = A ^ (k + 1)
      rw [h0A, iht]
      simp [localLetterMatrix, pow_succ']

/-- Operator-norm envelope for any surviving two-letter local word.

When `L = 0`, a no-`L` word is a product of background letters `A` and spike
letters `Q`; its operator norm is bounded by the corresponding product of the
two scalar envelopes.  This is the bookkeeping backbone for the PT mixed-word
bridge. -/
theorem lower_localWordMatrixProduct_opNorm_bound_noL
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    {N M Sbound : ℝ} {k : ℕ} {A Q : BipMatrix p q}
    {w : Fin k → LocalExpansionLetter}
    (hMdivN_nonneg : 0 ≤ M / N)
    (hSbound_nonneg : 0 ≤ Sbound)
    (hA_op : opNorm (p := p) (q := q) A ≤ M / N)
    (hQ_op : opNorm (p := p) (q := q) Q ≤ Sbound)
    (hNoL : ∀ i : Fin k, w i ≠ LocalExpansionLetter.L) :
    opNorm (p := p) (q := q)
        (localWordMatrixProduct (p := p) (q := q) A 0 Q w) ≤
      (M / N) ^ localWordLetterCount LocalExpansionLetter.A w *
        Sbound ^ localWordLetterCount LocalExpansionLetter.Q w := by
  induction k with
  | zero =>
      simpa [localWordMatrixProduct, localWordLetterCount] using
        (lower_opNorm_one_le (p := p) (q := q))
  | succ k ih =>
      let x := w 0
      let wt : Fin k → LocalExpansionLetter := Fin.tail w
      have hNoL_tail : ∀ i : Fin k, wt i ≠ LocalExpansionLetter.L := by
        intro i hi
        exact hNoL i.succ hi
      have iht := ih (w := wt) hNoL_tail
      have hcountA :
          localWordLetterCount LocalExpansionLetter.A w =
            (if w 0 = LocalExpansionLetter.A then 1 else 0) +
              localWordLetterCount LocalExpansionLetter.A wt := by
        simpa [wt, Fin.cons_self_tail] using
          localWordLetterCount_cons
            (k := k) LocalExpansionLetter.A (w 0) wt
      have hcountQ :
          localWordLetterCount LocalExpansionLetter.Q w =
            (if w 0 = LocalExpansionLetter.Q then 1 else 0) +
              localWordLetterCount LocalExpansionLetter.Q wt := by
        simpa [wt, Fin.cons_self_tail] using
          localWordLetterCount_cons
            (k := k) LocalExpansionLetter.Q (w 0) wt
      have htail_nonneg :
          0 ≤ opNorm (p := p) (q := q)
              (localWordMatrixProduct (p := p) (q := q) A 0 Q wt) := by
        unfold opNorm
        positivity
      have htail_bound_nonneg :
          0 ≤ (M / N) ^ localWordLetterCount LocalExpansionLetter.A wt *
              Sbound ^ localWordLetterCount LocalExpansionLetter.Q wt := by
        exact mul_nonneg (pow_nonneg hMdivN_nonneg _)
          (pow_nonneg hSbound_nonneg _)
      cases h0 : w 0 with
      | A =>
          have hmul :=
            lower_opNorm_mul_le
              (p := p) (q := q) A
              (localWordMatrixProduct (p := p) (q := q) A 0 Q wt)
          have hscaled :
              opNorm (p := p) (q := q) A *
                  opNorm (p := p) (q := q)
                    (localWordMatrixProduct (p := p) (q := q) A 0 Q wt) ≤
                (M / N) *
                  ((M / N) ^ localWordLetterCount LocalExpansionLetter.A wt *
                    Sbound ^ localWordLetterCount LocalExpansionLetter.Q wt) := by
            exact mul_le_mul hA_op iht htail_nonneg hMdivN_nonneg
          calc
            opNorm (p := p) (q := q)
                (localWordMatrixProduct (p := p) (q := q) A 0 Q w)
                = opNorm (p := p) (q := q)
                    (A *
                      localWordMatrixProduct (p := p) (q := q) A 0 Q wt) := by
                    have hwt :
                        (fun i : Fin k => w i.succ) = wt := by
                      rfl
                    simp [localWordMatrixProduct, localLetterMatrix, h0, hwt]
            _ ≤ opNorm (p := p) (q := q) A *
                  opNorm (p := p) (q := q)
                    (localWordMatrixProduct (p := p) (q := q) A 0 Q wt) := hmul
            _ ≤ (M / N) *
                  ((M / N) ^ localWordLetterCount LocalExpansionLetter.A wt *
                    Sbound ^ localWordLetterCount LocalExpansionLetter.Q wt) := hscaled
            _ = (M / N) ^ localWordLetterCount LocalExpansionLetter.A w *
                  Sbound ^ localWordLetterCount LocalExpansionLetter.Q w := by
                    rw [hcountA, hcountQ]
                    simp [h0]
                    rw [Nat.add_comm 1
                      (localWordLetterCount LocalExpansionLetter.A wt)]
                    rw [pow_succ']
                    ring
      | L =>
          exact False.elim (hNoL 0 h0)
      | Q =>
          have hmul :=
            lower_opNorm_mul_le
              (p := p) (q := q) Q
              (localWordMatrixProduct (p := p) (q := q) A 0 Q wt)
          have hscaled :
              opNorm (p := p) (q := q) Q *
                  opNorm (p := p) (q := q)
                    (localWordMatrixProduct (p := p) (q := q) A 0 Q wt) ≤
                Sbound *
                  ((M / N) ^ localWordLetterCount LocalExpansionLetter.A wt *
                    Sbound ^ localWordLetterCount LocalExpansionLetter.Q wt) := by
            exact mul_le_mul hQ_op iht htail_nonneg hSbound_nonneg
          calc
            opNorm (p := p) (q := q)
                (localWordMatrixProduct (p := p) (q := q) A 0 Q w)
                = opNorm (p := p) (q := q)
                    (Q *
                      localWordMatrixProduct (p := p) (q := q) A 0 Q wt) := by
                    have hwt :
                        (fun i : Fin k => w i.succ) = wt := by
                      rfl
                    simp [localWordMatrixProduct, localLetterMatrix, h0, hwt]
            _ ≤ opNorm (p := p) (q := q) Q *
                  opNorm (p := p) (q := q)
                    (localWordMatrixProduct (p := p) (q := q) A 0 Q wt) := hmul
            _ ≤ Sbound *
                  ((M / N) ^ localWordLetterCount LocalExpansionLetter.A wt *
                    Sbound ^ localWordLetterCount LocalExpansionLetter.Q wt) := hscaled
            _ = (M / N) ^ localWordLetterCount LocalExpansionLetter.A w *
                  Sbound ^ localWordLetterCount LocalExpansionLetter.Q w := by
                    rw [hcountA, hcountQ]
                    simp [h0]
                    rw [Nat.add_comm 1
                      (localWordLetterCount LocalExpansionLetter.Q wt)]
                    rw [pow_succ']
                    ring

/-- Frobenius envelope for a no-`L` local word containing at least one spike
letter.

The proof uses one spike letter in Frobenius norm and all remaining letters in
operator norm.  It is the analytic half of the many-spike PT trace estimate:
after cyclically exposing one `Q` in the trace, the remaining product is
controlled by this lemma. -/
theorem lower_localWordMatrixProduct_frobeniusNorm_bound_noL_posQ
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    {N M Sbound : ℝ} {k : ℕ} {A Q : BipMatrix p q}
    {w : Fin k → LocalExpansionLetter}
    (hMdivN_nonneg : 0 ≤ M / N)
    (hSbound_nonneg : 0 ≤ Sbound)
    (hA_op : opNorm (p := p) (q := q) A ≤ M / N)
    (hQ_op : opNorm (p := p) (q := q) Q ≤ Sbound)
    (hQ_frob :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) Q ≤ Sbound)
    (hNoL : ∀ i : Fin k, w i ≠ LocalExpansionLetter.L)
    (hQpos : 0 < localWordLetterCount LocalExpansionLetter.Q w) :
    frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
        (localWordMatrixProduct (p := p) (q := q) A 0 Q w) ≤
      (M / N) ^ localWordLetterCount LocalExpansionLetter.A w *
        Sbound ^ localWordLetterCount LocalExpansionLetter.Q w := by
  induction k with
  | zero =>
      simp [localWordLetterCount] at hQpos
  | succ k ih =>
      let x := w 0
      let wt : Fin k → LocalExpansionLetter := Fin.tail w
      have hNoL_tail : ∀ i : Fin k, wt i ≠ LocalExpansionLetter.L := by
        intro i hi
        exact hNoL i.succ hi
      have hcountA :
          localWordLetterCount LocalExpansionLetter.A w =
            (if w 0 = LocalExpansionLetter.A then 1 else 0) +
              localWordLetterCount LocalExpansionLetter.A wt := by
        simpa [wt, Fin.cons_self_tail] using
          localWordLetterCount_cons
            (k := k) LocalExpansionLetter.A (w 0) wt
      have hcountQ :
          localWordLetterCount LocalExpansionLetter.Q w =
            (if w 0 = LocalExpansionLetter.Q then 1 else 0) +
              localWordLetterCount LocalExpansionLetter.Q wt := by
        simpa [wt, Fin.cons_self_tail] using
          localWordLetterCount_cons
            (k := k) LocalExpansionLetter.Q (w 0) wt
      have htail_op_nonneg :
          0 ≤ opNorm (p := p) (q := q)
              (localWordMatrixProduct (p := p) (q := q) A 0 Q wt) := by
        unfold opNorm
        positivity
      have htail_frob_nonneg :
          0 ≤ frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
              (localWordMatrixProduct (p := p) (q := q) A 0 Q wt) := by
        unfold frobeniusNorm
        positivity
      have htail_bound_nonneg :
          0 ≤ (M / N) ^ localWordLetterCount LocalExpansionLetter.A wt *
              Sbound ^ localWordLetterCount LocalExpansionLetter.Q wt := by
        exact mul_nonneg (pow_nonneg hMdivN_nonneg _)
          (pow_nonneg hSbound_nonneg _)
      cases h0 : w 0 with
      | A =>
          have htailQpos :
              0 < localWordLetterCount LocalExpansionLetter.Q wt := by
            rw [hcountQ] at hQpos
            simpa [h0] using hQpos
          have iht := ih (w := wt) hNoL_tail htailQpos
          have hmul :=
            lower_frobeniusNorm_mul_le_opNorm_mul_frobeniusNorm
              (p := p) (q := q) A
              (localWordMatrixProduct (p := p) (q := q) A 0 Q wt)
          have hscaled :
              opNorm (p := p) (q := q) A *
                  frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
                    (localWordMatrixProduct (p := p) (q := q) A 0 Q wt) ≤
                (M / N) *
                  ((M / N) ^ localWordLetterCount LocalExpansionLetter.A wt *
                    Sbound ^ localWordLetterCount LocalExpansionLetter.Q wt) := by
            exact mul_le_mul hA_op iht htail_frob_nonneg hMdivN_nonneg
          calc
            frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
                (localWordMatrixProduct (p := p) (q := q) A 0 Q w)
                = frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
                    (A *
                      localWordMatrixProduct (p := p) (q := q) A 0 Q wt) := by
                    have hwt :
                        (fun i : Fin k => w i.succ) = wt := by
                      rfl
                    simp [localWordMatrixProduct, localLetterMatrix, h0, hwt]
            _ ≤ opNorm (p := p) (q := q) A *
                  frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
                    (localWordMatrixProduct (p := p) (q := q) A 0 Q wt) := hmul
            _ ≤ (M / N) *
                  ((M / N) ^ localWordLetterCount LocalExpansionLetter.A wt *
                    Sbound ^ localWordLetterCount LocalExpansionLetter.Q wt) := hscaled
            _ = (M / N) ^ localWordLetterCount LocalExpansionLetter.A w *
                  Sbound ^ localWordLetterCount LocalExpansionLetter.Q w := by
                    rw [hcountA, hcountQ]
                    simp [h0]
                    rw [Nat.add_comm 1
                      (localWordLetterCount LocalExpansionLetter.A wt)]
                    rw [pow_succ']
                    ring
      | L =>
          exact False.elim (hNoL 0 h0)
      | Q =>
          have htail_op :
              opNorm (p := p) (q := q)
                  (localWordMatrixProduct (p := p) (q := q) A 0 Q wt) ≤
                (M / N) ^ localWordLetterCount LocalExpansionLetter.A wt *
                  Sbound ^ localWordLetterCount LocalExpansionLetter.Q wt :=
            lower_localWordMatrixProduct_opNorm_bound_noL
              (p := p) (q := q) (N := N) (M := M)
              (Sbound := Sbound) (A := A) (Q := Q) (w := wt)
              hMdivN_nonneg hSbound_nonneg hA_op hQ_op hNoL_tail
          have hmul :=
            lower_frobeniusNorm_mul_le_frobeniusNorm_mul_opNorm
              (p := p) (q := q) Q
              (localWordMatrixProduct (p := p) (q := q) A 0 Q wt)
          have hscaled :
              frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) Q *
                  opNorm (p := p) (q := q)
                    (localWordMatrixProduct (p := p) (q := q) A 0 Q wt) ≤
                Sbound *
                  ((M / N) ^ localWordLetterCount LocalExpansionLetter.A wt *
                    Sbound ^ localWordLetterCount LocalExpansionLetter.Q wt) := by
            exact mul_le_mul hQ_frob htail_op htail_op_nonneg hSbound_nonneg
          calc
            frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
                (localWordMatrixProduct (p := p) (q := q) A 0 Q w)
                = frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
                    (Q *
                      localWordMatrixProduct (p := p) (q := q) A 0 Q wt) := by
                    have hwt :
                        (fun i : Fin k => w i.succ) = wt := by
                      rfl
                    simp [localWordMatrixProduct, localLetterMatrix, h0, hwt]
            _ ≤ frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) Q *
                  opNorm (p := p) (q := q)
                    (localWordMatrixProduct (p := p) (q := q) A 0 Q wt) := hmul
            _ ≤ Sbound *
                  ((M / N) ^ localWordLetterCount LocalExpansionLetter.A wt *
                    Sbound ^ localWordLetterCount LocalExpansionLetter.Q wt) := hscaled
            _ = (M / N) ^ localWordLetterCount LocalExpansionLetter.A w *
                  Sbound ^ localWordLetterCount LocalExpansionLetter.Q w := by
                    rw [hcountA, hcountQ]
                    simp [h0]
                    rw [Nat.add_comm 1
                      (localWordLetterCount LocalExpansionLetter.Q wt)]
                    rw [pow_succ']
                    ring

/-- Many-spike PT trace estimate for a word already cyclically rotated to start
with a spike letter.

The remaining arbitrary-word problem is now purely combinatorial: rotate any
no-`L` mixed word with at least two `Q` letters into this head-`Q` form while
preserving the trace and the letter counts. -/
theorem lower_localWordScaledTraceTerm_manyQ_headQ_noL_bound
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    {N M Sbound : ℝ} {m : ℕ} {A Q : BipMatrix p q}
    {w : Fin (m + 1) → LocalExpansionLetter}
    (hN : 0 ≤ N)
    (hMdivN_nonneg : 0 ≤ M / N)
    (hSbound_nonneg : 0 ≤ Sbound)
    (hA_op : opNorm (p := p) (q := q) A ≤ M / N)
    (hQ_op : opNorm (p := p) (q := q) Q ≤ Sbound)
    (hQ_frob :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) Q ≤ Sbound)
    (hNoL : ∀ i : Fin (m + 1), w i ≠ LocalExpansionLetter.L)
    (hHeadQ : w 0 = LocalExpansionLetter.Q)
    (hQtwo : 2 ≤ localWordLetterCount LocalExpansionLetter.Q w) :
    |localWordScaledTraceTerm (p := p) (q := q) N A 0 Q w| ≤
      N ^ m *
        ((M / N) ^ localWordLetterCount LocalExpansionLetter.A w *
          Sbound ^ localWordLetterCount LocalExpansionLetter.Q w) := by
  let wt : Fin m → LocalExpansionLetter := Fin.tail w
  have hNoL_tail : ∀ i : Fin m, wt i ≠ LocalExpansionLetter.L := by
    intro i hi
    exact hNoL i.succ hi
  have hcountA :
      localWordLetterCount LocalExpansionLetter.A w =
        localWordLetterCount LocalExpansionLetter.A wt := by
    have hcount :=
      localWordLetterCount_cons
        (k := m) LocalExpansionLetter.A (w 0) wt
    have hcount' :
        localWordLetterCount LocalExpansionLetter.A w =
          (if w 0 = LocalExpansionLetter.A then 1 else 0) +
            localWordLetterCount LocalExpansionLetter.A wt := by
      simpa [wt, Fin.cons_self_tail] using hcount
    rw [hcount']
    simp [hHeadQ]
  have hcountQ :
      localWordLetterCount LocalExpansionLetter.Q w =
        1 + localWordLetterCount LocalExpansionLetter.Q wt := by
    have hcount :=
      localWordLetterCount_cons
        (k := m) LocalExpansionLetter.Q (w 0) wt
    have hcount' :
        localWordLetterCount LocalExpansionLetter.Q w =
          (if w 0 = LocalExpansionLetter.Q then 1 else 0) +
            localWordLetterCount LocalExpansionLetter.Q wt := by
      simpa [wt, Fin.cons_self_tail] using hcount
    rw [hcount']
    simp [hHeadQ]
  have htailQpos :
      0 < localWordLetterCount LocalExpansionLetter.Q wt := by
    rw [hcountQ] at hQtwo
    omega
  have htail_frob :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
          (localWordMatrixProduct (p := p) (q := q) A 0 Q wt) ≤
        (M / N) ^ localWordLetterCount LocalExpansionLetter.A wt *
          Sbound ^ localWordLetterCount LocalExpansionLetter.Q wt :=
    lower_localWordMatrixProduct_frobeniusNorm_bound_noL_posQ
      (p := p) (q := q) (N := N) (M := M) (Sbound := Sbound)
      (A := A) (Q := Q) (w := wt)
      hMdivN_nonneg hSbound_nonneg hA_op hQ_op hQ_frob hNoL_tail htailQpos
  have htrace :=
    matrix_abs_re_trace_mul_le_frobenius_norm_mul
      (n := BipIndex p q) Q
      (localWordMatrixProduct (p := p) (q := q) A 0 Q wt)
  have htail_frob_nonneg :
      0 ≤ frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
          (localWordMatrixProduct (p := p) (q := q) A 0 Q wt) := by
    unfold frobeniusNorm
    positivity
  have htail_bound_nonneg :
      0 ≤ (M / N) ^ localWordLetterCount LocalExpansionLetter.A wt *
          Sbound ^ localWordLetterCount LocalExpansionLetter.Q wt := by
    exact mul_nonneg (pow_nonneg hMdivN_nonneg _)
      (pow_nonneg hSbound_nonneg _)
  have htrace_bound :
      |(Matrix.trace
          (Q *
            localWordMatrixProduct (p := p) (q := q) A 0 Q wt)).re| ≤
        Sbound *
          ((M / N) ^ localWordLetterCount LocalExpansionLetter.A wt *
            Sbound ^ localWordLetterCount LocalExpansionLetter.Q wt) := by
    calc
      |(Matrix.trace
          (Q *
            localWordMatrixProduct (p := p) (q := q) A 0 Q wt)).re| ≤
          frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) Q *
            frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
              (localWordMatrixProduct (p := p) (q := q) A 0 Q wt) := by
            simpa [frobeniusNorm] using htrace
      _ ≤ Sbound *
            ((M / N) ^ localWordLetterCount LocalExpansionLetter.A wt *
              Sbound ^ localWordLetterCount LocalExpansionLetter.Q wt) := by
            exact
              mul_le_mul hQ_frob htail_frob htail_frob_nonneg
                hSbound_nonneg
  have hNpow_nonneg : 0 ≤ N ^ m := pow_nonneg hN _
  unfold localWordScaledTraceTerm
  have hprod :
      localWordMatrixProduct (p := p) (q := q) A 0 Q w =
        Q * localWordMatrixProduct (p := p) (q := q) A 0 Q wt := by
    have hwt : (fun i : Fin m => w i.succ) = wt := by
      rfl
    simp [localWordMatrixProduct, localLetterMatrix, hHeadQ, hwt]
  rw [hprod]
  have hmexp : m + 1 - 1 = m := by omega
  rw [hmexp]
  rw [abs_mul, abs_of_nonneg hNpow_nonneg]
  calc
    N ^ m *
        |(Matrix.trace
          (Q *
            localWordMatrixProduct (p := p) (q := q) A 0 Q wt)).re| ≤
      N ^ m *
        (Sbound *
          ((M / N) ^ localWordLetterCount LocalExpansionLetter.A wt *
            Sbound ^ localWordLetterCount LocalExpansionLetter.Q wt)) := by
        exact mul_le_mul_of_nonneg_left htrace_bound hNpow_nonneg
    _ = N ^ m *
        ((M / N) ^ localWordLetterCount LocalExpansionLetter.A w *
          Sbound ^ localWordLetterCount LocalExpansionLetter.Q w) := by
        rw [hcountA, hcountQ]
        rw [Nat.add_comm 1 (localWordLetterCount LocalExpansionLetter.Q wt)]
        rw [pow_succ']
        ring

/-- Precomposing a local word with a `Fin.cast` does not change its letter
count. -/
theorem lower_localWordLetterCount_cast
    {k k' : ℕ} (h : k = k')
    (letter : LocalExpansionLetter)
    (w : Fin k' → LocalExpansionLetter) :
    localWordLetterCount letter (w ∘ Fin.cast h) =
      localWordLetterCount letter w := by
  subst h
  rfl

/-- Precomposing a local word with a `Fin.cast` does not change its ordered
matrix product. -/
theorem lower_localWordMatrixProduct_cast
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    {k k' : ℕ} (A L Q : BipMatrix p q)
    (h : k = k')
    (w : Fin k' → LocalExpansionLetter) :
    localWordMatrixProduct (p := p) (q := q) A L Q (w ∘ Fin.cast h) =
      localWordMatrixProduct (p := p) (q := q) A L Q w := by
  subst h
  rfl

/-- Precomposing a local word with a `Fin.cast` does not change its scaled
trace term. -/
theorem lower_localWordScaledTraceTerm_cast
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    {N : ℝ} {k k' : ℕ} (A L Q : BipMatrix p q)
    (h : k = k')
    (w : Fin k' → LocalExpansionLetter) :
    localWordScaledTraceTerm (p := p) (q := q) N A L Q (w ∘ Fin.cast h) =
      localWordScaledTraceTerm (p := p) (q := q) N A L Q w := by
  subst h
  rfl

/-- Letter counts add under concatenation of local words. -/
theorem lower_localWordLetterCount_append
    {m n : ℕ} (letter : LocalExpansionLetter)
    (u : Fin m → LocalExpansionLetter)
    (v : Fin n → LocalExpansionLetter) :
    localWordLetterCount letter (Fin.append u v) =
      localWordLetterCount letter u + localWordLetterCount letter v := by
  induction m with
  | zero =>
      have hu0 : u = Fin.elim0 := by
        funext i
        exact Fin.elim0 i
      have happ :
          Fin.append u v = v ∘ Fin.cast (Nat.zero_add n) := by
        rw [hu0]
        simp
      rw [happ, lower_localWordLetterCount_cast (h := Nat.zero_add n)]
      simp [localWordLetterCount]
  | succ m ih =>
      let a : LocalExpansionLetter := u 0
      let ut : Fin m → LocalExpansionLetter := Fin.tail u
      have hu : Fin.cons a ut = u := by
        simp [a, ut]
      calc
        localWordLetterCount letter (Fin.append u v)
            = localWordLetterCount letter (Fin.append (Fin.cons a ut) v) := by
                rw [← hu]
        _ =
            localWordLetterCount letter
              ((Fin.cons a (Fin.append ut v)) ∘
                Fin.cast (Nat.add_right_comm m 1 n)) := by
                  rw [Fin.append_cons]
        _ =
            localWordLetterCount letter
              (Fin.cons a (Fin.append ut v)) := by
                  simpa using
                    lower_localWordLetterCount_cast
                      (h := Nat.add_right_comm m 1 n)
                      (letter := letter)
                      (w := Fin.cons a (Fin.append ut v))
        _ =
            (if a = letter then 1 else 0) +
              localWordLetterCount letter (Fin.append ut v) := by
                  simpa using
                    localWordLetterCount_cons
                      (k := m + n) letter a (Fin.append ut v)
        _ =
            (if a = letter then 1 else 0) +
              (localWordLetterCount letter ut +
                localWordLetterCount letter v) := by
                  rw [ih]
        _ =
            localWordLetterCount letter (Fin.cons a ut) +
              localWordLetterCount letter v := by
                  rw [localWordLetterCount_cons]
                  omega
        _ = localWordLetterCount letter u + localWordLetterCount letter v := by
              rw [← hu]

/-- Ordered local-word matrix products factor across concatenation. -/
theorem lower_localWordMatrixProduct_append
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    (A L Q : BipMatrix p q)
    {m n : ℕ}
    (u : Fin m → LocalExpansionLetter)
    (v : Fin n → LocalExpansionLetter) :
    localWordMatrixProduct (p := p) (q := q) A L Q (Fin.append u v) =
      localWordMatrixProduct (p := p) (q := q) A L Q u *
        localWordMatrixProduct (p := p) (q := q) A L Q v := by
  induction m with
  | zero =>
      have hu0 : u = Fin.elim0 := by
        funext i
        exact Fin.elim0 i
      have happ :
          Fin.append u v = v ∘ Fin.cast (Nat.zero_add n) := by
        rw [hu0]
        simp
      rw [happ, lower_localWordMatrixProduct_cast (p := p) (q := q)
        A L Q (h := Nat.zero_add n)]
      simp [localWordMatrixProduct]
  | succ m ih =>
      let a : LocalExpansionLetter := u 0
      let ut : Fin m → LocalExpansionLetter := Fin.tail u
      have hu : Fin.cons a ut = u := by
        simp [a, ut]
      calc
        localWordMatrixProduct (p := p) (q := q) A L Q (Fin.append u v)
            =
              localWordMatrixProduct (p := p) (q := q) A L Q
                (Fin.append (Fin.cons a ut) v) := by
                  rw [← hu]
        _ =
            localWordMatrixProduct (p := p) (q := q) A L Q
              ((Fin.cons a (Fin.append ut v)) ∘
                Fin.cast (Nat.add_right_comm m 1 n)) := by
                  rw [Fin.append_cons]
        _ =
            localWordMatrixProduct (p := p) (q := q) A L Q
              (Fin.cons a (Fin.append ut v)) := by
                  simpa using
                    lower_localWordMatrixProduct_cast
                      (p := p) (q := q) A L Q
                      (h := Nat.add_right_comm m 1 n)
                      (w := Fin.cons a (Fin.append ut v))
        _ =
            localLetterMatrix A L Q a *
              localWordMatrixProduct (p := p) (q := q) A L Q
                (Fin.append ut v) := by
                  simp [localWordMatrixProduct]
        _ =
            localLetterMatrix A L Q a *
              (localWordMatrixProduct (p := p) (q := q) A L Q ut *
                localWordMatrixProduct (p := p) (q := q) A L Q v) := by
                  rw [ih]
        _ =
            (localLetterMatrix A L Q a *
              localWordMatrixProduct (p := p) (q := q) A L Q ut) *
                localWordMatrixProduct (p := p) (q := q) A L Q v := by
                  rw [Matrix.mul_assoc]
        _ =
            localWordMatrixProduct (p := p) (q := q) A L Q u *
              localWordMatrixProduct (p := p) (q := q) A L Q v := by
                  rw [← hu]
                  simp [localWordMatrixProduct]

/-- Cyclic rotation of a concatenated local word preserves the scaled trace
term.  This is the matrix-trace half of the finite combinatorial normalization
lemma. -/
theorem lower_localWordScaledTraceTerm_append_rotate
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    {N : ℝ} (A L Q : BipMatrix p q)
    {m n : ℕ}
    (u : Fin m → LocalExpansionLetter)
    (v : Fin n → LocalExpansionLetter) :
    localWordScaledTraceTerm (p := p) (q := q) N A L Q (Fin.append u v) =
      localWordScaledTraceTerm (p := p) (q := q) N A L Q
        ((Fin.append v u) ∘ Fin.cast (Nat.add_comm m n)) := by
  rw [lower_localWordScaledTraceTerm_cast
    (p := p) (q := q) (N := N) A L Q
    (h := Nat.add_comm m n) (w := Fin.append v u)]
  unfold localWordScaledTraceTerm
  rw [lower_localWordMatrixProduct_append, lower_localWordMatrixProduct_append]
  rw [Matrix.trace_mul_comm]
  simp [Nat.add_comm]

/-- Exact finite split form of a no-`L`, at-least-two-`Q` word that is enough
to build the cyclic head-`Q` normalization.

This is the append/split formulation of the remaining finite-word debt: split
the word into an arbitrary prefix `u` and a suffix beginning with `Q`.  The
full cyclic-normalization theorem then follows from count additivity and trace
cyclicity. -/
def lowerLocalTwoLetterMixedWordCyclicPrefixHeadQSplit
    {m : ℕ} (w : Fin (m + 1) → LocalExpansionLetter) : Prop :=
  ∃ r n : ℕ, ∃ hlen : r + (n + 1) = m + 1,
    ∃ u : Fin r → LocalExpansionLetter,
      ∃ v : Fin n → LocalExpansionLetter,
        w =
          (Fin.append u (Fin.cons LocalExpansionLetter.Q v)) ∘
            Fin.cast hlen.symm

/-- Narrow head-`Q` append split used by the many-`Q` mixed route.

This is intentionally smaller than cyclic normalization: the word is already
assumed to begin with `Q`, and the remaining obligation is only that its tail
splits as a prefix followed by another `Q`. -/
def lowerLocalTwoLetterMixedWordAppendHeadQSplit
    {m : ℕ} (w : Fin (m + 1) → LocalExpansionLetter) : Prop :=
  w 0 = LocalExpansionLetter.Q ∧
    ∃ r n : ℕ, ∃ hlen : r + (n + 1) = m,
      ∃ C : Fin r → LocalExpansionLetter,
        ∃ D : Fin n → LocalExpansionLetter,
          Fin.tail w =
            (Fin.append C (Fin.cons LocalExpansionLetter.Q D)) ∘
              Fin.cast hlen.symm

/-- Split a finite word at a specified position.  This is the generic `Fin`
bookkeeping lemma behind the local `Q`-occurrence split. -/
theorem lower_localWord_exists_cyclicPrefixSplitAt
    {α : Type*} {m : ℕ} (w : Fin (m + 1) → α) (i : Fin (m + 1)) :
    ∃ r n : ℕ, ∃ hlen : r + (n + 1) = m + 1,
      ∃ u : Fin r → α, ∃ v : Fin n → α,
        w = (Fin.append u (Fin.cons (w i) v)) ∘ Fin.cast hlen.symm := by
  let r : ℕ := i.val
  let n : ℕ := m - i.val
  have hlen : r + (n + 1) = m + 1 := by
    dsimp [r, n]
    omega
  let u : Fin r → α := fun j => w ⟨j.val, by dsimp [r] at j; omega⟩
  let v : Fin n → α :=
    fun j => w ⟨i.val + 1 + j.val, by dsimp [n] at j; omega⟩
  refine ⟨r, n, hlen, u, v, ?_⟩
  have hmain : w ∘ Fin.cast hlen =
      Fin.append u (Fin.cons (w i) v) := by
    funext y
    refine
      Fin.addCases
        (motive := fun y =>
          (w ∘ Fin.cast hlen) y = Fin.append u (Fin.cons (w i) v) y)
        ?left ?right y
    · intro j
      rw [Fin.append, Fin.addCases_left]
      change w (Fin.cast hlen (Fin.castAdd (n + 1) j)) = u j
      have hidx :
          Fin.cast hlen (Fin.castAdd (n + 1) j) =
            ⟨j.val, by dsimp [r] at j; omega⟩ := by
        apply Fin.ext
        simp [Fin.val_cast, Fin.val_castAdd]
      simp [u, hidx]
    · intro j
      rw [Fin.append, Fin.addCases_right]
      refine Fin.cases ?zero ?succ j
      · have hidx :
            Fin.cast hlen (Fin.natAdd r (0 : Fin (n + 1))) = i := by
          apply Fin.ext
          simp [r, Fin.val_cast, Fin.val_natAdd]
        simp [hidx]
      · intro k
        have hidx :
            Fin.cast hlen (Fin.natAdd r k.succ) =
              ⟨i.val + 1 + k.val, by dsimp [n] at k; omega⟩ := by
          apply Fin.ext
          rw [Fin.val_cast, Fin.val_natAdd, Fin.val_succ]
          dsimp [r]
          omega
        simp [v, hidx]
  funext x
  have hx := congrFun hmain (Fin.cast hlen.symm x)
  simpa using hx

/-- If a letter count is positive, that letter occurs somewhere in the word. -/
theorem lower_localWord_exists_of_letterCount_pos
    {k : ℕ} {letter : LocalExpansionLetter}
    {w : Fin k → LocalExpansionLetter}
    (hpos : 0 < localWordLetterCount letter w) :
    ∃ i : Fin k, w i = letter := by
  by_contra hnot
  have hNo : ∀ i : Fin k, w i ≠ letter := by
    intro i hi
    exact hnot ⟨i, hi⟩
  have hzero : localWordLetterCount letter w = 0 :=
    lower_localWordLetterCount_zero_of_forall_ne hNo
  omega

/-- Build the narrow head-`Q` split from a `Q` occurrence in the tail. -/
theorem lowerLocalTwoLetterMixedWordAppendHeadQSplit_of_headQ_tailOccurrence
    {m : ℕ} {w : Fin (m + 1) → LocalExpansionLetter}
    (hHead : w 0 = LocalExpansionLetter.Q)
    (hTail : ∃ i : Fin m, Fin.tail w i = LocalExpansionLetter.Q) :
    lowerLocalTwoLetterMixedWordAppendHeadQSplit w := by
  refine ⟨hHead, ?_⟩
  cases m with
  | zero =>
      rcases hTail with ⟨i, _hi⟩
      exact Fin.elim0 i
  | succ m =>
      rcases hTail with ⟨i, hi⟩
      rcases lower_localWord_exists_cyclicPrefixSplitAt (Fin.tail w) i with
        ⟨r, n, hlen, C, D, htail⟩
      refine ⟨r, n, hlen, C, D, ?_⟩
      simpa [hi] using htail

/-- A head-`Q` word with at least one further `Q` admits the narrow
append/head-`Q` split. -/
theorem lowerLocalTwoLetterMixedWordAppendHeadQSplit_of_headQ_twoQ
    {m : ℕ} {w : Fin (m + 1) → LocalExpansionLetter}
    (hHead : w 0 = LocalExpansionLetter.Q)
    (hQtwo : 2 ≤ localWordLetterCount LocalExpansionLetter.Q w) :
    lowerLocalTwoLetterMixedWordAppendHeadQSplit w := by
  have htail_count :
      localWordLetterCount LocalExpansionLetter.Q w =
        1 + localWordLetterCount LocalExpansionLetter.Q (Fin.tail w) := by
    have hcount :=
      localWordLetterCount_cons
        (k := m) LocalExpansionLetter.Q (w 0) (Fin.tail w)
    have hconsw : Fin.cons (w 0) (Fin.tail w) = w :=
      Fin.cons_self_tail w
    calc
      localWordLetterCount LocalExpansionLetter.Q w
          =
            localWordLetterCount LocalExpansionLetter.Q
              (Fin.cons (w 0) (Fin.tail w)) := by
                rw [hconsw]
      _ =
          (if w 0 = LocalExpansionLetter.Q then 1 else 0) +
            localWordLetterCount LocalExpansionLetter.Q (Fin.tail w) := hcount
      _ = 1 + localWordLetterCount LocalExpansionLetter.Q (Fin.tail w) := by
            simp [hHead]
  have hTailPos : 0 < localWordLetterCount LocalExpansionLetter.Q (Fin.tail w) := by
    rw [htail_count] at hQtwo
    omega
  exact
    lowerLocalTwoLetterMixedWordAppendHeadQSplit_of_headQ_tailOccurrence
      hHead
      (lower_localWord_exists_of_letterCount_pos
        (letter := LocalExpansionLetter.Q) (w := Fin.tail w) hTailPos)

/-- Exact remaining finite index-selection obligation for the append/head-`Q`
split: once a concrete `Q` occurrence is supplied, split the word immediately
before that occurrence. -/
def lowerLocalTwoLetterMixedWordCyclicPrefixHeadQSplitFromOccurrence : Prop :=
  ∀ {m : ℕ} {w : Fin (m + 1) → LocalExpansionLetter},
    (∃ i : Fin (m + 1), w i = LocalExpansionLetter.Q) →
      lowerLocalTwoLetterMixedWordCyclicPrefixHeadQSplit w

/-- Close the occurrence-based cyclic-prefix split frontier. -/
theorem lowerLocalTwoLetterMixedWordCyclicPrefixHeadQSplitFromOccurrence_closed :
    lowerLocalTwoLetterMixedWordCyclicPrefixHeadQSplitFromOccurrence := by
  intro m w hOcc
  rcases hOcc with ⟨i, hi⟩
  rcases lower_localWord_exists_cyclicPrefixSplitAt w i with
    ⟨r, n, hlen, u, v, hw⟩
  refine ⟨r, n, hlen, u, v, ?_⟩
  simpa [hi] using hw

/-- The two-`Q` count reduces the split frontier to the exact occurrence-based
finite split obligation. -/
theorem lowerLocalTwoLetterMixedWordCyclicPrefixHeadQSplit_of_twoQ_of_occurrenceSplit
    (hOccurrence :
      lowerLocalTwoLetterMixedWordCyclicPrefixHeadQSplitFromOccurrence)
    {m : ℕ} {w : Fin (m + 1) → LocalExpansionLetter}
    (hQtwo : 2 ≤ localWordLetterCount LocalExpansionLetter.Q w) :
    lowerLocalTwoLetterMixedWordCyclicPrefixHeadQSplit w :=
  hOccurrence
    (lower_localWord_exists_of_letterCount_pos
      (letter := LocalExpansionLetter.Q) (w := w) (by omega))

/-- A word with at least two `Q` letters has the cyclic-prefix split. -/
theorem lowerLocalTwoLetterMixedWordCyclicPrefixHeadQSplit_of_twoQ
    {m : ℕ} {w : Fin (m + 1) → LocalExpansionLetter}
    (hQtwo : 2 ≤ localWordLetterCount LocalExpansionLetter.Q w) :
    lowerLocalTwoLetterMixedWordCyclicPrefixHeadQSplit w :=
  lowerLocalTwoLetterMixedWordCyclicPrefixHeadQSplit_of_twoQ_of_occurrenceSplit
    lowerLocalTwoLetterMixedWordCyclicPrefixHeadQSplitFromOccurrence_closed hQtwo

/-- The exact finite combinatorial normal form still needed to turn the
head-`Q` many-spike trace estimate into an arbitrary-word estimate.

It says that every no-`L` word with at least two `Q` letters can be cyclically
rotated to start with `Q`, preserving all two-letter counts and the scaled
trace term.  No analytic estimate is hidden in this statement: it is purely
the trace-cyclicity/word-rotation bridge. -/
def lowerLocalTwoLetterMixedWordCyclicNormalization
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    {N : ℝ} {m : ℕ} (A Q : BipMatrix p q)
    (w : Fin (m + 1) → LocalExpansionLetter) : Prop :=
      (∀ i : Fin (m + 1), w i ≠ LocalExpansionLetter.L) →
      2 ≤ localWordLetterCount LocalExpansionLetter.Q w →
      ∃ wRot : Fin (m + 1) → LocalExpansionLetter,
        wRot 0 = LocalExpansionLetter.Q ∧
        (∀ i : Fin (m + 1), wRot i ≠ LocalExpansionLetter.L) ∧
        localWordLetterCount LocalExpansionLetter.A wRot =
          localWordLetterCount LocalExpansionLetter.A w ∧
        localWordLetterCount LocalExpansionLetter.Q wRot =
          localWordLetterCount LocalExpansionLetter.Q w ∧
        localWordScaledTraceTerm (p := p) (q := q) N A 0 Q w =
          localWordScaledTraceTerm (p := p) (q := q) N A 0 Q wRot

/-- The append/split finite-word frontier is already enough to build the full
cyclic head-`Q` normalization.

This removes all analytic content from the remaining many-`Q` arbitrary-word
obligation: once the word is split as a prefix followed by a suffix beginning
with `Q`, the rotated word is obtained by concatenation in the opposite order,
and the desired properties follow from count additivity and trace cyclicity. -/
theorem lowerLocalTwoLetterMixedWordCyclicNormalization_of_appendHeadQSplit
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    {N : ℝ} {m : ℕ} {A Q : BipMatrix p q}
    {w : Fin (m + 1) → LocalExpansionLetter}
    (hSplit : lowerLocalTwoLetterMixedWordCyclicPrefixHeadQSplit w) :
    lowerLocalTwoLetterMixedWordCyclicNormalization (N := N) A Q w := by
  intro hNoL _hQtwo
  rcases hSplit with ⟨r, n, hlen, u, v, hw⟩
  have hrot : (n + 1) + r = m + 1 := by omega
  let wRot : Fin (m + 1) → LocalExpansionLetter :=
    (Fin.append (Fin.cons LocalExpansionLetter.Q v) u) ∘ Fin.cast hrot.symm
  refine ⟨wRot, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · have hcountLw : localWordLetterCount LocalExpansionLetter.L w = 0 :=
      lower_localWordLetterCount_zero_of_forall_ne hNoL
    have hcountLRot :
        localWordLetterCount LocalExpansionLetter.L wRot =
          localWordLetterCount LocalExpansionLetter.L w := by
      calc
        localWordLetterCount LocalExpansionLetter.L wRot
            =
              localWordLetterCount LocalExpansionLetter.L
                (Fin.append (Fin.cons LocalExpansionLetter.Q v) u) := by
                  simp [wRot, lower_localWordLetterCount_cast]
        _ =
            localWordLetterCount LocalExpansionLetter.L
              (Fin.append u (Fin.cons LocalExpansionLetter.Q v)) := by
                rw [lower_localWordLetterCount_append,
                  lower_localWordLetterCount_append]
                simp [localWordLetterCount_cons]
                omega
        _ =
            localWordLetterCount LocalExpansionLetter.L
              ((Fin.append u (Fin.cons LocalExpansionLetter.Q v)) ∘
                Fin.cast hlen.symm) := by
                  symm
                  simpa using
                    lower_localWordLetterCount_cast
                      (h := hlen.symm)
                      (letter := LocalExpansionLetter.L)
                      (w := Fin.append u (Fin.cons LocalExpansionLetter.Q v))
        _ = localWordLetterCount LocalExpansionLetter.L w := by
              rw [hw]
    have hcountLRot0 : localWordLetterCount LocalExpansionLetter.L wRot = 0 := by
      rw [hcountLRot, hcountLw]
    exact lower_localWord_no_letter_of_count_zero hcountLRot0
  · calc
      localWordLetterCount LocalExpansionLetter.A wRot
          =
            localWordLetterCount LocalExpansionLetter.A
              (Fin.append (Fin.cons LocalExpansionLetter.Q v) u) := by
                simp [wRot, lower_localWordLetterCount_cast]
      _ =
          localWordLetterCount LocalExpansionLetter.A
            (Fin.append u (Fin.cons LocalExpansionLetter.Q v)) := by
              rw [lower_localWordLetterCount_append,
                lower_localWordLetterCount_append]
              simp [localWordLetterCount_cons]
              omega
      _ =
          localWordLetterCount LocalExpansionLetter.A
            ((Fin.append u (Fin.cons LocalExpansionLetter.Q v)) ∘
              Fin.cast hlen.symm) := by
                symm
                simpa using
                  lower_localWordLetterCount_cast
                    (h := hlen.symm)
                    (letter := LocalExpansionLetter.A)
                    (w := Fin.append u (Fin.cons LocalExpansionLetter.Q v))
      _ = localWordLetterCount LocalExpansionLetter.A w := by
            rw [hw]
  · calc
      localWordLetterCount LocalExpansionLetter.Q wRot
          =
            localWordLetterCount LocalExpansionLetter.Q
              (Fin.append (Fin.cons LocalExpansionLetter.Q v) u) := by
                simp [wRot, lower_localWordLetterCount_cast]
      _ =
          localWordLetterCount LocalExpansionLetter.Q
            (Fin.append u (Fin.cons LocalExpansionLetter.Q v)) := by
              rw [lower_localWordLetterCount_append,
                lower_localWordLetterCount_append]
              simp [localWordLetterCount_cons]
              omega
      _ =
          localWordLetterCount LocalExpansionLetter.Q
            ((Fin.append u (Fin.cons LocalExpansionLetter.Q v)) ∘
              Fin.cast hlen.symm) := by
                symm
                simpa using
                  lower_localWordLetterCount_cast
                    (h := hlen.symm)
                    (letter := LocalExpansionLetter.Q)
                    (w := Fin.append u (Fin.cons LocalExpansionLetter.Q v))
      _ = localWordLetterCount LocalExpansionLetter.Q w := by
            rw [hw]
  · calc
      localWordScaledTraceTerm (p := p) (q := q) N A 0 Q w
          =
            localWordScaledTraceTerm (p := p) (q := q) N A 0 Q
              ((Fin.append u (Fin.cons LocalExpansionLetter.Q v)) ∘
                Fin.cast hlen.symm) := by
                  rw [hw]
      _ =
          localWordScaledTraceTerm (p := p) (q := q) N A 0 Q
            (Fin.append u (Fin.cons LocalExpansionLetter.Q v)) := by
              simpa using
                lower_localWordScaledTraceTerm_cast
                  (p := p) (q := q) (N := N) A 0 Q
                  (h := hlen.symm)
                  (w := Fin.append u (Fin.cons LocalExpansionLetter.Q v))
      _ =
          localWordScaledTraceTerm (p := p) (q := q) N A 0 Q
            (Fin.append (Fin.cons LocalExpansionLetter.Q v) u) := by
              rw [lower_localWordScaledTraceTerm_append_rotate
                (p := p) (q := q) (N := N) A 0 Q u
                (Fin.cons LocalExpansionLetter.Q v)]
              simpa using
                lower_localWordScaledTraceTerm_cast
                  (p := p) (q := q) (N := N) A 0 Q
                  (h := Nat.add_comm r (n + 1))
                  (w := Fin.append (Fin.cons LocalExpansionLetter.Q v) u)
      _ = localWordScaledTraceTerm (p := p) (q := q) N A 0 Q wRot := by
            symm
            simpa using
              lower_localWordScaledTraceTerm_cast
                (p := p) (q := q) (N := N) A 0 Q
                (h := hrot.symm)
                (w := Fin.append (Fin.cons LocalExpansionLetter.Q v) u)

/-- The occurrence-based split frontier implies the full cyclic normalization
for this word. -/
theorem lowerLocalTwoLetterMixedWordCyclicNormalization_of_occurrenceSplit
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    {N : ℝ} {m : ℕ} {A Q : BipMatrix p q}
    {w : Fin (m + 1) → LocalExpansionLetter}
    (hOccurrence :
      lowerLocalTwoLetterMixedWordCyclicPrefixHeadQSplitFromOccurrence) :
    lowerLocalTwoLetterMixedWordCyclicNormalization (N := N) A Q w := by
  intro hNoL hQtwo
  exact
    lowerLocalTwoLetterMixedWordCyclicNormalization_of_appendHeadQSplit
      (p := p) (q := q) (N := N) (A := A) (Q := Q)
      (w := w)
      (lowerLocalTwoLetterMixedWordCyclicPrefixHeadQSplit_of_twoQ_of_occurrenceSplit
        hOccurrence hQtwo)
      hNoL hQtwo

/-- Close the arbitrary no-`L`, at-least-two-`Q` cyclic normalization. -/
theorem lowerLocalTwoLetterMixedWordCyclicNormalization_closed
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    {N : ℝ} {m : ℕ} {A Q : BipMatrix p q}
    {w : Fin (m + 1) → LocalExpansionLetter} :
    lowerLocalTwoLetterMixedWordCyclicNormalization (N := N) A Q w :=
  lowerLocalTwoLetterMixedWordCyclicNormalization_of_occurrenceSplit
    (p := p) (q := q) (N := N) (A := A) (Q := Q)
    lowerLocalTwoLetterMixedWordCyclicPrefixHeadQSplitFromOccurrence_closed

/-- Paper-facing name for the no-`L`, at-least-two-`Q` cyclic head-`Q`
normal form.  This is an alias for the verified local frontier used by the
many-`Q` PT trace estimate. -/
def noL_twoQ_word_cyclic_headQ_normalForm
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    {N : ℝ} {m : ℕ} (A Q : BipMatrix p q)
    (w : Fin (m + 1) → LocalExpansionLetter) : Prop :=
  lowerLocalTwoLetterMixedWordCyclicNormalization (N := N) A Q w

/-- The paper-facing cyclic normal-form name is exactly the existing local
frontier name. -/
theorem noL_twoQ_word_cyclic_headQ_normalForm_iff_lowerLocalTwoLetterMixedWordCyclicNormalization
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    {N : ℝ} {m : ℕ} (A Q : BipMatrix p q)
    (w : Fin (m + 1) → LocalExpansionLetter) :
    noL_twoQ_word_cyclic_headQ_normalForm (N := N) A Q w ↔
      lowerLocalTwoLetterMixedWordCyclicNormalization (N := N) A Q w := by
  rfl

/-- The paper-facing cyclic normal form already follows from the smaller
append/split frontier. -/
theorem noL_twoQ_word_cyclic_headQ_normalForm_of_cyclicPrefixHeadQSplit
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    {N : ℝ} {m : ℕ} {A Q : BipMatrix p q}
    {w : Fin (m + 1) → LocalExpansionLetter}
    (hSplit : lowerLocalTwoLetterMixedWordCyclicPrefixHeadQSplit w) :
    noL_twoQ_word_cyclic_headQ_normalForm (N := N) A Q w :=
  lowerLocalTwoLetterMixedWordCyclicNormalization_of_appendHeadQSplit
    (p := p) (q := q) (N := N) (A := A) (Q := Q) hSplit

/-- Paper-facing normal form from the exact occurrence-split frontier. -/
theorem noL_twoQ_word_cyclic_headQ_normalForm_of_occurrenceSplit
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    {N : ℝ} {m : ℕ} {A Q : BipMatrix p q}
    {w : Fin (m + 1) → LocalExpansionLetter}
    (hOccurrence :
      lowerLocalTwoLetterMixedWordCyclicPrefixHeadQSplitFromOccurrence) :
    noL_twoQ_word_cyclic_headQ_normalForm (N := N) A Q w :=
  lowerLocalTwoLetterMixedWordCyclicNormalization_of_occurrenceSplit
    (p := p) (q := q) (N := N) (A := A) (Q := Q) hOccurrence

/-- Closed paper-facing cyclic normal form. -/
theorem noL_twoQ_word_cyclic_headQ_normalForm_closed
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    {N : ℝ} {m : ℕ} {A Q : BipMatrix p q}
    {w : Fin (m + 1) → LocalExpansionLetter} :
    noL_twoQ_word_cyclic_headQ_normalForm (N := N) A Q w :=
  lowerLocalTwoLetterMixedWordCyclicNormalization_closed
    (p := p) (q := q) (N := N) (A := A) (Q := Q)

/-- The head-`Q` many-spike estimate can consume exactly the narrow
append/head-`Q` split.  The split itself supplies the second `Q` in the tail. -/
theorem lower_localWordScaledTraceTerm_manyQ_headQ_noL_bound_of_appendHeadQSplit
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    {N M Sbound : ℝ} {m : ℕ} {A Q : BipMatrix p q}
    {w : Fin (m + 1) → LocalExpansionLetter}
    (hSplit : lowerLocalTwoLetterMixedWordAppendHeadQSplit w)
    (hN : 0 ≤ N)
    (hMdivN_nonneg : 0 ≤ M / N)
    (hSbound_nonneg : 0 ≤ Sbound)
    (hA_op : opNorm (p := p) (q := q) A ≤ M / N)
    (hQ_op : opNorm (p := p) (q := q) Q ≤ Sbound)
    (hQ_frob :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) Q ≤ Sbound)
    (hNoL : ∀ i : Fin (m + 1), w i ≠ LocalExpansionLetter.L) :
    |localWordScaledTraceTerm (p := p) (q := q) N A 0 Q w| ≤
      N ^ m *
        ((M / N) ^ localWordLetterCount LocalExpansionLetter.A w *
          Sbound ^ localWordLetterCount LocalExpansionLetter.Q w) := by
  rcases hSplit with ⟨hHead, r, n, hlen, C, D, htail⟩
  have htail_count :
      localWordLetterCount LocalExpansionLetter.Q (Fin.tail w) =
        localWordLetterCount LocalExpansionLetter.Q
          (Fin.append C (Fin.cons LocalExpansionLetter.Q D)) := by
    rw [htail]
    simpa using
      lower_localWordLetterCount_cast
        (h := hlen.symm)
        (letter := LocalExpansionLetter.Q)
        (w := Fin.append C (Fin.cons LocalExpansionLetter.Q D))
  have htailQpos :
      0 < localWordLetterCount LocalExpansionLetter.Q (Fin.tail w) := by
    rw [htail_count, lower_localWordLetterCount_append]
    have hcons :=
      localWordLetterCount_cons
        (k := n) LocalExpansionLetter.Q LocalExpansionLetter.Q D
    have hcons' :
        localWordLetterCount LocalExpansionLetter.Q
            (Fin.cons LocalExpansionLetter.Q D) =
          1 + localWordLetterCount LocalExpansionLetter.Q D := by
      simpa using hcons
    rw [hcons']
    omega
  have hcountW :
      localWordLetterCount LocalExpansionLetter.Q w =
        1 + localWordLetterCount LocalExpansionLetter.Q (Fin.tail w) := by
    have hcount :=
      localWordLetterCount_cons
        (k := m) LocalExpansionLetter.Q (w 0) (Fin.tail w)
    have hconsw : Fin.cons (w 0) (Fin.tail w) = w :=
      Fin.cons_self_tail w
    calc
      localWordLetterCount LocalExpansionLetter.Q w
          =
            localWordLetterCount LocalExpansionLetter.Q
              (Fin.cons (w 0) (Fin.tail w)) := by
                rw [hconsw]
      _ =
          (if w 0 = LocalExpansionLetter.Q then 1 else 0) +
            localWordLetterCount LocalExpansionLetter.Q (Fin.tail w) := hcount
      _ = 1 + localWordLetterCount LocalExpansionLetter.Q (Fin.tail w) := by
            simp [hHead]
  have hQtwo : 2 ≤ localWordLetterCount LocalExpansionLetter.Q w := by
    rw [hcountW]
    omega
  exact
    lower_localWordScaledTraceTerm_manyQ_headQ_noL_bound
      (p := p) (q := q) (N := N) (M := M) (Sbound := Sbound)
      (m := m) (A := A) (Q := Q) (w := w)
      hN hMdivN_nonneg hSbound_nonneg hA_op hQ_op hQ_frob
      hNoL hHead hQtwo

/-- Count and length bookkeeping exported by the narrow head-`Q` split.

Here `A` is the background letter in the local two-letter alphabet. -/
theorem lowerLocalTwoLetterMixedWordAppendHeadQSplit_count_identities
    {m : ℕ} {w : Fin (m + 1) → LocalExpansionLetter}
    (hSplit : lowerLocalTwoLetterMixedWordAppendHeadQSplit w) :
    ∃ r n : ℕ, ∃ hlen : r + (n + 1) = m,
      ∃ C : Fin r → LocalExpansionLetter,
        ∃ D : Fin n → LocalExpansionLetter,
          Fin.tail w =
              (Fin.append C (Fin.cons LocalExpansionLetter.Q D)) ∘
                Fin.cast hlen.symm ∧
          localWordLetterCount LocalExpansionLetter.Q C +
              localWordLetterCount LocalExpansionLetter.Q D =
            localWordLetterCount LocalExpansionLetter.Q w - 2 ∧
          localWordLetterCount LocalExpansionLetter.A C +
              localWordLetterCount LocalExpansionLetter.A D =
            localWordLetterCount LocalExpansionLetter.A w ∧
          r + n = m - 1 := by
  rcases hSplit with ⟨hHead, r, n, hlen, C, D, htail⟩
  refine ⟨r, n, hlen, C, D, htail, ?_, ?_, ?_⟩
  · have htail_count :
        localWordLetterCount LocalExpansionLetter.Q (Fin.tail w) =
          localWordLetterCount LocalExpansionLetter.Q
            (Fin.append C (Fin.cons LocalExpansionLetter.Q D)) := by
      rw [htail]
      simpa using
        lower_localWordLetterCount_cast
          (h := hlen.symm)
          (letter := LocalExpansionLetter.Q)
          (w := Fin.append C (Fin.cons LocalExpansionLetter.Q D))
    have htail_expand :
        localWordLetterCount LocalExpansionLetter.Q (Fin.tail w) =
          localWordLetterCount LocalExpansionLetter.Q C +
            (1 + localWordLetterCount LocalExpansionLetter.Q D) := by
      rw [htail_count, lower_localWordLetterCount_append]
      have hcons :=
        localWordLetterCount_cons
          (k := n) LocalExpansionLetter.Q LocalExpansionLetter.Q D
      have hcons' :
          localWordLetterCount LocalExpansionLetter.Q
              (Fin.cons LocalExpansionLetter.Q D) =
            1 + localWordLetterCount LocalExpansionLetter.Q D := by
        simpa using hcons
      rw [hcons']
    have hcountW :
        localWordLetterCount LocalExpansionLetter.Q w =
          1 + localWordLetterCount LocalExpansionLetter.Q (Fin.tail w) := by
      have hcount :=
        localWordLetterCount_cons
          (k := m) LocalExpansionLetter.Q (w 0) (Fin.tail w)
      have hconsw : Fin.cons (w 0) (Fin.tail w) = w :=
        Fin.cons_self_tail w
      calc
        localWordLetterCount LocalExpansionLetter.Q w
            =
              localWordLetterCount LocalExpansionLetter.Q
                (Fin.cons (w 0) (Fin.tail w)) := by
                  rw [hconsw]
        _ =
            (if w 0 = LocalExpansionLetter.Q then 1 else 0) +
              localWordLetterCount LocalExpansionLetter.Q (Fin.tail w) := hcount
        _ = 1 + localWordLetterCount LocalExpansionLetter.Q (Fin.tail w) := by
              simp [hHead]
    omega
  · have htail_count :
        localWordLetterCount LocalExpansionLetter.A (Fin.tail w) =
          localWordLetterCount LocalExpansionLetter.A
            (Fin.append C (Fin.cons LocalExpansionLetter.Q D)) := by
      rw [htail]
      simpa using
        lower_localWordLetterCount_cast
          (h := hlen.symm)
          (letter := LocalExpansionLetter.A)
          (w := Fin.append C (Fin.cons LocalExpansionLetter.Q D))
    have htail_expand :
        localWordLetterCount LocalExpansionLetter.A (Fin.tail w) =
          localWordLetterCount LocalExpansionLetter.A C +
            localWordLetterCount LocalExpansionLetter.A D := by
      rw [htail_count, lower_localWordLetterCount_append]
      have hcons :=
        localWordLetterCount_cons
          (k := n) LocalExpansionLetter.A LocalExpansionLetter.Q D
      have hcons' :
          localWordLetterCount LocalExpansionLetter.A
              (Fin.cons LocalExpansionLetter.Q D) =
            localWordLetterCount LocalExpansionLetter.A D := by
        simpa using hcons
      rw [hcons']
    have hcountW :
        localWordLetterCount LocalExpansionLetter.A w =
          localWordLetterCount LocalExpansionLetter.A (Fin.tail w) := by
      have hcount :=
        localWordLetterCount_cons
          (k := m) LocalExpansionLetter.A (w 0) (Fin.tail w)
      have hconsw : Fin.cons (w 0) (Fin.tail w) = w :=
        Fin.cons_self_tail w
      calc
        localWordLetterCount LocalExpansionLetter.A w
            =
              localWordLetterCount LocalExpansionLetter.A
                (Fin.cons (w 0) (Fin.tail w)) := by
                  rw [hconsw]
        _ =
            (if w 0 = LocalExpansionLetter.A then 1 else 0) +
              localWordLetterCount LocalExpansionLetter.A (Fin.tail w) := hcount
        _ = localWordLetterCount LocalExpansionLetter.A (Fin.tail w) := by
              simp [hHead]
    omega
  · omega

/-- Arbitrary no-`L`, many-spike local word bound, assuming only the exact
finite cyclic-normalization bridge above.

This packages the PT analytic estimate for all mixed words with at least two
spike letters.  The only remaining input is the purely combinatorial
normal-form lemma `lowerLocalTwoLetterMixedWordCyclicNormalization`. -/
theorem lower_localWordScaledTraceTerm_manyQ_noL_bound_of_cyclicNormalization
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    {N M Sbound : ℝ} {m : ℕ} {A Q : BipMatrix p q}
    {w : Fin (m + 1) → LocalExpansionLetter}
    (hCyclic :
      lowerLocalTwoLetterMixedWordCyclicNormalization (N := N) A Q w)
    (hN : 0 ≤ N)
    (hMdivN_nonneg : 0 ≤ M / N)
    (hSbound_nonneg : 0 ≤ Sbound)
    (hA_op : opNorm (p := p) (q := q) A ≤ M / N)
    (hQ_op : opNorm (p := p) (q := q) Q ≤ Sbound)
    (hQ_frob :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) Q ≤ Sbound)
    (hNoL : ∀ i : Fin (m + 1), w i ≠ LocalExpansionLetter.L)
    (hQtwo : 2 ≤ localWordLetterCount LocalExpansionLetter.Q w) :
    |localWordScaledTraceTerm (p := p) (q := q) N A 0 Q w| ≤
      N ^ m *
        ((M / N) ^ localWordLetterCount LocalExpansionLetter.A w *
          Sbound ^ localWordLetterCount LocalExpansionLetter.Q w) := by
  rcases hCyclic hNoL hQtwo with
    ⟨wRot, hHead, hNoLRot, hAcount, hQcount, hTrace⟩
  rw [hTrace]
  have hQtwoRot : 2 ≤ localWordLetterCount LocalExpansionLetter.Q wRot := by
    simpa [hQcount]
  have hBound :
      |localWordScaledTraceTerm (p := p) (q := q) N A 0 Q wRot| ≤
        N ^ m *
          ((M / N) ^ localWordLetterCount LocalExpansionLetter.A wRot *
            Sbound ^ localWordLetterCount LocalExpansionLetter.Q wRot) :=
    lower_localWordScaledTraceTerm_manyQ_headQ_noL_bound
      (p := p) (q := q) (N := N) (M := M) (Sbound := Sbound)
      (m := m) (A := A) (Q := Q) (w := wRot)
      hN hMdivN_nonneg hSbound_nonneg hA_op hQ_op hQ_frob
      hNoLRot hHead hQtwoRot
  simpa [hAcount, hQcount] using hBound

/-- The arbitrary-word many-`Q` bound now depends only on the smaller
append/split finite-word frontier. -/
theorem lower_localWordScaledTraceTerm_manyQ_noL_bound_of_cyclicPrefixHeadQSplit
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    {N M Sbound : ℝ} {m : ℕ} {A Q : BipMatrix p q}
    {w : Fin (m + 1) → LocalExpansionLetter}
    (hSplit : lowerLocalTwoLetterMixedWordCyclicPrefixHeadQSplit w)
    (hN : 0 ≤ N)
    (hMdivN_nonneg : 0 ≤ M / N)
    (hSbound_nonneg : 0 ≤ Sbound)
    (hA_op : opNorm (p := p) (q := q) A ≤ M / N)
    (hQ_op : opNorm (p := p) (q := q) Q ≤ Sbound)
    (hQ_frob :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) Q ≤ Sbound)
    (hNoL : ∀ i : Fin (m + 1), w i ≠ LocalExpansionLetter.L)
    (hQtwo : 2 ≤ localWordLetterCount LocalExpansionLetter.Q w) :
    |localWordScaledTraceTerm (p := p) (q := q) N A 0 Q w| ≤
      N ^ m *
        ((M / N) ^ localWordLetterCount LocalExpansionLetter.A w *
          Sbound ^ localWordLetterCount LocalExpansionLetter.Q w) := by
  exact
    lower_localWordScaledTraceTerm_manyQ_noL_bound_of_cyclicNormalization
      (p := p) (q := q) (N := N) (M := M) (Sbound := Sbound)
      (A := A) (Q := Q)
      (w := w)
      (lowerLocalTwoLetterMixedWordCyclicNormalization_of_appendHeadQSplit
        (p := p) (q := q) (N := N) (A := A) (Q := Q) hSplit)
      hN hMdivN_nonneg hSbound_nonneg hA_op hQ_op hQ_frob hNoL hQtwo

/-- The arbitrary-word many-`Q` bound from the exact occurrence-split
frontier. -/
theorem lower_localWordScaledTraceTerm_manyQ_noL_bound_of_occurrenceSplit
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    {N M Sbound : ℝ} {m : ℕ} {A Q : BipMatrix p q}
    {w : Fin (m + 1) → LocalExpansionLetter}
    (hOccurrence :
      lowerLocalTwoLetterMixedWordCyclicPrefixHeadQSplitFromOccurrence)
    (hN : 0 ≤ N)
    (hMdivN_nonneg : 0 ≤ M / N)
    (hSbound_nonneg : 0 ≤ Sbound)
    (hA_op : opNorm (p := p) (q := q) A ≤ M / N)
    (hQ_op : opNorm (p := p) (q := q) Q ≤ Sbound)
    (hQ_frob :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) Q ≤ Sbound)
    (hNoL : ∀ i : Fin (m + 1), w i ≠ LocalExpansionLetter.L)
    (hQtwo : 2 ≤ localWordLetterCount LocalExpansionLetter.Q w) :
    |localWordScaledTraceTerm (p := p) (q := q) N A 0 Q w| ≤
      N ^ m *
        ((M / N) ^ localWordLetterCount LocalExpansionLetter.A w *
          Sbound ^ localWordLetterCount LocalExpansionLetter.Q w) := by
  exact
    lower_localWordScaledTraceTerm_manyQ_noL_bound_of_cyclicNormalization
      (p := p) (q := q) (N := N) (M := M) (Sbound := Sbound)
      (A := A) (Q := Q) (w := w)
      (lowerLocalTwoLetterMixedWordCyclicNormalization_of_occurrenceSplit
        (p := p) (q := q) (N := N) (A := A) (Q := Q) hOccurrence)
      hN hMdivN_nonneg hSbound_nonneg hA_op hQ_op hQ_frob hNoL hQtwo

/-- Closed arbitrary no-`L`, many-`Q` local word bound. -/
theorem lower_localWordScaledTraceTerm_manyQ_noL_bound
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    {N M Sbound : ℝ} {m : ℕ} {A Q : BipMatrix p q}
    {w : Fin (m + 1) → LocalExpansionLetter}
    (hN : 0 ≤ N)
    (hMdivN_nonneg : 0 ≤ M / N)
    (hSbound_nonneg : 0 ≤ Sbound)
    (hA_op : opNorm (p := p) (q := q) A ≤ M / N)
    (hQ_op : opNorm (p := p) (q := q) Q ≤ Sbound)
    (hQ_frob :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) Q ≤ Sbound)
    (hNoL : ∀ i : Fin (m + 1), w i ≠ LocalExpansionLetter.L)
    (hQtwo : 2 ≤ localWordLetterCount LocalExpansionLetter.Q w) :
    |localWordScaledTraceTerm (p := p) (q := q) N A 0 Q w| ≤
      N ^ m *
        ((M / N) ^ localWordLetterCount LocalExpansionLetter.A w *
          Sbound ^ localWordLetterCount LocalExpansionLetter.Q w) :=
  lower_localWordScaledTraceTerm_manyQ_noL_bound_of_cyclicNormalization
    (p := p) (q := q) (N := N) (M := M) (Sbound := Sbound)
    (A := A) (Q := Q) (w := w)
    (lowerLocalTwoLetterMixedWordCyclicNormalization_closed
      (p := p) (q := q) (N := N) (A := A) (Q := Q))
    hN hMdivN_nonneg hSbound_nonneg hA_op hQ_op hQ_frob hNoL hQtwo

/-- A two-letter word with exactly one spike/quadratic letter evaluates as a
background power, followed by the spike letter, followed by another background
power. -/
theorem lower_localWordMatrixProduct_exists_powA_Q_powA_of_oneQ_noL
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    {k : ℕ} (A Q : BipMatrix p q) (w : Fin k → LocalExpansionLetter)
    (hNoL : ∀ i : Fin k, w i ≠ LocalExpansionLetter.L)
    (hQone : localWordLetterCount LocalExpansionLetter.Q w = 1) :
    ∃ r s : ℕ, r + 1 + s = k ∧
      localWordMatrixProduct (p := p) (q := q) A 0 Q w = A ^ r * Q * A ^ s := by
  induction k with
  | zero =>
      simp [localWordLetterCount] at hQone
  | succ k ih =>
      let wt : Fin k → LocalExpansionLetter := Fin.tail w
      have hcount := localWordLetterCount_cons LocalExpansionLetter.Q (w 0) wt
      by_cases h0Q : w 0 = LocalExpansionLetter.Q
      · have htailQ0 : localWordLetterCount LocalExpansionLetter.Q wt = 0 := by
          have hcountw :
              localWordLetterCount LocalExpansionLetter.Q w =
                (if w 0 = LocalExpansionLetter.Q then 1 else 0) +
                  localWordLetterCount LocalExpansionLetter.Q wt := by
            simpa [wt, Fin.cons_self_tail] using hcount
          rw [hcountw] at hQone
          simp [h0Q] at hQone
          exact hQone
        have hNoQ_tail : ∀ i : Fin k, wt i ≠ LocalExpansionLetter.Q :=
          lower_localWord_no_letter_of_count_zero htailQ0
        have hNoL_tail : ∀ i : Fin k, wt i ≠ LocalExpansionLetter.L := by
          intro i hi
          exact hNoL i.succ hi
        refine ⟨0, k, ?_, ?_⟩
        · omega
        · have htail :=
            lower_localWordMatrixProduct_pow_A_of_noL_noQ
              (p := p) (q := q) A Q wt hNoL_tail hNoQ_tail
          change localLetterMatrix A 0 Q (w 0) *
              localWordMatrixProduct (p := p) (q := q) A 0 Q wt =
            A ^ 0 * Q * A ^ k
          rw [h0Q, htail]
          simp [localLetterMatrix]
      · have h0A : w 0 = LocalExpansionLetter.A := by
          cases h : w 0 with
          | A => rfl
          | L => exact False.elim (hNoL 0 h)
          | Q => exact False.elim (h0Q h)
        have htailQone : localWordLetterCount LocalExpansionLetter.Q wt = 1 := by
          have hcountw :
              localWordLetterCount LocalExpansionLetter.Q w =
                (if w 0 = LocalExpansionLetter.Q then 1 else 0) +
                  localWordLetterCount LocalExpansionLetter.Q wt := by
            simpa [wt, Fin.cons_self_tail] using hcount
          rw [hcountw] at hQone
          simp [h0Q] at hQone
          exact hQone
        have hNoL_tail : ∀ i : Fin k, wt i ≠ LocalExpansionLetter.L := by
          intro i hi
          exact hNoL i.succ hi
        rcases ih wt hNoL_tail htailQone with ⟨r, s, hrs, hprod⟩
        refine ⟨r + 1, s, ?_, ?_⟩
        · omega
        · change localLetterMatrix A 0 Q (w 0) *
              localWordMatrixProduct (p := p) (q := q) A 0 Q wt =
            A ^ (r + 1) * Q * A ^ s
          rw [h0A, hprod]
          simp [localLetterMatrix, pow_succ', mul_assoc]

/-- Cyclic trace reduction for a word with one spike letter. -/
theorem lower_trace_powA_Q_powA_eq_trace_Q_powA
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    (A Q : BipMatrix p q) {k r s : ℕ}
    (hrs : r + 1 + s = k) :
    Matrix.trace (A ^ r * Q * A ^ s) =
      Matrix.trace (Q * A ^ (k - 1)) := by
  have hcyc := Matrix.trace_mul_cycle (A := A ^ r) (B := Q) (C := A ^ s)
  have hcomm := Matrix.trace_mul_comm (A := A ^ s * A ^ r) (B := Q)
  calc
    Matrix.trace (A ^ r * Q * A ^ s)
        = Matrix.trace (A ^ s * A ^ r * Q) := hcyc
    _ = Matrix.trace (Q * (A ^ s * A ^ r)) := hcomm
    _ = Matrix.trace (Q * A ^ (k - 1)) := by
      have hsadd : s + r = k - 1 := by omega
      rw [← pow_add]
      rw [hsadd]

/-- One-spike local word bound for the corrected partial-transpose mixed
route.

The word algebra reduces the term to the cyclic form `Tr(Q * A^(k-1))`; the
analytic estimate is then the Frobenius-pairing bound with the background edge
scale. -/
theorem lower_localWordScaledTraceTerm_oneQ_noL_bound
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    {N M Sbound : ℝ} {k : ℕ} {A Q : BipMatrix p q}
    {w : Fin k → LocalExpansionLetter}
    (hN : 0 ≤ N)
    (hk : 3 ≤ k)
    (hSbound_nonneg : 0 ≤ Sbound)
    (hQ_frob :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) Q ≤ Sbound)
    (hA_op : opNorm (p := p) (q := q) A ≤ M / N)
    (hA_frob :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) A ≤
        M / Real.sqrt N)
    (hNoL : ∀ i : Fin k, w i ≠ LocalExpansionLetter.L)
    (hQone : localWordLetterCount LocalExpansionLetter.Q w = 1) :
    |localWordScaledTraceTerm (p := p) (q := q) N A 0 Q w| ≤
      N ^ (k - 1) *
        (Sbound * ((M / N) ^ (k - 2) * (M / Real.sqrt N))) := by
  rcases lower_localWordMatrixProduct_exists_powA_Q_powA_of_oneQ_noL
      (p := p) (q := q) A Q w hNoL hQone with
    ⟨r, s, hrs, hprod⟩
  have hNpow : 0 ≤ N ^ (k - 1) := pow_nonneg hN _
  have htrace_eq :
      (Matrix.trace
        (localWordMatrixProduct (p := p) (q := q) A 0 Q w)).re =
        (Matrix.trace (Q * A ^ (k - 1))).re := by
    rw [hprod]
    exact congrArg Complex.re
      (lower_trace_powA_Q_powA_eq_trace_Q_powA
        (p := p) (q := q) A Q hrs)
  unfold localWordScaledTraceTerm
  rw [htrace_eq]
  rw [abs_mul, abs_of_nonneg hNpow]
  exact
    mul_le_mul_of_nonneg_left
      (lower_trace_one_spike_cyclic_bound_with_frobenius
        (p := p) (q := q) (N := N) (M := M) (Sbound := Sbound)
        (k := k) (S := Q) (B := A)
        hk hSbound_nonneg hQ_frob hA_op hA_frob)
      hNpow

/-! ### Runtime mixed-word envelope coming directly from the favourable event -/

/-- Literal runtime envelope for a single mixed word on the one-column
favourable event.

This keeps the spike and background scales exactly as they are supplied by the
current concrete event:

* the spike letter is bounded by the Beta-interval upper endpoint,
* the background letter is bounded by `lowerConcreteM R a slack d`.

Unlike `lowerPartialTransposeMixedWordBoundD`, this envelope makes no attempt
to replace the runtime background threshold by a fixed scalar. -/
noncomputable def lowerConcreteMixedRuntimeWordBound
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (a slack : ℝ) (d : ℕ)
    (w : Fin k → LocalExpansionLetter) : ℝ :=
  let N : ℝ := lowerConcreteN d
  let M : ℝ := lowerConcreteM R a slack d
  let S : ℝ :=
    betaColumnIntervalUpper
      (betaColumnSpikeScale N (spikeSpeed k d) a)
      (lowerConcreteDelta a slack d)
  if _hL : localWordLetterCount LocalExpansionLetter.L w = 0 then
    if _hQ1 : localWordLetterCount LocalExpansionLetter.Q w = 1 then
      N ^ (k - 1) * (S * ((M / N) ^ (k - 2) * (M / Real.sqrt N)))
    else if _hQ2 : 2 ≤ localWordLetterCount LocalExpansionLetter.Q w then
      N ^ (k - 1) *
        ((M / N) ^ localWordLetterCount LocalExpansionLetter.A w *
          S ^ localWordLetterCount LocalExpansionLetter.Q w)
    else
      0
  else
    0

/-- A runtime mixed word containing an `L` contributes no no-`L` PT mixed
budget.  This exposes the first case split used by the endpoint domination
leaf as a standalone reusable lemma. -/
theorem lowerConcreteMixedRuntimeWordBound_eq_zero_of_exists_L
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (a slack : ℝ) (d : ℕ)
    (w : Fin k → LocalExpansionLetter)
    (hL : ∃ i : Fin k, w i = LocalExpansionLetter.L) :
    lowerConcreteMixedRuntimeWordBound R k a slack d w = 0 := by
  have hLpos :
      0 < localWordLetterCount LocalExpansionLetter.L w :=
    lower_localWordLetterCount_pos_of_exists
      (letter := LocalExpansionLetter.L) (w := w) hL
  have hLne :
      localWordLetterCount LocalExpansionLetter.L w ≠ 0 := by
    omega
  unfold lowerConcreteMixedRuntimeWordBound
  simp [hLne]

/-- Runtime envelope in the exactly-one-`Q`, no-`L` case. -/
theorem lowerConcreteMixedRuntimeWordBound_eq_oneQ_noL
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (a slack : ℝ) (d : ℕ)
    (w : Fin k → LocalExpansionLetter)
    (hL0 : localWordLetterCount LocalExpansionLetter.L w = 0)
    (hQ1 : localWordLetterCount LocalExpansionLetter.Q w = 1) :
    lowerConcreteMixedRuntimeWordBound R k a slack d w =
      (lowerConcreteN d) ^ (k - 1) *
        (betaColumnIntervalUpper
            (betaColumnSpikeScale (lowerConcreteN d) (spikeSpeed k d) a)
            (lowerConcreteDelta a slack d) *
          (((lowerConcreteM R a slack d) / (lowerConcreteN d)) ^ (k - 2) *
            ((lowerConcreteM R a slack d) / Real.sqrt (lowerConcreteN d)))) := by
  unfold lowerConcreteMixedRuntimeWordBound
  simp [hL0, hQ1]

/-- Runtime envelope in the many-`Q`, no-`L` case. -/
theorem lowerConcreteMixedRuntimeWordBound_eq_manyQ_noL
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (a slack : ℝ) (d : ℕ)
    (w : Fin k → LocalExpansionLetter)
    (hL0 : localWordLetterCount LocalExpansionLetter.L w = 0)
    (hQtwo : 2 ≤ localWordLetterCount LocalExpansionLetter.Q w) :
    lowerConcreteMixedRuntimeWordBound R k a slack d w =
      (lowerConcreteN d) ^ (k - 1) *
        (((lowerConcreteM R a slack d) / (lowerConcreteN d)) ^
            localWordLetterCount LocalExpansionLetter.A w *
          betaColumnIntervalUpper
              (betaColumnSpikeScale (lowerConcreteN d) (spikeSpeed k d) a)
              (lowerConcreteDelta a slack d) ^
            localWordLetterCount LocalExpansionLetter.Q w) := by
  have hQ1ne :
      localWordLetterCount LocalExpansionLetter.Q w ≠ 1 := by
    omega
  unfold lowerConcreteMixedRuntimeWordBound
  simp [hL0, hQ1ne, hQtwo]

/-- Concrete spike speed expressed in the operator dimension
`lowerConcreteN d = d²`. -/
theorem lowerConcrete_spikeSpeed_eq_lowerConcreteN_rpow
    {k d : ℕ} (hd : 0 < d) :
    spikeSpeed k d =
      (lowerConcreteN d : ℝ) ^ (1 + 1 / (k : ℝ)) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  rw [spikeSpeed, lowerConcreteN, Nat.cast_pow]
  rw [← Real.rpow_natCast (d : ℝ) 2]
  rw [← Real.rpow_mul (le_of_lt hdR)]
  congr 1
  ring

/-- The concrete beta-column spike scale is exactly
`a * N^(-1+1/k)` in `N = d²` variables. -/
theorem lowerConcrete_betaColumnSpikeScale_eq_rpow
    {k d : ℕ} (a : ℝ) (hd : 0 < d) :
    betaColumnSpikeScale (lowerConcreteN d : ℝ) (spikeSpeed k d) a =
      a * (lowerConcreteN d : ℝ) ^ ((-1 : ℝ) + 1 / (k : ℝ)) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hNpos : 0 < (lowerConcreteN d : ℝ) := by
    simp [lowerConcreteN, pow_two, mul_pos hdR hdR]
  have hspeed :=
    lowerConcrete_spikeSpeed_eq_lowerConcreteN_rpow
      (k := k) (d := d) hd
  rw [betaColumnSpikeScale, hspeed]
  rw [div_eq_mul_inv, mul_assoc]
  congr 1
  rw [← Real.rpow_natCast (lowerConcreteN d : ℝ) 2]
  rw [← Real.rpow_neg hNpos.le]
  rw [← Real.rpow_add hNpos]
  congr 1
  ring

/-- Eventual scalar domination of the concrete beta-interval upper endpoint by
the slackened sharp spike scale.

This closes the spike-radius half of the scalar mixed domination problem; the
remaining scalar issue is the comparison of the runtime background threshold
`lowerConcreteM R a slack d` with the fixed envelope parameter `M`. -/
theorem lowerConcrete_betaColumnIntervalUpper_spike_le_slack_rpow
    {k : ℕ} :
    ∀ a : ℝ,
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          betaColumnIntervalUpper
            (betaColumnSpikeScale
              (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
            (lowerConcreteDelta a slack d) ≤
            (a + slack) *
              (lowerConcreteN d : ℝ) ^ ((-1 : ℝ) + 1 / (k : ℝ)) := by
  intro a slack hslack
  have hcoef_tendsto :
      Tendsto (fun d : ℕ => (1 + lowerConcreteDelta a slack d) * a)
        atTop (nhds a) := by
    have hfactor :
        Tendsto (fun d : ℕ => 1 + lowerConcreteDelta a slack d)
          atTop (nhds 1) := by
      simpa using
        tendsto_const_nhds.add
          (lower_concrete_delta_tendsto_zero (a := a) (slack := slack))
    simpa using hfactor.mul tendsto_const_nhds
  have hcoef_ev :
      ∀ᶠ d : ℕ in atTop,
        (1 + lowerConcreteDelta a slack d) * a ≤ a + slack := by
    exact
      (hcoef_tendsto.eventually
        (eventually_lt_nhds (show a < a + slack by linarith))).mono
        (by
          intro d hd
          exact le_of_lt hd)
  filter_upwards [eventually_gt_atTop 0, hcoef_ev] with d hd hcoef
  have hNnonneg :
      0 ≤ (lowerConcreteN d : ℝ) ^ ((-1 : ℝ) + 1 / (k : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  calc
    betaColumnIntervalUpper
        (betaColumnSpikeScale
          (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
        (lowerConcreteDelta a slack d)
        =
          (1 + lowerConcreteDelta a slack d) *
            (a * (lowerConcreteN d : ℝ) ^ ((-1 : ℝ) + 1 / (k : ℝ))) := by
          rw [betaColumnIntervalUpper,
            lowerConcrete_betaColumnSpikeScale_eq_rpow
              (k := k) (d := d) a hd]
    _ =
          ((1 + lowerConcreteDelta a slack d) * a) *
            (lowerConcreteN d : ℝ) ^ ((-1 : ℝ) + 1 / (k : ℝ)) := by
          ring
    _ ≤
          (a + slack) *
            (lowerConcreteN d : ℝ) ^ ((-1 : ℝ) + 1 / (k : ℝ)) := by
          exact mul_le_mul_of_nonneg_right hcoef hNnonneg

/-- Lower companion to `lowerConcrete_betaColumnIntervalUpper_spike_le_slack_rpow`.

The interval upper endpoint is at least the nominal spike scale.  This is useful
when diagnosing why a runtime mixed envelope using the concrete `lowerConcreteM`
cannot generally be dominated by a fixed PT edge coefficient. -/
theorem lowerConcrete_betaColumnIntervalUpper_spike_ge_rpow
    {k d : ℕ} (a slack : ℝ) (hd : 0 < d) (ha : 0 ≤ a) :
    a * (lowerConcreteN d : ℝ) ^ ((-1 : ℝ) + 1 / (k : ℝ)) ≤
      betaColumnIntervalUpper
        (betaColumnSpikeScale
          (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
        (lowerConcreteDelta a slack d) := by
  have hdelta_nonneg : 0 ≤ lowerConcreteDelta a slack d := by
    have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
    simp [lowerConcreteDelta, le_of_lt hdR]
  have hpow_nonneg :
      0 ≤ (lowerConcreteN d : ℝ) ^ ((-1 : ℝ) + 1 / (k : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  have hq_nonneg :
      0 ≤ a * (lowerConcreteN d : ℝ) ^ ((-1 : ℝ) + 1 / (k : ℝ)) :=
    mul_nonneg ha hpow_nonneg
  calc
    a * (lowerConcreteN d : ℝ) ^ ((-1 : ℝ) + 1 / (k : ℝ))
        ≤ (1 + lowerConcreteDelta a slack d) *
            (a * (lowerConcreteN d : ℝ) ^ ((-1 : ℝ) + 1 / (k : ℝ))) := by
          nlinarith
    _ = betaColumnIntervalUpper
          (betaColumnSpikeScale
            (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
          (lowerConcreteDelta a slack d) := by
          rw [betaColumnIntervalUpper,
            lowerConcrete_betaColumnSpikeScale_eq_rpow
              (k := k) (d := d) a hd]

/-- Explicit lower bound exposing the scale of the concrete runtime background
threshold.

For the deleted-column background, `lowerConcreteM` dominates the concrete
partial-transpose operator-norm threshold.  After unfolding the canonical
high-probability package, this threshold contains the factor
`(2 + 128 * (d² + 1)) * (sample d - 1) / (1/2)`.  This is the precise scalar
place where a fixed endpoint parameter `M` must be justified or the mixed
domination leaf must be reformulated with a dimension-dependent background
budget. -/
theorem lowerConcreteM_ge_deletedColumn_gammaThreshold_explicit
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (a slack : ℝ) {d : ℕ} (hs : 0 < R.sample d) :
    ((2 + 128 * ((d : ℝ) ^ 2 + 1)) *
        ((R.sample d - 1 : ℕ) : ℝ) / (1 / 2 : ℝ)) ≤
      lowerConcreteM R a slack d := by
  have h :=
    lowerConcreteM_ge_concreteRhoGammaOpNormThreshold R a slack hs
  simpa [PptFactorization.AppendixB.concreteRhoGammaOpNormThreshold,
    PptFactorization.HighProbabilityBounds.concreteHighProbabilityBounds,
    PptFactorization.HighProbabilityBounds.bipartiteDimension,
    PptFactorization.HighProbabilityBounds.sampleDimension,
    PptFactorization.RandomMatrixModel.BipIndex, DeletedColumn, pow_two] using h

/-- The concrete runtime background threshold is eventually at least quadratic
in the tensor-side dimension parameter.

This is a verified localization of the mixed scalar obstruction: the current
runtime envelope uses `lowerConcreteM R a slack d`, while the endpoint-facing
PT budget is parameterized by a fixed scalar `M`. -/
theorem lowerConcreteM_eventually_ge_quadratic
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (a slack : ℝ) :
    ∀ᶠ d : ℕ in atTop,
      256 * (d : ℝ) ^ 2 ≤ lowerConcreteM R a slack d := by
  filter_upwards [lower_concrete_eventually_two_le_sample R] with d hs2
  have hspos : 0 < R.sample d := by omega
  have hmain :=
    lowerConcreteM_ge_deletedColumn_gammaThreshold_explicit
      (R := R) (a := a) (slack := slack) (d := d) hspos
  have hs_sub : 1 ≤ R.sample d - 1 := by omega
  have hs_subR :
      (1 : ℝ) ≤ ((R.sample d - 1 : ℕ) : ℝ) := by
    exact_mod_cast hs_sub
  have hd2_nonneg : 0 ≤ (d : ℝ) ^ 2 := by positivity
  have hfactor :
      256 * (d : ℝ) ^ 2 ≤
        ((2 + 128 * ((d : ℝ) ^ 2 + 1)) *
          ((R.sample d - 1 : ℕ) : ℝ) / (1 / 2 : ℝ)) := by
    nlinarith [hs_subR, hd2_nonneg]
  exact le_trans hfactor hmain

/-- The runtime background threshold divided by the operator dimension is
eventually bounded below by a positive fixed constant.

This is the exact ratio appearing in the scalar mixed domination leaf.  It
shows that the current runtime envelope does not have the sharp PT edge scale
`M / N` with fixed `M`; its `M`-like coefficient is already at least `256`
eventually. -/
theorem lowerConcreteM_div_lowerConcreteN_eventually_ge_const
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (a slack : ℝ) :
    ∀ᶠ d : ℕ in atTop,
      256 ≤ lowerConcreteM R a slack d / (lowerConcreteN d : ℝ) := by
  filter_upwards [eventually_gt_atTop 0,
    lowerConcreteM_eventually_ge_quadratic R a slack] with d hd hMquad
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hNpos : 0 < (lowerConcreteN d : ℝ) := by
    simp [lowerConcreteN, pow_two, mul_pos hdR hdR]
  have hquad :
      256 * (lowerConcreteN d : ℝ) ≤ lowerConcreteM R a slack d := by
    simpa [lowerConcreteN, Nat.cast_pow] using hMquad
  exact (le_div_iff₀ hNpos).mpr hquad

/-- A positive balanced aspect ratio forces the concrete sample count to tend
to infinity.

This strengthens the existing eventual nonemptiness/two-column facts and is
the scalar growth input behind the fixed-scale mixed obstruction below. -/
theorem lower_concrete_sample_eventually_ge
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (n : ℕ) :
    ∀ᶠ d : ℕ in atTop, n ≤ R.sample d := by
  have hhalf : 0 < R.lam / 2 := by linarith [R.lam_pos]
  have hratio_gt :
      ∀ᶠ d in atTop,
        R.lam / 2 <
          _root_.PptFactorization.AppendixB.ConcreteModel.sampleRatio
            R.sample d :=
    R.ratio_tendsto.eventually
      (eventually_gt_nhds (by linarith [R.lam_pos]))
  have hd2_atTop :
      Tendsto (fun d : ℕ => (d : ℝ) ^ 2) atTop atTop := by
    simpa using
      ((tendsto_rpow_atTop (show (0 : ℝ) < 2 by norm_num)).comp
        (tendsto_natCast_atTop_atTop :
          Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop))
  have hn_div :
      Tendsto (fun d : ℕ => (n : ℝ) / ((d : ℝ) ^ 2)) atTop
        (nhds 0) :=
    hd2_atTop.const_div_atTop (n : ℝ)
  have hsmall :
      ∀ᶠ d : ℕ in atTop, (n : ℝ) / ((d : ℝ) ^ 2) < R.lam / 2 := by
    exact hn_div.eventually (eventually_lt_nhds hhalf)
  filter_upwards [hratio_gt, hsmall, eventually_gt_atTop 0]
    with d hratio hsmall_d hd
  by_contra hnot
  have hs_lt : R.sample d < n := Nat.lt_of_not_ge hnot
  have hs_le_R : (R.sample d : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (le_of_lt hs_lt)
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hden_pos : 0 < (d : ℝ) ^ 2 := by positivity
  have hratio_le :
      _root_.PptFactorization.AppendixB.ConcreteModel.sampleRatio
          R.sample d ≤
        (n : ℝ) / ((d : ℝ) ^ 2) := by
    unfold _root_.PptFactorization.AppendixB.ConcreteModel.sampleRatio
    exact div_le_div_of_nonneg_right hs_le_R (le_of_lt hden_pos)
  linarith

/-- The normalized runtime background coefficient eventually exceeds every
fixed real bound.

Together with `lowerConcreteM_div_lowerConcreteN_eventually_ge_sample`, this
formalizes the fixed-scale obstruction: the current concrete favourable event
does not merely fail to give an `o(1)` coefficient; its normalized background
threshold is unbounded along the balanced regime. -/
theorem lowerConcreteM_div_lowerConcreteN_eventually_ge_real
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (a slack B : ℝ) :
    ∀ᶠ d : ℕ in atTop,
      B ≤ lowerConcreteM R a slack d / (lowerConcreteN d : ℝ) := by
  obtain ⟨n, hn⟩ := exists_nat_ge (max (1 : ℝ) (B / 256 + 1))
  have hn1R : (1 : ℝ) ≤ (n : ℝ) :=
    le_trans (le_max_left (1 : ℝ) (B / 256 + 1)) hn
  have hn1 : 1 ≤ n := by exact_mod_cast hn1R
  have hnBraw : B / 256 + 1 ≤ (n : ℝ) :=
    le_trans (le_max_right (1 : ℝ) (B / 256 + 1)) hn
  have hB_le_n : B ≤ 256 * ((n - 1 : ℕ) : ℝ) := by
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn1]
      norm_num
    rw [hcast]
    nlinarith
  filter_upwards [lower_concrete_sample_eventually_ge R n,
    eventually_gt_atTop 0] with d hsge hd
  have hspos : 0 < R.sample d := by omega
  have hmain :=
    lowerConcreteM_ge_deletedColumn_gammaThreshold_explicit
      (R := R) (a := a) (slack := slack) (d := d) hspos
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hNpos : 0 < (lowerConcreteN d : ℝ) := by
    simp [lowerConcreteN, pow_two, mul_pos hdR hdR]
  have hsub : n - 1 ≤ R.sample d - 1 := Nat.sub_le_sub_right hsge 1
  have hsubR :
      ((n - 1 : ℕ) : ℝ) ≤ ((R.sample d - 1 : ℕ) : ℝ) := by
    exact_mod_cast hsub
  have hratio_sample :
      256 * ((R.sample d - 1 : ℕ) : ℝ) ≤
        lowerConcreteM R a slack d / (lowerConcreteN d : ℝ) := by
    apply (le_div_iff₀ hNpos).mpr
    have hS_nonneg : 0 ≤ ((R.sample d - 1 : ℕ) : ℝ) := by positivity
    have hd2_nonneg : 0 ≤ (d : ℝ) ^ 2 := by positivity
    have hfactor :
        256 * ((R.sample d - 1 : ℕ) : ℝ) *
            (lowerConcreteN d : ℝ) ≤
          ((2 + 128 * ((d : ℝ) ^ 2 + 1)) *
              ((R.sample d - 1 : ℕ) : ℝ) / (1 / 2 : ℝ)) := by
      simp [lowerConcreteN, Nat.cast_pow]
      nlinarith [hS_nonneg, hd2_nonneg]
    exact le_trans hfactor hmain
  nlinarith [hB_le_n, hsubR, hratio_sample]

/-- The runtime background coefficient is not an `o(1)` scalar.

This is the formal obstruction behind the fixed-`M` mixed-domination warning:
the current favourable background event uses a threshold whose normalized
coefficient `lowerConcreteM / lowerConcreteN` is eventually at least `256`.
Thus it cannot be treated as an eventually arbitrarily small PT edge
coefficient. -/
theorem lowerConcreteM_div_lowerConcreteN_not_eventuallySmall
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (a slack : ℝ) :
    ¬ (∀ η : ℝ, 0 < η →
        ∀ᶠ d : ℕ in atTop,
          lowerConcreteM R a slack d / (lowerConcreteN d : ℝ) ≤ η) := by
  intro hsmall
  have hle_one := hsmall 1 (by norm_num)
  have hge_256 := lowerConcreteM_div_lowerConcreteN_eventually_ge_const R a slack
  have hfalse : ∀ᶠ _d : ℕ in atTop, False := by
    filter_upwards [hle_one, hge_256] with d hle hge
    linarith
  simp only [Filter.Eventually, Set.setOf_false] at hfalse
  have hbot : (∅ : Set ℕ) ∈ (atTop : Filter ℕ) := hfalse
  have hne : (atTop : Filter ℕ).NeBot := inferInstance
  exact hne.ne ((Filter.empty_mem_iff_bot).mp hbot)

/-- Sharper version of the previous ratio diagnostic: the runtime background
coefficient `lowerConcreteM / N` already dominates the deleted-column sample
dimension, up to a fixed factor.

This pins the mixed obstruction to the concrete Gaussian tail threshold: in a
balanced regime the right-hand side grows with the sample count, so it is not
the fixed PT edge coefficient expected by `lowerPartialTransposeMixedWordBoundD`.
-/
theorem lowerConcreteM_div_lowerConcreteN_eventually_ge_sample
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (a slack : ℝ) :
    ∀ᶠ d : ℕ in atTop,
      256 * ((R.sample d - 1 : ℕ) : ℝ) ≤
        lowerConcreteM R a slack d / (lowerConcreteN d : ℝ) := by
  filter_upwards [eventually_gt_atTop 0,
    lower_concrete_eventually_two_le_sample R] with d hd hs2
  have hspos : 0 < R.sample d := by omega
  have hmain :=
    lowerConcreteM_ge_deletedColumn_gammaThreshold_explicit
      (R := R) (a := a) (slack := slack) (d := d) hspos
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hNpos : 0 < (lowerConcreteN d : ℝ) := by
    simp [lowerConcreteN, pow_two, mul_pos hdR hdR]
  have hs_sub_nonneg :
      0 ≤ ((R.sample d - 1 : ℕ) : ℝ) := by positivity
  have hfactor :
      256 * ((R.sample d - 1 : ℕ) : ℝ) *
          (lowerConcreteN d : ℝ) ≤
        ((2 + 128 * ((d : ℝ) ^ 2 + 1)) *
          ((R.sample d - 1 : ℕ) : ℝ) / (1 / 2 : ℝ)) := by
    simp [lowerConcreteN, Nat.cast_pow]
    nlinarith [sq_nonneg (d : ℝ), hs_sub_nonneg]
  exact (le_div_iff₀ hNpos).mpr (le_trans hfactor hmain)

/-- The favourable event already supplies the sharp runtime word-by-word mixed
bound.

This closes the local deterministic analytic step: every mixed word is bounded
either by the one-`Q` cyclic estimate, by the many-`Q` split estimate, or is
zero because it contains an `L`. What remains afterwards is only the separate
task of comparing this runtime envelope to a smaller endpoint-facing scalar
budget. -/
theorem lowerConcreteMixedWordPointwiseBoundOnSphere_runtimeEnvelope
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε) :
    lowerConcreteMixedWordPointwiseBoundOnSphere R k ε
      (lowerConcreteMixedRuntimeWordBound R k) := by
  intro a ha slack hslack
  have hk : 1 ≤ k := by omega
  have hk0 : 0 < k := Nat.zero_lt_of_lt hk
  filter_upwards [eventually_gt_atTop 0,
      lower_concrete_hBetaScalePos (k := k) hk0 (ε := ε) hε a ha slack hslack]
    with d hd hq0pos
  intro hs X hFav hSphere w hmix
  let N : ℝ := lowerConcreteN d
  let M : ℝ := lowerConcreteM R a slack d
  let S : ℝ :=
    betaColumnIntervalUpper
      (betaColumnSpikeScale N (spikeSpeed k d) a)
      (lowerConcreteDelta a slack d)
  let A :=
    columnBackgroundMatrix
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      X (⟨0, hs⟩ : Fin (R.sample d))
  let Q :=
    columnSpikeMatrix
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      X (⟨0, hs⟩ : Fin (R.sample d))
  by_cases hL : ∃ i : Fin k, w i = LocalExpansionLetter.L
  · have hzero :
        localWordScaledTraceTerm (p := Fin d) (q := Fin d) N A 0 Q w = 0 :=
      lower_localWordScaledTraceTerm_zero_of_exists_L
        (p := Fin d) (q := Fin d) (N := N) A Q w hL
    have hLpos :
        0 < localWordLetterCount LocalExpansionLetter.L w :=
      lower_localWordLetterCount_pos_of_exists
        (letter := LocalExpansionLetter.L) (w := w) hL
    have hLne :
        localWordLetterCount LocalExpansionLetter.L w ≠ 0 := by
      omega
    have hrhs :
        lowerConcreteMixedRuntimeWordBound R k a slack d w = 0 := by
      unfold lowerConcreteMixedRuntimeWordBound
      simp [hLne]
    rw [hrhs]
    rw [hzero]
    simp
  · have hNoL : ∀ i : Fin k, w i ≠ LocalExpansionLetter.L := by
        intro i hi
        exact hL ⟨i, hi⟩
    have hL0 :
        localWordLetterCount LocalExpansionLetter.L w = 0 :=
      lower_localWordLetterCount_zero_of_forall_ne
        (letter := LocalExpansionLetter.L) hNoL
    have hQrange :=
      lower_localWord_mixed_noL_Q_count_range
        (k := k) (w := w) hmix hNoL
    have hN_nonneg : 0 ≤ N := by
      dsimp [N, lowerConcreteN]
      positivity
    have hBgOp :
        opNorm (p := Fin d) (q := Fin d) A ≤ M / N := by
      simpa [A, M, N] using
        (lower_sphericalOneColumnFavorableEvent_columnBackgroundMatrix_opNorm_bound
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (α₀ := (⟨0, hs⟩ : Fin (R.sample d)))
          (q₀ := betaColumnSpikeScale N (spikeSpeed k d) a)
          (δ := lowerConcreteDelta a slack d)
          (N := N) (M := M)
          (τ := lowerConcreteTau a slack d)
          (mean := lowerConcreteDeletedBackgroundMean R k d)
          (k := k)
          (directionSet := lowerConcreteDirectionCapSet
            lowerConcreteCanonicalDirection a slack d)
          hFav hSphere)
    have hBgFrob :
        frobeniusNorm (p := Fin d) (q := Fin d) (σ := BipIndex (Fin d) (Fin d)) A ≤
          M / Real.sqrt N := by
      simpa [A, M, N] using
        (lower_sphericalOneColumnFavorableEvent_columnBackgroundMatrix_frobeniusNorm_bound
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (α₀ := (⟨0, hs⟩ : Fin (R.sample d)))
          (q₀ := betaColumnSpikeScale N (spikeSpeed k d) a)
          (δ := lowerConcreteDelta a slack d)
          (N := N) (M := M)
          (τ := lowerConcreteTau a slack d)
          (mean := lowerConcreteDeletedBackgroundMean R k d)
          (k := k)
          (directionSet := lowerConcreteDirectionCapSet
            lowerConcreteCanonicalDirection a slack d)
          hFav hSphere)
    have hQFrob :
        frobeniusNorm (p := Fin d) (q := Fin d) (σ := BipIndex (Fin d) (Fin d)) Q ≤ S := by
      simpa [Q, S, N] using
        (lower_sphericalOneColumnFavorableEvent_columnSpikeMatrix_frobeniusNorm_le_intervalUpper
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (α₀ := (⟨0, hs⟩ : Fin (R.sample d)))
          (q₀ := betaColumnSpikeScale N (spikeSpeed k d) a)
          (δ := lowerConcreteDelta a slack d)
          (directionSet := lowerConcreteDirectionCapSet
            lowerConcreteCanonicalDirection a slack d)
          (backgroundSet := backgroundTypicalSet
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            N M (lowerConcreteTau a slack d)
            (lowerConcreteDeletedBackgroundMean R k d) k)
          hq0pos hFav)
    have hQOp :
        opNorm (p := Fin d) (q := Fin d) Q ≤ S := by
      simpa [Q, S, N] using
        (lower_sphericalOneColumnFavorableEvent_columnSpikeMatrix_opNorm_le_intervalUpper
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (α₀ := (⟨0, hs⟩ : Fin (R.sample d)))
          (q₀ := betaColumnSpikeScale N (spikeSpeed k d) a)
          (δ := lowerConcreteDelta a slack d)
          (directionSet := lowerConcreteDirectionCapSet
            lowerConcreteCanonicalDirection a slack d)
          (backgroundSet := backgroundTypicalSet
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            N M (lowerConcreteTau a slack d)
            (lowerConcreteDeletedBackgroundMean R k d) k)
          hq0pos hFav)
    by_cases hQ1 :
        localWordLetterCount LocalExpansionLetter.Q w = 1
    · have hOne :=
          lower_localWordScaledTraceTerm_oneQ_noL_bound
            (p := Fin d) (q := Fin d)
            (N := N) (M := M) (Sbound := S)
            (A := A) (Q := Q) (w := w)
            hN_nonneg hk3
            (le_trans (by
              unfold opNorm
              positivity) hQOp)
            hQFrob hBgOp hBgFrob hNoL hQ1
      have hrhs :
          lowerConcreteMixedRuntimeWordBound R k a slack d w =
            N ^ (k - 1) * (S * ((M / N) ^ (k - 2) * (M / Real.sqrt N))) := by
        unfold lowerConcreteMixedRuntimeWordBound
        simp [N, M, S, hL0, hQ1]
      rw [hrhs]
      exact hOne
    · have hQtwo :
          2 ≤ localWordLetterCount LocalExpansionLetter.Q w := by
        omega
      have hMdivN_nonneg : 0 ≤ M / N := by
        exact le_trans (by
          unfold opNorm
          positivity) hBgOp
      have hS_nonneg : 0 ≤ S := by
        exact le_trans (by
          unfold opNorm
          positivity) hQOp
      have hkpred : (k - 1) + 1 = k := by
        omega
      have hNoL_cast :
          ∀ i : Fin ((k - 1) + 1),
            (w ∘ Fin.cast hkpred) i ≠ LocalExpansionLetter.L := by
        intro i hi
        exact hNoL (Fin.cast hkpred i) hi
      have hQtwo_cast :
          2 ≤ localWordLetterCount LocalExpansionLetter.Q (w ∘ Fin.cast hkpred) := by
        simpa [lower_localWordLetterCount_cast, hkpred] using hQtwo
      have hMany_raw :=
        lower_localWordScaledTraceTerm_manyQ_noL_bound
          (p := Fin d) (q := Fin d)
          (N := N) (M := M) (Sbound := S) (m := k - 1)
          (A := A) (Q := Q) (w := w ∘ Fin.cast hkpred)
          hN_nonneg hMdivN_nonneg hS_nonneg
          hBgOp hQOp hQFrob hNoL_cast hQtwo_cast
      have hMany := hMany_raw
      rw [lower_localWordScaledTraceTerm_cast
          (p := Fin d) (q := Fin d) (N := N) A 0 Q hkpred w] at hMany
      have hMany_final :
          |localWordScaledTraceTerm (p := Fin d) (q := Fin d) N A 0 Q w| ≤
            N ^ (k - 1) *
              ((M / N) ^ localWordLetterCount LocalExpansionLetter.A w *
                S ^ localWordLetterCount LocalExpansionLetter.Q w) := by
        simpa [lower_localWordLetterCount_cast, hkpred] using hMany
      have hrhs :
          lowerConcreteMixedRuntimeWordBound R k a slack d w =
            N ^ (k - 1) *
              ((M / N) ^ localWordLetterCount LocalExpansionLetter.A w *
                S ^ localWordLetterCount LocalExpansionLetter.Q w) := by
        unfold lowerConcreteMixedRuntimeWordBound
        simp [N, M, S, hL0, hQ1, hQtwo]
      rw [hrhs]
      exact hMany_final

/-- If the concrete runtime word envelope is eventually dominated by a cleaner
bound, then the pointwise mixed-word frontier closes for that cleaner bound. -/
theorem lowerConcreteMixedWordPointwiseBoundOnSphere_of_runtimeEnvelope_domination
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ}
    {bound : ℝ → ℝ → ℕ → (Fin k → LocalExpansionLetter) → ℝ}
    (hRuntime :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k ε
        (lowerConcreteMixedRuntimeWordBound R k))
    (hDom :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ w : Fin k → LocalExpansionLetter,
              lowerConcreteMixedRuntimeWordBound R k a slack d w ≤
                bound a slack d w) :
    lowerConcreteMixedWordPointwiseBoundOnSphere R k ε bound := by
  intro a ha slack hslack
  filter_upwards [hRuntime a ha slack hslack, hDom a ha slack hslack]
    with d hRuntime_d hDom_d
  intro hs X hFav hSphere w hmix
  exact le_trans (hRuntime_d hs X hFav hSphere w hmix) (hDom_d w)

/-- Mixed-only version of
`lowerConcreteMixedWordPointwiseBoundOnSphere_of_runtimeEnvelope_domination`.

This is the sharper form actually needed by the local-expansion remainder:
pure background and pure spike words are filtered out before the mixed budget is
formed, so the runtime-to-clean-envelope comparison only has to hold on
`localWordIsMixed` words. -/
theorem lowerConcreteMixedWordPointwiseBoundOnSphere_of_runtimeEnvelope_domination_on_mixed
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ}
    {bound : ℝ → ℝ → ℕ → (Fin k → LocalExpansionLetter) → ℝ}
    (hRuntime :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k ε
        (lowerConcreteMixedRuntimeWordBound R k))
    (hDom :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                lowerConcreteMixedRuntimeWordBound R k a slack d w ≤
                  bound a slack d w) :
    lowerConcreteMixedWordPointwiseBoundOnSphere R k ε bound := by
  intro a ha slack hslack
  filter_upwards [hRuntime a ha slack hslack, hDom a ha slack hslack]
    with d hRuntime_d hDom_d
  intro hs X hFav hSphere w hmix
  exact le_trans (hRuntime_d hs X hFav hSphere w hmix) (hDom_d w hmix)

/-- Scalar budget assigning the mixed-word finite sum to the concrete
mixed-error sequence. -/
def lowerConcreteMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (ε : ℝ)
    (bound : ℝ → ℝ → ℕ → (Fin k → LocalExpansionLetter) → ℝ) : Prop :=
  ∀ a : ℝ, spikeRoot k ε < a →
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        localMixedWordFilteredSum (k := k) (bound a slack d) ≤
          lowerConcreteMixedError R k ε a slack d

/-- Scalar budget assigning the finite mixed-word sum to an explicit mixed
error sequence. -/
def lowerConcreteMixedWordBudgetWithError
    (_R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (ε : ℝ)
    (bound : ℝ → ℝ → ℕ → (Fin k → LocalExpansionLetter) → ℝ)
    (errMix : ℝ → ℝ → ℕ → ℝ) : Prop :=
  ∀ a : ℝ, spikeRoot k ε < a →
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        localMixedWordFilteredSum (k := k) (bound a slack d) ≤
          errMix a slack d

/-- The exact finite mixed-word sum satisfies the explicit mixed budget
predicate by reflexivity.

This removes a bookkeeping input whenever the selected mixed error is exactly
the finite filtered word sum attached to the pointwise word bound. -/
theorem lowerConcreteMixedWordBudgetWithExactSum
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (ε : ℝ)
    (bound : ℝ → ℝ → ℕ → (Fin k → LocalExpansionLetter) → ℝ) :
    lowerConcreteMixedWordBudgetWithError R k ε bound
      (fun a slack d => localMixedWordFilteredSum (k := k) (bound a slack d)) := by
  intro a _ha slack _hslack
  exact Filter.Eventually.of_forall (fun _d => le_rfl)

/-! ### Literal PT mixed-word budget aggregation -/

/-- No-`L` two-letter words with exactly `j` spike letters are the same data as
choosing the `j` spike positions. -/
noncomputable def lowerNoLQCountWordsEquiv (k j : ℕ) :
    { w : Fin k → LocalExpansionLetter //
      localWordLetterCount LocalExpansionLetter.L w = 0 ∧
      localWordLetterCount LocalExpansionLetter.Q w = j } ≃
    { s : Finset (Fin k) // s.card = j } := by
  classical
  exact
    { toFun := fun w => by
        refine ⟨Finset.univ.filter
          (fun i : Fin k => w.1 i = LocalExpansionLetter.Q), ?_⟩
        have hcard :=
          Finset.card_filter
            (fun i : Fin k => w.1 i = LocalExpansionLetter.Q) Finset.univ
        have hcount :
            localWordLetterCount LocalExpansionLetter.Q w.1 =
              (Finset.univ.filter
                (fun i : Fin k => w.1 i = LocalExpansionLetter.Q)).card := by
          unfold localWordLetterCount
          exact hcard.symm
        rw [← hcount]
        exact w.2.2
      invFun := fun s => by
        refine
          ⟨(fun i : Fin k =>
              if i ∈ s.1 then LocalExpansionLetter.Q else LocalExpansionLetter.A),
            ?_⟩
        constructor
        · exact
            lower_localWordLetterCount_zero_of_forall_ne
              (letter := LocalExpansionLetter.L) (by
                intro i
                by_cases hi : i ∈ s.1 <;> simp [hi])
        · unfold localWordLetterCount
          have hsum :
              (∑ i : Fin k,
                if (if i ∈ s.1 then
                      LocalExpansionLetter.Q
                    else
                      LocalExpansionLetter.A) = LocalExpansionLetter.Q
                then 1 else 0) =
                ∑ i : Fin k, if i ∈ s.1 then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro i _
            by_cases hi : i ∈ s.1 <;> simp [hi]
          rw [hsum]
          have hcard :=
            Finset.card_filter (fun i : Fin k => i ∈ s.1) Finset.univ
          have hfilter :
              Finset.univ.filter (fun i : Fin k => i ∈ s.1) = s.1 := by
            ext i
            simp
          rw [← hcard, hfilter]
          exact s.2
      left_inv := by
        intro w
        ext i
        by_cases hq : w.1 i = LocalExpansionLetter.Q
        · simp [hq]
        · have hNoL : w.1 i ≠ LocalExpansionLetter.L := by
            intro hL
            have hpos :
                0 < localWordLetterCount LocalExpansionLetter.L w.1 :=
              lower_localWordLetterCount_pos_of_exists
                (letter := LocalExpansionLetter.L) (w := w.1) ⟨i, hL⟩
            omega
          cases hw : w.1 i with
          | A => simp [hq]
          | L => exact False.elim (hNoL hw)
          | Q => exact False.elim (hq hw)
      right_inv := by
        intro s
        ext i
        simp }

/-- The literal binomial fiber count for no-`L` words with exactly `j` spike
letters. This is the finite combinatorics behind the PT mixed budget; no
Catalan counting is involved. -/
theorem card_words_noL_countQ_eq_choose (k j : ℕ) :
    Fintype.card
      { w : Fin k → LocalExpansionLetter //
        localWordLetterCount LocalExpansionLetter.L w = 0 ∧
        localWordLetterCount LocalExpansionLetter.Q w = j } =
      Nat.choose k j := by
  classical
  calc
    Fintype.card
      { w : Fin k → LocalExpansionLetter //
        localWordLetterCount LocalExpansionLetter.L w = 0 ∧
        localWordLetterCount LocalExpansionLetter.Q w = j }
        = Fintype.card { s : Finset (Fin k) // s.card = j } :=
            Fintype.card_congr (lowerNoLQCountWordsEquiv k j)
    _ = Nat.choose k j := by
          rw [Fintype.card_finset_len]
          simp [Fintype.card_fin]

/-- Indicator for one coefficient-budget fiber: no linear letters and exactly
`j` spike letters. -/
noncomputable def lowerNoLQCountIndicator
    (k j : ℕ) (x : ℝ) (w : Fin k → LocalExpansionLetter) : ℝ := by
  classical
  exact
    if localWordLetterCount LocalExpansionLetter.L w = 0 ∧
        localWordLetterCount LocalExpansionLetter.Q w = j then
      x
    else
      0

/-- Summing a constant over the no-`L`, `#Q = j` fiber gives the binomial
coefficient times that constant. -/
theorem lowerNoLQCountIndicator_sum (k j : ℕ) (x : ℝ) :
    (∑ w : Fin k → LocalExpansionLetter,
      lowerNoLQCountIndicator k j x w) =
      (Nat.choose k j : ℝ) * x := by
  classical
  unfold lowerNoLQCountIndicator
  rw [← Finset.sum_filter]
  rw [Finset.sum_const]
  rw [nsmul_eq_mul]
  have hcard :
      (Finset.univ.filter
        (fun w : Fin k → LocalExpansionLetter =>
          localWordLetterCount LocalExpansionLetter.L w = 0 ∧
            localWordLetterCount LocalExpansionLetter.Q w = j)).card =
        Nat.choose k j := by
    have hsub :=
      Fintype.card_subtype
        (fun w : Fin k → LocalExpansionLetter =>
          localWordLetterCount LocalExpansionLetter.L w = 0 ∧
            localWordLetterCount LocalExpansionLetter.Q w = j)
    rw [← hsub]
    exact card_words_noL_countQ_eq_choose k j
  rw [hcard]

theorem lowerNoLQCountIndicator_nonneg
    {k j : ℕ} {x : ℝ} (hx : 0 ≤ x)
    (w : Fin k → LocalExpansionLetter) :
    0 ≤ lowerNoLQCountIndicator k j x w := by
  classical
  unfold lowerNoLQCountIndicator
  by_cases h :
      localWordLetterCount LocalExpansionLetter.L w = 0 ∧
        localWordLetterCount LocalExpansionLetter.Q w = j
  · simp [h, hx]
  · simp [h]

/-- On its own no-`L`, exact-`#Q` fiber, the indicator is the supplied
constant. -/
theorem lowerNoLQCountIndicator_eq_of_counts
    {k j : ℕ} {x : ℝ} {w : Fin k → LocalExpansionLetter}
    (hL0 : localWordLetterCount LocalExpansionLetter.L w = 0)
    (hQj : localWordLetterCount LocalExpansionLetter.Q w = j) :
    lowerNoLQCountIndicator k j x w = x := by
  classical
  unfold lowerNoLQCountIndicator
  simp [hL0, hQj]

/-- Off its exact-`#Q` fiber, the no-`L`/`#Q` indicator is zero. -/
theorem lowerNoLQCountIndicator_eq_zero_of_q_ne
    {k j : ℕ} {x : ℝ} {w : Fin k → LocalExpansionLetter}
    (hQne : localWordLetterCount LocalExpansionLetter.Q w ≠ j) :
    lowerNoLQCountIndicator k j x w = 0 := by
  classical
  unfold lowerNoLQCountIndicator
  simp [hQne]

/-- Literal PT word-budget envelope. The first summand is the one-`Q` fiber;
the finite sum is the many-`Q` fiber budget with the corrected PT powers. -/
noncomputable def lowerPartialTransposeMixedWordBoundN
    (k : ℕ) (A M N : ℝ) (w : Fin k → LocalExpansionLetter) : ℝ :=
  lowerNoLQCountIndicator k 1
      (A * M ^ (k - 1) * N ^ ((-1 / 2 : ℝ) + 1 / (k : ℝ))) w +
    (Finset.Icc 2 (k - 1)).sum (fun j =>
      lowerNoLQCountIndicator k j
        (A ^ j * M ^ (k - j) * N ^ ((j : ℝ) / (k : ℝ) - 1)) w)

theorem lowerPartialTransposeMixedWordBoundN_nonneg
    {k : ℕ} {A M N : ℝ}
    (hA : 0 ≤ A) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (w : Fin k → LocalExpansionLetter) :
    0 ≤ lowerPartialTransposeMixedWordBoundN k A M N w := by
  classical
  unfold lowerPartialTransposeMixedWordBoundN
  apply add_nonneg
  · exact lowerNoLQCountIndicator_nonneg (by positivity) w
  · apply Finset.sum_nonneg
    intro j _
    exact lowerNoLQCountIndicator_nonneg (by positivity) w

/-- The literal fiberwise PT word budget sums exactly to
`lowerPartialTransposeMixedErrorN`. -/
theorem lowerPartialTransposeMixedWordBoundN_sum
    (k : ℕ) (A M N : ℝ) :
    (∑ w : Fin k → LocalExpansionLetter,
      lowerPartialTransposeMixedWordBoundN k A M N w) =
      lowerPartialTransposeMixedErrorN k A M N := by
  classical
  unfold lowerPartialTransposeMixedWordBoundN lowerPartialTransposeMixedErrorN
  rw [Finset.sum_add_distrib]
  rw [lowerNoLQCountIndicator_sum]
  rw [Finset.sum_comm]
  simp_rw [lowerNoLQCountIndicator_sum]
  simp [Nat.choose_one_right, div_eq_mul_inv]
  ring_nf

/-- Aggregating the literal word fibers gives the corrected PT mixed error. -/
theorem lowerPartialTransposeMixedWordBoundN_budget
    {k : ℕ} {A M N : ℝ}
    (hA : 0 ≤ A) (hM : 0 ≤ M) (hN : 0 ≤ N) :
    localMixedWordFilteredSum (k := k)
        (lowerPartialTransposeMixedWordBoundN k A M N) ≤
      lowerPartialTransposeMixedErrorN k A M N := by
  classical
  unfold localMixedWordFilteredSum
  calc
    (∑ w : Fin k → LocalExpansionLetter,
      if localWordIsMixed w then
        lowerPartialTransposeMixedWordBoundN k A M N w
      else
        0)
        ≤ ∑ w : Fin k → LocalExpansionLetter,
            lowerPartialTransposeMixedWordBoundN k A M N w := by
          apply Finset.sum_le_sum
          intro w _
          by_cases hw : localWordIsMixed w
          · simp [hw]
          · simp [hw, lowerPartialTransposeMixedWordBoundN_nonneg hA hM hN w]
    _ = lowerPartialTransposeMixedErrorN k A M N :=
          lowerPartialTransposeMixedWordBoundN_sum k A M N

/-- The same literal PT word-budget envelope in concrete `d` variables. -/
noncomputable def lowerPartialTransposeMixedWordBoundD
    (k : ℕ) (A M : ℝ) (d : ℕ)
    (w : Fin k → LocalExpansionLetter) : ℝ :=
  lowerPartialTransposeMixedWordBoundN k A M ((d : ℝ) ^ 2) w

/-- The concrete `d`-variable PT word-budget envelope is nonnegative for
nonnegative scalar parameters. -/
theorem lowerPartialTransposeMixedWordBoundD_nonneg
    {k d : ℕ} {A M : ℝ}
    (hA : 0 ≤ A) (hM : 0 ≤ M)
    (w : Fin k → LocalExpansionLetter) :
    0 ≤ lowerPartialTransposeMixedWordBoundD k A M d w := by
  unfold lowerPartialTransposeMixedWordBoundD
  exact
    lowerPartialTransposeMixedWordBoundN_nonneg
      (k := k) (A := A) (M := M) (N := (d : ℝ) ^ 2)
      hA hM (by positivity) w

/-- On the no-`L`, exactly-one-`Q` fiber, the literal PT word envelope
dominates the one-`Q` scalar term. -/
theorem lowerPartialTransposeMixedWordBoundD_oneQ_term_le
    {k d : ℕ} {A M : ℝ} {w : Fin k → LocalExpansionLetter}
    (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hL0 : localWordLetterCount LocalExpansionLetter.L w = 0)
    (hQ1 : localWordLetterCount LocalExpansionLetter.Q w = 1) :
    A * M ^ (k - 1) * ((d : ℝ) ^ 2) ^ ((-1 / 2 : ℝ) + 1 / (k : ℝ)) ≤
      lowerPartialTransposeMixedWordBoundD k A M d w := by
  classical
  unfold lowerPartialTransposeMixedWordBoundD lowerPartialTransposeMixedWordBoundN
  rw [lowerNoLQCountIndicator_eq_of_counts (k := k) (j := 1)
    (x := A * M ^ (k - 1) * ((d : ℝ) ^ 2) ^ ((-1 / 2 : ℝ) + 1 / (k : ℝ)))
    (w := w) hL0 hQ1]
  exact le_add_of_nonneg_right (by
    apply Finset.sum_nonneg
    intro j _hj
    exact lowerNoLQCountIndicator_nonneg (by positivity) w)

/-- On a no-`L`, exact-`j` many-`Q` fiber, the literal PT word envelope
dominates the corresponding many-`Q` scalar term. -/
theorem lowerPartialTransposeMixedWordBoundD_manyQ_term_le
    {k d j : ℕ} {A M : ℝ} {w : Fin k → LocalExpansionLetter}
    (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hj : j ∈ Finset.Icc 2 (k - 1))
    (hL0 : localWordLetterCount LocalExpansionLetter.L w = 0)
    (hQj : localWordLetterCount LocalExpansionLetter.Q w = j) :
    A ^ j * M ^ (k - j) * ((d : ℝ) ^ 2) ^ ((j : ℝ) / (k : ℝ) - 1) ≤
      lowerPartialTransposeMixedWordBoundD k A M d w := by
  classical
  unfold lowerPartialTransposeMixedWordBoundD lowerPartialTransposeMixedWordBoundN
  have hjge : 2 ≤ j := (Finset.mem_Icc.mp hj).1
  have hQne1 : localWordLetterCount LocalExpansionLetter.Q w ≠ 1 := by
    rw [hQj]
    omega
  rw [lowerNoLQCountIndicator_eq_zero_of_q_ne (k := k) (j := 1)
    (x := A * M ^ (k - 1) * ((d : ℝ) ^ 2) ^ ((-1 / 2 : ℝ) + 1 / (k : ℝ)))
    (w := w) hQne1]
  simp only [zero_add]
  let f : ℕ → ℝ := fun i =>
    lowerNoLQCountIndicator k i
      (A ^ i * M ^ (k - i) * ((d : ℝ) ^ 2) ^ ((i : ℝ) / (k : ℝ) - 1)) w
  have hfj :
      f j =
        A ^ j * M ^ (k - j) *
          ((d : ℝ) ^ 2) ^ ((j : ℝ) / (k : ℝ) - 1) := by
    dsimp [f]
    exact lowerNoLQCountIndicator_eq_of_counts hL0 hQj
  rw [← hfj]
  exact Finset.single_le_sum
    (fun i _hi => by
      dsimp [f]
      exact lowerNoLQCountIndicator_nonneg (by positivity) w)
    hj

/-- Direct one-`Q` scalar leaf for the literal PT mixed-word envelope.

This is the theorem-strength estimate that remains after the local word has no
`L` letters and exactly one `Q` letter.  It is stated directly in terms of the
actual local trace word, not through the runtime envelope. -/
def lowerConcretePTMixedWordOneQDirectScalarBound
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (ε M : ℝ) : Prop :=
  ∀ a : ℝ, spikeRoot k ε < a →
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        ∀ hs : 0 < R.sample d,
          ∀ X : SampleMatrix (Fin d) (Fin d) (Fin (R.sample d)),
            X ∈
              sphericalOneColumnFavorableEvent
                (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                (⟨0, hs⟩ : Fin (R.sample d))
                (betaColumnSpikeScale
                  (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                (lowerConcreteDelta a slack d)
                (lowerConcreteDirectionCapSet
                  lowerConcreteCanonicalDirection a slack d)
                (backgroundTypicalSet
                  (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                  (lowerConcreteN d) (lowerConcreteM R a slack d)
                  (lowerConcreteTau a slack d)
                  (lowerConcreteDeletedBackgroundMean R k d) k) →
            frobeniusNorm (p := Fin d) (q := Fin d)
                (σ := Fin (R.sample d)) X = 1 →
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                localWordLetterCount LocalExpansionLetter.L w = 0 →
                  localWordLetterCount LocalExpansionLetter.Q w = 1 →
                    |localWordScaledTraceTerm (p := Fin d) (q := Fin d)
                        (lowerConcreteN d)
                        (columnBackgroundMatrix
                          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                          X (⟨0, hs⟩ : Fin (R.sample d)))
                        0
                        (columnSpikeMatrix
                          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                          X (⟨0, hs⟩ : Fin (R.sample d)))
                        w| ≤
                      (a + slack) * M ^ (k - 1) *
                        ((d : ℝ) ^ 2) ^ ((-1 / 2 : ℝ) + 1 / (k : ℝ))

/-- Scalar comparison sufficient for the direct one-`Q` mixed-word leaf.

This is the exact scale inequality left after applying the closed local
one-spike trace estimate to the current concrete favourable event.  It is kept
separate because this comparison is where the current background threshold
`lowerConcreteM` meets the fixed PT envelope parameter `M`. -/
def lowerConcretePTMixedWordOneQScaleComparison
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (ε M : ℝ) : Prop :=
  ∀ a : ℝ, spikeRoot k ε < a →
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        (lowerConcreteN d : ℝ) ^ (k - 1) *
          (betaColumnIntervalUpper
              (betaColumnSpikeScale
                (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
              (lowerConcreteDelta a slack d) *
            (((lowerConcreteM R a slack d) / (lowerConcreteN d : ℝ)) ^
                (k - 2) *
              ((lowerConcreteM R a slack d) /
                Real.sqrt (lowerConcreteN d : ℝ)))) ≤
          (a + slack) * M ^ (k - 1) *
            ((d : ℝ) ^ 2) ^ ((-1 / 2 : ℝ) + 1 / (k : ℝ))

/-- Close the direct one-`Q` mixed-word leaf from the local trace estimate plus
the scalar scale comparison.

The local analytic part is already proved by
`lower_localWordScaledTraceTerm_oneQ_noL_bound`; the only remaining ingredient
is the scalar comparison packaged as
`lowerConcretePTMixedWordOneQScaleComparison`. -/
theorem lowerConcretePTMixedWordOneQDirectScalarBound_of_scaleComparison
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε M : ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hScale : lowerConcretePTMixedWordOneQScaleComparison R k ε M) :
    lowerConcretePTMixedWordOneQDirectScalarBound R k ε M := by
  intro a ha slack hslack
  have hk : 1 ≤ k := by omega
  have hk0 : 0 < k := Nat.zero_lt_of_lt hk
  filter_upwards [eventually_gt_atTop 0,
      lower_concrete_hBetaScalePos (k := k) hk0 (ε := ε) hε a ha slack hslack,
      hScale a ha slack hslack]
    with d hd hq0pos hScale_d
  intro hs X hFav hSphere w _hmix hL0 hQ1
  let N : ℝ := lowerConcreteN d
  let Mbg : ℝ := lowerConcreteM R a slack d
  let S : ℝ :=
    betaColumnIntervalUpper
      (betaColumnSpikeScale N (spikeSpeed k d) a)
      (lowerConcreteDelta a slack d)
  let A :=
    columnBackgroundMatrix
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      X (⟨0, hs⟩ : Fin (R.sample d))
  let Q :=
    columnSpikeMatrix
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      X (⟨0, hs⟩ : Fin (R.sample d))
  have hN_nonneg : 0 ≤ N := by
    dsimp [N, lowerConcreteN]
    positivity
  have hNoL : ∀ i : Fin k, w i ≠ LocalExpansionLetter.L := by
    intro i hi
    have hpos :
        0 < localWordLetterCount LocalExpansionLetter.L w :=
      lower_localWordLetterCount_pos_of_exists
        (letter := LocalExpansionLetter.L) (w := w) ⟨i, hi⟩
    omega
  have hBgOp :
      opNorm (p := Fin d) (q := Fin d) A ≤ Mbg / N := by
    simpa [A, Mbg, N] using
      (lower_sphericalOneColumnFavorableEvent_columnBackgroundMatrix_opNorm_bound
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        (α₀ := (⟨0, hs⟩ : Fin (R.sample d)))
        (q₀ := betaColumnSpikeScale N (spikeSpeed k d) a)
        (δ := lowerConcreteDelta a slack d)
        (N := N) (M := Mbg)
        (τ := lowerConcreteTau a slack d)
        (mean := lowerConcreteDeletedBackgroundMean R k d)
        (k := k)
        (directionSet := lowerConcreteDirectionCapSet
          lowerConcreteCanonicalDirection a slack d)
        hFav hSphere)
  have hBgFrob :
      frobeniusNorm (p := Fin d) (q := Fin d)
          (σ := BipIndex (Fin d) (Fin d)) A ≤
        Mbg / Real.sqrt N := by
    simpa [A, Mbg, N] using
      (lower_sphericalOneColumnFavorableEvent_columnBackgroundMatrix_frobeniusNorm_bound
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        (α₀ := (⟨0, hs⟩ : Fin (R.sample d)))
        (q₀ := betaColumnSpikeScale N (spikeSpeed k d) a)
        (δ := lowerConcreteDelta a slack d)
        (N := N) (M := Mbg)
        (τ := lowerConcreteTau a slack d)
        (mean := lowerConcreteDeletedBackgroundMean R k d)
        (k := k)
        (directionSet := lowerConcreteDirectionCapSet
          lowerConcreteCanonicalDirection a slack d)
        hFav hSphere)
  have hQFrob :
      frobeniusNorm (p := Fin d) (q := Fin d)
          (σ := BipIndex (Fin d) (Fin d)) Q ≤ S := by
    simpa [Q, S, N] using
      (lower_sphericalOneColumnFavorableEvent_columnSpikeMatrix_frobeniusNorm_le_intervalUpper
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        (α₀ := (⟨0, hs⟩ : Fin (R.sample d)))
        (q₀ := betaColumnSpikeScale N (spikeSpeed k d) a)
        (δ := lowerConcreteDelta a slack d)
        (directionSet := lowerConcreteDirectionCapSet
          lowerConcreteCanonicalDirection a slack d)
        (backgroundSet := backgroundTypicalSet
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          N Mbg (lowerConcreteTau a slack d)
          (lowerConcreteDeletedBackgroundMean R k d) k)
        hq0pos hFav)
  have hQOp :
      opNorm (p := Fin d) (q := Fin d) Q ≤ S := by
    simpa [Q, S, N] using
      (lower_sphericalOneColumnFavorableEvent_columnSpikeMatrix_opNorm_le_intervalUpper
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        (α₀ := (⟨0, hs⟩ : Fin (R.sample d)))
        (q₀ := betaColumnSpikeScale N (spikeSpeed k d) a)
        (δ := lowerConcreteDelta a slack d)
        (directionSet := lowerConcreteDirectionCapSet
          lowerConcreteCanonicalDirection a slack d)
        (backgroundSet := backgroundTypicalSet
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          N Mbg (lowerConcreteTau a slack d)
          (lowerConcreteDeletedBackgroundMean R k d) k)
        hq0pos hFav)
  have hS_nonneg : 0 ≤ S :=
    le_trans (by
      unfold opNorm
      positivity) hQOp
  have hLocal :
      |localWordScaledTraceTerm (p := Fin d) (q := Fin d) N A 0 Q w| ≤
        N ^ (k - 1) *
          (S * ((Mbg / N) ^ (k - 2) * (Mbg / Real.sqrt N))) :=
    lower_localWordScaledTraceTerm_oneQ_noL_bound
      (p := Fin d) (q := Fin d)
      (N := N) (M := Mbg) (Sbound := S)
      (A := A) (Q := Q) (w := w)
      hN_nonneg hk3 hS_nonneg hQFrob hBgOp hBgFrob hNoL hQ1
  exact le_trans hLocal (by simpa [N, Mbg, S, A, Q] using hScale_d)

/-- Direct many-`Q` scalar leaf for the literal PT mixed-word envelope.

This is the many-spike analogue of
`lowerConcretePTMixedWordOneQDirectScalarBound`.  The parameter `j` is the
number of `Q` letters in the word. -/
def lowerConcretePTMixedWordManyQDirectScalarBound
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (ε M : ℝ) : Prop :=
  ∀ a : ℝ, spikeRoot k ε < a →
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        ∀ hs : 0 < R.sample d,
          ∀ X : SampleMatrix (Fin d) (Fin d) (Fin (R.sample d)),
            X ∈
              sphericalOneColumnFavorableEvent
                (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                (⟨0, hs⟩ : Fin (R.sample d))
                (betaColumnSpikeScale
                  (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                (lowerConcreteDelta a slack d)
                (lowerConcreteDirectionCapSet
                  lowerConcreteCanonicalDirection a slack d)
                (backgroundTypicalSet
                  (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                  (lowerConcreteN d) (lowerConcreteM R a slack d)
                  (lowerConcreteTau a slack d)
                  (lowerConcreteDeletedBackgroundMean R k d) k) →
            frobeniusNorm (p := Fin d) (q := Fin d)
                (σ := Fin (R.sample d)) X = 1 →
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                localWordLetterCount LocalExpansionLetter.L w = 0 →
                  ∀ j : ℕ, j ∈ Finset.Icc 2 (k - 1) →
                    localWordLetterCount LocalExpansionLetter.Q w = j →
                      |localWordScaledTraceTerm (p := Fin d) (q := Fin d)
                          (lowerConcreteN d)
                          (columnBackgroundMatrix
                            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                            X (⟨0, hs⟩ : Fin (R.sample d)))
                          0
                          (columnSpikeMatrix
                            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                            X (⟨0, hs⟩ : Fin (R.sample d)))
                          w| ≤
                        (a + slack) ^ j * M ^ (k - j) *
                          ((d : ℝ) ^ 2) ^ ((j : ℝ) / (k : ℝ) - 1)

/-- Scalar comparison sufficient for the direct many-`Q` mixed-word leaf.

The finite cyclic normalization and the local many-`Q` trace estimate are
already proved.  This predicate isolates the remaining scalar comparison
between the concrete background threshold and the fixed PT envelope, for each
fiber with `j ≥ 2` spike letters. -/
def lowerConcretePTMixedWordManyQScaleComparison
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (ε M : ℝ) : Prop :=
  ∀ a : ℝ, spikeRoot k ε < a →
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        ∀ j : ℕ, j ∈ Finset.Icc 2 (k - 1) →
          (lowerConcreteN d : ℝ) ^ (k - 1) *
            (((lowerConcreteM R a slack d) / (lowerConcreteN d : ℝ)) ^
                (k - j) *
              betaColumnIntervalUpper
                (betaColumnSpikeScale
                  (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                (lowerConcreteDelta a slack d) ^ j) ≤
            (a + slack) ^ j * M ^ (k - j) *
              ((d : ℝ) ^ 2) ^ ((j : ℝ) / (k : ℝ) - 1)

/-- The many-`Q` scale-comparison packet already forces the fixed PT envelope
parameter to be nonnegative.

Specializing the comparison to `j = k - 1` leaves the right-hand side as a
positive scalar multiple of `M`.  The left-hand side is nonnegative at a large
dimension where the sample size is at least two and the spike scale is
positive. -/
theorem lowerConcretePTMixedWordManyQScaleComparison_nonneg_M
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε M : ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hManyScale : lowerConcretePTMixedWordManyQScaleComparison R k ε M) :
    0 ≤ M := by
  let a : ℝ := spikeRoot k ε + 1
  have hk0 : 0 < k := by omega
  have ha : spikeRoot k ε < a := by
    dsimp [a]
    linarith
  have hslack : 0 < (1 : ℝ) := by norm_num
  have hScaleEv := hManyScale a ha 1 hslack
  have hBetaEv :=
    lower_concrete_hBetaScalePos
      (k := k) hk0 (ε := ε) hε a ha 1 hslack
  have hAll :
      ∀ᶠ d : ℕ in atTop,
        (∀ j ∈ Finset.Icc 2 (k - 1),
          (lowerConcreteN d : ℝ) ^ (k - 1) *
              (((lowerConcreteM R a 1 d) / (lowerConcreteN d : ℝ)) ^
                  (k - j) *
                betaColumnIntervalUpper
                  (betaColumnSpikeScale
                    (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                  (lowerConcreteDelta a 1 d) ^ j) ≤
            (a + 1) ^ j * M ^ (k - j) *
              ((d : ℝ) ^ 2) ^ ((j : ℝ) / (k : ℝ) - 1)) ∧
          0 < d ∧
          2 ≤ R.sample d ∧
          0 < betaColumnSpikeScale
            (lowerConcreteN d : ℝ) (spikeSpeed k d) a := by
    filter_upwards [hScaleEv, eventually_gt_atTop 0,
      lower_concrete_eventually_two_le_sample R, hBetaEv]
      with d hScale hd hSample2 hBeta
    exact ⟨hScale, hd, hSample2, hBeta⟩
  rcases hAll.exists with ⟨d, hScale, hd, hSample2, hBeta_pos⟩
  have hj : k - 1 ∈ Finset.Icc 2 (k - 1) := by
    exact Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
  have hineq := hScale (k - 1) hj
  have hkminus : k - (k - 1) = 1 := by omega
  rw [hkminus, pow_one] at hineq
  have hdR : 0 < (d : ℝ) := by
    exact_mod_cast hd
  have hNpos : 0 < (lowerConcreteN d : ℝ) := by
    simp [lowerConcreteN, pow_two, mul_pos hdR hdR]
  have hspos : 0 < R.sample d := by omega
  have hSampleMinusOne : 0 < ((R.sample d - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < R.sample d - 1)
  have hgamma_pos :
      0 < (2 + 128 * ((d : ℝ) ^ 2 + 1)) *
          ((R.sample d - 1 : ℕ) : ℝ) / (1 / 2 : ℝ) := by
    positivity
  have hMbg_pos : 0 < lowerConcreteM R a 1 d :=
    lt_of_lt_of_le hgamma_pos
      (lowerConcreteM_ge_deletedColumn_gammaThreshold_explicit
        R a 1 hspos)
  have hMdiv_pos : 0 < lowerConcreteM R a 1 d / (lowerConcreteN d : ℝ) :=
    div_pos hMbg_pos hNpos
  have hdelta_pos : 0 < lowerConcreteDelta a 1 d := by
    simp [lowerConcreteDelta, inv_pos, hdR]
  have hOnePlusDelta : 0 < 1 + lowerConcreteDelta a 1 d := by
    linarith
  have hbetaUpper_pos :
      0 < betaColumnIntervalUpper
        (betaColumnSpikeScale
          (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
        (lowerConcreteDelta a 1 d) := by
    dsimp [betaColumnIntervalUpper]
    exact mul_pos hOnePlusDelta hBeta_pos
  have hleft_nonneg :
      0 ≤ (lowerConcreteN d : ℝ) ^ (k - 1) *
            ((lowerConcreteM R a 1 d / (lowerConcreteN d : ℝ)) *
              betaColumnIntervalUpper
                (betaColumnSpikeScale
                  (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                (lowerConcreteDelta a 1 d) ^ (k - 1)) := by
    positivity
  have hrhs_nonneg := le_trans hleft_nonneg hineq
  rw [pow_one] at hrhs_nonneg
  have ha_pos : 0 < a := lt_trans (spikeRoot_pos hk0 hε) ha
  have ha1_pos : 0 < a + 1 := by
    linarith
  have hApow_pos : 0 < (a + 1) ^ (k - 1) := pow_pos ha1_pos _
  have hd2_pos : 0 < (d : ℝ) ^ 2 := sq_pos_of_pos hdR
  have hDpow_pos :
      0 < ((d : ℝ) ^ 2) ^
        (((k - 1 : ℕ) : ℝ) / (k : ℝ) - 1) :=
    Real.rpow_pos_of_pos hd2_pos _
  rw [show
      (a + 1) ^ (k - 1) * M *
          ((d : ℝ) ^ 2) ^ (((k - 1 : ℕ) : ℝ) / (k : ℝ) - 1) =
        ((a + 1) ^ (k - 1) *
            ((d : ℝ) ^ 2) ^
              (((k - 1 : ℕ) : ℝ) / (k : ℝ) - 1)) * M by
    ring] at hrhs_nonneg
  exact
    (mul_nonneg_iff_of_pos_left
      (mul_pos hApow_pos hDpow_pos)).mp hrhs_nonneg

/-- Close the direct many-`Q` mixed-word leaf from the local many-`Q` trace
estimate plus the scalar scale comparison.

This is the many-`Q` analogue of
`lowerConcretePTMixedWordOneQDirectScalarBound_of_scaleComparison`.  It does
not use the known-dead runtime-domination route; the runtime-shaped scalar
quantity appears only as the exact output of the local trace estimate. -/
theorem lowerConcretePTMixedWordManyQDirectScalarBound_of_scaleComparison
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε M : ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hScale : lowerConcretePTMixedWordManyQScaleComparison R k ε M) :
    lowerConcretePTMixedWordManyQDirectScalarBound R k ε M := by
  intro a ha slack hslack
  have hk : 1 ≤ k := by omega
  have hk0 : 0 < k := Nat.zero_lt_of_lt hk
  filter_upwards [eventually_gt_atTop 0,
      lower_concrete_hBetaScalePos (k := k) hk0 (ε := ε) hε a ha slack hslack,
      hScale a ha slack hslack]
    with d hd hq0pos hScale_d
  intro hs X hFav hSphere w hmix hL0 j hj hQj
  let N : ℝ := lowerConcreteN d
  let Mbg : ℝ := lowerConcreteM R a slack d
  let S : ℝ :=
    betaColumnIntervalUpper
      (betaColumnSpikeScale N (spikeSpeed k d) a)
      (lowerConcreteDelta a slack d)
  let A :=
    columnBackgroundMatrix
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      X (⟨0, hs⟩ : Fin (R.sample d))
  let Q :=
    columnSpikeMatrix
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      X (⟨0, hs⟩ : Fin (R.sample d))
  have hNoL : ∀ i : Fin k, w i ≠ LocalExpansionLetter.L := by
    intro i hi
    have hpos :
        0 < localWordLetterCount LocalExpansionLetter.L w :=
      lower_localWordLetterCount_pos_of_exists
        (letter := LocalExpansionLetter.L) (w := w) ⟨i, hi⟩
    omega
  have hBgOp :
      opNorm (p := Fin d) (q := Fin d) A ≤ Mbg / N := by
    simpa [A, Mbg, N] using
      (lower_sphericalOneColumnFavorableEvent_columnBackgroundMatrix_opNorm_bound
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        (α₀ := (⟨0, hs⟩ : Fin (R.sample d)))
        (q₀ := betaColumnSpikeScale N (spikeSpeed k d) a)
        (δ := lowerConcreteDelta a slack d)
        (N := N) (M := Mbg)
        (τ := lowerConcreteTau a slack d)
        (mean := lowerConcreteDeletedBackgroundMean R k d)
        (k := k)
        (directionSet := lowerConcreteDirectionCapSet
          lowerConcreteCanonicalDirection a slack d)
        hFav hSphere)
  have hQFrob :
      frobeniusNorm (p := Fin d) (q := Fin d)
          (σ := BipIndex (Fin d) (Fin d)) Q ≤ S := by
    simpa [Q, S, N] using
      (lower_sphericalOneColumnFavorableEvent_columnSpikeMatrix_frobeniusNorm_le_intervalUpper
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        (α₀ := (⟨0, hs⟩ : Fin (R.sample d)))
        (q₀ := betaColumnSpikeScale N (spikeSpeed k d) a)
        (δ := lowerConcreteDelta a slack d)
        (directionSet := lowerConcreteDirectionCapSet
          lowerConcreteCanonicalDirection a slack d)
        (backgroundSet := backgroundTypicalSet
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          N Mbg (lowerConcreteTau a slack d)
          (lowerConcreteDeletedBackgroundMean R k d) k)
        hq0pos hFav)
  have hQOp :
      opNorm (p := Fin d) (q := Fin d) Q ≤ S := by
    simpa [Q, S, N] using
      (lower_sphericalOneColumnFavorableEvent_columnSpikeMatrix_opNorm_le_intervalUpper
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        (α₀ := (⟨0, hs⟩ : Fin (R.sample d)))
        (q₀ := betaColumnSpikeScale N (spikeSpeed k d) a)
        (δ := lowerConcreteDelta a slack d)
        (directionSet := lowerConcreteDirectionCapSet
          lowerConcreteCanonicalDirection a slack d)
        (backgroundSet := backgroundTypicalSet
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          N Mbg (lowerConcreteTau a slack d)
          (lowerConcreteDeletedBackgroundMean R k d) k)
        hq0pos hFav)
  have hN_nonneg : 0 ≤ N := by
    dsimp [N, lowerConcreteN]
    positivity
  have hMdivN_nonneg : 0 ≤ Mbg / N := by
    exact le_trans (by
      unfold opNorm
      positivity) hBgOp
  have hS_nonneg : 0 ≤ S := by
    exact le_trans (by
      unfold opNorm
      positivity) hQOp
  have hQtwo : 2 ≤ localWordLetterCount LocalExpansionLetter.Q w := by
    have hj2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
    omega
  have hkpred : (k - 1) + 1 = k := by omega
  have hNoL_cast :
      ∀ i : Fin ((k - 1) + 1),
        (w ∘ Fin.cast hkpred) i ≠ LocalExpansionLetter.L := by
    intro i hi
    exact hNoL (Fin.cast hkpred i) hi
  have hQtwo_cast :
      2 ≤ localWordLetterCount LocalExpansionLetter.Q (w ∘ Fin.cast hkpred) := by
    simpa [lower_localWordLetterCount_cast, hkpred] using hQtwo
  have hMany_raw :=
    lower_localWordScaledTraceTerm_manyQ_noL_bound
      (p := Fin d) (q := Fin d)
      (N := N) (M := Mbg) (Sbound := S) (m := k - 1)
      (A := A) (Q := Q) (w := w ∘ Fin.cast hkpred)
      hN_nonneg hMdivN_nonneg hS_nonneg
      hBgOp hQOp hQFrob hNoL_cast hQtwo_cast
  have hMany := hMany_raw
  rw [lower_localWordScaledTraceTerm_cast
      (p := Fin d) (q := Fin d) (N := N) A 0 Q hkpred w] at hMany
  have hAcount :
      localWordLetterCount LocalExpansionLetter.A w = k - j := by
    have htotal := localWordLetterCount_total w
    rw [hL0, hQj] at htotal
    omega
  have hLocal :
      |localWordScaledTraceTerm (p := Fin d) (q := Fin d) N A 0 Q w| ≤
        N ^ (k - 1) * ((Mbg / N) ^ (k - j) * S ^ j) := by
    simpa [lower_localWordLetterCount_cast, hkpred, hAcount, hQj] using hMany
  exact le_trans hLocal (by simpa [N, Mbg, S, A, Q] using hScale_d j hj)

/-- Direct scalar case split for the literal PT pointwise mixed-word bound.

The proof does not use the runtime envelope.  Words containing `L` vanish;
words with no `L` split into the exactly-one-`Q` and many-`Q` cases, where the
two direct scalar leaves are consumed and then inserted into the literal PT
word-budget envelope. -/
theorem lowerConcreteMixedWordPointwiseBoundOnSphere_withPTError_of_directScalarCases
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε M : ℝ}
    (hk0 : 0 < k) (hε : 0 < ε) (hM : 0 ≤ M)
    (hOne : lowerConcretePTMixedWordOneQDirectScalarBound R k ε M)
    (hMany : lowerConcretePTMixedWordManyQDirectScalarBound R k ε M) :
    lowerConcreteMixedWordPointwiseBoundOnSphere R k ε
      (fun a slack d => lowerPartialTransposeMixedWordBoundD k (a + slack) M d) := by
  intro a ha slack hslack
  filter_upwards [hOne a ha slack hslack, hMany a ha slack hslack]
    with d hOne_d hMany_d
  intro hs X hFav hSphere w hmix
  have ha_nonneg : 0 ≤ a :=
    le_of_lt (lt_trans (spikeRoot_pos hk0 hε) ha)
  have hA : 0 ≤ a + slack := by
    linarith
  by_cases hL : ∃ i : Fin k, w i = LocalExpansionLetter.L
  · have hzero :
        localWordScaledTraceTerm (p := Fin d) (q := Fin d)
            (lowerConcreteN d)
            (columnBackgroundMatrix
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              X (⟨0, hs⟩ : Fin (R.sample d)))
            0
            (columnSpikeMatrix
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              X (⟨0, hs⟩ : Fin (R.sample d)))
            w = 0 :=
      lower_localWordScaledTraceTerm_zero_of_exists_L
        (p := Fin d) (q := Fin d)
        (N := lowerConcreteN d)
        (A :=
          columnBackgroundMatrix
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            X (⟨0, hs⟩ : Fin (R.sample d)))
        (Q :=
          columnSpikeMatrix
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            X (⟨0, hs⟩ : Fin (R.sample d)))
        w hL
    rw [hzero]
    simpa using
      lowerPartialTransposeMixedWordBoundD_nonneg
        (k := k) (d := d) (A := a + slack) (M := M) hA hM w
  · have hNoL : ∀ i : Fin k, w i ≠ LocalExpansionLetter.L := by
      intro i hi
      exact hL ⟨i, hi⟩
    have hL0 :
        localWordLetterCount LocalExpansionLetter.L w = 0 :=
      lower_localWordLetterCount_zero_of_forall_ne
        (letter := LocalExpansionLetter.L) hNoL
    by_cases hQ1 : localWordLetterCount LocalExpansionLetter.Q w = 1
    · calc
        |localWordScaledTraceTerm (p := Fin d) (q := Fin d)
            (lowerConcreteN d)
            (columnBackgroundMatrix
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              X (⟨0, hs⟩ : Fin (R.sample d)))
            0
            (columnSpikeMatrix
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              X (⟨0, hs⟩ : Fin (R.sample d)))
            w| ≤
              (a + slack) * M ^ (k - 1) *
                ((d : ℝ) ^ 2) ^ ((-1 / 2 : ℝ) + 1 / (k : ℝ)) :=
            hOne_d hs X hFav hSphere w hmix hL0 hQ1
        _ ≤ lowerPartialTransposeMixedWordBoundD k (a + slack) M d w :=
            lowerPartialTransposeMixedWordBoundD_oneQ_term_le
              (k := k) (d := d) (A := a + slack) (M := M)
              (w := w) hA hM hL0 hQ1
    · have hrange :=
        lower_localWord_mixed_noL_Q_count_range
          (k := k) (w := w) hmix hNoL
      have hQtwo : 2 ≤ localWordLetterCount LocalExpansionLetter.Q w := by
        omega
      let j : ℕ := localWordLetterCount LocalExpansionLetter.Q w
      have hQj : localWordLetterCount LocalExpansionLetter.Q w = j := rfl
      have hj : j ∈ Finset.Icc 2 (k - 1) := by
        exact Finset.mem_Icc.mpr
          ⟨by simpa [j] using hQtwo, by simpa [j] using hrange.2⟩
      calc
        |localWordScaledTraceTerm (p := Fin d) (q := Fin d)
            (lowerConcreteN d)
            (columnBackgroundMatrix
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              X (⟨0, hs⟩ : Fin (R.sample d)))
            0
            (columnSpikeMatrix
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              X (⟨0, hs⟩ : Fin (R.sample d)))
            w| ≤
              (a + slack) ^ j * M ^ (k - j) *
                ((d : ℝ) ^ 2) ^ ((j : ℝ) / (k : ℝ) - 1) :=
            hMany_d hs X hFav hSphere w hmix hL0 j hj hQj
        _ ≤ lowerPartialTransposeMixedWordBoundD k (a + slack) M d w :=
            lowerPartialTransposeMixedWordBoundD_manyQ_term_le
              (k := k) (d := d) (j := j) (A := a + slack) (M := M)
              (w := w) hA hM hj hL0 hQj

/-- Reduce the mixed runtime-domination leaf to the two genuine no-`L` cases.

For a mixed word containing `L`, the runtime envelope is zero and the literal
PT envelope is nonnegative.  For a mixed word with no `L`, the existing
finite-word range lemma says that the `Q` count is either exactly `1` or at
least `2`.  Thus the remaining domination work is precisely the one-`Q`
scalar estimate and the many-`Q` scalar estimate. -/
theorem lowerConcreteMixedRuntimeWordBound_domination_on_mixed_of_oneQ_manyQ
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε M : ℝ}
    (hk0 : 0 < k) (hε : 0 < ε) (hM : 0 ≤ M)
    (hOne :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                localWordLetterCount LocalExpansionLetter.L w = 0 →
                  localWordLetterCount LocalExpansionLetter.Q w = 1 →
                    lowerConcreteMixedRuntimeWordBound R k a slack d w ≤
                      lowerPartialTransposeMixedWordBoundD k (a + slack) M d w)
    (hMany :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                localWordLetterCount LocalExpansionLetter.L w = 0 →
                  2 ≤ localWordLetterCount LocalExpansionLetter.Q w →
                    lowerConcreteMixedRuntimeWordBound R k a slack d w ≤
                      lowerPartialTransposeMixedWordBoundD k (a + slack) M d w) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ w : Fin k → LocalExpansionLetter,
            localWordIsMixed w →
              lowerConcreteMixedRuntimeWordBound R k a slack d w ≤
                lowerPartialTransposeMixedWordBoundD k (a + slack) M d w := by
  intro a ha slack hslack
  filter_upwards [hOne a ha slack hslack, hMany a ha slack hslack]
    with d hOne_d hMany_d
  intro w hmix
  by_cases hL : ∃ i : Fin k, w i = LocalExpansionLetter.L
  · have hzero :
        lowerConcreteMixedRuntimeWordBound R k a slack d w = 0 :=
      lowerConcreteMixedRuntimeWordBound_eq_zero_of_exists_L
        (R := R) (k := k) (a := a) (slack := slack) (d := d) (w := w) hL
    rw [hzero]
    have ha_nonneg : 0 ≤ a :=
      le_of_lt (lt_trans (spikeRoot_pos hk0 hε) ha)
    have hA : 0 ≤ a + slack := by
      linarith
    exact lowerPartialTransposeMixedWordBoundD_nonneg
      (k := k) (d := d) (A := a + slack) (M := M) hA hM w
  · have hNoL : ∀ i : Fin k, w i ≠ LocalExpansionLetter.L := by
      intro i hi
      exact hL ⟨i, hi⟩
    have hL0 :
        localWordLetterCount LocalExpansionLetter.L w = 0 :=
      lower_localWordLetterCount_zero_of_forall_ne
        (letter := LocalExpansionLetter.L) hNoL
    by_cases hQ1 : localWordLetterCount LocalExpansionLetter.Q w = 1
    · exact hOne_d w hmix hL0 hQ1
    · have hrange :=
        lower_localWord_mixed_noL_Q_count_range
          (k := k) (w := w) hmix hNoL
      have hQtwo : 2 ≤ localWordLetterCount LocalExpansionLetter.Q w := by
        omega
      exact hMany_d w hmix hL0 hQtwo

/-- Reduce the mixed runtime-domination leaf one step further: after the
finite word split, the only remaining inputs are two scalar eventual
inequalities, one for the exactly-one-`Q` fiber and one for each many-`Q`
fiber.

This theorem intentionally keeps the scalar hypotheses explicit.  They are the
place where the Beta interval radius and the concrete runtime background
threshold `lowerConcreteM` must be compared with the fixed PT envelope
parameters. -/
theorem lowerConcreteMixedRuntimeWordBound_domination_on_mixed_of_scalar_cases
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε M : ℝ}
    (hk0 : 0 < k) (hε : 0 < ε) (hM : 0 ≤ M)
    (hOneScalar :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            (lowerConcreteN d : ℝ) ^ (k - 1) *
              (betaColumnIntervalUpper
                  (betaColumnSpikeScale
                    (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                  (lowerConcreteDelta a slack d) *
                (((lowerConcreteM R a slack d) / (lowerConcreteN d : ℝ)) ^
                    (k - 2) *
                  ((lowerConcreteM R a slack d) /
                    Real.sqrt (lowerConcreteN d : ℝ)))) ≤
              (a + slack) * M ^ (k - 1) *
                ((d : ℝ) ^ 2) ^ ((-1 / 2 : ℝ) + 1 / (k : ℝ)))
    (hManyScalar :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ j : ℕ, j ∈ Finset.Icc 2 (k - 1) →
              (lowerConcreteN d : ℝ) ^ (k - 1) *
                (((lowerConcreteM R a slack d) / (lowerConcreteN d : ℝ)) ^
                    (k - j) *
                  betaColumnIntervalUpper
                    (betaColumnSpikeScale
                      (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                    (lowerConcreteDelta a slack d) ^ j) ≤
                (a + slack) ^ j * M ^ (k - j) *
                  ((d : ℝ) ^ 2) ^ ((j : ℝ) / (k : ℝ) - 1)) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ w : Fin k → LocalExpansionLetter,
            localWordIsMixed w →
              lowerConcreteMixedRuntimeWordBound R k a slack d w ≤
                lowerPartialTransposeMixedWordBoundD k (a + slack) M d w := by
  intro a ha slack hslack
  filter_upwards [hOneScalar a ha slack hslack, hManyScalar a ha slack hslack]
    with d hOne_d hMany_d
  intro w hmix
  have ha_nonneg : 0 ≤ a :=
    le_of_lt (lt_trans (spikeRoot_pos hk0 hε) ha)
  have hA : 0 ≤ a + slack := by
    linarith
  by_cases hL : ∃ i : Fin k, w i = LocalExpansionLetter.L
  · have hzero :
        lowerConcreteMixedRuntimeWordBound R k a slack d w = 0 :=
      lowerConcreteMixedRuntimeWordBound_eq_zero_of_exists_L
        (R := R) (k := k) (a := a) (slack := slack) (d := d) (w := w) hL
    rw [hzero]
    exact lowerPartialTransposeMixedWordBoundD_nonneg
      (k := k) (d := d) (A := a + slack) (M := M) hA hM w
  · have hNoL : ∀ i : Fin k, w i ≠ LocalExpansionLetter.L := by
      intro i hi
      exact hL ⟨i, hi⟩
    have hL0 :
        localWordLetterCount LocalExpansionLetter.L w = 0 :=
      lower_localWordLetterCount_zero_of_forall_ne
        (letter := LocalExpansionLetter.L) hNoL
    by_cases hQ1 : localWordLetterCount LocalExpansionLetter.Q w = 1
    · calc
        lowerConcreteMixedRuntimeWordBound R k a slack d w
            =
              (lowerConcreteN d : ℝ) ^ (k - 1) *
                (betaColumnIntervalUpper
                    (betaColumnSpikeScale
                      (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                    (lowerConcreteDelta a slack d) *
                  (((lowerConcreteM R a slack d) / (lowerConcreteN d : ℝ)) ^
                      (k - 2) *
                    ((lowerConcreteM R a slack d) /
                      Real.sqrt (lowerConcreteN d : ℝ)))) := by
              exact
                lowerConcreteMixedRuntimeWordBound_eq_oneQ_noL
                  (R := R) (k := k) (a := a) (slack := slack)
                  (d := d) (w := w) hL0 hQ1
        _ ≤
              (a + slack) * M ^ (k - 1) *
                ((d : ℝ) ^ 2) ^ ((-1 / 2 : ℝ) + 1 / (k : ℝ)) :=
              hOne_d
        _ ≤ lowerPartialTransposeMixedWordBoundD k (a + slack) M d w :=
              lowerPartialTransposeMixedWordBoundD_oneQ_term_le
                (k := k) (d := d) (A := a + slack) (M := M)
                (w := w) hA hM hL0 hQ1
    · have hrange :=
        lower_localWord_mixed_noL_Q_count_range
          (k := k) (w := w) hmix hNoL
      have hQtwo : 2 ≤ localWordLetterCount LocalExpansionLetter.Q w := by
        omega
      let j : ℕ := localWordLetterCount LocalExpansionLetter.Q w
      have hQj : localWordLetterCount LocalExpansionLetter.Q w = j := rfl
      have hj : j ∈ Finset.Icc 2 (k - 1) := by
        exact Finset.mem_Icc.mpr ⟨by simpa [j] using hQtwo, by simpa [j] using hrange.2⟩
      have hAcount :
          localWordLetterCount LocalExpansionLetter.A w = k - j := by
        have htotal := localWordLetterCount_total w
        rw [hL0, hQj] at htotal
        omega
      calc
        lowerConcreteMixedRuntimeWordBound R k a slack d w
            =
              (lowerConcreteN d : ℝ) ^ (k - 1) *
                (((lowerConcreteM R a slack d) / (lowerConcreteN d : ℝ)) ^
                    localWordLetterCount LocalExpansionLetter.A w *
                  betaColumnIntervalUpper
                    (betaColumnSpikeScale
                      (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                    (lowerConcreteDelta a slack d) ^
                      localWordLetterCount LocalExpansionLetter.Q w) := by
              exact
                lowerConcreteMixedRuntimeWordBound_eq_manyQ_noL
                  (R := R) (k := k) (a := a) (slack := slack)
                  (d := d) (w := w) hL0 hQtwo
        _ =
              (lowerConcreteN d : ℝ) ^ (k - 1) *
                (((lowerConcreteM R a slack d) / (lowerConcreteN d : ℝ)) ^
                    (k - j) *
                  betaColumnIntervalUpper
                    (betaColumnSpikeScale
                      (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                    (lowerConcreteDelta a slack d) ^ j) := by
              simp [hAcount, hQj]
        _ ≤
              (a + slack) ^ j * M ^ (k - j) *
                ((d : ℝ) ^ 2) ^ ((j : ℝ) / (k : ℝ) - 1) :=
              hMany_d j hj
        _ ≤ lowerPartialTransposeMixedWordBoundD k (a + slack) M d w :=
              lowerPartialTransposeMixedWordBoundD_manyQ_term_le
                (k := k) (d := d) (j := j) (A := a + slack) (M := M)
                (w := w) hA hM hj hL0 hQj

/-- LFC-PPT-012: the finite coefficient-budget aggregation for the corrected PT
mixed error. This closes the budget layer; the separate pointwise theorem is
responsible for proving that each literal word is bounded by this envelope. -/
theorem lowerConcreteMixedWordBudgetWithPTError_literal
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε M : ℝ}
    (hk0 : 0 < k) (hε : 0 < ε) (hM : 0 ≤ M) :
    lowerConcreteMixedWordBudgetWithError R k ε
      (fun a slack d =>
        lowerPartialTransposeMixedWordBoundD k (a + slack) M d)
      (fun a slack d =>
        lowerPartialTransposeMixedErrorD k (a + slack) M d) := by
  intro a ha slack hslack
  refine Filter.Eventually.of_forall ?_
  intro d
  unfold lowerPartialTransposeMixedWordBoundD lowerPartialTransposeMixedErrorD
  have ha_nonneg : 0 ≤ a :=
    le_of_lt (lt_trans (spikeRoot_pos hk0 hε) ha)
  have hA : 0 ≤ a + slack := by
    linarith
  exact
    lowerPartialTransposeMixedWordBoundN_budget
      (k := k) (A := a + slack) (M := M) (N := (d : ℝ) ^ 2)
      hA hM (by positivity)

/-! ### Filtered-sum extraction lemmas for runtime diagnostics -/

/-- A filtered mixed-word sum is nonnegative when every mixed summand is
nonnegative.

This is deliberately stated for the raw filtered sum rather than the concrete
runtime envelope, so later diagnostics can extract individual mixed words from
any repaired envelope. -/
theorem localMixedWordFilteredSum_nonneg
    {k : ℕ} (f : (Fin k → LocalExpansionLetter) → ℝ)
    (hf : ∀ w, localWordIsMixed w → 0 ≤ f w) :
    0 ≤ localMixedWordFilteredSum (k := k) f := by
  classical
  unfold localMixedWordFilteredSum
  apply Finset.sum_nonneg
  intro w _
  by_cases hw : localWordIsMixed w
  · simp [hw, hf w hw]
  · simp [hw]

/-- A filtered mixed-word sum dominates any one mixed summand, provided all
mixed summands are nonnegative. -/
theorem localMixedWordFilteredSum_single_le
    {k : ℕ} (f : (Fin k → LocalExpansionLetter) → ℝ)
    (hf : ∀ w, localWordIsMixed w → 0 ≤ f w)
    (w₀ : Fin k → LocalExpansionLetter) (hw₀ : localWordIsMixed w₀) :
    f w₀ ≤ localMixedWordFilteredSum (k := k) f := by
  classical
  let g : (Fin k → LocalExpansionLetter) → ℝ :=
    fun w => if localWordIsMixed w then f w else 0
  have hg : ∀ w, 0 ≤ g w := by
    intro w
    by_cases hw : localWordIsMixed w
    · simp [g, hw, hf w hw]
    · simp [g, hw]
  have hmem :
      w₀ ∈ (Finset.univ : Finset (Fin k → LocalExpansionLetter)) :=
    Finset.mem_univ _
  have hsingle :=
    Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin k → LocalExpansionLetter)))
      (f := g) (fun i _ => hg i) hmem
  simpa [localMixedWordFilteredSum, g, hw₀] using hsingle

/-! ### A distinguished one-`Q` mixed word for runtime obstructions -/

/-- The explicit mixed word with a spike letter at the head and background
letters everywhere else.  It has length `k + 1`, one `Q`, and no `L`. -/
def lowerHeadQRestAWord (k : ℕ) : Fin (k + 1) → LocalExpansionLetter :=
  fun i => if i = 0 then LocalExpansionLetter.Q else LocalExpansionLetter.A

/-- The head-`Q`, rest-`A` word has exactly one spike letter. -/
theorem lowerHeadQRestAWord_Q_count (k : ℕ) :
    localWordLetterCount LocalExpansionLetter.Q
      (lowerHeadQRestAWord k) = 1 := by
  unfold lowerHeadQRestAWord localWordLetterCount
  simp

/-- The head-`Q`, rest-`A` word has no linear defect letters. -/
theorem lowerHeadQRestAWord_L_count (k : ℕ) :
    localWordLetterCount LocalExpansionLetter.L
      (lowerHeadQRestAWord k) = 0 := by
  unfold localWordLetterCount
  apply Finset.sum_eq_zero
  intro x _
  unfold lowerHeadQRestAWord
  by_cases hx : x = 0
  · simp [hx]
  · simp [hx]

/-- For length at least two, the head-`Q`, rest-`A` word is genuinely mixed. -/
theorem lowerHeadQRestAWord_mixed {k : ℕ} (hk : 0 < k) :
    localWordIsMixed (lowerHeadQRestAWord k) := by
  rw [localWordIsMixed_iff_ne_pureA_and_ne_pureQ]
  constructor
  · intro h
    have h0 := congrFun h 0
    simp [lowerHeadQRestAWord, localPureAWord] at h0
  · intro h
    let i1 : Fin (k + 1) := ⟨1, Nat.succ_lt_succ hk⟩
    have h1 := congrFun h i1
    have hi1_ne_zero : i1 ≠ 0 := by
      intro hz
      have hzv := congrArg Fin.val hz
      simp [i1] at hzv
    simp [lowerHeadQRestAWord, localPureQWord, hi1_ne_zero] at h1

/-- Reduction of the mixed frontier to a word-by-word estimate plus a finite
scalar mixed-word budget. -/
theorem lower_concreteMixedLocalExpansionEnvelope_of_wordBounds
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ}
    (hk : 1 ≤ k)
    (bound : ℝ → ℝ → ℕ → (Fin k → LocalExpansionLetter) → ℝ)
    (hWord :
      lowerConcreteMixedWordPointwiseBound R k ε bound)
    (hBudget :
      lowerConcreteMixedWordBudget R k ε bound) :
    lowerConcreteMixedLocalExpansionEnvelope R k ε := by
  intro a ha slack hslack
  filter_upwards [hWord a ha slack hslack, hBudget a ha slack hslack]
    with d hWord_d hBudget_d
  intro hs X hFav
  have hAbs :
      |localExpansionMixedRemainder (p := Fin d) (q := Fin d)
          (lowerConcreteN d) k
          (columnBackgroundMatrix
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            X (⟨0, hs⟩ : Fin (R.sample d)))
          0
          (columnSpikeMatrix
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            X (⟨0, hs⟩ : Fin (R.sample d)))| ≤
        localMixedWordFilteredSum (k := k) (bound a slack d) := by
    exact
      localExpansionMixedRemainder_abs_le_of_wordBounds
        (p := Fin d) (q := Fin d)
        (N := lowerConcreteN d)
        (k := k)
        (A :=
          columnBackgroundMatrix
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            X (⟨0, hs⟩ : Fin (R.sample d)))
        (L := 0)
        (Q :=
          columnSpikeMatrix
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            X (⟨0, hs⟩ : Fin (R.sample d)))
        hk
        (bound := bound a slack d)
        (by
          intro w hw
          exact hWord_d hs X hFav w hw)
  exact le_trans hAbs hBudget_d

/-- Explicit-error version of
`lower_concreteMixedLocalExpansionEnvelope_of_wordBounds`.

This is the preferred reduction for the remaining mixed debt: first prove
word-by-word bounds, then choose an error sequence large enough for their
finite sum and prove that sequence is `o(1)` at the endpoint level. -/
theorem lower_concreteMixedLocalExpansionEnvelopeWithError_of_wordBounds
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ}
    (hk : 1 ≤ k)
    (bound : ℝ → ℝ → ℕ → (Fin k → LocalExpansionLetter) → ℝ)
    (errMix : ℝ → ℝ → ℕ → ℝ)
    (hWord :
      lowerConcreteMixedWordPointwiseBound R k ε bound)
    (hBudget :
      lowerConcreteMixedWordBudgetWithError R k ε bound errMix) :
    lowerConcreteMixedLocalExpansionEnvelopeWithError R k ε errMix := by
  intro a ha slack hslack
  filter_upwards [hWord a ha slack hslack, hBudget a ha slack hslack]
    with d hWord_d hBudget_d
  intro hs X hFav
  have hAbs :
      |localExpansionMixedRemainder (p := Fin d) (q := Fin d)
          (lowerConcreteN d) k
          (columnBackgroundMatrix
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            X (⟨0, hs⟩ : Fin (R.sample d)))
          0
          (columnSpikeMatrix
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            X (⟨0, hs⟩ : Fin (R.sample d)))| ≤
        localMixedWordFilteredSum (k := k) (bound a slack d) := by
    exact
      localExpansionMixedRemainder_abs_le_of_wordBounds
        (p := Fin d) (q := Fin d)
        (N := lowerConcreteN d)
        (k := k)
        (A :=
          columnBackgroundMatrix
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            X (⟨0, hs⟩ : Fin (R.sample d)))
        (L := 0)
        (Q :=
          columnSpikeMatrix
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            X (⟨0, hs⟩ : Fin (R.sample d)))
        hk
        (bound := bound a slack d)
        (by
          intro w hw
          exact hWord_d hs X hFav w hw)
  exact le_trans hAbs hBudget_d

/-- Sphere-supported reduction of the repaired mixed frontier to word-by-word
bounds plus a finite scalar budget. -/
theorem lower_concreteMixedLocalExpansionEnvelopeOnSphereWithError_of_wordBounds
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ}
    (hk : 1 ≤ k)
    (bound : ℝ → ℝ → ℕ → (Fin k → LocalExpansionLetter) → ℝ)
    (errMix : ℝ → ℝ → ℕ → ℝ)
    (hWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k ε bound)
    (hBudget :
      lowerConcreteMixedWordBudgetWithError R k ε bound errMix) :
    lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithError R k ε errMix := by
  intro a ha slack hslack
  filter_upwards [hWord a ha slack hslack, hBudget a ha slack hslack]
    with d hWord_d hBudget_d
  intro hs X hFav hSphere
  have hAbs :
      |localExpansionMixedRemainder (p := Fin d) (q := Fin d)
          (lowerConcreteN d) k
          (columnBackgroundMatrix
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            X (⟨0, hs⟩ : Fin (R.sample d)))
          0
          (columnSpikeMatrix
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            X (⟨0, hs⟩ : Fin (R.sample d)))| ≤
        localMixedWordFilteredSum (k := k) (bound a slack d) := by
    exact
      localExpansionMixedRemainder_abs_le_of_wordBounds
        (p := Fin d) (q := Fin d)
        (N := lowerConcreteN d)
        (k := k)
        (A :=
          columnBackgroundMatrix
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            X (⟨0, hs⟩ : Fin (R.sample d)))
        (L := 0)
        (Q :=
          columnSpikeMatrix
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            X (⟨0, hs⟩ : Fin (R.sample d)))
        hk
        (bound := bound a slack d)
        (by
          intro w hw
          exact hWord_d hs X hFav hSphere w hw)
  exact le_trans hAbs hBudget_d

/-- Runtime-native finite mixed-word error.

This is the exact deterministic error produced by the favourable event through
`lowerConcreteMixedRuntimeWordBound`. It deliberately does not compare the
runtime background threshold `lowerConcreteM R a slack d` with a fixed
endpoint-facing scalar parameter. The latter comparison is incompatible with
the already-formalized eventual lower bound
`lowerConcreteM R a slack d / lowerConcreteN d ≥ 256` unless the favourable
background event is sharpened. -/
noncomputable def lowerConcreteMixedRuntimeWordError
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (a slack : ℝ) (d : ℕ) : ℝ :=
  localMixedWordFilteredSum (k := k)
    (lowerConcreteMixedRuntimeWordBound R k a slack d)

/-- Exact runtime envelope for the distinguished head-`Q`, rest-`A` word. -/
theorem lowerConcreteMixedRuntimeWordBound_headQRestA_eq
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (m : ℕ) (a slack : ℝ) (d : ℕ) :
    lowerConcreteMixedRuntimeWordBound R (m + 1) a slack d
        (lowerHeadQRestAWord m) =
      (lowerConcreteN d) ^ m *
        (betaColumnIntervalUpper
            (betaColumnSpikeScale (lowerConcreteN d) (spikeSpeed (m + 1) d) a)
            (lowerConcreteDelta a slack d) *
          (((lowerConcreteM R a slack d) / (lowerConcreteN d)) ^ (m - 1) *
            ((lowerConcreteM R a slack d) / Real.sqrt (lowerConcreteN d)))) := by
  simpa using
    lowerConcreteMixedRuntimeWordBound_eq_oneQ_noL
      (R := R) (k := m + 1) (a := a) (slack := slack) (d := d)
      (w := lowerHeadQRestAWord m)
      (lowerHeadQRestAWord_L_count m)
      (lowerHeadQRestAWord_Q_count m)

/-- Scalar lower bound for the distinguished length-three runtime word.

This is the first theorem-strength scalar extraction from the runtime
diagnostic: for the word `QAA`, the runtime envelope is bounded below by the
nominal spike scale times two certified background-threshold lower bounds. -/
theorem lowerConcreteMixedRuntimeWordBound_headQRestA_two_eventually_ge
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ a : ℝ, spikeRoot 3 ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d : ℕ in atTop,
          (lowerConcreteN d : ℝ) ^ 2 *
              (a * (lowerConcreteN d : ℝ) ^ ((-1 : ℝ) + 1 / (3 : ℝ)) *
                (256 * (256 * Real.sqrt (lowerConcreteN d : ℝ)))) ≤
            lowerConcreteMixedRuntimeWordBound R 3 a slack d
              (lowerHeadQRestAWord 2) := by
  intro a ha slack _hslack
  have ha_nonneg : 0 ≤ a := by
    have hrootpos : 0 < spikeRoot 3 ε :=
      spikeRoot_pos (k := 3) (by norm_num) hε
    exact le_of_lt (lt_trans hrootpos ha)
  filter_upwards [eventually_gt_atTop 0,
      lowerConcreteM_div_lowerConcreteN_eventually_ge_const R a slack,
      lowerConcreteM_eventually_ge_quadratic R a slack]
    with d hd hMN hMquad
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hNpos : 0 < (lowerConcreteN d : ℝ) := by
    simp [lowerConcreteN, pow_two, mul_pos hdR hdR]
  have hN_nonneg : 0 ≤ (lowerConcreteN d : ℝ) := le_of_lt hNpos
  have hsqrt_pos :
      0 < Real.sqrt (lowerConcreteN d : ℝ) :=
    Real.sqrt_pos.2 hNpos
  have hM_nonneg : 0 ≤ lowerConcreteM R a slack d := by
    have hquad_nonneg : 0 ≤ 256 * (d : ℝ) ^ 2 := by positivity
    exact le_trans hquad_nonneg hMquad
  have hMsqrt :
      256 * Real.sqrt (lowerConcreteN d : ℝ) ≤
        lowerConcreteM R a slack d / Real.sqrt (lowerConcreteN d : ℝ) := by
    apply (le_div_iff₀ hsqrt_pos).mpr
    have hsqrt_sq :
        Real.sqrt (lowerConcreteN d : ℝ) *
            Real.sqrt (lowerConcreteN d : ℝ) =
          (lowerConcreteN d : ℝ) := by
      rw [← sq]
      exact Real.sq_sqrt hN_nonneg
    have hbase :
        256 * (lowerConcreteN d : ℝ) ≤ lowerConcreteM R a slack d := by
      exact (le_div_iff₀ hNpos).mp hMN
    calc
      256 * Real.sqrt (lowerConcreteN d : ℝ) *
          Real.sqrt (lowerConcreteN d : ℝ)
          = 256 * (lowerConcreteN d : ℝ) := by
            rw [mul_assoc, hsqrt_sq]
      _ ≤ lowerConcreteM R a slack d := hbase
  have hS :
      a * (lowerConcreteN d : ℝ) ^ ((-1 : ℝ) + 1 / (3 : ℝ)) ≤
        betaColumnIntervalUpper
          (betaColumnSpikeScale (lowerConcreteN d : ℝ) (spikeSpeed 3 d) a)
          (lowerConcreteDelta a slack d) := by
    exact
      lowerConcrete_betaColumnIntervalUpper_spike_ge_rpow
        (k := 3) (d := d) a slack hd ha_nonneg
  have hMN_nonneg :
      0 ≤ lowerConcreteM R a slack d / (lowerConcreteN d : ℝ) :=
    div_nonneg hM_nonneg (le_of_lt hNpos)
  have hMsqrt_nonneg :
      0 ≤ lowerConcreteM R a slack d /
          Real.sqrt (lowerConcreteN d : ℝ) :=
    div_nonneg hM_nonneg (le_of_lt hsqrt_pos)
  rw [lowerConcreteMixedRuntimeWordBound_headQRestA_eq
    (R := R) (m := 2) (a := a) (slack := slack) (d := d)]
  simp only [Nat.reduceAdd, Nat.reduceSub, pow_one]
  have hprod_inner :
      256 * (256 * Real.sqrt (lowerConcreteN d : ℝ)) ≤
        (lowerConcreteM R a slack d / (lowerConcreteN d : ℝ)) *
          (lowerConcreteM R a slack d /
            Real.sqrt (lowerConcreteN d : ℝ)) := by
    exact mul_le_mul hMN hMsqrt (by positivity) hMN_nonneg
  have hleft_nonneg :
      0 ≤ a * (lowerConcreteN d : ℝ) ^ ((-1 : ℝ) + 1 / (3 : ℝ)) := by
    positivity
  have hright_nonneg :
      0 ≤ betaColumnIntervalUpper
        (betaColumnSpikeScale (lowerConcreteN d : ℝ) (spikeSpeed 3 d) a)
        (lowerConcreteDelta a slack d) :=
    le_trans hleft_nonneg hS
  have hinner :
      a * (lowerConcreteN d : ℝ) ^ ((-1 : ℝ) + 1 / (3 : ℝ)) *
          (256 * (256 * Real.sqrt (lowerConcreteN d : ℝ))) ≤
        betaColumnIntervalUpper
          (betaColumnSpikeScale (lowerConcreteN d : ℝ) (spikeSpeed 3 d) a)
          (lowerConcreteDelta a slack d) *
          ((lowerConcreteM R a slack d / (lowerConcreteN d : ℝ)) *
            (lowerConcreteM R a slack d /
              Real.sqrt (lowerConcreteN d : ℝ))) := by
    exact mul_le_mul hS hprod_inner (by positivity) hright_nonneg
  exact mul_le_mul_of_nonneg_left hinner (by positivity)

/-- For `x ≥ 1`, the scalar power factor appearing in the length-three
head-`Q`, rest-`A` runtime word is at least one. -/
theorem lower_headQRestA_two_powerFactor_ge_one {x : ℝ} (hx : 1 ≤ x) :
    1 ≤ x ^ 2 * x ^ ((-1 : ℝ) + 1 / (3 : ℝ)) * Real.sqrt x := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hsqrt : Real.sqrt x = x ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
  have hpow2 : x ^ 2 = x ^ (2 : ℝ) := by
    rw [← Real.rpow_natCast]
    norm_num
  calc
    1 ≤ x ^ ((2 : ℝ) + ((-1 : ℝ) + 1 / (3 : ℝ)) + 1 / 2) := by
      apply Real.one_le_rpow hx
      norm_num
    _ = x ^ (2 : ℝ) * x ^ ((-1 : ℝ) + 1 / (3 : ℝ)) *
          x ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_add hxpos
        ((2 : ℝ) + ((-1 : ℝ) + 1 / (3 : ℝ))) (1 / 2 : ℝ)]
      rw [Real.rpow_add hxpos (2 : ℝ) ((-1 : ℝ) + 1 / (3 : ℝ))]
    _ = x ^ 2 * x ^ ((-1 : ℝ) + 1 / (3 : ℝ)) * Real.sqrt x := by
      rw [hpow2, hsqrt]

/-- The explicit scalar lower bound for the distinguished length-three runtime
word is itself eventually bounded below by the positive constant `256*256*a`.

This is the final scalar diagnostic needed to show that the runtime-native
length-three mixed error is not an `o(1)` error. -/
theorem lower_headQRestA_two_scalar_eventually_ge_const
    {ε : ℝ} (hε : 0 < ε) :
    ∀ a : ℝ, spikeRoot 3 ε < a →
      ∀ᶠ d : ℕ in atTop,
        (256 : ℝ) * ((256 : ℝ) * a) ≤
          (lowerConcreteN d : ℝ) ^ 2 *
            (a * (lowerConcreteN d : ℝ) ^ ((-1 : ℝ) + 1 / (3 : ℝ)) *
              ((256 : ℝ) * ((256 : ℝ) *
                Real.sqrt (lowerConcreteN d : ℝ)))) := by
  intro a ha
  have hapos : 0 < a := by
    have hrootpos : 0 < spikeRoot 3 ε :=
      spikeRoot_pos (k := 3) (by norm_num) hε
    exact lt_trans hrootpos ha
  filter_upwards [eventually_gt_atTop 0] with d hd
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hNge : 1 ≤ (lowerConcreteN d : ℝ) := by
    simp [lowerConcreteN, Nat.cast_pow]
    nlinarith [sq_nonneg (d : ℝ), hdR]
  have hmain :
      1 ≤ (lowerConcreteN d : ℝ) ^ 2 *
          (lowerConcreteN d : ℝ) ^ ((-1 : ℝ) + 1 / (3 : ℝ)) *
          Real.sqrt (lowerConcreteN d : ℝ) :=
    lower_headQRestA_two_powerFactor_ge_one hNge
  have hcpos : 0 ≤ (256 : ℝ) * ((256 : ℝ) * a) := by positivity
  calc
    (256 : ℝ) * ((256 : ℝ) * a)
        = ((256 : ℝ) * ((256 : ℝ) * a)) * 1 := by ring
    _ ≤ ((256 : ℝ) * ((256 : ℝ) * a)) *
          ((lowerConcreteN d : ℝ) ^ 2 *
            (lowerConcreteN d : ℝ) ^ ((-1 : ℝ) + 1 / (3 : ℝ)) *
            Real.sqrt (lowerConcreteN d : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hmain hcpos
    _ = (lowerConcreteN d : ℝ) ^ 2 *
          (a * (lowerConcreteN d : ℝ) ^ ((-1 : ℝ) + 1 / (3 : ℝ)) *
            ((256 : ℝ) * ((256 : ℝ) *
              Real.sqrt (lowerConcreteN d : ℝ)))) := by ring

/-- Along the endpoint spike window, every mixed summand in the runtime
envelope is eventually nonnegative.

The proof uses only the already-verified eventual quadratic lower bound on
`lowerConcreteM` and the lower bound on the Beta interval upper endpoint. -/
theorem lowerConcreteMixedRuntimeWordBound_eventually_nonneg
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d : ℕ in atTop,
          ∀ w : Fin k → LocalExpansionLetter,
            localWordIsMixed w →
              0 ≤ lowerConcreteMixedRuntimeWordBound R k a slack d w := by
  intro a ha slack _hslack
  have hk0 : 0 < k := by omega
  have ha_nonneg : 0 ≤ a :=
    le_of_lt (lt_trans (spikeRoot_pos hk0 hε) ha)
  filter_upwards [eventually_gt_atTop 0,
    lowerConcreteM_eventually_ge_quadratic R a slack] with d hd hMquad w _hmix
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hNpos : 0 < (lowerConcreteN d : ℝ) := by
    simp [lowerConcreteN, pow_two, mul_pos hdR hdR]
  have hM_nonneg : 0 ≤ lowerConcreteM R a slack d := by
    have hquad_nonneg : 0 ≤ 256 * (d : ℝ) ^ 2 := by positivity
    exact le_trans hquad_nonneg hMquad
  have hS_nonneg :
      0 ≤ betaColumnIntervalUpper
        (betaColumnSpikeScale (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
        (lowerConcreteDelta a slack d) := by
    have hlower :=
      lowerConcrete_betaColumnIntervalUpper_spike_ge_rpow
        (k := k) (d := d) a slack hd ha_nonneg
    have hpow_nonneg :
        0 ≤ (lowerConcreteN d : ℝ) ^ ((-1 : ℝ) + 1 / (k : ℝ)) :=
      Real.rpow_nonneg (by positivity) _
    exact le_trans (mul_nonneg ha_nonneg hpow_nonneg) hlower
  by_cases hL0 : localWordLetterCount LocalExpansionLetter.L w = 0
  · by_cases hQ1 : localWordLetterCount LocalExpansionLetter.Q w = 1
    · rw [lowerConcreteMixedRuntimeWordBound_eq_oneQ_noL
        (R := R) (k := k) (a := a) (slack := slack) (d := d)
        (w := w) hL0 hQ1]
      positivity
    · by_cases hQtwo : 2 ≤ localWordLetterCount LocalExpansionLetter.Q w
      · rw [lowerConcreteMixedRuntimeWordBound_eq_manyQ_noL
          (R := R) (k := k) (a := a) (slack := slack) (d := d)
          (w := w) hL0 hQtwo]
        positivity
      · unfold lowerConcreteMixedRuntimeWordBound
        simp [hL0, hQ1, hQtwo]
  · unfold lowerConcreteMixedRuntimeWordBound
    simp [hL0]

/-- The runtime mixed error is eventually nonnegative in the endpoint spike
window. -/
theorem lowerConcreteMixedRuntimeWordError_eventually_nonneg
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d : ℕ in atTop,
          0 ≤ lowerConcreteMixedRuntimeWordError R k a slack d := by
  intro a ha slack hslack
  filter_upwards
    [lowerConcreteMixedRuntimeWordBound_eventually_nonneg
      (R := R) (k := k) (ε := ε) hk3 hε a ha slack hslack]
    with d hnonneg
  exact
    localMixedWordFilteredSum_nonneg
      (lowerConcreteMixedRuntimeWordBound R k a slack d)
      hnonneg

/-- Eventually, the full runtime mixed error dominates each individual mixed
runtime word.

This is the extraction adapter needed for future one-word lower-bound
obstructions: once a single mixed word is shown large, the whole finite error
is large as well. -/
theorem lowerConcreteMixedRuntimeWordBound_le_runtimeWordError_eventually
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d : ℕ in atTop,
          ∀ w : Fin k → LocalExpansionLetter,
            localWordIsMixed w →
              lowerConcreteMixedRuntimeWordBound R k a slack d w ≤
                lowerConcreteMixedRuntimeWordError R k a slack d := by
  intro a ha slack hslack
  filter_upwards
    [lowerConcreteMixedRuntimeWordBound_eventually_nonneg
      (R := R) (k := k) (ε := ε) hk3 hε a ha slack hslack]
    with d hnonneg w hmix
  unfold lowerConcreteMixedRuntimeWordError
  exact
    localMixedWordFilteredSum_single_le
      (lowerConcreteMixedRuntimeWordBound R k a slack d)
      hnonneg w hmix

/-- The full runtime mixed error eventually dominates the distinguished
head-`Q`, rest-`A` word. -/
theorem lowerConcreteMixedRuntimeWordError_eventually_ge_headQRestA
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {m : ℕ} {ε : ℝ} (hm3 : 3 ≤ m + 1) (hε : 0 < ε) :
    ∀ a : ℝ, spikeRoot (m + 1) ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d : ℕ in atTop,
          lowerConcreteMixedRuntimeWordBound R (m + 1) a slack d
              (lowerHeadQRestAWord m) ≤
            lowerConcreteMixedRuntimeWordError R (m + 1) a slack d := by
  intro a ha slack hslack
  have hm_pos : 0 < m := by omega
  filter_upwards
    [lowerConcreteMixedRuntimeWordBound_le_runtimeWordError_eventually
      (R := R) (k := m + 1) (ε := ε) hm3 hε a ha slack hslack]
    with d hle
  exact hle (lowerHeadQRestAWord m) (lowerHeadQRestAWord_mixed hm_pos)

/-- The full runtime mixed error eventually dominates the explicit scalar
lower bound coming from the distinguished length-three word. -/
theorem lowerConcreteMixedRuntimeWordError_three_eventually_ge_headQRestA_scalar
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ a : ℝ, spikeRoot 3 ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d : ℕ in atTop,
          (lowerConcreteN d : ℝ) ^ 2 *
              (a * (lowerConcreteN d : ℝ) ^ ((-1 : ℝ) + 1 / (3 : ℝ)) *
                (256 * (256 * Real.sqrt (lowerConcreteN d : ℝ)))) ≤
            lowerConcreteMixedRuntimeWordError R 3 a slack d := by
  intro a ha slack hslack
  filter_upwards
    [lowerConcreteMixedRuntimeWordBound_headQRestA_two_eventually_ge
      (R := R) (ε := ε) hε a ha slack hslack,
     lowerConcreteMixedRuntimeWordError_eventually_ge_headQRestA
      (R := R) (m := 2) (ε := ε) (by norm_num) hε a ha slack hslack]
    with d hscalar hword
  exact le_trans hscalar hword

/-- The runtime-native length-three mixed error cannot be an eventually
arbitrarily small scalar error.

This is a diagnostic theorem about the runtime event-native envelope: it shows
that the old route cannot close by treating the concrete background threshold
as a fixed small PT coefficient.  It is not the paper-facing PT mixed supplier,
which uses `lowerPartialTransposeMixedErrorD` instead. -/
theorem lowerConcreteMixedRuntimeWordError_three_not_eventuallySmall
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ a : ℝ, spikeRoot 3 ε < a →
      ∀ slack : ℝ, 0 < slack →
        ¬ (∀ η : ℝ, 0 < η →
          ∀ᶠ d : ℕ in atTop,
            lowerConcreteMixedRuntimeWordError R 3 a slack d ≤ η) := by
  intro a ha slack hslack hsmall
  have hapos : 0 < a := by
    have hrootpos : 0 < spikeRoot 3 ε :=
      spikeRoot_pos (k := 3) (by norm_num) hε
    exact lt_trans hrootpos ha
  let c : ℝ := (256 : ℝ) * ((256 : ℝ) * a)
  have hcpos : 0 < c := by
    dsimp [c]
    positivity
  have hle_half := hsmall (c / 2) (by positivity)
  have hge_const : ∀ᶠ d : ℕ in atTop,
      c ≤ lowerConcreteMixedRuntimeWordError R 3 a slack d := by
    filter_upwards
      [lower_headQRestA_two_scalar_eventually_ge_const (ε := ε) hε a ha,
       lowerConcreteMixedRuntimeWordError_three_eventually_ge_headQRestA_scalar
        (R := R) (ε := ε) hε a ha slack hslack]
      with d hconst hscalar
    exact le_trans hconst hscalar
  have hfalse : ∀ᶠ _d : ℕ in atTop, False := by
    filter_upwards [hge_const, hle_half] with d hge hle
    linarith
  simp only [Filter.Eventually, Set.setOf_false] at hfalse
  have hbot : (∅ : Set ℕ) ∈ (atTop : Filter ℕ) := hfalse
  have hne : (atTop : Filter ℕ).NeBot := inferInstance
  exact hne.ne ((Filter.empty_mem_iff_bot).mp hbot)

/-- The uniform runtime-smallness hypothesis used by the old length-three
runtime endpoint is impossible.

This packages `lowerConcreteMixedRuntimeWordError_three_not_eventuallySmall`
in the exact quantifier shape of the public runtime-smallness input: even after
allowing the parameter `a` to be chosen above `spikeRoot 3 ε`, the runtime
event-native mixed error cannot be uniformly `o(1)`. -/
theorem lowerConcreteMixedRuntimeWordError_three_not_uniformEventuallySmall
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {ε : ℝ} (hε : 0 < ε) :
    ¬ (∀ a : ℝ, spikeRoot 3 ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d : ℕ in atTop,
            lowerConcreteMixedRuntimeWordError R 3 a slack d ≤ η) := by
  intro hsmall
  let a : ℝ := spikeRoot 3 ε + 1
  have ha : spikeRoot 3 ε < a := by
    dsimp [a]
    linarith
  have hnot :=
    lowerConcreteMixedRuntimeWordError_three_not_eventuallySmall
      (R := R) (ε := ε) hε a ha 1 (by norm_num)
  exact hnot (hsmall a ha 1 (by norm_num))

/-- The distinguished length-three runtime word cannot be eventually dominated
by any fixed-`M` literal PT word budget.

This pinpoints the failed scalar-domination route: even before summing over
mixed words, the single `QAA` word is bounded below by a positive constant,
whereas the literal PT word budget is controlled by the `o(1)` error
`lowerPartialTransposeMixedErrorD 3 (a+slack) M`. -/
theorem lowerConcreteMixedRuntimeWordBound_headQRestA_two_not_eventually_le_PT
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {ε : ℝ} (hε : 0 < ε) (M : ℝ) (hM : 0 ≤ M) :
    ∀ a : ℝ, spikeRoot 3 ε < a →
      ∀ slack : ℝ, 0 < slack →
        ¬ (∀ᶠ d : ℕ in atTop,
          lowerConcreteMixedRuntimeWordBound R 3 a slack d
              (lowerHeadQRestAWord 2) ≤
            lowerPartialTransposeMixedWordBoundD 3 (a + slack) M d
              (lowerHeadQRestAWord 2)) := by
  intro a ha slack hslack hdom
  let c : ℝ := (256 : ℝ) * ((256 : ℝ) * a)
  have hapos : 0 < a := by
    have hrootpos : 0 < spikeRoot 3 ε :=
      spikeRoot_pos (k := 3) (by norm_num) hε
    exact lt_trans hrootpos ha
  have hcpos : 0 < c := by
    dsimp [c]
    positivity
  have hA : 0 ≤ a + slack := by linarith
  have hptSmall : ∀ᶠ d : ℕ in atTop,
      lowerPartialTransposeMixedErrorD 3 (a + slack) M d ≤ c / 2 :=
    lowerPartialTransposeMixedErrorD_eventually_le
      (k := 3) (by norm_num) (a + slack) M (c / 2) (by positivity)
  have hscalarConst :=
    lower_headQRestA_two_scalar_eventually_ge_const (ε := ε) hε a ha
  have hwordScalar :=
    lowerConcreteMixedRuntimeWordBound_headQRestA_two_eventually_ge
      (R := R) (ε := ε) hε a ha slack hslack
  have hbudget :=
    lowerConcreteMixedWordBudgetWithPTError_literal
      (R := R) (k := 3) (ε := ε) (M := M)
      (by norm_num) hε hM a ha slack hslack
  have hfalse : ∀ᶠ _d : ℕ in atTop, False := by
    filter_upwards [hscalarConst, hwordScalar, hdom, hbudget, hptSmall]
      with d hconst hword hdom_d hbudget_d hsmall_d
    have hsingle :
        lowerPartialTransposeMixedWordBoundD 3 (a + slack) M d
            (lowerHeadQRestAWord 2) ≤
          localMixedWordFilteredSum (k := 3)
            (lowerPartialTransposeMixedWordBoundD 3 (a + slack) M d) := by
      exact
        localMixedWordFilteredSum_single_le
          (lowerPartialTransposeMixedWordBoundD 3 (a + slack) M d)
          (fun w _hw =>
            lowerPartialTransposeMixedWordBoundD_nonneg
              (k := 3) (d := d) (A := a + slack) (M := M) hA hM w)
          (lowerHeadQRestAWord 2)
          (lowerHeadQRestAWord_mixed (by norm_num))
    have hptWordSmall :
        lowerPartialTransposeMixedWordBoundD 3 (a + slack) M d
            (lowerHeadQRestAWord 2) ≤ c / 2 :=
      le_trans hsingle (le_trans hbudget_d hsmall_d)
    have hruntimeSmall :
        lowerConcreteMixedRuntimeWordBound R 3 a slack d
            (lowerHeadQRestAWord 2) ≤ c / 2 :=
      le_trans hdom_d hptWordSmall
    have hconst_runtime :
        c ≤ lowerConcreteMixedRuntimeWordBound R 3 a slack d
            (lowerHeadQRestAWord 2) :=
      le_trans hconst hword
    linarith
  simp only [Filter.Eventually, Set.setOf_false] at hfalse
  have hbot : (∅ : Set ℕ) ∈ (atTop : Filter ℕ) := hfalse
  have hne : (atTop : Filter ℕ).NeBot := inferInstance
  exact hne.ne ((Filter.empty_mem_iff_bot).mp hbot)

/-- The length-three one-`Q` scale-comparison branch is impossible.

The one-`Q` scale comparison would force the distinguished `QAA` runtime word
to be eventually dominated by the literal fixed-`M` PT word budget.  The
previous obstruction shows exactly that this domination cannot hold.  Thus this
diagnostic scale-comparison route is not an unconditional lower-proof path. -/
theorem lowerConcretePTMixedWordOneQScaleComparison_three_not_uniform
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {ε : ℝ} (hε : 0 < ε) (M : ℝ) (hM : 0 ≤ M) :
    ¬ lowerConcretePTMixedWordOneQScaleComparison R 3 ε M := by
  intro hScale
  let a : ℝ := spikeRoot 3 ε + 1
  have ha : spikeRoot 3 ε < a := by
    dsimp [a]
    linarith
  have hslack : (0 : ℝ) < 1 := by norm_num
  have hA : 0 ≤ a + 1 := by
    have hrootpos : 0 < spikeRoot 3 ε :=
      spikeRoot_pos (k := 3) (by norm_num) hε
    dsimp [a]
    linarith
  have hdom : ∀ᶠ d : ℕ in atTop,
      lowerConcreteMixedRuntimeWordBound R 3 a 1 d
          (lowerHeadQRestAWord 2) ≤
        lowerPartialTransposeMixedWordBoundD 3 (a + 1) M d
          (lowerHeadQRestAWord 2) := by
    filter_upwards [hScale a ha 1 hslack] with d hScale_d
    have hterm :
        (a + 1) * M ^ (3 - 1) *
            ((d : ℝ) ^ 2) ^ ((-1 / 2 : ℝ) + 1 / (3 : ℝ)) ≤
          lowerPartialTransposeMixedWordBoundD 3 (a + 1) M d
            (lowerHeadQRestAWord 2) := by
      exact
        lowerPartialTransposeMixedWordBoundD_oneQ_term_le
          (k := 3) (d := d) (A := a + 1) (M := M)
          (w := lowerHeadQRestAWord 2) hA hM
          (lowerHeadQRestAWord_L_count 2)
          (lowerHeadQRestAWord_Q_count 2)
    have hscale' :
        lowerConcreteMixedRuntimeWordBound R 3 a 1 d
            (lowerHeadQRestAWord 2) ≤
          (a + 1) * M ^ (3 - 1) *
            ((d : ℝ) ^ 2) ^ ((-1 / 2 : ℝ) + 1 / (3 : ℝ)) := by
      rw [lowerConcreteMixedRuntimeWordBound_headQRestA_eq
        (R := R) (m := 2) (a := a) (slack := 1) (d := d)]
      simpa using hScale_d
    exact le_trans hscale' hterm
  exact
    (lowerConcreteMixedRuntimeWordBound_headQRestA_two_not_eventually_le_PT
      (R := R) (ε := ε) hε M hM a ha 1 hslack) hdom

/-- No nonnegative fixed PT envelope can make the length-three one-`Q`
scale-comparison branch true. -/
theorem lowerConcretePTMixedWordOneQScaleComparison_three_not_uniform_noM
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {ε : ℝ} (hε : 0 < ε) :
    ¬ ∃ M : ℝ, 0 ≤ M ∧
      lowerConcretePTMixedWordOneQScaleComparison R 3 ε M := by
  rintro ⟨M, hM, hScale⟩
  exact
    lowerConcretePTMixedWordOneQScaleComparison_three_not_uniform
      (R := R) (ε := ε) hε M hM hScale

/-- The full length-three fixed-`M` scale-comparison packet is impossible.

The public scale-comparison endpoint consumes both the one-`Q` and many-`Q`
scale comparisons.  At length three the first component is already
contradictory, so the whole packet cannot be used as an unconditional lower
route. -/
theorem lowerConcretePTMixedWordScaleComparisons_three_not_uniform
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {ε : ℝ} (hε : 0 < ε) (M : ℝ) (hM : 0 ≤ M) :
    ¬ (lowerConcretePTMixedWordOneQScaleComparison R 3 ε M ∧
      lowerConcretePTMixedWordManyQScaleComparison R 3 ε M) := by
  intro hScales
  exact
    lowerConcretePTMixedWordOneQScaleComparison_three_not_uniform
      (R := R) (ε := ε) hε M hM hScales.1

/-- No nonnegative fixed PT envelope can make the full length-three
scale-comparison packet true. -/
theorem lowerConcretePTMixedWordScaleComparisons_three_not_uniform_noM
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {ε : ℝ} (hε : 0 < ε) :
    ¬ ∃ M : ℝ, 0 ≤ M ∧
      lowerConcretePTMixedWordOneQScaleComparison R 3 ε M ∧
      lowerConcretePTMixedWordManyQScaleComparison R 3 ε M := by
  rintro ⟨M, hM, hScales⟩
  exact
    lowerConcretePTMixedWordScaleComparisons_three_not_uniform
      (R := R) (ε := ε) hε M hM hScales

/-- The mixed-only runtime-to-PT domination hypothesis is already impossible
at length three.

This is the exact public input shape used by
`mixed_noL_atLeastTwoQ_ge_neg_errMix_of_runtimeEnvelope_domination_on_mixed`,
specialized to `k = 3`: the single mixed word `QAA` contradicts any eventual
domination by a fixed-`M` literal PT word budget. -/
theorem lowerConcreteMixedRuntimeWordDominationOnMixed_three_not_uniform
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {ε : ℝ} (hε : 0 < ε) (M : ℝ) (hM : 0 ≤ M) :
    ¬ (∀ a : ℝ, spikeRoot 3 ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ w : Fin 3 → LocalExpansionLetter,
            localWordIsMixed w →
              lowerConcreteMixedRuntimeWordBound R 3 a slack d w ≤
                lowerPartialTransposeMixedWordBoundD 3 (a + slack) M d w) := by
  intro hDom
  let a : ℝ := spikeRoot 3 ε + 1
  have ha : spikeRoot 3 ε < a := by
    dsimp [a]
    linarith
  have hslack : (0 : ℝ) < 1 := by norm_num
  have hQAA :
      ∀ᶠ d : ℕ in atTop,
        lowerConcreteMixedRuntimeWordBound R 3 a 1 d
            (lowerHeadQRestAWord 2) ≤
          lowerPartialTransposeMixedWordBoundD 3 (a + 1) M d
            (lowerHeadQRestAWord 2) := by
    filter_upwards [hDom a ha 1 hslack] with d hd
    exact hd (lowerHeadQRestAWord 2) (lowerHeadQRestAWord_mixed (by norm_num))
  exact
    (lowerConcreteMixedRuntimeWordBound_headQRestA_two_not_eventually_le_PT
      (R := R) (ε := ε) hε M hM a ha 1 hslack) hQAA

/-- The runtime-native mixed-word budget is tautological: its error is exactly
the filtered finite sum of the runtime word envelope. -/
theorem lowerConcreteMixedWordBudgetWithRuntimeWordError
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (ε : ℝ) :
    lowerConcreteMixedWordBudgetWithError R k ε
      (lowerConcreteMixedRuntimeWordBound R k)
      (lowerConcreteMixedRuntimeWordError R k) := by
  intro _a _ha _slack _hslack
  exact Filter.Eventually.of_forall (fun _d => le_rfl)

/-- Sphere-supported local-expansion envelope with the exact runtime-native
mixed-word error.

This closes the mixed deterministic part without the impossible fixed-`M`
scalar leaves `hOneScalar` and `hManyScalar`. Any later endpoint theorem that
needs an `o(1)` mixed error must either work with this explicit runtime error
or supply a sharper fixed-scale background estimate replacing the current
`lowerConcreteM` event. -/
theorem lower_concreteMixedLocalExpansionEnvelopeOnSphereWithRuntimeWordError
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < ε) :
    lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithError R k ε
      (lowerConcreteMixedRuntimeWordError R k) := by
  have hk : 1 ≤ k := by omega
  refine
    lower_concreteMixedLocalExpansionEnvelopeOnSphereWithError_of_wordBounds
      (R := R) (k := k) (ε := ε) hk
      (bound := lowerConcreteMixedRuntimeWordBound R k)
      (errMix := lowerConcreteMixedRuntimeWordError R k)
      ?_ ?_
  · exact
      lowerConcreteMixedWordPointwiseBoundOnSphere_runtimeEnvelope
        (R := R) (k := k) (ε := ε) hk3 hε
  · exact lowerConcreteMixedWordBudgetWithRuntimeWordError R k ε

/-- One-sided mixed lower supplier on the Frobenius sphere with the exact
runtime-native mixed-word error. -/
theorem lower_mixedLowerOnSphere_concreteChoices_of_runtimeWordError
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < ε) :
    lowerConcreteMixedLowerBoundOnSphere R lowerConcreteCanonicalDirection
      (lowerConcreteM R)
      lowerConcreteTau
      (fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
      (lowerConcreteMixedRuntimeWordError R k) k ε := by
  exact
    lower_mixedLowerOnSphere_concreteChoices_of_localExpansionEnvelopeOnSphereWithError
      (R := R) (k := k) (ε := ε)
      (errMix := lowerConcreteMixedRuntimeWordError R k)
      (lower_concreteMixedLocalExpansionEnvelopeOnSphereWithRuntimeWordError
        (R := R) (k := k) (ε := ε) hk3 hε)

/-- Paper-facing mixed-supplier frontier for the no-`L`, at-least-two-`Q`
partial-transpose route, with the concrete endpoint error
`errMixPT k (a + slack) M d`.

This name intentionally points at the sphere-supported local-expansion envelope:
the analytic one-`Q` and many-`Q` estimates are already in this file, while the
remaining theorem-strength input is the finite cyclic normal-form/budget
supplier for the actual words. -/
def mixed_noL_atLeastTwoQ_ge_neg_errMix
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (ε M : ℝ) : Prop :=
  lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithError R k ε
    (fun a slack d => lowerPartialTransposeMixedErrorD k (a + slack) M d)

/-- The paper-facing mixed-supplier name is exactly the existing
sphere-supported PT local-expansion envelope with the corrected concrete error. -/
theorem mixed_noL_atLeastTwoQ_ge_neg_errMix_iff_lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithPTError
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (ε M : ℝ) :
    mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M ↔
      lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithError R k ε
        (fun a slack d => lowerPartialTransposeMixedErrorD k (a + slack) M d) := by
  rfl

/-- Build the paper-facing PT mixed supplier from the remaining pointwise
word-level estimate.

The finite coefficient budget and the scalar smallness of
`lowerPartialTransposeMixedErrorD` are already closed elsewhere in this file.
So, once the word-by-word PT estimate is available with the literal envelope
`lowerPartialTransposeMixedWordBoundD`, the mixed supplier itself is automatic.
-/
theorem mixed_noL_atLeastTwoQ_ge_neg_errMix_of_pointwiseWordBound
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε M : ℝ}
    (hk : 1 ≤ k) (hε : 0 < ε) (hM : 0 ≤ M)
    (hWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k ε
        (fun a slack d => lowerPartialTransposeMixedWordBoundD k (a + slack) M d)) :
    mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M := by
  refine
    lower_concreteMixedLocalExpansionEnvelopeOnSphereWithError_of_wordBounds
      (R := R) (k := k) (ε := ε) hk
      (bound := fun a slack d => lowerPartialTransposeMixedWordBoundD k (a + slack) M d)
      (errMix := fun a slack d => lowerPartialTransposeMixedErrorD k (a + slack) M d)
      hWord ?_
  exact lowerConcreteMixedWordBudgetWithPTError_literal
    (R := R) (k := k) (ε := ε) (M := M) hk hε hM

/-- Build the paper-facing PT mixed supplier from the runtime event-native
word envelope plus an eventual domination by the literal PT envelope.

This isolates the last genuinely mixed-specific comparison step.  The
word-by-word runtime estimate from the favourable event and the finite PT
budget aggregation are already closed in this file; once the runtime envelope
is shown to sit below the cleaner fixed-parameter PT bound, the packaged
mixed supplier follows automatically. -/
theorem mixed_noL_atLeastTwoQ_ge_neg_errMix_of_runtimeEnvelope_domination
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε M : ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < ε) (hM : 0 ≤ M)
    (hDom :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ w : Fin k → LocalExpansionLetter,
              lowerConcreteMixedRuntimeWordBound R k a slack d w ≤
                lowerPartialTransposeMixedWordBoundD k (a + slack) M d w) :
    mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M := by
  have hk : 1 ≤ k := by omega
  have hRuntime :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k ε
        (lowerConcreteMixedRuntimeWordBound R k) :=
    lowerConcreteMixedWordPointwiseBoundOnSphere_runtimeEnvelope
      (R := R) (k := k) (ε := ε) hk3 hε
  have hWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k ε
        (fun a slack d => lowerPartialTransposeMixedWordBoundD k (a + slack) M d) :=
    lowerConcreteMixedWordPointwiseBoundOnSphere_of_runtimeEnvelope_domination
      (R := R) (k := k) (ε := ε) hRuntime hDom
  exact
    mixed_noL_atLeastTwoQ_ge_neg_errMix_of_pointwiseWordBound
      (R := R) (k := k) (ε := ε) (M := M) hk hε hM hWord

/-- Mixed-only variant of
`mixed_noL_atLeastTwoQ_ge_neg_errMix_of_runtimeEnvelope_domination`.

This is the endpoint-facing shape that matches the finite mixed-word filtered
sum: the domination is required exactly on mixed words, not on the pure `A` or
pure `Q` fibers handled elsewhere in the expansion. -/
theorem mixed_noL_atLeastTwoQ_ge_neg_errMix_of_runtimeEnvelope_domination_on_mixed
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε M : ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < ε) (hM : 0 ≤ M)
    (hDom :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                lowerConcreteMixedRuntimeWordBound R k a slack d w ≤
                  lowerPartialTransposeMixedWordBoundD k (a + slack) M d w) :
    mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M := by
  have hk : 1 ≤ k := by omega
  have hRuntime :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k ε
        (lowerConcreteMixedRuntimeWordBound R k) :=
    lowerConcreteMixedWordPointwiseBoundOnSphere_runtimeEnvelope
      (R := R) (k := k) (ε := ε) hk3 hε
  have hWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k ε
        (fun a slack d => lowerPartialTransposeMixedWordBoundD k (a + slack) M d) :=
    lowerConcreteMixedWordPointwiseBoundOnSphere_of_runtimeEnvelope_domination_on_mixed
      (R := R) (k := k) (ε := ε) hRuntime hDom
  exact
    mixed_noL_atLeastTwoQ_ge_neg_errMix_of_pointwiseWordBound
      (R := R) (k := k) (ε := ε) (M := M) hk hε hM hWord

/-- Use the paper-facing mixed-supplier frontier as the concrete PT envelope
input expected by the lower endpoint. -/
theorem lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithPTError_of_mixed_noL_atLeastTwoQ_ge_neg_errMix
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (ε M : ℝ)
    (hMixed : mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M) :
    lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithError R k ε
      (fun a slack d => lowerPartialTransposeMixedErrorD k (a + slack) M d) :=
  hMixed

/-- Named-frontier version of the mixed supplier. -/
theorem lower_mixedLower_concreteChoices_of_localExpansionEnvelope
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ}
    (hEnvelope : lowerConcreteMixedLocalExpansionEnvelope R k ε) :
    lowerConcreteMixedLowerBound R lowerConcreteCanonicalDirection
      (lowerConcreteM R)
      lowerConcreteTau
      (fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
      (lowerConcreteMixedError R k ε) k ε :=
  lower_mixedLower_concreteChoices_of_eventual_localExpansionEnvelope
    (R := R) (k := k) (ε := ε) hEnvelope

/-!
Retired route.

The old no-input theorem path attempted to derive the pointwise mixed lower
bound directly from `hFav`.  The active lower frontier now keeps the mixed
input explicit as `lowerConcreteMixedLocalExpansionEnvelope`, and the mixed
supplier is provided by
`lower_mixedLower_concreteChoices_of_localExpansionEnvelope`.
-/

end AppendixB
