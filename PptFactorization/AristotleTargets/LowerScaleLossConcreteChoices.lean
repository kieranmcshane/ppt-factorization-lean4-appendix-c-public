import PptFactorization.AristotleTargets.LowerMixedLowerConcreteChoices

/-!
Aristotle handoff for the lower-bound closure.

Target: close the concrete background scale-loss supplier used as `hScaleLoss`
in
`AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_concreteScalarChoices`.

Protected file: do not edit `PptFactorization/AppendixBSpikeLowerBound.lean`.

Allowed inputs/context: use existing local lemmas from
`PptFactorization.AppendixBLowerBoundClosure`,
`PptFactorization.AppendixBWishartBridge`, and mathlib.  Do not add axioms,
`opaque`, `unsafe`, new theorem parameters, or weaken the statement.

PROVIDED SOLUTION:
Try to prove the scale-loss inequality from the exact deleted-column scaling
identity, the definition of `backgroundTypicalSet`, the common operator
threshold `lowerConcreteM R`, the mean-centered deleted-background center
`lowerConcreteDeletedBackgroundMean R k`, and the concrete choices in
`AppendixBLowerBoundClosure`.  If the concrete `O(1/d)` scale error is too
small, report the exact replacement error definition needed and the first
missing local lemma rather than weakening this theorem.  Preserve the theorem
statement exactly.
-/
namespace AppendixB

open PptFactorization.RandomMatrixModel
open Filter
open scoped Topology Matrix.Norms.Frobenius

theorem lower_backgroundMomentValue_upper_of_backgroundTypicalSet
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {N M τ mean : ℝ} {k : ℕ} {Y : SampleMatrix p q σ}
    (hY :
      Y ∈ backgroundTypicalSet
        (p := p) (q := q) (σ := σ) N M τ mean k) :
    backgroundMomentValue (p := p) (q := q) (σ := σ) N k Y ≤
      mean + τ := by
  have hAbs :=
    backgroundTypicalSet_moment_bound
      (p := p) (q := q) (σ := σ)
      (N := N) (M := M) (τ := τ) (mean := mean)
      (k := k) hY
  have hUpper := (abs_le.mp hAbs).2
  linarith

set_option linter.unusedSectionVars false in
theorem lower_frobeniusNorm_sq_eq_entry_sum
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
  · exact Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun α _ => by positivity

theorem lower_sampleColumnMass_add_complement_frobeniusNorm_sq
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    (X : SampleMatrix p q σ) (α₀ : σ) :
    sampleColumnMass (p := p) (q := q) (σ := σ) X α₀ +
      frobeniusNorm (p := p) (q := q) (σ := σ)
        (sampleColumnComplement (p := p) (q := q) (σ := σ) X α₀) ^ 2 =
      frobeniusNorm (p := p) (q := q) (σ := σ) X ^ 2 := by
  unfold sampleColumnMass
  rw [lower_frobeniusNorm_sq_eq_entry_sum
        (p := p) (q := q) (σ := σ)
        (A := sampleColumnPart (p := p) (q := q) (σ := σ) X α₀)]
  rw [lower_frobeniusNorm_sq_eq_entry_sum
        (p := p) (q := q) (σ := σ)
        (A := sampleColumnComplement (p := p) (q := q) (σ := σ) X α₀)]
  rw [lower_frobeniusNorm_sq_eq_entry_sum
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

theorem lower_sampleColumnComplement_frobeniusNorm_sq_eq_one_sub_mass_of_norm_one
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    {X : SampleMatrix p q σ} {α₀ : σ}
    (hX : frobeniusNorm (p := p) (q := q) (σ := σ) X = 1) :
    frobeniusNorm (p := p) (q := q) (σ := σ)
        (sampleColumnComplement (p := p) (q := q) (σ := σ) X α₀) ^ 2 =
      1 - sampleColumnMass (p := p) (q := q) (σ := σ) X α₀ := by
  have hsum :=
    lower_sampleColumnMass_add_complement_frobeniusNorm_sq
      (p := p) (q := q) (σ := σ) X α₀
  rw [hX] at hsum
  nlinarith

theorem lower_sampleColumnComplement_frobeniusNorm_pow_eq_one_sub_mass_pow_of_norm_one
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    {X : SampleMatrix p q σ} {α₀ : σ} (k : ℕ)
    (hX : frobeniusNorm (p := p) (q := q) (σ := σ) X = 1) :
    frobeniusNorm (p := p) (q := q) (σ := σ)
        (sampleColumnComplement (p := p) (q := q) (σ := σ) X α₀) ^ (2 * k) =
      (1 - sampleColumnMass (p := p) (q := q) (σ := σ) X α₀) ^ k := by
  calc
    frobeniusNorm (p := p) (q := q) (σ := σ)
        (sampleColumnComplement (p := p) (q := q) (σ := σ) X α₀) ^ (2 * k)
        = (frobeniusNorm (p := p) (q := q) (σ := σ)
            (sampleColumnComplement (p := p) (q := q) (σ := σ) X α₀) ^ 2) ^ k := by
            exact
              pow_mul
                (frobeniusNorm (p := p) (q := q) (σ := σ)
                  (sampleColumnComplement (p := p) (q := q) (σ := σ) X α₀)) 2 k
    _ = (1 - sampleColumnMass (p := p) (q := q) (σ := σ) X α₀) ^ k := by
            rw [lower_sampleColumnComplement_frobeniusNorm_sq_eq_one_sub_mass_of_norm_one
              (p := p) (q := q) (σ := σ) hX]

theorem lower_sampleColumnMass_le_one_of_frobeniusNorm_eq_one
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    {X : SampleMatrix p q σ} {α₀ : σ}
    (hX : frobeniusNorm (p := p) (q := q) (σ := σ) X = 1) :
    sampleColumnMass (p := p) (q := q) (σ := σ) X α₀ ≤ 1 := by
  have hsum :=
    lower_sampleColumnMass_add_complement_frobeniusNorm_sq
      (p := p) (q := q) (σ := σ) X α₀
  rw [hX] at hsum
  have hcomp_nonneg :
      0 ≤ frobeniusNorm (p := p) (q := q) (σ := σ)
        (sampleColumnComplement (p := p) (q := q) (σ := σ) X α₀) ^ 2 :=
    sq_nonneg _
  nlinarith

theorem lower_one_sub_one_sub_sampleColumnMass_pow_nonneg_of_norm_one
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    {X : SampleMatrix p q σ} {α₀ : σ} (k : ℕ)
    (hX : frobeniusNorm (p := p) (q := q) (σ := σ) X = 1) :
    0 ≤ 1 - (1 - sampleColumnMass (p := p) (q := q) (σ := σ) X α₀) ^ k := by
  have hmass_nonneg :=
    sampleColumnMass_nonneg (p := p) (q := q) (σ := σ) X α₀
  have hmass_le_one :=
    lower_sampleColumnMass_le_one_of_frobeniusNorm_eq_one
      (p := p) (q := q) (σ := σ) (α₀ := α₀) hX
  have hbase_nonneg :
      0 ≤ 1 - sampleColumnMass (p := p) (q := q) (σ := σ) X α₀ := by
    linarith
  have hbase_le_one :
      1 - sampleColumnMass (p := p) (q := q) (σ := σ) X α₀ ≤ 1 := by
    linarith
  have hpow_le_one :
      (1 - sampleColumnMass (p := p) (q := q) (σ := σ) X α₀) ^ k ≤ 1 :=
    pow_le_one₀ hbase_nonneg hbase_le_one
  linarith

/-!
The pointwise scale-loss supplier is not a consequence of typicality alone:
one also needs a concrete estimate for the mass-loss factor
`1 - ‖X_{≠α₀}‖^(2k)`.  The next lemma records the closed bookkeeping around
that fact.  Once the factor is known to be nonnegative and its product with the
typical moment upper bound fits the concrete error budget, the required
scale-loss inequality follows.
-/
theorem lower_backgroundScaleLoss_pointwise_concreteChoices_of_upper_budget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (ε a slack : ℝ) (d : ℕ)
    (hs : 0 < R.sample d)
    (X : SampleMatrix (Fin d) (Fin d) (Fin (R.sample d)))
    (hTypical :
      sampleColumnComplementNormalized
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          X (⟨0, hs⟩ : Fin (R.sample d)) ∈
        backgroundTypicalSet
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (lowerConcreteN d) (lowerConcreteM R a slack d)
          (lowerConcreteTau a slack d)
          (lowerConcreteDeletedBackgroundMean R k d) k)
    (hFactorNonneg :
      0 ≤
        1 -
          frobeniusNorm
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              (sampleColumnComplement
                (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                X (⟨0, hs⟩ : Fin (R.sample d))) ^ (2 * k))
    (hBudget :
      (lowerConcreteDeletedBackgroundMean R k d +
          lowerConcreteTau a slack d) *
        (1 -
          frobeniusNorm
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              (sampleColumnComplement
                (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                X (⟨0, hs⟩ : Fin (R.sample d))) ^ (2 * k)) ≤
        lowerConcreteScaleError R k ε a slack d) :
    backgroundMomentValue
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        (lowerConcreteN d) k
        (sampleColumnComplementNormalized
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          X (⟨0, hs⟩ : Fin (R.sample d))) *
      (1 -
        frobeniusNorm
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            (sampleColumnComplement
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              X (⟨0, hs⟩ : Fin (R.sample d))) ^ (2 * k)) ≤
        lowerConcreteScaleError R k ε a slack d := by
  have hMomentUpper :
      backgroundMomentValue
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (lowerConcreteN d) k
          (sampleColumnComplementNormalized
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            X (⟨0, hs⟩ : Fin (R.sample d))) ≤
        lowerConcreteDeletedBackgroundMean R k d +
          lowerConcreteTau a slack d :=
    lower_backgroundMomentValue_upper_of_backgroundTypicalSet
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      (N := lowerConcreteN d) (M := lowerConcreteM R a slack d)
      (τ := lowerConcreteTau a slack d)
      (mean := lowerConcreteDeletedBackgroundMean R k d)
      (k := k)
      (Y :=
        sampleColumnComplementNormalized
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          X (⟨0, hs⟩ : Fin (R.sample d)))
      hTypical
  exact (mul_le_mul_of_nonneg_right hMomentUpper hFactorNonneg).trans hBudget

theorem lower_backgroundScaleLoss_pointwise_concreteChoices_of_sphere_mass_budget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (ε a slack : ℝ) (d : ℕ)
    (hs : 0 < R.sample d)
    (X : SampleMatrix (Fin d) (Fin d) (Fin (R.sample d)))
    (hTypical :
      sampleColumnComplementNormalized
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          X (⟨0, hs⟩ : Fin (R.sample d)) ∈
        backgroundTypicalSet
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (lowerConcreteN d) (lowerConcreteM R a slack d)
          (lowerConcreteTau a slack d)
          (lowerConcreteDeletedBackgroundMean R k d) k)
    (hSphere :
      frobeniusNorm (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)) X = 1)
    (hBudget :
      (lowerConcreteDeletedBackgroundMean R k d +
          lowerConcreteTau a slack d) *
        (1 -
          (1 - sampleColumnMass
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            X (⟨0, hs⟩ : Fin (R.sample d))) ^ k) ≤
        lowerConcreteScaleError R k ε a slack d) :
    backgroundMomentValue
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        (lowerConcreteN d) k
        (sampleColumnComplementNormalized
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          X (⟨0, hs⟩ : Fin (R.sample d))) *
      (1 -
        frobeniusNorm
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            (sampleColumnComplement
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              X (⟨0, hs⟩ : Fin (R.sample d))) ^ (2 * k)) ≤
        lowerConcreteScaleError R k ε a slack d := by
  have hFactorEq :=
    lower_sampleColumnComplement_frobeniusNorm_pow_eq_one_sub_mass_pow_of_norm_one
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      (α₀ := (⟨0, hs⟩ : Fin (R.sample d))) (X := X) k hSphere
  refine lower_backgroundScaleLoss_pointwise_concreteChoices_of_upper_budget
    (R := R) (k := k) (ε := ε) (a := a) (slack := slack)
    (d := d) hs X hTypical ?_ ?_
  · rw [hFactorEq]
    exact lower_one_sub_one_sub_sampleColumnMass_pow_nonneg_of_norm_one
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      (α₀ := (⟨0, hs⟩ : Fin (R.sample d))) (X := X) k hSphere
  · simpa [hFactorEq] using hBudget

set_option linter.unusedSectionVars false in
theorem lower_one_sub_one_sub_sampleColumnMass_pow_le_of_mass_le
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    {X : SampleMatrix p q σ} {α₀ : σ} (k : ℕ) {r : ℝ}
    (hr1 : r ≤ 1)
    (hmass_le : sampleColumnMass (p := p) (q := q) (σ := σ) X α₀ ≤ r) :
    1 - (1 - sampleColumnMass (p := p) (q := q) (σ := σ) X α₀) ^ k ≤
      1 - (1 - r) ^ k := by
  have hbase_r_nonneg : 0 ≤ 1 - r := by linarith
  have hbase_le :
      1 - r ≤ 1 - sampleColumnMass (p := p) (q := q) (σ := σ) X α₀ := by
    linarith
  have hpow_le :
      (1 - r) ^ k ≤
        (1 - sampleColumnMass (p := p) (q := q) (σ := σ) X α₀) ^ k :=
    pow_le_pow_left₀ hbase_r_nonneg hbase_le k
  linarith

/-!
Corrected deterministic scale-loss replacement.

The unrestricted target below is too strong: typicality of the normalized
deleted background controls only its direction, not the scale of the deleted
columns.  This replacement adds the two deterministic hypotheses that make the
statement true in the spherical one-column model: full Frobenius normalization
of `X` and an upper bound on the distinguished-column mass.
-/
theorem lower_backgroundScaleLoss_pointwise_concreteChoices_of_sphere_mass_upper_budget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (ε a slack r : ℝ) (d : ℕ)
    (hs : 0 < R.sample d)
    (X : SampleMatrix (Fin d) (Fin d) (Fin (R.sample d)))
    (hTypical :
      sampleColumnComplementNormalized
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          X (⟨0, hs⟩ : Fin (R.sample d)) ∈
        backgroundTypicalSet
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (lowerConcreteN d) (lowerConcreteM R a slack d)
          (lowerConcreteTau a slack d)
          (lowerConcreteDeletedBackgroundMean R k d) k)
    (hSphere :
      frobeniusNorm (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)) X = 1)
    (hr1 : r ≤ 1)
    (hMassUpper :
      sampleColumnMass
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        X (⟨0, hs⟩ : Fin (R.sample d)) ≤ r)
    (hBudget :
      max (lowerConcreteDeletedBackgroundMean R k d + lowerConcreteTau a slack d) 0 *
        (1 - (1 - r) ^ k) ≤
        lowerConcreteScaleError R k ε a slack d) :
    backgroundMomentValue
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        (lowerConcreteN d) k
        (sampleColumnComplementNormalized
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          X (⟨0, hs⟩ : Fin (R.sample d))) *
      (1 -
        frobeniusNorm
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            (sampleColumnComplement
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              X (⟨0, hs⟩ : Fin (R.sample d))) ^ (2 * k)) ≤
        lowerConcreteScaleError R k ε a slack d := by
  let α₀ : Fin (R.sample d) := ⟨0, hs⟩
  let M : ℝ := lowerConcreteDeletedBackgroundMean R k d + lowerConcreteTau a slack d
  let actual : ℝ :=
    1 -
      frobeniusNorm
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (sampleColumnComplement
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)) X α₀) ^ (2 * k)
  have hMomentUpper :
      backgroundMomentValue
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (lowerConcreteN d) k
          (sampleColumnComplementNormalized
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)) X α₀) ≤ M := by
    dsimp [M]
    exact lower_backgroundMomentValue_upper_of_backgroundTypicalSet
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      (N := lowerConcreteN d) (M := lowerConcreteM R a slack d)
      (τ := lowerConcreteTau a slack d)
      (mean := lowerConcreteDeletedBackgroundMean R k d) (k := k)
      (Y := sampleColumnComplementNormalized
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)) X α₀)
      hTypical
  have hFactorEq :
      actual =
        1 -
          (1 - sampleColumnMass
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)) X α₀) ^ k := by
    dsimp [actual]
    rw [lower_sampleColumnComplement_frobeniusNorm_pow_eq_one_sub_mass_pow_of_norm_one
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      (α₀ := α₀) (X := X) k hSphere]
  have hActualNonneg : 0 ≤ actual := by
    rw [hFactorEq]
    exact lower_one_sub_one_sub_sampleColumnMass_pow_nonneg_of_norm_one
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      (α₀ := α₀) (X := X) k hSphere
  have hFactorLe : actual ≤ 1 - (1 - r) ^ k := by
    rw [hFactorEq]
    exact lower_one_sub_one_sub_sampleColumnMass_pow_le_of_mass_le
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      (α₀ := α₀) (X := X) k hr1 hMassUpper
  have hMleMax : M ≤ max M 0 := le_max_left M 0
  have hMaxNonneg : 0 ≤ max M 0 := le_max_right M 0
  calc
    backgroundMomentValue
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        (lowerConcreteN d) k
        (sampleColumnComplementNormalized
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)) X α₀) * actual
        ≤ M * actual := mul_le_mul_of_nonneg_right hMomentUpper hActualNonneg
    _ ≤ max M 0 * actual := mul_le_mul_of_nonneg_right hMleMax hActualNonneg
    _ ≤ max M 0 * (1 - (1 - r) ^ k) :=
          mul_le_mul_of_nonneg_left hFactorLe hMaxNonneg
    _ ≤ lowerConcreteScaleError R k ε a slack d := hBudget

theorem lower_betaColumnIntervalSet_right_le {q δ R : ℝ} :
    R ∈ betaColumnIntervalSet q δ → R ≤ betaColumnIntervalUpper q δ := by
  intro h
  exact h.2

/-!
Specialization of the corrected scale-loss bridge to the Beta mass interval.

This is the form used by the one-column favorable event: the Beta interval
supplies the needed upper bound on the distinguished-column mass.  Its lower
endpoint is irrelevant for this scale-transfer step.
-/
theorem lower_backgroundScaleLoss_pointwise_concreteChoices_of_sphere_betaInterval_budget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (ε a slack q δ : ℝ) (d : ℕ)
    (hs : 0 < R.sample d)
    (X : SampleMatrix (Fin d) (Fin d) (Fin (R.sample d)))
    (hTypical :
      sampleColumnComplementNormalized
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          X (⟨0, hs⟩ : Fin (R.sample d)) ∈
        backgroundTypicalSet
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (lowerConcreteN d) (lowerConcreteM R a slack d)
          (lowerConcreteTau a slack d)
          (lowerConcreteDeletedBackgroundMean R k d) k)
    (hSphere :
      frobeniusNorm (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)) X = 1)
    (hMass :
      sampleColumnMass
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        X (⟨0, hs⟩ : Fin (R.sample d)) ∈ betaColumnIntervalSet q δ)
    (hUpperLeOne : betaColumnIntervalUpper q δ ≤ 1)
    (hBudget :
      max (lowerConcreteDeletedBackgroundMean R k d + lowerConcreteTau a slack d) 0 *
        (1 - (1 - betaColumnIntervalUpper q δ) ^ k) ≤
        lowerConcreteScaleError R k ε a slack d) :
    backgroundMomentValue
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        (lowerConcreteN d) k
        (sampleColumnComplementNormalized
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          X (⟨0, hs⟩ : Fin (R.sample d))) *
      (1 -
        frobeniusNorm
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            (sampleColumnComplement
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              X (⟨0, hs⟩ : Fin (R.sample d))) ^ (2 * k)) ≤
        lowerConcreteScaleError R k ε a slack d := by
  exact lower_backgroundScaleLoss_pointwise_concreteChoices_of_sphere_mass_upper_budget
    (R := R) (k := k) (ε := ε) (a := a) (slack := slack)
    (r := betaColumnIntervalUpper q δ) (d := d) hs X hTypical hSphere
    hUpperLeOne (lower_betaColumnIntervalSet_right_le hMass) hBudget

/-!
Pointwise background contribution lower bound with the corrected scale-loss
hypotheses.

This is the event-local replacement for the obsolete unrestricted
`lowerConcreteBackgroundScaleLoss` supplier: on a spherical matrix whose
distinguished-column mass lies in the Beta interval, the normalized
background-typical lower bound transfers to the unnormalized deleted-column
background contribution with the concrete error `lowerConcreteScaleError`.
-/
theorem lower_columnBackgroundContribution_lower_of_sphere_betaInterval_budget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (ε a slack q δ : ℝ) (d : ℕ)
    (hs : 0 < R.sample d)
    (X : SampleMatrix (Fin d) (Fin d) (Fin (R.sample d)))
    (hTypical :
      sampleColumnComplementNormalized
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          X (⟨0, hs⟩ : Fin (R.sample d)) ∈
        backgroundTypicalSet
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (lowerConcreteN d) (lowerConcreteM R a slack d)
          (lowerConcreteTau a slack d)
          (lowerConcreteDeletedBackgroundMean R k d) k)
    (hSphere :
      frobeniusNorm (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)) X = 1)
    (hMass :
      sampleColumnMass
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        X (⟨0, hs⟩ : Fin (R.sample d)) ∈ betaColumnIntervalSet q δ)
    (hUpperLeOne : betaColumnIntervalUpper q δ ≤ 1)
    (hBudget :
      max (lowerConcreteDeletedBackgroundMean R k d + lowerConcreteTau a slack d) 0 *
        (1 - (1 - betaColumnIntervalUpper q δ) ^ k) ≤
        lowerConcreteScaleError R k ε a slack d) :
    lowerConcreteDeletedBackgroundMean R k d -
        (lowerConcreteTau a slack d + lowerConcreteScaleError R k ε a slack d) ≤
      columnBackgroundContribution
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        (lowerConcreteN d) k X (⟨0, hs⟩ : Fin (R.sample d)) := by
  let α₀ : Fin (R.sample d) := ⟨0, hs⟩
  let B : ℝ :=
    backgroundMomentValue
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      (lowerConcreteN d) k
      (sampleColumnComplementNormalized
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)) X α₀)
  let T : ℝ :=
    frobeniusNorm
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      (sampleColumnComplement
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)) X α₀) ^ (2 * k)
  have hMomentLower :
      lowerConcreteDeletedBackgroundMean R k d - lowerConcreteTau a slack d ≤ B := by
    dsimp [B, α₀]
    exact backgroundMomentValue_lower_of_backgroundTypicalSet
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      (N := lowerConcreteN d) (M := lowerConcreteM R a slack d)
      (τ := lowerConcreteTau a slack d)
      (mean := lowerConcreteDeletedBackgroundMean R k d) (k := k)
      hTypical
  have hScale :
      B * (1 - T) ≤ lowerConcreteScaleError R k ε a slack d := by
    dsimp [B, T, α₀]
    exact
      lower_backgroundScaleLoss_pointwise_concreteChoices_of_sphere_betaInterval_budget
        (R := R) (k := k) (ε := ε) (a := a) (slack := slack)
        (q := q) (δ := δ) (d := d) hs X hTypical hSphere hMass
        hUpperLeOne hBudget
  have hContributionEq :
      columnBackgroundContribution
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (lowerConcreteN d) k X α₀ =
        T * B := by
    simpa [B, T, α₀] using
      columnBackgroundContribution_eq_norm_pow_mul_backgroundMomentValue_normalized
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        (α₀ := α₀) (lowerConcreteN d) k X
  have hTransfer :
      B - lowerConcreteScaleError R k ε a slack d ≤
        columnBackgroundContribution
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (lowerConcreteN d) k X α₀ := by
    rw [hContributionEq]
    calc
      B - lowerConcreteScaleError R k ε a slack d ≤ B - B * (1 - T) := by
        linarith
      _ = T * B := by ring
  simpa [α₀] using (by linarith : lowerConcreteDeletedBackgroundMean R k d -
      (lowerConcreteTau a slack d + lowerConcreteScaleError R k ε a slack d) ≤
        columnBackgroundContribution
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (lowerConcreteN d) k X α₀)

/-!
Deterministic deleted-column local expansion bridge with an explicit
mass-upper scale term.

This is the pointwise lower counterpart used in the lower-route bookkeeping:
background typicality controls the normalized deleted background, the spherical
identity transfers it to the unnormalized deleted block with the exact factor
`1 - (1 - U)^k`, and the mixed term remains as a one-sided error input.
-/
theorem lower_deletedColumn_localExpansion_lower_of_sphere_mass_upper_scaleTerm_mixed
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (a slack U errMix : ℝ) (d : ℕ)
    (hs : 0 < R.sample d)
    (X : SampleMatrix (Fin d) (Fin d) (Fin (R.sample d)))
    (hTypical :
      sampleColumnComplementNormalized
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          X (⟨0, hs⟩ : Fin (R.sample d)) ∈
        backgroundTypicalSet
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (lowerConcreteN d) (lowerConcreteM R a slack d)
          (lowerConcreteTau a slack d)
          (lowerConcreteDeletedBackgroundMean R k d) k)
    (hSphere :
      frobeniusNorm (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)) X = 1)
    (hUleOne : U ≤ 1)
    (hMassUpper :
      sampleColumnMass
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        X (⟨0, hs⟩ : Fin (R.sample d)) ≤ U)
    (hMixed :
      -errMix ≤
        columnMixedRemainder
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (lowerConcreteN d) k X (⟨0, hs⟩ : Fin (R.sample d))) :
    scaledTracePower (p := Fin d) (q := Fin d) (lowerConcreteN d) k
        (gamma (densityMatrix X)) -
        lowerConcreteDeletedBackgroundMean R k d ≥
      columnSpikeContribution
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (lowerConcreteN d) k X (⟨0, hs⟩ : Fin (R.sample d)) -
        (lowerConcreteTau a slack d +
          max (lowerConcreteDeletedBackgroundMean R k d +
                lowerConcreteTau a slack d) 0 *
            (1 - (1 - U) ^ k)) - errMix := by
  let α₀ : Fin (R.sample d) := ⟨0, hs⟩
  let B : ℝ :=
    backgroundMomentValue
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      (lowerConcreteN d) k
      (sampleColumnComplementNormalized
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)) X α₀)
  let T : ℝ :=
    frobeniusNorm
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      (sampleColumnComplement
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)) X α₀) ^ (2 * k)
  let scaleTerm : ℝ :=
    max (lowerConcreteDeletedBackgroundMean R k d +
          lowerConcreteTau a slack d) 0 *
      (1 - (1 - U) ^ k)
  have hMomentLower :
      lowerConcreteDeletedBackgroundMean R k d - lowerConcreteTau a slack d ≤ B := by
    dsimp [B, α₀]
    exact backgroundMomentValue_lower_of_backgroundTypicalSet
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      (N := lowerConcreteN d) (M := lowerConcreteM R a slack d)
      (τ := lowerConcreteTau a slack d)
      (mean := lowerConcreteDeletedBackgroundMean R k d) (k := k)
      hTypical
  have hMomentUpper :
      B ≤ lowerConcreteDeletedBackgroundMean R k d + lowerConcreteTau a slack d := by
    dsimp [B, α₀]
    exact lower_backgroundMomentValue_upper_of_backgroundTypicalSet
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      (N := lowerConcreteN d) (M := lowerConcreteM R a slack d)
      (τ := lowerConcreteTau a slack d)
      (mean := lowerConcreteDeletedBackgroundMean R k d) (k := k)
      hTypical
  have hFactorEq :
      1 - T =
        1 -
          (1 - sampleColumnMass
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)) X α₀) ^ k := by
    dsimp [T]
    rw [lower_sampleColumnComplement_frobeniusNorm_pow_eq_one_sub_mass_pow_of_norm_one
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      (α₀ := α₀) (X := X) k hSphere]
  have hFactorNonneg : 0 ≤ 1 - T := by
    rw [hFactorEq]
    exact lower_one_sub_one_sub_sampleColumnMass_pow_nonneg_of_norm_one
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      (α₀ := α₀) (X := X) k hSphere
  have hFactorLe :
      1 - T ≤ 1 - (1 - U) ^ k := by
    rw [hFactorEq]
    exact lower_one_sub_one_sub_sampleColumnMass_pow_le_of_mass_le
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      (X := X) (α₀ := α₀) k hUleOne hMassUpper
  have hScale :
      B * (1 - T) ≤ scaleTerm := by
    have hMleMax :
        lowerConcreteDeletedBackgroundMean R k d + lowerConcreteTau a slack d ≤
          max (lowerConcreteDeletedBackgroundMean R k d +
            lowerConcreteTau a slack d) 0 :=
      le_max_left _ _
    have hMaxNonneg :
        0 ≤
          max (lowerConcreteDeletedBackgroundMean R k d +
            lowerConcreteTau a slack d) 0 :=
      le_max_right _ _
    have hstep1 :
        B * (1 - T) ≤
          (lowerConcreteDeletedBackgroundMean R k d +
            lowerConcreteTau a slack d) * (1 - T) :=
      mul_le_mul_of_nonneg_right hMomentUpper hFactorNonneg
    have hstep2 :
        (lowerConcreteDeletedBackgroundMean R k d +
          lowerConcreteTau a slack d) * (1 - T) ≤
        max (lowerConcreteDeletedBackgroundMean R k d +
            lowerConcreteTau a slack d) 0 * (1 - T) :=
      mul_le_mul_of_nonneg_right hMleMax hFactorNonneg
    have hstep3 :
        max (lowerConcreteDeletedBackgroundMean R k d +
            lowerConcreteTau a slack d) 0 * (1 - T) ≤
          max (lowerConcreteDeletedBackgroundMean R k d +
              lowerConcreteTau a slack d) 0 *
            (1 - (1 - U) ^ k) :=
      mul_le_mul_of_nonneg_left hFactorLe hMaxNonneg
    exact (hstep1.trans hstep2).trans hstep3
  have hContributionEq :
      columnBackgroundContribution
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (lowerConcreteN d) k X α₀ =
        T * B := by
    simpa [B, T, α₀] using
      columnBackgroundContribution_eq_norm_pow_mul_backgroundMomentValue_normalized
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        (α₀ := α₀) (lowerConcreteN d) k X
  have hTransfer :
      B - scaleTerm ≤
        columnBackgroundContribution
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (lowerConcreteN d) k X α₀ := by
    rw [hContributionEq]
    calc
      B - scaleTerm ≤ B - B * (1 - T) := by linarith
      _ = T * B := by ring
  have hBackground :
      lowerConcreteDeletedBackgroundMean R k d -
          (lowerConcreteTau a slack d + scaleTerm) ≤
        columnBackgroundContribution
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (lowerConcreteN d) k X α₀ := by
    linarith
  have hDecomp :
      scaledTracePower (p := Fin d) (q := Fin d) (lowerConcreteN d) k
          (gamma (densityMatrix X)) =
        columnSpikeContribution
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            (lowerConcreteN d) k X α₀ +
          columnBackgroundContribution
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            (lowerConcreteN d) k X α₀ +
          columnMixedRemainder
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            (lowerConcreteN d) k X α₀ := by
    simpa [α₀] using
      scaledTracePower_column_decomposition
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        (N := lowerConcreteN d) (k := k) (X := X) α₀
  linarith

/-- Named deterministic deleted-column local expansion bridge in the concrete
PT lower route.

This is a thin naming wrapper around
`lower_deletedColumn_localExpansion_lower_of_sphere_mass_upper_scaleTerm_mixed`,
kept for downstream use where the local expansion is referenced as a standalone
deterministic ingredient. -/
theorem lower_deletedColumn_localExpansion_bound_concreteChoices
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (a slack U errMix : ℝ) (d : ℕ)
    (hs : 0 < R.sample d)
    (X : SampleMatrix (Fin d) (Fin d) (Fin (R.sample d)))
    (hTypical :
      sampleColumnComplementNormalized
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          X (⟨0, hs⟩ : Fin (R.sample d)) ∈
        backgroundTypicalSet
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (lowerConcreteN d) (lowerConcreteM R a slack d)
          (lowerConcreteTau a slack d)
          (lowerConcreteDeletedBackgroundMean R k d) k)
    (hSphere :
      frobeniusNorm (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)) X = 1)
    (hUleOne : U ≤ 1)
    (hMassUpper :
      sampleColumnMass
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        X (⟨0, hs⟩ : Fin (R.sample d)) ≤ U)
    (hMixed :
      -errMix ≤
        columnMixedRemainder
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (lowerConcreteN d) k X (⟨0, hs⟩ : Fin (R.sample d))) :
    scaledTracePower (p := Fin d) (q := Fin d) (lowerConcreteN d) k
        (gamma (densityMatrix X)) -
        lowerConcreteDeletedBackgroundMean R k d ≥
      columnSpikeContribution
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (lowerConcreteN d) k X (⟨0, hs⟩ : Fin (R.sample d)) -
        (lowerConcreteTau a slack d +
          max (lowerConcreteDeletedBackgroundMean R k d +
                lowerConcreteTau a slack d) 0 *
            (1 - (1 - U) ^ k)) - errMix :=
  lower_deletedColumn_localExpansion_lower_of_sphere_mass_upper_scaleTerm_mixed
    (R := R) (k := k) (a := a) (slack := slack) (U := U)
    (errMix := errMix) (d := d) hs X hTypical hSphere hUleOne hMassUpper hMixed

theorem lower_deletedColumn_localExpansion_bound_concreteChoices_invD
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (a slack U errMix : ℝ) (d : ℕ)
    (hs : 0 < R.sample d)
    (X : SampleMatrix (Fin d) (Fin d) (Fin (R.sample d)))
    (hTypical :
      sampleColumnComplementNormalized
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          X (⟨0, hs⟩ : Fin (R.sample d)) ∈
        backgroundTypicalSet
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (lowerConcreteN d) (lowerConcreteM R a slack d)
          (lowerConcreteTau a slack d)
          (lowerConcreteDeletedBackgroundMean R k d) k)
    (hSphere :
      frobeniusNorm (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)) X = 1)
    (hUleOne : U ≤ 1)
    (hMassUpper :
      sampleColumnMass
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        X (⟨0, hs⟩ : Fin (R.sample d)) ≤ U)
    (hScaleTerm :
      max (lowerConcreteDeletedBackgroundMean R k d +
            lowerConcreteTau a slack d) 0 *
        (1 - (1 - U) ^ k) ≤ (d : ℝ)⁻¹)
    (hMixed :
      -errMix ≤
        columnMixedRemainder
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (lowerConcreteN d) k X (⟨0, hs⟩ : Fin (R.sample d))) :
    scaledTracePower (p := Fin d) (q := Fin d) (lowerConcreteN d) k
        (gamma (densityMatrix X)) -
        lowerConcreteDeletedBackgroundMean R k d ≥
      columnSpikeContribution
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (lowerConcreteN d) k X (⟨0, hs⟩ : Fin (R.sample d)) -
        (((2 : ℝ) * (d : ℝ)⁻¹) + errMix) := by
  have hbase :
      scaledTracePower (p := Fin d) (q := Fin d) (lowerConcreteN d) k
          (gamma (densityMatrix X)) -
          lowerConcreteDeletedBackgroundMean R k d ≥
        columnSpikeContribution
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            (lowerConcreteN d) k X (⟨0, hs⟩ : Fin (R.sample d)) -
          (lowerConcreteTau a slack d +
            max (lowerConcreteDeletedBackgroundMean R k d +
                  lowerConcreteTau a slack d) 0 *
              (1 - (1 - U) ^ k)) - errMix :=
    lower_deletedColumn_localExpansion_bound_concreteChoices
      (R := R) (k := k) (a := a) (slack := slack)
      (U := U) (errMix := errMix) (d := d) hs X
      hTypical hSphere hUleOne hMassUpper hMixed
  have hTauInv : lowerConcreteTau a slack d = (d : ℝ)⁻¹ := by
    simp [lowerConcreteTau, lowerConcreteDelta]
  linarith [hbase, hScaleTerm, hTauInv]

theorem lower_deletedColumn_localExpansion_lower_of_sphere_betaInterval_scaleTerm_mixed
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (a slack q δ errMix : ℝ) (d : ℕ)
    (hs : 0 < R.sample d)
    (X : SampleMatrix (Fin d) (Fin d) (Fin (R.sample d)))
    (hTypical :
      sampleColumnComplementNormalized
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          X (⟨0, hs⟩ : Fin (R.sample d)) ∈
        backgroundTypicalSet
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (lowerConcreteN d) (lowerConcreteM R a slack d)
          (lowerConcreteTau a slack d)
          (lowerConcreteDeletedBackgroundMean R k d) k)
    (hSphere :
      frobeniusNorm (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)) X = 1)
    (hMass :
      sampleColumnMass
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        X (⟨0, hs⟩ : Fin (R.sample d)) ∈ betaColumnIntervalSet q δ)
    (hUpperLeOne : betaColumnIntervalUpper q δ ≤ 1)
    (hMixed :
      -errMix ≤
        columnMixedRemainder
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (lowerConcreteN d) k X (⟨0, hs⟩ : Fin (R.sample d))) :
    scaledTracePower (p := Fin d) (q := Fin d) (lowerConcreteN d) k
        (gamma (densityMatrix X)) -
        lowerConcreteDeletedBackgroundMean R k d ≥
      columnSpikeContribution
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (lowerConcreteN d) k X (⟨0, hs⟩ : Fin (R.sample d)) -
        (lowerConcreteTau a slack d +
          max (lowerConcreteDeletedBackgroundMean R k d +
                lowerConcreteTau a slack d) 0 *
            (1 - (1 - betaColumnIntervalUpper q δ) ^ k)) - errMix := by
  refine
    lower_deletedColumn_localExpansion_lower_of_sphere_mass_upper_scaleTerm_mixed
      (R := R) (k := k) (a := a) (slack := slack)
      (U := betaColumnIntervalUpper q δ) (errMix := errMix)
      (d := d) hs X hTypical hSphere hUpperLeOne ?_ hMixed
  exact lower_betaColumnIntervalSet_right_le hMass

/-!
Measure-level support bridge for the corrected scale-loss route.

The corrected deterministic estimate is only valid on the Frobenius sphere.
The spherical model measure is supported on that sphere, so an inclusion that
holds after adding `frobeniusNorm X = 1` is enough for probability comparison.
-/
theorem lower_measureReal_le_of_subset_on_full_measure_set
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsFiniteMeasure μ] {E T S : Set α}
    (hS : μ.real Sᶜ = 0) (hSub : E ∩ S ⊆ T) :
    μ.real E ≤ μ.real T := by
  have hEsub : E ⊆ T ∪ Sᶜ := by
    intro x hxE
    by_cases hxS : x ∈ S
    · exact Or.inl (hSub ⟨hxE, hxS⟩)
    · exact Or.inr hxS
  calc
    μ.real E ≤ μ.real (T ∪ Sᶜ) := MeasureTheory.measureReal_mono hEsub
    _ ≤ μ.real T + μ.real Sᶜ := MeasureTheory.measureReal_union_le T Sᶜ
    _ = μ.real T := by simp [hS]

theorem lower_sphericalModelMeasure_frobeniusNorm_one_compl_real_zero
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [Nonempty p] [Nonempty q] [Nonempty σ] :
    (_root_.PptFactorization.AppendixB.sphericalModelMeasure
        (p := p) (q := q) (σ := σ)).real
      ({X : SampleMatrix p q σ |
        frobeniusNorm (p := p) (q := q) (σ := σ) X = 1}ᶜ) = 0 := by
  let S : Set (SampleMatrix p q σ) := Metric.sphere 0 1
  have hsphere :
      _root_.PptFactorization.AppendixB.sphericalModelMeasure
          (p := p) (q := q) (σ := σ) S = 1 := by
    simpa [S, _root_.PptFactorization.AppendixB.sphericalModelMeasure] using
      _root_.PptFactorization.AppendixB.gaussianDirection_law_sphere
        (p := p) (q := q) (σ := σ)
  have hcomp :
      _root_.PptFactorization.AppendixB.sphericalModelMeasure
          (p := p) (q := q) (σ := σ) Sᶜ = 0 := by
    haveI :
        MeasureTheory.IsProbabilityMeasure
          (_root_.PptFactorization.AppendixB.sphericalModelMeasure
            (p := p) (q := q) (σ := σ)) :=
      _root_.PptFactorization.AppendixB.sphericalModelMeasure_isProbabilityMeasure
        (p := p) (q := q) (σ := σ)
    rw [MeasureTheory.measure_compl]
    · rw [hsphere, MeasureTheory.IsProbabilityMeasure.measure_univ]
      norm_num
    · dsimp [S]
      exact Metric.isClosed_sphere.measurableSet
    · rw [hsphere]
      exact ENNReal.one_ne_top
  have hset :
      ({X : SampleMatrix p q σ |
        frobeniusNorm (p := p) (q := q) (σ := σ) X = 1}ᶜ) = Sᶜ := by
    dsimp [S]
    ext X
    simp [frobeniusNorm]
  rw [hset]
  simp [MeasureTheory.measureReal_def, hcomp]

theorem lower_sphericalModelMeasure_real_le_of_subset_on_frobenius_sphere
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [Nonempty p] [Nonempty q] [Nonempty σ]
    {E T : Set (SampleMatrix p q σ)}
    (hSub :
      ∀ X : SampleMatrix p q σ,
        X ∈ E →
        frobeniusNorm (p := p) (q := q) (σ := σ) X = 1 →
        X ∈ T) :
    (_root_.PptFactorization.AppendixB.sphericalModelMeasure
        (p := p) (q := q) (σ := σ)).real E ≤
      (_root_.PptFactorization.AppendixB.sphericalModelMeasure
        (p := p) (q := q) (σ := σ)).real T := by
  let S : Set (SampleMatrix p q σ) :=
    {X | frobeniusNorm (p := p) (q := q) (σ := σ) X = 1}
  haveI :
      MeasureTheory.IsProbabilityMeasure
        (_root_.PptFactorization.AppendixB.sphericalModelMeasure
          (p := p) (q := q) (σ := σ)) :=
    _root_.PptFactorization.AppendixB.sphericalModelMeasure_isProbabilityMeasure
      (p := p) (q := q) (σ := σ)
  haveI :
      MeasureTheory.IsFiniteMeasure
        (_root_.PptFactorization.AppendixB.sphericalModelMeasure
          (p := p) (q := q) (σ := σ)) :=
    inferInstance
  exact lower_measureReal_le_of_subset_on_full_measure_set
    (μ := _root_.PptFactorization.AppendixB.sphericalModelMeasure
      (p := p) (q := q) (σ := σ))
    (E := E) (T := T) (S := S)
    (by
      dsimp [S]
      exact lower_sphericalModelMeasure_frobeniusNorm_one_compl_real_zero
        (p := p) (q := q) (σ := σ))
    (by
      intro X hX
      exact hSub X hX.1 hX.2)

/-!
Corrected scale-budget input.

The old `lowerConcreteBackgroundScaleLoss` predicate asked for a pointwise
transfer from normalized background typicality alone.  That is too strong.
This replacement is the scalar budget actually needed after restricting to the
spherical one-column favourable event: the Beta interval supplies the
distinguished-column mass upper bound, and the spherical support supplies
`‖X‖_F = 1`.
-/
def lowerConcreteBackgroundScaleBudgetOnBetaInterval
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (ε : ℝ) : Prop :=
  ∀ a : ℝ, spikeRoot k ε < a →
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        max (lowerConcreteDeletedBackgroundMean R k d +
            lowerConcreteTau a slack d) 0 *
          (1 -
            (1 -
              betaColumnIntervalUpper
                (betaColumnSpikeScale
                  (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                (lowerConcreteDelta a slack d)) ^ k) ≤
          lowerConcreteScaleError R k ε a slack d

/-- For `k ≥ 3`, the Beta-interval upper endpoint is small enough that the
extra factor `d` still sends it to zero.  This is the scalar rate fact behind
the corrected sphere/Beta scale-budget route. -/
theorem lower_concrete_d_mul_betaColumnIntervalUpper_tendsto_zero
    {k : ℕ} (hk3 : 3 ≤ k) {a slack : ℝ} :
    Tendsto
      (fun d : ℕ =>
        (d : ℝ) *
          betaColumnIntervalUpper
            (betaColumnSpikeScale
              (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
            (lowerConcreteDelta a slack d))
      atTop (nhds 0) := by
  have hkRpos : 0 < (k : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 3) hk3)
  have hkR_ge3 : (3 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hk3
  have htwo_div_lt_one : (2 : ℝ) / (k : ℝ) < 1 := by
    rw [div_lt_one hkRpos]
    linarith
  have hgap_pos : 0 < (1 : ℝ) - (2 : ℝ) / (k : ℝ) := by
    linarith
  have hgap_atTop :
      Tendsto
        (fun d : ℕ => (d : ℝ) ^ ((1 : ℝ) - (2 : ℝ) / (k : ℝ)))
        atTop atTop :=
    (tendsto_rpow_atTop hgap_pos).comp tendsto_natCast_atTop_atTop
  have hinv :
      Tendsto
        (fun d : ℕ => ((d : ℝ) ^ ((1 : ℝ) - (2 : ℝ) / (k : ℝ)))⁻¹)
        atTop (nhds 0) := by
    simpa using (tendsto_inv_atTop_zero.comp hgap_atTop)
  have hsum :
      Tendsto (fun d : ℕ => 1 + lowerConcreteDelta a slack d)
        atTop (nhds (1 + 0)) :=
    tendsto_const_nhds.add
      (lower_concrete_delta_tendsto_zero (a := a) (slack := slack))
  have hfactor :
      Tendsto (fun d : ℕ => a * (1 + lowerConcreteDelta a slack d))
        atTop (nhds (a * 1)) := by
    simpa using tendsto_const_nhds.mul hsum
  have hlim :
      Tendsto
        (fun d : ℕ =>
          (a * (1 + lowerConcreteDelta a slack d)) *
            ((d : ℝ) ^ ((1 : ℝ) - (2 : ℝ) / (k : ℝ)))⁻¹)
        atTop (nhds 0) := by
    simpa using hfactor.mul hinv
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with d hd
  have hdR : 0 < (d : ℝ) := by
    exact_mod_cast hd
  have hcore :
      (d : ℝ) *
          ((d : ℝ) ^ (2 + (2 : ℝ) / (k : ℝ)) / ((d : ℝ) ^ 2) ^ 2) =
        ((d : ℝ) ^ ((1 : ℝ) - (2 : ℝ) / (k : ℝ)))⁻¹ := by
    field_simp [ne_of_gt hdR,
      ne_of_gt (Real.rpow_pos_of_pos hdR ((1 : ℝ) - (2 : ℝ) / (k : ℝ))),
      ne_of_gt (Real.rpow_pos_of_pos hdR (2 + (2 : ℝ) / (k : ℝ)))]
    rw [← Real.rpow_add hdR]
    have hexp :
        2 * ((k : ℝ) + 1) / (k : ℝ) +
            ((k : ℝ) - 2) / (k : ℝ) = (3 : ℝ) := by
      field_simp [ne_of_gt hkRpos]
      ring
    rw [hexp]
    exact Real.rpow_natCast (d : ℝ) 3
  simp [betaColumnIntervalUpper, betaColumnSpikeScale, lowerConcreteN,
    lowerConcreteDelta, spikeSpeed, Nat.cast_pow]
  rw [← hcore]
  ring

/-- Conditional closure of the corrected scale budget.

This is the honest reduced form of the remaining scale-budget proof: for
`k ≥ 3`, it is enough to know that the positive part of the deleted-background
spherical mean plus the tolerance is eventually bounded.  The theorem does not
claim that mean bound; that is the next concrete moment/expectation input to
close. -/
theorem lower_scaleBudget_concreteChoices_of_eventually_boundedMean
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanBound :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∃ C : ℝ, 0 ≤ C ∧
            ∀ᶠ d in atTop,
              max (lowerConcreteDeletedBackgroundMean R k d +
                  lowerConcreteTau a slack d) 0 ≤ C) :
    lowerConcreteBackgroundScaleBudgetOnBetaInterval R k ε := by
  intro a ha slack hslack
  rcases hMeanBound a ha slack hslack with ⟨C, hC_nonneg, hCevent⟩
  have hk1 : 1 < k := lt_of_lt_of_le (by decide : 1 < 3) hk3
  have hk0 : 0 < k := Nat.zero_lt_of_lt hk1
  let U : ℕ → ℝ := fun d =>
    betaColumnIntervalUpper
      (betaColumnSpikeScale (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
      (lowerConcreteDelta a slack d)
  have hscaled_tendsto :
      Tendsto (fun d : ℕ => C * ((k : ℝ) * ((d : ℝ) * (U d))))
        atTop (nhds 0) := by
    have hU : Tendsto (fun d : ℕ => (d : ℝ) * (U d)) atTop (nhds 0) := by
      simpa [U] using
        (lower_concrete_d_mul_betaColumnIntervalUpper_tendsto_zero
          (k := k) hk3 (a := a) (slack := slack))
    have hkU :
        Tendsto (fun d : ℕ => (k : ℝ) * ((d : ℝ) * (U d)))
          atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hU
    simpa using tendsto_const_nhds.mul hkU
  have hscaled_le :
      ∀ᶠ d : ℕ in atTop, C * ((k : ℝ) * ((d : ℝ) * (U d))) ≤ 1 :=
    hscaled_tendsto.eventually
      (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hCevent, hscaled_le,
    lower_concrete_hBetaScalePos (k := k) hk0 (ε := ε) hε a ha slack hslack,
    lower_concrete_hDeltaPos (k := k) (ε := ε) a ha slack hslack,
    lower_concrete_hUpper (k := k) hk1 (ε := ε) a ha slack hslack,
    eventually_gt_atTop 0] with d hMle hscaled hqpos hδpos hUpper hd
  have hdR : 0 < (d : ℝ) := by
    exact_mod_cast hd
  have hU_pos : 0 < U d := by
    have hfactor_pos : 0 < 1 + lowerConcreteDelta a slack d := by
      linarith
    simpa [U, betaColumnIntervalUpper] using mul_pos hfactor_pos hqpos
  have hU_le_one : U d ≤ 1 := le_of_lt (by simpa [U] using hUpper)
  have hbase_nonneg : 0 ≤ 1 - U d := by
    linarith
  have hpow_le_one : (1 - U d) ^ k ≤ 1 :=
    pow_le_one₀ hbase_nonneg (by linarith : 1 - U d ≤ 1)
  have hterm_nonneg : 0 ≤ 1 - (1 - U d) ^ k := by
    linarith
  have hBern : 1 + (k : ℝ) * (-(U d)) ≤ (1 + (-(U d))) ^ k := by
    exact one_add_mul_le_pow (by linarith : -2 ≤ -(U d)) k
  have hBern' : 1 - (k : ℝ) * U d ≤ (1 - U d) ^ k := by
    simpa [sub_eq_add_neg, mul_neg] using hBern
  have hterm_le : 1 - (1 - U d) ^ k ≤ (k : ℝ) * U d := by
    linarith
  have hCkU_le_delta :
      C * ((k : ℝ) * U d) ≤ lowerConcreteDelta a slack d := by
    have hscaled' : C * ((k : ℝ) * ((d : ℝ) * U d)) ≤ 1 := by
      simpa [U] using hscaled
    calc
      C * ((k : ℝ) * U d)
          = (C * ((k : ℝ) * ((d : ℝ) * U d))) / (d : ℝ) := by
              field_simp [ne_of_gt hdR]
      _ ≤ 1 / (d : ℝ) := by
              exact div_le_div_of_nonneg_right hscaled' (le_of_lt hdR)
      _ = lowerConcreteDelta a slack d := by
              simp [lowerConcreteDelta]
  calc
    max (lowerConcreteDeletedBackgroundMean R k d + lowerConcreteTau a slack d) 0 *
          (1 - (1 - U d) ^ k)
        ≤ C * (1 - (1 - U d) ^ k) :=
          mul_le_mul_of_nonneg_right hMle hterm_nonneg
    _ ≤ C * ((k : ℝ) * U d) :=
          mul_le_mul_of_nonneg_left hterm_le hC_nonneg
    _ ≤ lowerConcreteScaleError R k ε a slack d := by
          simpa [lowerConcreteScaleError] using hCkU_le_delta

/-- Monotonicity of the scaled Beta interval upper endpoint in the spike
parameter `a`. -/
theorem lower_concrete_d_mul_betaColumnIntervalUpper_mono_in_a
    {k d : ℕ} {a A slack : ℝ} (hd : 0 < d) (haA : a ≤ A) :
    (d : ℝ) *
          betaColumnIntervalUpper
            (betaColumnSpikeScale
              (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
            (lowerConcreteDelta a slack d) ≤
    (d : ℝ) *
          betaColumnIntervalUpper
            (betaColumnSpikeScale
              (lowerConcreteN d : ℝ) (spikeSpeed k d) A)
            (lowerConcreteDelta A slack d) := by
  have hdR : 0 < (d : ℝ) := by
    exact_mod_cast hd
  have hfactor_nonneg :
      0 ≤ (d : ℝ) * ((1 + (d : ℝ)⁻¹) *
          (spikeSpeed k d / ((d : ℝ) ^ 2) ^ 2)) := by
    have hspeed_nonneg : 0 ≤ spikeSpeed k d := by
      exact le_of_lt (by simp [spikeSpeed, Real.rpow_pos_of_pos hdR])
    have hinv_nonneg : 0 ≤ (d : ℝ)⁻¹ := inv_nonneg.mpr (le_of_lt hdR)
    have hfactor_left : 0 ≤ 1 + (d : ℝ)⁻¹ := by linarith
    have hden_nonneg : 0 ≤ ((d : ℝ) ^ 2) ^ 2 := sq_nonneg ((d : ℝ) ^ 2)
    exact mul_nonneg (le_of_lt hdR)
      (mul_nonneg hfactor_left (div_nonneg hspeed_nonneg hden_nonneg))
  calc
    (d : ℝ) *
          betaColumnIntervalUpper
            (betaColumnSpikeScale
              (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
            (lowerConcreteDelta a slack d)
        = a * ((d : ℝ) * ((1 + (d : ℝ)⁻¹) *
            (spikeSpeed k d / ((d : ℝ) ^ 2) ^ 2))) := by
            simp [betaColumnIntervalUpper, betaColumnSpikeScale,
              lowerConcreteN, lowerConcreteDelta, Nat.cast_pow]
            ring
    _ ≤ A * ((d : ℝ) * ((1 + (d : ℝ)⁻¹) *
            (spikeSpeed k d / ((d : ℝ) ^ 2) ^ 2))) :=
          mul_le_mul_of_nonneg_right haA hfactor_nonneg
    _ = (d : ℝ) *
          betaColumnIntervalUpper
            (betaColumnSpikeScale
              (lowerConcreteN d : ℝ) (spikeSpeed k d) A)
            (lowerConcreteDelta A slack d) := by
            simp [betaColumnIntervalUpper, betaColumnSpikeScale,
              lowerConcreteN, lowerConcreteDelta, Nat.cast_pow]
            ring

/-- Uniform bounded-`a` version of the scalar Beta endpoint estimate. -/
theorem lower_concrete_d_mul_betaColumnIntervalUpper_eventually_le_on_Icc
    {k : ℕ} (hk3 : 3 ≤ k) {A slack η : ℝ} (hη : 0 < η) :
    ∀ᶠ d : ℕ in atTop, ∀ a : ℝ, 0 ≤ a → a ≤ A →
      (d : ℝ) *
          betaColumnIntervalUpper
            (betaColumnSpikeScale
              (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
            (lowerConcreteDelta a slack d) ≤ η := by
  have hA :=
    lower_concrete_d_mul_betaColumnIntervalUpper_tendsto_zero
      (k := k) hk3 (a := A) (slack := slack)
  have hAle : ∀ᶠ d : ℕ in atTop,
      (d : ℝ) * betaColumnIntervalUpper
        (betaColumnSpikeScale (lowerConcreteN d : ℝ) (spikeSpeed k d) A)
        (lowerConcreteDelta A slack d) ≤ η :=
    hA.eventually (eventually_le_nhds hη)
  filter_upwards [hAle, eventually_gt_atTop 0] with d hAd hd a _ha0 haA
  exact le_trans
    (lower_concrete_d_mul_betaColumnIntervalUpper_mono_in_a
      (k := k) (d := d) (a := a) (A := A) (slack := slack) hd haA)
    hAd

/-- Bounded-`a` form of the corrected scale budget.

This is the mathematically robust quantifier order: for each finite upper
window `A`, the lower-bound scale budget is eventually valid uniformly for
`0 ≤ a ≤ A`. -/
def lowerConcreteBackgroundScaleBudgetOnBetaIntervalBoundedA
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (ε : ℝ) : Prop :=
  ∀ A : ℝ, 0 ≤ A →
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d : ℕ in atTop,
        ∀ a : ℝ, spikeRoot k ε < a → 0 ≤ a → a ≤ A →
          max (lowerConcreteDeletedBackgroundMean R k d +
              lowerConcreteTau a slack d) 0 *
            (1 -
              (1 -
                betaColumnIntervalUpper
                  (betaColumnSpikeScale
                    (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                  (lowerConcreteDelta a slack d)) ^ k) ≤
            lowerConcreteScaleError R k ε a slack d

/-- Exact remaining mean-growth input for the corrected scale-budget proof.

For every bounded spike window `0 ≤ a ≤ A`, the positive part of the
deleted-background spherical mean plus the tolerance is eventually bounded.
This is the first non-scalar input needed after the Beta-scale and
sphere-support bookkeeping has been closed. -/
def lowerConcreteDeletedBackgroundMeanPositivePartBoundedOnCompactA
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (_ε : ℝ) : Prop :=
  ∀ A : ℝ, 0 ≤ A →
    ∀ slack : ℝ, 0 < slack →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ᶠ d : ℕ in atTop,
          ∀ a : ℝ, 0 ≤ a → a ≤ A →
            max (lowerConcreteDeletedBackgroundMean R k d +
                lowerConcreteTau a slack d) 0 ≤ C

/-- Minimal scalar frontier for the corrected scale-budget proof.

Since the current concrete choice has `lowerConcreteTau a slack d = d⁻¹`, the
bounded-window mean input above is equivalent, for the scale-budget use, to
eventual boundedness of `max (mean_d + d⁻¹) 0`.  This is the first real
non-scalar lemma still needed to turn the corrected scale-budget route into a
no-input supplier. -/
def lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ d : ℕ in atTop,
      max (lowerConcreteDeletedBackgroundMean R k d + (d : ℝ)⁻¹) 0 ≤ C

/-- Scalar conditional-mean bound.

If a mean is bounded above by a positive-part integral divided by an event
probability, the event probability is eventually bounded below by `beta > 0`,
and the positive-part integral is eventually bounded by `Cpos`, then the
positive part of the mean is eventually bounded by `Cpos / beta`. -/
theorem lower_eventually_posPart_le_of_conditional_positive_integral
    {mean prob posInt : ℕ → ℝ} {beta Cpos : ℝ}
    (hbeta : 0 < beta) (hCpos : 0 ≤ Cpos)
    (hprob : ∀ᶠ n : ℕ in atTop, beta ≤ prob n)
    (hposInt_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ posInt n)
    (hposInt_le : ∀ᶠ n : ℕ in atTop, posInt n ≤ Cpos)
    (hmean_le : ∀ᶠ n : ℕ in atTop, mean n ≤ posInt n / prob n) :
    ∀ᶠ n : ℕ in atTop, max (mean n) 0 ≤ Cpos / beta := by
  filter_upwards [hprob, hposInt_nonneg, hposInt_le, hmean_le]
    with n hprob_n hpos_nonneg hpos_le hmean_n
  have hprob_pos : 0 < prob n := lt_of_lt_of_le hbeta hprob_n
  have hdiv_left : posInt n / prob n ≤ Cpos / prob n :=
    div_le_div_of_nonneg_right hpos_le (le_of_lt hprob_pos)
  have hdiv_right : Cpos / prob n ≤ Cpos / beta := by
    exact div_le_div_of_nonneg_left hCpos hbeta hprob_n
  have hmean_bound : mean n ≤ Cpos / beta :=
    le_trans hmean_n (le_trans hdiv_left hdiv_right)
  exact max_le hmean_bound (div_nonneg hCpos (le_of_lt hbeta))

/-- Shifted scalar conditional-mean bound.

This is the form used by the scale-budget frontier: after bounding the positive
part of the conditional mean, add an eventual bound for the positive part of the
tolerance sequence. -/
theorem lower_eventually_shiftedPosPart_le_of_conditional_positive_integral
    {mean tau prob posInt : ℕ → ℝ} {beta Cpos Ttau : ℝ}
    (hbeta : 0 < beta) (hCpos : 0 ≤ Cpos) (_hTtau : 0 ≤ Ttau)
    (hprob : ∀ᶠ n : ℕ in atTop, beta ≤ prob n)
    (hposInt_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ posInt n)
    (hposInt_le : ∀ᶠ n : ℕ in atTop, posInt n ≤ Cpos)
    (hmean_le : ∀ᶠ n : ℕ in atTop, mean n ≤ posInt n / prob n)
    (htau_pos_le : ∀ᶠ n : ℕ in atTop, max (tau n) 0 ≤ Ttau) :
    ∀ᶠ n : ℕ in atTop,
      max (mean n + tau n) 0 ≤ Cpos / beta + Ttau := by
  have hmean_pos :
      ∀ᶠ n : ℕ in atTop, max (mean n) 0 ≤ Cpos / beta :=
    lower_eventually_posPart_le_of_conditional_positive_integral
      hbeta hCpos hprob hposInt_nonneg hposInt_le hmean_le
  filter_upwards [hmean_pos, htau_pos_le] with n hmean_n htau_n
  have hmean_le_max : mean n ≤ max (mean n) 0 := le_max_left _ _
  have htau_le_max : tau n ≤ max (tau n) 0 := le_max_left _ _
  have hsum :
      mean n + tau n ≤ max (mean n) 0 + max (tau n) 0 := by
    linarith
  have hsum_nonneg : 0 ≤ max (mean n) 0 + max (tau n) 0 := by
    have hm0 : 0 ≤ max (mean n) 0 := le_max_right _ _
    have ht0 : 0 ≤ max (tau n) 0 := le_max_right _ _
    linarith
  calc
    max (mean n + tau n) 0
        ≤ max (mean n) 0 + max (tau n) 0 :=
          max_le hsum hsum_nonneg
    _ ≤ Cpos / beta + Ttau := add_le_add hmean_n htau_n

/-- Concrete scale-frontier closure from the conditional-positive-integral
criterion.

Here `prob d` is the probability of the background event and `posInt d` is the
positive-part background moment integral over that event.  The theorem does not
claim those probabilistic facts; it records the exact scalar bridge from them
to the bounded positive part needed by the corrected scale budget. -/
theorem lower_concrete_deletedBackgroundMean_positivePartEventuallyBounded_of_conditional_positive_integral
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {prob posInt : ℕ → ℝ} {beta Cpos : ℝ}
    (hbeta : 0 < beta) (hCpos : 0 ≤ Cpos)
    (hprob : ∀ᶠ d : ℕ in atTop, beta ≤ prob d)
    (hposInt_nonneg : ∀ᶠ d : ℕ in atTop, 0 ≤ posInt d)
    (hposInt_le : ∀ᶠ d : ℕ in atTop, posInt d ≤ Cpos)
    (hmean_le :
      ∀ᶠ d : ℕ in atTop,
        lowerConcreteDeletedBackgroundMean R k d ≤ posInt d / prob d) :
    lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k := by
  have htau :
      ∀ᶠ d : ℕ in atTop, max ((d : ℝ)⁻¹) 0 ≤ (1 : ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with d hd
    have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
    have hdR_ge_one : 1 ≤ (d : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hd
    have hinv_le : (d : ℝ)⁻¹ ≤ 1 := by
      simpa using
        (div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 1 by norm_num)
          (show (0 : ℝ) < 1 by norm_num) hdR_ge_one)
    exact max_le hinv_le (by norm_num)
  refine ⟨Cpos / beta + 1, ?_, ?_⟩
  · exact add_nonneg (div_nonneg hCpos (le_of_lt hbeta)) (by norm_num)
  · simpa using
      (lower_eventually_shiftedPosPart_le_of_conditional_positive_integral
        (mean := fun d : ℕ => lowerConcreteDeletedBackgroundMean R k d)
        (tau := fun d : ℕ => (d : ℝ)⁻¹)
        (prob := prob) (posInt := posInt)
        (beta := beta) (Cpos := Cpos) (Ttau := 1)
        hbeta hCpos (by norm_num) hprob hposInt_nonneg hposInt_le
        hmean_le htau)

/-- The one-dimensional scalar frontier supplies the bounded-window mean input
because the concrete tolerance is just `d⁻¹`, independent of `a` and `slack`. -/
theorem lower_concrete_meanPositivePartBoundedOnCompactA_of_eventuallyBounded
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ}
    (hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k) :
    lowerConcreteDeletedBackgroundMeanPositivePartBoundedOnCompactA R k ε := by
  intro _A _hA _slack _hslack
  rcases hMeanBound with ⟨C, hC_nonneg, hCevent⟩
  refine ⟨C, hC_nonneg, ?_⟩
  filter_upwards [hCevent] with d hCd a _ha0 _haA
  simpa [lowerConcreteTau, lowerConcreteDelta] using hCd

/-- A finite limit of the deleted-background mean is enough for the scalar
frontier.  This records the shortest route if the mean asymptotics are later
closed by a spherical/Aubrun moment theorem. -/
theorem lower_concrete_deletedBackgroundMean_positivePartEventuallyBounded_of_tendsto
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {m : ℝ}
    (hMean :
      Tendsto (fun d : ℕ => lowerConcreteDeletedBackgroundMean R k d)
        atTop (nhds m)) :
    lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k := by
  have hinv :
      Tendsto (fun d : ℕ => (d : ℝ)⁻¹) atTop (nhds 0) := by
    simpa using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
  have hsum :
      Tendsto
        (fun d : ℕ => lowerConcreteDeletedBackgroundMean R k d + (d : ℝ)⁻¹)
        atTop (nhds (m + 0)) :=
    hMean.add hinv
  have hle :
      ∀ᶠ d : ℕ in atTop,
        lowerConcreteDeletedBackgroundMean R k d + (d : ℝ)⁻¹ ≤ m + 1 := by
    simpa [add_zero] using
      hsum.eventually (eventually_le_nhds (by linarith : m + 0 < m + 1))
  refine ⟨max (m + 1) 0, le_max_right _ _, ?_⟩
  filter_upwards [hle] with d hd
  exact max_le_max hd le_rfl

/-- A finite limit of the deleted-background mean gives the positive-part
boundedness needed by the corrected scale budget.

This version avoids exposing an arbitrary limit witness in downstream theorem
signatures: the remaining mathematical input is exactly the existence of a
finite limit for `lowerConcreteDeletedBackgroundMean R k d`. -/
theorem lower_concrete_deletedBackgroundMean_positivePartEventuallyBounded_of_hasFiniteLimit
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ}
    (hMean :
      ∃ m : ℝ,
        Tendsto (fun d : ℕ => lowerConcreteDeletedBackgroundMean R k d)
          atTop (nhds m)) :
    lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k := by
  rcases hMean with ⟨m, hm⟩
  exact
    lower_concrete_deletedBackgroundMean_positivePartEventuallyBounded_of_tendsto
      (R := R) (k := k) (m := m) hm

/-- Bounded-window closure of the corrected scale budget from the exact
remaining mean input. -/
theorem lower_scaleBudget_boundedA_concreteChoices_of_eventually_boundedMean
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanBound :
      ∀ A : ℝ, 0 ≤ A →
        ∀ slack : ℝ, 0 < slack →
          ∃ C : ℝ, 0 ≤ C ∧
            ∀ᶠ d : ℕ in atTop,
              ∀ a : ℝ, 0 ≤ a → a ≤ A →
                max (lowerConcreteDeletedBackgroundMean R k d +
                    lowerConcreteTau a slack d) 0 ≤ C) :
    lowerConcreteBackgroundScaleBudgetOnBetaIntervalBoundedA R k ε := by
  intro A hA_nonneg slack hslack
  rcases hMeanBound A hA_nonneg slack hslack with ⟨C, hC_nonneg, hCevent⟩
  have hk1 : 1 < k := lt_of_lt_of_le (by decide : 1 < 3) hk3
  have hk0 : 0 < k := Nat.zero_lt_of_lt hk1
  let U : ℕ → ℝ → ℝ := fun d a =>
    betaColumnIntervalUpper
      (betaColumnSpikeScale (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
      (lowerConcreteDelta a slack d)
  have hscaledA_tendsto :
      Tendsto (fun d : ℕ => C * ((k : ℝ) * ((d : ℝ) * (U d A))))
        atTop (nhds 0) := by
    have hU : Tendsto (fun d : ℕ => (d : ℝ) * (U d A)) atTop (nhds 0) := by
      simpa [U] using
        (lower_concrete_d_mul_betaColumnIntervalUpper_tendsto_zero
          (k := k) hk3 (a := A) (slack := slack))
    have hkU :
        Tendsto (fun d : ℕ => (k : ℝ) * ((d : ℝ) * (U d A)))
          atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hU
    simpa using tendsto_const_nhds.mul hkU
  have hscaledA_le :
      ∀ᶠ d : ℕ in atTop, C * ((k : ℝ) * ((d : ℝ) * (U d A))) ≤ 1 :=
    hscaledA_tendsto.eventually
      (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num))
  have hUhalf : ∀ᶠ d : ℕ in atTop,
      ∀ a : ℝ, 0 ≤ a → a ≤ A → (d : ℝ) * U d a ≤ (1 / 2 : ℝ) := by
    simpa [U] using
      (lower_concrete_d_mul_betaColumnIntervalUpper_eventually_le_on_Icc
        (k := k) hk3 (A := A) (slack := slack)
        (η := (1 / 2 : ℝ)) (by norm_num))
  filter_upwards [hCevent, hscaledA_le, hUhalf, eventually_gt_atTop 0]
    with d hMleA hscaledA hUhalf_d hd
    a _haRoot ha_nonneg haA
  have hdR : 0 < (d : ℝ) := by
    exact_mod_cast hd
  have hU_pos : 0 < U d a := by
    have hfactor_pos : 0 < 1 + lowerConcreteDelta a slack d := by
      have hδpos : 0 < lowerConcreteDelta a slack d := by
        simp [lowerConcreteDelta, inv_pos.mpr hdR]
      linarith
    have hqpos : 0 <
        betaColumnSpikeScale (lowerConcreteN d : ℝ) (spikeSpeed k d) a := by
      have ha_pos : 0 < a := lt_of_lt_of_le (spikeRoot_pos hk0 hε) (le_of_lt _haRoot)
      have hNpos : 0 < (lowerConcreteN d : ℝ) := by
        simp [lowerConcreteN, pow_two, mul_pos hdR hdR]
      have hspeed : 0 < spikeSpeed k d := by
        simp [spikeSpeed, Real.rpow_pos_of_pos hdR]
      unfold betaColumnSpikeScale
      exact div_pos (mul_pos ha_pos hspeed) (sq_pos_of_pos hNpos)
    simpa [U, betaColumnIntervalUpper] using mul_pos hfactor_pos hqpos
  have hUpper : U d a < 1 := by
    have hU_nonneg : 0 ≤ U d a := le_of_lt hU_pos
    have hdR_ge_one : 1 ≤ (d : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hd)
    have hU_le_scaled : U d a ≤ (d : ℝ) * U d a := by
      nlinarith
    have hU_le_half : U d a ≤ (1 / 2 : ℝ) :=
      le_trans hU_le_scaled (hUhalf_d a ha_nonneg haA)
    nlinarith
  have hU_le_one : U d a ≤ 1 := le_of_lt hUpper
  have hbase_nonneg : 0 ≤ 1 - U d a := by
    linarith
  have hpow_le_one : (1 - U d a) ^ k ≤ 1 :=
    pow_le_one₀ hbase_nonneg (by linarith : 1 - U d a ≤ 1)
  have hterm_nonneg : 0 ≤ 1 - (1 - U d a) ^ k := by
    linarith
  have hBern :
      1 + (k : ℝ) * (-(U d a)) ≤ (1 + (-(U d a))) ^ k := by
    exact one_add_mul_le_pow (by linarith : -2 ≤ -(U d a)) k
  have hBern' : 1 - (k : ℝ) * U d a ≤ (1 - U d a) ^ k := by
    simpa [sub_eq_add_neg, mul_neg] using hBern
  have hterm_le : 1 - (1 - U d a) ^ k ≤ (k : ℝ) * U d a := by
    linarith
  have hCkU_le_delta :
      C * ((k : ℝ) * U d a) ≤ lowerConcreteDelta a slack d := by
    have hmono :=
      lower_concrete_d_mul_betaColumnIntervalUpper_mono_in_a
        (k := k) (d := d) (a := a) (A := A) (slack := slack) hd haA
    have hscaled_a : C * ((k : ℝ) * ((d : ℝ) * U d a)) ≤ 1 := by
      have hscaled_mono :
          C * ((k : ℝ) * ((d : ℝ) * U d a)) ≤
            C * ((k : ℝ) * ((d : ℝ) * U d A)) := by
        have hdu_mono : (d : ℝ) * U d a ≤ (d : ℝ) * U d A := by
          simpa [U] using hmono
        have hk_nonneg : 0 ≤ (k : ℝ) := by positivity
        have hCk_nonneg : 0 ≤ C * (k : ℝ) :=
          mul_nonneg hC_nonneg hk_nonneg
        nlinarith [mul_le_mul_of_nonneg_left hdu_mono hCk_nonneg]
      exact le_trans hscaled_mono hscaledA
    calc
      C * ((k : ℝ) * U d a)
          = (C * ((k : ℝ) * ((d : ℝ) * U d a))) / (d : ℝ) := by
              field_simp [ne_of_gt hdR]
      _ ≤ 1 / (d : ℝ) := by
              exact div_le_div_of_nonneg_right hscaled_a (le_of_lt hdR)
      _ = lowerConcreteDelta a slack d := by
              simp [lowerConcreteDelta]
  calc
    max (lowerConcreteDeletedBackgroundMean R k d + lowerConcreteTau a slack d) 0 *
          (1 - (1 - U d a) ^ k)
        ≤ C * (1 - (1 - U d a) ^ k) :=
          mul_le_mul_of_nonneg_right (hMleA a ha_nonneg haA) hterm_nonneg
    _ ≤ C * ((k : ℝ) * U d a) :=
          mul_le_mul_of_nonneg_left hterm_le hC_nonneg
    _ ≤ lowerConcreteScaleError R k ε a slack d := by
          simpa [U, lowerConcreteScaleError] using hCkU_le_delta

/-- The bounded-window budget implies the original fixed-`a` scale-budget
predicate by taking `A = a`. -/
theorem lower_scaleBudget_concreteChoices_of_boundedA
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanBound :
      ∀ A : ℝ, 0 ≤ A →
        ∀ slack : ℝ, 0 < slack →
          ∃ C : ℝ, 0 ≤ C ∧
            ∀ᶠ d : ℕ in atTop,
              ∀ a : ℝ, 0 ≤ a → a ≤ A →
                max (lowerConcreteDeletedBackgroundMean R k d +
                    lowerConcreteTau a slack d) 0 ≤ C) :
    lowerConcreteBackgroundScaleBudgetOnBetaInterval R k ε := by
  have hbounded :
      lowerConcreteBackgroundScaleBudgetOnBetaIntervalBoundedA R k ε :=
    lower_scaleBudget_boundedA_concreteChoices_of_eventually_boundedMean
      (R := R) (k := k) (ε := ε) hk3 hε hMeanBound
  intro a ha slack hslack
  have hk0 : 0 < k := Nat.zero_lt_of_lt (lt_of_lt_of_le (by decide : 1 < 3) hk3)
  have ha_nonneg : 0 ≤ a := le_of_lt (lt_trans (spikeRoot_pos hk0 hε) ha)
  filter_upwards [hbounded a ha_nonneg slack hslack] with d hd
  exact hd a ha ha_nonneg le_rfl

/-- Named frontier theorem for the corrected scale-loss supplier.

This is the strongest honest local closure currently available: the requested
fixed-`a` scale-budget predicate follows for `k ≥ 3` once the compact-window
positive-part bound on the deleted-background mean is proved.  The stronger
signature with only `1 < k` is not introduced here because the case `k = 2`
requires either a different scale budget or an additional smallness restriction
on the spike window. -/
theorem lower_scaleBudget_concreteChoices_of_meanPositivePartBoundedOnCompactA
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartBoundedOnCompactA R k ε) :
    lowerConcreteBackgroundScaleBudgetOnBetaInterval R k ε :=
  lower_scaleBudget_concreteChoices_of_boundedA
    (R := R) (k := k) (ε := ε) hk3 hε hMeanBound

/-- Corrected scale-budget supplier from the smallest currently isolated
scalar frontier.

This is as close as the scale-loss block can honestly get without proving the
deleted-background mean bound itself.  The requested no-input signature with
only `1 < k` is not asserted here: the `k = 2` budget needs either a different
scale error or an additional bounded/small spike window. -/
theorem lower_scaleBudget_concreteChoices_of_meanPositivePartEventuallyBounded
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k) :
    lowerConcreteBackgroundScaleBudgetOnBetaInterval R k ε :=
  lower_scaleBudget_concreteChoices_of_meanPositivePartBoundedOnCompactA
    (R := R) (k := k) (ε := ε) hk3 hε
    (lower_concrete_meanPositivePartBoundedOnCompactA_of_eventuallyBounded
      (R := R) (k := k) (ε := ε) hMeanBound)

/-- Corrected scale-budget supplier from a finite deleted-background mean
limit.

This is the sharpest scalar-facing version of the corrected scale route: the
obsolete unrestricted `lowerConcreteBackgroundScaleLoss` statement is not used;
it is enough to prove that the mean-centered deleted-background spherical mean
has a finite limit. -/
theorem lower_scaleBudget_concreteChoices_of_deletedBackgroundMean_tendsto
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε m : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMean :
      Tendsto (fun d : ℕ => lowerConcreteDeletedBackgroundMean R k d)
        atTop (nhds m)) :
    lowerConcreteBackgroundScaleBudgetOnBetaInterval R k ε :=
  lower_scaleBudget_concreteChoices_of_meanPositivePartEventuallyBounded
    (R := R) (k := k) (ε := ε) hk3 hε
    (lower_concrete_deletedBackgroundMean_positivePartEventuallyBounded_of_tendsto
      (R := R) (k := k) (m := m) hMean)

/-- Corrected scale-budget supplier from existence of a finite deleted-background
mean limit.

This is the compact scalar-facing frontier for the repaired scale route: the
old unrestricted scale-loss statement is not used, and the only remaining
scale-side mathematical input is that the deleted-background mean sequence has
some finite limit. -/
theorem lower_scaleBudget_concreteChoices_of_deletedBackgroundMean_hasFiniteLimit
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMean :
      ∃ m : ℝ,
        Tendsto (fun d : ℕ => lowerConcreteDeletedBackgroundMean R k d)
          atTop (nhds m)) :
    lowerConcreteBackgroundScaleBudgetOnBetaInterval R k ε :=
  lower_scaleBudget_concreteChoices_of_meanPositivePartEventuallyBounded
    (R := R) (k := k) (ε := ε) hk3 hε
    (lower_concrete_deletedBackgroundMean_positivePartEventuallyBounded_of_hasFiniteLimit
      (R := R) (k := k) hMean)

set_option maxHeartbeats 1000000 in
/-- Corrected deterministic `hColumnIncluded`.

This reroutes the one-column deterministic inclusion through the spherical
support comparison instead of the obsolete unrestricted
`lowerConcreteBackgroundScaleLoss` statement.  The remaining scale input is the
honest scalar budget
`lowerConcreteBackgroundScaleBudgetOnBetaInterval`, which is exactly the
Beta-mass upper-bound budget needed by
`lower_columnBackgroundContribution_lower_of_sphere_betaInterval_budget`.
-/
theorem
    lower_concrete_hColumnIncluded_of_closed_unitProfile_sphereBetaScaleBudget_sameBackgroundError_mixedLowerBound_sameMean_smallErrors
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ}
    (hk : 1 < k) (hε : 0 < ε)
    (hUnitProfile :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ Rmass : ℝ,
              ∀ u : EuclideanSpace ℂ (BipIndex (Fin d) (Fin d)),
                Rmass ∈
                  betaColumnIntervalSet
                    (betaColumnSpikeScale
                      (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                    (lowerConcreteDelta a slack d) →
                u ∈
                  lowerConcreteDirectionCapSet
                    lowerConcreteCanonicalDirection a slack d →
                ‖u‖ = 1 →
                a ^ k - lowerConcreteProfileError k ε a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hScaleBudget :
      lowerConcreteBackgroundScaleBudgetOnBetaInterval R k ε)
    (hMixedLower :
      lowerConcreteMixedLowerBound R lowerConcreteCanonicalDirection
        (lowerConcreteM R) lowerConcreteTau
        (fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
        (lowerConcreteMixedError R k ε) k ε) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          lowerConcreteColumnProb R lowerConcreteCanonicalDirection
              (lowerConcreteM R) lowerConcreteTau
              (fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
              k a slack d ≤
            lowerConcreteTargetProb R (lowerConcreteEps ε)
              (lowerConcreteDeletedBackgroundMean R k) k d := by
  intro a ha slack hslack
  have hBudgetEv :
      ∀ᶠ d in atTop,
        lowerConcreteEps ε d +
            lowerConcreteProfileError k ε a slack d +
              (lowerConcreteTau a slack d +
                lowerConcreteScaleError R k ε a slack d) +
            lowerConcreteMixedError R k ε a slack d + 0 ≤
          a ^ k :=
    lower_concrete_hBudget_sameMean_of_eventual_small
      (eps := lowerConcreteEps ε)
      (errProfile := lowerConcreteProfileError k ε)
      (τ := lowerConcreteTau)
      (errScale := lowerConcreteScaleError R k ε)
      (errMix := lowerConcreteMixedError R k ε)
      (k := k) (ε := ε) (Nat.zero_lt_of_lt hk) hε
      (lower_concrete_hEpsLe ε)
      (lower_concrete_hProfileSmall (k := k) (ε := ε))
      (fun a _ha slack _hslack => lower_concrete_hTauSmall a slack)
      (lower_concrete_hScaleSmall R (k := k) (ε := ε))
      (lower_concrete_hMixedSmall R (k := k) (ε := ε))
      a ha slack hslack
  filter_upwards
    [eventually_gt_atTop 0,
      lower_concrete_eventually_two_le_sample R,
      lower_concrete_hBetaScalePos
        (k := k) (Nat.zero_lt_of_lt hk) (ε := ε) hε a ha slack hslack,
      lower_concrete_hUpper (k := k) hk (ε := ε) a ha slack hslack,
      hUnitProfile a ha slack hslack,
      hScaleBudget a ha slack hslack,
      hMixedLower a ha slack hslack,
      hBudgetEv]
    with d hd hs2 hqpos_d hUpper_d hProfile_d hScaleBudget_d
      hMixedLower_d hBudget_d
  have hs : 0 < R.sample d := lt_of_lt_of_le (by norm_num) hs2
  let α₀ : Fin (R.sample d) := ⟨0, hs⟩
  let q₀ : ℝ :=
    betaColumnSpikeScale (lowerConcreteN d : ℝ) (spikeSpeed k d) a
  let δ : ℝ := lowerConcreteDelta a slack d
  let directionSet : Set (EuclideanSpace ℂ (BipIndex (Fin d) (Fin d))) :=
    lowerConcreteDirectionCapSet lowerConcreteCanonicalDirection a slack d
  let backgroundSet : Set (SampleMatrix (Fin d) (Fin d) (Fin (R.sample d))) :=
    backgroundTypicalSet
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      (lowerConcreteN d) (lowerConcreteM R a slack d)
      (lowerConcreteTau a slack d)
      (lowerConcreteDeletedBackgroundMean R k d) k
  let targetSet : Set (SampleMatrix (Fin d) (Fin d) (Fin (R.sample d))) :=
    columnMomentUpperTailSet
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      (lowerConcreteN d) (lowerConcreteEps ε d)
      (lowerConcreteDeletedBackgroundMean R k d) k
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  haveI : Nonempty (Fin (R.sample d)) := ⟨α₀⟩
  have hprob :
      (_root_.PptFactorization.AppendixB.sphericalModelMeasure
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))).real
        (sphericalOneColumnFavorableEvent
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          α₀ q₀ δ directionSet backgroundSet) ≤
      (_root_.PptFactorization.AppendixB.sphericalModelMeasure
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))).real
        targetSet := by
    refine
      lower_sphericalModelMeasure_real_le_of_subset_on_frobenius_sphere
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        (E :=
          sphericalOneColumnFavorableEvent
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            α₀ q₀ δ directionSet backgroundSet)
        (T := targetSet) ?_
    intro X hX hSphere
    have hmass_lower :
        q₀ ≤
          sampleColumnMass
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)) X α₀ := by
      exact hX.1.1
    have hmass_pos :
        0 <
          sampleColumnMass
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)) X α₀ :=
      lt_of_lt_of_le hqpos_d hmass_lower
    have hdir_unit :
        ‖sampleColumnDirection
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)) X α₀‖ = 1 :=
      sampleColumnDirection_norm_eq_one_of_columnMass_pos
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        X α₀ hmass_pos
    have hSpikeProfile :
        a ^ k - lowerConcreteProfileError k ε a slack d ≤
          columnDirectionSpikeProfile
            (p := Fin d) (q := Fin d)
            (lowerConcreteN d) k
            (sampleColumnMass
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)) X α₀)
            (sampleColumnDirection
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)) X α₀) := by
      exact hProfile_d
        (sampleColumnMass
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)) X α₀)
        (sampleColumnDirection
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)) X α₀)
        hX.1 hX.2.1 hdir_unit
    have hSpikeTransfer :
        columnDirectionSpikeProfile
            (p := Fin d) (q := Fin d)
            (lowerConcreteN d) k
            (sampleColumnMass
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)) X α₀)
            (sampleColumnDirection
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)) X α₀) - 0 ≤
          columnSpikeContribution
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            (lowerConcreteN d) k X α₀ :=
      columnSpikeContribution_transfer_noError
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        (α₀ := α₀) (N := lowerConcreteN d) (k := k) X
    have hSpike :
        a ^ k - lowerConcreteProfileError k ε a slack d ≤
          columnSpikeContribution
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            (lowerConcreteN d) k X α₀ := by
      linarith
    have hBackground :
        lowerConcreteDeletedBackgroundMean R k d -
            (lowerConcreteTau a slack d +
              lowerConcreteScaleError R k ε a slack d) ≤
          columnBackgroundContribution
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            (lowerConcreteN d) k X α₀ := by
      exact
        lower_columnBackgroundContribution_lower_of_sphere_betaInterval_budget
          (R := R) (k := k) (ε := ε) (a := a) (slack := slack)
          (q := q₀) (δ := δ) (d := d) hs X
          (by simpa [backgroundSet] using hX.2.2)
          hSphere
          (by simpa [q₀, δ] using hX.1)
          (le_of_lt (by simpa [q₀, δ] using hUpper_d))
          (by simpa [q₀, δ] using hScaleBudget_d)
    have hMixed :
        -lowerConcreteMixedError R k ε a slack d ≤
          columnMixedRemainder
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            (lowerConcreteN d) k X α₀ := by
      exact hMixedLower_d hs X (by simpa [α₀, q₀, δ, directionSet, backgroundSet] using hX)
    dsimp [targetSet, columnMomentUpperTailSet]
    exact
      column_spike_event_deviation_of_background_mixed
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        (N := lowerConcreteN d) (a := a) (eps := lowerConcreteEps ε d)
        (mean := lowerConcreteDeletedBackgroundMean R k d)
        (center := lowerConcreteDeletedBackgroundMean R k d)
        (errSpike := lowerConcreteProfileError k ε a slack d)
        (errBg := lowerConcreteTau a slack d +
          lowerConcreteScaleError R k ε a slack d)
        (errMix := lowerConcreteMixedError R k ε a slack d)
        (errMean := 0) (k := k) (X := X) (α₀ := α₀)
        hSpike hBackground hMixed
        (by simp)
        hBudget_d
  simpa [lowerConcreteColumnProb, lowerConcreteTargetProb, hs,
    α₀, q₀, δ, directionSet, backgroundSet, targetSet] using hprob

set_option maxHeartbeats 1000000 in
/-- Corrected deterministic `hColumnIncluded` with an explicit mixed-error
sequence.

This is the same sphere-supported/Beta-scale route as
`lower_concrete_hColumnIncluded_of_closed_unitProfile_sphereBetaScaleBudget_sameBackgroundError_mixedLowerBound_sameMean_smallErrors`,
but it does not hard-code the mixed error to `lowerConcreteMixedError`.  This is
the right interface for the deterministic mixed-word estimates, whose natural
envelope is an arbitrary `o(1)` sequence rather than the old fixed `1 / d`
budget. -/
theorem
    lower_concrete_hColumnIncluded_of_closed_unitProfile_sphereBetaScaleBudget_sameBackgroundError_mixedLowerBound_sameMean_smallErrors_withMixedError
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ}
    (hk : 1 < k) (hε : 0 < ε)
    {errMix : ℝ → ℝ → ℕ → ℝ}
    (hUnitProfile :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ Rmass : ℝ,
              ∀ u : EuclideanSpace ℂ (BipIndex (Fin d) (Fin d)),
                Rmass ∈
                  betaColumnIntervalSet
                    (betaColumnSpikeScale
                      (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                    (lowerConcreteDelta a slack d) →
                u ∈
                  lowerConcreteDirectionCapSet
                    lowerConcreteCanonicalDirection a slack d →
                ‖u‖ = 1 →
                a ^ k - lowerConcreteProfileError k ε a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hScaleBudget :
      lowerConcreteBackgroundScaleBudgetOnBetaInterval R k ε)
    (hMixedLower :
      lowerConcreteMixedLowerBoundOnSphere R lowerConcreteCanonicalDirection
        (lowerConcreteM R) lowerConcreteTau
        (fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
        errMix k ε)
    (hMixedSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errMix a slack d ≤ η) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          lowerConcreteColumnProb R lowerConcreteCanonicalDirection
              (lowerConcreteM R) lowerConcreteTau
              (fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
              k a slack d ≤
            lowerConcreteTargetProb R (lowerConcreteEps ε)
              (lowerConcreteDeletedBackgroundMean R k) k d := by
  intro a ha slack hslack
  have hBudgetEv :
      ∀ᶠ d in atTop,
        lowerConcreteEps ε d +
            lowerConcreteProfileError k ε a slack d +
              (lowerConcreteTau a slack d +
                lowerConcreteScaleError R k ε a slack d) +
            errMix a slack d + 0 ≤
          a ^ k :=
    lower_concrete_hBudget_sameMean_of_eventual_small
      (eps := lowerConcreteEps ε)
      (errProfile := lowerConcreteProfileError k ε)
      (τ := lowerConcreteTau)
      (errScale := lowerConcreteScaleError R k ε)
      (errMix := errMix)
      (k := k) (ε := ε) (Nat.zero_lt_of_lt hk) hε
      (lower_concrete_hEpsLe ε)
      (lower_concrete_hProfileSmall (k := k) (ε := ε))
      (fun a _ha slack _hslack => lower_concrete_hTauSmall a slack)
      (lower_concrete_hScaleSmall R (k := k) (ε := ε))
      hMixedSmall
      a ha slack hslack
  filter_upwards
    [eventually_gt_atTop 0,
      lower_concrete_eventually_two_le_sample R,
      lower_concrete_hBetaScalePos
        (k := k) (Nat.zero_lt_of_lt hk) (ε := ε) hε a ha slack hslack,
      lower_concrete_hUpper (k := k) hk (ε := ε) a ha slack hslack,
      hUnitProfile a ha slack hslack,
      hScaleBudget a ha slack hslack,
      hMixedLower a ha slack hslack,
      hBudgetEv]
    with d hd hs2 hqpos_d hUpper_d hProfile_d hScaleBudget_d
      hMixedLower_d hBudget_d
  have hs : 0 < R.sample d := lt_of_lt_of_le (by norm_num) hs2
  let α₀ : Fin (R.sample d) := ⟨0, hs⟩
  let q₀ : ℝ :=
    betaColumnSpikeScale (lowerConcreteN d : ℝ) (spikeSpeed k d) a
  let δ : ℝ := lowerConcreteDelta a slack d
  let directionSet : Set (EuclideanSpace ℂ (BipIndex (Fin d) (Fin d))) :=
    lowerConcreteDirectionCapSet lowerConcreteCanonicalDirection a slack d
  let backgroundSet : Set (SampleMatrix (Fin d) (Fin d) (Fin (R.sample d))) :=
    backgroundTypicalSet
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      (lowerConcreteN d) (lowerConcreteM R a slack d)
      (lowerConcreteTau a slack d)
      (lowerConcreteDeletedBackgroundMean R k d) k
  let targetSet : Set (SampleMatrix (Fin d) (Fin d) (Fin (R.sample d))) :=
    columnMomentUpperTailSet
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      (lowerConcreteN d) (lowerConcreteEps ε d)
      (lowerConcreteDeletedBackgroundMean R k d) k
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  haveI : Nonempty (Fin (R.sample d)) := ⟨α₀⟩
  have hprob :
      (_root_.PptFactorization.AppendixB.sphericalModelMeasure
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))).real
        (sphericalOneColumnFavorableEvent
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          α₀ q₀ δ directionSet backgroundSet) ≤
      (_root_.PptFactorization.AppendixB.sphericalModelMeasure
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))).real
        targetSet := by
    refine
      lower_sphericalModelMeasure_real_le_of_subset_on_frobenius_sphere
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        (E :=
          sphericalOneColumnFavorableEvent
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            α₀ q₀ δ directionSet backgroundSet)
        (T := targetSet) ?_
    intro X hX hSphere
    have hmass_lower :
        q₀ ≤
          sampleColumnMass
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)) X α₀ := by
      exact hX.1.1
    have hmass_pos :
        0 <
          sampleColumnMass
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)) X α₀ :=
      lt_of_lt_of_le hqpos_d hmass_lower
    have hdir_unit :
        ‖sampleColumnDirection
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)) X α₀‖ = 1 :=
      sampleColumnDirection_norm_eq_one_of_columnMass_pos
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        X α₀ hmass_pos
    have hSpikeProfile :
        a ^ k - lowerConcreteProfileError k ε a slack d ≤
          columnDirectionSpikeProfile
            (p := Fin d) (q := Fin d)
            (lowerConcreteN d) k
            (sampleColumnMass
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)) X α₀)
            (sampleColumnDirection
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)) X α₀) := by
      exact hProfile_d
        (sampleColumnMass
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)) X α₀)
        (sampleColumnDirection
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)) X α₀)
        hX.1 hX.2.1 hdir_unit
    have hSpikeTransfer :
        columnDirectionSpikeProfile
            (p := Fin d) (q := Fin d)
            (lowerConcreteN d) k
            (sampleColumnMass
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)) X α₀)
            (sampleColumnDirection
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)) X α₀) - 0 ≤
          columnSpikeContribution
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            (lowerConcreteN d) k X α₀ :=
      columnSpikeContribution_transfer_noError
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        (α₀ := α₀) (N := lowerConcreteN d) (k := k) X
    have hSpike :
        a ^ k - lowerConcreteProfileError k ε a slack d ≤
          columnSpikeContribution
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            (lowerConcreteN d) k X α₀ := by
      linarith
    have hBackground :
        lowerConcreteDeletedBackgroundMean R k d -
            (lowerConcreteTau a slack d +
              lowerConcreteScaleError R k ε a slack d) ≤
          columnBackgroundContribution
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            (lowerConcreteN d) k X α₀ := by
      exact
        lower_columnBackgroundContribution_lower_of_sphere_betaInterval_budget
          (R := R) (k := k) (ε := ε) (a := a) (slack := slack)
          (q := q₀) (δ := δ) (d := d) hs X
          (by simpa [backgroundSet] using hX.2.2)
          hSphere
          (by simpa [q₀, δ] using hX.1)
          (le_of_lt (by simpa [q₀, δ] using hUpper_d))
          (by simpa [q₀, δ] using hScaleBudget_d)
    have hMixed :
        -errMix a slack d ≤
          columnMixedRemainder
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            (lowerConcreteN d) k X α₀ := by
      exact hMixedLower_d hs X
        (by simpa [α₀, q₀, δ, directionSet, backgroundSet] using hX)
        hSphere
    dsimp [targetSet, columnMomentUpperTailSet]
    exact
      column_spike_event_deviation_of_background_mixed
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        (N := lowerConcreteN d) (a := a) (eps := lowerConcreteEps ε d)
        (mean := lowerConcreteDeletedBackgroundMean R k d)
        (center := lowerConcreteDeletedBackgroundMean R k d)
        (errSpike := lowerConcreteProfileError k ε a slack d)
        (errBg := lowerConcreteTau a slack d +
          lowerConcreteScaleError R k ε a slack d)
        (errMix := errMix a slack d)
        (errMean := 0) (k := k) (X := X) (α₀ := α₀)
        hSpike hBackground hMixed
        (by simp)
        hBudget_d
  simpa [lowerConcreteColumnProb, lowerConcreteTargetProb, hs,
    α₀, q₀, δ, directionSet, backgroundSet, targetSet] using hprob

set_option maxHeartbeats 1000000 in
/-- Concrete lower endpoint with the scale block rerouted through the corrected
spherical-support/Beta-interval budget.

This is the replacement API for the old
`lower_eventual_log_over_spikeSpeed_concreteModel_of_concreteScalarChoices`
path when working on `hScaleLoss`: it no longer asks for the false
`lowerConcreteBackgroundScaleLoss` predicate.  The remaining scale input is the
honest scalar budget `lowerConcreteBackgroundScaleBudgetOnBetaInterval`.
-/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_concreteScalarChoices_sphereBetaScaleBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ}
    (hk : 1 < k) (hε : 0 < ε)
    (hUnitProfile :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ Rmass : ℝ,
              ∀ u : EuclideanSpace ℂ (BipIndex (Fin d) (Fin d)),
                Rmass ∈
                  betaColumnIntervalSet
                    (betaColumnSpikeScale
                      (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                    (lowerConcreteDelta a slack d) →
                u ∈
                  lowerConcreteDirectionCapSet
                    lowerConcreteCanonicalDirection a slack d →
                ‖u‖ = 1 →
                a ^ k - lowerConcreteProfileError k ε a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hScaleBudget :
      lowerConcreteBackgroundScaleBudgetOnBetaInterval R k ε)
    (hMixedLower :
      lowerConcreteMixedLowerBound R lowerConcreteCanonicalDirection
        (lowerConcreteM R) lowerConcreteTau
        (fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
        (lowerConcreteMixedError R k ε) k ε)
    (hReference :
      ∀ᶠ d in atTop,
        ∀ i₀ : BipIndex (Fin d) (Fin d),
          SurfaceReferenceProjectiveCapConeCoordinateFormula
            (BipIndex (Fin d) (Fin d)) i₀)
    (hMoment :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            (_root_.PptFactorization.AppendixB.sphericalModelMeasure
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
              (backgroundMomentBadSet
                (p := Fin d) (q := Fin d)
                (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
                (lowerConcreteN d) (lowerConcreteTau a slack d)
                (lowerConcreteDeletedBackgroundMean R k d) k) ≤
              lowerConcreteMomentBound R k a slack d) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_referenceCone_canonicalDirection
      (R := R)
      (eps := lowerConcreteEps ε)
      (mean := lowerConcreteDeletedBackgroundMean R k)
      (M := lowerConcreteM R)
      (τ := lowerConcreteTau)
      (center := fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
      (bMoment := lowerConcreteMomentBound R k)
      (bSample := lowerConcreteSampleTailBound)
      (bGamma := lowerConcreteGammaTailBound)
      (k := k) (ε := ε) hk hε
      (lower_concrete_hColumnIncluded_of_closed_unitProfile_sphereBetaScaleBudget_sameBackgroundError_mixedLowerBound_sameMean_smallErrors
        (R := R) (k := k) (ε := ε) hk hε
        hUnitProfile hScaleBudget hMixedLower)
      hReference
      (lower_concrete_hBounds_of_reduced_spherical_bad_bounds
        (R := R) (M := lowerConcreteM R) (τ := lowerConcreteTau)
        (center := fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
        (bMoment := lowerConcreteMomentBound R k)
        (bSample := lowerConcreteSampleTailBound)
        (bGamma := lowerConcreteGammaTailBound)
        (k := k)
        (lower_concrete_hReduced_of_moment_and_gaussian_operator_tails
          (R := R) (M := lowerConcreteM R) (τ := lowerConcreteTau)
          (center := fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
          (bMoment := lowerConcreteMomentBound R k)
          (bSample := lowerConcreteSampleTailBound)
          (bGamma := lowerConcreteGammaTailBound)
          (k := k)
          hMoment
          (lower_concrete_hSampleTail_of_deletedColumn_operator_tails R)
          (lower_concrete_hGammaTail_of_deletedColumn_operator_tails R)))
      (lower_concrete_hBad_of_eventual_small
        (bMoment := lowerConcreteMomentBound R k)
        (bSample := lowerConcreteSampleTailBound)
        (bGamma := lowerConcreteGammaTailBound)
        (lower_concrete_hMomentSmall R (k := k))
        lower_concrete_hSampleSmall_commonThreshold
        lower_concrete_hGammaSmall_commonThreshold)

set_option maxHeartbeats 1000000 in
/-- Same corrected scale-route endpoint, but with an arbitrary moment bad-set
budget.

This is the hook needed by the second-moment/Chebyshev concentration route:
the moment budget only has to be eventually small; it need not be the stronger
hard-coded `exp (-d)` sequence. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_concreteScalarChoices_sphereBetaScaleBudget_withMomentBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ}
    (hk : 1 < k) (hε : 0 < ε)
    {bMoment : ℝ → ℝ → ℕ → ℝ}
    (hUnitProfile :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ Rmass : ℝ,
              ∀ u : EuclideanSpace ℂ (BipIndex (Fin d) (Fin d)),
                Rmass ∈
                  betaColumnIntervalSet
                    (betaColumnSpikeScale
                      (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                    (lowerConcreteDelta a slack d) →
                u ∈
                  lowerConcreteDirectionCapSet
                    lowerConcreteCanonicalDirection a slack d →
                ‖u‖ = 1 →
                a ^ k - lowerConcreteProfileError k ε a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hScaleBudget :
      lowerConcreteBackgroundScaleBudgetOnBetaInterval R k ε)
    (hMixedLower :
      lowerConcreteMixedLowerBound R lowerConcreteCanonicalDirection
        (lowerConcreteM R) lowerConcreteTau
        (fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
        (lowerConcreteMixedError R k ε) k ε)
    (hReference :
      ∀ᶠ d in atTop,
        ∀ i₀ : BipIndex (Fin d) (Fin d),
          SurfaceReferenceProjectiveCapConeCoordinateFormula
            (BipIndex (Fin d) (Fin d)) i₀)
    (hMoment :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            (_root_.PptFactorization.AppendixB.sphericalModelMeasure
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
              (backgroundMomentBadSet
                (p := Fin d) (q := Fin d)
                (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
                (lowerConcreteN d) (lowerConcreteTau a slack d)
                (lowerConcreteDeletedBackgroundMean R k d) k) ≤
              bMoment a slack d)
    (hMomentSmall :
      ∀ a : ℝ, ∀ slack : ℝ, ∀ η : ℝ, 0 < η →
        ∀ᶠ d in atTop, bMoment a slack d ≤ η) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_referenceCone_canonicalDirection
      (R := R)
      (eps := lowerConcreteEps ε)
      (mean := lowerConcreteDeletedBackgroundMean R k)
      (M := lowerConcreteM R)
      (τ := lowerConcreteTau)
      (center := fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
      (bMoment := bMoment)
      (bSample := lowerConcreteSampleTailBound)
      (bGamma := lowerConcreteGammaTailBound)
      (k := k) (ε := ε) hk hε
      (lower_concrete_hColumnIncluded_of_closed_unitProfile_sphereBetaScaleBudget_sameBackgroundError_mixedLowerBound_sameMean_smallErrors
        (R := R) (k := k) (ε := ε) hk hε
        hUnitProfile hScaleBudget hMixedLower)
      hReference
      (lower_concrete_hBounds_of_reduced_spherical_bad_bounds
        (R := R) (M := lowerConcreteM R) (τ := lowerConcreteTau)
        (center := fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
        (bMoment := bMoment)
        (bSample := lowerConcreteSampleTailBound)
        (bGamma := lowerConcreteGammaTailBound)
        (k := k)
        (lower_concrete_hReduced_of_moment_and_gaussian_operator_tails
          (R := R) (M := lowerConcreteM R) (τ := lowerConcreteTau)
          (center := fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
          (bMoment := bMoment)
          (bSample := lowerConcreteSampleTailBound)
          (bGamma := lowerConcreteGammaTailBound)
          (k := k)
          hMoment
          (lower_concrete_hSampleTail_of_deletedColumn_operator_tails R)
          (lower_concrete_hGammaTail_of_deletedColumn_operator_tails R)))
      (lower_concrete_hBad_of_eventual_small
        (bMoment := bMoment)
        (bSample := lowerConcreteSampleTailBound)
        (bGamma := lowerConcreteGammaTailBound)
        hMomentSmall
        lower_concrete_hSampleSmall_commonThreshold
        lower_concrete_hGammaSmall_commonThreshold)

set_option maxHeartbeats 1000000 in
/-- Corrected scale-route endpoint with both flexible budgets exposed.

This is the common endpoint for the PT mixed-word route and the
two-trace-Wick/Chebyshev concentration route: the mixed contribution is
controlled by an arbitrary `o(1)` envelope, and the background bad set is
controlled by an arbitrary eventually-small moment budget. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_concreteScalarChoices_sphereBetaScaleBudget_withMomentBudgetAndMixedError
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ}
    (hk : 1 < k) (hε : 0 < ε)
    {bMoment errMix : ℝ → ℝ → ℕ → ℝ}
    (hUnitProfile :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ Rmass : ℝ,
              ∀ u : EuclideanSpace ℂ (BipIndex (Fin d) (Fin d)),
                Rmass ∈
                  betaColumnIntervalSet
                    (betaColumnSpikeScale
                      (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                    (lowerConcreteDelta a slack d) →
                u ∈
                  lowerConcreteDirectionCapSet
                    lowerConcreteCanonicalDirection a slack d →
                ‖u‖ = 1 →
                a ^ k - lowerConcreteProfileError k ε a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hScaleBudget :
      lowerConcreteBackgroundScaleBudgetOnBetaInterval R k ε)
    (hMixedLower :
      lowerConcreteMixedLowerBoundOnSphere R lowerConcreteCanonicalDirection
        (lowerConcreteM R) lowerConcreteTau
        (fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
        errMix k ε)
    (hMixedSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errMix a slack d ≤ η)
    (hReference :
      ∀ᶠ d in atTop,
        ∀ i₀ : BipIndex (Fin d) (Fin d),
          SurfaceReferenceProjectiveCapConeCoordinateFormula
            (BipIndex (Fin d) (Fin d)) i₀)
    (hMoment :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            (_root_.PptFactorization.AppendixB.sphericalModelMeasure
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
              (backgroundMomentBadSet
                (p := Fin d) (q := Fin d)
                (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
                (lowerConcreteN d) (lowerConcreteTau a slack d)
                (lowerConcreteDeletedBackgroundMean R k d) k) ≤
              bMoment a slack d)
    (hMomentSmall :
      ∀ a : ℝ, ∀ slack : ℝ, ∀ η : ℝ, 0 < η →
        ∀ᶠ d in atTop, bMoment a slack d ≤ η) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_referenceCone_canonicalDirection
      (R := R)
      (eps := lowerConcreteEps ε)
      (mean := lowerConcreteDeletedBackgroundMean R k)
      (M := lowerConcreteM R)
      (τ := lowerConcreteTau)
      (center := fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
      (bMoment := bMoment)
      (bSample := lowerConcreteSampleTailBound)
      (bGamma := lowerConcreteGammaTailBound)
      (k := k) (ε := ε) hk hε
      (lower_concrete_hColumnIncluded_of_closed_unitProfile_sphereBetaScaleBudget_sameBackgroundError_mixedLowerBound_sameMean_smallErrors_withMixedError
        (R := R) (k := k) (ε := ε) hk hε
        hUnitProfile hScaleBudget hMixedLower hMixedSmall)
      hReference
      (lower_concrete_hBounds_of_reduced_spherical_bad_bounds
        (R := R) (M := lowerConcreteM R) (τ := lowerConcreteTau)
        (center := fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
        (bMoment := bMoment)
        (bSample := lowerConcreteSampleTailBound)
        (bGamma := lowerConcreteGammaTailBound)
        (k := k)
        (lower_concrete_hReduced_of_moment_and_gaussian_operator_tails
          (R := R) (M := lowerConcreteM R) (τ := lowerConcreteTau)
          (center := fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
          (bMoment := bMoment)
          (bSample := lowerConcreteSampleTailBound)
          (bGamma := lowerConcreteGammaTailBound)
          (k := k)
          hMoment
          (lower_concrete_hSampleTail_of_deletedColumn_operator_tails R)
          (lower_concrete_hGammaTail_of_deletedColumn_operator_tails R)))
      (lower_concrete_hBad_of_eventual_small
        (bMoment := bMoment)
        (bSample := lowerConcreteSampleTailBound)
        (bGamma := lowerConcreteGammaTailBound)
        hMomentSmall
        lower_concrete_hSampleSmall_commonThreshold
        lower_concrete_hGammaSmall_commonThreshold)

set_option maxHeartbeats 1000000 in
/-- Concrete lower endpoint with corrected scale routing and an explicit mixed
error sequence.

Compared with
`lower_eventual_log_over_spikeSpeed_concreteModel_of_concreteScalarChoices_sphereBetaScaleBudget`,
this wrapper keeps the mixed error as a visible `errMix` together with its
eventual-smallness proof.  It is the preferred endpoint for the mixed-word
frontier, where the deterministic envelope is `o(1)` but need not be the old
hard-coded `1 / d` sequence. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_concreteScalarChoices_sphereBetaScaleBudget_withMixedError
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ}
    (hk : 1 < k) (hε : 0 < ε)
    {errMix : ℝ → ℝ → ℕ → ℝ}
    (hUnitProfile :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ Rmass : ℝ,
              ∀ u : EuclideanSpace ℂ (BipIndex (Fin d) (Fin d)),
                Rmass ∈
                  betaColumnIntervalSet
                    (betaColumnSpikeScale
                      (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                    (lowerConcreteDelta a slack d) →
                u ∈
                  lowerConcreteDirectionCapSet
                    lowerConcreteCanonicalDirection a slack d →
                ‖u‖ = 1 →
                a ^ k - lowerConcreteProfileError k ε a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hScaleBudget :
      lowerConcreteBackgroundScaleBudgetOnBetaInterval R k ε)
    (hMixedLower :
      lowerConcreteMixedLowerBoundOnSphere R lowerConcreteCanonicalDirection
        (lowerConcreteM R) lowerConcreteTau
        (fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
        errMix k ε)
    (hMixedSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errMix a slack d ≤ η)
    (hReference :
      ∀ᶠ d in atTop,
        ∀ i₀ : BipIndex (Fin d) (Fin d),
          SurfaceReferenceProjectiveCapConeCoordinateFormula
            (BipIndex (Fin d) (Fin d)) i₀)
    (hMoment :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            (_root_.PptFactorization.AppendixB.sphericalModelMeasure
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
              (backgroundMomentBadSet
                (p := Fin d) (q := Fin d)
                (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
                (lowerConcreteN d) (lowerConcreteTau a slack d)
                (lowerConcreteDeletedBackgroundMean R k d) k) ≤
              lowerConcreteMomentBound R k a slack d) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_referenceCone_canonicalDirection
      (R := R)
      (eps := lowerConcreteEps ε)
      (mean := lowerConcreteDeletedBackgroundMean R k)
      (M := lowerConcreteM R)
      (τ := lowerConcreteTau)
      (center := fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
      (bMoment := lowerConcreteMomentBound R k)
      (bSample := lowerConcreteSampleTailBound)
      (bGamma := lowerConcreteGammaTailBound)
      (k := k) (ε := ε) hk hε
      (lower_concrete_hColumnIncluded_of_closed_unitProfile_sphereBetaScaleBudget_sameBackgroundError_mixedLowerBound_sameMean_smallErrors_withMixedError
        (R := R) (k := k) (ε := ε) hk hε
        hUnitProfile hScaleBudget hMixedLower hMixedSmall)
      hReference
      (lower_concrete_hBounds_of_reduced_spherical_bad_bounds
        (R := R) (M := lowerConcreteM R) (τ := lowerConcreteTau)
        (center := fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
        (bMoment := lowerConcreteMomentBound R k)
        (bSample := lowerConcreteSampleTailBound)
        (bGamma := lowerConcreteGammaTailBound)
        (k := k)
        (lower_concrete_hReduced_of_moment_and_gaussian_operator_tails
          (R := R) (M := lowerConcreteM R) (τ := lowerConcreteTau)
          (center := fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
          (bMoment := lowerConcreteMomentBound R k)
          (bSample := lowerConcreteSampleTailBound)
          (bGamma := lowerConcreteGammaTailBound)
          (k := k)
          hMoment
          (lower_concrete_hSampleTail_of_deletedColumn_operator_tails R)
          (lower_concrete_hGammaTail_of_deletedColumn_operator_tails R)))
      (lower_concrete_hBad_of_eventual_small
        (bMoment := lowerConcreteMomentBound R k)
        (bSample := lowerConcreteSampleTailBound)
        (bGamma := lowerConcreteGammaTailBound)
        (lower_concrete_hMomentSmall R (k := k))
        lower_concrete_hSampleSmall_commonThreshold
        lower_concrete_hGammaSmall_commonThreshold)

/-!
The old standalone target `lower_scaleLoss_concreteChoices` was intentionally
removed from this file.  Its premise only knew that the normalized deleted
background direction was typical, which is not enough to control the scale of
the deleted block.  The valid route above uses the Frobenius-sphere support and
the Beta interval upper bound, leaving the scalar budget
`lowerConcreteBackgroundScaleBudgetOnBetaInterval` visible instead of proving a
false unrestricted statement.
-/

end AppendixB
