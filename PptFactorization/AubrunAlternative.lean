import Mathlib.Data.Nat.Choose.Central
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Alternative Aubrun threshold route

This file contains small public adapters for the moment-Hankel proof route to
the PPT threshold.  It deliberately keeps the analytic probability estimates
out of scope: the first deterministic bridge is the finite certificate saying
that a negative shifted odd Hankel determinant rules out the corresponding
finite PPT moment criterion.
-/

namespace AubrunAlternative

open MeasureTheory
open scoped BigOperators ENNReal

/-- If a real spectral value is negative, its centered distance from `1`
contributes at least one unit to every even centered moment. -/
theorem one_le_centered_even_power_of_neg (x : ℝ) (m : ℕ) (hx : x < 0) :
    1 ≤ (x - 1) ^ (2 * m) := by
  have hsq : 1 ≤ (x - 1) ^ 2 := by
    nlinarith [sq_nonneg x]
  rw [show (x - 1) ^ (2 * m) = ((x - 1) ^ 2) ^ m by rw [pow_mul]]
  exact one_le_pow₀ hsq

/-- Even centered powers are nonnegative. -/
theorem centered_even_power_nonneg (x : ℝ) (m : ℕ) :
    0 ≤ (x - 1) ^ (2 * m) := by
  rw [show (x - 1) ^ (2 * m) = ((x - 1) ^ 2) ^ m by rw [pow_mul]]
  exact pow_nonneg (sq_nonneg (x - 1)) m

/-- Deterministic fixed-moment bridge for the `λ > 4` route:
the number of negative spectral values is bounded by any even centered moment.

For the normalized partial transpose eigenvalues `y_i`, this is the formal
version of the blackboard observation
`y_i < 0 ⇒ |y_i - 1| ≥ 1`.  After dividing by the matrix dimension, fixed
moment convergence gives an almost-positivity statement, but not yet full PPT. -/
theorem neg_count_le_centered_even_moment {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (m : ℕ) :
    ((Finset.univ.filter fun i : ι => f i < 0).card : ℝ) ≤
      ∑ i : ι, (f i - 1) ^ (2 * m) := by
  classical
  rw [show ((Finset.univ.filter fun i : ι => f i < 0).card : ℝ) =
      ∑ i : ι, if f i < 0 then (1 : ℝ) else 0 by
    simp]
  refine Finset.sum_le_sum ?_
  intro i _hi
  by_cases hneg : f i < 0
  · simpa [hneg] using one_le_centered_even_power_of_neg (f i) m hneg
  · simpa [hneg] using centered_even_power_nonneg (f i) m

/-- Normalized version of `neg_count_le_centered_even_moment`.

This is the deterministic fixed-moment bridge in empirical-measure form: the
fraction of negative spectral values is bounded by the normalized centered
even moment. -/
theorem neg_count_average_le_centered_even_moment_average {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (m : ℕ) :
    ((Finset.univ.filter fun i : ι => f i < 0).card : ℝ) / (Fintype.card ι : ℝ) ≤
      (∑ i : ι, (f i - 1) ^ (2 * m)) / (Fintype.card ι : ℝ) := by
  have hcount := neg_count_le_centered_even_moment (f := f) m
  exact div_le_div_of_nonneg_right hcount (Nat.cast_nonneg _)

/-- Deterministic event adapter for fixed-moment bulk almost-positivity:
once the normalized centered even moment is at most `η`, the normalized count
of negative spectral values is also at most `η`. -/
theorem neg_count_average_le_of_centered_even_moment_average_le {ι : Type*}
    [Fintype ι] (f : ι → ℝ) (m : ℕ) {η : ℝ}
    (hMoment :
      (∑ i : ι, (f i - 1) ^ (2 * m)) / (Fintype.card ι : ℝ) ≤ η) :
    ((Finset.univ.filter fun i : ι => f i < 0).card : ℝ) / (Fintype.card ι : ℝ) ≤
      η :=
  le_trans (neg_count_average_le_centered_even_moment_average (f := f) m) hMoment

/-- Pointwise negative-mass control by an even centered moment of positive
order.  The `m + 1` indexing avoids the false zero-th moment variant.

This is the scalar inequality behind the trace-mass version of almost
positivity: if `y < 0`, then `-y ≤ (y - 1)^2`, and higher even powers only
increase the right-hand side on that region. -/
theorem neg_part_le_centered_even_power_succ (x : ℝ) (m : ℕ) :
    max 0 (-x) ≤ (x - 1) ^ (2 * (m + 1)) := by
  by_cases hx : x < 0
  · have hmax : max 0 (-x) = -x := by
      exact max_eq_right (by linarith)
    rw [hmax]
    have hmass : -x ≤ (x - 1) ^ 2 := by
      nlinarith [sq_nonneg x]
    have hsq : 1 ≤ (x - 1) ^ 2 := by
      nlinarith [sq_nonneg x]
    have hpow : (x - 1) ^ 2 ≤ ((x - 1) ^ 2) ^ (m + 1) := by
      exact le_self_pow₀ hsq (by omega)
    rw [show (x - 1) ^ (2 * (m + 1)) = ((x - 1) ^ 2) ^ (m + 1) by
      rw [pow_mul]]
    exact le_trans hmass hpow
  · have hmax : max 0 (-x) = 0 := by
      exact max_eq_left (by linarith)
    rw [hmax]
    rw [show (x - 1) ^ (2 * (m + 1)) = ((x - 1) ^ 2) ^ (m + 1) by
      rw [pow_mul]]
    exact pow_nonneg (sq_nonneg (x - 1)) (m + 1)

/-- Deterministic fixed-moment bridge for the trace-mass version of
almost-positivity: the total negative part of a finite real spectrum is bounded
by any positive even centered moment. -/
theorem neg_mass_le_centered_even_moment_succ {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (m : ℕ) :
    (∑ i : ι, max 0 (-(f i))) ≤
      ∑ i : ι, (f i - 1) ^ (2 * (m + 1)) := by
  classical
  exact Finset.sum_le_sum (fun i _hi =>
    neg_part_le_centered_even_power_succ (f i) m)

/-- Normalized trace-mass version of
`neg_mass_le_centered_even_moment_succ`.

This is the empirical negative-mass bridge: the average negative part of a
finite real spectrum is bounded by the normalized positive even centered
moment. -/
theorem neg_mass_average_le_centered_even_moment_average_succ {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (m : ℕ) :
    (∑ i : ι, max 0 (-(f i))) / (Fintype.card ι : ℝ) ≤
      (∑ i : ι, (f i - 1) ^ (2 * (m + 1))) / (Fintype.card ι : ℝ) := by
  have hmass := neg_mass_le_centered_even_moment_succ (f := f) m
  exact div_le_div_of_nonneg_right hmass (Nat.cast_nonneg _)

/-- Deterministic event adapter for fixed-moment negative trace mass:
once the normalized positive even centered moment is at most `η`, the
normalized negative part is also at most `η`. -/
theorem neg_mass_average_le_of_centered_even_moment_average_le_succ {ι : Type*}
    [Fintype ι] (f : ι → ℝ) (m : ℕ) {η : ℝ}
    (hMoment :
      (∑ i : ι, (f i - 1) ^ (2 * (m + 1))) / (Fintype.card ι : ℝ) ≤ η) :
    (∑ i : ι, max 0 (-(f i))) / (Fintype.card ι : ℝ) ≤ η :=
  le_trans (neg_mass_average_le_centered_even_moment_average_succ (f := f) m) hMoment

/-- Catalan growth bound in the scalar form needed by the fixed-moment
`λ > 4` bulk route. -/
theorem catalan_le_four_pow_real (m : ℕ) : (catalan m : ℝ) ≤ (4 : ℝ) ^ m := by
  have hcat_nat : catalan m ≤ Nat.centralBinom m := by
    rw [catalan_eq_centralBinom_div]
    exact Nat.div_le_self _ _
  exact_mod_cast (le_trans hcat_nat (Nat.centralBinom_le_four_pow m))

/-- Scalar Catalan choice for the fixed-moment `λ > 4` bulk route.

For every `λ > 4` and every tolerance `η > 0`, a sufficiently high fixed
centered semicircle moment has Catalan contribution below `η`. -/
theorem exists_catalan_div_pow_lt_of_four_lt {lam η : ℝ}
    (hlam : 4 < lam) (hη : 0 < η) :
    ∃ m : ℕ, (catalan m : ℝ) / lam ^ m < η := by
  have hlam_pos : 0 < lam := by linarith
  have hr_nonneg : 0 ≤ (4 : ℝ) / lam := div_nonneg (by norm_num) (le_of_lt hlam_pos)
  have hr_lt_one : (4 : ℝ) / lam < 1 := (div_lt_one hlam_pos).2 hlam
  have htend : Filter.Tendsto (fun m : ℕ => ((4 : ℝ) / lam) ^ m)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr_nonneg hr_lt_one
  have hevent : ∀ᶠ m : ℕ in Filter.atTop, ((4 : ℝ) / lam) ^ m < η :=
    htend.eventually_lt_const hη
  rcases Filter.eventually_atTop.1 hevent with ⟨m0, hm0⟩
  refine ⟨m0, ?_⟩
  have hbound : (catalan m0 : ℝ) / lam ^ m0 ≤ (4 : ℝ) ^ m0 / lam ^ m0 :=
    div_le_div_of_nonneg_right (catalan_le_four_pow_real m0)
      (pow_nonneg (le_of_lt hlam_pos) m0)
  have hdivpow : (4 : ℝ) ^ m0 / lam ^ m0 = ((4 : ℝ) / lam) ^ m0 := by
    rw [div_pow]
  exact lt_of_le_of_lt (hbound.trans_eq hdivpow) (hm0 m0 le_rfl)

/-- Fixed-moment bulk package for the `λ > 4` count route.

Choose a fixed even moment whose Catalan limit lies below half the requested
tolerance.  Then any finite spectrum whose normalized centered moment is at
most that Catalan limit plus the other half has at most an `η` fraction of
negative values. -/
theorem exists_neg_count_average_le_of_centered_even_moment_average_le_catalan_add
    {ι : Type*} [Fintype ι] {lam η : ℝ}
    (hlam : 4 < lam) (hη : 0 < η) :
    ∃ m : ℕ, ∀ f : ι → ℝ,
      (∑ i : ι, (f i - 1) ^ (2 * m)) / (Fintype.card ι : ℝ) ≤
          (catalan m : ℝ) / lam ^ m + η / 2 →
      ((Finset.univ.filter fun i : ι => f i < 0).card : ℝ) /
          (Fintype.card ι : ℝ) ≤ η := by
  have hηhalf : 0 < η / 2 := by linarith
  rcases exists_catalan_div_pow_lt_of_four_lt (lam := lam) (η := η / 2) hlam hηhalf with
    ⟨m, hm⟩
  refine ⟨m, ?_⟩
  intro f hMoment
  exact neg_count_average_le_of_centered_even_moment_average_le (f := f) m
    (le_trans hMoment (le_of_lt (by linarith)))

/-- Fixed-moment bulk package for the negative trace-mass route.

The positive-order indexing matches `neg_mass_average_le_*_succ`: choose `m`
so the centered semicircle contribution at order `2 * (m + 1)` is below half
the requested tolerance, then allow the other half for finite-dimensional
moment error. -/
theorem exists_neg_mass_average_le_of_centered_even_moment_average_le_catalan_add_succ
    {ι : Type*} [Fintype ι] {lam η : ℝ}
    (hlam : 4 < lam) (hη : 0 < η) :
    ∃ m : ℕ, ∀ f : ι → ℝ,
      (∑ i : ι, (f i - 1) ^ (2 * (m + 1))) / (Fintype.card ι : ℝ) ≤
          (catalan (m + 1) : ℝ) / lam ^ (m + 1) + η / 2 →
      (∑ i : ι, max 0 (-(f i))) / (Fintype.card ι : ℝ) ≤ η := by
  have hlam_pos : 0 < lam := by linarith
  have hηhalf : 0 < η / 2 := by linarith
  have hr_nonneg : 0 ≤ (4 : ℝ) / lam := div_nonneg (by norm_num) (le_of_lt hlam_pos)
  have hr_lt_one : (4 : ℝ) / lam < 1 := (div_lt_one hlam_pos).2 hlam
  have htend : Filter.Tendsto (fun m : ℕ => ((4 : ℝ) / lam) ^ m)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr_nonneg hr_lt_one
  have hevent : ∀ᶠ m : ℕ in Filter.atTop, ((4 : ℝ) / lam) ^ m < η / 2 :=
    htend.eventually_lt_const hηhalf
  rcases Filter.eventually_atTop.1 hevent with ⟨m0, hm0⟩
  refine ⟨m0, ?_⟩
  intro f hMoment
  let c : ℝ := (catalan (m0 + 1) : ℝ) / lam ^ (m0 + 1)
  have hbound : c ≤ (4 : ℝ) ^ (m0 + 1) / lam ^ (m0 + 1) := by
    dsimp [c]
    exact div_le_div_of_nonneg_right (catalan_le_four_pow_real (m0 + 1))
      (pow_nonneg (le_of_lt hlam_pos) (m0 + 1))
  have hdivpow : (4 : ℝ) ^ (m0 + 1) / lam ^ (m0 + 1) =
      ((4 : ℝ) / lam) ^ (m0 + 1) := by
    rw [div_pow]
  have hcat : c < η / 2 :=
    lt_of_le_of_lt (hbound.trans_eq hdivpow) (hm0 (m0 + 1) (Nat.le_succ m0))
  have htol : c + η / 2 ≤ η := by
    have hadd : c + η / 2 < η / 2 + η / 2 := add_lt_add_left hcat (η / 2)
    have hhalf_sum : η / 2 + η / 2 = η := by ring
    exact le_of_lt (by simpa [hhalf_sum] using hadd)
  exact neg_mass_average_le_of_centered_even_moment_average_le_succ (f := f) m0
    (le_trans hMoment htol)

/-- Fixed-moment bulk package giving both empirical almost-positivity controls.

A single positive even centered moment controls both the fraction of negative
values and the normalized negative trace mass.  This is the deterministic
endpoint consumed by a future fixed-order moment convergence/concentration
supplier. -/
theorem exists_neg_count_and_mass_average_le_of_centered_even_moment_average_le_catalan_add_succ
    {ι : Type*} [Fintype ι] {lam η : ℝ}
    (hlam : 4 < lam) (hη : 0 < η) :
    ∃ m : ℕ, ∀ f : ι → ℝ,
      (∑ i : ι, (f i - 1) ^ (2 * (m + 1))) / (Fintype.card ι : ℝ) ≤
          (catalan (m + 1) : ℝ) / lam ^ (m + 1) + η / 2 →
      ((Finset.univ.filter fun i : ι => f i < 0).card : ℝ) /
          (Fintype.card ι : ℝ) ≤ η ∧
        (∑ i : ι, max 0 (-(f i))) / (Fintype.card ι : ℝ) ≤ η := by
  have hlam_pos : 0 < lam := by linarith
  have hηhalf : 0 < η / 2 := by linarith
  have hr_nonneg : 0 ≤ (4 : ℝ) / lam := div_nonneg (by norm_num) (le_of_lt hlam_pos)
  have hr_lt_one : (4 : ℝ) / lam < 1 := (div_lt_one hlam_pos).2 hlam
  have htend : Filter.Tendsto (fun m : ℕ => ((4 : ℝ) / lam) ^ m)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr_nonneg hr_lt_one
  have hevent : ∀ᶠ m : ℕ in Filter.atTop, ((4 : ℝ) / lam) ^ m < η / 2 :=
    htend.eventually_lt_const hηhalf
  rcases Filter.eventually_atTop.1 hevent with ⟨m0, hm0⟩
  refine ⟨m0, ?_⟩
  intro f hMoment
  let c : ℝ := (catalan (m0 + 1) : ℝ) / lam ^ (m0 + 1)
  have hbound : c ≤ (4 : ℝ) ^ (m0 + 1) / lam ^ (m0 + 1) := by
    dsimp [c]
    exact div_le_div_of_nonneg_right (catalan_le_four_pow_real (m0 + 1))
      (pow_nonneg (le_of_lt hlam_pos) (m0 + 1))
  have hdivpow : (4 : ℝ) ^ (m0 + 1) / lam ^ (m0 + 1) =
      ((4 : ℝ) / lam) ^ (m0 + 1) := by
    rw [div_pow]
  have hcat : c < η / 2 :=
    lt_of_le_of_lt (hbound.trans_eq hdivpow) (hm0 (m0 + 1) (Nat.le_succ m0))
  have htol : c + η / 2 ≤ η := by
    have hadd : c + η / 2 < η / 2 + η / 2 := add_lt_add_left hcat (η / 2)
    have hhalf_sum : η / 2 + η / 2 = η := by ring
    exact le_of_lt (by simpa [hhalf_sum] using hadd)
  have hMomentEta :
      (∑ i : ι, (f i - 1) ^ (2 * (m0 + 1))) / (Fintype.card ι : ℝ) ≤ η :=
    le_trans hMoment htol
  constructor
  · exact neg_count_average_le_of_centered_even_moment_average_le (f := f) (m0 + 1)
      hMomentEta
  · exact neg_mass_average_le_of_centered_even_moment_average_le_succ (f := f) m0
      hMomentEta

/-- Bad-event form of the fixed-moment bulk package.

For `λ > 4`, a sufficiently high fixed positive even moment is chosen so that
failure of either empirical almost-positivity control forces the normalized
centered moment to exceed its Catalan limit plus the half-tolerance budget.
This is the deterministic inclusion consumed by a later concentration bound. -/
theorem exists_centered_moment_threshold_lt_of_neg_count_or_mass_gt
    {ι : Type*} [Fintype ι] {lam η : ℝ}
    (hlam : 4 < lam) (hη : 0 < η) :
    ∃ m : ℕ, ∀ f : ι → ℝ,
      η < ((Finset.univ.filter fun i : ι => f i < 0).card : ℝ) /
          (Fintype.card ι : ℝ) ∨
        η < (∑ i : ι, max 0 (-(f i))) / (Fintype.card ι : ℝ) →
      (catalan (m + 1) : ℝ) / lam ^ (m + 1) + η / 2 <
        (∑ i : ι, (f i - 1) ^ (2 * (m + 1))) / (Fintype.card ι : ℝ) := by
  rcases exists_neg_count_and_mass_average_le_of_centered_even_moment_average_le_catalan_add_succ
      (ι := ι) hlam hη with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  intro f hbad
  by_contra hnot
  have hMoment :
      (∑ i : ι, (f i - 1) ^ (2 * (m + 1))) / (Fintype.card ι : ℝ) ≤
          (catalan (m + 1) : ℝ) / lam ^ (m + 1) + η / 2 :=
    le_of_not_gt hnot
  rcases hm f hMoment with ⟨hcount, hmass⟩
  rcases hbad with hbad | hbad
  · exact (not_lt_of_ge hcount) hbad
  · exact (not_lt_of_ge hmass) hbad

/-- Set-valued bad-event inclusion for the fixed-moment bulk package.

This is the probability-facing form of
`exists_centered_moment_threshold_lt_of_neg_count_or_mass_gt`: for any random
finite spectrum `F`, the event where either empirical almost-positivity
control fails is contained in the event where the normalized centered moment
exceeds its Catalan-plus-half-tolerance threshold. -/
theorem exists_bad_event_subset_centered_moment_threshold_event
    {Ω ι : Type*} [Fintype ι] {lam η : ℝ}
    (hlam : 4 < lam) (hη : 0 < η) :
    ∃ m : ℕ, ∀ F : Ω → ι → ℝ,
      {ω : Ω |
        η < ((Finset.univ.filter fun i : ι => F ω i < 0).card : ℝ) /
            (Fintype.card ι : ℝ) ∨
          η < (∑ i : ι, max 0 (-(F ω i))) / (Fintype.card ι : ℝ)} ⊆
        {ω : Ω |
          (catalan (m + 1) : ℝ) / lam ^ (m + 1) + η / 2 <
            (∑ i : ι, (F ω i - 1) ^ (2 * (m + 1))) / (Fintype.card ι : ℝ)} := by
  rcases exists_centered_moment_threshold_lt_of_neg_count_or_mass_gt
      (ι := ι) hlam hη with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  intro F ω hω
  exact hm (F ω) hω

/-- Measure-valued bad-event adapter for the fixed-moment bulk package.

This is only the monotonicity step after
`exists_bad_event_subset_centered_moment_threshold_event`: if a concentration
or moment supplier bounds the threshold event, the same bound holds for the
event where either empirical almost-positivity control fails. -/
theorem exists_bad_event_measure_le_of_centered_moment_threshold_event_measure_le
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {lam η : ℝ}
    (hlam : 4 < lam) (hη : 0 < η) :
    ∃ m : ℕ, ∀ (μ : Measure Ω) (F : Ω → ι → ℝ) {δ : ℝ≥0∞},
      μ {ω : Ω |
        (catalan (m + 1) : ℝ) / lam ^ (m + 1) + η / 2 <
          (∑ i : ι, (F ω i - 1) ^ (2 * (m + 1))) / (Fintype.card ι : ℝ)} ≤ δ →
      μ {ω : Ω |
        η < ((Finset.univ.filter fun i : ι => F ω i < 0).card : ℝ) /
            (Fintype.card ι : ℝ) ∨
          η < (∑ i : ι, max 0 (-(F ω i))) / (Fintype.card ι : ℝ)} ≤ δ := by
  rcases exists_bad_event_subset_centered_moment_threshold_event
      (Ω := Ω) (ι := ι) hlam hη with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  intro μ F δ hthreshold
  exact le_trans (measure_mono (hm F)) hthreshold

/-- Dependent-index measure-valued bad-event adapter for the fixed-moment bulk
package.

Concrete matrix spectra usually have an index type depending on the dimension.
This wrapper chooses one fixed moment order from `λ > 4` and transfers any
dimensionwise bound on the centered-moment threshold event to the event where
either empirical almost-positivity control fails. -/
theorem exists_bad_event_measure_le_of_centered_moment_threshold_event_measure_le_dependent
    {Ω : Type*} {ι : ℕ → Type*} [MeasurableSpace Ω] [∀ d : ℕ, Fintype (ι d)]
    {lam η : ℝ} (hlam : 4 < lam) (hη : 0 < η) :
    ∃ m : ℕ, ∀ (μ : ℕ → Measure Ω) (F : (d : ℕ) → Ω → ι d → ℝ)
      {δ : ℕ → ℝ≥0∞},
      (∀ d : ℕ,
        μ d {ω : Ω |
          (catalan (m + 1) : ℝ) / lam ^ (m + 1) + η / 2 <
            (∑ i : ι d, (F d ω i - 1) ^ (2 * (m + 1))) /
              (Fintype.card (ι d) : ℝ)} ≤ δ d) →
      ∀ d : ℕ,
        μ d {ω : Ω |
          η < ((Finset.univ.filter fun i : ι d => F d ω i < 0).card : ℝ) /
              (Fintype.card (ι d) : ℝ) ∨
            η < (∑ i : ι d, max 0 (-(F d ω i))) /
              (Fintype.card (ι d) : ℝ)} ≤ δ d := by
  have hlam_pos : 0 < lam := by linarith
  have hηhalf : 0 < η / 2 := by linarith
  have hr_nonneg : 0 ≤ (4 : ℝ) / lam := div_nonneg (by norm_num) (le_of_lt hlam_pos)
  have hr_lt_one : (4 : ℝ) / lam < 1 := (div_lt_one hlam_pos).2 hlam
  have htend : Filter.Tendsto (fun m : ℕ => ((4 : ℝ) / lam) ^ m)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr_nonneg hr_lt_one
  have hevent : ∀ᶠ m : ℕ in Filter.atTop, ((4 : ℝ) / lam) ^ m < η / 2 :=
    htend.eventually_lt_const hηhalf
  rcases Filter.eventually_atTop.1 hevent with ⟨m0, hm0⟩
  refine ⟨m0, ?_⟩
  intro μ F δ hthreshold d
  let c : ℝ := (catalan (m0 + 1) : ℝ) / lam ^ (m0 + 1)
  have hbound : c ≤ (4 : ℝ) ^ (m0 + 1) / lam ^ (m0 + 1) := by
    dsimp [c]
    exact div_le_div_of_nonneg_right (catalan_le_four_pow_real (m0 + 1))
      (pow_nonneg (le_of_lt hlam_pos) (m0 + 1))
  have hdivpow : (4 : ℝ) ^ (m0 + 1) / lam ^ (m0 + 1) =
      ((4 : ℝ) / lam) ^ (m0 + 1) := by
    rw [div_pow]
  have hcat : c < η / 2 :=
    lt_of_le_of_lt (hbound.trans_eq hdivpow) (hm0 (m0 + 1) (Nat.le_succ m0))
  have htol : c + η / 2 ≤ η := by
    have hadd : c + η / 2 < η / 2 + η / 2 := add_lt_add_left hcat (η / 2)
    have hhalf_sum : η / 2 + η / 2 = η := by ring
    exact le_of_lt (by simpa [hhalf_sum] using hadd)
  have hsubset :
      {ω : Ω |
        η < ((Finset.univ.filter fun i : ι d => F d ω i < 0).card : ℝ) /
            (Fintype.card (ι d) : ℝ) ∨
          η < (∑ i : ι d, max 0 (-(F d ω i))) /
            (Fintype.card (ι d) : ℝ)} ⊆
      {ω : Ω |
        (catalan (m0 + 1) : ℝ) / lam ^ (m0 + 1) + η / 2 <
          (∑ i : ι d, (F d ω i - 1) ^ (2 * (m0 + 1))) /
            (Fintype.card (ι d) : ℝ)} := by
    intro ω hbad
    by_contra hnot
    have hMoment :
        (∑ i : ι d, (F d ω i - 1) ^ (2 * (m0 + 1))) /
            (Fintype.card (ι d) : ℝ) ≤
          (catalan (m0 + 1) : ℝ) / lam ^ (m0 + 1) + η / 2 :=
      le_of_not_gt hnot
    have hMomentEta :
        (∑ i : ι d, (F d ω i - 1) ^ (2 * (m0 + 1))) /
            (Fintype.card (ι d) : ℝ) ≤ η := by
      exact le_trans hMoment htol
    have hcount :
        ((Finset.univ.filter fun i : ι d => F d ω i < 0).card : ℝ) /
            (Fintype.card (ι d) : ℝ) ≤ η :=
      neg_count_average_le_of_centered_even_moment_average_le
        (f := F d ω) (m0 + 1) hMomentEta
    have hmass :
        (∑ i : ι d, max 0 (-(F d ω i))) /
            (Fintype.card (ι d) : ℝ) ≤ η :=
      neg_mass_average_le_of_centered_even_moment_average_le_succ
        (f := F d ω) m0 hMomentEta
    rcases hbad with hbad | hbad
    · exact (not_lt_of_ge hcount) hbad
    · exact (not_lt_of_ge hmass) hbad
  exact le_trans (measure_mono hsubset) (hthreshold d)

/-- Dependent-index convergence form of the fixed-moment bulk adapter.

If, for the fixed moment order chosen from `λ > 4`, the centered-moment
threshold event has probability tending to zero, then the event where either
the negative eigenvalue fraction or the normalized negative trace mass exceeds
`η` also has probability tending to zero. -/
theorem exists_tendsto_bad_event_measure_zero_of_centered_moment_threshold_event_tendsto_zero_dependent
    {Ω : Type*} {ι : ℕ → Type*} [MeasurableSpace Ω] [∀ d : ℕ, Fintype (ι d)]
    {lam η : ℝ} (hlam : 4 < lam) (hη : 0 < η) :
    ∃ m : ℕ, ∀ (μ : ℕ → Measure Ω) (F : (d : ℕ) → Ω → ι d → ℝ),
      Filter.Tendsto
        (fun d : ℕ =>
          μ d {ω : Ω |
            (catalan (m + 1) : ℝ) / lam ^ (m + 1) + η / 2 <
              (∑ i : ι d, (F d ω i - 1) ^ (2 * (m + 1))) /
                (Fintype.card (ι d) : ℝ)})
        Filter.atTop (nhds 0) →
      Filter.Tendsto
        (fun d : ℕ =>
          μ d {ω : Ω |
            η < ((Finset.univ.filter fun i : ι d => F d ω i < 0).card : ℝ) /
                (Fintype.card (ι d) : ℝ) ∨
              η < (∑ i : ι d, max 0 (-(F d ω i))) /
                (Fintype.card (ι d) : ℝ)})
        Filter.atTop (nhds 0) := by
  rcases
    exists_bad_event_measure_le_of_centered_moment_threshold_event_measure_le_dependent
      (Ω := Ω) (ι := ι) hlam hη with
    ⟨m, hm⟩
  refine ⟨m, ?_⟩
  intro μ F hthreshold
  have hle :
      ∀ d : ℕ,
        μ d {ω : Ω |
          η < ((Finset.univ.filter fun i : ι d => F d ω i < 0).card : ℝ) /
              (Fintype.card (ι d) : ℝ) ∨
            η < (∑ i : ι d, max 0 (-(F d ω i))) /
              (Fintype.card (ι d) : ℝ)} ≤
        μ d {ω : Ω |
          (catalan (m + 1) : ℝ) / lam ^ (m + 1) + η / 2 <
            (∑ i : ι d, (F d ω i - 1) ^ (2 * (m + 1))) /
              (Fintype.card (ι d) : ℝ)} :=
    hm μ F (δ := fun d : ℕ =>
      μ d {ω : Ω |
        (catalan (m + 1) : ℝ) / lam ^ (m + 1) + η / 2 <
          (∑ i : ι d, (F d ω i - 1) ^ (2 * (m + 1))) /
            (Fintype.card (ι d) : ℝ)}) (fun _d => le_rfl)
  rw [ENNReal.tendsto_nhds_zero]
  intro ε' hε'
  have hthreshold_event :
      ∀ᶠ d : ℕ in Filter.atTop,
        μ d {ω : Ω |
          (catalan (m + 1) : ℝ) / lam ^ (m + 1) + η / 2 <
            (∑ i : ι d, (F d ω i - 1) ^ (2 * (m + 1))) /
              (Fintype.card (ι d) : ℝ)} ≤ ε' :=
    (ENNReal.tendsto_nhds_zero.mp hthreshold) ε' hε'
  filter_upwards [hthreshold_event] with d hd
  exact le_trans (hle d) hd

/-- Dependent-index fixed-moment concentration adapter in finite-rate deviation
form.

If a fixed-order concentration estimate bounds the probability that the
normalized centered moment deviates from its Catalan limit by more than
`η / 2`, then the same bound holds for the event where either empirical
almost-positivity control fails. -/
theorem exists_bad_event_measure_le_of_centered_moment_deviation_event_measure_le_dependent
    {Ω : Type*} {ι : ℕ → Type*} [MeasurableSpace Ω] [∀ d : ℕ, Fintype (ι d)]
    {lam η : ℝ} (hlam : 4 < lam) (hη : 0 < η) :
    ∃ m : ℕ, ∀ (μ : ℕ → Measure Ω) (F : (d : ℕ) → Ω → ι d → ℝ)
      {δ : ℕ → ℝ≥0∞},
      (∀ d : ℕ,
        μ d {ω : Ω |
          η / 2 <
            |(∑ i : ι d, (F d ω i - 1) ^ (2 * (m + 1))) /
                (Fintype.card (ι d) : ℝ) -
              (catalan (m + 1) : ℝ) / lam ^ (m + 1)|} ≤ δ d) →
      ∀ d : ℕ,
        μ d {ω : Ω |
          η < ((Finset.univ.filter fun i : ι d => F d ω i < 0).card : ℝ) /
              (Fintype.card (ι d) : ℝ) ∨
            η < (∑ i : ι d, max 0 (-(F d ω i))) /
              (Fintype.card (ι d) : ℝ)} ≤ δ d := by
  rcases
    exists_bad_event_measure_le_of_centered_moment_threshold_event_measure_le_dependent
      (Ω := Ω) (ι := ι) hlam hη with
    ⟨m, hm⟩
  refine ⟨m, ?_⟩
  intro μ F δ hdev
  refine hm μ F ?_
  intro d
  have hsubset :
      {ω : Ω |
        (catalan (m + 1) : ℝ) / lam ^ (m + 1) + η / 2 <
          (∑ i : ι d, (F d ω i - 1) ^ (2 * (m + 1))) /
            (Fintype.card (ι d) : ℝ)} ⊆
      {ω : Ω |
        η / 2 <
          |(∑ i : ι d, (F d ω i - 1) ^ (2 * (m + 1))) /
              (Fintype.card (ι d) : ℝ) -
            (catalan (m + 1) : ℝ) / lam ^ (m + 1)|} := by
    intro ω hω
    have hω' :
        (catalan (m + 1) : ℝ) / lam ^ (m + 1) + η / 2 <
          (∑ i : ι d, (F d ω i - 1) ^ (2 * (m + 1))) /
            (Fintype.card (ι d) : ℝ) := hω
    have hdiff :
        η / 2 <
          (∑ i : ι d, (F d ω i - 1) ^ (2 * (m + 1))) /
              (Fintype.card (ι d) : ℝ) -
            (catalan (m + 1) : ℝ) / lam ^ (m + 1) := by
      linarith
    exact lt_of_lt_of_le hdiff (le_abs_self _)
  exact le_trans (measure_mono hsubset) (hdev d)

/-- Dependent-index fixed-moment concentration adapter in deviation form.

Fixed-order concentration inputs are often stated as convergence in probability
of the normalized centered moment to its Catalan limit.  This wrapper converts
that natural deviation event into the combined almost-positivity bad event:
excessive negative eigenvalue fraction or excessive normalized negative trace
mass. -/
theorem exists_tendsto_bad_event_measure_zero_of_centered_moment_deviation_event_tendsto_zero_dependent
    {Ω : Type*} {ι : ℕ → Type*} [MeasurableSpace Ω] [∀ d : ℕ, Fintype (ι d)]
    {lam η : ℝ} (hlam : 4 < lam) (hη : 0 < η) :
    ∃ m : ℕ, ∀ (μ : ℕ → Measure Ω) (F : (d : ℕ) → Ω → ι d → ℝ),
      Filter.Tendsto
        (fun d : ℕ =>
          μ d {ω : Ω |
            η / 2 <
              |(∑ i : ι d, (F d ω i - 1) ^ (2 * (m + 1))) /
                  (Fintype.card (ι d) : ℝ) -
                (catalan (m + 1) : ℝ) / lam ^ (m + 1)|})
        Filter.atTop (nhds 0) →
      Filter.Tendsto
        (fun d : ℕ =>
          μ d {ω : Ω |
            η < ((Finset.univ.filter fun i : ι d => F d ω i < 0).card : ℝ) /
                (Fintype.card (ι d) : ℝ) ∨
              η < (∑ i : ι d, max 0 (-(F d ω i))) /
                (Fintype.card (ι d) : ℝ)})
        Filter.atTop (nhds 0) := by
  rcases
    exists_bad_event_measure_le_of_centered_moment_deviation_event_measure_le_dependent
      (Ω := Ω) (ι := ι) hlam hη with
    ⟨m, hm⟩
  refine ⟨m, ?_⟩
  intro μ F hdev
  have hle :
      ∀ d : ℕ,
        μ d {ω : Ω |
          η < ((Finset.univ.filter fun i : ι d => F d ω i < 0).card : ℝ) /
              (Fintype.card (ι d) : ℝ) ∨
            η < (∑ i : ι d, max 0 (-(F d ω i))) /
              (Fintype.card (ι d) : ℝ)} ≤
        μ d {ω : Ω |
          η / 2 <
            |(∑ i : ι d, (F d ω i - 1) ^ (2 * (m + 1))) /
                (Fintype.card (ι d) : ℝ) -
              (catalan (m + 1) : ℝ) / lam ^ (m + 1)|} :=
    hm μ F (δ := fun d : ℕ =>
      μ d {ω : Ω |
        η / 2 <
          |(∑ i : ι d, (F d ω i - 1) ^ (2 * (m + 1))) /
              (Fintype.card (ι d) : ℝ) -
            (catalan (m + 1) : ℝ) / lam ^ (m + 1)|}) (fun _d => le_rfl)
  rw [ENNReal.tendsto_nhds_zero]
  intro ε' hε'
  have hdev_event :
      ∀ᶠ d : ℕ in Filter.atTop,
        μ d {ω : Ω |
          η / 2 <
            |(∑ i : ι d, (F d ω i - 1) ^ (2 * (m + 1))) /
                (Fintype.card (ι d) : ℝ) -
              (catalan (m + 1) : ℝ) / lam ^ (m + 1)|} ≤ ε' :=
    (ENNReal.tendsto_nhds_zero.mp hdev) ε' hε'
  filter_upwards [hdev_event] with d hd
  exact le_trans (hle d) hd

/-- Deterministic edge bridge: if an unnormalised even centered spectral moment
is strictly below `1`, then no spectral value is negative.

This is the Lean version of the high-moment shortcut used for the `λ > 4`
PPT side: a negative eigenvalue `y < 0` would contribute at least `1` to
`∑ i, (y_i - 1)^(2m)`. -/
theorem all_nonneg_of_centered_even_moment_lt_one {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (m : ℕ)
    (hMoment : (∑ i : ι, (f i - 1) ^ (2 * m)) < 1) :
    ∀ i : ι, 0 ≤ f i := by
  classical
  intro i
  by_contra hnonneg
  have hneg : f i < 0 := lt_of_not_ge hnonneg
  let s : Finset ι := Finset.univ.filter fun j : ι => f j < 0
  have hi : i ∈ s := by
    simp [s, hneg]
  have hcard_pos : 0 < s.card := Finset.card_pos.mpr ⟨i, hi⟩
  have hcard_one_nat : 1 ≤ s.card := Nat.succ_le_of_lt hcard_pos
  have hcard_one : (1 : ℝ) ≤ (s.card : ℝ) := by
    exact_mod_cast hcard_one_nat
  have hcount := neg_count_le_centered_even_moment (f := f) m
  have hone : (1 : ℝ) ≤ ∑ i : ι, (f i - 1) ^ (2 * m) :=
    le_trans hcard_one hcount
  linarith

/-- Set-valued high-moment positivity bridge.

For any random finite spectrum `F`, the event that some spectral value is
negative is contained in the event that the unnormalised centered even moment is
at least `1`.  A Markov bound for the right-hand event is therefore enough to
prove PPT with high probability. -/
theorem exists_negative_subset_centered_even_moment_ge_one_event
    {Ω ι : Type*} [Fintype ι] (F : Ω → ι → ℝ) (m : ℕ) :
    {ω : Ω | ∃ i : ι, F ω i < 0} ⊆
      {ω : Ω | (1 : ℝ) ≤ ∑ i : ι, (F ω i - 1) ^ (2 * m)} := by
  intro ω hω
  by_contra hnot
  have hMoment : (∑ i : ι, (F ω i - 1) ^ (2 * m)) < 1 := lt_of_not_ge hnot
  have hnonneg := all_nonneg_of_centered_even_moment_lt_one (f := F ω) m hMoment
  rcases hω with ⟨i, hi⟩
  exact (not_lt_of_ge (hnonneg i)) hi

/-- Measure-facing high-moment positivity bridge.

Once the unnormalised centered even-moment event has measure at most `δ`, the
event that some spectral value is negative has measure at most `δ`.  This is the
abstract probability wrapper sitting between the deterministic event inclusion
and a later Markov/growing-moment estimate. -/
theorem negative_event_measure_le_of_centered_event_measure_le
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (F : Ω → ι → ℝ) (m : ℕ) {δ : ℝ≥0∞}
    (hBound :
      μ {ω : Ω | (1 : ℝ) ≤ ∑ i : ι, (F ω i - 1) ^ (2 * m)} ≤ δ) :
    μ {ω : Ω | ∃ i : ι, F ω i < 0} ≤ δ := by
  exact le_trans (measure_mono (exists_negative_subset_centered_even_moment_ge_one_event F m))
    hBound

/-- Markov-facing high-moment positivity bridge.

The measure of the negative-spectrum event is bounded by the `lintegral` of the
unnormalised centered even spectral moment.  This is still abstract in the
random finite spectrum `F`; the genuine random-matrix work is to bound the
right-hand side at a growing order. -/
theorem negative_event_measure_le_lintegral_centered_even_moment
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (F : Ω → ι → ℝ) (m : ℕ)
    (hMeas : AEMeasurable
      (fun ω : Ω => ENNReal.ofReal (∑ i : ι, (F ω i - 1) ^ (2 * m))) μ) :
    μ {ω : Ω | ∃ i : ι, F ω i < 0} ≤
      ∫⁻ ω, ENNReal.ofReal (∑ i : ι, (F ω i - 1) ^ (2 * m)) ∂μ := by
  apply meas_le_lintegral₀ hMeas
  intro ω hω
  have hreal : (1 : ℝ) ≤ ∑ i : ι, (F ω i - 1) ^ (2 * m) :=
    exists_negative_subset_centered_even_moment_ge_one_event F m hω
  exact ENNReal.one_le_ofReal.mpr hreal

/-- Direct expectation-bound form of the high-moment PPT bridge.

If a growing-moment supplier bounds the `lintegral` of the unnormalised centered
even spectral moment by `δ`, then the negative-spectrum event has measure at
most `δ`. -/
theorem negative_event_measure_le_of_lintegral_centered_even_moment_le
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (F : Ω → ι → ℝ) (m : ℕ) {δ : ℝ≥0∞}
    (hMeas : AEMeasurable
      (fun ω : Ω => ENNReal.ofReal (∑ i : ι, (F ω i - 1) ^ (2 * m))) μ)
    (hBound :
      (∫⁻ ω, ENNReal.ofReal (∑ i : ι, (F ω i - 1) ^ (2 * m)) ∂μ) ≤ δ) :
    μ {ω : Ω | ∃ i : ι, F ω i < 0} ≤ δ :=
  le_trans (negative_event_measure_le_lintegral_centered_even_moment μ F m hMeas) hBound

/-- Real-valued finite-dimensional expectation-bound form of the high-moment
PPT bridge.

If the lifted centered-moment `lintegral` is bounded by `ofReal δ`, then the
negative-spectrum event is bounded by the same explicit finite-dimensional
rate. -/
theorem negative_event_measure_le_of_lintegral_bound_ofReal
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (F : Ω → ι → ℝ) (m : ℕ) (δ : ℝ)
    (hMeas : AEMeasurable
      (fun ω : Ω => ENNReal.ofReal (∑ i : ι, (F ω i - 1) ^ (2 * m))) μ)
    (hBound :
      (∫⁻ ω, ENNReal.ofReal (∑ i : ι, (F ω i - 1) ^ (2 * m)) ∂μ) ≤
        ENNReal.ofReal δ) :
    μ {ω : Ω | ∃ i : ι, F ω i < 0} ≤ ENNReal.ofReal δ :=
  negative_event_measure_le_of_lintegral_centered_even_moment_le μ F m hMeas hBound

/-- Coordinate a.e. measurability is enough for the centered even-moment
integrand.

This removes a broad measurability hypothesis from later upper adapters: for a
finite spectrum, Lean can build the measurability of the whole centered-moment
sum from the coordinate functions. -/
theorem centered_even_moment_lintegrand_aemeasurable_of_coordinate
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (F : Ω → ι → ℝ) (m : ℕ)
    (hF : ∀ i : ι, AEMeasurable (fun ω : Ω => F ω i) μ) :
    AEMeasurable
      (fun ω : Ω => ENNReal.ofReal (∑ i : ι, (F ω i - 1) ^ (2 * m))) μ := by
  apply AEMeasurable.ennreal_ofReal
  have hsum :
      AEMeasurable (∑ i : ι, fun ω : Ω => (F ω i - 1) ^ (2 * m)) μ := by
    refine Finset.aemeasurable_sum Finset.univ ?_
    intro i _hi
    exact (hF i).sub_const 1 |>.pow_const (2 * m)
  convert hsum using 1
  ext ω
  simp

/-- Eventual finite-dimensional expectation-bound form of the high-moment PPT
bridge.

If the lifted centered-moment `lintegral` is eventually bounded by
`ofReal (δ d)`, then the negative-spectrum event is eventually bounded by the
same explicit rate. -/
theorem eventually_negative_event_measure_le_of_eventually_lintegral_bound_ofReal
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : ℕ → Measure Ω) (F : ℕ → Ω → ι → ℝ) (m : ℕ → ℕ)
    (δ : ℕ → ℝ)
    (hMeas : ∀ d : ℕ, AEMeasurable
      (fun ω : Ω => ENNReal.ofReal (∑ i : ι, (F d ω i - 1) ^ (2 * m d))) (μ d))
    (hBound : ∀ᶠ d : ℕ in Filter.atTop,
      (∫⁻ ω, ENNReal.ofReal (∑ i : ι, (F d ω i - 1) ^ (2 * m d)) ∂(μ d)) ≤
        ENNReal.ofReal (δ d)) :
    ∀ᶠ d : ℕ in Filter.atTop,
      μ d {ω : Ω | ∃ i : ι, F d ω i < 0} ≤ ENNReal.ofReal (δ d) := by
  filter_upwards [hBound] with d hd
  exact negative_event_measure_le_of_lintegral_bound_ofReal
    (μ d) (F d) (m d) (δ d) (hMeas d) hd

/-- Explicit paper-shape finite-dimensional probability bound.

This is the quantitative speed statement behind the controlled growing-moment
route: if the unnormalised centered moment is bounded by
`C (log d)^α d^2 q^(c log d)`, then the negative-spectrum event has probability
at most that same rate. -/
theorem negative_event_measure_le_of_lintegral_bound_log_quadratic_rpow_log
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : ℕ → Measure Ω) (F : ℕ → Ω → ι → ℝ) (m : ℕ → ℕ)
    (d : ℕ) (C α q c : ℝ)
    (hMeas : ∀ d : ℕ, AEMeasurable
      (fun ω : Ω => ENNReal.ofReal (∑ i : ι, (F d ω i - 1) ^ (2 * m d))) (μ d))
    (hBound : ∀ d : ℕ,
      (∫⁻ ω, ENNReal.ofReal (∑ i : ι, (F d ω i - 1) ^ (2 * m d)) ∂(μ d)) ≤
        ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
          ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))) :
    μ d {ω : Ω | ∃ i : ι, F d ω i < 0} ≤
      ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
        ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ))))) :=
  negative_event_measure_le_of_lintegral_bound_ofReal (μ d) (F d) (m d)
    (C * ((Real.log (d : ℝ)) ^ α *
      ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))
    (hMeas d) (hBound d)

/-- Eventual paper-shape finite-dimensional probability bound.

This is the finite-rate version used by asymptotic random-matrix suppliers:
if the paper-shape centered-moment estimate holds eventually, then the
non-PPT event has the same paper-shape bound eventually. -/
theorem eventually_negative_event_measure_le_of_eventually_lintegral_bound_log_quadratic_rpow_log
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : ℕ → Measure Ω) (F : ℕ → Ω → ι → ℝ) (m : ℕ → ℕ)
    (C α q c : ℝ)
    (hMeas : ∀ d : ℕ, AEMeasurable
      (fun ω : Ω => ENNReal.ofReal (∑ i : ι, (F d ω i - 1) ^ (2 * m d))) (μ d))
    (hBound : ∀ᶠ d : ℕ in Filter.atTop,
      (∫⁻ ω, ENNReal.ofReal (∑ i : ι, (F d ω i - 1) ^ (2 * m d)) ∂(μ d)) ≤
        ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
          ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))) :
    ∀ᶠ d : ℕ in Filter.atTop,
      μ d {ω : Ω | ∃ i : ι, F d ω i < 0} ≤
        ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
          ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ))))) := by
  exact eventually_negative_event_measure_le_of_eventually_lintegral_bound_ofReal
    μ F m
    (fun d : ℕ => C * ((Real.log (d : ℝ)) ^ α *
      ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))
    hMeas hBound

/-- Dependent-index version of the eventual paper-shape finite-dimensional
probability bound.

This removes an adapter mismatch for concrete matrix models, whose spectral
index type usually depends on the dimension parameter. -/
theorem eventually_negative_event_measure_le_of_eventually_lintegral_bound_log_quadratic_rpow_log_dependent
    {Ω : Type*} {ι : ℕ → Type*} [MeasurableSpace Ω] [∀ d : ℕ, Fintype (ι d)]
    (μ : ℕ → Measure Ω) (F : (d : ℕ) → Ω → ι d → ℝ) (m : ℕ → ℕ)
    (C α q c : ℝ)
    (hMeas : ∀ d : ℕ, AEMeasurable
      (fun ω : Ω => ENNReal.ofReal (∑ i : ι d, (F d ω i - 1) ^ (2 * m d))) (μ d))
    (hBound : ∀ᶠ d : ℕ in Filter.atTop,
      (∫⁻ ω, ENNReal.ofReal (∑ i : ι d, (F d ω i - 1) ^ (2 * m d)) ∂(μ d)) ≤
        ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
          ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))) :
    ∀ᶠ d : ℕ in Filter.atTop,
      μ d {ω : Ω | ∃ i : ι d, F d ω i < 0} ≤
        ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
          ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ))))) := by
  filter_upwards [hBound] with d hd
  exact negative_event_measure_le_of_lintegral_bound_ofReal
    (μ d) (F d) (m d)
    (C * ((Real.log (d : ℝ)) ^ α *
      ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))
    (hMeas d) hd

/-- Asymptotic expectation-bound form of the high-moment PPT bridge.

If the growing centered-moment supplier gives a sequence of `lintegral` bounds
`δ d → 0`, then the negative-spectrum event has probability tending to zero.
This is the precise abstract meaning of the controlled growing-moment endpoint;
the remaining random-matrix work is to prove such a bound for the concrete
partial-transpose model. -/
theorem tendsto_negative_event_measure_zero_of_lintegral_bound
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : ℕ → Measure Ω) (F : ℕ → Ω → ι → ℝ) (m : ℕ → ℕ)
    (δ : ℕ → ℝ≥0∞)
    (hMeas : ∀ d : ℕ, AEMeasurable
      (fun ω : Ω => ENNReal.ofReal (∑ i : ι, (F d ω i - 1) ^ (2 * m d))) (μ d))
    (hBound : ∀ d : ℕ,
      (∫⁻ ω, ENNReal.ofReal (∑ i : ι, (F d ω i - 1) ^ (2 * m d)) ∂(μ d)) ≤ δ d)
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun d : ℕ => μ d {ω : Ω | ∃ i : ι, F d ω i < 0})
      Filter.atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hδevent : ∀ᶠ d : ℕ in Filter.atTop, δ d ≤ ε :=
    (ENNReal.tendsto_nhds_zero.mp hδ) ε hε
  exact hδevent.mono (fun d hd =>
    le_trans
      (negative_event_measure_le_of_lintegral_centered_even_moment_le
        (μ d) (F d) (m d) (hMeas d) (hBound d)) hd)

/-- Real-valued asymptotic expectation-bound form of the high-moment PPT bridge.

Many paper estimates bound the centered-moment `lintegral` by `ofReal (δ d)`,
where `δ d` is an ordinary real scalar rate.  If that real rate tends to zero,
then the negative-spectrum event probabilities tend to zero. -/
theorem tendsto_negative_event_measure_zero_of_lintegral_bound_ofReal
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : ℕ → Measure Ω) (F : ℕ → Ω → ι → ℝ) (m : ℕ → ℕ)
    (δ : ℕ → ℝ)
    (hMeas : ∀ d : ℕ, AEMeasurable
      (fun ω : Ω => ENNReal.ofReal (∑ i : ι, (F d ω i - 1) ^ (2 * m d))) (μ d))
    (hBound : ∀ d : ℕ,
      (∫⁻ ω, ENNReal.ofReal (∑ i : ι, (F d ω i - 1) ^ (2 * m d)) ∂(μ d)) ≤
        ENNReal.ofReal (δ d))
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun d : ℕ => μ d {ω : Ω | ∃ i : ι, F d ω i < 0})
      Filter.atTop (nhds 0) := by
  refine tendsto_negative_event_measure_zero_of_lintegral_bound μ F m
    (fun d : ℕ => ENNReal.ofReal (δ d)) hMeas hBound ?_
  simpa using ENNReal.tendsto_ofReal hδ

/-- Eventual real-valued expectation-bound form of the high-moment PPT bridge.

This is the asymptotic form most convenient for random-matrix suppliers: it is
enough to prove the centered-moment `lintegral` bound for all sufficiently
large dimensions. -/
theorem tendsto_negative_event_measure_zero_of_eventually_lintegral_bound_ofReal
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : ℕ → Measure Ω) (F : ℕ → Ω → ι → ℝ) (m : ℕ → ℕ)
    (δ : ℕ → ℝ)
    (hMeas : ∀ d : ℕ, AEMeasurable
      (fun ω : Ω => ENNReal.ofReal (∑ i : ι, (F d ω i - 1) ^ (2 * m d))) (μ d))
    (hBound : ∀ᶠ d : ℕ in Filter.atTop,
      (∫⁻ ω, ENNReal.ofReal (∑ i : ι, (F d ω i - 1) ^ (2 * m d)) ∂(μ d)) ≤
        ENNReal.ofReal (δ d))
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun d : ℕ => μ d {ω : Ω | ∃ i : ι, F d ω i < 0})
      Filter.atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hδenn : Filter.Tendsto (fun d : ℕ => ENNReal.ofReal (δ d))
      Filter.atTop (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal hδ
  have hδevent : ∀ᶠ d : ℕ in Filter.atTop, ENNReal.ofReal (δ d) ≤ ε :=
    (ENNReal.tendsto_nhds_zero.mp hδenn) ε hε
  filter_upwards [hBound, hδevent] with d hdBound hdδ
  exact le_trans
    (negative_event_measure_le_of_lintegral_bound_ofReal
      (μ d) (F d) (m d) (δ d) (hMeas d) hdBound) hdδ

/-- Dependent-index asymptotic expectation-bound form of the high-moment PPT
bridge.

This is the concrete matrix-model shape: the spectral index type may depend on
the dimension `d`.  An eventual real-valued `lintegral` bound with rate
`δ d → 0` still forces the non-PPT event probabilities to tend to zero. -/
theorem tendsto_negative_event_measure_zero_of_eventually_lintegral_bound_ofReal_dependent
    {Ω : Type*} {ι : ℕ → Type*} [MeasurableSpace Ω] [∀ d : ℕ, Fintype (ι d)]
    (μ : ℕ → Measure Ω) (F : (d : ℕ) → Ω → ι d → ℝ) (m : ℕ → ℕ)
    (δ : ℕ → ℝ)
    (hMeas : ∀ d : ℕ, AEMeasurable
      (fun ω : Ω => ENNReal.ofReal (∑ i : ι d, (F d ω i - 1) ^ (2 * m d))) (μ d))
    (hBound : ∀ᶠ d : ℕ in Filter.atTop,
      (∫⁻ ω, ENNReal.ofReal (∑ i : ι d, (F d ω i - 1) ^ (2 * m d)) ∂(μ d)) ≤
        ENNReal.ofReal (δ d))
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun d : ℕ => μ d {ω : Ω | ∃ i : ι d, F d ω i < 0})
      Filter.atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hδenn : Filter.Tendsto (fun d : ℕ => ENNReal.ofReal (δ d))
      Filter.atTop (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal hδ
  have hδevent : ∀ᶠ d : ℕ in Filter.atTop, ENNReal.ofReal (δ d) ≤ ε :=
    (ENNReal.tendsto_nhds_zero.mp hδenn) ε hε
  filter_upwards [hBound, hδevent] with d hdBound hdδ
  exact le_trans
    (negative_event_measure_le_of_lintegral_bound_ofReal
      (μ d) (F d) (m d) (δ d) (hMeas d) hdBound) hdδ

/-- Negative powers of the dimension parameter tend to zero. -/
theorem natCast_rpow_tendsto_zero_of_neg {e : ℝ} (he : e < 0) :
    Filter.Tendsto (fun d : ℕ => (d : ℝ) ^ e) Filter.atTop (nhds 0) := by
  have hneg : 0 < -e := by linarith
  refine ((tendsto_rpow_neg_atTop hneg).comp tendsto_natCast_atTop_atTop).congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with d _hd
  simp only [Function.comp_apply, neg_neg]

/-- A constant times a negative power of the dimension parameter tends to zero. -/
theorem const_mul_natCast_rpow_tendsto_zero_of_neg (C : ℝ) {e : ℝ} (he : e < 0) :
    Filter.Tendsto (fun d : ℕ => C * (d : ℝ) ^ e) Filter.atTop (nhds 0) := by
  simpa [mul_zero] using (natCast_rpow_tendsto_zero_of_neg he).const_mul C

/-- Polynomial-rate expectation-bound form of the high-moment PPT bridge.

If the lifted centered-moment `lintegral` is bounded by a real polynomial
decay rate `C * d^{-β}` with `β > 0`, then the negative-spectrum event
probabilities tend to zero. -/
theorem tendsto_negative_event_measure_zero_of_lintegral_bound_const_mul_rpow_neg
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : ℕ → Measure Ω) (F : ℕ → Ω → ι → ℝ) (m : ℕ → ℕ)
    (C β : ℝ) (hβ : 0 < β)
    (hMeas : ∀ d : ℕ, AEMeasurable
      (fun ω : Ω => ENNReal.ofReal (∑ i : ι, (F d ω i - 1) ^ (2 * m d))) (μ d))
    (hBound : ∀ d : ℕ,
      (∫⁻ ω, ENNReal.ofReal (∑ i : ι, (F d ω i - 1) ^ (2 * m d)) ∂(μ d)) ≤
        ENNReal.ofReal (C * (d : ℝ) ^ (-β))) :
    Filter.Tendsto (fun d : ℕ => μ d {ω : Ω | ∃ i : ι, F d ω i < 0})
      Filter.atTop (nhds 0) := by
  refine tendsto_negative_event_measure_zero_of_lintegral_bound_ofReal μ F m
    (fun d : ℕ => C * (d : ℝ) ^ (-β)) hMeas hBound ?_
  exact const_mul_natCast_rpow_tendsto_zero_of_neg C (by linarith)

/-- Dependent-index polynomial-rate expectation-bound form of the high-moment
PPT bridge. -/
theorem tendsto_negative_event_measure_zero_of_lintegral_bound_const_mul_rpow_neg_dependent
    {Ω : Type*} {ι : ℕ → Type*} [MeasurableSpace Ω] [∀ d : ℕ, Fintype (ι d)]
    (μ : ℕ → Measure Ω) (F : (d : ℕ) → Ω → ι d → ℝ) (m : ℕ → ℕ)
    (C β : ℝ) (hβ : 0 < β)
    (hMeas : ∀ d : ℕ, AEMeasurable
      (fun ω : Ω => ENNReal.ofReal (∑ i : ι d, (F d ω i - 1) ^ (2 * m d))) (μ d))
    (hBound : ∀ d : ℕ,
      (∫⁻ ω, ENNReal.ofReal (∑ i : ι d, (F d ω i - 1) ^ (2 * m d)) ∂(μ d)) ≤
        ENNReal.ofReal (C * (d : ℝ) ^ (-β))) :
    Filter.Tendsto (fun d : ℕ => μ d {ω : Ω | ∃ i : ι d, F d ω i < 0})
      Filter.atTop (nhds 0) := by
  refine
    tendsto_negative_event_measure_zero_of_eventually_lintegral_bound_ofReal_dependent
      μ F m (fun d : ℕ => C * (d : ℝ) ^ (-β)) hMeas
      (Filter.Eventually.of_forall hBound) ?_
  exact const_mul_natCast_rpow_tendsto_zero_of_neg C (by linarith)

/-- Scalar logarithmic conversion behind the growing-moment rate:
`q^(c log x)` is the same as `x^(c log q)` for positive `q` and `x`. -/
theorem rpow_const_mul_log_eq_rpow_log_mul {q x c : ℝ} (hq : 0 < q) (hx : 0 < x) :
    q ^ (c * Real.log x) = x ^ (c * Real.log q) := by
  rw [Real.rpow_def_of_pos hq, Real.rpow_def_of_pos hx]
  congr 1
  ring

/-- The main scalar part of the logarithmic high-moment envelope:
`x^2 * q^(c log x)` is exactly `x^(2 + c log q)`. -/
theorem quadratic_rpow_const_mul_log_eq_rpow {q x c : ℝ} (hq : 0 < q) (hx : 0 < x) :
    x ^ 2 * q ^ (c * Real.log x) = x ^ (2 + c * Real.log q) := by
  rw [rpow_const_mul_log_eq_rpow_log_mul hq hx]
  rw [show x ^ 2 = x ^ (2 : ℝ) by norm_num [Real.rpow_natCast]]
  rw [Real.rpow_add hx]

/-- A logarithmic power is absorbed by any positive polynomial decay. -/
theorem log_rpow_mul_natCast_rpow_neg_tendsto_zero
    (α β : ℝ) (hβ : 0 < β) :
    Filter.Tendsto (fun d : ℕ => (Real.log (d : ℝ)) ^ α * (d : ℝ) ^ (-β))
      Filter.atTop (nhds 0) := by
  have hhalf : 0 < β / 2 := by linarith
  have hLittleR : (fun x : ℝ => Real.log x ^ α) =o[Filter.atTop]
      (fun x : ℝ => x ^ (β / 2)) :=
    isLittleO_log_rpow_rpow_atTop α hhalf
  have hLittleNat : (fun d : ℕ => Real.log (d : ℝ) ^ α) =o[Filter.atTop]
      (fun d : ℕ => (d : ℝ) ^ (β / 2)) := by
    simpa [Function.comp_def] using hLittleR.comp_tendsto
      (tendsto_natCast_atTop_atTop :
        Filter.Tendsto (fun d : ℕ => (d : ℝ)) Filter.atTop Filter.atTop)
  have hmul : (fun d : ℕ => Real.log (d : ℝ) ^ α * (d : ℝ) ^ (-β)) =o[Filter.atTop]
      (fun d : ℕ => (d : ℝ) ^ (β / 2) * (d : ℝ) ^ (-β)) :=
    hLittleNat.mul_isBigO
      (Asymptotics.isBigO_refl (fun d : ℕ => (d : ℝ) ^ (-β)) Filter.atTop)
  have hright : Filter.Tendsto
      (fun d : ℕ => (d : ℝ) ^ (β / 2) * (d : ℝ) ^ (-β)) Filter.atTop (nhds 0) := by
    refine (natCast_rpow_tendsto_zero_of_neg (e := -(β / 2)) (by linarith)).congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with d hd
    have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
    rw [← Real.rpow_add hdpos]
    congr 1
    ring
  exact hmul.trans_tendsto hright

/-- A constant times a logarithmic power is still absorbed by any positive
polynomial decay. -/
theorem const_mul_log_rpow_mul_natCast_rpow_neg_tendsto_zero
    (C α β : ℝ) (hβ : 0 < β) :
    Filter.Tendsto
      (fun d : ℕ => C * ((Real.log (d : ℝ)) ^ α * (d : ℝ) ^ (-β)))
      Filter.atTop (nhds 0) := by
  simpa [mul_zero] using
    (log_rpow_mul_natCast_rpow_neg_tendsto_zero α β hβ).const_mul C

/-- Log-polynomial-rate expectation-bound form of the high-moment PPT bridge.

If the lifted centered-moment `lintegral` is bounded by
`C * (log d)^α * d^{-β}` with `β > 0`, then the negative-spectrum event
probabilities tend to zero. -/
theorem tendsto_negative_event_measure_zero_of_lintegral_bound_log_rpow_mul_rpow_neg
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : ℕ → Measure Ω) (F : ℕ → Ω → ι → ℝ) (m : ℕ → ℕ)
    (C α β : ℝ) (hβ : 0 < β)
    (hMeas : ∀ d : ℕ, AEMeasurable
      (fun ω : Ω => ENNReal.ofReal (∑ i : ι, (F d ω i - 1) ^ (2 * m d))) (μ d))
    (hBound : ∀ d : ℕ,
      (∫⁻ ω, ENNReal.ofReal (∑ i : ι, (F d ω i - 1) ^ (2 * m d)) ∂(μ d)) ≤
        ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α * (d : ℝ) ^ (-β)))) :
    Filter.Tendsto (fun d : ℕ => μ d {ω : Ω | ∃ i : ι, F d ω i < 0})
      Filter.atTop (nhds 0) := by
  refine tendsto_negative_event_measure_zero_of_lintegral_bound_ofReal μ F m
    (fun d : ℕ => C * ((Real.log (d : ℝ)) ^ α * (d : ℝ) ^ (-β))) hMeas hBound ?_
  exact const_mul_log_rpow_mul_natCast_rpow_neg_tendsto_zero C α β hβ

/-- Dependent-index log-polynomial-rate expectation-bound form of the
high-moment PPT bridge. -/
theorem tendsto_negative_event_measure_zero_of_lintegral_bound_log_rpow_mul_rpow_neg_dependent
    {Ω : Type*} {ι : ℕ → Type*} [MeasurableSpace Ω] [∀ d : ℕ, Fintype (ι d)]
    (μ : ℕ → Measure Ω) (F : (d : ℕ) → Ω → ι d → ℝ) (m : ℕ → ℕ)
    (C α β : ℝ) (hβ : 0 < β)
    (hMeas : ∀ d : ℕ, AEMeasurable
      (fun ω : Ω => ENNReal.ofReal (∑ i : ι d, (F d ω i - 1) ^ (2 * m d))) (μ d))
    (hBound : ∀ d : ℕ,
      (∫⁻ ω, ENNReal.ofReal (∑ i : ι d, (F d ω i - 1) ^ (2 * m d)) ∂(μ d)) ≤
        ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α * (d : ℝ) ^ (-β)))) :
    Filter.Tendsto (fun d : ℕ => μ d {ω : Ω | ∃ i : ι d, F d ω i < 0})
      Filter.atTop (nhds 0) := by
  refine
    tendsto_negative_event_measure_zero_of_eventually_lintegral_bound_ofReal_dependent
      μ F m
      (fun d : ℕ => C * ((Real.log (d : ℝ)) ^ α * (d : ℝ) ^ (-β)))
      hMeas (Filter.Eventually.of_forall hBound) ?_
  exact const_mul_log_rpow_mul_natCast_rpow_neg_tendsto_zero C α β hβ

/-- Paper-shape scalar high-moment envelope.

If `q^(c log d)` beats the ambient `d^2` factor, then even an extra
logarithmic power and a constant still tend to zero. -/
theorem const_mul_log_rpow_mul_quadratic_rpow_const_mul_log_tendsto_zero
    (C α q c : ℝ) (hq : 0 < q) (hgap : 2 + c * Real.log q < 0) :
    Filter.Tendsto
      (fun d : ℕ => C * ((Real.log (d : ℝ)) ^ α *
        ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))
      Filter.atTop (nhds 0) := by
  have hβ : 0 < -(2 + c * Real.log q) := by linarith
  refine (const_mul_log_rpow_mul_natCast_rpow_neg_tendsto_zero
    C α (-(2 + c * Real.log q)) hβ).congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with d hd
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
  rw [quadratic_rpow_const_mul_log_eq_rpow hq hdpos]
  congr 2
  ring_nf

/-- Logarithmic-order threshold in the positive form used on paper:
`c log(1/q) > 2` is exactly the scalar condition that makes
`d^2 q^(c log d)` decay. -/
theorem two_add_mul_log_neg_of_two_lt_mul_log_inv {q c : ℝ}
    (hc : 2 < c * Real.log q⁻¹) :
    2 + c * Real.log q < 0 := by
  rw [Real.log_inv] at hc
  linarith

/-- For every `0 < q < 1`, some logarithmic moment order constant `c` makes
`d^2 q^(c log d)` decay. -/
theorem exists_two_lt_mul_log_inv_of_pos_lt_one {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ c : ℝ, 0 < c ∧ 2 < c * Real.log q⁻¹ := by
  have hinv : 1 < q⁻¹ := (one_lt_inv₀ hq0).2 hq1
  have hlog : 0 < Real.log q⁻¹ := Real.log_pos hinv
  refine ⟨3 / Real.log q⁻¹, ?_, ?_⟩
  · exact div_pos (by norm_num) hlog
  · calc
      (2 : ℝ) < 3 := by norm_num
      _ = (3 / Real.log q⁻¹) * Real.log q⁻¹ := by
        rw [div_mul_cancel₀]
        exact hlog.ne'

/-- For every `λ > 4`, one can choose an edge slack `eps`, a ratio
`q = (4 + eps) / λ`, and a positive logarithmic order constant `c` so that
the paper-shape rate `d^2 q^(c log d)` decays. -/
theorem exists_log_order_constants_of_four_lt {lam : ℝ} (hlam : 4 < lam) :
    ∃ eps q c : ℝ,
      0 < eps ∧ q = (4 + eps) / lam ∧ 0 < q ∧ q < 1 ∧
        0 < c ∧ 2 < c * Real.log q⁻¹ := by
  let eps : ℝ := (lam - 4) / 2
  have heps_pos : 0 < eps := by
    dsimp [eps]
    linarith
  have hfour_eps_lt : 4 + eps < lam := by
    dsimp [eps]
    linarith
  have hlam_pos : 0 < lam := by linarith
  let q : ℝ := (4 + eps) / lam
  have hnum_pos : 0 < 4 + eps := by linarith
  have hq_pos : 0 < q := by
    dsimp [q]
    exact div_pos hnum_pos hlam_pos
  have hq_lt_one : q < 1 := by
    dsimp [q]
    rw [div_lt_iff₀ hlam_pos]
    linarith
  rcases exists_two_lt_mul_log_inv_of_pos_lt_one hq_pos hq_lt_one with ⟨c, hc_pos, hc⟩
  exact ⟨eps, q, c, heps_pos, rfl, hq_pos, hq_lt_one, hc_pos, hc⟩

/-- Paper-shape scalar high-moment envelope with the readable threshold
`c log(1/q) > 2`. -/
theorem const_mul_log_rpow_mul_quadratic_rpow_const_mul_log_tendsto_zero_of_two_lt_mul_log_inv
    (C α q c : ℝ) (hq : 0 < q) (hc : 2 < c * Real.log q⁻¹) :
    Filter.Tendsto
      (fun d : ℕ => C * ((Real.log (d : ℝ)) ^ α *
        ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))
      Filter.atTop (nhds 0) :=
  const_mul_log_rpow_mul_quadratic_rpow_const_mul_log_tendsto_zero
    C α q c hq (two_add_mul_log_neg_of_two_lt_mul_log_inv hc)

/-- Paper-shape expectation-bound form of the high-moment PPT bridge.

This is the scalar wrapper for a future growing-moment estimate of the form
`C (log d)^α d^2 q^(c log d)`, with `2 + c log q < 0`.  It does not prove the
growing-moment estimate itself. -/
theorem tendsto_negative_event_measure_zero_of_lintegral_bound_log_quadratic_rpow_log
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : ℕ → Measure Ω) (F : ℕ → Ω → ι → ℝ) (m : ℕ → ℕ)
    (C α q c : ℝ) (hq : 0 < q) (hgap : 2 + c * Real.log q < 0)
    (hMeas : ∀ d : ℕ, AEMeasurable
      (fun ω : Ω => ENNReal.ofReal (∑ i : ι, (F d ω i - 1) ^ (2 * m d))) (μ d))
    (hBound : ∀ d : ℕ,
      (∫⁻ ω, ENNReal.ofReal (∑ i : ι, (F d ω i - 1) ^ (2 * m d)) ∂(μ d)) ≤
        ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
          ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))) :
    Filter.Tendsto (fun d : ℕ => μ d {ω : Ω | ∃ i : ι, F d ω i < 0})
      Filter.atTop (nhds 0) := by
  refine tendsto_negative_event_measure_zero_of_lintegral_bound_ofReal μ F m
    (fun d : ℕ => C * ((Real.log (d : ℝ)) ^ α *
      ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ))))) hMeas hBound ?_
  exact const_mul_log_rpow_mul_quadratic_rpow_const_mul_log_tendsto_zero C α q c hq hgap

/-- Eventual paper-shape expectation-bound form of the high-moment PPT bridge.

The future growing-moment estimate only has to provide the paper-shape bound
eventually in the dimension parameter. -/
theorem tendsto_negative_event_measure_zero_of_eventually_lintegral_bound_log_quadratic_rpow_log
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : ℕ → Measure Ω) (F : ℕ → Ω → ι → ℝ) (m : ℕ → ℕ)
    (C α q c : ℝ) (hq : 0 < q) (hgap : 2 + c * Real.log q < 0)
    (hMeas : ∀ d : ℕ, AEMeasurable
      (fun ω : Ω => ENNReal.ofReal (∑ i : ι, (F d ω i - 1) ^ (2 * m d))) (μ d))
    (hBound : ∀ᶠ d : ℕ in Filter.atTop,
      (∫⁻ ω, ENNReal.ofReal (∑ i : ι, (F d ω i - 1) ^ (2 * m d)) ∂(μ d)) ≤
        ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
          ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))) :
    Filter.Tendsto (fun d : ℕ => μ d {ω : Ω | ∃ i : ι, F d ω i < 0})
      Filter.atTop (nhds 0) := by
  refine tendsto_negative_event_measure_zero_of_eventually_lintegral_bound_ofReal μ F m
    (fun d : ℕ => C * ((Real.log (d : ℝ)) ^ α *
      ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ))))) hMeas hBound ?_
  exact const_mul_log_rpow_mul_quadratic_rpow_const_mul_log_tendsto_zero C α q c hq hgap

/-- Dependent-index eventual paper-shape expectation-bound form of the
high-moment PPT bridge.

This is the concrete-model version of
`tendsto_negative_event_measure_zero_of_eventually_lintegral_bound_log_quadratic_rpow_log`:
the eigenvalue index type may vary with the dimension. -/
theorem tendsto_negative_event_measure_zero_of_eventually_lintegral_bound_log_quadratic_rpow_log_dependent
    {Ω : Type*} {ι : ℕ → Type*} [MeasurableSpace Ω] [∀ d : ℕ, Fintype (ι d)]
    (μ : ℕ → Measure Ω) (F : (d : ℕ) → Ω → ι d → ℝ) (m : ℕ → ℕ)
    (C α q c : ℝ) (hq : 0 < q) (hgap : 2 + c * Real.log q < 0)
    (hMeas : ∀ d : ℕ, AEMeasurable
      (fun ω : Ω => ENNReal.ofReal (∑ i : ι d, (F d ω i - 1) ^ (2 * m d))) (μ d))
    (hBound : ∀ᶠ d : ℕ in Filter.atTop,
      (∫⁻ ω, ENNReal.ofReal (∑ i : ι d, (F d ω i - 1) ^ (2 * m d)) ∂(μ d)) ≤
        ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
          ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))) :
    Filter.Tendsto (fun d : ℕ => μ d {ω : Ω | ∃ i : ι d, F d ω i < 0})
      Filter.atTop (nhds 0) := by
  refine
    tendsto_negative_event_measure_zero_of_eventually_lintegral_bound_ofReal_dependent
      μ F m
      (fun d : ℕ => C * ((Real.log (d : ℝ)) ^ α *
        ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))
      hMeas hBound ?_
  exact const_mul_log_rpow_mul_quadratic_rpow_const_mul_log_tendsto_zero C α q c hq hgap

/-- Paper-shape expectation-bound form of the high-moment PPT bridge, using the
readable threshold `c log(1/q) > 2`. -/
theorem tendsto_negative_event_measure_zero_of_lintegral_bound_log_quadratic_rpow_log_of_two_lt_mul_log_inv
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : ℕ → Measure Ω) (F : ℕ → Ω → ι → ℝ) (m : ℕ → ℕ)
    (C α q c : ℝ) (hq : 0 < q) (hc : 2 < c * Real.log q⁻¹)
    (hMeas : ∀ d : ℕ, AEMeasurable
      (fun ω : Ω => ENNReal.ofReal (∑ i : ι, (F d ω i - 1) ^ (2 * m d))) (μ d))
    (hBound : ∀ d : ℕ,
      (∫⁻ ω, ENNReal.ofReal (∑ i : ι, (F d ω i - 1) ^ (2 * m d)) ∂(μ d)) ≤
        ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
          ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))) :
    Filter.Tendsto (fun d : ℕ => μ d {ω : Ω | ∃ i : ι, F d ω i < 0})
      Filter.atTop (nhds 0) := by
  exact tendsto_negative_event_measure_zero_of_lintegral_bound_log_quadratic_rpow_log
    μ F m C α q c hq (two_add_mul_log_neg_of_two_lt_mul_log_inv hc) hMeas hBound

/-- Eventual paper-shape expectation-bound form of the high-moment PPT bridge,
using the readable threshold `c log(1/q) > 2`. -/
theorem tendsto_negative_event_measure_zero_of_eventually_lintegral_bound_log_quadratic_rpow_log_of_two_lt_mul_log_inv
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : ℕ → Measure Ω) (F : ℕ → Ω → ι → ℝ) (m : ℕ → ℕ)
    (C α q c : ℝ) (hq : 0 < q) (hc : 2 < c * Real.log q⁻¹)
    (hMeas : ∀ d : ℕ, AEMeasurable
      (fun ω : Ω => ENNReal.ofReal (∑ i : ι, (F d ω i - 1) ^ (2 * m d))) (μ d))
    (hBound : ∀ᶠ d : ℕ in Filter.atTop,
      (∫⁻ ω, ENNReal.ofReal (∑ i : ι, (F d ω i - 1) ^ (2 * m d)) ∂(μ d)) ≤
        ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
          ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))) :
    Filter.Tendsto (fun d : ℕ => μ d {ω : Ω | ∃ i : ι, F d ω i < 0})
      Filter.atTop (nhds 0) := by
  exact tendsto_negative_event_measure_zero_of_eventually_lintegral_bound_log_quadratic_rpow_log
    μ F m C α q c hq (two_add_mul_log_neg_of_two_lt_mul_log_inv hc) hMeas hBound

/-- Dependent-index eventual paper-shape expectation-bound form, using the
readable threshold `c log(1/q) > 2`. -/
theorem tendsto_negative_event_measure_zero_of_eventually_lintegral_bound_log_quadratic_rpow_log_dependent_of_two_lt_mul_log_inv
    {Ω : Type*} {ι : ℕ → Type*} [MeasurableSpace Ω] [∀ d : ℕ, Fintype (ι d)]
    (μ : ℕ → Measure Ω) (F : (d : ℕ) → Ω → ι d → ℝ) (m : ℕ → ℕ)
    (C α q c : ℝ) (hq : 0 < q) (hc : 2 < c * Real.log q⁻¹)
    (hMeas : ∀ d : ℕ, AEMeasurable
      (fun ω : Ω => ENNReal.ofReal (∑ i : ι d, (F d ω i - 1) ^ (2 * m d))) (μ d))
    (hBound : ∀ᶠ d : ℕ in Filter.atTop,
      (∫⁻ ω, ENNReal.ofReal (∑ i : ι d, (F d ω i - 1) ^ (2 * m d)) ∂(μ d)) ≤
        ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
          ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))) :
    Filter.Tendsto (fun d : ℕ => μ d {ω : Ω | ∃ i : ι d, F d ω i < 0})
      Filter.atTop (nhds 0) := by
  exact
    tendsto_negative_event_measure_zero_of_eventually_lintegral_bound_log_quadratic_rpow_log_dependent
      μ F m C α q c hq (two_add_mul_log_neg_of_two_lt_mul_log_inv hc)
      hMeas hBound

/-- Fully scalar `λ > 4` packaging for the controlled growing-moment route.

For every `λ > 4`, Lean chooses paper constants `eps`, `q`, and `c`.  If the
future random-matrix supplier proves the corresponding paper-shape centered
moment bound, then the negative-spectrum event probabilities tend to zero. -/
theorem exists_log_order_constants_and_tendsto_negative_event_measure_zero_of_four_lt
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : ℕ → Measure Ω) (F : ℕ → Ω → ι → ℝ) (m : ℕ → ℕ)
    (lam C α : ℝ) (hlam : 4 < lam)
    (hMeas : ∀ d : ℕ, AEMeasurable
      (fun ω : Ω => ENNReal.ofReal (∑ i : ι, (F d ω i - 1) ^ (2 * m d))) (μ d)) :
    ∃ eps q c : ℝ,
      0 < eps ∧ q = (4 + eps) / lam ∧ 0 < q ∧ q < 1 ∧
        0 < c ∧ 2 < c * Real.log q⁻¹ ∧
          ((∀ d : ℕ,
            (∫⁻ ω, ENNReal.ofReal (∑ i : ι, (F d ω i - 1) ^ (2 * m d)) ∂(μ d)) ≤
              ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
                ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))) →
            Filter.Tendsto (fun d : ℕ => μ d {ω : Ω | ∃ i : ι, F d ω i < 0})
              Filter.atTop (nhds 0)) := by
  rcases exists_log_order_constants_of_four_lt hlam with
    ⟨eps, q, c, heps, hq_def, hq_pos, hq_lt_one, hc_pos, hc⟩
  refine ⟨eps, q, c, heps, hq_def, hq_pos, hq_lt_one, hc_pos, hc, ?_⟩
  intro hBound
  exact tendsto_negative_event_measure_zero_of_lintegral_bound_log_quadratic_rpow_log_of_two_lt_mul_log_inv
    μ F m C α q c hq_pos hc hMeas hBound

/-- Fully scalar `λ > 4` packaging with an eventual paper-shape bound.

This is the preferred endpoint for future random-matrix suppliers, since
growing-moment estimates are normally stated only for all sufficiently large
dimensions. -/
theorem exists_log_order_constants_and_tendsto_negative_event_measure_zero_of_four_lt_eventually
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : ℕ → Measure Ω) (F : ℕ → Ω → ι → ℝ) (m : ℕ → ℕ)
    (lam C α : ℝ) (hlam : 4 < lam)
    (hMeas : ∀ d : ℕ, AEMeasurable
      (fun ω : Ω => ENNReal.ofReal (∑ i : ι, (F d ω i - 1) ^ (2 * m d))) (μ d)) :
    ∃ eps q c : ℝ,
      0 < eps ∧ q = (4 + eps) / lam ∧ 0 < q ∧ q < 1 ∧
        0 < c ∧ 2 < c * Real.log q⁻¹ ∧
          ((∀ᶠ d : ℕ in Filter.atTop,
            (∫⁻ ω, ENNReal.ofReal (∑ i : ι, (F d ω i - 1) ^ (2 * m d)) ∂(μ d)) ≤
              ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
                ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))) →
            Filter.Tendsto (fun d : ℕ => μ d {ω : Ω | ∃ i : ι, F d ω i < 0})
              Filter.atTop (nhds 0)) := by
  rcases exists_log_order_constants_of_four_lt hlam with
    ⟨eps, q, c, heps, hq_def, hq_pos, hq_lt_one, hc_pos, hc⟩
  refine ⟨eps, q, c, heps, hq_def, hq_pos, hq_lt_one, hc_pos, hc, ?_⟩
  intro hBound
  exact tendsto_negative_event_measure_zero_of_eventually_lintegral_bound_log_quadratic_rpow_log_of_two_lt_mul_log_inv
    μ F m C α q c hq_pos hc hMeas hBound

/-- Fully scalar `λ > 4` packaging with an eventual paper-shape bound and a
dimension-dependent spectral index type.

This is the concrete-model form of
`exists_log_order_constants_and_tendsto_negative_event_measure_zero_of_four_lt_eventually`.
It still assumes the hard growing-moment estimate; it only supplies the scalar
constant choice and the dependent-index Markov/decay adapter. -/
theorem exists_log_order_constants_and_tendsto_negative_event_measure_zero_of_four_lt_eventually_dependent
    {Ω : Type*} {ι : ℕ → Type*} [MeasurableSpace Ω] [∀ d : ℕ, Fintype (ι d)]
    (μ : ℕ → Measure Ω) (F : (d : ℕ) → Ω → ι d → ℝ) (m : ℕ → ℕ)
    (lam C α : ℝ) (hlam : 4 < lam)
    (hMeas : ∀ d : ℕ, AEMeasurable
      (fun ω : Ω => ENNReal.ofReal (∑ i : ι d, (F d ω i - 1) ^ (2 * m d))) (μ d)) :
    ∃ eps q c : ℝ,
      0 < eps ∧ q = (4 + eps) / lam ∧ 0 < q ∧ q < 1 ∧
        0 < c ∧ 2 < c * Real.log q⁻¹ ∧
          ((∀ᶠ d : ℕ in Filter.atTop,
            (∫⁻ ω, ENNReal.ofReal (∑ i : ι d, (F d ω i - 1) ^ (2 * m d)) ∂(μ d)) ≤
              ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
                ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))) →
            Filter.Tendsto (fun d : ℕ => μ d {ω : Ω | ∃ i : ι d, F d ω i < 0})
              Filter.atTop (nhds 0)) := by
  rcases exists_log_order_constants_of_four_lt hlam with
    ⟨eps, q, c, heps, hq_def, hq_pos, hq_lt_one, hc_pos, hc⟩
  refine ⟨eps, q, c, heps, hq_def, hq_pos, hq_lt_one, hc_pos, hc, ?_⟩
  intro hBound
  exact
    tendsto_negative_event_measure_zero_of_eventually_lintegral_bound_log_quadratic_rpow_log_dependent_of_two_lt_mul_log_inv
      μ F m C α q c hq_pos hc hMeas hBound

/-- Fully scalar `λ > 4` packaging with only coordinate a.e. measurability.

This is the same controlled growing-moment endpoint as
`exists_log_order_constants_and_tendsto_negative_event_measure_zero_of_four_lt_eventually_dependent`,
but the measurability input is reduced to the natural coordinate statement.
The growing-moment estimate itself remains the explicit theorem-strength
hypothesis consumed by the returned implication. -/
theorem exists_log_order_constants_and_tendsto_negative_event_measure_zero_of_four_lt_eventually_dependent_of_coordinate
    {Ω : Type*} {ι : ℕ → Type*} [MeasurableSpace Ω] [∀ d : ℕ, Fintype (ι d)]
    (μ : ℕ → Measure Ω) (F : (d : ℕ) → Ω → ι d → ℝ) (m : ℕ → ℕ)
    (lam C α : ℝ) (hlam : 4 < lam)
    (hCoord : ∀ d : ℕ, ∀ i : ι d,
      AEMeasurable (fun ω : Ω => F d ω i) (μ d)) :
    ∃ eps q c : ℝ,
      0 < eps ∧ q = (4 + eps) / lam ∧ 0 < q ∧ q < 1 ∧
        0 < c ∧ 2 < c * Real.log q⁻¹ ∧
          ((∀ᶠ d : ℕ in Filter.atTop,
            (∫⁻ ω, ENNReal.ofReal (∑ i : ι d, (F d ω i - 1) ^ (2 * m d)) ∂(μ d)) ≤
              ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
                ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))) →
            Filter.Tendsto (fun d : ℕ => μ d {ω : Ω | ∃ i : ι d, F d ω i < 0})
              Filter.atTop (nhds 0)) := by
  exact
    exists_log_order_constants_and_tendsto_negative_event_measure_zero_of_four_lt_eventually_dependent
      μ F m lam C α hlam
      (fun d =>
        centered_even_moment_lintegrand_aemeasurable_of_coordinate
          (μ d) (F d) (m d) (hCoord d))

/-- Fully scalar `λ > 4` packaging for the eventual finite-rate bound.

For every `λ > 4`, Lean chooses paper constants `eps`, `q`, and `c`.  If the
future random-matrix supplier proves the corresponding paper-shape centered
moment bound eventually, then the negative-spectrum event has the same
paper-shape probability bound eventually. -/
theorem exists_log_order_constants_and_eventually_negative_event_measure_le_of_four_lt
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : ℕ → Measure Ω) (F : ℕ → Ω → ι → ℝ) (m : ℕ → ℕ)
    (lam C α : ℝ) (hlam : 4 < lam)
    (hMeas : ∀ d : ℕ, AEMeasurable
      (fun ω : Ω => ENNReal.ofReal (∑ i : ι, (F d ω i - 1) ^ (2 * m d))) (μ d)) :
    ∃ eps q c : ℝ,
      0 < eps ∧ q = (4 + eps) / lam ∧ 0 < q ∧ q < 1 ∧
        0 < c ∧ 2 < c * Real.log q⁻¹ ∧
          ((∀ᶠ d : ℕ in Filter.atTop,
            (∫⁻ ω, ENNReal.ofReal (∑ i : ι, (F d ω i - 1) ^ (2 * m d)) ∂(μ d)) ≤
              ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
                ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))) →
            ∀ᶠ d : ℕ in Filter.atTop,
              μ d {ω : Ω | ∃ i : ι, F d ω i < 0} ≤
                ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
                  ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))) := by
  rcases exists_log_order_constants_of_four_lt hlam with
    ⟨eps, q, c, heps, hq_def, hq_pos, hq_lt_one, hc_pos, hc⟩
  refine ⟨eps, q, c, heps, hq_def, hq_pos, hq_lt_one, hc_pos, hc, ?_⟩
  intro hBound
  exact eventually_negative_event_measure_le_of_eventually_lintegral_bound_log_quadratic_rpow_log
    μ F m C α q c hMeas hBound

/-- Fully scalar `λ > 4` packaging for the eventual finite-rate bound with a
dimension-dependent spectral index type. -/
theorem exists_log_order_constants_and_eventually_negative_event_measure_le_of_four_lt_dependent
    {Ω : Type*} {ι : ℕ → Type*} [MeasurableSpace Ω] [∀ d : ℕ, Fintype (ι d)]
    (μ : ℕ → Measure Ω) (F : (d : ℕ) → Ω → ι d → ℝ) (m : ℕ → ℕ)
    (lam C α : ℝ) (hlam : 4 < lam)
    (hMeas : ∀ d : ℕ, AEMeasurable
      (fun ω : Ω => ENNReal.ofReal (∑ i : ι d, (F d ω i - 1) ^ (2 * m d))) (μ d)) :
    ∃ eps q c : ℝ,
      0 < eps ∧ q = (4 + eps) / lam ∧ 0 < q ∧ q < 1 ∧
        0 < c ∧ 2 < c * Real.log q⁻¹ ∧
          ((∀ᶠ d : ℕ in Filter.atTop,
            (∫⁻ ω, ENNReal.ofReal (∑ i : ι d, (F d ω i - 1) ^ (2 * m d)) ∂(μ d)) ≤
              ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
                ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))) →
            ∀ᶠ d : ℕ in Filter.atTop,
              μ d {ω : Ω | ∃ i : ι d, F d ω i < 0} ≤
                ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
                  ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))) := by
  rcases exists_log_order_constants_of_four_lt hlam with
    ⟨eps, q, c, heps, hq_def, hq_pos, hq_lt_one, hc_pos, hc⟩
  refine ⟨eps, q, c, heps, hq_def, hq_pos, hq_lt_one, hc_pos, hc, ?_⟩
  intro hBound
  exact
    eventually_negative_event_measure_le_of_eventually_lintegral_bound_log_quadratic_rpow_log_dependent
      μ F m C α q c hMeas hBound

/-- Fully scalar `λ > 4` finite-rate packaging with only coordinate
a.e. measurability.

This is the finite-rate companion to
`exists_log_order_constants_and_tendsto_negative_event_measure_zero_of_four_lt_eventually_dependent_of_coordinate`:
coordinate a.e. measurability supplies the centered-moment `lintegrand`
measurability, while the returned implication still keeps the growing-moment
bound explicit. -/
theorem exists_log_order_constants_and_eventually_negative_event_measure_le_of_four_lt_dependent_of_coordinate
    {Ω : Type*} {ι : ℕ → Type*} [MeasurableSpace Ω] [∀ d : ℕ, Fintype (ι d)]
    (μ : ℕ → Measure Ω) (F : (d : ℕ) → Ω → ι d → ℝ) (m : ℕ → ℕ)
    (lam C α : ℝ) (hlam : 4 < lam)
    (hCoord : ∀ d : ℕ, ∀ i : ι d,
      AEMeasurable (fun ω : Ω => F d ω i) (μ d)) :
    ∃ eps q c : ℝ,
      0 < eps ∧ q = (4 + eps) / lam ∧ 0 < q ∧ q < 1 ∧
        0 < c ∧ 2 < c * Real.log q⁻¹ ∧
          ((∀ᶠ d : ℕ in Filter.atTop,
            (∫⁻ ω, ENNReal.ofReal (∑ i : ι d, (F d ω i - 1) ^ (2 * m d)) ∂(μ d)) ≤
              ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
                ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))) →
            ∀ᶠ d : ℕ in Filter.atTop,
              μ d {ω : Ω | ∃ i : ι d, F d ω i < 0} ≤
                ENNReal.ofReal (C * ((Real.log (d : ℝ)) ^ α *
                  ((d : ℝ) ^ 2 * q ^ (c * Real.log (d : ℝ)))))) := by
  exact
    exists_log_order_constants_and_eventually_negative_event_measure_le_of_four_lt_dependent
      μ F m lam C α hlam
      (fun d =>
        centered_even_moment_lintegrand_aemeasurable_of_coordinate
          (μ d) (F d) (m d) (hCoord d))

/-- Direct asymptotic `lintegral` form of the high-moment PPT bridge.

If the unnormalised centered even spectral moment itself tends to zero in
`lintegral` along the chosen growing order `m d`, then the probability of a
negative spectral value tends to zero.  This is the cleanest abstract endpoint
for a future concrete growing-moment theorem. -/
theorem tendsto_negative_event_measure_zero_of_lintegral_tendsto_zero
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : ℕ → Measure Ω) (F : ℕ → Ω → ι → ℝ) (m : ℕ → ℕ)
    (hMeas : ∀ d : ℕ, AEMeasurable
      (fun ω : Ω => ENNReal.ofReal (∑ i : ι, (F d ω i - 1) ^ (2 * m d))) (μ d))
    (hMoment : Filter.Tendsto
      (fun d : ℕ =>
        ∫⁻ ω, ENNReal.ofReal (∑ i : ι, (F d ω i - 1) ^ (2 * m d)) ∂(μ d))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun d : ℕ => μ d {ω : Ω | ∃ i : ι, F d ω i < 0})
      Filter.atTop (nhds 0) :=
  tendsto_negative_event_measure_zero_of_lintegral_bound μ F m
    (fun d : ℕ =>
      ∫⁻ ω, ENNReal.ofReal (∑ i : ι, (F d ω i - 1) ^ (2 * m d)) ∂(μ d))
    hMeas (fun _d => le_rfl) hMoment

/-- Direct asymptotic `lintegral` form of the high-moment PPT bridge with a
dimension-dependent spectral index type.

This is the cleanest concrete-model endpoint when the future growing-moment
theorem is stated directly as convergence to zero of the unnormalised centered
even spectral moment. -/
theorem tendsto_negative_event_measure_zero_of_lintegral_tendsto_zero_dependent
    {Ω : Type*} {ι : ℕ → Type*} [MeasurableSpace Ω] [∀ d : ℕ, Fintype (ι d)]
    (μ : ℕ → Measure Ω) (F : (d : ℕ) → Ω → ι d → ℝ) (m : ℕ → ℕ)
    (hMeas : ∀ d : ℕ, AEMeasurable
      (fun ω : Ω => ENNReal.ofReal (∑ i : ι d, (F d ω i - 1) ^ (2 * m d))) (μ d))
    (hMoment : Filter.Tendsto
      (fun d : ℕ =>
        ∫⁻ ω, ENNReal.ofReal (∑ i : ι d, (F d ω i - 1) ^ (2 * m d)) ∂(μ d))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun d : ℕ => μ d {ω : Ω | ∃ i : ι d, F d ω i < 0})
      Filter.atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hMomentEvent :
      ∀ᶠ d : ℕ in Filter.atTop,
        (∫⁻ ω, ENNReal.ofReal (∑ i : ι d, (F d ω i - 1) ^ (2 * m d)) ∂(μ d)) ≤ ε :=
    (ENNReal.tendsto_nhds_zero.mp hMoment) ε hε
  filter_upwards [hMomentEvent] with d hd
  exact le_trans
    (negative_event_measure_le_lintegral_centered_even_moment
      (μ d) (F d) (m d) (hMeas d)) hd

/-- Direct asymptotic `lintegral` endpoint with only coordinate
a.e. measurability.

This is the shortest upper bridge for a future concrete growing-moment theorem
stated as `lintegral → 0`: it asks only for coordinate a.e. measurability of
the finite spectrum, and builds the centered even-moment integrand
measurability internally. -/
theorem tendsto_negative_event_measure_zero_of_lintegral_tendsto_zero_dependent_of_coordinate
    {Ω : Type*} {ι : ℕ → Type*} [MeasurableSpace Ω] [∀ d : ℕ, Fintype (ι d)]
    (μ : ℕ → Measure Ω) (F : (d : ℕ) → Ω → ι d → ℝ) (m : ℕ → ℕ)
    (hCoord : ∀ d : ℕ, ∀ i : ι d,
      AEMeasurable (fun ω : Ω => F d ω i) (μ d))
    (hMoment : Filter.Tendsto
      (fun d : ℕ =>
        ∫⁻ ω, ENNReal.ofReal (∑ i : ι d, (F d ω i - 1) ^ (2 * m d)) ∂(μ d))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun d : ℕ => μ d {ω : Ω | ∃ i : ι d, F d ω i < 0})
      Filter.atTop (nhds 0) :=
  tendsto_negative_event_measure_zero_of_lintegral_tendsto_zero_dependent
    μ F m
    (fun d =>
      centered_even_moment_lintegrand_aemeasurable_of_coordinate
        (μ d) (F d) (m d) (hCoord d))
    hMoment

end AubrunAlternative
