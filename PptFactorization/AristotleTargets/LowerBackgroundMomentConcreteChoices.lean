import PptFactorization.AppendixBLowerBoundClosure

/-!
Aristotle handoff for the corrected deleted-background moment tail.

Target: close the mean-centered deleted-background bad-set estimate used as
`hMoment` in
`AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_concreteScalarChoices`.

The old zero-centered target is intentionally not used: the correct center is
`lowerConcreteDeletedBackgroundMean R k d`.

Protected file: do not edit `PptFactorization/AppendixBSpikeLowerBound.lean`.

Allowed inputs/context: use existing local lemmas from
`PptFactorization.AppendixBLowerBoundClosure`,
`PptFactorization.AppendixBSphericalLevy`,
`PptFactorization.AppendixBLevyPolarBridge`, and mathlib.  Do not add axioms,
`opaque`, `unsafe`, new theorem parameters, or weaken the probability bound.

PROVIDED SOLUTION:
Use the existing spherical concentration/Levy framework.  The missing analytic
ingredient should be a Lipschitz estimate for `backgroundMomentValue` on the
deleted-column spherical good set, followed by the existing concentration
pipeline.  The scalar smallness of `lowerConcreteMomentBound` is already closed
in `AppendixB.lower_concrete_hMomentSmall`; this target must prove only the
probability estimate below.  Preserve the theorem statement exactly.
-/
namespace AppendixB

open MeasureTheory
open PptFactorization.RandomMatrixModel
open Filter
open scoped Topology

theorem lowerConcreteDeletedBackgroundMean_eq_deletedColumn_mean
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k d : ℕ) (hs : 0 < R.sample d) :
    lowerConcreteDeletedBackgroundMean R k d =
      ∫ X : SampleMatrix (Fin d) (Fin d)
          (DeletedColumn (⟨0, hs⟩ : Fin (R.sample d))),
        backgroundMomentValue
          (p := Fin d) (q := Fin d)
          (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
          (lowerConcreteN d) k X
        ∂_root_.PptFactorization.AppendixB.sphericalModelMeasure
          (p := Fin d) (q := Fin d)
          (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d))) := by
  simp [lowerConcreteDeletedBackgroundMean, hs]

/-- The strict moment bad set is contained in the closed absolute-deviation
set at the same threshold.

This closes the routine strict/closed-event plumbing for the lower moment
input.  The remaining concentration theorem may now be stated for the standard
closed deviation event `backgroundMomentDeviationSet`. -/
theorem lower_backgroundMomentBadSet_subset_deviationSet
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {N τ mean : ℝ} {k : ℕ} :
    backgroundMomentBadSet (p := p) (q := q) (σ := σ) N τ mean k ⊆
      backgroundMomentDeviationSet (p := p) (q := q) (σ := σ) N τ mean k := by
  intro X hX
  simpa [backgroundMomentBadSet, backgroundMomentDeviationSet] using
    (le_of_lt hX)

/-- Concrete lower moment-tail supplier from a closed deviation-set bound.

This theorem removes one bit of event plumbing from the probabilistic frontier:
it is enough to prove the concentration estimate for
`backgroundMomentDeviationSet`; Lean then derives the strict bad-set estimate
used by the lower background half-mass pipeline. -/
theorem lower_backgroundMomentTail_concreteChoices_of_deviationBound
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ}
    (hDeviation :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            (_root_.PptFactorization.AppendixB.sphericalModelMeasure
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
              (backgroundMomentDeviationSet
                (p := Fin d) (q := Fin d)
                (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
                (lowerConcreteN d) (lowerConcreteTau a slack d)
                (lowerConcreteDeletedBackgroundMean R k d) k) ≤
              lowerConcreteMomentBound R k a slack d) :
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
            lowerConcreteMomentBound R k a slack d := by
  intro a slack
  filter_upwards [hDeviation a slack] with d hd hs
  let μ :=
    _root_.PptFactorization.AppendixB.sphericalModelMeasure
      (p := Fin d) (q := Fin d)
      (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
  haveI : IsProbabilityMeasure μ :=
    _root_.PptFactorization.AppendixB.sphericalModelMeasure_isProbabilityMeasure
      (p := Fin d) (q := Fin d)
      (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
  have hmono :
      μ.real
          (backgroundMomentBadSet
            (p := Fin d) (q := Fin d)
            (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
            (lowerConcreteN d) (lowerConcreteTau a slack d)
            (lowerConcreteDeletedBackgroundMean R k d) k) ≤
        μ.real
          (backgroundMomentDeviationSet
            (p := Fin d) (q := Fin d)
            (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
            (lowerConcreteN d) (lowerConcreteTau a slack d)
            (lowerConcreteDeletedBackgroundMean R k d) k) :=
    measureReal_mono
      (lower_backgroundMomentBadSet_subset_deviationSet
        (p := Fin d) (q := Fin d)
        (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
        (N := lowerConcreteN d) (τ := lowerConcreteTau a slack d)
        (mean := lowerConcreteDeletedBackgroundMean R k d) (k := k))
      (h₂ := (measure_lt_top μ
        (backgroundMomentDeviationSet
          (p := Fin d) (q := Fin d)
          (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
          (lowerConcreteN d) (lowerConcreteTau a slack d)
          (lowerConcreteDeletedBackgroundMean R k d) k)).ne)
  exact hmono.trans (hd hs)

/-- Named closed-deviation lower moment-tail frontier.

This is the exact remaining concentration obligation for the lower moment side:
for every `(a, slack)`, the deleted-column spherical closed deviation event at
threshold `lowerConcreteTau a slack d` is controlled by
`lowerConcreteMomentBound R k a slack d`. -/
def lowerConcreteDeletedBackgroundMomentDeviationTailBound
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) : Prop :=
  ∀ a : ℝ, ∀ slack : ℝ,
    ∀ᶠ d in atTop,
      ∀ hs : 0 < R.sample d,
        (_root_.PptFactorization.AppendixB.sphericalModelMeasure
          (p := Fin d) (q := Fin d)
          (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
          (backgroundMomentDeviationSet
            (p := Fin d) (q := Fin d)
            (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
            (lowerConcreteN d) (lowerConcreteTau a slack d)
            (lowerConcreteDeletedBackgroundMean R k d) k) ≤
          lowerConcreteMomentBound R k a slack d

/-- Exponential closed-deviation frontier for the deleted-column background
moment.

The concrete endpoint budget is `exp (-d)`.  A concentration theorem of the
natural spherical form `exp (-c d²)` is strictly stronger, and the scalar
comparison to the endpoint budget is closed below. -/
def lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ a : ℝ, ∀ slack : ℝ,
      ∀ᶠ d in atTop,
        ∀ hs : 0 < R.sample d,
          (_root_.PptFactorization.AppendixB.sphericalModelMeasure
            (p := Fin d) (q := Fin d)
            (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
            (backgroundMomentDeviationSet
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
              (lowerConcreteN d) (lowerConcreteTau a slack d)
              (lowerConcreteDeletedBackgroundMean R k d) k) ≤
            Real.exp (-(c * (d : ℝ) ^ 2))

/-- Scalar comparison behind the moment-tail repair:
`exp (-c d²) ≤ exp (-d)` eventually for every `c > 0`. -/
theorem lower_exp_neg_const_mul_dsq_le_exp_neg_d_eventually
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ d : ℕ in atTop,
      Real.exp (-(c * (d : ℝ) ^ 2)) ≤ Real.exp (-(d : ℝ)) := by
  filter_upwards [eventually_ge_atTop (Nat.ceil (1 / c) + 1)] with d hd
  have hd_ge_ceil_nat : Nat.ceil (1 / c) ≤ d := by omega
  have hceil : (1 / c : ℝ) ≤ (Nat.ceil (1 / c) : ℝ) :=
    Nat.le_ceil _
  have hd_ge_ceil : (Nat.ceil (1 / c) : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast hd_ge_ceil_nat
  have hinv_le_d : (1 / c : ℝ) ≤ (d : ℝ) :=
    hceil.trans hd_ge_ceil
  have hc_nonneg : 0 ≤ c := le_of_lt hc
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have hcd_ge_one : 1 ≤ c * (d : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hinv_le_d hc_nonneg
    have hone : c * c⁻¹ = 1 := mul_inv_cancel₀ hc_ne
    simpa [one_div, hone] using hmul
  have hd_nonneg : 0 ≤ (d : ℝ) := by positivity
  have hd_le : (d : ℝ) ≤ c * (d : ℝ) ^ 2 := by
    calc
      (d : ℝ) = 1 * (d : ℝ) := by ring
      _ ≤ (c * (d : ℝ)) * (d : ℝ) :=
        mul_le_mul_of_nonneg_right hcd_ge_one hd_nonneg
      _ = c * (d : ℝ) ^ 2 := by ring
  exact Real.exp_le_exp_of_le (by linarith)

/-- Scalar comparison behind the second-moment-tail bridge:
`exp (-c d²) ≤ 1 / d²` eventually for every `c > 0`.

Since `lowerConcreteN d = d²`, this is exactly the comparison from a natural
spherical exponential concentration estimate to the polynomial Chebyshev
budget used by the `1 / d` background-typical threshold. -/
theorem lower_exp_neg_const_mul_dsq_le_inv_lowerConcreteN_eventually
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ d : ℕ in atTop,
      Real.exp (-(c * (d : ℝ) ^ 2)) ≤ ((lowerConcreteN d : ℝ))⁻¹ := by
  filter_upwards [eventually_ge_atTop (Nat.ceil (2 / c) + 1)] with d hd
  have hd_ge_ceil_nat : Nat.ceil (2 / c) ≤ d := by omega
  have hceil : (2 / c : ℝ) ≤ (Nat.ceil (2 / c) : ℝ) :=
    Nat.le_ceil _
  have hd_ge_ceil : (Nat.ceil (2 / c) : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast hd_ge_ceil_nat
  have htwoc_le_d : (2 / c : ℝ) ≤ (d : ℝ) :=
    hceil.trans hd_ge_ceil
  have hc_nonneg : 0 ≤ c := le_of_lt hc
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have hcd_ge_two : 2 ≤ c * (d : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left htwoc_le_d hc_nonneg
    have htwo : c * (2 / c) = 2 := by field_simp [hc_ne]
    simpa [htwo] using hmul
  have hd_pos_nat : 0 < d := by omega
  have hd_pos : 0 < (d : ℝ) := by exact_mod_cast hd_pos_nat
  have hd_nonneg : 0 ≤ (d : ℝ) := le_of_lt hd_pos
  have htwo_d_le : 2 * (d : ℝ) ≤ c * (d : ℝ) ^ 2 := by
    calc
      2 * (d : ℝ) ≤ (c * (d : ℝ)) * (d : ℝ) :=
        mul_le_mul_of_nonneg_right hcd_ge_two hd_nonneg
      _ = c * (d : ℝ) ^ 2 := by ring
  have hlog_le : Real.log (d : ℝ) ≤ (d : ℝ) :=
    Real.log_le_self hd_pos.le
  have htwo_log_le : 2 * Real.log (d : ℝ) ≤ c * (d : ℝ) ^ 2 := by
    nlinarith
  have hneg : -(c * (d : ℝ) ^ 2) ≤ -(2 * Real.log (d : ℝ)) := by
    linarith
  have hexp_le :
      Real.exp (-(c * (d : ℝ) ^ 2)) ≤
        Real.exp (-(2 * Real.log (d : ℝ))) :=
    Real.exp_le_exp_of_le hneg
  have hexp_eq :
      Real.exp (-(2 * Real.log (d : ℝ))) = ((d : ℝ) ^ 2)⁻¹ := by
    rw [Real.exp_neg]
    have hmain : Real.exp (2 * Real.log (d : ℝ)) = (d : ℝ) ^ 2 := by
      have htwo :
          (2 : ℝ) * Real.log (d : ℝ) =
            Real.log (d : ℝ) + Real.log (d : ℝ) := by
        ring
      rw [htwo, Real.exp_add]
      simp [Real.exp_log hd_pos, pow_two]
    rw [hmain]
  calc
    Real.exp (-(c * (d : ℝ) ^ 2))
        ≤ Real.exp (-(2 * Real.log (d : ℝ))) := hexp_le
    _ = ((d : ℝ) ^ 2)⁻¹ := hexp_eq
    _ = ((lowerConcreteN d : ℝ))⁻¹ := by simp [lowerConcreteN]

/-- A natural exponential concentration estimate at scale `exp (-c d²)`
supplies the exact `exp (-d)` closed-deviation frontier used by the lower
endpoint. -/
theorem lowerConcreteDeletedBackgroundMomentDeviationTailBound_of_exponentialDeviationTailBound
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ)
    (hExp :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R k) :
    lowerConcreteDeletedBackgroundMomentDeviationTailBound R k := by
  rcases hExp with ⟨c, hc, hTail⟩
  intro a slack
  filter_upwards
    [hTail a slack,
      lower_exp_neg_const_mul_dsq_le_exp_neg_d_eventually (c := c) hc]
    with d hdTail hdScalar hs
  exact (hdTail hs).trans (by
    simpa [lowerConcreteMomentBound] using hdScalar)

/-- Polynomial moment-tail budget supplied by the second-moment/Chebyshev
route.  Since `lowerConcreteN d = d²`, this is the advertised `C / d²`
failure probability at the endpoint tolerance `τ_d = 1 / d`. -/
noncomputable def lowerConcreteMomentPolynomialBound
    (C : ℝ)
    (_R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (_k : ℕ) (_a _slack : ℝ) (d : ℕ) : ℝ :=
  C / (lowerConcreteN d : ℝ)

/-- The polynomial Chebyshev budget `C / d²` is eventually smaller than every
positive constant. -/
theorem lower_concrete_polynomialMomentSmall
    (C : ℝ)
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) :
    ∀ a : ℝ, ∀ slack : ℝ, ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        lowerConcreteMomentPolynomialBound C R k a slack d ≤ η := by
  intro a slack η hη
  have hN_atTop :
      Tendsto (fun d : ℕ => (lowerConcreteN d : ℝ)) atTop atTop := by
    simpa [lowerConcreteN] using
      ((tendsto_rpow_atTop (show (0 : ℝ) < 2 by norm_num)).comp
        tendsto_natCast_atTop_atTop)
  have hinv :
      Tendsto (fun d : ℕ => ((lowerConcreteN d : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hN_atTop
  have hlim :
      Tendsto
        (fun d : ℕ => lowerConcreteMomentPolynomialBound C R k a slack d)
        atTop (nhds 0) := by
    simpa [lowerConcreteMomentPolynomialBound, div_eq_mul_inv] using
      (tendsto_const_nhds.mul hinv : Tendsto
        (fun d : ℕ => C * ((lowerConcreteN d : ℝ))⁻¹) atTop
          (nhds (C * 0)))
  have hevent :
      ∀ᶠ d in atTop,
        lowerConcreteMomentPolynomialBound C R k a slack d ∈ Set.Iio η :=
    hlim.eventually (Iio_mem_nhds hη)
  filter_upwards [hevent] with d hd
  exact le_of_lt hd

/-- Second-moment/Chebyshev closed-deviation frontier for the deleted-column
background moment.

This is the Lean-facing form of the Wick variance theorem
`Var(M_d) = O(d⁻⁴)`: at the concrete tolerance `lowerConcreteTau = 1 / d`,
the closed deviation event has probability at most `C / d²`. -/
def lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ a : ℝ, ∀ slack : ℝ,
      ∀ᶠ d in atTop,
        ∀ hs : 0 < R.sample d,
          (_root_.PptFactorization.AppendixB.sphericalModelMeasure
            (p := Fin d) (q := Fin d)
            (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
            (backgroundMomentDeviationSet
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
              (lowerConcreteN d) (lowerConcreteTau a slack d)
              (lowerConcreteDeletedBackgroundMean R k d) k) ≤
            lowerConcreteMomentPolynomialBound C R k a slack d

/-- A natural exponential concentration estimate at scale `exp (-c d²)`
supplies the exact polynomial second-moment/Chebyshev frontier `C / d²`.

This is a certified scalar bridge into the paper-facing
`deletedColumnSphericalMoment_variance_le_const_div_d4` predicate: the
remaining theorem-strength issue is proving the concentration/variance source,
not comparing its rate to the endpoint budget. -/
theorem lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound_of_exponentialDeviationTailBound
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ)
    (hExp :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R k) :
    lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k := by
  rcases hExp with ⟨c, hc, hTail⟩
  refine ⟨1, by norm_num, ?_⟩
  intro a slack
  filter_upwards
    [hTail a slack,
      lower_exp_neg_const_mul_dsq_le_inv_lowerConcreteN_eventually (c := c) hc]
    with d hdTail hdScalar hs
  exact (hdTail hs).trans (by
    simpa [lowerConcreteMomentPolynomialBound, one_div] using hdScalar)

/-- The grouped Wick/Chebyshev deviation frontier makes the deleted-background
closed deviation event negligible at the concrete tolerance.

This is the direct probabilistic force of
`lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound`: after
the constant `C` is supplied, the remaining step is only the scalar limit
`C / d^2 -> 0`. -/
theorem lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound.eventuallySmall
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ)
    (hDeviation :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k) :
    ∀ a : ℝ, ∀ slack : ℝ, ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        ∀ hs : 0 < R.sample d,
          (_root_.PptFactorization.AppendixB.sphericalModelMeasure
            (p := Fin d) (q := Fin d)
            (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
            (backgroundMomentDeviationSet
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
              (lowerConcreteN d) (lowerConcreteTau a slack d)
              (lowerConcreteDeletedBackgroundMean R k d) k) ≤ η := by
  rcases hDeviation with ⟨C, _hC, hDev⟩
  intro a slack η hη
  filter_upwards
    [hDev a slack,
      lower_concrete_polynomialMomentSmall C R k a slack η hη] with d hdDev hdSmall hs
  exact (hdDev hs).trans hdSmall

/-- Arithmetic core of the two-trace PT Wick exponent bound.

This is the final linear step in `LFC-PPT-007`.  In the two-trace expansion
the ambient permutation group is `S_{2k}`, so each cycle count is rewritten as
`2k -` its Cayley length.  Once the two triangle inequalities
`|γ₂ σ| + |σ| ≥ 2k - 2` and `|γ₂⁻¹ σ| + |σ| ≥ 2k - 2` are available, the
source-of-truth exponent with normalizing constant `4k + 4` is nonpositive.

The remaining work for the exact Wick theorem is therefore the finite
Gaussian/permutation expansion and the cycle-count-to-length/geodesic
instantiation, not this normalization arithmetic. -/
theorem ptSecondWickExponent_nonpositive_arith_of_cayley_length_triangles
    {k cγσ cγiσ cσ lγσ lγiσ lσ : ℤ}
    (hγσ : cγσ = 2 * k - lγσ)
    (hγiσ : cγiσ = 2 * k - lγiσ)
    (hσ : cσ = 2 * k - lσ)
    (htriγ : 2 * k - 2 ≤ lγσ + lσ)
    (htriγi : 2 * k - 2 ≤ lγiσ + lσ) :
    cγσ + cγiσ + 2 * cσ - (4 * k + 4) ≤ 0 := by
  linarith

/-- Arithmetic core of the connected `d⁻⁴` gap in the two-trace PT Wick
variance proof.

If a non-block-preserving contraction has a defect of at least `2` in each of
the two Cayley geodesic inequalities, then the same two-trace exponent is at
most `-4`.  This is the exact power gap needed to make all connected
permutations contribute `O(d⁻⁴)` after the spherical normalization. -/
theorem ptSecondWickExponent_connected_le_neg_four_arith_of_geodesic_defects
    {k cγσ cγiσ cσ lγσ lγiσ lσ : ℤ}
    (hγσ : cγσ = 2 * k - lγσ)
    (hγiσ : cγiσ = 2 * k - lγiσ)
    (hσ : cσ = 2 * k - lσ)
    (hdefγ : 2 * k ≤ lγσ + lσ)
    (hdefγi : 2 * k ≤ lγiσ + lσ) :
    cγσ + cγiσ + 2 * cσ - (4 * k + 4) ≤ -4 := by
  linarith

/-- Paper-facing name for the two-trace Wick expansion input behind the
deleted-column second-moment bound.

The current endpoint consumes this together with the variance comparison and
Chebyshev step as the single frontier
`lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound`. -/
def deletedColumnSphericalMoment_secondMoment_expansion
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) : Prop :=
  lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k

/-- Paper-facing name for the variance estimate `Var(M_d) ≤ C / d^4`. -/
def deletedColumnSphericalMoment_variance_le_const_div_d4
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) : Prop :=
  lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k

/-- Exponential concentration implies the paper-facing variance-tail name.

This theorem removes the scalar-rate bookkeeping from `LFC-PPT-008`: an
`exp (-c d²)` estimate is stronger than the endpoint `C / d²` Chebyshev
budget. -/
theorem deletedColumnSphericalMoment_variance_le_const_div_d4_of_exponentialDeviationTailBound
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ)
    (hExp :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R k) :
    deletedColumnSphericalMoment_variance_le_const_div_d4 R k :=
  lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound_of_exponentialDeviationTailBound
    R k hExp

/-- Paper-facing name for the endpoint tail
`P(|M_d - E M_d| > 1 / d) ≤ C / d^2`. -/
def deletedColumnSphericalMoment_deviation_one_over_d
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) : Prop :=
  lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k

theorem deletedColumnSphericalMoment_secondMoment_expansion_iff_secondMomentWickDeviationTailBound
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) :
    deletedColumnSphericalMoment_secondMoment_expansion R k ↔
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k := by
  rfl

theorem deletedColumnSphericalMoment_variance_le_const_div_d4_iff_secondMomentWickDeviationTailBound
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) :
    deletedColumnSphericalMoment_variance_le_const_div_d4 R k ↔
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k := by
  rfl

theorem deletedColumnSphericalMoment_deviation_one_over_d_iff_secondMomentWickDeviationTailBound
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) :
    deletedColumnSphericalMoment_deviation_one_over_d R k ↔
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k := by
  rfl

/-- The grouped Wick/Chebyshev frontier supplies the paper-facing two-trace
second-moment expansion name at this abstraction layer. -/
theorem deletedColumnSphericalMoment_secondMoment_expansion_of_secondMomentWickDeviationTailBound
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ)
    (h :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k) :
    deletedColumnSphericalMoment_secondMoment_expansion R k :=
  (deletedColumnSphericalMoment_secondMoment_expansion_iff_secondMomentWickDeviationTailBound
    R k).2 h

/-- The paper-facing two-trace second-moment expansion name unpacks to the
grouped Wick/Chebyshev frontier. -/
theorem lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound_of_secondMoment_expansion
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ)
    (hSecond :
      deletedColumnSphericalMoment_secondMoment_expansion R k) :
    lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k :=
  (deletedColumnSphericalMoment_secondMoment_expansion_iff_secondMomentWickDeviationTailBound
    R k).1 hSecond

/-- The grouped Wick/Chebyshev frontier supplies the paper-facing variance
name. -/
theorem deletedColumnSphericalMoment_variance_le_const_div_d4_of_secondMomentWickDeviationTailBound
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ)
    (h :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k) :
    deletedColumnSphericalMoment_variance_le_const_div_d4 R k :=
  (deletedColumnSphericalMoment_variance_le_const_div_d4_iff_secondMomentWickDeviationTailBound
    R k).2 h

/-- The grouped Wick/Chebyshev frontier supplies the paper-facing `1/d`
deviation-tail name. -/
theorem deletedColumnSphericalMoment_deviation_one_over_d_of_secondMomentWickDeviationTailBound
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ)
    (h :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k) :
    deletedColumnSphericalMoment_deviation_one_over_d R k :=
  (deletedColumnSphericalMoment_deviation_one_over_d_iff_secondMomentWickDeviationTailBound
    R k).2 h

theorem lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound_of_deletedColumnSphericalMoment_deviation_one_over_d
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ)
    (hDeviation : deletedColumnSphericalMoment_deviation_one_over_d R k) :
    lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k :=
  hDeviation

/-- In the current Lean abstraction layer, the paper-facing variance theorem is
the grouped Wick/Chebyshev tail frontier.  This adapter makes the intended
logical direction explicit: once the variance theorem is supplied, the endpoint
does not need a separate deviation-tail hypothesis. -/
theorem lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound_of_deletedColumnSphericalMoment_variance_le_const_div_d4
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ)
    (hVariance : deletedColumnSphericalMoment_variance_le_const_div_d4 R k) :
    lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k :=
  hVariance

/-- Chebyshev-facing paper theorem: the `1 / d` deviation tail is obtained from
the variance theorem.

At this Lean layer both paper-facing names unfold to the same grouped
second-moment Wick/Chebyshev frontier, but the theorem records the intended
dependency direction and lets endpoint adapters drop the separate deviation
hypothesis. -/
theorem deletedColumnSphericalMoment_deviation_one_over_d_of_variance_le_const_div_d4
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ)
    (hVariance : deletedColumnSphericalMoment_variance_le_const_div_d4 R k) :
    deletedColumnSphericalMoment_deviation_one_over_d R k :=
  hVariance

/-- Paper-facing second-moment stack closes the grouped Wick/Chebyshev
deviation frontier used by the lower endpoint.

The three named inputs are kept in the statement to match the mathematical
audit: two-trace expansion, variance gap, and the `1 / d` Chebyshev tail.  In
the present Lean layer they are aliases for the single endpoint frontier, so
the final deviation input is enough to discharge the grouped obligation. -/
theorem lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound_of_paperFacingDeviationStack
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ)
    (_hSecond :
      deletedColumnSphericalMoment_secondMoment_expansion R k)
    (_hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (hDeviation :
      deletedColumnSphericalMoment_deviation_one_over_d R k) :
    lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k :=
  lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound_of_deletedColumnSphericalMoment_deviation_one_over_d
    R k hDeviation

/-- Paper-facing second-moment stack, with the deviation corollary derived from
the variance input.

This is the dependency shape used by the endpoint after `LFC-PPT-008`: the
explicit deviation hypothesis is no longer needed once
`deletedColumnSphericalMoment_variance_le_const_div_d4` is available.

At this abstraction layer `deletedColumnSphericalMoment_secondMoment_expansion`
is the same grouped Wick/Chebyshev predicate, so the endpoint does not need to
carry it separately once the variance theorem is present. -/
theorem lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound_of_paperFacingVarianceStack
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k) :
    lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k :=
  lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound_of_deletedColumnSphericalMoment_variance_le_const_div_d4
    R k hVariance

/-- Strict bad-set version of the polynomial second-moment/Chebyshev tail. -/
def lowerConcreteDeletedBackgroundMomentSecondMomentWickBadTailBound
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
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
            lowerConcreteMomentPolynomialBound C R k a slack d

/-- Closed polynomial second-moment tail implies the strict bad-set polynomial
tail used by the lower background half-mass pipeline. -/
theorem lowerConcreteDeletedBackgroundMomentSecondMomentWickBadTailBound_of_deviationTailBound
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ)
    (hDeviation :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k) :
    lowerConcreteDeletedBackgroundMomentSecondMomentWickBadTailBound R k := by
  rcases hDeviation with ⟨C, hC, hDev⟩
  refine ⟨C, hC, ?_⟩
  intro a slack
  filter_upwards [hDev a slack] with d hd hs
  let μ :=
    _root_.PptFactorization.AppendixB.sphericalModelMeasure
      (p := Fin d) (q := Fin d)
      (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
  haveI : IsProbabilityMeasure μ :=
    _root_.PptFactorization.AppendixB.sphericalModelMeasure_isProbabilityMeasure
      (p := Fin d) (q := Fin d)
      (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
  have hmono :
      μ.real
          (backgroundMomentBadSet
            (p := Fin d) (q := Fin d)
            (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
            (lowerConcreteN d) (lowerConcreteTau a slack d)
            (lowerConcreteDeletedBackgroundMean R k d) k) ≤
        μ.real
          (backgroundMomentDeviationSet
            (p := Fin d) (q := Fin d)
            (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
            (lowerConcreteN d) (lowerConcreteTau a slack d)
            (lowerConcreteDeletedBackgroundMean R k d) k) :=
    measureReal_mono
      (lower_backgroundMomentBadSet_subset_deviationSet
        (p := Fin d) (q := Fin d)
        (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
        (N := lowerConcreteN d) (τ := lowerConcreteTau a slack d)
        (mean := lowerConcreteDeletedBackgroundMean R k d) (k := k))
      (h₂ := (measure_lt_top μ
        (backgroundMomentDeviationSet
          (p := Fin d) (q := Fin d)
          (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
          (lowerConcreteN d) (lowerConcreteTau a slack d)
          (lowerConcreteDeletedBackgroundMean R k d) k)).ne)
  exact hmono.trans (hd hs)

/-- The same grouped Wick/Chebyshev input makes the strict bad-background event
negligible.  This is the form feeding the lower background half-mass step: the
moment bad set has probability `o(1)`. -/
theorem lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound.badSetEventuallySmall
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ)
    (hDeviation :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k) :
    ∀ a : ℝ, ∀ slack : ℝ, ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        ∀ hs : 0 < R.sample d,
          (_root_.PptFactorization.AppendixB.sphericalModelMeasure
            (p := Fin d) (q := Fin d)
            (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
            (backgroundMomentBadSet
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
              (lowerConcreteN d) (lowerConcreteTau a slack d)
              (lowerConcreteDeletedBackgroundMean R k d) k) ≤ η := by
  rcases
    lowerConcreteDeletedBackgroundMomentSecondMomentWickBadTailBound_of_deviationTailBound
      (R := R) (k := k) hDeviation with
    ⟨C, _hC, hBad⟩
  intro a slack η hη
  filter_upwards
    [hBad a slack,
      lower_concrete_polynomialMomentSmall C R k a slack η hη] with d hdBad hdSmall hs
  exact (hdBad hs).trans hdSmall

/-- Named strict bad-set lower moment-tail frontier.

This is the strict-event form consumed by the lower no-input wrappers. -/
def lowerConcreteDeletedBackgroundMomentBadTailBound
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) : Prop :=
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
          lowerConcreteMomentBound R k a slack d

/-- Closed-deviation named frontier implies the strict bad-set named frontier. -/
theorem lowerConcreteDeletedBackgroundMomentBadTailBound_of_deviationTailBound
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ)
    (hDeviation :
      lowerConcreteDeletedBackgroundMomentDeviationTailBound R k) :
    lowerConcreteDeletedBackgroundMomentBadTailBound R k :=
  lower_backgroundMomentTail_concreteChoices_of_deviationBound
    (R := R) (k := k) hDeviation

/-!
Retired route.

The active lower assembly no longer depends on the old direct no-input moment
tail theorem.  The live frontier keeps the honest closed-deviation hypothesis
explicit and uses
`lower_backgroundMomentTail_concreteChoices_of_deviationBound` as the only
moment-side supplier in this file.
-/

end AppendixB
