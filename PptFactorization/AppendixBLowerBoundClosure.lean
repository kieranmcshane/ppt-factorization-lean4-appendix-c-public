import PptFactorization.AppendixBSpikeLowerBound
import PptFactorization.AppendixBConcreteModel
import PptFactorization.AppendixBConcreteBridge

/-!
# Appendix B lower-bound closure

Thin stable aliases for the lower-bound endpoint stack.

The public wrappers in this file are project-axiom-free by the local audit of
their `#print axioms` output: they introduce no project-specific axiom beyond
Lean/mathlib's standard foundational axioms reported by the audit.  Each proof
is only an `exact` call to the corresponding theorem in
`AppendixBSpikeLowerBound`.

The deleted-column transport and the Beta × directions machinery used by this
endpoint stack are already closed in `AppendixBSpikeLowerBound`; this file only
gives stable downstream names for those closed results and the final
bookkeeping wrappers.

The scalar and asymptotic facts that are not proved by these wrappers remain
visible as theorem parameters.  In particular, hypotheses such as
`hColumnIncluded`, `hProduct`, `hBeta`, `hCap`, `hBackgroundHalf`,
`hDeltaLimit`, `hEntropyLimit`, `hOneMinusLimit`, and `hCapCostLimit` are
assumptions of the alias theorem being called, not hidden axioms and not claimed
unconditionally here.

The concrete bundled endpoint
`lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_deterministic_blocks`
now derives `hColumnIncluded` from the closed deterministic one-column event
inclusion.  Its remaining assumptions are still explicit theorem parameters:
the model-specific deterministic spike profile, background transfer,
mixed-remainder, mean, and budget estimates, plus the cone-coordinate/unit
direction facts and deleted-background bad-set bounds.

Concretely, after the closed Beta/direction/deleted-column core has been
instantiated, the remaining model-specific scalar bookkeeping is exactly the
lower-bound scale asymptotics:

* `(-Real.log (δ a slack d)) / spikeSpeed k d → 0`;
* the entropy term
  `((N d : ℝ) * (2 * Real.log (N d : ℝ) -
    Real.log (a * spikeSpeed k d))) / spikeSpeed k d → 0`;
* the one-minus Beta term divided by `spikeSpeed k d` tends to `lam * a`;
* `capNLogNCost 2 (Ncap d : ℝ) / spikeSpeed k d → 0`.

Together with the visible positivity, upper-endpoint, and dimension-shape
assumptions, those are the concrete model-instantiation obligations before the
final call to
`eventual_log_over_spikeSpeed_lower_of_oneColumn_probability_pipeline_scalar_limits`
or its stable wrapper `lower_eventual_log_over_spikeSpeed`.
-/

namespace AppendixB

open PptFactorization.RandomMatrixModel
open MeasureTheory
open Filter
open scoped Topology

/-- Exact target probability sequence for the lower one-column deviation event.

At dimension/index `d`, this is the probability under `μ d` of the upper-tail
moment event
`eps d ≤ scaledTracePower (N d) k (gamma (densityMatrix X)) - mean d`.
This is the concrete `targetProb d` appearing in the lower-bound inclusion
theorems; no scalar or asymptotic assumption is hidden in this definition. -/
noncomputable def lowerTargetProb
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [MeasurableSpace (SampleMatrix p q σ)]
    (μ : ℕ → Measure (SampleMatrix p q σ))
    (N eps mean : ℕ → ℝ) (k : ℕ) : ℕ → ℝ :=
  fun d =>
    (μ d).real
      (columnMomentUpperTailSet
        (p := p) (q := q) (σ := σ)
        (N d) (eps d) (mean d) k)

/-- Thin alias for the closed deterministic inclusion
`columnProb a slack d ≤ targetProb d`.

This is the event-level bridge in the lower-bound pipeline: the concrete
one-column favourable event, consisting of the Beta mass interval, cap/direction
condition, and deleted-background typicality, is contained in the target
upper-tail lower-deviation event once the pure-spike, background, mixed, mean,
and scalar-budget hypotheses are supplied.  Those hypotheses remain explicit
parameters; the wrapper only gives the closed inclusion a stable downstream
name. -/
theorem lower_columnProb_le_targetProb_of_closed_deterministic_blocks
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [MeasurableSpace (SampleMatrix p q σ)] [DecidableEq σ]
    {μ : ℕ → Measure (SampleMatrix p q σ)}
    {columnProb : ℝ → ℝ → ℕ → ℝ} {targetProb : ℕ → ℝ}
    {q₀ δ N M eps mean center errProfile errSpike τ errScale errBg errMix
      errMean : ℝ → ℝ → ℕ → ℝ}
    {directionSet :
      ℝ → ℝ → ℕ → Set (EuclideanSpace ℂ (BipIndex p q))}
    {root : ℝ} {α₀ : σ} {k : ℕ}
    (hFinite : ∀ᶠ d in atTop, IsFiniteMeasure (μ d))
    (hColumnProb :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            columnProb a slack d =
              (μ d).real
                (sphericalOneColumnFavorableEvent
                  (p := p) (q := q) (σ := σ)
                  α₀ (q₀ a slack d) (δ a slack d)
                  (directionSet a slack d)
                  (backgroundTypicalSet (p := p) (q := q) (σ := σ)
                    (N a slack d) (M a slack d) (τ a slack d)
                    (center a slack d) k)))
    (hTargetProb :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            targetProb d =
              (μ d).real
                (columnMomentUpperTailSet
                  (p := p) (q := q) (σ := σ)
                  (N a slack d) (eps a slack d) (mean a slack d) k))
    (hProfile :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ R : ℝ, ∀ u : EuclideanSpace ℂ (BipIndex p q),
              R ∈ betaColumnIntervalSet (q₀ a slack d) (δ a slack d) →
              u ∈ directionSet a slack d →
              a ^ k - errProfile a slack d ≤
                columnDirectionSpikeProfile
                  (p := p) (q := q) (N a slack d) k R u)
    (hPureError :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            errProfile a slack d + 0 ≤ errSpike a slack d)
    (hBackgroundTransfer :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ X : SampleMatrix p q σ,
              sampleColumnComplementNormalized
                  (p := p) (q := q) (σ := σ) X α₀ ∈
                backgroundTypicalSet
                  (p := p) (q := q) (σ := σ)
                  (N a slack d) (M a slack d) (τ a slack d)
                  (center a slack d) k →
              backgroundMomentValue
                  (p := p) (q := q) (σ := σ) (N a slack d) k
                  (sampleColumnComplementNormalized
                    (p := p) (q := q) (σ := σ) X α₀) -
                  errScale a slack d ≤
                columnBackgroundContribution
                  (p := p) (q := q) (σ := σ) (N a slack d) k X α₀)
    (hBackgroundError :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            τ a slack d + errScale a slack d ≤ errBg a slack d)
    (hMixed :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ X : SampleMatrix p q σ,
              X ∈ sphericalOneColumnFavorableEvent
                (p := p) (q := q) (σ := σ)
                α₀ (q₀ a slack d) (δ a slack d)
                (directionSet a slack d)
                (backgroundTypicalSet
                  (p := p) (q := q) (σ := σ)
                  (N a slack d) (M a slack d) (τ a slack d)
                  (center a slack d) k) →
              |columnMixedRemainder
                  (p := p) (q := q) (σ := σ) (N a slack d) k X α₀| ≤
                errMix a slack d)
    (hMean :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            mean a slack d ≤ center a slack d + errMean a slack d)
    (hBudget :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            eps a slack d + errSpike a slack d + errBg a slack d +
              errMix a slack d + errMean a slack d ≤ a ^ k) :
    ∀ a : ℝ, root < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop, columnProb a slack d ≤ targetProb d := by
  exact
    oneColumnProbabilityPipeline_hColumnIncluded_of_closed_deterministic_blocks
      (p := p) (q := q) (σ := σ)
      (μ := μ)
      (columnProb := columnProb) (targetProb := targetProb)
      (q₀ := q₀) (δ := δ) (N := N) (M := M)
      (eps := eps) (mean := mean) (center := center)
      (errProfile := errProfile) (errSpike := errSpike)
      (τ := τ) (errScale := errScale) (errBg := errBg)
      (errMix := errMix) (errMean := errMean)
      (directionSet := directionSet) (root := root) (α₀ := α₀) (k := k)
      hFinite hColumnProb hTargetProb hProfile hPureError
      hBackgroundTransfer hBackgroundError hMixed hMean hBudget

/-- Direct probability form of the deterministic one-column inclusion.

This is the `hColumnIncluded` event implication before scalar probability
families are named: the probability of the concrete favourable one-column
event is bounded by the probability of the concrete target upper-tail event.
The pure-spike transfer is closed by the imported mass-direction identity.  The
remaining deterministic inputs are exactly the visible pointwise blocks:
profile lower bound on the mass/cap event, background contribution lower bound,
mixed-remainder lower bound, and the mean/budget inequalities. -/
theorem lower_oneColumnFavorableEvent_prob_le_upperTailProb_of_closed_deterministic_blocks
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [MeasurableSpace (SampleMatrix p q σ)] [DecidableEq σ]
    {μ : ℕ → Measure (SampleMatrix p q σ)}
    {q₀ δ N M eps mean center errProfile errSpike τ errBg errMix errMean :
      ℝ → ℝ → ℕ → ℝ}
    {directionSet :
      ℝ → ℝ → ℕ → Set (EuclideanSpace ℂ (BipIndex p q))}
    {root : ℝ} {α₀ : σ} {k : ℕ}
    (hFinite : ∀ᶠ d in atTop, IsFiniteMeasure (μ d))
    (hProfile :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ R : ℝ, ∀ u : EuclideanSpace ℂ (BipIndex p q),
              R ∈ betaColumnIntervalSet (q₀ a slack d) (δ a slack d) →
              u ∈ directionSet a slack d →
              a ^ k - errProfile a slack d ≤
                columnDirectionSpikeProfile
                  (p := p) (q := q) (N a slack d) k R u)
    (hPureError :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            errProfile a slack d + 0 ≤ errSpike a slack d)
    (hBackground :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ X : SampleMatrix p q σ,
              sampleColumnComplementNormalized
                  (p := p) (q := q) (σ := σ) X α₀ ∈
                backgroundTypicalSet
                  (p := p) (q := q) (σ := σ)
                  (N a slack d) (M a slack d) (τ a slack d)
                  (center a slack d) k →
              center a slack d - errBg a slack d ≤
                columnBackgroundContribution
                  (p := p) (q := q) (σ := σ) (N a slack d) k X α₀)
    (hMixed :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ X : SampleMatrix p q σ,
              X ∈
                sphericalOneColumnFavorableEvent
                  (p := p) (q := q) (σ := σ)
                  α₀ (q₀ a slack d) (δ a slack d)
                  (directionSet a slack d)
                  (backgroundTypicalSet
                    (p := p) (q := q) (σ := σ)
                    (N a slack d) (M a slack d) (τ a slack d)
                    (center a slack d) k) →
              -errMix a slack d ≤
                columnMixedRemainder
                  (p := p) (q := q) (σ := σ) (N a slack d) k X α₀)
    (hMean :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            mean a slack d ≤ center a slack d + errMean a slack d)
    (hBudget :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            eps a slack d + errSpike a slack d + errBg a slack d +
              errMix a slack d + errMean a slack d ≤ a ^ k) :
    ∀ a : ℝ, root < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (μ d).real
              (sphericalOneColumnFavorableEvent
                (p := p) (q := q) (σ := σ)
                α₀ (q₀ a slack d) (δ a slack d)
                (directionSet a slack d)
                (backgroundTypicalSet (p := p) (q := q) (σ := σ)
                  (N a slack d) (M a slack d) (τ a slack d)
                  (center a slack d) k)) ≤
            (μ d).real
              (columnMomentUpperTailSet
                (p := p) (q := q) (σ := σ)
                (N a slack d) (eps a slack d) (mean a slack d) k) := by
  intro a ha slack hslack
  filter_upwards
    [hFinite, hProfile a ha slack hslack,
      hPureError a ha slack hslack, hBackground a ha slack hslack,
      hMixed a ha slack hslack, hMean a ha slack hslack,
      hBudget a ha slack hslack]
    with d hFinite_d hProfile_d hPureError_d hBackground_d hMixed_d
      hMean_d hBudget_d
  letI : IsFiniteMeasure (μ d) := hFinite_d
  refine measureReal_mono ?_ (h₂ := (measure_lt_top (μ d) _).ne)
  intro X hX
  have hSpike :
      a ^ k - errSpike a slack d ≤
        columnSpikeContribution
          (p := p) (q := q) (σ := σ) (N a slack d) k X α₀ :=
    (columnMassCapEvent_subset_pureSpikeLowerBoundSet_noInputTransfer
      (p := p) (q := q) (σ := σ)
      (α₀ := α₀) (N := N a slack d) (a := a)
      (errProfile := errProfile a slack d)
      (errSpike := errSpike a slack d)
      (q₀ := q₀ a slack d) (δ := δ a slack d)
      (k := k) (directionSet := directionSet a slack d)
      hProfile_d hPureError_d) ⟨hX.1, hX.2.1⟩
  exact
    column_spike_event_deviation_of_background_mixed
      (p := p) (q := q) (σ := σ)
      (N := N a slack d) (a := a) (eps := eps a slack d)
      (mean := mean a slack d) (center := center a slack d)
      (errSpike := errSpike a slack d) (errBg := errBg a slack d)
      (errMix := errMix a slack d) (errMean := errMean a slack d)
      (k := k) (X := X) (α₀ := α₀)
      hSpike (hBackground_d X hX.2.2) (hMixed_d X hX)
      hMean_d hBudget_d

set_option linter.unusedSectionVars false in
/-- A positive distinguished-column mass makes the total column direction
normalized.

This is the small deterministic bridge needed to state the spike-profile input
only on the directions that the one-column event can actually produce.  The
ambient projective cap itself is not a unit-sphere subtype, but after the Beta
mass interval lower endpoint is positive, `sampleColumnDirection` is a unit
vector. -/
theorem sampleColumnDirection_norm_eq_one_of_columnMass_pos
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    (X : SampleMatrix p q σ) (α₀ : σ)
    (hmass : 0 < sampleColumnMass (p := p) (q := q) (σ := σ) X α₀) :
    ‖sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀‖ = 1 := by
  let v : EuclideanSpace ℂ (BipIndex p q) :=
    sampleColumnVector (p := p) (q := q) (σ := σ) X α₀
  have hvnorm_pos : 0 < ‖v‖ := by
    have hsq : 0 < ‖v‖ ^ 2 := by
      simpa [sampleColumnMass, v,
        frobeniusNorm_sampleColumnPart_eq_norm_sampleColumnVector
          (p := p) (q := q) (σ := σ) X α₀] using hmass
    nlinarith [norm_nonneg v]
  have hnorm_inv : ‖((‖v‖)⁻¹ : ℂ)‖ = (‖v‖)⁻¹ := by
    simp
  unfold sampleColumnDirection
  change ‖((‖v‖)⁻¹ : ℂ) • v‖ = 1
  rw [norm_smul, hnorm_inv]
  field_simp [ne_of_gt hvnorm_pos]

/-- Unit-direction version of the deterministic one-column inclusion.

Compared with
`lower_oneColumnFavorableEvent_prob_le_upperTailProb_of_closed_deterministic_blocks`,
this removes the artificial need to prove the spike-profile estimate on every
ambient vector in the cap.  It is enough to prove it on unit vectors, because the
positive Beta lower endpoint forces the actual sampled column direction to have
norm `1`. -/
theorem lower_oneColumnFavorableEvent_prob_le_upperTailProb_of_closed_unitProfile
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [MeasurableSpace (SampleMatrix p q σ)] [DecidableEq σ]
    {μ : ℕ → Measure (SampleMatrix p q σ)}
    {q₀ δ N M eps mean center errProfile errSpike τ errBg errMix errMean :
      ℝ → ℝ → ℕ → ℝ}
    {directionSet :
      ℝ → ℝ → ℕ → Set (EuclideanSpace ℂ (BipIndex p q))}
    {root : ℝ} {α₀ : σ} {k : ℕ}
    (hFinite : ∀ᶠ d in atTop, IsFiniteMeasure (μ d))
    (hqpos :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, 0 < q₀ a slack d)
    (hUnitProfile :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ R : ℝ, ∀ u : EuclideanSpace ℂ (BipIndex p q),
              R ∈ betaColumnIntervalSet (q₀ a slack d) (δ a slack d) →
              u ∈ directionSet a slack d →
              ‖u‖ = 1 →
              a ^ k - errProfile a slack d ≤
                columnDirectionSpikeProfile
                  (p := p) (q := q) (N a slack d) k R u)
    (hPureError :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            errProfile a slack d + 0 ≤ errSpike a slack d)
    (hBackground :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ X : SampleMatrix p q σ,
              sampleColumnComplementNormalized
                  (p := p) (q := q) (σ := σ) X α₀ ∈
                backgroundTypicalSet
                  (p := p) (q := q) (σ := σ)
                  (N a slack d) (M a slack d) (τ a slack d)
                  (center a slack d) k →
              center a slack d - errBg a slack d ≤
                columnBackgroundContribution
                  (p := p) (q := q) (σ := σ) (N a slack d) k X α₀)
    (hMixed :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ X : SampleMatrix p q σ,
              X ∈
                sphericalOneColumnFavorableEvent
                  (p := p) (q := q) (σ := σ)
                  α₀ (q₀ a slack d) (δ a slack d)
                  (directionSet a slack d)
                  (backgroundTypicalSet
                    (p := p) (q := q) (σ := σ)
                    (N a slack d) (M a slack d) (τ a slack d)
                    (center a slack d) k) →
              -errMix a slack d ≤
                columnMixedRemainder
                  (p := p) (q := q) (σ := σ) (N a slack d) k X α₀)
    (hMean :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            mean a slack d ≤ center a slack d + errMean a slack d)
    (hBudget :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            eps a slack d + errSpike a slack d + errBg a slack d +
              errMix a slack d + errMean a slack d ≤ a ^ k) :
    ∀ a : ℝ, root < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (μ d).real
              (sphericalOneColumnFavorableEvent
                (p := p) (q := q) (σ := σ)
                α₀ (q₀ a slack d) (δ a slack d)
                (directionSet a slack d)
                (backgroundTypicalSet (p := p) (q := q) (σ := σ)
                  (N a slack d) (M a slack d) (τ a slack d)
                  (center a slack d) k)) ≤
            (μ d).real
              (columnMomentUpperTailSet
                (p := p) (q := q) (σ := σ)
                (N a slack d) (eps a slack d) (mean a slack d) k) := by
  intro a ha slack hslack
  filter_upwards
    [hFinite, hqpos a ha slack hslack, hUnitProfile a ha slack hslack,
      hPureError a ha slack hslack, hBackground a ha slack hslack,
      hMixed a ha slack hslack, hMean a ha slack hslack,
      hBudget a ha slack hslack]
    with d hFinite_d hqpos_d hProfile_d hPureError_d hBackground_d hMixed_d
      hMean_d hBudget_d
  letI : IsFiniteMeasure (μ d) := hFinite_d
  refine measureReal_mono ?_ (h₂ := (measure_lt_top (μ d) _).ne)
  intro X hX
  have hmass_lower :
      q₀ a slack d ≤ sampleColumnMass (p := p) (q := q) (σ := σ) X α₀ := by
    exact hX.1.1
  have hmass_pos :
      0 < sampleColumnMass (p := p) (q := q) (σ := σ) X α₀ :=
    lt_of_lt_of_le hqpos_d hmass_lower
  have hdir_unit :
      ‖sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀‖ = 1 :=
    sampleColumnDirection_norm_eq_one_of_columnMass_pos
      (p := p) (q := q) (σ := σ) X α₀ hmass_pos
  have hProfileX :
      a ^ k - errProfile a slack d ≤
        columnDirectionSpikeProfile
          (p := p) (q := q) (N a slack d) k
          (sampleColumnMass (p := p) (q := q) (σ := σ) X α₀)
          (sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀) :=
    hProfile_d
      (sampleColumnMass (p := p) (q := q) (σ := σ) X α₀)
      (sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀)
      hX.1 hX.2.1 hdir_unit
  have hTransfer :
      columnDirectionSpikeProfile
          (p := p) (q := q) (N a slack d) k
          (sampleColumnMass (p := p) (q := q) (σ := σ) X α₀)
          (sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀) - 0 ≤
        columnSpikeContribution
          (p := p) (q := q) (σ := σ) (N a slack d) k X α₀ :=
    columnSpikeContribution_transfer_noError
      (p := p) (q := q) (σ := σ) (α₀ := α₀)
      (N := N a slack d) (k := k) X
  have hSpike :
      a ^ k - errSpike a slack d ≤
        columnSpikeContribution
          (p := p) (q := q) (σ := σ) (N a slack d) k X α₀ := by
    linarith
  exact
    column_spike_event_deviation_of_background_mixed
      (p := p) (q := q) (σ := σ)
      (N := N a slack d) (a := a) (eps := eps a slack d)
      (mean := mean a slack d) (center := center a slack d)
      (errSpike := errSpike a slack d) (errBg := errBg a slack d)
      (errMix := errMix a slack d) (errMean := errMean a slack d)
      (k := k) (X := X) (α₀ := α₀)
      hSpike (hBackground_d X hX.2.2) (hMixed_d X hX)
      hMean_d hBudget_d

/-- Thin alias for the canonical deleted-background spherical decomposition law.

This wrapper is project-axiom-free by audit and delegates directly to
`CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence.sphericalLaw`.
The deleted-column transport needed for this statement is already closed by the
imported theorem stack. -/
theorem lower_decomposition_sphericalLaw_noProjectAxioms
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    [Nonempty p] [Nonempty q]
    {α₀ : σ}
    (hσ : 2 ≤ Fintype.card σ) :
    CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence
      (p := p) (q := q) (σ := σ)
      (_root_.PptFactorization.AppendixB.sphericalModelMeasure
        (p := p) (q := q) (σ := σ))
      α₀
      (columnDirectionPushforward
        (p := p) (q := q) (σ := σ)
        (_root_.PptFactorization.AppendixB.sphericalModelMeasure
          (p := p) (q := q) (σ := σ)) α₀) := by
  exact
    CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence.sphericalLaw
      (p := p) (q := q) (σ := σ) (α₀ := α₀) hσ

/-- Closed product decomposition for the concrete one-column favourable event.

This wrapper supplies the lower-bound pipeline's `hProduct` ingredient:
eventually,
`columnProb a slack d = betaProb a slack d * capProb a slack d *
backgroundProb a slack d`.  The deleted-background independence input is closed
by `CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence.sphericalLaw`;
the remaining assumptions only identify the scalar probability families with
the actual Beta interval, direction cap, deleted-background, and favourable
event probabilities, and assert measurability of the chosen events. -/
theorem lower_columnProb_eq_product_of_closed_deletedBackground_sphericalLaw
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    [Nonempty p] [Nonempty q]
    {α₀ : σ}
    {q₀ δ : ℝ → ℝ → ℕ → ℝ}
    {directionSet :
      ℝ → ℝ → ℕ → Set (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundSet : ℝ → ℝ → ℕ → Set (SampleMatrix p q σ)}
    {betaProb capProb backgroundProb columnProb : ℝ → ℝ → ℕ → ℝ}
    {root : ℝ}
    (hσ : 2 ≤ Fintype.card σ)
    (hDirectionMeas :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, MeasurableSet (directionSet a slack d))
    (hBackgroundMeas :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, MeasurableSet (backgroundSet a slack d))
    (hBetaProb :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            betaProb a slack d =
              (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ)).real
                (betaColumnIntervalSet (q₀ a slack d) (δ a slack d)))
    (hCapProb :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            capProb a slack d =
              (columnDirectionPushforward
                (p := p) (q := q) (σ := σ)
                (_root_.PptFactorization.AppendixB.sphericalModelMeasure
                  (p := p) (q := q) (σ := σ)) α₀).real
                (directionSet a slack d))
    (hBackgroundProb :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            backgroundProb a slack d =
              (deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀).real
                (backgroundSet a slack d))
    (hColumnProb :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            columnProb a slack d =
              (_root_.PptFactorization.AppendixB.sphericalModelMeasure
                (p := p) (q := q) (σ := σ)).real
                (sphericalOneColumnFavorableEvent
                  (p := p) (q := q) (σ := σ)
                  α₀ (q₀ a slack d) (δ a slack d)
                  (directionSet a slack d) (backgroundSet a slack d))) :
    ∀ a : ℝ, root < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          columnProb a slack d =
            betaProb a slack d * capProb a slack d *
              backgroundProb a slack d := by
  exact
    oneColumnProbabilityPipeline_hProduct_of_deletedBackgroundDecomposition
      (p := p) (q := q) (σ := σ)
      (μ := fun _ =>
        _root_.PptFactorization.AppendixB.sphericalModelMeasure
          (p := p) (q := q) (σ := σ))
      (α₀ := α₀)
      (directionLaw := fun _ _ _ =>
        columnDirectionPushforward
          (p := p) (q := q) (σ := σ)
          (_root_.PptFactorization.AppendixB.sphericalModelMeasure
            (p := p) (q := q) (σ := σ)) α₀)
      (q₀ := q₀) (δ := δ)
      (directionSet := directionSet) (backgroundSet := backgroundSet)
      (betaProb := betaProb) (capProb := capProb)
      (backgroundProb := backgroundProb) (columnProb := columnProb)
      (root := root)
      (fun _ _ _ _ =>
        Filter.Eventually.of_forall fun _ =>
          CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence.sphericalLaw
            (p := p) (q := q) (σ := σ) (α₀ := α₀) hσ)
      hDirectionMeas hBackgroundMeas hBetaProb hCapProb
      hBackgroundProb hColumnProb

/-- Direct canonical product decomposition for the one-column favourable event.

This is the product calculation before auxiliary scalar probability families
are introduced.  It closes `hProduct` for the canonical spherical model once
the direction and background events are measurable. -/
theorem lower_canonical_product_probability_of_closed_deletedBackground_sphericalLaw
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    [Nonempty p] [Nonempty q]
    {α₀ : σ}
    {q₀ δ : ℝ → ℝ → ℕ → ℝ}
    {directionSet :
      ℝ → ℝ → ℕ → Set (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundSet : ℝ → ℝ → ℕ → Set (SampleMatrix p q σ)}
    {root : ℝ}
    (hσ : 2 ≤ Fintype.card σ)
    (hDirectionMeas :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, MeasurableSet (directionSet a slack d))
    (hBackgroundMeas :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, MeasurableSet (backgroundSet a slack d)) :
    ∀ a : ℝ, root < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (_root_.PptFactorization.AppendixB.sphericalModelMeasure
            (p := p) (q := q) (σ := σ)).real
            (sphericalOneColumnFavorableEvent
              (p := p) (q := q) (σ := σ)
              α₀ (q₀ a slack d) (δ a slack d)
              (directionSet a slack d) (backgroundSet a slack d)) =
            (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ)).real
              (betaColumnIntervalSet (q₀ a slack d) (δ a slack d)) *
              (columnDirectionPushforward
                (p := p) (q := q) (σ := σ)
                (_root_.PptFactorization.AppendixB.sphericalModelMeasure
                  (p := p) (q := q) (σ := σ)) α₀).real
                (directionSet a slack d) *
                (deletedColumnBackgroundLaw
                  (p := p) (q := q) (σ := σ) α₀).real
                  (backgroundSet a slack d) := by
  intro a ha slack hslack
  filter_upwards
    [hDirectionMeas a ha slack hslack,
      hBackgroundMeas a ha slack hslack]
    with d hDirectionMeas_d hBackgroundMeas_d
  exact
    CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence.favorable_event_probability_eq
      (p := p) (q := q) (σ := σ)
      (I :=
        CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence.sphericalLaw
          (p := p) (q := q) (σ := σ) (α₀ := α₀) hσ)
      (q₀ := q₀ a slack d) (δ := δ a slack d)
      (directionSet := directionSet a slack d)
      (backgroundSet := backgroundSet a slack d)
      hDirectionMeas_d hBackgroundMeas_d

/-- The one-column Beta mass interval is measurable.

The canonical product wrapper below does not expose this as a separate
hypothesis because the mass event is handled internally by the closed
decomposition theorem.  This lemma records the closure explicitly for audits
and downstream event wiring. -/
theorem lower_measurableSet_betaColumnIntervalSet
    (q₀ δ : ℝ) :
    MeasurableSet (betaColumnIntervalSet q₀ δ) := by
  simp [betaColumnIntervalSet,
    (isClosed_Icc.measurableSet :
      MeasurableSet (Set.Icc q₀ (betaColumnIntervalUpper q₀ δ)))]

/-- Canonical product decomposition for concrete lower-bound product events,
with all event-measurability side conditions closed.

This targets
`lower_canonical_product_probability_of_closed_deletedBackground_sphericalLaw`.
The direction event is the ambient projective cap and the background event is
the concrete `backgroundTypicalSet`, so their measurability follows from the
closed measurable-set lemmas.  The Beta mass interval is also measurable by
`lower_measurableSet_betaColumnIntervalSet`, although the targeted product
wrapper keeps that fact internal rather than exposing it as an assumption. -/
theorem lower_canonical_product_probability_concreteEvents_of_closed_deletedBackground_sphericalLaw
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    [Nonempty p] [Nonempty q]
    {α₀ : σ}
    {q₀ δ radius N M τ center : ℝ → ℝ → ℕ → ℝ}
    {e : ℝ → ℝ → ℕ → EuclideanSpace ℂ (BipIndex p q)}
    {root : ℝ} {k : ℕ}
    (hσ : 2 ≤ Fintype.card σ) :
    ∀ a : ℝ, root < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (_root_.PptFactorization.AppendixB.sphericalModelMeasure
            (p := p) (q := q) (σ := σ)).real
            (sphericalOneColumnFavorableEvent
              (p := p) (q := q) (σ := σ)
              α₀ (q₀ a slack d) (δ a slack d)
              (ambientProjectiveCapSet
                (ι := BipIndex p q) (e a slack d) (radius a slack d))
              (backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (N a slack d) (M a slack d) (τ a slack d)
                (center a slack d) k)) =
            (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ)).real
              (betaColumnIntervalSet (q₀ a slack d) (δ a slack d)) *
              (columnDirectionPushforward
                (p := p) (q := q) (σ := σ)
                (_root_.PptFactorization.AppendixB.sphericalModelMeasure
                  (p := p) (q := q) (σ := σ)) α₀).real
                (ambientProjectiveCapSet
                  (ι := BipIndex p q) (e a slack d) (radius a slack d)) *
                (deletedColumnBackgroundLaw
                  (p := p) (q := q) (σ := σ) α₀).real
                  (backgroundTypicalSet
                    (p := p) (q := q) (σ := σ)
                    (N a slack d) (M a slack d) (τ a slack d)
                    (center a slack d) k) := by
  exact
    lower_canonical_product_probability_of_closed_deletedBackground_sphericalLaw
      (p := p) (q := q) (σ := σ)
      (α₀ := α₀)
      (q₀ := q₀) (δ := δ)
      (directionSet := fun a slack d =>
        ambientProjectiveCapSet
          (ι := BipIndex p q) (e a slack d) (radius a slack d))
      (backgroundSet := fun a slack d =>
        backgroundTypicalSet
          (p := p) (q := q) (σ := σ)
          (N a slack d) (M a slack d) (τ a slack d)
          (center a slack d) k)
      (root := root)
      hσ
      (fun a _ha slack _hslack =>
        Filter.Eventually.of_forall fun d =>
          measurableSet_ambientProjectiveCapSet
            (ι := BipIndex p q) (e a slack d) (radius a slack d))
      (fun a _ha slack _hslack =>
        Filter.Eventually.of_forall fun d =>
          measurableSet_backgroundTypicalSet
            (p := p) (q := q) (σ := σ)
            (N a slack d) (M a slack d) (τ a slack d)
            (center a slack d) k)

/-- Pointwise version of
`lower_canonical_product_probability_concreteEvents_of_closed_deletedBackground_sphericalLaw`.

This is often the most convenient form when the finite types are already fixed:
the mass interval, ambient cap, and background typical event all have their
measurability closed, so no measurability hypotheses remain. -/
theorem lower_canonical_product_probability_concreteEvents_pointwise_of_closed_deletedBackground_sphericalLaw
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    [Nonempty p] [Nonempty q]
    {α₀ : σ}
    {q₀ δ radius N M τ center : ℝ}
    {e : EuclideanSpace ℂ (BipIndex p q)}
    {k : ℕ}
    (hσ : 2 ≤ Fintype.card σ) :
    (_root_.PptFactorization.AppendixB.sphericalModelMeasure
      (p := p) (q := q) (σ := σ)).real
      (sphericalOneColumnFavorableEvent
        (p := p) (q := q) (σ := σ)
        α₀ q₀ δ
        (ambientProjectiveCapSet (ι := BipIndex p q) e radius)
        (backgroundTypicalSet
          (p := p) (q := q) (σ := σ) N M τ center k)) =
      (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ)).real
        (betaColumnIntervalSet q₀ δ) *
        (columnDirectionPushforward
          (p := p) (q := q) (σ := σ)
          (_root_.PptFactorization.AppendixB.sphericalModelMeasure
            (p := p) (q := q) (σ := σ)) α₀).real
          (ambientProjectiveCapSet (ι := BipIndex p q) e radius) *
          (deletedColumnBackgroundLaw
            (p := p) (q := q) (σ := σ) α₀).real
            (backgroundTypicalSet
              (p := p) (q := q) (σ := σ) N M τ center k) := by
  have hEventual :
      ∀ᶠ d in (atTop : Filter ℕ),
        (_root_.PptFactorization.AppendixB.sphericalModelMeasure
          (p := p) (q := q) (σ := σ)).real
          (sphericalOneColumnFavorableEvent
            (p := p) (q := q) (σ := σ)
            α₀ q₀ δ
            (ambientProjectiveCapSet (ι := BipIndex p q) e radius)
            (backgroundTypicalSet
              (p := p) (q := q) (σ := σ) N M τ center k)) =
          (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ)).real
            (betaColumnIntervalSet q₀ δ) *
            (columnDirectionPushforward
              (p := p) (q := q) (σ := σ)
              (_root_.PptFactorization.AppendixB.sphericalModelMeasure
                (p := p) (q := q) (σ := σ)) α₀).real
              (ambientProjectiveCapSet (ι := BipIndex p q) e radius) *
              (deletedColumnBackgroundLaw
                (p := p) (q := q) (σ := σ) α₀).real
                (backgroundTypicalSet
                  (p := p) (q := q) (σ := σ) N M τ center k) := by
    simpa using
      (lower_canonical_product_probability_concreteEvents_of_closed_deletedBackground_sphericalLaw
        (p := p) (q := q) (σ := σ) (α₀ := α₀)
        (q₀ := fun _ _ _ => q₀) (δ := fun _ _ _ => δ)
        (radius := fun _ _ _ => radius) (N := fun _ _ _ => N)
        (M := fun _ _ _ => M) (τ := fun _ _ _ => τ)
        (center := fun _ _ _ => center)
        (e := fun _ _ _ => e) (root := 0) (k := k) hσ
        1 (by norm_num) 1 (by norm_num))
  rcases (show
      ∃ n : ℕ, ∀ m : ℕ, n ≤ m →
        (_root_.PptFactorization.AppendixB.sphericalModelMeasure
          (p := p) (q := q) (σ := σ)).real
          (sphericalOneColumnFavorableEvent
            (p := p) (q := q) (σ := σ)
            α₀ q₀ δ
            (ambientProjectiveCapSet (ι := BipIndex p q) e radius)
            (backgroundTypicalSet
              (p := p) (q := q) (σ := σ) N M τ center k)) =
          (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ)).real
            (betaColumnIntervalSet q₀ δ) *
            (columnDirectionPushforward
              (p := p) (q := q) (σ := σ)
              (_root_.PptFactorization.AppendixB.sphericalModelMeasure
                (p := p) (q := q) (σ := σ)) α₀).real
              (ambientProjectiveCapSet (ι := BipIndex p q) e radius) *
              (deletedColumnBackgroundLaw
                (p := p) (q := q) (σ := σ) α₀).real
                (backgroundTypicalSet
                  (p := p) (q := q) (σ := σ) N M τ center k) from by
        simpa [Filter.eventually_atTop] using hEventual) with ⟨n, hn⟩
  exact hn n le_rfl

/-- Closed Beta interval lower bound for the distinguished-column mass.

This wrapper supplies the lower-bound pipeline's `hBeta` ingredient in the
canonical one-column coordinates.  The Beta law itself comes from the closed
deleted-background spherical decomposition; the remaining assumptions are the
interval conditions `0 < q₀`, `0 < δ`, `betaColumnIntervalUpper q₀ δ < 1`,
and the identification of `betaProb` with the actual column-mass interval
probability. -/
theorem lower_betaIntervalLowerBound_of_closed_deletedBackground_sphericalLaw
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    [Nonempty p] [Nonempty q]
    {α₀ : σ}
    {q₀ δ betaProb : ℝ → ℝ → ℕ → ℝ}
    {root : ℝ}
    (hσ : 2 ≤ Fintype.card σ)
    (hq :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, 0 < q₀ a slack d)
    (hδ :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, 0 < δ a slack d)
    (hupper :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            betaColumnIntervalUpper (q₀ a slack d) (δ a slack d) < 1)
    (hBetaProb :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            betaProb a slack d =
              columnMassIntervalProbability
                (p := p) (q := q) (σ := σ)
                (_root_.PptFactorization.AppendixB.sphericalModelMeasure
                  (p := p) (q := q) (σ := σ))
                α₀ (q₀ a slack d) (δ a slack d)) :
    ∀ a : ℝ, root < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          BetaColumnIntervalLowerBound
            (betaProb a slack d)
            (columnMassBetaMainShape (p := p) (q := q))
            (columnMassBetaSampleCount (σ := σ))
            (q₀ a slack d) (δ a slack d) := by
  exact
    oneColumnProbabilityPipeline_hBeta_of_deletedBackgroundDecomposition
      (p := p) (q := q) (σ := σ)
      (μ := fun _ =>
        _root_.PptFactorization.AppendixB.sphericalModelMeasure
          (p := p) (q := q) (σ := σ))
      (α₀ := α₀)
      (directionLaw := fun _ _ _ =>
        columnDirectionPushforward
          (p := p) (q := q) (σ := σ)
          (_root_.PptFactorization.AppendixB.sphericalModelMeasure
            (p := p) (q := q) (σ := σ)) α₀)
      (q₀ := q₀) (δ := δ) (betaProb := betaProb) (root := root)
      hσ
      (fun _ _ _ _ =>
        Filter.Eventually.of_forall fun _ =>
          CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence.sphericalLaw
            (p := p) (q := q) (σ := σ) (α₀ := α₀) hσ)
      hq hδ hupper hBetaProb

/-- Closed Beta interval lower bound with the actual lower-bound spike scale.

This is the `hBeta` shape used by the scalar-limits lower-bound constructor:
the interval center is
`betaColumnSpikeScale (N d : ℝ) (spikeSpeed k d) a`, and the interval radius
is `δ a slack d`.  The canonical Beta parameters are related to the pipeline
families `N` and `s` by the explicit shape assumptions `hNshape` and
`hsshape`; no asymptotic scalar facts are hidden here. -/
theorem lower_betaIntervalLowerBound_spikeScale_of_closed_deletedBackground_sphericalLaw
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    [Nonempty p] [Nonempty q]
    {α₀ : σ}
    {N s : ℕ → ℕ} {δ betaProb : ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hσ : 2 ≤ Fintype.card σ)
    (hNshape :
      ∀ᶠ d in atTop, N d = columnMassBetaMainShape (p := p) (q := q))
    (hsshape :
      ∀ᶠ d in atTop, s d = columnMassBetaSampleCount (σ := σ))
    (hq :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            0 < betaColumnSpikeScale (N d : ℝ) (spikeSpeed k d) a)
    (hδ :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, 0 < δ a slack d)
    (hupper :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            betaColumnIntervalUpper
              (betaColumnSpikeScale (N d : ℝ) (spikeSpeed k d) a)
              (δ a slack d) < 1)
    (hBetaProb :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            betaProb a slack d =
              columnMassIntervalProbability
                (p := p) (q := q) (σ := σ)
                (_root_.PptFactorization.AppendixB.sphericalModelMeasure
                  (p := p) (q := q) (σ := σ))
                α₀
                (betaColumnSpikeScale (N d : ℝ) (spikeSpeed k d) a)
                (δ a slack d)) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          BetaColumnIntervalLowerBound
            (betaProb a slack d) (N d) (s d)
            (betaColumnSpikeScale (N d : ℝ) (spikeSpeed k d) a)
            (δ a slack d) := by
  have hBase :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            BetaColumnIntervalLowerBound
              (betaProb a slack d)
              (columnMassBetaMainShape (p := p) (q := q))
              (columnMassBetaSampleCount (σ := σ))
              (betaColumnSpikeScale (N d : ℝ) (spikeSpeed k d) a)
              (δ a slack d) :=
    lower_betaIntervalLowerBound_of_closed_deletedBackground_sphericalLaw
      (p := p) (q := q) (σ := σ)
      (α₀ := α₀)
      (q₀ := fun a _slack d =>
        betaColumnSpikeScale (N d : ℝ) (spikeSpeed k d) a)
      (δ := δ) (betaProb := betaProb)
      (root := spikeRoot k ε)
      hσ hq hδ hupper hBetaProb
  intro a ha slack hslack
  filter_upwards [hBase a ha slack hslack, hNshape, hsshape]
    with d hBeta_d hN_d hs_d
  simpa [hN_d, hs_d] using hBeta_d

/-- Canonical Beta interval lower bound with no column-mass identification
hypothesis.

This is the `hBeta` probability estimate for the canonical Beta factor
appearing in the deleted-background product formula.  The only remaining
conditions are the interval assumptions `0 < q₀`, `0 < δ`, and upper endpoint
below `1`. -/
theorem lower_betaIntervalLowerBound_canonicalProbability
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    [Nonempty p] [Nonempty q]
    {q₀ δ : ℝ → ℝ → ℕ → ℝ}
    {root : ℝ}
    (hσ : 2 ≤ Fintype.card σ)
    (hq :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, 0 < q₀ a slack d)
    (hδ :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, 0 < δ a slack d)
    (hupper :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            betaColumnIntervalUpper (q₀ a slack d) (δ a slack d) < 1) :
    ∀ a : ℝ, root < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          BetaColumnIntervalLowerBound
            ((canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ)).real
              (betaColumnIntervalSet (q₀ a slack d) (δ a slack d)))
            (columnMassBetaMainShape (p := p) (q := q))
            (columnMassBetaSampleCount (σ := σ))
            (q₀ a slack d) (δ a slack d) := by
  intro a ha slack hslack
  filter_upwards
    [hq a ha slack hslack, hδ a ha slack hslack,
      hupper a ha slack hslack]
    with d hq_d hδ_d hupper_d
  simpa [betaColumnMeasureIntervalProbability] using
    (canonicalIntegerBetaColumnMeasure
      (p := p) (q := q) (σ := σ) hσ).interval_lower
        (q₀ := q₀ a slack d) (δ := δ a slack d)
        hq_d hδ_d hupper_d

/-- Pointwise canonical Beta lower bound for a single finite model.

This packages the closed Beta interval estimate without any asymptotic
filtering.  It is useful for the varying concrete model, where the finite
types are `Fin d` and the shape identities are closed pointwise rather than by
eventual fixed-type hypotheses. -/
theorem lower_betaIntervalLowerBound_canonicalProbability_pointwise
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    [Nonempty p] [Nonempty q]
    {N s : ℕ} {q₀ δ : ℝ}
    (hσ : 2 ≤ Fintype.card σ)
    (hNshape : N = columnMassBetaMainShape (p := p) (q := q))
    (hsshape : s = columnMassBetaSampleCount (σ := σ))
    (hq : 0 < q₀) (hδ : 0 < δ)
    (hupper : betaColumnIntervalUpper q₀ δ < 1) :
    BetaColumnIntervalLowerBound
      ((canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ)).real
        (betaColumnIntervalSet q₀ δ))
      N s q₀ δ := by
  simpa [hNshape, hsshape, betaColumnMeasureIntervalProbability] using
    (canonicalIntegerBetaColumnMeasure
      (p := p) (q := q) (σ := σ) hσ).interval_lower
        (q₀ := q₀) (δ := δ) hq hδ hupper

/-- Canonical Beta lower bound at the lower-bound spike scale.

This is the direct canonical-probability version of `hBeta` for the
scalar-limits constructor.  The shape assumptions only rewrite the abstract
pipeline dimensions `N` and `s` to the canonical Beta parameters. -/
theorem lower_betaIntervalLowerBound_spikeScale_canonicalProbability
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    [Nonempty p] [Nonempty q]
    {N s : ℕ → ℕ} {δ : ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hσ : 2 ≤ Fintype.card σ)
    (hNshape :
      ∀ᶠ d in atTop, N d = columnMassBetaMainShape (p := p) (q := q))
    (hsshape :
      ∀ᶠ d in atTop, s d = columnMassBetaSampleCount (σ := σ))
    (hq :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            0 < betaColumnSpikeScale (N d : ℝ) (spikeSpeed k d) a)
    (hδ :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, 0 < δ a slack d)
    (hupper :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            betaColumnIntervalUpper
              (betaColumnSpikeScale (N d : ℝ) (spikeSpeed k d) a)
              (δ a slack d) < 1) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          BetaColumnIntervalLowerBound
            ((canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ)).real
              (betaColumnIntervalSet
                (betaColumnSpikeScale (N d : ℝ) (spikeSpeed k d) a)
                (δ a slack d)))
            (N d) (s d)
            (betaColumnSpikeScale (N d : ℝ) (spikeSpeed k d) a)
            (δ a slack d) := by
  have hBase :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            BetaColumnIntervalLowerBound
              ((canonicalColumnMassBetaMeasure
                (p := p) (q := q) (σ := σ)).real
                (betaColumnIntervalSet
                  (betaColumnSpikeScale (N d : ℝ) (spikeSpeed k d) a)
                  (δ a slack d)))
              (columnMassBetaMainShape (p := p) (q := q))
              (columnMassBetaSampleCount (σ := σ))
              (betaColumnSpikeScale (N d : ℝ) (spikeSpeed k d) a)
              (δ a slack d) :=
    lower_betaIntervalLowerBound_canonicalProbability
      (p := p) (q := q) (σ := σ)
      (q₀ := fun a _slack d =>
        betaColumnSpikeScale (N d : ℝ) (spikeSpeed k d) a)
      (δ := δ) (root := spikeRoot k ε)
      hσ hq hδ hupper
  intro a ha slack hslack
  filter_upwards [hBase a ha slack hslack, hNshape, hsshape]
    with d hBeta_d hN_d hs_d
  simpa [hN_d, hs_d] using hBeta_d

/-- Closed projective cap lower bound for the concrete column direction.

This wrapper supplies the lower-bound pipeline's `hCap` ingredient.  The
deleted-background decomposition is closed by the spherical law, while the
directional Haar/projective-overlap law, unit-vector condition, cap probability
identification, and dimension-shape identification for `Ncap` remain explicit
parameters. -/
theorem lower_projectiveCapLowerBound_of_closed_deletedBackground_sphericalLaw
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    [Nonempty p] [Nonempty q]
    {α₀ : σ}
    {Ncap : ℕ → ℕ}
    {e : ℝ → ℝ → ℕ → EuclideanSpace ℂ (BipIndex p q)}
    {capProb : ℝ → ℝ → ℕ → ℝ}
    {root : ℝ}
    (hσ : 2 ≤ Fintype.card σ)
    (hNcapShape :
      ∀ᶠ d in atTop, Ncap d = columnMassBetaMainShape (p := p) (q := q))
    (hDirectionBeta :
      AmbientHaarProjectiveOverlapBetaLaw
        (ι := BipIndex p q)
        (columnDirectionPushforward
          (p := p) (q := q) (σ := σ)
          (_root_.PptFactorization.AppendixB.sphericalModelMeasure
            (p := p) (q := q) (σ := σ)) α₀))
    (hUnit :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, ‖e a slack d‖ = 1)
    (hCapProb :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            capProb a slack d =
              columnDirectionCapProbability
                (p := p) (q := q) (σ := σ)
                (_root_.PptFactorization.AppendixB.sphericalModelMeasure
                  (p := p) (q := q) (σ := σ))
                α₀ (e a slack d) (1 / (Ncap d : ℝ))) :
    ∀ a : ℝ, root < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ProjectiveCapProbabilityLowerBound
            (capProb a slack d) (Ncap d) (1 / (Ncap d : ℝ)) := by
  have hCapProbCanonical :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            capProb a slack d =
              columnDirectionCapProbability
                (p := p) (q := q) (σ := σ)
                (_root_.PptFactorization.AppendixB.sphericalModelMeasure
                  (p := p) (q := q) (σ := σ))
                α₀ (e a slack d)
                (1 / (columnMassBetaMainShape (p := p) (q := q) : ℝ)) := by
    intro a ha slack hslack
    filter_upwards [hCapProb a ha slack hslack, hNcapShape]
      with d hCapProb_d hNcap_d
    simpa [hNcap_d] using hCapProb_d
  have hBase :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ProjectiveCapProbabilityLowerBound
              (capProb a slack d)
              (columnMassBetaMainShape (p := p) (q := q))
              (1 / (columnMassBetaMainShape (p := p) (q := q) : ℝ)) :=
    oneColumnProbabilityPipeline_hCap_of_deletedBackgroundDecomposition
      (p := p) (q := q) (σ := σ)
      (μ := fun _ =>
        _root_.PptFactorization.AppendixB.sphericalModelMeasure
          (p := p) (q := q) (σ := σ))
      (α₀ := α₀)
      (directionLaw := fun _ _ _ =>
        columnDirectionPushforward
          (p := p) (q := q) (σ := σ)
          (_root_.PptFactorization.AppendixB.sphericalModelMeasure
            (p := p) (q := q) (σ := σ)) α₀)
      (e := e) (capProb := capProb) (root := root)
      (fun _ _ _ _ =>
        Filter.Eventually.of_forall fun _ =>
          CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence.sphericalLaw
            (p := p) (q := q) (σ := σ) (α₀ := α₀) hσ)
      (fun _ _ _ _ => Filter.Eventually.of_forall fun _ => hDirectionBeta)
      hUnit hCapProbCanonical
  intro a ha slack hslack
  filter_upwards [hBase a ha slack hslack, hNcapShape]
    with d hCap_d hNcap_d
  simpa [hNcap_d] using hCap_d

/-- Haar/projective overlap law for the actual spherical column direction,
derived from the surface cone-coordinate formula.

This removes the direction-law plumbing from `hCap`; the geometric
cone-coordinate identity itself remains an explicit assumption. -/
theorem lower_columnDirectionAmbientHaarProjectiveOverlapBetaLaw_of_surfaceCone
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    [Nonempty p] [Nonempty q]
    {α₀ : σ}
    (hσ : 2 ≤ Fintype.card σ)
    (hN2 : 2 ≤ Fintype.card (BipIndex p q))
    (hCoord : SurfaceProjectiveCapConeCoordinateFormula (BipIndex p q)) :
    AmbientHaarProjectiveOverlapBetaLaw
      (ι := BipIndex p q)
      (columnDirectionPushforward
        (p := p) (q := q) (σ := σ)
        (_root_.PptFactorization.AppendixB.sphericalModelMeasure
          (p := p) (q := q) (σ := σ)) α₀) := by
  have hSurface :
      HaarProjectiveOverlapBetaLaw
        (ι := BipIndex p q) (surfaceMeasure (BipIndex p q)) :=
    surfaceHaarProjectiveOverlapBetaLaw_of_coneCoordinateFormula
      (ι := BipIndex p q) hN2 hCoord
  have hAmbient :
      AmbientHaarProjectiveOverlapBetaLaw
        (ι := BipIndex p q) (surfaceMeasureAmbient (BipIndex p q)) :=
    hSurface.toAmbient
  have hDir :
      columnDirectionPushforward
          (p := p) (q := q) (σ := σ)
          (_root_.PptFactorization.AppendixB.sphericalModelMeasure
            (p := p) (q := q) (σ := σ)) α₀ =
        surfaceMeasureAmbient (BipIndex p q) :=
    columnDirectionPushforward_sphericalModelMeasure_eq_surfaceMeasureAmbient
      (p := p) (q := q) (σ := σ) α₀ hσ
  simpa [hDir] using hAmbient

/-- Direct canonical cap lower bound from the surface cone-coordinate formula.

The cap probability is the actual column-direction cap probability under the
closed spherical model.  The remaining explicit assumptions are the
cone-coordinate formula, the unit centre, and the dimension-shape rewrite for
`Ncap`. -/
theorem lower_projectiveCapLowerBound_canonicalProbability_of_surfaceCone
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    [Nonempty p] [Nonempty q]
    {α₀ : σ}
    {Ncap : ℕ → ℕ}
    {e : ℝ → ℝ → ℕ → EuclideanSpace ℂ (BipIndex p q)}
    {root : ℝ}
    (hσ : 2 ≤ Fintype.card σ)
    (hN2 : 2 ≤ Fintype.card (BipIndex p q))
    (hCoord : SurfaceProjectiveCapConeCoordinateFormula (BipIndex p q))
    (hNcapShape :
      ∀ᶠ d in atTop, Ncap d = columnMassBetaMainShape (p := p) (q := q))
    (hUnit :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, ‖e a slack d‖ = 1) :
    ∀ a : ℝ, root < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ProjectiveCapProbabilityLowerBound
            (columnDirectionCapProbability
              (p := p) (q := q) (σ := σ)
              (_root_.PptFactorization.AppendixB.sphericalModelMeasure
                (p := p) (q := q) (σ := σ))
              α₀ (e a slack d) (1 / (Ncap d : ℝ)))
            (Ncap d) (1 / (Ncap d : ℝ)) := by
  exact
    lower_projectiveCapLowerBound_of_closed_deletedBackground_sphericalLaw
      (p := p) (q := q) (σ := σ)
      (α₀ := α₀) (Ncap := Ncap) (e := e)
      (capProb := fun a slack d =>
        columnDirectionCapProbability
          (p := p) (q := q) (σ := σ)
          (_root_.PptFactorization.AppendixB.sphericalModelMeasure
            (p := p) (q := q) (σ := σ))
          α₀ (e a slack d) (1 / (Ncap d : ℝ)))
      (root := root)
      hσ hNcapShape
      (lower_columnDirectionAmbientHaarProjectiveOverlapBetaLaw_of_surfaceCone
        (p := p) (q := q) (σ := σ) (α₀ := α₀)
        hσ hN2 hCoord)
      hUnit
      (by
        intro a _ha slack _hslack
        exact Filter.Eventually.of_forall fun _ => rfl)

/-- Closed background half-mass input for the lower-bound pipeline.

This wrapper supplies the `hBackgroundHalf` shape:
`1 / 2 ≤ backgroundProb a slack d` eventually.  The one-column
deleted-background independence is closed internally by the spherical law; the
remaining assumptions are the deleted-column bad-set estimates, their
union-bound budget, and the identification of `backgroundProb` with the actual
deleted-background typicality probability. -/
theorem lower_backgroundProb_ge_half_of_closed_deletedBackground_sphericalLaw
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    [Nonempty p] [Nonempty q]
    {α₀ : σ}
    {backgroundProb : ℝ → ℝ → ℕ → ℝ}
    {N M τ mean bMoment bSample bGamma : ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hσ : 2 ≤ Fintype.card σ)
    (hBounds :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          DeletedColumnBackgroundBadSetBounds
            (p := p) (q := q) (σ := σ)
            α₀ (N a slack d) (M a slack d) (τ a slack d)
            (mean a slack d) (bMoment a slack d)
            (bSample a slack d) (bGamma a slack d) k)
    (hBad :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          bMoment a slack d + bSample a slack d + bGamma a slack d ≤ 1 / 2)
    (hBackgroundProb :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          backgroundProb a slack d =
            columnBackgroundTypicalProbability
              (p := p) (q := q) (σ := σ)
              (_root_.PptFactorization.AppendixB.sphericalModelMeasure
                (p := p) (q := q) (σ := σ))
              α₀ (N a slack d) (M a slack d)
              (τ a slack d) (mean a slack d) k) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop, (1 / 2 : ℝ) ≤ backgroundProb a slack d := by
  exact
    eventual_hBackgroundHalf_of_deleted_background_bad_bounds
      (p := p) (q := q) (σ := σ)
      (μ := fun _ =>
        _root_.PptFactorization.AppendixB.sphericalModelMeasure
          (p := p) (q := q) (σ := σ))
      (α₀ := α₀)
      (directionLaw := fun _ =>
        columnDirectionPushforward
          (p := p) (q := q) (σ := σ)
          (_root_.PptFactorization.AppendixB.sphericalModelMeasure
            (p := p) (q := q) (σ := σ)) α₀)
      (backgroundProb := backgroundProb)
      (N := N) (M := M) (τ := τ) (mean := mean)
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (k := k) (ε := ε)
      (Filter.Eventually.of_forall fun _ =>
        CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence.sphericalLaw
          (p := p) (q := q) (σ := σ) (α₀ := α₀) hσ)
      hBounds hBad hBackgroundProb

/-- Direct background half-mass statement for the actual deleted-background
typicality probability.

This closes the `DeletedColumnBackgroundBadSetBounds` packaging from the three
visible bad-event probability estimates under the deleted-background law and
the scalar `≤ 1/2` union-bound budget.  The bad-event estimates themselves
remain genuine probabilistic inputs; this wrapper closes the measurability,
deleted-background probability, and one-column spherical-law plumbing. -/
theorem lower_backgroundTypicalProbability_ge_half_of_closed_deletedBackground_sphericalLaw
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    [Nonempty p] [Nonempty q]
    {α₀ : σ}
    {N M τ mean bMoment bSample bGamma : ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hσ : 2 ≤ Fintype.card σ)
    (hMoment :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          (deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀).real
            (backgroundMomentBadSet
              (p := p) (q := q) (σ := σ)
              (N a slack d) (τ a slack d) (mean a slack d) k) ≤
            bMoment a slack d)
    (hSample :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          (deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀).real
            (backgroundSampleOpNormBadSet
              (p := p) (q := q) (σ := σ)
              (N a slack d) (M a slack d)) ≤
            bSample a slack d)
    (hGamma :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          (deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀).real
            (backgroundGammaOpNormBadSet
              (p := p) (q := q) (σ := σ)
              (N a slack d) (M a slack d)) ≤
            bGamma a slack d)
    (hBad :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          bMoment a slack d + bSample a slack d + bGamma a slack d ≤ 1 / 2) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (1 / 2 : ℝ) ≤
            columnBackgroundTypicalProbability
              (p := p) (q := q) (σ := σ)
              (_root_.PptFactorization.AppendixB.sphericalModelMeasure
                (p := p) (q := q) (σ := σ))
              α₀ (N a slack d) (M a slack d)
              (τ a slack d) (mean a slack d) k := by
  have hBounds :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          DeletedColumnBackgroundBadSetBounds
            (p := p) (q := q) (σ := σ)
            α₀ (N a slack d) (M a slack d) (τ a slack d)
            (mean a slack d) (bMoment a slack d)
            (bSample a slack d) (bGamma a slack d) k := by
    intro a slack
    filter_upwards [hMoment a slack, hSample a slack, hGamma a slack]
      with d hMoment_d hSample_d hGamma_d
    exact
      DeletedColumnBackgroundBadSetBounds.of_deleted_background_bad_bounds_noInput_probability
        (p := p) (q := q) (σ := σ) (α₀ := α₀)
        (N := N a slack d) (M := M a slack d)
        (τ := τ a slack d) (mean := mean a slack d)
        (bMoment := bMoment a slack d)
        (bSample := bSample a slack d)
        (bGamma := bGamma a slack d)
        (k := k)
        hσ
        (measurableSet_backgroundTypicalSet
          (p := p) (q := q) (σ := σ)
          (N a slack d) (M a slack d) (τ a slack d)
          (mean a slack d) k)
        hMoment_d hSample_d hGamma_d
  exact
    lower_backgroundProb_ge_half_of_closed_deletedBackground_sphericalLaw
      (p := p) (q := q) (σ := σ) (α₀ := α₀)
      (backgroundProb := fun a slack d =>
        columnBackgroundTypicalProbability
          (p := p) (q := q) (σ := σ)
          (_root_.PptFactorization.AppendixB.sphericalModelMeasure
            (p := p) (q := q) (σ := σ))
          α₀ (N a slack d) (M a slack d)
          (τ a slack d) (mean a slack d) k)
      (N := N) (M := M) (τ := τ) (mean := mean)
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (k := k) (ε := ε)
      hσ hBounds hBad
      (by
        intro a slack
        exact Filter.Eventually.of_forall fun _ => rfl)

/-- Thin alias for the scalar-limits constructor of the spike lower-bound
input.

This wrapper is project-axiom-free by audit and delegates directly to
`SpikeLowerBoundInput.of_oneColumn_probability_pipeline_scalar_limits`.
The Beta × directions and one-column product-decomposition packaging used by
the underlying theorem are already closed in the imported stack.

This is not an unconditional scalar/asymptotic theorem: all remaining analytic
inputs are explicit parameters, including `hColumnIncluded`, `hProduct`,
`hBeta`, `hCap`, `hBackgroundHalf`, `hDeltaLimit`, `hEntropyLimit`,
`hOneMinusLimit`, and `hCapCostLimit`.

The scalar/asymptotic checklist consumed by this wrapper is exactly:
`hNpos`, `hDeltaPos`, `hUpper`, `hDeltaLimit`, `hEntropyLimit`,
`hOneMinusLimit`, `hNcap`, and `hCapCostLimit`.  These are concrete
model-instantiation obligations, not project axioms and not proved by this
closure alias. -/
theorem lower_spikeInput_of_oneColumn_scalarLimits
    {targetProb : ℕ → ℝ}
    {betaProb capProb backgroundProb columnProb : ℝ → ℝ → ℕ → ℝ}
    {N s Ncap : ℕ → ℕ} {δ : ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {lam ε : ℝ}
    (hk : 0 < k) (hlam : 0 < lam) (hε : 0 < ε)
    (hColumnIncluded :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, columnProb a slack d ≤ targetProb d)
    (hProduct :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            columnProb a slack d =
              betaProb a slack d * capProb a slack d * backgroundProb a slack d)
    (hBeta :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            BetaColumnIntervalLowerBound
              (betaProb a slack d) (N d) (s d)
              (betaColumnSpikeScale (N d : ℝ) (spikeSpeed k d) a)
              (δ a slack d))
    (hNpos :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, 0 < (N d : ℝ))
    (hDeltaPos :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, 0 < δ a slack d)
    (hUpper :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            betaColumnIntervalUpper
              (betaColumnSpikeScale (N d : ℝ) (spikeSpeed k d) a)
              (δ a slack d) < 1)
    (hDeltaLimit :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          Tendsto
            (fun d => (-Real.log (δ a slack d)) / spikeSpeed k d)
            atTop (nhds 0))
    (hEntropyLimit :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          Tendsto
            (fun d =>
              ((N d : ℝ) *
                (2 * Real.log (N d : ℝ) -
                  Real.log (a * spikeSpeed k d))) / spikeSpeed k d)
            atTop (nhds 0))
    (hOneMinusLimit :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          Tendsto
            (fun d =>
              ((((betaColumnOtherShape (N d) (s d) - 1 : ℕ) : ℝ) *
                  betaColumnIntervalUpper
                    (betaColumnSpikeScale (N d : ℝ) (spikeSpeed k d) a)
                    (δ a slack d) /
                    (1 - betaColumnIntervalUpper
                      (betaColumnSpikeScale (N d : ℝ) (spikeSpeed k d) a)
                      (δ a slack d))) /
                spikeSpeed k d))
            atTop (nhds (lam * a)))
    (hNcap : ∀ᶠ d in atTop, 1 ≤ Ncap d)
    (hCap :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ProjectiveCapProbabilityLowerBound
              (capProb a slack d) (Ncap d) (1 / (Ncap d : ℝ)))
    (hCapCostLimit :
      Tendsto
        (fun d => capNLogNCost 2 (Ncap d : ℝ) / spikeSpeed k d)
        atTop (nhds 0))
    (hBackgroundHalf :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, (1 / 2 : ℝ) ≤ backgroundProb a slack d) :
    SpikeLowerBoundInput targetProb k lam ε := by
  exact
    SpikeLowerBoundInput.of_oneColumn_probability_pipeline_scalar_limits
      (targetProb := targetProb)
      (betaProb := betaProb) (capProb := capProb)
      (backgroundProb := backgroundProb) (columnProb := columnProb)
      (N := N) (s := s) (Ncap := Ncap) (δ := δ)
      (k := k) (lam := lam) (ε := ε)
      hk hlam hε hColumnIncluded hProduct hBeta hNpos hDeltaPos hUpper
      hDeltaLimit hEntropyLimit hOneMinusLimit hNcap hCap hCapCostLimit
      hBackgroundHalf

/-- Thin alias for the scalar-limits eventual lower exponent.

This wrapper is project-axiom-free by audit and delegates directly to
`eventual_log_over_spikeSpeed_lower_of_oneColumn_probability_pipeline_scalar_limits`.
It packages the already-closed lower-bound machinery into the final eventual
lower exponent.

The scalar/asymptotic inputs remain exactly the explicit theorem parameters,
not axioms and not unconditional conclusions. -/
theorem lower_eventual_log_over_spikeSpeed
    {targetProb : ℕ → ℝ}
    {betaProb capProb backgroundProb columnProb : ℝ → ℝ → ℕ → ℝ}
    {N s Ncap : ℕ → ℕ} {δ : ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {lam ε : ℝ}
    (hk : 0 < k) (hlam : 0 < lam) (hε : 0 < ε)
    (hColumnIncluded :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, columnProb a slack d ≤ targetProb d)
    (hProduct :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            columnProb a slack d =
              betaProb a slack d * capProb a slack d * backgroundProb a slack d)
    (hBeta :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            BetaColumnIntervalLowerBound
              (betaProb a slack d) (N d) (s d)
              (betaColumnSpikeScale (N d : ℝ) (spikeSpeed k d) a)
              (δ a slack d))
    (hNpos :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, 0 < (N d : ℝ))
    (hDeltaPos :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, 0 < δ a slack d)
    (hUpper :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            betaColumnIntervalUpper
              (betaColumnSpikeScale (N d : ℝ) (spikeSpeed k d) a)
              (δ a slack d) < 1)
    (hDeltaLimit :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          Tendsto
            (fun d => (-Real.log (δ a slack d)) / spikeSpeed k d)
            atTop (nhds 0))
    (hEntropyLimit :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          Tendsto
            (fun d =>
              ((N d : ℝ) *
                (2 * Real.log (N d : ℝ) -
                  Real.log (a * spikeSpeed k d))) / spikeSpeed k d)
            atTop (nhds 0))
    (hOneMinusLimit :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          Tendsto
            (fun d =>
              ((((betaColumnOtherShape (N d) (s d) - 1 : ℕ) : ℝ) *
                  betaColumnIntervalUpper
                    (betaColumnSpikeScale (N d : ℝ) (spikeSpeed k d) a)
                    (δ a slack d) /
                    (1 - betaColumnIntervalUpper
                      (betaColumnSpikeScale (N d : ℝ) (spikeSpeed k d) a)
                      (δ a slack d))) /
                spikeSpeed k d))
            atTop (nhds (lam * a)))
    (hNcap : ∀ᶠ d in atTop, 1 ≤ Ncap d)
    (hCap :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ProjectiveCapProbabilityLowerBound
              (capProb a slack d) (Ncap d) (1 / (Ncap d : ℝ)))
    (hCapCostLimit :
      Tendsto
        (fun d => capNLogNCost 2 (Ncap d : ℝ) / spikeSpeed k d)
        atTop (nhds 0))
    (hBackgroundHalf :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, (1 / 2 : ℝ) ≤ backgroundProb a slack d) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k lam ε - η ≤
          Real.log (targetProb d) / spikeSpeed k d := by
  exact
    eventual_log_over_spikeSpeed_lower_of_oneColumn_probability_pipeline_scalar_limits
      (targetProb := targetProb)
      (betaProb := betaProb) (capProb := capProb)
      (backgroundProb := backgroundProb) (columnProb := columnProb)
      (N := N) (s := s) (Ncap := Ncap) (δ := δ)
      (k := k) (lam := lam) (ε := ε)
      hk hlam hε hColumnIncluded hProduct hBeta hNpos hDeltaPos hUpper
      hDeltaLimit hEntropyLimit hOneMinusLimit hNcap hCap hCapCostLimit
      hBackgroundHalf

/-- Thin alias for the eventual lower exponent from an already-built spike
input.

This wrapper is project-axiom-free by audit and delegates directly to
`SpikeLowerBoundInput.eventual_log_over_spikeSpeed_lower`.  Once the
`SpikeLowerBoundInput` parameter is supplied, the conclusion is pure
lower-bound bookkeeping; construction of that input is not hidden here. -/
theorem lower_eventual_log_over_spikeSpeed_from_input
    {p : ℕ → ℝ} {k : ℕ} {lam ε : ℝ}
    (I : SpikeLowerBoundInput p k lam ε) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k lam ε - η ≤
          Real.log (p d) / spikeSpeed k d := by
  exact SpikeLowerBoundInput.eventual_log_over_spikeSpeed_lower I

/-! ## Concrete scalar supplier for the lower endpoint -/

/-- Concrete lower-bound state dimension for the actual `Fin d × Fin d`
matrix model. -/
def lowerConcreteN (d : ℕ) : ℕ :=
  d ^ 2

/-- Concrete lower-bound sample count supplied by a balanced concrete
random-matrix regime. -/
def lowerConcreteS
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (d : ℕ) : ℕ :=
  R.sample d

/-- Concrete projective-cap ambient dimension for the actual `Fin d × Fin d`
matrix model. -/
def lowerConcreteNcap (d : ℕ) : ℕ :=
  d ^ 2

/-- Slowly shrinking relative width for the concrete lower Beta interval.

The choice `δ_d = d⁻¹` is small enough not to change the leading
one-minus-Beta exponent and large enough that `-log δ_d` is negligible at the
spike speed. -/
noncomputable def lowerConcreteDelta (_a _slack : ℝ) (d : ℕ) : ℝ :=
  (d : ℝ)⁻¹

/-- Canonical lower-side common operator-norm threshold for the deleted
background.

The initial tempting choice `lowerConcreteN d = d²` is not the right common
threshold for the concrete Gaussian/Wishart probability inputs: the canonical
Gamma threshold includes the sample dimension and the bipartite dimension, so
in the balanced model it is generally of larger order.  This definition mirrors
the upper-side choice, but for the deleted-column background law.  The `d = 0`
or empty-sample branch is irrelevant for the eventual lower pipeline and keeps
the definition total. -/
noncomputable def lowerConcreteM
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (_a _slack : ℝ) (d : ℕ) : ℝ :=
  if hs : 0 < R.sample d then
    max
      (_root_.PptFactorization.AppendixB.concreteSampleOpNormThreshold
        (p := Fin d) (q := Fin d)
        (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d))))
      (_root_.PptFactorization.AppendixB.concreteRhoGammaOpNormThreshold
        (p := Fin d) (q := Fin d)
        (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d))))
  else 0

/-! ### Public concrete choices for the bundled lower endpoint -/

/-- Concrete lower deviation threshold sequence: the fixed target `ε`. -/
noncomputable def lowerConcreteEps (ε : ℝ) (_d : ℕ) : ℝ :=
  ε

/-- Concrete background-typical tolerance for the lower endpoint. -/
noncomputable def lowerConcreteTau (a slack : ℝ) (d : ℕ) : ℝ :=
  lowerConcreteDelta a slack d

/-- Concrete pure-profile error budget. -/
noncomputable def lowerConcreteProfileError
    (_k : ℕ) (_ε : ℝ) (a slack : ℝ) (d : ℕ) : ℝ :=
  lowerConcreteDelta a slack d

/-- Concrete background scale-transfer error budget. -/
noncomputable def lowerConcreteScaleError
    (_R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (_k : ℕ) (_ε : ℝ) (a slack : ℝ) (d : ℕ) : ℝ :=
  lowerConcreteDelta a slack d

/-- Concrete mixed-remainder lower error budget. -/
noncomputable def lowerConcreteMixedError
    (_R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (_k : ℕ) (_ε : ℝ) (a slack : ℝ) (d : ℕ) : ℝ :=
  lowerConcreteDelta a slack d

/-- Correct deleted-background centering for the lower endpoint: the spherical
mean of the background moment functional on the deleted-column model. -/
noncomputable def lowerConcreteDeletedBackgroundMean
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k d : ℕ) : ℝ :=
  if hs : 0 < R.sample d then
    ∫ X : SampleMatrix (Fin d) (Fin d)
        (DeletedColumn (⟨0, hs⟩ : Fin (R.sample d))),
      backgroundMomentValue
        (p := Fin d) (q := Fin d)
        (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
        (lowerConcreteN d) k X
      ∂_root_.PptFactorization.AppendixB.sphericalModelMeasure
        (p := Fin d) (q := Fin d)
        (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
  else 0

/-- Concrete moment bad-set budget used by the bundled lower endpoint.

This is a scalar budget choice, not a proof of the background moment
concentration estimate.  The endpoint below still requires the explicit
`hMoment` hypothesis that the model actually satisfies this bound. -/
noncomputable def lowerConcreteMomentBound
    (_R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (_k : ℕ) (_a _slack : ℝ) (d : ℕ) : ℝ :=
  Real.exp (-(d : ℝ))

@[simp] theorem lowerConcreteEps_eq (ε : ℝ) (d : ℕ) :
    lowerConcreteEps ε d = ε := rfl

@[simp] theorem lowerConcreteTau_eq (a slack : ℝ) (d : ℕ) :
    lowerConcreteTau a slack d = lowerConcreteDelta a slack d := rfl

@[simp] theorem lowerConcreteProfileError_eq
    (k : ℕ) (ε a slack : ℝ) (d : ℕ) :
    lowerConcreteProfileError k ε a slack d = lowerConcreteDelta a slack d := rfl

@[simp] theorem lowerConcreteScaleError_eq
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (ε a slack : ℝ) (d : ℕ) :
    lowerConcreteScaleError R k ε a slack d = lowerConcreteDelta a slack d := rfl

@[simp] theorem lowerConcreteMixedError_eq
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (ε a slack : ℝ) (d : ℕ) :
    lowerConcreteMixedError R k ε a slack d = lowerConcreteDelta a slack d := rfl

@[simp] theorem lowerConcreteMomentBound_eq
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (a slack : ℝ) (d : ℕ) :
    lowerConcreteMomentBound R k a slack d = Real.exp (-(d : ℝ)) := rfl

/-- The concrete lower common threshold dominates the deleted-column sample
operator threshold whenever the selected column exists. -/
theorem lowerConcreteM_ge_concreteSampleOpNormThreshold
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (a slack : ℝ) {d : ℕ} (hs : 0 < R.sample d) :
    _root_.PptFactorization.AppendixB.concreteSampleOpNormThreshold
        (p := Fin d) (q := Fin d)
        (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d))) ≤
      lowerConcreteM R a slack d := by
  simp [lowerConcreteM, hs]

/-- The concrete lower common threshold dominates the deleted-column Gamma
operator threshold whenever the selected column exists. -/
theorem lowerConcreteM_ge_concreteRhoGammaOpNormThreshold
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (a slack : ℝ) {d : ℕ} (hs : 0 < R.sample d) :
    _root_.PptFactorization.AppendixB.concreteRhoGammaOpNormThreshold
        (p := Fin d) (q := Fin d)
        (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d))) ≤
      lowerConcreteM R a slack d := by
  simp [lowerConcreteM, hs]

/-- Lower-side monotonicity for the normalized sample-operator good event. -/
theorem lower_normalizedSampleOpNormEvent_subset_of_threshold_le
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b) :
    _root_.PptFactorization.HighProbabilityBounds.normalizedSampleOpNormEvent
        (p := p) (q := q) (σ := σ) a d ⊆
      _root_.PptFactorization.HighProbabilityBounds.normalizedSampleOpNormEvent
        (p := p) (q := q) (σ := σ) b d := by
  intro ω hω
  exact le_trans hω (div_le_div_of_nonneg_right hab hd.le)

/-- Complement form of lower-side threshold monotonicity for the normalized
sample event. -/
theorem lower_normalizedSampleOpNormEvent_compl_subset_of_threshold_le
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b) :
    (_root_.PptFactorization.HighProbabilityBounds.normalizedSampleOpNormEvent
        (p := p) (q := q) (σ := σ) b d)ᶜ ⊆
      (_root_.PptFactorization.HighProbabilityBounds.normalizedSampleOpNormEvent
        (p := p) (q := q) (σ := σ) a d)ᶜ := by
  intro ω hω hsmall
  exact hω
    (lower_normalizedSampleOpNormEvent_subset_of_threshold_le
      (p := p) (q := q) (σ := σ) hd hab hsmall)

/-- Lower-side monotonicity for the normalized partial-transpose good event. -/
theorem lower_normalizedRhoGammaOpNormEvent_subset_of_threshold_le
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {a b d : ℝ} (hab : a ≤ b) :
    _root_.PptFactorization.HighProbabilityBounds.normalizedRhoGammaOpNormEvent
        (p := p) (q := q) (σ := σ) a d ⊆
      _root_.PptFactorization.HighProbabilityBounds.normalizedRhoGammaOpNormEvent
        (p := p) (q := q) (σ := σ) b d := by
  intro ω hω
  exact le_trans hω (div_le_div_of_nonneg_right hab (sq_nonneg d))

/-- Complement form of lower-side threshold monotonicity for the normalized
partial-transpose event. -/
theorem lower_normalizedRhoGammaOpNormEvent_compl_subset_of_threshold_le
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {a b d : ℝ} (hab : a ≤ b) :
    (_root_.PptFactorization.HighProbabilityBounds.normalizedRhoGammaOpNormEvent
        (p := p) (q := q) (σ := σ) b d)ᶜ ⊆
      (_root_.PptFactorization.HighProbabilityBounds.normalizedRhoGammaOpNormEvent
        (p := p) (q := q) (σ := σ) a d)ᶜ := by
  intro ω hω hsmall
  exact hω
    (lower_normalizedRhoGammaOpNormEvent_subset_of_threshold_le
      (p := p) (q := q) (σ := σ) hab hsmall)

/-- If the concrete sample count is at least two, then deleting one selected
column leaves a nonempty deleted-column sample type. -/
theorem lower_deletedColumn_nonempty_of_two_le_sample
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {d : ℕ} (hs2 : 2 ≤ R.sample d) (hs : 0 < R.sample d) :
    Nonempty (DeletedColumn (⟨0, hs⟩ : Fin (R.sample d))) := by
  have h1 : 1 < R.sample d := by omega
  refine ⟨⟨(⟨1, h1⟩ : Fin (R.sample d)), ?_⟩⟩
  intro h
  have hval : (1 : ℕ) = 0 := by
    exact congrArg Fin.val h
  norm_num at hval

/-- The deleted-column sample dimension is exactly the original sample count
minus the distinguished column. -/
theorem lower_sampleDimension_deletedColumn_eq_sample_sub_one
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {d : ℕ} (hs : 0 < R.sample d) :
    _root_.PptFactorization.HighProbabilityBounds.sampleDimension
        (DeletedColumn (⟨0, hs⟩ : Fin (R.sample d))) =
      (R.sample d - 1 : ℕ) := by
  simp [_root_.PptFactorization.HighProbabilityBounds.sampleDimension]

/-- The deleted-column sample dimension is at least one once the original
sample count is at least two. -/
theorem lower_sampleDimension_deletedColumn_ge_one
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {d : ℕ} (hs2 : 2 ≤ R.sample d) (hs : 0 < R.sample d) :
    1 ≤
      _root_.PptFactorization.HighProbabilityBounds.sampleDimension
        (DeletedColumn (⟨0, hs⟩ : Fin (R.sample d))) := by
  have hsub : 1 ≤ R.sample d - 1 := by omega
  rw [lower_sampleDimension_deletedColumn_eq_sample_sub_one R hs]
  exact_mod_cast hsub

/-- The bipartite dimension of the concrete lower matrix space is `d²`. -/
theorem lower_bipartiteDimension_fin_fin_eq_sq (d : ℕ) :
    _root_.PptFactorization.HighProbabilityBounds.bipartiteDimension
        (Fin d) (Fin d) =
      (d : ℝ) ^ 2 := by
  simp [_root_.PptFactorization.HighProbabilityBounds.bipartiteDimension,
    _root_.PptFactorization.RandomMatrixModel.BipIndex, pow_two]

/-- Pointwise application of the concrete Gaussian/Wishart probability bridge
to the lower deleted-column background type.

This is deliberately before the common-threshold monotonicity step: the two
tails are stated at the canonical concrete sample and Gamma thresholds supplied
by `AppendixBConcreteBridge`. -/
theorem lower_concrete_deletedColumn_canonical_operator_tails_pointwise
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {d : ℕ} (hd : 0 < d) (hs2 : 2 ≤ R.sample d)
    (hs : 0 < R.sample d)
    (hLarge : 12 * Real.log 2 ≤ (d : ℝ) ^ 2) :
    (_root_.PptFactorization.HighProbabilityBounds.gaussianMeasure
        (Fin d) (Fin d)
        (DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
        ((_root_.PptFactorization.HighProbabilityBounds.normalizedSampleOpNormEvent
          (p := Fin d) (q := Fin d)
          (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
          (_root_.PptFactorization.AppendixB.concreteSampleOpNormThreshold
            (p := Fin d) (q := Fin d)
            (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d))))
          (d : ℝ))ᶜ) ≤
      Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)) ∧
    (_root_.PptFactorization.HighProbabilityBounds.gaussianMeasure
        (Fin d) (Fin d)
        (DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
        ((_root_.PptFactorization.HighProbabilityBounds.normalizedRhoGammaOpNormEvent
          (p := Fin d) (q := Fin d)
          (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
          (_root_.PptFactorization.AppendixB.concreteRhoGammaOpNormThreshold
            (p := Fin d) (q := Fin d)
            (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d))))
          (d : ℝ))ᶜ) ≤
      Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hs1 :
      1 ≤
        _root_.PptFactorization.HighProbabilityBounds.sampleDimension
          (DeletedColumn (⟨0, hs⟩ : Fin (R.sample d))) :=
    lower_sampleDimension_deletedColumn_ge_one R hs2 hs
  have hDim :
      _root_.PptFactorization.HighProbabilityBounds.bipartiteDimension
          (Fin d) (Fin d) =
        (d : ℝ) ^ 2 :=
    lower_bipartiteDimension_fin_fin_eq_sq d
  exact
    _root_.PptFactorization.AppendixB.concrete_normalized_operator_norm_probability_inputs
      (p := Fin d) (q := Fin d)
      (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
      (d := (d : ℝ)) hdR hs1 hDim hLarge

/-- Pointwise concrete deleted-background operator tails at the lower common
threshold `lowerConcreteM`.

This is the lower-side analogue of the upper closure's pointwise common
threshold lemma.  The Gaussian/Wishart probability bridge gives the two tails
at the canonical deleted-column thresholds; `lowerConcreteM` is their maximum,
so monotonicity transfers the bounds to the single threshold used by the lower
background typical set. -/
theorem lower_concrete_commonThreshold_operator_tails_pointwise
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {d : ℕ} (hd : 0 < d) (hs2 : 2 ≤ R.sample d)
    (hs : 0 < R.sample d)
    (hLarge : 12 * Real.log 2 ≤ (d : ℝ) ^ 2)
    (a slack : ℝ) :
    (_root_.PptFactorization.HighProbabilityBounds.gaussianMeasure
        (Fin d) (Fin d)
        (DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
        ((_root_.PptFactorization.HighProbabilityBounds.normalizedSampleOpNormEvent
          (p := Fin d) (q := Fin d)
          (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
          (lowerConcreteM R a slack d) (d : ℝ))ᶜ) ≤
      Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)) ∧
    (_root_.PptFactorization.HighProbabilityBounds.gaussianMeasure
        (Fin d) (Fin d)
        (DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
        ((_root_.PptFactorization.HighProbabilityBounds.normalizedRhoGammaOpNormEvent
          (p := Fin d) (q := Fin d)
          (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
          (lowerConcreteM R a slack d) (d : ℝ))ᶜ) ≤
      Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  haveI :
      IsProbabilityMeasure
        (_root_.PptFactorization.HighProbabilityBounds.gaussianMeasure
          (Fin d) (Fin d)
          (DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))) := by
    rw [_root_.PptFactorization.HighProbabilityBounds.gaussianMeasure_eq]
    infer_instance
  have hprob :=
    lower_concrete_deletedColumn_canonical_operator_tails_pointwise
      (R := R) hd hs2 hs hLarge
  constructor
  · have hsubset :
        ((_root_.PptFactorization.HighProbabilityBounds.normalizedSampleOpNormEvent
          (p := Fin d) (q := Fin d)
          (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
          (lowerConcreteM R a slack d) (d : ℝ))ᶜ) ⊆
          ((_root_.PptFactorization.HighProbabilityBounds.normalizedSampleOpNormEvent
            (p := Fin d) (q := Fin d)
            (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
            (_root_.PptFactorization.AppendixB.concreteSampleOpNormThreshold
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d))))
            (d : ℝ))ᶜ) :=
      lower_normalizedSampleOpNormEvent_compl_subset_of_threshold_le
        (p := Fin d) (q := Fin d)
        (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
        hdR
        (lowerConcreteM_ge_concreteSampleOpNormThreshold R a slack hs)
    have hmono :
        (_root_.PptFactorization.HighProbabilityBounds.gaussianMeasure
          (Fin d) (Fin d)
          (DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
          ((_root_.PptFactorization.HighProbabilityBounds.normalizedSampleOpNormEvent
            (p := Fin d) (q := Fin d)
            (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
            (lowerConcreteM R a slack d) (d : ℝ))ᶜ) ≤
        (_root_.PptFactorization.HighProbabilityBounds.gaussianMeasure
          (Fin d) (Fin d)
          (DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
          ((_root_.PptFactorization.HighProbabilityBounds.normalizedSampleOpNormEvent
            (p := Fin d) (q := Fin d)
            (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
            (_root_.PptFactorization.AppendixB.concreteSampleOpNormThreshold
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d))))
            (d : ℝ))ᶜ) :=
      measureReal_mono
        (h₂ := (measure_lt_top
          (_root_.PptFactorization.HighProbabilityBounds.gaussianMeasure
            (Fin d) (Fin d)
            (DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))) _).ne)
        hsubset
    exact le_trans hmono hprob.1
  · have hsubset :
        ((_root_.PptFactorization.HighProbabilityBounds.normalizedRhoGammaOpNormEvent
          (p := Fin d) (q := Fin d)
          (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
          (lowerConcreteM R a slack d) (d : ℝ))ᶜ) ⊆
          ((_root_.PptFactorization.HighProbabilityBounds.normalizedRhoGammaOpNormEvent
            (p := Fin d) (q := Fin d)
            (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
            (_root_.PptFactorization.AppendixB.concreteRhoGammaOpNormThreshold
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d))))
            (d : ℝ))ᶜ) :=
      lower_normalizedRhoGammaOpNormEvent_compl_subset_of_threshold_le
        (p := Fin d) (q := Fin d)
        (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
        (lowerConcreteM_ge_concreteRhoGammaOpNormThreshold R a slack hs)
    have hmono :
        (_root_.PptFactorization.HighProbabilityBounds.gaussianMeasure
          (Fin d) (Fin d)
          (DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
          ((_root_.PptFactorization.HighProbabilityBounds.normalizedRhoGammaOpNormEvent
            (p := Fin d) (q := Fin d)
            (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
            (lowerConcreteM R a slack d) (d : ℝ))ᶜ) ≤
        (_root_.PptFactorization.HighProbabilityBounds.gaussianMeasure
          (Fin d) (Fin d)
          (DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
          ((_root_.PptFactorization.HighProbabilityBounds.normalizedRhoGammaOpNormEvent
            (p := Fin d) (q := Fin d)
            (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
            (_root_.PptFactorization.AppendixB.concreteRhoGammaOpNormThreshold
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d))))
            (d : ℝ))ᶜ) :=
      measureReal_mono
        (h₂ := (measure_lt_top
          (_root_.PptFactorization.HighProbabilityBounds.gaussianMeasure
            (Fin d) (Fin d)
            (DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))) _).ne)
        hsubset
    exact le_trans hmono hprob.2

/-- Canonical lower-side sample operator tail budget.

This is the same paper-shaped exponential budget used by the existing upper
closure after the Gaussian/Wishart tails are collapsed to the `d²` scale. -/
noncomputable def lowerConcreteSampleTailBound
    (_a _slack : ℝ) (d : ℕ) : ℝ :=
  Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2))

/-- Canonical lower-side Gamma operator tail budget. -/
noncomputable def lowerConcreteGammaTailBound
    (_a _slack : ℝ) (d : ℕ) : ℝ :=
  Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2))

@[simp] theorem lowerConcreteSampleTailBound_eq
    (a slack : ℝ) (d : ℕ) :
    lowerConcreteSampleTailBound a slack d =
      Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)) := rfl

@[simp] theorem lowerConcreteGammaTailBound_eq
    (a slack : ℝ) (d : ℕ) :
    lowerConcreteGammaTailBound a slack d =
      Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)) := rfl

/-- Eventually the scalar dimension square is large enough for the paper-form
Gaussian/Wishart tail collapse. -/
theorem lower_eventually_large_dimension_sq :
    ∀ᶠ d : ℕ in atTop, 12 * Real.log 2 ≤ (d : ℝ) ^ 2 := by
  have ht :
      Tendsto (fun d : ℕ => (d : ℝ) ^ 2) atTop atTop := by
    simpa using
      ((tendsto_rpow_atTop (show (0 : ℝ) < 2 by norm_num)).comp
        (tendsto_natCast_atTop_atTop :
          Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop))
  exact ht.eventually (eventually_ge_atTop (12 * Real.log 2))

/-- The paper-form operator-tail budget `exp(-d²/12)` is eventually smaller
than any fixed positive scalar. -/
theorem lower_exp_tail_eventually_le
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ d : ℕ in atTop,
      Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)) ≤ η := by
  by_cases hηlt : η < 1
  · have ht :
        Tendsto (fun d : ℕ => (d : ℝ) ^ 2) atTop atTop := by
      simpa using
        ((tendsto_rpow_atTop (show (0 : ℝ) < 2 by norm_num)).comp
          (tendsto_natCast_atTop_atTop :
            Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop))
    have hlarge :
        ∀ᶠ d : ℕ in atTop,
          12 * (-Real.log η) ≤ (d : ℝ) ^ 2 :=
      ht.eventually (eventually_ge_atTop (12 * (-Real.log η)))
    filter_upwards [hlarge] with d hlarge_d
    have hle :
        -((1 / 12 : ℝ) * (d : ℝ) ^ 2) ≤ Real.log η := by
      nlinarith
    calc
      Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2))
          ≤ Real.exp (Real.log η) := Real.exp_le_exp.mpr hle
      _ = η := Real.exp_log hη
  · have hge : 1 ≤ η := le_of_not_gt hηlt
    filter_upwards [eventually_gt_atTop 0] with d hd
    have hle0 : -((1 / 12 : ℝ) * (d : ℝ) ^ 2) ≤ 0 := by
      have hnonneg : 0 ≤ (1 / 12 : ℝ) * (d : ℝ) ^ 2 := by positivity
      linarith
    have hexp_le_one :
        Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)) ≤ 1 := by
      simpa only [Real.exp_zero] using
        (Real.exp_le_exp.mpr hle0 :
          Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)) ≤ Real.exp 0)
    exact le_trans hexp_le_one hge

/-- The canonical lower sample-tail budget is eventually arbitrarily small. -/
theorem lower_concrete_hSampleSmall_commonThreshold :
    ∀ a : ℝ, ∀ slack : ℝ,
      ∀ η : ℝ, 0 < η →
        ∀ᶠ d in atTop,
          lowerConcreteSampleTailBound a slack d ≤ η := by
  intro _a _slack η hη
  simpa [lowerConcreteSampleTailBound] using
    (lower_exp_tail_eventually_le (η := η) hη)

/-- The canonical lower Gamma-tail budget is eventually arbitrarily small. -/
theorem lower_concrete_hGammaSmall_commonThreshold :
    ∀ a : ℝ, ∀ slack : ℝ,
      ∀ η : ℝ, 0 < η →
        ∀ᶠ d in atTop,
          lowerConcreteGammaTailBound a slack d ≤ η := by
  intro _a _slack η hη
  simpa [lowerConcreteGammaTailBound] using
    (lower_exp_tail_eventually_le (η := η) hη)

@[simp] theorem lowerConcreteN_eq (d : ℕ) :
    lowerConcreteN d = d ^ 2 := rfl

@[simp] theorem lowerConcreteS_eq
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (d : ℕ) :
    lowerConcreteS R d = R.sample d := rfl

@[simp] theorem lowerConcreteNcap_eq (d : ℕ) :
    lowerConcreteNcap d = d ^ 2 := rfl

@[simp] theorem lowerConcreteDelta_eq (a slack : ℝ) (d : ℕ) :
    lowerConcreteDelta a slack d = (d : ℝ)⁻¹ := rfl

/-! ### Concrete probability families for the varying `Fin d` model -/

/-- Canonical spike direction for the concrete lower-bound model.

For every eventual positive dimension this is the coordinate unit vector at
the distinguished matrix entry `(0, 0)` in `Fin d × Fin d`.  The `d = 0`
branch is irrelevant for the atTop lower-bound pipeline but keeps the
definition total. -/
noncomputable def lowerConcreteCanonicalDirection
    (x : ℝ × ℝ × ℕ) :
    EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)) :=
  if hd : 0 < x.2.2 then
    coordinateUnitVector
      (ι := BipIndex (Fin x.2.2) (Fin x.2.2))
      ((⟨0, hd⟩ : Fin x.2.2), (⟨0, hd⟩ : Fin x.2.2))
  else 0

/-- The canonical lower-bound spike direction is eventually unit norm.

This closes the standalone `hUnit` input for endpoints specialized to
`lowerConcreteCanonicalDirection`.  It does not prove any spike-profile
estimate on a cap; those profile assumptions remain visible separately. -/
theorem lower_concrete_hUnit_canonicalDirection
    {k : ℕ} {ε : ℝ} :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ‖lowerConcreteCanonicalDirection (a, slack, d)‖ = 1 := by
  intro a _ha slack _hslack
  filter_upwards [eventually_gt_atTop 0] with d hd
  simpa [lowerConcreteCanonicalDirection, hd] using
    (norm_coordinateUnitVector
      (ι := BipIndex (Fin d) (Fin d))
      ((⟨0, hd⟩ : Fin d), (⟨0, hd⟩ : Fin d)))

/-- Concrete lower-bound target probability for the actual `Fin d × Fin d`
spherical matrix model. -/
noncomputable def lowerConcreteTargetProb
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps mean : ℕ → ℝ) (k : ℕ) : ℕ → ℝ :=
  fun d =>
    (_root_.PptFactorization.AppendixB.sphericalModelMeasure
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))).real
      (columnMomentUpperTailSet
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        (lowerConcreteN d) (eps d) (mean d) k)

/-- Concrete cap event for the selected lower-bound spike direction. -/
noncomputable def lowerConcreteDirectionCapSet
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)))
    (a slack : ℝ) (d : ℕ) :
    Set (EuclideanSpace ℂ (BipIndex (Fin d) (Fin d))) :=
  ambientProjectiveCapSet
    (ι := BipIndex (Fin d) (Fin d))
    (e (a, slack, d)) (1 / (lowerConcreteNcap d : ℝ))

/-- Concrete one-column Beta interval probability for the varying model. -/
noncomputable def lowerConcreteBetaProb
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) : ℝ → ℝ → ℕ → ℝ :=
  fun a slack d =>
    (canonicalColumnMassBetaMeasure
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))).real
      (betaColumnIntervalSet
        (betaColumnSpikeScale
          (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
        (lowerConcreteDelta a slack d))

/-- Concrete projective cap probability for the varying model.

When the sample index is empty the distinguished column is not available; the
definition returns `0` on that irrelevant branch.  The balanced regime supplies
sample positivity eventually, and all closure theorems below work on that
eventual branch. -/
noncomputable def lowerConcreteCapProb
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2))) :
    ℝ → ℝ → ℕ → ℝ :=
  fun a slack d =>
    if hs : 0 < R.sample d then
      columnDirectionCapProbability
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        (_root_.PptFactorization.AppendixB.sphericalModelMeasure
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)))
        ⟨0, hs⟩ (e (a, slack, d)) (1 / (lowerConcreteNcap d : ℝ))
    else 0

/-- Concrete deleted-background typicality probability for the varying model.

This is the background marginal probability appearing in the product
decomposition, not a new probabilistic axiom. -/
noncomputable def lowerConcreteBackgroundProb
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (M τ center : ℝ → ℝ → ℕ → ℝ) (k : ℕ) :
    ℝ → ℝ → ℕ → ℝ :=
  fun a slack d =>
    if hs : 0 < R.sample d then
      (deletedColumnBackgroundLaw
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        ⟨0, hs⟩).real
        (backgroundTypicalSet
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (lowerConcreteN d) (M a slack d) (τ a slack d)
          (center a slack d) k)
    else 0

/-- Concrete one-column favourable-event probability for the varying model. -/
noncomputable def lowerConcreteColumnProb
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)))
    (M τ center : ℝ → ℝ → ℕ → ℝ) (k : ℕ) :
    ℝ → ℝ → ℕ → ℝ :=
  fun a slack d =>
    if hs : 0 < R.sample d then
      (_root_.PptFactorization.AppendixB.sphericalModelMeasure
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))).real
        (sphericalOneColumnFavorableEvent
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          ⟨0, hs⟩
          (betaColumnSpikeScale
            (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
          (lowerConcreteDelta a slack d)
          (lowerConcreteDirectionCapSet e a slack d)
          (backgroundTypicalSet
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            (lowerConcreteN d) (M a slack d) (τ a slack d)
            (center a slack d) k))
    else 0

/-- The concrete Beta interval center is eventually positive. -/
theorem lower_concrete_hBetaScalePos
    {k : ℕ} (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          0 < betaColumnSpikeScale
            (lowerConcreteN d : ℝ) (spikeSpeed k d) a := by
  intro a ha _slack _hslack
  filter_upwards [eventually_gt_atTop 0] with d hd
  have ha_pos : 0 < a := lt_trans (spikeRoot_pos hk hε) ha
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hNpos : 0 < (lowerConcreteN d : ℝ) := by
    simp [lowerConcreteN, pow_two, mul_pos hdR hdR]
  have hspeed : 0 < spikeSpeed k d := by
    simp [spikeSpeed, Real.rpow_pos_of_pos hdR]
  unfold betaColumnSpikeScale
  exact div_pos (mul_pos ha_pos hspeed) (sq_pos_of_pos hNpos)

/-- Concrete model supplier for the lower pipeline's `hNpos` scalar
assumption. -/
theorem lower_concrete_hNpos {k : ℕ} {ε : ℝ} :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop, 0 < (lowerConcreteN d : ℝ) := by
  intro _a _ha _slack _hslack
  filter_upwards [eventually_gt_atTop 0] with d hd
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  simp [lowerConcreteN, pow_two, mul_pos hdR hdR]

/-- Concrete model supplier for the lower pipeline's `hDeltaPos` scalar
assumption. -/
theorem lower_concrete_hDeltaPos {k : ℕ} {ε : ℝ} :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop, 0 < lowerConcreteDelta a slack d := by
  intro a _ha slack _hslack
  filter_upwards [eventually_gt_atTop 0] with d hd
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  simp [lowerConcreteDelta, inv_pos.mpr hdR]

/-- Concrete model supplier for the lower pipeline's `hNcap` scalar
assumption. -/
theorem lower_concrete_hNcap :
    ∀ᶠ d in atTop, 1 ≤ lowerConcreteNcap d := by
  filter_upwards [eventually_ge_atTop 1] with d hd
  simp [lowerConcreteNcap]
  nlinarith [sq_nonneg (d : ℤ)]

/-- The concrete distinguished-column spike mass scale tends to zero for
`k > 1`.

This is the scalar fact behind the upper-endpoint check
`(1 + δ_d) q_d < 1`; for `k = 1`, the center would be order one, so the
actual lower-deviation model requires this visible stronger moment-order
assumption. -/
theorem lower_concrete_betaColumnSpikeScale_tendsto_zero
    {k : ℕ} (hk : 1 < k) {a : ℝ} :
    Tendsto
      (fun d =>
        betaColumnSpikeScale
          (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
      atTop (nhds 0) := by
  have hkRpos : 0 < (k : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have hgap_pos : 0 < (2 : ℝ) - (2 : ℝ) / (k : ℝ) := by
    have hlt : (2 : ℝ) / (k : ℝ) < 2 := by
      rw [div_lt_iff₀ hkRpos]
      nlinarith [show (1 : ℝ) < (k : ℝ) by exact_mod_cast hk]
    linarith
  have hgap_atTop :
      Tendsto
        (fun d : ℕ => (d : ℝ) ^ ((2 : ℝ) - (2 : ℝ) / (k : ℝ)))
        atTop atTop :=
    (tendsto_rpow_atTop hgap_pos).comp tendsto_natCast_atTop_atTop
  have hbase :
      Tendsto
        (fun d : ℕ => a / ((d : ℝ) ^ ((2 : ℝ) - (2 : ℝ) / (k : ℝ))))
        atTop (nhds 0) :=
    hgap_atTop.const_div_atTop a
  refine hbase.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with d hd
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hpow_add :
      (d : ℝ) ^ (2 + (2 : ℝ) / (k : ℝ)) *
          (d : ℝ) ^ ((2 : ℝ) - (2 : ℝ) / (k : ℝ)) =
        (d : ℝ) ^ (4 : ℝ) := by
    rw [← Real.rpow_add hdR]
    ring_nf
  have hpow4 : (d : ℝ) ^ (4 : ℝ) = (d : ℝ) ^ 4 :=
    Real.rpow_natCast (d : ℝ) 4
  simp [betaColumnSpikeScale, lowerConcreteN, spikeSpeed, Nat.cast_pow]
  rw [show ((d : ℝ) ^ 2) ^ 2 = (d : ℝ) ^ 4 by ring,
    ← hpow4, ← hpow_add]
  field_simp [ne_of_gt hdR,
    Real.rpow_pos_of_pos hdR ((2 : ℝ) - (2 : ℝ) / (k : ℝ)),
    Real.rpow_pos_of_pos hdR (2 + (2 : ℝ) / (k : ℝ))]

/-- The concrete lower Beta interval width tends to zero. -/
theorem lower_concrete_delta_tendsto_zero {a slack : ℝ} :
    Tendsto (fun d => lowerConcreteDelta a slack d) atTop (nhds 0) := by
  simpa [lowerConcreteDelta] using
    (tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop))

/-- The concrete fixed threshold sequence is eventually bounded by the target
threshold. -/
theorem lower_concrete_hEpsLe (ε : ℝ) :
    ∀ᶠ d in atTop, lowerConcreteEps ε d ≤ ε := by
  exact Filter.Eventually.of_forall (fun _d => le_rfl)

/-- The concrete `δ_d = d⁻¹` budget is eventually smaller than any fixed
positive scalar. -/
theorem lower_concrete_delta_eventually_le
    (a slack : ℝ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ d in atTop, lowerConcreteDelta a slack d ≤ η := by
  exact (lower_concrete_delta_tendsto_zero (a := a) (slack := slack)).eventually
    (eventually_le_nhds hη)

/-- The pure-profile concrete error budget is eventually arbitrarily small. -/
theorem lower_concrete_hProfileSmall
    {k : ℕ} {ε : ℝ} :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop,
            lowerConcreteProfileError k ε a slack d ≤ η := by
  intro a _ha slack _hslack η hη
  simpa [lowerConcreteProfileError] using
    (lower_concrete_delta_eventually_le a slack hη)

/-- The concrete background tolerance is eventually arbitrarily small. -/
theorem lower_concrete_hTauSmall :
    ∀ a : ℝ, ∀ slack : ℝ,
      ∀ η : ℝ, 0 < η →
        ∀ᶠ d in atTop, lowerConcreteTau a slack d ≤ η := by
  intro a slack η hη
  simpa [lowerConcreteTau] using
    (lower_concrete_delta_eventually_le a slack hη)

/-- The background scale-transfer concrete error budget is eventually
arbitrarily small. -/
theorem lower_concrete_hScaleSmall
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop,
            lowerConcreteScaleError R k ε a slack d ≤ η := by
  intro a _ha slack _hslack η hη
  simpa [lowerConcreteScaleError] using
    (lower_concrete_delta_eventually_le a slack hη)

/-- The mixed-remainder concrete error budget is eventually arbitrarily small. -/
theorem lower_concrete_hMixedSmall
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop,
            lowerConcreteMixedError R k ε a slack d ≤ η := by
  intro a _ha slack _hslack η hη
  simpa [lowerConcreteMixedError] using
    (lower_concrete_delta_eventually_le a slack hη)

/-- The scalar budget `exp(-d)` is eventually smaller than any fixed positive
scalar. -/
theorem lower_exp_linear_tail_eventually_le
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ d : ℕ in atTop, Real.exp (-(d : ℝ)) ≤ η := by
  by_cases hηlt : η < 1
  · have hlarge :
        ∀ᶠ d : ℕ in atTop, -Real.log η ≤ (d : ℝ) :=
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop).eventually
        (eventually_ge_atTop (-Real.log η))
    filter_upwards [hlarge] with d hlarge_d
    have hle : -(d : ℝ) ≤ Real.log η := by
      linarith
    calc
      Real.exp (-(d : ℝ)) ≤ Real.exp (Real.log η) :=
        Real.exp_le_exp.mpr hle
      _ = η := Real.exp_log hη
  · have hge : 1 ≤ η := le_of_not_gt hηlt
    filter_upwards [eventually_gt_atTop 0] with d hd
    have hle0 : -(d : ℝ) ≤ 0 := by
      exact neg_nonpos.mpr (by positivity)
    have hexp_le_one : Real.exp (-(d : ℝ)) ≤ 1 := by
      simpa only [Real.exp_zero] using
        (Real.exp_le_exp.mpr hle0 :
          Real.exp (-(d : ℝ)) ≤ Real.exp 0)
    exact le_trans hexp_le_one hge

/-- The concrete moment bad-set budget is eventually arbitrarily small. -/
theorem lower_concrete_hMomentSmall
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} :
    ∀ a : ℝ, ∀ slack : ℝ,
      ∀ η : ℝ, 0 < η →
        ∀ᶠ d in atTop,
          lowerConcreteMomentBound R k a slack d ≤ η := by
  intro _a _slack η hη
  simpa [lowerConcreteMomentBound] using
    (lower_exp_linear_tail_eventually_le (η := η) hη)

/-- Concrete model supplier for the lower pipeline's upper-endpoint scalar
assumption `hUpper`. -/
theorem lower_concrete_hUpper {k : ℕ} (hk : 1 < k) {ε : ℝ} :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          betaColumnIntervalUpper
            (betaColumnSpikeScale
              (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
            (lowerConcreteDelta a slack d) < 1 := by
  intro a _ha slack _hslack
  have hfactor :
      Tendsto (fun d => 1 + lowerConcreteDelta a slack d) atTop (nhds 1) := by
    simpa using
      (tendsto_const_nhds.add
        (lower_concrete_delta_tendsto_zero (a := a) (slack := slack)))
  have hq :=
    lower_concrete_betaColumnSpikeScale_tendsto_zero
      (k := k) hk (a := a)
  have hlim :
      Tendsto
        (fun d =>
          betaColumnIntervalUpper
            (betaColumnSpikeScale
              (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
            (lowerConcreteDelta a slack d))
        atTop (nhds 0) := by
    simpa [betaColumnIntervalUpper, mul_comm, mul_left_comm, mul_assoc]
      using hfactor.mul hq
  exact hlim.eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))

/-- Scalar-supplied canonical Beta lower bound at the concrete lower spike
scale.

This is the fixed-canonical-probability wiring theorem requested by the lower
pipeline: it targets
`lower_betaIntervalLowerBound_spikeScale_canonicalProbability` and discharges
the concrete scalar side conditions from the already-closed scalar suppliers.

The shape hypotheses `hNshape` and `hsshape` remain explicit because they
identify the scalar sequences `lowerConcreteN` and `lowerConcreteS R` with the
canonical Beta parameters for the fixed finite types `p`, `q`, and `σ`; this
wrapper does not claim that such fixed-type shape assumptions hold
unconditionally in the varying `Fin d` model. -/
theorem lower_hBeta_concreteScalars
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    [Nonempty p] [Nonempty q]
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {betaProb : ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} (hk : 1 < k) {ε : ℝ} (hε : 0 < ε)
    (hσ : 2 ≤ Fintype.card σ)
    (hNshape :
      ∀ᶠ d in atTop,
        lowerConcreteN d = columnMassBetaMainShape (p := p) (q := q))
    (hsshape :
      ∀ᶠ d in atTop,
        lowerConcreteS R d = columnMassBetaSampleCount (σ := σ))
    (hBetaProb :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            betaProb a slack d =
              (canonicalColumnMassBetaMeasure
                (p := p) (q := q) (σ := σ)).real
                (betaColumnIntervalSet
                  (betaColumnSpikeScale
                    (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                  (lowerConcreteDelta a slack d))) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          BetaColumnIntervalLowerBound
            (betaProb a slack d)
            (lowerConcreteN d) (lowerConcreteS R d)
            (betaColumnSpikeScale
              (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
            (lowerConcreteDelta a slack d) := by
  have hk0 : 0 < k := Nat.zero_lt_of_lt hk
  have hq :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            0 < betaColumnSpikeScale
              (lowerConcreteN d : ℝ) (spikeSpeed k d) a :=
    lower_concrete_hBetaScalePos (k := k) hk0 (ε := ε) hε
  have hCanon :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            BetaColumnIntervalLowerBound
              ((canonicalColumnMassBetaMeasure
                (p := p) (q := q) (σ := σ)).real
                (betaColumnIntervalSet
                  (betaColumnSpikeScale
                    (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                  (lowerConcreteDelta a slack d)))
              (lowerConcreteN d) (lowerConcreteS R d)
              (betaColumnSpikeScale
                (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
              (lowerConcreteDelta a slack d) :=
    lower_betaIntervalLowerBound_spikeScale_canonicalProbability
      (p := p) (q := q) (σ := σ)
      (N := lowerConcreteN) (s := lowerConcreteS R)
      (δ := lowerConcreteDelta) (k := k) (ε := ε)
      hσ hNshape hsshape hq
      (lower_concrete_hDeltaPos (k := k) (ε := ε))
      (lower_concrete_hUpper (k := k) hk (ε := ε))
  intro a ha slack hslack
  filter_upwards [hCanon a ha slack hslack, hBetaProb a ha slack hslack]
    with d hCanon_d hBetaProb_d
  simpa [hBetaProb_d] using hCanon_d

/-- Concrete model supplier for the lower pipeline's `hDeltaLimit` scalar
assumption. -/
theorem lower_concrete_hDeltaLimit {k : ℕ} (hk : 0 < k) {ε : ℝ} :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        Tendsto
          (fun d => (-Real.log (lowerConcreteDelta a slack d)) / spikeSpeed k d)
          atTop (nhds 0) := by
  intro a _ha slack _hslack
  have hexp : 0 < 2 + (2 : ℝ) / (k : ℝ) := by
    have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
    positivity
  have hloglittle :
      Real.log =o[atTop] fun x : ℝ => x ^ (2 + (2 : ℝ) / (k : ℝ)) :=
    isLittleO_log_rpow_atTop hexp
  have hcomp :=
    hloglittle.comp_tendsto (k := fun d : ℕ => (d : ℝ))
      tendsto_natCast_atTop_atTop
  have hlim :
      Tendsto
        (fun d : ℕ =>
          Real.log (d : ℝ) / ((d : ℝ) ^ (2 + (2 : ℝ) / (k : ℝ))))
        atTop (nhds 0) := by
    simpa [Function.comp_def] using hcomp.tendsto_div_nhds_zero
  simpa [lowerConcreteDelta, spikeSpeed, Real.log_inv] using hlim

/-- Concrete model supplier for the lower pipeline's entropy scalar limit. -/
theorem lower_concrete_hEntropyLimit
    {k : ℕ} (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        Tendsto
          (fun d =>
            ((lowerConcreteN d : ℝ) *
              (2 * Real.log (lowerConcreteN d : ℝ) -
                Real.log (a * spikeSpeed k d))) / spikeSpeed k d)
          atTop (nhds 0) := by
  intro a ha _slack _hslack
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have ha_pos : 0 < a := lt_trans (spikeRoot_pos hk hε) ha
  have hexpSmall : 0 < (2 : ℝ) / (k : ℝ) := by positivity
  have hloglittle :
      Real.log =o[atTop] fun x : ℝ => x ^ ((2 : ℝ) / (k : ℝ)) :=
    isLittleO_log_rpow_atTop hexpSmall
  have hcomp :=
    hloglittle.comp_tendsto (k := fun d : ℕ => (d : ℝ))
      tendsto_natCast_atTop_atTop
  have hlimLog :
      Tendsto
        (fun d : ℕ =>
          Real.log (d : ℝ) / ((d : ℝ) ^ ((2 : ℝ) / (k : ℝ))))
        atTop (nhds 0) := by
    simpa [Function.comp_def] using hcomp.tendsto_div_nhds_zero
  have hsmall_atTop :
      Tendsto
        (fun d : ℕ => (d : ℝ) ^ ((2 : ℝ) / (k : ℝ))) atTop atTop :=
    (tendsto_rpow_atTop hexpSmall).comp tendsto_natCast_atTop_atTop
  have hconstDiv :
      Tendsto
        (fun d : ℕ =>
          Real.log a / ((d : ℝ) ^ ((2 : ℝ) / (k : ℝ))))
        atTop (nhds 0) :=
    hsmall_atTop.const_div_atTop (Real.log a)
  have hmain :
      Tendsto
        (fun d : ℕ =>
          (2 - (2 : ℝ) / (k : ℝ)) *
              (Real.log (d : ℝ) / ((d : ℝ) ^ ((2 : ℝ) / (k : ℝ)))) -
            Real.log a / ((d : ℝ) ^ ((2 : ℝ) / (k : ℝ))))
        atTop (nhds 0) := by
    have hmul :
        Tendsto
          (fun d : ℕ =>
            (2 - (2 : ℝ) / (k : ℝ)) *
              (Real.log (d : ℝ) / ((d : ℝ) ^ ((2 : ℝ) / (k : ℝ)))))
          atTop (nhds ((2 - (2 : ℝ) / (k : ℝ)) * 0)) :=
      tendsto_const_nhds.mul hlimLog
    simpa using hmul.sub hconstDiv
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with d hd
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hspeedPow :
      (d : ℝ) ^ (2 + (2 : ℝ) / (k : ℝ)) =
        (d : ℝ) ^ 2 * (d : ℝ) ^ ((2 : ℝ) / (k : ℝ)) := by
    simpa using (Real.rpow_add hdR (2 : ℝ) ((2 : ℝ) / (k : ℝ)))
  have hlogSpeed :
      Real.log (spikeSpeed k d) =
        (2 + (2 : ℝ) / (k : ℝ)) * Real.log (d : ℝ) := by
    simp [spikeSpeed, Real.log_rpow hdR]
  have hspeed_pos : 0 < spikeSpeed k d := by
    simp [spikeSpeed, Real.rpow_pos_of_pos hdR]
  have hlogA :
      Real.log (a * spikeSpeed k d) =
        Real.log a + (2 + (2 : ℝ) / (k : ℝ)) * Real.log (d : ℝ) := by
    rw [Real.log_mul (ne_of_gt ha_pos) (ne_of_gt hspeed_pos), hlogSpeed]
  rw [hlogA]
  simp only [lowerConcreteN, Nat.cast_pow, Real.log_pow]
  rw [spikeSpeed, hspeedPow]
  field_simp [ne_of_gt hdR,
    Real.rpow_pos_of_pos hdR ((2 : ℝ) / (k : ℝ))]
  ring_nf

/-- A positive balanced aspect ratio forces the concrete sample count to be at
least two eventually. -/
theorem lower_concrete_eventually_two_le_sample
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime) :
    ∀ᶠ d in atTop, 2 ≤ R.sample d := by
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
  have hone_div :
      Tendsto (fun d : ℕ => (1 : ℝ) / ((d : ℝ) ^ 2)) atTop
        (nhds 0) :=
    hd2_atTop.const_div_atTop 1
  have hsmall :
      ∀ᶠ d : ℕ in atTop, (1 : ℝ) / ((d : ℝ) ^ 2) < R.lam / 2 := by
    exact hone_div.eventually (eventually_lt_nhds hhalf)
  filter_upwards [hratio_gt, hsmall, eventually_gt_atTop 0]
    with d hratio hsmall_d hd
  by_contra hnot
  have hs_le_one : R.sample d ≤ 1 := by omega
  have hs_le_one_R : (R.sample d : ℝ) ≤ 1 := by exact_mod_cast hs_le_one
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hden_pos : 0 < (d : ℝ) ^ 2 := by positivity
  have hratio_le :
      _root_.PptFactorization.AppendixB.ConcreteModel.sampleRatio
          R.sample d ≤
        (1 : ℝ) / ((d : ℝ) ^ 2) := by
    unfold _root_.PptFactorization.AppendixB.ConcreteModel.sampleRatio
    exact div_le_div_of_nonneg_right hs_le_one_R (le_of_lt hden_pos)
  linarith

/-- Eventually, deleting the distinguished column from the balanced concrete
sample space leaves a nonempty deleted-column type. -/
theorem lower_eventually_deletedColumn_nonempty
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime) :
    ∀ᶠ d in atTop,
      ∀ hs : 0 < R.sample d,
        Nonempty (DeletedColumn (⟨0, hs⟩ : Fin (R.sample d))) := by
  filter_upwards [lower_concrete_eventually_two_le_sample R] with d hs2 hs
  exact lower_deletedColumn_nonempty_of_two_le_sample R hs2 hs

/-- Public lower deleted-column Gaussian-tail supplier at the common threshold.

For every fixed spike level and slack, the deleted-column Gaussian sample and
rho-gamma operator tails are simultaneously bounded by the canonical
`exp(-d²/12)` budgets, after replacing the two canonical thresholds by the
single common threshold `lowerConcreteM R`. -/
theorem lower_concrete_deletedColumn_commonThreshold_operator_tails
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime) :
    ∀ a : ℝ, ∀ slack : ℝ,
      ∀ᶠ d in atTop,
        ∀ hs : 0 < R.sample d,
          (_root_.PptFactorization.HighProbabilityBounds.gaussianMeasure
            (Fin d) (Fin d)
            (DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
            ((_root_.PptFactorization.HighProbabilityBounds.normalizedSampleOpNormEvent
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
              (lowerConcreteM R a slack d) (d : ℝ))ᶜ) ≤
            lowerConcreteSampleTailBound a slack d ∧
          (_root_.PptFactorization.HighProbabilityBounds.gaussianMeasure
            (Fin d) (Fin d)
            (DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
            ((_root_.PptFactorization.HighProbabilityBounds.normalizedRhoGammaOpNormEvent
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
              (lowerConcreteM R a slack d) (d : ℝ))ᶜ) ≤
            lowerConcreteGammaTailBound a slack d := by
  intro a slack
  filter_upwards
    [eventually_gt_atTop 0,
      lower_concrete_eventually_two_le_sample R,
      lower_eventually_large_dimension_sq]
    with d hd hs2 hLarge hs
  have htails :=
    lower_concrete_commonThreshold_operator_tails_pointwise
      (R := R) hd hs2 hs hLarge a slack
  constructor
  · simpa [lowerConcreteSampleTailBound] using htails.1
  · simpa [lowerConcreteGammaTailBound] using htails.2

/-- Projection of the public deleted-column tail supplier onto the sample
operator tail. -/
theorem lower_concrete_hSampleTail_of_deletedColumn_operator_tails
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime) :
    ∀ a : ℝ, ∀ slack : ℝ,
      ∀ᶠ d in atTop,
        ∀ hs : 0 < R.sample d,
          (_root_.PptFactorization.HighProbabilityBounds.gaussianMeasure
            (Fin d) (Fin d)
            (DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
            ((_root_.PptFactorization.HighProbabilityBounds.normalizedSampleOpNormEvent
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
              (lowerConcreteM R a slack d) (d : ℝ))ᶜ) ≤
            lowerConcreteSampleTailBound a slack d := by
  intro a slack
  filter_upwards
    [lower_concrete_deletedColumn_commonThreshold_operator_tails R a slack]
    with d htails hs
  exact (htails hs).1

/-- Projection of the public deleted-column tail supplier onto the rho-gamma
operator tail. -/
theorem lower_concrete_hGammaTail_of_deletedColumn_operator_tails
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime) :
    ∀ a : ℝ, ∀ slack : ℝ,
      ∀ᶠ d in atTop,
        ∀ hs : 0 < R.sample d,
          (_root_.PptFactorization.HighProbabilityBounds.gaussianMeasure
            (Fin d) (Fin d)
            (DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
            ((_root_.PptFactorization.HighProbabilityBounds.normalizedRhoGammaOpNormEvent
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
              (lowerConcreteM R a slack d) (d : ℝ))ᶜ) ≤
            lowerConcreteGammaTailBound a slack d := by
  intro a slack
  filter_upwards
    [lower_concrete_deletedColumn_commonThreshold_operator_tails R a slack]
    with d htails hs
  exact (htails hs).2

/-- Concrete lower `hSampleTail` supplier for the deleted-column background at
the canonical common lower threshold `lowerConcreteM`. -/
theorem lower_concrete_hSampleTail_commonThreshold
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime) :
    ∀ a : ℝ, ∀ slack : ℝ,
      ∀ᶠ d in atTop,
        ∀ hs : 0 < R.sample d,
          (_root_.PptFactorization.HighProbabilityBounds.gaussianMeasure
            (Fin d) (Fin d)
            (DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
            ((_root_.PptFactorization.HighProbabilityBounds.normalizedSampleOpNormEvent
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
              (lowerConcreteM R a slack d) (d : ℝ))ᶜ) ≤
            lowerConcreteSampleTailBound a slack d := by
  exact lower_concrete_hSampleTail_of_deletedColumn_operator_tails R

/-- Concrete lower `hGammaTail` supplier for the deleted-column background at
the canonical common lower threshold `lowerConcreteM`. -/
theorem lower_concrete_hGammaTail_commonThreshold
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime) :
    ∀ a : ℝ, ∀ slack : ℝ,
      ∀ᶠ d in atTop,
        ∀ hs : 0 < R.sample d,
          (_root_.PptFactorization.HighProbabilityBounds.gaussianMeasure
            (Fin d) (Fin d)
            (DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
            ((_root_.PptFactorization.HighProbabilityBounds.normalizedRhoGammaOpNormEvent
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
              (lowerConcreteM R a slack d) (d : ℝ))ᶜ) ≤
            lowerConcreteGammaTailBound a slack d := by
  exact lower_concrete_hGammaTail_of_deletedColumn_operator_tails R

/-- Concrete `hProduct`: the actual varying one-column favourable probability
factorizes into Beta, cap, and deleted-background factors. -/
theorem lower_concrete_hProduct
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)))
    (M τ center : ℝ → ℝ → ℕ → ℝ) {k : ℕ} {root : ℝ} :
    ∀ a : ℝ, root < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          lowerConcreteColumnProb R e M τ center k a slack d =
            lowerConcreteBetaProb R k a slack d *
              lowerConcreteCapProb R e a slack d *
                lowerConcreteBackgroundProb R M τ center k a slack d := by
  intro a _ha slack _hslack
  filter_upwards
    [eventually_gt_atTop 0, lower_concrete_eventually_two_le_sample R]
    with d hd hs2
  have hs : 0 < R.sample d := lt_of_lt_of_le (by norm_num) hs2
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hσ : 2 ≤ Fintype.card (Fin (R.sample d)) := by
    simpa using hs2
  have hprod :=
    lower_canonical_product_probability_concreteEvents_pointwise_of_closed_deletedBackground_sphericalLaw
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      (α₀ := (⟨0, hs⟩ : Fin (R.sample d)))
      (q₀ := betaColumnSpikeScale
        (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
      (δ := lowerConcreteDelta a slack d)
      (radius := 1 / (lowerConcreteNcap d : ℝ))
      (N := lowerConcreteN d)
      (M := M a slack d)
      (τ := τ a slack d)
      (center := center a slack d)
      (e := e (a, slack, d))
      (k := k) hσ
  simpa [lowerConcreteColumnProb, lowerConcreteBetaProb,
    lowerConcreteCapProb, lowerConcreteBackgroundProb,
    lowerConcreteDirectionCapSet, columnDirectionCapProbability,
    ambientProjectiveCapProbability, hs] using hprod

/-- Concrete `hBeta`: the varying canonical Beta interval probability satisfies
the lower-bound package at
`q = betaColumnSpikeScale (d²) (spikeSpeed k d) a` and
`δ = d⁻¹`. -/
theorem lower_concrete_hBeta
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} (hk : 1 < k) {ε : ℝ} (hε : 0 < ε) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          BetaColumnIntervalLowerBound
            (lowerConcreteBetaProb R k a slack d)
            (lowerConcreteN d) (lowerConcreteS R d)
            (betaColumnSpikeScale
              (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
            (lowerConcreteDelta a slack d) := by
  intro a ha slack hslack
  have hk0 : 0 < k := Nat.zero_lt_of_lt hk
  filter_upwards
    [eventually_gt_atTop 0,
      lower_concrete_eventually_two_le_sample R,
      lower_concrete_hBetaScalePos (k := k) hk0 (ε := ε) hε a ha slack hslack,
      lower_concrete_hDeltaPos (k := k) (ε := ε) a ha slack hslack,
      lower_concrete_hUpper (k := k) hk (ε := ε) a ha slack hslack]
    with d hd hs2 hq hδ hupper
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hσ : 2 ≤ Fintype.card (Fin (R.sample d)) := by
    simpa using hs2
  have hBeta :=
    lower_betaIntervalLowerBound_canonicalProbability_pointwise
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      (N := lowerConcreteN d) (s := lowerConcreteS R d)
      (q₀ :=
        betaColumnSpikeScale
          (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
      (δ := lowerConcreteDelta a slack d)
      hσ
      (by simp [lowerConcreteN, columnMassBetaMainShape, BipIndex, pow_two])
      (by simp [lowerConcreteS, columnMassBetaSampleCount])
      hq hδ hupper
  simpa [lowerConcreteBetaProb]
    using hBeta

/-- Concrete `hBounds` from the three bad-event estimates under the actual
deleted-column background law.

This closes the packaging, measurability, and deleted-background probability
fields in `DeletedColumnBackgroundBadSetBounds`.  The three probability
estimates themselves remain explicit inputs: moment bad set, sample operator
bad set, and partial-transpose operator bad set. -/
theorem lower_concrete_hBounds_of_deleted_background_bad_bounds
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {M τ center bMoment bSample bGamma : ℝ → ℝ → ℕ → ℝ}
    {k : ℕ}
    (hMoment :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            (deletedColumnBackgroundLaw
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              (⟨0, hs⟩ : Fin (R.sample d))).real
              (backgroundMomentBadSet
                (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                (lowerConcreteN d) (τ a slack d) (center a slack d) k) ≤
              bMoment a slack d)
    (hSample :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            (deletedColumnBackgroundLaw
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              (⟨0, hs⟩ : Fin (R.sample d))).real
              (backgroundSampleOpNormBadSet
                (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                (lowerConcreteN d) (M a slack d)) ≤
              bSample a slack d)
    (hGamma :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            (deletedColumnBackgroundLaw
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              (⟨0, hs⟩ : Fin (R.sample d))).real
              (backgroundGammaOpNormBadSet
                (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                (lowerConcreteN d) (M a slack d)) ≤
              bGamma a slack d) :
    ∀ a : ℝ, ∀ slack : ℝ,
      ∀ᶠ d in atTop,
        ∀ hs : 0 < R.sample d,
          DeletedColumnBackgroundBadSetBounds
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            (⟨0, hs⟩ : Fin (R.sample d))
            (lowerConcreteN d) (M a slack d) (τ a slack d)
            (center a slack d) (bMoment a slack d)
            (bSample a slack d) (bGamma a slack d) k := by
  intro a slack
  filter_upwards
    [eventually_gt_atTop 0, lower_concrete_eventually_two_le_sample R,
      hMoment a slack, hSample a slack, hGamma a slack]
    with d hd hs2 hMoment_d hSample_d hGamma_d
  intro hs
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hσ : 2 ≤ Fintype.card (Fin (R.sample d)) := by
    simpa using hs2
  exact
    DeletedColumnBackgroundBadSetBounds.of_deleted_background_bad_bounds_noInput_probability
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      (α₀ := (⟨0, hs⟩ : Fin (R.sample d)))
      (N := lowerConcreteN d) (M := M a slack d)
      (τ := τ a slack d) (mean := center a slack d)
      (bMoment := bMoment a slack d)
      (bSample := bSample a slack d)
      (bGamma := bGamma a slack d)
      (k := k)
      hσ
      (measurableSet_backgroundTypicalSet
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        (lowerConcreteN d) (M a slack d) (τ a slack d)
        (center a slack d) k)
      (hMoment_d hs) (hSample_d hs) (hGamma_d hs)

/-- Concrete `hBounds` from bad-set bounds on the reduced deleted-column
spherical model.

This is the canonical deleted-background transport closure: the background law
in the one-column decomposition is the spherical law on
`DeletedColumn α₀`, zero-extended back to the original sample space.  Thus a
`ConcreteSphericalBackgroundBadSetBounds` package on that reduced space
supplies the exact deleted-background `hBounds` package. -/
theorem lower_concrete_hBounds_of_reduced_spherical_bad_bounds
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {M τ center bMoment bSample bGamma : ℝ → ℝ → ℕ → ℝ}
    {k : ℕ}
    (hReduced :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            ConcreteSphericalBackgroundBadSetBounds
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
              (lowerConcreteN d) (M a slack d) (τ a slack d)
              (center a slack d) (bMoment a slack d)
              (bSample a slack d) (bGamma a slack d) k) :
    ∀ a : ℝ, ∀ slack : ℝ,
      ∀ᶠ d in atTop,
        ∀ hs : 0 < R.sample d,
          DeletedColumnBackgroundBadSetBounds
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            (⟨0, hs⟩ : Fin (R.sample d))
            (lowerConcreteN d) (M a slack d) (τ a slack d)
            (center a slack d) (bMoment a slack d)
            (bSample a slack d) (bGamma a slack d) k := by
  intro a slack
  filter_upwards
    [eventually_gt_atTop 0, lower_concrete_eventually_two_le_sample R,
      hReduced a slack]
    with d hd hs2 hReduced_d
  intro hs
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hσ : 2 ≤ Fintype.card (Fin (R.sample d)) := by
    simpa using hs2
  exact
    DeletedColumnBackgroundBadSetBounds.of_reduced_concrete_spherical_bad_bounds
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      (α₀ := (⟨0, hs⟩ : Fin (R.sample d)))
      (N := lowerConcreteN d) (M := M a slack d)
      (τ := τ a slack d) (mean := center a slack d)
      (bMoment := bMoment a slack d)
      (bSample := bSample a slack d)
      (bGamma := bGamma a slack d)
      (k := k)
      hσ
      (hReduced_d hs)

/-- Concrete reduced spherical bad-set package from one reduced moment bound
and the two normalized Gaussian operator-tail bounds.

This removes the bundled `ConcreteSphericalBackgroundBadSetBounds` input when
the actual estimates have already been proved in their natural forms.  The
moment estimate and the two Gaussian tails are still explicit theorem
parameters; this wrapper only supplies the closed spherical/Gaussian transfer
and the concrete identity `lowerConcreteN d = d²`. -/
theorem lower_concrete_hReduced_of_moment_and_gaussian_operator_tails
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {M τ center bMoment bSample bGamma : ℝ → ℝ → ℕ → ℝ}
    {k : ℕ}
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
                (lowerConcreteN d) (τ a slack d) (center a slack d) k) ≤
              bMoment a slack d)
    (hSampleTail :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            (_root_.PptFactorization.HighProbabilityBounds.gaussianMeasure
              (Fin d) (Fin d)
              (DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
              ((_root_.PptFactorization.HighProbabilityBounds.normalizedSampleOpNormEvent
                (p := Fin d) (q := Fin d)
                (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
                (M a slack d) (d : ℝ))ᶜ) ≤
              bSample a slack d)
    (hGammaTail :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            (_root_.PptFactorization.HighProbabilityBounds.gaussianMeasure
              (Fin d) (Fin d)
              (DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
              ((_root_.PptFactorization.HighProbabilityBounds.normalizedRhoGammaOpNormEvent
                (p := Fin d) (q := Fin d)
                (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
                (M a slack d) (d : ℝ))ᶜ) ≤
              bGamma a slack d) :
    ∀ a : ℝ, ∀ slack : ℝ,
      ∀ᶠ d in atTop,
        ∀ hs : 0 < R.sample d,
          ConcreteSphericalBackgroundBadSetBounds
            (p := Fin d) (q := Fin d)
            (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
            (lowerConcreteN d) (M a slack d) (τ a slack d)
            (center a slack d) (bMoment a slack d)
            (bSample a slack d) (bGamma a slack d) k := by
  intro a slack
  filter_upwards
    [eventually_gt_atTop 0, hMoment a slack, hSampleTail a slack,
      hGammaTail a slack]
    with d hd hMoment_d hSampleTail_d hGammaTail_d
  intro hs
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  exact
    ConcreteSphericalBackgroundBadSetBounds.of_moment_and_gaussian_operator_tails
      (p := Fin d) (q := Fin d)
      (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
      (N := (lowerConcreteN d : ℝ)) (d := (d : ℝ))
      (M := M a slack d) (τ := τ a slack d)
      (mean := center a slack d)
      (bMoment := bMoment a slack d)
      (bSample := bSample a slack d)
      (bGamma := bGamma a slack d)
      (k := k)
      hdR
      (by simp [lowerConcreteN, Nat.cast_pow])
      (hMoment_d hs) (hSampleTail_d hs) (hGammaTail_d hs)

/-- Concrete `hBad` from separate one-sixth budgets for the three
deleted-background bad events.

This is pure scalar bookkeeping: no probability estimate is proved here.  It
packages the three visible upper bounds into the union-bound budget required by
the background half-mass step. -/
theorem lower_concrete_hBad_of_each_le_sixth
    {bMoment bSample bGamma : ℝ → ℝ → ℕ → ℝ}
    (hMoment :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop, bMoment a slack d ≤ 1 / 6)
    (hSample :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop, bSample a slack d ≤ 1 / 6)
    (hGamma :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop, bGamma a slack d ≤ 1 / 6) :
    ∀ a : ℝ, ∀ slack : ℝ,
      ∀ᶠ d in atTop,
        bMoment a slack d + bSample a slack d + bGamma a slack d ≤ 1 / 2 := by
  intro a slack
  filter_upwards [hMoment a slack, hSample a slack, hGamma a slack]
    with d hMoment_d hSample_d hGamma_d
  linarith

/-- Concrete `hBad` from eventual smallness of each bad-event budget.

This closes the scalar union-bound budget when each of the three background
bad-event budgets can be made eventually smaller than any fixed positive
constant.  The smallness assumptions remain explicit parameters. -/
theorem lower_concrete_hBad_of_eventual_small
    {bMoment bSample bGamma : ℝ → ℝ → ℕ → ℝ}
    (hMoment :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop, bMoment a slack d ≤ η)
    (hSample :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop, bSample a slack d ≤ η)
    (hGamma :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop, bGamma a slack d ≤ η) :
    ∀ a : ℝ, ∀ slack : ℝ,
      ∀ᶠ d in atTop,
        bMoment a slack d + bSample a slack d + bGamma a slack d ≤ 1 / 2 := by
  exact
    lower_concrete_hBad_of_each_le_sixth
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (by
        intro a slack
        exact hMoment a slack (1 / 6) (by norm_num))
      (by
        intro a slack
        exact hSample a slack (1 / 6) (by norm_num))
      (by
        intro a slack
        exact hGamma a slack (1 / 6) (by norm_num))

/-- Concrete `hBackgroundHalf`: deleted-background bad-set bounds give
eventual half mass for the concrete varying background factor. -/
theorem lower_concrete_hBackgroundHalf
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {M τ center bMoment bSample bGamma : ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hBounds :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            DeletedColumnBackgroundBadSetBounds
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              (⟨0, hs⟩ : Fin (R.sample d))
              (lowerConcreteN d) (M a slack d) (τ a slack d)
              (center a slack d) (bMoment a slack d)
              (bSample a slack d) (bGamma a slack d) k)
    (hBad :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          bMoment a slack d + bSample a slack d + bGamma a slack d ≤ 1 / 2) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (1 / 2 : ℝ) ≤
            lowerConcreteBackgroundProb R M τ center k a slack d := by
  intro a _ha slack _hslack
  filter_upwards
    [lower_concrete_eventually_two_le_sample R, hBounds a slack, hBad a slack]
    with d hs2 hBounds_d hBad_d
  have hs : 0 < R.sample d := lt_of_lt_of_le (by norm_num) hs2
  have hHalf :=
    (hBounds_d hs).backgroundTypicalSet_measure_ge_half
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      (N := lowerConcreteN d) (M := M a slack d)
      (τ := τ a slack d) (mean := center a slack d)
      (bMoment := bMoment a slack d)
      (bSample := bSample a slack d)
      (bGamma := bGamma a slack d)
      (k := k) hBad_d
  simpa [lowerConcreteBackgroundProb, hs] using hHalf

/-- Concrete `hBackgroundHalf` with `hBounds` supplied from the three
deleted-background bad-event probability estimates. -/
theorem lower_concrete_hBackgroundHalf_of_deleted_background_bad_bounds
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {M τ center bMoment bSample bGamma : ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hMoment :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            (deletedColumnBackgroundLaw
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              (⟨0, hs⟩ : Fin (R.sample d))).real
              (backgroundMomentBadSet
                (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                (lowerConcreteN d) (τ a slack d) (center a slack d) k) ≤
              bMoment a slack d)
    (hSample :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            (deletedColumnBackgroundLaw
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              (⟨0, hs⟩ : Fin (R.sample d))).real
              (backgroundSampleOpNormBadSet
                (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                (lowerConcreteN d) (M a slack d)) ≤
              bSample a slack d)
    (hGamma :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            (deletedColumnBackgroundLaw
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              (⟨0, hs⟩ : Fin (R.sample d))).real
              (backgroundGammaOpNormBadSet
                (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                (lowerConcreteN d) (M a slack d)) ≤
              bGamma a slack d)
    (hBad :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          bMoment a slack d + bSample a slack d + bGamma a slack d ≤ 1 / 2) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (1 / 2 : ℝ) ≤
            lowerConcreteBackgroundProb R M τ center k a slack d := by
  exact
    lower_concrete_hBackgroundHalf
      (R := R) (M := M) (τ := τ) (center := center)
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (k := k) (ε := ε)
      (lower_concrete_hBounds_of_deleted_background_bad_bounds
        (R := R) (M := M) (τ := τ) (center := center)
        (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
        (k := k) hMoment hSample hGamma)
      hBad

/-- Concrete `hBackgroundHalf` with `hBounds` supplied by reduced spherical
bad-set bounds on `DeletedColumn`.

This is the preferred concrete lower-side background wrapper: it uses the
closed deleted-column transport and leaves only the reduced model bad-set
package plus the scalar union-bound budget visible. -/
theorem lower_concrete_hBackgroundHalf_of_reduced_spherical_bad_bounds
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {M τ center bMoment bSample bGamma : ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hReduced :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            ConcreteSphericalBackgroundBadSetBounds
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
              (lowerConcreteN d) (M a slack d) (τ a slack d)
              (center a slack d) (bMoment a slack d)
              (bSample a slack d) (bGamma a slack d) k)
    (hBad :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          bMoment a slack d + bSample a slack d + bGamma a slack d ≤ 1 / 2) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (1 / 2 : ℝ) ≤
            lowerConcreteBackgroundProb R M τ center k a slack d := by
  exact
    lower_concrete_hBackgroundHalf
      (R := R) (M := M) (τ := τ) (center := center)
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (k := k) (ε := ε)
      (lower_concrete_hBounds_of_reduced_spherical_bad_bounds
        (R := R) (M := M) (τ := τ) (center := center)
        (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
        (k := k) hReduced)
      hBad

/-- Concrete `hBackgroundHalf` with reduced spherical bad-set bounds and the
union-bound budget supplied by eventual smallness of the three bad-event
budgets. -/
theorem lower_concrete_hBackgroundHalf_of_reduced_spherical_bad_bounds_smallBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {M τ center bMoment bSample bGamma : ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hReduced :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            ConcreteSphericalBackgroundBadSetBounds
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
              (lowerConcreteN d) (M a slack d) (τ a slack d)
              (center a slack d) (bMoment a slack d)
              (bSample a slack d) (bGamma a slack d) k)
    (hMomentSmall :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop, bMoment a slack d ≤ η)
    (hSampleSmall :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop, bSample a slack d ≤ η)
    (hGammaSmall :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop, bGamma a slack d ≤ η) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (1 / 2 : ℝ) ≤
            lowerConcreteBackgroundProb R M τ center k a slack d := by
  exact
    lower_concrete_hBackgroundHalf_of_reduced_spherical_bad_bounds
      (R := R) (M := M) (τ := τ) (center := center)
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (k := k) (ε := ε)
      hReduced
      (lower_concrete_hBad_of_eventual_small
        (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
        hMomentSmall hSampleSmall hGammaSmall)

/-- Concrete `hCap`: the varying column-direction cap probability satisfies
the projective cap lower-bound package once the finite-dimensional
cone-coordinate formula and the unit spike direction are supplied. -/
theorem lower_concrete_hCap_of_surfaceCone
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)))
    {k : ℕ} {ε : ℝ}
    (hCoord :
      ∀ᶠ d in atTop,
        SurfaceProjectiveCapConeCoordinateFormula
          (BipIndex (Fin d) (Fin d)))
    (hUnit :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, ‖e (a, slack, d)‖ = 1) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ProjectiveCapProbabilityLowerBound
            (lowerConcreteCapProb R e a slack d)
            (lowerConcreteNcap d) (1 / (lowerConcreteNcap d : ℝ)) := by
  intro a ha slack hslack
  filter_upwards
    [eventually_ge_atTop 2, lower_concrete_eventually_two_le_sample R,
      hCoord, hUnit a ha slack hslack]
    with d hd2 hs2 hCoord_d hUnit_d
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) hd2
  have hs : 0 < R.sample d := lt_of_lt_of_le (by norm_num) hs2
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hσ : 2 ≤ Fintype.card (Fin (R.sample d)) := by
    simpa using hs2
  have hN2 : 2 ≤ Fintype.card (BipIndex (Fin d) (Fin d)) := by
    simp [BipIndex]
    nlinarith
  have hDirectionBeta :
      AmbientHaarProjectiveOverlapBetaLaw
        (ι := BipIndex (Fin d) (Fin d))
        (columnDirectionPushforward
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (_root_.PptFactorization.AppendixB.sphericalModelMeasure
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)))
          (⟨0, hs⟩ : Fin (R.sample d))) :=
    lower_columnDirectionAmbientHaarProjectiveOverlapBetaLaw_of_surfaceCone
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      (α₀ := (⟨0, hs⟩ : Fin (R.sample d)))
      hσ hN2 hCoord_d
  have hCap :=
    hDirectionBeta.toColumnDirectionProjectiveCapProbabilityLowerBound_inv
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      (μ :=
        _root_.PptFactorization.AppendixB.sphericalModelMeasure
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)))
      (α₀ := (⟨0, hs⟩ : Fin (R.sample d)))
      (e := e (a, slack, d)) hUnit_d
  simpa [lowerConcreteCapProb, lowerConcreteNcap, columnMassBetaMainShape,
    BipIndex, pow_two, hs] using hCap

/-- Concrete `hCap` for the canonical coordinate spike direction.

This removes the explicit unit-normalization hypothesis from
`lower_concrete_hCap_of_surfaceCone`; the only remaining geometric input here
is the finite-dimensional cone-coordinate formula. -/
theorem lower_concrete_hCap_of_surfaceCone_canonicalDirection
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ}
    (hCoord :
      ∀ᶠ d in atTop,
        SurfaceProjectiveCapConeCoordinateFormula
          (BipIndex (Fin d) (Fin d))) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ProjectiveCapProbabilityLowerBound
            (lowerConcreteCapProb R lowerConcreteCanonicalDirection a slack d)
            (lowerConcreteNcap d) (1 / (lowerConcreteNcap d : ℝ)) := by
  exact
    lower_concrete_hCap_of_surfaceCone
      (R := R) (e := lowerConcreteCanonicalDirection) (k := k) (ε := ε)
      hCoord (lower_concrete_hUnit_canonicalDirection (k := k) (ε := ε))

/-- Concrete supplier for the varying-model projective cone-coordinate input
from the reference-centre cone formula.

This closes the unitary-invariance transport in `hCoord`: once the reference
coordinate cap formula is available in each finite dimension, the full
`SurfaceProjectiveCapConeCoordinateFormula` for arbitrary unit centres follows
eventually.  The reference formula itself is still a visible analytic input;
this theorem does not claim to prove that integral calculation. -/
theorem lower_concrete_hCoord_of_referenceCone
    (hReference :
      ∀ᶠ d in atTop,
        ∀ i₀ : BipIndex (Fin d) (Fin d),
          SurfaceReferenceProjectiveCapConeCoordinateFormula
            (BipIndex (Fin d) (Fin d)) i₀) :
    ∀ᶠ d in atTop,
      SurfaceProjectiveCapConeCoordinateFormula
        (BipIndex (Fin d) (Fin d)) := by
  filter_upwards [eventually_gt_atTop 0, hReference] with d hd hReference_d
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let i₀ : BipIndex (Fin d) (Fin d) :=
    ((⟨0, hd⟩ : Fin d), (⟨0, hd⟩ : Fin d))
  change ∀ {e : EuclideanSpace ℂ (BipIndex (Fin d) (Fin d))}, ‖e‖ = 1 →
    ∀ {r : ℝ}, 0 ≤ r → r < 1 →
      projectiveCapProbability (ι := BipIndex (Fin d) (Fin d))
        (surfaceMeasure (BipIndex (Fin d) (Fin d))) e r =
      projectiveConeCoordinateRatio
        (Fintype.card (BipIndex (Fin d) (Fin d)) - 1) r
  exact
    SurfaceProjectiveCapConeCoordinateFormula.of_reference
      (ι := BipIndex (Fin d) (Fin d)) i₀ (hReference_d i₀)

/-- Concrete `hCap` with the cone-coordinate input reduced to the reference
coordinate cone formula.

Compared with `lower_concrete_hCap_of_surfaceCone`, this wrapper removes the
full arbitrary-centre `hCoord` assumption and asks only for the reference-centre
formula supplied to `lower_concrete_hCoord_of_referenceCone`. -/
theorem lower_concrete_hCap_of_referenceCone
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)))
    {k : ℕ} {ε : ℝ}
    (hReference :
      ∀ᶠ d in atTop,
        ∀ i₀ : BipIndex (Fin d) (Fin d),
          SurfaceReferenceProjectiveCapConeCoordinateFormula
            (BipIndex (Fin d) (Fin d)) i₀)
    (hUnit :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, ‖e (a, slack, d)‖ = 1) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ProjectiveCapProbabilityLowerBound
            (lowerConcreteCapProb R e a slack d)
            (lowerConcreteNcap d) (1 / (lowerConcreteNcap d : ℝ)) := by
  exact
    lower_concrete_hCap_of_surfaceCone
      (R := R) (e := e) (k := k) (ε := ε)
      (lower_concrete_hCoord_of_referenceCone hReference) hUnit

/-- Concrete `hCap` for the canonical coordinate spike direction with the
cone-coordinate input reduced to the reference-centre formula.

This closes the standalone `hUnit` side condition for the canonical direction;
the reference cone-volume identity remains a visible assumption. -/
theorem lower_concrete_hCap_of_referenceCone_canonicalDirection
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ}
    (hReference :
      ∀ᶠ d in atTop,
        ∀ i₀ : BipIndex (Fin d) (Fin d),
          SurfaceReferenceProjectiveCapConeCoordinateFormula
            (BipIndex (Fin d) (Fin d)) i₀) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ProjectiveCapProbabilityLowerBound
            (lowerConcreteCapProb R lowerConcreteCanonicalDirection a slack d)
            (lowerConcreteNcap d) (1 / (lowerConcreteNcap d : ℝ)) := by
  exact
    lower_concrete_hCap_of_referenceCone
      (R := R) (e := lowerConcreteCanonicalDirection) (k := k) (ε := ε)
      hReference
      (lower_concrete_hUnit_canonicalDirection (k := k) (ε := ε))

/-- Concrete `hColumnIncluded`: deterministic closed blocks imply that the
varying one-column favourable probability is bounded by the target lower-tail
deviation probability.

This closes the probability-inclusion plumbing for the concrete `Fin d` model.
The remaining inputs are not probabilistic axioms; they are the visible
deterministic estimates needed to put the favourable column event inside the
target event: the spike profile lower bound on the Beta/cap set, background
transfer, mixed-remainder envelope, mean comparison, and scalar error budget. -/
theorem lower_concrete_hColumnIncluded_of_closed_deterministic_blocks
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)))
    {eps mean : ℕ → ℝ}
    {M τ center errProfile errSpike errScale errBg errMix errMean :
      ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hProfile :
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
                u ∈ lowerConcreteDirectionCapSet e a slack d →
                a ^ k - errProfile a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hPureError :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            errProfile a slack d + 0 ≤ errSpike a slack d)
    (hBackgroundTransfer :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ hs : 0 < R.sample d,
              ∀ X : SampleMatrix (Fin d) (Fin d) (Fin (R.sample d)),
                sampleColumnComplementNormalized
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    X (⟨0, hs⟩ : Fin (R.sample d)) ∈
                  backgroundTypicalSet
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) (M a slack d) (τ a slack d)
                    (center a slack d) k →
                backgroundMomentValue
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) k
                    (sampleColumnComplementNormalized
                      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                      X (⟨0, hs⟩ : Fin (R.sample d))) -
                    errScale a slack d ≤
                  columnBackgroundContribution
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) k X
                    (⟨0, hs⟩ : Fin (R.sample d)))
    (hBackgroundError :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            τ a slack d + errScale a slack d ≤ errBg a slack d)
    (hMixed :
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
                |columnMixedRemainder
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) k X
                    (⟨0, hs⟩ : Fin (R.sample d))| ≤
                  errMix a slack d)
    (hMean :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            mean d ≤ center a slack d + errMean a slack d)
    (hBudget :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            eps d + errSpike a slack d + errBg a slack d +
              errMix a slack d + errMean a slack d ≤ a ^ k) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          lowerConcreteColumnProb R e M τ center k a slack d ≤
            lowerConcreteTargetProb R eps mean k d := by
  intro a ha slack hslack
  filter_upwards
    [lower_concrete_eventually_two_le_sample R,
      hProfile a ha slack hslack,
      hPureError a ha slack hslack,
      hBackgroundTransfer a ha slack hslack,
      hBackgroundError a ha slack hslack,
      hMixed a ha slack hslack,
      hMean a ha slack hslack,
      hBudget a ha slack hslack]
    with d hs2 hProfile_d hPureError_d hBackgroundTransfer_d
      hBackgroundError_d hMixed_d hMean_d hBudget_d
  have hs : 0 < R.sample d := lt_of_lt_of_le (by norm_num) hs2
  letI : IsProbabilityMeasure
      (_root_.PptFactorization.AppendixB.sphericalModelMeasure
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))) :=
    _root_.PptFactorization.AppendixB.sphericalModelMeasure_isProbabilityMeasure
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
  exact
    columnProb_le_upperTailProb_of_closed_deterministic_blocks
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      (μ :=
        _root_.PptFactorization.AppendixB.sphericalModelMeasure
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d)))
      (columnProb := lowerConcreteColumnProb R e M τ center k a slack d)
      (targetProb := lowerConcreteTargetProb R eps mean k d)
      (α₀ := (⟨0, hs⟩ : Fin (R.sample d)))
      (q₀ :=
        betaColumnSpikeScale
          (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
      (δ := lowerConcreteDelta a slack d)
      (N := lowerConcreteN d) (M := M a slack d) (a := a)
      (eps := eps d) (mean := mean d) (center := center a slack d)
      (errProfile := errProfile a slack d)
      (errSpike := errSpike a slack d)
      (τ := τ a slack d) (errScale := errScale a slack d)
      (errBg := errBg a slack d) (errMix := errMix a slack d)
      (errMean := errMean a slack d) (k := k)
      (directionSet := lowerConcreteDirectionCapSet e a slack d)
      (by simp [lowerConcreteColumnProb, hs])
      (by rfl)
      hProfile_d hPureError_d (hBackgroundTransfer_d hs)
      hBackgroundError_d (hMixed_d hs) hMean_d hBudget_d

/-- Concrete `hColumnIncluded` with the spike-profile obligation restricted to
unit directions.

This is the sharper deterministic bridge for the actual `Fin d` model.  The
positive canonical Beta lower endpoint implies the sampled column direction has
norm `1`, so the profile estimate no longer has to cover arbitrary non-unit
ambient vectors lying in the projective cap. -/
theorem lower_concrete_hColumnIncluded_of_closed_unitProfile
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)))
    {eps mean : ℕ → ℝ}
    {M τ center errProfile errSpike errScale errBg errMix errMean :
      ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hk : 0 < k) (hε : 0 < ε)
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
                u ∈ lowerConcreteDirectionCapSet e a slack d →
                ‖u‖ = 1 →
                a ^ k - errProfile a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hPureError :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            errProfile a slack d + 0 ≤ errSpike a slack d)
    (hBackgroundTransfer :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ hs : 0 < R.sample d,
              ∀ X : SampleMatrix (Fin d) (Fin d) (Fin (R.sample d)),
                sampleColumnComplementNormalized
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    X (⟨0, hs⟩ : Fin (R.sample d)) ∈
                  backgroundTypicalSet
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) (M a slack d) (τ a slack d)
                    (center a slack d) k →
                backgroundMomentValue
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) k
                    (sampleColumnComplementNormalized
                      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                      X (⟨0, hs⟩ : Fin (R.sample d))) -
                    errScale a slack d ≤
                  columnBackgroundContribution
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) k X
                    (⟨0, hs⟩ : Fin (R.sample d)))
    (hBackgroundError :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            τ a slack d + errScale a slack d ≤ errBg a slack d)
    (hMixed :
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
                |columnMixedRemainder
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) k X
                    (⟨0, hs⟩ : Fin (R.sample d))| ≤
                  errMix a slack d)
    (hMean :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            mean d ≤ center a slack d + errMean a slack d)
    (hBudget :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            eps d + errSpike a slack d + errBg a slack d +
              errMix a slack d + errMean a slack d ≤ a ^ k) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          lowerConcreteColumnProb R e M τ center k a slack d ≤
            lowerConcreteTargetProb R eps mean k d := by
  intro a ha slack hslack
  filter_upwards
    [lower_concrete_eventually_two_le_sample R,
      lower_concrete_hBetaScalePos (k := k) hk (ε := ε) hε a ha slack hslack,
      hUnitProfile a ha slack hslack,
      hPureError a ha slack hslack,
      hBackgroundTransfer a ha slack hslack,
      hBackgroundError a ha slack hslack,
      hMixed a ha slack hslack,
      hMean a ha slack hslack,
      hBudget a ha slack hslack]
    with d hs2 hqpos_d hProfile_d hPureError_d hBackgroundTransfer_d
      hBackgroundError_d hMixed_d hMean_d hBudget_d
  have hs : 0 < R.sample d := lt_of_lt_of_le (by norm_num) hs2
  letI : IsProbabilityMeasure
      (_root_.PptFactorization.AppendixB.sphericalModelMeasure
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))) :=
    _root_.PptFactorization.AppendixB.sphericalModelMeasure_isProbabilityMeasure
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
  have hprob :
      (_root_.PptFactorization.AppendixB.sphericalModelMeasure
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))).real
        (sphericalOneColumnFavorableEvent
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (⟨0, hs⟩ : Fin (R.sample d))
          (betaColumnSpikeScale
            (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
          (lowerConcreteDelta a slack d)
          (lowerConcreteDirectionCapSet e a slack d)
          (backgroundTypicalSet
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            (lowerConcreteN d) (M a slack d) (τ a slack d)
            (center a slack d) k)) ≤
      (_root_.PptFactorization.AppendixB.sphericalModelMeasure
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))).real
        (columnMomentUpperTailSet
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (lowerConcreteN d) (eps d) (mean d) k) := by
    refine measureReal_mono ?_ (h₂ :=
      (measure_lt_top
        (_root_.PptFactorization.AppendixB.sphericalModelMeasure
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))) _).ne)
    intro X hX
    have hmass_lower :
        betaColumnSpikeScale
            (lowerConcreteN d : ℝ) (spikeSpeed k d) a ≤
          sampleColumnMass
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            X (⟨0, hs⟩ : Fin (R.sample d)) := by
      exact hX.1.1
    have hmass_pos :
        0 <
          sampleColumnMass
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            X (⟨0, hs⟩ : Fin (R.sample d)) :=
      lt_of_lt_of_le hqpos_d hmass_lower
    have hdir_unit :
        ‖sampleColumnDirection
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            X (⟨0, hs⟩ : Fin (R.sample d))‖ = 1 :=
      sampleColumnDirection_norm_eq_one_of_columnMass_pos
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        X (⟨0, hs⟩ : Fin (R.sample d)) hmass_pos
    have hProfileX :
        a ^ k - errProfile a slack d ≤
          columnDirectionSpikeProfile
            (p := Fin d) (q := Fin d)
            (lowerConcreteN d) k
            (sampleColumnMass
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              X (⟨0, hs⟩ : Fin (R.sample d)))
            (sampleColumnDirection
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              X (⟨0, hs⟩ : Fin (R.sample d))) :=
      hProfile_d
        (sampleColumnMass
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          X (⟨0, hs⟩ : Fin (R.sample d)))
        (sampleColumnDirection
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          X (⟨0, hs⟩ : Fin (R.sample d)))
        hX.1 hX.2.1 hdir_unit
    have hTransfer :
        columnDirectionSpikeProfile
            (p := Fin d) (q := Fin d)
            (lowerConcreteN d) k
            (sampleColumnMass
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              X (⟨0, hs⟩ : Fin (R.sample d)))
            (sampleColumnDirection
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              X (⟨0, hs⟩ : Fin (R.sample d))) - 0 ≤
          columnSpikeContribution
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            (lowerConcreteN d) k X (⟨0, hs⟩ : Fin (R.sample d)) :=
      columnSpikeContribution_transfer_noError
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        (α₀ := (⟨0, hs⟩ : Fin (R.sample d)))
        (N := lowerConcreteN d) (k := k) X
    have hSpike :
        a ^ k - errSpike a slack d ≤
          columnSpikeContribution
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            (lowerConcreteN d) k X (⟨0, hs⟩ : Fin (R.sample d)) := by
      linarith
    have hBackground :
        center a slack d - errBg a slack d ≤
          columnBackgroundContribution
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            (lowerConcreteN d) k X (⟨0, hs⟩ : Fin (R.sample d)) := by
      have hsmall :=
        columnBackgroundContribution_lower_of_normalizedDeletedBackground_typical
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (α₀ := (⟨0, hs⟩ : Fin (R.sample d)))
          (N := lowerConcreteN d) (M := M a slack d)
          (τ := τ a slack d) (center := center a slack d)
          (errScale := errScale a slack d) (k := k)
          (X := X) hX.2.2 (hBackgroundTransfer_d hs X hX.2.2)
      linarith
    have hMixedLower :
        -errMix a slack d ≤
          columnMixedRemainder
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            (lowerConcreteN d) k X (⟨0, hs⟩ : Fin (R.sample d)) :=
      (abs_le.mp (hMixed_d hs X hX)).1
    exact
      column_spike_event_deviation_of_background_mixed
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        (N := lowerConcreteN d) (a := a) (eps := eps d)
        (mean := mean d) (center := center a slack d)
        (errSpike := errSpike a slack d) (errBg := errBg a slack d)
        (errMix := errMix a slack d) (errMean := errMean a slack d)
        (k := k) (X := X) (α₀ := (⟨0, hs⟩ : Fin (R.sample d)))
        hSpike hBackground hMixedLower hMean_d hBudget_d
  simpa [lowerConcreteColumnProb, lowerConcreteTargetProb, hs] using hprob

/-- No-transfer pure spike error budget when the spike certificate error is
chosen to be the profile error itself. -/
theorem lower_concrete_hPureError_sameProfile
    {errProfile : ℝ → ℝ → ℕ → ℝ} {k : ℕ} {ε : ℝ} :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          errProfile a slack d + 0 ≤ errProfile a slack d := by
  intro a _ha slack _hslack
  exact Filter.Eventually.of_forall (fun d => by
    calc
      errProfile a slack d + 0 = errProfile a slack d := add_zero _
      _ ≤ errProfile a slack d := le_rfl)

/-- Scalar background error budget when the background certificate error is
chosen to be exactly `τ + errScale`. -/
theorem lower_concrete_hBackgroundError_sumScale
    {τ errScale : ℝ → ℝ → ℕ → ℝ} {k : ℕ} {ε : ℝ} :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          τ a slack d + errScale a slack d ≤
            τ a slack d + errScale a slack d := by
  intro a _ha slack _hslack
  exact Filter.Eventually.of_forall (fun _d => le_rfl)

/-- Mean comparison budget when the background centre is chosen to be the target
mean itself and the mean error is zero. -/
theorem lower_concrete_hMean_sameCenter
    {mean : ℕ → ℝ} {k : ℕ} {ε : ℝ} :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          mean d ≤ mean d + 0 := by
  intro _a _ha _slack _hslack
  exact Filter.Eventually.of_forall (fun d => by
    calc
      mean d = mean d + 0 := by rw [add_zero]
      _ ≤ mean d + 0 := le_rfl)

/-- The scalar scale-loss condition behind concrete background transfer.

It states exactly that the loss from replacing the normalized deleted background
moment by the unnormalized deleted-column contribution is absorbed by
`errScale`.  This is still a visible theorem assumption; it is not claimed here
as an automatic probabilistic estimate. -/
def lowerConcreteBackgroundScaleLoss
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (M τ center errScale : ℝ → ℝ → ℕ → ℝ) (k : ℕ) (ε : ℝ) : Prop :=
  ∀ a : ℝ, spikeRoot k ε < a →
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        ∀ hs : 0 < R.sample d,
          ∀ X : SampleMatrix (Fin d) (Fin d) (Fin (R.sample d)),
            sampleColumnComplementNormalized
                (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                X (⟨0, hs⟩ : Fin (R.sample d)) ∈
              backgroundTypicalSet
                (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                (lowerConcreteN d) (M a slack d) (τ a slack d)
                (center a slack d) k →
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
                errScale a slack d

/-- The concrete lower-side mixed-remainder condition.

The deterministic lower inclusion only needs the one-sided estimate
`-errMix ≤ mixed`; the stronger absolute envelope `|mixed| ≤ errMix` is useful
when supplied by word estimates, but it is not logically required for the lower
deviation event.  This condition is still a visible model input, not proved
unconditionally here. -/
def lowerConcreteMixedLowerBound
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
            -errMix a slack d ≤
              columnMixedRemainder
                (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                (lowerConcreteN d) k X (⟨0, hs⟩ : Fin (R.sample d))

/-- Concrete background transfer from the exact deleted-column scaling identity.

The remaining input is the scalar scale-loss inequality
`backgroundMoment * (1 - ‖X_{≠α₀}‖^(2k)) ≤ errScale`.  This theorem packages
that scalar inequality into the `hBackgroundTransfer` shape used by the
deterministic lower-bound inclusion. -/
theorem lower_concrete_hBackgroundTransfer_of_scaleLoss
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {M τ center errScale : ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hScaleLoss :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ hs : 0 < R.sample d,
              ∀ X : SampleMatrix (Fin d) (Fin d) (Fin (R.sample d)),
                sampleColumnComplementNormalized
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    X (⟨0, hs⟩ : Fin (R.sample d)) ∈
                  backgroundTypicalSet
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) (M a slack d) (τ a slack d)
                    (center a slack d) k →
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
                    errScale a slack d) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            ∀ X : SampleMatrix (Fin d) (Fin d) (Fin (R.sample d)),
              sampleColumnComplementNormalized
                  (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                  X (⟨0, hs⟩ : Fin (R.sample d)) ∈
                backgroundTypicalSet
                  (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                  (lowerConcreteN d) (M a slack d) (τ a slack d)
                  (center a slack d) k →
              backgroundMomentValue
                  (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                  (lowerConcreteN d) k
                  (sampleColumnComplementNormalized
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    X (⟨0, hs⟩ : Fin (R.sample d))) -
                  errScale a slack d ≤
                columnBackgroundContribution
                  (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                  (lowerConcreteN d) k X
                  (⟨0, hs⟩ : Fin (R.sample d)) := by
  intro a ha slack hslack
  filter_upwards [hScaleLoss a ha slack hslack] with d hScaleLoss_d
  intro hs X hTypical
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
  have hScale : B * (1 - T) ≤ errScale a slack d := by
    simpa [B, T, α₀] using hScaleLoss_d hs X hTypical
  have hEq :
      columnBackgroundContribution
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (lowerConcreteN d) k X α₀ =
        T * B := by
    simpa [B, T, α₀] using
      columnBackgroundContribution_eq_norm_pow_mul_backgroundMomentValue_normalized
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        (α₀ := α₀) (lowerConcreteN d) k X
  change B - errScale a slack d ≤
    columnBackgroundContribution
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
      (lowerConcreteN d) k X α₀
  rw [hEq]
  calc
    B - errScale a slack d ≤ B - B * (1 - T) := by linarith
    _ = T * B := by ring

/-- Deterministic concrete `hColumnIncluded` with no separate `hPureError`
parameter.

This keeps the stronger all-directions profile hypothesis from
`lower_concrete_hColumnIncluded_of_closed_deterministic_blocks`, but closes the
pure spike error budget by taking `errSpike := errProfile`. -/
theorem lower_concrete_hColumnIncluded_of_closed_deterministic_blocks_samePureError
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)))
    {eps mean : ℕ → ℝ}
    {M τ center errProfile errScale errBg errMix errMean :
      ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hProfile :
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
                u ∈ lowerConcreteDirectionCapSet e a slack d →
                a ^ k - errProfile a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hBackgroundTransfer :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ hs : 0 < R.sample d,
              ∀ X : SampleMatrix (Fin d) (Fin d) (Fin (R.sample d)),
                sampleColumnComplementNormalized
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    X (⟨0, hs⟩ : Fin (R.sample d)) ∈
                  backgroundTypicalSet
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) (M a slack d) (τ a slack d)
                    (center a slack d) k →
                backgroundMomentValue
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) k
                    (sampleColumnComplementNormalized
                      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                      X (⟨0, hs⟩ : Fin (R.sample d))) -
                    errScale a slack d ≤
                  columnBackgroundContribution
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) k X
                    (⟨0, hs⟩ : Fin (R.sample d)))
    (hBackgroundError :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            τ a slack d + errScale a slack d ≤ errBg a slack d)
    (hMixed :
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
                |columnMixedRemainder
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) k X
                    (⟨0, hs⟩ : Fin (R.sample d))| ≤
                  errMix a slack d)
    (hMean :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            mean d ≤ center a slack d + errMean a slack d)
    (hBudget :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            eps d + errProfile a slack d + errBg a slack d +
              errMix a slack d + errMean a slack d ≤ a ^ k) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          lowerConcreteColumnProb R e M τ center k a slack d ≤
            lowerConcreteTargetProb R eps mean k d := by
  exact
    lower_concrete_hColumnIncluded_of_closed_deterministic_blocks
      (R := R) (e := e) (eps := eps) (mean := mean)
      (M := M) (τ := τ) (center := center)
      (errProfile := errProfile) (errSpike := errProfile)
      (errScale := errScale) (errBg := errBg)
      (errMix := errMix) (errMean := errMean)
      (k := k) (ε := ε)
      hProfile
      (lower_concrete_hPureError_sameProfile
        (errProfile := errProfile) (k := k) (ε := ε))
      hBackgroundTransfer hBackgroundError hMixed hMean hBudget

/-- Concrete `hColumnIncluded` with unit-profile input and no separate
`hPureError` parameter.

This is the no-transfer specialization of
`lower_concrete_hColumnIncluded_of_closed_unitProfile`: the spike-side error
budget is closed by taking the certificate error to be `errProfile` itself. -/
theorem lower_concrete_hColumnIncluded_of_closed_unitProfile_samePureError
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)))
    {eps mean : ℕ → ℝ}
    {M τ center errProfile errScale errBg errMix errMean :
      ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hk : 0 < k) (hε : 0 < ε)
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
                u ∈ lowerConcreteDirectionCapSet e a slack d →
                ‖u‖ = 1 →
                a ^ k - errProfile a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hBackgroundTransfer :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ hs : 0 < R.sample d,
              ∀ X : SampleMatrix (Fin d) (Fin d) (Fin (R.sample d)),
                sampleColumnComplementNormalized
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    X (⟨0, hs⟩ : Fin (R.sample d)) ∈
                  backgroundTypicalSet
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) (M a slack d) (τ a slack d)
                    (center a slack d) k →
                backgroundMomentValue
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) k
                    (sampleColumnComplementNormalized
                      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                      X (⟨0, hs⟩ : Fin (R.sample d))) -
                    errScale a slack d ≤
                  columnBackgroundContribution
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) k X
                    (⟨0, hs⟩ : Fin (R.sample d)))
    (hBackgroundError :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            τ a slack d + errScale a slack d ≤ errBg a slack d)
    (hMixed :
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
                |columnMixedRemainder
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) k X
                    (⟨0, hs⟩ : Fin (R.sample d))| ≤
                  errMix a slack d)
    (hMean :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            mean d ≤ center a slack d + errMean a slack d)
    (hBudget :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            eps d + errProfile a slack d + errBg a slack d +
              errMix a slack d + errMean a slack d ≤ a ^ k) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          lowerConcreteColumnProb R e M τ center k a slack d ≤
            lowerConcreteTargetProb R eps mean k d := by
  exact
    lower_concrete_hColumnIncluded_of_closed_unitProfile
      (R := R) (e := e) (eps := eps) (mean := mean)
      (M := M) (τ := τ) (center := center)
      (errProfile := errProfile) (errSpike := errProfile)
      (errScale := errScale) (errBg := errBg)
      (errMix := errMix) (errMean := errMean)
      (k := k) (ε := ε) hk hε
      hUnitProfile
      (lower_concrete_hPureError_sameProfile
        (errProfile := errProfile) (k := k) (ε := ε))
      hBackgroundTransfer hBackgroundError hMixed hMean hBudget

set_option maxHeartbeats 800000 in
/-- Deterministic all-directions `hColumnIncluded` with `hPureError` closed and
`hBackgroundTransfer` reduced to the scalar background scale-loss condition. -/
theorem
    lower_concrete_hColumnIncluded_of_closed_deterministic_blocks_samePureError_backgroundScaleLoss
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)))
    {eps mean : ℕ → ℝ}
    {M τ center errProfile errScale errBg errMix errMean :
      ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hProfile :
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
                u ∈ lowerConcreteDirectionCapSet e a slack d →
                a ^ k - errProfile a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hScaleLoss :
      lowerConcreteBackgroundScaleLoss R M τ center errScale k ε)
    (hBackgroundError :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            τ a slack d + errScale a slack d ≤ errBg a slack d)
    (hMixed :
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
                |columnMixedRemainder
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) k X
                    (⟨0, hs⟩ : Fin (R.sample d))| ≤
                  errMix a slack d)
    (hMean :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            mean d ≤ center a slack d + errMean a slack d)
    (hBudget :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            eps d + errProfile a slack d + errBg a slack d +
              errMix a slack d + errMean a slack d ≤ a ^ k) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          lowerConcreteColumnProb R e M τ center k a slack d ≤
            lowerConcreteTargetProb R eps mean k d := by
  exact
    lower_concrete_hColumnIncluded_of_closed_deterministic_blocks_samePureError
      (R := R) (e := e) (eps := eps) (mean := mean)
      (M := M) (τ := τ) (center := center)
      (errProfile := errProfile)
      (errScale := errScale) (errBg := errBg)
      (errMix := errMix) (errMean := errMean)
      (k := k) (ε := ε)
      hProfile
      (lower_concrete_hBackgroundTransfer_of_scaleLoss
        (R := R) (M := M) (τ := τ) (center := center)
        (errScale := errScale) (k := k) (ε := ε)
        (by simpa [lowerConcreteBackgroundScaleLoss] using hScaleLoss))
      hBackgroundError hMixed hMean hBudget

set_option maxHeartbeats 800000 in
/-- Unit-profile concrete `hColumnIncluded` with `hPureError` closed and
`hBackgroundTransfer` reduced to the scalar background scale-loss condition. -/
theorem
    lower_concrete_hColumnIncluded_of_closed_unitProfile_samePureError_backgroundScaleLoss
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)))
    {eps mean : ℕ → ℝ}
    {M τ center errProfile errScale errBg errMix errMean :
      ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hk : 0 < k) (hε : 0 < ε)
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
                u ∈ lowerConcreteDirectionCapSet e a slack d →
                ‖u‖ = 1 →
                a ^ k - errProfile a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hScaleLoss :
      lowerConcreteBackgroundScaleLoss R M τ center errScale k ε)
    (hBackgroundError :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            τ a slack d + errScale a slack d ≤ errBg a slack d)
    (hMixed :
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
                |columnMixedRemainder
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) k X
                    (⟨0, hs⟩ : Fin (R.sample d))| ≤
                  errMix a slack d)
    (hMean :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            mean d ≤ center a slack d + errMean a slack d)
    (hBudget :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            eps d + errProfile a slack d + errBg a slack d +
              errMix a slack d + errMean a slack d ≤ a ^ k) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          lowerConcreteColumnProb R e M τ center k a slack d ≤
            lowerConcreteTargetProb R eps mean k d := by
  exact
    lower_concrete_hColumnIncluded_of_closed_unitProfile_samePureError
      (R := R) (e := e) (eps := eps) (mean := mean)
      (M := M) (τ := τ) (center := center)
      (errProfile := errProfile)
      (errScale := errScale) (errBg := errBg)
      (errMix := errMix) (errMean := errMean)
      (k := k) (ε := ε) hk hε
      hUnitProfile
      (lower_concrete_hBackgroundTransfer_of_scaleLoss
        (R := R) (M := M) (τ := τ) (center := center)
        (errScale := errScale) (k := k) (ε := ε)
        (by simpa [lowerConcreteBackgroundScaleLoss] using hScaleLoss))
      hBackgroundError hMixed hMean hBudget

set_option maxHeartbeats 800000 in
/-- Deterministic all-directions `hColumnIncluded` with `hPureError`,
`hBackgroundTransfer`, and `hBackgroundError` closed to explicit scalar
choices.

Here the background certificate error is specialized to `τ + errScale`, so the
remaining budget assumption displays that sum directly.  This is only scalar
bookkeeping: the profile, mixed, mean, scale-loss, and budget inputs remain
visible theorem parameters. -/
theorem
    lower_concrete_hColumnIncluded_of_closed_deterministic_blocks_samePureError_backgroundScaleLoss_sameBackgroundError
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)))
    {eps mean : ℕ → ℝ}
    {M τ center errProfile errScale errMix errMean :
      ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hProfile :
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
                u ∈ lowerConcreteDirectionCapSet e a slack d →
                a ^ k - errProfile a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hScaleLoss :
      lowerConcreteBackgroundScaleLoss R M τ center errScale k ε)
    (hMixed :
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
                |columnMixedRemainder
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) k X
                    (⟨0, hs⟩ : Fin (R.sample d))| ≤
                  errMix a slack d)
    (hMean :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            mean d ≤ center a slack d + errMean a slack d)
    (hBudget :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            eps d + errProfile a slack d +
                (τ a slack d + errScale a slack d) +
              errMix a slack d + errMean a slack d ≤ a ^ k) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          lowerConcreteColumnProb R e M τ center k a slack d ≤
            lowerConcreteTargetProb R eps mean k d := by
  exact
    lower_concrete_hColumnIncluded_of_closed_deterministic_blocks_samePureError_backgroundScaleLoss
      (R := R) (e := e) (eps := eps) (mean := mean)
      (M := M) (τ := τ) (center := center)
      (errProfile := errProfile)
      (errScale := errScale)
      (errBg := fun a slack d => τ a slack d + errScale a slack d)
      (errMix := errMix) (errMean := errMean)
      (k := k) (ε := ε)
      hProfile hScaleLoss
      (lower_concrete_hBackgroundError_sumScale
        (τ := τ) (errScale := errScale) (k := k) (ε := ε))
      hMixed hMean hBudget

set_option maxHeartbeats 800000 in
/-- Unit-profile `hColumnIncluded` with `hPureError`, `hBackgroundTransfer`,
and `hBackgroundError` closed to explicit scalar choices.

The background certificate error is fixed to `τ + errScale`; the remaining
budget hypothesis is therefore stated with that concrete sum. -/
theorem
    lower_concrete_hColumnIncluded_of_closed_unitProfile_samePureError_backgroundScaleLoss_sameBackgroundError
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)))
    {eps mean : ℕ → ℝ}
    {M τ center errProfile errScale errMix errMean :
      ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hk : 0 < k) (hε : 0 < ε)
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
                u ∈ lowerConcreteDirectionCapSet e a slack d →
                ‖u‖ = 1 →
                a ^ k - errProfile a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hScaleLoss :
      lowerConcreteBackgroundScaleLoss R M τ center errScale k ε)
    (hMixed :
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
                |columnMixedRemainder
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) k X
                    (⟨0, hs⟩ : Fin (R.sample d))| ≤
                  errMix a slack d)
    (hMean :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            mean d ≤ center a slack d + errMean a slack d)
    (hBudget :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            eps d + errProfile a slack d +
                (τ a slack d + errScale a slack d) +
              errMix a slack d + errMean a slack d ≤ a ^ k) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          lowerConcreteColumnProb R e M τ center k a slack d ≤
            lowerConcreteTargetProb R eps mean k d := by
  exact
    lower_concrete_hColumnIncluded_of_closed_unitProfile_samePureError_backgroundScaleLoss
      (R := R) (e := e) (eps := eps) (mean := mean)
      (M := M) (τ := τ) (center := center)
      (errProfile := errProfile)
      (errScale := errScale)
      (errBg := fun a slack d => τ a slack d + errScale a slack d)
      (errMix := errMix) (errMean := errMean)
      (k := k) (ε := ε) hk hε
      hUnitProfile hScaleLoss
      (lower_concrete_hBackgroundError_sumScale
        (τ := τ) (errScale := errScale) (k := k) (ε := ε))
      hMixed hMean hBudget

set_option maxHeartbeats 1000000 in
/-- Unit-profile `hColumnIncluded` with the mixed block weakened to the exact
one-sided lower estimate needed by the lower-bound event.

This closes the previous absolute-envelope-shaped `hMixed` parameter for this
endpoint.  The remaining mixed input is
`lowerConcreteMixedLowerBound`, namely `-errMix ≤ columnMixedRemainder` on the
favourable one-column event. -/
theorem
    lower_concrete_hColumnIncluded_of_closed_unitProfile_samePureError_backgroundScaleLoss_sameBackgroundError_mixedLowerBound
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)))
    {eps mean : ℕ → ℝ}
    {M τ center errProfile errScale errMix errMean :
      ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hk : 0 < k) (hε : 0 < ε)
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
                u ∈ lowerConcreteDirectionCapSet e a slack d →
                ‖u‖ = 1 →
                a ^ k - errProfile a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hScaleLoss :
      lowerConcreteBackgroundScaleLoss R M τ center errScale k ε)
    (hMixedLower :
      lowerConcreteMixedLowerBound R e M τ center errMix k ε)
    (hMean :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            mean d ≤ center a slack d + errMean a slack d)
    (hBudget :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            eps d + errProfile a slack d +
                (τ a slack d + errScale a slack d) +
              errMix a slack d + errMean a slack d ≤ a ^ k) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          lowerConcreteColumnProb R e M τ center k a slack d ≤
            lowerConcreteTargetProb R eps mean k d := by
  intro a ha slack hslack
  have hBackgroundTransfer :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ hs : 0 < R.sample d,
              ∀ X : SampleMatrix (Fin d) (Fin d) (Fin (R.sample d)),
                sampleColumnComplementNormalized
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    X (⟨0, hs⟩ : Fin (R.sample d)) ∈
                  backgroundTypicalSet
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) (M a slack d) (τ a slack d)
                    (center a slack d) k →
                backgroundMomentValue
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) k
                    (sampleColumnComplementNormalized
                      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                      X (⟨0, hs⟩ : Fin (R.sample d))) -
                    errScale a slack d ≤
                  columnBackgroundContribution
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) k X
                    (⟨0, hs⟩ : Fin (R.sample d)) :=
    lower_concrete_hBackgroundTransfer_of_scaleLoss
      (R := R) (M := M) (τ := τ) (center := center)
      (errScale := errScale) (k := k) (ε := ε)
      (by simpa [lowerConcreteBackgroundScaleLoss] using hScaleLoss)
  filter_upwards
    [lower_concrete_eventually_two_le_sample R,
      lower_concrete_hBetaScalePos (k := k) hk (ε := ε) hε a ha slack hslack,
      hUnitProfile a ha slack hslack,
      hBackgroundTransfer a ha slack hslack,
      hMixedLower a ha slack hslack,
      hMean a ha slack hslack,
      hBudget a ha slack hslack]
    with d hs2 hqpos_d hProfile_d hBackgroundTransfer_d hMixedLower_d
      hMean_d hBudget_d
  have hs : 0 < R.sample d := lt_of_lt_of_le (by norm_num) hs2
  letI : IsProbabilityMeasure
      (_root_.PptFactorization.AppendixB.sphericalModelMeasure
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))) :=
    _root_.PptFactorization.AppendixB.sphericalModelMeasure_isProbabilityMeasure
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
  have hprob :
      (_root_.PptFactorization.AppendixB.sphericalModelMeasure
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))).real
        (sphericalOneColumnFavorableEvent
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (⟨0, hs⟩ : Fin (R.sample d))
          (betaColumnSpikeScale
            (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
          (lowerConcreteDelta a slack d)
          (lowerConcreteDirectionCapSet e a slack d)
          (backgroundTypicalSet
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            (lowerConcreteN d) (M a slack d) (τ a slack d)
            (center a slack d) k)) ≤
      (_root_.PptFactorization.AppendixB.sphericalModelMeasure
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))).real
        (columnMomentUpperTailSet
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          (lowerConcreteN d) (eps d) (mean d) k) := by
    refine measureReal_mono ?_ (h₂ :=
      (measure_lt_top
        (_root_.PptFactorization.AppendixB.sphericalModelMeasure
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))) _).ne)
    intro X hX
    have hmass_lower :
        betaColumnSpikeScale
            (lowerConcreteN d : ℝ) (spikeSpeed k d) a ≤
          sampleColumnMass
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            X (⟨0, hs⟩ : Fin (R.sample d)) := by
      exact hX.1.1
    have hmass_pos :
        0 <
          sampleColumnMass
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            X (⟨0, hs⟩ : Fin (R.sample d)) :=
      lt_of_lt_of_le hqpos_d hmass_lower
    have hdir_unit :
        ‖sampleColumnDirection
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            X (⟨0, hs⟩ : Fin (R.sample d))‖ = 1 :=
      sampleColumnDirection_norm_eq_one_of_columnMass_pos
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        X (⟨0, hs⟩ : Fin (R.sample d)) hmass_pos
    have hProfileX :
        a ^ k - errProfile a slack d ≤
          columnDirectionSpikeProfile
            (p := Fin d) (q := Fin d)
            (lowerConcreteN d) k
            (sampleColumnMass
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              X (⟨0, hs⟩ : Fin (R.sample d)))
            (sampleColumnDirection
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              X (⟨0, hs⟩ : Fin (R.sample d))) :=
      hProfile_d
        (sampleColumnMass
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          X (⟨0, hs⟩ : Fin (R.sample d)))
        (sampleColumnDirection
          (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
          X (⟨0, hs⟩ : Fin (R.sample d)))
        hX.1 hX.2.1 hdir_unit
    have hTransfer :
        columnDirectionSpikeProfile
            (p := Fin d) (q := Fin d)
            (lowerConcreteN d) k
            (sampleColumnMass
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              X (⟨0, hs⟩ : Fin (R.sample d)))
            (sampleColumnDirection
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              X (⟨0, hs⟩ : Fin (R.sample d))) - 0 ≤
          columnSpikeContribution
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            (lowerConcreteN d) k X (⟨0, hs⟩ : Fin (R.sample d)) :=
      columnSpikeContribution_transfer_noError
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        (α₀ := (⟨0, hs⟩ : Fin (R.sample d)))
        (N := lowerConcreteN d) (k := k) X
    have hSpike :
        a ^ k - errProfile a slack d ≤
          columnSpikeContribution
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            (lowerConcreteN d) k X (⟨0, hs⟩ : Fin (R.sample d)) := by
      linarith
    have hBackground :
        center a slack d - (τ a slack d + errScale a slack d) ≤
          columnBackgroundContribution
            (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
            (lowerConcreteN d) k X (⟨0, hs⟩ : Fin (R.sample d)) :=
      columnBackgroundContribution_lower_of_normalizedDeletedBackground_typical
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        (α₀ := (⟨0, hs⟩ : Fin (R.sample d)))
        (N := lowerConcreteN d) (M := M a slack d)
        (τ := τ a slack d) (center := center a slack d)
        (errScale := errScale a slack d) (k := k)
        (X := X) hX.2.2 (hBackgroundTransfer_d hs X hX.2.2)
    exact
      column_spike_event_deviation_of_background_mixed
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
        (N := lowerConcreteN d) (a := a) (eps := eps d)
        (mean := mean d) (center := center a slack d)
        (errSpike := errProfile a slack d)
        (errBg := τ a slack d + errScale a slack d)
        (errMix := errMix a slack d) (errMean := errMean a slack d)
        (k := k) (X := X) (α₀ := (⟨0, hs⟩ : Fin (R.sample d)))
        hSpike hBackground (hMixedLower_d hs X hX) hMean_d hBudget_d
  simpa [lowerConcreteColumnProb, lowerConcreteTargetProb, hs] using hprob

set_option maxHeartbeats 1000000 in
/-- Unit-profile `hColumnIncluded` with the mean-comparison input closed by
choosing the background centre to be the target mean and the mean error to be
zero.

The remaining background and mixed assumptions are consequently stated with
`center a slack d = mean d`.  This is a canonical specialization of the
deterministic bookkeeping, not a proof of any background probabilistic estimate. -/
theorem
    lower_concrete_hColumnIncluded_of_closed_unitProfile_samePureError_backgroundScaleLoss_sameBackgroundError_mixedLowerBound_sameMean
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)))
    {eps mean : ℕ → ℝ}
    {M τ errProfile errScale errMix : ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hk : 0 < k) (hε : 0 < ε)
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
                u ∈ lowerConcreteDirectionCapSet e a slack d →
                ‖u‖ = 1 →
                a ^ k - errProfile a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hScaleLoss :
      lowerConcreteBackgroundScaleLoss R M τ
        (fun _a _slack d => mean d) errScale k ε)
    (hMixedLower :
      lowerConcreteMixedLowerBound R e M τ
        (fun _a _slack d => mean d) errMix k ε)
    (hBudget :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            eps d + errProfile a slack d +
                (τ a slack d + errScale a slack d) +
              errMix a slack d + 0 ≤ a ^ k) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          lowerConcreteColumnProb R e M τ
              (fun _a _slack d => mean d) k a slack d ≤
            lowerConcreteTargetProb R eps mean k d := by
  exact
    lower_concrete_hColumnIncluded_of_closed_unitProfile_samePureError_backgroundScaleLoss_sameBackgroundError_mixedLowerBound
      (R := R) (e := e) (eps := eps) (mean := mean)
      (M := M) (τ := τ) (center := fun _a _slack d => mean d)
      (errProfile := errProfile) (errScale := errScale)
      (errMix := errMix) (errMean := fun _a _slack _d => 0)
      (k := k) (ε := ε) hk hε
      hUnitProfile hScaleLoss hMixedLower
      (lower_concrete_hMean_sameCenter (mean := mean) (k := k) (ε := ε))
      hBudget

/-- The strict spike-radius condition gives the scalar gap needed by the final
one-column error budget.

This is only the algebraic consequence of
`spikeRoot k ε = ε^(1/k)`: under `0 < k` and `0 < ε`, any
`a > spikeRoot k ε` satisfies `ε < a^k`. -/
theorem lower_spikeRoot_lt_pow_gap
    {k : ℕ} (hk : 0 < k) {ε a : ℝ} (hε : 0 < ε)
    (ha : spikeRoot k ε < a) : ε < a ^ k := by
  have hroot_pos : 0 < spikeRoot k ε := spikeRoot_pos hk hε
  have hpow_lt : spikeRoot k ε ^ k < a ^ k :=
    pow_lt_pow_left₀ ha (le_of_lt hroot_pos) (ne_of_gt hk)
  have hroot_pow : spikeRoot k ε ^ k = ε := by
    unfold spikeRoot
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt hε)]
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
    field_simp [hkR]
    simp
  simpa [hroot_pow] using hpow_lt

/-- Concrete scalar supplier for the final deterministic error budget after
the mean centre has been specialized to the target mean.

The theorem closes the visible `hBudget` parameter from the previous endpoints
from four explicit scalar inputs: the target deviation sequence is eventually
bounded by the fixed deviation `ε`, and the profile, background scale terms,
and mixed error are all eventually smaller than any positive constant.  These
smallness assumptions remain theorem parameters; this wrapper does not prove
the model-specific asymptotics unconditionally. -/
theorem lower_concrete_hBudget_sameMean_of_eventual_small
    {eps : ℕ → ℝ}
    {errProfile τ errScale errMix : ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hk : 0 < k) (hε : 0 < ε)
    (hEpsLe : ∀ᶠ d in atTop, eps d ≤ ε)
    (hProfileSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errProfile a slack d ≤ η)
    (hTauSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, τ a slack d ≤ η)
    (hScaleSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errScale a slack d ≤ η)
    (hMixedSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errMix a slack d ≤ η) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          eps d + errProfile a slack d +
              (τ a slack d + errScale a slack d) +
            errMix a slack d + 0 ≤ a ^ k := by
  intro a ha slack hslack
  have hBackgroundSmall :
      ∀ η : ℝ, 0 < η →
        ∀ᶠ d in atTop,
          τ a slack d + errScale a slack d ≤ η := by
    intro η hη
    exact
      eventual_add_errors_le_of_eventual_small
        (e₁ := fun d => τ a slack d)
        (e₂ := fun d => errScale a slack d)
        (budget := η) hη
        (hTauSmall a ha slack hslack)
        (hScaleSmall a ha slack hslack)
  have hZeroSmall :
      ∀ η : ℝ, 0 < η →
        ∀ᶠ d in (atTop : Filter ℕ), (fun _d : ℕ => (0 : ℝ)) d ≤ η := by
    intro η hη
    exact Filter.Eventually.of_forall (fun _d => le_of_lt hη)
  have hBudgetConst :
      ∀ᶠ d in atTop,
        ε + errProfile a slack d +
            (τ a slack d + errScale a slack d) +
          errMix a slack d + (fun _d : ℕ => (0 : ℝ)) d ≤ a ^ k :=
    eventual_column_spike_error_budget_of_eventual_small
      (errSpike := fun d => errProfile a slack d)
      (errBg := fun d => τ a slack d + errScale a slack d)
      (errMix := fun d => errMix a slack d)
      (errMean := fun _d => (0 : ℝ))
      (eps := ε) (a := a) (k := k)
      (lower_spikeRoot_lt_pow_gap (k := k) hk (ε := ε) hε ha)
      (hProfileSmall a ha slack hslack)
      hBackgroundSmall
      (hMixedSmall a ha slack hslack)
      hZeroSmall
  filter_upwards [hEpsLe, hBudgetConst] with d hEps_d hBudget_d
  linarith

/-- Unit-profile deterministic inclusion with the final scalar budget supplied
by eventual-small error hypotheses.

This removes the explicit `hBudget` parameter from the previous `sameMean`
wrapper.  The replacement assumptions are still scalar model obligations:
eventual `eps d ≤ ε` and eventual smallness of the profile, `τ`, scale, and
mixed error terms. -/
theorem
    lower_concrete_hColumnIncluded_of_closed_unitProfile_samePureError_backgroundScaleLoss_sameBackgroundError_mixedLowerBound_sameMean_smallErrors
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)))
    {eps mean : ℕ → ℝ}
    {M τ errProfile errScale errMix : ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hk : 0 < k) (hε : 0 < ε)
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
                u ∈ lowerConcreteDirectionCapSet e a slack d →
                ‖u‖ = 1 →
                a ^ k - errProfile a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hScaleLoss :
      lowerConcreteBackgroundScaleLoss R M τ
        (fun _a _slack d => mean d) errScale k ε)
    (hMixedLower :
      lowerConcreteMixedLowerBound R e M τ
        (fun _a _slack d => mean d) errMix k ε)
    (hEpsLe : ∀ᶠ d in atTop, eps d ≤ ε)
    (hProfileSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errProfile a slack d ≤ η)
    (hTauSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, τ a slack d ≤ η)
    (hScaleSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errScale a slack d ≤ η)
    (hMixedSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errMix a slack d ≤ η) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          lowerConcreteColumnProb R e M τ
              (fun _a _slack d => mean d) k a slack d ≤
            lowerConcreteTargetProb R eps mean k d := by
  exact
    lower_concrete_hColumnIncluded_of_closed_unitProfile_samePureError_backgroundScaleLoss_sameBackgroundError_mixedLowerBound_sameMean
      (R := R) (e := e) (eps := eps) (mean := mean)
      (M := M) (τ := τ)
      (errProfile := errProfile) (errScale := errScale)
      (errMix := errMix) (k := k) (ε := ε) hk hε
      hUnitProfile hScaleLoss hMixedLower
      (lower_concrete_hBudget_sameMean_of_eventual_small
        (eps := eps) (errProfile := errProfile) (τ := τ)
        (errScale := errScale) (errMix := errMix)
        (k := k) (ε := ε) hk hε hEpsLe
        hProfileSmall hTauSmall hScaleSmall hMixedSmall)

/-- Shape-ratio limit for the concrete Beta one-minus exponent:
`(N_d (s_d - 1) - 1) / N_d^2 → λ`. -/
theorem lower_concrete_betaOtherShape_ratio_tendsto
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime) :
    Tendsto
      (fun d =>
        (((betaColumnOtherShape (lowerConcreteN d) (lowerConcreteS R d) -
            1 : ℕ) : ℝ) / ((lowerConcreteN d : ℝ) ^ 2)))
      atTop (nhds R.lam) := by
  have hd2_atTop :
      Tendsto (fun d : ℕ => (d : ℝ) ^ 2) atTop atTop := by
    simpa using
      ((tendsto_rpow_atTop (show (0 : ℝ) < 2 by norm_num)).comp
        (tendsto_natCast_atTop_atTop :
          Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop))
  have hd4_atTop :
      Tendsto (fun d : ℕ => (d : ℝ) ^ 4) atTop atTop := by
    simpa using
      ((tendsto_rpow_atTop (show (0 : ℝ) < 4 by norm_num)).comp
        (tendsto_natCast_atTop_atTop :
          Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop))
  have hone_div2 :
      Tendsto (fun d : ℕ => (1 : ℝ) / ((d : ℝ) ^ 2)) atTop
        (nhds 0) :=
    hd2_atTop.const_div_atTop 1
  have hone_div4 :
      Tendsto (fun d : ℕ => (1 : ℝ) / ((d : ℝ) ^ 4)) atTop
        (nhds 0) :=
    hd4_atTop.const_div_atTop 1
  have hmain :
      Tendsto
        (fun d : ℕ =>
          _root_.PptFactorization.AppendixB.ConcreteModel.sampleRatio
              R.sample d -
            (1 : ℝ) / ((d : ℝ) ^ 2) -
            (1 : ℝ) / ((d : ℝ) ^ 4))
        atTop (nhds R.lam) := by
    simpa using (R.ratio_tendsto.sub hone_div2).sub hone_div4
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop 0,
    lower_concrete_eventually_two_le_sample R] with d hd hs2
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hd2_nat_pos : 0 < d ^ 2 := by positivity
  have hs1 : 1 ≤ R.sample d := by omega
  have hprod_one : 1 ≤ d ^ 2 * (R.sample d - 1) := by
    have hs_sub_pos : 0 < R.sample d - 1 := by omega
    nlinarith [hd2_nat_pos, hs_sub_pos]
  unfold _root_.PptFactorization.AppendixB.ConcreteModel.sampleRatio
  simp [lowerConcreteN, lowerConcreteS, betaColumnOtherShape, Nat.cast_pow]
  rw [Nat.cast_sub hprod_one, Nat.cast_mul, Nat.cast_sub hs1]
  field_simp [ne_of_gt hdR]
  rw [Nat.cast_pow]
  ring

/-- Concrete model supplier for the lower pipeline's one-minus-Beta scalar
limit. -/
theorem lower_concrete_hOneMinusLimit
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} (hk : 1 < k) {ε : ℝ} :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        Tendsto
          (fun d =>
            ((((betaColumnOtherShape
                    (lowerConcreteN d) (lowerConcreteS R d) -
                  1 : ℕ) : ℝ) *
                betaColumnIntervalUpper
                  (betaColumnSpikeScale
                    (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                  (lowerConcreteDelta a slack d) /
                  (1 - betaColumnIntervalUpper
                    (betaColumnSpikeScale
                      (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                    (lowerConcreteDelta a slack d))) /
              spikeSpeed k d))
          atTop (nhds (R.lam * a)) := by
  intro a _ha slack _hslack
  let U : ℕ → ℝ := fun d =>
    betaColumnIntervalUpper
      (betaColumnSpikeScale
        (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
      (lowerConcreteDelta a slack d)
  have hU : Tendsto U atTop (nhds 0) := by
    have hfactor :
        Tendsto (fun d => 1 + lowerConcreteDelta a slack d) atTop
          (nhds 1) := by
      simpa using
        (tendsto_const_nhds.add
          (lower_concrete_delta_tendsto_zero (a := a) (slack := slack)))
    have hq :=
      lower_concrete_betaColumnSpikeScale_tendsto_zero
        (k := k) hk (a := a)
    simpa [U, betaColumnIntervalUpper, mul_comm, mul_left_comm, mul_assoc]
      using hfactor.mul hq
  have hfactor :
      Tendsto (fun d => 1 + lowerConcreteDelta a slack d) atTop
        (nhds 1) := by
    simpa using
      (tendsto_const_nhds.add
        (lower_concrete_delta_tendsto_zero (a := a) (slack := slack)))
  have hden : Tendsto (fun d => (1 - U d)⁻¹) atTop (nhds 1) := by
    have hsub : Tendsto (fun d => 1 - U d) atTop (nhds 1) := by
      simpa using tendsto_const_nhds.sub hU
    simpa using hsub.inv₀ (show (1 : ℝ) ≠ 0 by norm_num)
  have hright :
      Tendsto
        (fun d =>
          ((((betaColumnOtherShape
                  (lowerConcreteN d) (lowerConcreteS R d) -
                1 : ℕ) : ℝ) / ((lowerConcreteN d : ℝ) ^ 2)) *
            (a * (1 + lowerConcreteDelta a slack d)) * (1 - U d)⁻¹))
        atTop (nhds (R.lam * a)) := by
    have haFactor :
        Tendsto (fun d => a * (1 + lowerConcreteDelta a slack d)) atTop
          (nhds (a * 1)) :=
      tendsto_const_nhds.mul hfactor
    have hprod :=
      (lower_concrete_betaOtherShape_ratio_tendsto R).mul
        (haFactor.mul hden)
    simpa [mul_assoc, mul_comm, mul_left_comm] using hprod
  refine hright.congr' ?_
  filter_upwards [eventually_gt_atTop 0,
    lower_concrete_eventually_two_le_sample R,
    lower_concrete_hUpper (k := k) hk (ε := ε) a ‹spikeRoot k ε < a›
      slack ‹0 < slack›] with d hd hs2 hupper
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hspeed_pos : 0 < spikeSpeed k d := by
    simp [spikeSpeed, Real.rpow_pos_of_pos hdR]
  have hs1 : 1 ≤ R.sample d := by omega
  have hprod_one : 1 ≤ lowerConcreteN d * (lowerConcreteS R d - 1) := by
    have hNpos_nat : 0 < lowerConcreteN d := by
      simp [lowerConcreteN]
      positivity
    have hs_sub_pos : 0 < lowerConcreteS R d - 1 := by
      simp [lowerConcreteS]
      omega
    nlinarith [hNpos_nat, hs_sub_pos]
  have hden_ne : 1 - U d ≠ 0 := by
    have : U d ≠ 1 := by
      dsimp [U] at hupper ⊢
      linarith
    linarith
  simp [U, betaColumnSpikeScale, betaColumnIntervalUpper,
    betaColumnOtherShape, lowerConcreteN, lowerConcreteS, lowerConcreteDelta,
    spikeSpeed, Nat.cast_pow]
  have hprod_one' : 1 ≤ d ^ 2 * (R.sample d - 1) := by
    simpa [lowerConcreteN, lowerConcreteS] using hprod_one
  rw [Nat.cast_sub hprod_one', Nat.cast_mul, Nat.cast_sub hs1]
  field_simp [ne_of_gt hdR, ne_of_gt hspeed_pos, hden_ne]

/-- Concrete model supplier for the lower pipeline's cap-cost scalar limit. -/
theorem lower_concrete_hCapCostLimit {k : ℕ} (hk : 0 < k) :
    Tendsto
      (fun d => capNLogNCost 2 (lowerConcreteNcap d : ℝ) / spikeSpeed k d)
      atTop (nhds 0) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hexpSmall : 0 < (2 : ℝ) / (k : ℝ) := by positivity
  have hloglittle :
      Real.log =o[atTop] fun x : ℝ => x ^ ((2 : ℝ) / (k : ℝ)) :=
    isLittleO_log_rpow_atTop hexpSmall
  have hcomp :=
    hloglittle.comp_tendsto (k := fun d : ℕ => (d : ℝ))
      tendsto_natCast_atTop_atTop
  have hlimLog :
      Tendsto
        (fun d : ℕ =>
          Real.log (d : ℝ) / ((d : ℝ) ^ ((2 : ℝ) / (k : ℝ))))
        atTop (nhds 0) := by
    simpa [Function.comp_def] using hcomp.tendsto_div_nhds_zero
  have hlim4 :
      Tendsto
        (fun d : ℕ =>
          4 * (Real.log (d : ℝ) / ((d : ℝ) ^ ((2 : ℝ) / (k : ℝ)))))
        atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds.mul hlimLog :
        Tendsto
          (fun d : ℕ =>
            (4 : ℝ) *
              (Real.log (d : ℝ) / ((d : ℝ) ^ ((2 : ℝ) / (k : ℝ)))))
          atTop (nhds (4 * 0)))
  refine hlim4.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with d hd
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hpow :
      (d : ℝ) ^ (2 + (2 : ℝ) / (k : ℝ)) =
        (d : ℝ) ^ 2 * (d : ℝ) ^ ((2 : ℝ) / (k : ℝ)) := by
    simpa using (Real.rpow_add hdR (2 : ℝ) ((2 : ℝ) / (k : ℝ)))
  simp [lowerConcreteNcap, capNLogNCost, spikeSpeed, hpow, Real.log_pow]
  field_simp [ne_of_gt hdR,
    Real.rpow_pos_of_pos hdR ((2 : ℝ) / (k : ℝ))]
  ring

/-- Concrete-scalar lower-bound input constructor for the actual balanced
random-matrix regime.

This theorem plugs the actual model dimensions
`N_d = d^2`, `s_d = R.sample d`, `Ncap_d = d^2`, and the concrete interval
width `δ_d = d⁻¹` into the scalar-limits constructor.  Consequently, the only
remaining lower-bound assumptions are the five visible event/probability
inputs:

* `hColumnIncluded`, the one-column favourable event implies the target event;
* `hProduct`, the one-column probability product decomposition;
* `hBeta`, the Beta interval lower bound at the concrete `q` and `δ`;
* `hCap`, the projective cap lower bound;
* `hBackgroundHalf`, the deleted-background half-mass bound.

The strict moment-order hypothesis `1 < k` is the concrete scalar condition
ensuring the Beta interval upper endpoint eventually lies below `1`. -/
theorem lower_spikeInput_concreteScalars
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {targetProb : ℕ → ℝ}
    {betaProb capProb backgroundProb columnProb : ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hk : 1 < k) (hε : 0 < ε)
    (hColumnIncluded :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, columnProb a slack d ≤ targetProb d)
    (hProduct :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            columnProb a slack d =
              betaProb a slack d * capProb a slack d * backgroundProb a slack d)
    (hBeta :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            BetaColumnIntervalLowerBound
              (betaProb a slack d) (lowerConcreteN d) (lowerConcreteS R d)
              (betaColumnSpikeScale
                (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
              (lowerConcreteDelta a slack d))
    (hCap :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ProjectiveCapProbabilityLowerBound
              (capProb a slack d) (lowerConcreteNcap d)
              (1 / (lowerConcreteNcap d : ℝ)))
    (hBackgroundHalf :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, (1 / 2 : ℝ) ≤ backgroundProb a slack d) :
    SpikeLowerBoundInput targetProb k R.lam ε := by
  have hk0 : 0 < k := Nat.zero_lt_of_lt hk
  exact
    lower_spikeInput_of_oneColumn_scalarLimits
      (targetProb := targetProb)
      (betaProb := betaProb) (capProb := capProb)
      (backgroundProb := backgroundProb) (columnProb := columnProb)
      (N := lowerConcreteN) (s := lowerConcreteS R)
      (Ncap := lowerConcreteNcap) (δ := lowerConcreteDelta)
      (k := k) (lam := R.lam) (ε := ε)
      hk0 R.lam_pos hε hColumnIncluded hProduct hBeta
      (lower_concrete_hNpos (k := k) (ε := ε))
      (lower_concrete_hDeltaPos (k := k) (ε := ε))
      (lower_concrete_hUpper (k := k) hk (ε := ε))
      (lower_concrete_hDeltaLimit (k := k) hk0 (ε := ε))
      (lower_concrete_hEntropyLimit (k := k) hk0 (ε := ε) hε)
      (lower_concrete_hOneMinusLimit R (k := k) hk (ε := ε))
      lower_concrete_hNcap
      hCap
      (lower_concrete_hCapCostLimit (k := k) hk0)
      hBackgroundHalf

/-- Concrete-scalar lower-bound input constructor with the Beta ingredient
already closed for the varying `Fin d` model.

This is the concrete `hBeta` supplier requested downstream of
`lower_spikeInput_concreteScalars`: the generic scalar constructor is kept
unchanged, but once the Beta factor is the actual concrete probability
`lowerConcreteBetaProb R k`, the remaining visible inputs are only
`hColumnIncluded`, `hProduct`, `hCap`, and `hBackgroundHalf`.  The Beta lower
bound is discharged internally by `lower_concrete_hBeta`, which in turn uses
the concrete scalar side conditions already proved in this file. -/
theorem lower_spikeInput_concreteScalars_of_concreteBeta
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {targetProb : ℕ → ℝ}
    {capProb backgroundProb columnProb : ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hk : 1 < k) (hε : 0 < ε)
    (hColumnIncluded :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, columnProb a slack d ≤ targetProb d)
    (hProduct :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            columnProb a slack d =
              lowerConcreteBetaProb R k a slack d *
                capProb a slack d * backgroundProb a slack d)
    (hCap :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ProjectiveCapProbabilityLowerBound
              (capProb a slack d) (lowerConcreteNcap d)
              (1 / (lowerConcreteNcap d : ℝ)))
    (hBackgroundHalf :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, (1 / 2 : ℝ) ≤ backgroundProb a slack d) :
    SpikeLowerBoundInput targetProb k R.lam ε := by
  exact
    lower_spikeInput_concreteScalars
      (R := R) (targetProb := targetProb)
      (betaProb := lowerConcreteBetaProb R k)
      (capProb := capProb)
      (backgroundProb := backgroundProb)
      (columnProb := columnProb)
      (k := k) (ε := ε)
      hk hε hColumnIncluded hProduct
      (lower_concrete_hBeta (R := R) (k := k) hk (ε := ε) hε)
      hCap hBackgroundHalf

/-- Final lower exponent with all concrete scalar/asymptotic bookkeeping
discharged for a balanced concrete random-matrix regime.

The theorem deliberately leaves only the event/probability plumbing visible:
`hColumnIncluded`, `hProduct`, `hBeta`, `hCap`, and `hBackgroundHalf`. -/
theorem lower_eventual_log_over_spikeSpeed_concreteScalars
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {targetProb : ℕ → ℝ}
    {betaProb capProb backgroundProb columnProb : ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hk : 1 < k) (hε : 0 < ε)
    (hColumnIncluded :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, columnProb a slack d ≤ targetProb d)
    (hProduct :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            columnProb a slack d =
              betaProb a slack d * capProb a slack d * backgroundProb a slack d)
    (hBeta :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            BetaColumnIntervalLowerBound
              (betaProb a slack d) (lowerConcreteN d) (lowerConcreteS R d)
              (betaColumnSpikeScale
                (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
              (lowerConcreteDelta a slack d))
    (hCap :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ProjectiveCapProbabilityLowerBound
              (capProb a slack d) (lowerConcreteNcap d)
              (1 / (lowerConcreteNcap d : ℝ)))
    (hBackgroundHalf :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, (1 / 2 : ℝ) ≤ backgroundProb a slack d) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log (targetProb d) / spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_from_input
      (lower_spikeInput_concreteScalars
        (R := R) (targetProb := targetProb)
        (betaProb := betaProb) (capProb := capProb)
        (backgroundProb := backgroundProb) (columnProb := columnProb)
        (k := k) (ε := ε)
        hk hε hColumnIncluded hProduct hBeta hCap hBackgroundHalf)

/-- Final lower exponent for the varying concrete `Fin d` model after closing
the product, Beta, cap, background-half, and scalar/asymptotic bookkeeping.

The only remaining lower-bound inputs are deliberately visible:

* `hColumnIncluded`, the deterministic inclusion of the concrete one-column
  favourable event into the target upper-tail event;
* `hCoord`, the finite-dimensional projective cone-coordinate formula used to
  obtain the cap law;
* `hUnit`, the unit normalization of the chosen spike direction;
* `hBounds` and `hBad`, the deleted-background bad-set estimates and their
  `≤ 1/2` budget.

No claim is made here that those remaining inputs are automatic. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)))
    {eps mean : ℕ → ℝ}
    {M τ center bMoment bSample bGamma : ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hk : 1 < k) (hε : 0 < ε)
    (hColumnIncluded :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            lowerConcreteColumnProb R e M τ center k a slack d ≤
              lowerConcreteTargetProb R eps mean k d)
    (hCoord :
      ∀ᶠ d in atTop,
        SurfaceProjectiveCapConeCoordinateFormula
          (BipIndex (Fin d) (Fin d)))
    (hUnit :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, ‖e (a, slack, d)‖ = 1)
    (hBounds :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            DeletedColumnBackgroundBadSetBounds
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              (⟨0, hs⟩ : Fin (R.sample d))
              (lowerConcreteN d) (M a slack d) (τ a slack d)
              (center a slack d) (bMoment a slack d)
              (bSample a slack d) (bGamma a slack d) k)
    (hBad :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          bMoment a slack d + bSample a slack d + bGamma a slack d ≤ 1 / 2) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log (lowerConcreteTargetProb R eps mean k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteScalars
      (R := R)
      (targetProb := lowerConcreteTargetProb R eps mean k)
      (betaProb := lowerConcreteBetaProb R k)
      (capProb := lowerConcreteCapProb R e)
      (backgroundProb := lowerConcreteBackgroundProb R M τ center k)
      (columnProb := lowerConcreteColumnProb R e M τ center k)
      (k := k) (ε := ε)
      hk hε
      hColumnIncluded
      (lower_concrete_hProduct
        (R := R) (e := e) (M := M) (τ := τ) (center := center)
        (k := k) (root := spikeRoot k ε))
      (lower_concrete_hBeta (R := R) (k := k) hk (ε := ε) hε)
      (lower_concrete_hCap_of_surfaceCone
        (R := R) (e := e) (k := k) (ε := ε) hCoord hUnit)
      (lower_concrete_hBackgroundHalf
        (R := R) (M := M) (τ := τ) (center := center)
        (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
        (k := k) (ε := ε) hBounds hBad)

/-- Final concrete lower exponent with the full cone-coordinate assumption
reduced to the reference-centre cone formula.

The remaining geometric input is now the reference cone-volume identity in each
finite dimension.  The unitary-invariance transport to arbitrary cap centres is
closed by `lower_concrete_hCoord_of_referenceCone`. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_referenceCone
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)))
    {eps mean : ℕ → ℝ}
    {M τ center bMoment bSample bGamma : ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hk : 1 < k) (hε : 0 < ε)
    (hColumnIncluded :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            lowerConcreteColumnProb R e M τ center k a slack d ≤
              lowerConcreteTargetProb R eps mean k d)
    (hReference :
      ∀ᶠ d in atTop,
        ∀ i₀ : BipIndex (Fin d) (Fin d),
          SurfaceReferenceProjectiveCapConeCoordinateFormula
            (BipIndex (Fin d) (Fin d)) i₀)
    (hUnit :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, ‖e (a, slack, d)‖ = 1)
    (hBounds :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            DeletedColumnBackgroundBadSetBounds
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              (⟨0, hs⟩ : Fin (R.sample d))
              (lowerConcreteN d) (M a slack d) (τ a slack d)
              (center a slack d) (bMoment a slack d)
              (bSample a slack d) (bGamma a slack d) k)
    (hBad :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          bMoment a slack d + bSample a slack d + bGamma a slack d ≤ 1 / 2) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log (lowerConcreteTargetProb R eps mean k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel
      (R := R) (e := e) (eps := eps) (mean := mean)
      (M := M) (τ := τ) (center := center)
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (k := k) (ε := ε) hk hε hColumnIncluded
      (lower_concrete_hCoord_of_referenceCone hReference)
      hUnit hBounds hBad

/-- Final lower exponent for the canonical coordinate spike direction, with
`hCoord` reduced to the reference-centre cone formula.

This specialization removes the explicit `hUnit` assumption from
`lower_eventual_log_over_spikeSpeed_concreteModel_of_referenceCone`.  The
one-column inclusion and deleted-background bad-set estimates remain visible
inputs. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_referenceCone_canonicalDirection
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps mean : ℕ → ℝ}
    {M τ center bMoment bSample bGamma : ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hk : 1 < k) (hε : 0 < ε)
    (hColumnIncluded :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            lowerConcreteColumnProb R lowerConcreteCanonicalDirection
                M τ center k a slack d ≤
              lowerConcreteTargetProb R eps mean k d)
    (hReference :
      ∀ᶠ d in atTop,
        ∀ i₀ : BipIndex (Fin d) (Fin d),
          SurfaceReferenceProjectiveCapConeCoordinateFormula
            (BipIndex (Fin d) (Fin d)) i₀)
    (hBounds :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            DeletedColumnBackgroundBadSetBounds
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              (⟨0, hs⟩ : Fin (R.sample d))
              (lowerConcreteN d) (M a slack d) (τ a slack d)
              (center a slack d) (bMoment a slack d)
              (bSample a slack d) (bGamma a slack d) k)
    (hBad :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          bMoment a slack d + bSample a slack d + bGamma a slack d ≤ 1 / 2) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log (lowerConcreteTargetProb R eps mean k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_referenceCone
      (R := R) (e := lowerConcreteCanonicalDirection)
      (eps := eps) (mean := mean) (M := M) (τ := τ)
      (center := center) (bMoment := bMoment)
      (bSample := bSample) (bGamma := bGamma)
      (k := k) (ε := ε) hk hε hColumnIncluded hReference
      (lower_concrete_hUnit_canonicalDirection (k := k) (ε := ε))
      hBounds hBad

/-- Final lower exponent for the concrete `Fin d` model with
`hColumnIncluded` supplied by the closed deterministic one-column blocks.

This is the most bundled lower endpoint currently available in this closure
file.  It closes the scalar/asymptotic checks, product factorization, Beta
interval estimate, cap estimate, background half-mass estimate, and the
probability inclusion plumbing.  The remaining assumptions are precisely the
visible model-specific inputs: the deterministic spike/background/mixed/mean
budget estimates, the projective cone-coordinate and unit-direction facts, and
the deleted-background bad-set bounds. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_deterministic_blocks
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)))
    {eps mean : ℕ → ℝ}
    {M τ center bMoment bSample bGamma errProfile errSpike errScale errBg
      errMix errMean : ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hk : 1 < k) (hε : 0 < ε)
    (hProfile :
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
                u ∈ lowerConcreteDirectionCapSet e a slack d →
                a ^ k - errProfile a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hPureError :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            errProfile a slack d + 0 ≤ errSpike a slack d)
    (hBackgroundTransfer :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ hs : 0 < R.sample d,
              ∀ X : SampleMatrix (Fin d) (Fin d) (Fin (R.sample d)),
                sampleColumnComplementNormalized
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    X (⟨0, hs⟩ : Fin (R.sample d)) ∈
                  backgroundTypicalSet
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) (M a slack d) (τ a slack d)
                    (center a slack d) k →
                backgroundMomentValue
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) k
                    (sampleColumnComplementNormalized
                      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                      X (⟨0, hs⟩ : Fin (R.sample d))) -
                    errScale a slack d ≤
                  columnBackgroundContribution
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) k X
                    (⟨0, hs⟩ : Fin (R.sample d)))
    (hBackgroundError :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            τ a slack d + errScale a slack d ≤ errBg a slack d)
    (hMixed :
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
                |columnMixedRemainder
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) k X
                    (⟨0, hs⟩ : Fin (R.sample d))| ≤
                  errMix a slack d)
    (hMean :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            mean d ≤ center a slack d + errMean a slack d)
    (hBudget :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            eps d + errSpike a slack d + errBg a slack d +
              errMix a slack d + errMean a slack d ≤ a ^ k)
    (hCoord :
      ∀ᶠ d in atTop,
        SurfaceProjectiveCapConeCoordinateFormula
          (BipIndex (Fin d) (Fin d)))
    (hUnit :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, ‖e (a, slack, d)‖ = 1)
    (hBounds :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            DeletedColumnBackgroundBadSetBounds
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              (⟨0, hs⟩ : Fin (R.sample d))
              (lowerConcreteN d) (M a slack d) (τ a slack d)
              (center a slack d) (bMoment a slack d)
              (bSample a slack d) (bGamma a slack d) k)
    (hBad :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          bMoment a slack d + bSample a slack d + bGamma a slack d ≤ 1 / 2) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log (lowerConcreteTargetProb R eps mean k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel
      (R := R) (e := e) (eps := eps) (mean := mean)
      (M := M) (τ := τ) (center := center)
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (k := k) (ε := ε) hk hε
      (lower_concrete_hColumnIncluded_of_closed_deterministic_blocks
        (R := R) (e := e) (eps := eps) (mean := mean)
        (M := M) (τ := τ) (center := center)
        (errProfile := errProfile) (errSpike := errSpike)
        (errScale := errScale) (errBg := errBg)
        (errMix := errMix) (errMean := errMean)
        (k := k) (ε := ε)
        hProfile hPureError hBackgroundTransfer hBackgroundError
        hMixed hMean hBudget)
      hCoord hUnit hBounds hBad

/-- Final concrete lower exponent for the all-directions deterministic bridge,
with no separate `hPureError` parameter.

This is the `errSpike := errProfile` specialization of
`lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_deterministic_blocks`.
It does not prove the deterministic profile/background/mixed/mean estimates;
those remain explicit inputs. -/
theorem
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_deterministic_blocks_samePureError
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)))
    {eps mean : ℕ → ℝ}
    {M τ center bMoment bSample bGamma errProfile errScale errBg errMix
      errMean : ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hk : 1 < k) (hε : 0 < ε)
    (hProfile :
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
                u ∈ lowerConcreteDirectionCapSet e a slack d →
                a ^ k - errProfile a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hBackgroundTransfer :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ hs : 0 < R.sample d,
              ∀ X : SampleMatrix (Fin d) (Fin d) (Fin (R.sample d)),
                sampleColumnComplementNormalized
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    X (⟨0, hs⟩ : Fin (R.sample d)) ∈
                  backgroundTypicalSet
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) (M a slack d) (τ a slack d)
                    (center a slack d) k →
                backgroundMomentValue
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) k
                    (sampleColumnComplementNormalized
                      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                      X (⟨0, hs⟩ : Fin (R.sample d))) -
                    errScale a slack d ≤
                  columnBackgroundContribution
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) k X
                    (⟨0, hs⟩ : Fin (R.sample d)))
    (hBackgroundError :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            τ a slack d + errScale a slack d ≤ errBg a slack d)
    (hMixed :
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
                |columnMixedRemainder
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) k X
                    (⟨0, hs⟩ : Fin (R.sample d))| ≤
                  errMix a slack d)
    (hMean :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            mean d ≤ center a slack d + errMean a slack d)
    (hBudget :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            eps d + errProfile a slack d + errBg a slack d +
              errMix a slack d + errMean a slack d ≤ a ^ k)
    (hCoord :
      ∀ᶠ d in atTop,
        SurfaceProjectiveCapConeCoordinateFormula
          (BipIndex (Fin d) (Fin d)))
    (hUnit :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, ‖e (a, slack, d)‖ = 1)
    (hBounds :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            DeletedColumnBackgroundBadSetBounds
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              (⟨0, hs⟩ : Fin (R.sample d))
              (lowerConcreteN d) (M a slack d) (τ a slack d)
              (center a slack d) (bMoment a slack d)
              (bSample a slack d) (bGamma a slack d) k)
    (hBad :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          bMoment a slack d + bSample a slack d + bGamma a slack d ≤ 1 / 2) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log (lowerConcreteTargetProb R eps mean k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel
      (R := R) (e := e) (eps := eps) (mean := mean)
      (M := M) (τ := τ) (center := center)
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (k := k) (ε := ε) hk hε
      (lower_concrete_hColumnIncluded_of_closed_deterministic_blocks_samePureError
        (R := R) (e := e) (eps := eps) (mean := mean)
        (M := M) (τ := τ) (center := center)
        (errProfile := errProfile)
        (errScale := errScale) (errBg := errBg)
        (errMix := errMix) (errMean := errMean)
        (k := k) (ε := ε)
        hProfile hBackgroundTransfer hBackgroundError hMixed hMean hBudget)
      hCoord hUnit hBounds hBad

set_option maxHeartbeats 800000 in
/-- Final concrete lower exponent for the all-directions deterministic bridge,
with `hPureError` closed and `hBackgroundTransfer` replaced by the scalar
background scale-loss condition. -/
theorem
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_deterministic_blocks_samePureError_backgroundScaleLoss
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)))
    {eps mean : ℕ → ℝ}
    {M τ center bMoment bSample bGamma errProfile errScale errBg errMix
      errMean : ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hk : 1 < k) (hε : 0 < ε)
    (hProfile :
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
                u ∈ lowerConcreteDirectionCapSet e a slack d →
                a ^ k - errProfile a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hScaleLoss :
      lowerConcreteBackgroundScaleLoss R M τ center errScale k ε)
    (hBackgroundError :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            τ a slack d + errScale a slack d ≤ errBg a slack d)
    (hMixed :
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
                |columnMixedRemainder
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) k X
                    (⟨0, hs⟩ : Fin (R.sample d))| ≤
                  errMix a slack d)
    (hMean :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            mean d ≤ center a slack d + errMean a slack d)
    (hBudget :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            eps d + errProfile a slack d + errBg a slack d +
              errMix a slack d + errMean a slack d ≤ a ^ k)
    (hCoord :
      ∀ᶠ d in atTop,
        SurfaceProjectiveCapConeCoordinateFormula
          (BipIndex (Fin d) (Fin d)))
    (hUnit :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, ‖e (a, slack, d)‖ = 1)
    (hBounds :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            DeletedColumnBackgroundBadSetBounds
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              (⟨0, hs⟩ : Fin (R.sample d))
              (lowerConcreteN d) (M a slack d) (τ a slack d)
              (center a slack d) (bMoment a slack d)
              (bSample a slack d) (bGamma a slack d) k)
    (hBad :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          bMoment a slack d + bSample a slack d + bGamma a slack d ≤ 1 / 2) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log (lowerConcreteTargetProb R eps mean k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_deterministic_blocks_samePureError
      (R := R) (e := e) (eps := eps) (mean := mean)
      (M := M) (τ := τ) (center := center)
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (errProfile := errProfile)
      (errScale := errScale) (errBg := errBg)
      (errMix := errMix) (errMean := errMean)
      (k := k) (ε := ε) hk hε
      hProfile
      (lower_concrete_hBackgroundTransfer_of_scaleLoss
        (R := R) (M := M) (τ := τ) (center := center)
        (errScale := errScale) (k := k) (ε := ε)
        (by simpa [lowerConcreteBackgroundScaleLoss] using hScaleLoss))
      hBackgroundError hMixed hMean hBudget hCoord hUnit hBounds hBad

/-- Final concrete lower exponent using the unit-profile deterministic bridge.

This is the same bundled endpoint as
`lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_deterministic_blocks`,
but the spike-profile input is no longer stated for every ambient vector in the
cap.  It is required only for unit directions, which is exactly what the
positive Beta mass interval supplies for the actual sampled column direction. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_unitProfile
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)))
    {eps mean : ℕ → ℝ}
    {M τ center bMoment bSample bGamma errProfile errSpike errScale errBg
      errMix errMean : ℝ → ℝ → ℕ → ℝ}
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
                u ∈ lowerConcreteDirectionCapSet e a slack d →
                ‖u‖ = 1 →
                a ^ k - errProfile a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hPureError :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            errProfile a slack d + 0 ≤ errSpike a slack d)
    (hBackgroundTransfer :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ hs : 0 < R.sample d,
              ∀ X : SampleMatrix (Fin d) (Fin d) (Fin (R.sample d)),
                sampleColumnComplementNormalized
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    X (⟨0, hs⟩ : Fin (R.sample d)) ∈
                  backgroundTypicalSet
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) (M a slack d) (τ a slack d)
                    (center a slack d) k →
                backgroundMomentValue
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) k
                    (sampleColumnComplementNormalized
                      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                      X (⟨0, hs⟩ : Fin (R.sample d))) -
                    errScale a slack d ≤
                  columnBackgroundContribution
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) k X
                    (⟨0, hs⟩ : Fin (R.sample d)))
    (hBackgroundError :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            τ a slack d + errScale a slack d ≤ errBg a slack d)
    (hMixed :
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
                |columnMixedRemainder
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) k X
                    (⟨0, hs⟩ : Fin (R.sample d))| ≤
                  errMix a slack d)
    (hMean :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            mean d ≤ center a slack d + errMean a slack d)
    (hBudget :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            eps d + errSpike a slack d + errBg a slack d +
              errMix a slack d + errMean a slack d ≤ a ^ k)
    (hCoord :
      ∀ᶠ d in atTop,
        SurfaceProjectiveCapConeCoordinateFormula
          (BipIndex (Fin d) (Fin d)))
    (hUnit :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, ‖e (a, slack, d)‖ = 1)
    (hBounds :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            DeletedColumnBackgroundBadSetBounds
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              (⟨0, hs⟩ : Fin (R.sample d))
              (lowerConcreteN d) (M a slack d) (τ a slack d)
              (center a slack d) (bMoment a slack d)
              (bSample a slack d) (bGamma a slack d) k)
    (hBad :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          bMoment a slack d + bSample a slack d + bGamma a slack d ≤ 1 / 2) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log (lowerConcreteTargetProb R eps mean k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel
      (R := R) (e := e) (eps := eps) (mean := mean)
      (M := M) (τ := τ) (center := center)
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (k := k) (ε := ε) hk hε
      (lower_concrete_hColumnIncluded_of_closed_unitProfile
        (R := R) (e := e) (eps := eps) (mean := mean)
        (M := M) (τ := τ) (center := center)
        (errProfile := errProfile) (errSpike := errSpike)
        (errScale := errScale) (errBg := errBg)
        (errMix := errMix) (errMean := errMean)
        (k := k) (ε := ε)
        (Nat.zero_lt_of_lt hk) hε
        hUnitProfile hPureError hBackgroundTransfer hBackgroundError
        hMixed hMean hBudget)
      hCoord hUnit hBounds hBad

/-- Final concrete lower exponent with unit-profile input and no separate
`hPureError` parameter.

This endpoint specializes the spike certificate error to the profile error
itself, so the pure spike error budget is closed by
`lower_concrete_hPureError_sameProfile`.  The remaining deterministic and
probabilistic model inputs are still explicit theorem parameters. -/
theorem
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_unitProfile_samePureError
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)))
    {eps mean : ℕ → ℝ}
    {M τ center bMoment bSample bGamma errProfile errScale errBg errMix
      errMean : ℝ → ℝ → ℕ → ℝ}
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
                u ∈ lowerConcreteDirectionCapSet e a slack d →
                ‖u‖ = 1 →
                a ^ k - errProfile a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hBackgroundTransfer :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ hs : 0 < R.sample d,
              ∀ X : SampleMatrix (Fin d) (Fin d) (Fin (R.sample d)),
                sampleColumnComplementNormalized
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    X (⟨0, hs⟩ : Fin (R.sample d)) ∈
                  backgroundTypicalSet
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) (M a slack d) (τ a slack d)
                    (center a slack d) k →
                backgroundMomentValue
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) k
                    (sampleColumnComplementNormalized
                      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                      X (⟨0, hs⟩ : Fin (R.sample d))) -
                    errScale a slack d ≤
                  columnBackgroundContribution
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) k X
                    (⟨0, hs⟩ : Fin (R.sample d)))
    (hBackgroundError :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            τ a slack d + errScale a slack d ≤ errBg a slack d)
    (hMixed :
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
                |columnMixedRemainder
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) k X
                    (⟨0, hs⟩ : Fin (R.sample d))| ≤
                  errMix a slack d)
    (hMean :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            mean d ≤ center a slack d + errMean a slack d)
    (hBudget :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            eps d + errProfile a slack d + errBg a slack d +
              errMix a slack d + errMean a slack d ≤ a ^ k)
    (hCoord :
      ∀ᶠ d in atTop,
        SurfaceProjectiveCapConeCoordinateFormula
          (BipIndex (Fin d) (Fin d)))
    (hUnit :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, ‖e (a, slack, d)‖ = 1)
    (hBounds :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            DeletedColumnBackgroundBadSetBounds
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              (⟨0, hs⟩ : Fin (R.sample d))
              (lowerConcreteN d) (M a slack d) (τ a slack d)
              (center a slack d) (bMoment a slack d)
              (bSample a slack d) (bGamma a slack d) k)
    (hBad :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          bMoment a slack d + bSample a slack d + bGamma a slack d ≤ 1 / 2) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log (lowerConcreteTargetProb R eps mean k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_unitProfile
      (R := R) (e := e) (eps := eps) (mean := mean)
      (M := M) (τ := τ) (center := center)
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (errProfile := errProfile) (errSpike := errProfile)
      (errScale := errScale) (errBg := errBg)
      (errMix := errMix) (errMean := errMean)
      (k := k) (ε := ε) hk hε
      hUnitProfile
      (lower_concrete_hPureError_sameProfile
        (errProfile := errProfile) (k := k) (ε := ε))
      hBackgroundTransfer hBackgroundError hMixed hMean hBudget
      hCoord hUnit hBounds hBad

set_option maxHeartbeats 800000 in
/-- Final concrete lower exponent for the unit-profile deterministic bridge,
with `hPureError` closed and `hBackgroundTransfer` replaced by the scalar
background scale-loss condition. -/
theorem
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_unitProfile_samePureError_backgroundScaleLoss
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)))
    {eps mean : ℕ → ℝ}
    {M τ center bMoment bSample bGamma errProfile errScale errBg errMix
      errMean : ℝ → ℝ → ℕ → ℝ}
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
                u ∈ lowerConcreteDirectionCapSet e a slack d →
                ‖u‖ = 1 →
                a ^ k - errProfile a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hScaleLoss :
      lowerConcreteBackgroundScaleLoss R M τ center errScale k ε)
    (hBackgroundError :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            τ a slack d + errScale a slack d ≤ errBg a slack d)
    (hMixed :
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
                |columnMixedRemainder
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) k X
                    (⟨0, hs⟩ : Fin (R.sample d))| ≤
                  errMix a slack d)
    (hMean :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            mean d ≤ center a slack d + errMean a slack d)
    (hBudget :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            eps d + errProfile a slack d + errBg a slack d +
              errMix a slack d + errMean a slack d ≤ a ^ k)
    (hCoord :
      ∀ᶠ d in atTop,
        SurfaceProjectiveCapConeCoordinateFormula
          (BipIndex (Fin d) (Fin d)))
    (hUnit :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, ‖e (a, slack, d)‖ = 1)
    (hBounds :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            DeletedColumnBackgroundBadSetBounds
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              (⟨0, hs⟩ : Fin (R.sample d))
              (lowerConcreteN d) (M a slack d) (τ a slack d)
              (center a slack d) (bMoment a slack d)
              (bSample a slack d) (bGamma a slack d) k)
    (hBad :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          bMoment a slack d + bSample a slack d + bGamma a slack d ≤ 1 / 2) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log (lowerConcreteTargetProb R eps mean k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_unitProfile_samePureError
      (R := R) (e := e) (eps := eps) (mean := mean)
      (M := M) (τ := τ) (center := center)
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (errProfile := errProfile)
      (errScale := errScale) (errBg := errBg)
      (errMix := errMix) (errMean := errMean)
      (k := k) (ε := ε) hk hε
      hUnitProfile
      (lower_concrete_hBackgroundTransfer_of_scaleLoss
        (R := R) (M := M) (τ := τ) (center := center)
        (errScale := errScale) (k := k) (ε := ε)
        (by simpa [lowerConcreteBackgroundScaleLoss] using hScaleLoss))
      hBackgroundError hMixed hMean hBudget hCoord hUnit hBounds hBad

set_option maxHeartbeats 800000 in
/-- Final concrete lower exponent for the all-directions deterministic bridge,
with `hPureError`, `hBackgroundTransfer`, and `hBackgroundError` closed to
explicit scalar choices.

The background certificate error is specialized to `τ + errScale`.  The theorem
still exposes the model-specific profile, mixed, mean, scale-loss, bad-set, cap,
and budget assumptions; it does not claim those inputs unconditionally. -/
theorem
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_deterministic_blocks_samePureError_backgroundScaleLoss_sameBackgroundError
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)))
    {eps mean : ℕ → ℝ}
    {M τ center bMoment bSample bGamma errProfile errScale errMix
      errMean : ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hk : 1 < k) (hε : 0 < ε)
    (hProfile :
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
                u ∈ lowerConcreteDirectionCapSet e a slack d →
                a ^ k - errProfile a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hScaleLoss :
      lowerConcreteBackgroundScaleLoss R M τ center errScale k ε)
    (hMixed :
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
                |columnMixedRemainder
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) k X
                    (⟨0, hs⟩ : Fin (R.sample d))| ≤
                  errMix a slack d)
    (hMean :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            mean d ≤ center a slack d + errMean a slack d)
    (hBudget :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            eps d + errProfile a slack d +
                (τ a slack d + errScale a slack d) +
              errMix a slack d + errMean a slack d ≤ a ^ k)
    (hCoord :
      ∀ᶠ d in atTop,
        SurfaceProjectiveCapConeCoordinateFormula
          (BipIndex (Fin d) (Fin d)))
    (hUnit :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, ‖e (a, slack, d)‖ = 1)
    (hBounds :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            DeletedColumnBackgroundBadSetBounds
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              (⟨0, hs⟩ : Fin (R.sample d))
              (lowerConcreteN d) (M a slack d) (τ a slack d)
              (center a slack d) (bMoment a slack d)
              (bSample a slack d) (bGamma a slack d) k)
    (hBad :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          bMoment a slack d + bSample a slack d + bGamma a slack d ≤ 1 / 2) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log (lowerConcreteTargetProb R eps mean k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_deterministic_blocks_samePureError_backgroundScaleLoss
      (R := R) (e := e) (eps := eps) (mean := mean)
      (M := M) (τ := τ) (center := center)
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (errProfile := errProfile)
      (errScale := errScale)
      (errBg := fun a slack d => τ a slack d + errScale a slack d)
      (errMix := errMix) (errMean := errMean)
      (k := k) (ε := ε) hk hε
      hProfile hScaleLoss
      (lower_concrete_hBackgroundError_sumScale
        (τ := τ) (errScale := errScale) (k := k) (ε := ε))
      hMixed hMean hBudget hCoord hUnit hBounds hBad

set_option maxHeartbeats 800000 in
/-- Final concrete lower exponent for the unit-profile deterministic bridge,
with `hPureError`, `hBackgroundTransfer`, and `hBackgroundError` closed to
explicit scalar choices.

The background certificate error is specialized to `τ + errScale`.  The
remaining profile, mixed, mean, scale-loss, bad-set, cap, and budget inputs are
still explicit theorem parameters. -/
theorem
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_unitProfile_samePureError_backgroundScaleLoss_sameBackgroundError
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)))
    {eps mean : ℕ → ℝ}
    {M τ center bMoment bSample bGamma errProfile errScale errMix
      errMean : ℝ → ℝ → ℕ → ℝ}
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
                u ∈ lowerConcreteDirectionCapSet e a slack d →
                ‖u‖ = 1 →
                a ^ k - errProfile a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hScaleLoss :
      lowerConcreteBackgroundScaleLoss R M τ center errScale k ε)
    (hMixed :
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
                |columnMixedRemainder
                    (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
                    (lowerConcreteN d) k X
                    (⟨0, hs⟩ : Fin (R.sample d))| ≤
                  errMix a slack d)
    (hMean :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            mean d ≤ center a slack d + errMean a slack d)
    (hBudget :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            eps d + errProfile a slack d +
                (τ a slack d + errScale a slack d) +
              errMix a slack d + errMean a slack d ≤ a ^ k)
    (hCoord :
      ∀ᶠ d in atTop,
        SurfaceProjectiveCapConeCoordinateFormula
          (BipIndex (Fin d) (Fin d)))
    (hUnit :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, ‖e (a, slack, d)‖ = 1)
    (hBounds :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            DeletedColumnBackgroundBadSetBounds
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              (⟨0, hs⟩ : Fin (R.sample d))
              (lowerConcreteN d) (M a slack d) (τ a slack d)
              (center a slack d) (bMoment a slack d)
              (bSample a slack d) (bGamma a slack d) k)
    (hBad :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          bMoment a slack d + bSample a slack d + bGamma a slack d ≤ 1 / 2) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log (lowerConcreteTargetProb R eps mean k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_unitProfile_samePureError_backgroundScaleLoss
      (R := R) (e := e) (eps := eps) (mean := mean)
      (M := M) (τ := τ) (center := center)
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (errProfile := errProfile)
      (errScale := errScale)
      (errBg := fun a slack d => τ a slack d + errScale a slack d)
      (errMix := errMix) (errMean := errMean)
      (k := k) (ε := ε) hk hε
      hUnitProfile hScaleLoss
      (lower_concrete_hBackgroundError_sumScale
        (τ := τ) (errScale := errScale) (k := k) (ε := ε))
      hMixed hMean hBudget hCoord hUnit hBounds hBad

set_option maxHeartbeats 1000000 in
/-- Final concrete lower exponent for the all-directions deterministic bridge,
with the mixed input weakened to the one-sided lower estimate actually needed.

Compared with the previous `sameBackgroundError` endpoint, the absolute
envelope-shaped `hMixed` parameter is replaced by
`lowerConcreteMixedLowerBound`.  That lower mixed estimate remains a visible
model-specific assumption. -/
theorem
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_deterministic_blocks_samePureError_backgroundScaleLoss_sameBackgroundError_mixedLowerBound
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)))
    {eps mean : ℕ → ℝ}
    {M τ center bMoment bSample bGamma errProfile errScale errMix
      errMean : ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hk : 1 < k) (hε : 0 < ε)
    (hProfile :
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
                u ∈ lowerConcreteDirectionCapSet e a slack d →
                a ^ k - errProfile a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hScaleLoss :
      lowerConcreteBackgroundScaleLoss R M τ center errScale k ε)
    (hMixedLower :
      lowerConcreteMixedLowerBound R e M τ center errMix k ε)
    (hMean :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            mean d ≤ center a slack d + errMean a slack d)
    (hBudget :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            eps d + errProfile a slack d +
                (τ a slack d + errScale a slack d) +
              errMix a slack d + errMean a slack d ≤ a ^ k)
    (hCoord :
      ∀ᶠ d in atTop,
        SurfaceProjectiveCapConeCoordinateFormula
          (BipIndex (Fin d) (Fin d)))
    (hUnit :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, ‖e (a, slack, d)‖ = 1)
    (hBounds :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            DeletedColumnBackgroundBadSetBounds
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              (⟨0, hs⟩ : Fin (R.sample d))
              (lowerConcreteN d) (M a slack d) (τ a slack d)
              (center a slack d) (bMoment a slack d)
              (bSample a slack d) (bGamma a slack d) k)
    (hBad :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          bMoment a slack d + bSample a slack d + bGamma a slack d ≤ 1 / 2) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log (lowerConcreteTargetProb R eps mean k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel
      (R := R) (e := e) (eps := eps) (mean := mean)
      (M := M) (τ := τ) (center := center)
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (k := k) (ε := ε) hk hε
      (lower_concrete_hColumnIncluded_of_closed_unitProfile_samePureError_backgroundScaleLoss_sameBackgroundError_mixedLowerBound
        (R := R) (e := e) (eps := eps) (mean := mean)
        (M := M) (τ := τ) (center := center)
        (errProfile := errProfile) (errScale := errScale)
        (errMix := errMix) (errMean := errMean)
        (k := k) (ε := ε) (Nat.zero_lt_of_lt hk) hε
        (by
          intro a ha slack hslack
          filter_upwards [hProfile a ha slack hslack] with d hProfile_d
          intro Rmass u hMass hCap _hUnit
          exact hProfile_d Rmass u hMass hCap)
        hScaleLoss hMixedLower hMean hBudget)
      hCoord hUnit hBounds hBad

set_option maxHeartbeats 1000000 in
/-- Final concrete lower exponent for the unit-profile deterministic bridge,
with the mixed input weakened to the one-sided lower estimate actually needed.

This is the most economical deterministic lower-side endpoint in this file:
`hPureError`, `hBackgroundTransfer`, and `hBackgroundError` are closed by scalar
choices, while the mixed block is exposed only as
`lowerConcreteMixedLowerBound`. -/
theorem
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_unitProfile_samePureError_backgroundScaleLoss_sameBackgroundError_mixedLowerBound
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)))
    {eps mean : ℕ → ℝ}
    {M τ center bMoment bSample bGamma errProfile errScale errMix
      errMean : ℝ → ℝ → ℕ → ℝ}
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
                u ∈ lowerConcreteDirectionCapSet e a slack d →
                ‖u‖ = 1 →
                a ^ k - errProfile a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hScaleLoss :
      lowerConcreteBackgroundScaleLoss R M τ center errScale k ε)
    (hMixedLower :
      lowerConcreteMixedLowerBound R e M τ center errMix k ε)
    (hMean :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            mean d ≤ center a slack d + errMean a slack d)
    (hBudget :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            eps d + errProfile a slack d +
                (τ a slack d + errScale a slack d) +
              errMix a slack d + errMean a slack d ≤ a ^ k)
    (hCoord :
      ∀ᶠ d in atTop,
        SurfaceProjectiveCapConeCoordinateFormula
          (BipIndex (Fin d) (Fin d)))
    (hUnit :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, ‖e (a, slack, d)‖ = 1)
    (hBounds :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            DeletedColumnBackgroundBadSetBounds
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              (⟨0, hs⟩ : Fin (R.sample d))
              (lowerConcreteN d) (M a slack d) (τ a slack d)
              (center a slack d) (bMoment a slack d)
              (bSample a slack d) (bGamma a slack d) k)
    (hBad :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          bMoment a slack d + bSample a slack d + bGamma a slack d ≤ 1 / 2) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log (lowerConcreteTargetProb R eps mean k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel
      (R := R) (e := e) (eps := eps) (mean := mean)
      (M := M) (τ := τ) (center := center)
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (k := k) (ε := ε) hk hε
      (lower_concrete_hColumnIncluded_of_closed_unitProfile_samePureError_backgroundScaleLoss_sameBackgroundError_mixedLowerBound
        (R := R) (e := e) (eps := eps) (mean := mean)
        (M := M) (τ := τ) (center := center)
        (errProfile := errProfile) (errScale := errScale)
        (errMix := errMix) (errMean := errMean)
        (k := k) (ε := ε) (Nat.zero_lt_of_lt hk) hε
        hUnitProfile hScaleLoss hMixedLower hMean hBudget)
      hCoord hUnit hBounds hBad

set_option maxHeartbeats 1000000 in
/-- Final concrete lower exponent for the all-directions deterministic bridge,
with the mean-comparison input closed by taking the background centre to be the
target mean and the mean error to be zero.

The remaining background scale-loss, mixed lower-bound, bad-set, and budget
assumptions are stated with that specialized centre `mean d`. -/
theorem
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_deterministic_blocks_samePureError_backgroundScaleLoss_sameBackgroundError_mixedLowerBound_sameMean
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)))
    {eps mean : ℕ → ℝ}
    {M τ bMoment bSample bGamma errProfile errScale errMix :
      ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hk : 1 < k) (hε : 0 < ε)
    (hProfile :
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
                u ∈ lowerConcreteDirectionCapSet e a slack d →
                a ^ k - errProfile a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hScaleLoss :
      lowerConcreteBackgroundScaleLoss R M τ
        (fun _a _slack d => mean d) errScale k ε)
    (hMixedLower :
      lowerConcreteMixedLowerBound R e M τ
        (fun _a _slack d => mean d) errMix k ε)
    (hBudget :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            eps d + errProfile a slack d +
                (τ a slack d + errScale a slack d) +
              errMix a slack d + 0 ≤ a ^ k)
    (hCoord :
      ∀ᶠ d in atTop,
        SurfaceProjectiveCapConeCoordinateFormula
          (BipIndex (Fin d) (Fin d)))
    (hUnit :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, ‖e (a, slack, d)‖ = 1)
    (hBounds :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            DeletedColumnBackgroundBadSetBounds
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              (⟨0, hs⟩ : Fin (R.sample d))
              (lowerConcreteN d) (M a slack d) (τ a slack d)
              (mean d) (bMoment a slack d)
              (bSample a slack d) (bGamma a slack d) k)
    (hBad :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          bMoment a slack d + bSample a slack d + bGamma a slack d ≤ 1 / 2) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log (lowerConcreteTargetProb R eps mean k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_deterministic_blocks_samePureError_backgroundScaleLoss_sameBackgroundError_mixedLowerBound
      (R := R) (e := e) (eps := eps) (mean := mean)
      (M := M) (τ := τ) (center := fun _a _slack d => mean d)
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (errProfile := errProfile) (errScale := errScale)
      (errMix := errMix) (errMean := fun _a _slack _d => 0)
      (k := k) (ε := ε) hk hε
      hProfile hScaleLoss hMixedLower
      (lower_concrete_hMean_sameCenter (mean := mean) (k := k) (ε := ε))
      hBudget hCoord hUnit hBounds hBad

set_option maxHeartbeats 1000000 in
/-- Final concrete lower exponent for the unit-profile deterministic bridge,
with the mean-comparison input closed by taking the background centre to be the
target mean and the mean error to be zero.

This endpoint removes the separate `hMean` parameter.  It still assumes the
specialized background scale-loss, mixed lower-bound, bad-set, cap, unit-profile,
and scalar budget inputs. -/
theorem
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_unitProfile_samePureError_backgroundScaleLoss_sameBackgroundError_mixedLowerBound_sameMean
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)))
    {eps mean : ℕ → ℝ}
    {M τ bMoment bSample bGamma errProfile errScale errMix :
      ℝ → ℝ → ℕ → ℝ}
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
                u ∈ lowerConcreteDirectionCapSet e a slack d →
                ‖u‖ = 1 →
                a ^ k - errProfile a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hScaleLoss :
      lowerConcreteBackgroundScaleLoss R M τ
        (fun _a _slack d => mean d) errScale k ε)
    (hMixedLower :
      lowerConcreteMixedLowerBound R e M τ
        (fun _a _slack d => mean d) errMix k ε)
    (hBudget :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            eps d + errProfile a slack d +
                (τ a slack d + errScale a slack d) +
              errMix a slack d + 0 ≤ a ^ k)
    (hCoord :
      ∀ᶠ d in atTop,
        SurfaceProjectiveCapConeCoordinateFormula
          (BipIndex (Fin d) (Fin d)))
    (hUnit :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, ‖e (a, slack, d)‖ = 1)
    (hBounds :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            DeletedColumnBackgroundBadSetBounds
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              (⟨0, hs⟩ : Fin (R.sample d))
              (lowerConcreteN d) (M a slack d) (τ a slack d)
              (mean d) (bMoment a slack d)
              (bSample a slack d) (bGamma a slack d) k)
    (hBad :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          bMoment a slack d + bSample a slack d + bGamma a slack d ≤ 1 / 2) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log (lowerConcreteTargetProb R eps mean k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_unitProfile_samePureError_backgroundScaleLoss_sameBackgroundError_mixedLowerBound
      (R := R) (e := e) (eps := eps) (mean := mean)
      (M := M) (τ := τ) (center := fun _a _slack d => mean d)
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (errProfile := errProfile) (errScale := errScale)
      (errMix := errMix) (errMean := fun _a _slack _d => 0)
      (k := k) (ε := ε) hk hε
      hUnitProfile hScaleLoss hMixedLower
      (lower_concrete_hMean_sameCenter (mean := mean) (k := k) (ε := ε))
      hBudget hCoord hUnit hBounds hBad

set_option maxHeartbeats 1000000 in
/-- Final concrete lower exponent for the all-directions deterministic bridge,
with `hBudget` supplied by eventual-small scalar error estimates.

This wrapper removes the raw budget inequality from the signature.  The
remaining scalar obligations are the explicit ones needed to build it:
eventual `eps d ≤ ε` and eventual smallness of the profile error, `τ`, scale
error, and mixed error. -/
theorem
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_deterministic_blocks_samePureError_backgroundScaleLoss_sameBackgroundError_mixedLowerBound_sameMean_smallErrors
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)))
    {eps mean : ℕ → ℝ}
    {M τ bMoment bSample bGamma errProfile errScale errMix :
      ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hk : 1 < k) (hε : 0 < ε)
    (hProfile :
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
                u ∈ lowerConcreteDirectionCapSet e a slack d →
                a ^ k - errProfile a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hScaleLoss :
      lowerConcreteBackgroundScaleLoss R M τ
        (fun _a _slack d => mean d) errScale k ε)
    (hMixedLower :
      lowerConcreteMixedLowerBound R e M τ
        (fun _a _slack d => mean d) errMix k ε)
    (hEpsLe : ∀ᶠ d in atTop, eps d ≤ ε)
    (hProfileSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errProfile a slack d ≤ η)
    (hTauSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, τ a slack d ≤ η)
    (hScaleSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errScale a slack d ≤ η)
    (hMixedSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errMix a slack d ≤ η)
    (hCoord :
      ∀ᶠ d in atTop,
        SurfaceProjectiveCapConeCoordinateFormula
          (BipIndex (Fin d) (Fin d)))
    (hUnit :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, ‖e (a, slack, d)‖ = 1)
    (hBounds :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            DeletedColumnBackgroundBadSetBounds
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              (⟨0, hs⟩ : Fin (R.sample d))
              (lowerConcreteN d) (M a slack d) (τ a slack d)
              (mean d) (bMoment a slack d)
              (bSample a slack d) (bGamma a slack d) k)
    (hBad :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          bMoment a slack d + bSample a slack d + bGamma a slack d ≤ 1 / 2) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log (lowerConcreteTargetProb R eps mean k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_deterministic_blocks_samePureError_backgroundScaleLoss_sameBackgroundError_mixedLowerBound_sameMean
      (R := R) (e := e) (eps := eps) (mean := mean)
      (M := M) (τ := τ)
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (errProfile := errProfile) (errScale := errScale)
      (errMix := errMix) (k := k) (ε := ε) hk hε
      hProfile hScaleLoss hMixedLower
      (lower_concrete_hBudget_sameMean_of_eventual_small
        (eps := eps) (errProfile := errProfile) (τ := τ)
        (errScale := errScale) (errMix := errMix)
        (k := k) (ε := ε) (Nat.zero_lt_of_lt hk) hε hEpsLe
        hProfileSmall hTauSmall hScaleSmall hMixedSmall)
      hCoord hUnit hBounds hBad

set_option maxHeartbeats 1000000 in
/-- Final concrete lower exponent for the unit-profile deterministic bridge,
with `hBudget` supplied by eventual-small scalar error estimates.

The hard deterministic inputs are unchanged.  The raw scalar budget is replaced
by the exact scalar assumptions used to prove it. -/
theorem
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_unitProfile_samePureError_backgroundScaleLoss_sameBackgroundError_mixedLowerBound_sameMean_smallErrors
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)))
    {eps mean : ℕ → ℝ}
    {M τ bMoment bSample bGamma errProfile errScale errMix :
      ℝ → ℝ → ℕ → ℝ}
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
                u ∈ lowerConcreteDirectionCapSet e a slack d →
                ‖u‖ = 1 →
                a ^ k - errProfile a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hScaleLoss :
      lowerConcreteBackgroundScaleLoss R M τ
        (fun _a _slack d => mean d) errScale k ε)
    (hMixedLower :
      lowerConcreteMixedLowerBound R e M τ
        (fun _a _slack d => mean d) errMix k ε)
    (hEpsLe : ∀ᶠ d in atTop, eps d ≤ ε)
    (hProfileSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errProfile a slack d ≤ η)
    (hTauSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, τ a slack d ≤ η)
    (hScaleSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errScale a slack d ≤ η)
    (hMixedSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errMix a slack d ≤ η)
    (hCoord :
      ∀ᶠ d in atTop,
        SurfaceProjectiveCapConeCoordinateFormula
          (BipIndex (Fin d) (Fin d)))
    (hUnit :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, ‖e (a, slack, d)‖ = 1)
    (hBounds :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            DeletedColumnBackgroundBadSetBounds
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              (⟨0, hs⟩ : Fin (R.sample d))
              (lowerConcreteN d) (M a slack d) (τ a slack d)
              (mean d) (bMoment a slack d)
              (bSample a slack d) (bGamma a slack d) k)
    (hBad :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          bMoment a slack d + bSample a slack d + bGamma a slack d ≤ 1 / 2) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log (lowerConcreteTargetProb R eps mean k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_unitProfile_samePureError_backgroundScaleLoss_sameBackgroundError_mixedLowerBound_sameMean
      (R := R) (e := e) (eps := eps) (mean := mean)
      (M := M) (τ := τ)
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (errProfile := errProfile) (errScale := errScale)
      (errMix := errMix) (k := k) (ε := ε) hk hε
      hUnitProfile hScaleLoss hMixedLower
      (lower_concrete_hBudget_sameMean_of_eventual_small
        (eps := eps) (errProfile := errProfile) (τ := τ)
        (errScale := errScale) (errMix := errMix)
        (k := k) (ε := ε) (Nat.zero_lt_of_lt hk) hε hEpsLe
        hProfileSmall hTauSmall hScaleSmall hMixedSmall)
      hCoord hUnit hBounds hBad

set_option maxHeartbeats 1000000 in
/-- All-directions final lower endpoint with `hCoord` reduced to the
reference-centre cone formula. -/
theorem
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_deterministic_blocks_samePureError_backgroundScaleLoss_sameBackgroundError_mixedLowerBound_sameMean_smallErrors_referenceCone
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)))
    {eps mean : ℕ → ℝ}
    {M τ bMoment bSample bGamma errProfile errScale errMix :
      ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hk : 1 < k) (hε : 0 < ε)
    (hProfile :
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
                u ∈ lowerConcreteDirectionCapSet e a slack d →
                a ^ k - errProfile a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hScaleLoss :
      lowerConcreteBackgroundScaleLoss R M τ
        (fun _a _slack d => mean d) errScale k ε)
    (hMixedLower :
      lowerConcreteMixedLowerBound R e M τ
        (fun _a _slack d => mean d) errMix k ε)
    (hEpsLe : ∀ᶠ d in atTop, eps d ≤ ε)
    (hProfileSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errProfile a slack d ≤ η)
    (hTauSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, τ a slack d ≤ η)
    (hScaleSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errScale a slack d ≤ η)
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
    (hUnit :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, ‖e (a, slack, d)‖ = 1)
    (hBounds :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            DeletedColumnBackgroundBadSetBounds
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              (⟨0, hs⟩ : Fin (R.sample d))
              (lowerConcreteN d) (M a slack d) (τ a slack d)
              (mean d) (bMoment a slack d)
              (bSample a slack d) (bGamma a slack d) k)
    (hBad :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          bMoment a slack d + bSample a slack d + bGamma a slack d ≤ 1 / 2) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log (lowerConcreteTargetProb R eps mean k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_deterministic_blocks_samePureError_backgroundScaleLoss_sameBackgroundError_mixedLowerBound_sameMean_smallErrors
      (R := R) (e := e) (eps := eps) (mean := mean)
      (M := M) (τ := τ)
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (errProfile := errProfile) (errScale := errScale)
      (errMix := errMix) (k := k) (ε := ε) hk hε
      hProfile hScaleLoss hMixedLower hEpsLe
      hProfileSmall hTauSmall hScaleSmall hMixedSmall
      (lower_concrete_hCoord_of_referenceCone hReference)
      hUnit hBounds hBad

set_option maxHeartbeats 1000000 in
/-- Unit-profile final lower endpoint with `hCoord` reduced to the
reference-centre cone formula. -/
theorem
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_unitProfile_samePureError_backgroundScaleLoss_sameBackgroundError_mixedLowerBound_sameMean_smallErrors_referenceCone
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)))
    {eps mean : ℕ → ℝ}
    {M τ bMoment bSample bGamma errProfile errScale errMix :
      ℝ → ℝ → ℕ → ℝ}
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
                u ∈ lowerConcreteDirectionCapSet e a slack d →
                ‖u‖ = 1 →
                a ^ k - errProfile a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hScaleLoss :
      lowerConcreteBackgroundScaleLoss R M τ
        (fun _a _slack d => mean d) errScale k ε)
    (hMixedLower :
      lowerConcreteMixedLowerBound R e M τ
        (fun _a _slack d => mean d) errMix k ε)
    (hEpsLe : ∀ᶠ d in atTop, eps d ≤ ε)
    (hProfileSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errProfile a slack d ≤ η)
    (hTauSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, τ a slack d ≤ η)
    (hScaleSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errScale a slack d ≤ η)
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
    (hUnit :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, ‖e (a, slack, d)‖ = 1)
    (hBounds :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            DeletedColumnBackgroundBadSetBounds
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              (⟨0, hs⟩ : Fin (R.sample d))
              (lowerConcreteN d) (M a slack d) (τ a slack d)
              (mean d) (bMoment a slack d)
              (bSample a slack d) (bGamma a slack d) k)
    (hBad :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          bMoment a slack d + bSample a slack d + bGamma a slack d ≤ 1 / 2) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log (lowerConcreteTargetProb R eps mean k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_unitProfile_samePureError_backgroundScaleLoss_sameBackgroundError_mixedLowerBound_sameMean_smallErrors
      (R := R) (e := e) (eps := eps) (mean := mean)
      (M := M) (τ := τ)
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (errProfile := errProfile) (errScale := errScale)
      (errMix := errMix) (k := k) (ε := ε) hk hε
      hUnitProfile hScaleLoss hMixedLower hEpsLe
      hProfileSmall hTauSmall hScaleSmall hMixedSmall
      (lower_concrete_hCoord_of_referenceCone hReference)
      hUnit hBounds hBad

set_option maxHeartbeats 1000000 in
/-- All-directions final lower endpoint specialized to the canonical coordinate
spike direction.

This removes the explicit `hUnit` parameter from the reference-cone bundled
endpoint.  The deterministic profile assumption is still an explicit
all-directions input over the canonical cap set. -/
theorem
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_deterministic_blocks_samePureError_backgroundScaleLoss_sameBackgroundError_mixedLowerBound_sameMean_smallErrors_referenceCone_canonicalDirection
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps mean : ℕ → ℝ}
    {M τ bMoment bSample bGamma errProfile errScale errMix :
      ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hk : 1 < k) (hε : 0 < ε)
    (hProfile :
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
                a ^ k - errProfile a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hScaleLoss :
      lowerConcreteBackgroundScaleLoss R M τ
        (fun _a _slack d => mean d) errScale k ε)
    (hMixedLower :
      lowerConcreteMixedLowerBound R lowerConcreteCanonicalDirection M τ
        (fun _a _slack d => mean d) errMix k ε)
    (hEpsLe : ∀ᶠ d in atTop, eps d ≤ ε)
    (hProfileSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errProfile a slack d ≤ η)
    (hTauSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, τ a slack d ≤ η)
    (hScaleSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errScale a slack d ≤ η)
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
    (hBounds :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            DeletedColumnBackgroundBadSetBounds
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              (⟨0, hs⟩ : Fin (R.sample d))
              (lowerConcreteN d) (M a slack d) (τ a slack d)
              (mean d) (bMoment a slack d)
              (bSample a slack d) (bGamma a slack d) k)
    (hBad :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          bMoment a slack d + bSample a slack d + bGamma a slack d ≤ 1 / 2) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log (lowerConcreteTargetProb R eps mean k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_deterministic_blocks_samePureError_backgroundScaleLoss_sameBackgroundError_mixedLowerBound_sameMean_smallErrors_referenceCone
      (R := R) (e := lowerConcreteCanonicalDirection)
      (eps := eps) (mean := mean) (M := M) (τ := τ)
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (errProfile := errProfile) (errScale := errScale)
      (errMix := errMix) (k := k) (ε := ε) hk hε
      hProfile hScaleLoss hMixedLower hEpsLe
      hProfileSmall hTauSmall hScaleSmall hMixedSmall
      hReference
      (lower_concrete_hUnit_canonicalDirection (k := k) (ε := ε))
      hBounds hBad

set_option maxHeartbeats 1000000 in
/-- Unit-profile final lower endpoint specialized to the canonical coordinate
spike direction.

This is the current bundled lower endpoint with both geometric transport
steps closed as wrappers: `hCoord` is reduced to the reference cone formula and
`hUnit` is supplied by the canonical coordinate vector.  The unit-profile,
mixed, background, and scalar smallness assumptions remain explicit. -/
theorem
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_unitProfile_samePureError_backgroundScaleLoss_sameBackgroundError_mixedLowerBound_sameMean_smallErrors_referenceCone_canonicalDirection
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps mean : ℕ → ℝ}
    {M τ bMoment bSample bGamma errProfile errScale errMix :
      ℝ → ℝ → ℕ → ℝ}
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
                a ^ k - errProfile a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hScaleLoss :
      lowerConcreteBackgroundScaleLoss R M τ
        (fun _a _slack d => mean d) errScale k ε)
    (hMixedLower :
      lowerConcreteMixedLowerBound R lowerConcreteCanonicalDirection M τ
        (fun _a _slack d => mean d) errMix k ε)
    (hEpsLe : ∀ᶠ d in atTop, eps d ≤ ε)
    (hProfileSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errProfile a slack d ≤ η)
    (hTauSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, τ a slack d ≤ η)
    (hScaleSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errScale a slack d ≤ η)
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
    (hBounds :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            DeletedColumnBackgroundBadSetBounds
              (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
              (⟨0, hs⟩ : Fin (R.sample d))
              (lowerConcreteN d) (M a slack d) (τ a slack d)
              (mean d) (bMoment a slack d)
              (bSample a slack d) (bGamma a slack d) k)
    (hBad :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          bMoment a slack d + bSample a slack d + bGamma a slack d ≤ 1 / 2) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log (lowerConcreteTargetProb R eps mean k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_unitProfile_samePureError_backgroundScaleLoss_sameBackgroundError_mixedLowerBound_sameMean_smallErrors_referenceCone
      (R := R) (e := lowerConcreteCanonicalDirection)
      (eps := eps) (mean := mean) (M := M) (τ := τ)
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (errProfile := errProfile) (errScale := errScale)
      (errMix := errMix) (k := k) (ε := ε) hk hε
      hUnitProfile hScaleLoss hMixedLower hEpsLe
      hProfileSmall hTauSmall hScaleSmall hMixedSmall
      hReference
      (lower_concrete_hUnit_canonicalDirection (k := k) (ε := ε))
      hBounds hBad

set_option maxHeartbeats 1000000 in
/-- All-directions canonical endpoint with `hBounds` supplied by reduced
spherical bad-set bounds.

The deleted-background transport is closed here.  What remains visible is the
actual reduced-model bad-set package on `DeletedColumn`, plus the scalar
union-bound budget `hBad`; this theorem does not prove those probabilistic
bad-set estimates unconditionally. -/
theorem
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_deterministic_blocks_samePureError_backgroundScaleLoss_sameBackgroundError_mixedLowerBound_sameMean_smallErrors_referenceCone_canonicalDirection_reducedBackgroundBounds
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps mean : ℕ → ℝ}
    {M τ bMoment bSample bGamma errProfile errScale errMix :
      ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hk : 1 < k) (hε : 0 < ε)
    (hProfile :
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
                a ^ k - errProfile a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hScaleLoss :
      lowerConcreteBackgroundScaleLoss R M τ
        (fun _a _slack d => mean d) errScale k ε)
    (hMixedLower :
      lowerConcreteMixedLowerBound R lowerConcreteCanonicalDirection M τ
        (fun _a _slack d => mean d) errMix k ε)
    (hEpsLe : ∀ᶠ d in atTop, eps d ≤ ε)
    (hProfileSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errProfile a slack d ≤ η)
    (hTauSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, τ a slack d ≤ η)
    (hScaleSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errScale a slack d ≤ η)
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
    (hReduced :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            ConcreteSphericalBackgroundBadSetBounds
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
              (lowerConcreteN d) (M a slack d) (τ a slack d)
              (mean d) (bMoment a slack d)
              (bSample a slack d) (bGamma a slack d) k)
    (hBad :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          bMoment a slack d + bSample a slack d + bGamma a slack d ≤ 1 / 2) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log (lowerConcreteTargetProb R eps mean k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_deterministic_blocks_samePureError_backgroundScaleLoss_sameBackgroundError_mixedLowerBound_sameMean_smallErrors_referenceCone_canonicalDirection
      (R := R) (eps := eps) (mean := mean)
      (M := M) (τ := τ)
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (errProfile := errProfile) (errScale := errScale)
      (errMix := errMix) (k := k) (ε := ε) hk hε
      hProfile hScaleLoss hMixedLower hEpsLe
      hProfileSmall hTauSmall hScaleSmall hMixedSmall
      hReference
      (lower_concrete_hBounds_of_reduced_spherical_bad_bounds
        (R := R) (M := M) (τ := τ)
        (center := fun _a _slack d => mean d)
        (bMoment := bMoment) (bSample := bSample)
        (bGamma := bGamma) (k := k) hReduced)
      hBad

set_option maxHeartbeats 1000000 in
/-- All-directions canonical endpoint with both deleted-background transport
and the scalar `hBad` union budget closed.

The endpoint still exposes the genuine reduced bad-set estimates `hReduced`;
the former `hBad` parameter is supplied from eventual smallness of the three
bad-event budgets. -/
theorem
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_deterministic_blocks_samePureError_backgroundScaleLoss_sameBackgroundError_mixedLowerBound_sameMean_smallErrors_referenceCone_canonicalDirection_reducedBackgroundBounds_smallBadBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps mean : ℕ → ℝ}
    {M τ bMoment bSample bGamma errProfile errScale errMix :
      ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hk : 1 < k) (hε : 0 < ε)
    (hProfile :
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
                a ^ k - errProfile a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hScaleLoss :
      lowerConcreteBackgroundScaleLoss R M τ
        (fun _a _slack d => mean d) errScale k ε)
    (hMixedLower :
      lowerConcreteMixedLowerBound R lowerConcreteCanonicalDirection M τ
        (fun _a _slack d => mean d) errMix k ε)
    (hEpsLe : ∀ᶠ d in atTop, eps d ≤ ε)
    (hProfileSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errProfile a slack d ≤ η)
    (hTauSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, τ a slack d ≤ η)
    (hScaleSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errScale a slack d ≤ η)
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
    (hReduced :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            ConcreteSphericalBackgroundBadSetBounds
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
              (lowerConcreteN d) (M a slack d) (τ a slack d)
              (mean d) (bMoment a slack d)
              (bSample a slack d) (bGamma a slack d) k)
    (hMomentSmall :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop, bMoment a slack d ≤ η)
    (hSampleSmall :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop, bSample a slack d ≤ η)
    (hGammaSmall :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop, bGamma a slack d ≤ η) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log (lowerConcreteTargetProb R eps mean k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_deterministic_blocks_samePureError_backgroundScaleLoss_sameBackgroundError_mixedLowerBound_sameMean_smallErrors_referenceCone_canonicalDirection_reducedBackgroundBounds
      (R := R) (eps := eps) (mean := mean)
      (M := M) (τ := τ)
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (errProfile := errProfile) (errScale := errScale)
      (errMix := errMix) (k := k) (ε := ε) hk hε
      hProfile hScaleLoss hMixedLower hEpsLe
      hProfileSmall hTauSmall hScaleSmall hMixedSmall
      hReference hReduced
      (lower_concrete_hBad_of_eventual_small
        (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
        hMomentSmall hSampleSmall hGammaSmall)

set_option maxHeartbeats 1000000 in
/-- Unit-profile canonical endpoint with `hBounds` supplied by reduced
spherical bad-set bounds.

This is the most bundled lower endpoint in this file after closing `hUnit` and
the deleted-background `hBounds` transport.  The hard reduced bad-set estimates
and their `≤ 1/2` budget remain explicit parameters. -/
theorem
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_unitProfile_samePureError_backgroundScaleLoss_sameBackgroundError_mixedLowerBound_sameMean_smallErrors_referenceCone_canonicalDirection_reducedBackgroundBounds
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps mean : ℕ → ℝ}
    {M τ bMoment bSample bGamma errProfile errScale errMix :
      ℝ → ℝ → ℕ → ℝ}
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
                a ^ k - errProfile a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hScaleLoss :
      lowerConcreteBackgroundScaleLoss R M τ
        (fun _a _slack d => mean d) errScale k ε)
    (hMixedLower :
      lowerConcreteMixedLowerBound R lowerConcreteCanonicalDirection M τ
        (fun _a _slack d => mean d) errMix k ε)
    (hEpsLe : ∀ᶠ d in atTop, eps d ≤ ε)
    (hProfileSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errProfile a slack d ≤ η)
    (hTauSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, τ a slack d ≤ η)
    (hScaleSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errScale a slack d ≤ η)
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
    (hReduced :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            ConcreteSphericalBackgroundBadSetBounds
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
              (lowerConcreteN d) (M a slack d) (τ a slack d)
              (mean d) (bMoment a slack d)
              (bSample a slack d) (bGamma a slack d) k)
    (hBad :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          bMoment a slack d + bSample a slack d + bGamma a slack d ≤ 1 / 2) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log (lowerConcreteTargetProb R eps mean k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_unitProfile_samePureError_backgroundScaleLoss_sameBackgroundError_mixedLowerBound_sameMean_smallErrors_referenceCone_canonicalDirection
      (R := R) (eps := eps) (mean := mean)
      (M := M) (τ := τ)
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (errProfile := errProfile) (errScale := errScale)
      (errMix := errMix) (k := k) (ε := ε) hk hε
      hUnitProfile hScaleLoss hMixedLower hEpsLe
      hProfileSmall hTauSmall hScaleSmall hMixedSmall
      hReference
      (lower_concrete_hBounds_of_reduced_spherical_bad_bounds
        (R := R) (M := M) (τ := τ)
        (center := fun _a _slack d => mean d)
        (bMoment := bMoment) (bSample := bSample)
        (bGamma := bGamma) (k := k) hReduced)
      hBad

set_option maxHeartbeats 1000000 in
/-- Unit-profile canonical endpoint with both deleted-background transport and
the scalar `hBad` union budget closed.

This is the current most bundled lower endpoint in this closure file.  It does
not prove the reduced bad-set probabilities themselves; it only replaces the
single union-bound assumption by explicit eventual smallness of
`bMoment`, `bSample`, and `bGamma`. -/
theorem
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_unitProfile_samePureError_backgroundScaleLoss_sameBackgroundError_mixedLowerBound_sameMean_smallErrors_referenceCone_canonicalDirection_reducedBackgroundBounds_smallBadBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps mean : ℕ → ℝ}
    {M τ bMoment bSample bGamma errProfile errScale errMix :
      ℝ → ℝ → ℕ → ℝ}
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
                a ^ k - errProfile a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hScaleLoss :
      lowerConcreteBackgroundScaleLoss R M τ
        (fun _a _slack d => mean d) errScale k ε)
    (hMixedLower :
      lowerConcreteMixedLowerBound R lowerConcreteCanonicalDirection M τ
        (fun _a _slack d => mean d) errMix k ε)
    (hEpsLe : ∀ᶠ d in atTop, eps d ≤ ε)
    (hProfileSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errProfile a slack d ≤ η)
    (hTauSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, τ a slack d ≤ η)
    (hScaleSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errScale a slack d ≤ η)
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
    (hReduced :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            ConcreteSphericalBackgroundBadSetBounds
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
              (lowerConcreteN d) (M a slack d) (τ a slack d)
              (mean d) (bMoment a slack d)
              (bSample a slack d) (bGamma a slack d) k)
    (hMomentSmall :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop, bMoment a slack d ≤ η)
    (hSampleSmall :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop, bSample a slack d ≤ η)
    (hGammaSmall :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop, bGamma a slack d ≤ η) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log (lowerConcreteTargetProb R eps mean k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_unitProfile_samePureError_backgroundScaleLoss_sameBackgroundError_mixedLowerBound_sameMean_smallErrors_referenceCone_canonicalDirection_reducedBackgroundBounds
      (R := R) (eps := eps) (mean := mean)
      (M := M) (τ := τ)
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (errProfile := errProfile) (errScale := errScale)
      (errMix := errMix) (k := k) (ε := ε) hk hε
      hUnitProfile hScaleLoss hMixedLower hEpsLe
      hProfileSmall hTauSmall hScaleSmall hMixedSmall
      hReference hReduced
      (lower_concrete_hBad_of_eventual_small
        (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
        hMomentSmall hSampleSmall hGammaSmall)

set_option maxHeartbeats 1000000 in
/-- Unit-profile canonical endpoint with the reduced background package
assembled from its natural probability inputs.

Compared with
`lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_unitProfile_samePureError_backgroundScaleLoss_sameBackgroundError_mixedLowerBound_sameMean_smallErrors_referenceCone_canonicalDirection_reducedBackgroundBounds_smallBadBudget`,
this wrapper no longer asks for a pre-built
`ConcreteSphericalBackgroundBadSetBounds` hypothesis.  It takes instead the
reduced moment bad-set estimate and the two normalized Gaussian operator-tail
estimates, then calls the closed spherical/Gaussian transfer wrapper.  These
three estimates remain explicit assumptions; no unconditional concentration
statement is asserted here. -/
theorem
    lower_eventual_log_over_spikeSpeed_concreteModel_of_reducedMomentAndGaussianTails_smallBadBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps mean : ℕ → ℝ}
    {M τ bMoment bSample bGamma errProfile errScale errMix :
      ℝ → ℝ → ℕ → ℝ}
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
                a ^ k - errProfile a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hScaleLoss :
      lowerConcreteBackgroundScaleLoss R M τ
        (fun _a _slack d => mean d) errScale k ε)
    (hMixedLower :
      lowerConcreteMixedLowerBound R lowerConcreteCanonicalDirection M τ
        (fun _a _slack d => mean d) errMix k ε)
    (hEpsLe : ∀ᶠ d in atTop, eps d ≤ ε)
    (hProfileSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errProfile a slack d ≤ η)
    (hTauSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, τ a slack d ≤ η)
    (hScaleSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errScale a slack d ≤ η)
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
                (lowerConcreteN d) (τ a slack d) (mean d) k) ≤
              bMoment a slack d)
    (hSampleTail :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            (_root_.PptFactorization.HighProbabilityBounds.gaussianMeasure
              (Fin d) (Fin d)
              (DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
              ((_root_.PptFactorization.HighProbabilityBounds.normalizedSampleOpNormEvent
                (p := Fin d) (q := Fin d)
                (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
                (M a slack d) (d : ℝ))ᶜ) ≤
              bSample a slack d)
    (hGammaTail :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            (_root_.PptFactorization.HighProbabilityBounds.gaussianMeasure
              (Fin d) (Fin d)
              (DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
              ((_root_.PptFactorization.HighProbabilityBounds.normalizedRhoGammaOpNormEvent
                (p := Fin d) (q := Fin d)
                (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
                (M a slack d) (d : ℝ))ᶜ) ≤
              bGamma a slack d)
    (hMomentSmall :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop, bMoment a slack d ≤ η)
    (hSampleSmall :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop, bSample a slack d ≤ η)
    (hGammaSmall :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop, bGamma a slack d ≤ η) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log (lowerConcreteTargetProb R eps mean k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closed_unitProfile_samePureError_backgroundScaleLoss_sameBackgroundError_mixedLowerBound_sameMean_smallErrors_referenceCone_canonicalDirection_reducedBackgroundBounds_smallBadBudget
      (R := R) (eps := eps) (mean := mean)
      (M := M) (τ := τ)
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (errProfile := errProfile) (errScale := errScale)
      (errMix := errMix) (k := k) (ε := ε) hk hε
      hUnitProfile hScaleLoss hMixedLower hEpsLe
      hProfileSmall hTauSmall hScaleSmall hMixedSmall
      hReference
      (lower_concrete_hReduced_of_moment_and_gaussian_operator_tails
        (R := R) (M := M) (τ := τ)
        (center := fun _a _slack d => mean d)
        (bMoment := bMoment) (bSample := bSample)
        (bGamma := bGamma) (k := k)
        hMoment hSampleTail hGammaTail)
      hMomentSmall hSampleSmall hGammaSmall

set_option maxHeartbeats 1000000 in
/-- Reduced-moment endpoint with the two Gaussian operator-tail budgets fixed
to the canonical common lower threshold.

This wrapper closes the lower-side `hSampleTail`, `hGammaTail`,
`hSampleSmall`, and `hGammaSmall` inputs using the deleted-column Gaussian
bridge at `lowerConcreteM R` and the scalar estimate
`exp(-d²/12) → 0`.  It does not close the reduced moment estimate or its
smallness; these remain the visible `hMoment` and `hMomentSmall` assumptions. -/
theorem
    lower_eventual_log_over_spikeSpeed_concreteModel_of_reducedMoment_commonGaussianTails_smallBadBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps mean : ℕ → ℝ}
    {τ bMoment errProfile errScale errMix : ℝ → ℝ → ℕ → ℝ}
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
                a ^ k - errProfile a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u)
    (hScaleLoss :
      lowerConcreteBackgroundScaleLoss R (lowerConcreteM R) τ
        (fun _a _slack d => mean d) errScale k ε)
    (hMixedLower :
      lowerConcreteMixedLowerBound R lowerConcreteCanonicalDirection
        (lowerConcreteM R) τ
        (fun _a _slack d => mean d) errMix k ε)
    (hEpsLe : ∀ᶠ d in atTop, eps d ≤ ε)
    (hProfileSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errProfile a slack d ≤ η)
    (hTauSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, τ a slack d ≤ η)
    (hScaleSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errScale a slack d ≤ η)
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
                (lowerConcreteN d) (τ a slack d) (mean d) k) ≤
              bMoment a slack d)
    (hMomentSmall :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop, bMoment a slack d ≤ η) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log (lowerConcreteTargetProb R eps mean k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_reducedMomentAndGaussianTails_smallBadBudget
      (R := R) (eps := eps) (mean := mean)
      (M := lowerConcreteM R) (τ := τ)
      (bMoment := bMoment)
      (bSample := lowerConcreteSampleTailBound)
      (bGamma := lowerConcreteGammaTailBound)
      (errProfile := errProfile) (errScale := errScale)
      (errMix := errMix) (k := k) (ε := ε) hk hε
      hUnitProfile hScaleLoss hMixedLower hEpsLe
      hProfileSmall hTauSmall hScaleSmall hMixedSmall
      hReference hMoment
      (lower_concrete_hSampleTail_of_deletedColumn_operator_tails R)
      (lower_concrete_hGammaTail_of_deletedColumn_operator_tails R)
      hMomentSmall
      lower_concrete_hSampleSmall_commonThreshold
      lower_concrete_hGammaSmall_commonThreshold

set_option maxHeartbeats 1000000 in
/-- Lower endpoint with the public concrete scalar choices fixed.

Compared with
`lower_eventual_log_over_spikeSpeed_concreteModel_of_reducedMoment_deletedColumnOperatorTails`,
this wrapper no longer asks for `hEpsLe`, the four small-error hypotheses, or
`hMomentSmall`.  The genuinely hard deterministic/geometric/probabilistic
inputs remain explicit: `hUnitProfile`, `hScaleLoss`, `hMixedLower`,
`hReference`, and the mean-centered deleted-background moment estimate
`hMoment`. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_concreteScalarChoices
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
    (hScaleLoss :
      lowerConcreteBackgroundScaleLoss R (lowerConcreteM R) lowerConcreteTau
        (fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
        (lowerConcreteScaleError R k ε) k ε)
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
    lower_eventual_log_over_spikeSpeed_concreteModel_of_reducedMoment_commonGaussianTails_smallBadBudget
      (R := R) (eps := lowerConcreteEps ε)
      (mean := lowerConcreteDeletedBackgroundMean R k)
      (τ := lowerConcreteTau)
      (bMoment := lowerConcreteMomentBound R k)
      (errProfile := lowerConcreteProfileError k ε)
      (errScale := lowerConcreteScaleError R k ε)
      (errMix := lowerConcreteMixedError R k ε)
      (k := k) (ε := ε) hk hε
      hUnitProfile hScaleLoss hMixedLower
      (lower_concrete_hEpsLe ε)
      (lower_concrete_hProfileSmall (k := k) (ε := ε))
      (fun a _ha slack _hslack =>
        lower_concrete_hTauSmall a slack)
      (lower_concrete_hScaleSmall R (k := k) (ε := ε))
      (lower_concrete_hMixedSmall R (k := k) (ε := ε))
      hReference hMoment
      (lower_concrete_hMomentSmall R (k := k))

/-- Public lower endpoint with the deleted-column Gaussian operator tails
closed internally.

This is an alias of
`lower_eventual_log_over_spikeSpeed_concreteModel_of_reducedMoment_commonGaussianTails_smallBadBudget`
with a name that records the current API boundary: `hSampleTail`,
`hGammaTail`, `hSampleSmall`, and `hGammaSmall` are no longer theorem
parameters.  The reduced moment estimate `hMoment`, its scalar smallness
`hMomentSmall`, and the remaining deterministic/profile/reference hypotheses
remain explicit. -/
alias
  lower_eventual_log_over_spikeSpeed_concreteModel_of_reducedMoment_deletedColumnOperatorTails :=
    lower_eventual_log_over_spikeSpeed_concreteModel_of_reducedMoment_commonGaussianTails_smallBadBudget

end AppendixB
