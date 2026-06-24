import PptFactorization.AristotleTargets.LowerReferenceConeConcreteChoices
import PptFactorization.AristotleTargets.LowerUnitProfileConcreteChoices
import PptFactorization.AristotleTargets.LowerScaleLossConcreteChoices
import PptFactorization.AristotleTargets.LowerMixedLowerConcreteChoices
import PptFactorization.AristotleTargets.LowerBackgroundMomentConcreteChoices

/-!
Assembly target for the concrete lower endpoint.

This file should contain no independent mathematics.  The scale-loss transfer is
routed through the sphere-supported Beta-interval comparison, so the remaining
visible scale obligation is the honest scalar budget
`lowerConcreteBackgroundScaleBudgetOnBetaInterval`, not the obsolete standalone
`lowerConcreteBackgroundScaleLoss`.

Protected file: do not edit `PptFactorization/AppendixBSpikeLowerBound.lean`.
-/
namespace AppendixB

open Filter
open PptFactorization.RandomMatrixModel
open scoped Topology

/-- Clean frontier endpoint for the concrete lower assembly.

This theorem avoids the remaining broad supplier wrappers and exposes the exact
frontier inputs instead:

* cap trace-power stability for the canonical spike direction;
* bounded positive part of the deleted-background mean, used by the corrected
  sphere/Beta scale budget;
* the concrete local-expansion mixed envelope;
* the reference projective cone formula;
* the mean-centered deleted-background moment tail.

It is conditional, but it is deliberately conditional on the sharp local
frontiers rather than on the older broad supplier theorems. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_cleanFrontierInputs
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hTraceStability :
      lowerConcreteCanonicalCapSpikeTraceStability k ε)
    (hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
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
  have hk : 1 < k := lt_of_lt_of_le (by decide : 1 < 3) hk3
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_concreteScalarChoices_sphereBetaScaleBudget
      (R := R) (k := k) (ε := ε) hk hε
      (lower_unitProfile_canonicalDirection_concreteChoices_of_traceStability
        hk hε hTraceStability)
      (lower_scaleBudget_concreteChoices_of_meanPositivePartEventuallyBounded
        (R := R) (k := k) (ε := ε) hk3 hε hMeanBound)
      (lower_mixedLower_concreteChoices_of_localExpansionEnvelope
        (R := R) (k := k) (ε := ε) hMixedEnvelope)
      hReference
      hMoment

/-- Clean frontier endpoint with an explicit mixed-error sequence.

This is the repaired mixed-side interface.  The old
`lowerConcreteMixedLocalExpansionEnvelope` bakes in
`lowerConcreteMixedError = 1 / d`; deterministic mixed-word estimates naturally
produce an arbitrary `o(1)` envelope, and they use the Frobenius-sphere support
of the spherical law.  This endpoint therefore asks for that explicit
on-sphere envelope and its eventual-smallness proof. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_cleanFrontierInputs_withMixedError
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hTraceStability :
      lowerConcreteCanonicalCapSpikeTraceStability k ε)
    (hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k)
    (errMix : ℝ → ℝ → ℕ → ℝ)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithError R k ε errMix)
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
  have hk : 1 < k := lt_of_lt_of_le (by decide : 1 < 3) hk3
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_concreteScalarChoices_sphereBetaScaleBudget_withMixedError
      (R := R) (k := k) (ε := ε) hk hε
      (lower_unitProfile_canonicalDirection_concreteChoices_of_traceStability
        hk hε hTraceStability)
      (lower_scaleBudget_concreteChoices_of_meanPositivePartEventuallyBounded
        (R := R) (k := k) (ε := ε) hk3 hε hMeanBound)
      (lower_mixedLowerOnSphere_concreteChoices_of_localExpansionEnvelopeOnSphereWithError
        (R := R) (k := k) (ε := ε) errMix hMixedEnvelope)
      hMixedSmall
      hReference
      hMoment

/-- Clean lower endpoint after closing the reference cone-coordinate formula.

The projective reference-cap geometry is now supplied by
`lower_referenceCone_BipIndex_Fin_eventually_concreteChoices`, so the remaining
frontier is trace stability, the corrected scale/mean bound, the mixed
envelope, and the mean-centered background moment estimate. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_cleanFrontierInputs_noReference
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hTraceStability :
      lowerConcreteCanonicalCapSpikeTraceStability k ε)
    (hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
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
    lower_eventual_log_over_spikeSpeed_concreteModel_of_cleanFrontierInputs
      (R := R) (k := k) (ε := ε) hk3 hε
      hTraceStability
      hMeanBound
      hMixedEnvelope
      lower_referenceCone_BipIndex_Fin_eventually_concreteChoices
      hMoment

/-- Preferred live lower frontier after the scale-route repair.

This is the source-of-truth public endpoint for the active lower assembly.  It
uses the repaired mean-side input `hMeanBound`, not the legacy `hMeanLimit`
compatibility branch, and it keeps only the still-honest local frontiers
visible:

* trace stability on the canonical cap;
* bounded positive part of the deleted-background mean;
* the mixed local-expansion envelope;
* the mean-centered closed-deviation moment tail.

The reference-cone plumbing is already closed locally. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_activeFrontierInputs
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hTraceStability :
      lowerConcreteCanonicalCapSpikeTraceStability k ε)
    (hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
      (hMomentDeviation :
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
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_cleanFrontierInputs_noReference
      (R := R) (k := k) (ε := ε) hk3 hε
      hTraceStability
      hMeanBound
      hMixedEnvelope
      (lower_backgroundMomentTail_concreteChoices_of_deviationBound
        (R := R) (k := k) hMomentDeviation)

/-- Active lower frontier after the mixed supplier has already been assembled.

The older split into an arbitrary pointwise word bound plus an arbitrary scalar
budget is intentionally not exposed here: the endpoint should consume the
assembled mixed local-expansion envelope. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_activeFrontierInputs_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hTraceStability :
      lowerConcreteCanonicalCapSpikeTraceStability k ε)
    (hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
    (hMomentDeviation :
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
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_activeFrontierInputs
      (R := R) (k := k) (ε := ε) hk3 hε
      hTraceStability
      hMeanBound
      hMixedEnvelope
      hMomentDeviation

/-- Preferred active-frontier endpoint with a named moment-tail input.

This is definitionally equivalent to
`lower_eventual_log_over_spikeSpeed_concreteModel_of_activeFrontierInputs`, but
it isolates the first remaining probabilistic gap as the named predicate
`lowerConcreteDeletedBackgroundMomentDeviationTailBound R k`. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_activeFrontierInputs_namedMomentDeviation
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hTraceStability :
      lowerConcreteCanonicalCapSpikeTraceStability k ε)
    (hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
    (hMomentDeviation :
      lowerConcreteDeletedBackgroundMomentDeviationTailBound R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_activeFrontierInputs
      (R := R) (k := k) (ε := ε) hk3 hε
      hTraceStability hMeanBound hMixedEnvelope hMomentDeviation

/-- Active lower frontier using the second-moment/Chebyshev deleted-background
moment tail.

This wrapper is the polynomial-tail analogue of
`lower_eventual_log_over_spikeSpeed_concreteModel_of_activeFrontierInputs`:
the moment bad-set budget is `C / d²`, supplied by the Wick variance theorem,
and the generic lower assembly only needs that budget to be eventually small. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_activeFrontierInputs_secondMomentWickMomentTail
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hTraceStability :
      lowerConcreteCanonicalCapSpikeTraceStability k ε)
    (hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  have hk : 1 < k := lt_of_lt_of_le (by decide : 1 < 3) hk3
  rcases
    lowerConcreteDeletedBackgroundMomentSecondMomentWickBadTailBound_of_deviationTailBound
      (R := R) (k := k) hMomentSecond with
    ⟨C, _hC, hMomentBad⟩
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_concreteScalarChoices_sphereBetaScaleBudget_withMomentBudget
      (R := R) (k := k) (ε := ε) hk hε
      (bMoment := lowerConcreteMomentPolynomialBound C R k)
      (lower_unitProfile_canonicalDirection_concreteChoices_of_traceStability
        hk hε hTraceStability)
      (lower_scaleBudget_concreteChoices_of_meanPositivePartEventuallyBounded
        (R := R) (k := k) (ε := ε) hk3 hε hMeanBound)
      (lower_mixedLower_concreteChoices_of_localExpansionEnvelope
        (R := R) (k := k) (ε := ε) hMixedEnvelope)
      lower_referenceCone_BipIndex_Fin_eventually_concreteChoices
      hMomentBad
      (lower_concrete_polynomialMomentSmall C R k)

/-- Active lower frontier using the paper-facing deleted-background variance
bound.

The variance statement supplies the polynomial moment-tail budget by the
Chebyshev converter in the background-moment file, so this endpoint exposes the
remaining probabilistic input in the form used in the paper-facing stack. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_activeFrontierInputs_varianceMomentTail
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hTraceStability :
      lowerConcreteCanonicalCapSpikeTraceStability k ε)
    (hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_activeFrontierInputs_secondMomentWickMomentTail
      (R := R) (k := k) (ε := ε) hk3 hε
      hTraceStability
      hMeanBound
      hMixedEnvelope
      (lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound_of_deletedColumnSphericalMoment_variance_le_const_div_d4
        R k hVariance)

/-- No-reference closed-trace endpoint with the deleted-background moment tail
supplied by the two-trace Wick/Chebyshev polynomial bound.

This is the endpoint-safe concentration route at tolerance `1 / d`: it consumes
the visible variance-style frontier
`lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k`
rather than the stronger exponential deviation frontier. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceFrontierInputs_meanBound_secondMomentWickMomentTail
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_activeFrontierInputs_secondMomentWickMomentTail
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerConcreteCanonicalCapSpikeTraceStability_of_overlapLower
        (lt_of_lt_of_le (by decide : 1 < 3) hk3)
        hε
        (lowerConcreteCanonicalCapTracePowerOverlapLower_of_traceDominatesCoordinateOverlap
          (lowerConcreteRankOneProjectorGammaTracePowerDominatesCoordinateOverlap_of_leftDensityDiagonalPower
            (lowerConcreteRankOneProjectorGammaTracePowerDominatesLeftDensityDiagonalPower_closed k))))
      hMeanBound
      hMixedEnvelope
      hMomentSecond

/-- No-reference closed-trace endpoint with the background typicality side
exposed as the paper-facing variance estimate.

This is the no-reference analogue of
`...activeFrontierInputs_varianceMomentTail`: closed unit-profile trace
stability is supplied internally, and the moment-tail budget is obtained from
`deletedColumnSphericalMoment_variance_le_const_div_d4` by Chebyshev. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceFrontierInputs_meanBound_varianceMomentTail
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_activeFrontierInputs_varianceMomentTail
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerConcreteCanonicalCapSpikeTraceStability_of_overlapLower
        (lt_of_lt_of_le (by decide : 1 < 3) hk3)
        hε
        (lowerConcreteCanonicalCapTracePowerOverlapLower_of_traceDominatesCoordinateOverlap
          (lowerConcreteRankOneProjectorGammaTracePowerDominatesCoordinateOverlap_of_leftDensityDiagonalPower
            (lowerConcreteRankOneProjectorGammaTracePowerDominatesLeftDensityDiagonalPower_closed k))))
      hMeanBound
      hMixedEnvelope
      hVariance

/-- Same clean lower endpoint, with the unit-profile frontier split into its
geometric trace-overlap input and its scalar cap-loss budget.  This is a
strictly sharper boundary than `lowerConcreteCanonicalCapSpikeTraceStability`:
the Beta/profile wiring is closed, and the two remaining unit-profile facts are
visible separately. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_splitUnitProfileFrontierInputs
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hTraceOverlap :
      lowerConcreteCanonicalCapTracePowerOverlapLower k)
    (hProfileScalarBudget :
      lowerConcreteCanonicalCapProfileScalarBudget k ε)
    (hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
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
  have hk : 1 < k := lt_of_lt_of_le (by decide : 1 < 3) hk3
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_cleanFrontierInputs
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerConcreteCanonicalCapSpikeTraceStability_of_overlapLower_and_scalarBudget
        hk hε hTraceOverlap hProfileScalarBudget)
      hMeanBound
      hMixedEnvelope
      hReference
      hMoment

/-- Clean lower endpoint after closing the scalar half of the canonical
unit-profile cap budget.  The unit-profile frontier is now only the geometric
trace-overlap statement on the canonical projective cap. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_traceOverlapFrontierInputs
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hTraceOverlap :
      lowerConcreteCanonicalCapTracePowerOverlapLower k)
    (hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
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
  have hk : 1 < k := lt_of_lt_of_le (by decide : 1 < 3) hk3
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_cleanFrontierInputs
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerConcreteCanonicalCapSpikeTraceStability_of_overlapLower
        hk hε hTraceOverlap)
      hMeanBound
      hMixedEnvelope
      hReference
      hMoment

/-- Clean lower endpoint with the unit-profile debt reduced to the standalone
rank-one partial-transpose trace-dominance statement. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_traceDominanceFrontierInputs
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hTraceDominance :
      lowerConcreteRankOneProjectorGammaTracePowerDominatesCoordinateOverlap k)
    (hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
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
    lower_eventual_log_over_spikeSpeed_concreteModel_of_traceOverlapFrontierInputs
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerConcreteCanonicalCapTracePowerOverlapLower_of_traceDominatesCoordinateOverlap
        hTraceDominance)
      hMeanBound
      hMixedEnvelope
      hReference
      hMoment

/-- Clean lower endpoint with the trace/unit-profile frontier reduced below
coordinate overlap.

The remaining unit-profile input is now the left-reduced-density diagonal
trace-power domination statement; the coordinate-overlap comparison is closed
in `LowerUnitProfileConcreteChoices`. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_leftDensityDiagonalPowerFrontierInputs
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hLeftDensity :
      lowerConcreteRankOneProjectorGammaTracePowerDominatesLeftDensityDiagonalPower k)
    (hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
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
    lower_eventual_log_over_spikeSpeed_concreteModel_of_traceDominanceFrontierInputs
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerConcreteRankOneProjectorGammaTracePowerDominatesCoordinateOverlap_of_leftDensityDiagonalPower
        hLeftDensity)
      hMeanBound
      hMixedEnvelope
      hReference
      hMoment

/-- Clean lower endpoint with the trace/unit-profile frontier split into the
two local Schmidt-side ingredients.

This is the most local deterministic frontier currently exposed for the
unit-profile block:

* `hDiag`: diagonal-power ≤ reduced-density trace-power;
* `hTraceEq`: reduced-density trace-power equals the partial-transpose
  rank-one trace-power.

Together they recover the left-density diagonal frontier and therefore the
coordinate-overlap trace-dominance route. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_leftDensitySplitFrontierInputs
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hDiag :
      lowerLeftReducedDensityDiagonalPowerLeTracePower k)
    (hTraceEq :
      lowerRankOneProjectorGammaTracePowerEqLeftReducedDensityTracePower k)
    (hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
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
    lower_eventual_log_over_spikeSpeed_concreteModel_of_leftDensityDiagonalPowerFrontierInputs
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerConcreteRankOneProjectorGammaTracePowerDominatesLeftDensityDiagonalPower_of_split
        hDiag
        (lowerRankOneProjectorGammaTracePowerDominatesLeftReducedDensityTracePower_of_eq
          hTraceEq))
      hMeanBound
      hMixedEnvelope
      hReference
      hMoment

/-- Clean lower endpoint with the corrected scale-budget frontier stated as a
finite limit of the deleted-background mean.

This is the most concrete scalar-facing version of the current frontier: the
old unrestricted scale-loss predicate is not used, and the scale route is
reduced to proving `lowerConcreteDeletedBackgroundMean R k d` converges. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_traceDominanceAndMeanLimitFrontierInputs
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε m : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hTraceDominance :
      lowerConcreteRankOneProjectorGammaTracePowerDominatesCoordinateOverlap k)
    (hMeanLimit :
      Tendsto (fun d : ℕ => lowerConcreteDeletedBackgroundMean R k d)
        atTop (nhds m))
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
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
    lower_eventual_log_over_spikeSpeed_concreteModel_of_traceDominanceFrontierInputs
      (R := R) (k := k) (ε := ε) hk3 hε
      hTraceDominance
      (lower_concrete_deletedBackgroundMean_positivePartEventuallyBounded_of_tendsto
        (R := R) (k := k) (m := m) hMeanLimit)
      hMixedEnvelope
      hReference
      hMoment

/-- Clean lower endpoint with the scale/mean frontier stated as existence of a
finite deleted-background mean limit.

Compared with
`lower_eventual_log_over_spikeSpeed_concreteModel_of_traceDominanceAndMeanLimitFrontierInputs`,
this removes the arbitrary limit witness `m` from the public signature.  It is
still conditional: the finite-limit statement is a visible theorem assumption,
not proved here. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_traceDominanceAndMeanHasFiniteLimitFrontierInputs
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hTraceDominance :
      lowerConcreteRankOneProjectorGammaTracePowerDominatesCoordinateOverlap k)
    (hMeanLimit :
      ∃ m : ℝ,
        Tendsto (fun d : ℕ => lowerConcreteDeletedBackgroundMean R k d)
          atTop (nhds m))
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
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
  rcases hMeanLimit with ⟨m, hm⟩
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_traceDominanceAndMeanLimitFrontierInputs
      (R := R) (k := k) (ε := ε) (m := m) hk3 hε
      hTraceDominance
      hm
      hMixedEnvelope
      hReference
      hMoment

/-- Clean lower endpoint with the moment frontier stated for the closed
absolute-deviation event.

The lower background half-mass pipeline consumes the strict bad set
`backgroundMomentBadSet`, but concentration arguments usually produce the
closed event `backgroundMomentDeviationSet`.  This wrapper closes that
strict/closed event conversion; the deviation probability estimate itself
remains a visible input. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_closedDeviationMomentFrontierInputs
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hTraceDominance :
      lowerConcreteRankOneProjectorGammaTracePowerDominatesCoordinateOverlap k)
    (hMeanLimit :
      ∃ m : ℝ,
        Tendsto (fun d : ℕ => lowerConcreteDeletedBackgroundMean R k d)
          atTop (nhds m))
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
    (hReference :
      ∀ᶠ d in atTop,
        ∀ i₀ : BipIndex (Fin d) (Fin d),
          SurfaceReferenceProjectiveCapConeCoordinateFormula
            (BipIndex (Fin d) (Fin d)) i₀)
    (hMomentDeviation :
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
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_traceDominanceAndMeanHasFiniteLimitFrontierInputs
      (R := R) (k := k) (ε := ε) hk3 hε
      hTraceDominance
      hMeanLimit
      hMixedEnvelope
      hReference
      (lower_backgroundMomentTail_concreteChoices_of_deviationBound
        (R := R) (k := k) hMomentDeviation)

/-- Mean-bound variant of
`lower_eventual_log_over_spikeSpeed_concreteModel_of_closedDeviationMomentFrontierInputs`.

This removes the finite-limit assumption from the active closed-deviation
frontier: the corrected scale route now depends directly on the bounded positive
part of the deleted-background mean. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_closedDeviationMomentFrontierInputs_meanBound
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hTraceDominance :
      lowerConcreteRankOneProjectorGammaTracePowerDominatesCoordinateOverlap k)
    (hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
    (hReference :
      ∀ᶠ d in atTop,
        ∀ i₀ : BipIndex (Fin d) (Fin d),
          SurfaceReferenceProjectiveCapConeCoordinateFormula
            (BipIndex (Fin d) (Fin d)) i₀)
    (hMomentDeviation :
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
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_cleanFrontierInputs
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerConcreteCanonicalCapSpikeTraceStability_of_overlapLower
        (lt_of_lt_of_le (by decide : 1 < 3) hk3)
        hε
        (lowerConcreteCanonicalCapTracePowerOverlapLower_of_traceDominatesCoordinateOverlap
          hTraceDominance))
      hMeanBound
      hMixedEnvelope
      hReference
      (lower_backgroundMomentTail_concreteChoices_of_deviationBound
        (R := R) (k := k) hMomentDeviation)

/-- Legacy compatibility shim after closing `hReference`.

The active lower frontier now runs through `hMeanBound`; this older theorem is
kept only for callers that still package the mean-side debt as existence of a
finite limit. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceFrontierInputs
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hTraceDominance :
      lowerConcreteRankOneProjectorGammaTracePowerDominatesCoordinateOverlap k)
    (hMeanLimit :
      ∃ m : ℝ,
        Tendsto (fun d : ℕ => lowerConcreteDeletedBackgroundMean R k d)
          atTop (nhds m))
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
    (hMomentDeviation :
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
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closedDeviationMomentFrontierInputs
      (R := R) (k := k) (ε := ε) hk3 hε
      hTraceDominance
      hMeanLimit
      hMixedEnvelope
      lower_referenceCone_BipIndex_Fin_eventually_concreteChoices
      hMomentDeviation

/-- No-reference mean-bound variant of
`lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceFrontierInputs`.

This is the sharp closed-deviation endpoint with `hReference` and
`hMeanLimit` both removed from the visible frontier assumptions. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceFrontierInputs_meanBound
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hTraceDominance :
      lowerConcreteRankOneProjectorGammaTracePowerDominatesCoordinateOverlap k)
    (hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
    (hMomentDeviation :
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
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_closedDeviationMomentFrontierInputs_meanBound
      (R := R) (k := k) (ε := ε) hk3 hε
      hTraceDominance
      hMeanBound
      hMixedEnvelope
      lower_referenceCone_BipIndex_Fin_eventually_concreteChoices
      hMomentDeviation

/-- Legacy compatibility shim after closing both `hReference` and the
coordinate-overlap part of `hTraceDominance`.

The live lower branch no longer treats `hMeanLimit` as source-of-truth; this
wrapper remains only for downstream code that still exposes the finite-limit
form of the mean-side debt. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_leftDensity_noReferenceFrontierInputs
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hLeftDensity :
      lowerConcreteRankOneProjectorGammaTracePowerDominatesLeftDensityDiagonalPower k)
    (hMeanLimit :
      ∃ m : ℝ,
        Tendsto (fun d : ℕ => lowerConcreteDeletedBackgroundMean R k d)
          atTop (nhds m))
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
    (hMomentDeviation :
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
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceFrontierInputs
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerConcreteRankOneProjectorGammaTracePowerDominatesCoordinateOverlap_of_leftDensityDiagonalPower
        hLeftDensity)
      hMeanLimit
      hMixedEnvelope
      hMomentDeviation

/-- Left-density/no-reference mean-bound endpoint.

This is the same closed-deviation route as
`lower_eventual_log_over_spikeSpeed_concreteModel_of_leftDensity_noReferenceFrontierInputs`,
but with the finite mean-limit assumption replaced by the active scale-frontier
hypothesis `hMeanBound`. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_leftDensity_noReferenceFrontierInputs_meanBound
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hLeftDensity :
      lowerConcreteRankOneProjectorGammaTracePowerDominatesLeftDensityDiagonalPower k)
    (hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
    (hMomentDeviation :
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
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceFrontierInputs_meanBound
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerConcreteRankOneProjectorGammaTracePowerDominatesCoordinateOverlap_of_leftDensityDiagonalPower
        hLeftDensity)
      hMeanBound
      hMixedEnvelope
      hMomentDeviation

/-- Sharp no-reference mean-bound endpoint after closing the stale
`hLeftDensity` frontier.

The left-density trace-power dominance is now supplied by
`lowerConcreteRankOneProjectorGammaTracePowerDominatesLeftDensityDiagonalPower_closed`,
so this wrapper exposes only the currently live lower-side debts:
mean boundedness, mixed envelope, and the mean-centered moment deviation tail. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceFrontierInputs_meanBound
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
    (hMomentDeviation :
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
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_leftDensity_noReferenceFrontierInputs_meanBound
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerConcreteRankOneProjectorGammaTracePowerDominatesLeftDensityDiagonalPower_closed k)
      hMeanBound
      hMixedEnvelope
      hMomentDeviation

/-- Sharp no-reference closed-trace endpoint with the repaired mixed frontier.

This is the version to track for `hMixedEnvelope`: the stale fixed-budget
predicate is gone from the signature.  The remaining mixed-side obligations are
the explicit-envelope pointwise bound and the scalar fact that this envelope is
eventually arbitrarily small. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceFrontierInputs_meanBound_withMixedError
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k)
    (errMix : ℝ → ℝ → ℕ → ℝ)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithError R k ε errMix)
    (hMixedSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errMix a slack d ≤ η)
    (hMomentDeviation :
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
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_cleanFrontierInputs_withMixedError
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerConcreteCanonicalCapSpikeTraceStability_of_overlapLower
        (lt_of_lt_of_le (by decide : 1 < 3) hk3)
        hε
        (lowerConcreteCanonicalCapTracePowerOverlapLower_of_traceDominatesCoordinateOverlap
          (lowerConcreteRankOneProjectorGammaTracePowerDominatesCoordinateOverlap_of_leftDensityDiagonalPower
            (lowerConcreteRankOneProjectorGammaTracePowerDominatesLeftDensityDiagonalPower_closed k))))
      hMeanBound
      errMix
      hMixedEnvelope
      hMixedSmall
      lower_referenceCone_BipIndex_Fin_eventually_concreteChoices
      (lower_backgroundMomentTail_concreteChoices_of_deviationBound
        (R := R) (k := k) hMomentDeviation)

/-- Sharp no-reference closed-trace endpoint on the repaired PT mixed-error
route, with mixed-error eventual smallness discharged automatically.

When the explicit mixed envelope uses the deterministic PT budget
`lowerPartialTransposeMixedErrorD`, its `o(1)` smallness follows from
`lowerPartialTransposeMixedErrorD_tendsto_zero`; no separate `hMixedSmall`
input is needed. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceFrontierInputs_meanBound_withPTMixedError
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k)
    (A M : ℝ)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithError R k ε
        (fun _a _slack d => lowerPartialTransposeMixedErrorD k A M d))
    (hMomentDeviation :
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
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceFrontierInputs_meanBound_withMixedError
      (R := R) (k := k) (ε := ε) hk3 hε
      hMeanBound
      (fun _a _slack d => lowerPartialTransposeMixedErrorD k A M d)
      hMixedEnvelope
      (by
        intro a _ha slack _hslack η hη
        exact
          lowerPartialTransposeMixedErrorD_eventually_le
            (k := k) hk3 A M η hη)
      hMomentDeviation

/-- Sharp no-reference closed-trace PT mixed-error endpoint with the
two-trace Wick/Chebyshev deleted-background moment tail.

This is the endpoint form matching the current repaired proof stack: bounded
positive part of the mean, explicit PT `errMix`, and the polynomial
second-moment background typicality estimate at the `1 / d` threshold. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceFrontierInputs_meanBound_withPTMixedError_secondMomentWickMomentTail
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k)
    (A M : ℝ)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithError R k ε
        (fun _a _slack d => lowerPartialTransposeMixedErrorD k A M d))
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  have hk : 1 < k := lt_of_lt_of_le (by decide : 1 < 3) hk3
  rcases
    lowerConcreteDeletedBackgroundMomentSecondMomentWickBadTailBound_of_deviationTailBound
      (R := R) (k := k) hMomentSecond with
    ⟨C, _hC, hMomentBad⟩
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_concreteScalarChoices_sphereBetaScaleBudget_withMomentBudgetAndMixedError
      (R := R) (k := k) (ε := ε) hk hε
      (bMoment := lowerConcreteMomentPolynomialBound C R k)
      (errMix := fun _a _slack d => lowerPartialTransposeMixedErrorD k A M d)
      (lower_unitProfile_canonicalDirection_concreteChoices_of_traceStability
        hk hε
        (lowerConcreteCanonicalCapSpikeTraceStability_of_overlapLower
          (lt_of_lt_of_le (by decide : 1 < 3) hk3)
          hε
          (lowerConcreteCanonicalCapTracePowerOverlapLower_of_traceDominatesCoordinateOverlap
            (lowerConcreteRankOneProjectorGammaTracePowerDominatesCoordinateOverlap_of_leftDensityDiagonalPower
              (lowerConcreteRankOneProjectorGammaTracePowerDominatesLeftDensityDiagonalPower_closed k)))))
      (lower_scaleBudget_concreteChoices_of_meanPositivePartEventuallyBounded
        (R := R) (k := k) (ε := ε) hk3 hε hMeanBound)
      (lower_mixedLowerOnSphere_concreteChoices_of_localExpansionEnvelopeOnSphereWithError
        (R := R) (k := k) (ε := ε)
        (fun _a _slack d => lowerPartialTransposeMixedErrorD k A M d)
        hMixedEnvelope)
      (by
        intro a _ha slack _hslack η hη
        exact
          lowerPartialTransposeMixedErrorD_eventually_le
            (k := k) hk3 A M η hη)
      lower_referenceCone_BipIndex_Fin_eventually_concreteChoices
      hMomentBad
      (lower_concrete_polynomialMomentSmall C R k)

/-- Sharp no-reference closed-trace PT mixed-error endpoint with the concrete
mixed supplier already assembled.

The PT mixed error is the corrected dynamic budget
`lowerPartialTransposeMixedErrorD k (a + slack) M d`, so no fixed `A` and no
arbitrary word-bound/budget pair appears in the endpoint statement. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceFrontierInputs_meanBound_withPTMixedError_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k)
    (M : ℝ)
    (hMixed :
      mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M)
    (hMomentDeviation :
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
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceFrontierInputs_meanBound_withMixedError
      (R := R) (k := k) (ε := ε) hk3 hε
      hMeanBound
      (fun a slack d => lowerPartialTransposeMixedErrorD k (a + slack) M d)
      (lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithPTError_of_mixed_noL_atLeastTwoQ_ge_neg_errMix
        R k ε M hMixed)
      (by
        intro a _ha slack _hslack η hη
        exact
          lowerPartialTransposeMixedErrorD_eventually_le
            (k := k) hk3 (a + slack) M η hη)
      hMomentDeviation

/-- Sharp no-reference closed-trace fixed-`M` PT endpoint with the
paper-facing variance/Chebyshev background frontier.

This is the variance-stack version of
`...meanBound_withPTMixedError_splitMixedWordBudget`: the endpoint no longer
asks for the raw closed-deviation inequality, but for the named theorem
`deletedColumnSphericalMoment_variance_le_const_div_d4`. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceFrontierInputs_meanBound_withPTMixedError_splitMixedWordBudget_varianceStack
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k)
    (M : ℝ)
    (hMixed :
      mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  have hk : 1 < k := lt_of_lt_of_le (by decide : 1 < 3) hk3
  have hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k :=
    lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound_of_deletedColumnSphericalMoment_variance_le_const_div_d4
      R k hVariance
  rcases
    lowerConcreteDeletedBackgroundMomentSecondMomentWickBadTailBound_of_deviationTailBound
      (R := R) (k := k) hMomentSecond with
    ⟨C, _hC, hMomentBad⟩
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_concreteScalarChoices_sphereBetaScaleBudget_withMomentBudgetAndMixedError
      (R := R) (k := k) (ε := ε) hk hε
      (bMoment := lowerConcreteMomentPolynomialBound C R k)
      (errMix := fun a slack d => lowerPartialTransposeMixedErrorD k (a + slack) M d)
      (lower_unitProfile_canonicalDirection_concreteChoices_of_traceStability
        hk hε
        (lowerConcreteCanonicalCapSpikeTraceStability_of_overlapLower
          (lt_of_lt_of_le (by decide : 1 < 3) hk3)
          hε
          (lowerConcreteCanonicalCapTracePowerOverlapLower_of_traceDominatesCoordinateOverlap
            (lowerConcreteRankOneProjectorGammaTracePowerDominatesCoordinateOverlap_of_leftDensityDiagonalPower
              (lowerConcreteRankOneProjectorGammaTracePowerDominatesLeftDensityDiagonalPower_closed k)))))
      (lower_scaleBudget_concreteChoices_of_meanPositivePartEventuallyBounded
        (R := R) (k := k) (ε := ε) hk3 hε hMeanBound)
      (lower_mixedLowerOnSphere_concreteChoices_of_localExpansionEnvelopeOnSphereWithError
        (R := R) (k := k) (ε := ε)
        (fun a slack d => lowerPartialTransposeMixedErrorD k (a + slack) M d)
        (lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithPTError_of_mixed_noL_atLeastTwoQ_ge_neg_errMix
          R k ε M hMixed))
      (by
        intro a _ha slack _hslack η hη
        exact
          lowerPartialTransposeMixedErrorD_eventually_le
            (k := k) hk3 (a + slack) M η hη)
      lower_referenceCone_BipIndex_Fin_eventually_concreteChoices
      hMomentBad
      (lower_concrete_polynomialMomentSmall C R k)

/-- Sharp no-reference closed-trace fixed-`M` PT endpoint with the mean side
stated as finite-limit existence and the background side stated as the
paper-facing variance/Chebyshev theorem.

This removes the repaired scalar helper
`lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded` from the
variance-stack fixed-`M` PT branch.  The remaining mean-side input is the
sharper reusable statement that `lowerConcreteDeletedBackgroundMean R k d` has
a finite limit. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceFrontierInputs_meanHasFiniteLimit_withPTMixedError_splitMixedWordBudget_varianceStack
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanLimit :
      ∃ m : ℝ,
        Tendsto (fun d : ℕ => lowerConcreteDeletedBackgroundMean R k d)
          atTop (nhds m))
    (M : ℝ)
    (hMixed :
      mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceFrontierInputs_meanBound_withPTMixedError_splitMixedWordBudget_varianceStack
      (R := R) (k := k) (ε := ε) hk3 hε
      (lower_concrete_deletedBackgroundMean_positivePartEventuallyBounded_of_hasFiniteLimit
        (R := R) (k := k) hMeanLimit)
      M hMixed hVariance

/-- Sharp no-reference closed-trace endpoint with explicit mixed error and the
mean-side frontier stated as finite-limit existence.

This is the mixed-error analogue of
`..._meanHasFiniteLimit`: it removes the repaired scalar helper
`hMeanBound` from the sharp mixed route, keeping the remaining mean-side debt
as the explicit finite-limit statement for
`lowerConcreteDeletedBackgroundMean R k d`. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceFrontierInputs_meanHasFiniteLimit_withMixedError
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanLimit :
      ∃ m : ℝ,
        Tendsto (fun d : ℕ => lowerConcreteDeletedBackgroundMean R k d)
          atTop (nhds m))
    (errMix : ℝ → ℝ → ℕ → ℝ)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithError R k ε errMix)
    (hMixedSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errMix a slack d ≤ η)
    (hMomentDeviation :
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
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceFrontierInputs_meanBound_withMixedError
      (R := R) (k := k) (ε := ε) hk3 hε
      (lower_concrete_deletedBackgroundMean_positivePartEventuallyBounded_of_hasFiniteLimit
        (R := R) (k := k) hMeanLimit)
      errMix hMixedEnvelope hMixedSmall hMomentDeviation

/-- Sharp no-reference closed-trace endpoint with the mean-side frontier stated
as existence of a finite deleted-background mean limit.

This removes the stale `hMeanBound` parameter from the sharp endpoint.  The
remaining mean-side mathematical debt is now the sharper and reusable statement
that `lowerConcreteDeletedBackgroundMean R k d` has a finite limit. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceFrontierInputs_meanHasFiniteLimit
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanLimit :
      ∃ m : ℝ,
        Tendsto (fun d : ℕ => lowerConcreteDeletedBackgroundMean R k d)
          atTop (nhds m))
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
    (hMomentDeviation :
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
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceFrontierInputs_meanBound
      (R := R) (k := k) (ε := ε) hk3 hε
      (lower_concrete_deletedBackgroundMean_positivePartEventuallyBounded_of_hasFiniteLimit
        (R := R) (k := k) hMeanLimit)
      hMixedEnvelope
      hMomentDeviation

end AppendixB
