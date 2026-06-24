# Lean File Atlas

Last updated: 2026-06-02.

Purpose: keep one trustworthy map of the current Lean frontier. This atlas is
for active endpoints, live supplier leaves, and the shortest audited adapter
routes. It is not a transcript dump and it is not a history log of every
compatibility wrapper.

## Atlas Rules

- One canonical active endpoint per live branch.
- At most one source-explicit endpoint per branch when it materially clarifies
  the real inputs.
- Only assumptions visible on the chosen endpoint count as live frontier.
- Old compatibility wrappers are archived by summary, not tracked as parallel
  active debt.
- Draft, handoff, or staging files with any `sorry` are off-table as supplier
  candidates, even if their names sound relevant.
- "Aristotle" is not a status signal by itself. Only compiled, imported, and
  audited local theorems count as suppliers.
- Raw search transcripts, repeated `#print axioms` blocks, and duplicate theorem
  lists do not belong here.
- When this atlas says an endpoint is audited, read that as "proved from its
  explicit hypotheses with only Lean/mathlib foundational dependencies."  It is
  not a claim that the surrounding upper/lower random-matrix theorem is
  hypothesis-free unless the printed endpoint signature has no theorem-strength
  inputs left.

## Latest Atlas Delta

2026-06-02:

- Challenge Before:
  The shortest canonical envelope bridge still used a generic polynomial `Q`
  and exposed the real-power side conditions
  `0 ≤ d + Q k` and `0 ≤ sqrt s + Q k`.  For Aubrun's explicit polynomial
  these are nonnegativity adapters, not surviving-contraction combinatorics.
- Challenge After:
  `AppendixB.gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ`
  at `PptFactorization/AppendixBPipelineGraduate.lean:600` is now the shortest
  article-facing upper expectation/spherical bridge on this route.  It fixes
  `Q = aubrunProposition71Q C0`, closes the side conditions from `0 ≤ C0`, and
  leaves the single theorem-strength input
  `AubrunGraduateRelationCounting (aubrunProposition71Q C0) (dNat : ℝ)
  (sNat : ℝ) (aubrunEvenMomentParameter dNat - 1)`.
- Verification:
  `lake build PptFactorization.AppendixBPipelineGraduate`,
  `lake env lean /tmp/check_pipeline_canonical_explicitQ.lean`, and
  `lake build PptFactorization` pass; the new endpoint audits to `[propext,
  Classical.choice, Quot.sound]`.

- Challenge Before:
  The paper-facing lower endpoint with mean and variance inputs still consumed
  the mixed side through the broad packaged frontier
  `lowerConcreteMixedErrorFrontier R k ε errMix`, even though the literal PT
  branch had already decomposed that frontier through direct scalar leaves on
  other routes.
- Challenge After:
  `AppendixB.lowerConcreteMixedErrorFrontier_of_PTScaleComparisons` at
  `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:3445`
  supplies the literal PT mixed frontier from the two scalar scale comparisons.
  The paper-facing endpoint
  `AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanMeanAndVarianceStack_withPTScaleComparisons_splitMixedWordBudget`
  at `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:3672`
  now leaves exactly the PT Catalan mean theorem, the PT variance theorem,
  nonnegative `M`, and the one-`Q`/many-`Q` PT scale comparisons visible.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices`
  passes; `lake env lean /tmp/check_lower_paper_scale.lean` checks both public
  signatures; both audit to `[propext, Classical.choice, Quot.sound]`.

- Challenge Before:
  The new paper-facing scale-comparison endpoint could be mistaken for the
  current unconditional lower path, even though the fixed-`M` packet is known
  to be incompatible with the runtime lower construction at length three.
- Challenge After:
  `AppendixB.lower_paperFacingPTScaleComparisonPacket_three_not_uniform` at
  `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:3706`
  records the local no-go: for `k = 3`, nonnegative fixed `M`, and `0 < ε`,
  the one-`Q`/many-`Q` PT scale-comparison packet is impossible.  Treat
  `...withPTScaleComparisons...` as diagnostic/compatibility only.  The live
  paper-facing lower route is
  `AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanMeanAndVarianceStack_withMixedErrorFrontier_splitMixedWordBudget`,
  whose live inputs are the PT Catalan mean theorem, the PT variance theorem,
  and an honest mixed frontier tying one envelope to its own eventual
  smallness.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices`
  passes; `lake env lean /tmp/check_lower_paper_scale_nogo.lean` checks the
  no-go signature; the no-go theorem audits to `[propext, Classical.choice,
  Quot.sound]`.

- Challenge Before:
  The runtime-native mixed-error route was refuted at the scalar-smallness
  layer, but the public lower endpoint consumes
  `lowerConcreteMixedErrorFrontier R k ε errMix`, so the impossibility was not
  available in the exact packaged shape.
- Challenge After:
  `AppendixB.lowerConcreteMixedRuntimeWordError_three_not_mixedErrorFrontier`
  at `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:3505`
  proves that the runtime-native error cannot satisfy the honest mixed
  frontier at `k = 3`.  The deterministic runtime envelope remains useful as a
  diagnostic supplier, but the live lower proof must find a genuinely
  vanishing mixed `errMix` or sharpen the favourable event.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices`
  passes; `lake env lean /tmp/check_runtime_frontier_nogo.lean` checks the
  signature; the theorem audits to `[propext, Classical.choice, Quot.sound]`.

- Challenge Before:
  The sharpest length-three endpoint still consumed the broad variance/Chebyshev
  predicate `deletedColumnSphericalMoment_variance_le_const_div_d4 R 3`.
- Challenge After:
  `AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanErrorMeanAndExponentialTailStack_k3_withMixedErrorComponents_splitMixedWordBudget`
  at `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:3759`
  replaces that input by
  `lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R 3`.
  The endpoint derives the variance/Chebyshev predicate internally via
  `deletedColumnSphericalMoment_variance_le_const_div_d4_of_exponentialDeviationTailBound`.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices`
  passes; `lake env lean
  /tmp/check_lower_k3_mean_error_exp_tail_components.lean` checks the
  signature; the theorem audits to `[propext, Classical.choice, Quot.sound]`.

- Challenge Before:
  The length-three component endpoint still consumed the broad paper-facing
  mean theorem `deletedColumnSphericalMean_tendsto_ptCatalan R.sample 3 R.lam`.
- Challenge After:
  `AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanErrorMeanAndVarianceStack_k3_withMixedErrorComponents_splitMixedWordBudget`
  at `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:3721`
  replaces that broad mean input by
  `lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample 3`.
  The endpoint derives the PT Catalan mean internally using the existing
  balanced-regime deleted-column ratio adapter.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices`
  passes; `lake env lean /tmp/check_lower_k3_mean_error_components.lean`
  checks the signature; the theorem audits to `[propext, Classical.choice,
  Quot.sound]`.

- Challenge Before:
  The concrete length-three lower endpoint still packaged the mixed side as
  `lowerConcreteMixedErrorFrontier R 3 ε errMix`.
- Challenge After:
  `AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanMeanAndVarianceStack_k3_withMixedErrorComponents_splitMixedWordBudget`
  at `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:3689`
  is the component-level length-three endpoint.  The mixed leaves are now
  explicit: a sphere-supported mixed local-expansion envelope and eventual
  smallness for the same `errMix`.  PT Catalan mean and PT variance at `3`
  remain separate hard inputs.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices`
  passes; `lake env lean /tmp/check_lower_k3_mixed_components.lean` checks the
  signature; the theorem audits to `[propext, Classical.choice, Quot.sound]`.

- Challenge Before:
  The preferred paper-facing lower endpoint still exposed the moment-length
  bookkeeping hypothesis `hk3 : 3 ≤ k`.
- Challenge After:
  `AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanMeanAndVarianceStack_k3_withMixedErrorFrontier_splitMixedWordBudget`
  at `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:3690`
  is the concrete length-three form of the honest mixed-frontier route.  It
  removes `hk3`; the remaining hard inputs are the PT Catalan mean at `3`, the
  PT variance theorem at `3`, and `lowerConcreteMixedErrorFrontier R 3 ε
  errMix`.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices`
  passes; `lake env lean /tmp/check_lower_k3_mixed_frontier.lean` checks the
  signature; the theorem audits to `[propext, Classical.choice, Quot.sound]`.

- Challenge Before:
  The sharpest upper profile-count endpoint still had an arbitrary scalar
  constant `C0` and a visible scalar proof obligation `0 ≤ C0`.
- Challenge After:
  `AppendixB.gammaExpectation_pipeline_to_spherical_bound_of_profile_count_sum_canonical_Qone`
  at `PptFactorization/AppendixBPipelineGraduate.lean:723` specializes the
  public frontier to the concrete envelope `aubrunProposition71Q 1`, i.e.
  `Q(k)=k(2k)^36`.  The hard mathematical input remains the same finite
  `wickRelationProfileCount` sum bound; the scalar nonnegativity obligation is
  now discharged inside Lean.
- Verification:
  `lake build PptFactorization.AppendixBPipelineGraduate` passes.

- Challenge Before:
  The upper explicit-`Q` graduate endpoint exposed
  `AubrunGraduateRelationCounting` as its remaining hard input, although the
  local graduate file already proves that this broad interface follows from a
  concrete finite profile-count sum.
- Challenge After:
  `AppendixB.gammaExpectation_pipeline_to_spherical_bound_of_profile_count_sum_canonical_explicitQ`
  at `PptFactorization/AppendixBPipelineGraduate.lean:657` is the sharper
  explicit-`Q` upper endpoint.  It consumes the finite profile-count inequality
  directly and internally applies
  `AppendixB.aubrunGraduateRelationCounting_of_profileCountSumBound`.  The
  remaining upper theorem-strength input is now exactly the finite
  `wickRelationProfileCount` sum bound for
  `m = aubrunEvenMomentParameter dNat - 1`, not the broader relation-counting
  wrapper.
- Verification:
  `lake build PptFactorization.AppendixBPipelineGraduate` passes;
  `lake env lean /tmp/check_upper_profile_explicitQ.lean` checks the signature;
  the endpoint audits to `[propext, Classical.choice, Quot.sound]`.

- Challenge Before:
  The shortest canonical diagonal-closed bridge still exposed the auxiliary
  scalar comparison
  `aubrunOffDiagonalExpectationEnvelope Q (dNat : ℝ) (sNat : ℝ) k ≤ COff`.
  This comparison only chose an off-diagonal bookkeeping constant; it did not
  represent the hard Aubrun relation-counting estimate.
- Challenge After:
  `AppendixB.gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_envelope`
  at `PptFactorization/AppendixBPipelineGraduate.lean:551` is now the shortest
  canonical graduate-counting-to-spherical-mean bridge.  It sets `COff` equal
  to the explicit Aubrun expectation envelope, so the conclusion carries that
  formula directly.  The remaining theorem-strength upper input is
  `AubrunGraduateRelationCounting Q (dNat : ℝ) (sNat : ℝ)
  (aubrunEvenMomentParameter dNat - 1)`.  Scalar positivity and side
  conditions remain visible in the printed statement.
- Verification:
  `lake build PptFactorization.AppendixBPipelineGraduate`,
  `lake env lean /tmp/check_pipeline_canonical_envelope.lean`, and
  `lake build PptFactorization` pass; the new endpoint audits to `[propext,
  Classical.choice, Quot.sound]`.

- Challenge Before:
  The shortest canonical polar-closed graduate-counting bridge still exposed
  the diagonal expectation hypothesis
  `gaussianWishartGammaDiagonalOpNormMean ≤ CDiag`, although
  `AppendixBDiagonalGamma` already proved the concrete `C_lambda` estimate for
  the diagonal Gamma-max observable.
- Challenge After:
  `AppendixB.gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_polar_diagonal_closed`
  at `PptFactorization/AppendixBPipelineGraduate.lean:495` is now the shortest
  canonical graduate-counting-to-spherical-mean bridge.  It supplies the
  diagonal input from
  `AppendixB.gaussianWishartGammaDiagonalOpNormMean_le_C_lambda`, fixing the
  diagonal constant to `2 * Real.log 2 + 4 / lam` under
  `lam * (dNat : ℝ)^2 ≤ (sNat : ℝ)`.  The remaining theorem-strength upper
  inputs are graduate relation counting and the scalar off-diagonal envelope
  bound, plus scalar positivity/side conditions in the printed statement.
- Verification:
  `lake build PptFactorization.AppendixBPipelineGraduate`,
  `lake env lean /tmp/check_pipeline_canonical_polar_diagonal_closed.lean`,
  and `lake build PptFactorization` pass; both the new endpoint and diagonal
  supplier audit to `[propext, Classical.choice, Quot.sound]`.

- Challenge Before:
  The shortest canonical-scale graduate-counting bridge still exposed
  radius-squared/direction independence and positivity of the squared radial
  mean for the concrete `Fin dNat, Fin dNat, Fin sNat` Gaussian model.  These
  inputs were active in the endpoint signature, but audited suppliers already
  existed in the polar/radial stack.
- Challenge After:
  `AppendixB.gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_polar_closed`
  at `PptFactorization/AppendixBPipelineGraduate.lean:428` is now the shortest
  canonical graduate-counting-to-spherical-mean bridge.  It supplies
  radius-squared/direction independence from
  `AppendixB.gaussianRadiusSq_indep_gaussianDirection` and radial positivity
  from `AppendixB.gaussianQuadraticRadialMean_pos`.  The remaining
  theorem-strength upper inputs are graduate relation counting, the scalar
  off-diagonal envelope bound, and the diagonal expectation bound, plus the
  scalar positivity side conditions in the printed statement.
- Verification:
  `lake build PptFactorization.AppendixBPipelineGraduate`,
  `lake env lean /tmp/check_pipeline_canonical_polar_closed.lean`, and
  `lake build PptFactorization` pass; the new public endpoint audits to
  `[propext, Classical.choice, Quot.sound]`.

- Challenge Before:
  The shortest graduate-counting pipeline endpoint still exposed complex
  trace-integrability of the off-diagonal Wishart-Gamma trace power at
  `aubrunEvenMomentParameter dNat`.  The Wick expansion had already used
  entry-monomial integrability internally, but that integrability was not a
  separately available supplier for the Appendix B bridge.
- Challenge After:
  `AppendixB.gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_with_trace_integrability_closed`
  at `PptFactorization/AppendixBPipelineGraduate.lean:297` is now the shortest
  graduate-counting-to-spherical-mean bridge.  It supplies trace-integrability
  from `TraceWickExpansion.trace_pow_succ_integrable_of_monomial_expansion` at
  `PptFactorization/TraceWickExpansion.lean:209` and
  `TraceWickExpansion.trace_pow_succ_wishartGammaOffDiagonal_integrable` at
  `PptFactorization/TraceWickProductExpansion.lean:222`.
  The remaining theorem-strength upper inputs are graduate relation counting,
  scalar envelope/model comparison, diagonal expectation, and radial/spherical
  normalization.
- Verification:
  `lake build PptFactorization.TraceWickProductExpansion`,
  `lake build PptFactorization.AppendixBPipelineGraduate`,
  `lake env lean /tmp/check_trace_closed_bridge.lean`, and
  `lake build PptFactorization` pass; the new public bridge and both suppliers
  audit to `[propext, Classical.choice, Quot.sound]`.

- Challenge Before:
  The shortest graduate-counting pipeline endpoint still exposed the
  high-moment `MemLp` input for the off-diagonal Wishart-Gamma operator norm at
  `aubrunEvenMomentParameter dNat`.  This was an integrability/plumbing leaf,
  separate from the real Aubrun relation-counting and trace-moment estimates.
- Challenge After:
  `AppendixB.gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_with_memLp_closed`
  at `PptFactorization/AppendixBPipelineGraduate.lean:226` is now the shortest
  bridge.  It supplies the `MemLp` input from
  `AppendixB.gaussianWishartGammaOffDiagonalOpNorm_memLp_nat` at
  `PptFactorization/AppendixBGaussianIntegrability.lean:410`, which in turn
  uses `AppendixB.gaussianMass_pow_integrable` at
  `PptFactorization/AppendixBGaussianIntegrability.lean:350`.
  The remaining theorem-strength inputs are complex trace-integrability,
  graduate relation counting, scalar envelope/model comparison, diagonal
  expectation, and radial/spherical normalization.
- Verification:
  `lake build PptFactorization.AppendixBGaussianIntegrability`,
  `lake build PptFactorization.AppendixBPipelineGraduate`,
  `lake env lean /tmp/check_pipeline_graduate_memlp_closed.lean`, and
  `lake build PptFactorization` pass; all three new public declarations audit
  to `[propext, Classical.choice, Quot.sound]`.

- Challenge Before:
  The graduate-counting pipeline bridge still asked callers for the full,
  diagonal, and off-diagonal Wishart-Gamma operator-norm L¹ integrability
  assumptions, although `AppendixBGaussianIntegrability` already closed those
  elementary Gaussian domination facts.
- Challenge After:
  `AppendixB.gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_with_integrability_closed`
  at `PptFactorization/AppendixBPipelineGraduate.lean:145` is now the shortest
  graduate-counting-to-spherical-mean route with downstream L¹ integrability
  discharged.  It keeps the high-moment `MemLp` and complex trace-integrability
  assumptions visible because those belong to the Aubrun moment extraction, not
  to the elementary expectation split.
- Verification:
  `lake build PptFactorization.AppendixBPipelineGraduate`,
  `lake env lean /tmp/check_pipeline_graduate_closed.lean`, and
  `lake build PptFactorization` pass; the public declaration audits to
  `[propext, Classical.choice, Quot.sound]`.

- Challenge Before:
  The Appendix B expectation/spherical pipeline consumed an abstract
  `AubrunOffDiagonalExpectationDerivation` object.  The graduate-counting file
  had a checked constructor for that object, but the shortest public route from
  graduate relation counting to the spherical mean bound still had an avoidable
  packaging layer.
- Challenge After:
  `AppendixB.gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting`
  at `PptFactorization/AppendixBPipelineGraduate.lean:36` is the direct
  graduate-counting bridge.  It takes the concrete graduate relation-counting,
  integrability, scalar envelope/model comparison, diagonal, and
  radial/spherical inputs, then returns the off-diagonal, full gamma,
  quadratic lift, and spherical expectation bounds supplied by the existing
  pipeline.  This narrows an adapter route only; the remaining theorem-strength
  upper leaves are the graduate counting/profile estimates, Gaussian
  integrability, scalar envelope comparison, diagonal expectation, and the
  hard growing-moment/concentration inputs.
- Verification:
  `lake build PptFactorization.AppendixBPipelineGraduate` and
  `lake build PptFactorization` pass; the public declaration audits to
  `[propext, Classical.choice, Quot.sound]`.

- Challenge Before:
  The deviation-form fixed-moment upper bulk adapter was stated only as a
  convergence result.  It did not expose the finite-rate monotonicity step that
  a concrete concentration inequality would naturally supply first.
- Challenge After:
  `AubrunAlternative.exists_bad_event_measure_le_of_centered_moment_deviation_event_measure_le_dependent`
  at `PptFactorization/AubrunAlternative.lean:516` is the finite-rate
  deviation adapter.  Any dimensionwise probability bound for
  `η / 2 < |moment_average - catalan/λ^m|` now transfers directly to the bad
  event controlling both negative count and negative trace mass.  The tendsto
  companion at `PptFactorization/AubrunAlternative.lean:572` reuses this
  finite-rate theorem.
- Verification:
  `lake build PptFactorization.AubrunAlternative` passes; both public
  declarations audit to `[propext, Classical.choice, Quot.sound]`.

- Challenge Before:
  The dependent-index fixed-moment upper bulk endpoint consumed a
  centered-moment threshold-event probability bound.  That was correct, but one
  step away from the common concentration statement: convergence in probability
  of the normalized centered moment to the Catalan limit.
- Challenge After:
  `AubrunAlternative.exists_tendsto_bad_event_measure_zero_of_centered_moment_deviation_event_tendsto_zero_dependent`
  at `PptFactorization/AubrunAlternative.lean:572` is the deviation-form
  adapter.  It chooses a fixed moment order from `λ > 4`; if
  `moment_average` converges in probability to
  `(catalan (m + 1) : ℝ) / λ^(m + 1)` at tolerance `η / 2`, then the
  probability of excessive negative count or excessive negative trace mass
  tends to zero.  This is still Level 1 fixed-moment/bulk almost-positivity,
  not full PPT.
- Verification:
  `lake build PptFactorization.AubrunAlternative` passes; the public
  declaration audits to `[propext, Classical.choice, Quot.sound]`.

- Challenge Before:
  The fixed-moment upper bulk route had deterministic adapters for both the
  negative eigenvalue fraction and the normalized negative trace mass, and a
  fixed-index measure wrapper.  It did not yet have the concrete-model shape in
  which the spectral index type varies with dimension.
- Challenge After:
  `AubrunAlternative.exists_bad_event_measure_le_of_centered_moment_threshold_event_measure_le_dependent`
  at `PptFactorization/AubrunAlternative.lean:372` transfers a dimensionwise
  centered-moment threshold-event bound to the combined bad event over
  `ι d`.  The asymptotic companion
  `AubrunAlternative.exists_tendsto_bad_event_measure_zero_of_centered_moment_threshold_event_tendsto_zero_dependent`
  at `PptFactorization/AubrunAlternative.lean:456` says that if the threshold
  event probability tends to zero, then the probability of excessive negative
  count or negative trace mass also tends to zero.  This is the Level 1
  fixed-moment/bulk endpoint: it proves almost-positivity from a fixed-order
  concentration input, not full PPT and not Aubrun's growing-moment theorem.
- Verification:
  `lake build PptFactorization.AubrunAlternative` passes; both public
  declarations audit to `[propext, Classical.choice, Quot.sound]`.

- Challenge Before:
  The lower exponential background-concentration branch had a direct
  mixed-frontier endpoint.  The word-bounds/budget split was available on the
  variance-stack branch, so a caller with pointwise mixed-word estimates, a
  finite budget, and scalar smallness still needed to package the frontier by
  hand before using the stronger exponential-tail route.
- Challenge After:
  `AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withMixedWordBoundsAndBudget_exponentialDeviationStack`
  at
  `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:3739`
  is the word-bounds/budget adapter for the exponential branch.  It supplies
  `lowerConcreteMixedErrorFrontier` from the pointwise word estimates, finite
  budget, and scalar smallness, then calls the exponential-tail endpoint
  directly.  The live theorem-strength inputs remain survivor analysis, the
  exponential deleted-background deviation theorem, and the actual mixed
  word/budget/smallness suppliers.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices`
  passes; the public declaration audits to `[propext, Classical.choice,
  Quot.sound]`.

- Challenge Before:
  The exponential branch had the direct scalar split into one-`Q` and many-`Q`
  mixed trace bounds, but only the variance-stack branch reduced the one-`Q`
  direct scalar theorem to the exact scale comparison.
- Challenge After:
  `AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withPTOneQScaleComparisonAndManyQDirect_splitMixedWordBudget_exponentialDeviationStack`
  at `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:2805`
  is the exponential-tail one-`Q` scale-comparison adapter.  It replaces the
  visible one-`Q` direct scalar bound by
  `lowerConcretePTMixedWordOneQScaleComparison R k ε M`; survivor analysis, the
  exponential background tail, nonnegative `M`, and the many-`Q` direct scalar
  bound remain visible.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices`
  passes; `lake env lean /tmp/check_lower_oneq_scale_exp.lean` checks the
  signature; axiom audit reports `[propext, Classical.choice, Quot.sound]`.

- Challenge Before:
  The exponential one-`Q` scale-comparison endpoint still exposed the many-`Q`
  direct scalar mixed trace bound.  The variance-stack branch already had a
  both-scale-comparisons endpoint, but the stronger exponential route did not.
- Challenge After:
  `AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withPTScaleComparisons_splitMixedWordBudget_exponentialDeviationStack`
  at `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:2840`
  is the exponential-tail both-scale-comparisons adapter.  It supplies the
  many-`Q` direct scalar bound from
  `lowerConcretePTMixedWordManyQScaleComparison R k ε M` and leaves survivor
  analysis, the exponential background tail, nonnegative `M`, and the two
  scale comparisons visible.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices`
  passes; `lake env lean /tmp/check_lower_scale_exp.lean` checks the
  signature; axiom audit reports `[propext, Classical.choice, Quot.sound]`.

- Challenge Before:
  The lower survivor-core exponential branch consumed the mixed side as a
  pointwise PT mixed-word estimate.  The sharper split into the one-`Q` and
  many-`Q` direct scalar trace bounds existed on the variance-stack branch but
  not on the exponential-tail route.
- Challenge After:
  `AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withPTDirectMixedWordScalarCases_splitMixedWordBudget_exponentialDeviationStack`
  at
  `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:2771`
  is the direct-scalar mixed endpoint for the exponential branch.  It supplies
  the pointwise PT word estimate from
  `lowerConcretePTMixedWordOneQDirectScalarBound R k ε M` and
  `lowerConcretePTMixedWordManyQDirectScalarBound R k ε M`, then calls the
  exponential-tail pointwise endpoint.  The live theorem-strength inputs on
  this route are survivor analysis, the exponential deleted-background
  deviation theorem, and the two direct scalar mixed trace bounds.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices`
  passes; the public declaration audits to `[propext, Classical.choice,
  Quot.sound]`.

- Challenge Before:
  The runtime-native lower mixed route had a closed deterministic envelope, but
  at the preferred no-reference survivor/variance endpoint level the branch was
  still mostly visible through the abstract `lowerConcreteMixedErrorFrontier`
  packet.  The length-three obstruction to runtime smallness existed as a
  diagnostic, but not in the exact packaged predicate used by that endpoint
  family.
- Challenge After:
  `AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withRuntimeMixedError_varianceStack`
  at
  `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:3823`
  is the no-reference survivor/variance endpoint with the mixed side reduced to
  the exact runtime-native smallness predicate
  `lowerConcreteMixedErrorEventuallySmall k ε
  (lowerConcreteMixedRuntimeWordError R k)`.  The deterministic runtime envelope
  and budget are supplied internally.  Its companion
  `AppendixB.lowerConcreteMixedRuntimeWordError_three_not_errorEventuallySmall`
  at
  `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:3465`
  refutes that packaged smallness predicate at `k = 3`, so this runtime-native
  branch is diagnostic and cannot be the unconditional lower proof route.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices`
  passes; both public declarations audit to `[propext, Classical.choice,
  Quot.sound]`.

- Challenge Before:
  The lower fixed-`M` scale-comparison branch still exposed
  `lowerConcretePTMixedWordOneQScaleComparison R k ε M` as a conditional input;
  the runtime-domination route was refuted, but neither this exact one-`Q`
  scale-comparison predicate nor the public conjunction
  `hOneScale ∧ hManyScale` had been ruled out at a concrete length.
- Challenge After:
  `AppendixB.lowerConcretePTMixedWordOneQScaleComparison_three_not_uniform` at
  `PptFactorization/AristotleTargets/LowerMixedLowerConcreteChoices.lean:5936`
  proves that the one-`Q` scale comparison is impossible at `k = 3`.  The proof
  routes the scale comparison through the distinguished `QAA` runtime word and
  reuses the existing fixed-`M` PT-domination obstruction.  The packet-level
  companion
  `AppendixB.lowerConcretePTMixedWordScaleComparisons_three_not_uniform` at
  `PptFactorization/AristotleTargets/LowerMixedLowerConcreteChoices.lean:5987`
  refutes the full fixed-`M` scale-comparison packet consumed by the public
  endpoint.  This is a diagnostic closure: it rules out that branch as an
  unconditional route while leaving the honest mixed-frontier theorem-strength
  leaves visible.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMixedLowerConcreteChoices`
  passes; the public theorems audit to `[propext, Classical.choice,
  Quot.sound]`.

- Challenge Before:
  The direct upper bridge from centered-moment `lintegral → 0` to non-PPT
  probability convergence still took whole-integrand a.e. measurability.
- Challenge After:
  `AubrunAlternative.tendsto_negative_event_measure_zero_of_lintegral_tendsto_zero_dependent_of_coordinate`
  at `PptFactorization/AubrunAlternative.lean:1306` is now the shortest direct
  upper endpoint for a future concrete growing-moment convergence theorem over
  a dimension-dependent spectrum.  It consumes coordinate a.e. measurability
  plus `lintegral → 0`; the hard upper leaf remains the concrete
  growing-moment convergence theorem.
- Verification:
  `lake build PptFactorization.AubrunAlternative` passes; the public endpoint
  audits to `[propext, Classical.choice, Quot.sound]`.

- Challenge Before:
  The active dependent-index upper scalar package required a broad
  a.e. measurability hypothesis for the entire centered even-moment
  `lintegrand`; after the convergence-to-zero coordinate wrapper was added,
  the finite-rate package still used the broad hypothesis.
- Challenge After:
  `AubrunAlternative.centered_even_moment_lintegrand_aemeasurable_of_coordinate`
  at `PptFactorization/AubrunAlternative.lean:480` proves that coordinate
  a.e. measurability of a finite spectrum gives a.e. measurability of the
  `ENNReal.ofReal` centered even-moment integrand.  The active wrapper
  `AubrunAlternative.exists_log_order_constants_and_tendsto_negative_event_measure_zero_of_four_lt_eventually_dependent_of_coordinate`
  at `PptFactorization/AubrunAlternative.lean:1138` now consumes coordinate
  measurability and the same eventual growing-moment bound; the finite-rate
  companion
  `AubrunAlternative.exists_log_order_constants_and_eventually_negative_event_measure_le_of_four_lt_dependent_of_coordinate`
  at `PptFactorization/AubrunAlternative.lean:1225` does the same for the
  eventual finite-rate probability bound.  The hard upper leaf remains the
  concrete growing-moment estimate.
- Verification:
  `lake build PptFactorization.AubrunAlternative` passes; the public
  declarations audit to `[propext, Classical.choice, Quot.sound]`.

- Challenge Before:
  The upper simple polynomial-rate and log-polynomial-rate bridges were still
  fixed-index.
- Challenge After:
  `AubrunAlternative.tendsto_negative_event_measure_zero_of_lintegral_bound_const_mul_rpow_neg_dependent`
  at `PptFactorization/AubrunAlternative.lean:734` and
  `AubrunAlternative.tendsto_negative_event_measure_zero_of_lintegral_bound_log_rpow_mul_rpow_neg_dependent`
  at `PptFactorization/AubrunAlternative.lean:827` are the dependent-index
  polynomial/log-polynomial rate adapters.  They are useful fallback endpoints
  if the concrete growing-moment estimate is proved with a rate
  `C*d^{-β}` or `C*(log d)^α*d^{-β}` rather than the full paper-shape
  log-quadratic rate.  They do not prove the moment estimate.
- Verification:
  `lake build PptFactorization.AubrunAlternative` passes; both public
  endpoints audit to `[propext, Classical.choice, Quot.sound]`.

- Challenge Before:
  The direct upper endpoint
  `AubrunAlternative.tendsto_negative_event_measure_zero_of_lintegral_tendsto_zero`
  consumed convergence to zero of the centered-moment `lintegral`, but only
  for a fixed spectral index type.
- Challenge After:
  `AubrunAlternative.tendsto_negative_event_measure_zero_of_lintegral_tendsto_zero_dependent`
  at `PptFactorization/AubrunAlternative.lean:1277` is the dependent-index
  direct convergence adapter.  It is now the shortest upper bridge for a
  future concrete growing-moment theorem stated as `lintegral → 0` over
  `ι d`.  The live hard leaf remains that growing-moment convergence theorem.
- Verification:
  `lake build PptFactorization.AubrunAlternative` passes; the new public
  endpoint audits to `[propext, Classical.choice, Quot.sound]`.

- Challenge Before:
  The upper controlled growing-moment route had dependent-index probability
  adapters, but its fully scalar `λ > 4` constant-choice wrappers were still
  fixed-index.
- Challenge After:
  `AubrunAlternative.exists_log_order_constants_and_tendsto_negative_event_measure_zero_of_four_lt_eventually_dependent`
  at `PptFactorization/AubrunAlternative.lean:1108` and
  `AubrunAlternative.exists_log_order_constants_and_eventually_negative_event_measure_le_of_four_lt_dependent`
  at `PptFactorization/AubrunAlternative.lean:1192` are the active
  dependent-index scalar packages.  They choose `eps`, `q`, and `c` from
  `λ > 4` and consume the eventual paper-shape growing-moment estimate over
  the concrete index type `ι d`.  The live upper hard leaf is unchanged: prove
  that growing-moment estimate for the actual partial-transpose model.
- Verification:
  `lake build PptFactorization.AubrunAlternative` passes; both public
  endpoints audit to `[propext, Classical.choice, Quot.sound]`.

- Challenge Before:
  The upper controlled growing-moment bridge had fixed-index asymptotic
  wrappers and a dependent-index finite-rate wrapper, but no dependent-index
  asymptotic wrapper for the concrete spectrum type `ι d`.
- Challenge After:
  `AubrunAlternative.tendsto_negative_event_measure_zero_of_eventually_lintegral_bound_log_quadratic_rpow_log_dependent_of_two_lt_mul_log_inv`
  at `PptFactorization/AubrunAlternative.lean:969` is the active
  dependent-index upper adapter for the controlled growing-moment route.  It
  reduces a future concrete paper-shape moment estimate with
  `2 < c * log(q⁻¹)` to convergence to zero of the non-PPT event probability.
  Its lower-level suppliers are
  `AubrunAlternative.tendsto_negative_event_measure_zero_of_eventually_lintegral_bound_ofReal_dependent`
  at `PptFactorization/AubrunAlternative.lean:653` and
  `AubrunAlternative.tendsto_negative_event_measure_zero_of_eventually_lintegral_bound_log_quadratic_rpow_log_dependent`
  at `PptFactorization/AubrunAlternative.lean:913`.  The live upper
  theorem-strength leaf is still the growing-order centered-moment estimate;
  the adapter does not prove Aubrun's spectral-edge/combinatorial input.
- Verification:
  `lake build PptFactorization.AubrunAlternative` passes; all three new public
  adapters audit to `[propext, Classical.choice, Quot.sound]`.

- Challenge Before:
  The literal PT mixed frontier had a pointwise-to-frontier supplier, but the
  direct scalar one-`Q`/many-`Q` route still had to pass through the pointwise
  word estimate explicitly.
- Challenge After:
  `AppendixB.lowerConcreteMixedErrorFrontier_of_PTDirectScalarCases` at
  `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:3319`
  supplies the literal PT mixed frontier directly from
  `lowerConcretePTMixedWordOneQDirectScalarBound R k ε M` and
  `lowerConcretePTMixedWordManyQDirectScalarBound R k ε M`.  On this branch,
  the pointwise word split, PT finite budget, and PT smallness are now
  adapter-supplied.  The live mixed leaves are exactly the two direct scalar
  trace estimates.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices`
  passes; the new public adapter audits to `[propext, Classical.choice,
  Quot.sound]`.

- Challenge Before:
  The preferred mixed-frontier constructor split the lower mixed side into
  pointwise word estimates, a finite budget, and scalar smallness.  For the
  literal PT branch, the budget and smallness facts were proved locally but
  not exposed as a direct supplier of `lowerConcreteMixedErrorFrontier`.
- Challenge After:
  `AppendixB.lowerConcreteMixedErrorFrontier_of_PTPointwiseWordBound` at
  `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:3287`
  supplies the literal PT mixed frontier from the single pointwise word
  estimate
  `lowerConcreteMixedWordPointwiseBoundOnSphere R k ε
  (fun a slack d => lowerPartialTransposeMixedWordBoundD k (a + slack) M d)`.
  The finite PT budget is supplied by
  `lowerConcreteMixedWordBudgetWithPTError_literal`, and the scalar `o(1)`
  input is named as
  `AppendixB.lowerConcreteMixedErrorEventuallySmall_of_lowerPartialTransposeMixedErrorD`
  at
  `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:3272`.
  The live mixed theorem-strength leaf on this PT branch is therefore the
  pointwise PT word estimate itself, not the budget or smallness plumbing.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices`
  passes; both new public adapters audit to `[propext, Classical.choice,
  Quot.sound]`.

- Challenge Before:
  The atlas still treated the fixed-`M` PT scale-comparison branch as the
  preferred no-reference lower route.  That branch is a useful conditional
  diagnostic, but the fixed scalar `M` is not the right unconditional target
  for the dimension-dependent runtime threshold `lowerConcreteM R a slack d`.
- Challenge After:
  `AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withMixedErrorFrontier_varianceStack`
  at
  `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:3620`
  is the preferred no-reference endpoint with survivor-core mean input,
  polynomial variance/Chebyshev background concentration, and one matched
  `lowerConcreteMixedErrorFrontier R k ε errMix`.  Its live leaves are
  `lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k`,
  `deletedColumnSphericalMoment_variance_le_const_div_d4 R k`, and the mixed
  frontier.  The mixed frontier is adapter-supplied by
  `AppendixB.lowerConcreteMixedErrorFrontier_of_wordBoundsAndBudget` at
  `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:3252`
  from `lowerConcreteMixedWordPointwiseBoundOnSphere R k ε bound`,
  `lowerConcreteMixedWordBudgetWithError R k ε bound errMix`, and
  `lowerConcreteMixedErrorEventuallySmall k ε errMix`.  The fixed-`M` PT
  scale-comparison endpoint remains available as a compatibility/diagnostic
  branch, not as the atlas-preferred route toward unconditionality.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMixedLowerConcreteChoices`
  passes;
  `lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices`
  passes; the mixed-frontier adapter, new many-`Q` adapter, and endpoint
  audits report only `[propext, Classical.choice, Quot.sound]`; the touched
  Lean files contain no active `sorry`, `admit`, `axiom`, or `unsafe`.

- Challenge Before:
  The sample-ratio closed-form fixed-`M` PT mixed lower route still used the
  internal grouped second-moment Wick/Chebyshev tail through the older
  `SecondMomentWickStack` wrapper, while neighboring pointwise and
  mixed-frontier routes already accepted the paper-facing variance theorem.
- Challenge After:
  `AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_ClosedFormSampleRatioAndVarianceStack_withPTMixedError_splitMixedWordBudget`
  at
  `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:4258`
  is the sample-ratio closed-form packaged fixed-`M` PT mixed endpoint.  Its
  live leaves are
  `lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit_fromSampleRatio R.sample k`,
  `deletedColumnSphericalMoment_variance_le_const_div_d4 R k`, and
  `mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M`.  The pointwise PT branch is
  still the sharper branch when the actual sphere-supported word estimate is
  available.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices`
  passes; the new audit reports only `[propext, Classical.choice,
  Quot.sound]`; the touched Lean file contains no active `sorry`, `admit`,
  `axiom`, or `unsafe`.

- Challenge Before:
  The sample-ratio closed-form lower route exposed the pointwise PT endpoint,
  but its more primitive `lowerConcreteMixedErrorFrontier` endpoint was only
  available in the ratio convention.
- Challenge After:
  `AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_ClosedFormSampleRatioAndVarianceStack_withMixedErrorFrontier_splitMixedWordBudget`
  at
  `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:4102`
  is the sample-ratio closed-form mixed-frontier endpoint.  Its live leaves are
  `lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit_fromSampleRatio
  R.sample k`, `deletedColumnSphericalMoment_variance_le_const_div_d4 R k`,
  and the chosen `lowerConcreteMixedErrorFrontier R k ε errMix`.  The pointwise
  PT and runtime-diagnostic branches remain downstream choices, not hidden
  assumptions.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices`
  passes; the new audit reports only `[propext, Classical.choice,
  Quot.sound]`; the touched Lean file contains no active `sorry`, `admit`,
  `axiom`, or `unsafe`.

- Challenge Before:
  The sample-ratio closed-form mixed-frontier lower route consumed the
  paper-facing variance predicate even when the stronger exponential
  background tail was the available supplier.
- Challenge After:
  `AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_ClosedFormSampleRatioAndExponentialDeviationStack_withMixedErrorFrontier_splitMixedWordBudget`
  at
  `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:4138`
  is the sample-ratio closed-form exponential-background mixed-frontier
  endpoint.  It supplies the variance/Chebyshev predicate internally from
  `deletedColumnSphericalMoment_variance_le_const_div_d4_of_exponentialDeviationTailBound`.
  Its live leaves are now the closed-form sample-ratio mean theorem, the
  exponential background concentration theorem, and the chosen honest mixed
  frontier for the same `errMix`.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices`
  passes; `lake env lean /tmp/check_lower_closedform_exp_mixed_frontier.lean`
  checks the public theorem; the axiom audit reports only
  `[propext, Classical.choice, Quot.sound]`; the touched Lean file contains no
  active `sorry`, `admit`, `axiom`, or `unsafe`.

- Challenge Before:
  The sample-ratio closed-form exponential-background lower route consumed an
  abstract `lowerConcreteMixedErrorFrontier R k ε errMix`, even when the
  available mixed input was the packaged fixed-`M` PT theorem
  `mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M`.
- Challenge After:
  `AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_ClosedFormSampleRatioAndExponentialDeviationStack_withPTMixedError_splitMixedWordBudget`
  at
  `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:4173`
  is the sample-ratio closed-form exponential-background packaged fixed-`M` PT
  endpoint.  It supplies the mixed frontier internally via
  `AppendixB.lowerConcreteMixedErrorFrontier_of_mixed_noL_atLeastTwoQ_ge_neg_errMix`.
  Its live leaves are now the closed-form sample-ratio mean theorem, the
  exponential background concentration theorem, and the packaged fixed-`M` PT
  mixed supplier.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices`
  passes; `lake env lean /tmp/check_lower_closedform_exp_ptmixed.lean` checks
  the public theorem; the axiom audit reports only
  `[propext, Classical.choice, Quot.sound]`; the touched Lean file contains no
  active `sorry`, `admit`, `axiom`, or `unsafe`.

- Challenge Before:
  The sample-ratio closed-form exponential-background lower route consumed an
  abstract `lowerConcreteMixedErrorFrontier R k ε errMix`, even though the
  available mixed input may be the pointwise word estimate against the
  literal PT envelope.
- Challenge After:
  `AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_ClosedFormSampleRatioAndExponentialDeviationStack_withPTPointwiseMixedWordBound_splitMixedWordBudget`
  at
  `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:4207`
  is the sample-ratio closed-form exponential-background pointwise PT endpoint.
  It supplies the mixed frontier internally via
  `AppendixB.lowerConcreteMixedErrorFrontier_of_PTPointwiseWordBound`.  Its
  live leaves are now the closed-form sample-ratio mean theorem, the
  exponential background concentration theorem, and the pointwise PT mixed-word
  estimate.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices`
  passes; `lake env lean /tmp/check_lower_closedform_exp_ptpointwise.lean`
  checks the public theorem; the axiom audit reports only
  `[propext, Classical.choice, Quot.sound]`; the touched Lean file contains no
  active `sorry`, `admit`, `axiom`, or `unsafe`.

- Challenge Before:
  The sample-ratio closed-form pointwise lower route still used the internal
  `lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound`
  input for background concentration.
- Challenge After:
  `AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_ClosedFormSampleRatioAndVarianceStack_withPTPointwiseMixedWordBound_splitMixedWordBudget`
  at
  `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:4324`
  is the sample-ratio closed-form pointwise endpoint with paper-facing
  concentration.  Its live leaves are
  `lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit_fromSampleRatio R.sample k`,
  `deletedColumnSphericalMoment_variance_le_const_div_d4 R k`, and the
  pointwise PT mixed-word estimate.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices`
  passes; the new audit reports only `[propext, Classical.choice,
  Quot.sound]`; the touched Lean file contains no active `sorry`, `admit`,
  `axiom`, or `unsafe`.

- Challenge Before:
  The closed-form lower route had a direct
  `ClosedFormMomentLimitAndVarianceStack` endpoint only through the abstract
  mixed-frontier packet, while the pointwise PT mixed-word route was available
  through a separate sample-ratio wrapper.
- Challenge After:
  `AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_ClosedFormMomentLimitAndVarianceStack_withPTPointwiseMixedWordBound_splitMixedWordBudget`
  at
  `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:4170`
  is the direct source-explicit closed-form pointwise endpoint.  Its live
  leaves are
  `lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit_fromRatio R.sample k`,
  `deletedColumnSphericalMoment_variance_le_const_div_d4 R k`, and the
  pointwise PT mixed-word estimate.  The abstract mixed-frontier packet is
  adapter-supplied from pointwise words on this branch.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices`
  passes; the new audit reports only `[propext, Classical.choice,
  Quot.sound]`; the touched Lean file contains no active `sorry`, `admit`,
  `axiom`, or `unsafe`.

- Challenge Before:
  The runtime scalar-domination lower route still consumed the mean side as the
  broad `deletedColumnSphericalMean_tendsto_ptCatalan` hypothesis.
- Challenge After:
  `AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_CatalanErrorBoundAndVarianceStack_withPTRuntimeMixedScalarDomination_splitMixedWordBudget`
  at
  `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:3654`
  is the source-explicit diagnostic scalar endpoint.  Its live leaves are
  `lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample k`,
  `deletedColumnSphericalMoment_variance_le_const_div_d4 R k`, the one-`Q`
  scalar comparison, and the many-`Q` scalar comparison.  The broad Catalan
  mean convergence theorem is now adapter-supplied from the `D / d`
  Catalan-error estimate on this branch.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices`
  passes; the new audit reports only `[propext, Classical.choice,
  Quot.sound]`; the touched Lean file contains no active `sorry`, `admit`,
  `axiom`, or `unsafe`.

- Challenge Before:
  The Catalan-error lower route still consumed the mixed side through
  `lowerConcreteMixedErrorFrontier`, while pointwise PT mixed words appeared
  only on broader or more specialized wrappers.
- Challenge After:
  `AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_CatalanErrorBoundAndVarianceStack_withPTPointwiseMixedWordBound_splitMixedWordBudget`
  at
  `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:3019`
  is the middle source-explicit pointwise lower endpoint.  Its live leaves are
  `lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample k`,
  `deletedColumnSphericalMoment_variance_le_const_div_d4 R k`, and the
  pointwise PT mixed-word estimate.  The abstract mixed-frontier packet is now
  adapter-supplied from the pointwise word bound plus the scalar PT budget.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices`
  passes; the new audit reports only `[propext, Classical.choice,
  Quot.sound]`; the touched Lean file contains no active `sorry`, `admit`,
  `axiom`, or `unsafe`.

- Challenge Before:
  The sharp lower survivor route still displayed the internal grouped
  second-moment/Chebyshev tail
  `lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k`
  after the broad Gaussian/radial formula predicate had been supplied.
- Challenge After:
  `AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withPTPointwiseMixedWordBound_splitMixedWordBudget_varianceStack`
  at
  `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:2602`
  is the sharp survivor-style pointwise lower endpoint.  Its live leaves are
  geodesic/noncrossing survivor analysis, the paper-facing
  `deletedColumnSphericalMoment_variance_le_const_div_d4` theorem, and
  pointwise PT mixed words.  The grouped second-moment tail is adapter-supplied
  from the variance predicate, not a separate active leaf on this route.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices`
  passes; the new audit reports only `[propext, Classical.choice,
  Quot.sound]`; the touched Lean file contains no active `sorry`, `admit`,
  `axiom`, or `unsafe`.

- Challenge Before:
  The sharp lower PT Wick-core pointwise route still listed
  `lowerDeletedColumnPTGaussianRadialFormula_fromRatio R.sample k` as a visible
  input, although the current broad predicate has the audited supplier
  `AppendixB.lowerDeletedColumnPTGaussianRadialFormula_fromRatio_currentPredicate`.
- Challenge After:
  `AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withPTPointwiseMixedWordBound_splitMixedWordBudget_secondMomentWickMomentTail`
  at
  `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:2569`
  is now the sharp central pointwise lower endpoint.  Its live theorem-strength
  leaves are geodesic/noncrossing survivor analysis, grouped second-moment
  Wick/Chebyshev tail, and pointwise PT mixed words.  The Gaussian/radial
  formula predicate is closed for this route by the current identity-carrier
  witness and should be treated as adapter-supplied, not as active theorem
  debt.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices`
  passes; the new audit reports only `[propext, Classical.choice,
  Quot.sound]`; the touched Lean file contains no active `sorry`, `admit`,
  `axiom`, or `unsafe`.

- Challenge Before:
  The pointwise-PT lower core endpoint exposed the broad ratio-parametric
  Catalan mean core, but the already-isolated Wick components
  `lowerDeletedColumnPTGaussianRadialFormula_fromRatio` and
  `lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio` were not visible on
  that pointwise mixed-word route.
- Challenge After:
  `AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTWickCoreFrontierInputs_withPTPointwiseMixedWordBound_splitMixedWordBudget_secondMomentWickMomentTail`
  at
  `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:2343`
  exposes the PT Wick mean inputs directly together with the grouped
  second-moment tail and the pointwise PT mixed-word estimate.  The active
  lower branch is now split into four theorem-strength leaves: Gaussian/radial
  formula, geodesic/survivor analysis, second-moment Wick/Chebyshev tail, and
  pointwise PT mixed words.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices`
  passes; the new audit reports only `[propext, Classical.choice, Quot.sound]`;
  the touched Lean file contains no active `sorry`, `admit`, `axiom`, or
  `unsafe`.

- Challenge Before:
  The central no-reference closed-trace/core lower endpoint with grouped
  second-moment tail still consumed the packed PT mixed supplier
  `mixed_noL_atLeastTwoQ_ge_neg_errMix`.
- Challenge After:
  `AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCoreFrontierInputs_withPTPointwiseMixedWordBound_splitMixedWordBudget_secondMomentWickMomentTail`
  at
  `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:2309`
  exposes the actual mixed leaf directly as a sphere-supported pointwise
  estimate against `lowerPartialTransposeMixedWordBoundD`.  The active core
  lower branch is now: Catalan/closed-form mean core, grouped second-moment
  Wick/Chebyshev tail, and pointwise PT mixed-word estimate.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices`
  passes; the new audit reports only `[propext, Classical.choice, Quot.sound]`;
  the touched Lean file contains no active `sorry`, `admit`, `axiom`, or
  `unsafe`.

- Challenge Before:
  The cleaner lower route using the closed-form moment limit and grouped
  second-moment Wick tail still asked for the packed PT mixed supplier
  `mixed_noL_atLeastTwoQ_ge_neg_errMix`, so the actual pointwise mixed-word
  leaf was not visible on that canonical endpoint.
- Challenge After:
  `AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_ClosedFormSampleRatioAndSecondMomentWickStack_withPTPointwiseMixedWordBound_splitMixedWordBudget`
  at
  `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:3102`
  exposes the mixed leaf directly as the sphere-supported pointwise estimate
  against `lowerPartialTransposeMixedWordBoundD`.  The active lower route now
  cleanly separates the closed-form mean input, the grouped second-moment tail,
  and the genuine PT mixed-word estimate.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices`
  passes; the new audit reports only `[propext, Classical.choice, Quot.sound]`;
  the touched Lean file contains no active `sorry`, `admit`, `axiom`, or
  `unsafe`.

- Challenge Before:
  The atlas had a single-word obstruction showing that `QAA` is not eventually
  dominated by any fixed-`M` PT word budget, but the public mixed-only
  domination input used by the runtime-to-PT adapter still appeared as a
  separate possible shortcut.
- Challenge After:
  `AppendixB.lowerConcreteMixedRuntimeWordDominationOnMixed_three_not_uniform`
  at
  `PptFactorization/AristotleTargets/LowerMixedLowerConcreteChoices.lean:5437`
  proves that this public mixed-only domination hypothesis is impossible at
  `k = 3`.  The active lower mixed route must therefore prove the real
  sphere-supported PT pointwise mixed-word estimate; it cannot be closed by
  runtime-envelope domination against a fixed `M`.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMixedLowerConcreteChoices`
  passes; the new audit reports only `[propext, Classical.choice, Quot.sound]`;
  the touched Lean file contains no active `sorry`, `admit`, `axiom`, or
  `unsafe`.

- Challenge Before:
  The repaired explicit-diagram + variance lower route still consumed the
  packed PT mixed supplier `mixed_noL_atLeastTwoQ_ge_neg_errMix`, leaving the
  pointwise mixed-word estimate one layer below the live endpoint.
- Challenge After:
  `AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_ExplicitCatalanDiagramAndVarianceStack_withPTPointwiseMixedWordBound_splitMixedWordBudget`
  at
  `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:2947`
  exposes that pointwise leaf directly.  The active lower mixed obligation on
  this route is now the sphere-supported word estimate against
  `lowerPartialTransposeMixedWordBoundD`; the finite mixed budget adapter is
  closed.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices`
  passes; the new audit reports only `[propext, Classical.choice, Quot.sound]`;
  the touched Lean file contains no active `sorry`, `admit`, `axiom`, or
  `unsafe`.

- Challenge Before:
  The lower atlas had the honest mixed-frontier endpoint and the rejected
  runtime-smallness diagnostic, but the repaired fixed-`M` PT route did not have
  a short endpoint whose visible inputs were exactly the explicit Catalan
  diagram estimate, the paper-facing variance theorem, and the PT mixed
  supplier.
- Challenge After:
  `AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_ExplicitCatalanDiagramAndVarianceStack_withPTMixedError_splitMixedWordBudget`
  at
  `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:2914`
  packages that exact input surface.  It is an adapter: the remaining
  theorem-strength leaves are still the explicit diagram estimate, the
  variance/Chebyshev frontier, and `mixed_noL_atLeastTwoQ_ge_neg_errMix`.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices`
  passes; the new audit reports only `[propext, Classical.choice, Quot.sound]`;
  the touched Lean file contains no active `sorry`, `admit`, `axiom`, or
  `unsafe`.

- Challenge Before:
  The lower atlas had a length-three runtime non-smallness diagnostic for each
  admissible `a, slack`, but it did not yet name the exact obstruction to the
  uniform runtime-smallness hypothesis used by the public runtime endpoint.
- Challenge After:
  `AppendixB.lowerConcreteMixedRuntimeWordError_three_not_uniformEventuallySmall`
  at
  `PptFactorization/AristotleTargets/LowerMixedLowerConcreteChoices.lean:5338`
  proves that the public uniform hypothesis
  `∀ a > spikeRoot 3 ε, ∀ slack > 0, lowerConcreteMixedRuntimeWordError R 3 a slack = o(1)`
  is impossible.  The runtime-smallness lower endpoint is now recorded as a
  conditional diagnostic route.  The active lower mixed frontier remains the
  honest paper-facing PT mixed-error supplier, not the rejected runtime-native
  error.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMixedLowerConcreteChoices`
  and `lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices`
  pass; the new audit reports only `[propext, Classical.choice, Quot.sound]`;
  the touched Lean files contain no active `sorry`, `admit`, `axiom`, or
  `unsafe`.

- Challenge Before:
  The upper fixed-moment bulk path had an audited deterministic bad-event set
  inclusion, but the atlas did not yet name the measure-level adapter needed by
  a probability or concentration supplier.
- Challenge After:
  `AubrunAlternative.exists_bad_event_measure_le_of_centered_moment_threshold_event_measure_le`
  at `PptFactorization/AubrunAlternative.lean:348` packages the monotonicity
  step: after choosing the fixed moment order from `lambda > 4` and `eta > 0`,
  any measure bound for the centered-moment threshold event is inherited by the
  bad event where the normalized negative count or normalized negative mass is
  larger than `eta`.  The active upper fixed-moment branch is therefore cleanly
  separated from the harder growing-moment/Aubrun branch.
- Verification:
  `lake build PptFactorization.AubrunAlternative` passes; the new theorem audit
  reports only `[propext, Classical.choice, Quot.sound]`; the touched Lean file
  contains no active `sorry`, `admit`, `axiom`, or `unsafe`.

- Challenge Before:
  The atlas had a canonical length-three mixed witness `QAA` and a lift from
  one mixed runtime word to the full runtime error, and the previous scalar
  bridge still needed to be converted into an actual non-smallness obstruction.
- Challenge After:
  `AppendixB.lowerConcreteMixedRuntimeWordBound_headQRestA_two_eventually_ge`
  at
  `PptFactorization/AristotleTargets/LowerMixedLowerConcreteChoices.lean:4993`
  proves the eventual scalar lower bound for the distinguished `QAA` word.
  `AppendixB.lower_headQRestA_two_powerFactor_ge_one` at line `5088` and
  `AppendixB.lower_headQRestA_two_scalar_eventually_ge_const` at line `5113`
  show that the displayed scalar lower bound is eventually at least
  `256*256*a`.
  `AppendixB.lowerConcreteMixedRuntimeWordError_three_eventually_ge_headQRestA_scalar`
  at line `5271` lifts it to
  `lowerConcreteMixedRuntimeWordError R 3 a slack d`.
  `AppendixB.lowerConcreteMixedRuntimeWordError_three_not_eventuallySmall` at
  line `5297` proves this runtime-native error is not eventually arbitrarily
  small.  `AppendixB.lowerConcreteMixedRuntimeWordBound_headQRestA_two_not_eventually_le_PT`
  at line `5338` proves the sharper obstruction: even the single `QAA`
  runtime word is not eventually dominated by any fixed-`M` literal PT word
  budget.  The live lower leaf therefore moves to the honest paper-facing
  mixed-error frontier, not to the rejected runtime-native or fixed-`M`
  domination envelope.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMixedLowerConcreteChoices`
  and `lake build PptFactorization` pass; the new audits report only
  `[propext, Classical.choice, Quot.sound]`; the touched Lean file contains no
  active `sorry`, `admit`, `axiom`, or `unsafe`.

- Challenge Before:
  The runtime extraction layer could lift a large mixed word to the full
  runtime error, but the atlas did not name a canonical word or its exact
  envelope formula.
- Challenge After:
  `AppendixB.lowerHeadQRestAWord` at
  `PptFactorization/AristotleTargets/LowerMixedLowerConcreteChoices.lean:4765`
  fixes the head-`Q`, rest-`A` witness.  The count and mixedness facts are
  `AppendixB.lowerHeadQRestAWord_Q_count`,
  `AppendixB.lowerHeadQRestAWord_L_count`, and
  `AppendixB.lowerHeadQRestAWord_mixed` at lines `4769`, `4776`, and `4788`.
  `AppendixB.lowerConcreteMixedRuntimeWordBound_headQRestA_eq` at line `4970`
  gives the exact scalar formula, and
  `AppendixB.lowerConcreteMixedRuntimeWordError_eventually_ge_headQRestA` at
  line `5252` lifts it to the full runtime error.  At that stage, the next
  lower leaf was the scalar growth/lower-bound analysis of this named formula.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMixedLowerConcreteChoices`
  and `lake build PptFactorization` pass; audits report only foundational
  axioms; the touched Lean file contains no active `sorry`, `admit`, `axiom`,
  or `unsafe`.

- Challenge Before:
  The lower runtime-smallness branch had a scale diagnostic for
  `lowerConcreteM / lowerConcreteN`, but no audited extraction theorem saying
  that a single large mixed word forces the finite runtime error to be large.
- Challenge After:
  `AppendixB.localMixedWordFilteredSum_nonneg` and
  `AppendixB.localMixedWordFilteredSum_single_le` at
  `PptFactorization/AristotleTargets/LowerMixedLowerConcreteChoices.lean:4725`
  and `:4739` supply the generic filtered-sum facts.  The runtime adapters
  `AppendixB.lowerConcreteMixedRuntimeWordBound_eventually_nonneg`,
  `AppendixB.lowerConcreteMixedRuntimeWordError_eventually_nonneg`, and
  `AppendixB.lowerConcreteMixedRuntimeWordBound_le_runtimeWordError_eventually`
  at lines `4931`, `4981`, and `5004` specialize them to the exact runtime
  mixed envelope.  The next lower diagnostic can focus on one explicit mixed
  word instead of redoing finite-sum bookkeeping.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMixedLowerConcreteChoices`
  and `lake build PptFactorization` pass; all five new audits report only
  `[propext, Classical.choice, Quot.sound]`; the touched Lean file contains no
  active `sorry`, `admit`, `axiom`, or `unsafe`.

- Challenge Before:
  The lower runtime mixed diagnostic showed that
  `lowerConcreteM R a slack d / lowerConcreteN d` is not `o(1)`, but the atlas
  did not yet record the sharper fixed-scale obstruction.
- Challenge After:
  `AppendixB.lower_concrete_sample_eventually_ge` at
  `PptFactorization/AristotleTargets/LowerMixedLowerConcreteChoices.lean:3750`
  proves eventual domination of every fixed natural sample count, and
  `AppendixB.lowerConcreteM_div_lowerConcreteN_eventually_ge_real` at
  `PptFactorization/AristotleTargets/LowerMixedLowerConcreteChoices.lean:3798`
  proves the normalized runtime threshold eventually exceeds every fixed real
  bound.  The lower mixed frontier therefore cannot be completed by pretending
  the current runtime background coefficient is fixed-scale or vanishing.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMixedLowerConcreteChoices`
  passes; both new theorem audits report only
  `[propext, Classical.choice, Quot.sound]`; the touched Lean file contains no
  active `sorry`, `admit`, `axiom`, or `unsafe`.

- Challenge Before:
  The sharp lower concrete frontier lived in
  `PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices`, but the
  project root still imported only the older lower closure aliases.
- Challenge After:
  `PptFactorization.lean` imports
  `PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices`, making the
  current lower frontier and mixed-route diagnostics visible from
  `import PptFactorization`.
- Verification:
  `lake build PptFactorization` passes.

- Challenge Before:
  The runtime-native mixed route still listed
  `lowerConcreteMixedErrorEventuallySmall k ε
  (lowerConcreteMixedRuntimeWordError R k)` as a live target without a formal
  scalar diagnostic explaining why this `o(1)` route is suspect under the
  current favourable background event.
- Challenge After:
  `AppendixB.lowerConcreteM_div_lowerConcreteN_not_eventuallySmall` at
  `PptFactorization/AristotleTargets/LowerMixedLowerConcreteChoices.lean:3752`
  proves that the normalized runtime background threshold
  `lowerConcreteM R a slack d / lowerConcreteN d` is not eventually
  arbitrarily small; in fact the existing supplier gives an eventual lower
  bound by `256`.  The lower mixed frontier is therefore not a routine
  small-coefficient proof: it requires either a sharper background event or a
  different mixed envelope.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMixedLowerConcreteChoices`
  passes; axiom audit for the new theorem reports only
  `[propext, Classical.choice, Quot.sound]`.

- Challenge Before:
  The lower explicit-diagram endpoint still exposed the mixed side as the
  abstract packet `lowerConcreteMixedErrorFrontier R k ε errMix`, so the live
  frontier did not force callers to say whether they were using a fixed-`M`
  PT error or the exact runtime-native mixed error.
- Challenge After:
  `AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_ExplicitCatalanDiagramAndVarianceStack_withPTRuntimeMixedError_splitMixedWordBudget`
  at `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:4030`
  consumes the explicit Catalan diagram estimate, the variance frontier, and
  the exact runtime-smallness leaf
  `lowerConcreteMixedErrorEventuallySmall k ε
  (lowerConcreteMixedRuntimeWordError R k)`.  The deterministic runtime
  mixed-word envelope is supplied internally by the audited runtime adapter.
- Verification:
  `lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices`
  passes; axiom audit for the new theorem reports only
  `[propext, Classical.choice, Quot.sound]`; the touched Lean file contains no
  `sorry`, `admit`, `axiom`, or `unsafe`.

2026-06-01:

- Challenge Before:
  The progress board still pointed at the stale lower name
  `lower_eventual_log_over_spikeSpeed_concreteModel_noInputs` and could make
  old Aristotle draft files with `sorry` look like active suppliers.
- Challenge After:
  The active lower route is now recorded as the compiled paper-facing frontier
  in `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean`.
  The fixed-`M` PT branch at line `3259` leaves exactly the PT Catalan mean,
  PT variance, and two scalar runtime mixed-domination inequalities.  The
  honest mixed-frontier branch at line `2821` replaces fixed-`M` domination by
  a vanishing mixed-error envelope tied to the same error sequence.  The active
  upper source-explicit route remains the direct strict Lemma 4.3 plus
  north-pole coordinate-tail endpoint at
  `PptFactorization/AppendixBUpperBoundClosure.lean:13176`.
- Verification:
  `lake build PptFactorization.AppendixBUpperBoundClosure
  PptFactorization.AppendixBLowerBoundClosure` passes, and the audited upper
  and lower closure endpoints depend only on
  `[propext, Classical.choice, Quot.sound]`.

2026-06-02 20:20 CEST:

- Challenge Before:
  The canonical fixed-base finite-rate endpoint accepted arbitrary `q,c`.
  The `λ > 4` constant choices existed for the asymptotic PPT endpoint, but
  not for the dimensionwise non-PPT probability endpoint.
- Challenge After:
  `AubrunAlternative.exists_log_order_constants_and_eventually_not_rhoGamma_posSemidef_measure_le_of_canonicalGaussian_natSample_wishartGamma_frobeniusMass_eventually_log_bound_of_ratio_tendsto`
  at `PptFactorization/AubrunAlternativeModelBridge.lean:1502` is the
  finite-rate fixed-base `λ > 4` constant-choice endpoint: Lean chooses
  `eps,q,c`, then transfers the chosen fixed-base trace-moment estimate to the
  same eventual concrete non-PPT probability bound.  The live theorem-strength
  frontier remains the trace-moment estimate itself.

2026-06-02 20:05 CEST:

- Challenge Before:
  The canonical Gaussian fixed-base paper envelope had an asymptotic PPT
  endpoint, but no dimensionwise non-PPT probability endpoint with the same
  rate.  Thus a hard estimate of the form
  `C (log d)^α d^2 q^(c log d)` still had to pass through a limit argument
  before exposing its finite-rate probability meaning.
- Challenge After:
  `AubrunAlternative.eventually_not_rhoGamma_posSemidef_measure_le_of_canonicalGaussian_natSample_wishartGamma_frobeniusMass_eventually_log_bound_of_ratio_tendsto_pos`
  at `PptFactorization/AubrunAlternativeModelBridge.lean:1441` is the
  fixed-base canonical finite-rate endpoint: the displayed trace-moment
  envelope gives the same eventual bound on the concrete non-PPT event.  The
  remaining theorem-strength frontier is the actual growing trace-moment
  estimate.

2026-06-02 19:35 CEST:

- Challenge Before:
  The finite-rate canonical Gaussian non-PPT endpoint accepted arbitrary
  `eta,c`, while the `λ > 4` constant-choice wrapper existed only for the
  asymptotic PPT endpoint.  Callers of the finite-rate theorem still had to
  select the ratio slack and logarithmic order constant manually.
- Challenge After:
  `AubrunAlternative.exists_ratioDependent_log_order_constants_and_eventually_not_rhoGamma_posSemidef_measure_le_of_canonicalGaussian_natSample_wishartGamma_frobeniusMass_ratioDependent_log_bound_of_ratio_tendsto`
  at `PptFactorization/AubrunAlternativeModelBridge.lean:1806` is the
  finite-rate `λ > 4` constant-choice endpoint: Lean chooses `eta,c`, then
  transfers the chosen ratio-dependent trace-moment estimate to the same
  eventual concrete non-PPT probability bound.  The live theorem-strength
  frontier remains the trace-moment estimate itself.

2026-06-02 19:15 CEST:

- Challenge Before:
  The canonical Gaussian ratio-dependent route had an asymptotic endpoint
  converting the natural envelope into PPT probability tending to one, but not
  the sharper finite-rate non-PPT statement.  Thus the dimensionwise meaning of
  a concrete growing-moment bound was still one adapter away from the canonical
  model.
- Challenge After:
  `AubrunAlternative.eventually_not_rhoGamma_posSemidef_measure_le_of_canonicalGaussian_natSample_wishartGamma_frobeniusMass_ratioDependent_log_bound_of_ratio_tendsto_pos`
  at `PptFactorization/AubrunAlternativeModelBridge.lean:1705` is the canonical
  finite-rate endpoint: the natural ratio-dependent trace-moment envelope
  `((4 + eta) / (s_d / d^2))^(c log d)` gives the same eventual bound on the
  concrete non-PPT event.  The remaining theorem-strength frontier is precisely
  to prove that ratio-dependent Frobenius-mass-scaled growing trace-moment
  estimate.

2026-06-02 18:50 CEST:

- Challenge Before:
  The upper bridge had the fixed-space finite-rate Wishart/radial adapter and
  the varying-space asymptotic endpoint, but not the exact finite-rate type
  shape used by canonical Gaussian coordinate spaces.  A future supplier over
  `Ω d` in the native Frobenius-mass-scaled Wishart normalization still had to
  be hand-rewritten before it could bound the non-PPT event.
- Challenge After:
  `AubrunAlternative.eventually_not_rhoGamma_posSemidef_measure_le_of_eventually_varying_wishartGamma_frobeniusMass_traceMoment_bound_ofReal`
  at `PptFactorization/AubrunAlternativeModelBridge.lean:760` is the new
  varying-space finite-rate adapter: an eventual real-rate bound for
  `Re Tr((((d^2 #σ_d / frobeniusMass G_d) W_d^Γ)-I)^(2m_d))` over `Ω d`
  yields the same eventual bound on
  `μ_d {ω | ¬ PosSemidef (rhoGamma (G_d ω))}`.  The theorem-strength frontier
  remains the actual growing trace-moment estimate.

2026-05-28 17:37 CEST:

- Challenge Before:
  The canonical Gaussian ratio-dependent endpoint consumed the natural hard
  envelope
  `((4 + eta) / (s_d / d^2))^(c log d)`, but the caller still had to choose
  the ratio slack `eta` and logarithmic order constant `c` by hand.
- Challenge After:
  `AubrunAlternative.exists_ratioDependent_log_order_constants_of_four_lt`
  at `PptFactorization/AubrunAlternativeModelBridge.lean:1772` chooses
  `eta,c` from `λ > 4` for the midpoint fixed-base comparison, and
  `AubrunAlternative.exists_ratioDependent_log_order_constants_and_tendsto_rhoGamma_posSemidef_measureReal_one_of_canonicalGaussian_natSample_wishartGamma_frobeniusMass_ratioDependent_log_bound_of_ratio_tendsto`
  at `PptFactorization/AubrunAlternativeModelBridge.lean:1858` packages the
  natural ratio-dependent hard input into the concrete PPT probability
  conclusion.  This closes a constant-choice adapter only; the live hard
  kernel remains the ratio-dependent Frobenius-mass growing trace-moment
  estimate itself.

2026-05-27 11:42 CEST:

- Challenge Before:
  The natural sample-count endpoint expected a fixed paper constant
  `q < 1` in the envelope `q^(c log d)`.  A growing-moment supplier is more
  likely to produce the ratio-dependent base
  `(4 + eta) / (s_d / d^2)`, because the finite-dimensional sample ratio is
  still present in the Wick estimate.
- Challenge After:
  `AubrunAlternative.eventually_ratioDependent_log_envelope_le_fixed_of_tendsto_ratio`
  at `PptFactorization/AubrunAlternativeModelBridge.lean:1595` proves that,
  from `s_d / d^2 → λ` and `4 + eta < λ`, the ratio-dependent envelope is
  eventually bounded by the fixed base
  `(4 + eta) / ((λ + (4 + eta)) / 2)`.  The endpoint
  `AubrunAlternative.tendsto_rhoGamma_posSemidef_measureReal_one_of_canonicalGaussian_natSample_wishartGamma_frobeniusMass_ratioDependent_log_bound_of_ratio_tendsto_pos`
  at `PptFactorization/AubrunAlternativeModelBridge.lean:1648` consumes that
  ratio-dependent hard input directly.  This is still adapter work; the live
  hard kernel is the ratio-dependent Frobenius-mass growing-moment estimate.

2026-05-27 11:21 CEST:

- Challenge Before:
  The canonical paper-shape endpoint wrote the sample count as
  `Fintype.card (Fin (s d))`, which is definitionally equal to `s d` but noisy
  for a future paper-facing random-matrix supplier.
- Challenge After:
  `AubrunAlternative.tendsto_rhoGamma_posSemidef_measureReal_one_of_canonicalGaussian_natSample_wishartGamma_frobeniusMass_eventually_log_bound_of_ratio_tendsto_pos`
  at `PptFactorization/AubrunAlternativeModelBridge.lean:1301` accepts the
  eventual Frobenius-mass trace-moment envelope with the ordinary sample count
  `(s d : ℝ)`.  The `λ > 4` wrapper
  `AubrunAlternative.exists_log_order_constants_and_tendsto_rhoGamma_posSemidef_measureReal_one_of_canonicalGaussian_natSample_wishartGamma_frobeniusMass_eventually_log_bound_of_ratio_tendsto`
  at `PptFactorization/AubrunAlternativeModelBridge.lean:1343` chooses the
  constants and leaves exactly that natural sample-count envelope as the hard
  input.

2026-05-27 11:02 CEST:

- Challenge Before:
  The canonical Gaussian route accepted a `Tendsto ... 0` moment-convergence
  input.  A future paper-style supplier proving the usual eventual envelope
  `C (log d)^α d^2 q^(c log d)` would still have had to perform the scalar
  convergence-to-zero step separately.
- Challenge After:
  `AubrunAlternative.tendsto_rhoGamma_posSemidef_measureReal_one_of_canonicalGaussian_finSample_wishartGamma_frobeniusMass_eventually_log_bound_of_ratio_tendsto_pos`
  at `PptFactorization/AubrunAlternativeModelBridge.lean:1181` turns an
  eventual paper-shape Frobenius-mass trace-moment bound with
  `2 < c * log q⁻¹` directly into PPT probability tending to one.  The wrapper
  `AubrunAlternative.exists_log_order_constants_and_tendsto_rhoGamma_posSemidef_measureReal_one_of_canonicalGaussian_finSample_wishartGamma_frobeniusMass_eventually_log_bound_of_ratio_tendsto`
  at `PptFactorization/AubrunAlternativeModelBridge.lean:1255` chooses the
  `λ > 4` constants.  The live hard supplier is now exactly the eventual
  canonical Gaussian Frobenius-mass growing-moment envelope.

2026-05-27 10:41 CEST:

- Challenge Before:
  The canonical Gaussian finite-sample endpoint still exposed the routine
  nonemptiness hypothesis `∀ᶠ d, 0 < s_d` separately from the natural threshold
  scaling assumption `s_d / d^2 → λ`.
- Challenge After:
  `AubrunAlternative.eventually_pos_of_tendsto_natCast_div_sq_pos` at
  `PptFactorization/AubrunAlternativeModelBridge.lean:1065` proves eventual
  nonemptiness from `0 < λ` and
  `(fun d => (s d : ℝ) / (d : ℝ)^2) → λ`.  The wrapper
  `AubrunAlternative.tendsto_rhoGamma_posSemidef_measureReal_one_of_canonicalGaussian_finSample_wishartGamma_frobeniusMass_traceMoment_tendsto_zero_of_ratio_tendsto_pos`
  at `PptFactorization/AubrunAlternativeModelBridge.lean:1239` consumes that
  scalar adapter.  The canonical route now leaves the usual ratio limit plus
  the actual Frobenius-mass-scaled growing trace-moment convergence as its
  visible inputs.

2026-05-27 10:05 CEST:

- Challenge Before:
  The varying probability-space endpoint matched the shape of the canonical
  Gaussian model, but it still exposed the probability laws, sample maps,
  measurability, and sample-index family abstractly.
- Challenge After:
  `AubrunAlternative.tendsto_rhoGamma_posSemidef_measureReal_one_of_canonicalGaussian_finSample_wishartGamma_frobeniusMass_traceMoment_tendsto_zero`
  at `PptFactorization/AubrunAlternativeModelBridge.lean:1184` specializes the
  endpoint to the concrete Gaussian model on
  `Fin d × Fin d` with sample index `Fin (s_d)`.  Probability-law and
  sample-map measurability inputs are discharged by the existing Gaussian
  model suppliers.  The remaining visible inputs are eventual positivity of
  `s_d` and the actual Frobenius-mass-scaled Wishart growing trace-moment
  convergence.

2026-05-27 09:44 CEST:

- Challenge Before:
  The direct source-explicit Wishart/radial trace-limit endpoint used one fixed
  probability space `Ω` for all dimensions.  The canonical Gaussian coordinate
  model in the repository has dimension-dependent sample spaces, so a future
  supplier for the actual Gaussian model would still need a type-level
  transport wrapper.
- Challenge After:
  `AubrunAlternative.tendsto_rhoGamma_posSemidef_measureReal_one_of_varying_wishartGamma_frobeniusMass_traceMoment_tendsto_zero`
  at `PptFactorization/AubrunAlternativeModelBridge.lean:1020` is the varying
  probability-space endpoint: for a family `Ω_d`, convergence to zero of the
  Frobenius-mass-scaled Wishart centered trace moment implies real PPT
  probability tending to one.  The live hard frontier remains the same
  moment-convergence supplier, now in the type shape used by the concrete
  Gaussian model.

2026-05-27 09:24 CEST:

- Challenge Before:
  The source-explicit Wishart/radial endpoint accepted an eventual real-rate
  bound by a chosen sequence `δ_d` together with `δ_d → 0`.  This is useful
  for finite-rate bookkeeping, but a hard growing-moment supplier may more
  naturally prove directly that the displayed `lintegral` tends to zero.
- Challenge After:
  `AubrunAlternative.tendsto_rhoGamma_posSemidef_measureReal_one_of_wishartGamma_frobeniusMass_traceMoment_tendsto_zero`
  at `PptFactorization/AubrunAlternativeModelBridge.lean:984` is the direct
  source-explicit asymptotic endpoint: if the Frobenius-mass-scaled Wishart
  centered trace moment tends to zero, then the real PPT probability tends to
  one.  The visible theorem-strength frontier is now a single moment-limit
  supplier, plus the routine eventual nonemptiness of the sample index.

2026-05-27 08:53 CEST:

- Challenge Before:
  The article-facing real-rate PPT endpoint accepted a trace-moment supplier
  for `d^2ρ^Γ-I`, and the model file had the pointwise algebra rewriting that
  trace as a Frobenius-mass-scaled Wishart trace.  A future random-matrix
  supplier still had to compose those two facts manually at the `lintegral`
  endpoint.
- Challenge After:
  `PptFactorization.RandomMatrixModel.rhoGamma_centered_trace_ofReal_eq_wishartGamma_frobeniusMass`
  at `PptFactorization/RandomMatrixModel.lean:128` gives the lifted
  `ENNReal.ofReal` trace rewrite, and
  `AubrunAlternative.tendsto_rhoGamma_posSemidef_measureReal_one_of_eventually_wishartGamma_frobeniusMass_traceMoment_bound_ofReal`
  at `PptFactorization/AubrunAlternativeModelBridge.lean:716` is the
  source-explicit endpoint: an eventual real-rate bound for
  `Re Tr((((d^2 #σ_d / frobeniusMass G_d) W_d^Γ)-I)^(2m_d))`, plus
  `δ_d → 0`, gives real PPT probability tending to one.  The live frontier is
  now exactly the growing Wishart/Frobenius trace-moment estimate and radial
  concentration, not endpoint plumbing.

2026-05-27 08:32 CEST:

- Challenge Before:
  The model file had the mass-form identity `ρ^Γ = (#σ / frobeniusMass G) •
  W^Γ`, but the endpoint observable is the centered trace power
  `Re Tr((Dρ^Γ-I)^m)`.  Future Wishart-facing suppliers still had to rewrite
  this trace expression manually.
- Challenge After:
  `PptFactorization.RandomMatrixModel.rhoGamma_centered_trace_re_eq_wishartGamma_frobeniusMass`
  at `PptFactorization/RandomMatrixModel.lean:114` rewrites the concrete
  centered trace observable as
  `Re Tr(((D #σ / frobeniusMass G) W^Γ - I)^m)`.  The remaining work is now a
  genuine Wishart growing-moment estimate plus radial concentration, not an
  algebraic trace-normalization bridge.

2026-05-27 08:11 CEST:

- Challenge Before:
  The normalization bridge expressed the scalar between `ρ^Γ` and `W^Γ` as
  `#σ * ‖G‖₂^{-2}`.  The concentration/radial estimates are normally stated
  for the Frobenius mass `‖G‖₂²`, so future suppliers still had a small
  algebraic rewrite to perform.
- Challenge After:
  `PptFactorization.RandomMatrixModel.rhoGamma_eq_card_div_frobeniusMass_smul_wishartGamma`
  at `PptFactorization/RandomMatrixModel.lean:101` proves the mass-form
  identity `ρ^Γ = (#σ / frobeniusMass G) • W^Γ`.  The remaining scaling work
  is now the genuine concentration control for `frobeniusMass G`, not a
  normalization-notation adapter.

2026-05-27 07:53 CEST:

- Challenge Before:
  The `λ > 4` trace route had concrete `ρ^Γ` probability adapters, but the
  deterministic normalization bridge from the normalized induced state
  `ρ = GGᴴ / ‖G‖₂²` to the Wishart normalization `W = GGᴴ / #σ` was still not
  recorded as a public theorem.
- Challenge After:
  `PptFactorization.RandomMatrixModel.rhoGamma_eq_card_mul_inv_frobeniusNorm_sq_smul_wishartGamma`
  at `PptFactorization/RandomMatrixModel.lean:86` proves that, for nonempty
  sample index `σ`, `ρ^Γ` is the scalar
  `#σ * ‖G‖₂^{-2}` times `W^Γ`.  This closes a deterministic normalization
  adapter needed before a hard Wishart partial-transpose moment estimate can
  be transported to the normalized induced-state statement.

2026-05-27 07:37 CEST:

- Challenge Before:
  The real-rate asymptotic trace endpoint closed `μ_d(non-PPT) → 0`, but the
  article-facing statement still required the standard complement/probability
  wrapper to state `P(PPT) → 1` directly from the same real-rate supplier.
- Challenge After:
  `AubrunAlternative.tendsto_rhoGamma_posSemidef_measureReal_one_of_eventually_traceMoment_bound_ofReal`
  at `PptFactorization/AubrunAlternativeModelBridge.lean:657` gives the direct
  paper-facing PPT endpoint: under probability laws and measurable sample maps,
  an eventual trace-moment bound by `ofReal (δ_d)` plus `δ_d → 0` implies
  real PPT probability tending to one.  The remaining theorem-strength input is
  exactly the real-valued growing trace-moment estimate for the concrete
  partial-transpose model.

2026-05-27 07:13 CEST:

- Challenge Before:
  The real-rate finite trace adapter gave eventual bounds
  `μ_d(non-PPT) ≤ ofReal (δ_d)`, but the concrete trace route still lacked the
  direct asymptotic statement that a real rate tending to zero closes the
  non-PPT probability.
- Challenge After:
  `AubrunAlternative.tendsto_not_rhoGamma_posSemidef_measure_zero_of_eventually_traceMoment_bound_ofReal`
  at `PptFactorization/AubrunAlternativeModelBridge.lean:626` gives the
  paper-facing asymptotic endpoint: if eventually the lifted trace moment is
  bounded by `ofReal (δ_d)` and `δ_d → 0` in `ℝ`, then
  `μ_d(non-PPT) → 0`.  The remaining theorem-strength input is now exactly a
  real-valued growing trace-moment estimate with a vanishing rate.

2026-05-27 06:57 CEST:

- Challenge Before:
  The finite-rate trace adapter used an `ENNReal` rate `δ_d`; most paper
  moment estimates are naturally stated with ordinary real scalar rates and
  then lifted by `ENNReal.ofReal`.
- Challenge After:
  `AubrunAlternative.eventually_not_rhoGamma_posSemidef_measure_le_of_eventually_traceMoment_bound_ofReal`
  at `PptFactorization/AubrunAlternativeModelBridge.lean:604` gives the
  paper-facing real-rate version: an eventual trace-moment bound by
  `ofReal (δ_d)` gives `μ_d(non-PPT) ≤ ofReal (δ_d)` eventually.
  The hard theorem remains exactly the real-valued growing trace-moment
  estimate for the partial-transpose model.

2026-05-27 06:26 CEST:

- Challenge Before:
  The direct trace-moment endpoint gave the limit statement, but there was no
  concrete finite-rate wrapper saying that an arbitrary eventual bound `δ_d`
  on the trace moment bounds the non-PPT probability by the same `δ_d`.
- Challenge After:
  `AubrunAlternative.eventually_not_rhoGamma_posSemidef_measure_le_of_eventually_traceMoment_bound`
  at `PptFactorization/AubrunAlternativeModelBridge.lean:546` proves the
  finite-rate adapter at the paper scale `d^2`: if eventually
  `∫⁻ω ofReal(Re Tr((d^2ρ^Γ-I)^(2m_d))) ≤ δ_d`, then eventually
  `μ_d(non-PPT) ≤ δ_d`.  This is still deterministic/probabilistic plumbing;
  the hard theorem is now exactly to supply a useful `δ_d`, especially the
  Aubrun-style logarithmic envelope or a sequence tending to zero.

2026-05-27 06:11 CEST:

- Challenge Before:
  The sharp trace-moment endpoint was quantitative, carrying the paper-shape
  rate envelope `C (log d)^α d^2 q^(c log d)`.  There was no concrete
  model-facing theorem stating the cleaner controlled-moment principle:
  if the unnormalised centered trace moment itself tends to zero, then PPT
  probability tends to one.
- Challenge After:
  `AubrunAlternative.tendsto_not_rhoGamma_posSemidef_measure_zero_of_traceMoment_tendsto_zero`
  at `PptFactorization/AubrunAlternativeModelBridge.lean:857` proves the
  direct concrete non-PPT conclusion from
  `∫⁻ ω, ofReal (Re Tr((d^2ρ^Γ(G_d(ω))-I)^(2m_d))) → 0`.
  `AubrunAlternative.tendsto_rhoGamma_posSemidef_measureReal_one_of_traceMoment_tendsto_zero`
  at `PptFactorization/AubrunAlternativeModelBridge.lean:925` packages the
  complement form: under probability laws and measurable sample maps, the real
  PPT probability tends to one.  This does not prove Aubrun's finite-rate
  estimate; it isolates exactly the controlled growing-moment input needed for
  asymptotic PPT.

2026-05-27 05:56 CEST:

- Challenge Before:
  The trace-moment endpoint accepted the hard bound in the right matrix form,
  but it still carried an a.e. measurability hypothesis for the
  eigenvalue-coordinate centered sum.
- Challenge After:
  `AubrunAlternative.measurable_traceCenteredRhoGammaMoment` at
  `PptFactorization/AubrunAlternativeModelBridge.lean:151` proves measurability
  of `G ↦ Re Tr((Dρ^Γ(G)-I)^m)` from finite-dimensional matrix operations and
  the existing measurable `G ↦ ρ^Γ(G)` bridge.
  `AubrunAlternative.aemeasurable_scaledRhoGammaEigenvalueCenteredPowerSum_of_measurable`
  at `PptFactorization/AubrunAlternativeModelBridge.lean:163` transfers that
  measurability to the eigenvalue sum by the trace identity, without needing a
  separate sorted-eigenvalue measurability theorem.  The sharp endpoint
  `AubrunAlternative.exists_log_order_constants_and_tendsto_rhoGamma_posSemidef_measureReal_one_of_four_lt_dSquared_traceMomentBound_of_measurable`
  at `PptFactorization/AubrunAlternativeModelBridge.lean:511` now exposes only
  probability-law data, sample-map measurability, and the actual growing
  trace-moment estimate.

2026-05-27 05:35 CEST:

- Challenge Before:
  The preferred `λ > 4` endpoint still asked the hard growing-moment supplier
  to bound the eigenvalue-coordinate centered sum.  That shape also left an
  eigenvalue-coordinate AEMeasurability input visible, and probing found no
  ready mathlib supplier for measurability of sorted Hermitian eigenvalues.
- Challenge After:
  `AubrunAlternative.rhoGamma_centered_trace_re_eq_sum_scaledRhoGammaEigenvalues`
  at `PptFactorization/AubrunAlternativeModelBridge.lean:96` proves the
  deterministic spectral identity between `Re Tr((Dρ^Γ-I)^m)` and the
  centered scaled-eigenvalue power sum.  The endpoint
  `AubrunAlternative.exists_log_order_constants_and_tendsto_rhoGamma_posSemidef_measureReal_one_of_four_lt_dSquared_traceMomentBound`
  at `PptFactorization/AubrunAlternativeModelBridge.lean:456` lets the hard
  growing-moment supplier be stated in the usual trace-moment form
  `Re Tr((d^2ρ^Γ-I)^(2m))`.  The eigenvalue AEMeasurability input remains
  visible for the Markov adapter; closing it requires either manual
  matrix-operation measurability/trace-Markov plumbing or a measurable
  eigenvalue-coordinate theorem.

2026-05-27 05:17 CEST:

- Challenge Before:
  The article-facing concrete `λ > 4` endpoint still exposed raw measurability
  of the PPT event `{ω | (rhoGamma (G d ω)).PosSemidef}`.
- Challenge After:
  `AubrunAlternative.measurableSet_rhoGamma_posSemidef_of_measurable` at
  `PptFactorization/AubrunAlternativeModelBridge.lean:85` proves the PPT event
  measurable from a measurable random sample matrix.  The sharper endpoint
  `AubrunAlternative.exists_log_order_constants_and_tendsto_rhoGamma_posSemidef_measureReal_one_of_four_lt_dSquared_scaledRhoGamma_of_measurable`
  at `PptFactorization/AubrunAlternativeModelBridge.lean:417` now asks for
  `Measurable (G d)` instead of a raw PPT-event measurability supplier.  The
  theorem-strength frontier remains the growing centered-moment estimate for
  eigenvalues of `d^2 ρ^Γ - I`, plus the model scaling/probability-law data.

2026-05-27 05:02 CEST:

- Challenge Before:
  The concrete `λ > 4` endpoint concluded that the non-PPT probability tends to
  zero.  The article-facing statement "PPT with probability tending to one"
  still required a complement/probability-law adapter and measurability of the
  PPT event.
- Challenge After:
  `AubrunAlternative.exists_log_order_constants_and_tendsto_rhoGamma_posSemidef_measureReal_one_of_four_lt_dSquared_scaledRhoGamma`
  at `PptFactorization/AubrunAlternativeModelBridge.lean:349` now gives the
  concrete PPT-probability statement directly: under probability laws,
  measurability of `{ω | (rhoGamma (G d ω)).PosSemidef}`, and the same
  eventual paper-shape centered-moment supplier, `(μ d).real {ω | ...} → 1`.
  The hard input remains exactly the growing centered-moment estimate for
  eigenvalues of `d^2 ρ^Γ - I`.

2026-05-27 04:47 CEST:

- Challenge Before:
  The concrete asymptotic `d^2 ρ^Γ - I` endpoint still required callers to
  pick the edge slack `eps`, the ratio `q`, and the logarithmic moment-order
  constant `c` by hand, even though the scalar theorem already proves such
  constants exist for every `λ > 4`.
- Challenge After:
  `AubrunAlternative.exists_log_order_constants_and_tendsto_not_rhoGamma_posSemidef_measure_zero_of_four_lt_dSquared_scaledRhoGamma`
  at `PptFactorization/AubrunAlternativeModelBridge.lean:217` now chooses
  those constants from `λ > 4` and returns the concrete conclusion
  `μ d {ω | ¬ (rhoGamma (G d ω)).PosSemidef} → 0` from the single visible
  eventual paper-shape centered-moment supplier.  The hard input is still
  exactly the growing centered-moment estimate for the eigenvalues of
  `d^2 ρ^Γ - I`.

2026-05-27 03:30 CEST:

- Challenge Before:
  The model-facing `d^2 ρ^Γ - I` bridge returned the explicit eventual
  finite-rate upper bound for the concrete non-PPT event, but users of the
  endpoint still had to separately combine that bound with the scalar
  logarithmic-decay condition `c log(1/q) > 2` to get probability convergence
  to zero.
- Challenge After:
  `AubrunAlternative.tendsto_not_rhoGamma_posSemidef_measure_zero_of_eventually_lintegral_bound_dSquared_scaledRhoGamma`
  at `PptFactorization/AubrunAlternativeModelBridge.lean:170` now gives the
  model-facing asymptotic conclusion directly:
  `μ d {ω | ¬ (rhoGamma (G d ω)).PosSemidef} → 0`, under the same visible
  eventual paper-shape centered-moment bound plus `0 < q` and
  `2 < c * log q⁻¹`.  The hard input is unchanged: the actual growing
  centered-moment estimate for the eigenvalues of `d^2 ρ^Γ - I`.

2026-05-27 03:15 CEST:

- Challenge Before:
  The model-facing finite-rate endpoint accepted an arbitrary positive scale
  `D d`.  For the article's controlled growing-moment route, the relevant
  normalized partial transpose is the paper-scale object `d^2 ρ^Γ`.
- Challenge After:
  `AubrunAlternative.eventually_not_rhoGamma_posSemidef_measure_le_of_eventually_lintegral_bound_dSquared_scaledRhoGamma`
  at `PptFactorization/AubrunAlternativeModelBridge.lean:138` specializes the
  model-facing endpoint to `D d = (d : ℝ)^2`, discharging scale positivity
  automatically for all sufficiently large `d`; the narrow build and axiom
  audit pass with only Lean/mathlib foundations.  The remaining hard input is
  now exactly the eventual paper-shape centered-moment estimate for the
  eigenvalues of `d^2 ρ^Γ - I`.

2026-05-27 03:00 CEST:

- Challenge Before:
  The concrete `ρ^Γ` eigenvalue-event bridge and the dependent-index
  paper-shape Markov adapter were both closed, but future suppliers still had
  to compose them manually to turn a moment bound for
  `scaledRhoGammaEigenvalues` into a bound on the actual non-PPT event
  `¬ (ρ^Γ).PosSemidef`.
- Challenge After:
  `AubrunAlternative.eventually_not_rhoGamma_posSemidef_measure_le_of_eventually_lintegral_bound_scaledRhoGamma`
  at `PptFactorization/AubrunAlternativeModelBridge.lean:97` composes those
  two adapters.  The visible hard input is now exactly the eventual
  paper-shape centered-moment bound for the scaled partial-transpose
  eigenvalue coordinates, plus eventual positivity of the scale `D`.

2026-05-27 02:45 CEST:

- Challenge Before:
  The eventual paper-shape finite-rate wrapper for the `λ > 4` route assumed a
  fixed finite spectral index type `ι`.  The concrete balanced matrix model
  uses a dimension-dependent index, e.g. `Fin d × Fin d`, so the scalar
  adapter was not directly shaped for the model-facing moment supplier.
- Challenge After:
  `AubrunAlternative.eventually_negative_event_measure_le_of_eventually_lintegral_bound_log_quadratic_rpow_log_dependent`
  at `PptFactorization/AubrunAlternative.lean:526` gives the same eventual
  finite-rate conclusion with `ι : ℕ → Type*`.  The hard input remains exactly
  the eventual growing centered-moment bound; this round only removed the
  fixed-index mismatch.

2026-05-27 02:30 CEST:

- Challenge Before:
  The `λ > 4` controlled growing-moment branch ended at an abstract
  finite-spectrum event `{ω | ∃ i, F d ω i < 0}`.  The concrete random-matrix
  model had `ρ^Γ`, but no audited bridge from matrix non-PPT to the scalar
  negative-eigenvalue event used by the moment adapters.
- Challenge After:
  `PptFactorization.RandomMatrixModel.measure_not_rhoGamma_posSemidef_le_exists_scaled_eigenvalue_neg`
  at `PptFactorization/RandomMatrixModel.lean:221` gives the model-facing
  inclusion in measure form.  For any positive scaling `D`, the event
  `¬ (ρ^Γ).PosSemidef` is bounded by the event that one scaled Hermitian
  eigenvalue coordinate of `ρ^Γ` is negative.  The remaining model bridge is
  now the actual random-matrix growing-moment estimate for these scaled
  eigenvalue coordinates.

2026-05-26 09:56 CEST:

- Challenge Before:
  The average-form auto-height strict route had cone-Gaussian, cap-cone, and
  coordinate source-explicit endpoints, but no source-explicit endpoint for the
  normalized surface-cap below-half tail.
- Challenge After:
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsStrictGap_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
  at `PptFactorization/AppendixBUpperBoundClosure.lean:12882` now records that
  route.  It factors through the strict proof-core surface endpoint at line
  `11062` after deriving actual improving directions from the average-form
  Lemma 4.3 source.

2026-05-26 09:36 CEST:

- Challenge Before:
  The uniform strict-improvement proof core had cap-cone, coordinate, and
  cone-Gaussian tail endpoints, but no normalized surface-cap below-half
  endpoint for the same actual-polarization improvement input.
- Challenge After:
  `AppendixB.upper_eventual_from_concrete_sequences_of_uniformPolarizationGap_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
  at `PptFactorization/AppendixBUpperBoundClosure.lean:11062` now records that
  route.  This keeps the strict-improvement core independent of tail-form
  detours: surface, cap-cone, coordinate, and cone-Gaussian forms are all named
  at the proof-core layer.

2026-05-26 08:47 CEST:

- Challenge Before:
  The direct block-to-`sSup` auto-height data had source-explicit strict
  cone-Gaussian and coordinate endpoints, but no matching strict endpoint for
  the below-half ambient cap-cone power-law tail.
- Challenge After:
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectStrictGap_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
  at `PptFactorization/AppendixBUpperBoundClosure.lean:13038` now records that
  route.  The hard leaves remain the direct or average-form Lemma 4.3 geometric
  supplier plus the selected north-pole tail, with
  `sphere_northPoleCapConeCosinePowerTailBelowHalf` now available on the direct
  strict route and `sphere_northPoleCoordinateCosinePowerTailBelowHalf` still
  the sharpest tail formulation.

2026-05-26 01:31 CEST:

- Challenge Before:
  The direct block-to-`sSup` auto-height data had a strict coordinate endpoint,
  but no source-explicit cone-Gaussian endpoint showing the same direct data
  through the uniform strict proof core.
- Challenge After:
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectStrictGap_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
  at `PptFactorization/AppendixBUpperBoundClosure.lean:13004` now records that
  route.  The hard leaves remain the direct or average-form Lemma 4.3 geometric
  supplier plus the selected north-pole tail, with
  `sphere_northPoleCoordinateCosinePowerTailBelowHalf` still the sharpest
  tail formulation and `sphere_northPoleCapConeGaussianTailLargeExponent` now
  available on the direct strict route.

2026-05-26 01:11 CEST:

- Challenge Before:
  The direct block-to-`sSup` auto-height data had a strict-improvement extractor
  in `FinRealSphereIsoperimetryProof.lean`, but no theorem-facing upper
  endpoint showing that direct data route through the uniform strict coordinate
  proof core.
- Challenge After:
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectStrictGap_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
  at `PptFactorization/AppendixBUpperBoundClosure.lean:13073` now records that
  route.  The hard leaves remain the direct or average-form Lemma 4.3 geometric
  supplier and `sphere_northPoleCoordinateCosinePowerTailBelowHalf`.

## Canonical Endpoints

### Upper: theorem-facing sharp branch

- Theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_uniformPolarizationGap_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- File:
  `PptFactorization/AppendixBUpperBoundClosure.lean:12756`
- Meaning:
  sharpest compiled upper endpoint with canonical mixed-word branches and
  scalar defect limits supplied internally; moment local-expansion input reduced
  to word-envelope bounds plus limits; the spherical-isoperimetry core is
  reduced to the actual strict-improvement theorem `hUniformGap`, and the
  north-pole tail is stated in the prioritized ambient cone-Gaussian form.
- Visible hypotheses:
  `hk3`, `hε`, `hOneSided`, `hUniformGap`,
  `sphere_northPoleCapConeGaussianTailLargeExponent`, `hIsoRealDim`,
  `hOperatorDim`, `ha`, `hK_half`, `hEta`, `hMomentWordBound`,
  `hMomentTermLimit`, `hBudget`, and `hEnvelope`.  Cap comparison is supplied
  internally by
  `sphere_halfMeasure_hemisphereComparisonGeTwo_of_uniform_polarization_gap_improvement_pos_lt_pi`.
  The checked adapter
  `uniform_polarization_gap_improvement_of_uniform_polarization_gainSup_lower_pos_lt_pi`
  supplies this strict-improvement input from the uniform gain-supremum leaf,
  and
  `uniform_polarization_gap_improvement_of_lemma43_autoHeightBands_gainSup_equal_mass_pos_lt_pi`
  now supplies the same strict-improvement input directly from the natural
  average-form auto-height Lemma 4.3 data.  The source-explicit strict
  cone-Gaussian endpoint is
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsStrictGap_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
  at `PptFactorization/AppendixBUpperBoundClosure.lean:12813`, and the sharper
  below-half cap-cone power endpoint is
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsStrictGap_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
  at `PptFactorization/AppendixBUpperBoundClosure.lean:12847`, the normalized
  surface-cap endpoint is
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsStrictGap_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
  at `PptFactorization/AppendixBUpperBoundClosure.lean:12882`, and the sharpest
  one-dimensional coordinate-tail endpoint is
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsStrictGap_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
  at `PptFactorization/AppendixBUpperBoundClosure.lean:12970`, routed through
  the proof-core coordinate endpoint
  `AppendixB.upper_eventual_from_concrete_sequences_of_uniformPolarizationGap_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
  at `PptFactorization/AppendixBUpperBoundClosure.lean:12913`.  The older
  direct-gain coordinate below-half theorem is a compatibility route, not the
  canonical live frontier.  The direct block-to-`sSup` data also has strict
  source-explicit coordinate-Gaussian, cone-Gaussian, cap-cone below-half, and
  coordinate endpoints,
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectStrictGap_northPoleCoordinateGaussianTailInteriorLargeExponentNorthPole_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`,
  at `PptFactorization/AppendixBUpperBoundClosure.lean:13039`, routed through
  the cone-tail normalization adapter
  `sphere_northPoleCapConeGaussianTailLargeExponent_of_coordinateTail`; its
  coordinate Gaussian tail input is adapter-closed from the sharper below-half
  coordinate power-law tail by
  `PptFactorization.AppendixB.sphere_coordinateGaussianTailInteriorLargeExponentNorthPole_of_coordinateCosinePowerTailBelowHalf`
  at `PptFactorization/SphericalPolarizationPushforwardTransport.lean:1310`,
  and the upper endpoint that performs this wiring explicitly is
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectStrictGap_northPoleCoordinateGaussianTailInteriorLargeExponentNorthPole_of_coordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
  at `PptFactorization/AppendixBUpperBoundClosure.lean:13073`.
  The active article-facing hard tail leaf is now the equivalent ambient
  cap-cone power-law statement
  `PptFactorization.AppendixB.sphere_northPoleCapConeCosinePowerTailBelowHalf`,
  consumed directly by
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectStrictGap_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
  at `PptFactorization/AppendixBUpperBoundClosure.lean:13107`.  Do not treat
  the coordinate-Gaussian or cone-Gaussian wrappers as live upper-frontier
  leaves for this branch: they are adapter-closed from the below-half
  coordinate/cap-cone power statements.  The closure test is an audited proof
  of `sphere_northPoleCapConeCosinePowerTailBelowHalf` itself, or a strictly
  smaller public density/cap-volume theorem that implies it and is wired into
  that exact proposition.
  The exact coordinate/surface rewrite bridge is
  `PptFactorization.AppendixB.sphere_northPoleCoordinateCosinePowerTailBelowHalf_iff_closedHalfspaceCosinePowerTailBelowHalf`
  at `PptFactorization/SphericalPolarizationPushforwardTransport.lean:548`;
  use its surface-cap side as the preferred target for the cap-volume/density
  proof of the remaining tail.
  The matching surface-cap/ambient cone rewrite bridge is
  `PptFactorization.AppendixB.sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf_iff_capConeCosinePowerTailBelowHalf`
  at `PptFactorization/SphericalPolarizationPushforwardTransport.lean:1051`;
  use its cone side when attacking the remaining tail through the open unit-ball
  cone-volume formula.
  The direct composed bridge from the endpoint-visible coordinate formulation
  to that cone-volume formulation is
  `PptFactorization.AppendixB.sphere_northPoleCoordinateCosinePowerTailBelowHalf_iff_capConeCosinePowerTailBelowHalf`
  at `PptFactorization/SphericalPolarizationPushforwardTransport.lean:1084`;
  use this name in theorem probes when the intended proof target is the ambient
  open-cone inequality itself.
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectStrictGap_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`,
  at `PptFactorization/AppendixBUpperBoundClosure.lean:13004`, and
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectStrictGap_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`,
  at `PptFactorization/AppendixBUpperBoundClosure.lean:13107`, and
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectStrictGap_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`,
  at `PptFactorization/AppendixBUpperBoundClosure.lean:13176`, routed through
  the matching proof-core strict endpoints by
  `uniform_polarization_gap_improvement_of_lemma43_autoHeightBands_directGainSup_equal_mass_pos_lt_pi`.
- Audit:
  foundational axioms only: `[propext, Classical.choice, Quot.sound]`.
- Note:
  `hIsoRealDim` and `hOperatorDim` are fixed-type compatibility bridges;
  the file proves they cannot close as stated
  (`not_eventually_fixed_bipartiteDimension_eq_dimensionSquared`).  Use
  pointwise `upperConcreteRealDim_eq_concreteModel_realDim` on varying-model
  routes instead.

### Upper: modular geometry branch

- Theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_hemisphereComparison_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- Surface-cap theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_hemisphereComparison_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- Cone-volume theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_hemisphereComparison_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- Surface-Gaussian theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_hemisphereComparison_northPoleClosedHalfspaceGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- Cone-Gaussian theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_hemisphereComparison_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- Lemma 4.3 surface-cap theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBands_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- Uniform gain-supremum surface-cap theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_uniformPolarizationGainSup_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- Uniform gain-supremum coordinate below-half theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_uniformPolarizationGainSup_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- Uniform gain-supremum cone below-half theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_uniformPolarizationGainSup_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- Uniform gain-supremum cone-Gaussian theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_uniformPolarizationGainSup_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- Uniform polarization-improvement surface-cap below-half theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_uniformPolarizationGap_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- Uniform polarization-improvement cone below-half theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_uniformPolarizationGap_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- Uniform polarization-improvement coordinate below-half theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_uniformPolarizationGap_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- Uniform polarization-improvement cone-Gaussian theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_uniformPolarizationGap_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- Auto-height uniform-gain coordinate below-half theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsUniformGain_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- Auto-height uniform-gain surface-cap below-half theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsUniformGain_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- Auto-height uniform-gain cone below-half theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsUniformGain_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- Auto-height direct-gain-supremum coordinate below-half theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- Auto-height direct-gain-supremum surface-cap below-half theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- Auto-height direct-gain-supremum full surface-cap theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleClosedHalfspaceCosinePowerTail_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- Auto-height direct-gain-supremum cone-volume theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleCapConeCosinePowerTail_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- Auto-height direct-gain-supremum below-half cone-volume theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- Auto-height direct-gain-supremum cone-Gaussian theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- Fixed-band same-mass surface-cap theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43FixedBandsEqualMass_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- Fixed-band same-mass coordinate below-half theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43FixedBandsEqualMass_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- Fixed-band same-mass cone below-half theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43FixedBandsEqualMass_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- Separate-tau height-band surface-cap theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43SeparateTau_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- Separate-tau height-band coordinate below-half theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43SeparateTau_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- Separate-tau height-band cone below-half theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43SeparateTau_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- Separate-tau height-band cone-Gaussian theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43SeparateTau_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- Rect-tau height-band coordinate below-half theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43HeightBandsRectTau_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- Rect-tau height-band cone-Gaussian theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43HeightBandsRectTau_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- Fixed-height-band direct-gain-supremum surface-cap theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43HeightBandsDirectGainSup_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- Fixed-height-band direct-gain-supremum coordinate below-half theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43HeightBandsDirectGainSup_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- Fixed-height-band average-gain-supremum coordinate below-half theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43HeightBandsGainSup_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- Fixed-height-band direct-gain-supremum cone-Gaussian theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43HeightBandsDirectGainSup_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- Fixed-height-band direct-gain-supremum cap-cone below-half theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_lemma43HeightBandsDirectGainSup_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
- File:
  `PptFactorization/AppendixBUpperBoundClosure.lean:12545,12577,12610,12639,12670,12513,10903,10954,11005,12702,11062,11120,12913,12756,11178,11224,11270,11321,11351,11380,11410,11441,11473,11504,11536,11566,11662,11750,11842,11941,12043,12133,12228,12362,12438,12813,12847,12882,12970,13004,13038,13073,13107,13207,13307,13382`
- Meaning:
  sharp upper adapter for the post-isoperimetry route. It consumes raw
  `sphere_halfMeasure_hemisphereComparisonGeTwo` and the nontrivial
  tail directly, while the full isoperimetry, cone/surface
  normalization, closed-halfspace, Gaussian-tail, canonical mixed-word, and
  scalar term-limit adapters are internal.  The tail is available in four
  audited forms: coordinate-law
  `sphere_northPoleCoordinateCosinePowerTailBelowHalf` and surface-cap
  `sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf`, plus below-half
  cone-volume
  `sphere_northPoleCapConeCosinePowerTailBelowHalf`, the normalized
  surface-Gaussian package
  `sphere_northPoleClosedHalfspaceGaussianTailLargeExponent`, and the direct
  cone-Gaussian package `sphere_northPoleCapConeGaussianTailLargeExponent`.
  The below-half surface and cone forms now convert in both directions, and the
  coordinate-Gaussian endpoint can feed the cone-Gaussian package directly
  through the cone-to-coordinate Gaussian adapter.  The Lemma 4.3
  surface-cap, coordinate-law, cone-Gaussian, and cap-cone fixed-height
  direct-gain theorems are the same target with
  `sphere_halfMeasure_hemisphereComparisonGeTwo` supplied internally by
  `sphere_halfMeasure_hemisphereComparisonGeTwo_of_lemma43_heightBands_directGainSup_equal_mass_pos_lt_pi`.
  The fixed-height coordinate endpoint additionally transports the
  coordinate-law tail through
  `sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf_of_coordinateCosinePowerTailBelowHalf`.
  The fixed-height average-form coordinate endpoint first applies
  `PptFactorization.AppendixB.lemma43_heightBands_directGainSup_equal_mass_of_heightBands_gainSup_equal_mass_pos_lt_pi`
  in `PptFactorization/FinRealSphereIsoperimetryProof.lean:3118`, converting
  an auxiliary `avg` rectangular block plus `avg ≤ sSup` into the direct
  block-to-`sSup` supplier consumed by the fixed-height direct endpoint.
  The fixed-height cap-cone below-half endpoint additionally derives the
  cone-Gaussian package internally via
  `sphere_northPoleCapConeGaussianTailLargeExponent_of_cosinePowerTailBelowHalf`.
  The older auto-height Lemma 4.3 surface-cap theorem is the compatibility
  target supplied internally by
  `sphere_halfMeasure_hemisphereComparisonGeTwo_of_lemma43_autoHeightBands_gainSup_equal_mass_pos_lt_pi`.
  Auto-height-band data also has a direct public adapter to the uniform
  gain-supremum leaf:
  `PptFactorization.AppendixB.uniform_polarization_gainSup_lower_of_lemma43_autoHeightBands_gainSup_equal_mass_pos_lt_pi`
  in `PptFactorization/FinRealSphereIsoperimetryProof.lean:2655`; it chooses
  a small `tauBand ≤ tauMax` using
  `exists_finRealSphereHeightBands_small_le` and then reuses the
  measure-trimming gain-supremum theorem.  The same average-form data now also
  supplies actual strict-improvement directions through
  `PptFactorization.AppendixB.uniform_polarization_gap_improvement_of_lemma43_autoHeightBands_gainSup_equal_mass_pos_lt_pi`
  in `PptFactorization/FinRealSphereIsoperimetryProof.lean:2730`, by composing
  that gain-supremum adapter with the half-gain direction extractor.
  The sharper direct public adapter
  `PptFactorization.AppendixB.uniform_polarization_gainSup_lower_of_lemma43_autoHeightBands_directGainSup_equal_mass_pos_lt_pi`
  in `PptFactorization/FinRealSphereIsoperimetryProof.lean:2795`
  specializes the auxiliary average to `sSup` of the objective gains, so the
  active geometric supplier can prove the rectangular block lower bound
  directly against the supremum.  Direct data also supplies the actual
  strict-improvement direction through
  `PptFactorization.AppendixB.uniform_polarization_gap_improvement_of_lemma43_autoHeightBands_directGainSup_equal_mass_pos_lt_pi`
  in `PptFactorization/FinRealSphereIsoperimetryProof.lean:2862`, by composing
  the direct gain-supremum adapter with the half-gain direction extractor.  The
  direct data also has a public
  cap-comparison closure point:
  `PptFactorization.AppendixB.finRealSphereHalfMassComplementSup_le_northPole_of_lemma43_autoHeightBands_directGainSup_equal_mass`
  in `PptFactorization/FinRealSphereIsoperimetryProof.lean:2920` and
  `PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo_of_lemma43_autoHeightBands_directGainSup_equal_mass_pos_lt_pi`
  in `PptFactorization/FinRealSphereIsoperimetryProof.lean:3118`.
  The uniform gain-supremum surface-cap theorem is sharper for the proof core:
  it supplies cap comparison internally from
  `sphere_halfMeasure_hemisphereComparisonGeTwo_of_uniform_polarization_gainSup_lower_pos_lt_pi`,
  so the remaining strict-improvement leaf is exactly a positive lower bound
  for the supremum of polarization objective gains.  The coordinate below-half
  uniform-gain endpoint exposes the tail in the same one-dimensional form as
  the sharp auto-height branch, avoiding the surface-cap detour at this
  proof-core level; the cone below-half uniform-gain endpoint exposes the
  ambient cap-cone tail directly through the checked cone full-isoperimetry
  adapter.  The uniform gain-supremum cone-Gaussian endpoint consumes
  `hUniformGainSup` and `sphere_northPoleCapConeGaussianTailLargeExponent`
  directly, derives cap comparison through
  `sphere_halfMeasure_hemisphereComparisonGeTwo_of_uniform_polarization_gainSup_lower_pos_lt_pi`,
  and reuses the modular cone-Gaussian hemisphere-comparison endpoint.  The
  uniform polarization-improvement endpoints are the direct strict-improvement
  proof-core routes: they consume an actual polarization direction improving
  the objective uniformly, then invoke the existing cap-comparison adapter
  before packaging either the below-half cone tail or the cone-Gaussian tail.
  This actual-direction supplier is no longer independent when
  `hUniformGainSup` is available: use
  `uniform_polarization_gap_improvement_of_uniform_polarization_gainSup_lower_pos_lt_pi`
  to extract a direction from the gain supremum.
  The sharp
  auto-height uniform-gain endpoint consumes
  `hLemma43AutoHeightBands`, derives the uniform-gain supplier internally by
  `uniform_polarization_gainSup_lower_of_lemma43_autoHeightBands_gainSup_equal_mass_pos_lt_pi`,
  and then reuses the coordinate or cone below-half uniform-gain endpoints
  according to the available tail supplier; the surface-cap variant consumes
  `sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf` directly and the
  cone variant consumes `sphere_northPoleCapConeCosinePowerTailBelowHalf`
  directly.  The sharper
  auto-height direct-gain endpoint consumes `hLemma43AutoHeightBandsDirectGainSup`,
  derives cap comparison through the direct cap-comparison theorem above, and
  is available in coordinate-law, normalized surface-cap, cone-volume
  below-half, full surface-cap, and cone-Gaussian forms.  The surface-cap
  below-half form is the canonical active branch because
  the coordinate push-forward is then internal.  Same-mass fixed-band
  Lemma 4.3 data now has a direct public adapter to this uniform-gain leaf:
  `PptFactorization.AppendixB.uniform_polarization_gainSup_lower_of_lemma43_measure_trimming_gainSup_equal_mass_pos_lt_pi`
  in `PptFactorization/FinRealSphereIsoperimetryProof.lean:2209`.
  The surface-cap upper endpoint
  `upper_eventual_from_concrete_sequences_of_lemma43FixedBandsEqualMass_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
  consumes that fixed-band same-mass data directly and routes through the
  uniform-gain theorem internally.  The coordinate and cone below-half
  fixed-band endpoints reuse the direct uniform-gain routes, so a future
  fixed-band geometric supplier can pair directly with either
  `sphere_northPoleCoordinateCosinePowerTailBelowHalf` or
  `sphere_northPoleCapConeCosinePowerTailBelowHalf` without a tail-form detour.
  The rect-tau height-band theorem now consumes the concrete proof-core shape
  where the trimming bands are `finRealSphereHeightBandAbove/Below` at
  thickness `tau` and the rectangular block lower bound is proved at a possibly
  larger separation `tauRect`, with `tau ≤ tauRect`; it derives the uniform
  gain-supremum supplier by
  `uniform_polarization_gainSup_lower_of_lemma43_heightBands_rectTau_gainSup_equal_mass_pos_lt_pi`
  in `PptFactorization/FinRealSphereIsoperimetryProof.lean:3398`.  The
  cone-Gaussian rect-tau endpoint consumes the same rect-tau supplier plus
  `sphere_northPoleCapConeGaussianTailLargeExponent`, derives cap comparison
  through the uniform gain-supremum route, and then reuses the modular
  cone-Gaussian hemisphere-comparison endpoint without exposing raw
  `sphere_halfMeasure_hemisphereComparisonGeTwo`.  The
  separate-tau height-band theorem is still sharper: it consumes the concrete
  data shape where the trimming bands are `finRealSphereHeightBandAbove/Below`
  with independent `tauBand` and `tauSep`, and uses
  `uniform_polarization_gainSup_lower_of_lemma43_heightBands_separateTau_gainSup_equal_mass_pos_lt_pi`
  in `PptFactorization/FinRealSphereIsoperimetryProof.lean:3523`.  The
  coordinate below-half separate-tau endpoint exposes
  `sphere_northPoleCoordinateCosinePowerTailBelowHalf` directly and converts
  through the checked full-isoperimetry adapter instead of leaving the tail only
  in the surface-cap formulation.  The cone below-half separate-tau endpoint
  similarly exposes `sphere_northPoleCapConeCosinePowerTailBelowHalf` directly
  for ambient cap-cone tail suppliers.  The cone-Gaussian separate-tau endpoint
  consumes the same separate-tau supplier plus
  `sphere_northPoleCapConeGaussianTailLargeExponent`, derives cap comparison
  through the uniform gain-supremum route, and then reuses the modular
  cone-Gaussian hemisphere-comparison endpoint without exposing raw
  `sphere_halfMeasure_hemisphereComparisonGeTwo`.  The modular cone-volume endpoint
  consumes `sphere_northPoleCapConeCosinePowerTailBelowHalf` directly after cap
  comparison, using the checked cone-to-surface adapter inside
  `fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleCapConeCosinePowerTailBelowHalf`.
  The fixed-height-band direct-gain-supremum endpoint now consumes rectangular
  block data already stated against `sSup` of the polarization objective gains,
  derives cap comparison through
  `sphere_halfMeasure_hemisphereComparisonGeTwo_of_lemma43_heightBands_directGainSup_equal_mass_pos_lt_pi`,
  and feeds the same surface-cap below-half upper branch without exposing an
  auxiliary `avg` witness.
- Visible hypotheses:
  `hk3`, `hε`, `hOneSided`, `sphere_halfMeasure_hemisphereComparisonGeTwo`,
  `sphere_northPoleCoordinateCosinePowerTailBelowHalf`, `hIsoRealDim`,
  `hOperatorDim`, `ha`, `hK_half`, `hEta`, `hMomentWordBound`,
  `hMomentTermLimit`, `hBudget`, and `hEnvelope`.  On the Lemma 4.3
  surface-cap route, replace raw `sphere_halfMeasure_hemisphereComparisonGeTwo`
  by `hLemma43AutoHeightBands` and replace the coordinate tail by
  `sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf`; on the modular
  cone-volume route, replace it by
  `sphere_northPoleCapConeCosinePowerTailBelowHalf`.  On the uniform
  gain route, replace `hLemma43AutoHeightBands` by `hUniformGainSup`; use the
  coordinate below-half variant when the tail supplier is one-dimensional, or
  the cone below-half variant when the supplier is ambient cap-cone volume.  On
  the uniform polarization-improvement route, replace it by `hUniformGap` and
  use the cone below-half variant when the supplier is ambient cap-cone volume;
  if `hUniformGainSup` is available, derive this actual-direction supplier by
  `uniform_polarization_gap_improvement_of_uniform_polarization_gainSup_lower_pos_lt_pi`.
  On
  the auto-height uniform-gain route, keep `hLemma43AutoHeightBands`; the
  uniform-gain supplier is derived internally before cap comparison, and use
  the coordinate or cone below-half variant according to the tail supplier.  On the
  fixed-band same-mass route, replace `hUniformGainSup` by the explicit
  fixed-band Lemma 4.3 data packet `hLemma43FixedBandsEqualMass`; use the
  coordinate below-half variant when the tail supplier is one-dimensional, or
  the cone below-half variant when it is stated as ambient cap-cone volume.  On the
  separate-tau route, replace the abstract fixed bands by concrete height-band
  data `hLemma43SeparateTau`; use the coordinate below-half variant when the
  tail supplier is stated as a one-dimensional coordinate-law inequality, or the
  cone below-half variant when it is stated as ambient cap-cone volume.
- Audit:
  foundational axioms only: `[propext, Classical.choice, Quot.sound]`.
- Named route:
  `sphere_hemisphereGaussianTail_of_northPoleCoordinateCosinePowerTailBelowHalf`
  packages the below-half coordinate tail into `sphere_hemisphereGaussianTail`,
  and
  `fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleCoordinateCosinePowerTailBelowHalf`
  packages cap comparison plus that tail into `FullSphericalIsoperimetry`.
  The surface-cap variant is bridged by
  `sphere_northPoleCoordinateCosinePowerTailBelowHalf_of_closedHalfspaceCosinePowerTailBelowHalf`
  and packaged by
  `fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleClosedHalfspaceCosinePowerTailBelowHalf`.
  The below-half cone-volume form is packaged by
  `fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleCapConeCosinePowerTailBelowHalf`,
  and its modular endpoint is
  `upper_eventual_from_concrete_sequences_of_hemisphereComparison_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`.
  The normalized surface-Gaussian form is packaged by
  `fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleClosedHalfspaceGaussianTailLargeExponent`,
  and its modular endpoint is
  `upper_eventual_from_concrete_sequences_of_hemisphereComparison_northPoleClosedHalfspaceGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`.
  The cone-Gaussian modular endpoint is
  `upper_eventual_from_concrete_sequences_of_hemisphereComparison_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
  now factors through the normalized surface-Gaussian endpoint using
  `sphere_northPoleClosedHalfspaceGaussianTailLargeExponent_of_coneTail`.
  The same-mass fixed-band Lemma 4.3 route can feed the uniform-gain theorem
  through
  `uniform_polarization_gainSup_lower_of_lemma43_measure_trimming_gainSup_equal_mass_pos_lt_pi`;
  this is the preferred adapter when a future supplier gives fixed `eps,tau`
  per positive gap.  The fixed-band coordinate and cone endpoints are
  `upper_eventual_from_concrete_sequences_of_lemma43FixedBandsEqualMass_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
  and
  `upper_eventual_from_concrete_sequences_of_lemma43FixedBandsEqualMass_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`.
  If the supplier gives auto-height-band data with a positive `tauMax`, use
  `uniform_polarization_gainSup_lower_of_lemma43_autoHeightBands_gainSup_equal_mass_pos_lt_pi`;
  it performs the thin-band selection internally before producing the same
  uniform gain-supremum conclusion.  If the supplier can target `sSup` directly,
  use
  `uniform_polarization_gainSup_lower_of_lemma43_autoHeightBands_directGainSup_equal_mass_pos_lt_pi`;
  if an actual improving direction is the needed interface, use
  `uniform_polarization_gap_improvement_of_lemma43_autoHeightBands_directGainSup_equal_mass_pos_lt_pi`
  from the same direct data.
  The corresponding canonical upper endpoint is
  `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`;
  the coordinate-law direct endpoint remains available as
  `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`.
  The cone-Gaussian direct endpoint
  `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
  is the post-cap-comparison adapter when the tail supplier is already stated
  as `sphere_northPoleCapConeGaussianTailLargeExponent`.
  The older average-witness endpoint remains available as
  `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsUniformGain_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`.
  Its surface-cap variant
  `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsUniformGain_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
  routes the normalized closed-halfspace below-half tail through the same
  uniform-gain proof spine.
  Its cone-tail variant
  `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsUniformGain_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
  skips the coordinate-law detour when the tail supplier is the ambient
  cap-cone below-half estimate.
  If the supplier gives concrete height bands with
  independent band thickness and rectangular separation, use
  `uniform_polarization_gainSup_lower_of_lemma43_heightBands_separateTau_gainSup_equal_mass_pos_lt_pi`
  and the corresponding separate-tau upper endpoint instead.  The direct
  uniform-gain coordinate endpoint is
  `upper_eventual_from_concrete_sequences_of_uniformPolarizationGainSup_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`;
  the direct uniform-gain cone endpoint is
  `upper_eventual_from_concrete_sequences_of_uniformPolarizationGainSup_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`.
  The direct uniform-gain cone-Gaussian endpoint is
  `upper_eventual_from_concrete_sequences_of_uniformPolarizationGainSup_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`.
  The direct uniform polarization-improvement cone endpoint is
  `upper_eventual_from_concrete_sequences_of_uniformPolarizationGap_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`.
  Its cone-Gaussian variant is
  `upper_eventual_from_concrete_sequences_of_uniformPolarizationGap_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`.

### Upper: audit wrapper (supplier packets)

- Theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_fullIso_activeTicketSuppliers`
- File:
  `PptFactorization/AppendixBUpperBoundClosure.lean:7825`
- Meaning:
  compact audit wrapper grouping `hOneSided`, `hMoment`, `hWordCases`, and
  `hDefectLimits`; not the primitive theorem-facing frontier.
- Visible hypotheses:
  `hk3`, `hε`, `hOneSided`, `hFullIso`, `hIsoRealDim`, `hOperatorDim`,
  `hMoment`, `hWordCases`, `hDefectLimits`.
- Audit:
  foundational axioms only: `[propext, Classical.choice, Quot.sound]`.

### Upper: favourable-event local-expansion route

- Theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_coordinateTailGeometry_favorableEvent_localExpansionMoment_canonicalMixedWords`
- File:
  `PptFactorization/AppendixBUpperBoundClosure.lean:7480`
- Meaning:
  derives `hOneSided` from positive one-column favourable mass plus
  deterministic inclusion blocks via
  `upperConcreteOneSidedPositiveDeviationWitness_of_oneColumnFavorableEvent`,
  unfolds the named moment-scale supplier through
  `upperConcreteMomentBadSetScaleBound_of_localExpansion_envelope`, and then
  feeds the sharper coordinate-tail geometry endpoint.  The older
  `..._fullIso_favorableEvent_activeTicketSuppliers` and
  `..._coordinateTailGeometry_favorableEvent_isolatedMoment...` wrappers remain
  as compatibility routes but are no longer the sharpest favourable-event
  endpoint.

### Upper: one-sided lower-bound local-expansion route

- Theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedLowerBound_localExpansionMoment_canonicalMixedWords`
- Cone-volume theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_northPoleCapConeCosinePowerTailBelowHalf_oneSidedLowerBound_localExpansionMoment_canonicalMixedWords`
- File:
  `PptFactorization/AppendixBUpperBoundClosure.lean:10320,10412`
- Meaning:
  source-explicit route for branches that produce an eventually positive lower
  bound on the actual one-sided upper-tail event.  It builds the
  `UpperConcreteOneSidedPositiveDeviationWitness` internally from that lower
  bound, unfolds `UpperConcreteMomentBadSetScaleBound C k` through the
  local-expansion/envelope supplier, derives
  `sphere_northPoleCapConeGaussianTailLargeExponent` from
  either `sphere_northPoleCoordinateCosinePowerTailBelowHalf` or the ambient
  `sphere_northPoleCapConeCosinePowerTailBelowHalf`, and then feeds the older
  cone-tail coordinate-geometry endpoint.  The compatibility theorem
  `AppendixB.upper_eventual_from_concrete_sequences_of_coordinateTailGeometry_oneSidedLowerBound_localExpansionMoment_canonicalMixedWords`
  remains at `PptFactorization/AppendixBUpperBoundClosure.lean:7649`, but it is
  no longer the sharpest lower-bound-fed analogue of the favourable-event
  local-expansion endpoint.
- Audit:
  foundational axioms only: `[propext, Classical.choice, Quot.sound]`.

### Upper: canonical operator-tail route

- Theorem:
  `AppendixB.upper_eventual_from_concrete_sequences_of_coordinateTailGeometry_oneSidedPositive_isolatedMomentConcreteOperatorTails_canonicalMixedWords`
- File:
  `PptFactorization/AppendixBUpperBoundClosure.lean:7318`
- Meaning:
  concrete upper route with canonical mixed-word bounds and scalar term limits
  supplied internally, with normalized sample/gamma operator tails also supplied
  by the existing concrete Gaussian/Wishart estimates.  The raw moment bad-set
  estimate and bad-set union budget are folded into the named
  `UpperConcreteMomentBadSetScaleBound C k` input.  The broad
  `FullSphericalIsoperimetry` input and broad
  `sphere_hemisphereGaussianTail` wrapper are replaced by explicit global
  sphere suppliers: cap comparison, coordinate dominance, and coordinate tail.
  The positive-radius coordinate dominance, coordinate-tail endpoint cases, and
  large-radius hemisphere tail are supplied internally by
  `sphere_hemisphereComplementCoordinateDominance_surface`,
  `sphere_coordinateGaussianTail_of_interior`, and
  `sphere_hemisphereLargeRadiusTail_surface`.
- Visible hypotheses:
  `hk3`, `hε`, `hOneSided`, `sphere_halfMeasure_hemisphereComparisonGeTwo`,
  `sphere_northPoleCapConeGaussianTailLargeExponent`, `hIsoRealDim`,
  `hOperatorDim`, and `UpperConcreteMomentBadSetScaleBound C k`.  The raw sample/gamma
  operator-tail inputs, broad `hFullIso`, broad `sphere_hemisphereGaussianTail`,
  `sphere_hemisphereComplementCoordinateDominance`,
  `sphere_hemisphereLargeRadiusTail`, closed endpoint cases for
  `sphere_coordinateGaussianTail`, moment bad-set tail, bad-set budget,
  deterministic `hWordBound`, and `hTermLimit` inputs are no longer visible.
- Audit:
  foundational axioms only: `[propext, Classical.choice, Quot.sound]`.

## Live Upper Frontier

The table below is the only live upper frontier map. If an item is not listed
here, it is not live debt on the canonical upper branch.

Current sharp upper branch no longer exposes broad `FullSphericalIsoperimetry`
or raw `sphere_halfMeasure_hemisphereComparisonGeTwo`.  It exposes the exact
direct auto-height-band Lemma 4.3 supplier
`hLemma43AutoHeightBandsDirectGainSup` and the one-dimensional north-pole
coordinate-law power supplier, reduced to its nontrivial below-half form
`sphere_northPoleCoordinateCosinePowerTailBelowHalf`; the complementary range
is supplied by antipodal half-tail symmetry through
`sphere_northPoleCoordinateCosinePowerTail_of_belowHalf`, and the normalized
surface-cap form remains equivalent by checked coordinate push-forward
adapters.
The cap comparison, normalized cap power law, cap-cone power law, Gaussian
cap-cone tail, closed-halfspace tail, coordinate-law Gaussian tail, and full
isoperimetry wrappers are now internal adapters
below those two inputs.  The Gaussian north-pole cap-cone tail is
bidirectionally connected to the
north-pole coordinate-law formulation by
`sphere_coordinateGaussianTailInteriorLargeExponentNorthPole_of_coneTail` and
`sphere_northPoleCapConeGaussianTailLargeExponent_of_coordinateTail`; the
below-half coordinate cosine-power tail supplies the full coordinate
cosine-power tail by `sphere_northPoleCoordinateCosinePowerTail_of_belowHalf`,
and the coordinate cosine-power tail supplies the normalized cap power law by
`sphere_northPoleClosedHalfspaceCosinePowerTail_of_coordinateCosinePowerTail`;
the normalized cosine-power cap tail supplies the cap-cone power law by
`sphere_northPoleCapConeCosinePowerTail_of_closedHalfspaceCosinePowerTail`; the
cosine-power tail supplies that Gaussian cone tail by
`sphere_northPoleCapConeGaussianTailLargeExponent_of_cosinePowerTail`; the
below-half cone cosine-power tail also supplies it directly by
`sphere_northPoleCapConeGaussianTailLargeExponent_of_cosinePowerTailBelowHalf`,
using the large-exponent hypothesis to enter the below-half range; the
cone tail then supplies the normalized closed-halfspace statement by
`sphere_northPoleClosedHalfspaceGaussianTailLargeExponent_of_coneTail`, and
the coordinate-law package is also supplied from the concrete normalized
closed-halfspace statement by
`sphere_coordinateGaussianTailInteriorLargeExponentNorthPole_of_closedHalfspaceTail`.
The modular endpoint
`upper_eventual_from_concrete_sequences_of_hemisphereComparison_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`
now exposes raw cap comparison plus only this below-half tail, so the next
tail proof can attack only the below-half one-dimensional coordinate-law
inequality without dragging Lemma 4.3 through the upper wrapper.
The named adapters
`sphere_hemisphereGaussianTail_of_northPoleCoordinateCosinePowerTailBelowHalf`
and
`fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleCoordinateCosinePowerTailBelowHalf`
are the shortest audited route from the two geometric leaves to the full
isoperimetry package.  The equivalent surface-cap tail route
`sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf` is now exposed as the
preferred target for a cone-volume proof, with two checked push-forward
adapters converting between it and the coordinate-law form.  The cone-volume
cosine-power law now also converts back to the full and below-half normalized
surface-cap laws through
`sphere_northPoleClosedHalfspaceCosinePowerTail_of_capConeCosinePowerTail` and
`sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf_of_capConeCosinePowerTail`,
so a proof of `sphere_northPoleCapConeCosinePowerTail` can feed the active
surface-cap endpoint directly.  A proof of the full normalized surface-cap
power law now feeds the active below-half target directly through
`sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf_of_closedHalfspaceCosinePowerTail`.
The tighter
`sphere_northPoleCapConeCosinePowerTailBelowHalf` package now names only the
needed cone-volume range and feeds the surface-cap endpoint through
`sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf_of_capConeCosinePowerTailBelowHalf`.

| Object | Canonical declaration(s) | File | Status | Plain math / next action |
|---|---|---|---|---|
| Full real-sphere isoperimetry supplier | `sphere_caps_minimize_neighborhoods` / `FullSphericalIsoperimetry`; reduction adapters `sphere_caps_minimize_neighborhoods_of_hemisphereComparison_and_tail`, `fullSphericalIsoperimetry_of_hemisphereComparison_and_tail`, `sphere_halfMeasure_hemisphereComparison_of_geTwo`, `sphere_hemisphereGaussianTail_of_coordinateDominance_and_coordinateTail`, `sphere_coordinateGaussianTailInteriorLargeExponent_of_northPole`, `sphere_coordinateGaussianTailInteriorGeTwo_of_largeExponent`, `sphere_coordinateGaussianTail_of_interior`, `sphere_coordinateGaussianTailInteriorLargeExponentNorthPole_of_coneTail`, `sphere_coordinateGaussianTailInteriorLargeExponentNorthPole_of_closedHalfspaceTail`, `sphere_northPoleCapConeGaussianTailLargeExponent_of_coordinateTail`, below-half cap adapters `sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf_of_closedHalfspaceCosinePowerTail`, `sphere_northPoleCoordinateCosinePowerTailBelowHalf_of_closedHalfspaceCosinePowerTailBelowHalf`, and `sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf_of_coordinateCosinePowerTailBelowHalf`; closed hemisphere-tail suppliers `sphere_hemisphereComplementCoordinateDominance_surface` and `sphere_hemisphereLargeRadiusTail_surface`; variational seed `exists_finRealSphereHalfMassCompetitor_near_complementInf`; polarization measurability `measurableSet_finRealSpherePolarization`; reflection invariance `finRealSurfaceProbabilityMeasure_map_reflection`, `finRealSurfaceProbabilityMeasure_reflection_preimage_real`; transports `globalSurfaceSubtypeLevy_of_fullSphericalIsoperimetry`, `sharpSphericalIsoperimetry_sphericalModelMeasure_of_fullSphericalIsoperimetry`, `upper_hIso_concreteModel_pointwise_of_fullSphericalIsoperimetry` | `PptFactorization/AppendixBSurfaceMeasure.lean:1998,2066,2106,2176`; `PptFactorization/SphericalPolarizationJacobianTargets.lean:951,901`; `PptFactorization/SphericalPolarizationPushforwardTransport.lean:401,416,433,451,466,494,522,552,792,939`; `PptFactorization/FinRealSphereIsoperimetryProof.lean:445,559,732`; `PptFactorization/AppendixBSphericalConcentration.lean:922`; `PptFactorization/AppendixBUpperBoundClosure.lean:78,10226,10450` | `large-radius tail, coordinate dominance, coordinate-tail endpoints, small-exponent coordinate-tail range, arbitrary-pole coordinate transport, n=1 cap-comparison, minimizing-sequence seed, polarization measurability, reflection surface-measure invariance, both cone/coordinate tail adapters, closed-halfspace/coordinate adapter, full-surface-to-below-half restriction, and below-half tail reroute closed; reduced to dimension-at-least-two cap comparison plus the nontrivial below-half north-pole surface-cap or cone-volume power tail` | On `S^{n-1}` with normalized surface probability, every half-mass set has geodesic enlargement complement with Gaussian tail `exp(-((n-1)r²)/2)`. The local reflection/Jacobian transport is closed, the large-radius hemisphere tail is closed by containment in the antipode singleton, and the positive-radius coordinate-dominance supplier is closed by projecting to the equator and proving the exact latitude identity `dist_geo(x, equator(x)) = arcsin(-⟪c,x⟫)`. The coordinate-tail adapters now prove the closed endpoint cases `r = 0` and `r = π/2`, the `n = 1` strict-interior case, the small-exponent strict-interior range `((n - 1) r^2) / 2 ≤ log 2` by antipodal half-tail symmetry, the arbitrary-pole-to-north-pole reduction by orthogonal transitivity of the real sphere, and the easy coordinate-power range `1 / 2 ≤ cos(r)^(n-1)` by `finRealSphere_positive_coordinate_tail_le_half`. A full normalized surface-cap cosine-power estimate now restricts directly to the active below-half surface-cap tail. The cone formula works in both directions between the ambient radial cone statement and the north-pole coordinate law, and the below-half tail now has equivalent surface-cap and below-half cone-volume statements via checked normalization adapters. The zero-dimensional cap-comparison case is closed because a half-mass subset of `S^0` contains a point, and a point is a closed hemisphere. The `2 ≤ n` cap-minimization route now has a compiled variational seed: every radius and tolerance admits a measurable half-mass competitor within that tolerance of the infimum of neighbourhood-complement mass. The polarization bookkeeping now includes measurability and the key measure-preserving reflection fact: the concrete reflection is the restriction of an ambient orthogonal linear isometry, so reflection preimages have the same surface probability. The remaining global suppliers are explicit: `sphere_halfMeasure_hemisphereComparisonGeTwo` (strict-improvement/minimality argument after this minimizing-sequence seed and polarization bookkeeping) and `sphere_northPoleCapConeCosinePowerTailBelowHalf` or equivalently `sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf` (the north-pole cap inequality only in the nontrivial range `cos(r)^(n-1) < 1 / 2`; alternatively prove the full normalized surface-cap cosine-power law and restrict it by the new adapter). |
| Moment bad-set scale supplier | `UpperConcreteMomentBadSetScaleBound`; closed route `upperConcreteMomentBadSetScaleBound_of_localExpansion_envelope`; sharp wrappers `upper_eventual_from_concrete_sequences_of_coordinateTailGeometry_favorableEvent_localExpansionMoment_canonicalMixedWords` and `upper_eventual_from_concrete_sequences_of_coordinateTailGeometry_oneSidedLowerBound_localExpansionMoment_canonicalMixedWords` | `PptFactorization/AppendixBUpperBoundClosure.lean:4601,4617,7475,7639` | `unpacked on sharp favourable-event and lower-bound routes` | The named moment packet is no longer visible on the sharp favourable-event route or the one-sided-lower-bound route. It is replaced by the local half-mass, local mixed-remainder, budget, and spherical-tail envelope inputs consumed by the already-compiled local-expansion supplier. |
| One-sided upper-tail positive-mass witness | `UpperConcreteOneSidedPositiveDeviationWitness`; routes `upperConcreteOneSidedPositiveDeviationWitness_of_oneColumnFavorableEvent`, `upperConcreteOneSidedPositiveDeviationWitness_of_eventually_positive_lower_bound` | `PptFactorization/AppendixBUpperBoundClosure.lean:2355,2371,2443` | `live on sharp branch; discharged on favourable-event route` | Eventual μ(columnMomentUpperTailSet) > 0. Lower pipeline gives target-prob lower bounds on the varying model but deleted-column transport to fixed-type upper mean is not yet wired. |
| Deterministic mixed-word branch invoice | `UpperConcreteMixedWordCaseBounds`; adapter `upperConcreteMixedWordBound_of_caseBounds`; canonical suppliers `upperConcreteOneQuadraticMixedWordBound_of_canonical_oneQ`, `upperConcreteOneLinearMixedWordBound_of_canonical_oneL`, `upperConcreteMultiDefectMixedWordBound_of_canonical_multi`; kernels `localWordScaledTraceTerm_oneLinear_le_envelope`, `localWordScaledTraceTerm_multiDefect_le_envelope` | `PptFactorization/AppendixBUpperBoundClosure.lean:4882,5121,5444,5635`; `PptFactorization/UpperMixedOneQuadraticBranch.lean:130`; `PptFactorization/UpperMixedOneLinearBranch.lean:204`; `PptFactorization/UpperMixedMultiDefectBranch.lean:692` | `closed on canonical route` | All three casewise mixed-word bounds are now supplied on the canonical scalar route. |
| Scalar mixed branches | `UpperConcreteOneLinearMixedTermLimit`, `UpperConcreteOneQuadraticMixedTermLimit`, `UpperConcreteMultiDefectMixedTermLimit`; canonical suppliers `upperConcreteOneLinearMixedTermLimit_of_canonical_oneL`, `upperConcreteOneQuadraticMixedTermLimit_of_canonical_oneQ`, `upperConcreteMultiDefectMixedTermLimit_of_canonical_multi`; helpers `upperConcrete_oneLinearRadiusRatio_tendsto_zero`, `upperConcrete_oneLinearTermRatio_tendsto_zero`, `upperConcreteN_pow_three_halves_eq`; package `UpperConcreteMixedDefectCaseLimits`; adapter `upperConcreteMixedTermLimit_of_defectCaseLimits` | `PptFactorization/AppendixBUpperBoundClosure.lean:4986-5058,5375,5399,5537,5809`; `PptFactorization/UpperMixedOneLinearBranch.lean`; `PptFactorization/UpperMixedMultiDefectBranch.lean` | `closed on canonical route` | One-linear, one-quadratic, and multi-defect canonical envelope terms vanish along the concrete sequence (`k ≥ 3`). The former visible `hMulti` scalar debt is now discharged by `upperConcreteMultiDefectMixedTermLimit_of_canonical_multi`. |

## Spherical Polarization Jacobian Frontier

This is a side frontier for the full spherical-isoperimetry supplier path, not
an additional leaf on the concrete upper endpoint unless that path is selected.

| Object | Canonical declaration(s) | File | Status | Plain math / next action |
|---|---|---|---|---|
| Height tie-level null set | `finRealSphere_tie_level_null`; package `finRealSpherePolarizationNullBoundaries_concrete` | `PptFactorization/SphericalPolarizationJacobianTargets.lean` | `closed` | The product null statement is proved for the concrete normalized real-sphere surface law using scalar height atomlessness and Fubini. It is no longer a live theorem-strength leaf. |
| Scalar height atomlessness | `finRealSphereHeightDistributionAtomless_concrete` | `PptFactorization/SphericalPolarizationJacobianTargets.lean` | `closed` | For every pole \(p\), the random variable \(x \mapsto \langle x,p\rangle\) on the normalized real sphere has no atoms. Equivalently, every latitude has surface probability zero. |
| Fibrewise polarization change of variables | `finRealSphereReflectionMap_pushforward_lintegral_formula`; measure form `finRealSphereReflectionMap_pushforward_withDensity`; package `finRealSphereReflectionMap_isJacobianTarget` | `PptFactorization/SphericalPolarizationPushforwardTransport.lean` | `closed` | The concrete reflection parametrization now has the nonnegative-integral formula, the measure-level `withDensity` push-forward formula, and the full `FinRealSpherePolarizationJacobianTarget` package. Axiom audit reports only Lean/mathlib foundations. This is no longer a live theorem-strength supplier for the spherical-isoperimetry route. |
| Reflection geodesic transport | `finRealSphereReflectionMap_geodesicDistance`, `finRealSphereReflectionMap_image_geodesicThickening` | `PptFactorization/SphericalPolarizationJacobianTargets.lean:930,941` | `closed` | The canonical reflection is now proved to preserve the project geodesic distance and to transport geodesic thickenings exactly to thickenings of reflected sets. This sets up the next polarization objective lemma: reflected/polarized competitors should not increase neighbourhood-complement mass. Axiom audit reports only Lean/mathlib foundations. |
| Two-point halfspace distance inequalities | `finRealSphereReflectionMap_dist_reflection_right_le_of_nonneg_nonpos`, `finRealSphereReflectionMap_geodesicDistance_reflection_right_le_of_nonneg_nonpos`, `finRealSphereReflectionMap_dist_le_reflection_left_of_nonneg_nonneg`, `finRealSphereReflectionMap_geodesicDistance_le_reflection_left_of_nonneg_nonneg` | `PptFactorization/SphericalPolarizationJacobianTargets.lean:942,976,990,1023` | `closed` | Challenge before: the polarization-neighbourhood comparison still lacked the pointwise metric facts comparing a point and its reflected partner across the polarizing halfspace. Challenge after: the two sign configurations needed for the standard two-point argument are available in both chordal and geodesic forms. Axiom audit reports only Lean/mathlib foundations. |
| Positive-side polarization neighbourhood inclusion | `finRealSpherePolarization_positiveSide_geodesicThickening_subset` | `PptFactorization/SphericalPolarizationJacobianTargets.lean:1291` | `closed` | Challenge before: the pointwise distance inequalities were not yet assembled into a set-level polarization-neighbourhood statement. Challenge after: the positive-side part of `P_v(N_r A)` is proved to lie in `N_r(P_v A)`. The negative-side/two-point measure comparison remains live and must not be collapsed into a false global inclusion without its extra argument. Axiom audit reports only Lean/mathlib foundations. |
| Polarization neighbourhood pair lemma | `finRealSpherePolarization_geodesicThickening_pair_of_mem` | `PptFactorization/SphericalPolarizationJacobianTargets.lean:1381` | `closed` | Challenge before: the positive-side inclusion did not yet encode what happens to a negative-side neighbourhood witness. Challenge after: every point of `N_r(A)` has at least one representative in its reflection pair inside `N_r(P_v A)`. The remaining step is the measure-level objective comparison using this pairwise statement, positive-side inclusion, and reflection mass preservation. Axiom audit reports only Lean/mathlib foundations. |
| Polarization neighbourhood measure-facing adapters | `finRealSphereGeodesicThickening_subset_polarized_union_reflection_preimage`, `finRealSurfaceProbabilityMeasure_positiveSide_pairNeighbourhood_real_le_polarizedThickening` | `PptFactorization/SphericalPolarizationJacobianTargets.lean:1420,1438` | `closed` | Challenge before: the pair lemma was only pointwise, so the next measure comparison still had to rederive the union/preimage and positive-side `measureReal` forms. Challenge after: `N_r(A)` is packaged as contained in `N_r(P_v A) ∪ rho_v^{-1}(N_r(P_v A))`, and the positive-side polarized-neighbourhood inclusion is available directly as a normalized-surface `measureReal` inequality. The full pair-count/objective comparison remains the next live theorem-strength step. Axiom audit reports only Lean/mathlib foundations. |
| Reflection-invariant positive-representative count | `finRealSurfaceProbabilityMeasure_reflectionInvariant_real_le_two_positiveSide` | `PptFactorization/SphericalPolarizationJacobianTargets.lean:1461` | `closed` | Challenge before: the pair-count route still lacked a reusable measure theorem converting reflection-invariance into a positive-representative bound. Challenge after: every measurable reflection-invariant set has normalized surface mass at most twice the mass of its positive-side representatives. This is a true counting lemma, not the final objective comparison; the remaining step is to combine it with the neighbourhood adapters without losing the necessary sharp factor. Axiom audit reports only Lean/mathlib foundations. |
| Pair-neighbourhood union measure bound | `finRealSurfaceProbabilityMeasure_pairNeighbourhoodUnion_real_le_two_polarizedThickening` | `PptFactorization/SphericalPolarizationJacobianTargets.lean:1518` | `closed` | Challenge before: the reflection-invariant count and positive-side neighbourhood inequality were separate ingredients. Challenge after: the union `N_r(A) ∪ rho_v^{-1}(N_r(A))` is bounded by `2 * μ(N_r(P_v A))` in normalized surface measure. This packages the older pair-count route with its factor-two loss; the sharp no-factor-loss objective comparison is now closed separately in the next row. Axiom audit reports only Lean/mathlib foundations. |
| Sharp polarization objective comparison | `finRealSphereGeodesicThickening_polarization_subset_polarization_geodesicThickening`, `finRealSurfaceProbabilityMeasure_geodesicThickening_polarization_real_le`, `finRealSphereNeighbourhoodComplementMass_polarization_ge` | `PptFactorization/SphericalPolarizationJacobianTargets.lean:1557,1851,1885` | `closed` | Challenge before: the measure-facing pair route still lost a factor of two, so it did not directly compare the true variational objective. Challenge after: the sharp set inclusion `N_r(P_v A) ⊆ P_v(N_r A)` is proved, surface mass preservation converts it to `μ(N_r(P_v A)) ≤ μ(N_r(A))`, and complement arithmetic gives `ComplementMass(A) ≤ ComplementMass(P_v A)`. This removes the no-factor-loss polarization objective leaf. Axiom audit reports only Lean/mathlib foundations. |
| Orthogonal transport for the objective | `finRealOrthogonalSphereMap_dist`, `finRealOrthogonalSphereMap_geodesicDistance`, `finRealOrthogonalSphereMap_image_geodesicThickening`, `finRealOrthogonalSphereMap_preimage_geodesicThickening_image`, `finRealSurfaceProbabilityMeasure_orthogonal_image_neighbourhoodComplement_real`, `finRealSphereNeighbourhoodComplementMass_orthogonal_image` | `PptFactorization/AppendixBSurfaceMeasure.lean:1419,1433,1445,1485,1518,2248` | `closed` | Challenge before: only the special reflection transport had been packaged at the objective level, so future hemisphere-normalization arguments would have to redo the same geodesic-thickening and measure-invariance proof for arbitrary rotations. Challenge after: any orthogonal image of a competitor has exactly the same geodesic-neighbourhood complement mass. This is adapter plumbing for the radius-wise supremum-dominance proof, especially when reducing closed hemispheres to a convenient pole. Axiom audit reports only Lean/mathlib foundations. |
| Closed-hemisphere objective normalization | `finRealOrthogonalSphereMap_image_closedHemisphere`, `finRealSphereNeighbourhoodComplementMass_closedHemisphere_eq`, `finRealSphereNeighbourhoodComplementMass_closedHemisphere_eq_northPole` | `PptFactorization/FinRealSphereIsoperimetryProof.lean:839,886,906` | `closed` | Challenge before: the hemisphere comparison still had arbitrary poles, so future radius-wise supremum domination would have to repeat orthogonal transitivity and objective transport to compare against the north-pole representative. Challenge after: every closed hemisphere has the same geodesic-neighbourhood complement objective at a fixed radius, and the objective can be normalized directly to the north pole. Axiom audit reports only Lean/mathlib foundations. |
| North-pole supremum comparison adapter | `finRealSphere_complementSup_le_some_closedHemisphere_iff_northPole`, `finRealSphereHalfMeasureHemisphereComparisonGeTwo_of_complementSup_le_northPole`, `sphere_halfMeasure_hemisphereComparisonGeTwo_of_complementSup_le_northPole` | `PptFactorization/FinRealSphereIsoperimetryProof.lean:921,945,971` | `closed` | Challenge before: the public comparison adapter still asked for an existential closed-hemisphere pole at each radius, even though all poles have the same objective. Challenge after: proving the north-pole closed hemisphere dominates the half-mass complement supremum at every radius is enough to close the dimension-at-least-two cap comparison. Axiom audit reports only Lean/mathlib foundations. |
| Positive-radius comparison reduction | `finRealSphereGeodesicDistance_nonneg`, `finRealSphereGeodesicThickening_eq_empty_of_nonpos`, `finRealSphereNeighbourhoodComplementMass_eq_one_of_nonpos`, `finRealSphereHalfMassComplementSup_le_one_surface`, `finRealSphereHalfMassComplementSup_le_northPole_of_nonpos`, `sphere_halfMeasure_hemisphereComparisonGeTwo_of_complementSup_le_northPole_pos` | `PptFactorization/FinRealSphereIsoperimetryProof.lean:105,998,1011,1024,1042,1058` | `closed` | Challenge before: the normalized north-pole supremum domination still included the endpoint and negative-radius cases. Challenge after: nonpositive radii are automatic because open geodesic thickenings are empty, so the remaining cap-comparison supplier only has to prove north-pole supremum domination for `0 < r`. Axiom audit reports only Lean/mathlib foundations. |
| Bounded-radius comparison reduction | `finRealSphereGeodesicDistance_le_pi`, `FinRealSphereHalfMassCompetitor.nonempty`, `finRealSphereGeodesicThickening_eq_univ_of_pi_lt`, `finRealSphereNeighbourhoodComplementMass_eq_zero_of_pi_lt`, `finRealSphereHalfMassComplementSup_le_northPole_of_pi_lt`, `sphere_halfMeasure_hemisphereComparisonGeTwo_of_complementSup_le_northPole_pos_le_pi` | `PptFactorization/FinRealSphereIsoperimetryProof.lean:116,1067,1086,1101,1114,1167` | `closed` | Challenge before: the positive-radius normalized north-pole domination still included radii beyond the sphere diameter. Challenge after: for `π < r`, every nonempty half-mass competitor has full geodesic thickening and zero complement objective, so the cap-comparison supplier was reduced to north-pole supremum domination on `0 < r ≤ π`; the boundary `r = π` is now closed by the next row. Axiom audit reports only Lean/mathlib foundations. |
| Diameter-boundary comparison reduction | `finRealSphere_dist_lt_two_of_ne_neg`, `finRealSphereGeodesicDistance_lt_pi_of_ne_neg`, `FinRealSphereHalfMassCompetitor.not_subset_singleton_surface`, `finRealSphereGeodesicThickening_eq_univ_of_pi_of_halfMass`, `finRealSphereNeighbourhoodComplementMass_eq_zero_of_pi_of_halfMass`, `finRealSphereHalfMassComplementSup_le_northPole_of_pi`, `sphere_halfMeasure_hemisphereComparisonGeTwo_of_complementSup_le_northPole_pos_lt_pi` | `PptFactorization/FinRealSphereIsoperimetryProof.lean:1146,1168,1181,1207,1232,1245,1323` | `closed` | Challenge before: the compact positive-radius frontier still included the open-thickening boundary `r = π`. Challenge after: at `r = π`, a half-mass competitor cannot be contained in the singleton antipode of any point, because singletons have zero normalized surface measure in dimension at least two; hence every point is within strict geodesic distance `< π` of some competitor point, the thickening is the whole sphere, and the complement objective is zero. The public comparison theorem is now reduced to normalized north-pole supremum domination only on `0 < r < π`. Axiom audit reports only Lean/mathlib foundations. |
| Variational supremum and polarized near-supremizer adapters | `finRealSphereHalfMassComplementSup`, `finRealSphereHalfMassComplementValues_bddAbove_surface`, `finRealSphereHalfMassComplementSup_ge_of_competitor`, `exists_finRealSphereHalfMassCompetitor_near_complementSup`, `exists_finRealSphereHalfMassCompetitor_near_complementSup_with_polarized_objective_ge`, `finRealSphereHalfMassComplementSup_strictImprovement_lt_tolerance`, `exists_finRealSphereHalfMassCompetitor_near_complementSup_no_admissible_eta_improvement`, `exists_finRealSphereHalfMassCompetitor_near_complementSup_all_polarizations_no_eta_improvement`, `exists_finRealSphereHalfMassCompetitor_near_complementSup_no_fixed_polarization_eta_improvement`, `finRealSphereHalfMeasureHemisphereComparison_of_complementSup_le_hemisphere`, `finRealSphereHalfMeasureHemisphereComparisonGeTwo_of_complementSup_le_hemisphere`, `sphere_halfMeasure_hemisphereComparisonGeTwo_of_complementSup_le_hemisphere` | `PptFactorization/AppendixBSurfaceMeasure.lean:2125,2163,2219,2242,2259,2286,2465`; `PptFactorization/SphericalPolarizationJacobianTargets.lean:1988,2013,2040,2074,2116` | `closed` | Challenge before: the cap-comparison theorem is a complement-mass maximum statement, while only infimum/minimizer plumbing had been packaged; even after supremum plumbing, the comparison theorem still needed an adapter from a radius-wise supremum statement to the public hemisphere-comparison API and a fixed-direction contradiction package. Challenge after: the correct supremum/maximizing-sequence orientation is available; values are bounded above by one, every competitor lies below the supremum, near-supremizers exist, polarization preserves admissibility and improves the objective, and the arithmetic is now packaged in direction-free form. A single `η / 2`-near supremizer cannot be improved by `η` by any admissible half-mass competitor; hence the same near-supremizer works simultaneously for every polarization direction, whose polarized competitor is admissible/no-worse but not an `η`-improvement. The older fixed-direction theorem remains as a compatibility form. The public comparison theorem is now reduced to proving normalized north-pole supremum domination on `0 < r < π`; the remaining theorem-strength leaf is the geometric strict-improvement/cap-characterization supplier that proves this radius-wise domination. Axiom audit reports only Lean/mathlib foundations. |
| Quantitative gap-improvement adapter | `finRealSphereHalfMassComplementSup_le_northPole_of_quantitative_gap_improvement`, `sphere_halfMeasure_hemisphereComparisonGeTwo_of_quantitative_gap_improvement_pos_lt_pi` | `PptFactorization/FinRealSphereIsoperimetryProof.lean:1349,1409` | `closed` | Challenge before: the live frontier still asked directly for normalized north-pole supremum domination on `0 < r < π`, leaving the contradiction step implicit. Challenge after: the remaining theorem-strength leaf is sharpened to a quantitative strict-improvement/cap-characterization supplier: for `0 < r < π`, every half-mass competitor whose neighbourhood-complement objective is at least `η` above the north-pole closed-hemisphere objective must admit another half-mass competitor improving the objective by at least `η`. This supplier plus the closed near-supremizer/no-improvement arithmetic closes `sphere_halfMeasure_hemisphereComparisonGeTwo`. Axiom audit reports only Lean/mathlib foundations. |
| Polarization-specific gap-improvement adapter | `finRealSphereHalfMassComplementSup_le_northPole_of_polarization_gap_improvement`, `sphere_halfMeasure_hemisphereComparisonGeTwo_of_polarization_gap_improvement_pos_lt_pi` | `PptFactorization/FinRealSphereIsoperimetryProof.lean:1443,1477` | `closed` | Challenge before: the quantitative gap supplier could improve an above-hemisphere competitor by an arbitrary half-mass competitor, leaving the route broader than the closed polarization machinery. Challenge after: it is enough to prove the canonical strict-improvement statement: if a half-mass competitor is `η` worse than the north-pole closed hemisphere on `0 < r < π`, then some spherical polarization of that same competitor improves the complement objective by at least `η`. The half-mass admissibility of the polarized set is supplied by `finRealSphereHalfMassCompetitor_polarization`, so the remaining theorem-strength leaf is now exactly the geometric polarization strict-improvement supplier. Axiom audit reports only Lean/mathlib foundations. |
| Uniform polarization-gap adapter | `exists_finRealSphereHalfMassCompetitor_near_complementSup_no_admissible_delta_improvement`, `exists_finRealSphereHalfMassCompetitor_above_northPole_no_admissible_delta_improvement`, `exists_finRealSphereHalfMassCompetitor_above_northPole_all_polarizations_no_delta_improvement`, `finRealSphereHalfMassComplementSup_le_northPole_of_uniform_polarization_gap_improvement`, `sphere_halfMeasure_hemisphereComparisonGeTwo_of_uniform_polarization_gap_improvement_pos_lt_pi` | `PptFactorization/FinRealSphereIsoperimetryProof.lean:1508,1544,1598,1648,1702` | `closed` | Challenge before: the polarization-specific adapter still asked for an improvement of the same size as the objective gap `η`, whereas the Lemma 4.3/trimming machinery naturally supplies a positive constant depending on the gap. Challenge after: it is enough to prove the canonical uniform statement: for each positive gap `η`, there is some `δ > 0`, independent of the competitor `A`, such that every half-mass competitor lying at least `η` above the north-pole hemisphere has a polarization improving the complement objective by `δ`. The near-supremizer lemmas first decouple the near-supremum tolerance `β` from the forbidden improvement size `δ`, then package the exact contradiction object used by the route: a competitor already above the north-pole objective by the chosen gap and immune to any admissible `δ`-improvement. The strengthened all-polarizations helper also supplies, simultaneously for every direction, polarized admissibility, the no-worse objective inequality, and the negated `δ`-improvement; the uniform polarization-gap theorem now consumes this package directly. Axiom audit reports only Lean/mathlib foundations. |
| Polarization gain-supremum adapter | `finRealSpherePolarizationObjectiveGainValues`, `exists_finRealSpherePolarization_objective_improvement_of_gainSup_lower`, `uniform_polarization_gap_improvement_of_uniform_polarization_gainSup_lower_pos_lt_pi`, `exists_finRealSphereHalfMassCompetitor_above_northPole_no_gainSup_lower`, `finRealSphereHalfMassComplementSup_le_northPole_of_uniform_polarization_gainSup_lower`, `sphere_halfMeasure_hemisphereComparisonGeTwo_of_uniform_polarization_gainSup_lower_pos_lt_pi` | `PptFactorization/FinRealSphereIsoperimetryProof.lean:1732,1745,1780,1832,1868,1916` | `closed` | Challenge before: the uniform polarization adapter still required extracting an actual direction from a positive improvement theorem, and the contradiction was routed through the uniform polarization-gap adapter. Challenge after: it is enough to prove a positive lower bound on the supremum of the real polarization objective gains. If `δ ≤ sSup gains`, then some direction improves the objective by at least `δ / 2`; the above-gap helper packages the direct contradiction form, choosing a half-mass competitor above the north-pole objective for which `δ ≤ sSup gains` is impossible. The new uniform-gap adapter also converts the same gain-supremum lower bound into the actual-direction `hUniformGap` theorem, so the strict-improvement branch no longer has a separate theorem-strength supplier once `hUniformGainSup` is known. This matches the average-to-supremum output of the Lemma 4.3 machinery and leaves only the geometric lower-bound supplier. Axiom audit reports only Lean/mathlib foundations. |
| Lemma 4.3 gain-supremum data adapter | `finRealSpherePolarization_gainSup_lower_of_lemma43_measure_trimming`, `finRealSphereHalfMassComplementSup_le_northPole_of_lemma43_measure_trimming_gainSup`, `sphere_halfMeasure_hemisphereComparisonGeTwo_of_lemma43_measure_trimming_gainSup_pos_lt_pi`; equal-mass route `measureReal_diff_eq_diff_of_measureReal_eq`, `finRealPolarization_balance_of_measureReal_eq`, `finRealSpherePolarization_gainSup_lower_of_lemma43_measure_trimming_equal_mass`, `finRealSphereHalfMassComplementSup_le_northPole_of_lemma43_measure_trimming_gainSup_equal_mass`, `sphere_halfMeasure_hemisphereComparisonGeTwo_of_lemma43_measure_trimming_gainSup_equal_mass_pos_lt_pi`; height-band route `exists_finRealSphereHeightBands_small`, `finRealSphereHeightBandAbove_subset_of_le`, `finRealSphereHeightBandBelow_subset_of_le`, `exists_finRealSphereHeightBands_small_le`, `finRealSphereHalfMassComplementSup_le_northPole_of_lemma43_heightBands_gainSup_equal_mass`, `sphere_halfMeasure_hemisphereComparisonGeTwo_of_lemma43_heightBands_gainSup_equal_mass_pos_lt_pi`, `lemma43_heightBands_directGainSup_equal_mass_of_heightBands_gainSup_equal_mass_pos_lt_pi`, `finRealSphereHalfMassComplementSup_le_northPole_of_lemma43_heightBands_directGainSup_equal_mass`, `sphere_halfMeasure_hemisphereComparisonGeTwo_of_lemma43_heightBands_directGainSup_equal_mass_pos_lt_pi`, `finRealSphereHalfMassComplementSup_le_northPole_of_lemma43_heightBands_rectTau_gainSup_equal_mass`, `sphere_halfMeasure_hemisphereComparisonGeTwo_of_lemma43_heightBands_rectTau_gainSup_equal_mass_pos_lt_pi`, `uniform_polarization_gainSup_lower_of_lemma43_heightBands_rectTau_gainSup_equal_mass_pos_lt_pi`, `finRealSphereHalfMassComplementSup_le_northPole_of_lemma43_autoHeightBands_gainSup_equal_mass`, `sphere_halfMeasure_hemisphereComparisonGeTwo_of_lemma43_autoHeightBands_gainSup_equal_mass_pos_lt_pi`, `uniform_polarization_gainSup_lower_of_lemma43_autoHeightBands_gainSup_equal_mass_pos_lt_pi`, `uniform_polarization_gap_improvement_of_lemma43_autoHeightBands_gainSup_equal_mass_pos_lt_pi`, `uniform_polarization_gainSup_lower_of_lemma43_autoHeightBands_directGainSup_equal_mass_pos_lt_pi`, `uniform_polarization_gap_improvement_of_lemma43_autoHeightBands_directGainSup_equal_mass_pos_lt_pi`, `finRealSphereHalfMassComplementSup_le_northPole_of_lemma43_autoHeightBands_directGainSup_equal_mass`, `sphere_halfMeasure_hemisphereComparisonGeTwo_of_lemma43_autoHeightBands_directGainSup_equal_mass_pos_lt_pi`; rectangular-block adapters `SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound.mono_tau`, `finRealPolarizationMuPlus_nonneg`, `finRealPolarizationMuMinus_nonneg`, `finRealPolarization_rectangularBlockLowerBound_mono_tau`; concrete trimming bounds `finRealPolarization_trimmed_masses_lower_bound_of_balance`, `finRealPolarization_trimmed_masses_lower_bound_of_equal_mass` | `PptFactorization/FinRealSphereIsoperimetryProof.lean:1942,1977,1997,2015,2056,2113,2154,2272,2311,2409,2420,2432,2470,2530,2576,2655,2730,2795,2862,2920,2974,3015,3071,3118,3195,3248,3291,3351,3398,3467,3523,3592`; `PptFactorization/SphericalPolarizationGeometricKernel.lean:2109`; `PptFactorization/PolarizationLemma43MeasureTrimming.lean:123,130,138,157,197` | `closed and sharpened` | Challenge before: the active theorem still asked abstractly for a lower bound on the supremum of polarization gains, and the concrete data package included raw balance `μ(C \ A) = μ(A \ C)` plus abstract measurable bands. Challenge after: the lower bound is produced directly by the already-closed measure-trimming Lemma 4.3 theorem once `supDelta` is instantiated as that gain supremum; additionally, the balance condition is generated from the simpler same-mass condition `μ.real C = μ.real A`, the band measurability obligations disappear when the supplier chooses concrete height bands `finRealSphereHeightBandAbove/Below`, atomlessness gives a positive height thickness making both concrete bands have mass at most `eps / 4`, monotonicity lets that thickness be chosen below any prescribed positive `tauMax`, the rectangular-block inequality can now be proved at any larger separation `tauRect` and degraded to the smaller band thickness `tau` directly for the concrete trimmed defects, and the actual trimmed masses now satisfy `μ(D₊), μ(D₋) ≥ eps / 4` from either balanced symmetric difference or equal mass plus band removal. The fixed height-band route now also has a direct-`sSup` comparison theorem, and the new transformer derives that direct supplier from the ordinary `avg` plus `avg ≤ sSup` shape produced by trimming. The rect-tau height-band route now feeds the uniform gain-supremum theorem directly when the rectangular block is proved at `tauRect` and the trimming bands are thinner at `tau ≤ tauRect`. The active auto-band route chooses the concrete band thickness internally and now also feeds both the uniform gain-supremum theorem and a named actual-direction strict-improvement theorem; the direct-gain adapter further removes the auxiliary `avg` witness by using `sSup` of the objective gains as the rectangular-block target, and the direct cap-comparison theorem now exposes `sphere_halfMeasure_hemisphereComparisonGeTwo` directly from that data shape. The live theorem-strength supplier is the global geometric synchronization: choose a same-mass model `C`, pole and level, far symmetric-difference lower bound, and prove the rectangular block lower bound at an auxiliary average with a comparison to the gain supremum. Axiom audit reports only Lean/mathlib foundations. |
| Lemma 4.3 endpoint adapters | Separate-scale route `finRealSphereHalfMassComplementSup_le_northPole_of_lemma43_heightBands_separateTau_gainSup_equal_mass`, `sphere_halfMeasure_hemisphereComparisonGeTwo_of_lemma43_heightBands_separateTau_gainSup_equal_mass_pos_lt_pi`; active auto-band route `finRealSphereHalfMassComplementSup_le_northPole_of_lemma43_autoHeightBands_gainSup_equal_mass`, `sphere_halfMeasure_hemisphereComparisonGeTwo_of_lemma43_autoHeightBands_gainSup_equal_mass_pos_lt_pi`, `uniform_polarization_gainSup_lower_of_lemma43_autoHeightBands_gainSup_equal_mass_pos_lt_pi`, `uniform_polarization_gap_improvement_of_lemma43_autoHeightBands_gainSup_equal_mass_pos_lt_pi`, `uniform_polarization_gainSup_lower_of_lemma43_autoHeightBands_directGainSup_equal_mass_pos_lt_pi`, `uniform_polarization_gap_improvement_of_lemma43_autoHeightBands_directGainSup_equal_mass_pos_lt_pi`, `finRealSphereHalfMassComplementSup_le_northPole_of_lemma43_autoHeightBands_directGainSup_equal_mass`, `sphere_halfMeasure_hemisphereComparisonGeTwo_of_lemma43_autoHeightBands_directGainSup_equal_mass_pos_lt_pi`; upper wrappers `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBands_northPoleCapConeTail_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`, `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsUniformGain_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`, `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsUniformGain_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`, `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsUniformGain_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`, `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`, `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleClosedHalfspaceCosinePowerTail_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`, `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`, `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleCapConeCosinePowerTail_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`, `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`, `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleClosedHalfspaceGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`, `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm` | `PptFactorization/FinRealSphereIsoperimetryProof.lean:3467,3592,2470,2530,2655,2730,2795,2862,2920,2974`; `PptFactorization/AppendixBUpperBoundClosure.lean:9702,11021,11067,11113,11213,11242,11179,11272,11303,11335,11398` | `closed and canonical active frontier` | Challenge before: the preferred separate-scale endpoint still required the supplier to preselect one thin height-band scale and prove both band masses are at most `eps / 4`. Challenge after: the active auto-band endpoint chooses the band thickness internally using height atomlessness, and the same auto-band data now supplies the direct uniform gain-supremum leaf, the average-form actual-direction strict-improvement adapter, the direct actual-direction adapter, and cap comparison directly through the direct block-to-`sSup` theorem. The auto-height uniform-gain surface and cone endpoints also feed the normalized closed-halfspace and ambient below-half cone tails directly through the uniform-gain proof spine, avoiding tail-form detours on that compatibility branch. The direct-gain-supremum endpoint removes the auxiliary average witness from the active theorem-facing branch and now derives `sphere_halfMeasure_hemisphereComparisonGeTwo` explicitly; the active surface-cap version also makes the coordinate push-forward internal, the full surface-cap version restricts the natural cap power law internally to the active below-half range, the cone-volume versions make cone/surface normalization internal in the other direction, and the cone-Gaussian version now consumes a surface-Gaussian direct endpoint and a named `FullSphericalIsoperimetry` supplier for direct Lemma 4.3 data plus `sphere_northPoleCapConeGaussianTailLargeExponent` factored through the direct normalized surface-Gaussian full-isoperimetry adapter. The Lemma 4.3 supplier only has to produce a positive `tauMax` and prove the rectangular block lower bound with `sSup` of polarization gains as target for every `0 < tauBand ≤ tauMax`, while same mass, far symmetric difference, pole/level choice, rectangular geometry, and the selected north-pole tail estimate remain the genuine theorem-strength content. Axiom audit reports only Lean/mathlib foundations. |
| Historical infimum adapters | `finRealSphereHalfMassComplementInf_le_of_competitor`, `exists_finRealSphereHalfMassCompetitor_near_complementInf_with_polarized_objective_ge` | `PptFactorization/AppendixBSurfaceMeasure.lean:2185`; `PptFactorization/SphericalPolarizationJacobianTargets.lean:1962` | `closed but noncanonical` | These compile and remain harmless, but the cap-comparison theorem is oriented by maximizing complement mass. Prefer the supremum row above for the active spherical-isoperimetry route. |
| Reflection neighbourhood-objective invariance | `isOpen_finRealSphereGeodesicThickening`, `measurableSet_finRealSphereGeodesicThickening`, `finRealSurfaceProbabilityMeasure_reflection_image_neighbourhoodComplement_real`, `finRealSphereNeighbourhoodComplementMass_reflection_image` | `PptFactorization/AppendixBSurfaceMeasure.lean:1393,1411`; `PptFactorization/SphericalPolarizationJacobianTargets.lean:1031,1058` | `closed` | Challenge before: geodesic thickening measurability and reflection-measure invariance had not yet been combined at the objective level. Challenge after: a reflected competitor has exactly the same geodesic-neighbourhood complement mass. The remaining spherical-isoperimetry step is the nontrivial full-polarization comparison, not the pure-reflection objective bookkeeping. Axiom audit reports only Lean/mathlib foundations. |
| Polarization mass preservation | `finRealSurfaceProbabilityMeasure_polarizationGained_real_eq_lost_real`, `finRealSurfaceProbabilityMeasure_polarization_real_eq`, `finRealSphereHalfMassCompetitor_polarization` | `PptFactorization/SphericalPolarizationJacobianTargets.lean:1204,1247,1311` | `closed` | The concrete reflection swaps the gained and lost pieces of a polarization, fixing only the equator; reflection invariance of the normalized surface law then proves exact mass preservation and shows that polarizing a measurable half-mass competitor remains admissible for the variational cap-comparison problem. Axiom audit reports only Lean/mathlib foundations. |
| Quantitative strict-improvement core | `PolarizationLemma43Core.lemma43_strict_improvement_core`; measure-trimming route `PolarizationLemma43Core.lemma43_strict_improvement_core_of_measureTrimming`; FinRealSphere bridge `SphericalPolarization.GeometricKernel.lemma43_strict_improvement_from_measure_trimming`; concrete D± trimming bounds `finRealPolarization_trimmed_masses_lower_bound_of_balance`, `finRealPolarization_trimmed_masses_lower_bound_of_equal_mass` | `PptFactorization/PolarizationLemma43Core.lean`; `PptFactorization/PolarizationLemma43MeasureTrimming.lean:157,197`; `PptFactorization/SphericalPolarizationStrictImprovement.lean` | `closed and imported` | The algebraic trimming/product estimate behind Lemma 4.3 is compiled and included in the project import spine. The set-level band-removal step now proves `mu(D_±) ≥ eps / 4` from actual measurable trimmed sets, balanced symmetric difference, and band mass bounds; in the equal-mass concrete route, the balance is derived automatically from `μ.real C = μ.real E`. The D± lower bounds no longer have to be supplied as scalar hypotheses. The remaining geometric supplier still consumes only the rectangular kernel block lower bound and average-to-supremum comparison. |

## Resolved Or Rerouted Noise

These items are not live frontier on the canonical upper branch and should not
be re-listed elsewhere in this atlas as active debt.

| Item | Why it is not live frontier | Main audited route |
|---|---|---|
| `hFavPos` | replaced by the canonical one-sided witness or by the lower-pipeline source-explicit endpoint | `upper_hFavPos_of_positive_favorable_subset`, `upperConcreteModelOneSidedPositiveDeviationWitness_of_positiveFavorableEvent_absMean_tendstoErrorBudgets` |
| one-sided lower-bound packet with named moment supplier | replaced by the source-explicit local-expansion endpoints, which build both the one-sided witness and moment-scale supplier internally; the sharp tail form is now the below-half cone-volume variant | `upper_eventual_from_concrete_sequences_of_coordinateTailGeometry_oneSidedLowerBound_localExpansionMoment_canonicalMixedWords`, `upper_eventual_from_concrete_sequences_of_northPoleCapConeCosinePowerTailBelowHalf_oneSidedLowerBound_localExpansionMoment_canonicalMixedWords` |
| `sphere_hemisphereLargeRadiusTail` | closed by no-input supplier and no longer visible on coordinate-tail upper routes | `sphere_hemisphereLargeRadiusTail_surface` |
| `hMomentTail` | natural source shape, but not visible on the canonical exponential endpoint | `backgroundMomentValue_mean_tail_le_of_fullSphericalIsoperimetry`, then `upperConcreteModelMomentExponentialDeviationSetBound_of_backgroundMomentValue_meanTailBound` |
| `hWordBound` | compatibility envelope only | `upperConcreteModelMixedWordBound_of_caseBounds` |
| `hDefectLimits` | grouped scalar invoice only | `upperConcreteMixedTermLimit_of_defect_cases` and the three explicit scalar branches |
| `hMeanAbs`, `hBudgetGap`, zero-limit error bundle | older favorable-event or budget routes; not visible on the canonical branch | `upper_hMean_of_upperConcreteModelMean_abs_bound`, `upper_final_error_budget_of_eventual_gap_and_tendsto_zero` |
| raw existential deleted-background mean witness `hMean` on the lower-concrete canonical wrappers | replaced on the new audited wrapper by the named deleted-column Catalan asymptotic supplier | `upper_eventual_from_concreteModel_sequences_of_fullIso_lowerConcreteCanonicalProbabilitySuppliers_deletedColumnMomentAsymptotic_momentExponentialDeviationConcreteOperatorTails_mixedWordCaseBounds_isolatedMixedWordTermCases` |
| `hProfile`, `hBackgroundTransfer`, `hColumnMixed` | supplier-route ingredients for building `hOneSided`, not leaves on the canonical endpoint | `upperConcreteModelOneSidedPositiveDeviationWitness_of_positiveFavorableEvent_absMean_tendstoErrorBudgets` |

## Lower Pipeline Status For The Upper Route

The lower deterministic/probability pipeline should not be reported as live
upper mathematical debt just because the source-explicit upper endpoint names
its interface hypotheses.

Relevant lower-side suppliers already present in the workspace include:

- `lower_concrete_hColumnIncluded_of_closed_deterministic_blocks`
  at `PptFactorization/AppendixBLowerBoundClosure.lean:3715`
- `lower_concrete_hProduct`
  at `PptFactorization/AppendixBLowerBoundClosure.lean:3008`
- `lower_concrete_hCap_of_referenceCone` and
  `lower_concrete_hCap_of_referenceCone_canonicalDirection`
  at `PptFactorization/AppendixBLowerBoundClosure.lean:3665,3695`
- `lower_concrete_hBackgroundHalf_of_reduced_spherical_bad_bounds` and
  `lower_concrete_hBackgroundHalf_of_reduced_spherical_bad_bounds_smallBudget`
  at `PptFactorization/AppendixBLowerBoundClosure.lean:3469,3506`

So if those are the intended concrete suppliers, the remaining task is to wire
their conclusions into the source-explicit upper endpoint, not to reprove the
lower deterministic estimates from scratch.

## Short Supplier Registry

These are the important audited adapters that future rounds should reuse rather
than rediscover.

| Role | Declaration | File | Audit status |
|---|---|---|---|
| transport full isoperimetry to exact spherical Levy on the model law | `globalSurfaceSubtypeLevy_of_fullSphericalIsoperimetry` together with `globalSphericalLevy_sphericalModel_of_subtype_and_polar_law` | `PptFactorization/AppendixBSphericalConcentration.lean:923`; `PptFactorization/AppendixBLevyPolarBridge.lean:1562` | foundational axioms only |
| remove `hOneSided` by favourable-event deterministic blocks | `upperConcreteOneSidedPositiveDeviationWitness_of_oneColumnFavorableEvent` | `PptFactorization/AppendixBUpperBoundClosure.lean:2443` | foundational axioms only |
| remove monolithic mixed-word envelope | `upperConcreteMixedWordBound_of_caseBounds` | `PptFactorization/AppendixBUpperBoundClosure.lean:4882` | foundational axioms only |
| close moment scale supplier from local expansion | `upperConcreteMomentBadSetScaleBound_of_localExpansion_envelope`; sharp endpoints `upper_eventual_from_concrete_sequences_of_coordinateTailGeometry_favorableEvent_localExpansionMoment_canonicalMixedWords` and `upper_eventual_from_concrete_sequences_of_coordinateTailGeometry_oneSidedLowerBound_localExpansionMoment_canonicalMixedWords` | `PptFactorization/AppendixBUpperBoundClosure.lean:4617,7475,7639` | foundational axioms only |
| close large-radius hemisphere tail | `sphere_hemisphereLargeRadiusTail_surface` | `PptFactorization/FinRealSphereIsoperimetryProof.lean:732` | foundational axioms only |
| close coordinate-tail endpoint cases | `sphere_coordinateGaussianTail_of_interior` | `PptFactorization/FinRealSphereIsoperimetryProof.lean:558` | foundational axioms only |
| reduce coordinate power tail to below-half range | `sphere_northPoleCoordinateCosinePowerTail_of_belowHalf`; average-form coordinate endpoint `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBands_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm` | `PptFactorization/AppendixBUpperBoundClosure.lean:10156,10733`; `PptFactorization/SphericalPolarizationPushforwardTransport.lean:385` | foundational axioms only |
| reroute below-half tail between coordinate, normalized surface cap, and ambient cone forms | `sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf_of_closedHalfspaceCosinePowerTail`, `sphere_northPoleCoordinateCosinePowerTailBelowHalf_of_closedHalfspaceCosinePowerTailBelowHalf`, `sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf_of_coordinateCosinePowerTailBelowHalf`, `sphere_northPoleCapConeCosinePowerTailBelowHalf_of_closedHalfspaceCosinePowerTailBelowHalf`; uniform-gain coordinate endpoint `upper_eventual_from_concrete_sequences_of_uniformPolarizationGainSup_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`; uniform-gain surface endpoint `upper_eventual_from_concrete_sequences_of_uniformPolarizationGainSup_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`; uniform-gain cone endpoint `upper_eventual_from_concrete_sequences_of_uniformPolarizationGainSup_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`; uniform polarization-improvement surface and cone endpoints `upper_eventual_from_concrete_sequences_of_uniformPolarizationGap_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`, `upper_eventual_from_concrete_sequences_of_uniformPolarizationGap_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`; auto-height direct-gain endpoints `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`, `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`, and `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleClosedHalfspaceCosinePowerTail_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`; auto-height uniform-gain compatibility endpoints `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsUniformGain_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`, `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsUniformGain_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`, and `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsUniformGain_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`; fixed-band coordinate endpoint `upper_eventual_from_concrete_sequences_of_lemma43FixedBandsEqualMass_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`; fixed-band cone endpoint `upper_eventual_from_concrete_sequences_of_lemma43FixedBandsEqualMass_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`; separate-tau coordinate endpoint `upper_eventual_from_concrete_sequences_of_lemma43SeparateTau_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`; rect-tau coordinate endpoint `upper_eventual_from_concrete_sequences_of_lemma43HeightBandsRectTau_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`; separate-tau cone endpoint `upper_eventual_from_concrete_sequences_of_lemma43SeparateTau_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`; Lemma 4.3 surface endpoint `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBands_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`; independent surface endpoint `upper_eventual_from_concrete_sequences_of_hemisphereComparison_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm` | `PptFactorization/SphericalPolarizationPushforwardTransport.lean:466,494,522,843`; `PptFactorization/AppendixBUpperBoundClosure.lean:10954,10903,11005,11062,11120,11321,11351,11380,11178,11224,11270,11662,11750,11941,12043,12133,12513,12577` | foundational axioms only |
| route full surface, ambient cap-cone cosine tails, coordinate/surface Gaussian tails, and cone-Gaussian tails into the direct-gain compatibility endpoints | full surface endpoint `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleClosedHalfspaceCosinePowerTail_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`; full-to-below-half restriction `finRealSphereNorthPoleCapConeCosinePowerTailBelowHalf_of_capConeCosinePowerTail`, `sphere_northPoleCapConeCosinePowerTailBelowHalf_of_capConeCosinePowerTail`; full cone-to-surface adapters `finRealSphereNorthPoleClosedHalfspaceCosinePowerTail_of_capConeCosinePowerTail`, `sphere_northPoleClosedHalfspaceCosinePowerTail_of_capConeCosinePowerTail`, `sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf_of_capConeCosinePowerTail`; below-half cone-to-surface adapters `finRealSphereNorthPoleClosedHalfspaceCosinePowerTailBelowHalf_of_capConeCosinePowerTailBelowHalf`, `sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf_of_capConeCosinePowerTailBelowHalf`; cone-volume endpoints `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleCapConeCosinePowerTail_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm` and `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`; surface-Gaussian endpoint `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleClosedHalfspaceGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`; coordinate-Gaussian endpoint `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleCoordinateGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`; cone-Gaussian endpoint `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm` | `PptFactorization/SphericalPolarizationPushforwardTransport.lean:371,380,803,861,871,881,939,1241`; `PptFactorization/AppendixBUpperBoundClosure.lean:11380,11272,11303,11335,11366,11398` | foundational axioms only |
| derive uniform actual-polarization improvement from gain-supremum lower bound | `uniform_polarization_gap_improvement_of_uniform_polarization_gainSup_lower_pos_lt_pi`; direction extractor `exists_finRealSpherePolarization_objective_improvement_of_gainSup_lower` | `PptFactorization/FinRealSphereIsoperimetryProof.lean:1780,1745` | foundational axioms only |
| derive uniform actual-polarization improvement from auto-height Lemma 4.3 data | average-form adapter `uniform_polarization_gap_improvement_of_lemma43_autoHeightBands_gainSup_equal_mass_pos_lt_pi`; direct-data adapter `uniform_polarization_gap_improvement_of_lemma43_autoHeightBands_directGainSup_equal_mass_pos_lt_pi`; gain-supremum suppliers `uniform_polarization_gainSup_lower_of_lemma43_autoHeightBands_gainSup_equal_mass_pos_lt_pi` and `uniform_polarization_gainSup_lower_of_lemma43_autoHeightBands_directGainSup_equal_mass_pos_lt_pi` | `PptFactorization/FinRealSphereIsoperimetryProof.lean:2730,2862,2655,2795` | foundational axioms only |
| wire uniform gain-supremum proof-core into cone-Gaussian endpoint | cap-comparison adapter `sphere_halfMeasure_hemisphereComparisonGeTwo_of_uniform_polarization_gainSup_lower_pos_lt_pi`; cone-Gaussian endpoint `upper_eventual_from_concrete_sequences_of_uniformPolarizationGainSup_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm` | `PptFactorization/FinRealSphereIsoperimetryProof.lean:1916`; `PptFactorization/AppendixBUpperBoundClosure.lean:12702` | foundational axioms only |
| wire uniform polarization-improvement proof-core into surface-cap below-half endpoint | cap-comparison adapter `sphere_halfMeasure_hemisphereComparisonGeTwo_of_uniform_polarization_gap_improvement_pos_lt_pi`; surface-cap endpoint `upper_eventual_from_concrete_sequences_of_uniformPolarizationGap_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`; full-isoperimetry package `fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleClosedHalfspaceCosinePowerTailBelowHalf` | `PptFactorization/FinRealSphereIsoperimetryProof.lean:1702`; `PptFactorization/AppendixBUpperBoundClosure.lean:11062` | foundational axioms only; Challenge before: the actual-polarization strict proof core exposed cap-cone, coordinate, and cone-Gaussian tail forms but not the normalized surface-cap below-half tail. Challenge after: the proof core has all four named tail forms without strengthening the theorem hypotheses. |
| wire uniform polarization-improvement proof-core into cone-Gaussian endpoint | cap-comparison adapter `sphere_halfMeasure_hemisphereComparisonGeTwo_of_uniform_polarization_gap_improvement_pos_lt_pi`; cone-Gaussian endpoint `upper_eventual_from_concrete_sequences_of_uniformPolarizationGap_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm` | `PptFactorization/FinRealSphereIsoperimetryProof.lean:1702`; `PptFactorization/AppendixBUpperBoundClosure.lean:12756` | foundational axioms only; Challenge before: the live atlas row still pointed to a broader auto-height wrapper. Challenge after: the canonical upper row exposes `hUniformGap` plus the prioritized cone-Gaussian tail directly. |
| wire average-form auto-height data through the strict proof-core cone-Gaussian endpoint | strict source adapter `uniform_polarization_gap_improvement_of_lemma43_autoHeightBands_gainSup_equal_mass_pos_lt_pi`; endpoint `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsStrictGap_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm` | `PptFactorization/FinRealSphereIsoperimetryProof.lean:2730`; `PptFactorization/AppendixBUpperBoundClosure.lean:12813` | foundational axioms only; Challenge before: average-form auto-height data reached actual directions only through the unnamed generic gain-supremum chain. Challenge after: the strict-improvement source route is named and theorem-facing. |
| wire average-form auto-height data through the strict proof-core below-half cap-cone endpoint | strict source adapter `uniform_polarization_gap_improvement_of_lemma43_autoHeightBands_gainSup_equal_mass_pos_lt_pi`; endpoint `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsStrictGap_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`; tail adapter to the cone-Gaussian package `sphere_northPoleCapConeGaussianTailLargeExponent_of_cosinePowerTailBelowHalf` | `PptFactorization/FinRealSphereIsoperimetryProof.lean:2730`; `PptFactorization/AppendixBUpperBoundClosure.lean:12847`; `PptFactorization/SphericalPolarizationPushforwardTransport.lean:740` | foundational axioms only; Challenge before: the source-explicit strict endpoint still named the cone-Gaussian package as its tail leaf. Challenge after: the same strict source route exposes the smaller below-half ambient cap-cone power-law tail, from which cone-Gaussian follows by an audited adapter. |
| wire average-form auto-height data through the strict proof-core surface-cap endpoint | strict source adapter `uniform_polarization_gap_improvement_of_lemma43_autoHeightBands_gainSup_equal_mass_pos_lt_pi`; proof-core endpoint `upper_eventual_from_concrete_sequences_of_uniformPolarizationGap_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`; source endpoint `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsStrictGap_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm` | `PptFactorization/FinRealSphereIsoperimetryProof.lean:2730`; `PptFactorization/AppendixBUpperBoundClosure.lean:11062,12882` | foundational axioms only; Challenge before: the average-form strict source route lacked the normalized surface-cap below-half tail form. Challenge after: it factors through the reusable proof-core surface endpoint, leaving only the average-form Lemma 4.3 source and the surface-tail leaf visible. |
| wire uniform polarization-improvement proof-core into the coordinate below-half endpoint | cap-comparison adapter `sphere_halfMeasure_hemisphereComparisonGeTwo_of_uniform_polarization_gap_improvement_pos_lt_pi`; endpoint `upper_eventual_from_concrete_sequences_of_uniformPolarizationGap_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`; adapters `sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf_of_coordinateCosinePowerTailBelowHalf` and `sphere_northPoleCapConeCosinePowerTailBelowHalf_of_closedHalfspaceCosinePowerTailBelowHalf` | `PptFactorization/FinRealSphereIsoperimetryProof.lean:1702`; `PptFactorization/AppendixBUpperBoundClosure.lean:12913`; `PptFactorization/SphericalPolarizationPushforwardTransport.lean:522,843` | foundational axioms only; Challenge before: only the cone below-half proof-core endpoint exposed actual uniform polarization improvement. Challenge after: the proof core also exposes the one-dimensional coordinate-law below-half tail directly. |
| wire average-form auto-height data through the strict proof-core coordinate-tail endpoint | strict source adapter `uniform_polarization_gap_improvement_of_lemma43_autoHeightBands_gainSup_equal_mass_pos_lt_pi`; proof-core endpoint `upper_eventual_from_concrete_sequences_of_uniformPolarizationGap_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`; source endpoint `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsStrictGap_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm` | `PptFactorization/FinRealSphereIsoperimetryProof.lean:2730`; `PptFactorization/AppendixBUpperBoundClosure.lean:12913,12970` | foundational axioms only; Challenge before: the strict source route still performed the coordinate/surface/cone transport inline. Challenge after: the same route factors through the reusable proof-core coordinate endpoint, leaving only the average-form Lemma 4.3 source and the coordinate below-half tail as theorem-strength leaves. |
| wire direct block-to-`sSup` auto-height data through the strict proof-core cone-Gaussian endpoint | strict source adapter `uniform_polarization_gap_improvement_of_lemma43_autoHeightBands_directGainSup_equal_mass_pos_lt_pi`; proof-core endpoint `upper_eventual_from_concrete_sequences_of_uniformPolarizationGap_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`; source endpoint `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectStrictGap_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm` | `PptFactorization/FinRealSphereIsoperimetryProof.lean:2862`; `PptFactorization/AppendixBUpperBoundClosure.lean:12756,13004` | foundational axioms only; Challenge before: direct block-to-`sSup` data had no source-explicit cone-Gaussian strict endpoint. Challenge after: the direct source route factors through the reusable uniform strict cone-Gaussian endpoint, leaving the direct Lemma 4.3 source and the cone-Gaussian tail as the visible leaves. |
| wire direct block-to-`sSup` auto-height data through the strict proof-core below-half cap-cone endpoint | strict source adapter `uniform_polarization_gap_improvement_of_lemma43_autoHeightBands_directGainSup_equal_mass_pos_lt_pi`; proof-core endpoint `upper_eventual_from_concrete_sequences_of_uniformPolarizationGap_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`; source endpoint `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectStrictGap_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`; tail adapter to the cone-Gaussian package `sphere_northPoleCapConeGaussianTailLargeExponent_of_cosinePowerTailBelowHalf` | `PptFactorization/FinRealSphereIsoperimetryProof.lean:2862`; `PptFactorization/AppendixBUpperBoundClosure.lean:11120,13038`; `PptFactorization/SphericalPolarizationPushforwardTransport.lean:740` | foundational axioms only; Challenge before: direct block-to-`sSup` strict data exposed the cone-Gaussian package or coordinate tail, but not the intermediate cap-cone below-half tail. Challenge after: the direct source route exposes the smaller below-half ambient cap-cone power-law tail, from which cone-Gaussian follows by an audited adapter. |
| wire separate-tau height-band supplier into cone-Gaussian endpoint | uniform supplier `uniform_polarization_gainSup_lower_of_lemma43_heightBands_separateTau_gainSup_equal_mass_pos_lt_pi`; cone-Gaussian endpoint `upper_eventual_from_concrete_sequences_of_lemma43SeparateTau_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm` | `PptFactorization/FinRealSphereIsoperimetryProof.lean:3523`; `PptFactorization/AppendixBUpperBoundClosure.lean:13107` | foundational axioms only |
| wire rect-tau height-band supplier into coordinate and cone-Gaussian endpoints | uniform supplier `uniform_polarization_gainSup_lower_of_lemma43_heightBands_rectTau_gainSup_equal_mass_pos_lt_pi`; coordinate endpoint `upper_eventual_from_concrete_sequences_of_lemma43HeightBandsRectTau_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`; cone-Gaussian endpoint `upper_eventual_from_concrete_sequences_of_lemma43HeightBandsRectTau_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm` | `PptFactorization/FinRealSphereIsoperimetryProof.lean:3398`; `PptFactorization/AppendixBUpperBoundClosure.lean:12043,13207` | foundational axioms only |
| package average-form auto-height data plus coordinate below-half tail as full isoperimetry | full-isoperimetry supplier `fullSphericalIsoperimetry_of_lemma43AutoHeightBands_northPoleCoordinateCosinePowerTailBelowHalf`; active average-form coordinate endpoint `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBands_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm` | `PptFactorization/AppendixBUpperBoundClosure.lean:10717,10733` | foundational axioms only; Challenge before: the average-form below-half endpoint detoured through the full coordinate-tail route. Challenge after: it packages average-form cap comparison plus the below-half coordinate tail directly. |
| package average-form auto-height data plus cone-Gaussian tail as full isoperimetry | full-isoperimetry supplier `fullSphericalIsoperimetry_of_lemma43AutoHeightBands_northPoleCapConeGaussianTailLargeExponent`; active cone-Gaussian endpoint `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBands_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm` | `PptFactorization/AppendixBUpperBoundClosure.lean:10733,10782` | foundational axioms only; Challenge before: the average-form sharp row exposed the coordinate below-half tail. Challenge after: it exposes the prioritized ambient cone-Gaussian tail directly. |
| derive direct auto-height supplier from average-form auto-height data | transformer `lemma43_autoHeightBands_directGainSup_equal_mass_of_autoHeightBands_gainSup_equal_mass_pos_lt_pi`; compatibility direct coordinate endpoint `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm` | `PptFactorization/FinRealSphereIsoperimetryProof.lean:2576`; `PptFactorization/AppendixBUpperBoundClosure.lean:11193` | foundational axioms only; Challenge before: direct auto-height branch required block-to-`sSup` data directly. Challenge after: average-form block data plus `avg ≤ sSup` supplies the direct branch by scalar transitivity. |
| derive fixed-height direct-gain supplier from average-form height-band data | transformer `lemma43_heightBands_directGainSup_equal_mass_of_heightBands_gainSup_equal_mass_pos_lt_pi`; average-form coordinate endpoint `upper_eventual_from_concrete_sequences_of_lemma43HeightBandsGainSup_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm` | `PptFactorization/FinRealSphereIsoperimetryProof.lean:3118`; `PptFactorization/AppendixBUpperBoundClosure.lean:12438` | foundational axioms only |
| wire fixed-height direct-gain supplier into sharp cone-Gaussian endpoint | fixed-height direct cone-Gaussian endpoint `upper_eventual_from_concrete_sequences_of_lemma43HeightBandsDirectGainSup_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`; cap comparison supplier `sphere_halfMeasure_hemisphereComparisonGeTwo_of_lemma43_heightBands_directGainSup_equal_mass_pos_lt_pi` | `PptFactorization/AppendixBUpperBoundClosure.lean:13307`; `PptFactorization/FinRealSphereIsoperimetryProof.lean:3104` | foundational axioms only |
| reduce fixed-height direct-gain cone tail to below-half cap-cone power law | fixed-height cap-cone below-half endpoint `upper_eventual_from_concrete_sequences_of_lemma43HeightBandsDirectGainSup_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`; tail adapter `sphere_northPoleCapConeGaussianTailLargeExponent_of_cosinePowerTailBelowHalf` | `PptFactorization/AppendixBUpperBoundClosure.lean:13382`; `PptFactorization/SphericalPolarizationPushforwardTransport.lean:740` | foundational axioms only |
| package fixed-height direct-gain data plus coordinate below-half tail as full isoperimetry | full-isoperimetry supplier `fullSphericalIsoperimetry_of_lemma43HeightBandsDirectGainSup_northPoleCoordinateCosinePowerTailBelowHalf`; fixed-height coordinate below-half endpoint `upper_eventual_from_concrete_sequences_of_lemma43HeightBandsDirectGainSup_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm` | `PptFactorization/AppendixBUpperBoundClosure.lean:12300,12362` | foundational axioms only |
| package below-half tail as cone and hemisphere Gaussian tails | direct cone adapter `sphere_northPoleCapConeGaussianTailLargeExponent_of_cosinePowerTailBelowHalf`; direct surface adapter `sphere_northPoleCapConeGaussianTailLargeExponent_of_closedHalfspaceCosinePowerTailBelowHalf`; coordinate-chain adapter `sphere_northPoleCapConeGaussianTailLargeExponent_of_northPoleCoordinateCosinePowerTailBelowHalf`; surface-to-hemisphere package `sphere_hemisphereGaussianTail_of_northPoleClosedHalfspaceGaussianTailLargeExponent`; cone-to-hemisphere package `sphere_hemisphereGaussianTail_of_northPoleCapConeGaussianTailLargeExponent`; coordinate hemisphere package `sphere_hemisphereGaussianTail_of_northPoleCoordinateCosinePowerTailBelowHalf`; lower-bound local-expansion cone endpoint `upper_eventual_from_concrete_sequences_of_northPoleCapConeCosinePowerTailBelowHalf_oneSidedLowerBound_localExpansionMoment_canonicalMixedWords` | `PptFactorization/SphericalPolarizationPushforwardTransport.lean:740,853`; `PptFactorization/AppendixBUpperBoundClosure.lean:10182,10197,10216,10232,10412` | foundational axioms only |
| package cap comparison plus tail as full isoperimetry | `fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleCoordinateCosinePowerTailBelowHalf`, surface-cap power variant `fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleClosedHalfspaceCosinePowerTailBelowHalf`, cone-volume power variant `fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleCapConeCosinePowerTailBelowHalf`, surface-Gaussian variant `fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleClosedHalfspaceGaussianTailLargeExponent`, and cone-Gaussian variant `fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleCapConeGaussianTailLargeExponent` | `PptFactorization/AppendixBUpperBoundClosure.lean:10247,10261,10274,10289,10302` | foundational axioms only |
| package direct auto-height Lemma 4.3 data plus below-half surface tail as full isoperimetry | `fullSphericalIsoperimetry_of_lemma43AutoHeightBandsDirectGainSup_northPoleClosedHalfspaceCosinePowerTailBelowHalf`; sharp endpoint `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm` | `PptFactorization/AppendixBUpperBoundClosure.lean:10752,11213` | foundational axioms only |
| package direct auto-height Lemma 4.3 data plus coordinate/surface/cone Gaussian tails as full isoperimetry | surface-Gaussian supplier `fullSphericalIsoperimetry_of_lemma43AutoHeightBandsDirectGainSup_northPoleClosedHalfspaceGaussianTailLargeExponent`; coordinate-Gaussian supplier `fullSphericalIsoperimetry_of_lemma43AutoHeightBandsDirectGainSup_northPoleCoordinateGaussianTailLargeExponent`; cone-Gaussian supplier `fullSphericalIsoperimetry_of_lemma43AutoHeightBandsDirectGainSup_northPoleCapConeGaussianTailLargeExponent`, factored through the coordinate-Gaussian supplier via `sphere_coordinateGaussianTailInteriorLargeExponentNorthPole_of_coneTail`; surface-Gaussian sharp endpoint `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleClosedHalfspaceGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`; coordinate-Gaussian sharp endpoint `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleCoordinateGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`; cone-Gaussian sharp endpoint `upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm` | `PptFactorization/AppendixBUpperBoundClosure.lean:10770,10786,10801,11335,11366,11398` | foundational axioms only; Challenge before: direct cone-Gaussian endpoint had no one-dimensional north-pole coordinate Gaussian endpoint to factor through. Challenge after: coordinate-Gaussian endpoint `11366` feeds the cone-Gaussian endpoint `11398` via the cone-to-coordinate Gaussian tail adapter. |
| split cap comparison from tail on sharp upper branch | coordinate endpoint `upper_eventual_from_concrete_sequences_of_hemisphereComparison_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`, surface-cap endpoint `upper_eventual_from_concrete_sequences_of_hemisphereComparison_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`, cone-volume endpoint `upper_eventual_from_concrete_sequences_of_hemisphereComparison_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`, surface-Gaussian endpoint `upper_eventual_from_concrete_sequences_of_hemisphereComparison_northPoleClosedHalfspaceGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm`, cone-Gaussian endpoint `upper_eventual_from_concrete_sequences_of_hemisphereComparison_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm` | `PptFactorization/AppendixBUpperBoundClosure.lean:12610,12577,12545,12639,12670` | foundational axioms only; Challenge before: modular branch had no endpoint consuming cap comparison plus the normalized surface-Gaussian tail directly. Challenge after: surface-Gaussian endpoint `12639` feeds the cone-Gaussian endpoint `12670` via `sphere_northPoleClosedHalfspaceGaussianTailLargeExponent_of_coneTail`. |

## What Is Intentionally Omitted

- The long list of compatibility wrappers between lines `9000-11000` of
  `AppendixBUpperBoundClosure.lean`. They are real theorems, but they are not
  separate active frontier unless a future campaign explicitly chooses one of
  them as canonical.
- Old Aristotle draft or handoff files that still contain `sorry`. They are not
  authorized supplier leads for this atlas.
- Repeated `#print axioms` dumps for every helper. This atlas records audit
  status once per role.
- Raw search transcripts, file counts, and historical failed searches.

## Next Adapter

1. No missing strict-improvement adapter remains for the average-form
   auto-height route: the next theorem-strength work is either to prove the
   average-form Lemma 4.3 geometric supplier via the closed
   reflection/Jacobian, push-forward, trimming, and strict-improvement
   machinery, or to close the north-pole cone-Gaussian tail supplier below.
2. Prove the north-pole large-exponent tail for `2 ≤ n`, `0 < r < π/2`,
   and `log 2 < ((n - 1) r^2) / 2`.  The direct-gain and modular
   cap-comparison upper routes can now consume
   the cone-Gaussian package `sphere_northPoleCapConeGaussianTailLargeExponent`
   directly; the most elementary tail target remains the nontrivial below-half
   north-pole cap package, preferably in the coordinate-law form
   `sphere_northPoleCoordinateCosinePowerTailBelowHalf`, bounding the
   one-dimensional north-pole coordinate tail at threshold `sin r` by
   `cos(r)^(n-1)` under the extra hypothesis
   `cos(r)^(n-1) < 1 / 2`.  The normalized surface form
   `sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf` is equivalent by
   the checked coordinate push-forward adapters and feeds the ambient
   cone-volume below-half form and the large-exponent Gaussian cone tail
   directly through
   `sphere_northPoleCapConeCosinePowerTailBelowHalf_of_closedHalfspaceCosinePowerTailBelowHalf`
   and
   `sphere_northPoleCapConeGaussianTailLargeExponent_of_closedHalfspaceCosinePowerTailBelowHalf`.
   The ambient cone-volume
   formulation `sphere_northPoleCapConeCosinePowerTailBelowHalf` supplies the
   surface form by
   `sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf_of_capConeCosinePowerTailBelowHalf`.
   It also supplies the large-exponent Gaussian cone tail directly through
   `sphere_northPoleCapConeGaussianTailLargeExponent_of_cosinePowerTailBelowHalf`,
   since the large-exponent hypothesis implies the below-half condition.
   The checked adapter
   `sphere_northPoleCoordinateCosinePowerTail_of_belowHalf` adds the
   complementary range by antipodal half-tail symmetry, and
   `sphere_northPoleClosedHalfspaceCosinePowerTail_of_coordinateCosinePowerTail`
   turns the resulting full coordinate law into the normalized closed-halfspace
   cap power law.  The checked adapter
   `sphere_northPoleCapConeCosinePowerTail_of_closedHalfspaceCosinePowerTail`
   turns this into the ambient cap-cone power law by the surface/cone formula.
   The checked adapter
   `sphere_northPoleCapConeGaussianTailLargeExponent_of_northPoleCoordinateCosinePowerTailBelowHalf`
   packages this whole chain directly as the large-exponent Gaussian
   cone-volume package; it then feeds the normalized closed-halfspace package by
   `sphere_northPoleClosedHalfspaceGaussianTailLargeExponent_of_coneTail` and
   then the coordinate-law package by
   `sphere_coordinateGaussianTailInteriorLargeExponentNorthPole_of_closedHalfspaceTail`.
   The older adapter
   `sphere_northPoleCapConeGaussianTailLargeExponent_of_coordinateTail` remains
   available for routes that already have the large-exponent coordinate package.
   The `n = 1` case, arbitrary-pole transport, the closed endpoint cases, and
   the small-exponent strict-interior range are already supplied by
   `sphere_coordinateGaussianTailInterior_of_geTwo`,
   `sphere_coordinateGaussianTailInteriorLargeExponent_of_northPole`,
   `sphere_coordinateGaussianTail_of_interior`, and
   `sphere_coordinateGaussianTailInteriorGeTwo_of_largeExponent`.
3. Wire lower-side target-prob positivity to upper one-sided witness only after
   deleted-column / `Fin (R.sample d)` mean transport is explicit.

## Atlas Before

- 2026-05-25 18:51 CEST: the fixed-height direct-gain coordinate branch still
  routed the coordinate below-half tail through the normalized surface-cap
  endpoint before reaching `FullSphericalIsoperimetry`.
- The branch had no named full-isoperimetry supplier matching exactly the
  fixed-height direct block-to-`sSup` data plus the coordinate below-half tail.

## Atlas After

- The new supplier
  `AppendixB.fullSphericalIsoperimetry_of_lemma43HeightBandsDirectGainSup_northPoleCoordinateCosinePowerTailBelowHalf`
  at `PptFactorization/AppendixBUpperBoundClosure.lean:12300` packages
  fixed-height direct Lemma 4.3 data plus the coordinate below-half tail.
- The fixed-height coordinate endpoint at
  `PptFactorization/AppendixBUpperBoundClosure.lean:12362` now factors through
  that package directly.  The canonical sharp upper branch remains the
  auto-height coordinate endpoint at line `11193`; the live theorem-strength
  leaves remain the direct auto-height Lemma 4.3 supplier and the north-pole
  coordinate below-half cap tail.

## Aubrun Alternative Route

- `PptFactorization/AubrunAlternative.lean`
  starts the dedicated module for the moment-Hankel proof route to Aubrun's
  PPT threshold.  It intentionally contains deterministic adapters only; the
  quantitative probability estimates remain explicit frontier inputs.
- `AubrunAlternative.shiftedHankel_nonneg_of_ppt`
  (`PptFactorization/AubrunAlternative.lean:56`) names the odd-Hankel
  nonnegativity consequence of the finite `p_{2m+1}` PPT criterion.
- `AubrunAlternative.not_ppt_of_shiftedHankel_det_neg`
  (`PptFactorization/AubrunAlternative.lean:65`) is the paper-facing
  lower-side finite certificate: a negative shifted odd Hankel determinant
  rules out the corresponding finite PPT moment test.
- `AubrunAlternative.one_le_centered_even_power_of_neg`
  (`PptFactorization/AubrunAlternative.lean:20`) is the scalar observation
  behind the fixed-moment `λ > 4` route: a negative spectral value contributes
  at least one unit to every even centered moment.
- `AubrunAlternative.centered_even_power_nonneg`
  (`PptFactorization/AubrunAlternative.lean:28`) supplies nonnegativity of
  even centered powers for the finite-sum comparison.
- `AubrunAlternative.neg_count_le_centered_even_moment`
  (`PptFactorization/AubrunAlternative.lean:40`) bounds the count of negative
  values in any finite real spectrum by the corresponding centered even
  moment.  This is the deterministic bridge from fixed centered moments to
  almost-positivity above `λ = 4`; full PPT still needs a growing-moment or
  spectral-edge input.
- `AubrunAlternative.neg_count_average_le_centered_even_moment_average`
  (`PptFactorization/AubrunAlternative.lean:59`) is the empirical-measure
  version: the normalized fraction of negative values is bounded by the
  normalized centered even moment.
- `AubrunAlternative.neg_count_average_le_of_centered_even_moment_average_le`
  (`PptFactorization/AubrunAlternative.lean:70`) is the event-shaped count
  adapter: a normalized centered-moment threshold implies the same threshold
  for the normalized negative count.
- `AubrunAlternative.neg_part_le_centered_even_power_succ`
  (`PptFactorization/AubrunAlternative.lean:84`) is the pointwise mass
  analogue: the negative part `max 0 (-x)` is bounded by every positive even
  centered moment `(x - 1)^(2*(m+1))`.
- `AubrunAlternative.neg_mass_le_centered_even_moment_succ`
  (`PptFactorization/AubrunAlternative.lean:109`) sums the pointwise mass bound
  over any finite real spectrum.  This supplies the trace-mass version of
  fixed-moment almost-positivity.
- `AubrunAlternative.neg_mass_average_le_centered_even_moment_average_succ`
  (`PptFactorization/AubrunAlternative.lean:123`) is the empirical
  trace-mass version: the normalized average of the negative part is bounded
  by the normalized positive even centered moment.
- `AubrunAlternative.neg_mass_average_le_of_centered_even_moment_average_le_succ`
  (`PptFactorization/AubrunAlternative.lean:133`) is the event-shaped
  trace-mass adapter: a normalized positive even centered-moment threshold
  implies the same threshold for normalized negative trace mass.
- `AubrunAlternative.catalan_le_four_pow_real`
  (`PptFactorization/AubrunAlternative.lean:142`) records the scalar Catalan
  growth bound `(catalan m : ℝ) ≤ 4^m`.
- `AubrunAlternative.exists_catalan_div_pow_lt_of_four_lt`
  (`PptFactorization/AubrunAlternative.lean:152`) closes the fixed-moment
  scalar choice: for every `λ > 4` and `η > 0`, some fixed `m` satisfies
  `(catalan m : ℝ) / λ^m < η`.
- `AubrunAlternative.exists_neg_count_average_le_of_centered_even_moment_average_le_catalan_add`
  (`PptFactorization/AubrunAlternative.lean:178`) packages the fixed-moment
  count route with the canonical half-tolerance split: choose `m` so the
  Catalan centered-semicircle term is below `η / 2`, then a finite spectrum
  whose normalized centered moment is bounded by that Catalan term plus
  `η / 2` has negative-count fraction at most `η`.
- `AubrunAlternative.exists_neg_mass_average_le_of_centered_even_moment_average_le_catalan_add_succ`
  (`PptFactorization/AubrunAlternative.lean:200`) packages the trace-mass
  fixed-moment route with the same half-tolerance split, using the positive
  even order `2 * (m + 1)`: a normalized centered-moment bound by
  `(catalan (m + 1) : ℝ) / λ^(m + 1) + η / 2` implies normalized negative
  trace mass at most `η`.
- `AubrunAlternative.exists_neg_count_and_mass_average_le_of_centered_even_moment_average_le_catalan_add_succ`
  (`PptFactorization/AubrunAlternative.lean:242`) is the joint deterministic
  fixed-moment bulk package: the same positive even centered moment and
  Catalan-plus-`η / 2` budget simultaneously bound the negative-count fraction
  and the normalized negative trace mass by `η`.
- `AubrunAlternative.exists_centered_moment_threshold_lt_of_neg_count_or_mass_gt`
  (`PptFactorization/AubrunAlternative.lean:292`) is the probability-ready
  bad-event contrapositive: if either the negative-count fraction or the
  normalized negative trace mass exceeds `η`, then the normalized centered
  moment exceeds the Catalan-plus-half-tolerance threshold.
- `AubrunAlternative.exists_bad_event_subset_centered_moment_threshold_event`
  (`PptFactorization/AubrunAlternative.lean:322`) is the set-valued
  probability-facing form: for any random finite spectrum `F : Ω → ι → ℝ`, the
  event where either almost-positivity control fails is contained in the
  centered-moment threshold event.
- `AubrunAlternative.all_nonneg_of_centered_even_moment_lt_one`
  (`PptFactorization/AubrunAlternative.lean:345`) is the deterministic
  high-moment positivity bridge: an unnormalised centered even moment strictly
  below `1` rules out every negative spectral value.  This is the adapter used
  by a future growing-moment trace bound to prove PPT without first proving a
  full operator-norm edge theorem.
- `AubrunAlternative.exists_negative_subset_centered_even_moment_ge_one_event`
  (`PptFactorization/AubrunAlternative.lean:371`) is the set-valued
  high-moment PPT shortcut: for any random finite spectrum, the event that some
  spectral value is negative is contained in the event that the unnormalised
  centered even moment is at least `1`.
- `AubrunAlternative.negative_event_measure_le_of_centered_event_measure_le`
  (`PptFactorization/AubrunAlternative.lean:390`) is the abstract measure
  wrapper for the high-moment route: any measure bound on the unnormalised
  centered-moment event transfers directly to the negative-spectrum event.
- `AubrunAlternative.negative_event_measure_le_lintegral_centered_even_moment`
  (`PptFactorization/AubrunAlternative.lean:405`) is the abstract Markov
  wrapper: the negative-spectrum event is bounded by the `lintegral` of the
  unnormalised centered even spectral moment, assuming the lifted moment is
  a.e. measurable.
- `AubrunAlternative.negative_event_measure_le_of_lintegral_centered_even_moment_le`
  (`PptFactorization/AubrunAlternative.lean:424`) is the direct
  expectation-bound interface: a `lintegral` bound by `δ` transfers to the
  negative-spectrum event with the same bound.
- `AubrunAlternative.negative_event_measure_le_of_lintegral_bound_ofReal`
  (`PptFactorization/AubrunAlternative.lean:440`) is the real-valued
  finite-dimensional expectation-bound interface: a `lintegral` bound by
  `ENNReal.ofReal δ` transfers to the negative-spectrum event with the same
  explicit bound.
- `AubrunAlternative.negative_event_measure_le_of_lintegral_bound_log_quadratic_rpow_log`
  (`PptFactorization/AubrunAlternative.lean:478`) is the explicit
  finite-dimensional paper-shape probability bound: a lifted
  `C * (log d)^α * d^2 * q^(c log d)` moment bound gives the same upper bound
  on the negative-spectrum event at that dimension.
- `AubrunAlternative.eventually_negative_event_measure_le_of_eventually_lintegral_bound_ofReal`
  (`PptFactorization/AubrunAlternative.lean:457`) is the eventual
  finite-dimensional real-rate probability bound: an eventual `lintegral`
  bound by `ENNReal.ofReal (δ_d)` gives the same negative-spectrum event bound
  eventually.
- `AubrunAlternative.eventually_negative_event_measure_le_of_eventually_lintegral_bound_log_quadratic_rpow_log`
  (`PptFactorization/AubrunAlternative.lean:501`) is the eventual
  finite-dimensional paper-shape probability bound: an eventual lifted
  `C * (log d)^α * d^2 * q^(c log d)` moment bound gives the same event
  probability bound eventually.
- `AubrunAlternative.eventually_negative_event_measure_le_of_eventually_lintegral_bound_log_quadratic_rpow_log_dependent`
  (`PptFactorization/AubrunAlternative.lean:526`) is the dependent-index
  variant of the same finite-rate adapter.  This is the right scalar
  interface for concrete spectra whose index type varies with dimension, such
  as `Fin d × Fin d`.
- `AubrunAlternative.tendsto_negative_event_measure_zero_of_lintegral_bound`
  (`PptFactorization/AubrunAlternative.lean:554`) is the sequence-level
  controlled growing-moment interface: `lintegral` bounds by a vanishing
  `δ_d` imply that the negative-spectrum event probabilities tend to zero.
- `AubrunAlternative.tendsto_negative_event_measure_zero_of_lintegral_bound_ofReal`
  (`PptFactorization/AubrunAlternative.lean:579`) is the real-rate version:
  `lintegral` bounds by `ENNReal.ofReal (δ_d)` plus real convergence
  `δ_d → 0` imply that the negative-spectrum event probabilities tend to zero.
- `AubrunAlternative.tendsto_negative_event_measure_zero_of_eventually_lintegral_bound_ofReal`
  (`PptFactorization/AubrunAlternative.lean:600`) is the eventual real-rate
  version: the `lintegral` bound by `ENNReal.ofReal (δ_d)` only has to hold
  for all sufficiently large dimensions.
- `AubrunAlternative.natCast_rpow_tendsto_zero_of_neg`
  (`PptFactorization/AubrunAlternative.lean:625`) and
  `AubrunAlternative.const_mul_natCast_rpow_tendsto_zero_of_neg`
  (`PptFactorization/AubrunAlternative.lean:633`) are scalar decay helpers for
  negative powers of the dimension parameter.
- `AubrunAlternative.tendsto_negative_event_measure_zero_of_lintegral_bound_const_mul_rpow_neg`
  (`PptFactorization/AubrunAlternative.lean:642`) is the polynomial-rate
  controlled growing-moment interface: a lifted `C * d^{-β}` bound with
  `β > 0` implies that the negative-spectrum event probabilities tend to zero.
- `AubrunAlternative.rpow_const_mul_log_eq_rpow_log_mul`
  (`PptFactorization/AubrunAlternative.lean:659`) and
  `AubrunAlternative.quadratic_rpow_const_mul_log_eq_rpow`
  (`PptFactorization/AubrunAlternative.lean:667`) are the scalar logarithmic
  conversion lemmas behind the rate
  `d^2 q^(c log d) = d^(2 + c log q)` for positive `q` and `d`.
- `AubrunAlternative.log_rpow_mul_natCast_rpow_neg_tendsto_zero`
  (`PptFactorization/AubrunAlternative.lean:674`) and
  `AubrunAlternative.const_mul_log_rpow_mul_natCast_rpow_neg_tendsto_zero`
  (`PptFactorization/AubrunAlternative.lean:703`) absorb a real logarithmic
  power into any positive polynomial decay.
- `AubrunAlternative.tendsto_negative_event_measure_zero_of_lintegral_bound_log_rpow_mul_rpow_neg`
  (`PptFactorization/AubrunAlternative.lean:716`) is the log-polynomial-rate
  controlled growing-moment interface: a lifted
  `C * (log d)^α * d^{-β}` bound with `β > 0` implies that the
  negative-spectrum event probabilities tend to zero.
- `AubrunAlternative.const_mul_log_rpow_mul_quadratic_rpow_const_mul_log_tendsto_zero`
  (`PptFactorization/AubrunAlternative.lean:735`) is the direct scalar
  paper-shape rate: if `q > 0` and `2 + c log q < 0`, then
  `C * (log d)^α * d^2 * q^(c log d)` tends to zero.
- `AubrunAlternative.two_add_mul_log_neg_of_two_lt_mul_log_inv`
  (`PptFactorization/AubrunAlternative.lean:753`) is the readable threshold
  adapter: `2 < c * log(1/q)` implies `2 + c * log q < 0`.
- `AubrunAlternative.exists_two_lt_mul_log_inv_of_pos_lt_one`
  (`PptFactorization/AubrunAlternative.lean:761`) proves that every
  `0 < q < 1` admits some positive logarithmic-order constant `c` with
  `2 < c * log(1/q)`.
- `AubrunAlternative.exists_log_order_constants_of_four_lt`
  (`PptFactorization/AubrunAlternative.lean:776`) packages the `λ > 4`
  scalar choice: it provides an edge slack `eps`, ratio
  `q = (4 + eps) / λ` with `0 < q < 1`, and a positive logarithmic order
  constant `c` with `2 < c * log(1/q)`.
- `AubrunAlternative.const_mul_log_rpow_mul_quadratic_rpow_const_mul_log_tendsto_zero_of_two_lt_mul_log_inv`
  (`PptFactorization/AubrunAlternative.lean:802`) is the scalar paper-shape
  rate with the readable threshold `c log(1/q) > 2`.
- `AubrunAlternative.tendsto_negative_event_measure_zero_of_lintegral_bound_log_quadratic_rpow_log`
  (`PptFactorization/AubrunAlternative.lean:816`) is the paper-shape
  controlled growing-moment interface: a lifted
  `C * (log d)^α * d^2 * q^(c log d)` bound with `2 + c log q < 0` implies
  that the negative-spectrum event probabilities tend to zero.
- `AubrunAlternative.tendsto_negative_event_measure_zero_of_eventually_lintegral_bound_log_quadratic_rpow_log`
  (`PptFactorization/AubrunAlternative.lean:837`) is the eventual
  paper-shape interface: the same lifted bound only has to hold eventually in
  the dimension parameter.
- `AubrunAlternative.tendsto_negative_event_measure_zero_of_lintegral_bound_log_quadratic_rpow_log_of_two_lt_mul_log_inv`
  (`PptFactorization/AubrunAlternative.lean:856`) is the same paper-shape
  controlled growing-moment interface with the readable threshold
  `c log(1/q) > 2`.
- `AubrunAlternative.tendsto_negative_event_measure_zero_of_eventually_lintegral_bound_log_quadratic_rpow_log_of_two_lt_mul_log_inv`
  (`PptFactorization/AubrunAlternative.lean:873`) is the eventual
  paper-shape interface with the readable threshold `c log(1/q) > 2`.
- `AubrunAlternative.exists_log_order_constants_and_tendsto_negative_event_measure_zero_of_four_lt`
  (`PptFactorization/AubrunAlternative.lean:893`) is the conditional
  `λ > 4` endpoint for the controlled growing-moment route: Lean chooses
  admissible `eps`, `q`, and `c`, and a future paper-shape moment bound for
  those constants implies that the negative-spectrum event probabilities tend
  to zero.
- `AubrunAlternative.exists_log_order_constants_and_tendsto_negative_event_measure_zero_of_four_lt_eventually`
  (`PptFactorization/AubrunAlternative.lean:920`) is the preferred conditional
  `λ > 4` endpoint for future random-matrix suppliers: the paper-shape moment
  bound is required only eventually in `d`.
- `AubrunAlternative.exists_log_order_constants_and_eventually_negative_event_measure_le_of_four_lt`
  (`PptFactorization/AubrunAlternative.lean:948`) is the article-facing
  eventual finite-rate `λ > 4` package: Lean chooses admissible
  `eps`, `q`, and `c`, and an eventual paper-shape moment bound gives the same
  eventual paper-shape probability bound for the negative-spectrum event.
- `AubrunAlternative.tendsto_negative_event_measure_zero_of_lintegral_tendsto_zero`
  (`PptFactorization/AubrunAlternative.lean:978`) is the direct asymptotic
  controlled growing-moment interface: if the lifted centered-moment
  `lintegral` tends to zero, then the negative-spectrum event probabilities
  tend to zero.
- `PptFactorization.RandomMatrixModel.rhoGamma_eq_card_mul_inv_frobeniusNorm_sq_smul_wishartGamma`
  (`PptFactorization/RandomMatrixModel.lean:86`) is the deterministic
  normalization bridge between induced states and Wishart matrices: for
  nonempty sample index `σ`, `ρ^Γ` is
  `(#σ * ‖G‖₂^{-2}) • W^Γ`.
- `PptFactorization.RandomMatrixModel.rhoGamma_eq_card_div_frobeniusMass_smul_wishartGamma`
  (`PptFactorization/RandomMatrixModel.lean:101`) is the Frobenius-mass form
  of the same bridge: `ρ^Γ = (#σ / frobeniusMass G) • W^Γ`.
- `PptFactorization.RandomMatrixModel.rhoGamma_centered_trace_re_eq_wishartGamma_frobeniusMass`
  (`PptFactorization/RandomMatrixModel.lean:114`) rewrites the endpoint
  trace observable as
  `Re Tr(((D #σ / frobeniusMass G) W^Γ - I)^m)`.
- `PptFactorization.RandomMatrixModel.rhoGamma_centered_trace_ofReal_eq_wishartGamma_frobeniusMass`
  (`PptFactorization/RandomMatrixModel.lean:128`) is the `ENNReal.ofReal`
  version used to transport Wishart/Frobenius trace-moment bounds through
  `lintegral` endpoints.
- `PptFactorization.RandomMatrixModel.rhoGammaEigenvalues`
  (`PptFactorization/RandomMatrixModel.lean:175`) exposes the real Hermitian
  eigenvalue coordinates of the concrete normalized partial transpose `ρ^Γ`.
- `PptFactorization.RandomMatrixModel.rhoGamma_posSemidef_iff_eigenvalues_nonneg`
  (`PptFactorization/RandomMatrixModel.lean:180`) bridges the concrete matrix
  PPT condition `(ρ^Γ).PosSemidef` to pointwise nonnegativity of those real
  eigenvalue coordinates.
- `PptFactorization.RandomMatrixModel.scaledRhoGammaEigenvalues`
  (`PptFactorization/RandomMatrixModel.lean:193`) is the positive-scale
  coordinate function intended for the `d^2 ρ^Γ` high-moment route.
- `PptFactorization.RandomMatrixModel.measure_not_rhoGamma_posSemidef_le_exists_scaled_eigenvalue_neg`
  (`PptFactorization/RandomMatrixModel.lean:221`) is the concrete
  model-facing measure bridge: for `D > 0`, the non-PPT event is bounded by
  the scalar event that some scaled eigenvalue coordinate is negative.
- `AubrunAlternative.rhoGamma_centered_trace_re_eq_sum_scaledRhoGammaEigenvalues`
  (`PptFactorization/AubrunAlternativeModelBridge.lean:96`) proves the
  deterministic spectral identity
  `Re Tr((Dρ^Γ-I)^m) = ∑ᵢ (Dλᵢ(ρ^Γ)-1)^m`, allowing future hard
  growing-moment suppliers to be stated as matrix trace-moment estimates
  rather than eigenvalue-coordinate sums.
- `AubrunAlternative.measurable_traceCenteredRhoGammaMoment`
  (`PptFactorization/AubrunAlternativeModelBridge.lean:151`) proves that the
  trace-moment observable `G ↦ Re Tr((Dρ^Γ(G)-I)^m)` is measurable.
- `AubrunAlternative.aemeasurable_scaledRhoGammaEigenvalueCenteredPowerSum_of_measurable`
  (`PptFactorization/AubrunAlternativeModelBridge.lean:163`) supplies the
  eigenvalue-coordinate a.e. measurability needed by the abstract Markov
  adapter by rewriting it to the measurable trace observable.
- `AubrunAlternative.eventually_not_rhoGamma_posSemidef_measure_le_of_eventually_lintegral_bound_scaledRhoGamma`
  (`PptFactorization/AubrunAlternativeModelBridge.lean:191`) is the
  model-facing finite-rate endpoint: an eventual paper-shape centered-moment
  bound for `scaledRhoGammaEigenvalues (D d) (G d ω)` gives the same eventual
  paper-shape probability bound for the concrete non-PPT event
  `¬ (rhoGamma (G d ω)).PosSemidef`.
- `AubrunAlternative.eventually_not_rhoGamma_posSemidef_measure_le_of_eventually_lintegral_bound_dSquared_scaledRhoGamma`
  (`PptFactorization/AubrunAlternativeModelBridge.lean:232`) is the paper-scale
  model-facing endpoint: the same conclusion specialized to
  `D d = (d : ℝ)^2`, i.e. centered moments of the eigenvalues of
  `d^2 ρ^Γ - I`.
- `AubrunAlternative.tendsto_not_rhoGamma_posSemidef_measure_zero_of_eventually_lintegral_bound_dSquared_scaledRhoGamma`
  (`PptFactorization/AubrunAlternativeModelBridge.lean:264`) is the paper-scale
  model-facing asymptotic endpoint: the same eventual moment bound plus
  `0 < q` and `2 < c * log q⁻¹` implies the concrete non-PPT probability tends
  to zero.
- `AubrunAlternative.exists_log_order_constants_and_tendsto_not_rhoGamma_posSemidef_measure_zero_of_four_lt_dSquared_scaledRhoGamma`
  (`PptFactorization/AubrunAlternativeModelBridge.lean:311`) is the concrete
  `λ > 4` model endpoint: Lean chooses `eps,q,c`, and the only visible
  mathematical supplier is the eventual paper-shape centered-moment estimate
  for the eigenvalues of `d^2 ρ^Γ - I`.
- `AubrunAlternative.measurableSet_rhoGamma_posSemidef_of_measurable`
  (`PptFactorization/AubrunAlternativeModelBridge.lean:85`) proves the concrete
  PPT event measurable from a measurable random sample map.  It uses the closed
  positive-semidefinite cone and measurability of `G ↦ ρ^Γ(G)`.
- `AubrunAlternative.exists_log_order_constants_and_tendsto_rhoGamma_posSemidef_measureReal_one_of_four_lt_dSquared_scaledRhoGamma`
  (`PptFactorization/AubrunAlternativeModelBridge.lean:349`) is the
  article-facing concrete `λ > 4` endpoint: with probability laws and
  measurability of the PPT event, the same visible moment supplier gives real
  PPT probability tending to one.
- `AubrunAlternative.exists_log_order_constants_and_tendsto_rhoGamma_posSemidef_measureReal_one_of_four_lt_dSquared_scaledRhoGamma_of_measurable`
  (`PptFactorization/AubrunAlternativeModelBridge.lean:417`) is the preferred
  article-facing endpoint when the random sample maps themselves are measurable.
- `AubrunAlternative.exists_log_order_constants_and_tendsto_rhoGamma_posSemidef_measureReal_one_of_four_lt_dSquared_traceMomentBound`
  (`PptFactorization/AubrunAlternativeModelBridge.lean:456`) is the
  trace-moment supplier endpoint: the hard input may be stated as an eventual
  bound on
  `∫⁻ ω, ofReal (Re Tr((d^2ρ^Γ(G d ω)-I)^(2m_d)))`, while the
  eigenvalue-coordinate a.e. measurability input remains visible for
  compatibility.
- `AubrunAlternative.exists_log_order_constants_and_tendsto_rhoGamma_posSemidef_measureReal_one_of_four_lt_dSquared_traceMomentBound_of_measurable`
  (`PptFactorization/AubrunAlternativeModelBridge.lean:511`) is the sharp
  trace-moment supplier endpoint: for measurable sample maps, the hard input
  is only the eventual trace-moment bound.
- `AubrunAlternative.eventually_not_rhoGamma_posSemidef_measure_le_of_eventually_traceMoment_bound`
  (`PptFactorization/AubrunAlternativeModelBridge.lean:546`) is the
  finite-rate trace-moment adapter: an eventual bound by `δ d` on the lifted
  centered trace-moment integral gives the same eventual bound on the concrete
  non-PPT probability.
- `AubrunAlternative.eventually_not_rhoGamma_posSemidef_measure_le_of_eventually_traceMoment_bound_ofReal`
  (`PptFactorization/AubrunAlternativeModelBridge.lean:604`) is the
  real-rate version of the same finite-rate adapter: an eventual bound by
  `ENNReal.ofReal (δ d)` gives `μ_d(non-PPT) ≤ ENNReal.ofReal (δ d)`.
- `AubrunAlternative.tendsto_not_rhoGamma_posSemidef_measure_zero_of_eventually_traceMoment_bound_ofReal`
  (`PptFactorization/AubrunAlternativeModelBridge.lean:626`) is the
  asymptotic real-rate endpoint: an eventual trace-moment bound by
  `ENNReal.ofReal (δ d)` plus `δ d → 0` gives `μ_d(non-PPT) → 0`.
- `AubrunAlternative.tendsto_rhoGamma_posSemidef_measureReal_one_of_eventually_traceMoment_bound_ofReal`
  (`PptFactorization/AubrunAlternativeModelBridge.lean:657`) is the
  article-facing real-rate PPT endpoint: under probability laws and measurable
  sample maps, the same real-rate trace bound gives real PPT probability
  tending to one.
- `AubrunAlternative.tendsto_rhoGamma_posSemidef_measureReal_one_of_eventually_wishartGamma_frobeniusMass_traceMoment_bound_ofReal`
  (`PptFactorization/AubrunAlternativeModelBridge.lean:716`) is the
  source-explicit article endpoint for the hard supplier: the eventual
  real-rate bound may be stated directly for the Frobenius-mass-scaled
  Wishart partial transpose
  `((d^2 #σ_d / frobeniusMass G_d) W_d^Γ - I)`.
- `AubrunAlternative.eventually_not_rhoGamma_posSemidef_measure_le_of_eventually_varying_wishartGamma_frobeniusMass_traceMoment_bound_ofReal`
  (`PptFactorization/AubrunAlternativeModelBridge.lean:760`) is the
  varying-space finite-rate source-explicit endpoint: an eventual real-rate
  bound in the Frobenius-mass-scaled Wishart normalization over `Ω d` gives
  the same eventual bound on the non-PPT event over `Ω d`.
- `AubrunAlternative.tendsto_not_rhoGamma_posSemidef_measure_zero_of_traceMoment_tendsto_zero`
  (`PptFactorization/AubrunAlternativeModelBridge.lean:857`) is the direct
  controlled-moment endpoint for the concrete non-PPT event: if the lifted
  centered trace-moment integral tends to zero, then the non-PPT probability
  tends to zero.
- `AubrunAlternative.tendsto_rhoGamma_posSemidef_measureReal_one_of_traceMoment_tendsto_zero`
  (`PptFactorization/AubrunAlternativeModelBridge.lean:925`) is the direct
  controlled-moment PPT endpoint: under probability laws and measurable sample
  maps, the same trace-moment convergence gives real PPT probability tending to
  one.
- `AubrunAlternative.tendsto_rhoGamma_posSemidef_measureReal_one_of_wishartGamma_frobeniusMass_traceMoment_tendsto_zero`
  (`PptFactorization/AubrunAlternativeModelBridge.lean:984`) is the direct
  source-explicit controlled-moment PPT endpoint: the hard input may be stated
  as convergence to zero of the Frobenius-mass-scaled Wishart trace moment.
- `AubrunAlternative.tendsto_rhoGamma_posSemidef_measureReal_one_of_varying_wishartGamma_frobeniusMass_traceMoment_tendsto_zero`
  (`PptFactorization/AubrunAlternativeModelBridge.lean:1020`) is the varying
  probability-space version of the same endpoint, matching the type shape of
  dimension-dependent Gaussian coordinate spaces.
- `AubrunAlternative.tendsto_rhoGamma_posSemidef_measureReal_one_of_canonicalGaussian_finSample_wishartGamma_frobeniusMass_traceMoment_tendsto_zero`
  (`PptFactorization/AubrunAlternativeModelBridge.lean:1184`) is the canonical
  Gaussian finite-sample endpoint: the probability law and sample map are the
  repository's concrete Gaussian model on `Fin d × Fin d` with `Fin (s_d)`
  columns.
- `AubrunAlternative.eventually_not_rhoGamma_posSemidef_measure_le_of_canonicalGaussian_natSample_wishartGamma_frobeniusMass_eventually_log_bound_of_ratio_tendsto_pos`
  (`PptFactorization/AubrunAlternativeModelBridge.lean:1441`) is the canonical
  Gaussian finite-rate endpoint for the fixed-base paper envelope.
- `AubrunAlternative.exists_log_order_constants_and_eventually_not_rhoGamma_posSemidef_measure_le_of_canonicalGaussian_natSample_wishartGamma_frobeniusMass_eventually_log_bound_of_ratio_tendsto`
  (`PptFactorization/AubrunAlternativeModelBridge.lean:1502`) is the
  finite-rate `λ > 4` constant-choice wrapper for the fixed-base endpoint.
- `AubrunAlternative.eventually_not_rhoGamma_posSemidef_measure_le_of_canonicalGaussian_natSample_wishartGamma_frobeniusMass_ratioDependent_log_bound_of_ratio_tendsto_pos`
  (`PptFactorization/AubrunAlternativeModelBridge.lean:1705`) is the canonical
  Gaussian finite-rate endpoint for the natural ratio-dependent envelope:
  an eventual trace-moment bound of that shape gives the same eventual bound
  on the concrete non-PPT event.
- `AubrunAlternative.exists_ratioDependent_log_order_constants_and_eventually_not_rhoGamma_posSemidef_measure_le_of_canonicalGaussian_natSample_wishartGamma_frobeniusMass_ratioDependent_log_bound_of_ratio_tendsto`
  (`PptFactorization/AubrunAlternativeModelBridge.lean:1806`) is the finite-rate
  `λ > 4` constant-choice wrapper for that endpoint.
- The adapters and fixed-moment bridge build and audit to foundational axioms
  only:
  `[propext, Classical.choice, Quot.sound]`.
