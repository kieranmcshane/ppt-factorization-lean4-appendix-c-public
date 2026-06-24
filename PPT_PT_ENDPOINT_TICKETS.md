# PPT PT Endpoint Diagnostic Tickets

Last refreshed: 2026-05-20 17:45 Europe/Paris.

Endpoint inspected:

```lean
AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTWickAndDeviationStacks_withPTMixedError_splitMixedWordBudget
```

Location:

```text
PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean:2247
```

Current visible proof-debt inputs:

| hypothesis | visible type | class | grouped kernel |
| --- | --- | --- | --- |
| `hExponent` | `ptWickExponent_nonpositive R.sample k` | hard-math | PT mean Wick/radial/survivor |
| `hSurvivor` | `ptWickExponent_eq_zero_iff_noncrossingInvolution R.sample k` | hard-math | PT mean Wick/radial/survivor |
| `hCount` | `card_noncrossingInvolutions_with_r_pairs R.sample k` | hard-math | PT mean Wick/radial/survivor |
| `hSecond` | `deletedColumnSphericalMoment_secondMoment_expansion R k` | hard-math | PT second-moment/deviation |
| `hVariance` | `deletedColumnSphericalMoment_variance_le_const_div_d4 R k` | hard-math | PT second-moment/deviation |
| `hMixedWord` | `lowerConcreteMixedWordPointwiseBoundOnSphere R k ε bound` | deterministic | PT mixed word/budget |
| `hMixedBudget` | `lowerConcreteMixedWordBudgetWithError R k ε bound (fun _a _slack d => lowerPartialTransposeMixedErrorD k A M d)` | deterministic | PT mixed word/budget |

Live count:

- `7` live proof-debt inputs in the active endpoint.
- `5` hard-math inputs:
  `hExponent`, `hSurvivor`, `hCount`, `hSecond`, `hVariance`.
- `2` deterministic mixed inputs:
  `hMixedWord`, `hMixedBudget`.
- `5` parameters/context inputs are not proof tickets:
  `R`, `hk3`, `A`, `M`, `bound`.

Closed or no longer visible here:

- `ptGaussianWickMoment_exact R.sample k` is no longer an endpoint hypothesis.
  It is discharged by `ptGaussianWickMoment_exact_currentPredicate`.
- `deletedColumnSphericalMoment_eq_ptGaussianWickRatio R.sample k` is no
  longer an endpoint hypothesis. It is discharged by
  `deletedColumnSphericalMoment_eq_ptGaussianWickRatio_currentPredicate`.
  Diagnostic: these current Lean predicates are broad representation predicates;
  they are not the sharp mathematical cycle-count Wick theorem.
- `deletedColumnSphericalMoment_deviation_one_over_d R k` is no longer an endpoint hypothesis.  It is routed through `deletedColumnSphericalMoment_deviation_one_over_d_of_variance_le_const_div_d4`.
- The assembled Catalan mean wrapper `LFC_PPT_006_deletedColumnSphericalMean_tendsto_ptCatalan` exists, but this endpoint still exposes the three survivor-analysis ingredients rather than a single mean hypothesis.
- Two-trace exponent arithmetic sublemmas are proved:
  `ptSecondWickExponent_nonpositive_arith_of_cayley_length_triangles` and
  `ptSecondWickExponent_connected_le_neg_four_arith_of_geodesic_defects`.
- `LFC-PPT-009` is closed as a visible endpoint ticket: the endpoint no longer
  carries `deletedColumnSphericalMoment_deviation_one_over_d`.
- The raw full PT closed-walk Wick layer for `LFC-PPT-001` is now proved in
  `PptFactorization.TraceWickExpansion`:
  `pathProduct_rawWishartGamma_monomial_expansion`,
  `rawWishartGamma_closedWalkMonomialExpansion`,
  `gaussianRawWishartGamma_closedWalkMonomialExpansion`,
  `expected_trace_pow_succ_rawWishartGamma_eq_wick_sum`, and
  `expected_trace_pow_succ_rawWishartGamma_eq_explicit_wick_sum`.
- The next contraction-permutation layer for `LFC-PPT-001` is now proved as
  `wickExpansion_pathGammaMonomial_eq_perm_constraint_sum`; it exposes the
  sample-index, first tensor-factor, and second tensor-factor constraints of a
  Wick contraction.
- The full raw PT trace expectation has now been rewritten as a finite
  closed-walk/sample/permutation constraint sum in
  `expected_trace_pow_succ_rawWishartGamma_eq_perm_constraint_sum`.

Supporting internal tickets:

- `LFC-PPT-010` is not a visible endpoint hypothesis.  It is listed because it
  is the finite list lemma expected to help close `hMixedWord`.

Verification baseline:

```bash
lake env lean PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean
lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices
```

Axiom audit target:

```lean
#print axioms AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTWickAndDeviationStacks_withPTMixedError_splitMixedWordBudget
```

Current axiom audit: `[propext, Classical.choice, Quot.sound]`.

## Remaining Grouped Kernels

| grouped kernel | visible names | status |
| --- | --- | --- |
| PT mean survivor analysis | 3 | hard mathematical kernel remains visible |
| PT second-moment/deviation | 2 | hard mathematical kernel remains visible; Chebyshev tail wrapper is no longer separate |
| PT mixed word/budget | 2 | deterministic local kernel remains visible |

## LFC-PPT-001: `ptGaussianWickMoment_exact`

- priority: `P0`
- class: `closed-current-Lean-predicate`
- grouped kernel: `PT mean Wick/radial/survivor`
- endpoint visible hypothesis: none
- exact visible type:

```lean
ptGaussianWickMoment_exact R.sample k
```

- diagnosis: the endpoint no longer carries this hypothesis.  The current Lean
  predicate named `ptGaussianWickMoment_exact` was broader than the paper theorem:
  it only asked for some permutation-indexed representation with scalar `Q → 1`.
  The proof `ptGaussianWickMoment_exact_currentPredicate` witnesses it by putting
  the whole moment sequence on the identity permutation.
- current proved payload:
  - `ptGaussianWickMoment_exact_currentPredicate` proves the current Lean
    predicate and closes `hWick` as a visible endpoint input.
  - raw PT entry expansion is proved as
    `rawWishartGamma_entry_monomial_expansion`;
  - raw full PT path-product and closed-walk Wick expansion are proved as
    `expected_trace_pow_succ_rawWishartGamma_eq_explicit_wick_sum`.
  - each closed-walk monomial's Wick expansion is proved to be the sum over
    contraction permutations with the three explicit PT constraints in
    `wickExpansion_pathGammaMonomial_eq_perm_constraint_sum`.
  - the whole trace expectation is proved as the corresponding
    closed-walk/sample/permutation constraint sum in
    `expected_trace_pow_succ_rawWishartGamma_eq_perm_constraint_sum`.
- proof payload:
  - index `ℂ^(d^2)` by pairs `(a,b)`;
  - expand `(Wᴳ)_{(a,b),(c,e)} = ∑ r, G_{a,e,r} * conj (G_{c,b,r})`;
  - expand `Tr((Wᴳ)^k)`; **closed through the raw closed-walk Wick theorem**;
  - apply complex Gaussian Wick, with contraction `σ`; **closed through the raw closed-walk Wick theorem**;
  - prove the constraints leave `t_d ^ #σ`, `d ^ #(γσ)`, and `d ^ #(γ⁻¹σ)` free choices.
- remaining payload:
  - no remaining payload for the current endpoint predicate;
  - for the sharper paper theorem, collapse the explicit
    closed-walk/sample/permutation constraint sum to the
    permutation/cycle-count formula over `Equiv.Perm (Fin k)` by counting the
    assignments satisfying the three explicit constraints.
- closure test: `hWick` has disappeared from the active endpoint signature.
- verification:

```bash
lake env lean PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean
lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices
```

- axiom audit:

```lean
#print axioms AppendixB.ptGaussianWickMoment_exact
#print axioms AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTWickAndDeviationStacks_withPTMixedError_splitMixedWordBudget
```

## LFC-PPT-002: `deletedColumnSphericalMoment_eq_ptGaussianWickRatio`

- priority: `P0`
- class: `closed-current-Lean-predicate`
- grouped kernel: `PT mean Wick/radial/survivor`
- endpoint visible hypothesis: none
- exact visible type:

```lean
deletedColumnSphericalMoment_eq_ptGaussianWickRatio R.sample k
```

- diagnosis: the endpoint no longer carries this hypothesis.  In the current
  code it is an alias for the same broad predicate as `ptGaussianWickMoment_exact`,
  and is discharged by
  `deletedColumnSphericalMoment_eq_ptGaussianWickRatio_currentPredicate`.
- sharper paper payload, not needed by the current broad endpoint predicate:
  - set `T = ‖G‖₂^2 = Tr(GG*)`;
  - prove `Y = G / ‖G‖₂` is independent of `T`;
  - prove `(GG*)ᴳ = T • ((YY*)ᴳ)`;
  - use `T ∼ Gamma(N*t, 1)`;
  - prove `E[T^k] = (Nt)^{overline k}`.
- closure test: `hRadial` has disappeared from the active endpoint signature.
- verification:

```bash
lake env lean PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean
lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices
```

## LFC-PPT-003: `ptWickExponent_nonpositive`

- priority: `P0`
- class: `hard-math`
- grouped kernel: `PT mean Wick/radial/survivor`
- endpoint visible hypothesis: `hExponent`
- exact visible type:

```lean
ptWickExponent_nonpositive R.sample k
```

- diagnosis: the endpoint still needs the finite permutation exponent inequality.  The final arithmetic step is already isolated in `ptWickExponent_nonpositive_arith_of_cayley_length_triangles`.
- proof payload:
  - instantiate the project definition of the one-trace PT exponent;
  - rewrite cycle counts using Cayley length;
  - use `|γσ| + |σ| ≥ |γ|` and `|γ⁻¹σ| + |σ| ≥ |γ⁻¹|`;
  - discharge the linear step through the existing arithmetic lemma.
- closure test: `hExponent` disappears from the endpoint signature.
- verification:

```bash
lake env lean PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean
lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices
```

## LFC-PPT-004: `ptWickExponent_eq_zero_iff_noncrossingInvolution`

- priority: `P0`
- class: `hard-math`
- grouped kernel: `PT mean Wick/radial/survivor`
- endpoint visible hypothesis: `hSurvivor`
- exact visible type:

```lean
ptWickExponent_eq_zero_iff_noncrossingInvolution R.sample k
```

- diagnosis: the endpoint still needs the survivor class.  Survivors are noncrossing involutions with fixed points allowed, not fixed-point-free pairings and not ordinary Marchenko-Pastur noncrossing partitions.
- proof payload:
  - prove equality in the exponent is equality in both Cayley geodesic inequalities;
  - use the cyclic geodesic/noncrossing theorem for `γ` and for `γ⁻¹`;
  - show cycles of length at least `3` cannot be compatible with both orientations;
  - fixed points and transpositions survive.
- closure test: `hSurvivor` disappears from the endpoint signature.
- verification:

```bash
lake env lean PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean
lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices
```

## LFC-PPT-005: `card_noncrossingInvolutions_with_r_pairs`

- priority: `P0`
- class: `hard-math`
- grouped kernel: `PT mean Wick/radial/survivor`
- endpoint visible hypothesis: `hCount`
- exact visible type:

```lean
card_noncrossingInvolutions_with_r_pairs R.sample k
```

- diagnosis: the endpoint still needs the Catalan survivor count by number of transpositions.
- proof payload:
  - define `pairCount`;
  - show a survivor with `r` transpositions has `#σ = k - r`;
  - prove the fiber bijection: choose `2*r` paired points, then choose a noncrossing perfect matching;
  - feed the count into `ptSurvivorWeightSum_eq_ptCatalanMean_of_pairFiberCounts`.
- closure test: `hCount` disappears from the endpoint signature.
- verification:

```bash
lake env lean PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean
lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices
```

## LFC-PPT-007: `deletedColumnSphericalMoment_secondMoment_expansion`

- priority: `P0`
- class: `hard-math`
- grouped kernel: `PT second-moment/deviation`
- endpoint visible hypothesis: `hSecond`
- exact visible type:

```lean
deletedColumnSphericalMoment_secondMoment_expansion R k
```

- diagnosis: the endpoint still needs the exact two-trace PT Wick expansion.  The two-trace exponent arithmetic is proved, but the Gaussian Wick expansion and radial `2k` normalization remain the hard payload.
- proof payload:
  - use `γ₂=(1,...,k)(k+1,...,2k)`;
  - expand the product of two PT traces;
  - apply complex Gaussian Wick over `S_(2k)`;
  - prove the free-index factors `t_d ^ #σ`, `d ^ #(γ₂σ)`, and `d ^ #(γ₂⁻¹σ)`;
  - divide by the rising denominator `(Nt_d)^{overline 2k}`;
  - instantiate the source-of-truth exponent and use `ptSecondWickExponent_nonpositive_arith_of_cayley_length_triangles`.
- closure test: `hSecond` disappears from the endpoint signature.
- verification:

```bash
lake env lean PptFactorization/AristotleTargets/LowerBackgroundMomentConcreteChoices.lean
lake env lean PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean
lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices
```

## LFC-PPT-008: `deletedColumnSphericalMoment_variance_le_const_div_d4`

- priority: `P0`
- class: `hard-math`
- grouped kernel: `PT second-moment/deviation`
- endpoint visible hypothesis: `hVariance`
- exact visible type:

```lean
deletedColumnSphericalMoment_variance_le_const_div_d4 R k
```

- diagnosis: the endpoint still needs the variance theorem.  The endpoint no longer carries the separate Chebyshev/deviation hypothesis, so this is now the unique visible second-moment tail theorem after `hSecond`.
- proof payload:
  - use `hSecond` to rewrite the second moment;
  - prove block-preserving permutations reproduce the square of the one-trace Wick sum;
  - prove `Q₂,d - Q₁,d^2 = O(d^-4)`;
  - for non-block-preserving permutations, prove defect at least `2` in both geodesic inequalities;
  - apply `ptSecondWickExponent_connected_le_neg_four_arith_of_geodesic_defects`;
  - conclude connected terms are `O(d^-4)`.
- closure test: `hVariance` disappears from the endpoint signature.  No separate `deletedColumnSphericalMoment_deviation_one_over_d` hypothesis should return.
- verification:

```bash
lake env lean PptFactorization/AristotleTargets/LowerBackgroundMomentConcreteChoices.lean
lake env lean PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean
lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices
```

## LFC-PPT-010: `lowerLocalTwoLetterMixedWordAppendHeadQSplit`

- priority: `P1`
- class: `deterministic`
- grouped kernel: `PT mixed word/budget`
- live endpoint ticket: `no`; supporting sub-ticket for `hMixedWord`
- endpoint visible hypotheses served: `hMixedWord`, then `hMixedBudget`
- exact visible types:

```lean
lowerConcreteMixedWordPointwiseBoundOnSphere R k ε bound
lowerConcreteMixedWordBudgetWithError R k ε bound
  (fun _a _slack d => lowerPartialTransposeMixedErrorD k A M d)
```

- diagnosis: the mixed proof path needs the finite head-Q split only if upstream cyclic normalization has already made words start with `Q`.
- proof payload:
  - for `w = Q :: t` with one more `Q` in `t`, split `t = C ++ Q :: D`;
  - preserve `Q` count, `B` count, and length;
  - feed the split into the head-Q trace estimate.
- closure test: the pointwise mixed theorem uses this split and no longer needs arbitrary cyclic-normalization as an external hypothesis.
- verification:

```bash
lake env lean PptFactorization/AristotleTargets/LowerMixedLowerConcreteChoices.lean
lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices
```

## LFC-PPT-011: `lowerConcreteMixedWordPointwiseBoundOnSphere`

- priority: `P1`
- class: `deterministic`
- grouped kernel: `PT mixed word/budget`
- endpoint visible hypothesis: `hMixedWord`
- exact visible type:

```lean
lowerConcreteMixedWordPointwiseBoundOnSphere R k ε bound
```

- diagnosis: the endpoint still needs pointwise PT trace-word estimates on the favorable sphere event.
- proof payload:
  - one-Q words: `|Tr(QB^(k-1))| ≤ |Q|₂ |B^(k-1)|₂`;
  - many-Q words after split: `|Tr(Q C Q D)| ≤ |Q C|₂ |Q D|₂`;
  - use `|Q|₂ ≤ 1`, `|Q|op ≤ 1`, `|B|op ≤ M/N`, `|B|₂ ≤ M/sqrt(N)`.
- closure test: `hMixedWord` disappears from the endpoint signature or is supplied by a proved local theorem.
- verification:

```bash
lake env lean PptFactorization/AristotleTargets/LowerMixedLowerConcreteChoices.lean
lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices
```

## LFC-PPT-012: `lowerConcreteMixedWordBudgetWithError`

- priority: `P1`
- class: `deterministic`
- grouped kernel: `PT mixed word/budget`
- endpoint visible hypothesis: `hMixedBudget`
- exact visible type:

```lean
lowerConcreteMixedWordBudgetWithError R k ε bound
  (fun _a _slack d => lowerPartialTransposeMixedErrorD k A M d)
```

- diagnosis: the endpoint still needs coefficient-budget summation and scalar smallness of the explicit PT mixed error.
- proof payload:
  - group words by `j = #Q(w)`;
  - use `Re z ≥ -|z|`;
  - insert binomial or supplier coefficient budgets;
  - prove scalar smallness of `lowerPartialTransposeMixedErrorD` for fixed `k ≥ 3`.
- closure test: `hMixedBudget` disappears from the endpoint signature or is supplied by a proved local theorem.
- verification:

```bash
lake env lean PptFactorization/AristotleTargets/LowerMixedLowerConcreteChoices.lean
lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices
```
