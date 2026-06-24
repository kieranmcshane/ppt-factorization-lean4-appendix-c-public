# FORMALIZATION_BOARD_COMPACT - Lean upper/lower frontier

Last compacted: 2026-06-02.

This file is the short entrypoint for new Codex chats. It replaces the old
crashing `Agent 2.1 : upper` thread for routine work.

## Safety

Do not open the old Codex thread:

```text
Agent 2.1 : upper
019e34b3-8f8a-7413-9eb6-a51801aaf2a7
```

Use local files as memory. Keep new chats short and update this compact board
or `CODEX_RECOVERY_CONTEXT.md` before ending a long session.

For ticket-level status, use `TICKET_LEDGER.md` first.  It is the compact
checkbox ledger distinguishing done theorem tickets from checked adapters.

## Protected Constraints

- Do not edit `PptFactorization/AppendixBSpikeLowerBound.lean`.
- Do not change `lean-toolchain`.
- Do not add `axiom`, `opaque`, `unsafe`, `admit`, `sorry`, or extra theorem
  parameters to hide gaps.
- Acceptable foundational dependencies are `propext`, `Classical.choice`, and
  `Quot.sound`.

## Upper Active Endpoint

File:

```text
PptFactorization/AppendixBPipelineGraduate.lean
```

Canonical explicit-Q bridge:

```text
AppendixB.gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
```

around line 600.

Sharper profile-count endpoint:

```text
AppendixB.gammaExpectation_pipeline_to_spherical_bound_of_profile_count_sum_canonical_explicitQ
```

around line 657.

Concrete `C0 = 1` endpoint:

```text
AppendixB.gammaExpectation_pipeline_to_spherical_bound_of_profile_count_sum_canonical_Qone
```

around line 723.

Remaining upper theorem-strength input:

- finite `wickRelationProfileCount` profile-count sum bound for
  `m = aubrunEvenMomentParameter dNat - 1`.

Meaning:

- Scalar nonnegativity and side-condition plumbing are mostly closed.
- The real upper gap is Aubrun graduate relation counting / finite profile
  count, not diagonal or polar transport plumbing.

## Lower Active Endpoint

File:

```text
PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean
```

Sharp length-three component endpoint:

```text
AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanErrorMeanAndExponentialTailStack_k3_withMixedErrorComponents_splitMixedWordBudget
```

around line 3759.

This endpoint replaces broad PT mean/variance inputs by:

- `lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample 3`,
- `lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R 3`,
- mixed envelope for one `errMix`,
- mixed smallness for the same `errMix`.

Remaining lower theorem-strength leaves:

1. length-three Catalan-error / Wick estimate;
2. length-three exponential deviation tail;
3. mixed local-expansion envelope on the sphere;
4. mixed eventual smallness for the same `errMix`.

Important diagnostic:

- Fixed-`M` PT scale comparisons are not the live unconditional route at
  length three.
- `lower_paperFacingPTScaleComparisonPacket_three_not_uniform` records the
  no-go.
- The live route is the honest mixed-error route.

## Verification Status From Full Board

Recent build/audit claims recorded in the full board:

```zsh
lake build PptFactorization.AppendixBPipelineGraduate
lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices
lake build PptFactorization
```

The full board records audits to `[propext, Classical.choice, Quot.sound]`
for the listed endpoints. Re-run the relevant build before editing.

## Recommended Next Work

Pick one leaf only per new chat:

- mixed envelope,
- mixed smallness,
- Catalan-error/Wick at length three,
- exponential tail supplier,
- upper finite profile-count bound.

Do not start by reading every Lean file. Start from this compact board, then
inspect only the target file and direct imports.

## First Commands In A New Chat

```zsh
git status --short --branch
git diff --stat
lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices
```

For upper work:

```zsh
lake build PptFactorization.AppendixBPipelineGraduate
```

For full sanity only when needed:

```zsh
lake build PptFactorization
```
