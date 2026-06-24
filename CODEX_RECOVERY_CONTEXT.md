# Codex Safe Recovery Context - Agent 2.1 Upper

Use this file to resume the work without opening the original Codex thread.

## Safety Rule

Do not open the original Codex thread:

- Title: `Agent 2.1 : upper`
- Original thread id: `019e34b3-8f8a-7413-9eb6-a51801aaf2a7`

That original local rollout was large/pathological and can make Codex Desktop unsafe. Work from this project folder and this handoff instead.

## Workdir

`/Users/kieranmcshane/Documents/Claude/Projects/Article PPT/ppt_factorization_lean4`

## Main Files

- Main Lean file: `PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean`
- Board: `FORMALIZATION_BOARD.md`
- Atlas: `LEAN_FILE_ATLAS.md`
- Safe history export: `/Users/kieranmcshane/.codex/diagnostics/history-exports-20260602/Agent-2-1-upper-history.md`
- Recovery note: `/Users/kieranmcshane/.codex/diagnostics/recovery-agent-2-1-upper-20260602.md`

## Last Recovered State

Despite the thread title, the recovered tail was working on lower-side Lean endpoints.

Last completed theorem:

```text
AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanErrorMeanAndExponentialTailStack_k3_withMixedErrorComponents_splitMixedWordBudget
```

Recovered meaning:

- The live lower `k = 3` endpoint was sharpened from broad mean/variance assumptions to closer frontier assumptions.
- Mean side uses:
  `lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample 3`
- Variance/concentration side uses:
  `lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R 3`

Reported verification before thread loss:

- `lake build PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices` passed.
- The theorem audited to `[propext, Classical.choice, Quot.sound]`.
- The touched Lean file had no `sorry`, `admit`, `axiom`, or `unsafe`.
- `git diff --check` was clean at that time.

## Next Good Task

First re-run the build/audit because the repo may now be dirty. Then continue one of the remaining lower leaves:

- mixed envelope,
- mixed smallness,
- Catalan-error/Wick at length three,
- exponential tail supplier.

Keep theorem statements explicit about which frontier leaf remains.

## Suggested First Prompt In A New Codex Chat

```text
Read CODEX_RECOVERY_CONTEXT.md first. Continue the recovered Agent 2.1 upper Lean workstream from this project folder. Do not open or rely on the original Codex thread. Inspect git status, inspect PptFactorization/AristotleTargets/LowerMeanLimitConcreteChoices.lean, then run the relevant build/audit before changing files.
```
