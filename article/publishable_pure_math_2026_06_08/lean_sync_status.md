# Lean Sync Status

This note is not part of the publishable manuscript.  It records how the
fresh pure-math article is aligned with the current formalization frontier.

Status date: 2026-06-08.

## Manuscript Policy

The PDF body is pure mathematics: definitions, propositions, proofs,
standard references, and probabilistic interpretation.  Lean names and ticket
identifiers are kept out of the article.

## Current Formal Alignment

| Article component | Current formal status | Meaning |
| --- | --- | --- |
| Oriented Cayley defects | checked | plus/minus defects are separated rather than collapsed into total defect |
| Rank/bidefect identity | checked | the Aubrun rank loss equals the sum of the two oriented defects |
| Bidefect scalar absorption | checked | the double bidefect sum is absorbed into two shifted analytic bases |
| Odd plus-defect vanishing | checked | plus-defect slices reduce to integer genus slices |
| Genus-zero route | reduced | noncrossing/Catalan route is the intended mathematical input |
| Chapuy slicing route | theorem-facing | recurrence is still a live Lean leaf |
| Biane large-gap links | theorem-facing | left and right large-gap link leaves remain visible |
| Return-collision analysis | retargeted | terminal and several boundary cases are checked; the raw internal-right branch is descended while preserving the internal subinterval offsets; the current honest endpoint keeps the nested side data, splits the three origin-tag side cases, then splits each side case into primitive-residual and internal-subinterval branches; the nonwrapping internal-subinterval leaf was sharpened to the off-cycle open-internal subcase, retargeted to the smaller side-aware residual interval produced from that off-cycle witness, split again into side-aware primitive and internal-subinterval child branches, and now absorbs the strict child primitive alternatives into the parent primitive residual leaf; the child interval has no skipped `x`-cycle points inside it and its `π`-block remains trapped inside the parent interval and off `x`; the loose primitive target is Lean-refuted without that data |
| Two-base Wick insertion | article-conditional | article assumes the standard termwise two-base Wick form before applying the count |
| Public random-matrix endpoint | not yet wired | awaits the final count theorem package |

## Current Sharp Formal Endpoint

The current honest count endpoint in the Lean file is the side-tied residual
branch-case strict-return version of the bidefect-count reduction, with the
origin-tag disjunction split into explicit side cases, each side case split into
primitive-residual versus internal-subinterval branches, and the nonwrapping
internal-subinterval branch exposed only in its smaller child
internal-subinterval form after child primitive absorption.
Its live inputs are:

1. the left large-gap Biane adjacent-link theorem;
2. the right large-gap Biane adjacent-link theorem;
3. the side-specific residual branch nested return-collision theorems,
   together with the strict nonwrapping smaller child internal-subinterval
   collision theorem; this child branch keeps the child interval inside the
   first-return interval, has no skipped `x`-cycle points inside it, and keeps
   the child `π`-block trapped inside the parent interval and off `x`;
4. the Chapuy/trisection recurrence.

The primitive-residual endpoint is a checked conditional diagnostic, not the
current theorem face.  It removes the shorter-interval branch by well-founded
descent, but in doing so it asks for a loose five-branch primitive statement
without the nested predecessor-skip side data.  The Lean theorem
`not_forall_loose_primitiveResidual_commonCycle` proves that this loose
statement is false already at `m=2`: the inverse long cycle is left-tight and
noncrossing, the interval `(0,2)` is primitive residual through the
adjacent-pi branch, but `finRotate 3 * pi` is the identity and has no
nontrivial common cycle pair.  The intended next formal target is therefore
one of the side-tied residual branch collision theorems consumed by the
current endpoint, or a stronger side-descending replacement.  After the latest
Lean split, the current endpoint asks for primitive-residual and
internal-subinterval branches separately in each of the nonwrapping,
wrap-below, and wrap-above cases.  The nonwrapping internal-subinterval branch
has two checked refinements: the internal interval cannot start at the left
endpoint `a`, and its internal witness cannot remain in the skipped `x`-cycle,
because either situation would contradict the first-return condition.  It also
has a checked noncrossing confinement theorem: once the witness is off-cycle,
every element of its `pi`-block lies strictly between the return endpoints
`a` and `c`.  The latest bridge splits the smaller contour-repeat interval:
either it already gives a common pair, or it leaves a strictly smaller
residual interval that still carries the no-`x`-cycle and block-off-`x`
invariants.
The latest formal endpoint absorbs strict child primitive branches.  The
broad smaller `leftTightContourIntervalRepeat` collision is no longer
theorem-facing, raw internal `T` has been replaced by adjacent `T` or genuine
shorter internal subinterval, and the remaining child primitive alternatives
are consumed by the parent primitive residual leaf.  The theorem-facing
smaller child input is now only the genuine internal-subinterval branch.
A future side-descending primitive theorem would still have to carry the
origin data and internal subinterval geometry through the interval descent.

The article presents the corresponding pure-math route as a standard
combinatorial theorem using unicellular maps and Chapuy slicing.  Its final
matrix-model paragraph is intentionally conditional on the standard termwise
two-base Wick form, so it does not overclaim a public random-matrix endpoint.
Until the four groups of leaves above are fully closed in Lean, the article and the
formalization should be read as mathematically aligned but not yet equally
complete.
