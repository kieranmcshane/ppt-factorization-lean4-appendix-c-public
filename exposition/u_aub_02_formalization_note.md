---
title: "U-AUB-02: bidefect count route, current formal frontier"
author: "Kieran McShane"
date: "2026-06-07"
---

# U-AUB-02: bidefect count route, current formal frontier

**Status.** U-AUB-02 is still open.  The current Lean declaration is a
checked conditional reduction: it proves that the listed Biane, frontier, and
Chapuy inputs imply `AubrunBiDefectCountBound m`; it does not prove those
inputs.

## Target

The formal target behind U-AUB-02 is the corrected Aubrun count input used by
the expectation pipeline.  In mathematical terms, the route now tries to prove
a bidefect count theorem of the following form.

For each Wick length $m$, every admissible pair of defects $(a,b)$ should
satisfy
$$
  \#\{\pi : \delta_+(\pi)=a,\ \delta_-(\pi)=b\}
  \le
  E_m(a,b),
$$
where $E_m(a,b)$ is the explicit Aubrun envelope used later in the scalar
sum.  Once this count is known, the already checked scalar absorption turns the
double defect sum into shifted bases rather than a false common-base maximum.

The remaining theorem-strength work is exactly the following four groups:

1. the large-gap left Biane adjacent-link theorem;
2. the large-gap right Biane adjacent-link theorem;
3. the side-specific residual branch collision theorems for non-fixed
   predecessor skips, including the nonwrapping smaller internal-subinterval
   child branch;
4. the Chapuy/trisection recurrence.

The active Lean endpoint is the checked reduction from those four groups to
the bidefect count bound:

```text
AppendixB.AubrunBiDefectCountBound_of_bianeAdjacentLinkHalves_left_gap_three_start_impossible_frontiers_nestedStrictReturnIntervalOpenNonwrapOffCycleSmallerInternalOnly_and_chapuy
```

This name should not be read as a solved ticket.  Its theorem statement still
contains the theorem-strength hypotheses listed immediately below.

The previous reduction layer was:

```text
AppendixB.AubrunBiDefectCountBound_of_bianeAdjacentLinkHalves_left_gap_three_start_impossible_frontiers_skipMinimalFrontierCommonCycle_and_chapuy
```

Delta: the previous layers still asked the collision theorem to work from the
minimal-frontier packet.  The active layer uses
`permCyclicPredecessorSkip_direct_commonCycle` internally, supplies
branch-normalized return intervals internally, descends internal-right repeats
to actual shorter subintervals, splits the three origin-tag side cases, and
exposes the nonwrapping internal-subinterval branch only in the off-cycle
open-internal form.  The newest checked support then sends the off-cycle
witness through a smaller side-aware residual child and splits that child into
primitive and internal-subinterval branches, then absorbs the strict primitive
child alternatives into the already theorem-facing parent primitive residual
leaf.

Recent left-slice improvement: the residual branch
`not pi(a,a+2) and S(a,a+2)` is contradictory.  The repeat `S(a,a+2)` copies
the one-step contour move from `a+2` to `c` into a length-two path from
`S(a)` to `S(c)`.  Tree uniqueness compares this copied path with the direct
length-two path from `pi(a,c)` and forces `T(a+2)=T(a)`, i.e.
`pi(a,a+2)`, contradicting the branch assumption.

That change is `U-AUB-316` in the ledger.  It removes the last left-start
gap-three parameter; the start slice `c-a=3, b=a+1` is no longer present on
the endpoint surface.  The later `U-AUB-317` closes the right special-slice
branch `S(b,c)`: if `S(c,d)` failed, copying the contour step `c -> d` across
`S(b)=S(c)` would give a simple path from `S(b)` to `S(d)`, and tree
uniqueness against the direct path from `pi(b,d)` would force `pi(b,c)`,
contradicting `pi(a,c)` and the separating non-link `not pi(a,b)`.

The active endpoint reduces `AubrunBiDefectCountBound m` to the following
theorem-strength inputs:

1. the remaining large-gap left Biane adjacent link under `2<c-a` and
   `c-a != 3`;
2. the remaining large-gap right Biane adjacent link outside the checked
   `d-b=3, c=b+2` slice;
3. the side-specific residual branch collision theorems for non-fixed
   predecessor skips, together with the strict nonwrapping smaller child
   internal-subinterval collision theorem carrying the parent/child side data;
4. the Chapuy/trisection recurrence.

Current support discipline: these live leaf groups are also rendered as a
Graphviz frontier at `build/u_aub_02_frontier.svg`, tracked in the
leanblueprint declaration inventory, and checked by
`tools/build_formalization_artifacts.sh`.  Grok review is used only as
scientific criticism of the exposition; it is not a second formalization agent.
The finite permutation scripts remain conjecture finders only.

Previous delta: `U-AUB-349` consumes the off-cycle witness through a smaller
side-aware residual interval.  The smaller contour-repeat interval now splits:
either it already gives the common $\pi$/$S\pi$ pair, or it leaves a
strictly smaller `leftTightStrictReturnIntervalResidual` with the inherited
no-$x$-cycle and block-off-$x$ invariants.  The current endpoint therefore no
longer asks for the whole nonwrapping off-cycle open-internal subinterval
theorem.

Most recent delta: `U-AUB-358` absorbs the strict child primitive branches
into the parent primitive residual leaf.  The theorem face therefore no longer
asks separately for the child internal `S`, start `S`, end `S`, fixed
predecessor, or adjacent `T` branches.  Those are all primitive residuals on
a strict child interval, hence primitive residuals on the parent interval.
The remaining smaller nonwrapping child leaf is the genuine
internal-subinterval branch.

Previous delta: `U-AUB-355` wires the strict split of the smaller
contour-repeat packet into the sharp endpoint.  U-AUB-356 then replaces raw
internal `T` by adjacent `T` or genuine shorter internal subinterval, and
U-AUB-358 absorbs the primitive alternatives as above.

Previous delta: `U-AUB-350` splits that smaller child residual by the
subinterval-preserving descent.  The theorem face now asks separately for the
side-aware primitive child branch and the side-aware internal-subinterval child
branch; the raw child residual predicate is no longer the exposed input.

Previous delta: `U-AUB-348` turns the confined off-cycle internal witness
into a strictly smaller charged contour interval.  The witness endpoints
$a+r,a+s$ form a same-$\pi$ interval strictly inside $(a,c)$, the interval has
its own `leftTightContourIntervalRepeat` packet, and the whole witness block is
still off the skipped $x$-cycle.  This is support for the open collision leaf,
not a closure of that leaf.

Previous delta: `U-AUB-347` proves strict noncrossing confinement for the
off-cycle nonwrapping internal block.  If $a,c$ are the first-return endpoints
in the skipped $x$-cycle and the internal witness starts at $a+r$ off that
cycle, the whole $\pi$-block of $a+r$ lies strictly inside $(a,c)$.

Previous delta: `U-AUB-329` makes the branch-normalized return interval
theorem-facing at the current sharp endpoint.  The collision theorem no
longer has to consume an arbitrary minimal-frontier packet; it can use the
nonwrapping first-return, wrap-below last-return, or wrap-above first-return
interval tied to the original skip.  This is a sharper checked conditional
endpoint, not a proof of the collision theorem.

Previous delta: `U-AUB-328` completes the branch-normalized return-interval
package for nested predecessor skips.  The wrap-below branch now chooses the
last same-`pi` return below `x`; because a nonfixed wrapping skip has
`x.val < (pi x).val`, the interval ending at `(pi x).val` has a genuine gap
and carries the repeated-contour obstruction.  The unified theorem packages
nonwrapping first return, wrap-below last return, and wrap-above first return.
This still does not prove the nested collision theorem.  A new pure-math
article source was also created at `article/u_aub_02_pure_math_article.tex`;
it compiles cleanly and has one Grok referee pass recorded in
`build/grok_u_aub_02_article_referee.md`.

Previous delta: `U-AUB-327` extracts first-return contour intervals in two
branches of the nested predecessor-skip leaf.  In the nonwrapping branch, the
first same-`pi` return after `(pi x).val` is separated by a
genuine gap unless the already-closed direct-hit case occurs.  The same
first-return package is now available for the wrap-above branch.  Both
packages include the left-tight repeated-contour obstruction.  They do not
prove the collision theorem.

Previous delta: `U-AUB-326` adds a tied contour extractor for the nested
predecessor-skip leaf.  A non-fixed skip now produces a long repeated contour
interval together with an origin tag: either the interval is exactly
`[(pi x).val,x.val]`, or it is a wrapping interval ending at `(pi x).val`, or
it is a wrapping interval starting at `x.val`.  This prevents the later
collision proof from treating the charged interval as anonymous.  It does not
prove the collision theorem.

Previous delta: `U-AUB-325` removes the direct-hit branch from the
minimal-frontier leaf.  If `finRotate (pi x)` is already in the same
`pi`-cycle as `x`, the checked theorem
`permCyclicPredecessorSkip_direct_commonCycle` supplies the nontrivial common
`pi`/`finRotate*pi` pair.  The live frontier theorem therefore only needs to
handle the nested case where this same-cycle relation fails.

Most recent delta, right special slice: `U-AUB-320` closes the last checked
right branch, `S(b+1,d)`.  If `S(b+1,d)` holds while the target `S(c,d)`
fails, uniqueness of simple incidence paths from `S(c)` to `S(d)` forces
`pi(b+1,c)`.  Combined with `pi(a,c)`, this gives `pi(a,b+1)`.  The shifted
left adjacent-link input on `(a,b,b+1,d)` gives `S(a,b)`, and then
`S(a,b)`, `S(b+1,d)`, `pi(a,b+1)`, and `pi(b,d)` form the forbidden
incidence square.  The active endpoint no longer exposes `hRightS_b1_d`,
`hRightFixed_b1`, `hRightS_b_c`, or `hRightT_b1_c`.  This is a checked
closure of the right gap-three special slice; U-AUB-02 remains open because
the non-local leaves below are still theorem-facing.

Recent delta, left end slice: `U-AUB-321` closes the fixed `a+1`
branch.  In the slice `c-a=3`, `b=a+2`, fixedness of `a+1` gives the
adjacent repeat `S(a+1,b)`.  If the target `S(a,b)` failed, the contour step
`a -> a+1`, this repeat, and the contour step `b -> c` would form a simple
length-four incidence path from `S(a)` to `S(c)`.  Tree uniqueness compares
that path with the direct length-two path from `pi(a,c)`, contradiction.  The
active endpoint no longer exposes `hLeftEndFixed_a1`.

Most recent delta, left end slice: `U-AUB-322` closes the remaining
`S(a+1,c)` branch.  The branch copies the contour step `a+1 -> b` into a
simple path from `S(c)` to `S(b)`.  The reversed contour step `b -> c` gives a
second simple path with the same endpoints.  Tree uniqueness identifies their
middle right vertices, hence forces `pi(a+1,b)`.  The existing
`pi(a+1,b)` absorber then closes the target.  The active endpoint no longer
exposes any finite gap-three branch.

Tooling delta: `U-AUB-323` makes the large-gap sanity profile reproducible.
The branch sanity script now checks the live large-gap crossing hypotheses in
small left-tight models; through `n=9`, it enumerates 6,916 left-tight
permutations and finds no crossing hypotheses.  This is conjecture-finding
evidence only, not a substitute for the large-gap Biane theorem.

This endpoint is a checked reduction, not a no-input closure of U-AUB-02.
Each item in the list above is still theorem-facing.  Thus a `leanok` marker
for this endpoint means that the reduction from these inputs is verified; it
does not mean that the Aubrun count theorem has been proved unconditionally.
In particular, words such as `Biane`, `frontier`, or `chapuy` inside the Lean
name are not completion markers.  They name the hypotheses being consumed.

## Mathematical route

This section states the intended counting theorem, not a currently closed
checked theorem.

The corrected route is one-sided first.  The intended combinatorial theorem
interprets the plus-defect $\delta_+$ through the unicellular-map genus:
$$
  \delta_+(\pi) = 2g(\pi).
$$
The expected counting strategy is then:
$$
  \#\{\delta_+=0\} \le 4^{m+1},
$$
and for genus $g$,
$$
  N_{m,g+1}
  \le (2(m+1))^3 N_{m,g}.
$$
Iterating gives
$$
  N_{m,g} \le 4^{m+1}(2(m+1))^{3g}.
$$
This is the combinatorial content that should feed the bidefect envelope.
This paragraph is a proof target, not a closed checked theorem.  The current
verified content is the reduction from concrete Biane/Chapuy inputs to the
bidefect envelope; the unconditional genus-zero and Chapuy counting theorems
remain open.

## Current Checked Content

The proof graph contains a large amount of checked surrounding structure.

The high plus-defect tail, finite small-window reductions, bidefect scalar
absorption, `NCPart` cardinality, gap-two Biane adjacent links, and several
minimal-contour/frontier reductions are already verified.  The latest checked
endpoint sharpens the route as follows:

```text
large-gap Biane half-links
+ checked gap-three frontier reductions
+ side-specific residual branch collisions
+ Chapuy recurrence
=> AubrunBiDefectCountBound m.
```

This display is a conditional implication, not a completed theorem.  The
named declaration still carries the large-gap Biane inputs, the side-specific
residual return-interval collision theorems, and the Chapuy recurrence as
hypotheses.

As a conditional adapter, the endpoint narrows the previous large-gap route in
two ways.  First, it
removes the direct no-skip hypothesis from the theorem face.  Instead of
asking directly that a noncrossing left-tight cycle partition has no non-fixed
predecessor skip, the current endpoint asks for the sharper collision
statement:

If a non-fixed predecessor skip exists, extract the side-tied long
same-$\pi$ return interval.  Split the origin side into nonwrapping first
return, wrap-below last return, and wrap-above first return; then split each
side into primitive and internal-subinterval branches.  In the nonwrapping
internal-subinterval branch the endpoint-touching case and the case where the
internal witness remains in the skipped $x$-cycle are checked impossible, so the
theorem-facing nonwrapping child leaf is now split into the side-aware
primitive and internal-subinterval child branches produced from the off-cycle
witness; the child interval lies strictly inside the first-return interval, has
no skipped $x$-cycle points inside it, and its $\pi$-block stays inside the
parent interval and off $x$.  The remaining branch theorems must
force two distinct points $y,z$ such that
$$
  y \sim_\pi z
  \quad\text{and}\quad
  y \sim_{\gamma\pi} z.
$$
This contradicts left-tight transversality.

Second, it no longer asks the broad left large-gap Biane hypothesis to handle
any `c-a=3` slice.  Since `a<b<c` and `c-a=3` force either `b=a+1` or
`b=a+2`, both left length-three slices are now routed through finite contour
reductions.

For `c-a=3`, `b=a+1`, the left start-slice branches are now all discharged at
the active endpoint.  The four former branches were
$$
  S(b,c),\quad \pi(a+2)=a+2,\quad \pi(b,a+2),
  \quad
  \bigl(\neg(a\sim_\pi a+2)\ \wedge\ S(a,a+2)\bigr).
$$
The left-start `S(b,c)` among them is supplied by the right Biane frontier.
The fixed-point branch and the `pi(b,a+2)` branch both force that
already-closed left-start `S(b,c)` branch.  The last branch is closed directly
by the copied length-two incidence path described above.

For `c-a=3`, `b=a+2`, the remaining left finite branches are
$$
  S(a+1,c).
$$
The earlier start-slice proof used several normalizations before the final
closure.  If the raw branch $S(a,a+2)$ also has the hidden link
$a\sim_\pi a+2$, the checked start-gap-two right-repeat theorem gives the
target $S(a,b)$.  The adjacent branch $S(a+2,c)$ is exactly the adjacent
repeat at $a+2$, hence becomes the fixed-point branch $\pi(a+2)=a+2$.
The target $S(a,b)$ itself is impossible: $b=a+1$, while $a$ already lies in
a nontrivial same-$\pi$ interval with $c$ and $c-a=3$.  An adjacent
$(\gamma\pi)$-repeat $S(a,a+1)$ would force $a$ to be fixed by $\pi$,
contradicting $a\sim_\pi c$ with $a<c$.  The checked theorem
`leftTight_bianeAdjacentLink_left_of_gap_three_start_adjacent_branch_to_target_iff_false`
therefore records that branch-to-target implications in this slice are the
same as proving the corresponding branch impossible.
The branch $\pi(a,a+1)$ is now closed: together with $\pi(a,c)$ it gives
$\pi(a+1,c)$, so the shifted gap-two crossing $(a+1,b,c,d)$ gives
$S(a+1,b)$, which feeds the already exposed branch.
The branch $\pi(a+1,b)$ is also closed: viewed on the shifted crossing
$(a,a+1,c,d)$, it is the already exposed start-adjacent $\pi(b,a+2)$ branch.
That branch gives $S(a,a+1)$, which is impossible for the nontrivial
same-$\pi$ interval $a\sim_\pi c$.
The remaining adjacent-repeat branch $S(a+1,b)$ has also been normalized:
because $b=a+2$, it is exactly the adjacent left repeat at $a+1$, and
left-tightness turns it into the fixed-point branch $\pi(a+1)=a+1$.
That fixed-point branch is now closed: fixedness gives $S(a+1,b)$, and a
denial of $S(a,b)$ produces a simple length-four path from $S(a)$ to $S(c)$.
Tree uniqueness compares it with the direct length-two path from
$a\sim_\pi c$, contradiction.

The right branch `S(b,c)` is now closed: assuming `S(b,c)` and denying the
target `S(c,d)` gives a copied contour path from `S(b)` to `S(d)`, and tree
uniqueness against the direct `pi(b,d)` path forces the forbidden link
`pi(b,c)`.  This right special branch is no longer a theorem-facing input to
the active endpoint.

The branch `pi(b+1,c)` is also no longer independent.  It combines with the
crossing link `pi(a,c)` to give `pi(a,b+1)`.  Applying the large-gap right
input to the shifted crossing `(a,b,b+1,d)` gives `S(b+1,d)`, because the
shifted crossing is not the special `c=b+2` slice.

The fixed branch `pi(b+1)=b+1` is now also internal.  Fixedness gives the
adjacent repeat `S(b+1,c)`.  If `S(b+1,d)` failed, the contour step
`b -> b+1` followed by the copied contour step `c -> d` would be a simple
length-four incidence path from `S(b)` to `S(d)`.  Tree uniqueness compares
that path with the direct length-two path from `pi(b,d)`, contradiction.  So
the fixed branch feeds the same `S(b+1,d)` implication.

The last right branch `S(b+1,d)` is now closed.  If the target `S(c,d)` were
false, path uniqueness would force `pi(b+1,c)`.  Then `pi(a,c)` gives
`pi(a,b+1)`, the shifted left link gives `S(a,b)`, and the four incidences
`pi(a,b+1)`, `pi(b,d)`, `S(a,b)`, `S(b+1,d)` form a forbidden square.

There are no remaining right finite branches in the checked `d-b=3`,
`c=b+2` slice.
The right branch $\pi(b,c)$ is now closed: together with the crossing link
$\pi(a,c)$, it would imply $\pi(a,b)$, contradicting the separating
non-link.
The adjacent-repeat branch $S(b+1,c)$ has also been normalized: because
$c=b+2$, it is exactly the adjacent left repeat at $b+1$, and left-tightness
turns it into the fixed-point branch $\pi(b+1)=b+1$.

These branch lists are endpoint-local snapshots.  The same public endpoint
still separately requires the large-gap left Biane input, the large-gap right
Biane input, the side-specific residual collision theorems, and the Chapuy
recurrence.

## What remains open

U-AUB-02 is not done.  The remaining theorem-strength leaves are:

1. prove the remaining large-gap left Biane adjacent-link cases;
2. prove the remaining large-gap right Biane adjacent-link cases;
3. prove the remaining side-specific residual collision theorems, now with
   branch-normalized return data available in all three nested branches and
   the nonwrapping child residual carrying the inherited no-$x$-cycle and
   block-off-$x$ data; only the genuine smaller child internal-subinterval
   branch remains theorem-facing after child primitive absorption;
4. prove the Chapuy/trisection recurrence.

These branches are not mere notation.  They are finite Biane contour cases
that likely need incidence-tree uniqueness or a descent lemma, not a naive
cycle-transitivity shortcut.  The finite branch scripts are conjecture
finders only; their clean output is not counted as proof.

## Checked reduction evidence

The new endpoint is in:

```text
PptFactorization/AppendixBAubrunGraduate.lean
```

The active checked declaration is:

```text
PptFactorization.AppendixB.AubrunBiDefectCountBound_of_bianeAdjacentLinkHalves_left_gap_three_start_impossible_frontiers_nestedReturnContourIntervalCommonCycle_and_chapuy
```

The previous reduction layer is:

```text
PptFactorization.AppendixB.AubrunBiDefectCountBound_of_bianeAdjacentLinkHalves_left_gap_three_frontiers_skipMinimalFrontierCommonCycle_and_chapuy
```

Verification performed:

```text
python3 scripts/lean_quick_check.py PptFactorization.AppendixBAubrunGraduate --timeout 300
lake build PptFactorization.AppendixBAubrunGraduate
lake build PptFactorization.AristotleTargets.UpperFromLowerColumnConcreteChoices
python3 scripts/aubrun_branch_sanity.py --max-n 9 --all
Pandoc rebuild of exposition/u_aub_02_formalization_note.pdf
Blueprint print-PDF rebuild and declaration inventory check
Grok adversarial review
#print axioms ...left_gap_three_start_impossible_frontiers_nestedReturnContourIntervalCommonCycle_and_chapuy
#print axioms ...left_of_gap_three_end_adjacent_fixed_a1
```

The axiom audit reports only:

```text
[propext, Classical.choice, Quot.sound]
```

This audit is evidence that the current reduction layer has no project-specific
axioms.  It is not evidence for the open leaves themselves.  In particular,
the large-gap Biane links, the nested non-direct return-interval collision
theorem, and the Chapuy recurrence still need their own checked declarations
and axiom audits.

## Tooling status

Automatic prose narration is not used as proof evidence.  The current note is
hand-curated from the checked Lean declarations, and any future machine-written
prose must be audited against the exact hypothesis list of the active endpoint.

Pandoc is installed and converts this note to both LaTeX and PDF using the
repository TeX setup.  This PDF has been refreshed from the current Markdown.
Leanblueprint was initialized for the project, with a declaration inventory at
`blueprint/lean_decls`; blueprint refreshes are treated as a separate
verification step and are not proof evidence by themselves.  Full doc-gen
integration was deliberately deferred when it attempted to download a 518 MB
Lean release-candidate toolchain, which would slow the current proof workflow.

A finite branch sanity script is now available at
`scripts/aubrun_branch_sanity.py`.  It enumerates small left-tight permutations
and checks active branch implications for counterexamples before they are
attempted in Lean.  This is only a guardrail: the current script reports no
active finite gap-three branches, then records the large-gap profile through
`n=9`.

Grok was used for advisory proof-architecture and exposition review.  Its
commentary remains advisory; Lean declarations, builds, axiom audits, Pandoc
artifacts, and blueprint checks are the evidence.
