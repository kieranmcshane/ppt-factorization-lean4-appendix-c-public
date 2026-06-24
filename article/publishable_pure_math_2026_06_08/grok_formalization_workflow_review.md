# Grok Formalization Workflow Review

Date: 2026-06-08.

This is the useful signal from a Grok adversarial review of the current
U-AUB-02 formalization workflow and article-sync framing.  Grok was asked to
look for overclaiming, not to act as proof authority.

## Reviewer Signal

The framing is honest but still too easy to misread:

- U-AUB-02 is still explicitly not done.
- The current honest endpoint is described as a checked conditional implication
  with side-tied residual data, split first into the three origin-tag cases and
  then into primitive-residual versus internal-subinterval branches, with the
  nonwrapping internal-subinterval input exposed only in its off-cycle
  open-internal form.
- The live theorem-strength leaves remain large-gap left Biane, large-gap
  right Biane, the five unchanged side-specific residual branch
  return-collision theorems, the nonwrapping off-cycle open-internal collision
  theorem, and Chapuy recurrence.
- The new theorem `not_forall_loose_primitiveResidual_commonCycle` correctly
  rules out the loose primitive residual collision statement without nested
  predecessor-skip side data.

The latest adversarial review adds a stronger warning: long checked endpoint
names create a done-looking surface.  A reader can easily confuse "the
conditional reduction is checked" with "the ticket is closed" unless the four
open obligations are foregrounded as theorem-strength leaves.

The no-go theorem has already removed the old overclaim risk around the loose
primitive residual endpoint.  The remaining overclaim risk is subtler: the
current residual branch-case endpoint is the honest theorem face, but it still
depends on real mathematical inputs.

A refreshed quiet review after the open-nonwrapping endpoint made the same
warning sharper: a declaration beginning with `AubrunBiDefectCountBound_of_...`
can still look like theorem closure to a reader who is scanning names rather
than hypotheses.  The article-style workflow should therefore keep the open
leaf groups before the checked endpoint name.  It should also avoid letting the
return-collision casework dominate the story: the left and right large-gap
Biane adjacent-link theorems remain primary nonlocal combinatorial inputs, not
mere cleanup behind the already-built branch machinery.

## First-Class Open Obligations

The project workflow should keep these four leaves visible before any checked
endpoint name:

1. left large-gap Biane adjacent-link theorem;
2. right large-gap Biane adjacent-link theorem;
3. side-specific residual branch return-collision theorems for non-fixed
   predecessor skips, with the nonwrapping internal-subinterval leaf now
   narrowed to the off-cycle open-internal case;
4. Chapuy/trisection recurrence for the one-sided genus slices.

Finite permutation enumeration is useful for conjecture-finding and for
catching bad theorem statements.  It is not positive proof evidence for any of
these four leaves.

## Recommended Next Target

There are two reasonable next attacks.

The cautious local target is the nonwrapping internal-subinterval collision
leaf: the extractor and internal-subinterval vocabulary are already checked,
and the nonwrapping side has less wrap bookkeeping.  The first refinement of
that target is now checked: in the nonwrapping first-return case, the shorter
internal subinterval cannot start at the left endpoint, and its internal
witness cannot remain in the skipped `x`-cycle.  The remaining nonwrapping
internal-subinterval leaf is therefore the off-cycle open-internal case.

The refreshed review still recommends the nonwrapping residual leaves as the
best local proof-search target because they exploit the most checked
infrastructure.  It also warns that the large-gap Biane leaves have weaker
finite-enumeration support and should be treated as genuine new combinatorial
content.

The strategically central target is a side-tied branch collision theorem or a
replacement side-descending primitive theorem.  Any such theorem must remember
the predecessor-skip origin tag and the internal subinterval offsets:

- nonwrapping first return;
- wrap-below last return;
- wrap-above first return.

This second target has the highest trap density because the loose primitive
route was already Lean-refuted without the side data.

## Changes Accepted

- The ledger status key now defines `checked-tooling`, `checked-guardrail`,
  and `checked-reduction`.
- The blueprint endpoint now points at the off-cycle open-nonwrapping residual
  branch-case route, while the loose primitive endpoint is recorded only as an
  intermediate conditional diagnostic.
- The open nested-collision leaf now asks for side-tied branch collision
  theorems: primitive-residual branches for nonwrapping, wrap-below, and
  wrap-above; internal-subinterval branches for wrap-below and wrap-above; and
  the nonwrapping off-cycle open-internal branch.
- The nonwrapping internal-subinterval branch is sharpened to its off-cycle
  open-internal subcase; the endpoint-touching start case and the skipped
  `x`-cycle internal-witness case are discharged by the first-return side data.
- The project frontier graph now labels the current endpoint as the
  residual branch-case route, not the primitive route.
- The retained Grok workflow report now contains only scientific reviewer
  feedback.

## Still Open

This review did not close U-AUB-02.  It sharpened the project workflow and
made the next theorem target harder to misread.
