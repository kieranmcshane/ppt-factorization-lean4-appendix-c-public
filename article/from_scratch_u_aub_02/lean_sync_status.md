# Lean Sync Status

This file is the bridge between the pure-math article and the Lean
development.  It is not part of the publishable manuscript.

Status date: 2026-06-07.

## Article Components

| Article component | Formal status | Mathematical meaning |
| --- | --- | --- |
| Rank identity | checked | \(\mathcal R+\delta_++\delta_-=2n+2\) |
| Bidefect objects | checked | separate plus/minus Cayley defects |
| Scalar absorption | checked | two binomial shifted bases |
| Odd plus-defect vanishing | checked | parity/genus conversion |
| Genus induction from two inputs | checked | zero genus plus Chapuy gives envelope |
| Terminal full-endpoint return collision | checked | if one return interval's endpoints coincide in both cycle relations, they are the common-cycle witness |
| Return-interval repeat case split | checked | every repeated contour on a return interval is either the terminal case or a proper/internal branch |
| Strict return-interval boundary split | checked | start-adjacent repeats are impossible; end-adjacent repeats become the fixed-predecessor branch |
| Strict return-interval endpoint | checked | the current bidefect endpoint consumes the strict frontier rather than the raw repeated-contour predicate |
| Residual strict return-interval endpoint | checked | the solved common-cycle branch is discharged internally; the endpoint exposes only residual strict branches |
| Descended residual return-interval endpoint | checked | the raw internal-right repeat branch is replaced by adjacent right repeat or a strictly shorter same-\(\pi\) interval |
| Smaller child primitive absorption | checked | strict child primitive residual branches are absorbed into the parent primitive residual leaf |
| Genus-zero count | reduced | Catalan/noncrossing route still being closed |
| Chapuy slicing recurrence | open | exact model recurrence still theorem-facing |
| Public random-matrix endpoint | not wired | needs the final count theorem first |

## Current Formal Frontier

The current sharp formal endpoint has four theorem-strength leaf groups:

1. large-gap left Biane adjacent-link theorem;
2. large-gap right Biane adjacent-link theorem;
3. nested non-direct return-interval collision theorem;
4. Chapuy/trisection recurrence.

The full-endpoint repeated-contour subcase inside item 3 is now checked, and
the formalization has a checked case split separating that terminal case from
the proper endpoint-touching and internal return-collision branches.  The
boundary split has also been sharpened: the start-adjacent endpoint repeat is
impossible, and the end-adjacent endpoint repeat is the fixed-predecessor
branch.  The current endpoint now exposes this strict frontier rather than the
raw repeated-contour predicate, and the already-solved common-cycle branch is
now discharged internally.  The raw internal-right repeat branch has also been
replaced by the checked adjacent-or-strictly-shorter descent.  Non-adjacent
proper repeats, internal left repeats, adjacent/shorter right-repeat descent
branches, and the fixed predecessor branch still remain inside the leaf.
The nonwrapping smaller child primitive branches are no longer exposed
separately: a strict child primitive residual is now checked to be a parent
primitive residual.  The remaining smaller child theorem-facing branch is the
genuine internal-subinterval case with the inherited side data.  Adapter
theorems and endpoint rewiring have narrowed the frontier, but they do not
turn the reduction into an unconditional proof.

## Manuscript Policy

The LaTeX article stays pure math.  Lean names and formal ticket identifiers
belong in this sync file, the ticket ledger, or implementation notes, not in
the publishable PDF.
