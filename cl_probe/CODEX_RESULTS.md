# CODEX_RESULTS: CL spectrum probe

## Status

Branch: `codex/cl-spectrum`.

Open PR: <https://github.com/kieranmcshane/ppt-factorization-lean4/pull/1>.

Current reproducibility audit, rerun on 2026-06-17:

- rebuilt `cl_probe/bin/cl_spectrum` from `cl_probe/cl_spectrum.cpp`;
- rebuilt `cl_probe/bin/k2_character_spectrum_gmp` from
  `cl_probe/k2_character_spectrum_gmp.cpp`;
- checked that fresh brute-force `k=2,r=2..5` output matches
  `spectrum_k2_exact.csv` exactly;
- checked that fresh brute-force `k=4,r=2` output matches
  `spectrum_k4_exact.csv` exactly;
- regenerated the structural GMP `k=2,r<=8` table and checked that it matches
  the tracked `spectrum_k2_character.csv` prefix exactly;
- reran `cl_stress_audit.py --k 2 --csv cl_probe/spectrum_k2_character.csv`;
  it returned `audit_status=PASS`;
- built and ran `two_block_open_exact.cpp` for `k=6`, replacing the earlier
  Monte Carlo evidence for the first two-block open component range by exact
  counts and adding exact bidefect output for the same finite class;
- added `finite_type_frontier.py`, which separates bounded-size component
  catalogues from genuinely unbounded component-size entropy;
- added `eta_requirement_table.py`, which separates the local one-sided eta
  ceiling from the stricter direct full-CL component threshold;
- added `bidefect_local_threshold.py`, which rewrites the direct threshold in
  local two-sided total-genus variables;
- added `bidefect_min_genus_threshold.py`, which tests the sharper
  one-sided-intersection envelope based on `min(g_+,g_-)`;
- added `bidefect_remaining_lattice.py`, which lists the integer bidefect
  candidate rows still not closed by the min-genus intersection route;
- added `k6_remaining_arithmetic.py`, which rewrites the `k=6` remaining
  candidate rows as exact integer inequalities;
- added `k6_strip_entropy_threshold.py`, which computes the connected-count
  exponent needed for the balanced strip to threaten CL;
- added `k6_strip_population_sampler.py`, which estimates finite connected
  counts on balanced-strip rows and compares them to the CL threshold;
- added `bidefect_target_local_search.py`, a heuristic transposition-walk
  search for explicit witnesses in targeted balanced-strip rows;
- added `k6_balanced_strip_target_sweep.py`, which runs the targeted search
  across the exact `k=6` balanced arithmetic strip;
- added `k6_balanced_strip_certificates.py` and the tracked witness file
  `k6_balanced_strip_witnesses_t13_t40.csv`, giving deterministic
  certificate verification for the balanced-strip rows found through `t=40`;
- added `k6_balanced_strip_neutral_moves.py` and the tracked profile
  `k6_balanced_strip_neutral_moves_t13_t40.csv`, giving a deterministic
  one-swap local multiplicity diagnostic around the certified strip witnesses;
- added `k6_balanced_strip_shape_profile.py` and the tracked profile
  `k6_balanced_strip_shape_profile_t13_t40.csv`, recording the cycle-count
  split and coarse cycle-shape data for the same certified witnesses;
- added `k6_balanced_split_window.py` and the tracked profile
  `k6_balanced_split_window_t13_t40.csv`, isolating the strict and boundary
  cycle-count split slots not closed by the three-cycle-count envelope;
- added `k6_balanced_split_target_search.py` and the tracked profile
  `k6_balanced_split_target_search_t13_t40.csv`, a bounded heuristic search
  aimed directly at the strict split slots;
- added `k6_balanced_split_target_search_best_t13_t40.csv`, preserving the
  best near-hit permutations from the same strict split search;
- added `k6_balanced_split_asymptotics.py` and the tracked profile
  `k6_balanced_split_asymptotics_t13.csv`, giving the exact leading arithmetic
  size of the strict split-slot lattice;
- added `k6_balanced_split_invariant_sanity.py` and the tracked profile
  `k6_balanced_split_invariant_sanity_t13_t80.csv`, recording that the cheap
  sign parity relation is automatic on the strict slots checked through
  `t=80`;
- added `k6_strict_split_near_hit_local_profile.py`,
  `k6_strict_split_near_hit_local_profile_t13_t40.csv`,
  `k6_strict_split_zero_neighbor_extract.py`, and
  `k6_strict_split_zero_neighbor_witnesses_t13_t40.csv`, showing that one
  saved near-hit has a one-swap neighbor which is an actual strict split
  witness;
- added `k6_strict_split_local_descent.py` and the tracked profile
  `k6_strict_split_local_descent_t13_t40.csv`, a deterministic steepest
  one-swap descent from the saved strict near-hits;
- added `k6_strict_split_block_growth.py` and the tracked constructive profile
  `k6_strict_split_block_growth_t39_to_t40.csv`, which grows the `t=39`
  strict witness to every strict split target at `t=40` by adding one block
  and one bridge image-swap;
- added `k6_strict_split_fixed_bridge_growth.py` plus tracked propagation
  profiles `k6_strict_split_fixed_bridge_growth_t40_to_t41.csv`,
  `k6_strict_split_fixed_bridge_growth_t41_to_t42.csv`,
  `k6_strict_split_fixed_bridge_growth_t42_to_t43.csv`, and
  `k6_strict_split_fixed_bridge_growth_t43_to_t44_summary.csv`, testing the
  fixed bridge `0:new_block_start` through `t=44`;
- added `k6_strict_split_fixed_bridge_hit_counts.py`,
  `k6_strict_split_fixed_bridge_hit_summary.py`, the four tracked hit-count
  profiles through `t=44`, and
  `k6_strict_split_fixed_bridge_hit_summary_t40_to_t44.csv`, counting how many
  of the `6!` internal block permutations work for the fixed bridge;
- added `k6_strict_split_bridge_location_counts.py` and the tracked sample
  `k6_strict_split_bridge_location_counts_t41_to_t42_sample.csv`, counting old
  bridge-domain choices for one representative strict propagation step;
- added `k6_strict_split_bridge_location_counts_t41_to_t42_all_offsets.csv`,
  extending that same bridge-location count to all six new-domain offsets;
- added `k6_strict_split_bridge_choice_extract.py`,
  `k6_strict_split_bridge_choice_sample_t42.csv`, and
  `k6_strict_split_bridge_independence_sample_t42_to_t43.csv`, testing whether
  several different old bridge-domain choices at one step preserve the next
  step's bridge-location multiplicity;
- added `bidefect_witness_search.py`, which finds and verifies explicit
  finite connected witnesses for targeted bidefect rows;
- added `bidefect_witness_sweep.py`, which sweeps remaining candidate rows for
  finite witnesses under a fixed sampling budget;
- added `connected_bidefect_sampler.py`, a finite-sample diagnostic for
  connected bidefect rows at larger component sizes.

This round completed two exact enumeration paths:

- a faithful compiled C++ port of the Python `genus_grade.py` enumerator,
  validating the definitions by brute force through `kr = 12`;
- an exact compiled `k=2` character/component extractor, validated against the
  brute-force tables through `r=6` and against the Python structural CSV through
  `r=20`; the same compiled exact structural formula now reaches the requested
  `r=7,8` spectra and continues through `r=28`.

The general even-`k` combinatorial lemma (CL) is still **not settled**.  The
case `k=2` has a paper-level closure by the three-cycle-count envelope recorded
below.  The case `k=4` now has a paper-level closure of the remaining
proportional window using the connected map/genus supplier in
`CL_connected_map_genus_bound.md`, which relies on standard rooted-map
enumeration and Chapuy slicing.  Neither closure is a Lean formalization.  For
general even `k >= 6`, the central proportional-band entropy problem remains
open on the diagonal `r \simeq a_d`.  The latest `k=6` target sweep found
connected witnesses in every balanced-strip row tested from `t=13` through
`t=40`, so the remaining strip should be treated as populated; the still-open
question is its asymptotic count/entropy, not mere finite existence.

The analytic target is isolated in `CL_analytic_frontier.md`.  It turns the
finite proportional-band diagnostics into the precise `limsup` entropy
inequality that would prove the upper-bound CL closure.  A `liminf` statement
would belong to a separate lower-bound or sharpness argument, not to this
one-sided closure.

The same note also records a proved high-energy cutoff.  The trivial bound
`N_r(E) <= (kr)!` already rules out every proportional band
`E >= (2k + eta)r`, uniformly for fixed `eta > 0` on `r <= C a_d`.  Thus any
possible breach of (CL') must lie in the compact window `E/r <= 2k + o(1)`.
For `k=2`, the remaining asymptotic danger is therefore the window
`2 <= E/r <= 4` and the boundary layer near `4`; the much larger raw entropy
peak observed in finite data is not, by itself, a diagonal obstruction.

This round also adds a sharper three-cycle-count envelope.  If
`p = #pi`, `a = #(gamma pi)`, and `b = #(pi gamma^{-1})`, then on
`E = alpha r`,

```text
2p + a + b = (2k + 2 - alpha)r.
```

Combining this identity with the unsigned-Stirling cycle-count bound gives

```text
beta_k(alpha) <= (k - 1)/2 + alpha/4.
```

For `k=2`, this is strictly below the CL threshold `2/3 + alpha/3`.
Therefore the proportional-band `limsup` entropy target for `k=2` is closed
at leading `r log r` scale.  The same note then stitches the `O(r)` remainder
to the exact rising-factorial penalty across all `r <= C a_d`; this gives a
paper-level proof of (CL) for `k=2`.  This is not a Lean formalization.

The helper `cycle_count_envelope.py` reports the comparison directly.  On the
sampled full `k=2` proportional range `0 <= alpha <= 6`, the worst envelope
margin is at `alpha=0`:

```text
beta_bound - beta_threshold = -1/6.
```

For `k=4`, the same envelope crosses the threshold at

```text
alpha = 14/3.
```

So it helps only in the upper part of the `k=4` central window.
More generally, the unresolved proportional window left by the cycle-count
envelope is

```text
2 <= alpha < (2k^2 - 4k - 2)/(k - 1),
```

intersected with the central range.  For the first few even values this is:

| k | crossing alpha | remaining open window |
|---:|---:|---|
| 2 | -2 | none |
| 4 | 14/3 | `2 <= alpha < 14/3` |
| 6 | 46/5 | `2 <= alpha < 46/5` |
| 8 | 94/7 | `2 <= alpha < 94/7` |
| 10 | 158/9 | `2 <= alpha < 158/9` |
| 12 | 238/11 | `2 <= alpha < 238/11` |

## Proved / exact

The C++ exact enumerator in `cl_spectrum.cpp` uses the same definitions as
`genus_grade.py`:

- `gamma(k,r)` is the product of `r` disjoint `k`-cycles.
- `E = 2kr + 2r - #(gamma*pi) - #(pi*gamma^{-1}) - 2#pi`.
- The active condition removes every component that is exactly one original
  `k`-block on which `pi` lies in the genus-zero one-block set `G_k`.
- The table records `(j,h)` with `j = r - c(pi)` and `E = 4j + 2h`.

Validation against the Python reference passed exactly for `k=2`, `r=2..5`.
The compiled exact run also reached `k=2, r=6` and `k=4, r=2,3`.

The same compiled enumerator now has a `--defect-csv` mode for the
bidefect/cycle-count frontier.  It records

```text
delta_+ = kr + r - #pi - #(gamma*pi),
delta_- = kr + r - #pi - #(pi*gamma^{-1}),
```

along with the three cycle counts.  The mode was smoke-tested at `k=4,r=2`:
`delta_+ + delta_- = E` on every emitted row, and aggregating by `(j,h,E)`
recovers the ordinary `spectrum_k4_exact.csv` rows for `r=2`.  The `k=4,r=3`
defect profile is intentionally not rerun as a default check because it again
requires enumerating `12!` permutations.

The exact `k=4,r=1,2,3` bidefect table is now stored as
`spectrum_k4_defect_exact.csv` (287 data rows).  The `r=1` rows are the
one-block active rows needed for the connected-component extraction below.
The table was checked by aggregating back to `spectrum_k4_exact.csv` and by
verifying `delta_+ + delta_- = E` on every row.  The `r=3` defect run took
about 248 seconds on this machine.

The helper `defect_profile.py` summarizes this output.  At `k=4,r=2`, the
ordinary energy aggregate is

| E | count |
|---:|---:|
| 4 | 1648 |
| 6 | 5428 |
| 8 | 11665 |
| 10 | 11760 |
| 12 | 7820 |
| 14 | 1472 |
| 16 | 176 |

The dominant bidefect splits are balanced:

| E | dominant `(delta_+,delta_-)` | count |
|---:|---|---:|
| 4 | `(2,2)` | 1598 |
| 6 | `(2,4)` and `(4,2)` | 2714 each |
| 8 | `(4,4)` | 10289 |
| 10 | `(4,6)` and `(6,4)` | 5880 each |
| 12 | `(6,6)` | 7436 |
| 14 | `(6,8)` and `(8,6)` | 736 each |
| 16 | `(8,8)` | 176 |

At `k=4,r=3`, the energy aggregate is

| E | count |
|---:|---:|
| 6 | 47440 |
| 8 | 947696 |
| 10 | 5423150 |
| 12 | 22109989 |
| 14 | 56792056 |
| 16 | 108113076 |
| 18 | 126933856 |
| 20 | 105245904 |
| 22 | 41506048 |
| 24 | 10798848 |

The same balanced-defect pattern persists at the dominant splits:

| E | dominant `(delta_+,delta_-)` | count |
|---:|---|---:|
| 6 | `(2,4)` and `(4,2)` | 23595 each |
| 8 | `(4,4)` | 867026 |
| 10 | `(4,6)` and `(6,4)` | 2701255 each |
| 12 | `(6,6)` | 18092021 |
| 14 | `(6,8)` and `(8,6)` | 28075388 each |
| 16 | `(8,8)` | 88649332 |
| 18 | `(8,10)` and `(10,8)` | 63115824 each |
| 20 | `(10,10)` | 92918480 |
| 22 | `(10,12)` and `(12,10)` | 20753024 each |
| 24 | `(12,12)` | 10798848 |

This is diagnostic only, but it identifies the low-window structure that a
`k=4` proof must control.

The script `genus_frontier.py` benchmarks one-sided genus-count estimates
against the CL threshold.  If a one-sided plus-defect/genus count obeys

```text
count(g) <= exp(O(r)) r^(eta g),
```

then the bidefect intersection gives the proportional entropy benchmark

```text
beta_k(alpha) <= eta alpha / 4.
```

For `k=4`, a Chapuy-style `eta=3` benchmark closes only

```text
2 <= alpha <= 16/7.
```

It does not close the remaining window up to `14/3`.  An `eta=2` one-sided
genus exponent would close the whole `k=4` window.  Thus the next analytic
target is precise: either improve the effective one-sided genus exponent below
the crude `3g` slicing cost, or exploit genuinely two-sided/balanced bidefect
structure.

The same algebra is even more useful for the all-even problem.  Because the
high-energy cutoff has already reduced CL to the central window
`0 <= alpha <= 2k`, the critical leading one-sided exponent is

```text
eta <= 2
```

for every even `k`: it gives `beta_k(alpha) <= alpha/2`, which is below the CL
threshold exactly for `alpha <= 2k`.  This is a strict leading closure only
when `eta<2`.  At `eta=2`, the endpoint `alpha=2k` is an equality case, so an
`exp(O(r))` prefactor still leaves a genuine boundary-layer problem at the
`o(a_d)` level.  The command

```bash
python3 cl_probe/genus_frontier.py --table-k-max 12 --eta 2
```

now prints `central_window_status=critical_boundary` for every listed even
`k`.  This is a theorem target, not a proved estimate: the remaining difficulty
is to prove a strict `eta<2` estimate, or prove the `eta=2` estimate with
enough boundary-layer constants/subexponential control, or replace it with an
equally strong two-sided entropy estimate.

The exact `k=4,r<=3` bidefect CSV gives a small sanity check for the target.
Aggregating by plus defect and testing `eta=2`,

```bash
python3 cl_probe/one_sided_defect_sanity.py \
  cl_probe/spectrum_k4_defect_exact.csv --eta 2
```

reports worst required exponential base

```text
r=3, plus_defect=6, g=3, count=58992100,
A_needed=43.2535850323.
```

This is consistent with a bound of the form `A^r r^(2g)` at the exact small
sizes currently available, but it is only a sanity check and gives no
asymptotic proof.

The crude one-sided cycle-count bound was separated out in
`one_sided_cycle_frontier.py`.  If `delta_+=d r`, it gives

```text
beta_+(d) <= (k - 1 + d)/2.
```

For a one-sided target exponent `eta`, this closes only

```text
d >= (k - 1)/(eta - 1).
```

At the critical `eta=2` this means `d >= k-1`.  Thus plain cycle counts already
control the high plus-defect edge, including the top central density `d=k`, but
they do not prove the global one-sided estimate.  The missing topological
input is concentrated at lower plus-defect densities.

The standard connected-map plus labelled-SET benchmark was also separated out.
With

```text
M = r - c(pi),        G_ns = sum non-singleton g_+,
```

the standard connected estimate `exp(O(t))t!t^(3g_+)` gives the leading
one-sided benchmark

```text
beta_+ <= M/r + 3G_ns/r.
```

The critical `eta=2` target asks for `beta_+ <= delta_+/r`; on the
non-singleton part this is `2(M+G_ns)/r`, so the map/SET benchmark closes
`G_ns <= M`.  Singleton components can have positive one-sided genus, but they
are finite one-block types and contribute only `exp(O(r))`, so they do not
count toward the `r log r` entropy budget.  The cycle-count edge closes
`delta_+/(2r) >= (k-1)/2`.  Thus the current remaining benchmark gap is

```text
G_ns > M
and
delta_+/(2r) < (k-1)/2.
```

This is printed by `one_sided_balance_frontier.py`.  It is not a proof of CL;
it is a sharper localization of the still-missing one-sided entropy estimate.
The exact `k=4,r<=3` connected table has no open non-singleton rows under this
classification; the only benchmark-open connected rows are singleton finite
types.  The reproducible command

```bash
python3 cl_probe/connected_balance_sanity.py \
  cl_probe/spectrum_k4_defect_exact.csv --k 4
```

prints the status counts

| status | row count |
|---|---:|
| map_set_closes | 21 |
| cycle_closes | 16 |
| singleton_finite | 3 |
| open_non_singleton | 0 |

This `k=4` vanishing has an integer explanation.  For a connected
non-singleton component on `t` blocks, benchmark-open rows would need

```text
g_+ >= t
and
(t-1+g_+)/t < (k-1)/2.
```

At `k=4` this interval is empty for every `t`.  At `k=6`, it is already
nonempty for `t=2`, where `2 <= g_+ <= 3`.  The script
`one_sided_integer_open_ranges.py` prints this component-level obstruction
table.

An exact two-block enumeration confirms that the first `k=6,t=2` open range is
not merely a formal interval.  Running

```bash
./cl_probe/bin/two_block_open_exact --k 6
```

enumerates all `12!` permutations, keeps the `478483200` connected two-block
components, and gives:

| plus defect | `g_+` | status | exact count |
|---:|---:|---|---:|
| 2 | 0 | map_set_closes | 1280664 |
| 4 | 1 | map_set_closes | 22173480 |
| 6 | 2 | open_benchmark | 120689352 |
| 8 | 3 | open_benchmark | 220048920 |
| 10 | 4 | cycle_closes | 108156384 |
| 12 | 5 | cycle_closes | 6134400 |

The exact open rows are therefore large.  This still does not prove or refute
CL: it identifies the first concrete component class that any complete
all-even argument must control.

The same compiled enumerator has a bidefect mode:

```bash
./cl_probe/bin/two_block_open_exact --k 6 --bidefect
```

It was checked at `k=4` against the tracked exact defect CSV.  For `k=6`, the
largest bidefect rows are:

| plus | minus | `g_+` | `g_-` | exact count |
|---:|---:|---:|---:|---:|
| 8 | 8 | 3 | 3 | 113801916 |
| 6 | 8 | 2 | 3 | 51133800 |
| 8 | 6 | 3 | 2 | 51133800 |
| 6 | 6 | 2 | 2 | 48133578 |
| 8 | 10 | 3 | 4 | 47859006 |
| 10 | 8 | 4 | 3 | 47859006 |
| 10 | 10 | 4 | 4 | 45938244 |

The open-open quadrant `g_+,g_- in {2,3}` contains `264203094` permutations,
about `55.2%` of the connected two-block class.  Thus the first finite
`k=6` obstruction is genuinely two-sided and balanced, not merely one-sided.
Because `t=2` is fixed, this remains finite-type data and is not itself a
diagonal obstruction; it tells us what a future unbounded-component argument
must not ignore.

A sharper finite-type check changes the interpretation of this obstruction.
For any fixed finite catalogue of connected component types with block sizes
bounded independently of the global `r`, the labelled SET construction has
leading entropy only

```text
beta_+ = M/r,
```

while the internal one-sided genera contribute only `exp(O(r))`.  Therefore a
fixed connected type with `t` blocks and genus `g_+` has finite-type leading
margin

```text
(t-1)/t - 2(t-1+g_+)/t,
```

against the critical `eta=2` one-sided target.  This is always negative for a
nontrivial fixed type.  Running

```bash
python3 cl_probe/finite_type_frontier.py --k 6 --t-max 12
```

prints `finite_type_closes`; the worst listed open row is precisely the first
`t=2,g_+=2` row, with margin `-2.5`.  Thus the exact `k=6,t=2` rows are a real
diagnostic of where the crude `t^(3g_+)` benchmark overcounts, but they are
not themselves a diagonal obstruction.  The remaining all-even danger must
come from component sizes growing with `r`, or from an entropy source not
covered by this finite-catalogue SET estimate.

For that unbounded-component regime, the eta thresholds split into two
different questions.  Running

```bash
python3 cl_probe/eta_requirement_table.py --table-k-max 20
```

prints the local benchmark-open `y=g_+/t` window, the one-sided eta ceiling,
and the direct full-CL component threshold.  The first values are:

| k | open `y` window | one-sided eta ceiling | direct `eta_crit(k)` |
|---:|---|---:|---:|
| 4 | empty | none | 5 |
| 6 | `1<y<1.5` | 2.66666666667 | 1.46153846154 |
| 8 | `1<y<2.5` | 2.4 | 1.24242424242 |
| 10 | `1<y<3.5` | 2.28571428571 | 1.16393442623 |
| 12 | `1<y<4.5` | 2.22222222222 | 1.12371134021 |

So a local one-sided `eta=2` bound is not the leading obstruction inside the
open connected window.  The direct component strategy for the full CL
threshold is much stricter: it needs `eta <= eta_crit(k)`, which is already
`19/13` for `k=6` and tends to `1`.  This is why the remaining all-even proof
needs either a genuinely sharper unbounded-component count or a different
global two-sided/bidefect argument.

The local two-sided version is printed by

```bash
python3 cl_probe/bidefect_local_threshold.py --k 6 --s-step 0.25
```

with `s=(g_+ + g_-)/t` and `alpha_local=4+2s`.  It shows:

| `s` | `alpha_local` | allowed eta | margin at eta `2` |
|---:|---:|---:|---:|
| 1.5 | 7 | 1.90476190476 | 0.142857142857 |
| 2 | 8 | 1.64285714286 | 0.714285714286 |
| 2.5 | 9 | 1.48571428571 | 1.28571428571 |
| 2.6 | 9.2 | 1.46153846154 | 1.4 |

So for `k=6`, even a total-bidefect `eta=2` estimate is too weak for this
direct route near the cycle-count boundary.  The local endpoint value is again
`19/13`.  This narrows the remaining target: either prove a much sharper
two-sided count in this local window, or abandon the direct component-count
route.

There is a sharper intersection benchmark that does not count by the total
bidefect.  A bidefect class with fixed `(g_+,g_-)` is contained in the
one-sided plus-genus class and also in the one-sided minus-genus class.  Thus
a one-sided estimate

```text
count(t,g) <= exp(O(t)) t! t^(eta_min g)
```

would imply the two-sided intersection envelope

```text
count(t,g_+,g_-) <= exp(O(t)) t! t^(eta_min min(g_+,g_-)).
```

At fixed `s=(g_+ + g_-)/t`, the worst split for this bound is balanced, so
the local leading entropy becomes

```text
beta_local <= 1 + eta_min s/2.
```

The new calculator

```bash
python3 cl_probe/bidefect_min_genus_threshold.py --table-k-max 20
```

compares this min-genus route with the same CL threshold.  With the standard
Chapuy one-sided exponent `eta_min=3`, it reports:

| k | `s_cycle` | critical `eta_min` | closed `s` range at `eta_min=3` | verdict |
|---:|---:|---:|---|---|
| 4 | 0.333333333333 | 10 | all pre-cycle | closes |
| 6 | 2.6 | 2.92307692308 | `s <= 2.44444444444` | leaves `2.44444444444<s<2.6` |
| 8 | 4.71428571429 | 2.48484848485 | `s <= 2.72727272727` | leaves endpoint window |
| 10 | 6.77777777778 | 2.32786885246 | `s <= 2.92307692308` | leaves endpoint window |
| 12 | 8.81818181818 | 2.24742268041 | `s <= 3.06666666667` | leaves endpoint window |

This is meaningful progress in the proof architecture: for `k=6`, the usual
one-sided `t^(3g)` input plus intersection leaves only the narrow leading
window

```text
2.44444444444 < s < 2.6
```

before cycle-count takeover.  It still does not settle general even `k`; for
larger `k`, the remaining endpoint window is wide.  The all-even proof would
need either an improved one-sided exponent below the listed critical
`eta_min`, or a genuinely two-sided estimate stronger than the min-genus
intersection.

The lattice version of this statement is printed by

```bash
python3 cl_probe/bidefect_remaining_lattice.py --k 6 --t-max 20
```

It lists integer pairs `(g_+,g_-)` that are still before cycle-count takeover
and not closed by the `eta_min=3` min-genus bound.  This is only a candidate
list; it does not assert that the corresponding bidefect rows are populated.
For `k=6,t<=20`, the first remaining candidate is

| t | `g_+` | `g_-` | `s` | leading alpha | margin |
|---:|---:|---:|---:|---:|---:|
| 4 | 5 | 5 | 2.5 | 9 | 0.0357142857143 |

The worst listed candidate in this range is

| t | `g_+` | `g_-` | `s` | leading alpha | margin |
|---:|---:|---:|---:|---:|---:|
| 17 | 22 | 22 | 2.58823529412 | 9.17647058824 | 0.0924369747899 |

The remaining candidate counts by `t` through `20` are:

| t | count |
|---:|---:|
| 4 | 1 |
| 7 | 1 |
| 8 | 1 |
| 11 | 1 |
| 12 | 1 |
| 13 | 1 |
| 14 | 1 |
| 15 | 1 |
| 16 | 1 |
| 17 | 2 |
| 18 | 1 |
| 19 | 2 |
| 20 | 1 |

For `k=8`, the same lattice already has remaining candidates at `t=2`; through
`t=12` it lists `295` remaining candidates.  This confirms that the min-genus
route is a strong localization for `k=6`, but not an all-even closure.

For `k=6`, the remaining lattice has an exact arithmetic form.  The script

```bash
python3 cl_probe/k6_remaining_arithmetic.py --t-max 40
```

uses integer arithmetic to list rows satisfying

```text
g_+ <= g_-,
5(g_+ + g_-) < 13t,
15g_+ - 6g_- > 11t.
```

The first inequality is the pre-cycle condition
`4+2(g_+ + g_-)/t < 9.2`; the second is exactly the failure of the
`eta_min=3` min-genus closure.  Balanced rows reduce to the rational interval

```text
11/9 < g/t < 13/10.
```

Through `t<=20`, this exact arithmetic reproduces the previous lattice:
`15` remaining rows, `14` of them balanced, first at `t=4`.  Through `t<=40`,
it gives `86` remaining rows, `60` balanced.  The first non-balanced candidate
in the `t<=20` list is `(t,g_+,g_-)=(19,24,25)`.

The balanced strip has length

```text
(13/10 - 11/9)t = 7t/90.
```

Therefore every `t>=13` has at least one balanced lattice candidate.  This is
now the cleanest `k=6` proof target: either show that the connected bidefect
count is smaller on this infinite narrow rational strip, or construct enough
of this strip to breach the CL variational bound.

The arithmetic strip still needs entropy.  The calculator

```bash
python3 cl_probe/k6_strip_entropy_threshold.py --t-max 40
```

prints the connected-count exponent required for a balanced row to threaten
CL.  If

```text
count(t,g,g) = exp((beta+o(1)) t log t),
```

then one needs

```text
beta > T_6(4+4g/t) = (6/7)(3+2g/t).
```

On the listed strip this required exponent lies roughly between `4.67` and
`4.80`.  Through `t<=40`, the largest gap between the current min-genus upper
envelope `1+3g/t` and the CL threshold is only

```text
0.0965250965251
```

at `(t,g)=(37,48)`.  A single witness for each `t` has exponent `beta=0`, so
the finite witnesses above are far below a diagonal obstruction by themselves.
The remaining `k=6` proof problem is therefore genuinely an entropy estimate
on this strip, not an existence problem.

The finite population sampler

```bash
python3 cl_probe/k6_strip_population_sampler.py --t 7 \
  --samples 500000 --seed 20260618
```

estimates the actual row count in the balanced strip by sampling uniform
permutations.  Three reproducible finite checks are:

| t | g | samples | hits | beta estimate | beta required | margin | comment |
|---:|---:|---:|---:|---:|---:|---:|---|
| 4 | 5 | 50000 | 408 | 9.01255528583 | 4.71428571429 | 4.29826957154 | dense finite row |
| 7 | 9 | 500000 | 4 | 7.78451831653 | 4.77551020408 | 3.00900811245 | sparse, high variance |
| 8 | 10 | 500000 | 0 | none | 4.71428571429 | none | no hit observed |

These numbers are finite-`t` diagnostics.  They do not prove a diagonal breach:
the `t=7` estimate is based on only four hits, and `t=8` has no hit in the
listed budget.  They do show that small populated strip rows can have large
finite beta estimates, while the observed population becomes sparse quickly.

The no-hit `t=8` uniform-sampling result is not an emptiness statement.  The
targeted local search

```bash
python3 cl_probe/bidefect_target_local_search.py \
  --k 6 --t 8 --g 10 --seed 424242
```

optimizes the two cycle-sum equations directly and finds a connected witness.
With similar budgets it also finds balanced-strip witnesses at `t=11,12,13`.
The verified rows are:

| t | g | seed | `#pi` | `#(gamma*pi)` | `#(pi*gamma^{-1})` | plus/minus defect |
|---:|---:|---:|---:|---:|---:|---:|
| 8 | 10 | 424242 | 16 | 6 | 6 | 34 |
| 11 | 14 | 424243 | 20 | 9 | 9 | 48 |
| 12 | 15 | 424244 | 22 | 10 | 10 | 52 |
| 13 | 16 | 424245 | 25 | 10 | 10 | 56 |

The strip sweep

```bash
python3 cl_probe/k6_balanced_strip_target_sweep.py \
  --t-min 13 --t-max 40 --restarts 4 --steps 20000 --seed 424242
```

searches every balanced lattice candidate in the exact strip for
`13<=t<=40`.  It finds connected witnesses in all `55` searched rows, with no
misses.  In particular, it finds a witness at the previous worst finite
entropy-room row `(t,g)=(37,48)`.  Thus, at the current finite frontier, the
balanced strip is not an artifact of arithmetic inequalities: it is populated.
This still does not estimate the number of such witnesses, so it does not
settle the entropy question.

The same finite nonemptiness statement is now auditable without rerunning the
stochastic search.  The tracked certificate file

```text
cl_probe/k6_balanced_strip_witnesses_t13_t40.csv
```

stores explicit permutation images for all `55` found rows.  The deterministic
verifier

```bash
python3 cl_probe/k6_balanced_strip_certificates.py \
  --verify cl_probe/k6_balanced_strip_witnesses_t13_t40.csv
```

recomputes the three cycle counts, plus/minus defects, balanced genera, and
connectedness for every row, and reports `verified_rows=55`.

The neutral-move profiler

```bash
python3 cl_probe/k6_balanced_strip_neutral_moves.py \
  cl_probe/k6_balanced_strip_witnesses_t13_t40.csv
```

then enumerates all single image-swaps around each certificate and counts
which swaps remain in the same balanced row.  Across the same `55` rows it
finds:

| statistic | value |
|---|---:|
| minimum connected row-preserving swaps | 222 |
| median connected row-preserving swaps | 638 |
| maximum connected row-preserving swaps | 1599 |
| minimum connected density among all image-swaps | 0.0256202179457 |
| median connected density among all image-swaps | 0.0406091370558 |
| maximum connected density among all image-swaps | 0.106969520481 |

For these certificates every row-preserving single swap was still connected,
and no one-swap neighbor kept the exact original cycle-count triple.  This
shows that the saved witnesses are not isolated inside their balanced rows.
It is still only polynomial local multiplicity; the proxy
`log(neutral_degree)/(t log t)` ranges from about `0.045` to `0.162`, far
below the strip threshold near `4.7--4.8`.

The shape profiler

```bash
python3 cl_probe/k6_balanced_strip_shape_profile.py \
  cl_probe/k6_balanced_strip_witnesses_t13_t40.csv
```

records how the forced balanced-row equation

```text
#pi + #(gamma*pi) = #pi + #(pi*gamma^{-1}) = 5t + 2 - 2g
```

is split in the certificates.  In the `t=13..40` profile,
`#pi/t` ranges from `1.71428571429` to `2.1`, while the side count
`#(gamma*pi)/t = #(pi*gamma^{-1})/t` ranges from `0.448275862069` to
`0.866666666667`, with median `0.6`.  The side products have much larger
largest cycles than `pi`: median largest-cycle fractions are about `0.268`
and `0.273` for the two side products, versus about `0.079` for `pi`.
Thus this certificate set is not concentrated on one rigid cycle-count split;
a real count must control a broad family of side-cycle shapes.  This is a
finite structural diagnostic, not a substitute for the missing asymptotic
entropy bound.

There is one more arithmetic refinement.  At fixed balanced row `(t,g,g)`, put

```text
p = #pi,
q = #(gamma*pi) = #(pi*gamma^{-1}).
```

The row equation forces

```text
p+q = 5t+2-2g.
```

The three-cycle-count envelope at this fixed split gives

```text
beta <= 6 - max(p,q)/t.
```

Comparing with the row threshold `(6/7)(3+2g/t)`, a split is still strictly
open only if

```text
max(p,q) < 12(2t-g)/7.
```

The command

```bash
python3 cl_probe/k6_balanced_split_window.py --t-min 13 --t-max 40 \
  --certificates cl_probe/k6_balanced_strip_witnesses_t13_t40.csv
```

finds `12` balanced rows through `t=40` with strict open split slots and `3`
with boundary split slots.  The first strict open slot is

```text
(t,g,p,q) = (22,27,29,29).
```

None of the `55` certified witnesses lands in a strict open split slot.  They
all have `max(p,q)` comfortably above the split threshold, so each certified
witness row is already safe under the split-refined cycle-count envelope.  The
remaining possible `k=6` danger is therefore sharper still: one must populate
and count the near-balanced cycle-count split slots, not merely the balanced
bidefect strip.

The split-target search

```bash
python3 cl_probe/k6_balanced_split_target_search.py \
  --t-min 13 --t-max 40 --seed 20260617 --restarts 4 --steps 15000
```

then targets precisely those strict open split slots.  It searches `17`
strict split triples and finds no exact connected hit in this finite budget:

| statistic | value |
|---|---:|
| strict split targets searched | 17 |
| found | 0 |
| missed | 17 |
| minimum best score | 2 |
| median best score | 2 |
| maximum best score | 9 |
| targets with best score `2` | 11 |

The first strict target `(t,g,p,q)=(22,27,29,29)` missed with best score `2`,
at the connected triple `(29,27,29)`.  This is not an emptiness theorem; it is
a sharper finite diagnostic.  The live obstruction is now a concrete
population/count question for these near-balanced split slots, and the current
generic local search does not immediately populate them.

The strict split slots themselves are not a finite accident.  For a balanced
ratio `y=g/t`, the continuous strict split width is

```text
(13 - 10y)t/7.
```

Summing over the balanced strip `11/9<y<13/10` gives the leading cumulative
arithmetic sizes

```text
strict rows  ~ (7/180) T^2,
strict slots ~ (7/4860) T^3.
```

The reproducible command

```bash
python3 cl_probe/k6_balanced_split_asymptotics.py
```

stores these finite ratios in `k6_balanced_split_asymptotics_t13.csv`.
Through `T=400` it counts `5500` strict rows and `79431` strict slots, with
ratios already at about `0.884` and `0.862` of the respective leading terms.
This is still only arithmetic target-slot counting.  It neither constructs
permutations in those slots nor bounds their entropy; it says the strict split
window persists at cubic arithmetic scale.

A cheap sign-parity obstruction does not close these slots.  For
`n=6t` and `gamma` a product of `t` six-cycles, the parity identity

```text
#(gamma*pi) - #pi == t    mod 2
```

is necessary.  Running

```bash
python3 cl_probe/k6_balanced_split_invariant_sanity.py --t-min 13 --t-max 80 \
  --target-search-csv cl_probe/k6_balanced_split_target_search_t13_t40.csv
```

checks all `333` strict arithmetic slots through `t=80`; all satisfy this
parity relation.  The same diagnostic summarizes the bounded target-search
misses through `t=40`: `11` of `17` strict targets reached score `2`, always
by being short by `2` in exactly one of the three requested cycle counts.  This
points away from plain sign parity as an obstruction.

Saving the best near-hit permutations and enumerating their one-swap
neighborhoods changes the finite picture: one strict slot is actually
populated.  The commands

```bash
python3 cl_probe/k6_balanced_split_target_search.py \
  --t-min 13 --t-max 40 --seed 20260617 --restarts 4 --steps 15000 \
  --emit-permutation > cl_probe/k6_balanced_split_target_search_best_t13_t40.csv
python3 cl_probe/k6_strict_split_near_hit_local_profile.py \
  cl_probe/k6_balanced_split_target_search_best_t13_t40.csv \
  > cl_probe/k6_strict_split_near_hit_local_profile_t13_t40.csv
python3 cl_probe/k6_strict_split_zero_neighbor_extract.py \
  cl_probe/k6_balanced_split_target_search_best_t13_t40.csv \
  cl_probe/k6_strict_split_near_hit_local_profile_t13_t40.csv \
  > cl_probe/k6_strict_split_zero_neighbor_witnesses_t13_t40.csv
```

extract a connected witness at

```text
(t,g,p,q) = (39,48,50,51).
```

Its verified cycle data are

```text
#pi = 50,
#(gamma*pi) = #(pi*gamma^{-1}) = 51,
g_+ = g_- = 48,
components = 1.
```

This is strictly open because

```text
max(p,q)=51 < 12(2t-g)/7 = 360/7.
```

Only `1` of the `17` saved near-hit neighborhoods contains a zero-score
one-swap neighbor; the remaining local minima have minimum neighbor scores
`3`, `5`, `6`, or `7`.  This proves that the strict split window is not empty
at finite size, but it is still not an entropy estimate.  A single witness has
zero `t log t` exponent.

A deterministic steepest one-swap descent does not uncover more strict
witnesses from the same saved near-hits.  The command

```bash
python3 cl_probe/k6_strict_split_local_descent.py \
  cl_probe/k6_balanced_split_target_search_best_t13_t40.csv \
  --max-rounds 8 --emit-permutation \
  > cl_probe/k6_strict_split_local_descent_t13_t40.csv
```

finds the same zero-score witness at `(39,48,50,51)`.  Of the other `16`
targets, all stop at one-swap local minima.  The final score distribution is

```text
score 0: 1
score 2: 13
score 4: 2
score 6: 1
```

The only additional moving paths are

```text
(t,g,p,q)=(40,49,52,52): 9 -> 6 -> 5 -> 2,
(t,g,p,q)=(40,49,53,51): 6 -> 5 -> 2.
```

This makes the finite obstruction more concrete: near the strict split slots,
simple one-swap descent usually lands on score-2 local minima rather than
constructing a large family of exact strict witnesses.

On the constructive side, the strict witness is not isolated across component
size.  The command

```bash
python3 cl_probe/k6_strict_split_block_growth.py \
  cl_probe/k6_strict_split_zero_neighbor_witnesses_t13_t40.csv \
  --emit-permutation \
  > cl_probe/k6_strict_split_block_growth_t39_to_t40.csv
```

starts from the `t=39` witness, adds one new six-point block, and swaps one
old image with one new image.  This finite deterministic search finds all four
strict split targets at `t=40`:

| target `(t,g,p,q)` | checked candidates | bridge | new block image |
|---|---:|---|---|
| `(40,49,51,53)` | `47737` | `0:234` | `234 236 237 239 235 238` |
| `(40,49,52,52)` | `14041` | `0:234` | `234 235 237 239 236 238` |
| `(40,49,53,51)` | `22465` | `0:234` | `234 235 238 239 236 237` |
| `(40,50,51,51)` | `89857` | `0:234` | `234 237 238 239 235 236` |

Each row verifies with `components=1` and with the requested three cycle
counts.  This is still finite constructive evidence, not an entropy theorem;
but it changes the search target again.  The strict split witness at `t=39`
has at least one simple add-a-block bridge that populates every strict
arithmetic slot at the next size.

The same bridge pattern continues for several more sizes.  The fixed-bridge
probe keeps the old permutation, swaps old domain `0` with the first new
domain, and varies only the internal permutation of the new six-point block.
The reproducible commands are

```bash
python3 cl_probe/k6_strict_split_fixed_bridge_growth.py \
  cl_probe/k6_strict_split_block_growth_t39_to_t40.csv \
  --found-only --emit-permutation \
  > cl_probe/k6_strict_split_fixed_bridge_growth_t40_to_t41.csv
python3 cl_probe/k6_strict_split_fixed_bridge_growth.py \
  cl_probe/k6_strict_split_fixed_bridge_growth_t40_to_t41.csv \
  --found-only --emit-permutation \
  > cl_probe/k6_strict_split_fixed_bridge_growth_t41_to_t42.csv
python3 cl_probe/k6_strict_split_fixed_bridge_growth.py \
  cl_probe/k6_strict_split_fixed_bridge_growth_t41_to_t42.csv \
  --found-only --emit-permutation \
  > cl_probe/k6_strict_split_fixed_bridge_growth_t42_to_t43.csv
python3 cl_probe/k6_strict_split_fixed_bridge_growth.py \
  cl_probe/k6_strict_split_fixed_bridge_growth_t42_to_t43.csv \
  --found-only \
  > cl_probe/k6_strict_split_fixed_bridge_growth_t43_to_t44_summary.csv
```

They give the following finite propagation summary:

| step | source rows | target rows tested | found rows | strict target slots hit |
|---|---:|---:|---:|---|
| `40 -> 41` | `4` | `8` | `6` | all `2` |
| `41 -> 42` | `6` | `12` | `12` | all `2` |
| `42 -> 43` | `12` | `24` | `24` | all `2` |
| `43 -> 44` | `24` | `96` | `96` | all `4` |

This is the strongest constructive warning so far.  The strict split window is
not just populated; at least along this tested chain, a very rigid fixed
bridge propagates witnesses and hits every strict target slot through `t=44`.
It still does not decide CL.  To threaten the diagonal, one needs an
asymptotic lower count with `t log t` entropy, while this construction only
exhibits finite witnesses and a small set of internal block choices.

The hit-count version of the same fixed-bridge test counts all working
internal permutations of the new block.  Each source-target pair checks exactly
`6! = 720` internal choices.  The tracked summary

```bash
python3 cl_probe/k6_strict_split_fixed_bridge_hit_summary.py \
  cl_probe/k6_strict_split_fixed_bridge_hit_counts_t40_to_t41.csv \
  cl_probe/k6_strict_split_fixed_bridge_hit_counts_t41_to_t42.csv \
  cl_probe/k6_strict_split_fixed_bridge_hit_counts_t42_to_t43.csv \
  cl_probe/k6_strict_split_fixed_bridge_hit_counts_t43_to_t44.csv \
  > cl_probe/k6_strict_split_fixed_bridge_hit_summary_t40_to_t44.csv
```

gives:

| step | source-target rows | positive rows | total fixed-bridge hits | hit-count range on positive rows |
|---|---:|---:|---:|---|
| `40 -> 41` | `8` | `6` | `392` | `20..130` |
| `41 -> 42` | `12` | `12` | `954` | `20..130` |
| `42 -> 43` | `24` | `24` | `1674` | `5..130` |
| `43 -> 44` | `96` | `96` | `6996` | `6..130` |

So the fixed bridge is not a single-choice construction: many internal block
permutations work.  At the same time the number of choices per source-target
is bounded by `720` in this particular mechanism, so these finite counts do
not by themselves provide the `t log t` entropy needed to breach CL.  They
instead isolate a more precise next question: are there many independent
places/bridges to perform the same extension as `t` grows?

A representative bridge-location scan gives a first positive answer at one
step.  The command

```bash
python3 cl_probe/k6_strict_split_bridge_location_counts.py \
  cl_probe/k6_strict_split_fixed_bridge_growth_t40_to_t41.csv \
  --source-row 7 --target-g 52 --target-p 54 --target-q 54 \
  --new-domain-offsets 0 \
  > cl_probe/k6_strict_split_bridge_location_counts_t41_to_t42_sample.csv
```

uses the source row

```text
(source_t,source_g,source_p,source_q)=(41,51,53,52)
```

and targets

```text
(target_t,target_g,target_p,target_q)=(42,52,54,54).
```

It fixes the first new-domain offset and enumerates all `246=6*41` old bridge
domains.  Every old domain works, and each has exactly `114` working internal
new-block permutations:

```text
old domains checked:        246
positive old domains:       246
total witnesses found:      28044
hits per old domain:        114
```

This is the first explicit polynomial bridge-location factor in the strict
split construction.  It is still one finite step.  If such choices can be made
independently through many extensions, they could create factorial-scale
entropy; this artifact does not prove that independence.

The all-offset version of the same scan is even cleaner:

```bash
python3 cl_probe/k6_strict_split_bridge_location_counts.py \
  cl_probe/k6_strict_split_fixed_bridge_growth_t40_to_t41.csv \
  --source-row 7 --target-g 52 --target-p 54 --target-q 54 \
  --new-domain-offsets 0,1,2,3,4,5 \
  > cl_probe/k6_strict_split_bridge_location_counts_t41_to_t42_all_offsets.csv
```

It checks all `6 * 246 = 1476` old/new bridge-domain pairs.  Every pair works,
again with exactly `114` internal new-block choices:

```text
old/new bridge pairs checked: 1476
positive bridge pairs:        1476
total witnesses found:        168264
hits per bridge pair:         114
```

At the level of leading entropy, one independent bridge-location choice per
growth step would contribute a `t!`-type factor, i.e. one unit of `t log t`
entropy.  That is meaningful, but still below the strict-strip threat
threshold near `4.7--4.8`; a CL breach would require additional independent
choices or a broader construction.

A small two-step independence sample is also positive.  The extractor

```bash
python3 cl_probe/k6_strict_split_bridge_choice_extract.py \
  cl_probe/k6_strict_split_fixed_bridge_growth_t40_to_t41.csv \
  cl_probe/k6_strict_split_bridge_location_counts_t41_to_t42_all_offsets.csv \
  --old-domains 0,1,120,245 --new-domain-offsets 0 \
  > cl_probe/k6_strict_split_bridge_choice_sample_t42.csv
```

materializes four `t=42` witnesses obtained from four different old bridge
domains in the `t=41 -> t=42` step.  For each of these four sources, the next
step toward target `(43,53,55,56)` was checked over all `252=6*42` old
domains with first new-domain offset fixed.  The combined artifact
`k6_strict_split_bridge_independence_sample_t42_to_t43.csv` has

```text
sources tested:             4
old domains per source:     252
positive old domains:       1008
hits per old domain:        114
total witnesses found:      114912
```

This is still a finite sample, not an induction.  But it shows that changing
the previous old bridge domain does not immediately destroy the next
bridge-location factor.

The first `k=6` remaining candidate is not merely an empty lattice point.  The
command

```bash
python3 cl_probe/bidefect_witness_search.py \
  --k 6 --t 4 --g-plus 5 --g-minus 5 --seed 1730
```

finds an explicit connected witness on the first sampled permutation.  Its
verification data are

```text
c_pi=9,
#(gamma*pi)=3,
#(pi*gamma^{-1})=3,
plus_defect=16,
minus_defect=16,
g_+=5,
g_-=5,
alpha_exact=8,
alpha_leading=9,
min_genus_margin=0.0357142857143.
```

The permutation image is

```text
1,13,11,10,17,16,20,7,8,9,22,14,12,0,19,3,2,4,21,23,5,18,15,6
```

and in cycle notation:

```text
(0 1 13) (2 11 14 19 23 6 20 5 16) (3 10 22 15) (4 17) (18 21)
```

This is a finite existence witness for the first leftover row.  It is not a
growth estimate and does not by itself decide CL.

The companion sweep

```bash
python3 cl_probe/bidefect_witness_sweep.py \
  --k 6 --t-max 12 --max-samples 100000 --seed 20260617
```

tests the remaining candidate rows through `t=12` with a fixed budget.  It
finds witnesses for `t=4` and `t=7`, and does not find witnesses for
`t=8,11,12` within `100000` samples each:

| t | `g_+` | `g_-` | attempts | found |
|---:|---:|---:|---:|---|
| 4 | 5 | 5 | 83 | yes |
| 7 | 9 | 9 | 55242 | yes |
| 8 | 10 | 10 | 100000 | no |
| 11 | 14 | 14 | 100000 | no |
| 12 | 15 | 15 | 100000 | no |

For the second populated candidate `(t,g_+,g_-)=(7,9,9)`, the witness check
gives

```text
c_pi=11,
#(gamma*pi)=8,
#(pi*gamma^{-1})=8,
plus_defect=30,
minus_defect=30,
alpha_exact=8.57142857143,
alpha_leading=9.14285714286,
min_genus_margin=0.0816326530612.
```

A separate higher-budget check for `(t,g_+,g_-)=(8,10,10)` found no witness
in `1000000` samples with seed `1730`.  This is only negative sampling
evidence, not an emptiness proof.

The finite-size sampler

```bash
python3 cl_probe/connected_bidefect_sampler.py --k 6 --t 4 \
  --samples 50000 --seed 1730
python3 cl_probe/connected_bidefect_sampler.py --k 6 --t 6 \
  --samples 30000 --seed 1731
```

estimates connected bidefect counts by multiplying sample frequencies by
`(kt)!`.  This is noisy finite-t evidence only.  The sampler now prints the
cycle-count crossing threshold and separates the exact finite component
energy density

```text
alpha_exact = E/t
```

from the asymptotic leading coordinate

```text
alpha_leading = 4 + 2(g_+ + g_-)/t.
```

For `k=6`, the cycle-count envelope takes over at leading local alpha `9.2`,
so rows above that value are not the unresolved asymptotic local window.

The largest sampled rows by frequency are balanced, but they are already
post-cycle:

| t | plus | minus | `g_+` | `g_-` | hits | exact alpha | leading alpha | leading margin |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 4 | 20 | 20 | 7 | 7 | 7652 | 10 | 11 | 3.96977619 |
| 6 | 34 | 34 | 12 | 12 | 4263 | 11.3333333 | 12 | 2.72219662 |

With `min_hits=20`, the largest supported asymptotic pre-cycle row in the
`t=4` run is:

| t | plus | minus | `g_+` | `g_-` | hits | exact alpha | leading alpha | leading margin |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 4 | 16 | 16 | 5 | 5 | 408 | 8 | 9 | 4.29826957 |

The corresponding `t=6` run has no supported asymptotic pre-cycle row at
`min_hits=20`; the previously tempting row `(g_+,g_-)=(9,8)` has exact alpha
`9` but leading alpha `9.66666667`, already post-cycle in the asymptotic
coordinate.  This is not a diagonal verdict.  It says only that the finite-t
diagnostic has not found a benign decay mechanism in the small supported
pre-cycle data, and that the remaining proof still needs an asymptotic
two-sided/bidefect count, or a different route, before any all-even CL closure
can be claimed.

The connected bidefect extractor

```bash
python3 cl_probe/connected_defect_spectrum.py \
  cl_probe/spectrum_k4_defect_exact.csv --k 4 --top 10
```

also checks the one-sided Euler identity on exact data.  For every connected
row it verifies

```text
plus_defect  = 2(t - 1 + g_plus),
minus_defect = 2(t - 1 + g_minus),
```

with nonnegative integers `g_plus,g_minus`.  The largest connected bidefect
rows in the exact `k=4,r<=3` table are:

| rank | r | plus | minus | `g_plus` | `g_minus` | count |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 3 | 10 | 10 | 3 | 3 | 92915840 |
| 2 | 3 | 8 | 8 | 2 | 2 | 88515712 |
| 3 | 3 | 10 | 8 | 3 | 2 | 63102144 |
| 4 | 3 | 8 | 10 | 2 | 3 | 63102144 |
| 5 | 3 | 8 | 6 | 2 | 1 | 27872768 |

This confirms that the intended one-sided genus variable is the actual
connected hypermap genus in the exact enumerator.  It does not prove the global
`eta<2` or boundary-refined `eta=2` estimate.

For `k=2`, the exact structural table reaches much farther and gives an
additional sanity check.  Since `gamma^{-1}=gamma`, the two one-sided defects
coincide and `plus_defect=E/2`.  Running

```bash
python3 cl_probe/k2_one_sided_defect_sanity.py --eta 2
```

on `spectrum_k2_character.csv` through `r=28` reports a global worst required
base

```text
r=2, plus_defect=2, g=1, count=18,
A_needed=2.12132034356.
```

The worst required base by `r` then decreases in the exact table through
`r=28`.  This is finite evidence that the one-sided `A^r r^(2g)` shape is
natural in the already-closed `k=2` case, but it does not prove the all-even
estimate.

The labelled exponential formula gives a further component-level diagnostic.
After adding the exact one-block active rows to `spectrum_k4_exact.csv`, the
script `connected_spectrum.py` extracts the connected active component spectrum.
For `k=4`, the connected rows through `r=3` begin as

| r | E | connected count |
|---:|---:|---:|
| 1 | 2 | 10 |
| 1 | 4 | 5 |
| 2 | 4 | 1548 |
| 2 | 6 | 5328 |
| 2 | 8 | 11640 |
| 3 | 8 | 763136 |
| 3 | 10 | 4993280 |
| 3 | 12 | 21582464 |

In particular, the `r=3,E=6` active band is decomposable; connected
three-block components start at `E=8`, exactly as the identity
`E=4(t-1)+2h` predicts for `t=3`.

The resulting component/cycle-count benchmark says that for `k=4` and
`2 <= alpha <= 4`,

```text
beta_4(alpha) <= (5/4)(alpha - 2).
```

This closes the low part of the remaining window:

```text
2 <= alpha <= 66/17.
```

Together with the three-cycle-count high-window closure `alpha >= 14/3`, the
unresolved `k=4` proportional window is now narrowed to

```text
66/17 < alpha < 14/3.
```

A sharper conditional Task-B target is now isolated in
`k4_map_genus_frontier.py`.  Suppose the connected non-singleton `k=4`
component count on `t` labelled blocks and genus `h` satisfies

```text
connected_count(t,h) <= exp(O(t)) t! t^(3h).
```

Then a component of local energy density `a >= 4` has the map/genus envelope
`1 + (3/2)(a-4)`, while the existing cycle-count envelope gives
`3/2 + a/4`.  Optimizing over the fraction of blocks in non-singleton
components gives

```text
beta_4(alpha)
  <= max_a (alpha-2)/(a-2)
       * min(1 + (3/2)(a-4), 3/2 + a/4).
```

The two local envelopes meet at `a=26/5`.  On the remaining window
`66/17 < alpha < 14/3`, the optimized conditional envelope is explicit:

```text
beta_4(alpha) <= (7/8)(alpha-2),        2 <= alpha <= 26/5,
beta_4(alpha) <= 3/2 + alpha/4,         alpha >= 26/5.
```

The exact worst margin on the remaining `k=4` window is `-1/3`, attained at
the upper endpoint `alpha=14/3`.  On the whole central interval
`2 <= alpha <= 8`, the exact worst margin is `-2/25`, attained at
`alpha=26/5`.  Thus the exact next theorem that would close `k=4` is the
connected map/genus estimate above.  This has not been proved in the repo.

The paper-level proof packet `CL_connected_map_genus_bound.md` spells out the
standard route: translate a connected component into a bipartite hypermap,
bound the planar labelled base by `A^t t!`, and use Chapuy trisection slicing
to get the recurrence `M(t,g) <= B t^3 M(t,g-1)`.  Iterating gives
`M(t,g) <= exp(O(t)) t! t^(3g)`.  With this standard map-enumeration supplier,
the `k=4` proportional-band CL target is closed at paper level.

The sanity script `connected_bound_sanity.py` checks the shape against the
exact connected `k=4` spectrum through `t=3`.  The worst exact small connected
row is

```text
t=3, E=8, h=0, count=763136,
C_needed=(count/(t! t^(3h)))^(1/t)=50.2902232609.
```

This is consistent with the required `exp(O(t)) t! t^(3h)` form, but of course
does not prove the asymptotic estimate.

The same map/genus component strategy was stress-tested for general even `k`
in `k_map_genus_frontier.py`.  If the standard Chapuy cost
`connected_count_k(t,h) <= exp(O(t)) t! t^(3h)` is transplanted directly to
degree `k`, then the local map/genus line and the three-cycle-count line meet
at

```text
a_k = (2k + 18)/5.
```

At that density the gap to the CL threshold is

```text
(2k^2 - 9k + 2)/(5(k+1)).
```

This is `-2/25` for `k=4`, explaining the small but real margin above, but it
is already `4/7` for `k=6`.  Thus the direct `k=4` map/genus transplant does
not settle the all-even CL lemma; the remaining `k >= 6` proof must use extra
degree-`k` structure, a sharper connected-count exponent, or a different
two-sided entropy estimate.

The exact effective-exponent threshold is also now recorded.  If the component
bound had the form

```text
connected_count_k(t,h) <= exp(O(t)) t! t^(eta h),
```

then this direct component strategy would require

```text
eta <= eta_crit(k)
    = (k^2 - 3k + 1)/(k^2 - 4k + 1)
```

for `k >= 4`.  Thus `eta_crit(4)=5`, but `eta_crit(6)=19/13`; as `k` grows,
the required exponent tends to `1`.  This quantifies the obstruction: the
all-even proof needs much more than the standard genus-slicing `eta=3`.

The reproducible command

```bash
python3 cl_probe/k_map_genus_frontier.py --table-k-max 12
```

prints:

| k | `eta_crit` | pivot `a_k` at `eta=3` | worst margin | verdict |
|---:|---:|---:|---:|---|
| 2 | all | 4.4 | -0.666666666667 | closes |
| 4 | 5 | 5.2 | -0.08 | closes |
| 6 | 1.46153846154 | 6.0 | 0.571428571429 | does not close |
| 8 | 1.24242424242 | 6.8 | 1.28888888889 | does not close |
| 10 | 1.16393442623 | 7.6 | 2.03636363636 | does not close |
| 12 | 1.12371134021 | 8.4 | 2.8 | does not close |

The exact `k=4` tables are too small for the raw leading-margin diagnostic:
running `profile_cl.py` on `spectrum_k4_exact.csv` gives finite-size positive
margins at `r=2,3`.  This is not a diagonal verdict; the normalization
`r log r` is badly contaminated at such small `r`.

To probe just beyond exact brute force, `mc_spectrum.py` samples uniform
permutations and applies the same active/energy definitions.  With 100000
samples, the least favorable sampled band with at least 20 hits was:

| k | r | samples | E | hits | estimated leading margin |
|---:|---:|---:|---:|---:|---:|
| 4 | 4 | 100000 | 20 | 3481 | 2.1257 |
| 4 | 5 | 100000 | 26 | 678 | 1.7604 |
| 4 | 6 | 100000 | 32 | 104 | 1.5238 |
| 4 | 8 | 100000 | 48 | 21 | 1.1936 |
| 4 | 12 | 100000 | 86 | 31 | 0.7800 |

For `r=12`, the absolute least favorable sampled row had only one hit
(`E=78`, estimated margin `0.9315`), so the supported summary above is the more
stable headline.  These Monte Carlo numbers are noisy finite-data evidence
only.  They suggest that the visible k=4 leading-margin contamination is
decreasing with `r`, but they do not settle the remaining proportional window.

For `k=2`, the structural programs `k2_character_spectrum.py` and
`k2_character_spectrum_gmp.cpp` compute the total two-cycle-count polynomial
from symmetric-group connection coefficients for the matching class, extract
connected components by the labelled exponential formula, remove size-one
trivial components, and then group the active structures by `(j,h)`.  The
compiled GMP-backed version agrees exactly with the compiled brute-force table
through `r=6` and with the Python structural CSV through `r=20`; its `r<=26`
prefix was revalidated before accepting the `r=27..28` extension.  The `r>=7`
rows below come from this exact structural route, now extended through `r=28`.
The route uses the Jucys--Murphy content-polynomial identity for the
cycle-count transform and computes the extra rows through `r=28`.

## Exact `k=2` tables

Full brute-force CSV through `r=6`: `spectrum_k2_exact.csv`.
Full structural CSV through `r=28`: `spectrum_k2_character.csv` (2030 rows).

| r | j | h | E | count |
|---:|---:|---:|---:|---:|
| 2 | 1 | 0 | 4 | 18 |
| 2 | 1 | 2 | 8 | 2 |
| 3 | 2 | 0 | 8 | 432 |
| 3 | 2 | 2 | 12 | 160 |
| 4 | 2 | 0 | 8 | 972 |
| 4 | 2 | 2 | 12 | 216 |
| 4 | 3 | 0 | 12 | 18144 |
| 4 | 2 | 4 | 16 | 12 |
| 4 | 3 | 2 | 16 | 14736 |
| 4 | 3 | 4 | 20 | 1008 |
| 5 | 3 | 0 | 12 | 77760 |
| 5 | 3 | 2 | 16 | 37440 |
| 5 | 4 | 0 | 16 | 1119744 |
| 5 | 3 | 4 | 20 | 3200 |
| 5 | 4 | 2 | 20 | 1643520 |
| 5 | 4 | 4 | 24 | 370944 |
| 6 | 3 | 0 | 12 | 87480 |
| 6 | 3 | 2 | 16 | 29160 |
| 6 | 4 | 0 | 16 | 6765120 |
| 6 | 3 | 4 | 20 | 3240 |
| 6 | 4 | 2 | 20 | 5905440 |
| 6 | 5 | 0 | 20 | 92378880 |
| 6 | 3 | 6 | 24 | 120 |
| 6 | 4 | 4 | 24 | 970240 |
| 6 | 5 | 2 | 24 | 218549760 |
| 6 | 4 | 6 | 28 | 30240 |
| 6 | 5 | 4 | 28 | 107343360 |
| 6 | 5 | 6 | 32 | 5702400 |
| 7 | 4 | 0 | 16 | 14696640 |
| 7 | 4 | 2 | 20 | 8709120 |
| 7 | 5 | 0 | 20 | 697600512 |
| 7 | 4 | 4 | 24 | 1391040 |
| 7 | 5 | 2 | 24 | 992694528 |
| 7 | 6 | 0 | 24 | 9607403520 |
| 7 | 4 | 6 | 28 | 67200 |
| 7 | 5 | 4 | 28 | 307007232 |
| 7 | 6 | 2 | 28 | 33941053440 |
| 7 | 5 | 6 | 32 | 21224448 |
| 7 | 6 | 4 | 32 | 29955502080 |
| 7 | 6 | 6 | 36 | 5218836480 |
| 8 | 4 | 0 | 16 | 11022480 |
| 8 | 4 | 2 | 20 | 4898880 |
| 8 | 5 | 0 | 20 | 2175102720 |
| 8 | 4 | 4 | 24 | 816480 |
| 8 | 5 | 2 | 24 | 2078213760 |
| 8 | 6 | 0 | 24 | 85169968128 |
| 8 | 4 | 6 | 28 | 60480 |
| 8 | 5 | 4 | 28 | 513072000 |
| 8 | 6 | 2 | 28 | 183831137280 |
| 8 | 7 | 0 | 28 | 1210532843520 |
| 8 | 4 | 8 | 32 | 1680 |
| 8 | 5 | 6 | 32 | 41955200 |
| 8 | 6 | 4 | 32 | 98920136448 |
| 8 | 7 | 2 | 32 | 6044892456960 |
| 8 | 5 | 8 | 36 | 846720 |
| 8 | 6 | 6 | 36 | 13248668160 |
| 8 | 7 | 4 | 36 | 8562021027840 |
| 8 | 6 | 8 | 40 | 354896640 |
| 8 | 7 | 6 | 40 | 3230909337600 |
| 8 | 7 | 8 | 44 | 145297152000 |
| 9 | 5 | 0 | 20 | 3174474240 |
| 9 | 5 | 2 | 24 | 2233889280 |
| 9 | 6 | 0 | 24 | 337481883648 |
| 9 | 5 | 4 | 28 | 509483520 |
| 9 | 6 | 2 | 28 | 486815422464 |
| 9 | 7 | 0 | 28 | 12137738305536 |
| 9 | 5 | 6 | 32 | 47900160 |
| 9 | 6 | 4 | 32 | 187851073536 |
| 9 | 7 | 2 | 32 | 37694233903104 |
| 9 | 8 | 0 | 32 | 179599054602240 |
| 9 | 5 | 8 | 36 | 1612800 |
| 9 | 6 | 6 | 36 | 24424228864 |
| 9 | 7 | 4 | 36 | 32729336414208 |
| 9 | 8 | 2 | 36 | 1216154543063040 |
| 9 | 6 | 8 | 40 | 967292928 |
| 9 | 7 | 6 | 40 | 8085710905344 |
| 9 | 8 | 4 | 40 | 2563669514649600 |
| 9 | 7 | 8 | 44 | 499509338112 |
| 9 | 8 | 6 | 44 | 1732100999086080 |
| 9 | 8 | 8 | 48 | 254288281927680 |
| 10 | 5 | 0 | 20 | 1785641760 |
| 10 | 5 | 2 | 24 | 992023200 |
| 10 | 6 | 0 | 24 | 714256704000 |
| 10 | 5 | 4 | 28 | 220449600 |
| 10 | 6 | 2 | 28 | 748646841600 |
| 10 | 7 | 0 | 28 | 57242119495680 |
| 10 | 5 | 6 | 32 | 24494400 |
| 10 | 6 | 4 | 32 | 240763622400 |
| 10 | 7 | 2 | 32 | 118810302750720 |
| 10 | 8 | 0 | 32 | 1988547260276736 |
| 10 | 5 | 8 | 36 | 1360800 |
| 10 | 6 | 6 | 36 | 31752000000 |
| 10 | 7 | 4 | 36 | 70261361210880 |
| 10 | 8 | 2 | 36 | 8531637286440960 |
| 10 | 9 | 0 | 36 | 30711438336983040 |
| 10 | 5 | 10 | 40 | 30240 |
| 10 | 6 | 8 | 40 | 1702310400 |
| 10 | 7 | 6 | 40 | 14135253189120 |
| 10 | 8 | 4 | 40 | 11233730089193472 |
| 10 | 9 | 2 | 40 | 272984819342376960 |
| 10 | 6 | 10 | 44 | 25401600 |
| 10 | 7 | 8 | 44 | 1004870361600 |
| 10 | 8 | 6 | 44 | 4787111951400960 |
| 10 | 9 | 4 | 44 | 811261008142663680 |
| 10 | 7 | 10 | 48 | 17570649600 |
| 10 | 8 | 8 | 48 | 566380586151936 |
| 10 | 9 | 6 | 48 | 877207609648742400 |
| 10 | 8 | 10 | 52 | 14283827712000 |
| 10 | 9 | 8 | 52 | 277930102184017920 |
| 10 | 9 | 10 | 56 | 11058645491712000 |
| 11 | 6 | 0 | 24 | 785682374400 |
| 11 | 6 | 2 | 28 | 640185638400 |
| 11 | 7 | 0 | 28 | 155600029347840 |
| 11 | 6 | 4 | 32 | 187529126400 |
| 11 | 7 | 2 | 32 | 232437825607680 |
| 11 | 8 | 0 | 32 | 10721436646440960 |
| 11 | 6 | 6 | 36 | 25866086400 |
| 11 | 7 | 4 | 36 | 106334331586560 |
| 11 | 8 | 2 | 36 | 30851142435717120 |
| 11 | 9 | 0 | 36 | 369403967698698240 |
| 11 | 6 | 8 | 40 | 1716422400 |
| 11 | 7 | 6 | 40 | 19740663613440 |
| 11 | 8 | 4 | 40 | 27111546963578880 |
| 11 | 9 | 2 | 40 | 2119733681287495680 |
| 11 | 10 | 0 | 40 | 5953294200707481600 |
| 11 | 6 | 10 | 44 | 44352000 |
| 11 | 7 | 8 | 44 | 1562033285120 |
| 11 | 8 | 6 | 44 | 8401304440995840 |
| 11 | 9 | 4 | 44 | 4026610867207864320 |
| 11 | 10 | 2 | 44 | 67666881943122739200 |
| 11 | 7 | 10 | 48 | 42918543360 |
| 11 | 8 | 8 | 48 | 967177142046720 |
| 11 | 9 | 6 | 48 | 2763238930334023680 |
| 11 | 10 | 4 | 48 | 272118859599760588800 |
| 11 | 8 | 10 | 52 | 35218277867520 |
| 11 | 9 | 8 | 52 | 595998227575111680 |
| 11 | 10 | 6 | 52 | 436964989051758182400 |
| 11 | 9 | 10 | 56 | 34520804823859200 |
| 11 | 10 | 8 | 56 | 247179586881178828800 |
| 11 | 10 | 10 | 60 | 31986517715582976000 |
| 12 | 6 | 0 | 24 | 353557068480 |
| 12 | 6 | 2 | 28 | 235704712320 |
| 12 | 7 | 0 | 28 | 249846995059200 |
| 12 | 6 | 4 | 32 | 65473531200 |
| 12 | 7 | 2 | 32 | 286424874489600 |
| 12 | 8 | 0 | 32 | 35028443949649920 |
| 12 | 6 | 6 | 36 | 9699782400 |
| 12 | 7 | 4 | 36 | 112093918675200 |
| 12 | 8 | 2 | 36 | 72097070290882560 |
| 12 | 9 | 0 | 36 | 2217044163036561408 |
| 12 | 6 | 8 | 40 | 808315200 |
| 12 | 7 | 6 | 40 | 20186324928000 |
| 12 | 8 | 4 | 40 | 46681192608906240 |
| 12 | 9 | 2 | 40 | 8583916524469051392 |
| 12 | 10 | 0 | 40 | 76889262759849492480 |
| 12 | 6 | 10 | 44 | 35925120 |
| 12 | 7 | 8 | 44 | 1783322956800 |
| 12 | 8 | 6 | 44 | 12150922277007360 |
| 12 | 9 | 4 | 44 | 10848508777191038976 |
| 12 | 10 | 2 | 44 | 574646803022799175680 |
| 12 | 11 | 0 | 44 | 1291014370953422438400 |
| 12 | 6 | 12 | 48 | 665280 |
| 12 | 7 | 10 | 48 | 70816838400 |
| 12 | 8 | 8 | 48 | 1394081383045120 |
| 12 | 9 | 6 | 48 | 5118094745193222144 |
| 12 | 10 | 4 | 48 | 1512664919824477224960 |
| 12 | 11 | 2 | 48 | 18363975282782502912000 |
| 12 | 7 | 12 | 52 | 838252800 |
| 12 | 8 | 10 | 52 | 65848030617600 |
| 12 | 9 | 8 | 52 | 911399425670688768 |
| 12 | 10 | 6 | 52 | 1574312617644314296320 |
| 12 | 11 | 4 | 52 | 96775486307341251379200 |
| 12 | 8 | 12 | 56 | 843521817600 |
| 12 | 9 | 10 | 56 | 60271295116234752 |
| 12 | 10 | 8 | 56 | 582322956792658329600 |
| 12 | 11 | 6 | 56 | 218706903069646808678400 |
| 12 | 9 | 12 | 60 | 1028314886860800 |
| 12 | 10 | 10 | 60 | 63546154049003028480 |
| 12 | 11 | 8 | 60 | 197556982373042985369600 |
| 12 | 10 | 12 | 64 | 1547261694849024000 |
| 12 | 11 | 10 | 64 | 55006749341529263308800 |
| 12 | 11 | 12 | 68 | 1988616672221921280000 |
| 13 | 7 | 0 | 28 | 220619610731520 |
| 13 | 7 | 2 | 32 | 204277417344000 |
| 13 | 8 | 0 | 32 | 72755444961239040 |
| 13 | 7 | 4 | 36 | 72631970611200 |
| 13 | 8 | 2 | 36 | 113719876385955840 |
| 13 | 9 | 0 | 36 | 8352485701965250560 |
| 13 | 7 | 6 | 40 | 13114105804800 |
| 13 | 8 | 4 | 40 | 59758760842260480 |
| 13 | 9 | 2 | 40 | 23055318790680084480 |
| 13 | 10 | 0 | 40 | 504205083721720922112 |
| 13 | 7 | 8 | 44 | 1288993305600 |
| 13 | 8 | 6 | 44 | 14199360953057280 |
| 13 | 9 | 4 | 44 | 20855141888198492160 |
| 13 | 10 | 2 | 44 | 2562461908549909217280 |
| 13 | 11 | 0 | 44 | 17750314003419145175040 |
| 13 | 7 | 10 | 48 | 66006420480 |
| 13 | 8 | 8 | 48 | 1669775904276480 |
| 13 | 9 | 6 | 48 | 7631169234607226880 |
| 13 | 10 | 4 | 48 | 4515431661575886864384 |
| 13 | 11 | 2 | 48 | 168990991489540738252800 |
| 13 | 12 | 0 | 48 | 309843449028821385216000 |
| 13 | 7 | 12 | 52 | 1383782400 |
| 13 | 8 | 10 | 52 | 93782684835840 |
| 13 | 9 | 8 | 52 | 1245255400211496960 |
| 13 | 10 | 6 | 52 | 3168843304921458278400 |
| 13 | 11 | 4 | 52 | 596487354662299490058240 |
| 13 | 12 | 2 | 52 | 5416859713187262077337600 |
| 13 | 8 | 12 | 56 | 1964417495040 |
| 13 | 9 | 10 | 56 | 89817386696294400 |
| 13 | 10 | 8 | 56 | 866120952775094894592 |
| 13 | 11 | 6 | 56 | 895871848895788264980480 |
| 13 | 12 | 4 | 56 | 36452198266948571627520000 |
| 13 | 9 | 12 | 60 | 2282924034293760 |
| 13 | 10 | 10 | 60 | 92963234753905950720 |
| 13 | 11 | 8 | 60 | 532021093818808726978560 |
| 13 | 12 | 6 | 60 | 111325039768708937102131200 |
| 13 | 10 | 12 | 64 | 3275665847513579520 |
| 13 | 11 | 10 | 64 | 104585314030923703910400 |
| 13 | 12 | 8 | 64 | 149074500174964651877990400 |
| 13 | 11 | 12 | 68 | 5799644584906103193600 |
| 13 | 12 | 10 | 68 | 73928562564097307049984000 |
| 13 | 12 | 12 | 72 | 8664711525338893516800000 |
| 14 | 7 | 0 | 28 | 82732354024320 |
| 14 | 7 | 2 | 32 | 64347386463360 |
| 14 | 8 | 0 | 32 | 94204573782359040 |
| 14 | 7 | 4 | 36 | 21449128821120 |
| 14 | 8 | 2 | 36 | 117569824778165760 |
| 14 | 9 | 0 | 36 | 20998182336784773120 |
| 14 | 7 | 6 | 40 | 3972060892800 |
| 14 | 8 | 4 | 40 | 53825132354273280 |
| 14 | 9 | 2 | 40 | 43652300971534295040 |
| 14 | 10 | 0 | 40 | 2129906198915617554432 |
| 14 | 7 | 8 | 44 | 441340099200 |
| 14 | 8 | 6 | 44 | 12192167353766400 |
| 14 | 9 | 4 | 44 | 30764931398168647680 |
| 14 | 10 | 2 | 44 | 7710194633339886944256 |
| 14 | 11 | 0 | 44 | 125473592002661313675264 |
| 14 | 7 | 10 | 48 | 29422673280 |
| 14 | 8 | 8 | 48 | 1496633314176000 |
| 14 | 9 | 6 | 48 | 9668609739017349120 |
| 14 | 10 | 4 | 48 | 9580281553694408933376 |
| 14 | 11 | 2 | 48 | 819673576157818778812416 |
| 14 | 12 | 0 | 48 | 4505431916317980182446080 |
| 14 | 7 | 12 | 52 | 1089728640 |
| 14 | 8 | 10 | 52 | 98806422274560 |
| 14 | 9 | 8 | 52 | 1511867021845340160 |
| 14 | 10 | 6 | 52 | 4935366828881129152512 |
| 14 | 11 | 4 | 52 | 1958360355412009550217216 |
| 14 | 12 | 2 | 52 | 53621130645308119567564800 |
| 14 | 13 | 0 | 52 | 81566287956837229658112000 |
| 14 | 7 | 14 | 56 | 17297280 |
| 14 | 8 | 12 | 56 | 3110650583040 |
| 14 | 9 | 10 | 56 | 118474418495713280 |
| 14 | 10 | 8 | 56 | 1131895423688045592576 |
| 14 | 11 | 6 | 56 | 1985142763743953054072832 |
| 14 | 12 | 4 | 56 | 246962748059173856603013120 |
| 14 | 13 | 2 | 56 | 1725885779028823111001702400 |
| 14 | 8 | 14 | 60 | 30512401920 |
| 14 | 9 | 12 | 60 | 4146577302067200 |
| 14 | 10 | 10 | 60 | 119781219565143392256 |
| 14 | 11 | 8 | 60 | 825447688427564826624000 |
| 14 | 12 | 6 | 60 | 513956967612665882314014720 |
| 14 | 13 | 4 | 60 | 14518004194175217531302707200 |
| 14 | 9 | 14 | 64 | 41584044902400 |
| 14 | 10 | 12 | 64 | 5367330009173164032 |
| 14 | 11 | 10 | 64 | 136498601958256884842496 |
| 14 | 12 | 8 | 64 | 461871255752345488101212160 |
| 14 | 13 | 6 | 64 | 58039024253640113517074841600 |
| 14 | 10 | 14 | 68 | 67935252626841600 |
| 14 | 11 | 12 | 68 | 8686744282972152004608 |
| 14 | 12 | 10 | 68 | 154610617400895008365608960 |
| 14 | 13 | 8 | 68 | 109226578453160490775137484800 |
| 14 | 11 | 14 | 72 | 149374157538557952000 |
| 14 | 12 | 12 | 72 | 15912777555835345384243200 |
| 14 | 13 | 10 | 72 | 86329854297099506301272064000 |
| 14 | 12 | 14 | 76 | 375574609180824109056000 |
| 14 | 13 | 12 | 76 | 21714252836264683128225792000 |
| 14 | 13 | 14 | 80 | 725924630027890144051200000 |
| 15 | 8 | 0 | 32 | 69495177380428800 |
| 15 | 8 | 2 | 36 | 72069072838963200 |
| 15 | 9 | 0 | 36 | 35346791552961208320 |
| 15 | 8 | 4 | 40 | 30028780349568000 |
| 15 | 9 | 2 | 40 | 58084240847592960000 |
| 15 | 10 | 0 | 40 | 6215201542494469324800 |
| 15 | 8 | 6 | 44 | 6673062299904000 |
| 15 | 9 | 4 | 44 | 34323207349130219520 |
| 15 | 10 | 2 | 44 | 16838937670396236595200 |
| 15 | 11 | 0 | 44 | 582593291203361333575680 |
| 15 | 8 | 8 | 48 | 865026594432000 |
| 15 | 9 | 6 | 48 | 9847230508046131200 |
| 15 | 10 | 4 | 48 | 15827024189498967244800 |
| 15 | 11 | 2 | 48 | 2713837851912300564971520 |
| 15 | 12 | 0 | 48 | 33986658760015967246352384 |
| 15 | 8 | 10 | 52 | 65906788147200 |
| 15 | 9 | 8 | 52 | 1524949171870924800 |
| 15 | 10 | 6 | 52 | 6606528825778340659200 |
| 15 | 11 | 4 | 52 | 4547637639790244515676160 |
| 15 | 12 | 2 | 52 | 280287602470088196394844160 |
| 15 | 13 | 0 | 52 | 1247956836801022446041825280 |
| 15 | 8 | 12 | 56 | 2746116172800 |
| 15 | 9 | 10 | 56 | 129494087431188480 |
| 15 | 10 | 8 | 56 | 1370645904905935257600 |
| 15 | 11 | 6 | 56 | 3281075271839908106403840 |
| 15 | 12 | 4 | 56 | 885710780878622240960151552 |
| 15 | 13 | 2 | 56 | 18268537626557789800885125120 |
| 15 | 14 | 0 | 56 | 23375938525041822523195392000 |
| 15 | 8 | 14 | 60 | 48432384000 |
| 15 | 9 | 12 | 60 | 5607705911808000 |
| 15 | 10 | 10 | 60 | 146135397525672755200 |
| 15 | 11 | 8 | 60 | 1059054131727538104238080 |
| 15 | 12 | 6 | 60 | 1257902939652960496157982720 |
| 15 | 13 | 4 | 60 | 107304530994547709020093808640 |
| 15 | 14 | 2 | 60 | 590772518359008872811724800000 |
| 15 | 9 | 14 | 64 | 94710495559680 |
| 15 | 10 | 12 | 64 | 7551724647359692800 |
| 15 | 11 | 10 | 64 | 160246083971867505131520 |
| 15 | 12 | 8 | 64 | 778860993495440594975588352 |
| 15 | 13 | 6 | 64 | 299279397239998054201106104320 |
| 15 | 14 | 4 | 64 | 6101966203344973623019438080000 |
| 15 | 10 | 14 | 68 | 146124166783795200 |
| 15 | 11 | 12 | 68 | 11049756575024937369600 |
| 15 | 12 | 10 | 68 | 196801511751049114704936960 |
| 15 | 13 | 8 | 68 | 387328404436161029640762163200 |
| 15 | 14 | 6 | 68 | 31122805829067628310868000768000 |
| 15 | 11 | 14 | 72 | 275595178104697651200 |
| 15 | 12 | 12 | 72 | 20234004618301076402601984 |
| 15 | 13 | 10 | 72 | 207200297918003849774235648000 |
| 15 | 14 | 8 | 72 | 79061830611265574014159945728000 |
| 15 | 12 | 14 | 76 | 702896613607865843712000 |
| 15 | 13 | 12 | 76 | 37966916682768368760457789440 |
| 15 | 14 | 10 | 76 | 92491492275041387256553144320000 |
| 15 | 13 | 14 | 80 | 2032827387437788182872064000 |
| 15 | 14 | 12 | 80 | 41347949104612137592966820659200 |
| 15 | 14 | 14 | 84 | 4469069532100466957510246400000 |
| 16 | 8 | 0 | 32 | 22337735586566400 |
| 16 | 8 | 2 | 36 | 19855764965836800 |
| 16 | 9 | 0 | 36 | 38361337913996697600 |
| 16 | 8 | 4 | 40 | 7721686375603200 |
| 16 | 9 | 2 | 40 | 51858845698551091200 |
| 16 | 10 | 0 | 40 | 12728551368526324531200 |
| 16 | 8 | 6 | 44 | 1715930305689600 |
| 16 | 9 | 4 | 44 | 27069372549022003200 |
| 16 | 10 | 2 | 44 | 27024694299675994521600 |
| 16 | 11 | 0 | 44 | 1917600495253007131607040 |
| 16 | 8 | 8 | 48 | 238323653568000 |
| 16 | 9 | 6 | 48 | 7348884628448563200 |
| 16 | 10 | 4 | 48 | 20606156323332778598400 |
| 16 | 11 | 2 | 48 | 6656223560257408437780480 |
| 16 | 12 | 0 | 48 | 170921623097236199555727360 |
| 16 | 8 | 10 | 52 | 21184324761600 |
| 16 | 9 | 8 | 52 | 1150379448970752000 |
| 16 | 10 | 6 | 52 | 7517318897305715097600 |
| 16 | 11 | 4 | 52 | 8271427855320692962099200 |
| 16 | 12 | 2 | 52 | 1007866440585147454240849920 |
| 16 | 13 | 0 | 52 | 9968914608995394281055191040 |
| 16 | 8 | 12 | 56 | 1176906931200 |
| 16 | 9 | 10 | 56 | 106390817371238400 |
| 16 | 10 | 8 | 56 | 1474140787443381657600 |
| 16 | 11 | 6 | 56 | 4607643062069373206200320 |
| 16 | 12 | 4 | 56 | 2236110064177420419952803840 |
| 16 | 13 | 2 | 56 | 102169573484515660368791470080 |
| 16 | 14 | 0 | 56 | 374778983752381121143033036800 |
| 16 | 8 | 14 | 60 | 37362124800 |
| 16 | 9 | 12 | 60 | 5592836093644800 |
| 16 | 10 | 10 | 60 | 161037947711383142400 |
| 16 | 11 | 8 | 60 | 1267466178338522384302080 |
| 16 | 12 | 6 | 60 | 2232129020031268126206197760 |
| 16 | 13 | 4 | 60 | 417787321885032021086447861760 |
| 16 | 14 | 2 | 60 | 6653712498767694878189027328000 |
| 16 | 15 | 0 | 60 | 7246540942762964982190571520000 |
| 16 | 8 | 16 | 64 | 518918400 |
| 16 | 9 | 14 | 64 | 145742729932800 |
| 16 | 10 | 12 | 64 | 9484648745155584000 |
| 16 | 11 | 10 | 64 | 181520407403727750758400 |
| 16 | 12 | 8 | 64 | 1017909498033560744298086400 |
| 16 | 13 | 6 | 64 | 807702073470920649251629301760 |
| 16 | 14 | 4 | 64 | 48882315307436954946368962560000 |
| 16 | 15 | 2 | 64 | 216237732430350049687212392448000 |
| 16 | 9 | 16 | 68 | 1220496076800 |
| 16 | 10 | 14 | 68 | 262234857159475200 |
| 16 | 11 | 12 | 68 | 13345658967336073297920 |
| 16 | 12 | 10 | 68 | 216912002533193687594434560 |
| 16 | 13 | 8 | 68 | 723140842233715329594241843200 |
| 16 | 14 | 6 | 68 | 177732727486905716307164292710400 |
| 16 | 15 | 4 | 68 | 2701025382577269073567845187584000 |
| 16 | 10 | 16 | 72 | 2149816660992000 |
| 16 | 11 | 14 | 72 | 446245775597704642560 |
| 16 | 12 | 12 | 72 | 21982255053114057953771520 |
| 16 | 13 | 10 | 72 | 277097892932771331707035975680 |
| 16 | 14 | 8 | 72 | 318078989740174802522426730086400 |
| 16 | 15 | 6 | 72 | 17208611805561266093772112920576000 |
| 16 | 11 | 16 | 76 | 4430693677842432000 |
| 16 | 12 | 14 | 76 | 969520130395244542033920 |
| 16 | 13 | 12 | 76 | 43599975114665565887036129280 |
| 16 | 14 | 10 | 76 | 256582117562591995057692632678400 |
| 16 | 15 | 8 | 76 | 57171444357392757145320315420672000 |
| 16 | 12 | 16 | 80 | 12687231088866926592000 |
| 16 | 13 | 14 | 80 | 2705546161042180970486169600 |
| 16 | 14 | 12 | 80 | 79447660327857779062082843443200 |
| 16 | 15 | 10 | 80 | 93877183209004395204592369926144000 |
| 16 | 13 | 16 | 84 | 46800579195606098903040000 |
| 16 | 14 | 14 | 84 | 7805271501401864759295344640000 |
| 16 | 15 | 12 | 84 | 66770910994248647062789942149120000 |
| 16 | 14 | 16 | 88 | 178510989829271873008435200000 |
| 16 | 15 | 14 | 88 | 15452819346240605243924545536000000 |
| 16 | 15 | 16 | 92 | 483696391422230753983856640000000 |
| 17 | 9 | 0 | 36 | 24303456318184243200 |
| 17 | 9 | 2 | 40 | 27903968365322649600 |
| 17 | 10 | 0 | 40 | 18025603512793717800960 |
| 17 | 9 | 4 | 44 | 13301891729705779200 |
| 17 | 10 | 2 | 44 | 31196996683635436093440 |
| 17 | 11 | 0 | 44 | 4581349136971662517862400 |
| 17 | 9 | 6 | 48 | 3500497823606784000 |
| 17 | 10 | 4 | 48 | 20416832470519774248960 |
| 17 | 11 | 2 | 48 | 12371530084909058359296000 |
| 17 | 12 | 0 | 48 | 621631389042830533271224320 |
| 17 | 9 | 8 | 52 | 561808292677632000 |
| 17 | 10 | 6 | 52 | 6822499260962508963840 |
| 17 | 11 | 4 | 52 | 12140703835711443940147200 |
| 17 | 12 | 2 | 52 | 2724080591858468648606760960 |
| 17 | 13 | 0 | 52 | 53699402624536665336443830272 |
| 17 | 9 | 10 | 56 | 56661007295692800 |
| 17 | 10 | 8 | 56 | 1303151521986374860800 |
| 17 | 11 | 6 | 56 | 5656057474472174459289600 |
| 17 | 12 | 4 | 56 | 4428370313384455389377986560 |
| 17 | 13 | 2 | 56 | 395094539051688355985608409088 |
| 17 | 14 | 0 | 56 | 3151267403157744532137286041600 |
| 17 | 9 | 12 | 60 | 3521305538150400 |
| 17 | 10 | 10 | 60 | 147700001256702935040 |
| 17 | 11 | 8 | 60 | 1408096125975796088832000 |
| 17 | 12 | 6 | 60 | 3297950542577135656941649920 |
| 17 | 13 | 4 | 60 | 1140224946840696028231448395776 |
| 17 | 14 | 2 | 60 | 39584076973949582733757529456640 |
| 17 | 15 | 0 | 60 | 121340311474923819380774220595200 |
| 17 | 9 | 14 | 64 | 123643725004800 |
| 17 | 10 | 12 | 64 | 9758059584581468160 |
| 17 | 11 | 10 | 64 | 196887924736502346547200 |
| 17 | 12 | 8 | 64 | 1208718609389695428077813760 |
| 17 | 13 | 6 | 64 | 1548558993869997211749527322624 |
| 17 | 14 | 4 | 64 | 205469662911613812767543179345920 |
| 17 | 15 | 2 | 64 | 2580518668478859661256790795878400 |
| 17 | 16 | 0 | 64 | 2416530705965586638271550586880000 |
| 17 | 9 | 16 | 68 | 1881944064000 |
| 17 | 10 | 14 | 68 | 342951651843440640 |
| 17 | 11 | 12 | 68 | 15344547854493777920000 |
| 17 | 12 | 10 | 68 | 231145965736931549050306560 |
| 17 | 13 | 8 | 68 | 994348699813798129142423617536 |
| 17 | 14 | 6 | 68 | 526828496288607071094571133829120 |
| 17 | 15 | 4 | 68 | 23319244508695755329124508159180800 |
| 17 | 16 | 2 | 68 | 84285165622939792950382987051008000 |
| 17 | 10 | 16 | 72 | 4846834020188160 |
| 17 | 11 | 14 | 72 | 612648811327743590400 |
| 17 | 12 | 12 | 72 | 23353780494964893123870720 |
| 17 | 13 | 10 | 72 | 298573518011311767442616745984 |
| 17 | 14 | 8 | 72 | 661021906593832706673838475182080 |
| 17 | 15 | 6 | 72 | 108000412409926813178083615860326400 |
| 17 | 16 | 4 | 72 | 1256619476596428406890422712926208000 |
| 17 | 11 | 16 | 76 | 9517707775947571200 |
| 17 | 12 | 14 | 76 | 1166937886361245424025600 |
| 17 | 13 | 12 | 76 | 43269673316144857232003039232 |
| 17 | 14 | 10 | 76 | 376216138189333811630106161971200 |
| 17 | 15 | 8 | 76 | 258508174189873051790165210981990400 |
| 17 | 16 | 6 | 76 | 9824756761722980281430049690746880000 |
| 17 | 12 | 16 | 80 | 22291072634947711795200 |
| 17 | 13 | 14 | 80 | 2924166223920852566066331648 |
| 17 | 14 | 12 | 80 | 89854027687511382867617733672960 |
| 17 | 15 | 10 | 80 | 299435526525980389172890174488576000 |
| 17 | 16 | 8 | 80 | 41612685686229575766899466568728576000 |
| 17 | 13 | 16 | 84 | 73133680269266643949977600 |
| 17 | 14 | 14 | 84 | 8950770591929976337135168389120 |
| 17 | 15 | 12 | 84 | 147402212641206907333304380922265600 |
| 17 | 16 | 10 | 84 | 92137107359563304251168423145373696000 |
| 17 | 14 | 16 | 88 | 307492859392462740950876160000 |
| 17 | 15 | 14 | 88 | 25511092960564094397370568854732800 |
| 17 | 16 | 12 | 88 | 96861014985477458113005094139068416000 |
| 17 | 15 | 16 | 92 | 1324197154973156832305416765440000 |
| 17 | 16 | 14 | 92 | 39767173865300636083805157297487872000 |
| 17 | 16 | 16 | 96 | 4014826358596173785496356388864000000 |
| 18 | 9 | 0 | 36 | 6835347089489318400 |
| 18 | 9 | 2 | 40 | 6835347089489318400 |
| 18 | 10 | 0 | 40 | 16842295228501680537600 |
| 18 | 9 | 4 | 44 | 3037932039773030400 |
| 18 | 10 | 2 | 44 | 24542440305313054924800 |
| 18 | 11 | 0 | 44 | 7923976669041008842506240 |
| 18 | 9 | 6 | 48 | 787612010311526400 |
| 18 | 10 | 4 | 48 | 14345040081140600832000 |
| 18 | 11 | 2 | 48 | 17298832955054736192307200 |
| 18 | 12 | 0 | 48 | 1683187382002015400279408640 |
| 18 | 9 | 8 | 52 | 131268668385254400 |
| 18 | 10 | 6 | 52 | 4522643188099964928000 |
| 18 | 11 | 4 | 52 | 14189983289725331226378240 |
| 18 | 12 | 2 | 52 | 5704254802459938129509744640 |
| 18 | 13 | 0 | 52 | 212497758253675739340613877760 |
| 18 | 9 | 10 | 56 | 14585407598361600 |
| 18 | 10 | 8 | 56 | 857855333305235865600 |
| 18 | 11 | 6 | 56 | 5859224002157109250867200 |
| 18 | 12 | 4 | 56 | 7172377575989687516487352320 |
| 18 | 13 | 2 | 56 | 1160511364183864138533993185280 |
| 18 | 14 | 0 | 56 | 18025497322351397068236021301248 |
| 18 | 9 | 12 | 60 | 1080400562841600 |
| 18 | 10 | 10 | 60 | 101871689337376358400 |
| 18 | 11 | 8 | 60 | 1372318260338677568716800 |
| 18 | 12 | 6 | 60 | 4289203972583504543610961920 |
| 18 | 13 | 4 | 60 | 2439456648204509988554114334720 |
| 18 | 14 | 2 | 60 | 163370722124753798254585404456960 |
| 18 | 15 | 0 | 60 | 1068807364096735416339224089067520 |
| 18 | 9 | 14 | 64 | 51447645849600 |
| 18 | 10 | 12 | 64 | 7534953614271283200 |
| 18 | 11 | 10 | 64 | 191425036901471124111360 |
| 18 | 12 | 8 | 64 | 1359987915921484180777205760 |
| 18 | 13 | 6 | 64 | 2421553862532684794799021096960 |
| 18 | 14 | 4 | 64 | 603179702941470461185809086152704 |
| 18 | 15 | 2 | 64 | 16253591118211354610907530731192320 |
| 18 | 16 | 0 | 64 | 42143636211280064712034300094054400 |
| 18 | 9 | 16 | 68 | 1429101273600 |
| 18 | 10 | 14 | 68 | 328655183560704000 |
| 18 | 11 | 12 | 68 | 15907179297927562444800 |
| 18 | 12 | 10 | 68 | 242744369132893153137131520 |
| 18 | 13 | 8 | 68 | 1191482501815185554900934328320 |
| 18 | 14 | 6 | 68 | 1093739369253497943553279493406720 |
| 18 | 15 | 4 | 68 | 105294722684136763245980840330526720 |
| 18 | 16 | 2 | 68 | 1061928276007139067151558480232448000 |
| 18 | 17 | 0 | 68 | 862701462029714429862943559516160000 |
| 18 | 9 | 18 | 72 | 17643225600 |
| 18 | 10 | 16 | 72 | 7302883940352000 |
| 18 | 11 | 14 | 72 | 746554122409547612160 |
| 18 | 12 | 12 | 72 | 24710800281890373151621120 |
| 18 | 13 | 10 | 72 | 303687773596712997051926446080 |
| 18 | 14 | 8 | 72 | 976895545809371725284908029968384 |
| 18 | 15 | 6 | 72 | 349889871557587138298790364053504000 |
| 18 | 16 | 4 | 72 | 11634082353628317261179383414416998400 |
| 18 | 17 | 2 | 72 | 34856987548086039255319643147993088000 |
| 18 | 10 | 18 | 76 | 53353114214400 |
| 18 | 11 | 16 | 76 | 17003886481328947200 |
| 18 | 12 | 14 | 76 | 1375124092082215006371840 |
| 18 | 13 | 12 | 76 | 41438541617651333331603947520 |
| 18 | 14 | 10 | 76 | 415004758446769005388004390338560 |
| 18 | 15 | 8 | 76 | 597237549664091123762863170335539200 |
| 18 | 16 | 6 | 76 | 67299612031853482013740749666071347200 |
| 18 | 17 | 4 | 76 | 613255972434212061797146396924575744000 |
| 18 | 11 | 18 | 80 | 117483557500108800 |
| 18 | 12 | 16 | 80 | 36366697538579443875840 |
| 18 | 13 | 14 | 80 | 2965416590755121121755136000 |
| 18 | 14 | 12 | 80 | 84564943090563517319263549390848 |
| 18 | 15 | 10 | 80 | 490262248001557115038606665480929280 |
| 18 | 16 | 8 | 80 | 209582582666650064243272323507526041600 |
| 18 | 17 | 6 | 80 | 5795612015948199975624270460464660480000 |
| 18 | 12 | 18 | 84 | 294176267030790144000 |
| 18 | 13 | 16 | 84 | 98860388212753414750863360 |
| 18 | 14 | 14 | 84 | 8360611478243453955180802867200 |
| 18 | 15 | 12 | 84 | 176579571581949173549181761381990400 |
| 18 | 16 | 10 | 84 | 334849136182020087863674603523014656000 |
| 18 | 17 | 8 | 84 | 30643979325685522342275474087481442304000 |
| 18 | 13 | 18 | 88 | 1031118508922464714752000 |
| 18 | 14 | 16 | 88 | 367190051425364330648929566720 |
| 18 | 15 | 14 | 88 | 26734529503307303572743484814131200 |
| 18 | 16 | 12 | 88 | 247625132986386856148619146466793881600 |
| 18 | 17 | 10 | 88 | 88659773823423703425535662911152717824000 |
| 18 | 14 | 18 | 92 | 4960505300674239745228800000 |
| 18 | 15 | 16 | 92 | 1623659594063167239391392930201600 |
| 18 | 16 | 14 | 92 | 71886026731640528834545651235684352000 |
| 18 | 17 | 12 | 92 | 130670741043634415537532271401589800960000 |
| 18 | 15 | 18 | 96 | 27993823834923222568654602240000 |
| 18 | 16 | 16 | 96 | 6791394240282580241409904553754624000 |
| 18 | 17 | 14 | 96 | 85222741783513568031011195699016499200000 |
| 18 | 16 | 18 | 100 | 150531019356981090812864495616000000 |
| 18 | 17 | 16 | 100 | 18385900882909269480419075857317888000000 |
| 18 | 17 | 18 | 104 | 543849892967691838403507965132800000000 |
| 19 | 10 | 0 | 40 | 9350754818421387571200 |
| 19 | 10 | 2 | 44 | 11775024586160265830400 |
| 19 | 11 | 0 | 44 | 9688213170090639424880640 |
| 19 | 10 | 4 | 48 | 6310797490621841817600 |
| 19 | 11 | 2 | 48 | 17662721585508416945848320 |
| 19 | 12 | 0 | 48 | 3409453104794066452485242880 |
| 19 | 10 | 6 | 52 | 1915472409077632204800 |
| 19 | 11 | 4 | 52 | 12656196622119093148385280 |
| 19 | 12 | 2 | 52 | 9272346268822589492987166720 |
| 19 | 13 | 0 | 52 | 638569571483620568179220152320 |
| 19 | 10 | 8 | 56 | 365802022566908928000 |
| 19 | 11 | 6 | 56 | 4807567344169510770769920 |
| 19 | 12 | 4 | 56 | 9520547428052344655104573440 |
| 19 | 13 | 2 | 56 | 2684475144590461473124688855040 |
| 19 | 14 | 0 | 56 | 76696874277418999576341761753088 |
| 19 | 10 | 10 | 60 | 45817627068986572800 |
| 19 | 11 | 8 | 60 | 1087349706176360773386240 |
| 19 | 12 | 6 | 60 | 4876499408540237272692817920 |
| 19 | 13 | 4 | 60 | 4299073923751535461988302848000 |
| 19 | 14 | 2 | 60 | 516040848569421240192203357159424 |
| 19 | 15 | 0 | 60 | 6447958504871126962305885699833856 |
| 19 | 10 | 12 | 64 | 3777080367694233600 |
| 19 | 11 | 10 | 64 | 153656723854606544732160 |
| 19 | 12 | 8 | 64 | 1405918393558652444436725760 |
| 19 | 13 | 6 | 64 | 3314205401044357295684069621760 |
| 19 | 14 | 4 | 64 | 1385837554275339917380255116951552 |
| 19 | 15 | 2 | 64 | 71164228609105115330731240958459904 |
| 19 | 16 | 0 | 64 | 387376795449982219056475196243312640 |
| 19 | 10 | 14 | 68 | 198107734951526400 |
| 19 | 11 | 12 | 68 | 13650255724387248046080 |
| 19 | 12 | 10 | 68 | 241601173227720230307102720 |
| 19 | 13 | 8 | 68 | 1346646992415270033072209264640 |
| 19 | 14 | 6 | 68 | 1819755860283198858957578066460672 |
| 19 | 15 | 4 | 68 | 331006332549520211337528185066618880 |
| 19 | 16 | 2 | 68 | 7053629021597705081753017643622727680 |
| 19 | 17 | 0 | 68 | 15633308891829737222805655512730828800 |
| 19 | 10 | 16 | 72 | 6009847222579200 |
| 19 | 11 | 14 | 72 | 735837288191796510720 |
| 19 | 12 | 12 | 72 | 25092467654006302253383680 |
| 19 | 13 | 10 | 72 | 307084757979985845602667724800 |
| 19 | 14 | 8 | 72 | 1207268168765857731267129794101248 |
| 19 | 15 | 6 | 72 | 786202403649709969323029580629409792 |
| 19 | 16 | 4 | 72 | 56180713827165182235145275665295605760 |
| 19 | 17 | 2 | 72 | 462213566386759724928211924693077196800 |
| 19 | 18 | 0 | 72 | 328319527835308463022125948935864320000 |
| 19 | 10 | 18 | 76 | 80453108736000 |
| 19 | 11 | 16 | 76 | 21730151534362951680 |
| 19 | 12 | 14 | 76 | 1528651255523660802293760 |
| 19 | 13 | 12 | 76 | 40401616551965761621312143360 |
| 19 | 14 | 10 | 76 | 412116121358879117734946298396672 |
| 19 | 15 | 8 | 76 | 959277480407789979080232304486907904 |
| 19 | 16 | 6 | 76 | 237088580720150299069073352882609192960 |
| 19 | 17 | 4 | 76 | 6061882531832865507873644025591575347200 |
| 19 | 18 | 2 | 76 | 15245108152760499532843974982820167680000 |
| 19 | 11 | 18 | 80 | 263834706664488960 |
| 19 | 12 | 16 | 80 | 49484477855760936468480 |
| 19 | 13 | 14 | 80 | 3015118259715910387740180480 |
| 19 | 14 | 12 | 80 | 75370199437239586521552563208192 |
| 19 | 15 | 10 | 80 | 574387441821592823050930633291333632 |
| 19 | 16 | 8 | 80 | 535997585281822186138528077342100684800 |
| 19 | 17 | 6 | 80 | 43068213729160966926667403132853760819200 |
| 19 | 18 | 4 | 80 | 313347963917897980073866147140068179968000 |
| 19 | 12 | 18 | 84 | 639864349988207984640 |
| 19 | 13 | 16 | 84 | 116980020366754960480665600 |
| 19 | 14 | 14 | 84 | 7427060496376168965321705652224 |
| 19 | 15 | 12 | 84 | 164521454049649290746893118327488512 |
| 19 | 16 | 10 | 84 | 614973146020366697623585944236520898560 |
| 19 | 17 | 8 | 84 | 170515898532359276817812752106472760934400 |
| 19 | 18 | 6 | 84 | 3533204040089479864496738145781508210688000 |
| 19 | 13 | 18 | 88 | 1797090381719553599078400 |
| 19 | 14 | 16 | 88 | 368584830558479606894960836608 |
| 19 | 15 | 14 | 88 | 23173654799098470374090739541868544 |
| 19 | 16 | 12 | 88 | 327458577552796905523234196256813219840 |
| 19 | 17 | 10 | 88 | 363555271079664203095650970101515236147200 |
| 19 | 18 | 8 | 88 | 22913769542296963438747302994031060975616000 |
| 19 | 14 | 18 | 92 | 7140150396191737255506739200 |
| 19 | 15 | 16 | 92 | 1547061523788467515156822052831232 |
| 19 | 16 | 14 | 92 | 74723602749035739169810338460603514880 |
| 19 | 17 | 12 | 92 | 384930870748757388053288828631581825433600 |
| 19 | 18 | 10 | 92 | 84457800447101908016218577302175971540992000 |
| 19 | 15 | 18 | 96 | 38841370178195977991387873280000 |
| 19 | 16 | 16 | 96 | 7245107392556158735146826039516200960 |
| 19 | 17 | 14 | 96 | 176766471189685108877808830296558141440000 |
| 19 | 18 | 12 | 96 | 167685675779848860327333927153678724104192000 |
| 19 | 16 | 18 | 100 | 245871250690434283918482695258112000 |
| 19 | 17 | 16 | 100 | 29153596475976931964393297001505515110400 |
| 19 | 18 | 14 | 100 | 161435473260477435105352113747543088693248000 |
| 19 | 17 | 18 | 104 | 1471129319514841623434863110814433280000 |
| 19 | 18 | 16 | 104 | 61681756431161735606400879138735101313024000 |
| 19 | 18 | 18 | 108 | 5872320479521853935273802648285872128000000 |
| 20 | 10 | 0 | 40 | 2337688704605346892800 |
| 20 | 10 | 2 | 44 | 2597431894005940992000 |
| 20 | 11 | 0 | 44 | 7948141595658179435520000 |
| 20 | 10 | 4 | 48 | 1298715947002970496000 |
| 20 | 11 | 2 | 48 | 12427845802187092333056000 |
| 20 | 12 | 0 | 48 | 5106526168269497533238476800 |
| 20 | 10 | 6 | 52 | 384804725037917184000 |
| 20 | 11 | 4 | 52 | 8025808015994999053824000 |
| 20 | 12 | 2 | 52 | 11509464996379778605380403200 |
| 20 | 13 | 0 | 52 | 1471547576128193046877278044160 |
| 20 | 10 | 8 | 56 | 74823140979595008000 |
| 20 | 11 | 6 | 56 | 2874206255496176240640000 |
| 20 | 12 | 4 | 56 | 10105184183860146151791820800 |
| 20 | 13 | 2 | 56 | 4932397608732242025138310348800 |
| 20 | 14 | 0 | 56 | 251776336276831099682156131123200 |
| 20 | 10 | 10 | 60 | 9976418797279334400 |
| 20 | 11 | 8 | 60 | 638756840860471517184000 |
| 20 | 12 | 6 | 60 | 4640508583582025462199091200 |
| 20 | 13 | 4 | 60 | 6324331367045351290843838545920 |
| 20 | 14 | 2 | 60 | 1299516735842566761535765689139200 |
| 20 | 15 | 0 | 60 | 29226869390707971436056770940764160 |
| 20 | 10 | 12 | 64 | 923742481229568000 |
| 20 | 11 | 10 | 64 | 92446915864813526016000 |
| 20 | 12 | 8 | 64 | 1257560833178325328773120000 |
| 20 | 13 | 6 | 64 | 4037382728649528814674749030400 |
| 20 | 14 | 4 | 64 | 2631881761911409381395940638720000 |
| 20 | 15 | 2 | 64 | 239769717477433055478626413015203840 |
| 20 | 16 | 0 | 64 | 2451366201882735727860690962608029696 |
| 20 | 10 | 14 | 68 | 58650316268544000 |
| 20 | 11 | 12 | 68 | 8814419181261517824000 |
| 20 | 12 | 10 | 68 | 212579805960567260754739200 |
| 20 | 13 | 8 | 68 | 1439109888850636719359807324160 |
| 20 | 14 | 6 | 68 | 2619677244939834295797972546355200 |
| 20 | 15 | 4 | 68 | 812786797269065713785770055334625280 |
| 20 | 16 | 2 | 68 | 32604104723773729005745340914618859520 |
| 20 | 17 | 0 | 68 | 149481071360637751403580846680718704640 |
| 20 | 10 | 16 | 72 | 2443763177856000 |
| 20 | 11 | 14 | 72 | 542359024640649216000 |
| 20 | 12 | 12 | 72 | 22783142151564062633164800 |
| 20 | 13 | 10 | 72 | 305087725949087483065315491840 |
| 20 | 14 | 8 | 72 | 1375749010937969146525626394214400 |
| 20 | 15 | 6 | 72 | 1396418792603128787387029521872977920 |
| 20 | 16 | 4 | 72 | 188370057327578408284906101759629328384 |
| 20 | 17 | 2 | 72 | 3226900656171930986429770891454589173760 |
| 20 | 18 | 0 | 72 | 6169776329861741567034536252467367116800 |
| 20 | 10 | 18 | 76 | 60339831552000 |
| 20 | 11 | 16 | 76 | 20200568806978560000 |
| 20 | 12 | 14 | 76 | 1519690562808453542707200 |
| 20 | 13 | 12 | 76 | 39458497186997373511227801600 |
| 20 | 14 | 10 | 76 | 402235193032282465720158899404800 |
| 20 | 15 | 8 | 76 | 1246288021134126634475711357811425280 |
| 20 | 16 | 6 | 76 | 575407440840534752370546799088196648960 |
| 20 | 17 | 4 | 76 | 31181341563583804126017017159777790197760 |
| 20 | 18 | 2 | 76 | 212176150728608218958566408493182903910400 |
| 20 | 19 | 0 | 76 | 132700783705071038781488360815350251520000 |
| 20 | 10 | 20 | 80 | 670442572800 |
| 20 | 11 | 18 | 80 | 391149605822976000 |
| 20 | 12 | 16 | 80 | 59102872161339034828800 |
| 20 | 13 | 14 | 80 | 3080295768339208597079982080 |
| 20 | 14 | 12 | 80 | 68034933633919284776682396057600 |
| 20 | 15 | 10 | 80 | 574254063349450025290863044245585920 |
| 20 | 16 | 8 | 80 | 939586911746876599461451679652617650176 |
| 20 | 17 | 6 | 80 | 164170707731639931925115017386709556920320 |
| 20 | 18 | 4 | 80 | 3294128264356272241588674909908804567040000 |
| 20 | 19 | 2 | 80 | 7030758088401868629590655560284196831232000 |
| 20 | 11 | 20 | 84 | 2534272925184000 |
| 20 | 12 | 18 | 84 | 1142201151848300544000 |
| 20 | 13 | 16 | 84 | 136906009359173059048243200 |
| 20 | 14 | 14 | 84 | 6687724068076568405724522086400 |
| 20 | 15 | 12 | 84 | 140312008826552027663174447907471360 |
| 20 | 16 | 10 | 84 | 782549175709973715518824973403433205760 |
| 20 | 17 | 8 | 84 | 480110608915039391481120667178292184350720 |
| 20 | 18 | 6 | 84 | 28330015615390712100602832151567517142220800 |
| 20 | 19 | 4 | 84 | 167334617723036476105687810417768834007040000 |
| 20 | 12 | 20 | 88 | 6803436687151104000 |
| 20 | 13 | 18 | 88 | 2977564015077769785507840 |
| 20 | 14 | 16 | 88 | 365510616616397827357861478400 |
| 20 | 15 | 14 | 88 | 18670982287278925715408156822077440 |
| 20 | 16 | 12 | 88 | 316263796617895429670106273861844598784 |
| 20 | 17 | 10 | 88 | 747312034396010040376399737197321949020160 |
| 20 | 18 | 8 | 88 | 139841797504209650836109006136594074173440000 |
| 20 | 19 | 6 | 88 | 2225799964420336458571640928292646682624000000 |
| 20 | 13 | 20 | 92 | 20172407000796610560000 |
| 20 | 14 | 18 | 92 | 9707386425421460963681894400 |
| 20 | 15 | 16 | 92 | 1324007595263925910902433067827200 |
| 20 | 16 | 14 | 92 | 62375626879135531629397074063466168320 |
| 20 | 17 | 12 | 92 | 571656719991878356267580252409775333048320 |
| 20 | 18 | 10 | 92 | 387145896896658995060381182429345831138099200 |
| 20 | 19 | 8 | 92 | 17441070536377052766411228973981293116129280000 |
| 20 | 14 | 20 | 96 | 83297015310487502684160000 |
| 20 | 15 | 18 | 96 | 44615074386245713451845130649600 |
| 20 | 16 | 16 | 96 | 6052667353640411368370915512518967296 |
| 20 | 17 | 14 | 96 | 195491423066358530807651015702741621145600 |
| 20 | 18 | 12 | 96 | 564052779606020336533215138574585048124620800 |
| 20 | 19 | 10 | 96 | 80204930071673792065873547065014325566504960000 |
| 20 | 15 | 20 | 100 | 490031460807871829613871104000 |
| 20 | 16 | 18 | 100 | 264533293770261465718707959365632000 |
| 20 | 17 | 16 | 100 | 28644170614707836958598268092253177118720 |
| 20 | 18 | 14 | 100 | 387736766839187398797191663673271023304704000 |
| 20 | 19 | 12 | 100 | 207909907008616853851861760131153157500698624000 |
| 20 | 16 | 20 | 104 | 3635620305006751810821763891200000 |
| 20 | 17 | 18 | 104 | 1704678343698505083648885526659858432000 |
| 20 | 18 | 16 | 104 | 106541276914173158411301496979699561555558400 |
| 20 | 19 | 14 | 104 | 280313982565609362183200420773851612567306240000 |
| 20 | 17 | 20 | 108 | 29091992400609040307594034413568000000 |
| 20 | 18 | 18 | 108 | 9729692532652326409875655107936717373440000 |
| 20 | 19 | 16 | 108 | 169900387700862442154433183772876740168253440000 |
| 20 | 18 | 20 | 112 | 209233358981445867302183022448607232000000 |
| 20 | 19 | 18 | 112 | 34503191058200857409872393693415356760064000000 |
| 20 | 19 | 20 | 116 | 971327718152259207554299130471566540800000000 |
| 21 | 11 | 0 | 44 | 3927317023736982779904000 |
| 21 | 11 | 2 | 48 | 5381878884380309735424000 |
| 21 | 12 | 0 | 48 | 5494054695073123110233702400 |
| 21 | 11 | 4 | 52 | 3200036093415319302144000 |
| 21 | 12 | 2 | 52 | 10543595285533645502860492800 |
| 21 | 13 | 0 | 52 | 2589106015162746831782648217600 |
| 21 | 11 | 6 | 56 | 1099002294708291477504000 |
| 21 | 12 | 4 | 56 | 8198242502180663421090201600 |
| 21 | 13 | 2 | 56 | 7141603013635387492277629747200 |
| 21 | 14 | 0 | 56 | 646264155156063529707983654092800 |
| 21 | 11 | 8 | 60 | 243025561901724585984000 |
| 21 | 12 | 6 | 60 | 3478689867786423197722214400 |
| 21 | 13 | 4 | 60 | 7676294268485764338714397900800 |
| 21 | 14 | 2 | 60 | 2644874800148220037524756312883200 |
| 21 | 15 | 0 | 60 | 103531730687505132329404650624122880 |
| 21 | 11 | 10 | 64 | 36314164422096777216000 |
| 21 | 12 | 8 | 64 | 906194956729045408756531200 |
| 21 | 13 | 6 | 64 | 4275768544815725310581106278400 |
| 21 | 14 | 4 | 64 | 4220871271027350948110885348966400 |
| 21 | 15 | 2 | 64 | 650045048572180229783615236850319360 |
| 21 | 16 | 0 | 64 | 11749459400981742332863846958833336320 |
| 21 | 11 | 12 | 68 | 3724529684317618176000 |
| 21 | 12 | 10 | 68 | 152979732085353031021363200 |
| 21 | 13 | 8 | 68 | 1393894282336261970337084211200 |
| 21 | 14 | 6 | 68 | 3374499984229721823127571791872000 |
| 21 | 15 | 4 | 68 | 1651867312165011512500807548146810880 |
| 21 | 16 | 2 | 68 | 116421296009383988796446422771527843840 |
| 21 | 17 | 0 | 68 | 987851815498202304717596594927441018880 |
| 21 | 11 | 14 | 72 | 259468999172038656000 |
| 21 | 12 | 12 | 72 | 17049393799287364318003200 |
| 21 | 13 | 10 | 72 | 282703641656295878356539801600 |
| 21 | 14 | 8 | 72 | 1496571781633310648310519457382400 |
| 21 | 15 | 6 | 72 | 2118915540426124926447778287688089600 |
| 21 | 16 | 4 | 72 | 492342448119705649304499918609580032000 |
| 21 | 17 | 2 | 72 | 15684002967273514897583612616157754818560 |
| 21 | 18 | 0 | 72 | 61206596948797941901598351353984529203200 |
| 21 | 11 | 16 | 76 | 11769163464554496000 |
| 21 | 12 | 14 | 76 | 1241419780082156529254400 |
| 21 | 13 | 12 | 76 | 36559713939440410833046732800 |
| 21 | 14 | 10 | 76 | 392758331450161797965787483340800 |
| 21 | 15 | 8 | 76 | 1449133414425455337631141470677237760 |
| 21 | 16 | 6 | 76 | 1092541487278246472765773300294546882560 |
| 21 | 17 | 4 | 76 | 111108677109185517489584187517282811904000 |
| 21 | 18 | 2 | 76 | 1552453374267459935448404756709738597580800 |
| 21 | 19 | 0 | 76 | 2581520855397294729487203696611545841664000 |
| 21 | 11 | 18 | 80 | 314249842722816000 |
| 21 | 12 | 16 | 80 | 56424798689293556121600 |
| 21 | 13 | 14 | 80 | 2996560962563101640766259200 |
| 21 | 14 | 12 | 80 | 63121719931222820075631437414400 |
| 21 | 15 | 10 | 80 | 547134756554429938231973478389514240 |
| 21 | 16 | 8 | 80 | 1300471628171109539718091103751194542080 |
| 21 | 17 | 6 | 80 | 429105704975490334656731982818384208199680 |
| 21 | 18 | 4 | 80 | 17984824634749842998340525154269506882764800 |
| 21 | 19 | 2 | 80 | 102451967615416729581363132834938231980032000 |
| 21 | 20 | 0 | 80 | 56772857028604305287384585670567238041600000 |
| 21 | 11 | 20 | 84 | 3754478407680000 |
| 21 | 12 | 18 | 84 | 1435549949151923404800 |
| 21 | 13 | 16 | 84 | 149145654564588495215001600 |
| 21 | 14 | 14 | 84 | 6233476320153864817000264499200 |
| 21 | 15 | 12 | 84 | 118972048490872969405991336961638400 |
| 21 | 16 | 10 | 84 | 811881170332679129224511950816951664640 |
| 21 | 17 | 8 | 84 | 918515117654581878009365193301006661713920 |
| 21 | 18 | 6 | 84 | 116306065781029153155621551868828278430105600 |
| 21 | 19 | 4 | 84 | 1864406005743598543195810189294492824109056000 |
| 21 | 20 | 2 | 84 | 3410034064615732218309494812506223741501440000 |
| 21 | 12 | 20 | 88 | 15270514937988710400 |
| 21 | 13 | 18 | 88 | 4047361024801441303756800 |
| 21 | 14 | 16 | 88 | 365429249564834625523915161600 |
| 21 | 15 | 14 | 88 | 15195244854150936437140884679557120 |
| 21 | 16 | 12 | 88 | 266014776821742041136537948879102935040 |
| 21 | 17 | 10 | 88 | 1043862061976890106359842438143963698298880 |
| 21 | 18 | 8 | 88 | 431023667758413647939229489327394601199206400 |
| 21 | 19 | 6 | 88 | 19164546376523698865111660674154864830316544000 |
| 21 | 20 | 4 | 88 | 93237191124978312896963017627692216059166720000 |
| 21 | 13 | 20 | 92 | 44710010198446886092800 |
| 21 | 14 | 18 | 92 | 11512190216796907860865843200 |
| 21 | 15 | 16 | 92 | 1117807899176522330708818148720640 |
| 21 | 16 | 14 | 92 | 47406190326130014724366630180261724160 |
| 21 | 17 | 12 | 92 | 592862304627276616357642098382878183260160 |
| 21 | 18 | 10 | 92 | 886135327236196979084393669582764148313292800 |
| 21 | 19 | 8 | 92 | 115989285475913316311886344226200368371990528000 |
| 21 | 20 | 6 | 92 | 1448498915191857099245860120796068694804398080000 |
| 21 | 14 | 20 | 96 | 147069586846076374351872000 |
| 21 | 15 | 18 | 96 | 43435537418239038041787853701120 |
| 21 | 16 | 16 | 96 | 4612764065558543946143131876605296640 |
| 21 | 17 | 14 | 96 | 163606972259645669790242930614703027650560 |
| 21 | 18 | 12 | 96 | 944155408490009591249565858530485932864307200 |
| 21 | 19 | 10 | 96 | 407522913904216488206514673030693881353601024000 |
| 21 | 20 | 8 | 96 | 13537573071654254739421774239311168957432463360000 |
| 21 | 15 | 20 | 100 | 681927428758098643189235712000 |
| 21 | 16 | 18 | 100 | 229027899856289796529428388632330240 |
| 21 | 17 | 16 | 100 | 22511709612417189306258850188679824015360 |
| 21 | 18 | 14 | 100 | 474899991847786860067413104626293257797632000 |
| 21 | 19 | 12 | 100 | 790762306304420094103648759428180821321711616000 |
| 21 | 20 | 10 | 100 | 76319527737740182380599414210824719710677893120000 |
| 21 | 16 | 20 | 104 | 4504367462879843855476910456832000 |
| 21 | 17 | 18 | 104 | 1485478166272321785954984506543623372800 |
| 21 | 18 | 16 | 104 | 104203779735051668574838990588008112481894400 |
| 21 | 19 | 14 | 104 | 776195946788210815315523662295225843318784000000 |
| 21 | 20 | 12 | 104 | 251867901794051120186646006662732095906318909440000 |
| 21 | 17 | 20 | 108 | 37270165918722810249567011403202560000 |
| 21 | 18 | 18 | 108 | 9859393882078292680343346487462006358016000 |
| 21 | 19 | 16 | 108 | 335820135590146736889780519757138939990769664000 |
| 21 | 20 | 14 | 108 | 457035211395786879696975865267959153155270246400000 |
| 21 | 18 | 20 | 112 | 330189244291408113527792105927422771200000 |
| 21 | 19 | 18 | 112 | 53127159274480644208633675763135311301836800000 |
| 21 | 20 | 16 | 112 | 408423929277580705259418500007663400570186629120000 |
| 21 | 19 | 20 | 116 | 2612330925982458884263179345960269512704000000 |
| 21 | 20 | 18 | 116 | 146672900358050951874390323481382923132941107200000 |
| 21 | 20 | 20 | 120 | 13264684518747469611529165432182291195494400000000 |
| 22 | 11 | 0 | 44 | 883646330340821125478400 |
| 22 | 11 | 2 | 48 | 1080012181527670264473600 |
| 22 | 12 | 0 | 48 | 4017645315282933383841792000 |
| 22 | 11 | 4 | 52 | 600006767515372369152000 |
| 22 | 12 | 2 | 52 | 6712875714961986066072576000 |
| 22 | 13 | 0 | 52 | 3420476339775201719846933299200 |
| 22 | 11 | 6 | 56 | 200002255838457456384000 |
| 22 | 12 | 4 | 56 | 4740320133045892992909312000 |
| 22 | 13 | 2 | 56 | 7978004864435983087664322969600 |
| 22 | 14 | 0 | 56 | 1297557922024232708525238418145280 |
| 22 | 11 | 8 | 60 | 44444945741879434752000 |
| 22 | 12 | 6 | 60 | 1897058434082553873331200000 |
| 22 | 13 | 4 | 60 | 7463735881740442311496615526400 |
| 22 | 14 | 2 | 60 | 4341989935549676669416911281848320 |
| 22 | 15 | 0 | 60 | 291292725437924206177095772431974400 |
| 22 | 11 | 10 | 64 | 6913658226514578739200 |
| 22 | 12 | 8 | 64 | 482388979991343873896448000 |
| 22 | 13 | 6 | 64 | 3762890264545319273760659865600 |
| 22 | 14 | 4 | 64 | 5706094615793298274214381994639360 |
| 22 | 15 | 2 | 64 | 1443515429092086736374989101989888000 |
| 22 | 16 | 0 | 64 | 44477469633568922306023551685770608640 |
| 22 | 11 | 12 | 68 | 768184247390508748800 |
| 22 | 12 | 10 | 68 | 82200835699100372846592000 |
| 22 | 13 | 8 | 68 | 1153988670908989091002053427200 |
| 22 | 14 | 6 | 68 | 3870865658801956660718327479664640 |
| 22 | 15 | 4 | 68 | 2855172725612123989518527915202969600 |
| 22 | 16 | 2 | 68 | 336871635571551227680463521105387192320 |
| 22 | 17 | 0 | 68 | 4976760609831276988433133764540941467648 |
| 22 | 11 | 14 | 72 | 60967003761151488000 |
| 22 | 12 | 12 | 72 | 9584663305959799529472000 |
| 22 | 13 | 10 | 72 | 228403235611921112180018380800 |
| 22 | 14 | 8 | 72 | 1524827847406081262545578602004480 |
| 22 | 15 | 6 | 72 | 2868943656185168431102928398319616000 |
| 22 | 16 | 4 | 72 | 1065156802668978865584994741347585884160 |
| 22 | 17 | 2 | 72 | 59047030744261179494689789185252950802432 |
| 22 | 18 | 0 | 72 | 420881178614974283796544830673743658352640 |
| 22 | 11 | 16 | 76 | 3387055764508416000 |
| 22 | 12 | 14 | 76 | 762069482716982888448000 |
| 22 | 13 | 12 | 76 | 29914401671352728702690918400 |
| 22 | 14 | 10 | 76 | 372150403795103277318375384023040 |
| 22 | 15 | 8 | 76 | 1596414656746425358720887871596134400 |
| 22 | 16 | 6 | 76 | 1751705054283225870235352072051868303360 |
| 22 | 17 | 4 | 76 | 308027933396799290743549551356278223142912 |
| 22 | 18 | 2 | 76 | 7907723734818304062729402643043231308185600 |
| 22 | 19 | 0 | 76 | 26511826187031911857770272649639453995827200 |
| 22 | 11 | 18 | 80 | 125446509796608000 |
| 22 | 12 | 16 | 80 | 40107758112171509760000 |
| 22 | 13 | 14 | 80 | 2589410980966991697189273600 |
| 22 | 14 | 12 | 80 | 58092719088229505757111653498880 |
| 22 | 15 | 10 | 80 | 521604684477890579995655890599936000 |
| 22 | 16 | 8 | 80 | 1565400424042550067128531399495060029440 |
| 22 | 17 | 6 | 80 | 870849182403848595289779193961979416936448 |
| 22 | 18 | 4 | 80 | 67884311637915554668724090395475826274467840 |
| 22 | 19 | 2 | 80 | 783675124628681751163913502889058287956787200 |
| 22 | 20 | 0 | 80 | 1141594632723515726032865987117833431023616000 |
| 22 | 11 | 20 | 84 | 2787700217702400 |
| 22 | 12 | 18 | 84 | 1302915327749747712000 |
| 22 | 13 | 16 | 84 | 143825102065037042992742400 |
| 22 | 14 | 14 | 84 | 5827187630850473593697733181440 |
| 22 | 15 | 12 | 84 | 104202960799966281964734220586188800 |
| 22 | 16 | 10 | 84 | 770442860918829102545915935249882152960 |
| 22 | 17 | 8 | 84 | 1364687169261884582736816662815431299432448 |
| 22 | 18 | 6 | 84 | 326329810706862087831930704149431071727943680 |
| 22 | 19 | 4 | 84 | 10769247703150318812806079640299785578925260800 |
| 22 | 20 | 2 | 84 | 51913401900915242078886108302345091560767488000 |
| 22 | 21 | 0 | 84 | 25632944948414843837254140430261107975782400000 |
| 22 | 11 | 22 | 88 | 28158588057600 |
| 22 | 12 | 20 | 88 | 22351160856600576000 |
| 22 | 13 | 18 | 88 | 4766663129965546998988800 |
| 22 | 14 | 16 | 88 | 366449684733969011034984284160 |
| 22 | 15 | 14 | 88 | 12928506985259379147555302552371200 |
| 22 | 16 | 12 | 88 | 215989903084374476874767605874357698560 |
| 22 | 17 | 10 | 88 | 1149946647399952627232914881949951435210752 |
| 22 | 18 | 8 | 88 | 897885447631445814068294594650752353619148800 |
| 22 | 19 | 6 | 88 | 84372100262356564660179780069461832208534732800 |
| 22 | 20 | 4 | 88 | 1097573935451266835166182052677813163389878272000 |
| 22 | 21 | 2 | 88 | 1735248446938689165502623666446557440292945920000 |
| 22 | 12 | 22 | 92 | 130092676826112000 |
| 22 | 13 | 20 | 92 | 79892217337762013184000 |
| 22 | 14 | 18 | 92 | 13495209266025592298439966720 |
| 22 | 15 | 16 | 92 | 981811387066686360770806559539200 |
| 22 | 16 | 14 | 92 | 35582450180471457752925568044493701120 |
| 22 | 17 | 12 | 92 | 508749006011293368989220129082251675697152 |
| 22 | 18 | 10 | 92 | 1362879143613259656296737541104184318628986880 |
| 22 | 19 | 8 | 92 | 389187057604517067881140036495017616748209766400 |
| 22 | 20 | 6 | 92 | 13335329832442591979999387760536227393900118016000 |
| 22 | 21 | 4 | 92 | 54119148160170041399445833192840601938291589120000 |
| 22 | 13 | 22 | 96 | 417485984603111424000 |
| 22 | 14 | 20 | 96 | 248244429416569886531911680 |
| 22 | 15 | 18 | 96 | 43061873412177875151804786278400 |
| 22 | 16 | 16 | 96 | 3453087761193462605899430956357386240 |
| 22 | 17 | 14 | 96 | 120920357574674767771273205834275344089088 |
| 22 | 18 | 12 | 96 | 1073242166977042795302959507258773520347299840 |
| 22 | 19 | 10 | 96 | 1032261483818236510145119032076929039168071270400 |
| 22 | 20 | 8 | 96 | 97541529190521977674431142016486834742415589376000 |
| 22 | 21 | 6 | 96 | 973357165399762850326718858813749472908856524800000 |
| 22 | 14 | 22 | 100 | 1438608531482560069632000 |
| 22 | 15 | 20 | 100 | 943919468391897600902627328000 |
| 22 | 16 | 18 | 100 | 189037795291713787270112460354355200 |
| 22 | 17 | 16 | 100 | 15828106757852195210783927354973663264768 |
| 22 | 18 | 14 | 100 | 415961242502019937202620206402770180788715520 |
| 22 | 19 | 12 | 100 | 1487582128399133551542082011802535789660523724800 |
| 22 | 20 | 10 | 100 | 426596995724291595347825944230204912093464887296000 |
| 22 | 21 | 8 | 100 | 10728297008887298210884208254712037964363207802880000 |
| 22 | 15 | 22 | 104 | 6820302660067917866926080000 |
| 22 | 16 | 20 | 104 | 5131627461736107314015427467673600 |
| 22 | 17 | 18 | 104 | 1116271184261691119815339384630098788352 |
| 22 | 18 | 16 | 104 | 79781008232419304097044946099957097813770240 |
| 22 | 19 | 14 | 104 | 1070516723666772188561539654189187462640697344000 |
| 22 | 20 | 12 | 104 | 1073022184688280460606605276179989961272480235520000 |
| 22 | 21 | 10 | 104 | 73047364256818603744392064290008052992170115727360000 |
| 22 | 16 | 22 | 108 | 47115939538798035949693698048000 |
| 22 | 17 | 20 | 108 | 37913029943975698814176925903015116800 |
| 22 | 18 | 18 | 108 | 7609145687129447459893728763085744473374720 |
| 22 | 19 | 16 | 108 | 349922834953638523124405204846371545252731289600 |
| 22 | 20 | 14 | 108 | 1446293467430694709706621416803265526056165048320000 |
| 22 | 21 | 12 | 108 | 300589355350825721896686617451154543957871658270720000 |
| 22 | 17 | 22 | 112 | 430692153144411011607628716441600000 |
| 22 | 18 | 20 | 112 | 329962064678421474422982544160049856512000 |
| 22 | 19 | 18 | 112 | 49810347086846773723635934691996021603853926400 |
| 22 | 20 | 16 | 112 | 933639063183488628463880382714097828683759747072000 |
| 22 | 21 | 14 | 112 | 711592267381052651405168391169772164418275198894080000 |
| 22 | 18 | 22 | 116 | 4557766771521718876953133805312409600000 |
| 22 | 19 | 20 | 116 | 2907766118166032842353186547857326887403520000 |
| 22 | 20 | 18 | 116 | 244591003836747840235745688053710876807016742912000 |
| 22 | 21 | 16 | 116 | 889658653883576148249468718786191236173648751493120000 |
| 22 | 19 | 22 | 120 | 48937159158341848602700384146171101184000000 |
| 22 | 20 | 20 | 120 | 21677998674564626479459770481178651439346483200000 |
| 22 | 21 | 18 | 120 | 506173731661583525118664685043222054781085496115200000 |
| 22 | 20 | 22 | 124 | 453017242012754366239894922933534101340160000000 |
| 22 | 21 | 20 | 124 | 97490370023093812804328419987418443022881259520000000 |
| 22 | 21 | 22 | 128 | 2626750567972775462493701394283217282924544000000000 |
| 23 | 12 | 0 | 48 | 1788500172609821957968281600 |
| 23 | 12 | 2 | 52 | 2649629885347884382175232000 |
| 23 | 13 | 0 | 52 | 3286070983808446210773722726400 |
| 23 | 12 | 4 | 56 | 1729619508490980082808832000 |
| 23 | 13 | 2 | 56 | 6630345504098367615142561382400 |
| 23 | 14 | 0 | 56 | 2018671855268350455577660922265600 |
| 23 | 12 | 6 | 60 | 662407471336971095543808000 |
| 23 | 13 | 4 | 60 | 5554340621102611574520392908800 |
| 23 | 14 | 2 | 60 | 5674738872217558133441551977676800 |
| 23 | 15 | 0 | 60 | 653388505405643505170768523606097920 |
| 23 | 12 | 8 | 64 | 166283357002284925218816000 |
| 23 | 13 | 6 | 64 | 2598276253945864334217235660800 |
| 23 | 14 | 4 | 64 | 6383011456185251241864073877913600 |
| 23 | 15 | 2 | 64 | 2632174236853656609656894470697779200 |
| 23 | 16 | 0 | 64 | 135461715248657973041743402054535086080 |
| 23 | 12 | 10 | 68 | 28834563910050136394956800 |
| 23 | 13 | 8 | 68 | 764162681994431179393322188800 |
| 23 | 14 | 6 | 68 | 3834059627525420962299801423052800 |
| 23 | 15 | 4 | 68 | 4221393455468005096100067105979760640 |
| 23 | 16 | 2 | 68 | 806763896910187379914459506911823790080 |
| 23 | 17 | 0 | 68 | 19975488244756634890981456724160644382720 |
| 23 | 12 | 12 | 72 | 3533647537996340244480000 |
| 23 | 13 | 10 | 72 | 149676200751427026634653696000 |
| 23 | 14 | 8 | 72 | 1389388294090205099274617723289600 |
| 23 | 15 | 6 | 72 | 3503568660233487615176032867162521600 |
| 23 | 16 | 4 | 72 | 1967962875230472075980542824181105950720 |
| 23 | 17 | 2 | 72 | 181102344282817565700597822682716658728960 |
| 23 | 18 | 0 | 72 | 2217834096822307318885509451745133059899392 |
| 23 | 12 | 14 | 76 | 306623384249417883648000 |
| 23 | 13 | 12 | 76 | 20032646337109240910659584000 |
| 23 | 14 | 10 | 76 | 323551654025292863288505689702400 |
| 23 | 15 | 8 | 76 | 1677692488448628356099634205525278720 |
| 23 | 16 | 6 | 76 | 2488807291688922263604497229601591787520 |
| 23 | 17 | 4 | 76 | 706417325528741010243202278007806634229760 |
| 23 | 18 | 2 | 76 | 31256440777253617993582285041517859124019200 |
| 23 | 19 | 0 | 76 | 189125886627183243222345225090367045081497600 |
| 23 | 12 | 16 | 80 | 18488808399863273472000 |
| 23 | 13 | 14 | 80 | 1837040837908632932627251200 |
| 23 | 14 | 12 | 80 | 49921433438640973560501947596800 |
| 23 | 15 | 10 | 80 | 494897080728734942913472202570465280 |
| 23 | 16 | 8 | 80 | 1752712852808177169496377913418144808960 |
| 23 | 17 | 6 | 80 | 1477944590560751691604294734827726391214080 |
| 23 | 18 | 4 | 80 | 198995583345702850881124647406261755589951488 |
| 23 | 19 | 2 | 80 | 4171585274698955360348836213375271654475694080 |
| 23 | 20 | 0 | 80 | 12114239048613246073785651597620027118845952000 |
| 23 | 12 | 18 | 84 | 738629049682427904000 |
| 23 | 13 | 16 | 84 | 113116890325701450527539200 |
| 23 | 14 | 14 | 84 | 5135801260916373919365228134400 |
| 23 | 15 | 12 | 84 | 93371329316315011352896572280012800 |
| 23 | 16 | 10 | 84 | 718875492763312144941269800736973127680 |
| 23 | 17 | 8 | 84 | 1722269035271480389460153844522722556641280 |
| 23 | 18 | 6 | 84 | 707020336237851188683209074675953978709114880 |
| 23 | 19 | 4 | 84 | 42930910099616342589595578483240601141137899520 |
| 23 | 20 | 2 | 84 | 414222200367414962386680619968789277463229235200 |
| 23 | 21 | 0 | 84 | 532051023159785562199252545403686964502200320000 |
| 23 | 12 | 20 | 88 | 17610831508631961600 |
| 23 | 13 | 18 | 88 | 4439900813444576531251200 |
| 23 | 14 | 16 | 88 | 346081567358472541590926131200 |
| 23 | 15 | 14 | 88 | 11418815291943319163617043137167360 |
| 23 | 16 | 12 | 88 | 179153121160670261935673916697671106560 |
| 23 | 17 | 10 | 88 | 1113197745011276729506494895755117440532480 |
| 23 | 18 | 8 | 88 | 1436724644069800197706000077366039582974410752 |
| 23 | 19 | 6 | 88 | 253267716025071075693525062614623973286420152320 |
| 23 | 20 | 4 | 88 | 6687954770841980795949749869463130819003206860800 |
| 23 | 21 | 2 | 88 | 27544155543260486540742961005701049719797579776000 |
| 23 | 22 | 0 | 88 | 12180775439486733791463167532460078510091796480000 |
| 23 | 12 | 22 | 92 | 189976607428608000 |
| 23 | 13 | 20 | 92 | 99165990632516385177600 |
| 23 | 14 | 18 | 92 | 14518602401025192416929382400 |
| 23 | 15 | 16 | 92 | 894736502432409666836548655513600 |
| 23 | 16 | 14 | 92 | 27817724289269705057922017169160273920 |
| 23 | 17 | 12 | 92 | 404864870144183653613130248684837095342080 |
| 23 | 18 | 10 | 92 | 1616928068779682191476153207572565386424483840 |
| 23 | 19 | 8 | 92 | 879771720031576807754742027166958492696728043520 |
| 23 | 20 | 6 | 92 | 62709362390679802258222827924751164395145815654400 |
| 23 | 21 | 4 | 92 | 671224505142851308962347846560314898137690931200000 |
| 23 | 22 | 2 | 92 | 924412236407711737103984150155576364874753638400000 |
| 23 | 13 | 22 | 96 | 938332459411380633600 |
| 23 | 14 | 20 | 96 | 338456097338639055519744000 |
| 23 | 15 | 18 | 96 | 42936391715327835368326724321280 |
| 23 | 16 | 16 | 96 | 2690455567795423570912285537043742720 |
| 23 | 17 | 14 | 96 | 85923176967791027194016748766427778908160 |
| 23 | 18 | 12 | 96 | 968529292220718090486412853993430492798517248 |
| 23 | 19 | 10 | 96 | 1746037154286144956840160823362415538958709555200 |
| 23 | 20 | 8 | 96 | 354441737817433829104139108567291925725288438169600 |
| 23 | 21 | 6 | 96 | 9544743633412335002375993966426367652488516993024000 |
| 23 | 22 | 4 | 96 | 32675827883435519117920494566116385988686244741120000 |
| 23 | 14 | 22 | 100 | 3257691768093647595110400 |
| 23 | 15 | 20 | 100 | 1133332802476405278872489164800 |
| 23 | 16 | 18 | 100 | 156482078097932038621109163424481280 |
| 23 | 17 | 16 | 100 | 10831972564794694789687391521818500136960 |
| 23 | 18 | 14 | 100 | 307916654234133439105411143826274022315786240 |
| 23 | 19 | 12 | 100 | 1870029184229798190609704638321422645239406919680 |
| 23 | 20 | 10 | 100 | 1188300221475260703753178841862314416151826373017600 |
| 23 | 21 | 8 | 100 | 83322089943116849987152113329160948695258665844736000 |
| 23 | 22 | 6 | 100 | 675020691807131922644689645882243969429639947878400000 |
| 23 | 15 | 22 | 104 | 12338421803925324443733196800 |
| 23 | 16 | 20 | 104 | 4963499366353488124874069303623680 |
| 23 | 17 | 18 | 104 | 795211053112175542349684540800027852800 |
| 23 | 18 | 16 | 104 | 53795364566762997157058146993633173839020032 |
| 23 | 19 | 14 | 104 | 1014088163103418033046600891482401049100534415360 |
| 23 | 20 | 12 | 104 | 2255742963732831105895258439804559854920617531801600 |
| 23 | 21 | 10 | 104 | 446169863370497530596827586733862945600645445451776000 |
| 23 | 22 | 8 | 104 | 8687672478064939303939695423775275603896043904696320000 |
| 23 | 16 | 22 | 108 | 65138208896382930511633317888000 |
| 23 | 17 | 20 | 108 | 31208730536772601395493171929148293120 |
| 23 | 18 | 18 | 108 | 5179989585334072927154764426240891897774080 |
| 23 | 19 | 16 | 108 | 270837643757433419798800083106311621641848750080 |
| 23 | 20 | 14 | 108 | 2253587224337615328140400323077386799532531829964800 |
| 23 | 21 | 12 | 108 | 1422173901819695609730952428312327533633818507345920000 |
| 23 | 22 | 10 | 108 | 70527969946047002588804673066657510449323800872878080000 |
| 23 | 17 | 22 | 112 | 502057806821771648113864712650752000 |
| 23 | 18 | 20 | 112 | 256825317863308050234757954643625970237440 |
| 23 | 19 | 18 | 112 | 36477110854805171859639955543932643674842726400 |
| 23 | 20 | 16 | 112 | 1078200530873899489585518677261623922293869222297600 |
| 23 | 21 | 14 | 112 | 2548639205560071646531478875404174240385693170794496000 |
| 23 | 22 | 12 | 112 | 355617033957501356043880723065080541595932547413442560000 |
| 23 | 18 | 22 | 116 | 5092037950397198493704341352286781440000 |
| 23 | 19 | 20 | 116 | 2377555954221401198176516991770619843444736000 |
| 23 | 20 | 18 | 116 | 228562438145708728905256619677082846965807448064000 |
| 23 | 21 | 16 | 116 | 2343674565514658360709950146783853264200984701173760000 |
| 23 | 22 | 14 | 116 | 1071064270267532522849736133715502760269999431001047040000 |
| 23 | 19 | 22 | 120 | 59392026270524469927196438591605194096640000 |
| 23 | 20 | 20 | 120 | 21147052242646506032928072306486233046479536128000 |
| 23 | 21 | 18 | 120 | 962666853718718205136233886206283508523708847226880000 |
| 23 | 22 | 16 | 120 | 1800707093885209465619239562602497608922806621181050880000 |
| 23 | 20 | 22 | 124 | 698708476196021022532236361625368253379379200000 |
| 23 | 21 | 20 | 124 | 146832231077274926113993347409813201310551753359360000 |
| 23 | 22 | 18 | 124 | 1508895845491217329210908907438643099916971865538560000000 |
| 23 | 21 | 22 | 128 | 7049964270966859024180045470625567195791360000000000 |
| 23 | 22 | 20 | 128 | 513218294465860423859244070288634010925327762587648000000 |
| 23 | 22 | 22 | 132 | 44347004424588159067558257538609472190164238336000000000 |
| 24 | 12 | 0 | 48 | 365829580761099945948057600 |
| 24 | 12 | 2 | 52 | 487772774348133261264076800 |
| 24 | 13 | 0 | 52 | 2167662209203104213057557299200 |
| 24 | 12 | 4 | 56 | 298083362101636992994713600 |
| 24 | 13 | 2 | 56 | 3855608927663973958722288844800 |
| 24 | 14 | 0 | 56 | 2385916462267026006232342639411200 |
| 24 | 12 | 6 | 60 | 110401245222828515923968000 |
| 24 | 13 | 4 | 60 | 2952585622405355540339390054400 |
| 24 | 14 | 2 | 60 | 5766131268889775540463508055654400 |
| 24 | 15 | 0 | 60 | 1162871061319194367829584588984811520 |
| 24 | 12 | 8 | 64 | 27600311305707128980992000 |
| 24 | 13 | 6 | 64 | 1303985907741901877749960704000 |
| 24 | 14 | 4 | 64 | 5725286134914851704137586404556800 |
| 24 | 15 | 2 | 64 | 3911331324941172337463853174486466560 |
| 24 | 16 | 0 | 64 | 334014276259162659786812788271260631040 |
| 24 | 12 | 10 | 68 | 4906722009903489596620800 |
| 24 | 13 | 8 | 68 | 372788204702417622103265280000 |
| 24 | 14 | 6 | 68 | 3137539483358407660265702748979200 |
| 24 | 15 | 4 | 68 | 5285207132075449158890658495080693760 |
| 24 | 16 | 2 | 68 | 1608862259876847469919334685315600220160 |
| 24 | 17 | 0 | 68 | 65200665662780523092094998467863788912640 |
| 24 | 12 | 12 | 72 | 636056556839341244006400 |
| 24 | 13 | 10 | 72 | 72987913935018967310563737600 |
| 24 | 14 | 8 | 72 | 1071284642524105364296519203225600 |
| 24 | 15 | 6 | 72 | 3795242551539520412074390442653777920 |
| 24 | 16 | 4 | 72 | 3141210329211478543930310876723738050560 |
| 24 | 17 | 2 | 72 | 463494727492911514360123342007127276257280 |
| 24 | 18 | 0 | 72 | 9378418016393757895794248810900128102612992 |
| 24 | 12 | 14 | 76 | 60576814937080118476800 |
| 24 | 13 | 12 | 76 | 10049976289864631362520678400 |
| 24 | 14 | 10 | 76 | 242324906321946565517843732889600 |
| 24 | 15 | 8 | 76 | 1631899633869485866177094935691919360 |
| 24 | 16 | 6 | 76 | 3203177300632304976356685929026336849920 |
| 24 | 17 | 4 | 76 | 1386617905065018896491428462257636628234240 |
| 24 | 18 | 2 | 76 | 101053806235681511110997429909251552702365696 |
| 24 | 19 | 0 | 76 | 1038185032393934293293470275077434951759560704 |
| 24 | 12 | 16 | 80 | 4206723259519452672000 |
| 24 | 13 | 14 | 80 | 979320687644651761292083200 |
| 24 | 14 | 12 | 80 | 37425006099304221158840785305600 |
| 24 | 15 | 10 | 80 | 448680448266249510597766480779018240 |
| 24 | 16 | 8 | 80 | 1879079503865865370328150747750832537600 |
| 24 | 17 | 6 | 80 | 2204361709494985103849210492230627963699200 |
| 24 | 18 | 4 | 80 | 482097643008518031047411432998265157247303680 |
| 24 | 19 | 2 | 80 | 17251110400547069236423677776420288463410036736 |
| 24 | 20 | 0 | 80 | 89426223320955260624017164373227917534665113600 |
| 24 | 12 | 18 | 84 | 207739420223182848000 |
| 24 | 13 | 16 | 84 | 66707620706706690686976000 |
| 24 | 14 | 14 | 84 | 3979821708694369559074288435200 |
| 24 | 15 | 12 | 84 | 81722740845267455220926345128181760 |
| 24 | 16 | 10 | 84 | 674216853390056430511549517068888965120 |
| 24 | 17 | 8 | 84 | 1977325997666662602137000866965017308692480 |
| 24 | 18 | 6 | 84 | 1271129132744280993522425815574156449450819584 |
| 24 | 19 | 4 | 84 | 132696215055178037207712358840240472534751903744 |
| 24 | 20 | 2 | 84 | 2298657004421954617457437446221048380884170833920 |
| 24 | 21 | 0 | 84 | 5824477474644007436260078322382160852351451136000 |
| 24 | 12 | 20 | 88 | 6924647340772761600 |
| 24 | 13 | 18 | 88 | 3065541377760101560320000 |
| 24 | 14 | 16 | 88 | 288047864578440530681826508800 |
| 24 | 15 | 14 | 88 | 9990359068088648277611465555312640 |
| 24 | 16 | 12 | 88 | 154199166470585981135942460844403589120 |
| 24 | 17 | 10 | 88 | 1028389603195496681422802239327307531550720 |
| 24 | 18 | 8 | 88 | 1918404010006643973624605116826536644119101440 |
| 24 | 19 | 6 | 88 | 584722045728181881422146359510119662492701425664 |
| 24 | 20 | 4 | 88 | 28081863103952545175049622546985999476723223101440 |
| 24 | 21 | 2 | 88 | 228808328894470764538418975214047043255846882508800 |
| 24 | 22 | 0 | 88 | 260669092344270242926123017420796892035499950080000 |
| 24 | 12 | 22 | 92 | 139891865470156800 |
| 24 | 13 | 20 | 92 | 88277456047531393843200 |
| 24 | 14 | 18 | 92 | 13680971207512920766277222400 |
| 24 | 15 | 16 | 92 | 813276947205200340328118306734080 |
| 24 | 16 | 14 | 92 | 22958335420864295691886398408165949440 |
| 24 | 17 | 12 | 92 | 321592909746521775124805801720674045132800 |
| 24 | 18 | 10 | 92 | 1631533261747379377144300290757238090341810176 |
| 24 | 19 | 8 | 92 | 1516753103389774948381813504404621375556515004416 |
| 24 | 20 | 6 | 92 | 200727372383944333253555789268257031600661982085120 |
| 24 | 21 | 4 | 92 | 4303236629665845415975525371002457320651480471961600 |
| 24 | 22 | 2 | 92 | 15272308503898345351915782011670288860690811715584000 |
| 24 | 23 | 0 | 92 | 6077269961577765797802315739656620708958107074560000 |
| 24 | 12 | 24 | 96 | 1295295050649600 |
| 24 | 13 | 22 | 96 | 1359206635508718796800 |
| 24 | 14 | 20 | 96 | 394547700709757321433907200 |
| 24 | 15 | 18 | 96 | 42639620962120581178816911114240 |
| 24 | 16 | 16 | 96 | 2224528997999778406997138372433018880 |
| 24 | 17 | 14 | 96 | 62433176559500029442496173177101992591360 |
| 24 | 18 | 12 | 96 | 776156195206350362124479503574277537147125760 |
| 24 | 19 | 10 | 96 | 2246598520645329837884635000827444656395366957056 |
| 24 | 20 | 8 | 96 | 866097013549504864426061445452628923391981524090880 |
| 24 | 21 | 6 | 96 | 47769821607278773357465047806775206559796470743040000 |
| 24 | 22 | 4 | 96 | 425905491659786518019123499699615253942565414633472000 |
| 24 | 23 | 2 | 96 | 514525360058916121537029925905492232275520798064640000 |
| 24 | 13 | 24 | 100 | 7181115760801382400 |
| 24 | 14 | 22 | 100 | 5832645843238098812928000 |
| 24 | 15 | 20 | 100 | 1336296702583842884761225789440 |
| 24 | 16 | 18 | 100 | 136626935737392382266509796311040000 |
| 24 | 17 | 16 | 100 | 7619911328262832839670975770367906283520 |
| 24 | 18 | 14 | 100 | 212535977105405140238437417064283302038339584 |
| 24 | 19 | 12 | 100 | 1813171288244034861439399950304158225277107830784 |
| 24 | 20 | 10 | 100 | 2203192738859734358765712792942113714640707156705280 |
| 24 | 21 | 8 | 100 | 326321878878729857901438809141947404314472604709683200 |
| 24 | 22 | 6 | 100 | 7026142281277300307638707966856493730561234674122752000 |
| 24 | 23 | 4 | 100 | 20493254519025069911105631529636712973637464631541760000 |
| 24 | 14 | 24 | 104 | 27113841365425790976000 |
| 24 | 15 | 22 | 104 | 21235215143505773526232596480 |
| 24 | 16 | 20 | 104 | 4975725808816494502857212575088640 |
| 24 | 17 | 18 | 104 | 576023545562683995174979884029218652160 |
| 24 | 18 | 16 | 104 | 34511281728702120938676883998063491977052160 |
| 24 | 19 | 14 | 104 | 775957879862301619969084135833605005742507556864 |
| 24 | 20 | 12 | 104 | 3141373402002294034172642232338943937427887808839680 |
| 24 | 21 | 10 | 104 | 1358480787077749361289384122686498095987879774781440000 |
| 24 | 22 | 8 | 104 | 72398602353105216602573926423229985970112815838527488000 |
| 24 | 23 | 6 | 104 | 482833314643802312146193498395047095492377868438077440000 |
| 24 | 15 | 24 | 108 | 107042860509027134275584000 |
| 24 | 16 | 22 | 108 | 92354701464836923387510542827520 |
| 24 | 17 | 20 | 108 | 25501583497145202985280435175555072000 |
| 24 | 18 | 18 | 108 | 3330791002510383842377289209736460968656896 |
| 24 | 19 | 16 | 108 | 180184557681266153506922493128595043778744549376 |
| 24 | 20 | 14 | 108 | 2352636088948054067840048130922151198176528595681280 |
| 24 | 21 | 12 | 108 | 3319055521112191286846654502040236202848460202626252800 |
| 24 | 22 | 10 | 108 | 467930798764911716098252575859451835843294797500514304000 |
| 24 | 23 | 8 | 108 | 7192720255371325654315650236473898833935107892738785280000 |
| 24 | 16 | 24 | 112 | 572078399446216525977354240000 |
| 24 | 17 | 22 | 112 | 576231998058430139764867048302182400 |
| 24 | 18 | 20 | 112 | 183178185733847616535101172506237339697152 |
| 24 | 19 | 18 | 112 | 23238782506342221124922267052737319874892660736 |
| 24 | 20 | 16 | 112 | 878189248289251411439456334643636021502203637268480 |
| 24 | 21 | 14 | 112 | 4472637577623088587652211590414913490168238708673740800 |
| 24 | 22 | 12 | 112 | 1854275183875021090744354450217682731913464829249060864000 |
| 24 | 23 | 10 | 112 | 68842981329120198471980276351826217641592158409331834880000 |
| 24 | 17 | 24 | 116 | 4513579233530296735741051404288000 |
| 24 | 18 | 22 | 116 | 5065139719534506983961550276846524825600 |
| 24 | 19 | 20 | 116 | 1627444393396735608648370269371681563075411968 |
| 24 | 20 | 18 | 116 | 164231315569106296749698692594625816693139151257600 |
| 24 | 21 | 16 | 116 | 3049902472212033012808179100935503618439518662479052800 |
| 24 | 22 | 14 | 116 | 4301385172599381109863580169190001038752755062153412608000 |
| 24 | 23 | 12 | 116 | 419060369272112039634534068035873576203813734754287616000000 |
| 24 | 18 | 24 | 120 | 48786454917185724956597556999094272000 |
| 24 | 19 | 22 | 120 | 55371912556136121227347993590821919129600000 |
| 24 | 20 | 20 | 120 | 15406271297274596478537459766277539629709802864640 |
| 24 | 21 | 18 | 120 | 957936154487553900540595302767736810589882355495731200 |
| 24 | 22 | 16 | 120 | 5421435622996700056445890022780051208435014034536792064000 |
| 24 | 23 | 14 | 120 | 1572877199828049809516232604729161539032291522921428418560000 |
| 24 | 19 | 24 | 124 | 639963379418825309817529345500197683200000 |
| 24 | 20 | 22 | 124 | 661580403880617272860121377144383428515332096000 |
| 24 | 21 | 20 | 124 | 132873358650353053366416618101891727139575567482880000 |
| 24 | 22 | 18 | 124 | 3312771401698791838493320702640829445122549605027807232000 |
| 24 | 23 | 16 | 124 | 3447339603774813069578109320115961456899657497572571873280000 |
| 24 | 20 | 24 | 128 | 9117601822884710208136472560269288013824000000 |
| 24 | 21 | 22 | 128 | 7617718610988304188357957382175012484784796467200000 |
| 24 | 22 | 20 | 128 | 832191934144794576348895195965487015342481535368429568000 |
| 24 | 23 | 18 | 128 | 4037633548862860659264536614801218271841886327481124782080000 |
| 24 | 21 | 24 | 132 | 126224597678097616197522274158216573276389376000000 |
| 24 | 22 | 22 | 132 | 71809623871101118126875788361723604603483717632000000000 |
| 24 | 23 | 20 | 132 | 2173205486832253247324764897969726370061707349237946122240000 |
| 24 | 22 | 24 | 136 | 1460860408345085399783324174159332466057281536000000000 |
| 24 | 23 | 22 | 136 | 399344347947105916760415235261986259173201008671064064000000 |
| 24 | 23 | 24 | 140 | 10344929660446727225718574206144479198767905295564800000000 |
| 25 | 13 | 0 | 52 | 877990993826639870275338240000 |
| 25 | 13 | 2 | 56 | 1398281953131315348957020160000 |
| 25 | 14 | 0 | 56 | 2070653959840747470057357705216000 |
| 25 | 13 | 4 | 60 | 993611207005456643315712000000 |
| 25 | 14 | 2 | 60 | 4386356289998008679315809566720000 |
| 25 | 15 | 0 | 60 | 1621781705319666979639948691374080000 |
| 25 | 13 | 6 | 64 | 419524731846748360511078400000 |
| 25 | 14 | 4 | 64 | 3935445808949352845669738151936000 |
| 25 | 15 | 2 | 64 | 4661565139906819952644721548984320000 |
| 25 | 16 | 0 | 64 | 665767259009233267461311948472188928000 |
| 25 | 13 | 8 | 68 | 117761328237683750318899200000 |
| 25 | 14 | 6 | 68 | 2008866291911398239474758123520000 |
| 25 | 15 | 4 | 68 | 5482220344692559279818709315092480000 |
| 25 | 16 | 2 | 68 | 2662243265986616654962062455054794752000 |
| 25 | 17 | 0 | 68 | 174502665290325667535021763041813751398400 |
| 25 | 13 | 10 | 72 | 23225150846876517424005120000 |
| 25 | 14 | 8 | 72 | 657087348911210996386654126080000 |
| 25 | 15 | 6 | 72 | 3527471323386541551283944582021120000 |
| 25 | 16 | 4 | 72 | 4317042871437465189900801354976198656000 |
| 25 | 17 | 2 | 72 | 998814459590619639457186430887693123584000 |
| 25 | 18 | 0 | 72 | 32541455581276992923955860276668778151936000 |
| 25 | 13 | 12 | 76 | 3307494095564574468833280000 |
| 25 | 14 | 10 | 76 | 146209534837446921373680795648000 |
| 25 | 15 | 8 | 76 | 1402895958626144865041348221992960000 |
| 25 | 16 | 6 | 76 | 3721013126198701854355803099075969024000 |
| 25 | 17 | 4 | 76 | 2366970911315994129367441103409076450099200 |
| 25 | 18 | 2 | 76 | 274376149895086950470456643641885941825536000 |
| 25 | 19 | 0 | 76 | 4600775009105588187229317529015014797397196800 |
| 25 | 13 | 14 | 80 | 343268617976787338035200000 |
| 25 | 14 | 12 | 80 | 22807185182759390432913653760000 |
| 25 | 15 | 10 | 80 | 367760379252464904872246551511040000 |
| 25 | 16 | 8 | 80 | 1908694274515526453850497339860451328000 |
| 25 | 17 | 6 | 80 | 2974637256518444209361328373220310515712000 |
| 25 | 18 | 4 | 80 | 1000658248918484971198029197105062452658176000 |
| 25 | 19 | 2 | 80 | 58526569832204579383606712992683936198112051200 |
| 25 | 20 | 0 | 80 | 509654395829257647661878789153105903271463092224 |
| 25 | 13 | 16 | 84 | 25801235991719309721600000 |
| 25 | 14 | 14 | 84 | 2520147187721433811394101248000 |
| 25 | 15 | 12 | 84 | 65748575285165461117206905487360000 |
| 25 | 16 | 10 | 84 | 622415009871747404058172668839460864000 |
| 25 | 17 | 8 | 84 | 2156390045294961708129611203753488364339200 |
| 25 | 18 | 6 | 84 | 1992293326772770119397564282331473561780224000 |
| 25 | 19 | 4 | 84 | 338600690420868122932456905865470866911081267200 |
| 25 | 20 | 2 | 84 | 9916151870566851047895869956197047174969268633600 |
| 25 | 21 | 0 | 84 | 44397680341588367380195901804203100291479476633600 |
| 25 | 13 | 18 | 88 | 1371080173473006796800000 |
| 25 | 14 | 16 | 88 | 195943787592502856871444480000 |
| 25 | 15 | 14 | 88 | 8125230166034503166035364413440000 |
| 25 | 16 | 12 | 88 | 134195511858594709819163839014371328000 |
| 25 | 17 | 10 | 88 | 949126591964303158696271915025537014169600 |
| 25 | 18 | 8 | 88 | 2281683490470034127722769931257140438106112000 |
| 25 | 19 | 6 | 88 | 1113564041030824642538513899532391401233632460800 |
| 25 | 20 | 4 | 88 | 91290286041286732890388447423804982303401307013120 |
| 25 | 21 | 2 | 88 | 1320899188710425949830121830532180690769711359590400 |
| 25 | 22 | 0 | 88 | 2939705890132674186631290164087312319407902949376000 |
| 25 | 13 | 20 | 92 | 48934174541460848640000 |
| 25 | 14 | 18 | 92 | 10440660725732141946961920000 |
| 25 | 15 | 16 | 92 | 690900608277006015295775047680000 |
| 25 | 16 | 14 | 92 | 19493605428369712480508962085535744000 |
| 25 | 17 | 12 | 92 | 264544953886171767453883916698863953510400 |
| 25 | 18 | 10 | 92 | 1518881385882363243502749667216684983779328000 |
| 25 | 19 | 8 | 92 | 2154610211989411354223011693052037330293804236800 |
| 25 | 20 | 6 | 92 | 492732783856675108932570648779829317580943156838400 |
| 25 | 21 | 4 | 92 | 18984701425004086959472870730976131365622092136448000 |
| 25 | 22 | 2 | 92 | 131848044032194649340681139475095814017997202259968000 |
| 25 | 23 | 0 | 92 | 133940025823832523067436114936531179368950739763200000 |
| 25 | 13 | 22 | 96 | 1053852053208514560000 |
| 25 | 14 | 20 | 96 | 360372818348915828391936000 |
| 25 | 15 | 18 | 96 | 39415570757445324611062333440000 |
| 25 | 16 | 16 | 96 | 1908146896076675482363258214547456000 |
| 25 | 17 | 14 | 96 | 47983927323192927832434271328572067020800 |
| 25 | 18 | 12 | 96 | 600722585498002973161884480715531650859008000 |
| 25 | 19 | 10 | 96 | 2400580078395810352292495109287173825777316659200 |
| 25 | 20 | 8 | 96 | 1606723029034695179901492747327412600681770768138240 |
| 25 | 21 | 6 | 96 | 162535848504988786514223426096595720832097191146291200 |
| 25 | 22 | 4 | 96 | 2865925239399893771956386624477682278391950392426496000 |
| 25 | 23 | 2 | 96 | 8833028431871156499953353737520298806862401492746240000 |
| 25 | 24 | 0 | 96 | 3176386433251312256984677026593860423882103964303360000 |
| 25 | 13 | 24 | 100 | 10362360405196800000 |
| 25 | 14 | 22 | 100 | 7170522665171163217920000 |
| 25 | 15 | 20 | 100 | 1426271656378681568361185280000 |
| 25 | 16 | 18 | 100 | 123243202160559627887100970401792000 |
| 25 | 17 | 16 | 100 | 5714032359386987175673158113100300288000 |
| 25 | 18 | 14 | 100 | 146171395792738758996949333446584803786752000 |
| 25 | 19 | 12 | 100 | 1502611447872461313054977962142472881145328435200 |
| 25 | 20 | 10 | 100 | 3081128672437436752710097318531819710318911265177600 |
| 25 | 21 | 8 | 100 | 858531532332278889922075391150314498637981012931379200 |
| 25 | 22 | 6 | 100 | 37302442238297002516439459312446465432691941136400384000 |
| 25 | 23 | 4 | 100 | 280068906013571438178362954720611222307639585144832000000 |
| 25 | 24 | 2 | 100 | 298670482377823569567988025891551557637318667717836800000 |
| 25 | 14 | 24 | 104 | 61087358071883759616000 |
| 25 | 15 | 22 | 104 | 29100008444699960542494720000 |
| 25 | 16 | 20 | 104 | 4985818052891602412420210884608000 |
| 25 | 17 | 18 | 104 | 440836822219150280357499737473862860800 |
| 25 | 18 | 16 | 104 | 22384374418639643158888084396559787098112000 |
| 25 | 19 | 14 | 104 | 533549362371384816514386576379540944532065484800 |
| 25 | 20 | 12 | 104 | 3312743211732732607067992640246204443030714570506240 |
| 25 | 21 | 10 | 104 | 2749058584251261792778889395479712397496781634745139200 |
| 25 | 22 | 8 | 104 | 304258803960136187135696744071203027142104215275438080000 |
| 25 | 23 | 6 | 104 | 5318044549496444912565577897578266845894056251479818240000 |
| 25 | 24 | 4 | 104 | 13333236842256636338177240571014037009489857270828236800000 |
| 25 | 15 | 24 | 108 | 247842405155393030062080000 |
| 25 | 16 | 22 | 108 | 112862368520091408086115287040000 |
| 25 | 17 | 20 | 108 | 21069289801259393057713227464441856000 |
| 25 | 18 | 18 | 108 | 2155638278751292101400804588129974484992000 |
| 25 | 19 | 16 | 108 | 111397872725928635153686910571977314889682124800 |
| 25 | 20 | 14 | 108 | 1912967297781494457651445469568764922232826127974400 |
| 25 | 21 | 12 | 108 | 5109224557616031294865927691189996736501928513083801600 |
| 25 | 22 | 10 | 108 | 1548604444070566033350466897296878037499892857244221440000 |
| 25 | 23 | 8 | 108 | 64053328313912126653175592832922066928554682295831756800000 |
| 25 | 24 | 6 | 108 | 355994124280187717714823747706386171513888983457202176000000 |
| 25 | 16 | 24 | 112 | 1066918974691349634723348480000 |
| 25 | 17 | 22 | 112 | 561710693408260112770033612593561600 |
| 25 | 18 | 20 | 112 | 126101169020748376966228402633552429056000 |
| 25 | 19 | 18 | 112 | 13918958555340159084302882488849682733937459200 |
| 25 | 20 | 16 | 112 | 591951123744604864483781849689047541648494553989120 |
| 25 | 21 | 14 | 112 | 5185850712400586457193757738837824746588084755654246400 |
| 25 | 22 | 12 | 112 | 4772320094165201333644785650776254619272100832738279424000 |
| 25 | 23 | 10 | 112 | 493517896828341801228562330422500378512345512557307494400000 |
| 25 | 24 | 8 | 112 | 6090326274299686424576218624005917919658930190167100620800000 |
| 25 | 17 | 24 | 116 | 6302407193211260489116837478400000 |
| 25 | 18 | 22 | 116 | 4070163067089703792353756113314775040000 |
| 25 | 19 | 20 | 116 | 1020375303997554901476335128637846706978816000 |
| 25 | 20 | 18 | 116 | 101528746688314895487652113971511578575588923801600 |
| 25 | 21 | 16 | 116 | 2696479878335761878395474519470606760275813082962329600 |
| 25 | 22 | 14 | 116 | 8451979109257206545511881520628044371314868449217347584000 |
| 25 | 23 | 12 | 116 | 2391773672668145315938948705079567050097011862539295784960000 |
| 25 | 24 | 10 | 116 | 68049939421380437201422578697891868279171859140157898752000000 |
| 25 | 18 | 24 | 120 | 55162417947963911537796073075507200000 |
| 25 | 19 | 22 | 120 | 40305733192537413243792863528522008756224000 |
| 25 | 20 | 20 | 120 | 9668501486469055524003657467036285717792082100224 |
| 25 | 21 | 18 | 120 | 699152697000498608878230968147804609549037478084608000 |
| 25 | 22 | 16 | 120 | 7977322612943960120865685653395089760971925063907409920000 |
| 25 | 23 | 14 | 120 | 7022467091490236431905106510468405768662484109102489272320000 |
| 25 | 24 | 12 | 120 | 493710376423420592669349910860792691885657334951109690654720000 |
| 25 | 19 | 24 | 124 | 658496204242545624354562901271254138880000 |
| 25 | 20 | 22 | 124 | 477237549954365010391165987763367751503052800000 |
| 25 | 21 | 20 | 124 | 92307342135294370070962118126308377200917083901132800 |
| 25 | 22 | 18 | 124 | 3650951323599611544135743049305859226424935101707059200000 |
| 25 | 23 | 16 | 124 | 11750519693116345542741041551088776204373233810280797962240000 |
| 25 | 24 | 14 | 124 | 2269500293368196317135433059230294145990143932349114482688000000 |
| 25 | 20 | 24 | 128 | 9481838457298927463364144249076155678720000000 |
| 25 | 21 | 22 | 128 | 5941628657631367237291469986607897055857611898880000 |
| 25 | 22 | 20 | 128 | 750568632644566309626190849197252059707678838526836736000 |
| 25 | 23 | 18 | 128 | 10206024819652696120588880879586211281912628225836161433600000 |
| 25 | 24 | 16 | 128 | 6324405057366332947388310672254757316999379637628126730649600000 |
| 25 | 21 | 24 | 132 | 147476375270310847948018444722259838600478720000000 |
| 25 | 22 | 22 | 132 | 68033365331140661276872959525402120785393953328332800000 |
| 25 | 23 | 20 | 132 | 4004324068812629242903248946414768966342999916995349053440000 |
| 25 | 24 | 18 | 132 | 9952908502499399824994641844080701865105625424804339253248000000 |
| 25 | 22 | 24 | 136 | 2218205698274477225642136388499072304901301207040000000 |
| 25 | 23 | 22 | 136 | 591269536810934895046751037276571741366676373544894464000000 |
| 25 | 24 | 20 | 136 | 7881869413667871938297910884426670529098096906680080049111040000 |
| 25 | 23 | 24 | 140 | 27771662328687052739423465077505260004423598342144000000000 |
| 25 | 24 | 22 | 140 | 2554561216624337367746997103590834109298208803616435732480000000 |
| 25 | 24 | 24 | 144 | 211902271619106550197076654219217287901755139774899814400000000 |
| 26 | 13 | 0 | 52 | 164623311342494975676625920000 |
| 26 | 13 | 2 | 56 | 237789227494714964866237440000 |
| 26 | 14 | 0 | 56 | 1244113238252348696180154286080000 |
| 26 | 13 | 4 | 60 | 158526151663143309910824960000 |
| 26 | 14 | 2 | 60 | 2347666622030043657572710440960000 |
| 26 | 15 | 0 | 60 | 1734301463379053913354010794393600000 |
| 26 | 13 | 6 | 64 | 64584728455354681815521280000 |
| 26 | 14 | 4 | 64 | 1936477184197618850013891624960000 |
| 26 | 15 | 2 | 64 | 4345161328333355567757003077713920000 |
| 26 | 16 | 0 | 64 | 1064372150284190252435123528196685824000 |
| 26 | 13 | 8 | 68 | 17940202348709633837644800000 |
| 26 | 14 | 6 | 68 | 934478828047506719139955752960000 |
| 26 | 15 | 4 | 68 | 4562951538467306959200516158668800000 |
| 26 | 16 | 2 | 68 | 3616386729545488798736572691751763968000 |
| 26 | 17 | 0 | 68 | 383278855035040140977331504558895005696000 |
| 26 | 13 | 10 | 72 | 3588040469741926767528960000 |
| 26 | 14 | 8 | 72 | 296324302261086591974325043200000 |
| 26 | 15 | 6 | 72 | 2696736659178473808527653655592960000 |
| 26 | 16 | 4 | 72 | 5034360308201636386524962811482603520000 |
| 26 | 17 | 2 | 72 | 1811728814774169839894985137250329690112000 |
| 26 | 18 | 0 | 72 | 93577693426965174739737198689130349854720000 |
| 26 | 13 | 12 | 76 | 531561551072878039633920000 |
| 26 | 14 | 10 | 76 | 65461096265890166743531069440000 |
| 26 | 15 | 8 | 76 | 1012461410969178972846103953653760000 |
| 26 | 16 | 6 | 76 | 3814009884041795677613398467085074432000 |
| 26 | 17 | 4 | 76 | 3520779451928655292659559498677542191104000 |
| 26 | 18 | 2 | 76 | 632896274167603140694668612586882228813824000 |
| 26 | 19 | 0 | 76 | 16857361507709849988549559897640443685791334400 |
| 26 | 13 | 14 | 80 | 59062394563653115514880000 |
| 26 | 14 | 12 | 80 | 10383326464009054115823943680000 |
| 26 | 15 | 10 | 80 | 257096140511228926184149207695360000 |
| 26 | 16 | 8 | 80 | 1773349716891490160151967920560406528000 |
| 26 | 17 | 6 | 80 | 3657979162808888273490783621091757654016000 |
| 26 | 18 | 4 | 80 | 1813950202397602801788142124922421358100480000 |
| 26 | 19 | 2 | 80 | 167593451035558796742702716810568523685088460800 |
| 26 | 20 | 0 | 80 | 2356546065201727309312767614577368880161331609600 |
| 26 | 13 | 16 | 84 | 4921866213637759626240000 |
| 26 | 14 | 14 | 84 | 1197155362875539549409607680000 |
| 26 | 15 | 12 | 84 | 45654371241738667859250497617920000 |
| 26 | 16 | 10 | 84 | 540615037018948737435854339199860736000 |
| 26 | 17 | 8 | 84 | 2254019739957180196909480241191346503680000 |
| 26 | 18 | 6 | 84 | 2812987832114106067499114407518535742914560000 |
| 26 | 19 | 4 | 84 | 740419323065370492675946322969140953787190476800 |
| 26 | 20 | 2 | 84 | 35170564011067017120331585134455259920170431283200 |
| 26 | 21 | 0 | 84 | 261954501813191496080296191907550104198377268838400 |
| 26 | 13 | 18 | 88 | 303818902076404915200000 |
| 26 | 14 | 16 | 88 | 100087182438590901776302080000 |
| 26 | 15 | 14 | 88 | 5751137547168161257571211509760000 |
| 26 | 16 | 12 | 88 | 112190829177608963214481801470541824000 |
| 26 | 17 | 10 | 88 | 877230201188101994657160075916490833920000 |
| 26 | 18 | 8 | 88 | 2539653607442673082406463648528376950423552000 |
| 26 | 19 | 6 | 88 | 1835693512203079616912070943057278126185565388800 |
| 26 | 20 | 4 | 88 | 244720667781479674529747101552578715876989704601600 |
| 26 | 21 | 2 | 88 | 5929369491498197705473098965597752640562938039500800 |
| 26 | 22 | 0 | 88 | 23096992191362233126619323956315600957446427770880000 |
| 26 | 13 | 20 | 92 | 13503062314506885120000 |
| 26 | 14 | 18 | 92 | 5959441521884468678860800000 |
| 26 | 15 | 16 | 92 | 513196173882182775783170211840000 |
| 26 | 16 | 14 | 92 | 16137057687315284398058689264091136000 |
| 26 | 17 | 12 | 92 | 224803725221864703490178796504707235840000 |
| 26 | 18 | 10 | 92 | 1385383076614650166274283727431375771402240000 |
| 26 | 19 | 8 | 92 | 2678703078067226595080776095791204819050640179200 |
| 26 | 20 | 6 | 92 | 993231742979052112644517566381567684509234626560000 |
| 26 | 21 | 4 | 92 | 64759669929845045469706901591111424538376313136742400 |
| 26 | 22 | 2 | 92 | 790352685680765044573756287362203794500718138753024000 |
| 26 | 23 | 0 | 92 | 1554179816453084593922565875922608191339593990144000000 |
| 26 | 13 | 22 | 96 | 409183706500208640000 |
| 26 | 14 | 20 | 96 | 242959099884665216532480000 |
| 26 | 15 | 18 | 96 | 31854080632801324372813578240000 |
| 26 | 16 | 16 | 96 | 1611272764511557608586001279090688000 |
| 26 | 17 | 14 | 96 | 38853981446132018503652444006129860608000 |
| 26 | 18 | 12 | 96 | 474063997524473955348809629749082935263232000 |
| 26 | 19 | 10 | 96 | 2294949074687913310256977295158414017194832691200 |
| 26 | 20 | 8 | 96 | 2434549249531737799389335419986689678334822344294400 |
| 26 | 21 | 6 | 96 | 423211437981186713446034997074292255461981516149555200 |
| 26 | 22 | 4 | 96 | 13254635367479602829867281866835455082511515703574528000 |
| 26 | 23 | 2 | 96 | 79125600652353098819750794797487202900077501910876160000 |
| 26 | 24 | 0 | 96 | 72026591143678385938607509819574958510581955428352000000 |
| 26 | 13 | 24 | 100 | 7577476046300160000 |
| 26 | 14 | 22 | 100 | 6281949915013524111360000 |
| 26 | 15 | 20 | 100 | 1319863189745073936673751040000 |
| 26 | 16 | 18 | 100 | 109931721731184782345085905928192000 |
| 26 | 17 | 16 | 100 | 4562347879943755866778047056190111744000 |
| 26 | 18 | 14 | 100 | 105024067315516117001156165254564489986048000 |
| 26 | 19 | 12 | 100 | 1158425114540224876840193331040194683177061580800 |
| 26 | 20 | 10 | 100 | 3520755785638906108284974099684688244821649784832000 |
| 26 | 21 | 8 | 100 | 1709930250539949708028643924549803453224763801573785600 |
| 26 | 22 | 6 | 100 | 134511893368766572712454493144547880040624203994497024000 |
| 26 | 23 | 4 | 100 | 1973729318133926245920827567306252541467415978254008320000 |
| 26 | 24 | 2 | 100 | 5319990723788145540378422192979751008981672931413196800000 |
| 26 | 25 | 0 | 100 | 1735668301026609911852341375245930874478435380494336000000 |
| 26 | 13 | 26 | 104 | 64764752532480000 |
| 26 | 14 | 24 | 104 | 87728088602409615360000 |
| 26 | 15 | 22 | 104 | 33662254413882355345244160000 |
| 26 | 16 | 20 | 104 | 4928081234584232417614306344960000 |
| 26 | 17 | 18 | 104 | 360146879951293296877678124536954880000 |
| 26 | 18 | 16 | 104 | 15323551559907126288640107082285106331648000 |
| 26 | 19 | 14 | 104 | 354883393204068565398333524478434087690620108800 |
| 26 | 20 | 12 | 104 | 2900252770380033844886166443717934853711646529945600 |
| 26 | 21 | 10 | 104 | 4175504318840866099549320896407752214672767850433740800 |
| 26 | 22 | 8 | 104 | 858546186489292466358500362674513240258360293827018752000 |
| 26 | 23 | 6 | 104 | 29860620792387651471116126909213931518735318932877475840000 |
| 26 | 24 | 4 | 104 | 190652138620379337710568269240659605266575524727514726400000 |
| 26 | 25 | 2 | 104 | 180506353626758748215942850311729610866948897318633472000000 |
| 26 | 14 | 26 | 108 | 424338658592808960000 |
| 26 | 15 | 24 | 108 | 444823991261829825085440000 |
| 26 | 16 | 22 | 108 | 134115988926061255114342268928000 |
| 26 | 17 | 20 | 108 | 18474890957442037556180210867503104000 |
| 26 | 18 | 18 | 108 | 1470192981930732830975334353632216743936000 |
| 26 | 19 | 16 | 108 | 68013891505880061513410176940583752930898739200 |
| 26 | 20 | 14 | 108 | 1345045527116454593474348747241180512695521116160000 |
| 26 | 21 | 12 | 108 | 5890724322004628643105941848400729189675297474504294400 |
| 26 | 22 | 10 | 108 | 3404750034082384090789231559535292521593459019935121408000 |
| 26 | 23 | 8 | 108 | 287706072490975164228723240927635342134959046382447493120000 |
| 26 | 24 | 6 | 108 | 4137388205977441966866072000798821853007491460699992883200000 |
| 26 | 25 | 4 | 108 | 8988071390058665087505155234995455642681155166998102016000000 |
| 26 | 15 | 26 | 112 | 1860421918887615283200000 |
| 26 | 16 | 24 | 112 | 1871862054843641776562110464000 |
| 26 | 17 | 22 | 112 | 572792494416481815022981163778048000 |
| 26 | 18 | 20 | 112 | 90395053068731471775284783628605718528000 |
| 26 | 19 | 18 | 112 | 8256603934709357043633167542062213344998195200 |
| 26 | 20 | 16 | 112 | 361482699158084511155412272922877220610193647206400 |
| 26 | 21 | 14 | 112 | 4567244679256504896858063999160025515299860324234035200 |
| 26 | 22 | 12 | 112 | 8087290511921225558867259982946491770204506170891173888000 |
| 26 | 23 | 10 | 112 | 1766179313686716220617979590526238078603231224293218058240000 |
| 26 | 24 | 8 | 112 | 57745071861462762907963974785750861856742949898847204147200000 |
| 26 | 25 | 6 | 112 | 270381368311627455701613382040886584881077838397181001728000000 |
| 26 | 16 | 26 | 116 | 8320126893853611265228800000 |
| 26 | 17 | 24 | 116 | 9179476409550452084947620200448000 |
| 26 | 18 | 22 | 116 | 3341301113224567623713502526829494272000 |
| 26 | 19 | 20 | 116 | 625910183080957835215855103731918097822515200 |
| 26 | 20 | 18 | 116 | 57981640026931047497686598411153982262175858688000 |
| 26 | 21 | 16 | 116 | 1894968104478811596204450102863197252978151469455769600 |
| 26 | 22 | 14 | 116 | 10894381313040111937167336047538408883543087183004958720000 |
| 26 | 23 | 12 | 116 | 6745673499195368140383710546208740273331000159746025062400000 |
| 26 | 24 | 10 | 116 | 524615920537169573739848186812016837114159562249878057779200000 |
| 26 | 25 | 8 | 116 | 5274918980644634547500647011546008890408910338842565804032000000 |
| 26 | 17 | 26 | 120 | 49450512957052634961562828800000 |
| 26 | 18 | 24 | 120 | 64340776280696729719295110419578880000 |
| 26 | 19 | 22 | 120 | 28066465986347037872021108107723071396249600 |
| 26 | 20 | 20 | 120 | 5562825225265502799564444494017574818014245683200 |
| 26 | 21 | 18 | 120 | 430523486794175906726740593756525083299465904573644800 |
| 26 | 22 | 16 | 120 | 7793407429726696763113685191067237968517269692604219392000 |
| 26 | 23 | 14 | 120 | 15346353690124530773748354986602607610394032187735151738880000 |
| 26 | 24 | 12 | 120 | 3065763935595086845636454098789166756481316393613673470361600000 |
| 26 | 25 | 10 | 120 | 68205998493435853800427881235707107608549007714308998561792000000 |
| 26 | 18 | 26 | 124 | 436706546005078197546854803046400000 |
| 26 | 19 | 24 | 124 | 651891372564221817192093585374623825920000 |
| 26 | 20 | 22 | 124 | 306194018594813466509032183852771801346290483200 |
| 26 | 21 | 20 | 124 | 54718946572066221311377118621280240381131727097036800 |
| 26 | 22 | 18 | 124 | 2811585513717226434216274207506513437180028984420728832000 |
| 26 | 23 | 16 | 124 | 19491046080526179705213182169065242149698132073498531594240000 |
| 26 | 24 | 14 | 124 | 11178784087029967575524221735814434019721142959635947742822400000 |
| 26 | 25 | 12 | 124 | 583232172905604674812058808172879609384409350004427051761664000000 |
| 26 | 19 | 26 | 128 | 5424822031083902220759937617022156800000 |
| 26 | 20 | 24 | 128 | 8550034094650505126996178358354021208555520000 |
| 26 | 21 | 22 | 128 | 3799111304808130295216476617646808476026987872256000 |
| 26 | 22 | 20 | 128 | 513785543413829302014419167272524757979151468643483648000 |
| 26 | 23 | 18 | 128 | 12669723930951104919220606229513224066622513619483198750720000 |
| 26 | 24 | 16 | 128 | 24182774002631567673225619500872117619618070503911850403430400000 |
| 26 | 25 | 14 | 128 | 3235278683970722356108912112688077872567554244128198063292416000000 |
| 26 | 20 | 26 | 132 | 84662381093328169678050085636405198848000000 |
| 26 | 21 | 24 | 132 | 128927462197110706132606652412264313970176819200000 |
| 26 | 22 | 22 | 132 | 47445551123974057557942592747962069376496951309107200000 |
| 26 | 23 | 20 | 132 | 3840475949037855830337909309810247644205312414655226839040000 |
| 26 | 24 | 18 | 132 | 28740782768324516503615658733900321595370295359031809251737600000 |
| 26 | 25 | 16 | 132 | 11229177912677605848614374182045342754790010931501247722684416000000 |
| 26 | 21 | 26 | 136 | 1500330317609735410819942074751689519267840000000 |
| 26 | 22 | 24 | 136 | 2016026961579309913151559154193167478862762737664000000 |
| 26 | 23 | 22 | 136 | 520404962592219140250954279811540745279769329580323635200000 |
| 26 | 24 | 20 | 136 | 16729711625746823073636636418777246669324484131599811608576000000 |
| 26 | 25 | 18 | 136 | 23021780312144641029924935778817015320484103549030796166692864000000 |
| 26 | 22 | 26 | 140 | 27610208618629816898543334167567444084156006400000000 |
| 26 | 23 | 24 | 140 | 29336539415419749707680381602717434534074028497305600000000 |
| 26 | 24 | 22 | 140 | 4048581957890430382975081051820774464464190724638953701376000000 |
| 26 | 25 | 20 | 140 | 25460663389919184925414073149391548507630886708503442614124544000000 |
| 26 | 23 | 26 | 144 | 478354428544762743162420882381866173942978314240000000000 |
| 26 | 24 | 24 | 144 | 341014998798688341600875135699551366957739440648853913600000000 |
| 26 | 25 | 22 | 144 | 13044367924153449887165587967224825268925447848173573767168000000000 |
| 26 | 24 | 26 | 148 | 6765229385461413135344236821114578583359679753093120000000000 |
| 26 | 25 | 24 | 148 | 2298015248551218063170618730804169245894956371813764956160000000000 |
| 26 | 25 | 26 | 152 | 57448842714347491860157148758122341150491100741369856000000000000 |
| 27 | 14 | 0 | 56 | 462262258249725891699965583360000 |
| 27 | 14 | 2 | 60 | 787557921462495963636978401280000 |
| 27 | 15 | 0 | 60 | 1372569642184341661008502253027328000 |
| 27 | 14 | 4 | 64 | 604935794746554870619708047360000 |
| 27 | 15 | 2 | 64 | 3047844590506691480747780981194752000 |
| 27 | 16 | 0 | 64 | 1345286835652488886551629008113500160000 |
| 27 | 14 | 6 | 68 | 279006026927132225443051929600000 |
| 27 | 15 | 4 | 68 | 2914192925258753539862152815771648000 |
| 27 | 16 | 2 | 68 | 3962528603569736178257998495772835840000 |
| 27 | 17 | 0 | 68 | 687665175425146218125527448041209987072000 |
| 27 | 14 | 8 | 72 | 86543536130175273632798515200000 |
| 27 | 15 | 6 | 72 | 1609947397895057782102470876659712000 |
| 27 | 16 | 4 | 72 | 4866829776637842483130848250871808000000 |
| 27 | 17 | 2 | 72 | 2746925986458504052154031662155674157056000 |
| 27 | 18 | 0 | 72 | 223614564346793080194048993009161857086259200 |
| 27 | 14 | 10 | 76 | 19117079622784985817394298880000 |
| 27 | 15 | 8 | 76 | 578866778420059814933891223060480000 |
| 27 | 16 | 6 | 76 | 3336249446900777039843813939179683840000 |
| 27 | 17 | 4 | 76 | 4523605343752854128885016106961643503616000 |
| 27 | 18 | 2 | 76 | 1243063322840454662827944328774793927904460800 |
| 27 | 19 | 0 | 76 | 51654062230516443997651373190086413435011072000 |
| 27 | 14 | 12 | 80 | 3100066965857024727145021440000 |
| 27 | 15 | 10 | 80 | 144011209941674197723992552505344000 |
| 27 | 16 | 8 | 80 | 1441815241349496054554456812181913600000 |
| 27 | 17 | 6 | 80 | 4049042421991120147869619038194963054592000 |
| 27 | 18 | 4 | 80 | 2889914031518924876537706101674437856827801600 |
| 27 | 19 | 2 | 80 | 410653870678390102938756973916546029798293504000 |
| 27 | 20 | 0 | 80 | 9067154318578574834168673515856141547671335731200 |
| 27 | 14 | 14 | 84 | 374219331955306139902279680000 |
| 27 | 15 | 12 | 84 | 25619502638861978668178253152256000 |
| 27 | 16 | 10 | 84 | 419184917560203469847377584307568640000 |
| 27 | 17 | 8 | 84 | 2211366326428956134309818877643190173696000 |
| 27 | 18 | 6 | 84 | 3632774727809854163272402327175665082066534400 |
| 27 | 19 | 4 | 84 | 1417742559615570919070987509477708949505441792000 |
| 27 | 20 | 2 | 84 | 105704721192221330088129846576501275176581306777600 |
| 27 | 21 | 0 | 84 | 1259111572356909624050528314568550745684258829893632 |
| 27 | 14 | 16 | 88 | 33665564901282275843481600000 |
| 27 | 15 | 14 | 88 | 3309154898599760627159896817664000 |
| 27 | 16 | 12 | 88 | 85018269567613626560525283742187520000 |
| 27 | 17 | 10 | 88 | 787403475204010032667932738399359729664000 |
| 27 | 18 | 8 | 88 | 2711029318099098819033627117298602131167641600 |
| 27 | 19 | 6 | 88 | 2710803403781854622752687130189520347087241216000 |
| 27 | 20 | 4 | 88 | 562050988005354501094712146411137565464069144576000 |
| 27 | 21 | 2 | 88 | 21917401043264269219469089057333931750484911113371648 |
| 27 | 22 | 0 | 88 | 140744997886168659824238207332197979573776976078438400 |
| 27 | 14 | 18 | 92 | 2231246016849117697228800000 |
| 27 | 15 | 16 | 92 | 310735549284577339641155813376000 |
| 27 | 16 | 14 | 92 | 12245720327561545528101250463170560000 |
| 27 | 17 | 12 | 92 | 190297969741626270217215350811012366336000 |
| 27 | 18 | 10 | 92 | 1269626841260440475769837837433524827927347200 |
| 27 | 19 | 8 | 92 | 3063778729613848251109860771698111209455747072000 |
| 27 | 20 | 6 | 92 | 1722822455281021232192315430465890197019342300774400 |
| 27 | 21 | 4 | 92 | 181957218099628332029842909575065754384348972067061760 |
| 27 | 22 | 2 | 92 | 3683820923033880740993747326032391735276148276959641600 |
| 27 | 23 | 0 | 92 | 12566819293700145437326419367193825822070156608667648000 |
| 27 | 14 | 20 | 96 | 105972033044250034421760000 |
| 27 | 15 | 18 | 96 | 20944741684173682573898219520000 |
| 27 | 16 | 16 | 96 | 1256560093266337015567663988736000000 |
| 27 | 17 | 14 | 96 | 31911545671026811953850168345765085184000 |
| 27 | 18 | 12 | 96 | 389069952339285320268458328283841892345446400 |
| 27 | 19 | 10 | 96 | 2092742720194037764865354544024465630585421824000 |
| 27 | 20 | 8 | 96 | 3184831349671921812106151260632157077068656410624000 |
| 27 | 21 | 6 | 96 | 901831019768608477500754655391110888046626288267427840 |
| 27 | 22 | 4 | 96 | 47341963275271552265476302932969790954643173494331801600 |
| 27 | 23 | 2 | 96 | 491696013655170229145199186846714908591286700254167040000 |
| 27 | 24 | 0 | 96 | 858988634313117466873530626554851288771332972268748800000 |
| 27 | 14 | 22 | 100 | 3417502316689742561280000 |
| 27 | 15 | 20 | 100 | 982869196029813187144777728000 |
| 27 | 16 | 18 | 100 | 90797864638052567148153038438400000 |
| 27 | 17 | 16 | 100 | 3738775425162314671832305808260988928000 |
| 27 | 18 | 14 | 100 | 80243910055678981656699603654593156952883200 |
| 27 | 19 | 12 | 100 | 887074602848191514429660505470035226831880192000 |
| 27 | 20 | 10 | 100 | 3512238378467437558731186084368394039551982147993600 |
| 27 | 21 | 8 | 100 | 2765229175248071267018231096414517161547501046301982720 |
| 27 | 22 | 6 | 100 | 370614540137550568626765374905071585544164282702023884800 |
| 27 | 23 | 4 | 100 | 9549567889920616059376966971396805170090918956985483264000 |
| 27 | 24 | 2 | 100 | 49377693519870457752501900935968798814865162125998817280000 |
| 27 | 25 | 0 | 100 | 40456738237214196762326568403651244659153413398310420480000 |
| 27 | 14 | 24 | 104 | 67106127866034216960000 |
| 27 | 15 | 22 | 104 | 30260591571454259537313792000 |
| 27 | 16 | 20 | 104 | 4482730969881988691695642214400000 |
| 27 | 17 | 18 | 104 | 303500239831552718220335433215115264000 |
| 27 | 18 | 16 | 104 | 11290189319203905034222669520046848055705600 |
| 27 | 19 | 14 | 104 | 241173454810479797556838728802869585402396672000 |
| 27 | 20 | 12 | 104 | 2279984479101033532127741808695725768780579602432000 |
| 27 | 21 | 10 | 104 | 5127670076998318637427341864656564202149980404585594880 |
| 27 | 22 | 8 | 104 | 1830802409590948098913204445554016941737018453010887475200 |
| 27 | 23 | 6 | 104 | 113799761962051570383851518140139549155909206396154937344000 |
| 27 | 24 | 4 | 104 | 1404307440672431463200519160617619496979336980291104276480000 |
| 27 | 25 | 2 | 104 | 3331427508564533773624395339726831705910148990700009553920000 |
| 27 | 26 | 0 | 104 | 989690035371586948358286792450576308288807153512218624000000 |
| 27 | 14 | 26 | 108 | 606198083704012800000 |
| 27 | 15 | 24 | 108 | 542727570919398734757888000 |
| 27 | 16 | 22 | 108 | 142422111120906744793493667840000 |
| 27 | 17 | 20 | 108 | 16611418078439410714354445539344384000 |
| 27 | 18 | 18 | 108 | 1081231580597340633519529708847616124518400 |
| 27 | 19 | 16 | 108 | 43079656865537410841932544893217971076333568000 |
| 27 | 20 | 14 | 108 | 884954566577323958544888589226558919324887049830400 |
| 27 | 21 | 12 | 108 | 5526475107438057510134063574322761288937571266508881920 |
| 27 | 22 | 10 | 108 | 5603491293836511277562495296379726188505977328918908108800 |
| 27 | 23 | 8 | 108 | 867535279939468341033559796141347730155108767791094693888000 |
| 27 | 24 | 6 | 108 | 24502367921681480469301287173916197938478489319428409262080000 |
| 27 | 25 | 4 | 108 | 134210380387817381478365749555623131559345934860953636044800000 |
| 27 | 26 | 2 | 108 | 113405303505017150635305311554857301188651888274443337728000000 |
| 27 | 15 | 26 | 112 | 4204007958410676928512000 |
| 27 | 16 | 24 | 112 | 2580798488403635114396221440000 |
| 27 | 17 | 22 | 112 | 579173382714919805741159770226688000 |
| 27 | 18 | 20 | 112 | 68972061966488405779666122378235713945600 |
| 27 | 19 | 18 | 112 | 5095637636350634427206699364854276460380160000 |
| 27 | 20 | 16 | 112 | 212533405845905407028530042931781109527361880064000 |
| 27 | 21 | 14 | 112 | 3364588076539967732201620347560002445694498997618606080 |
| 27 | 22 | 12 | 112 | 10201941972921676487759357758715592039309821478784991232000 |
| 27 | 23 | 10 | 112 | 4199714411271868683431752694182817494833168202479112814592000 |
| 27 | 24 | 8 | 112 | 276211313873480073569625276027965553313573718762850311208960000 |
| 27 | 25 | 6 | 112 | 3307298428374075122356713812630692134714446922912865714176000000 |
| 27 | 26 | 4 | 112 | 6270489508799848624620190368053616543011583816782139359232000000 |
| 27 | 16 | 26 | 116 | 19692228220533222648053760000 |
| 27 | 17 | 24 | 116 | 11447199034007555685159602749440000 |
| 27 | 18 | 22 | 116 | 2784755055615823074542310963018517708800 |
| 27 | 19 | 20 | 116 | 393920692764758235343096337218610090999808000 |
| 27 | 20 | 18 | 116 | 32313346954091559846956777146310429984318658969600 |
| 27 | 21 | 16 | 116 | 1169193586326881770657492071841802464194161420072386560 |
| 27 | 22 | 14 | 116 | 10501215715288747319702310170815851694866266460780075417600 |
| 27 | 23 | 12 | 116 | 12523321453969880469553591271506502505119696636140578668544000 |
| 27 | 24 | 10 | 116 | 2020770709674595808304695752408386231778115129278159745187840000 |
| 27 | 25 | 8 | 116 | 53073262096339139144361733446804463915366014728575289131008000000 |
| 27 | 26 | 6 | 116 | 211407078605836204750140210288282331259585625305953018576896000000 |
| 27 | 17 | 26 | 120 | 95370547552682078097459118080000 |
| 27 | 18 | 24 | 120 | 63768494459811775748531396141069107200 |
| 27 | 19 | 22 | 120 | 19049549541200501281375414923728277995520000 |
| 27 | 20 | 20 | 120 | 3108649219451873127070336965258021627394994995200 |
| 27 | 21 | 18 | 120 | 240394053725545965774218852423227677621635213049200640 |
| 27 | 22 | 16 | 120 | 5856265930091251341470880320568369650852723578637176012800 |
| 27 | 23 | 14 | 120 | 21930607378445786578096654431595160014009997682846644305920000 |
| 27 | 24 | 12 | 120 | 9420140788763160475718266548768549269707919612327116060753920000 |
| 27 | 25 | 10 | 120 | 563079214334709761818441476002597381253350309425714993456742400000 |
| 27 | 26 | 8 | 120 | 4673432327939485168320215948613299611990159120039777337868288000000 |
| 27 | 18 | 26 | 124 | 622338711706918059919979933859840000 |
| 27 | 19 | 24 | 124 | 519943639810731963998373767993119211520000 |
| 27 | 20 | 22 | 124 | 182881806478842316274179657108994269774872576000 |
| 27 | 21 | 20 | 124 | 29752077690385197938148441086928503646900596854751232 |
| 27 | 22 | 18 | 124 | 1766668511146477939025986953683633076713976899787816960000 |
| 27 | 23 | 16 | 124 | 21193963885766939764021063608869363933745772476259381542912000 |
| 27 | 24 | 14 | 124 | 26985664080835114633711795067271373364939286403751238382387200000 |
| 27 | 25 | 12 | 124 | 3919156507812467433537286816677222844906454589063025522177474560000 |
| 27 | 26 | 10 | 124 | 69385556930356977313154958084088818894801408287137925852823552000000 |
| 27 | 19 | 26 | 128 | 6065352556508827699220923007002214400000 |
| 27 | 20 | 24 | 128 | 5980945977739555347114606362709296607657984000 |
| 27 | 21 | 22 | 128 | 2172333273741250147493314083651000868276201479733248 |
| 27 | 22 | 20 | 128 | 297697074902015296625074197736481234316035930417056972800 |
| 27 | 23 | 18 | 128 | 10606858162195446715176629081991054137564414851839336382464000 |
| 27 | 24 | 16 | 128 | 44957169564056785178269802792889852373419648462074077847224320000 |
| 27 | 25 | 14 | 128 | 17461325733141660332141496188263880752810868154654150025795338240000 |
| 27 | 26 | 12 | 128 | 692458166966232716423572024729957394101206972640832203706597376000000 |
| 27 | 20 | 26 | 132 | 82864627791133569519243272584345430261760000 |
| 27 | 21 | 24 | 132 | 85935696824105491685926266884037883169322565632000 |
| 27 | 22 | 22 | 132 | 28024452278154626439921422733869322422306293225095168000 |
| 27 | 23 | 20 | 132 | 2677252912218632045221656384152294442240766579713245184000000 |
| 27 | 24 | 18 | 132 | 40340329624431269570773311087721454872346117053005469203824640000 |
| 27 | 25 | 16 | 132 | 47760953697765329429341839285435224512531504106432745869987020800000 |
| 27 | 26 | 14 | 132 | 4576487388516223076701426592791135940022917991144520113746608128000000 |
| 27 | 21 | 26 | 136 | 1414334505633062612032642780493894932601241600000 |
| 27 | 22 | 24 | 136 | 1374593994418978475169539512944914708955426245836800000 |
| 27 | 23 | 22 | 136 | 347009549531629028192611760686348699174464194485369700352000 |
| 27 | 24 | 20 | 136 | 17745029978395928723466764036258013304835684604793604202823680000 |
| 27 | 25 | 18 | 136 | 75257410478952945649540498487027198752893355725755353852280832000000 |
| 27 | 26 | 16 | 136 | 19444682613757612782981859536817759348798627028475235058004787200000000 |
| 27 | 22 | 26 | 140 | 27271422345859391721128518252055501343264079872000000 |
| 27 | 23 | 24 | 140 | 22063880504199034877752817578612668034533103812948787200000 |
| 27 | 24 | 22 | 140 | 3549088892600781120981238675401264039008891737673734532628480000 |
| 27 | 25 | 20 | 140 | 62143753590841080537022152513248516599077612740404832221286891520000 |
| 27 | 26 | 18 | 140 | 50655902336537722136116178282401214482740154506399656196691722240000000 |
| 27 | 23 | 26 | 144 | 543643471946306150443505815716542506390602771333120000000 |
| 27 | 24 | 24 | 144 | 315690172568212058585016544868516116942785734451300139008000000 |
| 27 | 25 | 22 | 144 | 23405459436578760678962258514997077742427046232587599041611694080000 |
| 27 | 26 | 20 | 144 | 75218209199223896624131043678745669361060293372414644255169970176000000 |
| 27 | 24 | 26 | 148 | 10161984329896120771125981350378444101529662044241920000000000 |
| 27 | 25 | 24 | 148 | 3356856278198392786246352521708214927703344950881990066831360000000 |
| 27 | 26 | 22 | 148 | 56647403882842654594121320448287524574166092885768703190975381504000000 |
| 27 | 25 | 26 | 152 | 154490290785622733256120590496310818143234551664343829708800000000 |
| 27 | 26 | 24 | 152 | 17581469924974418890863093128579845990939086659883727614640128000000000 |
| 27 | 26 | 26 | 156 | 1405453301381666039307741802909883476523494212451211610685440000000000 |
| 28 | 14 | 0 | 56 | 80006929312452558178840197120000 |
| 28 | 14 | 2 | 60 | 124455223374926201611529195520000 |
| 28 | 15 | 0 | 60 | 757185579013051010604543625543680000 |
| 28 | 14 | 4 | 64 | 89884327993002256719437752320000 |
| 28 | 15 | 2 | 64 | 1511135322218353939967187492003840000 |
| 28 | 16 | 0 | 64 | 1313625081850703457891613237160312832000 |
| 28 | 14 | 6 | 68 | 39948590219112114097527889920000 |
| 28 | 15 | 4 | 68 | 1335015304139028332949219534643200000 |
| 28 | 16 | 2 | 68 | 3412156101426371997649735980702105600000 |
| 28 | 17 | 0 | 68 | 998042986778221376960541879245562445824000 |
| 28 | 14 | 8 | 72 | 12206513678062034863133521920000 |
| 28 | 15 | 6 | 72 | 698286561255924527715862505472000000 |
| 28 | 16 | 4 | 72 | 3777832048708910087647298521641418752000 |
| 28 | 17 | 2 | 72 | 3437948076072279398126579469188228972544000 |
| 28 | 18 | 0 | 72 | 442999979447551431050771586304488983494656000 |
| 28 | 14 | 10 | 76 | 2712558595124896636251893760000 |
| 28 | 15 | 8 | 76 | 242994615696081740537626312212480000 |
| 28 | 16 | 6 | 76 | 2392472254004531589342859933229383680000 |
| 28 | 17 | 4 | 76 | 4935980567441710648717974895062174400512000 |
| 28 | 18 | 2 | 76 | 2070440135785405211263709538102119516602368000 |
| 28 | 19 | 0 | 76 | 132918784238875563657177444314383112798522572800 |
| 28 | 14 | 12 | 80 | 452093099187482772708648960000 |
| 28 | 15 | 10 | 80 | 59726320729057807424388086538240000 |
| 28 | 16 | 8 | 80 | 978019528758959173359301346144747520000 |
| 28 | 17 | 6 | 80 | 3933657317692931295579451603006153162752000 |
| 28 | 18 | 4 | 80 | 4030313941185740658119025326377867964055552000 |
| 28 | 19 | 2 | 80 | 864867817602099177224819366930601555234127872000 |
| 28 | 20 | 0 | 80 | 29402186794753166820810354222137941625479259750400 |
| 28 | 14 | 14 | 84 | 57408647515870828280463360000 |
| 28 | 15 | 12 | 84 | 10713668776167249156333066117120000 |
| 28 | 16 | 10 | 84 | 275000480637792681829523919551594496000 |
| 28 | 17 | 8 | 84 | 1963156939120420797627972653973862219776000 |
| 28 | 18 | 6 | 84 | 4278764029042662538214434328262119701610496000 |
| 28 | 19 | 4 | 84 | 2400186652081160053992976062385718776008435302400 |
| 28 | 20 | 2 | 84 | 273430200363670728038325383676473216431743723110400 |
| 28 | 21 | 0 | 84 | 5063696377372295422331667167553207931200863836569600 |
| 28 | 14 | 16 | 88 | 5581396286265219416156160000 |
| 28 | 15 | 14 | 88 | 1425414192894986835960734515200000 |
| 28 | 16 | 12 | 88 | 55107708637572735794901309439180800000 |
| 28 | 17 | 10 | 88 | 655613720659622144106981627112537325568000 |
| 28 | 18 | 8 | 88 | 2761655230446451964047404558090721426931712000 |
| 28 | 19 | 6 | 88 | 3660178637599707547590522960229388843432804352000 |
| 28 | 20 | 4 | 88 | 1132047929351669094890703082318314233305006866432000 |
| 28 | 21 | 2 | 88 | 68861657130287405574530835846015051369237309082828800 |
| 28 | 22 | 0 | 88 | 701054028452539544264457500308053490960438471182778368 |
| 28 | 14 | 18 | 92 | 413436761945571808604160000 |
| 28 | 15 | 16 | 92 | 141188654204412772638320640000000 |
| 28 | 16 | 14 | 92 | 8013774256503839512974765174030336000 |
| 28 | 17 | 12 | 92 | 152314903181722474599044084810987470848000 |
| 28 | 18 | 10 | 92 | 1155262872655344735907653047234471512768512000 |
| 28 | 19 | 8 | 92 | 3335227261974232560672119265800173155044976230400 |
| 28 | 20 | 6 | 92 | 2661549751178629109187694088045306399875097690112000 |
| 28 | 21 | 4 | 92 | 437797390585319153371219853032821763786783349696102400 |
| 28 | 22 | 2 | 92 | 14153979896014363263842367829866421827905203456746455040 |
| 28 | 23 | 0 | 92 | 78927173081882374024483746535846959891164485479353548800 |
| 28 | 14 | 20 | 96 | 22968708996976211589120000 |
| 28 | 15 | 18 | 96 | 10328844686268226541934551040000 |
| 28 | 16 | 16 | 96 | 849753063500635574894861384417280000 |
| 28 | 17 | 14 | 96 | 25142523519969313995756193308130148352000 |
| 28 | 18 | 12 | 96 | 326602622363556492904287194929298922799104000 |
| 28 | 19 | 10 | 96 | 1898444853255956057168319628502317672019735347200 |
| 28 | 20 | 8 | 96 | 3771581121678954092941970985018877495506882684518400 |
| 28 | 21 | 6 | 96 | 1645808706170155014040196837614414323019609617412915200 |
| 28 | 22 | 4 | 96 | 139132413151331960943000168251595558389834505122155069440 |
| 28 | 23 | 2 | 96 | 2375220776875577898665653159674476845978019092919589273600 |
| 28 | 24 | 0 | 96 | 7138364557049020384858641709957588253238014205153509376000 |
| 28 | 14 | 22 | 100 | 928028646342473195520000 |
| 28 | 15 | 20 | 100 | 546032566906338036306862080000 |
| 28 | 16 | 18 | 100 | 65193027390179113618099330744320000 |
| 28 | 17 | 16 | 100 | 2970381338654524036193016653430915072000 |
| 28 | 18 | 14 | 100 | 64019701172927878858074202577576172453888000 |
| 28 | 19 | 12 | 100 | 701275455229545656248063798125373160761904332800 |
| 28 | 20 | 10 | 100 | 3251137998289053045684293536904755898665157001216000 |
| 28 | 21 | 8 | 100 | 3822248079847193889242714929507668700476116244312883200 |
| 28 | 22 | 6 | 100 | 833565508797368148331123383520696364192255380358273433600 |
| 28 | 23 | 4 | 100 | 35644178538162410007958007247683771104810101862095755673600 |
| 28 | 24 | 2 | 100 | 317614871531945354429417100192616812319934036432910286848000 |
| 28 | 25 | 0 | 100 | 495412380903807411342100943985738888906378524233071329280000 |
| 28 | 14 | 24 | 104 | 25778573509513144320000 |
| 28 | 15 | 22 | 104 | 19999154814405681433559040000 |
| 28 | 16 | 20 | 104 | 3537731099353059088893010870272000 |
| 28 | 17 | 18 | 104 | 249702274260005811066731006838964224000 |
| 28 | 18 | 16 | 104 | 8803742473892190247402693908016665722880000 |
| 28 | 19 | 14 | 104 | 173381198440389284573739221455676707163445657600 |
| 28 | 20 | 12 | 104 | 1723836798493154582477271097091808499646705801625600 |
| 28 | 21 | 10 | 104 | 5399622112004844737968294032584127427185056754224332800 |
| 28 | 22 | 8 | 104 | 3157504322648628688778381454924842149869676757003827937280 |
| 28 | 23 | 6 | 104 | 330995893857949110178035015026853635293694359941179611545600 |
| 28 | 24 | 4 | 104 | 7094503792694931302276821841362420238999403775709606313984000 |
| 28 | 25 | 2 | 104 | 31995610136576758473983522304748445278609173493281057669120000 |
| 28 | 26 | 0 | 104 | 23693330825917398967128593763834480254938256294620031877120000 |
| 28 | 14 | 26 | 108 | 440659376230993920000 |
| 28 | 15 | 24 | 108 | 469131847393865873817600000 |
| 28 | 16 | 22 | 108 | 129889829601631484361975398400000 |
| 28 | 17 | 20 | 108 | 14623801733805593194237989927518208000 |
| 28 | 18 | 18 | 108 | 847850056822522120043938143512253431808000 |
| 28 | 19 | 16 | 108 | 29246074774874364989918985506031069309173760000 |
| 28 | 20 | 14 | 108 | 578754194539895991592684045620785855223803412480000 |
| 28 | 21 | 12 | 108 | 4522918709757500819105037887061398075570436250062028800 |
| 28 | 22 | 10 | 108 | 7407138471386897726922566261771151699947633345210351616000 |
| 28 | 23 | 8 | 108 | 1974902725317277948202937670637087079432671247610189499596800 |
| 28 | 24 | 6 | 108 | 98434125919399662364843541725046768100587842946869871247360000 |
| 28 | 25 | 4 | 108 | 1031339913641488805315624116603856221637445902063814668451840000 |
| 28 | 26 | 2 | 108 | 2165905569138774047147524622353656876840967621697257183641600000 |
| 28 | 27 | 0 | 108 | 587875881010722647324822354715642327123551449186257862656000000 |
| 28 | 14 | 28 | 112 | 3497296636753920000 |
| 28 | 15 | 26 | 112 | 5993783552623426560000000 |
| 28 | 16 | 24 | 112 | 2967681310377581322709696512000 |
| 28 | 17 | 22 | 112 | 571441057926262758929080246468608000 |
| 28 | 18 | 20 | 112 | 56202783282290348017686721179640922112000 |
| 28 | 19 | 18 | 112 | 3383861074516382808317547564955665190984089600 |
| 28 | 20 | 16 | 112 | 126682827041961147866646707039202370556518622822400 |
| 28 | 21 | 14 | 112 | 2241193069748606360163217981222995376289414697399091200 |
| 28 | 22 | 12 | 112 | 10337589604541848447465090230369284282329705769580185518080 |
| 28 | 23 | 10 | 112 | 7465716767699289407278955466007031971241578030057624122163200 |
| 28 | 24 | 8 | 112 | 886966100477764284466297743472916136708544290367882339024896000 |
| 28 | 25 | 6 | 112 | 20606278265991035339699114356160545841982591159677386909286400000 |
| 28 | 26 | 4 | 112 | 97603062566456867938284750404809380107505017013375656892825600000 |
| 28 | 27 | 2 | 112 | 73958921594592496596844595798315983164903599408598296297472000000 |
| 28 | 15 | 28 | 116 | 26733335491346964480000 |
| 28 | 16 | 26 | 116 | 35436446695481563915223040000 |
| 28 | 17 | 24 | 116 | 13720673719911850511347785793536000 |
| 28 | 18 | 22 | 116 | 2466194319735361576897414488111710208000 |
| 28 | 19 | 20 | 116 | 265655513293050202969725870459884056608768000 |
| 28 | 20 | 18 | 116 | 18383061682890785933539926932965417630102978560000 |
| 28 | 21 | 16 | 116 | 676873049705279781422402446935847963677662997852979200 |
| 28 | 22 | 14 | 116 | 8258978774642471195886513377303493869507310373128948940800 |
| 28 | 23 | 12 | 116 | 17252964145408008622404132182342713794425158705699097464012800 |
| 28 | 24 | 10 | 116 | 5174361179951799127723421411840908035351040544133846518464512000 |
| 28 | 25 | 8 | 116 | 269456495690755720917019053606454821540025831559506024244183040000 |
| 28 | 26 | 6 | 116 | 2715256408216515518588484643295792344509740147624192899232563200000 |
| 28 | 27 | 4 | 116 | 4522385752104120718683127769164412796624581021365183684018176000000 |
| 28 | 16 | 28 | 120 | 134598525151004630876160000 |
| 28 | 17 | 26 | 120 | 170443209812395955447645208576000 |
| 28 | 18 | 24 | 120 | 66348309674396499362754507248762880000 |
| 28 | 19 | 22 | 120 | 13694777806959593093621278530141250859827200 |
| 28 | 20 | 20 | 120 | 1766363427921403573919871897123197715814023168000 |
| 28 | 21 | 18 | 120 | 128490177725892160712505255457035430477052018216140800 |
| 28 | 22 | 16 | 120 | 3736494437765786999679329915385568408685543585176029757440 |
| 28 | 23 | 14 | 120 | 23227086602596908230887798553312595352575974509539017883648000 |
| 28 | 24 | 12 | 120 | 19062762967610704159412507312426573764848237060669807462973440000 |
| 28 | 25 | 10 | 120 | 2324603933776931505845254495095590956636458971646408658161500160000 |
| 28 | 26 | 8 | 120 | 49748137143285115176847757413418289482175417974768403551040307200000 |
| 28 | 27 | 6 | 120 | 170056298214846356742658948244500216885009834020796805085659136000000 |
| 28 | 17 | 28 | 124 | 675624102538874256152985600000 |
| 28 | 18 | 26 | 124 | 932273256667038032153000514945024000 |
| 28 | 19 | 24 | 124 | 432593128852557824424438677159207239680000 |
| 28 | 20 | 22 | 124 | 109639664643925133486985769979522715509745254400 |
| 28 | 21 | 20 | 124 | 15527454971598589814715284152691354721255938221670400 |
| 28 | 22 | 18 | 124 | 985941120310467686087103469219897930858194430226910412800 |
| 28 | 23 | 16 | 124 | 17328925230681429453167384797890648659684036126376201918873600 |
| 28 | 24 | 14 | 124 | 42563070895119185748389845919059420574033873156711803628027904000 |
| 28 | 25 | 12 | 124 | 13050007726577178508429535733547320685918090655661907581893345280000 |
| 28 | 26 | 10 | 124 | 611079879867617897975308739162275380442977371671963069079302963200000 |
| 28 | 27 | 8 | 124 | 4235239497349453744179977398787178673496309353963633895452704768000000 |
| 28 | 18 | 28 | 128 | 4419564532553295398495571148800000 |
| 28 | 19 | 26 | 128 | 7226222628806274347445333397453406208000 |
| 28 | 20 | 24 | 128 | 4133315386344655351038472200126038502958694400 |
| 28 | 21 | 22 | 128 | 1178191528265529556993246861482393607950487781376000 |
| 28 | 22 | 20 | 128 | 156155037359174601450054348156226786131726879201341472768 |
| 28 | 23 | 18 | 128 | 6982926745241214383633559867555635033359321429271999466700800 |
| 28 | 24 | 16 | 128 | 54445707824498716484055671116728690877692677548470126954676224000 |
| 28 | 25 | 14 | 128 | 46264433085381033942678043613153278712737428368173443294607441920000 |
| 28 | 26 | 12 | 128 | 5011216001995575785272802527795425997810557330748722202321291837440000 |
| 28 | 27 | 10 | 128 | 71695083246386910474006760063669676850043231022246845017791397888000000 |
| 28 | 19 | 28 | 132 | 43028455749341203308871495817625600000 |
| 28 | 20 | 26 | 132 | 82470867481219745707725283366510924922880000 |
| 28 | 21 | 24 | 132 | 53227341724459048914932238086359576828349880729600 |
| 28 | 22 | 22 | 132 | 14867865674066406177275393344493465989909698672265789440 |
| 28 | 23 | 20 | 132 | 1554131510250597665740262666149800222472435956761819401420800 |
| 28 | 24 | 18 | 132 | 37356201813360653080330808099205507309327757562507660271550464000 |
| 28 | 25 | 16 | 132 | 98846088694548941173909276547828941521085379701089140079926968320000 |
| 28 | 26 | 14 | 132 | 26900446002127530039625398342963381315211261913743188302494905139200000 |
| 28 | 27 | 12 | 132 | 827817435773474640216591735094226761705861726095172165593232048128000000 |
| 28 | 20 | 28 | 136 | 601586697499073637855105467874174566400000 |
| 28 | 21 | 26 | 136 | 1257326457560678279379835606244135521505771520000 |
| 28 | 22 | 24 | 136 | 816188551112144974595113428287041421595993290519347200 |
| 28 | 23 | 22 | 136 | 194735997487274030922601013520214001362058872413134782464000 |
| 28 | 24 | 20 | 136 | 13066347461844135861175941727265264423303022877821129480732672000 |
| 28 | 25 | 18 | 136 | 119100683676648748557025552118959544258266495358586580937987850240000 |
| 28 | 26 | 16 | 136 | 91296479504789253446684703609278347029728406209137844149263374745600000 |
| 28 | 27 | 14 | 136 | 6446283667008355813673560921873648027765726746241110326405725421568000000 |
| 28 | 21 | 28 | 140 | 10857333692054586203431465550156181327052800000 |
| 28 | 22 | 26 | 140 | 22867077529575793225094138016469751235934892851200000 |
| 28 | 23 | 24 | 140 | 13394578841596199067683955532492988810329475824880713728000 |
| 28 | 24 | 22 | 140 | 2337796920760328097772686584893216983979315385209949352099840000 |
| 28 | 25 | 20 | 140 | 74173412099180123334046917004352845728643365605112159852319211520000 |
| 28 | 26 | 18 | 140 | 185780208706076983229821472718060615780603429750593088463375958016000000 |
| 28 | 27 | 16 | 140 | 33037644315407846042733842442219305998057661232562371781547092082688000000 |
| 28 | 22 | 28 | 144 | 229731796479230251932564386667743902622023680000000 |
| 28 | 23 | 26 | 144 | 452318642876676745545278232918832557014286734878310400000 |
| 28 | 24 | 24 | 144 | 212723599086001270956705163668625852464666389064662447554560000 |
| 28 | 25 | 22 | 144 | 21778239457753719109117747810698873276750658405994599397562777600000 |
| 28 | 26 | 20 | 144 | 209594452517203028906067336832642916028201819854400900462238425415680000 |
| 28 | 27 | 18 | 144 | 107141127720945380901266163985477882826885787681908922033694618681344000000 |
| 28 | 23 | 28 | 148 | 5268399525917860431652829388424498634146027929600000000 |
| 28 | 24 | 26 | 148 | 8943003832606956284518096284487879283977905450183032832000000 |
| 28 | 25 | 24 | 148 | 2889130796016753339089099232437390688686205583484167222670131200000 |
| 28 | 26 | 22 | 148 | 116822948764490174384063261966247670980246497480100859631844615782400000 |
| 28 | 27 | 20 | 148 | 207121899148450045979546291972080877726367678114089520058216029880320000000 |
| 28 | 24 | 28 | 152 | 121454899787406134930981689142036585201430425921126400000000 |
| 28 | 25 | 26 | 152 | 160334105495627557360648205179490318524354095905863976878080000000 |
| 28 | 26 | 24 | 152 | 27338641915892389117824876259538191766548228826328432056236769280000000 |
| 28 | 27 | 22 | 152 | 217663571499881463911149105875092736134206522066691838870082730065920000000 |
| 28 | 25 | 28 | 156 | 2572882014277453394318261187036968506973715050665082880000000000 |
| 28 | 26 | 26 | 156 | 2252676655753696546021436046421216535466946366030912383300403200000000 |
| 28 | 27 | 24 | 156 | 106683890470361608538499684762729260421979848051226926937741983744000000000 |
| 28 | 26 | 28 | 160 | 43651032541165082389043474886966742767175841083690309386240000000000 |
| 28 | 27 | 26 | 160 | 18090273205631816714868716429620096780334663206290722422731571200000000000 |
| 28 | 27 | 28 | 164 | 437807012195112962964313822329879895157942105222394371112960000000000000 |

Checks against requested landmarks:

- `N_4(8)=972` exactly.
- At `r=4`, energy `12` splits as `18144 + 216`, hence aggregate
  `N_4(12)=18360`.
- The minimal `r=6` band is `87480`, consistent with the old Monte Carlo
  estimate `A_6≈85668` within its sampling error, but now exact for this
  convention.
## Exact `k=4` tables

Full CSV: `spectrum_k4_exact.csv`.

### `k=4, r=2`

| j | h | E | count |
|---:|---:|---:|---:|
| 0 | 2 | 4 | 100 |
| 0 | 3 | 6 | 100 |
| 0 | 4 | 8 | 25 |
| 1 | 0 | 4 | 1548 |
| 1 | 1 | 6 | 5328 |
| 1 | 2 | 8 | 11640 |
| 1 | 3 | 10 | 11760 |
| 1 | 4 | 12 | 7820 |
| 1 | 5 | 14 | 1472 |
| 1 | 6 | 16 | 176 |

### `k=4, r=3`

| j | h | E | count |
|---:|---:|---:|---:|
| 0 | 3 | 6 | 1000 |
| 0 | 4 | 8 | 1500 |
| 0 | 5 | 10 | 750 |
| 0 | 6 | 12 | 125 |
| 1 | 1 | 6 | 46440 |
| 1 | 2 | 8 | 183060 |
| 1 | 3 | 10 | 429120 |
| 1 | 4 | 12 | 527400 |
| 1 | 5 | 14 | 411000 |
| 1 | 6 | 16 | 161460 |
| 1 | 7 | 18 | 27360 |
| 1 | 8 | 20 | 2640 |
| 2 | 0 | 8 | 763136 |
| 2 | 1 | 10 | 4993280 |
| 2 | 2 | 12 | 21582464 |
| 2 | 3 | 14 | 56381056 |
| 2 | 4 | 16 | 107951616 |
| 2 | 5 | 18 | 126906496 |
| 2 | 6 | 20 | 105243264 |
| 2 | 7 | 22 | 41506048 |
| 2 | 8 | 24 | 10798848 |

## Numerical / extrapolated diagonal analysis

The consolidated command

```bash
python3 cl_probe/cl_stress_audit.py --k 2 \
  --csv cl_probe/spectrum_k2_character.csv
```

reruns the headline finite/extrapolated checks and exits nonzero if any tested
margin is positive.  On the current exact `r<=28` table it reports:

| check | least favorable value |
|---|---:|
| fixed-excess diagonal `G/a_d` | -1.56202 |
| empirical proportional margin | -0.0659215 |
| moving tail-window margin | -0.0659215 |
| ray-sensitivity fitted margin | -0.206298 |
| backtest predicted held-out margin | -0.283039 |

The audit status is `PASS`.  This is a reproducibility gate for the finite
evidence, not a proof of (CL).

The script `analyze_cl.py` aggregates the exact `k=2` table by energy and fits
fixed-excess bands

```text
log N_r(2r+t) = a_t r log r + b_t r + c_t.
```

The exact `r<=28` data give the following fixed-excess fits with at least three
points:

| t | fitted `a_t` | fitted `b_t` | points |
|---:|---:|---:|---|
| 0 | 0.497626 | 0.954644 | `(2,18),...,(28,80006929312452558178840197120000)` |
| 2 | 0.334147 | 1.67745 | `(3,432),...,(27,462262258249725891699965583360000)` |
| 4 | -0.0531488 | 3.25383 | `(2,2),...,(28,757310034236425936806155154739200000)` |
| 6 | -0.156363 | 3.74207 | `(3,160),...,(27,1373357200105804156972139231428608000)` |
| 8 | -0.209518 | 4.05669 | `(4,14748),...,(28,1315136307057249804833837144090068992000)` |
| 10 | -0.314929 | 4.54834 | `(5,1646720),...,(27,1348335285178790324587247408802742272000)` |
| 12 | -0.830575 | 6.64966 | `(4,1008),...,(28,1001456477934900478205636678543327084544000)` |
| 14 | -0.911641 | 7.04576 | `(5,370944),...,(27,691630618500647239984457534132850524160000)` |
| 16 | -0.896806 | 7.10832 | `(6,107373600),...,(28,446441706053971187128588402822924492879872000)` |
| 18 | -1.0178 | 7.65947 | `(7,29976726528),...,(27,226366358773062163519874112895672078226227200)` |
| 20 | -1.67962 | 10.3774 | `(6,5702400),...,(28,134994162747943661911876138035674490283015372800)` |
| 22 | -1.77787 | 10.8409 | `(7,5218836480),...,(27,52901652495528984310884924978701816803462348800)` |
| 24 | -1.7025 | 10.6811 | `(8,3231264234240),...,(28,30271088860931848687156369524200732561770540646400)` |
| 26 | -1.86816 | 11.4155 | `(9,1732600508424192),...,(27,9480702153772865108763620760102605742168952012800)` |
| 28 | -2.68302 | 14.7972 | `(8,145297152000),...,(28,5339531045115508303401308516850962333583078000230400)` |
| 30 | -2.81358 | 15.3974 | `(9,254288281927680),...,(27,1366237671095259871878285617030457135021080819269632)` |
| 32 | -2.66882 | 14.9801 | `(10,277944386011729920),...,(28,771051396453127117917672273297885693672147774045831168)` |
| 34 | -2.89129 | 15.9581 | `(11,247214107686002688000),...,(27,163227163432658871995306346467159510881794016961691648)` |
| 36 | -3.87161 | 20.0701 | `(10,11058645491712000),...,(28,93521615254615912240611524488907247368441760231976304640)` |
| 38 | -4.03085 | 20.8028 | `(11,31986517715582976000),...,(27,16434323322337482296906666195474652075113227812248616960)` |
| 40 | -3.79905 | 20.0537 | `(12,55008296603224112332800),...,(28,9654367329261993559457121073715166292811941578298591395840)` |
| 42 | -4.07209 | 21.2621 | `(13,73934362208682213153177600),...,(27,1398931629187809350742698279391736680787598847126155427840)` |
| 44 | -5.25702 | 26.2772 | `(12,1988616672221921280000),...,(28,849508821982631728888650628325138082851340862558313034547200)` |
| 46 | -5.42714 | 27.0779 | `(13,8664711525338893516800000),...,(27,99757382929443602532033892065625561658214519475200794296320)` |
| 48 | -5.08151 | 25.8813 | `(14,21714628410873863952334848000),...,(28,63117603554715808675596076426187203022178501668826965032058880)` |
| 50 | -5.39066 | 27.2689 | `(15,41349981931999575381149692723200),...,(27,5841060678930497365830940278574382198746226267000161780039680)` |
| 52 | -6.86871 | 33.5651 | `(14,725924630027890144051200000),...,(28,3885537804097671320197707850286850759184060854150990609656217600)` |
| 54 | -7.03582 | 34.3791 | `(15,4469069532100466957510246400000),...,(27,272991196113109422520656418398011504714131996200381714436587520)` |
| 56 | -6.53124 | 32.5413 | `(16,15452997857230434515797553971200000),...,(28,193062704584116787746510050322497256404564442533652188710323732480)` |
| 58 | -6.88036 | 34.127 | `(17,39768498062455609240637462714253312000),...,(27,9858209170765449225947969215364641520859502411597179181392199680)` |
| 60 | -8.80525 | 42.3633 | `(16,483696391422230753983856640000000),...,(28,7512290278415144831400481108148906017361336804735330594556931276800)` |
| 62 | -8.98416 | 43.2501 | `(17,4014826358596173785496356388864000000),...,(27,266513645235688850772091272120825458823597925157081169910887874560)` |
| 64 | -8.23778 | 40.4196 | `(18,18386051413928626461509888721813504000000),...,(28,222148125285699239656129493562730678644453643653048406095125776957440)` |
| 66 | -8.67375 | 42.4005 | `(19,61683227560481250448024314001845915746304000),...,(27,5245953619526842863654598944320934594496001906709402357153493155840)` |
| 68 | -11.2863 | 53.6211 | `(18,543849892967691838403507965132800000000),...,(28,4859411965344455127178768596078220136380908661805653853111281070899200)` |
| 70 | -11.5312 | 54.808 | `(19,5872320479521853935273802648285872128000000),...,(27,73331720297980863891672771367543951550279306487137484915977572319232)` |
| 72 | -10.3929 | 50.3485 | `(20,34503400291559838855739695876437805367296000000),...,(28,76752618134158774693395493910572524905858163441042076755567467946835968)` |
| 74 | -11.0124 | 53.1402 | `(21,146675512688976934333274586660728883402453811200000),...,(27,709964460476094294983579775887561560500351905199263816159804730114048)` |
| 76 | -14.7133 | 69.0934 | `(20,971327718152259207554299130471566540800000000),...,(28,854816765222052678936213622200887880668234954719327383224762735882403840)` |
| 78 | -15.136 | 71.0604 | `(21,13264684518747469611529165432182291195494400000000),...,(27,4624288685220893774157185184924488474384845939058505218607022080000000)` |
| 80 | -13.3237 | 63.7718 | `(22,97490823040335825558694659882341376556982599680000000),...,(28,6537699260263363914526615594681113784589389938010494465028858370536243200)` |
| 82 | -14.3106 | 68.1765 | `(23,513225344430131390718268250334104636492523553947648000000),...,(27,19519957769613555048687161283745542798402719506755262250305487634432000)` |
| 84 | -19.85 | 92.1438 | `(22,2626750567972775462493701394283217282924544000000000),...,(28,33223498699863832521449034744213034720812423124094630998248210812633088000)` |
| 86 | -20.7198 | 96.0602 | `(23,44347004424588159067558257538609472190164238336000000000),...,(27,50718049639239519725209942796890282939310402048121833149724570419200000)` |
| 88 | -17.6393 | 83.3985 | `(24,399345808807514261845815018586160418505667065952600064000000),...,(28,107350743951914765735296214319488266380986057588105620076010274019082240000)` |
| 92 | -28.4039 | 130.303 | `(24,10344929660446727225718574206144479198767905295564800000000),...,(28,207238724986354275179784700805348736362675930565483680941611308128665600000)` |

For `lambda=1`, `rho in {0.5,1,2}`, and `N in {50,200,1000,4000}`, the fitted
maximizing band is always `t=0`, i.e. `E*=2r`, and `G/a_d` is negative and
decreasing over this tested range.

Representative output:

| rho | N | r | t* | E* | G/a_d |
|---:|---:|---:|---:|---:|---:|
| 0.5 | 50 | 176 | 0 | 352 | -1.56202 |
| 0.5 | 200 | 1414 | 0 | 2828 | -2.27549 |
| 0.5 | 1000 | 15811 | 0 | 31622 | -3.16597 |
| 0.5 | 4000 | 126491 | 0 | 252982 | -3.97518 |
| 1 | 50 | 353 | 0 | 706 | -3.84409 |
| 1 | 200 | 2828 | 0 | 5656 | -5.37999 |
| 1 | 1000 | 31622 | 0 | 63244 | -7.25367 |
| 1 | 4000 | 252982 | 0 | 505964 | -8.92113 |
| 2 | 50 | 707 | 0 | 1414 | -9.3631 |
| 2 | 200 | 5656 | 0 | 11312 | -12.5831 |
| 2 | 1000 | 63245 | 0 | 126490 | -16.4492 |
| 2 | 4000 | 505964 | 0 | 1011928 | -19.8435 |

## Proportional-energy finite profile

The fixed-excess fit above does not directly test bands with `E/r` bounded away
from `2`.  The script `profile_cl.py` therefore computes, for each exact band,
the empirical entropy density

```text
beta_emp(r,E) = log N_r(E) / (r log r)
```

and the leading diagonal margin for `k=2`,

```text
beta_emp(r,E) - E/(3r) - 2/3.
```

Negative margin is supportive finite evidence for (CL) at that band.  This is
still not a proof: small `r` has large lower-order contamination, and the table
does not identify the asymptotic proportional-band entropy.

The exact `r<=28` proportional profile is:

| r | entropy peak `E/r` | peak count | least favorable `E/r` | leading margin |
|---:|---:|---:|---:|---:|
| 2 | 2 | 18 | 2 | 0.751629 |
| 3 | 2.66667 | 432 | 2.66667 | 0.285684 |
| 4 | 3 | 18360 | 3 | 0.103868 |
| 5 | 4 | 1646720 | 3.2 | 0.00162021 |
| 6 | 4 | 219520120 | 3.33333 | -0.0659215 |
| 7 | 4 | 34248127872 | 3.42857 | -0.114815 |
| 8 | 4.5 | 8575270542720 | 3 | -0.152316 |
| 9 | 4.44444 | 2571756192847872 | 3.11111 | -0.178208 |
| 10 | 4.8 | 877774007805543936 | 3.2 | -0.200955 |
| 11 | 4.72727 | 437561022497611161600 | 3.27273 | -0.220958 |
| 12 | 4.66667 | 219289286298578105060352 | 3.33333 | -0.238643 |
| 13 | 4.92308 | 149179088764661423095480320 | 3.38462 | -0.254384 |
| 14 | 4.85714 | 109381197757373604008281939968 | 3.42857 | -0.26849 |
| 15 | 5.06667 | 92529459894620769233179445821440 | 3.46667 | -0.281215 |
| 16 | 5 | 93956633574891101256924290182348800 | 3.5 | -0.292763 |
| 17 | 5.17647 | 96886526385930881599865205658799308800 | 3.52941 | -0.303302 |
| 18 | 5.11111 | 130742628694030610634834730683963644313600 | 3.55556 | -0.312971 |
| 19 | 5.05263 | 167862449496184779362548667108792709635112960 | 3.36842 | -0.321651 |
| 20 | 5.2 | 280420525547205514660421812671527660552611430400 | 3.4 | -0.329541 |
| 21 | 5.14286 | 457371041390808178678077048941312346568670576640000 | 3.42857 | -0.33694 |
| 22 | 5.27273 | 889903247795183572022508828546308448041587968049152000 | 3.45455 | -0.34389 |
| 23 | 5.21739 | 1801669781886039818497152353886703395356154981701910528000 | 3.47826 | -0.350432 |
| 24 | 5.33333 | 4038465748414733182431012583065349277504801563089303502848000 | 3.5 | -0.356602 |
| 25 | 5.28 | 9956912894601725261753476680748024177918811469953888409354240000 | 3.52 | -0.362432 |
| 26 | 5.38462 | 25464712001213642381425416567940649428146953000746194221137920000000 | 3.53846 | -0.367951 |
| 27 | 5.33333 | 75241614974351191596494010828427654813134553903939356908283053998080000 | 3.55556 | -0.373184 |
| 28 | 5.42857 | 217690910302131583250794275518135410487152530856457464638428864839680000000 | 3.57143 | -0.378156 |

Thus the entropy peak is not at the minimal band: by `r=8,9` it sits near
`E/r \approx 4.4`, and by `r=10..28` it sits in the range `4.67..5.43`.
But after applying the leading diagonal penalty, the
least-favorable observed tail-window band (`r>=6`) is `r=6,E=20`, with margin
`-0.06592151`.  No proportional-band breach is observed in this exact finite
data, but this remains evidence rather than an asymptotic bound.

## Tail-window trend diagnostic

The script `profile_trends.py` summarizes the same proportional-energy data by
moving tail windows.  This is meant to separate the small-`r` contamination from
the behavior near the current exact frontier.  It is still a finite-data
diagnostic, not a proof of the diagonal entropy bound.

For each tail window, the table records the band with largest leading diagonal
margin:

| tail start | r | E/r | beta_emp | leading margin |
|---:|---:|---:|---:|---:|
| 6 | 6 | 3.33333 | 1.71186 | -0.0659215 |
| 10 | 10 | 3.2 | 1.53238 | -0.200955 |
| 14 | 14 | 3.42857 | 1.54103 | -0.26849 |
| 18 | 18 | 3.55556 | 1.53888 | -0.312971 |
| 22 | 22 | 3.45455 | 1.47429 | -0.34389 |
| 24 | 24 | 3.5 | 1.47673 | -0.356602 |
| 26 | 26 | 3.53846 | 1.4782 | -0.367951 |

Near the frontier, the least-favorable per-`r` bands drift downward in margin:

| r | E/r | beta_emp | leading margin |
|---:|---:|---:|---:|
| 21 | 3.42857 | 1.47258 | -0.33694 |
| 22 | 3.45455 | 1.47429 | -0.34389 |
| 23 | 3.47826 | 1.47565 | -0.350432 |
| 24 | 3.5 | 1.47673 | -0.356602 |
| 25 | 3.52 | 1.47757 | -0.362432 |
| 26 | 3.53846 | 1.4782 | -0.367951 |
| 27 | 3.55556 | 1.47867 | -0.373184 |
| 28 | 3.57143 | 1.47899 | -0.378156 |

A simple recent-window fit of margin against `1/log r` gives intercept
approximately `-0.814`; this number is only a heuristic summary of the finite
data.  The useful point is more modest: after removing the very small `r`
rows, the exact windows through `r=28` show no drift toward a positive leading
margin.

## Proportional-ray extrapolation

The script `proportional_ray_fit.py` gives a more diagonal-facing numerical
stress test.  For target values of `alpha`, it follows approximate rays
`E/r \approx alpha`, fits

```text
beta_emp(r,E) = log N_r(E)/(r log r)
```

against `1/log r`, and estimates the leading CL margin

```text
beta(alpha) - alpha/3 - 2/3
```

for `k=2`.  This is a finite-data extrapolation, not an asymptotic theorem.

With `r>=10`, alpha step `0.25`, and matching window `0.13`, the least
favorable fitted ray is near `alpha=5.5`:

| target alpha | mean alpha | beta intercept | fitted margin | latest alpha | latest margin | max empirical margin |
|---:|---:|---:|---:|---:|---:|---:|
| 5.5 | 5.49415 | 2.27459 | -0.223461 | 5.42857 | -0.641613 | -0.641613 |

Selected fitted rays:

| target alpha | mean alpha | beta intercept | fitted margin |
|---:|---:|---:|---:|
| 3.0 | 2.97963 | 0.8576 | -0.802276 |
| 3.5 | 3.49104 | 1.048 | -0.782347 |
| 4.0 | 4 | 1.30797 | -0.692035 |
| 4.5 | 4.48879 | 1.56173 | -0.601203 |
| 5.0 | 4.98755 | 1.87957 | -0.449617 |
| 5.25 | 5.24639 | 2.03703 | -0.378438 |
| 5.5 | 5.49415 | 2.27459 | -0.223461 |
| 5.75 | 5.72818 | 2.2823 | -0.293762 |

Small sensitivity checks stayed negative.  Raising the cutoff to `r>=12` or
`r>=14` moves the least favorable target to `alpha=5.75`, with fitted margins
about `-0.294` and `-0.285`; using alpha step `0.2` and window `0.11` gives a
least favorable target near `alpha=5.6`, with fitted margin about `-0.220`.
Thus the ray fit is the strongest numerical stress test here, but it still
shows no fitted positive-margin proportional band in the exact `r<=28` data.

The script `proportional_ray_sensitivity.py` repeats this stress test over
`min_r in {10,12,14,16}`, alpha steps `{0.2,0.25}`, and matching windows
`{0.11,0.13,0.17,0.2}`.  The least favorable configuration in that grid is:

| min r | alpha step | window | target alpha | mean alpha | fitted margin | latest alpha | latest margin |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 10 | 0.2 | 0.13 | 5.6 | 5.6021 | -0.206298 | 5.57143 | -0.696876 |

Thus even after this small robustness sweep, the most adverse fitted
proportional-ray margin remains negative in the exact `r<=28` data.

The script `proportional_ray_backtest.py` gives a finite-data check on the same
fit model.  It trains each approximate ray only up to a cutoff
`r <= 18,20,22,24`, then compares the predictions with the later exact rows.
The most optimistic held-out prediction is still negative:

| diagnostic | target alpha | train max | mean alpha | value | latest predicted margin | latest actual margin |
|---|---:|---:|---:|---:|---:|---:|
| largest predicted margin | 3.25 | 18 | 3.24121 | -0.283039 | -0.37025 | -0.380604 |
| largest overprediction | 3.75 | 18 | 3.73532 | 0.0575805 | -0.325147 | -0.379601 |

So the simple ray model does sometimes overpredict later margins, but in this
backtest the overprediction is modest and does not create a held-out positive
margin.  This is again evidence only; it does not replace an asymptotic bound.

## Verdict

At the reachable exact scale, **(CL) is inconclusive**.

The fixed-excess extrapolation from the exact `k=2` data is compatible with
(CL): it chooses the minimal band and gives negative `G/a_d`.  The additional
proportional-energy profile is also supportive at the available tail window:
although the raw entropy peak moves up to `E/r \approx 5.43`, the leading
diagonal margin is negative for every observed band with `r>=6` through `r=28`.
After the high-energy cutoff, the stress audit also reports the central window
`E/r <= 4` separately for `k=2`; its worst observed margin is again the
`r=6,E=20` band, with margin `-0.06592151`.
The new tail-window trend diagnostic makes the same finite-data point more
sharply: later windows have increasingly negative maximum margins.
The proportional-ray fit is the closest numerical test to the diagonal
higher-energy failure mode; its least favorable fitted margin is still
negative, around `-0.21` in the sensitivity grid.
The ray backtest gives no sign that the finite extrapolation is hiding a
positive held-out margin.
However this is not a diagonal proof.  The hardest
part of (CL') is now paper-level closed for `k=2` by the cycle-count envelope.
For `k >= 4`, the central proportional entropy problem remains open.

So the honest conclusion is:

- proved/exact: faithful compiled exact enumerator, validation through `k=2,
  r=5`, compiled brute-force extension to `k=2,r=6` and `k=4,r=3`, and
  compiled exact character/component extension to `k=2,r=7..28`;
- numerical: fixed-excess small-r extrapolation and finite proportional-band
  leading-margin profiles are CL-supportive, including the tail-window trend
  diagnostic, proportional-ray fits, ray-fit backtests, and the consolidated
  stress audit;
- proved analytic reduction: the trivial `(kr)!` count excludes proportional
  bands with `E/r >= 2k + eta` for any fixed `eta > 0`;
- proved analytic envelope: the three-cycle-count unsigned-Stirling bound
  closes the `k=2` proportional-band entropy target and, after scale stitching,
  proves (CL) for `k=2` at paper level;
- conjectural: for `k >= 4`, the central proportional window remains open;
- final verdict: **no breach for `k=2`; CL is paper-level proved in the
  `k=2` case, but the general even-`k` problem remains inconclusive**.

## Remaining work

The next mathematical target is no longer exact fixed-`r` enumeration for `k=2,r<=28`;
that has been supplied.  The unresolved part is analytic or asymptotic:
for `k >= 4`, control, or find a breach from, proportional bands in the
remaining central window on the diagonal.  The character/component extractor
gives exact finite data, but it is not itself a topological-recursion bound.

The next computational frontier is beyond `k=2,r=28`.  After the content-polynomial
and common-denominator optimizations, the Python route rebuilds `r=20` in about
213 seconds on this machine.  The compiled GMP-backed structural extractor
matches the same `r<=20` CSV in about 17 seconds, generated the exact
`r<=24` CSV in about 141 seconds, generated the exact
`r<=26` CSV in about 395 seconds, and generated the exact
`r<=28` CSV in about 1111 seconds.  Further progress likely
needs either a dedicated recurrence for the aggregated cycle-count transform
or a more specialized implementation before another exact frontier push.

Task B now has a complete paper-level `k=2` CL proof through the
three-cycle-count envelope.  It does not close general even `k`.
Task C was not attempted in this round.
