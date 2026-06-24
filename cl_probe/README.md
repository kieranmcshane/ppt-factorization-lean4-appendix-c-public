# CL spectrum probe

This directory contains exact and exploratory code for the combinatorial lemma
(CL) diagonal spectrum task.

## Build the compiled exact enumerator

```bash
mkdir -p cl_probe/bin
g++ -O3 -std=c++17 cl_probe/cl_spectrum.cpp -o cl_probe/bin/cl_spectrum
g++ -O3 -std=c++17 cl_probe/two_block_open_exact.cpp \
  -o cl_probe/bin/two_block_open_exact
```

## Run exact spectra

Faithful exact brute-force grading:

```bash
./cl_probe/bin/cl_spectrum --k 2 --r-min 2 --r-max 5
./cl_probe/bin/cl_spectrum --k 2 --r-min 6 --r-max 6
./cl_probe/bin/cl_spectrum --k 4 --r-min 2 --r-max 3
```

CSV output:

```bash
./cl_probe/bin/cl_spectrum --k 2 --r-min 2 --r-max 5 --csv
```

For the bidefect/cycle-count profile used in the analytic frontier, use:

```bash
./cl_probe/bin/cl_spectrum --k 4 --r-min 2 --r-max 2 --defect-csv
```

This emits `plus_defect`, `minus_defect`, and the three cycle counts
`#pi`, `#(gamma*pi)`, and `#(pi*gamma^{-1})`.  Aggregating this output by
`(j,h,E)` recovers the ordinary spectrum.
The checked `k=4,r=1,2,3` bidefect table is stored in
`spectrum_k4_defect_exact.csv`.

To summarize a defect CSV:

```bash
python3 cl_probe/defect_profile.py cl_probe/spectrum_k4_defect_exact.csv --top 5
```

The exact brute-force method enumerates all permutations in `S_{kr}`.  It is
fast for `kr <= 10` and took about four minutes for `kr = 12` on this machine.
It is not a viable route to `k=2, r=7,8`; those require a structural generator
or a topological-recursion count.

## Analytic frontier

The file `CL_analytic_frontier.md` isolates the actual asymptotic theorem
needed to close CL from the finite data.  It states the proportional-band
entropy target as a `limsup` upper bound; a `liminf` would only enter a
matching lower-bound or sharpness statement.  It also records the proved
trivial-count high-energy cutoff: for fixed `eta > 0`, bands with
`E/r >= 2k + eta` cannot breach (CL'), so the remaining Task B frontier is the
central proportional window `E/r <= 2k + o(1)`.

The same note now gives a sharper three-cycle-count envelope.  For `k=2`, it
proves the proportional-band `limsup` entropy target and stitches the remainder
to the rising-factorial penalty, giving a paper-level proof of (CL) for `k=2`:

```bash
python3 cl_probe/cycle_count_envelope.py --k 2 --alpha-min 0 --alpha-max 6
```

For `k >= 4`, this envelope closes only part of the central window.

To print the remaining window for several even values of `k`, run:

```bash
python3 cl_probe/cycle_count_envelope.py --table-k-max 12
```

To benchmark a one-sided genus-count bound of the form
`count(g) <= exp(O(r)) r^(eta*g)`, run:

```bash
python3 cl_probe/genus_frontier.py --k 4 --eta 3
python3 cl_probe/genus_frontier.py --table-k-max 12 --eta 2
python3 cl_probe/one_sided_cycle_frontier.py --table-k-max 12 --eta 2
python3 cl_probe/one_sided_balance_frontier.py --table-k-max 12
python3 cl_probe/one_sided_integer_open_ranges.py --table-k-max 12 --t-max 20
python3 cl_probe/finite_type_frontier.py --k 6 --t-max 12
python3 cl_probe/eta_requirement_table.py --table-k-max 20
python3 cl_probe/bidefect_local_threshold.py --table-k-max 20
python3 cl_probe/bidefect_min_genus_threshold.py --table-k-max 20
python3 cl_probe/bidefect_remaining_lattice.py --k 6 --t-max 20
python3 cl_probe/k6_remaining_arithmetic.py --t-max 40
python3 cl_probe/k6_strip_entropy_threshold.py --t-max 40
python3 cl_probe/k6_strip_population_sampler.py --t 7 --samples 500000 --seed 20260618
python3 cl_probe/bidefect_target_local_search.py --k 6 --t 8 --g 10 --seed 424242
python3 cl_probe/k6_balanced_strip_target_sweep.py --t-min 13 --t-max 40
python3 cl_probe/k6_balanced_strip_certificates.py \
  --verify cl_probe/k6_balanced_strip_witnesses_t13_t40.csv
python3 cl_probe/k6_balanced_strip_neutral_moves.py \
  cl_probe/k6_balanced_strip_witnesses_t13_t40.csv
python3 cl_probe/k6_balanced_strip_shape_profile.py \
  cl_probe/k6_balanced_strip_witnesses_t13_t40.csv
python3 cl_probe/k6_balanced_split_window.py --t-min 13 --t-max 40 \
  --certificates cl_probe/k6_balanced_strip_witnesses_t13_t40.csv
python3 cl_probe/k6_balanced_split_target_search.py --t-min 13 --t-max 40
python3 cl_probe/k6_balanced_split_target_search.py --t-min 13 --t-max 40 \
  --seed 20260617 --restarts 4 --steps 15000 --emit-permutation \
  > cl_probe/k6_balanced_split_target_search_best_t13_t40.csv
python3 cl_probe/k6_balanced_split_asymptotics.py
python3 cl_probe/k6_balanced_split_invariant_sanity.py --t-min 13 --t-max 80 \
  --target-search-csv cl_probe/k6_balanced_split_target_search_t13_t40.csv
python3 cl_probe/k6_strict_split_near_hit_local_profile.py \
  cl_probe/k6_balanced_split_target_search_best_t13_t40.csv
python3 cl_probe/k6_strict_split_zero_neighbor_extract.py \
  cl_probe/k6_balanced_split_target_search_best_t13_t40.csv \
  cl_probe/k6_strict_split_near_hit_local_profile_t13_t40.csv
python3 cl_probe/k6_strict_split_local_descent.py \
  cl_probe/k6_balanced_split_target_search_best_t13_t40.csv \
  --max-rounds 8 --emit-permutation
python3 cl_probe/k6_strict_split_block_growth.py \
  cl_probe/k6_strict_split_zero_neighbor_witnesses_t13_t40.csv \
  --emit-permutation
python3 cl_probe/k6_strict_split_fixed_bridge_growth.py \
  cl_probe/k6_strict_split_block_growth_t39_to_t40.csv \
  --found-only --emit-permutation
python3 cl_probe/k6_strict_split_fixed_bridge_growth.py \
  cl_probe/k6_strict_split_fixed_bridge_growth_t40_to_t41.csv \
  --found-only --emit-permutation
python3 cl_probe/k6_strict_split_fixed_bridge_growth.py \
  cl_probe/k6_strict_split_fixed_bridge_growth_t41_to_t42.csv \
  --found-only --emit-permutation
python3 cl_probe/k6_strict_split_fixed_bridge_growth.py \
  cl_probe/k6_strict_split_fixed_bridge_growth_t42_to_t43.csv \
  --found-only
python3 cl_probe/k6_strict_split_fixed_bridge_hit_counts.py \
  cl_probe/k6_strict_split_fixed_bridge_growth_t42_to_t43.csv \
  --found-only
python3 cl_probe/k6_strict_split_fixed_bridge_hit_summary.py \
  cl_probe/k6_strict_split_fixed_bridge_hit_counts_t40_to_t41.csv \
  cl_probe/k6_strict_split_fixed_bridge_hit_counts_t41_to_t42.csv \
  cl_probe/k6_strict_split_fixed_bridge_hit_counts_t42_to_t43.csv \
  cl_probe/k6_strict_split_fixed_bridge_hit_counts_t43_to_t44.csv
python3 cl_probe/k6_strict_split_bridge_location_counts.py \
  cl_probe/k6_strict_split_fixed_bridge_growth_t40_to_t41.csv \
  --source-row 7 --target-g 52 --target-p 54 --target-q 54 \
  --new-domain-offsets 0
python3 cl_probe/k6_strict_split_bridge_location_counts.py \
  cl_probe/k6_strict_split_fixed_bridge_growth_t40_to_t41.csv \
  --source-row 7 --target-g 52 --target-p 54 --target-q 54 \
  --new-domain-offsets 0,1,2,3,4,5
python3 cl_probe/k6_strict_split_bridge_choice_extract.py \
  cl_probe/k6_strict_split_fixed_bridge_growth_t40_to_t41.csv \
  cl_probe/k6_strict_split_bridge_location_counts_t41_to_t42_all_offsets.csv \
  --old-domains 0,1,120,245 --new-domain-offsets 0
python3 cl_probe/k6_strict_split_bridge_witness_uniqueness.py \
  cl_probe/k6_strict_split_fixed_bridge_growth_t40_to_t41.csv \
  --source-row 7 --target-g 52 --target-p 54 --target-q 54 \
  --new-domain-offsets 0,1,2,3,4,5
python3 cl_probe/bidefect_witness_search.py --k 6 --t 4 --g-plus 5 --g-minus 5 --seed 1730
python3 cl_probe/bidefect_witness_sweep.py --k 6 --t-max 12 --max-samples 100000 --seed 20260617
python3 cl_probe/connected_bidefect_sampler.py --k 6 --t 6 --samples 30000 --seed 1731
python3 cl_probe/one_sided_defect_sanity.py cl_probe/spectrum_k4_defect_exact.csv --eta 2
python3 cl_probe/connected_defect_spectrum.py cl_probe/spectrum_k4_defect_exact.csv --k 4
python3 cl_probe/connected_balance_sanity.py cl_probe/spectrum_k4_defect_exact.csv --k 4
python3 cl_probe/k2_one_sided_defect_sanity.py --eta 2
./cl_probe/bin/two_block_open_exact --k 6
./cl_probe/bin/two_block_open_exact --k 6 --bidefect
python3 cl_probe/two_block_open_sampler.py --k 6 --samples 50000 --seed 1729
```

The connected bidefect sampler is finite-sample evidence only.  Its summary
separates rows before the cycle-count crossing from the largest rows by raw
sample frequency, because the latter may already lie in a range controlled by
the cycle-count envelope.  It reports both the exact finite density `E/t` and
the leading density `4+2(g_++g_-)/t`; the pre-cycle summary uses the leading
density, which is the relevant coordinate for growing component sizes.

The balanced-strip target sweep is also heuristic finite evidence.  It uses
the exact `k=6` arithmetic strip `11/9 < g/t < 13/10`, then runs the targeted
local search on each balanced row.  A found row proves finite nonemptiness of
that target row; a miss is not a proof of emptiness.
The tracked file `k6_balanced_strip_witnesses_t13_t40.csv` stores explicit
permutation images for the `t=13..40` found rows, and
`k6_balanced_strip_certificates.py --verify` recomputes their cycle counts,
defects, genera, and connectedness.
The neutral-move profiler enumerates all single image-swaps around each stored
certificate and counts how many swaps remain in the same balanced row.  This is
a local finite multiplicity diagnostic, not an asymptotic row count.
The shape profiler records the cycle-count split
`#pi + #(gamma*pi) = #pi + #(pi*gamma^-1)` and coarse cycle-length statistics
for the certified rows.  This is a structural diagnostic for future counting
arguments.
The split-window calculator lists which balanced rows still have strict or
boundary split slots after applying the three-cycle-count envelope at fixed
`(#pi,#(gamma*pi),#(pi*gamma^-1))`.
The split-target search is a heuristic transposition-walk search on those
strict split slots.  A miss is not an emptiness proof; it records the best
cycle-count triple seen under the chosen finite budget.
The split-asymptotics calculator counts the arithmetic strict split slots
left after this refinement.  It proves only that the target slot lattice is
infinite and gives its leading size; it does not count permutations inside
those slots.
The invariant sanity script checks cheap sign parity on the strict slots and
summarizes the deficit pattern in a target-search CSV.
The near-hit local profiler and extractor deterministically inspect saved
best misses from the target search.  In the tracked `t=13..40` run, this
recovers one genuine strict split witness from a one-swap neighbor.
The local descent script follows strict score-improving one-swaps from the
same saved near-hits and records whether they reach another witness or a
one-swap local minimum.
The block-growth probe tests whether a strict witness can be extended by one
new six-point block and one bridge image-swap.  The tracked `39 -> 40` run
constructs all strict split targets at `t=40` from the `t=39` witness.
The fixed-bridge growth probe specializes this construction to the bridge
`0:new_block_start` and varies only the new block's internal permutation.  The
tracked run propagates strict witnesses through `t=44`.
The fixed-bridge hit-count probe counts how many of the `6!` internal block
permutations work for each source-target pair, giving a finite branching
diagnostic rather than just first-hit certificates.
The bridge-location count probe fixes one source-target step and counts how
many old bridge domains work.  The tracked sample shows that all old domains
work for one `t=41 -> t=42` strict target, and the all-offset sample shows
that all six new-domain offsets work too.
The bridge-choice extractor materializes selected bridge choices as witnesses
so the next step can test whether different previous bridge domains preserve
the same bridge-location multiplicity.
The bridge-witness uniqueness probe checks whether the bridge-location
construction choices collapse to duplicate permutations.  In the tracked
representative `t=41 -> t=42` all-offset sample, it reports `168264`
successful choices, `168264` distinct witnesses, and no duplicate hits.

The current detailed write-up of this branch is
`K6_STRICT_SPLIT_RESULTS_REPORT.md`.

To extract connected active component spectra and benchmark the component/cycle
frontier for `k=4`, run:

```bash
python3 cl_probe/connected_spectrum.py cl_probe/spectrum_k4_exact.csv --k 4
python3 cl_probe/component_frontier.py --alpha-min 2 --alpha-max 4.8
python3 cl_probe/k4_map_genus_frontier.py --alpha-min 3.8 --alpha-max 4.8
python3 cl_probe/connected_bound_sanity.py
```

The `k4_map_genus_frontier.py` command is a conditional proof-target
calculator: it assumes the connected map/genus estimate
`exp(O(t)) t! t^(3h)` and shows that this input would close the remaining
`k=4` proportional window.  The proof packet
`CL_connected_map_genus_bound.md` records the hypermap translation and the
Chapuy-slicing route to that estimate; `connected_bound_sanity.py` checks the
shape on exact connected data through `t=3`.

To test whether the same map/genus component strategy would settle higher
even `k`, run:

```bash
python3 cl_probe/k_map_genus_frontier.py --table-k-max 12
```

This shows that the standard `t^(3h)` Chapuy cost closes `k=4` but already
fails to close the central window for `k=6`; the all-even proof needs more
structure than the direct `k=4` map/genus transplant.  The table also prints
the critical effective exponent
`eta_crit(k)=(k^2-3k+1)/(k^2-4k+1)` required by this direct component strategy.
For the global one-sided genus benchmark, `eta=2` is a critical leading target;
strict closure needs `eta<2` or an additional boundary-layer estimate at
`E/r=2k`.

For a noisy finite-sample spectrum beyond the exact brute-force range, run:

```bash
python3 cl_probe/mc_spectrum.py --k 4 --r 8 --samples 100000 --seed 37
```

This Monte Carlo probe is only a stress diagnostic; it is not an exact count
and is not used as proof of CL.

## Exact structural k=2 spectrum through r=28

For `k=2`, use the compiled GMP-backed character/component extractor:

```bash
GMP=$(brew --prefix gmp)
g++ -O3 -std=c++17 -I"$GMP/include" -L"$GMP/lib" \
  -Wl,-rpath,"$GMP/lib" \
  cl_probe/k2_character_spectrum_gmp.cpp -lgmpxx -lgmp \
  -o cl_probe/bin/k2_character_spectrum_gmp

./cl_probe/bin/k2_character_spectrum_gmp --r-max 28 \
  --out cl_probe/spectrum_k2_character.csv
```

There is also a Python version with the same formulas, useful for smaller
cross-checks:

```bash
python3 cl_probe/k2_character_spectrum.py --r-max 20 --out /tmp/k2_python.csv
```

This computes the total two-cycle-count polynomial from symmetric-group
connection coefficients for the fixed matching class, extracts connected
components by the labelled exponential formula, removes size-one trivial
components, and writes the active spectrum.  The connection-coefficient step
uses the Jucys-Murphy content-polynomial identity for the cycle-count transform,
which keeps `r=28` practical in the compiled GMP version.  It was validated
against the compiled brute-force enumerator through `r=6`.  The compiled
structural extractor matches the Python structural CSV through `r=20`, and its
`r<=26` prefix was revalidated before accepting the compiled `r=28` extension.

One reproducible validation is:

```bash
python3 cl_probe/k2_character_spectrum.py --r-max 6 --out /tmp/k2_char_r6.csv
./cl_probe/bin/cl_spectrum --k 2 --r-min 2 --r-max 6 --csv > /tmp/k2_brute_r6.csv
python3 - <<'PY'
import csv

def rows(path):
    with open(path) as f:
        return sorted(tuple(int(row[k]) for k in ["k", "r", "j", "h", "E", "count"])
                      for row in csv.DictReader(f))

assert rows("/tmp/k2_char_r6.csv") == rows("/tmp/k2_brute_r6.csv")
print("validation ok")
PY
```

## Diagonal extrapolation

Run the consolidated finite-data stress audit:

```bash
python3 cl_probe/cl_stress_audit.py --k 2 \
  --csv cl_probe/spectrum_k2_character.csv
```

This reruns the headline checks below and exits nonzero if any tested
finite/extrapolated margin is positive.  It now reports the remaining central
window `E/r <= 2k` separately from the full finite proportional profile.
Passing this audit is evidence only, not a proof of (CL).

```bash
python3 cl_probe/analyze_cl.py --k 2 --csv cl_probe/spectrum_k2_character.csv \
  --N 50 200 1000 4000 --rho 0.5 1 2
```

The extrapolation is deliberately conservative and explicitly limited: it fits
fixed-excess bands `E = 2r + t` from exact small-`r` data.  It is numerical
evidence only, not a proof of (CL) on the diagonal.

For a finite-data check aimed directly at proportional-energy bands, run:

```bash
python3 cl_probe/profile_cl.py --k 2 \
  --csv cl_probe/spectrum_k2_character.csv --tail-min-r 6
```

For a compact tail-window trend view, run:

```bash
python3 cl_probe/profile_trends.py --k 2 \
  --csv cl_probe/spectrum_k2_character.csv --recent-count 8
```

For a proportional-ray extrapolation aimed at bands `E/r ~= alpha`, run:

```bash
python3 cl_probe/proportional_ray_fit.py --k 2 \
  --csv cl_probe/spectrum_k2_character.csv \
  --min-r 10 --alpha-min 2 --alpha-max 6 --alpha-step 0.25 \
  --window 0.13 --min-points 6
```

For a small sensitivity grid over ray-fit cutoffs and matching windows, run:

```bash
python3 cl_probe/proportional_ray_sensitivity.py --k 2 \
  --csv cl_probe/spectrum_k2_character.csv
```

For a finite-data backtest of the ray fits, run:

```bash
python3 cl_probe/proportional_ray_backtest.py --k 2 \
  --csv cl_probe/spectrum_k2_character.csv
```

The first profile command reports the empirical entropy profile as a function
of `E/r` and the leading diagonal CL margin for each exact band.  The trend
command summarizes moving tail-window maxima and the frontier bands.  The ray
fit follows approximate proportional-energy bands and fits beta against
`1/log r`; the sensitivity script repeats that fit over several cutoffs, alpha
steps, and windows.  The backtest trains ray fits on earlier `r` values and
checks their predictions against later exact rows.  The default tail window
avoids using the very small `r` rows as a headline verdict.
