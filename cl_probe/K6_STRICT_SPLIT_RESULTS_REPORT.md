# Report on the `k=6` strict split probe

## 1. Executive summary

The current computation does **not** prove the combinatorial lemma (CL) for
general even `k`.  It does, however, identify a concrete and nontrivial
remaining threat mechanism in the first open case `k=6`.

The main result of the latest probe is this:

```text
t = 41 -> 42 representative strict split step
construction choices checked: 1,062,720
successful choices:           168,264
distinct witness permutations:168,264
duplicate successful choices:  0
```

Thus, in this representative step, the large bridge-location count is not an
artifact of many construction choices producing the same permutation.  Every
successful choice counted by the probe gives a different witness.

This matters because the remaining obstruction to CL is not just existence of
some finite witnesses.  The dangerous question is asymptotic entropy: can
strict split witnesses be grown in sufficiently many independent ways to create
a diagonal count of size large enough to violate the desired `limsup` bound?

The present evidence says:

- strict split target slots exist infinitely often at the arithmetic level;
- a genuine strict split witness exists at `t=39`;
- that witness can be propagated through several later sizes;
- bridge-location choices give a real `O(t)` one-step multiplicity in a
  representative growth step;
- the successful bridge choices in that step are distinct as permutations;
- but the observed bridge factor, even if independently iterable, appears to
  contribute only about one unit of `t log t` entropy, whereas the strict-strip
  breach threshold is roughly `4.7--4.8` units.

So the honest conclusion is:

```text
The k=6 strict split branch is real and deserves a proof-level explanation.
It is not yet an asymptotic counterexample to CL.
CL remains open.
```

## 2. The mathematical object being probed

The CL problem is a diagonal counting problem for permutation data associated
with partial-transpose Wick expansions.  The relevant data are the cycle
counts

```text
#pi,
#(gamma*pi),
#(pi*gamma^{-1}),
```

where `gamma` is the block long-cycle determined by `k` and the size parameter
`t`.  In the `k=6` probe, the ambient permutation acts on `6t` points.

The hard region is not the high-energy region.  The high-energy bands are
already controlled by coarse counting.  The remaining issue is the central
balanced diagonal window, where the three-cycle-count envelope is close to
being sharp.

Inside that window, the current scripts isolate **strict split slots**.  These
are arithmetic target triples `(g,p,q)` for which the existing
three-cycle-count envelope still leaves a possible gap.  Here:

```text
g = g_+ = g_-
p = #pi
q = #(gamma*pi) = #(pi*gamma^{-1}) target side, depending on the split
```

The word "strict" means the target lies strictly inside the remaining strip,
not just on a boundary case.

The computational question is:

```text
Are there connected permutations pi realizing these strict split cycle counts,
and if so, how many can be grown?
```

The proof-level question is stronger:

```text
Can one prove a uniform upper bound on the number of such permutations strong
enough to preserve the CL limsup inequality?
```

## 3. Arithmetic strict slots

The script

```text
cl_probe/k6_balanced_split_asymptotics.py
```

counts the arithmetic strict split slots left after the current envelope
refinement.

The leading asymptotics recorded by the script are:

```text
strict rows  ~ (7/180) T^2
strict slots ~ (7/4860) T^3
```

Through `T=400`, the tracked output reports:

```text
strict rows:  5,500
strict slots: 79,431
```

This is important but limited.  It says the target lattice is infinite and has
positive polynomial density.  It does **not** say those slots contain
permutations, and it does **not** give an entropy lower bound.

The output file is:

```text
cl_probe/k6_balanced_split_asymptotics_t13.csv
```

## 4. Invariant sanity checks

The script

```text
cl_probe/k6_balanced_split_invariant_sanity.py
```

checks a cheap necessary sign-parity condition on the strict slots.  Through
`t <= 80`, all `333` strict slots satisfy

```text
q - p == t mod 2.
```

This removes one possible explanation for the remaining slots.  They are not
merely impossible because of the first obvious parity obstruction.

The output file is:

```text
cl_probe/k6_balanced_split_invariant_sanity_t13_t80.csv
```

## 5. First strict witness

The original target search did not directly find strict witnesses through
`t=40`.  It found near misses.  The local one-swap profiler then inspected the
saved near misses and found a genuine zero-score neighbor.

The extracted witness is:

```text
(t,g,p,q) = (39,48,50,51)
#pi = 50
#(gamma*pi) = 51
#(pi*gamma^{-1}) = 51
g_+ = 48
g_- = 48
components = 1
```

This is a connected strict split witness.

The relevant files are:

```text
cl_probe/k6_balanced_split_target_search_best_t13_t40.csv
cl_probe/k6_strict_split_near_hit_local_profile_t13_t40.csv
cl_probe/k6_strict_split_zero_neighbor_witnesses_t13_t40.csv
```

Mathematical interpretation:

```text
The strict split branch is not empty.
```

This is a finite existence result, not an asymptotic count.

## 6. One-step block growth from t=39 to t=40

Starting from the `t=39` witness, the block-growth probe adds one new
six-point block and one bridge image-swap.  It constructs all four strict
targets at `t=40`:

```text
(40,49,51,53)
(40,49,52,52)
(40,49,53,51)
(40,50,51,51)
```

Each constructed row has the requested cycle counts and remains connected.

The output file is:

```text
cl_probe/k6_strict_split_block_growth_t39_to_t40.csv
```

Mathematical interpretation:

```text
The t=39 strict witness is not isolated.  There is a concrete local extension
operation that reaches every strict target at t=40.
```

Again, this is still finite.  The proof-level task would be to replace this
checked instance by a uniform growth lemma.

## 7. Fixed-bridge propagation through t=44

The fixed-bridge growth probe specializes the extension operation to one
bridge position, namely the bridge from old domain `0` to the start of the new
block, and varies only the internal permutation of the new six-point block.

The tracked propagation summary is:

```text
40 -> 41:  6 found rows, all 2 strict target slots hit
41 -> 42: 12 found rows, all 2 strict target slots hit
42 -> 43: 24 found rows, all 2 strict target slots hit
43 -> 44: 96 found rows, all 4 strict target slots hit
```

Every found row verifies the requested cycle counts and connectedness.

The output files are:

```text
cl_probe/k6_strict_split_fixed_bridge_growth_t40_to_t41.csv
cl_probe/k6_strict_split_fixed_bridge_growth_t41_to_t42.csv
cl_probe/k6_strict_split_fixed_bridge_growth_t42_to_t43.csv
cl_probe/k6_strict_split_fixed_bridge_growth_t43_to_t44_summary.csv
```

Mathematical interpretation:

```text
A very restricted growth rule already propagates the strict branch several
steps.  The branch is not a one-off accident of t=39.
```

What this does not prove:

```text
It does not prove propagation for all t.
It does not prove enough multiplicity for a CL breach.
It does not give an upper bound either.
```

## 8. Fixed-bridge hit counts

The fixed-bridge hit-count probe counts how many of the `6! = 720` internal
new-block permutations work for each source-target pair.

The aggregated results are:

```text
40 -> 41: total hits 188 + 204 = 392
41 -> 42: total hits 732 + 222 = 954
42 -> 43: total hits 714 + 960 = 1,674
43 -> 44: total hits 1,440 + 2,928 + 1,740 + 888 = 6,996
```

Positive source-target hit counts range from small but nonzero values to
`130` successful internal permutations.

The summary file is:

```text
cl_probe/k6_strict_split_fixed_bridge_hit_summary_t40_to_t44.csv
```

Mathematical interpretation:

```text
The fixed bridge already has many internal choices, but this factor is bounded
by 720 per source-target pair.  By itself it cannot produce t log t entropy.
```

Thus the fixed-bridge internal block permutations are useful evidence of
robustness, but they are not the main entropy danger.

## 9. Bridge-location multiplicity

The bridge-location count probe then asks a sharper question.  Instead of
fixing the old bridge domain, it fixes one source-target step and varies the
old domain used in the bridge.

For the representative step

```text
source: (t,g,p,q) = (41,51,53,52)
target: (t,g,p,q) = (42,52,54,54)
```

with one fixed new-domain offset, the result is:

```text
old domains checked:     246 = 6*41
positive old domains:    246
hits per old domain:     114
total successful choices:28,044
```

With all six new-domain offsets, the result is:

```text
old/new bridge pairs checked: 1,476 = 6*(6*41)
positive bridge pairs:        1,476
hits per bridge pair:         114
total successful choices:     168,264
```

The output files are:

```text
cl_probe/k6_strict_split_bridge_location_counts_t41_to_t42_sample.csv
cl_probe/k6_strict_split_bridge_location_counts_t41_to_t42_all_offsets.csv
```

Mathematical interpretation:

```text
In this representative step, the bridge location supplies a genuine O(t)
family of successful construction choices.
```

This is the first place where a possible `t log t` entropy source appears.

## 10. Distinctness of the bridge-location witnesses

The latest uniqueness probe checks whether the `168,264` successful
bridge-location choices collapse to fewer actual permutations.

It does this by hashing every successful witness permutation in the same
representative step:

```text
source: (t,g,p,q) = (41,51,53,52)
target: (t,g,p,q) = (42,52,54,54)
new-domain offsets: 0,1,2,3,4,5
old domains checked: 246
choices checked: 1,062,720
```

The reproduced result is:

```text
hit_count:          168,264
distinct_witnesses:168,264
duplicate_hits:    0
min hits per old domain: 684
max hits per old domain: 684
hits by offset:
  0: 28,044
  1: 28,044
  2: 28,044
  3: 28,044
  4: 28,044
  5: 28,044
```

The output file is:

```text
cl_probe/k6_strict_split_bridge_witness_uniqueness_t41_to_t42_all_offsets.csv
```

Mathematical interpretation:

```text
For this step, the bridge-location count is a real lower-count factor, not an
overcount caused by duplicate construction choices.
```

This is an important correction to the evidential status of the probe.  Before
this check, the bridge-location count could have been mostly parametrization
noise.  After this check, at least in the tested step, it is actual witness
multiplicity.

What it still does not prove:

```text
It does not prove the same distinctness uniformly in t.
It does not prove independence across multiple growth steps.
It does not prove that the resulting count reaches the CL breach threshold.
```

## 11. Two-step independence evidence

The bridge-choice extraction script saved four distinct `t=42` witnesses coming
from different old bridge domains:

```text
old bridge domains: 0, 1, 120, 245
```

The next-step independence sample then used each of those four witnesses as a
source for the step toward

```text
(t,g,p,q) = (43,53,55,56).
```

The result is:

```text
sources tested:       4
old domains per source:252
positive old domains: 1008
hits per old domain:  114
total witnesses:      114,912
```

The relevant files are:

```text
cl_probe/k6_strict_split_bridge_choice_sample_t42.csv
cl_probe/k6_strict_split_bridge_independence_sample_t42_to_t43.csv
```

Mathematical interpretation:

```text
Changing the previous bridge location does not immediately destroy the next
bridge-location factor.
```

This is exactly the kind of fact one would need for an entropy lower-bound
construction.  But it is still only a finite two-step sample.  It is not an
induction.

## 12. Entropy reading

The danger to CL is not that there are many finite witnesses.  The danger would
be a lower bound of the form

```text
log count(t) >= c t log t + O(t)
```

with `c` large enough to defeat the rising-factorial penalty in the CL
inequality.

The strict strip currently appears to require roughly

```text
c ~= 4.7--4.8
```

units of `t log t` entropy to become a genuine asymptotic breach.

The bridge-location mechanism gives, at most naively,

```text
one O(t) choice per growth step.
```

If such choices were independent over `t` growth steps, that would contribute
roughly

```text
sum_{s <= t} log s = t log t + O(t),
```

or about one entropy unit.

This is significant, but it is not enough by itself to cross the apparent
`4.7--4.8` threshold.

Therefore:

```text
The bridge mechanism is a real entropy source.
The observed bridge mechanism alone is not yet a CL counterexample.
```

To threaten CL, one would need additional independent choices, a larger
branching mechanism, or a different family with several independent
polynomial-size choices per growth step.

## 13. What has been proved by computation

The computations prove the following finite statements, conditional only on
the correctness of the scripts and their deterministic verification routines:

1. The strict split target lattice is infinite at the arithmetic level and has
   the recorded polynomial leading size.

2. The parity sanity condition does not eliminate the tracked strict slots
   through the tested range.

3. There is a connected strict split witness at `(t,g,p,q)=(39,48,50,51)`.

4. That witness grows to all strict target slots at `t=40` by the tested
   block-plus-bridge operation.

5. A fixed-bridge specialization propagates strict witnesses through `t=44`.

6. Internal new-block permutations give many successful choices, but only a
   bounded factor per source-target pair.

7. In one representative `t=41 -> 42` step, every old bridge domain and every
   new-domain offset is viable, and each bridge pair has exactly `114`
   successful internal choices.

8. In that same representative step, the `168,264` successful choices give
   `168,264` distinct witness permutations.

9. A small two-step sample shows that changing the previous bridge domain does
   not immediately kill the next bridge-location factor.

These are genuine finite results.  They should be cited as finite probes, not
as asymptotic theorems.

## 14. What is not proved

The following statements are **not** proved:

1. Uniform strict split nonemptiness for all sufficiently large `t`.

2. Uniform bridge-location viability for all strict source-target steps.

3. A closed-form injection or recurrence generating the observed witnesses.

4. Independence of bridge-location choices across arbitrarily many growth
   steps.

5. A lower bound large enough to violate CL.

6. A matching upper bound proving that this branch is harmless.

7. The general even-`k` CL theorem.

This distinction matters.  The computations have found a real branch, but the
asymptotic theorem is still missing.

## 15. The right next theorem

The next useful theorem is not another finite search.  It is a structural
statement explaining the bridge growth.

A natural target is:

```text
For every sufficiently large t and every source in the strict split family
with the observed local form, a positive proportion of old bridge domains
and a fixed positive number of internal new-block permutations produce a
connected strict split witness at size t+1.
```

This would turn the observed finite pattern into an actual lower-bound
mechanism.

However, even that theorem would probably not disprove CL by itself, because
one bridge-domain choice per step gives only about one `t log t` entropy unit.
It would instead clarify the branch and force the upper-bound proof to account
for it.

The theorem that would be decisive in the other direction is an upper bound:

```text
The total number of connected strict split witnesses in the remaining k=6
strip is at most exp(O(t)) t^{c t}
```

with

```text
c < the CL breach threshold.
```

The current data suggest such a theorem may be true, but they do not prove it.

## 16. Bottom line

The latest result strengthens the evidence in a very specific way:

```text
The bridge-location family is not fake multiplicity.
```

It gives real distinct witnesses in the representative `t=41 -> 42` step.
That makes the strict split branch mathematically meaningful and worth
understanding.

But the same result also keeps the scale in perspective:

```text
One real bridge-location factor per step is serious, but it is far below the
currently visible entropy needed for a CL breach.
```

So the state of affairs is:

```text
CL is not proved.
No counterexample is proved.
The k=6 strict split branch is the live frontier.
The newest probe confirms real one-step witness multiplicity, not an
asymptotic violation.
```

