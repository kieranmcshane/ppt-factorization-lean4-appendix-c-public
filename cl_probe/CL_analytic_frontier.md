# CL analytic frontier

This note isolates the analytic statement that would actually settle the
diagonal combinatorial lemma (CL).  It is not a proof.  Its purpose is to
turn the current exact `k=2` computations into a precise asymptotic target.

## 1. The beta-surface target

Write

```text
N_r(E) = #{active permutations with energy E}.
```

On the diagonal `r = rho a_d`, with `a_d = N^{1+1/k}`, one has

```text
log r = (1 + 1/k) log N + O(1).
```

For a proportional energy band `E = alpha r`, define the entropy surface

```text
beta_k(alpha)
  = limsup log N_r(E) / (r log r),
```

where the limsup is taken along integer pairs with `E/r -> alpha`.

The variational criterion (CL') is

```text
sup_E [log N_r(E) - (E/2) log N]
  <= r log N + o(a_d).
```

Therefore the proportional-band entropy condition needed for CL is

```text
(1 + 1/k) beta_k(alpha) - alpha/2 <= 1
```

for every relevant `alpha`, with enough uniformity in the tails.  Equivalently,

```text
beta_k(alpha) <= (k/(k+1)) (1 + alpha/2).
```

For `k=2`, this becomes

```text
beta_2(alpha) <= 2/3 + alpha/3.
```

This is a one-sided upper-bound problem.  The object above is therefore a
`limsup`: it is enough to prove that no subsequence of proportional energy
bands has entropy above the threshold.  A matching `liminf` would be relevant
only for a lower-bound construction or for proving sharpness/failure of the
candidate threshold; it is not part of the upper-tail CL closure.

This is exactly the leading margin used by the proportional diagnostics:

```text
margin_2(r,E)
  = log N_r(E)/(r log r) - E/(3r) - 2/3.
```

Thus the numerical evidence in `profile_cl.py`, `profile_trends.py`,
`proportional_ray_fit.py`, `proportional_ray_sensitivity.py`,
`proportional_ray_backtest.py`, and `cl_stress_audit.py` is probing the
same inequality.  The missing proof is a uniform upper bound on
`beta_k(alpha)`.

## 2. A proved high-energy cutoff

There is one simple analytic reduction that does not use the special
partial-transpose structure.  Since the active set is a subset of `S_{kr}`,

```text
N_r(E) <= (kr)!.
```

Fix `C < infinity`, `eta > 0`, and work uniformly on `r <= C a_d`.  If

```text
E >= (2k + eta) r,
```

then, using `log r = (1 + 1/k) log N + O_{k,C}(1)`,

```text
log N_r(E) - (E/2) log N - r log N
  <= log((kr)!) - ((2k + eta)r/2) log N - r log N
  <= kr log(kr) - (k + 1 + eta/2) r log N
  = -(eta/2) r log N + O_{k,C}(r).
```

For large `N`, this is at most `-(eta/4) r log N`, hence is much smaller than
the allowed `o(a_d)` error on the diagonal.  Therefore no fixed positive
energy gap above `E/r = 2k` can breach (CL').

Equivalently, the trivial entropy bound `beta_k(alpha) <= k` is already enough
for every fixed `alpha > 2k`.  The boundary `alpha = 2k` is not closed by this
argument: the remaining `O(r)` term is of order `a_d`, not `o(a_d)`.  Thus the
real analytic problem is localized to the compact proportional window

```text
2 <= E/r <= 2k + o(1),
```

and, for `k=2`, essentially to `2 <= E/r <= 4` plus the boundary layer near
`4`.  This explains why the raw entropy peak at larger observed `E/r` values
is not automatically dangerous after the diagonal penalty is included.

## 3. A three-cycle-count entropy envelope

The high-energy cutoff can be sharpened by using all three cycle counts in the
energy.  Put `n = kr` and write

```text
p = #pi,       a = #(gamma pi),       b = #(pi gamma^{-1}).
```

Then

```text
2p + a + b = (2k + 2 - alpha) r
```

on the proportional band `E = alpha r`.

Let `c(n,q)` be the unsigned Stirling number of the first kind, i.e. the number
of permutations in `S_n` with exactly `q` cycles.  If `q = xr`, then uniformly
for fixed `k` and `0 <= x <= k`,

```text
log c(kr, xr) <= (k - x) r log r + O_k(r).
```

Indeed, with `m = kr - xr`,

```text
c(kr, xr) = e_m(1,2,...,kr-1)
          <= (1 + 2 + ... + (kr-1))^m / m!,
```

and Stirling's formula gives the displayed leading coefficient.

For fixed `(p,a,b)`, the number of permutations with these three cycle counts
is bounded by each of `c(n,p)`, `c(n,a)`, and `c(n,b)`.  The number of possible
triples is polynomial in `r`, so it is invisible at `r log r` scale.  Therefore

```text
beta_k(alpha)
  <= max_{2x+y+z=2k+2-alpha} min(k-x, k-y, k-z).
```

The right-hand side is maximized by minimizing `max(x,y,z)` under
`2x+y+z = 2k+2-alpha`.  Since the total weight is `4`, this gives

```text
beta_k(alpha) <= (k - 1)/2 + alpha/4.
```

For `k=2`, this is

```text
beta_2(alpha) <= 1/2 + alpha/4,
```

whereas the CL threshold is

```text
2/3 + alpha/3.
```

The gap is

```text
(2/3 + alpha/3) - (1/2 + alpha/4)
  = 1/6 + alpha/12 > 0.
```

Thus the three-cycle-count envelope proves the proportional `limsup` entropy
target for `k=2` at the leading `r log r` scale.  This is stronger than the
finite-data evidence and explains why the observed `k=2` proportional margins
are not drifting toward a breach.

For `k=2`, the same estimate also stitches into the full uniform (CL') bound.
Indeed, for `r <= C N^{3/2}` and all energies,

```text
log N_r(E)
  <= (r/2 + E/4) log r + O_C(r).
```

Since `log r <= (3/2) log N + O_C(1) < 2 log N` for large `N`, the coefficient
of `E` in

```text
log N_r(E) - (E/2) log N
```

is negative.  Hence

```text
sup_E [log N_r(E) - (E/2) log N]
  <= (r/2) log r + O_C(r).
```

Let

```text
P_{r,N} = log[(s)_{2r}/s^{2r}],        s ~ lambda N.
```

It remains to compare `(r/2)log r` with `P_{r,N}` uniformly for
`0 <= r <= C N^{3/2}`.  This is elementary:

* if `r <= N^{4/3 + delta}` with fixed `delta < 1/6`, then
  `r log N = o(N^{3/2})`, so the whole left side is already `o(a_d)`;
* if `r = Nt` with `t >= N^{1/3 + delta}`, then for any small fixed
  `epsilon > 0`,

```text
P_{r,N}
  >= (2 - epsilon) r log(1 + epsilon t/lambda),
```

because all terms with `i >= epsilon r` contribute at least this much.  Choosing
`epsilon` so small that

```text
(2 - epsilon)(1/3 + delta) > 2/3 + delta/2,
```

this lower bound dominates `(r/2)log r + O_C(r)` for large `N`.  This is the
worst comparison in the large-`r` range: if `r = N^{1+beta}`, then the lower
bound has leading coefficient `(2 - epsilon) beta`, while `(r/2)log r` has
leading coefficient `(1 + beta)/2`, and the difference increases for
`beta > 1/3 + delta`.

The fixed factor `lambda^{#pi-2r}` present away from `lambda = 1` changes the
left side by at most `O_lambda(r)`, so it is absorbed in the same `O_C(r)`
remainder for fixed `lambda > 0`.

Therefore

```text
sup_E [log N_r(E) - (E/2) log N]
  <= P_{r,N} + o(N^{3/2})
```

uniformly for `0 <= r <= C N^{3/2}`.  In other words, the combinatorial lemma
(CL) is proved by this cycle-count envelope in the `k=2` case.  This is a
paper-level proof, not a Lean formalization.

For general even `k`, the same envelope closes only the range where

```text
(k - 1)/2 + alpha/4
  <= (k/(k+1)) (1 + alpha/2).
```

Equivalently, for `k >= 4`, it closes

```text
alpha >= (2k^2 - 4k - 2)/(k - 1).
```

This is only an upper subwindow of the central range, so more structure is
still needed below that crossing.  For example, the remaining `k=4` window is

```text
2 <= alpha < 14/3.
```

The script `cycle_count_envelope.py` prints this comparison.

## 4. One-sided genus-count benchmark

Another natural input is a one-sided plus-defect count.  Suppose that the
number of permutations in one plus-defect genus slice satisfies

```text
count(g) <= exp(O(r)) r^(eta g).
```

Since `delta_+ = 2g_+`, `delta_- = 2g_-`, and
`delta_+ + delta_- = E = alpha r`, the intersection of the two one-sided
estimates gives, at best,

```text
beta_k(alpha) <= eta alpha/4,
```

with the maximum at balanced bidefects.  Comparing with the CL threshold gives
the closed range

```text
alpha <= 4k / (eta(k+1) - 2k)
```

when `eta(k+1) > 2k`; if `eta(k+1) <= 2k`, this benchmark closes every
nonnegative `alpha`.

For `k=4`, a crude Chapuy-slicing exponent `eta=3` closes only

```text
2 <= alpha <= 16/7.
```

Thus it is useful but far from enough: the interval `16/7 < alpha < 14/3`
remains open after combining it with the three-cycle-count envelope.  An
effective one-sided exponent `eta=2` would close the whole `k=4` window.

The script `genus_frontier.py` prints this benchmark.

There is, however, a sharp algebraic target hidden in this calculation.  Since
the high-energy cutoff has already reduced the problem to the central window
`0 <= alpha <= 2k`, the global one-sided genus route has critical leading
exponent

```text
eta <= 2.
```

Indeed, at `eta=2` the one-sided intersection gives `beta_k(alpha) <= alpha/2`,
and the CL threshold satisfies

```text
alpha/2 <= (k/(k+1)) (1 + alpha/2)
```

exactly up to `alpha <= 2k`.  The endpoint `alpha=2k` is the equality case.
Consequently, a bound with `eta<2` gives a strict leading margin throughout the
central window.  A bound with exactly `eta=2` reduces the problem to the
boundary layer near `alpha=2k`; with a general `exp(O(r))` prefactor it does
not by itself give the required `o(a_d)` error at the equality endpoint.

For closing all nonnegative `alpha` without separately using the high-energy
cutoff one would need the stronger condition

```text
eta <= 2k/(k+1),
```

but that is not necessary for CL because fixed gaps above `2k` are already
handled by the trivial factorial bound.

The exact one-sided variable is the plus defect

```text
delta_+(pi) = kr + r - #pi - #(gamma pi).
```

On a connected component using `t` original `k`-blocks, the hypermap Euler
identity gives

```text
delta_+ = 2(t - 1 + g_+),
```

where `g_+ >= 0` is the genus of the one-sided hypermap defined by
`(gamma, pi)`.  Thus the global half-defect is

```text
delta_+(pi)/2 = (r - c(pi)) + sum_components g_+.
```

The script `connected_defect_spectrum.py` extracts the connected bidefect
spectrum from the exact defect CSV and checks this parity/lower-bound identity
on the available `k=4,r<=3` data.

The same one-sided slice has a crude cycle-count envelope that is useful near
the high-defect edge.  If `delta_+ = d r`, then

```text
#pi/r + #(gamma pi)/r = k + 1 - d.
```

Bounding by the smaller of the two one-cycle-count classes gives

```text
beta_+(d) <= (k - 1 + d)/2.
```

Compared with the desired one-sided target `beta_+(d) <= eta d/2`, this crude
bound closes only

```text
d >= (k - 1)/(eta - 1).
```

For the critical `eta=2` target, it controls `d >= k-1`; topology is still
needed for the lower one-sided defect densities.  The script
`one_sided_cycle_frontier.py` prints this comparison.

There is also a useful merger/genus balance form.  Write

```text
M = r - c(pi),
G_ns = sum_{non-singleton components} g_+.
```

Combining the labelled SET decomposition with the standard connected map
estimate `exp(O(t)) t! t^(3g_+)` gives the leading benchmark

```text
beta_+ <= M/r + 3G_ns/r.
```

The critical `eta=2` one-sided target asks for `beta_+ <= delta_+/r`; on the
non-singleton part this is `2(M+G_ns)/r`, so this map/SET benchmark closes the
balanced region

```text
G_ns <= M.
```

Singleton components may have positive one-sided genus, but they form only a
finite one-block class and contribute `exp(O(r))`, not `r log r`, so their
genus is harmless at the leading entropy scale.  Together with the one-sided
cycle-count edge, the remaining benchmark gap is

```text
G_ns > M
and
delta_+/(2r) < (k-1)/2.
```

The scripts `one_sided_balance_frontier.py` and `connected_balance_sanity.py`
record this precise region.  On the exact `k=4,r<=3` connected bidefect table,
there are no open non-singleton rows; the only benchmark-open connected rows
are one-block finite-type components.

For a connected non-singleton component on `t` blocks the integer form is even
sharper.  Since `M=t-1`, a benchmark-open component would need

```text
g_+ >= t
and
(t-1+g_+)/t < (k-1)/2.
```

For `k=4` this interval is empty for every `t`: it would require
`g_+ >= t` and `g_+ < t/2+1`.  Thus the one-sided balance plus cycle-count
benchmarks give a purely algebraic explanation for why no open non-singleton
rows appear in the exact `k=4` connected table.  For `k=6`, open connected
ranges already appear, starting at `t=2`, `2 <= g_+ <= 3`.  The script
`one_sided_integer_open_ranges.py` prints these ranges.

The exact compiled enumerator `two_block_open_exact.cpp` confirms that these
first `k=6,t=2` open ranges are populated, not merely sampled: among the
`478483200` connected two-block permutations, the `g_+=2` and `g_+=3`
benchmark-open rows have counts `120689352` and `220048920`.  This is not a
proof or disproof of CL, but it identifies the first concrete component class
that a complete all-even argument must control.

The same exact run with `--bidefect` shows that this finite class is genuinely
two-sided.  The largest row is balanced,

```text
(g_+,g_-)=(3,3),    count = 113801916,
```

and the open-open quadrant `g_+,g_- in {2,3}` contains `264203094` of the
`478483200` connected two-block permutations.  Thus the finite warning sign is
not a one-sided artifact.  Since `t=2` is fixed, it is still finite-type data;
its role is to identify the balanced bidefect patterns that an unbounded
component-size proof must control.

There is an important correction to the interpretation of these first open
rows.  If the catalogue of allowed connected component types has block size
bounded independently of the global number of blocks `r`, then the labelled SET
decomposition contributes only the set-partition entropy

```text
beta_+ = M/r
```

at the leading `r log r` scale.  The internal genera of those fixed component
types contribute only `exp(O(r))`.  For a fixed connected type with `t` blocks
and one-sided genus `g_+`, the finite-type leading margin against the critical
`eta=2` one-sided target is

```text
(t-1)/t - 2(t-1+g_+)/t < 0.
```

The script `finite_type_frontier.py` prints this comparison.  For `k=6` and
`t<=12`, every benchmark-open bounded component row has negative finite-type
margin; the worst is already the first row `t=2,g_+=2`, with margin `-2.5`.
Thus the exact `k=6,t=2` rows are a real warning about the crude
`t^(3g_+)` map/genus benchmark, but not by themselves a diagonal obstruction.
The remaining all-even danger must involve connected component sizes growing
with `r`, or a different entropy source not captured by the finite-catalogue
SET estimate.

The script `eta_requirement_table.py` separates the two eta thresholds in that
unbounded-component regime.  For one connected component with `t -> infinity`
and `y=g_+/t`, the one-sided target compares

```text
1 + eta y <= 2(1+y).
```

In the benchmark-open window, `y>1` and `y<(k-3)/2`.  Hence the worst
one-sided ceiling is `eta <= 2+2/(k-3)`, so the `eta=2` one-sided target is not
the leading obstruction in that local window.  The stricter number is the
direct full-CL component threshold

```text
eta_crit(k) = (k^2 - 3k + 1)/(k^2 - 4k + 1),
```

coming from the mixture of non-singleton components with one-block active
components and the three-cycle-count envelope.  The first values are:

| k | open `y=g_+/t` window | one-sided eta ceiling | direct `eta_crit(k)` |
|---:|---|---:|---:|
| 4 | empty | none | 5 |
| 6 | `1<y<1.5` | 2.66666666667 | 1.46153846154 |
| 8 | `1<y<2.5` | 2.4 | 1.24242424242 |
| 10 | `1<y<3.5` | 2.28571428571 | 1.16393442623 |
| 12 | `1<y<4.5` | 2.22222222222 | 1.12371134021 |

Thus the all-even obstruction is not merely "prove eta two" locally.  A direct
component-count proof of the full CL threshold would need a degree-dependent
effective exponent at or below `eta_crit(k)`, or a different global
two-sided/bidefect estimate.

The script `bidefect_local_threshold.py` gives the same requirement in local
two-sided variables.  Put

```text
s=(g_+ + g_-)/t,      alpha_local = 4+2s.
```

If a connected bidefect count had the leading form

```text
exp(O(t)) t! t^{eta (g_+ + g_-)},
```

then the local entropy would be `1+eta s`.  Compatibility with the full CL
threshold asks for

```text
1+eta s <= (k/(k+1))(1+alpha_local/2).
```

The three-cycle-count envelope takes over after `alpha_local` reaches
`cycle_crossing_alpha(k)`, so the relevant endpoint is
`s_cycle=(cycle_crossing_alpha(k)-4)/2`.  For `k=6`,

| `s` | `alpha_local` | allowed eta | margin at eta `2` |
|---:|---:|---:|---:|
| 1.5 | 7 | 1.90476190476 | 0.142857142857 |
| 2 | 8 | 1.64285714286 | 0.714285714286 |
| 2.5 | 9 | 1.48571428571 | 1.28571428571 |
| 2.6 | 9.2 | 1.46153846154 | 1.4 |

Thus even a total-bidefect `eta=2` estimate would not close the direct
component route for `k=6`; the required endpoint value is `eta=19/13`.

The total-bidefect route is not the only natural use of the one-sided map
estimate.  A fixed bidefect class is an intersection of a plus-genus class
and a minus-genus class, so a one-sided estimate

```text
count(t,g) <= exp(O(t)) t! t^(eta_min g)
```

implies the two-sided min-genus envelope

```text
count(t,g_+,g_-) <= exp(O(t)) t! t^(eta_min min(g_+,g_-)).
```

At fixed `s=(g_+ + g_-)/t`, the worst case for this bound is balanced, giving

```text
beta_local <= 1 + eta_min s/2.
```

The script `bidefect_min_genus_threshold.py` compares this envelope with the
same local CL threshold.  With the standard Chapuy exponent `eta_min=3`, it
closes the whole pre-cycle window for `k=4`, and for `k=6` it closes

```text
s <= 2.44444444444
```

leaving only

```text
2.44444444444 < s < 2.6
```

before the cycle-count envelope takes over.  This is a sharper proof target
than the total-bidefect route, but it still does not settle all even `k`:
already for `k=8`, the same calculation leaves

```text
2.72727272727 < s < 4.71428571429.
```

Equivalently, the required endpoint exponent on `min(g_+,g_-)` is `38/13`
for `k=6`, `82/33` for `k=8`, and tends down to `2` as `k` grows.

The integer lattice left by this comparison is quite sparse for `k=6`.
The script `bidefect_remaining_lattice.py` lists candidate rows that satisfy
both

```text
4 + 2(g_+ + g_-)/t < 9.2
```

and

```text
1 + 3 min(g_+,g_-)/t
  > (6/7)(3 + (g_+ + g_-)/t).
```

Through `t<=20`, the first such candidate is exactly

```text
(t,g_+,g_-) = (4,5,5).
```

The worst listed candidate is `(17,22,22)`, with leading alpha
`9.17647058824` and margin `0.0924369747899`.  This lattice calculation is
not an existence theorem for those bidefect rows; it only identifies the rows
not yet covered by the current analytic envelopes.

For `k=6` this lattice has a particularly simple exact form.  With
`g_+<=g_-`, the remaining conditions are precisely

```text
5(g_+ + g_-) < 13t,
15g_+ - 6g_- > 11t.
```

The balanced subfamily is therefore

```text
g_+=g_-=g,
11/9 < g/t < 13/10.
```

The script `k6_remaining_arithmetic.py` records this rational strip.  Through
`t<=20`, it gives `15` remaining candidate rows, `14` balanced; through
`t<=40`, it gives `86` rows, `60` balanced.  The first non-balanced row up to
`t=20` is `(t,g_+,g_-)=(19,24,25)`.

The balanced interval has length

```text
(13/10 - 11/9)t = 7t/90,
```

so every `t>=13` has at least one balanced lattice candidate.  This proves
that the remaining `k=6` candidate lattice is infinite at the arithmetic
level; it does not prove that the corresponding connected bidefect classes
are populated with enough entropy to matter on the diagonal.

The entropy threshold on this strip is explicit.  If

```text
count(t,g,g)=exp((beta+o(1))t log t),
```

then the balanced row can threaten CL only if

```text
beta > (6/7)(3+2g/t).
```

On the rational strip, this required exponent is about `4.67` to `4.80`.
The current min-genus envelope `beta <= 1+3g/t` exceeds the threshold by at
most about `0.1` in the sampled range through `t<=40`.  Thus the remaining
`k=6` question is not whether the strip exists; it is whether the connected
count along the strip has that much `t log t` entropy.

The finite population sampler gives mixed small-`t` evidence.  At `t=4`, the
balanced row `(g,g)=(5,5)` has `408` hits in `50000` samples, giving a finite
beta estimate `9.01255528583`, well above the local threshold.  At `t=7`, the
row `(9,9)` has only `4` hits in `500000` samples, still yielding beta
estimate `7.78451831653` but with high sampling variance.  At `t=8`, the row
`(10,10)` has no hit in `500000` samples.  This is useful stress evidence, not
a diagonal conclusion.

Targeted local search changes the finite-existence picture.  A transposition
walk optimizing the two cycle-sum constraints finds connected balanced-strip
witnesses at `t=8,11,12,13`, with cycle-count triples

```text
(16,6,6), (20,9,9), (22,10,10), (25,10,10),
```

respectively for `(#pi,#(gamma*pi),#(pi*gamma^{-1}))`.  Thus the uniform
sampler's `t=8` miss was a sampling limitation, not evidence of emptiness.
The extended strip sweep

```bash
python3 cl_probe/k6_balanced_strip_target_sweep.py \
  --t-min 13 --t-max 40 --restarts 4 --steps 20000 --seed 424242
```

finds connected witnesses in all `55` balanced candidate rows it searches.
This includes the previous worst finite entropy-room row `(t,g)=(37,48)`.
Thus the remaining `k=6` strip is populated throughout the tested arithmetic
frontier.  The tracked file
`k6_balanced_strip_witnesses_t13_t40.csv` stores the corresponding permutation
images, and

```bash
python3 cl_probe/k6_balanced_strip_certificates.py \
  --verify cl_probe/k6_balanced_strip_witnesses_t13_t40.csv
```

checks them deterministically by recomputing cycle counts, defects, genera,
and connectedness.  The entropy question remains untouched: witnesses are not
counts.

The same certificates also have a deterministic one-swap local-neighborhood
profile.  The command

```bash
python3 cl_probe/k6_balanced_strip_neutral_moves.py \
  cl_probe/k6_balanced_strip_witnesses_t13_t40.csv
```

enumerates every image-swap around each stored witness.  Across the `55`
certified rows, the number of connected swaps staying in the same balanced
row ranges from `222` to `1599`, with median `638`; the density among all
single image-swaps ranges from about `0.0256` to `0.107`.  Thus the witnesses
are not isolated points in their rows.  But this remains only polynomial local
neighborhood data: the largest value of
`log(neutral_degree)/(t log t)` in this profile is about `0.162`, while a CL
threat on the strip would need a row-count exponent about `4.67--4.80`.

The certified rows also show that the strip is not represented by one rigid
cycle-count split.  In the shape profile

```bash
python3 cl_probe/k6_balanced_strip_shape_profile.py \
  cl_probe/k6_balanced_strip_witnesses_t13_t40.csv
```

the forced equality

```text
#pi + #(gamma*pi) = #pi + #(pi*gamma^{-1}) = 5t+2-2g
```

is split with `#pi/t` ranging from about `1.71` to `2.10`, and
`#(gamma*pi)/t` ranging from about `0.45` to `0.87`.  The side products
typically have a macroscopic largest cycle: median largest-cycle fractions are
about `0.268` and `0.273` for `gamma*pi` and `pi*gamma^{-1}`, compared with
about `0.079` for `pi`.  A future count therefore has to control a broad
family of side-cycle shapes, not just one template.

Refining by the actual cycle-count split narrows the danger further.  For a
balanced row, write

```text
p=#pi,    q=#(gamma*pi)=#(pi*gamma^{-1}).
```

The row condition gives `p+q=5t+2-2g`, while the three-cycle-count envelope at
fixed `(p,q,q)` gives

```text
beta <= 6 - max(p,q)/t.
```

Thus the split is still strictly open only when

```text
max(p,q) < 12(2t-g)/7.
```

The calculator

```bash
python3 cl_probe/k6_balanced_split_window.py --t-min 13 --t-max 40 \
  --certificates cl_probe/k6_balanced_strip_witnesses_t13_t40.csv
```

finds only `12` strict-open balanced rows and `3` boundary rows through
`t=40`.  The first strict-open split is the exactly balanced slot
`(t,g,p,q)=(22,27,29,29)`.  None of the certified witnesses hits a strict-open
split; their `max(p,q)` is already large enough for the split-refined
cycle-count envelope to close them.  Consequently, the live `k=6` obstruction
is not "the balanced strip" as a whole, but the much narrower question of
whether these near-balanced cycle-count split slots are populated with large
entropy.

A bounded direct search of those strict split slots does not currently
populate them.  Running

```bash
python3 cl_probe/k6_balanced_split_target_search.py \
  --t-min 13 --t-max 40 --seed 20260617 --restarts 4 --steps 15000
```

targets the `17` strict split triples through `t=40`.  It finds no exact hit;
the best score is `2` for `11` of the `17` targets.  The first strict target
`(22,27,29,29)` gets as close as the connected triple `(29,27,29)`.  This is
finite heuristic evidence only.  It does, however, make the next mathematical
question extremely concrete: either construct permutations in the strict
near-balanced split slots, or prove that these slots are empty or too sparse.

The strict split-slot lattice is infinite at the arithmetic level.  For a
balanced ratio `y=g/t`, the continuous number of strict splits at that row is

```text
(13 - 10y)t/7.
```

After summing over `11/9<y<13/10` and over `t<=T`, this gives

```text
strict rows  ~ (7/180) T^2,
strict slots ~ (7/4860) T^3.
```

The script

```bash
python3 cl_probe/k6_balanced_split_asymptotics.py
```

checks the finite arithmetic ratios.  This does not count permutations.  Its
role is narrower: it rules out the comforting possibility that the strict
near-balanced split slots are only a bounded small-`t` artifact.

The first cheap invariant check is negative.  The sign relation forced by
`sign(gamma*pi)=sign(gamma)sign(pi)` is

```text
q-p == t  mod 2.
```

All strict arithmetic slots through `t<=80` satisfy it.  The existing
target-search misses through `t<=40` are also not random-looking: most best
near-hits have score `2`, with exactly one of `#pi`, `#(gamma*pi)`, or
`#(pi*gamma^{-1})` short by `2`.  Plain parity is therefore not the missing
obstruction.

Moreover, the strict split window is not empty at finite size.  After saving
the best miss permutations from the bounded target search, a deterministic
one-swap neighborhood profile finds one zero-score neighbor.  This gives a
connected strict-slot witness at

```text
(t,g,p,q)=(39,48,50,51),
```

with

```text
#pi=50,
#(gamma*pi)=#(pi*gamma^{-1})=51,
g_+=g_-=48.
```

Since `51 < 360/7`, the witness lies strictly inside the split-open region.
Thus the next deterministic question is no longer mere emptiness.  It is
whether these strict near-balanced split slots have subcritical entropy, or
whether a constructive family populates them at a threatening `t log t` scale.

Following strict score-improving one-swaps from all saved near-hits through
`t<=40` finds no additional strict witness.  The same `(39,48,50,51)` target
reaches score zero in one step, two `t=40` targets descend to score `2`, and
the rest are already one-swap local minima for this score.  This is still only
finite local evidence, but it points to score-2 local traps as the concrete
object to explain.

There is also a constructive finite extension.  Starting from the
`(39,48,50,51)` witness, keep the old permutation, add one new six-point
block, and swap the image of old domain `0` with the image of new domain
`234`.  With four different internal permutations of the new block, this
constructs all strict split targets at `t=40`:

```text
(40,49,51,53),
(40,49,52,52),
(40,49,53,51),
(40,50,51,51).
```

So the strict split witness is not merely a single accidental point.  The next
real question is whether this add-a-block bridge can be iterated, and if so
how many independent choices it leaves.  That is exactly the entropy issue;
the current construction gives finite propagation evidence, not a diagonal
count.

The first iteration tests are positive.  With the fixed bridge
`0:new_block_start`, varying only the new block's internal permutation
propagates strict witnesses through `t=44`.  The tested chain hits every
strict target slot at `t=41`, `t=42`, `t=43`, and `t=44`.  This strengthens
the constructive warning: the strict split branch has a visible growth
mechanism.  What remains unknown is its entropy.  A rigid single-choice chain
does not breach CL, but a version with enough independent choices at each
step might.

Counting all `6!` internal new-block permutations for the fixed bridge shows
that this is not literally single-choice: through `t=44`, positive
source-target pairs have between `5` and `130` working internal choices, and
the tested steps have `392`, `954`, `1674`, and `6996` total fixed-bridge
hits.  This is still bounded branching for the particular bridge
`0:new_block_start`; by itself it gives at most exponential-in-`t` growth, not
the `t log t` entropy needed for a CL breach.  The natural next target is to
count how many bridge locations, not just internal block permutations, can be
chosen independently.

A representative bridge-location count finds a polynomial factor at one step:
for the `t=41 -> t=42` propagation from source `(41,51,53,52)` to target
`(42,52,54,54)`, with first new-domain offset fixed, all `6*41=246` old
domains work, and each has `114` internal block choices.  Thus the mechanism
has at least a visible `O(t)` bridge-location multiplicity in this sample.
The unresolved issue is whether such bridge choices remain independent across
many growth steps.  That independence, not finite existence, is now the
entropy-critical point.

Extending the same sample to all six new-domain offsets, all `1476` old/new
bridge pairs work and each still has `114` internal choices.  If a comparable
bridge-location choice were available independently at each step, it would
produce a `t!`-scale factor, contributing one unit of `t log t` entropy.  The
strict strip needs roughly `4.7--4.8` units, so this bridge factor is important
but not sufficient by itself.

A two-step sample supports, but does not prove, independence of the bridge
choice.  Four different old bridge-domain choices in the `t=41 -> t=42` step
were materialized as `t=42` witnesses.  For each of them, all `252` old domains
work in the next `t=42 -> t=43` step toward one strict target, again with
`114` internal choices each.  This makes the possible `t!` bridge factor more
credible, while still leaving the actual induction and any further entropy
sources unproved.

The first remaining row is populated.  The script
`bidefect_witness_search.py` finds a connected `k=6,t=4` permutation with

```text
(g_+,g_-)=(5,5),
```

and verification data

```text
#pi=9,   #(gamma*pi)=3,   #(pi*gamma^{-1})=3.
```

Equivalently, its plus and minus defects are both `16`, so its exact finite
component density is `8` and its leading asymptotic density is `9`.  This is
only a finite witness, but it confirms that the first row left by the current
envelopes is not vacuous.

A uniform-sampling sweep through the remaining `k=6` candidate rows with
`t<=12` finds
another populated row,

```text
(t,g_+,g_-)=(7,9,9),
```

with `#pi=11`, `#(gamma*pi)=8`, and `#(pi*gamma^{-1})=8`.  The same sweep does
not find witnesses for `(8,10,10)`, `(11,14,14)`, or `(12,15,15)` within
`100000` samples each, and a separate one-million-sample search does not find
`(8,10,10)`.  These misses are not emptiness proofs; they only say that the
uniform finite witness evidence is sparse.  The targeted sweep above shows
that direct cycle-sum search has no trouble finding witnesses in those rows.

The sampler `connected_bidefect_sampler.py` probes this local window at finite
component size.  It now reports both the exact finite component density
`alpha_exact=E/t` and the asymptotic leading density
`alpha_leading=4+2(g_++g_-)/t`.  The distinction matters: the exact finite
density contains a `-4/t` correction, while the unbounded-component frontier is
expressed in the leading coordinate.  For `k=6`, the cycle-count crossing is
at leading local alpha `9.2`, so larger leading-alpha rows are already in the
range where the three-cycle-count envelope has taken over.

The largest sampled rows by frequency at `t=4` and `t=6` are balanced but
post-cycle:

| t | `(g_+,g_-)` | exact alpha | leading alpha | sampled leading margin |
|---:|---|---:|---:|---:|
| 4 | `(7,7)` | 10 | 11 | 3.96977619 |
| 6 | `(12,12)` | 11.3333333 | 12 | 2.72219662 |

With `min_hits=20`, the `t=4` run has one supported asymptotic pre-cycle
headline row:

| t | `(g_+,g_-)` | exact alpha | leading alpha | sampled leading margin |
|---:|---|---:|---:|---:|
| 4 | `(5,5)` | 8 | 9 | 4.29826957 |

The `t=6` run has no supported asymptotic pre-cycle row at `min_hits=20`; the
row `(g_+,g_-)=(9,8)` has exact alpha `9` but leading alpha `9.66666667`, so
it is post-cycle for the asymptotic local problem.

These are Monte Carlo finite-size diagnostics, not asymptotic estimates.  They
do, however, sharpen the structural message from the exact two-block data:
the unresolved finite-data warning is genuinely two-sided/bidefect.  It still
requires an asymptotic count for growing component size; the sampler alone
does not prove or disprove CL.

## 5. Component/cycle benchmark for `k=4`

The connected-component decomposition gives one more useful reduction in the
remaining `k=4` window.  A one-block active component has energy at least `2`.
A connected component using `t >= 2` blocks has `j=t-1`, hence

```text
E = 4(t-1) + 2h >= 4t - 4.
```

Thus any macroscopic non-singleton component has local energy density at least
`4`.  For total proportional energy `2 <= alpha <= 4`, at most an
`(alpha-2)/2` fraction of the blocks can belong to macroscopic non-singleton
components if the remaining blocks sit at one-block energy `2`.

On each such macroscopic component, the three-cycle-count envelope for `k=4`
gives local entropy density at most

```text
3/2 + 4/4 = 5/2
```

at the lowest possible local energy density `4`.  Bounded-size non-singleton
components contribute only the usual label-partition exponent, which is no
larger than their merge density and is dominated by the same estimate.  Hence,
for `2 <= alpha <= 4`, the component/cycle benchmark is

```text
beta_4(alpha) <= (5/4)(alpha - 2).
```

Comparing with the CL threshold

```text
4/5 + (2/5) alpha
```

shows that this closes

```text
2 <= alpha <= 66/17.
```

The earlier three-cycle-count envelope closes

```text
alpha >= 14/3.
```

Therefore the unresolved `k=4` proportional window is reduced to

```text
66/17 < alpha < 14/3.
```

This is still a paper-level benchmark, not a Lean formalization.  The scripts
`connected_spectrum.py` and `component_frontier.py` provide exact small-`r`
checks and print this frontier.

## 6. Conditional map/genus component optimizer for `k=4`

The previous component/cycle benchmark is deliberately crude near local
component energy density `4`: it pays the connected planar component by the
three-cycle-count envelope.  A sharper theorem-facing input is the standard
map/genus shape

```text
connected_count(t,h) <= exp(O(t)) t! t^(3h),
```

for connected non-singleton `k=4` components on `t` labelled blocks and genus
`h`.  This is the form supplied by planar map counts plus Chapuy slicing; the
reference-based proof packet is `CL_connected_map_genus_bound.md`.

If this estimate holds, then a connected component of local energy density
`a >= 4` has leading entropy

```text
beta_map(a) <= 1 + (3/2)(a - 4),
```

because `h/t = (a-4)/2` at leading order.  We can also use the cycle-count
envelope on the same component:

```text
beta_cycle(a) <= 3/2 + a/4.
```

Thus the local component cost is bounded by

```text
min(1 + (3/2)(a - 4), 3/2 + a/4).
```

If a fraction `q` of all blocks belongs to non-singleton components and the
remaining blocks are one-block active components at energy density `2`, then

```text
alpha = 2 + q(a - 2),
beta  <= q min(1 + (3/2)(a - 4), 3/2 + a/4).
```

Optimizing in `a` gives the exact local maximizer

```text
a_* = 26/5,
```

where the two local bounds meet.  Thus the conditional envelope is

```text
beta_4(alpha) <= (7/8)(alpha-2),        2 <= alpha <= 26/5,
beta_4(alpha) <= 3/2 + alpha/4,         alpha >= 26/5.
```

Compared with the CL threshold `4/5 + (2/5)alpha`, the margins are

```text
(19/40)alpha - 51/20,        2 <= alpha <= 26/5,
7/10 - (3/20)alpha,          alpha >= 26/5.
```

On the remaining `k=4` window `66/17 < alpha < 14/3`, the exact worst margin
is therefore `-1/3`, attained at the upper endpoint `alpha=14/3`.  On the
whole central interval `2 <= alpha <= 8`, the exact worst margin is `-2/25`,
attained at `alpha=26/5`.  Therefore:

```text
connected_count(t,h) <= exp(O(t)) t! t^(3h)
  + the existing cycle-count envelope
  => k=4 proportional-band CL target.
```

This closes the `k=4` proportional-band target at paper level, using the
external rooted-map enumeration and Chapuy-slicing supplier recorded in
`CL_connected_map_genus_bound.md`.  It is not a Lean formalization and it does
not by itself close all even `k`.

## 7. Why the same map/genus transplant does not close all `k`

The direct degree-`k` analogue of the preceding component calculation is useful
as a stress test.  Suppose connected non-singleton degree-`k` components on
`t` labelled blocks and total genus parameter `h` obey

```text
connected_count_k(t,h) <= exp(O(t)) t! t^(3h).
```

The map/genus local envelope is still

```text
beta_map(a) <= 1 + (3/2)(a - 4),
```

while the three-cycle-count local envelope is now

```text
beta_cycle,k(a) <= (k - 1)/2 + a/4.
```

The two local lines meet at

```text
a_k = (2k + 18)/5.
```

At this point the direct component envelope has value

```text
beta_k(a_k) <= (3k + 2)/5,
```

whereas the CL threshold is

```text
(k/(k+1)) (1 + a_k/2) = k(k+14)/(5(k+1)).
```

The margin is therefore

```text
(3k + 2)/5 - k(k+14)/(5(k+1))
  = (2k^2 - 9k + 2)/(5(k+1)).
```

This is negative for `k=4` but positive already for `k=6`.  Thus the standard
`t^(3h)` map/genus component supplier is enough to close the remaining `k=4`
window, but it is not enough to settle the all-even CL lemma.  The script
`k_map_genus_frontier.py` prints this obstruction.

More generally, if the connected component estimate had genus exponent `eta`,
so that

```text
connected_count_k(t,h) <= exp(O(t)) t! t^(eta h),
```

then the local map/genus and cycle-count lines meet at

```text
a_k(eta) = (2k - 6 + 8 eta)/(2 eta - 1).
```

The component strategy closes the central range precisely when this crossing
lies at or to the right of the cycle-count/CL-threshold crossing

```text
alpha_cycle(k) = (2k^2 - 4k - 2)/(k - 1).
```

Equivalently, for `k >= 4`, this direct component strategy would need

```text
eta <= eta_crit(k)
    := (k^2 - 3k + 1)/(k^2 - 4k + 1).
```

The threshold is `eta_crit(4)=5`, `eta_crit(6)=19/13`, and tends to `1` as
`k -> infinity`.  Hence the all-even route cannot rely merely on the standard
Chapuy exponent `3`; it would need either a much sharper effective component
count, a global one-sided genus count without the extra component-label
entropy, or a different two-sided estimate.

## 8. Exact `k=2` character formula

For `k=2`, let `n = 2r` and let `gamma` be a fixed perfect matching, i.e. a
permutation of cycle type `(2^r)`.  The exact extractor computes the polynomial

```text
T_r(x,y) = sum_{pi in S_n} x^{#pi} y^{#(gamma pi)}.
```

The implementation uses the Jucys--Murphy content identity

```text
sum_{sigma in S_n} x^{#sigma} chi_lambda(sigma)
  = f^lambda prod_{u in lambda} (x + c(u)),
```

where `f^lambda` is the Specht dimension and `c(u)` is the content of the box
`u`.  If

```text
A_lambda(x) = f^lambda prod_{u in lambda} (x + c(u))
             = sum_p A_{lambda,p} x^p,
```

then the coefficient formula implemented by
`total_polynomial_for_r` is

```text
[x^p y^q] T_r(x,y)
  =
  1 / ((2r)!)^2
  sum_{lambda |- 2r}
    chi_lambda(2^r) ((2r)!/f^lambda)
    A_{lambda,p} A_{lambda,q}.
```

This formula is exact; it is the source of the `r<=28` table.

## 9. Connected and active extraction

The active condition is not imposed directly on `T_r`.  The extractor first
uses the labelled exponential formula.

Let

```text
T(z;x,y) = sum_{r>=0} T_r(x,y) z^r/r!.
```

Then

```text
C(z;x,y) = log T(z;x,y)
```

extracts connected components for the group generated by `gamma` and `pi`.
The active spectrum is obtained by deleting the size-one connected component
and exponentiating again, now keeping a marker for the number of active
components.

In the notation of the code, an active term has

```text
r          = number of matching blocks,
c          = number of active connected components,
p          = #pi,
q          = #(gamma pi),
j          = r - c,
h          = r - p - q + 2c,
E          = 4j + 2h = 6r - 2p - 2q.
```

Thus, for `k=2`, bounding `N_r(E)` is equivalent to bounding the aggregate
coefficients of the active exponential transform of the character polynomial
on the diagonal

```text
p + q = 3r - E/2.
```

## 10. What would prove CL for `k=2`

A sufficient analytic theorem is:

```text
For every alpha in the relevant energy range,
limsup_{E/r -> alpha} log N_r(E)/(r log r)
  <= 2/3 + alpha/3,
```

with a uniform version strong enough to control the supremum over all energies
in (CL').  A strict gap away from a finite exceptional set would be more than
enough; the finite exceptional bands can be handled separately by fixed-excess
estimates.

The exact data through `r=28` are compatible with this condition.  The current
finite stress audit reports:

```text
fixed-excess best G/a_d              < 0,
empirical proportional max margin    < 0,
central-window max margin            < 0,
tail-window max margin               < 0,
proportional-ray fitted max margin   < 0,
held-out ray backtest max prediction < 0.
```

The three-cycle-count envelope above proves this leading `limsup` target for
`k=2`.  The exact finite diagnostics remain useful as validation and as a
guard against undercounting, but they are no longer the only evidence at the
proportional-band level.

## 11. Plausible proof routes

Any proof of the beta-surface bound must control the active coefficient
growth after the connected-component transform.  Possible routes are:

1. **Character asymptotics.**  Bound the character sum above using asymptotics
   for `chi_lambda(2^r)`, Specht dimensions, and the content polynomial
   coefficients.

2. **Bivariate analytic combinatorics.**  Treat the connected transform
   `log T(z;x,y)` and active exponential transform as coefficient-extraction
   problems, then derive a uniform saddle bound for the diagonal
   `p+q = 3r - E/2`.

3. **Map/constellation enumeration.**  Identify the active connected objects
   as the corresponding bipartite-map/constellation class and use known
   topological-recursion or genus-growth bounds to control the aggregate
   energy bands.

4. **Hybrid finite-plus-asymptotic bound.**  Use exact computation to isolate
   the low and moderate `r` regime, and prove a coarse but uniform asymptotic
   inequality for large `r`.

The current computational work supplies exact data and stress tests.  The
remaining mathematical frontier is the uniform entropy bound above.
