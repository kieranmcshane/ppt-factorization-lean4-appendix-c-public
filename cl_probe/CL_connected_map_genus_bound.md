# Connected map/genus bound for the k=4 frontier

This note records the exact theorem-facing input that closes the remaining
`k=4` proportional window in `CL_analytic_frontier.md`, once the standard
rooted-map enumeration estimates are admitted as external references.

It is a paper-level proof packet, not a Lean formalization.

## Target statement

Let `C_4(t,h)` be the number of connected non-singleton `k=4` active
components on `t` labelled original blocks with

```text
E = 4(t-1) + 2h.
```

The needed bound is the following.

**Proposition.**  There are constants `A,B < infinity` such that for all `t`
and `h`,

```text
C_4(t,h) <= exp(O(t)) t! t^(3h).
```

Equivalently, at leading `t log t` scale,

```text
log C_4(t,h) / (t log t) <= 1 + 3h/t + o(1).
```

This is precisely the input consumed by `k4_map_genus_frontier.py`.

## Hypermap translation

Fix

```text
gamma = (0 1 2 3)(4 5 6 7)...(4t-4 4t-3 4t-2 4t-1).
```

A connected component is a permutation `pi` of the `4t` darts for which
`<gamma,pi>` acts transitively.  The pair `(gamma,pi)` is an orientable
hypermap:

- black vertices are the cycles of `gamma`, hence there are `t` labelled
  black vertices, each of degree `4`;
- white vertices are the cycles of `pi`;
- plus-faces are the cycles of `gamma*pi`.

The plus Euler characteristic is

```text
t + #pi + #(gamma*pi) - 4t = 2 - 2g_+.
```

Thus

```text
delta_+ = 4t + t - #pi - #(gamma*pi)
        = 2(t-1) + 2g_+.
```

The same construction with the opposite face permutation gives

```text
delta_- = 2(t-1) + 2g_-.
```

Therefore, for a connected component,

```text
E = delta_+ + delta_-
  = 4(t-1) + 2(g_+ + g_-).
```

So the parameter `h` in the target statement is `h=g_+ + g_-`.

## Counting reduction

It is enough to count by the plus genus alone.  If `g_+ <= h`, then the
component is included in the class of connected bipartite maps of genus `g_+`
with `t` labelled black vertices of degree `4`, arbitrary white degrees, and
the local cyclic orders fixed by `gamma`.

Let `M(t,g)` denote this plus-side map count.  The required bound follows from

```text
M(t,g) <= exp(O(t)) t! t^(3g).
```

Indeed,

```text
C_4(t,h) <= sum_{0 <= g <= h} M(t,g)
          <= exp(O(t)) t! t^(3h),
```

because `h <= 2t+O(1)` in the central window and the finite sum contributes
only another exponential factor.

## Map/genus estimate

The estimate for `M(t,g)` follows from the standard planar-map base count
plus Chapuy slicing.

1. Planar base:

   ```text
   M(t,0) <= A^t t!
   ```

   for an absolute constant `A`.  This is a coarse consequence of planar
   bipartite map enumeration: after rooting and forgetting the degree
   restrictions, the number of planar rooted maps with `O(t)` edges is
   exponential in `t`.  The factor `t!` labels the degree-four black vertices;
   fixed cyclic orders, rooting choices, and the forgetting/rooting maps cost
   only `exp(O(t))`.

2. Slicing step:

   ```text
   M(t,g) <= B t^3 M(t,g-1)
   ```

   for an absolute constant `B`.  Chapuy's trisection/slicing operation lowers
   genus by one after marking a bounded amount of local data.  Conversely, to
   reconstruct genus `g`, choose three corners in a genus `g-1` map and glue
   them.  The number of corners is `O(t)`, so this costs `O(t^3)` choices,
   up to constants absorbed in `B`.  This is the same polynomial genus-loss
   mechanism behind the usual `n^{3g}` bounds for maps and unicellular maps.

Iterating the slicing step gives

```text
M(t,g) <= A^t t! (B t^3)^g
        <= exp(O(t)) t! t^(3g),
```

since `g=O(t)` in the relevant energy window.

## Consequence for CL

The conditional bound gives the local component entropy

```text
beta_map(a) <= 1 + (3/2)(a-4),
```

where `a` is local component energy density.  Combining this with the existing
cycle-count envelope

```text
beta_cycle(a) <= 3/2 + a/4
```

and optimizing over the non-singleton component fraction gives the exact
piecewise envelope recorded in `CL_analytic_frontier.md`:

```text
beta_4(alpha) <= (7/8)(alpha-2),        2 <= alpha <= 26/5,
beta_4(alpha) <= 3/2 + alpha/4,         alpha >= 26/5.
```

This sits below the CL threshold throughout the remaining `k=4` window.

Thus the connected map/genus estimate above supplies the paper-level
enumerative input for closing `k=4`.

## Status

- This is a pure-math, reference-based closure of the `k=4` Task-B input.
- It is not a Lean theorem.
- The constants are intentionally not optimized; any bound of the form
  `exp(O(t)) t! t^(3h)` is more than enough for the CL variational margin.
- The argument is specific to the connected `k=4` component class used in the
  current frontier.  It does not by itself settle all even `k`.

## References

- Guillaume Chapuy, *The structure of unicellular maps, and a connection
  between maps of positive genus and planar labelled trees*, Probability Theory
  and Related Fields 147 (2010), 415--447, arXiv:0804.0546.
- E. A. Bender and E. R. Canfield, *The asymptotic number of rooted maps on a
  surface*, Journal of Combinatorial Theory, Series A 43 (1986), 244--257.
- The slicing input used here is the standard consequence that genus can be
  lowered by cutting a trisection, with the inverse operation controlled by
  choosing three corners.
