import PptFactorization.AppendixB
import PptFactorization.AppendixBLevyPolarBridge
import PptFactorization.AppendixBSphericalLevy
import PptFactorization.HighProbabilityBounds
import PptFactorization.RandomMatrixModel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.HasLaw

/-!
# Appendix B spike exponent skeleton

This file formalises the conservative large-deviation statement discussed in
the Appendix B notes.

It does **not** prove the hard matrix-model upper large-deviation theorem and
it does **not** assert that the optimized local-Lipschitz upper speed is sharp
or false.  The theorems proved here are the logically safe exponent
bookkeeping:

if a favourable spike event has logarithmic cost

`log P(E_d(a)) ≥ -(lam a + o(1)) d^(2+2/k)`

for every `a > ε^(1/k)`, and this event is contained in the target deviation
event, then the deviation probability has the lower exponent

`liminf d^(-(2+2/k)) log p_d ≥ -lam ε^(1/k)`.

The formal statement records the conclusion in the equivalent eventual form: for every
`η > 0`, eventually

`-lam ε^(1/k) - η ≤ log p_d / d^(2+2/k)`.

The file also contains a purely conditional upper-bound wrapper: if, as an
extra hypothesis, the target probability itself satisfies

`log p_d ≤ -(lam ε^(1/k) - o(1)) d^(2+2/k)`,

then the wrapper gives the corresponding eventual limsup inequality.

No theorem in this file proves that upper large-deviation hypothesis for the
partial-transpose random-matrix model.  Consequently the matching limsup and
any exact large-deviation principle remain open/conditional here.
-/

namespace AppendixB

open Matrix MeasureTheory
open PptFactorization.RandomMatrixModel
open PptFactorization.HighProbabilityBounds
open PptFactorization.AppendixB
open Filter
open scoped BigOperators Matrix.Norms.Frobenius Pointwise ENNReal Topology

/-! ## Abstract exponent bookkeeping -/

/-- Abstract input for a spike lower bound.

`p d` is the target deviation probability, `speed d` is the exponential speed,
`root` is the limiting spike mass parameter (in the concrete application,
`root = ε^(1/k)`), and `lam` is the aspect-ratio constant.

The field `favorable_event_lower` is the formal version of:
for every spike strength `a > root`, and every fixed logarithmic slack, the
favourable event gives a lower bound on `log p d` at cost `lam a`. -/
structure AbstractSpikeLowerBoundInput
    (p speed : ℕ → ℝ) (root lam : ℝ) : Prop where
  lambda_pos : 0 < lam
  speed_pos_eventually : ∀ᶠ d in atTop, 0 < speed d
  favorable_event_lower :
    ∀ a : ℝ, root < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          Real.log (p d) ≥ -(lam * a + slack) * speed d

/-- Eventual lower exponent obtained from the spike lower-bound inputs.

This is the formal liminf-style conclusion in an `Eventually` form: for every
`η > 0`, the normalized logarithmic probability is eventually at least
`-lam * root - η`. -/
theorem AbstractSpikeLowerBoundInput.eventual_log_over_speed_lower
    {p speed : ℕ → ℝ} {root lam : ℝ}
    (I : AbstractSpikeLowerBoundInput p speed root lam) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -(lam * root) - η ≤ Real.log (p d) / speed d := by
  intro η hη
  let a : ℝ := root + η / (4 * lam)
  let slack : ℝ := η / 4
  have hden_pos : 0 < 4 * lam := mul_pos (by norm_num) I.lambda_pos
  have ha : root < a := by
    dsimp [a]
    have hquot : 0 < η / (4 * lam) := div_pos hη hden_pos
    linarith
  have hslack : 0 < slack := by
    dsimp [slack]
    positivity
  have htail := I.favorable_event_lower a ha slack hslack
  filter_upwards [I.speed_pos_eventually, htail] with d hspeed hlog
  have hle : -(lam * a + slack) * speed d ≤ Real.log (p d) := by
    linarith
  have hdiv :
      (-(lam * a + slack) * speed d) / speed d ≤
        Real.log (p d) / speed d :=
    div_le_div_of_nonneg_right hle (le_of_lt hspeed)
  have hcancel :
      (-(lam * a + slack) * speed d) / speed d =
        -(lam * a + slack) := by
    field_simp [ne_of_gt hspeed]
  have hcost :
      lam * a + slack = lam * root + η / 2 := by
    dsimp [a, slack]
    field_simp [ne_of_gt I.lambda_pos]
    ring
  have hmain : -(lam * root) - η ≤ -(lam * a + slack) := by
    rw [hcost]
    linarith
  rw [hcancel] at hdiv
  exact le_trans hmain hdiv

/-! ## Beta interval lower bound for one column -/

/-- The second Beta shape parameter for one distinguished column in a
rectangular complex Hilbert--Schmidt sphere.

If the state space dimension is `N` and there are `s` sample columns, the
mass of one column has Beta parameters `(N, N*(s-1))`. -/
def betaColumnOtherShape (N s : ℕ) : ℕ :=
  N * (s - 1)

/-- Upper endpoint `(1 + δ) q` of the column-mass interval. -/
noncomputable def betaColumnIntervalUpper (q δ : ℝ) : ℝ :=
  (1 + δ) * q

/-- The elementary lower-bound kernel for the interval probability of
`R ~ Beta(N, N*(s-1))` on `[q, (1+δ)q]`.

The normalized integer-Beta density is

`C * r^(N-1) * (1-r)^(N*(s-1)-1)`

with `C ≥ 1`.  On the interval `[q, (1+δ)q]`, the factors are bounded below by
`q^(N-1)` and `(1-(1+δ)q)^(N*(s-1)-1)`, while the interval length is `δ q`.
Thus the lower kernel is

`δ * q^N * (1-(1+δ)q)^(N*(s-1)-1)`.

This definition is the finite-dimensional bound used by the column spike
lower bound.  The separate theorem below records the logarithmic consequence;
the proof that an actual column mass has this Beta law is intentionally kept as
a different obligation. -/
noncomputable def betaColumnIntervalKernel (N s : ℕ) (q δ : ℝ) : ℝ :=
  δ * q ^ N * (1 - betaColumnIntervalUpper q δ) ^
    (betaColumnOtherShape N s - 1)

theorem betaColumnIntervalKernel_pos
    {N s : ℕ} {q δ : ℝ}
    (hq : 0 < q) (hδ : 0 < δ)
    (hupper : betaColumnIntervalUpper q δ < 1) :
    0 < betaColumnIntervalKernel N s q δ := by
  unfold betaColumnIntervalKernel
  have hbase : 0 < 1 - betaColumnIntervalUpper q δ := by linarith
  positivity

/-- Finite lower-bound package for the interval probability of the one-column
Beta law.

`prob` is the actual interval probability

`P(q ≤ R ≤ (1+δ)q)`

for a random variable `R ~ Beta(N, N*(s-1))`.  The field `prob_lower` is the
standard density lower bound by `betaColumnIntervalKernel`.

This is deliberately not stated as a law-of-column theorem: the sphere-to-Beta
identification is a separate probabilistic input. -/
structure BetaColumnIntervalLowerBound
    (prob : ℝ) (N s : ℕ) (q δ : ℝ) : Prop where
  q_pos : 0 < q
  delta_pos : 0 < δ
  upper_lt_one : betaColumnIntervalUpper q δ < 1
  prob_lower : betaColumnIntervalKernel N s q δ ≤ prob

theorem BetaColumnIntervalLowerBound.kernel_pos
    {prob : ℝ} {N s : ℕ} {q δ : ℝ}
    (I : BetaColumnIntervalLowerBound prob N s q δ) :
    0 < betaColumnIntervalKernel N s q δ :=
  betaColumnIntervalKernel_pos I.q_pos I.delta_pos I.upper_lt_one

theorem BetaColumnIntervalLowerBound.prob_pos
    {prob : ℝ} {N s : ℕ} {q δ : ℝ}
    (I : BetaColumnIntervalLowerBound prob N s q δ) :
    0 < prob :=
  lt_of_lt_of_le I.kernel_pos I.prob_lower

/-- Logarithmic version of the finite Beta interval lower bound. -/
theorem BetaColumnIntervalLowerBound.log_kernel_le_log_prob
    {prob : ℝ} {N s : ℕ} {q δ : ℝ}
    (I : BetaColumnIntervalLowerBound prob N s q δ) :
    Real.log (betaColumnIntervalKernel N s q δ) ≤ Real.log prob :=
  Real.log_le_log I.kernel_pos I.prob_lower

/-- If the lower kernel has the desired logarithmic cost, then so does the
actual Beta interval probability. -/
theorem BetaColumnIntervalLowerBound.log_prob_ge_of_kernel_cost
    {prob : ℝ} {N s : ℕ} {q δ lower : ℝ}
    (I : BetaColumnIntervalLowerBound prob N s q δ)
    (hkernel : lower ≤ Real.log (betaColumnIntervalKernel N s q δ)) :
    lower ≤ Real.log prob :=
  le_trans hkernel I.log_kernel_le_log_prob

/-- Eventual transfer of the Beta interval kernel lower bound to a probability
sequence.

This is the exact interface needed for the one-column spike event: once the
column-mass interval probability is known to satisfy the integer-Beta interval
lower bound, and once the kernel has cost at most `lam * a` at the chosen
speed, the interval probability inherits the same logarithmic lower bound. -/
theorem eventual_log_lower_of_betaColumnInterval
    {prob speed : ℕ → ℝ} {N s : ℕ → ℕ} {q δ : ℕ → ℝ}
    {lam a slack : ℝ}
    (hBeta :
      ∀ᶠ d in atTop,
        BetaColumnIntervalLowerBound (prob d) (N d) (s d) (q d) (δ d))
    (hKernelCost :
      ∀ᶠ d in atTop,
        -(lam * a + slack) * speed d ≤
          Real.log (betaColumnIntervalKernel (N d) (s d) (q d) (δ d))) :
    ∀ᶠ d in atTop,
      Real.log (prob d) ≥ -(lam * a + slack) * speed d := by
  filter_upwards [hBeta, hKernelCost] with d hB hK
  exact hB.log_prob_ge_of_kernel_cost hK

/-- Elementary logarithmic lower bound used for the one-minus factor in the
Beta interval kernel:

`log(1-x) ≥ -x/(1-x)` for `x < 1`.

This is the finite-dimensional substitute for silently writing
`log(1-x) = -x + O(x^2)`. -/
theorem log_one_sub_ge_neg_div_one_sub
    {x : ℝ} (hx1 : x < 1) :
    -x / (1 - x) ≤ Real.log (1 - x) := by
  have hpos : 0 < 1 - x := by linarith
  have hinv_pos : 0 < (1 - x)⁻¹ := inv_pos.mpr hpos
  have hlog := Real.log_le_sub_one_of_pos hinv_pos
  have hlog_inv : Real.log ((1 - x)⁻¹) = -Real.log (1 - x) := by
    rw [Real.log_inv]
  have hsub : (1 - x)⁻¹ - 1 = x / (1 - x) := by
    field_simp [ne_of_gt hpos]
    ring
  rw [hlog_inv, hsub] at hlog
  have hneg := neg_le_neg hlog
  simpa [neg_div] using hneg

/-- Canonical one-column spike mass scale.

At large-deviation speed `speed = N^(1+1/k)`, the column-mass interval is placed
at

`q = a * speed / N^2`,

which is the same as `a * N^(-1+1/k)` when `speed = N^(1+1/k)`. -/
noncomputable def betaColumnSpikeScale (N speed a : ℝ) : ℝ :=
  a * speed / N ^ 2

/-- Finite logarithmic lower bound for the Beta interval kernel.

The kernel is

`δ * q^N * (1-(1+δ)q)^(N(s-1)-1)`.

This theorem separates its three logarithmic costs:

* the interval length `log δ`;
* the entropy term `N log q`;
* the one-minus term controlled by
  `log(1-x) ≥ -x/(1-x)`, with `x=(1+δ)q`.

It is the finite-dimensional core of the Beta-kernel asymptotics. -/
theorem betaColumnIntervalKernel_log_lower_of_cost_bounds
    {N s : ℕ} {q δ deltaCost qCost oneMinusCost : ℝ}
    (hq : 0 < q) (hδ : 0 < δ)
    (hupper : betaColumnIntervalUpper q δ < 1)
    (hDelta : -deltaCost ≤ Real.log δ)
    (hQ : -qCost ≤ (N : ℝ) * Real.log q)
    (hOneMinus :
      (((betaColumnOtherShape N s - 1 : ℕ) : ℝ) *
          betaColumnIntervalUpper q δ /
            (1 - betaColumnIntervalUpper q δ)) ≤ oneMinusCost) :
    -(deltaCost + qCost + oneMinusCost) ≤
      Real.log (betaColumnIntervalKernel N s q δ) := by
  let x : ℝ := betaColumnIntervalUpper q δ
  let m : ℕ := betaColumnOtherShape N s - 1
  have hbase : 0 < 1 - x := by
    dsimp [x]
    linarith
  have hqpow : 0 < q ^ N := pow_pos hq N
  have hbasepow : 0 < (1 - x) ^ m := pow_pos hbase m
  have hprod : 0 < δ * q ^ N := mul_pos hδ hqpow
  have hlogeq :
      Real.log (betaColumnIntervalKernel N s q δ) =
        Real.log δ + (N : ℝ) * Real.log q +
          (m : ℝ) * Real.log (1 - x) := by
    unfold betaColumnIntervalKernel
    dsimp [x, m]
    rw [Real.log_mul (ne_of_gt hprod) (ne_of_gt hbasepow),
      Real.log_mul (ne_of_gt hδ) (ne_of_gt hqpow),
      Real.log_pow, Real.log_pow]
  have hlog_base : -x / (1 - x) ≤ Real.log (1 - x) := by
    exact log_one_sub_ge_neg_div_one_sub (x := x) (by simpa [x] using hupper)
  have hm_nonneg : 0 ≤ (m : ℝ) := by positivity
  have hmul_base :
      -(((m : ℝ) * x) / (1 - x)) ≤ (m : ℝ) * Real.log (1 - x) := by
    have hmul := mul_le_mul_of_nonneg_left hlog_base hm_nonneg
    have hleft : (m : ℝ) * (-x / (1 - x)) =
        -(((m : ℝ) * x) / (1 - x)) := by ring
    simpa [hleft] using hmul
  have hOneNeg :
      -oneMinusCost ≤ -(((m : ℝ) * x) / (1 - x)) := by
    have hOne : (((m : ℝ) * x) / (1 - x)) ≤ oneMinusCost := by
      simpa [x, m] using hOneMinus
    linarith
  have hOneLog : -oneMinusCost ≤ (m : ℝ) * Real.log (1 - x) :=
    le_trans hOneNeg hmul_base
  rw [hlogeq]
  linarith

/-- The entropy term for the canonical spike mass scale.

For `q = a * speed / N^2`, the logarithmic contribution `N log q` is bounded
below once the scalar cost

`N * (2 log N - log(a * speed))`

is absorbed. -/
theorem betaColumnSpikeScale_entropy_log_lower
    {N speed a entropyCost : ℝ}
    (hN : 0 < N) (hSpike : 0 < a * speed)
    (hEntropy :
      N * (2 * Real.log N - Real.log (a * speed)) ≤ entropyCost) :
    -entropyCost ≤ N * Real.log (betaColumnSpikeScale N speed a) := by
  have hN2 : (N ^ 2) ≠ 0 := pow_ne_zero 2 (ne_of_gt hN)
  have hlog :
      Real.log (betaColumnSpikeScale N speed a) =
        Real.log (a * speed) - 2 * Real.log N := by
    unfold betaColumnSpikeScale
    rw [Real.log_div (ne_of_gt hSpike) hN2, Real.log_pow]
    ring
  rw [hlog]
  linarith

/-- Eventual Beta-kernel lower bound from explicit scalar cost controls.

This theorem is the asymptotic interface for `hBetaKernel`: the interval-length
and entropy terms each consume a slack, while the one-minus factor carries the
main cost `lam * a`. -/
theorem eventual_log_lower_of_betaColumnIntervalKernel
    {N s : ℕ → ℕ} {q δ speed : ℕ → ℝ}
    {lam a deltaSlack qSlack oneMinusSlack : ℝ}
    (hGeom :
      ∀ᶠ d in atTop,
        0 < q d ∧ 0 < δ d ∧ betaColumnIntervalUpper (q d) (δ d) < 1)
    (hDelta :
      ∀ᶠ d in atTop,
        -deltaSlack * speed d ≤ Real.log (δ d))
    (hQ :
      ∀ᶠ d in atTop,
        -qSlack * speed d ≤ (N d : ℝ) * Real.log (q d))
    (hOneMinus :
      ∀ᶠ d in atTop,
        (((betaColumnOtherShape (N d) (s d) - 1 : ℕ) : ℝ) *
            betaColumnIntervalUpper (q d) (δ d) /
              (1 - betaColumnIntervalUpper (q d) (δ d))) ≤
          (lam * a + oneMinusSlack) * speed d) :
    ∀ᶠ d in atTop,
      -(lam * a + deltaSlack + qSlack + oneMinusSlack) * speed d ≤
        Real.log (betaColumnIntervalKernel (N d) (s d) (q d) (δ d)) := by
  filter_upwards [hGeom, hDelta, hQ, hOneMinus]
    with d hgeom hdelta hq hone
  rcases hgeom with ⟨hqpos, hδpos, hupper⟩
  have hdelta' : -(deltaSlack * speed d) ≤ Real.log (δ d) := by
    have hrew : -(deltaSlack * speed d) = -deltaSlack * speed d := by ring
    rw [hrew]
    exact hdelta
  have hq' : -(qSlack * speed d) ≤ (N d : ℝ) * Real.log (q d) := by
    have hrew : -(qSlack * speed d) = -qSlack * speed d := by ring
    rw [hrew]
    exact hq
  have hfinite :=
    betaColumnIntervalKernel_log_lower_of_cost_bounds
      (N := N d) (s := s d) (q := q d) (δ := δ d)
      (deltaCost := deltaSlack * speed d)
      (qCost := qSlack * speed d)
      (oneMinusCost := (lam * a + oneMinusSlack) * speed d)
      hqpos hδpos hupper hdelta' hq' hone
  have hcost :
      -(deltaSlack * speed d + qSlack * speed d +
          (lam * a + oneMinusSlack) * speed d) =
        -(lam * a + deltaSlack + qSlack + oneMinusSlack) * speed d := by
    ring
  simpa [hcost] using hfinite

/-- Canonical-spike-scale version of the Beta-kernel asymptotic lower bound.

Here `q d` is fixed to `a * speed d / (N d)^2`.  The remaining hypotheses are
pure scalar estimates:

* positivity and upper-endpoint validity for the interval;
* absorption of `log δ`;
* absorption of the entropy term `N(2 log N - log(a speed))`;
* the main one-minus cost. -/
theorem eventual_log_lower_of_betaColumnIntervalKernel_spike_scale
    {N s : ℕ → ℕ} {δ speed : ℕ → ℝ}
    {lam a deltaSlack entropySlack oneMinusSlack : ℝ}
    (hNpos : ∀ᶠ d in atTop, 0 < (N d : ℝ))
    (hSpikePos : ∀ᶠ d in atTop, 0 < a * speed d)
    (hDeltaPos : ∀ᶠ d in atTop, 0 < δ d)
    (hUpper :
      ∀ᶠ d in atTop,
        betaColumnIntervalUpper
          (betaColumnSpikeScale (N d : ℝ) (speed d) a) (δ d) < 1)
    (hDelta :
      ∀ᶠ d in atTop,
        -deltaSlack * speed d ≤ Real.log (δ d))
    (hEntropy :
      ∀ᶠ d in atTop,
        (N d : ℝ) *
            (2 * Real.log (N d : ℝ) - Real.log (a * speed d)) ≤
          entropySlack * speed d)
    (hOneMinus :
      ∀ᶠ d in atTop,
        (((betaColumnOtherShape (N d) (s d) - 1 : ℕ) : ℝ) *
            betaColumnIntervalUpper
              (betaColumnSpikeScale (N d : ℝ) (speed d) a) (δ d) /
              (1 - betaColumnIntervalUpper
                (betaColumnSpikeScale (N d : ℝ) (speed d) a) (δ d))) ≤
          (lam * a + oneMinusSlack) * speed d) :
    ∀ᶠ d in atTop,
      -(lam * a + deltaSlack + entropySlack + oneMinusSlack) * speed d ≤
        Real.log
          (betaColumnIntervalKernel (N d) (s d)
            (betaColumnSpikeScale (N d : ℝ) (speed d) a) (δ d)) := by
  let q : ℕ → ℝ :=
    fun d => betaColumnSpikeScale (N d : ℝ) (speed d) a
  have hGeom :
      ∀ᶠ d in atTop,
        0 < q d ∧ 0 < δ d ∧ betaColumnIntervalUpper (q d) (δ d) < 1 := by
    filter_upwards [hNpos, hSpikePos, hDeltaPos, hUpper]
      with d hNd hSpiked hδd hUpperd
    have hN2 : 0 < (N d : ℝ) ^ 2 := pow_pos hNd 2
    have hq : 0 < q d := by
      dsimp [q, betaColumnSpikeScale]
      exact div_pos hSpiked hN2
    exact ⟨hq, hδd, hUpperd⟩
  have hQ :
      ∀ᶠ d in atTop,
        -entropySlack * speed d ≤ (N d : ℝ) * Real.log (q d) := by
    filter_upwards [hNpos, hSpikePos, hEntropy] with d hNd hSpiked hEntd
    have hraw :
        -(entropySlack * speed d) ≤
          (N d : ℝ) *
            Real.log (betaColumnSpikeScale (N d : ℝ) (speed d) a) :=
      betaColumnSpikeScale_entropy_log_lower
        (N := (N d : ℝ)) (speed := speed d) (a := a)
        (entropyCost := entropySlack * speed d)
        hNd hSpiked hEntd
    have hrew : -entropySlack * speed d = -(entropySlack * speed d) := by ring
    rw [hrew]
    simpa [q] using hraw
  exact
    eventual_log_lower_of_betaColumnIntervalKernel
      (N := N) (s := s) (q := q) (δ := δ) (speed := speed)
      (lam := lam) (a := a)
      (deltaSlack := deltaSlack) (qSlack := entropySlack)
      (oneMinusSlack := oneMinusSlack)
      hGeom hDelta hQ hOneMinus

/-- Single-slack canonical-spike-scale Beta-kernel asymptotic.

This is the form that plugs directly into the one-column lower-bound pipeline:
each non-main contribution consumes one third of the slack, and the main
one-minus term contributes `lam * a`. -/
theorem eventual_log_lower_of_betaColumnIntervalKernel_spike_scale_split_slack
    {N s : ℕ → ℕ} {δ speed : ℕ → ℝ}
    {lam a slack : ℝ}
    (hNpos : ∀ᶠ d in atTop, 0 < (N d : ℝ))
    (hSpikePos : ∀ᶠ d in atTop, 0 < a * speed d)
    (hDeltaPos : ∀ᶠ d in atTop, 0 < δ d)
    (hUpper :
      ∀ᶠ d in atTop,
        betaColumnIntervalUpper
          (betaColumnSpikeScale (N d : ℝ) (speed d) a) (δ d) < 1)
    (hDelta :
      ∀ᶠ d in atTop,
        -(slack / 3) * speed d ≤ Real.log (δ d))
    (hEntropy :
      ∀ᶠ d in atTop,
        (N d : ℝ) *
            (2 * Real.log (N d : ℝ) - Real.log (a * speed d)) ≤
          (slack / 3) * speed d)
    (hOneMinus :
      ∀ᶠ d in atTop,
        (((betaColumnOtherShape (N d) (s d) - 1 : ℕ) : ℝ) *
            betaColumnIntervalUpper
              (betaColumnSpikeScale (N d : ℝ) (speed d) a) (δ d) /
              (1 - betaColumnIntervalUpper
                (betaColumnSpikeScale (N d : ℝ) (speed d) a) (δ d))) ≤
          (lam * a + slack / 3) * speed d) :
    ∀ᶠ d in atTop,
      -(lam * a + slack) * speed d ≤
        Real.log
          (betaColumnIntervalKernel (N d) (s d)
            (betaColumnSpikeScale (N d : ℝ) (speed d) a) (δ d)) := by
  have h :=
    eventual_log_lower_of_betaColumnIntervalKernel_spike_scale
      (N := N) (s := s) (δ := δ) (speed := speed)
      (lam := lam) (a := a)
      (deltaSlack := slack / 3)
      (entropySlack := slack / 3)
      (oneMinusSlack := slack / 3)
      hNpos hSpikePos hDeltaPos hUpper hDelta hEntropy hOneMinus
  filter_upwards [h] with d hd
  have hcost :
      -(lam * a + slack / 3 + slack / 3 + slack / 3) * speed d =
        -(lam * a + slack) * speed d := by
    ring
  have hle :
      -(lam * a + slack / 3 + slack / 3 + slack / 3) * speed d ≤
        Real.log
          (betaColumnIntervalKernel (N d) (s d)
            (betaColumnSpikeScale (N d : ℝ) (speed d) a) (δ d)) := by
    simpa using hd
  rw [hcost] at hle
  exact hle

/-! ## Cap probability lower bound -/

/-- The logarithmic cost `C * N * log N` used for a small spherical cap in the
one-column lower-bound construction.

For the intended cap radius `N⁻¹` on the complex unit sphere in dimension `N`,
the cap probability is of order `exp(-O(N log N))`. -/
noncomputable def capNLogNCost (C N : ℝ) : ℝ :=
  C * N * Real.log N

/-- Finite lower-bound package for the column-direction cap probability.

`prob` is the probability that the normalized distinguished column direction
lies in the chosen cap around a fixed product vector.  The field
`prob_lower` records the only estimate used by the large-deviation lower
bound:

`prob ≥ exp(- C * N * log N)`.

This deliberately does not identify the exact spherical cap volume.  It
packages the `exp[-O(N log N)]` statement as a transparent input. -/
structure CapProbabilityLowerBound
    (prob N C : ℝ) : Prop where
  N_pos : 0 < N
  C_nonneg : 0 ≤ C
  prob_lower : Real.exp (-(capNLogNCost C N)) ≤ prob

theorem CapProbabilityLowerBound.prob_pos
    {prob N C : ℝ} (I : CapProbabilityLowerBound prob N C) :
    0 < prob :=
  lt_of_lt_of_le (Real.exp_pos _) I.prob_lower

/-- Logarithmic form of the finite cap lower bound:

`log prob ≥ - C N log N`. -/
theorem CapProbabilityLowerBound.log_prob_ge
    {prob N C : ℝ} (I : CapProbabilityLowerBound prob N C) :
    -(capNLogNCost C N) ≤ Real.log prob := by
  have hlog :
      Real.log (Real.exp (-(capNLogNCost C N))) ≤ Real.log prob :=
    Real.log_le_log (Real.exp_pos _) I.prob_lower
  simpa using hlog

/-- Exact algebraic lower kernel for a small projective cap on the complex
unit sphere.

For a Haar vector `u ∈ ℂ^N` and a fixed unit vector `e`, the squared overlap
`|⟪u,e⟫|^2` has distribution `Beta(1, N-1)`.  Hence the cap
`|⟪u,e⟫|^2 ≥ 1 - r^2` has probability exactly `r^(2(N-1))`.

This definition isolates that explicit finite-dimensional kernel. -/
noncomputable def projectiveCapKernel (N : ℕ) (r : ℝ) : ℝ :=
  r ^ (2 * (N - 1))

theorem projectiveCapKernel_pos
    {N : ℕ} {r : ℝ} (hr : 0 < r) :
    0 < projectiveCapKernel N r := by
  unfold projectiveCapKernel
  positivity

/-- Concrete finite lower-bound package for a projective cap probability.

`prob` is the probability of the cap and `r` is its Hilbert-space radius
parameter.  The field records the exact beta/projective cap lower kernel
`r^(2(N-1))`. -/
structure ProjectiveCapProbabilityLowerBound
    (prob : ℝ) (N : ℕ) (r : ℝ) : Prop where
  radius_pos : 0 < r
  prob_lower : projectiveCapKernel N r ≤ prob

theorem ProjectiveCapProbabilityLowerBound.prob_pos
    {prob : ℝ} {N : ℕ} {r : ℝ}
    (I : ProjectiveCapProbabilityLowerBound prob N r) :
    0 < prob :=
  lt_of_lt_of_le (projectiveCapKernel_pos I.radius_pos) I.prob_lower

/-! ### Geometric projective cap on the complex unit sphere -/

section ProjectiveCapGeometry

variable {ι : Type*} [Fintype ι]

/-- The projective cap around a unit vector `e` on the complex unit sphere:

`{u : S(ℂ^N) | 1 - r^2 ≤ |⟪e,u⟫|^2}`.

This is the cap used in the one-column spike event, because it controls the
phase-free overlap with the chosen product direction. -/
noncomputable def projectiveCapSet
    (e : EuclideanSpace ℂ ι) (r : ℝ) :
    Set (Metric.sphere (0 : EuclideanSpace ℂ ι) 1) :=
  {u | 1 - r ^ 2 ≤ ‖inner ℂ e (u : EuclideanSpace ℂ ι)‖ ^ 2}

/-- The radial cone over a projective cap, truncated at radius `< 1`.

This is the set whose ambient volume appears in Mathlib's
`Measure.toSphere_apply'` formula. -/
noncomputable def projectiveCapCone
    (e : EuclideanSpace ℂ ι) (r : ℝ) :
    Set (EuclideanSpace ℂ ι) :=
  Set.Ioo (0 : ℝ) 1 •
    ((Subtype.val : Metric.sphere (0 : EuclideanSpace ℂ ι) 1 →
      EuclideanSpace ℂ ι) '' projectiveCapSet (ι := ι) e r)

theorem measurableSet_projectiveCapSet
    (e : EuclideanSpace ℂ ι) (r : ℝ) :
    MeasurableSet (projectiveCapSet (ι := ι) e r) := by
  dsimp [projectiveCapSet]
  exact measurableSet_le measurable_const (by fun_prop)

/-- Surface probability of a projective cap as normalized cone volume.

This is the direct `Measure.toSphere_apply'` reduction:

`surface_probability(cap) = volume(cone over cap inside the unit ball)
  / volume(unit ball)`.

The factor `Module.finrank ℝ E` appearing in `Measure.toSphere_apply'` cancels
against the same factor in `Measure.toSphere_apply_univ`. -/
theorem toFinite_toSphere_projectiveCapSet_eq_cone_volume_ratio
    [Nonempty ι]
    (μ : Measure (EuclideanSpace ℂ ι)) [μ.IsAddHaarMeasure]
    [SFinite μ.toSphere] [IsFiniteMeasure μ.toSphere]
    (e : EuclideanSpace ℂ ι) (r : ℝ) :
    μ.toSphere.toFinite (projectiveCapSet (ι := ι) e r) =
      (μ (Metric.ball (0 : EuclideanSpace ℂ ι) 1))⁻¹ *
        μ (projectiveCapCone (ι := ι) e r) := by
  have hraw :
      μ.toSphere.toFinite (projectiveCapSet (ι := ι) e r) =
        (Module.finrank ℝ (EuclideanSpace ℂ ι) *
            μ (Metric.ball (0 : EuclideanSpace ℂ ι) 1))⁻¹ *
          (Module.finrank ℝ (EuclideanSpace ℂ ι) *
            μ (projectiveCapCone (ι := ι) e r)) := by
    have htoFinite :
        μ.toSphere.toFinite = ProbabilityTheory.cond μ.toSphere Set.univ := by
      unfold Measure.toFinite
      rw [Measure.toFiniteAux,
        if_pos (inferInstance : IsFiniteMeasure μ.toSphere)]
    rw [htoFinite]
    rw [ProbabilityTheory.cond_apply MeasurableSet.univ μ.toSphere]
    simp only [Set.univ_inter]
    rw [Measure.toSphere_apply' μ
      (measurableSet_projectiveCapSet (ι := ι) e r)]
    rw [Measure.toSphere_apply_univ]
    rfl
  rw [hraw]
  have hdim_nat :
      0 < Module.finrank ℝ (EuclideanSpace ℂ ι) :=
    Module.finrank_pos
  have hdim0 :
      (Module.finrank ℝ (EuclideanSpace ℂ ι) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hdim_nat.ne'
  have hdimt :
      (Module.finrank ℝ (EuclideanSpace ℂ ι) : ℝ≥0∞) ≠ ∞ := by
    simp
  rw [ENNReal.mul_inv]
  · calc
      ((Module.finrank ℝ (EuclideanSpace ℂ ι) : ℝ≥0∞)⁻¹ *
          (μ (Metric.ball (0 : EuclideanSpace ℂ ι) 1))⁻¹) *
          ((Module.finrank ℝ (EuclideanSpace ℂ ι) : ℝ≥0∞) *
            μ (projectiveCapCone (ι := ι) e r))
        =
          (μ (Metric.ball (0 : EuclideanSpace ℂ ι) 1))⁻¹ *
            (((Module.finrank ℝ (EuclideanSpace ℂ ι) : ℝ≥0∞)⁻¹ *
                (Module.finrank ℝ (EuclideanSpace ℂ ι) : ℝ≥0∞)) *
              μ (projectiveCapCone (ι := ι) e r)) := by
            ac_rfl
      _ =
          (μ (Metric.ball (0 : EuclideanSpace ℂ ι) 1))⁻¹ *
            μ (projectiveCapCone (ι := ι) e r) := by
            rw [ENNReal.inv_mul_cancel hdim0 hdimt, one_mul]
  · exact Or.inl hdim0
  · exact Or.inl hdimt

/-- Probability of the geometric projective cap under a chosen sphere law. -/
noncomputable def projectiveCapProbability
    (μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1))
    (e : EuclideanSpace ℂ ι) (r : ℝ) : ℝ :=
  μ.real (projectiveCapSet (ι := ι) e r)

/-- Real-valued version of
`toFinite_toSphere_projectiveCapSet_eq_cone_volume_ratio`, phrased in the
project's cap-probability notation. -/
theorem projectiveCapProbability_toFinite_toSphere_eq_cone_volume_ratio
    [Nonempty ι]
    (μ : Measure (EuclideanSpace ℂ ι)) [μ.IsAddHaarMeasure]
    [SFinite μ.toSphere] [IsFiniteMeasure μ.toSphere]
    (e : EuclideanSpace ℂ ι) (r : ℝ) :
    projectiveCapProbability (ι := ι) μ.toSphere.toFinite e r =
      ENNReal.toReal
        ((μ (Metric.ball (0 : EuclideanSpace ℂ ι) 1))⁻¹ *
          μ (projectiveCapCone (ι := ι) e r)) := by
  unfold projectiveCapProbability Measure.real
  rw [toFinite_toSphere_projectiveCapSet_eq_cone_volume_ratio
    (ι := ι) μ e r]

/-- Cone-volume form of the projective-cap identity.

Mathematically, after reducing the center to the first coordinate and writing
`x = z ⊕ y ∈ ℂ ⊕ ℂ^(N-1)`, the cone over the cap is described by

`|z|^2 ≥ (1 - r^2) (|z|^2 + ‖y‖^2)` and
`|z|^2 + ‖y‖^2 < 1`.

Integrating this coordinate description gives

`Vol(cone cap) = r^(2(N-1)) Vol(unit ball)`.

This theorem is the formal `Measure.toSphere_apply'` version of that exact
volume statement: once the normalized spherical cap probability is known to be
`r^(2(N-1))`, the real ambient volume of the radial cone is exactly
`r^(2(N-1))` times the real volume of the ambient unit ball. -/
theorem projectiveCapCone_toReal_volume_eq_pow_mul_ball_toReal_of_capProbability
    [Nonempty ι]
    (μ : Measure (EuclideanSpace ℂ ι)) [μ.IsAddHaarMeasure]
    [SFinite μ.toSphere] [IsFiniteMeasure μ.toSphere]
    (e : EuclideanSpace ℂ ι) (N : ℕ) (r : ℝ)
    (hball0 : μ (Metric.ball (0 : EuclideanSpace ℂ ι) 1) ≠ 0)
    (hballt : μ (Metric.ball (0 : EuclideanSpace ℂ ι) 1) ≠ ∞)
    (hcap :
      projectiveCapProbability (ι := ι) μ.toSphere.toFinite e r =
        r ^ (2 * (N - 1))) :
    ENNReal.toReal (μ (projectiveCapCone (ι := ι) e r)) =
      r ^ (2 * (N - 1)) *
        ENNReal.toReal (μ (Metric.ball (0 : EuclideanSpace ℂ ι) 1)) := by
  have hratio :=
    projectiveCapProbability_toFinite_toSphere_eq_cone_volume_ratio
      (ι := ι) μ e r
  rw [hratio] at hcap
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv] at hcap
  have hbpos :
      0 < ENNReal.toReal
        (μ (Metric.ball (0 : EuclideanSpace ℂ ι) 1)) :=
    ENNReal.toReal_pos hball0 hballt
  calc
    ENNReal.toReal (μ (projectiveCapCone (ι := ι) e r))
        =
          ((ENNReal.toReal
              (μ (Metric.ball (0 : EuclideanSpace ℂ ι) 1)))⁻¹ *
            ENNReal.toReal (μ (projectiveCapCone (ι := ι) e r))) *
          ENNReal.toReal
            (μ (Metric.ball (0 : EuclideanSpace ℂ ι) 1)) := by
            field_simp [hbpos.ne']
    _ =
        r ^ (2 * (N - 1)) *
          ENNReal.toReal
            (μ (Metric.ball (0 : EuclideanSpace ℂ ι) 1)) := by
          rw [hcap]

theorem projectiveCapCone_toReal_volume_eq_kernel_mul_ball_toReal
    [Nonempty ι]
    (μ : Measure (EuclideanSpace ℂ ι)) [μ.IsAddHaarMeasure]
    [SFinite μ.toSphere] [IsFiniteMeasure μ.toSphere]
    (e : EuclideanSpace ℂ ι) (N : ℕ) (r : ℝ)
    (hball0 : μ (Metric.ball (0 : EuclideanSpace ℂ ι) 1) ≠ 0)
    (hballt : μ (Metric.ball (0 : EuclideanSpace ℂ ι) 1) ≠ ∞)
    (hcap :
      projectiveCapProbability (ι := ι) μ.toSphere.toFinite e r =
        projectiveCapKernel N r) :
    ENNReal.toReal (μ (projectiveCapCone (ι := ι) e r)) =
      projectiveCapKernel N r *
        ENNReal.toReal (μ (Metric.ball (0 : EuclideanSpace ℂ ι) 1)) := by
  exact
    projectiveCapCone_toReal_volume_eq_pow_mul_ball_toReal_of_capProbability
      (ι := ι) μ e N r hball0 hballt (by
        simpa [projectiveCapKernel] using hcap)

/-! #### Direct coordinate integral for the projective cone -/

/-- The one-dimensional coordinate integral obtained by writing the cone over
the projective cap in coordinates `x = z ⊕ y`.

Here `n` is the complex dimension of the `y`-block.  For `0 ≤ r < 1`, the
cone condition

`|z|² ≥ (1-r²)(|z|² + ‖y‖²)`, `|z|² + ‖y‖² < 1`

has `y`-radius

* `sqrt(|z|² r²/(1-r²))` for `0 ≤ |z|² ≤ 1-r²`;
* `sqrt(1-|z|²)` for `1-r² ≤ |z|² ≤ 1`.

After cancelling the common ball-volume constant, the remaining ratio is this
scalar integral. -/
noncomputable def projectiveConeCoordinateRatio (n : ℕ) (r : ℝ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) *
    (((r ^ 2 / (1 - r ^ 2)) ^ n) *
        (∫ t in (0 : ℝ)..(1 - r ^ 2), t ^ n) +
      ∫ t in (1 - r ^ 2)..1, (1 - t) ^ n)

/-- The scalar coordinate integral before division by the unit-ball
normalizing factor.

If the transverse complex dimension is `n`, the coordinate computation gives

`Vol(cone cap) = π V_n * projectiveConeCoordinateBracket n r`,

where `V_n` is the volume of the unit ball in the transverse `ℂ^n`. -/
noncomputable def projectiveConeCoordinateBracket (n : ℕ) (r : ℝ) : ℝ :=
  ((r ^ 2 / (1 - r ^ 2)) ^ n) *
      (∫ t in (0 : ℝ)..(1 - r ^ 2), t ^ n) +
    ∫ t in (1 - r ^ 2)..1, (1 - t) ^ n

/-- Direct evaluation of the `z ⊕ y` cone integral.

This is the formal scalar core of the geometric cap computation:

`Vol(cone cap) / Vol(unit ball) = r^(2n)`,

where `n = N-1` is the complex dimension transverse to the cap centre.  The
proof is purely by evaluating the two coordinate integrals; it does not use
the Beta distribution. -/
theorem projectiveConeCoordinateRatio_eq_pow
    (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    projectiveConeCoordinateRatio n r = r ^ (2 * n) := by
  let A : ℝ := 1 - r ^ 2
  have hr2lt : r ^ 2 < 1 := by nlinarith
  have hApos : 0 < A := by
    dsimp [A]
    linarith
  have hAne : A ≠ 0 := ne_of_gt hApos
  have hNne : (((n + 1 : ℕ) : ℝ) ≠ 0) := by positivity
  have hInt1 :
      (∫ t in (0 : ℝ)..A, t ^ n) =
        A ^ (n + 1) / ((n + 1 : ℕ) : ℝ) := by
    rw [integral_pow]
    simp
  have hInt2 :
      (∫ t in A..1, (1 - t) ^ n) =
        (1 - A) ^ (n + 1) / ((n + 1 : ℕ) : ℝ) := by
    have hderiv : ∀ x ∈ Set.uIcc A 1,
        HasDerivAt (fun y : ℝ => - (1 - y) ^ (n + 1))
          (((n + 1 : ℕ) : ℝ) * (1 - x) ^ n) x := by
      intro x _hx
      have h1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
        simpa using (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
      have h2 := h1.pow (n + 1)
      simpa [Nat.succ_eq_add_one, add_comm, add_left_comm, add_assoc,
        mul_assoc, mul_left_comm, mul_comm] using h2.neg
    have hint : IntervalIntegrable
        (fun x : ℝ => ((n + 1 : ℕ) : ℝ) * (1 - x) ^ n)
        MeasureTheory.volume A 1 := by
      exact
        (continuous_const.mul
          ((continuous_const.sub continuous_id).pow n)).intervalIntegrable _ _
    have h :
        (∫ x in A..1, ((n + 1 : ℕ) : ℝ) * (1 - x) ^ n) =
          (1 - A) ^ (n + 1) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
      simp
    rw [intervalIntegral.integral_const_mul] at h
    calc
      (∫ t in A..1, (1 - t) ^ n)
          =
            (((n + 1 : ℕ) : ℝ) *
              (∫ t in A..1, (1 - t) ^ n)) /
              ((n + 1 : ℕ) : ℝ) := by
              field_simp [hNne]
      _ = (1 - A) ^ (n + 1) / ((n + 1 : ℕ) : ℝ) := by
              rw [h]
  have h1A : 1 - A = r ^ 2 := by
    dsimp [A]
    ring
  have hterm1 :
      (r ^ 2 / A) ^ n * A ^ (n + 1) = (r ^ 2) ^ n * A := by
    rw [div_pow, show A ^ (n + 1) = A ^ n * A by rw [pow_succ]]
    field_simp [hAne, pow_ne_zero n hAne]
  dsimp [projectiveConeCoordinateRatio]
  change
    ((n + 1 : ℕ) : ℝ) *
      (((r ^ 2 / A) ^ n) *
          (∫ t in (0 : ℝ)..A, t ^ n) +
        ∫ t in A..1, (1 - t) ^ n) =
      r ^ (2 * n)
  rw [hInt1, hInt2, h1A]
  calc
    ((n + 1 : ℕ) : ℝ) *
        ((r ^ 2 / A) ^ n *
            (A ^ (n + 1) / ((n + 1 : ℕ) : ℝ)) +
          (r ^ 2) ^ (n + 1) / ((n + 1 : ℕ) : ℝ))
        =
          (r ^ 2 / A) ^ n * A ^ (n + 1) +
            (r ^ 2) ^ (n + 1) := by
          field_simp [hNne]
    _ = (r ^ 2) ^ n * A + (r ^ 2) ^ (n + 1) := by
          rw [hterm1]
    _ = (r ^ 2) ^ n := by
          rw [show (r ^ 2) ^ (n + 1) = (r ^ 2) ^ n * r ^ 2 by
            rw [pow_succ]]
          have hAadd : A + r ^ 2 = 1 := by
            dsimp [A]
            ring
          calc
            (r ^ 2) ^ n * A + (r ^ 2) ^ n * r ^ 2
                = (r ^ 2) ^ n * (A + r ^ 2) := by ring
            _ = (r ^ 2) ^ n := by rw [hAadd, mul_one]
    _ = r ^ (2 * n) := by
          rw [pow_mul]

/-- Evaluation of the unnormalised scalar bracket in the `z ⊕ y` cone-volume
calculation.

This is the displayed calculation

`[(r²/(1-r²))^n ∫₀^{1-r²} t^n dt + ∫_{1-r²}^1 (1-t)^n dt]
  = r^{2n}/(n+1)`.

It is the same computation as `projectiveConeCoordinateRatio_eq_pow`, but
before multiplying by the normalizing factor `n+1`. -/
theorem projectiveConeCoordinateBracket_eq_pow_div
    (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    projectiveConeCoordinateBracket n r =
      r ^ (2 * n) / ((n + 1 : ℕ) : ℝ) := by
  have hratio := projectiveConeCoordinateRatio_eq_pow n hr0 hr1
  have hNne : (((n + 1 : ℕ) : ℝ) ≠ 0) := by positivity
  let B : ℝ := projectiveConeCoordinateBracket n r
  have hB :
      projectiveConeCoordinateRatio n r =
        ((n + 1 : ℕ) : ℝ) * B := by
    rfl
  rw [hB] at hratio
  change B = r ^ (2 * n) / ((n + 1 : ℕ) : ℝ)
  rw [← hratio]
  field_simp [hNne]

/-- Full scalar volume formula for the coordinate cone.

If `Vn` denotes the volume of the unit ball in the transverse `ℂ^n`, then
the coordinate integration gives

`Vol(C_r) = π Vn /(n+1) * r^(2n)`.

This is the exact `π V_{N-1}/N · r^{2N-2}` formula, with `n = N-1`. -/
theorem projectiveConeCoordinateVolume_eq
    (n : ℕ) {r Vn : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Real.pi * Vn * projectiveConeCoordinateBracket n r =
      (Real.pi * Vn / ((n + 1 : ℕ) : ℝ)) * r ^ (2 * n) := by
  rw [projectiveConeCoordinateBracket_eq_pow_div n hr0 hr1]
  ring

/-- Real volume of the complex Euclidean unit ball in dimension `card ι`.

This is Mathlib's even-dimensional Euclidean ball formula specialized to
`EuclideanSpace ℂ ι`. -/
theorem complexUnitBallVolume_toReal_eq_pi_pow_div_factorial
    {ι : Type*} [Fintype ι] [Nonempty ι] :
    ENNReal.toReal
        ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι))
          (Metric.ball (0 : EuclideanSpace ℂ ι) 1)) =
      Real.pi ^ (Fintype.card ι) / (Fintype.card ι).factorial := by
  rw [InnerProductSpace.volume_ball_of_dim_even
    (E := EuclideanSpace ℂ ι)
    (k := Fintype.card ι)
    (complex_euclidean_real_finrank (ι := ι))
    (0 : EuclideanSpace ℂ ι) (1 : ℝ)]
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow]
  rw [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (1 : ℝ))]
  simp only [one_pow, one_mul]
  rw [ENNReal.toReal_ofReal]
  positivity

/-- Recursive form of the complex unit-ball volume:

`Vol(B_{ℂ^{n+1}}) = π Vol(B_{ℂ^n}) / (n+1)`.

This is the normalizing identity used after the coordinate cone computation. -/
theorem complexUnitBallVolume_toReal_option
    {ι : Type*} [Fintype ι] [Nonempty ι] :
    ENNReal.toReal
        ((MeasureTheory.volume : Measure (EuclideanSpace ℂ (Option ι)))
          (Metric.ball (0 : EuclideanSpace ℂ (Option ι)) 1)) =
      Real.pi *
        ENNReal.toReal
          ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι))
            (Metric.ball (0 : EuclideanSpace ℂ ι) 1)) /
        ((Fintype.card ι + 1 : ℕ) : ℝ) := by
  rw [complexUnitBallVolume_toReal_eq_pi_pow_div_factorial
    (ι := Option ι)]
  rw [complexUnitBallVolume_toReal_eq_pi_pow_div_factorial
    (ι := ι)]
  have hfac :
      (((Fintype.card ι + 1 : ℕ).factorial : ℕ) : ℝ) =
        ((Fintype.card ι + 1 : ℕ) : ℝ) *
          (((Fintype.card ι).factorial : ℕ) : ℝ) := by
    rw [Nat.factorial_succ]
    norm_num
  have hden₁ :
      (((Fintype.card ι + 1 : ℕ) : ℝ) ≠ 0) := by positivity
  have hden₂ :
      ((((Fintype.card ι).factorial : ℕ) : ℝ) ≠ 0) := by positivity
  simp only [Fintype.card_option]
  rw [hfac]
  field_simp [hden₁, hden₂]
  ring

/-- Coordinate cone volume normalized by the actual ambient complex unit-ball
volume.

For a transverse coordinate space `ℂ^ι`, the ambient space after adjoining the
distinguished complex coordinate is `ℂ^(Option ι)`.  Combining the exact cone
coordinate integral with the recursive ball-volume identity gives

`π Vol(B_{ℂ^ι}) bracket(card ι,r)
  = Vol(B_{ℂ^(Option ι)}) r^(2 card ι)`.

This is the formal statement corresponding to

`Vol(C_r) = Vol(B_{ℂ^N}) r^{2(N-1)}` with `N = card ι + 1`,
after the `z ⊕ y` coordinate calculation. -/
theorem projectiveConeCoordinateVolume_eq_unitBallVolume_mul_pow
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Real.pi *
        ENNReal.toReal
          ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι))
            (Metric.ball (0 : EuclideanSpace ℂ ι) 1)) *
        projectiveConeCoordinateBracket (Fintype.card ι) r =
      ENNReal.toReal
          ((MeasureTheory.volume : Measure (EuclideanSpace ℂ (Option ι)))
            (Metric.ball (0 : EuclideanSpace ℂ (Option ι)) 1)) *
        r ^ (2 * Fintype.card ι) := by
  rw [projectiveConeCoordinateVolume_eq (Fintype.card ι) hr0 hr1]
  rw [complexUnitBallVolume_toReal_option (ι := ι)]

/-! ### Moving the centre of a projective cap by unitary invariance -/

/-- Pulling a projective cap back by a complex linear isometry moves the
centre by the inverse isometry. -/
theorem projectiveCapSet_preimage_linearIsometryEquiv
    (V : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι)
    (e : EuclideanSpace ℂ ι) (r : ℝ) :
    (Subtype.map V (fun _ hx => by simpa using hx)) ⁻¹'
        projectiveCapSet (ι := ι) e r =
      projectiveCapSet (ι := ι) (V.symm e) r := by
  ext u
  simp [projectiveCapSet]
  have hinner :
      inner ℂ e (V (u : EuclideanSpace ℂ ι)) =
        inner ℂ (V.symm e) (u : EuclideanSpace ℂ ι) := by
    simpa using
      (LinearIsometryEquiv.inner_map_map V (V.symm e)
        (u : EuclideanSpace ℂ ι))
  rw [hinner]

/-- If a sphere law is invariant under a complex linear isometry, the cap
probability at `e` equals the cap probability at the inverse image of `e`. -/
theorem projectiveCapProbability_eq_symm_center_of_map_linearIsometryEquiv
    (μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1))
    (V : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι)
    (hμ : Measure.map (Subtype.map V (fun _ hx => by simpa using hx)) μ = μ)
    (e : EuclideanSpace ℂ ι) (r : ℝ) :
    projectiveCapProbability (ι := ι) μ e r =
      projectiveCapProbability (ι := ι) μ (V.symm e) r := by
  unfold projectiveCapProbability Measure.real
  let S : Metric.sphere (0 : EuclideanSpace ℂ ι) 1 →
      Metric.sphere (0 : EuclideanSpace ℂ ι) 1 :=
    Subtype.map V (fun _ hx => by simpa using hx)
  have hS_meas : Measurable S :=
    V.continuous.subtype_map (fun _ hx => by simpa using hx) |>.measurable
  have hpre :
      S ⁻¹' projectiveCapSet (ι := ι) e r =
        projectiveCapSet (ι := ι) (V.symm e) r :=
    projectiveCapSet_preimage_linearIsometryEquiv (ι := ι) V e r
  have hmeasure :
      μ (projectiveCapSet (ι := ι) e r) =
        μ (projectiveCapSet (ι := ι) (V.symm e) r) := by
    calc
      μ (projectiveCapSet (ι := ι) e r)
          = (Measure.map S μ) (projectiveCapSet (ι := ι) e r) := by
            rw [hμ]
      _ = μ (S ⁻¹' projectiveCapSet (ι := ι) e r) := by
            rw [Measure.map_apply hS_meas
              (measurableSet_projectiveCapSet (ι := ι) e r)]
      _ = μ (projectiveCapSet (ι := ι) (V.symm e) r) := by
            rw [hpre]
  exact congrArg ENNReal.toReal hmeasure

/-- The projective-cap probability can be transported from `e₀` to `e` by any
isometry sending `e₀` to `e`, provided the sphere law is invariant under that
isometry. -/
theorem projectiveCapProbability_eq_of_linearIsometryEquiv
    (μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1))
    (V : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι)
    (hμ : Measure.map (Subtype.map V (fun _ hx => by simpa using hx)) μ = μ)
    {e₀ e : EuclideanSpace ℂ ι}
    (hVe : V e₀ = e) (r : ℝ) :
    projectiveCapProbability (ι := ι) μ e r =
      projectiveCapProbability (ι := ι) μ e₀ r := by
  have hprob :
      projectiveCapProbability (ι := ι) μ e r =
        projectiveCapProbability (ι := ι) μ (V.symm e) r :=
    projectiveCapProbability_eq_symm_center_of_map_linearIsometryEquiv
      (ι := ι) μ V hμ e r
  have hsymm : V.symm e = e₀ := by
    calc
      V.symm e = V.symm (V e₀) := by rw [hVe]
      _ = e₀ := by simp
  simpa [hsymm] using hprob

/-- The abstract `Subtype.map` action induced by `matrixUnitaryLinearIsometryEquiv`
is the same action as the already-registered unitary action on the complex
unit sphere. -/
theorem matrixUnitaryLinearIsometryEquiv_sphereMap_eq_smul
    [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ) :
    (Subtype.map (matrixUnitaryLinearIsometryEquiv U)
        (fun x hx => by
          rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hx ⊢
          calc
            ‖matrixUnitaryLinearIsometryEquiv U x‖ = ‖x‖ :=
              (matrixUnitaryLinearIsometryEquiv U).norm_map x
            _ = 1 := hx)) =
      (fun u : Metric.sphere (0 : EuclideanSpace ℂ ι) 1 => U • u) := by
  funext u
  apply Subtype.ext
  ext i
  change
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
        (U : Matrix ι ι ℂ) (u : EuclideanSpace ℂ ι)) i =
      (WithLp.toLp 2
        (fun i => ∑ j, (U : Matrix ι ι ℂ) i j *
          (u : EuclideanSpace ℂ ι) j)) i
  simp [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct]

/-- Reduction to a reference unit vector by invariance under the compact
unitary action on the sphere.

In particular, once the cap identity is proved for one chosen unit vector
`e₀` (the role of `e₁`), it holds for every unit centre `e`. -/
theorem projectiveCapProbability_eq_reference_of_unitary_invariant
    [DecidableEq ι] [Nonempty ι]
    {μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)}
    (hμ : ∀ U : Matrix.unitaryGroup ι ℂ,
      Measure.map
        (fun u : Metric.sphere (0 : EuclideanSpace ℂ ι) 1 => U • u) μ = μ)
    {e₀ e : EuclideanSpace ℂ ι}
    (he₀ : ‖e₀‖ = 1) (he : ‖e‖ = 1) (r : ℝ) :
    projectiveCapProbability (ι := ι) μ e r =
      projectiveCapProbability (ι := ι) μ e₀ r := by
  let x₀ : Metric.sphere (0 : EuclideanSpace ℂ ι) 1 :=
    ⟨e₀, by simpa [Metric.mem_sphere, dist_eq_norm] using he₀⟩
  let x : Metric.sphere (0 : EuclideanSpace ℂ ι) 1 :=
    ⟨e, by simpa [Metric.mem_sphere, dist_eq_norm] using he⟩
  obtain ⟨U, hU⟩ :=
    MulAction.exists_smul_eq (Matrix.unitaryGroup ι ℂ) x₀ x
  have hVe : matrixUnitaryLinearIsometryEquiv U e₀ = e := by
    have hcoe := congrArg
      (fun y : Metric.sphere (0 : EuclideanSpace ℂ ι) 1 =>
        (y : EuclideanSpace ℂ ι)) hU
    simpa [x₀, x, matrixUnitaryLinearIsometryEquiv_apply] using hcoe
  let V : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι :=
    matrixUnitaryLinearIsometryEquiv U
  have hmap :
      Measure.map (Subtype.map V (fun _ hx => by simpa using hx)) μ = μ := by
    have hfun :
        (Subtype.map V (fun _ hx => by simpa using hx)) =
          (fun u : Metric.sphere (0 : EuclideanSpace ℂ ι) 1 => U • u) := by
      dsimp [V]
      exact matrixUnitaryLinearIsometryEquiv_sphereMap_eq_smul (ι := ι) U
    rw [hfun]
    exact hμ U
  exact projectiveCapProbability_eq_of_linearIsometryEquiv
    (ι := ι) μ V hmap hVe r

/-- Squared projective overlap with the chosen direction `e`.

This is the real random variable whose upper tail is exactly the projective
cap.  Separating it out prevents the Haar-cap computation from being hidden
inside a set-theoretic rewrite. -/
noncomputable def projectiveOverlapSq
    (e : EuclideanSpace ℂ ι) :
    Metric.sphere (0 : EuclideanSpace ℂ ι) 1 → ℝ :=
  fun u => ‖inner ℂ e (u : EuclideanSpace ℂ ι)‖ ^ 2

theorem measurable_projectiveOverlapSq
    (e : EuclideanSpace ℂ ι) :
    Measurable (projectiveOverlapSq (ι := ι) e) := by
  change Measurable
    (fun u : Metric.sphere (0 : EuclideanSpace ℂ ι) 1 =>
      ‖inner ℂ e (u : EuclideanSpace ℂ ι)‖ ^ 2)
  fun_prop

/-- The squared projective overlap with a unit vector takes values in `[0,1]`. -/
theorem projectiveOverlapSq_bounds
    {e : EuclideanSpace ℂ ι} (he : ‖e‖ = 1)
    (u : Metric.sphere (0 : EuclideanSpace ℂ ι) 1) :
    0 ≤ projectiveOverlapSq (ι := ι) e u ∧
      projectiveOverlapSq (ι := ι) e u ≤ 1 := by
  constructor
  · unfold projectiveOverlapSq
    positivity
  · unfold projectiveOverlapSq
    have hu : ‖(u : EuclideanSpace ℂ ι)‖ = 1 := by
      rw [← dist_zero_right (a := (u : EuclideanSpace ℂ ι))]
      exact u.2
    have hle : ‖inner ℂ e (u : EuclideanSpace ℂ ι)‖ ≤ 1 := by
      calc
        ‖inner ℂ e (u : EuclideanSpace ℂ ι)‖
            ≤ ‖e‖ * ‖(u : EuclideanSpace ℂ ι)‖ :=
              norm_inner_le_norm e (u : EuclideanSpace ℂ ι)
        _ = 1 := by rw [he, hu, one_mul]
    exact (sq_le_one_iff₀ (norm_nonneg _)).2 hle

/-- The geometric projective cap is exactly the inverse image of the upper tail
of the squared projective overlap. -/
theorem projectiveCapSet_eq_preimage_projectiveOverlapSq
    (e : EuclideanSpace ℂ ι) (r : ℝ) :
    projectiveCapSet (ι := ι) e r =
      (projectiveOverlapSq (ι := ι) e) ⁻¹' Set.Ici (1 - r ^ 2) := by
  rfl

/-- Push-forward law of the squared projective overlap under a sphere law. -/
noncomputable def projectiveOverlapSqLaw
    (μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1))
    (e : EuclideanSpace ℂ ι) : Measure ℝ :=
  Measure.map (projectiveOverlapSq (ι := ι) e) μ

/-- If the threshold is nonpositive, the upper tail of the squared-overlap
law is the whole probability mass. -/
theorem projectiveOverlapSqLaw_real_Ici_of_nonpos
    {μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)}
    [IsProbabilityMeasure μ]
    {e : EuclideanSpace ℂ ι} (he : ‖e‖ = 1)
    {a : ℝ} (ha : a ≤ 0) :
    (projectiveOverlapSqLaw (ι := ι) μ e).real (Set.Ici a) = 1 := by
  unfold projectiveOverlapSqLaw Measure.real
  rw [Measure.map_apply (measurable_projectiveOverlapSq (ι := ι) e)
    measurableSet_Ici]
  have hpre :
      (projectiveOverlapSq (ι := ι) e) ⁻¹' Set.Ici a = Set.univ := by
    ext u
    simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_univ, iff_true]
    exact ha.trans (projectiveOverlapSq_bounds (ι := ι) he u).1
  rw [hpre]
  simp

/-- Analytic conversion: the upper tail of the squared-overlap push-forward is
the projective cap probability. -/
theorem projectiveOverlapSqLaw_tail_eq_capProbability
    (μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1))
    (e : EuclideanSpace ℂ ι) (r : ℝ) :
    (projectiveOverlapSqLaw (ι := ι) μ e).real (Set.Ici (1 - r ^ 2)) =
      projectiveCapProbability (ι := ι) μ e r := by
  unfold projectiveOverlapSqLaw projectiveCapProbability
  rw [map_measureReal_apply
    (measurable_projectiveOverlapSq (ι := ι) e) measurableSet_Ici]
  rfl

/-- Exact geometric cap-volume statement.

For the normalized Haar/surface law on the complex unit sphere in dimension
`N`, the intended theorem is

`projectiveCapProbability μ e r = r^(2*(N-1))`.

This structure isolates precisely that geometric fact from the downstream
large-deviation bookkeeping. -/
structure ProjectiveCapExactVolume
    (μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1))
    (e : EuclideanSpace ℂ ι) (N : ℕ) (r : ℝ) : Prop where
  radius_pos : 0 < r
  prob_eq : projectiveCapProbability (ι := ι) μ e r = projectiveCapKernel N r

/-- Unit-vector version of the exact geometric cap-volume statement.

This is the mathematically honest spherical cap law: the formula
`r^(2*(N-1))` is attached to a normalized center `e`.  The older
`ProjectiveCapExactVolume` interface is kept as a downstream bookkeeping
object, but the canonical theorem should pass through this unit-vector
version first. -/
structure UnitProjectiveCapExactVolume
    (μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1))
    (e : EuclideanSpace ℂ ι) (N : ℕ) (r : ℝ) : Prop where
  unit_vector : ‖e‖ = 1
  radius_pos : 0 < r
  prob_eq : projectiveCapProbability (ι := ι) μ e r = projectiveCapKernel N r

/-- Forgetting the unit-vector certificate gives the legacy exact-volume
interface used by the lower-bound pipeline. -/
theorem UnitProjectiveCapExactVolume.toProjectiveCapExactVolume
    {μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)}
    {e : EuclideanSpace ℂ ι} {N : ℕ} {r : ℝ}
    (I : UnitProjectiveCapExactVolume (ι := ι) μ e N r) :
    ProjectiveCapExactVolume (ι := ι) μ e N r where
  radius_pos := I.radius_pos
  prob_eq := I.prob_eq

/-- Exact projective-kernel tail for a real overlap law.

For Haar measure on the complex unit sphere in dimension `N`, this is the
finite-dimensional identity

`P(|⟪e,u⟫|² ≥ 1 - r²) = r^(2*(N-1))`.

The structure records that analytic input independently of the geometric cap
set. -/
structure ProjectiveOverlapKernelTail
    (ν : Measure ℝ) (N : ℕ) : Prop where
  tail_eq :
    ∀ {r : ℝ}, 0 < r → r ≤ 1 →
      ν.real (Set.Ici (1 - r ^ 2)) = projectiveCapKernel N r

/-! #### Beta tail computation for the projective overlap -/

theorem beta_one_nat_succ (m : ℕ) :
    ProbabilityTheory.beta (1 : ℝ) ((m + 1 : ℕ) : ℝ) =
      1 / ((m + 1 : ℕ) : ℝ) := by
  unfold ProbabilityTheory.beta
  rw [Real.Gamma_one]
  have hsum :
      (1 : ℝ) + ((m + 1 : ℕ) : ℝ) =
        ((m + 1 : ℕ) : ℝ) + 1 := by
    ring
  rw [hsum]
  rw [show ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 by norm_num]
  rw [Real.Gamma_nat_eq_factorial m]
  rw [show ((m : ℝ) + 1 + 1) = ((m + 1 : ℕ) : ℝ) + 1 by norm_num]
  rw [Real.Gamma_nat_eq_factorial (m + 1)]
  rw [Nat.factorial_succ]
  have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hfac : ((Nat.factorial m : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hm1, hfac]
  norm_num
  ring

theorem betaPDFReal_one_nat_succ (m : ℕ) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    ProbabilityTheory.betaPDFReal (1 : ℝ) ((m + 1 : ℕ) : ℝ) x =
      ((m + 1 : ℕ) : ℝ) * (1 - x) ^ m := by
  rw [ProbabilityTheory.betaPDFReal, if_pos ⟨hx0, hx1⟩]
  rw [beta_one_nat_succ]
  simp [Real.rpow_natCast]

theorem betaPDFReal_one_nat_succ_eq_zero_of_one_le
    (m : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    ProbabilityTheory.betaPDFReal (1 : ℝ) ((m + 1 : ℕ) : ℝ) x = 0 := by
  simp [ProbabilityTheory.betaPDFReal, hx.not_gt]

theorem betaPDFReal_one_nat_succ_nonneg (m : ℕ) (x : ℝ) :
    0 ≤ ProbabilityTheory.betaPDFReal (1 : ℝ) ((m + 1 : ℕ) : ℝ) x := by
  by_cases hx : 0 < x ∧ x < 1
  · rw [betaPDFReal_one_nat_succ m hx.1 hx.2]
    have h1mx : 0 ≤ 1 - x := by linarith [hx.2]
    exact mul_nonneg (by positivity) (pow_nonneg h1mx m)
  · rw [ProbabilityTheory.betaPDFReal, if_neg hx]

theorem betaPDFReal_one_nat_succ_Ici_integral
    (m : ℕ) {a : ℝ} (ha0 : 0 ≤ a) :
    ∫ x in Set.Ici a,
        ProbabilityTheory.betaPDFReal (1 : ℝ) ((m + 1 : ℕ) : ℝ) x =
      ∫ x in Set.Ioo a 1, ((m + 1 : ℕ) : ℝ) * (1 - x) ^ m := by
  rw [integral_Ici_eq_integral_Ioi]
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hxa : a < x
  · by_cases hx1 : x < 1
    · have hx0 : 0 < x := lt_of_le_of_lt ha0 hxa
      rw [Set.indicator_of_mem (s := Set.Ioi a) hxa]
      rw [Set.indicator_of_mem (s := Set.Ioo a 1) ⟨hxa, hx1⟩]
      exact betaPDFReal_one_nat_succ m hx0 hx1
    · have hx1le : 1 ≤ x := le_of_not_gt hx1
      rw [Set.indicator_of_mem (s := Set.Ioi a) hxa]
      rw [Set.indicator_of_notMem (s := Set.Ioo a 1)]
      · exact betaPDFReal_one_nat_succ_eq_zero_of_one_le m hx1le
      · intro hx
        exact hx1 hx.2
  · have hxnot : x ∉ Set.Ioi a := by simpa using hxa
    have hxnotIoo : x ∉ Set.Ioo a 1 := by
      intro hx
      exact hxa hx.1
    simp [hxnot, hxnotIoo]

theorem betaPDFReal_one_nat_succ_interval_integral
    (m : ℕ) {a : ℝ} :
    (∫ x in a..1, ((m + 1 : ℕ) : ℝ) * (1 - x) ^ m) =
      (1 - a) ^ (m + 1) := by
  have hderiv : ∀ x ∈ Set.uIcc a 1,
      HasDerivAt (fun y : ℝ => - (1 - y) ^ (m + 1))
        (((m + 1 : ℕ) : ℝ) * (1 - x) ^ m) x := by
    intro x _hx
    have h1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      simpa using (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
    have h2 := h1.pow (m + 1)
    simpa [Nat.succ_eq_add_one, add_comm, add_left_comm, add_assoc,
      mul_assoc, mul_left_comm, mul_comm] using h2.neg
  have hint : IntervalIntegrable
      (fun x : ℝ => ((m + 1 : ℕ) : ℝ) * (1 - x) ^ m)
      MeasureTheory.volume a 1 := by
    exact
      (continuous_const.mul
        ((continuous_const.sub continuous_id).pow m)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp

theorem betaPDFReal_one_nat_succ_Ioo_integral
    (m : ℕ) {a : ℝ} (ha1 : a ≤ 1) :
    ∫ x in Set.Ioo a 1, ((m + 1 : ℕ) : ℝ) * (1 - x) ^ m =
      (1 - a) ^ (m + 1) := by
  rw [← integral_Ioc_eq_integral_Ioo]
  rw [← intervalIntegral.integral_of_le ha1]
  exact betaPDFReal_one_nat_succ_interval_integral m

theorem betaMeasure_one_nat_succ_real_Ici (m : ℕ) {a : ℝ} :
    (ProbabilityTheory.betaMeasure (1 : ℝ) ((m + 1 : ℕ) : ℝ)).real
        (Set.Ici a) =
      ∫ x in Set.Ici a,
        ProbabilityTheory.betaPDFReal (1 : ℝ) ((m + 1 : ℕ) : ℝ) x := by
  haveI : IsProbabilityMeasure
      (ProbabilityTheory.betaMeasure (1 : ℝ) ((m + 1 : ℕ) : ℝ)) :=
    ProbabilityTheory.isProbabilityMeasureBeta (by norm_num) (by positivity)
  rw [ProbabilityTheory.betaMeasure, measureReal_def,
    withDensity_apply _ measurableSet_Ici]
  simpa [ProbabilityTheory.betaPDF] using
    (integral_eq_lintegral_of_nonneg_ae
      (μ := MeasureTheory.volume.restrict (Set.Ici a))
      (f := ProbabilityTheory.betaPDFReal (1 : ℝ) ((m + 1 : ℕ) : ℝ))
      (Filter.Eventually.of_forall (betaPDFReal_one_nat_succ_nonneg m))
      ((ProbabilityTheory.measurable_betaPDFReal
        (1 : ℝ) ((m + 1 : ℕ) : ℝ)).aestronglyMeasurable)).symm

/-- Real upper tail of `Beta(1,m+1)` on thresholds in `[0,1]`. -/
theorem betaMeasure_one_nat_succ_real_Ici_of_mem_Icc
    (m : ℕ) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (ProbabilityTheory.betaMeasure (1 : ℝ) ((m + 1 : ℕ) : ℝ)).real
        (Set.Ici a) =
      (1 - a) ^ (m + 1) := by
  calc
    (ProbabilityTheory.betaMeasure (1 : ℝ) ((m + 1 : ℕ) : ℝ)).real
        (Set.Ici a)
        = ∫ x in Set.Ici a,
            ProbabilityTheory.betaPDFReal (1 : ℝ) ((m + 1 : ℕ) : ℝ) x := by
            rw [betaMeasure_one_nat_succ_real_Ici]
    _ = ∫ x in Set.Ioo a 1, ((m + 1 : ℕ) : ℝ) * (1 - x) ^ m := by
            exact betaPDFReal_one_nat_succ_Ici_integral m ha0
    _ = (1 - a) ^ (m + 1) :=
            betaPDFReal_one_nat_succ_Ioo_integral m ha1

/-- The `Beta(1,m+1)` upper tail is `1` below the support. -/
theorem betaMeasure_one_nat_succ_real_Ici_of_nonpos
    (m : ℕ) {a : ℝ} (ha : a ≤ 0) :
    (ProbabilityTheory.betaMeasure (1 : ℝ) ((m + 1 : ℕ) : ℝ)).real
        (Set.Ici a) = 1 := by
  let ν := ProbabilityTheory.betaMeasure (1 : ℝ) ((m + 1 : ℕ) : ℝ)
  haveI : IsProbabilityMeasure ν :=
    ProbabilityTheory.isProbabilityMeasureBeta (by norm_num) (by positivity)
  have h0 : ν.real (Set.Ici (0 : ℝ)) = 1 := by
    dsimp [ν]
    simpa using
      (betaMeasure_one_nat_succ_real_Ici_of_mem_Icc m
        (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1))
  have hsub : Set.Ici (0 : ℝ) ⊆ Set.Ici a := by
    intro x hx
    exact ha.trans hx
  have hge : (1 : ℝ) ≤ ν.real (Set.Ici a) := by
    rw [← h0]
    exact measureReal_mono hsub
  have hle : ν.real (Set.Ici a) ≤ 1 := by
    simpa using
      (measureReal_mono (μ := ν) (s₁ := Set.Ici a) (s₂ := Set.univ)
        (Set.subset_univ _))
  exact le_antisymm hle hge

/-- The `Beta(1,m+1)` upper tail is `0` above the support. -/
theorem betaMeasure_one_nat_succ_real_Ici_of_one_le
    (m : ℕ) {a : ℝ} (ha : 1 ≤ a) :
    (ProbabilityTheory.betaMeasure (1 : ℝ) ((m + 1 : ℕ) : ℝ)).real
        (Set.Ici a) = 0 := by
  let ν := ProbabilityTheory.betaMeasure (1 : ℝ) ((m + 1 : ℕ) : ℝ)
  haveI : IsProbabilityMeasure ν :=
    ProbabilityTheory.isProbabilityMeasureBeta (by norm_num) (by positivity)
  have h1 : ν.real (Set.Ici (1 : ℝ)) = 0 := by
    dsimp [ν]
    simpa using
      (betaMeasure_one_nat_succ_real_Ici_of_mem_Icc m
        (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 1))
  have hsub : Set.Ici a ⊆ Set.Ici (1 : ℝ) := by
    intro x hx
    exact ha.trans hx
  have hle : ν.real (Set.Ici a) ≤ 0 := by
    rw [← h1]
    exact measureReal_mono hsub (h₂ := measure_ne_top _ _)
  exact le_antisymm hle measureReal_nonneg

/-- Exact upper-tail identity for `Beta(1,m+1)`:

`P(T ≥ 1-r²) = r^(2(m+1))`, for `0 < r ≤ 1`.

This is the scalar Beta calculation behind the complex projective cap law. -/
theorem betaMeasure_one_nat_succ_tail
    (m : ℕ) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    (ProbabilityTheory.betaMeasure (1 : ℝ) ((m + 1 : ℕ) : ℝ)).real
        (Set.Ici (1 - r ^ 2)) =
      r ^ (2 * (m + 1)) := by
  let a : ℝ := 1 - r ^ 2
  have hr_nonneg : 0 ≤ r := le_of_lt hr
  have hr2_le_one : r ^ 2 ≤ 1 := by
    nlinarith [mul_le_mul hr1 hr1 hr_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
  have ha0 : 0 ≤ a := by
    dsimp [a]
    nlinarith
  have ha1 : a ≤ 1 := by
    dsimp [a]
    nlinarith [sq_nonneg r]
  calc
    (ProbabilityTheory.betaMeasure (1 : ℝ) ((m + 1 : ℕ) : ℝ)).real
        (Set.Ici (1 - r ^ 2))
        = ∫ x in Set.Ici a,
            ProbabilityTheory.betaPDFReal (1 : ℝ) ((m + 1 : ℕ) : ℝ) x := by
            rw [betaMeasure_one_nat_succ_real_Ici]
    _ = ∫ x in Set.Ioo a 1, ((m + 1 : ℕ) : ℝ) * (1 - x) ^ m := by
            exact betaPDFReal_one_nat_succ_Ici_integral m ha0
    _ = (1 - a) ^ (m + 1) := betaPDFReal_one_nat_succ_Ioo_integral m ha1
    _ = r ^ (2 * (m + 1)) := by
            dsimp [a]
            rw [show 1 - (1 - r ^ 2) = r ^ 2 by ring]
            rw [← pow_mul]

/-- `Beta(1,m+1)` has exactly the projective-overlap kernel in complex
dimension `m+2`. -/
theorem betaMeasure_one_nat_succ_projectiveOverlapKernelTail (m : ℕ) :
    ProjectiveOverlapKernelTail
      (ProbabilityTheory.betaMeasure (1 : ℝ) ((m + 1 : ℕ) : ℝ))
      (m + 2) where
  tail_eq := by
    intro r hr hr1
    rw [betaMeasure_one_nat_succ_tail m hr hr1]
    unfold projectiveCapKernel
    congr 1

/-- Dimension-indexed form: for `N ≥ 2`, `Beta(1,N-1)` has exactly the
projective-overlap kernel in complex dimension `N`. -/
theorem betaMeasure_one_nat_sub_projectiveOverlapKernelTail
    {N : ℕ} (hN : 2 ≤ N) :
    ProjectiveOverlapKernelTail
      (ProbabilityTheory.betaMeasure (1 : ℝ) ((N - 1 : ℕ) : ℝ)) N := by
  have hN' : N = (N - 2) + 2 := by omega
  have hNsub : N - 1 = (N - 2) + 1 := by omega
  rw [hNsub, hN']
  exact betaMeasure_one_nat_succ_projectiveOverlapKernelTail (N - 2)

/-- The `Beta(1,N-1)` upper tail is `1` below the support. -/
theorem betaMeasure_one_nat_sub_real_Ici_of_nonpos
    {N : ℕ} (hN : 2 ≤ N) {a : ℝ} (ha : a ≤ 0) :
    (ProbabilityTheory.betaMeasure (1 : ℝ) ((N - 1 : ℕ) : ℝ)).real
        (Set.Ici a) = 1 := by
  have hNsub : N - 1 = (N - 2) + 1 := by omega
  rw [hNsub]
  exact betaMeasure_one_nat_succ_real_Ici_of_nonpos (N - 2) ha

/-- The `Beta(1,N-1)` upper tail is `0` above the support. -/
theorem betaMeasure_one_nat_sub_real_Ici_of_one_le
    {N : ℕ} (hN : 2 ≤ N) {a : ℝ} (ha : 1 ≤ a) :
    (ProbabilityTheory.betaMeasure (1 : ℝ) ((N - 1 : ℕ) : ℝ)).real
        (Set.Ici a) = 0 := by
  have hNsub : N - 1 = (N - 2) + 1 := by omega
  rw [hNsub]
  exact betaMeasure_one_nat_succ_real_Ici_of_one_le (N - 2) ha

/-- Exact projective-cap tails determine the Beta law of the squared overlap.

This is the formal order of reasoning used for the intrinsic Haar cap proof:
first prove the projective cap tails

`P(T ≥ 1-r²) = r^(2(N-1))`, for all `0 ≤ r ≤ 1`,

then compare with the already-computed `Beta(1,N-1)` tails and conclude
equality of laws by upper-ray extensionality. -/
theorem projectiveOverlapSqLaw_eq_betaMeasure_of_projective_tail_eq
    {μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)}
    [IsProbabilityMeasure μ]
    {e : EuclideanSpace ℂ ι} {N : ℕ}
    (hN : 2 ≤ N) (he : ‖e‖ = 1)
    (hTail :
      ∀ {r : ℝ}, 0 ≤ r → r ≤ 1 →
        (projectiveOverlapSqLaw (ι := ι) μ e).real
          (Set.Ici (1 - r ^ 2)) =
            r ^ (2 * (N - 1))) :
    projectiveOverlapSqLaw (ι := ι) μ e =
      ProbabilityTheory.betaMeasure (1 : ℝ) ((N - 1 : ℕ) : ℝ) := by
  let ν := projectiveOverlapSqLaw (ι := ι) μ e
  let β := ProbabilityTheory.betaMeasure (1 : ℝ) ((N - 1 : ℕ) : ℝ)
  haveI : IsProbabilityMeasure ν := by
    unfold ν projectiveOverlapSqLaw
    exact Measure.isProbabilityMeasure_map
      (measurable_projectiveOverlapSq (ι := ι) e).aemeasurable
  haveI : IsProbabilityMeasure β :=
    ProbabilityTheory.isProbabilityMeasureBeta
      (by norm_num) (by
        have hpos : 0 < ((N - 1 : ℕ) : ℝ) := by
          exact_mod_cast (Nat.sub_pos_of_lt hN)
        exact hpos)
  apply Measure.ext_of_Ici
  intro a
  have hreal : ν.real (Set.Ici a) = β.real (Set.Ici a) := by
    by_cases ha_nonpos : a ≤ 0
    · have hν : ν.real (Set.Ici a) = 1 := by
        simpa [ν] using
          projectiveOverlapSqLaw_real_Ici_of_nonpos
            (ι := ι) (μ := μ) he ha_nonpos
      have hβ : β.real (Set.Ici a) = 1 := by
        simpa [β] using
          betaMeasure_one_nat_sub_real_Ici_of_nonpos hN ha_nonpos
      rw [hν, hβ]
    · have ha_pos : 0 < a := lt_of_not_ge ha_nonpos
      by_cases ha_lt_one : a < 1
      · let r : ℝ := Real.sqrt (1 - a)
        have h1a_pos : 0 < 1 - a := sub_pos.mpr ha_lt_one
        have hr_nonneg : 0 ≤ r := Real.sqrt_nonneg (1 - a)
        have hr_pos : 0 < r := Real.sqrt_pos.2 h1a_pos
        have hr_le_one : r ≤ 1 := by
          dsimp [r]
          rw [Real.sqrt_le_one]
          linarith
        have hthreshold : 1 - r ^ 2 = a := by
          dsimp [r]
          rw [Real.sq_sqrt (le_of_lt h1a_pos)]
          ring
        have hν :
            ν.real (Set.Ici (1 - r ^ 2)) =
              r ^ (2 * (N - 1)) := by
          simpa [ν] using hTail hr_nonneg hr_le_one
        have hβ :
            β.real (Set.Ici (1 - r ^ 2)) =
              r ^ (2 * (N - 1)) := by
          have hβtail :=
            (betaMeasure_one_nat_sub_projectiveOverlapKernelTail hN).tail_eq
              hr_pos hr_le_one
          simpa [β, projectiveCapKernel] using hβtail
        calc
          ν.real (Set.Ici a)
              = ν.real (Set.Ici (1 - r ^ 2)) := by rw [hthreshold]
          _ = r ^ (2 * (N - 1)) := hν
          _ = β.real (Set.Ici (1 - r ^ 2)) := hβ.symm
          _ = β.real (Set.Ici a) := by rw [hthreshold]
      · have ha_one_le : 1 ≤ a := le_of_not_gt ha_lt_one
        have hν1 : ν.real (Set.Ici (1 : ℝ)) = 0 := by
          have h0 := hTail (r := 0) (by norm_num : (0 : ℝ) ≤ 0)
            (by norm_num : (0 : ℝ) ≤ 1)
          have hpow : (0 : ℝ) ^ (2 * (N - 1)) = 0 := by
            have hne : 2 * (N - 1) ≠ 0 := by omega
            exact zero_pow hne
          simpa [ν, hpow] using h0
        have hν : ν.real (Set.Ici a) = 0 := by
          have hsub : Set.Ici a ⊆ Set.Ici (1 : ℝ) := by
            intro x hx
            exact ha_one_le.trans hx
          have hle : ν.real (Set.Ici a) ≤ 0 := by
            rw [← hν1]
            exact measureReal_mono hsub (h₂ := measure_ne_top _ _)
          exact le_antisymm hle measureReal_nonneg
        have hβ : β.real (Set.Ici a) = 0 := by
          simpa [β] using
            betaMeasure_one_nat_sub_real_Ici_of_one_le hN ha_one_le
        rw [hν, hβ]
  exact
    (measureReal_eq_measureReal_iff
      (μ := ν) (ν := β) (s := Set.Ici a)
      (measure_ne_top _ _) (measure_ne_top _ _)).mp hreal

/-- Exact projective-cap probabilities imply the `Beta(1,N-1)` law of the
squared projective overlap.

This is the direct geometric-to-probabilistic step:

* the cap identity gives
  `μ {u | |⟪e,u⟫|² ≥ 1-r²} = r^(2(N-1))`;
* `projectiveOverlapSqLaw_tail_eq_capProbability` rewrites this as an upper
  `Ici` tail identity for `T = |⟪e,u⟫|²`;
* `projectiveOverlapSqLaw_eq_betaMeasure_of_projective_tail_eq` compares those
  upper tails with the scalar `Beta(1,N-1)` tails and applies real-line
  measure extensionality. -/
theorem projectiveOverlapSqLaw_eq_betaMeasure_of_projectiveCapProbability_eq
    {μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)}
    [IsProbabilityMeasure μ]
    {e : EuclideanSpace ℂ ι} {N : ℕ}
    (hN : 2 ≤ N) (he : ‖e‖ = 1)
    (hCap :
      ∀ {r : ℝ}, 0 ≤ r → r ≤ 1 →
        projectiveCapProbability (ι := ι) μ e r =
          r ^ (2 * (N - 1))) :
    projectiveOverlapSqLaw (ι := ι) μ e =
      ProbabilityTheory.betaMeasure (1 : ℝ) ((N - 1 : ℕ) : ℝ) := by
  refine
    projectiveOverlapSqLaw_eq_betaMeasure_of_projective_tail_eq
      (ι := ι) hN he ?_
  intro r hr0 hr1
  calc
    (projectiveOverlapSqLaw (ι := ι) μ e).real
        (Set.Ici (1 - r ^ 2))
        = projectiveCapProbability (ι := ι) μ e r := by
            rw [projectiveOverlapSqLaw_tail_eq_capProbability]
    _ = r ^ (2 * (N - 1)) := hCap hr0 hr1

/-- Exact projective-cap probabilities imply the `HasLaw` statement

`|⟪e,u⟫|² ∼ Beta(1,N-1)`.

This is the theorem form closest to the mathematical sentence
“deduce the Beta law by comparison of `Ici` tails.” -/
theorem hasLaw_projectiveOverlapSq_betaMeasure_of_projectiveCapProbability_eq
    {μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)}
    [IsProbabilityMeasure μ]
    {e : EuclideanSpace ℂ ι} {N : ℕ}
    (hN : 2 ≤ N) (he : ‖e‖ = 1)
    (hCap :
      ∀ {r : ℝ}, 0 ≤ r → r ≤ 1 →
        projectiveCapProbability (ι := ι) μ e r =
          r ^ (2 * (N - 1))) :
    ProbabilityTheory.HasLaw (projectiveOverlapSq (ι := ι) e)
      (ProbabilityTheory.betaMeasure (1 : ℝ) ((N - 1 : ℕ) : ℝ)) μ where
  aemeasurable :=
    (measurable_projectiveOverlapSq (ι := ι) e).aemeasurable
  map_eq :=
    projectiveOverlapSqLaw_eq_betaMeasure_of_projectiveCapProbability_eq
      (ι := ι) hN he hCap

/-- A coordinate cone-volume formula implies the exact projective-cap
probability.

This is the non-circular bridge from the geometric computation to the cap
tail.  The input `hCoord` is only the coordinate-volume identity

`projectiveCapProbability μ e r = projectiveConeCoordinateRatio (N-1) r`

for `0 ≤ r < 1`.  The scalar theorem
`projectiveConeCoordinateRatio_eq_pow` then evaluates the ratio as
`r^(2(N-1))`; the endpoint `r=1` is handled directly because the cap is the
whole sphere. -/
theorem projectiveCapProbability_eq_pow_of_projectiveConeCoordinateRatio_eq
    {μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)}
    [IsProbabilityMeasure μ]
    {e : EuclideanSpace ℂ ι} {N : ℕ}
    (hCoord :
      ∀ {r : ℝ}, 0 ≤ r → r < 1 →
        projectiveCapProbability (ι := ι) μ e r =
          projectiveConeCoordinateRatio (N - 1) r) :
    ∀ {r : ℝ}, 0 ≤ r → r ≤ 1 →
      projectiveCapProbability (ι := ι) μ e r =
        r ^ (2 * (N - 1)) := by
  intro r hr0 hr1
  by_cases hrlt : r < 1
  · rw [hCoord hr0 hrlt]
    exact projectiveConeCoordinateRatio_eq_pow (N - 1) hr0 hrlt
  · have hr_eq : r = 1 := le_antisymm hr1 (le_of_not_gt hrlt)
    subst r
    have hcap_univ :
        projectiveCapSet (ι := ι) e (1 : ℝ) =
          Set.univ := by
      ext u
      simp [projectiveCapSet]
    rw [projectiveCapProbability, hcap_univ]
    simp

/-- Coordinate cone-volume formula implies the `Beta(1,N-1)` law of the
squared projective overlap, without assuming any Beta law for Haar measure.

The dependency order is:

1. prove the cone-coordinate probability identity `hCoord`;
2. evaluate the scalar coordinate integral by
   `projectiveConeCoordinateRatio_eq_pow`;
3. obtain exact projective-cap tails;
4. compare those tails with the scalar `Beta(1,N-1)` tails. -/
theorem projectiveOverlapSqLaw_eq_betaMeasure_of_projectiveConeCoordinateRatio_eq
    {μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)}
    [IsProbabilityMeasure μ]
    {e : EuclideanSpace ℂ ι} {N : ℕ}
    (hN : 2 ≤ N) (he : ‖e‖ = 1)
    (hCoord :
      ∀ {r : ℝ}, 0 ≤ r → r < 1 →
        projectiveCapProbability (ι := ι) μ e r =
          projectiveConeCoordinateRatio (N - 1) r) :
    projectiveOverlapSqLaw (ι := ι) μ e =
      ProbabilityTheory.betaMeasure (1 : ℝ) ((N - 1 : ℕ) : ℝ) := by
  exact
    projectiveOverlapSqLaw_eq_betaMeasure_of_projectiveCapProbability_eq
      (ι := ι) hN he
      (projectiveCapProbability_eq_pow_of_projectiveConeCoordinateRatio_eq
        (ι := ι) (e := e) (N := N) hCoord)

/-- `HasLaw` form of
`projectiveOverlapSqLaw_eq_betaMeasure_of_projectiveConeCoordinateRatio_eq`. -/
theorem hasLaw_projectiveOverlapSq_betaMeasure_of_projectiveConeCoordinateRatio_eq
    {μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)}
    [IsProbabilityMeasure μ]
    {e : EuclideanSpace ℂ ι} {N : ℕ}
    (hN : 2 ≤ N) (he : ‖e‖ = 1)
    (hCoord :
      ∀ {r : ℝ}, 0 ≤ r → r < 1 →
        projectiveCapProbability (ι := ι) μ e r =
          projectiveConeCoordinateRatio (N - 1) r) :
    ProbabilityTheory.HasLaw (projectiveOverlapSq (ι := ι) e)
      (ProbabilityTheory.betaMeasure (1 : ℝ) ((N - 1 : ℕ) : ℝ)) μ where
  aemeasurable :=
    (measurable_projectiveOverlapSq (ι := ι) e).aemeasurable
  map_eq :=
    projectiveOverlapSqLaw_eq_betaMeasure_of_projectiveConeCoordinateRatio_eq
      (ι := ι) hN he hCoord

/-- Exact squared-overlap tail law implies exact geometric projective cap
volume. -/
theorem ProjectiveOverlapKernelTail.toProjectiveCapExactVolume
    {μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)}
    {ν : Measure ℝ} {e : EuclideanSpace ℂ ι} {N : ℕ} {r : ℝ}
    (I : ProjectiveOverlapKernelTail ν N)
    (hLaw : projectiveOverlapSqLaw (ι := ι) μ e = ν)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    ProjectiveCapExactVolume (ι := ι) μ e N r where
  radius_pos := hr
  prob_eq := by
    calc
      projectiveCapProbability (ι := ι) μ e r
          = (projectiveOverlapSqLaw (ι := ι) μ e).real
              (Set.Ici (1 - r ^ 2)) := by
                rw [projectiveOverlapSqLaw_tail_eq_capProbability]
      _ = ν.real (Set.Ici (1 - r ^ 2)) := by rw [hLaw]
      _ = projectiveCapKernel N r := I.tail_eq hr hr1

/-- Unit-vector theorem form of the exact spherical cap law, obtained once the
squared-overlap law has been identified with the projective kernel.

This is the preferred local theorem to instantiate for the Haar/surface
measure: it records both the exact cap probability and the required
normalization of the cap center. -/
theorem ProjectiveOverlapKernelTail.toUnitProjectiveCapExactVolume
    {μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)}
    {ν : Measure ℝ} {e : EuclideanSpace ℂ ι} {N : ℕ} {r : ℝ}
    (I : ProjectiveOverlapKernelTail ν N)
    (he : ‖e‖ = 1)
    (hLaw : projectiveOverlapSqLaw (ι := ι) μ e = ν)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    UnitProjectiveCapExactVolume (ι := ι) μ e N r where
  unit_vector := he
  radius_pos := hr
  prob_eq :=
    (I.toProjectiveCapExactVolume
      (μ := μ) (e := e) (r := r) hLaw hr hr1).prob_eq

/-- Same conversion, stated from a `HasLaw` hypothesis for the squared
overlap. -/
theorem ProjectiveOverlapKernelTail.toProjectiveCapExactVolume_of_hasLaw
    {μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)}
    {ν : Measure ℝ} {e : EuclideanSpace ℂ ι} {N : ℕ} {r : ℝ}
    (I : ProjectiveOverlapKernelTail ν N)
    (hLaw : ProbabilityTheory.HasLaw (projectiveOverlapSq (ι := ι) e) ν μ)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    ProjectiveCapExactVolume (ι := ι) μ e N r :=
  I.toProjectiveCapExactVolume (μ := μ) (e := e) (r := r)
    hLaw.map_eq hr hr1

/-- Same unit-vector conversion, stated from a `HasLaw` hypothesis for the
squared overlap. -/
theorem ProjectiveOverlapKernelTail.toUnitProjectiveCapExactVolume_of_hasLaw
    {μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)}
    {ν : Measure ℝ} {e : EuclideanSpace ℂ ι} {N : ℕ} {r : ℝ}
    (I : ProjectiveOverlapKernelTail ν N)
    (he : ‖e‖ = 1)
    (hLaw : ProbabilityTheory.HasLaw (projectiveOverlapSq (ι := ι) e) ν μ)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    UnitProjectiveCapExactVolume (ι := ι) μ e N r :=
  I.toUnitProjectiveCapExactVolume (μ := μ) (e := e) (r := r)
    he hLaw.map_eq hr hr1

/-- If the squared overlap with a unit vector has law `Beta(1,N-1)`, then the
projective cap has the exact Haar/Beta volume `r^(2(N-1))`.

This is the local “Haar → Beta → cap” bridge.  The genuinely geometric
Haar-to-Beta input is the `HasLaw` hypothesis; the Beta tail and cap conversion
are proved here with no further assumptions. -/
theorem betaMeasure_one_nat_sub_hasLaw_toUnitProjectiveCapExactVolume
    {μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)}
    {e : EuclideanSpace ℂ ι} {N : ℕ} {r : ℝ}
    (hN : 2 ≤ N) (he : ‖e‖ = 1)
    (hLaw :
      ProbabilityTheory.HasLaw (projectiveOverlapSq (ι := ι) e)
        (ProbabilityTheory.betaMeasure (1 : ℝ) ((N - 1 : ℕ) : ℝ)) μ)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    UnitProjectiveCapExactVolume (ι := ι) μ e N r :=
  ProjectiveOverlapKernelTail.toUnitProjectiveCapExactVolume_of_hasLaw
    (betaMeasure_one_nat_sub_projectiveOverlapKernelTail hN) he hLaw hr hr1

/-- Exact cap identity from the `Beta(1,N-1)` squared-overlap law.

This is the literal finite-dimensional formula

`σ {u : S(ℂ^N) | |⟪e,u⟫|² ≥ 1 - r²} = r^(2(N-1))`

written in the project's cap notation.  The only probabilistic input is the
`HasLaw` statement identifying the squared overlap with `Beta(1,N-1)`; the
Beta tail integral and the conversion from the tail to the cap set are proved
above. -/
theorem projectiveCapSet_measureReal_eq_pow_of_hasLaw_betaMeasure
    {μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)}
    {e : EuclideanSpace ℂ ι} {N : ℕ} {r : ℝ}
    (hN : 2 ≤ N) (he : ‖e‖ = 1)
    (hLaw :
      ProbabilityTheory.HasLaw (projectiveOverlapSq (ι := ι) e)
        (ProbabilityTheory.betaMeasure (1 : ℝ) ((N - 1 : ℕ) : ℝ)) μ)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    μ.real (projectiveCapSet (ι := ι) e r) =
      r ^ (2 * (N - 1)) := by
  have H :=
    betaMeasure_one_nat_sub_hasLaw_toUnitProjectiveCapExactVolume
      (ι := ι) hN he hLaw hr hr1
  simpa [projectiveCapProbability, projectiveCapKernel] using H.prob_eq

/-! #### Exact Haar/projective overlap law interface -/

/-- Exact projective-overlap law for a complex spherical law.

For a Haar vector `u` on the unit sphere of `ℂ^N`, and every unit vector `e`,
the random variable `|⟪e,u⟫|²` has law `Beta(1,N-1)`.  This structure records
exactly that finite-dimensional theorem.  The scalar `Beta → r^(2(N-1))`
calculation and the cap conversion are proved below, so downstream arguments
only have to provide this single geometric law. -/
structure HaarProjectiveOverlapBetaLaw
    (μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)) : Prop where
  dimension_ge_two : 2 ≤ Fintype.card ι
  overlap_hasLaw :
    ∀ {e : EuclideanSpace ℂ ι}, ‖e‖ = 1 →
      ProbabilityTheory.HasLaw (projectiveOverlapSq (ι := ι) e)
        (ProbabilityTheory.betaMeasure (1 : ℝ)
          (((Fintype.card ι) - 1 : ℕ) : ℝ)) μ

/-- Tail-extensional constructor for the exact Haar/projective-overlap law.

To prove `HaarProjectiveOverlapBetaLaw μ`, it is enough to prove that for
every unit vector `e`, the push-forward law of `|⟪e,u⟫|²` has the same upper
tails on all intervals `Ici a` as `Beta(1,N-1)`.  The proof uses the standard
real-line measure extensionality theorem for upper rays.

This theorem is deliberately stated with **all** upper rays `Ici a`, not only
the cap thresholds `a = 1-r²`; this avoids hiding atom/boundary obligations. -/
theorem HaarProjectiveOverlapBetaLaw.of_forall_Ici_tail_eq_beta
    {μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)}
    [IsProbabilityMeasure μ]
    (hN : 2 ≤ Fintype.card ι)
    (hTail :
      ∀ {e : EuclideanSpace ℂ ι}, ‖e‖ = 1 → ∀ a : ℝ,
        (projectiveOverlapSqLaw (ι := ι) μ e).real (Set.Ici a) =
          (ProbabilityTheory.betaMeasure (1 : ℝ)
            (((Fintype.card ι) - 1 : ℕ) : ℝ)).real (Set.Ici a)) :
    HaarProjectiveOverlapBetaLaw (ι := ι) μ where
  dimension_ge_two := hN
  overlap_hasLaw := by
    intro e he
    let νβ : Measure ℝ :=
      ProbabilityTheory.betaMeasure (1 : ℝ)
        (((Fintype.card ι) - 1 : ℕ) : ℝ)
    haveI : IsProbabilityMeasure νβ :=
      ProbabilityTheory.isProbabilityMeasureBeta
        (by norm_num) (by
          have hpos : 0 < ((Fintype.card ι - 1 : ℕ) : ℝ) := by
            exact_mod_cast (Nat.sub_pos_of_lt hN)
          exact hpos)
    haveI : IsProbabilityMeasure (projectiveOverlapSqLaw (ι := ι) μ e) := by
      unfold projectiveOverlapSqLaw
      exact Measure.isProbabilityMeasure_map
        (measurable_projectiveOverlapSq (ι := ι) e).aemeasurable
    have hmap :
        projectiveOverlapSqLaw (ι := ι) μ e = νβ := by
      apply Measure.ext_of_Ici
      intro a
      exact
        (measureReal_eq_measureReal_iff
          (μ := projectiveOverlapSqLaw (ι := ι) μ e)
          (ν := νβ)
          (s := Set.Ici a)
          (measure_ne_top _ _) (measure_ne_top _ _)).mp
          (by
            simpa [νβ] using hTail he a)
    exact
      { aemeasurable :=
          (measurable_projectiveOverlapSq (ι := ι) e).aemeasurable
        map_eq := by
          simpa [projectiveOverlapSqLaw, νβ] using hmap }

/-- Constructor from exact projective cap tails.

This is the intended intrinsic order:

1. prove the projective cap tail
   `P(|⟪e,u⟫|² ≥ 1-r²) = r^(2(N-1))`;
2. compare it with the scalar `Beta(1,N-1)` tail calculation;
3. conclude the Beta law by upper-ray extensionality. -/
theorem HaarProjectiveOverlapBetaLaw.of_projective_tail_eq
    {μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)}
    [IsProbabilityMeasure μ]
    (hN : 2 ≤ Fintype.card ι)
    (hTail :
      ∀ {e : EuclideanSpace ℂ ι}, ‖e‖ = 1 →
        ∀ {r : ℝ}, 0 ≤ r → r ≤ 1 →
          (projectiveOverlapSqLaw (ι := ι) μ e).real
            (Set.Ici (1 - r ^ 2)) =
              r ^ (2 * (Fintype.card ι - 1))) :
    HaarProjectiveOverlapBetaLaw (ι := ι) μ where
  dimension_ge_two := hN
  overlap_hasLaw := by
    intro e he
    refine
      { aemeasurable :=
          (measurable_projectiveOverlapSq (ι := ι) e).aemeasurable
        map_eq := ?_ }
    exact
      projectiveOverlapSqLaw_eq_betaMeasure_of_projective_tail_eq
        (ι := ι) hN he (hTail he)

/-- Constructor from exact projective cap probabilities.

This is the same intrinsic constructor as
`HaarProjectiveOverlapBetaLaw.of_projective_tail_eq`, but stated in terms of
the geometric cap probability
`σ {u : sphere | |⟪e,u⟫|² ≥ 1-r²}`.  It is the direct bridge from the
coordinate cone-volume computation to the Beta law of the squared overlap. -/
theorem HaarProjectiveOverlapBetaLaw.of_projectiveCapProbability_eq
    {μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)}
    [IsProbabilityMeasure μ]
    (hN : 2 ≤ Fintype.card ι)
    (hCap :
      ∀ {e : EuclideanSpace ℂ ι}, ‖e‖ = 1 →
        ∀ {r : ℝ}, 0 ≤ r → r ≤ 1 →
          projectiveCapProbability (ι := ι) μ e r =
            r ^ (2 * (Fintype.card ι - 1))) :
    HaarProjectiveOverlapBetaLaw (ι := ι) μ where
  dimension_ge_two := hN
  overlap_hasLaw := by
    intro e he
    exact
      hasLaw_projectiveOverlapSq_betaMeasure_of_projectiveCapProbability_eq
        (ι := ι) hN he (hCap he)

/-- Constructor from the coordinate cone-volume formula.

This is the preferred non-circular constructor for the Haar/projective Beta
law: it does not assume a Beta law and does not assume exact cap tails.  It
assumes only the geometric coordinate-ratio identity for the cap probability;
the exact tail and the Beta law are then derived inside the proof. -/
theorem HaarProjectiveOverlapBetaLaw.of_projectiveConeCoordinateRatio_eq
    {μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)}
    [IsProbabilityMeasure μ]
    (hN : 2 ≤ Fintype.card ι)
    (hCoord :
      ∀ {e : EuclideanSpace ℂ ι}, ‖e‖ = 1 →
        ∀ {r : ℝ}, 0 ≤ r → r < 1 →
          projectiveCapProbability (ι := ι) μ e r =
            projectiveConeCoordinateRatio (Fintype.card ι - 1) r) :
    HaarProjectiveOverlapBetaLaw (ι := ι) μ where
  dimension_ge_two := hN
  overlap_hasLaw := by
    intro e he
    exact
      hasLaw_projectiveOverlapSq_betaMeasure_of_projectiveConeCoordinateRatio_eq
        (ι := ι) hN he (hCoord he)

/-- Canonical normalized surface probability measure on the complex unit
sphere, in the ambient `EuclideanSpace ℂ ι` form used by the projective-cap
calculation. -/
noncomputable abbrev surfaceMeasure (ι : Type*) [Fintype ι]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere)] :
    Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1) :=
  ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere.toFinite)

set_option linter.unusedSectionVars false in
/-- The normalized surface measure on a nonempty complex unit sphere is a
probability measure. -/
theorem surfaceMeasure_isProbabilityMeasure (ι : Type*) [Fintype ι] [Nonempty ι]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere)] :
    IsProbabilityMeasure (surfaceMeasure ι) := by
  unfold surfaceMeasure
  haveI : NeZero
      ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere) :=
    ⟨Measure.toSphere_ne_zero
      (μ := (MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)))⟩
  infer_instance

/-- Ambient version of the canonical surface probability measure on the complex
unit sphere.  This is the law of a vector already viewed in
`EuclideanSpace ℂ ι`, rather than in the sphere subtype. -/
noncomputable def surfaceMeasureAmbient (ι : Type*) [Fintype ι]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere)] :
    Measure (EuclideanSpace ℂ ι) :=
  Measure.map Subtype.val (surfaceMeasure ι)

instance surfaceMeasureAmbient.instIsFiniteMeasure (ι : Type*) [Fintype ι]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere)] :
    IsFiniteMeasure (surfaceMeasureAmbient ι) := by
  unfold surfaceMeasureAmbient
  infer_instance

set_option linter.unusedSectionVars false in
/-- The ambient surface measure is still a probability measure after embedding
the sphere subtype into the ambient Euclidean space. -/
theorem surfaceMeasureAmbient_isProbabilityMeasure (ι : Type*) [Fintype ι] [Nonempty ι]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere)] :
    IsProbabilityMeasure (surfaceMeasureAmbient ι) := by
  unfold surfaceMeasureAmbient
  letI : IsProbabilityMeasure (surfaceMeasure ι) :=
    surfaceMeasure_isProbabilityMeasure ι
  exact Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable

theorem surfaceMeasureAmbient_apply_eq_inv_mul_toSphere_preimage
    (ι : Type*) [Fintype ι] [Nonempty ι]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere)]
    {s : Set (EuclideanSpace ℂ ι)}
    (hs : MeasurableSet s) :
    surfaceMeasureAmbient ι s =
      ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere
          (Set.univ :
            Set (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)))⁻¹ *
        (MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere
          ((Subtype.val :
              Metric.sphere (0 : EuclideanSpace ℂ ι) 1 →
                EuclideanSpace ℂ ι) ⁻¹' s) := by
  rw [surfaceMeasureAmbient]
  rw [Measure.map_apply measurable_subtype_coe hs]
  unfold surfaceMeasure
  unfold Measure.toFinite
  rw [Measure.toFiniteAux,
    if_pos (inferInstance :
      IsFiniteMeasure
        ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere))]
  rw [ProbabilityTheory.cond_apply MeasurableSet.univ
    ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere)]
  simp only [Set.univ_inter]

theorem toSphere_preimage_eq_total_mul_surfaceMeasureAmbient
    (ι : Type*) [Fintype ι] [Nonempty ι]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere)]
    {s : Set (EuclideanSpace ℂ ι)}
    (hs : MeasurableSet s) :
    (MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere
        ((Subtype.val :
            Metric.sphere (0 : EuclideanSpace ℂ ι) 1 →
              EuclideanSpace ℂ ι) ⁻¹' s) =
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere
          (Set.univ :
            Set (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)) *
        surfaceMeasureAmbient ι s := by
  let μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1) :=
    (MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere
  let usphere : Set (Metric.sphere (0 : EuclideanSpace ℂ ι) 1) := Set.univ
  have hμ0 : μ usphere ≠ 0 := by
    have hne : μ ≠ 0 := Measure.toSphere_ne_zero
      (μ := (MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)))
    exact mt (Measure.measure_univ_eq_zero (μ := μ)).1 hne
  have hμt : μ usphere ≠ ∞ := by
    exact measure_ne_top _ _
  calc
    μ
        ((Subtype.val :
            Metric.sphere (0 : EuclideanSpace ℂ ι) 1 →
              EuclideanSpace ℂ ι) ⁻¹' s) =
      (μ usphere * (μ usphere)⁻¹) *
        μ
          ((Subtype.val :
              Metric.sphere (0 : EuclideanSpace ℂ ι) 1 →
                EuclideanSpace ℂ ι) ⁻¹' s) := by
          rw [ENNReal.mul_inv_cancel hμ0 hμt, one_mul]
    _ =
      μ usphere *
        ((μ usphere)⁻¹ *
          μ
            ((Subtype.val :
                Metric.sphere (0 : EuclideanSpace ℂ ι) 1 →
                  EuclideanSpace ℂ ι) ⁻¹' s)) := by
          ac_rfl
    _ = μ usphere * surfaceMeasureAmbient ι s := by
          rw [surfaceMeasureAmbient_apply_eq_inv_mul_toSphere_preimage
            (ι := ι) hs]
    _ =
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere
          (Set.univ :
            Set (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)) *
        surfaceMeasureAmbient ι s := by
          rfl

/-- The canonical surface probability measure on the complex unit sphere is
invariant under every complex linear isometry.

This is the ambient `EuclideanSpace ℂ ι` analogue of the already-used sample
matrix surface invariance theorem.  It follows from Mathlib's fact that real
linear isometries preserve Lebesgue measure, transported to the sphere by
`Measure.toSphere`. -/
theorem surfaceMeasure_map_complexLinearIsometryEquiv
    [Nonempty ι]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere)]
    (V : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι) :
    Measure.map (Subtype.map V (fun _ hx => by simpa using hx))
        (surfaceMeasure ι) = surfaceMeasure ι := by
  let U : EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℂ ι :=
    IsometryEquiv.toRealLinearIsometryEquivOfMapZero V.toIsometryEquiv
      (by simp : V.toIsometryEquiv 0 = 0)
  let S : Metric.sphere (0 : EuclideanSpace ℂ ι) 1 →
      Metric.sphere (0 : EuclideanSpace ℂ ι) 1 :=
    Subtype.map U (fun _ hx => by simpa using hx)
  have hS_meas : Measurable S :=
    U.continuous.subtype_map (fun _ hx => by simpa using hx) |>.measurable
  let μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1) :=
    (MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere
  have hμ_map : Measure.map S μ = μ := by
    have hvol :
        Measure.map U
            (MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)) =
          (MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)) :=
      U.measurePreserving.map_eq
    exact toSphere_map_linearIsometryEquiv_of_map_eq
      (μ := (MeasureTheory.volume : Measure (EuclideanSpace ℂ ι))) U hvol
  have hμ_fin : IsFiniteMeasure μ := ⟨by
    have hball_lt_top :
        (MeasureTheory.volume : Measure (EuclideanSpace ℂ ι))
            (Metric.ball (0 : EuclideanSpace ℂ ι) 1) < ∞ := by
      exact lt_of_le_of_lt
        (measure_mono Metric.ball_subset_closedBall)
        ((isCompact_closedBall (0 : EuclideanSpace ℂ ι) 1).measure_lt_top)
    unfold μ
    rw [Measure.toSphere_apply_univ]
    exact ENNReal.mul_lt_top (by simp) hball_lt_top⟩
  have htoFinite : μ.toFinite = ProbabilityTheory.cond μ Set.univ := by
    unfold Measure.toFinite
    rw [Measure.toFiniteAux, if_pos hμ_fin]
  have hmapS : Measure.map S μ.toFinite = μ.toFinite := by
    ext t ht
    rw [Measure.map_apply hS_meas ht]
    rw [htoFinite]
    rw [ProbabilityTheory.cond_apply MeasurableSet.univ μ]
    rw [ProbabilityTheory.cond_apply MeasurableSet.univ μ]
    have hpre : μ (S ⁻¹' t) = μ t := by
      have h := congrArg
        (fun ν : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1) =>
          ν t) hμ_map
      simpa [Measure.map_apply hS_meas ht] using h
    simp [hpre]
  change
    Measure.map (Subtype.map V (fun _ hx => by simpa using hx)) μ.toFinite =
      μ.toFinite
  simpa [U, S] using hmapS

/-- The same invariance, phrased for the registered action of the matrix
unitary group on the complex unit sphere. -/
theorem surfaceMeasure_map_matrixUnitary
    [DecidableEq ι] [Nonempty ι]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere)]
    (U : Matrix.unitaryGroup ι ℂ) :
    Measure.map
        (fun u : Metric.sphere (0 : EuclideanSpace ℂ ι) 1 => U • u)
        (surfaceMeasure ι) = surfaceMeasure ι := by
  have h :=
    surfaceMeasure_map_complexLinearIsometryEquiv
      (ι := ι) (matrixUnitaryLinearIsometryEquiv U)
  simpa [matrixUnitaryLinearIsometryEquiv_sphereMap_eq_smul (ι := ι) U]
    using h

/-- The coordinate unit vector used as the reference centre in the cone
calculation. -/
noncomputable def coordinateUnitVector [DecidableEq ι] (i₀ : ι) :
    EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (Pi.single i₀ (1 : ℂ))

theorem norm_coordinateUnitVector [DecidableEq ι] (i₀ : ι) :
    ‖coordinateUnitVector (ι := ι) i₀‖ = 1 := by
  have hsq :
      ‖coordinateUnitVector (ι := ι) i₀‖ ^ 2 = 1 := by
    dsimp [coordinateUnitVector]
    rw [PiLp.norm_sq_eq_of_L2]
    rw [Finset.sum_eq_single i₀]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hnot
      simp at hnot
  nlinarith [norm_nonneg (coordinateUnitVector (ι := ι) i₀)]

/-- Reference-centre version of the surface cone-coordinate formula.

This is the genuinely analytic volume calculation left after unitary
invariance: one only has to compute the cone around a coordinate vector, i.e.
the `z ⊕ y` integral. -/
def SurfaceReferenceProjectiveCapConeCoordinateFormula
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere)]
    (i₀ : ι) : Prop :=
  ∀ {r : ℝ}, 0 ≤ r → r < 1 →
    projectiveCapProbability (ι := ι) (surfaceMeasure ι)
        (coordinateUnitVector (ι := ι) i₀) r =
      projectiveConeCoordinateRatio (Fintype.card ι - 1) r

/-- The single remaining geometric statement needed to make the Haar/projective
Beta law completely no-input.

For the actual normalized surface law
`(volume : Measure (EuclideanSpace ℂ ι)).toSphere.toFinite`, this says that
the cap probability is exactly the coordinate cone ratio obtained by writing
`x = z ⊕ y`.  Proving this statement is precisely the formal version of the
Fubini/polar-coordinate cone-volume computation. -/
def SurfaceProjectiveCapConeCoordinateFormula (ι : Type*) [Fintype ι]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere)] :
    Prop :=
  ∀ {e : EuclideanSpace ℂ ι}, ‖e‖ = 1 →
    ∀ {r : ℝ}, 0 ≤ r → r < 1 →
      projectiveCapProbability (ι := ι) (surfaceMeasure ι) e r =
        projectiveConeCoordinateRatio (Fintype.card ι - 1) r

/-- Unitary invariance reduces the full surface cone-coordinate formula to the
single reference-centre cone-volume computation. -/
theorem SurfaceProjectiveCapConeCoordinateFormula.of_reference
    [DecidableEq ι] [Nonempty ι]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere)]
    (i₀ : ι)
    (hRef : SurfaceReferenceProjectiveCapConeCoordinateFormula ι i₀) :
    SurfaceProjectiveCapConeCoordinateFormula ι := by
  intro e he r hr0 hr1
  have hmove :
      projectiveCapProbability (ι := ι) (surfaceMeasure ι) e r =
        projectiveCapProbability (ι := ι) (surfaceMeasure ι)
          (coordinateUnitVector (ι := ι) i₀) r :=
    projectiveCapProbability_eq_reference_of_unitary_invariant
      (ι := ι) (μ := surfaceMeasure ι)
      (fun U => surfaceMeasure_map_matrixUnitary (ι := ι) U)
      (norm_coordinateUnitVector (ι := ι) i₀) he r
  rw [hmove]
  exact hRef hr0 hr1

/-- Once the concrete cone-coordinate volume formula is proved for surface
measure, the exact Haar/projective `Beta(1,N-1)` law follows with no further
input. -/
theorem surfaceHaarProjectiveOverlapBetaLaw_of_coneCoordinateFormula
    [Nonempty ι]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere)]
    (hN : 2 ≤ Fintype.card ι)
    (hCoord : SurfaceProjectiveCapConeCoordinateFormula ι) :
    HaarProjectiveOverlapBetaLaw (ι := ι)
      (surfaceMeasure ι) := by
  haveI : NeZero
      ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere) :=
    ⟨Measure.toSphere_ne_zero
      (μ := (MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)))⟩
  exact
    HaarProjectiveOverlapBetaLaw.of_projectiveConeCoordinateRatio_eq
      (ι := ι) hN hCoord

/-- Explicit instantiation of
`HaarProjectiveOverlapBetaLaw.of_projectiveConeCoordinateRatio_eq` for the
canonical surface probability measure. -/
theorem surfaceHaarProjectiveOverlapBetaLaw
    [Nonempty ι]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere)]
    (hN : 2 ≤ Fintype.card ι)
    (hCoord :
      ∀ {e : EuclideanSpace ℂ ι}, ‖e‖ = 1 →
        ∀ {r : ℝ}, 0 ≤ r → r < 1 →
          projectiveCapProbability (ι := ι) (surfaceMeasure ι) e r =
            projectiveConeCoordinateRatio (Fintype.card ι - 1) r) :
    HaarProjectiveOverlapBetaLaw (ι := ι) (surfaceMeasure ι) := by
  exact
    surfaceHaarProjectiveOverlapBetaLaw_of_coneCoordinateFormula
      (ι := ι) hN hCoord

/-- Exact projective-cap probability for the canonical surface measure, once the
coordinate cone formula has been proved.

This is the surface-measure specialization of
`projectiveCapProbability_eq_pow_of_projectiveConeCoordinateRatio_eq`: the only
remaining input is the geometric cone-coordinate identity
`SurfaceProjectiveCapConeCoordinateFormula`. -/
theorem surfaceProjectiveCapProbability_eq_pow_of_coneCoordinateFormula
    [Nonempty ι]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere)]
    (hCoord : SurfaceProjectiveCapConeCoordinateFormula ι)
    {e : EuclideanSpace ℂ ι} (he : ‖e‖ = 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    projectiveCapProbability (ι := ι) (surfaceMeasure ι) e r =
      r ^ (2 * (Fintype.card ι - 1)) := by
  haveI : NeZero
      ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere) :=
    ⟨Measure.toSphere_ne_zero
      (μ := (MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)))⟩
  exact
    projectiveCapProbability_eq_pow_of_projectiveConeCoordinateRatio_eq
      (ι := ι) (μ := surfaceMeasure ι) (e := e)
      (N := Fintype.card ι)
      (by
        intro r hr0 hrlt
        exact hCoord he hr0 hrlt)
      hr0 hr1

/-- The exact surface projective-cap identity supplies the finite lower-bound
package consumed by the one-column spike probability pipeline. -/
theorem surfaceProjectiveCapProbabilityLowerBound_of_coneCoordinateFormula
    [Nonempty ι]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere)]
    (hCoord : SurfaceProjectiveCapConeCoordinateFormula ι)
    {e : EuclideanSpace ℂ ι} (he : ‖e‖ = 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ProjectiveCapProbabilityLowerBound
      (projectiveCapProbability (ι := ι) (surfaceMeasure ι) e r)
      (Fintype.card ι) r where
  radius_pos := hr
  prob_lower := by
    rw [surfaceProjectiveCapProbability_eq_pow_of_coneCoordinateFormula
      (ι := ι) hCoord he (le_of_lt hr) hr1]
    rfl

/-- Radius `1/N` specialization of the previous lower-bound package. -/
theorem surfaceProjectiveCapProbabilityLowerBound_inv_of_coneCoordinateFormula
    [Nonempty ι]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere)]
    (hN : 1 ≤ Fintype.card ι)
    (hCoord : SurfaceProjectiveCapConeCoordinateFormula ι)
    {e : EuclideanSpace ℂ ι} (he : ‖e‖ = 1) :
    ProjectiveCapProbabilityLowerBound
      (projectiveCapProbability (ι := ι) (surfaceMeasure ι) e
        (1 / (Fintype.card ι : ℝ)))
      (Fintype.card ι) (1 / (Fintype.card ι : ℝ)) := by
  have hcard_pos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mp hN)
  have hr : 0 < (1 / (Fintype.card ι : ℝ)) :=
    one_div_pos.mpr hcard_pos
  have hr1 : (1 / (Fintype.card ι : ℝ)) ≤ 1 := by
    have hcard_ge_one : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by
      exact_mod_cast hN
    simpa [one_div] using inv_le_one_of_one_le₀ hcard_ge_one
  exact
    surfaceProjectiveCapProbabilityLowerBound_of_coneCoordinateFormula
      (ι := ι) hCoord he hr hr1

/-- The exact Haar/projective overlap law gives the exact cap-volume package
at every radius `0 < r ≤ 1`. -/
theorem HaarProjectiveOverlapBetaLaw.toUnitProjectiveCapExactVolume
    {μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)}
    (I : HaarProjectiveOverlapBetaLaw (ι := ι) μ)
    {e : EuclideanSpace ℂ ι} (he : ‖e‖ = 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    UnitProjectiveCapExactVolume (ι := ι) μ e (Fintype.card ι) r :=
  betaMeasure_one_nat_sub_hasLaw_toUnitProjectiveCapExactVolume
    (ι := ι) I.dimension_ge_two he (I.overlap_hasLaw he) hr hr1

/-- Probability form of the exact Haar/projective cap law:

`P(|⟪e,u⟫|² ≥ 1-r²) = r^(2(N-1))`. -/
theorem HaarProjectiveOverlapBetaLaw.projectiveCapProbability_eq
    {μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)}
    (I : HaarProjectiveOverlapBetaLaw (ι := ι) μ)
    {e : EuclideanSpace ℂ ι} (he : ‖e‖ = 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    projectiveCapProbability (ι := ι) μ e r =
      r ^ (2 * (Fintype.card ι - 1)) := by
  have H :=
    I.toUnitProjectiveCapExactVolume (ι := ι) he hr hr1
  simpa [projectiveCapKernel] using H.prob_eq

/-- Surface-measure cap identity as a corollary of the master projective
overlap law.

This is the intended dependency order for the projective cap:

1. prove the master law `|⟪e,u⟫|² ∼ Beta(1,N-1)` for the spherical law;
2. use the already formalized `Beta(1,N-1)` upper tail at `1-r²`;
3. rewrite that tail as the projective cap probability.

Thus the cap formula is not an independent geometric input once the
Haar/projective overlap law is available. -/
theorem surfaceProjectiveCapProbability_eq_pow_of_haarProjectiveOverlapBetaLaw
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere)]
    (I : HaarProjectiveOverlapBetaLaw (ι := ι) (surfaceMeasure ι))
    {e : EuclideanSpace ℂ ι} (he : ‖e‖ = 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    projectiveCapProbability (ι := ι) (surfaceMeasure ι) e r =
      r ^ (2 * (Fintype.card ι - 1)) :=
  I.projectiveCapProbability_eq (ι := ι) he hr hr1

/-- Surface lower-bound package obtained from the master projective-overlap
Beta law, not from a separate cap computation. -/
theorem surfaceProjectiveCapProbabilityLowerBound_of_haarProjectiveOverlapBetaLaw
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere)]
    (I : HaarProjectiveOverlapBetaLaw (ι := ι) (surfaceMeasure ι))
    {e : EuclideanSpace ℂ ι} (he : ‖e‖ = 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ProjectiveCapProbabilityLowerBound
      (projectiveCapProbability (ι := ι) (surfaceMeasure ι) e r)
      (Fintype.card ι) r where
  radius_pos := hr
  prob_lower := by
    rw [surfaceProjectiveCapProbability_eq_pow_of_haarProjectiveOverlapBetaLaw
      (ι := ι) I he hr hr1]
    rfl

/-- Radius `1/N` specialization of the Beta-law-derived surface cap
lower-bound package. -/
theorem surfaceProjectiveCapProbabilityLowerBound_inv_of_haarProjectiveOverlapBetaLaw
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere)]
    (I : HaarProjectiveOverlapBetaLaw (ι := ι) (surfaceMeasure ι))
    {e : EuclideanSpace ℂ ι} (he : ‖e‖ = 1) :
    ProjectiveCapProbabilityLowerBound
      (projectiveCapProbability (ι := ι) (surfaceMeasure ι) e
        (1 / (Fintype.card ι : ℝ)))
      (Fintype.card ι) (1 / (Fintype.card ι : ℝ)) := by
  have hcard_ge_one : 1 ≤ Fintype.card ι :=
    le_trans (by norm_num : 1 ≤ 2) I.dimension_ge_two
  have hcard_posℝ : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hcard_ge_one)
  have hr : 0 < (1 / (Fintype.card ι : ℝ)) :=
    one_div_pos.mpr hcard_posℝ
  have hr1 : (1 / (Fintype.card ι : ℝ)) ≤ 1 := by
    have hcard_ge_oneℝ : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by
      exact_mod_cast hcard_ge_one
    simpa [one_div] using inv_le_one_of_one_le₀ hcard_ge_oneℝ
  exact
    surfaceProjectiveCapProbabilityLowerBound_of_haarProjectiveOverlapBetaLaw
      (ι := ι) I he hr hr1

/-- Literal set-measure form of the Haar/projective cap identity.

For any spherical law whose squared projective overlap has the Haar
`Beta(1,N-1)` law, the cap around every unit vector has exact measure
`r^(2(N-1))`. -/
theorem HaarProjectiveOverlapBetaLaw.projectiveCapSet_measureReal_eq_pow
    {μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)}
    (I : HaarProjectiveOverlapBetaLaw (ι := ι) μ)
    {e : EuclideanSpace ℂ ι} (he : ‖e‖ = 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    μ.real (projectiveCapSet (ι := ι) e r) =
      r ^ (2 * (Fintype.card ι - 1)) := by
  simpa [projectiveCapProbability] using
    (I.projectiveCapProbability_eq (ι := ι) he hr hr1)

/-- Exact projective cap identity, in the notation of the mathematical
statement.

If `sigma` is a spherical Haar/projective-overlap law on the unit sphere of
`ℂ^N`, then

`sigma {u | |⟪e,u⟫|² ≥ 1-r²} = r^(2(N-1))`

for every unit center `e` and every `0 < r ≤ 1`. -/
theorem exact_projective_cap_identity
    {sigma : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)}
    (hsigma : HaarProjectiveOverlapBetaLaw (ι := ι) sigma)
    {e : EuclideanSpace ℂ ι} (he : ‖e‖ = 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    sigma.real {u : Metric.sphere (0 : EuclideanSpace ℂ ι) 1 |
      1 - r ^ 2 ≤ ‖inner ℂ e (u : EuclideanSpace ℂ ι)‖ ^ 2} =
        r ^ (2 * (Fintype.card ι - 1)) := by
  simpa [projectiveCapSet] using
    hsigma.projectiveCapSet_measureReal_eq_pow
      (ι := ι) he hr hr1

/-- Cone-volume version of `exact_projective_cap_identity`.

For an ambient Haar measure whose induced normalized sphere law satisfies the
Haar/projective-overlap law, the radial cone over the projective cap has real
volume `r^(2(N-1))` times the real volume of the ambient unit ball. -/
theorem HaarProjectiveOverlapBetaLaw.projectiveCapCone_toReal_volume_eq_pow_mul_ball_toReal
    [Nonempty ι]
    (μ : Measure (EuclideanSpace ℂ ι)) [μ.IsAddHaarMeasure]
    [SFinite μ.toSphere] [IsFiniteMeasure μ.toSphere]
    (I : HaarProjectiveOverlapBetaLaw (ι := ι) μ.toSphere.toFinite)
    {e : EuclideanSpace ℂ ι} (he : ‖e‖ = 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hball0 : μ (Metric.ball (0 : EuclideanSpace ℂ ι) 1) ≠ 0)
    (hballt : μ (Metric.ball (0 : EuclideanSpace ℂ ι) 1) ≠ ∞) :
    ENNReal.toReal (μ (projectiveCapCone (ι := ι) e r)) =
      r ^ (2 * (Fintype.card ι - 1)) *
        ENNReal.toReal (μ (Metric.ball (0 : EuclideanSpace ℂ ι) 1)) := by
  have hcap :
      projectiveCapProbability (ι := ι) μ.toSphere.toFinite e r =
        r ^ (2 * (Fintype.card ι - 1)) :=
    I.projectiveCapProbability_eq (ι := ι) he hr hr1
  exact
    projectiveCapCone_toReal_volume_eq_pow_mul_ball_toReal_of_capProbability
      (ι := ι) μ e (Fintype.card ι) r hball0 hballt hcap

/-- Explicit law form of the Haar/projective-overlap theorem.

Under the exact Haar/projective interface, the push-forward measure of
`u ↦ |⟪e,u⟫|²` is `Beta(1,N-1)`, where `N = card ι`.  This is the
measure-level statement behind the cap identity
`P(|⟪e,u⟫|² ≥ 1-r²) = r^(2(N-1))`. -/
theorem HaarProjectiveOverlapBetaLaw.projectiveOverlapSqLaw_eq_betaMeasure
    {μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)}
    (I : HaarProjectiveOverlapBetaLaw (ι := ι) μ)
    {e : EuclideanSpace ℂ ι} (he : ‖e‖ = 1) :
    projectiveOverlapSqLaw (ι := ι) μ e =
      ProbabilityTheory.betaMeasure (1 : ℝ)
        (((Fintype.card ι) - 1 : ℕ) : ℝ) := by
  exact (I.overlap_hasLaw he).map_eq

/-- Explicit `HasLaw` form of the Haar/projective-overlap theorem. -/
theorem HaarProjectiveOverlapBetaLaw.hasLaw_projectiveOverlapSq
    {μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)}
    (I : HaarProjectiveOverlapBetaLaw (ι := ι) μ)
    {e : EuclideanSpace ℂ ι} (he : ‖e‖ = 1) :
    ProbabilityTheory.HasLaw (projectiveOverlapSq (ι := ι) e)
      (ProbabilityTheory.betaMeasure (1 : ℝ)
        (((Fintype.card ι) - 1 : ℕ) : ℝ)) μ :=
  I.overlap_hasLaw he

/-- Exact geometric cap volume implies the projective-cap lower-bound
interface consumed by the column-event probability theorem. -/
theorem ProjectiveCapExactVolume.toProjectiveCapProbabilityLowerBound
    {μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)}
    {e : EuclideanSpace ℂ ι} {N : ℕ} {r : ℝ}
    (I : ProjectiveCapExactVolume (ι := ι) μ e N r) :
    ProjectiveCapProbabilityLowerBound
      (projectiveCapProbability (ι := ι) μ e r) N r where
  radius_pos := I.radius_pos
  prob_lower := by
    rw [I.prob_eq]

/-- Unit-vector exact cap volume implies the projective-cap lower-bound
interface. -/
theorem UnitProjectiveCapExactVolume.toProjectiveCapProbabilityLowerBound
    {μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)}
    {e : EuclideanSpace ℂ ι} {N : ℕ} {r : ℝ}
    (I : UnitProjectiveCapExactVolume (ι := ι) μ e N r) :
    ProjectiveCapProbabilityLowerBound
      (projectiveCapProbability (ι := ι) μ e r) N r :=
  I.toProjectiveCapExactVolume.toProjectiveCapProbabilityLowerBound

/-- Ambient version of the projective cap around `e`.

This is the set used by the concrete column direction `u`, which is represented
as an ambient vector rather than as an element of the sphere subtype. -/
noncomputable def ambientProjectiveCapSet
    (e : EuclideanSpace ℂ ι) (r : ℝ) :
    Set (EuclideanSpace ℂ ι) :=
  {u | 1 - r ^ 2 ≤ ‖inner ℂ e u‖ ^ 2}

theorem measurableSet_ambientProjectiveCapSet
    (e : EuclideanSpace ℂ ι) (r : ℝ) :
    MeasurableSet (ambientProjectiveCapSet (ι := ι) e r) := by
  dsimp [ambientProjectiveCapSet]
  exact measurableSet_le measurable_const (by fun_prop)

/-- Probability of the ambient projective cap under an ambient direction law. -/
noncomputable def ambientProjectiveCapProbability
    (μ : Measure (EuclideanSpace ℂ ι))
    (e : EuclideanSpace ℂ ι) (r : ℝ) : ℝ :=
  μ.real (ambientProjectiveCapSet (ι := ι) e r)

/-- Squared ambient projective overlap with the chosen direction `e`. -/
noncomputable def ambientProjectiveOverlapSq
    (e : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ ι → ℝ :=
  fun u => ‖inner ℂ e u‖ ^ 2

theorem measurable_ambientProjectiveOverlapSq
    (e : EuclideanSpace ℂ ι) :
    Measurable (ambientProjectiveOverlapSq (ι := ι) e) := by
  change Measurable (fun u : EuclideanSpace ℂ ι => ‖inner ℂ e u‖ ^ 2)
  fun_prop

/-- The ambient cap is the inverse image of the upper tail of the ambient
squared-overlap map. -/
theorem ambientProjectiveCapSet_eq_preimage_ambientProjectiveOverlapSq
    (e : EuclideanSpace ℂ ι) (r : ℝ) :
    ambientProjectiveCapSet (ι := ι) e r =
      (ambientProjectiveOverlapSq (ι := ι) e) ⁻¹' Set.Ici (1 - r ^ 2) := by
  rfl

/-- Push-forward law of the ambient squared projective overlap. -/
noncomputable def ambientProjectiveOverlapSqLaw
    (μ : Measure (EuclideanSpace ℂ ι))
    (e : EuclideanSpace ℂ ι) : Measure ℝ :=
  Measure.map (ambientProjectiveOverlapSq (ι := ι) e) μ

/-- Analytic conversion: the upper tail of the ambient squared-overlap law is
the ambient projective cap probability. -/
theorem ambientProjectiveOverlapSqLaw_tail_eq_capProbability
    (μ : Measure (EuclideanSpace ℂ ι))
    (e : EuclideanSpace ℂ ι) (r : ℝ) :
    (ambientProjectiveOverlapSqLaw (ι := ι) μ e).real (Set.Ici (1 - r ^ 2)) =
      ambientProjectiveCapProbability (ι := ι) μ e r := by
  unfold ambientProjectiveOverlapSqLaw ambientProjectiveCapProbability
  rw [map_measureReal_apply
    (measurable_ambientProjectiveOverlapSq (ι := ι) e) measurableSet_Ici]
  rfl

/-- Exact ambient cap-volume statement for the column direction law. -/
structure AmbientProjectiveCapExactVolume
    (μ : Measure (EuclideanSpace ℂ ι))
    (e : EuclideanSpace ℂ ι) (N : ℕ) (r : ℝ) : Prop where
  radius_pos : 0 < r
  prob_eq : ambientProjectiveCapProbability (ι := ι) μ e r =
    projectiveCapKernel N r

/-- Unit-vector version of the exact ambient cap-volume statement. -/
structure UnitAmbientProjectiveCapExactVolume
    (μ : Measure (EuclideanSpace ℂ ι))
    (e : EuclideanSpace ℂ ι) (N : ℕ) (r : ℝ) : Prop where
  unit_vector : ‖e‖ = 1
  radius_pos : 0 < r
  prob_eq : ambientProjectiveCapProbability (ι := ι) μ e r =
    projectiveCapKernel N r

/-- Forgetting the unit-vector certificate gives the legacy ambient
exact-volume interface. -/
theorem UnitAmbientProjectiveCapExactVolume.toAmbientProjectiveCapExactVolume
    {μ : Measure (EuclideanSpace ℂ ι)}
    {e : EuclideanSpace ℂ ι} {N : ℕ} {r : ℝ}
    (I : UnitAmbientProjectiveCapExactVolume (ι := ι) μ e N r) :
    AmbientProjectiveCapExactVolume (ι := ι) μ e N r where
  radius_pos := I.radius_pos
  prob_eq := I.prob_eq

/-- Exact ambient squared-overlap tail law implies exact ambient cap volume. -/
theorem ProjectiveOverlapKernelTail.toAmbientProjectiveCapExactVolume
    {μ : Measure (EuclideanSpace ℂ ι)}
    {ν : Measure ℝ} {e : EuclideanSpace ℂ ι} {N : ℕ} {r : ℝ}
    (I : ProjectiveOverlapKernelTail ν N)
    (hLaw : ambientProjectiveOverlapSqLaw (ι := ι) μ e = ν)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    AmbientProjectiveCapExactVolume (ι := ι) μ e N r where
  radius_pos := hr
  prob_eq := by
    calc
      ambientProjectiveCapProbability (ι := ι) μ e r
          = (ambientProjectiveOverlapSqLaw (ι := ι) μ e).real
              (Set.Ici (1 - r ^ 2)) := by
                rw [ambientProjectiveOverlapSqLaw_tail_eq_capProbability]
      _ = ν.real (Set.Ici (1 - r ^ 2)) := by rw [hLaw]
      _ = projectiveCapKernel N r := I.tail_eq hr hr1

/-- Unit-vector theorem form of the exact ambient cap law. -/
theorem ProjectiveOverlapKernelTail.toUnitAmbientProjectiveCapExactVolume
    {μ : Measure (EuclideanSpace ℂ ι)}
    {ν : Measure ℝ} {e : EuclideanSpace ℂ ι} {N : ℕ} {r : ℝ}
    (I : ProjectiveOverlapKernelTail ν N)
    (he : ‖e‖ = 1)
    (hLaw : ambientProjectiveOverlapSqLaw (ι := ι) μ e = ν)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    UnitAmbientProjectiveCapExactVolume (ι := ι) μ e N r where
  unit_vector := he
  radius_pos := hr
  prob_eq :=
    (I.toAmbientProjectiveCapExactVolume
      (μ := μ) (e := e) (r := r) hLaw hr hr1).prob_eq

/-- Same ambient conversion from a `HasLaw` statement. -/
theorem ProjectiveOverlapKernelTail.toAmbientProjectiveCapExactVolume_of_hasLaw
    {μ : Measure (EuclideanSpace ℂ ι)}
    {ν : Measure ℝ} {e : EuclideanSpace ℂ ι} {N : ℕ} {r : ℝ}
    (I : ProjectiveOverlapKernelTail ν N)
    (hLaw : ProbabilityTheory.HasLaw (ambientProjectiveOverlapSq (ι := ι) e) ν μ)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    AmbientProjectiveCapExactVolume (ι := ι) μ e N r :=
  I.toAmbientProjectiveCapExactVolume (μ := μ) (e := e) (r := r)
    hLaw.map_eq hr hr1

/-- Same unit-vector ambient conversion from a `HasLaw` statement. -/
theorem ProjectiveOverlapKernelTail.toUnitAmbientProjectiveCapExactVolume_of_hasLaw
    {μ : Measure (EuclideanSpace ℂ ι)}
    {ν : Measure ℝ} {e : EuclideanSpace ℂ ι} {N : ℕ} {r : ℝ}
    (I : ProjectiveOverlapKernelTail ν N)
    (he : ‖e‖ = 1)
    (hLaw : ProbabilityTheory.HasLaw (ambientProjectiveOverlapSq (ι := ι) e) ν μ)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    UnitAmbientProjectiveCapExactVolume (ι := ι) μ e N r :=
  I.toUnitAmbientProjectiveCapExactVolume (μ := μ) (e := e) (r := r)
    he hLaw.map_eq hr hr1

/-- Ambient version of the “Haar → Beta → cap” bridge.  Once the ambient
direction law has squared-overlap distribution `Beta(1,N-1)`, the exact
projective cap law follows. -/
theorem betaMeasure_one_nat_sub_hasLaw_toUnitAmbientProjectiveCapExactVolume
    {μ : Measure (EuclideanSpace ℂ ι)}
    {e : EuclideanSpace ℂ ι} {N : ℕ} {r : ℝ}
    (hN : 2 ≤ N) (he : ‖e‖ = 1)
    (hLaw :
      ProbabilityTheory.HasLaw (ambientProjectiveOverlapSq (ι := ι) e)
        (ProbabilityTheory.betaMeasure (1 : ℝ) ((N - 1 : ℕ) : ℝ)) μ)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    UnitAmbientProjectiveCapExactVolume (ι := ι) μ e N r :=
  ProjectiveOverlapKernelTail.toUnitAmbientProjectiveCapExactVolume_of_hasLaw
    (betaMeasure_one_nat_sub_projectiveOverlapKernelTail hN) he hLaw hr hr1

/-- A subtype-sphere squared-overlap law pushes forward to the corresponding
ambient squared-overlap law under the inclusion of the sphere into the ambient
Hilbert space. -/
theorem hasLaw_ambientProjectiveOverlapSq_of_subtype_val
    {μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)}
    {ν : Measure ℝ} {e : EuclideanSpace ℂ ι}
    (hLaw :
      ProbabilityTheory.HasLaw (projectiveOverlapSq (ι := ι) e) ν μ) :
    ProbabilityTheory.HasLaw (ambientProjectiveOverlapSq (ι := ι) e) ν
      (Measure.map
        ((↑) : Metric.sphere (0 : EuclideanSpace ℂ ι) 1 →
          EuclideanSpace ℂ ι) μ) where
  aemeasurable :=
    (measurable_ambientProjectiveOverlapSq (ι := ι) e).aemeasurable
  map_eq := by
    rw [← hLaw.map_eq]
    symm
    calc
      Measure.map (projectiveOverlapSq (ι := ι) e) μ =
          Measure.map
            (ambientProjectiveOverlapSq (ι := ι) e ∘
              ((↑) : Metric.sphere (0 : EuclideanSpace ℂ ι) 1 →
                EuclideanSpace ℂ ι)) μ := by
            rfl
      _ =
          Measure.map (ambientProjectiveOverlapSq (ι := ι) e)
            (Measure.map
              ((↑) : Metric.sphere (0 : EuclideanSpace ℂ ι) 1 →
                EuclideanSpace ℂ ι) μ) := by
            symm
            exact Measure.map_map
              (μ := μ)
              (f := ((↑) : Metric.sphere (0 : EuclideanSpace ℂ ι) 1 →
                EuclideanSpace ℂ ι))
              (g := ambientProjectiveOverlapSq (ι := ι) e)
              (measurable_ambientProjectiveOverlapSq (ι := ι) e)
              continuous_subtype_val.measurable

/-- Ambient version of the exact projective-overlap law.  It is useful when a
spherical law is represented as an ambient measure supported on the unit
sphere. -/
structure AmbientHaarProjectiveOverlapBetaLaw
    (μ : Measure (EuclideanSpace ℂ ι)) : Prop where
  dimension_ge_two : 2 ≤ Fintype.card ι
  overlap_hasLaw :
    ∀ {e : EuclideanSpace ℂ ι}, ‖e‖ = 1 →
      ProbabilityTheory.HasLaw (ambientProjectiveOverlapSq (ι := ι) e)
        (ProbabilityTheory.betaMeasure (1 : ℝ)
          (((Fintype.card ι) - 1 : ℕ) : ℝ)) μ

/-- Ambient tail-extensional constructor for the exact Haar/projective-overlap
law.

This is the version used for column-direction laws represented as ambient
measures supported on the unit sphere.  As in the subtype constructor, the
hypothesis is stated for all upper rays `Ici a` so that boundary/atom issues
are explicit rather than hidden in cap notation. -/
theorem AmbientHaarProjectiveOverlapBetaLaw.of_forall_Ici_tail_eq_beta
    {μ : Measure (EuclideanSpace ℂ ι)}
    [IsProbabilityMeasure μ]
    (hN : 2 ≤ Fintype.card ι)
    (hTail :
      ∀ {e : EuclideanSpace ℂ ι}, ‖e‖ = 1 → ∀ a : ℝ,
        (ambientProjectiveOverlapSqLaw (ι := ι) μ e).real (Set.Ici a) =
          (ProbabilityTheory.betaMeasure (1 : ℝ)
            (((Fintype.card ι) - 1 : ℕ) : ℝ)).real (Set.Ici a)) :
    AmbientHaarProjectiveOverlapBetaLaw (ι := ι) μ where
  dimension_ge_two := hN
  overlap_hasLaw := by
    intro e he
    let νβ : Measure ℝ :=
      ProbabilityTheory.betaMeasure (1 : ℝ)
        (((Fintype.card ι) - 1 : ℕ) : ℝ)
    haveI : IsProbabilityMeasure νβ :=
      ProbabilityTheory.isProbabilityMeasureBeta
        (by norm_num) (by
          have hpos : 0 < ((Fintype.card ι - 1 : ℕ) : ℝ) := by
            exact_mod_cast (Nat.sub_pos_of_lt hN)
          exact hpos)
    haveI : IsProbabilityMeasure (ambientProjectiveOverlapSqLaw (ι := ι) μ e) := by
      unfold ambientProjectiveOverlapSqLaw
      exact Measure.isProbabilityMeasure_map
        (measurable_ambientProjectiveOverlapSq (ι := ι) e).aemeasurable
    have hmap :
        ambientProjectiveOverlapSqLaw (ι := ι) μ e = νβ := by
      apply Measure.ext_of_Ici
      intro a
      exact
        (measureReal_eq_measureReal_iff
          (μ := ambientProjectiveOverlapSqLaw (ι := ι) μ e)
          (ν := νβ)
          (s := Set.Ici a)
          (measure_ne_top _ _) (measure_ne_top _ _)).mp
          (by
            simpa [νβ] using hTail he a)
    exact
      { aemeasurable :=
          (measurable_ambientProjectiveOverlapSq (ι := ι) e).aemeasurable
        map_eq := by
          simpa [ambientProjectiveOverlapSqLaw, νβ] using hmap }

/-- The exact ambient Haar/projective overlap law gives the exact ambient
cap-volume package at every radius `0 < r ≤ 1`. -/
theorem AmbientHaarProjectiveOverlapBetaLaw.toUnitAmbientProjectiveCapExactVolume
    {μ : Measure (EuclideanSpace ℂ ι)}
    (I : AmbientHaarProjectiveOverlapBetaLaw (ι := ι) μ)
    {e : EuclideanSpace ℂ ι} (he : ‖e‖ = 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    UnitAmbientProjectiveCapExactVolume (ι := ι) μ e (Fintype.card ι) r :=
  betaMeasure_one_nat_sub_hasLaw_toUnitAmbientProjectiveCapExactVolume
    (ι := ι) I.dimension_ge_two he (I.overlap_hasLaw he) hr hr1

/-- Probability form of the exact ambient Haar/projective cap law. -/
theorem AmbientHaarProjectiveOverlapBetaLaw.ambientProjectiveCapProbability_eq
    {μ : Measure (EuclideanSpace ℂ ι)}
    (I : AmbientHaarProjectiveOverlapBetaLaw (ι := ι) μ)
    {e : EuclideanSpace ℂ ι} (he : ‖e‖ = 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ambientProjectiveCapProbability (ι := ι) μ e r =
      r ^ (2 * (Fintype.card ι - 1)) := by
  have H :=
    I.toUnitAmbientProjectiveCapExactVolume (ι := ι) he hr hr1
  simpa [projectiveCapKernel] using H.prob_eq

/-- Explicit ambient law form of the Haar/projective-overlap theorem.

This is the form used by column directions, which are represented as ambient
vectors supported on the unit sphere. -/
theorem AmbientHaarProjectiveOverlapBetaLaw.ambientProjectiveOverlapSqLaw_eq_betaMeasure
    {μ : Measure (EuclideanSpace ℂ ι)}
    (I : AmbientHaarProjectiveOverlapBetaLaw (ι := ι) μ)
    {e : EuclideanSpace ℂ ι} (he : ‖e‖ = 1) :
    ambientProjectiveOverlapSqLaw (ι := ι) μ e =
      ProbabilityTheory.betaMeasure (1 : ℝ)
        (((Fintype.card ι) - 1 : ℕ) : ℝ) := by
  exact (I.overlap_hasLaw he).map_eq

/-- Explicit ambient `HasLaw` form of the Haar/projective-overlap theorem. -/
theorem AmbientHaarProjectiveOverlapBetaLaw.hasLaw_ambientProjectiveOverlapSq
    {μ : Measure (EuclideanSpace ℂ ι)}
    (I : AmbientHaarProjectiveOverlapBetaLaw (ι := ι) μ)
    {e : EuclideanSpace ℂ ι} (he : ‖e‖ = 1) :
    ProbabilityTheory.HasLaw (ambientProjectiveOverlapSq (ι := ι) e)
      (ProbabilityTheory.betaMeasure (1 : ℝ)
        (((Fintype.card ι) - 1 : ℕ) : ℝ)) μ :=
  I.overlap_hasLaw he

/-- Pushing a subtype exact Haar/projective law through the sphere inclusion
gives the corresponding ambient exact law. -/
theorem HaarProjectiveOverlapBetaLaw.toAmbient
    {μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)}
    (I : HaarProjectiveOverlapBetaLaw (ι := ι) μ) :
    AmbientHaarProjectiveOverlapBetaLaw (ι := ι)
      (Measure.map
        ((↑) : Metric.sphere (0 : EuclideanSpace ℂ ι) 1 →
          EuclideanSpace ℂ ι) μ) where
  dimension_ge_two := I.dimension_ge_two
  overlap_hasLaw := by
    intro e he
    exact hasLaw_ambientProjectiveOverlapSq_of_subtype_val
      (ι := ι) (I.overlap_hasLaw he)

/-- Exact ambient cap volume implies the projective-cap lower-bound interface. -/
theorem AmbientProjectiveCapExactVolume.toProjectiveCapProbabilityLowerBound
    {μ : Measure (EuclideanSpace ℂ ι)}
    {e : EuclideanSpace ℂ ι} {N : ℕ} {r : ℝ}
    (I : AmbientProjectiveCapExactVolume (ι := ι) μ e N r) :
    ProjectiveCapProbabilityLowerBound
      (ambientProjectiveCapProbability (ι := ι) μ e r) N r where
  radius_pos := I.radius_pos
  prob_lower := by
    rw [I.prob_eq]

/-- Unit-vector exact ambient cap volume implies the projective-cap lower-bound
interface. -/
theorem UnitAmbientProjectiveCapExactVolume.toProjectiveCapProbabilityLowerBound
    {μ : Measure (EuclideanSpace ℂ ι)}
    {e : EuclideanSpace ℂ ι} {N : ℕ} {r : ℝ}
    (I : UnitAmbientProjectiveCapExactVolume (ι := ι) μ e N r) :
    ProjectiveCapProbabilityLowerBound
      (ambientProjectiveCapProbability (ι := ι) μ e r) N r :=
  I.toAmbientProjectiveCapExactVolume.toProjectiveCapProbabilityLowerBound

end ProjectiveCapGeometry

/-- At radius `r = 1/N`, the explicit projective cap kernel is at least
`exp(-2 N log N)`.

This is the promised formal `exp[-O(N log N)]` estimate, with the concrete
constant `2`. -/
theorem exp_neg_two_mul_nat_log_le_projectiveCapKernel_inv
    {N : ℕ} (hN : 1 ≤ N) :
    Real.exp (-(capNLogNCost 2 (N : ℝ))) ≤
      projectiveCapKernel N (1 / (N : ℝ)) := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hN)
  have hbase_pos : 0 < (1 / (N : ℝ)) := one_div_pos.mpr hNpos
  have hkernel_pos :
      0 < projectiveCapKernel N (1 / (N : ℝ)) :=
    projectiveCapKernel_pos hbase_pos
  rw [← Real.le_log_iff_exp_le hkernel_pos]
  unfold projectiveCapKernel capNLogNCost
  have hbase_eq : (1 / (N : ℝ)) = ((N : ℝ)⁻¹) := by ring
  rw [hbase_eq, Real.log_pow, Real.log_inv]
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  have hcoeffNat : 2 * (N - 1) ≤ 2 * N :=
    Nat.mul_le_mul_left 2 (Nat.sub_le N 1)
  have hcoeff :
      ((2 * (N - 1) : ℕ) : ℝ) ≤ (2 * (N : ℝ)) := by
    exact_mod_cast hcoeffNat
  have hmul :
      ((2 * (N - 1) : ℕ) : ℝ) * Real.log (N : ℝ) ≤
        (2 * (N : ℝ)) * Real.log (N : ℝ) :=
    mul_le_mul_of_nonneg_right hcoeff hlog_nonneg
  nlinarith

/-- The exact projective cap estimate at radius `1/N` implies the coarser
`CapProbabilityLowerBound` interface with cost `2 N log N`. -/
theorem ProjectiveCapProbabilityLowerBound.toCapProbabilityLowerBound_inv
    {prob : ℝ} {N : ℕ}
    (I : ProjectiveCapProbabilityLowerBound prob N (1 / (N : ℝ)))
    (hN : 1 ≤ N) :
    CapProbabilityLowerBound prob (N : ℝ) 2 where
  N_pos := by exact_mod_cast (Nat.succ_le_iff.mp hN)
  C_nonneg := by norm_num
  prob_lower :=
    le_trans (exp_neg_two_mul_nat_log_le_projectiveCapKernel_inv hN)
      I.prob_lower

section ProjectiveCapGeometry

variable {ι : Type*} [Fintype ι]

/-- At the chosen radius `r = 1/N`, exact geometric cap volume implies the
coarser `CapProbabilityLowerBound` with cost `2 N log N`. -/
theorem ProjectiveCapExactVolume.toCapProbabilityLowerBound_inv
    {μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)}
    {e : EuclideanSpace ℂ ι} {N : ℕ}
    (I : ProjectiveCapExactVolume (ι := ι) μ e N (1 / (N : ℝ)))
    (hN : 1 ≤ N) :
    CapProbabilityLowerBound
      (projectiveCapProbability (ι := ι) μ e (1 / (N : ℝ))) (N : ℝ) 2 :=
  (I.toProjectiveCapProbabilityLowerBound).toCapProbabilityLowerBound_inv hN

/-- Unit-vector version at radius `1/N`. -/
theorem UnitProjectiveCapExactVolume.toCapProbabilityLowerBound_inv
    {μ : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)}
    {e : EuclideanSpace ℂ ι} {N : ℕ}
    (I : UnitProjectiveCapExactVolume (ι := ι) μ e N (1 / (N : ℝ)))
    (hN : 1 ≤ N) :
    CapProbabilityLowerBound
      (projectiveCapProbability (ι := ι) μ e (1 / (N : ℝ))) (N : ℝ) 2 :=
  I.toProjectiveCapExactVolume.toCapProbabilityLowerBound_inv hN

/-- At radius `r = 1/N`, exact ambient cap volume implies the coarser
`CapProbabilityLowerBound` with cost `2 N log N`. -/
theorem AmbientProjectiveCapExactVolume.toCapProbabilityLowerBound_inv
    {μ : Measure (EuclideanSpace ℂ ι)}
    {e : EuclideanSpace ℂ ι} {N : ℕ}
    (I : AmbientProjectiveCapExactVolume (ι := ι) μ e N (1 / (N : ℝ)))
    (hN : 1 ≤ N) :
    CapProbabilityLowerBound
      (ambientProjectiveCapProbability (ι := ι) μ e (1 / (N : ℝ)))
      (N : ℝ) 2 :=
  (I.toProjectiveCapProbabilityLowerBound).toCapProbabilityLowerBound_inv hN

/-- Unit-vector ambient version at radius `1/N`. -/
theorem UnitAmbientProjectiveCapExactVolume.toCapProbabilityLowerBound_inv
    {μ : Measure (EuclideanSpace ℂ ι)}
    {e : EuclideanSpace ℂ ι} {N : ℕ}
    (I : UnitAmbientProjectiveCapExactVolume (ι := ι) μ e N (1 / (N : ℝ)))
    (hN : 1 ≤ N) :
    CapProbabilityLowerBound
      (ambientProjectiveCapProbability (ι := ι) μ e (1 / (N : ℝ)))
      (N : ℝ) 2 :=
  I.toAmbientProjectiveCapExactVolume.toCapProbabilityLowerBound_inv hN

end ProjectiveCapGeometry

/-- Transfer the cap estimate `exp[-O(N log N)]` to a chosen large-deviation
speed.

If `C_d N_d log N_d ≤ slack * speed_d`, then the logarithmic cap cost is
absorbed by the slack:

`log capProb_d ≥ - slack * speed_d`.

This is the formal version of saying that the cap cost
`exp[-O(N log N)]` is negligible at any speed for which
`N log N = o(speed)`. -/
theorem eventual_log_lower_of_capProbability
    {capProb N C speed : ℕ → ℝ} {slack : ℝ}
    (hCap :
      ∀ᶠ d in atTop,
        CapProbabilityLowerBound (capProb d) (N d) (C d))
    (hCost :
      ∀ᶠ d in atTop,
        capNLogNCost (C d) (N d) ≤ slack * speed d) :
    ∀ᶠ d in atTop,
      -slack * speed d ≤ Real.log (capProb d) := by
  filter_upwards [hCap, hCost] with d hcap hcost
  have hlog := hcap.log_prob_ge
  linarith

/-- Direct asymptotic form for the projective cap at radius `1/N`.

If the exact projective cap kernel lower bound holds and
`2 N log N ≤ slack * speed`, then the cap probability contributes at most
`slack` to the logarithmic cost at speed `speed`. -/
theorem eventual_log_lower_of_projectiveCapProbability_inv
    {capProb speed : ℕ → ℝ} {N : ℕ → ℕ} {slack : ℝ}
    (hN : ∀ᶠ d in atTop, 1 ≤ N d)
    (hCap :
      ∀ᶠ d in atTop,
        ProjectiveCapProbabilityLowerBound
          (capProb d) (N d) (1 / (N d : ℝ)))
    (hCost :
      ∀ᶠ d in atTop,
        capNLogNCost 2 (N d : ℝ) ≤ slack * speed d) :
    ∀ᶠ d in atTop,
      -slack * speed d ≤ Real.log (capProb d) := by
  have hCoarse :
      ∀ᶠ d in atTop,
        CapProbabilityLowerBound (capProb d) (N d : ℝ) 2 := by
    filter_upwards [hN, hCap] with d hNd hcapd
    exact hcapd.toCapProbabilityLowerBound_inv hNd
  exact
    eventual_log_lower_of_capProbability
      (capProb := capProb) (N := fun d => (N d : ℝ))
      (C := fun _ => 2) (speed := speed) (slack := slack)
      hCoarse hCost

/-- Product form for combining a Beta column-mass interval with an independent
cap event.

If the two probabilities have logarithmic costs `betaCost` and `capCost`, then
their product has the sum of the costs.  In applications independence turns
the favourable event probability into this product. -/
theorem log_mul_prob_ge_of_two_lower_bounds
    {p q betaCost capCost : ℝ}
    (hp : 0 < p) (hq : 0 < q)
    (hpLower : -betaCost ≤ Real.log p)
    (hqLower : -capCost ≤ Real.log q) :
    -(betaCost + capCost) ≤ Real.log (p * q) := by
  rw [Real.log_mul (ne_of_gt hp) (ne_of_gt hq)]
  linarith

/-- Eventual product version: a Beta interval lower bound and a cap lower
bound combine additively at the logarithmic level. -/
theorem eventual_log_lower_of_beta_and_cap_product
    {betaProb capProb productProb speed : ℕ → ℝ}
    {N s : ℕ → ℕ} {q δ C Ncap : ℕ → ℝ}
    {lam a betaSlack capSlack : ℝ}
    (hProduct :
      ∀ᶠ d in atTop,
        productProb d = betaProb d * capProb d)
    (hBeta :
      ∀ᶠ d in atTop,
        BetaColumnIntervalLowerBound (betaProb d) (N d) (s d) (q d) (δ d))
    (hBetaKernel :
      ∀ᶠ d in atTop,
        -(lam * a + betaSlack) * speed d ≤
          Real.log (betaColumnIntervalKernel (N d) (s d) (q d) (δ d)))
    (hCap :
      ∀ᶠ d in atTop,
        CapProbabilityLowerBound (capProb d) (Ncap d) (C d))
    (hCapCost :
      ∀ᶠ d in atTop,
        capNLogNCost (C d) (Ncap d) ≤ capSlack * speed d) :
    ∀ᶠ d in atTop,
      Real.log (productProb d) ≥
        -(lam * a + betaSlack + capSlack) * speed d := by
  have hBetaLog :=
    eventual_log_lower_of_betaColumnInterval
      (prob := betaProb) (speed := speed) (N := N) (s := s)
      (q := q) (δ := δ) (lam := lam) (a := a) (slack := betaSlack)
      hBeta hBetaKernel
  have hCapLog :=
    eventual_log_lower_of_capProbability
      (capProb := capProb) (N := Ncap) (C := C) (speed := speed)
      (slack := capSlack) hCap hCapCost
  filter_upwards [hProduct, hBeta, hCap, hBetaLog, hCapLog]
    with d hprod hbeta hcap hbetalog hcaplog
  rw [hprod]
  have hbetalog' :
      -((lam * a + betaSlack) * speed d) ≤ Real.log (betaProb d) := by
    have hcostBeta :
        -((lam * a + betaSlack) * speed d) =
          -(lam * a + betaSlack) * speed d := by
      ring
    rw [hcostBeta]
    exact hbetalog
  have hcaplog' :
      -(capSlack * speed d) ≤ Real.log (capProb d) := by
    have hcostCap :
        -(capSlack * speed d) = -capSlack * speed d := by
      ring
    rw [hcostCap]
    exact hcaplog
  have hmul :=
    log_mul_prob_ge_of_two_lower_bounds
      (p := betaProb d) (q := capProb d)
      (betaCost := (lam * a + betaSlack) * speed d)
      (capCost := capSlack * speed d)
      hbeta.prob_pos hcap.prob_pos hbetalog' hcaplog'
  have hcost :
      ((lam * a + betaSlack) * speed d + capSlack * speed d) =
        (lam * a + betaSlack + capSlack) * speed d := by
    ring
  change -(lam * a + betaSlack + capSlack) * speed d ≤
    Real.log (betaProb d * capProb d)
  have htarget :
      -(lam * a + betaSlack + capSlack) * speed d =
        -((lam * a + betaSlack) * speed d + capSlack * speed d) := by
    rw [hcost]
    ring
  rw [htarget]
  exact hmul

/-- Product version specialized to the concrete projective cap at radius
`1/Ncap`.

This combines the Beta interval lower bound with the formal cap estimate
`projectiveCapKernel Ncap (1/Ncap) ≥ exp(-2 Ncap log Ncap)`. -/
theorem eventual_log_lower_of_beta_and_projective_cap_product
    {betaProb capProb productProb speed : ℕ → ℝ}
    {N s Ncap : ℕ → ℕ} {q δ : ℕ → ℝ}
    {lam a betaSlack capSlack : ℝ}
    (hProduct :
      ∀ᶠ d in atTop,
        productProb d = betaProb d * capProb d)
    (hBeta :
      ∀ᶠ d in atTop,
        BetaColumnIntervalLowerBound (betaProb d) (N d) (s d) (q d) (δ d))
    (hBetaKernel :
      ∀ᶠ d in atTop,
        -(lam * a + betaSlack) * speed d ≤
          Real.log (betaColumnIntervalKernel (N d) (s d) (q d) (δ d)))
    (hNcap : ∀ᶠ d in atTop, 1 ≤ Ncap d)
    (hCap :
      ∀ᶠ d in atTop,
        ProjectiveCapProbabilityLowerBound
          (capProb d) (Ncap d) (1 / (Ncap d : ℝ)))
    (hCapCost :
      ∀ᶠ d in atTop,
        capNLogNCost 2 (Ncap d : ℝ) ≤ capSlack * speed d) :
    ∀ᶠ d in atTop,
      Real.log (productProb d) ≥
        -(lam * a + betaSlack + capSlack) * speed d := by
  have hCapCoarse :
      ∀ᶠ d in atTop,
        CapProbabilityLowerBound (capProb d) (Ncap d : ℝ) 2 := by
    filter_upwards [hNcap, hCap] with d hNd hcapd
    exact hcapd.toCapProbabilityLowerBound_inv hNd
  exact
    eventual_log_lower_of_beta_and_cap_product
      (betaProb := betaProb) (capProb := capProb)
      (productProb := productProb) (speed := speed)
      (N := N) (s := s) (q := q) (δ := δ)
      (C := fun _ => 2) (Ncap := fun d => (Ncap d : ℝ))
      (lam := lam) (a := a) (betaSlack := betaSlack)
      (capSlack := capSlack)
      hProduct hBeta hBetaKernel hCapCoarse hCapCost

/-! ## Asymptotic probability of the full one-column favourable event -/

/-- Product form for combining the three independent pieces of the favourable
one-column event: column mass, column direction, and deleted-column
background.

The logarithmic costs add.  This is the finite-dimensional algebra behind
the statement

`P(E_col) = P(E_mass) P(E_cap) P(E_background)`. -/
theorem log_mul_prob_ge_of_three_lower_bounds
    {p q r betaCost capCost backgroundCost : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hpLower : -betaCost ≤ Real.log p)
    (hqLower : -capCost ≤ Real.log q)
    (hrLower : -backgroundCost ≤ Real.log r) :
    -(betaCost + capCost + backgroundCost) ≤ Real.log (p * q * r) := by
  have hpq : 0 < p * q := mul_pos hp hq
  rw [Real.log_mul (ne_of_gt hpq) (ne_of_gt hr),
    Real.log_mul (ne_of_gt hp) (ne_of_gt hq)]
  linarith

/-- If the background typical event has probability at least `1/2`, then its
logarithmic cost is negligible at any speed that eventually absorbs the fixed
constant `log(1/2)`. -/
theorem eventual_log_lower_of_background_probability_half
    {backgroundProb speed : ℕ → ℝ} {backgroundSlack : ℝ}
    (hHalf : ∀ᶠ d in atTop, (1 / 2 : ℝ) ≤ backgroundProb d)
    (hAbsorb :
      ∀ᶠ d in atTop,
        -backgroundSlack * speed d ≤ Real.log (1 / 2 : ℝ)) :
    ∀ᶠ d in atTop,
      -backgroundSlack * speed d ≤ Real.log (backgroundProb d) := by
  filter_upwards [hHalf, hAbsorb] with d hhalf habsorb
  have hlog :
      Real.log (1 / 2 : ℝ) ≤ Real.log (backgroundProb d) :=
    Real.log_le_log (by norm_num) hhalf
  exact le_trans habsorb hlog

/-- Full one-column event probability lower bound.

This is the formal asymptotic estimate for the favourable column event whose
pieces are:

* a Beta interval for the distinguished column mass;
* a projective cap for the distinguished column direction;
* a typical event for the deleted-column background.

The cap and background costs are carried as explicit slacks, so this theorem
does not hide the fact that they must be negligible at the chosen speed. -/
theorem eventual_log_lower_of_column_event_probability
    {betaProb capProb backgroundProb columnProb speed : ℕ → ℝ}
    {N s Ncap : ℕ → ℕ} {q δ : ℕ → ℝ}
    {lam a betaSlack capSlack backgroundSlack : ℝ}
    (hProduct :
      ∀ᶠ d in atTop,
        columnProb d = betaProb d * capProb d * backgroundProb d)
    (hBeta :
      ∀ᶠ d in atTop,
        BetaColumnIntervalLowerBound (betaProb d) (N d) (s d) (q d) (δ d))
    (hBetaKernel :
      ∀ᶠ d in atTop,
        -(lam * a + betaSlack) * speed d ≤
          Real.log (betaColumnIntervalKernel (N d) (s d) (q d) (δ d)))
    (hNcap : ∀ᶠ d in atTop, 1 ≤ Ncap d)
    (hCap :
      ∀ᶠ d in atTop,
        ProjectiveCapProbabilityLowerBound
          (capProb d) (Ncap d) (1 / (Ncap d : ℝ)))
    (hCapCost :
      ∀ᶠ d in atTop,
        capNLogNCost 2 (Ncap d : ℝ) ≤ capSlack * speed d)
    (hBackgroundPos :
      ∀ᶠ d in atTop, 0 < backgroundProb d)
    (hBackgroundLog :
      ∀ᶠ d in atTop,
        -backgroundSlack * speed d ≤ Real.log (backgroundProb d)) :
    ∀ᶠ d in atTop,
      Real.log (columnProb d) ≥
        -(lam * a + betaSlack + capSlack + backgroundSlack) * speed d := by
  have hBetaLog :=
    eventual_log_lower_of_betaColumnInterval
      (prob := betaProb) (speed := speed) (N := N) (s := s)
      (q := q) (δ := δ) (lam := lam) (a := a)
      (slack := betaSlack) hBeta hBetaKernel
  have hCapCoarse :
      ∀ᶠ d in atTop,
        CapProbabilityLowerBound (capProb d) (Ncap d : ℝ) 2 := by
    filter_upwards [hNcap, hCap] with d hNd hcapd
    exact hcapd.toCapProbabilityLowerBound_inv hNd
  have hCapLog :=
    eventual_log_lower_of_capProbability
      (capProb := capProb) (N := fun d => (Ncap d : ℝ))
      (C := fun _ => 2) (speed := speed) (slack := capSlack)
      hCapCoarse hCapCost
  filter_upwards
      [hProduct, hBeta, hCap, hBetaLog, hCapLog,
        hBackgroundPos, hBackgroundLog]
    with d hprod hbeta hcap hbetalog hcaplog hbgpos hbglog
  rw [hprod]
  have hbetalog' :
      -((lam * a + betaSlack) * speed d) ≤ Real.log (betaProb d) := by
    have hcost :
        -((lam * a + betaSlack) * speed d) =
          -(lam * a + betaSlack) * speed d := by
      ring
    rw [hcost]
    exact hbetalog
  have hcaplog' :
      -(capSlack * speed d) ≤ Real.log (capProb d) := by
    have hcost : -(capSlack * speed d) = -capSlack * speed d := by
      ring
    rw [hcost]
    exact hcaplog
  have hbglog' :
      -(backgroundSlack * speed d) ≤ Real.log (backgroundProb d) := by
    have hcost :
        -(backgroundSlack * speed d) = -backgroundSlack * speed d := by
      ring
    rw [hcost]
    exact hbglog
  have hmul :=
    log_mul_prob_ge_of_three_lower_bounds
      (p := betaProb d) (q := capProb d) (r := backgroundProb d)
      (betaCost := (lam * a + betaSlack) * speed d)
      (capCost := capSlack * speed d)
      (backgroundCost := backgroundSlack * speed d)
      hbeta.prob_pos hcap.prob_pos hbgpos
      hbetalog' hcaplog' hbglog'
  have htarget :
      -(lam * a + betaSlack + capSlack + backgroundSlack) * speed d =
        -((lam * a + betaSlack) * speed d +
          capSlack * speed d + backgroundSlack * speed d) := by
    ring
  rw [htarget]
  exact hmul

/-- Version of the full column-event probability lower bound where the
background contribution is supplied by the concrete estimate
`P(background typical) ≥ 1/2`. -/
theorem eventual_log_lower_of_column_event_probability_of_background_half
    {betaProb capProb backgroundProb columnProb speed : ℕ → ℝ}
    {N s Ncap : ℕ → ℕ} {q δ : ℕ → ℝ}
    {lam a betaSlack capSlack backgroundSlack : ℝ}
    (hProduct :
      ∀ᶠ d in atTop,
        columnProb d = betaProb d * capProb d * backgroundProb d)
    (hBeta :
      ∀ᶠ d in atTop,
        BetaColumnIntervalLowerBound (betaProb d) (N d) (s d) (q d) (δ d))
    (hBetaKernel :
      ∀ᶠ d in atTop,
        -(lam * a + betaSlack) * speed d ≤
          Real.log (betaColumnIntervalKernel (N d) (s d) (q d) (δ d)))
    (hNcap : ∀ᶠ d in atTop, 1 ≤ Ncap d)
    (hCap :
      ∀ᶠ d in atTop,
        ProjectiveCapProbabilityLowerBound
          (capProb d) (Ncap d) (1 / (Ncap d : ℝ)))
    (hCapCost :
      ∀ᶠ d in atTop,
        capNLogNCost 2 (Ncap d : ℝ) ≤ capSlack * speed d)
    (hBackgroundHalf :
      ∀ᶠ d in atTop, (1 / 2 : ℝ) ≤ backgroundProb d)
    (hBackgroundAbsorb :
      ∀ᶠ d in atTop,
        -backgroundSlack * speed d ≤ Real.log (1 / 2 : ℝ)) :
    ∀ᶠ d in atTop,
      Real.log (columnProb d) ≥
        -(lam * a + betaSlack + capSlack + backgroundSlack) * speed d := by
  have hBackgroundPos :
      ∀ᶠ d in atTop, 0 < backgroundProb d := by
    filter_upwards [hBackgroundHalf] with d hhalf
    linarith
  have hBackgroundLog :=
    eventual_log_lower_of_background_probability_half
      (backgroundProb := backgroundProb) (speed := speed)
      (backgroundSlack := backgroundSlack)
      hBackgroundHalf hBackgroundAbsorb
  exact
    eventual_log_lower_of_column_event_probability
      (betaProb := betaProb) (capProb := capProb)
      (backgroundProb := backgroundProb) (columnProb := columnProb)
      (speed := speed) (N := N) (s := s) (Ncap := Ncap)
      (q := q) (δ := δ) (lam := lam) (a := a)
      (betaSlack := betaSlack) (capSlack := capSlack)
      (backgroundSlack := backgroundSlack)
      hProduct hBeta hBetaKernel hNcap hCap hCapCost
      hBackgroundPos hBackgroundLog

/-- Single-slack version of
`eventual_log_lower_of_column_event_probability_of_background_half`.

This is the form used in the spike liminf argument: the Beta kernel carries
the main cost `lam * a`, while the projective cap and the background event
consume only an arbitrarily small part of the slack. -/
theorem eventual_log_lower_of_column_event_probability_split_slack
    {betaProb capProb backgroundProb columnProb speed : ℕ → ℝ}
    {N s Ncap : ℕ → ℕ} {q δ : ℕ → ℝ}
    {lam a slack : ℝ}
    (hProduct :
      ∀ᶠ d in atTop,
        columnProb d = betaProb d * capProb d * backgroundProb d)
    (hBeta :
      ∀ᶠ d in atTop,
        BetaColumnIntervalLowerBound (betaProb d) (N d) (s d) (q d) (δ d))
    (hBetaKernel :
      ∀ᶠ d in atTop,
        -(lam * a + slack / 3) * speed d ≤
          Real.log (betaColumnIntervalKernel (N d) (s d) (q d) (δ d)))
    (hNcap : ∀ᶠ d in atTop, 1 ≤ Ncap d)
    (hCap :
      ∀ᶠ d in atTop,
        ProjectiveCapProbabilityLowerBound
          (capProb d) (Ncap d) (1 / (Ncap d : ℝ)))
    (hCapCost :
      ∀ᶠ d in atTop,
        capNLogNCost 2 (Ncap d : ℝ) ≤ (slack / 3) * speed d)
    (hBackgroundHalf :
      ∀ᶠ d in atTop, (1 / 2 : ℝ) ≤ backgroundProb d)
    (hBackgroundAbsorb :
      ∀ᶠ d in atTop,
        -(slack / 3) * speed d ≤ Real.log (1 / 2 : ℝ)) :
    ∀ᶠ d in atTop,
      Real.log (columnProb d) ≥ -(lam * a + slack) * speed d := by
  have h :=
    eventual_log_lower_of_column_event_probability_of_background_half
      (betaProb := betaProb) (capProb := capProb)
      (backgroundProb := backgroundProb) (columnProb := columnProb)
      (speed := speed) (N := N) (s := s) (Ncap := Ncap)
      (q := q) (δ := δ) (lam := lam) (a := a)
      (betaSlack := slack / 3) (capSlack := slack / 3)
      (backgroundSlack := slack / 3)
      hProduct hBeta hBetaKernel hNcap hCap hCapCost
      hBackgroundHalf hBackgroundAbsorb
  filter_upwards [h] with d hd
  have hcost :
      -(lam * a + slack / 3 + slack / 3 + slack / 3) * speed d =
        -(lam * a + slack) * speed d := by
    ring
  have hlower :
      -(lam * a + slack / 3 + slack / 3 + slack / 3) * speed d ≤
        Real.log (columnProb d) := by
    simpa using hd
  rw [hcost] at hlower
  exact hlower

/-- Abstract lower-bound input from a **family** of one-column events.

This is the honest lower-bound formulation: for each spike strength
`a > root` and each logarithmic slack, the proof may use a different favourable
one-column event.  That is exactly what happens in the concrete construction,
where the column-mass interval is centred at the scale determined by `a`.

The theorem packages the final monotonicity step:

`P(E_col(a,slack)) ≤ P(target)` and
`log P(E_col(a,slack)) ≥ -(lam*a+slack) speed`

imply the abstract spike lower-bound input for the target probability. -/
theorem abstractSpikeLowerBoundInput_of_oneColumn_event_family
    {targetProb speed : ℕ → ℝ}
    {columnProb : ℝ → ℝ → ℕ → ℝ} {root lam : ℝ}
    (hlam : 0 < lam)
    (hspeed : ∀ᶠ d in atTop, 0 < speed d)
    (hColumnPos :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, 0 < columnProb a slack d)
    (hColumnIncluded :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, columnProb a slack d ≤ targetProb d)
    (hColumnLower :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            Real.log (columnProb a slack d) ≥
              -(lam * a + slack) * speed d) :
    AbstractSpikeLowerBoundInput targetProb speed root lam where
  lambda_pos := hlam
  speed_pos_eventually := hspeed
  favorable_event_lower := by
    intro a ha slack hslack
    filter_upwards
      [hColumnLower a ha slack hslack,
        hColumnPos a ha slack hslack,
        hColumnIncluded a ha slack hslack]
      with d hLower hPos hIncluded
    have hlog_mono : Real.log (columnProb a slack d) ≤ Real.log (targetProb d) :=
      Real.log_le_log hPos hIncluded
    linarith

/-- Full one-column lower-bound pipeline.

For each `a > root` and each slack, the favourable event is decomposed into
three independent scalar probabilities:

* the one-column mass Beta interval;
* the projective cap for the column direction;
* the typical deleted-column background event.

The Beta kernel carries the main cost `lam*a`; the cap and background terms
are absorbed into `slack/3` each.  The output is the abstract lower-bound input
for the target deviation probability. -/
theorem abstractSpikeLowerBoundInput_of_oneColumn_probability_pipeline
    {targetProb speed : ℕ → ℝ}
    {betaProb capProb backgroundProb columnProb : ℝ → ℝ → ℕ → ℝ}
    {N s Ncap : ℕ → ℕ} {q δ : ℝ → ℝ → ℕ → ℝ}
    {root lam : ℝ}
    (hlam : 0 < lam)
    (hspeed : ∀ᶠ d in atTop, 0 < speed d)
    (hColumnIncluded :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, columnProb a slack d ≤ targetProb d)
    (hProduct :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            columnProb a slack d =
              betaProb a slack d * capProb a slack d * backgroundProb a slack d)
    (hBeta :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            BetaColumnIntervalLowerBound
              (betaProb a slack d) (N d) (s d) (q a slack d) (δ a slack d))
    (hBetaKernel :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            -(lam * a + slack / 3) * speed d ≤
              Real.log
                (betaColumnIntervalKernel
                  (N d) (s d) (q a slack d) (δ a slack d)))
    (hNcap : ∀ᶠ d in atTop, 1 ≤ Ncap d)
    (hCap :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ProjectiveCapProbabilityLowerBound
              (capProb a slack d) (Ncap d) (1 / (Ncap d : ℝ)))
    (hCapCost :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          capNLogNCost 2 (Ncap d : ℝ) ≤ (slack / 3) * speed d)
    (hBackgroundHalf :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, (1 / 2 : ℝ) ≤ backgroundProb a slack d)
    (hBackgroundAbsorb :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          -(slack / 3) * speed d ≤ Real.log (1 / 2 : ℝ)) :
    AbstractSpikeLowerBoundInput targetProb speed root lam := by
  refine
    abstractSpikeLowerBoundInput_of_oneColumn_event_family
      (targetProb := targetProb) (speed := speed)
      (columnProb := columnProb) (root := root) (lam := lam)
      hlam hspeed ?_ hColumnIncluded ?_
  · intro a ha slack hslack
    filter_upwards
      [hProduct a ha slack hslack,
        hBeta a ha slack hslack,
        hCap a ha slack hslack,
        hBackgroundHalf a ha slack hslack]
      with d hprod hbeta hcap hbg
    rw [hprod]
    have hbgpos : 0 < backgroundProb a slack d := by linarith
    exact mul_pos (mul_pos hbeta.prob_pos hcap.prob_pos) hbgpos
  · intro a ha slack hslack
    exact
      eventual_log_lower_of_column_event_probability_split_slack
        (betaProb := betaProb a slack)
        (capProb := capProb a slack)
        (backgroundProb := backgroundProb a slack)
        (columnProb := columnProb a slack)
        (speed := speed) (N := N) (s := s) (Ncap := Ncap)
        (q := q a slack) (δ := δ a slack)
        (lam := lam) (a := a) (slack := slack)
        (hProduct a ha slack hslack)
        (hBeta a ha slack hslack)
        (hBetaKernel a ha slack hslack)
        hNcap
        (hCap a ha slack hslack)
        (hCapCost slack hslack)
        (hBackgroundHalf a ha slack hslack)
        (hBackgroundAbsorb slack hslack)

/-! ## Abstract Hermitian two-block spherical decomposition -/

section HermitianBlockDecomposition

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Left block projection from the finite Hermitian direct sum
`ℂ^ι ⊕ ℂ^κ`, represented by coordinates on `Sum ι κ`. -/
noncomputable def hermitianBlockLeft
    (x : EuclideanSpace ℂ (Sum ι κ)) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun i : ι => x (Sum.inl i))

/-- Right block projection from the finite Hermitian direct sum
`ℂ^ι ⊕ ℂ^κ`, represented by coordinates on `Sum ι κ`. -/
noncomputable def hermitianBlockRight
    (x : EuclideanSpace ℂ (Sum ι κ)) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun j : κ => x (Sum.inr j))

/-- Internal Gaussian direction of the left Hermitian block.

For a Gaussian block vector `g = (g_E, g_F)`, this is the normalized direction
`g_E / ‖g_E‖`, totalized to return `0` when `g_E = 0`. -/
noncomputable def gaussianBlockLeftDirection
    (g : EuclideanSpace ℂ (Sum ι κ)) : EuclideanSpace ℂ ι :=
  ((‖hermitianBlockLeft (ι := ι) (κ := κ) g‖)⁻¹ : ℂ) •
    hermitianBlockLeft (ι := ι) (κ := κ) g

/-- Internal Gaussian direction of the right Hermitian block.

For a Gaussian block vector `g = (g_E, g_F)`, this is the normalized direction
`g_F / ‖g_F‖`, again totalized to return `0` on the zero block. -/
noncomputable def gaussianBlockRightDirection
    (g : EuclideanSpace ℂ (Sum ι κ)) : EuclideanSpace ℂ κ :=
  ((‖hermitianBlockRight (ι := ι) (κ := κ) g‖)⁻¹ : ℂ) •
    hermitianBlockRight (ι := ι) (κ := κ) g

/-- Squared mass of the left block.  For Haar measure on the complex unit
sphere this has `Beta(card ι, card κ)` law. -/
noncomputable def hermitianBlockMass
    (x : EuclideanSpace ℂ (Sum ι κ)) : ℝ :=
  ‖hermitianBlockLeft (ι := ι) (κ := κ) x‖ ^ 2

/-- Normalized left-block direction.  This total version returns zero when the
left block is zero.  In the nondegenerate spherical law that exceptional set is
null, but totality keeps the map usable in push-forward statements. -/
noncomputable def hermitianBlockLeftDirection
    (x : EuclideanSpace ℂ (Sum ι κ)) : EuclideanSpace ℂ ι :=
  ((‖hermitianBlockLeft (ι := ι) (κ := κ) x‖)⁻¹ : ℂ) •
    hermitianBlockLeft (ι := ι) (κ := κ) x

/-- Normalized right-block direction.  This total version returns zero when the
right block is zero. -/
noncomputable def hermitianBlockRightDirection
    (x : EuclideanSpace ℂ (Sum ι κ)) : EuclideanSpace ℂ κ :=
  ((‖hermitianBlockRight (ι := ι) (κ := κ) x‖)⁻¹ : ℂ) •
    hermitianBlockRight (ι := ι) (κ := κ) x

@[simp] theorem gaussianBlockLeftDirection_eq_hermitianBlockLeftDirection
    (g : EuclideanSpace ℂ (Sum ι κ)) :
    gaussianBlockLeftDirection (ι := ι) (κ := κ) g =
      hermitianBlockLeftDirection (ι := ι) (κ := κ) g := by
  rfl

@[simp] theorem gaussianBlockRightDirection_eq_hermitianBlockRightDirection
    (g : EuclideanSpace ℂ (Sum ι κ)) :
    gaussianBlockRightDirection (ι := ι) (κ := κ) g =
      hermitianBlockRightDirection (ι := ι) (κ := κ) g := by
  rfl

set_option linter.unusedSectionVars false in
@[fun_prop]
theorem measurable_hermitianBlockLeft :
    Measurable (hermitianBlockLeft (ι := ι) (κ := κ)) := by
  unfold hermitianBlockLeft
  fun_prop

set_option linter.unusedSectionVars false in
@[fun_prop]
theorem measurable_hermitianBlockRight :
    Measurable (hermitianBlockRight (ι := ι) (κ := κ)) := by
  unfold hermitianBlockRight
  fun_prop

@[fun_prop]
theorem measurable_hermitianBlockMass :
    Measurable (hermitianBlockMass (ι := ι) (κ := κ)) := by
  unfold hermitianBlockMass
  fun_prop

@[fun_prop]
theorem measurable_gaussianBlockLeftDirection :
    Measurable (gaussianBlockLeftDirection (ι := ι) (κ := κ)) := by
  unfold gaussianBlockLeftDirection
  fun_prop

@[fun_prop]
theorem measurable_gaussianBlockRightDirection :
    Measurable (gaussianBlockRightDirection (ι := ι) (κ := κ)) := by
  unfold gaussianBlockRightDirection
  fun_prop

@[fun_prop]
theorem measurable_hermitianBlockLeftDirection :
    Measurable (hermitianBlockLeftDirection (ι := ι) (κ := κ)) := by
  unfold hermitianBlockLeftDirection
  fun_prop

@[fun_prop]
theorem measurable_hermitianBlockRightDirection :
    Measurable (hermitianBlockRightDirection (ι := ι) (κ := κ)) := by
  unfold hermitianBlockRightDirection
  fun_prop

/-- Real/imaginary-coordinate block corresponding to the left Hermitian
component. -/
noncomputable def hermitianBlockLeftRealCoordinates
    (x :
      PptFactorization.GaussianModel.ComplexRealCoordSpace (Sum ι κ)) :
    PptFactorization.GaussianModel.ComplexRealCoordSpace ι :=
  WithLp.toLp 2 (fun ik : ι × Fin 2 => x (Sum.inl ik.1, ik.2))

/-- Real/imaginary-coordinate block corresponding to the right Hermitian
component. -/
noncomputable def hermitianBlockRightRealCoordinates
    (x :
      PptFactorization.GaussianModel.ComplexRealCoordSpace (Sum ι κ)) :
    PptFactorization.GaussianModel.ComplexRealCoordSpace κ :=
  WithLp.toLp 2 (fun jk : κ × Fin 2 => x (Sum.inr jk.1, jk.2))

@[fun_prop]
theorem measurable_hermitianBlockLeftRealCoordinates :
    Measurable (hermitianBlockLeftRealCoordinates (ι := ι) (κ := κ)) := by
  unfold hermitianBlockLeftRealCoordinates
  fun_prop

@[fun_prop]
theorem measurable_hermitianBlockRightRealCoordinates :
    Measurable (hermitianBlockRightRealCoordinates (ι := ι) (κ := κ)) := by
  unfold hermitianBlockRightRealCoordinates
  fun_prop

/-- Generic coordinate-selector lemma for the product real Gaussian. -/
theorem raw_standardGaussianCoordinateSelector_pi_map
    {α β : Type*} [Fintype α] [Fintype β]
    (g : β → α) (hg : Function.Injective g) :
    Measure.map
        (fun x : α → ℝ => fun b : β => x (g b))
        (Measure.pi (fun _ : α => ProbabilityTheory.gaussianReal 0 1)) =
      Measure.pi (fun _ : β => ProbabilityTheory.gaussianReal 0 1) := by
  let μ : Measure (α → ℝ) :=
    Measure.pi (fun _ : α => ProbabilityTheory.gaussianReal 0 1)
  have hbase :
      ProbabilityTheory.iIndepFun
        (fun a : α =>
          fun x : α → ℝ => x a) μ := by
    dsimp [μ]
    exact ProbabilityTheory.iIndepFun_pi
      (μ := fun _ : α => ProbabilityTheory.gaussianReal 0 1)
      (X := fun _ => (id : ℝ → ℝ))
      (fun _ => measurable_id.aemeasurable)
  have hsel :
      ProbabilityTheory.iIndepFun
        (fun b : β =>
          fun x : α → ℝ => x (g b)) μ := by
    simpa using hbase.precomp hg
  have hmeas :
      ∀ b : β,
        AEMeasurable
          (fun x : α → ℝ => x (g b)) μ := by
    intro b
    exact (measurable_pi_apply (g b)).aemeasurable
  have hmap := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map hmeas).1 hsel
  have heval (b : β) :
      Measure.map
          (fun x : α → ℝ => x (g b)) μ =
        ProbabilityTheory.gaussianReal 0 1 := by
    dsimp [μ]
    simpa using
      (measurePreserving_eval
        (μ := fun _ : α => ProbabilityTheory.gaussianReal 0 1)
        (g b)).map_eq
  rw [hmap]
  simp_rw [heval]

/-- The raw real coordinates of the left Hermitian block remain standard
Gaussian. -/
theorem raw_hermitianBlockLeftRealCoordinates_pi_map :
    Measure.map
        (fun x : ((Sum ι κ) × Fin 2) → ℝ =>
          fun ik : ι × Fin 2 => x (Sum.inl ik.1, ik.2))
        (Measure.pi
          (fun _ : (Sum ι κ) × Fin 2 => ProbabilityTheory.gaussianReal 0 1)) =
      Measure.pi
        (fun _ : ι × Fin 2 => ProbabilityTheory.gaussianReal 0 1) := by
  refine raw_standardGaussianCoordinateSelector_pi_map
    (g := fun ik : ι × Fin 2 => (Sum.inl ik.1, ik.2)) ?_
  intro a b h
  cases a
  cases b
  cases h
  rfl

/-- The raw real coordinates of the right Hermitian block remain standard
Gaussian. -/
theorem raw_hermitianBlockRightRealCoordinates_pi_map :
    Measure.map
        (fun x : ((Sum ι κ) × Fin 2) → ℝ =>
          fun jk : κ × Fin 2 => x (Sum.inr jk.1, jk.2))
        (Measure.pi
          (fun _ : (Sum ι κ) × Fin 2 => ProbabilityTheory.gaussianReal 0 1)) =
      Measure.pi
        (fun _ : κ × Fin 2 => ProbabilityTheory.gaussianReal 0 1) := by
  refine raw_standardGaussianCoordinateSelector_pi_map
    (g := fun jk : κ × Fin 2 => (Sum.inr jk.1, jk.2)) ?_
  intro a b h
  cases a
  cases b
  cases h
  rfl

/-- The full family of left/right real block coordinates is still a product
Gaussian after reindexing by the disjoint union of the two block coordinate
sets. -/
theorem raw_hermitianBlockRealCoordinates_joint_pi_map :
    Measure.map
        (fun x : ((Sum ι κ) × Fin 2) → ℝ =>
          fun s : (ι × Fin 2) ⊕ (κ × Fin 2) =>
            x ((Equiv.sumProdDistrib ι κ (Fin 2)).symm s))
        (Measure.pi
          (fun _ : (Sum ι κ) × Fin 2 => ProbabilityTheory.gaussianReal 0 1)) =
      Measure.pi
        (fun _ : (ι × Fin 2) ⊕ (κ × Fin 2) =>
          ProbabilityTheory.gaussianReal 0 1) := by
  refine raw_standardGaussianCoordinateSelector_pi_map
    (g := (Equiv.sumProdDistrib ι κ (Fin 2)).symm)
    (Equiv.injective (Equiv.sumProdDistrib ι κ (Fin 2)).symm)

/-- The raw pair of left/right real coordinate blocks is distributed as the
product of the two raw Gaussian block measures. -/
theorem raw_hermitianBlockRealCoordinates_pair_pi_map :
    Measure.map
        (fun x : ((Sum ι κ) × Fin 2) → ℝ =>
          (fun ik : ι × Fin 2 => x (Sum.inl ik.1, ik.2),
            fun jk : κ × Fin 2 => x (Sum.inr jk.1, jk.2)))
        (Measure.pi
          (fun _ : (Sum ι κ) × Fin 2 => ProbabilityTheory.gaussianReal 0 1)) =
      (Measure.pi
        (fun _ : ι × Fin 2 => ProbabilityTheory.gaussianReal 0 1)).prod
        (Measure.pi
          (fun _ : κ × Fin 2 => ProbabilityTheory.gaussianReal 0 1)) := by
  let rawJoin :
      (((Sum ι κ) × Fin 2) → ℝ) →
        (((ι × Fin 2) ⊕ (κ × Fin 2)) → ℝ) :=
    fun x s => x ((Equiv.sumProdDistrib ι κ (Fin 2)).symm s)
  have hmeasRawJoin : Measurable rawJoin := by
    dsimp [rawJoin]
    refine measurable_pi_lambda _ ?_
    intro s
    exact measurable_pi_apply _
  calc
    Measure.map
        (fun x : ((Sum ι κ) × Fin 2) → ℝ =>
          (fun ik : ι × Fin 2 => x (Sum.inl ik.1, ik.2),
            fun jk : κ × Fin 2 => x (Sum.inr jk.1, jk.2)))
        (Measure.pi
          (fun _ : (Sum ι κ) × Fin 2 => ProbabilityTheory.gaussianReal 0 1)) =
      Measure.map
        (MeasurableEquiv.sumPiEquivProdPi
          (fun _ : (ι × Fin 2) ⊕ (κ × Fin 2) => ℝ))
        (Measure.map rawJoin
          (Measure.pi
            (fun _ : (Sum ι κ) × Fin 2 => ProbabilityTheory.gaussianReal 0 1))) := by
        symm
        simpa [rawJoin, Function.comp] using
          (Measure.map_map
            (μ := Measure.pi
              (fun _ : (Sum ι κ) × Fin 2 => ProbabilityTheory.gaussianReal 0 1))
            (f := rawJoin)
            (g := MeasurableEquiv.sumPiEquivProdPi
              (fun _ : (ι × Fin 2) ⊕ (κ × Fin 2) => ℝ))
            (MeasurableEquiv.sumPiEquivProdPi
              (fun _ : (ι × Fin 2) ⊕ (κ × Fin 2) => ℝ)).measurable
            hmeasRawJoin)
    _ =
      Measure.map
        (MeasurableEquiv.sumPiEquivProdPi
          (fun _ : (ι × Fin 2) ⊕ (κ × Fin 2) => ℝ))
        (Measure.pi
          (fun _ : (ι × Fin 2) ⊕ (κ × Fin 2) =>
            ProbabilityTheory.gaussianReal 0 1)) := by
        rw [raw_hermitianBlockRealCoordinates_joint_pi_map (ι := ι) (κ := κ)]
    _ =
      (Measure.pi
        (fun _ : ι × Fin 2 => ProbabilityTheory.gaussianReal 0 1)).prod
        (Measure.pi
          (fun _ : κ × Fin 2 => ProbabilityTheory.gaussianReal 0 1)) := by
        simpa using
          (measurePreserving_sumPiEquivProdPi
            (X := fun _ : (ι × Fin 2) ⊕ (κ × Fin 2) => ℝ)
            (fun _ => ProbabilityTheory.gaussianReal 0 1)).map_eq

/-- Passing from real Gaussian coordinates to the complex vector commutes with
taking the left Hermitian block. -/
theorem hermitianBlockLeft_complexVectorOfRealCoordinates
    (x :
      PptFactorization.GaussianModel.ComplexRealCoordSpace (Sum ι κ)) :
    hermitianBlockLeft (ι := ι) (κ := κ)
        (PptFactorization.GaussianModel.complexVectorOfRealCoordinates
          (ι := Sum ι κ) x) =
      PptFactorization.GaussianModel.complexVectorOfRealCoordinates
        (ι := ι)
        (hermitianBlockLeftRealCoordinates (ι := ι) (κ := κ) x) := by
  ext i
  rfl

/-- Passing from real Gaussian coordinates to the complex vector commutes with
taking the right Hermitian block. -/
theorem hermitianBlockRight_complexVectorOfRealCoordinates
    (x :
      PptFactorization.GaussianModel.ComplexRealCoordSpace (Sum ι κ)) :
    hermitianBlockRight (ι := ι) (κ := κ)
        (PptFactorization.GaussianModel.complexVectorOfRealCoordinates
          (ι := Sum ι κ) x) =
      PptFactorization.GaussianModel.complexVectorOfRealCoordinates
        (ι := κ)
        (hermitianBlockRightRealCoordinates (ι := ι) (κ := κ) x) := by
  ext j
  rfl

/-- The left real coordinate block of a standard complex Gaussian vector is a
standard finite-dimensional real Gaussian vector. -/
theorem hermitianBlockLeftRealCoordinates_map_stdGaussian :
    Measure.map
        (hermitianBlockLeftRealCoordinates (ι := ι) (κ := κ))
        (ProbabilityTheory.stdGaussian
          (PptFactorization.GaussianModel.ComplexRealCoordSpace (Sum ι κ))) =
      ProbabilityTheory.stdGaussian
        (PptFactorization.GaussianModel.ComplexRealCoordSpace ι) := by
  let rawProj : ((Sum ι κ) × Fin 2 → ℝ) → (ι × Fin 2 → ℝ) :=
    fun x ik => x (Sum.inl ik.1, ik.2)
  have hcomp :
      hermitianBlockLeftRealCoordinates (ι := ι) (κ := κ) ∘
          (WithLp.toLp 2 :
            (((Sum ι κ) × Fin 2) → ℝ) →
              PptFactorization.GaussianModel.ComplexRealCoordSpace (Sum ι κ)) =
        (WithLp.toLp 2 :
          ((ι × Fin 2) → ℝ) →
            PptFactorization.GaussianModel.ComplexRealCoordSpace ι) ∘ rawProj := by
    funext x
    ext ik
    rfl
  rw [← ProbabilityTheory.map_pi_eq_stdGaussian
    (ι := (Sum ι κ) × Fin 2)]
  calc
    Measure.map
        (hermitianBlockLeftRealCoordinates (ι := ι) (κ := κ))
        (Measure.map (WithLp.toLp 2)
          (Measure.pi
            (fun _ : (Sum ι κ) × Fin 2 =>
              ProbabilityTheory.gaussianReal 0 1))) =
      Measure.map
        (hermitianBlockLeftRealCoordinates (ι := ι) (κ := κ) ∘ WithLp.toLp 2)
        (Measure.pi
          (fun _ : (Sum ι κ) × Fin 2 =>
            ProbabilityTheory.gaussianReal 0 1)) := by
        rw [Measure.map_map]
        · exact measurable_hermitianBlockLeftRealCoordinates (ι := ι) (κ := κ)
        · fun_prop
    _ =
      Measure.map
        ((WithLp.toLp 2 :
          ((ι × Fin 2) → ℝ) →
            PptFactorization.GaussianModel.ComplexRealCoordSpace ι) ∘ rawProj)
        (Measure.pi
          (fun _ : (Sum ι κ) × Fin 2 =>
            ProbabilityTheory.gaussianReal 0 1)) := by
        rw [hcomp]
    _ =
      Measure.map (WithLp.toLp 2)
        (Measure.map rawProj
          (Measure.pi
            (fun _ : (Sum ι κ) × Fin 2 =>
              ProbabilityTheory.gaussianReal 0 1))) := by
        symm
        exact
          (Measure.map_map
            (μ := Measure.pi
              (fun _ : (Sum ι κ) × Fin 2 =>
                ProbabilityTheory.gaussianReal 0 1))
            (f := rawProj)
            (g := (WithLp.toLp 2 :
              ((ι × Fin 2) → ℝ) →
                PptFactorization.GaussianModel.ComplexRealCoordSpace ι))
            (by fun_prop)
            (by fun_prop))
    _ =
      Measure.map (WithLp.toLp 2)
        (Measure.pi
          (fun _ : ι × Fin 2 =>
            ProbabilityTheory.gaussianReal 0 1)) := by
        rw [raw_hermitianBlockLeftRealCoordinates_pi_map (ι := ι) (κ := κ)]
    _ =
      ProbabilityTheory.stdGaussian
        (PptFactorization.GaussianModel.ComplexRealCoordSpace ι) := by
        exact ProbabilityTheory.map_pi_eq_stdGaussian

/-- The right real coordinate block of a standard complex Gaussian vector is a
standard finite-dimensional real Gaussian vector. -/
theorem hermitianBlockRightRealCoordinates_map_stdGaussian :
    Measure.map
        (hermitianBlockRightRealCoordinates (ι := ι) (κ := κ))
        (ProbabilityTheory.stdGaussian
          (PptFactorization.GaussianModel.ComplexRealCoordSpace (Sum ι κ))) =
      ProbabilityTheory.stdGaussian
        (PptFactorization.GaussianModel.ComplexRealCoordSpace κ) := by
  let rawProj : ((Sum ι κ) × Fin 2 → ℝ) → (κ × Fin 2 → ℝ) :=
    fun x jk => x (Sum.inr jk.1, jk.2)
  have hcomp :
      hermitianBlockRightRealCoordinates (ι := ι) (κ := κ) ∘
          (WithLp.toLp 2 :
            (((Sum ι κ) × Fin 2) → ℝ) →
              PptFactorization.GaussianModel.ComplexRealCoordSpace (Sum ι κ)) =
        (WithLp.toLp 2 :
          ((κ × Fin 2) → ℝ) →
            PptFactorization.GaussianModel.ComplexRealCoordSpace κ) ∘ rawProj := by
    funext x
    ext jk
    rfl
  rw [← ProbabilityTheory.map_pi_eq_stdGaussian
    (ι := (Sum ι κ) × Fin 2)]
  calc
    Measure.map
        (hermitianBlockRightRealCoordinates (ι := ι) (κ := κ))
        (Measure.map (WithLp.toLp 2)
          (Measure.pi
            (fun _ : (Sum ι κ) × Fin 2 =>
              ProbabilityTheory.gaussianReal 0 1))) =
      Measure.map
        (hermitianBlockRightRealCoordinates (ι := ι) (κ := κ) ∘ WithLp.toLp 2)
        (Measure.pi
          (fun _ : (Sum ι κ) × Fin 2 =>
            ProbabilityTheory.gaussianReal 0 1)) := by
        rw [Measure.map_map]
        · exact measurable_hermitianBlockRightRealCoordinates (ι := ι) (κ := κ)
        · fun_prop
    _ =
      Measure.map
        ((WithLp.toLp 2 :
          ((κ × Fin 2) → ℝ) →
            PptFactorization.GaussianModel.ComplexRealCoordSpace κ) ∘ rawProj)
        (Measure.pi
          (fun _ : (Sum ι κ) × Fin 2 =>
            ProbabilityTheory.gaussianReal 0 1)) := by
        rw [hcomp]
    _ =
      Measure.map (WithLp.toLp 2)
        (Measure.map rawProj
          (Measure.pi
            (fun _ : (Sum ι κ) × Fin 2 =>
              ProbabilityTheory.gaussianReal 0 1))) := by
        symm
        exact
          (Measure.map_map
            (μ := Measure.pi
              (fun _ : (Sum ι κ) × Fin 2 =>
                ProbabilityTheory.gaussianReal 0 1))
            (f := rawProj)
            (g := (WithLp.toLp 2 :
              ((κ × Fin 2) → ℝ) →
                PptFactorization.GaussianModel.ComplexRealCoordSpace κ))
            (by fun_prop)
            (by fun_prop))
    _ =
      Measure.map (WithLp.toLp 2)
        (Measure.pi
          (fun _ : κ × Fin 2 =>
            ProbabilityTheory.gaussianReal 0 1)) := by
        rw [raw_hermitianBlockRightRealCoordinates_pi_map (ι := ι) (κ := κ)]
    _ =
      ProbabilityTheory.stdGaussian
        (PptFactorization.GaussianModel.ComplexRealCoordSpace κ) := by
        exact ProbabilityTheory.map_pi_eq_stdGaussian

/-- The pair of real coordinate blocks of a standard complex Gaussian vector is
distributed as the product of the two standard real block Gaussians. -/
theorem hermitianBlockRealCoordinates_pair_map_stdGaussian :
    Measure.map
        (fun x :
          PptFactorization.GaussianModel.ComplexRealCoordSpace (Sum ι κ) =>
          (hermitianBlockLeftRealCoordinates (ι := ι) (κ := κ) x,
            hermitianBlockRightRealCoordinates (ι := ι) (κ := κ) x))
        (ProbabilityTheory.stdGaussian
          (PptFactorization.GaussianModel.ComplexRealCoordSpace (Sum ι κ))) =
      (ProbabilityTheory.stdGaussian
        (PptFactorization.GaussianModel.ComplexRealCoordSpace ι)).prod
        (ProbabilityTheory.stdGaussian
          (PptFactorization.GaussianModel.ComplexRealCoordSpace κ)) := by
  let rawPair :
      (((Sum ι κ) × Fin 2) → ℝ) →
        ((ι × Fin 2) → ℝ) × ((κ × Fin 2) → ℝ) :=
    fun x =>
      (fun ik : ι × Fin 2 => x (Sum.inl ik.1, ik.2),
        fun jk : κ × Fin 2 => x (Sum.inr jk.1, jk.2))
  let rawJoin :
      (((Sum ι κ) × Fin 2) → ℝ) →
        (((ι × Fin 2) ⊕ (κ × Fin 2)) → ℝ) :=
    fun x s =>
      match s with
      | Sum.inl ik => x (Sum.inl ik.1, ik.2)
      | Sum.inr jk => x (Sum.inr jk.1, jk.2)
  let pairToLp :
      (((ι × Fin 2) → ℝ) × ((κ × Fin 2) → ℝ)) →
        PptFactorization.GaussianModel.ComplexRealCoordSpace ι ×
          PptFactorization.GaussianModel.ComplexRealCoordSpace κ :=
    fun y => (WithLp.toLp 2 y.1, WithLp.toLp 2 y.2)
  have hcomp :
      (fun x :
        PptFactorization.GaussianModel.ComplexRealCoordSpace (Sum ι κ) =>
          (hermitianBlockLeftRealCoordinates (ι := ι) (κ := κ) x,
            hermitianBlockRightRealCoordinates (ι := ι) (κ := κ) x)) ∘
          (WithLp.toLp 2 :
            (((Sum ι κ) × Fin 2) → ℝ) →
              PptFactorization.GaussianModel.ComplexRealCoordSpace (Sum ι κ)) =
        pairToLp ∘ rawPair := by
    funext x
    ext <;> rfl
  rw [← ProbabilityTheory.map_pi_eq_stdGaussian
    (ι := (Sum ι κ) × Fin 2)]
  calc
    Measure.map
        (fun x :
          PptFactorization.GaussianModel.ComplexRealCoordSpace (Sum ι κ) =>
          (hermitianBlockLeftRealCoordinates (ι := ι) (κ := κ) x,
            hermitianBlockRightRealCoordinates (ι := ι) (κ := κ) x))
        (Measure.map (WithLp.toLp 2)
          (Measure.pi
            (fun _ : (Sum ι κ) × Fin 2 =>
              ProbabilityTheory.gaussianReal 0 1))) =
      Measure.map
        ((fun x :
          PptFactorization.GaussianModel.ComplexRealCoordSpace (Sum ι κ) =>
            (hermitianBlockLeftRealCoordinates (ι := ι) (κ := κ) x,
              hermitianBlockRightRealCoordinates (ι := ι) (κ := κ) x)) ∘
          WithLp.toLp 2)
        (Measure.pi
          (fun _ : (Sum ι κ) × Fin 2 =>
            ProbabilityTheory.gaussianReal 0 1)) := by
        rw [Measure.map_map]
        · fun_prop
        · fun_prop
    _ =
      Measure.map (pairToLp ∘ rawPair)
        (Measure.pi
          (fun _ : (Sum ι κ) × Fin 2 =>
            ProbabilityTheory.gaussianReal 0 1)) := by
        rw [hcomp]
    _ =
      Measure.map pairToLp
        (Measure.map rawPair
          (Measure.pi
            (fun _ : (Sum ι κ) × Fin 2 =>
              ProbabilityTheory.gaussianReal 0 1))) := by
        symm
        exact
          (Measure.map_map
            (μ := Measure.pi
              (fun _ : (Sum ι κ) × Fin 2 =>
                ProbabilityTheory.gaussianReal 0 1))
            (f := rawPair)
            (g := pairToLp)
            (show Measurable pairToLp by
              dsimp [pairToLp]
              fun_prop)
            (by
              dsimp [rawPair]
              fun_prop))
    _ =
      Measure.map pairToLp
        ((Measure.pi
          (fun _ : ι × Fin 2 =>
            ProbabilityTheory.gaussianReal 0 1)).prod
          (Measure.pi
            (fun _ : κ × Fin 2 =>
              ProbabilityTheory.gaussianReal 0 1))) := by
        rw [raw_hermitianBlockRealCoordinates_pair_pi_map (ι := ι) (κ := κ)]
    _ =
      (Measure.map
        (WithLp.toLp 2 :
          ((ι × Fin 2) → ℝ) →
            PptFactorization.GaussianModel.ComplexRealCoordSpace ι)
        (Measure.pi
          (fun _ : ι × Fin 2 =>
            ProbabilityTheory.gaussianReal 0 1))).prod
        (Measure.map
          (WithLp.toLp 2 :
            ((κ × Fin 2) → ℝ) →
              PptFactorization.GaussianModel.ComplexRealCoordSpace κ)
          (Measure.pi
            (fun _ : κ × Fin 2 =>
              ProbabilityTheory.gaussianReal 0 1))) := by
        simpa [pairToLp, Prod.map] using
          (Measure.map_prod_map
            (Measure.pi
              (fun _ : ι × Fin 2 =>
                ProbabilityTheory.gaussianReal 0 1))
            (Measure.pi
              (fun _ : κ × Fin 2 =>
                ProbabilityTheory.gaussianReal 0 1))
            (show Measurable
              (WithLp.toLp 2 :
                ((ι × Fin 2) → ℝ) →
                  PptFactorization.GaussianModel.ComplexRealCoordSpace ι) by
              fun_prop)
            (show Measurable
              (WithLp.toLp 2 :
                ((κ × Fin 2) → ℝ) →
                  PptFactorization.GaussianModel.ComplexRealCoordSpace κ) by
              fun_prop)).symm
    _ =
      (ProbabilityTheory.stdGaussian
        (PptFactorization.GaussianModel.ComplexRealCoordSpace ι)).prod
        (ProbabilityTheory.stdGaussian
          (PptFactorization.GaussianModel.ComplexRealCoordSpace κ)) := by
        rw [ProbabilityTheory.map_pi_eq_stdGaussian,
          ProbabilityTheory.map_pi_eq_stdGaussian]

/-- The left Hermitian block of a standard complex Gaussian vector is itself a
standard complex Gaussian vector. -/
theorem hermitianBlockLeft_map_standardComplexGaussianVectorMeasure :
    Measure.map
        (hermitianBlockLeft (ι := ι) (κ := κ))
        (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
          (Sum ι κ)) =
      PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure ι := by
  unfold PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
  calc
    Measure.map
        (hermitianBlockLeft (ι := ι) (κ := κ))
        (Measure.map
          (PptFactorization.GaussianModel.complexVectorOfRealCoordinates
            (ι := Sum ι κ))
          (ProbabilityTheory.stdGaussian
            (PptFactorization.GaussianModel.ComplexRealCoordSpace
              (Sum ι κ)))) =
      Measure.map
        (hermitianBlockLeft (ι := ι) (κ := κ) ∘
          PptFactorization.GaussianModel.complexVectorOfRealCoordinates
            (ι := Sum ι κ))
        (ProbabilityTheory.stdGaussian
          (PptFactorization.GaussianModel.ComplexRealCoordSpace
            (Sum ι κ))) := by
        rw [Measure.map_map]
        · exact measurable_hermitianBlockLeft (ι := ι) (κ := κ)
        · exact
            PptFactorization.GaussianModel.measurable_complexVectorOfRealCoordinates
              (Sum ι κ)
    _ =
      Measure.map
        (PptFactorization.GaussianModel.complexVectorOfRealCoordinates
          (ι := ι) ∘ hermitianBlockLeftRealCoordinates (ι := ι) (κ := κ))
        (ProbabilityTheory.stdGaussian
          (PptFactorization.GaussianModel.ComplexRealCoordSpace
            (Sum ι κ))) := by
        rfl
    _ =
      Measure.map
        (PptFactorization.GaussianModel.complexVectorOfRealCoordinates
          (ι := ι))
        (Measure.map
          (hermitianBlockLeftRealCoordinates (ι := ι) (κ := κ))
          (ProbabilityTheory.stdGaussian
            (PptFactorization.GaussianModel.ComplexRealCoordSpace
              (Sum ι κ)))) := by
        symm
        simpa [Function.comp] using
          (Measure.map_map
            (μ := ProbabilityTheory.stdGaussian
              (PptFactorization.GaussianModel.ComplexRealCoordSpace
                (Sum ι κ)))
            (f := hermitianBlockLeftRealCoordinates (ι := ι) (κ := κ))
            (g := PptFactorization.GaussianModel.complexVectorOfRealCoordinates
              (ι := ι))
            (PptFactorization.GaussianModel.measurable_complexVectorOfRealCoordinates
              ι)
            (measurable_hermitianBlockLeftRealCoordinates (ι := ι) (κ := κ)))
    _ =
      Measure.map
        (PptFactorization.GaussianModel.complexVectorOfRealCoordinates
          (ι := ι))
        (ProbabilityTheory.stdGaussian
          (PptFactorization.GaussianModel.ComplexRealCoordSpace ι)) := by
        rw [hermitianBlockLeftRealCoordinates_map_stdGaussian
          (ι := ι) (κ := κ)]

/-- The right Hermitian block of a standard complex Gaussian vector is itself a
standard complex Gaussian vector. -/
theorem hermitianBlockRight_map_standardComplexGaussianVectorMeasure :
    Measure.map
        (hermitianBlockRight (ι := ι) (κ := κ))
        (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
          (Sum ι κ)) =
      PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure κ := by
  unfold PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
  calc
    Measure.map
        (hermitianBlockRight (ι := ι) (κ := κ))
        (Measure.map
          (PptFactorization.GaussianModel.complexVectorOfRealCoordinates
            (ι := Sum ι κ))
          (ProbabilityTheory.stdGaussian
            (PptFactorization.GaussianModel.ComplexRealCoordSpace
              (Sum ι κ)))) =
      Measure.map
        (hermitianBlockRight (ι := ι) (κ := κ) ∘
          PptFactorization.GaussianModel.complexVectorOfRealCoordinates
            (ι := Sum ι κ))
        (ProbabilityTheory.stdGaussian
          (PptFactorization.GaussianModel.ComplexRealCoordSpace
            (Sum ι κ))) := by
        rw [Measure.map_map]
        · exact measurable_hermitianBlockRight (ι := ι) (κ := κ)
        · exact
            PptFactorization.GaussianModel.measurable_complexVectorOfRealCoordinates
              (Sum ι κ)
    _ =
      Measure.map
        (PptFactorization.GaussianModel.complexVectorOfRealCoordinates
          (ι := κ) ∘ hermitianBlockRightRealCoordinates (ι := ι) (κ := κ))
        (ProbabilityTheory.stdGaussian
          (PptFactorization.GaussianModel.ComplexRealCoordSpace
            (Sum ι κ))) := by
        rfl
    _ =
      Measure.map
        (PptFactorization.GaussianModel.complexVectorOfRealCoordinates
          (ι := κ))
        (Measure.map
          (hermitianBlockRightRealCoordinates (ι := ι) (κ := κ))
          (ProbabilityTheory.stdGaussian
            (PptFactorization.GaussianModel.ComplexRealCoordSpace
              (Sum ι κ)))) := by
        symm
        simpa [Function.comp] using
          (Measure.map_map
            (μ := ProbabilityTheory.stdGaussian
              (PptFactorization.GaussianModel.ComplexRealCoordSpace
                (Sum ι κ)))
            (f := hermitianBlockRightRealCoordinates (ι := ι) (κ := κ))
            (g := PptFactorization.GaussianModel.complexVectorOfRealCoordinates
              (ι := κ))
            (PptFactorization.GaussianModel.measurable_complexVectorOfRealCoordinates
              κ)
            (measurable_hermitianBlockRightRealCoordinates (ι := ι) (κ := κ)))
    _ =
      Measure.map
        (PptFactorization.GaussianModel.complexVectorOfRealCoordinates
          (ι := κ))
        (ProbabilityTheory.stdGaussian
          (PptFactorization.GaussianModel.ComplexRealCoordSpace κ)) := by
        rw [hermitianBlockRightRealCoordinates_map_stdGaussian
          (ι := ι) (κ := κ)]

/-- The pair of Hermitian Gaussian blocks has the product standard-complex
Gaussian law. -/
theorem hermitianBlockLeftRight_pair_map_standardComplexGaussianVectorMeasure :
    Measure.map
        (fun z : EuclideanSpace ℂ (Sum ι κ) =>
          (hermitianBlockLeft (ι := ι) (κ := κ) z,
            hermitianBlockRight (ι := ι) (κ := κ) z))
        (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
          (Sum ι κ)) =
      (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure ι).prod
        (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure κ) := by
  let pairReal :
      PptFactorization.GaussianModel.ComplexRealCoordSpace (Sum ι κ) →
        PptFactorization.GaussianModel.ComplexRealCoordSpace ι ×
          PptFactorization.GaussianModel.ComplexRealCoordSpace κ :=
    fun x =>
      (hermitianBlockLeftRealCoordinates (ι := ι) (κ := κ) x,
        hermitianBlockRightRealCoordinates (ι := ι) (κ := κ) x)
  let pairComplex :
      PptFactorization.GaussianModel.ComplexRealCoordSpace ι ×
          PptFactorization.GaussianModel.ComplexRealCoordSpace κ →
        EuclideanSpace ℂ ι × EuclideanSpace ℂ κ :=
    fun y =>
      (PptFactorization.GaussianModel.complexVectorOfRealCoordinates
        (ι := ι) y.1,
        PptFactorization.GaussianModel.complexVectorOfRealCoordinates
          (ι := κ) y.2)
  have hcomp :
      (fun z : EuclideanSpace ℂ (Sum ι κ) =>
        (hermitianBlockLeft (ι := ι) (κ := κ) z,
          hermitianBlockRight (ι := ι) (κ := κ) z)) ∘
          PptFactorization.GaussianModel.complexVectorOfRealCoordinates
            (ι := Sum ι κ) =
        pairComplex ∘ pairReal := by
    funext x
    ext <;> rfl
  unfold PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
  calc
    Measure.map
        (fun z : EuclideanSpace ℂ (Sum ι κ) =>
          (hermitianBlockLeft (ι := ι) (κ := κ) z,
            hermitianBlockRight (ι := ι) (κ := κ) z))
        (Measure.map
          (PptFactorization.GaussianModel.complexVectorOfRealCoordinates
            (ι := Sum ι κ))
          (ProbabilityTheory.stdGaussian
            (PptFactorization.GaussianModel.ComplexRealCoordSpace
              (Sum ι κ)))) =
      Measure.map
        ((fun z : EuclideanSpace ℂ (Sum ι κ) =>
          (hermitianBlockLeft (ι := ι) (κ := κ) z,
            hermitianBlockRight (ι := ι) (κ := κ) z)) ∘
          PptFactorization.GaussianModel.complexVectorOfRealCoordinates
            (ι := Sum ι κ))
        (ProbabilityTheory.stdGaussian
          (PptFactorization.GaussianModel.ComplexRealCoordSpace
            (Sum ι κ))) := by
        rw [Measure.map_map]
        · fun_prop
        · exact
            PptFactorization.GaussianModel.measurable_complexVectorOfRealCoordinates
              (Sum ι κ)
    _ =
      Measure.map (pairComplex ∘ pairReal)
        (ProbabilityTheory.stdGaussian
          (PptFactorization.GaussianModel.ComplexRealCoordSpace
            (Sum ι κ))) := by
        rw [hcomp]
    _ =
      Measure.map pairComplex
        (Measure.map pairReal
          (ProbabilityTheory.stdGaussian
            (PptFactorization.GaussianModel.ComplexRealCoordSpace
              (Sum ι κ)))) := by
        symm
        simpa [Function.comp, pairReal] using
          (Measure.map_map
            (μ := ProbabilityTheory.stdGaussian
              (PptFactorization.GaussianModel.ComplexRealCoordSpace
                (Sum ι κ)))
            (f := pairReal)
            (g := pairComplex)
            (by fun_prop)
            (by
              dsimp [pairReal]
              fun_prop))
    _ =
      Measure.map pairComplex
        ((ProbabilityTheory.stdGaussian
          (PptFactorization.GaussianModel.ComplexRealCoordSpace ι)).prod
          (ProbabilityTheory.stdGaussian
            (PptFactorization.GaussianModel.ComplexRealCoordSpace κ))) := by
        rw [hermitianBlockRealCoordinates_pair_map_stdGaussian
          (ι := ι) (κ := κ)]
    _ =
      (Measure.map
        (PptFactorization.GaussianModel.complexVectorOfRealCoordinates
          (ι := ι))
        (ProbabilityTheory.stdGaussian
          (PptFactorization.GaussianModel.ComplexRealCoordSpace ι))).prod
        (Measure.map
          (PptFactorization.GaussianModel.complexVectorOfRealCoordinates
            (ι := κ))
          (ProbabilityTheory.stdGaussian
            (PptFactorization.GaussianModel.ComplexRealCoordSpace κ))) := by
        simpa [pairComplex, Prod.map] using
          (Measure.map_prod_map
            (ProbabilityTheory.stdGaussian
              (PptFactorization.GaussianModel.ComplexRealCoordSpace ι))
            (ProbabilityTheory.stdGaussian
              (PptFactorization.GaussianModel.ComplexRealCoordSpace κ))
            (PptFactorization.GaussianModel.measurable_complexVectorOfRealCoordinates
              ι)
            (PptFactorization.GaussianModel.measurable_complexVectorOfRealCoordinates
              κ)).symm

/-- The left and right Hermitian blocks of a standard complex Gaussian vector
on `ℂ^(ι ⊕ κ)` are independent. -/
theorem hermitianBlockLeft_indep_hermitianBlockRight :
    ProbabilityTheory.IndepFun
      (hermitianBlockLeft (ι := ι) (κ := κ))
      (hermitianBlockRight (ι := ι) (κ := κ))
      (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
        (Sum ι κ)) := by
  refine (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
    (measurable_hermitianBlockLeft (ι := ι) (κ := κ)).aemeasurable
    (measurable_hermitianBlockRight (ι := ι) (κ := κ)).aemeasurable).2 ?_
  rw [hermitianBlockLeftRight_pair_map_standardComplexGaussianVectorMeasure
    (ι := ι) (κ := κ)]
  rw [hermitianBlockLeft_map_standardComplexGaussianVectorMeasure
    (ι := ι) (κ := κ)]
  rw [hermitianBlockRight_map_standardComplexGaussianVectorMeasure
    (ι := ι) (κ := κ)]

set_option linter.unusedSectionVars false in
/-- Scaling the ambient block vector by a positive real scalar does not change
the internal direction of the left block. -/
theorem hermitianBlockLeftDirection_real_smul
    {r : ℝ} (hr : 0 < r)
    (g : EuclideanSpace ℂ (Sum ι κ)) :
    hermitianBlockLeftDirection
        (ι := ι) (κ := κ)
        ((r : ℂ) • g) =
      hermitianBlockLeftDirection (ι := ι) (κ := κ) g := by
  by_cases hL : hermitianBlockLeft (ι := ι) (κ := κ) g = 0
  · have hL' :
        hermitianBlockLeft
            (ι := ι) (κ := κ)
            ((r : ℂ) • g) = 0 := by
      ext i
      have hi : g (Sum.inl i) = 0 := by
        have hcoord :
            hermitianBlockLeft (ι := ι) (κ := κ) g i = 0 := by
          simpa using congrArg (fun v : EuclideanSpace ℂ ι => v i) hL
        simpa [hermitianBlockLeft] using hcoord
      simp [hermitianBlockLeft, hi]
    unfold hermitianBlockLeftDirection
    rw [hL, hL']
  · have hL_norm_ne : ‖hermitianBlockLeft (ι := ι) (κ := κ) g‖ ≠ 0 := by
      exact norm_ne_zero_iff.mpr hL
    have hr_ne : r ≠ 0 := by linarith
    have hleft_smul :
        hermitianBlockLeft
            (ι := ι) (κ := κ)
            ((r : ℂ) • g) =
          ((r : ℂ) • hermitianBlockLeft (ι := ι) (κ := κ) g) := by
      ext i
      simp [hermitianBlockLeft]
    have hnorm_smul :
        ‖((r : ℂ) • hermitianBlockLeft (ι := ι) (κ := κ) g)‖ =
          r * ‖hermitianBlockLeft (ι := ι) (κ := κ) g‖ := by
      rw [norm_smul]
      simp [Real.norm_eq_abs, abs_of_pos hr]
    have hcoefR :
        (r * ‖hermitianBlockLeft (ι := ι) (κ := κ) g‖)⁻¹ * r =
          (‖hermitianBlockLeft (ι := ι) (κ := κ) g‖)⁻¹ := by
      field_simp [hr_ne, hL_norm_ne]
    have hcoef :
        ((((r * ‖hermitianBlockLeft (ι := ι) (κ := κ) g‖ : ℝ) : ℂ)⁻¹) *
            (r : ℂ)) =
          ((‖hermitianBlockLeft (ι := ι) (κ := κ) g‖)⁻¹ : ℂ) := by
      exact_mod_cast hcoefR
    unfold hermitianBlockLeftDirection
    rw [hleft_smul, hnorm_smul, smul_smul, hcoef]

set_option linter.unusedSectionVars false in
/-- Scaling the ambient block vector by a positive real scalar does not change
the internal direction of the right block. -/
theorem hermitianBlockRightDirection_real_smul
    {r : ℝ} (hr : 0 < r)
    (g : EuclideanSpace ℂ (Sum ι κ)) :
    hermitianBlockRightDirection
        (ι := ι) (κ := κ)
        ((r : ℂ) • g) =
      hermitianBlockRightDirection (ι := ι) (κ := κ) g := by
  by_cases hR : hermitianBlockRight (ι := ι) (κ := κ) g = 0
  · have hR' :
        hermitianBlockRight
            (ι := ι) (κ := κ)
            ((r : ℂ) • g) = 0 := by
      ext j
      have hj : g (Sum.inr j) = 0 := by
        have hcoord :
            hermitianBlockRight (ι := ι) (κ := κ) g j = 0 := by
          simpa using congrArg (fun v : EuclideanSpace ℂ κ => v j) hR
        simpa [hermitianBlockRight] using hcoord
      simp [hermitianBlockRight, hj]
    unfold hermitianBlockRightDirection
    rw [hR, hR']
  · have hR_norm_ne : ‖hermitianBlockRight (ι := ι) (κ := κ) g‖ ≠ 0 := by
      exact norm_ne_zero_iff.mpr hR
    have hr_ne : r ≠ 0 := by linarith
    have hright_smul :
        hermitianBlockRight
            (ι := ι) (κ := κ)
            ((r : ℂ) • g) =
          ((r : ℂ) • hermitianBlockRight (ι := ι) (κ := κ) g) := by
      ext j
      simp [hermitianBlockRight]
    have hnorm_smul :
        ‖((r : ℂ) • hermitianBlockRight (ι := ι) (κ := κ) g)‖ =
          r * ‖hermitianBlockRight (ι := ι) (κ := κ) g‖ := by
      rw [norm_smul]
      simp [Real.norm_eq_abs, abs_of_pos hr]
    have hcoefR :
        (r * ‖hermitianBlockRight (ι := ι) (κ := κ) g‖)⁻¹ * r =
          (‖hermitianBlockRight (ι := ι) (κ := κ) g‖)⁻¹ := by
      field_simp [hr_ne, hR_norm_ne]
    have hcoef :
        ((((r * ‖hermitianBlockRight (ι := ι) (κ := κ) g‖ : ℝ) : ℂ)⁻¹) *
            (r : ℂ)) =
          ((‖hermitianBlockRight (ι := ι) (κ := κ) g‖)⁻¹ : ℂ) := by
      exact_mod_cast hcoefR
    unfold hermitianBlockRightDirection
    rw [hright_smul, hnorm_smul, smul_smul, hcoef]

set_option linter.unusedSectionVars false in
/-- Global normalization of the ambient block vector does not change the
internal direction of the left block. -/
theorem hermitianBlockLeftDirection_normalized_eq_gaussianBlockLeftDirection
    (g : EuclideanSpace ℂ (Sum ι κ)) :
    hermitianBlockLeftDirection
        (ι := ι) (κ := κ)
        ((((‖g‖)⁻¹ : ℝ) : ℂ) • g) =
      gaussianBlockLeftDirection (ι := ι) (κ := κ) g := by
  by_cases hg : g = 0
  · subst hg
    simp [hermitianBlockLeftDirection, gaussianBlockLeftDirection, hermitianBlockLeft]
  · have hpos : 0 < (‖g‖)⁻¹ := by
      exact inv_pos.mpr (norm_pos_iff.mpr hg)
    rw [gaussianBlockLeftDirection_eq_hermitianBlockLeftDirection]
    exact hermitianBlockLeftDirection_real_smul
      (ι := ι) (κ := κ) hpos g

set_option linter.unusedSectionVars false in
/-- Global normalization of the ambient block vector does not change the
internal direction of the right block. -/
theorem hermitianBlockRightDirection_normalized_eq_gaussianBlockRightDirection
    (g : EuclideanSpace ℂ (Sum ι κ)) :
    hermitianBlockRightDirection
        (ι := ι) (κ := κ)
        ((((‖g‖)⁻¹ : ℝ) : ℂ) • g) =
      gaussianBlockRightDirection (ι := ι) (κ := κ) g := by
  by_cases hg : g = 0
  · subst hg
    simp [hermitianBlockRightDirection, gaussianBlockRightDirection, hermitianBlockRight]
  · have hpos : 0 < (‖g‖)⁻¹ := by
      exact inv_pos.mpr (norm_pos_iff.mpr hg)
    rw [gaussianBlockRightDirection_eq_hermitianBlockRightDirection]
    exact hermitianBlockRightDirection_real_smul
      (ι := ι) (κ := κ) hpos g

set_option linter.unusedSectionVars false in
/-- Almost-everywhere version of the left-block normalization invariance under
the standard complex Gaussian law on `ℂ^(ι ⊕ κ)`. -/
theorem hermitianBlockLeftDirection_normalized_ae_eq_gaussianBlockLeftDirection :
    (fun g : EuclideanSpace ℂ (Sum ι κ) =>
      hermitianBlockLeftDirection
        (ι := ι) (κ := κ)
        ((((‖g‖)⁻¹ : ℝ) : ℂ) • g)) =ᵐ[
          PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
            (Sum ι κ)]
      gaussianBlockLeftDirection (ι := ι) (κ := κ) := by
  exact Filter.Eventually.of_forall
    (fun g =>
      hermitianBlockLeftDirection_normalized_eq_gaussianBlockLeftDirection
        (ι := ι) (κ := κ) g)

set_option linter.unusedSectionVars false in
/-- Almost-everywhere version of the right-block normalization invariance under
the standard complex Gaussian law on `ℂ^(ι ⊕ κ)`. -/
theorem hermitianBlockRightDirection_normalized_ae_eq_gaussianBlockRightDirection :
    (fun g : EuclideanSpace ℂ (Sum ι κ) =>
      hermitianBlockRightDirection
        (ι := ι) (κ := κ)
        ((((‖g‖)⁻¹ : ℝ) : ℂ) • g)) =ᵐ[
          PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
            (Sum ι κ)]
      gaussianBlockRightDirection (ι := ι) (κ := κ) := by
  exact Filter.Eventually.of_forall
    (fun g =>
      hermitianBlockRightDirection_normalized_eq_gaussianBlockRightDirection
        (ι := ι) (κ := κ) g)

/-! ### Block rectangular cones for the Hermitian decomposition -/

/-- The block-rectangular event on the unit sphere of `ℂ^ι ⊕ ℂ^κ`.

For measurable sets `massSet`, `leftSet`, and `rightSet`, this is the sphere
event

`‖x_E‖² ∈ massSet`, `x_E / ‖x_E‖ ∈ leftSet`,
`x_F / ‖x_F‖ ∈ rightSet`. -/
noncomputable def hermitianBlockRectSphereSet
    (massSet : Set ℝ)
    (leftSet : Set (EuclideanSpace ℂ ι))
    (rightSet : Set (EuclideanSpace ℂ κ)) :
    Set (Metric.sphere (0 : EuclideanSpace ℂ (Sum ι κ)) 1) :=
  {x |
    hermitianBlockMass (ι := ι) (κ := κ)
        (x : EuclideanSpace ℂ (Sum ι κ)) ∈ massSet ∧
      hermitianBlockLeftDirection (ι := ι) (κ := κ)
          (x : EuclideanSpace ℂ (Sum ι κ)) ∈ leftSet ∧
        hermitianBlockRightDirection (ι := ι) (κ := κ)
            (x : EuclideanSpace ℂ (Sum ι κ)) ∈ rightSet}

/-- The radial cone in the ambient block space corresponding to a
block-rectangular event on the unit sphere.

This is the exact set appearing in `Measure.toSphere_apply'`. -/
noncomputable def hermitianBlockRectCone
    (massSet : Set ℝ)
    (leftSet : Set (EuclideanSpace ℂ ι))
    (rightSet : Set (EuclideanSpace ℂ κ)) :
    Set (EuclideanSpace ℂ (Sum ι κ)) :=
  Set.Ioo (0 : ℝ) 1 •
    ((Subtype.val : Metric.sphere (0 : EuclideanSpace ℂ (Sum ι κ)) 1 →
      EuclideanSpace ℂ (Sum ι κ)) ''
        hermitianBlockRectSphereSet
          (ι := ι) (κ := κ) massSet leftSet rightSet)

theorem measurableSet_hermitianBlockRectSphereSet
    {massSet : Set ℝ}
    {leftSet : Set (EuclideanSpace ℂ ι)}
    {rightSet : Set (EuclideanSpace ℂ κ)}
    (hmass : MeasurableSet massSet)
    (hleft : MeasurableSet leftSet)
    (hright : MeasurableSet rightSet) :
    MeasurableSet
      (hermitianBlockRectSphereSet
        (ι := ι) (κ := κ) massSet leftSet rightSet) := by
  have hmass_meas :
      Measurable
        (fun x : Metric.sphere (0 : EuclideanSpace ℂ (Sum ι κ)) 1 =>
          hermitianBlockMass (ι := ι) (κ := κ)
            (x : EuclideanSpace ℂ (Sum ι κ))) :=
    (measurable_hermitianBlockMass (ι := ι) (κ := κ)).comp
      measurable_subtype_coe
  have hleft_meas :
      Measurable
        (fun x : Metric.sphere (0 : EuclideanSpace ℂ (Sum ι κ)) 1 =>
          hermitianBlockLeftDirection (ι := ι) (κ := κ)
            (x : EuclideanSpace ℂ (Sum ι κ))) :=
    (measurable_hermitianBlockLeftDirection (ι := ι) (κ := κ)).comp
      measurable_subtype_coe
  have hright_meas :
      Measurable
        (fun x : Metric.sphere (0 : EuclideanSpace ℂ (Sum ι κ)) 1 =>
          hermitianBlockRightDirection (ι := ι) (κ := κ)
            (x : EuclideanSpace ℂ (Sum ι κ))) :=
    (measurable_hermitianBlockRightDirection (ι := ι) (κ := κ)).comp
      measurable_subtype_coe
  exact (hmass_meas hmass).inter
    ((hleft_meas hleft).inter (hright_meas hright))

/-- Surface probability of a block-rectangular event as a normalized ambient
cone volume.

This is the direct Hermitian-block analogue of
`toFinite_toSphere_projectiveCapSet_eq_cone_volume_ratio`: applying
`Measure.toSphere_apply'` to the sphere event gives the cone volume, and the
same identity on `univ` cancels the ambient real dimension factor. -/
theorem toFinite_toSphere_hermitianBlockRectSphereSet_eq_cone_volume_ratio
    [Nonempty ι] [Nonempty κ]
    (μ : Measure (EuclideanSpace ℂ (Sum ι κ))) [μ.IsAddHaarMeasure]
    [SFinite μ.toSphere] [IsFiniteMeasure μ.toSphere]
    {massSet : Set ℝ}
    {leftSet : Set (EuclideanSpace ℂ ι)}
    {rightSet : Set (EuclideanSpace ℂ κ)}
    (hmass : MeasurableSet massSet)
    (hleft : MeasurableSet leftSet)
    (hright : MeasurableSet rightSet) :
    μ.toSphere.toFinite
        (hermitianBlockRectSphereSet
          (ι := ι) (κ := κ) massSet leftSet rightSet) =
      (μ (Metric.ball (0 : EuclideanSpace ℂ (Sum ι κ)) 1))⁻¹ *
        μ (hermitianBlockRectCone
          (ι := ι) (κ := κ) massSet leftSet rightSet) := by
  have hraw :
      μ.toSphere.toFinite
          (hermitianBlockRectSphereSet
            (ι := ι) (κ := κ) massSet leftSet rightSet) =
        (Module.finrank ℝ (EuclideanSpace ℂ (Sum ι κ)) *
            μ (Metric.ball (0 : EuclideanSpace ℂ (Sum ι κ)) 1))⁻¹ *
          (Module.finrank ℝ (EuclideanSpace ℂ (Sum ι κ)) *
            μ (hermitianBlockRectCone
              (ι := ι) (κ := κ) massSet leftSet rightSet)) := by
    have htoFinite :
        μ.toSphere.toFinite = ProbabilityTheory.cond μ.toSphere Set.univ := by
      unfold Measure.toFinite
      rw [Measure.toFiniteAux,
        if_pos (inferInstance : IsFiniteMeasure μ.toSphere)]
    rw [htoFinite]
    rw [ProbabilityTheory.cond_apply MeasurableSet.univ μ.toSphere]
    simp only [Set.univ_inter]
    rw [Measure.toSphere_apply' μ
      (measurableSet_hermitianBlockRectSphereSet
        (ι := ι) (κ := κ) hmass hleft hright)]
    rw [Measure.toSphere_apply_univ]
    rfl
  rw [hraw]
  have hdim_nat :
      0 < Module.finrank ℝ (EuclideanSpace ℂ (Sum ι κ)) :=
    Module.finrank_pos
  have hdim0 :
      (Module.finrank ℝ (EuclideanSpace ℂ (Sum ι κ)) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hdim_nat.ne'
  have hdimt :
      (Module.finrank ℝ (EuclideanSpace ℂ (Sum ι κ)) : ℝ≥0∞) ≠ ∞ := by
    simp
  rw [ENNReal.mul_inv]
  · calc
      ((Module.finrank ℝ (EuclideanSpace ℂ (Sum ι κ)) : ℝ≥0∞)⁻¹ *
          (μ (Metric.ball (0 : EuclideanSpace ℂ (Sum ι κ)) 1))⁻¹) *
          ((Module.finrank ℝ (EuclideanSpace ℂ (Sum ι κ)) : ℝ≥0∞) *
            μ (hermitianBlockRectCone
              (ι := ι) (κ := κ) massSet leftSet rightSet))
        =
          (μ (Metric.ball (0 : EuclideanSpace ℂ (Sum ι κ)) 1))⁻¹ *
            (((Module.finrank ℝ (EuclideanSpace ℂ (Sum ι κ)) : ℝ≥0∞)⁻¹ *
                (Module.finrank ℝ (EuclideanSpace ℂ (Sum ι κ)) : ℝ≥0∞)) *
              μ (hermitianBlockRectCone
                (ι := ι) (κ := κ) massSet leftSet rightSet)) := by
            ac_rfl
      _ =
          (μ (Metric.ball (0 : EuclideanSpace ℂ (Sum ι κ)) 1))⁻¹ *
            μ (hermitianBlockRectCone
              (ι := ι) (κ := κ) massSet leftSet rightSet) := by
            rw [ENNReal.inv_mul_cancel hdim0 hdimt, one_mul]
  · exact Or.inl hdim0
  · exact Or.inl hdimt

set_option linter.unusedSectionVars false in
/-- Canonical surface-measure version of the block cone-volume ratio. -/
theorem surfaceMeasure_hermitianBlockRectSphereSet_eq_cone_volume_ratio
    [Nonempty ι] [Nonempty κ]
    [SFinite
      ((MeasureTheory.volume :
        Measure (EuclideanSpace ℂ (Sum ι κ))).toSphere)]
    {massSet : Set ℝ}
    {leftSet : Set (EuclideanSpace ℂ ι)}
    {rightSet : Set (EuclideanSpace ℂ κ)}
    (hmass : MeasurableSet massSet)
    (hleft : MeasurableSet leftSet)
    (hright : MeasurableSet rightSet) :
    surfaceMeasure (Sum ι κ)
        (hermitianBlockRectSphereSet
          (ι := ι) (κ := κ) massSet leftSet rightSet) =
      ((MeasureTheory.volume :
        Measure (EuclideanSpace ℂ (Sum ι κ)))
          (Metric.ball (0 : EuclideanSpace ℂ (Sum ι κ)) 1))⁻¹ *
        (MeasureTheory.volume :
          Measure (EuclideanSpace ℂ (Sum ι κ)))
          (hermitianBlockRectCone
            (ι := ι) (κ := κ) massSet leftSet rightSet) := by
  exact
    toFinite_toSphere_hermitianBlockRectSphereSet_eq_cone_volume_ratio
      (ι := ι) (κ := κ)
      (μ := (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ))))
      hmass hleft hright

/-! ### Separated polar coordinates on the two Hermitian blocks -/

/-- The canonical product-coordinate equivalence
`ℂ^(ι ⊕ κ) ≃ ℂ^ι × ℂ^κ` used to split a block vector into its left and
right components. -/
noncomputable abbrev hermitianBlockSumEquivProd :
    EuclideanSpace ℂ (Sum ι κ) ≃L[ℂ]
      EuclideanSpace ℂ ι × EuclideanSpace ℂ κ :=
  EuclideanSpace.sumEquivProd (𝕜 := ℂ)

theorem hermitianBlockSumEquivProd_fst
    (x : EuclideanSpace ℂ (Sum ι κ)) :
    (hermitianBlockSumEquivProd (ι := ι) (κ := κ) x).1 =
      hermitianBlockLeft (ι := ι) (κ := κ) x := by
  ext i
  rfl

theorem hermitianBlockSumEquivProd_snd
    (x : EuclideanSpace ℂ (Sum ι κ)) :
    (hermitianBlockSumEquivProd (ι := ι) (κ := κ) x).2 =
      hermitianBlockRight (ι := ι) (κ := κ) x := by
  ext j
  rfl

theorem hermitianBlockLeft_sumEquivProd_symm
    (x : EuclideanSpace ℂ ι × EuclideanSpace ℂ κ) :
    hermitianBlockLeft (ι := ι) (κ := κ)
        ((hermitianBlockSumEquivProd (ι := ι) (κ := κ)).symm x) =
      x.1 := by
  have h :=
    hermitianBlockSumEquivProd_fst
      (ι := ι) (κ := κ)
      ((hermitianBlockSumEquivProd (ι := ι) (κ := κ)).symm x)
  simpa using h.symm

theorem hermitianBlockRight_sumEquivProd_symm
    (x : EuclideanSpace ℂ ι × EuclideanSpace ℂ κ) :
    hermitianBlockRight (ι := ι) (κ := κ)
        ((hermitianBlockSumEquivProd (ι := ι) (κ := κ)).symm x) =
      x.2 := by
  have h :=
    hermitianBlockSumEquivProd_snd
      (ι := ι) (κ := κ)
      ((hermitianBlockSumEquivProd (ι := ι) (κ := κ)).symm x)
  simpa using h.symm

theorem measurePreserving_hermitianBlockSumEquivProd :
    MeasurePreserving
      (hermitianBlockSumEquivProd (ι := ι) (κ := κ))
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ)))
      (MeasureTheory.volume :
        Measure (EuclideanSpace ℂ ι × EuclideanSpace ℂ κ)) := by
  unfold hermitianBlockSumEquivProd
  unfold EuclideanSpace.sumEquivProd
  let U : EuclideanSpace ℂ (Sum ι κ) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℂ ι × EuclideanSpace ℂ κ) :=
    IsometryEquiv.toRealLinearIsometryEquivOfMapZero
      ((PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℂ) 2
        (fun _ : Sum ι κ => ℂ)).toIsometryEquiv)
      (by simp)
  have h₁ :
      MeasurePreserving
        ((PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℂ) 2
          (fun _ : Sum ι κ => ℂ)) :
          EuclideanSpace ℂ (Sum ι κ) →
            WithLp 2 (EuclideanSpace ℂ ι × EuclideanSpace ℂ κ))
        (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ)))
        (MeasureTheory.volume :
          Measure (WithLp 2 (EuclideanSpace ℂ ι × EuclideanSpace ℂ κ))) :=
    LinearIsometryEquiv.measurePreserving U
  have h₂ :
      MeasurePreserving
        (WithLp.prodContinuousLinearEquiv 2 ℂ
          (EuclideanSpace ℂ ι) (EuclideanSpace ℂ κ))
        (MeasureTheory.volume :
          Measure (WithLp 2 (EuclideanSpace ℂ ι × EuclideanSpace ℂ κ)))
        (MeasureTheory.volume :
          Measure (EuclideanSpace ℂ ι × EuclideanSpace ℂ κ)) := by
    simpa [WithLp.prodContinuousLinearEquiv] using
      (WithLp.volume_preserving_ofLp
        (U := EuclideanSpace ℂ ι) (V := EuclideanSpace ℂ κ))
  simpa [ContinuousLinearEquiv.trans_apply] using h₂.comp h₁

theorem volume_preimage_hermitianBlockSumEquivProd
    {s : Set (EuclideanSpace ℂ ι × EuclideanSpace ℂ κ)}
    (hs : MeasurableSet s) :
    (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ)))
      ((hermitianBlockSumEquivProd (ι := ι) (κ := κ)) ⁻¹' s) =
    (MeasureTheory.volume :
      Measure (EuclideanSpace ℂ ι × EuclideanSpace ℂ κ)) s := by
  simpa [Measure.map_apply
    (measurePreserving_hermitianBlockSumEquivProd
      (ι := ι) (κ := κ)).measurable hs] using
    congrArg
      (fun ν : Measure (EuclideanSpace ℂ ι × EuclideanSpace ℂ κ) => ν s)
      (measurePreserving_hermitianBlockSumEquivProd
        (ι := ι) (κ := κ)).map_eq

/-- Squared norm in the direct sum is the sum of the squared block norms. -/
theorem hermitianBlock_norm_sq_eq_add
    (x : EuclideanSpace ℂ (Sum ι κ)) :
    ‖x‖ ^ 2 =
      ‖hermitianBlockLeft (ι := ι) (κ := κ) x‖ ^ 2 +
        ‖hermitianBlockRight (ι := ι) (κ := κ) x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq (𝕜 := ℂ) x]
  rw [EuclideanSpace.norm_sq_eq (𝕜 := ℂ)
    (hermitianBlockLeft (ι := ι) (κ := κ) x)]
  rw [EuclideanSpace.norm_sq_eq (𝕜 := ℂ)
    (hermitianBlockRight (ι := ι) (κ := κ) x)]
  simp [hermitianBlockLeft, hermitianBlockRight]

/-- Product of the two separate polar-coordinate maps, one on `ℂ^ι` and one
on `ℂ^κ`.  This is the coordinate change

`(x_E, x_F) ↦ ((u_E, r_E), (u_F, r_F))`. -/
noncomputable def hermitianBlockSeparatePolarMap :
    ({0}ᶜ : Set (EuclideanSpace ℂ ι)) ×
        ({0}ᶜ : Set (EuclideanSpace ℂ κ)) →
      (Metric.sphere (0 : EuclideanSpace ℂ ι) 1 × Set.Ioi (0 : ℝ)) ×
        (Metric.sphere (0 : EuclideanSpace ℂ κ) 1 × Set.Ioi (0 : ℝ)) :=
  Prod.map
    (homeomorphUnitSphereProd (EuclideanSpace ℂ ι))
    (homeomorphUnitSphereProd (EuclideanSpace ℂ κ))

/-- Applying the polar-coordinate theorem separately on the two blocks gives a
product of two direction measures and two radial measures. -/
theorem measurePreserving_hermitianBlockSeparatePolarMap
    [SFinite
      ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).comap
        (Subtype.val : ({0}ᶜ : Set (EuclideanSpace ℂ ι)) →
          EuclideanSpace ℂ ι))]
    [SFinite
      ((MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)).comap
        (Subtype.val : ({0}ᶜ : Set (EuclideanSpace ℂ κ)) →
          EuclideanSpace ℂ κ))] :
    MeasurePreserving
      (hermitianBlockSeparatePolarMap (ι := ι) (κ := κ))
      (((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).comap
          (Subtype.val : ({0}ᶜ : Set (EuclideanSpace ℂ ι)) →
            EuclideanSpace ℂ ι)).prod
        ((MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)).comap
          (Subtype.val : ({0}ᶜ : Set (EuclideanSpace ℂ κ)) →
            EuclideanSpace ℂ κ)))
      (((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere.prod
          (MeasureTheory.Measure.volumeIoiPow
            (Module.finrank ℝ (EuclideanSpace ℂ ι) - 1))).prod
        ((MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)).toSphere.prod
          (MeasureTheory.Measure.volumeIoiPow
            (Module.finrank ℝ (EuclideanSpace ℂ κ) - 1)))) := by
  unfold hermitianBlockSeparatePolarMap
  refine MeasurePreserving.prod ?_ ?_
  · exact Measure.measurePreserving_homeomorphUnitSphereProd
      (μ := (MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)))
  · exact Measure.measurePreserving_homeomorphUnitSphereProd
      (μ := (MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)))

/-- The trace of an ambient block-direction set on the left unit sphere. -/
def hermitianBlockLeftSphereTrace
    (leftSet : Set (EuclideanSpace ℂ ι)) :
    Set (Metric.sphere (0 : EuclideanSpace ℂ ι) 1) :=
  {u | (u : EuclideanSpace ℂ ι) ∈ leftSet}

/-- The trace of an ambient block-direction set on the right unit sphere. -/
def hermitianBlockRightSphereTrace
    (rightSet : Set (EuclideanSpace ℂ κ)) :
    Set (Metric.sphere (0 : EuclideanSpace ℂ κ) 1) :=
  {v | (v : EuclideanSpace ℂ κ) ∈ rightSet}

/-- Total normalization map on one Hermitian block.  It returns `0` at the
origin, matching the totalized block-direction maps used in the spherical law. -/
noncomputable def hermitianBlockNormalize {η : Type*} [Fintype η]
    (x : EuclideanSpace ℂ η) : EuclideanSpace ℂ η :=
  ((‖x‖)⁻¹ : ℂ) • x

set_option linter.unusedSectionVars false in
/-- On `EuclideanSpace ℂ η`, real scalar multiplication agrees coordinatewise
with multiplication by the corresponding complex scalar.  This small bridge is
useful because Mathlib's polar homeomorphism is real-linear, whereas the
Hermitian block directions are written with complex scalars. -/
theorem euclideanSpace_real_smul_eq_complex_smul
    {η : Type*} [Fintype η]
    (r : ℝ) (x : EuclideanSpace ℂ η) :
    (r : ℝ) • x = ((r : ℂ) • x) := by
  ext i
  calc
    ((r : ℝ) • x).ofLp i = r • x.ofLp i := by
      exact PiLp.smul_apply (fun _ : η => ℂ) r x i
    _ = (r : ℂ) • x.ofLp i := by
      simp [Complex.real_smul, smul_eq_mul]
    _ = (((r : ℂ) • x).ofLp i) := by
      exact (PiLp.smul_apply (fun _ : η => ℂ) (r : ℂ) x i).symm

/-- Norm of a nonnegative real rescaling in a complex Euclidean block. -/
theorem norm_real_smul_euclideanSpace
    {η : Type*} [Fintype η]
    {r : ℝ} (hr : 0 ≤ r) (x : EuclideanSpace ℂ η) :
    ‖(r : ℝ) • x‖ = r * ‖x‖ := by
  rw [euclideanSpace_real_smul_eq_complex_smul]
  rw [norm_smul]
  simp [abs_of_nonneg hr]

/-- Normalizing a positive radial multiple of a unit vector recovers the unit
vector, with the Hermitian-block normalization convention. -/
theorem hermitianBlockNormalize_real_smul_sphere
    {η : Type*} [Fintype η]
    (u : Metric.sphere (0 : EuclideanSpace ℂ η) 1)
    (r : Set.Ioi (0 : ℝ)) :
    hermitianBlockNormalize ((r : ℝ) • (u : EuclideanSpace ℂ η)) =
      (u : EuclideanSpace ℂ η) := by
  have hu : ‖(u : EuclideanSpace ℂ η)‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using u.2
  have hnorm : ‖(r.1 : ℝ) • (u : EuclideanSpace ℂ η)‖ = r.1 := by
    rw [norm_real_smul_euclideanSpace (le_of_lt r.2), hu, mul_one]
  rw [hermitianBlockNormalize, hnorm]
  rw [euclideanSpace_real_smul_eq_complex_smul]
  rw [smul_smul]
  have hrne : ((r.1 : ℂ) ≠ 0) := by
    exact_mod_cast ne_of_gt r.2
  have hcoef : ((r.1 : ℂ)⁻¹ * (r.1 : ℂ)) = 1 := by
    exact inv_mul_cancel₀ hrne
  simp [hcoef]

/-- Hermitian-block normalization is invariant under positive real radial
rescaling. -/
theorem hermitianBlockNormalize_real_smul
    {η : Type*} [Fintype η]
    {r : ℝ} (hr : 0 < r) (x : EuclideanSpace ℂ η) :
    hermitianBlockNormalize ((r : ℝ) • x) =
      hermitianBlockNormalize x := by
  by_cases hx : x = 0
  · subst hx
    have hzero : (r : ℝ) • (0 : EuclideanSpace ℂ η) = 0 := by
      ext i
      simp
    rw [hzero]
  · have hxnorm_ne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hr_ne : r ≠ 0 := ne_of_gt hr
    have hnorm : ‖(r : ℝ) • x‖ = r * ‖x‖ :=
      norm_real_smul_euclideanSpace (η := η) (le_of_lt hr) x
    have hcoefR : (r * ‖x‖)⁻¹ * r = (‖x‖)⁻¹ := by
      field_simp [hr_ne, hxnorm_ne]
    have hcoef :
        ((((r * ‖x‖ : ℝ) : ℂ)⁻¹) * (r : ℂ)) =
          ((‖x‖)⁻¹ : ℂ) := by
      exact_mod_cast hcoefR
    rw [hermitianBlockNormalize, hermitianBlockNormalize, hnorm]
    rw [euclideanSpace_real_smul_eq_complex_smul]
    rw [smul_smul, hcoef]

/-- Squared norm of a positive radial multiple of a unit vector. -/
theorem norm_sq_real_smul_sphere
    {η : Type*} [Fintype η]
    (u : Metric.sphere (0 : EuclideanSpace ℂ η) 1)
    (r : Set.Ioi (0 : ℝ)) :
    ‖(r : ℝ) • (u : EuclideanSpace ℂ η)‖ ^ 2 = (r : ℝ) ^ 2 := by
  have hu : ‖(u : EuclideanSpace ℂ η)‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using u.2
  rw [norm_real_smul_euclideanSpace (le_of_lt r.2), hu, mul_one]

/-- The angular component of Mathlib's punctured-space polar homeomorphism is
the Hermitian-block normalization used in this file. -/
theorem homeomorphUnitSphereProd_fst_eq_hermitianBlockNormalize
    {η : Type*} [Fintype η]
    (x : ({0}ᶜ : Set (EuclideanSpace ℂ η))) :
    ((homeomorphUnitSphereProd (EuclideanSpace ℂ η) x).1 :
        EuclideanSpace ℂ η) =
      hermitianBlockNormalize (x : EuclideanSpace ℂ η) := by
  have h := homeomorphUnitSphereProd_apply_fst_coe
    (EuclideanSpace ℂ η) x
  calc
    ((homeomorphUnitSphereProd (EuclideanSpace ℂ η) x).1 :
        EuclideanSpace ℂ η)
        = (‖(x : EuclideanSpace ℂ η)‖⁻¹ : ℝ) •
            (x : EuclideanSpace ℂ η) := h
    _ = ((‖(x : EuclideanSpace ℂ η)‖⁻¹ : ℂ) •
            (x : EuclideanSpace ℂ η)) := by
          simpa [Complex.ofReal_inv] using
            euclideanSpace_real_smul_eq_complex_smul
              (η := η) (‖(x : EuclideanSpace ℂ η)‖⁻¹)
              (x : EuclideanSpace ℂ η)
    _ = hermitianBlockNormalize (x : EuclideanSpace ℂ η) := by rfl

/-- The radial component of Mathlib's punctured-space polar homeomorphism is
the Euclidean norm. -/
theorem homeomorphUnitSphereProd_snd_eq_norm
    {η : Type*} [Fintype η]
    (x : ({0}ᶜ : Set (EuclideanSpace ℂ η))) :
    ((homeomorphUnitSphereProd (EuclideanSpace ℂ η) x).2 : ℝ) =
      ‖(x : EuclideanSpace ℂ η)‖ := by
  simpa using
    (homeomorphUnitSphereProd_apply_snd_coe
      (EuclideanSpace ℂ η) x)

/-- Recomposition from the polar variables returned by
`homeomorphUnitSphereProd` recovers the original punctured vector. -/
theorem homeomorphUnitSphereProd_recompose_eq
    {η : Type*} [Fintype η]
    (x : ({0}ᶜ : Set (EuclideanSpace ℂ η))) :
    ((homeomorphUnitSphereProd (EuclideanSpace ℂ η) x).2 : ℝ) •
        ((homeomorphUnitSphereProd (EuclideanSpace ℂ η) x).1 :
          EuclideanSpace ℂ η) =
      (x : EuclideanSpace ℂ η) := by
  have hleft := homeomorphUnitSphereProd_symm_apply_coe
    (EuclideanSpace ℂ η)
    ((homeomorphUnitSphereProd (EuclideanSpace ℂ η)) x)
  have hright := congrArg Subtype.val
    ((homeomorphUnitSphereProd (EuclideanSpace ℂ η)).left_inv x)
  calc
    ((homeomorphUnitSphereProd (EuclideanSpace ℂ η) x).2 : ℝ) •
        ((homeomorphUnitSphereProd (EuclideanSpace ℂ η) x).1 :
          EuclideanSpace ℂ η)
        =
          (((homeomorphUnitSphereProd (EuclideanSpace ℂ η)).symm
              ((homeomorphUnitSphereProd (EuclideanSpace ℂ η)) x)) :
            EuclideanSpace ℂ η) := hleft.symm
    _ = (x : EuclideanSpace ℂ η) := hright

@[fun_prop]
theorem measurable_hermitianBlockNormalize
    {η : Type*} [Fintype η] :
    Measurable (hermitianBlockNormalize (η := η)) := by
  unfold hermitianBlockNormalize
  fun_prop

/-- Away from the origin, the total Hermitian-block normalization lands on the
unit sphere. -/
theorem hermitianBlockNormalize_mem_sphere_of_ne_zero
    {η : Type*} [Fintype η]
    {z : EuclideanSpace ℂ η} (hz : z ≠ 0) :
    hermitianBlockNormalize z ∈
      Metric.sphere (0 : EuclideanSpace ℂ η) 1 := by
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [Metric.mem_sphere, dist_eq_norm, hermitianBlockNormalize]
  simp only [sub_zero]
  rw [norm_smul]
  have hnorm : ‖(((‖z‖ : ℝ)⁻¹ : ℂ))‖ = (‖z‖)⁻¹ := by
    simp
  rw [hnorm]
  field_simp [hpos.ne']

/-- The standard complex Gaussian vector has no atom at the origin. -/
theorem standardComplexGaussianVectorMeasure_zero_eq_zero
    {η : Type*} [Fintype η] [Nonempty η] :
    PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure η
      ({0} : Set (EuclideanSpace ℂ η)) = 0 := by
  unfold PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
  rw [Measure.map_apply
    (PptFactorization.GaussianModel.measurable_complexVectorOfRealCoordinates η)
    (measurableSet_singleton 0)]
  have hpre :
      (PptFactorization.GaussianModel.complexVectorOfRealCoordinates
          (ι := η)) ⁻¹'
          ({0} : Set (EuclideanSpace ℂ η)) =
        ({0} : Set (PptFactorization.GaussianModel.ComplexRealCoordSpace η)) := by
    ext x
    constructor
    · intro hx
      have h0 :
          PptFactorization.GaussianModel.complexVectorOfRealCoordinates
              (ι := η) 0 = 0 := by
        ext i
        simp [PptFactorization.GaussianModel.complexVectorOfRealCoordinates,
          PptFactorization.GaussianModel.complexGaussianScale]
      have hxeq :
          PptFactorization.GaussianModel.complexVectorOfRealCoordinates
              (ι := η) x =
            PptFactorization.GaussianModel.complexVectorOfRealCoordinates
              (ι := η) 0 := by
        simpa using (Set.mem_singleton_iff.mp hx).trans h0.symm
      exact
        (PptFactorization.AppendixB.complexVectorOfRealCoordinates_injective
          (ι := η)) hxeq
    · intro hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      change
        PptFactorization.GaussianModel.complexVectorOfRealCoordinates
          (ι := η) 0 = 0
      ext i
      simp [PptFactorization.GaussianModel.complexVectorOfRealCoordinates,
        PptFactorization.GaussianModel.complexGaussianScale]
  rw [hpre]
  haveI :
      NoAtoms
        (ProbabilityTheory.stdGaussian
          (PptFactorization.GaussianModel.ComplexRealCoordSpace η)) := by
    simpa [PptFactorization.GaussianModel.ComplexRealCoordSpace] using
      (PptFactorization.AppendixB.stdGaussian_noAtoms
        (ι := η × Fin 2))
  exact
    measure_singleton
      (μ := ProbabilityTheory.stdGaussian
        (PptFactorization.GaussianModel.ComplexRealCoordSpace η))
      0

/-- Alias of `standardComplexGaussianVectorMeasure_zero_eq_zero`, stated in the
singleton-at-zero form used by pushforward arguments. -/
theorem standardComplexGaussianVectorMeasure_singleton_zero_eq_zero
    {η : Type*} [Fintype η] [Nonempty η] :
    PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure η
      ({0} : Set (EuclideanSpace ℂ η)) = 0 :=
  standardComplexGaussianVectorMeasure_zero_eq_zero (η := η)

/-- Under the ambient standard complex Gaussian law on `ℂ^(ι ⊕ κ)`, the event
`hermitianBlockLeft g = 0` has probability zero as soon as the left block is
nontrivial. -/
theorem standardComplexGaussianVectorMeasure_hermitianBlockLeft_eq_zero_eq_zero
    [Nonempty ι] :
    PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
        (Sum ι κ)
      ({g | hermitianBlockLeft (ι := ι) (κ := κ) g = 0} :
        Set (EuclideanSpace ℂ (Sum ι κ))) = 0 := by
  have hpre :
      ({g | hermitianBlockLeft (ι := ι) (κ := κ) g = 0} :
        Set (EuclideanSpace ℂ (Sum ι κ))) =
      (hermitianBlockLeft (ι := ι) (κ := κ)) ⁻¹'
        ({0} : Set (EuclideanSpace ℂ ι)) := by
    ext g
    simp
  calc
    PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
        (Sum ι κ)
        ({g | hermitianBlockLeft (ι := ι) (κ := κ) g = 0} :
          Set (EuclideanSpace ℂ (Sum ι κ))) =
      PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
        (Sum ι κ)
        ((hermitianBlockLeft (ι := ι) (κ := κ)) ⁻¹'
          ({0} : Set (EuclideanSpace ℂ ι))) := by
          rw [hpre]
    _ =
      Measure.map
          (hermitianBlockLeft (ι := ι) (κ := κ))
          (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
            (Sum ι κ))
        ({0} : Set (EuclideanSpace ℂ ι)) := by
          symm
          rw [Measure.map_apply
            (measurable_hermitianBlockLeft (ι := ι) (κ := κ))
            (measurableSet_singleton (0 : EuclideanSpace ℂ ι))]
    _ =
      PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure ι
        ({0} : Set (EuclideanSpace ℂ ι)) := by
          rw [hermitianBlockLeft_map_standardComplexGaussianVectorMeasure
            (ι := ι) (κ := κ)]
    _ = 0 := by
          exact standardComplexGaussianVectorMeasure_singleton_zero_eq_zero
            (η := ι)

/-- Under the ambient standard complex Gaussian law on `ℂ^(ι ⊕ κ)`, the event
`hermitianBlockRight g = 0` has probability zero as soon as the right block is
nontrivial. -/
theorem standardComplexGaussianVectorMeasure_hermitianBlockRight_eq_zero_eq_zero
    [Nonempty κ] :
    PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
        (Sum ι κ)
      ({g | hermitianBlockRight (ι := ι) (κ := κ) g = 0} :
        Set (EuclideanSpace ℂ (Sum ι κ))) = 0 := by
  have hpre :
      ({g | hermitianBlockRight (ι := ι) (κ := κ) g = 0} :
        Set (EuclideanSpace ℂ (Sum ι κ))) =
      (hermitianBlockRight (ι := ι) (κ := κ)) ⁻¹'
        ({0} : Set (EuclideanSpace ℂ κ)) := by
    ext g
    simp
  calc
    PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
        (Sum ι κ)
        ({g | hermitianBlockRight (ι := ι) (κ := κ) g = 0} :
          Set (EuclideanSpace ℂ (Sum ι κ))) =
      PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
        (Sum ι κ)
        ((hermitianBlockRight (ι := ι) (κ := κ)) ⁻¹'
          ({0} : Set (EuclideanSpace ℂ κ))) := by
          rw [hpre]
    _ =
      Measure.map
          (hermitianBlockRight (ι := ι) (κ := κ))
          (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
            (Sum ι κ))
        ({0} : Set (EuclideanSpace ℂ κ)) := by
          symm
          rw [Measure.map_apply
            (measurable_hermitianBlockRight (ι := ι) (κ := κ))
            (measurableSet_singleton (0 : EuclideanSpace ℂ κ))]
    _ =
      PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure κ
        ({0} : Set (EuclideanSpace ℂ κ)) := by
          rw [hermitianBlockRight_map_standardComplexGaussianVectorMeasure
            (ι := ι) (κ := κ)]
    _ = 0 := by
          exact standardComplexGaussianVectorMeasure_singleton_zero_eq_zero
            (η := κ)

/-- The total Gaussian direction is supported on the unit sphere. -/
theorem standardComplexGaussian_direction_law_sphere
    {η : Type*} [Fintype η] [Nonempty η] :
    Measure.map (hermitianBlockNormalize (η := η))
        (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure η)
      (Metric.sphere (0 : EuclideanSpace ℂ η) 1) = 1 := by
  have hcomp :
      Measure.map (hermitianBlockNormalize (η := η))
          (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure η)
        (Metric.sphere (0 : EuclideanSpace ℂ η) 1)ᶜ = 0 := by
    rw [Measure.map_apply
      (measurable_hermitianBlockNormalize (η := η))
      Metric.isClosed_sphere.measurableSet.compl]
    have hsubset :
        (hermitianBlockNormalize (η := η)) ⁻¹'
            (Metric.sphere (0 : EuclideanSpace ℂ η) 1)ᶜ ⊆
          ({0} : Set (EuclideanSpace ℂ η)) := by
      intro z hz
      by_contra hz0
      exact hz (hermitianBlockNormalize_mem_sphere_of_ne_zero
        (η := η) hz0)
    exact measure_mono_null hsubset
      (standardComplexGaussianVectorMeasure_zero_eq_zero (η := η))
  haveI :
      IsProbabilityMeasure
        (Measure.map (hermitianBlockNormalize (η := η))
          (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure η)) :=
    Measure.isProbabilityMeasure_map
      (measurable_hermitianBlockNormalize (η := η)).aemeasurable
  simpa using measure_of_measure_compl_eq_zero hcomp

/-- The Gaussian direction law viewed as a measure on the unit-sphere subtype.
The ambient theorem below is the push-forward of this measure by
`Subtype.val`. -/
noncomputable def standardComplexGaussianDirectionSubtypeMeasure
    (η : Type*) [Fintype η] :
    Measure (Metric.sphere (0 : EuclideanSpace ℂ η) 1) :=
  (Measure.map (hermitianBlockNormalize (η := η))
      (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure η)).comap
    Subtype.val

theorem standardComplexGaussianDirectionSubtypeMeasure_apply_univ
    {η : Type*} [Fintype η] [Nonempty η] :
    standardComplexGaussianDirectionSubtypeMeasure η Set.univ = 1 := by
  unfold standardComplexGaussianDirectionSubtypeMeasure
  rw [Measure.comap_apply Subtype.val Subtype.val_injective]
  · simpa [Metric.sphere] using
      standardComplexGaussian_direction_law_sphere (η := η)
  · intro s hs
    exact
      (MeasurableEmbedding.subtype_coe
        (Metric.isClosed_sphere.measurableSet :
          MeasurableSet (Metric.sphere
            (0 : EuclideanSpace ℂ η) 1))).measurableSet_image' hs
  · simp

theorem standardComplexGaussianDirectionSubtypeMeasure_isProbabilityMeasure
    {η : Type*} [Fintype η] [Nonempty η] :
    IsProbabilityMeasure (standardComplexGaussianDirectionSubtypeMeasure η) := by
  exact
    ⟨standardComplexGaussianDirectionSubtypeMeasure_apply_univ
      (η := η)⟩

theorem hermitianBlockNormalize_complexLinearIsometryEquiv
    {η : Type*} [Fintype η]
    (V : EuclideanSpace ℂ η ≃ₗᵢ[ℂ] EuclideanSpace ℂ η)
    (z : EuclideanSpace ℂ η) :
    hermitianBlockNormalize (V z) =
      V (hermitianBlockNormalize z) := by
  simp [hermitianBlockNormalize, V.norm_map, map_smul]

/-- The ambient Gaussian direction law is invariant under coordinate unitary
actions. -/
theorem standardComplexGaussian_direction_measure_map_matrixUnitary
    {η : Type*} [Fintype η] [DecidableEq η]
    (U : Matrix.unitaryGroup η ℂ) :
    Measure.map (matrixUnitaryLinearIsometryEquiv U)
        (Measure.map (hermitianBlockNormalize (η := η))
          (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure η)) =
      Measure.map (hermitianBlockNormalize (η := η))
        (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure η) := by
  let V : EuclideanSpace ℂ η ≃ₗᵢ[ℂ] EuclideanSpace ℂ η :=
    matrixUnitaryLinearIsometryEquiv U
  calc
    Measure.map V
        (Measure.map (hermitianBlockNormalize (η := η))
          (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure η)) =
      Measure.map (V ∘ hermitianBlockNormalize (η := η))
        (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure η) := by
        simpa [Function.comp, V] using
          (Measure.map_map
            (μ := PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure η)
            (f := hermitianBlockNormalize (η := η))
            (g := V)
            V.continuous.measurable
            (measurable_hermitianBlockNormalize (η := η)))
    _ = Measure.map ((hermitianBlockNormalize (η := η)) ∘ V)
        (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure η) := by
        congr 1
        funext z
        exact
          (hermitianBlockNormalize_complexLinearIsometryEquiv
            (η := η) V z).symm
    _ = Measure.map (hermitianBlockNormalize (η := η))
        (Measure.map V
          (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure η)) := by
        symm
        simpa [Function.comp] using
          (Measure.map_map
            (μ := PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure η)
            (f := V)
            (g := hermitianBlockNormalize (η := η))
            (measurable_hermitianBlockNormalize (η := η))
            V.continuous.measurable)
    _ = Measure.map (hermitianBlockNormalize (η := η))
        (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure η) := by
        rw [standardComplexGaussianVectorMeasure_map_matrixUnitary
          (ι := η) U]

theorem standardComplexGaussianDirectionSubtypeMeasure_map_val
    {η : Type*} [Fintype η] [Nonempty η] :
    Measure.map Subtype.val
        (standardComplexGaussianDirectionSubtypeMeasure η) =
      Measure.map (hermitianBlockNormalize (η := η))
        (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure η) := by
  let hsphere :
      MeasurableSet (Metric.sphere (0 : EuclideanSpace ℂ η) 1) :=
    Metric.isClosed_sphere.measurableSet
  unfold standardComplexGaussianDirectionSubtypeMeasure
  rw [map_comap_subtype_coe hsphere]
  haveI :
      IsProbabilityMeasure
        (Measure.map (hermitianBlockNormalize (η := η))
          (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure η)) :=
    Measure.isProbabilityMeasure_map
      (measurable_hermitianBlockNormalize (η := η)).aemeasurable
  have hmem :
      Metric.sphere (0 : EuclideanSpace ℂ η) 1 ∈
        ae (Measure.map (hermitianBlockNormalize (η := η))
          (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure η)) := by
    exact (mem_ae_iff_prob_eq_one hsphere).2
      (standardComplexGaussian_direction_law_sphere (η := η))
  exact Measure.restrict_eq_self_of_ae_mem hmem

/-- The Gaussian direction law on the sphere subtype is invariant under the
unitary action. -/
theorem standardComplexGaussianDirectionSubtypeMeasure_map_matrixUnitary
    {η : Type*} [Fintype η] [DecidableEq η] [Nonempty η]
    (U : Matrix.unitaryGroup η ℂ) :
    Measure.map
        (fun u : Metric.sphere (0 : EuclideanSpace ℂ η) 1 => U • u)
        (standardComplexGaussianDirectionSubtypeMeasure η) =
      standardComplexGaussianDirectionSubtypeMeasure η := by
  let hsphere :
      MeasurableSet (Metric.sphere (0 : EuclideanSpace ℂ η) 1) :=
    Metric.isClosed_sphere.measurableSet
  apply (MeasurableEmbedding.subtype_coe hsphere).map_injective
  let V : EuclideanSpace ℂ η ≃ₗᵢ[ℂ] EuclideanSpace ℂ η :=
    matrixUnitaryLinearIsometryEquiv U
  calc
    Measure.map Subtype.val
        (Measure.map
          (fun u : Metric.sphere (0 : EuclideanSpace ℂ η) 1 => U • u)
          (standardComplexGaussianDirectionSubtypeMeasure η)) =
      Measure.map
        (Subtype.val ∘
          fun u : Metric.sphere (0 : EuclideanSpace ℂ η) 1 => U • u)
        (standardComplexGaussianDirectionSubtypeMeasure η) := by
        simpa [Function.comp] using
          (Measure.map_map
            (μ := standardComplexGaussianDirectionSubtypeMeasure η)
            (f := fun u : Metric.sphere (0 : EuclideanSpace ℂ η) 1 => U • u)
            (g := Subtype.val)
            continuous_subtype_val.measurable
            (continuous_const_smul U).measurable)
    _ = Measure.map (V ∘ Subtype.val)
        (standardComplexGaussianDirectionSubtypeMeasure η) := by
        rfl
    _ = Measure.map V
        (Measure.map Subtype.val
          (standardComplexGaussianDirectionSubtypeMeasure η)) := by
        symm
        simpa [Function.comp] using
          (Measure.map_map
            (μ := standardComplexGaussianDirectionSubtypeMeasure η)
            (f := Subtype.val)
            (g := V)
            V.continuous.measurable
            continuous_subtype_val.measurable)
    _ = Measure.map V
        (Measure.map (hermitianBlockNormalize (η := η))
          (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure η)) := by
        rw [standardComplexGaussianDirectionSubtypeMeasure_map_val
          (η := η)]
    _ = Measure.map (hermitianBlockNormalize (η := η))
        (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure η) := by
        exact
          standardComplexGaussian_direction_measure_map_matrixUnitary
            (η := η) U
    _ = Measure.map Subtype.val
        (standardComplexGaussianDirectionSubtypeMeasure η) := by
        rw [standardComplexGaussianDirectionSubtypeMeasure_map_val
          (η := η)]

/-- The subtype Gaussian direction law is the canonical surface measure on the
complex unit sphere. -/
theorem standardComplexGaussianDirectionSubtypeMeasure_eq_surfaceMeasure
    {η : Type*} [Fintype η] [Nonempty η]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ η)).toSphere)] :
    standardComplexGaussianDirectionSubtypeMeasure η =
      surfaceMeasure η := by
  classical
  letI :
      IsProbabilityMeasure
        (standardComplexGaussianDirectionSubtypeMeasure η) :=
    standardComplexGaussianDirectionSubtypeMeasure_isProbabilityMeasure
      (η := η)
  letI : IsProbabilityMeasure (surfaceMeasure η) :=
    surfaceMeasure_isProbabilityMeasure η
  exact invariant_probabilityMeasure_eq_of_compact_pretransitive
    (G := Matrix.unitaryGroup η ℂ)
    (X := Metric.sphere (0 : EuclideanSpace ℂ η) 1)
    (μ := standardComplexGaussianDirectionSubtypeMeasure η)
    (σ := surfaceMeasure η)
    (fun U => ⟨(continuous_const_smul U).measurable,
      standardComplexGaussianDirectionSubtypeMeasure_map_matrixUnitary
        (η := η) U⟩)
    (fun U => ⟨(continuous_const_smul U).measurable,
      surfaceMeasure_map_matrixUnitary (ι := η) U⟩)

/-- Spherical law of the direction of a standard complex Gaussian vector:
`Z / ‖Z‖` is uniform on the complex unit sphere. -/
theorem standardComplexGaussian_direction_hasLaw_surfaceMeasureAmbient
    {η : Type*} [Fintype η] [Nonempty η]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ η)).toSphere)] :
    Measure.map
        (fun z : EuclideanSpace ℂ η => ((‖z‖)⁻¹ : ℂ) • z)
        (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure η) =
      surfaceMeasureAmbient η := by
  calc
    Measure.map
        (fun z : EuclideanSpace ℂ η => ((‖z‖)⁻¹ : ℂ) • z)
        (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure η) =
      Measure.map (hermitianBlockNormalize (η := η))
        (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure η) := by
        rfl
    _ = Measure.map Subtype.val
        (standardComplexGaussianDirectionSubtypeMeasure η) := by
        rw [standardComplexGaussianDirectionSubtypeMeasure_map_val
          (η := η)]
    _ = Measure.map Subtype.val (surfaceMeasure η) := by
        rw [standardComplexGaussianDirectionSubtypeMeasure_eq_surfaceMeasure
          (η := η)]
    _ = surfaceMeasureAmbient η := by
        rfl

/-- Local uniqueness principle for real laws from equality of MGFs on the
left-neighbourhood `(-∞,1)`.  The proof promotes the equality to the complex
MGF on the half-plane `Re z < 1`, then reads off the characteristic function
on the imaginary axis. -/
lemma map_eq_of_mgf_eq_on_Iio_one
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {μ' : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {X : Ω → ℝ} {Y : Ω' → ℝ}
    (hXmeas : AEMeasurable X μ) (hYmeas : AEMeasurable Y μ')
    (hXint :
      ∀ ⦃t : ℝ⦄, t < 1 →
        Integrable (fun ω => Real.exp (t * X ω)) μ)
    (hYint :
      ∀ ⦃t : ℝ⦄, t < 1 →
        Integrable (fun ω => Real.exp (t * Y ω)) μ')
    (hmgf :
      ∀ ⦃t : ℝ⦄, t < 1 →
        ProbabilityTheory.mgf X μ t = ProbabilityTheory.mgf Y μ' t) :
    Measure.map X μ = Measure.map Y μ' := by
  let S : Set ℂ := {z : ℂ | z.re < 1}
  have hSpre : IsPreconnected S := by
    simpa [S] using
      (convex_halfSpace_re_lt (r := (1 : ℝ))).isPreconnected
  have hS0 : (0 : ℂ) ∈ S := by
    simp [S]
  have hSX :
      S ⊆
        {z : ℂ |
          z.re ∈ interior (ProbabilityTheory.integrableExpSet X μ)} := by
    intro z hz
    have hsub :
        Set.Iio (1 : ℝ) ⊆
          ProbabilityTheory.integrableExpSet X μ := by
      intro r hr
      exact hXint hr
    exact interior_maximal hsub isOpen_Iio hz
  have hSY :
      S ⊆
        {z : ℂ |
          z.re ∈ interior (ProbabilityTheory.integrableExpSet Y μ')} := by
    intro z hz
    have hsub :
        Set.Iio (1 : ℝ) ⊆
          ProbabilityTheory.integrableExpSet Y μ' := by
      intro r hr
      exact hYint hr
    exact interior_maximal hsub isOpen_Iio hz
  have hAX : AnalyticOnNhd ℂ (ProbabilityTheory.complexMGF X μ) S := by
    exact ProbabilityTheory.analyticOnNhd_complexMGF.mono hSX
  have hAY : AnalyticOnNhd ℂ (ProbabilityTheory.complexMGF Y μ') S := by
    exact ProbabilityTheory.analyticOnNhd_complexMGF.mono hSY
  have hreal :
      ∃ᶠ x : ℝ in 𝓝[≠] (0 : ℝ),
        ProbabilityTheory.complexMGF X μ x =
          ProbabilityTheory.complexMGF Y μ' x := by
    refine
      (show ∀ᶠ x : ℝ in 𝓝[≠] (0 : ℝ),
        ProbabilityTheory.complexMGF X μ x =
          ProbabilityTheory.complexMGF Y μ' x from ?_).frequently
    have hlt : ∀ᶠ x : ℝ in 𝓝[≠] (0 : ℝ), x < 1 := by
      exact
        nhdsWithin_le_nhds
          ((isOpen_Iio : IsOpen (Set.Iio (1 : ℝ))).mem_nhds
            (by norm_num : (0 : ℝ) ∈ Set.Iio (1 : ℝ)))
    filter_upwards [hlt] with x hx
    rw [ProbabilityTheory.complexMGF_ofReal,
      ProbabilityTheory.complexMGF_ofReal]
    exact_mod_cast hmgf hx
  have hcomplexFreq :
      ∃ᶠ z : ℂ in 𝓝[≠] (0 : ℂ),
        ProbabilityTheory.complexMGF X μ z =
          ProbabilityTheory.complexMGF Y μ' z := by
    rw [frequently_iff_seq_forall] at hreal ⊢
    obtain ⟨xs, hx_tendsto, hx_eq⟩ := hreal
    refine ⟨fun n => (xs n : ℂ), ?_, fun n => ?_⟩
    · rw [tendsto_nhdsWithin_iff] at hx_tendsto ⊢
      constructor
      · exact
          (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp
            hx_tendsto.1
      · simpa using hx_tendsto.2
    · exact hx_eq n
  have hEqOn :
      Set.EqOn (ProbabilityTheory.complexMGF X μ)
        (ProbabilityTheory.complexMGF Y μ') S :=
    hAX.eqOn_of_preconnected_of_frequently_eq hAY hSpre hS0
      hcomplexFreq
  apply Measure.ext_of_charFun (E := ℝ)
  ext u
  rw [← ProbabilityTheory.complexMGF_mul_I hXmeas u]
  rw [← ProbabilityTheory.complexMGF_mul_I hYmeas u]
  exact hEqOn (x := (u : ℂ) * Complex.I) (by simp [S])

/-- The unit-rate Gamma MGF on its subcritical range. -/
lemma gammaMeasure_mgf_id_eq_rpow_neg_of_lt_one
    {a t : ℝ} (ha : 0 < a) (ht : t < 1) :
    ProbabilityTheory.mgf id (ProbabilityTheory.gammaMeasure a 1) t =
      (1 - t) ^ (-a) := by
  rw [ProbabilityTheory.mgf, ProbabilityTheory.gammaMeasure]
  have hmeas : Measurable (ProbabilityTheory.gammaPDF a 1) := by
    unfold ProbabilityTheory.gammaPDF
    exact (ProbabilityTheory.measurable_gammaPDFReal a 1).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hmeas]
  swap
  · exact ae_of_all _ (by intro x; simp [ProbabilityTheory.gammaPDF])
  simp only [id_eq, smul_eq_mul]
  have htoReal (x : ℝ) :
      (ProbabilityTheory.gammaPDF a 1 x).toReal =
        ProbabilityTheory.gammaPDFReal a 1 x := by
    rw [ProbabilityTheory.gammaPDF]
    exact ENNReal.toReal_ofReal
      (ProbabilityTheory.gammaPDFReal_nonneg ha zero_lt_one x)
  simp_rw [htoReal]
  have hsupport :
      (∫ x in Set.Ici (0 : ℝ),
        ProbabilityTheory.gammaPDFReal a 1 x *
          Real.exp (t * x) ∂volume) =
        ∫ x,
          ProbabilityTheory.gammaPDFReal a 1 x *
            Real.exp (t * x) ∂volume := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hxneg : x < 0 := by
      simpa [Set.mem_Ici] using hx
    simp [ProbabilityTheory.gammaPDFReal, hxneg.not_ge]
  rw [← hsupport]
  rw [integral_Ici_eq_integral_Ioi]
  have hcongr :
      ∫ x in Set.Ioi (0 : ℝ),
          ProbabilityTheory.gammaPDFReal a 1 x *
            Real.exp (t * x) ∂volume =
        ∫ x in Set.Ioi (0 : ℝ),
          (1 / Real.Gamma a) *
            (x ^ (a - 1) * Real.exp (-((1 - t) * x))) ∂volume := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hxpos : 0 < x := by
      simpa using hx
    dsimp
    unfold ProbabilityTheory.gammaPDFReal
    rw [if_pos hxpos.le]
    rw [Real.one_rpow]
    rw [div_eq_mul_inv, one_mul]
    ring_nf
    have hExp :
        Real.exp (-x) * Real.exp (x * t) =
          Real.exp (-x + x * t) := by
      rw [← Real.exp_add]
    rw [← hExp]
    ring
  rw [hcongr]
  rw [integral_const_mul]
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi ha
    (by linarith : 0 < 1 - t)]
  have hGamma_ne : Real.Gamma a ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos ha)
  field_simp [hGamma_ne]
  have hbase : 1 / (1 - t) = (1 - t)⁻¹ := by
    ring
  rw [hbase]
  rw [Real.inv_rpow (le_of_lt (by linarith : 0 < 1 - t))]
  rw [← Real.rpow_neg (le_of_lt (by linarith : 0 < 1 - t))]

/-- Exponential integrability of the unit-rate Gamma law on the same
subcritical range used by its MGF. -/
lemma gammaMeasure_integrable_exp_id_of_lt_one
    {a t : ℝ} (ha : 0 < a) (ht : t < 1) :
    Integrable (fun x : ℝ => Real.exp (t * x))
      (ProbabilityTheory.gammaMeasure a 1) := by
  rw [ProbabilityTheory.gammaMeasure]
  have hmeas : Measurable (ProbabilityTheory.gammaPDF a 1) := by
    unfold ProbabilityTheory.gammaPDF
    exact (ProbabilityTheory.measurable_gammaPDFReal a 1).ennreal_ofReal
  rw [integrable_withDensity_iff hmeas]
  swap
  · exact ae_of_all _ (by intro x; simp [ProbabilityTheory.gammaPDF])
  change
    Integrable
      (fun x : ℝ =>
        Real.exp (t * x) * (ProbabilityTheory.gammaPDF a 1 x).toReal)
      volume
  have htoReal (x : ℝ) :
      (ProbabilityTheory.gammaPDF a 1 x).toReal =
        ProbabilityTheory.gammaPDFReal a 1 x := by
    rw [ProbabilityTheory.gammaPDF]
    exact ENNReal.toReal_ofReal
      (ProbabilityTheory.gammaPDFReal_nonneg ha zero_lt_one x)
  simp_rw [htoReal]
  let f : ℝ → ℝ := fun x =>
    (1 / Real.Gamma a) *
      (x ^ (a - 1) * Real.exp (-((1 - t) * x)))
  have hfIoi : IntegrableOn f (Set.Ioi (0 : ℝ)) volume := by
    have hbase :
        IntegrableOn
          (fun x : ℝ =>
            x ^ (a - 1) * Real.exp (-(1 - t) * x ^ (1 : ℝ)))
          (Set.Ioi (0 : ℝ)) volume := by
      exact integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := 1) (s := a - 1) (b := 1 - t)
        (by linarith) (by norm_num) (by linarith)
    have hcongr :
        (fun x : ℝ =>
          x ^ (a - 1) * Real.exp (-(1 - t) * x ^ (1 : ℝ))) =ᵐ[
            volume.restrict (Set.Ioi (0 : ℝ))]
          (fun x : ℝ =>
            x ^ (a - 1) * Real.exp (-((1 - t) * x))) := by
      refine (ae_restrict_iff' measurableSet_Ioi).2 ?_
      exact ae_of_all _ fun x hx => by
        simp only [Real.rpow_one]
        congr 1
        ring_nf
    exact (hbase.congr hcongr).const_mul _
  have htargetIoi :
      IntegrableOn
        (fun x : ℝ =>
          Real.exp (t * x) * ProbabilityTheory.gammaPDFReal a 1 x)
        (Set.Ioi (0 : ℝ)) volume := by
    refine hfIoi.congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hxpos : 0 < x := by
      simpa using hx
    dsimp [f]
    unfold ProbabilityTheory.gammaPDFReal
    rw [if_pos hxpos.le]
    rw [Real.one_rpow]
    rw [div_eq_mul_inv, one_mul]
    have hExp :
        Real.exp (-((1 - t) * x)) =
          Real.exp (t * x) * Real.exp (-(1 * x)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hExp]
    ring_nf
  apply htargetIoi.integrable_of_ae_notMem_eq_zero
  have hzero_ae : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [hzero_ae] with x hx0 hxnot
  have hxle : x ≤ 0 := by
    simpa [Set.mem_Ioi] using hxnot
  have hxlt : x < 0 := lt_of_le_of_ne hxle hx0
  simp [ProbabilityTheory.gammaPDFReal, hxlt.not_ge]

/-- Exponential integrability of the squared norm of a standard complex
Gaussian vector, in the subcritical range. -/
lemma standardComplexGaussian_normSq_integrable_exp_of_lt_one
    {η : Type*} [Fintype η] {t : ℝ} (ht : t < 1) :
    Integrable
      (fun z : EuclideanSpace ℂ η => Real.exp (t * ‖z‖ ^ 2))
      (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
        η) := by
  have hcenter :=
    standardComplexGaussianVectorMeasure_norm_sq_centered_integrable_exp_mul
      (ι := η) (θ := t) ht
  have hcongr :
      (fun z : EuclideanSpace ℂ η => Real.exp (t * ‖z‖ ^ 2)) =
        fun z : EuclideanSpace ℂ η =>
          Real.exp (t * (Fintype.card η : ℝ)) *
            Real.exp (t * (‖z‖ ^ 2 - Fintype.card η)) := by
    funext z
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hcongr]
  exact hcenter.const_mul _

/-- The MGF of `‖Z‖²` for a standard complex Gaussian vector on `ℂ^η`. -/
lemma standardComplexGaussian_normSq_mgf_eq_gamma_mgf
    {η : Type*} [Fintype η] {t : ℝ} (ht : t < 1) :
    ProbabilityTheory.mgf
        (fun z : EuclideanSpace ℂ η => ‖z‖ ^ 2)
        (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
          η) t =
      (1 - t) ^ (-(Fintype.card η : ℝ)) := by
  rw [ProbabilityTheory.mgf]
  have hcenter :=
    standardComplexGaussianVectorMeasure_norm_sq_centered_mgf_factorization
      (ι := η) (θ := t) ht
  have hfun :
      (fun z : EuclideanSpace ℂ η => Real.exp (t * ‖z‖ ^ 2)) =
        fun z : EuclideanSpace ℂ η =>
          Real.exp (t * (Fintype.card η : ℝ)) *
            Real.exp (t * (‖z‖ ^ 2 - Fintype.card η)) := by
    funext z
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hfun]
  rw [integral_const_mul]
  rw [hcenter]
  have hprod :
      (∏ _i : η, Real.exp (-t) / (1 - t)) =
        (Real.exp (-t) / (1 - t)) ^ Fintype.card η := by
    simpa using
      (Finset.prod_const (s := (Finset.univ : Finset η))
        (b := Real.exp (-t) / (1 - t)))
  rw [hprod]
  rw [div_pow]
  rw [← Real.exp_nat_mul]
  rw [div_eq_mul_inv]
  rw [← mul_assoc]
  rw [← Real.exp_add]
  have hExp :
      t * (Fintype.card η : ℝ) + ↑(Fintype.card η) * -t = 0 := by
    ring
  rw [hExp, Real.exp_zero, one_mul]
  have hpos : 0 < 1 - t := by
    linarith
  rw [← Real.rpow_natCast (1 - t) (Fintype.card η)]
  rw [← Real.rpow_neg hpos.le]

/-- The squared norm of a standard complex Gaussian vector on `ℂ^η` has the
integer-shape Gamma law `Gamma(card η, 1)`.

This is the finite-dimensional complex analogue of the chi-square law, written
in the rate-parameter convention used by `gammaMeasure`. -/
theorem stdComplexGaussian_normSq_hasLaw_gamma_nat
    {η : Type*} [Fintype η] [Nonempty η] :
    ProbabilityTheory.HasLaw
      (fun z : EuclideanSpace ℂ η => ‖z‖ ^ 2)
      (ProbabilityTheory.gammaMeasure (Fintype.card η : ℝ) 1)
      (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
        η) := by
  have hcard_pos : 0 < (Fintype.card η : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card η)
  haveI :
      IsProbabilityMeasure
        (ProbabilityTheory.gammaMeasure (Fintype.card η : ℝ) 1) :=
    ProbabilityTheory.isProbabilityMeasure_gammaMeasure hcard_pos zero_lt_one
  refine
    ⟨(by
      fun_prop :
        AEMeasurable (fun z : EuclideanSpace ℂ η => ‖z‖ ^ 2)
          (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
            η)), ?_⟩
  simpa using
    (map_eq_of_mgf_eq_on_Iio_one
      (μ := PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
        η)
      (μ' := ProbabilityTheory.gammaMeasure (Fintype.card η : ℝ) 1)
      (X := fun z : EuclideanSpace ℂ η => ‖z‖ ^ 2)
      (Y := id)
      (by fun_prop)
      (by fun_prop)
      (fun {t} ht =>
        standardComplexGaussian_normSq_integrable_exp_of_lt_one
          (η := η) ht)
      (fun {t} ht =>
        gammaMeasure_integrable_exp_id_of_lt_one hcard_pos ht)
      (fun {t} ht => by
        rw [standardComplexGaussian_normSq_mgf_eq_gamma_mgf
          (η := η) ht]
        rw [gammaMeasure_mgf_id_eq_rpow_neg_of_lt_one
          hcard_pos ht]))

/-- One complex standard Gaussian coordinate has squared norm distributed as
`Gamma(1,1) = Exp(1)`.  This is the one-dimensional specialization of the
finite-dimensional Gamma law above. -/
theorem stdComplexGaussian_normSq_hasLaw_gamma_one :
    ProbabilityTheory.HasLaw
      (fun z : EuclideanSpace ℂ Unit => ‖z‖ ^ 2)
      (ProbabilityTheory.gammaMeasure (1 : ℝ) 1)
      (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
        Unit) := by
  simpa using (stdComplexGaussian_normSq_hasLaw_gamma_nat (η := Unit))

/-- The trivial matrix-coordinate index `(Unit × Unit) × η` is just `η`. -/
def unitUnitSampleCoordEquiv (η : Type*) :
    PptFactorization.GaussianModel.SampleCoord Unit Unit η ≃ η where
  toFun a := a.2
  invFun α := (((), ()), α)
  left_inv := by
    rintro ⟨⟨⟨⟩, ⟨⟩⟩, α⟩
    rfl
  right_inv := by
    intro α
    rfl

/-- Real-coordinate version of the trivial `(Unit, Unit)` reindexing. -/
noncomputable def unitUnitSampleCoordRealIso
    (η : Type*) [Fintype η] :
    PptFactorization.GaussianModel.GaussianSampleSpace Unit Unit η ≃ₗᵢ[ℝ]
      PptFactorization.GaussianModel.ComplexRealCoordSpace η :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    ((unitUnitSampleCoordEquiv η).prodCongr (Equiv.refl (Fin 2)))

/-- Identify the one-row one-column sample matrix model with `ℂ^η`. -/
noncomputable def unitUnitSampleMatrixEuclideanIso
    (η : Type*) [Fintype η] :
    SampleMatrix Unit Unit η ≃ₗᵢ[ℂ] EuclideanSpace ℂ η :=
  (sampleMatrixComplexLinearIsometryEquiv
      (p := Unit) (q := Unit) (σ := η)).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (unitUnitSampleCoordEquiv η))

@[simp] theorem unitUnitSampleMatrixEuclideanIso_apply
    {η : Type*} [Fintype η]
    (G : SampleMatrix Unit Unit η) (α : η) :
    unitUnitSampleMatrixEuclideanIso η G α = G ((), ()) α := by
  simp [unitUnitSampleMatrixEuclideanIso, unitUnitSampleCoordEquiv,
    sampleMatrixComplexLinearIsometryEquiv]

theorem unitUnitSampleMatrixEuclideanIso_gaussianMatrix
    {η : Type*} [Fintype η]
    (ω : PptFactorization.HighProbabilityBounds.Ω Unit Unit η) :
    unitUnitSampleMatrixEuclideanIso η
        (PptFactorization.HighProbabilityBounds.gaussianMatrix Unit Unit η ω) =
      PptFactorization.GaussianModel.complexVectorOfRealCoordinates
        (ι := η) (unitUnitSampleCoordRealIso η ω) := by
  ext α
  rw [unitUnitSampleMatrixEuclideanIso_apply]
  simp [unitUnitSampleCoordRealIso, unitUnitSampleCoordEquiv,
    PptFactorization.HighProbabilityBounds.gaussianMatrix,
    PptFactorization.GaussianModel.gaussianSampleMatrix]

/-- The one-row one-column Gaussian sample matrix, transported through the
trivial coordinate isometry, has the standard complex Gaussian law on `ℂ^η`. -/
theorem unitUnitSampleMatrixEuclideanIso_gaussianMatrix_map
    (η : Type*) [Fintype η] :
    Measure.map
        (fun ω =>
          unitUnitSampleMatrixEuclideanIso η
            (PptFactorization.HighProbabilityBounds.gaussianMatrix
              Unit Unit η ω))
        (PptFactorization.HighProbabilityBounds.gaussianMeasure
          Unit Unit η) =
      PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
        η := by
  let C :
      PptFactorization.GaussianModel.ComplexRealCoordSpace η →
        EuclideanSpace ℂ η :=
    PptFactorization.GaussianModel.complexVectorOfRealCoordinates (ι := η)
  let R :
      PptFactorization.GaussianModel.GaussianSampleSpace Unit Unit η ≃ₗᵢ[ℝ]
        PptFactorization.GaussianModel.ComplexRealCoordSpace η :=
    unitUnitSampleCoordRealIso η
  have hpoint :
      (fun ω =>
          unitUnitSampleMatrixEuclideanIso η
            (PptFactorization.HighProbabilityBounds.gaussianMatrix
              Unit Unit η ω)) =
        fun ω => C (R ω) := by
    funext ω
    exact unitUnitSampleMatrixEuclideanIso_gaussianMatrix (η := η) ω
  unfold PptFactorization.HighProbabilityBounds.gaussianMeasure
    PptFactorization.GaussianModel.gaussianSampleMeasure
    PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
  calc
    Measure.map
        (fun ω =>
          unitUnitSampleMatrixEuclideanIso η
            (PptFactorization.HighProbabilityBounds.gaussianMatrix
              Unit Unit η ω))
        (ProbabilityTheory.stdGaussian
          (PptFactorization.GaussianModel.GaussianSampleSpace
            Unit Unit η)) =
      Measure.map (fun ω => C (R ω))
        (ProbabilityTheory.stdGaussian
          (PptFactorization.GaussianModel.GaussianSampleSpace
            Unit Unit η)) := by
        rw [hpoint]
    _ =
      Measure.map C
        (Measure.map R
          (ProbabilityTheory.stdGaussian
            (PptFactorization.GaussianModel.GaussianSampleSpace
              Unit Unit η))) := by
        symm
        simpa [C, R, Function.comp] using
          (Measure.map_map
            (μ := ProbabilityTheory.stdGaussian
              (PptFactorization.GaussianModel.GaussianSampleSpace
                Unit Unit η))
            (f := R)
            (g := C)
            (PptFactorization.GaussianModel.measurable_complexVectorOfRealCoordinates
              η)
            R.continuous.measurable)
    _ =
      Measure.map C
        (ProbabilityTheory.stdGaussian
          (PptFactorization.GaussianModel.ComplexRealCoordSpace η)) := by
        rw [ProbabilityTheory.stdGaussian_map R]

theorem unitUnit_gaussianRadiusSq_eq_norm_sq
    {η : Type*} [Fintype η]
    (ω : PptFactorization.HighProbabilityBounds.Ω Unit Unit η) :
    gaussianRadiusSq (p := Unit) (q := Unit) (σ := η) ω =
      ‖unitUnitSampleMatrixEuclideanIso η
        (PptFactorization.HighProbabilityBounds.gaussianMatrix
          Unit Unit η ω)‖ ^ 2 := by
  simp [gaussianRadiusSq, gaussianRadius,
    PptFactorization.RandomMatrixModel.frobeniusNorm,
    (unitUnitSampleMatrixEuclideanIso η).norm_map]

theorem unitUnit_gaussianDirection_eq_normalized
    {η : Type*} [Fintype η]
    (ω : PptFactorization.HighProbabilityBounds.Ω Unit Unit η) :
    unitUnitSampleMatrixEuclideanIso η
        (gaussianDirection (p := Unit) (q := Unit) (σ := η) ω) =
      ((‖unitUnitSampleMatrixEuclideanIso η
          (PptFactorization.HighProbabilityBounds.gaussianMatrix
            Unit Unit η ω)‖)⁻¹ : ℂ) •
        unitUnitSampleMatrixEuclideanIso η
          (PptFactorization.HighProbabilityBounds.gaussianMatrix
            Unit Unit η ω) := by
  simp [gaussianDirection, PptFactorization.RandomMatrixModel.normalizedSample,
    PptFactorization.RandomMatrixModel.frobeniusNorm,
    (unitUnitSampleMatrixEuclideanIso η).norm_map,
    map_smul]

/-- Transport independence from a parametrizing probability space to its image
law. -/
theorem indepFun_of_indepFun_comp_of_map_eq
    {Ω α β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ]
    {μΩ : Measure Ω} {μα : Measure α}
    [IsFiniteMeasure μΩ] [IsFiniteMeasure μα]
    {X : Ω → α} {f : α → β} {g : α → γ}
    (hX : Measurable X) (hf : Measurable f) (hg : Measurable g)
    (hmap : Measure.map X μΩ = μα)
    (hind :
      ProbabilityTheory.IndepFun
        (fun ω => f (X ω)) (fun ω => g (X ω)) μΩ) :
    ProbabilityTheory.IndepFun f g μα := by
  have hpairComp :
      Measure.map (fun ω => (f (X ω), g (X ω))) μΩ =
        (Measure.map (fun ω => f (X ω)) μΩ).prod
          (Measure.map (fun ω => g (X ω)) μΩ) := by
    exact
      (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
        ((hf.comp hX).aemeasurable)
        ((hg.comp hX).aemeasurable)).1 hind
  have hmapPair :
      Measure.map (fun a => (f a, g a)) μα =
        Measure.map (fun ω => (f (X ω), g (X ω))) μΩ := by
    calc
      Measure.map (fun a => (f a, g a)) μα =
        Measure.map (fun a => (f a, g a)) (Measure.map X μΩ) := by
          rw [hmap]
      _ =
        Measure.map ((fun a => (f a, g a)) ∘ X) μΩ := by
          rw [Measure.map_map]
          · exact hf.prodMk hg
          · exact hX
      _ = Measure.map (fun ω => (f (X ω), g (X ω))) μΩ := by
          rfl
  have hmapF :
      Measure.map (fun ω => f (X ω)) μΩ =
        Measure.map f μα := by
    calc
      Measure.map (fun ω => f (X ω)) μΩ =
        Measure.map (f ∘ X) μΩ := by
          rfl
      _ = Measure.map f (Measure.map X μΩ) := by
          symm
          rw [Measure.map_map]
          · exact hf
          · exact hX
      _ = Measure.map f μα := by
          rw [hmap]
  have hmapG :
      Measure.map (fun ω => g (X ω)) μΩ =
        Measure.map g μα := by
    calc
      Measure.map (fun ω => g (X ω)) μΩ =
        Measure.map (g ∘ X) μΩ := by
          rfl
      _ = Measure.map g (Measure.map X μΩ) := by
          symm
          rw [Measure.map_map]
          · exact hg
          · exact hX
      _ = Measure.map g μα := by
          rw [hmap]
  refine
    (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      hf.aemeasurable hg.aemeasurable).2 ?_
  rw [hmapPair, hpairComp, hmapF, hmapG]

/-- Radius squared and total direction are independent for a standard complex
Gaussian vector.

This transports the already-formalized polar independence theorem for
Gaussian sample matrices through the trivial `(Unit, Unit, η)` matrix model. -/
theorem standardComplexGaussian_normSq_indep_direction
    {η : Type*} [Fintype η] :
    ProbabilityTheory.IndepFun
      (fun z : EuclideanSpace ℂ η => ‖z‖ ^ 2)
      (fun z : EuclideanSpace ℂ η => ((‖z‖)⁻¹ : ℂ) • z)
      (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure η) := by
  by_cases hη : Nonempty η
  · classical
    let X :
        PptFactorization.HighProbabilityBounds.Ω Unit Unit η →
          EuclideanSpace ℂ η :=
      fun ω =>
        unitUnitSampleMatrixEuclideanIso η
          (PptFactorization.HighProbabilityBounds.gaussianMatrix
            Unit Unit η ω)
    let f : EuclideanSpace ℂ η → ℝ := fun z => ‖z‖ ^ 2
    let g : EuclideanSpace ℂ η → EuclideanSpace ℂ η :=
      fun z => ((‖z‖)⁻¹ : ℂ) • z
    haveI : Nonempty η := hη
    haveI :
        IsProbabilityMeasure
          (PptFactorization.HighProbabilityBounds.gaussianMeasure
            Unit Unit η) := by
      rw [PptFactorization.HighProbabilityBounds.gaussianMeasure_eq]
      infer_instance
    have hbase :
        ProbabilityTheory.IndepFun
          (gaussianRadiusSq (p := Unit) (q := Unit) (σ := η))
          (gaussianDirection (p := Unit) (q := Unit) (σ := η))
          (PptFactorization.HighProbabilityBounds.gaussianMeasure
            Unit Unit η) :=
      gaussianRadiusSq_indep_gaussianDirection
        (p := Unit) (q := Unit) (σ := η)
    have hdir :
        ProbabilityTheory.IndepFun
          (gaussianRadiusSq (p := Unit) (q := Unit) (σ := η))
          (fun ω =>
            unitUnitSampleMatrixEuclideanIso η
              (gaussianDirection (p := Unit) (q := Unit) (σ := η) ω))
          (PptFactorization.HighProbabilityBounds.gaussianMeasure
            Unit Unit η) := by
      simpa [Function.comp] using
        hbase.comp measurable_id
          (unitUnitSampleMatrixEuclideanIso η).continuous.measurable
    have hΩ :
        ProbabilityTheory.IndepFun
          (fun ω => f (X ω)) (fun ω => g (X ω))
          (PptFactorization.HighProbabilityBounds.gaussianMeasure
            Unit Unit η) := by
      refine hdir.congr ?_ ?_
      · exact Filter.Eventually.of_forall fun ω => by
          simpa [f, X] using
            (unitUnit_gaussianRadiusSq_eq_norm_sq (η := η) ω)
      · exact Filter.Eventually.of_forall fun ω => by
          simpa [g, X] using
            (unitUnit_gaussianDirection_eq_normalized (η := η) ω)
    have hXmeas : Measurable X := by
      dsimp [X]
      exact
        (unitUnitSampleMatrixEuclideanIso η).continuous.measurable.comp
          (measurable_gaussianMatrix
            (p := Unit) (q := Unit) (σ := η))
    have hfmeas : Measurable f := by
      dsimp [f]
      fun_prop
    have hgmeas : Measurable g := by
      dsimp [g]
      fun_prop
    have hXlaw :
        Measure.map X
            (PptFactorization.HighProbabilityBounds.gaussianMeasure
              Unit Unit η) =
          PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
            η := by
      simpa [X] using unitUnitSampleMatrixEuclideanIso_gaussianMatrix_map η
    simpa [f, g] using
      indepFun_of_indepFun_comp_of_map_eq
        (μΩ := PptFactorization.HighProbabilityBounds.gaussianMeasure
          Unit Unit η)
        (μα :=
          PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
            η)
        (X := X) (f := f) (g := g)
        hXmeas hfmeas hgmeas hXlaw hΩ
  · have hnorm :
        (fun z : EuclideanSpace ℂ η => ‖z‖ ^ 2) =
          fun _ => (0 : ℝ) := by
      funext z
      have hz : z = 0 := by
        ext i
        exact False.elim (hη ⟨i⟩)
      simp [hz]
    simpa [hnorm] using
      (ProbabilityTheory.indepFun_const_left
        (μ :=
          PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
            η)
        (c := (0 : ℝ))
        (fun z : EuclideanSpace ℂ η => ((‖z‖)⁻¹ : ℂ) • z))

/-- Alias for the block-independence theorem in the Gaussian section, kept so
the later mass-direction composition lemmas can continue to use the shorter
name. -/
theorem gaussianBlockLeftRight_indep :
    ProbabilityTheory.IndepFun
      (hermitianBlockLeft (ι := ι) (κ := κ))
      (hermitianBlockRight (ι := ι) (κ := κ))
      (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
        (Sum ι κ)) :=
  hermitianBlockLeft_indep_hermitianBlockRight (ι := ι) (κ := κ)

/-- Consequently the left mass-direction pair `(S,U)` is independent of the
right mass-direction pair `(T,V)`. -/
theorem gaussianBlockLeftRight_normSq_direction_indep :
    ProbabilityTheory.IndepFun
      (fun g : EuclideanSpace ℂ (Sum ι κ) =>
        (‖hermitianBlockLeft (ι := ι) (κ := κ) g‖ ^ 2,
          gaussianBlockLeftDirection (ι := ι) (κ := κ) g))
      (fun g : EuclideanSpace ℂ (Sum ι κ) =>
        (‖hermitianBlockRight (ι := ι) (κ := κ) g‖ ^ 2,
          gaussianBlockRightDirection (ι := ι) (κ := κ) g))
      (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
        (Sum ι κ)) := by
  let leftPair : EuclideanSpace ℂ ι → ℝ × EuclideanSpace ℂ ι :=
    fun z => (‖z‖ ^ 2, ((‖z‖)⁻¹ : ℂ) • z)
  let rightPair : EuclideanSpace ℂ κ → ℝ × EuclideanSpace ℂ κ :=
    fun z => (‖z‖ ^ 2, ((‖z‖)⁻¹ : ℂ) • z)
  have h :=
    (gaussianBlockLeftRight_indep (ι := ι) (κ := κ)).comp
      (show Measurable leftPair by
        dsimp [leftPair]
        fun_prop)
      (show Measurable rightPair by
        dsimp [rightPair]
        fun_prop)
  simpa [leftPair, rightPair, Function.comp, gaussianBlockLeftDirection,
    gaussianBlockRightDirection] using h

/-- After global Gaussian normalization, the left block mass becomes the
Gamma/Gamma ratio `‖G_E‖² / (‖G_E‖² + ‖G_F‖²)`. -/
theorem hermitianBlockMass_normalized_eq_gaussianBlockMassRatio
    (g : EuclideanSpace ℂ (Sum ι κ)) :
    hermitianBlockMass (ι := ι) (κ := κ)
        (hermitianBlockNormalize (η := Sum ι κ) g) =
      ‖hermitianBlockLeft (ι := ι) (κ := κ) g‖ ^ 2 /
        (‖hermitianBlockLeft (ι := ι) (κ := κ) g‖ ^ 2 +
          ‖hermitianBlockRight (ι := ι) (κ := κ) g‖ ^ 2) := by
  by_cases hg : g = 0
  · subst hg
    have hnormalize0 :
        hermitianBlockNormalize (η := Sum ι κ)
            (0 : EuclideanSpace ℂ (Sum ι κ)) = 0 := by
      simp [hermitianBlockNormalize]
    have hleft0 :
        hermitianBlockLeft (ι := ι) (κ := κ)
            (0 : EuclideanSpace ℂ (Sum ι κ)) = 0 := by
      ext i
      simp [hermitianBlockLeft]
    have hright0 :
        hermitianBlockRight (ι := ι) (κ := κ)
            (0 : EuclideanSpace ℂ (Sum ι κ)) = 0 := by
      ext j
      simp [hermitianBlockRight]
    rw [hnormalize0]
    unfold hermitianBlockMass
    rw [hleft0, hright0]
    simp
  · have hnorm_ne : ‖g‖ ≠ 0 := norm_ne_zero_iff.mpr hg
    have hinv_nonneg : 0 ≤ (‖g‖)⁻¹ := inv_nonneg.mpr (norm_nonneg g)
    have hnormalize :
        hermitianBlockNormalize (η := Sum ι κ) g =
          ((‖g‖)⁻¹ : ℝ) • g := by
      simpa [hermitianBlockNormalize] using
        (euclideanSpace_real_smul_eq_complex_smul ((‖g‖)⁻¹) g).symm
    have hleft :
        hermitianBlockLeft (ι := ι) (κ := κ)
            (hermitianBlockNormalize (η := Sum ι κ) g) =
          ((‖g‖)⁻¹ : ℝ) • hermitianBlockLeft (ι := ι) (κ := κ) g := by
      rw [hnormalize]
      ext i
      simp [hermitianBlockLeft]
    have hnorm_left :
        ‖hermitianBlockLeft (ι := ι) (κ := κ)
            (hermitianBlockNormalize (η := Sum ι κ) g)‖ =
          (‖g‖)⁻¹ * ‖hermitianBlockLeft (ι := ι) (κ := κ) g‖ := by
      rw [hleft, norm_real_smul_euclideanSpace hinv_nonneg]
    calc
      hermitianBlockMass (ι := ι) (κ := κ)
          (hermitianBlockNormalize (η := Sum ι κ) g) =
        ((‖g‖)⁻¹ * ‖hermitianBlockLeft (ι := ι) (κ := κ) g‖) ^ 2 := by
          unfold hermitianBlockMass
          rw [hnorm_left]
      _ =
        ‖hermitianBlockLeft (ι := ι) (κ := κ) g‖ ^ 2 / ‖g‖ ^ 2 := by
          field_simp [hnorm_ne]
      _ =
        ‖hermitianBlockLeft (ι := ι) (κ := κ) g‖ ^ 2 /
          (‖hermitianBlockLeft (ι := ι) (κ := κ) g‖ ^ 2 +
            ‖hermitianBlockRight (ι := ι) (κ := κ) g‖ ^ 2) := by
          simpa [hermitianBlock_norm_sq_eq_add (ι := ι) (κ := κ) g]

set_option linter.unusedSectionVars false in
/-- Almost-everywhere rewriting of the block mass after global Gaussian
normalization. -/
theorem hermitianBlockMass_comp_hermitianBlockNormalize_ae_eq_gaussianBlockMassRatio :
    (fun g : EuclideanSpace ℂ (Sum ι κ) =>
      hermitianBlockMass (ι := ι) (κ := κ)
        (hermitianBlockNormalize (η := Sum ι κ) g)) =ᵐ[
          PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
            (Sum ι κ)]
      (fun g =>
        ‖hermitianBlockLeft (ι := ι) (κ := κ) g‖ ^ 2 /
          (‖hermitianBlockLeft (ι := ι) (κ := κ) g‖ ^ 2 +
            ‖hermitianBlockRight (ι := ι) (κ := κ) g‖ ^ 2)) := by
  exact Filter.Eventually.of_forall
    (fun g =>
      hermitianBlockMass_normalized_eq_gaussianBlockMassRatio
        (ι := ι) (κ := κ) g)

set_option linter.unusedSectionVars false in
/-- Almost-everywhere rewriting of the left block direction after global
Gaussian normalization, stated directly with `hermitianBlockNormalize`. -/
theorem hermitianBlockLeftDirection_comp_hermitianBlockNormalize_ae_eq_gaussianBlockLeftDirection :
    (fun g : EuclideanSpace ℂ (Sum ι κ) =>
      hermitianBlockLeftDirection (ι := ι) (κ := κ)
        (hermitianBlockNormalize (η := Sum ι κ) g)) =ᵐ[
          PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
            (Sum ι κ)]
      gaussianBlockLeftDirection (ι := ι) (κ := κ) := by
  simpa [hermitianBlockNormalize] using
    (hermitianBlockLeftDirection_normalized_ae_eq_gaussianBlockLeftDirection
      (ι := ι) (κ := κ))

set_option linter.unusedSectionVars false in
/-- Almost-everywhere rewriting of the right block direction after global
Gaussian normalization, stated directly with `hermitianBlockNormalize`. -/
theorem hermitianBlockRightDirection_comp_hermitianBlockNormalize_ae_eq_gaussianBlockRightDirection :
    (fun g : EuclideanSpace ℂ (Sum ι κ) =>
      hermitianBlockRightDirection (ι := ι) (κ := κ)
        (hermitianBlockNormalize (η := Sum ι κ) g)) =ᵐ[
          PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
            (Sum ι κ)]
      gaussianBlockRightDirection (ι := ι) (κ := κ) := by
  simpa [hermitianBlockNormalize] using
    (hermitianBlockRightDirection_normalized_ae_eq_gaussianBlockRightDirection
      (ι := ι) (κ := κ))

set_option linter.unusedSectionVars false in
/-- Almost-everywhere rewriting of the full Hermitian block triple after global
Gaussian normalization.  This packages the mass and the two directions into a
single `ae` equality for pushforward arguments. -/
theorem hermitianBlockTriple_comp_hermitianBlockNormalize_ae_eq_gaussianTriple :
    (fun g : EuclideanSpace ℂ (Sum ι κ) =>
      (hermitianBlockMass (ι := ι) (κ := κ)
          (hermitianBlockNormalize (η := Sum ι κ) g),
        hermitianBlockLeftDirection (ι := ι) (κ := κ)
          (hermitianBlockNormalize (η := Sum ι κ) g),
        hermitianBlockRightDirection (ι := ι) (κ := κ)
          (hermitianBlockNormalize (η := Sum ι κ) g))) =ᵐ[
            PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
              (Sum ι κ)]
      (fun g =>
        (‖hermitianBlockLeft (ι := ι) (κ := κ) g‖ ^ 2 /
            (‖hermitianBlockLeft (ι := ι) (κ := κ) g‖ ^ 2 +
              ‖hermitianBlockRight (ι := ι) (κ := κ) g‖ ^ 2),
          gaussianBlockLeftDirection (ι := ι) (κ := κ) g,
          gaussianBlockRightDirection (ι := ι) (κ := κ) g)) := by
  filter_upwards
      [hermitianBlockMass_comp_hermitianBlockNormalize_ae_eq_gaussianBlockMassRatio
          (ι := ι) (κ := κ),
        hermitianBlockLeftDirection_comp_hermitianBlockNormalize_ae_eq_gaussianBlockLeftDirection
          (ι := ι) (κ := κ),
        hermitianBlockRightDirection_comp_hermitianBlockNormalize_ae_eq_gaussianBlockRightDirection
          (ι := ι) (κ := κ)] with g hmass hleft hright
  exact Prod.ext hmass (Prod.ext hleft hright)

/-- The block axes in product coordinates: one of the two blocks is zero. -/
def hermitianBlockProductAxes :
    Set (EuclideanSpace ℂ ι × EuclideanSpace ℂ κ) :=
  {x | x.1 = 0} ∪ {x | x.2 = 0}

/-- The same axes pulled back to the ambient `Sum` coordinate space. -/
def hermitianBlockAmbientAxes :
    Set (EuclideanSpace ℂ (Sum ι κ)) :=
  (hermitianBlockSumEquivProd (ι := ι) (κ := κ)) ⁻¹'
    hermitianBlockProductAxes (ι := ι) (κ := κ)

/-- Product-coordinate version of the block cone, away from the two axes. -/
noncomputable def hermitianBlockProductCone
    (massSet : Set ℝ)
    (leftSet : Set (EuclideanSpace ℂ ι))
    (rightSet : Set (EuclideanSpace ℂ κ)) :
    Set (EuclideanSpace ℂ ι × EuclideanSpace ℂ κ) :=
  {x |
    x ∉ hermitianBlockProductAxes (ι := ι) (κ := κ) ∧
      ‖x.1‖ ^ 2 / (‖x.1‖ ^ 2 + ‖x.2‖ ^ 2) ∈ massSet ∧
        hermitianBlockNormalize x.1 ∈ leftSet ∧
        hermitianBlockNormalize x.2 ∈ rightSet ∧
            ‖x.1‖ ^ 2 + ‖x.2‖ ^ 2 < 1}

theorem measurableSet_hermitianBlockProductCone
    {massSet : Set ℝ}
    {leftSet : Set (EuclideanSpace ℂ ι)}
    {rightSet : Set (EuclideanSpace ℂ κ)}
    (hmass : MeasurableSet massSet)
    (hleft : MeasurableSet leftSet)
    (hright : MeasurableSet rightSet) :
    MeasurableSet
      (hermitianBlockProductCone
        (ι := ι) (κ := κ) massSet leftSet rightSet) := by
  have hfst0 :
      MeasurableSet
        ({x | x.1 = (0 : EuclideanSpace ℂ ι)} :
          Set (EuclideanSpace ℂ ι × EuclideanSpace ℂ κ)) := by
    exact measurable_fst (measurableSet_singleton (0 : EuclideanSpace ℂ ι))
  have hsnd0 :
      MeasurableSet
        ({x | x.2 = (0 : EuclideanSpace ℂ κ)} :
          Set (EuclideanSpace ℂ ι × EuclideanSpace ℂ κ)) := by
    exact measurable_snd (measurableSet_singleton (0 : EuclideanSpace ℂ κ))
  have hmassMeas :
      Measurable
        (fun x : EuclideanSpace ℂ ι × EuclideanSpace ℂ κ =>
          ‖x.1‖ ^ 2 / (‖x.1‖ ^ 2 + ‖x.2‖ ^ 2)) := by
    fun_prop
  have hleftDirMeas :
      Measurable
        (fun x : EuclideanSpace ℂ ι × EuclideanSpace ℂ κ =>
          hermitianBlockNormalize x.1) := by
    exact measurable_hermitianBlockNormalize.comp measurable_fst
  have hrightDirMeas :
      Measurable
        (fun x : EuclideanSpace ℂ ι × EuclideanSpace ℂ κ =>
          hermitianBlockNormalize x.2) := by
    exact measurable_hermitianBlockNormalize.comp measurable_snd
  have hballMeas :
      Measurable
        (fun x : EuclideanSpace ℂ ι × EuclideanSpace ℂ κ =>
          ‖x.1‖ ^ 2 + ‖x.2‖ ^ 2) := by
    fun_prop
  exact
    (hfst0.union hsnd0).compl.inter
      ((hmassMeas hmass).inter
        ((hleftDirMeas hleft).inter
          ((hrightDirMeas hright).inter
            (measurableSet_lt hballMeas measurable_const))))

/-- Recomposition map from the factorized polar variables back to product
block coordinates. -/
noncomputable def hermitianBlockFactorPolarRecomposeProduct :
    ((Metric.sphere (0 : EuclideanSpace ℂ ι) 1 ×
        Metric.sphere (0 : EuclideanSpace ℂ κ) 1) ×
      (Set.Ioi (0 : ℝ) × Set.Ioi (0 : ℝ))) →
      EuclideanSpace ℂ ι × EuclideanSpace ℂ κ :=
  fun z =>
    ((z.2.1.1 : ℝ) • (z.1.1 : EuclideanSpace ℂ ι),
      (z.2.2.1 : ℝ) • (z.1.2 : EuclideanSpace ℂ κ))

/-- Recomposition map from factorized polar variables all the way back to
ambient `Sum` coordinates. -/
noncomputable def hermitianBlockFactorPolarRecomposeAmbient :
    ((Metric.sphere (0 : EuclideanSpace ℂ ι) 1 ×
        Metric.sphere (0 : EuclideanSpace ℂ κ) 1) ×
      (Set.Ioi (0 : ℝ) × Set.Ioi (0 : ℝ))) →
      EuclideanSpace ℂ (Sum ι κ) :=
  fun z =>
    (hermitianBlockSumEquivProd (ι := ι) (κ := κ)).symm
      (hermitianBlockFactorPolarRecomposeProduct (ι := ι) (κ := κ) z)

set_option linter.unusedSectionVars false in
/-- Left block commutes with real radial scalar multiplication. -/
theorem hermitianBlockLeft_real_smul
    (r : ℝ) (x : EuclideanSpace ℂ (Sum ι κ)) :
    hermitianBlockLeft (ι := ι) (κ := κ) ((r : ℝ) • x) =
      (r : ℝ) • hermitianBlockLeft (ι := ι) (κ := κ) x := by
  ext i
  simp [hermitianBlockLeft]

set_option linter.unusedSectionVars false in
/-- Right block commutes with real radial scalar multiplication. -/
theorem hermitianBlockRight_real_smul
    (r : ℝ) (x : EuclideanSpace ℂ (Sum ι κ)) :
    hermitianBlockRight (ι := ι) (κ := κ) ((r : ℝ) • x) =
      (r : ℝ) • hermitianBlockRight (ι := ι) (κ := κ) x := by
  ext j
  simp [hermitianBlockRight]

set_option linter.unusedSectionVars false in
theorem hermitianBlockProductAxes_eq :
    hermitianBlockProductAxes (ι := ι) (κ := κ) =
      ({0} ×ˢ (Set.univ : Set (EuclideanSpace ℂ κ))) ∪
        ((Set.univ : Set (EuclideanSpace ℂ ι)) ×ˢ {0}) := by
  ext x
  simp [hermitianBlockProductAxes]

/-- The product-coordinate left axis, as a real linear subspace. -/
def hermitianBlockProductLeftAxisSubmodule :
    Submodule ℝ (EuclideanSpace ℂ ι × EuclideanSpace ℂ κ) where
  carrier := {x | x.1 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change x.1 + y.1 = 0
    rw [hx, hy, zero_add]
  smul_mem' := by
    intro a x hx
    change a • x.1 = 0
    rw [hx]
    exact smul_zero a

/-- The product-coordinate right axis, as a real linear subspace. -/
def hermitianBlockProductRightAxisSubmodule :
    Submodule ℝ (EuclideanSpace ℂ ι × EuclideanSpace ℂ κ) where
  carrier := {x | x.2 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change x.2 + y.2 = 0
    rw [hx, hy, zero_add]
  smul_mem' := by
    intro a x hx
    change a • x.2 = 0
    rw [hx]
    exact smul_zero a

theorem hermitianBlockProductLeftAxisSubmodule_ne_top
    [Nonempty ι] :
    hermitianBlockProductLeftAxisSubmodule (ι := ι) (κ := κ) ≠ ⊤ := by
  intro htop
  obtain ⟨v, hv⟩ := exists_ne (0 : EuclideanSpace ℂ ι)
  have hmem :
      (v, (0 : EuclideanSpace ℂ κ)) ∈
        hermitianBlockProductLeftAxisSubmodule (ι := ι) (κ := κ) := by
    simpa [htop]
  exact hv (by simpa [hermitianBlockProductLeftAxisSubmodule] using hmem)

theorem hermitianBlockProductRightAxisSubmodule_ne_top
    [Nonempty κ] :
    hermitianBlockProductRightAxisSubmodule (ι := ι) (κ := κ) ≠ ⊤ := by
  intro htop
  obtain ⟨v, hv⟩ := exists_ne (0 : EuclideanSpace ℂ κ)
  have hmem :
      ((0 : EuclideanSpace ℂ ι), v) ∈
        hermitianBlockProductRightAxisSubmodule (ι := ι) (κ := κ) := by
    simpa [htop]
  exact hv (by simpa [hermitianBlockProductRightAxisSubmodule] using hmem)

theorem measure_prod_hermitianBlockProductLeftAxis_eq_zero
    [Nonempty ι] :
    ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).prod
        (MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)))
      ({x | x.1 = 0} : Set
        (EuclideanSpace ℂ ι × EuclideanSpace ℂ κ)) = 0 := by
  have hset :
      ({x | x.1 = 0} :
        Set (EuclideanSpace ℂ ι × EuclideanSpace ℂ κ)) =
        ({0} : Set (EuclideanSpace ℂ ι)) ×ˢ
          (Set.univ : Set (EuclideanSpace ℂ κ)) := by
    ext x
    simp
  rw [hset, Measure.prod_prod]
  simp

theorem measure_prod_hermitianBlockProductRightAxis_eq_zero
    [Nonempty κ] :
    ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).prod
        (MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)))
      ({x | x.2 = 0} : Set
        (EuclideanSpace ℂ ι × EuclideanSpace ℂ κ)) = 0 := by
  have hset :
      ({x | x.2 = 0} :
        Set (EuclideanSpace ℂ ι × EuclideanSpace ℂ κ)) =
        (Set.univ : Set (EuclideanSpace ℂ ι)) ×ˢ
          ({0} : Set (EuclideanSpace ℂ κ)) := by
    ext x
    simp
  rw [hset, Measure.prod_prod]
  simp

theorem measure_prod_hermitianBlockProductAxes_eq_zero
    [Nonempty ι] [Nonempty κ] :
    ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).prod
        (MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)))
      (hermitianBlockProductAxes (ι := ι) (κ := κ)) = 0
    := by
  rw [hermitianBlockProductAxes]
  exact measure_union_null
    (measure_prod_hermitianBlockProductLeftAxis_eq_zero
      (ι := ι) (κ := κ))
    (measure_prod_hermitianBlockProductRightAxis_eq_zero
      (ι := ι) (κ := κ))

/-- The scalar radial domain for the two separated block radii.

In separate polar coordinates `x_E = r_E u_E`, `x_F = r_F u_F`, the left mass
of the normalized total vector is

`r_E^2 / (r_E^2 + r_F^2)`,

and the cone over the unit sphere imposes `r_E^2 + r_F^2 < 1`. -/
noncomputable def hermitianBlockRadialMassCoord :
    Set.Ioi (0 : ℝ) × Set.Ioi (0 : ℝ) → ℝ :=
  fun r => r.1.1 ^ 2 / (r.1.1 ^ 2 + r.2.1 ^ 2)

/-- The scalar radial part of the cone condition `r_E^2 + r_F^2 < 1`. -/
noncomputable def hermitianBlockRadialBallSet :
    Set (Set.Ioi (0 : ℝ) × Set.Ioi (0 : ℝ)) :=
  {r | r.1.1 ^ 2 + r.2.1 ^ 2 < 1}

/-- The scalar radial domain for a left-mass set. -/
noncomputable def hermitianBlockRadialMassSet
    (massSet : Set ℝ) :
    Set (Set.Ioi (0 : ℝ) × Set.Ioi (0 : ℝ)) :=
  {r | hermitianBlockRadialMassCoord r ∈ massSet ∧
    r ∈ hermitianBlockRadialBallSet}

/-- The fully factorized polar-coordinate event:
left direction, right direction, and the scalar two-radius domain. -/
noncomputable def hermitianBlockFactorPolarSet
    (massSet : Set ℝ)
    (leftSet : Set (EuclideanSpace ℂ ι))
    (rightSet : Set (EuclideanSpace ℂ κ)) :
    Set ((Metric.sphere (0 : EuclideanSpace ℂ ι) 1 ×
        Metric.sphere (0 : EuclideanSpace ℂ κ) 1) ×
      (Set.Ioi (0 : ℝ) × Set.Ioi (0 : ℝ))) :=
  (hermitianBlockLeftSphereTrace (ι := ι) leftSet ×ˢ
      hermitianBlockRightSphereTrace (κ := κ) rightSet) ×ˢ
    hermitianBlockRadialMassSet massSet

/-- Geometric core: in product coordinates, the non-axis part of the ambient
block cone is exactly the image of the factorized polar rectangle under the
separate polar recomposition map. -/
theorem hermitianBlockProductCone_eq_factorPolar_image
    (massSet : Set ℝ)
    (leftSet : Set (EuclideanSpace ℂ ι))
    (rightSet : Set (EuclideanSpace ℂ κ)) :
    hermitianBlockProductCone (ι := ι) (κ := κ) massSet leftSet rightSet =
      hermitianBlockFactorPolarRecomposeProduct (ι := ι) (κ := κ) ''
      hermitianBlockFactorPolarSet (ι := ι) (κ := κ)
        massSet leftSet rightSet := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨haxes, hmass, hleft, hright, hball⟩
    have hx1_ne : x.1 ≠ 0 := by
      intro hzero
      exact haxes (by simp [hermitianBlockProductAxes, hzero])
    have hx2_ne : x.2 ≠ 0 := by
      intro hzero
      exact haxes (by simp [hermitianBlockProductAxes, hzero])
    let x1nz : ({0}ᶜ : Set (EuclideanSpace ℂ ι)) :=
      ⟨x.1, by simpa using hx1_ne⟩
    let x2nz : ({0}ᶜ : Set (EuclideanSpace ℂ κ)) :=
      ⟨x.2, by simpa using hx2_ne⟩
    let p1 := homeomorphUnitSphereProd (EuclideanSpace ℂ ι) x1nz
    let p2 := homeomorphUnitSphereProd (EuclideanSpace ℂ κ) x2nz
    refine ⟨((p1.1, p2.1), (p1.2, p2.2)), ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · change (p1.1 : EuclideanSpace ℂ ι) ∈ leftSet
          rw [homeomorphUnitSphereProd_fst_eq_hermitianBlockNormalize
            (η := ι) x1nz]
          exact hleft
        · change (p2.1 : EuclideanSpace ℂ κ) ∈ rightSet
          rw [homeomorphUnitSphereProd_fst_eq_hermitianBlockNormalize
            (η := κ) x2nz]
          exact hright
      · refine ⟨?_, ?_⟩
        · have hr1 := homeomorphUnitSphereProd_snd_eq_norm
            (η := ι) x1nz
          have hr2 := homeomorphUnitSphereProd_snd_eq_norm
            (η := κ) x2nz
          simpa [hermitianBlockRadialMassCoord, p1, p2, hr1, hr2]
            using hmass
        · have hr1 := homeomorphUnitSphereProd_snd_eq_norm
            (η := ι) x1nz
          have hr2 := homeomorphUnitSphereProd_snd_eq_norm
            (η := κ) x2nz
          simpa [hermitianBlockRadialBallSet, p1, p2, hr1, hr2]
            using hball
    · apply Prod.ext
      · simpa [hermitianBlockFactorPolarRecomposeProduct, p1, p2, x1nz]
          using homeomorphUnitSphereProd_recompose_eq (η := ι) x1nz
      · simpa [hermitianBlockFactorPolarRecomposeProduct, p1, p2, x2nz]
          using homeomorphUnitSphereProd_recompose_eq (η := κ) x2nz
  · rintro ⟨z, hz, rfl⟩
    rcases z with ⟨⟨u, v⟩, ⟨r, s⟩⟩
    rcases hz with ⟨⟨hu, hv⟩, ⟨hmass, hball⟩⟩
    have hnorm1 := norm_sq_real_smul_sphere (η := ι) u r
    have hnorm2 := norm_sq_real_smul_sphere (η := κ) v s
    have hleft_ne :
        (r : ℝ) • (u : EuclideanSpace ℂ ι) ≠ 0 := by
      intro hzero
      have hzero_sq : ((r : ℝ) ^ 2) = 0 := by
        simpa [hzero] using hnorm1.symm
      have hpos : 0 < ((r : ℝ) ^ 2) := sq_pos_of_pos r.2
      nlinarith
    have hright_ne :
        (s : ℝ) • (v : EuclideanSpace ℂ κ) ≠ 0 := by
      intro hzero
      have hzero_sq : ((s : ℝ) ^ 2) = 0 := by
        simpa [hzero] using hnorm2.symm
      have hpos : 0 < ((s : ℝ) ^ 2) := sq_pos_of_pos s.2
      nlinarith
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [hermitianBlockProductAxes, hermitianBlockFactorPolarRecomposeProduct,
        hleft_ne, hright_ne]
    · simpa [hermitianBlockFactorPolarRecomposeProduct,
        hermitianBlockRadialMassCoord, hnorm1, hnorm2] using hmass
    · simpa [hermitianBlockFactorPolarRecomposeProduct,
        hermitianBlockNormalize_real_smul_sphere (η := ι) u r] using hu
    · simpa [hermitianBlockFactorPolarRecomposeProduct,
        hermitianBlockNormalize_real_smul_sphere (η := κ) v s] using hv
    · simpa [hermitianBlockFactorPolarRecomposeProduct,
        hermitianBlockRadialBallSet, hnorm1, hnorm2] using hball

/-- For the global polar decomposition of a nonzero ambient block vector, the
left mass of the angular component is the product-coordinate block ratio of the
original vector. -/
theorem hermitianBlockMass_polar_fst_eq_ratio
    (x : ({0}ᶜ : Set (EuclideanSpace ℂ (Sum ι κ)))) :
    hermitianBlockMass (ι := ι) (κ := κ)
        ((homeomorphUnitSphereProd (EuclideanSpace ℂ (Sum ι κ)) x).1 :
          EuclideanSpace ℂ (Sum ι κ)) =
      ‖hermitianBlockLeft (ι := ι) (κ := κ)
          (x : EuclideanSpace ℂ (Sum ι κ))‖ ^ 2 /
        (‖hermitianBlockLeft (ι := ι) (κ := κ)
            (x : EuclideanSpace ℂ (Sum ι κ))‖ ^ 2 +
          ‖hermitianBlockRight (ι := ι) (κ := κ)
            (x : EuclideanSpace ℂ (Sum ι κ))‖ ^ 2) := by
  let p := homeomorphUnitSphereProd (EuclideanSpace ℂ (Sum ι κ)) x
  let u : EuclideanSpace ℂ (Sum ι κ) :=
    (p.1 : EuclideanSpace ℂ (Sum ι κ))
  let r : ℝ := p.2.1
  have hrpos : 0 < r := p.2.2
  have hrnonneg : 0 ≤ r := le_of_lt hrpos
  have hrec : r • u = (x : EuclideanSpace ℂ (Sum ι κ)) := by
    simpa [p, u, r] using
      homeomorphUnitSphereProd_recompose_eq
        (η := Sum ι κ) x
  have hleftx :
      hermitianBlockLeft (ι := ι) (κ := κ)
          (x : EuclideanSpace ℂ (Sum ι κ)) =
        r • hermitianBlockLeft (ι := ι) (κ := κ) u := by
    rw [← hrec]
    exact hermitianBlockLeft_real_smul (ι := ι) (κ := κ) r u
  have hrightx :
      hermitianBlockRight (ι := ι) (κ := κ)
          (x : EuclideanSpace ℂ (Sum ι κ)) =
        r • hermitianBlockRight (ι := ι) (κ := κ) u := by
    rw [← hrec]
    exact hermitianBlockRight_real_smul (ι := ι) (κ := κ) r u
  have hnormL :
      ‖hermitianBlockLeft (ι := ι) (κ := κ)
          (x : EuclideanSpace ℂ (Sum ι κ))‖ =
        r * ‖hermitianBlockLeft (ι := ι) (κ := κ) u‖ := by
    rw [hleftx]
    exact norm_real_smul_euclideanSpace (η := ι) hrnonneg _
  have hnormR :
      ‖hermitianBlockRight (ι := ι) (κ := κ)
          (x : EuclideanSpace ℂ (Sum ι κ))‖ =
        r * ‖hermitianBlockRight (ι := ι) (κ := κ) u‖ := by
    rw [hrightx]
    exact norm_real_smul_euclideanSpace (η := κ) hrnonneg _
  have hunorm : ‖u‖ = 1 := by
    simpa [u, p, Metric.mem_sphere, dist_eq_norm] using p.1.2
  have hsumu :
      ‖hermitianBlockLeft (ι := ι) (κ := κ) u‖ ^ 2 +
        ‖hermitianBlockRight (ι := ι) (κ := κ) u‖ ^ 2 = 1 := by
    have h := hermitianBlock_norm_sq_eq_add (ι := ι) (κ := κ) u
    nlinarith
  have hden :
      r ^ 2 *
        (‖hermitianBlockLeft (ι := ι) (κ := κ) u‖ ^ 2 +
          ‖hermitianBlockRight (ι := ι) (κ := κ) u‖ ^ 2) ≠ 0 := by
    have hr2 : r ^ 2 ≠ 0 := by
      nlinarith [sq_pos_of_pos hrpos]
    nlinarith
  unfold hermitianBlockMass
  rw [hnormL, hnormR]
  field_simp [hden]
  nlinarith

/-- The ambient left-zero block, as a real linear subspace. -/
noncomputable def hermitianBlockLeftZeroSubmodule :
    Submodule ℝ (EuclideanSpace ℂ (Sum ι κ)) where
  carrier := {x | ∀ i : ι, x (Sum.inl i) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy i
    simp [hx i, hy i]
  smul_mem' := by
    intro a x hx i
    simp [hx i]

/-- The ambient right-zero block, as a real linear subspace. -/
noncomputable def hermitianBlockRightZeroSubmodule :
    Submodule ℝ (EuclideanSpace ℂ (Sum ι κ)) where
  carrier := {x | ∀ j : κ, x (Sum.inr j) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy j
    simp [hx j, hy j]
  smul_mem' := by
    intro a x hx j
    simp [hx j]

theorem mem_hermitianBlockLeftZeroSubmodule
    (x : EuclideanSpace ℂ (Sum ι κ)) :
    x ∈ hermitianBlockLeftZeroSubmodule (ι := ι) (κ := κ) ↔
      hermitianBlockLeft (ι := ι) (κ := κ) x = 0 := by
  constructor
  · intro hx
    ext i
    simpa [hermitianBlockLeft] using hx i
  · intro hx i
    have hfun : (fun i : ι => x (Sum.inl i)) = 0 := by
      simpa [hermitianBlockLeft] using hx
    exact congr_fun hfun i

theorem mem_hermitianBlockRightZeroSubmodule
    (x : EuclideanSpace ℂ (Sum ι κ)) :
    x ∈ hermitianBlockRightZeroSubmodule (ι := ι) (κ := κ) ↔
      hermitianBlockRight (ι := ι) (κ := κ) x = 0 := by
  constructor
  · intro hx
    ext j
    simpa [hermitianBlockRight] using hx j
  · intro hx j
    have hfun : (fun j : κ => x (Sum.inr j)) = 0 := by
      simpa [hermitianBlockRight] using hx
    exact congr_fun hfun j

theorem hermitianBlockLeftZeroSubmodule_ne_top
    [Nonempty ι] :
    hermitianBlockLeftZeroSubmodule (ι := ι) (κ := κ) ≠ ⊤ := by
  intro htop
  obtain ⟨v, hv⟩ := exists_ne (0 : EuclideanSpace ℂ ι)
  let x : EuclideanSpace ℂ (Sum ι κ) :=
    (hermitianBlockSumEquivProd (ι := ι) (κ := κ)).symm
      (v, (0 : EuclideanSpace ℂ κ))
  have hmem :
      x ∈ hermitianBlockLeftZeroSubmodule (ι := ι) (κ := κ) := by
    simpa [htop]
  have hleft :
      hermitianBlockLeft (ι := ι) (κ := κ) x = 0 :=
    (mem_hermitianBlockLeftZeroSubmodule
      (ι := ι) (κ := κ) x).1 hmem
  have : v = 0 := by
    simpa [x, hermitianBlockLeft_sumEquivProd_symm] using hleft
  exact hv this

theorem hermitianBlockRightZeroSubmodule_ne_top
    [Nonempty κ] :
    hermitianBlockRightZeroSubmodule (ι := ι) (κ := κ) ≠ ⊤ := by
  intro htop
  obtain ⟨v, hv⟩ := exists_ne (0 : EuclideanSpace ℂ κ)
  let x : EuclideanSpace ℂ (Sum ι κ) :=
    (hermitianBlockSumEquivProd (ι := ι) (κ := κ)).symm
      ((0 : EuclideanSpace ℂ ι), v)
  have hmem :
      x ∈ hermitianBlockRightZeroSubmodule (ι := ι) (κ := κ) := by
    simpa [htop]
  have hright :
      hermitianBlockRight (ι := ι) (κ := κ) x = 0 :=
    (mem_hermitianBlockRightZeroSubmodule
      (ι := ι) (κ := κ) x).1 hmem
  have : v = 0 := by
    simpa [x, hermitianBlockRight_sumEquivProd_symm] using hright
  exact hv this

theorem volume_hermitianBlockLeftZero_eq_zero
    [Nonempty ι] :
    (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ)))
      ({x | hermitianBlockLeft (ι := ι) (κ := κ) x = 0} :
        Set (EuclideanSpace ℂ (Sum ι κ))) = 0 := by
  have hset :
      (hermitianBlockLeftZeroSubmodule (ι := ι) (κ := κ) :
        Set (EuclideanSpace ℂ (Sum ι κ))) =
      ({x | hermitianBlockLeft (ι := ι) (κ := κ) x = 0} :
        Set (EuclideanSpace ℂ (Sum ι κ))) := by
    ext x
    exact mem_hermitianBlockLeftZeroSubmodule (ι := ι) (κ := κ) x
  rw [← hset]
  exact
    Measure.addHaar_submodule
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ)))
      (hermitianBlockLeftZeroSubmodule (ι := ι) (κ := κ))
      (hermitianBlockLeftZeroSubmodule_ne_top
        (ι := ι) (κ := κ))

theorem volume_hermitianBlockRightZero_eq_zero
    [Nonempty κ] :
    (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ)))
      ({x | hermitianBlockRight (ι := ι) (κ := κ) x = 0} :
        Set (EuclideanSpace ℂ (Sum ι κ))) = 0 := by
  have hset :
      (hermitianBlockRightZeroSubmodule (ι := ι) (κ := κ) :
        Set (EuclideanSpace ℂ (Sum ι κ))) =
      ({x | hermitianBlockRight (ι := ι) (κ := κ) x = 0} :
        Set (EuclideanSpace ℂ (Sum ι κ))) := by
    ext x
    exact mem_hermitianBlockRightZeroSubmodule (ι := ι) (κ := κ) x
  rw [← hset]
  exact
    Measure.addHaar_submodule
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ)))
      (hermitianBlockRightZeroSubmodule (ι := ι) (κ := κ))
      (hermitianBlockRightZeroSubmodule_ne_top
        (ι := ι) (κ := κ))

theorem hermitianBlockAmbientAxes_eq_zeroSets :
    hermitianBlockAmbientAxes (ι := ι) (κ := κ) =
      ({x | hermitianBlockLeft (ι := ι) (κ := κ) x = 0} :
        Set (EuclideanSpace ℂ (Sum ι κ))) ∪
      ({x | hermitianBlockRight (ι := ι) (κ := κ) x = 0} :
        Set (EuclideanSpace ℂ (Sum ι κ))) := by
  ext x
  unfold hermitianBlockAmbientAxes hermitianBlockProductAxes
  simp only [Set.mem_preimage, Set.mem_union, Set.mem_setOf_eq]
  rw [hermitianBlockSumEquivProd_fst, hermitianBlockSumEquivProd_snd]

/-- The two ambient axes have zero volume.  This is the null-boundary fact that
allows the totalized directions to be compared with genuine polar coordinates. -/
theorem measure_hermitianBlockAmbientAxes_eq_zero
    [Nonempty ι] [Nonempty κ] :
    (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ)))
      (hermitianBlockAmbientAxes (ι := ι) (κ := κ)) = 0
    := by
  rw [hermitianBlockAmbientAxes_eq_zeroSets]
  exact measure_union_null
    (volume_hermitianBlockLeftZero_eq_zero
      (ι := ι) (κ := κ))
    (volume_hermitianBlockRightZero_eq_zero
      (ι := ι) (κ := κ))

/-- Spherical set where the left Hermitian block vanishes. -/
noncomputable def hermitianBlockLeftZeroSphereSet :
    Set (Metric.sphere (0 : EuclideanSpace ℂ (Sum ι κ)) 1) :=
  {x | hermitianBlockLeft (ι := ι) (κ := κ)
      (x : EuclideanSpace ℂ (Sum ι κ)) = 0}

/-- Spherical set where the right Hermitian block vanishes. -/
noncomputable def hermitianBlockRightZeroSphereSet :
    Set (Metric.sphere (0 : EuclideanSpace ℂ (Sum ι κ)) 1) :=
  {x | hermitianBlockRight (ι := ι) (κ := κ)
      (x : EuclideanSpace ℂ (Sum ι κ)) = 0}

/-- The spherical null boundary where at least one block direction is
degenerate. -/
noncomputable def hermitianBlockAxisSphereSet :
    Set (Metric.sphere (0 : EuclideanSpace ℂ (Sum ι κ)) 1) :=
  hermitianBlockLeftZeroSphereSet (ι := ι) (κ := κ) ∪
    hermitianBlockRightZeroSphereSet (ι := ι) (κ := κ)

theorem measurableSet_hermitianBlockLeftZeroSphereSet :
    MeasurableSet (hermitianBlockLeftZeroSphereSet (ι := ι) (κ := κ)) := by
  exact ((measurable_hermitianBlockLeft
    (ι := ι) (κ := κ)).comp measurable_subtype_coe)
      (measurableSet_singleton (0 : EuclideanSpace ℂ ι))

theorem measurableSet_hermitianBlockRightZeroSphereSet :
    MeasurableSet (hermitianBlockRightZeroSphereSet (ι := ι) (κ := κ)) := by
  exact ((measurable_hermitianBlockRight
    (ι := ι) (κ := κ)).comp measurable_subtype_coe)
      (measurableSet_singleton (0 : EuclideanSpace ℂ κ))

theorem measurableSet_hermitianBlockAxisSphereSet :
    MeasurableSet (hermitianBlockAxisSphereSet (ι := ι) (κ := κ)) := by
  exact measurableSet_hermitianBlockLeftZeroSphereSet
    (ι := ι) (κ := κ) |>.union
      (measurableSet_hermitianBlockRightZeroSphereSet
        (ι := ι) (κ := κ))

theorem toSphere_hermitianBlockLeftZeroSphereSet_eq_zero
    [Nonempty ι] :
    (MeasureTheory.volume :
        Measure (EuclideanSpace ℂ (Sum ι κ))).toSphere
      (hermitianBlockLeftZeroSphereSet (ι := ι) (κ := κ)) = 0 := by
  rw [Measure.toSphere_apply'
    (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ)))
    (measurableSet_hermitianBlockLeftZeroSphereSet
      (ι := ι) (κ := κ))]
  have hsubset :
      Set.Ioo (0 : ℝ) 1 •
          ((Subtype.val :
              Metric.sphere (0 : EuclideanSpace ℂ (Sum ι κ)) 1 →
                EuclideanSpace ℂ (Sum ι κ)) ''
            hermitianBlockLeftZeroSphereSet (ι := ι) (κ := κ)) ⊆
        ({x | hermitianBlockLeft (ι := ι) (κ := κ) x = 0} :
          Set (EuclideanSpace ℂ (Sum ι κ))) := by
    rintro y ⟨r, hr, z, hz, rfl⟩
    rcases hz with ⟨u, hu, rfl⟩
    have hfun : (fun i : ι =>
        (u : EuclideanSpace ℂ (Sum ι κ)) (Sum.inl i)) = 0 := by
      simpa [hermitianBlockLeftZeroSphereSet, hermitianBlockLeft] using hu
    ext i
    have hi :
        (u : EuclideanSpace ℂ (Sum ι κ)) (Sum.inl i) = 0 := by
      simpa using congr_fun hfun i
    change (r : ℂ) * (u : EuclideanSpace ℂ (Sum ι κ)) (Sum.inl i) = 0
    rw [hi, mul_zero]
  have hcone :
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ)))
        (Set.Ioo (0 : ℝ) 1 •
          ((Subtype.val :
              Metric.sphere (0 : EuclideanSpace ℂ (Sum ι κ)) 1 →
                EuclideanSpace ℂ (Sum ι κ)) ''
            hermitianBlockLeftZeroSphereSet (ι := ι) (κ := κ))) = 0 :=
    measure_mono_null hsubset
      (volume_hermitianBlockLeftZero_eq_zero
        (ι := ι) (κ := κ))
  exact mul_eq_zero.mpr (Or.inr hcone)

theorem toSphere_hermitianBlockRightZeroSphereSet_eq_zero
    [Nonempty κ] :
    (MeasureTheory.volume :
        Measure (EuclideanSpace ℂ (Sum ι κ))).toSphere
      (hermitianBlockRightZeroSphereSet (ι := ι) (κ := κ)) = 0 := by
  rw [Measure.toSphere_apply'
    (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ)))
    (measurableSet_hermitianBlockRightZeroSphereSet
      (ι := ι) (κ := κ))]
  have hsubset :
      Set.Ioo (0 : ℝ) 1 •
          ((Subtype.val :
              Metric.sphere (0 : EuclideanSpace ℂ (Sum ι κ)) 1 →
                EuclideanSpace ℂ (Sum ι κ)) ''
            hermitianBlockRightZeroSphereSet (ι := ι) (κ := κ)) ⊆
        ({x | hermitianBlockRight (ι := ι) (κ := κ) x = 0} :
          Set (EuclideanSpace ℂ (Sum ι κ))) := by
    rintro y ⟨r, hr, z, hz, rfl⟩
    rcases hz with ⟨u, hu, rfl⟩
    have hfun : (fun j : κ =>
        (u : EuclideanSpace ℂ (Sum ι κ)) (Sum.inr j)) = 0 := by
      simpa [hermitianBlockRightZeroSphereSet, hermitianBlockRight] using hu
    ext j
    have hj :
        (u : EuclideanSpace ℂ (Sum ι κ)) (Sum.inr j) = 0 := by
      simpa using congr_fun hfun j
    change (r : ℂ) * (u : EuclideanSpace ℂ (Sum ι κ)) (Sum.inr j) = 0
    rw [hj, mul_zero]
  have hcone :
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ)))
        (Set.Ioo (0 : ℝ) 1 •
          ((Subtype.val :
              Metric.sphere (0 : EuclideanSpace ℂ (Sum ι κ)) 1 →
                EuclideanSpace ℂ (Sum ι κ)) ''
            hermitianBlockRightZeroSphereSet (ι := ι) (κ := κ))) = 0 :=
    measure_mono_null hsubset
      (volume_hermitianBlockRightZero_eq_zero
        (ι := ι) (κ := κ))
  exact mul_eq_zero.mpr (Or.inr hcone)

theorem toFinite_toSphere_hermitianBlockLeftZeroSphereSet_eq_zero
    [Nonempty ι]
    [SFinite
      (MeasureTheory.Measure.toSphere
        (MeasureTheory.volume : Measure
          (EuclideanSpace ℂ (Sum ι κ))))] :
    (MeasureTheory.volume :
        Measure (EuclideanSpace ℂ (Sum ι κ))).toSphere.toFinite
      (hermitianBlockLeftZeroSphereSet (ι := ι) (κ := κ)) = 0 := by
  exact MeasureTheory.toFinite_apply_eq_zero_iff.2
    (toSphere_hermitianBlockLeftZeroSphereSet_eq_zero
      (ι := ι) (κ := κ))

theorem toFinite_toSphere_hermitianBlockRightZeroSphereSet_eq_zero
    [Nonempty κ]
    [SFinite
      (MeasureTheory.Measure.toSphere
        (MeasureTheory.volume : Measure
          (EuclideanSpace ℂ (Sum ι κ))))] :
    (MeasureTheory.volume :
        Measure (EuclideanSpace ℂ (Sum ι κ))).toSphere.toFinite
      (hermitianBlockRightZeroSphereSet (ι := ι) (κ := κ)) = 0 := by
  exact MeasureTheory.toFinite_apply_eq_zero_iff.2
    (toSphere_hermitianBlockRightZeroSphereSet_eq_zero
      (ι := ι) (κ := κ))

theorem toSphere_hermitianBlockAxisSphereSet_eq_zero
    [Nonempty ι] [Nonempty κ] :
    (MeasureTheory.volume :
        Measure (EuclideanSpace ℂ (Sum ι κ))).toSphere
      (hermitianBlockAxisSphereSet (ι := ι) (κ := κ)) = 0 := by
  rw [hermitianBlockAxisSphereSet]
  exact measure_union_null
    (toSphere_hermitianBlockLeftZeroSphereSet_eq_zero
      (ι := ι) (κ := κ))
    (toSphere_hermitianBlockRightZeroSphereSet_eq_zero
      (ι := ι) (κ := κ))

theorem toFinite_toSphere_hermitianBlockAxisSphereSet_eq_zero
    [Nonempty ι] [Nonempty κ]
    [SFinite
      (MeasureTheory.Measure.toSphere
        (MeasureTheory.volume : Measure
          (EuclideanSpace ℂ (Sum ι κ))))] :
    (MeasureTheory.volume :
        Measure (EuclideanSpace ℂ (Sum ι κ))).toSphere.toFinite
      (hermitianBlockAxisSphereSet (ι := ι) (κ := κ)) = 0 := by
  exact MeasureTheory.toFinite_apply_eq_zero_iff.2
    (toSphere_hermitianBlockAxisSphereSet_eq_zero
      (ι := ι) (κ := κ))

theorem surfaceMeasureAmbient_hermitianBlockLeft_eq_zero_eq_zero
    [Nonempty ι]
    [SFinite
      (MeasureTheory.Measure.toSphere
        (MeasureTheory.volume : Measure
          (EuclideanSpace ℂ (Sum ι κ))))] :
    surfaceMeasureAmbient (Sum ι κ)
      ({x | hermitianBlockLeft (ι := ι) (κ := κ) x = 0} :
        Set (EuclideanSpace ℂ (Sum ι κ))) = 0 := by
  have hmeasAmbient :
      MeasurableSet
        ({x | hermitianBlockLeft (ι := ι) (κ := κ) x = 0} :
          Set (EuclideanSpace ℂ (Sum ι κ))) := by
    have hpre :
        ({x | hermitianBlockLeft (ι := ι) (κ := κ) x = 0} :
          Set (EuclideanSpace ℂ (Sum ι κ))) =
        (hermitianBlockLeft (ι := ι) (κ := κ)) ⁻¹'
          ({0} : Set (EuclideanSpace ℂ ι)) := by
      ext x
      simp
    rw [hpre]
    exact
      (measurable_hermitianBlockLeft
        (ι := ι) (κ := κ))
          (measurableSet_singleton (0 : EuclideanSpace ℂ ι))
  rw [surfaceMeasureAmbient]
  rw [Measure.map_apply measurable_subtype_coe hmeasAmbient]
  change surfaceMeasure (Sum ι κ)
      ((Subtype.val :
          Metric.sphere (0 : EuclideanSpace ℂ (Sum ι κ)) 1 →
            EuclideanSpace ℂ (Sum ι κ)) ⁻¹'
        ({x | hermitianBlockLeft (ι := ι) (κ := κ) x = 0} :
          Set (EuclideanSpace ℂ (Sum ι κ)))) = 0
  have hpre :
      ((Subtype.val :
          Metric.sphere (0 : EuclideanSpace ℂ (Sum ι κ)) 1 →
            EuclideanSpace ℂ (Sum ι κ)) ⁻¹'
        ({x | hermitianBlockLeft (ι := ι) (κ := κ) x = 0} :
          Set (EuclideanSpace ℂ (Sum ι κ)))) =
        hermitianBlockLeftZeroSphereSet (ι := ι) (κ := κ) := by
    ext u
    simp [hermitianBlockLeftZeroSphereSet]
  rw [hpre]
  change (MeasureTheory.volume :
      Measure (EuclideanSpace ℂ (Sum ι κ))).toSphere.toFinite
    (hermitianBlockLeftZeroSphereSet (ι := ι) (κ := κ)) = 0
  exact toFinite_toSphere_hermitianBlockLeftZeroSphereSet_eq_zero
    (ι := ι) (κ := κ)

theorem surfaceMeasureAmbient_hermitianBlockRight_eq_zero_eq_zero
    [Nonempty κ]
    [SFinite
      (MeasureTheory.Measure.toSphere
        (MeasureTheory.volume : Measure
          (EuclideanSpace ℂ (Sum ι κ))))] :
    surfaceMeasureAmbient (Sum ι κ)
      ({x | hermitianBlockRight (ι := ι) (κ := κ) x = 0} :
        Set (EuclideanSpace ℂ (Sum ι κ))) = 0 := by
  have hmeasAmbient :
      MeasurableSet
        ({x | hermitianBlockRight (ι := ι) (κ := κ) x = 0} :
          Set (EuclideanSpace ℂ (Sum ι κ))) := by
    have hpre :
        ({x | hermitianBlockRight (ι := ι) (κ := κ) x = 0} :
          Set (EuclideanSpace ℂ (Sum ι κ))) =
        (hermitianBlockRight (ι := ι) (κ := κ)) ⁻¹'
          ({0} : Set (EuclideanSpace ℂ κ)) := by
      ext x
      simp
    rw [hpre]
    exact
      (measurable_hermitianBlockRight
        (ι := ι) (κ := κ))
          (measurableSet_singleton (0 : EuclideanSpace ℂ κ))
  rw [surfaceMeasureAmbient]
  rw [Measure.map_apply measurable_subtype_coe hmeasAmbient]
  change surfaceMeasure (Sum ι κ)
      ((Subtype.val :
          Metric.sphere (0 : EuclideanSpace ℂ (Sum ι κ)) 1 →
            EuclideanSpace ℂ (Sum ι κ)) ⁻¹'
        ({x | hermitianBlockRight (ι := ι) (κ := κ) x = 0} :
          Set (EuclideanSpace ℂ (Sum ι κ)))) = 0
  have hpre :
      ((Subtype.val :
          Metric.sphere (0 : EuclideanSpace ℂ (Sum ι κ)) 1 →
            EuclideanSpace ℂ (Sum ι κ)) ⁻¹'
        ({x | hermitianBlockRight (ι := ι) (κ := κ) x = 0} :
          Set (EuclideanSpace ℂ (Sum ι κ)))) =
        hermitianBlockRightZeroSphereSet (ι := ι) (κ := κ) := by
    ext u
    simp [hermitianBlockRightZeroSphereSet]
  rw [hpre]
  change (MeasureTheory.volume :
      Measure (EuclideanSpace ℂ (Sum ι κ))).toSphere.toFinite
    (hermitianBlockRightZeroSphereSet (ι := ι) (κ := κ)) = 0
  exact toFinite_toSphere_hermitianBlockRightZeroSphereSet_eq_zero
    (ι := ι) (κ := κ)

/-- For a radial multiple of a unit ambient block vector, the product-coordinate
block ratio is exactly the left mass of the unit vector. -/
theorem hermitianBlock_product_ratio_real_smul_sphere
    (u : Metric.sphere (0 : EuclideanSpace ℂ (Sum ι κ)) 1)
    {r : ℝ} (hr : 0 < r) :
    ‖hermitianBlockLeft (ι := ι) (κ := κ)
        ((r : ℝ) • (u : EuclideanSpace ℂ (Sum ι κ)))‖ ^ 2 /
      (‖hermitianBlockLeft (ι := ι) (κ := κ)
          ((r : ℝ) • (u : EuclideanSpace ℂ (Sum ι κ)))‖ ^ 2 +
        ‖hermitianBlockRight (ι := ι) (κ := κ)
          ((r : ℝ) • (u : EuclideanSpace ℂ (Sum ι κ)))‖ ^ 2) =
      hermitianBlockMass (ι := ι) (κ := κ)
        (u : EuclideanSpace ℂ (Sum ι κ)) := by
  have hxnorm :=
    norm_sq_real_smul_sphere (η := Sum ι κ) u ⟨r, hr⟩
  have hxne :
      (r : ℝ) • (u : EuclideanSpace ℂ (Sum ι κ)) ≠ 0 := by
    intro hzero
    have hzero_sq : r ^ 2 = 0 := by
      simpa [hzero] using hxnorm.symm
    have hpos : 0 < r ^ 2 := sq_pos_of_pos hr
    nlinarith
  let xnz : ({0}ᶜ : Set (EuclideanSpace ℂ (Sum ι κ))) :=
    ⟨(r : ℝ) • (u : EuclideanSpace ℂ (Sum ι κ)), by simpa using hxne⟩
  have hp1 :
      ((homeomorphUnitSphereProd (EuclideanSpace ℂ (Sum ι κ)) xnz).1 :
        EuclideanSpace ℂ (Sum ι κ)) =
        (u : EuclideanSpace ℂ (Sum ι κ)) := by
    rw [homeomorphUnitSphereProd_fst_eq_hermitianBlockNormalize]
    exact
      hermitianBlockNormalize_real_smul_sphere
        (η := Sum ι κ) u ⟨r, hr⟩
  have h := hermitianBlockMass_polar_fst_eq_ratio
    (ι := ι) (κ := κ) xnz
  rw [hp1] at h
  exact h.symm

/-- The product-coordinate cone, pulled back to ambient `Sum` coordinates, is
contained in the radial cone over the corresponding spherical rectangle. -/
theorem hermitianBlock_preimage_productCone_subset_rectCone
    (massSet : Set ℝ)
    (leftSet : Set (EuclideanSpace ℂ ι))
    (rightSet : Set (EuclideanSpace ℂ κ)) :
    ((hermitianBlockSumEquivProd (ι := ι) (κ := κ)) ⁻¹'
        hermitianBlockProductCone (ι := ι) (κ := κ)
          massSet leftSet rightSet) ⊆
      hermitianBlockRectCone (ι := ι) (κ := κ)
        massSet leftSet rightSet := by
  intro x hx
  rcases hx with ⟨haxes, hmass, hleft, hright, hball⟩
  have hxleft_ne : hermitianBlockLeft (ι := ι) (κ := κ) x ≠ 0 := by
    intro hzero
    exact haxes (Or.inl (by
      simpa [hermitianBlockSumEquivProd_fst, hermitianBlockLeft]
        using hzero))
  have hxnz : x ≠ 0 := by
    intro hzero
    subst hzero
    exact hxleft_ne (by ext i; simp [hermitianBlockLeft])
  let xnz : ({0}ᶜ : Set (EuclideanSpace ℂ (Sum ι κ))) :=
    ⟨x, by simpa using hxnz⟩
  let p := homeomorphUnitSphereProd (EuclideanSpace ℂ (Sum ι κ)) xnz
  have hxnorm_sq_lt : ‖x‖ ^ 2 < 1 := by
    have h := hermitianBlock_norm_sq_eq_add (ι := ι) (κ := κ) x
    simpa [hermitianBlockSumEquivProd_fst, hermitianBlockSumEquivProd_snd, h]
      using hball
  have hxnorm_lt : ‖x‖ < 1 := by
    nlinarith [norm_nonneg x]
  have hrlt : (p.2 : ℝ) < 1 := by
    rw [homeomorphUnitSphereProd_snd_eq_norm (η := Sum ι κ) xnz]
    exact hxnorm_lt
  have hrec :
      (p.2 : ℝ) • (p.1 : EuclideanSpace ℂ (Sum ι κ)) = x := by
    simpa [p, xnz] using
      homeomorphUnitSphereProd_recompose_eq (η := Sum ι κ) xnz
  have hmassx :
      ‖hermitianBlockLeft (ι := ι) (κ := κ) x‖ ^ 2 /
        (‖hermitianBlockLeft (ι := ι) (κ := κ) x‖ ^ 2 +
          ‖hermitianBlockRight (ι := ι) (κ := κ) x‖ ^ 2) ∈
        massSet := by
    simpa [hermitianBlockSumEquivProd_fst, hermitianBlockSumEquivProd_snd]
      using hmass
  have hmassu :
      hermitianBlockMass (ι := ι) (κ := κ)
        (p.1 : EuclideanSpace ℂ (Sum ι κ)) ∈ massSet := by
    rw [hermitianBlockMass_polar_fst_eq_ratio (ι := ι) (κ := κ) xnz]
    exact hmassx
  have hleftx :
      hermitianBlockLeft (ι := ι) (κ := κ) x =
        (p.2 : ℝ) • hermitianBlockLeft (ι := ι) (κ := κ)
          (p.1 : EuclideanSpace ℂ (Sum ι κ)) := by
    rw [← hrec]
    exact hermitianBlockLeft_real_smul
      (ι := ι) (κ := κ) (p.2 : ℝ)
      (p.1 : EuclideanSpace ℂ (Sum ι κ))
  have hrightx :
      hermitianBlockRight (ι := ι) (κ := κ) x =
        (p.2 : ℝ) • hermitianBlockRight (ι := ι) (κ := κ)
          (p.1 : EuclideanSpace ℂ (Sum ι κ)) := by
    rw [← hrec]
    exact hermitianBlockRight_real_smul
      (ι := ι) (κ := κ) (p.2 : ℝ)
      (p.1 : EuclideanSpace ℂ (Sum ι κ))
  have hleftprod :
      hermitianBlockNormalize
        (hermitianBlockLeft (ι := ι) (κ := κ) x) ∈ leftSet := by
    simpa [hermitianBlockSumEquivProd_fst] using hleft
  have hleftu :
      hermitianBlockLeftDirection (ι := ι) (κ := κ)
        (p.1 : EuclideanSpace ℂ (Sum ι κ)) ∈ leftSet := by
    rw [hleftx] at hleftprod
    rw [hermitianBlockNormalize_real_smul (η := ι) p.2.2] at hleftprod
    simpa [hermitianBlockLeftDirection, hermitianBlockNormalize] using hleftprod
  have hrightprod :
      hermitianBlockNormalize
        (hermitianBlockRight (ι := ι) (κ := κ) x) ∈ rightSet := by
    simpa [hermitianBlockSumEquivProd_snd] using hright
  have hrightu :
      hermitianBlockRightDirection (ι := ι) (κ := κ)
        (p.1 : EuclideanSpace ℂ (Sum ι κ)) ∈ rightSet := by
    rw [hrightx] at hrightprod
    rw [hermitianBlockNormalize_real_smul (η := κ) p.2.2] at hrightprod
    simpa [hermitianBlockRightDirection, hermitianBlockNormalize] using hrightprod
  rw [hermitianBlockRectCone]
  refine ⟨(p.2 : ℝ), ⟨p.2.2, hrlt⟩,
    (p.1 : EuclideanSpace ℂ (Sum ι κ)), ?_, ?_⟩
  · exact ⟨p.1, ⟨hmassu, hleftu, hrightu⟩, rfl⟩
  · exact hrec

/-- Away from the two block axes, the radial cone over a spherical rectangle
lies in the pullback of the product-coordinate cone. -/
theorem hermitianBlock_rectCone_diff_axes_subset_preimage_productCone
    (massSet : Set ℝ)
    (leftSet : Set (EuclideanSpace ℂ ι))
    (rightSet : Set (EuclideanSpace ℂ κ)) :
    hermitianBlockRectCone (ι := ι) (κ := κ)
        massSet leftSet rightSet \
          hermitianBlockAmbientAxes (ι := ι) (κ := κ) ⊆
      ((hermitianBlockSumEquivProd (ι := ι) (κ := κ)) ⁻¹'
        hermitianBlockProductCone (ι := ι) (κ := κ)
          massSet leftSet rightSet) := by
  rintro x ⟨hxcone, hxnotaxes⟩
  rcases hxcone with ⟨r, hr, y, hy, rfl⟩
  rcases hy with ⟨u, hu, rfl⟩
  rcases hu with ⟨hmassu, hleftu, hrightu⟩
  have hratio := hermitianBlock_product_ratio_real_smul_sphere
    (ι := ι) (κ := κ) u hr.1
  have hleft_smul :
      hermitianBlockLeft (ι := ι) (κ := κ)
          ((r : ℝ) • (u : EuclideanSpace ℂ (Sum ι κ))) =
        (r : ℝ) • hermitianBlockLeft (ι := ι) (κ := κ)
          (u : EuclideanSpace ℂ (Sum ι κ)) :=
    hermitianBlockLeft_real_smul (ι := ι) (κ := κ) r
      (u : EuclideanSpace ℂ (Sum ι κ))
  have hright_smul :
      hermitianBlockRight (ι := ι) (κ := κ)
          ((r : ℝ) • (u : EuclideanSpace ℂ (Sum ι κ))) =
        (r : ℝ) • hermitianBlockRight (ι := ι) (κ := κ)
          (u : EuclideanSpace ℂ (Sum ι κ)) :=
    hermitianBlockRight_real_smul (ι := ι) (κ := κ) r
      (u : EuclideanSpace ℂ (Sum ι κ))
  have hleftnorm :
      hermitianBlockNormalize
        (hermitianBlockLeft (ι := ι) (κ := κ)
          ((r : ℝ) • (u : EuclideanSpace ℂ (Sum ι κ)))) =
      hermitianBlockLeftDirection (ι := ι) (κ := κ)
        (u : EuclideanSpace ℂ (Sum ι κ)) := by
    rw [hleft_smul]
    rw [hermitianBlockNormalize_real_smul (η := ι) hr.1]
    rfl
  have hrightnorm :
      hermitianBlockNormalize
        (hermitianBlockRight (ι := ι) (κ := κ)
          ((r : ℝ) • (u : EuclideanSpace ℂ (Sum ι κ)))) =
      hermitianBlockRightDirection (ι := ι) (κ := κ)
        (u : EuclideanSpace ℂ (Sum ι κ)) := by
    rw [hright_smul]
    rw [hermitianBlockNormalize_real_smul (η := κ) hr.1]
    rfl
  have hnormsq :=
    norm_sq_real_smul_sphere (η := Sum ι κ) u ⟨r, hr.1⟩
  have hsum_lt :
      ‖hermitianBlockLeft (ι := ι) (κ := κ)
          ((r : ℝ) • (u : EuclideanSpace ℂ (Sum ι κ)))‖ ^ 2 +
        ‖hermitianBlockRight (ι := ι) (κ := κ)
          ((r : ℝ) • (u : EuclideanSpace ℂ (Sum ι κ)))‖ ^ 2 < 1 := by
    have hnormadd := hermitianBlock_norm_sq_eq_add
      (ι := ι) (κ := κ)
      ((r : ℝ) • (u : EuclideanSpace ℂ (Sum ι κ)))
    have hr2lt : r ^ 2 < 1 := by
      nlinarith [hr.1, hr.2]
    nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hxnotaxes
  · simpa [hermitianBlockSumEquivProd_fst, hermitianBlockSumEquivProd_snd]
      using hratio.symm ▸ hmassu
  · rw [hermitianBlockSumEquivProd_fst]
    rw [hleftnorm]
    exact hleftu
  · rw [hermitianBlockSumEquivProd_snd]
    rw [hrightnorm]
    exact hrightu
  · rw [hermitianBlockSumEquivProd_fst, hermitianBlockSumEquivProd_snd]
    exact hsum_lt

/-- Ambient cone equals the pullback of the product-coordinate cone up to the
two null axes. -/
theorem hermitianBlockRectCone_ae_eq_productCone
    [Nonempty ι] [Nonempty κ]
    (massSet : Set ℝ)
    (leftSet : Set (EuclideanSpace ℂ ι))
    (rightSet : Set (EuclideanSpace ℂ κ)) :
    (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ)))
      (hermitianBlockRectCone (ι := ι) (κ := κ) massSet leftSet rightSet) =
    (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ)))
      ((hermitianBlockSumEquivProd (ι := ι) (κ := κ)) ⁻¹'
        hermitianBlockProductCone (ι := ι) (κ := κ)
          massSet leftSet rightSet) := by
  let μ : Measure (EuclideanSpace ℂ (Sum ι κ)) := MeasureTheory.volume
  let A := hermitianBlockRectCone
    (ι := ι) (κ := κ) massSet leftSet rightSet
  let B := ((hermitianBlockSumEquivProd (ι := ι) (κ := κ)) ⁻¹'
    hermitianBlockProductCone (ι := ι) (κ := κ)
      massSet leftSet rightSet)
  let Z := hermitianBlockAmbientAxes (ι := ι) (κ := κ)
  have hBA : B ⊆ A := by
    simpa [A, B] using
      hermitianBlock_preimage_productCone_subset_rectCone
        (ι := ι) (κ := κ) massSet leftSet rightSet
  have hAZ : A ⊆ B ∪ Z := by
    intro x hxA
    by_cases hxZ : x ∈ Z
    · exact Or.inr hxZ
    · exact Or.inl
        ((hermitianBlock_rectCone_diff_axes_subset_preimage_productCone
          (ι := ι) (κ := κ) massSet leftSet rightSet) ⟨hxA, hxZ⟩)
  have hZ0 : μ Z = 0 := by
    simpa [μ, Z] using
      measure_hermitianBlockAmbientAxes_eq_zero
        (ι := ι) (κ := κ)
  apply le_antisymm
  · calc
      μ A ≤ μ (B ∪ Z) := measure_mono hAZ
      _ ≤ μ B + μ Z := measure_union_le B Z
      _ = μ B := by rw [hZ0, add_zero]
  · exact measure_mono hBA

/-- Final geometric identification of the ambient cone with the image of the
factorized polar set, after deleting the null axes. -/
theorem hermitianBlockRectCone_volume_eq_factorPolar_image
    [Nonempty ι] [Nonempty κ]
    (massSet : Set ℝ)
    (leftSet : Set (EuclideanSpace ℂ ι))
    (rightSet : Set (EuclideanSpace ℂ κ)) :
    (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ)))
      (hermitianBlockRectCone (ι := ι) (κ := κ) massSet leftSet rightSet) =
    (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ)))
      ((hermitianBlockSumEquivProd (ι := ι) (κ := κ)) ⁻¹'
        (hermitianBlockFactorPolarRecomposeProduct (ι := ι) (κ := κ) ''
          hermitianBlockFactorPolarSet (ι := ι) (κ := κ)
            massSet leftSet rightSet)) := by
  rw [hermitianBlockRectCone_ae_eq_productCone]
  rw [hermitianBlockProductCone_eq_factorPolar_image]

theorem measurableSet_hermitianBlockLeftSphereTrace
    {leftSet : Set (EuclideanSpace ℂ ι)}
    (hleft : MeasurableSet leftSet) :
    MeasurableSet (hermitianBlockLeftSphereTrace (ι := ι) leftSet) :=
  measurable_subtype_coe hleft

theorem measurableSet_hermitianBlockRightSphereTrace
    {rightSet : Set (EuclideanSpace ℂ κ)}
    (hright : MeasurableSet rightSet) :
    MeasurableSet (hermitianBlockRightSphereTrace (κ := κ) rightSet) :=
  measurable_subtype_coe hright

theorem measurableSet_hermitianBlockRadialMassSet
    {massSet : Set ℝ}
    (hmass : MeasurableSet massSet) :
    MeasurableSet (hermitianBlockRadialMassSet massSet) := by
  have hratio :
      Measurable (hermitianBlockRadialMassCoord) := by
    unfold hermitianBlockRadialMassCoord
    fun_prop
  have hsum :
      Measurable
        (fun r : Set.Ioi (0 : ℝ) × Set.Ioi (0 : ℝ) =>
          r.1.1 ^ 2 + r.2.1 ^ 2) := by
    fun_prop
  exact (hratio hmass).inter (measurableSet_lt hsum measurable_const)

theorem measurableSet_hermitianBlockFactorPolarSet
    {massSet : Set ℝ}
    {leftSet : Set (EuclideanSpace ℂ ι)}
    {rightSet : Set (EuclideanSpace ℂ κ)}
    (hmass : MeasurableSet massSet)
    (hleft : MeasurableSet leftSet)
    (hright : MeasurableSet rightSet) :
    MeasurableSet
      (hermitianBlockFactorPolarSet
        (ι := ι) (κ := κ) massSet leftSet rightSet) :=
  ((measurableSet_hermitianBlockLeftSphereTrace (ι := ι) hleft).prod
    (measurableSet_hermitianBlockRightSphereTrace (κ := κ) hright)).prod
      (measurableSet_hermitianBlockRadialMassSet hmass)

/-- The factorized polar measure: left direction, right direction, and the two
radial coordinates. -/
noncomputable def hermitianBlockFactorPolarMeasure :
    Measure ((Metric.sphere (0 : EuclideanSpace ℂ ι) 1 ×
        Metric.sphere (0 : EuclideanSpace ℂ κ) 1) ×
      (Set.Ioi (0 : ℝ) × Set.Ioi (0 : ℝ))) :=
  (((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere).prod
      ((MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)).toSphere)).prod
    ((MeasureTheory.Measure.volumeIoiPow
        (Module.finrank ℝ (EuclideanSpace ℂ ι) - 1)).prod
      (MeasureTheory.Measure.volumeIoiPow
        (Module.finrank ℝ (EuclideanSpace ℂ κ) - 1)))

/-- In the separated polar variables, the block-rectangular event factors into
left direction, right direction, and a scalar integral over `(r_E,r_F)`. -/
theorem hermitianBlockFactorPolarMeasure_rect
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere)]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)).toSphere)]
    {massSet : Set ℝ}
    {leftSet : Set (EuclideanSpace ℂ ι)}
    {rightSet : Set (EuclideanSpace ℂ κ)} :
    hermitianBlockFactorPolarMeasure (ι := ι) (κ := κ)
        (hermitianBlockFactorPolarSet
          (ι := ι) (κ := κ) massSet leftSet rightSet) =
      ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere
          (hermitianBlockLeftSphereTrace (ι := ι) leftSet) *
        (MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)).toSphere
          (hermitianBlockRightSphereTrace (κ := κ) rightSet)) *
        ((MeasureTheory.Measure.volumeIoiPow
            (Module.finrank ℝ (EuclideanSpace ℂ ι) - 1)).prod
          (MeasureTheory.Measure.volumeIoiPow
            (Module.finrank ℝ (EuclideanSpace ℂ κ) - 1)))
          (hermitianBlockRadialMassSet massSet) := by
  letI : SFinite
      (MeasureTheory.Measure.volumeIoiPow
        (Module.finrank ℝ (EuclideanSpace ℂ ι) - 1)) :=
    inferInstance
  letI : SFinite
      (MeasureTheory.Measure.volumeIoiPow
        (Module.finrank ℝ (EuclideanSpace ℂ κ) - 1)) :=
    inferInstance
  unfold hermitianBlockFactorPolarMeasure hermitianBlockFactorPolarSet
  rw [Measure.prod_prod, Measure.prod_prod]

noncomputable def hermitianBlockPuncturedProdVal :
    ({0}ᶜ : Set (EuclideanSpace ℂ ι)) ×
        ({0}ᶜ : Set (EuclideanSpace ℂ κ)) →
      EuclideanSpace ℂ ι × EuclideanSpace ℂ κ :=
  Prod.map Subtype.val Subtype.val

theorem measurableEmbedding_hermitianBlockPuncturedProdVal :
    MeasurableEmbedding (hermitianBlockPuncturedProdVal (ι := ι) (κ := κ)) := by
  let hsL : MeasurableSet ({0}ᶜ : Set (EuclideanSpace ℂ ι)) :=
    (measurableSet_singleton (0 : EuclideanSpace ℂ ι)).compl
  let hsR : MeasurableSet ({0}ᶜ : Set (EuclideanSpace ℂ κ)) :=
    (measurableSet_singleton (0 : EuclideanSpace ℂ κ)).compl
  simpa [hermitianBlockPuncturedProdVal] using
    (MeasurableEmbedding.subtype_coe hsL).prodMap
      (MeasurableEmbedding.subtype_coe hsR)

theorem hermitianBlockPuncturedProdMeasure_eq_comap :
    (((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).comap
        (Subtype.val : ({0}ᶜ : Set (EuclideanSpace ℂ ι)) →
          EuclideanSpace ℂ ι)).prod
      ((MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)).comap
        (Subtype.val : ({0}ᶜ : Set (EuclideanSpace ℂ κ)) →
          EuclideanSpace ℂ κ))) =
    (((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).prod
        (MeasureTheory.volume : Measure (EuclideanSpace ℂ κ))).comap
      (hermitianBlockPuncturedProdVal (ι := ι) (κ := κ))) := by
  let μL : Measure (EuclideanSpace ℂ ι) := MeasureTheory.volume
  let μR : Measure (EuclideanSpace ℂ κ) := MeasureTheory.volume
  let sL : Set (EuclideanSpace ℂ ι) := {0}ᶜ
  let sR : Set (EuclideanSpace ℂ κ) := {0}ᶜ
  let fL : sL → EuclideanSpace ℂ ι := Subtype.val
  let fR : sR → EuclideanSpace ℂ κ := Subtype.val
  let f : sL × sR → EuclideanSpace ℂ ι × EuclideanSpace ℂ κ :=
    hermitianBlockPuncturedProdVal (ι := ι) (κ := κ)
  have hsL : MeasurableSet sL := by
    exact (measurableSet_singleton (0 : EuclideanSpace ℂ ι)).compl
  have hsR : MeasurableSet sR := by
    exact (measurableSet_singleton (0 : EuclideanSpace ℂ κ)).compl
  let hEmbL : MeasurableEmbedding fL :=
    (MeasurableEmbedding.subtype_coe hsL :
      MeasurableEmbedding
        (Subtype.val : sL → EuclideanSpace ℂ ι))
  let hEmbR : MeasurableEmbedding fR :=
    (MeasurableEmbedding.subtype_coe hsR :
      MeasurableEmbedding
        (Subtype.val : sR → EuclideanSpace ℂ κ))
  have hEmbF : MeasurableEmbedding f := by
    simpa [f, fL, fR, hermitianBlockPuncturedProdVal] using
      hEmbL.prodMap hEmbR
  letI :
      SigmaFinite (μL.comap fL) := by
    refine SigmaFinite.of_map _ hEmbL.measurable.aemeasurable ?_
    rw [hEmbL.map_comap]
    infer_instance
  letI :
      SigmaFinite (μR.comap fR) := by
    refine SigmaFinite.of_map _ hEmbR.measurable.aemeasurable ?_
    rw [hEmbR.map_comap]
    infer_instance
  apply hEmbF.map_injective
  calc
    Measure.map f ((μL.comap fL).prod (μR.comap fR)) =
      (Measure.map fL (μL.comap fL)).prod
        (Measure.map fR (μR.comap fR)) := by
        simpa [f, fL, fR, hermitianBlockPuncturedProdVal] using
          (Measure.map_prod_map
            (μa := μL.comap fL) (μc := μR.comap fR)
            hEmbL.measurable hEmbR.measurable).symm
    _ = (μL.restrict sL).prod (μR.restrict sR) := by
        rw [hEmbL.map_comap, hEmbR.map_comap]
        congr 2 <;> ext x <;> simp [fL, fR, sL, sR]
    _ = (μL.prod μR).restrict (sL ×ˢ sR) := by
        rw [Measure.prod_restrict]
    _ = Measure.map f ((μL.prod μR).comap f) := by
        rw [hEmbF.map_comap]
        congr 1
        ext x
        simp [f, hermitianBlockPuncturedProdVal, sL, sR]
    _ = Measure.map f
        (((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).prod
          (MeasureTheory.volume : Measure (EuclideanSpace ℂ κ))).comap
          (hermitianBlockPuncturedProdVal (ι := ι) (κ := κ))) := by
        rfl

noncomputable def hermitianBlockFactorPolarPack :
    ((Metric.sphere (0 : EuclideanSpace ℂ ι) 1 × Set.Ioi (0 : ℝ)) ×
        (Metric.sphere (0 : EuclideanSpace ℂ κ) 1 × Set.Ioi (0 : ℝ))) →
      ((Metric.sphere (0 : EuclideanSpace ℂ ι) 1 ×
          Metric.sphere (0 : EuclideanSpace ℂ κ) 1) ×
        (Set.Ioi (0 : ℝ) × Set.Ioi (0 : ℝ))) :=
  fun z => ((z.1.1, z.2.1), (z.1.2, z.2.2))

theorem hermitianBlockFactorPolarPack_map_eq
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere)]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)).toSphere)] :
    Measure.map
        (hermitianBlockFactorPolarPack (ι := ι) (κ := κ))
        ((((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere).prod
            (MeasureTheory.Measure.volumeIoiPow
              (Module.finrank ℝ (EuclideanSpace ℂ ι) - 1))).prod
          (((MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)).toSphere).prod
            (MeasureTheory.Measure.volumeIoiPow
              (Module.finrank ℝ (EuclideanSpace ℂ κ) - 1)))) =
      hermitianBlockFactorPolarMeasure (ι := ι) (κ := κ) := by
  let μL : Measure (Metric.sphere (0 : EuclideanSpace ℂ ι) 1) :=
    (MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere
  let ρL : Measure (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.volumeIoiPow
      (Module.finrank ℝ (EuclideanSpace ℂ ι) - 1)
  let μR : Measure (Metric.sphere (0 : EuclideanSpace ℂ κ) 1) :=
    (MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)).toSphere
  let ρR : Measure (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.volumeIoiPow
      (Module.finrank ℝ (EuclideanSpace ℂ κ) - 1)
  let reorderSecond :
      Set.Ioi (0 : ℝ) × (Metric.sphere (0 : EuclideanSpace ℂ κ) 1 × Set.Ioi (0 : ℝ)) →
        Metric.sphere (0 : EuclideanSpace ℂ κ) 1 ×
          (Set.Ioi (0 : ℝ) × Set.Ioi (0 : ℝ)) :=
    fun x => (x.2.1, (x.1, x.2.2))
  have hReorderSecond :
      Measure.map reorderSecond (ρL.prod (μR.prod ρR)) =
        μR.prod (ρL.prod ρR) := by
    let swapLeft :
        Set.Ioi (0 : ℝ) × Metric.sphere (0 : EuclideanSpace ℂ κ) 1 →
          Metric.sphere (0 : EuclideanSpace ℂ κ) 1 × Set.Ioi (0 : ℝ) :=
      fun x => (x.2, x.1)
    have hswap :
        Measure.map swapLeft (ρL.prod μR) = μR.prod ρL := by
      simpa [swapLeft] using
        (MeasureTheory.Measure.prod_swap (μ := ρL) (ν := μR))
    have hreorder :
        reorderSecond =
          MeasurableEquiv.prodAssoc ∘
            Prod.map swapLeft (fun x : Set.Ioi (0 : ℝ) => x) ∘
              MeasurableEquiv.prodAssoc.symm := by
      funext x
      rfl
    calc
      Measure.map reorderSecond (ρL.prod (μR.prod ρR)) =
        Measure.map
          (MeasurableEquiv.prodAssoc ∘
            Prod.map swapLeft (fun x : Set.Ioi (0 : ℝ) => x) ∘
              MeasurableEquiv.prodAssoc.symm)
          (ρL.prod (μR.prod ρR)) := by
            rw [hreorder]
      _ =
        Measure.map
          (MeasurableEquiv.prodAssoc ∘
            Prod.map swapLeft (fun x : Set.Ioi (0 : ℝ) => x))
          (Measure.map MeasurableEquiv.prodAssoc.symm
            (ρL.prod (μR.prod ρR))) := by
              symm
              simpa [Function.comp] using
                (Measure.map_map
                  (μ := ρL.prod (μR.prod ρR))
                  (f := MeasurableEquiv.prodAssoc.symm)
                  (g := MeasurableEquiv.prodAssoc ∘
                    Prod.map swapLeft (fun x : Set.Ioi (0 : ℝ) => x))
                  (show Measurable
                      (MeasurableEquiv.prodAssoc ∘
                        Prod.map swapLeft (fun x : Set.Ioi (0 : ℝ) => x)) by
                    fun_prop)
                  (show Measurable MeasurableEquiv.prodAssoc.symm by
                    exact MeasurableEquiv.prodAssoc.symm.measurable))
      _ =
        Measure.map MeasurableEquiv.prodAssoc
          (Measure.map
            (Prod.map swapLeft (fun x : Set.Ioi (0 : ℝ) => x))
            (Measure.map MeasurableEquiv.prodAssoc.symm
              (ρL.prod (μR.prod ρR)))) := by
                symm
                simpa [Function.comp] using
                  (Measure.map_map
                    (μ := Measure.map MeasurableEquiv.prodAssoc.symm
                      (ρL.prod (μR.prod ρR)))
                    (f := Prod.map swapLeft (fun x : Set.Ioi (0 : ℝ) => x))
                    (g := MeasurableEquiv.prodAssoc)
                    (show Measurable MeasurableEquiv.prodAssoc by
                      exact MeasurableEquiv.prodAssoc.measurable)
                    (show Measurable
                        (Prod.map swapLeft (fun x : Set.Ioi (0 : ℝ) => x)) by
                      fun_prop))
      _ =
        Measure.map MeasurableEquiv.prodAssoc
          (Measure.map
            (Prod.map swapLeft (fun x : Set.Ioi (0 : ℝ) => x))
            ((ρL.prod μR).prod ρR)) := by
              rw [(MeasurePreserving.symm MeasurableEquiv.prodAssoc
                (MeasureTheory.measurePreserving_prodAssoc ρL μR ρR)).map_eq]
      _ =
        Measure.map MeasurableEquiv.prodAssoc
          ((Measure.map swapLeft (ρL.prod μR)).prod
            (Measure.map (fun x : Set.Ioi (0 : ℝ) => x) ρR)) := by
              congr 1
              simpa [Prod.map] using
                (Measure.map_prod_map
                  (ρL.prod μR) ρR
                  (show Measurable swapLeft by fun_prop)
                  measurable_id).symm
      _ = Measure.map MeasurableEquiv.prodAssoc
          ((μR.prod ρL).prod ρR) := by
            congr 1
            rw [hswap]
            simp
      _ = μR.prod (ρL.prod ρR) := by
            exact (MeasureTheory.measurePreserving_prodAssoc μR ρL ρR).map_eq
  have hPack :
      Measure.map
        (hermitianBlockFactorPolarPack (ι := ι) (κ := κ))
        ((μL.prod ρL).prod (μR.prod ρR)) =
      (μL.prod μR).prod (ρL.prod ρR) := by
    have hpack :
        hermitianBlockFactorPolarPack (ι := ι) (κ := κ) =
          MeasurableEquiv.prodAssoc.symm ∘
            Prod.map (fun x : Metric.sphere (0 : EuclideanSpace ℂ ι) 1 => x)
              reorderSecond ∘
                MeasurableEquiv.prodAssoc := by
      funext x
      rfl
    calc
      Measure.map
          (hermitianBlockFactorPolarPack (ι := ι) (κ := κ))
          ((μL.prod ρL).prod (μR.prod ρR)) =
        Measure.map
          (MeasurableEquiv.prodAssoc.symm ∘
            Prod.map (fun x : Metric.sphere (0 : EuclideanSpace ℂ ι) 1 => x)
              reorderSecond ∘
                MeasurableEquiv.prodAssoc)
          ((μL.prod ρL).prod (μR.prod ρR)) := by
            rw [hpack]
      _ =
        Measure.map
          (MeasurableEquiv.prodAssoc.symm ∘
            Prod.map (fun x : Metric.sphere (0 : EuclideanSpace ℂ ι) 1 => x)
              reorderSecond)
          (Measure.map MeasurableEquiv.prodAssoc
            ((μL.prod ρL).prod (μR.prod ρR))) := by
              symm
              simpa [Function.comp] using
                (Measure.map_map
                  (μ := ((μL.prod ρL).prod (μR.prod ρR)))
                  (f := MeasurableEquiv.prodAssoc)
                  (g := MeasurableEquiv.prodAssoc.symm ∘
                    Prod.map
                      (fun x : Metric.sphere (0 : EuclideanSpace ℂ ι) 1 => x)
                      reorderSecond)
                  (show Measurable
                      (MeasurableEquiv.prodAssoc.symm ∘
                        Prod.map
                          (fun x :
                            Metric.sphere (0 : EuclideanSpace ℂ ι) 1 => x)
                          reorderSecond) by
                    fun_prop)
                  (show Measurable MeasurableEquiv.prodAssoc by
                    exact MeasurableEquiv.prodAssoc.measurable))
      _ =
        Measure.map MeasurableEquiv.prodAssoc.symm
          (Measure.map
            (Prod.map
              (fun x : Metric.sphere (0 : EuclideanSpace ℂ ι) 1 => x)
              reorderSecond)
            (Measure.map MeasurableEquiv.prodAssoc
              ((μL.prod ρL).prod (μR.prod ρR)))) := by
                symm
                simpa [Function.comp] using
                  (Measure.map_map
                    (μ := Measure.map MeasurableEquiv.prodAssoc
                      ((μL.prod ρL).prod (μR.prod ρR)))
                    (f := Prod.map
                      (fun x : Metric.sphere (0 : EuclideanSpace ℂ ι) 1 => x)
                      reorderSecond)
                    (g := MeasurableEquiv.prodAssoc.symm)
                    (show Measurable MeasurableEquiv.prodAssoc.symm by
                      exact MeasurableEquiv.prodAssoc.symm.measurable)
                    (show Measurable
                        (Prod.map
                          (fun x :
                            Metric.sphere (0 : EuclideanSpace ℂ ι) 1 => x)
                          reorderSecond) by
                      fun_prop))
      _ =
        Measure.map MeasurableEquiv.prodAssoc.symm
          (Measure.map
            (Prod.map
              (fun x : Metric.sphere (0 : EuclideanSpace ℂ ι) 1 => x)
              reorderSecond)
            (μL.prod (ρL.prod (μR.prod ρR)))) := by
              rw [(MeasureTheory.measurePreserving_prodAssoc μL ρL
                (μR.prod ρR)).map_eq]
      _ =
        Measure.map MeasurableEquiv.prodAssoc.symm
          ((Measure.map
              (fun x : Metric.sphere (0 : EuclideanSpace ℂ ι) 1 => x) μL).prod
            (Measure.map reorderSecond (ρL.prod (μR.prod ρR)))) := by
              congr 1
              simpa [Prod.map] using
                (Measure.map_prod_map
                  μL (ρL.prod (μR.prod ρR))
                  measurable_id
                  (show Measurable reorderSecond by
                    dsimp [reorderSecond]
                    fun_prop)).symm
      _ =
        Measure.map MeasurableEquiv.prodAssoc.symm
          (μL.prod (μR.prod (ρL.prod ρR))) := by
            congr 1
            simp [hReorderSecond]
      _ = (μL.prod μR).prod (ρL.prod ρR) := by
            exact (MeasurePreserving.symm MeasurableEquiv.prodAssoc
              (MeasureTheory.measurePreserving_prodAssoc μL μR
                (ρL.prod ρR))).map_eq
  simpa [hermitianBlockFactorPolarMeasure, μL, ρL, μR, ρR] using hPack

theorem hermitianBlockFactorPolarPack_comp_preimage_eq_productCone
    (massSet : Set ℝ)
    (leftSet : Set (EuclideanSpace ℂ ι))
    (rightSet : Set (EuclideanSpace ℂ κ)) :
    ((fun x =>
        hermitianBlockFactorPolarPack (ι := ι) (κ := κ)
          (hermitianBlockSeparatePolarMap (ι := ι) (κ := κ) x)) ⁻¹'
        hermitianBlockFactorPolarSet (ι := ι) (κ := κ)
          massSet leftSet rightSet) =
      (hermitianBlockPuncturedProdVal (ι := ι) (κ := κ)) ⁻¹'
        hermitianBlockProductCone (ι := ι) (κ := κ)
          massSet leftSet rightSet := by
  ext x
  rcases x with ⟨xL, xR⟩
  let pL := homeomorphUnitSphereProd (EuclideanSpace ℂ ι) xL
  let pR := homeomorphUnitSphereProd (EuclideanSpace ℂ κ) xR
  have hpL_norm :
      (pL.2 : ℝ) = ‖(xL : EuclideanSpace ℂ ι)‖ := by
    simpa [pL] using
      homeomorphUnitSphereProd_snd_eq_norm (η := ι) xL
  have hpR_norm :
      (pR.2 : ℝ) = ‖(xR : EuclideanSpace ℂ κ)‖ := by
    simpa [pR] using
      homeomorphUnitSphereProd_snd_eq_norm (η := κ) xR
  have hpL_dir :
      (pL.1 : EuclideanSpace ℂ ι) =
        hermitianBlockNormalize (xL : EuclideanSpace ℂ ι) := by
    simpa [pL] using
      homeomorphUnitSphereProd_fst_eq_hermitianBlockNormalize
        (η := ι) xL
  have hpR_dir :
      (pR.1 : EuclideanSpace ℂ κ) =
        hermitianBlockNormalize (xR : EuclideanSpace ℂ κ) := by
    simpa [pR] using
      homeomorphUnitSphereProd_fst_eq_hermitianBlockNormalize
        (η := κ) xR
  have hxL_ne : (xL : EuclideanSpace ℂ ι) ≠ 0 := by
    exact xL.2
  have hxR_ne : (xR : EuclideanSpace ℂ κ) ≠ 0 := by
    exact xR.2
  constructor
  · intro h
    rcases h with ⟨⟨hleft, hright⟩, hmass, hball⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [hermitianBlockPuncturedProdVal, hermitianBlockProductAxes,
        hxL_ne, hxR_ne]
    · simpa [hermitianBlockPuncturedProdVal, hermitianBlockSeparatePolarMap,
        hermitianBlockFactorPolarPack, hermitianBlockFactorPolarSet,
        hermitianBlockRadialMassSet, hermitianBlockRadialMassCoord,
        pL, pR, hpL_norm, hpR_norm] using hmass
    · have hleft' : (pL.1 : EuclideanSpace ℂ ι) ∈ leftSet := by
        simpa [hermitianBlockLeftSphereTrace] using hleft
      simpa [hpL_dir] using hleft'
    · have hright' : (pR.1 : EuclideanSpace ℂ κ) ∈ rightSet := by
        simpa [hermitianBlockRightSphereTrace] using hright
      simpa [hpR_dir] using hright'
    · simpa [hermitianBlockPuncturedProdVal, hermitianBlockSeparatePolarMap,
        hermitianBlockFactorPolarPack, hermitianBlockFactorPolarSet,
        hermitianBlockRadialMassSet, hermitianBlockRadialBallSet,
        pL, pR, hpL_norm, hpR_norm] using hball
  · intro h
    rcases h with ⟨haxes, hmass, hleft, hright, hball⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · have hleft' : (pL.1 : EuclideanSpace ℂ ι) ∈ leftSet := by
        simpa [hpL_dir] using hleft
      simpa [hermitianBlockLeftSphereTrace] using hleft'
    · have hright' : (pR.1 : EuclideanSpace ℂ κ) ∈ rightSet := by
        simpa [hpR_dir] using hright
      simpa [hermitianBlockRightSphereTrace] using hright'
    · simpa [hermitianBlockPuncturedProdVal, hermitianBlockSeparatePolarMap,
        hermitianBlockFactorPolarPack, hermitianBlockFactorPolarSet,
        hermitianBlockRadialMassSet, hermitianBlockRadialMassCoord,
        pL, pR, hpL_norm, hpR_norm] using hmass
    · simpa [hermitianBlockPuncturedProdVal, hermitianBlockSeparatePolarMap,
        hermitianBlockFactorPolarPack, hermitianBlockFactorPolarSet,
        hermitianBlockRadialMassSet, hermitianBlockRadialBallSet,
        pL, pR, hpL_norm, hpR_norm] using hball

theorem hermitianBlockProductCone_subset_range_puncturedProdVal
    (massSet : Set ℝ)
    (leftSet : Set (EuclideanSpace ℂ ι))
    (rightSet : Set (EuclideanSpace ℂ κ)) :
    hermitianBlockProductCone (ι := ι) (κ := κ)
        massSet leftSet rightSet ⊆
      Set.range (hermitianBlockPuncturedProdVal (ι := ι) (κ := κ)) := by
  intro x hx
  refine ⟨(⟨x.1, ?_⟩, ⟨x.2, ?_⟩), rfl⟩
  · intro hzero
    exact hx.1 (Or.inl hzero)
  · intro hzero
    exact hx.1 (Or.inr hzero)

theorem measure_prod_hermitianBlockProductCone_eq_factorPolarMeasure
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere)]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)).toSphere)]
    {massSet : Set ℝ}
    {leftSet : Set (EuclideanSpace ℂ ι)}
    {rightSet : Set (EuclideanSpace ℂ κ)}
    (hmass : MeasurableSet massSet)
    (hleft : MeasurableSet leftSet)
    (hright : MeasurableSet rightSet) :
    ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).prod
        (MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)))
      (hermitianBlockProductCone (ι := ι) (κ := κ)
        massSet leftSet rightSet) =
    hermitianBlockFactorPolarMeasure (ι := ι) (κ := κ)
      (hermitianBlockFactorPolarSet (ι := ι) (κ := κ)
        massSet leftSet rightSet) := by
  let μprod : Measure (EuclideanSpace ℂ ι × EuclideanSpace ℂ κ) :=
    (MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).prod
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ κ))
  let μpunc :
      Measure
        (({0}ᶜ : Set (EuclideanSpace ℂ ι)) ×
          ({0}ᶜ : Set (EuclideanSpace ℂ κ))) :=
    (((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).comap
        (Subtype.val : ({0}ᶜ : Set (EuclideanSpace ℂ ι)) →
          EuclideanSpace ℂ ι)).prod
      ((MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)).comap
        (Subtype.val : ({0}ᶜ : Set (EuclideanSpace ℂ κ)) →
          EuclideanSpace ℂ κ)))
  let packPreimage :
      Set ((Metric.sphere (0 : EuclideanSpace ℂ ι) 1 × Set.Ioi (0 : ℝ)) ×
          (Metric.sphere (0 : EuclideanSpace ℂ κ) 1 × Set.Ioi (0 : ℝ))) :=
    (hermitianBlockFactorPolarPack (ι := ι) (κ := κ)) ⁻¹'
      hermitianBlockFactorPolarSet (ι := ι) (κ := κ)
        massSet leftSet rightSet
  let hsL : MeasurableSet ({0}ᶜ : Set (EuclideanSpace ℂ ι)) :=
    (measurableSet_singleton (0 : EuclideanSpace ℂ ι)).compl
  let hsR : MeasurableSet ({0}ᶜ : Set (EuclideanSpace ℂ κ)) :=
    (measurableSet_singleton (0 : EuclideanSpace ℂ κ)).compl
  let hEmbL :=
    (MeasurableEmbedding.subtype_coe hsL :
      MeasurableEmbedding
        (Subtype.val : ({0}ᶜ : Set (EuclideanSpace ℂ ι)) →
          EuclideanSpace ℂ ι))
  let hEmbR :=
    (MeasurableEmbedding.subtype_coe hsR :
      MeasurableEmbedding
        (Subtype.val : ({0}ᶜ : Set (EuclideanSpace ℂ κ)) →
          EuclideanSpace ℂ κ))
  letI :
      SigmaFinite
        ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).comap
          (Subtype.val : ({0}ᶜ : Set (EuclideanSpace ℂ ι)) →
            EuclideanSpace ℂ ι)) := by
    refine SigmaFinite.of_map _ measurable_subtype_coe.aemeasurable ?_
    rw [hEmbL.map_comap]
    infer_instance
  letI :
      SigmaFinite
        ((MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)).comap
          (Subtype.val : ({0}ᶜ : Set (EuclideanSpace ℂ κ)) →
            EuclideanSpace ℂ κ)) := by
    refine SigmaFinite.of_map _ measurable_subtype_coe.aemeasurable ?_
    rw [hEmbR.map_comap]
    infer_instance
  have hmeasFactor :
      MeasurableSet
        (hermitianBlockFactorPolarSet
          (ι := ι) (κ := κ) massSet leftSet rightSet) :=
    measurableSet_hermitianBlockFactorPolarSet
      (ι := ι) (κ := κ) hmass hleft hright
  have hmeasPackPreimage : MeasurableSet packPreimage := by
    exact (show Measurable (hermitianBlockFactorPolarPack (ι := ι) (κ := κ)) by
      fun_prop) hmeasFactor
  calc
    μprod
        (hermitianBlockProductCone (ι := ι) (κ := κ)
          massSet leftSet rightSet) =
      (μprod.comap (hermitianBlockPuncturedProdVal (ι := ι) (κ := κ)))
        ((hermitianBlockPuncturedProdVal (ι := ι) (κ := κ)) ⁻¹'
          hermitianBlockProductCone (ι := ι) (κ := κ)
            massSet leftSet rightSet) := by
          rw [(measurableEmbedding_hermitianBlockPuncturedProdVal
            (ι := ι) (κ := κ)).comap_apply μprod]
          rw [Set.image_preimage_eq_inter_range,
            Set.inter_eq_left.2
              (hermitianBlockProductCone_subset_range_puncturedProdVal
                (ι := ι) (κ := κ) massSet leftSet rightSet)]
    _ = μpunc
        ((hermitianBlockPuncturedProdVal (ι := ι) (κ := κ)) ⁻¹'
          hermitianBlockProductCone (ι := ι) (κ := κ)
            massSet leftSet rightSet) := by
          rw [← hermitianBlockPuncturedProdMeasure_eq_comap
            (ι := ι) (κ := κ)]
    _ = μpunc
        (((fun x =>
            hermitianBlockFactorPolarPack (ι := ι) (κ := κ)
              (hermitianBlockSeparatePolarMap (ι := ι) (κ := κ) x)) ⁻¹'
            hermitianBlockFactorPolarSet (ι := ι) (κ := κ)
              massSet leftSet rightSet)) := by
          rw [hermitianBlockFactorPolarPack_comp_preimage_eq_productCone
            (ι := ι) (κ := κ) massSet leftSet rightSet]
    _ =
      Measure.map
          (hermitianBlockSeparatePolarMap (ι := ι) (κ := κ))
          μpunc
          packPreimage := by
          change
            μpunc
              ((hermitianBlockSeparatePolarMap (ι := ι) (κ := κ)) ⁻¹'
                packPreimage) =
              Measure.map
                (hermitianBlockSeparatePolarMap (ι := ι) (κ := κ))
                μpunc packPreimage
          rw [← Measure.map_apply
            (measurePreserving_hermitianBlockSeparatePolarMap
              (ι := ι) (κ := κ)).measurable
            hmeasPackPreimage]
    _ =
      ((((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere).prod
          (MeasureTheory.Measure.volumeIoiPow
            (Module.finrank ℝ (EuclideanSpace ℂ ι) - 1))).prod
        (((MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)).toSphere).prod
          (MeasureTheory.Measure.volumeIoiPow
            (Module.finrank ℝ (EuclideanSpace ℂ κ) - 1))))
        packPreimage := by
          simpa [μpunc] using
            congrArg
              (fun ν :
                Measure
                  ((Metric.sphere (0 : EuclideanSpace ℂ ι) 1 ×
                      Set.Ioi (0 : ℝ)) ×
                    (Metric.sphere (0 : EuclideanSpace ℂ κ) 1 ×
                      Set.Ioi (0 : ℝ))) =>
                ν packPreimage)
              ((measurePreserving_hermitianBlockSeparatePolarMap
                (ι := ι) (κ := κ)).map_eq)
    _ =
      hermitianBlockFactorPolarMeasure (ι := ι) (κ := κ)
        (hermitianBlockFactorPolarSet
          (ι := ι) (κ := κ) massSet leftSet rightSet) := by
          rw [← Measure.map_apply
            (show Measurable
                (hermitianBlockFactorPolarPack (ι := ι) (κ := κ)) by
              fun_prop)
            hmeasFactor]
          rw [hermitianBlockFactorPolarPack_map_eq (ι := ι) (κ := κ)]

/-! ### Scalar beta calculation for the separated block radii -/

/-- The canonical Beta law for the squared mass of the left block in a complex
Hermitian two-block decomposition. -/
noncomputable def hermitianBlockMassBetaMeasure : Measure ℝ :=
  ProbabilityTheory.betaMeasure
    ((Fintype.card ι : ℕ) : ℝ) ((Fintype.card κ : ℕ) : ℝ)

/-- Real shape parameter of the left complex block. -/
noncomputable def hermitianBlockBetaLeftShape : ℝ :=
  (Fintype.card ι : ℝ)

/-- Real shape parameter of the right complex block. -/
noncomputable def hermitianBlockBetaRightShape : ℝ :=
  (Fintype.card κ : ℝ)

/-- Product radial measure obtained after applying polar coordinates separately
on the two blocks. -/
noncomputable def hermitianBlockRadialProductMeasure :
    Measure (Set.Ioi (0 : ℝ) × Set.Ioi (0 : ℝ)) :=
  (MeasureTheory.Measure.volumeIoiPow
      (Module.finrank ℝ (EuclideanSpace ℂ ι) - 1)).prod
    (MeasureTheory.Measure.volumeIoiPow
      (Module.finrank ℝ (EuclideanSpace ℂ κ) - 1))

/-- Total scalar radial normalization of the block cone. -/
noncomputable def hermitianBlockRadialNormalization : ℝ≥0∞ :=
  hermitianBlockRadialProductMeasure (ι := ι) (κ := κ)
    (hermitianBlockRadialBallSet)

/-- Push-forward of the scalar cone measure by
`t = r_E^2 / (r_E^2 + r_F^2)`.

After the change of variables to total radius and mass fraction, this is the
unnormalized Beta law for the left block mass. -/
noncomputable def hermitianBlockRadialMassMeasure : Measure ℝ :=
  Measure.map hermitianBlockRadialMassCoord
    ((hermitianBlockRadialProductMeasure (ι := ι) (κ := κ)).restrict
      hermitianBlockRadialBallSet)

theorem measurable_hermitianBlockRadialMassCoord :
    Measurable (hermitianBlockRadialMassCoord) := by
  unfold hermitianBlockRadialMassCoord
  fun_prop

theorem measurableSet_hermitianBlockRadialBallSet :
    MeasurableSet
      (hermitianBlockRadialBallSet :
        Set (Set.Ioi (0 : ℝ) × Set.Ioi (0 : ℝ))) := by
  unfold hermitianBlockRadialBallSet
  exact measurableSet_lt (by fun_prop) measurable_const

/-- Integral-of-cone form: measuring `massSet` under the scalar mass
push-forward is exactly measuring the radial cone slice. -/
theorem hermitianBlockRadialMassMeasure_apply
    {massSet : Set ℝ}
    (hmass : MeasurableSet massSet) :
    hermitianBlockRadialMassMeasure (ι := ι) (κ := κ) massSet =
      hermitianBlockRadialProductMeasure (ι := ι) (κ := κ)
        (hermitianBlockRadialMassSet massSet) := by
  rw [hermitianBlockRadialMassMeasure]
  rw [Measure.map_apply measurable_hermitianBlockRadialMassCoord hmass]
  rw [Measure.restrict_apply'
    (μ := hermitianBlockRadialProductMeasure (ι := ι) (κ := κ))
    (s := hermitianBlockRadialBallSet)
    (t := hermitianBlockRadialMassCoord ⁻¹' massSet)
    measurableSet_hermitianBlockRadialBallSet]
  congr 1

/-- The scalar density appearing after the change of variables
`t = r_E^2 / (r_E^2 + r_F^2)`: up to the normalizing Beta constant it is
`t^(card ι - 1) * (1-t)^(card κ - 1)` on `(0,1)`. -/
noncomputable def hermitianBlockScalarBetaDensity (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (if 0 < t ∧ t < 1 then
      t ^ (hermitianBlockBetaLeftShape (ι := ι) - 1) *
        (1 - t) ^ (hermitianBlockBetaRightShape (κ := κ) - 1)
    else
      0)

theorem hermitianBlockMassBetaPDF_of_pos_lt_one
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ProbabilityTheory.betaPDF
        (hermitianBlockBetaLeftShape (ι := ι))
        (hermitianBlockBetaRightShape (κ := κ)) t =
      ENNReal.ofReal
        ((1 / ProbabilityTheory.beta
            (hermitianBlockBetaLeftShape (ι := ι))
            (hermitianBlockBetaRightShape (κ := κ))) *
          t ^ (hermitianBlockBetaLeftShape (ι := ι) - 1) *
          (1 - t) ^ (hermitianBlockBetaRightShape (κ := κ) - 1)) := by
  exact ProbabilityTheory.betaPDF_of_pos_lt_one ht0 ht1

/- The radial mass normalization lemmas are proved later, once the spherical
mass law has been transported from the Gaussian model. -/

set_option linter.unusedSectionVars false in
/-- The canonical Hermitian block mass Beta law is a probability measure when
both blocks are nonempty. -/
theorem hermitianBlockMassBetaMeasure_isProbabilityMeasure
    [Nonempty ι] [Nonempty κ] :
    IsProbabilityMeasure
      (hermitianBlockMassBetaMeasure (ι := ι) (κ := κ)) := by
  unfold hermitianBlockMassBetaMeasure
  exact ProbabilityTheory.isProbabilityMeasureBeta
    (by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι))
    (by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card κ))

/-- Ratio-of-Gammas to Beta, in the integer-shape case needed for complex
Hermitian block masses.

If `S ~ Gamma(m,1)` and `T ~ Gamma(n,1)` are independent, then

`S / (S + T) ~ Beta(m,n)`.

This is the scalar analytic step behind the Gaussian block mass law. -/
noncomputable def gammaRatioMap (p : ℝ × ℝ) : ℝ :=
  p.1 / (p.1 + p.2)

noncomputable def gammaRatioChange (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 * p.2, (1 - p.1) * p.2)

def gammaRatioChangeDomain : Set (ℝ × ℝ) :=
  Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioi (0 : ℝ)

def gammaRatioPositiveQuadrant : Set (ℝ × ℝ) :=
  Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)

noncomputable def fderivGammaRatioChange (p : ℝ × ℝ) :
    ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![p.2, p.1; -p.2, 1 - p.1]).toContinuousLinearMap

theorem measurable_gammaRatioMap :
    Measurable gammaRatioMap := by
  unfold gammaRatioMap
  fun_prop

theorem measurable_gammaRatioChange :
    Measurable gammaRatioChange := by
  unfold gammaRatioChange
  fun_prop

theorem measurableSet_gammaRatioChangeDomain :
    MeasurableSet gammaRatioChangeDomain := by
  unfold gammaRatioChangeDomain
  exact measurableSet_Ioo.prod measurableSet_Ioi

theorem measurableSet_gammaRatioPositiveQuadrant :
    MeasurableSet gammaRatioPositiveQuadrant := by
  unfold gammaRatioPositiveQuadrant
  exact measurableSet_Ioi.prod measurableSet_Ioi

theorem hasFDerivAt_gammaRatioChange (p : ℝ × ℝ) :
    HasFDerivAt gammaRatioChange (fderivGammaRatioChange p) p := by
  unfold fderivGammaRatioChange gammaRatioChange
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  have hf1 : HasFDerivAt (fun q : ℝ × ℝ => q.1 * q.2)
      (p.1 • (ContinuousLinearMap.snd ℝ ℝ ℝ) +
        p.2 • (ContinuousLinearMap.fst ℝ ℝ ℝ)) p := by
    have hf : HasFDerivAt (fun q : ℝ × ℝ => q.1)
        (ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
      hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := p)
    have hg : HasFDerivAt (fun q : ℝ × ℝ => q.2)
        (ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
      hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := p)
    simpa using hf.mul hg
  have hf2_left : HasFDerivAt (fun q : ℝ × ℝ => 1 - q.1)
      (-(ContinuousLinearMap.fst ℝ ℝ ℝ)) p := by
    have hf : HasFDerivAt (fun q : ℝ × ℝ => q.1)
        (ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
      hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := p)
    simpa using hf.const_sub (1 : ℝ)
  have hf2 : HasFDerivAt (fun q : ℝ × ℝ => (1 - q.1) * q.2)
      ((1 - p.1) • (ContinuousLinearMap.snd ℝ ℝ ℝ) +
        p.2 • (-(ContinuousLinearMap.fst ℝ ℝ ℝ))) p := by
    have hg : HasFDerivAt (fun q : ℝ × ℝ => q.2)
        (ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
      hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := p)
    simpa using hf2_left.mul hg
  convert HasFDerivAt.prodMk (𝕜 := ℝ) hf1 hf2 using 2
  · module
  · rw [smul_neg]
    module

theorem det_fderivGammaRatioChange (p : ℝ × ℝ) :
    (fderivGammaRatioChange p).det = p.2 := by
  unfold fderivGammaRatioChange
  simp only [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
    Matrix.det_fin_two_of]
  ring

theorem gammaRatioChange_image_domain :
    gammaRatioChange '' gammaRatioChangeDomain =
      gammaRatioPositiveQuadrant := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨⟨hu0, hu1⟩, hv0⟩
    constructor
    · exact mul_pos hu0 hv0
    · exact mul_pos (sub_pos.mpr hu1) hv0
  · intro hy
    rcases hy with ⟨hy1mem, hy2mem⟩
    have hy1 : 0 < y.1 := by simpa using hy1mem
    have hy2 : 0 < y.2 := by simpa using hy2mem
    let v : ℝ := y.1 + y.2
    let u : ℝ := y.1 / v
    have hv0 : 0 < v := by
      dsimp [v]
      linarith
    have hu0 : 0 < u := by
      dsimp [u]
      exact div_pos hy1 hv0
    have hu1 : u < 1 := by
      dsimp [u, v]
      rw [div_lt_one hv0]
      linarith
    refine ⟨(u, v), ?_, ?_⟩
    · exact ⟨⟨hu0, hu1⟩, hv0⟩
    · ext <;> dsimp [gammaRatioChange, u, v]
      · field_simp [ne_of_gt hv0]
      · field_simp [ne_of_gt hv0]
        ring_nf

theorem gammaRatioChange_injOn_domain :
    Set.InjOn gammaRatioChange gammaRatioChangeDomain := by
  intro x hx y hy hxy
  rcases hx with ⟨⟨_hx0, _hx1⟩, hxv0⟩
  rcases hy with ⟨⟨_hy0, _hy1⟩, hyv0⟩
  have hsumx : (gammaRatioChange x).1 + (gammaRatioChange x).2 = x.2 := by
    dsimp [gammaRatioChange]
    ring
  have hsumy : (gammaRatioChange y).1 + (gammaRatioChange y).2 = y.2 := by
    dsimp [gammaRatioChange]
    ring
  have hv : x.2 = y.2 := by
    rw [← hsumx, hxy, hsumy]
  have hu : x.1 = y.1 := by
    have h1 : x.1 * x.2 = y.1 * y.2 := congrArg Prod.fst hxy
    rw [hv] at h1
    rw [mul_comm x.1 y.2, mul_comm y.1 y.2] at h1
    exact (mul_right_inj' (ne_of_gt hyv0)).mp h1
  exact Prod.ext hu hv

theorem gammaRatioChange_map_jacobian :
    Measure.map gammaRatioChange
      (((volume : Measure (ℝ × ℝ)).restrict gammaRatioChangeDomain).withDensity
        fun x => ENNReal.ofReal |(fderivGammaRatioChange x).det|) =
      (volume : Measure (ℝ × ℝ)).restrict gammaRatioPositiveQuadrant := by
  rw [← gammaRatioChange_image_domain]
  exact map_withDensity_abs_det_fderiv_eq_addHaar
    (μ := (volume : Measure (ℝ × ℝ)))
    (s := gammaRatioChangeDomain)
    (f := gammaRatioChange)
    (f' := fderivGammaRatioChange)
    measurableSet_gammaRatioChangeDomain.nullMeasurableSet
    (fun x hx =>
      (hasFDerivAt_gammaRatioChange x).hasFDerivWithinAt)
    gammaRatioChange_injOn_domain

lemma map_withDensity_comp_eq_withDensity_map
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {f : α → β} {g : β → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    Measure.map f (μ.withDensity fun x => g (f x)) =
      (Measure.map f μ).withDensity g := by
  ext s hs
  rw [Measure.map_apply hf hs]
  rw [withDensity_apply _ (hf hs)]
  rw [withDensity_apply _ hs]
  rw [← lintegral_indicator (μ := μ) (s := f ⁻¹' s)
    (f := fun a => g (f a)) (hf hs)]
  rw [← lintegral_indicator (μ := Measure.map f μ) (s := s) (f := g) hs]
  rw [lintegral_map (hg.indicator hs) hf]
  rfl

lemma gammaPDFReal_nat_one_of_pos {m : ℕ} (hm : 0 < m)
    {x : ℝ} (hx : 0 < x) :
    ProbabilityTheory.gammaPDFReal (m : ℝ) 1 x =
      (1 / Real.Gamma (m : ℝ)) *
        x ^ ((m - 1 : ℕ)) * Real.exp (-x) := by
    rw [ProbabilityTheory.gammaPDFReal, if_pos hx.le]
    have hmcast : (m : ℝ) - 1 = ((m - 1 : ℕ) : ℝ) := by
      have hsucc : (((m - 1 : ℕ) + 1 : ℕ) : ℝ) = (m : ℝ) := by
        exact_mod_cast (Nat.succ_pred_eq_of_pos hm)
      norm_num at hsucc ⊢
      linarith
    rw [hmcast]
    simp [Real.rpow_natCast]

lemma betaPDFReal_nat_of_pos_lt_one {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    ProbabilityTheory.betaPDFReal (m : ℝ) (n : ℝ) u =
      (1 / ProbabilityTheory.beta (m : ℝ) (n : ℝ)) *
        u ^ ((m - 1 : ℕ)) * (1 - u) ^ ((n - 1 : ℕ)) := by
    rw [ProbabilityTheory.betaPDFReal, if_pos ⟨hu0, hu1⟩]
    have hmcast : (m : ℝ) - 1 = ((m - 1 : ℕ) : ℝ) := by
      have hsucc : (((m - 1 : ℕ) + 1 : ℕ) : ℝ) = (m : ℝ) := by
        exact_mod_cast (Nat.succ_pred_eq_of_pos hm)
      norm_num at hsucc ⊢
      linarith
    have hncast : (n : ℝ) - 1 = ((n - 1 : ℕ) : ℝ) := by
      have hsucc : (((n - 1 : ℕ) + 1 : ℕ) : ℝ) = (n : ℝ) := by
        exact_mod_cast (Nat.succ_pred_eq_of_pos hn)
      norm_num at hsucc ⊢
      linarith
    rw [hmcast, hncast]
    simp [Real.rpow_natCast]

lemma gamma_beta_density_identity_real {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {u v : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hv : 0 < v) :
    ProbabilityTheory.gammaPDFReal (m : ℝ) 1 (u * v) *
        ProbabilityTheory.gammaPDFReal (n : ℝ) 1 ((1 - u) * v) * v =
      ProbabilityTheory.betaPDFReal (m : ℝ) (n : ℝ) u *
        ProbabilityTheory.gammaPDFReal ((m + n : ℕ) : ℝ) 1 v := by
  have h1u : 0 < 1 - u := sub_pos.mpr hu1
  have huv : 0 < u * v := mul_pos hu0 hv
  have h1uv : 0 < (1 - u) * v := mul_pos h1u hv
  have hmn : 0 < m + n := Nat.add_pos_left hm n
  rw [gammaPDFReal_nat_one_of_pos hm huv,
    gammaPDFReal_nat_one_of_pos hn h1uv,
    gammaPDFReal_nat_one_of_pos hmn hv,
    betaPDFReal_nat_of_pos_lt_one hm hn hu0 hu1]
  have hbeta :
      ProbabilityTheory.beta (m : ℝ) (n : ℝ) =
        Real.Gamma (m : ℝ) * Real.Gamma (n : ℝ) /
          Real.Gamma ((m + n : ℕ) : ℝ) := by
    simp [ProbabilityTheory.beta, Nat.cast_add]
  rw [hbeta]
  have hgm : Real.Gamma (m : ℝ) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by exact_mod_cast hm)).ne'
  have hgn : Real.Gamma (n : ℝ) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by exact_mod_cast hn)).ne'
  have hgs : Real.Gamma ((m + n : ℕ) : ℝ) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by exact_mod_cast hmn)).ne'
  have hexp :
      Real.exp (-(u * v)) *
          Real.exp (-((1 - u) * v)) =
        Real.exp (-v) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hpow1 :
      (u * v) ^ (m - 1) =
        u ^ (m - 1) * v ^ (m - 1) := by
    exact mul_pow u v (m - 1)
  have hpow2 :
      ((1 - u) * v) ^ (n - 1) =
        (1 - u) ^ (n - 1) * v ^ (n - 1) := by
    exact mul_pow (1 - u) v (n - 1)
  rw [hpow1, hpow2]
  have hpowv :
      v ^ (m - 1) * v ^ (n - 1) * v =
        v ^ (m + n - 1) := by
    rw [← pow_add]
    have hs : (m - 1) + (n - 1) + 1 = m + n - 1 := by
      omega
    rw [← pow_succ, hs]
  field_simp [hgm, hgn, hgs]
  ring_nf
  have hpowv' :
      v * v ^ (m - 1) * v ^ (n - 1) =
        v ^ (m + n - 1) := by
    calc
      v * v ^ (m - 1) * v ^ (n - 1) =
          v ^ (m - 1) * v ^ (n - 1) * v := by ring
      _ = v ^ (m + n - 1) := hpowv
  have hexp' :
      Real.exp (-(v * u)) * Real.exp (-v + v * u) =
        Real.exp (-v) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    v * v ^ (m - 1) * v ^ (n - 1) * Real.exp (-(v * u)) *
        Real.exp (-v + v * u) =
      (v * v ^ (m - 1) * v ^ (n - 1)) *
        (Real.exp (-(v * u)) * Real.exp (-v + v * u)) := by
        ring
    _ = (v * v ^ (m - 1) * v ^ (n - 1)) * Real.exp (-v) := by
        rw [hexp']
    _ = v ^ (m + n - 1) * Real.exp (-v) := by
        rw [hpowv']

noncomputable def gammaGammaProdPDF (m n : ℕ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  ProbabilityTheory.gammaPDF (m : ℝ) 1 p.1 *
    ProbabilityTheory.gammaPDF (n : ℝ) 1 p.2

noncomputable def betaGammaProdPDF (m n : ℕ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  ProbabilityTheory.betaPDF (m : ℝ) (n : ℝ) p.1 *
    ProbabilityTheory.gammaPDF ((m + n : ℕ) : ℝ) 1 p.2

theorem measurable_gammaGammaProdPDF (m n : ℕ) :
    Measurable (gammaGammaProdPDF m n) := by
  unfold gammaGammaProdPDF ProbabilityTheory.gammaPDF
  fun_prop

theorem measurable_betaGammaProdPDF (m n : ℕ) :
    Measurable (betaGammaProdPDF m n) := by
  unfold betaGammaProdPDF ProbabilityTheory.betaPDF ProbabilityTheory.gammaPDF
  fun_prop

theorem ae_fst_ne_zero_volume_prod_real :
    ∀ᵐ p : ℝ × ℝ ∂(volume : Measure (ℝ × ℝ)), p.1 ≠ 0 := by
  rw [ae_iff]
  have hzero :
      (volume : Measure (ℝ × ℝ)) {p : ℝ × ℝ | p.1 = 0} = 0 := by
    rw [Measure.volume_eq_prod]
    have hset :
        {p : ℝ × ℝ | p.1 = 0} =
          ({0} : Set ℝ) ×ˢ Set.univ := by
      ext p
      simp
    rw [hset, Measure.prod_prod]
    simp
  simpa using hzero

theorem ae_snd_ne_zero_volume_prod_real :
    ∀ᵐ p : ℝ × ℝ ∂(volume : Measure (ℝ × ℝ)), p.2 ≠ 0 := by
  rw [ae_iff]
  have hzero :
      (volume : Measure (ℝ × ℝ)) {p : ℝ × ℝ | p.2 = 0} = 0 := by
    rw [Measure.volume_eq_prod]
    have hset :
        {p : ℝ × ℝ | p.2 = 0} =
          (Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ) := by
      ext p
      simp
    rw [hset, Measure.prod_prod]
    simp
  simpa using hzero

theorem gammaGammaProdPDF_ae_eq_indicator (m n : ℕ) :
    gammaGammaProdPDF m n =ᵐ[(volume : Measure (ℝ × ℝ))]
      gammaRatioPositiveQuadrant.indicator (gammaGammaProdPDF m n) := by
  classical
  filter_upwards [ae_fst_ne_zero_volume_prod_real,
    ae_snd_ne_zero_volume_prod_real] with p hp1 hp2
  by_cases hpQ : p ∈ gammaRatioPositiveQuadrant
  · rw [Set.indicator_of_mem hpQ]
  · rw [Set.indicator_of_notMem hpQ]
    have hpQ' : ¬ (0 < p.1 ∧ 0 < p.2) := by
      simpa [gammaRatioPositiveQuadrant] using hpQ
    rcases not_and_or.mp hpQ' with hp1le | hp2le
    · have hp1neg : p.1 < 0 :=
        lt_of_le_of_ne (le_of_not_gt hp1le) hp1
      simp [gammaGammaProdPDF, ProbabilityTheory.gammaPDF_of_neg hp1neg]
    · have hp2neg : p.2 < 0 :=
        lt_of_le_of_ne (le_of_not_gt hp2le) hp2
      simp [gammaGammaProdPDF, ProbabilityTheory.gammaPDF_of_neg hp2neg]

theorem betaGammaProdPDF_ae_eq_indicator (m n : ℕ) :
    betaGammaProdPDF m n =ᵐ[(volume : Measure (ℝ × ℝ))]
      gammaRatioChangeDomain.indicator (betaGammaProdPDF m n) := by
  classical
  filter_upwards [ae_snd_ne_zero_volume_prod_real] with p hp2
  by_cases hpD : p ∈ gammaRatioChangeDomain
  · rw [Set.indicator_of_mem hpD]
  · rw [Set.indicator_of_notMem hpD]
    have hpD' : ¬ ((0 < p.1 ∧ p.1 < 1) ∧ 0 < p.2) := by
      simpa [gammaRatioChangeDomain] using hpD
    by_cases hu : 0 < p.1 ∧ p.1 < 1
    · have hp2le : p.2 ≤ 0 := by
        exact le_of_not_gt (fun hp2pos => hpD' ⟨hu, hp2pos⟩)
      have hp2neg : p.2 < 0 := lt_of_le_of_ne hp2le hp2
      simp [betaGammaProdPDF, ProbabilityTheory.gammaPDF_of_neg hp2neg]
    · have hu' : p.1 ≤ 0 ∨ 1 ≤ p.1 := by
        by_contra hcontra
        push_neg at hcontra
        exact hu ⟨hcontra.1, hcontra.2⟩
      rcases hu' with hp1le | hple1
      · simp [betaGammaProdPDF,
          ProbabilityTheory.betaPDF_eq_zero_of_nonpos hp1le]
      · simp [betaGammaProdPDF,
          ProbabilityTheory.betaPDF_eq_zero_of_one_le hple1]

theorem gammaMeasure_prod_gammaMeasure_eq_withDensity
    (m n : ℕ) :
    (ProbabilityTheory.gammaMeasure (m : ℝ) 1).prod
        (ProbabilityTheory.gammaMeasure (n : ℝ) 1) =
      (volume : Measure (ℝ × ℝ)).withDensity
        (gammaGammaProdPDF m n) := by
  rw [ProbabilityTheory.gammaMeasure, ProbabilityTheory.gammaMeasure]
  rw [prod_withDensity
    (show Measurable (ProbabilityTheory.gammaPDF (m : ℝ) 1) by
      unfold ProbabilityTheory.gammaPDF
      fun_prop)
    (show Measurable (ProbabilityTheory.gammaPDF (n : ℝ) 1) by
      unfold ProbabilityTheory.gammaPDF
      fun_prop)]
  rw [← Measure.volume_eq_prod ℝ ℝ]
  rfl

theorem betaMeasure_prod_gammaMeasure_eq_withDensity
    (m n : ℕ) :
    (ProbabilityTheory.betaMeasure (m : ℝ) (n : ℝ)).prod
        (ProbabilityTheory.gammaMeasure ((m + n : ℕ) : ℝ) 1) =
      (volume : Measure (ℝ × ℝ)).withDensity
        (betaGammaProdPDF m n) := by
  rw [ProbabilityTheory.betaMeasure, ProbabilityTheory.gammaMeasure]
  rw [prod_withDensity
    (show Measurable (ProbabilityTheory.betaPDF (m : ℝ) (n : ℝ)) by
      unfold ProbabilityTheory.betaPDF
      fun_prop)
    (show Measurable
        (ProbabilityTheory.gammaPDF ((m + n : ℕ) : ℝ) 1) by
      unfold ProbabilityTheory.gammaPDF
      fun_prop)]
  rw [← Measure.volume_eq_prod ℝ ℝ]
  rfl

theorem gammaMeasure_prod_gammaMeasure_eq_restrict_positiveQuadrant
    (m n : ℕ) :
    (ProbabilityTheory.gammaMeasure (m : ℝ) 1).prod
        (ProbabilityTheory.gammaMeasure (n : ℝ) 1) =
      ((volume : Measure (ℝ × ℝ)).restrict
        gammaRatioPositiveQuadrant).withDensity
          (gammaGammaProdPDF m n) := by
  calc
    (ProbabilityTheory.gammaMeasure (m : ℝ) 1).prod
        (ProbabilityTheory.gammaMeasure (n : ℝ) 1) =
      (volume : Measure (ℝ × ℝ)).withDensity
        (gammaGammaProdPDF m n) := by
        exact gammaMeasure_prod_gammaMeasure_eq_withDensity m n
    _ = (volume : Measure (ℝ × ℝ)).withDensity
        (gammaRatioPositiveQuadrant.indicator
          (gammaGammaProdPDF m n)) := by
        exact withDensity_congr_ae
          (gammaGammaProdPDF_ae_eq_indicator m n)
    _ = ((volume : Measure (ℝ × ℝ)).restrict
        gammaRatioPositiveQuadrant).withDensity
          (gammaGammaProdPDF m n) := by
        rw [withDensity_indicator
          measurableSet_gammaRatioPositiveQuadrant]

theorem betaMeasure_prod_gammaMeasure_eq_restrict_domain
    (m n : ℕ) :
    (ProbabilityTheory.betaMeasure (m : ℝ) (n : ℝ)).prod
        (ProbabilityTheory.gammaMeasure ((m + n : ℕ) : ℝ) 1) =
      ((volume : Measure (ℝ × ℝ)).restrict
        gammaRatioChangeDomain).withDensity
          (betaGammaProdPDF m n) := by
  calc
    (ProbabilityTheory.betaMeasure (m : ℝ) (n : ℝ)).prod
        (ProbabilityTheory.gammaMeasure ((m + n : ℕ) : ℝ) 1) =
      (volume : Measure (ℝ × ℝ)).withDensity
        (betaGammaProdPDF m n) := by
        exact betaMeasure_prod_gammaMeasure_eq_withDensity m n
    _ = (volume : Measure (ℝ × ℝ)).withDensity
        (gammaRatioChangeDomain.indicator
          (betaGammaProdPDF m n)) := by
        exact withDensity_congr_ae
          (betaGammaProdPDF_ae_eq_indicator m n)
    _ = ((volume : Measure (ℝ × ℝ)).restrict
        gammaRatioChangeDomain).withDensity
          (betaGammaProdPDF m n) := by
        rw [withDensity_indicator
          measurableSet_gammaRatioChangeDomain]

lemma betaGammaProdPDF_eq_jac_mul_gammaGammaProdPDF_comp
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {x : ℝ × ℝ} (hx : x ∈ gammaRatioChangeDomain) :
    betaGammaProdPDF m n x =
      ENNReal.ofReal |(fderivGammaRatioChange x).det| *
        gammaGammaProdPDF m n (gammaRatioChange x) := by
  rcases hx with ⟨⟨hu0, hu1⟩, hv0⟩
  have h1u : 0 < 1 - x.1 := sub_pos.mpr hu1
  have huv : 0 < x.1 * x.2 := mul_pos hu0 hv0
  have h1uv : 0 < (1 - x.1) * x.2 := mul_pos h1u hv0
  have hmn : 0 < m + n := Nat.add_pos_left hm n
  have hγ1nonneg :
      0 ≤ ProbabilityTheory.gammaPDFReal (m : ℝ) 1 (x.1 * x.2) :=
    ProbabilityTheory.gammaPDFReal_nonneg
      (by exact_mod_cast hm) zero_lt_one _
  have hγ2nonneg :
      0 ≤ ProbabilityTheory.gammaPDFReal (n : ℝ) 1 ((1 - x.1) * x.2) :=
    ProbabilityTheory.gammaPDFReal_nonneg
      (by exact_mod_cast hn) zero_lt_one _
  have hβnonneg :
      0 ≤ ProbabilityTheory.betaPDFReal (m : ℝ) (n : ℝ) x.1 :=
    le_of_lt (ProbabilityTheory.betaPDFReal_pos hu0 hu1
      (by exact_mod_cast hm) (by exact_mod_cast hn))
  have hreal :=
    gamma_beta_density_identity_real (m := m) (n := n)
      hm hn hu0 hu1 hv0
  have hdet :
      |(fderivGammaRatioChange x).det| = x.2 := by
    rw [det_fderivGammaRatioChange]
    exact abs_of_pos hv0
  unfold betaGammaProdPDF gammaGammaProdPDF ProbabilityTheory.betaPDF
    ProbabilityTheory.gammaPDF gammaRatioChange
  rw [hdet]
  calc
    ENNReal.ofReal (ProbabilityTheory.betaPDFReal (m : ℝ) (n : ℝ) x.1) *
        ENNReal.ofReal
          (ProbabilityTheory.gammaPDFReal ((m + n : ℕ) : ℝ) 1 x.2) =
      ENNReal.ofReal
        (ProbabilityTheory.betaPDFReal (m : ℝ) (n : ℝ) x.1 *
          ProbabilityTheory.gammaPDFReal ((m + n : ℕ) : ℝ) 1 x.2) := by
        rw [ENNReal.ofReal_mul hβnonneg]
    _ = ENNReal.ofReal
        (ProbabilityTheory.gammaPDFReal (m : ℝ) 1 (x.1 * x.2) *
          ProbabilityTheory.gammaPDFReal (n : ℝ) 1 ((1 - x.1) * x.2) *
          x.2) := by
        rw [← hreal]
    _ =
      ENNReal.ofReal x.2 *
        (ENNReal.ofReal
          (ProbabilityTheory.gammaPDFReal (m : ℝ) 1 (x.1 * x.2)) *
          ENNReal.ofReal
            (ProbabilityTheory.gammaPDFReal (n : ℝ) 1 ((1 - x.1) * x.2))) := by
        rw [ENNReal.ofReal_mul (mul_nonneg hγ1nonneg hγ2nonneg)]
        rw [ENNReal.ofReal_mul hγ1nonneg]
        ring

theorem gammaRatioChange_map_betaGammaProd_eq_gammaGammaProd
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
      Measure.map gammaRatioChange
          ((ProbabilityTheory.betaMeasure (m : ℝ) (n : ℝ)).prod
            (ProbabilityTheory.gammaMeasure ((m + n : ℕ) : ℝ) 1)) =
        (ProbabilityTheory.gammaMeasure (m : ℝ) 1).prod
          (ProbabilityTheory.gammaMeasure (n : ℝ) 1) := by
  let base : Measure (ℝ × ℝ) :=
    (volume : Measure (ℝ × ℝ)).restrict gammaRatioChangeDomain
  let jac : ℝ × ℝ → ℝ≥0∞ :=
    fun x => ENNReal.ofReal |(fderivGammaRatioChange x).det|
  let pull : ℝ × ℝ → ℝ≥0∞ :=
    fun x => gammaGammaProdPDF m n (gammaRatioChange x)
  have hjac_meas : AEMeasurable jac base := by
    have hjac_eq : jac = fun x : ℝ × ℝ => ENNReal.ofReal |x.2| := by
      funext x
      dsimp [jac]
      rw [det_fderivGammaRatioChange]
    rw [hjac_eq]
    exact (show Measurable (fun x : ℝ × ℝ => ENNReal.ofReal |x.2|) by
      fun_prop).aemeasurable
  have hpull_meas : AEMeasurable pull base := by
    dsimp [pull, jac, base]
    exact ((measurable_gammaGammaProdPDF m n).comp
      measurable_gammaRatioChange).aemeasurable
  have hsource :
      ((volume : Measure (ℝ × ℝ)).restrict
          gammaRatioChangeDomain).withDensity
            (betaGammaProdPDF m n) =
        (base.withDensity jac).withDensity pull := by
    dsimp [base, jac, pull]
    rw [← withDensity_mul₀ hjac_meas hpull_meas]
    apply withDensity_congr_ae
    exact (ae_restrict_mem measurableSet_gammaRatioChangeDomain).mono
      (fun x hx =>
        (betaGammaProdPDF_eq_jac_mul_gammaGammaProdPDF_comp
          (m := m) (n := n) hm hn hx))
  calc
    Measure.map gammaRatioChange
        ((ProbabilityTheory.betaMeasure (m : ℝ) (n : ℝ)).prod
          (ProbabilityTheory.gammaMeasure ((m + n : ℕ) : ℝ) 1)) =
      Measure.map gammaRatioChange
        (((volume : Measure (ℝ × ℝ)).restrict
          gammaRatioChangeDomain).withDensity
            (betaGammaProdPDF m n)) := by
        rw [betaMeasure_prod_gammaMeasure_eq_restrict_domain]
    _ = Measure.map gammaRatioChange
        ((base.withDensity jac).withDensity pull) := by
        rw [hsource]
    _ =
      (Measure.map gammaRatioChange
        (base.withDensity jac)).withDensity (gammaGammaProdPDF m n) := by
        dsimp [pull]
        exact map_withDensity_comp_eq_withDensity_map
          measurable_gammaRatioChange (measurable_gammaGammaProdPDF m n)
    _ =
      ((volume : Measure (ℝ × ℝ)).restrict
        gammaRatioPositiveQuadrant).withDensity
          (gammaGammaProdPDF m n) := by
        dsimp [base, jac]
        rw [gammaRatioChange_map_jacobian]
    _ =
      (ProbabilityTheory.gammaMeasure (m : ℝ) 1).prod
        (ProbabilityTheory.gammaMeasure (n : ℝ) 1) := by
        rw [gammaMeasure_prod_gammaMeasure_eq_restrict_positiveQuadrant]

theorem gamma_gamma_ratio_prod_hasLaw_beta_nat
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    ProbabilityTheory.HasLaw
      gammaRatioMap
      (ProbabilityTheory.betaMeasure (m : ℝ) (n : ℝ))
      ((ProbabilityTheory.gammaMeasure (m : ℝ) 1).prod
        (ProbabilityTheory.gammaMeasure (n : ℝ) 1)) := by
  let β : Measure ℝ := ProbabilityTheory.betaMeasure (m : ℝ) (n : ℝ)
  have hsum_pos : 0 < ((m + n : ℕ) : ℝ) := by
    exact_mod_cast (Nat.add_pos_left hm n)
  letI : IsProbabilityMeasure
      (ProbabilityTheory.gammaMeasure ((m + n : ℕ) : ℝ) 1) :=
    ProbabilityTheory.isProbabilityMeasure_gammaMeasure hsum_pos zero_lt_one
  let γsum : Measure ℝ :=
    ProbabilityTheory.gammaMeasure ((m + n : ℕ) : ℝ) 1
  haveI : IsProbabilityMeasure γsum := by
    dsimp [γsum]
    infer_instance
  have hmap :
      Measure.map gammaRatioChange (β.prod γsum) =
        (ProbabilityTheory.gammaMeasure (m : ℝ) 1).prod
          (ProbabilityTheory.gammaMeasure (n : ℝ) 1) := by
    simpa [β, γsum] using
      gammaRatioChange_map_betaGammaProd_eq_gammaGammaProd
        (m := m) (n := n) hm hn
  have hsource_mem :
      ∀ᵐ x ∂(β.prod γsum), x ∈ gammaRatioChangeDomain := by
    change ∀ᵐ x ∂((ProbabilityTheory.betaMeasure (m : ℝ) (n : ℝ)).prod
      (ProbabilityTheory.gammaMeasure ((m + n : ℕ) : ℝ) 1)),
        x ∈ gammaRatioChangeDomain
    rw [betaMeasure_prod_gammaMeasure_eq_restrict_domain]
    exact (withDensity_absolutelyContinuous
      ((volume : Measure (ℝ × ℝ)).restrict gammaRatioChangeDomain)
      (betaGammaProdPDF m n)).ae_le
        (ae_restrict_mem measurableSet_gammaRatioChangeDomain)
  have hcomp :
      (fun x : ℝ × ℝ => gammaRatioMap (gammaRatioChange x))
        =ᵐ[β.prod γsum] Prod.fst := by
    filter_upwards [hsource_mem] with x hx
    rcases hx with ⟨⟨_hu0, _hu1⟩, hv0⟩
    have hv0' : 0 < x.2 := by simpa using hv0
    dsimp [gammaRatioMap, gammaRatioChange]
    have hden : x.1 * x.2 + (1 - x.1) * x.2 = x.2 := by ring
    rw [hden]
    field_simp [ne_of_gt hv0']
  refine ⟨measurable_gammaRatioMap.aemeasurable, ?_⟩
  calc
      Measure.map gammaRatioMap
          ((ProbabilityTheory.gammaMeasure (m : ℝ) 1).prod
            (ProbabilityTheory.gammaMeasure (n : ℝ) 1)) =
        Measure.map gammaRatioMap (Measure.map gammaRatioChange (β.prod γsum)) := by
          rw [hmap]
      _ =
        Measure.map (fun x : ℝ × ℝ => gammaRatioMap (gammaRatioChange x))
          (β.prod γsum) := by
          rw [Measure.map_map measurable_gammaRatioMap measurable_gammaRatioChange]
          rfl
      _ = Measure.map Prod.fst (β.prod γsum) := by
          exact Measure.map_congr hcomp
      _ = β := by
          rw [Measure.map_fst_prod]
          simp

theorem indep_gamma_gamma_ratio_hasLaw_beta_nat
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {S T : Ω → ℝ} {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n)
    (hS : ProbabilityTheory.HasLaw
      S (ProbabilityTheory.gammaMeasure (m : ℝ) 1) μ)
    (hT : ProbabilityTheory.HasLaw
      T (ProbabilityTheory.gammaMeasure (n : ℝ) 1) μ)
    (hIndep : ProbabilityTheory.IndepFun S T μ) :
    ProbabilityTheory.HasLaw
      (fun ω => S ω / (S ω + T ω))
      (ProbabilityTheory.betaMeasure (m : ℝ) (n : ℝ)) μ := by
  letI : IsProbabilityMeasure
      (ProbabilityTheory.gammaMeasure (m : ℝ) 1) :=
    ProbabilityTheory.isProbabilityMeasure_gammaMeasure
      (by exact_mod_cast hm) zero_lt_one
  letI : IsProbabilityMeasure
      (ProbabilityTheory.gammaMeasure (n : ℝ) 1) :=
    ProbabilityTheory.isProbabilityMeasure_gammaMeasure
      (by exact_mod_cast hn) zero_lt_one
  let γm : Measure ℝ := ProbabilityTheory.gammaMeasure (m : ℝ) 1
  let γn : Measure ℝ := ProbabilityTheory.gammaMeasure (n : ℝ) 1
  letI : IsProbabilityMeasure μ := by
    exact hS.isProbabilityMeasure
  have hPairMap :
      Measure.map (fun ω => (S ω, T ω)) μ = γm.prod γn := by
    calc
      Measure.map (fun ω => (S ω, T ω)) μ =
        (Measure.map S μ).prod (Measure.map T μ) := by
          exact
            (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
              hS.aemeasurable hT.aemeasurable).1 hIndep
        _ = γm.prod γn := by
            rw [hS.map_eq, hT.map_eq]
  have hPairLaw :
      ProbabilityTheory.HasLaw (fun ω => (S ω, T ω)) (γm.prod γn) μ := by
    exact ⟨hS.aemeasurable.prodMk hT.aemeasurable, hPairMap⟩
  have hRatioLaw :
      ProbabilityTheory.HasLaw gammaRatioMap
        (ProbabilityTheory.betaMeasure (m : ℝ) (n : ℝ)) (γm.prod γn) := by
    simpa [γm, γn] using
      gamma_gamma_ratio_prod_hasLaw_beta_nat (m := m) (n := n) hm hn
  simpa [gammaRatioMap] using hRatioLaw.fun_comp hPairLaw

/-- The Gaussian left-block mass ratio

`‖G_E‖² / (‖G_E‖² + ‖G_F‖²)`

has the canonical Beta law. -/
theorem gaussianBlockMassRatio_hasLaw_beta
    [Nonempty ι] [Nonempty κ] :
    ProbabilityTheory.HasLaw
      (fun g : EuclideanSpace ℂ (Sum ι κ) =>
        ‖hermitianBlockLeft (ι := ι) (κ := κ) g‖ ^ 2 /
          (‖hermitianBlockLeft (ι := ι) (κ := κ) g‖ ^ 2 +
            ‖hermitianBlockRight (ι := ι) (κ := κ) g‖ ^ 2))
      (hermitianBlockMassBetaMeasure (ι := ι) (κ := κ))
      (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
        (Sum ι κ)) := by
  let μ :=
    PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
      (Sum ι κ)
  have hLeftLaw :
      ProbabilityTheory.HasLaw
        (hermitianBlockLeft (ι := ι) (κ := κ))
        (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure ι) μ := by
    refine ⟨(measurable_hermitianBlockLeft (ι := ι) (κ := κ)).aemeasurable, ?_⟩
    simpa [μ] using
      (hermitianBlockLeft_map_standardComplexGaussianVectorMeasure
        (ι := ι) (κ := κ))
  have hRightLaw :
      ProbabilityTheory.HasLaw
        (hermitianBlockRight (ι := ι) (κ := κ))
        (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure κ) μ := by
    refine ⟨(measurable_hermitianBlockRight (ι := ι) (κ := κ)).aemeasurable, ?_⟩
    simpa [μ] using
      (hermitianBlockRight_map_standardComplexGaussianVectorMeasure
        (ι := ι) (κ := κ))
  have hS :
      ProbabilityTheory.HasLaw
        (fun g : EuclideanSpace ℂ (Sum ι κ) =>
          ‖hermitianBlockLeft (ι := ι) (κ := κ) g‖ ^ 2)
        (ProbabilityTheory.gammaMeasure (Fintype.card ι : ℝ) 1) μ := by
    simpa [μ] using
      (stdComplexGaussian_normSq_hasLaw_gamma_nat (η := ι)).fun_comp hLeftLaw
  have hT :
      ProbabilityTheory.HasLaw
        (fun g : EuclideanSpace ℂ (Sum ι κ) =>
          ‖hermitianBlockRight (ι := ι) (κ := κ) g‖ ^ 2)
        (ProbabilityTheory.gammaMeasure (Fintype.card κ : ℝ) 1) μ := by
    simpa [μ] using
      (stdComplexGaussian_normSq_hasLaw_gamma_nat (η := κ)).fun_comp hRightLaw
  have hST :
      ProbabilityTheory.IndepFun
        (fun g : EuclideanSpace ℂ (Sum ι κ) =>
          ‖hermitianBlockLeft (ι := ι) (κ := κ) g‖ ^ 2)
        (fun g : EuclideanSpace ℂ (Sum ι κ) =>
          ‖hermitianBlockRight (ι := ι) (κ := κ) g‖ ^ 2)
        μ := by
    simpa [Function.comp, μ] using
      (gaussianBlockLeftRight_indep (ι := ι) (κ := κ)).comp
        (show Measurable (fun z : EuclideanSpace ℂ ι => ‖z‖ ^ 2) by
          fun_prop)
        (show Measurable (fun z : EuclideanSpace ℂ κ => ‖z‖ ^ 2) by
          fun_prop)
  simpa [hermitianBlockMassBetaMeasure, μ] using
    indep_gamma_gamma_ratio_hasLaw_beta_nat
      (μ := μ)
      (S := fun g : EuclideanSpace ℂ (Sum ι κ) =>
        ‖hermitianBlockLeft (ι := ι) (κ := κ) g‖ ^ 2)
      (T := fun g : EuclideanSpace ℂ (Sum ι κ) =>
        ‖hermitianBlockRight (ι := ι) (κ := κ) g‖ ^ 2)
      (m := Fintype.card ι)
      (n := Fintype.card κ)
      Fintype.card_pos Fintype.card_pos hS hT hST

/-- Joint Gaussian product law for the Hermitian block mass ratio and the two
internal block directions.

For `G = (G_E,G_F)` standard complex Gaussian, this states that

`(‖G_E‖² / (‖G_E‖² + ‖G_F‖²), G_E/‖G_E‖, G_F/‖G_F‖)`

has law

`Beta(card ι, card κ) × surfaceMeasureAmbient ι × surfaceMeasureAmbient κ`.

Analytically, this is the assembled Gaussian statement: Gamma/Gamma gives the
Beta mass ratio, the single-block polar theorem gives uniform directions, and
the two blocks are independent. -/
theorem gaussianBlock_massRatio_directions_map_eq_prod
    [Nonempty ι] [Nonempty κ]
    [SFinite ((MeasureTheory.volume :
      Measure (EuclideanSpace ℂ ι)).toSphere)]
    [SFinite ((MeasureTheory.volume :
      Measure (EuclideanSpace ℂ κ)).toSphere)] :
    Measure.map
        (fun g : EuclideanSpace ℂ (Sum ι κ) =>
          (‖hermitianBlockLeft (ι := ι) (κ := κ) g‖ ^ 2 /
              (‖hermitianBlockLeft (ι := ι) (κ := κ) g‖ ^ 2 +
                ‖hermitianBlockRight (ι := ι) (κ := κ) g‖ ^ 2),
            gaussianBlockLeftDirection (ι := ι) (κ := κ) g,
            gaussianBlockRightDirection (ι := ι) (κ := κ) g))
        (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
          (Sum ι κ)) =
      (hermitianBlockMassBetaMeasure (ι := ι) (κ := κ)).prod
        ((surfaceMeasureAmbient ι).prod (surfaceMeasureAmbient κ)) := by
  let μG :=
    PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
      (Sum ι κ)
  let γL : Measure ℝ :=
    ProbabilityTheory.gammaMeasure (Fintype.card ι : ℝ) 1
  let γR : Measure ℝ :=
    ProbabilityTheory.gammaMeasure (Fintype.card κ : ℝ) 1
  let σL : Measure (EuclideanSpace ℂ ι) := surfaceMeasureAmbient ι
  let σR : Measure (EuclideanSpace ℂ κ) := surfaceMeasureAmbient κ
  let leftPair : EuclideanSpace ℂ ι → ℝ × EuclideanSpace ℂ ι :=
    fun z => (‖z‖ ^ 2, ((‖z‖)⁻¹ : ℂ) • z)
  let rightPair : EuclideanSpace ℂ κ → ℝ × EuclideanSpace ℂ κ :=
    fun z => (‖z‖ ^ 2, ((‖z‖)⁻¹ : ℂ) • z)
  let leftPairAmbient :
      EuclideanSpace ℂ (Sum ι κ) → ℝ × EuclideanSpace ℂ ι :=
    fun g => (‖hermitianBlockLeft (ι := ι) (κ := κ) g‖ ^ 2,
      gaussianBlockLeftDirection (ι := ι) (κ := κ) g)
  let rightPairAmbient :
      EuclideanSpace ℂ (Sum ι κ) → ℝ × EuclideanSpace ℂ κ :=
    fun g => (‖hermitianBlockRight (ι := ι) (κ := κ) g‖ ^ 2,
      gaussianBlockRightDirection (ι := ι) (κ := κ) g)
  let pairPairs :
      EuclideanSpace ℂ (Sum ι κ) →
        (ℝ × EuclideanSpace ℂ ι) × (ℝ × EuclideanSpace ℂ κ) :=
    fun g => (leftPairAmbient g, rightPairAmbient g)
  let reorderSecond :
      EuclideanSpace ℂ ι × (ℝ × EuclideanSpace ℂ κ) →
        ℝ × (EuclideanSpace ℂ ι × EuclideanSpace ℂ κ) :=
    fun x => (x.2.1, (x.1, x.2.2))
  let pack :
      ((ℝ × EuclideanSpace ℂ ι) × (ℝ × EuclideanSpace ℂ κ)) →
        (ℝ × ℝ) × (EuclideanSpace ℂ ι × EuclideanSpace ℂ κ) :=
    fun x => ((x.1.1, x.2.1), (x.1.2, x.2.2))
  let ratioMap : ℝ × ℝ → ℝ := fun x => x.1 / (x.1 + x.2)
  let collapse :
      (ℝ × ℝ) × (EuclideanSpace ℂ ι × EuclideanSpace ℂ κ) →
        ℝ × EuclideanSpace ℂ ι × EuclideanSpace ℂ κ :=
    fun x => (ratioMap x.1, x.2.1, x.2.2)
  let swapLeft : EuclideanSpace ℂ ι × ℝ → ℝ × EuclideanSpace ℂ ι := Prod.swap
  have hγL : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hγR : 0 < (Fintype.card κ : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card κ)
  letI : IsProbabilityMeasure γL :=
    ProbabilityTheory.isProbabilityMeasure_gammaMeasure hγL zero_lt_one
  letI : IsProbabilityMeasure γR :=
    ProbabilityTheory.isProbabilityMeasure_gammaMeasure hγR zero_lt_one
  letI : IsProbabilityMeasure σL :=
    surfaceMeasureAmbient_isProbabilityMeasure ι
  letI : IsProbabilityMeasure σR :=
    surfaceMeasureAmbient_isProbabilityMeasure κ
  have hLeftLaw :
      ProbabilityTheory.HasLaw
        (hermitianBlockLeft (ι := ι) (κ := κ))
        (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure ι) μG := by
    refine ⟨(measurable_hermitianBlockLeft (ι := ι) (κ := κ)).aemeasurable, ?_⟩
    simpa [μG] using
      (hermitianBlockLeft_map_standardComplexGaussianVectorMeasure
        (ι := ι) (κ := κ))
  have hRightLaw :
      ProbabilityTheory.HasLaw
        (hermitianBlockRight (ι := ι) (κ := κ))
        (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure κ) μG := by
    refine ⟨(measurable_hermitianBlockRight (ι := ι) (κ := κ)).aemeasurable, ?_⟩
    simpa [μG] using
      (hermitianBlockRight_map_standardComplexGaussianVectorMeasure
        (ι := ι) (κ := κ))
  have hLeftPairBase :
      ProbabilityTheory.HasLaw leftPair (γL.prod σL)
        (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure ι) := by
    refine ⟨(show Measurable leftPair by
      dsimp [leftPair]
      fun_prop).aemeasurable, ?_⟩
    calc
      Measure.map leftPair
          (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure ι) =
        (Measure.map
            (fun z : EuclideanSpace ℂ ι => ‖z‖ ^ 2)
            (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure ι)).prod
          (Measure.map
            (fun z : EuclideanSpace ℂ ι => ((‖z‖)⁻¹ : ℂ) • z)
            (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure ι)) := by
            exact
              (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
                (show AEMeasurable
                    (fun z : EuclideanSpace ℂ ι => ‖z‖ ^ 2)
                    (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure ι) from
                  (show Measurable
                      (fun z : EuclideanSpace ℂ ι => ‖z‖ ^ 2) by
                    fun_prop).aemeasurable)
                (show AEMeasurable
                    (fun z : EuclideanSpace ℂ ι => ((‖z‖)⁻¹ : ℂ) • z)
                    (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure ι) from
                  (show Measurable
                      (fun z : EuclideanSpace ℂ ι => ((‖z‖)⁻¹ : ℂ) • z) by
                    fun_prop).aemeasurable)).1
                (standardComplexGaussian_normSq_indep_direction (η := ι))
      _ = γL.prod σL := by
          rw [(stdComplexGaussian_normSq_hasLaw_gamma_nat (η := ι)).map_eq,
            standardComplexGaussian_direction_hasLaw_surfaceMeasureAmbient
              (η := ι)]
  have hRightPairBase :
      ProbabilityTheory.HasLaw rightPair (γR.prod σR)
        (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure κ) := by
    refine ⟨(show Measurable rightPair by
      dsimp [rightPair]
      fun_prop).aemeasurable, ?_⟩
    calc
      Measure.map rightPair
          (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure κ) =
        (Measure.map
            (fun z : EuclideanSpace ℂ κ => ‖z‖ ^ 2)
            (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure κ)).prod
          (Measure.map
            (fun z : EuclideanSpace ℂ κ => ((‖z‖)⁻¹ : ℂ) • z)
            (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure κ)) := by
            exact
              (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
                (show AEMeasurable
                    (fun z : EuclideanSpace ℂ κ => ‖z‖ ^ 2)
                    (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure κ) from
                  (show Measurable
                      (fun z : EuclideanSpace ℂ κ => ‖z‖ ^ 2) by
                    fun_prop).aemeasurable)
                (show AEMeasurable
                    (fun z : EuclideanSpace ℂ κ => ((‖z‖)⁻¹ : ℂ) • z)
                    (PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure κ) from
                  (show Measurable
                      (fun z : EuclideanSpace ℂ κ => ((‖z‖)⁻¹ : ℂ) • z) by
                    fun_prop).aemeasurable)).1
                (standardComplexGaussian_normSq_indep_direction (η := κ))
      _ = γR.prod σR := by
          rw [(stdComplexGaussian_normSq_hasLaw_gamma_nat (η := κ)).map_eq,
            standardComplexGaussian_direction_hasLaw_surfaceMeasureAmbient
              (η := κ)]
  have hLeftPairAmbient :
      ProbabilityTheory.HasLaw leftPairAmbient (γL.prod σL) μG := by
    simpa [leftPairAmbient, leftPair, gaussianBlockLeftDirection] using
      hLeftPairBase.fun_comp hLeftLaw
  have hRightPairAmbient :
      ProbabilityTheory.HasLaw rightPairAmbient (γR.prod σR) μG := by
    simpa [rightPairAmbient, rightPair, gaussianBlockRightDirection] using
      hRightPairBase.fun_comp hRightLaw
  have hPairPairs :
      Measure.map pairPairs μG = (γL.prod σL).prod (γR.prod σR) := by
    calc
      Measure.map pairPairs μG =
        (Measure.map leftPairAmbient μG).prod
          (Measure.map rightPairAmbient μG) := by
            exact
              (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
                (show AEMeasurable leftPairAmbient μG from
                  (show Measurable leftPairAmbient by
                    dsimp [leftPairAmbient]
                    fun_prop).aemeasurable)
                (show AEMeasurable rightPairAmbient μG from
                  (show Measurable rightPairAmbient by
                    dsimp [rightPairAmbient]
                    fun_prop).aemeasurable)).1
                (gaussianBlockLeftRight_normSq_direction_indep
                  (ι := ι) (κ := κ))
      _ = (γL.prod σL).prod (γR.prod σR) := by
          rw [hLeftPairAmbient.map_eq, hRightPairAmbient.map_eq]
  have hReorderSecond :
      Measure.map reorderSecond (σL.prod (γR.prod σR)) =
        γR.prod (σL.prod σR) := by
    have hreorder :
        reorderSecond =
          MeasurableEquiv.prodAssoc ∘
            Prod.map swapLeft (fun x : EuclideanSpace ℂ κ => x) ∘
              MeasurableEquiv.prodAssoc.symm := by
      funext x
      rfl
    calc
      Measure.map reorderSecond (σL.prod (γR.prod σR)) =
        Measure.map
          (MeasurableEquiv.prodAssoc ∘
            Prod.map swapLeft (fun x : EuclideanSpace ℂ κ => x) ∘
              MeasurableEquiv.prodAssoc.symm)
          (σL.prod (γR.prod σR)) := by
            rw [hreorder]
      _ =
        Measure.map
          (MeasurableEquiv.prodAssoc ∘
            Prod.map swapLeft (fun x : EuclideanSpace ℂ κ => x))
          (Measure.map MeasurableEquiv.prodAssoc.symm
            (σL.prod (γR.prod σR))) := by
              symm
              simpa [Function.comp] using
                (Measure.map_map
                  (μ := σL.prod (γR.prod σR))
                  (f := MeasurableEquiv.prodAssoc.symm)
                  (g := MeasurableEquiv.prodAssoc ∘
                    Prod.map swapLeft (fun x : EuclideanSpace ℂ κ => x))
                  (show Measurable
                      (MeasurableEquiv.prodAssoc ∘
                        Prod.map swapLeft (fun x : EuclideanSpace ℂ κ => x)) by
                    fun_prop)
                  (show Measurable MeasurableEquiv.prodAssoc.symm by
                    exact MeasurableEquiv.prodAssoc.symm.measurable))
      _ =
        Measure.map MeasurableEquiv.prodAssoc
          (Measure.map
            (Prod.map swapLeft (fun x : EuclideanSpace ℂ κ => x))
            (Measure.map MeasurableEquiv.prodAssoc.symm
              (σL.prod (γR.prod σR)))) := by
                symm
                simpa [Function.comp] using
                  (Measure.map_map
                    (μ := Measure.map MeasurableEquiv.prodAssoc.symm
                      (σL.prod (γR.prod σR)))
                    (f := Prod.map swapLeft (fun x : EuclideanSpace ℂ κ => x))
                    (g := MeasurableEquiv.prodAssoc)
                    (show Measurable MeasurableEquiv.prodAssoc by
                      exact MeasurableEquiv.prodAssoc.measurable)
                    (show Measurable
                        (Prod.map swapLeft (fun x : EuclideanSpace ℂ κ => x)) by
                      fun_prop))
      _ =
        Measure.map MeasurableEquiv.prodAssoc
          (Measure.map
            (Prod.map swapLeft (fun x : EuclideanSpace ℂ κ => x))
            ((σL.prod γR).prod σR)) := by
              rw [(MeasurePreserving.symm MeasurableEquiv.prodAssoc
                (MeasureTheory.measurePreserving_prodAssoc σL γR σR)).map_eq]
      _ =
        Measure.map MeasurableEquiv.prodAssoc
          ((Measure.map swapLeft (σL.prod γR)).prod
            (Measure.map (fun x : EuclideanSpace ℂ κ => x) σR)) := by
              congr 1
              simpa [Prod.map] using
                (Measure.map_prod_map
                  (σL.prod γR) σR
                  (show Measurable swapLeft by fun_prop)
                  measurable_id).symm
      _ = Measure.map MeasurableEquiv.prodAssoc
          (((γR.prod σL)).prod σR) := by
            congr 1
            have hswap :
                Measure.map swapLeft (σL.prod γR) = γR.prod σL := by
              simpa [swapLeft] using
                (MeasureTheory.Measure.prod_swap (μ := σL) (ν := γR))
            rw [hswap]
            simp
      _ = γR.prod (σL.prod σR) := by
            exact (MeasureTheory.measurePreserving_prodAssoc γR σL σR).map_eq
  have hPack :
      Measure.map pack ((γL.prod σL).prod (γR.prod σR)) =
        (γL.prod γR).prod (σL.prod σR) := by
    have hpack :
        pack =
          MeasurableEquiv.prodAssoc.symm ∘
            Prod.map (fun x : ℝ => x) reorderSecond ∘
              MeasurableEquiv.prodAssoc := by
      funext x
      rfl
    calc
      Measure.map pack ((γL.prod σL).prod (γR.prod σR)) =
        Measure.map
          (MeasurableEquiv.prodAssoc.symm ∘
            Prod.map (fun x : ℝ => x) reorderSecond ∘
              MeasurableEquiv.prodAssoc)
          ((γL.prod σL).prod (γR.prod σR)) := by
            rw [hpack]
      _ =
        Measure.map
          (MeasurableEquiv.prodAssoc.symm ∘
            Prod.map (fun x : ℝ => x) reorderSecond)
          (Measure.map MeasurableEquiv.prodAssoc
            ((γL.prod σL).prod (γR.prod σR))) := by
              symm
              simpa [Function.comp] using
                (Measure.map_map
                  (μ := ((γL.prod σL).prod (γR.prod σR)))
                  (f := MeasurableEquiv.prodAssoc)
                  (g := MeasurableEquiv.prodAssoc.symm ∘
                    Prod.map (fun x : ℝ => x) reorderSecond)
                  (show Measurable
                      (MeasurableEquiv.prodAssoc.symm ∘
                        Prod.map (fun x : ℝ => x) reorderSecond) by
                    fun_prop)
                  (show Measurable MeasurableEquiv.prodAssoc by
                    exact MeasurableEquiv.prodAssoc.measurable))
      _ =
        Measure.map MeasurableEquiv.prodAssoc.symm
          (Measure.map
            (Prod.map (fun x : ℝ => x) reorderSecond)
            (Measure.map MeasurableEquiv.prodAssoc
              ((γL.prod σL).prod (γR.prod σR)))) := by
                symm
                simpa [Function.comp] using
                  (Measure.map_map
                    (μ := Measure.map MeasurableEquiv.prodAssoc
                      ((γL.prod σL).prod (γR.prod σR)))
                    (f := Prod.map (fun x : ℝ => x) reorderSecond)
                    (g := MeasurableEquiv.prodAssoc.symm)
                    (show Measurable MeasurableEquiv.prodAssoc.symm by
                      exact MeasurableEquiv.prodAssoc.symm.measurable)
                    (show Measurable
                        (Prod.map (fun x : ℝ => x) reorderSecond) by
                      fun_prop))
      _ =
        Measure.map MeasurableEquiv.prodAssoc.symm
          (Measure.map
            (Prod.map (fun x : ℝ => x) reorderSecond)
            (γL.prod (σL.prod (γR.prod σR)))) := by
              rw [(MeasureTheory.measurePreserving_prodAssoc γL σL
                (γR.prod σR)).map_eq]
      _ =
        Measure.map MeasurableEquiv.prodAssoc.symm
          ((Measure.map (fun x : ℝ => x) γL).prod
            (Measure.map reorderSecond (σL.prod (γR.prod σR)))) := by
              congr 1
              simpa [Prod.map] using
                (Measure.map_prod_map
                  γL (σL.prod (γR.prod σR))
                  measurable_id
                  (show Measurable reorderSecond by
                    dsimp [reorderSecond]
                    fun_prop)).symm
      _ =
        Measure.map MeasurableEquiv.prodAssoc.symm
          (γL.prod (γR.prod (σL.prod σR))) := by
            congr 1
            simp [hReorderSecond]
      _ = (γL.prod γR).prod (σL.prod σR) := by
            exact (MeasurePreserving.symm MeasurableEquiv.prodAssoc
              (MeasureTheory.measurePreserving_prodAssoc γL γR
                (σL.prod σR))).map_eq
  have hRatioLaw :
      ProbabilityTheory.HasLaw ratioMap
        (hermitianBlockMassBetaMeasure (ι := ι) (κ := κ))
        (γL.prod γR) := by
    have hfst :
        ProbabilityTheory.HasLaw (fun x : ℝ × ℝ => x.1) γL (γL.prod γR) :=
      MeasureTheory.measurePreserving_fst.hasLaw
    have hsnd :
        ProbabilityTheory.HasLaw (fun x : ℝ × ℝ => x.2) γR (γL.prod γR) :=
      MeasureTheory.measurePreserving_snd.hasLaw
    have hind :
        ProbabilityTheory.IndepFun
          (fun x : ℝ × ℝ => x.1)
          (fun x : ℝ × ℝ => x.2)
          (γL.prod γR) := by
      simpa using
        (ProbabilityTheory.indepFun_prod measurable_id measurable_id
          (μ := γL) (ν := γR))
    simpa [γL, γR, hermitianBlockMassBetaMeasure, ratioMap] using
      indep_gamma_gamma_ratio_hasLaw_beta_nat
        (μ := γL.prod γR)
        (S := fun x : ℝ × ℝ => x.1)
        (T := fun x : ℝ × ℝ => x.2)
        (m := Fintype.card ι)
        (n := Fintype.card κ)
        Fintype.card_pos Fintype.card_pos hfst hsnd hind
  have hCollapse :
      Measure.map collapse ((γL.prod γR).prod (σL.prod σR)) =
        (hermitianBlockMassBetaMeasure (ι := ι) (κ := κ)).prod
          (σL.prod σR) := by
    calc
      Measure.map collapse ((γL.prod γR).prod (σL.prod σR)) =
        (Measure.map ratioMap (γL.prod γR)).prod
          (Measure.map (fun x : EuclideanSpace ℂ ι × EuclideanSpace ℂ κ => x)
            (σL.prod σR)) := by
            simpa [collapse, ratioMap] using
              (Measure.map_prod_map
                (γL.prod γR) (σL.prod σR)
                (show Measurable ratioMap by
                  dsimp [ratioMap]
                  fun_prop)
                measurable_id).symm
      _ =
        (hermitianBlockMassBetaMeasure (ι := ι) (κ := κ)).prod
          (σL.prod σR) := by
            simp [hRatioLaw.map_eq]
  calc
    Measure.map
        (fun g : EuclideanSpace ℂ (Sum ι κ) =>
          (‖hermitianBlockLeft (ι := ι) (κ := κ) g‖ ^ 2 /
              (‖hermitianBlockLeft (ι := ι) (κ := κ) g‖ ^ 2 +
                ‖hermitianBlockRight (ι := ι) (κ := κ) g‖ ^ 2),
            gaussianBlockLeftDirection (ι := ι) (κ := κ) g,
            gaussianBlockRightDirection (ι := ι) (κ := κ) g))
        μG =
      Measure.map (collapse ∘ pack ∘ pairPairs) μG := by
        rfl
    _ = Measure.map collapse (Measure.map pack (Measure.map pairPairs μG)) := by
        have h1 :
            Measure.map (collapse ∘ pack ∘ pairPairs) μG =
              Measure.map collapse (Measure.map (pack ∘ pairPairs) μG) := by
          symm
          simpa [Function.comp] using
            (Measure.map_map
              (μ := μG)
              (f := pack ∘ pairPairs)
              (g := collapse)
              (show Measurable collapse by
                dsimp [collapse, ratioMap]
                fun_prop)
              (show Measurable (pack ∘ pairPairs) by
                fun_prop))
        rw [h1]
        have h2 :
            Measure.map (pack ∘ pairPairs) μG =
              Measure.map pack (Measure.map pairPairs μG) := by
          symm
          simpa [Function.comp] using
            (Measure.map_map
              (μ := μG)
              (f := pairPairs)
              (g := pack)
              (show Measurable pack by
                dsimp [pack]
                fun_prop)
              (show Measurable pairPairs by
                dsimp [pairPairs, leftPairAmbient, rightPairAmbient]
                fun_prop))
        rw [h2]
    _ =
      Measure.map collapse (Measure.map pack ((γL.prod σL).prod (γR.prod σR))) := by
        rw [hPairPairs]
    _ =
      Measure.map collapse ((γL.prod γR).prod (σL.prod σR)) := by
        rw [hPack]
    _ =
      (hermitianBlockMassBetaMeasure (ι := ι) (κ := κ)).prod
        ((surfaceMeasureAmbient ι).prod (surfaceMeasureAmbient κ)) := by
          simpa [σL, σR] using hCollapse

/-- Abstract two-block spherical decomposition and independence.

This is the coordinate-free version of the one-column spherical theorem:
for `x ∈ E ⊕ F`, the triple

`(‖x_E‖², x_E/‖x_E‖, x_F/‖x_F‖)`

has product law `massLaw × leftDirectionLaw × rightDirectionLaw`.  The
marginal equalities are included so downstream proofs cannot accidentally use
the wrong background law. -/
structure HermitianBlockSphericalDecompositionIndependence
    (μ : Measure (EuclideanSpace ℂ (Sum ι κ)))
    (massLaw : Measure ℝ)
    (leftDirectionLaw : Measure (EuclideanSpace ℂ ι))
    (rightDirectionLaw : Measure (EuclideanSpace ℂ κ)) : Prop where
  measurable_mass : Measurable (hermitianBlockMass (ι := ι) (κ := κ))
  measurable_leftDirection :
    Measurable (hermitianBlockLeftDirection (ι := ι) (κ := κ))
  measurable_rightDirection :
    Measurable (hermitianBlockRightDirection (ι := ι) (κ := κ))
  sfinite_massLaw : SFinite massLaw
  sfinite_leftDirectionLaw : SFinite leftDirectionLaw
  sfinite_rightDirectionLaw : SFinite rightDirectionLaw
  map_mass_eq :
    Measure.map (hermitianBlockMass (ι := ι) (κ := κ)) μ = massLaw
  map_leftDirection_eq :
    Measure.map (hermitianBlockLeftDirection (ι := ι) (κ := κ)) μ =
      leftDirectionLaw
  map_rightDirection_eq :
    Measure.map (hermitianBlockRightDirection (ι := ι) (κ := κ)) μ =
      rightDirectionLaw
  map_triple_eq :
    Measure.map
        (fun x =>
          (hermitianBlockMass (ι := ι) (κ := κ) x,
            hermitianBlockLeftDirection (ι := ι) (κ := κ) x,
            hermitianBlockRightDirection (ι := ι) (κ := κ) x))
        μ =
      massLaw.prod (leftDirectionLaw.prod rightDirectionLaw)

/-- Measurability of the joint block-coordinate map. -/
theorem HermitianBlockSphericalDecompositionIndependence.measurable_triple
    {μ : Measure (EuclideanSpace ℂ (Sum ι κ))}
    {massLaw : Measure ℝ}
    {leftDirectionLaw : Measure (EuclideanSpace ℂ ι)}
    {rightDirectionLaw : Measure (EuclideanSpace ℂ κ)}
    (I :
      HermitianBlockSphericalDecompositionIndependence
        (ι := ι) (κ := κ) μ massLaw leftDirectionLaw rightDirectionLaw) :
    Measurable
      (fun x =>
        (hermitianBlockMass (ι := ι) (κ := κ) x,
          hermitianBlockLeftDirection (ι := ι) (κ := κ) x,
          hermitianBlockRightDirection (ι := ι) (κ := κ) x)) := by
  exact I.measurable_mass.prod
    (I.measurable_leftDirection.prod I.measurable_rightDirection)

/-- Product law gives exact factorization on block-rectangular events. -/
theorem HermitianBlockSphericalDecompositionIndependence.rect_event_probability_eq
    {μ : Measure (EuclideanSpace ℂ (Sum ι κ))}
    {massLaw : Measure ℝ}
    {leftDirectionLaw : Measure (EuclideanSpace ℂ ι)}
    {rightDirectionLaw : Measure (EuclideanSpace ℂ κ)}
    (I :
      HermitianBlockSphericalDecompositionIndependence
        (ι := ι) (κ := κ) μ massLaw leftDirectionLaw rightDirectionLaw)
    {massSet : Set ℝ}
    {leftSet : Set (EuclideanSpace ℂ ι)}
    {rightSet : Set (EuclideanSpace ℂ κ)}
    (hmass : MeasurableSet massSet)
    (hleft : MeasurableSet leftSet)
    (hright : MeasurableSet rightSet) :
    μ.real
        {x |
          hermitianBlockMass (ι := ι) (κ := κ) x ∈ massSet ∧
            hermitianBlockLeftDirection (ι := ι) (κ := κ) x ∈ leftSet ∧
              hermitianBlockRightDirection (ι := ι) (κ := κ) x ∈ rightSet} =
      massLaw.real massSet * leftDirectionLaw.real leftSet *
        rightDirectionLaw.real rightSet := by
  let T : EuclideanSpace ℂ (Sum ι κ) → ℝ × EuclideanSpace ℂ ι ×
      EuclideanSpace ℂ κ :=
    fun x =>
      (hermitianBlockMass (ι := ι) (κ := κ) x,
        hermitianBlockLeftDirection (ι := ι) (κ := κ) x,
        hermitianBlockRightDirection (ι := ι) (κ := κ) x)
  let rect : Set (ℝ × EuclideanSpace ℂ ι × EuclideanSpace ℂ κ) :=
    massSet ×ˢ (leftSet ×ˢ rightSet)
  have hrect : MeasurableSet rect := hmass.prod (hleft.prod hright)
  have hpre :
      T ⁻¹' rect =
        {x |
          hermitianBlockMass (ι := ι) (κ := κ) x ∈ massSet ∧
            hermitianBlockLeftDirection (ι := ι) (κ := κ) x ∈ leftSet ∧
              hermitianBlockRightDirection (ι := ι) (κ := κ) x ∈ rightSet} := by
    ext x
    simp [T, rect]
  calc
    μ.real
        {x |
          hermitianBlockMass (ι := ι) (κ := κ) x ∈ massSet ∧
            hermitianBlockLeftDirection (ι := ι) (κ := κ) x ∈ leftSet ∧
              hermitianBlockRightDirection (ι := ι) (κ := κ) x ∈ rightSet}
        = μ.real (T ⁻¹' rect) := by rw [hpre]
    _ = (Measure.map T μ).real rect := by
          rw [map_measureReal_apply I.measurable_triple hrect]
    _ = (massLaw.prod (leftDirectionLaw.prod rightDirectionLaw)).real rect := by
          rw [I.map_triple_eq]
    _ = massLaw.real massSet * leftDirectionLaw.real leftSet *
          rightDirectionLaw.real rightSet := by
          letI : SFinite leftDirectionLaw := I.sfinite_leftDirectionLaw
          letI : SFinite rightDirectionLaw := I.sfinite_rightDirectionLaw
          rw [measureReal_prod_prod, measureReal_prod_prod]
          ring

/-- Rectangular-event formulation of the Hermitian two-block spherical law.

This is the measure-theoretic core needed before packaging the statement as a
full product law for the triple.  It states the factorization on measurable
rectangles

`massSet × leftSet × rightSet`

for the block coordinates

`x ↦ (‖x_E‖², x_E/‖x_E‖, x_F/‖x_F‖)`. -/
structure HermitianBlockSphericalRectangularLaw
    (μ : Measure (EuclideanSpace ℂ (Sum ι κ)))
    (massLaw : Measure ℝ)
    (leftDirectionLaw : Measure (EuclideanSpace ℂ ι))
    (rightDirectionLaw : Measure (EuclideanSpace ℂ κ)) : Prop where
  measurable_mass : Measurable (hermitianBlockMass (ι := ι) (κ := κ))
  measurable_leftDirection :
    Measurable (hermitianBlockLeftDirection (ι := ι) (κ := κ))
  measurable_rightDirection :
    Measurable (hermitianBlockRightDirection (ι := ι) (κ := κ))
  sfinite_massLaw : SFinite massLaw
  sfinite_leftDirectionLaw : SFinite leftDirectionLaw
  sfinite_rightDirectionLaw : SFinite rightDirectionLaw
  rect_event_eq :
    ∀ {massSet : Set ℝ}
      {leftSet : Set (EuclideanSpace ℂ ι)}
      {rightSet : Set (EuclideanSpace ℂ κ)},
      MeasurableSet massSet →
      MeasurableSet leftSet →
      MeasurableSet rightSet →
        μ
          {x |
            hermitianBlockMass (ι := ι) (κ := κ) x ∈ massSet ∧
              hermitianBlockLeftDirection (ι := ι) (κ := κ) x ∈ leftSet ∧
                hermitianBlockRightDirection (ι := ι) (κ := κ) x ∈ rightSet} =
          massLaw massSet * (leftDirectionLaw leftSet * rightDirectionLaw rightSet)

/-- Measurability of the joint block-coordinate map from the rectangular-law
package. -/
theorem HermitianBlockSphericalRectangularLaw.measurable_triple
    {μ : Measure (EuclideanSpace ℂ (Sum ι κ))}
    {massLaw : Measure ℝ}
    {leftDirectionLaw : Measure (EuclideanSpace ℂ ι)}
    {rightDirectionLaw : Measure (EuclideanSpace ℂ κ)}
    (I :
      HermitianBlockSphericalRectangularLaw
        (ι := ι) (κ := κ) μ massLaw leftDirectionLaw rightDirectionLaw) :
    Measurable
      (fun x =>
        (hermitianBlockMass (ι := ι) (κ := κ) x,
          hermitianBlockLeftDirection (ι := ι) (κ := κ) x,
          hermitianBlockRightDirection (ι := ι) (κ := κ) x)) := by
  exact I.measurable_mass.prod
    (I.measurable_leftDirection.prod I.measurable_rightDirection)

/-- The rectangular-law package gives exactly the real-valued probability
factorization requested for measurable block rectangles. -/
theorem HermitianBlockSphericalRectangularLaw.rect_event_probability_eq
    {μ : Measure (EuclideanSpace ℂ (Sum ι κ))}
    {massLaw : Measure ℝ}
    {leftDirectionLaw : Measure (EuclideanSpace ℂ ι)}
    {rightDirectionLaw : Measure (EuclideanSpace ℂ κ)}
    (I :
      HermitianBlockSphericalRectangularLaw
        (ι := ι) (κ := κ) μ massLaw leftDirectionLaw rightDirectionLaw)
    {massSet : Set ℝ}
    {leftSet : Set (EuclideanSpace ℂ ι)}
    {rightSet : Set (EuclideanSpace ℂ κ)}
    (hmass : MeasurableSet massSet)
    (hleft : MeasurableSet leftSet)
    (hright : MeasurableSet rightSet) :
    μ.real
        {x |
          hermitianBlockMass (ι := ι) (κ := κ) x ∈ massSet ∧
            hermitianBlockLeftDirection (ι := ι) (κ := κ) x ∈ leftSet ∧
              hermitianBlockRightDirection (ι := ι) (κ := κ) x ∈ rightSet} =
      massLaw.real massSet * leftDirectionLaw.real leftSet *
        rightDirectionLaw.real rightSet := by
  letI : SFinite leftDirectionLaw := I.sfinite_leftDirectionLaw
  letI : SFinite rightDirectionLaw := I.sfinite_rightDirectionLaw
  let rect : Set (ℝ × EuclideanSpace ℂ ι × EuclideanSpace ℂ κ) :=
    massSet ×ˢ (leftSet ×ˢ rightSet)
  have hrect : MeasurableSet rect := hmass.prod (hleft.prod hright)
  have hprod :
      (massLaw.prod (leftDirectionLaw.prod rightDirectionLaw)).real rect =
        massLaw.real massSet * leftDirectionLaw.real leftSet *
          rightDirectionLaw.real rightSet := by
    rw [measureReal_prod_prod, measureReal_prod_prod]
    ring
  have hprod_apply :
      (massLaw.prod (leftDirectionLaw.prod rightDirectionLaw)) rect =
        massLaw massSet * (leftDirectionLaw leftSet * rightDirectionLaw rightSet) := by
    rw [Measure.prod_prod, Measure.prod_prod]
  calc
    μ.real
        {x |
          hermitianBlockMass (ι := ι) (κ := κ) x ∈ massSet ∧
            hermitianBlockLeftDirection (ι := ι) (κ := κ) x ∈ leftSet ∧
              hermitianBlockRightDirection (ι := ι) (κ := κ) x ∈ rightSet}
        = ENNReal.toReal
            (massLaw massSet *
              (leftDirectionLaw leftSet * rightDirectionLaw rightSet)) := by
            rw [Measure.real, I.rect_event_eq hmass hleft hright]
    _ = (massLaw.prod (leftDirectionLaw.prod rightDirectionLaw)).real rect := by
            rw [Measure.real, hprod_apply]
    _ = massLaw.real massSet * leftDirectionLaw.real leftSet *
          rightDirectionLaw.real rightSet := hprod

/-- A rectangular law determines the full product law of the block-coordinate
triple. -/
theorem HermitianBlockSphericalRectangularLaw.map_triple_eq
    {μ : Measure (EuclideanSpace ℂ (Sum ι κ))}
    {massLaw : Measure ℝ}
    {leftDirectionLaw : Measure (EuclideanSpace ℂ ι)}
    {rightDirectionLaw : Measure (EuclideanSpace ℂ κ)}
    [IsFiniteMeasure μ]
    (I :
      HermitianBlockSphericalRectangularLaw
        (ι := ι) (κ := κ) μ massLaw leftDirectionLaw rightDirectionLaw) :
    Measure.map
        (fun x =>
          (hermitianBlockMass (ι := ι) (κ := κ) x,
            hermitianBlockLeftDirection (ι := ι) (κ := κ) x,
            hermitianBlockRightDirection (ι := ι) (κ := κ) x))
        μ =
      massLaw.prod (leftDirectionLaw.prod rightDirectionLaw) := by
  classical
  letI : SFinite massLaw := I.sfinite_massLaw
  letI : SFinite leftDirectionLaw := I.sfinite_leftDirectionLaw
  letI : SFinite rightDirectionLaw := I.sfinite_rightDirectionLaw
  let T : EuclideanSpace ℂ (Sum ι κ) → ℝ × EuclideanSpace ℂ ι ×
      EuclideanSpace ℂ κ :=
    fun x =>
      (hermitianBlockMass (ι := ι) (κ := κ) x,
        hermitianBlockLeftDirection (ι := ι) (κ := κ) x,
        hermitianBlockRightDirection (ι := ι) (κ := κ) x)
  have hmeas_T : Measurable T := I.measurable_triple
  change Measure.map T μ = massLaw.prod (leftDirectionLaw.prod rightDirectionLaw)
  refine Measure.ext_prod₃
    (μ := Measure.map T μ)
    (ν := massLaw.prod (leftDirectionLaw.prod rightDirectionLaw)) ?_
  intro massSet leftSet rightSet hmass hleft hright
  let rect : Set (ℝ × EuclideanSpace ℂ ι × EuclideanSpace ℂ κ) :=
    massSet ×ˢ (leftSet ×ˢ rightSet)
  have hrect : MeasurableSet rect := hmass.prod (hleft.prod hright)
  have hpre :
      T ⁻¹' rect =
        {x |
          hermitianBlockMass (ι := ι) (κ := κ) x ∈ massSet ∧
            hermitianBlockLeftDirection (ι := ι) (κ := κ) x ∈ leftSet ∧
              hermitianBlockRightDirection (ι := ι) (κ := κ) x ∈ rightSet} := by
    ext x
    simp [T, rect]
  calc
    Measure.map T μ rect = μ (T ⁻¹' rect) := by
      rw [Measure.map_apply hmeas_T hrect]
    _ =
        μ
          {x |
            hermitianBlockMass (ι := ι) (κ := κ) x ∈ massSet ∧
              hermitianBlockLeftDirection (ι := ι) (κ := κ) x ∈ leftSet ∧
                hermitianBlockRightDirection (ι := ι) (κ := κ) x ∈ rightSet} := by
          rw [hpre]
    _ = massLaw massSet * (leftDirectionLaw leftSet * rightDirectionLaw rightSet) := by
          exact I.rect_event_eq hmass hleft hright
    _ = massLaw.prod (leftDirectionLaw.prod rightDirectionLaw) rect := by
          rw [Measure.prod_prod, Measure.prod_prod]

/-- Canonical two-block spherical decomposition: the left-block mass law is
fixed to `Beta(card ι, card κ)`. -/
abbrev CanonicalHermitianBlockSphericalDecompositionIndependence
    (μ : Measure (EuclideanSpace ℂ (Sum ι κ)))
    (leftDirectionLaw : Measure (EuclideanSpace ℂ ι))
    (rightDirectionLaw : Measure (EuclideanSpace ℂ κ)) : Prop :=
  HermitianBlockSphericalDecompositionIndependence
    (ι := ι) (κ := κ) μ
    (hermitianBlockMassBetaMeasure (ι := ι) (κ := κ))
    leftDirectionLaw rightDirectionLaw

/-- Canonical rectangular formulation of the Hermitian block spherical law. -/
abbrev CanonicalHermitianBlockSphericalRectangularLaw
    (μ : Measure (EuclideanSpace ℂ (Sum ι κ)))
    (leftDirectionLaw : Measure (EuclideanSpace ℂ ι))
    (rightDirectionLaw : Measure (EuclideanSpace ℂ κ)) : Prop :=
  HermitianBlockSphericalRectangularLaw
    (ι := ι) (κ := κ) μ
    (hermitianBlockMassBetaMeasure (ι := ι) (κ := κ))
    leftDirectionLaw rightDirectionLaw

/-- The abstract block theorem from a single joint law equality.

This is the theorem to instantiate after proving the genuine spherical
coordinate law for `E ⊕ F`: once the push-forward of

`x ↦ (‖x_E‖², x_E/‖x_E‖, x_F/‖x_F‖)`

is the stated product measure, all marginal laws and rectangular-event
factorizations are available through
`HermitianBlockSphericalDecompositionIndependence`. -/
theorem HermitianBlockSphericalDecompositionIndependence.of_map_triple_eq
    {μ : Measure (EuclideanSpace ℂ (Sum ι κ))}
    {massLaw : Measure ℝ}
    {leftDirectionLaw : Measure (EuclideanSpace ℂ ι)}
    {rightDirectionLaw : Measure (EuclideanSpace ℂ κ)}
    [IsProbabilityMeasure massLaw]
    [IsProbabilityMeasure leftDirectionLaw]
    [IsProbabilityMeasure rightDirectionLaw]
    (hTriple :
      Measure.map
          (fun x =>
            (hermitianBlockMass (ι := ι) (κ := κ) x,
              hermitianBlockLeftDirection (ι := ι) (κ := κ) x,
              hermitianBlockRightDirection (ι := ι) (κ := κ) x))
          μ =
        massLaw.prod (leftDirectionLaw.prod rightDirectionLaw)) :
    HermitianBlockSphericalDecompositionIndependence
      (ι := ι) (κ := κ) μ massLaw leftDirectionLaw rightDirectionLaw := by
  classical
  let mass : EuclideanSpace ℂ (Sum ι κ) → ℝ :=
    hermitianBlockMass (ι := ι) (κ := κ)
  let left : EuclideanSpace ℂ (Sum ι κ) → EuclideanSpace ℂ ι :=
    hermitianBlockLeftDirection (ι := ι) (κ := κ)
  let right : EuclideanSpace ℂ (Sum ι κ) → EuclideanSpace ℂ κ :=
    hermitianBlockRightDirection (ι := ι) (κ := κ)
  have hmeas_mass : Measurable mass :=
    measurable_hermitianBlockMass (ι := ι) (κ := κ)
  have hmeas_left : Measurable left :=
    measurable_hermitianBlockLeftDirection (ι := ι) (κ := κ)
  have hmeas_right : Measurable right :=
    measurable_hermitianBlockRightDirection (ι := ι) (κ := κ)
  have hmeas_triple :
      Measurable (fun x => (mass x, left x, right x)) :=
    hmeas_mass.prod (hmeas_left.prod hmeas_right)
  have hTriple' :
      Measure.map (fun x => (mass x, left x, right x)) μ =
        massLaw.prod (leftDirectionLaw.prod rightDirectionLaw) := by
    simpa [mass, left, right] using hTriple
  refine
    { measurable_mass := hmeas_mass
      measurable_leftDirection := hmeas_left
      measurable_rightDirection := hmeas_right
      sfinite_massLaw := inferInstance
      sfinite_leftDirectionLaw := inferInstance
      sfinite_rightDirectionLaw := inferInstance
      map_mass_eq := ?_
      map_leftDirection_eq := ?_
      map_rightDirection_eq := ?_
      map_triple_eq := hTriple' }
  · calc
      Measure.map mass μ =
          Measure.map (fun z : ℝ × EuclideanSpace ℂ ι × EuclideanSpace ℂ κ => z.1)
            (Measure.map (fun x => (mass x, left x, right x)) μ) := by
            rw [Measure.map_map
              (μ := μ)
              (f := fun x => (mass x, left x, right x))
              (g := fun z : ℝ × EuclideanSpace ℂ ι × EuclideanSpace ℂ κ => z.1)
              measurable_fst hmeas_triple]
            rfl
      _ = Measure.map (fun z : ℝ × EuclideanSpace ℂ ι × EuclideanSpace ℂ κ => z.1)
            (massLaw.prod (leftDirectionLaw.prod rightDirectionLaw)) := by
            rw [hTriple']
      _ = massLaw := by
            simp
  · calc
      Measure.map left μ =
          Measure.map
            (fun z : ℝ × EuclideanSpace ℂ ι × EuclideanSpace ℂ κ => z.2.1)
            (Measure.map (fun x => (mass x, left x, right x)) μ) := by
            rw [Measure.map_map
              (μ := μ)
              (f := fun x => (mass x, left x, right x))
              (g := fun z : ℝ × EuclideanSpace ℂ ι × EuclideanSpace ℂ κ =>
                z.2.1)
              (measurable_fst.comp measurable_snd) hmeas_triple]
            rfl
      _ = Measure.map
            (fun z : ℝ × EuclideanSpace ℂ ι × EuclideanSpace ℂ κ => z.2.1)
            (massLaw.prod (leftDirectionLaw.prod rightDirectionLaw)) := by
            rw [hTriple']
      _ = leftDirectionLaw := by
            calc
              Measure.map
                  (fun z : ℝ × EuclideanSpace ℂ ι × EuclideanSpace ℂ κ =>
                    z.2.1)
                  (massLaw.prod (leftDirectionLaw.prod rightDirectionLaw)) =
                Measure.map
                  (fun z : EuclideanSpace ℂ ι × EuclideanSpace ℂ κ => z.1)
                  (Measure.map
                    (fun z : ℝ × EuclideanSpace ℂ ι × EuclideanSpace ℂ κ =>
                      z.2)
                    (massLaw.prod (leftDirectionLaw.prod rightDirectionLaw))) := by
                  rw [Measure.map_map
                    (μ := massLaw.prod (leftDirectionLaw.prod rightDirectionLaw))
                    (f := fun z : ℝ × EuclideanSpace ℂ ι × EuclideanSpace ℂ κ =>
                      z.2)
                    (g := fun z : EuclideanSpace ℂ ι × EuclideanSpace ℂ κ =>
                      z.1)
                    measurable_fst measurable_snd]
                  rfl
              _ = Measure.map
                  (fun z : EuclideanSpace ℂ ι × EuclideanSpace ℂ κ => z.1)
                  (leftDirectionLaw.prod rightDirectionLaw) := by
                  simp
              _ = leftDirectionLaw := by
                  simp
  · calc
      Measure.map right μ =
          Measure.map
            (fun z : ℝ × EuclideanSpace ℂ ι × EuclideanSpace ℂ κ => z.2.2)
            (Measure.map (fun x => (mass x, left x, right x)) μ) := by
            rw [Measure.map_map
              (μ := μ)
              (f := fun x => (mass x, left x, right x))
              (g := fun z : ℝ × EuclideanSpace ℂ ι × EuclideanSpace ℂ κ =>
                z.2.2)
              (measurable_snd.comp measurable_snd) hmeas_triple]
            rfl
      _ = Measure.map
            (fun z : ℝ × EuclideanSpace ℂ ι × EuclideanSpace ℂ κ => z.2.2)
            (massLaw.prod (leftDirectionLaw.prod rightDirectionLaw)) := by
            rw [hTriple']
      _ = rightDirectionLaw := by
            calc
              Measure.map
                  (fun z : ℝ × EuclideanSpace ℂ ι × EuclideanSpace ℂ κ =>
                    z.2.2)
                  (massLaw.prod (leftDirectionLaw.prod rightDirectionLaw)) =
                Measure.map
                  (fun z : EuclideanSpace ℂ ι × EuclideanSpace ℂ κ => z.2)
                  (Measure.map
                    (fun z : ℝ × EuclideanSpace ℂ ι × EuclideanSpace ℂ κ =>
                      z.2)
                    (massLaw.prod (leftDirectionLaw.prod rightDirectionLaw))) := by
                  rw [Measure.map_map
                    (μ := massLaw.prod (leftDirectionLaw.prod rightDirectionLaw))
                    (f := fun z : ℝ × EuclideanSpace ℂ ι × EuclideanSpace ℂ κ =>
                      z.2)
                    (g := fun z : EuclideanSpace ℂ ι × EuclideanSpace ℂ κ =>
                      z.2)
                    measurable_snd measurable_snd]
                  rfl
              _ = Measure.map
                  (fun z : EuclideanSpace ℂ ι × EuclideanSpace ℂ κ => z.2)
                  (leftDirectionLaw.prod rightDirectionLaw) := by
                  simp
              _ = rightDirectionLaw := by
                  simp

/-- Packaging theorem: a rectangular Hermitian block law is enough to obtain
the full decomposition-and-independence structure. -/
theorem HermitianBlockSphericalDecompositionIndependence.of_rectangularLaw
    {μ : Measure (EuclideanSpace ℂ (Sum ι κ))}
    {massLaw : Measure ℝ}
    {leftDirectionLaw : Measure (EuclideanSpace ℂ ι)}
    {rightDirectionLaw : Measure (EuclideanSpace ℂ κ)}
    [IsFiniteMeasure μ]
    [IsProbabilityMeasure massLaw]
    [IsProbabilityMeasure leftDirectionLaw]
    [IsProbabilityMeasure rightDirectionLaw]
    (I :
      HermitianBlockSphericalRectangularLaw
        (ι := ι) (κ := κ) μ massLaw leftDirectionLaw rightDirectionLaw) :
    HermitianBlockSphericalDecompositionIndependence
      (ι := ι) (κ := κ) μ massLaw leftDirectionLaw rightDirectionLaw :=
  HermitianBlockSphericalDecompositionIndependence.of_map_triple_eq
    (ι := ι) (κ := κ) I.map_triple_eq

/-- Canonical version of the abstract block theorem: the mass law is fixed to
`Beta(card ι, card κ)`. -/
theorem CanonicalHermitianBlockSphericalDecompositionIndependence.of_map_triple_eq
    {μ : Measure (EuclideanSpace ℂ (Sum ι κ))}
    {leftDirectionLaw : Measure (EuclideanSpace ℂ ι)}
    {rightDirectionLaw : Measure (EuclideanSpace ℂ κ)}
    [IsProbabilityMeasure (hermitianBlockMassBetaMeasure (ι := ι) (κ := κ))]
    [IsProbabilityMeasure leftDirectionLaw]
    [IsProbabilityMeasure rightDirectionLaw]
    (hTriple :
      Measure.map
          (fun x =>
            (hermitianBlockMass (ι := ι) (κ := κ) x,
              hermitianBlockLeftDirection (ι := ι) (κ := κ) x,
              hermitianBlockRightDirection (ι := ι) (κ := κ) x))
          μ =
        (hermitianBlockMassBetaMeasure (ι := ι) (κ := κ)).prod
          (leftDirectionLaw.prod rightDirectionLaw)) :
    CanonicalHermitianBlockSphericalDecompositionIndependence
      (ι := ι) (κ := κ) μ leftDirectionLaw rightDirectionLaw :=
  HermitianBlockSphericalDecompositionIndependence.of_map_triple_eq
    (ι := ι) (κ := κ) hTriple

/-- Canonical packaging theorem from measurable rectangles to the full
Hermitian two-block spherical decomposition. -/
theorem CanonicalHermitianBlockSphericalDecompositionIndependence.of_rectangularLaw
    {μ : Measure (EuclideanSpace ℂ (Sum ι κ))}
    {leftDirectionLaw : Measure (EuclideanSpace ℂ ι)}
    {rightDirectionLaw : Measure (EuclideanSpace ℂ κ)}
    [IsFiniteMeasure μ]
    [IsProbabilityMeasure (hermitianBlockMassBetaMeasure (ι := ι) (κ := κ))]
    [IsProbabilityMeasure leftDirectionLaw]
    [IsProbabilityMeasure rightDirectionLaw]
    (I :
      CanonicalHermitianBlockSphericalRectangularLaw
        (ι := ι) (κ := κ) μ leftDirectionLaw rightDirectionLaw) :
    CanonicalHermitianBlockSphericalDecompositionIndependence
      (ι := ι) (κ := κ) μ leftDirectionLaw rightDirectionLaw :=
  HermitianBlockSphericalDecompositionIndependence.of_rectangularLaw
    (ι := ι) (κ := κ) I

theorem measure_prod_hermitianBlockProductCone_univ_eq_ball
    [Nonempty ι] [Nonempty κ] :
    ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).prod
        (MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)))
      (hermitianBlockProductCone
        (ι := ι) (κ := κ) Set.univ Set.univ Set.univ) =
    (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ)))
      (Metric.ball (0 : EuclideanSpace ℂ (Sum ι κ)) 1) := by
  let μprod : Measure (EuclideanSpace ℂ ι × EuclideanSpace ℂ κ) :=
    (MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).prod
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ κ))
  let B : Set (EuclideanSpace ℂ ι × EuclideanSpace ℂ κ) :=
    {x | ‖x.1‖ ^ 2 + ‖x.2‖ ^ 2 < 1}
  have hConeSub :
      hermitianBlockProductCone
          (ι := ι) (κ := κ) Set.univ Set.univ Set.univ ⊆ B := by
    intro x hx
    exact hx.2.2.2.2
  have hBallSub :
      B ⊆
        hermitianBlockProductCone
            (ι := ι) (κ := κ) Set.univ Set.univ Set.univ ∪
          hermitianBlockProductAxes (ι := ι) (κ := κ) := by
    intro x hx
    by_cases haxes : x ∈ hermitianBlockProductAxes (ι := ι) (κ := κ)
    · exact Or.inr haxes
    · exact Or.inl ⟨haxes, by simp, by simp, by simp, hx⟩
  have haxes0 :
      μprod (hermitianBlockProductAxes (ι := ι) (κ := κ)) = 0 := by
    simpa [μprod] using
      measure_prod_hermitianBlockProductAxes_eq_zero
        (ι := ι) (κ := κ)
  have hConeEq :
      μprod
          (hermitianBlockProductCone
            (ι := ι) (κ := κ) Set.univ Set.univ Set.univ) =
        μprod B := by
    apply le_antisymm
    · exact measure_mono hConeSub
    · calc
        μprod B ≤
            μprod
              (hermitianBlockProductCone
                  (ι := ι) (κ := κ) Set.univ Set.univ Set.univ ∪
                hermitianBlockProductAxes (ι := ι) (κ := κ)) :=
            measure_mono hBallSub
        _ ≤
            μprod
                (hermitianBlockProductCone
                  (ι := ι) (κ := κ) Set.univ Set.univ Set.univ) +
              μprod (hermitianBlockProductAxes (ι := ι) (κ := κ)) := by
              exact measure_union_le _ _
        _ =
            μprod
              (hermitianBlockProductCone
                (ι := ι) (κ := κ) Set.univ Set.univ Set.univ) := by
              rw [haxes0, add_zero]
  have hBMeas : MeasurableSet B := by
    have hballMeas :
        Measurable
          (fun x : EuclideanSpace ℂ ι × EuclideanSpace ℂ κ =>
            ‖x.1‖ ^ 2 + ‖x.2‖ ^ 2) := by
      fun_prop
    exact measurableSet_lt hballMeas measurable_const
  have hpreBall :
      (hermitianBlockSumEquivProd (ι := ι) (κ := κ)) ⁻¹' B =
        Metric.ball (0 : EuclideanSpace ℂ (Sum ι κ)) 1 := by
    ext x
    constructor
    · intro hx
      have hx' :
          ‖hermitianBlockLeft (ι := ι) (κ := κ) x‖ ^ 2 +
            ‖hermitianBlockRight (ι := ι) (κ := κ) x‖ ^ 2 < 1 := by
        simpa [B, hermitianBlockSumEquivProd_fst, hermitianBlockSumEquivProd_snd]
          using hx
      have hnormsq := hermitianBlock_norm_sq_eq_add (ι := ι) (κ := κ) x
      have : ‖x‖ ^ 2 < 1 := by
        simpa [hnormsq] using hx'
      simp [Metric.mem_ball, dist_eq_norm]
      nlinarith [norm_nonneg x]
    · intro hx
      have hxsq : ‖x‖ ^ 2 < 1 := by
        simp [Metric.mem_ball, dist_eq_norm] at hx
        nlinarith [hx, norm_nonneg x]
      have hsum :
          ‖hermitianBlockLeft (ι := ι) (κ := κ) x‖ ^ 2 +
            ‖hermitianBlockRight (ι := ι) (κ := κ) x‖ ^ 2 < 1 := by
        simpa [hermitianBlock_norm_sq_eq_add (ι := ι) (κ := κ) x] using hxsq
      simpa [B, hermitianBlockSumEquivProd_fst, hermitianBlockSumEquivProd_snd]
        using hsum
  calc
    μprod
        (hermitianBlockProductCone
          (ι := ι) (κ := κ) Set.univ Set.univ Set.univ) = μprod B := hConeEq
    _ =
        (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ)))
          ((hermitianBlockSumEquivProd (ι := ι) (κ := κ)) ⁻¹' B) := by
          simpa [μprod] using
            (volume_preimage_hermitianBlockSumEquivProd
              (ι := ι) (κ := κ) (s := B) hBMeas).symm
    _ =
        (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ)))
          (Metric.ball (0 : EuclideanSpace ℂ (Sum ι κ)) 1) := by
          rw [hpreBall]

theorem hermitianBlockAmbientBall_eq_directionTotals_mul_radialNormalization
    [Nonempty ι] [Nonempty κ]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere)]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)).toSphere)] :
    (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ)))
        (Metric.ball (0 : EuclideanSpace ℂ (Sum ι κ)) 1) =
      (((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere
          (Set.univ : Set (Metric.sphere (0 : EuclideanSpace ℂ ι) 1))) *
        ((MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)).toSphere
          (Set.univ : Set (Metric.sphere (0 : EuclideanSpace ℂ κ) 1)))) *
        hermitianBlockRadialNormalization (ι := ι) (κ := κ) := by
  calc
    (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ)))
        (Metric.ball (0 : EuclideanSpace ℂ (Sum ι κ)) 1) =
      ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).prod
          (MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)))
        (hermitianBlockProductCone
          (ι := ι) (κ := κ) Set.univ Set.univ Set.univ) := by
          exact
            (measure_prod_hermitianBlockProductCone_univ_eq_ball
              (ι := ι) (κ := κ)).symm
    _ =
      hermitianBlockFactorPolarMeasure (ι := ι) (κ := κ)
        (hermitianBlockFactorPolarSet
          (ι := ι) (κ := κ) Set.univ Set.univ Set.univ) := by
          rw [measure_prod_hermitianBlockProductCone_eq_factorPolarMeasure
            (ι := ι) (κ := κ)
            (massSet := Set.univ) (leftSet := Set.univ) (rightSet := Set.univ)
            MeasurableSet.univ MeasurableSet.univ MeasurableSet.univ]
    _ =
      (((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere
          (Set.univ : Set (Metric.sphere (0 : EuclideanSpace ℂ ι) 1))) *
        ((MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)).toSphere
          (Set.univ : Set (Metric.sphere (0 : EuclideanSpace ℂ κ) 1)))) *
        hermitianBlockRadialNormalization (ι := ι) (κ := κ) := by
          simpa [hermitianBlockLeftSphereTrace, hermitianBlockRightSphereTrace,
            hermitianBlockRadialMassSet, hermitianBlockRadialNormalization] using
            (hermitianBlockFactorPolarMeasure_rect
              (ι := ι) (κ := κ)
              (massSet := Set.univ) (leftSet := Set.univ)
              (rightSet := Set.univ))

/-- Transport the Gaussian block-mass ratio law to the sphere by global
normalization.

For `X = G / ‖G‖` with `G` standard complex Gaussian on `ℂ^(ι ⊕ κ)`, the left
block mass

`hermitianBlockMass X = ‖X_E‖²`

is exactly the Gamma/Gamma ratio

`‖G_E‖² / (‖G_E‖² + ‖G_F‖²)`,

so its spherical law is the canonical `Beta(card ι, card κ)` law. -/
theorem hermitianBlockMass_map_surfaceMeasureAmbient_eq_beta
    [Nonempty ι] [Nonempty κ]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ))).toSphere)] :
    Measure.map (hermitianBlockMass (ι := ι) (κ := κ))
        (surfaceMeasureAmbient (Sum ι κ)) =
      hermitianBlockMassBetaMeasure (ι := ι) (κ := κ) := by
  let μG :=
    PptFactorization.GaussianModel.standardComplexGaussianVectorMeasure
      (Sum ι κ)
  have hsurf :
      Measure.map (hermitianBlockNormalize (η := Sum ι κ)) μG =
        surfaceMeasureAmbient (Sum ι κ) := by
    simpa [hermitianBlockNormalize] using
      (standardComplexGaussian_direction_hasLaw_surfaceMeasureAmbient
        (η := Sum ι κ))
  calc
    Measure.map (hermitianBlockMass (ι := ι) (κ := κ))
        (surfaceMeasureAmbient (Sum ι κ)) =
      Measure.map (hermitianBlockMass (ι := ι) (κ := κ))
        (Measure.map (hermitianBlockNormalize (η := Sum ι κ)) μG) := by
        rw [hsurf.symm]
    _ =
      Measure.map
        (fun g : EuclideanSpace ℂ (Sum ι κ) =>
          hermitianBlockMass (ι := ι) (κ := κ)
            (hermitianBlockNormalize (η := Sum ι κ) g))
        μG := by
        simpa [Function.comp] using
          (Measure.map_map
            (μ := μG)
            (f := hermitianBlockNormalize (η := Sum ι κ))
            (g := hermitianBlockMass (ι := ι) (κ := κ))
            (measurable_hermitianBlockMass (ι := ι) (κ := κ))
            (measurable_hermitianBlockNormalize (η := Sum ι κ)))
    _ =
      Measure.map
        (fun g : EuclideanSpace ℂ (Sum ι κ) =>
          ‖hermitianBlockLeft (ι := ι) (κ := κ) g‖ ^ 2 /
            (‖hermitianBlockLeft (ι := ι) (κ := κ) g‖ ^ 2 +
              ‖hermitianBlockRight (ι := ι) (κ := κ) g‖ ^ 2))
        μG := by
        apply Measure.map_congr
        exact
          hermitianBlockMass_comp_hermitianBlockNormalize_ae_eq_gaussianBlockMassRatio
            (ι := ι) (κ := κ)
    _ = hermitianBlockMassBetaMeasure (ι := ι) (κ := κ) := by
        simpa [μG] using
          (gaussianBlockMassRatio_hasLaw_beta (ι := ι) (κ := κ)).map_eq

/-- Scalar change-of-variables input for the block cone.

This is the dedicated analytic statement left by the separate-polar reduction:
the push-forward of the radial cone measure by
`t = r_E^2 / (r_E^2 + r_F^2)` is its total radial mass times the normalized
Beta law with parameters `(card ι, card κ)`. -/
theorem hermitianBlockRadialMassSet_measure_eq_normalization_mul_beta
    [Nonempty ι] [Nonempty κ]
    [SFinite
      ((MeasureTheory.volume :
        Measure (EuclideanSpace ℂ (Sum ι κ))).toSphere)]
    [SFinite
      ((MeasureTheory.volume :
        Measure (EuclideanSpace ℂ ι)).toSphere)]
    [SFinite
      ((MeasureTheory.volume :
        Measure (EuclideanSpace ℂ κ)).toSphere)]
    {massSet : Set ℝ}
    (hmass : MeasurableSet massSet) :
    hermitianBlockRadialProductMeasure (ι := ι) (κ := κ)
        (hermitianBlockRadialMassSet massSet) =
      hermitianBlockRadialNormalization (ι := ι) (κ := κ) *
        hermitianBlockMassBetaMeasure (ι := ι) (κ := κ) massSet := by
  let eventSet : Set (EuclideanSpace ℂ (Sum ι κ)) :=
    (hermitianBlockMass (ι := ι) (κ := κ)) ⁻¹' massSet
  let ballVol : ℝ≥0∞ :=
    (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ)))
      (Metric.ball (0 : EuclideanSpace ℂ (Sum ι κ)) 1)
  let leftTot : ℝ≥0∞ :=
    (MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere
      (Set.univ : Set (Metric.sphere (0 : EuclideanSpace ℂ ι) 1))
  let rightTot : ℝ≥0∞ :=
    (MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)).toSphere
      (Set.univ : Set (Metric.sphere (0 : EuclideanSpace ℂ κ) 1))
  let dirTot : ℝ≥0∞ := leftTot * rightTot
  let radialMass : ℝ≥0∞ :=
    hermitianBlockRadialProductMeasure (ι := ι) (κ := κ)
      (hermitianBlockRadialMassSet massSet)
  let radNorm : ℝ≥0∞ :=
    hermitianBlockRadialNormalization (ι := ι) (κ := κ)
  let betaMass : ℝ≥0∞ :=
    hermitianBlockMassBetaMeasure (ι := ι) (κ := κ) massSet
  have hmeasEvent : MeasurableSet eventSet := by
    exact (measurable_hermitianBlockMass (ι := ι) (κ := κ)) hmass
  have hpreEvent :
      ((Subtype.val :
          Metric.sphere (0 : EuclideanSpace ℂ (Sum ι κ)) 1 →
            EuclideanSpace ℂ (Sum ι κ)) ⁻¹' eventSet) =
        hermitianBlockRectSphereSet
          (ι := ι) (κ := κ) massSet Set.univ Set.univ := by
    ext x
    simp [eventSet, hermitianBlockRectSphereSet]
  have hmapMass :
      surfaceMeasureAmbient (Sum ι κ) eventSet = betaMass := by
    simpa [eventSet, betaMass,
      Measure.map_apply
        (measurable_hermitianBlockMass (ι := ι) (κ := κ)) hmass] using
      congrArg (fun ν : Measure ℝ => ν massSet)
        (hermitianBlockMass_map_surfaceMeasureAmbient_eq_beta
          (ι := ι) (κ := κ))
  have hsurfEvent :
      surfaceMeasureAmbient (Sum ι κ) eventSet =
        ballVol⁻¹ * (dirTot * radialMass) := by
    calc
      surfaceMeasureAmbient (Sum ι κ) eventSet =
        surfaceMeasure (Sum ι κ)
          (hermitianBlockRectSphereSet
            (ι := ι) (κ := κ) massSet Set.univ Set.univ) := by
          rw [surfaceMeasureAmbient,
            Measure.map_apply measurable_subtype_coe hmeasEvent, hpreEvent]
      _ =
        ballVol⁻¹ *
          (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ)))
            (hermitianBlockRectCone
              (ι := ι) (κ := κ) massSet Set.univ Set.univ) := by
          exact
            surfaceMeasure_hermitianBlockRectSphereSet_eq_cone_volume_ratio
              (ι := ι) (κ := κ) hmass MeasurableSet.univ MeasurableSet.univ
      _ =
        ballVol⁻¹ *
          (((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere
                (Set.univ : Set (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)) *
              (MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)).toSphere
                (Set.univ : Set (Metric.sphere (0 : EuclideanSpace ℂ κ) 1))) *
            radialMass) := by
          congr 1
          calc
            (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ)))
                (hermitianBlockRectCone
                  (ι := ι) (κ := κ) massSet Set.univ Set.univ) =
              ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).prod
                  (MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)))
                (hermitianBlockProductCone
                  (ι := ι) (κ := κ) massSet Set.univ Set.univ) := by
                rw [hermitianBlockRectCone_ae_eq_productCone
                  (ι := ι) (κ := κ) massSet Set.univ Set.univ]
                exact
                  volume_preimage_hermitianBlockSumEquivProd
                    (ι := ι) (κ := κ)
                    (s := hermitianBlockProductCone
                      (ι := ι) (κ := κ) massSet Set.univ Set.univ)
                    (measurableSet_hermitianBlockProductCone
                      (ι := ι) (κ := κ) hmass MeasurableSet.univ
                        MeasurableSet.univ)
            _ =
              hermitianBlockFactorPolarMeasure (ι := ι) (κ := κ)
                (hermitianBlockFactorPolarSet
                  (ι := ι) (κ := κ) massSet Set.univ Set.univ) := by
                rw [measure_prod_hermitianBlockProductCone_eq_factorPolarMeasure
                  (ι := ι) (κ := κ)
                  (massSet := massSet) (leftSet := Set.univ)
                  (rightSet := Set.univ)
                  hmass MeasurableSet.univ MeasurableSet.univ]
            _ =
              (((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere
                    (Set.univ : Set (Metric.sphere (0 : EuclideanSpace ℂ ι) 1))) *
                ((MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)).toSphere
                  (Set.univ : Set (Metric.sphere (0 : EuclideanSpace ℂ κ) 1)))) *
                radialMass := by
                simpa [radialMass, hermitianBlockLeftSphereTrace,
                  hermitianBlockRightSphereTrace, hermitianBlockRadialMassSet]
                  using
                    (hermitianBlockFactorPolarMeasure_rect
                      (ι := ι) (κ := κ)
                      (massSet := massSet) (leftSet := Set.univ)
                      (rightSet := Set.univ))
      _ = ballVol⁻¹ * (dirTot * radialMass) := by
          rfl
  have hball0 : ballVol ≠ 0 := by
    dsimp [ballVol]
    exact Metric.isOpen_ball.measure_ne_zero
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ))) ⟨0, by simp⟩
  have hballt : ballVol ≠ ∞ := by
    dsimp [ballVol]
    exact ne_of_lt <|
      lt_of_le_of_lt
        (measure_mono Metric.ball_subset_closedBall)
        ((isCompact_closedBall
          (0 : EuclideanSpace ℂ (Sum ι κ)) 1).measure_lt_top)
  have hleft0 : leftTot ≠ 0 := by
    dsimp [leftTot]
    have hne :
        ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere) ≠ 0 := by
      simpa using
        (Measure.toSphere_ne_zero
          (μ := (MeasureTheory.volume : Measure (EuclideanSpace ℂ ι))))
    exact mt (Measure.measure_univ_eq_zero (μ :=
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere)).1 hne
  have hright0 : rightTot ≠ 0 := by
    dsimp [rightTot]
    have hne :
        ((MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)).toSphere) ≠ 0 := by
      simpa using
        (Measure.toSphere_ne_zero
          (μ := (MeasureTheory.volume : Measure (EuclideanSpace ℂ κ))))
    exact mt (Measure.measure_univ_eq_zero (μ :=
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)).toSphere)).1 hne
  have hleftt : leftTot ≠ ∞ := by
    dsimp [leftTot]
    have hball_lt :
        (MeasureTheory.volume : Measure (EuclideanSpace ℂ ι))
          (Metric.ball (0 : EuclideanSpace ℂ ι) 1) < ∞ := by
      exact lt_of_le_of_lt
        (measure_mono Metric.ball_subset_closedBall)
        ((isCompact_closedBall (0 : EuclideanSpace ℂ ι) 1).measure_lt_top)
    rw [Measure.toSphere_apply_univ
      (μ := (MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)))]
    exact ne_of_lt <| ENNReal.mul_lt_top (by simp) hball_lt
  have hrightt : rightTot ≠ ∞ := by
    dsimp [rightTot]
    have hball_lt :
        (MeasureTheory.volume : Measure (EuclideanSpace ℂ κ))
          (Metric.ball (0 : EuclideanSpace ℂ κ) 1) < ∞ := by
      exact lt_of_le_of_lt
        (measure_mono Metric.ball_subset_closedBall)
        ((isCompact_closedBall (0 : EuclideanSpace ℂ κ) 1).measure_lt_top)
    rw [Measure.toSphere_apply_univ
      (μ := (MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)))]
    exact ne_of_lt <| ENNReal.mul_lt_top (by simp) hball_lt
  have hdir0 : dirTot ≠ 0 := by
    dsimp [dirTot]
    exact mul_ne_zero hleft0 hright0
  have hdirt : dirTot ≠ ∞ := by
    dsimp [dirTot]
    exact ne_of_lt <|
      ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hleftt)
        (lt_top_iff_ne_top.mpr hrightt)
  have hnorm :
      ballVol = dirTot * radNorm := by
    dsimp [ballVol, dirTot, leftTot, rightTot, radNorm]
    simpa [mul_assoc] using
      (hermitianBlockAmbientBall_eq_directionTotals_mul_radialNormalization
        (ι := ι) (κ := κ))
  have hbetaEq : betaMass = ballVol⁻¹ * (dirTot * radialMass) := by
    rw [← hmapMass]
    exact hsurfEvent
  have hmul :
      ballVol * betaMass = dirTot * radialMass := by
    calc
      ballVol * betaMass =
        ballVol * (ballVol⁻¹ * (dirTot * radialMass)) := by
          rw [hbetaEq]
      _ = (ballVol * ballVol⁻¹) * (dirTot * radialMass) := by
          ac_rfl
      _ = dirTot * radialMass := by
          rw [ENNReal.mul_inv_cancel hball0 hballt, one_mul]
  have hcancel :
      dirTot * (radNorm * betaMass) = dirTot * radialMass := by
    calc
      dirTot * (radNorm * betaMass) = (dirTot * radNorm) * betaMass := by
        ac_rfl
      _ = ballVol * betaMass := by
        rw [hnorm]
      _ = dirTot * radialMass := hmul
  calc
    hermitianBlockRadialProductMeasure (ι := ι) (κ := κ)
        (hermitianBlockRadialMassSet massSet) = radialMass := by
      rfl
    _ = (dirTot⁻¹ * dirTot) * radialMass := by
      rw [ENNReal.inv_mul_cancel hdir0 hdirt, one_mul]
    _ = dirTot⁻¹ * (dirTot * radialMass) := by
      ac_rfl
    _ = dirTot⁻¹ * (dirTot * (radNorm * betaMass)) := by
      rw [hcancel]
    _ = (dirTot⁻¹ * dirTot) * (radNorm * betaMass) := by
      ac_rfl
    _ = radNorm * betaMass := by
      rw [ENNReal.inv_mul_cancel hdir0 hdirt, one_mul]
    _ =
        hermitianBlockRadialNormalization (ι := ι) (κ := κ) *
          hermitianBlockMassBetaMeasure (ι := ι) (κ := κ) massSet := by
      rfl

/-- Scalar change-of-variables input for the block cone, now obtained from the
mass law on the ambient sphere together with the factorized cone-volume
formula. -/
theorem hermitianBlockRadialMassMeasure_eq_normalization_smul_beta
    [Nonempty ι] [Nonempty κ]
    [SFinite
      ((MeasureTheory.volume :
        Measure (EuclideanSpace ℂ (Sum ι κ))).toSphere)]
    [SFinite
      ((MeasureTheory.volume :
        Measure (EuclideanSpace ℂ ι)).toSphere)]
    [SFinite
      ((MeasureTheory.volume :
        Measure (EuclideanSpace ℂ κ)).toSphere)] :
    hermitianBlockRadialMassMeasure (ι := ι) (κ := κ) =
      hermitianBlockRadialNormalization (ι := ι) (κ := κ) •
        hermitianBlockMassBetaMeasure (ι := ι) (κ := κ) := by
  ext massSet hmass
  calc
    hermitianBlockRadialMassMeasure (ι := ι) (κ := κ) massSet =
      hermitianBlockRadialProductMeasure (ι := ι) (κ := κ)
        (hermitianBlockRadialMassSet massSet) := by
        exact hermitianBlockRadialMassMeasure_apply
          (ι := ι) (κ := κ) hmass
    _ =
      hermitianBlockRadialNormalization (ι := ι) (κ := κ) *
        hermitianBlockMassBetaMeasure (ι := ι) (κ := κ) massSet := by
        exact hermitianBlockRadialMassSet_measure_eq_normalization_mul_beta
          (ι := ι) (κ := κ) hmass
    _ =
      (hermitianBlockRadialNormalization (ι := ι) (κ := κ) •
        hermitianBlockMassBetaMeasure (ι := ι) (κ := κ)) massSet := by
        simp [Measure.smul_apply, smul_eq_mul]

set_option linter.unusedSectionVars false in
/-- Rectangular no-input Hermitian two-block spherical law on `ℂ^ι ⊕ ℂ^κ`.

Under the canonical uniform surface law on the unit sphere of
`EuclideanSpace ℂ (Sum ι κ)`, measurable block rectangles factor as

`Beta(card ι, card κ) × σ_ι × σ_κ`.

This is the analytic core: it is the rectangle statement from which the full
product law of the block triple is derived below. -/
theorem canonicalHermitianBlockSphericalRectangularLaw_noInput
    [Nonempty ι] [Nonempty κ]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ))).toSphere)]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere)]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)).toSphere)] :
    CanonicalHermitianBlockSphericalRectangularLaw
      (ι := ι) (κ := κ)
      (surfaceMeasureAmbient (Sum ι κ))
      (surfaceMeasureAmbient ι)
      (surfaceMeasureAmbient κ) := by
  letI : IsProbabilityMeasure
      (hermitianBlockMassBetaMeasure (ι := ι) (κ := κ)) :=
    hermitianBlockMassBetaMeasure_isProbabilityMeasure
      (ι := ι) (κ := κ)
  refine
    { measurable_mass := measurable_hermitianBlockMass (ι := ι) (κ := κ)
      measurable_leftDirection :=
        measurable_hermitianBlockLeftDirection (ι := ι) (κ := κ)
      measurable_rightDirection :=
        measurable_hermitianBlockRightDirection (ι := ι) (κ := κ)
      sfinite_massLaw := inferInstance
      sfinite_leftDirectionLaw := inferInstance
      sfinite_rightDirectionLaw := inferInstance
      rect_event_eq := ?_ }
  intro massSet leftSet rightSet hmass hleft hright
  let eventSet : Set (EuclideanSpace ℂ (Sum ι κ)) :=
    {x |
      hermitianBlockMass (ι := ι) (κ := κ) x ∈ massSet ∧
        hermitianBlockLeftDirection (ι := ι) (κ := κ) x ∈ leftSet ∧
          hermitianBlockRightDirection (ι := ι) (κ := κ) x ∈ rightSet}
  have hmeasEvent : MeasurableSet eventSet := by
    exact
      ((measurable_hermitianBlockMass (ι := ι) (κ := κ)) hmass).inter
        (((measurable_hermitianBlockLeftDirection (ι := ι) (κ := κ)) hleft).inter
          ((measurable_hermitianBlockRightDirection (ι := ι) (κ := κ)) hright))
  have hpreEvent :
      ((Subtype.val :
          Metric.sphere (0 : EuclideanSpace ℂ (Sum ι κ)) 1 →
            EuclideanSpace ℂ (Sum ι κ)) ⁻¹' eventSet) =
        hermitianBlockRectSphereSet
          (ι := ι) (κ := κ) massSet leftSet rightSet := by
    ext x
    simp [eventSet, hermitianBlockRectSphereSet]
  have hconeEq :
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ)))
        (hermitianBlockRectCone
          (ι := ι) (κ := κ) massSet leftSet rightSet) =
      ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).prod
          (MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)))
        (hermitianBlockProductCone
          (ι := ι) (κ := κ) massSet leftSet rightSet) := by
    calc
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ)))
          (hermitianBlockRectCone
            (ι := ι) (κ := κ) massSet leftSet rightSet) =
        (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ)))
          ((hermitianBlockSumEquivProd (ι := ι) (κ := κ)) ⁻¹'
            hermitianBlockProductCone
              (ι := ι) (κ := κ) massSet leftSet rightSet) := by
            rw [hermitianBlockRectCone_ae_eq_productCone
              (ι := ι) (κ := κ) massSet leftSet rightSet]
      _ =
        ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).prod
            (MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)))
          (hermitianBlockProductCone
            (ι := ι) (κ := κ) massSet leftSet rightSet) := by
            exact
              volume_preimage_hermitianBlockSumEquivProd
                (ι := ι) (κ := κ)
                (s := hermitianBlockProductCone
                  (ι := ι) (κ := κ) massSet leftSet rightSet)
                (measurableSet_hermitianBlockProductCone
                  (ι := ι) (κ := κ) hmass hleft hright)
  have hleftTrace :
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere
          (hermitianBlockLeftSphereTrace (ι := ι) leftSet) =
        (MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere
            (Set.univ : Set (Metric.sphere (0 : EuclideanSpace ℂ ι) 1)) *
          surfaceMeasureAmbient ι leftSet := by
    simpa [hermitianBlockLeftSphereTrace] using
      (toSphere_preimage_eq_total_mul_surfaceMeasureAmbient
        (ι := ι) (s := leftSet) hleft)
  have hrightTrace :
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)).toSphere
          (hermitianBlockRightSphereTrace (κ := κ) rightSet) =
        (MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)).toSphere
            (Set.univ : Set (Metric.sphere (0 : EuclideanSpace ℂ κ) 1)) *
          surfaceMeasureAmbient κ rightSet := by
    simpa [hermitianBlockRightSphereTrace] using
      (toSphere_preimage_eq_total_mul_surfaceMeasureAmbient
        (ι := κ) (s := rightSet) hright)
  have hball0 :
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ)))
        (Metric.ball (0 : EuclideanSpace ℂ (Sum ι κ)) 1) ≠ 0 := by
    exact Metric.isOpen_ball.measure_ne_zero
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ))) ⟨0, by simp⟩
  have hballt :
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ)))
        (Metric.ball (0 : EuclideanSpace ℂ (Sum ι κ)) 1) ≠ ∞ := by
    exact ne_of_lt <|
      lt_of_le_of_lt
        (measure_mono Metric.ball_subset_closedBall)
        ((isCompact_closedBall
          (0 : EuclideanSpace ℂ (Sum ι κ)) 1).measure_lt_top)
  calc
    surfaceMeasureAmbient (Sum ι κ) eventSet =
      surfaceMeasure (Sum ι κ)
        (hermitianBlockRectSphereSet
          (ι := ι) (κ := κ) massSet leftSet rightSet) := by
        rw [surfaceMeasureAmbient,
          Measure.map_apply measurable_subtype_coe hmeasEvent, hpreEvent]
    _ =
      ((MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ)))
          (Metric.ball (0 : EuclideanSpace ℂ (Sum ι κ)) 1))⁻¹ *
        (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ)))
          (hermitianBlockRectCone
            (ι := ι) (κ := κ) massSet leftSet rightSet) := by
        exact
          surfaceMeasure_hermitianBlockRectSphereSet_eq_cone_volume_ratio
            (ι := ι) (κ := κ) hmass hleft hright
    _ =
      ((MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ)))
          (Metric.ball (0 : EuclideanSpace ℂ (Sum ι κ)) 1))⁻¹ *
        ((((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere
              (hermitianBlockLeftSphereTrace (ι := ι) leftSet)) *
            ((MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)).toSphere
              (hermitianBlockRightSphereTrace (κ := κ) rightSet))) *
          (hermitianBlockRadialNormalization (ι := ι) (κ := κ) *
            hermitianBlockMassBetaMeasure (ι := ι) (κ := κ) massSet)) := by
        congr 1
        calc
          (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ)))
              (hermitianBlockRectCone
                (ι := ι) (κ := κ) massSet leftSet rightSet) =
            ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).prod
                (MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)))
              (hermitianBlockProductCone
                (ι := ι) (κ := κ) massSet leftSet rightSet) := hconeEq
          _ =
            hermitianBlockFactorPolarMeasure (ι := ι) (κ := κ)
              (hermitianBlockFactorPolarSet
                (ι := ι) (κ := κ) massSet leftSet rightSet) := by
              rw [measure_prod_hermitianBlockProductCone_eq_factorPolarMeasure
                (ι := ι) (κ := κ)
                (massSet := massSet) (leftSet := leftSet)
                (rightSet := rightSet) hmass hleft hright]
          _ =
            (((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere
                  (hermitianBlockLeftSphereTrace (ι := ι) leftSet)) *
                ((MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)).toSphere
                  (hermitianBlockRightSphereTrace (κ := κ) rightSet))) *
              hermitianBlockRadialProductMeasure (ι := ι) (κ := κ)
                (hermitianBlockRadialMassSet massSet) := by
              exact hermitianBlockFactorPolarMeasure_rect
                (ι := ι) (κ := κ)
          _ =
            (((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere
                  (hermitianBlockLeftSphereTrace (ι := ι) leftSet)) *
                ((MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)).toSphere
                  (hermitianBlockRightSphereTrace (κ := κ) rightSet))) *
              (hermitianBlockRadialNormalization (ι := ι) (κ := κ) *
                hermitianBlockMassBetaMeasure (ι := ι) (κ := κ) massSet) := by
              rw [hermitianBlockRadialMassSet_measure_eq_normalization_mul_beta
                (ι := ι) (κ := κ) hmass]
    _ =
      hermitianBlockMassBetaMeasure (ι := ι) (κ := κ) massSet *
        (surfaceMeasureAmbient ι leftSet *
          surfaceMeasureAmbient κ rightSet) := by
        rw [hleftTrace, hrightTrace]
        let ballVol : ℝ≥0∞ :=
          (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ)))
            (Metric.ball (0 : EuclideanSpace ℂ (Sum ι κ)) 1)
        let leftTot : ℝ≥0∞ :=
          (MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere
            (Set.univ : Set (Metric.sphere (0 : EuclideanSpace ℂ ι) 1))
        let rightTot : ℝ≥0∞ :=
          (MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)).toSphere
            (Set.univ : Set (Metric.sphere (0 : EuclideanSpace ℂ κ) 1))
        let surfL : ℝ≥0∞ := surfaceMeasureAmbient ι leftSet
        let surfR : ℝ≥0∞ := surfaceMeasureAmbient κ rightSet
        let radNorm : ℝ≥0∞ :=
          hermitianBlockRadialNormalization (ι := ι) (κ := κ)
        let betaMass : ℝ≥0∞ :=
          hermitianBlockMassBetaMeasure (ι := ι) (κ := κ) massSet
        have hnorm :=
          show ballVol = (leftTot * rightTot) * radNorm by
            dsimp [ballVol, leftTot, rightTot, radNorm]
            simpa [mul_assoc] using
              (hermitianBlockAmbientBall_eq_directionTotals_mul_radialNormalization
                (ι := ι) (κ := κ))
        have hball0' : ballVol ≠ 0 := by
          simpa [ballVol] using hball0
        have hballt' : ballVol ≠ ∞ := by
          simpa [ballVol] using hballt
        change ballVol⁻¹ *
            (leftTot * surfL * (rightTot * surfR) * (radNorm * betaMass)) =
          betaMass * (surfL * surfR)
        have hrewrite :
            ballVol⁻¹ *
                (leftTot * surfL * (rightTot * surfR) *
                  (radNorm * betaMass)) =
              ballVol⁻¹ * (ballVol * (betaMass * (surfL * surfR))) := by
          rw [hnorm]
          ac_rfl
        calc
          ballVol⁻¹ *
              (leftTot * surfL * (rightTot * surfR) *
                (radNorm * betaMass)) =
            ballVol⁻¹ * (ballVol * (betaMass * (surfL * surfR))) := hrewrite
          _ = betaMass * (surfL * surfR) := by
              rw [← mul_assoc, ENNReal.inv_mul_cancel hball0' hballt', one_mul]

/-- No-input spherical product law for the Hermitian block triple.

This is the abstract Step 1 endpoint on the sphere itself: once the measurable
rectangle factorization has been proved for
`canonicalHermitianBlockSphericalRectangularLaw_noInput`, the full
`Measure.map` equality for

`x ↦ (hermitianBlockMass x, hermitianBlockLeftDirection x,
      hermitianBlockRightDirection x)`

follows by the generic packaging theorem
`HermitianBlockSphericalRectangularLaw.map_triple_eq`. -/
theorem hermitianBlockDirections_independent_of_mass
    [Nonempty ι] [Nonempty κ]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ))).toSphere)]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere)]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)).toSphere)] :
    Measure.map
        (fun x =>
          (hermitianBlockMass (ι := ι) (κ := κ) x,
            hermitianBlockLeftDirection (ι := ι) (κ := κ) x,
            hermitianBlockRightDirection (ι := ι) (κ := κ) x))
        (surfaceMeasureAmbient (Sum ι κ)) =
      (hermitianBlockMassBetaMeasure (ι := ι) (κ := κ)).prod
        ((surfaceMeasureAmbient ι).prod (surfaceMeasureAmbient κ)) := by
  exact
    HermitianBlockSphericalRectangularLaw.map_triple_eq
      (ι := ι) (κ := κ)
      (μ := surfaceMeasureAmbient (Sum ι κ))
      (massLaw := hermitianBlockMassBetaMeasure (ι := ι) (κ := κ))
      (leftDirectionLaw := surfaceMeasureAmbient ι)
      (rightDirectionLaw := surfaceMeasureAmbient κ)
      (canonicalHermitianBlockSphericalRectangularLaw_noInput
        (ι := ι) (κ := κ))

/-- No-input push-forward law for the Hermitian block triple.

This is the explicit π-system step: the rectangular factorization determines
the full equality of measures for

`x ↦ (‖x_E‖², x_E/‖x_E‖, x_F/‖x_F‖)`. -/
theorem canonicalHermitianBlockSphericalMapTripleEq_noInput
    [Nonempty ι] [Nonempty κ]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ))).toSphere)]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere)]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)).toSphere)] :
    Measure.map
        (fun x =>
          (hermitianBlockMass (ι := ι) (κ := κ) x,
            hermitianBlockLeftDirection (ι := ι) (κ := κ) x,
            hermitianBlockRightDirection (ι := ι) (κ := κ) x))
        (surfaceMeasureAmbient (Sum ι κ)) =
      (hermitianBlockMassBetaMeasure (ι := ι) (κ := κ)).prod
        ((surfaceMeasureAmbient ι).prod (surfaceMeasureAmbient κ)) := by
  exact hermitianBlockDirections_independent_of_mass
    (ι := ι) (κ := κ)

/-- Master no-input Hermitian two-block spherical decomposition on
`ℂ^ι ⊕ ℂ^κ`.

The full product-law package is now a consequence of the rectangular
factorization statement
`canonicalHermitianBlockSphericalRectangularLaw_noInput`. -/
theorem canonicalHermitianBlockSphericalDecompositionIndependence_noInput
    [Nonempty ι] [Nonempty κ]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum ι κ))).toSphere)]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere)]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)).toSphere)] :
    CanonicalHermitianBlockSphericalDecompositionIndependence
      (ι := ι) (κ := κ)
      (surfaceMeasureAmbient (Sum ι κ))
      (surfaceMeasureAmbient ι)
      (surfaceMeasureAmbient κ) := by
  letI : IsProbabilityMeasure
      (hermitianBlockMassBetaMeasure (ι := ι) (κ := κ)) :=
    hermitianBlockMassBetaMeasure_isProbabilityMeasure (ι := ι) (κ := κ)
  letI : IsProbabilityMeasure (surfaceMeasureAmbient ι) :=
    surfaceMeasureAmbient_isProbabilityMeasure ι
  letI : IsProbabilityMeasure (surfaceMeasureAmbient κ) :=
    surfaceMeasureAmbient_isProbabilityMeasure κ
  exact
    CanonicalHermitianBlockSphericalDecompositionIndependence.of_map_triple_eq
      (ι := ι) (κ := κ)
      (hermitianBlockDirections_independent_of_mass
        (ι := ι) (κ := κ))

end HermitianBlockDecomposition

/-! ## Concrete column decomposition and spike/background algebra -/

variable {p q σ : Type*}

/-- The sample-column type obtained after deleting the distinguished column
`α₀`.

This is the intrinsic column set for the normalized background in the one-column
spike decomposition. -/
abbrev DeletedColumn (α₀ : σ) : Type _ :=
  {α : σ // α ≠ α₀}

@[simp] theorem fintype_card_deletedColumn
    [Fintype σ] [DecidableEq σ] (α₀ : σ) :
    Fintype.card (DeletedColumn (σ := σ) α₀) = Fintype.card σ - 1 := by
  classical
  have hcompl :=
    Fintype.card_subtype_compl (α := σ) (p := fun α : σ => α = α₀)
  simp [DeletedColumn] at hcompl ⊢

/-- The sample matrix obtained by keeping only column `α₀`. -/
noncomputable def sampleColumnPart
    [DecidableEq σ] (X : SampleMatrix p q σ) (α₀ : σ) :
    SampleMatrix p q σ :=
  fun i α => if α = α₀ then X i α else 0

/-- The sample matrix obtained by deleting column `α₀`. -/
noncomputable def sampleColumnComplement
    [DecidableEq σ] (X : SampleMatrix p q σ) (α₀ : σ) :
    SampleMatrix p q σ :=
  fun i α => if α = α₀ then 0 else X i α

/-- Zero-extension of a reduced deleted-column sample matrix back to the
original sample-column type.

The deleted coordinate `α₀` is filled with zero; every other coordinate is read
from the reduced subtype `{α // α ≠ α₀}`. -/
noncomputable def deletedColumnZeroExtend
    [DecidableEq σ] (α₀ : σ)
    (Y : SampleMatrix p q (DeletedColumn α₀)) :
    SampleMatrix p q σ :=
  fun i α => if h : α ≠ α₀ then Y i ⟨α, h⟩ else 0

@[simp] theorem deletedColumnZeroExtend_apply_self
    [DecidableEq σ] (α₀ : σ)
    (Y : SampleMatrix p q (DeletedColumn α₀)) (i : BipIndex p q) :
    deletedColumnZeroExtend (p := p) (q := q) (σ := σ) α₀ Y i α₀ = 0 := by
  simp [deletedColumnZeroExtend]

@[simp] theorem deletedColumnZeroExtend_apply_ne
    [DecidableEq σ] (α₀ : σ)
    (Y : SampleMatrix p q (DeletedColumn α₀)) (i : BipIndex p q)
    {α : σ} (hα : α ≠ α₀) :
    deletedColumnZeroExtend (p := p) (q := q) (σ := σ) α₀ Y i α =
      Y i ⟨α, hα⟩ := by
  simp [deletedColumnZeroExtend, hα]

set_option linter.unusedSectionVars false in
/-- Zero-extension of a deleted-column matrix does not change its density
matrix.  The distinguished column contributes exactly zero. -/
theorem densityMatrix_deletedColumnZeroExtend
    [Fintype σ] [DecidableEq σ] (α₀ : σ)
    (Y : SampleMatrix p q (DeletedColumn α₀)) :
    densityMatrix (deletedColumnZeroExtend (p := p) (q := q) (σ := σ) α₀ Y) =
      densityMatrix Y := by
  ext i j
  simp only [densityMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply]
  let t : σ → ℂ := fun α =>
    deletedColumnZeroExtend (p := p) (q := q) (σ := σ) α₀ Y i α *
      star (deletedColumnZeroExtend (p := p) (q := q) (σ := σ) α₀ Y j α)
  have hsplit :
      (∑ α : σ, t α) =
        t α₀ + ∑ α : {α : σ // α ≠ α₀}, t α.1 := by
    simpa using Fintype.sum_eq_add_sum_subtype_ne t α₀
  calc
    (∑ α : σ,
        deletedColumnZeroExtend (p := p) (q := q) (σ := σ) α₀ Y i α *
          star (deletedColumnZeroExtend (p := p) (q := q) (σ := σ) α₀ Y j α)) =
        t α₀ + ∑ α : {α : σ // α ≠ α₀}, t α.1 := hsplit
    _ = ∑ α : DeletedColumn α₀, Y i α * star (Y j α) := by
      have ht0 : t α₀ = 0 := by
        simp [t, deletedColumnZeroExtend]
      rw [ht0, zero_add]
      apply Finset.sum_congr rfl
      intro α _hα
      simp [t, deletedColumnZeroExtend, α.2]

set_option linter.unusedSectionVars false in
/-- The coordinate projection from the full sample-coordinate sphere to the
deleted-column coordinate subspace is contractive. -/
theorem norm_deletedColumnProjection_le
    [Fintype σ] [DecidableEq σ] (α₀ : σ)
    (x : EuclideanSpace ℂ σ) :
    ‖(WithLp.toLp 2 (fun α : DeletedColumn α₀ => x α.1) :
        EuclideanSpace ℂ (DeletedColumn α₀))‖ ≤ ‖x‖ := by
  let xdel : EuclideanSpace ℂ (DeletedColumn α₀) :=
    WithLp.toLp 2 (fun α : DeletedColumn α₀ => x α.1)
  have hxdel_sq :
      ‖xdel‖ ^ 2 = ∑ α : DeletedColumn α₀, ‖x α.1‖ ^ 2 := by
    simpa [xdel] using
      (EuclideanSpace.norm_sq_eq (𝕜 := ℂ) xdel)
  have hx_sq :
      ‖x‖ ^ 2 =
        ‖x α₀‖ ^ 2 + ∑ α : DeletedColumn α₀, ‖x α.1‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq (𝕜 := ℂ) x]
    simpa using
      (Fintype.sum_eq_add_sum_subtype_ne
        (fun α : σ => ‖x α‖ ^ 2) α₀)
  have hsq : ‖xdel‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [hxdel_sq, hx_sq]
    nlinarith [sq_nonneg (‖x α₀‖)]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

set_option linter.unusedSectionVars false in
/-- Applying a zero-extended deleted-column matrix to a full coordinate vector
is the same as applying the reduced matrix to the deleted-coordinate
projection. -/
theorem toEuclideanLin_deletedColumnZeroExtend_apply
    [Fintype σ] [DecidableEq σ] (α₀ : σ)
    (Y : SampleMatrix p q (DeletedColumn α₀))
    (x : EuclideanSpace ℂ σ) :
    Matrix.toEuclideanLin (𝕜 := ℂ) (m := BipIndex p q) (n := σ)
        (deletedColumnZeroExtend (p := p) (q := q) (σ := σ) α₀ Y) x =
      Matrix.toEuclideanLin (𝕜 := ℂ) (m := BipIndex p q)
        (n := DeletedColumn α₀) Y
        (WithLp.toLp 2 (fun α : DeletedColumn α₀ => x α.1)) := by
  ext i
  simp only [Matrix.toLpLin_apply, PiLp.toLp_apply,
    Matrix.mulVec, dotProduct]
  let t : σ → ℂ := fun α =>
    deletedColumnZeroExtend (p := p) (q := q) (σ := σ) α₀ Y i α * x α
  have hsplit :
      (∑ α : σ, t α) =
        t α₀ + ∑ α : {α : σ // α ≠ α₀}, t α.1 := by
    simpa using Fintype.sum_eq_add_sum_subtype_ne t α₀
  calc
    (∑ α : σ,
        deletedColumnZeroExtend (p := p) (q := q) (σ := σ) α₀ Y i α * x α) =
        t α₀ + ∑ α : {α : σ // α ≠ α₀}, t α.1 := hsplit
    _ = ∑ α : DeletedColumn α₀, Y i α * x α.1 := by
      have ht0 : t α₀ = 0 := by
        simp [t, deletedColumnZeroExtend]
      rw [ht0, zero_add]
      apply Finset.sum_congr rfl
      intro α _hα
      simp [t, deletedColumnZeroExtend, α.2]

set_option linter.unusedSectionVars false in
/-- Zero-extension cannot increase the rectangular operator norm. -/
theorem sampleOpNorm_deletedColumnZeroExtend_le
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    (α₀ : σ)
    (Y : SampleMatrix p q (DeletedColumn α₀)) :
    PptFactorization.HighProbabilityBounds.sampleOpNorm
        (p := p) (q := q) (σ := σ)
        (deletedColumnZeroExtend (p := p) (q := q) (σ := σ) α₀ Y) ≤
      PptFactorization.HighProbabilityBounds.sampleOpNorm
        (p := p) (q := q) (σ := DeletedColumn α₀) Y := by
  unfold PptFactorization.HighProbabilityBounds.sampleOpNorm
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  intro x
  let xdel : EuclideanSpace ℂ (DeletedColumn α₀) :=
    WithLp.toLp 2 (fun α : DeletedColumn α₀ => x α.1)
  have happly :
      Matrix.toEuclideanLin (𝕜 := ℂ) (m := BipIndex p q) (n := σ)
          (deletedColumnZeroExtend (p := p) (q := q) (σ := σ) α₀ Y) x =
        Matrix.toEuclideanLin (𝕜 := ℂ) (m := BipIndex p q)
          (n := DeletedColumn α₀) Y xdel := by
    simpa [xdel] using
      toEuclideanLin_deletedColumnZeroExtend_apply
        (p := p) (q := q) (σ := σ) α₀ Y x
  have hproj : ‖xdel‖ ≤ ‖x‖ := by
    simpa [xdel] using
      norm_deletedColumnProjection_le (σ := σ) α₀ x
  calc
    ‖LinearMap.toContinuousLinearMap
        (Matrix.toEuclideanLin (𝕜 := ℂ) (m := BipIndex p q) (n := σ)
          (deletedColumnZeroExtend (p := p) (q := q) (σ := σ) α₀ Y)) x‖ =
        ‖LinearMap.toContinuousLinearMap
          (Matrix.toEuclideanLin (𝕜 := ℂ) (m := BipIndex p q)
            (n := DeletedColumn α₀) Y) xdel‖ := by
          simpa using congrArg norm happly
    _ ≤ ‖LinearMap.toContinuousLinearMap
          (Matrix.toEuclideanLin (𝕜 := ℂ) (m := BipIndex p q)
            (n := DeletedColumn α₀) Y)‖ * ‖xdel‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖LinearMap.toContinuousLinearMap
          (Matrix.toEuclideanLin (𝕜 := ℂ) (m := BipIndex p q)
            (n := DeletedColumn α₀) Y)‖ * ‖x‖ := by
        gcongr

@[fun_prop]
theorem measurable_deletedColumnZeroExtend
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    (α₀ : σ) :
    Measurable
      (deletedColumnZeroExtend (p := p) (q := q) (σ := σ) α₀) := by
  have hcont :
      Continuous
        (deletedColumnZeroExtend (p := p) (q := q) (σ := σ) α₀) := by
    unfold deletedColumnZeroExtend
    refine continuous_pi ?_
    intro i
    refine continuous_pi ?_
    intro α
    by_cases hα : α ≠ α₀
    · simpa [hα] using
        (continuous_apply (⟨α, hα⟩ : DeletedColumn α₀)).comp
          (continuous_apply i)
    · simpa [hα] using (continuous_const : Continuous fun _ :
        SampleMatrix p q (DeletedColumn α₀) => (0 : ℂ))
  exact hcont.measurable

/-- The canonical deleted-column background law.

It is the spherical law on the reduced sample space with columns
`DeletedColumn α₀`, pushed forward by zero-extension back to the original
sample-column type `σ`.  This is the background marginal that should appear in
the one-column spherical decomposition. -/
noncomputable def deletedColumnBackgroundLaw
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    (α₀ : σ) : Measure (SampleMatrix p q σ) :=
  Measure.map
    (deletedColumnZeroExtend (p := p) (q := q) (σ := σ) α₀)
    (sphericalModelMeasure (p := p) (q := q) (σ := DeletedColumn α₀))

theorem deletedColumnBackgroundLaw_isProbabilityMeasure
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    [Nonempty p] [Nonempty q] {α₀ : σ} [Nonempty (DeletedColumn α₀)] :
    IsProbabilityMeasure
      (deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀) := by
  unfold deletedColumnBackgroundLaw
  letI :
      IsProbabilityMeasure
        (sphericalModelMeasure (p := p) (q := q) (σ := DeletedColumn α₀)) :=
    sphericalModelMeasure_isProbabilityMeasure
      (p := p) (q := q) (σ := DeletedColumn α₀)
  exact Measure.isProbabilityMeasure_map
    (measurable_deletedColumnZeroExtend
      (p := p) (q := q) (σ := σ) α₀).aemeasurable

/-- The reduced matrix formed by the non-distinguished sample columns. -/
noncomputable def sampleDeletedColumns
    (X : SampleMatrix p q σ) (α₀ : σ) :
    SampleMatrix p q (DeletedColumn α₀) :=
  fun i α => X i α.1

set_option linter.unusedSectionVars false in
@[fun_prop]
theorem measurable_sampleDeletedColumns
    [Fintype p] [Fintype q] [Fintype σ]
    (α₀ : σ) :
    Measurable
      (fun X : SampleMatrix p q σ =>
        sampleDeletedColumns (p := p) (q := q) (σ := σ) X α₀) := by
  have hcont :
      Continuous
        (fun X : SampleMatrix p q σ =>
          sampleDeletedColumns (p := p) (q := q) (σ := σ) X α₀) := by
    unfold sampleDeletedColumns
    refine continuous_pi ?_
    intro i
    refine continuous_pi ?_
    intro α
    exact
      ((continuous_apply α.1 : Continuous fun row : σ → ℂ => row α.1).comp
        (continuous_apply i :
          Continuous fun X : SampleMatrix p q σ => X i))
  exact hcont.measurable

/-- The concrete sample-matrix coordinates as a Hermitian direct sum:
distinguished column on the left, deleted columns on the right. -/
noncomputable def deletedColumnBlockVector
    [Fintype p] [Fintype q] [Fintype σ]
    (α₀ : σ) (X : SampleMatrix p q σ) :
    EuclideanSpace ℂ
      (Sum (BipIndex p q)
        (PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀))) :=
  WithLp.toLp 2
    (fun a =>
      match a with
      | Sum.inl i => X i α₀
      | Sum.inr b => X b.1 b.2.1)

/-- Coordinate equivalence splitting the full sample-coordinate index set into
the distinguished column and all deleted-column coordinates. -/
def deletedColumnBlockIndexEquiv
    [Fintype p] [Fintype q] [Fintype σ] [DecidableEq σ]
    (α₀ : σ) :
    PptFactorization.GaussianModel.SampleCoord p q σ ≃
      Sum (BipIndex p q)
        (PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀)) where
  toFun a :=
    if h : a.2 = α₀ then
      Sum.inl a.1
    else
      Sum.inr (a.1, ⟨a.2, h⟩)
  invFun a :=
    match a with
    | Sum.inl i => (i, α₀)
    | Sum.inr b => (b.1, b.2.1)
  left_inv := by
    intro a
    rcases a with ⟨i, α⟩
    by_cases h : α = α₀
    · simp [h]
    · simp [h]
  right_inv := by
    intro a
    cases a with
    | inl i =>
        simp
    | inr b =>
        rcases b with ⟨i, α⟩
        simp [α.2]

/-- Concrete deleted-column block isometry.

It identifies the matrix sample space with
`ℂ^(BipIndex p q) ⊕ ℂ^(SampleCoord p q (DeletedColumn α₀))`, by placing the
distinguished column on the left block and all remaining entries on the right
block. -/
noncomputable def deletedColumnBlockLinearIsometryEquiv
    [Fintype p] [Fintype q] [Fintype σ] [DecidableEq σ]
    (α₀ : σ) :
    SampleMatrix p q σ ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ
        (Sum (BipIndex p q)
          (PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀))) :=
  (sampleMatrixComplexLinearIsometryEquiv (p := p) (q := q) (σ := σ)).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (deletedColumnBlockIndexEquiv (p := p) (q := q) (σ := σ) α₀))

@[simp] theorem deletedColumnBlockLinearIsometryEquiv_apply
    [Fintype p] [Fintype q] [Fintype σ] [DecidableEq σ]
    (α₀ : σ) (X : SampleMatrix p q σ) :
    deletedColumnBlockLinearIsometryEquiv
        (p := p) (q := q) (σ := σ) α₀ X =
      deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀ X := by
  ext a
  cases a with
  | inl i =>
      simp [deletedColumnBlockLinearIsometryEquiv, deletedColumnBlockVector,
        deletedColumnBlockIndexEquiv, sampleMatrixComplexLinearIsometryEquiv]
  | inr b =>
      rcases b with ⟨i, α⟩
      simp [deletedColumnBlockLinearIsometryEquiv, deletedColumnBlockVector,
        deletedColumnBlockIndexEquiv, sampleMatrixComplexLinearIsometryEquiv]

set_option linter.unusedSectionVars false in
/-- Transport of the concrete ambient matrix-sphere surface law by a complex
linear isometry into a complex Euclidean coordinate space. -/
theorem surfaceModelMeasure_map_complexLinearIsometryEquiv
    [Fintype p] [Fintype q] [Fintype σ] [Fintype τ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ] [Nonempty τ]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ τ)).toSphere)]
    (V : SampleMatrix p q σ ≃ₗᵢ[ℂ] EuclideanSpace ℂ τ) :
    Measure.map V (surfaceModelMeasure (p := p) (q := q) (σ := σ)) =
      surfaceMeasureAmbient τ := by
  let U : SampleMatrix p q σ ≃ₗᵢ[ℝ] EuclideanSpace ℂ τ :=
    IsometryEquiv.toRealLinearIsometryEquivOfMapZero V.toIsometryEquiv
      (by simp : V.toIsometryEquiv 0 = 0)
  let μ : Measure (SampleMatrix p q σ) :=
    sampleHaarMeasure (p := p) (q := q) (σ := σ)
  let ν : Measure (EuclideanSpace ℂ τ) := MeasureTheory.volume
  haveI : μ.IsAddHaarMeasure := by
    unfold μ sampleHaarMeasure
    infer_instance
  haveI : ν.IsAddHaarMeasure := by
    unfold ν
    infer_instance
  haveI : SFinite μ.toSphere := by
    unfold μ sampleHaarMeasure
    infer_instance
  haveI : IsFiniteMeasure μ.toSphere := ⟨by
    simpa [μ, sampleSurfaceMeasure] using
      sampleSurfaceMeasure_lt_top_univ (p := p) (q := q) (σ := σ)⟩
  haveI : SFinite ν.toSphere := by
    unfold ν
    infer_instance
  haveI : IsFiniteMeasure ν.toSphere := ⟨by
    have hball_lt_top :
        ν (Metric.ball (0 : EuclideanSpace ℂ τ) 1) < ∞ := by
      exact lt_of_le_of_lt
        (measure_mono Metric.ball_subset_closedBall)
        ((isCompact_closedBall (0 : EuclideanSpace ℂ τ) 1).measure_lt_top)
    unfold ν
    rw [Measure.toSphere_apply_univ]
    exact ENNReal.mul_lt_top (by simp) hball_lt_top⟩
  have hsurj : Function.Surjective U.toLinearEquiv.toLinearMap :=
    U.toLinearEquiv.surjective
  obtain ⟨c, hcpos, hmap⟩ :=
    U.toLinearEquiv.toLinearMap.exists_map_addHaar_eq_smul_addHaar
      (μ := μ) (ν := ν) hsurj
  have hmapU : Measure.map U μ = c • ν := by
    simpa using hmap
  have hc0 : c ≠ 0 := ne_of_gt hcpos
  have hνball_ne_zero :
      ν (Metric.ball (0 : EuclideanSpace ℂ τ) 1) ≠ 0 := by
    exact Metric.isOpen_ball.measure_ne_zero ν ⟨0, by simp⟩
  have hμball_lt_top :
      μ (Metric.ball (0 : SampleMatrix p q σ) 1) < ∞ := by
    exact lt_of_le_of_lt
      (measure_mono Metric.ball_subset_closedBall)
      ((isCompact_closedBall (0 : SampleMatrix p q σ) 1).measure_lt_top)
  have hpre_ball :
      U ⁻¹' Metric.ball (0 : EuclideanSpace ℂ τ) 1 =
        Metric.ball (0 : SampleMatrix p q σ) 1 := by
    ext x
    simp [Metric.mem_ball, dist_eq_norm, U]
  have hball_eq :
      μ (Metric.ball (0 : SampleMatrix p q σ) 1) =
        c * ν (Metric.ball (0 : EuclideanSpace ℂ τ) 1) := by
    calc
      μ (Metric.ball (0 : SampleMatrix p q σ) 1) =
          Measure.map U μ (Metric.ball (0 : EuclideanSpace ℂ τ) 1) := by
        rw [Measure.map_apply U.continuous.measurable
          Metric.isOpen_ball.measurableSet]
        rw [hpre_ball]
      _ = (c • ν) (Metric.ball (0 : EuclideanSpace ℂ τ) 1) := by
        rw [hmapU]
      _ = c * ν (Metric.ball (0 : EuclideanSpace ℂ τ) 1) := by
        simp [smul_eq_mul]
  have hctop : c ≠ ∞ := by
    intro hc
    have hright :
        c * ν (Metric.ball (0 : EuclideanSpace ℂ τ) 1) = ∞ := by
      rw [hc]
      simp [hνball_ne_zero]
    have hμtop : μ (Metric.ball (0 : SampleMatrix p q σ) 1) = ∞ := by
      rw [hball_eq, hright]
    exact hμball_lt_top.ne hμtop
  have hsub :
      Measure.map
          (Subtype.map U (fun _ hx => by simpa using hx))
          (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)) =
        surfaceMeasure τ := by
    change
      Measure.map
          (Subtype.map U (fun _ hx => by simpa using hx))
          μ.toSphere.toFinite =
        ν.toSphere.toFinite
    exact
      map_toFinite_toSphere_linearIsometryEquiv_of_map_eq_smul
        (μ := μ) (ν := ν) U hc0 hctop hmapU
  change
    Measure.map U (surfaceModelMeasure (p := p) (q := q) (σ := σ)) =
      surfaceMeasureAmbient τ
  unfold surfaceModelMeasure sampleSurfaceProbabilityMeasureAmbient
    surfaceMeasureAmbient
  rw [← hsub]
  rw [Measure.map_map U.continuous.measurable continuous_subtype_val.measurable]
  rw [Measure.map_map continuous_subtype_val.measurable
    ((U.continuous.subtype_map (fun _ hx => by simpa using hx)).measurable)]
  rfl

set_option linter.unusedSectionVars false in
/-- The spherical law of the concrete deleted-column block vector is exactly
the ambient surface law on
`ℂ^(BipIndex p q) ⊕ ℂ^(SampleCoord p q (DeletedColumn α₀))`. -/
theorem deletedColumnBlockVector_map_sphericalModelMeasure_eq_surfaceMeasureAmbient
    [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q]
    [DecidableEq σ] [Nonempty p] [Nonempty q] [Nonempty σ]
    (α₀ : σ)
    [SFinite
      ((MeasureTheory.volume : Measure
        (EuclideanSpace ℂ
          (Sum (BipIndex p q)
            (PptFactorization.GaussianModel.SampleCoord p q
              (DeletedColumn α₀))))).toSphere)] :
    Measure.map
        (fun X : SampleMatrix p q σ =>
          deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀ X)
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)) =
      surfaceMeasureAmbient
        (Sum (BipIndex p q)
          (PptFactorization.GaussianModel.SampleCoord p q
            (DeletedColumn α₀))) := by
  rw [polarLaw (p := p) (q := q) (σ := σ)]
  have hfun :
      (fun X : SampleMatrix p q σ =>
        deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀ X) =
      (deletedColumnBlockLinearIsometryEquiv
        (p := p) (q := q) (σ := σ) α₀) := by
    funext X
    exact (deletedColumnBlockLinearIsometryEquiv_apply
      (p := p) (q := q) (σ := σ) α₀ X).symm
  rw [hfun]
  exact
    surfaceModelMeasure_map_complexLinearIsometryEquiv
      (p := p) (q := q) (σ := σ)
      (τ := Sum (BipIndex p q)
        (PptFactorization.GaussianModel.SampleCoord p q
          (DeletedColumn α₀)))
      (deletedColumnBlockLinearIsometryEquiv
        (p := p) (q := q) (σ := σ) α₀)

set_option linter.unusedSectionVars false in
@[fun_prop]
theorem measurable_deletedColumnBlockVector
    [Fintype p] [Fintype q] [Fintype σ]
    (α₀ : σ) :
    Measurable
      (fun X : SampleMatrix p q σ =>
        deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀ X) := by
  let J :=
    Sum (BipIndex p q)
      (PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀))
  have hcont_raw :
      Continuous
        (fun X : SampleMatrix p q σ =>
          (fun a : J =>
            (match a with
            | Sum.inl i => X i α₀
            | Sum.inr b => X b.1 b.2.1 : ℂ))) := by
    refine continuous_pi ?_
    intro a
    cases a with
    | inl i =>
        exact
          ((continuous_apply α₀ : Continuous fun row : σ → ℂ => row α₀).comp
            (continuous_apply i :
              Continuous fun X : SampleMatrix p q σ => X i))
    | inr b =>
        exact
          ((continuous_apply b.2.1 : Continuous fun row : σ → ℂ => row b.2.1).comp
            (continuous_apply b.1 :
              Continuous fun X : SampleMatrix p q σ => X b.1))
  simpa [deletedColumnBlockVector, J] using
    ((PiLp.continuous_toLp 2 _).comp hcont_raw).measurable

/-- Transport a normalized right-block vector on the deleted-column coordinate
space back to the original sample-matrix space by the sample-matrix isometry
and zero-extension. -/
noncomputable def deletedColumnRightDirectionToBackground
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    (α₀ : σ)
    (u : EuclideanSpace ℂ
      (PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀))) :
    SampleMatrix p q σ :=
  deletedColumnZeroExtend (p := p) (q := q) (σ := σ) α₀
    ((sampleMatrixComplexLinearIsometryEquiv
      (p := p) (q := q) (σ := DeletedColumn α₀)).symm u)

set_option linter.unusedSectionVars false in
@[fun_prop]
theorem measurable_deletedColumnRightDirectionToBackground
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    (α₀ : σ) :
    Measurable
      (deletedColumnRightDirectionToBackground
        (p := p) (q := q) (σ := σ) α₀) := by
  unfold deletedColumnRightDirectionToBackground
  exact
    (measurable_deletedColumnZeroExtend
      (p := p) (q := q) (σ := σ) α₀).comp
      (sampleMatrixComplexLinearIsometryEquiv
        (p := p) (q := q) (σ := DeletedColumn α₀)).symm.continuous.measurable

/-- The genuine deleted-column right-direction law.

This is **not** the full spherical law on the original column type `σ`.
It is the spherical law on the reduced deleted-column sample space
`DeletedColumn α₀`, transported to Euclidean coordinates by the matrix
flattening isometry. -/
noncomputable def deletedColumnRightDirectionLaw
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    (α₀ : σ) :
    Measure (EuclideanSpace ℂ
      (PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀))) :=
  Measure.map
    (sampleMatrixComplexLinearIsometryEquiv
      (p := p) (q := q) (σ := DeletedColumn α₀))
    (sphericalModelMeasure (p := p) (q := q) (σ := DeletedColumn α₀))

set_option linter.unusedSectionVars false in
theorem deletedColumnRightDirectionLaw_isProbabilityMeasure
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    (α₀ : σ) :
    IsProbabilityMeasure
      (deletedColumnRightDirectionLaw
        (p := p) (q := q) (σ := σ) α₀) := by
  unfold deletedColumnRightDirectionLaw
  haveI : IsProbabilityMeasure
      (sphericalModelMeasure (p := p) (q := q) (σ := DeletedColumn α₀)) :=
    sphericalModelMeasure_isProbabilityMeasure
      (p := p) (q := q) (σ := DeletedColumn α₀)
  exact Measure.isProbabilityMeasure_map
    (sampleMatrixComplexLinearIsometryEquiv
      (p := p) (q := q) (σ := DeletedColumn α₀)).continuous.measurable.aemeasurable

set_option linter.unusedSectionVars false in
/-- Zero-extending the genuine deleted-column right-direction law gives exactly
`deletedColumnBackgroundLaw`.

This is the formal guard against the common mistake of reusing
`sphericalModelMeasure p q σ` for the background.  The background is the
reduced spherical law on `DeletedColumn α₀`, pushed forward by
`deletedColumnZeroExtend`. -/
theorem deletedColumnRightDirectionLaw_toBackground_eq_deletedColumnBackgroundLaw
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    (α₀ : σ) :
    Measure.map
        (deletedColumnRightDirectionToBackground
          (p := p) (q := q) (σ := σ) α₀)
        (deletedColumnRightDirectionLaw
          (p := p) (q := q) (σ := σ) α₀) =
      deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀ := by
  let Φ :=
    sampleMatrixComplexLinearIsometryEquiv
      (p := p) (q := q) (σ := DeletedColumn α₀)
  let Z :=
    deletedColumnZeroExtend (p := p) (q := q) (σ := σ) α₀
  have hmeasΦ : Measurable Φ := Φ.continuous.measurable
  have hmeasToBackground :
      Measurable
        (deletedColumnRightDirectionToBackground
          (p := p) (q := q) (σ := σ) α₀) :=
    measurable_deletedColumnRightDirectionToBackground
      (p := p) (q := q) (σ := σ) α₀
  calc
    Measure.map
        (deletedColumnRightDirectionToBackground
          (p := p) (q := q) (σ := σ) α₀)
        (deletedColumnRightDirectionLaw
          (p := p) (q := q) (σ := σ) α₀) =
      Measure.map
        (fun Y : SampleMatrix p q (DeletedColumn α₀) =>
          deletedColumnRightDirectionToBackground
            (p := p) (q := q) (σ := σ) α₀ (Φ Y))
        (sphericalModelMeasure (p := p) (q := q) (σ := DeletedColumn α₀)) := by
        rw [deletedColumnRightDirectionLaw]
        rw [Measure.map_map hmeasToBackground hmeasΦ]
        rfl
    _ =
      Measure.map Z
        (sphericalModelMeasure (p := p) (q := q) (σ := DeletedColumn α₀)) := by
        congr 1
    _ = deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀ := by
      rfl

set_option linter.unusedSectionVars false in
/-- Explicit Step 8 form of the deleted-background law.

This is the same statement as
`deletedColumnRightDirectionLaw_toBackground_eq_deletedColumnBackgroundLaw`,
but with the right-hand side expanded to the actual pushforward

`Measure.map (deletedColumnZeroExtend α₀)
  (sphericalModelMeasure (σ := DeletedColumn α₀))`.

It is the precise point where we avoid replacing the deleted background by the
full spherical law on `σ`. -/
theorem deletedColumnRightDirectionLaw_toBackground_eq_zeroExtend_sphericalModelMeasure
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    (α₀ : σ) :
    Measure.map
        (deletedColumnRightDirectionToBackground
          (p := p) (q := q) (σ := σ) α₀)
        (deletedColumnRightDirectionLaw
          (p := p) (q := q) (σ := σ) α₀) =
      Measure.map
        (deletedColumnZeroExtend (p := p) (q := q) (σ := σ) α₀)
        (sphericalModelMeasure
          (p := p) (q := q) (σ := DeletedColumn α₀)) := by
  simpa [deletedColumnBackgroundLaw] using
    deletedColumnRightDirectionLaw_toBackground_eq_deletedColumnBackgroundLaw
      (p := p) (q := q) (σ := σ) α₀

section ColumnDecomposition

variable [DecidableEq σ]

/-- A sample matrix is the sum of one distinguished column and its complement. -/
theorem sampleColumnPart_add_complement
    (X : SampleMatrix p q σ) (α₀ : σ) :
    sampleColumnPart X α₀ + sampleColumnComplement X α₀ = X := by
  ext i α
  by_cases h : α = α₀ <;> simp [sampleColumnPart, sampleColumnComplement, h]

variable [Fintype σ]

/-- Exact column decomposition of the density matrix.

This is the formal version of the step

`XX* = x_α x_α* + Σ_{β≠α} x_β x_β*`.

The point of using a column, rather than an arbitrary fibre projection, is that
there are no cross terms in `XX*`: the matrix product already sums over the
sample-column index. -/
theorem densityMatrix_column_decomposition
    (X : SampleMatrix p q σ) (α₀ : σ) :
    densityMatrix X =
      densityMatrix (sampleColumnPart X α₀) +
        densityMatrix (sampleColumnComplement X α₀) := by
  ext i j
  simp [densityMatrix, sampleColumnPart, sampleColumnComplement, Matrix.mul_apply]
  let t : σ → ℂ := fun x => X i x * (starRingEnd ℂ) (X j x)
  have hsplit : (∑ x : σ, t x) =
      (∑ x : σ, (if x = α₀ then t x else 0)) +
        ∑ x : σ, (if x = α₀ then 0 else t x) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _hx
    by_cases h : x = α₀ <;> simp [h]
  have hsingle : (∑ x : σ, (if x = α₀ then t x else 0)) = t α₀ := by
    simp
  rw [hsplit, hsingle]
  congr 1
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases h : x = α₀ <;> simp [t, h]

/-- Exact column decomposition after partial transpose. -/
theorem gamma_densityMatrix_column_decomposition
    [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (X : SampleMatrix p q σ) (α₀ : σ) :
    gamma (densityMatrix X) =
      gamma (densityMatrix (sampleColumnPart X α₀)) +
        gamma (densityMatrix (sampleColumnComplement X α₀)) := by
  rw [densityMatrix_column_decomposition (X := X) (α₀ := α₀)]
  simp [gamma]

set_option linter.unusedSectionVars false in
/-- Density matrices are quadratic under scalar multiplication. -/
theorem densityMatrix_smul
    [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (c : ℂ) (X : SampleMatrix p q σ) :
    densityMatrix (p := p) (q := q) (σ := σ) (c • X) =
      (c * star c) • densityMatrix (p := p) (q := q) (σ := σ) X := by
  ext i j
  simp [densityMatrix, Matrix.mul_apply]
  calc
    (∑ x : σ, c * X i x * ((starRingEnd ℂ) c * (starRingEnd ℂ) (X j x))) =
        ∑ x : σ, (c * (starRingEnd ℂ) c) *
          (X i x * (starRingEnd ℂ) (X j x)) := by
          refine Finset.sum_congr rfl ?_
          intro x _hx
          ring
    _ = c * (starRingEnd ℂ) c *
          ∑ x : σ, X i x * (starRingEnd ℂ) (X j x) := by
          rw [Finset.mul_sum]

end ColumnDecomposition

section MatrixSpikeAlgebra

variable [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]

/-- Normalized real trace moment `N^(k-1) Re Tr(A^k)`. -/
noncomputable def scaledTracePower (N : ℝ) (k : ℕ) (A : BipMatrix p q) : ℝ :=
  N ^ (k - 1) * (Matrix.trace (A ^ k)).re

/-- Pure-spike contribution for `R S + (1-R) B`. -/
noncomputable def pureSpikeContribution
    (N : ℝ) (k : ℕ) (R : ℝ) (S : BipMatrix p q) : ℝ :=
  N ^ (k - 1) * R ^ k * (Matrix.trace (S ^ k)).re

/-- Pure-background contribution for `R S + (1-R) B`. -/
noncomputable def pureBackgroundContribution
    (N : ℝ) (k : ℕ) (R : ℝ) (B : BipMatrix p q) : ℝ :=
  N ^ (k - 1) * (1 - R) ^ k * (Matrix.trace (B ^ k)).re

/-- The exact mixed remainder left after subtracting the pure spike and pure
background pieces from the trace moment of `R S + (1-R) B`.

The hard analytic estimate in the spike proof is precisely a lower bound on
this quantity.  Defining it this way keeps the mixed terms explicit instead of
silently discarding them. -/
noncomputable def matrixSpikeMixedRemainder
    (N : ℝ) (k : ℕ) (R : ℝ) (S B : BipMatrix p q) : ℝ :=
  scaledTracePower N k (((R : ℂ) • S) + (((1 - R : ℝ) : ℂ) • B)) -
    pureSpikeContribution N k R S - pureBackgroundContribution N k R B

/-- Exact spike/background/remainder decomposition of the normalized trace
moment. -/
theorem scaledTracePower_spike_background_decomposition
    (N : ℝ) (k : ℕ) (R : ℝ) (S B : BipMatrix p q) :
    scaledTracePower N k (((R : ℂ) • S) + (((1 - R : ℝ) : ℂ) • B)) =
      pureSpikeContribution N k R S + pureBackgroundContribution N k R B +
        matrixSpikeMixedRemainder N k R S B := by
  unfold matrixSpikeMixedRemainder
  ring

/-- Deterministic matrix-level spike inclusion.

If the pure spike contributes at least `a^k` up to `errSpike`, the pure
background is at least the limiting centre up to `errBg`, the exact mixed
remainder is bounded below by `-errMix`, and the mean is at most the centre up
to `errMean`, then the matrix lies in the upper-deviation event whenever the
error budget is smaller than `a^k - eps`.

This is the matrix-formalized part of the clean spike proof.  The probabilistic
work is to construct an event on which the four hypotheses below hold and to
estimate its probability. -/
theorem matrix_spike_event_deviation_of_pure_background_mixed
    {N R a eps mean center errSpike errBg errMix errMean : ℝ}
    {k : ℕ} {S B : BipMatrix p q}
    (hSpike : a ^ k - errSpike ≤ pureSpikeContribution N k R S)
    (hBackground : center - errBg ≤ pureBackgroundContribution N k R B)
    (hMixed : -errMix ≤ matrixSpikeMixedRemainder N k R S B)
    (hMean : mean ≤ center + errMean)
    (hBudget : eps + errSpike + errBg + errMix + errMean ≤ a ^ k) :
    eps ≤
      scaledTracePower N k (((R : ℂ) • S) + (((1 - R : ℝ) : ℂ) • B)) - mean := by
  have hDecomp := scaledTracePower_spike_background_decomposition
    (p := p) (q := q) N k R S B
  linarith

end MatrixSpikeAlgebra

/-! ## Column lower-bound algebra, not fibre-overlap algebra -/

section ColumnSpikeAlgebra

variable [Fintype p] [Fintype q] [Fintype σ]
variable [DecidableEq p] [DecidableEq q] [DecidableEq σ]

/-- Squared Hilbert--Schmidt mass of one distinguished sample column. -/
noncomputable def sampleColumnMass (X : SampleMatrix p q σ) (α₀ : σ) : ℝ :=
  frobeniusNorm (p := p) (q := q) (σ := σ)
    (sampleColumnPart (p := p) (q := q) (σ := σ) X α₀) ^ 2

set_option linter.unusedSectionVars false in
@[fun_prop]
theorem measurable_sampleColumnPart (α₀ : σ) :
    Measurable
      (fun X : SampleMatrix p q σ =>
        sampleColumnPart (p := p) (q := q) (σ := σ) X α₀) := by
  have hcont :
      Continuous
        (fun X : SampleMatrix p q σ =>
          sampleColumnPart (p := p) (q := q) (σ := σ) X α₀) := by
    unfold sampleColumnPart
    refine continuous_pi ?_
    intro i
    refine continuous_pi ?_
    intro α
    by_cases hα : α = α₀
    · simpa [hα] using
        ((continuous_apply α : Continuous fun row : σ → ℂ => row α).comp
          (continuous_apply i :
            Continuous fun X : SampleMatrix p q σ => X i))
    · simpa [hα] using
        (continuous_const : Continuous fun _ : SampleMatrix p q σ => (0 : ℂ))
  exact hcont.measurable

set_option linter.unusedSectionVars false in
@[fun_prop]
theorem measurable_sampleColumnComplement (α₀ : σ) :
    Measurable
      (fun X : SampleMatrix p q σ =>
        sampleColumnComplement (p := p) (q := q) (σ := σ) X α₀) := by
  have hcont :
      Continuous
        (fun X : SampleMatrix p q σ =>
          sampleColumnComplement (p := p) (q := q) (σ := σ) X α₀) := by
    unfold sampleColumnComplement
    refine continuous_pi ?_
    intro i
    refine continuous_pi ?_
    intro α
    by_cases hα : α = α₀
    · simpa [hα] using
        (continuous_const : Continuous fun _ : SampleMatrix p q σ => (0 : ℂ))
    · simpa [hα] using
        ((continuous_apply α : Continuous fun row : σ → ℂ => row α).comp
          (continuous_apply i :
            Continuous fun X : SampleMatrix p q σ => X i))
  exact hcont.measurable

@[fun_prop]
theorem measurable_sampleColumnMass (α₀ : σ) :
    Measurable
      (fun X : SampleMatrix p q σ =>
        sampleColumnMass (p := p) (q := q) (σ := σ) X α₀) := by
  unfold sampleColumnMass frobeniusNorm
  fun_prop

set_option linter.unusedSectionVars false in
theorem sampleColumnMass_nonneg (X : SampleMatrix p q σ) (α₀ : σ) :
    0 ≤ sampleColumnMass (p := p) (q := q) (σ := σ) X α₀ := by
  unfold sampleColumnMass
  positivity

/-! ### Law of the one-column mass -/

section ColumnMassBetaLaw

variable [MeasurableSpace (SampleMatrix p q σ)]

/-- The interval `[q, (1+δ)q]` used for the one-column Beta mass. -/
noncomputable def betaColumnIntervalSet (q₀ δ : ℝ) : Set ℝ :=
  Set.Icc q₀ (betaColumnIntervalUpper q₀ δ)

/-- The event that the distinguished column has squared mass in the Beta
interval `[q, (1+δ)q]`. -/
noncomputable def columnMassIntervalEvent (α₀ : σ) (q₀ δ : ℝ) :
    Set (SampleMatrix p q σ) :=
  {X | sampleColumnMass (p := p) (q := q) (σ := σ) X α₀ ∈
      betaColumnIntervalSet q₀ δ}

/-- Pushforward law of the distinguished column mass under a measure on the
Hilbert--Schmidt sphere/model space. -/
noncomputable def columnMassPushforward
    (μ : Measure (SampleMatrix p q σ)) (α₀ : σ) : Measure ℝ :=
  Measure.map (fun X => sampleColumnMass (p := p) (q := q) (σ := σ) X α₀) μ

/-- Probability, computed from the pushforward law, that the distinguished
column mass lies in `[q, (1+δ)q]`. -/
noncomputable def columnMassIntervalProbability
    (μ : Measure (SampleMatrix p q σ)) (α₀ : σ) (q₀ δ : ℝ) : ℝ :=
  (columnMassPushforward (p := p) (q := q) (σ := σ) μ α₀).real
    (betaColumnIntervalSet q₀ δ)

/-- The same interval probability, but for an abstract real Beta measure. -/
noncomputable def betaColumnMeasureIntervalProbability
    (ν : Measure ℝ) (q₀ δ : ℝ) : ℝ :=
  ν.real (betaColumnIntervalSet q₀ δ)

/-- The concrete Beta law expected for one distinguished column mass:
`Beta(N, N*(s-1))`. -/
noncomputable def betaColumnMeasure (N s : ℕ) : Measure ℝ :=
  ProbabilityTheory.betaMeasure (N : ℝ) (betaColumnOtherShape N s : ℝ)

/-- Exact pushforward statement for the one-column mass:

`(sampleColumnMass α₀)_* μ = Beta(N, N*(s-1))`.

This is the precise formal target for the probabilistic proof that the squared
mass of one column of a spherical vector has the stated Beta law. -/
def ColumnMassHasBetaMeasure
    (μ : Measure (SampleMatrix p q σ)) (α₀ : σ) (N s : ℕ) : Prop :=
  columnMassPushforward (p := p) (q := q) (σ := σ) μ α₀ =
    betaColumnMeasure N s

set_option linter.unusedSectionVars false in
theorem ColumnMassHasBetaMeasure.hasLaw
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ} {N s : ℕ}
    (h : ColumnMassHasBetaMeasure (p := p) (q := q) (σ := σ) μ α₀ N s)
    (hmeas :
      AEMeasurable
        (fun X => sampleColumnMass (p := p) (q := q) (σ := σ) X α₀) μ) :
    ProbabilityTheory.HasLaw
      (fun X => sampleColumnMass (p := p) (q := q) (σ := σ) X α₀)
      (betaColumnMeasure N s) μ where
  aemeasurable := hmeas
  map_eq := by
    simpa [ColumnMassHasBetaMeasure, columnMassPushforward] using h

set_option linter.unusedSectionVars false in
theorem ColumnMassHasBetaMeasure.of_hasLaw
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ} {N s : ℕ}
    (h :
      ProbabilityTheory.HasLaw
        (fun X => sampleColumnMass (p := p) (q := q) (σ := σ) X α₀)
        (betaColumnMeasure N s) μ) :
    ColumnMassHasBetaMeasure (p := p) (q := q) (σ := σ) μ α₀ N s := by
  simpa [ColumnMassHasBetaMeasure, columnMassPushforward] using h.map_eq

theorem columnMassHasBetaMeasure_iff_hasLaw
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ} {N s : ℕ}
    (hmeas :
      AEMeasurable
        (fun X => sampleColumnMass (p := p) (q := q) (σ := σ) X α₀) μ) :
    ColumnMassHasBetaMeasure (p := p) (q := q) (σ := σ) μ α₀ N s ↔
      ProbabilityTheory.HasLaw
        (fun X => sampleColumnMass (p := p) (q := q) (σ := σ) X α₀)
        (betaColumnMeasure N s) μ := by
  constructor
  · intro h
    exact h.hasLaw hmeas
  · intro h
    exact ColumnMassHasBetaMeasure.of_hasLaw h

/-- An integer-Beta measure with the interval lower bounds needed for the
one-column spike proof.

This records the **Beta density calculation** separately from the
sphere-to-Beta identification.  In the intended application, `ν` is the
`Beta(N, N*(s-1))` law on `[0,1]`. -/
structure IntegerBetaColumnMeasure (ν : Measure ℝ) (N s : ℕ) : Prop where
  interval_lower :
    ∀ {q₀ δ : ℝ}, 0 < q₀ → 0 < δ → betaColumnIntervalUpper q₀ δ < 1 →
      BetaColumnIntervalLowerBound
        (betaColumnMeasureIntervalProbability ν q₀ δ) N s q₀ δ

set_option linter.unusedSectionVars false in
/-- Nonnegativity of the integer-parameter Beta density. -/
theorem betaPDFReal_nat_nonneg {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (x : ℝ) :
    0 ≤ ProbabilityTheory.betaPDFReal (N : ℝ) (M : ℝ) x := by
  by_cases hx : 0 < x ∧ x < 1
  · exact
      (ProbabilityTheory.betaPDFReal_pos hx.1 hx.2
        (by exact_mod_cast hN) (by exact_mod_cast hM)).le
  · rw [ProbabilityTheory.betaPDFReal, if_neg hx]

set_option linter.unusedSectionVars false in
/-- The Beta normalizing constant at positive integer parameters, written by
factorials. -/
theorem beta_nat_eq_factorial_ratio {N M : ℕ} (hN : 0 < N) (hM : 0 < M) :
    ProbabilityTheory.beta (N : ℝ) (M : ℝ) =
      ((Nat.factorial (N - 1) : ℕ) : ℝ) *
          ((Nat.factorial (M - 1) : ℕ) : ℝ) /
        ((Nat.factorial (N + M - 1) : ℕ) : ℝ) := by
  unfold ProbabilityTheory.beta
  have hNcast : (N : ℝ) = ((N - 1 : ℕ) : ℝ) + 1 := by
    have : N = (N - 1) + 1 := (Nat.sub_add_cancel hN).symm
    rw [this]
    norm_num
  have hMcast : (M : ℝ) = ((M - 1 : ℕ) : ℝ) + 1 := by
    have : M = (M - 1) + 1 := (Nat.sub_add_cancel hM).symm
    rw [this]
    norm_num
  rw [hNcast, hMcast]
  have hden :
      ((N - 1 : ℕ) : ℝ) + 1 + (((M - 1 : ℕ) : ℝ) + 1) =
        ((N + M - 1 : ℕ) : ℝ) + 1 := by
    have hdenNat :
        (N - 1) + 1 + ((M - 1) + 1) = (N + M - 1) + 1 := by
      omega
    exact_mod_cast hdenNat
  rw [hden]
  rw [Real.Gamma_nat_eq_factorial (N - 1),
    Real.Gamma_nat_eq_factorial (M - 1),
    Real.Gamma_nat_eq_factorial (N + M - 1)]

set_option linter.unusedSectionVars false in
/-- At positive integer parameters the Beta normalizing constant is at most
`1`.  Equivalently, the density prefactor `1 / beta` is at least `1`. -/
theorem beta_nat_le_one {N M : ℕ} (hN : 0 < N) (hM : 0 < M) :
    ProbabilityTheory.beta (N : ℝ) (M : ℝ) ≤ 1 := by
  rw [beta_nat_eq_factorial_ratio hN hM]
  have hdvd := Nat.factorial_mul_factorial_dvd_factorial_add (N - 1) (M - 1)
  have hle_add :
      Nat.factorial (N - 1) * Nat.factorial (M - 1) ≤
        Nat.factorial ((N - 1) + (M - 1)) := by
    exact Nat.le_of_dvd (Nat.factorial_pos _) hdvd
  have hidx : (N - 1) + (M - 1) ≤ N + M - 1 := by omega
  have hle_den_nat :
      Nat.factorial (N - 1) * Nat.factorial (M - 1) ≤
        Nat.factorial (N + M - 1) :=
    hle_add.trans (Nat.factorial_le hidx)
  have hle_den :
      ((Nat.factorial (N - 1) * Nat.factorial (M - 1) : ℕ) : ℝ) ≤
        ((Nat.factorial (N + M - 1) : ℕ) : ℝ) := by
    exact_mod_cast hle_den_nat
  have hdenpos : 0 < ((Nat.factorial (N + M - 1) : ℕ) : ℝ) := by
    positivity
  rw [div_le_iff₀ hdenpos]
  rw [Nat.cast_mul] at hle_den
  calc
    ((Nat.factorial (N - 1) : ℕ) : ℝ) *
        ((Nat.factorial (M - 1) : ℕ) : ℝ) ≤
        ((Nat.factorial (N + M - 1) : ℕ) : ℝ) := hle_den
    _ = 1 * ((Nat.factorial (N + M - 1) : ℕ) : ℝ) := by ring

set_option linter.unusedSectionVars false in
/-- Integer-parameter density prefactor lower bound. -/
theorem one_le_one_div_beta_nat {N M : ℕ} (hN : 0 < N) (hM : 0 < M) :
    1 ≤ 1 / ProbabilityTheory.beta (N : ℝ) (M : ℝ) := by
  have hbpos : 0 < ProbabilityTheory.beta (N : ℝ) (M : ℝ) :=
    ProbabilityTheory.beta_pos (by exact_mod_cast hN) (by exact_mod_cast hM)
  have hble := beta_nat_le_one hN hM
  rw [one_le_div hbpos]
  exact hble

set_option linter.unusedSectionVars false in
/-- Pointwise lower bound for the integer-parameter Beta density on an
interval `[q,u] ⊂ (0,1)`. -/
theorem betaPDFReal_nat_lower_on_Icc {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    {q u x : ℝ} (hq : 0 < q) (hu : u < 1) (hxq : q ≤ x) (hxu : x ≤ u) :
    q ^ (N - 1) * (1 - u) ^ (M - 1) ≤
      ProbabilityTheory.betaPDFReal (N : ℝ) (M : ℝ) x := by
  have hx0 : 0 < x := lt_of_lt_of_le hq hxq
  have hx1 : x < 1 := lt_of_le_of_lt hxu hu
  rw [ProbabilityTheory.betaPDFReal, if_pos ⟨hx0, hx1⟩]
  have hNexp : (N : ℝ) - 1 = ((N - 1 : ℕ) : ℝ) := by
    have : N = (N - 1) + 1 := (Nat.sub_add_cancel hN).symm
    rw [this]
    norm_num
  have hMexp : (M : ℝ) - 1 = ((M - 1 : ℕ) : ℝ) := by
    have : M = (M - 1) + 1 := (Nat.sub_add_cancel hM).symm
    rw [this]
    norm_num
  rw [hNexp, hMexp, Real.rpow_natCast, Real.rpow_natCast]
  have h1u_nonneg : 0 ≤ 1 - u := by linarith
  have h1x_nonneg : 0 ≤ 1 - x := by linarith
  have hqpow : q ^ (N - 1) ≤ x ^ (N - 1) :=
    pow_le_pow_left₀ hq.le hxq _
  have hupow : (1 - u) ^ (M - 1) ≤ (1 - x) ^ (M - 1) :=
    pow_le_pow_left₀ h1u_nonneg (by linarith) _
  have hbeta := one_le_one_div_beta_nat hN hM
  have hleft_nonneg : 0 ≤ (1 - u) ^ (M - 1) :=
    pow_nonneg h1u_nonneg _
  have hxpow_nonneg : 0 ≤ x ^ (N - 1) :=
    pow_nonneg hx0.le _
  have hypow_nonneg : 0 ≤ (1 - x) ^ (M - 1) :=
    pow_nonneg h1x_nonneg _
  have hfirst :
      q ^ (N - 1) * (1 - u) ^ (M - 1) ≤
        x ^ (N - 1) * (1 - x) ^ (M - 1) :=
    mul_le_mul hqpow hupow hleft_nonneg hxpow_nonneg
  have hxy_nonneg : 0 ≤ x ^ (N - 1) * (1 - x) ^ (M - 1) :=
    mul_nonneg hxpow_nonneg hypow_nonneg
  have hsecond :
      x ^ (N - 1) * (1 - x) ^ (M - 1) ≤
        (1 / ProbabilityTheory.beta (N : ℝ) (M : ℝ)) *
          (x ^ (N - 1) * (1 - x) ^ (M - 1)) := by
    calc
      x ^ (N - 1) * (1 - x) ^ (M - 1) =
          1 * (x ^ (N - 1) * (1 - x) ^ (M - 1)) := by ring
      _ ≤ (1 / ProbabilityTheory.beta (N : ℝ) (M : ℝ)) *
            (x ^ (N - 1) * (1 - x) ^ (M - 1)) :=
          mul_le_mul_of_nonneg_right hbeta hxy_nonneg
  have hsecond' :
      x ^ (N - 1) * (1 - x) ^ (M - 1) ≤
        (1 / ProbabilityTheory.beta (N : ℝ) (M : ℝ)) *
          x ^ (N - 1) * (1 - x) ^ (M - 1) := by
    calc
      x ^ (N - 1) * (1 - x) ^ (M - 1) ≤
          (1 / ProbabilityTheory.beta (N : ℝ) (M : ℝ)) *
            (x ^ (N - 1) * (1 - x) ^ (M - 1)) := hsecond
      _ = (1 / ProbabilityTheory.beta (N : ℝ) (M : ℝ)) *
            x ^ (N - 1) * (1 - x) ^ (M - 1) := by ring
  exact le_trans hfirst hsecond'

set_option linter.unusedSectionVars false in
/-- Interval lower bound for an integer-parameter Beta measure. -/
theorem betaMeasure_nat_real_Icc_lower {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    {q u : ℝ} (hq : 0 < q) (hu : u < 1) (_hqu : q ≤ u) :
    (u - q) * q ^ (N - 1) * (1 - u) ^ (M - 1) ≤
      (ProbabilityTheory.betaMeasure (N : ℝ) (M : ℝ)).real (Set.Icc q u) := by
  let C : ℝ := q ^ (N - 1) * (1 - u) ^ (M - 1)
  have h1u_nonneg : 0 ≤ 1 - u := by linarith
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (pow_nonneg hq.le _) (pow_nonneg h1u_nonneg _)
  have hmeasure :
      (ProbabilityTheory.betaMeasure (N : ℝ) (M : ℝ)) (Set.Icc q u) =
        ∫⁻ x in Set.Icc q u,
          ProbabilityTheory.betaPDF (N : ℝ) (M : ℝ) x := by
    rw [ProbabilityTheory.betaMeasure, withDensity_apply _ measurableSet_Icc]
  have hconst :
      (∫⁻ x in Set.Icc q u, ENNReal.ofReal C ∂(volume : Measure ℝ)) =
        ENNReal.ofReal (C * (u - q)) := by
    rw [lintegral_const]
    simp only [Measure.restrict_apply, MeasurableSet.univ, Set.univ_inter]
    rw [Real.volume_Icc]
    rw [ENNReal.ofReal_mul hCnonneg]
  have hpoint :
      ∀ x ∈ Set.Icc q u,
        ENNReal.ofReal C ≤
          ProbabilityTheory.betaPDF (N : ℝ) (M : ℝ) x := by
    intro x hx
    exact ENNReal.ofReal_le_ofReal
      (by
        dsimp [C]
        exact betaPDFReal_nat_lower_on_Icc hN hM hq hu hx.1 hx.2)
  have hlin : ENNReal.ofReal (C * (u - q)) ≤
      (ProbabilityTheory.betaMeasure (N : ℝ) (M : ℝ)) (Set.Icc q u) := by
    calc
      ENNReal.ofReal (C * (u - q)) =
          ∫⁻ x in Set.Icc q u, ENNReal.ofReal C ∂(volume : Measure ℝ) :=
        hconst.symm
      _ ≤ ∫⁻ x in Set.Icc q u,
            ProbabilityTheory.betaPDF (N : ℝ) (M : ℝ) x ∂(volume : Measure ℝ) :=
        lintegral_mono_ae
          (ae_restrict_of_forall_mem measurableSet_Icc hpoint)
      _ = (ProbabilityTheory.betaMeasure (N : ℝ) (M : ℝ)) (Set.Icc q u) :=
        hmeasure.symm
  have hfinite :
      (ProbabilityTheory.betaMeasure (N : ℝ) (M : ℝ)) (Set.Icc q u) ≠ ∞ := by
    haveI : IsProbabilityMeasure
        (ProbabilityTheory.betaMeasure (N : ℝ) (M : ℝ)) :=
      ProbabilityTheory.isProbabilityMeasureBeta
        (by exact_mod_cast hN) (by exact_mod_cast hM)
    exact measure_ne_top _ _
  have hreal := (ENNReal.ofReal_le_iff_le_toReal hfinite).mp hlin
  rw [Measure.real]
  calc
    (u - q) * q ^ (N - 1) * (1 - u) ^ (M - 1) =
        C * (u - q) := by
      dsimp [C]
      ring
    _ ≤ ENNReal.toReal
        ((ProbabilityTheory.betaMeasure (N : ℝ) (M : ℝ)) (Set.Icc q u)) :=
      hreal

set_option linter.unusedSectionVars false in
/-- The concrete `Beta(N,N*(s-1))` law has the interval lower-bound package
used by the one-column spike proof. -/
theorem betaColumnMeasureIntervalLowerBound_betaColumnMeasure
    {N s : ℕ} (hN : 0 < N) (hOther : 0 < betaColumnOtherShape N s)
    {q₀ δ : ℝ} (hq : 0 < q₀) (hδ : 0 < δ)
    (hupper : betaColumnIntervalUpper q₀ δ < 1) :
    BetaColumnIntervalLowerBound
      (betaColumnMeasureIntervalProbability (betaColumnMeasure N s) q₀ δ)
      N s q₀ δ := by
  let u : ℝ := betaColumnIntervalUpper q₀ δ
  have hqu : q₀ ≤ u := by
    dsimp [u, betaColumnIntervalUpper]
    nlinarith [mul_pos hδ hq]
  have hlower :=
    betaMeasure_nat_real_Icc_lower
      (N := N) (M := betaColumnOtherShape N s)
      hN hOther hq (by simpa [u] using hupper) hqu
  have hkernel :
      betaColumnIntervalKernel N s q₀ δ =
        (u - q₀) * q₀ ^ (N - 1) *
          (1 - u) ^ (betaColumnOtherShape N s - 1) := by
    have hNdecomp : N = (N - 1) + 1 := (Nat.sub_add_cancel hN).symm
    have hpow : q₀ ^ N = q₀ ^ (N - 1) * q₀ := by
      conv_lhs => rw [hNdecomp]
      rw [pow_succ]
    dsimp [u, betaColumnIntervalKernel, betaColumnIntervalUpper]
    rw [hpow]
    ring
  refine ⟨hq, hδ, hupper, ?_⟩
  rw [hkernel]
  simpa [betaColumnMeasureIntervalProbability, betaColumnMeasure,
    betaColumnIntervalSet, u] using hlower

set_option linter.unusedSectionVars false in
/-- No-input interval package for the concrete integer-Beta column law. -/
theorem integerBetaColumnMeasure_betaColumnMeasure
    {N s : ℕ} (hN : 0 < N) (hOther : 0 < betaColumnOtherShape N s) :
    IntegerBetaColumnMeasure (betaColumnMeasure N s) N s where
  interval_lower := by
    intro q₀ δ hq hδ hupper
    exact betaColumnMeasureIntervalLowerBound_betaColumnMeasure
      (N := N) (s := s) hN hOther hq hδ hupper

/-- Exact law statement for the mass of one distinguished sample column:
its pushforward distribution is an integer-Beta measure with parameters
`(N, N*(s-1))`. -/
structure ColumnMassBetaLaw
    (μ : Measure (SampleMatrix p q σ)) (α₀ : σ) (ν : Measure ℝ)
    (N s : ℕ) : Prop where
  map_eq : columnMassPushforward (p := p) (q := q) (σ := σ) μ α₀ = ν
  beta_measure : IntegerBetaColumnMeasure ν N s

set_option linter.unusedSectionVars false in
theorem ColumnMassBetaLaw.of_has_betaMeasure
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ} {N s : ℕ}
    (hLaw : ColumnMassHasBetaMeasure (p := p) (q := q) (σ := σ) μ α₀ N s)
    (hIntervals : IntegerBetaColumnMeasure (betaColumnMeasure N s) N s) :
    ColumnMassBetaLaw (p := p) (q := q) (σ := σ) μ α₀
      (betaColumnMeasure N s) N s where
  map_eq := hLaw
  beta_measure := hIntervals

set_option linter.unusedSectionVars false in
/-- Once the exact pushforward law
`sampleColumnMass α₀ ~ Beta(N,N*(s-1))` is known, the full column-mass Beta
package is no-input: the integer-Beta interval estimates are supplied by the
density calculation above. -/
theorem ColumnMassHasBetaMeasure.columnMassBetaLaw_noInput
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ} {N s : ℕ}
    (hLaw : ColumnMassHasBetaMeasure (p := p) (q := q) (σ := σ) μ α₀ N s)
    (hN : 0 < N) (hOther : 0 < betaColumnOtherShape N s) :
    ColumnMassBetaLaw (p := p) (q := q) (σ := σ) μ α₀
      (betaColumnMeasure N s) N s :=
  ColumnMassBetaLaw.of_has_betaMeasure
    (p := p) (q := q) (σ := σ) hLaw
    (integerBetaColumnMeasure_betaColumnMeasure hN hOther)

set_option linter.unusedSectionVars false in
theorem ColumnMassBetaLaw.interval_probability_eq
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ} {ν : Measure ℝ}
    {N s : ℕ} (I : ColumnMassBetaLaw (p := p) (q := q) (σ := σ) μ α₀ ν N s)
    (q₀ δ : ℝ) :
    columnMassIntervalProbability (p := p) (q := q) (σ := σ) μ α₀ q₀ δ =
      betaColumnMeasureIntervalProbability ν q₀ δ := by
  unfold columnMassIntervalProbability betaColumnMeasureIntervalProbability
  rw [I.map_eq]

/-- The exact column-mass Beta law supplies the finite Beta interval lower
bound used by the spike lower-bound argument. -/
theorem ColumnMassBetaLaw.betaColumnIntervalLowerBound
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ} {ν : Measure ℝ}
    {N s : ℕ} (I : ColumnMassBetaLaw (p := p) (q := q) (σ := σ) μ α₀ ν N s)
    {q₀ δ : ℝ} (hq : 0 < q₀) (hδ : 0 < δ)
    (hupper : betaColumnIntervalUpper q₀ δ < 1) :
    BetaColumnIntervalLowerBound
      (columnMassIntervalProbability (p := p) (q := q) (σ := σ) μ α₀ q₀ δ)
      N s q₀ δ := by
  simpa [I.interval_probability_eq q₀ δ] using
    I.beta_measure.interval_lower hq hδ hupper

set_option linter.unusedSectionVars false in
/-- Direct interval lower bound obtained from the exact
`sampleColumnMass ~ Beta(N,N*(s-1))` law. -/
theorem ColumnMassHasBetaMeasure.betaColumnIntervalLowerBound
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ} {N s : ℕ}
    (hLaw : ColumnMassHasBetaMeasure (p := p) (q := q) (σ := σ) μ α₀ N s)
    (hN : 0 < N) (hOther : 0 < betaColumnOtherShape N s)
    {q₀ δ : ℝ} (hq : 0 < q₀) (hδ : 0 < δ)
    (hupper : betaColumnIntervalUpper q₀ δ < 1) :
    BetaColumnIntervalLowerBound
      (columnMassIntervalProbability (p := p) (q := q) (σ := σ) μ α₀ q₀ δ)
      N s q₀ δ :=
  (hLaw.columnMassBetaLaw_noInput hN hOther).betaColumnIntervalLowerBound
    hq hδ hupper

set_option linter.unusedSectionVars false in
/-- If the column-mass map is measurable, the pushforward interval
probability is the probability of the corresponding event in the original
matrix space. -/
theorem columnMassIntervalProbability_eq_eventProbability
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ} {q₀ δ : ℝ}
    (hmeas :
      Measurable
        (fun X => sampleColumnMass (p := p) (q := q) (σ := σ) X α₀)) :
    columnMassIntervalProbability (p := p) (q := q) (σ := σ) μ α₀ q₀ δ =
      μ.real (columnMassIntervalEvent (p := p) (q := q) (σ := σ) α₀ q₀ δ) := by
  unfold columnMassIntervalProbability columnMassPushforward
    columnMassIntervalEvent betaColumnIntervalSet
  change
    ENNReal.toReal
        ((Measure.map
              (fun X => sampleColumnMass (p := p) (q := q) (σ := σ) X α₀) μ)
          (Set.Icc q₀ (betaColumnIntervalUpper q₀ δ))) =
      ENNReal.toReal
        (μ {X | sampleColumnMass (p := p) (q := q) (σ := σ) X α₀ ∈
          Set.Icc q₀ (betaColumnIntervalUpper q₀ δ)})
  exact congrArg ENNReal.toReal (Measure.map_apply hmeas measurableSet_Icc)

/-- Canonical first Beta parameter: the Hilbert-space dimension of one
sample column. -/
def columnMassBetaMainShape : ℕ :=
  Fintype.card (BipIndex p q)

/-- Canonical sample-column count. -/
def columnMassBetaSampleCount : ℕ :=
  Fintype.card σ

set_option linter.unusedSectionVars false in
theorem betaColumnOtherShape_canonical :
    betaColumnOtherShape
        (columnMassBetaMainShape (p := p) (q := q))
        (columnMassBetaSampleCount (σ := σ)) =
      Fintype.card (BipIndex p q) * (Fintype.card σ - 1) := by
  rfl

/-- Canonical Beta measure for the one-column mass

`R = ‖x_{α₀}‖²`

on the rectangular complex Hilbert--Schmidt sphere.  The parameters are

* `card (BipIndex p q)` for the distinguished column;
* `card (BipIndex p q) * (card σ - 1)` for all remaining columns. -/
noncomputable def canonicalColumnMassBetaMeasure : Measure ℝ :=
  betaColumnMeasure
    (columnMassBetaMainShape (p := p) (q := q))
    (columnMassBetaSampleCount (σ := σ))

set_option linter.unusedSectionVars false in
/-- The canonical one-column Beta law is exactly the left-block mass law for
the Hermitian block decomposition

`ℂ^(BipIndex p q) ⊕ ℂ^(SampleCoord p q (DeletedColumn α₀))`.

This is the finite-cardinality bridge between the abstract block theorem and
the column interface: the right block has
`card (BipIndex p q) * (card σ - 1)` complex coordinates. -/
theorem hermitianBlockMassBetaMeasure_deletedColumn_eq_canonicalColumnMassBetaMeasure
    [DecidableEq σ] (α₀ : σ) :
    hermitianBlockMassBetaMeasure
        (ι := BipIndex p q)
        (κ := PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀)) =
      canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ) := by
  simp [hermitianBlockMassBetaMeasure, canonicalColumnMassBetaMeasure,
    betaColumnMeasure, columnMassBetaMainShape, columnMassBetaSampleCount,
    betaColumnOtherShape, PptFactorization.GaussianModel.SampleCoord]

/-- Exact canonical Beta-law statement for

`R(X) = ‖x_{α₀}‖²`.

This is only the push-forward law of `R`; the interval-density lower bound is
kept in `CanonicalColumnMassBetaLaw`, which additionally records the integer
Beta density estimates needed by the spike lower-bound pipeline. -/
def ColumnMassRHasCanonicalBetaLaw
    (μ : Measure (SampleMatrix p q σ)) (α₀ : σ) : Prop :=
  ColumnMassHasBetaMeasure
    (p := p) (q := q) (σ := σ) μ α₀
    (columnMassBetaMainShape (p := p) (q := q))
    (columnMassBetaSampleCount (σ := σ))

set_option linter.unusedSectionVars false in
/-- Unfolding of the canonical Beta-law statement for `R`. -/
theorem columnMassRHasCanonicalBetaLaw_iff_map_eq
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ} :
    ColumnMassRHasCanonicalBetaLaw (p := p) (q := q) (σ := σ) μ α₀ ↔
      columnMassPushforward (p := p) (q := q) (σ := σ) μ α₀ =
        canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ) := by
  rfl

set_option linter.unusedSectionVars false in
/-- The canonical Beta-law statement for `R`, in `HasLaw` form. -/
theorem ColumnMassRHasCanonicalBetaLaw.hasLaw
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    (h :
      ColumnMassRHasCanonicalBetaLaw
        (p := p) (q := q) (σ := σ) μ α₀)
    (hmeas :
      AEMeasurable
        (fun X => sampleColumnMass (p := p) (q := q) (σ := σ) X α₀) μ) :
    ProbabilityTheory.HasLaw
      (fun X => sampleColumnMass (p := p) (q := q) (σ := σ) X α₀)
      (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ)) μ := by
  exact
    ColumnMassHasBetaMeasure.hasLaw
      (p := p) (q := q) (σ := σ)
      (N := columnMassBetaMainShape (p := p) (q := q))
      (s := columnMassBetaSampleCount (σ := σ)) h hmeas

set_option linter.unusedSectionVars false in
/-- `HasLaw` form implies the canonical push-forward Beta law for `R`. -/
theorem ColumnMassRHasCanonicalBetaLaw.of_hasLaw
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    (h :
      ProbabilityTheory.HasLaw
        (fun X => sampleColumnMass (p := p) (q := q) (σ := σ) X α₀)
        (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ)) μ) :
    ColumnMassRHasCanonicalBetaLaw
      (p := p) (q := q) (σ := σ) μ α₀ := by
  exact
    ColumnMassHasBetaMeasure.of_hasLaw
      (p := p) (q := q) (σ := σ)
      (N := columnMassBetaMainShape (p := p) (q := q))
      (s := columnMassBetaSampleCount (σ := σ)) h

set_option linter.unusedSectionVars false in
/-- Positivity of the first canonical Beta parameter in the nonempty
bipartite Hilbert space. -/
theorem columnMassBetaMainShape_pos [Nonempty p] [Nonempty q] :
    0 < columnMassBetaMainShape (p := p) (q := q) := by
  unfold columnMassBetaMainShape
  exact Fintype.card_pos

set_option linter.unusedSectionVars false in
/-- Positivity of the second canonical Beta parameter when at least two sample
columns are present. -/
theorem betaColumnOtherShape_canonical_pos
    [Nonempty p] [Nonempty q]
    (hσ : 2 ≤ Fintype.card σ) :
    0 <
      betaColumnOtherShape
        (columnMassBetaMainShape (p := p) (q := q))
        (columnMassBetaSampleCount (σ := σ)) := by
  have hN : 0 < columnMassBetaMainShape (p := p) (q := q) :=
    columnMassBetaMainShape_pos (p := p) (q := q)
  have hs_sub : 0 < Fintype.card σ - 1 := by omega
  unfold betaColumnOtherShape columnMassBetaSampleCount
  exact Nat.mul_pos hN hs_sub

set_option linter.unusedSectionVars false in
/-- The canonical Beta measure is a probability measure in the genuine
nondegenerate case `card(p×q)>0` and `card σ ≥ 2`. -/
theorem canonicalColumnMassBetaMeasure_isProbabilityMeasure
    [Nonempty p] [Nonempty q]
    (hσ : 2 ≤ Fintype.card σ) :
    IsProbabilityMeasure
      (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ)) := by
  unfold canonicalColumnMassBetaMeasure betaColumnMeasure
  exact ProbabilityTheory.isProbabilityMeasureBeta
    (by
      exact_mod_cast columnMassBetaMainShape_pos (p := p) (q := q))
    (by
      exact_mod_cast
        betaColumnOtherShape_canonical_pos
          (p := p) (q := q) (σ := σ) hσ)

set_option linter.unusedSectionVars false in
/-- Canonical no-input integer-Beta interval package for the one-column mass
law. -/
theorem canonicalIntegerBetaColumnMeasure
    [Nonempty p] [Nonempty q]
    (hσ : 2 ≤ Fintype.card σ) :
    IntegerBetaColumnMeasure
      (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ))
      (columnMassBetaMainShape (p := p) (q := q))
      (columnMassBetaSampleCount (σ := σ)) := by
  unfold canonicalColumnMassBetaMeasure
  exact
    integerBetaColumnMeasure_betaColumnMeasure
      (N := columnMassBetaMainShape (p := p) (q := q))
      (s := columnMassBetaSampleCount (σ := σ))
      (columnMassBetaMainShape_pos (p := p) (q := q))
      (betaColumnOtherShape_canonical_pos
        (p := p) (q := q) (σ := σ) hσ)

/-- Canonical form of the one-column Beta law for a measure on the rectangular
complex Hilbert--Schmidt sphere/model space. -/
def CanonicalColumnMassBetaLaw
    (μ : Measure (SampleMatrix p q σ)) (α₀ : σ) : Prop :=
  ∃ ν : Measure ℝ,
    ColumnMassBetaLaw (p := p) (q := q) (σ := σ) μ α₀ ν
      (columnMassBetaMainShape (p := p) (q := q))
      (columnMassBetaSampleCount (σ := σ))

/-- Build the full canonical column-mass Beta law from the exact push-forward
law of `R` and the integer-Beta interval lower-bound package. -/
theorem CanonicalColumnMassBetaLaw.of_R_hasCanonicalBetaLaw
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    (hR :
      ColumnMassRHasCanonicalBetaLaw
        (p := p) (q := q) (σ := σ) μ α₀)
    (hIntervals :
      IntegerBetaColumnMeasure
        (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ))
        (columnMassBetaMainShape (p := p) (q := q))
        (columnMassBetaSampleCount (σ := σ))) :
    CanonicalColumnMassBetaLaw (p := p) (q := q) (σ := σ) μ α₀ := by
  refine ⟨canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ), ?_⟩
  exact
    ColumnMassBetaLaw.of_has_betaMeasure
      (p := p) (q := q) (σ := σ)
      (N := columnMassBetaMainShape (p := p) (q := q))
      (s := columnMassBetaSampleCount (σ := σ))
      hR hIntervals

/-- The canonical one-column Beta law gives the interval lower bound with
parameters `(card (BipIndex p q), card σ)`. -/
theorem CanonicalColumnMassBetaLaw.betaColumnIntervalLowerBound
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    (I : CanonicalColumnMassBetaLaw (p := p) (q := q) (σ := σ) μ α₀)
    {q₀ δ : ℝ} (hq : 0 < q₀) (hδ : 0 < δ)
    (hupper : betaColumnIntervalUpper q₀ δ < 1) :
    BetaColumnIntervalLowerBound
      (columnMassIntervalProbability (p := p) (q := q) (σ := σ) μ α₀ q₀ δ)
      (columnMassBetaMainShape (p := p) (q := q))
      (columnMassBetaSampleCount (σ := σ)) q₀ δ := by
  rcases I with ⟨ν, hν⟩
  exact hν.betaColumnIntervalLowerBound hq hδ hupper

end ColumnMassBetaLaw

/-! ### Spherical one-column decomposition and independence -/

/-- Column `α₀` as an ambient vector in the bipartite Hilbert space. -/
noncomputable def sampleColumnVector
    (X : SampleMatrix p q σ) (α₀ : σ) :
    EuclideanSpace ℂ (BipIndex p q) :=
  PptFactorization.GaussianModel.columnVector X α₀

/-- Normalized direction of column `α₀`, as an ambient vector.

The definition is total: if the column is zero this returns zero.  Under the
intended spherical law the zero-column event is null, while this total version
keeps all event maps definable without partial functions. -/
noncomputable def sampleColumnDirection
    (X : SampleMatrix p q σ) (α₀ : σ) :
    EuclideanSpace ℂ (BipIndex p q) :=
  ((‖sampleColumnVector (p := p) (q := q) (σ := σ) X α₀‖)⁻¹ : ℂ) •
    sampleColumnVector (p := p) (q := q) (σ := σ) X α₀

set_option linter.unusedSectionVars false in
theorem hermitianBlockLeft_deletedColumnBlockVector
    (X : SampleMatrix p q σ) (α₀ : σ) :
    hermitianBlockLeft
        (ι := BipIndex p q)
        (κ := PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀))
        (deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀ X) =
      sampleColumnVector (p := p) (q := q) (σ := σ) X α₀ := by
  ext i
  rfl

set_option linter.unusedSectionVars false in
theorem hermitianBlockLeftDirection_deletedColumnBlockVector
    (X : SampleMatrix p q σ) (α₀ : σ) :
    hermitianBlockLeftDirection
        (ι := BipIndex p q)
        (κ := PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀))
        (deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀ X) =
      sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀ := by
  unfold hermitianBlockLeftDirection sampleColumnDirection
  rw [hermitianBlockLeft_deletedColumnBlockVector
    (p := p) (q := q) (σ := σ) X α₀]

set_option linter.unusedSectionVars false in
theorem frobeniusNorm_sampleColumnPart_eq_norm_sampleColumnVector
    (X : SampleMatrix p q σ) (α₀ : σ) :
    frobeniusNorm
        (p := p) (q := q) (σ := σ)
        (sampleColumnPart (p := p) (q := q) (σ := σ) X α₀) =
      ‖sampleColumnVector (p := p) (q := q) (σ := σ) X α₀‖ := by
  unfold frobeniusNorm
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [Matrix.frobenius_norm_def, EuclideanSpace.norm_sq_eq]
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt]
  · have hinner :
        ∀ i : BipIndex p q,
          (∑ α : σ, ‖(if α = α₀ then X i α else 0 : ℂ)‖ ^ 2) =
            ‖X i α₀‖ ^ 2 := by
        intro i
        rw [Finset.sum_eq_single α₀]
        · simp
        · intro α _ hα
          simp [hα]
        · intro hα₀
          exact (hα₀ (Finset.mem_univ α₀)).elim
    simp [sampleColumnPart, sampleColumnVector,
      PptFactorization.GaussianModel.columnVector, hinner]
  · exact Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun α _ => by positivity

set_option linter.unusedSectionVars false in
theorem hermitianBlockRight_deletedColumnBlockVector
    (X : SampleMatrix p q σ) (α₀ : σ) :
    hermitianBlockRight
        (ι := BipIndex p q)
        (κ := PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀))
        (deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀ X) =
      sampleMatrixComplexLinearIsometryEquiv
        (p := p) (q := q) (σ := DeletedColumn α₀)
        (sampleDeletedColumns (p := p) (q := q) (σ := σ) X α₀) := by
  ext a
  rfl

set_option linter.unusedSectionVars false in
theorem frobeniusNorm_sampleDeletedColumns_eq_sampleColumnComplement
    (X : SampleMatrix p q σ) (α₀ : σ) :
    frobeniusNorm
        (p := p) (q := q) (σ := DeletedColumn α₀)
        (sampleDeletedColumns (p := p) (q := q) (σ := σ) X α₀) =
      frobeniusNorm
        (p := p) (q := q) (σ := σ)
        (sampleColumnComplement (p := p) (q := q) (σ := σ) X α₀) := by
  unfold frobeniusNorm
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [Matrix.frobenius_norm_def, Matrix.frobenius_norm_def]
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  rw [Real.sq_sqrt, Real.sq_sqrt]
  · have hinner :
        ∀ i : BipIndex p q,
          (∑ α : DeletedColumn α₀, ‖X i α.1‖ ^ 2) =
            ∑ α : σ, ‖(if α = α₀ then 0 else X i α : ℂ)‖ ^ 2 := by
        intro i
        calc
          (∑ α : DeletedColumn α₀, ‖X i α.1‖ ^ 2) =
              (∑ α ∈ (Finset.univ.filter (fun α : σ => α ≠ α₀)),
                ‖X i α‖ ^ 2) := by
                symm
                exact
                  Finset.sum_subtype
                    (s := Finset.univ.filter (fun α : σ => α ≠ α₀))
                    (p := fun α : σ => α ≠ α₀)
                    (by intro α; simp)
                    (fun α : σ => ‖X i α‖ ^ 2)
          _ = ∑ α : σ, ‖(if α = α₀ then 0 else X i α : ℂ)‖ ^ 2 := by
                rw [Finset.sum_filter]
                refine Finset.sum_congr rfl ?_
                intro α _
                by_cases hα : α = α₀ <;> simp [hα]
    exact Finset.sum_congr rfl fun i _ => by
      simpa [sampleDeletedColumns, sampleColumnComplement] using hinner i
  · exact Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun α _ => by positivity
  · exact Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun α _ => by positivity

set_option linter.unusedSectionVars false in
theorem hermitianBlockMass_deletedColumnBlockVector
    (X : SampleMatrix p q σ) (α₀ : σ) :
    hermitianBlockMass
        (ι := BipIndex p q)
        (κ := PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀))
        (deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀ X) =
      sampleColumnMass (p := p) (q := q) (σ := σ) X α₀ := by
  unfold hermitianBlockMass sampleColumnMass
  rw [hermitianBlockLeft_deletedColumnBlockVector
    (p := p) (q := q) (σ := σ) X α₀]
  rw [frobeniusNorm_sampleColumnPart_eq_norm_sampleColumnVector
    (p := p) (q := q) (σ := σ) X α₀]

set_option linter.unusedSectionVars false in
@[fun_prop]
theorem measurable_sampleColumnVector (α₀ : σ) :
    Measurable
      (fun X : SampleMatrix p q σ =>
        sampleColumnVector (p := p) (q := q) (σ := σ) X α₀) := by
  unfold sampleColumnVector PptFactorization.GaussianModel.columnVector
  have hcont_raw :
      Continuous
        (fun X : SampleMatrix p q σ =>
          fun i : BipIndex p q => X i α₀) := by
    exact continuous_pi fun i =>
      ((continuous_apply α₀ : Continuous fun row : σ → ℂ => row α₀).comp
        (continuous_apply i :
          Continuous fun X : SampleMatrix p q σ => X i))
  exact ((PiLp.continuous_toLp 2 _).comp hcont_raw).measurable

@[fun_prop]
theorem measurable_sampleColumnDirection (α₀ : σ) :
    Measurable
      (fun X : SampleMatrix p q σ =>
        sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀) := by
  unfold sampleColumnDirection
  fun_prop

/-! ### Law of the one-column direction cap -/

/-- Pushforward law of the distinguished column direction `u`. -/
noncomputable def columnDirectionPushforward
    [MeasurableSpace (SampleMatrix p q σ)]
    (μ : Measure (SampleMatrix p q σ)) (α₀ : σ) :
    Measure (EuclideanSpace ℂ (BipIndex p q)) :=
  Measure.map
    (fun X => sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀) μ

/-- Probability, computed from the pushforward direction law, that the
distinguished column direction lies in the ambient projective cap around `e`. -/
noncomputable def columnDirectionCapProbability
    [MeasurableSpace (SampleMatrix p q σ)]
    (μ : Measure (SampleMatrix p q σ)) (α₀ : σ)
    (e : EuclideanSpace ℂ (BipIndex p q)) (r : ℝ) : ℝ :=
  ambientProjectiveCapProbability
    (ι := BipIndex p q)
    (columnDirectionPushforward (p := p) (q := q) (σ := σ) μ α₀) e r

/-- Exact ambient projective-cap law for the distinguished column direction. -/
def ColumnDirectionHasAmbientCapLaw
    [MeasurableSpace (SampleMatrix p q σ)]
    (μ : Measure (SampleMatrix p q σ)) (α₀ : σ)
    (e : EuclideanSpace ℂ (BipIndex p q)) (N : ℕ) (r : ℝ) : Prop :=
  AmbientProjectiveCapExactVolume
    (ι := BipIndex p q)
    (columnDirectionPushforward (p := p) (q := q) (σ := σ) μ α₀) e N r

/-- Canonical cap-law statement for `u`: the ambient dimension is
`card (BipIndex p q)`. -/
def ColumnDirectionHasCanonicalCapLaw
    [MeasurableSpace (SampleMatrix p q σ)]
    (μ : Measure (SampleMatrix p q σ)) (α₀ : σ)
    (e : EuclideanSpace ℂ (BipIndex p q)) (r : ℝ) : Prop :=
  ColumnDirectionHasAmbientCapLaw
    (p := p) (q := q) (σ := σ) μ α₀ e
    (columnMassBetaMainShape (p := p) (q := q)) r

/-- Unit-vector version of the exact ambient projective-cap law for the
distinguished column direction.  This is the preferred interface for the
canonical Haar/projective-cap theorem. -/
def ColumnDirectionHasUnitAmbientCapLaw
    [MeasurableSpace (SampleMatrix p q σ)]
    (μ : Measure (SampleMatrix p q σ)) (α₀ : σ)
    (e : EuclideanSpace ℂ (BipIndex p q)) (N : ℕ) (r : ℝ) : Prop :=
  UnitAmbientProjectiveCapExactVolume
    (ι := BipIndex p q)
    (columnDirectionPushforward (p := p) (q := q) (σ := σ) μ α₀) e N r

/-- Canonical unit-vector cap-law statement for `u`: the ambient dimension is
`card (BipIndex p q)`. -/
def ColumnDirectionHasUnitCanonicalCapLaw
    [MeasurableSpace (SampleMatrix p q σ)]
    (μ : Measure (SampleMatrix p q σ)) (α₀ : σ)
    (e : EuclideanSpace ℂ (BipIndex p q)) (r : ℝ) : Prop :=
  ColumnDirectionHasUnitAmbientCapLaw
    (p := p) (q := q) (σ := σ) μ α₀ e
    (columnMassBetaMainShape (p := p) (q := q)) r

set_option linter.unusedSectionVars false in
/-- The unit-vector column cap law forgets to the legacy exact cap-law
interface. -/
theorem ColumnDirectionHasUnitAmbientCapLaw.toColumnDirectionHasAmbientCapLaw
    [MeasurableSpace (SampleMatrix p q σ)]
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {e : EuclideanSpace ℂ (BipIndex p q)} {N : ℕ} {r : ℝ}
    (I :
      ColumnDirectionHasUnitAmbientCapLaw
        (p := p) (q := q) (σ := σ) μ α₀ e N r) :
    ColumnDirectionHasAmbientCapLaw
      (p := p) (q := q) (σ := σ) μ α₀ e N r := by
  change AmbientProjectiveCapExactVolume
    (ι := BipIndex p q)
    (columnDirectionPushforward (p := p) (q := q) (σ := σ) μ α₀) e N r
  exact UnitAmbientProjectiveCapExactVolume.toAmbientProjectiveCapExactVolume I

set_option linter.unusedSectionVars false in
/-- The canonical unit-vector column cap law forgets to the legacy canonical
cap-law interface. -/
theorem ColumnDirectionHasUnitCanonicalCapLaw.toColumnDirectionHasCanonicalCapLaw
    [MeasurableSpace (SampleMatrix p q σ)]
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {e : EuclideanSpace ℂ (BipIndex p q)} {r : ℝ}
    (I :
      ColumnDirectionHasUnitCanonicalCapLaw
        (p := p) (q := q) (σ := σ) μ α₀ e r) :
    ColumnDirectionHasCanonicalCapLaw
      (p := p) (q := q) (σ := σ) μ α₀ e r := by
  exact
    ColumnDirectionHasUnitAmbientCapLaw.toColumnDirectionHasAmbientCapLaw
      (p := p) (q := q) (σ := σ) I

set_option linter.unusedSectionVars false in
/-- Exact cap law for the column direction supplies the finite cap lower-bound
interface. -/
theorem ColumnDirectionHasAmbientCapLaw.toProjectiveCapProbabilityLowerBound
    [MeasurableSpace (SampleMatrix p q σ)]
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {e : EuclideanSpace ℂ (BipIndex p q)} {N : ℕ} {r : ℝ}
    (I :
      ColumnDirectionHasAmbientCapLaw
        (p := p) (q := q) (σ := σ) μ α₀ e N r) :
    ProjectiveCapProbabilityLowerBound
      (columnDirectionCapProbability (p := p) (q := q) (σ := σ) μ α₀ e r)
      N r := by
  change ProjectiveCapProbabilityLowerBound
    (ambientProjectiveCapProbability
      (ι := BipIndex p q)
      (columnDirectionPushforward (p := p) (q := q) (σ := σ) μ α₀) e r)
    N r
  exact AmbientProjectiveCapExactVolume.toProjectiveCapProbabilityLowerBound I

set_option linter.unusedSectionVars false in
/-- Unit-vector exact cap law for the column direction supplies the same finite
cap lower-bound interface. -/
theorem ColumnDirectionHasUnitAmbientCapLaw.toProjectiveCapProbabilityLowerBound
    [MeasurableSpace (SampleMatrix p q σ)]
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {e : EuclideanSpace ℂ (BipIndex p q)} {N : ℕ} {r : ℝ}
    (I :
      ColumnDirectionHasUnitAmbientCapLaw
        (p := p) (q := q) (σ := σ) μ α₀ e N r) :
    ProjectiveCapProbabilityLowerBound
      (columnDirectionCapProbability (p := p) (q := q) (σ := σ) μ α₀ e r)
      N r :=
  I.toColumnDirectionHasAmbientCapLaw.toProjectiveCapProbabilityLowerBound

set_option linter.unusedSectionVars false in
/-- Canonical cap law at radius `1/N` gives the coarse `exp[-2N log N]`
lower-bound interface. -/
theorem ColumnDirectionHasCanonicalCapLaw.toCapProbabilityLowerBound_inv
    [MeasurableSpace (SampleMatrix p q σ)]
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {e : EuclideanSpace ℂ (BipIndex p q)}
    (I :
      ColumnDirectionHasCanonicalCapLaw
        (p := p) (q := q) (σ := σ) μ α₀ e
        (1 / (columnMassBetaMainShape (p := p) (q := q) : ℝ)))
    (hN : 1 ≤ columnMassBetaMainShape (p := p) (q := q)) :
    CapProbabilityLowerBound
      (columnDirectionCapProbability
        (p := p) (q := q) (σ := σ) μ α₀ e
        (1 / (columnMassBetaMainShape (p := p) (q := q) : ℝ)))
      (columnMassBetaMainShape (p := p) (q := q) : ℝ) 2 := by
  change CapProbabilityLowerBound
    (ambientProjectiveCapProbability
      (ι := BipIndex p q)
      (columnDirectionPushforward (p := p) (q := q) (σ := σ) μ α₀) e
      (1 / (columnMassBetaMainShape (p := p) (q := q) : ℝ)))
    (columnMassBetaMainShape (p := p) (q := q) : ℝ) 2
  exact AmbientProjectiveCapExactVolume.toCapProbabilityLowerBound_inv I hN

set_option linter.unusedSectionVars false in
/-- Unit-vector canonical cap law at radius `1/N` gives the same coarse
`exp[-2N log N]` lower-bound interface. -/
theorem ColumnDirectionHasUnitCanonicalCapLaw.toCapProbabilityLowerBound_inv
    [MeasurableSpace (SampleMatrix p q σ)]
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {e : EuclideanSpace ℂ (BipIndex p q)}
    (I :
      ColumnDirectionHasUnitCanonicalCapLaw
        (p := p) (q := q) (σ := σ) μ α₀ e
        (1 / (columnMassBetaMainShape (p := p) (q := q) : ℝ)))
    (hN : 1 ≤ columnMassBetaMainShape (p := p) (q := q)) :
    CapProbabilityLowerBound
      (columnDirectionCapProbability
        (p := p) (q := q) (σ := σ) μ α₀ e
        (1 / (columnMassBetaMainShape (p := p) (q := q) : ℝ)))
      (columnMassBetaMainShape (p := p) (q := q) : ℝ) 2 :=
  I.toColumnDirectionHasCanonicalCapLaw.toCapProbabilityLowerBound_inv hN

/-! #### Beta-first cap law for the actual column direction -/

set_option linter.unusedSectionVars false in
/-- Column-facing projective cap lower bound obtained from the Beta law of the
squared overlap.

This is the intended order for probabilistic column/cap interfaces:

1. identify the law of `|⟪e,u_α⟫|²` as `Beta(1,N-1)`;
2. use the scalar Beta tail calculation to get the exact cap probability;
3. forget the exact value to the lower-bound package consumed by the spike
   pipeline. -/
theorem columnDirectionProjectiveCapProbabilityLowerBound_inv_of_hasLaw_betaMeasure
    [MeasurableSpace (SampleMatrix p q σ)]
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {e : EuclideanSpace ℂ (BipIndex p q)}
    (hN : 2 ≤ columnMassBetaMainShape (p := p) (q := q))
    (he : ‖e‖ = 1)
    (hLaw :
      ProbabilityTheory.HasLaw
        (ambientProjectiveOverlapSq (ι := BipIndex p q) e)
        (ProbabilityTheory.betaMeasure (1 : ℝ)
          (((columnMassBetaMainShape (p := p) (q := q)) - 1 : ℕ) : ℝ))
        (columnDirectionPushforward (p := p) (q := q) (σ := σ) μ α₀)) :
    ProjectiveCapProbabilityLowerBound
      (columnDirectionCapProbability
        (p := p) (q := q) (σ := σ) μ α₀ e
        (1 / (columnMassBetaMainShape (p := p) (q := q) : ℝ)))
      (columnMassBetaMainShape (p := p) (q := q))
      (1 / (columnMassBetaMainShape (p := p) (q := q) : ℝ)) := by
  have hNposℝ :
      0 < (columnMassBetaMainShape (p := p) (q := q) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hN)
  have hr :
      0 < (1 / (columnMassBetaMainShape (p := p) (q := q) : ℝ)) :=
    one_div_pos.mpr hNposℝ
  have hr1 :
      (1 / (columnMassBetaMainShape (p := p) (q := q) : ℝ)) ≤ 1 := by
    have hNge1 :
        (1 : ℝ) ≤ (columnMassBetaMainShape (p := p) (q := q) : ℝ) := by
      exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hN)
    simpa [one_div] using inv_le_one_of_one_le₀ hNge1
  change ProjectiveCapProbabilityLowerBound
    (ambientProjectiveCapProbability
      (ι := BipIndex p q)
      (columnDirectionPushforward (p := p) (q := q) (σ := σ) μ α₀)
      e (1 / (columnMassBetaMainShape (p := p) (q := q) : ℝ)))
    (columnMassBetaMainShape (p := p) (q := q))
    (1 / (columnMassBetaMainShape (p := p) (q := q) : ℝ))
  exact
    (betaMeasure_one_nat_sub_hasLaw_toUnitAmbientProjectiveCapExactVolume
      (ι := BipIndex p q) hN he hLaw hr hr1).toProjectiveCapProbabilityLowerBound

set_option linter.unusedSectionVars false in
/-- Coarse `exp[-2N log N]` column cap lower bound obtained from the Beta law
of the squared overlap. -/
theorem columnDirectionCapProbabilityLowerBound_inv_of_hasLaw_betaMeasure
    [MeasurableSpace (SampleMatrix p q σ)]
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {e : EuclideanSpace ℂ (BipIndex p q)}
    (hN : 2 ≤ columnMassBetaMainShape (p := p) (q := q))
    (he : ‖e‖ = 1)
    (hLaw :
      ProbabilityTheory.HasLaw
        (ambientProjectiveOverlapSq (ι := BipIndex p q) e)
        (ProbabilityTheory.betaMeasure (1 : ℝ)
          (((columnMassBetaMainShape (p := p) (q := q)) - 1 : ℕ) : ℝ))
        (columnDirectionPushforward (p := p) (q := q) (σ := σ) μ α₀)) :
    CapProbabilityLowerBound
      (columnDirectionCapProbability
        (p := p) (q := q) (σ := σ) μ α₀ e
        (1 / (columnMassBetaMainShape (p := p) (q := q) : ℝ)))
      (columnMassBetaMainShape (p := p) (q := q) : ℝ) 2 := by
  have hN1 :
      1 ≤ columnMassBetaMainShape (p := p) (q := q) :=
    le_trans (by norm_num : 1 ≤ 2) hN
  exact
    (columnDirectionProjectiveCapProbabilityLowerBound_inv_of_hasLaw_betaMeasure
      (p := p) (q := q) (σ := σ) (μ := μ) (α₀ := α₀)
      hN he hLaw).toCapProbabilityLowerBound_inv hN1

set_option linter.unusedSectionVars false in
/-- If the actual pushforward law of the normalized distinguished column
direction has the exact Haar/projective overlap law, then the column direction
has the canonical unit cap law immediately.

This is the column-facing version of the Haar/projective theorem: downstream
code no longer has to manufacture an intermediate `UnitAmbientProjectiveCapExactVolume`
input by hand. -/
theorem AmbientHaarProjectiveOverlapBetaLaw.toColumnDirectionHasUnitCanonicalCapLaw
    [MeasurableSpace (SampleMatrix p q σ)]
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    (H :
      AmbientHaarProjectiveOverlapBetaLaw
        (ι := BipIndex p q)
        (columnDirectionPushforward (p := p) (q := q) (σ := σ) μ α₀))
    {e : EuclideanSpace ℂ (BipIndex p q)} (he : ‖e‖ = 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ColumnDirectionHasUnitCanonicalCapLaw
      (p := p) (q := q) (σ := σ) μ α₀ e r := by
  change UnitAmbientProjectiveCapExactVolume
    (ι := BipIndex p q)
    (columnDirectionPushforward (p := p) (q := q) (σ := σ) μ α₀)
    e (columnMassBetaMainShape (p := p) (q := q)) r
  simpa [columnMassBetaMainShape] using
    (H.toUnitAmbientProjectiveCapExactVolume (ι := BipIndex p q) he hr hr1)

set_option linter.unusedSectionVars false in
/-- Probability form for the actual column direction:

`P(|⟪e,u_α⟫|² ≥ 1-r²) = r^(2(N-1))`,

where `N = card (BipIndex p q)`, once the column-direction pushforward has the
exact Haar/projective overlap law. -/
theorem AmbientHaarProjectiveOverlapBetaLaw.columnDirectionCapProbability_eq
    [MeasurableSpace (SampleMatrix p q σ)]
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    (H :
      AmbientHaarProjectiveOverlapBetaLaw
        (ι := BipIndex p q)
        (columnDirectionPushforward (p := p) (q := q) (σ := σ) μ α₀))
    {e : EuclideanSpace ℂ (BipIndex p q)} (he : ‖e‖ = 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    columnDirectionCapProbability
        (p := p) (q := q) (σ := σ) μ α₀ e r =
      r ^ (2 * (columnMassBetaMainShape (p := p) (q := q) - 1)) := by
  have hcap :=
    H.toColumnDirectionHasUnitCanonicalCapLaw
      (p := p) (q := q) (σ := σ) (μ := μ) (α₀ := α₀)
      he hr hr1
  change ambientProjectiveCapProbability
      (ι := BipIndex p q)
      (columnDirectionPushforward (p := p) (q := q) (σ := σ) μ α₀)
      e r =
    r ^ (2 * (columnMassBetaMainShape (p := p) (q := q) - 1))
  simpa [projectiveCapKernel] using hcap.prob_eq

set_option linter.unusedSectionVars false in
/-- Explicit law form for the actual column direction:

under the Haar/projective law of the column-direction pushforward, the squared
overlap with any unit vector has law `Beta(1,N-1)`, where
`N = card (BipIndex p q)`. -/
theorem AmbientHaarProjectiveOverlapBetaLaw.columnDirectionProjectiveOverlapSqLaw_eq_betaMeasure
    [MeasurableSpace (SampleMatrix p q σ)]
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    (H :
      AmbientHaarProjectiveOverlapBetaLaw
        (ι := BipIndex p q)
        (columnDirectionPushforward (p := p) (q := q) (σ := σ) μ α₀))
    {e : EuclideanSpace ℂ (BipIndex p q)} (he : ‖e‖ = 1) :
    ambientProjectiveOverlapSqLaw
        (ι := BipIndex p q)
        (columnDirectionPushforward (p := p) (q := q) (σ := σ) μ α₀)
        e =
      ProbabilityTheory.betaMeasure (1 : ℝ)
        (((columnMassBetaMainShape (p := p) (q := q)) - 1 : ℕ) : ℝ) := by
  simpa [columnMassBetaMainShape] using
    (H.ambientProjectiveOverlapSqLaw_eq_betaMeasure
      (ι := BipIndex p q) he)

set_option linter.unusedSectionVars false in
/-- Explicit `HasLaw` form for the actual column direction. -/
theorem AmbientHaarProjectiveOverlapBetaLaw.hasLaw_columnDirectionProjectiveOverlapSq
    [MeasurableSpace (SampleMatrix p q σ)]
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    (H :
      AmbientHaarProjectiveOverlapBetaLaw
        (ι := BipIndex p q)
        (columnDirectionPushforward (p := p) (q := q) (σ := σ) μ α₀))
    {e : EuclideanSpace ℂ (BipIndex p q)} (he : ‖e‖ = 1) :
    ProbabilityTheory.HasLaw
      (ambientProjectiveOverlapSq (ι := BipIndex p q) e)
      (ProbabilityTheory.betaMeasure (1 : ℝ)
        (((columnMassBetaMainShape (p := p) (q := q)) - 1 : ℕ) : ℝ))
      (columnDirectionPushforward (p := p) (q := q) (σ := σ) μ α₀) := by
  simpa [columnMassBetaMainShape] using
    (H.hasLaw_ambientProjectiveOverlapSq (ι := BipIndex p q) he)

set_option linter.unusedSectionVars false in
/-- Column-facing tail-extensional constructor.

To prove the exact Haar/projective law for the actual column direction, it is
enough to prove the `Ici a` tails of the squared overlap with every unit
direction.  This is the final logical wrapper before the genuinely geometric
Haar/projective cap-volume calculation. -/
theorem AmbientHaarProjectiveOverlapBetaLaw.of_columnDirection_Ici_tail_eq_beta
    [MeasurableSpace (SampleMatrix p q σ)]
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    [IsProbabilityMeasure
      (columnDirectionPushforward (p := p) (q := q) (σ := σ) μ α₀)]
    (hN : 2 ≤ columnMassBetaMainShape (p := p) (q := q))
    (hTail :
      ∀ {e : EuclideanSpace ℂ (BipIndex p q)}, ‖e‖ = 1 → ∀ a : ℝ,
        (ambientProjectiveOverlapSqLaw
          (ι := BipIndex p q)
          (columnDirectionPushforward (p := p) (q := q) (σ := σ) μ α₀)
          e).real (Set.Ici a) =
          (ProbabilityTheory.betaMeasure (1 : ℝ)
            (((columnMassBetaMainShape (p := p) (q := q)) - 1 : ℕ) : ℝ)).real
              (Set.Ici a)) :
    AmbientHaarProjectiveOverlapBetaLaw
      (ι := BipIndex p q)
      (columnDirectionPushforward (p := p) (q := q) (σ := σ) μ α₀) := by
  refine
    AmbientHaarProjectiveOverlapBetaLaw.of_forall_Ici_tail_eq_beta
      (ι := BipIndex p q)
      (μ := columnDirectionPushforward (p := p) (q := q) (σ := σ) μ α₀)
      ?_ ?_
  · simpa [columnMassBetaMainShape] using hN
  · intro e he a
    simpa [columnMassBetaMainShape] using hTail he a

set_option linter.unusedSectionVars false in
/-- Column-facing lower-bound package at the spike radius `1/N`.

This is the exact object consumed by the one-column lower-bound pipeline:
from the Haar/projective law of the **actual column direction pushforward**,
the theorem obtains the `ProjectiveCapProbabilityLowerBound` for
`columnDirectionCapProbability`, with no separate cap-volume input. -/
theorem AmbientHaarProjectiveOverlapBetaLaw.toColumnDirectionProjectiveCapProbabilityLowerBound_inv
    [MeasurableSpace (SampleMatrix p q σ)]
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    (H :
      AmbientHaarProjectiveOverlapBetaLaw
        (ι := BipIndex p q)
        (columnDirectionPushforward (p := p) (q := q) (σ := σ) μ α₀))
    {e : EuclideanSpace ℂ (BipIndex p q)} (he : ‖e‖ = 1) :
    ProjectiveCapProbabilityLowerBound
      (columnDirectionCapProbability
        (p := p) (q := q) (σ := σ) μ α₀ e
        (1 / (columnMassBetaMainShape (p := p) (q := q) : ℝ)))
      (columnMassBetaMainShape (p := p) (q := q))
      (1 / (columnMassBetaMainShape (p := p) (q := q) : ℝ)) := by
  have hN2 :
      2 ≤ columnMassBetaMainShape (p := p) (q := q) := by
    simpa [columnMassBetaMainShape] using H.dimension_ge_two
  have hLaw :
      ProbabilityTheory.HasLaw
        (ambientProjectiveOverlapSq (ι := BipIndex p q) e)
        (ProbabilityTheory.betaMeasure (1 : ℝ)
          (((columnMassBetaMainShape (p := p) (q := q)) - 1 : ℕ) : ℝ))
        (columnDirectionPushforward (p := p) (q := q) (σ := σ) μ α₀) := by
    simpa [columnMassBetaMainShape] using H.overlap_hasLaw he
  exact
    columnDirectionProjectiveCapProbabilityLowerBound_inv_of_hasLaw_betaMeasure
      (p := p) (q := q) (σ := σ) (μ := μ) (α₀ := α₀)
      hN2 he hLaw

set_option linter.unusedSectionVars false in
/-- Coarse `exp[-2 N log N]` lower-bound package for the actual column
direction at radius `1/N`.

This is the final cap input expected by the spike lower-bound constructor,
obtained directly from the Haar/projective law of the actual column direction
pushforward. -/
theorem AmbientHaarProjectiveOverlapBetaLaw.toColumnDirectionCapProbabilityLowerBound_inv
    [MeasurableSpace (SampleMatrix p q σ)]
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    (H :
      AmbientHaarProjectiveOverlapBetaLaw
        (ι := BipIndex p q)
        (columnDirectionPushforward (p := p) (q := q) (σ := σ) μ α₀))
    {e : EuclideanSpace ℂ (BipIndex p q)} (he : ‖e‖ = 1) :
    CapProbabilityLowerBound
      (columnDirectionCapProbability
        (p := p) (q := q) (σ := σ) μ α₀ e
        (1 / (columnMassBetaMainShape (p := p) (q := q) : ℝ)))
      (columnMassBetaMainShape (p := p) (q := q) : ℝ) 2 := by
  have hN2 :
      2 ≤ columnMassBetaMainShape (p := p) (q := q) := by
    simpa [columnMassBetaMainShape] using H.dimension_ge_two
  have hN1 :
      1 ≤ columnMassBetaMainShape (p := p) (q := q) :=
    le_trans (by norm_num : 1 ≤ 2) hN2
  exact
    (H.toColumnDirectionProjectiveCapProbabilityLowerBound_inv
      (p := p) (q := q) (σ := σ) (μ := μ) (α₀ := α₀)
      he).toCapProbabilityLowerBound_inv hN1

/-- Normalized deleted-column background.

As for `sampleColumnDirection`, this is total: if the deleted-column complement
is zero, the inverse convention returns zero. -/
noncomputable def sampleColumnComplementNormalized
    (X : SampleMatrix p q σ) (α₀ : σ) :
    SampleMatrix p q σ :=
  ((frobeniusNorm (p := p) (q := q) (σ := σ)
      (sampleColumnComplement (p := p) (q := q) (σ := σ) X α₀))⁻¹ : ℂ) •
    sampleColumnComplement (p := p) (q := q) (σ := σ) X α₀

set_option linter.unusedSectionVars false in
theorem deletedColumnRightDirectionToBackground_hermitianBlockRightDirection_deletedColumnBlockVector
    (X : SampleMatrix p q σ) (α₀ : σ) :
    deletedColumnRightDirectionToBackground
        (p := p) (q := q) (σ := σ) α₀
        (hermitianBlockRightDirection
          (ι := BipIndex p q)
          (κ := PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀))
          (deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀ X)) =
      sampleColumnComplementNormalized (p := p) (q := q) (σ := σ) X α₀ := by
  ext i α
  unfold deletedColumnRightDirectionToBackground hermitianBlockRightDirection
    sampleColumnComplementNormalized
  rw [hermitianBlockRight_deletedColumnBlockVector
    (p := p) (q := q) (σ := σ) X α₀]
  have hnorm :
      ‖sampleMatrixComplexLinearIsometryEquiv
          (p := p) (q := q) (σ := DeletedColumn α₀)
          (sampleDeletedColumns (p := p) (q := q) (σ := σ) X α₀)‖ =
        frobeniusNorm
          (p := p) (q := q) (σ := σ)
          (sampleColumnComplement (p := p) (q := q) (σ := σ) X α₀) := by
    rw [(sampleMatrixComplexLinearIsometryEquiv
      (p := p) (q := q) (σ := DeletedColumn α₀)).norm_map]
    exact
      frobeniusNorm_sampleDeletedColumns_eq_sampleColumnComplement
        (p := p) (q := q) (σ := σ) X α₀
  by_cases hα : α = α₀
  · subst hα
    simp [deletedColumnZeroExtend, sampleColumnComplement]
  · simp [deletedColumnZeroExtend, sampleColumnComplement, sampleDeletedColumns,
      hα, hnorm]

set_option linter.unusedSectionVars false in
/-- Bundled Step 7 identification for the concrete deleted-column block.

After applying `deletedColumnBlockVector α₀`, the Hermitian block triple
matches the existing concrete one-column triple exactly. -/
theorem deletedColumnBlockVector_concreteTriple
    (X : SampleMatrix p q σ) (α₀ : σ) :
    (hermitianBlockMass
        (ι := BipIndex p q)
        (κ := PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀))
        (deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀ X),
      hermitianBlockLeftDirection
        (ι := BipIndex p q)
        (κ := PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀))
        (deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀ X),
      deletedColumnRightDirectionToBackground
        (p := p) (q := q) (σ := σ) α₀
        (hermitianBlockRightDirection
          (ι := BipIndex p q)
          (κ := PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀))
          (deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀ X))) =
      (sampleColumnMass (p := p) (q := q) (σ := σ) X α₀,
        sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀,
        sampleColumnComplementNormalized (p := p) (q := q) (σ := σ) X α₀) := by
  refine Prod.ext ?_ ?_
  · exact hermitianBlockMass_deletedColumnBlockVector
      (p := p) (q := q) (σ := σ) X α₀
  · refine Prod.ext ?_ ?_
    · exact hermitianBlockLeftDirection_deletedColumnBlockVector
        (p := p) (q := q) (σ := σ) X α₀
    · exact
        deletedColumnRightDirectionToBackground_hermitianBlockRightDirection_deletedColumnBlockVector
          (p := p) (q := q) (σ := σ) X α₀

@[fun_prop]
theorem measurable_sampleColumnComplementNormalized (α₀ : σ) :
    Measurable
      (fun X : SampleMatrix p q σ =>
        sampleColumnComplementNormalized (p := p) (q := q) (σ := σ) X α₀) := by
  unfold sampleColumnComplementNormalized frobeniusNorm
  fun_prop

/-- Pushforward law of the normalized deleted-column background `Y`.

This is the marginal law of the third coordinate in the one-column spherical
decomposition

`X ↦ (R, U, Y)`.

Keeping this as a named measure prevents the background typicality estimate
from being hidden inside the product-event factorization. -/
noncomputable def columnBackgroundPushforward
    [MeasurableSpace (SampleMatrix p q σ)]
    (μ : Measure (SampleMatrix p q σ)) (α₀ : σ) :
    Measure (SampleMatrix p q σ) :=
  Measure.map
    (fun X => sampleColumnComplementNormalized (p := p) (q := q) (σ := σ) X α₀)
    μ

/-- Probability, computed from the actual normalized deleted-column background
law, that `Y` lies in a chosen background set. -/
noncomputable def columnBackgroundProbability
    [MeasurableSpace (SampleMatrix p q σ)]
    (μ : Measure (SampleMatrix p q σ)) (α₀ : σ)
    (backgroundSet : Set (SampleMatrix p q σ)) : ℝ :=
  (columnBackgroundPushforward (p := p) (q := q) (σ := σ) μ α₀).real backgroundSet

/-- Generic rectangular event generated by three maps: mass, direction, and
background.

This is deliberately map-level rather than coordinate-level.  The exact
spherical probabilistic theorem will assert that the push-forward of these
three coordinates is a product measure. -/
noncomputable def sphericalColumnRectEvent
    {θ β : Type*}
    (mass : SampleMatrix p q σ → ℝ)
    (direction : SampleMatrix p q σ → θ)
    (background : SampleMatrix p q σ → β)
    (massSet : Set ℝ) (directionSet : Set θ) (backgroundSet : Set β) :
    Set (SampleMatrix p q σ) :=
  {X |
    mass X ∈ massSet ∧
      direction X ∈ directionSet ∧
        background X ∈ backgroundSet}

/-- The concrete one-column favourable event generated by the spherical column
coordinates:

* column mass in the Beta interval;
* column direction in a chosen cap/event;
* normalized deleted-column background in a chosen typical set. -/
noncomputable def sphericalOneColumnFavorableEvent
    (α₀ : σ) (q₀ δ : ℝ)
    (directionSet : Set (EuclideanSpace ℂ (BipIndex p q)))
    (backgroundSet : Set (SampleMatrix p q σ)) :
    Set (SampleMatrix p q σ) :=
  sphericalColumnRectEvent
    (p := p) (q := q) (σ := σ)
    (fun X => sampleColumnMass (p := p) (q := q) (σ := σ) X α₀)
    (fun X => sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀)
    (fun X => sampleColumnComplementNormalized (p := p) (q := q) (σ := σ) X α₀)
    (betaColumnIntervalSet q₀ δ) directionSet backgroundSet

section SphericalColumnIndependence

variable [MeasurableSpace (SampleMatrix p q σ)]
variable {θ β : Type*} [MeasurableSpace θ] [MeasurableSpace β]

/-- Spherical column decomposition and independence, stated as an exact product
law for the three coordinate maps.

For the intended uniform-sphere law this is the formal statement of

`X ↦ (R, U, Y)`

where `R` is the distinguished-column mass, `U` its direction, and `Y` the
normalized deleted-column background.  The field `map_triple_eq` is the
independence statement; the marginal map equalities are included so the laws
cannot be confused with unrelated measures. -/
structure SphericalColumnDecompositionIndependence
    (μ : Measure (SampleMatrix p q σ))
    (mass : SampleMatrix p q σ → ℝ)
    (direction : SampleMatrix p q σ → θ)
    (background : SampleMatrix p q σ → β)
    (massLaw : Measure ℝ) (directionLaw : Measure θ) (backgroundLaw : Measure β) :
    Prop where
  measurable_mass : Measurable mass
  measurable_direction : Measurable direction
  measurable_background : Measurable background
  sfinite_massLaw : SFinite massLaw
  sfinite_directionLaw : SFinite directionLaw
  sfinite_backgroundLaw : SFinite backgroundLaw
  map_mass_eq : Measure.map mass μ = massLaw
  map_direction_eq : Measure.map direction μ = directionLaw
  map_background_eq : Measure.map background μ = backgroundLaw
  map_triple_eq :
    Measure.map (fun X => (mass X, direction X, background X)) μ =
      massLaw.prod (directionLaw.prod backgroundLaw)

set_option linter.unusedSectionVars false in
/-- The triple coordinate map in a spherical column decomposition is measurable. -/
theorem SphericalColumnDecompositionIndependence.measurable_triple
    {μ : Measure (SampleMatrix p q σ)}
    {mass : SampleMatrix p q σ → ℝ}
    {direction : SampleMatrix p q σ → θ}
    {background : SampleMatrix p q σ → β}
    {massLaw : Measure ℝ} {directionLaw : Measure θ} {backgroundLaw : Measure β}
    (I :
      SphericalColumnDecompositionIndependence
        (p := p) (q := q) (σ := σ)
        μ mass direction background massLaw directionLaw backgroundLaw) :
    Measurable (fun X => (mass X, direction X, background X)) := by
  exact I.measurable_mass.prod (I.measurable_direction.prod I.measurable_background)

/-- Product law gives exact factorization on rectangular events. -/
theorem SphericalColumnDecompositionIndependence.rect_event_probability_eq
    {μ : Measure (SampleMatrix p q σ)}
    {mass : SampleMatrix p q σ → ℝ}
    {direction : SampleMatrix p q σ → θ}
    {background : SampleMatrix p q σ → β}
    {massLaw : Measure ℝ} {directionLaw : Measure θ} {backgroundLaw : Measure β}
    (I :
      SphericalColumnDecompositionIndependence
        (p := p) (q := q) (σ := σ)
        μ mass direction background massLaw directionLaw backgroundLaw)
    {massSet : Set ℝ} {directionSet : Set θ} {backgroundSet : Set β}
    (hmass : MeasurableSet massSet)
    (hdirection : MeasurableSet directionSet)
    (hbackground : MeasurableSet backgroundSet) :
    μ.real
        (sphericalColumnRectEvent
          (p := p) (q := q) (σ := σ)
          mass direction background massSet directionSet backgroundSet) =
      massLaw.real massSet * directionLaw.real directionSet *
        backgroundLaw.real backgroundSet := by
  let T : SampleMatrix p q σ → ℝ × θ × β :=
    fun X => (mass X, direction X, background X)
  let rect : Set (ℝ × θ × β) := massSet ×ˢ (directionSet ×ˢ backgroundSet)
  have hrect : MeasurableSet rect := hmass.prod (hdirection.prod hbackground)
  have hpre :
      T ⁻¹' rect =
        sphericalColumnRectEvent
          (p := p) (q := q) (σ := σ)
          mass direction background massSet directionSet backgroundSet := by
    ext X
    simp [T, rect, sphericalColumnRectEvent]
  calc
    μ.real
        (sphericalColumnRectEvent
          (p := p) (q := q) (σ := σ)
          mass direction background massSet directionSet backgroundSet)
        = μ.real (T ⁻¹' rect) := by rw [hpre]
    _ = (Measure.map T μ).real rect := by
          rw [map_measureReal_apply I.measurable_triple hrect]
    _ = (massLaw.prod (directionLaw.prod backgroundLaw)).real rect := by
          rw [I.map_triple_eq]
    _ = massLaw.real massSet * directionLaw.real directionSet *
          backgroundLaw.real backgroundSet := by
          letI : SFinite directionLaw := I.sfinite_directionLaw
          letI : SFinite backgroundLaw := I.sfinite_backgroundLaw
          rw [measureReal_prod_prod, measureReal_prod_prod]
          ring

/-- Concrete one-column version of `SphericalColumnDecompositionIndependence`. -/
def SphericalOneColumnDecompositionIndependence
    (μ : Measure (SampleMatrix p q σ)) (α₀ : σ)
    (massLaw : Measure ℝ)
    (directionLaw : Measure (EuclideanSpace ℂ (BipIndex p q)))
    (backgroundLaw : Measure (SampleMatrix p q σ)) : Prop :=
  SphericalColumnDecompositionIndependence
    (p := p) (q := q) (σ := σ)
    μ
    (fun X => sampleColumnMass (p := p) (q := q) (σ := σ) X α₀)
    (fun X => sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀)
    (fun X => sampleColumnComplementNormalized (p := p) (q := q) (σ := σ) X α₀)
    massLaw directionLaw backgroundLaw

/-- Canonical one-column spherical decomposition: the mass coordinate is fixed
to the canonical Beta law for

`R = ‖x_{α₀}‖²`,

while the direction and background laws remain explicit. -/
def CanonicalSphericalOneColumnDecompositionIndependence
    (μ : Measure (SampleMatrix p q σ)) (α₀ : σ)
    (directionLaw : Measure (EuclideanSpace ℂ (BipIndex p q)))
    (backgroundLaw : Measure (SampleMatrix p q σ)) : Prop :=
  SphericalOneColumnDecompositionIndependence
    (p := p) (q := q) (σ := σ)
    μ α₀
    (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ))
    directionLaw backgroundLaw

set_option linter.unusedSectionVars false in
/-- A canonical spherical one-column decomposition immediately gives the
canonical Beta law for the mass coordinate `R = ‖x_{α₀}‖²`. -/
theorem CanonicalSphericalOneColumnDecompositionIndependence.columnMassRHasCanonicalBetaLaw
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {directionLaw : Measure (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundLaw : Measure (SampleMatrix p q σ)}
    (I :
      CanonicalSphericalOneColumnDecompositionIndependence
        (p := p) (q := q) (σ := σ)
        μ α₀ directionLaw backgroundLaw) :
    ColumnMassRHasCanonicalBetaLaw (p := p) (q := q) (σ := σ) μ α₀ := by
  change columnMassPushforward (p := p) (q := q) (σ := σ) μ α₀ =
    canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ)
  simpa [CanonicalSphericalOneColumnDecompositionIndependence,
    SphericalOneColumnDecompositionIndependence, columnMassPushforward] using
    I.map_mass_eq

/-- If the canonical Beta measure is also equipped with the integer-Beta
interval lower-bound package, the canonical spherical decomposition supplies
the full `CanonicalColumnMassBetaLaw` used downstream. -/
theorem CanonicalSphericalOneColumnDecompositionIndependence.canonicalColumnMassBetaLaw
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {directionLaw : Measure (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundLaw : Measure (SampleMatrix p q σ)}
    (I :
      CanonicalSphericalOneColumnDecompositionIndependence
        (p := p) (q := q) (σ := σ)
        μ α₀ directionLaw backgroundLaw)
    (hIntervals :
      IntegerBetaColumnMeasure
        (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ))
        (columnMassBetaMainShape (p := p) (q := q))
        (columnMassBetaSampleCount (σ := σ))) :
    CanonicalColumnMassBetaLaw (p := p) (q := q) (σ := σ) μ α₀ :=
  CanonicalColumnMassBetaLaw.of_R_hasCanonicalBetaLaw
    (p := p) (q := q) (σ := σ)
    I.columnMassRHasCanonicalBetaLaw hIntervals

set_option linter.unusedSectionVars false in
/-- Canonical spherical one-column decomposition gives the full column-mass
Beta package with the integer-Beta interval estimates filled automatically. -/
theorem CanonicalSphericalOneColumnDecompositionIndependence.canonicalColumnMassBetaLaw_noInput
    [Nonempty p] [Nonempty q]
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {directionLaw : Measure (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundLaw : Measure (SampleMatrix p q σ)}
    (I :
      CanonicalSphericalOneColumnDecompositionIndependence
        (p := p) (q := q) (σ := σ)
        μ α₀ directionLaw backgroundLaw)
    (hσ : 2 ≤ Fintype.card σ) :
    CanonicalColumnMassBetaLaw (p := p) (q := q) (σ := σ) μ α₀ :=
  I.canonicalColumnMassBetaLaw
    (canonicalIntegerBetaColumnMeasure (p := p) (q := q) (σ := σ) hσ)

set_option linter.unusedSectionVars false in
/-- `HasLaw` form of the one-column mass Beta law obtained from the canonical
spherical decomposition. -/
theorem CanonicalSphericalOneColumnDecompositionIndependence.sampleColumnMass_hasLaw_beta
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {directionLaw : Measure (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundLaw : Measure (SampleMatrix p q σ)}
    (I :
      CanonicalSphericalOneColumnDecompositionIndependence
        (p := p) (q := q) (σ := σ)
        μ α₀ directionLaw backgroundLaw) :
    ProbabilityTheory.HasLaw
      (fun X => sampleColumnMass (p := p) (q := q) (σ := σ) X α₀)
      (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ)) μ :=
  I.columnMassRHasCanonicalBetaLaw.hasLaw I.measurable_mass.aemeasurable

set_option linter.unusedSectionVars false in
/-- Direct interval lower bound for the actual column mass probability, once
the canonical spherical one-column decomposition is available. -/
theorem CanonicalSphericalOneColumnDecompositionIndependence.betaColumnIntervalLowerBound
    [Nonempty p] [Nonempty q]
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {directionLaw : Measure (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundLaw : Measure (SampleMatrix p q σ)}
    (I :
      CanonicalSphericalOneColumnDecompositionIndependence
        (p := p) (q := q) (σ := σ)
        μ α₀ directionLaw backgroundLaw)
    (hσ : 2 ≤ Fintype.card σ)
    {q₀ δ : ℝ} (hq : 0 < q₀) (hδ : 0 < δ)
    (hupper : betaColumnIntervalUpper q₀ δ < 1) :
    BetaColumnIntervalLowerBound
      (columnMassIntervalProbability (p := p) (q := q) (σ := σ) μ α₀ q₀ δ)
      (columnMassBetaMainShape (p := p) (q := q))
      (columnMassBetaSampleCount (σ := σ)) q₀ δ :=
  (I.canonicalColumnMassBetaLaw_noInput hσ).betaColumnIntervalLowerBound
    hq hδ hupper

set_option linter.unusedSectionVars false in
/-- A one-column spherical decomposition identifies the pushforward law of the
column direction `u` with its stated direction marginal. -/
theorem SphericalOneColumnDecompositionIndependence.columnDirectionPushforward_eq
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {massLaw : Measure ℝ}
    {directionLaw : Measure (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundLaw : Measure (SampleMatrix p q σ)}
    (I :
      SphericalOneColumnDecompositionIndependence
        (p := p) (q := q) (σ := σ)
        μ α₀ massLaw directionLaw backgroundLaw) :
    columnDirectionPushforward (p := p) (q := q) (σ := σ) μ α₀ =
      directionLaw := by
  simpa [SphericalOneColumnDecompositionIndependence, columnDirectionPushforward] using
    I.map_direction_eq

/-- Therefore the cap probability computed from the actual column direction
equals the cap probability computed from the direction marginal. -/
theorem SphericalOneColumnDecompositionIndependence.columnDirectionCapProbability_eq
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {massLaw : Measure ℝ}
    {directionLaw : Measure (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundLaw : Measure (SampleMatrix p q σ)}
    (I :
      SphericalOneColumnDecompositionIndependence
        (p := p) (q := q) (σ := σ)
        μ α₀ massLaw directionLaw backgroundLaw)
    (e : EuclideanSpace ℂ (BipIndex p q)) (r : ℝ) :
    columnDirectionCapProbability (p := p) (q := q) (σ := σ) μ α₀ e r =
      ambientProjectiveCapProbability (ι := BipIndex p q) directionLaw e r := by
  unfold columnDirectionCapProbability
  rw [I.columnDirectionPushforward_eq]

/-- The one-column decomposition transfers the Beta overlap law of the stated
direction marginal to the actual normalized column direction. -/
theorem SphericalOneColumnDecompositionIndependence.columnDirectionAmbientHaarProjectiveOverlapBetaLaw
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {massLaw : Measure ℝ}
    {directionLaw : Measure (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundLaw : Measure (SampleMatrix p q σ)}
    (I :
      SphericalOneColumnDecompositionIndependence
        (p := p) (q := q) (σ := σ)
        μ α₀ massLaw directionLaw backgroundLaw)
    (hBeta :
      AmbientHaarProjectiveOverlapBetaLaw
        (ι := BipIndex p q) directionLaw) :
    AmbientHaarProjectiveOverlapBetaLaw
      (ι := BipIndex p q)
      (columnDirectionPushforward (p := p) (q := q) (σ := σ) μ α₀) where
  dimension_ge_two := hBeta.dimension_ge_two
  overlap_hasLaw := by
    intro e he
    rw [I.columnDirectionPushforward_eq]
    exact hBeta.overlap_hasLaw he

/-- If the direction marginal has the exact ambient cap law, then the actual
column direction `u` has the same cap law. -/
theorem SphericalOneColumnDecompositionIndependence.columnDirectionHasAmbientCapLaw
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {massLaw : Measure ℝ}
    {directionLaw : Measure (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundLaw : Measure (SampleMatrix p q σ)}
    (I :
      SphericalOneColumnDecompositionIndependence
        (p := p) (q := q) (σ := σ)
        μ α₀ massLaw directionLaw backgroundLaw)
    {e : EuclideanSpace ℂ (BipIndex p q)} {N : ℕ} {r : ℝ}
    (hCap :
      AmbientProjectiveCapExactVolume (ι := BipIndex p q) directionLaw e N r) :
    ColumnDirectionHasAmbientCapLaw (p := p) (q := q) (σ := σ) μ α₀ e N r := by
  change AmbientProjectiveCapExactVolume
    (ι := BipIndex p q)
    (columnDirectionPushforward (p := p) (q := q) (σ := σ) μ α₀) e N r
  rw [I.columnDirectionPushforward_eq]
  exact hCap

/-- Unit-vector version: if the direction marginal has the exact unit-centered
ambient cap law, then the actual column direction `u` has the same unit cap
law. -/
theorem SphericalOneColumnDecompositionIndependence.columnDirectionHasUnitAmbientCapLaw
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {massLaw : Measure ℝ}
    {directionLaw : Measure (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundLaw : Measure (SampleMatrix p q σ)}
    (I :
      SphericalOneColumnDecompositionIndependence
        (p := p) (q := q) (σ := σ)
        μ α₀ massLaw directionLaw backgroundLaw)
    {e : EuclideanSpace ℂ (BipIndex p q)} {N : ℕ} {r : ℝ}
    (hCap :
      UnitAmbientProjectiveCapExactVolume (ι := BipIndex p q) directionLaw e N r) :
    ColumnDirectionHasUnitAmbientCapLaw (p := p) (q := q) (σ := σ) μ α₀ e N r := by
  change UnitAmbientProjectiveCapExactVolume
    (ι := BipIndex p q)
    (columnDirectionPushforward (p := p) (q := q) (σ := σ) μ α₀) e N r
  rw [I.columnDirectionPushforward_eq]
  exact hCap

/-- Canonical version: if the direction marginal has the exact cap law in
dimension `card (BipIndex p q)`, then `u` has the canonical cap law. -/
theorem CanonicalSphericalOneColumnDecompositionIndependence.columnDirectionHasCanonicalCapLaw
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {directionLaw : Measure (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundLaw : Measure (SampleMatrix p q σ)}
    (I :
      CanonicalSphericalOneColumnDecompositionIndependence
        (p := p) (q := q) (σ := σ)
        μ α₀ directionLaw backgroundLaw)
    {e : EuclideanSpace ℂ (BipIndex p q)} {r : ℝ}
    (hCap :
      AmbientProjectiveCapExactVolume
        (ι := BipIndex p q) directionLaw e
        (columnMassBetaMainShape (p := p) (q := q)) r) :
    ColumnDirectionHasCanonicalCapLaw
      (p := p) (q := q) (σ := σ) μ α₀ e r := by
  exact
    SphericalOneColumnDecompositionIndependence.columnDirectionHasAmbientCapLaw
      (p := p) (q := q) (σ := σ) (I := I) hCap

/-- Unit-vector canonical version: if the direction marginal has the exact
unit-centered cap law in dimension `card (BipIndex p q)`, then `u` has the
canonical unit cap law. -/
theorem CanonicalSphericalOneColumnDecompositionIndependence.columnDirectionHasUnitCanonicalCapLaw
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {directionLaw : Measure (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundLaw : Measure (SampleMatrix p q σ)}
    (I :
      CanonicalSphericalOneColumnDecompositionIndependence
        (p := p) (q := q) (σ := σ)
        μ α₀ directionLaw backgroundLaw)
    {e : EuclideanSpace ℂ (BipIndex p q)} {r : ℝ}
    (hCap :
      UnitAmbientProjectiveCapExactVolume
        (ι := BipIndex p q) directionLaw e
        (columnMassBetaMainShape (p := p) (q := q)) r) :
    ColumnDirectionHasUnitCanonicalCapLaw
      (p := p) (q := q) (σ := σ) μ α₀ e r := by
  exact
    SphericalOneColumnDecompositionIndependence.columnDirectionHasUnitAmbientCapLaw
      (p := p) (q := q) (σ := σ) (I := I) hCap

/-- Paper-facing cap output for `u`: at radius `1/N`, the exact cap law of the
direction marginal gives the coarse lower-bound interface for the actual column
direction. -/
theorem CanonicalSphericalOneColumnDecompositionIndependence.columnDirectionCapLowerBound_inv
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {directionLaw : Measure (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundLaw : Measure (SampleMatrix p q σ)}
    (I :
      CanonicalSphericalOneColumnDecompositionIndependence
        (p := p) (q := q) (σ := σ)
        μ α₀ directionLaw backgroundLaw)
    {e : EuclideanSpace ℂ (BipIndex p q)}
    (hCap :
      AmbientProjectiveCapExactVolume
        (ι := BipIndex p q) directionLaw e
        (columnMassBetaMainShape (p := p) (q := q))
        (1 / (columnMassBetaMainShape (p := p) (q := q) : ℝ)))
    (hN : 1 ≤ columnMassBetaMainShape (p := p) (q := q)) :
    CapProbabilityLowerBound
      (columnDirectionCapProbability
        (p := p) (q := q) (σ := σ) μ α₀ e
        (1 / (columnMassBetaMainShape (p := p) (q := q) : ℝ)))
      (columnMassBetaMainShape (p := p) (q := q) : ℝ) 2 := by
  exact
    (I.columnDirectionHasCanonicalCapLaw hCap).toCapProbabilityLowerBound_inv hN

/-- Unit-vector paper-facing cap output for `u`: at radius `1/N`, the exact
unit cap law of the direction marginal gives the coarse lower-bound interface
for the actual column direction. -/
theorem CanonicalSphericalOneColumnDecompositionIndependence.columnDirectionUnitCapLowerBound_inv
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {directionLaw : Measure (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundLaw : Measure (SampleMatrix p q σ)}
    (I :
      CanonicalSphericalOneColumnDecompositionIndependence
        (p := p) (q := q) (σ := σ)
        μ α₀ directionLaw backgroundLaw)
    {e : EuclideanSpace ℂ (BipIndex p q)}
    (hCap :
      UnitAmbientProjectiveCapExactVolume
        (ι := BipIndex p q) directionLaw e
        (columnMassBetaMainShape (p := p) (q := q))
        (1 / (columnMassBetaMainShape (p := p) (q := q) : ℝ)))
    (hN : 1 ≤ columnMassBetaMainShape (p := p) (q := q)) :
    CapProbabilityLowerBound
      (columnDirectionCapProbability
        (p := p) (q := q) (σ := σ) μ α₀ e
        (1 / (columnMassBetaMainShape (p := p) (q := q) : ℝ)))
      (columnMassBetaMainShape (p := p) (q := q) : ℝ) 2 := by
  exact
    (I.columnDirectionHasUnitCanonicalCapLaw hCap).toCapProbabilityLowerBound_inv hN

theorem CanonicalSphericalOneColumnDecompositionIndependence.columnDirectionAmbientHaarProjectiveOverlapBetaLaw
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {directionLaw : Measure (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundLaw : Measure (SampleMatrix p q σ)}
    (I :
      CanonicalSphericalOneColumnDecompositionIndependence
        (p := p) (q := q) (σ := σ)
        μ α₀ directionLaw backgroundLaw)
    (hBeta :
      AmbientHaarProjectiveOverlapBetaLaw
        (ι := BipIndex p q) directionLaw) :
    AmbientHaarProjectiveOverlapBetaLaw
      (ι := BipIndex p q)
      (columnDirectionPushforward (p := p) (q := q) (σ := σ) μ α₀) :=
  SphericalOneColumnDecompositionIndependence.columnDirectionAmbientHaarProjectiveOverlapBetaLaw
    (p := p) (q := q) (σ := σ) (I := I) hBeta

/-- Preferred paper-facing cap output: the direction marginal is supplied by
its squared-overlap Beta law, and the cap lower-bound interface is derived only
after that law has been installed. -/
theorem CanonicalSphericalOneColumnDecompositionIndependence.columnDirectionCapLowerBound_inv_of_overlapBetaLaw
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {directionLaw : Measure (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundLaw : Measure (SampleMatrix p q σ)}
    (I :
      CanonicalSphericalOneColumnDecompositionIndependence
        (p := p) (q := q) (σ := σ)
        μ α₀ directionLaw backgroundLaw)
    (hBeta :
      AmbientHaarProjectiveOverlapBetaLaw
        (ι := BipIndex p q) directionLaw)
    {e : EuclideanSpace ℂ (BipIndex p q)} (he : ‖e‖ = 1) :
    CapProbabilityLowerBound
      (columnDirectionCapProbability
        (p := p) (q := q) (σ := σ) μ α₀ e
        (1 / (columnMassBetaMainShape (p := p) (q := q) : ℝ)))
      (columnMassBetaMainShape (p := p) (q := q) : ℝ) 2 := by
  have hColumnBeta :=
    I.columnDirectionAmbientHaarProjectiveOverlapBetaLaw hBeta
  exact
    hColumnBeta.toColumnDirectionCapProbabilityLowerBound_inv
      (p := p) (q := q) (σ := σ) (μ := μ) (α₀ := α₀) he

set_option linter.unusedSectionVars false in
/-- A one-column spherical decomposition identifies the pushforward law of the
normalized deleted-column background `Y` with its stated background marginal. -/
theorem SphericalOneColumnDecompositionIndependence.columnBackgroundPushforward_eq
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {massLaw : Measure ℝ}
    {directionLaw : Measure (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundLaw : Measure (SampleMatrix p q σ)}
    (I :
      SphericalOneColumnDecompositionIndependence
        (p := p) (q := q) (σ := σ)
        μ α₀ massLaw directionLaw backgroundLaw) :
    columnBackgroundPushforward (p := p) (q := q) (σ := σ) μ α₀ =
      backgroundLaw := by
  simpa [SphericalOneColumnDecompositionIndependence, columnBackgroundPushforward] using
    I.map_background_eq

/-- Therefore the probability that the actual deleted-column background lies in
any background set equals the probability of that set under the background
marginal. -/
theorem SphericalOneColumnDecompositionIndependence.columnBackgroundProbability_eq
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {massLaw : Measure ℝ}
    {directionLaw : Measure (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundLaw : Measure (SampleMatrix p q σ)}
    (I :
      SphericalOneColumnDecompositionIndependence
        (p := p) (q := q) (σ := σ)
        μ α₀ massLaw directionLaw backgroundLaw)
    (backgroundSet : Set (SampleMatrix p q σ)) :
    columnBackgroundProbability (p := p) (q := q) (σ := σ) μ α₀ backgroundSet =
      backgroundLaw.real backgroundSet := by
  unfold columnBackgroundProbability
  rw [I.columnBackgroundPushforward_eq]

/-- Half-measure background typicality transfers from the background marginal to
the actual normalized deleted-column background `Y`. -/
theorem SphericalOneColumnDecompositionIndependence.columnBackgroundProbability_ge_half
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {massLaw : Measure ℝ}
    {directionLaw : Measure (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundLaw : Measure (SampleMatrix p q σ)}
    (I :
      SphericalOneColumnDecompositionIndependence
        (p := p) (q := q) (σ := σ)
        μ α₀ massLaw directionLaw backgroundLaw)
    {backgroundSet : Set (SampleMatrix p q σ)}
    (hHalf : (1 / 2 : ℝ) ≤ backgroundLaw.real backgroundSet) :
    (1 / 2 : ℝ) ≤
      columnBackgroundProbability (p := p) (q := q) (σ := σ) μ α₀ backgroundSet := by
  simpa [I.columnBackgroundProbability_eq backgroundSet] using hHalf

/-- The concrete one-column independence law factors the favourable-event
probability into mass, direction and background probabilities. -/
theorem SphericalOneColumnDecompositionIndependence.favorable_event_probability_eq
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {massLaw : Measure ℝ}
    {directionLaw : Measure (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundLaw : Measure (SampleMatrix p q σ)}
    (I :
      SphericalOneColumnDecompositionIndependence
        (p := p) (q := q) (σ := σ)
        μ α₀ massLaw directionLaw backgroundLaw)
    {q₀ δ : ℝ}
    {directionSet : Set (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundSet : Set (SampleMatrix p q σ)}
    (hdirection : MeasurableSet directionSet)
    (hbackground : MeasurableSet backgroundSet) :
    μ.real
        (sphericalOneColumnFavorableEvent
          (p := p) (q := q) (σ := σ)
          α₀ q₀ δ directionSet backgroundSet) =
      massLaw.real (betaColumnIntervalSet q₀ δ) *
        directionLaw.real directionSet *
          backgroundLaw.real backgroundSet := by
  simpa [sphericalOneColumnFavorableEvent, SphericalOneColumnDecompositionIndependence] using
    I.rect_event_probability_eq
      (p := p) (q := q) (σ := σ)
      (massSet := betaColumnIntervalSet q₀ δ)
      (directionSet := directionSet)
      (backgroundSet := backgroundSet)
      measurableSet_Icc hdirection hbackground

/-- Canonical version of the favourable-event factorization: the mass factor is
the canonical Beta probability of the interval for `R`. -/
theorem CanonicalSphericalOneColumnDecompositionIndependence.favorable_event_probability_eq
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {directionLaw : Measure (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundLaw : Measure (SampleMatrix p q σ)}
    (I :
      CanonicalSphericalOneColumnDecompositionIndependence
        (p := p) (q := q) (σ := σ)
        μ α₀ directionLaw backgroundLaw)
    {q₀ δ : ℝ}
    {directionSet : Set (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundSet : Set (SampleMatrix p q σ)}
    (hdirection : MeasurableSet directionSet)
    (hbackground : MeasurableSet backgroundSet) :
    μ.real
        (sphericalOneColumnFavorableEvent
          (p := p) (q := q) (σ := σ)
          α₀ q₀ δ directionSet backgroundSet) =
      (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ)).real
          (betaColumnIntervalSet q₀ δ) *
        directionLaw.real directionSet *
          backgroundLaw.real backgroundSet := by
  simpa [CanonicalSphericalOneColumnDecompositionIndependence] using
    SphericalOneColumnDecompositionIndependence.favorable_event_probability_eq
      (p := p) (q := q) (σ := σ)
      (I := I) hdirection hbackground

/-- Eventual product identity supplied by a sequence of concrete one-column
decomposition/independence laws.  This is the exact `hProduct` ingredient used
by the one-column lower-bound pipeline. -/
theorem eventual_columnProb_eq_product_of_sphericalOneColumnDecomposition
    {μ : ℕ → Measure (SampleMatrix p q σ)} {α₀ : σ}
    {massLaw : ℕ → Measure ℝ}
    {directionLaw : ℕ → Measure (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundLaw : ℕ → Measure (SampleMatrix p q σ)}
    {q₀ δ : ℕ → ℝ}
    {directionSet : ℕ → Set (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundSet : ℕ → Set (SampleMatrix p q σ)}
    {betaProb capProb backgroundProb columnProb : ℕ → ℝ}
    (hIndep :
      ∀ᶠ d in atTop,
        SphericalOneColumnDecompositionIndependence
          (p := p) (q := q) (σ := σ)
          (μ d) α₀ (massLaw d) (directionLaw d) (backgroundLaw d))
    (hDirectionMeas :
      ∀ᶠ d in atTop, MeasurableSet (directionSet d))
    (hBackgroundMeas :
      ∀ᶠ d in atTop, MeasurableSet (backgroundSet d))
    (hBetaProb :
      ∀ᶠ d in atTop,
        betaProb d = (massLaw d).real (betaColumnIntervalSet (q₀ d) (δ d)))
    (hCapProb :
      ∀ᶠ d in atTop,
        capProb d = (directionLaw d).real (directionSet d))
    (hBackgroundProb :
      ∀ᶠ d in atTop,
        backgroundProb d = (backgroundLaw d).real (backgroundSet d))
    (hColumnProb :
      ∀ᶠ d in atTop,
        columnProb d =
          (μ d).real
            (sphericalOneColumnFavorableEvent
              (p := p) (q := q) (σ := σ)
              α₀ (q₀ d) (δ d) (directionSet d) (backgroundSet d))) :
    ∀ᶠ d in atTop,
      columnProb d = betaProb d * capProb d * backgroundProb d := by
  filter_upwards
    [hIndep, hDirectionMeas, hBackgroundMeas,
      hBetaProb, hCapProb, hBackgroundProb, hColumnProb]
    with d hI hDmeas hBmeas hBeta hCap hBg hCol
  rw [hCol, hBeta, hCap, hBg]
  exact hI.favorable_event_probability_eq hDmeas hBmeas

end SphericalColumnIndependence

/-- Canonical one-column spherical decomposition with the **actual deleted-column
background law** fixed.

The background marginal is the spherical law on the reduced column type
`DeletedColumn α₀`, pushed forward by zero-extension to the original sample
space.  This is the interface that should be used for the one-column lower
bound; the full `sphericalModelMeasure p q σ` is not the deleted-column
background law. -/
def CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence
    (μ : Measure (SampleMatrix p q σ)) (α₀ : σ)
    (directionLaw : Measure (EuclideanSpace ℂ (BipIndex p q))) : Prop :=
  CanonicalSphericalOneColumnDecompositionIndependence
    (p := p) (q := q) (σ := σ)
    μ α₀ directionLaw
    (deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀)

set_option linter.unusedSectionVars false in
/-- If there are at least two sample columns, deleting one distinguished column
leaves a nonempty deleted-column type. -/
theorem deletedColumn_nonempty_of_two_le_card
    (α₀ : σ) (hσ : 2 ≤ Fintype.card σ) :
    Nonempty (DeletedColumn α₀) := by
  have hlt : 1 < Fintype.card σ := by omega
  rcases Fintype.exists_ne_of_one_lt_card hlt α₀ with ⟨α, hα⟩
  exact ⟨⟨α, hα⟩⟩

set_option linter.unusedSectionVars false in
/-- Canonical deleted-background one-column decomposition from the exact joint
product law.

This is the sharp interface for the spherical column decomposition: the only
probabilistic content is the single map equality for

`X ↦ (R(X), U(X), Y_deleted(X))`.

All three marginal laws are then recovered by projection, so the decomposition
cannot accidentally use a full-sphere background law in place of the deleted
background law. -/
theorem CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence.of_map_triple_eq
    [Nonempty p] [Nonempty q]
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {directionLaw : Measure (EuclideanSpace ℂ (BipIndex p q))}
    (hσ : 2 ≤ Fintype.card σ)
    (hDirectionProb : IsProbabilityMeasure directionLaw)
    (hTriple :
      Measure.map
          (fun X =>
            (sampleColumnMass (p := p) (q := q) (σ := σ) X α₀,
              sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀,
              sampleColumnComplementNormalized
                (p := p) (q := q) (σ := σ) X α₀))
          μ =
        (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ)).prod
          (directionLaw.prod
            (deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀))) :
    CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence
      (p := p) (q := q) (σ := σ) μ α₀ directionLaw := by
  classical
  let mass : SampleMatrix p q σ → ℝ :=
    fun X => sampleColumnMass (p := p) (q := q) (σ := σ) X α₀
  let direction : SampleMatrix p q σ → EuclideanSpace ℂ (BipIndex p q) :=
    fun X => sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀
  let background : SampleMatrix p q σ → SampleMatrix p q σ :=
    fun X => sampleColumnComplementNormalized
      (p := p) (q := q) (σ := σ) X α₀
  let massLaw : Measure ℝ :=
    canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ)
  let backgroundLaw : Measure (SampleMatrix p q σ) :=
    deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀
  haveI : IsProbabilityMeasure directionLaw := hDirectionProb
  haveI : Nonempty (DeletedColumn α₀) :=
    deletedColumn_nonempty_of_two_le_card
      (α₀ := α₀) hσ
  haveI : IsProbabilityMeasure massLaw := by
    simpa [massLaw] using
      canonicalColumnMassBetaMeasure_isProbabilityMeasure
        (p := p) (q := q) (σ := σ) hσ
  haveI : IsProbabilityMeasure backgroundLaw := by
    simpa [backgroundLaw] using
      deletedColumnBackgroundLaw_isProbabilityMeasure
        (p := p) (q := q) (σ := σ) (α₀ := α₀)
  have hmeas_mass :
      Measurable
        (fun X => sampleColumnMass (p := p) (q := q) (σ := σ) X α₀) :=
    measurable_sampleColumnMass (p := p) (q := q) (σ := σ) α₀
  have hmeas_direction :
      Measurable
        (fun X => sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀) :=
    measurable_sampleColumnDirection (p := p) (q := q) (σ := σ) α₀
  have hmeas_background :
      Measurable
        (fun X => sampleColumnComplementNormalized
          (p := p) (q := q) (σ := σ) X α₀) :=
    measurable_sampleColumnComplementNormalized (p := p) (q := q) (σ := σ) α₀
  have hmeas_triple :
      Measurable (fun X => (mass X, direction X, background X)) :=
    hmeas_mass.prod (hmeas_direction.prod hmeas_background)
  have hTriple' :
      Measure.map (fun X => (mass X, direction X, background X)) μ =
        massLaw.prod (directionLaw.prod backgroundLaw) := by
    simpa [mass, direction, background, massLaw, backgroundLaw] using hTriple
  refine
    (show SphericalOneColumnDecompositionIndependence
      (p := p) (q := q) (σ := σ)
      μ α₀ massLaw directionLaw backgroundLaw from ?_)
  refine
    { measurable_mass := hmeas_mass
      measurable_direction := hmeas_direction
      measurable_background := hmeas_background
      sfinite_massLaw := inferInstance
      sfinite_directionLaw := inferInstance
      sfinite_backgroundLaw := inferInstance
      map_mass_eq := ?_
      map_direction_eq := ?_
      map_background_eq := ?_
      map_triple_eq := hTriple' }
  · calc
      Measure.map mass μ =
          Measure.map (fun z : ℝ × EuclideanSpace ℂ (BipIndex p q) ×
              SampleMatrix p q σ => z.1)
            (Measure.map (fun X => (mass X, direction X, background X)) μ) := by
            rw [Measure.map_map
              (μ := μ)
              (f := fun X => (mass X, direction X, background X))
              (g := fun z : ℝ × EuclideanSpace ℂ (BipIndex p q) ×
                SampleMatrix p q σ => z.1)
              measurable_fst hmeas_triple]
            rfl
      _ = Measure.map (fun z : ℝ × EuclideanSpace ℂ (BipIndex p q) ×
              SampleMatrix p q σ => z.1)
            (massLaw.prod (directionLaw.prod backgroundLaw)) := by
            rw [hTriple']
      _ = massLaw := by
            simp [massLaw]
  · calc
      Measure.map direction μ =
          Measure.map (fun z : ℝ × EuclideanSpace ℂ (BipIndex p q) ×
              SampleMatrix p q σ => z.2.1)
            (Measure.map (fun X => (mass X, direction X, background X)) μ) := by
            rw [Measure.map_map
              (μ := μ)
              (f := fun X => (mass X, direction X, background X))
              (g := fun z : ℝ × EuclideanSpace ℂ (BipIndex p q) ×
                SampleMatrix p q σ => z.2.1)
              (measurable_fst.comp measurable_snd) hmeas_triple]
            rfl
      _ = Measure.map (fun z : ℝ × EuclideanSpace ℂ (BipIndex p q) ×
              SampleMatrix p q σ => z.2.1)
            (massLaw.prod (directionLaw.prod backgroundLaw)) := by
            rw [hTriple']
      _ = directionLaw := by
            calc
              Measure.map (fun z : ℝ × EuclideanSpace ℂ (BipIndex p q) ×
                  SampleMatrix p q σ => z.2.1)
                  (massLaw.prod (directionLaw.prod backgroundLaw)) =
                Measure.map (fun z : EuclideanSpace ℂ (BipIndex p q) ×
                    SampleMatrix p q σ => z.1)
                  (Measure.map (fun z : ℝ × EuclideanSpace ℂ (BipIndex p q) ×
                    SampleMatrix p q σ => z.2)
                    (massLaw.prod (directionLaw.prod backgroundLaw))) := by
                  rw [Measure.map_map
                    (μ := massLaw.prod (directionLaw.prod backgroundLaw))
                    (f := fun z : ℝ × EuclideanSpace ℂ (BipIndex p q) ×
                      SampleMatrix p q σ => z.2)
                    (g := fun z : EuclideanSpace ℂ (BipIndex p q) ×
                      SampleMatrix p q σ => z.1)
                    measurable_fst measurable_snd]
                  rfl
              _ = Measure.map (fun z : EuclideanSpace ℂ (BipIndex p q) ×
                    SampleMatrix p q σ => z.1)
                  (directionLaw.prod backgroundLaw) := by
                  simp
              _ = directionLaw := by
                  simp
  · calc
      Measure.map background μ =
          Measure.map (fun z : ℝ × EuclideanSpace ℂ (BipIndex p q) ×
              SampleMatrix p q σ => z.2.2)
            (Measure.map (fun X => (mass X, direction X, background X)) μ) := by
            rw [Measure.map_map
              (μ := μ)
              (f := fun X => (mass X, direction X, background X))
              (g := fun z : ℝ × EuclideanSpace ℂ (BipIndex p q) ×
                SampleMatrix p q σ => z.2.2)
              (measurable_snd.comp measurable_snd) hmeas_triple]
            rfl
      _ = Measure.map (fun z : ℝ × EuclideanSpace ℂ (BipIndex p q) ×
              SampleMatrix p q σ => z.2.2)
            (massLaw.prod (directionLaw.prod backgroundLaw)) := by
            rw [hTriple']
      _ = backgroundLaw := by
            calc
              Measure.map (fun z : ℝ × EuclideanSpace ℂ (BipIndex p q) ×
                  SampleMatrix p q σ => z.2.2)
                  (massLaw.prod (directionLaw.prod backgroundLaw)) =
                Measure.map (fun z : EuclideanSpace ℂ (BipIndex p q) ×
                    SampleMatrix p q σ => z.2)
                  (Measure.map (fun z : ℝ × EuclideanSpace ℂ (BipIndex p q) ×
                    SampleMatrix p q σ => z.2)
                    (massLaw.prod (directionLaw.prod backgroundLaw))) := by
                  rw [Measure.map_map
                    (μ := massLaw.prod (directionLaw.prod backgroundLaw))
                    (f := fun z : ℝ × EuclideanSpace ℂ (BipIndex p q) ×
                      SampleMatrix p q σ => z.2)
                    (g := fun z : EuclideanSpace ℂ (BipIndex p q) ×
                      SampleMatrix p q σ => z.2)
                    measurable_snd measurable_snd]
                  rfl
              _ = Measure.map (fun z : EuclideanSpace ℂ (BipIndex p q) ×
                    SampleMatrix p q σ => z.2)
                  (directionLaw.prod backgroundLaw) := by
                  simp
              _ = backgroundLaw := by
                  simp

theorem measure_map_prod_nested_right
    {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ]
    (μ : Measure α) (ν : Measure β) (κ : Measure γ)
    [SFinite μ] [SFinite ν] [SFinite κ]
    {f : γ → δ} (hf : Measurable f) :
    Measure.map (fun z : α × β × γ => (z.1, z.2.1, f z.2.2))
        (μ.prod (ν.prod κ)) =
      μ.prod (ν.prod (Measure.map f κ)) := by
  calc
    Measure.map (fun z : α × β × γ => (z.1, z.2.1, f z.2.2))
        (μ.prod (ν.prod κ)) =
      Measure.map (Prod.map id (Prod.map id f)) (μ.prod (ν.prod κ)) := by
        rfl
    _ = (Measure.map id μ).prod
        (Measure.map (Prod.map id f) (ν.prod κ)) := by
        exact
          (MeasureTheory.Measure.map_prod_map μ (ν.prod κ)
            measurable_id (measurable_id.prodMap hf)).symm
    _ = μ.prod ((Measure.map id ν).prod (Measure.map f κ)) := by
        rw [← MeasureTheory.Measure.map_prod_map ν κ measurable_id hf]
        simp
    _ = μ.prod (ν.prod (Measure.map f κ)) := by
        simp

set_option linter.unusedSectionVars false in
/-- Transport the abstract `E ⊕ F` spherical block decomposition to the
concrete one-column/deleted-column interface.

The only remaining concrete work is the three pointwise identifications saying
that the block coordinates built from `deletedColumnBlockVector α₀` are exactly
the existing column mass, column direction, and zero-extended deleted
background maps.  Once these mechanical identifications are supplied, the
deleted-column independence package follows from the abstract block product
law. -/
theorem CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence.of_hermitianBlock_transport
    [Nonempty p] [Nonempty q]
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {directionLaw : Measure (EuclideanSpace ℂ (BipIndex p q))}
    {deletedDirectionLaw :
      Measure (EuclideanSpace ℂ
        (PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀)))}
    (hσ : 2 ≤ Fintype.card σ)
    (hDirectionProb : IsProbabilityMeasure directionLaw)
    (hBlock :
      HermitianBlockSphericalDecompositionIndependence
        (ι := BipIndex p q)
        (κ := PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀))
        (Measure.map
          (deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀) μ)
        (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ))
        directionLaw deletedDirectionLaw)
    (hBackgroundLaw :
      Measure.map
          (deletedColumnRightDirectionToBackground
            (p := p) (q := q) (σ := σ) α₀)
          deletedDirectionLaw =
        deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀)
    (hMass :
      ∀ X : SampleMatrix p q σ,
        hermitianBlockMass
          (ι := BipIndex p q)
          (κ := PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀))
          (deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀ X) =
        sampleColumnMass (p := p) (q := q) (σ := σ) X α₀)
    (hDirection :
      ∀ X : SampleMatrix p q σ,
        hermitianBlockLeftDirection
          (ι := BipIndex p q)
          (κ := PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀))
          (deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀ X) =
        sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀)
    (hBackground :
      ∀ X : SampleMatrix p q σ,
        deletedColumnRightDirectionToBackground
          (p := p) (q := q) (σ := σ) α₀
          (hermitianBlockRightDirection
            (ι := BipIndex p q)
            (κ := PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀))
            (deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀ X)) =
        sampleColumnComplementNormalized (p := p) (q := q) (σ := σ) X α₀) :
    CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence
      (p := p) (q := q) (σ := σ) μ α₀ directionLaw := by
  classical
  let block : SampleMatrix p q σ →
      EuclideanSpace ℂ
        (Sum (BipIndex p q)
          (PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀))) :=
    fun X => deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀ X
  let T :
      EuclideanSpace ℂ
        (Sum (BipIndex p q)
          (PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀))) →
        ℝ × EuclideanSpace ℂ (BipIndex p q) ×
          EuclideanSpace ℂ
            (PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀)) :=
    fun x =>
      (hermitianBlockMass
        (ι := BipIndex p q)
        (κ := PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀)) x,
        hermitianBlockLeftDirection
          (ι := BipIndex p q)
          (κ := PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀)) x,
        hermitianBlockRightDirection
          (ι := BipIndex p q)
          (κ := PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀)) x)
  let toBackground :
      EuclideanSpace ℂ
        (PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀)) →
        SampleMatrix p q σ :=
    deletedColumnRightDirectionToBackground (p := p) (q := q) (σ := σ) α₀
  let Φ :
      ℝ × EuclideanSpace ℂ (BipIndex p q) ×
        EuclideanSpace ℂ
          (PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀)) →
        ℝ × EuclideanSpace ℂ (BipIndex p q) × SampleMatrix p q σ :=
    fun z => (z.1, z.2.1, toBackground z.2.2)
  let massLaw : Measure ℝ :=
    canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ)
  let backgroundLaw : Measure (SampleMatrix p q σ) :=
    deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀
  have hmeas_block : Measurable block := by
    simpa [block] using
      measurable_deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀
  have hmeas_T : Measurable T := by
    simpa [T] using hBlock.measurable_triple
  have hmeas_toBackground : Measurable toBackground := by
    simpa [toBackground] using
      measurable_deletedColumnRightDirectionToBackground
        (p := p) (q := q) (σ := σ) α₀
  have hmeas_Φ : Measurable Φ := by
    have hfst :
        Measurable
          (fun z : ℝ × EuclideanSpace ℂ (BipIndex p q) ×
              EuclideanSpace ℂ
                (PptFactorization.GaussianModel.SampleCoord p q
                  (DeletedColumn α₀)) => z.1) :=
      measurable_fst
    have hmid :
        Measurable
          (fun z : ℝ × EuclideanSpace ℂ (BipIndex p q) ×
              EuclideanSpace ℂ
                (PptFactorization.GaussianModel.SampleCoord p q
                  (DeletedColumn α₀)) => z.2.1) :=
      measurable_fst.comp measurable_snd
    have hright :
        Measurable
          (fun z : ℝ × EuclideanSpace ℂ (BipIndex p q) ×
              EuclideanSpace ℂ
                (PptFactorization.GaussianModel.SampleCoord p q
                  (DeletedColumn α₀)) => toBackground z.2.2) :=
      hmeas_toBackground.comp (measurable_snd.comp measurable_snd)
    have hpair :
        Measurable
          (fun z : ℝ × EuclideanSpace ℂ (BipIndex p q) ×
              EuclideanSpace ℂ
                (PptFactorization.GaussianModel.SampleCoord p q
                  (DeletedColumn α₀)) =>
            (z.2.1, toBackground z.2.2)) :=
      hmid.prodMk hright
    exact hfst.prodMk hpair
  haveI : SFinite massLaw := by
    simpa [massLaw] using hBlock.sfinite_massLaw
  haveI : SFinite directionLaw := hBlock.sfinite_leftDirectionLaw
  haveI : SFinite deletedDirectionLaw := hBlock.sfinite_rightDirectionLaw
  have hBlockTriple :
      Measure.map (fun X => T (block X)) μ =
        massLaw.prod (directionLaw.prod deletedDirectionLaw) := by
    calc
      Measure.map (fun X => T (block X)) μ =
          Measure.map T (Measure.map block μ) := by
            rw [Measure.map_map (μ := μ) (f := block) (g := T)
              hmeas_T hmeas_block]
            rfl
      _ = massLaw.prod (directionLaw.prod deletedDirectionLaw) := by
            simpa [T, block, massLaw] using hBlock.map_triple_eq
  have hMapped :
      Measure.map (fun X => Φ (T (block X))) μ =
        massLaw.prod (directionLaw.prod backgroundLaw) := by
    calc
      Measure.map (fun X => Φ (T (block X))) μ =
          Measure.map Φ (Measure.map (fun X => T (block X)) μ) := by
            rw [Measure.map_map
              (μ := μ)
              (f := fun X => T (block X))
              (g := Φ)
              hmeas_Φ (hmeas_T.comp hmeas_block)]
            rfl
      _ = Measure.map Φ (massLaw.prod (directionLaw.prod deletedDirectionLaw)) := by
            rw [hBlockTriple]
      _ = massLaw.prod (directionLaw.prod backgroundLaw) := by
            have hprod :=
              measure_map_prod_nested_right
                massLaw directionLaw deletedDirectionLaw hmeas_toBackground
            simpa [Φ, toBackground, backgroundLaw, hBackgroundLaw] using hprod
  have hTriple :
      Measure.map
          (fun X =>
            (sampleColumnMass (p := p) (q := q) (σ := σ) X α₀,
              sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀,
              sampleColumnComplementNormalized
                (p := p) (q := q) (σ := σ) X α₀))
          μ =
        (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ)).prod
          (directionLaw.prod
            (deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀)) := by
    have hfun :
        (fun X => Φ (T (block X))) =
          (fun X : SampleMatrix p q σ =>
            (sampleColumnMass (p := p) (q := q) (σ := σ) X α₀,
              sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀,
              sampleColumnComplementNormalized
                (p := p) (q := q) (σ := σ) X α₀)) := by
      funext X
      simp [Φ, T, block, toBackground, hMass X, hDirection X, hBackground X]
    simpa [hfun, massLaw, backgroundLaw] using hMapped
  exact
    CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence.of_map_triple_eq
      (p := p) (q := q) (σ := σ) (μ := μ) (α₀ := α₀)
      hσ hDirectionProb hTriple

set_option linter.unusedSectionVars false in
/-- Same transport as `of_hermitianBlock_transport`, with the left-direction
identification discharged by the concrete coordinate computation. -/
theorem CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence.of_hermitianBlock_transport_concreteDirection
    [Nonempty p] [Nonempty q]
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {directionLaw : Measure (EuclideanSpace ℂ (BipIndex p q))}
    {deletedDirectionLaw :
      Measure (EuclideanSpace ℂ
        (PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀)))}
    (hσ : 2 ≤ Fintype.card σ)
    (hDirectionProb : IsProbabilityMeasure directionLaw)
    (hBlock :
      HermitianBlockSphericalDecompositionIndependence
        (ι := BipIndex p q)
        (κ := PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀))
        (Measure.map
          (deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀) μ)
        (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ))
        directionLaw deletedDirectionLaw)
    (hBackgroundLaw :
      Measure.map
          (deletedColumnRightDirectionToBackground
            (p := p) (q := q) (σ := σ) α₀)
          deletedDirectionLaw =
        deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀)
    (hMass :
      ∀ X : SampleMatrix p q σ,
        hermitianBlockMass
          (ι := BipIndex p q)
          (κ := PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀))
          (deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀ X) =
        sampleColumnMass (p := p) (q := q) (σ := σ) X α₀)
    (hBackground :
      ∀ X : SampleMatrix p q σ,
        deletedColumnRightDirectionToBackground
          (p := p) (q := q) (σ := σ) α₀
          (hermitianBlockRightDirection
            (ι := BipIndex p q)
            (κ := PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀))
            (deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀ X)) =
        sampleColumnComplementNormalized (p := p) (q := q) (σ := σ) X α₀) :
    CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence
      (p := p) (q := q) (σ := σ) μ α₀ directionLaw :=
  CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence.of_hermitianBlock_transport
    (p := p) (q := q) (σ := σ) (μ := μ) (α₀ := α₀)
    hσ hDirectionProb hBlock hBackgroundLaw hMass
    (fun X =>
      hermitianBlockLeftDirection_deletedColumnBlockVector
        (p := p) (q := q) (σ := σ) X α₀)
    hBackground

set_option linter.unusedSectionVars false in
/-- Fully concrete deleted-column transport from the abstract Hermitian block
decomposition.

The two remaining coordinate identifications are discharged here:

* the left block mass is exactly `sampleColumnMass`;
* the zero-extended normalized right block is exactly
  `sampleColumnComplementNormalized`.

Thus downstream column-decomposition code can consume the abstract block law
without carrying any pointwise transport hypotheses. -/
theorem CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence.of_hermitianBlock_transport_concrete
    [Nonempty p] [Nonempty q]
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {directionLaw : Measure (EuclideanSpace ℂ (BipIndex p q))}
    {deletedDirectionLaw :
      Measure (EuclideanSpace ℂ
        (PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀)))}
    (hσ : 2 ≤ Fintype.card σ)
    (hDirectionProb : IsProbabilityMeasure directionLaw)
    (hBlock :
      HermitianBlockSphericalDecompositionIndependence
        (ι := BipIndex p q)
        (κ := PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀))
        (Measure.map
          (deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀) μ)
        (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ))
        directionLaw deletedDirectionLaw)
    (hBackgroundLaw :
      Measure.map
          (deletedColumnRightDirectionToBackground
            (p := p) (q := q) (σ := σ) α₀)
          deletedDirectionLaw =
        deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀) :
    CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence
      (p := p) (q := q) (σ := σ) μ α₀ directionLaw :=
  CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence.of_hermitianBlock_transport_concreteDirection
    (p := p) (q := q) (σ := σ) (μ := μ) (α₀ := α₀)
    hσ hDirectionProb hBlock hBackgroundLaw
    (fun X =>
      hermitianBlockMass_deletedColumnBlockVector
        (p := p) (q := q) (σ := σ) X α₀)
    (fun X =>
      deletedColumnRightDirectionToBackground_hermitianBlockRightDirection_deletedColumnBlockVector
        (p := p) (q := q) (σ := σ) X α₀)

set_option linter.unusedSectionVars false in
/-- Fully concrete deleted-column transport when the right-block marginal is
the genuine deleted-column spherical law.

This is the safe constructor for the one-column lower-bound pipeline: the
background marginal is forced to be
`Measure.map (deletedColumnZeroExtend α₀)
  (sphericalModelMeasure p q (DeletedColumn α₀))`.
There is no hypothesis mentioning the full spherical law on `σ`. -/
theorem CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence.of_hermitianBlock_transport_deletedBackground
    [Nonempty p] [Nonempty q]
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {directionLaw : Measure (EuclideanSpace ℂ (BipIndex p q))}
    (hσ : 2 ≤ Fintype.card σ)
    (hDirectionProb : IsProbabilityMeasure directionLaw)
    (hBlock :
      HermitianBlockSphericalDecompositionIndependence
        (ι := BipIndex p q)
        (κ := PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀))
        (Measure.map
          (deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀) μ)
        (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ))
        directionLaw
        (deletedColumnRightDirectionLaw
          (p := p) (q := q) (σ := σ) α₀)) :
    CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence
      (p := p) (q := q) (σ := σ) μ α₀ directionLaw := by
  have hBackgroundLaw :
      Measure.map
          (deletedColumnRightDirectionToBackground
            (p := p) (q := q) (σ := σ) α₀)
          (deletedColumnRightDirectionLaw
            (p := p) (q := q) (σ := σ) α₀) =
        deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀ := by
    simpa [deletedColumnBackgroundLaw] using
      deletedColumnRightDirectionLaw_toBackground_eq_zeroExtend_sphericalModelMeasure
        (p := p) (q := q) (σ := σ) α₀
  exact
    CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence.of_hermitianBlock_transport
      (p := p) (q := q) (σ := σ) (μ := μ) (α₀ := α₀)
      hσ hDirectionProb hBlock hBackgroundLaw
      (fun X => by
        simpa using
          congrArg Prod.fst
            (deletedColumnBlockVector_concreteTriple
              (p := p) (q := q) (σ := σ) X α₀))
      (fun X => by
        simpa using
          congrArg (fun z => z.2.1)
            (deletedColumnBlockVector_concreteTriple
              (p := p) (q := q) (σ := σ) X α₀))
      (fun X => by
        simpa using
          congrArg (fun z => z.2.2)
            (deletedColumnBlockVector_concreteTriple
              (p := p) (q := q) (σ := σ) X α₀))

set_option linter.unusedSectionVars false in
/-- Column/deleted-background decomposition from the canonical Hermitian
block spherical decomposition.

This is the no-extra-transport theorem for the concrete spherical model.  The
input block law lives on the genuine orthogonal block

`ℂ^(BipIndex p q) ⊕ ℂ^(SampleCoord p q (DeletedColumn α₀))`

obtained by applying `deletedColumnBlockVector α₀` to
`sphericalModelMeasure p q σ`.  That single block decomposition gives:

* the column mass law with Beta parameters
  `(card (BipIndex p q), card (BipIndex p q) * (card σ - 1))`;
* the actual column direction law;
* the normalized deleted-column background law, zero-extended back to `σ`.

In particular, the background marginal is not the full spherical law on `σ`;
it is the deleted-column spherical law pushed forward by zero extension.

The proof is the clean final downstream call:

1. recover that `directionLaw` is a probability measure from the left marginal
   of the canonical Hermitian block law;
2. forget the word `Canonical` by rewriting the mass law through
   `hermitianBlockMassBetaMeasure_deletedColumn_eq_canonicalColumnMassBetaMeasure`;
3. invoke
   `CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence
      .of_hermitianBlock_transport_deletedBackground`. -/
theorem CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence.of_canonicalHermitianBlock_sphericalLaw
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    [Nonempty p] [Nonempty q]
    {α₀ : σ}
    {directionLaw : Measure (EuclideanSpace ℂ (BipIndex p q))}
    (hσ : 2 ≤ Fintype.card σ)
    (hBlock :
      CanonicalHermitianBlockSphericalDecompositionIndependence
        (ι := BipIndex p q)
        (κ := PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀))
        (Measure.map
          (deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀)
          (sphericalModelMeasure (p := p) (q := q) (σ := σ)))
        directionLaw
        (deletedColumnRightDirectionLaw
          (p := p) (q := q) (σ := σ) α₀)) :
    CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence
      (p := p) (q := q) (σ := σ)
      (sphericalModelMeasure (p := p) (q := q) (σ := σ)) α₀ directionLaw := by
  classical
  let block : SampleMatrix p q σ →
      EuclideanSpace ℂ
        (Sum (BipIndex p q)
          (PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀))) :=
    deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀
  let μblock : Measure
      (EuclideanSpace ℂ
        (Sum (BipIndex p q)
          (PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀)))) :=
    Measure.map block (sphericalModelMeasure (p := p) (q := q) (σ := σ))
  have hmeas_block : Measurable block := by
    simpa [block] using
      measurable_deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀
  haveI : IsProbabilityMeasure
      (sphericalModelMeasure (p := p) (q := q) (σ := σ)) :=
    sphericalModelMeasure_isProbabilityMeasure (p := p) (q := q) (σ := σ)
  haveI : IsProbabilityMeasure μblock := by
    dsimp [μblock]
    exact Measure.isProbabilityMeasure_map hmeas_block.aemeasurable
  have hLeftMarginal :
      Measure.map
          (hermitianBlockLeftDirection
            (ι := BipIndex p q)
            (κ := PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀)))
          μblock =
        directionLaw := by
    simpa [μblock, block,
      CanonicalHermitianBlockSphericalDecompositionIndependence] using
      hBlock.map_leftDirection_eq
  have hDirectionProb : IsProbabilityMeasure directionLaw := by
    rw [← hLeftMarginal]
    exact
      Measure.isProbabilityMeasure_map
        (measurable_hermitianBlockLeftDirection
          (ι := BipIndex p q)
          (κ := PptFactorization.GaussianModel.SampleCoord p q
            (DeletedColumn α₀))).aemeasurable
  have hBlockHermitian :
      HermitianBlockSphericalDecompositionIndependence
        (ι := BipIndex p q)
        (κ := PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀))
        (Measure.map
          (deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀)
          (sphericalModelMeasure (p := p) (q := q) (σ := σ)))
        (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ))
        directionLaw
        (deletedColumnRightDirectionLaw
          (p := p) (q := q) (σ := σ) α₀) := by
    simpa [CanonicalHermitianBlockSphericalDecompositionIndependence,
      hermitianBlockMassBetaMeasure_deletedColumn_eq_canonicalColumnMassBetaMeasure
        (p := p) (q := q) (σ := σ) α₀] using hBlock
  exact
    CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence.of_hermitianBlock_transport_deletedBackground
      (p := p) (q := q) (σ := σ)
      (μ := sphericalModelMeasure (p := p) (q := q) (σ := σ))
      (α₀ := α₀) (directionLaw := directionLaw)
      hσ hDirectionProb hBlockHermitian

set_option linter.unusedSectionVars false in
/-- Concrete deleted-column specialization of the Hermitian block spherical
law.

At this point in the file, the genuinely analytic core has been isolated as
`canonicalHermitianBlockSphericalDecompositionIndependence_noInput` on an
abstract block `ℂ^ι ⊕ ℂ^κ`.  The present declaration is the remaining bridge to
the concrete deleted-column block appearing in the PPT model. -/
theorem deletedColumnRightDirectionLaw_eq_surfaceMeasureAmbient
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    [Nonempty p] [Nonempty q]
    (α₀ : σ)
    (hσ : 2 ≤ Fintype.card σ) :
    deletedColumnRightDirectionLaw
        (p := p) (q := q) (σ := σ) α₀ =
      surfaceMeasureAmbient
        (PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀)) := by
  haveI : Nonempty (DeletedColumn α₀) :=
    deletedColumn_nonempty_of_two_le_card (α₀ := α₀) hσ
  rw [deletedColumnRightDirectionLaw]
  rw [polarLaw (p := p) (q := q) (σ := DeletedColumn α₀)]
  exact
    surfaceModelMeasure_map_complexLinearIsometryEquiv
      (p := p) (q := q) (σ := DeletedColumn α₀)
      (τ := PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀))
      (sampleMatrixComplexLinearIsometryEquiv
        (p := p) (q := q) (σ := DeletedColumn α₀))

set_option linter.unusedSectionVars false in
/-- The concrete pushforward law of the distinguished column direction is the
ambient surface measure on `ℂ^(BipIndex p q)`. -/
theorem columnDirectionPushforward_sphericalModelMeasure_eq_surfaceMeasureAmbient
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    [Nonempty p] [Nonempty q]
    (α₀ : σ)
    (hσ : 2 ≤ Fintype.card σ) :
    columnDirectionPushforward
        (p := p) (q := q) (σ := σ)
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)) α₀ =
      surfaceMeasureAmbient (BipIndex p q) := by
  haveI : Nonempty σ := by
    refine Fintype.card_pos_iff.mp ?_
    exact lt_of_lt_of_le (by norm_num) hσ
  haveI : Nonempty (DeletedColumn α₀) :=
    deletedColumn_nonempty_of_two_le_card (α₀ := α₀) hσ
  let κ := PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀)
  have hBase :=
    canonicalHermitianBlockSphericalDecompositionIndependence_noInput
      (ι := BipIndex p q) (κ := κ)
  unfold columnDirectionPushforward
  have hfun :
      (fun X : SampleMatrix p q σ =>
        sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀) =
      (fun X : SampleMatrix p q σ =>
        hermitianBlockLeftDirection
          (ι := BipIndex p q)
          (κ := κ)
          (deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀ X)) := by
    funext X
    symm
    exact
      hermitianBlockLeftDirection_deletedColumnBlockVector
        (p := p) (q := q) (σ := σ) X α₀
  rw [hfun]
  change
    Measure.map
        ((hermitianBlockLeftDirection
          (ι := BipIndex p q)
          (κ := κ)) ∘
          (deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀))
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)) =
      surfaceMeasureAmbient (BipIndex p q)
  rw [← Measure.map_map
    (measurable_hermitianBlockLeftDirection
      (ι := BipIndex p q) (κ := κ))
    (measurable_deletedColumnBlockVector
      (p := p) (q := q) (σ := σ) α₀)]
  rw [deletedColumnBlockVector_map_sphericalModelMeasure_eq_surfaceMeasureAmbient
    (p := p) (q := q) (σ := σ) α₀]
  simpa [κ] using hBase.map_leftDirection_eq

set_option linter.unusedSectionVars false in
/-- Concrete deleted-column specialization of the Hermitian block spherical
law.

This is now just the concrete block obtained from
`deletedColumnBlockVector α₀`, together with the ambient-surface
identifications of its left and right marginals. -/
theorem CanonicalHermitianBlockSphericalDecompositionIndependence.sphericalLaw
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    [Nonempty p] [Nonempty q]
    (α₀ : σ)
    (hσ : 2 ≤ Fintype.card σ) :
    CanonicalHermitianBlockSphericalDecompositionIndependence
      (ι := BipIndex p q)
      (κ := PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀))
      (Measure.map
        (deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀)
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)))
      (columnDirectionPushforward
        (p := p) (q := q) (σ := σ)
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)) α₀)
      (deletedColumnRightDirectionLaw
        (p := p) (q := q) (σ := σ) α₀) := by
  haveI : Nonempty σ := by
    refine Fintype.card_pos_iff.mp ?_
    exact lt_of_lt_of_le (by norm_num) hσ
  haveI : Nonempty (DeletedColumn α₀) :=
    deletedColumn_nonempty_of_two_le_card (α₀ := α₀) hσ
  let κ := PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀)
  have hBase :
      CanonicalHermitianBlockSphericalDecompositionIndependence
        (ι := BipIndex p q) (κ := κ)
        (surfaceMeasureAmbient (Sum (BipIndex p q) κ))
        (surfaceMeasureAmbient (BipIndex p q))
        (surfaceMeasureAmbient κ) :=
    canonicalHermitianBlockSphericalDecompositionIndependence_noInput
      (ι := BipIndex p q) (κ := κ)
  have hμ :
      Measure.map
          (deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀)
          (sphericalModelMeasure (p := p) (q := q) (σ := σ)) =
        surfaceMeasureAmbient (Sum (BipIndex p q) κ) :=
    deletedColumnBlockVector_map_sphericalModelMeasure_eq_surfaceMeasureAmbient
      (p := p) (q := q) (σ := σ) α₀
  have hleft :
      columnDirectionPushforward
          (p := p) (q := q) (σ := σ)
          (sphericalModelMeasure (p := p) (q := q) (σ := σ)) α₀ =
        surfaceMeasureAmbient (BipIndex p q) :=
    columnDirectionPushforward_sphericalModelMeasure_eq_surfaceMeasureAmbient
      (p := p) (q := q) (σ := σ) α₀ hσ
  have hright :
      deletedColumnRightDirectionLaw
          (p := p) (q := q) (σ := σ) α₀ =
        surfaceMeasureAmbient κ :=
    deletedColumnRightDirectionLaw_eq_surfaceMeasureAmbient
      (p := p) (q := q) (σ := σ) α₀ hσ
  simpa [κ, hμ, hleft, hright] using hBase

set_option linter.unusedSectionVars false in
/-- No-extra-input deleted-background one-column decomposition for the concrete
spherical model.

This is the final Step 9 entrypoint for the whole pipeline:

1. the abstract triple law on `ℂ^ι ⊕ ℂ^κ`;
2. transport to the concrete `deletedColumnBlockVector α₀` block;
3. identification of the three concrete coordinates
   `sampleColumnMass`, `sampleColumnDirection`,
   `sampleColumnComplementNormalized`;
4. identification of the true deleted background law
   `Measure.map (deletedColumnZeroExtend α₀)
      (sphericalModelMeasure (σ := DeletedColumn α₀))`;
5. final application of
   `CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence
      .of_canonicalHermitianBlock_sphericalLaw`. -/
theorem CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence.sphericalLaw
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    [Nonempty p] [Nonempty q]
    {α₀ : σ}
    (hσ : 2 ≤ Fintype.card σ) :
    CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence
      (p := p) (q := q) (σ := σ)
      (sphericalModelMeasure (p := p) (q := q) (σ := σ))
      α₀
      (columnDirectionPushforward
        (p := p) (q := q) (σ := σ)
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)) α₀) :=
  CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence.of_canonicalHermitianBlock_sphericalLaw
      (p := p) (q := q) (σ := σ)
      (α₀ := α₀)
      (directionLaw :=
        columnDirectionPushforward
          (p := p) (q := q) (σ := σ)
          (sphericalModelMeasure (p := p) (q := q) (σ := σ)) α₀)
      hσ
      (CanonicalHermitianBlockSphericalDecompositionIndependence.sphericalLaw
        (p := p) (q := q) (σ := σ) α₀ hσ)

set_option linter.unusedSectionVars false in
/-- The background marginal in the final deleted-background spherical
decomposition is exactly the zero-extended reduced spherical law.

This is the explicit downstream Step 8 guarantee: the third marginal is

`Measure.map (deletedColumnZeroExtend α₀)
  (sphericalModelMeasure (σ := DeletedColumn α₀))`,

not the full spherical law on `σ`. -/
theorem CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence.sphericalLaw_map_background_eq
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    [Nonempty p] [Nonempty q]
    {α₀ : σ}
    (hσ : 2 ≤ Fintype.card σ) :
    Measure.map
        (fun X =>
          sampleColumnComplementNormalized
            (p := p) (q := q) (σ := σ) X α₀)
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)) =
      Measure.map
        (deletedColumnZeroExtend (p := p) (q := q) (σ := σ) α₀)
        (sphericalModelMeasure
          (p := p) (q := q) (σ := DeletedColumn α₀)) := by
  let I :=
    CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence.sphericalLaw
      (p := p) (q := q) (σ := σ) (α₀ := α₀) hσ
  simpa [CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence,
    deletedColumnBackgroundLaw] using I.map_background_eq

set_option linter.unusedSectionVars false in
/-- Deleted-background version of the favourable-event product formula.

This is the one-shot probability identity used by the column-spike lower
bound once the column decomposition has been transported to the genuine
deleted-column background law. -/
theorem CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence.favorable_event_probability_eq
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {directionLaw : Measure (EuclideanSpace ℂ (BipIndex p q))}
    (I :
      CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence
        (p := p) (q := q) (σ := σ) μ α₀ directionLaw)
    {q₀ δ : ℝ}
    {directionSet : Set (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundSet : Set (SampleMatrix p q σ)}
    (hdirection : MeasurableSet directionSet)
    (hbackground : MeasurableSet backgroundSet) :
    μ.real
        (sphericalOneColumnFavorableEvent
          (p := p) (q := q) (σ := σ)
          α₀ q₀ δ directionSet backgroundSet) =
      (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ)).real
          (betaColumnIntervalSet q₀ δ) *
        directionLaw.real directionSet *
          (deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀).real
            backgroundSet := by
  simpa [CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence] using
    CanonicalSphericalOneColumnDecompositionIndependence.favorable_event_probability_eq
      (p := p) (q := q) (σ := σ)
      (I := I) hdirection hbackground

set_option linter.unusedSectionVars false in
/-- Eventual product identity from a family of deleted-background one-column
decompositions.

This is the family-level `hProduct` shape expected by
`SpikeLowerBoundInput.of_oneColumn_probability_pipeline`, with the background
law fixed to the deleted-column spherical law pushed forward by zero-extension. -/
theorem eventual_columnProb_eq_product_of_deletedBackgroundDecomposition
    {μ : ℕ → Measure (SampleMatrix p q σ)} {α₀ : σ}
    {directionLaw : ℕ → Measure (EuclideanSpace ℂ (BipIndex p q))}
    {q₀ δ : ℕ → ℝ}
    {directionSet : ℕ → Set (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundSet : ℕ → Set (SampleMatrix p q σ)}
    {betaProb capProb backgroundProb columnProb : ℕ → ℝ}
    (hIndep :
      ∀ᶠ d in atTop,
        CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence
          (p := p) (q := q) (σ := σ) (μ d) α₀ (directionLaw d))
    (hDirectionMeas :
      ∀ᶠ d in atTop, MeasurableSet (directionSet d))
    (hBackgroundMeas :
      ∀ᶠ d in atTop, MeasurableSet (backgroundSet d))
    (hBetaProb :
      ∀ᶠ d in atTop,
        betaProb d =
          (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ)).real
            (betaColumnIntervalSet (q₀ d) (δ d)))
    (hCapProb :
      ∀ᶠ d in atTop,
        capProb d = (directionLaw d).real (directionSet d))
    (hBackgroundProb :
      ∀ᶠ d in atTop,
        backgroundProb d =
          (deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀).real
            (backgroundSet d))
    (hColumnProb :
      ∀ᶠ d in atTop,
        columnProb d =
          (μ d).real
            (sphericalOneColumnFavorableEvent
              (p := p) (q := q) (σ := σ)
              α₀ (q₀ d) (δ d) (directionSet d) (backgroundSet d))) :
    ∀ᶠ d in atTop,
      columnProb d = betaProb d * capProb d * backgroundProb d := by
  have hIndep' :
      ∀ᶠ d in atTop,
        SphericalOneColumnDecompositionIndependence
          (p := p) (q := q) (σ := σ)
          (μ d) α₀
          (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ))
          (directionLaw d)
          (deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀) := by
    filter_upwards [hIndep] with d hI
    simpa [CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence,
      CanonicalSphericalOneColumnDecompositionIndependence] using hI
  exact
    eventual_columnProb_eq_product_of_sphericalOneColumnDecomposition
      (p := p) (q := q) (σ := σ)
      (μ := μ) (α₀ := α₀)
      (massLaw := fun _ =>
        canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ))
      (directionLaw := directionLaw)
      (backgroundLaw := fun _ =>
        deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀)
      (q₀ := q₀) (δ := δ)
      (directionSet := directionSet) (backgroundSet := backgroundSet)
      (betaProb := betaProb) (capProb := capProb)
      (backgroundProb := backgroundProb) (columnProb := columnProb)
      hIndep' hDirectionMeas hBackgroundMeas
      hBetaProb hCapProb hBackgroundProb hColumnProb

set_option linter.unusedSectionVars false in
/-- Family-level `hProduct` directly from the canonical deleted-background
one-column decomposition.

This is the preferred product constructor once the genuine joint law

`X ↦ (R_α(X), U_α(X), Y_deleted(X))`

has been proved.  It avoids routing the probability split through the
Hermitian-block transport interface, so the lower-bound pipeline has only one
probabilistic decomposition input. -/
theorem oneColumnProbabilityPipeline_hProduct_of_deletedBackgroundDecomposition
    {μ : ℕ → Measure (SampleMatrix p q σ)} {α₀ : σ}
    {directionLaw :
      ℝ → ℝ → ℕ → Measure (EuclideanSpace ℂ (BipIndex p q))}
    {q₀ δ : ℝ → ℝ → ℕ → ℝ}
    {directionSet :
      ℝ → ℝ → ℕ → Set (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundSet : ℝ → ℝ → ℕ → Set (SampleMatrix p q σ)}
    {betaProb capProb backgroundProb columnProb : ℝ → ℝ → ℕ → ℝ}
    {root : ℝ}
    (hIndep :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence
              (p := p) (q := q) (σ := σ) (μ d) α₀
              (directionLaw a slack d))
    (hDirectionMeas :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, MeasurableSet (directionSet a slack d))
    (hBackgroundMeas :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, MeasurableSet (backgroundSet a slack d))
    (hBetaProb :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            betaProb a slack d =
              (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ)).real
                (betaColumnIntervalSet (q₀ a slack d) (δ a slack d)))
    (hCapProb :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            capProb a slack d =
              (directionLaw a slack d).real (directionSet a slack d))
    (hBackgroundProb :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            backgroundProb a slack d =
              (deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀).real
                (backgroundSet a slack d))
    (hColumnProb :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            columnProb a slack d =
              (μ d).real
                (sphericalOneColumnFavorableEvent
                  (p := p) (q := q) (σ := σ)
                  α₀ (q₀ a slack d) (δ a slack d)
                  (directionSet a slack d) (backgroundSet a slack d))) :
    ∀ a : ℝ, root < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          columnProb a slack d =
            betaProb a slack d * capProb a slack d *
              backgroundProb a slack d := by
  intro a ha slack hslack
  exact
    eventual_columnProb_eq_product_of_deletedBackgroundDecomposition
      (p := p) (q := q) (σ := σ)
      (μ := μ) (α₀ := α₀)
      (directionLaw := fun d => directionLaw a slack d)
      (q₀ := fun d => q₀ a slack d)
      (δ := fun d => δ a slack d)
      (directionSet := fun d => directionSet a slack d)
      (backgroundSet := fun d => backgroundSet a slack d)
      (betaProb := fun d => betaProb a slack d)
      (capProb := fun d => capProb a slack d)
      (backgroundProb := fun d => backgroundProb a slack d)
      (columnProb := fun d => columnProb a slack d)
      (hIndep a ha slack hslack)
      (hDirectionMeas a ha slack hslack)
      (hBackgroundMeas a ha slack hslack)
      (hBetaProb a ha slack hslack)
      (hCapProb a ha slack hslack)
      (hBackgroundProb a ha slack hslack)
      (hColumnProb a ha slack hslack)

set_option linter.unusedSectionVars false in
/-- Direct canonical Beta interval lower bound from the deleted-background
one-column decomposition.

This is the `hBeta` ingredient without any Hermitian-block transport
hypothesis: the decomposition already contains the canonical Beta marginal for
the distinguished-column mass. -/
theorem eventual_betaProb_lowerBound_of_deletedBackgroundDecomposition
    [Nonempty p] [Nonempty q]
    {μ : ℕ → Measure (SampleMatrix p q σ)} {α₀ : σ}
    {directionLaw : ℕ → Measure (EuclideanSpace ℂ (BipIndex p q))}
    {q₀ δ : ℕ → ℝ}
    {betaProb : ℕ → ℝ}
    (hσ : 2 ≤ Fintype.card σ)
    (hIndep :
      ∀ᶠ d in atTop,
        CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence
          (p := p) (q := q) (σ := σ) (μ d) α₀ (directionLaw d))
    (hq :
      ∀ᶠ d in atTop, 0 < q₀ d)
    (hδ :
      ∀ᶠ d in atTop, 0 < δ d)
    (hupper :
      ∀ᶠ d in atTop, betaColumnIntervalUpper (q₀ d) (δ d) < 1)
    (hBetaProb :
      ∀ᶠ d in atTop,
        betaProb d =
          columnMassIntervalProbability
            (p := p) (q := q) (σ := σ) (μ d) α₀ (q₀ d) (δ d)) :
    ∀ᶠ d in atTop,
      BetaColumnIntervalLowerBound
        (betaProb d)
        (columnMassBetaMainShape (p := p) (q := q))
        (columnMassBetaSampleCount (σ := σ))
        (q₀ d) (δ d) := by
  filter_upwards
    [hIndep, hq, hδ, hupper, hBetaProb]
    with d hI hq_d hδ_d hupper_d hBetaProb_d
  have hBeta :
      BetaColumnIntervalLowerBound
        (columnMassIntervalProbability
          (p := p) (q := q) (σ := σ) (μ d) α₀ (q₀ d) (δ d))
        (columnMassBetaMainShape (p := p) (q := q))
        (columnMassBetaSampleCount (σ := σ))
        (q₀ d) (δ d) :=
    hI.betaColumnIntervalLowerBound
      (p := p) (q := q) (σ := σ)
      hσ hq_d hδ_d hupper_d
  simpa [hBetaProb_d] using hBeta

set_option linter.unusedSectionVars false in
/-- Family-level `hBeta` directly from the canonical deleted-background
one-column decomposition. -/
theorem oneColumnProbabilityPipeline_hBeta_of_deletedBackgroundDecomposition
    [Nonempty p] [Nonempty q]
    {μ : ℕ → Measure (SampleMatrix p q σ)} {α₀ : σ}
    {directionLaw :
      ℝ → ℝ → ℕ → Measure (EuclideanSpace ℂ (BipIndex p q))}
    {q₀ δ : ℝ → ℝ → ℕ → ℝ}
    {betaProb : ℝ → ℝ → ℕ → ℝ}
    {root : ℝ}
    (hσ : 2 ≤ Fintype.card σ)
    (hIndep :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence
              (p := p) (q := q) (σ := σ) (μ d) α₀
              (directionLaw a slack d))
    (hq :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, 0 < q₀ a slack d)
    (hδ :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, 0 < δ a slack d)
    (hupper :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            betaColumnIntervalUpper (q₀ a slack d) (δ a slack d) < 1)
    (hBetaProb :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            betaProb a slack d =
              columnMassIntervalProbability
                (p := p) (q := q) (σ := σ)
                (μ d) α₀ (q₀ a slack d) (δ a slack d)) :
    ∀ a : ℝ, root < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          BetaColumnIntervalLowerBound
            (betaProb a slack d)
            (columnMassBetaMainShape (p := p) (q := q))
            (columnMassBetaSampleCount (σ := σ))
            (q₀ a slack d) (δ a slack d) := by
  intro a ha slack hslack
  exact
    eventual_betaProb_lowerBound_of_deletedBackgroundDecomposition
      (p := p) (q := q) (σ := σ)
      (μ := μ) (α₀ := α₀)
      (directionLaw := fun d => directionLaw a slack d)
      (q₀ := fun d => q₀ a slack d)
      (δ := fun d => δ a slack d)
      (betaProb := fun d => betaProb a slack d)
      hσ
      (hIndep a ha slack hslack)
      (hq a ha slack hslack)
      (hδ a ha slack hslack)
      (hupper a ha slack hslack)
      (hBetaProb a ha slack hslack)

set_option linter.unusedSectionVars false in
/-- Direct canonical cap lower bound from the deleted-background one-column
decomposition and the Haar/projective overlap law for its direction marginal.

This is the `hCap` ingredient without any Hermitian-block transport
hypothesis. -/
theorem eventual_capProb_lowerBound_of_deletedBackgroundDecomposition
    {μ : ℕ → Measure (SampleMatrix p q σ)} {α₀ : σ}
    {directionLaw : ℕ → Measure (EuclideanSpace ℂ (BipIndex p q))}
    {e : ℕ → EuclideanSpace ℂ (BipIndex p q)}
    {capProb : ℕ → ℝ}
    (hIndep :
      ∀ᶠ d in atTop,
        CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence
          (p := p) (q := q) (σ := σ) (μ d) α₀ (directionLaw d))
    (hDirectionBeta :
      ∀ᶠ d in atTop,
        AmbientHaarProjectiveOverlapBetaLaw
          (ι := BipIndex p q) (directionLaw d))
    (hUnit :
      ∀ᶠ d in atTop, ‖e d‖ = 1)
    (hCapProb :
      ∀ᶠ d in atTop,
        capProb d =
          columnDirectionCapProbability
            (p := p) (q := q) (σ := σ) (μ d) α₀ (e d)
            (1 / (columnMassBetaMainShape (p := p) (q := q) : ℝ))) :
    ∀ᶠ d in atTop,
      ProjectiveCapProbabilityLowerBound
        (capProb d)
        (columnMassBetaMainShape (p := p) (q := q))
        (1 / (columnMassBetaMainShape (p := p) (q := q) : ℝ)) := by
  filter_upwards
    [hIndep, hDirectionBeta, hUnit, hCapProb]
    with d hI hBeta_d hUnit_d hCapProb_d
  have hColumnBeta :
      AmbientHaarProjectiveOverlapBetaLaw
        (ι := BipIndex p q)
        (columnDirectionPushforward (p := p) (q := q) (σ := σ) (μ d) α₀) :=
    hI.columnDirectionAmbientHaarProjectiveOverlapBetaLaw
      (p := p) (q := q) (σ := σ) hBeta_d
  have hCap :
      ProjectiveCapProbabilityLowerBound
        (columnDirectionCapProbability
          (p := p) (q := q) (σ := σ) (μ d) α₀ (e d)
          (1 / (columnMassBetaMainShape (p := p) (q := q) : ℝ)))
        (columnMassBetaMainShape (p := p) (q := q))
        (1 / (columnMassBetaMainShape (p := p) (q := q) : ℝ)) :=
    hColumnBeta.toColumnDirectionProjectiveCapProbabilityLowerBound_inv
      (p := p) (q := q) (σ := σ) (μ := μ d) (α₀ := α₀)
      hUnit_d
  simpa [hCapProb_d] using hCap

set_option linter.unusedSectionVars false in
/-- Family-level `hCap` directly from the canonical deleted-background
one-column decomposition. -/
theorem oneColumnProbabilityPipeline_hCap_of_deletedBackgroundDecomposition
    {μ : ℕ → Measure (SampleMatrix p q σ)} {α₀ : σ}
    {directionLaw :
      ℝ → ℝ → ℕ → Measure (EuclideanSpace ℂ (BipIndex p q))}
    {e : ℝ → ℝ → ℕ → EuclideanSpace ℂ (BipIndex p q)}
    {capProb : ℝ → ℝ → ℕ → ℝ}
    {root : ℝ}
    (hIndep :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence
              (p := p) (q := q) (σ := σ) (μ d) α₀
              (directionLaw a slack d))
    (hDirectionBeta :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            AmbientHaarProjectiveOverlapBetaLaw
              (ι := BipIndex p q) (directionLaw a slack d))
    (hUnit :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, ‖e a slack d‖ = 1)
    (hCapProb :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            capProb a slack d =
              columnDirectionCapProbability
                (p := p) (q := q) (σ := σ) (μ d) α₀
                (e a slack d)
                (1 / (columnMassBetaMainShape (p := p) (q := q) : ℝ))) :
    ∀ a : ℝ, root < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ProjectiveCapProbabilityLowerBound
            (capProb a slack d)
            (columnMassBetaMainShape (p := p) (q := q))
            (1 / (columnMassBetaMainShape (p := p) (q := q) : ℝ)) := by
  intro a ha slack hslack
  exact
    eventual_capProb_lowerBound_of_deletedBackgroundDecomposition
      (p := p) (q := q) (σ := σ)
      (μ := μ) (α₀ := α₀)
      (directionLaw := fun d => directionLaw a slack d)
      (e := fun d => e a slack d)
      (capProb := fun d => capProb a slack d)
      (hIndep a ha slack hslack)
      (hDirectionBeta a ha slack hslack)
      (hUnit a ha slack hslack)
      (hCapProb a ha slack hslack)

set_option linter.unusedSectionVars false in
/-- Eventual product identity obtained by transporting a Hermitian block product
law to the deleted-column background law.

This is the no-extra-input closure of the product-probability step: once the
Hermitian block law is available, the column event probability is automatically
the product of its Beta, cap, and deleted-background factors. -/
theorem eventual_columnProb_eq_product_of_hermitianBlock_transport_deletedBackground
    [Nonempty p] [Nonempty q]
    {μ : ℕ → Measure (SampleMatrix p q σ)} {α₀ : σ}
    {directionLaw : ℕ → Measure (EuclideanSpace ℂ (BipIndex p q))}
    {q₀ δ : ℕ → ℝ}
    {directionSet : ℕ → Set (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundSet : ℕ → Set (SampleMatrix p q σ)}
    {betaProb capProb backgroundProb columnProb : ℕ → ℝ}
    (hσ : 2 ≤ Fintype.card σ)
    (hDirectionProb :
      ∀ᶠ d in atTop, IsProbabilityMeasure (directionLaw d))
    (hBlock :
      ∀ᶠ d in atTop,
        HermitianBlockSphericalDecompositionIndependence
          (ι := BipIndex p q)
          (κ := PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀))
          (Measure.map
            (deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀) (μ d))
          (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ))
          (directionLaw d)
          (deletedColumnRightDirectionLaw
            (p := p) (q := q) (σ := σ) α₀))
    (hDirectionMeas :
      ∀ᶠ d in atTop, MeasurableSet (directionSet d))
    (hBackgroundMeas :
      ∀ᶠ d in atTop, MeasurableSet (backgroundSet d))
    (hBetaProb :
      ∀ᶠ d in atTop,
        betaProb d =
          (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ)).real
            (betaColumnIntervalSet (q₀ d) (δ d)))
    (hCapProb :
      ∀ᶠ d in atTop,
        capProb d = (directionLaw d).real (directionSet d))
    (hBackgroundProb :
      ∀ᶠ d in atTop,
        backgroundProb d =
          (deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀).real
            (backgroundSet d))
    (hColumnProb :
      ∀ᶠ d in atTop,
        columnProb d =
          (μ d).real
            (sphericalOneColumnFavorableEvent
              (p := p) (q := q) (σ := σ)
              α₀ (q₀ d) (δ d) (directionSet d) (backgroundSet d))) :
    ∀ᶠ d in atTop,
      columnProb d = betaProb d * capProb d * backgroundProb d := by
  have hIndep :
      ∀ᶠ d in atTop,
        CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence
          (p := p) (q := q) (σ := σ) (μ d) α₀ (directionLaw d) := by
    filter_upwards [hDirectionProb, hBlock] with d hDir hBlk
    exact
      CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence.of_hermitianBlock_transport_deletedBackground
        (p := p) (q := q) (σ := σ)
        (μ := μ d) (α₀ := α₀) (directionLaw := directionLaw d)
        hσ hDir hBlk
  exact
    eventual_columnProb_eq_product_of_deletedBackgroundDecomposition
      (p := p) (q := q) (σ := σ)
      (μ := μ) (α₀ := α₀) (directionLaw := directionLaw)
      (q₀ := q₀) (δ := δ)
      (directionSet := directionSet) (backgroundSet := backgroundSet)
      (betaProb := betaProb) (capProb := capProb)
      (backgroundProb := backgroundProb) (columnProb := columnProb)
      hIndep hDirectionMeas hBackgroundMeas
      hBetaProb hCapProb hBackgroundProb hColumnProb

set_option linter.unusedSectionVars false in
/-- Eventual canonical Beta interval lower bound obtained from the Hermitian
block transport to the deleted-background one-column decomposition.

This is the direct `hBeta` content before any family-level `a/slack`
bookkeeping: if `betaProb d` is the actual distinguished-column mass interval
probability, then it satisfies the canonical Beta lower bound with parameters
`(card (BipIndex p q), card σ)`. -/
theorem eventual_betaProb_lowerBound_of_hermitianBlock_transport_deletedBackground
    [Nonempty p] [Nonempty q]
    {μ : ℕ → Measure (SampleMatrix p q σ)} {α₀ : σ}
    {directionLaw : ℕ → Measure (EuclideanSpace ℂ (BipIndex p q))}
    {q₀ δ : ℕ → ℝ}
    {betaProb : ℕ → ℝ}
    (hσ : 2 ≤ Fintype.card σ)
    (hDirectionProb :
      ∀ᶠ d in atTop, IsProbabilityMeasure (directionLaw d))
    (hBlock :
      ∀ᶠ d in atTop,
        HermitianBlockSphericalDecompositionIndependence
          (ι := BipIndex p q)
          (κ := PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀))
          (Measure.map
            (deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀)
            (μ d))
          (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ))
          (directionLaw d)
          (deletedColumnRightDirectionLaw
            (p := p) (q := q) (σ := σ) α₀))
    (hq :
      ∀ᶠ d in atTop, 0 < q₀ d)
    (hδ :
      ∀ᶠ d in atTop, 0 < δ d)
    (hupper :
      ∀ᶠ d in atTop, betaColumnIntervalUpper (q₀ d) (δ d) < 1)
    (hBetaProb :
      ∀ᶠ d in atTop,
        betaProb d =
          columnMassIntervalProbability
            (p := p) (q := q) (σ := σ) (μ d) α₀ (q₀ d) (δ d)) :
    ∀ᶠ d in atTop,
      BetaColumnIntervalLowerBound
        (betaProb d)
        (columnMassBetaMainShape (p := p) (q := q))
        (columnMassBetaSampleCount (σ := σ))
        (q₀ d) (δ d) := by
  filter_upwards
    [hDirectionProb, hBlock, hq, hδ, hupper, hBetaProb]
    with d hDir hBlk hq_d hδ_d hupper_d hBetaProb_d
  have hI :
      CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence
        (p := p) (q := q) (σ := σ) (μ d) α₀ (directionLaw d) :=
    CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence.of_hermitianBlock_transport_deletedBackground
        (p := p) (q := q) (σ := σ)
        (μ := μ d) (α₀ := α₀) (directionLaw := directionLaw d)
        hσ hDir hBlk
  have hBeta :
      BetaColumnIntervalLowerBound
        (columnMassIntervalProbability
          (p := p) (q := q) (σ := σ) (μ d) α₀ (q₀ d) (δ d))
        (columnMassBetaMainShape (p := p) (q := q))
        (columnMassBetaSampleCount (σ := σ))
        (q₀ d) (δ d) :=
    hI.betaColumnIntervalLowerBound
      (p := p) (q := q) (σ := σ)
      hσ hq_d hδ_d hupper_d
  simpa [hBetaProb_d] using hBeta

set_option linter.unusedSectionVars false in
/-- Family-level `hBeta` constructor for
`SpikeLowerBoundInput.of_oneColumn_probability_pipeline`.

The only real input is the Hermitian block spherical decomposition; the Beta
law for the distinguished-column mass is then automatic, and the interval
lower bound follows for every chosen spike strength and logarithmic slack. -/
theorem oneColumnProbabilityPipeline_hBeta_of_hermitianBlock_transport_deletedBackground
    [Nonempty p] [Nonempty q]
    {μ : ℕ → Measure (SampleMatrix p q σ)} {α₀ : σ}
    {directionLaw :
      ℝ → ℝ → ℕ → Measure (EuclideanSpace ℂ (BipIndex p q))}
    {q₀ δ : ℝ → ℝ → ℕ → ℝ}
    {betaProb : ℝ → ℝ → ℕ → ℝ}
    {root : ℝ}
    (hσ : 2 ≤ Fintype.card σ)
    (hDirectionProb :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, IsProbabilityMeasure (directionLaw a slack d))
    (hBlock :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            HermitianBlockSphericalDecompositionIndependence
              (ι := BipIndex p q)
              (κ := PptFactorization.GaussianModel.SampleCoord p q
                (DeletedColumn α₀))
              (Measure.map
                (deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀)
                (μ d))
              (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ))
              (directionLaw a slack d)
              (deletedColumnRightDirectionLaw
                (p := p) (q := q) (σ := σ) α₀))
    (hq :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, 0 < q₀ a slack d)
    (hδ :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, 0 < δ a slack d)
    (hupper :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            betaColumnIntervalUpper (q₀ a slack d) (δ a slack d) < 1)
    (hBetaProb :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            betaProb a slack d =
              columnMassIntervalProbability
                (p := p) (q := q) (σ := σ)
                (μ d) α₀ (q₀ a slack d) (δ a slack d)) :
    ∀ a : ℝ, root < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          BetaColumnIntervalLowerBound
            (betaProb a slack d)
            (columnMassBetaMainShape (p := p) (q := q))
            (columnMassBetaSampleCount (σ := σ))
            (q₀ a slack d) (δ a slack d) := by
  intro a ha slack hslack
  exact
    eventual_betaProb_lowerBound_of_hermitianBlock_transport_deletedBackground
      (p := p) (q := q) (σ := σ)
      (μ := μ) (α₀ := α₀)
      (directionLaw := fun d => directionLaw a slack d)
      (q₀ := fun d => q₀ a slack d)
      (δ := fun d => δ a slack d)
      (betaProb := fun d => betaProb a slack d)
      hσ
      (hDirectionProb a ha slack hslack)
      (hBlock a ha slack hslack)
      (hq a ha slack hslack)
      (hδ a ha slack hslack)
      (hupper a ha slack hslack)
      (hBetaProb a ha slack hslack)

set_option linter.unusedSectionVars false in
/-- Eventual canonical cap lower bound obtained from the Hermitian block
transport to the deleted-background one-column decomposition.

This is the direct `hCap` content before any family-level `a/slack`
bookkeeping: if `capProb d` is the actual distinguished-column direction cap
probability at radius `1/N`, and the direction marginal has the canonical
Haar/projective overlap Beta law, then `capProb d` satisfies the projective
cap lower-bound interface used by the lower-bound pipeline. -/
theorem eventual_capProb_lowerBound_of_hermitianBlock_transport_deletedBackground
    [Nonempty p] [Nonempty q]
    {μ : ℕ → Measure (SampleMatrix p q σ)} {α₀ : σ}
    {directionLaw : ℕ → Measure (EuclideanSpace ℂ (BipIndex p q))}
    {e : ℕ → EuclideanSpace ℂ (BipIndex p q)}
    {capProb : ℕ → ℝ}
    (hσ : 2 ≤ Fintype.card σ)
    (hDirectionProb :
      ∀ᶠ d in atTop, IsProbabilityMeasure (directionLaw d))
    (hBlock :
      ∀ᶠ d in atTop,
        HermitianBlockSphericalDecompositionIndependence
          (ι := BipIndex p q)
          (κ := PptFactorization.GaussianModel.SampleCoord p q (DeletedColumn α₀))
          (Measure.map
            (deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀)
            (μ d))
          (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ))
          (directionLaw d)
          (deletedColumnRightDirectionLaw
            (p := p) (q := q) (σ := σ) α₀))
    (hDirectionBeta :
      ∀ᶠ d in atTop,
        AmbientHaarProjectiveOverlapBetaLaw
          (ι := BipIndex p q) (directionLaw d))
    (hUnit :
      ∀ᶠ d in atTop, ‖e d‖ = 1)
    (hCapProb :
      ∀ᶠ d in atTop,
        capProb d =
          columnDirectionCapProbability
            (p := p) (q := q) (σ := σ) (μ d) α₀ (e d)
            (1 / (columnMassBetaMainShape (p := p) (q := q) : ℝ))) :
    ∀ᶠ d in atTop,
      ProjectiveCapProbabilityLowerBound
        (capProb d)
        (columnMassBetaMainShape (p := p) (q := q))
        (1 / (columnMassBetaMainShape (p := p) (q := q) : ℝ)) := by
  filter_upwards
    [hDirectionProb, hBlock, hDirectionBeta, hUnit, hCapProb]
    with d hDir hBlk hBeta_d hUnit_d hCapProb_d
  have hI :
      CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence
        (p := p) (q := q) (σ := σ) (μ d) α₀ (directionLaw d) :=
    CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence.of_hermitianBlock_transport_deletedBackground
      (p := p) (q := q) (σ := σ)
      (μ := μ d) (α₀ := α₀) (directionLaw := directionLaw d)
      hσ hDir hBlk
  have hColumnBeta :
      AmbientHaarProjectiveOverlapBetaLaw
        (ι := BipIndex p q)
        (columnDirectionPushforward (p := p) (q := q) (σ := σ) (μ d) α₀) :=
    hI.columnDirectionAmbientHaarProjectiveOverlapBetaLaw
      (p := p) (q := q) (σ := σ) hBeta_d
  have hCap :
      ProjectiveCapProbabilityLowerBound
        (columnDirectionCapProbability
          (p := p) (q := q) (σ := σ) (μ d) α₀ (e d)
          (1 / (columnMassBetaMainShape (p := p) (q := q) : ℝ)))
        (columnMassBetaMainShape (p := p) (q := q))
        (1 / (columnMassBetaMainShape (p := p) (q := q) : ℝ)) :=
    hColumnBeta.toColumnDirectionProjectiveCapProbabilityLowerBound_inv
      (p := p) (q := q) (σ := σ) (μ := μ d) (α₀ := α₀)
      hUnit_d
  simpa [hCapProb_d] using hCap

set_option linter.unusedSectionVars false in
/-- Family-level `hCap` constructor for
`SpikeLowerBoundInput.of_oneColumn_probability_pipeline`.

The only geometric input is the canonical Haar/projective overlap Beta law for
the chosen direction marginal; after transport through the Hermitian block
decomposition, the theorem produces the projective cap lower bound at the canonical
radius `1/N` for every chosen spike strength and logarithmic slack. -/
theorem oneColumnProbabilityPipeline_hCap_of_hermitianBlock_transport_deletedBackground
    [Nonempty p] [Nonempty q]
    {μ : ℕ → Measure (SampleMatrix p q σ)} {α₀ : σ}
    {directionLaw :
      ℝ → ℝ → ℕ → Measure (EuclideanSpace ℂ (BipIndex p q))}
    {e : ℝ → ℝ → ℕ → EuclideanSpace ℂ (BipIndex p q)}
    {capProb : ℝ → ℝ → ℕ → ℝ}
    {root : ℝ}
    (hσ : 2 ≤ Fintype.card σ)
    (hDirectionProb :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, IsProbabilityMeasure (directionLaw a slack d))
    (hBlock :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            HermitianBlockSphericalDecompositionIndependence
              (ι := BipIndex p q)
              (κ := PptFactorization.GaussianModel.SampleCoord p q
                (DeletedColumn α₀))
              (Measure.map
                (deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀)
                (μ d))
              (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ))
              (directionLaw a slack d)
              (deletedColumnRightDirectionLaw
                (p := p) (q := q) (σ := σ) α₀))
    (hDirectionBeta :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            AmbientHaarProjectiveOverlapBetaLaw
              (ι := BipIndex p q) (directionLaw a slack d))
    (hUnit :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, ‖e a slack d‖ = 1)
    (hCapProb :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            capProb a slack d =
              columnDirectionCapProbability
                (p := p) (q := q) (σ := σ) (μ d) α₀
                (e a slack d)
                (1 / (columnMassBetaMainShape (p := p) (q := q) : ℝ))) :
    ∀ a : ℝ, root < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ProjectiveCapProbabilityLowerBound
            (capProb a slack d)
            (columnMassBetaMainShape (p := p) (q := q))
            (1 / (columnMassBetaMainShape (p := p) (q := q) : ℝ)) := by
  intro a ha slack hslack
  exact
    eventual_capProb_lowerBound_of_hermitianBlock_transport_deletedBackground
      (p := p) (q := q) (σ := σ)
      (μ := μ) (α₀ := α₀)
      (directionLaw := fun d => directionLaw a slack d)
      (e := fun d => e a slack d)
      (capProb := fun d => capProb a slack d)
      hσ
      (hDirectionProb a ha slack hslack)
      (hBlock a ha slack hslack)
      (hDirectionBeta a ha slack hslack)
      (hUnit a ha slack hslack)
      (hCapProb a ha slack hslack)

set_option linter.unusedSectionVars false in
/-- Same product identity, already shaped as the `hProduct` hypothesis of
`SpikeLowerBoundInput.of_oneColumn_probability_pipeline`.

The quantifiers over spike strength and logarithmic slack are only bookkeeping:
for every chosen one-column favourable event, the product identity follows from
the Hermitian block decomposition transported to the deleted-column background. -/
theorem oneColumnProbabilityPipeline_hProduct_of_hermitianBlock_transport_deletedBackground
    [Nonempty p] [Nonempty q]
    {μ : ℕ → Measure (SampleMatrix p q σ)} {α₀ : σ}
    {directionLaw :
      ℝ → ℝ → ℕ → Measure (EuclideanSpace ℂ (BipIndex p q))}
    {q₀ δ : ℝ → ℝ → ℕ → ℝ}
    {directionSet :
      ℝ → ℝ → ℕ → Set (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundSet : ℝ → ℝ → ℕ → Set (SampleMatrix p q σ)}
    {betaProb capProb backgroundProb columnProb : ℝ → ℝ → ℕ → ℝ}
    {root : ℝ}
    (hσ : 2 ≤ Fintype.card σ)
    (hDirectionProb :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, IsProbabilityMeasure (directionLaw a slack d))
    (hBlock :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            HermitianBlockSphericalDecompositionIndependence
              (ι := BipIndex p q)
              (κ := PptFactorization.GaussianModel.SampleCoord p q
                (DeletedColumn α₀))
              (Measure.map
                (deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀)
                (μ d))
              (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ))
              (directionLaw a slack d)
              (deletedColumnRightDirectionLaw
                (p := p) (q := q) (σ := σ) α₀))
    (hDirectionMeas :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, MeasurableSet (directionSet a slack d))
    (hBackgroundMeas :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, MeasurableSet (backgroundSet a slack d))
    (hBetaProb :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            betaProb a slack d =
              (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ)).real
                (betaColumnIntervalSet (q₀ a slack d) (δ a slack d)))
    (hCapProb :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            capProb a slack d =
              (directionLaw a slack d).real (directionSet a slack d))
    (hBackgroundProb :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            backgroundProb a slack d =
              (deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀).real
                (backgroundSet a slack d))
    (hColumnProb :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            columnProb a slack d =
              (μ d).real
                (sphericalOneColumnFavorableEvent
                  (p := p) (q := q) (σ := σ)
                  α₀ (q₀ a slack d) (δ a slack d)
                  (directionSet a slack d) (backgroundSet a slack d))) :
    ∀ a : ℝ, root < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          columnProb a slack d =
            betaProb a slack d * capProb a slack d *
              backgroundProb a slack d := by
  intro a ha slack hslack
  exact
    eventual_columnProb_eq_product_of_hermitianBlock_transport_deletedBackground
      (p := p) (q := q) (σ := σ)
      (μ := μ) (α₀ := α₀)
      (directionLaw := fun d => directionLaw a slack d)
      (q₀ := fun d => q₀ a slack d)
      (δ := fun d => δ a slack d)
      (directionSet := fun d => directionSet a slack d)
      (backgroundSet := fun d => backgroundSet a slack d)
      (betaProb := fun d => betaProb a slack d)
      (capProb := fun d => capProb a slack d)
      (backgroundProb := fun d => backgroundProb a slack d)
      (columnProb := fun d => columnProb a slack d)
      hσ (hDirectionProb a ha slack hslack)
      (hBlock a ha slack hslack)
      (hDirectionMeas a ha slack hslack)
      (hBackgroundMeas a ha slack hslack)
      (hBetaProb a ha slack hslack)
      (hCapProb a ha slack hslack)
      (hBackgroundProb a ha slack hslack)
      (hColumnProb a ha slack hslack)

set_option linter.unusedSectionVars false in
/-- Canonical probability-product identity for the one-column favourable event.

This is the closed `hProduct` calculation with no auxiliary scalar probability
families.  The left-hand side is the actual probability of the concrete
one-column event; the right-hand side is the product of the canonical Beta
mass interval probability, the chosen direction-event probability, and the
deleted-background probability.  The background law is the deleted-column
spherical law pushed forward by zero extension, not the full spherical law on
all columns. -/
theorem oneColumnFavorableEvent_probability_eq_product_of_hermitianBlock_transport_deletedBackground
    [Nonempty p] [Nonempty q]
    {μ : ℕ → Measure (SampleMatrix p q σ)} {α₀ : σ}
    {directionLaw :
      ℝ → ℝ → ℕ → Measure (EuclideanSpace ℂ (BipIndex p q))}
    {q₀ δ : ℝ → ℝ → ℕ → ℝ}
    {directionSet :
      ℝ → ℝ → ℕ → Set (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundSet : ℝ → ℝ → ℕ → Set (SampleMatrix p q σ)}
    {root : ℝ}
    (hσ : 2 ≤ Fintype.card σ)
    (hDirectionProb :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, IsProbabilityMeasure (directionLaw a slack d))
    (hBlock :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            HermitianBlockSphericalDecompositionIndependence
              (ι := BipIndex p q)
              (κ := PptFactorization.GaussianModel.SampleCoord p q
                (DeletedColumn α₀))
              (Measure.map
                (deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀)
                (μ d))
              (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ))
              (directionLaw a slack d)
              (deletedColumnRightDirectionLaw
                (p := p) (q := q) (σ := σ) α₀))
    (hDirectionMeas :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, MeasurableSet (directionSet a slack d))
    (hBackgroundMeas :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, MeasurableSet (backgroundSet a slack d)) :
    ∀ a : ℝ, root < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (μ d).real
            (sphericalOneColumnFavorableEvent
              (p := p) (q := q) (σ := σ)
              α₀ (q₀ a slack d) (δ a slack d)
              (directionSet a slack d) (backgroundSet a slack d)) =
            (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ)).real
              (betaColumnIntervalSet (q₀ a slack d) (δ a slack d)) *
              (directionLaw a slack d).real (directionSet a slack d) *
                (deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀).real
                  (backgroundSet a slack d) := by
  intro a ha slack hslack
  filter_upwards
    [hDirectionProb a ha slack hslack,
      hBlock a ha slack hslack,
      hDirectionMeas a ha slack hslack,
      hBackgroundMeas a ha slack hslack]
    with d hDir hBlk hDirMeas hBgMeas
  have hI :
      CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence
        (p := p) (q := q) (σ := σ) (μ d) α₀ (directionLaw a slack d) :=
    CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence.of_hermitianBlock_transport_deletedBackground
        (p := p) (q := q) (σ := σ)
        (μ := μ d) (α₀ := α₀)
        (directionLaw := directionLaw a slack d)
        hσ hDir hBlk
  exact
    CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence.favorable_event_probability_eq
        (p := p) (q := q) (σ := σ)
        (I := hI) (q₀ := q₀ a slack d) (δ := δ a slack d)
        (directionSet := directionSet a slack d)
        (backgroundSet := backgroundSet a slack d)
        hDirMeas hBgMeas

set_option linter.unusedSectionVars false in
/-- The same canonical product identity, specialized to the exact `hProduct`
shape of `SpikeLowerBoundInput.of_oneColumn_probability_pipeline`.

Use this theorem when the scalar probability families are definitionally the
canonical probabilities of the mass interval, direction event, deleted
background event, and full favourable column event. -/
theorem oneColumnProbabilityPipeline_hProduct_of_canonical_probabilities
    [Nonempty p] [Nonempty q]
    {μ : ℕ → Measure (SampleMatrix p q σ)} {α₀ : σ}
    {directionLaw :
      ℝ → ℝ → ℕ → Measure (EuclideanSpace ℂ (BipIndex p q))}
    {q₀ δ : ℝ → ℝ → ℕ → ℝ}
    {directionSet :
      ℝ → ℝ → ℕ → Set (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundSet : ℝ → ℝ → ℕ → Set (SampleMatrix p q σ)}
    {root : ℝ}
    (hσ : 2 ≤ Fintype.card σ)
    (hDirectionProb :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, IsProbabilityMeasure (directionLaw a slack d))
    (hBlock :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            HermitianBlockSphericalDecompositionIndependence
              (ι := BipIndex p q)
              (κ := PptFactorization.GaussianModel.SampleCoord p q
                (DeletedColumn α₀))
              (Measure.map
                (deletedColumnBlockVector (p := p) (q := q) (σ := σ) α₀)
                (μ d))
              (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ))
              (directionLaw a slack d)
              (deletedColumnRightDirectionLaw
                (p := p) (q := q) (σ := σ) α₀))
    (hDirectionMeas :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, MeasurableSet (directionSet a slack d))
    (hBackgroundMeas :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, MeasurableSet (backgroundSet a slack d)) :
    ∀ a : ℝ, root < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (μ d).real
              (sphericalOneColumnFavorableEvent
                (p := p) (q := q) (σ := σ)
                α₀ (q₀ a slack d) (δ a slack d)
                (directionSet a slack d) (backgroundSet a slack d)) =
            (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ)).real
                (betaColumnIntervalSet (q₀ a slack d) (δ a slack d)) *
              (directionLaw a slack d).real (directionSet a slack d) *
                (deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀).real
                  (backgroundSet a slack d) :=
  oneColumnFavorableEvent_probability_eq_product_of_hermitianBlock_transport_deletedBackground
    (p := p) (q := q) (σ := σ)
    (μ := μ) (α₀ := α₀) (directionLaw := directionLaw)
    (q₀ := q₀) (δ := δ)
    (directionSet := directionSet) (backgroundSet := backgroundSet)
    (root := root)
    hσ hDirectionProb hBlock hDirectionMeas hBackgroundMeas

/-- The actual column spike matrix:
`S_α(X) = (x_α x_α*)^Γ`.

This is a one-column object.  It is not the projection of `X` onto a
fibre/subspace of sample dimension `s`. -/
noncomputable def columnSpikeMatrix (X : SampleMatrix p q σ) (α₀ : σ) :
    BipMatrix p q :=
  gamma (densityMatrix (sampleColumnPart (p := p) (q := q) (σ := σ) X α₀))

/-- The background matrix obtained by deleting one distinguished sample column. -/
noncomputable def columnBackgroundMatrix (X : SampleMatrix p q σ) (α₀ : σ) :
    BipMatrix p q :=
  gamma (densityMatrix (sampleColumnComplement (p := p) (q := q) (σ := σ) X α₀))

/-- Pure one-column spike contribution to the normalized trace moment. -/
noncomputable def columnSpikeContribution
    (N : ℝ) (k : ℕ) (X : SampleMatrix p q σ) (α₀ : σ) : ℝ :=
  scaledTracePower (p := p) (q := q) N k
    (columnSpikeMatrix (p := p) (q := q) (σ := σ) X α₀)

/-- Pure background contribution after deleting the distinguished column. -/
noncomputable def columnBackgroundContribution
    (N : ℝ) (k : ℕ) (X : SampleMatrix p q σ) (α₀ : σ) : ℝ :=
  scaledTracePower (p := p) (q := q) N k
    (columnBackgroundMatrix (p := p) (q := q) (σ := σ) X α₀)

/-- Exact mixed remainder for the column decomposition.

It is whatever remains after subtracting the pure one-column spike and the
pure deleted-column background from the full trace moment.  The definition is
intentionally exact; no mixed word is thrown away. -/
noncomputable def columnMixedRemainder
    (N : ℝ) (k : ℕ) (X : SampleMatrix p q σ) (α₀ : σ) : ℝ :=
  scaledTracePower (p := p) (q := q) N k (gamma (densityMatrix X)) -
    columnSpikeContribution (p := p) (q := q) (σ := σ) N k X α₀ -
      columnBackgroundContribution (p := p) (q := q) (σ := σ) N k X α₀

/-- Exact full/spike/background/mixed decomposition using one sample column.

This is the lower-bound algebra that replaces any fibre-overlap formulation:
the split comes from one column of the rectangular matrix, and the absence of
cross terms is supplied by `densityMatrix_column_decomposition`. -/
theorem scaledTracePower_column_decomposition
    (N : ℝ) (k : ℕ) (X : SampleMatrix p q σ) (α₀ : σ) :
    scaledTracePower (p := p) (q := q) N k (gamma (densityMatrix X)) =
      columnSpikeContribution (p := p) (q := q) (σ := σ) N k X α₀ +
        columnBackgroundContribution (p := p) (q := q) (σ := σ) N k X α₀ +
          columnMixedRemainder (p := p) (q := q) (σ := σ) N k X α₀ := by
  unfold columnMixedRemainder
  ring

/-- The column decomposition really uses the exact matrix split
`(XX*)^Γ = S_α(X) + B_α(X)`. -/
theorem gamma_densityMatrix_eq_columnSpike_add_background
    (X : SampleMatrix p q σ) (α₀ : σ) :
    gamma (densityMatrix X) =
      columnSpikeMatrix (p := p) (q := q) (σ := σ) X α₀ +
        columnBackgroundMatrix (p := p) (q := q) (σ := σ) X α₀ := by
  simpa [columnSpikeMatrix, columnBackgroundMatrix] using
    gamma_densityMatrix_column_decomposition
      (p := p) (q := q) (σ := σ) X α₀

/-- Deterministic one-column lower-bound inclusion.

If the distinguished column spike supplies `a^k`, the deleted-column
background is typical, the exact mixed remainder is not too negative, and the
mean is close to the limiting centre, then the matrix is in the upper
deviation event.

This theorem is deliberately stated with `columnSpikeContribution`, not with a
fibre-overlap or a projection mass. -/
theorem column_spike_event_deviation_of_background_mixed
    {N a eps mean center errSpike errBg errMix errMean : ℝ}
    {k : ℕ} {X : SampleMatrix p q σ} {α₀ : σ}
    (hSpike :
      a ^ k - errSpike ≤
        columnSpikeContribution (p := p) (q := q) (σ := σ) N k X α₀)
    (hBackground :
      center - errBg ≤
        columnBackgroundContribution (p := p) (q := q) (σ := σ) N k X α₀)
    (hMixed :
      -errMix ≤
        columnMixedRemainder (p := p) (q := q) (σ := σ) N k X α₀)
    (hMean : mean ≤ center + errMean)
    (hBudget : eps + errSpike + errBg + errMix + errMean ≤ a ^ k) :
    eps ≤
      scaledTracePower (p := p) (q := q) N k (gamma (densityMatrix X)) - mean := by
  have hDecomp :=
    scaledTracePower_column_decomposition
      (p := p) (q := q) (σ := σ) N k X α₀
  linarith

/-- Absolute-deviation version of the one-column inclusion. -/
theorem column_spike_event_abs_deviation_of_background_mixed
    {N a eps mean center errSpike errBg errMix errMean : ℝ}
    {k : ℕ} {X : SampleMatrix p q σ} {α₀ : σ}
    (hSpike :
      a ^ k - errSpike ≤
        columnSpikeContribution (p := p) (q := q) (σ := σ) N k X α₀)
    (hBackground :
      center - errBg ≤
        columnBackgroundContribution (p := p) (q := q) (σ := σ) N k X α₀)
    (hMixed :
      -errMix ≤
        columnMixedRemainder (p := p) (q := q) (σ := σ) N k X α₀)
    (hMean : mean ≤ center + errMean)
    (hBudget : eps + errSpike + errBg + errMix + errMean ≤ a ^ k) :
    eps ≤
      |scaledTracePower (p := p) (q := q) N k (gamma (densityMatrix X)) - mean| := by
  have hupper :=
    column_spike_event_deviation_of_background_mixed
      (p := p) (q := q) (σ := σ)
      (N := N) (a := a) (eps := eps) (mean := mean)
      (center := center) (errSpike := errSpike) (errBg := errBg)
      (errMix := errMix) (errMean := errMean) (k := k)
      (X := X) (α₀ := α₀)
      hSpike hBackground hMixed hMean hBudget
  exact hupper.trans (le_abs_self _)

/-- Upper-tail event for the normalized partially-transposed moment:

`F_N(X) - mean ≥ eps`.

This is the target event for the one-column spike lower bound before passing to
absolute deviations. -/
noncomputable def columnMomentUpperTailSet
    (N eps mean : ℝ) (k : ℕ) : Set (SampleMatrix p q σ) :=
  {X | eps ≤
    scaledTracePower (p := p) (q := q) N k (gamma (densityMatrix X)) - mean}

/-- Deterministic certificate set for the one-column upper-tail inclusion.

A matrix belongs to this set if:

* the distinguished-column pure spike contributes at least `a^k - errSpike`;
* the deleted-column background contributes at least `center - errBg`;
* the exact mixed remainder is not below `-errMix`.

The mean and scalar budget conditions are kept as theorem hypotheses because
they are global, not properties of `X`. -/
noncomputable def columnSpikeUpperTailCertificateSet
    (α₀ : σ) (N a center errSpike errBg errMix : ℝ) (k : ℕ) :
    Set (SampleMatrix p q σ) :=
  {X |
    a ^ k - errSpike ≤
      columnSpikeContribution (p := p) (q := q) (σ := σ) N k X α₀ ∧
    center - errBg ≤
      columnBackgroundContribution (p := p) (q := q) (σ := σ) N k X α₀ ∧
    -errMix ≤ columnMixedRemainder (p := p) (q := q) (σ := σ) N k X α₀}

/-- Event carrying exactly the first two one-column coordinates:

* the distinguished column mass lies in the Beta interval;
* the distinguished column direction lies in the chosen cap/direction set.

This is the deterministic domain for the pure-spike lower bound. -/
noncomputable def columnMassCapEvent
    (α₀ : σ) (q₀ δ : ℝ)
    (directionSet : Set (EuclideanSpace ℂ (BipIndex p q))) :
    Set (SampleMatrix p q σ) :=
  {X |
    sampleColumnMass (p := p) (q := q) (σ := σ) X α₀ ∈
      betaColumnIntervalSet q₀ δ ∧
    sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀ ∈ directionSet}

/-- Certificate set for the pure one-column spike lower bound. -/
noncomputable def columnPureSpikeLowerBoundSet
    (α₀ : σ) (N a errSpike : ℝ) (k : ℕ) :
    Set (SampleMatrix p q σ) :=
  {X |
    a ^ k - errSpike ≤
      columnSpikeContribution (p := p) (q := q) (σ := σ) N k X α₀}

/-- Certificate set for the deleted-column background lower bound. -/
noncomputable def columnBackgroundContributionLowerBoundSet
    (α₀ : σ) (N center errBg : ℝ) (k : ℕ) :
    Set (SampleMatrix p q σ) :=
  {X |
    center - errBg ≤
      columnBackgroundContribution (p := p) (q := q) (σ := σ) N k X α₀}

/-- Certificate set for the mixed-remainder lower bound. -/
noncomputable def columnMixedRemainderLowerBoundSet
    (α₀ : σ) (N errMix : ℝ) (k : ℕ) :
    Set (SampleMatrix p q σ) :=
  {X |
    -errMix ≤ columnMixedRemainder (p := p) (q := q) (σ := σ) N k X α₀}

/-- Absolute-value envelope for the exact mixed remainder.  This is stronger than
the lower-bound certificate and is the natural output of the word-by-word
Schatten/Hölder estimates. -/
noncomputable def columnMixedRemainderEnvelopeSet
    (α₀ : σ) (N errMix : ℝ) (k : ℕ) :
    Set (SampleMatrix p q σ) :=
  {X |
    |columnMixedRemainder (p := p) (q := q) (σ := σ) N k X α₀| ≤ errMix}

/-- Scalar monotonicity for the pure-spike error budget.  If a pure-spike
certificate holds with a smaller error, then it also holds with any larger
error. -/
theorem columnPureSpikeLowerBoundSet_mono_error
    {α₀ : σ} {N a errSmall errBig : ℝ} {k : ℕ}
    (herr : errSmall ≤ errBig) :
    columnPureSpikeLowerBoundSet
        (p := p) (q := q) (σ := σ) α₀ N a errSmall k ⊆
      columnPureSpikeLowerBoundSet
        (p := p) (q := q) (σ := σ) α₀ N a errBig k := by
  intro X hX
  dsimp [columnPureSpikeLowerBoundSet] at hX ⊢
  linarith

/-- Scalar monotonicity for the background error budget. -/
theorem columnBackgroundContributionLowerBoundSet_mono_error
    {α₀ : σ} {N center errSmall errBig : ℝ} {k : ℕ}
    (herr : errSmall ≤ errBig) :
    columnBackgroundContributionLowerBoundSet
        (p := p) (q := q) (σ := σ) α₀ N center errSmall k ⊆
      columnBackgroundContributionLowerBoundSet
        (p := p) (q := q) (σ := σ) α₀ N center errBig k := by
  intro X hX
  dsimp [columnBackgroundContributionLowerBoundSet] at hX ⊢
  linarith

/-- Scalar monotonicity for the mixed-remainder lower-bound error budget. -/
theorem columnMixedRemainderLowerBoundSet_mono_error
    {α₀ : σ} {N errSmall errBig : ℝ} {k : ℕ}
    (herr : errSmall ≤ errBig) :
    columnMixedRemainderLowerBoundSet
        (p := p) (q := q) (σ := σ) α₀ N errSmall k ⊆
      columnMixedRemainderLowerBoundSet
        (p := p) (q := q) (σ := σ) α₀ N errBig k := by
  intro X hX
  dsimp [columnMixedRemainderLowerBoundSet] at hX ⊢
  linarith

/-- If two scalar error sequences are eventually bounded by half of a target
error sequence, then their sum is eventually bounded by that target sequence. -/
theorem eventual_add_errors_le_of_eventual_half_bounds
    {e₁ e₂ e : ℕ → ℝ}
    (h₁ : ∀ᶠ d in atTop, e₁ d ≤ e d / 2)
    (h₂ : ∀ᶠ d in atTop, e₂ d ≤ e d / 2) :
    ∀ᶠ d in atTop, e₁ d + e₂ d ≤ e d := by
  filter_upwards [h₁, h₂] with d h₁d h₂d
  linarith

/-- Eventual scalar budget for the pure-spike gate:

`errProfile + errTransfer ≤ errSpike`. -/
theorem eventual_pureSpike_error_budget_of_half_bounds
    {errProfile errTransfer errSpike : ℕ → ℝ}
    (hProfile :
      ∀ᶠ d in atTop, errProfile d ≤ errSpike d / 2)
    (hTransfer :
      ∀ᶠ d in atTop, errTransfer d ≤ errSpike d / 2) :
    ∀ᶠ d in atTop, errProfile d + errTransfer d ≤ errSpike d :=
  eventual_add_errors_le_of_eventual_half_bounds
    (e₁ := errProfile) (e₂ := errTransfer) (e := errSpike)
    hProfile hTransfer

/-- Eventual scalar budget for the background gate:

`τ + errScale ≤ errBg`. -/
theorem eventual_background_error_budget_of_half_bounds
    {τ errScale errBg : ℕ → ℝ}
    (hTau : ∀ᶠ d in atTop, τ d ≤ errBg d / 2)
    (hScale : ∀ᶠ d in atTop, errScale d ≤ errBg d / 2) :
    ∀ᶠ d in atTop, τ d + errScale d ≤ errBg d :=
  eventual_add_errors_le_of_eventual_half_bounds
    (e₁ := τ) (e₂ := errScale) (e := errBg) hTau hScale

/-- If two scalar error sequences are `o(1)` in eventual epsilon form, then their
sum is eventually below any fixed positive budget. -/
theorem eventual_add_errors_le_of_eventual_small
    {e₁ e₂ : ℕ → ℝ} {budget : ℝ}
    (hbudget : 0 < budget)
    (h₁ : ∀ η : ℝ, 0 < η → ∀ᶠ d in atTop, e₁ d ≤ η)
    (h₂ : ∀ η : ℝ, 0 < η → ∀ᶠ d in atTop, e₂ d ≤ η) :
    ∀ᶠ d in atTop, e₁ d + e₂ d ≤ budget := by
  have hhalf : 0 < budget / 2 := by positivity
  filter_upwards [h₁ (budget / 2) hhalf, h₂ (budget / 2) hhalf]
    with d h₁d h₂d
  linarith

/-- Eventual scalar budget for the final one-column deterministic inclusion.

If the four error terms are all `o(1)` and `eps < a^k`, then eventually

`eps + errSpike + errBg + errMix + errMean ≤ a^k`. -/
theorem eventual_column_spike_error_budget_of_eventual_small
    {errSpike errBg errMix errMean : ℕ → ℝ}
    {eps a : ℝ} {k : ℕ}
    (hgap : eps < a ^ k)
    (hSpike :
      ∀ η : ℝ, 0 < η → ∀ᶠ d in atTop, errSpike d ≤ η)
    (hBg :
      ∀ η : ℝ, 0 < η → ∀ᶠ d in atTop, errBg d ≤ η)
    (hMix :
      ∀ η : ℝ, 0 < η → ∀ᶠ d in atTop, errMix d ≤ η)
    (hMean :
      ∀ η : ℝ, 0 < η → ∀ᶠ d in atTop, errMean d ≤ η) :
    ∀ᶠ d in atTop,
      eps + errSpike d + errBg d + errMix d + errMean d ≤ a ^ k := by
  let budget : ℝ := (a ^ k - eps) / 4
  have hbudget : 0 < budget := by
    dsimp [budget]
    linarith
  filter_upwards
    [hSpike budget hbudget, hBg budget hbudget,
      hMix budget hbudget, hMean budget hbudget]
    with d hSd hBd hMd hMeand
  dsimp [budget] at hSd hBd hMd hMeand
  linarith

/-- A symmetric absolute scalar estimate implies the one-sided mean estimate used
in the deterministic certificate. -/
theorem eventual_mean_le_center_add_error_of_abs_bound
    {mean center errMean : ℕ → ℝ}
    (hAbs : ∀ᶠ d in atTop, |mean d - center d| ≤ errMean d) :
    ∀ᶠ d in atTop, mean d ≤ center d + errMean d := by
  filter_upwards [hAbs] with d hd
  have hupper := (abs_le.mp hd).2
  linarith

/-- The normalized pure-spike profile associated with a mass `R` and a column
direction `u`.

This isolates the analytic cap calculation from the actual column matrix.  A
separate transfer hypothesis identifies this profile with, or bounds it by, the
concrete one-column contribution. -/
noncomputable def columnDirectionSpikeProfile
    (N : ℝ) (k : ℕ) (R : ℝ)
    (u : EuclideanSpace ℂ (BipIndex p q)) : ℝ :=
  pureSpikeContribution (p := p) (q := q) N k R
    (rankOneProjectorGamma (p := p) (q := q) u)

set_option linter.unusedSectionVars false in
/-- The density matrix of one sample column is exactly the rank-one projector
onto the corresponding column vector. -/
theorem densityMatrix_sampleColumnPart_eq_rankOneProjector_columnVector
    [DecidableEq σ] {α₀ : σ} (X : SampleMatrix p q σ) :
    densityMatrix (p := p) (q := q) (σ := σ)
        (sampleColumnPart (p := p) (q := q) (σ := σ) X α₀) =
      rankOneProjector (p := p) (q := q)
        (sampleColumnVector (p := p) (q := q) (σ := σ) X α₀) := by
  ext i j
  simp [densityMatrix, sampleColumnPart, sampleColumnVector,
    PptFactorization.GaussianModel.columnVector, rankOneProjector,
    Matrix.mul_apply]

set_option linter.unusedSectionVars false in
/-- Normalizing a nonzero vector and then multiplying its rank-one projector by
the squared norm recovers the original rank-one projector.  The total inverse
convention makes the zero-vector case true as well. -/
theorem norm_sq_smul_rankOneProjector_direction_eq_rankOneProjector
    (v : EuclideanSpace ℂ (BipIndex p q)) :
    ((‖v‖ ^ 2 : ℝ) : ℂ) •
        rankOneProjector (p := p) (q := q)
          (((‖v‖)⁻¹ : ℂ) • v) =
      rankOneProjector (p := p) (q := q) v := by
  ext i j
  by_cases hv : ‖v‖ = 0
  · have hz : v = 0 := norm_eq_zero.mp hv
    simp [rankOneProjector, hz]
  · simp [rankOneProjector, smul_eq_mul]
    field_simp [hv]

set_option linter.unusedSectionVars false in
/-- Concrete one-column density matrix in mass-direction coordinates. -/
theorem densityMatrix_sampleColumnPart_eq_mass_smul_rankOneProjector_direction
    [DecidableEq σ] {α₀ : σ} (X : SampleMatrix p q σ) :
    densityMatrix (p := p) (q := q) (σ := σ)
        (sampleColumnPart (p := p) (q := q) (σ := σ) X α₀) =
      ((sampleColumnMass (p := p) (q := q) (σ := σ) X α₀ : ℝ) : ℂ) •
        rankOneProjector (p := p) (q := q)
          (sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀) := by
  rw [densityMatrix_sampleColumnPart_eq_rankOneProjector_columnVector
    (p := p) (q := q) (σ := σ) (α₀ := α₀) X]
  rw [← norm_sq_smul_rankOneProjector_direction_eq_rankOneProjector
    (p := p) (q := q)
    (v := sampleColumnVector (p := p) (q := q) (σ := σ) X α₀)]
  simp [sampleColumnMass, sampleColumnDirection,
    frobeniusNorm_sampleColumnPart_eq_norm_sampleColumnVector
      (p := p) (q := q) (σ := σ) X α₀]

set_option linter.unusedSectionVars false in
/-- The one-column spike matrix is exactly the partially-transposed rank-one
projector associated with the column direction, scaled by the column mass. -/
theorem columnSpikeMatrix_eq_mass_smul_rankOneProjectorGamma_direction
    [DecidableEq σ] {α₀ : σ} (X : SampleMatrix p q σ) :
    columnSpikeMatrix (p := p) (q := q) (σ := σ) X α₀ =
      ((sampleColumnMass (p := p) (q := q) (σ := σ) X α₀ : ℝ) : ℂ) •
        rankOneProjectorGamma (p := p) (q := q)
          (sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀) := by
  unfold columnSpikeMatrix rankOneProjectorGamma
  rw [densityMatrix_sampleColumnPart_eq_mass_smul_rankOneProjector_direction
    (p := p) (q := q) (σ := σ) (α₀ := α₀) X]
  ext i j
  simp [gamma, Matrix.partialTranspose]

/-- Scaling a matrix by a real scalar pulls out of the normalized trace power
as the corresponding pure-spike contribution. -/
theorem scaledTracePower_real_smul_eq_pureSpikeContribution
    (N R : ℝ) (k : ℕ) (S : BipMatrix p q) :
    scaledTracePower (p := p) (q := q) N k ((R : ℂ) • S) =
      pureSpikeContribution (p := p) (q := q) N k R S := by
  unfold scaledTracePower pureSpikeContribution
  rw [smul_pow, Matrix.trace_smul]
  have hpow : (R : ℂ) ^ k = ((R ^ k : ℝ) : ℂ) :=
    (Complex.ofReal_pow R k).symm
  rw [hpow]
  change
    N ^ (k - 1) * ((((R ^ k : ℝ) : ℂ) * Matrix.trace (S ^ k)).re) =
      N ^ (k - 1) * R ^ k * (Matrix.trace (S ^ k)).re
  rw [Complex.re_ofReal_mul]
  ring

set_option linter.unusedSectionVars false in
/-- Exact closure of the pure-spike transfer block: the abstract directional
profile is the concrete one-column spike contribution. -/
theorem columnSpikeContribution_eq_directionSpikeProfile
    [DecidableEq σ] {α₀ : σ} (N : ℝ) (k : ℕ)
    (X : SampleMatrix p q σ) :
    columnSpikeContribution (p := p) (q := q) (σ := σ) N k X α₀ =
      columnDirectionSpikeProfile (p := p) (q := q) N k
        (sampleColumnMass (p := p) (q := q) (σ := σ) X α₀)
        (sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀) := by
  unfold columnSpikeContribution columnDirectionSpikeProfile
  rw [columnSpikeMatrix_eq_mass_smul_rankOneProjectorGamma_direction
    (p := p) (q := q) (σ := σ) (α₀ := α₀) X]
  exact
    scaledTracePower_real_smul_eq_pureSpikeContribution
      (p := p) (q := q) N
      (sampleColumnMass (p := p) (q := q) (σ := σ) X α₀) k
      (rankOneProjectorGamma (p := p) (q := q)
        (sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀))

set_option linter.unusedSectionVars false in
/-- No-input pointwise pure-spike transfer, with zero transfer loss. -/
theorem columnSpikeContribution_transfer_noError
    [DecidableEq σ] {α₀ : σ} {N : ℝ} {k : ℕ}
    (X : SampleMatrix p q σ) :
    columnDirectionSpikeProfile (p := p) (q := q) N k
        (sampleColumnMass (p := p) (q := q) (σ := σ) X α₀)
        (sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀) - 0 ≤
      columnSpikeContribution (p := p) (q := q) (σ := σ) N k X α₀ := by
  rw [columnSpikeContribution_eq_directionSpikeProfile
    (p := p) (q := q) (σ := σ) (α₀ := α₀) N k X]
  simp

/-- Pointwise pure-spike implication:

mass interval + direction cap + profile lower bound + transfer to the concrete
column spike contribution imply the pure-spike certificate. -/
theorem columnSpikeContribution_lower_of_mass_interval_and_cap
    {α₀ : σ} {N a errProfile errTransfer q₀ δ : ℝ} {k : ℕ}
    {X : SampleMatrix p q σ}
    {directionSet : Set (EuclideanSpace ℂ (BipIndex p q))}
    (hMass :
      sampleColumnMass (p := p) (q := q) (σ := σ) X α₀ ∈
        betaColumnIntervalSet q₀ δ)
    (hCap :
      sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀ ∈ directionSet)
    (hProfile :
      ∀ R : ℝ, ∀ u : EuclideanSpace ℂ (BipIndex p q),
        R ∈ betaColumnIntervalSet q₀ δ →
        u ∈ directionSet →
        a ^ k - errProfile ≤
          columnDirectionSpikeProfile (p := p) (q := q) N k R u)
    (hTransfer :
      columnDirectionSpikeProfile (p := p) (q := q) N k
          (sampleColumnMass (p := p) (q := q) (σ := σ) X α₀)
          (sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀) -
          errTransfer ≤
        columnSpikeContribution (p := p) (q := q) (σ := σ) N k X α₀) :
    a ^ k - (errProfile + errTransfer) ≤
      columnSpikeContribution (p := p) (q := q) (σ := σ) N k X α₀ := by
  have hProfileX :=
    hProfile
      (sampleColumnMass (p := p) (q := q) (σ := σ) X α₀)
      (sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀)
      hMass hCap
  linarith

/-- Set-level pure-spike implication:

`columnMassCapEvent` is included in the pure-spike lower-bound certificate once
the profile lower bound and concrete transfer are available pointwise. -/
theorem columnMassCapEvent_subset_pureSpikeLowerBoundSet
    {α₀ : σ} {N a errProfile errTransfer q₀ δ : ℝ} {k : ℕ}
    {directionSet : Set (EuclideanSpace ℂ (BipIndex p q))}
    (hProfile :
      ∀ R : ℝ, ∀ u : EuclideanSpace ℂ (BipIndex p q),
        R ∈ betaColumnIntervalSet q₀ δ →
        u ∈ directionSet →
        a ^ k - errProfile ≤
          columnDirectionSpikeProfile (p := p) (q := q) N k R u)
    (hTransfer :
      ∀ X : SampleMatrix p q σ,
        X ∈ columnMassCapEvent
          (p := p) (q := q) (σ := σ) α₀ q₀ δ directionSet →
        columnDirectionSpikeProfile (p := p) (q := q) N k
            (sampleColumnMass (p := p) (q := q) (σ := σ) X α₀)
            (sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀) -
            errTransfer ≤
          columnSpikeContribution (p := p) (q := q) (σ := σ) N k X α₀) :
    columnMassCapEvent (p := p) (q := q) (σ := σ) α₀ q₀ δ directionSet ⊆
      columnPureSpikeLowerBoundSet
        (p := p) (q := q) (σ := σ) α₀ N a
        (errProfile + errTransfer) k := by
  intro X hX
  exact
    columnSpikeContribution_lower_of_mass_interval_and_cap
      (p := p) (q := q) (σ := σ)
      (α₀ := α₀) (N := N) (a := a)
      (errProfile := errProfile) (errTransfer := errTransfer)
      (q₀ := q₀) (δ := δ) (k := k) (X := X)
      (directionSet := directionSet)
      hX.1 hX.2 hProfile (hTransfer X hX)

/-- Pure-spike implication with the scalar error budget separated.

The analytic/profile step produces the error `errProfile + errTransfer`; the
separate scalar hypothesis `errProfile + errTransfer ≤ errSpike` widens it to
the certificate error `errSpike`. -/
theorem columnMassCapEvent_subset_pureSpikeLowerBoundSet_of_error_budget
    {α₀ : σ} {N a errProfile errTransfer errSpike q₀ δ : ℝ} {k : ℕ}
    {directionSet : Set (EuclideanSpace ℂ (BipIndex p q))}
    (hProfile :
      ∀ R : ℝ, ∀ u : EuclideanSpace ℂ (BipIndex p q),
        R ∈ betaColumnIntervalSet q₀ δ →
        u ∈ directionSet →
        a ^ k - errProfile ≤
          columnDirectionSpikeProfile (p := p) (q := q) N k R u)
    (hTransfer :
      ∀ X : SampleMatrix p q σ,
        X ∈ columnMassCapEvent
          (p := p) (q := q) (σ := σ) α₀ q₀ δ directionSet →
        columnDirectionSpikeProfile (p := p) (q := q) N k
            (sampleColumnMass (p := p) (q := q) (σ := σ) X α₀)
            (sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀) -
            errTransfer ≤
          columnSpikeContribution (p := p) (q := q) (σ := σ) N k X α₀)
    (hError : errProfile + errTransfer ≤ errSpike) :
    columnMassCapEvent (p := p) (q := q) (σ := σ) α₀ q₀ δ directionSet ⊆
      columnPureSpikeLowerBoundSet
        (p := p) (q := q) (σ := σ) α₀ N a errSpike k :=
  Set.Subset.trans
    (columnMassCapEvent_subset_pureSpikeLowerBoundSet
      (p := p) (q := q) (σ := σ)
      (α₀ := α₀) (N := N) (a := a)
      (errProfile := errProfile) (errTransfer := errTransfer)
      (q₀ := q₀) (δ := δ) (k := k) (directionSet := directionSet)
      hProfile hTransfer)
    (columnPureSpikeLowerBoundSet_mono_error
      (p := p) (q := q) (σ := σ)
      (α₀ := α₀) (N := N) (a := a)
      (errSmall := errProfile + errTransfer) (errBig := errSpike)
      (k := k) hError)

set_option linter.unusedSectionVars false in
/-- Pure-spike inclusion with the transfer block closed by the exact
mass-direction identity. -/
theorem columnMassCapEvent_subset_pureSpikeLowerBoundSet_noInputTransfer
    [DecidableEq σ]
    {α₀ : σ} {N a errProfile errSpike q₀ δ : ℝ} {k : ℕ}
    {directionSet : Set (EuclideanSpace ℂ (BipIndex p q))}
    (hProfile :
      ∀ R : ℝ, ∀ u : EuclideanSpace ℂ (BipIndex p q),
        R ∈ betaColumnIntervalSet q₀ δ →
        u ∈ directionSet →
        a ^ k - errProfile ≤
          columnDirectionSpikeProfile (p := p) (q := q) N k R u)
    (hError : errProfile + 0 ≤ errSpike) :
    columnMassCapEvent (p := p) (q := q) (σ := σ) α₀ q₀ δ directionSet ⊆
      columnPureSpikeLowerBoundSet
        (p := p) (q := q) (σ := σ) α₀ N a errSpike k :=
  columnMassCapEvent_subset_pureSpikeLowerBoundSet_of_error_budget
    (p := p) (q := q) (σ := σ)
    (α₀ := α₀) (N := N) (a := a)
    (errProfile := errProfile) (errTransfer := 0)
    (errSpike := errSpike) (q₀ := q₀) (δ := δ) (k := k)
    (directionSet := directionSet)
    hProfile
    (fun X _hX =>
      columnSpikeContribution_transfer_noError
        (p := p) (q := q) (σ := σ) (α₀ := α₀)
        (N := N) (k := k) X)
    hError

/-- The normalized deleted-column background event associated with a chosen
background set. -/
noncomputable def normalizedDeletedBackgroundEvent
    (α₀ : σ) (backgroundSet : Set (SampleMatrix p q σ)) :
    Set (SampleMatrix p q σ) :=
  {X |
    sampleColumnComplementNormalized (p := p) (q := q) (σ := σ) X α₀ ∈
      backgroundSet}

/-- Set-level background implication:

membership of the normalized deleted matrix in the background-typical set implies
the background contribution lower-bound certificate, once the concrete transfer
from normalized background typicality to the unnormalized background contribution
has been supplied. -/
theorem normalizedDeletedBackgroundEvent_subset_backgroundContributionLowerBoundSet
    {α₀ : σ} {backgroundSet : Set (SampleMatrix p q σ)}
    {N center errBg : ℝ} {k : ℕ}
    (hBackground :
      ∀ X : SampleMatrix p q σ,
        sampleColumnComplementNormalized (p := p) (q := q) (σ := σ) X α₀ ∈
          backgroundSet →
        center - errBg ≤
          columnBackgroundContribution (p := p) (q := q) (σ := σ) N k X α₀) :
    normalizedDeletedBackgroundEvent
        (p := p) (q := q) (σ := σ) α₀ backgroundSet ⊆
      columnBackgroundContributionLowerBoundSet
        (p := p) (q := q) (σ := σ) α₀ N center errBg k := by
  intro X hX
  exact hBackground X hX

/-- Pointwise mixed implication: an absolute envelope on the exact mixed
remainder implies the lower-bound certificate for that mixed term. -/
theorem columnMixedRemainder_lower_of_abs_envelope
    {α₀ : σ} {N errMix : ℝ} {k : ℕ} {X : SampleMatrix p q σ}
    (hEnvelope :
      |columnMixedRemainder (p := p) (q := q) (σ := σ) N k X α₀| ≤ errMix) :
    -errMix ≤ columnMixedRemainder (p := p) (q := q) (σ := σ) N k X α₀ :=
  (abs_le.mp hEnvelope).1

/-- Set-level mixed implication:

the word-by-word mixed-remainder envelope set is included in the mixed lower-bound
certificate set. -/
theorem columnMixedRemainderEnvelopeSet_subset_lowerBoundSet
    {α₀ : σ} {N errMix : ℝ} {k : ℕ} :
    columnMixedRemainderEnvelopeSet
        (p := p) (q := q) (σ := σ) α₀ N errMix k ⊆
      columnMixedRemainderLowerBoundSet
        (p := p) (q := q) (σ := σ) α₀ N errMix k := by
  intro X hX
  exact
    columnMixedRemainder_lower_of_abs_envelope
      (p := p) (q := q) (σ := σ)
      (α₀ := α₀) (N := N) (errMix := errMix) (k := k)
      (X := X) hX

/-- Pointwise word-envelope estimates produce the mixed-envelope set used by
the deterministic inclusion. -/
theorem sphericalOneColumnFavorableEvent_subset_mixedEnvelopeSet_of_pointwise
    {α₀ : σ}
    {q₀ δ N errMix : ℝ} {k : ℕ}
    {directionSet : Set (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundSet : Set (SampleMatrix p q σ)}
    (hMixed :
      ∀ X : SampleMatrix p q σ,
        X ∈ sphericalOneColumnFavorableEvent
          (p := p) (q := q) (σ := σ) α₀ q₀ δ directionSet backgroundSet →
        |columnMixedRemainder (p := p) (q := q) (σ := σ) N k X α₀| ≤
          errMix) :
    sphericalOneColumnFavorableEvent
        (p := p) (q := q) (σ := σ) α₀ q₀ δ directionSet backgroundSet ⊆
      columnMixedRemainderEnvelopeSet
        (p := p) (q := q) (σ := σ) α₀ N errMix k := by
  intro X hX
  exact hMixed X hX

/-- Direct three-block deterministic inclusion into the upper-tail event.

This is the smallest event-level certificate for the one-column spike lower
bound.  It separates the deterministic proof into exactly the three reusable
blocks:

* the favourable event implies the pure one-column spike lower bound;
* the favourable event implies the deleted-background lower bound;
* the favourable event implies the mixed-remainder absolute envelope.

The last block is intentionally an absolute envelope; the one-sided mixed lower
bound follows by `columnMixedRemainderEnvelopeSet_subset_lowerBoundSet`.
-/
theorem sphericalOneColumnFavorableEvent_subset_upperTailSet_of_three_blocks
    {α₀ : σ}
    {q₀ δ N a eps mean center errSpike errBg errMix errMean : ℝ}
    {k : ℕ}
    {directionSet : Set (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundSet : Set (SampleMatrix p q σ)}
    (hPure :
      sphericalOneColumnFavorableEvent
          (p := p) (q := q) (σ := σ) α₀ q₀ δ directionSet backgroundSet ⊆
        columnPureSpikeLowerBoundSet
          (p := p) (q := q) (σ := σ) α₀ N a errSpike k)
    (hBackground :
      sphericalOneColumnFavorableEvent
          (p := p) (q := q) (σ := σ) α₀ q₀ δ directionSet backgroundSet ⊆
        columnBackgroundContributionLowerBoundSet
          (p := p) (q := q) (σ := σ) α₀ N center errBg k)
    (hMixedEnvelope :
      sphericalOneColumnFavorableEvent
          (p := p) (q := q) (σ := σ) α₀ q₀ δ directionSet backgroundSet ⊆
        columnMixedRemainderEnvelopeSet
          (p := p) (q := q) (σ := σ) α₀ N errMix k)
    (hMean : mean ≤ center + errMean)
    (hBudget : eps + errSpike + errBg + errMix + errMean ≤ a ^ k) :
    sphericalOneColumnFavorableEvent
        (p := p) (q := q) (σ := σ) α₀ q₀ δ directionSet backgroundSet ⊆
      columnMomentUpperTailSet (p := p) (q := q) (σ := σ) N eps mean k := by
  intro X hX
  exact
    column_spike_event_deviation_of_background_mixed
      (p := p) (q := q) (σ := σ)
      (N := N) (a := a) (eps := eps) (mean := mean)
      (center := center) (errSpike := errSpike) (errBg := errBg)
      (errMix := errMix) (errMean := errMean) (k := k)
      (X := X) (α₀ := α₀)
      (hPure hX) (hBackground hX)
      (columnMixedRemainderEnvelopeSet_subset_lowerBoundSet
        (p := p) (q := q) (σ := σ)
        (α₀ := α₀) (N := N) (errMix := errMix) (k := k)
        (hMixedEnvelope hX))
      hMean hBudget

/-- Assemble the three deterministic component implications into the certificate
set used by the one-column lower-bound inclusion.

This is the non-opaque replacement for a single monolithic `hE`: the favourable
event supplies

* mass interval + cap, hence the pure-spike lower bound;
* normalized deleted-background typicality, hence the background lower bound;
* a mixed-remainder envelope, hence the mixed lower bound. -/
theorem sphericalOneColumnFavorableEvent_subset_certificate_of_three_implications
    {α₀ : σ} {q₀ δ N a center errSpike errBg errMix : ℝ} {k : ℕ}
    {directionSet : Set (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundSet : Set (SampleMatrix p q σ)}
    (hPure :
      columnMassCapEvent (p := p) (q := q) (σ := σ)
          α₀ q₀ δ directionSet ⊆
        columnPureSpikeLowerBoundSet
          (p := p) (q := q) (σ := σ) α₀ N a errSpike k)
    (hBackground :
      normalizedDeletedBackgroundEvent
          (p := p) (q := q) (σ := σ) α₀ backgroundSet ⊆
        columnBackgroundContributionLowerBoundSet
          (p := p) (q := q) (σ := σ) α₀ N center errBg k)
    (hMixedEnvelope :
      sphericalOneColumnFavorableEvent
          (p := p) (q := q) (σ := σ) α₀ q₀ δ directionSet backgroundSet ⊆
        columnMixedRemainderEnvelopeSet
          (p := p) (q := q) (σ := σ) α₀ N errMix k) :
    sphericalOneColumnFavorableEvent
        (p := p) (q := q) (σ := σ) α₀ q₀ δ directionSet backgroundSet ⊆
      columnSpikeUpperTailCertificateSet
        (p := p) (q := q) (σ := σ) α₀ N a center errSpike errBg errMix k := by
  intro X hX
  rcases hX with ⟨hMass, hDirection, hBackgroundTypical⟩
  refine ⟨?_, ?_, ?_⟩
  · exact hPure ⟨hMass, hDirection⟩
  · exact hBackground hBackgroundTypical
  · exact
      columnMixedRemainderEnvelopeSet_subset_lowerBoundSet
        (p := p) (q := q) (σ := σ)
        (α₀ := α₀) (N := N) (errMix := errMix) (k := k)
        (hMixedEnvelope ⟨hMass, hDirection, hBackgroundTypical⟩)

/-- The deterministic certificate set is included in the upper-tail event.

This is the set-level form of `column_spike_event_deviation_of_background_mixed`.
It is the exact deterministic inclusion needed before comparing probabilities. -/
theorem columnSpikeUpperTailCertificateSet_subset_upperTailSet
    {α₀ : σ} {N a eps mean center errSpike errBg errMix errMean : ℝ}
    {k : ℕ}
    (hMean : mean ≤ center + errMean)
    (hBudget : eps + errSpike + errBg + errMix + errMean ≤ a ^ k) :
    columnSpikeUpperTailCertificateSet
        (p := p) (q := q) (σ := σ)
        α₀ N a center errSpike errBg errMix k ⊆
      columnMomentUpperTailSet (p := p) (q := q) (σ := σ) N eps mean k := by
  intro X hX
  rcases hX with ⟨hSpike, hBackground, hMixed⟩
  exact
    column_spike_event_deviation_of_background_mixed
      (p := p) (q := q) (σ := σ)
      (N := N) (a := a) (eps := eps) (mean := mean)
      (center := center) (errSpike := errSpike) (errBg := errBg)
      (errMix := errMix) (errMean := errMean) (k := k)
      (X := X) (α₀ := α₀)
      hSpike hBackground hMixed hMean hBudget

/-- Any favourable event contained in the deterministic certificate set is
therefore contained in the upper-tail event. -/
theorem subset_columnMomentUpperTailSet_of_subset_certificate
    {E : Set (SampleMatrix p q σ)}
    {α₀ : σ} {N a eps mean center errSpike errBg errMix errMean : ℝ}
    {k : ℕ}
    (hE :
      E ⊆ columnSpikeUpperTailCertificateSet
        (p := p) (q := q) (σ := σ)
        α₀ N a center errSpike errBg errMix k)
    (hMean : mean ≤ center + errMean)
    (hBudget : eps + errSpike + errBg + errMix + errMean ≤ a ^ k) :
    E ⊆ columnMomentUpperTailSet (p := p) (q := q) (σ := σ) N eps mean k :=
  Set.Subset.trans hE
    (columnSpikeUpperTailCertificateSet_subset_upperTailSet
      (p := p) (q := q) (σ := σ)
      (α₀ := α₀) (N := N) (a := a) (eps := eps) (mean := mean)
      (center := center) (errSpike := errSpike) (errBg := errBg)
      (errMix := errMix) (errMean := errMean) (k := k)
      hMean hBudget)

/-- Probability comparison induced by the deterministic upper-tail inclusion.

This is the form used to supply the lower-bound pipeline hypothesis
`columnProb ≤ targetProb`: if `columnProb` is the probability of the favourable
event and `targetProb` is the probability of the upper-tail event, the
deterministic inclusion gives the scalar inequality. -/
theorem columnProb_le_upperTailProb_of_subset_certificate
    [MeasurableSpace (SampleMatrix p q σ)]
    {μ : Measure (SampleMatrix p q σ)}
    [IsFiniteMeasure μ]
    {E : Set (SampleMatrix p q σ)}
    {columnProb targetProb : ℝ}
    {α₀ : σ} {N a eps mean center errSpike errBg errMix errMean : ℝ}
    {k : ℕ}
    (hColumnProb : columnProb = μ.real E)
    (hTargetProb :
      targetProb =
        μ.real
          (columnMomentUpperTailSet
            (p := p) (q := q) (σ := σ) N eps mean k))
    (hE :
      E ⊆ columnSpikeUpperTailCertificateSet
        (p := p) (q := q) (σ := σ)
        α₀ N a center errSpike errBg errMix k)
    (hMean : mean ≤ center + errMean)
    (hBudget : eps + errSpike + errBg + errMix + errMean ≤ a ^ k) :
    columnProb ≤ targetProb := by
  rw [hColumnProb, hTargetProb]
  exact
    measureReal_mono
      (subset_columnMomentUpperTailSet_of_subset_certificate
        (p := p) (q := q) (σ := σ)
        (E := E) (α₀ := α₀) (N := N) (a := a) (eps := eps)
        (mean := mean) (center := center) (errSpike := errSpike)
        (errBg := errBg) (errMix := errMix) (errMean := errMean)
        (k := k)
        hE hMean hBudget)
      (h₂ := (measure_lt_top μ _).ne)

/-- Eventual sequence form of the deterministic inclusion into the upper-tail
event. -/
theorem eventual_columnProb_le_upperTailProb_of_subset_certificate
    [MeasurableSpace (SampleMatrix p q σ)]
    {μ : ℕ → Measure (SampleMatrix p q σ)}
    {E : ℕ → Set (SampleMatrix p q σ)}
    {columnProb targetProb N a eps mean center errSpike errBg errMix errMean :
      ℕ → ℝ}
    {α₀ : σ} {k : ℕ}
    (hFinite : ∀ᶠ d in atTop, IsFiniteMeasure (μ d))
    (hColumnProb : ∀ᶠ d in atTop, columnProb d = (μ d).real (E d))
    (hTargetProb :
      ∀ᶠ d in atTop,
        targetProb d =
          (μ d).real
            (columnMomentUpperTailSet
              (p := p) (q := q) (σ := σ) (N d) (eps d) (mean d) k))
    (hE :
      ∀ᶠ d in atTop,
        E d ⊆ columnSpikeUpperTailCertificateSet
          (p := p) (q := q) (σ := σ)
          α₀ (N d) (a d) (center d)
          (errSpike d) (errBg d) (errMix d) k)
    (hMean : ∀ᶠ d in atTop, mean d ≤ center d + errMean d)
    (hBudget :
      ∀ᶠ d in atTop,
        eps d + errSpike d + errBg d + errMix d + errMean d ≤ a d ^ k) :
    ∀ᶠ d in atTop, columnProb d ≤ targetProb d := by
  filter_upwards [hFinite, hColumnProb, hTargetProb, hE, hMean, hBudget]
    with d hFinite_d hCol hTarget hEd hMean_d hBudget_d
  letI : IsFiniteMeasure (μ d) := hFinite_d
  exact
    columnProb_le_upperTailProb_of_subset_certificate
      (p := p) (q := q) (σ := σ)
      (μ := μ d) (E := E d)
      (columnProb := columnProb d) (targetProb := targetProb d)
      (α₀ := α₀) (N := N d) (a := a d) (eps := eps d)
      (mean := mean d) (center := center d)
      (errSpike := errSpike d) (errBg := errBg d)
      (errMix := errMix d) (errMean := errMean d) (k := k)
      hCol hTarget hEd hMean_d hBudget_d

end ColumnSpikeAlgebra

/-! ## Deterministic local expansion lemma -/

section LocalExpansionAlgebra

variable [Fintype p] [Fintype q] [Fintype σ]
variable [DecidableEq p] [DecidableEq q]

/-- Background term `A = (YY*)^Γ` in the local expansion around `Y`. -/
noncomputable def localBackground (Y : SampleMatrix p q σ) : BipMatrix p q :=
  gamma (densityMatrix Y)

/-- Linear term `L = (YH* + HY*)^Γ` in the local expansion, with `H = X - Y`. -/
noncomputable def localLinear (Y H : SampleMatrix p q σ) : BipMatrix p q :=
  gamma (Y * Hᴴ + H * Yᴴ)

/-- Quadratic term `Q = (HH*)^Γ` in the local expansion, with `H = X - Y`. -/
noncomputable def localQuadratic (H : SampleMatrix p q σ) : BipMatrix p q :=
  gamma (H * Hᴴ)

set_option linter.unusedSectionVars false in
/-- The quadratic local term `Q = (HH*)^Γ` is Hermitian. -/
theorem localQuadratic_isHermitian
    (H : SampleMatrix p q σ) :
    (localQuadratic (p := p) (q := q) (σ := σ) H).IsHermitian := by
  have hraw : (H * Hᴴ).IsHermitian := by
    simpa using (Matrix.isHermitian_mul_conjTranspose_self (A := H))
  dsimp [localQuadratic, gamma]
  calc
    (Matrix.partialTranspose (H * Hᴴ))ᴴ =
        Matrix.partialTranspose ((H * Hᴴ)ᴴ) := by
          exact (partialTranspose_conjTranspose (M := H * Hᴴ)).symm
    _ = Matrix.partialTranspose (H * Hᴴ) := by
          rw [hraw.eq]

set_option linter.unusedSectionVars false in
/-- Exact Hilbert--Schmidt matrix identity behind the local expansion:

`XX* = YY* + YH* + HY* + HH*`, where `H = X - Y`.

This is the algebraic point that ensures there are no hidden first-order
or cross terms outside `L` and `Q`. -/
theorem densityMatrix_local_decomposition
    (X Y : SampleMatrix p q σ) :
    densityMatrix X =
      densityMatrix Y +
        (Y * (X - Y)ᴴ + (X - Y) * Yᴴ) +
          (X - Y) * (X - Y)ᴴ := by
  let H : SampleMatrix p q σ := X - Y
  have hX : X = Y + H := by
    ext i α
    simp [H]
  rw [hX]
  ext i j
  simp [densityMatrix, Matrix.mul_apply, H, Finset.sum_add_distrib,
    add_mul, mul_add, sub_eq_add_neg]
  ring

/-- Exact local expansion after partial transpose:

`(XX*)^Γ = A + L + Q`,
with `A = (YY*)^Γ`, `L = (YH* + HY*)^Γ`, and `Q = (HH*)^Γ`. -/
theorem gamma_densityMatrix_local_decomposition
    (X Y : SampleMatrix p q σ) :
    gamma (densityMatrix X) =
      localBackground (p := p) (q := q) (σ := σ) Y +
        localLinear (p := p) (q := q) (σ := σ) Y (X - Y) +
          localQuadratic (p := p) (q := q) (σ := σ) (X - Y) := by
  unfold localBackground localLinear localQuadratic
  rw [densityMatrix_local_decomposition (X := X) (Y := Y)]
  simp [gamma]

/-- The quadratic local term is genuinely quadratic in the perturbation:
`‖Q‖₂ ≤ ‖H‖₂²`. -/
theorem localQuadratic_frobeniusNorm_le
    (H : SampleMatrix p q σ) :
    frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
        (localQuadratic (p := p) (q := q) (σ := σ) H) ≤
      frobeniusNorm (p := p) (q := q) (σ := σ) H ^ 2 := by
  calc
    frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
        (localQuadratic (p := p) (q := q) (σ := σ) H)
        = frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
            (H * Hᴴ) := by
            unfold localQuadratic
            exact PptFactorization.RandomMatrixModel.frobeniusNorm_gamma (H * Hᴴ)
    _ = ‖H * Hᴴ‖ := rfl
    _ ≤ ‖H‖ * ‖Hᴴ‖ := Matrix.frobenius_norm_mul H Hᴴ
    _ = frobeniusNorm (p := p) (q := q) (σ := σ) H ^ 2 := by
          rw [Matrix.frobenius_norm_conjTranspose]
          simp [frobeniusNorm, pow_two]

/-- The linear local term is bounded by the Frobenius product estimate:
`‖L‖₂ ≤ 2 ‖Y‖₂ ‖H‖₂`.

The sharper upper-bound proof later replaces one Frobenius factor by an
operator-norm good-set bound.  This lemma records the no-input algebraic
linear-in-`H` part. -/
theorem localLinear_frobeniusNorm_le_two_mul
    (Y H : SampleMatrix p q σ) :
    frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
        (localLinear (p := p) (q := q) (σ := σ) Y H) ≤
      2 * frobeniusNorm (p := p) (q := q) (σ := σ) Y *
        frobeniusNorm (p := p) (q := q) (σ := σ) H := by
  have hgamma :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
          (localLinear (p := p) (q := q) (σ := σ) Y H) =
        frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
          (Y * Hᴴ + H * Yᴴ) := by
    unfold localLinear
    exact PptFactorization.RandomMatrixModel.frobeniusNorm_gamma (Y * Hᴴ + H * Yᴴ)
  calc
    frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
        (localLinear (p := p) (q := q) (σ := σ) Y H)
        = ‖Y * Hᴴ + H * Yᴴ‖ := by
            rw [hgamma]
            rfl
    _ ≤ ‖Y * Hᴴ‖ + ‖H * Yᴴ‖ := norm_add_le _ _
    _ ≤ ‖Y‖ * ‖Hᴴ‖ + ‖H‖ * ‖Yᴴ‖ := by
          exact add_le_add (Matrix.frobenius_norm_mul Y Hᴴ)
            (Matrix.frobenius_norm_mul H Yᴴ)
    _ = 2 * frobeniusNorm (p := p) (q := q) (σ := σ) Y *
          frobeniusNorm (p := p) (q := q) (σ := σ) H := by
          rw [Matrix.frobenius_norm_conjTranspose,
            Matrix.frobenius_norm_conjTranspose]
          simp [frobeniusNorm]
          ring

/-- Sharper linear local bound using the operator norm of the background point:
`‖L‖₂ ≤ 2 ‖Y‖op ‖H‖₂`.

This is the estimate that makes the multi-defect mixed words decay at the
sharp local radius.  One copy of `Y` is controlled by the rectangular operator
norm, and the second term is reduced to the first by conjugate transpose. -/
theorem localLinear_frobeniusNorm_le_two_mul_sampleOpNorm
    (Y H : SampleMatrix p q σ) :
    frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
        (localLinear (p := p) (q := q) (σ := σ) Y H) ≤
      2 *
        PptFactorization.HighProbabilityBounds.sampleOpNorm
          (p := p) (q := q) (σ := σ) Y *
        frobeniusNorm (p := p) (q := q) (σ := σ) H := by
  have hgamma :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
          (localLinear (p := p) (q := q) (σ := σ) Y H) =
        frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
          (Y * Hᴴ + H * Yᴴ) := by
    unfold localLinear
    exact PptFactorization.RandomMatrixModel.frobeniusNorm_gamma (Y * Hᴴ + H * Yᴴ)
  have hfirst :
      ‖Y * Hᴴ‖ ≤
        PptFactorization.HighProbabilityBounds.sampleOpNorm
          (p := p) (q := q) (σ := σ) Y * ‖Hᴴ‖ := by
    exact
      PptFactorization.HighProbabilityBounds.sampleOpNorm_mul_frobeniusNorm_le
        (p := p) (q := q) (σ := σ) Y Hᴴ
  have hsecond :
      ‖H * Yᴴ‖ ≤
        PptFactorization.HighProbabilityBounds.sampleOpNorm
          (p := p) (q := q) (σ := σ) Y * ‖Hᴴ‖ := by
    calc
      ‖H * Yᴴ‖ = ‖(H * Yᴴ)ᴴ‖ := by
        rw [Matrix.frobenius_norm_conjTranspose]
      _ = ‖Y * Hᴴ‖ := by
        simp [Matrix.conjTranspose_mul]
      _ ≤
          PptFactorization.HighProbabilityBounds.sampleOpNorm
            (p := p) (q := q) (σ := σ) Y * ‖Hᴴ‖ := hfirst
  calc
    frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
        (localLinear (p := p) (q := q) (σ := σ) Y H)
        = ‖Y * Hᴴ + H * Yᴴ‖ := by
            rw [hgamma]
            rfl
    _ ≤ ‖Y * Hᴴ‖ + ‖H * Yᴴ‖ := norm_add_le _ _
    _ ≤
        PptFactorization.HighProbabilityBounds.sampleOpNorm
            (p := p) (q := q) (σ := σ) Y * ‖Hᴴ‖ +
          PptFactorization.HighProbabilityBounds.sampleOpNorm
            (p := p) (q := q) (σ := σ) Y * ‖Hᴴ‖ := by
          exact add_le_add hfirst hsecond
    _ =
        2 *
          PptFactorization.HighProbabilityBounds.sampleOpNorm
            (p := p) (q := q) (σ := σ) Y *
          frobeniusNorm (p := p) (q := q) (σ := σ) H := by
          rw [Matrix.frobenius_norm_conjTranspose]
          simp [frobeniusNorm]
          ring

/-- Concrete linear-defect bound from an operator-norm estimate on the
background point.

If `sampleOpNorm Y ≤ M / √N` and `‖X - Y‖₂ ≤ r`, then

`‖L(Y, X-Y)‖₂ ≤ 2 * (M / √N) * r`.

This is the quantitative estimate later specialized on the background typical
set `K_N`. -/
theorem localLinear_frobeniusNorm_bound_of_sampleOpNorm
    {N M : ℝ} {X Y : SampleMatrix p q σ} {r : ℝ}
    (hOp :
      PptFactorization.HighProbabilityBounds.sampleOpNorm
        (p := p) (q := q) (σ := σ) Y ≤ M / Real.sqrt N)
    (hdist :
      frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤ r) :
    frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
        (localLinear (p := p) (q := q) (σ := σ) Y (X - Y)) ≤
      2 * (M / Real.sqrt N) * r := by
  have hL :=
    localLinear_frobeniusNorm_le_two_mul_sampleOpNorm
      (p := p) (q := q) (σ := σ) Y (X - Y)
  have hOp_nonneg :
      0 ≤
        PptFactorization.HighProbabilityBounds.sampleOpNorm
          (p := p) (q := q) (σ := σ) Y := by
    unfold PptFactorization.HighProbabilityBounds.sampleOpNorm
    positivity
  have hcoef_nonneg : 0 ≤ M / Real.sqrt N := le_trans hOp_nonneg hOp
  have hcoef2_nonneg : 0 ≤ 2 * (M / Real.sqrt N) := by
    nlinarith
  have hdist_nonneg :
      0 ≤ frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) := by
    unfold frobeniusNorm
    positivity
  calc
    frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
        (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
        ≤
      2 *
        PptFactorization.HighProbabilityBounds.sampleOpNorm
          (p := p) (q := q) (σ := σ) Y *
        frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) := hL
    _ ≤ 2 * (M / Real.sqrt N) *
          frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) := by
          gcongr
    _ ≤ 2 * (M / Real.sqrt N) * r := by
          exact mul_le_mul_of_nonneg_left hdist hcoef2_nonneg

/-- Sharp-radius specialization of the quadratic local bound.

If `‖X - Y‖₂ ≤ r`, then the quadratic term satisfies `‖Q(X-Y)‖₂ ≤ r²`. -/
theorem localQuadratic_frobeniusNorm_bound_of_radius
    {X Y : SampleMatrix p q σ} {r : ℝ}
    (hdist :
      frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤ r) :
    frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
        (localQuadratic (p := p) (q := q) (σ := σ) (X - Y)) ≤
      r ^ 2 := by
  have hQ :=
    localQuadratic_frobeniusNorm_le
      (p := p) (q := q) (σ := σ) (X - Y)
  have hdist_nonneg :
      0 ≤ frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) := by
    unfold frobeniusNorm
    positivity
  calc
    frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
        (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
        ≤
      frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ^ 2 := hQ
    _ ≤ r ^ 2 := by
      exact pow_le_pow_left₀ hdist_nonneg hdist 2

/-- Exact mixed remainder in the local expansion of the normalized trace
power around `A`.

It contains every word in `(A + L + Q)^k` except the pure background word
`A^k` and the pure quadratic word `Q^k`.  It is defined by subtraction rather
than by a combinatorial word sum, so the identity below is definitional and
cannot silently drop a mixed term. -/
noncomputable def localExpansionMixedRemainder
    (N : ℝ) (k : ℕ) (A L Q : BipMatrix p q) : ℝ :=
  scaledTracePower (p := p) (q := q) N k (A + L + Q) -
    scaledTracePower (p := p) (q := q) N k A -
      scaledTracePower (p := p) (q := q) N k Q

/-- Exact local expansion of the normalized trace power:

`F(A + L + Q) = F(A) + F(Q) + mixed`.

This is the deterministic core of the local expansion lemma. -/
theorem scaledTracePower_localExpansion_decomposition
    (N : ℝ) (k : ℕ) (A L Q : BipMatrix p q) :
    scaledTracePower (p := p) (q := q) N k (A + L + Q) =
      scaledTracePower (p := p) (q := q) N k A +
        scaledTracePower (p := p) (q := q) N k Q +
          localExpansionMixedRemainder (p := p) (q := q) N k A L Q := by
  unfold localExpansionMixedRemainder
  ring

/-- Local expansion in bound form.

If the pure quadratic word is bounded by `a^k + errQ` and the exact mixed
remainder is bounded by `errMix`, then the perturbation of the normalized trace
moment is bounded by `a^k + errQ + errMix`.

This is the formal statement of the deterministic estimate
`|F(A+L+Q)-F(A)| ≤ a^k + o(1)`, before the separate Schatten estimates prove
that the two errors are small on the good set. -/
theorem localExpansion_bound_from_quadratic_and_mixed
    {N a errQ errMix : ℝ} {k : ℕ} {A L Q : BipMatrix p q}
    (hQ :
      |scaledTracePower (p := p) (q := q) N k Q| ≤ a ^ k + errQ)
    (hMixed :
      |localExpansionMixedRemainder (p := p) (q := q) N k A L Q| ≤ errMix) :
    |scaledTracePower (p := p) (q := q) N k (A + L + Q) -
        scaledTracePower (p := p) (q := q) N k A| ≤
      a ^ k + errQ + errMix := by
  have hdecomp :
      scaledTracePower (p := p) (q := q) N k (A + L + Q) -
          scaledTracePower (p := p) (q := q) N k A =
        scaledTracePower (p := p) (q := q) N k Q +
          localExpansionMixedRemainder (p := p) (q := q) N k A L Q := by
    have h :=
      scaledTracePower_localExpansion_decomposition
        (p := p) (q := q) N k A L Q
    linarith
  calc
    |scaledTracePower (p := p) (q := q) N k (A + L + Q) -
        scaledTracePower (p := p) (q := q) N k A|
        = |scaledTracePower (p := p) (q := q) N k Q +
            localExpansionMixedRemainder (p := p) (q := q) N k A L Q| := by
            rw [hdecomp]
    _ ≤ |scaledTracePower (p := p) (q := q) N k Q| +
          |localExpansionMixedRemainder (p := p) (q := q) N k A L Q| :=
            abs_add_le _ _
    _ ≤ a ^ k + errQ + errMix := by
          linarith

/-- Sample-level local expansion bound.

With `H = X - Y`, this is the same estimate rewritten for the actual matrices
`(XX*)^Γ` and `(YY*)^Γ`. -/
theorem sample_localExpansion_bound_from_quadratic_and_mixed
    {N a errQ errMix : ℝ} {k : ℕ} {X Y : SampleMatrix p q σ}
    (hQ :
      |scaledTracePower (p := p) (q := q) N k
          (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))| ≤
        a ^ k + errQ)
    (hMixed :
      |localExpansionMixedRemainder (p := p) (q := q) N k
          (localBackground (p := p) (q := q) (σ := σ) Y)
          (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
          (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))| ≤ errMix) :
    |scaledTracePower (p := p) (q := q) N k (gamma (densityMatrix X)) -
        scaledTracePower (p := p) (q := q) N k (gamma (densityMatrix Y))| ≤
      a ^ k + errQ + errMix := by
  rw [gamma_densityMatrix_local_decomposition (X := X) (Y := Y)]
  exact localExpansion_bound_from_quadratic_and_mixed
    (p := p) (q := q) (N := N) (a := a) (errQ := errQ)
    (errMix := errMix) (k := k)
    (A := localBackground (p := p) (q := q) (σ := σ) Y)
    (L := localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
    (Q := localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
    hQ hMixed

/-- Eventual `a^k + o(1)` form of the local expansion lemma.

The inputs say that the pure quadratic contribution is eventually at most
`a^k + o(1)` and the mixed remainder is `o(1)`.  The conclusion is the final
epsilon bookkeeping for the local expansion estimate. -/
theorem localExpansion_eventual_bound
    {Nseq : ℕ → ℝ} {A L Q : ℕ → BipMatrix p q} {a : ℝ} {k : ℕ}
    (hQ :
      ∀ η : ℝ, 0 < η →
        ∀ᶠ d in atTop,
          |scaledTracePower (p := p) (q := q) (Nseq d) k (Q d)| ≤
            a ^ k + η)
    (hMixed :
      ∀ η : ℝ, 0 < η →
        ∀ᶠ d in atTop,
          |localExpansionMixedRemainder (p := p) (q := q)
              (Nseq d) k (A d) (L d) (Q d)| ≤ η) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        |scaledTracePower (p := p) (q := q) (Nseq d) k
              (A d + L d + Q d) -
            scaledTracePower (p := p) (q := q) (Nseq d) k (A d)| ≤
          a ^ k + η := by
  intro η hη
  have hηhalf : 0 < η / 2 := by positivity
  filter_upwards [hQ (η / 2) hηhalf, hMixed (η / 2) hηhalf] with d hQd hMixd
  have h :=
    localExpansion_bound_from_quadratic_and_mixed
      (p := p) (q := q) (N := Nseq d) (a := a) (errQ := η / 2)
      (errMix := η / 2) (k := k)
      (A := A d) (L := L d) (Q := Q d) hQd hMixd
  linarith

/-- Finite-dimensional `ℓ^k`/`ℓ^2` comparison in the exact form needed for
Hermitian trace powers.

The hypothesis `2 ≤ k` is necessary: for `k = 1`, the corresponding matrix
trace estimate would fail on the identity matrix. -/
theorem abs_sum_pow_le_sqrt_sum_sq_pow
    {ι : Type*} [Fintype ι] (f : ι → ℝ) {k : ℕ} (hk : 2 ≤ k) :
    |∑ i : ι, f i ^ k| ≤
      (Real.sqrt (∑ i : ι, f i ^ 2)) ^ k := by
  classical
  let S : ℝ := ∑ i : ι, f i ^ 2
  have hS_nonneg : 0 ≤ S := by
    exact Finset.sum_nonneg (fun i _ => sq_nonneg (f i))
  have h_abs_le_sqrt (i : ι) : |f i| ≤ Real.sqrt S := by
    have hsingle : f i ^ 2 ≤ ∑ j : ι, f j ^ 2 := by
      exact Finset.single_le_sum
        (s := (Finset.univ : Finset ι))
        (f := fun j : ι => f j ^ 2)
        (fun j _ => sq_nonneg (f j))
        (by simp)
    exact Real.abs_le_sqrt hsingle
  have hterm (i : ι) :
      |f i ^ k| ≤ |f i| ^ 2 * (Real.sqrt S) ^ (k - 2) := by
    rw [abs_pow]
    have hsplit : |f i| ^ k = |f i| ^ 2 * |f i| ^ (k - 2) := by
      rw [← pow_add, Nat.add_sub_of_le hk]
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg (f i)) (h_abs_le_sqrt i) (k - 2))
      (pow_nonneg (abs_nonneg (f i)) 2)
  calc
    |∑ i : ι, f i ^ k| ≤ ∑ i : ι, |f i ^ k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : ι, |f i| ^ 2 * (Real.sqrt S) ^ (k - 2) :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = (∑ i : ι, |f i| ^ 2) * (Real.sqrt S) ^ (k - 2) := by
      rw [Finset.sum_mul]
    _ = S * (Real.sqrt S) ^ (k - 2) := by
      simp [S, sq_abs]
    _ = (Real.sqrt S) ^ k := by
      calc
        S * (Real.sqrt S) ^ (k - 2)
            = (Real.sqrt S) ^ 2 * (Real.sqrt S) ^ (k - 2) := by
              rw [Real.sq_sqrt hS_nonneg]
        _ = (Real.sqrt S) ^ (2 + (k - 2)) := by
              rw [pow_add]
        _ = (Real.sqrt S) ^ k := by
              rw [Nat.add_sub_of_le hk]

/-- Spectral trace formula for powers of a Hermitian complex matrix, expressed
as a real identity. -/
theorem hermitian_re_trace_pow_eq_sum_eigenvalues_pow
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (k : ℕ) :
    RCLike.re ((A ^ k).trace) = ∑ i : n, hA.eigenvalues i ^ k := by
  let φ := (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ)) hA.eigenvectorUnitary
  let D : Matrix n n ℂ := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  have hAeq : A = φ D := by
    simpa [φ, D] using hA.spectral_theorem
  have hpowA : A ^ k = φ (D ^ k) := by
    rw [hAeq]
    exact (map_pow φ D k).symm
  calc
    RCLike.re ((A ^ k).trace)
        = RCLike.re (((φ (D ^ k))).trace) := by
            rw [hpowA]
    _ = RCLike.re ((D ^ k).trace) := by
            exact congrArg RCLike.re
              (PptFactorization.HighProbabilityBounds.matrix_trace_conjStarAlgAut
                hA.eigenvectorUnitary (D ^ k))
    _ = ∑ i : n, hA.eigenvalues i ^ k := by
            rw [Matrix.diagonal_pow, Matrix.trace_diagonal]
            simp only [Function.comp_apply, Pi.pow_apply]
            change (∑ x, ((hA.eigenvalues x : ℂ) ^ k)).re =
              ∑ i, hA.eigenvalues i ^ k
            rw [Complex.re_sum]
            refine Finset.sum_congr rfl ?_
            intro i _
            have hp :
                ((hA.eigenvalues i ^ k : ℝ) : ℂ) =
                  (hA.eigenvalues i : ℂ) ^ k :=
              Complex.ofReal_pow (hA.eigenvalues i) k
            have h1 :
                RCLike.re ((hA.eigenvalues i : ℂ) ^ k) =
                  RCLike.re (((hA.eigenvalues i ^ k : ℝ) : ℂ)) :=
              congrArg RCLike.re hp.symm
            exact h1.trans (RCLike.ofReal_re (K := ℂ) (hA.eigenvalues i ^ k))

/-- Primitive Hermitian Schatten/Hölder trace-power estimate.

For `k ≥ 2`,

`|Re Tr(Q^k)| ≤ ‖Q‖₂^k`.

This is the finite-dimensional spectral proof of the Schatten/Hölder input
used by the pure `Q^k` word. -/
theorem hermitian_abs_re_trace_pow_le_frobenius_norm_pow
    {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℂ) (hQ : Q.IsHermitian) {k : ℕ} (hk : 2 ≤ k) :
    |RCLike.re ((Q ^ k).trace)| ≤ ‖Q‖ ^ k := by
  have htrace :
      RCLike.re ((Q ^ k).trace) = ∑ i : n, hQ.eigenvalues i ^ k :=
    hermitian_re_trace_pow_eq_sum_eigenvalues_pow Q hQ k
  have htrace2 :
      RCLike.re ((Q ^ 2).trace) = ∑ i : n, hQ.eigenvalues i ^ 2 :=
    hermitian_re_trace_pow_eq_sum_eigenvalues_pow Q hQ 2
  have hmul : Qᴴ * Q = Q ^ 2 := by
    rw [hQ.eq]
    rw [pow_two]
  have hfrob_sq :
      ‖Q‖ ^ 2 = ∑ i : n, hQ.eigenvalues i ^ 2 := by
    calc
      ‖Q‖ ^ 2 = RCLike.re (((Qᴴ * Q).trace)) := by
        exact matrix_frobenius_norm_sq_eq_re_trace_conjTranspose_mul_self Q
      _ = RCLike.re ((Q ^ 2).trace) := by
        rw [hmul]
      _ = ∑ i : n, hQ.eigenvalues i ^ 2 := htrace2
  have hsqrt :
      Real.sqrt (∑ i : n, hQ.eigenvalues i ^ 2) = ‖Q‖ := by
    rw [← hfrob_sq]
    exact Real.sqrt_sq (norm_nonneg Q)
  calc
    |RCLike.re ((Q ^ k).trace)|
        = |∑ i : n, hQ.eigenvalues i ^ k| := by
          rw [htrace]
    _ ≤ (Real.sqrt (∑ i : n, hQ.eigenvalues i ^ 2)) ^ k :=
          abs_sum_pow_le_sqrt_sum_sq_pow hQ.eigenvalues hk
    _ = ‖Q‖ ^ k := by
          rw [hsqrt]

/-- The primitive Hermitian Schatten/Hölder trace-power estimate in the
project's `frobeniusNorm` notation for bipartite matrices. -/
theorem hermitian_abs_re_trace_pow_le_frobeniusNorm_pow
    {k : ℕ} (hk : 2 ≤ k) {Q : BipMatrix p q} (hQ : Q.IsHermitian) :
    |(Matrix.trace (Q ^ k)).re| ≤
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) Q ^ k := by
  simpa [frobeniusNorm] using
    (hermitian_abs_re_trace_pow_le_frobenius_norm_pow
      (n := BipIndex p q) Q hQ hk)

/-- Primitive trace-versus-Frobenius estimate for square complex matrices.

This is the exact one-defect bound used for local mixed words with a single
linear or quadratic defect:

`|Re Tr(M)| ≤ sqrt(dim) * ‖M‖₂`.
-/
theorem matrix_vec_norm_eq_frobenius_norm
    {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    ‖WithLp.toLp 2 (Matrix.vec A)‖ = ‖A‖ := by
  calc
    ‖WithLp.toLp 2 (Matrix.vec A)‖ =
        Real.sqrt (∑ i : m, ∑ j : n, ‖A i j‖ ^ 2) := by
      calc
        ‖WithLp.toLp 2 (Matrix.vec A)‖ =
            Real.sqrt (∑ ij : n × m, ‖Matrix.vec A ij‖ ^ 2) := by
              simpa using (PiLp.norm_eq_of_L2 (x := WithLp.toLp 2 (Matrix.vec A)))
        _ = Real.sqrt (∑ ij : n × m, ‖A ij.2 ij.1‖ ^ 2) := by
              simp [Matrix.vec]
        _ = Real.sqrt (∑ j : n, ∑ i : m, ‖A i j‖ ^ 2) := by
              congr 1
              rw [Fintype.sum_prod_type]
        _ = Real.sqrt (∑ i : m, ∑ j : n, ‖A i j‖ ^ 2) := by
              congr 1
              rw [Finset.sum_comm]
    _ = ‖A‖ := by
      rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
      congr 1
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      simpa using (Real.rpow_natCast (‖A i j‖) 2).symm

/-- Primitive Hilbert--Schmidt trace-pairing bound.

For square complex matrices,

`|Re Tr(UV)| ≤ ‖U‖₂ ‖V‖₂`.

This is the no-dimension-loss estimate used for mixed words carrying at least
two defect letters. -/
theorem matrix_abs_re_trace_mul_le_frobenius_norm_mul
    {n : Type*} [Fintype n] [DecidableEq n] (U V : Matrix n n ℂ) :
    |(Matrix.trace (U * V)).re| ≤ ‖U‖ * ‖V‖ := by
  have htrace :
      star (Matrix.vec Uᴴ) ⬝ᵥ Matrix.vec V =
        Matrix.trace (U * V) := by
    simpa using (Matrix.star_vec_dotProduct_vec Uᴴ V)
  have hnorm :
      ‖Matrix.trace (U * V)‖ ≤
        ‖WithLp.toLp 2 (Matrix.vec Uᴴ)‖ * ‖WithLp.toLp 2 (Matrix.vec V)‖ := by
    rw [← htrace, dotProduct_comm]
    rw [← EuclideanSpace.inner_eq_star_dotProduct
      (x := WithLp.toLp 2 (Matrix.vec Uᴴ))
      (y := WithLp.toLp 2 (Matrix.vec V))]
    exact norm_inner_le_norm _ _
  have hre :
      |(Matrix.trace (U * V)).re| ≤ ‖Matrix.trace (U * V)‖ := by
    exact Complex.abs_re_le_norm (Matrix.trace (U * V))
  calc
    |(Matrix.trace (U * V)).re| ≤ ‖Matrix.trace (U * V)‖ := hre
    _ ≤ ‖WithLp.toLp 2 (Matrix.vec Uᴴ)‖ * ‖WithLp.toLp 2 (Matrix.vec V)‖ := hnorm
    _ = ‖Uᴴ‖ * ‖V‖ := by
          rw [matrix_vec_norm_eq_frobenius_norm (A := Uᴴ),
            matrix_vec_norm_eq_frobenius_norm (A := V)]
    _ = ‖U‖ * ‖V‖ := by
          rw [Matrix.frobenius_norm_conjTranspose]

theorem matrix_abs_re_trace_le_sqrt_card_mul_frobenius_norm
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    |(Matrix.trace A).re| ≤ Real.sqrt (Fintype.card n) * ‖A‖ := by
  have hone :
      ‖(1 : Matrix n n ℂ)‖ = Real.sqrt (Fintype.card n) := by
    have honeN :
        ‖(1 : Matrix n n ℂ)‖₊ = NNReal.sqrt (Fintype.card n) := by
      simpa using (Matrix.frobenius_nnnorm_one (n := n) (α := ℂ))
    change ((‖(1 : Matrix n n ℂ)‖₊ : ℝ) = Real.sqrt (Fintype.card n))
    simpa [Real.coe_sqrt] using congrArg (fun x : NNReal => (x : ℝ)) honeN
  have hmul :=
    matrix_abs_re_trace_mul_le_frobenius_norm_mul (n := n) A (1 : Matrix n n ℂ)
  simpa [Matrix.mul_one, hone, mul_comm] using hmul

/-- Pure `Q^k` estimate from the Schatten/Hölder trace-power bound and a
Frobenius-radius estimate.

The primitive analytic input is the dimension-free Schatten/Hölder inequality

`|Re Tr(Q^k)| ≤ ‖Q‖₂^k`.

The scaling step is:
if `‖Q‖₂ ≤ radius` and
`N^(k-1) radius^k ≤ a^k + err`, then the normalized pure quadratic word is
bounded by `a^k + err`. -/
theorem pureQuadratic_scaledTracePower_le_from_schattenHolder_radius
    {N a err radius : ℝ} {k : ℕ} {Q : BipMatrix p q}
    (hN : 0 ≤ N)
    (hk : 2 ≤ k)
    (hQHerm : Q.IsHermitian)
    (hQradius :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) Q ≤ radius)
    (hScale :
      N ^ (k - 1) * radius ^ k ≤ a ^ k + err) :
    |scaledTracePower (p := p) (q := q) N k Q| ≤ a ^ k + err := by
  have hNpow : 0 ≤ N ^ (k - 1) := pow_nonneg hN _
  have hQnorm_nonneg :
      0 ≤ frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) Q := by
    unfold frobeniusNorm
    exact norm_nonneg _
  have hQpow :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) Q ^ k ≤
        radius ^ k :=
    pow_le_pow_left₀ hQnorm_nonneg hQradius k
  unfold scaledTracePower
  rw [abs_mul, abs_of_nonneg hNpow]
  have hTrace :
      |(Matrix.trace (Q ^ k)).re| ≤
        frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) Q ^ k :=
    hermitian_abs_re_trace_pow_le_frobeniusNorm_pow
      (p := p) (q := q) (k := k) hk hQHerm
  calc
    N ^ (k - 1) * |(Matrix.trace (Q ^ k)).re| ≤
        N ^ (k - 1) *
          frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) Q ^ k :=
      mul_le_mul_of_nonneg_left hTrace hNpow
    _ ≤ N ^ (k - 1) * radius ^ k :=
      mul_le_mul_of_nonneg_left hQpow hNpow
    _ ≤ a ^ k + err := hScale

/-- Eventual pure `Q^k` estimate at the local radius.

This is the asymptotic form consumed by `localExpansion_eventual_bound`: the
Schatten/Hölder trace inequality plus radius scaling gives

`|N^(k-1) Re Tr(Q_d^k)| ≤ a^k + o(1)`. -/
theorem pureQuadratic_eventual_bound_from_schattenHolder_radius
    {Nseq radius : ℕ → ℝ} {Q : ℕ → BipMatrix p q} {a : ℝ} {k : ℕ}
    (hN : ∀ᶠ d in atTop, 0 ≤ Nseq d)
    (hk : 2 ≤ k)
    (hQHerm :
      ∀ᶠ d in atTop,
        (Q d).IsHermitian)
    (hQradius :
      ∀ᶠ d in atTop,
        frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) (Q d) ≤
          radius d)
    (hScale :
      ∀ η : ℝ, 0 < η →
        ∀ᶠ d in atTop,
          Nseq d ^ (k - 1) * radius d ^ k ≤ a ^ k + η) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        |scaledTracePower (p := p) (q := q) (Nseq d) k (Q d)| ≤
          a ^ k + η := by
  intro η hη
  filter_upwards [hN, hQHerm, hQradius, hScale η hη]
    with d hNd hQHd hQrd hscaled
  exact
    pureQuadratic_scaledTracePower_le_from_schattenHolder_radius
      (p := p) (q := q) (N := Nseq d) (a := a) (err := η)
      (radius := radius d) (k := k) (Q := Q d)
      hNd hk hQHd hQrd hscaled

/-- If the Schatten/Hölder word estimates give a deterministic envelope
`errMix_d` for the exact mixed remainder and that envelope tends to zero in
the eventual `∀η>0` sense, then the mixed remainder is `o(1)`. -/
theorem mixedRemainder_eventual_small_of_schattenHolder_envelope
    {Nseq : ℕ → ℝ} {A L Q : ℕ → BipMatrix p q} {errMix : ℕ → ℝ} {k : ℕ}
    (hEnvelope :
      ∀ᶠ d in atTop,
        |localExpansionMixedRemainder (p := p) (q := q)
            (Nseq d) k (A d) (L d) (Q d)| ≤ errMix d)
    (hSmall :
      ∀ η : ℝ, 0 < η →
        ∀ᶠ d in atTop, errMix d ≤ η) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        |localExpansionMixedRemainder (p := p) (q := q)
            (Nseq d) k (A d) (L d) (Q d)| ≤ η := by
  intro η hη
  filter_upwards [hEnvelope, hSmall η hη] with d hEnv hErr
  exact le_trans hEnv hErr

/-- The three letters in the local expansion alphabet:

* `A` is the background word letter `(YY*)^Γ`;
* `L` is the linear perturbation letter `(YH* + HY*)^Γ`;
* `Q` is the quadratic perturbation letter `(HH*)^Γ`.

Words in `(A + L + Q)^k` are functions `Fin k → LocalExpansionLetter`. -/
inductive LocalExpansionLetter where
  | A
  | L
  | Q
  deriving DecidableEq, Fintype

theorem sum_localExpansionLetter
    {α : Type*} [AddCommMonoid α] (f : LocalExpansionLetter → α) :
    (∑ x : LocalExpansionLetter, f x) =
      f LocalExpansionLetter.A +
        f LocalExpansionLetter.L +
          f LocalExpansionLetter.Q := by
  let e : LocalExpansionLetter ≃ Fin 3 :=
    { toFun := fun x =>
        match x with
        | LocalExpansionLetter.A => 0
        | LocalExpansionLetter.L => 1
        | LocalExpansionLetter.Q => 2
      invFun := fun i =>
        if i = 0 then LocalExpansionLetter.A
        else if i = 1 then LocalExpansionLetter.L
        else LocalExpansionLetter.Q
      left_inv := by
        intro x
        cases x <;> simp
      right_inv := by
        intro i
        fin_cases i <;> simp }
  calc
    (∑ x : LocalExpansionLetter, f x) = ∑ i : Fin 3, f (e.symm i) := by
      exact
        Fintype.sum_equiv e f
          (fun i : Fin 3 => f (e.symm i))
          (by
            intro x
            cases x <;> simp [e])
    _ = f (e.symm 0) + f (e.symm 1) + f (e.symm 2) := by
      rw [Fin.sum_univ_three]
    _ = f LocalExpansionLetter.A +
          f LocalExpansionLetter.L +
            f LocalExpansionLetter.Q := by
      simp [e]

/-- Number of occurrences of a given letter in a local-expansion word. -/
def localWordLetterCount {k : ℕ}
    (letter : LocalExpansionLetter) (w : Fin k → LocalExpansionLetter) : ℕ :=
  ∑ i : Fin k, if w i = letter then 1 else 0

/-- A local-expansion word is pure in one letter if all its slots carry that
letter. -/
def localWordIsPure {k : ℕ}
    (letter : LocalExpansionLetter) (w : Fin k → LocalExpansionLetter) : Prop :=
  ∀ i : Fin k, w i = letter

/-- The words contributing to the mixed remainder are exactly the words which
are neither the pure background word `A^k` nor the pure quadratic word `Q^k`.

This includes the pure `L^k` word and all genuinely mixed words; both are part
of the subtraction-defined remainder
`F(A+L+Q)-F(A)-F(Q)`. -/
def localWordIsMixed {k : ℕ} (w : Fin k → LocalExpansionLetter) : Prop :=
  ¬ localWordIsPure LocalExpansionLetter.A w ∧
    ¬ localWordIsPure LocalExpansionLetter.Q w

/-- A word with exactly one linear defect and no quadratic defect.  These are
the words estimated with a trace-norm bound for `L`. -/
def localWordHasOneLinearDefect {k : ℕ}
    (w : Fin k → LocalExpansionLetter) : Prop :=
  localWordLetterCount LocalExpansionLetter.L w = 1 ∧
    localWordLetterCount LocalExpansionLetter.Q w = 0

/-- A word with exactly one quadratic defect and no linear defect.  These are
the words estimated with a trace-norm bound for `Q`. -/
def localWordHasOneQuadraticDefect {k : ℕ}
    (w : Fin k → LocalExpansionLetter) : Prop :=
  localWordLetterCount LocalExpansionLetter.L w = 0 ∧
    localWordLetterCount LocalExpansionLetter.Q w = 1

/-- The constant pure-`A` word of length `k`. -/
def localPureAWord (k : ℕ) : Fin k → LocalExpansionLetter :=
  fun _ => LocalExpansionLetter.A

/-- The constant pure-`Q` word of length `k`. -/
def localPureQWord (k : ℕ) : Fin k → LocalExpansionLetter :=
  fun _ => LocalExpansionLetter.Q

/-- Matrix carried by one local-expansion letter. -/
def localLetterMatrix (A L Q : BipMatrix p q) :
    LocalExpansionLetter → BipMatrix p q
  | LocalExpansionLetter.A => A
  | LocalExpansionLetter.L => L
  | LocalExpansionLetter.Q => Q

/-- Ordered product of matrices attached to a local-expansion word. -/
noncomputable def localWordMatrixProduct
    (A L Q : BipMatrix p q) {k : ℕ}
    (w : Fin k → LocalExpansionLetter) : BipMatrix p q :=
  match k with
  | 0 => 1
  | k + 1 =>
      localLetterMatrix A L Q (w 0) *
        localWordMatrixProduct A L Q (fun i : Fin k => w i.succ)

/-- Normalized real trace term attached to a single local-expansion word. -/
noncomputable def localWordScaledTraceTerm
    (N : ℝ) (A L Q : BipMatrix p q) {k : ℕ}
    (w : Fin k → LocalExpansionLetter) : ℝ :=
  N ^ (k - 1) *
    (Matrix.trace
      (localWordMatrixProduct (p := p) (q := q) A L Q w)).re

theorem localWordIsPure_iff_eq_pure
    {k : ℕ} {letter : LocalExpansionLetter}
    {w : Fin k → LocalExpansionLetter} :
    localWordIsPure letter w ↔ w = fun _ => letter := by
  constructor
  · intro hw
    funext i
    exact hw i
  · intro hw
    intro i
    simpa [hw]

theorem localWordIsPure_A_iff_eq_pureA
    {k : ℕ} {w : Fin k → LocalExpansionLetter} :
    localWordIsPure LocalExpansionLetter.A w ↔ w = localPureAWord k := by
  simpa [localPureAWord] using
    (localWordIsPure_iff_eq_pure
      (k := k) (letter := LocalExpansionLetter.A) (w := w))

theorem localWordIsPure_Q_iff_eq_pureQ
    {k : ℕ} {w : Fin k → LocalExpansionLetter} :
    localWordIsPure LocalExpansionLetter.Q w ↔ w = localPureQWord k := by
  simpa [localPureQWord] using
    (localWordIsPure_iff_eq_pure
      (k := k) (letter := LocalExpansionLetter.Q) (w := w))

theorem localPureAWord_ne_localPureQWord
    {k : ℕ} (hk : 0 < k) :
    localPureAWord k ≠ localPureQWord k := by
  intro h
  have h0 := congrFun h ⟨0, hk⟩
  simp [localPureAWord, localPureQWord] at h0

theorem localWordIsMixed_iff_ne_pureA_and_ne_pureQ
    {k : ℕ} {w : Fin k → LocalExpansionLetter} :
    localWordIsMixed w ↔
      w ≠ localPureAWord k ∧ w ≠ localPureQWord k := by
  simp [localWordIsMixed, localWordIsPure_A_iff_eq_pureA,
    localWordIsPure_Q_iff_eq_pureQ]

theorem localWordLetterCount_cons
    {k : ℕ} (letter : LocalExpansionLetter)
    (x : LocalExpansionLetter) (w : Fin k → LocalExpansionLetter) :
    localWordLetterCount letter (Fin.cons x w) =
      (if x = letter then 1 else 0) + localWordLetterCount letter w := by
  rw [localWordLetterCount, Fin.sum_univ_succ, localWordLetterCount]
  simp

theorem localWordLetterCount_total
    {k : ℕ} (w : Fin k → LocalExpansionLetter) :
    localWordLetterCount LocalExpansionLetter.A w +
      localWordLetterCount LocalExpansionLetter.L w +
      localWordLetterCount LocalExpansionLetter.Q w = k := by
  induction k with
  | zero =>
      simp [localWordLetterCount]
  | succ k ih =>
      let x := w 0
      let wt : Fin k → LocalExpansionLetter := Fin.tail w
      have hA :
          localWordLetterCount LocalExpansionLetter.A w =
            (if x = LocalExpansionLetter.A then 1 else 0) +
              localWordLetterCount LocalExpansionLetter.A wt := by
        simpa [x, wt, Fin.cons_self_tail] using
        localWordLetterCount_cons
          (k := k) LocalExpansionLetter.A x wt
      have hL :
          localWordLetterCount LocalExpansionLetter.L w =
            (if x = LocalExpansionLetter.L then 1 else 0) +
              localWordLetterCount LocalExpansionLetter.L wt := by
        simpa [x, wt, Fin.cons_self_tail] using
        localWordLetterCount_cons
          (k := k) LocalExpansionLetter.L x wt
      have hQ :
          localWordLetterCount LocalExpansionLetter.Q w =
            (if x = LocalExpansionLetter.Q then 1 else 0) +
              localWordLetterCount LocalExpansionLetter.Q wt := by
        simpa [x, wt, Fin.cons_self_tail] using
        localWordLetterCount_cons
          (k := k) LocalExpansionLetter.Q x wt
      rw [hA, hL, hQ]
      have hone :
          (if x = LocalExpansionLetter.A then 1 else 0) +
            (if x = LocalExpansionLetter.L then 1 else 0) +
            (if x = LocalExpansionLetter.Q then 1 else 0) = 1 := by
        cases x <;> simp
      linarith [ih wt, hone]

theorem localWordMatrixProduct_pureA
    (A L Q : BipMatrix p q) {k : ℕ} :
    localWordMatrixProduct (p := p) (q := q) A L Q (localPureAWord k) = A ^ k := by
  induction k with
  | zero =>
      simp [localWordMatrixProduct]
  | succ k ih =>
      simp [localWordMatrixProduct, localPureAWord, localLetterMatrix, pow_succ']
      simpa [localPureAWord] using congrArg (fun M => A * M) ih

theorem localWordMatrixProduct_pureQ
    (A L Q : BipMatrix p q) {k : ℕ} :
    localWordMatrixProduct (p := p) (q := q) A L Q (localPureQWord k) = Q ^ k := by
  induction k with
  | zero =>
      simp [localWordMatrixProduct]
  | succ k ih =>
      simp [localWordMatrixProduct, localPureQWord, localLetterMatrix, pow_succ']
      simpa [localPureQWord] using congrArg (fun M => Q * M) ih

theorem localWordScaledTraceTerm_pureA
    (N : ℝ) (A L Q : BipMatrix p q) {k : ℕ} :
    localWordScaledTraceTerm (p := p) (q := q) N A L Q (localPureAWord k) =
      scaledTracePower (p := p) (q := q) N k A := by
  simp [localWordScaledTraceTerm, scaledTracePower,
    localWordMatrixProduct_pureA]

theorem localWordScaledTraceTerm_pureQ
    (N : ℝ) (A L Q : BipMatrix p q) {k : ℕ} :
    localWordScaledTraceTerm (p := p) (q := q) N A L Q (localPureQWord k) =
      scaledTracePower (p := p) (q := q) N k Q := by
  simp [localWordScaledTraceTerm, scaledTracePower,
    localWordMatrixProduct_pureQ]

theorem localWordMatrixProduct_sum
    (A L Q : BipMatrix p q) (k : ℕ) :
    (A + L + Q) ^ k =
      ∑ w : Fin k → LocalExpansionLetter,
        localWordMatrixProduct (p := p) (q := q) A L Q w := by
  classical
  induction k with
  | zero =>
      simp [localWordMatrixProduct]
  | succ k ih =>
      let e :
          (LocalExpansionLetter × (Fin k → LocalExpansionLetter)) ≃
            (Fin (k + 1) → LocalExpansionLetter) :=
        { toFun := fun xw => Fin.cons xw.1 xw.2
          invFun := fun w => (w 0, Fin.tail w)
          left_inv := by
            intro xw
            cases xw
            simp [Fin.tail_cons]
          right_inv := by
            intro w
            simpa using Fin.cons_self_tail w }
      calc
        (A + L + Q) ^ (k + 1)
            = (A + L + Q) * (A + L + Q) ^ k := by rw [pow_succ']
        _ = (A + L + Q) *
              ∑ w : Fin k → LocalExpansionLetter,
                localWordMatrixProduct (p := p) (q := q) A L Q w := by
              rw [ih]
        _ = ((A + L + Q) : BipMatrix p q) *
              ∑ w : Fin k → LocalExpansionLetter,
                localWordMatrixProduct (p := p) (q := q) A L Q w := by rfl
        _ = ((A : BipMatrix p q) + L + Q) *
              ∑ w : Fin k → LocalExpansionLetter,
                localWordMatrixProduct (p := p) (q := q) A L Q w := by rfl
        _ = A *
              ∑ w : Fin k → LocalExpansionLetter,
                localWordMatrixProduct (p := p) (q := q) A L Q w +
              (L *
                ∑ w : Fin k → LocalExpansionLetter,
                  localWordMatrixProduct (p := p) (q := q) A L Q w +
                Q *
                  ∑ w : Fin k → LocalExpansionLetter,
                    localWordMatrixProduct (p := p) (q := q) A L Q w) := by
              simp [add_mul, mul_add, add_assoc]
        _ = ∑ x : Fin k → LocalExpansionLetter,
              A * localWordMatrixProduct (p := p) (q := q) A L Q x +
              (∑ x : Fin k → LocalExpansionLetter,
                L * localWordMatrixProduct (p := p) (q := q) A L Q x +
                ∑ x : Fin k → LocalExpansionLetter,
                  Q * localWordMatrixProduct (p := p) (q := q) A L Q x) := by
              simp [Finset.mul_sum, add_assoc]
        _ = ∑ x : LocalExpansionLetter,
              ∑ w : Fin k → LocalExpansionLetter,
                localWordMatrixProduct (p := p) (q := q) A L Q (Fin.cons x w) := by
              have hsum :
                  (∑ x : LocalExpansionLetter,
                      ∑ w : Fin k → LocalExpansionLetter,
                        localWordMatrixProduct (p := p) (q := q) A L Q
                          (Fin.cons x w)) =
                    ∑ x : Fin k → LocalExpansionLetter,
                      A * localWordMatrixProduct (p := p) (q := q) A L Q x +
                      (∑ x : Fin k → LocalExpansionLetter,
                        L * localWordMatrixProduct (p := p) (q := q) A L Q x +
                        ∑ x : Fin k → LocalExpansionLetter,
                          Q * localWordMatrixProduct (p := p) (q := q) A L Q x) := by
                    rw [sum_localExpansionLetter]
                    simp [localWordMatrixProduct, localLetterMatrix, add_assoc]
              exact hsum.symm
        _ = ∑ xw : LocalExpansionLetter × (Fin k → LocalExpansionLetter),
              localWordMatrixProduct (p := p) (q := q) A L Q (Fin.cons xw.1 xw.2) := by
              rw [Fintype.sum_prod_type]
        _ = ∑ w : Fin (k + 1) → LocalExpansionLetter,
              localWordMatrixProduct (p := p) (q := q) A L Q w := by
              exact
                Fintype.sum_equiv e
                  (fun xw : LocalExpansionLetter × (Fin k → LocalExpansionLetter) =>
                    localWordMatrixProduct (p := p) (q := q) A L Q
                      (Fin.cons xw.1 xw.2))
                  (fun w : Fin (k + 1) → LocalExpansionLetter =>
                    localWordMatrixProduct (p := p) (q := q) A L Q w)
                  (by
                    intro xw
                    cases xw
                    rfl)

theorem scaledTracePower_eq_sum_localWordScaledTraceTerm
    (N : ℝ) (k : ℕ) (A L Q : BipMatrix p q) :
    scaledTracePower (p := p) (q := q) N k (A + L + Q) =
      ∑ w : Fin k → LocalExpansionLetter,
        localWordScaledTraceTerm (p := p) (q := q) N A L Q w := by
  unfold scaledTracePower localWordScaledTraceTerm
  rw [localWordMatrixProduct_sum (p := p) (q := q) A L Q k]
  rw [Matrix.trace_sum]
  simp [map_sum, Finset.mul_sum, mul_assoc]

noncomputable def localMixedWordFilteredSum {k : ℕ}
    (f : (Fin k → LocalExpansionLetter) → ℝ) : ℝ := by
  classical
  exact
    ∑ w : Fin k → LocalExpansionLetter,
      if localWordIsMixed w then
        f w
      else
        0

noncomputable def localExpansionMixedWordSum
    (N : ℝ) (k : ℕ) (A L Q : BipMatrix p q) : ℝ :=
  localMixedWordFilteredSum (k := k)
    (fun w => localWordScaledTraceTerm (p := p) (q := q) N A L Q w)

theorem localExpansionMixedRemainder_eq_sum_mixedWordScaledTraceTerm
    (N : ℝ) (k : ℕ) (A L Q : BipMatrix p q)
    (hk : 1 ≤ k) :
    localExpansionMixedRemainder (p := p) (q := q) N k A L Q =
      localExpansionMixedWordSum (p := p) (q := q) N k A L Q := by
  classical
  let t : (Fin k → LocalExpansionLetter) → ℝ :=
    fun w => localWordScaledTraceTerm (p := p) (q := q) N A L Q w
  let sA : Finset (Fin k → LocalExpansionLetter) :=
    Finset.univ.erase (localPureAWord k)
  let sAQ : Finset (Fin k → LocalExpansionLetter) :=
    sA.erase (localPureQWord k)
  have hAQ :
      localPureAWord k ≠ localPureQWord k :=
    localPureAWord_ne_localPureQWord (k := k) hk
  have hfilter :
      (Finset.univ.filter fun w : Fin k → LocalExpansionLetter => localWordIsMixed w) =
        sAQ := by
    ext w
    simp [sA, sAQ, localWordIsMixed_iff_ne_pureA_and_ne_pureQ, hAQ,
      and_comm, and_left_comm]
  have hsplit :
      (∑ w : Fin k → LocalExpansionLetter, t w) =
        t (localPureAWord k) + t (localPureQWord k) +
          ∑ w : Fin k → LocalExpansionLetter,
            if localWordIsMixed w then t w else 0 := by
    have hsumA :
        (∑ w : Fin k → LocalExpansionLetter, t w) =
          t (localPureAWord k) +
            sA.sum t := by
      simpa [sA] using
        (Finset.add_sum_erase
          (s := (Finset.univ : Finset (Fin k → LocalExpansionLetter)))
          (f := t)
          (a := localPureAWord k)
          (Finset.mem_univ _)).symm
    have hmemQ :
        localPureQWord k ∈ sA := by
      simpa [sA] using hAQ.symm
    have hsumQ :
        sA.sum t =
          t (localPureQWord k) +
            sAQ.sum t := by
      simpa [sAQ] using
        (Finset.add_sum_erase
          (s := sA)
          (f := t)
          (a := localPureQWord k)
          hmemQ).symm
    have hsumMixed :
        sAQ.sum t =
          ∑ w : Fin k → LocalExpansionLetter,
            if localWordIsMixed w then t w else 0 := by
      rw [← Finset.sum_filter]
      simp [hfilter]
    calc
      (∑ w : Fin k → LocalExpansionLetter, t w)
          = t (localPureAWord k) +
              sA.sum t := hsumA
      _ = t (localPureAWord k) +
            (t (localPureQWord k) + sAQ.sum t) := by
            rw [hsumQ]
      _ = t (localPureAWord k) + t (localPureQWord k) +
            ∑ w : Fin k → LocalExpansionLetter,
              if localWordIsMixed w then t w else 0 := by
            rw [hsumMixed]
            ring
  have hall :
      scaledTracePower (p := p) (q := q) N k (A + L + Q) =
        scaledTracePower (p := p) (q := q) N k A +
          scaledTracePower (p := p) (q := q) N k Q +
            localExpansionMixedWordSum (p := p) (q := q) N k A L Q := by
    rw [scaledTracePower_eq_sum_localWordScaledTraceTerm (p := p) (q := q) N k A L Q]
    rw [← localWordScaledTraceTerm_pureA (p := p) (q := q) N A L Q]
    rw [← localWordScaledTraceTerm_pureQ (p := p) (q := q) N A L Q]
    dsimp [t] at hsplit
    simpa [localExpansionMixedWordSum, localMixedWordFilteredSum] using hsplit
  unfold localExpansionMixedRemainder
  linarith

theorem localExpansionMixedRemainder_abs_le_of_wordBounds
    (N : ℝ) (k : ℕ) (A L Q : BipMatrix p q)
    (hk : 1 ≤ k)
    (bound : (Fin k → LocalExpansionLetter) → ℝ)
    (hWord :
      ∀ w : Fin k → LocalExpansionLetter,
        localWordIsMixed w →
          |localWordScaledTraceTerm (p := p) (q := q) N A L Q w| ≤ bound w) :
    |localExpansionMixedRemainder (p := p) (q := q) N k A L Q| ≤
      localMixedWordFilteredSum (k := k) bound := by
  classical
  rw [localExpansionMixedRemainder_eq_sum_mixedWordScaledTraceTerm
    (p := p) (q := q) N k A L Q hk]
  show |localExpansionMixedWordSum (p := p) (q := q) N k A L Q| ≤
    localMixedWordFilteredSum (k := k) bound
  unfold localExpansionMixedWordSum localMixedWordFilteredSum
  calc
    |∑ w : Fin k → LocalExpansionLetter,
        if localWordIsMixed w then
          localWordScaledTraceTerm (p := p) (q := q) N A L Q w
        else
          0| ≤
      ∑ w : Fin k → LocalExpansionLetter,
        |if localWordIsMixed w then
            localWordScaledTraceTerm (p := p) (q := q) N A L Q w
          else
            0| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ w : Fin k → LocalExpansionLetter,
        if localWordIsMixed w then bound w else 0 := by
          refine Finset.sum_le_sum ?_
          intro w _hw
          by_cases hm : localWordIsMixed w
          · simpa [hm] using hWord w hm
          · simp [hm]

/-- Scalar envelope assigned to a single word.

The envelope follows the Schatten/Hölder proof word by word.

* a single `L` defect is bounded with `‖L‖₁`;
* a single `Q` defect is bounded with `‖Q‖₁`;
* words with at least two defects are bounded with Hilbert--Schmidt norms for
  the defect letters.

Thus the scalar parameters are, in order, the bound on `‖A‖op`, the
Hilbert--Schmidt and trace bounds for `L`, and the Hilbert--Schmidt and trace
bounds for `Q`. -/
noncomputable def localExpansionMixedWordEnvelopeTerm
    (N Abound L2bound L1bound Q2bound Q1bound : ℝ) (k : ℕ)
    (w : Fin k → LocalExpansionLetter) : ℝ := by
  classical
  exact
    if localWordHasOneLinearDefect w then
      N ^ (k - 1) * Abound ^ (k - 1) * L1bound
    else if localWordHasOneQuadraticDefect w then
      N ^ (k - 1) * Abound ^ (k - 1) * Q1bound
    else
      N ^ (k - 1) *
        Abound ^ localWordLetterCount LocalExpansionLetter.A w *
          L2bound ^ localWordLetterCount LocalExpansionLetter.L w *
            Q2bound ^ localWordLetterCount LocalExpansionLetter.Q w

/-- Finite word-by-word envelope for the exact mixed remainder.

This is the non-opaque replacement for a single abstract `errMix`: every word
which is not the pure `A^k` or pure `Q^k` word receives its own scalar envelope,
and the mixed error is bounded by the finite sum of those envelopes. -/
noncomputable def localExpansionMixedWordEnvelope
    (N Abound L2bound L1bound Q2bound Q1bound : ℝ) (k : ℕ) : ℝ := by
  classical
  exact
    ∑ w : Fin k → LocalExpansionLetter,
      if localWordIsMixed w then
        localExpansionMixedWordEnvelopeTerm
          N Abound L2bound L1bound Q2bound Q1bound k w
      else
        0

/-- If every mixed word envelope is eventually arbitrarily small, then their
finite sum is eventually arbitrarily small.

This is the precise epsilon bookkeeping that turns the word-by-word
Schatten/Hölder estimates into `errMix_d → 0`. -/
theorem localExpansionMixedWordEnvelope_eventual_small
    {Nseq Abound L2bound L1bound Q2bound Q1bound : ℕ → ℝ} {k : ℕ}
    (hWordSmall :
      ∀ w : Fin k → LocalExpansionLetter,
        localWordIsMixed w →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop,
              localExpansionMixedWordEnvelopeTerm
                (Nseq d) (Abound d) (L2bound d) (L1bound d)
                (Q2bound d) (Q1bound d) k w ≤ η) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        localExpansionMixedWordEnvelope
          (Nseq d) (Abound d) (L2bound d) (L1bound d)
          (Q2bound d) (Q1bound d) k ≤ η := by
  intro η hη
  classical
  let cardWords : ℝ := Fintype.card (Fin k → LocalExpansionLetter)
  let eps : ℝ := η / (cardWords + 1)
  have hcard_nonneg : 0 ≤ cardWords := by
    dsimp [cardWords]
    positivity
  have hden_pos : 0 < cardWords + 1 := by
    linarith
  have heps_pos : 0 < eps := by
    exact div_pos hη hden_pos
  have hsum_eps : cardWords * eps ≤ η := by
    dsimp [eps]
    rw [← mul_div_assoc]
    rw [div_le_iff₀ hden_pos]
    nlinarith
  have hAll :
      ∀ᶠ d in atTop,
        ∀ w : Fin k → LocalExpansionLetter,
          if hw : localWordIsMixed w then
            localExpansionMixedWordEnvelopeTerm
              (Nseq d) (Abound d) (L2bound d) (L1bound d)
              (Q2bound d) (Q1bound d) k w ≤ eps
          else
            True := by
    rw [Filter.eventually_all]
    intro w
    by_cases hw : localWordIsMixed w
    · simpa [hw] using hWordSmall w hw eps heps_pos
    · exact Eventually.of_forall (fun _ => by simp [hw])
  filter_upwards [hAll] with d hd
  unfold localExpansionMixedWordEnvelope
  calc
    (∑ w : Fin k → LocalExpansionLetter,
        if localWordIsMixed w then
          localExpansionMixedWordEnvelopeTerm
            (Nseq d) (Abound d) (L2bound d) (L1bound d)
            (Q2bound d) (Q1bound d) k w
        else
          0)
        ≤ ∑ _w : Fin k → LocalExpansionLetter, eps := by
          refine Finset.sum_le_sum ?_
          intro w _
          by_cases hw : localWordIsMixed w
          · simpa [hw] using hd w
          · simp [hw, le_of_lt heps_pos]
    _ = cardWords * eps := by
          simp [cardWords]
    _ ≤ η := hsum_eps

theorem mixedRemainder_eventual_small_uniform_of_wordEnvelope
    {Nseq Abound L2bound L1bound Q2bound Q1bound : ℕ → ℝ}
    {M : ℕ → Set (SampleMatrix p q σ)} {k : ℕ}
    (hEnvelope :
      ∀ η : ℝ, 0 < η →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y : SampleMatrix p q σ⦄,
            Y ∈ M d →
            |localExpansionMixedRemainder (p := p) (q := q)
                (Nseq d) k
                (localBackground (p := p) (q := q) (σ := σ) Y)
                (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))| ≤
              localExpansionMixedWordEnvelope
                (Nseq d) (Abound d) (L2bound d) (L1bound d)
                (Q2bound d) (Q1bound d) k)
    (hWordSmall :
      ∀ w : Fin k → LocalExpansionLetter,
        localWordIsMixed w →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop,
              localExpansionMixedWordEnvelopeTerm
                (Nseq d) (Abound d) (L2bound d) (L1bound d)
                (Q2bound d) (Q1bound d) k w ≤ η) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        ∀ ⦃X Y : SampleMatrix p q σ⦄,
          Y ∈ M d →
          |localExpansionMixedRemainder (p := p) (q := q)
              (Nseq d) k
              (localBackground (p := p) (q := q) (σ := σ) Y)
              (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
              (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))| ≤ η := by
  intro η hη
  filter_upwards
    [hEnvelope η hη,
      localExpansionMixedWordEnvelope_eventual_small
        (Nseq := Nseq) (Abound := Abound) (L2bound := L2bound)
        (L1bound := L1bound) (Q2bound := Q2bound) (Q1bound := Q1bound)
        (k := k) hWordSmall η hη]
    with d hEnv hSmall
  intro X Y hY
  exact le_trans (hEnv hY) hSmall

/-- Word-by-word version of `mixedRemainder_eventual_small_of_schattenHolder_envelope`.

Instead of assuming an opaque sequence `errMix_d → 0`, it assumes:

* the exact mixed remainder is bounded by the explicit finite word envelope;
* every mixed word in that envelope is `o(1)`.

The exact mixed remainder then follows as `o(1)`. -/
theorem mixedRemainder_eventual_small_of_wordEnvelope
    {Nseq Abound L2bound L1bound Q2bound Q1bound : ℕ → ℝ}
    {A L Q : ℕ → BipMatrix p q} {k : ℕ}
    (hEnvelope :
      ∀ᶠ d in atTop,
        |localExpansionMixedRemainder (p := p) (q := q)
            (Nseq d) k (A d) (L d) (Q d)| ≤
          localExpansionMixedWordEnvelope
            (Nseq d) (Abound d) (L2bound d) (L1bound d)
            (Q2bound d) (Q1bound d) k)
    (hWordSmall :
      ∀ w : Fin k → LocalExpansionLetter,
        localWordIsMixed w →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop,
              localExpansionMixedWordEnvelopeTerm
                (Nseq d) (Abound d) (L2bound d) (L1bound d)
                (Q2bound d) (Q1bound d) k w ≤ η) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        |localExpansionMixedRemainder (p := p) (q := q)
            (Nseq d) k (A d) (L d) (Q d)| ≤ η := by
  intro η hη
  filter_upwards
    [hEnvelope,
      localExpansionMixedWordEnvelope_eventual_small
        (Nseq := Nseq) (Abound := Abound) (L2bound := L2bound)
        (L1bound := L1bound) (Q2bound := Q2bound) (Q1bound := Q1bound)
        (k := k) hWordSmall η hη]
    with d hEnv hSmall
  exact le_trans hEnv hSmall

/-- Local expansion bound obtained from the two Schatten/Hölder estimates:

* the pure quadratic word `Q^k` is controlled at the local radius;
* the exact mixed remainder is `o(1)`.

The conclusion is the deterministic upper-bound input

`|F(A+L+Q)-F(A)| ≤ a^k + o(1)`. -/
theorem localExpansion_eventual_bound_from_schattenHolder_radius
    {Nseq radius : ℕ → ℝ} {A L Q : ℕ → BipMatrix p q} {errMix : ℕ → ℝ}
    {a : ℝ} {k : ℕ}
    (hN : ∀ᶠ d in atTop, 0 ≤ Nseq d)
    (hk : 2 ≤ k)
    (hQHerm :
      ∀ᶠ d in atTop,
        (Q d).IsHermitian)
    (hQradius :
      ∀ᶠ d in atTop,
        frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) (Q d) ≤
          radius d)
    (hScale :
      ∀ η : ℝ, 0 < η →
        ∀ᶠ d in atTop,
          Nseq d ^ (k - 1) * radius d ^ k ≤ a ^ k + η)
    (hMixedEnvelope :
      ∀ᶠ d in atTop,
        |localExpansionMixedRemainder (p := p) (q := q)
            (Nseq d) k (A d) (L d) (Q d)| ≤ errMix d)
    (hMixedSmall :
      ∀ η : ℝ, 0 < η →
        ∀ᶠ d in atTop, errMix d ≤ η) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        |scaledTracePower (p := p) (q := q) (Nseq d) k
              (A d + L d + Q d) -
            scaledTracePower (p := p) (q := q) (Nseq d) k (A d)| ≤
          a ^ k + η := by
  exact
    localExpansion_eventual_bound
      (p := p) (q := q) (Nseq := Nseq) (A := A) (L := L) (Q := Q)
      (a := a) (k := k)
      (pureQuadratic_eventual_bound_from_schattenHolder_radius
        (p := p) (q := q) (Nseq := Nseq) (radius := radius)
        (Q := Q) (a := a) (k := k)
        hN hk hQHerm hQradius hScale)
      (mixedRemainder_eventual_small_of_schattenHolder_envelope
        (p := p) (q := q) (Nseq := Nseq) (A := A) (L := L) (Q := Q)
        (errMix := errMix) (k := k) hMixedEnvelope hMixedSmall)

/-- Local expansion bound with the mixed part controlled word-by-word.

This is the non-opaque version of
`localExpansion_eventual_bound_from_schattenHolder_radius`: the mixed remainder
is bounded by the explicit finite sum over `A/L/Q` words, and each word
envelope is proved separately to be `o(1)`. -/
theorem localExpansion_eventual_bound_from_schattenHolder_wordEnvelope
    {Nseq radius Abound L2bound L1bound Q2bound Q1bound : ℕ → ℝ}
    {A L Q : ℕ → BipMatrix p q} {a : ℝ} {k : ℕ}
    (hN : ∀ᶠ d in atTop, 0 ≤ Nseq d)
    (hk : 2 ≤ k)
    (hQHerm :
      ∀ᶠ d in atTop,
        (Q d).IsHermitian)
    (hQradius :
      ∀ᶠ d in atTop,
        frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) (Q d) ≤
          radius d)
    (hScale :
      ∀ η : ℝ, 0 < η →
        ∀ᶠ d in atTop,
          Nseq d ^ (k - 1) * radius d ^ k ≤ a ^ k + η)
    (hMixedEnvelope :
      ∀ᶠ d in atTop,
        |localExpansionMixedRemainder (p := p) (q := q)
            (Nseq d) k (A d) (L d) (Q d)| ≤
          localExpansionMixedWordEnvelope
            (Nseq d) (Abound d) (L2bound d) (L1bound d)
            (Q2bound d) (Q1bound d) k)
    (hWordSmall :
      ∀ w : Fin k → LocalExpansionLetter,
        localWordIsMixed w →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop,
              localExpansionMixedWordEnvelopeTerm
                (Nseq d) (Abound d) (L2bound d) (L1bound d)
                (Q2bound d) (Q1bound d) k w ≤ η) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        |scaledTracePower (p := p) (q := q) (Nseq d) k
              (A d + L d + Q d) -
            scaledTracePower (p := p) (q := q) (Nseq d) k (A d)| ≤
          a ^ k + η := by
  exact
    localExpansion_eventual_bound
      (p := p) (q := q) (Nseq := Nseq) (A := A) (L := L) (Q := Q)
      (a := a) (k := k)
      (pureQuadratic_eventual_bound_from_schattenHolder_radius
        (p := p) (q := q) (Nseq := Nseq) (radius := radius)
        (Q := Q) (a := a) (k := k)
        hN hk hQHerm hQradius hScale)
      (mixedRemainder_eventual_small_of_wordEnvelope
        (p := p) (q := q) (Nseq := Nseq) (Abound := Abound)
        (L2bound := L2bound) (L1bound := L1bound)
        (Q2bound := Q2bound) (Q1bound := Q1bound)
        (A := A) (L := L) (Q := Q) (k := k)
        hMixedEnvelope hWordSmall)

end LocalExpansionAlgebra

/-! ## Background typical set `K_N` -/

section BackgroundTypicalSet

variable [Fintype p] [Fintype q] [Fintype σ]
variable [DecidableEq p] [DecidableEq q]

/-- The normalized partially-transposed moment functional used in the
background typical set:

`F_N(Y) = N^(k-1) Re Tr(((YY*)^Γ)^k)`. -/
noncomputable def backgroundMomentValue
    (N : ℝ) (k : ℕ) (Y : SampleMatrix p q σ) : ℝ :=
  scaledTracePower (p := p) (q := q) N k (gamma (densityMatrix Y))

/-- A sample matrix is recovered at the density-matrix level from its normalized
version by multiplying by the squared Frobenius norm. -/
theorem densityMatrix_eq_norm_sq_smul_densityMatrix_normalized
    [DecidableEq σ]
    (Y : SampleMatrix p q σ) :
    densityMatrix (p := p) (q := q) (σ := σ) Y =
      ((frobeniusNorm (p := p) (q := q) (σ := σ) Y ^ 2 : ℝ) : ℂ) •
        densityMatrix (p := p) (q := q) (σ := σ)
          (((frobeniusNorm (p := p) (q := q) (σ := σ) Y)⁻¹ : ℂ) • Y) := by
  by_cases hY : frobeniusNorm (p := p) (q := q) (σ := σ) Y = 0
  · have hzero : Y = 0 := by
      exact norm_eq_zero.mp hY
    simp [densityMatrix, frobeniusNorm, hzero]
  · rw [densityMatrix_smul]
    ext i j
    have hn : ‖Y‖ ≠ 0 := by
      simpa [frobeniusNorm] using hY
    simp [frobeniusNorm, mul_assoc, mul_left_comm]
    field_simp [hn]

/-- Exact scaling of the deleted-column background matrix by the complement
Frobenius mass. -/
theorem columnBackgroundMatrix_eq_norm_sq_smul_normalized
    [DecidableEq σ] {α₀ : σ} (X : SampleMatrix p q σ) :
    columnBackgroundMatrix (p := p) (q := q) (σ := σ) X α₀ =
      ((frobeniusNorm (p := p) (q := q) (σ := σ)
            (sampleColumnComplement (p := p) (q := q) (σ := σ) X α₀) ^ 2 : ℝ) :
          ℂ) •
        gamma (densityMatrix
          (sampleColumnComplementNormalized (p := p) (q := q) (σ := σ) X α₀)) := by
  unfold columnBackgroundMatrix sampleColumnComplementNormalized
  rw [densityMatrix_eq_norm_sq_smul_densityMatrix_normalized
    (p := p) (q := q) (σ := σ)
    (Y := sampleColumnComplement (p := p) (q := q) (σ := σ) X α₀)]
  ext i j
  simp [gamma, Matrix.partialTranspose]

/-- Exact scaling identity for the deleted-column background contribution.

The remaining background lower-bound work is scalar: one must lower-bound the
factor `‖X_{≠α₀}‖₂^(2k)` on the favourable event and control the sign/size of
the normalized background moment. -/
theorem columnBackgroundContribution_eq_norm_pow_mul_backgroundMomentValue_normalized
    [DecidableEq σ] {α₀ : σ} (N : ℝ) (k : ℕ)
    (X : SampleMatrix p q σ) :
    columnBackgroundContribution (p := p) (q := q) (σ := σ) N k X α₀ =
      frobeniusNorm (p := p) (q := q) (σ := σ)
          (sampleColumnComplement (p := p) (q := q) (σ := σ) X α₀) ^ (2 * k) *
        backgroundMomentValue (p := p) (q := q) (σ := σ) N k
          (sampleColumnComplementNormalized (p := p) (q := q) (σ := σ) X α₀) := by
  unfold columnBackgroundContribution backgroundMomentValue
  rw [columnBackgroundMatrix_eq_norm_sq_smul_normalized
    (p := p) (q := q) (σ := σ) (α₀ := α₀) X]
  rw [scaledTracePower_real_smul_eq_pureSpikeContribution]
  unfold pureSpikeContribution scaledTracePower
  rw [pow_mul]
  ring

/-- Measurability of the normalized moment functional defining the background
typical set. -/
theorem measurable_backgroundMomentValue
    (N : ℝ) (k : ℕ) :
    Measurable
      (fun Y : SampleMatrix p q σ =>
        backgroundMomentValue (p := p) (q := q) (σ := σ) N k Y) := by
  classical
  have hbase :
      ∀ i j : BipIndex p q,
        Measurable fun Y : SampleMatrix p q σ =>
          (gamma (densityMatrix Y)) i j := by
    intro i j
    unfold gamma densityMatrix
    simp [Matrix.partialTranspose, Matrix.mul_apply]
    fun_prop
  have hpow :
      ∀ n : ℕ, ∀ i j : BipIndex p q,
        Measurable fun Y : SampleMatrix p q σ =>
          ((gamma (densityMatrix Y)) ^ n) i j := by
    intro n
    induction n with
    | zero =>
        intro i j
        simp
    | succ n ih =>
        intro i j
        simpa [pow_succ, Matrix.mul_apply] using
          (Finset.measurable_sum _ fun l _ =>
            (ih i l).mul (hbase l j))
  have htrace :
      Measurable fun Y : SampleMatrix p q σ =>
        Matrix.trace ((gamma (densityMatrix Y)) ^ k) := by
    unfold Matrix.trace
    exact Finset.measurable_sum _ fun i _ => hpow k i i
  have htrace_re :
      Measurable fun Y : SampleMatrix p q σ =>
        (Matrix.trace ((gamma (densityMatrix Y)) ^ k)).re :=
    (RCLike.continuous_re (K := ℂ)).measurable.comp htrace
  unfold backgroundMomentValue scaledTracePower
  exact (measurable_const.mul htrace_re)

/-- The moment-typical part of `K_N`: the background moment is within `τ` of
the chosen centering value `mean`. -/
noncomputable def backgroundMomentTypicalSet
    (N τ mean : ℝ) (k : ℕ) : Set (SampleMatrix p q σ) :=
  {Y | |backgroundMomentValue (p := p) (q := q) (σ := σ) N k Y - mean| ≤ τ}

/-- The sample-operator-norm part of `K_N`:

`‖Y‖op ≤ M / sqrt(N)`. -/
noncomputable def backgroundSampleOpNormGoodSet
    (N M : ℝ) : Set (SampleMatrix p q σ) :=
  {Y |
    PptFactorization.HighProbabilityBounds.sampleOpNorm
      (p := p) (q := q) (σ := σ) Y ≤ M / Real.sqrt N}

/-- The partial-transpose operator-norm part of `K_N`:

`‖(YY*)^Γ‖op ≤ M / N`. -/
noncomputable def backgroundGammaOpNormGoodSet
    (N M : ℝ) : Set (SampleMatrix p q σ) :=
  {Y | opNorm (p := p) (q := q) (gamma (densityMatrix Y)) ≤ M / N}

/-- The background typical set used in the upper-bound strategy.

This is the formal version of

`K_N = {|F_N(Y)-mean| ≤ τ,
        ‖Y‖op ≤ M/sqrt(N),
        ‖(YY*)^Γ‖op ≤ M/N}`. -/
noncomputable def backgroundTypicalSet
    (N M τ mean : ℝ) (k : ℕ) : Set (SampleMatrix p q σ) :=
  {Y |
    |backgroundMomentValue (p := p) (q := q) (σ := σ) N k Y - mean| ≤ τ ∧
    PptFactorization.HighProbabilityBounds.sampleOpNorm
      (p := p) (q := q) (σ := σ) Y ≤ M / Real.sqrt N ∧
    opNorm (p := p) (q := q) (gamma (densityMatrix Y)) ≤ M / N}

@[simp] theorem mem_backgroundTypicalSet_iff
    {N M τ mean : ℝ} {k : ℕ} {Y : SampleMatrix p q σ} :
    Y ∈ backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k ↔
      |backgroundMomentValue (p := p) (q := q) (σ := σ) N k Y - mean| ≤ τ ∧
      PptFactorization.HighProbabilityBounds.sampleOpNorm
        (p := p) (q := q) (σ := σ) Y ≤ M / Real.sqrt N ∧
      opNorm (p := p) (q := q) (gamma (densityMatrix Y)) ≤ M / N := by
  rfl

theorem backgroundTypicalSet_moment_bound
    {N M τ mean : ℝ} {k : ℕ} {Y : SampleMatrix p q σ}
    (hY : Y ∈ backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k) :
    |backgroundMomentValue (p := p) (q := q) (σ := σ) N k Y - mean| ≤ τ :=
  hY.1

theorem backgroundTypicalSet_sampleOpNorm_bound
    {N M τ mean : ℝ} {k : ℕ} {Y : SampleMatrix p q σ}
    (hY : Y ∈ backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k) :
    PptFactorization.HighProbabilityBounds.sampleOpNorm
      (p := p) (q := q) (σ := σ) Y ≤ M / Real.sqrt N :=
  hY.2.1

/-- Measurability of the full background typical set `K_N`. -/
theorem measurableSet_backgroundTypicalSet
    (N M τ mean : ℝ) (k : ℕ) :
    MeasurableSet
      (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k) := by
  unfold backgroundTypicalSet
  refine
    (measurableSet_le
      (((measurable_backgroundMomentValue
        (p := p) (q := q) (σ := σ) N k).sub measurable_const).norm)
      measurable_const).inter ?_
  refine
    (measurableSet_le
      (PptFactorization.HighProbabilityBounds.sampleOpNorm_continuous
        (p := p) (q := q) (σ := σ)).measurable
      measurable_const).inter ?_
  change MeasurableSet
    {Y : SampleMatrix p q σ |
      sphericalGammaOpNorm (p := p) (q := q) (σ := σ) Y ≤ M / N}
  exact measurableSet_le
    (continuous_sphericalGammaOpNorm (p := p) (q := q) (σ := σ)).measurable
    measurable_const

theorem backgroundTypicalSet_gammaOpNorm_bound
    {N M τ mean : ℝ} {k : ℕ} {Y : SampleMatrix p q σ}
    (hY : Y ∈ backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k) :
    opNorm (p := p) (q := q) (gamma (densityMatrix Y)) ≤ M / N :=
  hY.2.2

/-- The moment component of background typicality gives the lower side of the
background moment bound. -/
theorem backgroundMomentValue_lower_of_backgroundTypicalSet
    {N M τ mean : ℝ} {k : ℕ} {Y : SampleMatrix p q σ}
    (hY : Y ∈ backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k) :
    mean - τ ≤ backgroundMomentValue (p := p) (q := q) (σ := σ) N k Y := by
  have hAbs :=
    backgroundTypicalSet_moment_bound
      (p := p) (q := q) (σ := σ) (N := N) (M := M)
      (τ := τ) (mean := mean) (k := k) hY
  have hLower := (abs_le.mp hAbs).1
  linarith

/-- Pointwise background implication for the one-column lower bound.

If the normalized deleted-column matrix is in the concrete background typical set
and the normalized background moment transfers to the unnormalized deleted-column
background contribution up to `errScale`, then the background contribution is
bounded below by `center - (τ + errScale)`. -/
theorem columnBackgroundContribution_lower_of_normalizedDeletedBackground_typical
    [DecidableEq σ]
    {α₀ : σ} {N M τ center errScale : ℝ} {k : ℕ}
    {X : SampleMatrix p q σ}
    (hTypical :
      sampleColumnComplementNormalized (p := p) (q := q) (σ := σ) X α₀ ∈
        backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ center k)
    (hTransfer :
      backgroundMomentValue (p := p) (q := q) (σ := σ) N k
          (sampleColumnComplementNormalized (p := p) (q := q) (σ := σ) X α₀) -
          errScale ≤
        columnBackgroundContribution (p := p) (q := q) (σ := σ) N k X α₀) :
    center - (τ + errScale) ≤
      columnBackgroundContribution (p := p) (q := q) (σ := σ) N k X α₀ := by
  have hMomentLower :
      center - τ ≤
        backgroundMomentValue (p := p) (q := q) (σ := σ) N k
          (sampleColumnComplementNormalized (p := p) (q := q) (σ := σ) X α₀) :=
    backgroundMomentValue_lower_of_backgroundTypicalSet
      (p := p) (q := q) (σ := σ) (N := N) (M := M)
      (τ := τ) (mean := center) (k := k) hTypical
  linarith

/-- Set-level specialization of background typicality for the normalized deleted
matrix.  This is the component implication fed into
`sphericalOneColumnFavorableEvent_subset_certificate_of_three_implications`. -/
theorem normalizedDeletedBackgroundTypicalEvent_subset_backgroundContributionLowerBoundSet
    [DecidableEq σ]
    {α₀ : σ} {N M τ center errScale : ℝ} {k : ℕ}
    (hTransfer :
      ∀ X : SampleMatrix p q σ,
        sampleColumnComplementNormalized (p := p) (q := q) (σ := σ) X α₀ ∈
          backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ center k →
        backgroundMomentValue (p := p) (q := q) (σ := σ) N k
            (sampleColumnComplementNormalized (p := p) (q := q) (σ := σ) X α₀) -
            errScale ≤
          columnBackgroundContribution (p := p) (q := q) (σ := σ) N k X α₀) :
    normalizedDeletedBackgroundEvent
        (p := p) (q := q) (σ := σ) α₀
        (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ center k) ⊆
      columnBackgroundContributionLowerBoundSet
        (p := p) (q := q) (σ := σ) α₀ N center (τ + errScale) k := by
  intro X hX
  exact
    columnBackgroundContribution_lower_of_normalizedDeletedBackground_typical
      (p := p) (q := q) (σ := σ)
      (α₀ := α₀) (N := N) (M := M) (τ := τ)
      (center := center) (errScale := errScale) (k := k)
      (X := X) hX (hTransfer X hX)

/-- Background-typicality implication with the scalar error budget separated.

The normalized-background transfer gives the error `τ + errScale`; the scalar
hypothesis widens it to the certificate error `errBg`. -/
theorem normalizedDeletedBackgroundTypicalEvent_subset_backgroundContributionLowerBoundSet_of_error_budget
    [DecidableEq σ]
    {α₀ : σ} {N M τ center errScale errBg : ℝ} {k : ℕ}
    (hTransfer :
      ∀ X : SampleMatrix p q σ,
        sampleColumnComplementNormalized (p := p) (q := q) (σ := σ) X α₀ ∈
          backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ center k →
        backgroundMomentValue (p := p) (q := q) (σ := σ) N k
            (sampleColumnComplementNormalized (p := p) (q := q) (σ := σ) X α₀) -
            errScale ≤
          columnBackgroundContribution (p := p) (q := q) (σ := σ) N k X α₀)
    (hError : τ + errScale ≤ errBg) :
    normalizedDeletedBackgroundEvent
        (p := p) (q := q) (σ := σ) α₀
        (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ center k) ⊆
      columnBackgroundContributionLowerBoundSet
        (p := p) (q := q) (σ := σ) α₀ N center errBg k :=
  Set.Subset.trans
    (normalizedDeletedBackgroundTypicalEvent_subset_backgroundContributionLowerBoundSet
      (p := p) (q := q) (σ := σ)
      (α₀ := α₀) (N := N) (M := M) (τ := τ)
      (center := center) (errScale := errScale) (k := k)
      hTransfer)
    (columnBackgroundContributionLowerBoundSet_mono_error
      (p := p) (q := q) (σ := σ)
      (α₀ := α₀) (N := N) (center := center)
      (errSmall := τ + errScale) (errBig := errBg) (k := k)
      hError)

/-- Concrete event inclusion into the one-column upper-tail certificate.

This closes the deterministic `hE` used by the probability pipeline.  The
favourable event is exactly the concrete one-column event:

* column mass in the Beta interval;
* column direction in the cap;
* normalized deleted-column background in `K_N`.

The proof is assembled from the three primitive implications:

* mass + cap imply the pure-spike lower bound;
* deleted-background typicality implies the background lower bound;
* the mixed-remainder envelope implies the mixed lower bound. -/
theorem sphericalOneColumnFavorableEvent_subset_certificate_of_concrete_implications
    [DecidableEq σ]
    {α₀ : σ}
    {q₀ δ N M a center errProfile errTransfer errSpike τ errScale errBg
      errMix : ℝ}
    {k : ℕ}
    {directionSet : Set (EuclideanSpace ℂ (BipIndex p q))}
    (hProfile :
      ∀ R : ℝ, ∀ u : EuclideanSpace ℂ (BipIndex p q),
        R ∈ betaColumnIntervalSet q₀ δ →
        u ∈ directionSet →
        a ^ k - errProfile ≤
          columnDirectionSpikeProfile (p := p) (q := q) N k R u)
    (hSpikeTransfer :
      ∀ X : SampleMatrix p q σ,
        X ∈ columnMassCapEvent
          (p := p) (q := q) (σ := σ) α₀ q₀ δ directionSet →
        columnDirectionSpikeProfile (p := p) (q := q) N k
            (sampleColumnMass (p := p) (q := q) (σ := σ) X α₀)
            (sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀) -
            errTransfer ≤
          columnSpikeContribution (p := p) (q := q) (σ := σ) N k X α₀)
    (hPureError : errProfile + errTransfer ≤ errSpike)
    (hBackgroundTransfer :
      ∀ X : SampleMatrix p q σ,
        sampleColumnComplementNormalized (p := p) (q := q) (σ := σ) X α₀ ∈
          backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ center k →
        backgroundMomentValue (p := p) (q := q) (σ := σ) N k
            (sampleColumnComplementNormalized (p := p) (q := q) (σ := σ) X α₀) -
            errScale ≤
          columnBackgroundContribution (p := p) (q := q) (σ := σ) N k X α₀)
    (hBackgroundError : τ + errScale ≤ errBg)
    (hMixedEnvelope :
      sphericalOneColumnFavorableEvent
          (p := p) (q := q) (σ := σ)
          α₀ q₀ δ directionSet
          (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ center k) ⊆
        columnMixedRemainderEnvelopeSet
          (p := p) (q := q) (σ := σ) α₀ N errMix k) :
    sphericalOneColumnFavorableEvent
        (p := p) (q := q) (σ := σ)
        α₀ q₀ δ directionSet
        (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ center k) ⊆
      columnSpikeUpperTailCertificateSet
        (p := p) (q := q) (σ := σ)
        α₀ N a center errSpike errBg errMix k := by
  refine
    sphericalOneColumnFavorableEvent_subset_certificate_of_three_implications
      (α₀ := α₀) (q₀ := q₀) (δ := δ) (N := N) (a := a)
      (center := center) (errSpike := errSpike) (errBg := errBg)
      (errMix := errMix) (k := k) (directionSet := directionSet)
      (backgroundSet :=
        backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ center k)
      ?_ ?_ hMixedEnvelope
  · exact
      columnMassCapEvent_subset_pureSpikeLowerBoundSet_of_error_budget
        (α₀ := α₀) (N := N) (a := a)
        (errProfile := errProfile) (errTransfer := errTransfer)
        (errSpike := errSpike) (q₀ := q₀) (δ := δ) (k := k)
        (directionSet := directionSet)
        hProfile hSpikeTransfer hPureError
  · exact
      normalizedDeletedBackgroundTypicalEvent_subset_backgroundContributionLowerBoundSet_of_error_budget
        (α₀ := α₀) (N := N) (M := M) (τ := τ)
        (center := center) (errScale := errScale) (errBg := errBg)
        (k := k)
        hBackgroundTransfer hBackgroundError

/-- Concrete one-column favourable event inclusion into the upper-tail event.

This is the deterministic inclusion that supplies the event-level content of
`hColumnIncluded` in the lower-bound pipeline. -/
theorem sphericalOneColumnFavorableEvent_subset_upperTailSet_of_concrete_implications
    [DecidableEq σ]
    {α₀ : σ}
    {q₀ δ N M a eps mean center errProfile errTransfer errSpike τ errScale
      errBg errMix errMean : ℝ}
    {k : ℕ}
    {directionSet : Set (EuclideanSpace ℂ (BipIndex p q))}
    (hProfile :
      ∀ R : ℝ, ∀ u : EuclideanSpace ℂ (BipIndex p q),
        R ∈ betaColumnIntervalSet q₀ δ →
        u ∈ directionSet →
        a ^ k - errProfile ≤
          columnDirectionSpikeProfile (p := p) (q := q) N k R u)
    (hSpikeTransfer :
      ∀ X : SampleMatrix p q σ,
        X ∈ columnMassCapEvent
          (p := p) (q := q) (σ := σ) α₀ q₀ δ directionSet →
        columnDirectionSpikeProfile (p := p) (q := q) N k
            (sampleColumnMass (p := p) (q := q) (σ := σ) X α₀)
            (sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀) -
            errTransfer ≤
          columnSpikeContribution (p := p) (q := q) (σ := σ) N k X α₀)
    (hPureError : errProfile + errTransfer ≤ errSpike)
    (hBackgroundTransfer :
      ∀ X : SampleMatrix p q σ,
        sampleColumnComplementNormalized (p := p) (q := q) (σ := σ) X α₀ ∈
          backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ center k →
        backgroundMomentValue (p := p) (q := q) (σ := σ) N k
            (sampleColumnComplementNormalized (p := p) (q := q) (σ := σ) X α₀) -
            errScale ≤
          columnBackgroundContribution (p := p) (q := q) (σ := σ) N k X α₀)
    (hBackgroundError : τ + errScale ≤ errBg)
    (hMixedEnvelope :
      sphericalOneColumnFavorableEvent
          (p := p) (q := q) (σ := σ)
          α₀ q₀ δ directionSet
          (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ center k) ⊆
        columnMixedRemainderEnvelopeSet
          (p := p) (q := q) (σ := σ) α₀ N errMix k)
    (hMean : mean ≤ center + errMean)
    (hBudget : eps + errSpike + errBg + errMix + errMean ≤ a ^ k) :
    sphericalOneColumnFavorableEvent
        (p := p) (q := q) (σ := σ)
        α₀ q₀ δ directionSet
        (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ center k) ⊆
      columnMomentUpperTailSet (p := p) (q := q) (σ := σ) N eps mean k :=
  sphericalOneColumnFavorableEvent_subset_upperTailSet_of_three_blocks
    (α₀ := α₀) (q₀ := q₀) (δ := δ) (N := N) (a := a)
    (eps := eps) (mean := mean) (center := center)
    (errSpike := errSpike) (errBg := errBg) (errMix := errMix)
    (errMean := errMean) (k := k) (directionSet := directionSet)
    (backgroundSet :=
      backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ center k)
    (by
      have hPureBlock :
          columnMassCapEvent (p := p) (q := q) (σ := σ)
              α₀ q₀ δ directionSet ⊆
            columnPureSpikeLowerBoundSet
              (p := p) (q := q) (σ := σ) α₀ N a errSpike k :=
        columnMassCapEvent_subset_pureSpikeLowerBoundSet_of_error_budget
          (α₀ := α₀) (N := N) (a := a)
          (errProfile := errProfile) (errTransfer := errTransfer)
          (errSpike := errSpike) (q₀ := q₀) (δ := δ) (k := k)
          (directionSet := directionSet)
          hProfile hSpikeTransfer hPureError
      intro X hX
      exact hPureBlock ⟨hX.1, hX.2.1⟩)
    (by
      have hBackgroundBlock :
          normalizedDeletedBackgroundEvent
              (p := p) (q := q) (σ := σ) α₀
              (backgroundTypicalSet
                (p := p) (q := q) (σ := σ) N M τ center k) ⊆
            columnBackgroundContributionLowerBoundSet
              (p := p) (q := q) (σ := σ) α₀ N center errBg k :=
        normalizedDeletedBackgroundTypicalEvent_subset_backgroundContributionLowerBoundSet_of_error_budget
          (α₀ := α₀) (N := N) (M := M) (τ := τ)
          (center := center) (errScale := errScale) (errBg := errBg)
          (k := k)
          hBackgroundTransfer hBackgroundError
      intro X hX
      exact hBackgroundBlock hX.2.2)
    hMixedEnvelope hMean hBudget

/-- Scalar probability comparison for the concrete one-column favourable event.

This is the closed form of the `hColumnIncluded` ingredient for the lower-bound
pipeline when `columnProb` is the probability of the concrete event

`mass interval ∩ cap ∩ deleted-background typicality`

and `targetProb` is the upper-tail probability. -/
theorem columnProb_le_upperTailProb_of_concrete_favorable_event
    [MeasurableSpace (SampleMatrix p q σ)] [DecidableEq σ]
    {μ : Measure (SampleMatrix p q σ)}
    [IsFiniteMeasure μ]
    {columnProb targetProb : ℝ}
    {α₀ : σ}
    {q₀ δ N M a eps mean center errProfile errTransfer errSpike τ errScale
      errBg errMix errMean : ℝ}
    {k : ℕ}
    {directionSet : Set (EuclideanSpace ℂ (BipIndex p q))}
    (hColumnProb :
      columnProb =
        μ.real
          (sphericalOneColumnFavorableEvent
            (p := p) (q := q) (σ := σ)
            α₀ q₀ δ directionSet
            (backgroundTypicalSet (p := p) (q := q) (σ := σ)
              N M τ center k)))
    (hTargetProb :
      targetProb =
        μ.real
          (columnMomentUpperTailSet
            (p := p) (q := q) (σ := σ) N eps mean k))
    (hProfile :
      ∀ R : ℝ, ∀ u : EuclideanSpace ℂ (BipIndex p q),
        R ∈ betaColumnIntervalSet q₀ δ →
        u ∈ directionSet →
        a ^ k - errProfile ≤
          columnDirectionSpikeProfile (p := p) (q := q) N k R u)
    (hSpikeTransfer :
      ∀ X : SampleMatrix p q σ,
        X ∈ columnMassCapEvent
          (p := p) (q := q) (σ := σ) α₀ q₀ δ directionSet →
        columnDirectionSpikeProfile (p := p) (q := q) N k
            (sampleColumnMass (p := p) (q := q) (σ := σ) X α₀)
            (sampleColumnDirection (p := p) (q := q) (σ := σ) X α₀) -
            errTransfer ≤
          columnSpikeContribution (p := p) (q := q) (σ := σ) N k X α₀)
    (hPureError : errProfile + errTransfer ≤ errSpike)
    (hBackgroundTransfer :
      ∀ X : SampleMatrix p q σ,
        sampleColumnComplementNormalized (p := p) (q := q) (σ := σ) X α₀ ∈
          backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ center k →
        backgroundMomentValue (p := p) (q := q) (σ := σ) N k
            (sampleColumnComplementNormalized (p := p) (q := q) (σ := σ) X α₀) -
            errScale ≤
          columnBackgroundContribution (p := p) (q := q) (σ := σ) N k X α₀)
    (hBackgroundError : τ + errScale ≤ errBg)
    (hMixedEnvelope :
      sphericalOneColumnFavorableEvent
          (p := p) (q := q) (σ := σ)
          α₀ q₀ δ directionSet
          (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ center k) ⊆
        columnMixedRemainderEnvelopeSet
          (p := p) (q := q) (σ := σ) α₀ N errMix k)
    (hMean : mean ≤ center + errMean)
    (hBudget : eps + errSpike + errBg + errMix + errMean ≤ a ^ k) :
    columnProb ≤ targetProb := by
  exact
    columnProb_le_upperTailProb_of_subset_certificate
      (μ := μ)
      (E :=
        sphericalOneColumnFavorableEvent
          (p := p) (q := q) (σ := σ)
          α₀ q₀ δ directionSet
          (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ center k))
      (columnProb := columnProb) (targetProb := targetProb)
      (α₀ := α₀) (N := N) (a := a) (eps := eps) (mean := mean)
      (center := center) (errSpike := errSpike) (errBg := errBg)
      (errMix := errMix) (errMean := errMean) (k := k)
      hColumnProb hTargetProb
      (sphericalOneColumnFavorableEvent_subset_certificate_of_concrete_implications
        (α₀ := α₀) (q₀ := q₀) (δ := δ) (N := N) (M := M)
        (a := a) (center := center) (errProfile := errProfile)
        (errTransfer := errTransfer) (errSpike := errSpike)
        (τ := τ) (errScale := errScale) (errBg := errBg)
        (errMix := errMix) (k := k) (directionSet := directionSet)
      hProfile hSpikeTransfer hPureError
        hBackgroundTransfer hBackgroundError hMixedEnvelope)
      hMean hBudget

set_option linter.unusedSectionVars false in
/-- Scalar probability comparison for the concrete one-column favourable event,
with the pure-spike transfer closed no-input and the mixed block supplied in
its natural pointwise form.

This is the deterministic lower-bound inclusion in its cleanest scalar shape:
the favourable column event is measured directly under `μ`, and if the three
deterministic blocks hold with the stated budgets, then its probability is
bounded by the target upper-tail probability. -/
theorem columnProb_le_upperTailProb_of_closed_deterministic_blocks
    [MeasurableSpace (SampleMatrix p q σ)] [DecidableEq σ]
    {μ : Measure (SampleMatrix p q σ)}
    [IsFiniteMeasure μ]
    {columnProb targetProb : ℝ}
    {α₀ : σ}
    {q₀ δ N M a eps mean center errProfile errSpike τ errScale
      errBg errMix errMean : ℝ}
    {k : ℕ}
    {directionSet : Set (EuclideanSpace ℂ (BipIndex p q))}
    (hColumnProb :
      columnProb =
        μ.real
          (sphericalOneColumnFavorableEvent
            (p := p) (q := q) (σ := σ)
            α₀ q₀ δ directionSet
            (backgroundTypicalSet (p := p) (q := q) (σ := σ)
              N M τ center k)))
    (hTargetProb :
      targetProb =
        μ.real
          (columnMomentUpperTailSet
            (p := p) (q := q) (σ := σ) N eps mean k))
    (hProfile :
      ∀ R : ℝ, ∀ u : EuclideanSpace ℂ (BipIndex p q),
        R ∈ betaColumnIntervalSet q₀ δ →
        u ∈ directionSet →
        a ^ k - errProfile ≤
          columnDirectionSpikeProfile (p := p) (q := q) N k R u)
    (hPureError : errProfile + 0 ≤ errSpike)
    (hBackgroundTransfer :
      ∀ X : SampleMatrix p q σ,
        sampleColumnComplementNormalized (p := p) (q := q) (σ := σ) X α₀ ∈
          backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ center k →
        backgroundMomentValue (p := p) (q := q) (σ := σ) N k
            (sampleColumnComplementNormalized (p := p) (q := q) (σ := σ) X α₀) -
            errScale ≤
          columnBackgroundContribution (p := p) (q := q) (σ := σ) N k X α₀)
    (hBackgroundError : τ + errScale ≤ errBg)
    (hMixed :
      ∀ X : SampleMatrix p q σ,
        X ∈ sphericalOneColumnFavorableEvent
          (p := p) (q := q) (σ := σ)
          α₀ q₀ δ directionSet
          (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ center k) →
        |columnMixedRemainder (p := p) (q := q) (σ := σ) N k X α₀| ≤
          errMix)
    (hMean : mean ≤ center + errMean)
    (hBudget : eps + errSpike + errBg + errMix + errMean ≤ a ^ k) :
    columnProb ≤ targetProb := by
  exact
    columnProb_le_upperTailProb_of_subset_certificate
      (p := p) (q := q) (σ := σ)
      (μ := μ)
      (E :=
        sphericalOneColumnFavorableEvent
          (p := p) (q := q) (σ := σ)
          α₀ q₀ δ directionSet
          (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ center k))
      (columnProb := columnProb) (targetProb := targetProb)
      (α₀ := α₀) (N := N) (a := a) (eps := eps) (mean := mean)
      (center := center) (errSpike := errSpike) (errBg := errBg)
      (errMix := errMix) (errMean := errMean) (k := k)
      hColumnProb hTargetProb
      (sphericalOneColumnFavorableEvent_subset_certificate_of_concrete_implications
        (p := p) (q := q) (σ := σ)
        (α₀ := α₀) (q₀ := q₀) (δ := δ) (N := N) (M := M)
        (a := a) (center := center) (errProfile := errProfile)
        (errTransfer := 0) (errSpike := errSpike)
        (τ := τ) (errScale := errScale) (errBg := errBg)
        (errMix := errMix) (k := k) (directionSet := directionSet)
        hProfile
        (fun X _hX =>
          columnSpikeContribution_transfer_noError
            (p := p) (q := q) (σ := σ)
            (α₀ := α₀) (N := N) (k := k) X)
        hPureError
        hBackgroundTransfer hBackgroundError
        (sphericalOneColumnFavorableEvent_subset_mixedEnvelopeSet_of_pointwise
          (p := p) (q := q) (σ := σ)
          (α₀ := α₀) (q₀ := q₀) (δ := δ) (N := N)
          (errMix := errMix) (k := k) (directionSet := directionSet)
          (backgroundSet :=
            backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ center k)
          hMixed))
      hMean hBudget

set_option linter.unusedSectionVars false in
/-- Eventual sequence form of
`columnProb_le_upperTailProb_of_closed_deterministic_blocks`. -/
theorem eventual_columnProb_le_upperTailProb_of_closed_deterministic_blocks
    [MeasurableSpace (SampleMatrix p q σ)] [DecidableEq σ]
    {μ : ℕ → Measure (SampleMatrix p q σ)}
    {columnProb targetProb q₀ δ N M a eps mean center errProfile errSpike τ
      errScale errBg errMix errMean : ℕ → ℝ}
    {directionSet : ℕ → Set (EuclideanSpace ℂ (BipIndex p q))}
    {α₀ : σ} {k : ℕ}
    (hFinite : ∀ᶠ d in atTop, IsFiniteMeasure (μ d))
    (hColumnProb :
      ∀ᶠ d in atTop,
        columnProb d =
          (μ d).real
            (sphericalOneColumnFavorableEvent
              (p := p) (q := q) (σ := σ)
              α₀ (q₀ d) (δ d) (directionSet d)
              (backgroundTypicalSet (p := p) (q := q) (σ := σ)
                (N d) (M d) (τ d) (center d) k)))
    (hTargetProb :
      ∀ᶠ d in atTop,
        targetProb d =
          (μ d).real
            (columnMomentUpperTailSet
              (p := p) (q := q) (σ := σ) (N d) (eps d) (mean d) k))
    (hProfile :
      ∀ᶠ d in atTop,
        ∀ R : ℝ, ∀ u : EuclideanSpace ℂ (BipIndex p q),
          R ∈ betaColumnIntervalSet (q₀ d) (δ d) →
          u ∈ directionSet d →
          a d ^ k - errProfile d ≤
            columnDirectionSpikeProfile (p := p) (q := q) (N d) k R u)
    (hPureError :
      ∀ᶠ d in atTop, errProfile d + 0 ≤ errSpike d)
    (hBackgroundTransfer :
      ∀ᶠ d in atTop,
        ∀ X : SampleMatrix p q σ,
          sampleColumnComplementNormalized (p := p) (q := q) (σ := σ) X α₀ ∈
            backgroundTypicalSet (p := p) (q := q) (σ := σ)
              (N d) (M d) (τ d) (center d) k →
          backgroundMomentValue (p := p) (q := q) (σ := σ) (N d) k
              (sampleColumnComplementNormalized (p := p) (q := q) (σ := σ) X α₀) -
              errScale d ≤
            columnBackgroundContribution (p := p) (q := q) (σ := σ) (N d) k X α₀)
    (hBackgroundError :
      ∀ᶠ d in atTop, τ d + errScale d ≤ errBg d)
    (hMixed :
      ∀ᶠ d in atTop,
        ∀ X : SampleMatrix p q σ,
          X ∈ sphericalOneColumnFavorableEvent
            (p := p) (q := q) (σ := σ)
            α₀ (q₀ d) (δ d) (directionSet d)
            (backgroundTypicalSet (p := p) (q := q) (σ := σ)
              (N d) (M d) (τ d) (center d) k) →
          |columnMixedRemainder (p := p) (q := q) (σ := σ) (N d) k X α₀| ≤
            errMix d)
    (hMean : ∀ᶠ d in atTop, mean d ≤ center d + errMean d)
    (hBudget :
      ∀ᶠ d in atTop,
        eps d + errSpike d + errBg d + errMix d + errMean d ≤ a d ^ k) :
    ∀ᶠ d in atTop, columnProb d ≤ targetProb d := by
  filter_upwards
    [hFinite, hColumnProb, hTargetProb, hProfile, hPureError,
      hBackgroundTransfer, hBackgroundError, hMixed, hMean, hBudget]
    with d hFinite_d hColumnProb_d hTargetProb_d hProfile_d hPureError_d
      hBackgroundTransfer_d hBackgroundError_d hMixed_d hMean_d hBudget_d
  letI : IsFiniteMeasure (μ d) := hFinite_d
  exact
    columnProb_le_upperTailProb_of_closed_deterministic_blocks
      (p := p) (q := q) (σ := σ)
      (μ := μ d)
      (columnProb := columnProb d) (targetProb := targetProb d)
      (α₀ := α₀)
      (q₀ := q₀ d) (δ := δ d) (N := N d) (M := M d) (a := a d)
      (eps := eps d) (mean := mean d) (center := center d)
      (errProfile := errProfile d) (errSpike := errSpike d)
      (τ := τ d) (errScale := errScale d) (errBg := errBg d)
      (errMix := errMix d) (errMean := errMean d)
      (k := k) (directionSet := directionSet d)
      hColumnProb_d hTargetProb_d hProfile_d hPureError_d
      hBackgroundTransfer_d hBackgroundError_d hMixed_d hMean_d hBudget_d

set_option linter.unusedSectionVars false in
/-- Family-level `hColumnIncluded` constructor for the one-column lower-bound
pipeline.

This is the deterministic inclusion ingredient in the exact quantifier shape
expected by `SpikeLowerBoundInput.of_oneColumn_probability_pipeline`.  The
pure-spike transfer is closed no-input, and the only remaining deterministic
inputs are:

* the directional profile lower bound on the Beta interval and cap;
* the background transfer from normalized deleted background to concrete
  background contribution;
* the pointwise mixed-remainder envelope on the favourable event;
* the scalar budgets for the four error terms. -/
theorem oneColumnProbabilityPipeline_hColumnIncluded_of_closed_deterministic_blocks
    [MeasurableSpace (SampleMatrix p q σ)] [DecidableEq σ]
    {μ : ℕ → Measure (SampleMatrix p q σ)}
    {columnProb : ℝ → ℝ → ℕ → ℝ} {targetProb : ℕ → ℝ}
    {q₀ δ N M eps mean center errProfile errSpike τ errScale errBg errMix
      errMean : ℝ → ℝ → ℕ → ℝ}
    {directionSet :
      ℝ → ℝ → ℕ → Set (EuclideanSpace ℂ (BipIndex p q))}
    {root : ℝ} {α₀ : σ} {k : ℕ}
    (hFinite : ∀ᶠ d in atTop, IsFiniteMeasure (μ d))
    (hColumnProb :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            columnProb a slack d =
              (μ d).real
                (sphericalOneColumnFavorableEvent
                  (p := p) (q := q) (σ := σ)
                  α₀ (q₀ a slack d) (δ a slack d)
                  (directionSet a slack d)
                  (backgroundTypicalSet (p := p) (q := q) (σ := σ)
                    (N a slack d) (M a slack d) (τ a slack d)
                    (center a slack d) k)))
    (hTargetProb :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            targetProb d =
              (μ d).real
                (columnMomentUpperTailSet
                  (p := p) (q := q) (σ := σ)
                  (N a slack d) (eps a slack d) (mean a slack d) k))
    (hProfile :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ R : ℝ, ∀ u : EuclideanSpace ℂ (BipIndex p q),
              R ∈ betaColumnIntervalSet (q₀ a slack d) (δ a slack d) →
              u ∈ directionSet a slack d →
              a ^ k - errProfile a slack d ≤
                columnDirectionSpikeProfile
                  (p := p) (q := q) (N a slack d) k R u)
    (hPureError :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            errProfile a slack d + 0 ≤ errSpike a slack d)
    (hBackgroundTransfer :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ X : SampleMatrix p q σ,
              sampleColumnComplementNormalized
                  (p := p) (q := q) (σ := σ) X α₀ ∈
                backgroundTypicalSet
                  (p := p) (q := q) (σ := σ)
                  (N a slack d) (M a slack d) (τ a slack d)
                  (center a slack d) k →
              backgroundMomentValue
                  (p := p) (q := q) (σ := σ) (N a slack d) k
                  (sampleColumnComplementNormalized
                    (p := p) (q := q) (σ := σ) X α₀) -
                  errScale a slack d ≤
                columnBackgroundContribution
                  (p := p) (q := q) (σ := σ) (N a slack d) k X α₀)
    (hBackgroundError :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            τ a slack d + errScale a slack d ≤ errBg a slack d)
    (hMixed :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ X : SampleMatrix p q σ,
              X ∈ sphericalOneColumnFavorableEvent
                (p := p) (q := q) (σ := σ)
                α₀ (q₀ a slack d) (δ a slack d)
                (directionSet a slack d)
                (backgroundTypicalSet
                  (p := p) (q := q) (σ := σ)
                  (N a slack d) (M a slack d) (τ a slack d)
                  (center a slack d) k) →
              |columnMixedRemainder
                  (p := p) (q := q) (σ := σ) (N a slack d) k X α₀| ≤
                errMix a slack d)
    (hMean :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            mean a slack d ≤ center a slack d + errMean a slack d)
    (hBudget :
      ∀ a : ℝ, root < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            eps a slack d + errSpike a slack d + errBg a slack d +
              errMix a slack d + errMean a slack d ≤ a ^ k) :
    ∀ a : ℝ, root < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop, columnProb a slack d ≤ targetProb d := by
  intro a ha slack hslack
  exact
    eventual_columnProb_le_upperTailProb_of_closed_deterministic_blocks
      (p := p) (q := q) (σ := σ)
      (μ := μ)
      (columnProb := fun d => columnProb a slack d)
      (targetProb := targetProb)
      (q₀ := fun d => q₀ a slack d)
      (δ := fun d => δ a slack d)
      (N := fun d => N a slack d)
      (M := fun d => M a slack d)
      (a := fun _ => a)
      (eps := fun d => eps a slack d)
      (mean := fun d => mean a slack d)
      (center := fun d => center a slack d)
      (errProfile := fun d => errProfile a slack d)
      (errSpike := fun d => errSpike a slack d)
      (τ := fun d => τ a slack d)
      (errScale := fun d => errScale a slack d)
      (errBg := fun d => errBg a slack d)
      (errMix := fun d => errMix a slack d)
      (errMean := fun d => errMean a slack d)
      (directionSet := fun d => directionSet a slack d)
      (α₀ := α₀) (k := k)
      hFinite
      (hColumnProb a ha slack hslack)
      (hTargetProb a ha slack hslack)
      (hProfile a ha slack hslack)
      (hPureError a ha slack hslack)
      (hBackgroundTransfer a ha slack hslack)
      (hBackgroundError a ha slack hslack)
      (hMixed a ha slack hslack)
      (hMean a ha slack hslack)
      (hBudget a ha slack hslack)

/-- Closed deterministic-block certificate for the concrete one-column event.

Compared with
`sphericalOneColumnFavorableEvent_subset_certificate_of_concrete_implications`,
the pure-spike transfer is no longer an input: it is the exact
mass-direction identity
`columnSpikeContribution_eq_directionSpikeProfile`.  The mixed block is also
accepted in its natural pointwise form, namely an absolute envelope for the
exact mixed remainder on the favourable event. -/
theorem sphericalOneColumnFavorableEvent_subset_certificate_of_closed_deterministic_blocks
    [DecidableEq σ]
    {α₀ : σ}
    {q₀ δ N M a center errProfile errSpike τ errScale errBg errMix : ℝ}
    {k : ℕ}
    {directionSet : Set (EuclideanSpace ℂ (BipIndex p q))}
    (hProfile :
      ∀ R : ℝ, ∀ u : EuclideanSpace ℂ (BipIndex p q),
        R ∈ betaColumnIntervalSet q₀ δ →
        u ∈ directionSet →
        a ^ k - errProfile ≤
          columnDirectionSpikeProfile (p := p) (q := q) N k R u)
    (hPureError : errProfile + 0 ≤ errSpike)
    (hBackgroundTransfer :
      ∀ X : SampleMatrix p q σ,
        sampleColumnComplementNormalized (p := p) (q := q) (σ := σ) X α₀ ∈
          backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ center k →
        backgroundMomentValue (p := p) (q := q) (σ := σ) N k
            (sampleColumnComplementNormalized (p := p) (q := q) (σ := σ) X α₀) -
            errScale ≤
          columnBackgroundContribution (p := p) (q := q) (σ := σ) N k X α₀)
    (hBackgroundError : τ + errScale ≤ errBg)
    (hMixed :
      ∀ X : SampleMatrix p q σ,
        X ∈ sphericalOneColumnFavorableEvent
          (p := p) (q := q) (σ := σ)
          α₀ q₀ δ directionSet
          (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ center k) →
        |columnMixedRemainder (p := p) (q := q) (σ := σ) N k X α₀| ≤
          errMix) :
    sphericalOneColumnFavorableEvent
        (p := p) (q := q) (σ := σ)
        α₀ q₀ δ directionSet
        (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ center k) ⊆
      columnSpikeUpperTailCertificateSet
        (p := p) (q := q) (σ := σ)
        α₀ N a center errSpike errBg errMix k := by
  refine
    sphericalOneColumnFavorableEvent_subset_certificate_of_three_implications
      (α₀ := α₀) (q₀ := q₀) (δ := δ) (N := N) (a := a)
      (center := center) (errSpike := errSpike) (errBg := errBg)
      (errMix := errMix) (k := k) (directionSet := directionSet)
      (backgroundSet :=
        backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ center k)
      ?_ ?_ ?_
  · exact
      columnMassCapEvent_subset_pureSpikeLowerBoundSet_noInputTransfer
        (p := p) (q := q) (σ := σ)
        (α₀ := α₀) (N := N) (a := a)
        (errProfile := errProfile) (errSpike := errSpike)
        (q₀ := q₀) (δ := δ) (k := k)
        (directionSet := directionSet)
        hProfile hPureError
  · exact
      normalizedDeletedBackgroundTypicalEvent_subset_backgroundContributionLowerBoundSet_of_error_budget
        (p := p) (q := q) (σ := σ)
        (α₀ := α₀) (N := N) (M := M) (τ := τ)
        (center := center) (errScale := errScale) (errBg := errBg)
        (k := k)
        hBackgroundTransfer hBackgroundError
  · exact
      sphericalOneColumnFavorableEvent_subset_mixedEnvelopeSet_of_pointwise
        (p := p) (q := q) (σ := σ)
        (α₀ := α₀) (q₀ := q₀) (δ := δ) (N := N)
        (errMix := errMix) (k := k) (directionSet := directionSet)
        (backgroundSet :=
          backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ center k)
        hMixed

/-- Upper-tail inclusion with the three deterministic blocks exposed and the
pure-spike transfer closed no-input. -/
theorem sphericalOneColumnFavorableEvent_subset_upperTailSet_of_closed_deterministic_blocks
    [DecidableEq σ]
    {α₀ : σ}
    {q₀ δ N M a eps mean center errProfile errSpike τ errScale errBg errMix
      errMean : ℝ}
    {k : ℕ}
    {directionSet : Set (EuclideanSpace ℂ (BipIndex p q))}
    (hProfile :
      ∀ R : ℝ, ∀ u : EuclideanSpace ℂ (BipIndex p q),
        R ∈ betaColumnIntervalSet q₀ δ →
        u ∈ directionSet →
        a ^ k - errProfile ≤
          columnDirectionSpikeProfile (p := p) (q := q) N k R u)
    (hPureError : errProfile + 0 ≤ errSpike)
    (hBackgroundTransfer :
      ∀ X : SampleMatrix p q σ,
        sampleColumnComplementNormalized (p := p) (q := q) (σ := σ) X α₀ ∈
          backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ center k →
        backgroundMomentValue (p := p) (q := q) (σ := σ) N k
            (sampleColumnComplementNormalized (p := p) (q := q) (σ := σ) X α₀) -
            errScale ≤
          columnBackgroundContribution (p := p) (q := q) (σ := σ) N k X α₀)
    (hBackgroundError : τ + errScale ≤ errBg)
    (hMixed :
      ∀ X : SampleMatrix p q σ,
        X ∈ sphericalOneColumnFavorableEvent
          (p := p) (q := q) (σ := σ)
          α₀ q₀ δ directionSet
          (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ center k) →
        |columnMixedRemainder (p := p) (q := q) (σ := σ) N k X α₀| ≤
          errMix)
    (hMean : mean ≤ center + errMean)
    (hBudget : eps + errSpike + errBg + errMix + errMean ≤ a ^ k) :
    sphericalOneColumnFavorableEvent
        (p := p) (q := q) (σ := σ)
        α₀ q₀ δ directionSet
        (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ center k) ⊆
      columnMomentUpperTailSet (p := p) (q := q) (σ := σ) N eps mean k :=
  Set.Subset.trans
    (sphericalOneColumnFavorableEvent_subset_certificate_of_closed_deterministic_blocks
      (p := p) (q := q) (σ := σ)
      (α₀ := α₀) (q₀ := q₀) (δ := δ) (N := N) (M := M)
      (a := a) (center := center) (errProfile := errProfile)
      (errSpike := errSpike) (τ := τ) (errScale := errScale)
      (errBg := errBg) (errMix := errMix) (k := k)
      (directionSet := directionSet)
      hProfile hPureError hBackgroundTransfer hBackgroundError hMixed)
    (columnSpikeUpperTailCertificateSet_subset_upperTailSet
      (p := p) (q := q) (σ := σ)
      (α₀ := α₀) (N := N) (a := a) (eps := eps)
      (mean := mean) (center := center) (errSpike := errSpike)
      (errBg := errBg) (errMix := errMix) (errMean := errMean) (k := k)
      hMean hBudget)

/-- Probability of the background typical set under an arbitrary background
marginal law. -/
noncomputable def backgroundTypicalProbability
    [MeasurableSpace (SampleMatrix p q σ)]
    (ν : Measure (SampleMatrix p q σ))
    (N M τ mean : ℝ) (k : ℕ) : ℝ :=
  ν.real (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k)

/-- Probability that the normalized deleted-column background `Y` extracted from
`X` lies in the concrete background typical set `K_N`. -/
noncomputable def columnBackgroundTypicalProbability
    [MeasurableSpace (SampleMatrix p q σ)] [DecidableEq σ]
    (μ : Measure (SampleMatrix p q σ)) (α₀ : σ)
    (N M τ mean : ℝ) (k : ℕ) : ℝ :=
  columnBackgroundProbability (p := p) (q := q) (σ := σ) μ α₀
    (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k)

set_option linter.unusedSectionVars false in
/-- Under a one-column spherical decomposition, the typicality probability of
the actual deleted-column background equals the `K_N` probability under the
background marginal. -/
theorem SphericalOneColumnDecompositionIndependence.columnBackgroundTypicalProbability_eq
    [MeasurableSpace (SampleMatrix p q σ)] [DecidableEq σ]
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {massLaw : Measure ℝ}
    {directionLaw : Measure (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundLaw : Measure (SampleMatrix p q σ)}
    (I :
      SphericalOneColumnDecompositionIndependence
        (p := p) (q := q) (σ := σ)
        μ α₀ massLaw directionLaw backgroundLaw)
    (N M τ mean : ℝ) (k : ℕ) :
    columnBackgroundTypicalProbability
        (p := p) (q := q) (σ := σ) μ α₀ N M τ mean k =
      backgroundTypicalProbability
        (p := p) (q := q) (σ := σ) backgroundLaw N M τ mean k := by
  unfold columnBackgroundTypicalProbability backgroundTypicalProbability
  exact
    I.columnBackgroundProbability_eq
      (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k)

set_option linter.unusedSectionVars false in
/-- Half-measure typicality for the background marginal transfers to the actual
normalized deleted-column background `Y`. -/
theorem SphericalOneColumnDecompositionIndependence.columnBackgroundTypicalProbability_ge_half
    [MeasurableSpace (SampleMatrix p q σ)] [DecidableEq σ]
    {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
    {massLaw : Measure ℝ}
    {directionLaw : Measure (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundLaw : Measure (SampleMatrix p q σ)}
    (I :
      SphericalOneColumnDecompositionIndependence
        (p := p) (q := q) (σ := σ)
        μ α₀ massLaw directionLaw backgroundLaw)
    {N M τ mean : ℝ} {k : ℕ}
    (hHalf :
      (1 / 2 : ℝ) ≤
        backgroundTypicalProbability
          (p := p) (q := q) (σ := σ) backgroundLaw N M τ mean k) :
    (1 / 2 : ℝ) ≤
      columnBackgroundTypicalProbability
        (p := p) (q := q) (σ := σ) μ α₀ N M τ mean k := by
  rw [I.columnBackgroundTypicalProbability_eq N M τ mean k]
  exact hHalf

/-- The bad moment event complementary to the first condition in `K_N`. -/
noncomputable def backgroundMomentBadSet
    (N τ mean : ℝ) (k : ℕ) : Set (SampleMatrix p q σ) :=
  {Y | τ < |backgroundMomentValue (p := p) (q := q) (σ := σ) N k Y - mean|}

  /-- Measurability of the background moment bad set. -/
  theorem measurableSet_backgroundMomentBadSet
      (N τ mean : ℝ) (k : ℕ) :
      MeasurableSet
        (backgroundMomentBadSet (p := p) (q := q) (σ := σ) N τ mean k) := by
    unfold backgroundMomentBadSet
    exact measurableSet_lt measurable_const
      (((measurable_backgroundMomentValue
        (p := p) (q := q) (σ := σ) N k).sub measurable_const).norm)

/-- The bad sample-operator-norm event complementary to the second condition
in `K_N`. -/
noncomputable def backgroundSampleOpNormBadSet
    (N M : ℝ) : Set (SampleMatrix p q σ) :=
  {Y |
    M / Real.sqrt N <
      PptFactorization.HighProbabilityBounds.sampleOpNorm
        (p := p) (q := q) (σ := σ) Y}

  /-- The bad partial-transpose operator-norm event complementary to the third
  condition in `K_N`. -/
  noncomputable def backgroundGammaOpNormBadSet
      (N M : ℝ) : Set (SampleMatrix p q σ) :=
    {Y | M / N < opNorm (p := p) (q := q) (gamma (densityMatrix Y))}

  omit [DecidableEq p] [DecidableEq q] in
  /-- Measurability of the background sample-operator-norm bad set. -/
  theorem measurableSet_backgroundSampleOpNormBadSet
      (N M : ℝ) :
      MeasurableSet
        (backgroundSampleOpNormBadSet (p := p) (q := q) (σ := σ) N M) := by
    unfold backgroundSampleOpNormBadSet
    exact measurableSet_lt measurable_const
      (PptFactorization.HighProbabilityBounds.sampleOpNorm_continuous
        (p := p) (q := q) (σ := σ)).measurable

  /-- Measurability of the background partial-transpose operator-norm bad set. -/
  theorem measurableSet_backgroundGammaOpNormBadSet
      (N M : ℝ) :
      MeasurableSet
        (backgroundGammaOpNormBadSet (p := p) (q := q) (σ := σ) N M) := by
    unfold backgroundGammaOpNormBadSet
    change MeasurableSet
      {Y : SampleMatrix p q σ |
        M / N < sphericalGammaOpNorm (p := p) (q := q) (σ := σ) Y}
    exact measurableSet_lt measurable_const
      (continuous_sphericalGammaOpNorm (p := p) (q := q) (σ := σ)).measurable

  omit [DecidableEq p] [DecidableEq q] in
  /-- Under the concrete spherical law, the sample-operator bad set is exactly
  the Gaussian-direction image of the corresponding normalized Gaussian bad
  event. -/
  theorem spherical_backgroundSampleOpNormBadSet_tail_from_gaussian
      {N d M b : ℝ}
      (hd : 0 < d) (hN : N = d ^ 2)
      (hTail :
        (gaussianMeasure p q σ).real
          ((normalizedSampleOpNormEvent
            (p := p) (q := q) (σ := σ) M d)ᶜ) ≤ b) :
      (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
        (backgroundSampleOpNormBadSet (p := p) (q := q) (σ := σ) N M) ≤ b := by
    unfold sphericalModelMeasure gaussianSphericalSampleMeasure
    rw [map_measureReal_apply
      (measurable_gaussianDirection (p := p) (q := q) (σ := σ))
      (measurableSet_backgroundSampleOpNormBadSet
        (p := p) (q := q) (σ := σ) N M)]
    have hsqrt : Real.sqrt N = d := by
      rw [hN, Real.sqrt_sq_eq_abs, abs_of_pos hd]
    have hpre :
        gaussianDirection (p := p) (q := q) (σ := σ) ⁻¹'
          backgroundSampleOpNormBadSet (p := p) (q := q) (σ := σ) N M =
        (normalizedSampleOpNormEvent (p := p) (q := q) (σ := σ) M d)ᶜ := by
      ext ω
      simp [backgroundSampleOpNormBadSet, normalizedSampleOpNormEvent,
        gaussianDirection, hsqrt]
    simpa [hpre] using hTail

  /-- Under the concrete spherical law, the partial-transpose operator-norm bad
  set is exactly the Gaussian-direction image of the corresponding normalized
  Gaussian bad event. -/
  theorem spherical_backgroundGammaOpNormBadSet_tail_from_gaussian
      {N d M b : ℝ}
      (hN : N = d ^ 2)
      (hTail :
        (gaussianMeasure p q σ).real
          ((normalizedRhoGammaOpNormEvent
            (p := p) (q := q) (σ := σ) M d)ᶜ) ≤ b) :
      (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
        (backgroundGammaOpNormBadSet (p := p) (q := q) (σ := σ) N M) ≤ b := by
    unfold sphericalModelMeasure gaussianSphericalSampleMeasure
    rw [map_measureReal_apply
      (measurable_gaussianDirection (p := p) (q := q) (σ := σ))
      (measurableSet_backgroundGammaOpNormBadSet
        (p := p) (q := q) (σ := σ) N M)]
    have hpre :
        gaussianDirection (p := p) (q := q) (σ := σ) ⁻¹'
          backgroundGammaOpNormBadSet (p := p) (q := q) (σ := σ) N M =
        (normalizedRhoGammaOpNormEvent (p := p) (q := q) (σ := σ) M d)ᶜ := by
      ext ω
      simp [backgroundGammaOpNormBadSet, normalizedRhoGammaOpNormEvent,
        gaussianDirection, rhoGamma, rho, hN]
    simpa [hpre] using hTail

  /-- The three concrete spherical bad-set probability bounds for `K_N`.

  The moment bad-set estimate is the genuine background-typicality input.  The
  two operator-norm bad-set estimates are obtained from the concrete Gaussian
  normalized tails by the two transfer lemmas above. -/
  structure ConcreteSphericalBackgroundBadSetBounds
      (N M τ mean bMoment bSample bGamma : ℝ) (k : ℕ) : Prop where
    moment_bad :
      (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
        (backgroundMomentBadSet (p := p) (q := q) (σ := σ) N τ mean k) ≤
          bMoment
    sample_bad :
      (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
        (backgroundSampleOpNormBadSet (p := p) (q := q) (σ := σ) N M) ≤
          bSample
    gamma_bad :
      (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
        (backgroundGammaOpNormBadSet (p := p) (q := q) (σ := σ) N M) ≤
          bGamma

  /-- Build the concrete three-bad-set package from one moment-tail input and
  the two normalized Gaussian operator tails. -/
  theorem ConcreteSphericalBackgroundBadSetBounds.of_moment_and_gaussian_operator_tails
      {N d M τ mean bMoment bSample bGamma : ℝ} {k : ℕ}
      (hd : 0 < d) (hN : N = d ^ 2)
      (hMoment :
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
          (backgroundMomentBadSet (p := p) (q := q) (σ := σ) N τ mean k) ≤
            bMoment)
      (hSampleTail :
        (gaussianMeasure p q σ).real
          ((normalizedSampleOpNormEvent
            (p := p) (q := q) (σ := σ) M d)ᶜ) ≤ bSample)
      (hGammaTail :
        (gaussianMeasure p q σ).real
          ((normalizedRhoGammaOpNormEvent
            (p := p) (q := q) (σ := σ) M d)ᶜ) ≤ bGamma) :
      ConcreteSphericalBackgroundBadSetBounds
        (p := p) (q := q) (σ := σ) N M τ mean bMoment bSample bGamma k where
    moment_bad := hMoment
    sample_bad :=
      spherical_backgroundSampleOpNormBadSet_tail_from_gaussian
        (p := p) (q := q) (σ := σ)
        (N := N) (d := d) (M := M) (b := bSample)
        hd hN hSampleTail
    gamma_bad :=
      spherical_backgroundGammaOpNormBadSet_tail_from_gaussian
        (p := p) (q := q) (σ := σ)
        (N := N) (d := d) (M := M) (b := bGamma)
        hN hGammaTail

  set_option linter.unusedSectionVars false in
  /-- The background moment functional is unchanged by zero-extending a
  deleted-column matrix. -/
  theorem backgroundMomentValue_deletedColumnZeroExtend
      [DecidableEq σ] (α₀ : σ)
      (Y : SampleMatrix p q (DeletedColumn α₀)) (N : ℝ) (k : ℕ) :
      backgroundMomentValue (p := p) (q := q) (σ := σ) N k
          (deletedColumnZeroExtend (p := p) (q := q) (σ := σ) α₀ Y) =
        backgroundMomentValue (p := p) (q := q) (σ := DeletedColumn α₀)
          N k Y := by
    simp [backgroundMomentValue, densityMatrix_deletedColumnZeroExtend]

  set_option linter.unusedSectionVars false in
  /-- Pulling back the full moment bad set by zero-extension gives exactly the
  reduced deleted-column moment bad set. -/
  theorem backgroundMomentBadSet_preimage_deletedColumnZeroExtend
      [DecidableEq σ] (α₀ : σ) (N τ mean : ℝ) (k : ℕ) :
      (deletedColumnZeroExtend (p := p) (q := q) (σ := σ) α₀) ⁻¹'
          backgroundMomentBadSet (p := p) (q := q) (σ := σ) N τ mean k =
        backgroundMomentBadSet
          (p := p) (q := q) (σ := DeletedColumn α₀) N τ mean k := by
    ext Y
    simp [backgroundMomentBadSet,
      backgroundMomentValue_deletedColumnZeroExtend
        (p := p) (q := q) (σ := σ) α₀ Y N k]

  set_option linter.unusedSectionVars false in
  /-- Pulling back the full gamma-operator bad set by zero-extension gives
  exactly the reduced deleted-column gamma-operator bad set. -/
  theorem backgroundGammaOpNormBadSet_preimage_deletedColumnZeroExtend
      [DecidableEq σ] (α₀ : σ) (N M : ℝ) :
      (deletedColumnZeroExtend (p := p) (q := q) (σ := σ) α₀) ⁻¹'
          backgroundGammaOpNormBadSet (p := p) (q := q) (σ := σ) N M =
        backgroundGammaOpNormBadSet
          (p := p) (q := q) (σ := DeletedColumn α₀) N M := by
    ext Y
    simp [backgroundGammaOpNormBadSet, densityMatrix_deletedColumnZeroExtend]

  set_option linter.unusedSectionVars false in
  /-- Pulling back the full sample-operator bad set by zero-extension is
  contained in the reduced deleted-column sample-operator bad set.  Equality is
  true, but the one-sided form is all the probability bound needs. -/
  theorem backgroundSampleOpNormBadSet_preimage_deletedColumnZeroExtend_subset
      [DecidableEq σ] (α₀ : σ) (N M : ℝ) :
      (deletedColumnZeroExtend (p := p) (q := q) (σ := σ) α₀) ⁻¹'
          backgroundSampleOpNormBadSet (p := p) (q := q) (σ := σ) N M ⊆
        backgroundSampleOpNormBadSet
          (p := p) (q := q) (σ := DeletedColumn α₀) N M := by
    intro Y hY
    have hle :=
      sampleOpNorm_deletedColumnZeroExtend_le
        (p := p) (q := q) (σ := σ) α₀ Y
    exact lt_of_lt_of_le hY hle

  /-- The complement of `K_N` is contained in the union of its three explicit
  bad events. -/
  theorem backgroundTypicalSet_compl_subset_bad_union
    (N M τ mean : ℝ) (k : ℕ) :
    (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k)ᶜ ⊆
      backgroundMomentBadSet (p := p) (q := q) (σ := σ) N τ mean k ∪
        backgroundSampleOpNormBadSet (p := p) (q := q) (σ := σ) N M ∪
          backgroundGammaOpNormBadSet (p := p) (q := q) (σ := σ) N M := by
  intro Y hY
  simp only [backgroundTypicalSet, backgroundMomentBadSet,
    backgroundSampleOpNormBadSet, backgroundGammaOpNormBadSet,
    Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_union] at hY ⊢
  by_cases hMoment :
      |backgroundMomentValue (p := p) (q := q) (σ := σ) N k Y - mean| ≤ τ
  · by_cases hSample :
        PptFactorization.HighProbabilityBounds.sampleOpNorm
          (p := p) (q := q) (σ := σ) Y ≤ M / Real.sqrt N
    · have hGamma :
          ¬ opNorm (p := p) (q := q) (gamma (densityMatrix Y)) ≤ M / N := by
        exact fun h => hY ⟨hMoment, hSample, h⟩
      right
      exact lt_of_not_ge hGamma
    · left
      right
      exact lt_of_not_ge hSample
  · left
    left
    exact lt_of_not_ge hMoment

/-- Probability lower bound for `K_N` from three bad-event estimates.

This is the formal union-bound step:

`P(K_N) ≥ 1 - P(moment bad) - P(sample-op bad) - P(gamma-op bad)`. -/
theorem backgroundTypicalSet_measure_ge_one_sub_bad
    [MeasurableSpace (SampleMatrix p q σ)]
    {μ : Measure (SampleMatrix p q σ)}
    (hprob : IsProbabilityMeasure μ)
    {N M τ mean bMoment bSample bGamma : ℝ} {k : ℕ}
    (hK_meas :
      MeasurableSet
        (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k))
    (hMoment :
      μ.real
        (backgroundMomentBadSet (p := p) (q := q) (σ := σ) N τ mean k) ≤
          bMoment)
    (hSample :
      μ.real
        (backgroundSampleOpNormBadSet (p := p) (q := q) (σ := σ) N M) ≤
          bSample)
    (hGamma :
      μ.real
        (backgroundGammaOpNormBadSet (p := p) (q := q) (σ := σ) N M) ≤
          bGamma) :
    1 - (bMoment + bSample + bGamma) ≤
      μ.real
        (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k) := by
  letI : IsProbabilityMeasure μ := hprob
  let K :=
    backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k
  let B₁ :=
    backgroundMomentBadSet (p := p) (q := q) (σ := σ) N τ mean k
  let B₂ :=
    backgroundSampleOpNormBadSet (p := p) (q := q) (σ := σ) N M
  let B₃ :=
    backgroundGammaOpNormBadSet (p := p) (q := q) (σ := σ) N M
  have hsubset : Kᶜ ⊆ B₁ ∪ B₂ ∪ B₃ := by
    simpa [K, B₁, B₂, B₃] using
      backgroundTypicalSet_compl_subset_bad_union
        (p := p) (q := q) (σ := σ) N M τ mean k
  have hKc_le :
      μ.real Kᶜ ≤ bMoment + bSample + bGamma := by
    calc
      μ.real Kᶜ ≤ μ.real (B₁ ∪ B₂ ∪ B₃) :=
        measureReal_mono hsubset (h₂ := (measure_lt_top μ _).ne)
      _ ≤ μ.real (B₁ ∪ B₂) + μ.real B₃ := by
        exact measureReal_union_le _ _
      _ ≤ (μ.real B₁ + μ.real B₂) + μ.real B₃ := by
        gcongr
        exact measureReal_union_le _ _
      _ ≤ (bMoment + bSample) + bGamma := by
        gcongr
      _ = bMoment + bSample + bGamma := by ring
  have hcompl :
      μ.real Kᶜ = 1 - μ.real K := by
    simpa [K] using measureReal_compl (μ := μ) hK_meas
  linarith

/-- Half-measure version of the preceding probability lower bound, the exact
form needed before applying spherical isoperimetry. -/
theorem backgroundTypicalSet_measure_ge_half
    [MeasurableSpace (SampleMatrix p q σ)]
    {μ : Measure (SampleMatrix p q σ)}
    (hprob : IsProbabilityMeasure μ)
    {N M τ mean bMoment bSample bGamma : ℝ} {k : ℕ}
    (hK_meas :
      MeasurableSet
        (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k))
    (hMoment :
      μ.real
        (backgroundMomentBadSet (p := p) (q := q) (σ := σ) N τ mean k) ≤
          bMoment)
    (hSample :
      μ.real
        (backgroundSampleOpNormBadSet (p := p) (q := q) (σ := σ) N M) ≤
          bSample)
    (hGamma :
      μ.real
        (backgroundGammaOpNormBadSet (p := p) (q := q) (σ := σ) N M) ≤
          bGamma)
    (hBad : bMoment + bSample + bGamma ≤ 1 / 2) :
    1 / 2 ≤
      μ.real
        (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k) := by
  have h :=
    backgroundTypicalSet_measure_ge_one_sub_bad
      (p := p) (q := q) (σ := σ) (μ := μ) hprob
      (N := N) (M := M) (τ := τ) (mean := mean)
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (k := k) hK_meas hMoment hSample hGamma
  linarith

  /-- Three bad-set bounds for `K_N` under an arbitrary background marginal law.

  This is the canonical interface for the deleted-column background in the
  one-column spike argument: the marginal law of the normalized remainder may be
  a deleted-column/zero-extension law, not the full spherical law on all
  columns.  The older concrete spherical package below is only the specialization
  where this marginal has already been identified with `sphericalModelMeasure`. -/
  structure BackgroundBadSetBounds
      [MeasurableSpace (SampleMatrix p q σ)]
      (ν : Measure (SampleMatrix p q σ))
      (N M τ mean bMoment bSample bGamma : ℝ) (k : ℕ) : Prop where
    is_probability : IsProbabilityMeasure ν
    K_meas :
      MeasurableSet
        (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k)
    moment_bad :
      ν.real
        (backgroundMomentBadSet (p := p) (q := q) (σ := σ) N τ mean k) ≤
          bMoment
    sample_bad :
      ν.real
        (backgroundSampleOpNormBadSet (p := p) (q := q) (σ := σ) N M) ≤
          bSample
    gamma_bad :
      ν.real
        (backgroundGammaOpNormBadSet (p := p) (q := q) (σ := σ) N M) ≤
          bGamma

  /-- The three bad-set bounds for the actual deleted-column background law:
  spherical measure on `DeletedColumn α₀`, pushed forward by zero-extension. -/
  abbrev DeletedColumnBackgroundBadSetBounds
      [DecidableEq σ] (α₀ : σ)
      (N M τ mean bMoment bSample bGamma : ℝ) (k : ℕ) : Prop :=
    BackgroundBadSetBounds
      (p := p) (q := q) (σ := σ)
      (deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀)
      N M τ mean bMoment bSample bGamma k

  /-- Direct constructor for the deleted-column background bad-set package.

  This is deliberately stated under the actual deleted background law
  `deletedColumnBackgroundLaw α₀`.  It is the point where the three concrete
  bad-set estimates for the normalized deleted matrix enter; downstream code
  only sees the packaged `DeletedColumnBackgroundBadSetBounds`. -/
  theorem DeletedColumnBackgroundBadSetBounds.of_deleted_background_bad_bounds
      [DecidableEq σ]
      {α₀ : σ} {N M τ mean bMoment bSample bGamma : ℝ} {k : ℕ}
      (hprob :
        IsProbabilityMeasure
          (deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀))
      (hK_meas :
        MeasurableSet
          (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k))
      (hMoment :
        (deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀).real
          (backgroundMomentBadSet (p := p) (q := q) (σ := σ) N τ mean k) ≤
            bMoment)
      (hSample :
        (deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀).real
          (backgroundSampleOpNormBadSet (p := p) (q := q) (σ := σ) N M) ≤
            bSample)
      (hGamma :
        (deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀).real
          (backgroundGammaOpNormBadSet (p := p) (q := q) (σ := σ) N M) ≤
            bGamma) :
      DeletedColumnBackgroundBadSetBounds
        (p := p) (q := q) (σ := σ)
        α₀ N M τ mean bMoment bSample bGamma k where
    is_probability := hprob
    K_meas := hK_meas
    moment_bad := hMoment
    sample_bad := hSample
    gamma_bad := hGamma

  /-- No-input probability field for the deleted background law in the
  nondegenerate case. -/
  theorem DeletedColumnBackgroundBadSetBounds.deleted_background_probability
      [DecidableEq σ] [Nonempty p] [Nonempty q]
      {α₀ : σ} (hσ : 2 ≤ Fintype.card σ) :
      IsProbabilityMeasure
        (deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀) := by
    haveI : Nonempty (DeletedColumn α₀) :=
      deletedColumn_nonempty_of_two_le_card (α₀ := α₀) hσ
    exact deletedColumnBackgroundLaw_isProbabilityMeasure
      (p := p) (q := q) (σ := σ) (α₀ := α₀)

  /-- Direct constructor for the deleted-column background bad-set package with
  the probability-measure field filled automatically from `card σ ≥ 2`. -/
  theorem DeletedColumnBackgroundBadSetBounds.of_deleted_background_bad_bounds_noInput_probability
      [DecidableEq σ] [Nonempty p] [Nonempty q]
      {α₀ : σ} {N M τ mean bMoment bSample bGamma : ℝ} {k : ℕ}
      (hσ : 2 ≤ Fintype.card σ)
      (hK_meas :
        MeasurableSet
          (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k))
      (hMoment :
        (deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀).real
          (backgroundMomentBadSet (p := p) (q := q) (σ := σ) N τ mean k) ≤
            bMoment)
      (hSample :
        (deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀).real
          (backgroundSampleOpNormBadSet (p := p) (q := q) (σ := σ) N M) ≤
            bSample)
      (hGamma :
        (deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀).real
          (backgroundGammaOpNormBadSet (p := p) (q := q) (σ := σ) N M) ≤
            bGamma) :
      DeletedColumnBackgroundBadSetBounds
        (p := p) (q := q) (σ := σ)
        α₀ N M τ mean bMoment bSample bGamma k :=
    DeletedColumnBackgroundBadSetBounds.of_deleted_background_bad_bounds
      (p := p) (q := q) (σ := σ) (α₀ := α₀)
      (N := N) (M := M) (τ := τ) (mean := mean)
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (k := k)
      (DeletedColumnBackgroundBadSetBounds.deleted_background_probability
        (p := p) (q := q) (σ := σ) (α₀ := α₀) hσ)
      hK_meas hMoment hSample hGamma

  set_option linter.unusedSectionVars false in
  /-- Close the deleted-column bad-set package from the concrete spherical
  bad-set package on the reduced deleted-column sample space.

  This is the canonical no-input transport: the background law is
  `Measure.map (deletedColumnZeroExtend α₀)
    (sphericalModelMeasure p q (DeletedColumn α₀))`, so all three bad-set
  estimates are inherited from the reduced spherical model.  The sample
  operator-norm estimate uses the one-sided fact that adding a zero column
  cannot increase the rectangular operator norm. -/
  theorem DeletedColumnBackgroundBadSetBounds.of_reduced_concrete_spherical_bad_bounds
      [DecidableEq σ] [Nonempty p] [Nonempty q]
      {α₀ : σ} {N M τ mean bMoment bSample bGamma : ℝ} {k : ℕ}
      (hσ : 2 ≤ Fintype.card σ)
      (I :
        ConcreteSphericalBackgroundBadSetBounds
          (p := p) (q := q) (σ := DeletedColumn α₀)
          N M τ mean bMoment bSample bGamma k) :
      DeletedColumnBackgroundBadSetBounds
        (p := p) (q := q) (σ := σ)
        α₀ N M τ mean bMoment bSample bGamma k := by
    classical
    haveI : Nonempty (DeletedColumn α₀) :=
      deletedColumn_nonempty_of_two_le_card
        (α₀ := α₀) hσ
    haveI : IsProbabilityMeasure
        (sphericalModelMeasure (p := p) (q := q) (σ := DeletedColumn α₀)) :=
      sphericalModelMeasure_isProbabilityMeasure
        (p := p) (q := q) (σ := DeletedColumn α₀)
    refine
      DeletedColumnBackgroundBadSetBounds.of_deleted_background_bad_bounds_noInput_probability
        (p := p) (q := q) (σ := σ) (α₀ := α₀)
        (N := N) (M := M) (τ := τ) (mean := mean)
        (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
        (k := k) hσ
        (measurableSet_backgroundTypicalSet
          (p := p) (q := q) (σ := σ) N M τ mean k)
        ?_ ?_ ?_
    · unfold deletedColumnBackgroundLaw
      rw [map_measureReal_apply
        (measurable_deletedColumnZeroExtend
          (p := p) (q := q) (σ := σ) α₀)
        (measurableSet_backgroundMomentBadSet
          (p := p) (q := q) (σ := σ) N τ mean k)]
      rw [backgroundMomentBadSet_preimage_deletedColumnZeroExtend
        (p := p) (q := q) (σ := σ) α₀ N τ mean k]
      exact I.moment_bad
    · unfold deletedColumnBackgroundLaw
      rw [map_measureReal_apply
        (measurable_deletedColumnZeroExtend
          (p := p) (q := q) (σ := σ) α₀)
        (measurableSet_backgroundSampleOpNormBadSet
          (p := p) (q := q) (σ := σ) N M)]
      calc
        (sphericalModelMeasure
            (p := p) (q := q) (σ := DeletedColumn α₀)).real
            ((deletedColumnZeroExtend
              (p := p) (q := q) (σ := σ) α₀) ⁻¹'
              backgroundSampleOpNormBadSet
                (p := p) (q := q) (σ := σ) N M) ≤
          (sphericalModelMeasure
            (p := p) (q := q) (σ := DeletedColumn α₀)).real
            (backgroundSampleOpNormBadSet
              (p := p) (q := q) (σ := DeletedColumn α₀) N M) :=
            measureReal_mono
              (backgroundSampleOpNormBadSet_preimage_deletedColumnZeroExtend_subset
                (p := p) (q := q) (σ := σ) α₀ N M)
              (h₂ := (measure_lt_top
                (sphericalModelMeasure
                  (p := p) (q := q) (σ := DeletedColumn α₀))
                _).ne)
        _ ≤ bSample := I.sample_bad
    · unfold deletedColumnBackgroundLaw
      rw [map_measureReal_apply
        (measurable_deletedColumnZeroExtend
          (p := p) (q := q) (σ := σ) α₀)
        (measurableSet_backgroundGammaOpNormBadSet
          (p := p) (q := q) (σ := σ) N M)]
      rw [backgroundGammaOpNormBadSet_preimage_deletedColumnZeroExtend
        (p := p) (q := q) (σ := σ) α₀ N M]
      exact I.gamma_bad

  /-- Arbitrary-background bad-set bounds imply the named typical-probability
  lower bound. -/
  theorem BackgroundBadSetBounds.backgroundTypicalProbability_ge_one_sub_bad
      [MeasurableSpace (SampleMatrix p q σ)]
      {ν : Measure (SampleMatrix p q σ)}
      {N M τ mean bMoment bSample bGamma : ℝ} {k : ℕ}
      (I :
        BackgroundBadSetBounds
          (p := p) (q := q) (σ := σ)
          ν N M τ mean bMoment bSample bGamma k) :
      1 - (bMoment + bSample + bGamma) ≤
        backgroundTypicalProbability
          (p := p) (q := q) (σ := σ) ν N M τ mean k := by
    simpa [backgroundTypicalProbability] using
      _root_.AppendixB.backgroundTypicalSet_measure_ge_one_sub_bad
        (p := p) (q := q) (σ := σ) (μ := ν)
        I.is_probability
        (N := N) (M := M) (τ := τ) (mean := mean)
        (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
        (k := k)
        I.K_meas I.moment_bad I.sample_bad I.gamma_bad

  /-- Half-measure version of `BackgroundBadSetBounds`, ready for the
  one-column lower-bound pipeline. -/
  theorem BackgroundBadSetBounds.backgroundTypicalProbability_ge_half
      [MeasurableSpace (SampleMatrix p q σ)]
      {ν : Measure (SampleMatrix p q σ)}
      {N M τ mean bMoment bSample bGamma : ℝ} {k : ℕ}
      (I :
        BackgroundBadSetBounds
          (p := p) (q := q) (σ := σ)
          ν N M τ mean bMoment bSample bGamma k)
      (hBad : bMoment + bSample + bGamma ≤ 1 / 2) :
      1 / 2 ≤
        backgroundTypicalProbability
          (p := p) (q := q) (σ := σ) ν N M τ mean k := by
    have h := I.backgroundTypicalProbability_ge_one_sub_bad
    linarith

  /-- Deleted-background bad-set bounds imply half-measure typicality under the
  actual deleted background law. -/
  theorem DeletedColumnBackgroundBadSetBounds.backgroundTypicalProbability_ge_half
      [DecidableEq σ]
      {α₀ : σ} {N M τ mean bMoment bSample bGamma : ℝ} {k : ℕ}
      (I :
        DeletedColumnBackgroundBadSetBounds
          (p := p) (q := q) (σ := σ)
          α₀ N M τ mean bMoment bSample bGamma k)
      (hBad : bMoment + bSample + bGamma ≤ 1 / 2) :
      1 / 2 ≤
        backgroundTypicalProbability
          (p := p) (q := q) (σ := σ)
          (deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀)
          N M τ mean k :=
    BackgroundBadSetBounds.backgroundTypicalProbability_ge_half
      (p := p) (q := q) (σ := σ)
      (ν := deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀)
      (N := N) (M := M) (τ := τ) (mean := mean)
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (k := k)
      I hBad

  /-- Deleted-background bad-set bounds imply half-measure typicality for the
  actual set `K_N`, not only for the named probability wrapper.

  This is the direct `P(K_N) ≥ 1/2` statement under the true deleted-column
  background law
  `Measure.map (deletedColumnZeroExtend α₀)
    (sphericalModelMeasure p q (DeletedColumn α₀))`. -/
  theorem DeletedColumnBackgroundBadSetBounds.backgroundTypicalSet_measure_ge_half
      [DecidableEq σ]
      {α₀ : σ} {N M τ mean bMoment bSample bGamma : ℝ} {k : ℕ}
      (I :
        DeletedColumnBackgroundBadSetBounds
          (p := p) (q := q) (σ := σ)
          α₀ N M τ mean bMoment bSample bGamma k)
      (hBad : bMoment + bSample + bGamma ≤ 1 / 2) :
      1 / 2 ≤
        (deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀).real
          (backgroundTypicalSet
            (p := p) (q := q) (σ := σ) N M τ mean k) := by
    simpa [backgroundTypicalProbability] using
      I.backgroundTypicalProbability_ge_half
        (p := p) (q := q) (σ := σ)
        (N := N) (M := M) (τ := τ) (mean := mean)
        (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
        (k := k) hBad

  /-- Slack-family form of `P(K_{d,slack}) ≥ 1/2` for the true deleted-column
  background law.

  This is the standalone background-typicality input for the slack-dependent
  upper/lower large-deviation interfaces: once the three explicit bad events
  have total deleted-background mass at most `1/2`, the corresponding typical
  set has deleted-background mass at least `1/2`, eventually in `d`. -/
  theorem eventual_deletedColumnBackgroundTypicalSet_measure_ge_half_of_bad_bounds_slack
      [DecidableEq σ]
      {α₀ : σ}
      {N M τ mean bMoment bSample bGamma : ℝ → ℕ → ℝ} {k : ℕ}
      (hBounds :
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            DeletedColumnBackgroundBadSetBounds
              (p := p) (q := q) (σ := σ)
              α₀ (N slack d) (M slack d) (τ slack d) (mean slack d)
              (bMoment slack d) (bSample slack d) (bGamma slack d) k)
      (hBad :
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            bMoment slack d + bSample slack d + bGamma slack d ≤ 1 / 2) :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          1 / 2 ≤
            (deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀).real
              (backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (N slack d) (M slack d) (τ slack d) (mean slack d) k) := by
    intro slack hslack
    filter_upwards [hBounds slack hslack, hBad slack hslack] with d hB hBad_d
    exact
      hB.backgroundTypicalSet_measure_ge_half
        (p := p) (q := q) (σ := σ)
        (N := N slack d) (M := M slack d)
        (τ := τ slack d) (mean := mean slack d)
        (bMoment := bMoment slack d)
        (bSample := bSample slack d)
        (bGamma := bGamma slack d)
        (k := k) hBad_d

  /-- The concrete three-bad-set package gives the probability lower bound for
  the spherical background typical set. -/
  theorem ConcreteSphericalBackgroundBadSetBounds.backgroundTypicalSet_measure_ge_one_sub_bad
      {N M τ mean bMoment bSample bGamma : ℝ} {k : ℕ}
      (I :
        ConcreteSphericalBackgroundBadSetBounds
          (p := p) (q := q) (σ := σ) N M τ mean bMoment bSample bGamma k)
      (hK_meas :
        MeasurableSet
          (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k)) :
      1 - (bMoment + bSample + bGamma) ≤
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
          (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k) := by
    exact
      _root_.AppendixB.backgroundTypicalSet_measure_ge_one_sub_bad
        (p := p) (q := q) (σ := σ)
        (μ := sphericalModelMeasure (p := p) (q := q) (σ := σ))
        (sphericalModelMeasure_isProbabilityMeasure (p := p) (q := q) (σ := σ))
        (N := N) (M := M) (τ := τ) (mean := mean)
        (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
        (k := k)
        hK_meas
        I.moment_bad I.sample_bad I.gamma_bad

  /-- Half-measure form for the concrete spherical background typical set. -/
  theorem ConcreteSphericalBackgroundBadSetBounds.backgroundTypicalSet_measure_ge_half
      {N M τ mean bMoment bSample bGamma : ℝ} {k : ℕ}
      (I :
        ConcreteSphericalBackgroundBadSetBounds
          (p := p) (q := q) (σ := σ) N M τ mean bMoment bSample bGamma k)
      (hK_meas :
        MeasurableSet
          (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k))
      (hBad : bMoment + bSample + bGamma ≤ 1 / 2) :
      1 / 2 ≤
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
          (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k) := by
    have h :=
      I.backgroundTypicalSet_measure_ge_one_sub_bad
        (p := p) (q := q) (σ := σ)
        (N := N) (M := M) (τ := τ) (mean := mean)
        (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
        (k := k)
        hK_meas
    linarith

  /-- The concrete three-bad-set package, rewritten in terms of the named
  background typicality probability. -/
  theorem ConcreteSphericalBackgroundBadSetBounds.backgroundTypicalProbability_ge_half
      {N M τ mean bMoment bSample bGamma : ℝ} {k : ℕ}
      (I :
        ConcreteSphericalBackgroundBadSetBounds
          (p := p) (q := q) (σ := σ) N M τ mean bMoment bSample bGamma k)
      (hK_meas :
        MeasurableSet
          (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k))
      (hBad : bMoment + bSample + bGamma ≤ 1 / 2) :
      1 / 2 ≤
        backgroundTypicalProbability
          (p := p) (q := q) (σ := σ)
          (sphericalModelMeasure (p := p) (q := q) (σ := σ))
          N M τ mean k := by
    simpa [backgroundTypicalProbability] using
      I.backgroundTypicalSet_measure_ge_half
        (p := p) (q := q) (σ := σ)
        (N := N) (M := M) (τ := τ) (mean := mean)
        (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
        (k := k)
        hK_meas hBad

  /-- Generic transfer of arbitrary-background bad-set estimates to the actual
  normalized deleted-column background `Y`.  This is the preferred interface:
  first identify the real background marginal in the column decomposition, then
  prove the three bad-set estimates under that marginal law. -/
  theorem SphericalOneColumnDecompositionIndependence.columnBackgroundTypicalProbability_ge_half_of_background_bad_bounds
      [MeasurableSpace (SampleMatrix p q σ)] [DecidableEq σ]
      {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
      {massLaw : Measure ℝ}
      {directionLaw : Measure (EuclideanSpace ℂ (BipIndex p q))}
      {backgroundLaw : Measure (SampleMatrix p q σ)}
      {N M τ mean bMoment bSample bGamma : ℝ} {k : ℕ}
      (hIndep :
        SphericalOneColumnDecompositionIndependence
          (p := p) (q := q) (σ := σ)
          μ α₀ massLaw directionLaw backgroundLaw)
      (I :
        BackgroundBadSetBounds
          (p := p) (q := q) (σ := σ)
          backgroundLaw N M τ mean bMoment bSample bGamma k)
      (hBad : bMoment + bSample + bGamma ≤ 1 / 2) :
      1 / 2 ≤
        columnBackgroundTypicalProbability
          (p := p) (q := q) (σ := σ) μ α₀ N M τ mean k := by
    exact
      hIndep.columnBackgroundTypicalProbability_ge_half
        (p := p) (q := q) (σ := σ)
        (N := N) (M := M) (τ := τ) (mean := mean) (k := k)
        (I.backgroundTypicalProbability_ge_half hBad)

  /-- Deleted-column specialization of the generic background-marginal transfer:
  the background law is the reduced spherical law pushed forward by zero
  extension. -/
  theorem CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence.columnBackgroundTypicalProbability_ge_half_of_deleted_background_bad_bounds
      [DecidableEq σ]
      {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
      {directionLaw : Measure (EuclideanSpace ℂ (BipIndex p q))}
      {N M τ mean bMoment bSample bGamma : ℝ} {k : ℕ}
      (hIndep :
        CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence
          (p := p) (q := q) (σ := σ) μ α₀ directionLaw)
      (I :
        DeletedColumnBackgroundBadSetBounds
          (p := p) (q := q) (σ := σ)
          α₀ N M τ mean bMoment bSample bGamma k)
      (hBad : bMoment + bSample + bGamma ≤ 1 / 2) :
      1 / 2 ≤
        columnBackgroundTypicalProbability
          (p := p) (q := q) (σ := σ) μ α₀ N M τ mean k := by
    change
      SphericalOneColumnDecompositionIndependence
        (p := p) (q := q) (σ := σ)
        μ α₀
        (canonicalColumnMassBetaMeasure (p := p) (q := q) (σ := σ))
        directionLaw
        (deletedColumnBackgroundLaw (p := p) (q := q) (σ := σ) α₀) at hIndep
    exact
      hIndep.columnBackgroundTypicalProbability_ge_half_of_background_bad_bounds
        (p := p) (q := q) (σ := σ)
        (N := N) (M := M) (τ := τ) (mean := mean)
        (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
        (k := k)
        I hBad

  /-- If the deleted-column background marginal has already been identified with
  the full concrete spherical law, the concrete spherical bad-set estimates give
  half-measure typicality for the actual normalized deleted-column background
  `Y`.  This is a useful special case of the generic background-marginal
  interface above, not the canonical target when the real marginal is a
  deleted-column law. -/
  theorem SphericalOneColumnDecompositionIndependence.columnBackgroundTypicalProbability_ge_half_of_concrete_bad_bounds
      [DecidableEq σ]
      {μ : Measure (SampleMatrix p q σ)} {α₀ : σ}
      {massLaw : Measure ℝ}
      {directionLaw : Measure (EuclideanSpace ℂ (BipIndex p q))}
      {N M τ mean bMoment bSample bGamma : ℝ} {k : ℕ}
      (hIndep :
        SphericalOneColumnDecompositionIndependence
          (p := p) (q := q) (σ := σ)
          μ α₀ massLaw directionLaw
          (sphericalModelMeasure (p := p) (q := q) (σ := σ)))
      (I :
        ConcreteSphericalBackgroundBadSetBounds
          (p := p) (q := q) (σ := σ) N M τ mean bMoment bSample bGamma k)
      (hK_meas :
        MeasurableSet
          (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k))
      (hBad : bMoment + bSample + bGamma ≤ 1 / 2) :
      1 / 2 ≤
        columnBackgroundTypicalProbability
          (p := p) (q := q) (σ := σ) μ α₀ N M τ mean k := by
    exact
      hIndep.columnBackgroundTypicalProbability_ge_half
        (p := p) (q := q) (σ := σ)
        (N := N) (M := M) (τ := τ) (mean := mean) (k := k)
        (I.backgroundTypicalProbability_ge_half
          (p := p) (q := q) (σ := σ)
          (N := N) (M := M) (τ := τ) (mean := mean)
          (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
          (k := k)
          hK_meas hBad)

  /-- Eventual sequence form of the generic background-marginal typicality
  transfer. -/
  theorem eventual_columnBackgroundTypicalProbability_ge_half_of_background_bad_bounds
      [MeasurableSpace (SampleMatrix p q σ)] [DecidableEq σ]
      {μ : ℕ → Measure (SampleMatrix p q σ)} {α₀ : σ}
      {massLaw : ℕ → Measure ℝ}
      {directionLaw : ℕ → Measure (EuclideanSpace ℂ (BipIndex p q))}
      {backgroundLaw : ℕ → Measure (SampleMatrix p q σ)}
      {N M τ mean bMoment bSample bGamma : ℕ → ℝ} {k : ℕ}
      (hIndep :
        ∀ᶠ d in atTop,
          SphericalOneColumnDecompositionIndependence
            (p := p) (q := q) (σ := σ)
            (μ d) α₀ (massLaw d) (directionLaw d) (backgroundLaw d))
      (hBounds :
        ∀ᶠ d in atTop,
          BackgroundBadSetBounds
            (p := p) (q := q) (σ := σ)
            (backgroundLaw d)
            (N d) (M d) (τ d) (mean d)
            (bMoment d) (bSample d) (bGamma d) k)
      (hBad :
        ∀ᶠ d in atTop,
          bMoment d + bSample d + bGamma d ≤ 1 / 2) :
      ∀ᶠ d in atTop,
        1 / 2 ≤
          columnBackgroundTypicalProbability
            (p := p) (q := q) (σ := σ)
            (μ d) α₀ (N d) (M d) (τ d) (mean d) k := by
    filter_upwards [hIndep, hBounds, hBad] with d hI hB hBad_d
    exact
      hI.columnBackgroundTypicalProbability_ge_half_of_background_bad_bounds
        (p := p) (q := q) (σ := σ)
        (N := N d) (M := M d) (τ := τ d) (mean := mean d)
        (bMoment := bMoment d) (bSample := bSample d) (bGamma := bGamma d)
        (k := k)
        hB hBad_d

  /-- Eventual sequence form for the actual deleted-column background law.

  This is the canonical background input for the one-column lower-bound
  pipeline.  The background marginal is not the full spherical law on
  `SampleMatrix p q σ`; it is the spherical law on the reduced column type
  `DeletedColumn α₀`, pushed forward to the original sample space by
  `deletedColumnZeroExtend`. -/
  theorem eventual_columnBackgroundTypicalProbability_ge_half_of_deleted_background_bad_bounds
      [DecidableEq σ]
      {μ : ℕ → Measure (SampleMatrix p q σ)} {α₀ : σ}
      {directionLaw : ℕ → Measure (EuclideanSpace ℂ (BipIndex p q))}
      {N M τ mean bMoment bSample bGamma : ℕ → ℝ} {k : ℕ}
      (hIndep :
        ∀ᶠ d in atTop,
          CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence
            (p := p) (q := q) (σ := σ)
            (μ d) α₀ (directionLaw d))
      (hBounds :
        ∀ᶠ d in atTop,
          DeletedColumnBackgroundBadSetBounds
            (p := p) (q := q) (σ := σ)
            α₀ (N d) (M d) (τ d) (mean d)
            (bMoment d) (bSample d) (bGamma d) k)
      (hBad :
        ∀ᶠ d in atTop,
          bMoment d + bSample d + bGamma d ≤ 1 / 2) :
      ∀ᶠ d in atTop,
        1 / 2 ≤
          columnBackgroundTypicalProbability
            (p := p) (q := q) (σ := σ)
            (μ d) α₀ (N d) (M d) (τ d) (mean d) k := by
    filter_upwards [hIndep, hBounds, hBad] with d hI hB hBad_d
    exact
      hI.columnBackgroundTypicalProbability_ge_half_of_deleted_background_bad_bounds
        (p := p) (q := q) (σ := σ)
        (N := N d) (M := M d) (τ := τ d) (mean := mean d)
        (bMoment := bMoment d) (bSample := bSample d) (bGamma := bGamma d)
        (k := k)
        hB hBad_d

  /-- Family-level `hBackgroundHalf` constructor for the one-column liminf
  pipeline.

  The lower-bound constructor wants a scalar family `backgroundProb a slack d`.
  This theorem closes that hypothesis from:

  * the canonical deleted-background decomposition;
  * deleted-column bad-set bounds;
  * the union-bound budget `bMoment + bSample + bGamma ≤ 1/2`;
  * the definitional identification of `backgroundProb` with the actual
    deleted-background typicality probability.

  This is the version to feed directly to
  `SpikeLowerBoundInput.of_oneColumn_probability_pipeline`. -/
  theorem eventual_backgroundProb_ge_half_of_deleted_background_bad_bounds
      [DecidableEq σ]
      {μ : ℕ → Measure (SampleMatrix p q σ)} {α₀ : σ}
      {directionLaw : ℕ → Measure (EuclideanSpace ℂ (BipIndex p q))}
      {backgroundProb : ℝ → ℝ → ℕ → ℝ}
      {N M τ mean bMoment bSample bGamma : ℝ → ℝ → ℕ → ℝ} {k : ℕ}
      (hIndep :
        ∀ᶠ d in atTop,
          CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence
            (p := p) (q := q) (σ := σ)
            (μ d) α₀ (directionLaw d))
      (hBounds :
        ∀ a : ℝ, ∀ slack : ℝ,
          ∀ᶠ d in atTop,
            DeletedColumnBackgroundBadSetBounds
              (p := p) (q := q) (σ := σ)
              α₀ (N a slack d) (M a slack d) (τ a slack d)
              (mean a slack d) (bMoment a slack d)
              (bSample a slack d) (bGamma a slack d) k)
      (hBad :
        ∀ a : ℝ, ∀ slack : ℝ,
          ∀ᶠ d in atTop,
            bMoment a slack d + bSample a slack d + bGamma a slack d ≤ 1 / 2)
      (hBackgroundProb :
        ∀ a : ℝ, ∀ slack : ℝ,
          ∀ᶠ d in atTop,
            backgroundProb a slack d =
              columnBackgroundTypicalProbability
                (p := p) (q := q) (σ := σ)
                (μ d) α₀ (N a slack d) (M a slack d)
                (τ a slack d) (mean a slack d) k) :
      ∀ a : ℝ, ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop, (1 / 2 : ℝ) ≤ backgroundProb a slack d := by
    intro a slack _hslack
    filter_upwards
      [hIndep, hBounds a slack, hBad a slack, hBackgroundProb a slack]
      with d hI hB hBad_d hProb
    rw [hProb]
    exact
      hI.columnBackgroundTypicalProbability_ge_half_of_deleted_background_bad_bounds
        (p := p) (q := q) (σ := σ)
        (N := N a slack d) (M := M a slack d)
        (τ := τ a slack d) (mean := mean a slack d)
        (bMoment := bMoment a slack d)
        (bSample := bSample a slack d)
        (bGamma := bGamma a slack d)
        (k := k)
        hB hBad_d

  /-- Eventual sequence form of background typicality for the actual normalized
  deleted-column background `Y_d`.

  This is the full-spherical-law special case of
  `eventual_columnBackgroundTypicalProbability_ge_half_of_background_bad_bounds`.
  It is kept only for situations where the background marginal really has been
  identified with the full spherical law on `SampleMatrix p q σ`.  In the
  one-column liminf pipeline, use
  `eventual_columnBackgroundTypicalProbability_ge_half_of_deleted_background_bad_bounds`
  instead. -/
  theorem eventual_columnBackgroundTypicalProbability_ge_half_of_concrete_bad_bounds
      [DecidableEq σ]
      {μ : ℕ → Measure (SampleMatrix p q σ)} {α₀ : σ}
      {massLaw : ℕ → Measure ℝ}
      {directionLaw : ℕ → Measure (EuclideanSpace ℂ (BipIndex p q))}
      {N M τ mean bMoment bSample bGamma : ℕ → ℝ} {k : ℕ}
      (hIndep :
        ∀ᶠ d in atTop,
          SphericalOneColumnDecompositionIndependence
            (p := p) (q := q) (σ := σ)
            (μ d) α₀ (massLaw d) (directionLaw d)
            (sphericalModelMeasure (p := p) (q := q) (σ := σ)))
      (hBounds :
        ∀ᶠ d in atTop,
          ConcreteSphericalBackgroundBadSetBounds
            (p := p) (q := q) (σ := σ)
            (N d) (M d) (τ d) (mean d)
            (bMoment d) (bSample d) (bGamma d) k)
      (hK_meas :
        ∀ᶠ d in atTop,
          MeasurableSet
            (backgroundTypicalSet
              (p := p) (q := q) (σ := σ)
              (N d) (M d) (τ d) (mean d) k))
      (hBad :
        ∀ᶠ d in atTop,
          bMoment d + bSample d + bGamma d ≤ 1 / 2) :
      ∀ᶠ d in atTop,
        1 / 2 ≤
          columnBackgroundTypicalProbability
            (p := p) (q := q) (σ := σ)
            (μ d) α₀ (N d) (M d) (τ d) (mean d) k := by
    filter_upwards [hIndep, hBounds, hK_meas, hBad] with d hI hB hK hBad_d
    exact
      hI.columnBackgroundTypicalProbability_ge_half_of_concrete_bad_bounds
        (p := p) (q := q) (σ := σ)
        (N := N d) (M := M d) (τ := τ d) (mean := mean d)
        (bMoment := bMoment d) (bSample := bSample d) (bGamma := bGamma d)
        (k := k)
        hB hK hBad_d

  /-- Frobenius neighbourhood of a set of backgrounds. -/
  noncomputable def frobeniusNeighborhood
    (A : Set (SampleMatrix p q σ)) (r : ℝ) :
    Set (SampleMatrix p q σ) :=
  {X | ∃ Y ∈ A, frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤ r}

/-- The absolute-deviation event for the normalized moment functional. -/
noncomputable def backgroundMomentDeviationSet
    (N eps mean : ℝ) (k : ℕ) : Set (SampleMatrix p q σ) :=
  {X | eps ≤ |backgroundMomentValue (p := p) (q := q) (σ := σ) N k X - mean|}

/-- If every point within Frobenius distance `r` of `K_N` changes the moment
by at most `localErr`, and `localErr + τ < eps`, then the `r`-neighbourhood of
`K_N` is disjoint from the `eps`-deviation event. -/
theorem frobeniusNeighborhood_backgroundTypicalSet_subset_deviation_compl
    {N M τ mean eps localErr r : ℝ} {k : ℕ}
    (hLocal :
      ∀ ⦃X Y : SampleMatrix p q σ⦄,
        Y ∈ backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k →
        frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤ r →
        |backgroundMomentValue (p := p) (q := q) (σ := σ) N k X -
          backgroundMomentValue (p := p) (q := q) (σ := σ) N k Y| ≤
            localErr)
    (hBudget : localErr + τ < eps) :
    frobeniusNeighborhood
        (p := p) (q := q) (σ := σ)
        (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k) r ⊆
      (backgroundMomentDeviationSet (p := p) (q := q) (σ := σ) N eps mean k)ᶜ := by
  intro X hX
  rcases hX with ⟨Y, hY, hdist⟩
  have hLocalXY := hLocal hY hdist
  have hYmoment :=
    backgroundTypicalSet_moment_bound
      (p := p) (q := q) (σ := σ)
      (N := N) (M := M) (τ := τ) (mean := mean) (k := k) hY
  intro hDev
  have htri :
      |backgroundMomentValue (p := p) (q := q) (σ := σ) N k X - mean| ≤
        |backgroundMomentValue (p := p) (q := q) (σ := σ) N k X -
          backgroundMomentValue (p := p) (q := q) (σ := σ) N k Y| +
        |backgroundMomentValue (p := p) (q := q) (σ := σ) N k Y - mean| := by
    have hsplit :
        backgroundMomentValue (p := p) (q := q) (σ := σ) N k X - mean =
          (backgroundMomentValue (p := p) (q := q) (σ := σ) N k X -
            backgroundMomentValue (p := p) (q := q) (σ := σ) N k Y) +
          (backgroundMomentValue (p := p) (q := q) (σ := σ) N k Y - mean) := by
      ring
    rw [hsplit]
    exact abs_add_le _ _
  simp only [backgroundMomentDeviationSet, Set.mem_setOf_eq] at hDev
  linarith

/-- Contrapositive form: the deviation event is contained in the complement of
the Frobenius neighbourhood of `K_N`.  This is the exact set inclusion fed to
spherical isoperimetry in the upper-bound strategy. -/
theorem backgroundMomentDeviationSet_subset_frobeniusNeighborhood_compl
    {N M τ mean eps localErr r : ℝ} {k : ℕ}
    (hLocal :
      ∀ ⦃X Y : SampleMatrix p q σ⦄,
        Y ∈ backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k →
        frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤ r →
        |backgroundMomentValue (p := p) (q := q) (σ := σ) N k X -
          backgroundMomentValue (p := p) (q := q) (σ := σ) N k Y| ≤
            localErr)
    (hBudget : localErr + τ < eps) :
    backgroundMomentDeviationSet (p := p) (q := q) (σ := σ) N eps mean k ⊆
      (frobeniusNeighborhood
        (p := p) (q := q) (σ := σ)
        (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k) r)ᶜ := by
  intro X hDev hNear
  have hsub :=
    frobeniusNeighborhood_backgroundTypicalSet_subset_deviation_compl
      (p := p) (q := q) (σ := σ)
      (N := N) (M := M) (τ := τ) (mean := mean)
      (eps := eps) (localErr := localErr) (r := r) (k := k)
      hLocal hBudget hNear
  exact hsub hDev

/-- Finite-dimensional upper-bound step from `K_N` to an isoperimetric tail.

If the local expansion excludes the deviation event from the Frobenius
`r`-neighbourhood of `K_N`, and the complement of that neighbourhood has the
displayed spherical-isoperimetric tail, then the deviation probability has the
same tail. -/
theorem backgroundMomentDeviation_probability_le_of_local_isoperimetry
    [MeasurableSpace (SampleMatrix p q σ)]
    {μ : Measure (SampleMatrix p q σ)}
    (hprob : IsProbabilityMeasure μ)
    {N M τ mean eps localErr r realDim radiusSq : ℝ} {k : ℕ}
    (hLocal :
      ∀ ⦃X Y : SampleMatrix p q σ⦄,
        Y ∈ backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k →
        frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤ r →
        |backgroundMomentValue (p := p) (q := q) (σ := σ) N k X -
          backgroundMomentValue (p := p) (q := q) (σ := σ) N k Y| ≤
            localErr)
    (hBudget : localErr + τ < eps)
    (hIso :
      μ.real
        ((frobeniusNeighborhood
          (p := p) (q := q) (σ := σ)
          (backgroundTypicalSet (p := p) (q := q) (σ := σ)
            N M τ mean k) r)ᶜ) ≤
        Real.exp (-(((realDim - 1) * radiusSq) / 2))) :
    μ.real
      (backgroundMomentDeviationSet (p := p) (q := q) (σ := σ)
        N eps mean k) ≤
      Real.exp (-(((realDim - 1) * radiusSq) / 2)) := by
  letI : IsProbabilityMeasure μ := hprob
  have hsubset :=
    backgroundMomentDeviationSet_subset_frobeniusNeighborhood_compl
      (p := p) (q := q) (σ := σ)
      (N := N) (M := M) (τ := τ) (mean := mean)
      (eps := eps) (localErr := localErr) (r := r) (k := k)
      hLocal hBudget
  exact (measureReal_mono hsubset (h₂ := (measure_lt_top μ _).ne)).trans hIso

end BackgroundTypicalSet

/-! ## Spherical isoperimetric constant bookkeeping -/

/-- The sharp Gaussian-type constant in the spherical isoperimetric tail used
for the upper-bound strategy:

`μ(A_rᶜ) ≤ exp (- (n - 1) r² / 2)` for a half-measure set `A`.

The theorem proving this geometric inequality is an external geometric input;
this definition only fixes the constant so that the downstream exponent
bookkeeping cannot silently change it. -/
noncomputable def sphericalIsoperimetricConstant : ℝ := 1 / 2

/-- Cost contributed by the spherical isoperimetric inequality, already
divided by the large-deviation speed.  The radius enters through its square,
which is the form used in the proof. -/
noncomputable def sphericalIsoperimetricCostSq
    (realDim radiusSq speed : ℝ) : ℝ :=
  ((realDim - 1) * radiusSq) / (2 * speed)

/-- Same cost, written with a radius rather than a squared radius. -/
noncomputable def sphericalIsoperimetricCost
    (realDim radius speed : ℝ) : ℝ :=
  sphericalIsoperimetricCostSq realDim (radius ^ 2) speed

theorem sphericalIsoperimetricConstant_pos :
    0 < sphericalIsoperimetricConstant := by
  norm_num [sphericalIsoperimetricConstant]

section SharpSphericalIsoperimetry

variable {p q σ : Type*}
variable [Fintype p] [Fintype q] [Fintype σ]
variable [DecidableEq p] [DecidableEq q]

/-- Sharp spherical isoperimetry for the ambient Hilbert--Schmidt sphere law.

This is the exact geometric theorem needed by the upper-bound strategy.  It is
stated in the ambient matrix space because the project uses the push-forward
spherical law `sphericalModelMeasure` as a measure on `SampleMatrix p q σ`.

For every measurable set `A` of spherical measure at least `1/2`, its
Frobenius `r`-neighbourhood satisfies

`μ((A_r)ᶜ) ≤ exp (- (realDim - 1) r² / 2)`.

The constant is the sharp Gaussian-type constant used downstream; all later
large-deviation constants are derived from this field, not re-entered by hand. -/
structure SharpSphericalIsoperimetry
    (μ : Measure (SampleMatrix p q σ)) (realDim : ℝ) : Prop where
  is_probability : IsProbabilityMeasure μ
  tail :
    ∀ {A : Set (SampleMatrix p q σ)} {r : ℝ},
      MeasurableSet A →
      1 / 2 ≤ μ.real A →
      0 ≤ r →
      μ.real
          ((frobeniusNeighborhood (p := p) (q := q) (σ := σ) A r)ᶜ) ≤
        Real.exp (-(((realDim - 1) * r ^ 2) / 2))

/-- Sharp spherical isoperimetry plus the local-expansion exclusion gives the
finite-dimensional deviation tail. -/
theorem backgroundMomentDeviation_probability_le_of_sharp_spherical_isoperimetry
    {μ : Measure (SampleMatrix p q σ)} {realDim N M τ mean eps localErr r : ℝ}
    {k : ℕ}
    (I : SharpSphericalIsoperimetry (p := p) (q := q) (σ := σ) μ realDim)
    (hK_meas :
      MeasurableSet
        (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k))
    (hK_half :
      1 / 2 ≤ μ.real
        (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k))
    (hr : 0 ≤ r)
    (hLocal :
      ∀ ⦃X Y : SampleMatrix p q σ⦄,
        Y ∈ backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k →
        frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤ r →
        |backgroundMomentValue (p := p) (q := q) (σ := σ) N k X -
          backgroundMomentValue (p := p) (q := q) (σ := σ) N k Y| ≤
            localErr)
    (hBudget : localErr + τ < eps) :
    μ.real
      (backgroundMomentDeviationSet (p := p) (q := q) (σ := σ)
        N eps mean k) ≤
      Real.exp (-(((realDim - 1) * r ^ 2) / 2)) := by
  exact
    backgroundMomentDeviation_probability_le_of_local_isoperimetry
      (p := p) (q := q) (σ := σ) (μ := μ)
      I.is_probability
      (N := N) (M := M) (τ := τ) (mean := mean)
      (eps := eps) (localErr := localErr) (r := r)
      (realDim := realDim) (radiusSq := r ^ 2) (k := k)
      hLocal hBudget
      (I.tail hK_meas hK_half hr)

end SharpSphericalIsoperimetry

/-- Passing from the isoperimetric probability tail to a logarithmic tail.

This is deliberately only the analytic/logarithmic conversion; the geometric
isoperimetric inequality itself is the hypothesis `htail`. -/
theorem log_probability_le_of_isoperimetric_tail_sq
    {p realDim radiusSq : ℝ}
    (hp : 0 < p)
    (htail :
      p ≤ Real.exp (-(((realDim - 1) * radiusSq) / 2))) :
    Real.log p ≤ -(((realDim - 1) * radiusSq) / 2) := by
  have hlog :
      Real.log p ≤ Real.log (Real.exp (-(((realDim - 1) * radiusSq) / 2))) :=
    Real.log_le_log hp htail
  simpa using hlog

/-- Normalized logarithmic form of the isoperimetric tail. -/
theorem normalized_log_probability_le_neg_isoperimetricCostSq
    {p realDim radiusSq speed : ℝ}
    (hp : 0 < p)
    (hspeed : 0 < speed)
    (htail :
      p ≤ Real.exp (-(((realDim - 1) * radiusSq) / 2))) :
    Real.log p / speed ≤
      -sphericalIsoperimetricCostSq realDim radiusSq speed := by
  have hlog :=
    log_probability_le_of_isoperimetric_tail_sq
      (p := p) (realDim := realDim) (radiusSq := radiusSq) hp htail
  have hdiv :
      Real.log p / speed ≤
        (-(((realDim - 1) * radiusSq) / 2)) / speed :=
    div_le_div_of_nonneg_right hlog (le_of_lt hspeed)
  have hcost :
      (-(((realDim - 1) * radiusSq) / 2)) / speed =
        -sphericalIsoperimetricCostSq realDim radiusSq speed := by
    unfold sphericalIsoperimetricCostSq
    field_simp [ne_of_gt hspeed]
  simpa [hcost] using hdiv

/-- Eventual normalized isoperimetric upper exponent from an eventual
probability tail and an eventual lower bound on the isoperimetric cost. -/
theorem eventual_log_probability_le_of_isoperimetric_cost
    {p realDim radiusSq speed : ℕ → ℝ} {rate η : ℝ}
    (hspeed : ∀ᶠ d in atTop, 0 < speed d)
    (hp : ∀ᶠ d in atTop, 0 < p d)
    (htail :
      ∀ᶠ d in atTop,
        p d ≤
          Real.exp (-(((realDim d - 1) * radiusSq d) / 2)))
    (hcost :
      ∀ᶠ d in atTop,
        rate - η ≤
          sphericalIsoperimetricCostSq (realDim d) (radiusSq d) (speed d)) :
    ∀ᶠ d in atTop,
      Real.log (p d) / speed d ≤ -rate + η := by
  filter_upwards [hspeed, hp, htail, hcost] with d hspeed_d hp_d htail_d hcost_d
  have hnorm :=
    normalized_log_probability_le_neg_isoperimetricCostSq
      (p := p d) (realDim := realDim d) (radiusSq := radiusSq d)
      (speed := speed d) hp_d hspeed_d htail_d
  linarith

/-- The constant cancellation for a complex Hilbert--Schmidt sphere.

If the real ambient dimension is `2 * N * s`, then the isoperimetric exponent
with constant `1 / 2` is exactly

`N * s * radiusSq / speed - radiusSq / (2 * speed)`.

This is the formal check that the factor `2` from complex real dimension and
the factor `1/2` from spherical isoperimetry cancel, leaving the leading
constant `λ a` rather than `2λa` or `λa/2`. -/
theorem sphericalIsoperimetricCostSq_realDim_two_mul
    {N s radiusSq speed : ℝ} (hspeed : speed ≠ 0) :
    sphericalIsoperimetricCostSq (2 * N * s) radiusSq speed =
      (N * s * radiusSq) / speed - radiusSq / (2 * speed) := by
  unfold sphericalIsoperimetricCostSq
  field_simp [hspeed]

/-- The squared radius used by the sharp isoperimetric upper-bound strategy.

If the matrix dimension parameter is `N`, the large-deviation speed is
`speed = N^(1+1/k)`, and the local-expansion radius is
`r_N = sqrt(a) * N^(-1/2 + 1/(2k))`, then

`r_N^2 = a * speed / N^2`.

The definition is written in terms of `speed` so that the constant check below
does not depend on any informal manipulation of real powers. -/
noncomputable def sharpSphericalRadiusSq
    (N speed a : ℝ) : ℝ :=
  a * speed / N ^ 2

/-- The corresponding radius `r_N`.  Most estimates use the squared form
`sharpSphericalRadiusSq`, but this name records the geometric radius itself. -/
noncomputable def sharpSphericalRadius
    (N speed a : ℝ) : ℝ :=
  Real.sqrt (sharpSphericalRadiusSq N speed a)

theorem sharpSphericalRadiusSq_nonneg
    {N speed a : ℝ} (ha : 0 ≤ a) (hspeed : 0 ≤ speed) :
    0 ≤ sharpSphericalRadiusSq N speed a := by
  unfold sharpSphericalRadiusSq
  positivity

theorem sharpSphericalRadius_sq
    {N speed a : ℝ} (ha : 0 ≤ a) (hspeed : 0 ≤ speed) :
    sharpSphericalRadius N speed a ^ 2 =
      sharpSphericalRadiusSq N speed a := by
  unfold sharpSphericalRadius
  exact Real.sq_sqrt (sharpSphericalRadiusSq_nonneg (N := N) (speed := speed) (a := a)
    ha hspeed)

section SharpSphericalIsoperimetryAtRadius

variable {p q σ : Type*}
variable [Fintype p] [Fintype q] [Fintype σ]
variable [DecidableEq p] [DecidableEq q]

/-- Sharp spherical isoperimetry at the local-expansion radius
`r_N = sqrt (a * speed / N^2)`.

This is the finite-dimensional theorem actually consumed by the upper-bound
strategy: once the background typical set has measure at least `1/2` and the
local expansion excludes the target event inside the `r_N`-neighbourhood, the
target deviation probability is bounded by

`exp (-((realDim - 1) * (a * speed / N^2)) / 2)`. -/
theorem backgroundMomentDeviation_probability_le_of_sharp_spherical_isoperimetry_at_radius
    {μ : Measure (SampleMatrix p q σ)}
    {realDim N speed a M τ mean eps localErr : ℝ} {k : ℕ}
    (I : SharpSphericalIsoperimetry (p := p) (q := q) (σ := σ) μ realDim)
    (ha : 0 ≤ a)
    (hspeed_nonneg : 0 ≤ speed)
    (hK_meas :
      MeasurableSet
        (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k))
    (hK_half :
      1 / 2 ≤ μ.real
        (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k))
    (hLocal :
      ∀ ⦃X Y : SampleMatrix p q σ⦄,
        Y ∈ backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k →
        frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
          sharpSphericalRadius N speed a →
        |backgroundMomentValue (p := p) (q := q) (σ := σ) N k X -
          backgroundMomentValue (p := p) (q := q) (σ := σ) N k Y| ≤
            localErr)
    (hBudget : localErr + τ < eps) :
    μ.real
      (backgroundMomentDeviationSet (p := p) (q := q) (σ := σ)
        N eps mean k) ≤
      Real.exp (-(((realDim - 1) * sharpSphericalRadiusSq N speed a) / 2)) := by
  have htail :=
    backgroundMomentDeviation_probability_le_of_sharp_spherical_isoperimetry
      (p := p) (q := q) (σ := σ) (μ := μ)
      (realDim := realDim) (N := N) (M := M) (τ := τ)
      (mean := mean) (eps := eps) (localErr := localErr)
      (r := sharpSphericalRadius N speed a) (k := k)
      I hK_meas hK_half (Real.sqrt_nonneg _) hLocal hBudget
  simpa [sharpSphericalRadius_sq (N := N) (speed := speed) (a := a)
    ha hspeed_nonneg] using htail

end SharpSphericalIsoperimetryAtRadius

/-- Exact scalar check at the sharp local radius.

If the speed satisfies `speed^k = N^(k+1)`, which is the algebraic form of
`speed = N^(1+1/k)`, then

`N^(k-1) * (a * speed / N^2)^k = a^k`.

This is the scalar computation behind the statement that the pure `Q^k` word
is controlled by `a^k` at the local radius. -/
theorem pureQuadratic_sharp_radius_scale_eq_of_speed_pow
    {N speed a : ℝ} {k : ℕ}
    (hk : 1 ≤ k)
    (hN : N ≠ 0)
    (hSpeedPow : speed ^ k = N ^ (k + 1)) :
    N ^ (k - 1) * (sharpSphericalRadiusSq N speed a) ^ k = a ^ k := by
  unfold sharpSphericalRadiusSq
  rw [div_pow, mul_pow, hSpeedPow]
  have hden_ne : (N ^ 2) ^ k ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hN)
  field_simp [hN, hden_ne]
  rw [← pow_mul]
  calc
    N ^ (k - 1) * a ^ k * N ^ (k + 1) =
        a ^ k * (N ^ (k - 1) * N ^ (k + 1)) := by
      ring
    _ = a ^ k * N ^ ((k - 1) + (k + 1)) := by
      rw [← pow_add]
    _ = a ^ k * N ^ (2 * k) := by
      have hnat : (k - 1) + (k + 1) = 2 * k := by omega
      rw [hnat]

/-- Pure `Q^k` bound at the sharp radius, with exact scalar speed
normalization. -/
theorem pureQuadratic_scaledTracePower_le_from_schattenHolder_sharp_radius
    [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    {N speed a : ℝ} {k : ℕ} {Q : BipMatrix p q}
    (hk : 2 ≤ k)
    (hN_nonneg : 0 ≤ N)
    (hN_ne : N ≠ 0)
    (hSpeedPow : speed ^ k = N ^ (k + 1))
    (hQHerm : Q.IsHermitian)
    (hQradius :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) Q ≤
        sharpSphericalRadiusSq N speed a) :
    |scaledTracePower (p := p) (q := q) N k Q| ≤ a ^ k := by
  have hle :
      |scaledTracePower (p := p) (q := q) N k Q| ≤ a ^ k + 0 := by
    refine
    pureQuadratic_scaledTracePower_le_from_schattenHolder_radius
      (p := p) (q := q) (N := N) (a := a) (err := 0)
      (radius := sharpSphericalRadiusSq N speed a) (k := k) (Q := Q)
      hN_nonneg hk hQHerm hQradius ?_
    rw [pureQuadratic_sharp_radius_scale_eq_of_speed_pow
      (N := N) (speed := speed) (a := a) (k := k) (le_trans (by norm_num) hk)
      hN_ne hSpeedPow]
    simp
  simpa using hle

/-- Uniform local expansion around the background typical set at the sharp
spherical radius.

This is the pointwise deterministic `hLocal` used by the upper-bound
isoperimetric step.  The pure quadratic word `Q^k` is closed no-input from the
Hermitian Schatten/Hölder bound and the sharp radius scaling.  The only
remaining hypothesis is the exact mixed-remainder estimate, stated uniformly
for all `X` in the sharp Frobenius neighbourhood of a background point
`Y ∈ K_N`.

The theorem is stated for `k ≥ 3`, the range used for the one-spike upper
strategy.  The pure `Q^k` estimate itself only needs `k ≥ 2`; the stricter
hypothesis is reserved for the mixed-word estimates which feed `hMixed`. -/
theorem localExpansion_uniformAround_backgroundTypicalSet_sharpRadius
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {N speed a M τ mean η : ℝ} {k : ℕ}
    (hk : 3 ≤ k)
    (ha : 0 ≤ a)
    (hN_nonneg : 0 ≤ N)
    (hN_ne : N ≠ 0)
    (hspeed_nonneg : 0 ≤ speed)
    (hSpeedPow : speed ^ k = N ^ (k + 1))
    (hMixed :
      ∀ ⦃X Y : SampleMatrix p q σ⦄,
        Y ∈ backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k →
        frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
          sharpSphericalRadius N speed a →
        |localExpansionMixedRemainder (p := p) (q := q) N k
            (localBackground (p := p) (q := q) (σ := σ) Y)
            (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
            (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))| ≤ η) :
    ∀ ⦃X Y : SampleMatrix p q σ⦄,
      Y ∈ backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k →
      frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
        sharpSphericalRadius N speed a →
      |backgroundMomentValue (p := p) (q := q) (σ := σ) N k X -
        backgroundMomentValue (p := p) (q := q) (σ := σ) N k Y| ≤
          a ^ k + η := by
  intro X Y hY hdist
  have hk2 : 2 ≤ k := le_trans (by norm_num) hk
  have hH_nonneg :
      0 ≤ frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) := by
    unfold frobeniusNorm
    positivity
  have hQradius :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
          (localQuadratic (p := p) (q := q) (σ := σ) (X - Y)) ≤
        sharpSphericalRadiusSq N speed a := by
    calc
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
          (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
          ≤ frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ^ 2 :=
            localQuadratic_frobeniusNorm_le
              (p := p) (q := q) (σ := σ) (X - Y)
      _ ≤ sharpSphericalRadius N speed a ^ 2 :=
            pow_le_pow_left₀ hH_nonneg hdist 2
      _ = sharpSphericalRadiusSq N speed a :=
            sharpSphericalRadius_sq (N := N) (speed := speed) (a := a)
              ha hspeed_nonneg
  have hQ :
      |scaledTracePower (p := p) (q := q) N k
          (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))| ≤
        a ^ k + 0 := by
    have hQexact :=
      pureQuadratic_scaledTracePower_le_from_schattenHolder_sharp_radius
        (p := p) (q := q) (N := N) (speed := speed) (a := a)
        (k := k)
        (Q := localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
        hk2 hN_nonneg hN_ne hSpeedPow
        (localQuadratic_isHermitian (p := p) (q := q) (σ := σ) (X - Y))
        hQradius
    simpa using hQexact
  have hloc :=
    sample_localExpansion_bound_from_quadratic_and_mixed
      (p := p) (q := q) (σ := σ)
      (N := N) (a := a) (errQ := 0) (errMix := η) (k := k)
      (X := X) (Y := Y)
      hQ
      (hMixed hY hdist)
  simpa [backgroundMomentValue] using hloc

/-- Slack-family form of the uniform local expansion around
`K_{d,slack}`.

For each positive `slack`, if the exact mixed remainder is uniformly bounded
by `η` on the sharp neighbourhood of the slack-dependent typical set, then
eventually the normalized moment varies by at most
`aSlack slack ^ k + η` throughout that neighbourhood. -/
theorem eventual_localExpansion_uniformAround_backgroundTypicalSet_sharpRadius
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {N speed : ℕ → ℝ}
    {aSlack : ℝ → ℝ}
    {M τ mean : ℝ → ℕ → ℝ}
    {k : ℕ}
    (hk : 3 ≤ k)
    (ha : ∀ slack : ℝ, 0 < slack → 0 ≤ aSlack slack)
    (hN_nonneg : ∀ᶠ d in atTop, 0 ≤ N d)
    (hN_ne : ∀ᶠ d in atTop, N d ≠ 0)
    (hspeed_nonneg : ∀ᶠ d in atTop, 0 ≤ speed d)
    (hSpeedPow :
      ∀ᶠ d in atTop, speed d ^ k = N d ^ (k + 1))
    (hMixed :
      ∀ slack : ℝ, 0 < slack →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop,
            ∀ ⦃X Y : SampleMatrix p q σ⦄,
              Y ∈ backgroundTypicalSet
                  (p := p) (q := q) (σ := σ)
                  (N d) (M slack d) (τ slack d) (mean slack d) k →
              frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
                sharpSphericalRadius (N d) (speed d) (aSlack slack) →
              |localExpansionMixedRemainder (p := p) (q := q) (N d) k
                  (localBackground (p := p) (q := q) (σ := σ) Y)
                  (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                  (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))| ≤ η) :
    ∀ slack : ℝ, 0 < slack →
      ∀ η : ℝ, 0 < η →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y : SampleMatrix p q σ⦄,
            Y ∈ backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (N d) (M slack d) (τ slack d) (mean slack d) k →
            frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
              sharpSphericalRadius (N d) (speed d) (aSlack slack) →
            |backgroundMomentValue (p := p) (q := q) (σ := σ)
                (N d) k X -
              backgroundMomentValue (p := p) (q := q) (σ := σ)
                (N d) k Y| ≤
              aSlack slack ^ k + η := by
  intro slack hslack η hη
  filter_upwards
    [hN_nonneg, hN_ne, hspeed_nonneg, hSpeedPow,
      hMixed slack hslack η hη]
    with d hNd hNned hspeedd hpowd hmixed_d
  exact
    localExpansion_uniformAround_backgroundTypicalSet_sharpRadius
      (p := p) (q := q) (σ := σ)
      (N := N d) (speed := speed d) (a := aSlack slack)
      (M := M slack d) (τ := τ slack d) (mean := mean slack d)
      (η := η) (k := k)
      hk (ha slack hslack) hNd hNned hspeedd hpowd
      (by
        intro X Y hY hdist
        exact hmixed_d hY hdist)

/-- The sharp-radius neighbourhood of `K_N` contains no `eps`-deviation once
the local-expansion budget is below `eps`.

This is the advertised deterministic inclusion

`{|F_N - mean| ≥ eps} ⊆ (K_N)_{r_N}ᶜ`,

with `r_N = sharpSphericalRadius N speed a`.  The proof is just the
contrapositive neighbourhood lemma applied to the uniform local expansion:
inside the neighbourhood, `F_N(X)` differs from `F_N(Y)` by at most
`a^k + η`, while `Y ∈ K_N` differs from `mean` by at most `τ`. -/
theorem backgroundMomentDeviationSet_subset_sharpRadiusNeighborhood_compl_of_localExpansion
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {N speed a M τ mean eps η : ℝ} {k : ℕ}
    (hk : 3 ≤ k)
    (ha : 0 ≤ a)
    (hN_nonneg : 0 ≤ N)
    (hN_ne : N ≠ 0)
    (hspeed_nonneg : 0 ≤ speed)
    (hSpeedPow : speed ^ k = N ^ (k + 1))
    (hMixed :
      ∀ ⦃X Y : SampleMatrix p q σ⦄,
        Y ∈ backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k →
        frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
          sharpSphericalRadius N speed a →
        |localExpansionMixedRemainder (p := p) (q := q) N k
            (localBackground (p := p) (q := q) (σ := σ) Y)
            (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
            (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))| ≤ η)
    (hBudget : a ^ k + η + τ < eps) :
    backgroundMomentDeviationSet
        (p := p) (q := q) (σ := σ) N eps mean k ⊆
      (frobeniusNeighborhood
        (p := p) (q := q) (σ := σ)
        (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k)
        (sharpSphericalRadius N speed a))ᶜ := by
  exact
    backgroundMomentDeviationSet_subset_frobeniusNeighborhood_compl
      (p := p) (q := q) (σ := σ)
      (N := N) (M := M) (τ := τ) (mean := mean)
      (eps := eps) (localErr := a ^ k + η)
      (r := sharpSphericalRadius N speed a) (k := k)
      (localExpansion_uniformAround_backgroundTypicalSet_sharpRadius
        (p := p) (q := q) (σ := σ)
        (N := N) (speed := speed) (a := a)
        (M := M) (τ := τ) (mean := mean) (η := η) (k := k)
        hk ha hN_nonneg hN_ne hspeed_nonneg hSpeedPow hMixed)
      hBudget

/-- Slack-family form of
`{|F_d - mean_d| ≥ eps} ⊆ (K_{d,slack})_{r_d}ᶜ`.

The scalar hypothesis `hBudget` is the only place where the chosen
slack-radius is compared with the requested deviation level:
`aSlack(slack)^k + η + τ_{d,slack} < eps`. -/
theorem eventual_backgroundMomentDeviationSet_subset_sharpRadiusNeighborhood_compl_of_localExpansion
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {N speed : ℕ → ℝ}
    {aSlack : ℝ → ℝ}
    {M τ mean : ℝ → ℕ → ℝ}
    {eps : ℝ} {k : ℕ}
    (hk : 3 ≤ k)
    (ha : ∀ slack : ℝ, 0 < slack → 0 ≤ aSlack slack)
    (hN_nonneg : ∀ᶠ d in atTop, 0 ≤ N d)
    (hN_ne : ∀ᶠ d in atTop, N d ≠ 0)
    (hspeed_nonneg : ∀ᶠ d in atTop, 0 ≤ speed d)
    (hSpeedPow :
      ∀ᶠ d in atTop, speed d ^ k = N d ^ (k + 1))
    (hMixed :
      ∀ slack : ℝ, 0 < slack →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop,
            ∀ ⦃X Y : SampleMatrix p q σ⦄,
              Y ∈ backgroundTypicalSet
                  (p := p) (q := q) (σ := σ)
                  (N d) (M slack d) (τ slack d) (mean slack d) k →
              frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
                sharpSphericalRadius (N d) (speed d) (aSlack slack) →
              |localExpansionMixedRemainder (p := p) (q := q) (N d) k
                  (localBackground (p := p) (q := q) (σ := σ) Y)
                  (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                  (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))| ≤ η)
    (hBudget :
      ∀ slack : ℝ, 0 < slack →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop, aSlack slack ^ k + η + τ slack d < eps) :
    ∀ slack : ℝ, 0 < slack →
      ∀ η : ℝ, 0 < η →
        ∀ᶠ d in atTop,
          backgroundMomentDeviationSet
              (p := p) (q := q) (σ := σ)
              (N d) eps (mean slack d) k ⊆
            (frobeniusNeighborhood
              (p := p) (q := q) (σ := σ)
              (backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (N d) (M slack d) (τ slack d) (mean slack d) k)
              (sharpSphericalRadius (N d) (speed d) (aSlack slack)))ᶜ := by
  intro slack hslack η hη
  filter_upwards
    [hN_nonneg, hN_ne, hspeed_nonneg, hSpeedPow,
      hMixed slack hslack η hη, hBudget slack hslack η hη]
    with d hNd hNned hspeedd hpowd hmixed_d hBudget_d
  exact
    backgroundMomentDeviationSet_subset_sharpRadiusNeighborhood_compl_of_localExpansion
      (p := p) (q := q) (σ := σ)
      (N := N d) (speed := speed d) (a := aSlack slack)
      (M := M slack d) (τ := τ slack d) (mean := mean slack d)
      (eps := eps) (η := η) (k := k)
      hk (ha slack hslack) hNd hNned hspeedd hpowd
      (by
        intro X Y hY hdist
        exact hmixed_d hY hdist)
      hBudget_d

/-- Sharp spherical isoperimetry applied to the local-expansion exclusion.

This is the finite-dimensional upper-tail estimate:

`P{|F_N - mean| ≥ eps}
 ≤ exp(-((realDim - 1) * r_N^2) / 2)`,

where `r_N^2 = sharpSphericalRadiusSq N speed a`.  The proof combines:

* `K_N` has mass at least `1/2`;
* the local expansion excludes the deviation event from the `r_N`-neighbourhood
  of `K_N`;
* sharp spherical isoperimetry bounds the complement of that neighbourhood. -/
theorem backgroundMomentDeviation_probability_le_sharpIso_of_localExpansion
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {μ : Measure (SampleMatrix p q σ)}
    {realDim N speed a M τ mean eps η : ℝ} {k : ℕ}
    (I : SharpSphericalIsoperimetry (p := p) (q := q) (σ := σ) μ realDim)
    (hk : 3 ≤ k)
    (ha : 0 ≤ a)
    (hN_nonneg : 0 ≤ N)
    (hN_ne : N ≠ 0)
    (hspeed_nonneg : 0 ≤ speed)
    (hSpeedPow : speed ^ k = N ^ (k + 1))
    (hK_meas :
      MeasurableSet
        (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k))
    (hK_half :
      1 / 2 ≤ μ.real
        (backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k))
    (hMixed :
      ∀ ⦃X Y : SampleMatrix p q σ⦄,
        Y ∈ backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τ mean k →
        frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
          sharpSphericalRadius N speed a →
        |localExpansionMixedRemainder (p := p) (q := q) N k
            (localBackground (p := p) (q := q) (σ := σ) Y)
            (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
            (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))| ≤ η)
    (hBudget : a ^ k + η + τ < eps) :
    μ.real
      (backgroundMomentDeviationSet (p := p) (q := q) (σ := σ)
        N eps mean k) ≤
      Real.exp (-(((realDim - 1) * sharpSphericalRadiusSq N speed a) / 2)) := by
  exact
    backgroundMomentDeviation_probability_le_of_sharp_spherical_isoperimetry_at_radius
      (p := p) (q := q) (σ := σ) (μ := μ)
      (realDim := realDim) (N := N) (speed := speed) (a := a)
      (M := M) (τ := τ) (mean := mean) (eps := eps)
      (localErr := a ^ k + η) (k := k)
      I ha hspeed_nonneg hK_meas hK_half
      (localExpansion_uniformAround_backgroundTypicalSet_sharpRadius
        (p := p) (q := q) (σ := σ)
        (N := N) (speed := speed) (a := a)
        (M := M) (τ := τ) (mean := mean) (η := η) (k := k)
        hk ha hN_nonneg hN_ne hspeed_nonneg hSpeedPow hMixed)
      hBudget

/-- Eventual slack-family form of sharp isoperimetry applied after the local
expansion.

For every positive `slack` and every positive mixed-error allowance `η`,
eventually in `d` the deviation probability is bounded by the sharp spherical
tail at the slack-dependent radius. -/
theorem eventual_backgroundMomentDeviation_probability_le_sharpIso_of_localExpansion
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {μ : ℕ → Measure (SampleMatrix p q σ)}
    {realDim N speed : ℕ → ℝ}
    {aSlack : ℝ → ℝ}
    {M τ mean : ℝ → ℕ → ℝ}
    {eps : ℝ} {k : ℕ}
    (hIso :
      ∀ᶠ d in atTop,
        SharpSphericalIsoperimetry
          (p := p) (q := q) (σ := σ) (μ d) (realDim d))
    (hk : 3 ≤ k)
    (ha : ∀ slack : ℝ, 0 < slack → 0 ≤ aSlack slack)
    (hN_nonneg : ∀ᶠ d in atTop, 0 ≤ N d)
    (hN_ne : ∀ᶠ d in atTop, N d ≠ 0)
    (hspeed_nonneg : ∀ᶠ d in atTop, 0 ≤ speed d)
    (hSpeedPow :
      ∀ᶠ d in atTop, speed d ^ k = N d ^ (k + 1))
    (hK_meas :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          MeasurableSet
            (backgroundTypicalSet
              (p := p) (q := q) (σ := σ)
              (N d) (M slack d) (τ slack d) (mean slack d) k))
    (hK_half :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          1 / 2 ≤ (μ d).real
            (backgroundTypicalSet
              (p := p) (q := q) (σ := σ)
              (N d) (M slack d) (τ slack d) (mean slack d) k))
    (hMixed :
      ∀ slack : ℝ, 0 < slack →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop,
            ∀ ⦃X Y : SampleMatrix p q σ⦄,
              Y ∈ backgroundTypicalSet
                  (p := p) (q := q) (σ := σ)
                  (N d) (M slack d) (τ slack d) (mean slack d) k →
              frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
                sharpSphericalRadius (N d) (speed d) (aSlack slack) →
              |localExpansionMixedRemainder (p := p) (q := q) (N d) k
                  (localBackground (p := p) (q := q) (σ := σ) Y)
                  (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                  (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))| ≤ η)
    (hBudget :
      ∀ slack : ℝ, 0 < slack →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop, aSlack slack ^ k + η + τ slack d < eps) :
    ∀ slack : ℝ, 0 < slack →
      ∀ η : ℝ, 0 < η →
        ∀ᶠ d in atTop,
          (μ d).real
            (backgroundMomentDeviationSet
              (p := p) (q := q) (σ := σ)
              (N d) eps (mean slack d) k) ≤
            Real.exp
              (-(((realDim d - 1) *
                  sharpSphericalRadiusSq
                    (N d) (speed d) (aSlack slack)) / 2)) := by
  intro slack hslack η hη
  filter_upwards
    [hIso, hN_nonneg, hN_ne, hspeed_nonneg, hSpeedPow,
      hK_meas slack hslack, hK_half slack hslack,
      hMixed slack hslack η hη, hBudget slack hslack η hη]
    with d hIso_d hNd hNned hspeedd hpowd hKmeas_d hKhalf_d hmixed_d hBudget_d
  exact
    backgroundMomentDeviation_probability_le_sharpIso_of_localExpansion
      (p := p) (q := q) (σ := σ) (μ := μ d)
      (realDim := realDim d) (N := N d) (speed := speed d)
      (a := aSlack slack) (M := M slack d) (τ := τ slack d)
      (mean := mean slack d) (eps := eps) (η := η) (k := k)
      hIso_d hk (ha slack hslack) hNd hNned hspeedd hpowd
      hKmeas_d hKhalf_d
      (by
        intro X Y hY hdist
        exact hmixed_d hY hdist)
      hBudget_d

/-- Direct production of the `htail` hypothesis for the slack-dependent sharp
upper-bound constructor.

Choose a positive mixed-error allowance `etaSlack slack`; if the public target
probability is definitionally/equationally the deviation probability, sharp
isoperimetry and the local expansion give exactly the required tail bound. -/
theorem eventual_targetProbability_le_sharp_spherical_tail_of_localExpansion
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {targetProb : ℕ → ℝ}
    {μ : ℕ → Measure (SampleMatrix p q σ)}
    {realDim N speed : ℕ → ℝ}
    {aSlack etaSlack : ℝ → ℝ}
    {M τ mean : ℝ → ℕ → ℝ}
    {eps : ℝ} {k : ℕ}
    (hTarget :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          targetProb d =
            (μ d).real
              (backgroundMomentDeviationSet
                (p := p) (q := q) (σ := σ)
                (N d) eps (mean slack d) k))
    (hIso :
      ∀ᶠ d in atTop,
        SharpSphericalIsoperimetry
          (p := p) (q := q) (σ := σ) (μ d) (realDim d))
    (hk : 3 ≤ k)
    (ha : ∀ slack : ℝ, 0 < slack → 0 ≤ aSlack slack)
    (hEta : ∀ slack : ℝ, 0 < slack → 0 < etaSlack slack)
    (hN_nonneg : ∀ᶠ d in atTop, 0 ≤ N d)
    (hN_ne : ∀ᶠ d in atTop, N d ≠ 0)
    (hspeed_nonneg : ∀ᶠ d in atTop, 0 ≤ speed d)
    (hSpeedPow :
      ∀ᶠ d in atTop, speed d ^ k = N d ^ (k + 1))
    (hK_meas :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          MeasurableSet
            (backgroundTypicalSet
              (p := p) (q := q) (σ := σ)
              (N d) (M slack d) (τ slack d) (mean slack d) k))
    (hK_half :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          1 / 2 ≤ (μ d).real
            (backgroundTypicalSet
              (p := p) (q := q) (σ := σ)
              (N d) (M slack d) (τ slack d) (mean slack d) k))
    (hMixed :
      ∀ slack : ℝ, 0 < slack →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop,
            ∀ ⦃X Y : SampleMatrix p q σ⦄,
              Y ∈ backgroundTypicalSet
                  (p := p) (q := q) (σ := σ)
                  (N d) (M slack d) (τ slack d) (mean slack d) k →
              frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
                sharpSphericalRadius (N d) (speed d) (aSlack slack) →
              |localExpansionMixedRemainder (p := p) (q := q) (N d) k
                  (localBackground (p := p) (q := q) (σ := σ) Y)
                  (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                  (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))| ≤ η)
    (hBudget :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          aSlack slack ^ k + etaSlack slack + τ slack d < eps) :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        targetProb d ≤
          Real.exp
            (-(((realDim d - 1) *
                sharpSphericalRadiusSq
                  (N d) (speed d) (aSlack slack)) / 2)) := by
  intro slack hslack
  have heta := hEta slack hslack
  filter_upwards
    [hTarget slack hslack, hIso, hN_nonneg, hN_ne, hspeed_nonneg, hSpeedPow,
      hK_meas slack hslack, hK_half slack hslack,
      hMixed slack hslack (etaSlack slack) heta, hBudget slack hslack]
    with d hTarget_d hIso_d hNd hNned hspeedd hpowd hKmeas_d hKhalf_d hmixed_d
      hBudget_d
  rw [hTarget_d]
  exact
    backgroundMomentDeviation_probability_le_sharpIso_of_localExpansion
      (p := p) (q := q) (σ := σ) (μ := μ d)
      (realDim := realDim d) (N := N d) (speed := speed d)
      (a := aSlack slack) (M := M slack d) (τ := τ slack d)
      (mean := mean slack d) (eps := eps) (η := etaSlack slack)
      (k := k)
      hIso_d hk (ha slack hslack) hNd hNned hspeedd hpowd
      hKmeas_d hKhalf_d
      (by
        intro X Y hY hdist
        exact hmixed_d hY hdist)
      hBudget_d

/-- Exact sharp-cost identity at the local-expansion radius.

For real sphere dimension `2*N*s` and squared radius
`r_N^2 = a * speed / N^2`, the sharp spherical-isoperimetric exponent

`((2*N*s - 1) * r_N^2) / (2 * speed)`

divided by `speed` is exactly

`a * s / N - a / (2*N^2)`.

This is the formal constant check: no extra factor `2`, `1/2`, or `k` is
hidden in the spherical-isoperimetric step. -/
theorem sphericalIsoperimetricCostSq_sharp_radius
    {N s speed a : ℝ} (hN : N ≠ 0) (hspeed : speed ≠ 0) :
    sphericalIsoperimetricCostSq
        (2 * N * s) (sharpSphericalRadiusSq N speed a) speed =
      a * s / N - a / (2 * N ^ 2) := by
  rw [sphericalIsoperimetricCostSq_realDim_two_mul
    (N := N) (s := s) (radiusSq := sharpSphericalRadiusSq N speed a)
    (speed := speed) hspeed]
  unfold sharpSphericalRadiusSq
  field_simp [hN, hspeed]

/-- Eventual lower bound on the sharp spherical-isoperimetric cost at the
local-expansion radius `r_N`.

The two scalar hypotheses are exactly the two terms in

`a*s/N - a/(2*N^2)`.

Thus the proof separates the leading aspect-ratio term from the sharp
finite-dimensional correction coming from the `-1` in `(n-1)`. -/
theorem eventual_isoperimetricCostSq_lower_sharp_radius
    {N s speed a : ℕ → ℝ} {rate η : ℝ}
    (hN : ∀ᶠ d in atTop, N d ≠ 0)
    (hspeed : ∀ᶠ d in atTop, speed d ≠ 0)
    (hmain :
      ∀ᶠ d in atTop,
        rate - η / 2 ≤ a d * s d / N d)
    (hremainder :
      ∀ᶠ d in atTop,
        a d / (2 * (N d) ^ 2) ≤ η / 2) :
    ∀ᶠ d in atTop,
      rate - η ≤
        sphericalIsoperimetricCostSq
          (2 * N d * s d)
          (sharpSphericalRadiusSq (N d) (speed d) (a d))
          (speed d) := by
  filter_upwards [hN, hspeed, hmain, hremainder] with d hN_d hspeed_d hmain_d hrem_d
  rw [sphericalIsoperimetricCostSq_sharp_radius
    (N := N d) (s := s d) (speed := speed d) (a := a d) hN_d hspeed_d]
  linarith

/-- Sharp spherical-isoperimetric logarithmic tail at the local-expansion
radius `r_N`.

The geometric input is the probability tail

`p_d ≤ exp(-((2*N_d*s_d - 1) r_N^2)/2)`.

This theorem proves the full normalized exponent consequence at the exact
radius `r_N`, including the sharp finite-dimensional correction. -/
theorem eventual_log_probability_le_of_sharp_spherical_isoperimetry_at_radius
    {p N s speed a : ℕ → ℝ} {rate η : ℝ}
    (hspeed_pos : ∀ᶠ d in atTop, 0 < speed d)
    (hp : ∀ᶠ d in atTop, 0 < p d)
    (hN : ∀ᶠ d in atTop, N d ≠ 0)
    (htail :
      ∀ᶠ d in atTop,
        p d ≤
          Real.exp
            (-(((2 * N d * s d - 1) *
                sharpSphericalRadiusSq (N d) (speed d) (a d)) / 2)))
    (hmain :
      ∀ᶠ d in atTop,
        rate - η / 2 ≤ a d * s d / N d)
    (hremainder :
      ∀ᶠ d in atTop,
        a d / (2 * (N d) ^ 2) ≤ η / 2) :
    ∀ᶠ d in atTop,
      Real.log (p d) / speed d ≤ -rate + η := by
  have hspeed_ne :
      ∀ᶠ d in atTop, speed d ≠ 0 := by
    filter_upwards [hspeed_pos] with d hd
    exact ne_of_gt hd
  exact eventual_log_probability_le_of_isoperimetric_cost
    (p := p)
    (realDim := fun d => 2 * N d * s d)
    (radiusSq := fun d => sharpSphericalRadiusSq (N d) (speed d) (a d))
    (speed := speed)
    (rate := rate) (η := η)
    hspeed_pos hp htail
    (eventual_isoperimetricCostSq_lower_sharp_radius
      (N := N) (s := s) (speed := speed) (a := a)
      (rate := rate) (η := η) hN hspeed_ne hmain hremainder)

/-- Lower-bound the normalized isoperimetric cost from the leading
`N*s*radiusSq/speed` term and the small `radiusSq/(2*speed)` correction. -/
theorem eventual_isoperimetricCostSq_lower_realDim_two_mul
    {N s radiusSq speed : ℕ → ℝ} {rate η : ℝ}
    (hspeed : ∀ᶠ d in atTop, speed d ≠ 0)
    (hmain :
      ∀ᶠ d in atTop,
        rate - η / 2 ≤ (N d * s d * radiusSq d) / speed d)
    (hremainder :
      ∀ᶠ d in atTop,
        radiusSq d / (2 * speed d) ≤ η / 2) :
    ∀ᶠ d in atTop,
      rate - η ≤
        sphericalIsoperimetricCostSq
          (2 * N d * s d) (radiusSq d) (speed d) := by
  filter_upwards [hspeed, hmain, hremainder] with d hspeed_d hmain_d hrem_d
  rw [sphericalIsoperimetricCostSq_realDim_two_mul (N := N d) (s := s d)
    (radiusSq := radiusSq d) (speed := speed d) hspeed_d]
  linarith

/-! ## Abstract upper-bound bookkeeping -/

/-- Abstract input for the corresponding spike-speed upper bound.

This is deliberately only an exponent interface.  In the concrete random-matrix
problem, the field `target_event_upper` is the hard large-deviation upper bound:
it says that the whole target deviation probability has cost at least
`lam * root` at the spike speed. -/
structure AbstractSpikeUpperBoundInput
    (p speed : ℕ → ℝ) (root lam : ℝ) : Prop where
  lambda_pos : 0 < lam
  speed_pos_eventually : ∀ᶠ d in atTop, 0 < speed d
  target_event_upper :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        Real.log (p d) ≤ -(lam * root - slack) * speed d

/-- A probability upper bound transfers to the target probability when the
target event is dominated by the comparison event.

In applications `q d` is the probability of a covering event or net-union
event.  Positivity of `p d` is included explicitly because the formal real
logarithm is total at zero, while the intended large-deviation statement is
logarithmic for positive probabilities. -/
theorem abstractSpikeUpperBoundInput_of_probability_upper
    {p q speed : ℕ → ℝ} {root lam : ℝ}
    (hlam : 0 < lam)
    (hspeed : ∀ᶠ d in atTop, 0 < speed d)
    (hppos : ∀ᶠ d in atTop, 0 < p d)
    (hdom : ∀ᶠ d in atTop, p d ≤ q d)
    (hqUpper :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          Real.log (q d) ≤ -(lam * root - slack) * speed d) :
    AbstractSpikeUpperBoundInput p speed root lam where
  lambda_pos := hlam
  speed_pos_eventually := hspeed
  target_event_upper := by
    intro slack hslack
    filter_upwards [hqUpper slack hslack, hppos, hdom] with d hq hp_pos hpq
    have hlog_mono : Real.log (p d) ≤ Real.log (q d) :=
      Real.log_le_log hp_pos hpq
    exact le_trans hlog_mono hq

/-- Eventual upper exponent obtained from the upper-bound inputs.

This is the formal limsup-style conclusion in an `Eventually` form: for every
`η > 0`, the normalized logarithmic probability is eventually at most
`-lam * root + η`. -/
theorem AbstractSpikeUpperBoundInput.eventual_log_over_speed_upper
    {p speed : ℕ → ℝ} {root lam : ℝ}
    (I : AbstractSpikeUpperBoundInput p speed root lam) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (p d) / speed d ≤ -(lam * root) + η := by
  intro η hη
  let slack : ℝ := η / 2
  have hslack : 0 < slack := by
    dsimp [slack]
    positivity
  have htail := I.target_event_upper slack hslack
  filter_upwards [I.speed_pos_eventually, htail] with d hspeed hlog
  have hdiv :
      Real.log (p d) / speed d ≤
        (-(lam * root - slack) * speed d) / speed d :=
    div_le_div_of_nonneg_right hlog (le_of_lt hspeed)
  have hcancel :
      (-(lam * root - slack) * speed d) / speed d =
        -(lam * root - slack) := by
    field_simp [ne_of_gt hspeed]
  have hmain : -(lam * root - slack) ≤ -(lam * root) + η := by
    dsimp [slack]
    linarith
  rw [hcancel] at hdiv
  exact le_trans hdiv hmain

/-- Conditional sharp-spherical upper-bound packaging.

This theorem turns the explicit isoperimetric tail at the local-expansion
radius into the abstract spike-speed upper-bound input.  It does not prove the
tail hypothesis `htail`; in the random-matrix application that hypothesis is
the hard upper-LDP content.  The hypotheses are exactly the remaining
conditional facts:

* the target probability is assumed to be bounded by the sharp spherical tail;
* the leading isoperimetric cost `a_d s_d / N_d` approaches at least
  `lam * root`;
* the finite-dimensional correction `a_d/(2 N_d^2)` is negligible.

All logarithmic normalization and constant bookkeeping is proved here. -/
theorem abstractSpikeUpperBoundInput_of_sharp_spherical_isoperimetry
    {p N s speed a : ℕ → ℝ} {root lam : ℝ}
    (hlam : 0 < lam)
    (hspeed_pos : ∀ᶠ d in atTop, 0 < speed d)
    (hp : ∀ᶠ d in atTop, 0 < p d)
    (hN : ∀ᶠ d in atTop, N d ≠ 0)
    (htail :
      ∀ᶠ d in atTop,
        p d ≤
          Real.exp
            (-(((2 * N d * s d - 1) *
                sharpSphericalRadiusSq (N d) (speed d) (a d)) / 2)))
    (hmain :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          lam * root - slack / 2 ≤ a d * s d / N d)
    (hremainder :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          a d / (2 * (N d) ^ 2) ≤ slack / 2) :
    AbstractSpikeUpperBoundInput p speed root lam where
  lambda_pos := hlam
  speed_pos_eventually := hspeed_pos
  target_event_upper := by
    intro slack hslack
    have hnorm :=
      eventual_log_probability_le_of_sharp_spherical_isoperimetry_at_radius
        (p := p) (N := N) (s := s) (speed := speed) (a := a)
        (rate := lam * root) (η := slack)
        hspeed_pos hp hN htail (hmain slack hslack) (hremainder slack hslack)
    filter_upwards [hnorm, hspeed_pos] with d hnorm_d hspeed_d
    have hmul :
        (Real.log (p d) / speed d) * speed d ≤
          (-(lam * root) + slack) * speed d :=
      mul_le_mul_of_nonneg_right hnorm_d (le_of_lt hspeed_d)
    have hleft :
        (Real.log (p d) / speed d) * speed d = Real.log (p d) := by
      field_simp [ne_of_gt hspeed_d]
    have hright :
        (-(lam * root) + slack) * speed d =
          -(lam * root - slack) * speed d := by
      ring
    rwa [hleft, hright] at hmul

/-- Slack-dependent sharp-spherical upper-bound packaging.

This is the optimized-radius variant of
`abstractSpikeUpperBoundInput_of_sharp_spherical_isoperimetry`.  Instead of
using one fixed radius sequence `a d` for every logarithmic slack, it allows
the proof to choose a scalar `aSlack slack < root` after the requested slack is
known.  The hypotheses split the sharp cost into the three finite checks used
in the proof:

* `hchoose`: the chosen scalar is below the limiting spike radius and has
  `lam * aSlack` within `slack/4` of `lam * root`;
* `haspect`: the concrete aspect-ratio term `aSlack * s_d / N_d` is within
  another `slack/4` of `lam * aSlack`;
* `hremainder`: the sharp finite-dimensional correction
  `aSlack / (2 N_d^2)` is absorbed by the remaining slack.

The tail domination hypothesis is also slack-dependent, because it must be
checked at the radius chosen for that slack. -/
theorem abstractSpikeUpperBoundInput_of_sharp_spherical_isoperimetry_slack_radius
    {p N s speed : ℕ → ℝ} {aSlack : ℝ → ℝ} {root lam : ℝ}
    (hlam : 0 < lam)
    (hspeed_pos : ∀ᶠ d in atTop, 0 < speed d)
    (hp : ∀ᶠ d in atTop, 0 < p d)
    (hN : ∀ᶠ d in atTop, N d ≠ 0)
    (hchoose :
      ∀ slack : ℝ, 0 < slack →
        0 ≤ aSlack slack ∧
          aSlack slack < root ∧
            lam * root - slack / 4 ≤ lam * aSlack slack)
    (htail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          p d ≤
            Real.exp
              (-(((2 * N d * s d - 1) *
                  sharpSphericalRadiusSq (N d) (speed d) (aSlack slack)) / 2)))
    (haspect :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          lam * aSlack slack - slack / 4 ≤
            aSlack slack * s d / N d)
    (hremainder :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          aSlack slack / (2 * (N d) ^ 2) ≤ slack / 2) :
    AbstractSpikeUpperBoundInput p speed root lam where
  lambda_pos := hlam
  speed_pos_eventually := hspeed_pos
  target_event_upper := by
    intro slack hslack
    let a : ℕ → ℝ := fun _ => aSlack slack
    have hchoose_slack := hchoose slack hslack
    have hmain :
        ∀ᶠ d in atTop,
          lam * root - slack / 2 ≤ a d * s d / N d := by
      filter_upwards [haspect slack hslack] with d hd
      dsimp [a]
      linarith [hchoose_slack.2.2, hd]
    have htail' :
        ∀ᶠ d in atTop,
          p d ≤
            Real.exp
              (-(((2 * N d * s d - 1) *
                  sharpSphericalRadiusSq (N d) (speed d) (a d)) / 2)) := by
      simpa [a] using htail slack hslack
    have hremainder' :
        ∀ᶠ d in atTop,
          a d / (2 * (N d) ^ 2) ≤ slack / 2 := by
      simpa [a] using hremainder slack hslack
    have hnorm :=
      eventual_log_probability_le_of_sharp_spherical_isoperimetry_at_radius
        (p := p) (N := N) (s := s) (speed := speed) (a := a)
        (rate := lam * root) (η := slack)
        hspeed_pos hp hN htail' hmain hremainder'
    filter_upwards [hnorm, hspeed_pos] with d hnorm_d hspeed_d
    have hmul :
        (Real.log (p d) / speed d) * speed d ≤
          (-(lam * root) + slack) * speed d :=
      mul_le_mul_of_nonneg_right hnorm_d (le_of_lt hspeed_d)
    have hleft :
        (Real.log (p d) / speed d) * speed d = Real.log (p d) := by
      field_simp [ne_of_gt hspeed_d]
    have hright :
        (-(lam * root) + slack) * speed d =
          -(lam * root - slack) * speed d := by
      ring
    rwa [hleft, hright] at hmul

/-! ## Concrete Appendix B speed and rate -/

/-- The spike lower-bound speed, written as `d^(2+2/k)`.

For the paper application `k ≥ 2`; the definition is total because real
division is total in the formal library.  The corresponding hypotheses should
still assume the intended `0 < k` when the expression is used analytically. -/
noncomputable def spikeSpeed (k d : ℕ) : ℝ :=
  (d : ℝ) ^ (2 + (2 : ℝ) / (k : ℝ))

/-- The spike root `ε^(1/k)`. -/
noncomputable def spikeRoot (k : ℕ) (ε : ℝ) : ℝ :=
  ε ^ ((1 : ℝ) / (k : ℝ))

/-- The spike lower-bound rate `lam ε^(1/k)`. -/
noncomputable def spikeRate (k : ℕ) (lam ε : ℝ) : ℝ :=
  lam * spikeRoot k ε

/-! ### Scalar asymptotic closures for the spike-speed pipeline -/

/-- If `cost/speed → 0` and the speed is eventually positive, then `cost` is
eventually absorbed by any fixed positive multiple of `speed`.

This is the reusable scalar closure behind all `o(speed)` bookkeeping in the
one-column lower-bound pipeline. -/
theorem eventual_cost_le_mul_speed_of_tendsto_div_zero
    {cost speed : ℕ → ℝ} {slack : ℝ}
    (hslack : 0 < slack)
    (hspeed : ∀ᶠ d in atTop, 0 < speed d)
    (hlim : Tendsto (fun d => cost d / speed d) atTop (nhds 0)) :
    ∀ᶠ d in atTop, cost d ≤ slack * speed d := by
  have hlt : ∀ᶠ d in atTop, cost d / speed d < slack :=
    hlim.eventually (eventually_lt_nhds hslack)
  filter_upwards [hspeed, hlt] with d hs hd
  have hle : cost d / speed d * speed d ≤ slack * speed d :=
    mul_le_mul_of_nonneg_right (le_of_lt hd) (le_of_lt hs)
  simpa [div_mul_cancel₀ _ (ne_of_gt hs)] using hle

/-- If `cost/speed → L`, then `cost` is eventually bounded by
`(L + slack) speed`, provided the speed is eventually positive. -/
theorem eventual_cost_le_limit_add_mul_speed_of_tendsto_div
    {cost speed : ℕ → ℝ} {L slack : ℝ}
    (hslack : 0 < slack)
    (hspeed : ∀ᶠ d in atTop, 0 < speed d)
    (hlim : Tendsto (fun d => cost d / speed d) atTop (nhds L)) :
    ∀ᶠ d in atTop, cost d ≤ (L + slack) * speed d := by
  have hle_ratio : ∀ᶠ d in atTop, cost d / speed d ≤ L + slack :=
    hlim.eventually (eventually_le_nhds (by linarith))
  filter_upwards [hspeed, hle_ratio] with d hs hd
  have hle : cost d / speed d * speed d ≤ (L + slack) * speed d :=
    mul_le_mul_of_nonneg_right hd (le_of_lt hs)
  simpa [div_mul_cancel₀ _ (ne_of_gt hs)] using hle

/-- The concrete spike speed is eventually positive for every positive
moment order. -/
theorem spikeSpeed_pos_eventually {k : ℕ} (_hk : 0 < k) :
    ∀ᶠ d in atTop, 0 < spikeSpeed k d := by
  filter_upwards [eventually_gt_atTop 0] with d hd
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  exact Real.rpow_pos_of_pos hdR _

/-- The concrete spike speed tends to `+∞` for every positive moment order. -/
theorem spikeSpeed_tendsto_atTop {k : ℕ} (hk : 0 < k) :
    Tendsto (spikeSpeed k) atTop atTop := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hexp : 0 < 2 + (2 : ℝ) / (k : ℝ) := by positivity
  simpa [spikeSpeed] using
    ((tendsto_rpow_atTop hexp).comp tendsto_natCast_atTop_atTop)

/-- The spike root is positive when the deviation size and moment order are
positive. -/
theorem spikeRoot_pos {k : ℕ} (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) :
    0 < spikeRoot k ε := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  unfold spikeRoot
  exact Real.rpow_pos_of_pos hε _

/-- Any fixed background probability lower bound `1/2` is negligible at a
speed tending to infinity. -/
theorem eventual_backgroundAbsorb_of_speed_tendsto_atTop
    {speed : ℕ → ℝ} {slack : ℝ}
    (hslack : 0 < slack)
    (hspeed : Tendsto speed atTop atTop) :
    ∀ᶠ d in atTop,
      -(slack / 3) * speed d ≤ Real.log (1 / 2 : ℝ) := by
  let A : ℝ := -Real.log (1 / 2 : ℝ) / (slack / 3)
  have hcoeff_pos : 0 < slack / 3 := by positivity
  have htail : ∀ᶠ d in atTop, A ≤ speed d :=
    hspeed.eventually_ge_atTop A
  filter_upwards [htail] with d hd
  have hmul : -(slack / 3) * speed d ≤ -(slack / 3) * A :=
    mul_le_mul_of_nonpos_left hd (by linarith)
  have hA : -(slack / 3) * A = Real.log (1 / 2 : ℝ) := by
    dsimp [A]
    field_simp [ne_of_gt hcoeff_pos]
  simpa [hA] using hmul

/-- Concrete background-absorption scalar for the spike speed. -/
theorem eventual_backgroundAbsorb_spikeSpeed
    {k : ℕ} (hk : 0 < k) {slack : ℝ} (hslack : 0 < slack) :
    ∀ᶠ d in atTop,
      -(slack / 3) * spikeSpeed k d ≤ Real.log (1 / 2 : ℝ) :=
  eventual_backgroundAbsorb_of_speed_tendsto_atTop
    (speed := spikeSpeed k) hslack (spikeSpeed_tendsto_atTop hk)

/-- Cap-cost scalar closure: once `2 Ncap log Ncap` is `o(spikeSpeed k)`,
the projective-cap cost is absorbed by the `slack/3` cap budget expected by
the family-level one-column constructor. -/
theorem eventual_capNLogNCost_le_spikeSpeed_of_tendsto_div_zero
    {Ncap : ℕ → ℕ} {k : ℕ} (hk : 0 < k)
    (hlim :
      Tendsto
        (fun d => capNLogNCost 2 (Ncap d : ℝ) / spikeSpeed k d)
        atTop (nhds 0)) :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        capNLogNCost 2 (Ncap d : ℝ) ≤ (slack / 3) * spikeSpeed k d := by
  intro slack hslack
  have hthird : 0 < slack / 3 := by positivity
  exact
    eventual_cost_le_mul_speed_of_tendsto_div_zero
      (cost := fun d => capNLogNCost 2 (Ncap d : ℝ))
      (speed := spikeSpeed k) hthird (spikeSpeed_pos_eventually hk) hlim

/-- Beta-kernel scalar closure from ratio limits.

This theorem turns the three scalar asymptotic facts

* `-log δ = o(speed)`;
* `N(2 log N - log(a speed)) = o(speed)`;
* the one-minus term divided by `speed` tends to `lam*a`;

into the exact `hBetaKernel` hypothesis consumed by
`SpikeLowerBoundInput.of_oneColumn_probability_pipeline`. -/
theorem eventual_log_lower_of_betaColumnIntervalKernel_spike_scale_split_slack_of_scalar_limits
    {N s : ℕ → ℕ} {δ speed : ℕ → ℝ}
    {lam a slack : ℝ}
    (hslack : 0 < slack)
    (hspeed : ∀ᶠ d in atTop, 0 < speed d)
    (hNpos : ∀ᶠ d in atTop, 0 < (N d : ℝ))
    (hSpikePos : ∀ᶠ d in atTop, 0 < a * speed d)
    (hDeltaPos : ∀ᶠ d in atTop, 0 < δ d)
    (hUpper :
      ∀ᶠ d in atTop,
        betaColumnIntervalUpper
          (betaColumnSpikeScale (N d : ℝ) (speed d) a) (δ d) < 1)
    (hDeltaLimit :
      Tendsto (fun d => (-Real.log (δ d)) / speed d) atTop (nhds 0))
    (hEntropyLimit :
      Tendsto
        (fun d =>
          ((N d : ℝ) *
            (2 * Real.log (N d : ℝ) - Real.log (a * speed d))) /
              speed d)
        atTop (nhds 0))
    (hOneMinusLimit :
      Tendsto
        (fun d =>
          ((((betaColumnOtherShape (N d) (s d) - 1 : ℕ) : ℝ) *
              betaColumnIntervalUpper
                (betaColumnSpikeScale (N d : ℝ) (speed d) a) (δ d) /
                (1 - betaColumnIntervalUpper
                  (betaColumnSpikeScale (N d : ℝ) (speed d) a) (δ d))) /
            speed d))
        atTop (nhds (lam * a))) :
    ∀ᶠ d in atTop,
      -(lam * a + slack / 3) * speed d ≤
        Real.log
          (betaColumnIntervalKernel (N d) (s d)
            (betaColumnSpikeScale (N d : ℝ) (speed d) a) (δ d)) := by
  have hthird : 0 < slack / 9 := by positivity
  have hDeltaCost :
      ∀ᶠ d in atTop,
        -Real.log (δ d) ≤ (slack / 9) * speed d :=
    eventual_cost_le_mul_speed_of_tendsto_div_zero
      (cost := fun d => -Real.log (δ d)) (speed := speed)
      hthird hspeed hDeltaLimit
  have hDelta :
      ∀ᶠ d in atTop,
        -(slack / 9) * speed d ≤ Real.log (δ d) := by
    filter_upwards [hDeltaCost] with d hd
    linarith
  have hEntropy :
      ∀ᶠ d in atTop,
        (N d : ℝ) *
            (2 * Real.log (N d : ℝ) - Real.log (a * speed d)) ≤
          (slack / 9) * speed d :=
    eventual_cost_le_mul_speed_of_tendsto_div_zero
      (cost := fun d =>
        (N d : ℝ) *
          (2 * Real.log (N d : ℝ) - Real.log (a * speed d)))
      (speed := speed) hthird hspeed hEntropyLimit
  have hOneMinus :
      ∀ᶠ d in atTop,
        (((betaColumnOtherShape (N d) (s d) - 1 : ℕ) : ℝ) *
            betaColumnIntervalUpper
              (betaColumnSpikeScale (N d : ℝ) (speed d) a) (δ d) /
              (1 - betaColumnIntervalUpper
                (betaColumnSpikeScale (N d : ℝ) (speed d) a) (δ d))) ≤
          (lam * a + slack / 9) * speed d :=
    eventual_cost_le_limit_add_mul_speed_of_tendsto_div
      (cost := fun d =>
        (((betaColumnOtherShape (N d) (s d) - 1 : ℕ) : ℝ) *
          betaColumnIntervalUpper
            (betaColumnSpikeScale (N d : ℝ) (speed d) a) (δ d) /
            (1 - betaColumnIntervalUpper
              (betaColumnSpikeScale (N d : ℝ) (speed d) a) (δ d))))
      (speed := speed) (L := lam * a) (slack := slack / 9)
      hthird hspeed hOneMinusLimit
  have hkernel :=
    eventual_log_lower_of_betaColumnIntervalKernel_spike_scale
      (N := N) (s := s) (δ := δ) (speed := speed)
      (lam := lam) (a := a)
      (deltaSlack := slack / 9)
      (entropySlack := slack / 9)
      (oneMinusSlack := slack / 9)
      hNpos hSpikePos hDeltaPos hUpper hDelta hEntropy hOneMinus
  filter_upwards [hkernel] with d hd
  have hweaken :
      -(lam * a + slack / 3) * speed d ≤
        -(lam * a + slack / 9 + slack / 9 + slack / 9) * speed d := by
    ring_nf
    exact le_rfl
  exact le_trans hweaken hd

/-- Concrete Appendix B spike lower-bound input at speed `d^(2+2/k)`. -/
abbrev SpikeLowerBoundInput (p : ℕ → ℝ) (k : ℕ) (lam ε : ℝ) : Prop :=
  AbstractSpikeLowerBoundInput p (spikeSpeed k) (spikeRoot k ε) lam

set_option linter.unusedSectionVars false in
/-- Paper-facing `hBackgroundHalf` constructor with the exact quantifier shape
used by `SpikeLowerBoundInput.of_oneColumn_probability_pipeline`.

The strict spike condition `spikeRoot k ε < a` is irrelevant for background
typicality; it is present only so this theorem can be passed directly as the
`hBackgroundHalf` ingredient of the one-column lower-bound pipeline. -/
theorem eventual_hBackgroundHalf_of_deleted_background_bad_bounds
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    {μ : ℕ → Measure (SampleMatrix p q σ)} {α₀ : σ}
    {directionLaw : ℕ → Measure (EuclideanSpace ℂ (BipIndex p q))}
    {backgroundProb : ℝ → ℝ → ℕ → ℝ}
    {N M τ mean bMoment bSample bGamma : ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {ε : ℝ}
    (hIndep :
      ∀ᶠ d in atTop,
        CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence
          (p := p) (q := q) (σ := σ)
          (μ d) α₀ (directionLaw d))
    (hBounds :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          DeletedColumnBackgroundBadSetBounds
            (p := p) (q := q) (σ := σ)
            α₀ (N a slack d) (M a slack d) (τ a slack d)
            (mean a slack d) (bMoment a slack d)
            (bSample a slack d) (bGamma a slack d) k)
    (hBad :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          bMoment a slack d + bSample a slack d + bGamma a slack d ≤ 1 / 2)
    (hBackgroundProb :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          backgroundProb a slack d =
            columnBackgroundTypicalProbability
              (p := p) (q := q) (σ := σ)
              (μ d) α₀ (N a slack d) (M a slack d)
              (τ a slack d) (mean a slack d) k) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop, (1 / 2 : ℝ) ≤ backgroundProb a slack d := by
  intro a _ha slack hslack
  exact
    eventual_backgroundProb_ge_half_of_deleted_background_bad_bounds
      (p := p) (q := q) (σ := σ)
      (μ := μ) (α₀ := α₀) (directionLaw := directionLaw)
      (backgroundProb := backgroundProb)
      (N := N) (M := M) (τ := τ) (mean := mean)
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (k := k)
      hIndep hBounds hBad hBackgroundProb a slack hslack

/-- Concrete Appendix B spike-speed upper-bound input.  This is the interface
for a future hard large-deviation upper bound; it is not supplied by the spike
lower-bound construction itself. -/
abbrev SpikeUpperBoundInput (p : ℕ → ℝ) (k : ℕ) (lam ε : ℝ) : Prop :=
  AbstractSpikeUpperBoundInput p (spikeSpeed k) (spikeRoot k ε) lam

/-- Conditional upper-bound constructor at the Appendix B spike speed.

This is the paper-facing version of
`abstractSpikeUpperBoundInput_of_sharp_spherical_isoperimetry`: once the
target probability is assumed to be dominated by the sharp spherical tail around
the background typical set and the aspect-ratio scalar cost tends to
`lam * ε^(1/k)`, the theorem produces `SpikeUpperBoundInput`.

This is not a certification of the upper LDP. -/
theorem SpikeUpperBoundInput.of_sharp_spherical_isoperimetry
    {p N s a : ℕ → ℝ} {k : ℕ} {lam ε : ℝ}
    (hlam : 0 < lam)
    (hspeed_pos : ∀ᶠ d in atTop, 0 < spikeSpeed k d)
    (hp : ∀ᶠ d in atTop, 0 < p d)
    (hN : ∀ᶠ d in atTop, N d ≠ 0)
    (htail :
      ∀ᶠ d in atTop,
        p d ≤
          Real.exp
            (-(((2 * N d * s d - 1) *
                sharpSphericalRadiusSq (N d) (spikeSpeed k d) (a d)) / 2)))
    (hmain :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          spikeRate k lam ε - slack / 2 ≤ a d * s d / N d)
    (hremainder :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          a d / (2 * (N d) ^ 2) ≤ slack / 2) :
    SpikeUpperBoundInput p k lam ε := by
  simpa [SpikeUpperBoundInput, spikeRate] using
    (abstractSpikeUpperBoundInput_of_sharp_spherical_isoperimetry
      (p := p) (N := N) (s := s) (speed := spikeSpeed k) (a := a)
      (root := spikeRoot k ε) (lam := lam)
      hlam hspeed_pos hp hN htail hmain hremainder)

/-- Conditional upper-bound constructor with a slack-dependent local radius.

For each requested logarithmic slack, the proof may choose a scalar
`aSlack slack < ε^(1/k)` whose cost is arbitrarily close to the limiting cost
`λ ε^(1/k)`.  This is the form needed for the optimized sharp-spherical
upper-bound strategy: the isoperimetric radius is selected after the slack is
known, rather than being fixed once and for all.

This remains a conditional upper-LDP wrapper: the hypothesis `htail` is still
the hard random-matrix domination by the sharp spherical neighbourhood tail. -/
theorem SpikeUpperBoundInput.of_sharp_spherical_isoperimetry_slack_radius
    {p N s : ℕ → ℝ} {aSlack : ℝ → ℝ} {k : ℕ} {lam ε : ℝ}
    (hlam : 0 < lam)
    (hspeed_pos : ∀ᶠ d in atTop, 0 < spikeSpeed k d)
    (hp : ∀ᶠ d in atTop, 0 < p d)
    (hN : ∀ᶠ d in atTop, N d ≠ 0)
    (hchoose :
      ∀ slack : ℝ, 0 < slack →
        0 ≤ aSlack slack ∧
          aSlack slack < spikeRoot k ε ∧
            spikeRate k lam ε - slack / 4 ≤ lam * aSlack slack)
    (htail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          p d ≤
            Real.exp
              (-(((2 * N d * s d - 1) *
                  sharpSphericalRadiusSq
                    (N d) (spikeSpeed k d) (aSlack slack)) / 2)))
    (haspect :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          lam * aSlack slack - slack / 4 ≤
            aSlack slack * s d / N d)
    (hremainder :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          aSlack slack / (2 * (N d) ^ 2) ≤ slack / 2) :
    SpikeUpperBoundInput p k lam ε := by
  simpa [SpikeUpperBoundInput, spikeRate] using
    (abstractSpikeUpperBoundInput_of_sharp_spherical_isoperimetry_slack_radius
      (p := p) (N := N) (s := s) (speed := spikeSpeed k)
      (aSlack := aSlack) (root := spikeRoot k ε) (lam := lam)
      hlam hspeed_pos hp hN hchoose htail haspect hremainder)

/-! ### Scalar closures for the slack-dependent upper-bound radius -/

/-- Canonical scalar radius used by the slack-dependent upper-bound
constructor.

For a requested logarithmic slack, this takes `root - slack/(8*lam)` when that
is nonnegative and `0` otherwise.  The `max` makes the definition total and
keeps the nonnegativity proof mechanical. -/
noncomputable def upperSlackRadius (root lam slack : ℝ) : ℝ :=
  max 0 (root - slack / (8 * lam))

/-- Scalar choice lemma for `upperSlackRadius`.

It is strictly below `root`, nonnegative, and loses only `slack/4` in the
leading cost `lam * root`.  This closes the radius-choice bookkeeping in the
optimized upper-bound constructor. -/
theorem upperSlackRadius_choice
    {root lam slack : ℝ} (hroot : 0 < root) (hlam : 0 < lam)
    (hslack : 0 < slack) :
    0 ≤ upperSlackRadius root lam slack ∧
      upperSlackRadius root lam slack < root ∧
        lam * root - slack / 4 ≤ lam * upperSlackRadius root lam slack := by
  have hden_pos : 0 < 8 * lam := by positivity
  have hcut_pos : 0 < slack / (8 * lam) := by positivity
  constructor
  · exact le_max_left _ _
  constructor
  · unfold upperSlackRadius
    exact max_lt hroot (by linarith)
  · by_cases hnonneg : 0 ≤ root - slack / (8 * lam)
    · have hmax :
          upperSlackRadius root lam slack = root - slack / (8 * lam) := by
        unfold upperSlackRadius
        exact max_eq_right hnonneg
      rw [hmax]
      have hmul : lam * (slack / (8 * lam)) = slack / 8 := by
        field_simp [ne_of_gt hlam]
      nlinarith
    · have hle : root - slack / (8 * lam) ≤ 0 := le_of_not_ge hnonneg
      have hmax : upperSlackRadius root lam slack = 0 := by
        unfold upperSlackRadius
        exact max_eq_left hle
      rw [hmax]
      have hroot_le : root ≤ slack / (8 * lam) := by linarith
      have hmul_le : lam * root ≤ slack / 8 := by
        have htmp := mul_le_mul_of_nonneg_left hroot_le (le_of_lt hlam)
        have hmul : lam * (slack / (8 * lam)) = slack / 8 := by
          field_simp [ne_of_gt hlam]
        linarith
      nlinarith

/-- Appendix-B specialization of `upperSlackRadius_choice`. -/
theorem upperSlackRadius_spike_choice
    {k : ℕ} {lam ε : ℝ} (hk : 0 < k) (hlam : 0 < lam) (hε : 0 < ε) :
    ∀ slack : ℝ, 0 < slack →
      0 ≤ upperSlackRadius (spikeRoot k ε) lam slack ∧
        upperSlackRadius (spikeRoot k ε) lam slack < spikeRoot k ε ∧
          spikeRate k lam ε - slack / 4 ≤
            lam * upperSlackRadius (spikeRoot k ε) lam slack := by
  intro slack hslack
  simpa [spikeRate] using
    upperSlackRadius_choice
      (root := spikeRoot k ε) (lam := lam) (slack := slack)
      (spikeRoot_pos hk hε) hlam hslack

/-- Aspect-ratio scalar closure for the upper-bound radius.

If `s_d/N_d → lam`, then every fixed slack-dependent radius has leading
isoperimetric cost eventually at least `lam * aSlack - slack/4`. -/
theorem eventual_upperAspect_of_tendsto_ratio
    {N s : ℕ → ℝ} {lam : ℝ} {aSlack : ℝ → ℝ}
    (hRatio : Tendsto (fun d => s d / N d) atTop (nhds lam)) :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        lam * aSlack slack - slack / 4 ≤
          aSlack slack * s d / N d := by
  intro slack hslack
  let a := aSlack slack
  have hlim :
      Tendsto (fun d => a * (s d / N d)) atTop (nhds (a * lam)) :=
    tendsto_const_nhds.mul hRatio
  have hev :
      ∀ᶠ d in atTop, a * lam - slack / 4 ≤ a * (s d / N d) :=
    hlim.eventually (eventually_ge_nhds (by linarith))
  filter_upwards [hev] with d hd
  simpa [a, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hd

/-- Finite-dimensional correction closure for the sharp spherical
isoperimetric cost. -/
theorem eventual_upperRemainder_of_tendsto_zero
    {N : ℕ → ℝ} {aSlack : ℝ → ℝ}
    (hlim :
      ∀ slack : ℝ, 0 < slack →
        Tendsto
          (fun d => aSlack slack / (2 * (N d) ^ 2))
          atTop (nhds 0)) :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        aSlack slack / (2 * (N d) ^ 2) ≤ slack / 2 := by
  intro slack hslack
  have hhalf : 0 < slack / 2 := by positivity
  exact (hlim slack hslack).eventually (eventually_le_nhds hhalf)

/-- Local-expansion budget closure.

Once the deterministic static part `aSlack^k + etaSlack` is strictly below
`eps`, any error term `τ_d → 0` is eventually absorbed. -/
theorem eventual_localExpansion_budget_of_tau_tendsto
    {aSlack etaSlack : ℝ → ℝ} {τ : ℝ → ℕ → ℝ} {eps : ℝ} {k : ℕ}
    (hGap :
      ∀ slack : ℝ, 0 < slack →
        aSlack slack ^ k + etaSlack slack < eps)
    (hTau :
      ∀ slack : ℝ, 0 < slack →
        Tendsto (τ slack) atTop (nhds 0)) :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        aSlack slack ^ k + etaSlack slack + τ slack d < eps := by
  intro slack hslack
  let gap : ℝ := eps - (aSlack slack ^ k + etaSlack slack)
  have hgap : 0 < gap := by
    dsimp [gap]
    linarith [hGap slack hslack]
  have htau : ∀ᶠ d in atTop, τ slack d < gap :=
    (hTau slack hslack).eventually (eventually_lt_nhds hgap)
  filter_upwards [htau] with d hd
  dsimp [gap] at hd
  linarith

/-- Closed scalar wrapper for the slack-dependent sharp-spherical upper-bound
strategy.

This theorem removes the purely scalar obligations from the local-expansion
upper-bound pipeline:

* the radius is chosen canonically by `upperSlackRadius`;
* `s_d/N_d → lam` supplies the leading aspect-ratio cost;
* `a/(2N_d^2) → 0` absorbs the sharp finite-dimensional correction;
* `τ_d → 0` absorbs the remaining deterministic local-expansion budget.

The genuinely geometric/random-matrix ingredients remain visible: sharp
spherical isoperimetry, half-mass of the typical set, local mixed-remainder
control, and the target-event identification. -/
theorem eventual_log_over_spikeSpeed_upper_of_localExpansion_scalar_limits
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {targetProb : ℕ → ℝ}
    {μ : ℕ → Measure (SampleMatrix p q σ)}
    {realDim N s : ℕ → ℝ}
    {etaSlack : ℝ → ℝ}
    {M τ mean : ℝ → ℕ → ℝ}
    {eps : ℝ} {k : ℕ} {lam : ℝ}
    (hk : 0 < k) (hk3 : 3 ≤ k) (hlam : 0 < lam) (hε : 0 < eps)
    (hp : ∀ᶠ d in atTop, 0 < targetProb d)
    (hTarget :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          targetProb d =
            (μ d).real
              (backgroundMomentDeviationSet
                (p := p) (q := q) (σ := σ)
                (N d) eps (mean slack d) k))
    (hIso :
      ∀ᶠ d in atTop,
        SharpSphericalIsoperimetry
          (p := p) (q := q) (σ := σ) (μ d) (realDim d))
    (hRealDim : ∀ᶠ d in atTop, realDim d = 2 * N d * s d)
    (hN_nonneg : ∀ᶠ d in atTop, 0 ≤ N d)
    (hN_ne : ∀ᶠ d in atTop, N d ≠ 0)
    (hSpeedPow :
      ∀ᶠ d in atTop, spikeSpeed k d ^ k = N d ^ (k + 1))
    (hK_meas :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          MeasurableSet
            (backgroundTypicalSet
              (p := p) (q := q) (σ := σ)
              (N d) (M slack d) (τ slack d) (mean slack d) k))
    (hK_half :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          1 / 2 ≤ (μ d).real
            (backgroundTypicalSet
              (p := p) (q := q) (σ := σ)
              (N d) (M slack d) (τ slack d) (mean slack d) k))
    (hMixed :
      ∀ slack : ℝ, 0 < slack →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop,
            ∀ ⦃X Y : SampleMatrix p q σ⦄,
              Y ∈ backgroundTypicalSet
                  (p := p) (q := q) (σ := σ)
                  (N d) (M slack d) (τ slack d) (mean slack d) k →
              frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
                sharpSphericalRadius
                  (N d) (spikeSpeed k d)
                  (upperSlackRadius (spikeRoot k eps) lam slack) →
              |localExpansionMixedRemainder (p := p) (q := q) (N d) k
                  (localBackground (p := p) (q := q) (σ := σ) Y)
                  (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                  (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))| ≤ η)
    (hRatio : Tendsto (fun d => s d / N d) atTop (nhds lam))
    (hRemainderLimit :
      ∀ slack : ℝ, 0 < slack →
        Tendsto
          (fun d =>
            upperSlackRadius (spikeRoot k eps) lam slack /
              (2 * (N d) ^ 2))
          atTop (nhds 0))
    (hEta : ∀ slack : ℝ, 0 < slack → 0 < etaSlack slack)
    (hGap :
      ∀ slack : ℝ, 0 < slack →
        upperSlackRadius (spikeRoot k eps) lam slack ^ k +
          etaSlack slack < eps)
    (hTau :
      ∀ slack : ℝ, 0 < slack →
        Tendsto (τ slack) atTop (nhds 0)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (targetProb d) / spikeSpeed k d ≤
          -spikeRate k lam eps + η := by
  let aSlack : ℝ → ℝ := fun slack =>
    upperSlackRadius (spikeRoot k eps) lam slack
  have ha : ∀ slack : ℝ, 0 < slack → 0 ≤ aSlack slack := by
    intro slack hslack
    exact (upperSlackRadius_spike_choice hk hlam hε slack hslack).1
  have hchoose :
      ∀ slack : ℝ, 0 < slack →
        0 ≤ aSlack slack ∧
          aSlack slack < spikeRoot k eps ∧
            spikeRate k lam eps - slack / 4 ≤ lam * aSlack slack := by
    intro slack hslack
    exact upperSlackRadius_spike_choice hk hlam hε slack hslack
  have hBudget :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          aSlack slack ^ k + etaSlack slack + τ slack d < eps :=
    eventual_localExpansion_budget_of_tau_tendsto
      (aSlack := aSlack) (etaSlack := etaSlack) (τ := τ)
      (eps := eps) (k := k) hGap hTau
  have hTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          targetProb d ≤
            Real.exp
              (-(((realDim d - 1) *
                  sharpSphericalRadiusSq
                    (N d) (spikeSpeed k d) (aSlack slack)) / 2)) := by
    exact
      eventual_targetProbability_le_sharp_spherical_tail_of_localExpansion
        (p := p) (q := q) (σ := σ)
        (targetProb := targetProb) (μ := μ)
        (realDim := realDim) (N := N) (speed := spikeSpeed k)
        (aSlack := aSlack) (etaSlack := etaSlack)
        (M := M) (τ := τ) (mean := mean)
        (eps := eps) (k := k)
        hTarget hIso hk3 ha hEta hN_nonneg hN_ne
        (by
          filter_upwards [spikeSpeed_pos_eventually hk] with d hd
          exact le_of_lt hd)
        hSpeedPow hK_meas hK_half hMixed hBudget
  have hTailTwoNs :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          targetProb d ≤
            Real.exp
              (-(((2 * N d * s d - 1) *
                  sharpSphericalRadiusSq
                    (N d) (spikeSpeed k d) (aSlack slack)) / 2)) := by
    intro slack hslack
    filter_upwards [hTail slack hslack, hRealDim] with d hd hdim
    rw [hdim] at hd
    simpa [mul_assoc, mul_comm, mul_left_comm] using hd
  have haspect :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          lam * aSlack slack - slack / 4 ≤
            aSlack slack * s d / N d :=
    eventual_upperAspect_of_tendsto_ratio
      (N := N) (s := s) (lam := lam) (aSlack := aSlack) hRatio
  have hremainder :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          aSlack slack / (2 * (N d) ^ 2) ≤ slack / 2 :=
    eventual_upperRemainder_of_tendsto_zero
      (N := N) (aSlack := aSlack) hRemainderLimit
  have I : SpikeUpperBoundInput targetProb k lam eps :=
    SpikeUpperBoundInput.of_sharp_spherical_isoperimetry_slack_radius
      (p := targetProb) (N := N) (s := s) (aSlack := aSlack)
      (k := k) (lam := lam) (ε := eps)
      hlam (spikeSpeed_pos_eventually hk) hp hN_ne hchoose
      hTailTwoNs haspect hremainder
  exact
    AbstractSpikeUpperBoundInput.eventual_log_over_speed_upper
      (p := targetProb) (speed := spikeSpeed k) (root := spikeRoot k eps)
      (lam := lam) I

/-- Canonical family-level one-column lower-bound constructor at the Appendix B
spike speed.

This is the constructor to use for the liminf: for each `a > ε^(1/k)` and
each logarithmic slack, the favourable event is allowed to be a different
one-column event.  Provide the one-column product decomposition

`P(E_col) = P(E_mass) P(E_cap) P(E_background)`,

the Beta interval estimate for `E_mass`, the projective cap estimate for
`E_cap`, the half-measure background estimate, and the inclusion
`E_col ⊆ target`.  These inputs return the canonical `SpikeLowerBoundInput`. -/
theorem SpikeLowerBoundInput.of_oneColumn_probability_pipeline
    {targetProb : ℕ → ℝ}
    {betaProb capProb backgroundProb columnProb : ℝ → ℝ → ℕ → ℝ}
    {N s Ncap : ℕ → ℕ} {q δ : ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {lam ε : ℝ}
    (hlam : 0 < lam)
    (hspeed : ∀ᶠ d in atTop, 0 < spikeSpeed k d)
    (hColumnIncluded :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, columnProb a slack d ≤ targetProb d)
    (hProduct :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            columnProb a slack d =
              betaProb a slack d * capProb a slack d * backgroundProb a slack d)
    (hBeta :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            BetaColumnIntervalLowerBound
              (betaProb a slack d) (N d) (s d) (q a slack d) (δ a slack d))
    (hBetaKernel :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            -(lam * a + slack / 3) * spikeSpeed k d ≤
              Real.log
                (betaColumnIntervalKernel
                  (N d) (s d) (q a slack d) (δ a slack d)))
    (hNcap : ∀ᶠ d in atTop, 1 ≤ Ncap d)
    (hCap :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ProjectiveCapProbabilityLowerBound
              (capProb a slack d) (Ncap d) (1 / (Ncap d : ℝ)))
    (hCapCost :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          capNLogNCost 2 (Ncap d : ℝ) ≤ (slack / 3) * spikeSpeed k d)
    (hBackgroundHalf :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, (1 / 2 : ℝ) ≤ backgroundProb a slack d)
    (hBackgroundAbsorb :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          -(slack / 3) * spikeSpeed k d ≤ Real.log (1 / 2 : ℝ)) :
    SpikeLowerBoundInput targetProb k lam ε := by
  simpa [SpikeLowerBoundInput] using
    (abstractSpikeLowerBoundInput_of_oneColumn_probability_pipeline
      (targetProb := targetProb) (speed := spikeSpeed k)
      (betaProb := betaProb) (capProb := capProb)
      (backgroundProb := backgroundProb) (columnProb := columnProb)
      (N := N) (s := s) (Ncap := Ncap) (q := q) (δ := δ)
      (root := spikeRoot k ε) (lam := lam)
      hlam hspeed hColumnIncluded hProduct hBeta hBetaKernel
      hNcap hCap hCapCost hBackgroundHalf hBackgroundAbsorb)

/-- Family-level one-column lower-bound constructor with the scalar
asymptotics closed.

Compared with `SpikeLowerBoundInput.of_oneColumn_probability_pipeline`, this
version asks for the three transparent Beta-kernel ratio limits and for the
cap-cost ratio limit.  It then supplies internally:

* positivity of the spike speed;
* the Beta-kernel logarithmic lower bound;
* cap-cost absorption;
* background `1/2` absorption.

The mass interval is specialized to the canonical scale
`a * spikeSpeed k d / (N d)^2`. -/
theorem SpikeLowerBoundInput.of_oneColumn_probability_pipeline_scalar_limits
    {targetProb : ℕ → ℝ}
    {betaProb capProb backgroundProb columnProb : ℝ → ℝ → ℕ → ℝ}
    {N s Ncap : ℕ → ℕ} {δ : ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {lam ε : ℝ}
    (hk : 0 < k) (hlam : 0 < lam) (hε : 0 < ε)
    (hColumnIncluded :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, columnProb a slack d ≤ targetProb d)
    (hProduct :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            columnProb a slack d =
              betaProb a slack d * capProb a slack d * backgroundProb a slack d)
    (hBeta :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            BetaColumnIntervalLowerBound
              (betaProb a slack d) (N d) (s d)
              (betaColumnSpikeScale (N d : ℝ) (spikeSpeed k d) a)
              (δ a slack d))
    (hNpos :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, 0 < (N d : ℝ))
    (hDeltaPos :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, 0 < δ a slack d)
    (hUpper :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            betaColumnIntervalUpper
              (betaColumnSpikeScale (N d : ℝ) (spikeSpeed k d) a)
              (δ a slack d) < 1)
    (hDeltaLimit :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          Tendsto
            (fun d => (-Real.log (δ a slack d)) / spikeSpeed k d)
            atTop (nhds 0))
    (hEntropyLimit :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          Tendsto
            (fun d =>
              ((N d : ℝ) *
                (2 * Real.log (N d : ℝ) -
                  Real.log (a * spikeSpeed k d))) / spikeSpeed k d)
            atTop (nhds 0))
    (hOneMinusLimit :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          Tendsto
            (fun d =>
              ((((betaColumnOtherShape (N d) (s d) - 1 : ℕ) : ℝ) *
                  betaColumnIntervalUpper
                    (betaColumnSpikeScale (N d : ℝ) (spikeSpeed k d) a)
                    (δ a slack d) /
                    (1 - betaColumnIntervalUpper
                      (betaColumnSpikeScale (N d : ℝ) (spikeSpeed k d) a)
                      (δ a slack d))) /
                spikeSpeed k d))
            atTop (nhds (lam * a)))
    (hNcap : ∀ᶠ d in atTop, 1 ≤ Ncap d)
    (hCap :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ProjectiveCapProbabilityLowerBound
              (capProb a slack d) (Ncap d) (1 / (Ncap d : ℝ)))
    (hCapCostLimit :
      Tendsto
        (fun d => capNLogNCost 2 (Ncap d : ℝ) / spikeSpeed k d)
        atTop (nhds 0))
    (hBackgroundHalf :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, (1 / 2 : ℝ) ≤ backgroundProb a slack d) :
    SpikeLowerBoundInput targetProb k lam ε := by
  refine
    SpikeLowerBoundInput.of_oneColumn_probability_pipeline
      (targetProb := targetProb)
      (betaProb := betaProb) (capProb := capProb)
      (backgroundProb := backgroundProb) (columnProb := columnProb)
      (N := N) (s := s) (Ncap := Ncap)
      (q := fun a _slack d =>
        betaColumnSpikeScale (N d : ℝ) (spikeSpeed k d) a)
      (δ := δ) (k := k) (lam := lam) (ε := ε)
      hlam (spikeSpeed_pos_eventually hk)
      hColumnIncluded hProduct hBeta ?_ hNcap hCap ?_ hBackgroundHalf ?_
  · intro a ha slack hslack
    have ha_pos : 0 < a := lt_trans (spikeRoot_pos hk hε) ha
    have hSpikePos : ∀ᶠ d in atTop, 0 < a * spikeSpeed k d := by
      filter_upwards [spikeSpeed_pos_eventually hk] with d hd
      exact mul_pos ha_pos hd
    exact
      eventual_log_lower_of_betaColumnIntervalKernel_spike_scale_split_slack_of_scalar_limits
        (N := N) (s := s) (δ := δ a slack) (speed := spikeSpeed k)
        (lam := lam) (a := a) (slack := slack)
        hslack
        (spikeSpeed_pos_eventually hk)
        (hNpos a ha slack hslack)
        hSpikePos
        (hDeltaPos a ha slack hslack)
        (hUpper a ha slack hslack)
        (hDeltaLimit a ha slack hslack)
        (hEntropyLimit a ha slack hslack)
        (hOneMinusLimit a ha slack hslack)
  · exact eventual_capNLogNCost_le_spikeSpeed_of_tendsto_div_zero
      (Ncap := Ncap) (k := k) hk hCapCostLimit
  · exact fun slack hslack =>
      eventual_backgroundAbsorb_spikeSpeed (k := k) hk hslack

/-- Conditional eventual upper exponent obtained from the sharp-spherical
upper-bound packaging.

This theorem consumes the tail domination hypothesis `htail`; it does not prove
that such a tail holds for the target random-matrix deviation probability. -/
theorem eventual_log_over_spikeSpeed_upper_of_sharp_spherical_isoperimetry
    {p N s a : ℕ → ℝ} {k : ℕ} {lam ε : ℝ}
    (hlam : 0 < lam)
    (hspeed_pos : ∀ᶠ d in atTop, 0 < spikeSpeed k d)
    (hp : ∀ᶠ d in atTop, 0 < p d)
    (hN : ∀ᶠ d in atTop, N d ≠ 0)
    (htail :
      ∀ᶠ d in atTop,
        p d ≤
          Real.exp
            (-(((2 * N d * s d - 1) *
                sharpSphericalRadiusSq (N d) (spikeSpeed k d) (a d)) / 2)))
    (hmain :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          spikeRate k lam ε - slack / 2 ≤ a d * s d / N d)
    (hremainder :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          a d / (2 * (N d) ^ 2) ≤ slack / 2) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (p d) / spikeSpeed k d ≤ -spikeRate k lam ε + η := by
  intro η hη
  have I : SpikeUpperBoundInput p k lam ε :=
    SpikeUpperBoundInput.of_sharp_spherical_isoperimetry
      (p := p) (N := N) (s := s) (a := a) (k := k)
      (lam := lam) (ε := ε)
      hlam hspeed_pos hp hN htail hmain hremainder
  simpa [SpikeUpperBoundInput, spikeRate] using
    (AbstractSpikeUpperBoundInput.eventual_log_over_speed_upper
      (p := p) (speed := spikeSpeed k) (root := spikeRoot k ε)
      (lam := lam) I η hη)

/-- Conditional eventual upper exponent obtained from the slack-dependent
sharp-spherical radius constructor.

This is the optimized-radius variant of
`eventual_log_over_spikeSpeed_upper_of_sharp_spherical_isoperimetry`: for each
requested slack, the isoperimetric radius may be chosen through
`aSlack slack < ε^(1/k)`. -/
theorem eventual_log_over_spikeSpeed_upper_of_sharp_spherical_isoperimetry_slack_radius
    {p N s : ℕ → ℝ} {aSlack : ℝ → ℝ} {k : ℕ} {lam ε : ℝ}
    (hlam : 0 < lam)
    (hspeed_pos : ∀ᶠ d in atTop, 0 < spikeSpeed k d)
    (hp : ∀ᶠ d in atTop, 0 < p d)
    (hN : ∀ᶠ d in atTop, N d ≠ 0)
    (hchoose :
      ∀ slack : ℝ, 0 < slack →
        0 ≤ aSlack slack ∧
          aSlack slack < spikeRoot k ε ∧
            spikeRate k lam ε - slack / 4 ≤ lam * aSlack slack)
    (htail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          p d ≤
            Real.exp
              (-(((2 * N d * s d - 1) *
                  sharpSphericalRadiusSq
                    (N d) (spikeSpeed k d) (aSlack slack)) / 2)))
    (haspect :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          lam * aSlack slack - slack / 4 ≤
            aSlack slack * s d / N d)
    (hremainder :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          aSlack slack / (2 * (N d) ^ 2) ≤ slack / 2) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (p d) / spikeSpeed k d ≤ -spikeRate k lam ε + η := by
  intro η hη
  have I : SpikeUpperBoundInput p k lam ε :=
    SpikeUpperBoundInput.of_sharp_spherical_isoperimetry_slack_radius
      (p := p) (N := N) (s := s) (aSlack := aSlack)
      (k := k) (lam := lam) (ε := ε)
      hlam hspeed_pos hp hN hchoose htail haspect hremainder
  simpa [SpikeUpperBoundInput, spikeRate] using
    (AbstractSpikeUpperBoundInput.eventual_log_over_speed_upper
      (p := p) (speed := spikeSpeed k) (root := spikeRoot k ε)
      (lam := lam) I η hη)

/-- Direct lower exponent from the closed one-column probability pipeline.

This is the no-input-at-the-packaging-level statement: once the explicit
one-column ingredients are supplied, the theorem records

`-lam*ε^(1/k)-η ≤ log(targetProb d)/d^(2+2/k)`

eventually.

This is the final lower-bound packaging theorem.  It deliberately goes through
the paper-facing family-level constructor
`SpikeLowerBoundInput.of_oneColumn_probability_pipeline`, so the favourable
column event may depend on the spike strength `a` and on the logarithmic slack. -/
theorem eventual_log_over_spikeSpeed_lower_of_oneColumn_probability_pipeline
    {targetProb : ℕ → ℝ}
    {betaProb capProb backgroundProb columnProb : ℝ → ℝ → ℕ → ℝ}
    {N s Ncap : ℕ → ℕ} {q δ : ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {lam ε : ℝ}
    (hlam : 0 < lam)
    (hspeed : ∀ᶠ d in atTop, 0 < spikeSpeed k d)
    (hColumnIncluded :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, columnProb a slack d ≤ targetProb d)
    (hProduct :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            columnProb a slack d =
              betaProb a slack d * capProb a slack d * backgroundProb a slack d)
    (hBeta :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            BetaColumnIntervalLowerBound
              (betaProb a slack d) (N d) (s d) (q a slack d) (δ a slack d))
    (hBetaKernel :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            -(lam * a + slack / 3) * spikeSpeed k d ≤
              Real.log
                (betaColumnIntervalKernel
                  (N d) (s d) (q a slack d) (δ a slack d)))
    (hNcap : ∀ᶠ d in atTop, 1 ≤ Ncap d)
    (hCap :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ProjectiveCapProbabilityLowerBound
              (capProb a slack d) (Ncap d) (1 / (Ncap d : ℝ)))
    (hCapCost :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          capNLogNCost 2 (Ncap d : ℝ) ≤ (slack / 3) * spikeSpeed k d)
    (hBackgroundHalf :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, (1 / 2 : ℝ) ≤ backgroundProb a slack d)
    (hBackgroundAbsorb :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          -(slack / 3) * spikeSpeed k d ≤ Real.log (1 / 2 : ℝ)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k lam ε - η ≤
          Real.log (targetProb d) / spikeSpeed k d := by
  intro η hη
  have I : SpikeLowerBoundInput targetProb k lam ε :=
    SpikeLowerBoundInput.of_oneColumn_probability_pipeline
      (targetProb := targetProb)
      (betaProb := betaProb) (capProb := capProb)
      (backgroundProb := backgroundProb) (columnProb := columnProb)
      (N := N) (s := s) (Ncap := Ncap) (q := q) (δ := δ)
      (k := k) (lam := lam) (ε := ε)
      hlam hspeed hColumnIncluded hProduct hBeta hBetaKernel
      hNcap hCap hCapCost hBackgroundHalf hBackgroundAbsorb
  simpa [spikeRate] using
    (AbstractSpikeLowerBoundInput.eventual_log_over_speed_lower
      (p := targetProb) (speed := spikeSpeed k) (root := spikeRoot k ε)
      (lam := lam) I η hη)

/-- Terminal one-column lower-bound theorem with scalar asymptotics closed.

This is the no-extra-input packaging endpoint for the lower-bound side:
it constructs the canonical `SpikeLowerBoundInput` through
`SpikeLowerBoundInput.of_oneColumn_probability_pipeline_scalar_limits`, whose
only lower-bound constructor call is the family-level
`SpikeLowerBoundInput.of_oneColumn_probability_pipeline`, and immediately
returns the normalized logarithmic lower bound. -/
theorem eventual_log_over_spikeSpeed_lower_of_oneColumn_probability_pipeline_scalar_limits
    {targetProb : ℕ → ℝ}
    {betaProb capProb backgroundProb columnProb : ℝ → ℝ → ℕ → ℝ}
    {N s Ncap : ℕ → ℕ} {δ : ℝ → ℝ → ℕ → ℝ}
    {k : ℕ} {lam ε : ℝ}
    (hk : 0 < k) (hlam : 0 < lam) (hε : 0 < ε)
    (hColumnIncluded :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, columnProb a slack d ≤ targetProb d)
    (hProduct :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            columnProb a slack d =
              betaProb a slack d * capProb a slack d * backgroundProb a slack d)
    (hBeta :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            BetaColumnIntervalLowerBound
              (betaProb a slack d) (N d) (s d)
              (betaColumnSpikeScale (N d : ℝ) (spikeSpeed k d) a)
              (δ a slack d))
    (hNpos :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, 0 < (N d : ℝ))
    (hDeltaPos :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, 0 < δ a slack d)
    (hUpper :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            betaColumnIntervalUpper
              (betaColumnSpikeScale (N d : ℝ) (spikeSpeed k d) a)
              (δ a slack d) < 1)
    (hDeltaLimit :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          Tendsto
            (fun d => (-Real.log (δ a slack d)) / spikeSpeed k d)
            atTop (nhds 0))
    (hEntropyLimit :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          Tendsto
            (fun d =>
              ((N d : ℝ) *
                (2 * Real.log (N d : ℝ) -
                  Real.log (a * spikeSpeed k d))) / spikeSpeed k d)
            atTop (nhds 0))
    (hOneMinusLimit :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          Tendsto
            (fun d =>
              ((((betaColumnOtherShape (N d) (s d) - 1 : ℕ) : ℝ) *
                  betaColumnIntervalUpper
                    (betaColumnSpikeScale (N d : ℝ) (spikeSpeed k d) a)
                    (δ a slack d) /
                    (1 - betaColumnIntervalUpper
                      (betaColumnSpikeScale (N d : ℝ) (spikeSpeed k d) a)
                      (δ a slack d))) /
                spikeSpeed k d))
            atTop (nhds (lam * a)))
    (hNcap : ∀ᶠ d in atTop, 1 ≤ Ncap d)
    (hCap :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ProjectiveCapProbabilityLowerBound
              (capProb a slack d) (Ncap d) (1 / (Ncap d : ℝ)))
    (hCapCostLimit :
      Tendsto
        (fun d => capNLogNCost 2 (Ncap d : ℝ) / spikeSpeed k d)
        atTop (nhds 0))
    (hBackgroundHalf :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop, (1 / 2 : ℝ) ≤ backgroundProb a slack d) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k lam ε - η ≤
          Real.log (targetProb d) / spikeSpeed k d := by
  intro η hη
  have I : SpikeLowerBoundInput targetProb k lam ε :=
    SpikeLowerBoundInput.of_oneColumn_probability_pipeline_scalar_limits
      (targetProb := targetProb)
      (betaProb := betaProb) (capProb := capProb)
      (backgroundProb := backgroundProb) (columnProb := columnProb)
      (N := N) (s := s) (Ncap := Ncap) (δ := δ)
      (k := k) (lam := lam) (ε := ε)
      hk hlam hε hColumnIncluded hProduct hBeta hNpos hDeltaPos hUpper
      hDeltaLimit hEntropyLimit hOneMinusLimit hNcap hCap hCapCostLimit
      hBackgroundHalf
  simpa [SpikeLowerBoundInput, spikeRate] using
    (AbstractSpikeLowerBoundInput.eventual_log_over_speed_lower
      (p := targetProb) (speed := spikeSpeed k) (root := spikeRoot k ε)
      (lam := lam) I η hη)

/-- Generic eventual lower exponent for an already-built spike lower-bound
input:

for every `η > 0`, eventually

`-lam ε^(1/k) - η ≤ log p_d / d^(2+2/k)`.

This is the no-overclaim formal replacement for the informal assertion that the
spike construction gives a liminf lower bound at speed `d^(2+2/k)`.

For the one-column liminf, the input `I` should be obtained from the
family-level constructor `SpikeLowerBoundInput.of_oneColumn_probability_pipeline`,
or one can call
`eventual_log_over_spikeSpeed_lower_of_oneColumn_probability_pipeline`
directly. -/
theorem SpikeLowerBoundInput.eventual_log_over_spikeSpeed_lower
    {p : ℕ → ℝ} {k : ℕ} {lam ε : ℝ}
    (I : SpikeLowerBoundInput p k lam ε) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k lam ε - η ≤
          Real.log (p d) / spikeSpeed k d := by
  intro η hη
  simpa [SpikeLowerBoundInput, spikeRate] using
    (AbstractSpikeLowerBoundInput.eventual_log_over_speed_lower
      (p := p) (speed := spikeSpeed k) (root := spikeRoot k ε) (lam := lam) I η hη)

/-- Conditional eventual upper exponent at the spike speed:

for every `η > 0`, eventually

`log p_d / d^(2+2/k) ≤ -lam ε^(1/k) + η`.

The theorem is conditional on `SpikeUpperBoundInput`, i.e. on a genuine
large-deviation upper bound for the target event. -/
theorem SpikeUpperBoundInput.eventual_log_over_spikeSpeed_upper
    {p : ℕ → ℝ} {k : ℕ} {lam ε : ℝ}
    (I : SpikeUpperBoundInput p k lam ε) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (p d) / spikeSpeed k d ≤
          -spikeRate k lam ε + η := by
  intro η hη
  simpa [SpikeUpperBoundInput, spikeRate] using
    (AbstractSpikeUpperBoundInput.eventual_log_over_speed_upper
      (p := p) (speed := spikeSpeed k) (root := spikeRoot k ε) (lam := lam) I η hη)

/-! ## Conditional refutation of the slower claimed speed -/

/-- The slower speed `d^(2+1/k)` that one sometimes obtains from a
non-optimized Lipschitz estimate. -/
noncomputable def claimedSpeed (k d : ℕ) : ℝ :=
  (d : ℝ) ^ (2 + (1 : ℝ) / (k : ℝ))

/-- Eventual formulation of `u d → +∞`. -/
def TendsToPosInfinity (u : ℕ → ℝ) : Prop :=
  ∀ A : ℝ, ∀ᶠ d in atTop, A ≤ u d

/-- Eventual formulation of `u d → -∞`. -/
def TendsToNegInfinity (u : ℕ → ℝ) : Prop :=
  ∀ A : ℝ, ∀ᶠ d in atTop, u d ≤ A

/-- Conditional exact-spike-speed exponent package: the lower and upper bounds
at the candidate speed `d^(2+2/k)`.

This packages a *logical* exact-rate hypothesis.  It is not a proof of the hard
random-matrix upper bound; the matching limsup is precisely the field `upper`,
and remains open/conditional unless supplied externally. -/
structure ConditionalExactSpikeRateInput (p : ℕ → ℝ) (k : ℕ) (lam ε : ℝ) : Prop where
  lower : SpikeLowerBoundInput p k lam ε
  upper : SpikeUpperBoundInput p k lam ε

/-- Conditional certification of the speed-refutation step.

If the target probability has the spike-speed upper exponent and the ratio
between the correct speed and a claimed slower speed goes to `+∞`, then the
logarithmic probability divided by the claimed speed goes to `-∞`.

For the intended application, the claimed speed is `d^(2+1/k)`, the correct
speed is `d^(2+2/k)`, and the ratio is `d^(1/k)`. -/
theorem SpikeUpperBoundInput.claimedSpeed_goes_to_negInfinity
    {p ratio : ℕ → ℝ} {k : ℕ} {lam ε : ℝ}
    (I : SpikeUpperBoundInput p k lam ε)
    (hrate : 0 < spikeRate k lam ε)
    (hratio : TendsToPosInfinity ratio)
    (hfactor :
      ∀ᶠ d in atTop,
        Real.log (p d) / claimedSpeed k d =
          (Real.log (p d) / spikeSpeed k d) * ratio d) :
    TendsToNegInfinity
      (fun d => Real.log (p d) / claimedSpeed k d) := by
  intro B
  have hhalf : 0 < spikeRate k lam ε / 2 := by positivity
  have hupper :=
    I.eventual_log_over_spikeSpeed_upper (spikeRate k lam ε / 2) hhalf
  by_cases hB : B < 0
  · let threshold : ℝ := (-2 * B) / spikeRate k lam ε
    have hthreshold_pos : 0 < threshold := by
      dsimp [threshold]
      apply div_pos
      · nlinarith [hB]
      · exact hrate
    have hratio_tail := hratio threshold
    filter_upwards [hupper, hratio_tail, hfactor] with d hupper_d hratio_d hfactor_d
    rw [hfactor_d]
    have hupper_d' :
        Real.log (p d) / spikeSpeed k d ≤ -(spikeRate k lam ε) / 2 := by
      linarith
    have hratio_nonneg : 0 ≤ ratio d :=
      le_trans (le_of_lt hthreshold_pos) hratio_d
    have hmul_upper :
        (Real.log (p d) / spikeSpeed k d) * ratio d ≤
          (-(spikeRate k lam ε) / 2) * ratio d :=
      mul_le_mul_of_nonneg_right hupper_d' hratio_nonneg
    have hmul_threshold :
        (-(spikeRate k lam ε) / 2) * ratio d ≤ B := by
      have hnonpos : -(spikeRate k lam ε) / 2 ≤ 0 := by linarith
      have hmul :
          (-(spikeRate k lam ε) / 2) * ratio d ≤
            (-(spikeRate k lam ε) / 2) * threshold :=
        mul_le_mul_of_nonpos_left hratio_d hnonpos
      have hthreshold :
          (-(spikeRate k lam ε) / 2) * threshold = B := by
        dsimp [threshold]
        field_simp [ne_of_gt hrate]
      simpa [hthreshold] using hmul
    exact le_trans hmul_upper hmul_threshold
  · have hB_nonneg : 0 ≤ B := le_of_not_gt hB
    have hratio_tail := hratio 0
    filter_upwards [hupper, hratio_tail, hfactor] with d hupper_d hratio_nonneg hfactor_d
    rw [hfactor_d]
    have hupper_d' :
        Real.log (p d) / spikeSpeed k d ≤ -(spikeRate k lam ε) / 2 := by
      linarith
    have hmul_upper :
        (Real.log (p d) / spikeSpeed k d) * ratio d ≤
          (-(spikeRate k lam ε) / 2) * ratio d :=
      mul_le_mul_of_nonneg_right hupper_d' hratio_nonneg
    have hmul_nonpos : (-(spikeRate k lam ε) / 2) * ratio d ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hratio_nonneg
    exact le_trans hmul_upper (le_trans hmul_nonpos hB_nonneg)

/-- Same conclusion from the conditional exact-rate package.

The proof only uses the upper half of the package.  Thus this theorem should be
read only as: *if* an upper LDP at the spike speed is supplied, then the slower
claimed speed gives `-∞`. -/
theorem ConditionalExactSpikeRateInput.claimedSpeed_goes_to_negInfinity
    {p ratio : ℕ → ℝ} {k : ℕ} {lam ε : ℝ}
    (I : ConditionalExactSpikeRateInput p k lam ε)
    (hrate : 0 < spikeRate k lam ε)
    (hratio : TendsToPosInfinity ratio)
    (hfactor :
      ∀ᶠ d in atTop,
        Real.log (p d) / claimedSpeed k d =
          (Real.log (p d) / spikeSpeed k d) * ratio d) :
    TendsToNegInfinity
      (fun d => Real.log (p d) / claimedSpeed k d) :=
  I.upper.claimedSpeed_goes_to_negInfinity hrate hratio hfactor

/-- A sequence tending to `-∞` is eventually below every finite claimed bound,
strictly. -/
theorem TendsToNegInfinity.eventually_lt
    {u : ℕ → ℝ} (hu : TendsToNegInfinity u) (B : ℝ) :
    ∀ᶠ d in atTop, u d < B := by
  have htail := hu (B - 1)
  filter_upwards [htail] with d hd
  linarith

end AppendixB
