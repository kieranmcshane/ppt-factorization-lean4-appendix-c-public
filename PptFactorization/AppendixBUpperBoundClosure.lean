import PptFactorization.AppendixBSpikeLowerBound
import PptFactorization.AppendixBSphericalConcentration
import PptFactorization.AppendixBConcreteModel
import PptFactorization.AppendixBLowerBoundClosure
import PptFactorization.SphericalPolarizationPushforwardTransport
import PptFactorization.FinRealSphereIsoperimetryProof
import PptFactorization.UpperMixedOneQuadraticBranch
import PptFactorization.UpperMixedOneLinearBranch
import PptFactorization.UpperMixedMultiDefectBranch

/-!
# Appendix B upper-bound closure

Stable thin wrappers for the conditional upper-bound pipeline in
`AppendixBSpikeLowerBound`.

The file also records the precise geometric closure for the actual spherical
law used by the model: once the remaining deep real-sphere input
`FullSphericalIsoperimetry` is supplied, the model law
`sphericalModelMeasure` satisfies `SharpSphericalIsoperimetry` with ambient
real dimension `2 * bipartiteDimension p q * sampleDimension σ`.  The
family-level helper below is the form that matches the upper-bound pipeline's
parameters `μ`, `N`, `s`, and `realDim`.

Status:

* These wrappers have a clean dependency inspection: the reported dependencies
  are only the usual foundations (`propext`, `Classical.choice`, `Quot.sound`).
* They do not prove the hard random-matrix upper large-deviation principle.
  They only re-export already formalized conditional implications.
* The clean bundled endpoint is
  `upper_eventual_from_localExpansion_scalarLimits`.
* The external-input endpoint is `upper_eventual_from_input`.
* The concrete scalar section below discharges the routine scalar pieces
  `hRatio`, `hRemainderLimit`, `hTau`, `hGap`, `hSpeedPow`, `hN_nonneg`,
  `hN_ne`, `hk`, and `hlam` for the canonical balanced regime and canonical
  slack budgets.

Conditionality:

This closure file does **not** prove the hard random-matrix upper LDP.  It only
packages already-formalized implications once the analytic/geometric upper-bound
inputs are supplied.

The hard assumptions still visible in theorem signatures include:

* `SharpSphericalIsoperimetry` / `hIso`;
* `hTarget`;
* `hK_meas`;
* `hK_half`;
* `hMixed`;
* `hRatio`, the aspect-ratio input;
* `hRemainderLimit`;
* `hTau`;
* `hGap`;
* positivity, speed, and aspect assumptions such as `hk`, `hk3`, `hlam`, `hε`,
  `hp`, `hspeed_pos`, `hN`, `hN_nonneg`, `hN_ne`, `hSpeedPow`, `haspect`, and
  the associated dimensional bookkeeping inputs.

These are parameters, not hidden assumptions.  Several scalar ones now have
concrete helper theorems in this file; the target positivity `hp`, the
deviation positivity `hε`, and the hard geometric/probabilistic inputs remain
external.
-/

namespace AppendixB

open Matrix MeasureTheory
open PptFactorization.RandomMatrixModel
open PptFactorization.HighProbabilityBounds
open Filter
open scoped BigOperators Matrix.Norms.Frobenius Pointwise ENNReal Topology symmDiff

/-- Sharp spherical isoperimetry for the actual Gaussian-direction spherical
law used in the model, with the ambient real dimension normalized as
`2 * N * s`.

Here `N` is the bipartite dimension `bipartiteDimension p q`, and `s` is the
sample dimension `sampleDimension σ`.  This theorem is not a proof of the deep
real-sphere isoperimetric theorem itself; that remaining geometric input is
the visible assumption `hIso : PptFactorization.AppendixB.FullSphericalIsoperimetry`.
The proof only transports that input to the surface model, uses the Gaussian
polar law to identify `surfaceModelMeasure` with `sphericalModelMeasure`, and
rewrites `Module.finrank ℝ (SampleMatrix p q σ)` as `2 * N * s`. -/
theorem sharpSphericalIsoperimetry_sphericalModelMeasure_of_fullSphericalIsoperimetry
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (hIso : PptFactorization.AppendixB.FullSphericalIsoperimetry) :
    SharpSphericalIsoperimetry
      (p := p) (q := q) (σ := σ)
      (PptFactorization.AppendixB.sphericalModelMeasure
        (p := p) (q := q) (σ := σ))
      (2 * bipartiteDimension p q * sampleDimension σ) := by
  have hsurface :
      SharpSphericalIsoperimetry
        (p := p) (q := q) (σ := σ)
        (PptFactorization.AppendixB.surfaceModelMeasure
          (p := p) (q := q) (σ := σ))
        (Module.finrank ℝ (SampleMatrix p q σ)) :=
    PptFactorization.AppendixB.sharpSphericalIsoperimetry_of_fullSphericalIsoperimetry
      (p := p) (q := q) (σ := σ) hIso
  have hdim :
      (Module.finrank ℝ (SampleMatrix p q σ) : ℝ) =
        2 * bipartiteDimension p q * sampleDimension σ := by
    have hlevy :=
      PptFactorization.AppendixB.surfaceLevyDimension_eq_two_mul_bipartiteDimension_mul_sampleDimension_sub_one
          (p := p) (q := q) (σ := σ)
    unfold PptFactorization.AppendixB.surfaceLevyDimension at hlevy
    linarith
  simpa [PptFactorization.AppendixB.polarLaw (p := p) (q := q) (σ := σ), hdim]
    using hsurface

/-- Pointwise instantiation of the upper-bound `SharpSphericalIsoperimetry`
input for the concrete spherical matrix law.

This is the exact finite-dimensional shape used by the upper-bound pipeline:
if `μ` is the model law `sphericalModelMeasure`, `N` is the bipartite
dimension, `s` is the sample dimension, and `realDim = 2 * N * s`, then the
sharp isoperimetric input is available for `(μ, realDim)`.

The theorem still exposes the deep real-sphere geometric input
`hIso : PptFactorization.AppendixB.FullSphericalIsoperimetry`; it does not
prove that theorem from scratch. -/
theorem sharpSphericalIsoperimetry_sphericalModelMeasure_of_dimension_eq
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    {μ : Measure (SampleMatrix p q σ)} {realDim N s : ℝ}
    (hIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (hμ :
      μ =
        PptFactorization.AppendixB.sphericalModelMeasure
          (p := p) (q := q) (σ := σ))
    (hN : N = bipartiteDimension p q)
    (hs : s = sampleDimension σ)
    (hRealDim : realDim = 2 * N * s) :
    SharpSphericalIsoperimetry
      (p := p) (q := q) (σ := σ) μ realDim := by
  have hstatic :
      SharpSphericalIsoperimetry
        (p := p) (q := q) (σ := σ)
        (PptFactorization.AppendixB.sphericalModelMeasure
          (p := p) (q := q) (σ := σ))
        (2 * bipartiteDimension p q * sampleDimension σ) :=
    sharpSphericalIsoperimetry_sphericalModelMeasure_of_fullSphericalIsoperimetry
      (p := p) (q := q) (σ := σ) hIso
  have hdim : realDim = 2 * bipartiteDimension p q * sampleDimension σ := by
    calc
      realDim = 2 * N * s := hRealDim
      _ = 2 * bipartiteDimension p q * sampleDimension σ := by
        rw [hN, hs]
  simpa [hμ, hdim] using hstatic

/-- Family-level form of
`sharpSphericalIsoperimetry_sphericalModelMeasure_of_fullSphericalIsoperimetry`
matching the conditional upper-bound pipeline.

It closes the pipeline hypothesis
`SharpSphericalIsoperimetry (μ d) (realDim d)` when, eventually,
`μ d` is the concrete `sphericalModelMeasure`, `N d` is the bipartite
dimension, `s d` is the sample dimension, and
`realDim d = 2 * N d * s d`.  The deep geometric input remains explicit as
`hIso : PptFactorization.AppendixB.FullSphericalIsoperimetry`. -/
theorem eventually_sharpSphericalIsoperimetry_sphericalModelMeasure_of_fullSphericalIsoperimetry
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    {μ : ℕ → Measure (SampleMatrix p q σ)}
    {realDim N s : ℕ → ℝ}
    (hIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (hμ :
      ∀ᶠ d in atTop,
        μ d =
          PptFactorization.AppendixB.sphericalModelMeasure
            (p := p) (q := q) (σ := σ))
    (hN : ∀ᶠ d in atTop, N d = bipartiteDimension p q)
    (hs : ∀ᶠ d in atTop, s d = sampleDimension σ)
    (hRealDim : ∀ᶠ d in atTop, realDim d = 2 * N d * s d) :
    ∀ᶠ d in atTop,
      SharpSphericalIsoperimetry
        (p := p) (q := q) (σ := σ) (μ d) (realDim d) := by
  filter_upwards [hμ, hN, hs, hRealDim] with d hμd hNd hsd hdim
  exact
    sharpSphericalIsoperimetry_sphericalModelMeasure_of_dimension_eq
      (p := p) (q := q) (σ := σ)
      (μ := μ d) (realDim := realDim d) (N := N d) (s := s d)
      hIso hμd hNd hsd hdim

/-- Direct `hIso` constructor for
`upper_eventual_from_localExpansion_scalarLimits`.

Use this theorem to instantiate the upper-bound hypothesis

`∀ᶠ d, SharpSphericalIsoperimetry (μ d) (realDim d)`

for the actual spherical matrix law, with the exact ambient dimension
`realDim d = 2 * N d * s d`. -/
theorem upper_hIso_sphericalModelMeasure
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    {μ : ℕ → Measure (SampleMatrix p q σ)}
    {realDim N s : ℕ → ℝ}
    (hIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (hμ :
      ∀ᶠ d in atTop,
        μ d =
          PptFactorization.AppendixB.sphericalModelMeasure
            (p := p) (q := q) (σ := σ))
    (hN : ∀ᶠ d in atTop, N d = bipartiteDimension p q)
    (hs : ∀ᶠ d in atTop, s d = sampleDimension σ)
    (hRealDim : ∀ᶠ d in atTop, realDim d = 2 * N d * s d) :
    ∀ᶠ d in atTop,
      SharpSphericalIsoperimetry
        (p := p) (q := q) (σ := σ) (μ d) (realDim d) :=
  eventually_sharpSphericalIsoperimetry_sphericalModelMeasure_of_fullSphericalIsoperimetry
    (p := p) (q := q) (σ := σ)
    hIso hμ hN hs hRealDim

/-! ## Concrete scalar closures for the upper-bound endpoint -/

/-- The `hk` positivity input follows from the paper-facing moment assumption
`hk3 : 3 ≤ k`.

This is a scalar bookkeeping lemma only; the substantive moment-order
assumption remains `hk3`. -/
theorem upper_hk_of_hk3 {k : ℕ} (hk3 : 3 ≤ k) : 0 < k :=
  lt_of_lt_of_le (by norm_num : 0 < 3) hk3

/-- The limiting aspect-ratio positivity supplied by the concrete balanced
regime. -/
theorem upper_hlam_concreteBalancedRegime
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime) :
    0 < R.lam :=
  R.lam_pos

/-- Concrete `hRatio` for the Appendix-B balanced regime.

For the actual dimensions `N d = d²` and `s d = sample d`, this is exactly the
assumption `s d / N d → lam` recorded in `ConcreteModel.BalancedRegime`. -/
theorem upper_hRatio_concreteBalancedRegime
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime) :
    Tendsto
      (fun d : ℕ =>
        sampleDimension
            (PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d)) /
          bipartiteDimension
            (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (PptFactorization.AppendixB.ConcreteModel.RightIndex d))
      atTop (𝓝 R.lam) :=
  R.ratio_tendsto_dimension_form

/-- The same concrete `hRatio`, written using the canonical abbreviations
`ConcreteModel.S` and `ConcreteModel.D`. -/
theorem upper_hRatio_concreteBalancedRegime_D_S
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime) :
    Tendsto
      (fun d : ℕ =>
        PptFactorization.AppendixB.ConcreteModel.S (R.sample d) /
          PptFactorization.AppendixB.ConcreteModel.D d)
      atTop (𝓝 R.lam) := by
  simpa [PptFactorization.AppendixB.ConcreteModel.D,
    PptFactorization.AppendixB.ConcreteModel.S]
    using upper_hRatio_concreteBalancedRegime R

/-- Concrete nonnegativity for `N d = d²`. -/
theorem upper_hN_nonneg_concreteDimension :
    ∀ᶠ d in atTop,
      0 ≤ PptFactorization.AppendixB.ConcreteModel.D d := by
  filter_upwards with d
  simp [PptFactorization.AppendixB.ConcreteModel.D_eq]

/-- Concrete nonzero input for `N d = d²`, eventually away from `d = 0`. -/
theorem upper_hN_ne_concreteDimension :
    ∀ᶠ d in atTop,
      PptFactorization.AppendixB.ConcreteModel.D d ≠ 0 := by
  filter_upwards [eventually_gt_atTop 0] with d hd
  exact ne_of_gt (PptFactorization.AppendixB.ConcreteModel.D_pos (d := d) hd)

/-- Concrete nonnegativity for the raw bipartite dimension
`bipartiteDimension (Fin d) (Fin d)`. -/
theorem upper_hN_nonneg_concreteBipartiteDimension :
    ∀ᶠ d in atTop,
      0 ≤
        bipartiteDimension
          (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (PptFactorization.AppendixB.ConcreteModel.RightIndex d) := by
  change ∀ᶠ d in atTop, 0 ≤ PptFactorization.AppendixB.ConcreteModel.D d
  exact upper_hN_nonneg_concreteDimension

/-- Concrete nonzero input for the raw bipartite dimension
`bipartiteDimension (Fin d) (Fin d)`. -/
theorem upper_hN_ne_concreteBipartiteDimension :
    ∀ᶠ d in atTop,
      bipartiteDimension
          (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (PptFactorization.AppendixB.ConcreteModel.RightIndex d) ≠ 0 := by
  simpa [PptFactorization.AppendixB.ConcreteModel.D] using
    upper_hN_ne_concreteDimension

/-- Pointwise spike-speed identity for the concrete dimension `N = d²`.

This is the formal scalar identity behind
`hSpeedPow : spikeSpeed k d ^ k = N d ^ (k + 1)` when
`N d = (d : ℝ)^2`. -/
theorem upper_spikeSpeed_pow_eq_dimensionSquared
    {k d : ℕ} (hk : 0 < k) (hd : 0 < d) :
    spikeSpeed k d ^ k = ((d : ℝ) ^ 2) ^ (k + 1) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hd_nonneg : 0 ≤ (d : ℝ) := le_of_lt hdR
  have hkR_ne : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have hexp :
      (2 + (2 : ℝ) / (k : ℝ)) * (k : ℝ) =
        2 * ((k + 1 : ℕ) : ℝ) := by
    field_simp [hkR_ne]
    norm_num
  have hleft :
      spikeSpeed k d ^ k =
        (d : ℝ) ^ ((2 + (2 : ℝ) / (k : ℝ)) * (k : ℝ)) := by
    unfold spikeSpeed
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hd_nonneg]
  have hright :
      ((d : ℝ) ^ 2) ^ (k + 1) =
        (d : ℝ) ^ (2 * ((k + 1 : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_natCast (d : ℝ) 2]
    rw [← Real.rpow_mul hd_nonneg]
    norm_num
  rw [hleft, hright, hexp]

/-- Concrete eventual `hSpeedPow` for `N d = ConcreteModel.D d = d²`. -/
theorem upper_hSpeedPow_concreteDimension {k : ℕ} (hk : 0 < k) :
    ∀ᶠ d in atTop,
      spikeSpeed k d ^ k =
        PptFactorization.AppendixB.ConcreteModel.D d ^ (k + 1) := by
  filter_upwards [eventually_gt_atTop 0] with d hd
  simpa [PptFactorization.AppendixB.ConcreteModel.D_eq] using
    upper_spikeSpeed_pow_eq_dimensionSquared (k := k) (d := d) hk hd

/-- Concrete eventual `hSpeedPow` for the raw bipartite dimension
`N d = bipartiteDimension (Fin d) (Fin d)`. -/
theorem upper_hSpeedPow_concreteBipartiteDimension {k : ℕ} (hk : 0 < k) :
    ∀ᶠ d in atTop,
      spikeSpeed k d ^ k =
        (bipartiteDimension
            (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (PptFactorization.AppendixB.ConcreteModel.RightIndex d)) ^
          (k + 1) := by
  simpa [PptFactorization.AppendixB.ConcreteModel.D] using
    upper_hSpeedPow_concreteDimension (k := k) hk

/-- Any fixed numerator divided by `2 * (d²)^2` tends to zero. -/
theorem upper_const_over_two_concreteDimension_sq_tendsto_zero {C : ℝ} :
    Tendsto
      (fun d : ℕ =>
        C / (2 * (PptFactorization.AppendixB.ConcreteModel.D d) ^ 2))
      atTop (𝓝 0) := by
  have hD :
      Tendsto (fun d : ℕ => PptFactorization.AppendixB.ConcreteModel.D d)
        atTop atTop := by
    have h :
        Tendsto (fun d : ℕ => (d : ℝ) ^ (2 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2)).comp
        tendsto_natCast_atTop_atTop
    simpa [PptFactorization.AppendixB.ConcreteModel.D_eq, Real.rpow_natCast]
      using h
  have hD2 :
      Tendsto
        (fun d : ℕ => (PptFactorization.AppendixB.ConcreteModel.D d) ^ 2)
        atTop atTop := by
    simpa [pow_two] using
      (Filter.Tendsto.atTop_mul_atTop₀ hD hD)
  have hden :
      Tendsto
        (fun d : ℕ =>
          2 * (PptFactorization.AppendixB.ConcreteModel.D d) ^ 2)
        atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) hD2
  exact Filter.Tendsto.div_atTop tendsto_const_nhds hden

/-- Concrete `hRemainderLimit` for
`aSlack slack = upperSlackRadius (spikeRoot k eps) lam slack` and
`N d = d²`. -/
theorem upper_hRemainderLimit_concreteDimension
    {k : ℕ} {eps lam : ℝ} :
    ∀ slack : ℝ, 0 < slack →
      Tendsto
        (fun d : ℕ =>
          upperSlackRadius (spikeRoot k eps) lam slack /
            (2 * (PptFactorization.AppendixB.ConcreteModel.D d) ^ 2))
        atTop (𝓝 0) := by
  intro slack _hslack
  exact upper_const_over_two_concreteDimension_sq_tendsto_zero

/-- Canonical vanishing local-expansion tolerance for the upper-bound scalar
closure. -/
noncomputable def upperCanonicalTau (slack : ℝ) (d : ℕ) : ℝ :=
  slack / (d : ℝ)

/-- Concrete `hTau` for `upperCanonicalTau`. -/
theorem upper_hTau_canonical :
    ∀ slack : ℝ, 0 < slack →
      Tendsto (upperCanonicalTau slack) atTop (𝓝 0) := by
  intro slack _hslack
  exact Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_natCast_atTop_atTop

/-- Canonical positive gap budget for the local-expansion scalar closure.

For each slack, this chooses half of the remaining distance between `eps` and
the `k`-th power of the canonical upper radius. -/
noncomputable def upperCanonicalEtaSlack
    (k : ℕ) (eps lam : ℝ) (slack : ℝ) : ℝ :=
  (eps - upperSlackRadius (spikeRoot k eps) lam slack ^ k) / 2

/-- Positivity of the canonical `etaSlack` budget. -/
theorem upper_hEta_canonical
    {k : ℕ} {eps lam : ℝ}
    (hk : 0 < k) (hlam : 0 < lam) (hε : 0 < eps) :
    ∀ slack : ℝ, 0 < slack →
      0 < upperCanonicalEtaSlack k eps lam slack := by
  intro slack hslack
  let a := upperSlackRadius (spikeRoot k eps) lam slack
  have hchoice := upperSlackRadius_spike_choice hk hlam hε slack hslack
  have ha_nonneg : 0 ≤ a := hchoice.1
  have ha_lt_root : a < spikeRoot k eps := hchoice.2.1
  have hrootpow : spikeRoot k eps ^ k = eps := by
    unfold spikeRoot
    simpa [one_div] using
      (Real.rpow_inv_natCast_pow (le_of_lt hε) (Nat.ne_of_gt hk))
  have ha_pow_lt : a ^ k < eps := by
    have hlt : a ^ k < spikeRoot k eps ^ k :=
      pow_lt_pow_left₀ ha_lt_root ha_nonneg (Nat.ne_of_gt hk)
    simpa [hrootpow] using hlt
  have hnum : 0 < eps - a ^ k := by linarith
  dsimp [upperCanonicalEtaSlack, a]
  linarith

/-- Concrete `hGap` for the canonical `etaSlack` budget. -/
theorem upper_hGap_canonical
    {k : ℕ} {eps lam : ℝ}
    (hk : 0 < k) (hlam : 0 < lam) (hε : 0 < eps) :
    ∀ slack : ℝ, 0 < slack →
      upperSlackRadius (spikeRoot k eps) lam slack ^ k +
        upperCanonicalEtaSlack k eps lam slack < eps := by
  intro slack hslack
  let a := upperSlackRadius (spikeRoot k eps) lam slack
  have hchoice := upperSlackRadius_spike_choice hk hlam hε slack hslack
  have ha_nonneg : 0 ≤ a := hchoice.1
  have ha_lt_root : a < spikeRoot k eps := hchoice.2.1
  have hrootpow : spikeRoot k eps ^ k = eps := by
    unfold spikeRoot
    simpa [one_div] using
      (Real.rpow_inv_natCast_pow (le_of_lt hε) (Nat.ne_of_gt hk))
  have ha_pow_lt : a ^ k < eps := by
    have hlt : a ^ k < spikeRoot k eps ^ k :=
      pow_lt_pow_left₀ ha_lt_root ha_nonneg (Nat.ne_of_gt hk)
    simpa [hrootpow] using hlt
  dsimp [upperCanonicalEtaSlack, a]
  linarith

/-! ## Concrete upper-target event bridge -/

/-- Exact absolute-deviation target probability for the upper-bound pipeline.

This is the concrete `targetProb` for the formal absolute deviation event
`backgroundMomentDeviationSet`, namely
`P(|F_N(X) - mean_d| >= eps)` under the supplied spherical/background law
`μ d`. -/
noncomputable def upperBackgroundDeviationTargetProb
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    (μ : ℕ → Measure (SampleMatrix p q σ))
    (N : ℕ → ℝ) (eps : ℝ) (mean : ℕ → ℝ) (k : ℕ) : ℕ → ℝ :=
  fun d =>
    (μ d).real
      (backgroundMomentDeviationSet
        (p := p) (q := q) (σ := σ)
        (N d) eps (mean d) k)

/-- Concrete `hTarget` for `upperBackgroundDeviationTargetProb`.

The upper-bound scalar-limits endpoint allows the centering `mean slack d` to
be slack-dependent.  This lemma discharges its `hTarget` assumption whenever
that centering is eventually the paper centering `mean d` for every fixed
slack. -/
theorem upperBackgroundDeviationTargetProb_hTarget
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {μ : ℕ → Measure (SampleMatrix p q σ)}
    {N : ℕ → ℝ} {eps : ℝ} {mean : ℕ → ℝ}
    {meanSlack : ℝ → ℕ → ℝ} {k : ℕ}
    (hMean :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop, meanSlack slack d = mean d) :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        upperBackgroundDeviationTargetProb
            (p := p) (q := q) (σ := σ) μ N eps mean k d =
          (μ d).real
            (backgroundMomentDeviationSet
              (p := p) (q := q) (σ := σ)
              (N d) eps (meanSlack slack d) k) := by
  intro slack hslack
  filter_upwards [hMean slack hslack] with d hmean
  change
    (μ d).real
        (backgroundMomentDeviationSet
          (p := p) (q := q) (σ := σ)
          (N d) eps (mean d) k) =
      (μ d).real
        (backgroundMomentDeviationSet
          (p := p) (q := q) (σ := σ)
          (N d) eps (meanSlack slack d) k)
  rw [hmean]

/-- If the paper-facing observable is exactly the formal background moment
functional, then its absolute-deviation event is the formal
`backgroundMomentDeviationSet`. -/
theorem paperMomentDeviationSet_eq_backgroundMomentDeviationSet
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {f : SampleMatrix p q σ → ℝ} {N eps mean : ℝ} {k : ℕ}
    (hf :
      ∀ X : SampleMatrix p q σ,
        f X =
          backgroundMomentValue (p := p) (q := q) (σ := σ) N k X) :
    {X : SampleMatrix p q σ | eps ≤ |f X - mean|} =
      backgroundMomentDeviationSet
        (p := p) (q := q) (σ := σ) N eps mean k := by
  ext X
  simp [backgroundMomentDeviationSet, hf X]

/-- Concrete `hTarget` from a paper-facing absolute-deviation probability.

Use this when the paper target is written as
`P(|f_d(X) - mean_d| >= eps)` and `f_d` has been identified with the formal
background moment functional.  The optional slack-dependent centering is again
handled by an eventual equality to the paper centering. -/
theorem paperMomentDeviationTargetProb_hTarget
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {targetProb : ℕ → ℝ}
    {μ : ℕ → Measure (SampleMatrix p q σ)}
    {N : ℕ → ℝ} {eps : ℝ}
    {f : ℕ → SampleMatrix p q σ → ℝ}
    {mean : ℕ → ℝ} {meanSlack : ℝ → ℕ → ℝ} {k : ℕ}
    (hTargetPaper :
      ∀ᶠ d in atTop,
        targetProb d =
          (μ d).real {X : SampleMatrix p q σ | eps ≤ |f d X - mean d|})
    (hf :
      ∀ᶠ d in atTop,
        ∀ X : SampleMatrix p q σ,
          f d X =
            backgroundMomentValue
              (p := p) (q := q) (σ := σ) (N d) k X)
    (hMean :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop, meanSlack slack d = mean d) :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        targetProb d =
          (μ d).real
            (backgroundMomentDeviationSet
              (p := p) (q := q) (σ := σ)
              (N d) eps (meanSlack slack d) k) := by
  intro slack hslack
  filter_upwards [hTargetPaper, hf, hMean slack hslack] with d htarget hf_d hmean
  rw [htarget]
  have hset :
      {X : SampleMatrix p q σ | eps ≤ |f d X - mean d|} =
        backgroundMomentDeviationSet
          (p := p) (q := q) (σ := σ) (N d) eps (mean d) k :=
    paperMomentDeviationSet_eq_backgroundMomentDeviationSet
      (p := p) (q := q) (σ := σ) (N := N d) (eps := eps)
      (mean := mean d) (k := k) (f := f d) hf_d
  rw [hset, ← hmean]

/-- The one-sided normalized moment upper-tail event is contained in the
absolute-deviation event used by the upper-bound pipeline.

Thus if the final paper target is the one-sided event
`F_N(X) - mean >= eps`, its probability is bounded above by the formal
`backgroundMomentDeviationSet` probability.  This is the correct direction for
an upper bound. -/
theorem columnMomentUpperTailSet_subset_backgroundMomentDeviationSet
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {N eps mean : ℝ} {k : ℕ} :
    columnMomentUpperTailSet
        (p := p) (q := q) (σ := σ) N eps mean k ⊆
      backgroundMomentDeviationSet
        (p := p) (q := q) (σ := σ) N eps mean k := by
  intro X hX
  exact
    (show eps ≤
        backgroundMomentValue (p := p) (q := q) (σ := σ) N k X - mean by
      simpa [columnMomentUpperTailSet, backgroundMomentValue] using hX).trans
      (le_abs_self _)

/-- Probability form of
`columnMomentUpperTailSet_subset_backgroundMomentDeviationSet`. -/
theorem measureReal_columnMomentUpperTailSet_le_backgroundMomentDeviationSet
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {μ : Measure (SampleMatrix p q σ)} [IsFiniteMeasure μ]
    {N eps mean : ℝ} {k : ℕ} :
    μ.real
        (columnMomentUpperTailSet
          (p := p) (q := q) (σ := σ) N eps mean k) ≤
      μ.real
        (backgroundMomentDeviationSet
          (p := p) (q := q) (σ := σ) N eps mean k) :=
  measureReal_mono
    (columnMomentUpperTailSet_subset_backgroundMomentDeviationSet
      (p := p) (q := q) (σ := σ)
      (N := N) (eps := eps) (mean := mean) (k := k))
    (h₂ := (measure_lt_top μ
      (backgroundMomentDeviationSet
        (p := p) (q := q) (σ := σ) N eps mean k)).ne)

/-- The strict background-moment bad event is contained in the corresponding
closed absolute-deviation event at the same threshold. -/
theorem backgroundMomentBadSet_subset_backgroundMomentDeviationSet
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {N τ mean : ℝ} {k : ℕ} :
    backgroundMomentBadSet
        (p := p) (q := q) (σ := σ) N τ mean k ⊆
      backgroundMomentDeviationSet
        (p := p) (q := q) (σ := σ) N τ mean k := by
  intro X hX
  simpa [backgroundMomentBadSet, backgroundMomentDeviationSet] using
    (le_of_lt (by simpa [backgroundMomentBadSet] using hX))

/-- Probability form of
`backgroundMomentBadSet_subset_backgroundMomentDeviationSet`. -/
theorem measureReal_backgroundMomentBadSet_le_backgroundMomentDeviationSet
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {μ : Measure (SampleMatrix p q σ)} [IsFiniteMeasure μ]
    {N τ mean : ℝ} {k : ℕ} :
    μ.real
        (backgroundMomentBadSet
          (p := p) (q := q) (σ := σ) N τ mean k) ≤
      μ.real
        (backgroundMomentDeviationSet
          (p := p) (q := q) (σ := σ) N τ mean k) :=
  measureReal_mono
    (backgroundMomentBadSet_subset_backgroundMomentDeviationSet
      (p := p) (q := q) (σ := σ)
      (N := N) (τ := τ) (mean := mean) (k := k))
    (h₂ := (measure_lt_top μ
      (backgroundMomentDeviationSet
        (p := p) (q := q) (σ := σ) N τ mean k)).ne)

/-- One-sided paper upper-tail probability.  The underlying set is named
`columnMomentUpperTailSet` in the spike file, but it is simply the event
`F_N(X) - mean_d >= eps`. -/
noncomputable def upperOneSidedMomentTargetProb
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    (μ : ℕ → Measure (SampleMatrix p q σ))
    (N : ℕ → ℝ) (eps : ℝ) (mean : ℕ → ℝ) (k : ℕ) : ℕ → ℝ :=
  fun d =>
    (μ d).real
      (columnMomentUpperTailSet
        (p := p) (q := q) (σ := σ)
        (N d) eps (mean d) k)

/-- The one-sided paper target is dominated by the formal absolute-deviation
target. -/
theorem upperOneSidedMomentTargetProb_le_upperBackgroundDeviationTargetProb
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {μ : ℕ → Measure (SampleMatrix p q σ)}
    {N : ℕ → ℝ} {eps : ℝ} {mean : ℕ → ℝ} {k : ℕ}
    (hFinite : ∀ᶠ d in atTop, IsFiniteMeasure (μ d)) :
    ∀ᶠ d in atTop,
      upperOneSidedMomentTargetProb
          (p := p) (q := q) (σ := σ) μ N eps mean k d ≤
        upperBackgroundDeviationTargetProb
          (p := p) (q := q) (σ := σ) μ N eps mean k d := by
  filter_upwards [hFinite] with d hfinite
  letI : IsFiniteMeasure (μ d) := hfinite
  exact
    measureReal_columnMomentUpperTailSet_le_backgroundMomentDeviationSet
      (p := p) (q := q) (σ := σ)
      (μ := μ d) (N := N d) (eps := eps) (mean := mean d) (k := k)

/-! ## Concrete background typicality inputs -/

/-- Routine `hK_meas` constructor for the upper-bound pipeline.

The background typical set is measurable for every choice of the scalar
parameters, so the slack-family/eventual form required by
`upper_eventual_from_localExpansion_scalarLimits` has no probabilistic content. -/
theorem upper_hK_meas_backgroundTypicalSet
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {N : ℕ → ℝ} {M τ mean : ℝ → ℕ → ℝ} {k : ℕ} :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        MeasurableSet
          (backgroundTypicalSet
            (p := p) (q := q) (σ := σ)
            (N d) (M slack d) (τ slack d) (mean slack d) k) := by
  intro slack hslack
  exact
    Eventually.of_forall fun d =>
      measurableSet_backgroundTypicalSet
        (p := p) (q := q) (σ := σ)
        (N d) (M slack d) (τ slack d) (mean slack d) k

/-- Half-mass constructor for the concrete spherical matrix law from a packaged
three-bad-set estimate.

The package `ConcreteSphericalBackgroundBadSetBounds` contains exactly the
substantive probabilistic inputs: moment concentration for
`backgroundMomentBadSet`, and the sample-operator/gamma-operator bad-event
estimates for the concrete spherical law.  Once their total bad mass is at most
`1/2`, the formal typical set has mass at least `1/2`. -/
theorem upper_hK_half_sphericalModelMeasure_of_concrete_bad_bounds
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {N : ℕ → ℝ}
    {M τ mean bMoment bSample bGamma : ℝ → ℕ → ℝ}
    {k : ℕ}
    (hBounds :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ConcreteSphericalBackgroundBadSetBounds
            (p := p) (q := q) (σ := σ)
            (N d) (M slack d) (τ slack d) (mean slack d)
            (bMoment slack d) (bSample slack d) (bGamma slack d) k)
    (hBad :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          bMoment slack d + bSample slack d + bGamma slack d ≤ 1 / 2) :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        1 / 2 ≤
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := p) (q := q) (σ := σ)).real
            (backgroundTypicalSet
              (p := p) (q := q) (σ := σ)
              (N d) (M slack d) (τ slack d) (mean slack d) k) := by
  intro slack hslack
  filter_upwards [hBounds slack hslack, hBad slack hslack] with d hB hBad_d
  exact
    hB.backgroundTypicalSet_measure_ge_half
      (p := p) (q := q) (σ := σ)
      (N := N d) (M := M slack d)
      (τ := τ slack d) (mean := mean slack d)
      (bMoment := bMoment slack d)
      (bSample := bSample slack d)
      (bGamma := bGamma slack d)
      (k := k)
      (measurableSet_backgroundTypicalSet
        (p := p) (q := q) (σ := σ)
        (N d) (M slack d) (τ slack d) (mean slack d) k)
      hBad_d

/-- Pipeline-shaped `hK_half` constructor for a law `μ d` eventually equal to
the concrete spherical matrix law.

This is the form to feed directly to
`upper_eventual_from_localExpansion_scalarLimits` when the upper-bound law is
the actual spherical law and the concrete three-bad-set estimates have been
proved. -/
theorem upper_hK_half_of_sphericalModelMeasure_concrete_bad_bounds
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {μ : ℕ → Measure (SampleMatrix p q σ)}
    {N : ℕ → ℝ}
    {M τ mean bMoment bSample bGamma : ℝ → ℕ → ℝ}
    {k : ℕ}
    (hμ :
      ∀ᶠ d in atTop,
        μ d =
          PptFactorization.AppendixB.sphericalModelMeasure
            (p := p) (q := q) (σ := σ))
    (hBounds :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ConcreteSphericalBackgroundBadSetBounds
            (p := p) (q := q) (σ := σ)
            (N d) (M slack d) (τ slack d) (mean slack d)
            (bMoment slack d) (bSample slack d) (bGamma slack d) k)
    (hBad :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          bMoment slack d + bSample slack d + bGamma slack d ≤ 1 / 2) :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        1 / 2 ≤ (μ d).real
          (backgroundTypicalSet
            (p := p) (q := q) (σ := σ)
            (N d) (M slack d) (τ slack d) (mean slack d) k) := by
  intro slack hslack
  have hHalf :=
    upper_hK_half_sphericalModelMeasure_of_concrete_bad_bounds
      (p := p) (q := q) (σ := σ)
      (N := N) (M := M) (τ := τ) (mean := mean)
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (k := k)
      hBounds hBad slack hslack
  filter_upwards [hμ, hHalf] with d hμd hhalf
  simpa [hμd] using hhalf

/-- Concrete spherical-law `hK_half` constructor directly from the three
probabilistic estimates used in the paper.

The assumptions are:

* `hMoment`: moment concentration for the bad moment set;
* `hSampleTail`: the normalized sample-operator good-event estimate;
* `hGammaTail`: the normalized gamma/operator good-event estimate;
* `hBad`: the scalar union-bound budget saying the three bad probabilities
  sum to at most `1/2`.

The scalar `ambientDim d` is the paper's Hilbert dimension parameter with
`N d = ambientDim d ^ 2`, matching the existing normalized Gaussian tail
interfaces. -/
theorem upper_hK_half_sphericalModelMeasure_of_moment_and_operator_tails
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {N ambientDim : ℕ → ℝ}
    {M τ mean bMoment bSample bGamma : ℝ → ℕ → ℝ}
    {k : ℕ}
    (hDim_pos : ∀ᶠ d in atTop, 0 < ambientDim d)
    (hN_dim : ∀ᶠ d in atTop, N d = ambientDim d ^ 2)
    (hMoment :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := p) (q := q) (σ := σ)).real
            (backgroundMomentBadSet
              (p := p) (q := q) (σ := σ)
              (N d) (τ slack d) (mean slack d) k) ≤
              bMoment slack d)
    (hSampleTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (gaussianMeasure p q σ).real
            ((normalizedSampleOpNormEvent
              (p := p) (q := q) (σ := σ)
              (M slack d) (ambientDim d))ᶜ) ≤
            bSample slack d)
    (hGammaTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (gaussianMeasure p q σ).real
            ((normalizedRhoGammaOpNormEvent
              (p := p) (q := q) (σ := σ)
              (M slack d) (ambientDim d))ᶜ) ≤
            bGamma slack d)
    (hBad :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          bMoment slack d + bSample slack d + bGamma slack d ≤ 1 / 2) :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        1 / 2 ≤
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := p) (q := q) (σ := σ)).real
            (backgroundTypicalSet
              (p := p) (q := q) (σ := σ)
              (N d) (M slack d) (τ slack d) (mean slack d) k) := by
  intro slack hslack
  filter_upwards
      [hDim_pos, hN_dim, hMoment slack hslack,
        hSampleTail slack hslack, hGammaTail slack hslack, hBad slack hslack]
    with d hdim_pos hN hMoment_d hSample_d hGamma_d hBad_d
  have hBounds :
      ConcreteSphericalBackgroundBadSetBounds
        (p := p) (q := q) (σ := σ)
        (N d) (M slack d) (τ slack d) (mean slack d)
        (bMoment slack d) (bSample slack d) (bGamma slack d) k :=
    ConcreteSphericalBackgroundBadSetBounds.of_moment_and_gaussian_operator_tails
      (p := p) (q := q) (σ := σ)
      (N := N d) (d := ambientDim d) (M := M slack d)
      (τ := τ slack d) (mean := mean slack d)
      (bMoment := bMoment slack d)
      (bSample := bSample slack d)
      (bGamma := bGamma slack d)
      (k := k)
      hdim_pos hN hMoment_d hSample_d hGamma_d
  exact
    hBounds.backgroundTypicalSet_measure_ge_half
      (p := p) (q := q) (σ := σ)
      (N := N d) (M := M slack d)
      (τ := τ slack d) (mean := mean slack d)
      (bMoment := bMoment slack d)
      (bSample := bSample slack d)
      (bGamma := bGamma slack d)
      (k := k)
      (measurableSet_backgroundTypicalSet
        (p := p) (q := q) (σ := σ)
        (N d) (M slack d) (τ slack d) (mean slack d) k)
      hBad_d

/-- Pipeline-shaped `hK_half` constructor directly from moment concentration
and the two concrete Gaussian operator good-event estimates, for a law `μ d`
eventually equal to the spherical model law. -/
theorem upper_hK_half_of_sphericalModelMeasure_moment_and_operator_tails
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {μ : ℕ → Measure (SampleMatrix p q σ)}
    {N ambientDim : ℕ → ℝ}
    {M τ mean bMoment bSample bGamma : ℝ → ℕ → ℝ}
    {k : ℕ}
    (hμ :
      ∀ᶠ d in atTop,
        μ d =
          PptFactorization.AppendixB.sphericalModelMeasure
            (p := p) (q := q) (σ := σ))
    (hDim_pos : ∀ᶠ d in atTop, 0 < ambientDim d)
    (hN_dim : ∀ᶠ d in atTop, N d = ambientDim d ^ 2)
    (hMoment :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := p) (q := q) (σ := σ)).real
            (backgroundMomentBadSet
              (p := p) (q := q) (σ := σ)
              (N d) (τ slack d) (mean slack d) k) ≤
              bMoment slack d)
    (hSampleTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (gaussianMeasure p q σ).real
            ((normalizedSampleOpNormEvent
              (p := p) (q := q) (σ := σ)
              (M slack d) (ambientDim d))ᶜ) ≤
            bSample slack d)
    (hGammaTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (gaussianMeasure p q σ).real
            ((normalizedRhoGammaOpNormEvent
              (p := p) (q := q) (σ := σ)
              (M slack d) (ambientDim d))ᶜ) ≤
            bGamma slack d)
    (hBad :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          bMoment slack d + bSample slack d + bGamma slack d ≤ 1 / 2) :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        1 / 2 ≤ (μ d).real
          (backgroundTypicalSet
            (p := p) (q := q) (σ := σ)
            (N d) (M slack d) (τ slack d) (mean slack d) k) := by
  intro slack hslack
  have hHalf :=
    upper_hK_half_sphericalModelMeasure_of_moment_and_operator_tails
      (p := p) (q := q) (σ := σ)
      (N := N) (ambientDim := ambientDim)
      (M := M) (τ := τ) (mean := mean)
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (k := k)
      hDim_pos hN_dim hMoment hSampleTail hGammaTail hBad
      slack hslack
  filter_upwards [hμ, hHalf] with d hμd hhalf
  simpa [hμd] using hhalf

/-- Concrete upper `hBad` from three one-sixth budgets.

This is only scalar arithmetic: if each of the three bad-event budgets is at
most `1 / 6`, then their sum is at most `1 / 2`. -/
theorem upper_concrete_hBad_of_each_le_sixth
    {bMoment bSample bGamma : ℝ → ℕ → ℝ}
    (hMoment :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop, bMoment slack d ≤ 1 / 6)
    (hSample :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop, bSample slack d ≤ 1 / 6)
    (hGamma :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop, bGamma slack d ≤ 1 / 6) :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        bMoment slack d + bSample slack d + bGamma slack d ≤ 1 / 2 := by
  intro slack hslack
  filter_upwards [hMoment slack hslack, hSample slack hslack, hGamma slack hslack]
    with d hMoment_d hSample_d hGamma_d
  linarith

/-- Concrete upper `hBad` from eventual smallness of each bad-event budget.

Once the moment, sample-operator, and partial-transpose bad-event budgets can
each be made eventually smaller than any fixed positive number, the scalar
union-bound budget follows automatically. -/
theorem upper_concrete_hBad_of_eventual_small
    {bMoment bSample bGamma : ℝ → ℕ → ℝ}
    (hMoment :
      ∀ slack : ℝ, 0 < slack →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop, bMoment slack d ≤ η)
    (hSample :
      ∀ slack : ℝ, 0 < slack →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop, bSample slack d ≤ η)
    (hGamma :
      ∀ slack : ℝ, 0 < slack →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop, bGamma slack d ≤ η) :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        bMoment slack d + bSample slack d + bGamma slack d ≤ 1 / 2 := by
  exact
    upper_concrete_hBad_of_each_le_sixth
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (by
        intro slack hslack
        exact hMoment slack hslack (1 / 6) (by norm_num))
      (by
        intro slack hslack
        exact hSample slack hslack (1 / 6) (by norm_num))
      (by
        intro slack hslack
        exact hGamma slack hslack (1 / 6) (by norm_num))

/-- Concrete spherical-law `hK_half` from three bad-event estimates whose
budgets are eventually small.

This removes the scalar union-budget line from the generic upper background
interface.  The caller supplies the actual moment/sample/gamma probability
estimates and the fact that each chosen budget is eventually arbitrarily
small; the `1 / 2` half-mass budget is then closed internally. -/
theorem upper_hK_half_sphericalModelMeasure_of_moment_operator_tails_eventual_small
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {N ambientDim : ℕ → ℝ}
    {M τ mean bMoment bSample bGamma : ℝ → ℕ → ℝ}
    {k : ℕ}
    (hDim_pos : ∀ᶠ d in atTop, 0 < ambientDim d)
    (hN_dim : ∀ᶠ d in atTop, N d = ambientDim d ^ 2)
    (hMoment :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := p) (q := q) (σ := σ)).real
            (backgroundMomentBadSet
              (p := p) (q := q) (σ := σ)
              (N d) (τ slack d) (mean slack d) k) ≤
              bMoment slack d)
    (hSampleTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (gaussianMeasure p q σ).real
            ((normalizedSampleOpNormEvent
              (p := p) (q := q) (σ := σ)
              (M slack d) (ambientDim d))ᶜ) ≤
            bSample slack d)
    (hGammaTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (gaussianMeasure p q σ).real
            ((normalizedRhoGammaOpNormEvent
              (p := p) (q := q) (σ := σ)
              (M slack d) (ambientDim d))ᶜ) ≤
            bGamma slack d)
    (hMomentSmall :
      ∀ slack : ℝ, 0 < slack →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop, bMoment slack d ≤ η)
    (hSampleSmall :
      ∀ slack : ℝ, 0 < slack →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop, bSample slack d ≤ η)
    (hGammaSmall :
      ∀ slack : ℝ, 0 < slack →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop, bGamma slack d ≤ η) :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        1 / 2 ≤
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := p) (q := q) (σ := σ)).real
            (backgroundTypicalSet
              (p := p) (q := q) (σ := σ)
              (N d) (M slack d) (τ slack d) (mean slack d) k) :=
  upper_hK_half_sphericalModelMeasure_of_moment_and_operator_tails
    (p := p) (q := q) (σ := σ)
    (N := N) (ambientDim := ambientDim)
    (M := M) (τ := τ) (mean := mean)
    (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
    (k := k)
    hDim_pos hN_dim hMoment hSampleTail hGammaTail
    (upper_concrete_hBad_of_eventual_small
      hMomentSmall hSampleSmall hGammaSmall)

/-- Pipeline-shaped `hK_half` for a law eventually equal to the spherical model,
with the scalar union budget closed from eventual smallness of the three
bad-event budgets. -/
theorem upper_hK_half_of_sphericalModelMeasure_moment_operator_tails_eventual_small
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {μ : ℕ → Measure (SampleMatrix p q σ)}
    {N ambientDim : ℕ → ℝ}
    {M τ mean bMoment bSample bGamma : ℝ → ℕ → ℝ}
    {k : ℕ}
    (hμ :
      ∀ᶠ d in atTop,
        μ d =
          PptFactorization.AppendixB.sphericalModelMeasure
            (p := p) (q := q) (σ := σ))
    (hDim_pos : ∀ᶠ d in atTop, 0 < ambientDim d)
    (hN_dim : ∀ᶠ d in atTop, N d = ambientDim d ^ 2)
    (hMoment :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := p) (q := q) (σ := σ)).real
            (backgroundMomentBadSet
              (p := p) (q := q) (σ := σ)
              (N d) (τ slack d) (mean slack d) k) ≤
              bMoment slack d)
    (hSampleTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (gaussianMeasure p q σ).real
            ((normalizedSampleOpNormEvent
              (p := p) (q := q) (σ := σ)
              (M slack d) (ambientDim d))ᶜ) ≤
            bSample slack d)
    (hGammaTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (gaussianMeasure p q σ).real
            ((normalizedRhoGammaOpNormEvent
              (p := p) (q := q) (σ := σ)
              (M slack d) (ambientDim d))ᶜ) ≤
            bGamma slack d)
    (hMomentSmall :
      ∀ slack : ℝ, 0 < slack →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop, bMoment slack d ≤ η)
    (hSampleSmall :
      ∀ slack : ℝ, 0 < slack →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop, bSample slack d ≤ η)
    (hGammaSmall :
      ∀ slack : ℝ, 0 < slack →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop, bGamma slack d ≤ η) :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        1 / 2 ≤ (μ d).real
          (backgroundTypicalSet
            (p := p) (q := q) (σ := σ)
            (N d) (M slack d) (τ slack d) (mean slack d) k) := by
  intro slack hslack
  have hHalf :=
    upper_hK_half_sphericalModelMeasure_of_moment_operator_tails_eventual_small
      (p := p) (q := q) (σ := σ)
      (N := N) (ambientDim := ambientDim)
      (M := M) (τ := τ) (mean := mean)
      (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
      (k := k)
      hDim_pos hN_dim hMoment hSampleTail hGammaTail
      hMomentSmall hSampleSmall hGammaSmall
      slack hslack
  filter_upwards [hμ, hHalf] with d hμd hhalf
  simpa [hμd] using hhalf

/-! ## Concrete normalized operator-tail helpers -/

/-- A normalized sample-operator good event is monotone in its threshold. -/
theorem normalizedSampleOpNormEvent_subset_of_threshold_le
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b) :
    normalizedSampleOpNormEvent (p := p) (q := q) (σ := σ) a d ⊆
      normalizedSampleOpNormEvent (p := p) (q := q) (σ := σ) b d := by
  intro ω hω
  exact le_trans hω (div_le_div_of_nonneg_right hab hd.le)

/-- Complement form of threshold monotonicity for the normalized sample event. -/
theorem normalizedSampleOpNormEvent_compl_subset_of_threshold_le
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b) :
    (normalizedSampleOpNormEvent (p := p) (q := q) (σ := σ) b d)ᶜ ⊆
      (normalizedSampleOpNormEvent (p := p) (q := q) (σ := σ) a d)ᶜ := by
  intro ω hω hsmall
  exact hω
    (normalizedSampleOpNormEvent_subset_of_threshold_le
      (p := p) (q := q) (σ := σ) hd hab hsmall)

/-- A normalized partial-transpose good event is monotone in its threshold. -/
theorem normalizedRhoGammaOpNormEvent_subset_of_threshold_le
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {a b d : ℝ} (hab : a ≤ b) :
    normalizedRhoGammaOpNormEvent (p := p) (q := q) (σ := σ) a d ⊆
      normalizedRhoGammaOpNormEvent (p := p) (q := q) (σ := σ) b d := by
  intro ω hω
  exact le_trans hω (div_le_div_of_nonneg_right hab (sq_nonneg d))

/-- Complement form of threshold monotonicity for the normalized
partial-transpose event. -/
theorem normalizedRhoGammaOpNormEvent_compl_subset_of_threshold_le
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {a b d : ℝ} (hab : a ≤ b) :
    (normalizedRhoGammaOpNormEvent (p := p) (q := q) (σ := σ) b d)ᶜ ⊆
      (normalizedRhoGammaOpNormEvent (p := p) (q := q) (σ := σ) a d)ᶜ := by
  intro ω hω hsmall
  exact hω
    (normalizedRhoGammaOpNormEvent_subset_of_threshold_le
      (p := p) (q := q) (σ := σ) hab hsmall)

/-- A nonempty finite sample type has sample dimension at least one. -/
theorem sampleDimension_ge_one_of_nonempty
    (σ : Type*) [Fintype σ] [Nonempty σ] :
    1 ≤ sampleDimension σ := by
  unfold sampleDimension
  have hpos : 0 < Fintype.card σ := Fintype.card_pos
  exact_mod_cast (Nat.succ_le_iff.mpr hpos : 1 ≤ Fintype.card σ)

/-! ## Mixed-remainder closure -/

/-- Monotonicity of the background typical set in the moment tolerance.

Shrinking `τ` only strengthens the first clause of `backgroundTypicalSet`; the
two operator-norm clauses are unchanged. -/
theorem backgroundTypicalSet_subset_of_tau_le
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {N M τSmall τBig mean : ℝ} {k : ℕ}
    (hτ : τSmall ≤ τBig) :
    backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τSmall mean k ⊆
      backgroundTypicalSet (p := p) (q := q) (σ := σ) N M τBig mean k := by
  intro Y hY
  exact ⟨hY.1.trans hτ, hY.2⟩

/-- Pipeline-shaped `hMixed` constructor from a uniform finite mixed-word
envelope.

This theorem removes the opaque mixed-remainder hypothesis at the upper-bound
interface, but keeps the real analytic work visible.  The two explicit inputs
are:

* `hEnvelope`: every sharp-radius perturbation around every
  `Y ∈ backgroundTypicalSet` is bounded by the finite `A/L/Q` mixed-word
  envelope;
* `hWordSmall`: each scalar word-envelope term is eventually arbitrarily
  small.

Together these prove exactly the `hMixed` hypothesis consumed by
`upper_eventual_from_localExpansion_scalarLimits`. -/
theorem upper_hMixed_from_uniform_wordEnvelope
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {N speed : ℕ → ℝ}
    {aSlack : ℝ → ℝ}
    {M τ mean Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    {k : ℕ}
    (hEnvelope :
      ∀ slack : ℝ, 0 < slack →
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
                (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))| ≤
              localExpansionMixedWordEnvelope
                (N d) (Abound slack d) (L2bound slack d) (L1bound slack d)
                (Q2bound slack d) (Q1bound slack d) k)
    (hWordSmall :
      ∀ slack : ℝ, 0 < slack →
        ∀ w : Fin k → LocalExpansionLetter,
          localWordIsMixed w →
            ∀ η : ℝ, 0 < η →
              ∀ᶠ d in atTop,
                localExpansionMixedWordEnvelopeTerm
                  (N d) (Abound slack d) (L2bound slack d) (L1bound slack d)
                  (Q2bound slack d) (Q1bound slack d) k w ≤ η) :
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
                (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))| ≤ η := by
  intro slack hslack η hη
  have hSmall :
      ∀ᶠ d in atTop,
        localExpansionMixedWordEnvelope
          (N d) (Abound slack d) (L2bound slack d) (L1bound slack d)
          (Q2bound slack d) (Q1bound slack d) k ≤ η :=
    localExpansionMixedWordEnvelope_eventual_small
      (Nseq := N)
      (Abound := fun d => Abound slack d)
      (L2bound := fun d => L2bound slack d)
      (L1bound := fun d => L1bound slack d)
      (Q2bound := fun d => Q2bound slack d)
      (Q1bound := fun d => Q1bound slack d)
      (k := k)
      (hWordSmall slack hslack) η hη
  filter_upwards [hEnvelope slack hslack, hSmall] with d hEnv hSmall_d
  intro X Y hY hdist
  exact le_trans (hEnv hY hdist) hSmall_d

/-- Pipeline-shaped `hMixed` constructor from pointwise word bounds.

Compared with `upper_hMixed_from_uniform_wordEnvelope`, this version expands
the envelope input one layer further: each actual mixed word
`localWordScaledTraceTerm` must be bounded by its scalar envelope term on the
sharp-radius neighbourhood.  The existing finite-sum identity for
`localExpansionMixedRemainder` then supplies the uniform envelope
automatically. -/
theorem upper_hMixed_from_uniform_mixedWordBounds
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {N speed : ℕ → ℝ}
    {aSlack : ℝ → ℝ}
    {M τ mean Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    {k : ℕ}
    (hk : 1 ≤ k)
    (hWordBound :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y : SampleMatrix p q σ⦄,
            Y ∈ backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (N d) (M slack d) (τ slack d) (mean slack d) k →
            frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
              sharpSphericalRadius (N d) (speed d) (aSlack slack) →
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                |localWordScaledTraceTerm
                    (p := p) (q := q)
                    (N d)
                    (localBackground (p := p) (q := q) (σ := σ) Y)
                    (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                    (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
                    w| ≤
                  localExpansionMixedWordEnvelopeTerm
                    (N d) (Abound slack d) (L2bound slack d) (L1bound slack d)
                    (Q2bound slack d) (Q1bound slack d) k w)
    (hWordSmall :
      ∀ slack : ℝ, 0 < slack →
        ∀ w : Fin k → LocalExpansionLetter,
          localWordIsMixed w →
            ∀ η : ℝ, 0 < η →
              ∀ᶠ d in atTop,
                localExpansionMixedWordEnvelopeTerm
                  (N d) (Abound slack d) (L2bound slack d) (L1bound slack d)
                  (Q2bound slack d) (Q1bound slack d) k w ≤ η) :
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
                (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))| ≤ η := by
  refine
    upper_hMixed_from_uniform_wordEnvelope
      (p := p) (q := q) (σ := σ)
      (N := N) (speed := speed) (aSlack := aSlack)
      (M := M) (τ := τ) (mean := mean)
      (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
      (Q2bound := Q2bound) (Q1bound := Q1bound)
      ?_ hWordSmall
  intro slack hslack
  filter_upwards [hWordBound slack hslack] with d hWordBound_d
  intro X Y hY hdist
  have h :=
    localExpansionMixedRemainder_abs_le_of_wordBounds
      (p := p) (q := q)
      (N := N d) (k := k)
      (A := localBackground (p := p) (q := q) (σ := σ) Y)
      (L := localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
      (Q := localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
      hk
      (bound := fun w =>
        localExpansionMixedWordEnvelopeTerm
          (N d) (Abound slack d) (L2bound slack d) (L1bound slack d)
          (Q2bound slack d) (Q1bound slack d) k w)
      (by
        intro w hw
        exact hWordBound_d hY hdist w hw)
  simpa [localExpansionMixedWordEnvelope, localMixedWordFilteredSum] using h

/-- Pipeline-shaped `hMixed` constructor from pointwise word bounds and scalar
limits of every word-envelope term.

This is the cleanest public replacement for the old hard `hMixed` assumption:

* `hWordBound` is the deterministic Schatten/Hölder word-by-word estimate,
  uniform for all `X` in the sharp spherical neighbourhood of all
  `Y ∈ K_N`;
* `hTermLimit` says each resulting scalar mixed-word envelope tends to `0`.

No probability or isoperimetry is used here; this is the deterministic analytic
mixed-remainder block. -/
theorem upper_hMixed_from_uniform_mixedWordBounds_and_termLimits
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {N speed : ℕ → ℝ}
    {aSlack : ℝ → ℝ}
    {M τ mean Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    {k : ℕ}
    (hk : 1 ≤ k)
    (hWordBound :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y : SampleMatrix p q σ⦄,
            Y ∈ backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (N d) (M slack d) (τ slack d) (mean slack d) k →
            frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
              sharpSphericalRadius (N d) (speed d) (aSlack slack) →
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                |localWordScaledTraceTerm
                    (p := p) (q := q)
                    (N d)
                    (localBackground (p := p) (q := q) (σ := σ) Y)
                    (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                    (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
                    w| ≤
                  localExpansionMixedWordEnvelopeTerm
                    (N d) (Abound slack d) (L2bound slack d) (L1bound slack d)
                    (Q2bound slack d) (Q1bound slack d) k w)
    (hTermLimit :
      ∀ slack : ℝ, 0 < slack →
        ∀ w : Fin k → LocalExpansionLetter,
          localWordIsMixed w →
            Tendsto
              (fun d =>
                localExpansionMixedWordEnvelopeTerm
                  (N d) (Abound slack d) (L2bound slack d) (L1bound slack d)
                  (Q2bound slack d) (Q1bound slack d) k w)
              atTop (nhds 0)) :
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
                (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))| ≤ η := by
  refine
    upper_hMixed_from_uniform_mixedWordBounds
      (p := p) (q := q) (σ := σ)
      (N := N) (speed := speed) (aSlack := aSlack)
      (M := M) (τ := τ) (mean := mean)
      (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
      (Q2bound := Q2bound) (Q1bound := Q1bound)
      hk hWordBound ?_
  intro slack hslack w hw η hη
  have hIio : Set.Iio η ∈ nhds (0 : ℝ) := Iio_mem_nhds hη
  filter_upwards [(hTermLimit slack hslack w hw).eventually hIio] with d hd
  exact le_of_lt hd

/-- Stable wrapper for the eventual upper estimate supplied by an abstract
upper-bound input.

This is the minimal external-input form at the abstract speed.  The input
`I : AbstractSpikeUpperBoundInput p speed root lam` already contains the
conditional logarithmic upper-tail hypothesis. -/
theorem upper_eventual_from_abstract_input
    {p speed : ℕ → ℝ} {root lam : ℝ}
    (I : AbstractSpikeUpperBoundInput p speed root lam) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (p d) / speed d ≤ -(lam * root) + η :=
  I.eventual_log_over_speed_upper

/-- Stable wrapper for producing a spike upper-bound input from the
slack-radius sharp-spherical pipeline.

This does not prove the random-matrix upper LDP.  The hard assumptions are still
parameters: positivity (`hlam`, `hspeed_pos`, `hp`, `hN`), radius choice
`hchoose`, tail domination `htail`, aspect control `haspect`, and the
finite-dimensional remainder bound `hremainder`. -/
theorem upper_input_of_sharpIso_slackRadius
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
    SpikeUpperBoundInput p k lam ε :=
  SpikeUpperBoundInput.of_sharp_spherical_isoperimetry_slack_radius
    (p := p) (N := N) (s := s) (aSlack := aSlack)
    (k := k) (lam := lam) (ε := ε)
    hlam hspeed_pos hp hN hchoose htail haspect hremainder

/-- Stable wrapper for the eventual upper estimate from the slack-radius
sharp-spherical pipeline.

This is conditional on the same visible sharp-spherical upper inputs as
`upper_input_of_sharpIso_slackRadius`: positivity, `hchoose`, `htail`,
`haspect`, and `hremainder`.  The wrapper only forwards those assumptions to the
existing theorem. -/
theorem upper_eventual_from_sharpIso_slackRadius
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
        Real.log (p d) / spikeSpeed k d ≤ -spikeRate k lam ε + η :=
  eventual_log_over_spikeSpeed_upper_of_sharp_spherical_isoperimetry_slack_radius
    (p := p) (N := N) (s := s) (aSlack := aSlack)
    (k := k) (lam := lam) (ε := ε)
    hlam hspeed_pos hp hN hchoose htail haspect hremainder

/-- Clean bundled endpoint for the conditional local-expansion/scalar-limits
upper-bound pipeline.

This is the main bundled closure in this file.  It proves no hard random-matrix
upper LDP; instead, it keeps the remaining analytic and geometric inputs
explicit:

* `hIso`, the `SharpSphericalIsoperimetry` input;
* `hTarget`, identifying `targetProb` with the deviation event;
* `hK_meas`, measurability of the background typical set;
* `hK_half`, half-mass of the background typical set;
* `hMixed`, mixed-remainder control near the typical set;
* `hRatio`, the aspect-ratio scalar limit;
* `hRemainderLimit`, the finite-dimensional correction limit;
* `hTau`, decay of the typical-set tolerance;
* `hGap`, the local-expansion budget gap;
* positivity, speed, and aspect assumptions such as `hk`, `hk3`, `hlam`, `hε`,
  `hp`, `hN_nonneg`, `hN_ne`, `hSpeedPow`, and the aspect-ratio hypothesis
  `hRatio`.

These assumptions are not made unconditional by the wrapper.  The theorem says
only that, once these visible inputs are supplied, the existing conditional
upper-bound pipeline returns the normalized eventual upper exponent.

By dependency inspection, this wrapper introduces no project-specific
dependency beyond the usual foundations reported for its dependencies. -/
theorem upper_eventual_from_localExpansion_scalarLimits
    {p q σ : Type*}
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
          -spikeRate k lam eps + η :=
  eventual_log_over_spikeSpeed_upper_of_localExpansion_scalar_limits
    (p := p) (q := q) (σ := σ)
    (targetProb := targetProb) (μ := μ)
    (realDim := realDim) (N := N) (s := s)
    (etaSlack := etaSlack) (M := M) (τ := τ) (mean := mean)
    (eps := eps) (k := k) (lam := lam)
    hk hk3 hlam hε hp hTarget hIso hRealDim hN_nonneg hN_ne hSpeedPow
    hK_meas hK_half hMixed hRatio hRemainderLimit hEta hGap hTau

/-! ## Concrete sequence choice for the bundled upper endpoint -/

/-- Concrete upper-bound dimension sequence `N d = d²`. -/
noncomputable def upperConcreteN (d : ℕ) : ℝ :=
  PptFactorization.AppendixB.ConcreteModel.D d

/-- Concrete upper-bound sample/aspect sequence `s d = sample d`. -/
noncomputable def upperConcreteS
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (d : ℕ) : ℝ :=
  PptFactorization.AppendixB.ConcreteModel.S (R.sample d)

/-- Concrete real ambient dimension associated to the scalar model sequences. -/
noncomputable def upperConcreteRealDim
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (d : ℕ) : ℝ :=
  2 * upperConcreteN d * upperConcreteS R d

/-- Definitional scalar form of the concrete real dimension:
`realDim d = 2 * N d * s d`. -/
theorem upperConcreteRealDim_eq_two_mul_N_S
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (d : ℕ) :
    upperConcreteRealDim R d = 2 * upperConcreteN d * upperConcreteS R d :=
  rfl

/-- The concrete scalar `N d` is exactly the bipartite dimension of the actual
model type `Fin d × Fin d`. -/
theorem upperConcreteN_eq_concreteModel_bipartiteDimension (d : ℕ) :
    upperConcreteN d =
      bipartiteDimension
        (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (PptFactorization.AppendixB.ConcreteModel.RightIndex d) := by
  rfl

/-- The actual concrete-model bipartite dimension is `d²`. -/
theorem upperConcrete_bipartiteDimension_concreteModel_eq_dimensionSquared
    (d : ℕ) :
    bipartiteDimension
        (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (PptFactorization.AppendixB.ConcreteModel.RightIndex d) =
      (d : ℝ) ^ 2 := by
  simpa [PptFactorization.AppendixB.ConcreteModel.D] using
    PptFactorization.AppendixB.ConcreteModel.D_eq d

/-- The concrete scalar `s d` is exactly the sample dimension of the actual
model type `Fin (sample d)`. -/
theorem upperConcreteS_eq_concreteModel_sampleDimension
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (d : ℕ) :
    upperConcreteS R d =
      sampleDimension
        (PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d)) := by
  rfl

/-- The actual concrete-model sample dimension is the sample count. -/
theorem upperConcrete_sampleDimension_concreteModel_eq_sample
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (d : ℕ) :
    sampleDimension
        (PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d)) =
      (R.sample d : ℝ) := by
  simpa [PptFactorization.AppendixB.ConcreteModel.S] using
    PptFactorization.AppendixB.ConcreteModel.S_eq (R.sample d)

/-- Pointwise concrete dimension bridge for the actual model family:
`realDim d = 2 * bipartiteDimension (Fin d) (Fin d) *
sampleDimension (Fin (sample d))`.

This closes the real-dimension bridge whenever the theorem is stated
pointwise over the concrete model at size `d`. -/
theorem upperConcreteRealDim_eq_concreteModel_realDim
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (d : ℕ) :
    upperConcreteRealDim R d =
      2 *
        bipartiteDimension
          (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (PptFactorization.AppendixB.ConcreteModel.RightIndex d) *
        sampleDimension
          (PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d)) := by
  simp [upperConcreteRealDim_eq_two_mul_N_S,
    upperConcreteN_eq_concreteModel_bipartiteDimension,
    upperConcreteS_eq_concreteModel_sampleDimension]

/-- The spherical matrix law used by the concrete upper-bound closure, written
as a sequence so it can be fed to the asymptotic endpoint. -/
noncomputable def upperConcreteSphericalMu
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ] :
    ℕ → Measure (SampleMatrix p q σ) :=
  fun _ =>
    PptFactorization.AppendixB.sphericalModelMeasure
      (p := p) (q := q) (σ := σ)

/-- The concrete background centering for the upper deviation event: the
spherical mean of the formal background moment functional at `N d = d²`. -/
noncomputable def upperConcreteMean
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    (k : ℕ) (d : ℕ) : ℝ :=
  ∫ X : SampleMatrix p q σ,
    backgroundMomentValue (p := p) (q := q) (σ := σ)
      (upperConcreteN d) k X
    ∂PptFactorization.AppendixB.sphericalModelMeasure
      (p := p) (q := q) (σ := σ)

/-- A concrete common operator-norm threshold for the background typical set.

The two high-probability inputs in the project have separate sample and
Gamma thresholds; the typical set uses a single scalar `M`, so this takes their
maximum.  The theorem below keeps the resulting `hK_half` and `hMixed` facts
as explicit assumptions for this chosen `M`. -/
noncomputable def upperConcreteM
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    (_slack : ℝ) (_d : ℕ) : ℝ :=
  max
    (PptFactorization.AppendixB.concreteSampleOpNormThreshold
      (p := p) (q := q) (σ := σ))
    (PptFactorization.AppendixB.concreteRhoGammaOpNormThreshold
      (p := p) (q := q) (σ := σ))

/-- Actual-model common operator-norm threshold used by the upper typical set.

Unlike the fixed-type helper `upperConcreteM`, this scalar sequence instantiates
the ambient types at `Fin d`, `Fin d`, and `Fin (R.sample d)`.  Its growth is a
real part of the upper mixed frontier. -/
noncomputable def upperConcreteModelM
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (slack : ℝ) (d : ℕ) : ℝ :=
  upperConcreteM
    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
    (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
      (R.sample d))
    slack d

/-- A positive balanced aspect ratio forces the concrete sample count to exceed
any fixed natural bound eventually. -/
theorem upper_concrete_sample_eventually_ge
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (n : ℕ) :
    ∀ᶠ d : ℕ in atTop, n ≤ R.sample d := by
  have hhalf : 0 < R.lam / 2 := by linarith [R.lam_pos]
  have hratio_gt :
      ∀ᶠ d in atTop,
        R.lam / 2 <
          PptFactorization.AppendixB.ConcreteModel.sampleRatio
            R.sample d :=
    R.ratio_tendsto.eventually
      (eventually_gt_nhds (by linarith [R.lam_pos]))
  have hd2_atTop :
      Tendsto (fun d : ℕ => (d : ℝ) ^ 2) atTop atTop := by
    simpa using
      ((tendsto_rpow_atTop (show (0 : ℝ) < 2 by norm_num)).comp
        (tendsto_natCast_atTop_atTop :
          Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop))
  have hn_div :
      Tendsto (fun d : ℕ => (n : ℝ) / ((d : ℝ) ^ 2)) atTop
        (nhds 0) :=
    hd2_atTop.const_div_atTop (n : ℝ)
  have hsmall :
      ∀ᶠ d : ℕ in atTop, (n : ℝ) / ((d : ℝ) ^ 2) < R.lam / 2 := by
    exact hn_div.eventually (eventually_lt_nhds hhalf)
  filter_upwards [hratio_gt, hsmall, eventually_gt_atTop 0]
    with d hratio hsmall_d hd
  by_contra hnot
  have hs_lt : R.sample d < n := Nat.lt_of_not_ge hnot
  have hs_le_R : (R.sample d : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (le_of_lt hs_lt)
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hden_pos : 0 < (d : ℝ) ^ 2 := by positivity
  have hratio_le :
      PptFactorization.AppendixB.ConcreteModel.sampleRatio
          R.sample d ≤
        (n : ℝ) / ((d : ℝ) ^ 2) := by
    unfold PptFactorization.AppendixB.ConcreteModel.sampleRatio
    exact div_le_div_of_nonneg_right hs_le_R (le_of_lt hden_pos)
  linarith

/-- The actual-model upper threshold dominates the explicit rho-gamma threshold. -/
theorem upperConcreteModelM_ge_gammaThreshold_explicit
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (slack : ℝ) (d : ℕ) :
    (2 + 128 * ((d : ℝ) ^ 2 + 1)) * (R.sample d : ℝ) / (1 / 2 : ℝ) ≤
      upperConcreteModelM R slack d := by
  have hmax :
      PptFactorization.AppendixB.concreteRhoGammaOpNormThreshold
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d)) ≤
        upperConcreteModelM R slack d := by
    unfold upperConcreteModelM upperConcreteM
    exact le_max_right _ _
  simpa [PptFactorization.AppendixB.concreteRhoGammaOpNormThreshold,
    PptFactorization.HighProbabilityBounds.concreteHighProbabilityBounds,
    PptFactorization.AppendixB.ConcreteModel.D_eq,
    PptFactorization.AppendixB.ConcreteModel.S_eq,
    PptFactorization.AppendixB.ConcreteModel.LeftIndex,
    PptFactorization.AppendixB.ConcreteModel.RightIndex,
    PptFactorization.AppendixB.ConcreteModel.SampleIndex,
    bipartiteDimension, sampleDimension, pow_two] using hmax

/-- The normalized actual-model upper threshold dominates the sample count.

Thus the canonical upper good-set threshold is not a fixed small edge
coefficient on the actual varying model. -/
theorem upperConcreteModelM_div_upperConcreteN_eventually_ge_sample
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (slack : ℝ) :
    ∀ᶠ d : ℕ in atTop,
      256 * (R.sample d : ℝ) ≤
        upperConcreteModelM R slack d / upperConcreteN d := by
  filter_upwards [eventually_gt_atTop 0] with d hd
  have hmain := upperConcreteModelM_ge_gammaThreshold_explicit R slack d
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hNpos : 0 < upperConcreteN d := by
    unfold upperConcreteN
    exact PptFactorization.AppendixB.ConcreteModel.D_pos hd
  apply (le_div_iff₀ hNpos).mpr
  have hs_nonneg : 0 ≤ (R.sample d : ℝ) := by positivity
  have hd2_nonneg : 0 ≤ (d : ℝ) ^ 2 := by positivity
  have hfactor :
      256 * (R.sample d : ℝ) * upperConcreteN d ≤
        (2 + 128 * ((d : ℝ) ^ 2 + 1)) *
          (R.sample d : ℝ) / (1 / 2 : ℝ) := by
    simp [upperConcreteN, PptFactorization.AppendixB.ConcreteModel.D_eq]
    nlinarith [hs_nonneg, hd2_nonneg]
  exact le_trans hfactor hmain

/-- The normalized actual-model upper threshold eventually exceeds every fixed
real bound. -/
theorem upperConcreteModelM_div_upperConcreteN_eventually_ge_real
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (slack B : ℝ) :
    ∀ᶠ d : ℕ in atTop,
      B ≤ upperConcreteModelM R slack d / upperConcreteN d := by
  obtain ⟨n, hn⟩ := exists_nat_ge (max (1 : ℝ) (B / 256 + 1))
  have hnBraw : B / 256 + 1 ≤ (n : ℝ) :=
    le_trans (le_max_right (1 : ℝ) (B / 256 + 1)) hn
  have hB_le_n : B ≤ 256 * (n : ℝ) := by nlinarith
  filter_upwards [upper_concrete_sample_eventually_ge R n,
    upperConcreteModelM_div_upperConcreteN_eventually_ge_sample R slack]
    with d hsge hge
  have hsgeR : (n : ℝ) ≤ (R.sample d : ℝ) := by exact_mod_cast hsge
  nlinarith

/-- The canonical actual-model upper background coefficient is not `o(1)`.

In particular, the upper mixed scalar limits cannot be closed merely by
plugging the current canonical good-set threshold into a fixed-`M` style
argument. -/
theorem upperConcreteModelM_div_upperConcreteN_not_eventuallySmall
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (slack : ℝ) :
    ¬ (∀ η : ℝ, 0 < η →
        ∀ᶠ d : ℕ in atTop,
          upperConcreteModelM R slack d / upperConcreteN d ≤ η) := by
  intro hsmall
  have hle_one := hsmall 1 (by norm_num)
  have hge_two := upperConcreteModelM_div_upperConcreteN_eventually_ge_real
    R slack 2
  have hfalse : ∀ᶠ _d : ℕ in atTop, False := by
    filter_upwards [hle_one, hge_two] with d hle hge
    linarith
  simp only [Filter.Eventually, Set.setOf_false] at hfalse
  have hbot : (∅ : Set ℕ) ∈ (atTop : Filter ℕ) := hfalse
  have hne : (atTop : Filter ℕ).NeBot := inferInstance
  exact hne.ne ((Filter.empty_mem_iff_bot).mp hbot)

/-- Concrete absolute-deviation target probability for the chosen upper
sequence data. -/
noncomputable def upperConcreteTargetProb
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    (eps : ℝ) (k : ℕ) : ℕ → ℝ :=
  upperBackgroundDeviationTargetProb
    (p := p) (q := q) (σ := σ)
    (upperConcreteSphericalMu (p := p) (q := q) (σ := σ))
    upperConcreteN eps
    (upperConcreteMean (p := p) (q := q) (σ := σ) k)
    k

/-! ### Actual varying concrete-model target probability -/

/-- Actual concrete-model upper deviation probability.

Unlike `upperConcreteTargetProb`, which is a fixed-type sequence used by the
legacy asymptotic pipeline, this probability uses the genuine model type at
dimension `d`:

* `p = Fin d`;
* `q = Fin d`;
* `σ = Fin (R.sample d)`;
* `N d = d²`;
* the ambient spherical law is the actual spherical model law in that
  dimension.

This definition is the paper-facing target for the fully concrete upper model
and avoids the fixed-type bridge artefacts `hIsoRealDim` and `hOperatorDim`. -/
noncomputable def upperConcreteModelTargetProb
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps : ℝ) (k : ℕ) : ℕ → ℝ :=
  fun d =>
    (PptFactorization.AppendixB.sphericalModelMeasure
      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
        (R.sample d))).real
      (backgroundMomentDeviationSet
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d))
        (upperConcreteN d) eps
        (upperConcreteMean
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          k d)
        k)

/-- Actual concrete-model one-sided upper-tail probability.

This is the varying-model analogue of `upperOneSidedMomentTargetProb`: at
dimension `d` it measures the canonical one-sided event
`F_{d,k}(X) - mean_d >= eps` under the genuine spherical model law. -/
noncomputable def upperConcreteModelOneSidedProb
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps : ℝ) (k : ℕ) : ℕ → ℝ :=
  fun d =>
    (PptFactorization.AppendixB.sphericalModelMeasure
      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
        (R.sample d))).real
      (columnMomentUpperTailSet
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d))
        (upperConcreteN d) eps
        (upperConcreteMean
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          k d)
        k)

/-- The actual one-sided upper event is contained in the absolute-deviation
target event for the varying concrete model at dimension `d`. -/
theorem upperConcreteModel_columnMomentUpperTailSet_subset_target
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps : ℝ) (k d : ℕ) :
    columnMomentUpperTailSet
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d))
        (upperConcreteN d) eps
        (upperConcreteMean
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          k d)
        k ⊆
      backgroundMomentDeviationSet
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d))
        (upperConcreteN d) eps
        (upperConcreteMean
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          k d)
        k :=
  columnMomentUpperTailSet_subset_backgroundMomentDeviationSet
    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
    (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex (R.sample d))
    (N := upperConcreteN d) (eps := eps)
    (mean :=
      upperConcreteMean
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d))
        k d)
    (k := k)

/-- Actual varying-model one-sided positivity supplier.

This is the concrete-family analogue of
`UpperConcreteOneSidedPositiveDeviationWitness`: it asks for eventual positive
spherical mass of the one-sided upper-tail event in the genuine model type at
dimension `d`. -/
def UpperConcreteModelOneSidedPositiveDeviationWitness
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps : ℝ) (k : ℕ) : Prop :=
  ∀ᶠ d in atTop,
    0 <
      (PptFactorization.AppendixB.sphericalModelMeasure
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d))).real
        (columnMomentUpperTailSet
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          (upperConcreteN d) eps
          (upperConcreteMean
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            k d)
          k)

/-- Canonical actual-model mean sequence used by the varying-model upper
endpoint. -/
noncomputable def upperConcreteModelMeanSeq
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) : ℕ → ℝ :=
  fun d =>
    upperConcreteMean
      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
        (R.sample d))
      k d

/-- The lower-closure target probability is the same event mass as the actual
upper one-sided probability after specializing to the constant upper deviation
level and the canonical actual-model mean. -/
theorem upperConcreteModelOneSidedProb_eq_lowerConcreteTargetProb
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps : ℝ) (k : ℕ) :
    upperConcreteModelOneSidedProb R eps k =
      lowerConcreteTargetProb R (fun _d : ℕ => eps)
        (upperConcreteModelMeanSeq R k) k := by
  funext d
  simp [upperConcreteModelOneSidedProb, lowerConcreteTargetProb,
    upperConcreteModelMeanSeq, upperConcreteN, lowerConcreteN,
    PptFactorization.AppendixB.ConcreteModel.D_eq]

/-- Any lower bound for the lower-closure concrete target probability is also a
lower bound for the actual upper one-sided probability. -/
theorem upperConcreteModelOneSidedProb_lowerBound_of_lowerConcreteTargetProb
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} {lower : ℕ → ℝ}
    (hle :
      ∀ᶠ d in atTop,
        lower d ≤
          lowerConcreteTargetProb R (fun _d : ℕ => eps)
            (upperConcreteModelMeanSeq R k) k d) :
    ∀ᶠ d in atTop,
      lower d ≤ upperConcreteModelOneSidedProb R eps k d := by
  filter_upwards [hle] with d hle_d
  simpa [upperConcreteModelOneSidedProb, lowerConcreteTargetProb,
    upperConcreteModelMeanSeq, upperConcreteN, lowerConcreteN,
    PptFactorization.AppendixB.ConcreteModel.D_eq] using hle_d

/-- Build the actual varying-model one-sided positivity supplier from an
eventually positive lower bound for the actual one-sided event. -/
theorem upperConcreteModelOneSidedPositiveDeviationWitness_of_eventually_positive_lower_bound
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} {lower : ℕ → ℝ}
    (hlower_pos : ∀ᶠ d in atTop, 0 < lower d)
    (hle :
      ∀ᶠ d in atTop,
        lower d ≤ upperConcreteModelOneSidedProb R eps k d) :
    UpperConcreteModelOneSidedPositiveDeviationWitness R eps k := by
  filter_upwards [hlower_pos, hle] with d hpos hle_d
  exact lt_of_lt_of_le hpos (by
    simpa [upperConcreteModelOneSidedProb] using hle_d)

/-- Positive mass of the actual one-sided upper event supplies positivity of
the actual concrete-model absolute-deviation target probability. -/
theorem upperConcreteModelTargetProb_pos_of_oneSidedPositive
    {R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime}
    {eps : ℝ} {k : ℕ}
    (hOneSided :
      UpperConcreteModelOneSidedPositiveDeviationWitness R eps k) :
    ∀ᶠ d in atTop, 0 < upperConcreteModelTargetProb R eps k d := by
  filter_upwards [hOneSided] with d hpos
  haveI : IsProbabilityMeasure
      (PptFactorization.AppendixB.sphericalModelMeasure
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d))) :=
    PptFactorization.AppendixB.sphericalModelMeasure_isProbabilityMeasure
      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
        (R.sample d))
  have hsubset :=
    upperConcreteModel_columnMomentUpperTailSet_subset_target R eps k d
  have hmono :
      (PptFactorization.AppendixB.sphericalModelMeasure
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d))).real
        (columnMomentUpperTailSet
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          (upperConcreteN d) eps
          (upperConcreteMean
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            k d)
          k) ≤
        upperConcreteModelTargetProb R eps k d := by
    exact
      measureReal_mono hsubset
        (h₂ := (measure_lt_top
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d)))
          (backgroundMomentDeviationSet
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            (upperConcreteN d) eps
            (upperConcreteMean
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              k d)
              k)).ne)
  exact lt_of_lt_of_le hpos hmono

/-- Favourable-event route to actual varying-model one-sided positivity.

This is the concrete-family analogue of
`upperConcreteOneSidedPositiveDeviationWitness_of_oneColumnFavorableEvent`.
It works at the genuine model type in each dimension `d`, so the chosen
column, direction set, background set, and deterministic estimates may all
depend on `d`.

The theorem is still only an adapter: it turns positive mass of a concrete
one-column favourable event plus the already formalized deterministic
inclusion blocks into positivity of the actual one-sided upper-tail event. -/
theorem upperConcreteModelOneSidedPositiveDeviationWitness_of_oneColumnFavorableEvent
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {α₀ : ∀ d : ℕ,
      PptFactorization.AppendixB.ConcreteModel.SampleIndex (R.sample d)}
    {q₀ δ M a center errProfile errSpike τ errScale errBg errMix errMean :
      ℕ → ℝ}
    {directionSet :
      ∀ d : ℕ,
        Set (EuclideanSpace ℂ
          (BipIndex
            (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (PptFactorization.AppendixB.ConcreteModel.RightIndex d)))}
    (hFav_pos :
      ∀ᶠ d in atTop,
        0 <
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (sphericalOneColumnFavorableEvent
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (α₀ d) (q₀ d) (δ d) (directionSet d)
              (backgroundTypicalSet
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                (upperConcreteN d) (M d) (τ d) (center d) k)))
    (hProfile :
      ∀ᶠ d in atTop,
        ∀ ρ : ℝ,
          ∀ u : EuclideanSpace ℂ
              (BipIndex
                (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (PptFactorization.AppendixB.ConcreteModel.RightIndex d)),
            ρ ∈ betaColumnIntervalSet (q₀ d) (δ d) →
            u ∈ directionSet d →
            a d ^ k - errProfile d ≤
              columnDirectionSpikeProfile
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (upperConcreteN d) k ρ u)
    (hPureError :
      ∀ᶠ d in atTop, errProfile d + 0 ≤ errSpike d)
    (hBackgroundTransfer :
      ∀ᶠ d in atTop,
        ∀ X :
            SampleMatrix
              (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d)),
          sampleColumnComplementNormalized
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              X (α₀ d) ∈
            backgroundTypicalSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d) (M d) (τ d) (center d) k →
          backgroundMomentValue
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d) k
              (sampleColumnComplementNormalized
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                X (α₀ d)) -
            errScale d ≤
          columnBackgroundContribution
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            (upperConcreteN d) k X (α₀ d))
    (hBackgroundError :
      ∀ᶠ d in atTop, τ d + errScale d ≤ errBg d)
    (hMixed :
      ∀ᶠ d in atTop,
        ∀ X :
            SampleMatrix
              (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d)),
          X ∈ sphericalOneColumnFavorableEvent
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (α₀ d) (q₀ d) (δ d) (directionSet d)
              (backgroundTypicalSet
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                (upperConcreteN d) (M d) (τ d) (center d) k) →
          |columnMixedRemainder
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d) k X (α₀ d)| ≤
            errMix d)
    (hMean :
      ∀ᶠ d in atTop,
        upperConcreteMean
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            k d ≤
          center d + errMean d)
    (hBudget :
      ∀ᶠ d in atTop,
        eps + errSpike d + errBg d + errMix d + errMean d ≤ a d ^ k) :
    UpperConcreteModelOneSidedPositiveDeviationWitness R eps k := by
  filter_upwards
      [hFav_pos, hProfile, hPureError, hBackgroundTransfer, hBackgroundError,
        hMixed, hMean, hBudget]
      with d hFav_pos_d hProfile_d hPureError_d hBackgroundTransfer_d
        hBackgroundError_d hMixed_d hMean_d hBudget_d
  haveI : IsProbabilityMeasure
      (PptFactorization.AppendixB.sphericalModelMeasure
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d))) :=
    PptFactorization.AppendixB.sphericalModelMeasure_isProbabilityMeasure
      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
        (R.sample d))
  let fav :
      Set
        (SampleMatrix
          (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))) :=
    sphericalOneColumnFavorableEvent
      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
        (R.sample d))
      (α₀ d) (q₀ d) (δ d) (directionSet d)
      (backgroundTypicalSet
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d))
        (upperConcreteN d) (M d) (τ d) (center d) k)
  let upper :
      Set
        (SampleMatrix
          (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))) :=
    columnMomentUpperTailSet
      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
        (R.sample d))
      (upperConcreteN d) eps
      (upperConcreteMean
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d))
        k d)
      k
  have hsubset : fav ⊆ upper := by
    dsimp [fav, upper]
    exact
      sphericalOneColumnFavorableEvent_subset_upperTailSet_of_closed_deterministic_blocks
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d))
        (α₀ := α₀ d)
        (q₀ := q₀ d) (δ := δ d)
        (N := upperConcreteN d) (M := M d) (a := a d)
        (eps := eps)
        (mean :=
          upperConcreteMean
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            k d)
        (center := center d)
        (errProfile := errProfile d) (errSpike := errSpike d)
        (τ := τ d) (errScale := errScale d) (errBg := errBg d)
        (errMix := errMix d) (errMean := errMean d)
        (k := k) (directionSet := directionSet d)
        hProfile_d hPureError_d hBackgroundTransfer_d hBackgroundError_d
        hMixed_d hMean_d hBudget_d
  have hmono :
      (PptFactorization.AppendixB.sphericalModelMeasure
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d))).real fav ≤
        (PptFactorization.AppendixB.sphericalModelMeasure
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))).real upper :=
    measureReal_mono hsubset
      (h₂ := (measure_lt_top
        (PptFactorization.AppendixB.sphericalModelMeasure
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d)))
        upper).ne)
  exact lt_of_lt_of_le (by simpa [fav] using hFav_pos_d)
    (by simpa [upper] using hmono)

/-- Direct favourable-event route to positivity of the actual varying-model
target probability.

This composes
`upperConcreteModelOneSidedPositiveDeviationWitness_of_oneColumnFavorableEvent`
with `upperConcreteModelTargetProb_pos_of_oneSidedPositive`, so downstream
varying-model endpoints can consume one-column favourable event data without
mentioning the intermediate one-sided witness. -/
theorem upperConcreteModelTargetProb_pos_of_oneColumnFavorableEvent
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {α₀ : ∀ d : ℕ,
      PptFactorization.AppendixB.ConcreteModel.SampleIndex (R.sample d)}
    {q₀ δ M a center errProfile errSpike τ errScale errBg errMix errMean :
      ℕ → ℝ}
    {directionSet :
      ∀ d : ℕ,
        Set (EuclideanSpace ℂ
          (BipIndex
            (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (PptFactorization.AppendixB.ConcreteModel.RightIndex d)))}
    (hFav_pos :
      ∀ᶠ d in atTop,
        0 <
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (sphericalOneColumnFavorableEvent
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (α₀ d) (q₀ d) (δ d) (directionSet d)
              (backgroundTypicalSet
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                (upperConcreteN d) (M d) (τ d) (center d) k)))
    (hProfile :
      ∀ᶠ d in atTop,
        ∀ ρ : ℝ,
          ∀ u : EuclideanSpace ℂ
              (BipIndex
                (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (PptFactorization.AppendixB.ConcreteModel.RightIndex d)),
            ρ ∈ betaColumnIntervalSet (q₀ d) (δ d) →
            u ∈ directionSet d →
            a d ^ k - errProfile d ≤
              columnDirectionSpikeProfile
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (upperConcreteN d) k ρ u)
    (hPureError :
      ∀ᶠ d in atTop, errProfile d + 0 ≤ errSpike d)
    (hBackgroundTransfer :
      ∀ᶠ d in atTop,
        ∀ X :
            SampleMatrix
              (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d)),
          sampleColumnComplementNormalized
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              X (α₀ d) ∈
            backgroundTypicalSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d) (M d) (τ d) (center d) k →
          backgroundMomentValue
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d) k
              (sampleColumnComplementNormalized
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                X (α₀ d)) -
            errScale d ≤
          columnBackgroundContribution
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            (upperConcreteN d) k X (α₀ d))
    (hBackgroundError :
      ∀ᶠ d in atTop, τ d + errScale d ≤ errBg d)
    (hMixed :
      ∀ᶠ d in atTop,
        ∀ X :
            SampleMatrix
              (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d)),
          X ∈ sphericalOneColumnFavorableEvent
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (α₀ d) (q₀ d) (δ d) (directionSet d)
              (backgroundTypicalSet
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                (upperConcreteN d) (M d) (τ d) (center d) k) →
          |columnMixedRemainder
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d) k X (α₀ d)| ≤
            errMix d)
    (hMean :
      ∀ᶠ d in atTop,
        upperConcreteMean
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            k d ≤
          center d + errMean d)
    (hBudget :
      ∀ᶠ d in atTop,
        eps + errSpike d + errBg d + errMix d + errMean d ≤ a d ^ k) :
    ∀ᶠ d in atTop, 0 < upperConcreteModelTargetProb R eps k d :=
  upperConcreteModelTargetProb_pos_of_oneSidedPositive
    (upperConcreteModelOneSidedPositiveDeviationWitness_of_oneColumnFavorableEvent
      R
      (eps := eps) (k := k) (α₀ := α₀)
      (q₀ := q₀) (δ := δ) (M := M) (a := a) (center := center)
      (errProfile := errProfile) (errSpike := errSpike)
      (τ := τ) (errScale := errScale) (errBg := errBg)
      (errMix := errMix) (errMean := errMean) (directionSet := directionSet)
      hFav_pos hProfile hPureError hBackgroundTransfer hBackgroundError
      hMixed hMean hBudget)

/-! ## Concrete target-positivity closures -/

/-- Close a raw eventual target-positivity hypothesis from any eventual
positive lower bound.

This is deliberately only an order-theoretic wrapper: it does not assert that a
given deviation event is nonempty or has positive spherical measure.  That
remaining positivity must be supplied by a concrete lower bound. -/
theorem upper_hp_of_eventually_positive_lower_bound
    {targetProb lower : ℕ → ℝ}
    (hlower_pos : ∀ᶠ d in atTop, 0 < lower d)
    (hle : ∀ᶠ d in atTop, lower d ≤ targetProb d) :
    ∀ᶠ d in atTop, 0 < targetProb d := by
  filter_upwards [hlower_pos, hle] with d hpos hle_d
  exact lt_of_lt_of_le hpos hle_d

/-- Concrete form of `upper_hp_of_eventually_positive_lower_bound` for
`upperConcreteTargetProb`.

Use this when the paper proof has produced an explicit positive lower bound
for the absolute-deviation probability. -/
theorem upper_hp_concreteTargetProb_of_eventually_positive_lower_bound
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {eps : ℝ} {k : ℕ} {lower : ℕ → ℝ}
    (hlower_pos : ∀ᶠ d in atTop, 0 < lower d)
    (hle :
      ∀ᶠ d in atTop,
        lower d ≤
          upperConcreteTargetProb
            (p := p) (q := q) (σ := σ) eps k d) :
    ∀ᶠ d in atTop,
      0 <
        upperConcreteTargetProb
          (p := p) (q := q) (σ := σ) eps k d :=
  upper_hp_of_eventually_positive_lower_bound hlower_pos hle

/-- Concrete target positivity from a positive-measure subset of the formal
deviation event.

This is the canonical way to discharge the upper pipeline's `hp` assumption
without making it disappear: the remaining input is now an explicit witness set
`E d` whose spherical measure is eventually positive and whose points all lie
in the formal `backgroundMomentDeviationSet`. -/
theorem upper_hp_concreteTargetProb_of_positive_deviation_subset
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {eps : ℝ} {k : ℕ}
    {E : ℕ → Set (SampleMatrix p q σ)}
    (hE_pos :
      ∀ᶠ d in atTop,
        0 <
          (upperConcreteSphericalMu
            (p := p) (q := q) (σ := σ) d).real (E d))
    (hE_subset :
      ∀ᶠ d in atTop,
        E d ⊆
          backgroundMomentDeviationSet
            (p := p) (q := q) (σ := σ)
            (upperConcreteN d) eps
            (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k) :
    ∀ᶠ d in atTop,
      0 <
        upperConcreteTargetProb
          (p := p) (q := q) (σ := σ) eps k d := by
  filter_upwards [hE_pos, hE_subset] with d hpos hsubset
  haveI : IsProbabilityMeasure
      (upperConcreteSphericalMu (p := p) (q := q) (σ := σ) d) := by
    dsimp [upperConcreteSphericalMu]
    exact
      PptFactorization.AppendixB.sphericalModelMeasure_isProbabilityMeasure
        (p := p) (q := q) (σ := σ)
  have hmono :
      (upperConcreteSphericalMu
        (p := p) (q := q) (σ := σ) d).real (E d) ≤
        (upperConcreteSphericalMu
          (p := p) (q := q) (σ := σ) d).real
          (backgroundMomentDeviationSet
            (p := p) (q := q) (σ := σ)
            (upperConcreteN d) eps
            (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k) :=
    measureReal_mono hsubset
      (h₂ := (measure_lt_top
        (upperConcreteSphericalMu (p := p) (q := q) (σ := σ) d)
        (backgroundMomentDeviationSet
          (p := p) (q := q) (σ := σ)
          (upperConcreteN d) eps
          (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k)).ne)
  exact lt_of_lt_of_le hpos (by
    simpa [upperConcreteTargetProb, upperBackgroundDeviationTargetProb] using
      hmono)

/-- Named target-positivity witness for the concrete upper event.

This packages the non-analytic `hp` closure data: an eventually
positive-measure set `E d` contained in the formal
`backgroundMomentDeviationSet`.  It is intentionally a witness proposition,
not a proof of the random-matrix upper bound. -/
def UpperConcretePositiveDeviationWitness
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    (eps : ℝ) (k : ℕ) (E : ℕ → Set (SampleMatrix p q σ)) : Prop :=
  (∀ᶠ d in atTop,
    0 <
      (upperConcreteSphericalMu
        (p := p) (q := q) (σ := σ) d).real (E d)) ∧
  (∀ᶠ d in atTop,
    E d ⊆
      backgroundMomentDeviationSet
        (p := p) (q := q) (σ := σ)
        (upperConcreteN d) eps
        (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k)

/-- Unpack a named concrete target-positivity witness into the raw `hp`
hypothesis for `upperConcreteTargetProb`. -/
theorem upper_hp_of_upperConcretePositiveDeviationWitness
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {eps : ℝ} {k : ℕ}
    {E : ℕ → Set (SampleMatrix p q σ)}
    (hTarget :
      UpperConcretePositiveDeviationWitness
        (p := p) (q := q) (σ := σ) eps k E) :
    ∀ᶠ d in atTop,
      0 <
        upperConcreteTargetProb
          (p := p) (q := q) (σ := σ) eps k d :=
  upper_hp_concreteTargetProb_of_positive_deviation_subset
    (p := p) (q := q) (σ := σ)
    (eps := eps) (k := k) (E := E)
    hTarget.1 hTarget.2

/-- Sharper target-positivity frontier for the actual one-sided upper event.

Instead of supplying an arbitrary witness set `E d`, this proposition asks
directly for eventual positive spherical mass of the canonical one-sided upper
tail event.  The deterministic inclusion of that event into the formal
absolute-deviation target is already proved by
`columnMomentUpperTailSet_subset_backgroundMomentDeviationSet`. -/
def UpperConcreteOneSidedPositiveDeviationWitness
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    (eps : ℝ) (k : ℕ) : Prop :=
  ∀ᶠ d in atTop,
    0 <
      (upperConcreteSphericalMu
        (p := p) (q := q) (σ := σ) d).real
        (columnMomentUpperTailSet
          (p := p) (q := q) (σ := σ)
          (upperConcreteN d) eps
          (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k)

/-- Build the actual one-sided upper-tail positivity supplier from any
eventually positive lower bound for that one-sided event. -/
theorem upperConcreteOneSidedPositiveDeviationWitness_of_eventually_positive_lower_bound
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {eps : ℝ} {k : ℕ} {lower : ℕ → ℝ}
    (hlower_pos : ∀ᶠ d in atTop, 0 < lower d)
    (hle :
      ∀ᶠ d in atTop,
        lower d ≤
          (upperConcreteSphericalMu
            (p := p) (q := q) (σ := σ) d).real
            (columnMomentUpperTailSet
              (p := p) (q := q) (σ := σ)
              (upperConcreteN d) eps
              (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k)) :
    UpperConcreteOneSidedPositiveDeviationWitness
      (p := p) (q := q) (σ := σ) eps k := by
  filter_upwards [hlower_pos, hle] with d hpos hle_d
  exact lt_of_lt_of_le hpos hle_d

/-- The canonical one-sided upper-tail positivity input supplies the witness
data used by the endpoint-facing `UpperConcretePositiveDeviationWitness`. -/
theorem upper_targetWitness_of_upperConcreteOneSidedPositiveDeviationWitness
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {eps : ℝ} {k : ℕ}
    (hOneSided :
      UpperConcreteOneSidedPositiveDeviationWitness
        (p := p) (q := q) (σ := σ) eps k) :
    UpperConcretePositiveDeviationWitness
      (p := p) (q := q) (σ := σ) eps k
      (fun d =>
        columnMomentUpperTailSet
          (p := p) (q := q) (σ := σ)
          (upperConcreteN d) eps
          (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k) := by
  constructor
  · exact hOneSided
  · exact Eventually.of_forall fun d =>
      columnMomentUpperTailSet_subset_backgroundMomentDeviationSet
        (p := p) (q := q) (σ := σ)
        (N := upperConcreteN d) (eps := eps)
        (mean := upperConcreteMean (p := p) (q := q) (σ := σ) k d)
        (k := k)

/-- The actual one-sided upper-event positivity input supplies the raw `hp`
hypothesis for the absolute-deviation target probability. -/
theorem upper_hp_of_upperConcreteOneSidedPositiveDeviationWitness
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {eps : ℝ} {k : ℕ}
    (hOneSided :
      UpperConcreteOneSidedPositiveDeviationWitness
        (p := p) (q := q) (σ := σ) eps k) :
    ∀ᶠ d in atTop,
      0 <
        upperConcreteTargetProb
          (p := p) (q := q) (σ := σ) eps k d :=
  upper_hp_of_upperConcretePositiveDeviationWitness
    (p := p) (q := q) (σ := σ)
    (eps := eps) (k := k)
    (upper_targetWitness_of_upperConcreteOneSidedPositiveDeviationWitness
      (p := p) (q := q) (σ := σ) hOneSided)

/-- Favourable-event route to actual one-sided upper-tail positivity.

This turns eventual positive mass of the concrete one-column favourable event
into eventual positive mass of the actual one-sided upper-tail event, using the
closed deterministic inclusion theorem already available from the spike-file
development. -/
theorem upperConcreteOneSidedPositiveDeviationWitness_of_oneColumnFavorableEvent
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    {eps : ℝ} {k : ℕ} {α₀ : σ}
    {q₀ δ M a center errProfile errSpike τ errScale errBg errMix errMean : ℕ → ℝ}
    {directionSet : ℕ → Set (EuclideanSpace ℂ (BipIndex p q))}
    (hFav_pos :
      ∀ᶠ d in atTop,
        0 <
          (upperConcreteSphericalMu
            (p := p) (q := q) (σ := σ) d).real
            (sphericalOneColumnFavorableEvent
              (p := p) (q := q) (σ := σ)
              α₀ (q₀ d) (δ d) (directionSet d)
              (backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M d) (τ d) (center d) k)))
    (hProfile :
      ∀ᶠ d in atTop,
        ∀ ρ : ℝ, ∀ u : EuclideanSpace ℂ (BipIndex p q),
          ρ ∈ betaColumnIntervalSet (q₀ d) (δ d) →
          u ∈ directionSet d →
          a d ^ k - errProfile d ≤
            columnDirectionSpikeProfile
              (p := p) (q := q) (upperConcreteN d) k ρ u)
    (hPureError :
      ∀ᶠ d in atTop, errProfile d + 0 ≤ errSpike d)
    (hBackgroundTransfer :
      ∀ᶠ d in atTop,
        ∀ X : SampleMatrix p q σ,
          sampleColumnComplementNormalized
              (p := p) (q := q) (σ := σ) X α₀ ∈
            backgroundTypicalSet
              (p := p) (q := q) (σ := σ)
              (upperConcreteN d) (M d) (τ d) (center d) k →
          backgroundMomentValue
              (p := p) (q := q) (σ := σ) (upperConcreteN d) k
              (sampleColumnComplementNormalized
                (p := p) (q := q) (σ := σ) X α₀) -
            errScale d ≤
          columnBackgroundContribution
            (p := p) (q := q) (σ := σ) (upperConcreteN d) k X α₀)
    (hBackgroundError :
      ∀ᶠ d in atTop, τ d + errScale d ≤ errBg d)
    (hMixed :
      ∀ᶠ d in atTop,
        ∀ X : SampleMatrix p q σ,
          X ∈ sphericalOneColumnFavorableEvent
              (p := p) (q := q) (σ := σ)
              α₀ (q₀ d) (δ d) (directionSet d)
              (backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M d) (τ d) (center d) k) →
          |columnMixedRemainder
              (p := p) (q := q) (σ := σ) (upperConcreteN d) k X α₀| ≤
            errMix d)
    (hMean :
      ∀ᶠ d in atTop,
        upperConcreteMean (p := p) (q := q) (σ := σ) k d ≤
          center d + errMean d)
    (hBudget :
      ∀ᶠ d in atTop,
        eps + errSpike d + errBg d + errMix d + errMean d ≤ a d ^ k) :
    UpperConcreteOneSidedPositiveDeviationWitness
      (p := p) (q := q) (σ := σ) eps k := by
  filter_upwards
      [hFav_pos, hProfile, hPureError, hBackgroundTransfer, hBackgroundError,
        hMixed, hMean, hBudget]
      with d hFav_pos_d hProfile_d hPureError_d hBackgroundTransfer_d
        hBackgroundError_d hMixed_d hMean_d hBudget_d
  haveI : IsProbabilityMeasure
      (upperConcreteSphericalMu (p := p) (q := q) (σ := σ) d) := by
    dsimp [upperConcreteSphericalMu]
    exact
      PptFactorization.AppendixB.sphericalModelMeasure_isProbabilityMeasure
        (p := p) (q := q) (σ := σ)
  let fav : Set (SampleMatrix p q σ) :=
    sphericalOneColumnFavorableEvent
      (p := p) (q := q) (σ := σ)
      α₀ (q₀ d) (δ d) (directionSet d)
      (backgroundTypicalSet
        (p := p) (q := q) (σ := σ)
        (upperConcreteN d) (M d) (τ d) (center d) k)
  let upper : Set (SampleMatrix p q σ) :=
    columnMomentUpperTailSet
      (p := p) (q := q) (σ := σ)
      (upperConcreteN d) eps
      (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k
  have hsubset : fav ⊆ upper := by
    dsimp [fav, upper]
    exact
      sphericalOneColumnFavorableEvent_subset_upperTailSet_of_closed_deterministic_blocks
        (p := p) (q := q) (σ := σ)
        (α₀ := α₀)
        (q₀ := q₀ d) (δ := δ d)
        (N := upperConcreteN d) (M := M d) (a := a d)
        (eps := eps)
        (mean := upperConcreteMean (p := p) (q := q) (σ := σ) k d)
        (center := center d)
        (errProfile := errProfile d) (errSpike := errSpike d)
        (τ := τ d) (errScale := errScale d) (errBg := errBg d)
        (errMix := errMix d) (errMean := errMean d)
        (k := k) (directionSet := directionSet d)
        hProfile_d hPureError_d hBackgroundTransfer_d hBackgroundError_d
        hMixed_d hMean_d hBudget_d
  have hmono :
      (upperConcreteSphericalMu
        (p := p) (q := q) (σ := σ) d).real fav ≤
        (upperConcreteSphericalMu
          (p := p) (q := q) (σ := σ) d).real upper :=
    measureReal_mono hsubset
      (h₂ := (measure_lt_top
        (upperConcreteSphericalMu (p := p) (q := q) (σ := σ) d)
        upper).ne)
  exact lt_of_lt_of_le (by simpa [fav] using hFav_pos_d) (by simpa [upper] using hmono)

/-- Concrete sequence-level upper closure.

This theorem makes the canonical choices

* `N d = d²`;
* `s d = sample d` from `ConcreteModel.BalancedRegime`;
* `μ d = sphericalModelMeasure`;
* `mean d = ∫ backgroundMomentValue (N d) k`;
* `τ slack d = slack / d`;
* `M` equal to the maximum of the concrete sample and Gamma thresholds;
* `etaSlack` equal to the canonical half-gap budget.

It then calls `upper_eventual_from_localExpansion_scalarLimits` directly.
The remaining assumptions are exactly the non-scalar upper-bound inputs for
these chosen sequences: positivity of the concrete target probability, sharp
spherical isoperimetry at `upperConcreteRealDim R d`, half-mass of the chosen
background typical set, and the mixed-remainder estimate at the chosen sharp
radius. -/
theorem upper_eventual_from_concrete_sequences_localExpansion_scalarLimits
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hp :
      ∀ᶠ d in atTop,
        0 < upperConcreteTargetProb
          (p := p) (q := q) (σ := σ) eps k d)
    (hIso :
      ∀ᶠ d in atTop,
        SharpSphericalIsoperimetry
          (p := p) (q := q) (σ := σ)
          (upperConcreteSphericalMu (p := p) (q := q) (σ := σ) d)
          (upperConcreteRealDim R d))
    (hK_half :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          1 / 2 ≤
            (upperConcreteSphericalMu (p := p) (q := q) (σ := σ) d).real
              (backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d)
                (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
                (upperCanonicalTau slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d)
                k))
    (hMixed :
      ∀ slack : ℝ, 0 < slack →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop,
            ∀ ⦃X Y : SampleMatrix p q σ⦄,
              Y ∈ backgroundTypicalSet
                  (p := p) (q := q) (σ := σ)
                  (upperConcreteN d)
                  (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
                  (upperCanonicalTau slack d)
                  (upperConcreteMean (p := p) (q := q) (σ := σ) k d)
                  k →
              frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
                sharpSphericalRadius
                  (upperConcreteN d) (spikeSpeed k d)
                  (upperSlackRadius (spikeRoot k eps) R.lam slack) →
              |localExpansionMixedRemainder (p := p) (q := q)
                  (upperConcreteN d) k
                  (localBackground (p := p) (q := q) (σ := σ) Y)
                  (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                  (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))| ≤ η) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  let hk : 0 < k := upper_hk_of_hk3 hk3
  refine
    upper_eventual_from_localExpansion_scalarLimits
      (p := p) (q := q) (σ := σ)
      (targetProb := upperConcreteTargetProb
        (p := p) (q := q) (σ := σ) eps k)
      (μ := upperConcreteSphericalMu (p := p) (q := q) (σ := σ))
      (realDim := upperConcreteRealDim R)
      (N := upperConcreteN)
      (s := upperConcreteS R)
      (etaSlack := upperCanonicalEtaSlack k eps R.lam)
      (M := upperConcreteM (p := p) (q := q) (σ := σ))
      (τ := upperCanonicalTau)
      (mean := fun _ d =>
        upperConcreteMean (p := p) (q := q) (σ := σ) k d)
      (eps := eps) (k := k) (lam := R.lam)
      hk hk3 R.lam_pos hε hp ?_ hIso ?_ ?_ ?_ ?_
      ?_ hK_half hMixed ?_ ?_ ?_ ?_ ?_
  · intro slack _hslack
    exact Eventually.of_forall fun d => rfl
  · exact Eventually.of_forall fun d => rfl
  · change ∀ᶠ d in atTop, 0 ≤ PptFactorization.AppendixB.ConcreteModel.D d
    exact upper_hN_nonneg_concreteDimension
  · simpa [upperConcreteN] using upper_hN_ne_concreteDimension
  · simpa [upperConcreteN] using upper_hSpeedPow_concreteDimension hk
  · exact
      upper_hK_meas_backgroundTypicalSet
        (p := p) (q := q) (σ := σ)
        (N := upperConcreteN)
        (M := upperConcreteM (p := p) (q := q) (σ := σ))
        (τ := upperCanonicalTau)
        (mean := fun _ d =>
          upperConcreteMean (p := p) (q := q) (σ := σ) k d)
        (k := k)
  · simpa [upperConcreteN, upperConcreteS] using
      upper_hRatio_concreteBalancedRegime_D_S R
  · simpa [upperConcreteN] using
      (upper_hRemainderLimit_concreteDimension
        (k := k) (eps := eps) (lam := R.lam))
  · exact upper_hEta_canonical hk R.lam_pos hε
  · exact upper_hGap_canonical hk R.lam_pos hε
  · exact upper_hTau_canonical

/-- Close the concrete-sequence `hIso` obligation from the deep geometric
input `FullSphericalIsoperimetry`, provided the scalar dimension sequence is
identified with the true real dimension of the fixed matrix type.

The compatibility hypothesis is deliberately explicit.  The current upper
pipeline is sequence-valued in the scalar parameters, while the ambient matrix
type is fixed in the theorem; this equality is the bridge between those two
presentations. -/
theorem upper_hIso_concrete_sequences_of_fullSphericalIsoperimetry
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (hIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (hRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ) :
    ∀ᶠ d in atTop,
      SharpSphericalIsoperimetry
        (p := p) (q := q) (σ := σ)
        (upperConcreteSphericalMu (p := p) (q := q) (σ := σ) d)
        (upperConcreteRealDim R d) := by
  have hstatic :
      SharpSphericalIsoperimetry
        (p := p) (q := q) (σ := σ)
        (PptFactorization.AppendixB.sphericalModelMeasure
          (p := p) (q := q) (σ := σ))
        (2 * bipartiteDimension p q * sampleDimension σ) :=
    sharpSphericalIsoperimetry_sphericalModelMeasure_of_fullSphericalIsoperimetry
      (p := p) (q := q) (σ := σ) hIso
  filter_upwards [hRealDim] with d hdim
  simpa [upperConcreteSphericalMu, hdim] using hstatic

/-- Pointwise concrete-model instantiation of sharp spherical isoperimetry.

This is the exact model-level statement with
`p = Fin d`, `q = Fin d`, `σ = Fin (R.sample d)` and real dimension
`upperConcreteRealDim R d = 2 * upperConcreteN d * upperConcreteS R d`.
The deep geometric theorem remains the explicit assumption
`FullSphericalIsoperimetry`; this lemma only transports it to the concrete
spherical matrix law and rewrites the dimension. -/
theorem upper_hIso_concreteModel_pointwise_of_fullSphericalIsoperimetry
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {d : ℕ} (hd : 0 < d) (hs : 0 < R.sample d)
    (hIso : PptFactorization.AppendixB.FullSphericalIsoperimetry) :
    SharpSphericalIsoperimetry
      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex (R.sample d))
      (PptFactorization.AppendixB.sphericalModelMeasure
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex (R.sample d)))
      (upperConcreteRealDim R d) := by
  letI :
      Nonempty (PptFactorization.AppendixB.ConcreteModel.LeftIndex d) :=
    PptFactorization.AppendixB.ConcreteModel.nonempty_leftIndex hd
  letI :
      Nonempty (PptFactorization.AppendixB.ConcreteModel.RightIndex d) :=
    PptFactorization.AppendixB.ConcreteModel.nonempty_rightIndex hd
  letI :
      Nonempty
        (PptFactorization.AppendixB.ConcreteModel.SampleIndex (R.sample d)) :=
    PptFactorization.AppendixB.ConcreteModel.nonempty_sampleIndex hs
  have hstatic :
      SharpSphericalIsoperimetry
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex (R.sample d))
        (PptFactorization.AppendixB.sphericalModelMeasure
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d)))
        (2 *
          bipartiteDimension
            (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (PptFactorization.AppendixB.ConcreteModel.RightIndex d) *
          sampleDimension
            (PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))) :=
    sharpSphericalIsoperimetry_sphericalModelMeasure_of_fullSphericalIsoperimetry
      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex (R.sample d))
      hIso
  have hdim :
      upperConcreteRealDim R d =
        2 *
          bipartiteDimension
            (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (PptFactorization.AppendixB.ConcreteModel.RightIndex d) *
          sampleDimension
            (PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d)) :=
    upperConcreteRealDim_eq_concreteModel_realDim R d
  simpa [hdim] using hstatic

/-- Eventual sharp spherical isoperimetry for the actual varying concrete
model family.

This is the concrete-family bridge that avoids the fixed-type artefacts
`hIsoRealDim` and `hOperatorDim`: at each sufficiently large dimension `d`,
the model type is really
`Fin d × Fin d` with sample index `Fin (R.sample d)`, and the real dimension
is exactly `upperConcreteRealDim R d = 2 * d² * R.sample d`.

The only remaining geometric input is the genuine full-sphere theorem
`FullSphericalIsoperimetry`. -/
theorem eventually_upper_hIso_concreteModel_of_fullSphericalIsoperimetry
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (hIso : PptFactorization.AppendixB.FullSphericalIsoperimetry) :
    ∀ᶠ d in atTop,
      SharpSphericalIsoperimetry
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d))
        (PptFactorization.AppendixB.sphericalModelMeasure
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d)))
        (upperConcreteRealDim R d) := by
  filter_upwards [eventually_gt_atTop 0, R.sample_pos_eventually] with d hd hs
  exact upper_hIso_concreteModel_pointwise_of_fullSphericalIsoperimetry
    R hd hs hIso

/-- Pointwise concrete-model sharp spherical isoperimetry from the exact
no-input real-sphere target.

This theorem is only a naming adapter: the input
`sphere_caps_minimize_neighborhoods` is definitionally the same deep geometric
statement as `FullSphericalIsoperimetry`.  The value of this theorem is that it
removes any ambiguity about the remaining geometric frontier: once the
real-sphere cap-minimization theorem itself is supplied, the concrete
spherical matrix-law `hIso` obligation is closed pointwise. -/
theorem upper_hIso_concreteModel_pointwise_of_sphere_caps_minimize_neighborhoods
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {d : ℕ} (hd : 0 < d) (hs : 0 < R.sample d)
    (hIso : PptFactorization.AppendixB.sphere_caps_minimize_neighborhoods) :
    SharpSphericalIsoperimetry
      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex (R.sample d))
      (PptFactorization.AppendixB.sphericalModelMeasure
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex (R.sample d)))
      (upperConcreteRealDim R d) :=
  upper_hIso_concreteModel_pointwise_of_fullSphericalIsoperimetry R hd hs hIso

/-- Eventual concrete-model sharp spherical isoperimetry from the exact
no-input real-sphere target.

Plainly: no additional dimension, polar-law, or matrix-law transport input is
left here.  The only assumption is the classical spherical cap-minimization
theorem on finite real spheres. -/
theorem eventually_upper_hIso_concreteModel_of_sphere_caps_minimize_neighborhoods
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (hIso : PptFactorization.AppendixB.sphere_caps_minimize_neighborhoods) :
    ∀ᶠ d in atTop,
      SharpSphericalIsoperimetry
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d))
        (PptFactorization.AppendixB.sphericalModelMeasure
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d)))
        (upperConcreteRealDim R d) :=
  eventually_upper_hIso_concreteModel_of_fullSphericalIsoperimetry R hIso

/-- Actual varying-model sharp spherical tail from the local-expansion
exclusion.

Unlike the fixed-type sequence endpoint, this theorem works pointwise at the
true model type in each dimension:
`p = Fin d`, `q = Fin d`, and `σ = Fin (R.sample d)`.  Consequently the real
dimension bridge is produced internally by
`eventually_upper_hIso_concreteModel_of_fullSphericalIsoperimetry`; there are
no fixed-type dimension guard hypotheses. -/
theorem upperConcreteModelTargetProb_le_sharp_spherical_tail_of_localExpansion
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {aSlack etaSlack : ℝ → ℝ}
    {M τ : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k)
    (hFullIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (ha : ∀ slack : ℝ, 0 < slack → 0 ≤ aSlack slack)
    (hEta : ∀ slack : ℝ, 0 < slack → 0 < etaSlack slack)
    (hK_half :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          1 / 2 ≤
            (PptFactorization.AppendixB.sphericalModelMeasure
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))).real
              (backgroundTypicalSet
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  k d)
                k))
    (hMixed :
      ∀ slack : ℝ, 0 < slack →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop,
            ∀ ⦃X Y :
                SampleMatrix
                  (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))⦄,
              Y ∈ backgroundTypicalSet
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  (upperConcreteN d) (M slack d) (τ slack d)
                  (upperConcreteMean
                    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                    (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                      (R.sample d))
                    k d)
                  k →
              frobeniusNorm
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  (X - Y) ≤
                sharpSphericalRadius
                  (upperConcreteN d) (spikeSpeed k d) (aSlack slack) →
              |localExpansionMixedRemainder
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (upperConcreteN d) k
                  (localBackground
                    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                    (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                      (R.sample d))
                    Y)
                  (localLinear
                    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                    (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                      (R.sample d))
                    Y (X - Y))
                  (localQuadratic
                    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                    (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                      (R.sample d))
                    (X - Y))| ≤ η)
    (hBudget :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          aSlack slack ^ k + etaSlack slack + τ slack d < eps) :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        upperConcreteModelTargetProb R eps k d ≤
          Real.exp
            (-(((upperConcreteRealDim R d - 1) *
                sharpSphericalRadiusSq
                  (upperConcreteN d) (spikeSpeed k d) (aSlack slack)) / 2)) := by
  intro slack hslack
  have hk : 0 < k := upper_hk_of_hk3 hk3
  have heta := hEta slack hslack
  filter_upwards
      [eventually_upper_hIso_concreteModel_of_fullSphericalIsoperimetry R hFullIso,
        upper_hN_nonneg_concreteDimension,
        upper_hN_ne_concreteDimension,
        (spikeSpeed_pos_eventually hk).mono (fun _ hd => le_of_lt hd),
        upper_hSpeedPow_concreteDimension hk,
        hK_half slack hslack,
        hMixed slack hslack (etaSlack slack) heta,
        hBudget slack hslack]
    with d hIso_d hN_nonneg_d hN_ne_d hspeed_nonneg_d hSpeedPow_d
      hK_half_d hMixed_d hBudget_d
  have htail :
      (PptFactorization.AppendixB.sphericalModelMeasure
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d))).real
        (backgroundMomentDeviationSet
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          (upperConcreteN d) eps
          (upperConcreteMean
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            k d)
          k) ≤
        Real.exp
          (-(((upperConcreteRealDim R d - 1) *
              sharpSphericalRadiusSq
                (upperConcreteN d) (spikeSpeed k d) (aSlack slack)) / 2)) :=
    backgroundMomentDeviation_probability_le_sharpIso_of_localExpansion
      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
        (R.sample d))
      (μ :=
        PptFactorization.AppendixB.sphericalModelMeasure
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d)))
      (realDim := upperConcreteRealDim R d)
      (N := upperConcreteN d)
      (speed := spikeSpeed k d)
      (a := aSlack slack)
      (M := M slack d) (τ := τ slack d)
      (mean :=
        upperConcreteMean
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          k d)
      (eps := eps) (η := etaSlack slack) (k := k)
      hIso_d hk3 (ha slack hslack) hN_nonneg_d hN_ne_d
      hspeed_nonneg_d hSpeedPow_d
      (measurableSet_backgroundTypicalSet
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d))
        (upperConcreteN d) (M slack d) (τ slack d)
        (upperConcreteMean
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          k d)
        k)
      hK_half_d
      (by
        intro X Y hY hdist
        exact hMixed_d hY hdist)
      hBudget_d
  simpa [upperConcreteModelTargetProb] using htail

/-- Actual varying-model upper endpoint with scalar choices closed.

This is the concrete-family replacement for the old fixed-type upper endpoint:
the matrix type varies with `d`, so the real-dimension and operator-dimension
bridges are not theorem-facing hypotheses.  The remaining inputs are the
genuine proof ingredients: target positivity, full spherical isoperimetry,
half-mass of the background typical set, and the local mixed-remainder
estimate. -/
theorem upper_eventual_from_concrete_model_localExpansion_scalarLimits
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hOneSided :
      UpperConcreteModelOneSidedPositiveDeviationWitness R eps k)
    (hFullIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (hK_half :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          1 / 2 ≤
            (PptFactorization.AppendixB.sphericalModelMeasure
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))).real
              (backgroundTypicalSet
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                (upperConcreteN d)
                (upperConcreteM
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  slack d)
                (upperCanonicalTau slack d)
                (upperConcreteMean
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  k d)
                k))
    (hMixed :
      ∀ slack : ℝ, 0 < slack →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop,
            ∀ ⦃X Y :
                SampleMatrix
                  (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))⦄,
              Y ∈ backgroundTypicalSet
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  (upperConcreteN d)
                  (upperConcreteM
                    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                    (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                      (R.sample d))
                    slack d)
                  (upperCanonicalTau slack d)
                  (upperConcreteMean
                    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                    (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                      (R.sample d))
                    k d)
                  k →
              frobeniusNorm
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  (X - Y) ≤
                sharpSphericalRadius
                  (upperConcreteN d) (spikeSpeed k d)
                  (upperSlackRadius (spikeRoot k eps) R.lam slack) →
              |localExpansionMixedRemainder
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (upperConcreteN d) k
                  (localBackground
                    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                    (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                      (R.sample d))
                    Y)
                  (localLinear
                    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                    (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                      (R.sample d))
                    Y (X - Y))
                  (localQuadratic
                    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                    (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                      (R.sample d))
                    (X - Y))| ≤ η) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  let hk : 0 < k := upper_hk_of_hk3 hk3
  let aSlack : ℝ → ℝ := fun slack =>
    upperSlackRadius (spikeRoot k eps) R.lam slack
  have hchoose :
      ∀ slack : ℝ, 0 < slack →
        0 ≤ aSlack slack ∧
          aSlack slack < spikeRoot k eps ∧
            spikeRate k R.lam eps - slack / 4 ≤ R.lam * aSlack slack := by
    intro slack hslack
    exact upperSlackRadius_spike_choice hk R.lam_pos hε slack hslack
  have hEta :
      ∀ slack : ℝ, 0 < slack →
        0 < upperCanonicalEtaSlack k eps R.lam slack :=
    upper_hEta_canonical hk R.lam_pos hε
  have hBudget :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          aSlack slack ^ k +
              upperCanonicalEtaSlack k eps R.lam slack +
            upperCanonicalTau slack d < eps := by
    exact
      eventual_localExpansion_budget_of_tau_tendsto
        (aSlack := aSlack)
        (etaSlack := upperCanonicalEtaSlack k eps R.lam)
        (τ := upperCanonicalTau) (eps := eps) (k := k)
        (by
          intro slack hslack
          exact upper_hGap_canonical hk R.lam_pos hε slack hslack)
        upper_hTau_canonical
  have hTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          upperConcreteModelTargetProb R eps k d ≤
            Real.exp
              (-(((upperConcreteRealDim R d - 1) *
                  sharpSphericalRadiusSq
                    (upperConcreteN d) (spikeSpeed k d)
                    (aSlack slack)) / 2)) :=
    upperConcreteModelTargetProb_le_sharp_spherical_tail_of_localExpansion
      R
      (eps := eps) (k := k)
      (aSlack := aSlack)
      (etaSlack := upperCanonicalEtaSlack k eps R.lam)
      (M := fun slack d =>
        upperConcreteM
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          slack d)
      (τ := upperCanonicalTau)
      hk3 hFullIso
      (by
        intro slack hslack
        exact (hchoose slack hslack).1)
      hEta hK_half
      (by
        intro slack hslack η hη
        simpa [aSlack] using hMixed slack hslack η hη)
      hBudget
  have hTailTwoNS :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          upperConcreteModelTargetProb R eps k d ≤
            Real.exp
              (-(((2 * upperConcreteN d * upperConcreteS R d - 1) *
                  sharpSphericalRadiusSq
                    (upperConcreteN d) (spikeSpeed k d)
                    (aSlack slack)) / 2)) := by
    intro slack hslack
    filter_upwards [hTail slack hslack] with d htail_d
    simpa [upperConcreteRealDim_eq_two_mul_N_S, mul_assoc, mul_comm,
      mul_left_comm] using htail_d
  have haspect :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          R.lam * aSlack slack - slack / 4 ≤
            aSlack slack * upperConcreteS R d / upperConcreteN d :=
    eventual_upperAspect_of_tendsto_ratio
      (N := upperConcreteN) (s := upperConcreteS R)
      (lam := R.lam) (aSlack := aSlack)
      (by
        simpa [upperConcreteN, upperConcreteS] using
          upper_hRatio_concreteBalancedRegime_D_S R)
  have hremainder :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          aSlack slack / (2 * upperConcreteN d ^ 2) ≤ slack / 2 :=
    eventual_upperRemainder_of_tendsto_zero
      (N := upperConcreteN) (aSlack := aSlack)
      (by
        intro slack hslack
        simpa [aSlack, upperConcreteN] using
          (upper_hRemainderLimit_concreteDimension
            (k := k) (eps := eps) (lam := R.lam) slack hslack))
  have hUpper :
      SpikeUpperBoundInput (upperConcreteModelTargetProb R eps k) k R.lam eps :=
    SpikeUpperBoundInput.of_sharp_spherical_isoperimetry_slack_radius
      (p := upperConcreteModelTargetProb R eps k)
      (N := upperConcreteN) (s := upperConcreteS R)
      (aSlack := aSlack) (k := k) (lam := R.lam) (ε := eps)
      R.lam_pos (spikeSpeed_pos_eventually hk)
      (upperConcreteModelTargetProb_pos_of_oneSidedPositive hOneSided)
      (by simpa [upperConcreteN] using upper_hN_ne_concreteDimension)
      hchoose hTailTwoNS haspect hremainder
  exact
    AbstractSpikeUpperBoundInput.eventual_log_over_speed_upper
      (p := upperConcreteModelTargetProb R eps k)
      (speed := spikeSpeed k) (root := spikeRoot k eps)
      (lam := R.lam) hUpper

/-- Actual-family mixed-remainder input at the canonical upper radius.

This is the remaining deterministic local-expansion estimate for the true
varying concrete model: for every fixed positive slack and mixed-error
allowance, eventually every point in the sharp neighbourhood of the canonical
background typical set has mixed local-expansion remainder at most that
allowance. -/
def UpperConcreteModelMixedRemainderBound
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps : ℝ) (k : ℕ) : Prop :=
  ∀ slack : ℝ, 0 < slack →
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        ∀ ⦃X Y :
            SampleMatrix
              (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))⦄,
          Y ∈ backgroundTypicalSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperConcreteM
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                slack d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                k d)
              k →
          frobeniusNorm
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (X - Y) ≤
            sharpSphericalRadius
              (upperConcreteN d) (spikeSpeed k d)
              (upperSlackRadius (spikeRoot k eps) R.lam slack) →
          |localExpansionMixedRemainder
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (upperConcreteN d) k
              (localBackground
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                Y)
              (localLinear
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                Y (X - Y))
              (localQuadratic
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                (X - Y))| ≤ η

/-- Transport the canonical actual-model mixed-remainder estimate to a stricter
moment-typical set.

The radius, operator-norm cutoff, and centering are unchanged.  The only new
input is the eventual scalar comparison `τ slack d ≤ upperCanonicalTau slack d`,
which lets membership in the smaller typical set feed the canonical
mixed-remainder bound. -/
theorem UpperConcreteModelMixedRemainderBound.of_tau_le_canonical
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} {τ : ℝ → ℕ → ℝ}
    (hMixed : UpperConcreteModelMixedRemainderBound R eps k)
    (hτ :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop, τ slack d ≤ upperCanonicalTau slack d) :
    ∀ slack : ℝ, 0 < slack →
      ∀ η : ℝ, 0 < η →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y :
              SampleMatrix
                (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))⦄,
            Y ∈ backgroundTypicalSet
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                (upperConcreteN d)
                (upperConcreteM
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  slack d)
                (τ slack d)
                (upperConcreteMean
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  k d)
                k →
            frobeniusNorm
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed k d)
                (upperSlackRadius (spikeRoot k eps) R.lam slack) →
            |localExpansionMixedRemainder
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (upperConcreteN d) k
                (localBackground
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  Y)
                (localLinear
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  Y (X - Y))
                (localQuadratic
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  (X - Y))| ≤ η := by
  intro slack hslack η hη
  filter_upwards [hMixed slack hslack η hη, hτ slack hslack] with d hMixed_d hτ_d
  intro X Y hY hdist
  exact hMixed_d (backgroundTypicalSet_subset_of_tau_le hτ_d hY) hdist

/-- Varying-model mixed-word estimate for the actual upper concrete family.

This is the model-dependent analogue of `UpperConcreteMixedWordBound`: for
each large dimension `d`, the ambient types are the actual
`Fin d`, `Fin d`, and `Fin (R.sample d)` model types.  It isolates the
deterministic word-by-word estimate below
`UpperConcreteModelMixedRemainderBound`. -/
def UpperConcreteModelMixedWordBound
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps : ℝ) (k : ℕ)
    (Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ) : Prop :=
  ∀ slack : ℝ, 0 < slack →
    ∀ᶠ d in atTop,
      ∀ ⦃X Y :
          SampleMatrix
            (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))⦄,
        Y ∈ backgroundTypicalSet
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            (upperConcreteN d)
            (upperConcreteM
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              slack d)
            (upperCanonicalTau slack d)
            (upperConcreteMean
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              k d)
            k →
        frobeniusNorm
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            (X - Y) ≤
          sharpSphericalRadius
            (upperConcreteN d) (spikeSpeed k d)
            (upperSlackRadius (spikeRoot k eps) R.lam slack) →
        ∀ w : Fin k → LocalExpansionLetter,
          localWordIsMixed w →
            |localWordScaledTraceTerm
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (upperConcreteN d)
                (localBackground
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  Y)
                (localLinear
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  Y (X - Y))
                (localQuadratic
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  (X - Y))
                w| ≤
              localExpansionMixedWordEnvelopeTerm
                (upperConcreteN d) (Abound slack d) (L2bound slack d)
                (L1bound slack d) (Q2bound slack d) (Q1bound slack d) k w

/-- Actual-model casewise mixed-word bound for words with exactly one linear
defect and no quadratic defect. -/
def UpperConcreteModelOneLinearMixedWordBound
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps : ℝ) (k : ℕ)
    (Abound L1bound : ℝ → ℕ → ℝ) : Prop :=
  ∀ slack : ℝ, 0 < slack →
    ∀ᶠ d in atTop,
      ∀ ⦃X Y :
          SampleMatrix
            (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))⦄,
        Y ∈ backgroundTypicalSet
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            (upperConcreteN d)
            (upperConcreteM
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              slack d)
            (upperCanonicalTau slack d)
            (upperConcreteMean
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              k d)
            k →
        frobeniusNorm
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            (X - Y) ≤
          sharpSphericalRadius
            (upperConcreteN d) (spikeSpeed k d)
            (upperSlackRadius (spikeRoot k eps) R.lam slack) →
        ∀ w : Fin k → LocalExpansionLetter,
          localWordHasOneLinearDefect w →
            |localWordScaledTraceTerm
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (upperConcreteN d)
                (localBackground
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  Y)
                (localLinear
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  Y (X - Y))
                (localQuadratic
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  (X - Y))
                w| ≤
              upperConcreteN d ^ (k - 1) *
                Abound slack d ^ (k - 1) * L1bound slack d

/-- Actual-model casewise mixed-word bound for words with exactly one
quadratic defect and no linear defect. -/
def UpperConcreteModelOneQuadraticMixedWordBound
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps : ℝ) (k : ℕ)
    (Abound Q1bound : ℝ → ℕ → ℝ) : Prop :=
  ∀ slack : ℝ, 0 < slack →
    ∀ᶠ d in atTop,
      ∀ ⦃X Y :
          SampleMatrix
            (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))⦄,
        Y ∈ backgroundTypicalSet
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            (upperConcreteN d)
            (upperConcreteM
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              slack d)
            (upperCanonicalTau slack d)
            (upperConcreteMean
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              k d)
            k →
        frobeniusNorm
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            (X - Y) ≤
          sharpSphericalRadius
            (upperConcreteN d) (spikeSpeed k d)
            (upperSlackRadius (spikeRoot k eps) R.lam slack) →
        ∀ w : Fin k → LocalExpansionLetter,
          localWordHasOneQuadraticDefect w →
            |localWordScaledTraceTerm
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (upperConcreteN d)
                (localBackground
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  Y)
                (localLinear
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  Y (X - Y))
                (localQuadratic
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  (X - Y))
                w| ≤
              upperConcreteN d ^ (k - 1) *
                Abound slack d ^ (k - 1) * Q1bound slack d

/-- Actual-model casewise mixed-word bound for the remaining mixed words. -/
def UpperConcreteModelMultiDefectMixedWordBound
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps : ℝ) (k : ℕ)
    (Abound L2bound Q2bound : ℝ → ℕ → ℝ) : Prop :=
  ∀ slack : ℝ, 0 < slack →
    ∀ᶠ d in atTop,
      ∀ ⦃X Y :
          SampleMatrix
            (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))⦄,
        Y ∈ backgroundTypicalSet
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            (upperConcreteN d)
            (upperConcreteM
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              slack d)
            (upperCanonicalTau slack d)
            (upperConcreteMean
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              k d)
            k →
        frobeniusNorm
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            (X - Y) ≤
          sharpSphericalRadius
            (upperConcreteN d) (spikeSpeed k d)
            (upperSlackRadius (spikeRoot k eps) R.lam slack) →
        ∀ w : Fin k → LocalExpansionLetter,
          localWordIsMixed w →
          ¬ localWordHasOneLinearDefect w →
          ¬ localWordHasOneQuadraticDefect w →
            |localWordScaledTraceTerm
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (upperConcreteN d)
                (localBackground
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  Y)
                (localLinear
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  Y (X - Y))
                (localQuadratic
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  (X - Y))
                w| ≤
              upperConcreteN d ^ (k - 1) *
                Abound slack d ^
                  localWordLetterCount LocalExpansionLetter.A w *
                L2bound slack d ^
                  localWordLetterCount LocalExpansionLetter.L w *
                Q2bound slack d ^
                  localWordLetterCount LocalExpansionLetter.Q w

/-- Assemble the actual-model mixed-word bound from the three casewise word
estimates. -/
theorem UpperConcreteModelMixedWordBound_of_caseBounds
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hOneLinear :
      UpperConcreteModelOneLinearMixedWordBound
        R eps k Abound L1bound)
    (hOneQuadratic :
      UpperConcreteModelOneQuadraticMixedWordBound
        R eps k Abound Q1bound)
    (hMulti :
      UpperConcreteModelMultiDefectMixedWordBound
        R eps k Abound L2bound Q2bound) :
    UpperConcreteModelMixedWordBound
      R eps k Abound L2bound L1bound Q2bound Q1bound := by
  intro slack hslack
  filter_upwards [hOneLinear slack hslack, hOneQuadratic slack hslack,
    hMulti slack hslack] with d hOneLinear_d hOneQuadratic_d hMulti_d
  intro X Y hY hdist w hw
  by_cases hLinear : localWordHasOneLinearDefect w
  · simpa [localExpansionMixedWordEnvelopeTerm, hLinear] using
      (hOneLinear_d hY hdist w hLinear)
  · by_cases hQuadratic : localWordHasOneQuadraticDefect w
    · simpa [localExpansionMixedWordEnvelopeTerm, hLinear, hQuadratic] using
        (hOneQuadratic_d hY hdist w hQuadratic)
    · simpa [localExpansionMixedWordEnvelopeTerm, hLinear, hQuadratic] using
        (hMulti_d hY hdist w hw hLinear hQuadratic)

/-- Actual-model canonical background operator-norm scale for mixed-word
envelopes. -/
noncomputable def upperConcreteModelMixedWordAbound
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (slack : ℝ) (d : ℕ) : ℝ :=
  upperMixedWordAbound (upperConcreteModelM R slack d) (upperConcreteN d)

/-- Actual-model canonical one-`L` trace-envelope scale at the sharp spherical
radius. -/
noncomputable def upperConcreteModelMixedWordL1bound
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps : ℝ) (k : ℕ) (slack : ℝ) (d : ℕ) : ℝ :=
  upperMixedWordL1bound
    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
    (upperConcreteN d) (upperConcreteModelM R slack d) (spikeSpeed k d)
    (upperSlackRadius (spikeRoot k eps) R.lam slack)

/-- Actual-model canonical multi-defect linear trace-envelope scale at the
sharp spherical radius. -/
noncomputable def upperConcreteModelMixedWordL2bound
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps : ℝ) (k : ℕ) (slack : ℝ) (d : ℕ) : ℝ :=
  upperMixedWordL2bound
    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
    (upperConcreteN d) (upperConcreteModelM R slack d) (spikeSpeed k d)
    (upperSlackRadius (spikeRoot k eps) R.lam slack)

/-- Actual-model canonical one-`Q` trace-envelope scale at the sharp spherical
radius. -/
noncomputable def upperConcreteModelMixedWordQ1bound
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps : ℝ) (k : ℕ) (slack : ℝ) (d : ℕ) : ℝ :=
  upperMixedWordQ1bound
    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
    (upperConcreteN d) (spikeSpeed k d)
    (upperSlackRadius (spikeRoot k eps) R.lam slack)

/-- Actual-model canonical multi-defect quadratic trace-envelope scale at the
sharp spherical radius. -/
noncomputable def upperConcreteModelMixedWordQ2bound
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps : ℝ) (k : ℕ) (slack : ℝ) (d : ℕ) : ℝ :=
  upperMixedWordQ2bound
    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
    (upperConcreteN d) (spikeSpeed k d)
    (upperSlackRadius (spikeRoot k eps) R.lam slack)

/-- At `k = 3`, the actual-model canonical one-`Q` scalar contribution has a
simple closed form after multiplying by the two background index choices. -/
theorem upperConcreteModel_oneQuadraticCanonicalBase_eq
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps slack : ℝ) {d : ℕ} (hd : 0 < d) :
    upperConcreteN d ^ (3 - 1) *
        upperConcreteModelMixedWordQ1bound R eps 3 slack d =
      upperSlackRadius (spikeRoot 3 eps) R.lam slack *
        ((d : ℝ) * spikeSpeed 3 d) := by
  have hNpos : 0 < upperConcreteN d := by
    unfold upperConcreteN
    exact PptFactorization.AppendixB.ConcreteModel.D_pos hd
  let a := upperSlackRadius (spikeRoot 3 eps) R.lam slack
  have ha_nonneg : 0 ≤ a := by
    unfold a upperSlackRadius
    exact le_max_left _ _
  have hspeed_nonneg : 0 ≤ spikeSpeed 3 d := by
    unfold spikeSpeed
    exact Real.rpow_nonneg (Nat.cast_nonneg d) _
  have hsq :
      sharpSphericalRadius (upperConcreteN d) (spikeSpeed 3 d) a ^ 2 =
        sharpSphericalRadiusSq (upperConcreteN d) (spikeSpeed 3 d) a :=
    sharpSphericalRadius_sq (N := upperConcreteN d) (speed := spikeSpeed 3 d)
      (a := a) ha_nonneg hspeed_nonneg
  have hsqrtd : Real.sqrt ((d : ℝ) * (d : ℝ)) = (d : ℝ) := by
    rw [← sq]
    exact Real.sqrt_sq (by positivity : 0 ≤ (d : ℝ))
  have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hd
  simp only [upperConcreteModelMixedWordQ1bound, upperMixedWordQ1bound]
  rw [hsq]
  simp [sharpSphericalRadiusSq, upperConcreteN,
    PptFactorization.AppendixB.ConcreteModel.D_eq,
    PptFactorization.AppendixB.ConcreteModel.LeftIndex,
    PptFactorization.AppendixB.ConcreteModel.RightIndex,
    BipIndex, Fintype.card_prod, a, hsqrtd]
  field_simp [hdne]

/-- With positive slack radius, the canonical one-`Q` base contribution grows
like a positive multiple of `d^(11/3)`. -/
theorem upperConcreteModel_oneQuadraticCanonicalBase_tendsto_atTop
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps slack : ℝ}
    (ha : 0 < upperSlackRadius (spikeRoot 3 eps) R.lam slack) :
    Tendsto
      (fun d : ℕ =>
        upperConcreteN d ^ (3 - 1) *
          upperConcreteModelMixedWordQ1bound R eps 3 slack d)
      atTop atTop := by
  let a := upperSlackRadius (spikeRoot 3 eps) R.lam slack
  have hpow : Tendsto (fun d : ℕ => a * ((d : ℝ) ^ ((11 : ℝ) / 3))) atTop atTop := by
    exact Tendsto.const_mul_atTop ha
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (11 : ℝ) / 3)).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop))
  refine hpow.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with d hd
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hspeed_eq : spikeSpeed 3 d = (d : ℝ) ^ ((8 : ℝ) / 3) := by
    norm_num [spikeSpeed]
  calc
    a * ((d : ℝ) ^ ((11 : ℝ) / 3)) =
        a * ((d : ℝ) ^ (1 + (8 : ℝ) / 3)) := by norm_num
    _ = a * (((d : ℝ) ^ 1) * ((d : ℝ) ^ ((8 : ℝ) / 3))) := by
      simpa [Real.rpow_one] using
        congrArg (fun t => a * t) (Real.rpow_add hdR (1 : ℝ) ((8 : ℝ) / 3))
    _ = a * (((d : ℝ) ^ 1) * spikeSpeed 3 d) := by
      rw [hspeed_eq]
    _ = a * ((d : ℝ) * spikeSpeed 3 d) := by
      simp
    _ = upperConcreteN d ^ (3 - 1) *
          upperConcreteModelMixedWordQ1bound R eps 3 slack d := by
      rw [upperConcreteModel_oneQuadraticCanonicalBase_eq R eps slack hd]

/-- The actual-model canonical good-set threshold only increases the
one-quadratic term, so the full canonical term also diverges for positive
slack radius. -/
theorem upperConcreteModel_oneQuadraticCanonicalTerm_tendsto_atTop
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps slack : ℝ}
    (ha : 0 < upperSlackRadius (spikeRoot 3 eps) R.lam slack) :
    Tendsto
      (fun d : ℕ =>
        upperConcreteN d ^ (3 - 1) *
          upperConcreteModelMixedWordAbound R slack d ^ (3 - 1) *
          upperConcreteModelMixedWordQ1bound R eps 3 slack d)
      atTop atTop := by
  have hbase := upperConcreteModel_oneQuadraticCanonicalBase_tendsto_atTop
    R (eps := eps) (slack := slack) ha
  refine Filter.tendsto_atTop.mpr ?_
  intro B
  filter_upwards [Filter.tendsto_atTop.mp hbase B,
    upperConcreteModelM_div_upperConcreteN_eventually_ge_real R slack 1,
    eventually_gt_atTop 0] with d hB hA hd
  have hbase_eq := upperConcreteModel_oneQuadraticCanonicalBase_eq R eps slack hd
  have hspeed_nonneg : 0 ≤ spikeSpeed 3 d := by
    unfold spikeSpeed
    exact Real.rpow_nonneg (Nat.cast_nonneg d) _
  have hbase_nonneg :
      0 ≤ upperConcreteN d ^ (3 - 1) *
          upperConcreteModelMixedWordQ1bound R eps 3 slack d := by
    rw [hbase_eq]
    exact mul_nonneg (le_of_lt ha) (mul_nonneg (Nat.cast_nonneg d) hspeed_nonneg)
  have hA' : 1 ≤ upperConcreteModelMixedWordAbound R slack d := by
    simpa [upperConcreteModelMixedWordAbound, upperMixedWordAbound] using hA
  have hAge : 1 ≤ upperConcreteModelMixedWordAbound R slack d ^ (3 - 1) := by
    change 1 ≤ upperConcreteModelMixedWordAbound R slack d ^ 2
    nlinarith
  have hbase_le :
      upperConcreteN d ^ (3 - 1) *
          upperConcreteModelMixedWordQ1bound R eps 3 slack d ≤
        upperConcreteModelMixedWordAbound R slack d ^ (3 - 1) *
          (upperConcreteN d ^ (3 - 1) *
            upperConcreteModelMixedWordQ1bound R eps 3 slack d) := by
    simpa [one_mul] using mul_le_mul_of_nonneg_right hAge hbase_nonneg
  have hterm_ge :
      upperConcreteN d ^ (3 - 1) *
          upperConcreteModelMixedWordQ1bound R eps 3 slack d ≤
        upperConcreteN d ^ (3 - 1) *
          upperConcreteModelMixedWordAbound R slack d ^ (3 - 1) *
          upperConcreteModelMixedWordQ1bound R eps 3 slack d := by
    calc
      upperConcreteN d ^ (3 - 1) *
          upperConcreteModelMixedWordQ1bound R eps 3 slack d ≤
        upperConcreteModelMixedWordAbound R slack d ^ (3 - 1) *
          (upperConcreteN d ^ (3 - 1) *
            upperConcreteModelMixedWordQ1bound R eps 3 slack d) := hbase_le
      _ = upperConcreteN d ^ (3 - 1) *
          upperConcreteModelMixedWordAbound R slack d ^ (3 - 1) *
          upperConcreteModelMixedWordQ1bound R eps 3 slack d := by ring
  exact le_trans hB hterm_ge

/-- At `k = 3`, the actual-model canonical one-`L` scalar contribution reduces
to the background threshold times the sharp spherical radius. -/
theorem upperConcreteModel_oneLinearCanonicalBase_eq
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps slack : ℝ) {d : ℕ} (hd : 0 < d) :
    upperConcreteN d ^ (3 - 1) *
        upperConcreteModelMixedWordL1bound R eps 3 slack d =
      2 * upperConcreteModelM R slack d * upperConcreteN d ^ (3 - 1) *
        sharpSphericalRadius (upperConcreteN d) (spikeSpeed 3 d)
          (upperSlackRadius (spikeRoot 3 eps) R.lam slack) := by
  have hsqrtd : Real.sqrt ((d : ℝ) * (d : ℝ)) = (d : ℝ) := by
    rw [← sq]
    exact Real.sqrt_sq (by positivity : 0 ≤ (d : ℝ))
  have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hd
  simp [upperConcreteModelMixedWordL1bound, upperMixedWordL1bound,
    upperConcreteN, PptFactorization.AppendixB.ConcreteModel.D_eq,
    PptFactorization.AppendixB.ConcreteModel.LeftIndex,
    PptFactorization.AppendixB.ConcreteModel.RightIndex,
    BipIndex, Fintype.card_prod, hsqrtd]
  field_simp [hdne]

/-- Squared sharp radius in the actual upper model at `k = 3`.  The radius
itself shrinks, but only like `d^(-2/3)`. -/
theorem upperConcreteModel_spikeRadiusSq_eq
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps slack : ℝ) {d : ℕ} (hd : 0 < d) :
    sharpSphericalRadius (upperConcreteN d) (spikeSpeed 3 d)
          (upperSlackRadius (spikeRoot 3 eps) R.lam slack) ^ 2 =
      upperSlackRadius (spikeRoot 3 eps) R.lam slack *
        ((d : ℝ) ^ (-(4 : ℝ) / 3)) := by
  let a := upperSlackRadius (spikeRoot 3 eps) R.lam slack
  have ha_nonneg : 0 ≤ a := by
    unfold a upperSlackRadius
    exact le_max_left _ _
  have hspeed_nonneg : 0 ≤ spikeSpeed 3 d := by
    unfold spikeSpeed
    exact Real.rpow_nonneg (Nat.cast_nonneg d) _
  have hsq :
      sharpSphericalRadius (upperConcreteN d) (spikeSpeed 3 d) a ^ 2 =
        sharpSphericalRadiusSq (upperConcreteN d) (spikeSpeed 3 d) a :=
    sharpSphericalRadius_sq (N := upperConcreteN d) (speed := spikeSpeed 3 d)
      (a := a) ha_nonneg hspeed_nonneg
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hspeed_eq : spikeSpeed 3 d = (d : ℝ) ^ ((8 : ℝ) / 3) := by
    norm_num [spikeSpeed]
  rw [hsq]
  simp [sharpSphericalRadiusSq, upperConcreteN,
    PptFactorization.AppendixB.ConcreteModel.D_eq, hspeed_eq, a]
  calc
    a * (d : ℝ) ^ ((8 : ℝ) / 3) / ((d : ℝ) ^ 2) ^ 2 =
        a * ((d : ℝ) ^ ((8 : ℝ) / 3) / (d : ℝ) ^ 4) := by ring
    _ = a * ((d : ℝ) ^ (-(4 : ℝ) / 3)) := by
      congr 1
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_sub hdR]
      congr
      norm_num

/-- The squared `N^3`-weighted sharp radius grows like `d^(32/3)` when the
slack radius is positive. -/
theorem upperConcreteModel_Ncube_spikeRadius_sq_eq
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps slack : ℝ) {d : ℕ} (hd : 0 < d) :
    (upperConcreteN d ^ 3 *
      sharpSphericalRadius (upperConcreteN d) (spikeSpeed 3 d)
        (upperSlackRadius (spikeRoot 3 eps) R.lam slack)) ^ 2 =
      upperSlackRadius (spikeRoot 3 eps) R.lam slack *
        ((d : ℝ) ^ ((32 : ℝ) / 3)) := by
  have hr2 := upperConcreteModel_spikeRadiusSq_eq R eps slack hd
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  rw [mul_pow, hr2]
  simp [upperConcreteN, PptFactorization.AppendixB.ConcreteModel.D_eq]
  calc
    (((d : ℝ) ^ 2) ^ 3) ^ 2 *
        (upperSlackRadius (spikeRoot 3 eps) R.lam slack *
          (d : ℝ) ^ (-(4 : ℝ) / 3)) =
      upperSlackRadius (spikeRoot 3 eps) R.lam slack *
        ((d : ℝ) ^ 12 * (d : ℝ) ^ (-(4 : ℝ) / 3)) := by ring
    _ = upperSlackRadius (spikeRoot 3 eps) R.lam slack *
        ((d : ℝ) ^ ((32 : ℝ) / 3)) := by
      congr 1
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_add hdR]
      congr
      norm_num

/-- With positive slack radius, `N^3` times the sharp radius diverges.  This is
the growth left after the shrinking one-`L` radius is combined with the actual
upper-model background threshold. -/
theorem upperConcreteModel_Ncube_spikeRadius_tendsto_atTop
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps slack : ℝ}
    (ha : 0 < upperSlackRadius (spikeRoot 3 eps) R.lam slack) :
    Tendsto
      (fun d : ℕ => upperConcreteN d ^ 3 *
        sharpSphericalRadius (upperConcreteN d) (spikeSpeed 3 d)
          (upperSlackRadius (spikeRoot 3 eps) R.lam slack))
      atTop atTop := by
  let a := upperSlackRadius (spikeRoot 3 eps) R.lam slack
  have hsqtop : Tendsto
      (fun d : ℕ => (upperConcreteN d ^ 3 *
        sharpSphericalRadius (upperConcreteN d) (spikeSpeed 3 d) a) ^ 2)
      atTop atTop := by
    have hpow : Tendsto (fun d : ℕ => a * ((d : ℝ) ^ ((32 : ℝ) / 3))) atTop atTop := by
      exact Tendsto.const_mul_atTop ha
        ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (32 : ℝ) / 3)).comp
          (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop))
    refine hpow.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with d hd
    rw [upperConcreteModel_Ncube_spikeRadius_sq_eq R eps slack hd]
  refine Filter.tendsto_atTop.mpr ?_
  intro B
  by_cases hB : B ≤ 0
  · filter_upwards [eventually_gt_atTop 0] with d hd
    have hNpos : 0 < upperConcreteN d := by
      unfold upperConcreteN
      exact PptFactorization.AppendixB.ConcreteModel.D_pos hd
    have hN_nonneg : 0 ≤ upperConcreteN d ^ 3 := by positivity
    have hr_nonneg : 0 ≤ sharpSphericalRadius (upperConcreteN d) (spikeSpeed 3 d) a := by
      unfold sharpSphericalRadius
      exact Real.sqrt_nonneg _
    exact le_trans hB (mul_nonneg hN_nonneg hr_nonneg)
  · have hBpos : 0 < B := lt_of_not_ge hB
    filter_upwards [Filter.tendsto_atTop.mp hsqtop (B ^ 2), eventually_gt_atTop 0]
      with d hsq_ge hd
    have hNpos : 0 < upperConcreteN d := by
      unfold upperConcreteN
      exact PptFactorization.AppendixB.ConcreteModel.D_pos hd
    have hN_nonneg : 0 ≤ upperConcreteN d ^ 3 := by positivity
    have hr_nonneg : 0 ≤ sharpSphericalRadius (upperConcreteN d) (spikeSpeed 3 d) a := by
      unfold sharpSphericalRadius
      exact Real.sqrt_nonneg _
    have hf_nonneg :
        0 ≤ upperConcreteN d ^ 3 *
          sharpSphericalRadius (upperConcreteN d) (spikeSpeed 3 d) a :=
      mul_nonneg hN_nonneg hr_nonneg
    nlinarith [sq_nonneg
      (upperConcreteN d ^ 3 * sharpSphericalRadius (upperConcreteN d) (spikeSpeed 3 d) a)]

/-- The squared `N`-weighted sharp radius grows like `d^(8/3)` when the slack
radius is positive. -/
theorem upperConcreteModel_N_spikeRadius_sq_eq
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps slack : ℝ) {d : ℕ} (hd : 0 < d) :
    (upperConcreteN d *
      sharpSphericalRadius (upperConcreteN d) (spikeSpeed 3 d)
        (upperSlackRadius (spikeRoot 3 eps) R.lam slack)) ^ 2 =
      upperSlackRadius (spikeRoot 3 eps) R.lam slack *
        ((d : ℝ) ^ ((8 : ℝ) / 3)) := by
  have hr2 := upperConcreteModel_spikeRadiusSq_eq R eps slack hd
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  rw [mul_pow, hr2]
  simp [upperConcreteN, PptFactorization.AppendixB.ConcreteModel.D_eq]
  calc
    ((d : ℝ) ^ 2) ^ 2 *
        (upperSlackRadius (spikeRoot 3 eps) R.lam slack *
          (d : ℝ) ^ (-(4 : ℝ) / 3)) =
      upperSlackRadius (spikeRoot 3 eps) R.lam slack *
        ((d : ℝ) ^ 4 * (d : ℝ) ^ (-(4 : ℝ) / 3)) := by ring
    _ = upperSlackRadius (spikeRoot 3 eps) R.lam slack *
        ((d : ℝ) ^ ((8 : ℝ) / 3)) := by
      congr 1
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_add hdR]
      congr
      norm_num

/-- With positive slack radius, `N` times the sharp radius diverges. -/
theorem upperConcreteModel_N_spikeRadius_tendsto_atTop
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps slack : ℝ}
    (ha : 0 < upperSlackRadius (spikeRoot 3 eps) R.lam slack) :
    Tendsto
      (fun d : ℕ => upperConcreteN d *
        sharpSphericalRadius (upperConcreteN d) (spikeSpeed 3 d)
          (upperSlackRadius (spikeRoot 3 eps) R.lam slack))
      atTop atTop := by
  let a := upperSlackRadius (spikeRoot 3 eps) R.lam slack
  have hsqtop : Tendsto
      (fun d : ℕ => (upperConcreteN d *
        sharpSphericalRadius (upperConcreteN d) (spikeSpeed 3 d) a) ^ 2)
      atTop atTop := by
    have hpow : Tendsto (fun d : ℕ => a * ((d : ℝ) ^ ((8 : ℝ) / 3))) atTop atTop := by
      exact Tendsto.const_mul_atTop ha
        ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (8 : ℝ) / 3)).comp
          (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop))
    refine hpow.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with d hd
    rw [upperConcreteModel_N_spikeRadius_sq_eq R eps slack hd]
  refine Filter.tendsto_atTop.mpr ?_
  intro B
  by_cases hB : B ≤ 0
  · filter_upwards [eventually_gt_atTop 0] with d hd
    have hNpos : 0 < upperConcreteN d := by
      unfold upperConcreteN
      exact PptFactorization.AppendixB.ConcreteModel.D_pos hd
    have hN_nonneg : 0 ≤ upperConcreteN d := le_of_lt hNpos
    have hr_nonneg : 0 ≤ sharpSphericalRadius (upperConcreteN d) (spikeSpeed 3 d) a := by
      unfold sharpSphericalRadius
      exact Real.sqrt_nonneg _
    exact le_trans hB (mul_nonneg hN_nonneg hr_nonneg)
  · have hBpos : 0 < B := lt_of_not_ge hB
    filter_upwards [Filter.tendsto_atTop.mp hsqtop (B ^ 2), eventually_gt_atTop 0]
      with d hsq_ge hd
    have hNpos : 0 < upperConcreteN d := by
      unfold upperConcreteN
      exact PptFactorization.AppendixB.ConcreteModel.D_pos hd
    have hN_nonneg : 0 ≤ upperConcreteN d := le_of_lt hNpos
    have hr_nonneg : 0 ≤ sharpSphericalRadius (upperConcreteN d) (spikeSpeed 3 d) a := by
      unfold sharpSphericalRadius
      exact Real.sqrt_nonneg _
    have hf_nonneg :
        0 ≤ upperConcreteN d * sharpSphericalRadius (upperConcreteN d) (spikeSpeed 3 d) a :=
      mul_nonneg hN_nonneg hr_nonneg
    nlinarith [sq_nonneg
      (upperConcreteN d * sharpSphericalRadius (upperConcreteN d) (spikeSpeed 3 d) a)]

/-- The actual-model canonical one-`L` scalar term also diverges at `k = 3`
for a positive slack radius. -/
theorem upperConcreteModel_oneLinearCanonicalTerm_tendsto_atTop
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps slack : ℝ}
    (ha : 0 < upperSlackRadius (spikeRoot 3 eps) R.lam slack) :
    Tendsto
      (fun d : ℕ =>
        upperConcreteN d ^ (3 - 1) *
          upperConcreteModelMixedWordAbound R slack d ^ (3 - 1) *
          upperConcreteModelMixedWordL1bound R eps 3 slack d)
      atTop atTop := by
  have hbase := upperConcreteModel_Ncube_spikeRadius_tendsto_atTop
    R (eps := eps) (slack := slack) ha
  refine Filter.tendsto_atTop.mpr ?_
  intro B
  filter_upwards [Filter.tendsto_atTop.mp hbase B,
    upperConcreteModelM_div_upperConcreteN_eventually_ge_real R slack 1,
    eventually_gt_atTop 0] with d hB hA hd
  let rad := sharpSphericalRadius (upperConcreteN d) (spikeSpeed 3 d)
        (upperSlackRadius (spikeRoot 3 eps) R.lam slack)
  have hNpos : 0 < upperConcreteN d := by
    unfold upperConcreteN
    exact PptFactorization.AppendixB.ConcreteModel.D_pos hd
  have hr_nonneg : 0 ≤ rad := by
    unfold rad sharpSphericalRadius
    exact Real.sqrt_nonneg _
  have hMge : upperConcreteN d ≤ upperConcreteModelM R slack d := by
    have h := (le_div_iff₀ hNpos).mp hA
    simpa using h
  have hA_ge : 1 ≤ upperConcreteModelMixedWordAbound R slack d := by
    simpa [upperConcreteModelMixedWordAbound, upperMixedWordAbound] using hA
  have hA2_ge : 1 ≤ upperConcreteModelMixedWordAbound R slack d ^ (3 - 1) := by
    change 1 ≤ upperConcreteModelMixedWordAbound R slack d ^ 2
    nlinarith
  have hbase_eq := upperConcreteModel_oneLinearCanonicalBase_eq R eps slack hd
  have hN3_le_base : upperConcreteN d ^ 3 * rad ≤
      upperConcreteN d ^ (3 - 1) * upperConcreteModelMixedWordL1bound R eps 3 slack d := by
    rw [hbase_eq]
    change upperConcreteN d ^ 3 * rad ≤
      2 * upperConcreteModelM R slack d * upperConcreteN d ^ 2 * rad
    nlinarith [sq_nonneg (upperConcreteN d), mul_nonneg (sq_nonneg (upperConcreteN d)) hr_nonneg]
  have hbase_nonneg :
      0 ≤ upperConcreteN d ^ (3 - 1) * upperConcreteModelMixedWordL1bound R eps 3 slack d :=
    le_trans (mul_nonneg (by positivity : 0 ≤ upperConcreteN d ^ 3) hr_nonneg) hN3_le_base
  have hle_term : upperConcreteN d ^ 3 * rad ≤
      upperConcreteN d ^ (3 - 1) *
        upperConcreteModelMixedWordAbound R slack d ^ (3 - 1) *
        upperConcreteModelMixedWordL1bound R eps 3 slack d := by
    calc
      upperConcreteN d ^ 3 * rad ≤
        upperConcreteN d ^ (3 - 1) * upperConcreteModelMixedWordL1bound R eps 3 slack d :=
          hN3_le_base
      _ ≤ upperConcreteModelMixedWordAbound R slack d ^ (3 - 1) *
          (upperConcreteN d ^ (3 - 1) * upperConcreteModelMixedWordL1bound R eps 3 slack d) := by
        simpa [one_mul] using mul_le_mul_of_nonneg_right hA2_ge hbase_nonneg
      _ = upperConcreteN d ^ (3 - 1) *
          upperConcreteModelMixedWordAbound R slack d ^ (3 - 1) *
          upperConcreteModelMixedWordL1bound R eps 3 slack d := by ring
  exact le_trans hB hle_term

/-- Pointwise form of the actual-model canonical one-`L` scalar. -/
theorem upperConcreteModel_oneLinearCanonicalScalar_eq
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps slack : ℝ) {d : ℕ} (hd : 0 < d) :
    upperConcreteModelMixedWordL1bound R eps 3 slack d =
      2 * upperConcreteModelM R slack d *
        sharpSphericalRadius (upperConcreteN d) (spikeSpeed 3 d)
          (upperSlackRadius (spikeRoot 3 eps) R.lam slack) := by
  have hbase := upperConcreteModel_oneLinearCanonicalBase_eq R eps slack hd
  have hNpos : 0 < upperConcreteN d := by
    unfold upperConcreteN
    exact PptFactorization.AppendixB.ConcreteModel.D_pos hd
  have hN2ne : upperConcreteN d ^ (3 - 1) ≠ 0 := by positivity
  have h := congrArg (fun x => x / upperConcreteN d ^ (3 - 1)) hbase
  field_simp [hN2ne] at h
  simpa using h

/-- The actual-model canonical one-`L` scalar itself diverges for positive
slack radius. -/
theorem upperConcreteModel_oneLinearCanonicalScalar_tendsto_atTop
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps slack : ℝ}
    (ha : 0 < upperSlackRadius (spikeRoot 3 eps) R.lam slack) :
    Tendsto
      (fun d : ℕ => upperConcreteModelMixedWordL1bound R eps 3 slack d)
      atTop atTop := by
  have hbase := upperConcreteModel_N_spikeRadius_tendsto_atTop R (eps := eps) (slack := slack) ha
  refine Filter.tendsto_atTop.mpr ?_
  intro B
  filter_upwards [Filter.tendsto_atTop.mp hbase B,
    upperConcreteModelM_div_upperConcreteN_eventually_ge_real R slack 1,
    eventually_gt_atTop 0] with d hB hA hd
  let rad := sharpSphericalRadius (upperConcreteN d) (spikeSpeed 3 d)
        (upperSlackRadius (spikeRoot 3 eps) R.lam slack)
  have hNpos : 0 < upperConcreteN d := by
    unfold upperConcreteN
    exact PptFactorization.AppendixB.ConcreteModel.D_pos hd
  have hr_nonneg : 0 ≤ rad := by
    unfold rad sharpSphericalRadius
    exact Real.sqrt_nonneg _
  have hMge : upperConcreteN d ≤ upperConcreteModelM R slack d := by
    have h := (le_div_iff₀ hNpos).mp hA
    simpa using h
  have hL1 := upperConcreteModel_oneLinearCanonicalScalar_eq R eps slack hd
  have hNrad_le_L1 :
      upperConcreteN d * rad ≤ upperConcreteModelMixedWordL1bound R eps 3 slack d := by
    rw [hL1]
    change upperConcreteN d * rad ≤ 2 * upperConcreteModelM R slack d * rad
    nlinarith
  exact le_trans hB hNrad_le_L1

/-- The length-three pure-linear word used to test the multi-defect scalar
branch. -/
def upperConcreteModelPureL3Word : Fin 3 → LocalExpansionLetter :=
  fun _ => LocalExpansionLetter.L

/-- For the pure-`L` length-three word, the canonical multi-defect scalar term
diverges. -/
theorem upperConcreteModel_pureL3CanonicalMultiTerm_tendsto_atTop
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps slack : ℝ}
    (ha : 0 < upperSlackRadius (spikeRoot 3 eps) R.lam slack) :
    Tendsto
      (fun d : ℕ =>
        upperConcreteN d ^ (3 - 1) *
          upperConcreteModelMixedWordAbound R slack d ^
            localWordLetterCount LocalExpansionLetter.A upperConcreteModelPureL3Word *
          upperConcreteModelMixedWordL2bound R eps 3 slack d ^
            localWordLetterCount LocalExpansionLetter.L upperConcreteModelPureL3Word *
          upperConcreteModelMixedWordQ2bound R eps 3 slack d ^
            localWordLetterCount LocalExpansionLetter.Q upperConcreteModelPureL3Word)
      atTop atTop := by
  have hL1top := upperConcreteModel_oneLinearCanonicalScalar_tendsto_atTop
    R (eps := eps) (slack := slack) ha
  refine Filter.tendsto_atTop.mpr ?_
  intro B
  filter_upwards [Filter.tendsto_atTop.mp hL1top (max B 1), eventually_gt_atTop 0]
    with d hL1ge hd
  have hN2ge : 1 ≤ upperConcreteN d ^ (3 - 1) := by
    change 1 ≤ upperConcreteN d ^ 2
    have hNge1 : 1 ≤ upperConcreteN d := by
      unfold upperConcreteN
      simp [PptFactorization.AppendixB.ConcreteModel.D_eq]
      nlinarith [show (1 : ℝ) ≤ d by exact_mod_cast (Nat.succ_le_of_lt hd)]
    nlinarith
  have hL1ge1 :
      1 ≤ upperConcreteModelMixedWordL1bound R eps 3 slack d :=
    le_trans (le_max_right B 1) hL1ge
  have hB_le_L1 :
      B ≤ upperConcreteModelMixedWordL1bound R eps 3 slack d :=
    le_trans (le_max_left B 1) hL1ge
  have hL1_nonneg :
      0 ≤ upperConcreteModelMixedWordL1bound R eps 3 slack d :=
    le_trans zero_le_one hL1ge1
  have hL1_le_cube :
      upperConcreteModelMixedWordL1bound R eps 3 slack d ≤
        upperConcreteModelMixedWordL1bound R eps 3 slack d ^ 3 := by
    have hsquare :
        1 ≤ upperConcreteModelMixedWordL1bound R eps 3 slack d ^ 2 := by nlinarith
    calc
      upperConcreteModelMixedWordL1bound R eps 3 slack d =
        1 * upperConcreteModelMixedWordL1bound R eps 3 slack d := by ring
      _ ≤ upperConcreteModelMixedWordL1bound R eps 3 slack d ^ 2 *
          upperConcreteModelMixedWordL1bound R eps 3 slack d :=
        mul_le_mul_of_nonneg_right hsquare hL1_nonneg
      _ = upperConcreteModelMixedWordL1bound R eps 3 slack d ^ 3 := by ring
  have hcube_nonneg :
      0 ≤ upperConcreteModelMixedWordL1bound R eps 3 slack d ^ 3 := by positivity
  have hterm_ge_cube :
      upperConcreteModelMixedWordL1bound R eps 3 slack d ^ 3 ≤
        upperConcreteN d ^ (3 - 1) *
          upperConcreteModelMixedWordL1bound R eps 3 slack d ^ 3 := by
    simpa [one_mul] using mul_le_mul_of_nonneg_right hN2ge hcube_nonneg
  have hAcount :
      localWordLetterCount LocalExpansionLetter.A upperConcreteModelPureL3Word = 0 := by
    simp [upperConcreteModelPureL3Word, localWordLetterCount]
  have hLcount :
      localWordLetterCount LocalExpansionLetter.L upperConcreteModelPureL3Word = 3 := by
    simp [upperConcreteModelPureL3Word, localWordLetterCount]
  have hQcount :
      localWordLetterCount LocalExpansionLetter.Q upperConcreteModelPureL3Word = 0 := by
    simp [upperConcreteModelPureL3Word, localWordLetterCount]
  calc
    B ≤ upperConcreteModelMixedWordL1bound R eps 3 slack d := hB_le_L1
    _ ≤ upperConcreteModelMixedWordL1bound R eps 3 slack d ^ 3 := hL1_le_cube
    _ ≤ upperConcreteN d ^ (3 - 1) *
          upperConcreteModelMixedWordL1bound R eps 3 slack d ^ 3 := hterm_ge_cube
    _ = upperConcreteN d ^ (3 - 1) *
          upperConcreteModelMixedWordAbound R slack d ^
            localWordLetterCount LocalExpansionLetter.A upperConcreteModelPureL3Word *
          upperConcreteModelMixedWordL2bound R eps 3 slack d ^
            localWordLetterCount LocalExpansionLetter.L upperConcreteModelPureL3Word *
          upperConcreteModelMixedWordQ2bound R eps 3 slack d ^
            localWordLetterCount LocalExpansionLetter.Q upperConcreteModelPureL3Word := by
      rw [hAcount, hLcount, hQcount]
      simp [upperConcreteModelMixedWordL2bound, upperMixedWordL2bound,
        upperConcreteModelMixedWordL1bound]

/-- Scalar domination needed to replace the actual-model one-quadratic word
input by the checked local one-`Q` matrix estimate. -/
def UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps : ℝ) (k : ℕ)
    (Abound Q1bound : ℝ → ℕ → ℝ) : Prop :=
  ∀ slack : ℝ, 0 < slack →
    ∀ᶠ d in atTop,
      upperConcreteN d ^ (k - 1) *
          upperConcreteModelMixedWordAbound R slack d ^ (k - 1) *
          upperConcreteModelMixedWordQ1bound R eps k slack d ≤
        upperConcreteN d ^ (k - 1) *
          Abound slack d ^ (k - 1) * Q1bound slack d

/-- Scalar domination needed to replace the actual-model one-linear word input
by the checked local one-`L` matrix estimate. -/
def UpperConcreteModelOneLinearMixedWordEnvelopeDomination
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps : ℝ) (k : ℕ)
    (Abound L1bound : ℝ → ℕ → ℝ) : Prop :=
  ∀ slack : ℝ, 0 < slack →
    ∀ᶠ d in atTop,
      upperConcreteN d ^ (k - 1) *
          upperConcreteModelMixedWordAbound R slack d ^ (k - 1) *
          upperConcreteModelMixedWordL1bound R eps k slack d ≤
        upperConcreteN d ^ (k - 1) *
          Abound slack d ^ (k - 1) * L1bound slack d

/-- Scalar domination needed to replace the actual-model multi-defect word
input by the checked local multi-defect matrix estimate. -/
def UpperConcreteModelMultiDefectMixedWordEnvelopeDomination
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps : ℝ) (k : ℕ)
    (Abound L2bound Q2bound : ℝ → ℕ → ℝ) : Prop :=
  ∀ slack : ℝ, 0 < slack →
    ∀ᶠ d in atTop,
      ∀ w : Fin k → LocalExpansionLetter,
        localWordIsMixed w →
        ¬ localWordHasOneLinearDefect w →
        ¬ localWordHasOneQuadraticDefect w →
          upperConcreteN d ^ (k - 1) *
              upperConcreteModelMixedWordAbound R slack d ^
                localWordLetterCount LocalExpansionLetter.A w *
              upperConcreteModelMixedWordL2bound R eps k slack d ^
                localWordLetterCount LocalExpansionLetter.L w *
              upperConcreteModelMixedWordQ2bound R eps k slack d ^
                localWordLetterCount LocalExpansionLetter.Q w ≤
            upperConcreteN d ^ (k - 1) *
              Abound slack d ^
                localWordLetterCount LocalExpansionLetter.A w *
              L2bound slack d ^
                localWordLetterCount LocalExpansionLetter.L w *
              Q2bound slack d ^
                localWordLetterCount LocalExpansionLetter.Q w

/-- Close the actual-model one-linear mixed-word branch from the local matrix
estimate plus scalar envelope domination. -/
theorem UpperConcreteModelOneLinearMixedWordBound_of_envelopeDomination
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {Abound L1bound : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hDom :
      UpperConcreteModelOneLinearMixedWordEnvelopeDomination
        R eps k Abound L1bound) :
    UpperConcreteModelOneLinearMixedWordBound
      R eps k Abound L1bound := by
  intro slack hslack
  filter_upwards [eventually_gt_atTop 0, hDom slack hslack] with d hd hDom_d
  intro X Y hY hdist w hOneL
  have hNpos : 0 < upperConcreteN d := by
    unfold upperConcreteN
    exact PptFactorization.AppendixB.ConcreteModel.D_pos hd
  haveI :
      Nonempty (PptFactorization.AppendixB.ConcreteModel.LeftIndex d) :=
    ⟨⟨0, hd⟩⟩
  haveI :
      Nonempty (PptFactorization.AppendixB.ConcreteModel.RightIndex d) :=
    ⟨⟨0, hd⟩⟩
  have hM : 0 ≤ upperConcreteModelM R slack d := by
    unfold upperConcreteModelM upperConcreteM
    exact le_max_of_le_left (Real.sqrt_nonneg _)
  let a := upperSlackRadius (spikeRoot k eps) R.lam slack
  have hk_pos : 0 < k := by omega
  have ha : 0 ≤ a :=
    (upperSlackRadius_spike_choice hk_pos R.lam_pos hε slack hslack).1
  let hr : ℝ :=
    sharpSphericalRadius (upperConcreteN d) (spikeSpeed k d) a
  have hA_op :
      opNorm
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (localBackground
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            Y) ≤
        upperConcreteModelM R slack d / upperConcreteN d := by
    simpa [upperConcreteModelM] using
      backgroundTypicalSet_gammaOpNorm_bound
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d))
        (N := upperConcreteN d)
        (M :=
          upperConcreteM
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            slack d)
        (τ := upperCanonicalTau slack d)
        (mean :=
          upperConcreteMean
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            k d)
        (k := k) hY
  have hSampleOp :
      PptFactorization.HighProbabilityBounds.sampleOpNorm
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          Y ≤
        upperConcreteModelM R slack d / Real.sqrt (upperConcreteN d) := by
    simpa [upperConcreteModelM] using
      backgroundTypicalSet_sampleOpNorm_bound
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d))
        (N := upperConcreteN d)
        (M :=
          upperConcreteM
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            slack d)
        (τ := upperCanonicalTau slack d)
        (mean :=
          upperConcreteMean
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            k d)
        (k := k) hY
  have hL_frob :
      frobeniusNorm
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ :=
            BipIndex
              (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (PptFactorization.AppendixB.ConcreteModel.RightIndex d))
          (localLinear
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            Y (X - Y)) ≤
        upperMixedWordL1bound
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (upperConcreteN d) (upperConcreteModelM R slack d)
            (spikeSpeed k d) a /
          Real.sqrt
            (Fintype.card
              (BipIndex
                (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (PptFactorization.AppendixB.ConcreteModel.RightIndex d))) := by
    have hL :=
      localLinear_frobeniusNorm_bound_of_sampleOpNorm
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d))
        (X := X) (Y := Y)
        (N := upperConcreteN d) (M := upperConcreteModelM R slack d)
        (r := hr) hSampleOp (by simpa [hr, a] using hdist)
    have hcardpos :
        0 <
          (Fintype.card
            (BipIndex
              (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (PptFactorization.AppendixB.ConcreteModel.RightIndex d)) : ℝ) := by
      exact_mod_cast Fintype.card_pos
    calc
      frobeniusNorm
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ :=
            BipIndex
              (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (PptFactorization.AppendixB.ConcreteModel.RightIndex d))
          (localLinear
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            Y (X - Y)) ≤
          2 * (upperConcreteModelM R slack d / Real.sqrt (upperConcreteN d)) *
            hr := hL
      _ ≤
          upperMixedWordL1bound
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (upperConcreteN d) (upperConcreteModelM R slack d)
              (spikeSpeed k d) a /
            Real.sqrt
              (Fintype.card
                (BipIndex
                  (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (PptFactorization.AppendixB.ConcreteModel.RightIndex d))) := by
        have hsqrt_card_ne :
            Real.sqrt
                (Fintype.card
                  (BipIndex
                    (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (PptFactorization.AppendixB.ConcreteModel.RightIndex d)) : ℝ) ≠ 0 :=
          (Real.sqrt_pos.mpr hcardpos).ne'
        unfold upperMixedWordL1bound
        field_simp [hsqrt_card_ne]
        simp [hr]
  have hcore :=
    localWordScaledTraceTerm_oneLinear_le_envelope
      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
      (N := upperConcreteN d)
      (M := upperConcreteModelM R slack d)
      (a := a) (speed := spikeSpeed k d)
      (A :=
        localBackground
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          Y)
      (L :=
        localLinear
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          Y (X - Y))
      (Q :=
        localQuadratic
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          (X - Y))
      (w := w) hNpos hM hk3 hA_op hL_frob hOneL
  have hCanonical :
      |localWordScaledTraceTerm
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (upperConcreteN d)
          (localBackground
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            Y)
          (localLinear
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            Y (X - Y))
          (localQuadratic
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            (X - Y))
          w| ≤
        upperConcreteN d ^ (k - 1) *
          upperConcreteModelMixedWordAbound R slack d ^ (k - 1) *
          upperConcreteModelMixedWordL1bound R eps k slack d := by
    simpa [upperConcreteModelMixedWordAbound,
      upperConcreteModelMixedWordL1bound, upperMixedWordAbound,
      upperMixedWordL1bound, a, BipIndex, Fintype.card_prod] using hcore
  exact le_trans hCanonical hDom_d

/-- Close the actual-model one-quadratic mixed-word branch from the local
matrix estimate plus scalar envelope domination. -/
theorem UpperConcreteModelOneQuadraticMixedWordBound_of_envelopeDomination
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {Abound Q1bound : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hDom :
      UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination
        R eps k Abound Q1bound) :
    UpperConcreteModelOneQuadraticMixedWordBound
      R eps k Abound Q1bound := by
  intro slack hslack
  filter_upwards [eventually_gt_atTop 0, hDom slack hslack] with d hd hDom_d
  intro X Y hY hdist w hOneQ
  have hNpos : 0 < upperConcreteN d := by
    unfold upperConcreteN
    exact PptFactorization.AppendixB.ConcreteModel.D_pos hd
  haveI :
      Nonempty (PptFactorization.AppendixB.ConcreteModel.LeftIndex d) :=
    ⟨⟨0, hd⟩⟩
  haveI :
      Nonempty (PptFactorization.AppendixB.ConcreteModel.RightIndex d) :=
    ⟨⟨0, hd⟩⟩
  have hM : 0 ≤ upperConcreteModelM R slack d := by
    unfold upperConcreteModelM upperConcreteM
    exact le_max_of_le_left (Real.sqrt_nonneg _)
  let a := upperSlackRadius (spikeRoot k eps) R.lam slack
  have hk_pos : 0 < k := by omega
  have ha : 0 ≤ a :=
    (upperSlackRadius_spike_choice hk_pos R.lam_pos hε slack hslack).1
  let hr : ℝ :=
    sharpSphericalRadius (upperConcreteN d) (spikeSpeed k d) a
  have hA_op :
      opNorm
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (localBackground
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            Y) ≤
        upperConcreteModelM R slack d / upperConcreteN d := by
    simpa [upperConcreteModelM] using
      backgroundTypicalSet_gammaOpNorm_bound
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d))
        (N := upperConcreteN d)
        (M :=
          upperConcreteM
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            slack d)
        (τ := upperCanonicalTau slack d)
        (mean :=
          upperConcreteMean
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            k d)
        (k := k) hY
  have hQ_frob :
      frobeniusNorm
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ :=
            BipIndex
              (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (PptFactorization.AppendixB.ConcreteModel.RightIndex d))
          (localQuadratic
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            (X - Y)) ≤
        upperMixedWordQ1bound
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (upperConcreteN d) (spikeSpeed k d) a /
          Real.sqrt
            (Fintype.card
              (BipIndex
                (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (PptFactorization.AppendixB.ConcreteModel.RightIndex d))) := by
    have hQ :=
      localQuadratic_frobeniusNorm_bound_of_radius
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d))
        (X := X) (Y := Y) (r := hr)
        (by simpa [hr, a] using hdist)
    have hcardpos :
        0 <
          (Fintype.card
            (BipIndex
              (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (PptFactorization.AppendixB.ConcreteModel.RightIndex d)) : ℝ) := by
      exact_mod_cast Fintype.card_pos
    unfold upperMixedWordQ1bound
    rw [div_eq_mul_inv]
    field_simp [hcardpos.ne']
    exact hQ
  have hNoL :=
    localWordHasOneQuadraticDefect_noLinear hOneQ
  have hterm_eq :
      localWordScaledTraceTerm
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (upperConcreteN d)
          (localBackground
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            Y)
          (localLinear
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            Y (X - Y))
          (localQuadratic
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            (X - Y))
          w =
        localWordScaledTraceTerm
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (upperConcreteN d)
          (localBackground
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            Y)
          0
          (localQuadratic
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            (X - Y))
          w :=
    localWordScaledTraceTerm_eq_of_noLinear
      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
      (N := upperConcreteN d)
      (A :=
        localBackground
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          Y)
      (L :=
        localLinear
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          Y (X - Y))
      (Q :=
        localQuadratic
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          (X - Y))
      hNoL
  have hcore :=
    localWordScaledTraceTerm_oneQuadratic_le_envelope
      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
      (N := upperConcreteN d)
      (M := upperConcreteModelM R slack d)
      (a := a) (speed := spikeSpeed k d)
      (A :=
        localBackground
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          Y)
      (L := 0)
      (Q :=
        localQuadratic
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          (X - Y))
      (w := w) hNpos hM hk3 hA_op hQ_frob hOneQ
  have hCanonical :
      |localWordScaledTraceTerm
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (upperConcreteN d)
          (localBackground
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            Y)
          (localLinear
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            Y (X - Y))
          (localQuadratic
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            (X - Y))
          w| ≤
        upperConcreteN d ^ (k - 1) *
          upperConcreteModelMixedWordAbound R slack d ^ (k - 1) *
          upperConcreteModelMixedWordQ1bound R eps k slack d := by
    rw [hterm_eq]
    simpa [upperConcreteModelMixedWordAbound,
      upperConcreteModelMixedWordQ1bound, upperMixedWordAbound,
      upperMixedWordQ1bound, a, BipIndex, Fintype.card_prod] using hcore
  exact le_trans hCanonical hDom_d

/-- Close the actual-model multi-defect mixed-word branch from the local
matrix estimate plus scalar envelope domination. -/
theorem UpperConcreteModelMultiDefectMixedWordBound_of_envelopeDomination
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {Abound L2bound Q2bound : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hDom :
      UpperConcreteModelMultiDefectMixedWordEnvelopeDomination
        R eps k Abound L2bound Q2bound) :
    UpperConcreteModelMultiDefectMixedWordBound
      R eps k Abound L2bound Q2bound := by
  intro slack hslack
  filter_upwards [eventually_gt_atTop 0, hDom slack hslack] with d hd hDom_d
  intro X Y hY hdist w hmix hNotOneL hNotOneQ
  have hNpos : 0 < upperConcreteN d := by
    unfold upperConcreteN
    exact PptFactorization.AppendixB.ConcreteModel.D_pos hd
  haveI :
      Nonempty (PptFactorization.AppendixB.ConcreteModel.LeftIndex d) :=
    ⟨⟨0, hd⟩⟩
  haveI :
      Nonempty (PptFactorization.AppendixB.ConcreteModel.RightIndex d) :=
    ⟨⟨0, hd⟩⟩
  have hM : 0 ≤ upperConcreteModelM R slack d := by
    unfold upperConcreteModelM upperConcreteM
    exact le_max_of_le_left (Real.sqrt_nonneg _)
  let a := upperSlackRadius (spikeRoot k eps) R.lam slack
  have hk_pos : 0 < k := by omega
  have ha : 0 ≤ a :=
    (upperSlackRadius_spike_choice hk_pos R.lam_pos hε slack hslack).1
  let hr : ℝ :=
    sharpSphericalRadius (upperConcreteN d) (spikeSpeed k d) a
  have hA_op :
      opNorm
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (localBackground
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            Y) ≤
        upperConcreteModelM R slack d / upperConcreteN d := by
    simpa [upperConcreteModelM] using
      backgroundTypicalSet_gammaOpNorm_bound
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d))
        (N := upperConcreteN d)
        (M :=
          upperConcreteM
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            slack d)
        (τ := upperCanonicalTau slack d)
        (mean :=
          upperConcreteMean
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            k d)
        (k := k) hY
  have hSampleOp :
      PptFactorization.HighProbabilityBounds.sampleOpNorm
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          Y ≤
        upperConcreteModelM R slack d / Real.sqrt (upperConcreteN d) := by
    simpa [upperConcreteModelM] using
      backgroundTypicalSet_sampleOpNorm_bound
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d))
        (N := upperConcreteN d)
        (M :=
          upperConcreteM
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            slack d)
        (τ := upperCanonicalTau slack d)
        (mean :=
          upperConcreteMean
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            k d)
        (k := k) hY
  have hL_frob :
      frobeniusNorm
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ :=
            BipIndex
              (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (PptFactorization.AppendixB.ConcreteModel.RightIndex d))
          (localLinear
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            Y (X - Y)) ≤
        upperMixedWordL2bound
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (upperConcreteN d) (upperConcreteModelM R slack d)
            (spikeSpeed k d) a := by
    have hL :=
      localLinear_frobeniusNorm_bound_of_sampleOpNorm
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d))
        (X := X) (Y := Y)
        (N := upperConcreteN d) (M := upperConcreteModelM R slack d)
        (r := hr) hSampleOp (by simpa [hr, a] using hdist)
    calc
      frobeniusNorm
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ :=
            BipIndex
              (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (PptFactorization.AppendixB.ConcreteModel.RightIndex d))
          (localLinear
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            Y (X - Y)) ≤
          2 * (upperConcreteModelM R slack d / Real.sqrt (upperConcreteN d)) *
            hr := hL
      _ ≤
          upperMixedWordL2bound
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (upperConcreteN d) (upperConcreteModelM R slack d)
              (spikeSpeed k d) a := by
        have hcard1 :
            (1 : ℝ) ≤
              Real.sqrt
                (Fintype.card
                  (BipIndex
                    (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (PptFactorization.AppendixB.ConcreteModel.RightIndex d))) := by
          rw [← Real.sqrt_one]
          apply Real.sqrt_le_sqrt
          exact_mod_cast
            Nat.one_le_iff_ne_zero.mpr
              (Fintype.card_pos
                (α :=
                  BipIndex
                    (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (PptFactorization.AppendixB.ConcreteModel.RightIndex d))).ne'
        have hstep_nonneg :
            0 ≤
              2 * (upperConcreteModelM R slack d / Real.sqrt (upperConcreteN d)) *
                hr := by
          simp [hr, sharpSphericalRadius]
          positivity
        calc
          2 * (upperConcreteModelM R slack d / Real.sqrt (upperConcreteN d)) *
              hr ≤
            Real.sqrt
                (Fintype.card
                  (BipIndex
                    (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (PptFactorization.AppendixB.ConcreteModel.RightIndex d))) *
              (2 * (upperConcreteModelM R slack d / Real.sqrt (upperConcreteN d)) *
                hr) := by
            exact le_mul_of_one_le_left hstep_nonneg hcard1
          _ =
            upperMixedWordL2bound
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (upperConcreteN d) (upperConcreteModelM R slack d)
                (spikeSpeed k d) a := by
            simp [upperMixedWordL2bound, upperMixedWordL1bound, hr,
              sharpSphericalRadius]
  have hQ_frob :
      frobeniusNorm
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ :=
            BipIndex
              (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (PptFactorization.AppendixB.ConcreteModel.RightIndex d))
          (localQuadratic
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            (X - Y)) ≤
        upperMixedWordQ1bound
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (upperConcreteN d) (spikeSpeed k d) a /
          Real.sqrt
            (Fintype.card
              (BipIndex
                (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (PptFactorization.AppendixB.ConcreteModel.RightIndex d))) := by
    have hQ :=
      localQuadratic_frobeniusNorm_bound_of_radius
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d))
        (X := X) (Y := Y) (r := hr)
        (by simpa [hr, a] using hdist)
    have hcardpos :
        0 <
          (Fintype.card
            (BipIndex
              (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (PptFactorization.AppendixB.ConcreteModel.RightIndex d)) : ℝ) := by
      exact_mod_cast Fintype.card_pos
    unfold upperMixedWordQ1bound
    rw [div_eq_mul_inv]
    field_simp [hcardpos.ne']
    exact hQ
  have hcore :=
    localWordScaledTraceTerm_multiDefect_le_envelope
      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
      (N := upperConcreteN d)
      (M := upperConcreteModelM R slack d)
      (a := a) (speed := spikeSpeed k d)
      (A :=
        localBackground
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          Y)
      (L :=
        localLinear
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          Y (X - Y))
      (Q :=
        localQuadratic
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          (X - Y))
      (w := w) hNpos hM ha hA_op hL_frob hQ_frob hmix hNotOneL hNotOneQ
  have hCanonical :
      |localWordScaledTraceTerm
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (upperConcreteN d)
          (localBackground
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            Y)
          (localLinear
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            Y (X - Y))
          (localQuadratic
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            (X - Y))
          w| ≤
        upperConcreteN d ^ (k - 1) *
          upperConcreteModelMixedWordAbound R slack d ^
            localWordLetterCount LocalExpansionLetter.A w *
          upperConcreteModelMixedWordL2bound R eps k slack d ^
            localWordLetterCount LocalExpansionLetter.L w *
          upperConcreteModelMixedWordQ2bound R eps k slack d ^
            localWordLetterCount LocalExpansionLetter.Q w := by
    simpa [upperConcreteModelMixedWordAbound,
      upperConcreteModelMixedWordL2bound, upperConcreteModelMixedWordQ2bound,
      upperMixedWordAbound, upperMixedWordL2bound, upperMixedWordQ2bound,
      upperMixedWordQ1bound, a, BipIndex, Fintype.card_prod] using hcore
  exact le_trans hCanonical (hDom_d w hmix hNotOneL hNotOneQ)

/-- Scalar mixed-word envelope limits for the actual upper concrete family. -/
def UpperConcreteModelMixedTermLimit
    (k : ℕ)
    (Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ) : Prop :=
  ∀ slack : ℝ, 0 < slack →
    ∀ w : Fin k → LocalExpansionLetter,
      localWordIsMixed w →
        Tendsto
          (fun d =>
            localExpansionMixedWordEnvelopeTerm
              (upperConcreteN d) (Abound slack d) (L2bound slack d)
              (L1bound slack d) (Q2bound slack d) (Q1bound slack d) k w)
          atTop (nhds 0)

/-- Assemble the actual-model mixed-remainder supplier from model-level
mixed-word bounds and scalar term limits.

No probability or isoperimetry enters this lemma.  It is only the deterministic
finite-word summation step: the mixed remainder is the sum of mixed local words,
each word is bounded by its scalar envelope, and the finite envelope sum is
eventually smaller than any positive tolerance. -/
theorem UpperConcreteModelMixedRemainderBound_of_modelMixedWordBound_and_termLimit
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hk : 1 ≤ k)
    (hWord :
      UpperConcreteModelMixedWordBound
        R eps k Abound L2bound L1bound Q2bound Q1bound)
    (hTerm :
      UpperConcreteModelMixedTermLimit
        k Abound L2bound L1bound Q2bound Q1bound) :
    UpperConcreteModelMixedRemainderBound R eps k := by
  intro slack hslack η hη
  have hWordSmall :
      ∀ w : Fin k → LocalExpansionLetter,
        localWordIsMixed w →
          ∀ η' : ℝ, 0 < η' →
            ∀ᶠ d in atTop,
              localExpansionMixedWordEnvelopeTerm
                (upperConcreteN d) (Abound slack d) (L2bound slack d)
                (L1bound slack d) (Q2bound slack d) (Q1bound slack d) k w ≤ η' := by
    intro w hw η' hη'
    have hIio : Set.Iio η' ∈ nhds (0 : ℝ) := Iio_mem_nhds hη'
    filter_upwards [(hTerm slack hslack w hw).eventually hIio] with d hd
    exact le_of_lt hd
  have hSmall :
      ∀ᶠ d in atTop,
        localExpansionMixedWordEnvelope
            (upperConcreteN d) (Abound slack d) (L2bound slack d)
            (L1bound slack d) (Q2bound slack d) (Q1bound slack d) k ≤ η :=
    localExpansionMixedWordEnvelope_eventual_small
      (Nseq := upperConcreteN)
      (Abound := fun d => Abound slack d)
      (L2bound := fun d => L2bound slack d)
      (L1bound := fun d => L1bound slack d)
      (Q2bound := fun d => Q2bound slack d)
      (Q1bound := fun d => Q1bound slack d)
      (k := k) hWordSmall η hη
  filter_upwards [hWord slack hslack, hSmall] with d hWord_d hSmall_d
  intro X Y hY hdist
  have hEnvelope :
      |localExpansionMixedRemainder
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (upperConcreteN d) k
          (localBackground
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            Y)
          (localLinear
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            Y (X - Y))
          (localQuadratic
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            (X - Y))| ≤
        localExpansionMixedWordEnvelope
          (upperConcreteN d) (Abound slack d) (L2bound slack d)
          (L1bound slack d) (Q2bound slack d) (Q1bound slack d) k := by
    have h :=
      localExpansionMixedRemainder_abs_le_of_wordBounds
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (N := upperConcreteN d) (k := k)
        (A := localBackground
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          Y)
        (L := localLinear
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          Y (X - Y))
        (Q := localQuadratic
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          (X - Y))
        hk
        (bound := fun w =>
          localExpansionMixedWordEnvelopeTerm
            (upperConcreteN d) (Abound slack d) (L2bound slack d)
            (L1bound slack d) (Q2bound slack d) (Q1bound slack d) k w)
        (by
          intro w hw
          exact hWord_d hY hdist w hw)
    simpa [localExpansionMixedWordEnvelope, localMixedWordFilteredSum] using h
  exact le_trans hEnvelope hSmall_d

/-- Exponential envelope for full-model background moment deviation. -/
noncomputable def upperConcreteModelExponentialMomentEnvelope
    (c : ℝ) (_slack : ℝ) (d : ℕ) : ℝ :=
  Real.exp (-(c * (d : ℝ) ^ 2))

/-- Full-model exponential background moment deviation concentration.

For the true spherical model with matrix dimension `d` and sample count
`R.sample d`, every fixed positive slack has the closed background moment
deviation probability bounded eventually by `exp (-c d^2)`, for some positive
constant `c`. -/
def UpperConcreteModelMomentExponentialDeviationSetBound
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (c : ℝ) (k : ℕ) : Prop :=
  0 < c ∧
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        (PptFactorization.AppendixB.sphericalModelMeasure
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))).real
          (backgroundMomentDeviationSet
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            (upperConcreteN d)
            (upperCanonicalTau slack d)
            (upperConcreteMean
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              k d)
            k) ≤
          upperConcreteModelExponentialMomentEnvelope c slack d

/-- The exponential model-moment envelope tends to zero for every fixed
positive exponent. -/
theorem upperConcreteModelExponentialMomentEnvelope_tendsto_zero
    {c : ℝ} (hc : 0 < c) :
    ∀ slack : ℝ, 0 < slack →
      Tendsto (upperConcreteModelExponentialMomentEnvelope c slack)
        atTop (nhds 0) := by
  intro slack _hslack
  have hsq :
      Tendsto (fun d : ℕ => (d : ℝ) ^ 2) atTop atTop := by
    have h :
        Tendsto (fun d : ℕ => (d : ℝ) ^ (2 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2)).comp
        tendsto_natCast_atTop_atTop
    simpa [Real.rpow_natCast] using h
  have hbot :
      Tendsto (fun d : ℕ => (-c) * ((d : ℝ) ^ 2)) atTop atBot :=
    Filter.Tendsto.const_mul_atTop_of_neg (by linarith) hsq
  simpa [upperConcreteModelExponentialMomentEnvelope, neg_mul] using
    (Real.tendsto_exp_atBot.comp hbot)

/-- The full-model exponential deviation input really is a concentration
statement: for every fixed positive slack, the corresponding closed
background-moment deviation probability tends to zero.

This is only a consequence of the input, not a proof of the input.  It records
that the upper concentration leaf is stronger than mere eventual smallness: it
asks for a uniform-in-slack exponential envelope `exp (-c d²)` with `c > 0`. -/
theorem UpperConcreteModelMomentExponentialDeviationSetBound.tendsto_zero
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {c : ℝ} {k : ℕ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k) :
    ∀ slack : ℝ, 0 < slack →
      Tendsto
        (fun d : ℕ =>
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundMomentDeviationSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                k d)
              k)) atTop (nhds 0) := by
  intro slack hslack
  refine squeeze_zero' ?_ (hExp.2 slack hslack) ?_
  · exact Eventually.of_forall (fun _d => by positivity)
  · exact upperConcreteModelExponentialMomentEnvelope_tendsto_zero
      hExp.1 slack hslack

/-- Existential version of the upper full-model concentration consequence.

The sharp upper endpoint only asks for some positive exponential rate `c`.
Once such a rate exists, the centered full-model background-moment deviation
event still has probability `o(1)` for every fixed positive slack. -/
theorem UpperConcreteModelMomentExponentialDeviationSetBound.exists_tendsto_zero
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ}
    (hExp :
      ∃ c : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R c k) :
    ∀ slack : ℝ, 0 < slack →
      Tendsto
        (fun d : ℕ =>
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundMomentDeviationSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                k d)
              k)) atTop (nhds 0) := by
  rcases hExp with ⟨c, hc⟩
  exact UpperConcreteModelMomentExponentialDeviationSetBound.tendsto_zero
    R hc

/-- Convert the actual-family exponential deviation-set supplier into the
strict bad-set bound consumed by the half-mass constructor.

The only mathematical content is monotonicity: the strict bad set is contained
in the corresponding closed absolute-deviation set. -/
theorem upperConcreteModel_backgroundMomentBadSetBound_of_exponentialDeviationSetBound
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {c : ℝ} {k : ℕ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k) :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        (PptFactorization.AppendixB.sphericalModelMeasure
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))).real
          (backgroundMomentBadSet
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            (upperConcreteN d)
            (upperCanonicalTau slack d)
            (upperConcreteMean
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              k d)
            k) ≤
          upperConcreteModelExponentialMomentEnvelope c slack d := by
  intro slack hslack
  filter_upwards [hExp.2 slack hslack] with d hdev
  haveI :
      IsProbabilityMeasure
        (PptFactorization.AppendixB.sphericalModelMeasure
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))) :=
    PptFactorization.AppendixB.sphericalModelMeasure_isProbabilityMeasure
      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
        (R.sample d))
  exact
    (measureReal_backgroundMomentBadSet_le_backgroundMomentDeviationSet
      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
        (R.sample d))
      (μ :=
        PptFactorization.AppendixB.sphericalModelMeasure
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d)))
      (N := upperConcreteN d)
      (τ := upperCanonicalTau slack d)
      (mean :=
        upperConcreteMean
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          k d)
      (k := k)).trans hdev

/-- Existential exponential concentration makes the strict full-model moment bad
set negligible.

The endpoint-facing concentration input is stated for the closed absolute
deviation event.  This consequence records the exact typical-set use: the strict
moment bad event, one of the three bad background events, has probability
`o(1)` for every fixed positive slack. -/
theorem UpperConcreteModelMomentExponentialDeviationSetBound.exists_badSet_tendsto_zero
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ}
    (hExp :
      ∃ c : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R c k) :
    ∀ slack : ℝ, 0 < slack →
      Tendsto
        (fun d : ℕ =>
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundMomentBadSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                k d)
              k)) atTop (nhds 0) := by
  rcases hExp with ⟨c, hc⟩
  intro slack hslack
  refine squeeze_zero' ?_
    (upperConcreteModel_backgroundMomentBadSetBound_of_exponentialDeviationSetBound
      R hc slack hslack) ?_
  · exact Eventually.of_forall (fun _d => by positivity)
  · exact upperConcreteModelExponentialMomentEnvelope_tendsto_zero
      hc.1 slack hslack

/-- Local-expansion supplier for the full-model exponential background moment
concentration proposition.

This theorem keeps only the real analytic inputs on the surface:
half-mass of the chosen background typical set, pointwise local-expansion
control on a sharp spherical neighborhood, the deep geometric input
`FullSphericalIsoperimetry`, and a scalar comparison from the sharp spherical
tail to the requested envelope `exp (-c d^2)`. -/
theorem upperConcreteModelMomentExponentialDeviationSetBound_of_localExpansion_envelope
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {c : ℝ} {k : ℕ}
    {aSlack etaSlack : ℝ → ℝ}
    {M τ : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k) (hc : 0 < c)
    (hFullIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (ha : ∀ slack : ℝ, 0 < slack → 0 ≤ aSlack slack)
    (hEta : ∀ slack : ℝ, 0 < slack → 0 < etaSlack slack)
    (hK_half :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          1 / 2 ≤
            (PptFactorization.AppendixB.sphericalModelMeasure
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))).real
              (backgroundTypicalSet
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  k d)
                k))
    (hMixed :
      ∀ slack : ℝ, 0 < slack →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop,
            ∀ ⦃X Y :
                SampleMatrix
                  (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))⦄,
              Y ∈ backgroundTypicalSet
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  (upperConcreteN d) (M slack d) (τ slack d)
                  (upperConcreteMean
                    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                    (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                      (R.sample d))
                    k d)
                  k →
              frobeniusNorm
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  (X - Y) ≤
                sharpSphericalRadius
                  (upperConcreteN d) (spikeSpeed k d) (aSlack slack) →
              |localExpansionMixedRemainder
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (upperConcreteN d) k
                  (localBackground
                    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                    (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                      (R.sample d))
                    Y)
                  (localLinear
                    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                    (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                      (R.sample d))
                    Y (X - Y))
                  (localQuadratic
                    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                    (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                      (R.sample d))
                    (X - Y))| ≤ η)
    (hBudget :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          aSlack slack ^ k + etaSlack slack + τ slack d <
            upperCanonicalTau slack d)
    (hEnvelope :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          Real.exp
              (-(((upperConcreteRealDim R d - 1) *
                  sharpSphericalRadiusSq
                    (upperConcreteN d) (spikeSpeed k d) (aSlack slack)) /
                2)) ≤
            upperConcreteModelExponentialMomentEnvelope c slack d) :
    UpperConcreteModelMomentExponentialDeviationSetBound R c k := by
  refine ⟨hc, ?_⟩
  intro slack hslack
  let hk : 0 < k := upper_hk_of_hk3 hk3
  have heta := hEta slack hslack
  filter_upwards
      [eventually_gt_atTop 0, R.sample_pos_eventually,
        upper_hN_nonneg_concreteDimension,
        upper_hN_ne_concreteDimension,
        (spikeSpeed_pos_eventually hk).mono (fun _ h => le_of_lt h),
        upper_hSpeedPow_concreteDimension hk,
        hK_half slack hslack,
        hMixed slack hslack (etaSlack slack) heta,
        hBudget slack hslack,
        hEnvelope slack hslack]
    with d hd hs hN_nonneg_d hN_ne_d hspeed_nonneg_d hSpeedPow_d
      hK_half_d hMixed_d hBudget_d hEnvelope_d
  have hIso_d :
      SharpSphericalIsoperimetry
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d))
        (PptFactorization.AppendixB.sphericalModelMeasure
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d)))
        (upperConcreteRealDim R d) :=
    upper_hIso_concreteModel_pointwise_of_fullSphericalIsoperimetry
      R hd hs hFullIso
  have hTail :=
    backgroundMomentDeviation_probability_le_sharpIso_of_localExpansion
      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex (R.sample d))
      (μ :=
        PptFactorization.AppendixB.sphericalModelMeasure
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d)))
      (realDim := upperConcreteRealDim R d)
      (N := upperConcreteN d)
      (speed := spikeSpeed k d)
      (a := aSlack slack)
      (M := M slack d)
      (τ := τ slack d)
      (mean :=
        upperConcreteMean
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          k d)
      (eps := upperCanonicalTau slack d)
      (η := etaSlack slack)
      (k := k)
      hIso_d hk3 (ha slack hslack) hN_nonneg_d hN_ne_d
      hspeed_nonneg_d hSpeedPow_d
      (measurableSet_backgroundTypicalSet
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d))
        (upperConcreteN d) (M slack d) (τ slack d)
        (upperConcreteMean
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          k d)
        k)
      hK_half_d
      (by
        intro X Y hY hdist
        exact hMixed_d hY hdist)
      hBudget_d
  exact hTail.trans hEnvelope_d

/-- Local-expansion supplier for the full-model moment concentration using the
canonical actual-model mixed-remainder estimate on a smaller moment-typical
set.

Compared with `upperConcreteModelMomentExponentialDeviationSetBound_of_localExpansion_envelope`,
the theorem no longer asks for a raw mixed-remainder bound on the inner
typical set.  It asks for the canonical mixed-remainder proposition and the
scalar inclusion `τ slack d ≤ upperCanonicalTau slack d`; the inclusion of
typical sets supplies the transport. -/
theorem upperConcreteModelMomentExponentialDeviationSetBound_of_localExpansion_canonicalMixedRemainder_innerTau
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps c : ℝ} {k : ℕ}
    {etaSlack : ℝ → ℝ}
    {τ : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps) (hc : 0 < c)
    (hFullIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (hEta : ∀ slack : ℝ, 0 < slack → 0 < etaSlack slack)
    (hK_half :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          1 / 2 ≤
            (PptFactorization.AppendixB.sphericalModelMeasure
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))).real
              (backgroundTypicalSet
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                (upperConcreteN d)
                (upperConcreteM
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  slack d)
                (τ slack d)
                (upperConcreteMean
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  k d)
                k))
    (hMixed : UpperConcreteModelMixedRemainderBound R eps k)
    (hτ :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop, τ slack d ≤ upperCanonicalTau slack d)
    (hBudget :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          upperSlackRadius (spikeRoot k eps) R.lam slack ^ k +
              etaSlack slack + τ slack d <
            upperCanonicalTau slack d)
    (hEnvelope :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          Real.exp
              (-(((upperConcreteRealDim R d - 1) *
                  sharpSphericalRadiusSq
                    (upperConcreteN d) (spikeSpeed k d)
                    (upperSlackRadius (spikeRoot k eps) R.lam slack)) /
                2)) ≤
            upperConcreteModelExponentialMomentEnvelope c slack d) :
    UpperConcreteModelMomentExponentialDeviationSetBound R c k := by
  refine
    upperConcreteModelMomentExponentialDeviationSetBound_of_localExpansion_envelope
      (R := R) (c := c) (k := k)
      (aSlack := fun slack => upperSlackRadius (spikeRoot k eps) R.lam slack)
      (M := fun slack d =>
        upperConcreteM
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          slack d)
      (τ := τ)
      hk3 hc hFullIso ?_ hEta hK_half ?_ hBudget hEnvelope
  · intro slack hslack
    exact (upperSlackRadius_spike_choice
      (upper_hk_of_hk3 hk3) R.lam_pos hε slack hslack).1
  · exact UpperConcreteModelMixedRemainderBound.of_tau_le_canonical R hMixed hτ

/-- The current local-expansion hypothesis package for canonical upper moment
deviations is scalar-inconsistent.

For fixed positive slack, `upperCanonicalTau slack d = slack / d` tends to
zero.  If the inner typical set has mass at least one half while
`aSlack^k + etaSlack + τ < upperCanonicalTau`, with `aSlack ≥ 0` and
`etaSlack > 0`, then eventually `τ < 0`.  But a typical set with negative
moment tolerance is empty, contradicting the half-mass hypothesis.

This no-go theorem keeps the proof audit honest: the upper exponential moment
input cannot be closed by this fixed-in-slack local-expansion package without
changing the scalar budget structure. -/
theorem upperConcreteModel_localExpansionCanonicalTauBudget_halfMass_impossible
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ}
    {aSlack etaSlack : ℝ → ℝ}
    {M τ : ℝ → ℕ → ℝ}
    (ha : ∀ slack : ℝ, 0 < slack → 0 ≤ aSlack slack)
    (hEta : ∀ slack : ℝ, 0 < slack → 0 < etaSlack slack)
    (hK_half :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          1 / 2 ≤
            (PptFactorization.AppendixB.sphericalModelMeasure
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))).real
              (backgroundTypicalSet
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  k d)
                k))
    (hBudget :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          aSlack slack ^ k + etaSlack slack + τ slack d <
            upperCanonicalTau slack d) :
    False := by
  have hslack : (0 : ℝ) < 1 := by norm_num
  have heta : 0 < etaSlack 1 := hEta 1 hslack
  have hTauSmall :
      ∀ᶠ d : ℕ in atTop,
        upperCanonicalTau 1 d < etaSlack 1 / 2 := by
    exact
      (upper_hTau_canonical 1 hslack).eventually
        (eventually_lt_nhds (by linarith))
  have hfalse : ∀ᶠ _d : ℕ in atTop, False := by
    filter_upwards [hTauSmall, hK_half 1 hslack, hBudget 1 hslack]
      with d hTauSmall_d hK_half_d hBudget_d
    have ha_pow_nonneg : 0 ≤ aSlack 1 ^ k :=
      pow_nonneg (ha 1 hslack) k
    have hτ_neg : τ 1 d < 0 := by
      nlinarith
    let μ :=
      PptFactorization.AppendixB.sphericalModelMeasure
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d))
    let K :=
      backgroundTypicalSet
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d))
        (upperConcreteN d) (M 1 d) (τ 1 d)
        (upperConcreteMean
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          k d)
        k
    have hK_empty : K = ∅ := by
      ext Y
      constructor
      · intro hY
        exfalso
        have hmoment :
            |backgroundMomentValue
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                (upperConcreteN d) k Y -
              upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                k d| ≤ τ 1 d := hY.1
        have hnonneg :
            0 ≤
              |backgroundMomentValue
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  (upperConcreteN d) k Y -
                upperConcreteMean
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  k d| := abs_nonneg _
        linarith
      · intro hY
        cases hY
    have hmeasure : μ.real K = 0 := by
      simp [K, hK_empty]
    have hK_half' : 1 / 2 ≤ μ.real K := by
      simpa [μ, K] using hK_half_d
    linarith
  simp only [Filter.Eventually, Set.setOf_false] at hfalse
  have hbot : (∅ : Set ℕ) ∈ (atTop : Filter ℕ) := hfalse
  have hne : (atTop : Filter ℕ).NeBot := inferInstance
  exact hne.ne ((Filter.empty_mem_iff_bot).mp hbot)

/-- Fixed-type local-expansion supplier for the isolated moment block in raw
explicit scale form.

This is the fixed-type replay analogue of
`upperConcreteModelMomentExponentialDeviationSetBound_of_localExpansion_envelope`.
It packages the geometric/local-expansion argument into the isolated moment
proposition with envelope `C(slack) / (2 * D(d)^2)`.  The public canonical
wrapper appears later, once `upperConcreteMomentBoundScale` is defined. -/
theorem upperConcreteMomentBadSetBound_of_localExpansion_envelope_raw
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {C : ℝ → ℝ} {k : ℕ}
    {aSlack etaSlack : ℝ → ℝ}
    {M τ : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k)
    (hFullIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (ha : ∀ slack : ℝ, 0 < slack → 0 ≤ aSlack slack)
    (hK_half :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          1 / 2 ≤
            (upperConcreteSphericalMu (p := p) (q := q) (σ := σ) d).real
              (backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k))
    (hMixed :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y : SampleMatrix p q σ⦄,
            Y ∈ backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k →
            frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed k d) (aSlack slack) →
            |localExpansionMixedRemainder
                (p := p) (q := q) (upperConcreteN d) k
                (localBackground (p := p) (q := q) (σ := σ) Y)
                (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))| ≤
              etaSlack slack)
    (hBudget :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          aSlack slack ^ k + etaSlack slack + τ slack d <
            upperCanonicalTau slack d)
    (hEnvelope :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          Real.exp
              (-(((upperConcreteRealDim R d - 1) *
                  sharpSphericalRadiusSq
                    (upperConcreteN d) (spikeSpeed k d) (aSlack slack)) /
                2)) ≤
            C slack / (2 * (PptFactorization.AppendixB.ConcreteModel.D d) ^ 2)) :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        (PptFactorization.AppendixB.sphericalModelMeasure
          (p := p) (q := q) (σ := σ)).real
          (backgroundMomentBadSet
            (p := p) (q := q) (σ := σ)
            (upperConcreteN d)
            (upperCanonicalTau slack d)
            (upperConcreteMean (p := p) (q := q) (σ := σ) k d)
            k) ≤
          C slack / (2 * (PptFactorization.AppendixB.ConcreteModel.D d) ^ 2) := by
  intro slack hslack
  let hk : 0 < k := upper_hk_of_hk3 hk3
  have hIso :=
    upper_hIso_concrete_sequences_of_fullSphericalIsoperimetry
      (p := p) (q := q) (σ := σ) R hFullIso hIsoRealDim
  have hK_meas :=
    upper_hK_meas_backgroundTypicalSet
      (p := p) (q := q) (σ := σ)
      (N := upperConcreteN) (M := M) (τ := τ)
      (mean := fun _ d =>
        upperConcreteMean (p := p) (q := q) (σ := σ) k d)
      (k := k) slack hslack
  filter_upwards
      [hIso,
        upper_hN_nonneg_concreteDimension,
        upper_hN_ne_concreteDimension,
        (spikeSpeed_pos_eventually hk).mono (fun _ h => le_of_lt h),
        upper_hSpeedPow_concreteDimension hk,
        hK_meas,
        hK_half slack hslack,
        hMixed slack hslack,
        hBudget slack hslack,
        hEnvelope slack hslack]
    with d hIso_d hN_nonneg_d hN_ne_d hspeed_nonneg_d hSpeedPow_d hK_meas_d
      hK_half_d hMixed_d hBudget_d hEnvelope_d
  haveI : IsProbabilityMeasure
      (upperConcreteSphericalMu (p := p) (q := q) (σ := σ) d) := by
    dsimp [upperConcreteSphericalMu]
    exact
      PptFactorization.AppendixB.sphericalModelMeasure_isProbabilityMeasure
        (p := p) (q := q) (σ := σ)
  have hTail :=
    backgroundMomentDeviation_probability_le_sharpIso_of_localExpansion
      (p := p) (q := q) (σ := σ)
      (μ := upperConcreteSphericalMu (p := p) (q := q) (σ := σ) d)
      (realDim := upperConcreteRealDim R d)
      (N := upperConcreteN d)
      (speed := spikeSpeed k d)
      (a := aSlack slack)
      (M := M slack d)
      (τ := τ slack d)
      (mean := upperConcreteMean (p := p) (q := q) (σ := σ) k d)
      (eps := upperCanonicalTau slack d)
      (η := etaSlack slack)
      (k := k)
      hIso_d hk3 (ha slack hslack) hN_nonneg_d hN_ne_d
      hspeed_nonneg_d hSpeedPow_d hK_meas_d hK_half_d
      (by
        intro X Y hY hdist
        exact hMixed_d hY hdist)
      hBudget_d
  have hmono :
      (upperConcreteSphericalMu (p := p) (q := q) (σ := σ) d).real
          (backgroundMomentBadSet
            (p := p) (q := q) (σ := σ)
            (upperConcreteN d)
            (upperCanonicalTau slack d)
            (upperConcreteMean (p := p) (q := q) (σ := σ) k d)
            k) ≤
        (upperConcreteSphericalMu (p := p) (q := q) (σ := σ) d).real
          (backgroundMomentDeviationSet
            (p := p) (q := q) (σ := σ)
            (upperConcreteN d)
            (upperCanonicalTau slack d)
            (upperConcreteMean (p := p) (q := q) (σ := σ) k d)
            k) :=
    measureReal_backgroundMomentBadSet_le_backgroundMomentDeviationSet
      (p := p) (q := q) (σ := σ)
      (μ := upperConcreteSphericalMu (p := p) (q := q) (σ := σ) d)
      (N := upperConcreteN d)
      (τ := upperCanonicalTau slack d)
      (mean := upperConcreteMean (p := p) (q := q) (σ := σ) k d)
      (k := k)
  exact hmono.trans (hTail.trans hEnvelope_d)

/-- Next-layer concrete upper closure.

This theorem proceeds one level beyond
`upper_eventual_from_concrete_sequences_localExpansion_scalarLimits`:

* `hIso` is generated from `FullSphericalIsoperimetry` plus the explicit
  dimension-compatibility equality;
* `hK_half` is generated from concrete three-bad-set bounds and their
  union-bound budget;
* `hMixed` is generated from uniform mixed-word bounds and scalar term limits.

The remaining visible inputs are the genuinely hard facts in their proof-ready
forms: positivity of the concrete target probability, the geometric
isoperimetric theorem/dimension bridge, the probabilistic bad-set estimates,
and the deterministic mixed-word estimates. -/
theorem upper_eventual_from_concrete_sequences_of_fullIso_badBounds_mixedWords
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {bMoment bSample bGamma
      Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hp :
      ∀ᶠ d in atTop,
        0 < upperConcreteTargetProb
          (p := p) (q := q) (σ := σ) eps k d)
    (hFullIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hKBounds :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ConcreteSphericalBackgroundBadSetBounds
            (p := p) (q := q) (σ := σ)
            (upperConcreteN d)
            (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
            (upperCanonicalTau slack d)
            (upperConcreteMean (p := p) (q := q) (σ := σ) k d)
            (bMoment slack d) (bSample slack d) (bGamma slack d) k)
    (hBad :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          bMoment slack d + bSample slack d + bGamma slack d ≤ 1 / 2)
    (hWordBound :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y : SampleMatrix p q σ⦄,
            Y ∈ backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d)
                (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
                (upperCanonicalTau slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k →
            frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed k d)
                (upperSlackRadius (spikeRoot k eps) R.lam slack) →
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                |localWordScaledTraceTerm
                    (p := p) (q := q)
                    (upperConcreteN d)
                    (localBackground (p := p) (q := q) (σ := σ) Y)
                    (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                    (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
                    w| ≤
                  localExpansionMixedWordEnvelopeTerm
                    (upperConcreteN d) (Abound slack d) (L2bound slack d)
                    (L1bound slack d) (Q2bound slack d) (Q1bound slack d) k w)
    (hTermLimit :
      ∀ slack : ℝ, 0 < slack →
        ∀ w : Fin k → LocalExpansionLetter,
          localWordIsMixed w →
            Tendsto
              (fun d =>
                localExpansionMixedWordEnvelopeTerm
                  (upperConcreteN d) (Abound slack d) (L2bound slack d)
                  (L1bound slack d) (Q2bound slack d) (Q1bound slack d) k w)
              atTop (nhds 0)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  let hk : 0 < k := upper_hk_of_hk3 hk3
  have hk1 : 1 ≤ k := le_trans (by norm_num : 1 ≤ 3) hk3
  have hIso :
      ∀ᶠ d in atTop,
        SharpSphericalIsoperimetry
          (p := p) (q := q) (σ := σ)
          (upperConcreteSphericalMu (p := p) (q := q) (σ := σ) d)
          (upperConcreteRealDim R d) :=
    upper_hIso_concrete_sequences_of_fullSphericalIsoperimetry
      (p := p) (q := q) (σ := σ) R hFullIso hIsoRealDim
  have hK_half :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          1 / 2 ≤
            (upperConcreteSphericalMu (p := p) (q := q) (σ := σ) d).real
              (backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d)
                (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
                (upperCanonicalTau slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d)
                k) := by
    refine
      upper_hK_half_of_sphericalModelMeasure_concrete_bad_bounds
        (p := p) (q := q) (σ := σ)
        (μ := upperConcreteSphericalMu (p := p) (q := q) (σ := σ))
        (N := upperConcreteN)
        (M := upperConcreteM (p := p) (q := q) (σ := σ))
        (τ := upperCanonicalTau)
        (mean := fun _ d =>
          upperConcreteMean (p := p) (q := q) (σ := σ) k d)
        (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
        (k := k) ?_ hKBounds hBad
    exact Eventually.of_forall fun d => rfl
  have hMixed :
      ∀ slack : ℝ, 0 < slack →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop,
            ∀ ⦃X Y : SampleMatrix p q σ⦄,
              Y ∈ backgroundTypicalSet
                  (p := p) (q := q) (σ := σ)
                  (upperConcreteN d)
                  (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
                  (upperCanonicalTau slack d)
                  (upperConcreteMean (p := p) (q := q) (σ := σ) k d)
                  k →
              frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
                sharpSphericalRadius
                  (upperConcreteN d) (spikeSpeed k d)
                  (upperSlackRadius (spikeRoot k eps) R.lam slack) →
              |localExpansionMixedRemainder (p := p) (q := q)
                  (upperConcreteN d) k
                  (localBackground (p := p) (q := q) (σ := σ) Y)
                  (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                  (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))| ≤ η :=
    upper_hMixed_from_uniform_mixedWordBounds_and_termLimits
      (p := p) (q := q) (σ := σ)
      (N := upperConcreteN)
      (speed := spikeSpeed k)
      (aSlack := fun slack =>
        upperSlackRadius (spikeRoot k eps) R.lam slack)
      (M := upperConcreteM (p := p) (q := q) (σ := σ))
      (τ := upperCanonicalTau)
      (mean := fun _ d =>
        upperConcreteMean (p := p) (q := q) (σ := σ) k d)
      (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
      (Q2bound := Q2bound) (Q1bound := Q1bound)
      (k := k) hk1 hWordBound hTermLimit
  exact
    upper_eventual_from_concrete_sequences_localExpansion_scalarLimits
      (p := p) (q := q) (σ := σ)
      R hk3 hε hp hIso hK_half hMixed

/-- Concrete identity `upperConcreteN d = d²`, exported for the endpoint that
builds `hK_half` from normalized Gaussian operator tails. -/
theorem upperConcreteN_eq_dimensionSquared (d : ℕ) :
    upperConcreteN d = (d : ℝ) ^ 2 := by
  simp [upperConcreteN, PptFactorization.AppendixB.ConcreteModel.D_eq]

/-- Eventual positivity of the concrete ambient scalar `d`. -/
theorem upperConcreteAmbientDim_pos_eventually :
    ∀ᶠ d : ℕ in atTop, 0 < (d : ℝ) := by
  filter_upwards [eventually_gt_atTop 0] with d hd
  exact_mod_cast hd

/-- Eventual identity `N d = ambientDim d ^ 2` for the concrete choice
`N d = d²` and `ambientDim d = d`. -/
theorem upperConcreteN_eq_ambientDim_sq_eventually :
    ∀ᶠ d in atTop, upperConcreteN d = (d : ℝ) ^ 2 :=
  Eventually.of_forall upperConcreteN_eq_dimensionSquared

/-- Eventually the concrete ambient scalar is large enough for the
paper-shaped normalized operator-tail estimates. -/
theorem upperConcrete_eventually_large_ambientDim_sq :
    ∀ᶠ d : ℕ in atTop, 12 * Real.log 2 ≤ (d : ℝ) ^ 2 := by
  have hsq :
      Tendsto (fun d : ℕ => (d : ℝ) ^ 2) atTop atTop := by
    have h :
        Tendsto (fun d : ℕ => (d : ℝ) ^ (2 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2)).comp
        tendsto_natCast_atTop_atTop
    simpa [Real.rpow_natCast] using h
  exact hsq.eventually_ge_atTop (12 * Real.log 2)

/-- The concrete ambient scalar square eventually dominates any fixed real
constant. -/
theorem upperConcrete_eventually_large_ambientDim_sq_const (C : ℝ) :
    ∀ᶠ d : ℕ in atTop, C ≤ (d : ℝ) ^ 2 := by
  have hsq :
      Tendsto (fun d : ℕ => (d : ℝ) ^ 2) atTop atTop := by
    have h :
        Tendsto (fun d : ℕ => (d : ℝ) ^ (2 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2)).comp
        tendsto_natCast_atTop_atTop
    simpa [Real.rpow_natCast] using h
  exact hsq.eventually_ge_atTop C

/-- The concrete real dimension eventually dominates every fixed real number.

This is the growth fact behind the fixed-type obstruction: in the true
concrete model family, the underlying matrix type varies with `d`. -/
theorem upperConcreteRealDim_eventually_ge_const
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (C : ℝ) :
    ∀ᶠ d : ℕ in atTop, C ≤ upperConcreteRealDim R d := by
  filter_upwards
      [R.sample_pos_eventually,
        upperConcrete_eventually_large_ambientDim_sq_const C]
    with d hs hlarge
  have hs_ge_one : (1 : ℝ) ≤ (R.sample d : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hs)
  have hd2_nonneg : 0 ≤ (d : ℝ) ^ 2 := sq_nonneg _
  have hprod_ge :
      (d : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 * (R.sample d : ℝ) :=
    le_mul_of_one_le_right hd2_nonneg hs_ge_one
  have hprod_nonneg :
      0 ≤ (d : ℝ) ^ 2 * (R.sample d : ℝ) := by
    exact mul_nonneg hd2_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) hs_ge_one)
  have htwo_ge :
      (d : ℝ) ^ 2 * (R.sample d : ℝ) ≤
        2 * ((d : ℝ) ^ 2 * (R.sample d : ℝ)) := by
    nlinarith
  calc
    C ≤ (d : ℝ) ^ 2 := hlarge
    _ ≤ (d : ℝ) ^ 2 * (R.sample d : ℝ) := hprod_ge
    _ ≤ 2 * ((d : ℝ) ^ 2 * (R.sample d : ℝ)) := htwo_ge
    _ = upperConcreteRealDim R d := by
      simp [upperConcreteRealDim, upperConcreteN, upperConcreteS,
        PptFactorization.AppendixB.ConcreteModel.D_eq,
        PptFactorization.AppendixB.ConcreteModel.S_eq]
      ring

/-- A fixed real constant cannot eventually equal `d²`. -/
theorem not_eventually_const_eq_dimensionSquared (C : ℝ) :
    ¬ ∀ᶠ d : ℕ in atTop, C = (d : ℝ) ^ 2 := by
  intro hconst
  have hlarge_ev := upperConcrete_eventually_large_ambientDim_sq_const (C + 1)
  rw [eventually_atTop] at hconst
  rw [eventually_atTop] at hlarge_ev
  rcases hconst with ⟨n₁, hconst⟩
  rcases hlarge_ev with ⟨n₂, hlarge⟩
  let n := max n₁ n₂
  have hEq := hconst n (le_max_left n₁ n₂)
  have hlarge_n := hlarge n (le_max_right n₁ n₂)
  linarith

/-- Consequently, the fixed-type bridge
`bipartiteDimension p q = d²` cannot be closed for a fixed matrix type.

Use the pointwise concrete-model operator-tail theorem instead when
`p = Fin d` and `q = Fin d`. -/
theorem not_eventually_fixed_bipartiteDimension_eq_dimensionSquared
    {p q : Type*} [Fintype p] [Fintype q] :
    ¬ ∀ᶠ d : ℕ in atTop, bipartiteDimension p q = (d : ℝ) ^ 2 :=
  not_eventually_const_eq_dimensionSquared (bipartiteDimension p q)

/-- The concrete real dimension cannot eventually equal a fixed real constant. -/
theorem not_eventually_upperConcreteRealDim_eq_const
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (C : ℝ) :
    ¬ ∀ᶠ d : ℕ in atTop, upperConcreteRealDim R d = C := by
  intro hconst
  have hlarge_ev := upperConcreteRealDim_eventually_ge_const R (C + 1)
  rw [eventually_atTop] at hconst
  rw [eventually_atTop] at hlarge_ev
  rcases hconst with ⟨n₁, hconst⟩
  rcases hlarge_ev with ⟨n₂, hlarge⟩
  let n := max n₁ n₂
  have hEq := hconst n (le_max_left n₁ n₂)
  have hlarge_n := hlarge n (le_max_right n₁ n₂)
  linarith

/-- Consequently, the fixed-type real-dimension bridge for
`upperConcreteRealDim` cannot be closed in a theorem whose ambient type
`SampleMatrix p q σ` is fixed while `d → ∞`.

Use `upperConcreteRealDim_eq_concreteModel_realDim` in pointwise concrete-model
statements, where the ambient type is allowed to vary with `d`. -/
theorem not_eventually_upperConcreteRealDim_eq_fixed_type_realDim
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ] :
    ¬ ∀ᶠ d : ℕ in atTop,
      upperConcreteRealDim R d =
        2 * bipartiteDimension p q * sampleDimension σ :=
  not_eventually_upperConcreteRealDim_eq_const R
    (2 * bipartiteDimension p q * sampleDimension σ)

/-- Fixed-type dimension bridges cannot be the final concrete upper route.

The actual matrix family has varying ambient types
`p = Fin d`, `q = Fin d`, and `σ = Fin (sample d)`.  Therefore the bridge
`bipartiteDimension p q = d²` is impossible if `p` and `q` are fixed while
`d → ∞`.  This lemma records that the simultaneous fixed-type bridge package
is a compatibility-interface obstruction, not a hard analytic input to prove.

Use the pointwise concrete bridge
`upperConcreteRealDim_eq_concreteModel_realDim` for the actual model family. -/
theorem not_fixed_type_dimension_bridge_pair_for_concrete_upper
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ] :
    ¬
      ((∀ᶠ d : ℕ in atTop,
          upperConcreteRealDim R d =
            2 * bipartiteDimension p q * sampleDimension σ) ∧
        (∀ᶠ d : ℕ in atTop,
          bipartiteDimension p q = (d : ℝ) ^ 2)) := by
  intro h
  exact not_eventually_fixed_bipartiteDimension_eq_dimensionSquared h.2

/-- The concrete operator-tail profile `exp(-d²/12)` is eventually at most
`1/8`. -/
theorem upperConcrete_exp_tail_eventually_le_one_eighth :
    ∀ᶠ d : ℕ in atTop,
      Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)) ≤ 1 / 8 := by
  filter_upwards
      [upperConcrete_eventually_large_ambientDim_sq_const
        (12 * Real.log 8)]
    with d hlarge
  have hle : Real.log 8 ≤ (1 / 12 : ℝ) * (d : ℝ) ^ 2 := by
    nlinarith
  have hneg :
      -((1 / 12 : ℝ) * (d : ℝ) ^ 2) ≤ -Real.log 8 :=
    neg_le_neg hle
  have h8 :
      Real.exp (-(Real.log 8)) = (1 / 8 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 8)]
    norm_num
  simpa [h8] using Real.exp_le_exp.mpr hneg

/-- The two concrete normalized operator tails have total scalar budget at
most `1/4`, eventually. -/
theorem upperConcrete_two_exp_tails_eventually_le_quarter :
    ∀ᶠ d : ℕ in atTop,
      Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)) +
          Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)) ≤
        1 / 4 := by
  filter_upwards [upperConcrete_exp_tail_eventually_le_one_eighth] with d htail
  linarith

/-- Concrete normalized operator tails at the common threshold used by
`upperConcreteM`.

The proved Gaussian/Wishart estimates give separate tails at the canonical
sample and Gamma thresholds.  Since `upperConcreteM` is their maximum, the
good events only become larger and their complements smaller.  The only
dimension bridge left explicit here is the fixed-type identity
`bipartiteDimension p q = d²`, matching the existing concrete probability
theorems. -/
theorem upper_concrete_commonThreshold_operator_tails
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty σ]
    (hDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2) :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        (gaussianMeasure p q σ).real
            ((normalizedSampleOpNormEvent
              (p := p) (q := q) (σ := σ)
              (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
              (d : ℝ))ᶜ) ≤
          Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)) ∧
        (gaussianMeasure p q σ).real
            ((normalizedRhoGammaOpNormEvent
              (p := p) (q := q) (σ := σ)
              (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
              (d : ℝ))ᶜ) ≤
          Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)) := by
  intro slack _hslack
  haveI : IsProbabilityMeasure (gaussianMeasure p q σ) := by
    rw [gaussianMeasure_eq]
    infer_instance
  filter_upwards
      [upperConcreteAmbientDim_pos_eventually,
        upperConcrete_eventually_large_ambientDim_sq, hDim]
    with d hd hLarge hDim_d
  have hprob :=
    PptFactorization.AppendixB.concrete_normalized_operator_norm_probability_inputs
      (p := p) (q := q) (σ := σ)
      (d := (d : ℝ)) hd
      (sampleDimension_ge_one_of_nonempty σ)
      hDim_d hLarge
  constructor
  · have hsubset :
        ((normalizedSampleOpNormEvent
          (p := p) (q := q) (σ := σ)
          (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
          (d : ℝ))ᶜ) ⊆
          ((normalizedSampleOpNormEvent
            (p := p) (q := q) (σ := σ)
            (PptFactorization.AppendixB.concreteSampleOpNormThreshold
              (p := p) (q := q) (σ := σ))
            (d : ℝ))ᶜ) :=
      normalizedSampleOpNormEvent_compl_subset_of_threshold_le
        (p := p) (q := q) (σ := σ) hd
        (by simp [upperConcreteM])
    have hmono :
        (gaussianMeasure p q σ).real
            ((normalizedSampleOpNormEvent
              (p := p) (q := q) (σ := σ)
              (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
              (d : ℝ))ᶜ) ≤
          (gaussianMeasure p q σ).real
            ((normalizedSampleOpNormEvent
              (p := p) (q := q) (σ := σ)
              (PptFactorization.AppendixB.concreteSampleOpNormThreshold
                (p := p) (q := q) (σ := σ))
              (d : ℝ))ᶜ) :=
      measureReal_mono
        (h₂ := (measure_lt_top (gaussianMeasure p q σ) _).ne) hsubset
    exact le_trans hmono hprob.1
  · have hsubset :
        ((normalizedRhoGammaOpNormEvent
          (p := p) (q := q) (σ := σ)
          (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
          (d : ℝ))ᶜ) ⊆
          ((normalizedRhoGammaOpNormEvent
            (p := p) (q := q) (σ := σ)
            (PptFactorization.AppendixB.concreteRhoGammaOpNormThreshold
              (p := p) (q := q) (σ := σ))
            (d : ℝ))ᶜ) :=
      normalizedRhoGammaOpNormEvent_compl_subset_of_threshold_le
        (p := p) (q := q) (σ := σ)
        (by simp [upperConcreteM])
    have hmono :
        (gaussianMeasure p q σ).real
            ((normalizedRhoGammaOpNormEvent
              (p := p) (q := q) (σ := σ)
              (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
              (d : ℝ))ᶜ) ≤
          (gaussianMeasure p q σ).real
            ((normalizedRhoGammaOpNormEvent
              (p := p) (q := q) (σ := σ)
              (PptFactorization.AppendixB.concreteRhoGammaOpNormThreshold
                (p := p) (q := q) (σ := σ))
              (d : ℝ))ᶜ) :=
      measureReal_mono
        (h₂ := (measure_lt_top (gaussianMeasure p q σ) _).ne) hsubset
    exact le_trans hmono hprob.2

/-- Pointwise concrete-model version of the common-threshold operator tails.

Here the matrix type really is the concrete model at size `d`:
`p = Fin d`, `q = Fin d`, and `σ = Fin (R.sample d)`.  Consequently the
dimension identity required by the Gaussian/Wishart tail theorem is proved by
computation, rather than exposed as an eventually-impossible fixed-type bridge. -/
theorem upper_concreteModel_commonThreshold_operator_tails_pointwise
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {d : ℕ} (hd : 0 < d) (hs : 0 < R.sample d)
    (hLarge : 12 * Real.log 2 ≤ (d : ℝ) ^ 2)
    (slack : ℝ) :
    (gaussianMeasure
        (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (PptFactorization.AppendixB.ConcreteModel.SampleIndex (R.sample d))).real
        ((normalizedSampleOpNormEvent
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          (upperConcreteM
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            slack d)
          (d : ℝ))ᶜ) ≤
      Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)) ∧
    (gaussianMeasure
        (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (PptFactorization.AppendixB.ConcreteModel.SampleIndex (R.sample d))).real
        ((normalizedRhoGammaOpNormEvent
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          (upperConcreteM
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            slack d)
          (d : ℝ))ᶜ) ≤
      Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hs1 :
      1 ≤
        sampleDimension
          (PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d)) := by
    have hnat : (1 : ℕ) ≤ R.sample d := Nat.succ_le_iff.mpr hs
    simpa [sampleDimension, PptFactorization.AppendixB.ConcreteModel.SampleIndex]
      using (show (1 : ℝ) ≤ (R.sample d : ℝ) by exact_mod_cast hnat)
  have hDim :
      bipartiteDimension
          (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (PptFactorization.AppendixB.ConcreteModel.RightIndex d) =
        (d : ℝ) ^ 2 :=
    upperConcrete_bipartiteDimension_concreteModel_eq_dimensionSquared d
  haveI :
      IsProbabilityMeasure
        (gaussianMeasure
          (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))) := by
    rw [gaussianMeasure_eq]
    infer_instance
  have hprob :=
    PptFactorization.AppendixB.concrete_normalized_operator_norm_probability_inputs
      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex (R.sample d))
      (d := (d : ℝ)) hdR hs1 hDim hLarge
  constructor
  · have hsubset :
        ((normalizedSampleOpNormEvent
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          (upperConcreteM
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            slack d)
          (d : ℝ))ᶜ) ⊆
          ((normalizedSampleOpNormEvent
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            (PptFactorization.AppendixB.concreteSampleOpNormThreshold
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d)))
            (d : ℝ))ᶜ) :=
      normalizedSampleOpNormEvent_compl_subset_of_threshold_le
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex (R.sample d))
        hdR
        (by simp [upperConcreteM])
    have hmono :
        (gaussianMeasure
          (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (PptFactorization.AppendixB.ConcreteModel.SampleIndex (R.sample d))).real
            ((normalizedSampleOpNormEvent
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteM
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                slack d)
              (d : ℝ))ᶜ) ≤
          (gaussianMeasure
            (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            ((normalizedSampleOpNormEvent
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (PptFactorization.AppendixB.concreteSampleOpNormThreshold
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d)))
              (d : ℝ))ᶜ) :=
      measureReal_mono
        (h₂ := (measure_lt_top
          (gaussianMeasure
            (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))) _).ne)
        hsubset
    exact le_trans hmono hprob.1
  · have hsubset :
        ((normalizedRhoGammaOpNormEvent
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          (upperConcreteM
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            slack d)
          (d : ℝ))ᶜ) ⊆
          ((normalizedRhoGammaOpNormEvent
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            (PptFactorization.AppendixB.concreteRhoGammaOpNormThreshold
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d)))
            (d : ℝ))ᶜ) :=
      normalizedRhoGammaOpNormEvent_compl_subset_of_threshold_le
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex (R.sample d))
        (by simp [upperConcreteM])
    have hmono :
        (gaussianMeasure
          (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (PptFactorization.AppendixB.ConcreteModel.SampleIndex (R.sample d))).real
            ((normalizedRhoGammaOpNormEvent
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteM
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                slack d)
              (d : ℝ))ᶜ) ≤
          (gaussianMeasure
            (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            ((normalizedRhoGammaOpNormEvent
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (PptFactorization.AppendixB.concreteRhoGammaOpNormThreshold
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d)))
              (d : ℝ))ᶜ) :=
      measureReal_mono
        (h₂ := (measure_lt_top
          (gaussianMeasure
            (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))) _).ne)
        hsubset
    exact le_trans hmono hprob.2

/-- Pointwise concrete-model half-mass constructor for the background typical
set.

For the actual model at size `d`, the sample/gamma operator bad probabilities
are supplied by
`upper_concreteModel_commonThreshold_operator_tails_pointwise`.  Thus the only
pointwise probabilistic input is the moment bad-set bound, plus the scalar
budget combining that moment bound with the two concrete operator tails. -/
theorem upper_hK_half_concreteModel_pointwise_of_moment_bound
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {d : ℕ} (hd : 0 < d) (hs : 0 < R.sample d)
    (hLarge : 12 * Real.log 2 ≤ (d : ℝ) ^ 2)
    (slack : ℝ) {k : ℕ} {bMoment : ℝ}
    (hMoment :
      (PptFactorization.AppendixB.sphericalModelMeasure
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d))).real
        (backgroundMomentBadSet
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          (upperConcreteN d)
          (upperCanonicalTau slack d)
          (upperConcreteMean
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            k d)
          k) ≤ bMoment)
    (hBudget :
      bMoment + Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)) +
          Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)) ≤
        1 / 2) :
    1 / 2 ≤
      (PptFactorization.AppendixB.sphericalModelMeasure
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d))).real
        (backgroundTypicalSet
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          (upperConcreteN d)
          (upperConcreteM
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            slack d)
          (upperCanonicalTau slack d)
          (upperConcreteMean
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            k d)
          k) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have htails :=
    upper_concreteModel_commonThreshold_operator_tails_pointwise
      R hd hs hLarge slack
  have hBounds :
      ConcreteSphericalBackgroundBadSetBounds
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d))
        (upperConcreteN d)
        (upperConcreteM
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          slack d)
        (upperCanonicalTau slack d)
        (upperConcreteMean
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          k d)
        bMoment
        (Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)))
        (Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)))
        k :=
    ConcreteSphericalBackgroundBadSetBounds.of_moment_and_gaussian_operator_tails
      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex (R.sample d))
      (N := upperConcreteN d)
      (d := (d : ℝ))
      (M :=
        upperConcreteM
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          slack d)
      (τ := upperCanonicalTau slack d)
      (mean :=
        upperConcreteMean
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          k d)
      (bMoment := bMoment)
      (bSample := Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)))
      (bGamma := Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)))
      (k := k)
      hdR
      (upperConcreteN_eq_dimensionSquared d)
      hMoment htails.1 htails.2
  exact
    hBounds.backgroundTypicalSet_measure_ge_half
      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex (R.sample d))
      (N := upperConcreteN d)
      (M :=
        upperConcreteM
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          slack d)
      (τ := upperCanonicalTau slack d)
      (mean :=
        upperConcreteMean
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          k d)
      (bMoment := bMoment)
      (bSample := Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)))
      (bGamma := Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)))
      (k := k)
      (measurableSet_backgroundTypicalSet
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d))
        (upperConcreteN d)
        (upperConcreteM
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          slack d)
        (upperCanonicalTau slack d)
        (upperConcreteMean
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d))
          k d)
        k)
      hBudget

/-- Eventual concrete-model half-mass for the actual varying matrix family.

This is the family-level wrapper around
`upper_hK_half_concreteModel_pointwise_of_moment_bound`.  The matrix type is
the true one at size `d`, namely `Fin d × Fin d` with sample index
`Fin (R.sample d)`.  Consequently the Gaussian operator tails and their
dimension identities are produced internally by the pointwise concrete-model
tail theorem.  The only probabilistic input left visible here is the
background moment bad-set bound, plus the scalar union budget combining that
moment bound with the two concrete operator-tail estimates. -/
theorem eventually_upper_hK_half_concreteModel_of_moment_bound
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {bMoment : ℝ → ℕ → ℝ}
    (hMoment :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundMomentBadSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                k d)
              k) ≤ bMoment slack d)
    (hBudget :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d : ℕ in atTop,
          bMoment slack d +
              Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)) +
            Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)) ≤
            1 / 2) :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        1 / 2 ≤
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundTypicalSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperConcreteM
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                slack d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                k d)
              k) := by
  intro slack hslack
  filter_upwards
      [eventually_gt_atTop 0, R.sample_pos_eventually,
        upperConcrete_eventually_large_ambientDim_sq,
        hMoment slack hslack, hBudget slack hslack]
    with d hd hs hLarge hMoment_d hBudget_d
  exact
    upper_hK_half_concreteModel_pointwise_of_moment_bound
      R hd hs hLarge slack (k := k) (bMoment := bMoment slack d)
      hMoment_d hBudget_d

/-- Scalar union-budget closure for the concrete background typical set.

Once the moment bad-set envelope tends to zero, the existing concrete operator
tails provide the remaining budget:
`bMoment + exp(-d²/12) + exp(-d²/12) ≤ 1/2`, eventually. -/
theorem upper_hBad_of_moment_bound_tendsto_zero
    {bMoment : ℝ → ℕ → ℝ}
    (hMomentLimit :
      ∀ slack : ℝ, 0 < slack →
        Tendsto (bMoment slack) atTop (nhds 0)) :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d : ℕ in atTop,
        bMoment slack d +
            Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)) +
          Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)) ≤
          1 / 2 := by
  intro slack hslack
  have hMomentSmall :
      ∀ᶠ d : ℕ in atTop, bMoment slack d ≤ 1 / 4 :=
    (hMomentLimit slack hslack).eventually
      (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [hMomentSmall, upperConcrete_two_exp_tails_eventually_le_quarter]
    with d hMoment_d hTail_d
  linarith

/-- Scalar union-budget closure from an eventual smallness bound on the moment
bad-set envelope.

The two concrete operator tails already contribute at most `1/4`, eventually.
Thus it is enough to know that the moment envelope is eventually at most
`1/4`. -/
theorem upper_hBad_of_eventually_moment_bound_le_quarter
    {bMoment : ℝ → ℕ → ℝ}
    (hMomentSmall :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d : ℕ in atTop, bMoment slack d ≤ 1 / 4) :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d : ℕ in atTop,
        bMoment slack d +
            Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)) +
          Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)) ≤
          1 / 2 := by
  intro slack hslack
  filter_upwards [hMomentSmall slack hslack,
      upperConcrete_two_exp_tails_eventually_le_quarter]
    with d hMoment_d hTail_d
  linarith

/-- Scalar union-budget closure from any moment-bound scale which is itself
eventually at most `1/4`. -/
theorem upper_hBad_of_moment_bound_scale_eventually_le_quarter
    {bMoment momentScale : ℝ → ℕ → ℝ}
    (hScaleSmall :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d : ℕ in atTop, momentScale slack d ≤ 1 / 4)
    (hMomentBound :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d : ℕ in atTop, bMoment slack d ≤ momentScale slack d) :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d : ℕ in atTop,
        bMoment slack d +
            Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)) +
          Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)) ≤
          1 / 2 := by
  refine upper_hBad_of_eventually_moment_bound_le_quarter ?_
  intro slack hslack
  filter_upwards [hMomentBound slack hslack, hScaleSmall slack hslack]
    with d hb hs
  exact hb.trans hs

/-- Scalar union-budget closure from any vanishing moment-bound scale.

This is the general `hBad` replacement: if the chosen moment envelope
`bMoment` is eventually bounded above by a scale tending to zero, then the
moment part is eventually at most `1/4`, while the two concrete operator tails
already fit in the remaining `1/4`. -/
theorem upper_hBad_of_moment_bound_scale_tendsto_zero
    {bMoment momentScale : ℝ → ℕ → ℝ}
    (hScaleLimit :
      ∀ slack : ℝ, 0 < slack →
        Tendsto (momentScale slack) atTop (nhds 0))
    (hMomentBound :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d : ℕ in atTop, bMoment slack d ≤ momentScale slack d) :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d : ℕ in atTop,
        bMoment slack d +
            Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)) +
          Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)) ≤
          1 / 2 := by
  refine upper_hBad_of_moment_bound_scale_eventually_le_quarter ?_ hMomentBound
  intro slack hslack
  exact
    (hScaleLimit slack hslack).eventually
      (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 4))

/-- Canonical concrete moment-bound scale of order `D(d)⁻²`.

The numerator may depend on the fixed slack parameter.  For each fixed slack,
this scale tends to zero as `d → ∞`. -/
noncomputable def upperConcreteMomentBoundScale
    (C : ℝ → ℝ) (slack : ℝ) (d : ℕ) : ℝ :=
  C slack / (2 * (PptFactorization.AppendixB.ConcreteModel.D d) ^ 2)

/-- The canonical concrete moment-bound scale tends to zero for every fixed
slack. -/
theorem upperConcreteMomentBoundScale_tendsto_zero
    (C : ℝ → ℝ) :
    ∀ slack : ℝ, 0 < slack →
      Tendsto (upperConcreteMomentBoundScale C slack) atTop (nhds 0) := by
  intro slack _hslack
  exact upper_const_over_two_concreteDimension_sq_tendsto_zero

/-- `hBad` closed from the canonical concrete moment-bound scale
`C(slack) / (2 * D(d)^2)`. -/
theorem upper_hBad_of_moment_bound_concreteDimension_sq_scale
    {bMoment : ℝ → ℕ → ℝ} {C : ℝ → ℝ}
    (hMomentBound :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d : ℕ in atTop,
          bMoment slack d ≤ upperConcreteMomentBoundScale C slack d) :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d : ℕ in atTop,
        bMoment slack d +
            Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)) +
          Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)) ≤
          1 / 2 :=
  upper_hBad_of_moment_bound_scale_tendsto_zero
    (upperConcreteMomentBoundScale_tendsto_zero C) hMomentBound

/-- Actual-family background half-mass with the scalar bad-set budget closed
from a vanishing moment envelope.

Compared with
`eventually_upper_hK_half_concreteModel_of_moment_bound`, this theorem no
longer exposes the union-budget inequality

`bMoment + exp(-d²/12) + exp(-d²/12) ≤ 1/2`.

It derives that budget internally from the fact that the moment envelope tends
to zero, while the concrete operator-tail estimates already give the two
exponential terms. -/
theorem eventually_upper_hK_half_concreteModel_of_moment_bound_tendsto_zero
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {bMoment : ℝ → ℕ → ℝ}
    (hMoment :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundMomentBadSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                k d)
              k) ≤ bMoment slack d)
    (hMomentLimit :
      ∀ slack : ℝ, 0 < slack →
        Tendsto (bMoment slack) atTop (nhds 0)) :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        1 / 2 ≤
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundTypicalSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperConcreteM
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                slack d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                k d)
              k) :=
  eventually_upper_hK_half_concreteModel_of_moment_bound
    R hMoment (upper_hBad_of_moment_bound_tendsto_zero hMomentLimit)

/-- Actual-family background half-mass with the scalar bad-set budget closed
from any vanishing upper scale for the moment envelope. -/
theorem eventually_upper_hK_half_concreteModel_of_moment_bound_scale_tendsto_zero
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {bMoment momentScale : ℝ → ℕ → ℝ}
    (hMoment :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundMomentBadSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                k d)
              k) ≤ bMoment slack d)
    (hScaleLimit :
      ∀ slack : ℝ, 0 < slack →
        Tendsto (momentScale slack) atTop (nhds 0))
    (hMomentBound :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d : ℕ in atTop, bMoment slack d ≤ momentScale slack d) :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        1 / 2 ≤
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundTypicalSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperConcreteM
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                slack d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                k d)
              k) :=
  eventually_upper_hK_half_concreteModel_of_moment_bound
    R hMoment
    (upper_hBad_of_moment_bound_scale_tendsto_zero
      hScaleLimit hMomentBound)

/-- Actual-family background half-mass with the scalar bad-set budget closed
from the canonical `C(slack)/(2 * D(d)^2)` moment scale. -/
theorem eventually_upper_hK_half_concreteModel_of_moment_bound_concreteDimension_sq_scale
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {bMoment : ℝ → ℕ → ℝ} {C : ℝ → ℝ}
    (hMoment :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundMomentBadSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                k d)
              k) ≤ bMoment slack d)
    (hMomentBound :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d : ℕ in atTop,
          bMoment slack d ≤ upperConcreteMomentBoundScale C slack d) :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        1 / 2 ≤
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundTypicalSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperConcreteM
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                slack d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                k d)
              k) :=
  eventually_upper_hK_half_concreteModel_of_moment_bound
    R hMoment
    (upper_hBad_of_moment_bound_concreteDimension_sq_scale hMomentBound)

/-- Actual-family background half-mass from the exponential full-model moment
deviation supplier.

This folds three pieces together:

* strict bad set `⊆` closed deviation set;
* exponential moment envelope `exp (-c d²) → 0`;
* the concrete operator-tail budget already built into
  `eventually_upper_hK_half_concreteModel_of_moment_bound_tendsto_zero`.

Thus this endpoint no longer exposes a separate scalar `hBudget` or a raw
strict-bad-set probability bound; it consumes the named exponential moment
concentration supplier directly. -/
theorem eventually_upper_hK_half_concreteModel_of_exponentialDeviationSetBound
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {c : ℝ} {k : ℕ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k) :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        1 / 2 ≤
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundTypicalSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperConcreteM
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                slack d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                k d)
              k) :=
  eventually_upper_hK_half_concreteModel_of_moment_bound_tendsto_zero
    R
    (upperConcreteModel_backgroundMomentBadSetBound_of_exponentialDeviationSetBound
      R hExp)
    (upperConcreteModelExponentialMomentEnvelope_tendsto_zero hExp.1)

/-- Actual varying-model upper endpoint with background half-mass supplied by
the exponential background moment deviation estimate.

Compared with `upper_eventual_from_concrete_model_localExpansion_scalarLimits`,
this route no longer exposes the typical-set half-mass hypothesis.  The
half-mass statement is obtained internally from the exponential moment
deviation bound, the strict-to-closed bad-set inclusion, and the concrete
operator-tail budget. -/
theorem upper_eventual_from_concrete_model_of_fullIso_oneSidedPositive_exponentialDeviationSetBound_mixedRemainder
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} {c : ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hOneSided :
      UpperConcreteModelOneSidedPositiveDeviationWitness R eps k)
    (hFullIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    (hMixed : UpperConcreteModelMixedRemainderBound R eps k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_model_localExpansion_scalarLimits
    R hk3 hε hOneSided hFullIso
    (eventually_upper_hK_half_concreteModel_of_exponentialDeviationSetBound
      R hExp)
    hMixed

/-! ## Isolated moment concentration input -/

/-- The exact remaining concrete moment concentration obligation.

This is the isolated form of the `hMoment` hypothesis used by the upper
closure pipeline: for every fixed positive slack, the spherical probability of
the formal background moment bad set is eventually bounded by the chosen
envelope `bMoment slack d`.

Everything around this input is bookkeeping: measurability, operator tails,
scalar union budgets, and dimension identities.  Proving this proposition for
the concrete model is the remaining moment concentration block. -/
def UpperConcreteMomentBadSetBound
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    (bMoment : ℝ → ℕ → ℝ) (k : ℕ) : Prop :=
  ∀ slack : ℝ, 0 < slack →
    ∀ᶠ d in atTop,
      (PptFactorization.AppendixB.sphericalModelMeasure
        (p := p) (q := q) (σ := σ)).real
        (backgroundMomentBadSet
          (p := p) (q := q) (σ := σ)
          (upperConcreteN d)
          (upperCanonicalTau slack d)
          (upperConcreteMean (p := p) (q := q) (σ := σ) k d)
          k) ≤ bMoment slack d

/-- The isolated concrete moment concentration obligation with the canonical
scale `C(slack)/(2 * D(d)^2)` as envelope. -/
abbrev UpperConcreteMomentBadSetScaleBound
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    (C : ℝ → ℝ) (k : ℕ) : Prop :=
  UpperConcreteMomentBadSetBound
    (p := p) (q := q) (σ := σ)
    (upperConcreteMomentBoundScale C) k

/-- The canonical-scale moment input is exactly the general moment bad-set
input with envelope `upperConcreteMomentBoundScale C`.

This is an interface theorem only: it does not prove the concentration
estimate, but it makes clear that the scale-bound name introduces no additional
probabilistic input. -/
theorem UpperConcreteMomentBadSetScaleBound_iff_badSetBound_scale
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    (C : ℝ → ℝ) (k : ℕ) :
    UpperConcreteMomentBadSetScaleBound
      (p := p) (q := q) (σ := σ) C k ↔
      UpperConcreteMomentBadSetBound
        (p := p) (q := q) (σ := σ)
        (upperConcreteMomentBoundScale C) k := by
  rfl

/-- A general bad-set bound at the canonical scale supplies the named
canonical-scale input. -/
theorem UpperConcreteMomentBadSetScaleBound.of_badSetBound_scale
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {C : ℝ → ℝ} {k : ℕ}
    (h :
      UpperConcreteMomentBadSetBound
        (p := p) (q := q) (σ := σ)
        (upperConcreteMomentBoundScale C) k) :
    UpperConcreteMomentBadSetScaleBound
      (p := p) (q := q) (σ := σ) C k :=
  (UpperConcreteMomentBadSetScaleBound_iff_badSetBound_scale
    (p := p) (q := q) (σ := σ) C k).2 h

/-- The named canonical-scale input unpacks to the general bad-set bound with
the canonical envelope. -/
theorem UpperConcreteMomentBadSetScaleBound.to_badSetBound_scale
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {C : ℝ → ℝ} {k : ℕ}
    (h :
      UpperConcreteMomentBadSetScaleBound
        (p := p) (q := q) (σ := σ) C k) :
    UpperConcreteMomentBadSetBound
      (p := p) (q := q) (σ := σ)
      (upperConcreteMomentBoundScale C) k :=
  (UpperConcreteMomentBadSetScaleBound_iff_badSetBound_scale
    (p := p) (q := q) (σ := σ) C k).1 h

/-- Fixed-type local-expansion supplier for the isolated canonical-scale moment
block.

This is the fixed-type replay analogue of
`upperConcreteModelMomentExponentialDeviationSetBound_of_localExpansion_envelope`.
It packages the geometric/local-expansion argument directly into the isolated
moment proposition `UpperConcreteMomentBadSetScaleBound`. -/
theorem upperConcreteMomentBadSetScaleBound_of_localExpansion_envelope
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {C : ℝ → ℝ} {k : ℕ}
    {aSlack etaSlack : ℝ → ℝ}
    {M τ : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k)
    (hFullIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (ha : ∀ slack : ℝ, 0 < slack → 0 ≤ aSlack slack)
    (hK_half :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          1 / 2 ≤
            (upperConcreteSphericalMu (p := p) (q := q) (σ := σ) d).real
              (backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k))
    (hMixed :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y : SampleMatrix p q σ⦄,
            Y ∈ backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k →
            frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed k d) (aSlack slack) →
            |localExpansionMixedRemainder
                (p := p) (q := q) (upperConcreteN d) k
                (localBackground (p := p) (q := q) (σ := σ) Y)
                (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))| ≤
              etaSlack slack)
    (hBudget :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          aSlack slack ^ k + etaSlack slack + τ slack d <
            upperCanonicalTau slack d)
    (hEnvelope :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          Real.exp
              (-(((upperConcreteRealDim R d - 1) *
                  sharpSphericalRadiusSq
                    (upperConcreteN d) (spikeSpeed k d) (aSlack slack)) /
                2)) ≤
            upperConcreteMomentBoundScale C slack d) :
    UpperConcreteMomentBadSetScaleBound
      (p := p) (q := q) (σ := σ) C k := by
  simpa [UpperConcreteMomentBadSetScaleBound, UpperConcreteMomentBadSetBound,
    upperConcreteMomentBoundScale] using
    upperConcreteMomentBadSetBound_of_localExpansion_envelope_raw
      (p := p) (q := q) (σ := σ) R
      (C := C) (k := k)
      (aSlack := aSlack) (etaSlack := etaSlack)
      (M := M) (τ := τ)
      hk3 hFullIso hIsoRealDim ha hK_half hMixed hBudget hEnvelope

/-- Unpack the isolated `hMoment` proposition into the raw pipeline shape. -/
theorem upper_hMoment_of_upperConcreteMomentBadSetBound
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {bMoment : ℝ → ℕ → ℝ} {k : ℕ}
    (hMoment :
      UpperConcreteMomentBadSetBound
        (p := p) (q := q) (σ := σ) bMoment k) :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        (PptFactorization.AppendixB.sphericalModelMeasure
          (p := p) (q := q) (σ := σ)).real
          (backgroundMomentBadSet
            (p := p) (q := q) (σ := σ)
            (upperConcreteN d)
            (upperCanonicalTau slack d)
            (upperConcreteMean (p := p) (q := q) (σ := σ) k d)
            k) ≤ bMoment slack d :=
  hMoment

/-- Unpack the canonical-scale isolated `hMoment` proposition. -/
theorem upper_hMoment_of_upperConcreteMomentBadSetScaleBound
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {C : ℝ → ℝ} {k : ℕ}
    (hMoment :
      UpperConcreteMomentBadSetScaleBound
        (p := p) (q := q) (σ := σ) C k) :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        (PptFactorization.AppendixB.sphericalModelMeasure
          (p := p) (q := q) (σ := σ)).real
          (backgroundMomentBadSet
            (p := p) (q := q) (σ := σ)
            (upperConcreteN d)
            (upperCanonicalTau slack d)
            (upperConcreteMean (p := p) (q := q) (σ := σ) k d)
            k) ≤ upperConcreteMomentBoundScale C slack d :=
  hMoment

/-! ## Isolated mixed-word deterministic input -/

/-- The exact remaining concrete mixed-word estimate.

This isolates the deterministic `hWordBound` hypothesis used by the upper
closure pipeline.  For every fixed positive slack, eventually in the concrete
dimension parameter, every mixed local-expansion word is bounded by the chosen
scalar envelope term uniformly for all `Y` in the background typical set and
all `X` in the sharp spherical neighbourhood of `Y`.

This proposition does not prove the Schatten/Hölder mixed-word estimates; it
names the deterministic analytic obligation cleanly. -/
def UpperConcreteMixedWordBound
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps : ℝ) (k : ℕ)
    (Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ) : Prop :=
  ∀ slack : ℝ, 0 < slack →
    ∀ᶠ d in atTop,
      ∀ ⦃X Y : SampleMatrix p q σ⦄,
        Y ∈ backgroundTypicalSet
            (p := p) (q := q) (σ := σ)
            (upperConcreteN d)
            (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
            (upperCanonicalTau slack d)
            (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k →
        frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
          sharpSphericalRadius
            (upperConcreteN d) (spikeSpeed k d)
            (upperSlackRadius (spikeRoot k eps) R.lam slack) →
        ∀ w : Fin k → LocalExpansionLetter,
          localWordIsMixed w →
            |localWordScaledTraceTerm
                (p := p) (q := q)
                (upperConcreteN d)
                (localBackground (p := p) (q := q) (σ := σ) Y)
                (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
                w| ≤
                localExpansionMixedWordEnvelopeTerm
                (upperConcreteN d) (Abound slack d) (L2bound slack d)
                (L1bound slack d) (Q2bound slack d) (Q1bound slack d) k w

/-- Casewise mixed-word bound for words with exactly one linear defect and no
quadratic defect. -/
def UpperConcreteOneLinearMixedWordBound
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps : ℝ) (k : ℕ)
    (Abound L1bound : ℝ → ℕ → ℝ) : Prop :=
  ∀ slack : ℝ, 0 < slack →
    ∀ᶠ d in atTop,
      ∀ ⦃X Y : SampleMatrix p q σ⦄,
        Y ∈ backgroundTypicalSet
            (p := p) (q := q) (σ := σ)
            (upperConcreteN d)
            (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
            (upperCanonicalTau slack d)
            (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k →
        frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
          sharpSphericalRadius
            (upperConcreteN d) (spikeSpeed k d)
            (upperSlackRadius (spikeRoot k eps) R.lam slack) →
        ∀ w : Fin k → LocalExpansionLetter,
          localWordHasOneLinearDefect w →
            |localWordScaledTraceTerm
                (p := p) (q := q)
                (upperConcreteN d)
                (localBackground (p := p) (q := q) (σ := σ) Y)
                (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
                w| ≤
              upperConcreteN d ^ (k - 1) *
                Abound slack d ^ (k - 1) * L1bound slack d

/-- Casewise mixed-word bound for words with exactly one quadratic defect and
no linear defect. -/
def UpperConcreteOneQuadraticMixedWordBound
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps : ℝ) (k : ℕ)
    (Abound Q1bound : ℝ → ℕ → ℝ) : Prop :=
  ∀ slack : ℝ, 0 < slack →
    ∀ᶠ d in atTop,
      ∀ ⦃X Y : SampleMatrix p q σ⦄,
        Y ∈ backgroundTypicalSet
            (p := p) (q := q) (σ := σ)
            (upperConcreteN d)
            (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
            (upperCanonicalTau slack d)
            (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k →
        frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
          sharpSphericalRadius
            (upperConcreteN d) (spikeSpeed k d)
            (upperSlackRadius (spikeRoot k eps) R.lam slack) →
        ∀ w : Fin k → LocalExpansionLetter,
          localWordHasOneQuadraticDefect w →
            |localWordScaledTraceTerm
                (p := p) (q := q)
                (upperConcreteN d)
                (localBackground (p := p) (q := q) (σ := σ) Y)
                (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
                w| ≤
              upperConcreteN d ^ (k - 1) *
                Abound slack d ^ (k - 1) * Q1bound slack d

/-- Casewise mixed-word bound for the remaining mixed words: neither the
single-linear nor the single-quadratic branch. -/
def UpperConcreteMultiDefectMixedWordBound
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps : ℝ) (k : ℕ)
    (Abound L2bound Q2bound : ℝ → ℕ → ℝ) : Prop :=
  ∀ slack : ℝ, 0 < slack →
    ∀ᶠ d in atTop,
      ∀ ⦃X Y : SampleMatrix p q σ⦄,
        Y ∈ backgroundTypicalSet
            (p := p) (q := q) (σ := σ)
            (upperConcreteN d)
            (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
            (upperCanonicalTau slack d)
            (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k →
        frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
          sharpSphericalRadius
            (upperConcreteN d) (spikeSpeed k d)
            (upperSlackRadius (spikeRoot k eps) R.lam slack) →
        ∀ w : Fin k → LocalExpansionLetter,
          localWordIsMixed w →
          ¬ localWordHasOneLinearDefect w →
          ¬ localWordHasOneQuadraticDefect w →
            |localWordScaledTraceTerm
                (p := p) (q := q)
                (upperConcreteN d)
                (localBackground (p := p) (q := q) (σ := σ) Y)
                (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
                w| ≤
              upperConcreteN d ^ (k - 1) *
                Abound slack d ^
                  localWordLetterCount LocalExpansionLetter.A w *
                L2bound slack d ^
                  localWordLetterCount LocalExpansionLetter.L w *
                Q2bound slack d ^
                  localWordLetterCount LocalExpansionLetter.Q w

/-- Assemble the packaged mixed-word bound from the three explicit branches of
the word-envelope formula. -/
theorem upperConcreteMixedWordBound_of_caseBounds
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime}
    {eps : ℝ} {k : ℕ}
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hOneLinear :
      UpperConcreteOneLinearMixedWordBound
        (p := p) (q := q) (σ := σ)
        R eps k Abound L1bound)
    (hOneQuadratic :
      UpperConcreteOneQuadraticMixedWordBound
        (p := p) (q := q) (σ := σ)
        R eps k Abound Q1bound)
    (hMulti :
      UpperConcreteMultiDefectMixedWordBound
        (p := p) (q := q) (σ := σ)
        R eps k Abound L2bound Q2bound) :
    UpperConcreteMixedWordBound
      (p := p) (q := q) (σ := σ)
      R eps k Abound L2bound L1bound Q2bound Q1bound := by
  intro slack hslack
  filter_upwards [hOneLinear slack hslack, hOneQuadratic slack hslack,
    hMulti slack hslack] with d hOneLinear_d hOneQuadratic_d hMulti_d
  intro X Y hY hdist w hw
  by_cases hLinear : localWordHasOneLinearDefect w
  · simpa [localExpansionMixedWordEnvelopeTerm, hLinear] using
      (hOneLinear_d hY hdist w hLinear)
  · by_cases hQuadratic : localWordHasOneQuadraticDefect w
    · simpa [localExpansionMixedWordEnvelopeTerm, hLinear, hQuadratic] using
        (hOneQuadratic_d hY hdist w hQuadratic)
    · simpa [localExpansionMixedWordEnvelopeTerm, hLinear, hQuadratic] using
        (hMulti_d hY hdist w hw hLinear hQuadratic)

/-- Group the three branchwise deterministic mixed-word estimates into one
endpoint-facing package. -/
def UpperConcreteMixedWordCaseBounds
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps : ℝ) (k : ℕ)
    (Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ) : Prop :=
  UpperConcreteOneLinearMixedWordBound
      (p := p) (q := q) (σ := σ)
      R eps k Abound L1bound ∧
    UpperConcreteOneQuadraticMixedWordBound
      (p := p) (q := q) (σ := σ)
      R eps k Abound Q1bound ∧
    UpperConcreteMultiDefectMixedWordBound
      (p := p) (q := q) (σ := σ)
      R eps k Abound L2bound Q2bound

/-- Build the grouped mixed-word case package from the three branchwise
estimates. -/
theorem upperConcreteMixedWordCaseBounds_of_branch_bounds
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime}
    {eps : ℝ} {k : ℕ}
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hOneLinear :
      UpperConcreteOneLinearMixedWordBound
        (p := p) (q := q) (σ := σ)
        R eps k Abound L1bound)
    (hOneQuadratic :
      UpperConcreteOneQuadraticMixedWordBound
        (p := p) (q := q) (σ := σ)
        R eps k Abound Q1bound)
    (hMulti :
      UpperConcreteMultiDefectMixedWordBound
        (p := p) (q := q) (σ := σ)
        R eps k Abound L2bound Q2bound) :
    UpperConcreteMixedWordCaseBounds
      (p := p) (q := q) (σ := σ)
      R eps k Abound L2bound L1bound Q2bound Q1bound :=
  ⟨hOneLinear, hOneQuadratic, hMulti⟩

/-- The exact remaining scalar mixed-word envelope limits.

This isolates the deterministic `hTermLimit` hypothesis used by the upper
closure pipeline: every scalar envelope term attached to a mixed word tends to
zero for each fixed positive slack.

This proposition is deliberately separate from `UpperConcreteMixedWordBound`;
the former is a uniform word-by-word estimate, while this one is the scalar
asymptotic limit calculation. -/
def UpperConcreteMixedTermLimit
    (k : ℕ)
    (Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ) : Prop :=
  ∀ slack : ℝ, 0 < slack →
    ∀ w : Fin k → LocalExpansionLetter,
      localWordIsMixed w →
        Tendsto
          (fun d =>
            localExpansionMixedWordEnvelopeTerm
              (upperConcreteN d) (Abound slack d) (L2bound slack d)
              (L1bound slack d) (Q2bound slack d) (Q1bound slack d) k w)
          atTop (nhds 0)

/-- Casewise scalar limit for mixed words with exactly one linear defect and no
quadratic defect. -/
def UpperConcreteOneLinearMixedTermLimit
    (k : ℕ) (Abound L1bound : ℝ → ℕ → ℝ) : Prop :=
  ∀ slack : ℝ, 0 < slack →
    Tendsto
      (fun d =>
        upperConcreteN d ^ (k - 1) *
          Abound slack d ^ (k - 1) * L1bound slack d)
      atTop (nhds 0)

/-- The actual-model canonical good-set and one-`L` scalars cannot themselves
supply the one-linear scalar limit at `k = 3`: for the spike slack choice, the
canonical term diverges instead of tending to zero. -/
theorem upperConcreteModel_oneLinearMixedTermLimit_not_canonical
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps) :
    ¬ UpperConcreteOneLinearMixedTermLimit 3
      (upperConcreteModelMixedWordAbound R)
      (upperConcreteModelMixedWordL1bound R eps 3) := by
  intro hlim
  let slack := spikeRate 3 R.lam eps
  have hroot_pos : 0 < spikeRoot 3 eps := spikeRoot_pos (by norm_num) hε
  have hslack : 0 < slack := by
    unfold slack spikeRate
    nlinarith [R.lam_pos, hroot_pos]
  have hchoice := upperSlackRadius_spike_choice (k := 3)
    (by norm_num : 0 < 3) R.lam_pos hε slack hslack
  have ha : 0 < upperSlackRadius (spikeRoot 3 eps) R.lam slack := by
    have hcost := hchoice.2.2
    have hleft : 0 < spikeRate 3 R.lam eps - slack / 4 := by
      simp [slack]
      nlinarith [R.lam_pos, hroot_pos]
    have hprod : 0 < R.lam * upperSlackRadius (spikeRoot 3 eps) R.lam slack :=
      lt_of_lt_of_le hleft hcost
    nlinarith [R.lam_pos]
  have hAtTop := upperConcreteModel_oneLinearCanonicalTerm_tendsto_atTop
    R (eps := eps) (slack := slack) ha
  have htoZero := hlim slack hslack
  have hlt :
      ∀ᶠ d : ℕ in atTop,
        upperConcreteN d ^ (3 - 1) *
          upperConcreteModelMixedWordAbound R slack d ^ (3 - 1) *
          upperConcreteModelMixedWordL1bound R eps 3 slack d < 1 :=
    htoZero.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hge :
      ∀ᶠ d : ℕ in atTop,
        1 ≤ upperConcreteN d ^ (3 - 1) *
          upperConcreteModelMixedWordAbound R slack d ^ (3 - 1) *
          upperConcreteModelMixedWordL1bound R eps 3 slack d :=
    Filter.tendsto_atTop.mp hAtTop 1
  have hfalse : ∀ᶠ _d : ℕ in atTop, False := by
    filter_upwards [hlt, hge] with d hlt_d hge_d
    linarith
  simp only [Filter.Eventually, Set.setOf_false] at hfalse
  have hbot : (∅ : Set ℕ) ∈ (atTop : Filter ℕ) := hfalse
  have hne : (atTop : Filter ℕ).NeBot := inferInstance
  exact hne.ne ((Filter.empty_mem_iff_bot).mp hbot)

/-- The current one-linear upper branch interface is inconsistent with the
actual-model canonical lower envelope at `k = 3`.

If the abstract one-linear scalar package dominates the actual-model canonical
one-linear package and tends to zero, it must simultaneously dominate a term
that diverges. -/
theorem upperConcreteModel_oneLinearDom_and_termLimit_impossible
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    {Abound L1bound : ℝ → ℕ → ℝ} :
    ¬ (UpperConcreteModelOneLinearMixedWordEnvelopeDomination
          R eps 3 Abound L1bound ∧
        UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound) := by
  intro hpair
  let slack := spikeRate 3 R.lam eps
  have hroot_pos : 0 < spikeRoot 3 eps := spikeRoot_pos (by norm_num) hε
  have hslack : 0 < slack := by
    unfold slack spikeRate
    nlinarith [R.lam_pos, hroot_pos]
  have hchoice := upperSlackRadius_spike_choice (k := 3)
    (by norm_num : 0 < 3) R.lam_pos hε slack hslack
  have ha : 0 < upperSlackRadius (spikeRoot 3 eps) R.lam slack := by
    have hcost := hchoice.2.2
    have hleft : 0 < spikeRate 3 R.lam eps - slack / 4 := by
      simp [slack]
      nlinarith [R.lam_pos, hroot_pos]
    have hprod : 0 < R.lam * upperSlackRadius (spikeRoot 3 eps) R.lam slack :=
      lt_of_lt_of_le hleft hcost
    nlinarith [R.lam_pos]
  have hAtTop := upperConcreteModel_oneLinearCanonicalTerm_tendsto_atTop
    R (eps := eps) (slack := slack) ha
  have hdom := hpair.1 slack hslack
  have htoZero := hpair.2 slack hslack
  have hlt :
      ∀ᶠ d : ℕ in atTop,
        upperConcreteN d ^ (3 - 1) *
          Abound slack d ^ (3 - 1) * L1bound slack d < 1 :=
    htoZero.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hge :
      ∀ᶠ d : ℕ in atTop,
        1 ≤ upperConcreteN d ^ (3 - 1) *
          upperConcreteModelMixedWordAbound R slack d ^ (3 - 1) *
          upperConcreteModelMixedWordL1bound R eps 3 slack d :=
    Filter.tendsto_atTop.mp hAtTop 1
  have hfalse : ∀ᶠ _d : ℕ in atTop, False := by
    filter_upwards [hdom, hlt, hge] with d hdom_d hlt_d hge_d
    linarith
  simp only [Filter.Eventually, Set.setOf_false] at hfalse
  have hbot : (∅ : Set ℕ) ∈ (atTop : Filter ℕ) := hfalse
  have hne : (atTop : Filter ℕ).NeBot := inferInstance
  exact hne.ne ((Filter.empty_mem_iff_bot).mp hbot)

/-- Casewise scalar limit for mixed words with exactly one quadratic defect and
no linear defect. -/
def UpperConcreteOneQuadraticMixedTermLimit
    (k : ℕ) (Abound Q1bound : ℝ → ℕ → ℝ) : Prop :=
  ∀ slack : ℝ, 0 < slack →
    Tendsto
      (fun d =>
        upperConcreteN d ^ (k - 1) *
          Abound slack d ^ (k - 1) * Q1bound slack d)
      atTop (nhds 0)

/-- The actual-model canonical good-set and one-`Q` scalars cannot themselves
supply the one-quadratic scalar limit at `k = 3`: for the spike slack choice,
the canonical term diverges instead of tending to zero. -/
theorem upperConcreteModel_oneQuadraticMixedTermLimit_not_canonical
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps) :
    ¬ UpperConcreteOneQuadraticMixedTermLimit 3
      (upperConcreteModelMixedWordAbound R)
      (upperConcreteModelMixedWordQ1bound R eps 3) := by
  intro hlim
  let slack := spikeRate 3 R.lam eps
  have hroot_pos : 0 < spikeRoot 3 eps := spikeRoot_pos (by norm_num) hε
  have hslack : 0 < slack := by
    unfold slack spikeRate
    nlinarith [R.lam_pos, hroot_pos]
  have hchoice := upperSlackRadius_spike_choice (k := 3)
    (by norm_num : 0 < 3) R.lam_pos hε slack hslack
  have ha : 0 < upperSlackRadius (spikeRoot 3 eps) R.lam slack := by
    have hcost := hchoice.2.2
    have hleft : 0 < spikeRate 3 R.lam eps - slack / 4 := by
      simp [slack]
      nlinarith [R.lam_pos, hroot_pos]
    have hprod : 0 < R.lam * upperSlackRadius (spikeRoot 3 eps) R.lam slack :=
      lt_of_lt_of_le hleft hcost
    nlinarith [R.lam_pos]
  have hAtTop := upperConcreteModel_oneQuadraticCanonicalTerm_tendsto_atTop
    R (eps := eps) (slack := slack) ha
  have htoZero := hlim slack hslack
  have hlt :
      ∀ᶠ d : ℕ in atTop,
        upperConcreteN d ^ (3 - 1) *
          upperConcreteModelMixedWordAbound R slack d ^ (3 - 1) *
          upperConcreteModelMixedWordQ1bound R eps 3 slack d < 1 :=
    htoZero.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hge :
      ∀ᶠ d : ℕ in atTop,
        1 ≤ upperConcreteN d ^ (3 - 1) *
          upperConcreteModelMixedWordAbound R slack d ^ (3 - 1) *
          upperConcreteModelMixedWordQ1bound R eps 3 slack d :=
    Filter.tendsto_atTop.mp hAtTop 1
  have hfalse : ∀ᶠ _d : ℕ in atTop, False := by
    filter_upwards [hlt, hge] with d hlt_d hge_d
    linarith
  simp only [Filter.Eventually, Set.setOf_false] at hfalse
  have hbot : (∅ : Set ℕ) ∈ (atTop : Filter ℕ) := hfalse
  have hne : (atTop : Filter ℕ).NeBot := inferInstance
  exact hne.ne ((Filter.empty_mem_iff_bot).mp hbot)

/-- The current one-quadratic upper branch interface is inconsistent with the
actual-model canonical lower envelope at `k = 3`.

If the abstract one-quadratic scalar package dominates the actual-model
canonical one-quadratic package and tends to zero, it must simultaneously
dominate a term that diverges. -/
theorem upperConcreteModel_oneQuadraticDom_and_termLimit_impossible
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    {Abound Q1bound : ℝ → ℕ → ℝ} :
    ¬ (UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination
          R eps 3 Abound Q1bound ∧
        UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound) := by
  intro hpair
  let slack := spikeRate 3 R.lam eps
  have hroot_pos : 0 < spikeRoot 3 eps := spikeRoot_pos (by norm_num) hε
  have hslack : 0 < slack := by
    unfold slack spikeRate
    nlinarith [R.lam_pos, hroot_pos]
  have hchoice := upperSlackRadius_spike_choice (k := 3)
    (by norm_num : 0 < 3) R.lam_pos hε slack hslack
  have ha : 0 < upperSlackRadius (spikeRoot 3 eps) R.lam slack := by
    have hcost := hchoice.2.2
    have hleft : 0 < spikeRate 3 R.lam eps - slack / 4 := by
      simp [slack]
      nlinarith [R.lam_pos, hroot_pos]
    have hprod : 0 < R.lam * upperSlackRadius (spikeRoot 3 eps) R.lam slack :=
      lt_of_lt_of_le hleft hcost
    nlinarith [R.lam_pos]
  have hAtTop := upperConcreteModel_oneQuadraticCanonicalTerm_tendsto_atTop
    R (eps := eps) (slack := slack) ha
  have hdom := hpair.1 slack hslack
  have htoZero := hpair.2 slack hslack
  have hlt :
      ∀ᶠ d : ℕ in atTop,
        upperConcreteN d ^ (3 - 1) *
          Abound slack d ^ (3 - 1) * Q1bound slack d < 1 :=
    htoZero.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hge :
      ∀ᶠ d : ℕ in atTop,
        1 ≤ upperConcreteN d ^ (3 - 1) *
          upperConcreteModelMixedWordAbound R slack d ^ (3 - 1) *
          upperConcreteModelMixedWordQ1bound R eps 3 slack d :=
    Filter.tendsto_atTop.mp hAtTop 1
  have hfalse : ∀ᶠ _d : ℕ in atTop, False := by
    filter_upwards [hdom, hlt, hge] with d hdom_d hlt_d hge_d
    linarith
  simp only [Filter.Eventually, Set.setOf_false] at hfalse
  have hbot : (∅ : Set ℕ) ∈ (atTop : Filter ℕ) := hfalse
  have hne : (atTop : Filter ℕ).NeBot := inferInstance
  exact hne.ne ((Filter.empty_mem_iff_bot).mp hbot)

/-- Casewise scalar limit for mixed words carrying at least two defects in
total, after excluding the single-linear and single-quadratic branches. -/
def UpperConcreteMultiDefectMixedTermLimit
    (k : ℕ) (Abound L2bound Q2bound : ℝ → ℕ → ℝ) : Prop :=
  ∀ slack : ℝ, 0 < slack →
    ∀ w : Fin k → LocalExpansionLetter,
      localWordIsMixed w →
      ¬ localWordHasOneLinearDefect w →
      ¬ localWordHasOneQuadraticDefect w →
        Tendsto
          (fun d =>
            upperConcreteN d ^ (k - 1) *
              Abound slack d ^
                localWordLetterCount LocalExpansionLetter.A w *
              L2bound slack d ^
                localWordLetterCount LocalExpansionLetter.L w *
              Q2bound slack d ^
                localWordLetterCount LocalExpansionLetter.Q w)
          atTop (nhds 0)

/-- The actual-model canonical multi-defect scalars cannot themselves supply
the multi-defect scalar limit at `k = 3`.  The pure `L,L,L` word is already a
valid multi-defect word, and its canonical scalar term diverges. -/
theorem upperConcreteModel_multiDefectMixedTermLimit_not_canonical
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps) :
    ¬ UpperConcreteMultiDefectMixedTermLimit 3
      (upperConcreteModelMixedWordAbound R)
      (upperConcreteModelMixedWordL2bound R eps 3)
      (upperConcreteModelMixedWordQ2bound R eps 3) := by
  intro hlim
  let slack := spikeRate 3 R.lam eps
  have hroot_pos : 0 < spikeRoot 3 eps := spikeRoot_pos (by norm_num) hε
  have hslack : 0 < slack := by
    unfold slack spikeRate
    nlinarith [R.lam_pos, hroot_pos]
  have hchoice := upperSlackRadius_spike_choice (k := 3)
    (by norm_num : 0 < 3) R.lam_pos hε slack hslack
  have ha : 0 < upperSlackRadius (spikeRoot 3 eps) R.lam slack := by
    have hcost := hchoice.2.2
    have hleft : 0 < spikeRate 3 R.lam eps - slack / 4 := by
      simp [slack]
      nlinarith [R.lam_pos, hroot_pos]
    have hprod : 0 < R.lam * upperSlackRadius (spikeRoot 3 eps) R.lam slack :=
      lt_of_lt_of_le hleft hcost
    nlinarith [R.lam_pos]
  have hMixed : localWordIsMixed upperConcreteModelPureL3Word := by
    simp [upperConcreteModelPureL3Word, localWordIsMixed, localWordIsPure]
  have hNotOneLinear : ¬ localWordHasOneLinearDefect upperConcreteModelPureL3Word := by
    intro h
    have hL :
        localWordLetterCount LocalExpansionLetter.L upperConcreteModelPureL3Word = 3 := by
      simp [upperConcreteModelPureL3Word, localWordLetterCount]
    have hLone := h.1
    omega
  have hNotOneQuadratic : ¬ localWordHasOneQuadraticDefect upperConcreteModelPureL3Word := by
    intro h
    have hL :
        localWordLetterCount LocalExpansionLetter.L upperConcreteModelPureL3Word = 3 := by
      simp [upperConcreteModelPureL3Word, localWordLetterCount]
    have hLzero := h.1
    omega
  have hAtTop := upperConcreteModel_pureL3CanonicalMultiTerm_tendsto_atTop
    R (eps := eps) (slack := slack) ha
  have htoZero :=
    hlim slack hslack upperConcreteModelPureL3Word hMixed hNotOneLinear hNotOneQuadratic
  have hlt :
      ∀ᶠ d : ℕ in atTop,
        upperConcreteN d ^ (3 - 1) *
          upperConcreteModelMixedWordAbound R slack d ^
            localWordLetterCount LocalExpansionLetter.A upperConcreteModelPureL3Word *
          upperConcreteModelMixedWordL2bound R eps 3 slack d ^
            localWordLetterCount LocalExpansionLetter.L upperConcreteModelPureL3Word *
          upperConcreteModelMixedWordQ2bound R eps 3 slack d ^
            localWordLetterCount LocalExpansionLetter.Q upperConcreteModelPureL3Word < 1 :=
    htoZero.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hge :
      ∀ᶠ d : ℕ in atTop,
        1 ≤
          upperConcreteN d ^ (3 - 1) *
            upperConcreteModelMixedWordAbound R slack d ^
              localWordLetterCount LocalExpansionLetter.A upperConcreteModelPureL3Word *
            upperConcreteModelMixedWordL2bound R eps 3 slack d ^
              localWordLetterCount LocalExpansionLetter.L upperConcreteModelPureL3Word *
            upperConcreteModelMixedWordQ2bound R eps 3 slack d ^
              localWordLetterCount LocalExpansionLetter.Q upperConcreteModelPureL3Word :=
    Filter.tendsto_atTop.mp hAtTop 1
  have hfalse : ∀ᶠ _d : ℕ in atTop, False := by
    filter_upwards [hlt, hge] with d hlt_d hge_d
    linarith
  simp only [Filter.Eventually, Set.setOf_false] at hfalse
  have hbot : (∅ : Set ℕ) ∈ (atTop : Filter ℕ) := hfalse
  have hne : (atTop : Filter ℕ).NeBot := inferInstance
  exact hne.ne ((Filter.empty_mem_iff_bot).mp hbot)

/-- The current multi-defect upper branch interface is inconsistent with the
actual-model canonical lower envelope at `k = 3`.

For the pure `L,L,L` word, domination of the actual-model canonical
multi-defect package plus a zero-limit abstract package would force a divergent
term to be eventually below a term tending to zero. -/
theorem upperConcreteModel_multiDefectDom_and_termLimit_impossible
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    {Abound L2bound Q2bound : ℝ → ℕ → ℝ} :
    ¬ (UpperConcreteModelMultiDefectMixedWordEnvelopeDomination
          R eps 3 Abound L2bound Q2bound ∧
        UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) := by
  intro hpair
  let slack := spikeRate 3 R.lam eps
  have hroot_pos : 0 < spikeRoot 3 eps := spikeRoot_pos (by norm_num) hε
  have hslack : 0 < slack := by
    unfold slack spikeRate
    nlinarith [R.lam_pos, hroot_pos]
  have hchoice := upperSlackRadius_spike_choice (k := 3)
    (by norm_num : 0 < 3) R.lam_pos hε slack hslack
  have ha : 0 < upperSlackRadius (spikeRoot 3 eps) R.lam slack := by
    have hcost := hchoice.2.2
    have hleft : 0 < spikeRate 3 R.lam eps - slack / 4 := by
      simp [slack]
      nlinarith [R.lam_pos, hroot_pos]
    have hprod : 0 < R.lam * upperSlackRadius (spikeRoot 3 eps) R.lam slack :=
      lt_of_lt_of_le hleft hcost
    nlinarith [R.lam_pos]
  have hMixed : localWordIsMixed upperConcreteModelPureL3Word := by
    simp [upperConcreteModelPureL3Word, localWordIsMixed, localWordIsPure]
  have hNotOneLinear : ¬ localWordHasOneLinearDefect upperConcreteModelPureL3Word := by
    intro h
    have hL :
        localWordLetterCount LocalExpansionLetter.L upperConcreteModelPureL3Word = 3 := by
      simp [upperConcreteModelPureL3Word, localWordLetterCount]
    have hLone := h.1
    omega
  have hNotOneQuadratic : ¬ localWordHasOneQuadraticDefect upperConcreteModelPureL3Word := by
    intro h
    have hL :
        localWordLetterCount LocalExpansionLetter.L upperConcreteModelPureL3Word = 3 := by
      simp [upperConcreteModelPureL3Word, localWordLetterCount]
    have hLzero := h.1
    omega
  have hAtTop := upperConcreteModel_pureL3CanonicalMultiTerm_tendsto_atTop
    R (eps := eps) (slack := slack) ha
  have hdom :=
    (hpair.1 slack hslack).mono fun d hd =>
      hd upperConcreteModelPureL3Word hMixed hNotOneLinear hNotOneQuadratic
  have htoZero :=
    hpair.2 slack hslack upperConcreteModelPureL3Word
      hMixed hNotOneLinear hNotOneQuadratic
  have hlt :
      ∀ᶠ d : ℕ in atTop,
        upperConcreteN d ^ (3 - 1) *
          Abound slack d ^
            localWordLetterCount LocalExpansionLetter.A upperConcreteModelPureL3Word *
          L2bound slack d ^
            localWordLetterCount LocalExpansionLetter.L upperConcreteModelPureL3Word *
          Q2bound slack d ^
            localWordLetterCount LocalExpansionLetter.Q upperConcreteModelPureL3Word < 1 :=
    htoZero.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hge :
      ∀ᶠ d : ℕ in atTop,
        1 ≤
          upperConcreteN d ^ (3 - 1) *
            upperConcreteModelMixedWordAbound R slack d ^
              localWordLetterCount LocalExpansionLetter.A upperConcreteModelPureL3Word *
            upperConcreteModelMixedWordL2bound R eps 3 slack d ^
              localWordLetterCount LocalExpansionLetter.L upperConcreteModelPureL3Word *
            upperConcreteModelMixedWordQ2bound R eps 3 slack d ^
              localWordLetterCount LocalExpansionLetter.Q upperConcreteModelPureL3Word :=
    Filter.tendsto_atTop.mp hAtTop 1
  have hfalse : ∀ᶠ _d : ℕ in atTop, False := by
    filter_upwards [hdom, hlt, hge] with d hdom_d hlt_d hge_d
    linarith
  simp only [Filter.Eventually, Set.setOf_false] at hfalse
  have hbot : (∅ : Set ℕ) ∈ (atTop : Filter ℕ) := hfalse
  have hne : (atTop : Filter ℕ).NeBot := inferInstance
  exact hne.ne ((Filter.empty_mem_iff_bot).mp hbot)

/-- Assemble the packaged mixed-term limit from the three explicit mixed-word
branches: single linear defect, single quadratic defect, and the remaining
multi-defect words. -/
theorem upperConcreteMixedTermLimit_of_caseLimits
    {k : ℕ}
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hOneLinear :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hOneQuadratic :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hMulti :
      UpperConcreteMultiDefectMixedTermLimit
        k Abound L2bound Q2bound) :
    UpperConcreteMixedTermLimit
      k Abound L2bound L1bound Q2bound Q1bound := by
  intro slack hslack w hw
  by_cases hLinear : localWordHasOneLinearDefect w
  · simpa [localExpansionMixedWordEnvelopeTerm, hLinear] using
      hOneLinear slack hslack
  · by_cases hQuadratic : localWordHasOneQuadraticDefect w
    · simpa [localExpansionMixedWordEnvelopeTerm, hLinear, hQuadratic] using
        hOneQuadratic slack hslack
    · simpa [localExpansionMixedWordEnvelopeTerm, hLinear, hQuadratic] using
        hMulti slack hslack w hw hLinear hQuadratic

/-- Group the three scalar mixed-defect limit branches into one
endpoint-facing package. -/
def UpperConcreteMixedDefectCaseLimits
    (k : ℕ)
    (Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ) : Prop :=
  UpperConcreteOneLinearMixedTermLimit k Abound L1bound ∧
    UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound ∧
    UpperConcreteMultiDefectMixedTermLimit k Abound L2bound Q2bound

/-- Group the three scalar domination inputs used to derive the actual-model
mixed-word branch bounds. -/
def UpperConcreteMixedBranchEnvelopeDominations
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps : ℝ) (k : ℕ)
    (Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ) : Prop :=
  UpperConcreteModelOneLinearMixedWordEnvelopeDomination R eps k Abound L1bound ∧
    UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination R eps k Abound Q1bound ∧
    UpperConcreteModelMultiDefectMixedWordEnvelopeDomination R eps k Abound L2bound Q2bound

/-- Build the grouped scalar mixed-defect package from the three branchwise
limit inputs. -/
theorem upperConcreteMixedDefectCaseLimits_of_defect_cases
    {k : ℕ}
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hOneLinear :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hOneQuadratic :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hMulti :
      UpperConcreteMultiDefectMixedTermLimit
        k Abound L2bound Q2bound) :
    UpperConcreteMixedDefectCaseLimits
      k Abound L2bound L1bound Q2bound Q1bound :=
  ⟨hOneLinear, hOneQuadratic, hMulti⟩

/-- Fold the grouped scalar mixed-defect package into the single mixed-term
limit proposition consumed by the curated upper endpoint. -/
theorem upperConcreteMixedTermLimit_of_defectCaseLimits
    {k : ℕ}
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hDefectLimits :
      UpperConcreteMixedDefectCaseLimits
        k Abound L2bound L1bound Q2bound Q1bound) :
    UpperConcreteMixedTermLimit
      k Abound L2bound L1bound Q2bound Q1bound :=
  upperConcreteMixedTermLimit_of_caseLimits
    hDefectLimits.1 hDefectLimits.2.1 hDefectLimits.2.2

/-- Actual-model scalar mixed-word envelope limit from the three branchwise
scalar limits.

The actual-model term-limit predicate has the same scalar content as
`UpperConcreteMixedTermLimit`; this lemma records the branch split at the
model-facing API, so the upper route can expose the one-linear, one-quadratic,
and multi-defect limits separately. -/
theorem UpperConcreteModelMixedTermLimit_of_caseLimits
    {k : ℕ}
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hOneLinear :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hOneQuadratic :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hMulti :
      UpperConcreteMultiDefectMixedTermLimit
        k Abound L2bound Q2bound) :
    UpperConcreteModelMixedTermLimit
      k Abound L2bound L1bound Q2bound Q1bound := by
  simpa [UpperConcreteModelMixedTermLimit, UpperConcreteMixedTermLimit] using
    upperConcreteMixedTermLimit_of_caseLimits
      hOneLinear hOneQuadratic hMulti

/-- Actual-model scalar mixed-word envelope limit from the grouped branchwise
limit package. -/
theorem UpperConcreteModelMixedTermLimit_of_defectCaseLimits
    {k : ℕ}
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hDefectLimits :
      UpperConcreteMixedDefectCaseLimits
        k Abound L2bound L1bound Q2bound Q1bound) :
    UpperConcreteModelMixedTermLimit
      k Abound L2bound L1bound Q2bound Q1bound :=
  UpperConcreteModelMixedTermLimit_of_caseLimits
    hDefectLimits.1 hDefectLimits.2.1 hDefectLimits.2.2

/-- The actual-model canonical scalar package cannot supply the bundled
mixed-term limit at `k = 3`.

This is the closure-level version of the branch diagnostics: the pure
multi-defect branch already forces a canonical scalar term that diverges rather
than tending to zero. -/
theorem upperConcreteModel_mixedTermLimit_not_canonical
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps) :
    ¬ UpperConcreteModelMixedTermLimit 3
      (upperConcreteModelMixedWordAbound R)
      (upperConcreteModelMixedWordL2bound R eps 3)
      (upperConcreteModelMixedWordL1bound R eps 3)
      (upperConcreteModelMixedWordQ2bound R eps 3)
      (upperConcreteModelMixedWordQ1bound R eps 3) := by
  intro hUpperTerm
  apply upperConcreteModel_multiDefectMixedTermLimit_not_canonical (R := R) hε
  intro slack hslack w hMixed hNotOneLinear hNotOneQuadratic
  simpa [UpperConcreteModelMixedTermLimit, localExpansionMixedWordEnvelopeTerm,
    hNotOneLinear, hNotOneQuadratic] using
    hUpperTerm slack hslack w hMixed

/-- The actual-model canonical casewise scalar package is inconsistent at
`k = 3`.

Even before bundling the cases, the one-linear canonical scalar already cannot
tend to zero, so the three-case scalar packet cannot be a valid closure input. -/
theorem upperConcreteModel_caseTermLimits_not_canonical
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps) :
    ¬ UpperConcreteMixedDefectCaseLimits 3
      (upperConcreteModelMixedWordAbound R)
      (upperConcreteModelMixedWordL2bound R eps 3)
      (upperConcreteModelMixedWordL1bound R eps 3)
      (upperConcreteModelMixedWordQ2bound R eps 3)
      (upperConcreteModelMixedWordQ1bound R eps 3) := by
  intro hCases
  exact upperConcreteModel_oneLinearMixedTermLimit_not_canonical
    (R := R) hε hCases.1

/-- The endpoint-facing branch-domination route cannot close the actual-model
mixed scalar problem at `k = 3`.

Any abstract branch envelopes that both dominate the actual-model canonical
one-linear branch and tend to zero would force a divergent canonical term to
be eventually below a zero-limit term. -/
theorem upperConcreteModel_branchEnvelopeDominations_and_caseTermLimits_impossible
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ} :
    ¬ (UpperConcreteMixedBranchEnvelopeDominations
          R eps 3 Abound L2bound L1bound Q2bound Q1bound ∧
        UpperConcreteMixedDefectCaseLimits
          3 Abound L2bound L1bound Q2bound Q1bound) := by
  intro hPacket
  exact upperConcreteModel_oneLinearDom_and_termLimit_impossible
    (R := R) hε ⟨hPacket.1.1, hPacket.2.1⟩

/-- Assemble the actual-model mixed-remainder supplier from model-level
mixed-word bounds and the three scalar branch limits. -/
theorem UpperConcreteModelMixedRemainderBound_of_modelMixedWordBound_and_caseTermLimits
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hk : 1 ≤ k)
    (hWord :
      UpperConcreteModelMixedWordBound
        R eps k Abound L2bound L1bound Q2bound Q1bound)
    (hOneLinear :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hOneQuadratic :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hMulti :
      UpperConcreteMultiDefectMixedTermLimit
        k Abound L2bound Q2bound) :
    UpperConcreteModelMixedRemainderBound R eps k :=
  UpperConcreteModelMixedRemainderBound_of_modelMixedWordBound_and_termLimit
    R hk hWord
    (UpperConcreteModelMixedTermLimit_of_caseLimits
      hOneLinear hOneQuadratic hMulti)

/-- Assemble the actual-model mixed-remainder supplier directly from the three
casewise mixed-word estimates and the three scalar branch limits. -/
theorem UpperConcreteModelMixedRemainderBound_of_caseMixedWordBounds_and_caseTermLimits
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hk : 1 ≤ k)
    (hOneLinearWord :
      UpperConcreteModelOneLinearMixedWordBound
        R eps k Abound L1bound)
    (hOneQuadraticWord :
      UpperConcreteModelOneQuadraticMixedWordBound
        R eps k Abound Q1bound)
    (hMultiWord :
      UpperConcreteModelMultiDefectMixedWordBound
        R eps k Abound L2bound Q2bound)
    (hOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit
        k Abound L2bound Q2bound) :
    UpperConcreteModelMixedRemainderBound R eps k :=
  UpperConcreteModelMixedRemainderBound_of_modelMixedWordBound_and_caseTermLimits
    R hk
    (UpperConcreteModelMixedWordBound_of_caseBounds
      R hOneLinearWord hOneQuadraticWord hMultiWord)
    hOneLinearTerm hOneQuadraticTerm hMultiTerm

/-- Assemble the actual-model mixed-remainder supplier directly from the three
branch envelope-dominations and the three scalar branch limits.

This is the endpoint-facing deterministic upper mixed closure: the local
matrix estimates supply the three branch word bounds, while the caller still
has to provide the scalar dominations and scalar limits. -/
theorem UpperConcreteModelMixedRemainderBound_of_branchEnvelopeDominations_and_caseTermLimits
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hOneLinearDom :
      UpperConcreteModelOneLinearMixedWordEnvelopeDomination
        R eps k Abound L1bound)
    (hOneQuadraticDom :
      UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination
        R eps k Abound Q1bound)
    (hMultiDom :
      UpperConcreteModelMultiDefectMixedWordEnvelopeDomination
        R eps k Abound L2bound Q2bound)
    (hOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit
        k Abound L2bound Q2bound) :
    UpperConcreteModelMixedRemainderBound R eps k :=
  UpperConcreteModelMixedRemainderBound_of_caseMixedWordBounds_and_caseTermLimits
    R (le_trans (by norm_num : 1 ≤ 3) hk3)
    (UpperConcreteModelOneLinearMixedWordBound_of_envelopeDomination
      R hk3 hε hOneLinearDom)
    (UpperConcreteModelOneQuadraticMixedWordBound_of_envelopeDomination
      R hk3 hε hOneQuadraticDom)
    (UpperConcreteModelMultiDefectMixedWordBound_of_envelopeDomination
      R hk3 hε hMultiDom)
    hOneLinearTerm hOneQuadraticTerm hMultiTerm

/-- Actual-model one-linear mixed-word bound with the canonical actual-model
envelope choices.

This closes the word-estimate half of the one-linear upper mixed branch.  It
does not assert the corresponding scalar zero-limit. -/
theorem UpperConcreteModelOneLinearMixedWordBound_of_canonical_model
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    (hk3 : 3 ≤ k) (hε : 0 < eps) :
    UpperConcreteModelOneLinearMixedWordBound R eps k
      (upperConcreteModelMixedWordAbound R)
      (upperConcreteModelMixedWordL1bound R eps k) := by
  refine
    UpperConcreteModelOneLinearMixedWordBound_of_envelopeDomination
      R hk3 hε ?_
  intro slack hslack
  exact Filter.Eventually.of_forall fun d => le_rfl

/-- Actual-model one-quadratic mixed-word bound with the canonical actual-model
envelope choices.

This closes the word-estimate half of the one-quadratic upper mixed branch.  It
does not assert the corresponding scalar zero-limit. -/
theorem UpperConcreteModelOneQuadraticMixedWordBound_of_canonical_model
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    (hk3 : 3 ≤ k) (hε : 0 < eps) :
    UpperConcreteModelOneQuadraticMixedWordBound R eps k
      (upperConcreteModelMixedWordAbound R)
      (upperConcreteModelMixedWordQ1bound R eps k) := by
  refine
    UpperConcreteModelOneQuadraticMixedWordBound_of_envelopeDomination
      R hk3 hε ?_
  intro slack hslack
  exact Filter.Eventually.of_forall fun d => le_rfl

/-- Actual-model multi-defect mixed-word bound with the canonical actual-model
envelope choices.

This closes the word-estimate half of the multi-defect upper mixed branch.  It
does not assert the corresponding scalar zero-limit. -/
theorem UpperConcreteModelMultiDefectMixedWordBound_of_canonical_model
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    (hk3 : 3 ≤ k) (hε : 0 < eps) :
    UpperConcreteModelMultiDefectMixedWordBound R eps k
      (upperConcreteModelMixedWordAbound R)
      (upperConcreteModelMixedWordL2bound R eps k)
      (upperConcreteModelMixedWordQ2bound R eps k) := by
  refine
    UpperConcreteModelMultiDefectMixedWordBound_of_envelopeDomination
      R hk3 hε ?_
  intro slack hslack
  exact Filter.Eventually.of_forall fun d w hmix hNotOneLinear hNotOneQuadratic =>
    le_rfl

/-- Actual-model mixed-word bound with the canonical actual-model envelope
choices.

This closes the word-estimate half of the upper mixed block for the canonical
actual-model scalars.  It does not assert the scalar zero-limit needed to turn
the finite word envelope into an `o(1)` mixed remainder. -/
theorem UpperConcreteModelMixedWordBound_of_canonical_model
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    (hk3 : 3 ≤ k) (hε : 0 < eps) :
    UpperConcreteModelMixedWordBound R eps k
      (upperConcreteModelMixedWordAbound R)
      (upperConcreteModelMixedWordL2bound R eps k)
      (upperConcreteModelMixedWordL1bound R eps k)
      (upperConcreteModelMixedWordQ2bound R eps k)
      (upperConcreteModelMixedWordQ1bound R eps k) :=
  UpperConcreteModelMixedWordBound_of_caseBounds R
    (UpperConcreteModelOneLinearMixedWordBound_of_canonical_model
      R hk3 hε)
    (UpperConcreteModelOneQuadraticMixedWordBound_of_canonical_model
      R hk3 hε)
    (UpperConcreteModelMultiDefectMixedWordBound_of_canonical_model
      R hk3 hε)

/-- Actual-model mixed-remainder bound from canonical word estimates and a
bundled scalar term limit.

The word estimates are supplied internally by the canonical actual-model
envelopes.  The scalar `o(1)` content remains exactly the explicit hypothesis
`hTerm`. -/
theorem UpperConcreteModelMixedRemainderBound_of_canonical_model_and_termLimit
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hTerm :
      UpperConcreteModelMixedTermLimit k
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL2bound R eps k)
        (upperConcreteModelMixedWordL1bound R eps k)
        (upperConcreteModelMixedWordQ2bound R eps k)
        (upperConcreteModelMixedWordQ1bound R eps k)) :
    UpperConcreteModelMixedRemainderBound R eps k :=
  UpperConcreteModelMixedRemainderBound_of_modelMixedWordBound_and_termLimit
    R (le_trans (by norm_num : 1 ≤ 3) hk3)
    (UpperConcreteModelMixedWordBound_of_canonical_model R hk3 hε)
    hTerm

/-- Actual-model mixed-remainder bound from canonical word estimates and the
three casewise scalar term limits.

This is the case-split version of
`UpperConcreteModelMixedRemainderBound_of_canonical_model_and_termLimit`: the
finite scalar-limit package is assembled internally from the one-linear,
one-quadratic, and multi-defect limits. -/
theorem UpperConcreteModelMixedRemainderBound_of_canonical_model_and_caseTermLimits
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hOneLinear :
      UpperConcreteOneLinearMixedTermLimit k
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL1bound R eps k))
    (hOneQuadratic :
      UpperConcreteOneQuadraticMixedTermLimit k
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordQ1bound R eps k))
    (hMulti :
      UpperConcreteMultiDefectMixedTermLimit k
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL2bound R eps k)
        (upperConcreteModelMixedWordQ2bound R eps k)) :
    UpperConcreteModelMixedRemainderBound R eps k :=
  UpperConcreteModelMixedRemainderBound_of_canonical_model_and_termLimit
    R hk3 hε
    (UpperConcreteModelMixedTermLimit_of_caseLimits
      hOneLinear hOneQuadratic hMulti)

/-- Canonical one-`Q` mixed-word envelope scalars for the upper closure.

`Abound` is the background operator-norm scale `M/N`; `Q1bound` is the
trace-scale envelope `sqrt(dim) * r_N^2` at the sharp spherical radius. -/
noncomputable def upperConcreteMixedWordAboundCanonical
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    (slack : ℝ) (d : ℕ) : ℝ :=
  upperMixedWordAbound
    (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
    (upperConcreteN d)

noncomputable def upperConcreteMixedWordQ1boundCanonical
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps : ℝ) (k : ℕ) (slack : ℝ) (d : ℕ) : ℝ :=
  upperMixedWordQ1bound (p := p) (q := q)
    (upperConcreteN d) (spikeSpeed k d)
    (upperSlackRadius (spikeRoot k eps) R.lam slack)

/-- Canonical one-`L` mixed-word envelope scalar at the sharp spherical radius. -/
noncomputable def upperConcreteMixedWordL1boundCanonical
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps : ℝ) (k : ℕ) (slack : ℝ) (d : ℕ) : ℝ :=
  upperMixedWordL1bound (p := p) (q := q)
    (upperConcreteN d)
    (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
    (spikeSpeed k d)
    (upperSlackRadius (spikeRoot k eps) R.lam slack)

/-- Canonical multi-defect linear trace-envelope scalar. -/
noncomputable def upperConcreteMixedWordL2boundCanonical
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps : ℝ) (k : ℕ) (slack : ℝ) (d : ℕ) : ℝ :=
  upperMixedWordL2bound (p := p) (q := q)
    (upperConcreteN d)
    (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
    (spikeSpeed k d)
    (upperSlackRadius (spikeRoot k eps) R.lam slack)

/-- Canonical multi-defect quadratic trace-envelope scalar. -/
noncomputable def upperConcreteMixedWordQ2boundCanonical
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps : ℝ) (k : ℕ) (slack : ℝ) (d : ℕ) : ℝ :=
  upperMixedWordQ2bound (p := p) (q := q)
    (upperConcreteN d) (spikeSpeed k d)
    (upperSlackRadius (spikeRoot k eps) R.lam slack)

/-- Closed supplier for `UpperConcreteOneQuadraticMixedWordBound` with the
canonical scalar choices above.

The only extra input beyond the usual background/sharp-radius hypotheses is
`3 ≤ k`.  The supplier uses the background gamma operator-norm bound from
`backgroundTypicalSet` and the sharp-radius quadratic bound; no separate
matrix-dimension bridge is required. -/
theorem upperConcreteOneQuadraticMixedWordBound_of_canonical_oneQ
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    (hk3 : 3 ≤ k) (hε : 0 < eps) :
    UpperConcreteOneQuadraticMixedWordBound
      (p := p) (q := q) (σ := σ)
      R eps k
      (fun slack d => upperConcreteMixedWordAboundCanonical (p := p) (q := q) (σ := σ) slack d)
      (fun slack d =>
        upperConcreteMixedWordQ1boundCanonical (p := p) (q := q) (σ := σ) R eps k slack d) := by
  intro slack hslack
  filter_upwards [eventually_gt_atTop 0] with d hd
  intro X Y hY hdist w hOneQ
  have hNpos : 0 < upperConcreteN d := by
    unfold upperConcreteN
    exact PptFactorization.AppendixB.ConcreteModel.D_pos hd
  have hM : 0 ≤ upperConcreteM (p := p) (q := q) (σ := σ) slack d := by
    unfold upperConcreteM
    exact le_max_of_le_left (Real.sqrt_nonneg _)
  let a := upperSlackRadius (spikeRoot k eps) R.lam slack
  have hk_pos : 0 < k := by omega
  have ha : 0 ≤ a :=
    (upperSlackRadius_spike_choice hk_pos R.lam_pos hε slack hslack).1
  let hr : ℝ :=
    sharpSphericalRadius (upperConcreteN d) (spikeSpeed k d) a
  have hA_op :
      opNorm (p := p) (q := q)
        (localBackground (p := p) (q := q) (σ := σ) Y) ≤
        upperConcreteM (p := p) (q := q) (σ := σ) slack d /
          upperConcreteN d :=
    backgroundTypicalSet_gammaOpNorm_bound
      (p := p) (q := q) (σ := σ)
      (N := upperConcreteN d)
      (M := upperConcreteM (p := p) (q := q) (σ := σ) slack d)
      (τ := upperCanonicalTau slack d)
      (mean := upperConcreteMean (p := p) (q := q) (σ := σ) k d)
      (k := k) hY
  have hQ_frob :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
          (localQuadratic (p := p) (q := q) (σ := σ) (X - Y)) ≤
        upperMixedWordQ1bound (p := p) (q := q)
            (upperConcreteN d) (spikeSpeed k d) a /
          Real.sqrt (Fintype.card (BipIndex p q)) := by
    have hQ :=
      localQuadratic_frobeniusNorm_bound_of_radius
        (p := p) (q := q) (σ := σ) (X := X) (Y := Y)
        (r := hr) (by simpa [hr, a] using hdist)
    have hcardpos : 0 < (Fintype.card (BipIndex p q) : ℝ) := by
      exact_mod_cast Fintype.card_pos
    unfold upperMixedWordQ1bound
    rw [div_eq_mul_inv]
    field_simp [hcardpos.ne']
    exact hQ
  have hNoL :=
    localWordHasOneQuadraticDefect_noLinear hOneQ
  have hterm_eq :
      localWordScaledTraceTerm (p := p) (q := q)
          (upperConcreteN d)
          (localBackground (p := p) (q := q) (σ := σ) Y)
          (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
          (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
          w =
        localWordScaledTraceTerm (p := p) (q := q)
          (upperConcreteN d)
          (localBackground (p := p) (q := q) (σ := σ) Y) 0
          (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
          w :=
    localWordScaledTraceTerm_eq_of_noLinear
      (p := p) (q := q)
      (N := upperConcreteN d)
      (A := localBackground (p := p) (q := q) (σ := σ) Y)
      (L := localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
      (Q := localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
      hNoL
  have hcore :=
    localWordScaledTraceTerm_oneQuadratic_le_envelope
      (N := upperConcreteN d)
      (M := upperConcreteM (p := p) (q := q) (σ := σ) slack d)
      (a := a) (speed := spikeSpeed k d)
      (A := localBackground (p := p) (q := q) (σ := σ) Y)
      (L := 0)
      (Q := localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
      (w := w) hNpos hM hk3 hA_op hQ_frob hOneQ
  rw [hterm_eq]
  simpa [upperConcreteMixedWordAboundCanonical, upperConcreteMixedWordQ1boundCanonical,
    upperMixedWordAbound, upperMixedWordQ1bound, a, BipIndex, Fintype.card_prod] using hcore

/-- The concrete one-`Q` radius ratio vanishes for every `k ≥ 3`.

After unfolding the canonical choices this is the scalar fact
`d^(2 + 2/k) / d^4 → 0`.  It is isolated so the one-quadratic term-limit
supplier below does not have to repeat the real-power algebra. -/
theorem upperConcrete_oneQuadraticRadiusRatio_tendsto_zero
    {k : ℕ} (hk3 : 3 ≤ k) :
    Tendsto
      (fun d => spikeSpeed k d / upperConcreteN d ^ 2)
      atTop (nhds 0) := by
  have hkR : 0 < (k : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) hk3)
  have hexp : 0 < (2 : ℝ) - 2 / (k : ℝ) := by
    have hkge : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk3
    nlinarith
      [div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
        (by norm_num : (0 : ℝ) < 3) hkge]
  have hbase :
      Tendsto (fun d : ℕ => (d : ℝ) ^ ((2 : ℝ) - 2 / (k : ℝ))) atTop atTop :=
    (tendsto_rpow_atTop hexp).comp tendsto_natCast_atTop_atTop
  have hinv :
      Tendsto (fun d : ℕ => ((d : ℝ) ^ ((2 : ℝ) - 2 / (k : ℝ)))⁻¹)
        atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hbase
  refine hinv.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with d hd
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hpowpos : (d : ℝ) ^ ((2 : ℝ) - 2 / (k : ℝ)) ≠ 0 :=
    (Real.rpow_pos_of_pos hdR _).ne'
  unfold spikeSpeed upperConcreteN
  simp only [PptFactorization.AppendixB.ConcreteModel.D_eq]
  field_simp [hpowpos, ne_of_gt hkR, ne_of_gt hdR]
  rw [← Real.rpow_add hdR]
  have hs :
      2 * ((k : ℝ) - 1) / (k : ℝ) +
          2 * ((k : ℝ) + 1) / (k : ℝ) = (4 : ℝ) := by
    field_simp [ne_of_gt hkR]
    ring_nf
  rw [hs]
  exact (Real.rpow_natCast (d : ℝ) 4).symm

/-- Closed scalar supplier for the canonical one-`Q` mixed-term limit.

For the canonical upper scalars, the term is eventually a fixed constant times
`spikeSpeed k d / upperConcreteN d^2`; the previous lemma sends that ratio to
zero when `3 ≤ k`. -/
theorem upperConcreteOneQuadraticMixedTermLimit_of_canonical_oneQ
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    (hk3 : 3 ≤ k) (hε : 0 < eps) :
    UpperConcreteOneQuadraticMixedTermLimit
      k
      (fun slack d => upperConcreteMixedWordAboundCanonical (p := p) (q := q) (σ := σ) slack d)
      (fun slack d =>
        upperConcreteMixedWordQ1boundCanonical (p := p) (q := q) (σ := σ) R eps k slack d) := by
  intro slack hslack
  let a := upperSlackRadius (spikeRoot k eps) R.lam slack
  have hkpos : 0 < k := by omega
  have ha : 0 ≤ a :=
    (upperSlackRadius_spike_choice hkpos R.lam_pos hε slack hslack).1
  have hlim_ratio :=
    upperConcrete_oneQuadraticRadiusRatio_tendsto_zero (k := k) hk3
  have hlim :
      Tendsto
        (fun d =>
          ((upperConcreteM (p := p) (q := q) (σ := σ) slack 0) ^ (k - 1) *
              Real.sqrt (Fintype.card (BipIndex p q)) * a) *
            (spikeSpeed k d / upperConcreteN d ^ 2))
        atTop (nhds 0) := by
    simpa using
      hlim_ratio.const_mul
        ((upperConcreteM (p := p) (q := q) (σ := σ) slack 0) ^ (k - 1) *
          Real.sqrt (Fintype.card (BipIndex p q)) * a)
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with d hd
  have hNpos : 0 < upperConcreteN d := by
    unfold upperConcreteN
    exact PptFactorization.AppendixB.ConcreteModel.D_pos hd
  have hNne : upperConcreteN d ≠ 0 := ne_of_gt hNpos
  have hspeed_nonneg : 0 ≤ spikeSpeed k d := by
    unfold spikeSpeed
    exact Real.rpow_nonneg (Nat.cast_nonneg d) _
  have hsq :
      sharpSphericalRadius (upperConcreteN d) (spikeSpeed k d) a ^ 2 =
        sharpSphericalRadiusSq (upperConcreteN d) (spikeSpeed k d) a :=
    sharpSphericalRadius_sq (N := upperConcreteN d) (speed := spikeSpeed k d)
      (a := a) ha hspeed_nonneg
  have hNpow :
      upperConcreteN d ^ (k - 1) * (upperConcreteN d)⁻¹ ^ (k - 1) = 1 := by
    rw [← mul_pow]
    field_simp [hNne]
    simp
  have hdivpow :
      (upperConcreteM (p := p) (q := q) (σ := σ) slack d / upperConcreteN d) ^
          (k - 1) =
        upperConcreteM (p := p) (q := q) (σ := σ) slack 0 ^ (k - 1) *
          (upperConcreteN d)⁻¹ ^ (k - 1) := by
    simp [upperConcreteM, div_eq_mul_inv, mul_pow]
  simp [upperConcreteMixedWordAboundCanonical, upperConcreteMixedWordQ1boundCanonical,
    upperMixedWordAbound, upperMixedWordQ1bound, sharpSphericalRadiusSq, hsq, a,
    BipIndex, Fintype.card_prod, Real.sqrt_mul]
  field_simp [hNne]
  rw [hdivpow]
  rw [show
      √↑(Fintype.card p) * √↑(Fintype.card q) *
          upperSlackRadius (spikeRoot k eps) R.lam slack * spikeSpeed k d *
          upperConcreteN d ^ (k - 1) *
          (upperConcreteM (p := p) (q := q) (σ := σ) slack 0 ^ (k - 1) *
            (upperConcreteN d)⁻¹ ^ (k - 1)) =
        upperConcreteM (p := p) (q := q) (σ := σ) slack 0 ^ (k - 1) *
          √↑(Fintype.card p) * √↑(Fintype.card q) *
            upperSlackRadius (spikeRoot k eps) R.lam slack * spikeSpeed k d *
              (upperConcreteN d ^ (k - 1) *
                (upperConcreteN d)⁻¹ ^ (k - 1)) by ring]
  rw [hNpow]
  ring

/-- The concrete one-`L` radius ratio vanishes for every `k ≥ 3`.

After unfolding the canonical choices this is the scalar fact
`√(spikeSpeed k d) / upperConcreteN d → 0`. -/
theorem upperConcrete_oneLinearRadiusRatio_tendsto_zero
    {k : ℕ} (hk3 : 3 ≤ k) :
    Tendsto
      (fun d => Real.sqrt (spikeSpeed k d) / upperConcreteN d)
      atTop (nhds 0) := by
  have hQ :=
    upperConcrete_oneQuadraticRadiusRatio_tendsto_zero (k := k) hk3
  have h := hQ.sqrt
  rw [show (√(0 : ℝ)) = (0 : ℝ) from Real.sqrt_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with d hd
  have hNpos : 0 < upperConcreteN d := by
    unfold upperConcreteN
    exact PptFactorization.AppendixB.ConcreteModel.D_pos hd
  have hspeed_nonneg : 0 ≤ spikeSpeed k d := by
    unfold spikeSpeed
    exact Real.rpow_nonneg (Nat.cast_nonneg d) _
  have hmain :
      Real.sqrt (spikeSpeed k d / upperConcreteN d ^ 2) =
        Real.sqrt (spikeSpeed k d) / upperConcreteN d := by
    rw [Real.sqrt_div hspeed_nonneg (upperConcreteN d ^ 2), Real.sqrt_sq (le_of_lt hNpos)]
  exact hmain

/-- Helper for one-`L` mixed-term limits: `N^(3/2) = N * √N`. -/
theorem upperConcreteN_pow_three_halves_eq {d : ℕ} (hd : 0 < d) :
    upperConcreteN d ^ (3 / 2 : ℝ) =
      upperConcreteN d * Real.sqrt (upperConcreteN d) := by
  have hNpos : 0 < upperConcreteN d := by
    unfold upperConcreteN
    exact PptFactorization.AppendixB.ConcreteModel.D_pos hd
  calc
    upperConcreteN d ^ (3 / 2 : ℝ) = upperConcreteN d ^ (1 + 1 / 2 : ℝ) := by norm_num
    _ = upperConcreteN d ^ (1 : ℝ) * upperConcreteN d ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hNpos]
    _ = upperConcreteN d * Real.sqrt (upperConcreteN d) := by
      rw [Real.rpow_one, ← Real.sqrt_eq_rpow]

/-- The concrete one-`L` mixed-term ratio vanishes for every `k ≥ 3`.

After unfolding the canonical choices this is
`√(spikeSpeed k d) / upperConcreteN d ^ (3/2) → 0`. -/
theorem upperConcrete_oneLinearTermRatio_tendsto_zero
    {k : ℕ} (hk3 : 3 ≤ k) :
    Tendsto
      (fun d => Real.sqrt (spikeSpeed k d) / upperConcreteN d ^ (3 / 2 : ℝ))
      atTop (nhds 0) := by
  have hsqrt := upperConcrete_oneLinearRadiusRatio_tendsto_zero (k := k) hk3
  have hNsqrt :
      Tendsto (fun d => Real.sqrt (upperConcreteN d)) atTop atTop := by
    refine tendsto_natCast_atTop_atTop.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with d hd
    have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
    simp [upperConcreteN, PptFactorization.AppendixB.ConcreteModel.D_eq, Real.sqrt_sq (le_of_lt hdR)]
  have hquot := hsqrt.div_atTop hNsqrt
  refine hquot.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with d hd
  have hNpos : 0 < upperConcreteN d := by
    unfold upperConcreteN
    exact PptFactorization.AppendixB.ConcreteModel.D_pos hd
  have hN3 := upperConcreteN_pow_three_halves_eq hd
  calc
    Real.sqrt (spikeSpeed k d) / upperConcreteN d / Real.sqrt (upperConcreteN d) =
        Real.sqrt (spikeSpeed k d) /
          (upperConcreteN d * Real.sqrt (upperConcreteN d)) := by ring
    _ = Real.sqrt (spikeSpeed k d) / upperConcreteN d ^ (3 / 2 : ℝ) := by
      rw [← hN3]

/-- Closed supplier for `UpperConcreteOneLinearMixedWordBound` with the
canonical scalar choices above. -/
theorem upperConcreteOneLinearMixedWordBound_of_canonical_oneL
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    (hk3 : 3 ≤ k) (hε : 0 < eps) :
    UpperConcreteOneLinearMixedWordBound
      (p := p) (q := q) (σ := σ)
      R eps k
      (fun slack d => upperConcreteMixedWordAboundCanonical (p := p) (q := q) (σ := σ) slack d)
      (fun slack d =>
        upperConcreteMixedWordL1boundCanonical (p := p) (q := q) (σ := σ) R eps k slack d) := by
  intro slack hslack
  filter_upwards [eventually_gt_atTop 0] with d hd
  intro X Y hY hdist w hOneL
  have hNpos : 0 < upperConcreteN d := by
    unfold upperConcreteN
    exact PptFactorization.AppendixB.ConcreteModel.D_pos hd
  have hM : 0 ≤ upperConcreteM (p := p) (q := q) (σ := σ) slack d := by
    unfold upperConcreteM
    exact le_max_of_le_left (Real.sqrt_nonneg _)
  let a := upperSlackRadius (spikeRoot k eps) R.lam slack
  have hk_pos : 0 < k := by omega
  have ha : 0 ≤ a :=
    (upperSlackRadius_spike_choice hk_pos R.lam_pos hε slack hslack).1
  let hr : ℝ :=
    sharpSphericalRadius (upperConcreteN d) (spikeSpeed k d) a
  have hA_op :
      opNorm (p := p) (q := q)
        (localBackground (p := p) (q := q) (σ := σ) Y) ≤
        upperConcreteM (p := p) (q := q) (σ := σ) slack d /
          upperConcreteN d :=
    backgroundTypicalSet_gammaOpNorm_bound
      (p := p) (q := q) (σ := σ)
      (N := upperConcreteN d)
      (M := upperConcreteM (p := p) (q := q) (σ := σ) slack d)
      (τ := upperCanonicalTau slack d)
      (mean := upperConcreteMean (p := p) (q := q) (σ := σ) k d)
      (k := k) hY
  have hSampleOp :
      PptFactorization.HighProbabilityBounds.sampleOpNorm
          (p := p) (q := q) (σ := σ) Y ≤
        upperConcreteM (p := p) (q := q) (σ := σ) slack d / Real.sqrt (upperConcreteN d) :=
    backgroundTypicalSet_sampleOpNorm_bound
      (p := p) (q := q) (σ := σ)
      (N := upperConcreteN d)
      (M := upperConcreteM (p := p) (q := q) (σ := σ) slack d)
      (τ := upperCanonicalTau slack d)
      (mean := upperConcreteMean (p := p) (q := q) (σ := σ) k d)
      (k := k) hY
  have hL_frob :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
          (localLinear (p := p) (q := q) (σ := σ) Y (X - Y)) ≤
        upperMixedWordL1bound (p := p) (q := q)
            (upperConcreteN d)
            (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
            (spikeSpeed k d) a /
          Real.sqrt (Fintype.card (BipIndex p q)) := by
    have hL :=
      localLinear_frobeniusNorm_bound_of_sampleOpNorm
        (p := p) (q := q) (σ := σ) (X := X) (Y := Y)
        (N := upperConcreteN d)
        (M := upperConcreteM (p := p) (q := q) (σ := σ) slack d)
        (r := hr) hSampleOp (by simpa [hr, a] using hdist)
    have hcardpos : 0 < (Fintype.card (BipIndex p q) : ℝ) := by
      exact_mod_cast Fintype.card_pos
    calc
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
          (localLinear (p := p) (q := q) (σ := σ) Y (X - Y)) ≤
          2 * (upperConcreteM (p := p) (q := q) (σ := σ) slack d / Real.sqrt (upperConcreteN d)) *
            hr := hL
      _ ≤
          upperMixedWordL1bound (p := p) (q := q)
              (upperConcreteN d)
              (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
              (spikeSpeed k d) a /
            Real.sqrt (Fintype.card (BipIndex p q)) := by
        simp [hr, upperMixedWordL1bound, sharpSphericalRadius, hcardpos.ne']
  have hcore :=
    localWordScaledTraceTerm_oneLinear_le_envelope
      (N := upperConcreteN d)
      (M := upperConcreteM (p := p) (q := q) (σ := σ) slack d)
      (a := a) (speed := spikeSpeed k d)
      (A := localBackground (p := p) (q := q) (σ := σ) Y)
      (L := localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
      (Q := localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
      (w := w) hNpos hM hk3 hA_op hL_frob hOneL
  simpa [upperConcreteMixedWordAboundCanonical, upperConcreteMixedWordL1boundCanonical,
    upperMixedWordAbound, upperMixedWordL1bound, a, BipIndex, Fintype.card_prod] using hcore

/-- Closed scalar supplier for the canonical one-`L` mixed-term limit. -/
theorem upperConcreteOneLinearMixedTermLimit_of_canonical_oneL
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    (hk3 : 3 ≤ k) (hε : 0 < eps) :
    UpperConcreteOneLinearMixedTermLimit
      k
      (fun slack d => upperConcreteMixedWordAboundCanonical (p := p) (q := q) (σ := σ) slack d)
      (fun slack d =>
        upperConcreteMixedWordL1boundCanonical (p := p) (q := q) (σ := σ) R eps k slack d) := by
  intro slack hslack
  let a := upperSlackRadius (spikeRoot k eps) R.lam slack
  have hkpos : 0 < k := by omega
  have ha : 0 ≤ a :=
    (upperSlackRadius_spike_choice hkpos R.lam_pos hε slack hslack).1
  have hlim_ratio :=
    upperConcrete_oneLinearTermRatio_tendsto_zero (k := k) hk3
  have hlim :
      Tendsto
        (fun d =>
          ((upperConcreteM (p := p) (q := q) (σ := σ) slack 0) ^ k *
              Real.sqrt (Fintype.card (BipIndex p q)) * 2 * Real.sqrt a) *
            (Real.sqrt (spikeSpeed k d) / upperConcreteN d ^ (3 / 2 : ℝ)))
        atTop (nhds 0) := by
    simpa using
      hlim_ratio.const_mul
        ((upperConcreteM (p := p) (q := q) (σ := σ) slack 0) ^ k *
          Real.sqrt (Fintype.card (BipIndex p q)) * 2 * Real.sqrt a)
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with d hd
  have hNpos : 0 < upperConcreteN d := by
    unfold upperConcreteN
    exact PptFactorization.AppendixB.ConcreteModel.D_pos hd
  have hNne : upperConcreteN d ≠ 0 := ne_of_gt hNpos
  have hNpow :
      upperConcreteN d ^ (k - 1) * (upperConcreteN d)⁻¹ ^ (k - 1) = 1 := by
    rw [← mul_pow]
    field_simp [hNne]
    simp
  have hdivpow :
      (upperConcreteM (p := p) (q := q) (σ := σ) slack d / upperConcreteN d) ^
          (k - 1) =
        upperConcreteM (p := p) (q := q) (σ := σ) slack 0 ^ (k - 1) *
          (upperConcreteN d)⁻¹ ^ (k - 1) := by
    simp [upperConcreteM, div_eq_mul_inv, mul_pow]
  have hsharp :
      sharpSphericalRadius (upperConcreteN d) (spikeSpeed k d) a =
        Real.sqrt a * Real.sqrt (spikeSpeed k d) / upperConcreteN d := by
    simp [sharpSphericalRadius, sharpSphericalRadiusSq, Real.sqrt_mul, ha,
      Real.sqrt_sq (le_of_lt hNpos), sq_nonneg]
  have hM :
      upperConcreteM (p := p) (q := q) (σ := σ) slack d =
        upperConcreteM (p := p) (q := q) (σ := σ) slack 0 := rfl
  have hdivpowOneL :
      (upperConcreteM (p := p) (q := q) (σ := σ) slack 0 / upperConcreteN d) ^
          (k - 1) =
        upperConcreteM (p := p) (q := q) (σ := σ) slack 0 ^ (k - 1) *
          (upperConcreteN d)⁻¹ ^ (k - 1) := by
    simp [upperConcreteM, div_eq_mul_inv, mul_pow]
  have hEq :
      upperConcreteN d ^ (k - 1) *
          upperConcreteMixedWordAboundCanonical (p := p) (q := q) (σ := σ) slack d ^ (k - 1) *
        upperConcreteMixedWordL1boundCanonical (p := p) (q := q) (σ := σ) R eps k slack d =
        (upperConcreteM (p := p) (q := q) (σ := σ) slack 0 ^ k *
            Real.sqrt (Fintype.card (BipIndex p q)) * 2 * Real.sqrt a) *
          (Real.sqrt (spikeSpeed k d) / upperConcreteN d ^ (3 / 2 : ℝ)) := by
    simp only [upperConcreteMixedWordAboundCanonical, upperConcreteMixedWordL1boundCanonical,
      upperMixedWordAbound, upperMixedWordL1bound, a, BipIndex, Fintype.card_prod, hsharp]
    rw [hM, hdivpowOneL]
    rw [show
        upperConcreteN d ^ (k - 1) *
            (upperConcreteM (p := p) (q := q) (σ := σ) slack 0 ^ (k - 1) *
              (upperConcreteN d)⁻¹ ^ (k - 1)) =
          upperConcreteM (p := p) (q := q) (σ := σ) slack 0 ^ (k - 1) *
            (upperConcreteN d ^ (k - 1) * (upperConcreteN d)⁻¹ ^ (k - 1)) by ring]
    rw [hNpow]
    ring_nf
    have hMpow :
        upperConcreteM (p := p) (q := q) (σ := σ) slack 0 ^ k =
          upperConcreteM (p := p) (q := q) (σ := σ) slack 0 *
            upperConcreteM (p := p) (q := q) (σ := σ) slack 0 ^ (k - 1) := by
      cases k with
      | zero => exact absurd hkpos (by decide : ¬0 < 0)
      | succ n =>
        simp [pow_succ, Nat.succ_sub_one]
        ring
    rw [hMpow]
    rw [upperConcreteN_pow_three_halves_eq hd]
    ring
  exact hEq.symm

/-- Closed supplier for `UpperConcreteMultiDefectMixedWordBound` with the
canonical scalar choices above. -/
theorem upperConcreteMultiDefectMixedWordBound_of_canonical_multi
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    (hk3 : 3 ≤ k) (hε : 0 < eps) :
    UpperConcreteMultiDefectMixedWordBound
      (p := p) (q := q) (σ := σ)
      R eps k
      (fun slack d => upperConcreteMixedWordAboundCanonical (p := p) (q := q) (σ := σ) slack d)
      (fun slack d =>
        upperConcreteMixedWordL2boundCanonical (p := p) (q := q) (σ := σ) R eps k slack d)
      (fun slack d =>
        upperConcreteMixedWordQ2boundCanonical (p := p) (q := q) (σ := σ) R eps k slack d) := by
  intro slack hslack
  filter_upwards [eventually_gt_atTop 0] with d hd
  intro X Y hY hdist w hmix hNotOneL hNotOneQ
  have hNpos : 0 < upperConcreteN d := by
    unfold upperConcreteN
    exact PptFactorization.AppendixB.ConcreteModel.D_pos hd
  have hM : 0 ≤ upperConcreteM (p := p) (q := q) (σ := σ) slack d := by
    unfold upperConcreteM
    exact le_max_of_le_left (Real.sqrt_nonneg _)
  let a := upperSlackRadius (spikeRoot k eps) R.lam slack
  have hk_pos : 0 < k := by omega
  have ha : 0 ≤ a :=
    (upperSlackRadius_spike_choice hk_pos R.lam_pos hε slack hslack).1
  let hr : ℝ :=
    sharpSphericalRadius (upperConcreteN d) (spikeSpeed k d) a
  have hA_op :
      opNorm (p := p) (q := q)
        (localBackground (p := p) (q := q) (σ := σ) Y) ≤
        upperConcreteM (p := p) (q := q) (σ := σ) slack d /
          upperConcreteN d :=
    backgroundTypicalSet_gammaOpNorm_bound
      (p := p) (q := q) (σ := σ)
      (N := upperConcreteN d)
      (M := upperConcreteM (p := p) (q := q) (σ := σ) slack d)
      (τ := upperCanonicalTau slack d)
      (mean := upperConcreteMean (p := p) (q := q) (σ := σ) k d)
      (k := k) hY
  have hSampleOp :
      PptFactorization.HighProbabilityBounds.sampleOpNorm
          (p := p) (q := q) (σ := σ) Y ≤
        upperConcreteM (p := p) (q := q) (σ := σ) slack d / Real.sqrt (upperConcreteN d) :=
    backgroundTypicalSet_sampleOpNorm_bound
      (p := p) (q := q) (σ := σ)
      (N := upperConcreteN d)
      (M := upperConcreteM (p := p) (q := q) (σ := σ) slack d)
      (τ := upperCanonicalTau slack d)
      (mean := upperConcreteMean (p := p) (q := q) (σ := σ) k d)
      (k := k) hY
  have hL_frob :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
          (localLinear (p := p) (q := q) (σ := σ) Y (X - Y)) ≤
        upperMixedWordL2bound (p := p) (q := q)
          (upperConcreteN d)
          (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
          (spikeSpeed k d) a := by
    have hL :=
      localLinear_frobeniusNorm_bound_of_sampleOpNorm
        (p := p) (q := q) (σ := σ) (X := X) (Y := Y)
        (N := upperConcreteN d)
        (M := upperConcreteM (p := p) (q := q) (σ := σ) slack d)
        (r := hr) hSampleOp (by simpa [hr, a] using hdist)
    calc
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
          (localLinear (p := p) (q := q) (σ := σ) Y (X - Y)) ≤
          2 * (upperConcreteM (p := p) (q := q) (σ := σ) slack d / Real.sqrt (upperConcreteN d)) *
            hr := hL
      _ ≤ upperMixedWordL2bound (p := p) (q := q)
          (upperConcreteN d)
          (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
          (spikeSpeed k d) a := by
        have hcardpos : 0 < (Fintype.card (BipIndex p q) : ℝ) := by exact_mod_cast Fintype.card_pos
        have hcard1 : (1 : ℝ) ≤ Real.sqrt (Fintype.card (BipIndex p q)) := by
          rw [← Real.sqrt_one]
          apply Real.sqrt_le_sqrt
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Fintype.card_pos (α := BipIndex p q)).ne'
        have hstep_nonneg :
            0 ≤
              2 * (upperConcreteM (p := p) (q := q) (σ := σ) slack d / Real.sqrt (upperConcreteN d)) *
                hr := by
          simp [hr, sharpSphericalRadius]
          positivity
        calc
          2 * (upperConcreteM (p := p) (q := q) (σ := σ) slack d / Real.sqrt (upperConcreteN d)) *
              hr ≤
            Real.sqrt (Fintype.card (BipIndex p q)) *
              (2 * (upperConcreteM (p := p) (q := q) (σ := σ) slack d / Real.sqrt (upperConcreteN d)) *
                hr) := by
            exact le_mul_of_one_le_left hstep_nonneg hcard1
          _ = upperMixedWordL2bound (p := p) (q := q)
              (upperConcreteN d)
              (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
              (spikeSpeed k d) a := by
            simp [upperMixedWordL2bound, upperMixedWordL1bound, hr, sharpSphericalRadius]
  have hQ_frob :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
          (localQuadratic (p := p) (q := q) (σ := σ) (X - Y)) ≤
        upperMixedWordQ1bound (p := p) (q := q)
            (upperConcreteN d) (spikeSpeed k d) a /
          Real.sqrt (Fintype.card (BipIndex p q)) := by
    have hQ :=
      localQuadratic_frobeniusNorm_bound_of_radius
        (p := p) (q := q) (σ := σ) (X := X) (Y := Y)
        (r := hr) (by simpa [hr, a] using hdist)
    have hcardpos : 0 < (Fintype.card (BipIndex p q) : ℝ) := by
      exact_mod_cast Fintype.card_pos
    unfold upperMixedWordQ1bound
    rw [div_eq_mul_inv]
    field_simp [hcardpos.ne']
    exact hQ
  have hcore :=
    localWordScaledTraceTerm_multiDefect_le_envelope
      (N := upperConcreteN d)
      (M := upperConcreteM (p := p) (q := q) (σ := σ) slack d)
      (a := a) (speed := spikeSpeed k d)
      (A := localBackground (p := p) (q := q) (σ := σ) Y)
      (L := localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
      (Q := localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
      (w := w) hNpos hM ha hA_op hL_frob hQ_frob hmix hNotOneL hNotOneQ
  simpa [upperConcreteMixedWordAboundCanonical, upperConcreteMixedWordL2boundCanonical,
    upperConcreteMixedWordQ2boundCanonical, upperMixedWordAbound, upperMixedWordL2bound,
    upperMixedWordQ2bound, upperMixedWordQ1bound, a, BipIndex, Fintype.card_prod] using hcore

theorem upperConcrete_natCast_rpow_neg_tendsto_zero {e : ℝ} (he : e < 0) :
    Tendsto (fun d : ℕ => (d : ℝ) ^ e) atTop (nhds 0) := by
  have hneg : 0 < -e := by linarith
  refine ((tendsto_rpow_neg_atTop hneg).comp tendsto_natCast_atTop_atTop).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with d hd
  simp only [Function.comp_apply, neg_neg]

theorem upperConcrete_multiDefectCanonicalExponent_neg
    {k : ℕ} (hk3 : 3 ≤ k) {w : Fin k → LocalExpansionLetter}
    (hmix : localWordIsMixed w) :
    (-2 : ℝ) + (localWordLetterCount LocalExpansionLetter.L w +
      2 * localWordLetterCount LocalExpansionLetter.Q w) / (k : ℝ) < 0 := by
  set nA := localWordLetterCount LocalExpansionLetter.A w
  set nL := localWordLetterCount LocalExpansionLetter.L w
  set nQ := localWordLetterCount LocalExpansionLetter.Q w
  have htotal : nA + nL + nQ = k := localWordLetterCount_total w
  have hkR : (0 : ℝ) < k := by exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 3) hk3
  have haux : 1 ≤ 2 * nA + nL := by
    by_contra h
    push_neg at h
    have h0 : nA = 0 ∧ nL = 0 := by omega
    rcases h0 with ⟨hnA0, hnL0⟩
    have hpureQ : localWordIsPure LocalExpansionLetter.Q w := by
      have hAllQ : ∀ i, w i = LocalExpansionLetter.Q := by
        intro i
        cases hw : w i with
        | A =>
            have hpos :=
              lower_localWordLetterCount_pos_of_exists
                (letter := LocalExpansionLetter.A) (w := w) ⟨i, hw⟩
            omega
        | L =>
            have hpos :=
              lower_localWordLetterCount_pos_of_exists
                (letter := LocalExpansionLetter.L) (w := w) ⟨i, hw⟩
            omega
        | Q => rfl
      rw [localWordIsPure_Q_iff_eq_pureQ]
      ext i
      exact hAllQ i
    exact hmix.2 hpureQ
  have hbound : nL + 2 * nQ ≤ 2 * k - 1 := by omega
  have hlt : (nL + 2 * nQ : ℝ) < 2 * k := by exact_mod_cast (by omega : nL + 2 * nQ < 2 * k)
  have hratio : (nL + 2 * nQ : ℝ) / k < 2 := by
    rw [div_lt_iff₀ hkR]
    linarith
  linarith

theorem upperConcreteMultiDefectMixedTermLimit_of_canonical_multi
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    (hk3 : 3 ≤ k) (hε : 0 < eps) :
    UpperConcreteMultiDefectMixedTermLimit
      k
      (fun slack d => upperConcreteMixedWordAboundCanonical (p := p) (q := q) (σ := σ) slack d)
      (fun slack d =>
        upperConcreteMixedWordL2boundCanonical (p := p) (q := q) (σ := σ) R eps k slack d)
      (fun slack d =>
        upperConcreteMixedWordQ2boundCanonical (p := p) (q := q) (σ := σ) R eps k slack d) := by
  intro slack hslack w hmix hNotOneL hNotOneQ
  set nA := localWordLetterCount LocalExpansionLetter.A w
  set nL := localWordLetterCount LocalExpansionLetter.L w
  set nQ := localWordLetterCount LocalExpansionLetter.Q w
  let a := upperSlackRadius (spikeRoot k eps) R.lam slack
  have hkpos : 0 < k := by omega
  have ha : 0 ≤ a :=
    (upperSlackRadius_spike_choice hkpos R.lam_pos hε slack hslack).1
  let hexp := (-2 : ℝ) + (nL + 2 * nQ) / (k : ℝ)
  have hexp_neg :=
    upperConcrete_multiDefectCanonicalExponent_neg (k := k) hk3 hmix
  let C :=
    upperConcreteM (p := p) (q := q) (σ := σ) slack 0 ^ (nA + nL) *
      Real.sqrt (Fintype.card (BipIndex p q)) ^ (nL + nQ) *
        (2 * Real.sqrt a) ^ nL * a ^ nQ
  have hlim := by
    simpa [mul_zero] using
      (upperConcrete_natCast_rpow_neg_tendsto_zero hexp_neg).const_mul C
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with d hd
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hNne : upperConcreteN d ≠ 0 := ne_of_gt (by
    unfold upperConcreteN
    exact PptFactorization.AppendixB.ConcreteModel.D_pos hd)
  have hspeed_nonneg : 0 ≤ spikeSpeed k d := by
    unfold spikeSpeed
    exact Real.rpow_nonneg (Nat.cast_nonneg d) _
  have hsharp :
      sharpSphericalRadius (upperConcreteN d) (spikeSpeed k d) a ^ 2 =
        sharpSphericalRadiusSq (upperConcreteN d) (spikeSpeed k d) a :=
    sharpSphericalRadius_sq (N := upperConcreteN d) (speed := spikeSpeed k d)
      (a := a) ha hspeed_nonneg
  have hEq :
      C * (d : ℝ) ^ hexp =
        upperConcreteN d ^ (k - 1) *
          upperConcreteMixedWordAboundCanonical (p := p) (q := q) (σ := σ) slack d ^ nA *
          upperConcreteMixedWordL2boundCanonical (p := p) (q := q) (σ := σ) R eps k slack d ^ nL *
          upperConcreteMixedWordQ2boundCanonical (p := p) (q := q) (σ := σ) R eps k slack d ^ nQ := by
    simp only [upperConcreteMixedWordAboundCanonical, upperConcreteMixedWordL2boundCanonical,
      upperConcreteMixedWordQ2boundCanonical, upperMixedWordAbound, upperMixedWordL2bound,
      upperMixedWordL1bound, upperMixedWordQ2bound, upperMixedWordQ1bound, upperConcreteM,
      upperConcreteN, BipIndex, Fintype.card_prod, a, spikeSpeed,
      sharpSphericalRadius, sharpSphericalRadiusSq, PptFactorization.AppendixB.ConcreteModel.D_eq]
    have hsqrtN : Real.sqrt ((d : ℝ) ^ (2 : ℕ)) = (d : ℝ) :=
      Real.sqrt_sq (le_of_lt hdR)
    rw [hsqrtN]
    have hden : ((d : ℝ) ^ (2 : ℕ)) ^ 2 = (d : ℝ) ^ (4 : ℕ) := by
      rw [pow_mul (d : ℝ) 2 2]
    rw [hden]
    have hratio_nonneg : 0 ≤ a * (d : ℝ) ^ (2 + 2 / (k : ℝ)) / (d : ℝ) ^ (4 : ℕ) := by positivity
    rw [show (Real.sqrt (a * (d : ℝ) ^ (2 + 2 / (k : ℝ)) / (d : ℝ) ^ (4 : ℕ))) ^ 2 =
        a * (d : ℝ) ^ (2 + 2 / (k : ℝ)) / (d : ℝ) ^ (4 : ℕ) from Real.sq_sqrt hratio_nonneg]
    have hspeed :
        Real.sqrt (a * (d : ℝ) ^ (2 + 2 / (k : ℝ)) / (d : ℝ) ^ (4 : ℕ)) =
          Real.sqrt a * (d : ℝ) ^ (1 + 1 / (k : ℝ)) / (d : ℝ) ^ 2 := by
      have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
      simp [Real.sqrt_mul, ha, le_of_lt hdR]
      field_simp [hdR.ne', ne_of_gt hkR]
      rw [show (2 : ℝ) * ((k : ℝ) + 1) / (k : ℝ) = 2 + 2 / (k : ℝ) from by
        field_simp [ne_of_gt hkR]]
      rw [show ((k : ℝ) + 1) / (k : ℝ) = 1 + 1 / (k : ℝ) from by
        field_simp [ne_of_gt hkR]]
      have hd4 : Real.sqrt ((d : ℝ) ^ (4 : ℕ)) = (d : ℝ) ^ 2 := by
        have h : (d : ℝ) ^ (4 : ℕ) = ((d : ℝ) ^ 2) ^ 2 := by norm_cast; ring
        rw [h]
        exact Real.sqrt_sq (by positivity : 0 ≤ (d : ℝ) ^ 2)
      have hratio :
          Real.sqrt ((d : ℝ) ^ (2 + 2 / (k : ℝ))) = (d : ℝ) ^ (1 + 1 / (k : ℝ)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hdR)]
        field_simp [ne_of_gt hkR]
      rw [hratio, hd4]
      ring
    rw [hspeed]
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
    have htotal : (nA + nL + nQ : ℝ) = (k : ℝ) := by exact_mod_cast (localWordLetterCount_total w)
    let hpowExp :=
      2 * ((k : ℝ) - 1) + (-2 : ℝ) * nA + (-3 : ℝ) * nL + (-4 : ℝ) * nQ +
        nL * (1 + 1 / (k : ℝ)) + nQ * (2 + 2 / (k : ℝ))
    have hpow : hexp = hpowExp := by
      dsimp [hexp, hpowExp]
      field_simp [ne_of_gt hkR]
      rw [show (k : ℝ) = nA + nL + nQ from htotal.symm]
      ring_nf
    have hd :
        (d : ℝ) ^ (2 * ((k : ℝ) - 1)) * (d : ℝ) ^ ((-2 : ℝ) * nA) * (d : ℝ) ^ ((-3 : ℝ) * nL) *
            (d : ℝ) ^ ((-4 : ℝ) * nQ) * (d : ℝ) ^ (nL * (1 + 1 / (k : ℝ))) *
            (d : ℝ) ^ (nQ * (2 + 2 / (k : ℝ))) =
          (d : ℝ) ^ hpowExp := by
      rw [Real.rpow_add hdR, Real.rpow_add hdR, Real.rpow_add hdR, Real.rpow_add hdR,
        Real.rpow_add hdR]
    rw [hpow]
    ring_nf
    rw [← hd]
    dsimp [C]
    simp [a, upperConcreteM, pow_add, mul_pow]
    have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkR
    have hrhs_pow (t : ℕ) : ((d : ℝ) ^ t)⁻¹ = (d : ℝ) ^ (-((t : ℝ))) := by
      simpa [Real.rpow_natCast] using
        Real.inv_rpow (le_of_lt hdR).le (t : ℝ) (Nat.cast_nonneg t)
    conv_rhs =>
      rw [hrhs_pow (nA * 2), hrhs_pow (nL * 3), hrhs_pow (nQ * 4)]
      rw [show (1 + (↑k)⁻¹) = (1 + 1 / (k : ℝ)) from by field_simp [hkne]]
      rw [show (2 + (↑k)⁻¹ * 2) = (2 + 2 / (k : ℝ)) from by field_simp [hkne]]
      rw [show ((d : ℝ) ^ (1 + 1 / (k : ℝ))) ^ nL =
          (d : ℝ) ^ (nL * (1 + 1 / (k : ℝ))) from by
        calc
          ((d : ℝ) ^ (1 + 1 / (k : ℝ))) ^ nL =
              (d : ℝ) ^ ((1 + 1 / (k : ℝ)) * nL) :=
            (Real.rpow_mul_natCast hdR.le (1 + 1 / (k : ℝ)) nL).symm
          _ = (d : ℝ) ^ (nL * (1 + 1 / (k : ℝ))) := by
            congr 1
            ring]
      rw [show ((d : ℝ) ^ (2 + 2 / (k : ℝ))) ^ nQ =
          (d : ℝ) ^ (nQ * (2 + 2 / (k : ℝ))) from by
        calc
          ((d : ℝ) ^ (2 + 2 / (k : ℝ))) ^ nQ =
              (d : ℝ) ^ ((2 + 2 / (k : ℝ)) * nQ) :=
            (Real.rpow_mul_natCast hdR.le (2 + 2 / (k : ℝ)) nQ).symm
          _ = (d : ℝ) ^ (nQ * (2 + 2 / (k : ℝ))) := by
            congr 1
            ring]
    rw [show (d : ℝ) ^ (2 * ((k : ℝ) - 1)) =
        (d : ℝ) ^ (-2 + (k : ℝ) * 2) from by
      congr 1
      ring_nf]
    conv_rhs =>
      rw [show (d : ℝ) ^ ((k - 1) * 2) =
          (d : ℝ) ^ (-2 + (k : ℝ) * 2) from by
        rw [← Real.rpow_natCast (d : ℝ) ((k - 1) * 2)]
        have hkone : 1 ≤ k := Nat.succ_le_of_lt hkpos
        congr 1
        norm_num [Nat.cast_mul, Nat.cast_sub hkone]
        ring_nf]
    rw [show (d : ℝ) ^ (-((nA * 2 : ℕ) : ℝ)) = (d : ℝ) ^ ((-2 : ℝ) * nA) from by
      congr 1; norm_num [Nat.cast_mul]; ring]
    rw [show (d : ℝ) ^ (-((nL * 3 : ℕ) : ℝ)) = (d : ℝ) ^ ((-3 : ℝ) * nL) from by
      congr 1; norm_num [Nat.cast_mul]; ring]
    rw [show (d : ℝ) ^ (-((nQ * 4 : ℕ) : ℝ)) = (d : ℝ) ^ ((-4 : ℝ) * nQ) from by
      congr 1; norm_num [Nat.cast_mul]; ring]
    ring_nf
  exact hEq

/-- Unpack the isolated concrete mixed-word estimate into the raw pipeline
shape. -/
theorem upper_hWordBound_of_upperConcreteMixedWordBound
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    {R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime}
    {eps : ℝ} {k : ℕ}
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hWordBound :
      UpperConcreteMixedWordBound
        (p := p) (q := q) (σ := σ)
        R eps k Abound L2bound L1bound Q2bound Q1bound) :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        ∀ ⦃X Y : SampleMatrix p q σ⦄,
          Y ∈ backgroundTypicalSet
              (p := p) (q := q) (σ := σ)
              (upperConcreteN d)
              (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
              (upperCanonicalTau slack d)
              (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k →
          frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
            sharpSphericalRadius
              (upperConcreteN d) (spikeSpeed k d)
              (upperSlackRadius (spikeRoot k eps) R.lam slack) →
          ∀ w : Fin k → LocalExpansionLetter,
            localWordIsMixed w →
              |localWordScaledTraceTerm
                  (p := p) (q := q)
                  (upperConcreteN d)
                  (localBackground (p := p) (q := q) (σ := σ) Y)
                  (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                  (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
                  w| ≤
                localExpansionMixedWordEnvelopeTerm
                  (upperConcreteN d) (Abound slack d) (L2bound slack d)
                  (L1bound slack d) (Q2bound slack d) (Q1bound slack d) k w :=
  hWordBound

/-- Unpack the isolated scalar mixed-word envelope limits. -/
theorem upper_hTermLimit_of_upperConcreteMixedTermLimit
    {k : ℕ}
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hTermLimit :
      UpperConcreteMixedTermLimit
        k Abound L2bound L1bound Q2bound Q1bound) :
    ∀ slack : ℝ, 0 < slack →
      ∀ w : Fin k → LocalExpansionLetter,
        localWordIsMixed w →
          Tendsto
            (fun d =>
              localExpansionMixedWordEnvelopeTerm
                (upperConcreteN d) (Abound slack d) (L2bound slack d)
                (L1bound slack d) (Q2bound slack d) (Q1bound slack d) k w)
            atTop (nhds 0) :=
  hTermLimit

/-- Next-layer concrete upper closure using moment concentration and the two
normalized Gaussian operator-tail estimates, instead of a prepackaged
`ConcreteSphericalBackgroundBadSetBounds` assumption.

This is the current proof-ready upper endpoint: it chooses all concrete scalar
sequences, closes `hIso` from the full spherical isoperimetric theorem plus the
dimension bridge, closes `hK_half` from moment/sample/gamma bad-event bounds,
closes `hMixed` from mixed-word estimates, and then calls the bundled concrete
upper closure.

The remaining visible inputs are now:

* `hp`, positivity of the concrete target probability;
* `hFullIso` and `hIsoRealDim`, the geometric input and the fixed-type/scalar
  dimension bridge;
* `hMoment`, `hSampleTail`, `hGammaTail`, and `hBad`, the concrete
  background-typicality estimates;
* `hWordBound` and `hTermLimit`, the deterministic mixed-remainder analysis. -/
theorem upper_eventual_from_concrete_sequences_of_fullIso_momentOperatorTails_mixedWords
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {bMoment bSample bGamma
      Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hp :
      ∀ᶠ d in atTop,
        0 < upperConcreteTargetProb
          (p := p) (q := q) (σ := σ) eps k d)
    (hFullIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hMoment :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := p) (q := q) (σ := σ)).real
            (backgroundMomentBadSet
              (p := p) (q := q) (σ := σ)
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean (p := p) (q := q) (σ := σ) k d)
              k) ≤ bMoment slack d)
    (hSampleTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (gaussianMeasure p q σ).real
            ((normalizedSampleOpNormEvent
              (p := p) (q := q) (σ := σ)
              (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
              (d : ℝ))ᶜ) ≤
            bSample slack d)
    (hGammaTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (gaussianMeasure p q σ).real
            ((normalizedRhoGammaOpNormEvent
              (p := p) (q := q) (σ := σ)
              (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
              (d : ℝ))ᶜ) ≤
            bGamma slack d)
    (hBad :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          bMoment slack d + bSample slack d + bGamma slack d ≤ 1 / 2)
    (hWordBound :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y : SampleMatrix p q σ⦄,
            Y ∈ backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d)
                (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
                (upperCanonicalTau slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k →
            frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed k d)
                (upperSlackRadius (spikeRoot k eps) R.lam slack) →
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                |localWordScaledTraceTerm
                    (p := p) (q := q)
                    (upperConcreteN d)
                    (localBackground (p := p) (q := q) (σ := σ) Y)
                    (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                    (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
                    w| ≤
                  localExpansionMixedWordEnvelopeTerm
                    (upperConcreteN d) (Abound slack d) (L2bound slack d)
                    (L1bound slack d) (Q2bound slack d) (Q1bound slack d) k w)
    (hTermLimit :
      ∀ slack : ℝ, 0 < slack →
        ∀ w : Fin k → LocalExpansionLetter,
          localWordIsMixed w →
            Tendsto
              (fun d =>
                localExpansionMixedWordEnvelopeTerm
                  (upperConcreteN d) (Abound slack d) (L2bound slack d)
                  (L1bound slack d) (Q2bound slack d) (Q1bound slack d) k w)
              atTop (nhds 0)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  let hk : 0 < k := upper_hk_of_hk3 hk3
  have hk1 : 1 ≤ k := le_trans (by norm_num : 1 ≤ 3) hk3
  have hIso :
      ∀ᶠ d in atTop,
        SharpSphericalIsoperimetry
          (p := p) (q := q) (σ := σ)
          (upperConcreteSphericalMu (p := p) (q := q) (σ := σ) d)
          (upperConcreteRealDim R d) :=
    upper_hIso_concrete_sequences_of_fullSphericalIsoperimetry
      (p := p) (q := q) (σ := σ) R hFullIso hIsoRealDim
  have hK_half :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          1 / 2 ≤
            (upperConcreteSphericalMu (p := p) (q := q) (σ := σ) d).real
              (backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d)
                (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
                (upperCanonicalTau slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d)
                k) := by
    refine
      upper_hK_half_of_sphericalModelMeasure_moment_and_operator_tails
        (p := p) (q := q) (σ := σ)
        (μ := upperConcreteSphericalMu (p := p) (q := q) (σ := σ))
        (N := upperConcreteN)
        (ambientDim := fun d : ℕ => (d : ℝ))
        (M := upperConcreteM (p := p) (q := q) (σ := σ))
        (τ := upperCanonicalTau)
        (mean := fun _ d =>
          upperConcreteMean (p := p) (q := q) (σ := σ) k d)
        (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
        (k := k) ?_ upperConcreteAmbientDim_pos_eventually
        upperConcreteN_eq_ambientDim_sq_eventually
        hMoment hSampleTail hGammaTail hBad
    exact Eventually.of_forall fun d => rfl
  have hMixed :
      ∀ slack : ℝ, 0 < slack →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ d in atTop,
            ∀ ⦃X Y : SampleMatrix p q σ⦄,
              Y ∈ backgroundTypicalSet
                  (p := p) (q := q) (σ := σ)
                  (upperConcreteN d)
                  (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
                  (upperCanonicalTau slack d)
                  (upperConcreteMean (p := p) (q := q) (σ := σ) k d)
                  k →
              frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
                sharpSphericalRadius
                  (upperConcreteN d) (spikeSpeed k d)
                  (upperSlackRadius (spikeRoot k eps) R.lam slack) →
              |localExpansionMixedRemainder (p := p) (q := q)
                  (upperConcreteN d) k
                  (localBackground (p := p) (q := q) (σ := σ) Y)
                  (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                  (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))| ≤ η :=
    upper_hMixed_from_uniform_mixedWordBounds_and_termLimits
      (p := p) (q := q) (σ := σ)
      (N := upperConcreteN)
      (speed := spikeSpeed k)
      (aSlack := fun slack =>
        upperSlackRadius (spikeRoot k eps) R.lam slack)
      (M := upperConcreteM (p := p) (q := q) (σ := σ))
      (τ := upperCanonicalTau)
      (mean := fun _ d =>
        upperConcreteMean (p := p) (q := q) (σ := σ) k d)
      (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
      (Q2bound := Q2bound) (Q1bound := Q1bound)
      (k := k) hk1 hWordBound hTermLimit
  exact
    upper_eventual_from_concrete_sequences_localExpansion_scalarLimits
      (p := p) (q := q) (σ := σ)
      R hk3 hε hp hIso hK_half hMixed

/-- Canonical-scalar concrete upper endpoint with target positivity specialized
to the actual one-sided upper event.

This is the one-sided version of
`upper_eventual_from_concrete_sequences_of_fullIso_momentOperatorTails_mixedWords`.
It keeps the concrete scalar choices already made there:

* `aSlack slack = upperSlackRadius (spikeRoot k eps) R.lam slack`;
* `etaSlack = upperCanonicalEtaSlack k eps R.lam`;
* `τ = upperCanonicalTau`;
* `M = upperConcreteM`.

The raw eventual positivity hypothesis `hp` is replaced by the meaningful
supplier `UpperConcreteOneSidedPositiveDeviationWitness`; the conversion to
the absolute-deviation target probability is handled by
`upper_hp_of_upperConcreteOneSidedPositiveDeviationWitness`. -/
theorem upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_momentOperatorTails_mixedWords
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {bMoment bSample bGamma
      Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hOneSided :
      UpperConcreteOneSidedPositiveDeviationWitness
        (p := p) (q := q) (σ := σ) eps k)
    (hFullIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hMoment :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := p) (q := q) (σ := σ)).real
            (backgroundMomentBadSet
              (p := p) (q := q) (σ := σ)
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean (p := p) (q := q) (σ := σ) k d)
              k) ≤ bMoment slack d)
    (hSampleTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (gaussianMeasure p q σ).real
            ((normalizedSampleOpNormEvent
              (p := p) (q := q) (σ := σ)
              (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
              (d : ℝ))ᶜ) ≤
            bSample slack d)
    (hGammaTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (gaussianMeasure p q σ).real
            ((normalizedRhoGammaOpNormEvent
              (p := p) (q := q) (σ := σ)
              (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
              (d : ℝ))ᶜ) ≤
            bGamma slack d)
    (hBad :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          bMoment slack d + bSample slack d + bGamma slack d ≤ 1 / 2)
    (hWordBound :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y : SampleMatrix p q σ⦄,
            Y ∈ backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d)
                (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
                (upperCanonicalTau slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k →
            frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed k d)
                (upperSlackRadius (spikeRoot k eps) R.lam slack) →
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                |localWordScaledTraceTerm
                    (p := p) (q := q)
                    (upperConcreteN d)
                    (localBackground (p := p) (q := q) (σ := σ) Y)
                    (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                    (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
                    w| ≤
                  localExpansionMixedWordEnvelopeTerm
                    (upperConcreteN d) (Abound slack d) (L2bound slack d)
                    (L1bound slack d) (Q2bound slack d) (Q1bound slack d) k w)
    (hTermLimit :
      ∀ slack : ℝ, 0 < slack →
        ∀ w : Fin k → LocalExpansionLetter,
          localWordIsMixed w →
            Tendsto
              (fun d =>
                localExpansionMixedWordEnvelopeTerm
                  (upperConcreteN d) (Abound slack d) (L2bound slack d)
                  (L1bound slack d) (Q2bound slack d) (Q1bound slack d) k w)
              atTop (nhds 0)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_sequences_of_fullIso_momentOperatorTails_mixedWords
    (p := p) (q := q) (σ := σ) R
    (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
    (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
    (Q2bound := Q2bound) (Q1bound := Q1bound)
    hk3 hε
    (upper_hp_of_upperConcreteOneSidedPositiveDeviationWitness
      (p := p) (q := q) (σ := σ) hOneSided)
    hFullIso hIsoRealDim hMoment hSampleTail hGammaTail hBad
    hWordBound hTermLimit

/-- Canonical mixed-word specialization of
`upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_momentOperatorTails_mixedWords`.

This closes the deterministic mixed-remainder word bound and scalar term-limit
inputs on the canonical route by using the one-linear, one-quadratic, and
multi-defect suppliers. -/
theorem upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_momentOperatorTails_canonicalMixedWords
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {bMoment bSample bGamma : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hOneSided :
      UpperConcreteOneSidedPositiveDeviationWitness
        (p := p) (q := q) (σ := σ) eps k)
    (hFullIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hMoment :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := p) (q := q) (σ := σ)).real
            (backgroundMomentBadSet
              (p := p) (q := q) (σ := σ)
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean (p := p) (q := q) (σ := σ) k d)
              k) ≤ bMoment slack d)
    (hSampleTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (gaussianMeasure p q σ).real
            ((normalizedSampleOpNormEvent
              (p := p) (q := q) (σ := σ)
              (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
              (d : ℝ))ᶜ) ≤
            bSample slack d)
    (hGammaTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (gaussianMeasure p q σ).real
            ((normalizedRhoGammaOpNormEvent
              (p := p) (q := q) (σ := σ)
              (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
              (d : ℝ))ᶜ) ≤
            bGamma slack d)
    (hBad :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          bMoment slack d + bSample slack d + bGamma slack d ≤ 1 / 2) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_momentOperatorTails_mixedWords
    (p := p) (q := q) (σ := σ) R
    (bMoment := bMoment) (bSample := bSample) (bGamma := bGamma)
    (Abound := fun slack d =>
      upperConcreteMixedWordAboundCanonical (p := p) (q := q) (σ := σ) slack d)
    (L2bound := fun slack d =>
      upperConcreteMixedWordL2boundCanonical (p := p) (q := q) (σ := σ) R eps k slack d)
    (L1bound := fun slack d =>
      upperConcreteMixedWordL1boundCanonical (p := p) (q := q) (σ := σ) R eps k slack d)
    (Q2bound := fun slack d =>
      upperConcreteMixedWordQ2boundCanonical (p := p) (q := q) (σ := σ) R eps k slack d)
    (Q1bound := fun slack d =>
      upperConcreteMixedWordQ1boundCanonical (p := p) (q := q) (σ := σ) R eps k slack d)
    hk3 hε hOneSided hFullIso hIsoRealDim hMoment hSampleTail hGammaTail hBad
    (upper_hWordBound_of_upperConcreteMixedWordBound
      (p := p) (q := q) (σ := σ)
      (R := R) (eps := eps) (k := k)
      (Abound := fun slack d =>
        upperConcreteMixedWordAboundCanonical (p := p) (q := q) (σ := σ) slack d)
      (L2bound := fun slack d =>
        upperConcreteMixedWordL2boundCanonical (p := p) (q := q) (σ := σ) R eps k slack d)
      (L1bound := fun slack d =>
        upperConcreteMixedWordL1boundCanonical (p := p) (q := q) (σ := σ) R eps k slack d)
      (Q2bound := fun slack d =>
        upperConcreteMixedWordQ2boundCanonical (p := p) (q := q) (σ := σ) R eps k slack d)
      (Q1bound := fun slack d =>
        upperConcreteMixedWordQ1boundCanonical (p := p) (q := q) (σ := σ) R eps k slack d)
      (upperConcreteMixedWordBound_of_caseBounds
        (upperConcreteOneLinearMixedWordBound_of_canonical_oneL
          (p := p) (q := q) (σ := σ) R hk3 hε)
        (upperConcreteOneQuadraticMixedWordBound_of_canonical_oneQ
          (p := p) (q := q) (σ := σ) R hk3 hε)
        (upperConcreteMultiDefectMixedWordBound_of_canonical_multi
          (p := p) (q := q) (σ := σ) R hk3 hε)))
    (upper_hTermLimit_of_upperConcreteMixedTermLimit
      (upperConcreteMixedTermLimit_of_caseLimits
        (upperConcreteOneLinearMixedTermLimit_of_canonical_oneL
          (p := p) (q := q) (σ := σ) R hk3 hε)
        (upperConcreteOneQuadraticMixedTermLimit_of_canonical_oneQ
          (p := p) (q := q) (σ := σ) R hk3 hε)
        (upperConcreteMultiDefectMixedTermLimit_of_canonical_multi
          (p := p) (q := q) (σ := σ) R hk3 hε)))

/-- One-sided canonical mixed-word specialization with the concrete normalized
Gaussian operator tails closed.

This combines
`upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_momentOperatorTails_canonicalMixedWords`
with the existing concrete Gaussian/Wishart operator-tail estimates, so the
canonical scalar route no longer exposes `hSampleTail`, `hGammaTail`,
`hWordBound`, or `hTermLimit`. -/
theorem upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_momentConcreteOperatorTails_canonicalMixedWords
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {bMoment : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hOneSided :
      UpperConcreteOneSidedPositiveDeviationWitness
        (p := p) (q := q) (σ := σ) eps k)
    (hFullIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (hMoment :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := p) (q := q) (σ := σ)).real
            (backgroundMomentBadSet
              (p := p) (q := q) (σ := σ)
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean (p := p) (q := q) (σ := σ) k d)
              k) ≤ bMoment slack d)
    (hBad :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          bMoment slack d +
              Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)) +
            Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)) ≤
            1 / 2) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  refine
    upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_momentOperatorTails_canonicalMixedWords
      (p := p) (q := q) (σ := σ) R
      (bMoment := bMoment)
      (bSample := fun _ d => Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)))
      (bGamma := fun _ d => Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)))
      hk3 hε hOneSided hFullIso hIsoRealDim hMoment ?_ ?_ hBad
  · intro slack hslack
    exact
      (upper_concrete_commonThreshold_operator_tails
        (p := p) (q := q) (σ := σ) hOperatorDim slack hslack).mono
        fun _ htails => htails.1
  · intro slack hslack
    exact
      (upper_concrete_commonThreshold_operator_tails
        (p := p) (q := q) (σ := σ) hOperatorDim slack hslack).mono
        fun _ htails => htails.2

/-- Concrete upper closure with the normalized Gaussian operator tails closed.

Compared with
`upper_eventual_from_concrete_sequences_of_fullIso_momentOperatorTails_mixedWords`,
this endpoint no longer assumes `hSampleTail` and `hGammaTail`.  They are
obtained from the existing concrete Gaussian/Wishart probability estimates,
using monotonicity to pass from the two canonical thresholds to the shared
threshold `upperConcreteM`.

The remaining background-typicality assumptions are now exactly the moment
bad-set estimate `hMoment` and the scalar union-bound budget `hBad`, together
with the fixed-type dimension bridge
`bipartiteDimension p q = d²` required by the existing probability-tail API. -/
theorem upper_eventual_from_concrete_sequences_of_fullIso_momentConcreteOperatorTails_mixedWords
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {bMoment Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hp :
      ∀ᶠ d in atTop,
        0 < upperConcreteTargetProb
          (p := p) (q := q) (σ := σ) eps k d)
    (hFullIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (hMoment :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := p) (q := q) (σ := σ)).real
            (backgroundMomentBadSet
              (p := p) (q := q) (σ := σ)
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean (p := p) (q := q) (σ := σ) k d)
              k) ≤ bMoment slack d)
    (hBad :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          bMoment slack d +
              Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)) +
            Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)) ≤
            1 / 2)
    (hWordBound :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y : SampleMatrix p q σ⦄,
            Y ∈ backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d)
                (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
                (upperCanonicalTau slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k →
            frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed k d)
                (upperSlackRadius (spikeRoot k eps) R.lam slack) →
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                |localWordScaledTraceTerm
                    (p := p) (q := q)
                    (upperConcreteN d)
                    (localBackground (p := p) (q := q) (σ := σ) Y)
                    (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                    (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
                    w| ≤
                  localExpansionMixedWordEnvelopeTerm
                    (upperConcreteN d) (Abound slack d) (L2bound slack d)
                    (L1bound slack d) (Q2bound slack d) (Q1bound slack d) k w)
    (hTermLimit :
      ∀ slack : ℝ, 0 < slack →
        ∀ w : Fin k → LocalExpansionLetter,
          localWordIsMixed w →
            Tendsto
              (fun d =>
                localExpansionMixedWordEnvelopeTerm
                  (upperConcreteN d) (Abound slack d) (L2bound slack d)
                  (L1bound slack d) (Q2bound slack d) (Q1bound slack d) k w)
              atTop (nhds 0)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  refine
    upper_eventual_from_concrete_sequences_of_fullIso_momentOperatorTails_mixedWords
      (p := p) (q := q) (σ := σ) R
      (bMoment := bMoment)
      (bSample := fun _ d => Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)))
      (bGamma := fun _ d => Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2)))
      (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
      (Q2bound := Q2bound) (Q1bound := Q1bound)
      hk3 hε hp hFullIso hIsoRealDim hMoment ?_ ?_ hBad
      hWordBound hTermLimit
  · intro slack hslack
    exact
      (upper_concrete_commonThreshold_operator_tails
        (p := p) (q := q) (σ := σ) hOperatorDim slack hslack).mono
        fun _ htails => htails.1
  · intro slack hslack
    exact
      (upper_concrete_commonThreshold_operator_tails
        (p := p) (q := q) (σ := σ) hOperatorDim slack hslack).mono
        fun _ htails => htails.2

/-- Concrete upper closure with the bad-set union budget closed from a moment
bound tending to zero.

This is a slightly cleaner endpoint than
`upper_eventual_from_concrete_sequences_of_fullIso_momentConcreteOperatorTails_mixedWords`:
it replaces the explicit scalar assumption

`bMoment + exp(-d²/12) + exp(-d²/12) ≤ 1/2`

by the canonical limit input

`bMoment slack d → 0`.

The normalized operator tails still come from the already-proved concrete
Gaussian/Wishart estimates.  The remaining probabilistic background input is
therefore the moment bad-set estimate itself, plus the fact that its chosen
envelope tends to zero. -/
theorem upper_eventual_from_concrete_sequences_of_fullIso_momentLimitConcreteOperatorTails_mixedWords
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {bMoment Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hp :
      ∀ᶠ d in atTop,
        0 < upperConcreteTargetProb
          (p := p) (q := q) (σ := σ) eps k d)
    (hFullIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (hMoment :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := p) (q := q) (σ := σ)).real
            (backgroundMomentBadSet
              (p := p) (q := q) (σ := σ)
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean (p := p) (q := q) (σ := σ) k d)
              k) ≤ bMoment slack d)
    (hMomentLimit :
      ∀ slack : ℝ, 0 < slack →
        Tendsto (bMoment slack) atTop (nhds 0))
    (hWordBound :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y : SampleMatrix p q σ⦄,
            Y ∈ backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d)
                (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
                (upperCanonicalTau slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k →
            frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed k d)
                (upperSlackRadius (spikeRoot k eps) R.lam slack) →
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                |localWordScaledTraceTerm
                    (p := p) (q := q)
                    (upperConcreteN d)
                    (localBackground (p := p) (q := q) (σ := σ) Y)
                    (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                    (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
                    w| ≤
                  localExpansionMixedWordEnvelopeTerm
                    (upperConcreteN d) (Abound slack d) (L2bound slack d)
                    (L1bound slack d) (Q2bound slack d) (Q1bound slack d) k w)
    (hTermLimit :
      ∀ slack : ℝ, 0 < slack →
        ∀ w : Fin k → LocalExpansionLetter,
          localWordIsMixed w →
            Tendsto
              (fun d =>
                localExpansionMixedWordEnvelopeTerm
                  (upperConcreteN d) (Abound slack d) (L2bound slack d)
                  (L1bound slack d) (Q2bound slack d) (Q1bound slack d) k w)
              atTop (nhds 0)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_sequences_of_fullIso_momentConcreteOperatorTails_mixedWords
    (p := p) (q := q) (σ := σ) R
    (bMoment := bMoment)
    (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
    (Q2bound := Q2bound) (Q1bound := Q1bound)
    hk3 hε hp hFullIso hIsoRealDim hOperatorDim hMoment
    (upper_hBad_of_moment_bound_tendsto_zero hMomentLimit)
    hWordBound hTermLimit

/-- Concrete upper closure with the bad-set union budget closed from any
available vanishing moment-bound scale.

This version is often more convenient than
`upper_eventual_from_concrete_sequences_of_fullIso_momentLimitConcreteOperatorTails_mixedWords`:
the moment estimate may naturally give

`bMoment slack d ≤ momentScale slack d`

for an explicit scale, rather than a standalone proof that `bMoment slack d`
tends to zero.  The theorem closes `hBad` from that scale and then calls the
same concrete-operator-tail endpoint. -/
theorem upper_eventual_from_concrete_sequences_of_fullIso_momentScaleConcreteOperatorTails_mixedWords
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {bMoment momentScale
      Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hp :
      ∀ᶠ d in atTop,
        0 < upperConcreteTargetProb
          (p := p) (q := q) (σ := σ) eps k d)
    (hFullIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (hMoment :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := p) (q := q) (σ := σ)).real
            (backgroundMomentBadSet
              (p := p) (q := q) (σ := σ)
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean (p := p) (q := q) (σ := σ) k d)
              k) ≤ bMoment slack d)
    (hMomentScaleLimit :
      ∀ slack : ℝ, 0 < slack →
        Tendsto (momentScale slack) atTop (nhds 0))
    (hMomentScaleBound :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d : ℕ in atTop, bMoment slack d ≤ momentScale slack d)
    (hWordBound :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y : SampleMatrix p q σ⦄,
            Y ∈ backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d)
                (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
                (upperCanonicalTau slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k →
            frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed k d)
                (upperSlackRadius (spikeRoot k eps) R.lam slack) →
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                |localWordScaledTraceTerm
                    (p := p) (q := q)
                    (upperConcreteN d)
                    (localBackground (p := p) (q := q) (σ := σ) Y)
                    (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                    (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
                    w| ≤
                  localExpansionMixedWordEnvelopeTerm
                    (upperConcreteN d) (Abound slack d) (L2bound slack d)
                    (L1bound slack d) (Q2bound slack d) (Q1bound slack d) k w)
    (hTermLimit :
      ∀ slack : ℝ, 0 < slack →
        ∀ w : Fin k → LocalExpansionLetter,
          localWordIsMixed w →
            Tendsto
              (fun d =>
                localExpansionMixedWordEnvelopeTerm
                  (upperConcreteN d) (Abound slack d) (L2bound slack d)
                  (L1bound slack d) (Q2bound slack d) (Q1bound slack d) k w)
              atTop (nhds 0)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_sequences_of_fullIso_momentConcreteOperatorTails_mixedWords
    (p := p) (q := q) (σ := σ) R
    (bMoment := bMoment)
    (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
    (Q2bound := Q2bound) (Q1bound := Q1bound)
    hk3 hε hp hFullIso hIsoRealDim hOperatorDim hMoment
    (upper_hBad_of_moment_bound_scale_tendsto_zero
      hMomentScaleLimit hMomentScaleBound)
    hWordBound hTermLimit

/-- Concrete upper closure with `hBad` closed from the canonical scale
`C(slack)/(2 * D(d)^2)`. -/
theorem upper_eventual_from_concrete_sequences_of_fullIso_concreteMomentScaleConcreteOperatorTails_mixedWords
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {bMoment Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    {C : ℝ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hp :
      ∀ᶠ d in atTop,
        0 < upperConcreteTargetProb
          (p := p) (q := q) (σ := σ) eps k d)
    (hFullIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (hMoment :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := p) (q := q) (σ := σ)).real
            (backgroundMomentBadSet
              (p := p) (q := q) (σ := σ)
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean (p := p) (q := q) (σ := σ) k d)
              k) ≤ bMoment slack d)
    (hMomentScaleBound :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d : ℕ in atTop,
          bMoment slack d ≤ upperConcreteMomentBoundScale C slack d)
    (hWordBound :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y : SampleMatrix p q σ⦄,
            Y ∈ backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d)
                (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
                (upperCanonicalTau slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k →
            frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed k d)
                (upperSlackRadius (spikeRoot k eps) R.lam slack) →
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                |localWordScaledTraceTerm
                    (p := p) (q := q)
                    (upperConcreteN d)
                    (localBackground (p := p) (q := q) (σ := σ) Y)
                    (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                    (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
                    w| ≤
                  localExpansionMixedWordEnvelopeTerm
                    (upperConcreteN d) (Abound slack d) (L2bound slack d)
                    (L1bound slack d) (Q2bound slack d) (Q1bound slack d) k w)
    (hTermLimit :
      ∀ slack : ℝ, 0 < slack →
        ∀ w : Fin k → LocalExpansionLetter,
          localWordIsMixed w →
            Tendsto
              (fun d =>
                localExpansionMixedWordEnvelopeTerm
                  (upperConcreteN d) (Abound slack d) (L2bound slack d)
                  (L1bound slack d) (Q2bound slack d) (Q1bound slack d) k w)
              atTop (nhds 0)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_sequences_of_fullIso_momentScaleConcreteOperatorTails_mixedWords
    (p := p) (q := q) (σ := σ) R
    (bMoment := bMoment)
    (momentScale := upperConcreteMomentBoundScale C)
    (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
    (Q2bound := Q2bound) (Q1bound := Q1bound)
    hk3 hε hp hFullIso hIsoRealDim hOperatorDim hMoment
    (upperConcreteMomentBoundScale_tendsto_zero C)
    hMomentScaleBound hWordBound hTermLimit

/-- Concrete upper closure with the moment block isolated.

This endpoint replaces the raw probability estimate `hMoment` and the separate
scale comparison by the single proposition
`UpperConcreteMomentBadSetScaleBound C k`.  In other words, after the earlier
closures, the moment concentration input is exactly:

`P(backgroundMomentBadSet) ≤ C(slack) / (2 * D(d)^2)`, eventually for every
fixed positive slack.

The theorem does not prove that moment concentration estimate; it makes it the
one named remaining moment obligation. -/
theorem upper_eventual_from_concrete_sequences_of_fullIso_isolatedMomentConcreteOperatorTails_mixedWords
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {C : ℝ → ℝ}
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hp :
      ∀ᶠ d in atTop,
        0 < upperConcreteTargetProb
          (p := p) (q := q) (σ := σ) eps k d)
    (hFullIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (hMoment :
      UpperConcreteMomentBadSetScaleBound
        (p := p) (q := q) (σ := σ) C k)
    (hWordBound :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y : SampleMatrix p q σ⦄,
            Y ∈ backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d)
                (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
                (upperCanonicalTau slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k →
            frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed k d)
                (upperSlackRadius (spikeRoot k eps) R.lam slack) →
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                |localWordScaledTraceTerm
                    (p := p) (q := q)
                    (upperConcreteN d)
                    (localBackground (p := p) (q := q) (σ := σ) Y)
                    (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                    (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
                    w| ≤
                  localExpansionMixedWordEnvelopeTerm
                    (upperConcreteN d) (Abound slack d) (L2bound slack d)
                    (L1bound slack d) (Q2bound slack d) (Q1bound slack d) k w)
    (hTermLimit :
      ∀ slack : ℝ, 0 < slack →
        ∀ w : Fin k → LocalExpansionLetter,
          localWordIsMixed w →
            Tendsto
              (fun d =>
                localExpansionMixedWordEnvelopeTerm
                  (upperConcreteN d) (Abound slack d) (L2bound slack d)
                  (L1bound slack d) (Q2bound slack d) (Q1bound slack d) k w)
              atTop (nhds 0)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_sequences_of_fullIso_concreteMomentScaleConcreteOperatorTails_mixedWords
    (p := p) (q := q) (σ := σ) R
    (bMoment := upperConcreteMomentBoundScale C)
    (C := C)
    (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
    (Q2bound := Q2bound) (Q1bound := Q1bound)
    hk3 hε hp hFullIso hIsoRealDim hOperatorDim
    (upper_hMoment_of_upperConcreteMomentBadSetScaleBound hMoment)
    (by
      intro slack _hslack
      exact Eventually.of_forall fun d => le_rfl)
    hWordBound hTermLimit

/-- Concrete upper closure with both the moment block and mixed-word block
isolated.

Compared with
`upper_eventual_from_concrete_sequences_of_fullIso_isolatedMomentConcreteOperatorTails_mixedWords`,
this endpoint no longer exposes the long raw `hWordBound` and `hTermLimit`
signatures.  The remaining deterministic mixed-remainder obligations are
instead the two named propositions:

* `UpperConcreteMixedWordBound`, the uniform word-by-word estimate on the
  sharp-radius neighbourhood of the background typical set;
* `UpperConcreteMixedTermLimit`, the scalar limit calculation for each
  mixed-word envelope term.

The theorem still does not prove those deterministic analytic estimates; it
keeps them visible as the intended remaining mixed-remainder inputs. -/
theorem upper_eventual_from_concrete_sequences_of_fullIso_isolatedMomentConcreteOperatorTails_isolatedMixedWords
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {C : ℝ → ℝ}
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hp :
      ∀ᶠ d in atTop,
        0 < upperConcreteTargetProb
          (p := p) (q := q) (σ := σ) eps k d)
    (hFullIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (hMoment :
      UpperConcreteMomentBadSetScaleBound
        (p := p) (q := q) (σ := σ) C k)
    (hWordBound :
      UpperConcreteMixedWordBound
        (p := p) (q := q) (σ := σ)
        R eps k Abound L2bound L1bound Q2bound Q1bound)
    (hTermLimit :
      UpperConcreteMixedTermLimit
        k Abound L2bound L1bound Q2bound Q1bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_sequences_of_fullIso_isolatedMomentConcreteOperatorTails_mixedWords
    (p := p) (q := q) (σ := σ) R
    (C := C)
    (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
    (Q2bound := Q2bound) (Q1bound := Q1bound)
    hk3 hε hp hFullIso hIsoRealDim hOperatorDim hMoment
    (upper_hWordBound_of_upperConcreteMixedWordBound hWordBound)
    (upper_hTermLimit_of_upperConcreteMixedTermLimit hTermLimit)

/-- Concrete upper closure with target positivity, moment concentration, and
mixed-word analysis all isolated.

This is the cleanest fixed-type theorem-facing endpoint in this closure file.
It closes the raw `hp` assumption from a named
`UpperConcretePositiveDeviationWitness`, closes the bad-set union budget from
the isolated canonical-scale moment input, obtains the normalized operator
tails from the existing concrete estimates, and closes `hMixed` from the two
isolated deterministic mixed-word propositions.

The remaining genuinely hard analytic inputs are visible as:

* `hFullIso : FullSphericalIsoperimetry`;
* `hMoment : UpperConcreteMomentBadSetScaleBound C k`;
* `hWordBound : UpperConcreteMixedWordBound ...`;
* `hTermLimit : UpperConcreteMixedTermLimit ...`.

The fixed-type dimension bridges `hIsoRealDim` and `hOperatorDim` remain
explicit bookkeeping assumptions; earlier lemmas in this file explain why
they cannot be closed for a fixed ambient type as `d → ∞`. -/
theorem upper_eventual_from_concrete_sequences_of_fullIso_positiveDeviationWitness_isolatedMomentConcreteOperatorTails_isolatedMixedWords
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {C : ℝ → ℝ}
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    {E : ℕ → Set (SampleMatrix p q σ)}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hTarget :
      UpperConcretePositiveDeviationWitness
        (p := p) (q := q) (σ := σ) eps k E)
    (hFullIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (hMoment :
      UpperConcreteMomentBadSetScaleBound
        (p := p) (q := q) (σ := σ) C k)
    (hWordBound :
      UpperConcreteMixedWordBound
        (p := p) (q := q) (σ := σ)
        R eps k Abound L2bound L1bound Q2bound Q1bound)
    (hTermLimit :
      UpperConcreteMixedTermLimit
        k Abound L2bound L1bound Q2bound Q1bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_sequences_of_fullIso_isolatedMomentConcreteOperatorTails_isolatedMixedWords
    (p := p) (q := q) (σ := σ) R
    (C := C)
    (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
    (Q2bound := Q2bound) (Q1bound := Q1bound)
    hk3 hε
    (upper_hp_of_upperConcretePositiveDeviationWitness hTarget)
    hFullIso hIsoRealDim hOperatorDim hMoment hWordBound hTermLimit

/-- Actual-upper-event version of the isolated mixed-word endpoint.

This replaces the arbitrary positive-deviation witness `hTarget` by positivity
of the canonical one-sided upper-tail event. -/
theorem upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_isolatedMomentConcreteOperatorTails_isolatedMixedWords
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {C : ℝ → ℝ}
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hOneSided :
      UpperConcreteOneSidedPositiveDeviationWitness
        (p := p) (q := q) (σ := σ) eps k)
    (hFullIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (hMoment :
      UpperConcreteMomentBadSetScaleBound
        (p := p) (q := q) (σ := σ) C k)
    (hWordBound :
      UpperConcreteMixedWordBound
        (p := p) (q := q) (σ := σ)
        R eps k Abound L2bound L1bound Q2bound Q1bound)
    (hTermLimit :
      UpperConcreteMixedTermLimit
        k Abound L2bound L1bound Q2bound Q1bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_sequences_of_fullIso_positiveDeviationWitness_isolatedMomentConcreteOperatorTails_isolatedMixedWords
    (p := p) (q := q) (σ := σ) R
    (C := C)
    (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
    (Q2bound := Q2bound) (Q1bound := Q1bound)
    hk3 hε
    (upper_targetWitness_of_upperConcreteOneSidedPositiveDeviationWitness
      (p := p) (q := q) (σ := σ) hOneSided)
    hFullIso hIsoRealDim hOperatorDim hMoment hWordBound hTermLimit

/-- Actual-upper-event isolated-moment endpoint with the deterministic canonical
mixed-word and scalar term-limit suppliers folded internally.

Compared with
`upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_momentConcreteOperatorTails_canonicalMixedWords`,
this endpoint no longer exposes the raw moment bad-set estimate and scalar
union-bound budget separately: they are replaced by the named scale proposition
`UpperConcreteMomentBadSetScaleBound C k`. -/
theorem upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_isolatedMomentConcreteOperatorTails_canonicalMixedWords
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {C : ℝ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hOneSided :
      UpperConcreteOneSidedPositiveDeviationWitness
        (p := p) (q := q) (σ := σ) eps k)
    (hFullIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (hMoment :
      UpperConcreteMomentBadSetScaleBound
        (p := p) (q := q) (σ := σ) C k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_isolatedMomentConcreteOperatorTails_isolatedMixedWords
    (p := p) (q := q) (σ := σ) R
    (C := C)
    (Abound := fun slack d =>
      upperConcreteMixedWordAboundCanonical (p := p) (q := q) (σ := σ) slack d)
    (L2bound := fun slack d =>
      upperConcreteMixedWordL2boundCanonical (p := p) (q := q) (σ := σ) R eps k slack d)
    (L1bound := fun slack d =>
      upperConcreteMixedWordL1boundCanonical (p := p) (q := q) (σ := σ) R eps k slack d)
    (Q2bound := fun slack d =>
      upperConcreteMixedWordQ2boundCanonical (p := p) (q := q) (σ := σ) R eps k slack d)
    (Q1bound := fun slack d =>
      upperConcreteMixedWordQ1boundCanonical (p := p) (q := q) (σ := σ) R eps k slack d)
    hk3 hε hOneSided hFullIso hIsoRealDim hOperatorDim hMoment
    (upperConcreteMixedWordBound_of_caseBounds
      (upperConcreteOneLinearMixedWordBound_of_canonical_oneL
        (p := p) (q := q) (σ := σ) R hk3 hε)
      (upperConcreteOneQuadraticMixedWordBound_of_canonical_oneQ
        (p := p) (q := q) (σ := σ) R hk3 hε)
      (upperConcreteMultiDefectMixedWordBound_of_canonical_multi
        (p := p) (q := q) (σ := σ) R hk3 hε))
    (upperConcreteMixedTermLimit_of_caseLimits
      (upperConcreteOneLinearMixedTermLimit_of_canonical_oneL
        (p := p) (q := q) (σ := σ) R hk3 hε)
      (upperConcreteOneQuadraticMixedTermLimit_of_canonical_oneQ
        (p := p) (q := q) (σ := σ) R hk3 hε)
      (upperConcreteMultiDefectMixedTermLimit_of_canonical_multi
        (p := p) (q := q) (σ := σ) R hk3 hε))

/-- Canonical upper endpoint with the broad `FullSphericalIsoperimetry` input
replaced by its two explicit global geometric suppliers: half-mass cap
comparison and the hemisphere Gaussian tail. -/
theorem upper_eventual_from_concrete_sequences_of_hemisphereComparisonTail_oneSidedPositive_isolatedMomentConcreteOperatorTails_canonicalMixedWords
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {C : ℝ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hOneSided :
      UpperConcreteOneSidedPositiveDeviationWitness
        (p := p) (q := q) (σ := σ) eps k)
    (hCompare : PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo)
    (hTail : PptFactorization.AppendixB.sphere_hemisphereGaussianTail)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (hMoment :
      UpperConcreteMomentBadSetScaleBound
        (p := p) (q := q) (σ := σ) C k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_isolatedMomentConcreteOperatorTails_canonicalMixedWords
    (p := p) (q := q) (σ := σ) R
    (C := C) hk3 hε hOneSided
    (PptFactorization.AppendixB.fullSphericalIsoperimetry_of_hemisphereComparison_and_tail
      (PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparison_of_geTwo hCompare) hTail)
    hIsoRealDim hOperatorDim hMoment

/-- Canonical upper endpoint with the hemisphere Gaussian tail supplier unpacked
into geometric coordinate-dominance and coordinate-tail inputs.

The large-radius hemisphere tail is now supplied by the audited no-input
theorem `sphere_hemisphereLargeRadiusTail_surface`. -/
theorem upper_eventual_from_concrete_sequences_of_coordinateTailGeometry_oneSidedPositive_isolatedMomentConcreteOperatorTails_canonicalMixedWords
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {C : ℝ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hOneSided :
      UpperConcreteOneSidedPositiveDeviationWitness
        (p := p) (q := q) (σ := σ) eps k)
    (hCompare : PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo)
    (hCoordTailInterior : PptFactorization.AppendixB.sphere_northPoleCapConeGaussianTailLargeExponent)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (hMoment :
      UpperConcreteMomentBadSetScaleBound
        (p := p) (q := q) (σ := σ) C k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_sequences_of_hemisphereComparisonTail_oneSidedPositive_isolatedMomentConcreteOperatorTails_canonicalMixedWords
    (p := p) (q := q) (σ := σ) R
    (C := C) hk3 hε hOneSided hCompare
    (PptFactorization.AppendixB.sphere_hemisphereGaussianTail_of_coordinateDominance_and_coordinateTail
      PptFactorization.AppendixB.sphere_hemisphereComplementCoordinateDominance_surface
      (PptFactorization.AppendixB.sphere_coordinateGaussianTail_of_interior
        (PptFactorization.AppendixB.sphere_coordinateGaussianTailInterior_of_geTwo
          (PptFactorization.AppendixB.sphere_coordinateGaussianTailInteriorGeTwo_of_largeExponent
            (PptFactorization.AppendixB.sphere_coordinateGaussianTailInteriorLargeExponent_of_northPole
              (PptFactorization.AppendixB.sphere_coordinateGaussianTailInteriorLargeExponentNorthPole_of_coneTail
                hCoordTailInterior))))) PptFactorization.AppendixB.sphere_hemisphereLargeRadiusTail_surface)
    hIsoRealDim hOperatorDim hMoment

/-- Favourable-event version of the sharpened coordinate-tail geometry
endpoint.

This removes the visible packaged `hOneSided` input from the current
coordinate-tail route: positivity of the actual one-sided upper event is
derived from the one-column favourable event and the deterministic inclusion
blocks already proved in this file. -/
theorem upper_eventual_from_concrete_sequences_of_coordinateTailGeometry_favorableEvent_isolatedMomentConcreteOperatorTails_canonicalMixedWords
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} {α₀ : σ}
    {C : ℝ → ℝ}
    {q₀ δ M a center errProfile errSpike τ errScale errBg errMix errMean : ℕ → ℝ}
    {directionSet : ℕ → Set (EuclideanSpace ℂ (BipIndex p q))}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hFav_pos :
      ∀ᶠ d in atTop,
        0 <
          (upperConcreteSphericalMu
            (p := p) (q := q) (σ := σ) d).real
            (sphericalOneColumnFavorableEvent
              (p := p) (q := q) (σ := σ)
              α₀ (q₀ d) (δ d) (directionSet d)
              (backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M d) (τ d) (center d) k)))
    (hProfile :
      ∀ᶠ d in atTop,
        ∀ ρ : ℝ, ∀ u : EuclideanSpace ℂ (BipIndex p q),
          ρ ∈ betaColumnIntervalSet (q₀ d) (δ d) →
          u ∈ directionSet d →
          a d ^ k - errProfile d ≤
            columnDirectionSpikeProfile
              (p := p) (q := q) (upperConcreteN d) k ρ u)
    (hPureError :
      ∀ᶠ d in atTop, errProfile d + 0 ≤ errSpike d)
    (hBackgroundTransfer :
      ∀ᶠ d in atTop,
        ∀ X : SampleMatrix p q σ,
          sampleColumnComplementNormalized
              (p := p) (q := q) (σ := σ) X α₀ ∈
            backgroundTypicalSet
              (p := p) (q := q) (σ := σ)
              (upperConcreteN d) (M d) (τ d) (center d) k →
          backgroundMomentValue
              (p := p) (q := q) (σ := σ) (upperConcreteN d) k
              (sampleColumnComplementNormalized
                (p := p) (q := q) (σ := σ) X α₀) -
            errScale d ≤
          columnBackgroundContribution
            (p := p) (q := q) (σ := σ) (upperConcreteN d) k X α₀)
    (hBackgroundError :
      ∀ᶠ d in atTop, τ d + errScale d ≤ errBg d)
    (hMixed :
      ∀ᶠ d in atTop,
        ∀ X : SampleMatrix p q σ,
          X ∈ sphericalOneColumnFavorableEvent
              (p := p) (q := q) (σ := σ)
              α₀ (q₀ d) (δ d) (directionSet d)
              (backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M d) (τ d) (center d) k) →
          |columnMixedRemainder
              (p := p) (q := q) (σ := σ) (upperConcreteN d) k X α₀| ≤
            errMix d)
    (hMean :
      ∀ᶠ d in atTop,
        upperConcreteMean (p := p) (q := q) (σ := σ) k d ≤
          center d + errMean d)
    (hBudget :
      ∀ᶠ d in atTop,
        eps + errSpike d + errBg d + errMix d + errMean d ≤ a d ^ k)
    (hCompare : PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo)
    (hCoordTailInterior : PptFactorization.AppendixB.sphere_northPoleCapConeGaussianTailLargeExponent)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (hMoment :
      UpperConcreteMomentBadSetScaleBound
        (p := p) (q := q) (σ := σ) C k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_sequences_of_coordinateTailGeometry_oneSidedPositive_isolatedMomentConcreteOperatorTails_canonicalMixedWords
    (p := p) (q := q) (σ := σ) R
    (C := C) hk3 hε
    (upperConcreteOneSidedPositiveDeviationWitness_of_oneColumnFavorableEvent
      (p := p) (q := q) (σ := σ)
      (eps := eps) (k := k) (α₀ := α₀)
      (q₀ := q₀) (δ := δ) (M := M) (a := a) (center := center)
      (errProfile := errProfile) (errSpike := errSpike)
      (τ := τ) (errScale := errScale) (errBg := errBg)
      (errMix := errMix) (errMean := errMean) (directionSet := directionSet)
      hFav_pos hProfile hPureError hBackgroundTransfer hBackgroundError
      hMixed hMean hBudget)
    hCompare hCoordTailInterior hIsoRealDim hOperatorDim hMoment

/-- Favourable-event coordinate-tail endpoint with the isolated moment-scale
packet unpacked through its local-expansion supplier.

Compared with
`upper_eventual_from_concrete_sequences_of_coordinateTailGeometry_favorableEvent_isolatedMomentConcreteOperatorTails_canonicalMixedWords`,
this route no longer exposes the named
`UpperConcreteMomentBadSetScaleBound C k` packet.  Instead it asks directly for
the local half-mass, local mixed-remainder, budget, and spherical-tail envelope
inputs used by
`upperConcreteMomentBadSetScaleBound_of_localExpansion_envelope`. -/
theorem upper_eventual_from_concrete_sequences_of_coordinateTailGeometry_favorableEvent_localExpansionMoment_canonicalMixedWords
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} {α₀ : σ}
    {C : ℝ → ℝ}
    {q₀ δ favM a center errProfile errSpike favτ errScale errBg errMix errMean : ℕ → ℝ}
    {directionSet : ℕ → Set (EuclideanSpace ℂ (BipIndex p q))}
    {aSlack etaSlack : ℝ → ℝ}
    {M τ : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hFav_pos :
      ∀ᶠ d in atTop,
        0 <
          (upperConcreteSphericalMu
            (p := p) (q := q) (σ := σ) d).real
            (sphericalOneColumnFavorableEvent
              (p := p) (q := q) (σ := σ)
              α₀ (q₀ d) (δ d) (directionSet d)
              (backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (favM d) (favτ d) (center d) k)))
    (hProfile :
      ∀ᶠ d in atTop,
        ∀ ρ : ℝ, ∀ u : EuclideanSpace ℂ (BipIndex p q),
          ρ ∈ betaColumnIntervalSet (q₀ d) (δ d) →
          u ∈ directionSet d →
          a d ^ k - errProfile d ≤
            columnDirectionSpikeProfile
              (p := p) (q := q) (upperConcreteN d) k ρ u)
    (hPureError :
      ∀ᶠ d in atTop, errProfile d + 0 ≤ errSpike d)
    (hBackgroundTransfer :
      ∀ᶠ d in atTop,
        ∀ X : SampleMatrix p q σ,
          sampleColumnComplementNormalized
              (p := p) (q := q) (σ := σ) X α₀ ∈
            backgroundTypicalSet
              (p := p) (q := q) (σ := σ)
              (upperConcreteN d) (favM d) (favτ d) (center d) k →
          backgroundMomentValue
              (p := p) (q := q) (σ := σ) (upperConcreteN d) k
              (sampleColumnComplementNormalized
                (p := p) (q := q) (σ := σ) X α₀) -
            errScale d ≤
          columnBackgroundContribution
            (p := p) (q := q) (σ := σ) (upperConcreteN d) k X α₀)
    (hBackgroundError :
      ∀ᶠ d in atTop, favτ d + errScale d ≤ errBg d)
    (hFavorableMixed :
      ∀ᶠ d in atTop,
        ∀ X : SampleMatrix p q σ,
          X ∈ sphericalOneColumnFavorableEvent
              (p := p) (q := q) (σ := σ)
              α₀ (q₀ d) (δ d) (directionSet d)
              (backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (favM d) (favτ d) (center d) k) →
          |columnMixedRemainder
              (p := p) (q := q) (σ := σ) (upperConcreteN d) k X α₀| ≤
            errMix d)
    (hMean :
      ∀ᶠ d in atTop,
        upperConcreteMean (p := p) (q := q) (σ := σ) k d ≤
          center d + errMean d)
    (hFavorableBudget :
      ∀ᶠ d in atTop,
        eps + errSpike d + errBg d + errMix d + errMean d ≤ a d ^ k)
    (hCompare : PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo)
    (hCoordTailInterior : PptFactorization.AppendixB.sphere_northPoleCapConeGaussianTailLargeExponent)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (ha : ∀ slack : ℝ, 0 < slack → 0 ≤ aSlack slack)
    (hK_half :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          1 / 2 ≤
            (upperConcreteSphericalMu (p := p) (q := q) (σ := σ) d).real
              (backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k))
    (hLocalMixed :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y : SampleMatrix p q σ⦄,
            Y ∈ backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k →
            frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed k d) (aSlack slack) →
            |localExpansionMixedRemainder
                (p := p) (q := q) (upperConcreteN d) k
                (localBackground (p := p) (q := q) (σ := σ) Y)
                (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))| ≤
              etaSlack slack)
    (hMomentBudget :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          aSlack slack ^ k + etaSlack slack + τ slack d <
            upperCanonicalTau slack d)
    (hEnvelope :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          Real.exp
              (-(((upperConcreteRealDim R d - 1) *
                  sharpSphericalRadiusSq
                    (upperConcreteN d) (spikeSpeed k d) (aSlack slack)) /
                2)) ≤
            upperConcreteMomentBoundScale C slack d) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hTail :
      PptFactorization.AppendixB.sphere_hemisphereGaussianTail :=
    PptFactorization.AppendixB.sphere_hemisphereGaussianTail_of_coordinateDominance_and_coordinateTail
      PptFactorization.AppendixB.sphere_hemisphereComplementCoordinateDominance_surface
      (PptFactorization.AppendixB.sphere_coordinateGaussianTail_of_interior
        (PptFactorization.AppendixB.sphere_coordinateGaussianTailInterior_of_geTwo
          (PptFactorization.AppendixB.sphere_coordinateGaussianTailInteriorGeTwo_of_largeExponent
            (PptFactorization.AppendixB.sphere_coordinateGaussianTailInteriorLargeExponent_of_northPole
              (PptFactorization.AppendixB.sphere_coordinateGaussianTailInteriorLargeExponentNorthPole_of_coneTail
                hCoordTailInterior))))) PptFactorization.AppendixB.sphere_hemisphereLargeRadiusTail_surface
  have hFullIso :
      PptFactorization.AppendixB.FullSphericalIsoperimetry :=
    PptFactorization.AppendixB.fullSphericalIsoperimetry_of_hemisphereComparison_and_tail
      (PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparison_of_geTwo hCompare) hTail
  exact
    upper_eventual_from_concrete_sequences_of_coordinateTailGeometry_favorableEvent_isolatedMomentConcreteOperatorTails_canonicalMixedWords
      (p := p) (q := q) (σ := σ) R
      (C := C) (q₀ := q₀) (δ := δ) (M := favM) (a := a)
      (center := center) (errProfile := errProfile)
      (errSpike := errSpike) (τ := favτ) (errScale := errScale)
      (errBg := errBg) (errMix := errMix) (errMean := errMean)
      (directionSet := directionSet)
      hk3 hε hFav_pos hProfile hPureError hBackgroundTransfer
      hBackgroundError hFavorableMixed hMean hFavorableBudget
      hCompare hCoordTailInterior hIsoRealDim hOperatorDim
      (upperConcreteMomentBadSetScaleBound_of_localExpansion_envelope
        (p := p) (q := q) (σ := σ) R
        (C := C) (k := k)
        (aSlack := aSlack) (etaSlack := etaSlack)
        (M := M) (τ := τ)
        hk3 hFullIso hIsoRealDim ha hK_half hLocalMixed hMomentBudget
        hEnvelope)

/-- Lower-bound coordinate-tail endpoint with the isolated moment-scale packet
unpacked through its local-expansion supplier.

This is the lower-bound analogue of
`upper_eventual_from_concrete_sequences_of_coordinateTailGeometry_favorableEvent_localExpansionMoment_canonicalMixedWords`.
It consumes an eventually positive lower bound for the actual one-sided
upper-tail event, builds the one-sided positivity witness internally, and
also builds the concrete background moment bad-set scale bound from the local
expansion/envelope inputs. -/
theorem upper_eventual_from_concrete_sequences_of_coordinateTailGeometry_oneSidedLowerBound_localExpansionMoment_canonicalMixedWords
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {C : ℝ → ℝ}
    {lower : ℕ → ℝ}
    {aSlack etaSlack : ℝ → ℝ}
    {M τ : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hlower_pos : ∀ᶠ d in atTop, 0 < lower d)
    (hle :
      ∀ᶠ d in atTop,
        lower d ≤
          (upperConcreteSphericalMu
            (p := p) (q := q) (σ := σ) d).real
            (columnMomentUpperTailSet
              (p := p) (q := q) (σ := σ)
              (upperConcreteN d) eps
              (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k))
    (hCompare : PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo)
    (hCoordTailInterior : PptFactorization.AppendixB.sphere_northPoleCapConeGaussianTailLargeExponent)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (ha : ∀ slack : ℝ, 0 < slack → 0 ≤ aSlack slack)
    (hK_half :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          1 / 2 ≤
            (upperConcreteSphericalMu (p := p) (q := q) (σ := σ) d).real
              (backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k))
    (hLocalMixed :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y : SampleMatrix p q σ⦄,
            Y ∈ backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k →
            frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed k d) (aSlack slack) →
            |localExpansionMixedRemainder
                (p := p) (q := q) (upperConcreteN d) k
                (localBackground (p := p) (q := q) (σ := σ) Y)
                (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))| ≤
              etaSlack slack)
    (hMomentBudget :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          aSlack slack ^ k + etaSlack slack + τ slack d <
            upperCanonicalTau slack d)
    (hEnvelope :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          Real.exp
              (-(((upperConcreteRealDim R d - 1) *
                  sharpSphericalRadiusSq
                    (upperConcreteN d) (spikeSpeed k d) (aSlack slack)) /
                2)) ≤
            upperConcreteMomentBoundScale C slack d) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hTail :
      PptFactorization.AppendixB.sphere_hemisphereGaussianTail :=
    PptFactorization.AppendixB.sphere_hemisphereGaussianTail_of_coordinateDominance_and_coordinateTail
      PptFactorization.AppendixB.sphere_hemisphereComplementCoordinateDominance_surface
      (PptFactorization.AppendixB.sphere_coordinateGaussianTail_of_interior
        (PptFactorization.AppendixB.sphere_coordinateGaussianTailInterior_of_geTwo
          (PptFactorization.AppendixB.sphere_coordinateGaussianTailInteriorGeTwo_of_largeExponent
            (PptFactorization.AppendixB.sphere_coordinateGaussianTailInteriorLargeExponent_of_northPole
              (PptFactorization.AppendixB.sphere_coordinateGaussianTailInteriorLargeExponentNorthPole_of_coneTail
                hCoordTailInterior))))) PptFactorization.AppendixB.sphere_hemisphereLargeRadiusTail_surface
  have hFullIso :
      PptFactorization.AppendixB.FullSphericalIsoperimetry :=
    PptFactorization.AppendixB.fullSphericalIsoperimetry_of_hemisphereComparison_and_tail
      (PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparison_of_geTwo hCompare) hTail
  exact
    upper_eventual_from_concrete_sequences_of_coordinateTailGeometry_oneSidedPositive_isolatedMomentConcreteOperatorTails_canonicalMixedWords
      (p := p) (q := q) (σ := σ) R
      (C := C) hk3 hε
      (upperConcreteOneSidedPositiveDeviationWitness_of_eventually_positive_lower_bound
        (p := p) (q := q) (σ := σ)
        (eps := eps) (k := k) (lower := lower) hlower_pos hle)
      hCompare hCoordTailInterior hIsoRealDim hOperatorDim
      (upperConcreteMomentBadSetScaleBound_of_localExpansion_envelope
        (p := p) (q := q) (σ := σ) R
        (C := C) (k := k)
        (aSlack := aSlack) (etaSlack := etaSlack)
        (M := M) (τ := τ)
        hk3 hFullIso hIsoRealDim ha hK_half hLocalMixed hMomentBudget
        hEnvelope)

/-- Actual-upper-event endpoint with the grouped mixed-word case package and
grouped scalar mixed-defect package folded into the existing curated upper
pipeline. -/
theorem upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_isolatedMomentConcreteOperatorTails_mixedWordCaseBounds_mixedDefectCaseLimits
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {C : ℝ → ℝ}
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hOneSided :
      UpperConcreteOneSidedPositiveDeviationWitness
        (p := p) (q := q) (σ := σ) eps k)
    (hFullIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (hMoment :
      UpperConcreteMomentBadSetScaleBound
        (p := p) (q := q) (σ := σ) C k)
    (hWordCases :
      UpperConcreteMixedWordCaseBounds
        (p := p) (q := q) (σ := σ)
        R eps k Abound L2bound L1bound Q2bound Q1bound)
    (hDefectLimits :
      UpperConcreteMixedDefectCaseLimits
        k Abound L2bound L1bound Q2bound Q1bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_isolatedMomentConcreteOperatorTails_isolatedMixedWords
    (p := p) (q := q) (σ := σ) R
    (C := C)
    (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
    (Q2bound := Q2bound) (Q1bound := Q1bound)
    hk3 hε hOneSided hFullIso hIsoRealDim hOperatorDim hMoment
    (upperConcreteMixedWordBound_of_caseBounds
      hWordCases.1 hWordCases.2.1 hWordCases.2.2)
    (upperConcreteMixedTermLimit_of_defectCaseLimits hDefectLimits)

/-- Audit-facing endpoint for the current active ticket frontier.

Compared with the older curated endpoint, this theorem no longer exposes
`hTarget`, `hWordBound`, `hOneLinear`, `hOneQuadratic`, or `hMulti`
separately.  It consumes the actual one-sided upper-event positivity supplier,
the grouped mixed-word deterministic invoice, and the grouped scalar
mixed-defect limits, then folds them into the existing upper-bound pipeline.

This is a compact audit wrapper, not the primitive theorem-facing frontier.
The hypotheses `hOneSided`, `hMoment`, `hWordCases`, and `hDefectLimits` are
supplier packets.  Likewise, the fixed-type bridges `hIsoRealDim` and
`hOperatorDim` are compatibility artefacts: the file proves that the
fixed-type operator bridge cannot be closed as stated
(`not_eventually_fixed_bipartiteDimension_eq_dimensionSquared`), and the
actual concrete family should instead use the pointwise bridge
`upperConcreteRealDim_eq_concreteModel_realDim`. -/
theorem upper_eventual_from_concrete_sequences_of_fullIso_activeTicketSuppliers
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {C : ℝ → ℝ}
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hOneSided :
      UpperConcreteOneSidedPositiveDeviationWitness
        (p := p) (q := q) (σ := σ) eps k)
    (hFullIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (hMoment :
      UpperConcreteMomentBadSetScaleBound
        (p := p) (q := q) (σ := σ) C k)
    (hWordCases :
      UpperConcreteMixedWordCaseBounds
        (p := p) (q := q) (σ := σ)
        R eps k Abound L2bound L1bound Q2bound Q1bound)
    (hDefectLimits :
      UpperConcreteMixedDefectCaseLimits
        k Abound L2bound L1bound Q2bound Q1bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_isolatedMomentConcreteOperatorTails_mixedWordCaseBounds_mixedDefectCaseLimits
    (p := p) (q := q) (σ := σ) R
    (C := C)
    (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
    (Q2bound := Q2bound) (Q1bound := Q1bound)
    hk3 hε hOneSided hFullIso hIsoRealDim hOperatorDim
    hMoment hWordCases hDefectLimits

/-- Audit-facing favourable-event endpoint for the active ticket frontier.

This version removes the endpoint's visible target-positivity leaf: it derives
the actual one-sided positive-deviation witness from the positive one-column
favourable event and the deterministic inclusion blocks, then folds the mixed
word-case package and scalar defect-limit package through the curated upper
pipeline. -/
theorem upper_eventual_from_concrete_sequences_of_fullIso_favorableEvent_activeTicketSuppliers
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [DecidableEq σ]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} {α₀ : σ}
    {C : ℝ → ℝ}
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    {q₀ δ M a center errProfile errSpike τ errScale errBg errMix errMean : ℕ → ℝ}
    {directionSet : ℕ → Set (EuclideanSpace ℂ (BipIndex p q))}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hFav_pos :
      ∀ᶠ d in atTop,
        0 <
          (upperConcreteSphericalMu
            (p := p) (q := q) (σ := σ) d).real
            (sphericalOneColumnFavorableEvent
              (p := p) (q := q) (σ := σ)
              α₀ (q₀ d) (δ d) (directionSet d)
              (backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M d) (τ d) (center d) k)))
    (hProfile :
      ∀ᶠ d in atTop,
        ∀ ρ : ℝ, ∀ u : EuclideanSpace ℂ (BipIndex p q),
          ρ ∈ betaColumnIntervalSet (q₀ d) (δ d) →
          u ∈ directionSet d →
          a d ^ k - errProfile d ≤
            columnDirectionSpikeProfile
              (p := p) (q := q) (upperConcreteN d) k ρ u)
    (hPureError :
      ∀ᶠ d in atTop, errProfile d + 0 ≤ errSpike d)
    (hBackgroundTransfer :
      ∀ᶠ d in atTop,
        ∀ X : SampleMatrix p q σ,
          sampleColumnComplementNormalized
              (p := p) (q := q) (σ := σ) X α₀ ∈
            backgroundTypicalSet
              (p := p) (q := q) (σ := σ)
              (upperConcreteN d) (M d) (τ d) (center d) k →
          backgroundMomentValue
              (p := p) (q := q) (σ := σ) (upperConcreteN d) k
              (sampleColumnComplementNormalized
                (p := p) (q := q) (σ := σ) X α₀) -
            errScale d ≤
          columnBackgroundContribution
            (p := p) (q := q) (σ := σ) (upperConcreteN d) k X α₀)
    (hBackgroundError :
      ∀ᶠ d in atTop, τ d + errScale d ≤ errBg d)
    (hMixed :
      ∀ᶠ d in atTop,
        ∀ X : SampleMatrix p q σ,
          X ∈ sphericalOneColumnFavorableEvent
              (p := p) (q := q) (σ := σ)
              α₀ (q₀ d) (δ d) (directionSet d)
              (backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M d) (τ d) (center d) k) →
          |columnMixedRemainder
              (p := p) (q := q) (σ := σ) (upperConcreteN d) k X α₀| ≤
            errMix d)
    (hMean :
      ∀ᶠ d in atTop,
        upperConcreteMean (p := p) (q := q) (σ := σ) k d ≤
          center d + errMean d)
    (hBudget :
      ∀ᶠ d in atTop,
        eps + errSpike d + errBg d + errMix d + errMean d ≤ a d ^ k)
    (hFullIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (hMoment :
      UpperConcreteMomentBadSetScaleBound
        (p := p) (q := q) (σ := σ) C k)
    (hWordCases :
      UpperConcreteMixedWordCaseBounds
        (p := p) (q := q) (σ := σ)
        R eps k Abound L2bound L1bound Q2bound Q1bound)
    (hDefectLimits :
      UpperConcreteMixedDefectCaseLimits
        k Abound L2bound L1bound Q2bound Q1bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_sequences_of_fullIso_activeTicketSuppliers
    (p := p) (q := q) (σ := σ) R
    (C := C)
    (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
    (Q2bound := Q2bound) (Q1bound := Q1bound)
    hk3 hε
    (upperConcreteOneSidedPositiveDeviationWitness_of_oneColumnFavorableEvent
      (p := p) (q := q) (σ := σ)
      (eps := eps) (k := k) (α₀ := α₀)
      (q₀ := q₀) (δ := δ) (M := M) (a := a) (center := center)
      (errProfile := errProfile) (errSpike := errSpike)
      (τ := τ) (errScale := errScale) (errBg := errBg)
      (errMix := errMix) (errMean := errMean) (directionSet := directionSet)
      hFav_pos hProfile hPureError hBackgroundTransfer hBackgroundError
      hMixed hMean hBudget)
    hFullIso hIsoRealDim hOperatorDim hMoment hWordCases hDefectLimits

/-- Audit-facing lower-bound endpoint for the active ticket frontier.

Use this when another branch has produced an eventually positive lower bound
for the actual one-sided upper-tail event. -/
theorem upper_eventual_from_concrete_sequences_of_fullIso_oneSidedLowerBound_activeTicketSuppliers
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {C : ℝ → ℝ}
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    {lower : ℕ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hlower_pos : ∀ᶠ d in atTop, 0 < lower d)
    (hle :
      ∀ᶠ d in atTop,
        lower d ≤
          (upperConcreteSphericalMu
            (p := p) (q := q) (σ := σ) d).real
            (columnMomentUpperTailSet
              (p := p) (q := q) (σ := σ)
              (upperConcreteN d) eps
              (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k))
    (hFullIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (hMoment :
      UpperConcreteMomentBadSetScaleBound
        (p := p) (q := q) (σ := σ) C k)
    (hWordCases :
      UpperConcreteMixedWordCaseBounds
        (p := p) (q := q) (σ := σ)
        R eps k Abound L2bound L1bound Q2bound Q1bound)
    (hDefectLimits :
      UpperConcreteMixedDefectCaseLimits
        k Abound L2bound L1bound Q2bound Q1bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_sequences_of_fullIso_activeTicketSuppliers
    (p := p) (q := q) (σ := σ) R
    (C := C)
    (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
    (Q2bound := Q2bound) (Q1bound := Q1bound)
    hk3 hε
    (upperConcreteOneSidedPositiveDeviationWitness_of_eventually_positive_lower_bound
      (p := p) (q := q) (σ := σ)
      (eps := eps) (k := k) hlower_pos hle)
    hFullIso hIsoRealDim hOperatorDim hMoment hWordCases hDefectLimits

/-- Sharpened theorem-facing upper endpoint where the mixed scalar asymptotic
input is unpacked into the three actual branches of the word-envelope formula.

Compared with
`upper_eventual_from_concrete_sequences_of_fullIso_positiveDeviationWitness_isolatedMomentConcreteOperatorTails_isolatedMixedWords`,
this theorem no longer takes the packaged proposition
`UpperConcreteMixedTermLimit`.  Instead it asks directly for:

* the one-linear-defect term limit;
* the one-quadratic-defect term limit;
* the remaining multi-defect term limits.

So the mixed scalar leaf is now exposed in the same three-case form used in
the underlying envelope definition. -/
theorem upper_eventual_from_concrete_sequences_of_fullIso_positiveDeviationWitness_isolatedMomentConcreteOperatorTails_isolatedMixedWordBound_caseMixedTermLimits
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {C : ℝ → ℝ}
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    {E : ℕ → Set (SampleMatrix p q σ)}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hTarget :
      UpperConcretePositiveDeviationWitness
        (p := p) (q := q) (σ := σ) eps k E)
    (hFullIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (hMoment :
      UpperConcreteMomentBadSetScaleBound
        (p := p) (q := q) (σ := σ) C k)
    (hWordBound :
      UpperConcreteMixedWordBound
        (p := p) (q := q) (σ := σ)
        R eps k Abound L2bound L1bound Q2bound Q1bound)
    (hOneLinear :
      UpperConcreteOneLinearMixedTermLimit
        k Abound L1bound)
    (hOneQuadratic :
      UpperConcreteOneQuadraticMixedTermLimit
        k Abound Q1bound)
    (hMulti :
      UpperConcreteMultiDefectMixedTermLimit
        k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_sequences_of_fullIso_positiveDeviationWitness_isolatedMomentConcreteOperatorTails_isolatedMixedWords
    (p := p) (q := q) (σ := σ) R
    (C := C)
    (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
    (Q2bound := Q2bound) (Q1bound := Q1bound)
    hk3 hε hTarget hFullIso hIsoRealDim hOperatorDim hMoment hWordBound
    (upperConcreteMixedTermLimit_of_caseLimits
      hOneLinear hOneQuadratic hMulti)

/-- Sharp theorem-facing upper endpoint with the target-positivity witness
fully unpacked.

Compared with
`upper_eventual_from_concrete_sequences_of_fullIso_positiveDeviationWitness_isolatedMomentConcreteOperatorTails_isolatedMixedWordBound_caseMixedTermLimits`,
this theorem no longer takes the packaged proposition
`UpperConcretePositiveDeviationWitness`.  Instead it takes the two underlying
pieces directly:

* `hE_pos`, eventual positivity of the spherical mass of a witness set `E d`;
* `hE_subset`, eventual inclusion of `E d` in the formal deviation event.

So the target-positivity leaf is now exposed in raw set-theoretic form on the
same sharp upper endpoint. -/
theorem upper_eventual_from_concrete_sequences_of_fullIso_positiveDeviationWitnessData_isolatedMomentConcreteOperatorTails_isolatedMixedWordBound_caseMixedTermLimits
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {C : ℝ → ℝ}
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    {E : ℕ → Set (SampleMatrix p q σ)}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hE_pos :
      ∀ᶠ d in atTop,
        0 <
          (upperConcreteSphericalMu
            (p := p) (q := q) (σ := σ) d).real (E d))
    (hE_subset :
      ∀ᶠ d in atTop,
        E d ⊆
          backgroundMomentDeviationSet
            (p := p) (q := q) (σ := σ)
            (upperConcreteN d) eps
            (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k)
    (hFullIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (hMoment :
      UpperConcreteMomentBadSetScaleBound
        (p := p) (q := q) (σ := σ) C k)
    (hWordBound :
      UpperConcreteMixedWordBound
        (p := p) (q := q) (σ := σ)
        R eps k Abound L2bound L1bound Q2bound Q1bound)
    (hOneLinear :
      UpperConcreteOneLinearMixedTermLimit
        k Abound L1bound)
    (hOneQuadratic :
      UpperConcreteOneQuadraticMixedTermLimit
        k Abound Q1bound)
    (hMulti :
      UpperConcreteMultiDefectMixedTermLimit
        k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_sequences_of_fullIso_positiveDeviationWitness_isolatedMomentConcreteOperatorTails_isolatedMixedWordBound_caseMixedTermLimits
    (p := p) (q := q) (σ := σ) R
    (C := C)
    (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
    (Q2bound := Q2bound) (Q1bound := Q1bound)
    (E := E)
    hk3 hε
    ⟨hE_pos, hE_subset⟩
    hFullIso hIsoRealDim hOperatorDim hMoment hWordBound
    hOneLinear hOneQuadratic hMulti

/-- Sharp theorem-facing upper endpoint with the isolated moment package
replaced by its local-expansion supplier data.

Compared with
`upper_eventual_from_concrete_sequences_of_fullIso_positiveDeviationWitnessData_isolatedMomentConcreteOperatorTails_isolatedMixedWordBound_caseMixedTermLimits`,
this theorem no longer takes `hMoment` as a packaged proposition.  Instead it
asks directly for the local-expansion ingredients that produce the canonical
moment bad-set bound:

* half-mass of the chosen background typical set;
* mixed-remainder control at the chosen sharp radius and inner tolerance;
* the scalar budget `a^k + eta + tau < upperCanonicalTau`;
* the final exponential envelope bound.

So this endpoint pushes the moment branch down to the genuine local-expansion
frontier while keeping the theorem-facing mixed-word case split. -/
theorem upper_eventual_from_concrete_sequences_of_fullIso_positiveDeviationWitnessData_localExpansionMoment_isolatedMixedWordBound_caseMixedTermLimits
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {C : ℝ → ℝ}
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    {E : ℕ → Set (SampleMatrix p q σ)}
    {aSlack etaSlack : ℝ → ℝ}
    {M τ : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hE_pos :
      ∀ᶠ d in atTop,
        0 <
          (upperConcreteSphericalMu
            (p := p) (q := q) (σ := σ) d).real (E d))
    (hE_subset :
      ∀ᶠ d in atTop,
        E d ⊆
          backgroundMomentDeviationSet
            (p := p) (q := q) (σ := σ)
            (upperConcreteN d) eps
            (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k)
    (hFullIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (ha : ∀ slack : ℝ, 0 < slack → 0 ≤ aSlack slack)
    (hK_half :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          1 / 2 ≤
            (upperConcreteSphericalMu (p := p) (q := q) (σ := σ) d).real
              (backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k))
    (hMixed :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y : SampleMatrix p q σ⦄,
            Y ∈ backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k →
            frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed k d) (aSlack slack) →
            |localExpansionMixedRemainder
                (p := p) (q := q) (upperConcreteN d) k
                (localBackground (p := p) (q := q) (σ := σ) Y)
                (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))| ≤
              etaSlack slack)
    (hBudget :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          aSlack slack ^ k + etaSlack slack + τ slack d <
            upperCanonicalTau slack d)
    (hEnvelope :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          Real.exp
              (-(((upperConcreteRealDim R d - 1) *
                  sharpSphericalRadiusSq
                    (upperConcreteN d) (spikeSpeed k d) (aSlack slack)) /
                2)) ≤
            upperConcreteMomentBoundScale C slack d)
    (hWordBound :
      UpperConcreteMixedWordBound
        (p := p) (q := q) (σ := σ)
        R eps k Abound L2bound L1bound Q2bound Q1bound)
    (hOneLinear :
      UpperConcreteOneLinearMixedTermLimit
        k Abound L1bound)
    (hOneQuadratic :
      UpperConcreteOneQuadraticMixedTermLimit
        k Abound Q1bound)
    (hMulti :
      UpperConcreteMultiDefectMixedTermLimit
        k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_sequences_of_fullIso_positiveDeviationWitnessData_isolatedMomentConcreteOperatorTails_isolatedMixedWordBound_caseMixedTermLimits
    (p := p) (q := q) (σ := σ) R
    (C := C)
    (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
    (Q2bound := Q2bound) (Q1bound := Q1bound)
    (E := E)
    hk3 hε hE_pos hE_subset hFullIso hIsoRealDim hOperatorDim
    (upperConcreteMomentBadSetScaleBound_of_localExpansion_envelope
      (p := p) (q := q) (σ := σ) R
      (C := C) (k := k)
      (aSlack := aSlack) (etaSlack := etaSlack)
      (M := M) (τ := τ)
      hk3 hFullIso hIsoRealDim ha hK_half hMixed hBudget hEnvelope)
    hWordBound hOneLinear hOneQuadratic hMulti

/-- Sharp theorem-facing upper endpoint with both packaged mixed leaves fully
replaced by their explicit casewise branches.

Compared with
`upper_eventual_from_concrete_sequences_of_fullIso_positiveDeviationWitnessData_localExpansionMoment_isolatedMixedWordBound_caseMixedTermLimits`,
this theorem no longer takes the packaged mixed-word proposition
`UpperConcreteMixedWordBound`.  Instead it asks directly for the three
deterministic branches matching the word-envelope formula:

* one-linear-defect word bounds;
* one-quadratic-defect word bounds;
* the remaining multi-defect word bounds.

Together with the previously exposed mixed-term case limits, this leaves the
mixed frontier in fully casewise form on the sharp branch. -/
theorem upper_eventual_from_concrete_sequences_of_fullIso_positiveDeviationWitnessData_localExpansionMoment_caseMixedWordBounds_caseMixedTermLimits
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {C : ℝ → ℝ}
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    {E : ℕ → Set (SampleMatrix p q σ)}
    {aSlack etaSlack : ℝ → ℝ}
    {M τ : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hE_pos :
      ∀ᶠ d in atTop,
        0 <
          (upperConcreteSphericalMu
            (p := p) (q := q) (σ := σ) d).real (E d))
    (hE_subset :
      ∀ᶠ d in atTop,
        E d ⊆
          backgroundMomentDeviationSet
            (p := p) (q := q) (σ := σ)
            (upperConcreteN d) eps
            (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k)
    (hFullIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (ha : ∀ slack : ℝ, 0 < slack → 0 ≤ aSlack slack)
    (hK_half :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          1 / 2 ≤
            (upperConcreteSphericalMu (p := p) (q := q) (σ := σ) d).real
              (backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k))
    (hMixed :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y : SampleMatrix p q σ⦄,
            Y ∈ backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k →
            frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed k d) (aSlack slack) →
            |localExpansionMixedRemainder
                (p := p) (q := q) (upperConcreteN d) k
                (localBackground (p := p) (q := q) (σ := σ) Y)
                (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))| ≤
              etaSlack slack)
    (hBudget :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          aSlack slack ^ k + etaSlack slack + τ slack d <
            upperCanonicalTau slack d)
    (hEnvelope :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          Real.exp
              (-(((upperConcreteRealDim R d - 1) *
                  sharpSphericalRadiusSq
                    (upperConcreteN d) (spikeSpeed k d) (aSlack slack)) /
                2)) ≤
            upperConcreteMomentBoundScale C slack d)
    (hOneLinearWord :
      UpperConcreteOneLinearMixedWordBound
        (p := p) (q := q) (σ := σ)
        R eps k Abound L1bound)
    (hOneQuadraticWord :
      UpperConcreteOneQuadraticMixedWordBound
        (p := p) (q := q) (σ := σ)
        R eps k Abound Q1bound)
    (hMultiWord :
      UpperConcreteMultiDefectMixedWordBound
        (p := p) (q := q) (σ := σ)
        R eps k Abound L2bound Q2bound)
    (hOneLinear :
      UpperConcreteOneLinearMixedTermLimit
        k Abound L1bound)
    (hOneQuadratic :
      UpperConcreteOneQuadraticMixedTermLimit
        k Abound Q1bound)
    (hMulti :
      UpperConcreteMultiDefectMixedTermLimit
        k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_sequences_of_fullIso_positiveDeviationWitnessData_localExpansionMoment_isolatedMixedWordBound_caseMixedTermLimits
    (p := p) (q := q) (σ := σ) R
    (C := C)
    (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
    (Q2bound := Q2bound) (Q1bound := Q1bound)
    (E := E)
    (aSlack := aSlack) (etaSlack := etaSlack)
    (M := M) (τ := τ)
    hk3 hε hE_pos hE_subset hFullIso hIsoRealDim hOperatorDim
    ha hK_half hMixed hBudget hEnvelope
    (upperConcreteMixedWordBound_of_caseBounds
      hOneLinearWord hOneQuadraticWord hMultiWord)
    hOneLinear hOneQuadratic hMulti

/-- Sharp theorem-facing upper endpoint with the moment-side mixed-remainder
input replaced by word-envelope data.

Compared with
`upper_eventual_from_concrete_sequences_of_fullIso_positiveDeviationWitnessData_localExpansionMoment_caseMixedWordBounds_caseMixedTermLimits`,
this theorem no longer takes the raw moment-side `hMixed` assumption.  It
derives that assumption from:

* a uniform word-by-word bound for the local-expansion mixed remainder used in
  the moment concentration supplier;
* scalar limits saying each corresponding word envelope tends to zero.
* positivity of the inner mixed-remainder tolerance `etaSlack`.

This keeps the final mixed-word upper branch in its casewise form while also
pushing the moment-concentration mixed input down to the same deterministic
word-envelope mechanism. -/
theorem upper_eventual_from_concrete_sequences_of_fullIso_positiveDeviationWitnessData_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {C : ℝ → ℝ}
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    {momentAbound momentL2bound momentL1bound momentQ2bound momentQ1bound :
      ℝ → ℕ → ℝ}
    {E : ℕ → Set (SampleMatrix p q σ)}
    {aSlack etaSlack : ℝ → ℝ}
    {M τ : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hE_pos :
      ∀ᶠ d in atTop,
        0 <
          (upperConcreteSphericalMu
            (p := p) (q := q) (σ := σ) d).real (E d))
    (hE_subset :
      ∀ᶠ d in atTop,
        E d ⊆
          backgroundMomentDeviationSet
            (p := p) (q := q) (σ := σ)
            (upperConcreteN d) eps
            (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k)
    (hFullIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (ha : ∀ slack : ℝ, 0 < slack → 0 ≤ aSlack slack)
    (hK_half :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          1 / 2 ≤
            (upperConcreteSphericalMu (p := p) (q := q) (σ := σ) d).real
              (backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k))
    (hEta : ∀ slack : ℝ, 0 < slack → 0 < etaSlack slack)
    (hMomentWordBound :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y : SampleMatrix p q σ⦄,
            Y ∈ backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k →
            frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed k d) (aSlack slack) →
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                |localWordScaledTraceTerm
                    (p := p) (q := q)
                    (upperConcreteN d)
                    (localBackground (p := p) (q := q) (σ := σ) Y)
                    (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                    (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
                    w| ≤
                  localExpansionMixedWordEnvelopeTerm
                    (upperConcreteN d)
                    (momentAbound slack d) (momentL2bound slack d)
                    (momentL1bound slack d) (momentQ2bound slack d)
                    (momentQ1bound slack d) k w)
    (hMomentTermLimit :
      ∀ slack : ℝ, 0 < slack →
        ∀ w : Fin k → LocalExpansionLetter,
          localWordIsMixed w →
            Tendsto
              (fun d =>
                localExpansionMixedWordEnvelopeTerm
                  (upperConcreteN d)
                  (momentAbound slack d) (momentL2bound slack d)
                  (momentL1bound slack d) (momentQ2bound slack d)
                  (momentQ1bound slack d) k w)
              atTop (nhds 0))
    (hBudget :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          aSlack slack ^ k + etaSlack slack + τ slack d <
            upperCanonicalTau slack d)
    (hEnvelope :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          Real.exp
              (-(((upperConcreteRealDim R d - 1) *
                  sharpSphericalRadiusSq
                    (upperConcreteN d) (spikeSpeed k d) (aSlack slack)) /
                2)) ≤
            upperConcreteMomentBoundScale C slack d)
    (hOneLinearWord :
      UpperConcreteOneLinearMixedWordBound
        (p := p) (q := q) (σ := σ)
        R eps k Abound L1bound)
    (hOneQuadraticWord :
      UpperConcreteOneQuadraticMixedWordBound
        (p := p) (q := q) (σ := σ)
        R eps k Abound Q1bound)
    (hMultiWord :
      UpperConcreteMultiDefectMixedWordBound
        (p := p) (q := q) (σ := σ)
        R eps k Abound L2bound Q2bound)
    (hOneLinear :
      UpperConcreteOneLinearMixedTermLimit
        k Abound L1bound)
    (hOneQuadratic :
      UpperConcreteOneQuadraticMixedTermLimit
        k Abound Q1bound)
    (hMulti :
      UpperConcreteMultiDefectMixedTermLimit
        k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hk1 : 1 ≤ k := le_trans (by norm_num : 1 ≤ 3) hk3
  have hMixed :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y : SampleMatrix p q σ⦄,
            Y ∈ backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k →
            frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed k d) (aSlack slack) →
            |localExpansionMixedRemainder
                (p := p) (q := q) (upperConcreteN d) k
                (localBackground (p := p) (q := q) (σ := σ) Y)
                (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))| ≤
              etaSlack slack := by
    intro slack hslack
    exact
      upper_hMixed_from_uniform_mixedWordBounds_and_termLimits
        (p := p) (q := q) (σ := σ)
        (N := upperConcreteN)
        (speed := spikeSpeed k)
        (aSlack := aSlack)
        (M := M)
        (τ := τ)
        (mean := fun _ d =>
          upperConcreteMean (p := p) (q := q) (σ := σ) k d)
        (Abound := momentAbound)
        (L2bound := momentL2bound)
        (L1bound := momentL1bound)
        (Q2bound := momentQ2bound)
        (Q1bound := momentQ1bound)
        (k := k) hk1 hMomentWordBound hMomentTermLimit
        slack hslack (etaSlack slack) (hEta slack hslack)
  exact
    upper_eventual_from_concrete_sequences_of_fullIso_positiveDeviationWitnessData_localExpansionMoment_caseMixedWordBounds_caseMixedTermLimits
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
      (Q2bound := Q2bound) (Q1bound := Q1bound)
      (E := E)
      (aSlack := aSlack) (etaSlack := etaSlack)
      (M := M) (τ := τ)
      hk3 hε hE_pos hE_subset hFullIso hIsoRealDim hOperatorDim
      ha hK_half hMixed hBudget hEnvelope
      hOneLinearWord hOneQuadraticWord hMultiWord
      hOneLinear hOneQuadratic hMulti

/-- Sharp theorem-facing upper endpoint with the target witness specialized to
the canonical one-sided upper event.

This removes the raw witness data `hE_pos`/`hE_subset` from the sharp
word-envelope endpoint.  The remaining positivity input is the more meaningful
one-sided statement
`UpperConcreteOneSidedPositiveDeviationWitness`; the subset inclusion into the
formal absolute-deviation target is supplied by
`upper_targetWitness_of_upperConcreteOneSidedPositiveDeviationWitness`. -/
theorem upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {C : ℝ → ℝ}
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    {momentAbound momentL2bound momentL1bound momentQ2bound momentQ1bound :
      ℝ → ℕ → ℝ}
    {aSlack etaSlack : ℝ → ℝ}
    {M τ : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hOneSided :
      UpperConcreteOneSidedPositiveDeviationWitness
        (p := p) (q := q) (σ := σ) eps k)
    (hFullIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (ha : ∀ slack : ℝ, 0 < slack → 0 ≤ aSlack slack)
    (hK_half :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          1 / 2 ≤
            (upperConcreteSphericalMu (p := p) (q := q) (σ := σ) d).real
              (backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k))
    (hEta : ∀ slack : ℝ, 0 < slack → 0 < etaSlack slack)
    (hMomentWordBound :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y : SampleMatrix p q σ⦄,
            Y ∈ backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k →
            frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed k d) (aSlack slack) →
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                |localWordScaledTraceTerm
                    (p := p) (q := q)
                    (upperConcreteN d)
                    (localBackground (p := p) (q := q) (σ := σ) Y)
                    (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                    (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
                    w| ≤
                  localExpansionMixedWordEnvelopeTerm
                    (upperConcreteN d)
                    (momentAbound slack d) (momentL2bound slack d)
                    (momentL1bound slack d) (momentQ2bound slack d)
                    (momentQ1bound slack d) k w)
    (hMomentTermLimit :
      ∀ slack : ℝ, 0 < slack →
        ∀ w : Fin k → LocalExpansionLetter,
          localWordIsMixed w →
            Tendsto
              (fun d =>
                localExpansionMixedWordEnvelopeTerm
                  (upperConcreteN d)
                  (momentAbound slack d) (momentL2bound slack d)
                  (momentL1bound slack d) (momentQ2bound slack d)
                  (momentQ1bound slack d) k w)
              atTop (nhds 0))
    (hBudget :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          aSlack slack ^ k + etaSlack slack + τ slack d <
            upperCanonicalTau slack d)
    (hEnvelope :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          Real.exp
              (-(((upperConcreteRealDim R d - 1) *
                  sharpSphericalRadiusSq
                    (upperConcreteN d) (spikeSpeed k d) (aSlack slack)) /
                2)) ≤
            upperConcreteMomentBoundScale C slack d)
    (hOneLinearWord :
      UpperConcreteOneLinearMixedWordBound
        (p := p) (q := q) (σ := σ)
        R eps k Abound L1bound)
    (hOneQuadraticWord :
      UpperConcreteOneQuadraticMixedWordBound
        (p := p) (q := q) (σ := σ)
        R eps k Abound Q1bound)
    (hMultiWord :
      UpperConcreteMultiDefectMixedWordBound
        (p := p) (q := q) (σ := σ)
        R eps k Abound L2bound Q2bound)
    (hOneLinear :
      UpperConcreteOneLinearMixedTermLimit
        k Abound L1bound)
    (hOneQuadratic :
      UpperConcreteOneQuadraticMixedTermLimit
        k Abound Q1bound)
    (hMulti :
      UpperConcreteMultiDefectMixedTermLimit
        k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hTarget :
      UpperConcretePositiveDeviationWitness
        (p := p) (q := q) (σ := σ) eps k
        (fun d =>
          columnMomentUpperTailSet
            (p := p) (q := q) (σ := σ)
            (upperConcreteN d) eps
            (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k) :=
    upper_targetWitness_of_upperConcreteOneSidedPositiveDeviationWitness
      (p := p) (q := q) (σ := σ) hOneSided
  exact
    upper_eventual_from_concrete_sequences_of_fullIso_positiveDeviationWitnessData_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
      (Q2bound := Q2bound) (Q1bound := Q1bound)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (E := fun d =>
        columnMomentUpperTailSet
          (p := p) (q := q) (σ := σ)
          (upperConcreteN d) eps
          (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k)
      (aSlack := aSlack) (etaSlack := etaSlack)
      (M := M) (τ := τ)
      hk3 hε hTarget.1 hTarget.2 hFullIso hIsoRealDim hOperatorDim
      ha hK_half hEta hMomentWordBound hMomentTermLimit hBudget hEnvelope
      hOneLinearWord hOneQuadraticWord hMultiWord
      hOneLinear hOneQuadratic hMulti

/-- Canonical-scalar specialization of the sharp endpoint: the one-quadratic
mixed-word branch is supplied by
`upperConcreteOneQuadraticMixedWordBound_of_canonical_oneQ` rather than assumed. -/
theorem upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQ
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {C : ℝ → ℝ}
    {L2bound L1bound Q2bound : ℝ → ℕ → ℝ}
    {momentAbound momentL2bound momentL1bound momentQ2bound momentQ1bound :
      ℝ → ℕ → ℝ}
    {aSlack etaSlack : ℝ → ℝ}
    {M τ : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hOneSided :
      UpperConcreteOneSidedPositiveDeviationWitness
        (p := p) (q := q) (σ := σ) eps k)
    (hFullIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (ha : ∀ slack : ℝ, 0 < slack → 0 ≤ aSlack slack)
    (hK_half :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          1 / 2 ≤
            (upperConcreteSphericalMu (p := p) (q := q) (σ := σ) d).real
              (backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k))
    (hEta : ∀ slack : ℝ, 0 < slack → 0 < etaSlack slack)
    (hMomentWordBound :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y : SampleMatrix p q σ⦄,
            Y ∈ backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k →
            frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed k d) (aSlack slack) →
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                |localWordScaledTraceTerm
                    (p := p) (q := q)
                    (upperConcreteN d)
                    (localBackground (p := p) (q := q) (σ := σ) Y)
                    (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                    (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
                    w| ≤
                  localExpansionMixedWordEnvelopeTerm
                    (upperConcreteN d)
                    (momentAbound slack d) (momentL2bound slack d)
                    (momentL1bound slack d) (momentQ2bound slack d)
                    (momentQ1bound slack d) k w)
    (hMomentTermLimit :
      ∀ slack : ℝ, 0 < slack →
        ∀ w : Fin k → LocalExpansionLetter,
          localWordIsMixed w →
            Tendsto
              (fun d =>
                localExpansionMixedWordEnvelopeTerm
                  (upperConcreteN d)
                  (momentAbound slack d) (momentL2bound slack d)
                  (momentL1bound slack d) (momentQ2bound slack d)
                  (momentQ1bound slack d) k w)
              atTop (nhds 0))
    (hBudget :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          aSlack slack ^ k + etaSlack slack + τ slack d <
            upperCanonicalTau slack d)
    (hEnvelope :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          Real.exp
              (-(((upperConcreteRealDim R d - 1) *
                  sharpSphericalRadiusSq
                    (upperConcreteN d) (spikeSpeed k d) (aSlack slack)) /
                2)) ≤
            upperConcreteMomentBoundScale C slack d)
    (hOneLinearWord :
      UpperConcreteOneLinearMixedWordBound
        (p := p) (q := q) (σ := σ)
        R eps k
        (fun slack d => upperConcreteMixedWordAboundCanonical (p := p) (q := q) (σ := σ) slack d)
        L1bound)
    (hMultiWord :
      UpperConcreteMultiDefectMixedWordBound
        (p := p) (q := q) (σ := σ)
        R eps k
        (fun slack d => upperConcreteMixedWordAboundCanonical (p := p) (q := q) (σ := σ) slack d)
        L2bound Q2bound)
    (hOneLinear :
      UpperConcreteOneLinearMixedTermLimit
        k
        (fun slack d => upperConcreteMixedWordAboundCanonical (p := p) (q := q) (σ := σ) slack d)
        L1bound)
    (hOneQuadratic :
      UpperConcreteOneQuadraticMixedTermLimit
        k
        (fun slack d => upperConcreteMixedWordAboundCanonical (p := p) (q := q) (σ := σ) slack d)
        (fun slack d => upperConcreteMixedWordQ1boundCanonical (p := p) (q := q) (σ := σ) R eps k slack d))
    (hMulti :
      UpperConcreteMultiDefectMixedTermLimit
        k
        (fun slack d => upperConcreteMixedWordAboundCanonical (p := p) (q := q) (σ := σ) slack d)
        L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits
    (p := p) (q := q) (σ := σ) R
    (C := C)
    (Abound := fun slack d => upperConcreteMixedWordAboundCanonical (p := p) (q := q) (σ := σ) slack d)
    (L2bound := L2bound) (L1bound := L1bound) (Q2bound := Q2bound)
    (Q1bound := fun slack d => upperConcreteMixedWordQ1boundCanonical (p := p) (q := q) (σ := σ) R eps k slack d)
    (momentAbound := momentAbound) (momentL2bound := momentL2bound)
    (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
    (momentQ1bound := momentQ1bound)
    (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
    hk3 hε hOneSided hFullIso hIsoRealDim hOperatorDim ha hK_half hEta
    hMomentWordBound hMomentTermLimit hBudget hEnvelope hOneLinearWord
    (upperConcreteOneQuadraticMixedWordBound_of_canonical_oneQ (p := p) (q := q) (σ := σ) R hk3 hε)
    hMultiWord hOneLinear hOneQuadratic hMulti

/-- Canonical-scalar one-`Q` specialization of the sharp endpoint with the
one-quadratic, one-linear, and multi-defect mixed-word branches and their
scalar term limits supplied internally. -/
theorem upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {C : ℝ → ℝ}
    {momentAbound momentL2bound momentL1bound momentQ2bound momentQ1bound :
      ℝ → ℕ → ℝ}
    {aSlack etaSlack : ℝ → ℝ}
    {M τ : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hOneSided :
      UpperConcreteOneSidedPositiveDeviationWitness
        (p := p) (q := q) (σ := σ) eps k)
    (hFullIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (ha : ∀ slack : ℝ, 0 < slack → 0 ≤ aSlack slack)
    (hK_half :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          1 / 2 ≤
            (upperConcreteSphericalMu (p := p) (q := q) (σ := σ) d).real
              (backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k))
    (hEta : ∀ slack : ℝ, 0 < slack → 0 < etaSlack slack)
    (hMomentWordBound :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y : SampleMatrix p q σ⦄,
            Y ∈ backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k →
            frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed k d) (aSlack slack) →
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                |localWordScaledTraceTerm
                    (p := p) (q := q)
                    (upperConcreteN d)
                    (localBackground (p := p) (q := q) (σ := σ) Y)
                    (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                    (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
                    w| ≤
                  localExpansionMixedWordEnvelopeTerm
                    (upperConcreteN d)
                    (momentAbound slack d) (momentL2bound slack d)
                    (momentL1bound slack d) (momentQ2bound slack d)
                    (momentQ1bound slack d) k w)
    (hMomentTermLimit :
      ∀ slack : ℝ, 0 < slack →
        ∀ w : Fin k → LocalExpansionLetter,
          localWordIsMixed w →
            Tendsto
              (fun d =>
                localExpansionMixedWordEnvelopeTerm
                  (upperConcreteN d)
                  (momentAbound slack d) (momentL2bound slack d)
                  (momentL1bound slack d) (momentQ2bound slack d)
                  (momentQ1bound slack d) k w)
              atTop (nhds 0))
    (hBudget :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          aSlack slack ^ k + etaSlack slack + τ slack d <
            upperCanonicalTau slack d)
    (hEnvelope :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          Real.exp
              (-(((upperConcreteRealDim R d - 1) *
                  sharpSphericalRadiusSq
                    (upperConcreteN d) (spikeSpeed k d) (aSlack slack)) /
                2)) ≤
            upperConcreteMomentBoundScale C slack d) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQ
    (p := p) (q := q) (σ := σ) R
    (C := C)
    (L2bound := fun slack d =>
      upperConcreteMixedWordL2boundCanonical (p := p) (q := q) (σ := σ) R eps k slack d)
    (L1bound := fun slack d =>
      upperConcreteMixedWordL1boundCanonical (p := p) (q := q) (σ := σ) R eps k slack d)
    (Q2bound := fun slack d =>
      upperConcreteMixedWordQ2boundCanonical (p := p) (q := q) (σ := σ) R eps k slack d)
    (momentAbound := momentAbound) (momentL2bound := momentL2bound)
    (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
    (momentQ1bound := momentQ1bound)
    (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
    hk3 hε hOneSided hFullIso hIsoRealDim hOperatorDim ha hK_half hEta
    hMomentWordBound hMomentTermLimit hBudget hEnvelope
    (upperConcreteOneLinearMixedWordBound_of_canonical_oneL
      (p := p) (q := q) (σ := σ) R hk3 hε)
    (upperConcreteMultiDefectMixedWordBound_of_canonical_multi
      (p := p) (q := q) (σ := σ) R hk3 hε)
    (upperConcreteOneLinearMixedTermLimit_of_canonical_oneL
      (p := p) (q := q) (σ := σ) R hk3 hε)
    (upperConcreteOneQuadraticMixedTermLimit_of_canonical_oneQ
      (p := p) (q := q) (σ := σ) R hk3 hε)
    (upperConcreteMultiDefectMixedTermLimit_of_canonical_multi
      (p := p) (q := q) (σ := σ) R hk3 hε)

/-- Sharp canonical upper endpoint with `FullSphericalIsoperimetry` replaced by
the current two geometric frontier suppliers: the separate-scale Lemma 4.3
height-band package for the half-mass hemisphere comparison, and the north-pole
cap-cone tail supplier for the Gaussian hemisphere tail. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43SeparateTau_coordinateTail_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {C : ℝ → ℝ}
    {momentAbound momentL2bound momentL1bound momentQ2bound momentQ1bound :
      ℝ → ℕ → ℝ}
    {aSlack etaSlack : ℝ → ℝ}
    {M τ : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hOneSided :
      UpperConcreteOneSidedPositiveDeviationWitness
        (p := p) (q := q) (σ := σ) eps k)
    (hLemma43SeparateTau :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tauBand tauSep : ℝ, 0 < eps ∧ 0 < tauSep ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                ∃ Cmodel : Set (PptFactorization.AppendixB.FinRealSphere n),
                  ∃ pole : PptFactorization.AppendixB.FinRealSphere n,
                  ∃ a avg : ℝ,
                    MeasurableSet Cmodel ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real Cmodel =
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real A ∧
                    eps ≤
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (Cmodel ∆ A) ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                          n pole a tauBand) ≤ eps / 4 ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                          n pole a tauBand) ≤ eps / 4 ∧
                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tauSep
                      (PptFactorization.AppendixB.finRealPolarizationMuMinus Cmodel A
                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                          n pole a tauBand))
                      (PptFactorization.AppendixB.finRealPolarizationMuPlus Cmodel A
                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                          n pole a tauBand))
                      avg ∧
                    avg ≤
                      sSup
                        (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                          n r A))
    (hCoordTailInterior :
      PptFactorization.AppendixB.sphere_northPoleCapConeGaussianTailLargeExponent)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (ha : ∀ slack : ℝ, 0 < slack → 0 ≤ aSlack slack)
    (hK_half :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          1 / 2 ≤
            (upperConcreteSphericalMu (p := p) (q := q) (σ := σ) d).real
              (backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k))
    (hEta : ∀ slack : ℝ, 0 < slack → 0 < etaSlack slack)
    (hMomentWordBound :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y : SampleMatrix p q σ⦄,
            Y ∈ backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k →
            frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed k d) (aSlack slack) →
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                |localWordScaledTraceTerm
                    (p := p) (q := q)
                    (upperConcreteN d)
                    (localBackground (p := p) (q := q) (σ := σ) Y)
                    (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                    (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
                    w| ≤
                  localExpansionMixedWordEnvelopeTerm
                    (upperConcreteN d)
                    (momentAbound slack d) (momentL2bound slack d)
                    (momentL1bound slack d) (momentQ2bound slack d)
                    (momentQ1bound slack d) k w)
    (hMomentTermLimit :
      ∀ slack : ℝ, 0 < slack →
        ∀ w : Fin k → LocalExpansionLetter,
          localWordIsMixed w →
            Tendsto
              (fun d =>
                localExpansionMixedWordEnvelopeTerm
                  (upperConcreteN d)
                  (momentAbound slack d) (momentL2bound slack d)
                  (momentL1bound slack d) (momentQ2bound slack d)
                  (momentQ1bound slack d) k w)
              atTop (nhds 0))
    (hBudget :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          aSlack slack ^ k + etaSlack slack + τ slack d <
            upperCanonicalTau slack d)
    (hEnvelope :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          Real.exp
              (-(((upperConcreteRealDim R d - 1) *
                  sharpSphericalRadiusSq
                    (upperConcreteN d) (spikeSpeed k d) (aSlack slack)) /
                2)) ≤
            upperConcreteMomentBoundScale C slack d) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hCompare :
      PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo :=
    PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo_of_lemma43_heightBands_separateTau_gainSup_equal_mass_pos_lt_pi
      hLemma43SeparateTau
  have hTail :
      PptFactorization.AppendixB.sphere_hemisphereGaussianTail :=
    PptFactorization.AppendixB.sphere_hemisphereGaussianTail_of_coordinateDominance_and_coordinateTail
      PptFactorization.AppendixB.sphere_hemisphereComplementCoordinateDominance_surface
      (PptFactorization.AppendixB.sphere_coordinateGaussianTail_of_interior
        (PptFactorization.AppendixB.sphere_coordinateGaussianTailInterior_of_geTwo
          (PptFactorization.AppendixB.sphere_coordinateGaussianTailInteriorGeTwo_of_largeExponent
            (PptFactorization.AppendixB.sphere_coordinateGaussianTailInteriorLargeExponent_of_northPole
              (PptFactorization.AppendixB.sphere_coordinateGaussianTailInteriorLargeExponentNorthPole_of_coneTail
                hCoordTailInterior))))) PptFactorization.AppendixB.sphere_hemisphereLargeRadiusTail_surface
  have hFullIso :
      PptFactorization.AppendixB.FullSphericalIsoperimetry :=
    PptFactorization.AppendixB.fullSphericalIsoperimetry_of_hemisphereComparison_and_tail
      (PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparison_of_geTwo hCompare) hTail
  exact
    upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hFullIso hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope

/-- Sharp canonical upper endpoint with the north-pole tail stated directly as
the normalized spherical coordinate-law package, then lifted to the cone-volume
form consumed by the existing geometry pipeline. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43SeparateTau_northPoleCoordinateTail_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {C : ℝ → ℝ}
    {momentAbound momentL2bound momentL1bound momentQ2bound momentQ1bound :
      ℝ → ℕ → ℝ}
    {aSlack etaSlack : ℝ → ℝ}
    {M τ : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hOneSided :
      UpperConcreteOneSidedPositiveDeviationWitness
        (p := p) (q := q) (σ := σ) eps k)
    (hLemma43SeparateTau :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tauBand tauSep : ℝ, 0 < eps ∧ 0 < tauSep ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                ∃ Cmodel : Set (PptFactorization.AppendixB.FinRealSphere n),
                  ∃ pole : PptFactorization.AppendixB.FinRealSphere n,
                  ∃ a avg : ℝ,
                    MeasurableSet Cmodel ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real Cmodel =
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real A ∧
                    eps ≤
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (Cmodel ∆ A) ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                          n pole a tauBand) ≤ eps / 4 ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                          n pole a tauBand) ≤ eps / 4 ∧
                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tauSep
                      (PptFactorization.AppendixB.finRealPolarizationMuMinus Cmodel A
                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                          n pole a tauBand))
                      (PptFactorization.AppendixB.finRealPolarizationMuPlus Cmodel A
                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                          n pole a tauBand))
                      avg ∧
                    avg ≤
                      sSup
                        (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                          n r A))
    (hCoordTailInterior :
      PptFactorization.AppendixB.sphere_coordinateGaussianTailInteriorLargeExponentNorthPole)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (ha : ∀ slack : ℝ, 0 < slack → 0 ≤ aSlack slack)
    (hK_half :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          1 / 2 ≤
            (upperConcreteSphericalMu (p := p) (q := q) (σ := σ) d).real
              (backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k))
    (hEta : ∀ slack : ℝ, 0 < slack → 0 < etaSlack slack)
    (hMomentWordBound :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y : SampleMatrix p q σ⦄,
            Y ∈ backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k →
            frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed k d) (aSlack slack) →
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                |localWordScaledTraceTerm
                    (p := p) (q := q)
                    (upperConcreteN d)
                    (localBackground (p := p) (q := q) (σ := σ) Y)
                    (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                    (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
                    w| ≤
                  localExpansionMixedWordEnvelopeTerm
                    (upperConcreteN d)
                    (momentAbound slack d) (momentL2bound slack d)
                    (momentL1bound slack d) (momentQ2bound slack d)
                    (momentQ1bound slack d) k w)
    (hMomentTermLimit :
      ∀ slack : ℝ, 0 < slack →
        ∀ w : Fin k → LocalExpansionLetter,
          localWordIsMixed w →
            Tendsto
              (fun d =>
                localExpansionMixedWordEnvelopeTerm
                  (upperConcreteN d)
                  (momentAbound slack d) (momentL2bound slack d)
                  (momentL1bound slack d) (momentQ2bound slack d)
                  (momentQ1bound slack d) k w)
              atTop (nhds 0))
    (hBudget :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          aSlack slack ^ k + etaSlack slack + τ slack d <
            upperCanonicalTau slack d)
    (hEnvelope :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          Real.exp
              (-(((upperConcreteRealDim R d - 1) *
                  sharpSphericalRadiusSq
                    (upperConcreteN d) (spikeSpeed k d) (aSlack slack)) /
                2)) ≤
            upperConcreteMomentBoundScale C slack d) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  exact
    upper_eventual_from_concrete_sequences_of_lemma43SeparateTau_coordinateTail_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hLemma43SeparateTau
      (PptFactorization.AppendixB.sphere_northPoleCapConeGaussianTailLargeExponent_of_coordinateTail
        hCoordTailInterior)
      hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
      hBudget hEnvelope

/-- Sharp canonical upper endpoint with the height-band masses chosen
internally by the spherical height atomlessness adapter.  The remaining
Lemma 4.3 supplier only has to give a same-mass model and a rectangular block
valid for all sufficiently thin height bands. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBands_northPoleCoordinateTail_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {C : ℝ → ℝ}
    {momentAbound momentL2bound momentL1bound momentQ2bound momentQ1bound :
      ℝ → ℕ → ℝ}
    {aSlack etaSlack : ℝ → ℝ}
    {M τ : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hOneSided :
      UpperConcreteOneSidedPositiveDeviationWitness
        (p := p) (q := q) (σ := σ) eps k)
    (hLemma43AutoHeightBands :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tauSep : ℝ, 0 < eps ∧ 0 < tauSep ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                ∃ Cmodel : Set (PptFactorization.AppendixB.FinRealSphere n),
                  ∃ pole : PptFactorization.AppendixB.FinRealSphere n,
                  ∃ a tauMax : ℝ,
                    0 < tauMax ∧
                    MeasurableSet Cmodel ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real Cmodel =
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real A ∧
                    eps ≤
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (Cmodel ∆ A) ∧
                    ∀ ⦃tauBand : ℝ⦄, 0 < tauBand → tauBand ≤ tauMax →
                      ∃ avg : ℝ,
                        SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tauSep
                          (PptFactorization.AppendixB.finRealPolarizationMuMinus Cmodel A
                            (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                              n pole a tauBand))
                          (PptFactorization.AppendixB.finRealPolarizationMuPlus Cmodel A
                            (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                              n pole a tauBand))
                          avg ∧
                        avg ≤
                          sSup
                            (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                              n r A))
    (hCoordTailInterior :
      PptFactorization.AppendixB.sphere_coordinateGaussianTailInteriorLargeExponentNorthPole)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (ha : ∀ slack : ℝ, 0 < slack → 0 ≤ aSlack slack)
    (hK_half :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          1 / 2 ≤
            (upperConcreteSphericalMu (p := p) (q := q) (σ := σ) d).real
              (backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k))
    (hEta : ∀ slack : ℝ, 0 < slack → 0 < etaSlack slack)
    (hMomentWordBound :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y : SampleMatrix p q σ⦄,
            Y ∈ backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k →
            frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed k d) (aSlack slack) →
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                |localWordScaledTraceTerm
                    (p := p) (q := q)
                    (upperConcreteN d)
                    (localBackground (p := p) (q := q) (σ := σ) Y)
                    (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                    (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
                    w| ≤
                  localExpansionMixedWordEnvelopeTerm
                    (upperConcreteN d)
                    (momentAbound slack d) (momentL2bound slack d)
                    (momentL1bound slack d) (momentQ2bound slack d)
                    (momentQ1bound slack d) k w)
    (hMomentTermLimit :
      ∀ slack : ℝ, 0 < slack →
        ∀ w : Fin k → LocalExpansionLetter,
          localWordIsMixed w →
            Tendsto
              (fun d =>
                localExpansionMixedWordEnvelopeTerm
                  (upperConcreteN d)
                  (momentAbound slack d) (momentL2bound slack d)
                  (momentL1bound slack d) (momentQ2bound slack d)
                  (momentQ1bound slack d) k w)
              atTop (nhds 0))
    (hBudget :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          aSlack slack ^ k + etaSlack slack + τ slack d <
            upperCanonicalTau slack d)
    (hEnvelope :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          Real.exp
              (-(((upperConcreteRealDim R d - 1) *
                  sharpSphericalRadiusSq
                    (upperConcreteN d) (spikeSpeed k d) (aSlack slack)) /
                2)) ≤
            upperConcreteMomentBoundScale C slack d) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hCompare :
      PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo :=
    PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo_of_lemma43_autoHeightBands_gainSup_equal_mass_pos_lt_pi
      hLemma43AutoHeightBands
  have hTail :
      PptFactorization.AppendixB.sphere_hemisphereGaussianTail :=
    PptFactorization.AppendixB.sphere_hemisphereGaussianTail_of_coordinateDominance_and_coordinateTail
      PptFactorization.AppendixB.sphere_hemisphereComplementCoordinateDominance_surface
      (PptFactorization.AppendixB.sphere_coordinateGaussianTail_of_interior
        (PptFactorization.AppendixB.sphere_coordinateGaussianTailInterior_of_geTwo
          (PptFactorization.AppendixB.sphere_coordinateGaussianTailInteriorGeTwo_of_largeExponent
            (PptFactorization.AppendixB.sphere_coordinateGaussianTailInteriorLargeExponent_of_northPole
              hCoordTailInterior)))) PptFactorization.AppendixB.sphere_hemisphereLargeRadiusTail_surface
  have hFullIso :
      PptFactorization.AppendixB.FullSphericalIsoperimetry :=
    PptFactorization.AppendixB.fullSphericalIsoperimetry_of_hemisphereComparison_and_tail
      (PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparison_of_geTwo hCompare) hTail
  exact
    upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hFullIso hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope

/-- Sharp canonical upper endpoint with the remaining north-pole tail stated
directly as a normalized closed-halfspace estimate on the concrete real
sphere.  This removes the coordinate-law formulation from the theorem-facing
frontier; the coordinate law is supplied internally by
`sphereClosedHalfspaceMeasure_coordinate_formula`. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBands_northPoleClosedHalfspaceTail_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {C : ℝ → ℝ}
    {momentAbound momentL2bound momentL1bound momentQ2bound momentQ1bound :
      ℝ → ℕ → ℝ}
    {aSlack etaSlack : ℝ → ℝ}
    {M τ : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hOneSided :
      UpperConcreteOneSidedPositiveDeviationWitness
        (p := p) (q := q) (σ := σ) eps k)
    (hLemma43AutoHeightBands :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tauSep : ℝ, 0 < eps ∧ 0 < tauSep ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                ∃ Cmodel : Set (PptFactorization.AppendixB.FinRealSphere n),
                  ∃ pole : PptFactorization.AppendixB.FinRealSphere n,
                  ∃ a tauMax : ℝ,
                    0 < tauMax ∧
                    MeasurableSet Cmodel ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real Cmodel =
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real A ∧
                    eps ≤
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (Cmodel ∆ A) ∧
                    ∀ ⦃tauBand : ℝ⦄, 0 < tauBand → tauBand ≤ tauMax →
                      ∃ avg : ℝ,
                        SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tauSep
                          (PptFactorization.AppendixB.finRealPolarizationMuMinus Cmodel A
                            (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                              n pole a tauBand))
                          (PptFactorization.AppendixB.finRealPolarizationMuPlus Cmodel A
                            (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                              n pole a tauBand))
                          avg ∧
                        avg ≤
                          sSup
                            (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                              n r A))
    (hClosedHalfspaceTail :
      PptFactorization.AppendixB.sphere_northPoleClosedHalfspaceGaussianTailLargeExponent)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (ha : ∀ slack : ℝ, 0 < slack → 0 ≤ aSlack slack)
    (hK_half :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          1 / 2 ≤
            (upperConcreteSphericalMu (p := p) (q := q) (σ := σ) d).real
              (backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k))
    (hEta : ∀ slack : ℝ, 0 < slack → 0 < etaSlack slack)
    (hMomentWordBound :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y : SampleMatrix p q σ⦄,
            Y ∈ backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k →
            frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed k d) (aSlack slack) →
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                |localWordScaledTraceTerm
                    (p := p) (q := q)
                    (upperConcreteN d)
                    (localBackground (p := p) (q := q) (σ := σ) Y)
                    (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                    (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
                    w| ≤
                  localExpansionMixedWordEnvelopeTerm
                    (upperConcreteN d)
                    (momentAbound slack d) (momentL2bound slack d)
                    (momentL1bound slack d) (momentQ2bound slack d)
                    (momentQ1bound slack d) k w)
    (hMomentTermLimit :
      ∀ slack : ℝ, 0 < slack →
        ∀ w : Fin k → LocalExpansionLetter,
          localWordIsMixed w →
            Tendsto
              (fun d =>
                localExpansionMixedWordEnvelopeTerm
                  (upperConcreteN d)
                  (momentAbound slack d) (momentL2bound slack d)
                  (momentL1bound slack d) (momentQ2bound slack d)
                  (momentQ1bound slack d) k w)
              atTop (nhds 0))
    (hBudget :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          aSlack slack ^ k + etaSlack slack + τ slack d <
            upperCanonicalTau slack d)
    (hEnvelope :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          Real.exp
              (-(((upperConcreteRealDim R d - 1) *
                  sharpSphericalRadiusSq
                    (upperConcreteN d) (spikeSpeed k d) (aSlack slack)) /
                2)) ≤
            upperConcreteMomentBoundScale C slack d) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  exact
    upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBands_northPoleCoordinateTail_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hLemma43AutoHeightBands
      (PptFactorization.AppendixB.sphere_coordinateGaussianTailInteriorLargeExponentNorthPole_of_closedHalfspaceTail
        hClosedHalfspaceTail)
      hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
      hBudget hEnvelope

/-- Sharp canonical upper endpoint with the north-pole tail stated as the
ambient cone-volume estimate.  The normalized surface closed-halfspace form is
supplied internally by the `toSphere` cone-ratio bridge. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBands_northPoleCapConeTail_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {C : ℝ → ℝ}
    {momentAbound momentL2bound momentL1bound momentQ2bound momentQ1bound :
      ℝ → ℕ → ℝ}
    {aSlack etaSlack : ℝ → ℝ}
    {M τ : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hOneSided :
      UpperConcreteOneSidedPositiveDeviationWitness
        (p := p) (q := q) (σ := σ) eps k)
    (hLemma43AutoHeightBands :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tauSep : ℝ, 0 < eps ∧ 0 < tauSep ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                ∃ Cmodel : Set (PptFactorization.AppendixB.FinRealSphere n),
                  ∃ pole : PptFactorization.AppendixB.FinRealSphere n,
                  ∃ a tauMax : ℝ,
                    0 < tauMax ∧
                    MeasurableSet Cmodel ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real Cmodel =
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real A ∧
                    eps ≤
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (Cmodel ∆ A) ∧
                    ∀ ⦃tauBand : ℝ⦄, 0 < tauBand → tauBand ≤ tauMax →
                      ∃ avg : ℝ,
                        SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tauSep
                          (PptFactorization.AppendixB.finRealPolarizationMuMinus Cmodel A
                            (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                              n pole a tauBand))
                          (PptFactorization.AppendixB.finRealPolarizationMuPlus Cmodel A
                            (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                              n pole a tauBand))
                          avg ∧
                        avg ≤
                          sSup
                            (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                              n r A))
    (hConeTail :
      PptFactorization.AppendixB.sphere_northPoleCapConeGaussianTailLargeExponent)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (ha : ∀ slack : ℝ, 0 < slack → 0 ≤ aSlack slack)
    (hK_half :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          1 / 2 ≤
            (upperConcreteSphericalMu (p := p) (q := q) (σ := σ) d).real
              (backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k))
    (hEta : ∀ slack : ℝ, 0 < slack → 0 < etaSlack slack)
    (hMomentWordBound :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y : SampleMatrix p q σ⦄,
            Y ∈ backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k →
            frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed k d) (aSlack slack) →
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                |localWordScaledTraceTerm
                    (p := p) (q := q)
                    (upperConcreteN d)
                    (localBackground (p := p) (q := q) (σ := σ) Y)
                    (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                    (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
                    w| ≤
                  localExpansionMixedWordEnvelopeTerm
                    (upperConcreteN d)
                    (momentAbound slack d) (momentL2bound slack d)
                    (momentL1bound slack d) (momentQ2bound slack d)
                    (momentQ1bound slack d) k w)
    (hMomentTermLimit :
      ∀ slack : ℝ, 0 < slack →
        ∀ w : Fin k → LocalExpansionLetter,
          localWordIsMixed w →
            Tendsto
              (fun d =>
                localExpansionMixedWordEnvelopeTerm
                  (upperConcreteN d)
                  (momentAbound slack d) (momentL2bound slack d)
                  (momentL1bound slack d)
                  (momentQ2bound slack d)
                  (momentQ1bound slack d) k w)
              atTop (nhds 0))
    (hBudget :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          aSlack slack ^ k + etaSlack slack + τ slack d <
            upperCanonicalTau slack d)
    (hEnvelope :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          Real.exp
              (-(((upperConcreteRealDim R d - 1) *
                  sharpSphericalRadiusSq
                    (upperConcreteN d) (spikeSpeed k d) (aSlack slack)) /
                2)) ≤
            upperConcreteMomentBoundScale C slack d) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  exact
    upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBands_northPoleClosedHalfspaceTail_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hLemma43AutoHeightBands
      (PptFactorization.AppendixB.sphere_northPoleClosedHalfspaceGaussianTailLargeExponent_of_coneTail
        hConeTail)
      hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
      hBudget hEnvelope

/-- Sharp canonical upper endpoint with the north-pole cap-cone tail reduced
to the algebraic `cos(r)^(n-1)` cone-volume estimate.  The exponential
large-exponent form is supplied internally by the scalar comparison
`cos r ≤ exp(-r^2 / 2)`. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBands_northPoleCapConeCosinePowerTail_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {C : ℝ → ℝ}
    {momentAbound momentL2bound momentL1bound momentQ2bound momentQ1bound :
      ℝ → ℕ → ℝ}
    {aSlack etaSlack : ℝ → ℝ}
    {M τ : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hOneSided :
      UpperConcreteOneSidedPositiveDeviationWitness
        (p := p) (q := q) (σ := σ) eps k)
    (hLemma43AutoHeightBands :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tauSep : ℝ, 0 < eps ∧ 0 < tauSep ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                ∃ Cmodel : Set (PptFactorization.AppendixB.FinRealSphere n),
                  ∃ pole : PptFactorization.AppendixB.FinRealSphere n,
                  ∃ a tauMax : ℝ,
                    0 < tauMax ∧
                    MeasurableSet Cmodel ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real Cmodel =
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real A ∧
                    eps ≤
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (Cmodel ∆ A) ∧
                    ∀ ⦃tauBand : ℝ⦄, 0 < tauBand → tauBand ≤ tauMax →
                      ∃ avg : ℝ,
                        SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tauSep
                          (PptFactorization.AppendixB.finRealPolarizationMuMinus Cmodel A
                            (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                              n pole a tauBand))
                          (PptFactorization.AppendixB.finRealPolarizationMuPlus Cmodel A
                            (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                              n pole a tauBand))
                          avg ∧
                        avg ≤
                          sSup
                            (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                              n r A))
    (hCosinePowerTail :
      PptFactorization.AppendixB.sphere_northPoleCapConeCosinePowerTail)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (ha : ∀ slack : ℝ, 0 < slack → 0 ≤ aSlack slack)
    (hK_half :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          1 / 2 ≤
            (upperConcreteSphericalMu (p := p) (q := q) (σ := σ) d).real
              (backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k))
    (hEta : ∀ slack : ℝ, 0 < slack → 0 < etaSlack slack)
    (hMomentWordBound :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y : SampleMatrix p q σ⦄,
            Y ∈ backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k →
            frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed k d) (aSlack slack) →
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                |localWordScaledTraceTerm
                    (p := p) (q := q)
                    (upperConcreteN d)
                    (localBackground (p := p) (q := q) (σ := σ) Y)
                    (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                    (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
                    w| ≤
                  localExpansionMixedWordEnvelopeTerm
                    (upperConcreteN d)
                    (momentAbound slack d) (momentL2bound slack d)
                    (momentL1bound slack d) (momentQ2bound slack d)
                    (momentQ1bound slack d) k w)
    (hMomentTermLimit :
      ∀ slack : ℝ, 0 < slack →
        ∀ w : Fin k → LocalExpansionLetter,
          localWordIsMixed w →
            Tendsto
              (fun d =>
                localExpansionMixedWordEnvelopeTerm
                  (upperConcreteN d)
                  (momentAbound slack d) (momentL2bound slack d)
                  (momentL1bound slack d)
                  (momentQ2bound slack d)
                  (momentQ1bound slack d) k w)
              atTop (nhds 0))
    (hBudget :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          aSlack slack ^ k + etaSlack slack + τ slack d <
            upperCanonicalTau slack d)
    (hEnvelope :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          Real.exp
              (-(((upperConcreteRealDim R d - 1) *
                  sharpSphericalRadiusSq
                    (upperConcreteN d) (spikeSpeed k d) (aSlack slack)) /
                2)) ≤
            upperConcreteMomentBoundScale C slack d) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  exact
    upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBands_northPoleCapConeTail_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hLemma43AutoHeightBands
      (PptFactorization.AppendixB.sphere_northPoleCapConeGaussianTailLargeExponent_of_cosinePowerTail
        hCosinePowerTail)
      hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
      hBudget hEnvelope

/-- Sharp canonical upper endpoint with the north-pole tail stated as the
standard normalized spherical-cap power law.  The surface/cone normalization
and scalar Gaussian comparison are both supplied internally. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBands_northPoleClosedHalfspaceCosinePowerTail_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {C : ℝ → ℝ}
    {momentAbound momentL2bound momentL1bound momentQ2bound momentQ1bound :
      ℝ → ℕ → ℝ}
    {aSlack etaSlack : ℝ → ℝ}
    {M τ : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hOneSided :
      UpperConcreteOneSidedPositiveDeviationWitness
        (p := p) (q := q) (σ := σ) eps k)
    (hLemma43AutoHeightBands :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tauSep : ℝ, 0 < eps ∧ 0 < tauSep ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                ∃ Cmodel : Set (PptFactorization.AppendixB.FinRealSphere n),
                  ∃ pole : PptFactorization.AppendixB.FinRealSphere n,
                  ∃ a tauMax : ℝ,
                    0 < tauMax ∧
                    MeasurableSet Cmodel ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real Cmodel =
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real A ∧
                    eps ≤
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (Cmodel ∆ A) ∧
                    ∀ ⦃tauBand : ℝ⦄, 0 < tauBand → tauBand ≤ tauMax →
                      ∃ avg : ℝ,
                        SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tauSep
                          (PptFactorization.AppendixB.finRealPolarizationMuMinus Cmodel A
                            (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                              n pole a tauBand))
                          (PptFactorization.AppendixB.finRealPolarizationMuPlus Cmodel A
                            (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                              n pole a tauBand))
                          avg ∧
                        avg ≤
                          sSup
                            (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                              n r A))
    (hSurfaceCosineTail :
      PptFactorization.AppendixB.sphere_northPoleClosedHalfspaceCosinePowerTail)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (ha : ∀ slack : ℝ, 0 < slack → 0 ≤ aSlack slack)
    (hK_half :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          1 / 2 ≤
            (upperConcreteSphericalMu (p := p) (q := q) (σ := σ) d).real
              (backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k))
    (hEta : ∀ slack : ℝ, 0 < slack → 0 < etaSlack slack)
    (hMomentWordBound :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y : SampleMatrix p q σ⦄,
            Y ∈ backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k →
            frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed k d) (aSlack slack) →
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                |localWordScaledTraceTerm
                    (p := p) (q := q)
                    (upperConcreteN d)
                    (localBackground (p := p) (q := q) (σ := σ) Y)
                    (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                    (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
                    w| ≤
                  localExpansionMixedWordEnvelopeTerm
                    (upperConcreteN d)
                    (momentAbound slack d) (momentL2bound slack d)
                    (momentL1bound slack d) (momentQ2bound slack d)
                    (momentQ1bound slack d) k w)
    (hMomentTermLimit :
      ∀ slack : ℝ, 0 < slack →
        ∀ w : Fin k → LocalExpansionLetter,
          localWordIsMixed w →
            Tendsto
              (fun d =>
                localExpansionMixedWordEnvelopeTerm
                  (upperConcreteN d)
                  (momentAbound slack d) (momentL2bound slack d)
                  (momentL1bound slack d)
                  (momentQ2bound slack d)
                  (momentQ1bound slack d) k w)
              atTop (nhds 0))
    (hBudget :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          aSlack slack ^ k + etaSlack slack + τ slack d <
            upperCanonicalTau slack d)
    (hEnvelope :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          Real.exp
              (-(((upperConcreteRealDim R d - 1) *
                  sharpSphericalRadiusSq
                    (upperConcreteN d) (spikeSpeed k d) (aSlack slack)) /
                2)) ≤
            upperConcreteMomentBoundScale C slack d) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  exact
    upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBands_northPoleCapConeCosinePowerTail_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hLemma43AutoHeightBands
      (PptFactorization.AppendixB.sphere_northPoleCapConeCosinePowerTail_of_closedHalfspaceCosinePowerTail
        hSurfaceCosineTail)
      hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
      hBudget hEnvelope

/-- The nontrivial below-half coordinate power tail supplies the full
north-pole coordinate power tail.  The complementary case is closed by the
antipodal half-tail bound. -/
theorem sphere_northPoleCoordinateCosinePowerTail_of_belowHalf
    (hTail :
      PptFactorization.AppendixB.sphere_northPoleCoordinateCosinePowerTailBelowHalf) :
    PptFactorization.AppendixB.sphere_northPoleCoordinateCosinePowerTail := by
  intro n hn r hn2 hrpos hrlt
  by_cases hcos_half :
      (1 / 2 : ℝ) ≤ Real.cos r ^ (n - 1)
  · have hrpi : r < Real.pi := by
      linarith [Real.pi_pos]
    have hsin_pos : 0 < Real.sin r :=
      Real.sin_pos_of_pos_of_lt_pi hrpos hrpi
    have hhalf :
        (PptFactorization.AppendixB.finRealSphereCoordinateLaw n
          (-(PptFactorization.AppendixB.finRealSphereNorthPole n :
            PptFactorization.AppendixB.FinRealEuclideanSpace n))).real
            (Set.Ici (Real.sin r)) ≤
          (1 / 2 : ℝ) :=
      PptFactorization.AppendixB.finRealSphere_positive_coordinate_tail_le_half
        n (PptFactorization.AppendixB.finRealSphereNorthPole n) hsin_pos
    exact hhalf.trans hcos_half
  · exact hTail n hn2 hrpos hrlt (lt_of_not_ge hcos_half)

/-- The nontrivial below-half coordinate power tail supplies the ambient
north-pole cone Gaussian tail.  This names the whole tail-side adapter chain:
below-half range completion, coordinate-to-surface push-forward, surface-to-cone
normalization, and the cosine-to-Gaussian scalar comparison. -/
theorem sphere_northPoleCapConeGaussianTailLargeExponent_of_northPoleCoordinateCosinePowerTailBelowHalf
    (hTail :
      PptFactorization.AppendixB.sphere_northPoleCoordinateCosinePowerTailBelowHalf) :
    PptFactorization.AppendixB.sphere_northPoleCapConeGaussianTailLargeExponent :=
  PptFactorization.AppendixB.sphere_northPoleCapConeGaussianTailLargeExponent_of_cosinePowerTail
    (PptFactorization.AppendixB.sphere_northPoleCapConeCosinePowerTail_of_closedHalfspaceCosinePowerTail
      (PptFactorization.AppendixB.sphere_northPoleClosedHalfspaceCosinePowerTail_of_coordinateCosinePowerTail
        (sphere_northPoleCoordinateCosinePowerTail_of_belowHalf hTail)))

/-- The normalized north-pole closed-halfspace Gaussian tail supplies the
hemisphere Gaussian tail used by the spherical isoperimetry package.

This is the surface-measure version of the final tail assembly: closed
halfspace tail to north-pole coordinate tail, arbitrary-coordinate extension,
small-radius coordinate dominance, and large-radius hemisphere coverage. -/
theorem sphere_hemisphereGaussianTail_of_northPoleClosedHalfspaceGaussianTailLargeExponent
    (hTail :
      PptFactorization.AppendixB.sphere_northPoleClosedHalfspaceGaussianTailLargeExponent) :
    PptFactorization.AppendixB.sphere_hemisphereGaussianTail :=
  PptFactorization.AppendixB.sphere_hemisphereGaussianTail_of_coordinateDominance_and_coordinateTail
    PptFactorization.AppendixB.sphere_hemisphereComplementCoordinateDominance_surface
    (PptFactorization.AppendixB.sphere_coordinateGaussianTail_of_interior
      (PptFactorization.AppendixB.sphere_coordinateGaussianTailInterior_of_geTwo
        (PptFactorization.AppendixB.sphere_coordinateGaussianTailInteriorGeTwo_of_largeExponent
          (PptFactorization.AppendixB.sphere_coordinateGaussianTailInteriorLargeExponent_of_northPole
            (PptFactorization.AppendixB.sphere_coordinateGaussianTailInteriorLargeExponentNorthPole_of_closedHalfspaceTail
              hTail))))) PptFactorization.AppendixB.sphere_hemisphereLargeRadiusTail_surface

/-- The ambient north-pole cone-Gaussian tail supplies the hemisphere Gaussian
tail used by the spherical isoperimetry package.

This names the final tail-side assembly: cone tail to north-pole coordinate
tail, arbitrary-coordinate extension, small-radius coordinate dominance, and
the large-radius hemisphere-tail package. -/
theorem sphere_hemisphereGaussianTail_of_northPoleCapConeGaussianTailLargeExponent
    (hConeTail :
      PptFactorization.AppendixB.sphere_northPoleCapConeGaussianTailLargeExponent) :
    PptFactorization.AppendixB.sphere_hemisphereGaussianTail :=
  sphere_hemisphereGaussianTail_of_northPoleClosedHalfspaceGaussianTailLargeExponent
    (PptFactorization.AppendixB.sphere_northPoleClosedHalfspaceGaussianTailLargeExponent_of_coneTail
      hConeTail)

/-- The nontrivial below-half north-pole coordinate power tail supplies the
full hemisphere Gaussian tail used by the spherical isoperimetry package.

All transport is internal here: the below-half tail is completed by antipodal
half-tail symmetry, converted to the normalized closed-halfspace cap power law,
lifted to the cone-volume power law, converted to the large-exponent Gaussian
cone tail, and finally fed through the already-closed coordinate-dominance and
large-radius hemisphere-tail adapters. -/
theorem sphere_hemisphereGaussianTail_of_northPoleCoordinateCosinePowerTailBelowHalf
    (hTail :
      PptFactorization.AppendixB.sphere_northPoleCoordinateCosinePowerTailBelowHalf) :
    PptFactorization.AppendixB.sphere_hemisphereGaussianTail := by
  have hConeTail :
      PptFactorization.AppendixB.sphere_northPoleCapConeGaussianTailLargeExponent :=
    sphere_northPoleCapConeGaussianTailLargeExponent_of_northPoleCoordinateCosinePowerTailBelowHalf
      hTail
  exact
    sphere_hemisphereGaussianTail_of_northPoleCapConeGaussianTailLargeExponent
      hConeTail

/-- Cap comparison in dimensions at least two plus the nontrivial below-half
north-pole coordinate power tail supply the full real-sphere isoperimetric
package consumed by the upper-bound pipeline. -/
theorem fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleCoordinateCosinePowerTailBelowHalf
    (hCompare :
      PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo)
    (hTail :
      PptFactorization.AppendixB.sphere_northPoleCoordinateCosinePowerTailBelowHalf) :
    PptFactorization.AppendixB.FullSphericalIsoperimetry :=
  PptFactorization.AppendixB.fullSphericalIsoperimetry_of_hemisphereComparison_and_tail
    (PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparison_of_geTwo hCompare)
    (sphere_hemisphereGaussianTail_of_northPoleCoordinateCosinePowerTailBelowHalf hTail)

/-- Cap comparison in dimensions at least two plus the surface-halfspace
below-half north-pole cap power tail supply the full real-sphere
isoperimetric package.  This is the same tail leaf as the coordinate-law
version, but in the cap-measure form suited for a cone-volume proof. -/
theorem fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleClosedHalfspaceCosinePowerTailBelowHalf
    (hCompare :
      PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo)
    (hTail :
      PptFactorization.AppendixB.sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf) :
    PptFactorization.AppendixB.FullSphericalIsoperimetry :=
  fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleCoordinateCosinePowerTailBelowHalf
    hCompare
    (PptFactorization.AppendixB.sphere_northPoleCoordinateCosinePowerTailBelowHalf_of_closedHalfspaceCosinePowerTailBelowHalf
      hTail)

/-- Cap comparison in dimensions at least two plus the below-half ambient
cap-cone power tail supply the full real-sphere isoperimetric package. -/
theorem fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleCapConeCosinePowerTailBelowHalf
    (hCompare :
      PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo)
    (hTail :
      PptFactorization.AppendixB.sphere_northPoleCapConeCosinePowerTailBelowHalf) :
    PptFactorization.AppendixB.FullSphericalIsoperimetry :=
  fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleClosedHalfspaceCosinePowerTailBelowHalf
    hCompare
    (PptFactorization.AppendixB.sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf_of_capConeCosinePowerTailBelowHalf
      hTail)

/-- Cap comparison in dimensions at least two plus the normalized north-pole
closed-halfspace Gaussian tail supply the full real-sphere isoperimetric
package.  This is the surface-measure Gaussian tail package beneath the
ambient cone-Gaussian route. -/
theorem fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleClosedHalfspaceGaussianTailLargeExponent
    (hCompare :
      PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo)
    (hTail :
      PptFactorization.AppendixB.sphere_northPoleClosedHalfspaceGaussianTailLargeExponent) :
    PptFactorization.AppendixB.FullSphericalIsoperimetry :=
  PptFactorization.AppendixB.fullSphericalIsoperimetry_of_hemisphereComparison_and_tail
    (PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparison_of_geTwo hCompare)
    (sphere_hemisphereGaussianTail_of_northPoleClosedHalfspaceGaussianTailLargeExponent
      hTail)

/-- Cap comparison in dimensions at least two plus the ambient north-pole
cone-Gaussian tail supply the full real-sphere isoperimetric package. -/
theorem fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleCapConeGaussianTailLargeExponent
    (hCompare :
      PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo)
    (hConeTail :
      PptFactorization.AppendixB.sphere_northPoleCapConeGaussianTailLargeExponent) :
    PptFactorization.AppendixB.FullSphericalIsoperimetry :=
  fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleClosedHalfspaceGaussianTailLargeExponent
    hCompare
    (PptFactorization.AppendixB.sphere_northPoleClosedHalfspaceGaussianTailLargeExponent_of_coneTail
      hConeTail)

/-- Lower-bound local-expansion endpoint with the north-pole tail stated in the
nontrivial below-half coordinate-power form.

This is the same source-explicit route as
`upper_eventual_from_concrete_sequences_of_coordinateTailGeometry_oneSidedLowerBound_localExpansionMoment_canonicalMixedWords`,
but the large-exponent cone tail is supplied internally by the checked
below-half-to-cone adapter. -/
theorem upper_eventual_from_concrete_sequences_of_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedLowerBound_localExpansionMoment_canonicalMixedWords
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {C : ℝ → ℝ}
    {lower : ℕ → ℝ}
    {aSlack etaSlack : ℝ → ℝ}
    {M τ : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hlower_pos : ∀ᶠ d in atTop, 0 < lower d)
    (hle :
      ∀ᶠ d in atTop,
        lower d ≤
          (upperConcreteSphericalMu
            (p := p) (q := q) (σ := σ) d).real
            (columnMomentUpperTailSet
              (p := p) (q := q) (σ := σ)
              (upperConcreteN d) eps
              (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k))
    (hCompare : PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo)
    (hCoordinateCosineTailBelowHalf :
      PptFactorization.AppendixB.sphere_northPoleCoordinateCosinePowerTailBelowHalf)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (ha : ∀ slack : ℝ, 0 < slack → 0 ≤ aSlack slack)
    (hK_half :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          1 / 2 ≤
            (upperConcreteSphericalMu (p := p) (q := q) (σ := σ) d).real
              (backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k))
    (hLocalMixed :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y : SampleMatrix p q σ⦄,
            Y ∈ backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k →
            frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed k d) (aSlack slack) →
            |localExpansionMixedRemainder
                (p := p) (q := q) (upperConcreteN d) k
                (localBackground (p := p) (q := q) (σ := σ) Y)
                (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))| ≤
              etaSlack slack)
    (hMomentBudget :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          aSlack slack ^ k + etaSlack slack + τ slack d <
            upperCanonicalTau slack d)
    (hEnvelope :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          Real.exp
              (-(((upperConcreteRealDim R d - 1) *
                  sharpSphericalRadiusSq
                    (upperConcreteN d) (spikeSpeed k d) (aSlack slack)) /
                2)) ≤
            upperConcreteMomentBoundScale C slack d) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_sequences_of_coordinateTailGeometry_oneSidedLowerBound_localExpansionMoment_canonicalMixedWords
    (p := p) (q := q) (σ := σ) R
    (C := C) (lower := lower)
    (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
    hk3 hε hlower_pos hle hCompare
    (sphere_northPoleCapConeGaussianTailLargeExponent_of_northPoleCoordinateCosinePowerTailBelowHalf
      hCoordinateCosineTailBelowHalf)
    hIsoRealDim hOperatorDim ha hK_half hLocalMixed hMomentBudget hEnvelope

/-- Lower-bound local-expansion endpoint with the north-pole tail stated
directly in the below-half ambient cap-cone power form.  The large-exponent
cone Gaussian tail is supplied by the checked below-half cone power adapter. -/
theorem upper_eventual_from_concrete_sequences_of_northPoleCapConeCosinePowerTailBelowHalf_oneSidedLowerBound_localExpansionMoment_canonicalMixedWords
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {C : ℝ → ℝ}
    {lower : ℕ → ℝ}
    {aSlack etaSlack : ℝ → ℝ}
    {M τ : ℝ → ℕ → ℝ}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hlower_pos : ∀ᶠ d in atTop, 0 < lower d)
    (hle :
      ∀ᶠ d in atTop,
        lower d ≤
          (upperConcreteSphericalMu
            (p := p) (q := q) (σ := σ) d).real
            (columnMomentUpperTailSet
              (p := p) (q := q) (σ := σ)
              (upperConcreteN d) eps
              (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k))
    (hCompare : PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo)
    (hCapConeCosineTailBelowHalf :
      PptFactorization.AppendixB.sphere_northPoleCapConeCosinePowerTailBelowHalf)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (ha : ∀ slack : ℝ, 0 < slack → 0 ≤ aSlack slack)
    (hK_half :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          1 / 2 ≤
            (upperConcreteSphericalMu (p := p) (q := q) (σ := σ) d).real
              (backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k))
    (hLocalMixed :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y : SampleMatrix p q σ⦄,
            Y ∈ backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k →
            frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed k d) (aSlack slack) →
            |localExpansionMixedRemainder
                (p := p) (q := q) (upperConcreteN d) k
                (localBackground (p := p) (q := q) (σ := σ) Y)
                (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))| ≤
              etaSlack slack)
    (hMomentBudget :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          aSlack slack ^ k + etaSlack slack + τ slack d <
            upperCanonicalTau slack d)
    (hEnvelope :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          Real.exp
              (-(((upperConcreteRealDim R d - 1) *
                  sharpSphericalRadiusSq
                    (upperConcreteN d) (spikeSpeed k d) (aSlack slack)) /
                2)) ≤
            upperConcreteMomentBoundScale C slack d) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_sequences_of_coordinateTailGeometry_oneSidedLowerBound_localExpansionMoment_canonicalMixedWords
    (p := p) (q := q) (σ := σ) R
    (C := C) (lower := lower)
    (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
    hk3 hε hlower_pos hle hCompare
    (PptFactorization.AppendixB.sphere_northPoleCapConeGaussianTailLargeExponent_of_cosinePowerTailBelowHalf
      hCapConeCosineTailBelowHalf)
    hIsoRealDim hOperatorDim ha hK_half hLocalMixed hMomentBudget hEnvelope

section NorthPoleCoordinateCosineTailEndpoint

variable {p q σ : Type*}
variable [Fintype p] [Fintype q] [Fintype σ]
variable [DecidableEq p] [DecidableEq q]
variable [Nonempty p] [Nonempty q] [Nonempty σ]
variable (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
variable {eps : ℝ} {k : ℕ}
variable {C : ℝ → ℝ}
variable {momentAbound momentL2bound momentL1bound momentQ2bound momentQ1bound :
  ℝ → ℕ → ℝ}
variable {aSlack etaSlack : ℝ → ℝ}
variable {M τ : ℝ → ℕ → ℝ}
variable (hk3 : 3 ≤ k) (hε : 0 < eps)
variable
  (hOneSided :
    UpperConcreteOneSidedPositiveDeviationWitness
      (p := p) (q := q) (σ := σ) eps k)
variable
  (hLemma43AutoHeightBands :
    ∀ (n : ℕ) [NeZero n], 2 ≤ n →
      ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
        ∀ ⦃η : ℝ⦄, 0 < η →
          ∃ eps tauSep : ℝ, 0 < eps ∧ 0 < tauSep ∧
            ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
              PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                  (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
              PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                    (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                      (PptFactorization.AppendixB.finRealSphereNorthPole n :
                        PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                  (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
              ∃ Cmodel : Set (PptFactorization.AppendixB.FinRealSphere n),
                ∃ pole : PptFactorization.AppendixB.FinRealSphere n,
                ∃ a tauMax : ℝ,
                  0 < tauMax ∧
                  MeasurableSet Cmodel ∧
                  (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real Cmodel =
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real A ∧
                  eps ≤
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                      (Cmodel ∆ A) ∧
                  ∀ ⦃tauBand : ℝ⦄, 0 < tauBand → tauBand ≤ tauMax →
                    ∃ avg : ℝ,
                      SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tauSep
                        (PptFactorization.AppendixB.finRealPolarizationMuMinus Cmodel A
                          (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                            n pole a tauBand))
                        (PptFactorization.AppendixB.finRealPolarizationMuPlus Cmodel A
                          (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                            n pole a tauBand))
                        avg ∧
                      avg ≤
                        sSup
                          (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                            n r A))
variable
  (hLemma43AutoHeightBandsDirectGainSup :
    ∀ (n : ℕ) [NeZero n], 2 ≤ n →
      ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
        ∀ ⦃η : ℝ⦄, 0 < η →
          ∃ eps tauSep : ℝ, 0 < eps ∧ 0 < tauSep ∧
            ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
              PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                  (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
              PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                    (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                      (PptFactorization.AppendixB.finRealSphereNorthPole n :
                        PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                  (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
              ∃ Cmodel : Set (PptFactorization.AppendixB.FinRealSphere n),
                ∃ pole : PptFactorization.AppendixB.FinRealSphere n,
                ∃ a tauMax : ℝ,
                  0 < tauMax ∧
                  MeasurableSet Cmodel ∧
                  (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real Cmodel =
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real A ∧
                  eps ≤
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                      (Cmodel ∆ A) ∧
                  ∀ ⦃tauBand : ℝ⦄, 0 < tauBand → tauBand ≤ tauMax →
                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tauSep
                      (PptFactorization.AppendixB.finRealPolarizationMuMinus Cmodel A
                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                          n pole a tauBand))
                      (PptFactorization.AppendixB.finRealPolarizationMuPlus Cmodel A
                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                          n pole a tauBand))
                      (sSup
                        (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                          n r A)))
variable
  (hCoordinateCosineTail :
    PptFactorization.AppendixB.sphere_northPoleCoordinateCosinePowerTail)
variable
  (hCoordinateCosineTailBelowHalf :
    PptFactorization.AppendixB.sphere_northPoleCoordinateCosinePowerTailBelowHalf)
variable
  (hIsoRealDim :
    ∀ᶠ d in atTop,
      upperConcreteRealDim R d =
        2 * bipartiteDimension p q * sampleDimension σ)
variable
  (hOperatorDim :
    ∀ᶠ d : ℕ in atTop,
      bipartiteDimension p q = (d : ℝ) ^ 2)
variable (ha : ∀ slack : ℝ, 0 < slack → 0 ≤ aSlack slack)
variable
  (hK_half :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        1 / 2 ≤
          (upperConcreteSphericalMu (p := p) (q := q) (σ := σ) d).real
            (backgroundTypicalSet
              (p := p) (q := q) (σ := σ)
              (upperConcreteN d) (M slack d) (τ slack d)
              (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k))
variable (hEta : ∀ slack : ℝ, 0 < slack → 0 < etaSlack slack)
variable
  (hMomentWordBound :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        ∀ ⦃X Y : SampleMatrix p q σ⦄,
          Y ∈ backgroundTypicalSet
              (p := p) (q := q) (σ := σ)
              (upperConcreteN d) (M slack d) (τ slack d)
              (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k →
          frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
            sharpSphericalRadius
              (upperConcreteN d) (spikeSpeed k d) (aSlack slack) →
          ∀ w : Fin k → LocalExpansionLetter,
            localWordIsMixed w →
              |localWordScaledTraceTerm
                  (p := p) (q := q)
                  (upperConcreteN d)
                  (localBackground (p := p) (q := q) (σ := σ) Y)
                  (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                  (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
                  w| ≤
                localExpansionMixedWordEnvelopeTerm
                  (upperConcreteN d)
                  (momentAbound slack d) (momentL2bound slack d)
                  (momentL1bound slack d) (momentQ2bound slack d)
                  (momentQ1bound slack d) k w)
variable
  (hMomentTermLimit :
    ∀ slack : ℝ, 0 < slack →
      ∀ w : Fin k → LocalExpansionLetter,
        localWordIsMixed w →
          Tendsto
            (fun d =>
              localExpansionMixedWordEnvelopeTerm
                (upperConcreteN d)
                (momentAbound slack d) (momentL2bound slack d)
                (momentL1bound slack d)
                (momentQ2bound slack d)
                (momentQ1bound slack d) k w)
            atTop (nhds 0))
variable
  (hBudget :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        aSlack slack ^ k + etaSlack slack + τ slack d <
          upperCanonicalTau slack d)
variable
  (hEnvelope :
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        Real.exp
            (-(((upperConcreteRealDim R d - 1) *
                sharpSphericalRadiusSq
                  (upperConcreteN d) (spikeSpeed k d) (aSlack slack)) /
              2)) ≤
          upperConcreteMomentBoundScale C slack d)

include hk3 hε hOneSided hLemma43AutoHeightBands hCoordinateCosineTail
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Sharp canonical upper endpoint with the north-pole tail stated directly as
the one-dimensional coordinate-law power tail.  The coordinate push-forward,
surface/cone normalization, and scalar Gaussian comparison are supplied
internally. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBands_northPoleCoordinateCosinePowerTail_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  exact
    upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBands_northPoleClosedHalfspaceCosinePowerTail_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hLemma43AutoHeightBands
      (PptFactorization.AppendixB.sphere_northPoleClosedHalfspaceCosinePowerTail_of_coordinateCosinePowerTail
        hCoordinateCosineTail)
      hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
      hBudget hEnvelope

include hLemma43AutoHeightBands hCoordinateCosineTailBelowHalf in
/-- Average-form auto-height-band Lemma 4.3 data plus the one-dimensional
below-half north-pole coordinate power tail supply the full real-sphere
isoperimetric package consumed by the sharp coordinate endpoint.

This is the theorem-facing package for the natural measure-trimming output:
the geometric data may expose an auxiliary average `avg`, with `avg ≤ sSup`,
while the coordinate tail stays in its sharp below-half form. -/
theorem fullSphericalIsoperimetry_of_lemma43AutoHeightBands_northPoleCoordinateCosinePowerTailBelowHalf :
    PptFactorization.AppendixB.FullSphericalIsoperimetry := by
  have hCompare :
      PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo :=
    PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo_of_lemma43_autoHeightBands_gainSup_equal_mass_pos_lt_pi
      hLemma43AutoHeightBands
  exact
    fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleCoordinateCosinePowerTailBelowHalf
      hCompare hCoordinateCosineTailBelowHalf

include hLemma43AutoHeightBands in
/-- Average-form auto-height-band Lemma 4.3 data plus the ambient north-pole
cone Gaussian tail supply the full real-sphere isoperimetric package.

This keeps the geometric leaf in the natural `avg ≤ sSup` form while exposing
the tail leaf in the prioritized cone-Gaussian form. -/
theorem fullSphericalIsoperimetry_of_lemma43AutoHeightBands_northPoleCapConeGaussianTailLargeExponent
    (hConeTail :
      PptFactorization.AppendixB.sphere_northPoleCapConeGaussianTailLargeExponent) :
    PptFactorization.AppendixB.FullSphericalIsoperimetry := by
  have hCompare :
      PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo :=
    PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo_of_lemma43_autoHeightBands_gainSup_equal_mass_pos_lt_pi
      hLemma43AutoHeightBands
  exact
    fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleCapConeGaussianTailLargeExponent
      hCompare hConeTail

include hk3 hε hOneSided hLemma43AutoHeightBands hCoordinateCosineTailBelowHalf
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Sharp canonical upper endpoint with the north-pole coordinate-law tail
reduced to the nontrivial below-half range.  The range where
`1 / 2 ≤ cos(r)^(n-1)` is supplied internally by antipodal symmetry. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBands_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hFullIso :
      PptFactorization.AppendixB.FullSphericalIsoperimetry :=
    fullSphericalIsoperimetry_of_lemma43AutoHeightBands_northPoleCoordinateCosinePowerTailBelowHalf
      hLemma43AutoHeightBands hCoordinateCosineTailBelowHalf
  exact
    upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hFullIso hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope

include hk3 hε hOneSided hLemma43AutoHeightBands
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Sharp canonical upper endpoint with the tail leaf stated in the prioritized
ambient north-pole cone-Gaussian form.

The cap-comparison leaf is supplied internally from the natural average-form
auto-height Lemma 4.3 data. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBands_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hConeTail :
      PptFactorization.AppendixB.sphere_northPoleCapConeGaussianTailLargeExponent) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hFullIso :
      PptFactorization.AppendixB.FullSphericalIsoperimetry :=
    fullSphericalIsoperimetry_of_lemma43AutoHeightBands_northPoleCapConeGaussianTailLargeExponent
      hLemma43AutoHeightBands hConeTail
  exact
    upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hFullIso hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope

variable
  (hCompare :
    PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo)
variable
  (hClosedHalfspaceCosineTailBelowHalf :
    PptFactorization.AppendixB.sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf)

include hLemma43AutoHeightBandsDirectGainSup hCoordinateCosineTailBelowHalf in
/-- Direct auto-height-band block-to-`sSup` Lemma 4.3 data plus the
one-dimensional below-half north-pole coordinate power tail supply the full
real-sphere isoperimetric package consumed by the sharp coordinate endpoint. -/
theorem fullSphericalIsoperimetry_of_lemma43AutoHeightBandsDirectGainSup_northPoleCoordinateCosinePowerTailBelowHalf :
    PptFactorization.AppendixB.FullSphericalIsoperimetry := by
  have hCompare :
      PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo :=
    PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo_of_lemma43_autoHeightBands_directGainSup_equal_mass_pos_lt_pi
      hLemma43AutoHeightBandsDirectGainSup
  exact
    fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleCoordinateCosinePowerTailBelowHalf
      hCompare hCoordinateCosineTailBelowHalf

include hLemma43AutoHeightBandsDirectGainSup hClosedHalfspaceCosineTailBelowHalf in
/-- Direct auto-height-band block-to-`sSup` Lemma 4.3 data plus the normalized
below-half north-pole cap power tail supply the full real-sphere isoperimetric
package consumed by the upper-bound pipeline.

This is the reusable package form of the sharp endpoint's geometric assembly:
direct Lemma 4.3 data gives cap comparison, while the below-half tail gives the
Gaussian hemisphere tail through the existing north-pole adapters. -/
theorem fullSphericalIsoperimetry_of_lemma43AutoHeightBandsDirectGainSup_northPoleClosedHalfspaceCosinePowerTailBelowHalf :
    PptFactorization.AppendixB.FullSphericalIsoperimetry := by
  have hCompare :
      PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo :=
    PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo_of_lemma43_autoHeightBands_directGainSup_equal_mass_pos_lt_pi
      hLemma43AutoHeightBandsDirectGainSup
  exact
    fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleClosedHalfspaceCosinePowerTailBelowHalf
      hCompare hClosedHalfspaceCosineTailBelowHalf

include hLemma43AutoHeightBandsDirectGainSup in
/-- Direct auto-height-band block-to-`sSup` Lemma 4.3 data plus the normalized
north-pole closed-halfspace Gaussian tail supply the full real-sphere
isoperimetric package.

This is the surface-Gaussian analogue of the prioritized cone-Gaussian package:
direct Lemma 4.3 data gives cap comparison, and the normalized surface Gaussian
tail supplies the hemisphere Gaussian tail. -/
theorem fullSphericalIsoperimetry_of_lemma43AutoHeightBandsDirectGainSup_northPoleClosedHalfspaceGaussianTailLargeExponent
    (hTail :
      PptFactorization.AppendixB.sphere_northPoleClosedHalfspaceGaussianTailLargeExponent) :
    PptFactorization.AppendixB.FullSphericalIsoperimetry := by
  have hCompare :
      PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo :=
    PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo_of_lemma43_autoHeightBands_directGainSup_equal_mass_pos_lt_pi
      hLemma43AutoHeightBandsDirectGainSup
  exact
    fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleClosedHalfspaceGaussianTailLargeExponent
      hCompare hTail

include hLemma43AutoHeightBandsDirectGainSup in
/-- Direct auto-height-band block-to-`sSup` Lemma 4.3 data plus the
north-pole one-dimensional coordinate Gaussian tail supply the full
real-sphere isoperimetric package. -/
theorem fullSphericalIsoperimetry_of_lemma43AutoHeightBandsDirectGainSup_northPoleCoordinateGaussianTailLargeExponent
    (hTail :
      PptFactorization.AppendixB.sphere_coordinateGaussianTailInteriorLargeExponentNorthPole) :
    PptFactorization.AppendixB.FullSphericalIsoperimetry := by
  exact
    fullSphericalIsoperimetry_of_lemma43AutoHeightBandsDirectGainSup_northPoleClosedHalfspaceGaussianTailLargeExponent
      hLemma43AutoHeightBandsDirectGainSup
      (PptFactorization.AppendixB.sphere_northPoleClosedHalfspaceGaussianTailLargeExponent_of_coneTail
        (PptFactorization.AppendixB.sphere_northPoleCapConeGaussianTailLargeExponent_of_coordinateTail
          hTail))

include hLemma43AutoHeightBandsDirectGainSup in
/-- Direct auto-height-band block-to-`sSup` Lemma 4.3 data plus the ambient
north-pole cone Gaussian tail supply the full real-sphere isoperimetric
package used by the cone-Gaussian upper-bound branch. -/
theorem fullSphericalIsoperimetry_of_lemma43AutoHeightBandsDirectGainSup_northPoleCapConeGaussianTailLargeExponent
    (hConeTail :
      PptFactorization.AppendixB.sphere_northPoleCapConeGaussianTailLargeExponent) :
    PptFactorization.AppendixB.FullSphericalIsoperimetry := by
  exact
    fullSphericalIsoperimetry_of_lemma43AutoHeightBandsDirectGainSup_northPoleCoordinateGaussianTailLargeExponent
      hLemma43AutoHeightBandsDirectGainSup
      (PptFactorization.AppendixB.sphere_coordinateGaussianTailInteriorLargeExponentNorthPole_of_coneTail
        hConeTail)

include hLemma43AutoHeightBandsDirectGainSup in
/-- Direct auto-height-band block-to-`sSup` Lemma 4.3 data plus the explicit
cap-flattening-map tail supply the full real-sphere isoperimetric package.

This is the no-extra-tail-input geometric assembly used by the cap-cone upper
branch: the ambient cap-cone power tail is discharged by the explicit
flattening map, then converted to the large-exponent Gaussian tail. -/
theorem fullSphericalIsoperimetry_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap :
    PptFactorization.AppendixB.FullSphericalIsoperimetry := by
  exact
    fullSphericalIsoperimetry_of_lemma43AutoHeightBandsDirectGainSup_northPoleCapConeGaussianTailLargeExponent
      hLemma43AutoHeightBandsDirectGainSup
      (PptFactorization.AppendixB.sphere_northPoleCapConeGaussianTailLargeExponent_of_cosinePowerTailBelowHalf
        PptFactorization.AppendixB.sphere_northPoleCapConeCosinePowerTailBelowHalf_from_capConeFlatteningMap)

include hk3 hε hLemma43AutoHeightBandsDirectGainSup in
/-- Actual varying-model upper endpoint with the cap-tail and full-sphere
geometry routed through the explicit cap-flattening-map package.

This is the paper-shaped actual-model route: it has no fixed-type dimension
guards and no theorem-facing typical-set half-mass hypothesis.  The remaining
inputs are target-event positivity, direct Lemma 4.3 polarization data, the
model-specific exponential moment deviation estimate, and the deterministic
mixed-remainder estimate. -/
theorem upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_oneSidedPositive_exponentialDeviationSetBound_mixedRemainder
    (hModelOneSided :
      UpperConcreteModelOneSidedPositiveDeviationWitness R eps k)
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    (hMixed : UpperConcreteModelMixedRemainderBound R eps k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hFullIso : PptFactorization.AppendixB.FullSphericalIsoperimetry :=
    fullSphericalIsoperimetry_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap
      hLemma43AutoHeightBandsDirectGainSup
  exact
    upper_eventual_from_concrete_model_of_fullIso_oneSidedPositive_exponentialDeviationSetBound_mixedRemainder
      R hk3 hε hModelOneSided hFullIso hExp hMixed

include hk3 hε hLemma43AutoHeightBandsDirectGainSup in
/-- Actual varying-model upper endpoint with one-sided positivity exposed as an
eventually positive lower bound for the actual one-sided event.

This is a sharper frontier than
`upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_oneSidedPositive_exponentialDeviationSetBound_mixedRemainder`:
the theorem-facing positivity input is no longer the opaque proposition
`UpperConcreteModelOneSidedPositiveDeviationWitness`, but the concrete pair
`0 < lower d` and
`lower d <= upperConcreteModelOneSidedProb R eps k d` eventually. -/
theorem upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_oneSidedLowerBound_exponentialDeviationSetBound_mixedRemainder
    {lower : ℕ → ℝ}
    (hlower_pos : ∀ᶠ d in atTop, 0 < lower d)
    (hle :
      ∀ᶠ d in atTop,
        lower d ≤ upperConcreteModelOneSidedProb R eps k d)
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    (hMixed : UpperConcreteModelMixedRemainderBound R eps k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hModelOneSided :
      UpperConcreteModelOneSidedPositiveDeviationWitness R eps k :=
    upperConcreteModelOneSidedPositiveDeviationWitness_of_eventually_positive_lower_bound
      R (eps := eps) (k := k) (lower := lower) hlower_pos hle
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_oneSidedPositive_exponentialDeviationSetBound_mixedRemainder
      R hk3 hε hLemma43AutoHeightBandsDirectGainSup hModelOneSided hExp hMixed

include hk3 hε hLemma43AutoHeightBandsDirectGainSup in
/-- Actual varying-model upper endpoint with one-sided positivity routed through
the concrete lower-closure target probability.

The lower-bound side already names the actual one-sided upper-tail mass as
`lowerConcreteTargetProb R (fun _ => eps) (upperConcreteModelMeanSeq R k) k`.
This wrapper uses the definitional bridge to the upper endpoint's
`upperConcreteModelOneSidedProb`, so the visible positivity frontier is now the
same probability family used by the one-column lower pipeline. -/
theorem upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerConcreteTargetLowerBound_exponentialDeviationSetBound_mixedRemainder
    {lower : ℕ → ℝ}
    (hlower_pos : ∀ᶠ d in atTop, 0 < lower d)
    (hleLowerTarget :
      ∀ᶠ d in atTop,
        lower d ≤
          lowerConcreteTargetProb R (fun _d : ℕ => eps)
            (upperConcreteModelMeanSeq R k) k d)
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    (hMixed : UpperConcreteModelMixedRemainderBound R eps k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hleOneSided :
      ∀ᶠ d in atTop,
        lower d ≤ upperConcreteModelOneSidedProb R eps k d :=
    upperConcreteModelOneSidedProb_lowerBound_of_lowerConcreteTargetProb
      R (eps := eps) (k := k) (lower := lower) hleLowerTarget
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_oneSidedLowerBound_exponentialDeviationSetBound_mixedRemainder
      R hk3 hε hLemma43AutoHeightBandsDirectGainSup hlower_pos hleOneSided
      hExp hMixed

include hk3 hε hLemma43AutoHeightBandsDirectGainSup in
/-- Actual varying-model upper endpoint with one-sided positivity supplied by
the explicit one-column favourable event from the lower pipeline.

The lower-bound side is now the concrete probability
`lowerConcreteColumnProb`, whose product identity splits it into the beta
interval, projective cap, and deleted-background factors.  Positivity is
therefore derived from the beta lower-bound package, the cap lower-bound
package, and a half-mass lower bound for the deleted background. -/
theorem upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerConcreteColumnProb_exponentialDeviationSetBound_mixedRemainder
    (e : (x : ℝ × ℝ × ℕ) →
      EuclideanSpace ℂ (BipIndex (Fin x.2.2) (Fin x.2.2)))
    {M τ center : ℝ → ℝ → ℕ → ℝ}
    {a slack : ℝ}
    (ha : spikeRoot k eps < a) (hslack : 0 < slack)
    (hColumnIncluded :
      ∀ᶠ d in atTop,
        lowerConcreteColumnProb R e M τ center k a slack d ≤
          lowerConcreteTargetProb R (fun _d : ℕ => eps)
            (upperConcreteModelMeanSeq R k) k d)
    (hCap :
      ∀ᶠ d in atTop,
        ProjectiveCapProbabilityLowerBound
          (lowerConcreteCapProb R e a slack d) (lowerConcreteNcap d)
          (1 / (lowerConcreteNcap d : ℝ)))
    (hBackgroundHalf :
      ∀ᶠ d in atTop,
        (1 / 2 : ℝ) ≤ lowerConcreteBackgroundProb R M τ center k a slack d)
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    (hMixed : UpperConcreteModelMixedRemainderBound R eps k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hk1 : 1 < k := lt_of_lt_of_le (by norm_num : 1 < 3) hk3
  have hProduct :
      ∀ᶠ d in atTop,
        lowerConcreteColumnProb R e M τ center k a slack d =
          lowerConcreteBetaProb R k a slack d *
            lowerConcreteCapProb R e a slack d *
              lowerConcreteBackgroundProb R M τ center k a slack d :=
    lower_concrete_hProduct R e M τ center (k := k)
      (root := spikeRoot k eps) a ha slack hslack
  have hBeta :
      ∀ᶠ d in atTop,
        BetaColumnIntervalLowerBound
          (lowerConcreteBetaProb R k a slack d)
          (lowerConcreteN d) (lowerConcreteS R d)
          (betaColumnSpikeScale
            (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
          (lowerConcreteDelta a slack d) :=
    lower_concrete_hBeta R (k := k) hk1 (ε := eps) hε a ha slack hslack
  have hlower_pos :
      ∀ᶠ d in atTop,
        0 < lowerConcreteColumnProb R e M τ center k a slack d := by
    filter_upwards [hProduct, hBeta, hCap, hBackgroundHalf] with d hp hb hc hbg
    rw [hp]
    have hBackground_pos :
        0 < lowerConcreteBackgroundProb R M τ center k a slack d := by
      linarith
    exact mul_pos (mul_pos hb.prob_pos hc.prob_pos) hBackground_pos
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerConcreteTargetLowerBound_exponentialDeviationSetBound_mixedRemainder
      R hk3 hε hLemma43AutoHeightBandsDirectGainSup
      (lower := lowerConcreteColumnProb R e M τ center k a slack)
      hlower_pos hColumnIncluded hExp hMixed

include hk3 hε hOneSided hClosedHalfspaceCosineTailBelowHalf
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Sharp canonical upper endpoint with cap comparison reduced to the direct
uniform polarization gain-supremum theorem.  This is the theorem-strength
frontier just before the maximizing-sequence contradiction: every competitor
above the north-pole hemisphere by a fixed gap has a uniformly positive
polarization gain. -/
theorem upper_eventual_from_concrete_sequences_of_uniformPolarizationGainSup_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hUniformGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ δ : ℝ, 0 < δ ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                δ ≤
                  sSup
                    (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                      n r A)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hCompare :
      PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo :=
    PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo_of_uniform_polarization_gainSup_lower_pos_lt_pi
      hUniformGainSup
  have hFullIso :
      PptFactorization.AppendixB.FullSphericalIsoperimetry :=
    fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleClosedHalfspaceCosinePowerTailBelowHalf
      hCompare hClosedHalfspaceCosineTailBelowHalf
  exact
    upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hFullIso hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope

include hk3 hε hOneSided hCoordinateCosineTailBelowHalf
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Uniform polarization gain-supremum endpoint with the cap-tail leaf stated
directly in the one-dimensional below-half coordinate-law form. -/
theorem upper_eventual_from_concrete_sequences_of_uniformPolarizationGainSup_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hUniformGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ δ : ℝ, 0 < δ ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                δ ≤
                  sSup
                    (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                      n r A)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hCompare :
      PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo :=
    PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo_of_uniform_polarization_gainSup_lower_pos_lt_pi
      hUniformGainSup
  have hFullIso :
      PptFactorization.AppendixB.FullSphericalIsoperimetry :=
    fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleCoordinateCosinePowerTailBelowHalf
      hCompare hCoordinateCosineTailBelowHalf
  exact
    upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hFullIso hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope

include hk3 hε hOneSided
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Uniform polarization gain-supremum endpoint with the cap-tail leaf stated
directly in the below-half ambient cap-cone power form. -/
theorem upper_eventual_from_concrete_sequences_of_uniformPolarizationGainSup_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hCapConeCosineTailBelowHalf :
      PptFactorization.AppendixB.sphere_northPoleCapConeCosinePowerTailBelowHalf)
    (hUniformGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ δ : ℝ, 0 < δ ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                δ ≤
                  sSup
                    (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                      n r A)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hCompare :
      PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo :=
    PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo_of_uniform_polarization_gainSup_lower_pos_lt_pi
      hUniformGainSup
  have hFullIso :
      PptFactorization.AppendixB.FullSphericalIsoperimetry :=
    fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleCapConeCosinePowerTailBelowHalf
      hCompare hCapConeCosineTailBelowHalf
  exact
    upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hFullIso hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope

include hk3 hε hOneSided hClosedHalfspaceCosineTailBelowHalf
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Uniform polarization-improvement endpoint with the cap-tail leaf stated
directly in the normalized below-half closed-halfspace form.

This is the surface-tail analogue of the strict cap-cone proof-core route:
the actual polarization-improvement theorem supplies cap comparison, while
the normalized surface tail supplies the full isoperimetric package. -/
theorem upper_eventual_from_concrete_sequences_of_uniformPolarizationGap_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hUniformGap :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ δ : ℝ, 0 < δ ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                ∃ v : PptFactorization.AppendixB.FinRealSphere n,
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A + δ ≤
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSpherePolarization
                        (PptFactorization.AppendixB.finRealSphereReflectionMap n) v A)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hCompare :
      PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo :=
    PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo_of_uniform_polarization_gap_improvement_pos_lt_pi
      hUniformGap
  have hFullIso :
      PptFactorization.AppendixB.FullSphericalIsoperimetry :=
    fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleClosedHalfspaceCosinePowerTailBelowHalf
      hCompare hClosedHalfspaceCosineTailBelowHalf
  exact
    upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hFullIso hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope

include hk3 hε hOneSided
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Uniform polarization-improvement endpoint with the cap-tail leaf stated
directly in the below-half ambient cap-cone power form.

This is the proof-core route before translating improvements into
gain-supremum language: every above-hemisphere competitor is improved by an
actual polarization direction with a uniform positive gain. -/
theorem upper_eventual_from_concrete_sequences_of_uniformPolarizationGap_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hCapConeCosineTailBelowHalf :
      PptFactorization.AppendixB.sphere_northPoleCapConeCosinePowerTailBelowHalf)
    (hUniformGap :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ δ : ℝ, 0 < δ ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                ∃ v : PptFactorization.AppendixB.FinRealSphere n,
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A + δ ≤
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSpherePolarization
                        (PptFactorization.AppendixB.finRealSphereReflectionMap n) v A)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hCompare :
      PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo :=
    PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo_of_uniform_polarization_gap_improvement_pos_lt_pi
      hUniformGap
  have hFullIso :
      PptFactorization.AppendixB.FullSphericalIsoperimetry :=
    fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleCapConeCosinePowerTailBelowHalf
      hCompare hCapConeCosineTailBelowHalf
  exact
    upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hFullIso hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope

include hk3 hε hOneSided hLemma43AutoHeightBands hCoordinateCosineTailBelowHalf
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Sharp canonical upper endpoint with auto-height-band Lemma 4.3 data routed
through the direct uniform gain-supremum supplier.  This keeps the
theorem-facing frontier at the auto-height geometric data plus the below-half
coordinate-law tail, while avoiding the older cap-comparison detour. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsUniformGain_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hUniformGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ δ : ℝ, 0 < δ ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                δ ≤
                  sSup
                    (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                      n r A) :=
    PptFactorization.AppendixB.uniform_polarization_gainSup_lower_of_lemma43_autoHeightBands_gainSup_equal_mass_pos_lt_pi
      hLemma43AutoHeightBands
  exact
    upper_eventual_from_concrete_sequences_of_uniformPolarizationGainSup_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hCoordinateCosineTailBelowHalf hIsoRealDim hOperatorDim
      ha hK_half hEta hMomentWordBound hMomentTermLimit hBudget hEnvelope
      hUniformGainSup

include hk3 hε hOneSided hLemma43AutoHeightBands hClosedHalfspaceCosineTailBelowHalf
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Auto-height-band uniform-gain endpoint with the remaining tail stated
directly in the normalized below-half closed-halfspace form. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsUniformGain_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hUniformGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ δ : ℝ, 0 < δ ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                δ ≤
                  sSup
                    (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                      n r A) :=
    PptFactorization.AppendixB.uniform_polarization_gainSup_lower_of_lemma43_autoHeightBands_gainSup_equal_mass_pos_lt_pi
      hLemma43AutoHeightBands
  exact
    upper_eventual_from_concrete_sequences_of_uniformPolarizationGainSup_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope
      hClosedHalfspaceCosineTailBelowHalf hUniformGainSup

include hk3 hε hOneSided hLemma43AutoHeightBands
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Auto-height-band uniform-gain endpoint with the remaining tail stated
directly in the below-half ambient cap-cone form. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsUniformGain_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hCapConeCosineTailBelowHalf :
      PptFactorization.AppendixB.sphere_northPoleCapConeCosinePowerTailBelowHalf) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hUniformGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ δ : ℝ, 0 < δ ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                δ ≤
                  sSup
                    (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                      n r A) :=
    PptFactorization.AppendixB.uniform_polarization_gainSup_lower_of_lemma43_autoHeightBands_gainSup_equal_mass_pos_lt_pi
      hLemma43AutoHeightBands
  exact
    upper_eventual_from_concrete_sequences_of_uniformPolarizationGainSup_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope
      hCapConeCosineTailBelowHalf hUniformGainSup

include hk3 hε hOneSided hLemma43AutoHeightBandsDirectGainSup
  hCoordinateCosineTailBelowHalf hIsoRealDim hOperatorDim ha hK_half hEta
  hMomentWordBound hMomentTermLimit hBudget hEnvelope in
/-- Sharp canonical upper endpoint with auto-height-band Lemma 4.3 data stated
directly as a rectangular block lower bound against the supremum of polarization
objective gains.  Compared with the `avg`-witness route, this is the tighter
frontier for the geometric supplier: the remaining block estimate targets
`sSup` itself. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hFullIso :
      PptFactorization.AppendixB.FullSphericalIsoperimetry :=
    fullSphericalIsoperimetry_of_lemma43AutoHeightBandsDirectGainSup_northPoleCoordinateCosinePowerTailBelowHalf
      hLemma43AutoHeightBandsDirectGainSup hCoordinateCosineTailBelowHalf
  exact
    upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hFullIso hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope

include hk3 hε hOneSided hLemma43AutoHeightBandsDirectGainSup
  hClosedHalfspaceCosineTailBelowHalf hIsoRealDim hOperatorDim ha hK_half hEta
  hMomentWordBound hMomentTermLimit hBudget hEnvelope in
/-- Sharp direct-gain-supremum endpoint with the remaining north-pole tail in
the normalized closed-halfspace below-half form.  This is the cap-measure
version of the active direct block-to-`sSup` branch, so the coordinate
push-forward is internal to the full-isoperimetry adapter. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hFullIso :
      PptFactorization.AppendixB.FullSphericalIsoperimetry :=
    fullSphericalIsoperimetry_of_lemma43AutoHeightBandsDirectGainSup_northPoleClosedHalfspaceCosinePowerTailBelowHalf
      hLemma43AutoHeightBandsDirectGainSup hClosedHalfspaceCosineTailBelowHalf
  exact
    upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hFullIso hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope

include hk3 hε hOneSided hLemma43AutoHeightBandsDirectGainSup
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Full normalized surface-cap form of the sharp direct-gain-supremum
endpoint.  The full cap power law is restricted internally to the active
below-half surface-cap range. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleClosedHalfspaceCosinePowerTail_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hSurfaceCosineTail :
      PptFactorization.AppendixB.sphere_northPoleClosedHalfspaceCosinePowerTail) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  exact
    upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hLemma43AutoHeightBandsDirectGainSup hIsoRealDim
      hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit hBudget
      hEnvelope
      (PptFactorization.AppendixB.sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf_of_closedHalfspaceCosinePowerTail
        hSurfaceCosineTail)

include hk3 hε hOneSided hLemma43AutoHeightBandsDirectGainSup
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Cone-volume form of the sharp direct-gain-supremum endpoint.  The ambient
cap-cone cosine power law is converted to the active normalized surface-cap
below-half tail by the checked cone/surface normalization adapter. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleCapConeCosinePowerTail_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hCapConeCosineTail :
      PptFactorization.AppendixB.sphere_northPoleCapConeCosinePowerTail) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  exact
    upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hLemma43AutoHeightBandsDirectGainSup hIsoRealDim
      hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit hBudget
      hEnvelope
      (PptFactorization.AppendixB.sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf_of_capConeCosinePowerTail
        hCapConeCosineTail)

include hk3 hε hOneSided hLemma43AutoHeightBandsDirectGainSup
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Below-half cone-volume form of the sharp direct-gain-supremum endpoint.
This is the tightest current cone-tail wrapper: it asks only for the nontrivial
`cos(r)^(n-1) < 1/2` range that the active normalized surface-cap endpoint
uses. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hCapConeCosineTailBelowHalf :
      PptFactorization.AppendixB.sphere_northPoleCapConeCosinePowerTailBelowHalf) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  exact
    upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hLemma43AutoHeightBandsDirectGainSup hIsoRealDim
      hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit hBudget
      hEnvelope
      (PptFactorization.AppendixB.sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf_of_capConeCosinePowerTailBelowHalf
        hCapConeCosineTailBelowHalf)

include hk3 hε hOneSided hLemma43AutoHeightBandsDirectGainSup
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Normalized surface-Gaussian form of the sharp direct-gain-supremum
endpoint.  This is the surface-tail analogue of the cone-Gaussian wrapper:
cap comparison is supplied by the direct block-to-`sSup` Lemma 4.3 data, and
the hemisphere Gaussian tail is assembled from the normalized north-pole
closed-halfspace Gaussian tail. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleClosedHalfspaceGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hSurfaceTail :
      PptFactorization.AppendixB.sphere_northPoleClosedHalfspaceGaussianTailLargeExponent) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hFullIso :
      PptFactorization.AppendixB.FullSphericalIsoperimetry :=
    fullSphericalIsoperimetry_of_lemma43AutoHeightBandsDirectGainSup_northPoleClosedHalfspaceGaussianTailLargeExponent
      hLemma43AutoHeightBandsDirectGainSup hSurfaceTail
  exact
    upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hFullIso hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope

include hk3 hε hOneSided hLemma43AutoHeightBandsDirectGainSup
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- North-pole coordinate-Gaussian form of the sharp direct-gain-supremum
endpoint.  This exposes the remaining tail as the one-dimensional coordinate
law; cone/surface transport is internal. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleCoordinateGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hCoordinateTail :
      PptFactorization.AppendixB.sphere_coordinateGaussianTailInteriorLargeExponentNorthPole) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hFullIso :
      PptFactorization.AppendixB.FullSphericalIsoperimetry :=
    fullSphericalIsoperimetry_of_lemma43AutoHeightBandsDirectGainSup_northPoleCoordinateGaussianTailLargeExponent
      hLemma43AutoHeightBandsDirectGainSup hCoordinateTail
  exact
    upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hFullIso hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope

include hk3 hε hOneSided hLemma43AutoHeightBandsDirectGainSup
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Cone-Gaussian form of the sharp direct-gain-supremum endpoint.  This is the
post-cap-comparison tail frontier: cap comparison is supplied by the direct
block-to-`sSup` Lemma 4.3 data, and the hemisphere Gaussian tail is assembled
from the ambient north-pole cone Gaussian tail. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hConeTail :
      PptFactorization.AppendixB.sphere_northPoleCapConeGaussianTailLargeExponent) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  exact
    upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectGainSup_northPoleCoordinateGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hLemma43AutoHeightBandsDirectGainSup hIsoRealDim
      hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit hBudget
      hEnvelope
      (PptFactorization.AppendixB.sphere_coordinateGaussianTailInteriorLargeExponentNorthPole_of_coneTail
        hConeTail)

include hk3 hε hOneSided hClosedHalfspaceCosineTailBelowHalf
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Sharp canonical upper endpoint with the cap-comparison leaf supplied by
same-mass fixed-band Lemma 4.3 data, routed through the direct uniform
gain-supremum theorem. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43FixedBandsEqualMass_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hLemma43FixedBandsEqualMass :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tau : ℝ, 0 < eps ∧ 0 < tau ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                ∃ Cmodel bandPlus bandMinus :
                    Set (PptFactorization.AppendixB.FinRealSphere n),
                  ∃ avg : ℝ,
                    MeasurableSet Cmodel ∧
                    MeasurableSet bandPlus ∧
                    MeasurableSet bandMinus ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        Cmodel =
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        A ∧
                    eps ≤
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (Cmodel ∆ A) ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        bandPlus ≤ eps / 4 ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        bandMinus ≤ eps / 4 ∧
                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tau
                      (PptFactorization.AppendixB.finRealPolarizationMuMinus
                        Cmodel A bandMinus)
                      (PptFactorization.AppendixB.finRealPolarizationMuPlus
                        Cmodel A bandPlus)
                      avg ∧
                    avg ≤
                      sSup
                        (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                          n r A)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hUniformGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ δ : ℝ, 0 < δ ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                δ ≤
                  sSup
                    (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                      n r A) :=
    PptFactorization.AppendixB.uniform_polarization_gainSup_lower_of_lemma43_measure_trimming_gainSup_equal_mass_pos_lt_pi
      hLemma43FixedBandsEqualMass
  have hCompare :
      PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo :=
    PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo_of_uniform_polarization_gainSup_lower_pos_lt_pi
      hUniformGainSup
  have hFullIso :
      PptFactorization.AppendixB.FullSphericalIsoperimetry :=
    fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleClosedHalfspaceCosinePowerTailBelowHalf
      hCompare hClosedHalfspaceCosineTailBelowHalf
  exact
    upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hFullIso hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope

include hk3 hε hOneSided hCoordinateCosineTailBelowHalf
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Same-mass fixed-band Lemma 4.3 endpoint with the cap-tail leaf stated
directly in the one-dimensional below-half coordinate-law form.  This is the
fixed-band analogue of the direct uniform-gain coordinate endpoint. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43FixedBandsEqualMass_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hLemma43FixedBandsEqualMass :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tau : ℝ, 0 < eps ∧ 0 < tau ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                ∃ Cmodel bandPlus bandMinus :
                    Set (PptFactorization.AppendixB.FinRealSphere n),
                  ∃ avg : ℝ,
                    MeasurableSet Cmodel ∧
                    MeasurableSet bandPlus ∧
                    MeasurableSet bandMinus ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        Cmodel =
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        A ∧
                    eps ≤
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (Cmodel ∆ A) ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        bandPlus ≤ eps / 4 ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        bandMinus ≤ eps / 4 ∧
                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tau
                      (PptFactorization.AppendixB.finRealPolarizationMuMinus
                        Cmodel A bandMinus)
                      (PptFactorization.AppendixB.finRealPolarizationMuPlus
                        Cmodel A bandPlus)
                      avg ∧
                    avg ≤
                      sSup
                        (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                          n r A)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hUniformGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ δ : ℝ, 0 < δ ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                δ ≤
                  sSup
                    (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                      n r A) :=
    PptFactorization.AppendixB.uniform_polarization_gainSup_lower_of_lemma43_measure_trimming_gainSup_equal_mass_pos_lt_pi
      hLemma43FixedBandsEqualMass
  exact
    upper_eventual_from_concrete_sequences_of_uniformPolarizationGainSup_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hCoordinateCosineTailBelowHalf
      hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
      hBudget hEnvelope hUniformGainSup

include hk3 hε hOneSided
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Same-mass fixed-band Lemma 4.3 endpoint with the cap-tail leaf stated
directly in the below-half ambient cap-cone form. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43FixedBandsEqualMass_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hCapConeCosineTailBelowHalf :
      PptFactorization.AppendixB.sphere_northPoleCapConeCosinePowerTailBelowHalf)
    (hLemma43FixedBandsEqualMass :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tau : ℝ, 0 < eps ∧ 0 < tau ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                ∃ Cmodel bandPlus bandMinus :
                    Set (PptFactorization.AppendixB.FinRealSphere n),
                  ∃ avg : ℝ,
                    MeasurableSet Cmodel ∧
                    MeasurableSet bandPlus ∧
                    MeasurableSet bandMinus ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        Cmodel =
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        A ∧
                    eps ≤
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (Cmodel ∆ A) ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        bandPlus ≤ eps / 4 ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        bandMinus ≤ eps / 4 ∧
                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tau
                      (PptFactorization.AppendixB.finRealPolarizationMuMinus
                        Cmodel A bandMinus)
                      (PptFactorization.AppendixB.finRealPolarizationMuPlus
                        Cmodel A bandPlus)
                      avg ∧
                    avg ≤
                      sSup
                        (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                          n r A)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hUniformGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ δ : ℝ, 0 < δ ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                δ ≤
                  sSup
                    (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                      n r A) :=
    PptFactorization.AppendixB.uniform_polarization_gainSup_lower_of_lemma43_measure_trimming_gainSup_equal_mass_pos_lt_pi
      hLemma43FixedBandsEqualMass
  exact
    upper_eventual_from_concrete_sequences_of_uniformPolarizationGainSup_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope
      hCapConeCosineTailBelowHalf hUniformGainSup

include hk3 hε hOneSided hClosedHalfspaceCosineTailBelowHalf
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Sharp canonical upper endpoint with cap comparison supplied by same-mass
height-band Lemma 4.3 data whose band thickness and rectangular separation are
independent.  This is the concrete separate-scale version of the fixed-band
uniform-gain route. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43SeparateTau_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hLemma43SeparateTau :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tauBand tauSep : ℝ, 0 < eps ∧ 0 < tauSep ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                ∃ Cmodel : Set (PptFactorization.AppendixB.FinRealSphere n),
                  ∃ pole : PptFactorization.AppendixB.FinRealSphere n,
                  ∃ a avg : ℝ,
                    MeasurableSet Cmodel ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        Cmodel =
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        A ∧
                    eps ≤
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (Cmodel ∆ A) ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                          n pole a tauBand) ≤ eps / 4 ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                          n pole a tauBand) ≤ eps / 4 ∧
                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tauSep
                      (PptFactorization.AppendixB.finRealPolarizationMuMinus Cmodel A
                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                          n pole a tauBand))
                      (PptFactorization.AppendixB.finRealPolarizationMuPlus Cmodel A
                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                          n pole a tauBand))
                      avg ∧
                    avg ≤
                      sSup
                        (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                          n r A)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hUniformGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ δ : ℝ, 0 < δ ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                δ ≤
                  sSup
                    (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                      n r A) :=
    PptFactorization.AppendixB.uniform_polarization_gainSup_lower_of_lemma43_heightBands_separateTau_gainSup_equal_mass_pos_lt_pi
      hLemma43SeparateTau
  have hCompare :
      PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo :=
    PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo_of_uniform_polarization_gainSup_lower_pos_lt_pi
      hUniformGainSup
  have hFullIso :
      PptFactorization.AppendixB.FullSphericalIsoperimetry :=
    fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleClosedHalfspaceCosinePowerTailBelowHalf
      hCompare hClosedHalfspaceCosineTailBelowHalf
  exact
    upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hFullIso hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope

include hk3 hε hOneSided hCoordinateCosineTailBelowHalf
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Separate-scale height-band Lemma 4.3 endpoint with the cap-tail leaf in
the sharper one-dimensional below-half coordinate-law form.  The surface-cap
below-half version is supplied internally by the checked coordinate
push-forward adapter. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43SeparateTau_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hLemma43SeparateTau :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tauBand tauSep : ℝ, 0 < eps ∧ 0 < tauSep ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                ∃ Cmodel : Set (PptFactorization.AppendixB.FinRealSphere n),
                  ∃ pole : PptFactorization.AppendixB.FinRealSphere n,
                  ∃ a avg : ℝ,
                    MeasurableSet Cmodel ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        Cmodel =
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        A ∧
                    eps ≤
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (Cmodel ∆ A) ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                          n pole a tauBand) ≤ eps / 4 ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                          n pole a tauBand) ≤ eps / 4 ∧
                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tauSep
                      (PptFactorization.AppendixB.finRealPolarizationMuMinus Cmodel A
                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                          n pole a tauBand))
                      (PptFactorization.AppendixB.finRealPolarizationMuPlus Cmodel A
                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                          n pole a tauBand))
                      avg ∧
                    avg ≤
                      sSup
                        (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                          n r A)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hUniformGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ δ : ℝ, 0 < δ ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                δ ≤
                  sSup
                    (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                      n r A) :=
    PptFactorization.AppendixB.uniform_polarization_gainSup_lower_of_lemma43_heightBands_separateTau_gainSup_equal_mass_pos_lt_pi
      hLemma43SeparateTau
  have hCompare :
      PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo :=
    PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo_of_uniform_polarization_gainSup_lower_pos_lt_pi
      hUniformGainSup
  have hFullIso :
      PptFactorization.AppendixB.FullSphericalIsoperimetry :=
    fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleCoordinateCosinePowerTailBelowHalf
      hCompare hCoordinateCosineTailBelowHalf
  exact
    upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hFullIso hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope

include hk3 hε hOneSided hCoordinateCosineTailBelowHalf
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Rectangular-separation height-band Lemma 4.3 endpoint with the cap-tail
leaf in the one-dimensional below-half coordinate-law form.

The Lemma 4.3 data chooses thin height bands at thickness `tau` while allowing
the rectangular block lower bound at a possibly larger separation `tauRect`.
The uniform gain-supremum supplier is derived internally by the checked
`rectTau` adapter. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43HeightBandsRectTau_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hLemma43HeightBandsRectTau :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tau tauRect : ℝ, 0 < eps ∧ 0 < tau ∧ tau ≤ tauRect ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                ∃ Cmodel : Set (PptFactorization.AppendixB.FinRealSphere n),
                  ∃ pole : PptFactorization.AppendixB.FinRealSphere n,
                  ∃ a avg : ℝ,
                    MeasurableSet Cmodel ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        Cmodel =
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        A ∧
                    eps ≤
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (Cmodel ∆ A) ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                          n pole a tau) ≤ eps / 4 ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                          n pole a tau) ≤ eps / 4 ∧
                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tauRect
                      (PptFactorization.AppendixB.finRealPolarizationMuMinus Cmodel A
                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                          n pole a tau))
                      (PptFactorization.AppendixB.finRealPolarizationMuPlus Cmodel A
                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                          n pole a tau))
                      avg ∧
                    avg ≤
                      sSup
                        (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                          n r A)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hUniformGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ δ : ℝ, 0 < δ ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                δ ≤
                  sSup
                    (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                      n r A) :=
    PptFactorization.AppendixB.uniform_polarization_gainSup_lower_of_lemma43_heightBands_rectTau_gainSup_equal_mass_pos_lt_pi
      hLemma43HeightBandsRectTau
  exact
    upper_eventual_from_concrete_sequences_of_uniformPolarizationGainSup_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hCoordinateCosineTailBelowHalf
      hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
      hBudget hEnvelope hUniformGainSup

include hk3 hε hOneSided
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Separate-scale height-band Lemma 4.3 endpoint with the cap-tail leaf stated
directly in the below-half ambient cap-cone form. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43SeparateTau_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hCapConeCosineTailBelowHalf :
      PptFactorization.AppendixB.sphere_northPoleCapConeCosinePowerTailBelowHalf)
    (hLemma43SeparateTau :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tauBand tauSep : ℝ, 0 < eps ∧ 0 < tauSep ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                ∃ Cmodel : Set (PptFactorization.AppendixB.FinRealSphere n),
                  ∃ pole : PptFactorization.AppendixB.FinRealSphere n,
                  ∃ a avg : ℝ,
                    MeasurableSet Cmodel ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        Cmodel =
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        A ∧
                    eps ≤
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (Cmodel ∆ A) ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                          n pole a tauBand) ≤ eps / 4 ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                          n pole a tauBand) ≤ eps / 4 ∧
                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tauSep
                      (PptFactorization.AppendixB.finRealPolarizationMuMinus Cmodel A
                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                          n pole a tauBand))
                      (PptFactorization.AppendixB.finRealPolarizationMuPlus Cmodel A
                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                          n pole a tauBand))
                      avg ∧
                    avg ≤
                      sSup
                        (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                          n r A)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hUniformGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ δ : ℝ, 0 < δ ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                δ ≤
                  sSup
                    (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                      n r A) :=
    PptFactorization.AppendixB.uniform_polarization_gainSup_lower_of_lemma43_heightBands_separateTau_gainSup_equal_mass_pos_lt_pi
      hLemma43SeparateTau
  exact
    upper_eventual_from_concrete_sequences_of_uniformPolarizationGainSup_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope
      hCapConeCosineTailBelowHalf hUniformGainSup

include hk3 hε hOneSided hClosedHalfspaceCosineTailBelowHalf
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Fixed-height-band direct-gain-supremum endpoint.

The Lemma 4.3 data here states the rectangular block estimate directly against
`sSup` of the polarization objective gains, so the older auxiliary `avg`
witness is not visible in the upper endpoint. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43HeightBandsDirectGainSup_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hLemma43HeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tau : ℝ, 0 < eps ∧ 0 < tau ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                ∃ Cmodel : Set (PptFactorization.AppendixB.FinRealSphere n),
                  ∃ pole : PptFactorization.AppendixB.FinRealSphere n,
                  ∃ a : ℝ,
                    MeasurableSet Cmodel ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        Cmodel =
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        A ∧
                    eps ≤
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (Cmodel ∆ A) ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                          n pole a tau) ≤ eps / 4 ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                          n pole a tau) ≤ eps / 4 ∧
                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tau
                      (PptFactorization.AppendixB.finRealPolarizationMuMinus Cmodel A
                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                          n pole a tau))
                      (PptFactorization.AppendixB.finRealPolarizationMuPlus Cmodel A
                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                          n pole a tau))
                      (sSup
                        (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                          n r A))) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hCompare :
      PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo :=
    PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo_of_lemma43_heightBands_directGainSup_equal_mass_pos_lt_pi
      hLemma43HeightBandsDirectGainSup
  have hFullIso :
      PptFactorization.AppendixB.FullSphericalIsoperimetry :=
    fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleClosedHalfspaceCosinePowerTailBelowHalf
      hCompare hClosedHalfspaceCosineTailBelowHalf
  exact
    upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hFullIso hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope

/-- Fixed-height-band direct block-to-`sSup` Lemma 4.3 data plus the
one-dimensional below-half north-pole coordinate power tail supply the full
real-sphere isoperimetric package. -/
theorem fullSphericalIsoperimetry_of_lemma43HeightBandsDirectGainSup_northPoleCoordinateCosinePowerTailBelowHalf
    (hLemma43HeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tau : ℝ, 0 < eps ∧ 0 < tau ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                ∃ Cmodel : Set (PptFactorization.AppendixB.FinRealSphere n),
                  ∃ pole : PptFactorization.AppendixB.FinRealSphere n,
                  ∃ a : ℝ,
                    MeasurableSet Cmodel ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        Cmodel =
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        A ∧
                    eps ≤
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (Cmodel ∆ A) ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                          n pole a tau) ≤ eps / 4 ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                          n pole a tau) ≤ eps / 4 ∧
                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tau
                      (PptFactorization.AppendixB.finRealPolarizationMuMinus Cmodel A
                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                          n pole a tau))
                      (PptFactorization.AppendixB.finRealPolarizationMuPlus Cmodel A
                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                          n pole a tau))
                      (sSup
                        (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                          n r A)))
    (hCoordinateCosineTailBelowHalf :
      PptFactorization.AppendixB.sphere_northPoleCoordinateCosinePowerTailBelowHalf) :
    PptFactorization.AppendixB.FullSphericalIsoperimetry := by
  have hCompare :
      PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo :=
    PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo_of_lemma43_heightBands_directGainSup_equal_mass_pos_lt_pi
      hLemma43HeightBandsDirectGainSup
  exact
    fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleCoordinateCosinePowerTailBelowHalf
      hCompare hCoordinateCosineTailBelowHalf

include hk3 hε hOneSided
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Fixed-height-band direct-gain-supremum endpoint with the tail stated as
the below-half north-pole coordinate law.

The coordinate tail is packaged directly into the full real-sphere
isoperimetry supplier for this fixed-height direct branch. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43HeightBandsDirectGainSup_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hLemma43HeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tau : ℝ, 0 < eps ∧ 0 < tau ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                ∃ Cmodel : Set (PptFactorization.AppendixB.FinRealSphere n),
                  ∃ pole : PptFactorization.AppendixB.FinRealSphere n,
                  ∃ a : ℝ,
                    MeasurableSet Cmodel ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        Cmodel =
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        A ∧
                    eps ≤
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (Cmodel ∆ A) ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                          n pole a tau) ≤ eps / 4 ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                          n pole a tau) ≤ eps / 4 ∧
                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tau
                      (PptFactorization.AppendixB.finRealPolarizationMuMinus Cmodel A
                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                          n pole a tau))
                      (PptFactorization.AppendixB.finRealPolarizationMuPlus Cmodel A
                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                          n pole a tau))
                      (sSup
                        (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                          n r A)))
    (hCoordinateCosineTailBelowHalf :
      PptFactorization.AppendixB.sphere_northPoleCoordinateCosinePowerTailBelowHalf) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hFullIso :
      PptFactorization.AppendixB.FullSphericalIsoperimetry :=
    fullSphericalIsoperimetry_of_lemma43HeightBandsDirectGainSup_northPoleCoordinateCosinePowerTailBelowHalf
      hLemma43HeightBandsDirectGainSup hCoordinateCosineTailBelowHalf
  exact
    upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hFullIso hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope

include hk3 hε hOneSided
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Fixed-height-band Lemma 4.3 endpoint with the rectangular block first
bounded by an auxiliary average, then compared to the objective-gain supremum.

This keeps the sharp fixed-height coordinate-tail upper endpoint available from
the strict-improvement core's natural `avg ≤ sSup` output, deriving the direct
block-to-`sSup` supplier internally. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43HeightBandsGainSup_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hLemma43HeightBandsGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tau : ℝ, 0 < eps ∧ 0 < tau ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                ∃ Cmodel : Set (PptFactorization.AppendixB.FinRealSphere n),
                  ∃ pole : PptFactorization.AppendixB.FinRealSphere n,
                  ∃ a avg : ℝ,
                    MeasurableSet Cmodel ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        Cmodel =
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        A ∧
                    eps ≤
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (Cmodel ∆ A) ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                          n pole a tau) ≤ eps / 4 ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                          n pole a tau) ≤ eps / 4 ∧
                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tau
                      (PptFactorization.AppendixB.finRealPolarizationMuMinus Cmodel A
                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                          n pole a tau))
                      (PptFactorization.AppendixB.finRealPolarizationMuPlus Cmodel A
                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                          n pole a tau))
                      avg ∧
                    avg ≤
                      sSup
                        (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                          n r A))
    (hCoordinateCosineTailBelowHalf :
      PptFactorization.AppendixB.sphere_northPoleCoordinateCosinePowerTailBelowHalf) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  exact
    upper_eventual_from_concrete_sequences_of_lemma43HeightBandsDirectGainSup_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope
      (PptFactorization.AppendixB.lemma43_heightBands_directGainSup_equal_mass_of_heightBands_gainSup_equal_mass_pos_lt_pi
        hLemma43HeightBandsGainSup)
      hCoordinateCosineTailBelowHalf

include hk3 hε hOneSided hLemma43AutoHeightBands hClosedHalfspaceCosineTailBelowHalf
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Sharp canonical upper endpoint with the cap-comparison leaf supplied by
the current auto-height-band Lemma 4.3 route, while keeping the below-half
north-pole tail in the normalized surface-cap form targeted by the cone
formula. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBands_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hCompare :
      PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo :=
    PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo_of_lemma43_autoHeightBands_gainSup_equal_mass_pos_lt_pi
      hLemma43AutoHeightBands
  have hFullIso :
      PptFactorization.AppendixB.FullSphericalIsoperimetry :=
    fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleClosedHalfspaceCosinePowerTailBelowHalf
      hCompare hClosedHalfspaceCosineTailBelowHalf
  exact
    upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hFullIso hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope

include hk3 hε hOneSided hCompare
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Sharp canonical upper endpoint with cap comparison separated and the
remaining north-pole tail stated in the below-half ambient cap-cone form. -/
theorem upper_eventual_from_concrete_sequences_of_hemisphereComparison_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hCapConeCosineTailBelowHalf :
      PptFactorization.AppendixB.sphere_northPoleCapConeCosinePowerTailBelowHalf) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hFullIso :
      PptFactorization.AppendixB.FullSphericalIsoperimetry :=
    fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleCapConeCosinePowerTailBelowHalf
      hCompare hCapConeCosineTailBelowHalf
  exact
    upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hFullIso hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope

include hk3 hε hOneSided hCompare hClosedHalfspaceCosineTailBelowHalf
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Compatibility endpoint with the cap-tail supplier stated as the normalized
surface measure of the north-pole closed halfspace.  The sharp no-tail-input
route now uses the cap-flattening map wrapper below; this theorem remains useful
when callers already have the surface-cap form available. -/
theorem upper_eventual_from_concrete_sequences_of_hemisphereComparison_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hFullIso :
      PptFactorization.AppendixB.FullSphericalIsoperimetry :=
    fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleClosedHalfspaceCosinePowerTailBelowHalf
      hCompare hClosedHalfspaceCosineTailBelowHalf
  exact
    upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hFullIso hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope

include hk3 hε hOneSided hCompare hCoordinateCosineTailBelowHalf
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Sharp canonical upper endpoint with the global half-mass cap comparison
already separated from the remaining north-pole below-half cap-tail leaf.

This is the modular endpoint to use after the spherical isoperimetry core is
closed independently: Lemma 4.3 no longer appears in the theorem-facing
frontier, and the tail side is still reduced to its nontrivial below-half
coordinate-law range. -/
theorem upper_eventual_from_concrete_sequences_of_hemisphereComparison_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hFullIso :
      PptFactorization.AppendixB.FullSphericalIsoperimetry :=
    fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleCoordinateCosinePowerTailBelowHalf
      hCompare hCoordinateCosineTailBelowHalf
  exact
    upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hFullIso hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope

include hk3 hε hOneSided hCompare
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Sharp canonical upper endpoint with cap comparison separated and the
remaining north-pole tail stated directly as the normalized closed-halfspace
Gaussian large-exponent package. -/
theorem upper_eventual_from_concrete_sequences_of_hemisphereComparison_northPoleClosedHalfspaceGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hSurfaceTail :
      PptFactorization.AppendixB.sphere_northPoleClosedHalfspaceGaussianTailLargeExponent) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hFullIso :
      PptFactorization.AppendixB.FullSphericalIsoperimetry :=
    fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleClosedHalfspaceGaussianTailLargeExponent
      hCompare hSurfaceTail
  exact
    upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hFullIso hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope

include hk3 hε hOneSided hCompare
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Sharp canonical upper endpoint with cap comparison separated and the
remaining north-pole tail stated directly as the ambient cap-cone Gaussian
large-exponent package. -/
theorem upper_eventual_from_concrete_sequences_of_hemisphereComparison_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hConeTail :
      PptFactorization.AppendixB.sphere_northPoleCapConeGaussianTailLargeExponent) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  exact
    upper_eventual_from_concrete_sequences_of_hemisphereComparison_northPoleClosedHalfspaceGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope hCompare
      (PptFactorization.AppendixB.sphere_northPoleClosedHalfspaceGaussianTailLargeExponent_of_coneTail
        hConeTail)

include hk3 hε hOneSided
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Uniform polarization gain-supremum endpoint with the remaining north-pole
tail stated directly as the ambient cap-cone Gaussian large-exponent package.

This is the generic proof-core adapter behind the separate-tau and rect-tau
cone-Gaussian routes: it replaces raw cap comparison by the uniform positive
lower bound on the supremum of polarization objective gains. -/
theorem upper_eventual_from_concrete_sequences_of_uniformPolarizationGainSup_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hConeTail :
      PptFactorization.AppendixB.sphere_northPoleCapConeGaussianTailLargeExponent)
    (hUniformGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ δ : ℝ, 0 < δ ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                δ ≤
                  sSup
                    (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                      n r A)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hCompare :
      PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo :=
    PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo_of_uniform_polarization_gainSup_lower_pos_lt_pi
      hUniformGainSup
  exact
    upper_eventual_from_concrete_sequences_of_hemisphereComparison_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope hCompare hConeTail

include hk3 hε hOneSided
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Uniform polarization-improvement endpoint with the remaining north-pole
tail stated directly as the ambient cap-cone Gaussian large-exponent package.

This is the strict-improvement proof-core analogue of the uniform gain-supremum
cone-Gaussian adapter: it consumes an actual improving polarization direction,
derives cap comparison internally, and passes the Gaussian cap-cone tail to the
modular hemisphere-comparison endpoint. -/
theorem upper_eventual_from_concrete_sequences_of_uniformPolarizationGap_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hConeTail :
      PptFactorization.AppendixB.sphere_northPoleCapConeGaussianTailLargeExponent)
    (hUniformGap :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ δ : ℝ, 0 < δ ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                ∃ v : PptFactorization.AppendixB.FinRealSphere n,
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A + δ ≤
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSpherePolarization
                        (PptFactorization.AppendixB.finRealSphereReflectionMap n) v A)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hCompare :
      PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo :=
    PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo_of_uniform_polarization_gap_improvement_pos_lt_pi
      hUniformGap
  exact
    upper_eventual_from_concrete_sequences_of_hemisphereComparison_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope hCompare hConeTail

include hk3 hε hOneSided hLemma43AutoHeightBands
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Average-form auto-height-band Lemma 4.3 endpoint routed through the
strict uniform polarization-improvement API.

This is the source-explicit strict-improvement analogue of the proof-core
cone-Gaussian endpoint: the average/block Lemma 4.3 data first supplies actual
improving polarization directions, and the cap comparison is then derived by
the same minimality contradiction as the abstract `hUniformGap` route. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsStrictGap_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hConeTail :
      PptFactorization.AppendixB.sphere_northPoleCapConeGaussianTailLargeExponent) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hUniformGap :=
    PptFactorization.AppendixB.uniform_polarization_gap_improvement_of_lemma43_autoHeightBands_gainSup_equal_mass_pos_lt_pi
      hLemma43AutoHeightBands
  exact
    upper_eventual_from_concrete_sequences_of_uniformPolarizationGap_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope hConeTail hUniformGap

include hk3 hε hOneSided hLemma43AutoHeightBands
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Average-form auto-height-band Lemma 4.3 endpoint routed through the
strict uniform polarization-improvement API, with the tail exposed in the
below-half ambient cap-cone power form.

This sharpens the source-explicit strict route by replacing the Gaussian
large-exponent cone-tail package with the smaller below-half cap-cone power-law
supplier, from which the Gaussian package is already known to follow. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsStrictGap_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hCapConeCosineTailBelowHalf :
      PptFactorization.AppendixB.sphere_northPoleCapConeCosinePowerTailBelowHalf) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hUniformGap :=
    PptFactorization.AppendixB.uniform_polarization_gap_improvement_of_lemma43_autoHeightBands_gainSup_equal_mass_pos_lt_pi
      hLemma43AutoHeightBands
  exact
    upper_eventual_from_concrete_sequences_of_uniformPolarizationGap_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope hCapConeCosineTailBelowHalf hUniformGap

include hk3 hε hOneSided hLemma43AutoHeightBands hClosedHalfspaceCosineTailBelowHalf
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Average-form auto-height-band Lemma 4.3 endpoint routed through the
strict uniform polarization-improvement API, with the tail exposed in the
normalized below-half closed-halfspace form.

This is the surface-tail analogue of the average-form cap-cone strict endpoint:
the average/block Lemma 4.3 data supplies actual improving polarization
directions, and the normalized surface-cap tail is consumed directly by the
strict proof-core route. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsStrictGap_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hUniformGap :=
    PptFactorization.AppendixB.uniform_polarization_gap_improvement_of_lemma43_autoHeightBands_gainSup_equal_mass_pos_lt_pi
      hLemma43AutoHeightBands
  exact
    upper_eventual_from_concrete_sequences_of_uniformPolarizationGap_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope
      hClosedHalfspaceCosineTailBelowHalf hUniformGap

include hk3 hε hOneSided hCoordinateCosineTailBelowHalf
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Uniform polarization-improvement endpoint with the remaining north-pole
tail stated directly in the one-dimensional below-half coordinate-law form.
The coordinate push-forward and surface/cone normalization are internal, so
this proof-core route exposes only the actual strict-improvement supplier and
the sharp coordinate-tail leaf. -/
theorem upper_eventual_from_concrete_sequences_of_uniformPolarizationGap_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hUniformGap :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ δ : ℝ, 0 < δ ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                ∃ v : PptFactorization.AppendixB.FinRealSphere n,
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A + δ ≤
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSpherePolarization
                        (PptFactorization.AppendixB.finRealSphereReflectionMap n) v A)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hCapConeCosineTailBelowHalf :
      PptFactorization.AppendixB.sphere_northPoleCapConeCosinePowerTailBelowHalf :=
    PptFactorization.AppendixB.sphere_northPoleCapConeCosinePowerTailBelowHalf_of_closedHalfspaceCosinePowerTailBelowHalf
      (PptFactorization.AppendixB.sphere_northPoleClosedHalfspaceCosinePowerTailBelowHalf_of_coordinateCosinePowerTailBelowHalf
        hCoordinateCosineTailBelowHalf)
  exact
    upper_eventual_from_concrete_sequences_of_uniformPolarizationGap_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope
      hCapConeCosineTailBelowHalf hUniformGap

include hk3 hε hOneSided hLemma43AutoHeightBands
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Average-form auto-height-band Lemma 4.3 endpoint routed through the
strict uniform polarization-improvement API, with the tail exposed in the
one-dimensional north-pole coordinate-law below-half form.

The coordinate-law tail is converted to the normalized surface cap form by the
checked push-forward adapter, then to the ambient cap-cone form by the
surface/cone adapter. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsStrictGap_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hCoordinateTailBelowHalf :
      PptFactorization.AppendixB.sphere_northPoleCoordinateCosinePowerTailBelowHalf) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hUniformGap :=
    PptFactorization.AppendixB.uniform_polarization_gap_improvement_of_lemma43_autoHeightBands_gainSup_equal_mass_pos_lt_pi
      hLemma43AutoHeightBands
  exact
    upper_eventual_from_concrete_sequences_of_uniformPolarizationGap_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hCoordinateTailBelowHalf hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope hUniformGap

include hk3 hε hOneSided hLemma43AutoHeightBandsDirectGainSup
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Direct auto-height-band block-to-`sSup` Lemma 4.3 data routed through the
strict uniform polarization-improvement API, with the remaining tail stated as
the ambient north-pole cone-Gaussian large-exponent package.

This is the direct-data strict analogue of the average-form cone-Gaussian
endpoint: the direct block lower bound supplies actual improving polarization
directions before the modular upper endpoint consumes the cone-Gaussian tail. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectStrictGap_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hConeTail :
      PptFactorization.AppendixB.sphere_northPoleCapConeGaussianTailLargeExponent) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hUniformGap :=
    PptFactorization.AppendixB.uniform_polarization_gap_improvement_of_lemma43_autoHeightBands_directGainSup_equal_mass_pos_lt_pi
      hLemma43AutoHeightBandsDirectGainSup
  exact
    upper_eventual_from_concrete_sequences_of_uniformPolarizationGap_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope hConeTail hUniformGap

include hk3 hε hOneSided hLemma43AutoHeightBandsDirectGainSup
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Direct auto-height-band block-to-`sSup` Lemma 4.3 data routed through the
strict uniform polarization-improvement API, with the remaining tail exposed as
the north-pole large-exponent coordinate Gaussian tail.

This removes the ambient cone-volume formulation from the direct strict
frontier: the existing cone/surface normalization adapter supplies
`sphere_northPoleCapConeGaussianTailLargeExponent` from the coordinate-law
large-exponent north-pole tail. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectStrictGap_northPoleCoordinateGaussianTailInteriorLargeExponentNorthPole_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hNorthTail :
      PptFactorization.AppendixB.sphere_coordinateGaussianTailInteriorLargeExponentNorthPole) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  exact
    upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectStrictGap_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hLemma43AutoHeightBandsDirectGainSup
      hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
      hBudget hEnvelope
      (PptFactorization.AppendixB.sphere_northPoleCapConeGaussianTailLargeExponent_of_coordinateTail
        hNorthTail)

include hk3 hε hOneSided hLemma43AutoHeightBandsDirectGainSup
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Direct auto-height-band block-to-`sSup` Lemma 4.3 data routed through the
coordinate-Gaussian strict endpoint, with that Gaussian tail discharged by the
below-half north-pole coordinate power-law tail.

This is an explicit theorem-facing adapter showing that the coordinate
large-exponent Gaussian leaf is no longer independent once the sharper
below-half coordinate power law is selected as the active tail supplier. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectStrictGap_northPoleCoordinateGaussianTailInteriorLargeExponentNorthPole_of_coordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hCoordinateTailBelowHalf :
      PptFactorization.AppendixB.sphere_northPoleCoordinateCosinePowerTailBelowHalf) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  exact
    upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectStrictGap_northPoleCoordinateGaussianTailInteriorLargeExponentNorthPole_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hLemma43AutoHeightBandsDirectGainSup
      hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
      hBudget hEnvelope
      (PptFactorization.AppendixB.sphere_coordinateGaussianTailInteriorLargeExponentNorthPole_of_coordinateCosinePowerTailBelowHalf
        hCoordinateTailBelowHalf)

include hk3 hε hOneSided hLemma43AutoHeightBandsDirectGainSup
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Direct auto-height-band block-to-`sSup` Lemma 4.3 data routed through the
strict uniform polarization-improvement API, with the tail exposed in the
below-half ambient cap-cone power form.

This is the direct-data strict analogue of the average-form cap-cone endpoint:
it keeps the actual strict-improvement route and replaces the cone-Gaussian
package by the smaller power-law tail supplier. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectStrictGap_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hCapConeCosineTailBelowHalf :
      PptFactorization.AppendixB.sphere_northPoleCapConeCosinePowerTailBelowHalf) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hUniformGap :=
    PptFactorization.AppendixB.uniform_polarization_gap_improvement_of_lemma43_autoHeightBands_directGainSup_equal_mass_pos_lt_pi
      hLemma43AutoHeightBandsDirectGainSup
  exact
    upper_eventual_from_concrete_sequences_of_uniformPolarizationGap_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope
      hCapConeCosineTailBelowHalf hUniformGap

include hk3 hε hOneSided hLemma43AutoHeightBandsDirectGainSup
  hClosedHalfspaceCosineTailBelowHalf hIsoRealDim hOperatorDim ha hK_half hEta
  hMomentWordBound hMomentTermLimit hBudget hEnvelope in
/-- Direct auto-height-band block-to-`sSup` Lemma 4.3 data routed through the
strict uniform polarization-improvement API, with the tail exposed in the
normalized below-half closed-halfspace form.

This is the direct-data surface-tail analogue of the cap-cone strict endpoint:
the block lower bound supplies actual improving polarization directions, and
the normalized surface-cap tail is consumed directly by the strict proof-core
route. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectStrictGap_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hUniformGap :=
    PptFactorization.AppendixB.uniform_polarization_gap_improvement_of_lemma43_autoHeightBands_directGainSup_equal_mass_pos_lt_pi
      hLemma43AutoHeightBandsDirectGainSup
  exact
    upper_eventual_from_concrete_sequences_of_uniformPolarizationGap_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope
      hClosedHalfspaceCosineTailBelowHalf hUniformGap

include hk3 hε hOneSided hLemma43AutoHeightBandsDirectGainSup
  hClosedHalfspaceCosineTailBelowHalf hIsoRealDim hOperatorDim in
/-- Direct strict closed-halfspace endpoint with the background half-mass
input removed from the theorem-facing frontier.

This routes the same Lemma 4.3 direct strict geometry and normalized
closed-halfspace tail through the isolated-moment/concrete-operator-tail
pipeline.  Thus `hK_half` is no longer a user-supplied hypothesis here: the
half-mass statement is obtained internally from the isolated moment bad-set
bound, the already-proved concrete Gaussian operator tails, and the scalar
union budget closed by the canonical moment scale. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectStrictGap_northPoleClosedHalfspaceCosinePowerTailBelowHalf_oneSidedPositive_isolatedMomentConcreteOperatorTails_canonicalMixedWords
    (hMoment :
      UpperConcreteMomentBadSetScaleBound
        (p := p) (q := q) (σ := σ) C k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hUniformGap :=
    PptFactorization.AppendixB.uniform_polarization_gap_improvement_of_lemma43_autoHeightBands_directGainSup_equal_mass_pos_lt_pi
      hLemma43AutoHeightBandsDirectGainSup
  have hCompare :
      PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo :=
    PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo_of_uniform_polarization_gap_improvement_pos_lt_pi
      hUniformGap
  have hFullIso :
      PptFactorization.AppendixB.FullSphericalIsoperimetry :=
    fullSphericalIsoperimetry_of_hemisphereComparisonGeTwo_and_northPoleClosedHalfspaceCosinePowerTailBelowHalf
      hCompare hClosedHalfspaceCosineTailBelowHalf
  exact
    upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_isolatedMomentConcreteOperatorTails_canonicalMixedWords
      (p := p) (q := q) (σ := σ) R
      (C := C)
      hk3 hε hOneSided hFullIso hIsoRealDim hOperatorDim hMoment

include hk3 hε hOneSided hLemma43AutoHeightBandsDirectGainSup
  hIsoRealDim hOperatorDim in
/-- Direct strict endpoint with the cap-tail supplier discharged by the explicit
cap-flattening map.

The theorem-facing tail input is gone on this route: the normalized
closed-halfspace below-half tail is obtained from the no-input ambient
cap-cone power law proved in `SphericalPolarizationPushforwardTransport`. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectStrictGap_capConeFlatteningMap_oneSidedPositive_isolatedMomentConcreteOperatorTails_canonicalMixedWords
    (hMoment :
      UpperConcreteMomentBadSetScaleBound
        (p := p) (q := q) (σ := σ) C k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hFullIso : PptFactorization.AppendixB.FullSphericalIsoperimetry :=
    fullSphericalIsoperimetry_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap
      hLemma43AutoHeightBandsDirectGainSup
  exact
    upper_eventual_from_concrete_sequences_of_fullIso_oneSidedPositive_isolatedMomentConcreteOperatorTails_canonicalMixedWords
      (p := p) (q := q) (σ := σ) R
      (C := C)
      hk3 hε hOneSided hFullIso hIsoRealDim hOperatorDim hMoment

include hk3 hε hOneSided hLemma43AutoHeightBandsDirectGainSup
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Direct auto-height-band block-to-`sSup` Lemma 4.3 data routed through the
strict uniform polarization-improvement API, with the remaining tail exposed in
the one-dimensional north-pole coordinate-law below-half form.

This is the direct-data analogue of the average-form strict endpoint above:
the block lower bound already targets the gain supremum, then the audited
half-gain extractor produces an actual improving polarization direction. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43AutoHeightBandsDirectStrictGap_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hCoordinateTailBelowHalf :
      PptFactorization.AppendixB.sphere_northPoleCoordinateCosinePowerTailBelowHalf) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hUniformGap :=
    PptFactorization.AppendixB.uniform_polarization_gap_improvement_of_lemma43_autoHeightBands_directGainSup_equal_mass_pos_lt_pi
      hLemma43AutoHeightBandsDirectGainSup
  exact
    upper_eventual_from_concrete_sequences_of_uniformPolarizationGap_northPoleCoordinateCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hCoordinateTailBelowHalf hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope hUniformGap

include hk3 hε hOneSided
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Separate-scale height-band Lemma 4.3 endpoint with the remaining
north-pole tail stated directly as the ambient cap-cone Gaussian
large-exponent package.

This is the separate-tau analogue of the rect-tau cone-Gaussian endpoint:
cap comparison is supplied internally through the uniform gain-supremum route,
while the prioritized cone-Gaussian tail remains the only tail-side input. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43SeparateTau_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hLemma43SeparateTau :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tauBand tauSep : ℝ, 0 < eps ∧ 0 < tauSep ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                ∃ Cmodel : Set (PptFactorization.AppendixB.FinRealSphere n),
                  ∃ pole : PptFactorization.AppendixB.FinRealSphere n,
                  ∃ a avg : ℝ,
                    MeasurableSet Cmodel ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        Cmodel =
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        A ∧
                    eps ≤
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (Cmodel ∆ A) ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                          n pole a tauBand) ≤ eps / 4 ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                          n pole a tauBand) ≤ eps / 4 ∧
                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tauSep
                      (PptFactorization.AppendixB.finRealPolarizationMuMinus Cmodel A
                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                          n pole a tauBand))
                      (PptFactorization.AppendixB.finRealPolarizationMuPlus Cmodel A
                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                          n pole a tauBand))
                      avg ∧
                    avg ≤
                      sSup
                        (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                          n r A))
    (hConeTail :
      PptFactorization.AppendixB.sphere_northPoleCapConeGaussianTailLargeExponent) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hUniformGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ δ : ℝ, 0 < δ ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                δ ≤
                  sSup
                    (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                      n r A) :=
    PptFactorization.AppendixB.uniform_polarization_gainSup_lower_of_lemma43_heightBands_separateTau_gainSup_equal_mass_pos_lt_pi
      hLemma43SeparateTau
  have hCompare :
      PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo :=
    PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo_of_uniform_polarization_gainSup_lower_pos_lt_pi
      hUniformGainSup
  exact
    upper_eventual_from_concrete_sequences_of_hemisphereComparison_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope hCompare hConeTail

include hk3 hε hOneSided
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Rectangular-separation height-band Lemma 4.3 endpoint with the remaining
north-pole tail stated directly as the ambient cap-cone Gaussian
large-exponent package.

This is the `rectTau` analogue of the fixed-height cone-Gaussian endpoint:
cap comparison is supplied internally through the uniform gain-supremum route,
while the prioritized cone-Gaussian tail remains the only tail-side input. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43HeightBandsRectTau_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hLemma43HeightBandsRectTau :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tau tauRect : ℝ, 0 < eps ∧ 0 < tau ∧ tau ≤ tauRect ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                ∃ Cmodel : Set (PptFactorization.AppendixB.FinRealSphere n),
                  ∃ pole : PptFactorization.AppendixB.FinRealSphere n,
                  ∃ a avg : ℝ,
                    MeasurableSet Cmodel ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        Cmodel =
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        A ∧
                    eps ≤
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (Cmodel ∆ A) ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                          n pole a tau) ≤ eps / 4 ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                          n pole a tau) ≤ eps / 4 ∧
                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tauRect
                      (PptFactorization.AppendixB.finRealPolarizationMuMinus Cmodel A
                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                          n pole a tau))
                      (PptFactorization.AppendixB.finRealPolarizationMuPlus Cmodel A
                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                          n pole a tau))
                      avg ∧
                    avg ≤
                      sSup
                        (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                          n r A))
    (hConeTail :
      PptFactorization.AppendixB.sphere_northPoleCapConeGaussianTailLargeExponent) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hUniformGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ δ : ℝ, 0 < δ ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                δ ≤
                  sSup
                    (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                      n r A) :=
    PptFactorization.AppendixB.uniform_polarization_gainSup_lower_of_lemma43_heightBands_rectTau_gainSup_equal_mass_pos_lt_pi
      hLemma43HeightBandsRectTau
  have hCompare :
      PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo :=
    PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo_of_uniform_polarization_gainSup_lower_pos_lt_pi
      hUniformGainSup
  exact
    upper_eventual_from_concrete_sequences_of_hemisphereComparison_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope hCompare hConeTail

include hk3 hε hOneSided
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Fixed-height-band direct-gain-supremum endpoint with the remaining
north-pole tail stated directly as the ambient cap-cone Gaussian
large-exponent package.

This is the direct fixed-height analogue of the auto-height cone-Gaussian
adapter: cap comparison is supplied internally by the block-to-`sSup` Lemma
4.3 data, while the cap-tail theorem remains the only tail-side input. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43HeightBandsDirectGainSup_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hLemma43HeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tau : ℝ, 0 < eps ∧ 0 < tau ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                ∃ Cmodel : Set (PptFactorization.AppendixB.FinRealSphere n),
                  ∃ pole : PptFactorization.AppendixB.FinRealSphere n,
                  ∃ a : ℝ,
                    MeasurableSet Cmodel ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        Cmodel =
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        A ∧
                    eps ≤
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (Cmodel ∆ A) ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                          n pole a tau) ≤ eps / 4 ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                          n pole a tau) ≤ eps / 4 ∧
                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tau
                      (PptFactorization.AppendixB.finRealPolarizationMuMinus Cmodel A
                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                          n pole a tau))
                      (PptFactorization.AppendixB.finRealPolarizationMuPlus Cmodel A
                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                          n pole a tau))
                      (sSup
                        (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                          n r A)))
    (hConeTail :
      PptFactorization.AppendixB.sphere_northPoleCapConeGaussianTailLargeExponent) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hCompare :
      PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo :=
    PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo_of_lemma43_heightBands_directGainSup_equal_mass_pos_lt_pi
      hLemma43HeightBandsDirectGainSup
  exact
    upper_eventual_from_concrete_sequences_of_hemisphereComparison_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope hCompare hConeTail

include hk3 hε hOneSided
  hIsoRealDim hOperatorDim ha hK_half hEta hMomentWordBound hMomentTermLimit
  hBudget hEnvelope in
/-- Fixed-height-band direct-gain-supremum endpoint with the tail in the
below-half ambient cap-cone power-law form.

This removes the large-exponent Gaussian tail input from the fixed-height
direct route by using the audited below-half cosine-power-to-Gaussian adapter. -/
theorem upper_eventual_from_concrete_sequences_of_lemma43HeightBandsDirectGainSup_northPoleCapConeCosinePowerTailBelowHalf_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
    (hLemma43HeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ eps tau : ℝ, 0 < eps ∧ 0 < tau ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                ∃ Cmodel : Set (PptFactorization.AppendixB.FinRealSphere n),
                  ∃ pole : PptFactorization.AppendixB.FinRealSphere n,
                  ∃ a : ℝ,
                    MeasurableSet Cmodel ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        Cmodel =
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        A ∧
                    eps ≤
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (Cmodel ∆ A) ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                          n pole a tau) ≤ eps / 4 ∧
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                          n pole a tau) ≤ eps / 4 ∧
                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n tau
                      (PptFactorization.AppendixB.finRealPolarizationMuMinus Cmodel A
                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                          n pole a tau))
                      (PptFactorization.AppendixB.finRealPolarizationMuPlus Cmodel A
                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                          n pole a tau))
                      (sSup
                        (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                          n r A)))
    (hCapConeCosineTailBelowHalf :
      PptFactorization.AppendixB.sphere_northPoleCapConeCosinePowerTailBelowHalf) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  exact
    upper_eventual_from_concrete_sequences_of_lemma43HeightBandsDirectGainSup_northPoleCapConeGaussianTailLargeExponent_oneSidedPositive_localExpansionMomentWordEnvelope_caseMixedWordBounds_caseMixedTermLimits_canonicalOneQTerm
      (p := p) (q := q) (σ := σ) R
      (C := C)
      (momentAbound := momentAbound) (momentL2bound := momentL2bound)
      (momentL1bound := momentL1bound) (momentQ2bound := momentQ2bound)
      (momentQ1bound := momentQ1bound)
      (aSlack := aSlack) (etaSlack := etaSlack) (M := M) (τ := τ)
      hk3 hε hOneSided hIsoRealDim hOperatorDim ha hK_half hEta
      hMomentWordBound hMomentTermLimit hBudget hEnvelope
      hLemma43HeightBandsDirectGainSup
      (PptFactorization.AppendixB.sphere_northPoleCapConeGaussianTailLargeExponent_of_cosinePowerTailBelowHalf
        hCapConeCosineTailBelowHalf)

end NorthPoleCoordinateCosineTailEndpoint

/-- Concrete upper closure with raw target positivity `hp` discharged from a
positive-measure deviation witness.

This is the `hp`-closed version of
`upper_eventual_from_concrete_sequences_of_fullIso_momentLimitConcreteOperatorTails_mixedWords`.
It still does not prove the target event is positive for free; the visible
replacement is the canonical witness data:

* `hE_pos`: a set `E d` has eventually positive spherical measure;
* `hE_subset`: that set is contained in the formal
  `backgroundMomentDeviationSet`.

Those two assumptions are exactly what imply the positivity of
`upperConcreteTargetProb`, and the rest of the proof is the existing upper
closure. -/
theorem upper_eventual_from_concrete_sequences_of_fullIso_positiveDeviationWitness_momentLimitConcreteOperatorTails_mixedWords
    {p q σ : Type*}
    [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (R : PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    {bMoment Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    {E : ℕ → Set (SampleMatrix p q σ)}
    (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hE_pos :
      ∀ᶠ d in atTop,
        0 <
          (upperConcreteSphericalMu
            (p := p) (q := q) (σ := σ) d).real (E d))
    (hE_subset :
      ∀ᶠ d in atTop,
        E d ⊆
          backgroundMomentDeviationSet
            (p := p) (q := q) (σ := σ)
            (upperConcreteN d) eps
            (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k)
    (hFullIso : PptFactorization.AppendixB.FullSphericalIsoperimetry)
    (hIsoRealDim :
      ∀ᶠ d in atTop,
        upperConcreteRealDim R d =
          2 * bipartiteDimension p q * sampleDimension σ)
    (hOperatorDim :
      ∀ᶠ d : ℕ in atTop,
        bipartiteDimension p q = (d : ℝ) ^ 2)
    (hMoment :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := p) (q := q) (σ := σ)).real
            (backgroundMomentBadSet
              (p := p) (q := q) (σ := σ)
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean (p := p) (q := q) (σ := σ) k d)
              k) ≤ bMoment slack d)
    (hMomentLimit :
      ∀ slack : ℝ, 0 < slack →
        Tendsto (bMoment slack) atTop (nhds 0))
    (hWordBound :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y : SampleMatrix p q σ⦄,
            Y ∈ backgroundTypicalSet
                (p := p) (q := q) (σ := σ)
                (upperConcreteN d)
                (upperConcreteM (p := p) (q := q) (σ := σ) slack d)
                (upperCanonicalTau slack d)
                (upperConcreteMean (p := p) (q := q) (σ := σ) k d) k →
            frobeniusNorm (p := p) (q := q) (σ := σ) (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed k d)
                (upperSlackRadius (spikeRoot k eps) R.lam slack) →
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                |localWordScaledTraceTerm
                    (p := p) (q := q)
                    (upperConcreteN d)
                    (localBackground (p := p) (q := q) (σ := σ) Y)
                    (localLinear (p := p) (q := q) (σ := σ) Y (X - Y))
                    (localQuadratic (p := p) (q := q) (σ := σ) (X - Y))
                    w| ≤
                  localExpansionMixedWordEnvelopeTerm
                    (upperConcreteN d) (Abound slack d) (L2bound slack d)
                    (L1bound slack d) (Q2bound slack d) (Q1bound slack d) k w)
    (hTermLimit :
      ∀ slack : ℝ, 0 < slack →
        ∀ w : Fin k → LocalExpansionLetter,
          localWordIsMixed w →
            Tendsto
              (fun d =>
                localExpansionMixedWordEnvelopeTerm
                  (upperConcreteN d) (Abound slack d) (L2bound slack d)
                  (L1bound slack d) (Q2bound slack d) (Q1bound slack d) k w)
              atTop (nhds 0)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log
            (upperConcreteTargetProb
              (p := p) (q := q) (σ := σ) eps k d) /
            spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_sequences_of_fullIso_momentLimitConcreteOperatorTails_mixedWords
    (p := p) (q := q) (σ := σ) R
    (bMoment := bMoment)
    (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
    (Q2bound := Q2bound) (Q1bound := Q1bound)
    hk3 hε
    (upper_hp_concreteTargetProb_of_positive_deviation_subset
      (p := p) (q := q) (σ := σ)
      (eps := eps) (k := k) (E := E)
      hE_pos hE_subset)
    hFullIso hIsoRealDim hOperatorDim hMoment hMomentLimit
    hWordBound hTermLimit

/-- External-input endpoint for the conditional upper-bound pipeline.

This is the clean endpoint when a concrete `SpikeUpperBoundInput` has already
been supplied externally.  It does not construct that input and therefore does
not prove the hard random-matrix upper LDP.  By dependency inspection, this
wrapper is project-dependency-clean in the same sense as the other aliases in
this file. -/
theorem upper_eventual_from_input
    {p : ℕ → ℝ} {k : ℕ} {lam ε : ℝ}
    (I : SpikeUpperBoundInput p k lam ε) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (p d) / spikeSpeed k d ≤
          -spikeRate k lam ε + η :=
  I.eventual_log_over_spikeSpeed_upper

end AppendixB
