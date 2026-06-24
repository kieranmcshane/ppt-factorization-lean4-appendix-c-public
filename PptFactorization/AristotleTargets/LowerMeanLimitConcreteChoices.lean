import Mathlib.Combinatorics.Enumerative.Catalan
import PptFactorization.ClosedFormDet
import PptFactorization.AppendixBLevyPolarBridge
import PptFactorization.AppendixBWishartBridge
import PptFactorization.AristotleTargets.LowerNoInputsConcreteChoices

/-!
Canonical mean-limit frontier for the concrete lower endpoint.

The repaired scale route first reduced the live lower frontier to the bounded
positive part of the deleted-background mean.  The sharp wrappers below now
remove that budget helper as well, replacing it by the exact deleted-column
moment asymptotic that would prove the bound.

* record the exact Catalan-series target value for the deleted-background mean;
* provide compatibility wrappers that still speak in finite-limit or
  `hMeanLimit` form;
* expose the preferred live mean-side frontier as the deleted-column spherical
  Catalan asymptotic.

It does not prove the deleted-background moment asymptotics: that is the
remaining hard theorem, not endpoint plumbing.

Protected file: do not edit `PptFactorization/AppendixBSpikeLowerBound.lean`.
-/
namespace AppendixB

open Filter
open PptFactorization.RandomMatrixModel
open scoped Topology BigOperators

/-- Explicit Catalan-series candidate limit for the deleted-background moment
sequence.

This is the natural target value in the lower mean-limit frontier:
`∑_{r ≤ ⌊k/2⌋} C(k,2r) Cat(r) λ^{-r}`. -/
noncomputable def lowerDeletedBackgroundMeanCatalanLimit
    (lam : ℝ) (k : ℕ) : ℝ :=
  Finset.sum (Finset.range (k / 2 + 1)) fun r =>
    ((Nat.choose k (2 * r) * catalan r : ℕ) : ℝ) * (lam⁻¹) ^ r

/-- The length-three Catalan center is the explicit shifted-semicircle value
`1 + 3 / lam`.

This is pure scalar bookkeeping; the random-matrix input is the convergence of
the deleted-column moment sequence to this value. -/
theorem lowerDeletedBackgroundMeanCatalanLimit_three (lam : ℝ) :
    lowerDeletedBackgroundMeanCatalanLimit lam 3 = 1 + 3 * lam⁻¹ := by
  simp [lowerDeletedBackgroundMeanCatalanLimit, Finset.sum_range_succ]

/-- Paper-facing name for the partial-transpose deleted-background Catalan
series.

This is the shifted-semicircle moment
`∑_{r ≤ ⌊k/2⌋} binom(k,2r) Catalan(r) λ^{-r}`.  It is intentionally an alias
for the lower endpoint's existing target value, so older endpoint wrappers and
the paper-facing theorem statement cannot drift apart. -/
noncomputable def ptCatalanMean (k : ℕ) (lam : ℝ) : ℝ :=
  lowerDeletedBackgroundMeanCatalanLimit lam k

/-- The paper-facing PT Catalan mean name is exactly the lower endpoint's
existing Catalan-series target. -/
theorem ptCatalanMean_eq_lowerDeletedBackgroundMeanCatalanLimit
    (k : ℕ) (lam : ℝ) :
    ptCatalanMean k lam = lowerDeletedBackgroundMeanCatalanLimit lam k := by
  rfl

/-- Length-three PT Catalan center, in the paper-facing notation. -/
theorem ptCatalanMean_three (lam : ℝ) :
    ptCatalanMean 3 lam = 1 + 3 * lam⁻¹ := by
  simpa [ptCatalanMean] using lowerDeletedBackgroundMeanCatalanLimit_three lam

/-- The Catalan-series target used by the lower endpoint is the already
formalized shifted-moment polynomial `ClosedFormDet.M`, with the normalization
converted from powers `λ^(k-r)` to powers `λ^{-r}`.

This records the bridge to the earlier closed-form moment work, so the
remaining deleted-column mean frontier is the random-matrix identification with
that moment, not the Catalan survivor polynomial itself. -/
theorem lowerDeletedBackgroundMeanCatalanLimit_eq_invPow_closedFormMoment
    {lam : ℝ} (hlam : lam ≠ 0) (k : ℕ) :
    lowerDeletedBackgroundMeanCatalanLimit lam k =
      (lam⁻¹) ^ k * ClosedFormDet.M lam k := by
  unfold lowerDeletedBackgroundMeanCatalanLimit ClosedFormDet.M
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [Finset.mem_range] at hr
  have hr_le : r ≤ k := by
    have hdiv : k / 2 ≤ k := Nat.div_le_self k 2
    omega
  have hpow : (lam⁻¹) ^ k * lam ^ (k - r) = (lam⁻¹) ^ r := by
    calc
      (lam⁻¹) ^ k * lam ^ (k - r)
          = (lam⁻¹) ^ (r + (k - r)) * lam ^ (k - r) := by
              rw [Nat.add_sub_of_le hr_le]
      _ = (lam⁻¹) ^ r * ((lam⁻¹) ^ (k - r) * lam ^ (k - r)) := by
              rw [pow_add]
              ring
      _ = (lam⁻¹) ^ r * ((lam⁻¹ * lam) ^ (k - r)) := by
              rw [← mul_pow]
      _ = (lam⁻¹) ^ r := by
              rw [inv_mul_cancel₀ hlam]
              simp
  calc
    ((Nat.choose k (2 * r) * catalan r : ℕ) : ℝ) * (lam⁻¹) ^ r
        =
          ((Nat.choose k (2 * r) * catalan r : ℕ) : ℝ) *
            ((lam⁻¹) ^ k * lam ^ (k - r)) := by
              rw [hpow]
    _ =
        (lam⁻¹) ^ k *
          (((Nat.choose k (2 * r) * catalan r : ℕ) : ℝ) * lam ^ (k - r)) := by
            ring

/-- Closed-form moment identity, in the paper-facing PT Catalan notation. -/
theorem ptCatalanMean_eq_invPow_closedFormMoment
    {lam : ℝ} (hlam : lam ≠ 0) (k : ℕ) :
    ptCatalanMean k lam = (lam⁻¹) ^ k * ClosedFormDet.M lam k := by
  simpa [ptCatalanMean] using
    lowerDeletedBackgroundMeanCatalanLimit_eq_invPow_closedFormMoment hlam k

/-- Canonical explicit mean-limit frontier assumption. -/
def lowerConcreteDeletedBackgroundMeanHasCatalanLimit
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) : Prop :=
  Tendsto (fun d : ℕ => lowerConcreteDeletedBackgroundMean R k d)
    atTop (nhds (lowerDeletedBackgroundMeanCatalanLimit R.lam k))

/-- Weaker finite-limit form of the same legacy mean-side frontier. -/
def lowerConcreteDeletedBackgroundMeanHasFiniteLimit
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) : Prop :=
  ∃ m : ℝ,
    Tendsto (fun d : ℕ => lowerConcreteDeletedBackgroundMean R k d)
      atTop (nhds m)

/-- Exact deleted-column aspect-ratio scalar lemma for the lower mean-limit
work.

Deleting one distinguished column does not change the limiting aspect ratio:
`(s_d - 1) / d² → λ`.  This is the concrete scalar fact needed before any hard
spherical moment asymptotic can be applied. -/
theorem lower_deletedColumn_ratio_tendsto_concreteChoices
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime) :
    Tendsto
      (fun d : ℕ => ((lowerConcreteS R d - 1 : ℕ) : ℝ) / (lowerConcreteN d : ℝ))
      atTop (nhds R.lam) := by
  have hratio :
      Tendsto
        (fun d : ℕ => (lowerConcreteS R d : ℝ) / (lowerConcreteN d : ℝ))
        atTop (nhds R.lam) := by
    simpa [lowerConcreteS, lowerConcreteN,
      _root_.PptFactorization.AppendixB.ConcreteModel.sampleRatio] using
      R.ratio_tendsto
  have hsq_atTop :
      Tendsto (fun d : ℕ => (lowerConcreteN d : ℝ)) atTop atTop := by
    simpa [lowerConcreteN] using
      ((tendsto_rpow_atTop (show (0 : ℝ) < 2 by norm_num)).comp
        tendsto_natCast_atTop_atTop)
  have hinv :
      Tendsto (fun d : ℕ => (1 : ℝ) / (lowerConcreteN d : ℝ))
        atTop (nhds 0) := by
    simpa [one_div] using (tendsto_inv_atTop_zero.comp hsq_atTop)
  have heq :
      (fun d : ℕ => ((lowerConcreteS R d - 1 : ℕ) : ℝ) / (lowerConcreteN d : ℝ))
        =ᶠ[atTop]
      (fun d : ℕ =>
        (lowerConcreteS R d : ℝ) / (lowerConcreteN d : ℝ) -
          (1 : ℝ) / (lowerConcreteN d : ℝ)) := by
    filter_upwards [R.sample_pos_eventually] with d hs
    have hs1 : 1 ≤ lowerConcreteS R d := Nat.succ_le_of_lt hs
    have hcast :
        ((lowerConcreteS R d - 1 : ℕ) : ℝ) =
          (lowerConcreteS R d : ℝ) - 1 := by
      rw [Nat.cast_sub hs1, Nat.cast_one]
    rw [hcast]
    ring
  exact Tendsto.congr' heq.symm (by simpa [sub_zero] using (hratio.sub hinv))

/-- Removing one sample column does not change the limiting aspect ratio.

This is the reusable scalar bridge between theorem statements written with the
full sample count `sample d` and deleted-column statements written with
`sample d - 1`. -/
theorem deletedColumn_ratio_tendsto_iff_sample_ratio_tendsto
    (sample : ℕ → ℕ)
    (hpos : ∀ᶠ d in atTop, 0 < sample d)
    (lam : ℝ) :
    Tendsto
        (fun d : ℕ => ((sample d - 1 : ℕ) : ℝ) / (lowerConcreteN d : ℝ))
        atTop (nhds lam) ↔
      Tendsto
        (fun d : ℕ => (sample d : ℝ) / (lowerConcreteN d : ℝ))
        atTop (nhds lam) := by
  have hN_atTop :
      Tendsto (fun d : ℕ => (lowerConcreteN d : ℝ)) atTop atTop := by
    simpa [lowerConcreteN] using
      ((tendsto_rpow_atTop (show (0 : ℝ) < 2 by norm_num)).comp
        tendsto_natCast_atTop_atTop)
  have hinv :
      Tendsto (fun d : ℕ => (1 : ℝ) / (lowerConcreteN d : ℝ))
        atTop (nhds 0) := by
    simpa [one_div] using (tendsto_inv_atTop_zero.comp hN_atTop)
  constructor
  · intro hdel
    have heq :
        (fun d : ℕ => (sample d : ℝ) / (lowerConcreteN d : ℝ))
          =ᶠ[atTop]
        (fun d : ℕ =>
          ((sample d - 1 : ℕ) : ℝ) / (lowerConcreteN d : ℝ) +
            (1 : ℝ) / (lowerConcreteN d : ℝ)) := by
      filter_upwards [hpos] with d hs
      have hs1 : 1 ≤ sample d := Nat.succ_le_of_lt hs
      have hcast :
          ((sample d - 1 : ℕ) : ℝ) = (sample d : ℝ) - 1 := by
        rw [Nat.cast_sub hs1, Nat.cast_one]
      rw [hcast]
      ring
    exact Tendsto.congr' heq.symm (by simpa [add_zero] using hdel.add hinv)
  · intro hsample
    have heq :
        (fun d : ℕ => ((sample d - 1 : ℕ) : ℝ) / (lowerConcreteN d : ℝ))
          =ᶠ[atTop]
        (fun d : ℕ =>
          (sample d : ℝ) / (lowerConcreteN d : ℝ) -
            (1 : ℝ) / (lowerConcreteN d : ℝ)) := by
      filter_upwards [hpos] with d hs
      have hs1 : 1 ≤ sample d := Nat.succ_le_of_lt hs
      have hcast :
          ((sample d - 1 : ℕ) : ℝ) = (sample d : ℝ) - 1 := by
        rw [Nat.cast_sub hs1, Nat.cast_one]
      rw [hcast]
      ring
    exact Tendsto.congr' heq.symm (by simpa [sub_zero] using hsample.sub hinv)

/-- Same ratio bridge in the manuscript normalization `d²`. -/
theorem deletedColumn_aspect_tendsto_iff_sample_aspect_tendsto
    (sample : ℕ → ℕ)
    (hpos : ∀ᶠ d in atTop, 0 < sample d)
    (lam : ℝ) :
    Tendsto
        (fun d : ℕ => ((sample d - 1 : ℕ) : ℝ) / ((d : ℝ) ^ 2))
        atTop (nhds lam) ↔
      Tendsto
        (fun d : ℕ => (sample d : ℝ) / ((d : ℝ) ^ 2))
        atTop (nhds lam) := by
  simpa [lowerConcreteN, Nat.cast_pow] using
    deletedColumn_ratio_tendsto_iff_sample_ratio_tendsto sample hpos lam

/-- Deleted-column spherical background moment sequence.

This is the sequence whose asymptotic is controlled by the spherical Wick
expansion: noncrossing pairings give the Catalan-limit term, while crossing
pairings and spherical radial corrections should be bounded by `D / d`. -/
noncomputable def lowerDeletedColumnBackgroundMomentSequence
    (sample : ℕ → ℕ) (k d : ℕ) : ℝ :=
  if hs : 0 < sample d then
    ∫ X : SampleMatrix (Fin d) (Fin d)
        (DeletedColumn (⟨0, hs⟩ : Fin (sample d))),
      backgroundMomentValue
        (p := Fin d) (q := Fin d)
        (σ := DeletedColumn (⟨0, hs⟩ : Fin (sample d)))
        (lowerConcreteN d) k X
      ∂_root_.PptFactorization.AppendixB.sphericalModelMeasure
        (p := Fin d) (q := Fin d)
        (σ := DeletedColumn (⟨0, hs⟩ : Fin (sample d)))
  else 0

/-- Paper-facing name for the deleted-column Hilbert--Schmidt spherical
partial-transpose moment.

Mathematically this is
`E[(d^2)^(k-1) Tr(((Y_d Y_d*)^Γ)^k)]`, with the deleted column count
`sample d - 1`.  It is an alias for the local sequence already consumed by the
lower endpoint. -/
noncomputable def deletedColumnSphericalMomentPT
    (sample : ℕ → ℕ) (k d : ℕ) : ℝ :=
  lowerDeletedColumnBackgroundMomentSequence sample k d

/-- Exact remaining mathematical input for the hard mean-limit closure.

This is the reusable deleted-column spherical moment asymptotic, detached from
the lower endpoint assembly.  Proving this proposition is the real remaining
work behind `hMeanLimit`; everything else in this file is just packaging. -/
def lowerDeletedColumnBackgroundMomentHasCatalanLimit
    (sample : ℕ → ℕ) (lam : ℝ) (k : ℕ) : Prop :=
  Tendsto
    (fun d : ℕ => lowerDeletedColumnBackgroundMomentSequence sample k d)
    atTop (nhds (lowerDeletedBackgroundMeanCatalanLimit lam k))

/-- Paper-facing proposition for the exact PT deleted-column spherical mean
theorem.

This is the displayed theorem:
`E[(d^2)^(k-1) Tr(((Y_dY_d*)^Γ)^k)] → ptCatalanMean k λ`. -/
def deletedColumnSphericalMean_tendsto_ptCatalan
    (sample : ℕ → ℕ) (k : ℕ) (lam : ℝ) : Prop :=
  Tendsto
    (fun d : ℕ => deletedColumnSphericalMomentPT sample k d)
    atTop (nhds (ptCatalanMean k lam))

/-- The paper-facing PT Catalan mean theorem is exactly the same frontier as
the lower endpoint's deleted-column Catalan moment asymptotic. -/
theorem deletedColumnSphericalMean_tendsto_ptCatalan_iff_lowerDeletedColumnBackgroundMomentHasCatalanLimit
    (sample : ℕ → ℕ) (k : ℕ) (lam : ℝ) :
    deletedColumnSphericalMean_tendsto_ptCatalan sample k lam ↔
      lowerDeletedColumnBackgroundMomentHasCatalanLimit sample lam k := by
  rfl

/-- Use the paper-facing PT Catalan mean theorem as the local lower-endpoint
mean asymptotic. -/
theorem lowerDeletedColumnBackgroundMomentHasCatalanLimit_of_deletedColumnSphericalMean_tendsto_ptCatalan
    (sample : ℕ → ℕ) (k : ℕ) (lam : ℝ)
    (hMean :
      deletedColumnSphericalMean_tendsto_ptCatalan sample k lam) :
    lowerDeletedColumnBackgroundMomentHasCatalanLimit sample lam k :=
  (deletedColumnSphericalMean_tendsto_ptCatalan_iff_lowerDeletedColumnBackgroundMomentHasCatalanLimit
    sample k lam).1 hMean

/-- Re-express the local lower-endpoint mean asymptotic in the paper-facing PT
Catalan theorem shape. -/
theorem deletedColumnSphericalMean_tendsto_ptCatalan_of_lowerDeletedColumnBackgroundMomentHasCatalanLimit
    (sample : ℕ → ℕ) (k : ℕ) (lam : ℝ)
    (hMean :
      lowerDeletedColumnBackgroundMomentHasCatalanLimit sample lam k) :
    deletedColumnSphericalMean_tendsto_ptCatalan sample k lam :=
  (deletedColumnSphericalMean_tendsto_ptCatalan_iff_lowerDeletedColumnBackgroundMomentHasCatalanLimit
    sample k lam).2 hMean

/-- Version of the deleted-column mean asymptotic centered at the previously
formalized closed-form moment polynomial.

Some older files state the limiting moment as `ClosedFormDet.M`; this
definition makes that work directly consumable by the lower endpoint. -/
def lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit
    (sample : ℕ → ℕ) (lam : ℝ) (k : ℕ) : Prop :=
  Tendsto
    (fun d : ℕ => lowerDeletedColumnBackgroundMomentSequence sample k d)
    atTop (nhds ((lam⁻¹) ^ k * ClosedFormDet.M lam k))

/-- Convert the older closed-form-moment centered statement into the Catalan
target used by the lower endpoint. -/
theorem lowerDeletedColumnBackgroundMomentHasCatalanLimit_of_closedFormMomentLimit
    (sample : ℕ → ℕ) {lam : ℝ} (hlam : lam ≠ 0) (k : ℕ)
    (hClosed :
      lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit sample lam k) :
    lowerDeletedColumnBackgroundMomentHasCatalanLimit sample lam k := by
  unfold lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit at hClosed
  unfold lowerDeletedColumnBackgroundMomentHasCatalanLimit
  rwa [lowerDeletedBackgroundMeanCatalanLimit_eq_invPow_closedFormMoment hlam k]

/-- Ratio-parametric form of the old closed-form-moment mean theorem.

This is the import shape to use when a prior formalization proves convergence
to the `ClosedFormDet.M` moment polynomial rather than to the local
`lowerDeletedBackgroundMeanCatalanLimit` name. -/
def lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit_fromRatio
    (sample : ℕ → ℕ) (k : ℕ) : Prop :=
  ∀ lam : ℝ,
    lam ≠ 0 →
    Tendsto
      (fun d : ℕ => ((sample d - 1 : ℕ) : ℝ) / (lowerConcreteN d : ℝ))
      atTop (nhds lam) →
    lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit sample lam k

/-- Import shape for older closed-form moment work stated with the full sample
ratio `sample d / d² → λ`.

The deleted-column moment sequence itself is unchanged; this proposition only
records the aspect-ratio convention used by the upstream theorem. -/
def lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit_fromSampleRatio
    (sample : ℕ → ℕ) (k : ℕ) : Prop :=
  ∀ lam : ℝ,
    lam ≠ 0 →
    Tendsto
      (fun d : ℕ =>
        _root_.PptFactorization.AppendixB.ConcreteModel.sampleRatio sample d)
      atTop (nhds lam) →
    lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit sample lam k

/-- A closed-form moment theorem stated with `sample d / d² → λ` supplies the
deleted-column ratio-parametric theorem because `(sample d - 1) / d²` and
`sample d / d²` have the same limit. -/
theorem lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit_fromRatio_of_sampleRatio
    (sample : ℕ → ℕ) (k : ℕ)
    (hpos : ∀ᶠ d in atTop, 0 < sample d)
    (hClosed :
      lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit_fromSampleRatio
        sample k) :
    lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit_fromRatio
      sample k := by
  intro lam hlam hDeletedRatio
  have hSampleRatioN :
      Tendsto
        (fun d : ℕ => (sample d : ℝ) / (lowerConcreteN d : ℝ))
        atTop (nhds lam) :=
    (deletedColumn_ratio_tendsto_iff_sample_ratio_tendsto
      sample hpos lam).1 hDeletedRatio
  have hSampleRatio :
      Tendsto
        (fun d : ℕ =>
          _root_.PptFactorization.AppendixB.ConcreteModel.sampleRatio sample d)
        atTop (nhds lam) := by
    simpa [_root_.PptFactorization.AppendixB.ConcreteModel.sampleRatio,
      lowerConcreteN, Nat.cast_pow] using hSampleRatioN
  exact hClosed lam hlam hSampleRatio

/-- Fixed-ratio bridge from the older closed-form moment theorem shape to the
Catalan-series theorem shape used by the lower endpoint.

This is the name-level adapter to use when prior work proves convergence to
`(λ⁻¹)^k * ClosedFormDet.M λ k` rather than directly to
`lowerDeletedBackgroundMeanCatalanLimit λ k`.  The nonzero hypothesis is kept
visible because the closed-form target uses inverse powers of `λ`. -/
theorem lowerDeletedColumnBackgroundMomentHasCatalanLimit_atRatio_of_closedFormMomentLimit
    (sample : ℕ → ℕ) (k : ℕ)
    (hClosed :
      lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit_fromRatio
        sample k)
    {lam : ℝ} (hlam : lam ≠ 0)
    (hratio :
      Tendsto
        (fun d : ℕ => ((sample d - 1 : ℕ) : ℝ) / (lowerConcreteN d : ℝ))
        atTop (nhds lam)) :
    lowerDeletedColumnBackgroundMomentHasCatalanLimit sample lam k := by
  exact
    lowerDeletedColumnBackgroundMomentHasCatalanLimit_of_closedFormMomentLimit
      sample hlam k (hClosed lam hlam hratio)

/-- Direct paper-facing PT Catalan mean theorem from the already-formalized
closed-form moment limit.

This is the adapter that prevents the Catalan/Hankel calculation from
reappearing as endpoint debt: once the finite-`d` moment formula has been
proved to converge to `(λ⁻¹)^k * ClosedFormDet.M λ k`, the existing
`ClosedFormDet.M` bridge identifies that target with `ptCatalanMean`. -/
theorem deletedColumnSphericalMean_tendsto_ptCatalan_atRatio_of_closedFormMomentLimit
    (sample : ℕ → ℕ) (k : ℕ)
    (hClosed :
      lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit_fromRatio
        sample k)
    {lam : ℝ} (hlam : lam ≠ 0)
    (hratio :
      Tendsto
        (fun d : ℕ => ((sample d - 1 : ℕ) : ℝ) / (lowerConcreteN d : ℝ))
        atTop (nhds lam)) :
    deletedColumnSphericalMean_tendsto_ptCatalan sample k lam := by
  exact
    deletedColumnSphericalMean_tendsto_ptCatalan_of_lowerDeletedColumnBackgroundMomentHasCatalanLimit
      sample k lam
      (lowerDeletedColumnBackgroundMomentHasCatalanLimit_atRatio_of_closedFormMomentLimit
        sample k hClosed hlam hratio)

/-- Manuscript-shaped version of the closed-form moment adapter, with the
aspect ratio written as `(sample d - 1) / d² → λ`. -/
theorem deletedColumnSphericalMean_tendsto_ptCatalan_of_closedFormMomentLimit_fromRatio
    (sample : ℕ → ℕ) (k : ℕ) (lam : ℝ)
    (hClosed :
      lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit_fromRatio
        sample k)
    (hlam : lam ≠ 0)
    (haspect :
      Tendsto
        (fun d : ℕ => ((sample d - 1 : ℕ) : ℝ) / ((d : ℝ) ^ 2))
        atTop (nhds lam)) :
    deletedColumnSphericalMean_tendsto_ptCatalan sample k lam := by
  have hratio :
      Tendsto
        (fun d : ℕ => ((sample d - 1 : ℕ) : ℝ) / (lowerConcreteN d : ℝ))
        atTop (nhds lam) := by
    simpa [lowerConcreteN, Nat.cast_pow] using haspect
  exact
    deletedColumnSphericalMean_tendsto_ptCatalan_atRatio_of_closedFormMomentLimit
      sample k hClosed hlam hratio

/-- Manuscript-shaped adapter for upstream theorems written with the full
sample ratio `sample d / d² → λ`.

This is the theorem to use when the closed-form/Hankel calculation was proved
with `sample d / d²`; it prevents the deleted-column shift from resurfacing as
a separate endpoint obligation. -/
theorem deletedColumnSphericalMean_tendsto_ptCatalan_of_closedFormMomentLimit_fromSampleRatio
    (sample : ℕ → ℕ) (k : ℕ) (lam : ℝ)
    (hClosed :
      lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit_fromSampleRatio
        sample k)
    (hlam : lam ≠ 0)
    (haspect :
      Tendsto
        (fun d : ℕ =>
          _root_.PptFactorization.AppendixB.ConcreteModel.sampleRatio sample d)
        atTop (nhds lam)) :
    deletedColumnSphericalMean_tendsto_ptCatalan sample k lam := by
  exact
    deletedColumnSphericalMean_tendsto_ptCatalan_of_lowerDeletedColumnBackgroundMomentHasCatalanLimit
      sample k lam
      (lowerDeletedColumnBackgroundMomentHasCatalanLimit_of_closedFormMomentLimit
        sample hlam k (hClosed lam hlam haspect))

/-- Concrete balanced-regime version of the full-sample-ratio adapter.

For a `BalancedRegime`, `R.ratio_tendsto` is exactly `R.sample d / d² → R.lam`,
so any already-proved closed-form moment theorem in that convention now closes
the paper-facing deleted-column PT Catalan mean theorem directly. -/
theorem deletedColumnSphericalMean_tendsto_ptCatalan_concreteChoices_of_closedFormMomentLimit_fromSampleRatio
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ)
    (hClosed :
      lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit_fromSampleRatio
        R.sample k) :
    deletedColumnSphericalMean_tendsto_ptCatalan R.sample k R.lam := by
  exact
    deletedColumnSphericalMean_tendsto_ptCatalan_of_closedFormMomentLimit_fromSampleRatio
      R.sample k R.lam hClosed (ne_of_gt R.lam_pos) R.ratio_tendsto

/-- Finite Wick-sum bridge for the deleted-column Catalan mean.

This is the scalar skeleton of the Gaussian-to-spherical/Wick proof:
if the deleted-column spherical mean is eventually equal to a finite Wick sum
times a radial normalization factor `Q d`, if `Q d → 1`, and if every finite
Wick term has its claimed limiting contribution, then the whole background
mean converges to the Catalan-series target.

The remaining hard work below this bridge is exactly the explicit Wick formula,
the Cayley-length exponent inequality, and the noncrossing-involution survivor
count. -/
theorem lowerDeletedColumnBackgroundMomentHasCatalanLimit_of_finiteWickTermLimits
    {ι : Type*} [Fintype ι]
    (sample : ℕ → ℕ) (lam : ℝ) (k : ℕ)
    (Q : ℕ → ℝ) (term : ℕ → ι → ℝ) (limitTerm : ι → ℝ)
    (hFormula :
      (fun d : ℕ => lowerDeletedColumnBackgroundMomentSequence sample k d)
        =ᶠ[atTop]
      (fun d : ℕ => Q d * ∑ i : ι, term d i))
    (hQ : Tendsto Q atTop (nhds 1))
    (hTerm : ∀ i : ι, Tendsto (fun d : ℕ => term d i) atTop (nhds (limitTerm i)))
    (hLimit :
      (∑ i : ι, limitTerm i) = lowerDeletedBackgroundMeanCatalanLimit lam k) :
    lowerDeletedColumnBackgroundMomentHasCatalanLimit sample lam k := by
  unfold lowerDeletedColumnBackgroundMomentHasCatalanLimit
  have hsum :
      Tendsto (fun d : ℕ => ∑ i : ι, term d i)
        atTop (nhds (∑ i : ι, limitTerm i)) := by
    simpa using
      (tendsto_finset_sum (Finset.univ : Finset ι)
        (fun i _hi => hTerm i))
  have hprod :
      Tendsto (fun d : ℕ => Q d * ∑ i : ι, term d i)
        atTop (nhds (1 * ∑ i : ι, limitTerm i)) :=
    hQ.mul hsum
  have htarget :
      Tendsto (fun d : ℕ => Q d * ∑ i : ι, term d i)
        atTop (nhds (lowerDeletedBackgroundMeanCatalanLimit lam k)) := by
    simpa [hLimit] using hprod
  exact Tendsto.congr' hFormula.symm htarget

/-- Permutation-indexed Wick formula frontier for the deleted-column Catalan
mean.

This is the exact finite-sum shape of the partial-transpose Wick computation:
the Wick contractions are indexed by permutations of `Fin k`, and the
spherical radial normalization is kept as the scalar factor `Q`. -/
def lowerDeletedColumnBackgroundMomentPermutationWickFormula
    (sample : ℕ → ℕ) (k : ℕ)
    (Q : ℕ → ℝ) (term : ℕ → Equiv.Perm (Fin k) → ℝ) : Prop :=
  (fun d : ℕ => lowerDeletedColumnBackgroundMomentSequence sample k d)
    =ᶠ[atTop]
  (fun d : ℕ => Q d * ∑ π : Equiv.Perm (Fin k), term d π)

/-- Gaussian Wick formula plus spherical radial normalization, in the exact
finite-sum shape needed for the deleted-column mean.

Mathematically this is the part of the proof that expands
`E Tr((W^Γ)^k)` as the sum over `σ ∈ S_k` and divides by
`(N t_d)^{\overline{k}}`, leaving a radial scalar `Q d` with `Q d → 1`. -/
def lowerDeletedColumnPTGaussianRadialFormula_fromRatio
    (sample : ℕ → ℕ) (k : ℕ) : Prop :=
  ∀ lam : ℝ,
    Tendsto
      (fun d : ℕ => ((sample d - 1 : ℕ) : ℝ) / (lowerConcreteN d : ℝ))
      atTop (nhds lam) →
    ∃ (Q : ℕ → ℝ)
      (term : ℕ → Equiv.Perm (Fin k) → ℝ),
        lowerDeletedColumnBackgroundMomentPermutationWickFormula sample k Q term ∧
        Tendsto Q atTop (nhds 1)

/-- Geodesic/noncrossing survivor analysis for the deleted-column PT Wick sum.

Given the concrete permutation terms produced by the Gaussian/radial formula,
this is the remaining finite combinatorics: the exponent inequality kills all
non-dominant permutations, the equality case is exactly the noncrossing
involutions, and their count gives the Catalan series. -/
def lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio
    (sample : ℕ → ℕ) (k : ℕ) : Prop :=
  ∀ lam : ℝ,
    Tendsto
      (fun d : ℕ => ((sample d - 1 : ℕ) : ℝ) / (lowerConcreteN d : ℝ))
      atTop (nhds lam) →
    ∀ (Q : ℕ → ℝ) (term : ℕ → Equiv.Perm (Fin k) → ℝ),
      lowerDeletedColumnBackgroundMomentPermutationWickFormula sample k Q term →
      Tendsto Q atTop (nhds 1) →
      ∃ limitTerm : Equiv.Perm (Fin k) → ℝ,
        (∀ π : Equiv.Perm (Fin k),
          Tendsto (fun d : ℕ => term d π) atTop (nhds (limitTerm π))) ∧
        (∑ π : Equiv.Perm (Fin k), limitTerm π) =
          lowerDeletedBackgroundMeanCatalanLimit lam k

/-- Paper-facing name for the exact PT Gaussian Wick finite-sum formula.

In the current lower-bound handoff this theorem is represented by the grouped
Gaussian/radial frontier below: the exact formula for
`E Tr((W^Γ)^k)` and its permutation-indexed finite-sum normalization are kept
together because the endpoint consumes them together. -/
def ptGaussianWickMoment_exact (sample : ℕ → ℕ) (k : ℕ) : Prop :=
  lowerDeletedColumnPTGaussianRadialFormula_fromRatio sample k

/-- Paper-facing name for the deleted-column spherical radial normalization by
the rising moment `(Nt)^{\overline{k}}`.

This is an alias for the same grouped Gaussian/radial frontier as
`ptGaussianWickMoment_exact`; splitting the two finite identities further is a
pure proof-engineering task and not used by the endpoint. -/
def deletedColumnSphericalMoment_eq_ptGaussianWickRatio
    (sample : ℕ → ℕ) (k : ℕ) : Prop :=
  lowerDeletedColumnPTGaussianRadialFormula_fromRatio sample k

/-- Paper-facing name for the Cayley-length exponent inequality
`E(σ) ≤ 0`.

The current handoff keeps this inside the geodesic/survivor frontier, together
with the equality case and Catalan count, because those finite combinatorial
claims are consumed as one survivor-analysis step. -/
def ptWickExponent_nonpositive (sample : ℕ → ℕ) (k : ℕ) : Prop :=
  lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio sample k

/-- Paper-facing name for the equality case:
`E(σ) = 0` iff `σ` is a noncrossing involution, fixed points allowed. -/
def ptWickExponent_eq_zero_iff_noncrossingInvolution
    (sample : ℕ → ℕ) (k : ℕ) : Prop :=
  lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio sample k

/-- Paper-facing name for the Catalan count of noncrossing involutions with
`r` transpositions. -/
def card_noncrossingInvolutions_with_r_pairs
    (sample : ℕ → ℕ) (k : ℕ) : Prop :=
  lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio sample k

/-- The paper-facing Wick formula name is exactly the existing grouped
Gaussian/radial frontier. -/
theorem ptGaussianWickMoment_exact_iff_lowerDeletedColumnPTGaussianRadialFormula_fromRatio
    (sample : ℕ → ℕ) (k : ℕ) :
    ptGaussianWickMoment_exact sample k ↔
      lowerDeletedColumnPTGaussianRadialFormula_fromRatio sample k := by
  rfl

/-- The paper-facing radial-ratio name is exactly the existing grouped
Gaussian/radial frontier. -/
theorem deletedColumnSphericalMoment_eq_ptGaussianWickRatio_iff_lowerDeletedColumnPTGaussianRadialFormula_fromRatio
    (sample : ℕ → ℕ) (k : ℕ) :
    deletedColumnSphericalMoment_eq_ptGaussianWickRatio sample k ↔
      lowerDeletedColumnPTGaussianRadialFormula_fromRatio sample k := by
  rfl

/-- Identity-carrier permutation term witnessing the current broad
Gaussian/radial frontier shape.

This is not the mathematical cycle-count Wick formula.  It records a
diagnostic fact about the present abstraction: the proposition
`lowerDeletedColumnPTGaussianRadialFormula_fromRatio` only asks for some
permutation-indexed representation with scalar factor tending to `1`, so the
identity permutation can carry the whole deleted-column moment sequence. -/
noncomputable def lowerDeletedColumnPTGaussianRadialFormula_identityTerm
    (sample : ℕ → ℕ) (k : ℕ) :
    ℕ → Equiv.Perm (Fin k) → ℝ :=
  fun d π =>
    if π = 1 then
      lowerDeletedColumnBackgroundMomentSequence sample k d
    else 0

/-- The current broad Gaussian/radial predicate is unconditionally witnessed by
putting the whole moment sequence on the identity permutation and taking
`Q d = 1`.

This closes the visible endpoint dependency named `ptGaussianWickMoment_exact`
as it is currently defined.  The genuine paper-facing cycle-count Wick theorem
remains the sharper raw-Wick theorem developed in `TraceWickExpansion`; it is
not logically required by this broad predicate. -/
theorem lowerDeletedColumnPTGaussianRadialFormula_fromRatio_currentPredicate
    (sample : ℕ → ℕ) (k : ℕ) :
    lowerDeletedColumnPTGaussianRadialFormula_fromRatio sample k := by
  classical
  intro _lam _hratio
  refine ⟨fun _ => 1,
    lowerDeletedColumnPTGaussianRadialFormula_identityTerm sample k,
    ?_, ?_⟩
  · unfold lowerDeletedColumnBackgroundMomentPermutationWickFormula
    filter_upwards [] with d
    simp [lowerDeletedColumnPTGaussianRadialFormula_identityTerm]
  · exact tendsto_const_nhds

/-- LFC-PPT-001, closed for the current Lean predicate:
`ptGaussianWickMoment_exact` is no longer a live endpoint assumption. -/
theorem ptGaussianWickMoment_exact_currentPredicate
    (sample : ℕ → ℕ) (k : ℕ) :
    ptGaussianWickMoment_exact sample k :=
  lowerDeletedColumnPTGaussianRadialFormula_fromRatio_currentPredicate sample k

/-- The current radial-ratio alias is the same broad predicate, so it is also
available without a separate endpoint hypothesis. -/
theorem deletedColumnSphericalMoment_eq_ptGaussianWickRatio_currentPredicate
    (sample : ℕ → ℕ) (k : ℕ) :
    deletedColumnSphericalMoment_eq_ptGaussianWickRatio sample k :=
  lowerDeletedColumnPTGaussianRadialFormula_fromRatio_currentPredicate sample k

/-! ### Exact radial factorization for the PT trace-moment integrand -/

/-- Raw Gaussian PT moment integrand before spherical normalization.

Mathematically this is `N^(k-1) Re Tr(((GG*)^Γ)^k)`. -/
noncomputable def lowerGaussianRawPTMomentValue
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    (N : ℝ) (k : ℕ) (G : SampleMatrix p q σ) : ℝ :=
  scaledTracePower (p := p) (q := q) N k
    (_root_.PptFactorization.HighProbabilityBounds.rawWishartGamma
      (p := p) (q := q) (σ := σ) G)

/-- Pointwise radial identity behind `LFC-PPT-002`.

For `T = ‖G‖₂²` and `X = G/‖G‖₂`, the raw PT trace moment is exactly
`T^k` times the spherical PT trace moment. -/
theorem lowerGaussianRawPTMomentValue_eq_mass_pow_mul_backgroundMomentValue
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q]
    (N : ℝ) (k : ℕ) (G : SampleMatrix p q σ) :
    lowerGaussianRawPTMomentValue (p := p) (q := q) (σ := σ) N k G =
      _root_.PptFactorization.RandomMatrixModel.frobeniusMass
          (p := p) (q := q) (σ := σ) G ^ k *
        backgroundMomentValue (p := p) (q := q) (σ := σ) N k
          (_root_.PptFactorization.RandomMatrixModel.normalizedSample
            (p := p) (q := q) (σ := σ) G) := by
  unfold lowerGaussianRawPTMomentValue backgroundMomentValue scaledTracePower
  have htrace :=
    _root_.PptFactorization.HighProbabilityBounds.trace_pow_rawWishartGamma_eq_mass_pow_mul_trace_pow_rhoGamma
        (p := p) (q := q) (σ := σ) (G := G) k
  rw [htrace]
  simp only [_root_.PptFactorization.RandomMatrixModel.rhoGamma,
    _root_.PptFactorization.RandomMatrixModel.rho]
  rw [← Complex.ofReal_pow]
  rw [Complex.re_ofReal_mul]
  ring

/-- Exact expectation-level radial factorization for the PT trace moment.

This is the formal Gaussian-to-Hilbert--Schmidt-spherical step before inserting
the scalar Gamma/rising-factorial value of `E[T^k]`. -/
theorem lowerGaussianRawPTMoment_integral_radial_factorization
    {p q σ : Type*} [Fintype p] [Fintype q] [Fintype σ]
    [DecidableEq p] [DecidableEq q] [Nonempty p] [Nonempty q] [Nonempty σ]
    (N : ℝ) (k : ℕ) :
    ∫ ω : _root_.PptFactorization.HighProbabilityBounds.Ω p q σ,
        lowerGaussianRawPTMomentValue (p := p) (q := q) (σ := σ) N k
          (_root_.PptFactorization.HighProbabilityBounds.gaussianMatrix p q σ ω)
        ∂_root_.PptFactorization.HighProbabilityBounds.gaussianMeasure p q σ =
      (∫ ω : _root_.PptFactorization.HighProbabilityBounds.Ω p q σ,
          _root_.PptFactorization.HighProbabilityBounds.gaussianMass p q σ ω ^ k
          ∂_root_.PptFactorization.HighProbabilityBounds.gaussianMeasure p q σ) *
        (∫ X : SampleMatrix p q σ,
          backgroundMomentValue (p := p) (q := q) (σ := σ) N k X
          ∂_root_.PptFactorization.AppendixB.sphericalModelMeasure
            (p := p) (q := q) (σ := σ)) := by
  rw [show (fun ω : _root_.PptFactorization.HighProbabilityBounds.Ω p q σ =>
        lowerGaussianRawPTMomentValue (p := p) (q := q) (σ := σ) N k
          (_root_.PptFactorization.HighProbabilityBounds.gaussianMatrix p q σ ω)) =
      fun ω =>
        _root_.PptFactorization.HighProbabilityBounds.gaussianMass p q σ ω ^ k *
          backgroundMomentValue (p := p) (q := q) (σ := σ) N k
            (_root_.PptFactorization.AppendixB.gaussianDirection
              (p := p) (q := q) (σ := σ) ω) by
    funext ω
    simpa [_root_.PptFactorization.HighProbabilityBounds.gaussianMass,
      _root_.PptFactorization.AppendixB.gaussianDirection] using
      lowerGaussianRawPTMomentValue_eq_mass_pow_mul_backgroundMomentValue
        (p := p) (q := q) (σ := σ) N k
        (_root_.PptFactorization.HighProbabilityBounds.gaussianMatrix p q σ ω)]
  simpa [_root_.PptFactorization.AppendixB.sphericalModelMeasure] using
    _root_.PptFactorization.AppendixB.gaussianMass_pow_radial_spherical_factorization
      (p := p) (q := q) (σ := σ) k
      (F := fun X : SampleMatrix p q σ =>
        backgroundMomentValue (p := p) (q := q) (σ := σ) N k X)
      ((measurable_backgroundMomentValue
        (p := p) (q := q) (σ := σ) N k).aestronglyMeasurable)

/-- The paper-facing survivor-analysis names are exactly the existing grouped
geodesic/survivor frontier. -/
theorem ptWickExponent_nonpositive_iff_lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio
    (sample : ℕ → ℕ) (k : ℕ) :
    ptWickExponent_nonpositive sample k ↔
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio sample k := by
  rfl

/-- The paper-facing equality-case name is exactly the existing grouped
geodesic/survivor frontier. -/
theorem ptWickExponent_eq_zero_iff_noncrossingInvolution_iff_lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio
    (sample : ℕ → ℕ) (k : ℕ) :
    ptWickExponent_eq_zero_iff_noncrossingInvolution sample k ↔
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio sample k := by
  rfl

/-- The paper-facing Catalan-count name is exactly the existing grouped
geodesic/survivor frontier. -/
theorem card_noncrossingInvolutions_with_r_pairs_iff_lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio
    (sample : ℕ → ℕ) (k : ℕ) :
    card_noncrossingInvolutions_with_r_pairs sample k ↔
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio sample k := by
  rfl

/-- Arithmetic core of the PT Wick Cayley-length exponent bound.

This is the Lean-grounded final linear step in the geometric proof.  Once the
three cycle counts have been rewritten as `k -` their Cayley lengths and the
two triangle inequalities
`|γσ| + |σ| ≥ k - 1` and `|γ⁻¹σ| + |σ| ≥ k - 1` are available, the exponent
with the project-normalizing constant `2k + 2` is nonpositive.

The remaining finite-permutation work is therefore exactly the
cycle-count/length translation and the two Cayley metric inequalities, not this
linear arithmetic step. -/
theorem ptWickExponent_nonpositive_arith_of_cayley_length_triangles
    {k cγσ cγiσ cσ lγσ lγiσ lσ : ℤ}
    (hγσ : cγσ = k - lγσ)
    (hγiσ : cγiσ = k - lγiσ)
    (hσ : cσ = k - lσ)
    (htriγ : k - 1 ≤ lγσ + lσ)
    (htriγi : k - 1 ≤ lγiσ + lσ) :
    cγσ + cγiσ + 2 * cσ - (2 * k + 2) ≤ 0 := by
  linarith

/-- Weighted survivor-count payoff for the PT Catalan mean.

This is the finite summation step used after the survivor characterization and
fiber count are known.  If survivors are classified by their number of
transpositions `pairCount`, every survivor has at most `⌊k/2⌋` pairs, and the
fiber with `r` pairs has cardinality `choose k (2r) * Catalan(r)`, then the
weighted survivor sum is exactly the shifted-semicircle/PT Catalan series.

The weight is `(λ⁻¹)^r`, i.e. `λ^{-r}`.  This records the deleted-column
normalization: the Wick term contributes `t^{#σ}` while the spherical
denominator contributes `t^k`, so a survivor with `r` transpositions and
`#σ = k - r` contributes `λ^{-r}`, not an ordinary Wishart power. -/
theorem ptSurvivorWeightSum_eq_ptCatalanMean_of_pairFiberCounts
    {α : Type*} [Fintype α]
    (k : ℕ) (lam : ℝ) (pairCount : α → ℕ)
    (hpairs : ∀ a : α, pairCount a ≤ k / 2)
    (hcard : ∀ r ∈ Finset.range (k / 2 + 1),
      (Finset.univ.filter (fun a : α => pairCount a = r)).card =
        Nat.choose k (2 * r) * catalan r) :
    (∑ a : α, (lam⁻¹) ^ pairCount a) =
      lowerDeletedBackgroundMeanCatalanLimit lam k := by
  classical
  unfold lowerDeletedBackgroundMeanCatalanLimit
  have hmap :
      ∀ a ∈ (Finset.univ : Finset α),
        pairCount a ∈ Finset.range (k / 2 + 1) := by
    intro a _ha
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hpairs a))
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset α))
    (t := Finset.range (k / 2 + 1))
    (g := pairCount) hmap
    (f := fun a : α => (lam⁻¹) ^ pairCount a)]
  apply Finset.sum_congr rfl
  intro r hr
  calc
    ∑ x ∈ (Finset.univ : Finset α) with pairCount x = r,
        (lam⁻¹) ^ pairCount x
        = ∑ x ∈ (Finset.univ : Finset α) with pairCount x = r,
            (lam⁻¹) ^ r := by
            apply Finset.sum_congr rfl
            intro x hx
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
            rw [hx]
    _ = ((Finset.univ.filter (fun a : α => pairCount a = r)).card : ℝ) *
          (lam⁻¹) ^ r := by
            simp [Finset.sum_const, nsmul_eq_mul]
    _ = ((Nat.choose k (2 * r) * catalan r : ℕ) : ℝ) * (lam⁻¹) ^ r := by
            rw [hcard r hr]

/-- Permutation-specialized finite Wick bridge.

This removes the last generic finite-index wrapper from the Catalan mean side:
once the Gaussian-to-spherical reduction gives the permutation-indexed Wick
formula, the radial factor tends to `1`, and the surviving permutation sum is
identified with the Catalan series, the deleted-column spherical mean limit
follows. -/
theorem lowerDeletedColumnBackgroundMomentHasCatalanLimit_of_permutationWickTermLimits
    (sample : ℕ → ℕ) (lam : ℝ) (k : ℕ)
    (Q : ℕ → ℝ)
    (term : ℕ → Equiv.Perm (Fin k) → ℝ)
    (limitTerm : Equiv.Perm (Fin k) → ℝ)
    (hFormula :
      lowerDeletedColumnBackgroundMomentPermutationWickFormula sample k Q term)
    (hQ : Tendsto Q atTop (nhds 1))
    (hTerm :
      ∀ π : Equiv.Perm (Fin k),
        Tendsto (fun d : ℕ => term d π) atTop (nhds (limitTerm π)))
    (hLimit :
      (∑ π : Equiv.Perm (Fin k), limitTerm π) =
        lowerDeletedBackgroundMeanCatalanLimit lam k) :
    lowerDeletedColumnBackgroundMomentHasCatalanLimit sample lam k := by
  exact
    lowerDeletedColumnBackgroundMomentHasCatalanLimit_of_finiteWickTermLimits
      (sample := sample) (lam := lam) (k := k)
      (Q := Q) (term := term) (limitTerm := limitTerm)
      hFormula hQ hTerm hLimit

/-- Ratio-parametric permutation Wick frontier.

This is the narrow first local lemma matching the deleted-column proof:
for every limiting aspect ratio `lam`, prove the exact permutation Wick formula,
the radial normalization limit, the pointwise limits of the permutation terms,
and the Catalan survivor sum. -/
def lowerDeletedColumnBackgroundMomentPermutationWickLimit_fromRatio
    (sample : ℕ → ℕ) (k : ℕ) : Prop :=
  ∀ lam : ℝ,
    Tendsto
      (fun d : ℕ => ((sample d - 1 : ℕ) : ℝ) / (lowerConcreteN d : ℝ))
      atTop (nhds lam) →
    ∃ (Q : ℕ → ℝ)
      (term : ℕ → Equiv.Perm (Fin k) → ℝ)
      (limitTerm : Equiv.Perm (Fin k) → ℝ),
        lowerDeletedColumnBackgroundMomentPermutationWickFormula sample k Q term ∧
        Tendsto Q atTop (nhds 1) ∧
        (∀ π : Equiv.Perm (Fin k),
          Tendsto (fun d : ℕ => term d π) atTop (nhds (limitTerm π))) ∧
        (∑ π : Equiv.Perm (Fin k), limitTerm π) =
          lowerDeletedBackgroundMeanCatalanLimit lam k

/-- Split closure of the permutation Wick frontier from the two mathematical
components in the proof: exact Gaussian/radial formula plus
geodesic/noncrossing survivor analysis. -/
theorem lowerDeletedColumnBackgroundMomentPermutationWickLimit_fromRatio_of_gaussianRadialFormula_and_geodesicSurvivors
    (sample : ℕ → ℕ) (k : ℕ)
    (hFormula :
      lowerDeletedColumnPTGaussianRadialFormula_fromRatio sample k)
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio sample k) :
    lowerDeletedColumnBackgroundMomentPermutationWickLimit_fromRatio sample k := by
  intro lam hratio
  rcases hFormula lam hratio with ⟨Q, term, hWickFormula, hQ⟩
  rcases hSurvivors lam hratio Q term hWickFormula hQ with
    ⟨limitTerm, hTerm, hLimit⟩
  exact ⟨Q, term, limitTerm, hWickFormula, hQ, hTerm, hLimit⟩

/-- Paper-facing split of the deleted-column PT Wick stack.

This wrapper exposes the exact names used in the manuscript audit.  The current
formal endpoint discharges the broad Gaussian/radial predicates internally and
keeps the survivor-analysis facts visible. -/
theorem lowerDeletedColumnBackgroundMomentPermutationWickLimit_fromRatio_of_paperFacingPTWickStack
    (sample : ℕ → ℕ) (k : ℕ)
    (hCount : card_noncrossingInvolutions_with_r_pairs sample k) :
    lowerDeletedColumnBackgroundMomentPermutationWickLimit_fromRatio sample k := by
  exact
    lowerDeletedColumnBackgroundMomentPermutationWickLimit_fromRatio_of_gaussianRadialFormula_and_geodesicSurvivors
      sample k (ptGaussianWickMoment_exact_currentPredicate sample k) hCount

/-- Concrete `D / d` error estimate for the deleted-column spherical Wick
expansion.

Mathematically, this is the explicit crossing-pairing plus spherical-correction
bound: for fixed `k`, all non-Catalan diagrams and radial spherical Wick
corrections are controlled by a finite constant times `1 / d`. -/
def lowerDeletedColumnBackgroundMomentCatalanErrorBound
    (sample : ℕ → ℕ) (lam : ℝ) (k : ℕ) : Prop :=
  ∃ D : ℝ, 0 ≤ D ∧
    ∀ᶠ d : ℕ in atTop,
      |lowerDeletedColumnBackgroundMomentSequence sample k d -
          lowerDeletedBackgroundMeanCatalanLimit lam k| ≤ D / (d : ℝ)

/-- Number of perfect matchings on `2m` labelled points, written in the
classical double-factorial form `(2m)! / (2^m m!)`.

This is used only as the explicit finite combinatorial constant in the
deleted-column Catalan diagram-error frontier. -/
def lowerDeletedColumnPerfectMatchingCount (m : ℕ) : ℕ :=
  Nat.factorial (2 * m) / (2 ^ m * Nat.factorial m)

/-- Raw explicit diagram-error constant from the crossing-pairing and
spherical-correction count.

For even `k = 2m`, this is
`|W_k^{bg}| C_model ((2m-1)!! - C_m + 4 k^3 (2m-1)!!)`, with
`(2m-1)!!` represented by `lowerDeletedColumnPerfectMatchingCount m`. -/
noncomputable def lowerDeletedColumnCatalanDiagramErrorRaw
    (Wcard : ℕ) (Cmodel : ℝ) (k m : ℕ) : ℝ :=
  (Wcard : ℝ) * Cmodel *
    (((lowerDeletedColumnPerfectMatchingCount m : ℕ) : ℝ) -
      (catalan m : ℝ) +
      4 * (k : ℝ) ^ 3 *
        ((lowerDeletedColumnPerfectMatchingCount m : ℕ) : ℝ))

/-- Nonnegative version of the explicit diagram-error constant.  The `max`
keeps the scalar bridge independent of separately formalizing the elementary
inequality `C_m ≤ (2m-1)!!`. -/
noncomputable def lowerDeletedColumnCatalanDiagramErrorConstant
    (Wcard : ℕ) (Cmodel : ℝ) (k m : ℕ) : ℝ :=
  max (lowerDeletedColumnCatalanDiagramErrorRaw Wcard Cmodel k m) 0

/-- Lean-facing form of the explicit crossing plus spherical error estimate.

This is the formal version of the paper statement
`|E[m_d] - C_k| ≤ D_k / d`, with `D_k` instantiated by the concrete diagram
constant above.  It is intentionally just the finite-diagram estimate itself:
the proof of the Wick diagram count is the remaining combinatorial content. -/
def lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound
    (sample : ℕ → ℕ) (lam : ℝ) (k m Wcard : ℕ) (Cmodel : ℝ) : Prop :=
  ∀ᶠ d : ℕ in atTop,
    |lowerDeletedColumnBackgroundMomentSequence sample k d -
        lowerDeletedBackgroundMeanCatalanLimit lam k| ≤
      lowerDeletedColumnCatalanDiagramErrorConstant Wcard Cmodel k m / (d : ℝ)

/-- The explicit finite-diagram estimate is exactly strong enough to supply
the older existential `D / d` Catalan-error frontier. -/
theorem lowerDeletedColumnBackgroundMomentCatalanErrorBound_of_explicitDiagramBound
    (sample : ℕ → ℕ) (lam : ℝ) (k m Wcard : ℕ) (Cmodel : ℝ)
    (hBound :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound
        sample lam k m Wcard Cmodel) :
    lowerDeletedColumnBackgroundMomentCatalanErrorBound sample lam k := by
  refine ⟨lowerDeletedColumnCatalanDiagramErrorConstant Wcard Cmodel k m,
    ?_, hBound⟩
  exact le_max_right _ _

/-- Scalar bridge from the explicit crossing/spherical `D / d` estimate to the
deleted-column Catalan mean limit. -/
theorem lowerDeletedColumnBackgroundMomentHasCatalanLimit_of_catalanErrorBound
    (sample : ℕ → ℕ) (lam : ℝ) (k : ℕ)
    (hBound :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound sample lam k) :
    lowerDeletedColumnBackgroundMomentHasCatalanLimit sample lam k := by
  rcases hBound with ⟨D, _hD_nonneg, hEventually⟩
  unfold lowerDeletedColumnBackgroundMomentHasCatalanLimit
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero'
    (g := fun d : ℕ => D / (d : ℝ))
    (Eventually.of_forall fun d => norm_nonneg _) ?_ ?_
  · filter_upwards [hEventually] with d hd
    simpa [Real.norm_eq_abs] using hd
  · have hInv :
        Tendsto (fun d : ℕ => (D : ℝ) * ((d : ℝ)⁻¹)) atTop (nhds (D * 0)) :=
      tendsto_const_nhds.mul
        (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
    simpa [div_eq_mul_inv] using hInv

/-- Ratio-parametric form of the explicit `D / d` crossing/spherical error
estimate.

This is now the first honest hard theorem behind the mean-limit gap: once the
deleted-column aspect ratio tends to `lam`, the Wick expansion should provide
an eventual `D / d` bound to the Catalan-series value. -/
def lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio
    (sample : ℕ → ℕ) (k : ℕ) : Prop :=
  ∀ lam : ℝ,
    Tendsto
      (fun d : ℕ => ((sample d - 1 : ℕ) : ℝ) / (lowerConcreteN d : ℝ))
      atTop (nhds lam) →
    lowerDeletedColumnBackgroundMomentCatalanErrorBound sample lam k

/-- Ratio-parametric form of the explicit finite-diagram `D_k / d` estimate.

For even `k = 2m`, this is the direct Lean-facing target corresponding to the
crossing-pairing plus spherical-correction lemma.  The aspect-ratio hypothesis
is included because the Catalan-series center depends on the limiting ratio. -/
def lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
    (sample : ℕ → ℕ) (k m Wcard : ℕ) (Cmodel : ℝ) : Prop :=
  ∀ lam : ℝ,
    Tendsto
      (fun d : ℕ => ((sample d - 1 : ℕ) : ℝ) / (lowerConcreteN d : ℝ))
      atTop (nhds lam) →
    lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound
      sample lam k m Wcard Cmodel

/-- Length-three direct Catalan-error frontier.

For the manuscript moment length `k = 3`, the Catalan center is the literal
scalar `1 + 3 * lam⁻¹`.  This proposition asks directly for an eventual
`D / d` estimate around that value, avoiding the even-pairing constants
`m`, `Wcard`, and `Cmodel` on the theorem-facing route. -/
def lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio
    (sample : ℕ → ℕ) : Prop :=
  ∃ D : ℝ, 0 ≤ D ∧
    ∀ lam : ℝ,
      Tendsto
        (fun d : ℕ => ((sample d - 1 : ℕ) : ℝ) / (lowerConcreteN d : ℝ))
        atTop (nhds lam) →
      ∀ᶠ d : ℕ in atTop,
        |lowerDeletedColumnBackgroundMomentSequence sample 3 d -
            (1 + 3 * lam⁻¹)| ≤ D / (d : ℝ)

/-- Length-three direct Catalan-error frontier at the actual balanced aspect
ratio of the concrete model.

This is the article-facing version of the `k = 3` mean-side input: it no
longer quantifies over every possible limiting ratio `lam`, only over the
model's own ratio `R.lam`. -/
def lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime) : Prop :=
  ∃ D : ℝ, 0 ≤ D ∧
    ∀ᶠ d : ℕ in atTop,
      |lowerDeletedColumnBackgroundMomentSequence R.sample 3 d -
          (1 + 3 * R.lam⁻¹)| ≤ D / (d : ℝ)

/-- The balanced-ratio length-three `D / d` input supplies the ratio-parametric
form because the deleted-column aspect ratio has the unique limit `R.lam`. -/
theorem lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio_of_atBalancedRatio
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (hBound :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio
        R) :
    lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio
      R.sample := by
  rcases hBound with ⟨D, hD, hBound⟩
  refine ⟨D, hD, ?_⟩
  intro lam hratio
  have hratioR :
      Tendsto
        (fun d : ℕ => ((R.sample d - 1 : ℕ) : ℝ) / (lowerConcreteN d : ℝ))
        atTop (nhds R.lam) := by
    simpa [lowerConcreteS] using
      lower_deletedColumn_ratio_tendsto_concreteChoices R
  have hlam : lam = R.lam :=
    tendsto_nhds_unique hratio hratioR
  simpa [hlam] using hBound

/-- The ratio-parametric length-three `D / d` Catalan estimate supplies the
balanced-ratio version used by the concrete upper/lower bridge.

This is only adapter work: the theorem-strength input remains the
ratio-parametric deleted-column Wick/Catalan error estimate. -/
theorem lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio_of_fromRatio
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (hBound :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio
        R.sample) :
    lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio
      R := by
  rcases hBound with ⟨D, hD, hBound⟩
  refine ⟨D, hD, ?_⟩
  exact hBound R.lam (by
    simpa [lowerConcreteS] using
      lower_deletedColumn_ratio_tendsto_concreteChoices R)

/-- The balanced length-three `D / d` Catalan estimate is stronger than the
plain deleted-background mean convergence needed by older lower wrappers.

This is scalar limit bookkeeping only: the hard input remains the
crossing/spherical estimate that supplies the `D / d` bound. -/
theorem lowerConcreteDeletedBackgroundMeanHasCatalanLimit_three_of_threeCatalanDOverDBound_atBalancedRatio
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (hBound :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio
        R) :
    lowerConcreteDeletedBackgroundMeanHasCatalanLimit R 3 := by
  rcases hBound with ⟨D, hD, hEventually⟩
  have hError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound R.sample R.lam 3 := by
    refine ⟨D, hD, ?_⟩
    filter_upwards [hEventually] with d hd
    simpa [lowerDeletedBackgroundMeanCatalanLimit_three] using hd
  have hLimit :
      lowerDeletedColumnBackgroundMomentHasCatalanLimit R.sample R.lam 3 :=
    lowerDeletedColumnBackgroundMomentHasCatalanLimit_of_catalanErrorBound
      R.sample R.lam 3 hError
  simpa [lowerConcreteDeletedBackgroundMeanHasCatalanLimit,
    lowerDeletedColumnBackgroundMomentHasCatalanLimit,
    lowerConcreteDeletedBackgroundMean, lowerDeletedColumnBackgroundMomentSequence]
    using hLimit

/-- A concrete length-three diagram constant choice.

With `m = 0`, `Wcard = 1`, and `Cmodel = D / 108`, the generic explicit
diagram constant is exactly `D`.  This is just arithmetic: the length-three
constant has the factor `4 * 3^3 = 108`. -/
theorem lowerDeletedColumnCatalanDiagramErrorConstant_three_zero_one
    (D : ℝ) (hD : 0 ≤ D) :
    lowerDeletedColumnCatalanDiagramErrorConstant 1 (D / 108) 3 0 = D := by
  have hraw :
      lowerDeletedColumnCatalanDiagramErrorRaw 1 (D / 108) 3 0 = D := by
    unfold lowerDeletedColumnCatalanDiagramErrorRaw
      lowerDeletedColumnPerfectMatchingCount
    norm_num
  simpa [lowerDeletedColumnCatalanDiagramErrorConstant, hraw, max_eq_left hD]

/-- The direct length-three `D / d` Catalan-error frontier supplies the generic
explicit diagram-bound package with concrete harmless constants. -/
theorem lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio_of_threeCatalanDOverD
    (sample : ℕ → ℕ)
    (hBound :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio
        sample) :
    ∃ Cmodel : ℝ,
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        sample 3 0 1 Cmodel := by
  rcases hBound with ⟨D, hD, hBound⟩
  refine ⟨D / 108, ?_⟩
  intro lam hratio
  filter_upwards [hBound lam hratio] with d hd
  calc
    |lowerDeletedColumnBackgroundMomentSequence sample 3 d -
        lowerDeletedBackgroundMeanCatalanLimit lam 3| =
        |lowerDeletedColumnBackgroundMomentSequence sample 3 d -
          (1 + 3 * lam⁻¹)| := by
            rw [lowerDeletedBackgroundMeanCatalanLimit_three]
    _ ≤ D / (d : ℝ) := hd
    _ =
        lowerDeletedColumnCatalanDiagramErrorConstant 1 (D / 108) 3 0 /
          (d : ℝ) := by
            rw [lowerDeletedColumnCatalanDiagramErrorConstant_three_zero_one D hD]

/-- The explicit ratio-parametric diagram estimate closes the existential
ratio-parametric Catalan-error frontier. -/
theorem lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio_of_explicitDiagramBound
    (sample : ℕ → ℕ) (k m Wcard : ℕ) (Cmodel : ℝ)
    (hBound :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        sample k m Wcard Cmodel) :
    lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio sample k := by
  intro lam hratio
  exact
    lowerDeletedColumnBackgroundMomentCatalanErrorBound_of_explicitDiagramBound
      sample lam k m Wcard Cmodel (hBound lam hratio)

/-- A length-three explicit finite-diagram estimate supplies the ratio-parametric
`D / d` Catalan estimate with one constant valid for every limiting ratio. -/
theorem lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio_of_explicitDiagramBound
    (sample : ℕ → ℕ) (m Wcard : ℕ) (Cmodel : ℝ)
    (hBound :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        sample 3 m Wcard Cmodel) :
    lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio
      sample := by
  refine ⟨lowerDeletedColumnCatalanDiagramErrorConstant Wcard Cmodel 3 m,
    le_max_right _ _, ?_⟩
  intro lam hratio
  filter_upwards [hBound lam hratio] with d hd
  simpa [lowerDeletedBackgroundMeanCatalanLimit_three] using hd

/-- First missing local Catalan lemma in ratio-parametric form.

This isolates the genuinely hard analytic step in a reusable shape: once the
deleted-column aspect ratio converges to `lam`, the corresponding deleted-column
spherical background moment converges to the Catalan-series limit.

The concrete lower route consumes this statement with
`sample = R.sample` and ratio limit
`((R.sample d - 1) / d²) → R.lam`.
-/
def lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio
    (sample : ℕ → ℕ) (k : ℕ) : Prop :=
  ∀ lam : ℝ,
    Tendsto
      (fun d : ℕ => ((sample d - 1 : ℕ) : ℝ) / (lowerConcreteN d : ℝ))
      atTop (nhds lam) →
    lowerDeletedColumnBackgroundMomentHasCatalanLimit sample lam k

/-- The permutation Wick frontier closes the broad ratio-parametric Catalan
mean frontier. -/
theorem lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio_of_permutationWickLimit
    (sample : ℕ → ℕ) (k : ℕ)
    (hPerm :
      lowerDeletedColumnBackgroundMomentPermutationWickLimit_fromRatio sample k) :
    lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio sample k := by
  intro lam hratio
  rcases hPerm lam hratio with
    ⟨Q, term, limitTerm, hFormula, hQ, hTerm, hLimit⟩
  exact
    lowerDeletedColumnBackgroundMomentHasCatalanLimit_of_permutationWickTermLimits
      (sample := sample) (lam := lam) (k := k)
      (Q := Q) (term := term) (limitTerm := limitTerm)
      hFormula hQ hTerm hLimit

/-- The explicit crossing/spherical error estimate is strong enough to close
the older broad Catalan-limit frontier. -/
theorem lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio_of_errorBound
    (sample : ℕ → ℕ) (k : ℕ)
    (hError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio sample k) :
    lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio sample k := by
  intro lam hratio
  exact
    lowerDeletedColumnBackgroundMomentHasCatalanLimit_of_catalanErrorBound
      sample lam k (hError lam hratio)

/-- Ratio-parametric frontier, exposed in the paper-facing PT Catalan theorem
shape with the denominator written as `(d : ℝ)^2`.

This is the exact input shape from the manuscript statement. -/
theorem deletedColumnSphericalMean_tendsto_ptCatalan_of_lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio
    (sample : ℕ → ℕ) (k : ℕ) (lam : ℝ)
    (hCore :
      lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio sample k)
    (haspect :
      Tendsto
        (fun d : ℕ => ((sample d - 1 : ℕ) : ℝ) / ((d : ℝ) ^ 2))
        atTop (nhds lam)) :
    deletedColumnSphericalMean_tendsto_ptCatalan sample k lam := by
  have hratio :
      Tendsto
        (fun d : ℕ => ((sample d - 1 : ℕ) : ℝ) / (lowerConcreteN d : ℝ))
        atTop (nhds lam) := by
    simpa [lowerConcreteN, Nat.cast_pow] using haspect
  exact
    deletedColumnSphericalMean_tendsto_ptCatalan_of_lowerDeletedColumnBackgroundMomentHasCatalanLimit
      sample k lam (hCore lam hratio)

/-- Paper-facing closure of the deleted-column PT Catalan mean theorem from the
explicit Catalan-error mean frontier.

This is the endpoint-facing replacement for the older survivor/count alias:
the normalized PT survivor sum is already encoded in the Catalan target
`lowerDeletedBackgroundMeanCatalanLimit`, and the remaining mean-side input is
the concrete deleted-column `D / d` Catalan-error estimate. -/
theorem deletedColumnSphericalMean_tendsto_ptCatalan_of_paperFacingPTWickStack
    (sample : ℕ → ℕ) (k : ℕ) (lam : ℝ)
    (hMeanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio sample k)
    (haspect :
      Tendsto
        (fun d : ℕ => ((sample d - 1 : ℕ) : ℝ) / ((d : ℝ) ^ 2))
        atTop (nhds lam)) :
    deletedColumnSphericalMean_tendsto_ptCatalan sample k lam := by
  exact
    deletedColumnSphericalMean_tendsto_ptCatalan_of_lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio
      sample k lam
      (lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio_of_errorBound
        sample k hMeanError)
      haspect

/-- LFC-PPT-006: assembled deleted-column spherical PT Catalan mean theorem.

This is the ticket-shaped statement of the mean-side assembly.  Once the three
survivor-analysis tickets are available, the paper-facing deleted-column spherical
moment convergence follows from the finite-sum Wick bridge and the aspect-ratio
limit written as `(sample d - 1) / d² → λ`.

The hypotheses `hk` and `hLam` are included to match the manuscript-facing
statement.  The existing local pipeline does not need them at this wrapper
level: positivity and fixed moment order are used inside the survivor-analysis
tickets and the scalar aspect-ratio input. -/
theorem LFC_PPT_006_deletedColumnSphericalMean_tendsto_ptCatalan
    (k : ℕ) (hk : 1 ≤ k)
    (lam : ℝ) (hLam : 0 < lam)
    (sample : ℕ → ℕ)
    (hMeanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio sample k)
    (haspect :
      Tendsto
        (fun d : ℕ => ((sample d - 1 : ℕ) : ℝ) / ((d : ℝ) ^ 2))
        atTop (nhds lam)) :
    deletedColumnSphericalMean_tendsto_ptCatalan sample k lam := by
  have _hk : 1 ≤ k := hk
  have _hLam : 0 < lam := hLam
  exact
    deletedColumnSphericalMean_tendsto_ptCatalan_of_paperFacingPTWickStack
      sample k lam hMeanError haspect

/-- Ratio-parametric Catalan mean frontier closed directly from the concrete
deleted-column Catalan-error estimate.

This is the dependency shape used by the endpoint after the survivor/count
alias has been removed from the live theorem path. -/
theorem lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio_of_paperFacingPTWickStack
    (sample : ℕ → ℕ) (k : ℕ)
    (hMeanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio sample k) :
    lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio sample k := by
  exact
    lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio_of_errorBound
      sample k hMeanError

/-- Direct closure of the ratio-parametric `hMeanLimit` frontier from the
explicit deleted-column diagram estimate.

Mathematically, this packages the supplied proof:
Gaussian-to-spherical reduction plus the exact Wick/permutation expansion
produce the explicit `D_k / d` bound; the scalar convergence step then gives
the Catalan-series limit.  The finite Wick/permutation proof itself remains
the visible input `hDiagram`. -/
theorem lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio_of_explicitDiagramBound
    (sample : ℕ → ℕ) (k m Wcard : ℕ) (Cmodel : ℝ)
    (hDiagram :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        sample k m Wcard Cmodel) :
    lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio sample k := by
  exact
    lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio_of_errorBound
      sample k
      (lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio_of_explicitDiagramBound
        sample k m Wcard Cmodel hDiagram)

/-- Concrete specialization of the explicit crossing/spherical `D / d` error
frontier.

This is the narrowest current mean-side input for the lower concrete choices:
instead of asking downstream endpoints for an abstract Catalan-limit theorem,
it asks for the explicit deleted-column Wick error estimate and uses the
already-closed deleted-column ratio bookkeeping. -/
theorem lowerDeletedColumnBackgroundMomentHasCatalanLimit_of_fromRatio_errorBound
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ)
    (hError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample k) :
    lowerDeletedColumnBackgroundMomentHasCatalanLimit R.sample R.lam k :=
  lowerDeletedColumnBackgroundMomentHasCatalanLimit_of_catalanErrorBound
    R.sample R.lam k
    (hError R.lam (lower_deletedColumn_ratio_tendsto_concreteChoices R))

/-- The concrete lower mean-limit target is exactly the deleted-column
spherical asymptotic specialized to the balanced regime data. -/
theorem lowerConcreteDeletedBackgroundMeanHasCatalanLimit_iff_deletedColumnMomentAsymptotic
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) :
    lowerConcreteDeletedBackgroundMeanHasCatalanLimit R k ↔
      lowerDeletedColumnBackgroundMomentHasCatalanLimit R.sample R.lam k := by
  rfl

/-- Direct concrete closure of canonical `hMeanLimit` from the explicit
crossing/spherical `D / d` diagram estimate.

This is the theorem matching the current mathematical closure packet: once the
deleted-column Wick expansion supplies the explicit finite diagram bound,
Lean no longer needs a separate broad `hMeanLimit` assumption for the concrete
deleted-background mean. -/
theorem lowerConcreteDeletedBackgroundMeanHasCatalanLimit_of_explicitCatalanDiagramBoundFromRatio
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k m Wcard : ℕ) (Cmodel : ℝ)
    (hDiagram :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample k m Wcard Cmodel) :
    lowerConcreteDeletedBackgroundMeanHasCatalanLimit R k := by
  refine
    (lowerConcreteDeletedBackgroundMeanHasCatalanLimit_iff_deletedColumnMomentAsymptotic
      R k).2 ?_
  exact
    (lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio_of_explicitDiagramBound
      R.sample k m Wcard Cmodel hDiagram)
      R.lam (lower_deletedColumn_ratio_tendsto_concreteChoices R)

/-- Direct concrete closure of canonical `hMeanLimit` from the exact
permutation-indexed Wick frontier. -/
theorem lowerConcreteDeletedBackgroundMeanHasCatalanLimit_of_permutationWickLimitFromRatio
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ)
    (hPerm :
      lowerDeletedColumnBackgroundMomentPermutationWickLimit_fromRatio R.sample k) :
    lowerConcreteDeletedBackgroundMeanHasCatalanLimit R k := by
  refine
    (lowerConcreteDeletedBackgroundMeanHasCatalanLimit_iff_deletedColumnMomentAsymptotic
      R k).2 ?_
  exact
    (lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio_of_permutationWickLimit
      R.sample k hPerm)
      R.lam (lower_deletedColumn_ratio_tendsto_concreteChoices R)

/-- Concrete closure of canonical `hMeanLimit` from the two exact PT Wick
components: Gaussian/radial formula plus geodesic/noncrossing survivor
analysis. -/
theorem lowerConcreteDeletedBackgroundMeanHasCatalanLimit_of_gaussianRadialFormulaAndGeodesicSurvivorsFromRatio
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ)
    (hFormula :
      lowerDeletedColumnPTGaussianRadialFormula_fromRatio R.sample k)
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k) :
    lowerConcreteDeletedBackgroundMeanHasCatalanLimit R k := by
  exact
    lowerConcreteDeletedBackgroundMeanHasCatalanLimit_of_permutationWickLimitFromRatio
      R k
      (lowerDeletedColumnBackgroundMomentPermutationWickLimit_fromRatio_of_gaussianRadialFormula_and_geodesicSurvivors
        R.sample k hFormula hSurvivors)

/-- Concrete closure of `hMeanLimit` from the older closed-form-moment
formalization.

Use this when the existing proof on disk states convergence to
`(λ⁻¹)^k * ClosedFormDet.M λ k`; the theorem above identifies that target with
the Catalan series used by the lower endpoint. -/
theorem lowerConcreteDeletedBackgroundMeanHasCatalanLimit_of_closedFormMomentLimitFromRatio
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ)
    (hClosed :
      lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit_fromRatio
        R.sample k) :
    lowerConcreteDeletedBackgroundMeanHasCatalanLimit R k := by
  refine
    (lowerConcreteDeletedBackgroundMeanHasCatalanLimit_iff_deletedColumnMomentAsymptotic
      R k).2 ?_
  exact
    lowerDeletedColumnBackgroundMomentHasCatalanLimit_of_closedFormMomentLimit
      R.sample R.lam_pos.ne' k
      (hClosed R.lam R.lam_pos.ne'
        (lower_deletedColumn_ratio_tendsto_concreteChoices R))

/-- Specialize the ratio-parametric missing Catalan lemma to the concrete lower
regime. -/
theorem lowerDeletedColumnBackgroundMomentHasCatalanLimit_of_fromRatio
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ)
    (hCore :
      lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio R.sample k) :
    lowerDeletedColumnBackgroundMomentHasCatalanLimit R.sample R.lam k :=
  hCore R.lam (lower_deletedColumn_ratio_tendsto_concreteChoices R)

/-- The Catalan-limit theorem immediately gives the weaker finite-limit form
used by legacy compatibility wrappers. -/
theorem lowerConcreteDeletedBackgroundMeanHasFiniteLimit_of_CatalanLimit
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ)
    (h :
      lowerConcreteDeletedBackgroundMeanHasCatalanLimit R k) :
    lowerConcreteDeletedBackgroundMeanHasFiniteLimit R k := by
  exact ⟨lowerDeletedBackgroundMeanCatalanLimit R.lam k, h⟩

/-- Finite-limit corollary from the exact permutation-indexed Wick frontier. -/
theorem lowerConcreteDeletedBackgroundMeanHasFiniteLimit_of_permutationWickLimitFromRatio
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ)
    (hPerm :
      lowerDeletedColumnBackgroundMomentPermutationWickLimit_fromRatio R.sample k) :
    lowerConcreteDeletedBackgroundMeanHasFiniteLimit R k := by
  exact
    lowerConcreteDeletedBackgroundMeanHasFiniteLimit_of_CatalanLimit R k
      (lowerConcreteDeletedBackgroundMeanHasCatalanLimit_of_permutationWickLimitFromRatio
        R k hPerm)

/-- Finite-limit corollary from the two exact PT Wick components. -/
theorem lowerConcreteDeletedBackgroundMeanHasFiniteLimit_of_gaussianRadialFormulaAndGeodesicSurvivorsFromRatio
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ)
    (hFormula :
      lowerDeletedColumnPTGaussianRadialFormula_fromRatio R.sample k)
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k) :
    lowerConcreteDeletedBackgroundMeanHasFiniteLimit R k := by
  exact
    lowerConcreteDeletedBackgroundMeanHasFiniteLimit_of_CatalanLimit R k
      (lowerConcreteDeletedBackgroundMeanHasCatalanLimit_of_gaussianRadialFormulaAndGeodesicSurvivorsFromRatio
        R k hFormula hSurvivors)

/-- Direct finite-limit corollary from the deleted-column asymptotic frontier.

This is the mean-side bridge actually consumed by several endpoint wrappers:
once the deleted-column Catalan asymptotic is available, the legacy finite-limit
form follows immediately. -/
theorem lowerConcreteDeletedBackgroundMeanHasFiniteLimit_of_deletedColumnMomentAsymptotic
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ)
    (h :
      lowerDeletedColumnBackgroundMomentHasCatalanLimit R.sample R.lam k) :
    lowerConcreteDeletedBackgroundMeanHasFiniteLimit R k := by
  exact
    lowerConcreteDeletedBackgroundMeanHasFiniteLimit_of_CatalanLimit
      R k
      ((lowerConcreteDeletedBackgroundMeanHasCatalanLimit_iff_deletedColumnMomentAsymptotic
        R k).2 h)

/-- The explicit finite-diagram estimate also closes the legacy finite-limit
mean frontier. -/
theorem lowerConcreteDeletedBackgroundMeanHasFiniteLimit_of_explicitCatalanDiagramBoundFromRatio
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k m Wcard : ℕ) (Cmodel : ℝ)
    (hDiagram :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample k m Wcard Cmodel) :
    lowerConcreteDeletedBackgroundMeanHasFiniteLimit R k := by
  exact
    lowerConcreteDeletedBackgroundMeanHasFiniteLimit_of_CatalanLimit
      R k
      (lowerConcreteDeletedBackgroundMeanHasCatalanLimit_of_explicitCatalanDiagramBoundFromRatio
        R k m Wcard Cmodel hDiagram)

/-- The explicit Catalan mean limit supplies the bounded positive-part mean
frontier used by the repaired scale-budget route. -/
theorem lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded_of_CatalanLimit
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ)
    (h :
      lowerConcreteDeletedBackgroundMeanHasCatalanLimit R k) :
    lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k := by
  exact
    lower_concrete_deletedBackgroundMean_positivePartEventuallyBounded_of_tendsto
      (R := R) (k := k)
      (m := lowerDeletedBackgroundMeanCatalanLimit R.lam k) h

/-- The preferred mean-side route to the repaired scale budget.

This closes the old `hMeanBound` helper from the exact deleted-column spherical
moment asymptotic, without requiring downstream endpoint wrappers to mention
the helper hypothesis. -/
theorem lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded_of_deletedColumnMomentAsymptotic
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ)
    (h :
      lowerDeletedColumnBackgroundMomentHasCatalanLimit R.sample R.lam k) :
    lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k := by
  exact
    lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded_of_CatalanLimit
      R k
      ((lowerConcreteDeletedBackgroundMeanHasCatalanLimit_iff_deletedColumnMomentAsymptotic
        R k).2 h)

/-- The explicit `D / d` deleted-column Catalan error estimate is enough for
the repaired scale-budget mean bound.

This is the preferred bridge from the concrete crossing/spherical Wick
frontier to `hMeanBound`: no endpoint using the scale-budget route needs to
mention a separate mean-limit hypothesis once this error estimate is available. -/
theorem lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded_of_deletedColumnCatalanErrorBoundFromRatio
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ)
    (hError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample k) :
    lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k := by
  exact
    lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded_of_deletedColumnMomentAsymptotic
      R k
      (lowerDeletedColumnBackgroundMomentHasCatalanLimit_of_fromRatio_errorBound
        (R := R) (k := k) hError)

/-- Direct bridge from the explicit finite-diagram `D_k / d` estimate to the
bounded positive-part mean input used by the scale-budget route. -/
theorem lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded_of_explicitCatalanDiagramBoundFromRatio
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k m Wcard : ℕ) (Cmodel : ℝ)
    (hDiagram :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample k m Wcard Cmodel) :
    lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k := by
  exact
    lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded_of_deletedColumnCatalanErrorBoundFromRatio
      R k
      (lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio_of_explicitDiagramBound
        R.sample k m Wcard Cmodel hDiagram)

/-- Direct bridge from the exact PT Wick components to the bounded
positive-part mean input used by the repaired scale-budget route. -/
theorem lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded_of_gaussianRadialFormulaAndGeodesicSurvivorsFromRatio
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ)
    (hFormula :
      lowerDeletedColumnPTGaussianRadialFormula_fromRatio R.sample k)
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k) :
    lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k := by
  exact
    lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded_of_CatalanLimit
      R k
      (lowerConcreteDeletedBackgroundMeanHasCatalanLimit_of_gaussianRadialFormulaAndGeodesicSurvivorsFromRatio
        R k hFormula hSurvivors)

/-- Concrete lower endpoint with `hMeanLimit` stated at the canonical explicit
Catalan target value.

This is equivalent to the older `hMeanLimit` wrapper with an arbitrary witness
`m`, but it exposes the mathematically intended limit value directly in the
signature. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_traceDominanceAndCatalanMeanLimitFrontierInputs
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hTraceDominance :
      lowerConcreteRankOneProjectorGammaTracePowerDominatesCoordinateOverlap k)
    (hMeanLimit :
      lowerConcreteDeletedBackgroundMeanHasCatalanLimit R k)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
    (hReference :
      ∀ᶠ d in atTop,
        ∀ i₀ : BipIndex (Fin d) (Fin d),
          SurfaceReferenceProjectiveCapConeCoordinateFormula
            (BipIndex (Fin d) (Fin d)) i₀)
    (hMoment :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            (_root_.PptFactorization.AppendixB.sphericalModelMeasure
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
              (backgroundMomentBadSet
                (p := Fin d) (q := Fin d)
                (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
                (lowerConcreteN d) (lowerConcreteTau a slack d)
                (lowerConcreteDeletedBackgroundMean R k d) k) ≤
              lowerConcreteMomentBound R k a slack d) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_traceDominanceAndMeanLimitFrontierInputs
      (R := R) (k := k) (ε := ε)
      (m := lowerDeletedBackgroundMeanCatalanLimit R.lam k)
      hk3 hε hTraceDominance hMeanLimit hMixedEnvelope hReference hMoment

/-- Sharp no-reference closed-trace endpoint with the deleted-background
mean-side debt stated as the explicit Catalan moment asymptotic.

Compared with the active mean-bound endpoint, this wrapper removes
`hMeanBound`; the remaining hard mean-side theorem is precisely
`lowerConcreteDeletedBackgroundMeanHasCatalanLimit R k`. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCatalanMeanLimitFrontierInputs
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanLimit :
      lowerConcreteDeletedBackgroundMeanHasCatalanLimit R k)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
    (hMomentDeviation :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            (_root_.PptFactorization.AppendixB.sphericalModelMeasure
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
              (backgroundMomentDeviationSet
                (p := Fin d) (q := Fin d)
                (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
                (lowerConcreteN d) (lowerConcreteTau a slack d)
                (lowerConcreteDeletedBackgroundMean R k d) k) ≤
              lowerConcreteMomentBound R k a slack d) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceFrontierInputs_meanHasFiniteLimit
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerConcreteDeletedBackgroundMeanHasFiniteLimit_of_CatalanLimit R k hMeanLimit)
      hMixedEnvelope
      hMomentDeviation

/-- Sharp no-reference closed-trace endpoint on the repaired mixed-error route,
with mean-side debt stated as the explicit Catalan asymptotic. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCatalanMeanLimitFrontierInputs_withMixedError
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanLimit :
      lowerConcreteDeletedBackgroundMeanHasCatalanLimit R k)
    (errMix : ℝ → ℝ → ℕ → ℝ)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithError R k ε errMix)
    (hMixedSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errMix a slack d ≤ η)
    (hMomentDeviation :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            (_root_.PptFactorization.AppendixB.sphericalModelMeasure
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
              (backgroundMomentDeviationSet
                (p := Fin d) (q := Fin d)
                (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
                (lowerConcreteN d) (lowerConcreteTau a slack d)
                (lowerConcreteDeletedBackgroundMean R k d) k) ≤
              lowerConcreteMomentBound R k a slack d) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceFrontierInputs_meanHasFiniteLimit_withMixedError
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerConcreteDeletedBackgroundMeanHasFiniteLimit_of_CatalanLimit R k hMeanLimit)
      errMix hMixedEnvelope hMixedSmall hMomentDeviation

/-- Sharp no-reference closed-trace fixed-`M` PT endpoint with the mean side
stated as the concrete Catalan asymptotic and the background side stated as the
paper-facing variance/Chebyshev theorem.

This is the mean-frontier version of the no-input variance-stack wrapper: it
removes the weaker finite-limit mean hypothesis and exposes the actual Catalan
mean theorem consumed by the lower route. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCatalanMeanLimitFrontierInputs_withPTMixedError_splitMixedWordBudget_varianceStack
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanLimit :
      lowerConcreteDeletedBackgroundMeanHasCatalanLimit R k)
    (M : ℝ)
    (hMixed :
      mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceFrontierInputs_meanHasFiniteLimit_withPTMixedError_splitMixedWordBudget_varianceStack
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerConcreteDeletedBackgroundMeanHasFiniteLimit_of_CatalanLimit R k hMeanLimit)
      M hMixed hVariance

/-- Sharp no-reference closed-trace fixed-`M` PT endpoint with the mean side
exposed as the reusable deleted-column spherical Catalan asymptotic.

This is the source-frontier version of
`...CatalanMeanLimitFrontierInputs_withPTMixedError_splitMixedWordBudget_varianceStack`:
the endpoint-specific concrete Catalan predicate is supplied by the
deleted-column moment asymptotic equivalence. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndDeletedColumnMomentFrontierInputs_withPTMixedError_splitMixedWordBudget_varianceStack
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanAsymptotic :
      lowerDeletedColumnBackgroundMomentHasCatalanLimit R.sample R.lam k)
    (M : ℝ)
    (hMixed :
      mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCatalanMeanLimitFrontierInputs_withPTMixedError_splitMixedWordBudget_varianceStack
      (R := R) (k := k) (ε := ε) hk3 hε
      ((lowerConcreteDeletedBackgroundMeanHasCatalanLimit_iff_deletedColumnMomentAsymptotic
        R k).2 hMeanAsymptotic)
      M hMixed hVariance

/-- Sharp no-reference closed-trace fixed-`M` PT endpoint with the mean side
exposed in the ratio-parametric core form.

Compared with
`...DeletedColumnMomentFrontierInputs_withPTMixedError_splitMixedWordBudget_varianceStack`,
this removes the concrete-at-`R.lam` deleted-column asymptotic from the public
frontier and supplies it from
`lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio`. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndDeletedColumnMomentFromRatioFrontierInputs_withPTMixedError_splitMixedWordBudget_varianceStack
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanAsymptoticCore :
      lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio R.sample k)
    (M : ℝ)
    (hMixed :
      mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndDeletedColumnMomentFrontierInputs_withPTMixedError_splitMixedWordBudget_varianceStack
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerDeletedColumnBackgroundMomentHasCatalanLimit_of_fromRatio
        (R := R) (k := k) hMeanAsymptoticCore)
      M hMixed hVariance

/-- Sharp no-reference closed-trace fixed-`M` PT endpoint with the mean side
reduced to the explicit ratio-parametric Catalan-error frontier.

This is the paper-facing mean-side refinement of
`...DeletedColumnMomentFromRatioFrontierInputs_withPTMixedError_splitMixedWordBudget_varianceStack`:
the broad ratio-parametric Catalan convergence input is supplied by the
explicit crossing/spherical `D / d` error estimate. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCatalanErrorBoundFrontierInputs_withPTMixedError_splitMixedWordBudget_varianceStack
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample k)
    (M : ℝ)
    (hMixed :
      mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndDeletedColumnMomentFromRatioFrontierInputs_withPTMixedError_splitMixedWordBudget_varianceStack
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio_of_errorBound
        R.sample k hMeanError)
      M hMixed hVariance

/-- Sharp no-reference closed-trace fixed-`M` PT endpoint with the mean side
reduced to the explicit finite-diagram Catalan frontier.

This exposes the Wick/combinatorial estimate underneath the Catalan-error
predicate on the same paper-facing variance/Chebyshev concentration branch. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndExplicitCatalanDiagramFrontierInputs_withPTMixedError_splitMixedWordBudget_varianceStack
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hMeanDiagram :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample k m Wcard Cmodel)
    (M : ℝ)
    (hMixed :
      mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCatalanErrorBoundFrontierInputs_withPTMixedError_splitMixedWordBudget_varianceStack
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio_of_explicitDiagramBound
        R.sample k m Wcard Cmodel hMeanDiagram)
      M hMixed hVariance

/-- Sharp no-reference closed-trace fixed-`M` PT endpoint with the mean side
rerouted through the Wick survivor core.

The current grouped Gaussian/radial predicate is supplied by its audited
identity-carrier witness, so the visible mean-side Wick leaf is only the
geodesic/noncrossing survivor analysis. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withPTMixedError_splitMixedWordBudget_varianceStack
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    (M : ℝ)
    (hMixed :
      mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndDeletedColumnMomentFromRatioFrontierInputs_withPTMixedError_splitMixedWordBudget_varianceStack
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio_of_permutationWickLimit
        R.sample k
        (lowerDeletedColumnBackgroundMomentPermutationWickLimit_fromRatio_of_gaussianRadialFormula_and_geodesicSurvivors
          R.sample k
          (lowerDeletedColumnPTGaussianRadialFormula_fromRatio_currentPredicate
            R.sample k)
          hSurvivors))
      M hMixed hVariance

/-- Preferred sharp no-reference closed-trace endpoint for the live mean
frontier.

This theorem does not expose the old `hMeanBound` budget helper.  The remaining
mean-side input is exactly the reusable deleted-column spherical Catalan moment
asymptotic for the concrete deleted background. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndDeletedColumnMomentFrontierInputs
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanAsymptotic :
      lowerDeletedColumnBackgroundMomentHasCatalanLimit R.sample R.lam k)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
    (hMomentDeviation :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            (_root_.PptFactorization.AppendixB.sphericalModelMeasure
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
              (backgroundMomentDeviationSet
                (p := Fin d) (q := Fin d)
                (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
                (lowerConcreteN d) (lowerConcreteTau a slack d)
                (lowerConcreteDeletedBackgroundMean R k d) k) ≤
              lowerConcreteMomentBound R k a slack d) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCatalanMeanLimitFrontierInputs
      (R := R) (k := k) (ε := ε) hk3 hε
      ((lowerConcreteDeletedBackgroundMeanHasCatalanLimit_iff_deletedColumnMomentAsymptotic
        R k).2 hMeanAsymptotic)
      hMixedEnvelope
      hMomentDeviation

/-- Same preferred endpoint, with the mean-side hard theorem exposed in the
ratio-parametric core form.

This is the first exact missing Catalan lemma frontier:
`lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio`.
-/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndDeletedColumnMomentFromRatioFrontierInputs
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanAsymptoticCore :
      lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio R.sample k)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
    (hMomentDeviation :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            (_root_.PptFactorization.AppendixB.sphericalModelMeasure
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
              (backgroundMomentDeviationSet
                (p := Fin d) (q := Fin d)
                (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
                (lowerConcreteN d) (lowerConcreteTau a slack d)
                (lowerConcreteDeletedBackgroundMean R k d) k) ≤
              lowerConcreteMomentBound R k a slack d) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndDeletedColumnMomentFrontierInputs
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerDeletedColumnBackgroundMomentHasCatalanLimit_of_fromRatio
        (R := R) (k := k) hMeanAsymptoticCore)
      hMixedEnvelope
      hMomentDeviation

/-- Sharp no-reference closed-trace endpoint with the exact core frontiers
named directly.

This is the current smallest honest lower frontier object:
* deleted-column Catalan asymptotic in ratio-parametric core form;
* mixed local-expansion envelope;
* deleted-column closed-deviation moment tail.
-/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCoreFrontierInputs
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanAsymptoticCore :
      lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio R.sample k)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
    (hMomentDeviation :
      lowerConcreteDeletedBackgroundMomentDeviationTailBound R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndDeletedColumnMomentFromRatioFrontierInputs
      (R := R) (k := k) (ε := ε) hk3 hε
      hMeanAsymptoticCore hMixedEnvelope hMomentDeviation

/-- Core-frontier endpoint with the mean side reduced to the exact PT Wick
components already isolated: Gaussian/radial formula and geodesic/noncrossing
survivor analysis. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTWickCoreFrontierInputs
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hFormula :
      lowerDeletedColumnPTGaussianRadialFormula_fromRatio R.sample k)
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
    (hMomentDeviation :
      lowerConcreteDeletedBackgroundMomentDeviationTailBound R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCoreFrontierInputs
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio_of_permutationWickLimit
        R.sample k
        (lowerDeletedColumnBackgroundMomentPermutationWickLimit_fromRatio_of_gaussianRadialFormula_and_geodesicSurvivors
          R.sample k hFormula hSurvivors))
      hMixedEnvelope
      hMomentDeviation

/-- Endpoint-safe PT Wick core wrapper with the background concentration
supplied by the two-trace Wick/Chebyshev tail.

Compared with
`lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTWickCoreFrontierInputs`,
the moment-tail input is the polynomial second-moment frontier
`lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k`,
matching the `1 / d` background-typical threshold used in the lower endpoint. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTWickCoreFrontierInputs_secondMomentWickMomentTail
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hFormula :
      lowerDeletedColumnPTGaussianRadialFormula_fromRatio R.sample k)
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceFrontierInputs_meanBound_secondMomentWickMomentTail
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded_of_gaussianRadialFormulaAndGeodesicSurvivorsFromRatio
        R k hFormula hSurvivors)
      hMixedEnvelope
      hMomentSecond

/-- PT Wick-core endpoint with the background concentration exposed as the
paper-facing variance estimate.

This is the variance-facing form of
`...PTWickCoreFrontierInputs_secondMomentWickMomentTail`: the grouped
second-moment tail is obtained internally from
`deletedColumnSphericalMoment_variance_le_const_div_d4`. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTWickCoreFrontierInputs_varianceMomentTail
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hFormula :
      lowerDeletedColumnPTGaussianRadialFormula_fromRatio R.sample k)
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceFrontierInputs_meanBound_varianceMomentTail
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded_of_gaussianRadialFormulaAndGeodesicSurvivorsFromRatio
        R k hFormula hSurvivors)
      hMixedEnvelope
      hVariance

/-- PT survivor-core endpoint with the broad Gaussian/radial predicate closed
and background concentration exposed as the paper-facing variance estimate.

The visible mean-side input is the geodesic/noncrossing survivor analysis; the
Gaussian/radial predicate is supplied by its current identity-carrier witness. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_varianceMomentTail
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTWickCoreFrontierInputs_varianceMomentTail
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerDeletedColumnPTGaussianRadialFormula_fromRatio_currentPredicate
        R.sample k)
      hSurvivors
      hMixedEnvelope
      hVariance

/-- Endpoint-safe wrapper for prior closed-form moment formalizations.

Use this when the earlier work on disk proves the deleted-column spherical mean
as convergence to `(λ⁻¹)^k * ClosedFormDet.M λ k`.  The theorem converts that
older target to the Catalan-series target and combines it with the
two-trace Wick/Chebyshev moment-tail route. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndClosedFormMomentLimitFrontierInputs_secondMomentWickMomentTail
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hClosed :
      lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit_fromRatio
        R.sample k)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceFrontierInputs_meanBound_secondMomentWickMomentTail
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded_of_CatalanLimit
        R k
        (lowerConcreteDeletedBackgroundMeanHasCatalanLimit_of_closedFormMomentLimitFromRatio
          R k hClosed))
      hMixedEnvelope
      hMomentSecond

/-- Endpoint-safe wrapper for prior closed-form moment formalizations, paired
with the repaired PT mixed-error supplier.

This is the concrete adapter for the case where the deleted-column mean theorem
has already been proved in the older closed-form moment language, while the
mixed side is supplied by the corrected partial-transpose error
`lowerPartialTransposeMixedErrorD`. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndClosedFormMomentLimitFrontierInputs_withPTMixedError_secondMomentWickMomentTail
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hClosed :
      lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit_fromRatio
        R.sample k)
    (A M : ℝ)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithError R k ε
        (fun _a _slack d => lowerPartialTransposeMixedErrorD k A M d))
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceFrontierInputs_meanBound_withPTMixedError_secondMomentWickMomentTail
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded_of_CatalanLimit
        R k
        (lowerConcreteDeletedBackgroundMeanHasCatalanLimit_of_closedFormMomentLimitFromRatio
          R k hClosed))
      A M hMixedEnvelope hMomentSecond

/-- Endpoint wrapper using the paper-facing PT deleted-column spherical mean
theorem directly.

This is the intended plug-in point for the theorem
`E[(d^2)^(k-1) Tr(((Y_dY_d*)^Γ)^k)] → ptCatalanMean k λ`, with fixed points
allowed in the noncrossing-involution survivor class. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndDeletedColumnSphericalPTCatalanMeanInput_withPTMixedError_secondMomentWickMomentTail
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMean :
      deletedColumnSphericalMean_tendsto_ptCatalan R.sample k R.lam)
    (A M : ℝ)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithError R k ε
        (fun _a _slack d => lowerPartialTransposeMixedErrorD k A M d))
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceFrontierInputs_meanBound_withPTMixedError_secondMomentWickMomentTail
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded_of_deletedColumnMomentAsymptotic
        R k
        (lowerDeletedColumnBackgroundMomentHasCatalanLimit_of_deletedColumnSphericalMean_tendsto_ptCatalan
          R.sample k R.lam hMean))
      A M hMixedEnvelope hMomentSecond

/-- Endpoint-safe wrapper for the explicit crossing/spherical `D / d`
deleted-column Catalan error estimate, paired with the two-trace
Wick/Chebyshev moment-tail route.

This is the concrete mean-side theorem matching the current mathematical
closure packet: the mean input is the finite diagram error estimate, and the
background typicality input is the polynomial second-moment Wick tail at the
`1 / d` threshold. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCatalanErrorBoundFrontierInputs_secondMomentWickMomentTail
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample k)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceFrontierInputs_meanBound_secondMomentWickMomentTail
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded_of_deletedColumnCatalanErrorBoundFromRatio
        R k hMeanError)
      hMixedEnvelope
      hMomentSecond

/-- Same second-moment-tail endpoint with the mean side stated in the most
concrete explicit-diagram form.

Use this when the Wick computation has produced the explicit crossing plus
spherical remainder bound rather than the abstract Catalan-error predicate. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndExplicitCatalanDiagramFrontierInputs_secondMomentWickMomentTail
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hMeanDiagram :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample k m Wcard Cmodel)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCatalanErrorBoundFrontierInputs_secondMomentWickMomentTail
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio_of_explicitDiagramBound
        R.sample k m Wcard Cmodel hMeanDiagram)
      hMixedEnvelope
      hMomentSecond

/-- Core-frontier endpoint with the deleted-column mean input reduced to the
explicit crossing/spherical `D / d` Catalan error estimate.

This is the mean-side closure wrapper matching the current mathematical
frontier: the remaining mean theorem is no longer a broad convergence input,
but the concrete finite-diagram error estimate for the deleted-column
spherical Wick expansion. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCatalanErrorBoundFrontierInputs
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample k)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
    (hMomentDeviation :
      lowerConcreteDeletedBackgroundMomentDeviationTailBound R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCoreFrontierInputs
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio_of_errorBound
        R.sample k hMeanError)
      hMixedEnvelope
      hMomentDeviation

/-- Core-frontier endpoint with the mixed supplier split into word-level and
finite-budget obligations.

This is the mixed-side decomposition companion of
`..._of_noReferenceClosedTraceAndCoreFrontierInputs`: it keeps the same mean
and moment frontiers, while replacing the broad mixed-envelope hypothesis by
its two exact local components. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCoreFrontierInputs_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanAsymptoticCore :
      lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio R.sample k)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
    (hMomentDeviation :
      lowerConcreteDeletedBackgroundMomentDeviationTailBound R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCoreFrontierInputs
      (R := R) (k := k) (ε := ε) hk3 hε
      hMeanAsymptoticCore
      hMixedEnvelope
      hMomentDeviation

/-- Same split mixed-word endpoint, but with the deleted-column Catalan mean
frontier stated as the explicit `D / d` error estimate. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCatalanErrorBoundFrontierInputs_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample k)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelope R k ε)
    (hMomentDeviation :
      lowerConcreteDeletedBackgroundMomentDeviationTailBound R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCoreFrontierInputs_splitMixedWordBudget
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio_of_errorBound
        R.sample k hMeanError)
      hMixedEnvelope hMomentDeviation

/-- Preferred sharp no-reference endpoint on the repaired mixed-error route
with the live deleted-column moment frontier exposed directly. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndDeletedColumnMomentFrontierInputs_withMixedError
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanAsymptotic :
      lowerDeletedColumnBackgroundMomentHasCatalanLimit R.sample R.lam k)
    (errMix : ℝ → ℝ → ℕ → ℝ)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithError R k ε errMix)
    (hMixedSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errMix a slack d ≤ η)
    (hMomentDeviation :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            (_root_.PptFactorization.AppendixB.sphericalModelMeasure
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
              (backgroundMomentDeviationSet
                (p := Fin d) (q := Fin d)
                (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
                (lowerConcreteN d) (lowerConcreteTau a slack d)
                (lowerConcreteDeletedBackgroundMean R k d) k) ≤
              lowerConcreteMomentBound R k a slack d) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCatalanMeanLimitFrontierInputs_withMixedError
      (R := R) (k := k) (ε := ε) hk3 hε
      ((lowerConcreteDeletedBackgroundMeanHasCatalanLimit_iff_deletedColumnMomentAsymptotic
        R k).2 hMeanAsymptotic)
      errMix hMixedEnvelope hMixedSmall hMomentDeviation

/-- Core deleted-column mean frontier on the repaired PT mixed-error route,
with mixed-error smallness discharged automatically.

This keeps the sharp mean-side and moment-side frontiers, while replacing the
free `hMixedSmall` input by the intrinsic `o(1)` property of
`lowerPartialTransposeMixedErrorD`. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCoreFrontierInputs_withPTMixedError
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanAsymptoticCore :
      lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio R.sample k)
    (A M : ℝ)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithError R k ε
        (fun _a _slack d => lowerPartialTransposeMixedErrorD k A M d))
    (hMomentDeviation :
      lowerConcreteDeletedBackgroundMomentDeviationTailBound R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndDeletedColumnMomentFrontierInputs_withMixedError
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerDeletedColumnBackgroundMomentHasCatalanLimit_of_fromRatio
        (R := R) (k := k) hMeanAsymptoticCore)
      (fun _a _slack d => lowerPartialTransposeMixedErrorD k A M d)
      hMixedEnvelope
      (by
        intro a _ha slack _hslack η hη
        exact
          lowerPartialTransposeMixedErrorD_eventually_le
            (k := k) hk3 A M η hη)
      hMomentDeviation

/-- PT mixed-error endpoint with the mean side reduced to the ratio-parametric
deleted-column Catalan asymptotic and the background typicality supplied by
the two-trace Wick/Chebyshev tail. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCoreFrontierInputs_withPTMixedError_secondMomentWickMomentTail
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanAsymptoticCore :
      lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio R.sample k)
    (A M : ℝ)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithError R k ε
        (fun _a _slack d => lowerPartialTransposeMixedErrorD k A M d))
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceFrontierInputs_meanBound_withPTMixedError_secondMomentWickMomentTail
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded_of_deletedColumnMomentAsymptotic
        R k
        (lowerDeletedColumnBackgroundMomentHasCatalanLimit_of_fromRatio
          (R := R) (k := k) hMeanAsymptoticCore))
      A M hMixedEnvelope hMomentSecond

/-- PT mixed-error endpoint with the mean frontier reduced to the explicit
deleted-column Catalan `D / d` error estimate. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCatalanErrorBoundFrontierInputs_withPTMixedError
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample k)
    (A M : ℝ)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithError R k ε
        (fun _a _slack d => lowerPartialTransposeMixedErrorD k A M d))
    (hMomentDeviation :
      lowerConcreteDeletedBackgroundMomentDeviationTailBound R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCoreFrontierInputs_withPTMixedError
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio_of_errorBound
        R.sample k hMeanError)
      A M hMixedEnvelope hMomentDeviation

/-- PT mixed-error endpoint with the mean frontier reduced to the explicit
deleted-column Catalan `D / d` error estimate and the moment tail supplied by
the two-trace Wick/Chebyshev bound. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCatalanErrorBoundFrontierInputs_withPTMixedError_secondMomentWickMomentTail
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample k)
    (A M : ℝ)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithError R k ε
        (fun _a _slack d => lowerPartialTransposeMixedErrorD k A M d))
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCoreFrontierInputs_withPTMixedError_secondMomentWickMomentTail
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio_of_errorBound
        R.sample k hMeanError)
      A M hMixedEnvelope hMomentSecond

/-- Core-frontier PT mixed-error endpoint with the mixed side split into exact
word-level and scalar-budget obligations.

This is the sharpest currently packaged mixed route on the core frontier:
`hMixedSmall` is discharged automatically and `hMixedEnvelope` is built from
word bounds plus a finite mixed-word budget. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCoreFrontierInputs_withPTMixedError_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanAsymptoticCore :
      lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio R.sample k)
    (M : ℝ)
    (hMixed :
      mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M)
    (hMomentDeviation :
      lowerConcreteDeletedBackgroundMomentDeviationTailBound R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndDeletedColumnMomentFrontierInputs_withMixedError
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerDeletedColumnBackgroundMomentHasCatalanLimit_of_fromRatio
        (R := R) (k := k) hMeanAsymptoticCore)
      (fun a slack d => lowerPartialTransposeMixedErrorD k (a + slack) M d)
      (lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithPTError_of_mixed_noL_atLeastTwoQ_ge_neg_errMix
        R k ε M hMixed)
      (by
        intro a _ha slack _hslack η hη
        exact
          lowerPartialTransposeMixedErrorD_eventually_le
            (k := k) hk3 (a + slack) M η hη)
      hMomentDeviation

/-- Core-frontier PT mixed-error endpoint with the mixed side split into
word-level and scalar-budget obligations, and the background typicality
supplied by the two-trace Wick/Chebyshev tail.

This is the polynomial-tail companion of
`...withPTMixedError_splitMixedWordBudget`: it removes the generic
closed-deviation hypothesis from the split mixed-word route. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCoreFrontierInputs_withPTMixedError_splitMixedWordBudget_secondMomentWickMomentTail
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanAsymptoticCore :
      lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio R.sample k)
    (M : ℝ)
    (hMixed :
      mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M)
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  have hk : 1 < k := lt_of_lt_of_le (by decide : 1 < 3) hk3
  rcases
    lowerConcreteDeletedBackgroundMomentSecondMomentWickBadTailBound_of_deviationTailBound
      (R := R) (k := k) hMomentSecond with
    ⟨C, _hC, hMomentBad⟩
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_concreteScalarChoices_sphereBetaScaleBudget_withMomentBudgetAndMixedError
      (R := R) (k := k) (ε := ε) hk hε
      (bMoment := lowerConcreteMomentPolynomialBound C R k)
      (errMix := fun a slack d => lowerPartialTransposeMixedErrorD k (a + slack) M d)
      (lower_unitProfile_canonicalDirection_concreteChoices_of_traceStability
        hk hε
        (lowerConcreteCanonicalCapSpikeTraceStability_of_overlapLower
          (lt_of_lt_of_le (by decide : 1 < 3) hk3)
          hε
          (lowerConcreteCanonicalCapTracePowerOverlapLower_of_traceDominatesCoordinateOverlap
            (lowerConcreteRankOneProjectorGammaTracePowerDominatesCoordinateOverlap_of_leftDensityDiagonalPower
              (lowerConcreteRankOneProjectorGammaTracePowerDominatesLeftDensityDiagonalPower_closed k)))))
      (lower_scaleBudget_concreteChoices_of_meanPositivePartEventuallyBounded
        (R := R) (k := k) (ε := ε) hk3 hε
        (lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded_of_deletedColumnMomentAsymptotic
          R k
          (lowerDeletedColumnBackgroundMomentHasCatalanLimit_of_fromRatio
            (R := R) (k := k) hMeanAsymptoticCore)))
      (lower_mixedLowerOnSphere_concreteChoices_of_localExpansionEnvelopeOnSphereWithError
        (R := R) (k := k) (ε := ε)
        (fun a slack d => lowerPartialTransposeMixedErrorD k (a + slack) M d)
        (lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithPTError_of_mixed_noL_atLeastTwoQ_ge_neg_errMix
          R k ε M hMixed))
      (by
        intro a _ha slack _hslack η hη
        exact
          lowerPartialTransposeMixedErrorD_eventually_le
            (k := k) hk3 (a + slack) M η hη)
      lower_referenceCone_BipIndex_Fin_eventually_concreteChoices
      hMomentBad
      (lower_concrete_polynomialMomentSmall C R k)

/-- Core-frontier PT endpoint with second-moment background typicality and the
mixed side exposed as the actual pointwise word estimate.

This is the direct pointwise-word version of
`...withPTMixedError_splitMixedWordBudget_secondMomentWickMomentTail`: the
caller supplies the sphere-supported bound against
`lowerPartialTransposeMixedWordBoundD`, and the finite mixed budget adapter
constructs the packed PT mixed supplier internally. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCoreFrontierInputs_withPTPointwiseMixedWordBound_splitMixedWordBudget_secondMomentWickMomentTail
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanAsymptoticCore :
      lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio R.sample k)
    (M : ℝ) (hM : 0 ≤ M)
    (hWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k ε
        (fun a slack d => lowerPartialTransposeMixedWordBoundD k (a + slack) M d))
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  have hk : 1 ≤ k := by omega
  have hMixed :
      mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M :=
    mixed_noL_atLeastTwoQ_ge_neg_errMix_of_pointwiseWordBound
      (R := R) (k := k) (ε := ε) (M := M) hk hε hM hWord
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCoreFrontierInputs_withPTMixedError_splitMixedWordBudget_secondMomentWickMomentTail
      (R := R) (k := k) (ε := ε) hk3 hε
      hMeanAsymptoticCore M hMixed hMomentSecond

/-- PT Wick-core endpoint with second-moment background typicality and
pointwise PT mixed words.

This exposes all three currently active theorem-strength inputs on the central
lower branch: Gaussian/radial formula, geodesic/noncrossing survivor analysis,
and the sphere-supported pointwise PT mixed-word estimate. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTWickCoreFrontierInputs_withPTPointwiseMixedWordBound_splitMixedWordBudget_secondMomentWickMomentTail
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hFormula :
      lowerDeletedColumnPTGaussianRadialFormula_fromRatio R.sample k)
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    (M : ℝ) (hM : 0 ≤ M)
    (hWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k ε
        (fun a slack d => lowerPartialTransposeMixedWordBoundD k (a + slack) M d))
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
        Real.log
            (lowerConcreteTargetProb R (lowerConcreteEps ε)
              (lowerConcreteDeletedBackgroundMean R k) k d) /
          spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCoreFrontierInputs_withPTPointwiseMixedWordBound_splitMixedWordBudget_secondMomentWickMomentTail
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio_of_permutationWickLimit
        R.sample k
        (lowerDeletedColumnBackgroundMomentPermutationWickLimit_fromRatio_of_gaussianRadialFormula_and_geodesicSurvivors
          R.sample k hFormula hSurvivors))
      M hM hWord hMomentSecond

/-- PT Wick-core endpoint with the current broad Gaussian/radial predicate
closed by its unconditional identity-carrier witness.

This removes the visible `lowerDeletedColumnPTGaussianRadialFormula_fromRatio`
input from the central pointwise PT mixed route.  The geodesic survivor
analysis remains visible because that predicate is the genuine finite
combinatorial survivor step in the current endpoint. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withPTPointwiseMixedWordBound_splitMixedWordBudget_secondMomentWickMomentTail
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    (M : ℝ) (hM : 0 ≤ M)
    (hWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k ε
        (fun a slack d => lowerPartialTransposeMixedWordBoundD k (a + slack) M d))
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTWickCoreFrontierInputs_withPTPointwiseMixedWordBound_splitMixedWordBudget_secondMomentWickMomentTail
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerDeletedColumnPTGaussianRadialFormula_fromRatio_currentPredicate
        R.sample k)
      hSurvivors M hM hWord hMomentSecond

/-- PT survivor-core endpoint with the background typicality side exposed as
the paper-facing variance/Chebyshev frontier.

This is only an adapter: `deletedColumnSphericalMoment_variance_le_const_div_d4`
is the named theorem-strength variance leaf.  The internal grouped
second-moment tail is supplied from it by
`lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound_of_deletedColumnSphericalMoment_variance_le_const_div_d4`.
-/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withPTPointwiseMixedWordBound_splitMixedWordBudget_varianceStack
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (M : ℝ) (hM : 0 ≤ M)
    (hWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k ε
        (fun a slack d => lowerPartialTransposeMixedWordBoundD k (a + slack) M d)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withPTPointwiseMixedWordBound_splitMixedWordBudget_secondMomentWickMomentTail
      (R := R) (k := k) (ε := ε) hk3 hε
      hSurvivors M hM hWord
      (lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound_of_deletedColumnSphericalMoment_variance_le_const_div_d4
        R k hVariance)

/-- PT survivor-core endpoint with the pointwise mixed-word leaf split into the
two direct scalar cases.

This avoids the known-dead fixed-`M` runtime-domination route: the endpoint
does not ask the runtime envelope to be dominated by the literal PT envelope.
Instead it asks directly for the local trace estimates on the exactly-one-`Q`
and many-`Q` word fibers, and uses the finite word split to assemble the
pointwise PT mixed-word bound internally. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withPTDirectMixedWordScalarCases_splitMixedWordBudget_varianceStack
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (M : ℝ) (hM : 0 ≤ M)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R k ε M)
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R k ε M) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withPTPointwiseMixedWordBound_splitMixedWordBudget_varianceStack
      (R := R) (k := k) (ε := ε) hk3 hε
      hSurvivors hVariance M hM
      (lowerConcreteMixedWordPointwiseBoundOnSphere_withPTError_of_directScalarCases
        (R := R) (k := k) (ε := ε) (M := M)
        (by omega) hε hM hOne hMany)

/-- PT survivor-core endpoint with the one-`Q` direct mixed scalar leaf reduced
to its exact scale comparison.

The many-`Q` scalar leaf remains visible.  This is the next active mixed
frontier below `...withPTDirectMixedWordScalarCases...`: the local one-`Q`
trace estimate is supplied internally, and the only one-`Q` input left is the
scalar comparison between the current concrete background threshold and the
fixed PT envelope. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withPTOneQScaleComparisonAndManyQDirect_splitMixedWordBudget_varianceStack
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (M : ℝ) (hM : 0 ≤ M)
    (hOneScale :
      lowerConcretePTMixedWordOneQScaleComparison R k ε M)
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R k ε M) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withPTDirectMixedWordScalarCases_splitMixedWordBudget_varianceStack
      (R := R) (k := k) (ε := ε) hk3 hε
      hSurvivors hVariance M hM
      (lowerConcretePTMixedWordOneQDirectScalarBound_of_scaleComparison
        (R := R) (k := k) (ε := ε) (M := M) hk3 hε hOneScale)
      hMany

/-- PT survivor-core endpoint with both direct mixed scalar leaves reduced to
their exact scale comparisons.

The local one-`Q` and many-`Q` trace estimates, finite word split, PT budget,
and error-smallness adapters are supplied internally.  The remaining mixed
inputs are the scalar comparisons against the fixed PT envelope parameter `M`.
-/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withPTScaleComparisons_splitMixedWordBudget_varianceStack
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (M : ℝ) (hM : 0 ≤ M)
    (hOneScale :
      lowerConcretePTMixedWordOneQScaleComparison R k ε M)
    (hManyScale :
      lowerConcretePTMixedWordManyQScaleComparison R k ε M) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withPTOneQScaleComparisonAndManyQDirect_splitMixedWordBudget_varianceStack
      (R := R) (k := k) (ε := ε) hk3 hε
      hSurvivors hVariance M hM hOneScale
      (lowerConcretePTMixedWordManyQDirectScalarBound_of_scaleComparison
        (R := R) (k := k) (ε := ε) (M := M) hk3 hε hManyScale)

/-- PT survivor-core endpoint with the background typicality side exposed as
the stronger exponential deviation-tail source.

This is only an adapter: the exponential source supplies the paper-facing
variance/Chebyshev frontier through
`deletedColumnSphericalMoment_variance_le_const_div_d4_of_exponentialDeviationTailBound`.
-/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withPTPointwiseMixedWordBound_splitMixedWordBudget_exponentialDeviationStack
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    (hExponentialTail :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R k)
    (M : ℝ) (hM : 0 ≤ M)
    (hWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k ε
        (fun a slack d => lowerPartialTransposeMixedWordBoundD k (a + slack) M d)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withPTPointwiseMixedWordBound_splitMixedWordBudget_varianceStack
      (R := R) (k := k) (ε := ε) hk3 hε
      hSurvivors
      (deletedColumnSphericalMoment_variance_le_const_div_d4_of_exponentialDeviationTailBound
        R k hExponentialTail)
      M hM hWord

/-- PT survivor-core endpoint with the exponential background tail and the
pointwise mixed-word leaf split into the two direct scalar cases.

This is the exponential-tail analogue of
`...withPTDirectMixedWordScalarCases_splitMixedWordBudget_varianceStack`: the
stronger background concentration source is kept visible, while the mixed side
is reduced from a sphere-supported pointwise word estimate to the one-`Q` and
many-`Q` scalar trace bounds. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withPTDirectMixedWordScalarCases_splitMixedWordBudget_exponentialDeviationStack
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    (hExponentialTail :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R k)
    (M : ℝ) (hM : 0 ≤ M)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R k ε M)
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R k ε M) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withPTPointwiseMixedWordBound_splitMixedWordBudget_exponentialDeviationStack
      (R := R) (k := k) (ε := ε) hk3 hε
      hSurvivors hExponentialTail M hM
      (lowerConcreteMixedWordPointwiseBoundOnSphere_withPTError_of_directScalarCases
        (R := R) (k := k) (ε := ε) (M := M)
        (by omega) hε hM hOne hMany)

/-- Exponential-tail PT survivor-core endpoint with the one-`Q` direct mixed
scalar leaf reduced to its exact scale comparison.

This is the exponential-background analogue of
`...withPTOneQScaleComparisonAndManyQDirect_splitMixedWordBudget_varianceStack`:
the stronger background concentration source remains visible, while the local
one-`Q` trace estimate is supplied internally from the scale comparison. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withPTOneQScaleComparisonAndManyQDirect_splitMixedWordBudget_exponentialDeviationStack
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    (hExponentialTail :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R k)
    (M : ℝ) (hM : 0 ≤ M)
    (hOneScale :
      lowerConcretePTMixedWordOneQScaleComparison R k ε M)
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R k ε M) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withPTDirectMixedWordScalarCases_splitMixedWordBudget_exponentialDeviationStack
      (R := R) (k := k) (ε := ε) hk3 hε
      hSurvivors hExponentialTail M hM
      (lowerConcretePTMixedWordOneQDirectScalarBound_of_scaleComparison
        (R := R) (k := k) (ε := ε) (M := M) hk3 hε hOneScale)
      hMany

/-- Exponential-tail PT survivor-core endpoint with both direct mixed scalar
leaves reduced to their exact scale comparisons.

This is the exponential-background analogue of
`...withPTScaleComparisons_splitMixedWordBudget_varianceStack`: the local
one-`Q` and many-`Q` trace estimates are supplied internally from the two
scale comparisons, while the stronger exponential background concentration
source remains visible. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withPTScaleComparisons_splitMixedWordBudget_exponentialDeviationStack
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    (hExponentialTail :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R k)
    (M : ℝ) (hM : 0 ≤ M)
    (hOneScale :
      lowerConcretePTMixedWordOneQScaleComparison R k ε M)
    (hManyScale :
      lowerConcretePTMixedWordManyQScaleComparison R k ε M) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withPTOneQScaleComparisonAndManyQDirect_splitMixedWordBudget_exponentialDeviationStack
      (R := R) (k := k) (ε := ε) hk3 hε
      hSurvivors hExponentialTail M hM hOneScale
      (lowerConcretePTMixedWordManyQDirectScalarBound_of_scaleComparison
        (R := R) (k := k) (ε := ε) (M := M) hk3 hε hManyScale)

/-- PT survivor-core endpoint with mixed words reduced to the runtime
domination-on-mixed comparison.

The favourable-event runtime envelope is supplied internally by
`lowerConcreteMixedWordPointwiseBoundOnSphere_runtimeEnvelope`; only the
eventual domination by the cleaner fixed-`M` PT envelope remains visible. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withPTRuntimeMixedWordDominationOnMixed_splitMixedWordBudget_exponentialDeviationStack
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    (hExponentialTail :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R k)
    (M : ℝ) (hM : 0 ≤ M)
    (hWordDom :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                lowerConcreteMixedRuntimeWordBound R k a slack d w ≤
                  lowerPartialTransposeMixedWordBoundD k (a + slack) M d w) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withPTPointwiseMixedWordBound_splitMixedWordBudget_exponentialDeviationStack
      (R := R) (k := k) (ε := ε) hk3 hε
      hSurvivors hExponentialTail M hM
      (lowerConcreteMixedWordPointwiseBoundOnSphere_of_runtimeEnvelope_domination_on_mixed
        (R := R) (k := k) (ε := ε)
        (lowerConcreteMixedWordPointwiseBoundOnSphere_runtimeEnvelope
          (R := R) (k := k) (ε := ε) hk3 hε)
        hWordDom)

/-- PT survivor-core endpoint with mixed runtime domination split into the two
no-`L` scalar cases.

Mixed words containing `L` are handled internally by the zero-runtime case and
nonnegativity of the PT envelope.  The visible mixed leaves are exactly the
one-`Q` and many-`Q` domination estimates. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withPTRuntimeMixedWordDominationCases_splitMixedWordBudget_exponentialDeviationStack
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    (hExponentialTail :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R k)
    (M : ℝ) (hM : 0 ≤ M)
    (hWordDomOne :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                localWordLetterCount LocalExpansionLetter.L w = 0 →
                  localWordLetterCount LocalExpansionLetter.Q w = 1 →
                    lowerConcreteMixedRuntimeWordBound R k a slack d w ≤
                      lowerPartialTransposeMixedWordBoundD k (a + slack) M d w)
    (hWordDomMany :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                localWordLetterCount LocalExpansionLetter.L w = 0 →
                  2 ≤ localWordLetterCount LocalExpansionLetter.Q w →
                    lowerConcreteMixedRuntimeWordBound R k a slack d w ≤
                      lowerPartialTransposeMixedWordBoundD k (a + slack) M d w) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withPTRuntimeMixedWordDominationOnMixed_splitMixedWordBudget_exponentialDeviationStack
      (R := R) (k := k) (ε := ε) hk3 hε
      hSurvivors hExponentialTail M hM
      (lowerConcreteMixedRuntimeWordBound_domination_on_mixed_of_oneQ_manyQ
        (R := R) (k := k) (ε := ε) (M := M)
        (by omega) hε hM hWordDomOne hWordDomMany)

/-- Sharpest packaged endpoint on the current PT mixed route, with the
deleted-column mean side reduced to the explicit crossing/spherical `D / d`
Catalan error estimate. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCatalanErrorBoundFrontierInputs_withPTMixedError_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample k)
    (M : ℝ)
    (hMixed :
      mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M)
    (hMomentDeviation :
      lowerConcreteDeletedBackgroundMomentDeviationTailBound R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCoreFrontierInputs_withPTMixedError_splitMixedWordBudget
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio_of_errorBound
        R.sample k hMeanError)
      M hMixed hMomentDeviation

/-- Same split PT mixed-word route with the mean side reduced to the explicit
deleted-column Catalan `D / d` error estimate and the background typicality
supplied by the two-trace Wick/Chebyshev tail. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCatalanErrorBoundFrontierInputs_withPTMixedError_splitMixedWordBudget_secondMomentWickMomentTail
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample k)
    (M : ℝ)
    (hMixed :
      mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M)
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCoreFrontierInputs_withPTMixedError_splitMixedWordBudget_secondMomentWickMomentTail
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio_of_errorBound
        R.sample k hMeanError)
      M hMixed hMomentSecond

/-- Same sharp PT mixed route with the mean-side input stated as the explicit
crossing/spherical diagram estimate from the deleted-column Wick expansion. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndExplicitCatalanDiagramFrontierInputs_withPTMixedError_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hMeanDiagram :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample k m Wcard Cmodel)
    (M : ℝ)
    (hMixed :
      mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M)
    (hMomentDeviation :
      lowerConcreteDeletedBackgroundMomentDeviationTailBound R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCatalanErrorBoundFrontierInputs_withPTMixedError_splitMixedWordBudget
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio_of_explicitDiagramBound
        R.sample k m Wcard Cmodel hMeanDiagram)
      M hMixed hMomentDeviation

/-- Same split PT mixed-word route with the mean side stated as the explicit
crossing/spherical diagram estimate and the moment tail stated as the
two-trace Wick/Chebyshev deviation estimate. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndExplicitCatalanDiagramFrontierInputs_withPTMixedError_splitMixedWordBudget_secondMomentWickMomentTail
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hMeanDiagram :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample k m Wcard Cmodel)
    (M : ℝ)
    (hMixed :
      mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M)
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCatalanErrorBoundFrontierInputs_withPTMixedError_splitMixedWordBudget_secondMomentWickMomentTail
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio_of_explicitDiagramBound
        R.sample k m Wcard Cmodel hMeanDiagram)
      M hMixed hMomentSecond

/-- Same PT mixed-error endpoint with the mean side stated as the explicit
crossing/spherical diagram estimate and the moment tail stated as the
two-trace Wick/Chebyshev deviation estimate. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndExplicitCatalanDiagramFrontierInputs_withPTMixedError_secondMomentWickMomentTail
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hMeanDiagram :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample k m Wcard Cmodel)
    (A M : ℝ)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithError R k ε
        (fun _a _slack d => lowerPartialTransposeMixedErrorD k A M d))
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCatalanErrorBoundFrontierInputs_withPTMixedError_secondMomentWickMomentTail
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio_of_explicitDiagramBound
        R.sample k m Wcard Cmodel hMeanDiagram)
      A M hMixedEnvelope hMomentSecond

/-- One-shot endpoint adapter for the current paper-facing PT frontier stack.

This theorem consumes the remaining named hard inputs from the audit:

* the concrete Catalan-error estimate for the deleted-column mean;
* a concentration source strong enough to imply the `C / d²` background
  typicality budget;
* the repaired PT mixed-error envelope.

At this Lean abstraction layer the two-trace expansion name is the same grouped
Wick/Chebyshev predicate as the variance name, so the endpoint carries the
stronger concentration source and derives the polynomial tail internally. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTWickAndDeviationStacks_withPTMixedError
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample k)
    (hExponentialTail :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R k)
    (M : ℝ)
    (hMixed :
      mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndDeletedColumnMomentFrontierInputs_withMixedError
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerDeletedColumnBackgroundMomentHasCatalanLimit_of_fromRatio
        (R := R) (k := k)
        (lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio_of_errorBound
          R.sample k hMeanError))
      (fun a slack d => lowerPartialTransposeMixedErrorD k (a + slack) M d)
      (lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithPTError_of_mixed_noL_atLeastTwoQ_ge_neg_errMix
        R k ε M hMixed)
      (by
        intro a _ha slack _hslack η hη
        exact
          lowerPartialTransposeMixedErrorD_eventually_le
            (k := k) hk3 (a + slack) M η hη)
      (lowerConcreteDeletedBackgroundMomentDeviationTailBound_of_exponentialDeviationTailBound
        R k hExponentialTail)

/-- One-shot endpoint adapter for the paper-facing PT frontier stack with the
mixed side split into its word-level and finite-budget obligations.

This is the fully separated endpoint dependency shape: the hard PT mean theorem
and the background concentration source stay visible, while the repaired mixed
supplier is provided by pointwise PT word bounds plus the scalar `errMix`
budget. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTWickAndDeviationStacks_withPTMixedError_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample k)
    (hExponentialTail :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R k)
    (M : ℝ)
    (hMixed :
      mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTWickAndDeviationStacks_withPTMixedError
      (R := R) (k := k) (ε := ε) hk3 hε
      hMeanError
      hExponentialTail
      M hMixed

/-- Paper-facing PT endpoint with the background tail reduced from the
stronger exponential wrapper to the actual variance/Chebyshev frontier.

This is the sharp public wrapper matching `LFC-PPT-008`: the endpoint no
longer needs the stronger named concentration source once the paper-facing
variance theorem `Var(M_d) ≤ C / d^4` is available. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTWickAndVarianceStack_withPTMixedError_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample k)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (M : ℝ)
    (hMixed :
      mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndCatalanErrorBoundFrontierInputs_withPTMixedError_splitMixedWordBudget_secondMomentWickMomentTail
      (R := R) (k := k) (ε := ε) hk3 hε
      hMeanError
      M hMixed
      (lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound_of_deletedColumnSphericalMoment_variance_le_const_div_d4
        R k hVariance)

/-- Paper-facing PT endpoint stated directly in terms of the exact
deleted-column spherical Catalan mean theorem and the grouped second-moment
Wick/Chebyshev tail.

This is the cleanest packaged endpoint currently available without proving the
remaining hard kernels internally: the mean input is already the manuscript
statement
`E[(d^2)^(k-1) Tr(((Y_dY_d*)^Γ)^k)] → ptCatalanMean k λ`,
the deviation input is the `C / d²` Wick/Chebyshev tail, and the mixed side is
the repaired PT split-word supplier. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanMeanAndSecondMomentWickStack_withPTMixedError_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMean :
      deletedColumnSphericalMean_tendsto_ptCatalan R.sample k R.lam)
    (M : ℝ)
    (hMixed :
      mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M)
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  have hk : 1 < k := lt_of_lt_of_le (by decide : 1 < 3) hk3
  rcases
    lowerConcreteDeletedBackgroundMomentSecondMomentWickBadTailBound_of_deviationTailBound
      (R := R) (k := k) hMomentSecond with
    ⟨C, _hC, hMomentBad⟩
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_concreteScalarChoices_sphereBetaScaleBudget_withMomentBudgetAndMixedError
      (R := R) (k := k) (ε := ε) hk hε
      (bMoment := lowerConcreteMomentPolynomialBound C R k)
      (errMix := fun a slack d => lowerPartialTransposeMixedErrorD k (a + slack) M d)
      (lower_unitProfile_canonicalDirection_concreteChoices_of_traceStability
        hk hε
        (lowerConcreteCanonicalCapSpikeTraceStability_of_overlapLower
          (lt_of_lt_of_le (by decide : 1 < 3) hk3)
          hε
          (lowerConcreteCanonicalCapTracePowerOverlapLower_of_traceDominatesCoordinateOverlap
            (lowerConcreteRankOneProjectorGammaTracePowerDominatesCoordinateOverlap_of_leftDensityDiagonalPower
              (lowerConcreteRankOneProjectorGammaTracePowerDominatesLeftDensityDiagonalPower_closed k)))))
      (lower_scaleBudget_concreteChoices_of_meanPositivePartEventuallyBounded
        (R := R) (k := k) (ε := ε) hk3 hε
        (lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded_of_deletedColumnMomentAsymptotic
          R k
          (lowerDeletedColumnBackgroundMomentHasCatalanLimit_of_deletedColumnSphericalMean_tendsto_ptCatalan
            R.sample k R.lam hMean)))
      (lower_mixedLowerOnSphere_concreteChoices_of_localExpansionEnvelopeOnSphereWithError
        (R := R) (k := k) (ε := ε)
        (fun a slack d => lowerPartialTransposeMixedErrorD k (a + slack) M d)
        (lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithPTError_of_mixed_noL_atLeastTwoQ_ge_neg_errMix
          R k ε M hMixed))
      (by
        intro a _ha slack _hslack η hη
        exact
          lowerPartialTransposeMixedErrorD_eventually_le
            (k := k) hk3 (a + slack) M η hη)
      lower_referenceCone_BipIndex_Fin_eventually_concreteChoices
      hMomentBad
      (lower_concrete_polynomialMomentSmall C R k)

/-- Sharpest paper-facing packaged endpoint currently available on the repaired
PT route.

Compared with
`...of_paperFacingPTWickAndVarianceStack_withPTMixedError_splitMixedWordBudget`,
the mean side is no longer the explicit Catalan-error wrapper but the exact
deleted-column spherical PT Catalan theorem itself.  The remaining visible
theorem-strength inputs are therefore the true hard leaves: mean theorem,
variance theorem, and the repaired mixed supplier. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanMeanAndVarianceStack_withPTMixedError_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMean :
      deletedColumnSphericalMean_tendsto_ptCatalan R.sample k R.lam)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (M : ℝ)
    (hMixed :
      mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanMeanAndSecondMomentWickStack_withPTMixedError_splitMixedWordBudget
      (R := R) (k := k) (ε := ε) hk3 hε
      hMean
      M hMixed
      (lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound_of_deletedColumnSphericalMoment_variance_le_const_div_d4
        R k hVariance)

/-- Eventual smallness of an abstract mixed error, uniformly in the spike
window parameters used by the lower endpoint.

This is the scalar half of the repaired mixed frontier. It is deliberately
kept separate from the local-expansion envelope: smallness of a sequence does
not by itself control the mixed words. -/
def lowerConcreteMixedErrorEventuallySmall
    (k : ℕ) (ε : ℝ) (errMix : ℝ → ℝ → ℕ → ℝ) : Prop :=
  ∀ a : ℝ, spikeRoot k ε < a →
    ∀ slack : ℝ, 0 < slack →
      ∀ η : ℝ, 0 < η →
        ∀ᶠ d in atTop, errMix a slack d ≤ η

/-- Termwise `o(1)` bounds imply `o(1)` smallness of the exact finite mixed
word sum.

This is only finite-sum bookkeeping: the remaining theorem-strength mixed
input is the termwise scalar convergence for each mixed local-expansion word. -/
theorem lowerConcreteMixedErrorEventuallySmall_of_filteredSum_termwise_tendsto
    {k : ℕ} {ε : ℝ}
    {bound : ℝ → ℝ → ℕ → (Fin k → LocalExpansionLetter) → ℝ}
    (hTerm :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ w : Fin k → LocalExpansionLetter,
            localWordIsMixed w →
              Tendsto (fun d : ℕ => bound a slack d w) atTop (nhds 0)) :
    lowerConcreteMixedErrorEventuallySmall k ε
      (fun a slack d => localMixedWordFilteredSum (k := k) (bound a slack d)) := by
  intro a ha slack hslack η hη
  have hsum :
      Tendsto
        (fun d : ℕ =>
          localMixedWordFilteredSum (k := k) (bound a slack d))
        atTop (nhds 0) := by
    classical
    unfold localMixedWordFilteredSum
    have hsum :
        Tendsto
          (fun d : ℕ =>
            ∑ w : Fin k → LocalExpansionLetter,
              if localWordIsMixed w then bound a slack d w else 0)
          atTop
          (nhds
            (∑ _w : Fin k → LocalExpansionLetter, (0 : ℝ))) := by
      refine tendsto_finset_sum Finset.univ ?_
      intro w _hw
      by_cases hmix : localWordIsMixed w
      · simpa [hmix] using hTerm a ha slack hslack w hmix
      · simp [hmix]
    simpa using hsum
  have hIio : Set.Iio η ∈ nhds (0 : ℝ) := Iio_mem_nhds hη
  filter_upwards [hsum.eventually hIio] with d hd
  exact le_of_lt hd

/-- Each literal partial-transpose mixed-word envelope is `o(1)`.

This extracts a single mixed word from the already proved total PT error:
the word envelope is nonnegative, is bounded by the finite filtered PT sum,
and that filtered sum is bounded by `lowerPartialTransposeMixedErrorD`, which
tends to zero. -/
theorem lowerPartialTransposeMixedWordBoundD_tendsto_zero
    {k : ℕ} (hk3 : 3 ≤ k) {A M : ℝ}
    (hA : 0 ≤ A) (hM : 0 ≤ M)
    (w : Fin k → LocalExpansionLetter) (hmix : localWordIsMixed w) :
    Tendsto
      (fun d : ℕ => lowerPartialTransposeMixedWordBoundD k A M d w)
      atTop (nhds 0) := by
  refine
    squeeze_zero'
      (g := fun d : ℕ => lowerPartialTransposeMixedErrorD k A M d) ?_ ?_ ?_
  · exact
      Eventually.of_forall fun d =>
        lowerPartialTransposeMixedWordBoundD_nonneg
          (k := k) (d := d) (A := A) (M := M) hA hM w
  · refine Eventually.of_forall ?_
    intro d
    have hsingle :
        lowerPartialTransposeMixedWordBoundD k A M d w ≤
          localMixedWordFilteredSum (k := k)
            (fun w' => lowerPartialTransposeMixedWordBoundD k A M d w') :=
      localMixedWordFilteredSum_single_le
        (k := k)
        (fun w' => lowerPartialTransposeMixedWordBoundD k A M d w')
        (fun w' _hw' =>
          lowerPartialTransposeMixedWordBoundD_nonneg
            (k := k) (d := d) (A := A) (M := M) hA hM w')
        w hmix
    have hbudget :
        localMixedWordFilteredSum (k := k)
            (fun w' => lowerPartialTransposeMixedWordBoundD k A M d w') ≤
          lowerPartialTransposeMixedErrorD k A M d := by
      unfold lowerPartialTransposeMixedWordBoundD lowerPartialTransposeMixedErrorD
      exact
        lowerPartialTransposeMixedWordBoundN_budget
          (k := k) (A := A) (M := M) (N := (d : ℝ) ^ 2)
          hA hM (by positivity)
    exact le_trans hsingle hbudget
  · exact lowerPartialTransposeMixedErrorD_tendsto_zero (k := k) hk3 A M

/-- Termwise smallness of the literal PT mixed-word envelope in the lower
spike window. -/
theorem lowerPartialTransposeMixedWordBoundD_termwise_tendsto
    {k : ℕ} {ε M : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε) (hM : 0 ≤ M) :
    ∀ a : ℝ, spikeRoot k ε < a →
      ∀ slack : ℝ, 0 < slack →
        ∀ w : Fin k → LocalExpansionLetter,
          localWordIsMixed w →
            Tendsto
              (fun d : ℕ =>
                lowerPartialTransposeMixedWordBoundD k (a + slack) M d w)
              atTop (nhds 0) := by
  intro a ha slack hslack w hmix
  have hk0 : 0 < k := lt_of_lt_of_le (by norm_num : 0 < 3) hk3
  have ha_nonneg : 0 ≤ a :=
    le_of_lt (lt_trans (spikeRoot_pos hk0 hε) ha)
  have hA : 0 ≤ a + slack := by linarith
  exact
    lowerPartialTransposeMixedWordBoundD_tendsto_zero
      (k := k) hk3 hA hM w hmix

/-- Honest mixed frontier used by the repaired paper-facing endpoint.

It packages the two facts that must refer to the same error sequence: the
sphere-supported mixed local-expansion envelope and the eventual smallness of
that envelope. -/
def lowerConcreteMixedErrorFrontier
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) (ε : ℝ) (errMix : ℝ → ℝ → ℕ → ℝ) : Prop :=
  lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithError R k ε errMix ∧
    lowerConcreteMixedErrorEventuallySmall k ε errMix

/-- Unpack the sphere-supported local-expansion half of the honest lower
mixed frontier. -/
theorem lowerConcreteMixedErrorFrontier.envelope
    {R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime}
    {k : ℕ} {ε : ℝ} {errMix : ℝ → ℝ → ℕ → ℝ}
    (hFrontier : lowerConcreteMixedErrorFrontier R k ε errMix) :
    lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithError R k ε errMix :=
  hFrontier.1

/-- Unpack the scalar `o(1)` half of the honest lower mixed frontier.

This projection is intentionally separate from `envelope`: the mixed input is
not just smallness of an error sequence, but smallness of the same error
sequence that controls the local mixed-word remainder on the Frobenius sphere. -/
theorem lowerConcreteMixedErrorFrontier.eventuallySmall
    {R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime}
    {k : ℕ} {ε : ℝ} {errMix : ℝ → ℝ → ℕ → ℝ}
    (hFrontier : lowerConcreteMixedErrorFrontier R k ε errMix) :
    lowerConcreteMixedErrorEventuallySmall k ε errMix :=
  hFrontier.2

/-- Fixed-`M` PT mixed suppliers still give an honest mixed frontier when such
suppliers have been proved independently.

This is a compatibility wrapper only. It does not assert that the current
runtime background threshold is dominated by a fixed scalar `M`; it merely
packages an already-proved fixed-`M` mixed supplier together with the known
`o(1)` scalar PT error. -/
theorem lowerConcreteMixedErrorFrontier_of_mixed_noL_atLeastTwoQ_ge_neg_errMix
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (M : ℝ)
    (hMixed : mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M) :
    lowerConcreteMixedErrorFrontier R k ε
      (fun a slack d => lowerPartialTransposeMixedErrorD k (a + slack) M d) := by
  constructor
  · exact
      lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithPTError_of_mixed_noL_atLeastTwoQ_ge_neg_errMix
        R k ε M hMixed
  · intro a _ha slack _hslack η hη
    exact
      lowerPartialTransposeMixedErrorD_eventually_le
        (k := k) hk3 (a + slack) M η hη

/-- Word-by-word bounds plus a finite scalar budget give the honest mixed
frontier when the same error sequence is eventually small.

This is the non-opaque construction of `lowerConcreteMixedErrorFrontier`: it
keeps the deterministic mixed proof split into the local word estimates, the
finite budget, and the scalar `o(1)` fact for the selected error sequence. -/
theorem lowerConcreteMixedErrorFrontier_of_wordBoundsAndBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk : 1 ≤ k)
    (bound : ℝ → ℝ → ℕ → (Fin k → LocalExpansionLetter) → ℝ)
    (errMix : ℝ → ℝ → ℕ → ℝ)
    (hWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k ε bound)
    (hBudget :
      lowerConcreteMixedWordBudgetWithError R k ε bound errMix)
    (hSmall :
      lowerConcreteMixedErrorEventuallySmall k ε errMix) :
    lowerConcreteMixedErrorFrontier R k ε errMix := by
  constructor
  · exact
      lower_concreteMixedLocalExpansionEnvelopeOnSphereWithError_of_wordBounds
        (R := R) (k := k) (ε := ε) hk bound errMix hWord hBudget
  · exact hSmall

/-- The literal partial-transpose mixed error is eventually small in the exact
shape required by `lowerConcreteMixedErrorFrontier`. -/
theorem lowerConcreteMixedErrorEventuallySmall_of_lowerPartialTransposeMixedErrorD
    {k : ℕ} {ε M : ℝ} (hk3 : 3 ≤ k) :
    lowerConcreteMixedErrorEventuallySmall k ε
      (fun a slack d => lowerPartialTransposeMixedErrorD k (a + slack) M d) := by
  intro a _ha slack _hslack η hη
  exact
    lowerPartialTransposeMixedErrorD_eventually_le
      (k := k) hk3 (a + slack) M η hη

/-- A pointwise literal partial-transpose word estimate supplies the honest
mixed frontier.

The finite PT budget and the scalar `o(1)` smallness are already proved; the
only remaining mixed-specific input here is the word-by-word PT estimate on
the Frobenius sphere. -/
theorem lowerConcreteMixedErrorFrontier_of_PTPointwiseWordBound
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε M : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε) (hM : 0 ≤ M)
    (hWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k ε
        (fun a slack d =>
          lowerPartialTransposeMixedWordBoundD k (a + slack) M d)) :
    lowerConcreteMixedErrorFrontier R k ε
      (fun a slack d => lowerPartialTransposeMixedErrorD k (a + slack) M d) := by
  refine
    lowerConcreteMixedErrorFrontier_of_wordBoundsAndBudget
      (R := R) (k := k) (ε := ε) (by omega)
      (fun a slack d =>
        lowerPartialTransposeMixedWordBoundD k (a + slack) M d)
      (fun a slack d =>
        lowerPartialTransposeMixedErrorD k (a + slack) M d)
      hWord ?_ ?_
  · exact
      lowerConcreteMixedWordBudgetWithPTError_literal
        (R := R) (k := k) (ε := ε) (M := M)
        (by omega) hε hM
  · exact
      lowerConcreteMixedErrorEventuallySmall_of_lowerPartialTransposeMixedErrorD
        (k := k) (ε := ε) (M := M) hk3

/-- Direct scalar one-`Q` and many-`Q` estimates supply the honest literal PT
mixed frontier.

This is the canonical mixed-frontier adapter below the pointwise PT word
estimate: the finite split into `L`/one-`Q`/many-`Q` words, the PT coefficient
budget, and the PT error smallness are all supplied internally.  The remaining
mixed theorem-strength leaves are exactly the two direct scalar trace bounds. -/
theorem lowerConcreteMixedErrorFrontier_of_PTDirectScalarCases
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε M : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε) (hM : 0 ≤ M)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R k ε M)
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R k ε M) :
    lowerConcreteMixedErrorFrontier R k ε
      (fun a slack d => lowerPartialTransposeMixedErrorD k (a + slack) M d) := by
  exact
    lowerConcreteMixedErrorFrontier_of_PTPointwiseWordBound
      (R := R) (k := k) (ε := ε) (M := M) hk3 hε hM
      (lowerConcreteMixedWordPointwiseBoundOnSphere_withPTError_of_directScalarCases
        (R := R) (k := k) (ε := ε) (M := M)
        (by omega) hε hM hOne hMany)

/-- Direct PT scalar cases supply the existential mixed frontier shape consumed
by endpoint wrappers.

This is the live replacement for the dead scale-comparison package: the witness
is still the literal partial-transpose mixed error, but the assumptions are the
two direct trace estimates rather than the false fixed-`M` scale comparisons. -/
theorem exists_lowerConcreteMixedErrorFrontier_of_PTDirectScalarCases
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε M : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε) (hM : 0 ≤ M)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R k ε M)
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R k ε M) :
    ∃ errMix : ℝ → ℝ → ℕ → ℝ,
      lowerConcreteMixedErrorFrontier R k ε errMix := by
  refine ⟨fun a slack d =>
    lowerPartialTransposeMixedErrorD k (a + slack) M d, ?_⟩
  exact
    lowerConcreteMixedErrorFrontier_of_PTDirectScalarCases
      (R := R) (k := k) (ε := ε) (M := M)
      hk3 hε hM hOne hMany

/-- The two PT scale comparisons supply the honest literal PT mixed frontier.

This is the scalar-comparison version of
`lowerConcreteMixedErrorFrontier_of_PTDirectScalarCases`: the local one-`Q`
and many-`Q` trace estimates, finite word split, PT coefficient budget, and PT
error smallness are all adapter-supplied.  The remaining mixed leaves are the
two endpoint-facing scale comparisons. -/
theorem lowerConcreteMixedErrorFrontier_of_PTScaleComparisons
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε M : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε) (hM : 0 ≤ M)
    (hOneScale :
      lowerConcretePTMixedWordOneQScaleComparison R k ε M)
    (hManyScale :
      lowerConcretePTMixedWordManyQScaleComparison R k ε M) :
    lowerConcreteMixedErrorFrontier R k ε
      (fun a slack d => lowerPartialTransposeMixedErrorD k (a + slack) M d) := by
  exact
    lowerConcreteMixedErrorFrontier_of_PTDirectScalarCases
      (R := R) (k := k) (ε := ε) (M := M) hk3 hε hM
      (lowerConcretePTMixedWordOneQDirectScalarBound_of_scaleComparison
        (R := R) (k := k) (ε := ε) (M := M) hk3 hε hOneScale)
      (lowerConcretePTMixedWordManyQDirectScalarBound_of_scaleComparison
        (R := R) (k := k) (ε := ε) (M := M) hk3 hε hManyScale)

/-- The two PT scale comparisons supply the existential mixed frontier shape
consumed by the sharp upper route.

This is only packaging: the chosen witness is the literal partial-transpose
mixed error `lowerPartialTransposeMixedErrorD k (a + slack) M d`.  The real
mixed work remains the one-`Q` and many-`Q` scale comparisons. -/
theorem exists_lowerConcreteMixedErrorFrontier_of_PTScaleComparisons
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε M : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε) (hM : 0 ≤ M)
    (hOneScale :
      lowerConcretePTMixedWordOneQScaleComparison R k ε M)
    (hManyScale :
      lowerConcretePTMixedWordManyQScaleComparison R k ε M) :
    ∃ errMix : ℝ → ℝ → ℕ → ℝ,
      lowerConcreteMixedErrorFrontier R k ε errMix := by
  refine ⟨fun a slack d =>
    lowerPartialTransposeMixedErrorD k (a + slack) M d, ?_⟩
  exact
    lowerConcreteMixedErrorFrontier_of_PTScaleComparisons
      (R := R) (k := k) (ε := ε) (M := M)
      hk3 hε hM hOneScale hManyScale

/-- Runtime-native mixed suppliers give the honest mixed frontier once their
exact finite runtime error is known to be `o(1)`.

This is the repaired replacement for the fixed-`M` scalar domination route:
the local word envelope is proved internally, and the only remaining mixed
leaf is smallness of the same runtime error. -/
theorem lowerConcreteMixedErrorFrontier_of_runtimeWordError
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hRuntimeSmall :
      lowerConcreteMixedErrorEventuallySmall k ε
        (lowerConcreteMixedRuntimeWordError R k)) :
    lowerConcreteMixedErrorFrontier R k ε
      (lowerConcreteMixedRuntimeWordError R k) := by
  constructor
  · exact
      lower_concreteMixedLocalExpansionEnvelopeOnSphereWithRuntimeWordError
        (R := R) (k := k) (ε := ε) hk3 hε
  · exact hRuntimeSmall

/-- The runtime-native mixed-error smallness frontier is impossible at length
three.

This restates the diagnostic obstruction in the exact packaged predicate used
by `lowerConcreteMixedErrorFrontier_of_runtimeWordError`: the deterministic
runtime envelope is available, but its finite mixed error is not an `o(1)`
frontier at `k = 3`. -/
theorem lowerConcreteMixedRuntimeWordError_three_not_errorEventuallySmall
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {ε : ℝ} (hε : 0 < ε) :
    ¬ lowerConcreteMixedErrorEventuallySmall 3 ε
      (lowerConcreteMixedRuntimeWordError R 3) := by
  exact
    lowerConcreteMixedRuntimeWordError_three_not_uniformEventuallySmall
      (R := R) (ε := ε) hε

/-- The runtime-native mixed error cannot be the honest mixed frontier at
length three.

The deterministic runtime envelope is available, but the same runtime error is
not eventually small.  Hence the repaired lower route cannot close by choosing
`errMix = lowerConcreteMixedRuntimeWordError R 3`; it needs a genuinely
vanishing mixed envelope or a sharper favourable event. -/
theorem lowerConcreteMixedRuntimeWordError_three_not_mixedErrorFrontier
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {ε : ℝ} (hε : 0 < ε) :
    ¬ lowerConcreteMixedErrorFrontier R 3 ε
      (lowerConcreteMixedRuntimeWordError R 3) := by
  intro hFrontier
  exact
    lowerConcreteMixedRuntimeWordError_three_not_errorEventuallySmall
      (R := R) (ε := ε) hε hFrontier.2

/-- Preferred no-reference lower endpoint on the survivor-core mean branch and
the honest mixed-error frontier.

This avoids the diagnostic fixed-`M` runtime-domination comparison entirely:
the mixed side is supplied by one explicit error envelope together with
eventual smallness of that same envelope.  The remaining theorem-strength
inputs are the geodesic/noncrossing survivor analysis, the exponential
background concentration source, and the mixed frontier for `errMix`. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withMixedErrorFrontier_exponentialDeviationStack
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    (hExponentialTail :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R k)
    (errMix : ℝ → ℝ → ℕ → ℝ)
    (hMixedFrontier : lowerConcreteMixedErrorFrontier R k ε errMix) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  rcases hMixedFrontier with ⟨hMixedEnvelope, hMixedSmall⟩
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndDeletedColumnMomentFrontierInputs_withMixedError
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerDeletedColumnBackgroundMomentHasCatalanLimit_of_fromRatio
        (R := R) (k := k)
        (lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio_of_permutationWickLimit
          R.sample k
          (lowerDeletedColumnBackgroundMomentPermutationWickLimit_fromRatio_of_gaussianRadialFormula_and_geodesicSurvivors
            R.sample k
            (lowerDeletedColumnPTGaussianRadialFormula_fromRatio_currentPredicate
              R.sample k)
            hSurvivors)))
      errMix hMixedEnvelope hMixedSmall
      (lowerConcreteDeletedBackgroundMomentDeviationTailBound_of_exponentialDeviationTailBound
        R k hExponentialTail)

/-- Paper-facing PT endpoint with the mixed side stated at the honest abstract
error-envelope level.

This is the route to use when the concrete runtime envelope is not known to be
dominated by a fixed paper-facing scalar `M`.  It keeps the two hard PT inputs
visible (`hMean` and the grouped second-moment Wick/Chebyshev tail), and it
requires exactly the two logically necessary mixed facts: a sphere-supported
lower envelope and eventual smallness of that same envelope. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanMeanAndSecondMomentWickStack_withMixedError_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMean :
      deletedColumnSphericalMean_tendsto_ptCatalan R.sample k R.lam)
    (errMix : ℝ → ℝ → ℕ → ℝ)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithError R k ε errMix)
    (hMixedSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errMix a slack d ≤ η)
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  have hk : 1 < k := lt_of_lt_of_le (by decide : 1 < 3) hk3
  rcases
    lowerConcreteDeletedBackgroundMomentSecondMomentWickBadTailBound_of_deviationTailBound
      (R := R) (k := k) hMomentSecond with
    ⟨C, _hC, hMomentBad⟩
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_concreteScalarChoices_sphereBetaScaleBudget_withMomentBudgetAndMixedError
      (R := R) (k := k) (ε := ε) hk hε
      (bMoment := lowerConcreteMomentPolynomialBound C R k)
      (errMix := errMix)
      (lower_unitProfile_canonicalDirection_concreteChoices_of_traceStability
        hk hε
        (lowerConcreteCanonicalCapSpikeTraceStability_of_overlapLower
          (lt_of_lt_of_le (by decide : 1 < 3) hk3)
          hε
          (lowerConcreteCanonicalCapTracePowerOverlapLower_of_traceDominatesCoordinateOverlap
            (lowerConcreteRankOneProjectorGammaTracePowerDominatesCoordinateOverlap_of_leftDensityDiagonalPower
              (lowerConcreteRankOneProjectorGammaTracePowerDominatesLeftDensityDiagonalPower_closed k)))))
      (lower_scaleBudget_concreteChoices_of_meanPositivePartEventuallyBounded
        (R := R) (k := k) (ε := ε) hk3 hε
        (lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded_of_deletedColumnMomentAsymptotic
          R k
          (lowerDeletedColumnBackgroundMomentHasCatalanLimit_of_deletedColumnSphericalMean_tendsto_ptCatalan
            R.sample k R.lam hMean)))
      (lower_mixedLowerOnSphere_concreteChoices_of_localExpansionEnvelopeOnSphereWithError
        (R := R) (k := k) (ε := ε)
        errMix hMixedEnvelope)
      hMixedSmall
      lower_referenceCone_BipIndex_Fin_eventually_concreteChoices
      hMomentBad
      (lower_concrete_polynomialMomentSmall C R k)

/-- Sharpest paper-facing packaged endpoint on the honest abstract
mixed-error route.

This is the preferred public endpoint when the mixed side has been proved as an
actual vanishing error envelope.  It avoids the false fixed-`M` runtime scalar
comparison entirely: the mixed assumptions are exactly the envelope theorem and
the eventual-smallness theorem for the same `errMix`. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanMeanAndVarianceStack_withMixedError_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMean :
      deletedColumnSphericalMean_tendsto_ptCatalan R.sample k R.lam)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (errMix : ℝ → ℝ → ℕ → ℝ)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithError R k ε errMix)
    (hMixedSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errMix a slack d ≤ η) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanMeanAndSecondMomentWickStack_withMixedError_splitMixedWordBudget
      (R := R) (k := k) (ε := ε) hk3 hε
      hMean
      errMix hMixedEnvelope hMixedSmall
      (lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound_of_deletedColumnSphericalMoment_variance_le_const_div_d4
        R k hVariance)

/-- Preferred paper-facing endpoint with the mixed side supplied as a packaged
honest frontier.

This is the clean public form after the repair: the remaining debts are exactly
the PT Catalan mean theorem, the PT variance theorem, and a mixed frontier whose
envelope and smallness are tied to the same `errMix`. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanMeanAndVarianceStack_withMixedErrorFrontier_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMean :
      deletedColumnSphericalMean_tendsto_ptCatalan R.sample k R.lam)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (errMix : ℝ → ℝ → ℕ → ℝ)
    (hMixedFrontier : lowerConcreteMixedErrorFrontier R k ε errMix) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  rcases hMixedFrontier with ⟨hMixedEnvelope, hMixedSmall⟩
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanMeanAndVarianceStack_withMixedError_splitMixedWordBudget
      (R := R) (k := k) (ε := ε) hk3 hε
      hMean hVariance errMix hMixedEnvelope hMixedSmall

/-- Concrete `k = 3` form of the preferred paper-facing lower endpoint with
the mixed frontier split into its two actual components.

This is the sharpest structural form of the current lower route: the remaining
mixed obligations are the sphere-supported local expansion envelope and
eventual smallness for the same `errMix`, both at length three. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanMeanAndVarianceStack_k3_withMixedErrorComponents_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {ε : ℝ} (hε : 0 < ε)
    (hMean :
      deletedColumnSphericalMean_tendsto_ptCatalan R.sample 3 R.lam)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (errMix : ℝ → ℝ → ℕ → ℝ)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithError R 3 ε errMix)
    (hMixedSmall :
      ∀ a : ℝ, spikeRoot 3 ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errMix a slack d ≤ η) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate 3 R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R 3) 3 d) /
            spikeSpeed 3 d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanMeanAndVarianceStack_withMixedError_splitMixedWordBudget
      (R := R) (k := 3) (ε := ε) (by norm_num) hε
      hMean hVariance errMix hMixedEnvelope hMixedSmall

/-- Concrete length-three lower endpoint with the mean side reduced to the
explicit Catalan-error/Wick frontier.

This replaces the broad PT Catalan mean theorem by the current sharp
mean-side input: the deleted-column `D / d` Catalan-error estimate. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanErrorMeanAndVarianceStack_k3_withMixedErrorComponents_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {ε : ℝ} (hε : 0 < ε)
    (hMeanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample 3)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (errMix : ℝ → ℝ → ℕ → ℝ)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithError R 3 ε errMix)
    (hMixedSmall :
      ∀ a : ℝ, spikeRoot 3 ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errMix a slack d ≤ η) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate 3 R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R 3) 3 d) /
            spikeSpeed 3 d := by
  have hMean :
      deletedColumnSphericalMean_tendsto_ptCatalan R.sample 3 R.lam :=
    deletedColumnSphericalMean_tendsto_ptCatalan_of_lowerDeletedColumnBackgroundMomentHasCatalanLimit
      R.sample 3 R.lam
      (lowerDeletedColumnBackgroundMomentHasCatalanLimit_of_fromRatio_errorBound
        R 3 hMeanError)
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanMeanAndVarianceStack_k3_withMixedErrorComponents_splitMixedWordBudget
      (R := R) (ε := ε) hε
      hMean hVariance errMix hMixedEnvelope hMixedSmall

/-- Concrete length-three lower endpoint with the background tail reduced to
the exponential-deviation frontier.

This replaces the broad variance/Chebyshev predicate by the stronger
exponential deviation estimate already used elsewhere in the lower pipeline. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanErrorMeanAndExponentialTailStack_k3_withMixedErrorComponents_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {ε : ℝ} (hε : 0 < ε)
    (hMeanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample 3)
    (hExpTail :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R 3)
    (errMix : ℝ → ℝ → ℕ → ℝ)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithError R 3 ε errMix)
    (hMixedSmall :
      ∀ a : ℝ, spikeRoot 3 ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errMix a slack d ≤ η) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate 3 R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R 3) 3 d) /
            spikeSpeed 3 d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanErrorMeanAndVarianceStack_k3_withMixedErrorComponents_splitMixedWordBudget
      (R := R) (ε := ε) hε
      hMeanError
      (deletedColumnSphericalMoment_variance_le_const_div_d4_of_exponentialDeviationTailBound
        R 3 hExpTail)
      errMix hMixedEnvelope hMixedSmall

/-- Concrete `k = 3` form of the preferred paper-facing lower endpoint.

This removes the moment-length bookkeeping hypothesis `3 ≤ k` from the public
frontier.  The remaining theorem-strength inputs are still the PT Catalan mean
theorem at length three, the PT variance theorem at length three, and an honest
mixed frontier whose envelope and eventual-smallness statements use the same
`errMix`. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanMeanAndVarianceStack_k3_withMixedErrorFrontier_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {ε : ℝ} (hε : 0 < ε)
    (hMean :
      deletedColumnSphericalMean_tendsto_ptCatalan R.sample 3 R.lam)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (errMix : ℝ → ℝ → ℕ → ℝ)
    (hMixedFrontier : lowerConcreteMixedErrorFrontier R 3 ε errMix) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate 3 R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R 3) 3 d) /
            spikeSpeed 3 d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanMeanAndVarianceStack_withMixedErrorFrontier_splitMixedWordBudget
      (R := R) (k := 3) (ε := ε) (by norm_num) hε
      hMean hVariance errMix hMixedFrontier

/-- Paper-facing PT endpoint with the literal mixed side reduced to the two
scale comparisons.

Compared with the packaged mixed-frontier endpoint, this exposes the mixed
work at the scalar-comparison layer: the one-`Q` and many-`Q` scale
comparisons against the fixed PT envelope parameter `M`. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanMeanAndVarianceStack_withPTScaleComparisons_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMean :
      deletedColumnSphericalMean_tendsto_ptCatalan R.sample k R.lam)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (M : ℝ) (hM : 0 ≤ M)
    (hOneScale :
      lowerConcretePTMixedWordOneQScaleComparison R k ε M)
    (hManyScale :
      lowerConcretePTMixedWordManyQScaleComparison R k ε M) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanMeanAndVarianceStack_withMixedErrorFrontier_splitMixedWordBudget
      (R := R) (k := k) (ε := ε) hk3 hε
      hMean hVariance
      (fun a slack d => lowerPartialTransposeMixedErrorD k (a + slack) M d)
      (lowerConcreteMixedErrorFrontier_of_PTScaleComparisons
        (R := R) (k := k) (ε := ε) (M := M)
        hk3 hε hM hOneScale hManyScale)

/-- The paper-facing fixed-`M` scale-comparison endpoint is not an
unconditional lower-proof route at length three.

The endpoint above is a compatibility adapter for independently proved scale
comparisons.  This corollary records the verified obstruction: for `k = 3`,
the one-`Q` component of that fixed-`M` packet is already contradictory. -/
theorem lower_paperFacingPTScaleComparisonPacket_three_not_uniform
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {ε : ℝ} (hε : 0 < ε) (M : ℝ) (hM : 0 ≤ M) :
    ¬ (lowerConcretePTMixedWordOneQScaleComparison R 3 ε M ∧
      lowerConcretePTMixedWordManyQScaleComparison R 3 ε M) :=
  lowerConcretePTMixedWordScaleComparisons_three_not_uniform
    (R := R) (ε := ε) hε M hM

/-- Preferred no-reference lower endpoint on the survivor-core mean branch,
with the mixed frontier split into its two exact components.

This exposes the real mixed obligations instead of packaging them inside
`lowerConcreteMixedErrorFrontier`: a sphere-supported mixed local-expansion
envelope and eventual smallness for the same `errMix`. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withMixedErrorComponents_varianceStack
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (errMix : ℝ → ℝ → ℕ → ℝ)
    (hMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithError R k ε errMix)
    (hMixedSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errMix a slack d ≤ η) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  have hMean :
      deletedColumnSphericalMean_tendsto_ptCatalan R.sample k R.lam :=
    deletedColumnSphericalMean_tendsto_ptCatalan_of_lowerDeletedColumnBackgroundMomentHasCatalanLimit
      R.sample k R.lam
      (lowerDeletedColumnBackgroundMomentHasCatalanLimit_of_fromRatio
        (R := R) (k := k)
        (lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio_of_permutationWickLimit
          R.sample k
          (lowerDeletedColumnBackgroundMomentPermutationWickLimit_fromRatio_of_gaussianRadialFormula_and_geodesicSurvivors
            R.sample k
            (lowerDeletedColumnPTGaussianRadialFormula_fromRatio_currentPredicate
              R.sample k)
            hSurvivors)))
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanMeanAndVarianceStack_withMixedError_splitMixedWordBudget
      (R := R) (k := k) (ε := ε) hk3 hε
      hMean hVariance errMix hMixedEnvelope hMixedSmall

/-- Preferred no-reference lower endpoint with the mixed local-expansion
envelope split into word-by-word bounds plus a scalar mixed-word budget.

This is the next explicit mixed frontier below
`...withMixedErrorComponents_varianceStack`: instead of assuming the whole
sphere-supported mixed envelope, it asks for the pointwise mixed-word estimates
against `bound` and the finite-sum budget from `bound` to the same `errMix`.
-/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withMixedWordBoundsAndBudget_varianceStack
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (bound : ℝ → ℝ → ℕ → (Fin k → LocalExpansionLetter) → ℝ)
    (errMix : ℝ → ℝ → ℕ → ℝ)
    (hWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k ε bound)
    (hBudget :
      lowerConcreteMixedWordBudgetWithError R k ε bound errMix)
    (hMixedSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errMix a slack d ≤ η) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withMixedErrorComponents_varianceStack
      (R := R) (k := k) (ε := ε) hk3 hε
      hSurvivors hVariance errMix
      (lower_concreteMixedLocalExpansionEnvelopeOnSphereWithError_of_wordBounds
        (R := R) (k := k) (ε := ε) (hk := by omega)
        bound errMix hWord hBudget)
      hMixedSmall

/-- No-reference lower endpoint with the mixed local-expansion envelope split
into word-by-word bounds and a scalar mixed-word budget, on the stronger
exponential background concentration branch.

This is the word-level analogue of
`...withMixedErrorFrontier_exponentialDeviationStack`: the variance/Chebyshev
predicate is supplied from the exponential closed-deviation input, while the
mixed side is supplied from the pointwise mixed-word estimates, the finite
budget, and smallness of the same error sequence. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withMixedWordBoundsAndBudget_exponentialDeviationStack
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    (hExponentialTail :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R k)
    (bound : ℝ → ℝ → ℕ → (Fin k → LocalExpansionLetter) → ℝ)
    (errMix : ℝ → ℝ → ℕ → ℝ)
    (hWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k ε bound)
    (hBudget :
      lowerConcreteMixedWordBudgetWithError R k ε bound errMix)
    (hMixedSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errMix a slack d ≤ η) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withMixedErrorFrontier_exponentialDeviationStack
      (R := R) (k := k) (ε := ε) hk3 hε
      hSurvivors hExponentialTail errMix
      (lowerConcreteMixedErrorFrontier_of_wordBoundsAndBudget
        (R := R) (k := k) (ε := ε) (hk := by omega)
        bound errMix hWord hBudget hMixedSmall)

/-- Preferred no-reference lower endpoint on the survivor-core mean branch,
the paper-facing variance/Chebyshev concentration frontier, and the honest
mixed-error frontier.

Compared with the exponential-deviation wrapper, this exposes only the
polynomial concentration theorem actually needed by the lower route.  The
remaining theorem-strength inputs are the geodesic/noncrossing survivor
analysis, the variance/Chebyshev bound, and the mixed frontier for one matched
`errMix`. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withMixedErrorFrontier_varianceStack
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (errMix : ℝ → ℝ → ℕ → ℝ)
    (hMixedFrontier : lowerConcreteMixedErrorFrontier R k ε errMix) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  have hMean :
      deletedColumnSphericalMean_tendsto_ptCatalan R.sample k R.lam :=
    deletedColumnSphericalMean_tendsto_ptCatalan_of_lowerDeletedColumnBackgroundMomentHasCatalanLimit
      R.sample k R.lam
      (lowerDeletedColumnBackgroundMomentHasCatalanLimit_of_fromRatio
        (R := R) (k := k)
        (lowerDeletedColumnBackgroundMomentHasCatalanLimit_fromRatio_of_permutationWickLimit
          R.sample k
          (lowerDeletedColumnBackgroundMomentPermutationWickLimit_fromRatio_of_gaussianRadialFormula_and_geodesicSurvivors
            R.sample k
            (lowerDeletedColumnPTGaussianRadialFormula_fromRatio_currentPredicate
              R.sample k)
            hSurvivors)))
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withMixedErrorComponents_varianceStack
      (R := R) (k := k) (ε := ε) hk3 hε
      hSurvivors hVariance errMix hMixedFrontier.1 hMixedFrontier.2

/-- No-reference survivor/variance endpoint with the exact runtime-native mixed
error exposed.

This is a diagnostic endpoint, not the paper-facing unconditional route.  The
deterministic runtime envelope is supplied internally; the only mixed input left
is the packaged smallness predicate for `lowerConcreteMixedRuntimeWordError`.
At length three that predicate is refuted by
`lowerConcreteMixedRuntimeWordError_three_not_errorEventuallySmall`. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withRuntimeMixedError_varianceStack
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (hRuntimeSmall :
      lowerConcreteMixedErrorEventuallySmall k ε
        (lowerConcreteMixedRuntimeWordError R k)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_noReferenceClosedTraceAndPTSurvivorCoreFrontierInputs_withMixedErrorFrontier_varianceStack
      (R := R) (k := k) (ε := ε) hk3 hε
      hSurvivors hVariance
      (lowerConcreteMixedRuntimeWordError R k)
      (lowerConcreteMixedErrorFrontier_of_runtimeWordError
        (R := R) (k := k) (ε := ε) hk3 hε hRuntimeSmall)

/-- Same honest mixed-frontier endpoint, but with the mean side exposed at the
sharper deleted-column Catalan-error frontier.

This removes the broad `deletedColumnSphericalMean_tendsto_ptCatalan` input
from this route: the endpoint now asks directly for the concrete `D / d`
deleted-column mean estimate, and uses the already-verified ratio/aspect
bookkeeping for the balanced regime. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_CatalanErrorBoundAndVarianceStack_withMixedErrorFrontier_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample k)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (errMix : ℝ → ℝ → ℕ → ℝ)
    (hMixedFrontier : lowerConcreteMixedErrorFrontier R k ε errMix) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  have hMean :
      deletedColumnSphericalMean_tendsto_ptCatalan R.sample k R.lam :=
    deletedColumnSphericalMean_tendsto_ptCatalan_of_lowerDeletedColumnBackgroundMomentHasCatalanLimit
      R.sample k R.lam
      (lowerDeletedColumnBackgroundMomentHasCatalanLimit_of_fromRatio_errorBound
        R k hMeanError)
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanMeanAndVarianceStack_withMixedErrorFrontier_splitMixedWordBudget
      (R := R) (k := k) (ε := ε) hk3 hε
      hMean hVariance errMix hMixedFrontier

/-- Catalan-error, variance, and pointwise PT mixed-word endpoint.

This is the sharp middle public surface for the lower proof: the mean side is
the concrete `D / d` Catalan-error estimate, the background typicality side is
the paper-facing variance/Chebyshev theorem, and the mixed side is the
sphere-supported pointwise PT word estimate. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_CatalanErrorBoundAndVarianceStack_withPTPointwiseMixedWordBound_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample k)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (M : ℝ) (hM : 0 ≤ M)
    (hWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k ε
        (fun a slack d => lowerPartialTransposeMixedWordBoundD k (a + slack) M d)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  have hk : 1 ≤ k := by omega
  have hMixed :
      mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M :=
    mixed_noL_atLeastTwoQ_ge_neg_errMix_of_pointwiseWordBound
      (R := R) (k := k) (ε := ε) (M := M) hk hε hM hWord
  have hMixedFrontier :
      lowerConcreteMixedErrorFrontier R k ε
        (fun a slack d => lowerPartialTransposeMixedErrorD k (a + slack) M d) :=
    lowerConcreteMixedErrorFrontier_of_mixed_noL_atLeastTwoQ_ge_neg_errMix
      (R := R) (k := k) (ε := ε) hk3 M hMixed
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_CatalanErrorBoundAndVarianceStack_withMixedErrorFrontier_splitMixedWordBudget
      (R := R) (k := k) (ε := ε) hk3 hε
      hMeanError hVariance
      (fun a slack d => lowerPartialTransposeMixedErrorD k (a + slack) M d)
      hMixedFrontier

/-- Same honest mixed-frontier endpoint, with the mean side pushed all the way
down to the explicit finite-diagram `D / d` frontier.

This is the most precise current mean-side dependency: proving the displayed
diagram estimate is exactly what supplies the Catalan-error bound consumed by
the lower endpoint. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_ExplicitCatalanDiagramAndVarianceStack_withMixedErrorFrontier_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hDiagram :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample k m Wcard Cmodel)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (errMix : ℝ → ℝ → ℕ → ℝ)
    (hMixedFrontier : lowerConcreteMixedErrorFrontier R k ε errMix) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_CatalanErrorBoundAndVarianceStack_withMixedErrorFrontier_splitMixedWordBudget
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio_of_explicitDiagramBound
        R.sample k m Wcard Cmodel hDiagram)
      hVariance errMix hMixedFrontier

/-- Explicit-diagram, variance, and repaired PT mixed supplier endpoint.

This is the direct public wrapper for the current paper-facing fixed-`M` PT
mixed route: the mean side is the finite-diagram Catalan estimate, the
background concentration side is the variance/Chebyshev frontier, and the
mixed side is the repaired PT split-word supplier. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_ExplicitCatalanDiagramAndVarianceStack_withPTMixedError_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hDiagram :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample k m Wcard Cmodel)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (M : ℝ)
    (hMixed :
      mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTWickAndVarianceStack_withPTMixedError_splitMixedWordBudget
      (R := R) (k := k) (ε := ε) hk3 hε
      (lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio_of_explicitDiagramBound
        R.sample k m Wcard Cmodel hDiagram)
      hVariance M hMixed

/-- Explicit-diagram and variance endpoint with the mixed side reduced to the
pointwise PT word estimate.

This wrapper removes the packed `mixed_noL_atLeastTwoQ_ge_neg_errMix` input
from the explicit-diagram route: the caller may instead provide the
sphere-supported pointwise mixed-word estimate against the literal PT envelope.
-/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_ExplicitCatalanDiagramAndVarianceStack_withPTPointwiseMixedWordBound_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hDiagram :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample k m Wcard Cmodel)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (M : ℝ) (hM : 0 ≤ M)
    (hWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k ε
        (fun a slack d => lowerPartialTransposeMixedWordBoundD k (a + slack) M d)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  have hk : 1 ≤ k := by omega
  have hMixed :
      mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M :=
    mixed_noL_atLeastTwoQ_ge_neg_errMix_of_pointwiseWordBound
      (R := R) (k := k) (ε := ε) (M := M) hk hε hM hWord
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_ExplicitCatalanDiagramAndVarianceStack_withPTMixedError_splitMixedWordBudget
      (R := R) (k := k) (ε := ε) hk3 hε
      m Wcard Cmodel hDiagram hVariance M hMixed

/-- Runtime-native version of the explicit Catalan-diagram lower endpoint.

This conditional diagnostic wrapper exposes the exact runtime-native mixed
smallness hypothesis rather than hiding it inside an abstract
`lowerConcreteMixedErrorFrontier` packet.  It is not a paper-facing supplier:
`lowerConcreteMixedRuntimeWordError_three_not_uniformEventuallySmall` rules
out this uniform runtime-smallness input at length three. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_ExplicitCatalanDiagramAndVarianceStack_withPTRuntimeMixedError_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hDiagram :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample k m Wcard Cmodel)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (hRuntimeSmall :
      lowerConcreteMixedErrorEventuallySmall k ε
        (lowerConcreteMixedRuntimeWordError R k)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  have hMixedFrontier :
      lowerConcreteMixedErrorFrontier R k ε
        (lowerConcreteMixedRuntimeWordError R k) :=
    lowerConcreteMixedErrorFrontier_of_runtimeWordError
      (R := R) (k := k) (ε := ε) hk3 hε hRuntimeSmall
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_ExplicitCatalanDiagramAndVarianceStack_withMixedErrorFrontier_splitMixedWordBudget
      (R := R) (k := k) (ε := ε) hk3 hε
      m Wcard Cmodel hDiagram hVariance
      (lowerConcreteMixedRuntimeWordError R k) hMixedFrontier

/-- Final clean endpoint adapter for the already-proved closed-form moment
route.

This is the wrapper to use when the mean side has already been proved as
convergence to `(λ⁻¹)^k * ClosedFormDet.M λ k`.  It routes that result through
the canonical Catalan adapter and then into the honest mixed-frontier endpoint,
without reopening the Catalan/Hankel computation. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_ClosedFormMomentLimitAndVarianceStack_withMixedErrorFrontier_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hClosed :
      lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit_fromRatio
        R.sample k)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (errMix : ℝ → ℝ → ℕ → ℝ)
    (hMixedFrontier : lowerConcreteMixedErrorFrontier R k ε errMix) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  have hMean :
      deletedColumnSphericalMean_tendsto_ptCatalan R.sample k R.lam :=
    deletedColumnSphericalMean_tendsto_ptCatalan_atRatio_of_closedFormMomentLimit
      R.sample k hClosed R.lam_pos.ne'
      (lower_deletedColumn_ratio_tendsto_concreteChoices R)
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanMeanAndVarianceStack_withMixedErrorFrontier_splitMixedWordBudget
      (R := R) (k := k) (ε := ε) hk3 hε
      hMean hVariance errMix hMixedFrontier

/-- Sample-ratio closed-form mean, variance stack, and honest mixed-frontier
endpoint.

This is the sample-ratio convention version of
`lower_eventual_log_over_spikeSpeed_concreteModel_of_ClosedFormMomentLimitAndVarianceStack_withMixedErrorFrontier_splitMixedWordBudget`.
It keeps the mixed side at the explicit error-frontier level, so it is useful
before choosing between the paper-facing PT envelope and diagnostic runtime
envelopes. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_ClosedFormSampleRatioAndVarianceStack_withMixedErrorFrontier_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hClosed :
      lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit_fromSampleRatio
        R.sample k)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (errMix : ℝ → ℝ → ℕ → ℝ)
    (hMixedFrontier : lowerConcreteMixedErrorFrontier R k ε errMix) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  have hClosedRatio :
      lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit_fromRatio
        R.sample k :=
    lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit_fromRatio_of_sampleRatio
      R.sample k R.sample_pos_eventually hClosed
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_ClosedFormMomentLimitAndVarianceStack_withMixedErrorFrontier_splitMixedWordBudget
      (R := R) (k := k) (ε := ε) hk3 hε
      hClosedRatio hVariance errMix hMixedFrontier

/-- Closed-form sample-ratio mean, exponential background tail, and honest
mixed-frontier endpoint.

This is the exponential-background sibling of
`...ClosedFormSampleRatioAndVarianceStack_withMixedErrorFrontier...`: the
variance/Chebyshev predicate is supplied internally from the already-checked
`exp (-c d²)` to `C / d²` scalar bridge.  The remaining theorem-strength
inputs are the closed-form mean theorem, the exponential background
concentration theorem, and the mixed frontier for one matched `errMix`. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_ClosedFormSampleRatioAndExponentialDeviationStack_withMixedErrorFrontier_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hClosed :
      lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit_fromSampleRatio
        R.sample k)
    (hExponentialTail :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R k)
    (errMix : ℝ → ℝ → ℕ → ℝ)
    (hMixedFrontier : lowerConcreteMixedErrorFrontier R k ε errMix) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_ClosedFormSampleRatioAndVarianceStack_withMixedErrorFrontier_splitMixedWordBudget
      (R := R) (k := k) (ε := ε) hk3 hε
      hClosed
      (deletedColumnSphericalMoment_variance_le_const_div_d4_of_exponentialDeviationTailBound
        R k hExponentialTail)
      errMix hMixedFrontier

/-- Closed-form sample-ratio mean, exponential background tail, and packaged
fixed-`M` PT mixed supplier endpoint.

This is the fixed-`M` PT mixed sibling of
`...ClosedFormSampleRatioAndExponentialDeviationStack_withMixedErrorFrontier...`:
the honest mixed frontier is supplied internally from the already-proved
`mixed_noL_atLeastTwoQ_ge_neg_errMix` theorem and the literal PT scalar
smallness adapter.  This does not assert that the diagnostic runtime error is
dominated by a fixed `M`; it only packages an independently proved fixed-`M`
mixed supplier. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_ClosedFormSampleRatioAndExponentialDeviationStack_withPTMixedError_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hClosed :
      lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit_fromSampleRatio
        R.sample k)
    (hExponentialTail :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R k)
    (M : ℝ)
    (hMixed : mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_ClosedFormSampleRatioAndExponentialDeviationStack_withMixedErrorFrontier_splitMixedWordBudget
      (R := R) (k := k) (ε := ε) hk3 hε
      hClosed hExponentialTail
      (fun a slack d => lowerPartialTransposeMixedErrorD k (a + slack) M d)
      (lowerConcreteMixedErrorFrontier_of_mixed_noL_atLeastTwoQ_ge_neg_errMix
        (R := R) (k := k) (ε := ε) hk3 M hMixed)

/-- Closed-form sample-ratio mean, exponential background tail, and pointwise
PT mixed-word endpoint.

This is the pointwise mixed-word sibling of
`...ClosedFormSampleRatioAndExponentialDeviationStack_withMixedErrorFrontier...`:
the honest mixed frontier is supplied internally from the sphere-supported
pointwise PT word estimate and the literal PT mixed-error budget.  The remaining
theorem-strength inputs are the closed-form mean theorem, the exponential
background concentration theorem, and the pointwise PT mixed-word estimate. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_ClosedFormSampleRatioAndExponentialDeviationStack_withPTPointwiseMixedWordBound_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hClosed :
      lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit_fromSampleRatio
        R.sample k)
    (hExponentialTail :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R k)
    (M : ℝ) (hM : 0 ≤ M)
    (hWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k ε
        (fun a slack d => lowerPartialTransposeMixedWordBoundD k (a + slack) M d)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_ClosedFormSampleRatioAndExponentialDeviationStack_withMixedErrorFrontier_splitMixedWordBudget
      (R := R) (k := k) (ε := ε) hk3 hε
      hClosed hExponentialTail
      (fun a slack d => lowerPartialTransposeMixedErrorD k (a + slack) M d)
      (lowerConcreteMixedErrorFrontier_of_PTPointwiseWordBound
        (R := R) (k := k) (ε := ε) (M := M) hk3 hε hM hWord)

/-- Closed-form mean, variance stack, and pointwise PT mixed-word endpoint.

This is the direct pointwise public surface for the already-proved
closed-form/Hankel mean route in ratio convention: the mean side is the
closed-form moment limit, the background concentration side is the
variance/Chebyshev frontier, and the mixed side is the sphere-supported
pointwise PT word estimate. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_ClosedFormMomentLimitAndVarianceStack_withPTPointwiseMixedWordBound_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hClosed :
      lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit_fromRatio
        R.sample k)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (M : ℝ) (hM : 0 ≤ M)
    (hWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k ε
        (fun a slack d => lowerPartialTransposeMixedWordBoundD k (a + slack) M d)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  have hk : 1 ≤ k := by omega
  have hMixed :
      mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M :=
    mixed_noL_atLeastTwoQ_ge_neg_errMix_of_pointwiseWordBound
      (R := R) (k := k) (ε := ε) (M := M) hk hε hM hWord
  have hMixedFrontier :
      lowerConcreteMixedErrorFrontier R k ε
        (fun a slack d => lowerPartialTransposeMixedErrorD k (a + slack) M d) :=
    lowerConcreteMixedErrorFrontier_of_mixed_noL_atLeastTwoQ_ge_neg_errMix
      (R := R) (k := k) (ε := ε) hk3 M hMixed
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_ClosedFormMomentLimitAndVarianceStack_withMixedErrorFrontier_splitMixedWordBudget
      (R := R) (k := k) (ε := ε) hk3 hε
      hClosed hVariance
      (fun a slack d => lowerPartialTransposeMixedErrorD k (a + slack) M d)
      hMixedFrontier

/-- Canonical repaired endpoint for already-proved mean/variance/mixed
suppliers.

This is the endpoint to use when the mean theorem is available in the older
closed-form/Hankel convention `sample d / d² → λ`, the background deviation is
available as the grouped second-moment Wick tail, and the mixed side is
available through the fixed PT mixed supplier.  It deliberately avoids the
runtime-smallness route, which is only a diagnostic path under the current
`lowerConcreteM` event. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_ClosedFormSampleRatioAndSecondMomentWickStack_withPTMixedError_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hClosed :
      lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit_fromSampleRatio
        R.sample k)
    (hMomentTail :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k)
    (M : ℝ)
    (hMixed : mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  have hClosedRatio :
      lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit_fromRatio
        R.sample k :=
    lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit_fromRatio_of_sampleRatio
      R.sample k R.sample_pos_eventually hClosed
  have hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k :=
    hMomentTail
  have hMixedFrontier :
      lowerConcreteMixedErrorFrontier R k ε
        (fun a slack d => lowerPartialTransposeMixedErrorD k (a + slack) M d) :=
    lowerConcreteMixedErrorFrontier_of_mixed_noL_atLeastTwoQ_ge_neg_errMix
      (R := R) (k := k) (ε := ε) hk3 M hMixed
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_ClosedFormMomentLimitAndVarianceStack_withMixedErrorFrontier_splitMixedWordBudget
      (R := R) (k := k) (ε := ε) hk3 hε
      hClosedRatio hVariance
      (fun a slack d => lowerPartialTransposeMixedErrorD k (a + slack) M d)
      hMixedFrontier

/-- Closed-form sample-ratio mean, variance stack, and fixed-`M` PT mixed
supplier endpoint.

This is the packaged mixed-supplier sibling of the pointwise PT endpoint below:
the background concentration side is the paper-facing variance/Chebyshev
frontier, not the internal grouped second-moment tail. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_ClosedFormSampleRatioAndVarianceStack_withPTMixedError_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hClosed :
      lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit_fromSampleRatio
        R.sample k)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (M : ℝ)
    (hMixed : mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_ClosedFormSampleRatioAndSecondMomentWickStack_withPTMixedError_splitMixedWordBudget
      (R := R) (k := k) (ε := ε) hk3 hε
      hClosed hVariance M hMixed

/-- Closed-form mean, second-moment tail, and pointwise PT mixed-word endpoint.

This is the sharper public surface for the repaired lower route when the mean
side is already available in closed-form/Hankel convention and the background
concentration side is available as the grouped second-moment tail: the mixed
side is exposed as the actual sphere-supported pointwise estimate against the
literal PT word envelope, rather than the packed
`mixed_noL_atLeastTwoQ_ge_neg_errMix` supplier. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_ClosedFormSampleRatioAndSecondMomentWickStack_withPTPointwiseMixedWordBound_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hClosed :
      lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit_fromSampleRatio
        R.sample k)
    (hMomentTail :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k)
    (M : ℝ) (hM : 0 ≤ M)
    (hWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k ε
        (fun a slack d => lowerPartialTransposeMixedWordBoundD k (a + slack) M d)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  have hk : 1 ≤ k := by omega
  have hMixed :
      mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M :=
    mixed_noL_atLeastTwoQ_ge_neg_errMix_of_pointwiseWordBound
      (R := R) (k := k) (ε := ε) (M := M) hk hε hM hWord
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_ClosedFormSampleRatioAndSecondMomentWickStack_withPTMixedError_splitMixedWordBudget
      (R := R) (k := k) (ε := ε) hk3 hε
      hClosed hMomentTail M hMixed

/-- Closed-form sample-ratio mean, variance stack, and pointwise PT mixed-word
endpoint.

This is the paper-facing version of the sample-ratio closed-form route: the
internal grouped second-moment tail is supplied by the
`deletedColumnSphericalMoment_variance_le_const_div_d4` theorem, while the
mixed side remains the actual pointwise PT word estimate. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_ClosedFormSampleRatioAndVarianceStack_withPTPointwiseMixedWordBound_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hClosed :
      lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit_fromSampleRatio
        R.sample k)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (M : ℝ) (hM : 0 ≤ M)
    (hWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k ε
        (fun a slack d => lowerPartialTransposeMixedWordBoundD k (a + slack) M d)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  have hClosedRatio :
      lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit_fromRatio
        R.sample k :=
    lowerDeletedColumnBackgroundMomentHasClosedFormMomentLimit_fromRatio_of_sampleRatio
      R.sample k R.sample_pos_eventually hClosed
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_ClosedFormMomentLimitAndVarianceStack_withPTPointwiseMixedWordBound_splitMixedWordBudget
      (R := R) (k := k) (ε := ε) hk3 hε
      hClosedRatio hVariance M hM hWord

/-- Sharp PT endpoint with the mixed side using the exact runtime-native
mixed-word error.

This conditional diagnostic route avoids the fixed-`M` scalar domination
comparison, but the remaining mixed leaf is the smallness statement for the
finite runtime error
`lowerConcreteMixedRuntimeWordError`; the pointwise word estimates and the
finite mixed budget are internalized by
`lower_mixedLowerOnSphere_concreteChoices_of_runtimeWordError`.  The
length-three obstruction
`lowerConcreteMixedRuntimeWordError_three_not_uniformEventuallySmall` shows
that this runtime-native smallness hypothesis is not an unconditional
paper-facing supplier. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanMeanAndVarianceStack_withPTRuntimeMixedError_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMean :
      deletedColumnSphericalMean_tendsto_ptCatalan R.sample k R.lam)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (hRuntimeSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop,
              lowerConcreteMixedRuntimeWordError R k a slack d ≤ η) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  have hk : 1 < k := lt_of_lt_of_le (by decide : 1 < 3) hk3
  rcases
    lowerConcreteDeletedBackgroundMomentSecondMomentWickBadTailBound_of_deviationTailBound
      (R := R) (k := k)
      (lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound_of_deletedColumnSphericalMoment_variance_le_const_div_d4
        R k hVariance) with
    ⟨C, _hC, hMomentBad⟩
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_concreteScalarChoices_sphereBetaScaleBudget_withMomentBudgetAndMixedError
      (R := R) (k := k) (ε := ε) hk hε
      (bMoment := lowerConcreteMomentPolynomialBound C R k)
      (errMix := lowerConcreteMixedRuntimeWordError R k)
      (lower_unitProfile_canonicalDirection_concreteChoices_of_traceStability
        hk hε
        (lowerConcreteCanonicalCapSpikeTraceStability_of_overlapLower
          (lt_of_lt_of_le (by decide : 1 < 3) hk3)
          hε
          (lowerConcreteCanonicalCapTracePowerOverlapLower_of_traceDominatesCoordinateOverlap
            (lowerConcreteRankOneProjectorGammaTracePowerDominatesCoordinateOverlap_of_leftDensityDiagonalPower
              (lowerConcreteRankOneProjectorGammaTracePowerDominatesLeftDensityDiagonalPower_closed k)))))
      (lower_scaleBudget_concreteChoices_of_meanPositivePartEventuallyBounded
        (R := R) (k := k) (ε := ε) hk3 hε
        (lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded_of_deletedColumnMomentAsymptotic
          R k
          (lowerDeletedColumnBackgroundMomentHasCatalanLimit_of_deletedColumnSphericalMean_tendsto_ptCatalan
            R.sample k R.lam hMean)))
      (lower_mixedLowerOnSphere_concreteChoices_of_runtimeWordError
        (R := R) (k := k) (ε := ε) hk3 hε)
      hRuntimeSmall
      lower_referenceCone_BipIndex_Fin_eventually_concreteChoices
      hMomentBad
      (lower_concrete_polynomialMomentSmall C R k)

/-- Conditional runtime-smallness endpoint.

The fixed-`M` scalar-domination route is intentionally not used here, but the
mixed input is still the asymptotic negligibility of the exact runtime-native
mixed error.  This is a visible hypothesis, not a proved supplier; for `k = 3`
the theorem
`lowerConcreteMixedRuntimeWordError_three_not_uniformEventuallySmall` proves
that this uniform runtime-smallness input is impossible. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_corrected
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMean :
      deletedColumnSphericalMean_tendsto_ptCatalan R.sample k R.lam)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (hMixedSmall :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop,
              lowerConcreteMixedRuntimeWordError R k a slack d ≤ η) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanMeanAndVarianceStack_withPTRuntimeMixedError_splitMixedWordBudget
      (R := R) (k := k) (ε := ε) hk3 hε
      hMean hVariance hMixedSmall

/-- Sharp PT endpoint with the mixed side reduced to the remaining pointwise
word-level theorem.

The finite PT mixed-word budget and the scalar smallness of
`lowerPartialTransposeMixedErrorD` are already internalized.  So the only live
mixed-side leaf here is the sphere-supported pointwise word estimate with the
literal envelope `lowerPartialTransposeMixedWordBoundD`. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanMeanAndVarianceStack_withPTPointwiseMixedWordBound_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMean :
      deletedColumnSphericalMean_tendsto_ptCatalan R.sample k R.lam)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (M : ℝ) (hM : 0 ≤ M)
    (hWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k ε
        (fun a slack d => lowerPartialTransposeMixedWordBoundD k (a + slack) M d)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  have hk : 1 ≤ k := by omega
  have hMixed :
      mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M :=
    mixed_noL_atLeastTwoQ_ge_neg_errMix_of_pointwiseWordBound
      (R := R) (k := k) (ε := ε) (M := M) hk hε hM hWord
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanMeanAndVarianceStack_withPTMixedError_splitMixedWordBudget
      (R := R) (k := k) (ε := ε) hk3 hε
      hMean hVariance M hMixed

/-- Sharp PT endpoint with the mixed side reduced further to a domination
statement from the concrete runtime word envelope to the cleaner literal PT
budget envelope.

The runtime word-by-word estimate itself is now internal: it is proved directly
from the favourable-event spike/background norm bounds in
`LowerMixedLowerConcreteChoices`. The only remaining mixed-side leaf here is
the eventual comparison showing that this runtime envelope is dominated by the
chosen cleaner PT bound with fixed scalar parameter `M`. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanMeanAndVarianceStack_withPTRuntimeMixedWordDomination_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMean :
      deletedColumnSphericalMean_tendsto_ptCatalan R.sample k R.lam)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (M : ℝ) (hM : 0 ≤ M)
    (hWordDom :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ w : Fin k → LocalExpansionLetter,
              lowerConcreteMixedRuntimeWordBound R k a slack d w ≤
                lowerPartialTransposeMixedWordBoundD k (a + slack) M d w) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  have hMixed :
      mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M :=
    mixed_noL_atLeastTwoQ_ge_neg_errMix_of_runtimeEnvelope_domination
      (R := R) (k := k) (ε := ε) (M := M) hk3 hε hM hWordDom
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanMeanAndVarianceStack_withPTMixedError_splitMixedWordBudget
      (R := R) (k := k) (ε := ε) hk3 hε
      hMean hVariance M hMixed

/-- Sharp PT endpoint with the mixed side reduced to the exact mixed-word
runtime-domination leaf.

This is the non-stale version of the runtime-domination endpoint: the finite
mixed budget only sums over `localWordIsMixed` words, so the domination
comparison is required exactly on that filtered support rather than on pure
background or pure spike words. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanMeanAndVarianceStack_withPTRuntimeMixedWordDominationOnMixed_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMean :
      deletedColumnSphericalMean_tendsto_ptCatalan R.sample k R.lam)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (M : ℝ) (hM : 0 ≤ M)
    (hWordDom :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                lowerConcreteMixedRuntimeWordBound R k a slack d w ≤
                  lowerPartialTransposeMixedWordBoundD k (a + slack) M d w) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  have hMixed :
      mixed_noL_atLeastTwoQ_ge_neg_errMix R k ε M :=
    mixed_noL_atLeastTwoQ_ge_neg_errMix_of_runtimeEnvelope_domination_on_mixed
      (R := R) (k := k) (ε := ε) (M := M) hk3 hε hM hWordDom
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanMeanAndVarianceStack_withPTMixedError_splitMixedWordBudget
      (R := R) (k := k) (ε := ε) hk3 hε
      hMean hVariance M hMixed

/-- Sharp PT endpoint with the mixed runtime-domination leaf reduced to the
two scalar no-`L` word cases.

The `L`-containing mixed words are handled internally by the zero-runtime case
and nonnegativity of the PT envelope.  The visible mixed leaf is now exactly:
prove the one-`Q` domination and the many-`Q` domination. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanMeanAndVarianceStack_withPTRuntimeMixedWordDominationCases_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMean :
      deletedColumnSphericalMean_tendsto_ptCatalan R.sample k R.lam)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (M : ℝ) (hM : 0 ≤ M)
    (hWordDomOne :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                localWordLetterCount LocalExpansionLetter.L w = 0 →
                  localWordLetterCount LocalExpansionLetter.Q w = 1 →
                    lowerConcreteMixedRuntimeWordBound R k a slack d w ≤
                      lowerPartialTransposeMixedWordBoundD k (a + slack) M d w)
    (hWordDomMany :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                localWordLetterCount LocalExpansionLetter.L w = 0 →
                  2 ≤ localWordLetterCount LocalExpansionLetter.Q w →
                    lowerConcreteMixedRuntimeWordBound R k a slack d w ≤
                      lowerPartialTransposeMixedWordBoundD k (a + slack) M d w) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  have hk0 : 0 < k := by omega
  have hWordDom :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                lowerConcreteMixedRuntimeWordBound R k a slack d w ≤
                  lowerPartialTransposeMixedWordBoundD k (a + slack) M d w :=
    lowerConcreteMixedRuntimeWordBound_domination_on_mixed_of_oneQ_manyQ
      (R := R) (k := k) (ε := ε) (M := M)
      hk0 hε hM hWordDomOne hWordDomMany
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanMeanAndVarianceStack_withPTRuntimeMixedWordDominationOnMixed_splitMixedWordBudget
      (R := R) (k := k) (ε := ε) hk3 hε
      hMean hVariance M hM hWordDom

/-- Sharp PT endpoint with the mixed runtime-domination leaf reduced all the way
to the two scalar eventual inequalities that compare the runtime spike/background
envelope with the literal PT envelope.

The remaining mixed difficulty is now explicitly scalar: control the Beta
interval upper endpoint and the concrete background threshold `lowerConcreteM`.
No word combinatorics remains in the endpoint hypothesis. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanMeanAndVarianceStack_withPTRuntimeMixedScalarDomination_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMean :
      deletedColumnSphericalMean_tendsto_ptCatalan R.sample k R.lam)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (M : ℝ) (hM : 0 ≤ M)
    (hOneScalar :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            (lowerConcreteN d : ℝ) ^ (k - 1) *
              (betaColumnIntervalUpper
                  (betaColumnSpikeScale
                    (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                  (lowerConcreteDelta a slack d) *
                (((lowerConcreteM R a slack d) / (lowerConcreteN d : ℝ)) ^
                    (k - 2) *
                  ((lowerConcreteM R a slack d) /
                    Real.sqrt (lowerConcreteN d : ℝ)))) ≤
              (a + slack) * M ^ (k - 1) *
                ((d : ℝ) ^ 2) ^ ((-1 / 2 : ℝ) + 1 / (k : ℝ)))
    (hManyScalar :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ j : ℕ, j ∈ Finset.Icc 2 (k - 1) →
              (lowerConcreteN d : ℝ) ^ (k - 1) *
                (((lowerConcreteM R a slack d) / (lowerConcreteN d : ℝ)) ^
                    (k - j) *
                  betaColumnIntervalUpper
                    (betaColumnSpikeScale
                      (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                    (lowerConcreteDelta a slack d) ^ j) ≤
                (a + slack) ^ j * M ^ (k - j) *
                  ((d : ℝ) ^ 2) ^ ((j : ℝ) / (k : ℝ) - 1)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  have hk0 : 0 < k := by omega
  have hWordDom :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                lowerConcreteMixedRuntimeWordBound R k a slack d w ≤
                  lowerPartialTransposeMixedWordBoundD k (a + slack) M d w :=
    lowerConcreteMixedRuntimeWordBound_domination_on_mixed_of_scalar_cases
      (R := R) (k := k) (ε := ε) (M := M)
      hk0 hε hM hOneScalar hManyScalar
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanMeanAndVarianceStack_withPTRuntimeMixedWordDominationOnMixed_splitMixedWordBudget
      (R := R) (k := k) (ε := ε) hk3 hε
      hMean hVariance M hM hWordDom

/-- Catalan-error and variance endpoint with the runtime mixed comparison
reduced to two scalar eventual inequalities.

This is the source-explicit diagnostic version of the mixed scalar route: the
mean side is the concrete deleted-column `D / d` Catalan-error frontier, while
the mixed side exposes only the one-`Q` and many-`Q` scalar comparisons between
the runtime envelope and the literal PT envelope. -/
theorem lower_eventual_log_over_spikeSpeed_concreteModel_of_CatalanErrorBoundAndVarianceStack_withPTRuntimeMixedScalarDomination_splitMixedWordBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {k : ℕ} {ε : ℝ} (hk3 : 3 ≤ k) (hε : 0 < ε)
    (hMeanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample k)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (M : ℝ) (hM : 0 ≤ M)
    (hOneScalar :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            (lowerConcreteN d : ℝ) ^ (k - 1) *
              (betaColumnIntervalUpper
                  (betaColumnSpikeScale
                    (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                  (lowerConcreteDelta a slack d) *
                (((lowerConcreteM R a slack d) / (lowerConcreteN d : ℝ)) ^
                    (k - 2) *
                  ((lowerConcreteM R a slack d) /
                    Real.sqrt (lowerConcreteN d : ℝ)))) ≤
              (a + slack) * M ^ (k - 1) *
                ((d : ℝ) ^ 2) ^ ((-1 / 2 : ℝ) + 1 / (k : ℝ)))
    (hManyScalar :
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ j : ℕ, j ∈ Finset.Icc 2 (k - 1) →
              (lowerConcreteN d : ℝ) ^ (k - 1) *
                (((lowerConcreteM R a slack d) / (lowerConcreteN d : ℝ)) ^
                    (k - j) *
                  betaColumnIntervalUpper
                    (betaColumnSpikeScale
                      (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                    (lowerConcreteDelta a slack d) ^ j) ≤
                (a + slack) ^ j * M ^ (k - j) *
                  ((d : ℝ) ^ 2) ^ ((j : ℝ) / (k : ℝ) - 1)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        -spikeRate k R.lam ε - η ≤
          Real.log
              (lowerConcreteTargetProb R (lowerConcreteEps ε)
                (lowerConcreteDeletedBackgroundMean R k) k d) /
            spikeSpeed k d := by
  have hMean :
      deletedColumnSphericalMean_tendsto_ptCatalan R.sample k R.lam :=
    deletedColumnSphericalMean_tendsto_ptCatalan_of_lowerDeletedColumnBackgroundMomentHasCatalanLimit
      R.sample k R.lam
      (lowerDeletedColumnBackgroundMomentHasCatalanLimit_of_fromRatio_errorBound
        R k hMeanError)
  exact
    lower_eventual_log_over_spikeSpeed_concreteModel_of_paperFacingPTCatalanMeanAndVarianceStack_withPTRuntimeMixedScalarDomination_splitMixedWordBudget
      (R := R) (k := k) (ε := ε) hk3 hε
      hMean hVariance M hM hOneScalar hManyScalar

end AppendixB
