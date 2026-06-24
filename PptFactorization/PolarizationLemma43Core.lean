import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

open scoped symmDiff

/-!
# Quantitative core of Lemma 4.3

Sorry-free algebraic / order-theoretic core of the strict improvement lemma
(after the change-of-variables formula is abstracted as a single inequality).

Dictionary with the handwritten proof:

* `eps`        = ε
* `tau`        = τ
* `symm`       = μ (E △ C)
* `miss`       = μ (C \ E)
* `extra`      = μ (E \ C)
* `bandPlus`   = μ {a ≤ φ ≤ a + τ}
* `bandMinus`  = μ {a - τ ≤ φ ≤ a}
* `muPlus`     = μ D₊
* `muMinus`    = μ D₋
* `avg`        = ∫_{V_p} Δ_v(E) dν_p(v)
* `supDelta`   = sup_v Δ_v(E)

Geometric input (not proved here): from bounds on D₋, D₊, kernel lower bound
K_n ≥ 2^{-(n-2)}, and average ≤ supremum,

`2 * tau * (1 / 2^(n-2)) * muMinus * muPlus ≤ avg`.

This file then derives `avg ≥ tau * eps^2 / 2^(n+1)` and passes to `supDelta`.

The spherical Jacobian / change-of-variables with
K_n(x,y) = 2^{-(n-2)} sin(d_geo(x,y)/2)^{-(n-2)} (chordal equivalent in the project)
is proved in `SphericalPolarizationPushforwardTransport.lean`
(`finRealSphereReflectionMap_pushforward_withDensity`). What remains packaged
only as a scalar hypothesis here is the rectangular-block integral lower bound
`HasRectangularBlockLowerBound`; see `SphericalPolarizationStrictImprovement.lean`.
-/

namespace PolarizationLemma43Core

open MeasureTheory Set
open scoped symmDiff
open scoped symmDiff

/-- If a mass `trimmed` is obtained from `total` by removing at most `band`,
and `total ≥ eps / 2`, `band ≤ eps / 4`, then `trimmed ≥ eps / 4`. -/
lemma trimmed_mass_lower_bound
    {eps total band trimmed : ℝ}
    (htotal : eps / 2 ≤ total)
    (hband : band ≤ eps / 4)
    (htrimmed : total - band ≤ trimmed) :
    eps / 4 ≤ trimmed := by
  linarith

/-! ### Measure-theoretic trimming

Cursor's first core lemma above is purely real-valued: it assumes the scalar
inequality `total - band ≤ trimmed`.  The lemmas below prove that inequality
from actual set trimming in any finite measure space. -/

/-- Measure-theoretic trimming lower bound.

If `D` contains the set obtained from `A` after removing `B`, if `A` has mass
at least `eps / 2`, and if the removed band `B` has mass at most `eps / 4`,
then `D` has mass at least `eps / 4`.

This is the set-level replacement for the scalar hypothesis
`total - band ≤ trimmed` in `trimmed_mass_lower_bound`. -/
lemma measureReal_trimmed_diff_lower_bound
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {eps : ℝ} {A B D : Set Ω}
    (hB_meas : MeasurableSet B)
    (hA_mass : eps / 2 ≤ μ.real A)
    (hB_mass : μ.real B ≤ eps / 4)
    (hD : A \ B ⊆ D) :
    eps / 4 ≤ μ.real D := by
  have htrim_scalar : μ.real A - μ.real B ≤ μ.real (A \ B) := by
    have hdiff :
        μ.real (A \ B) + μ.real (A ∩ B) = μ.real A :=
      measureReal_diff_add_inter (μ := μ) (s := A) (t := B) hB_meas
    have hinter_le : μ.real (A ∩ B) ≤ μ.real B :=
      measureReal_mono (μ := μ) inter_subset_right
    linarith
  have hbase : eps / 4 ≤ μ.real A - μ.real B := by
    linarith
  exact le_trans hbase (le_trans htrim_scalar (measureReal_mono (μ := μ) hD))

/-- Two simultaneous set-trimming lower bounds. -/
lemma measureReal_two_sided_trim_lower_bounds
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {eps : ℝ} {Aplus Aminus Bplus Bminus Dplus Dminus : Set Ω}
    (hBplus_meas : MeasurableSet Bplus)
    (hBminus_meas : MeasurableSet Bminus)
    (hAplus_mass : eps / 2 ≤ μ.real Aplus)
    (hAminus_mass : eps / 2 ≤ μ.real Aminus)
    (hBplus_mass : μ.real Bplus ≤ eps / 4)
    (hBminus_mass : μ.real Bminus ≤ eps / 4)
    (hDplus : Aplus \ Bplus ⊆ Dplus)
    (hDminus : Aminus \ Bminus ⊆ Dminus) :
    eps / 4 ≤ μ.real Dplus ∧ eps / 4 ≤ μ.real Dminus := by
  constructor
  · exact measureReal_trimmed_diff_lower_bound
      (μ := μ) hBplus_meas hAplus_mass hBplus_mass hDplus
  · exact measureReal_trimmed_diff_lower_bound
      (μ := μ) hBminus_meas hAminus_mass hBminus_mass hDminus

/--
If `symm = miss + extra`, `miss = extra`, and `symm ≥ eps`, then both balanced
halves have mass at least `eps / 2`.
-/
lemma halves_from_balanced_symm
    {eps symm miss extra : ℝ}
    (hsymm : symm = miss + extra)
    (hbalance : miss = extra)
    (hfar : eps ≤ symm) :
    eps / 2 ≤ miss ∧ eps / 2 ≤ extra := by
  constructor <;> linarith

/-- Balanced symmetric-difference trimming, stated with actual measurable sets.

If `E` and `C` have symmetric difference at least `eps`, the two halves
`C \ E` and `E \ C` have equal mass, and the two bands being removed have mass
at most `eps / 4`, then the trimmed sets `Dplus` and `Dminus` have mass at
least `eps / 4` as soon as they contain the corresponding set differences. -/
lemma measureReal_symmDiff_trim_lower_bounds
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {eps : ℝ} {E C Bplus Bminus Dplus Dminus : Set Ω}
    (hE_meas : MeasurableSet E)
    (hC_meas : MeasurableSet C)
    (hBplus_meas : MeasurableSet Bplus)
    (hBminus_meas : MeasurableSet Bminus)
    (hfar : eps ≤ μ.real (E ∆ C))
    (hbalance : μ.real (C \ E) = μ.real (E \ C))
    (hBplus_mass : μ.real Bplus ≤ eps / 4)
    (hBminus_mass : μ.real Bminus ≤ eps / 4)
    (hDplus : (C \ E) \ Bplus ⊆ Dplus)
    (hDminus : (E \ C) \ Bminus ⊆ Dminus) :
    eps / 4 ≤ μ.real Dplus ∧ eps / 4 ≤ μ.real Dminus := by
  have hsymm :
      μ.real (E ∆ C) = μ.real (C \ E) + μ.real (E \ C) := by
    rw [measureReal_symmDiff_eq (μ := μ) hE_meas hC_meas]
    ac_rfl
  have hhalves :
      eps / 2 ≤ μ.real (C \ E) ∧ eps / 2 ≤ μ.real (E \ C) :=
    halves_from_balanced_symm
      (eps := eps)
      (symm := μ.real (E ∆ C))
      (miss := μ.real (C \ E))
      (extra := μ.real (E \ C))
      hsymm hbalance hfar
  exact measureReal_two_sided_trim_lower_bounds
    (μ := μ)
    hBplus_meas hBminus_meas
    hhalves.1 hhalves.2
    hBplus_mass hBminus_mass
    hDplus hDminus

/--
Product lower bound: replacing each trimmed mass by its lower bound preserves
the averaged improvement lower bound when the scalar prefactor is nonnegative.
-/
lemma product_lower_bound
    {eps tau kappa muMinus muPlus avg : ℝ}
    (heps : 0 ≤ eps)
    (htau : 0 ≤ tau)
    (hkappa : 0 < kappa)
    (hminus : eps / 4 ≤ muMinus)
    (hplus : eps / 4 ≤ muPlus)
    (havg :
      2 * tau * (1 / kappa) * muMinus * muPlus ≤ avg) :
    2 * tau * (1 / kappa) * (eps / 4) * (eps / 4) ≤ avg := by
  let c : ℝ := 2 * tau * (1 / kappa)
  have heps4 : 0 ≤ eps / 4 := by
    positivity
  have hmuMinus : 0 ≤ muMinus :=
    le_trans heps4 hminus
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hprod : (eps / 4) * (eps / 4) ≤ muMinus * muPlus :=
    mul_le_mul hminus hplus heps4 hmuMinus
  have hmul :
      c * ((eps / 4) * (eps / 4)) ≤ c * (muMinus * muPlus) :=
    mul_le_mul_of_nonneg_left hprod hc
  calc
    2 * tau * (1 / kappa) * (eps / 4) * (eps / 4)
        = c * ((eps / 4) * (eps / 4)) := by
            dsimp [c]
            ring
    _ ≤ c * (muMinus * muPlus) := hmul
    _ = 2 * tau * (1 / kappa) * muMinus * muPlus := by
            dsimp [c]
            ring
    _ ≤ avg := havg

/-- For `n ≥ 2`, `2^(n+1) = 8 * 2^(n-2)` over the reals. -/
lemma pow_shift_two
    (n : ℕ)
    (hn : 2 ≤ n) :
    (2 : ℝ) ^ (n + 1) = 8 * (2 : ℝ) ^ (n - 2) := by
  have h : n + 1 = (n - 2) + 3 := by
    omega
  calc
    (2 : ℝ) ^ (n + 1)
        = (2 : ℝ) ^ ((n - 2) + 3) := by
            rw [h]
    _ = (2 : ℝ) ^ (n - 2) * (2 : ℝ) ^ 3 := by
            rw [pow_add]
    _ = (2 : ℝ) ^ (n - 2) * 8 := by
            norm_num
    _ = 8 * (2 : ℝ) ^ (n - 2) := by
            ring

/-- The constant `tau * eps^2 / 2^(n+1)` is positive when `tau, eps > 0`. -/
lemma eta_pos
    (n : ℕ)
    {eps tau : ℝ}
    (heps : 0 < eps)
    (htau : 0 < tau) :
    0 < tau * eps ^ 2 / ((2 : ℝ) ^ (n + 1)) := by
  positivity

/--
Main lower bound after the product estimate.

If the averaged improvement dominates

`2 * tau * 2^{-(n-2)} * muMinus * muPlus`

and both trimmed masses are at least `eps / 4`, then it dominates

`tau * eps^2 / 2^(n+1)`.
-/
theorem avg_improvement_lower_bound
    (n : ℕ)
    (hn : 2 ≤ n)
    {eps tau muMinus muPlus avg : ℝ}
    (heps : 0 ≤ eps)
    (htau : 0 ≤ tau)
    (hminus : eps / 4 ≤ muMinus)
    (hplus : eps / 4 ≤ muPlus)
    (havgProduct :
      2 * tau * (1 / ((2 : ℝ) ^ (n - 2))) * muMinus * muPlus ≤ avg) :
    tau * eps ^ 2 / ((2 : ℝ) ^ (n + 1)) ≤ avg := by
  have hcore :
      2 * tau * (1 / ((2 : ℝ) ^ (n - 2))) * (eps / 4) * (eps / 4)
        ≤ avg :=
    product_lower_bound
      (eps := eps)
      (tau := tau)
      (kappa := (2 : ℝ) ^ (n - 2))
      (muMinus := muMinus)
      (muPlus := muPlus)
      (avg := avg)
      heps
      htau
      (by positivity)
      hminus
      hplus
      havgProduct
  have heq :
      tau * eps ^ 2 / ((2 : ℝ) ^ (n + 1))
        =
      2 * tau * (1 / ((2 : ℝ) ^ (n - 2))) * (eps / 4) * (eps / 4) := by
    rw [pow_shift_two n hn]
    ring_nf
  exact heq ▸ hcore

/--
From the average lower bound and `avg ≤ supDelta`, get the strict improvement
bound for the supremum.
-/
theorem strict_improvement_from_average
    (n : ℕ)
    (hn : 2 ≤ n)
    {eps tau muMinus muPlus avg supDelta : ℝ}
    (heps : 0 ≤ eps)
    (htau : 0 ≤ tau)
    (hminus : eps / 4 ≤ muMinus)
    (hplus : eps / 4 ≤ muPlus)
    (havgProduct :
      2 * tau * (1 / ((2 : ℝ) ^ (n - 2))) * muMinus * muPlus ≤ avg)
    (havgLeSup : avg ≤ supDelta) :
    tau * eps ^ 2 / ((2 : ℝ) ^ (n + 1)) ≤ supDelta := by
  exact le_trans
    (avg_improvement_lower_bound
      n hn heps htau hminus hplus havgProduct)
    havgLeSup

/--
Full quantitative core of Lemma 4.3.

This packages:

* balanced symmetric difference gives `miss, extra ≥ eps / 2`;
* removing bands of mass at most `eps / 4` gives `D_+, D_- ≥ eps / 4`;
* the kernel/product lower bound gives the average improvement;
* average improvement is bounded above by the supremum;
* hence the supremum is at least `tau * eps^2 / 2^(n+1)`, a positive number.
-/
theorem lemma43_strict_improvement_core
    (n : ℕ)
    (hn : 2 ≤ n)
    {eps tau symm miss extra bandPlus bandMinus
      muMinus muPlus avg supDelta : ℝ}
    (heps : 0 < eps)
    (htau : 0 < tau)
    (hsymm : symm = miss + extra)
    (hbalance : miss = extra)
    (hfar : eps ≤ symm)
    (hbandPlus : bandPlus ≤ eps / 4)
    (hbandMinus : bandMinus ≤ eps / 4)
    (hDplus : miss - bandPlus ≤ muPlus)
    (hDminus : extra - bandMinus ≤ muMinus)
    (havgProduct :
      2 * tau * (1 / ((2 : ℝ) ^ (n - 2))) * muMinus * muPlus ≤ avg)
    (havgLeSup : avg ≤ supDelta) :
    0 < tau * eps ^ 2 / ((2 : ℝ) ^ (n + 1)) ∧
      tau * eps ^ 2 / ((2 : ℝ) ^ (n + 1)) ≤ supDelta := by
  have hhalves :
      eps / 2 ≤ miss ∧ eps / 2 ≤ extra :=
    halves_from_balanced_symm
      (eps := eps)
      (symm := symm)
      (miss := miss)
      (extra := extra)
      hsymm hbalance hfar
  have hplus : eps / 4 ≤ muPlus :=
    trimmed_mass_lower_bound
      hhalves.1
      hbandPlus
      hDplus
  have hminus : eps / 4 ≤ muMinus :=
    trimmed_mass_lower_bound
      hhalves.2
      hbandMinus
      hDminus
  constructor
  · exact eta_pos n heps htau
  · exact strict_improvement_from_average
      n hn
      heps.le
      htau.le
      hminus
      hplus
      havgProduct
      havgLeSup

/--
Measure-theoretic version of `lemma43_strict_improvement_core`.

This removes the scalar trimming hypotheses
`miss - bandPlus ≤ muPlus` and `extra - bandMinus ≤ muMinus`: the lower bounds
on `muPlus` and `muMinus` are derived from actual trimmed sets

* `Dplus ⊇ (C \ E) \ Bplus`;
* `Dminus ⊇ (E \ C) \ Bminus`.

The remaining analytic/geometric input is still the post-kernel product lower
bound `havgProduct`.
-/
theorem lemma43_strict_improvement_core_of_measureTrimming
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (n : ℕ)
    (hn : 2 ≤ n)
    {eps tau avg supDelta : ℝ}
    {E C Bplus Bminus Dplus Dminus : Set Ω}
    (heps : 0 < eps)
    (htau : 0 < tau)
    (hE_meas : MeasurableSet E)
    (hC_meas : MeasurableSet C)
    (hBplus_meas : MeasurableSet Bplus)
    (hBminus_meas : MeasurableSet Bminus)
    (hfar : eps ≤ μ.real (E ∆ C))
    (hbalance : μ.real (C \ E) = μ.real (E \ C))
    (hBplus_mass : μ.real Bplus ≤ eps / 4)
    (hBminus_mass : μ.real Bminus ≤ eps / 4)
    (hDplus : (C \ E) \ Bplus ⊆ Dplus)
    (hDminus : (E \ C) \ Bminus ⊆ Dminus)
    (havgProduct :
      2 * tau * (1 / ((2 : ℝ) ^ (n - 2))) *
          μ.real Dminus * μ.real Dplus ≤ avg)
    (havgLeSup : avg ≤ supDelta) :
    0 < tau * eps ^ 2 / ((2 : ℝ) ^ (n + 1)) ∧
      tau * eps ^ 2 / ((2 : ℝ) ^ (n + 1)) ≤ supDelta := by
  have htrim :
      eps / 4 ≤ μ.real Dplus ∧ eps / 4 ≤ μ.real Dminus :=
    measureReal_symmDiff_trim_lower_bounds
      (μ := μ)
      hE_meas hC_meas hBplus_meas hBminus_meas
      hfar hbalance hBplus_mass hBminus_mass hDplus hDminus
  constructor
  · exact eta_pos n heps htau
  · exact strict_improvement_from_average
      n hn heps.le htau.le
      htrim.2 htrim.1
      havgProduct
      havgLeSup

end PolarizationLemma43Core
