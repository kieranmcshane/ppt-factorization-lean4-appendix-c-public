import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
# Measure-theoretic trimming lemmas

This file isolates the elementary trimming step used in the polarization proof:
from a set of mass at least `ε / 2`, removing a band of mass at most `ε / 4`
leaves mass at least `ε / 4`.

The proof is deliberately independent of the spherical geometry and of the
Jacobian/push-forward kernel theorem.
-/

open MeasureTheory Set
open scoped ENNReal

namespace SphericalPolarization
namespace MeasureTrimming

variable {α : Type*} [MeasurableSpace α]
variable {μ : Measure α}

/--
If `A ⊆ D ∪ B`, then in any finite measure space
`μ(A).toReal ≤ μ(D).toReal + μ(B).toReal`.

This is the only measure-theoretic input needed for trimming.
-/
lemma toReal_measure_le_add_of_subset_union
    [IsFiniteMeasure μ]
    {A B D : Set α}
    (hsub : A ⊆ D ∪ B) :
    (μ A).toReal ≤ (μ D).toReal + (μ B).toReal := by
  have hμ : μ A ≤ μ D + μ B := by
    calc
      μ A ≤ μ (D ∪ B) := measure_mono hsub
      _ ≤ μ D + μ B := measure_union_le D B
  have hDfin : μ D ≠ ∞ := by finiteness
  have hBfin : μ B ≠ ∞ := by finiteness
  have hsumfin : μ D + μ B ≠ ∞ := by finiteness
  have hreal : (μ A).toReal ≤ (μ D + μ B).toReal :=
    ENNReal.toReal_mono hsumfin hμ
  simpa [ENNReal.toReal_add hDfin hBfin] using hreal

/-- `μ.real` agrees with `ENNReal.toReal` on finite measures. -/
lemma measureReal_eq_toReal (s : Set α) : μ.real s = (μ s).toReal := rfl

/--
Abstract trimming lemma.

If `D = A \ B`, `μ(A) ≥ ε/2`, and `μ(B) ≤ ε/4`, then
`μ(D) ≥ ε/4`, with all masses read as real numbers via `ENNReal.toReal`.
-/
lemma trimmed_measure_lower_bound
    [IsFiniteMeasure μ]
    {ε : ℝ}
    {A B D : Set α}
    (hD : D = A \ B)
    (hA_lower : ε / 2 ≤ (μ A).toReal)
    (hB_upper : (μ B).toReal ≤ ε / 4) :
    ε / 4 ≤ (μ D).toReal := by
  have hsub : A ⊆ D ∪ B := by
    intro x hxA
    by_cases hxB : x ∈ B
    · exact Or.inr hxB
    · exact Or.inl (by
        rw [hD]
        exact ⟨hxA, hxB⟩)
  have hμ : (μ A).toReal ≤ (μ D).toReal + (μ B).toReal :=
    toReal_measure_le_add_of_subset_union (μ := μ) hsub
  linarith

/-- Same bound with `μ.real` notation. -/
lemma trimmed_measureReal_lower_bound
    [IsFiniteMeasure μ]
    {ε : ℝ}
    {A B D : Set α}
    (hD : D = A \ B)
    (hA_lower : ε / 2 ≤ μ.real A)
    (hB_upper : μ.real B ≤ ε / 4) :
    ε / 4 ≤ μ.real D := by
  simpa [measureReal_eq_toReal] using
    trimmed_measure_lower_bound (μ := μ) hD
      (by simpa [measureReal_eq_toReal] using hA_lower)
      (by simpa [measureReal_eq_toReal] using hB_upper)

/--
The `D₊` trimming step.

In applications:
* `A = C \ E`, the part of the cap missing from `E`;
* `B = bandPlus`, the thin band near the cap boundary;
* `Dplus = (C \ E) \ bandPlus`.
-/
lemma dplus_measure_lower_bound
    [IsFiniteMeasure μ]
    {ε : ℝ}
    {C E bandPlus Dplus : Set α}
    (hDplus : Dplus = (C \ E) \ bandPlus)
    (hmissing : ε / 2 ≤ (μ (C \ E)).toReal)
    (hbandPlus : (μ bandPlus).toReal ≤ ε / 4) :
    ε / 4 ≤ (μ Dplus).toReal := by
  exact trimmed_measure_lower_bound
    (μ := μ)
    (A := C \ E)
    (B := bandPlus)
    (D := Dplus)
    hDplus hmissing hbandPlus

/--
The `D₋` trimming step.

In applications:
* `A = E \ C`, the part of `E` below/outside the cap;
* `B = bandMinus`, the thin band near the cap boundary;
* `Dminus = (E \ C) \ bandMinus`.
-/
lemma dminus_measure_lower_bound
    [IsFiniteMeasure μ]
    {ε : ℝ}
    {C E bandMinus Dminus : Set α}
    (hDminus : Dminus = (E \ C) \ bandMinus)
    (hextra : ε / 2 ≤ (μ (E \ C)).toReal)
    (hbandMinus : (μ bandMinus).toReal ≤ ε / 4) :
    ε / 4 ≤ (μ Dminus).toReal := by
  exact trimmed_measure_lower_bound
    (μ := μ)
    (A := E \ C)
    (B := bandMinus)
    (D := Dminus)
    hDminus hextra hbandMinus

/--
Pure real lemma: if two halves are equal and their sum is at least `ε`,
then each half is at least `ε / 2`.

This is the algebra behind
`μ(C \ E) = μ(E \ C) = μ(E △ C) / 2`.
-/
lemma halves_lower_bound_of_equal_sum
    {ε miss extra : ℝ}
    (hbalance : miss = extra)
    (hfar : ε ≤ miss + extra) :
    ε / 2 ≤ miss ∧ ε / 2 ≤ extra := by
  constructor <;> linarith

/--
Combined trimming package from already-balanced missing/extra masses.

This is the exact measure-theoretic block used after proving
`μ(C \ E) = μ(E \ C) ≥ ε / 2` and after choosing bands of mass at most `ε / 4`.
-/
theorem dplus_dminus_measure_lower_bound
    [IsFiniteMeasure μ]
    {ε : ℝ}
    {C E bandPlus bandMinus Dplus Dminus : Set α}
    (hDplus : Dplus = (C \ E) \ bandPlus)
    (hDminus : Dminus = (E \ C) \ bandMinus)
    (hmissing : ε / 2 ≤ (μ (C \ E)).toReal)
    (hextra : ε / 2 ≤ (μ (E \ C)).toReal)
    (hbandPlus : (μ bandPlus).toReal ≤ ε / 4)
    (hbandMinus : (μ bandMinus).toReal ≤ ε / 4) :
    ε / 4 ≤ (μ Dplus).toReal ∧ ε / 4 ≤ (μ Dminus).toReal := by
  constructor
  · exact dplus_measure_lower_bound
      (μ := μ) hDplus hmissing hbandPlus
  · exact dminus_measure_lower_bound
      (μ := μ) hDminus hextra hbandMinus

/-- Combined trimming with `μ.real`. -/
theorem dplus_dminus_measureReal_lower_bound
    [IsFiniteMeasure μ]
    {ε : ℝ}
    {C E bandPlus bandMinus Dplus Dminus : Set α}
    (hDplus : Dplus = (C \ E) \ bandPlus)
    (hDminus : Dminus = (E \ C) \ bandMinus)
    (hmissing : ε / 2 ≤ μ.real (C \ E))
    (hextra : ε / 2 ≤ μ.real (E \ C))
    (hbandPlus : μ.real bandPlus ≤ ε / 4)
    (hbandMinus : μ.real bandMinus ≤ ε / 4) :
    ε / 4 ≤ μ.real Dplus ∧ ε / 4 ≤ μ.real Dminus := by
  simpa [measureReal_eq_toReal] using
    dplus_dminus_measure_lower_bound (μ := μ) hDplus hDminus
      (by simpa [measureReal_eq_toReal] using hmissing)
      (by simpa [measureReal_eq_toReal] using hextra)
      (by simpa [measureReal_eq_toReal] using hbandPlus)
      (by simpa [measureReal_eq_toReal] using hbandMinus)

end MeasureTrimming
end SphericalPolarization
