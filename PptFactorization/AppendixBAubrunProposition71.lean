import PptFactorization.AppendixBAubrunMomentInput

/-!
# Appendix B: Aubrun Proposition 7.1 interface

This file gives the proposition-facing Lean shape of Aubrun's Proposition 7.1.

The no-input part already proved in the repo is the Wick/closed-walk reduction:
the trace moment of the off-diagonal partial transpose is exactly controlled
by a finite sum over closed walks, sample-column words, and surviving Wick
contractions.

The remaining mathematical core of Aubrun Proposition 7.1 is precisely the
finite combinatorial bound on that surviving-contraction sum:

`≤ (2 / s)^m (d + Q(m))^(m+2) (sqrt s + Q(m))^m`

for a polynomial `Q` independent of `d` and `s`.

No theorem below asserts that combinatorial estimate for free.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal

noncomputable section

namespace PptFactorization
namespace AppendixB

open RandomMatrixModel GaussianModel HighProbabilityBounds
open TraceWickExpansion

variable {p q σ : Type*}
variable [Fintype p] [Fintype q] [Fintype σ]
variable [DecidableEq p] [DecidableEq q] [DecidableEq σ]

/-! ## The exact finite sum controlled by Aubrun's counting argument -/

/-- The finite surviving-contraction sum which remains after the no-input
Wick/Isserlis expansion of the off-diagonal trace moment.  Aubrun Proposition
7.1 is exactly the sharp polynomial estimate for this quantity. -/
def aubrunSurvivingPairingSumNorm (m : ℕ) : ℝ :=
  ∑ w : ClosedWalk (BipIndex p q) m,
    ∑ α : Fin (m + 1) → σ,
      ‖pathGammaCoeff (p := p) (q := q) (σ := σ) w.1 w.1 w.2 α *
        (Fintype.card
          (SurvivingClosedWalkPairing
            (p := p) (q := q) (σ := σ) w α) : ℂ)‖

/-- No-input reduction of the off-diagonal trace moment to Aubrun's finite
surviving-contraction sum. -/
theorem gaussianWishartGammaOffDiagonal_traceMoment_norm_le_aubrunSurvivingPairingSumNorm
    (m : ℕ) :
    ‖gaussianWishartGammaOffDiagonalTraceMoment
        (p := p) (q := q) (σ := σ) m‖ ≤
      aubrunSurvivingPairingSumNorm (p := p) (q := q) (σ := σ) m := by
  simpa [aubrunSurvivingPairingSumNorm] using
    gaussianWishartGammaOffDiagonal_traceMoment_norm_le_survivingPairing_sum_norm
      (p := p) (q := q) (σ := σ) m

/-! ## Proposition-facing closure theorem -/

/-- Aubrun Proposition 7.1, as a closure theorem from the exact finite
surviving-contraction estimate.

The hypothesis `hSharp` is the real combinatorial content of Proposition 7.1.
Everything else in the theorem is already proved in the repository. -/
theorem AubrunProposition71_traceMomentBound_of_survivingPairing_bound
    {Q : ℕ → ℝ} {d s : ℝ}
    (hSharp :
      ∀ m,
        aubrunSurvivingPairingSumNorm (p := p) (q := q) (σ := σ) m ≤
          aubrunOffDiagonalTraceMomentEnvelope Q d s m) :
    ∀ m,
      AubrunOffDiagonalTraceMomentBound
        (p := p) (q := q) (σ := σ) m
        (aubrunOffDiagonalTraceMomentEnvelope Q d s m) := by
  intro m
  exact
    (gaussianWishartGammaOffDiagonal_traceMoment_norm_le_aubrunSurvivingPairingSumNorm
      (p := p) (q := q) (σ := σ) m).trans (hSharp m)

/-- Exact-power version of the proposition-facing closure.  The closed-walk
parameter `m` computes the trace power `m + 1`. -/
theorem AubrunProposition71_traceMomentPowerBound_succ_of_survivingPairing_bound
    {Q : ℕ → ℝ} {d s : ℝ}
    (hSharp :
      ∀ m,
        aubrunSurvivingPairingSumNorm (p := p) (q := q) (σ := σ) m ≤
          aubrunOffDiagonalTraceMomentEnvelope Q d s m) :
    ∀ m,
      AubrunOffDiagonalTraceMomentPowerBound
        (p := p) (q := q) (σ := σ) (m + 1)
        (aubrunOffDiagonalTraceMomentEnvelope Q d s m) := by
  intro m
  simpa [AubrunOffDiagonalTraceMomentPowerBound,
    gaussianWishartGammaOffDiagonalTraceMomentPower_succ] using
    AubrunProposition71_traceMomentBound_of_survivingPairing_bound
      (p := p) (q := q) (σ := σ) (Q := Q) (d := d) (s := s) hSharp m

/-- Positive-power version of the proposition-facing closure. -/
theorem AubrunProposition71_traceMomentPowerBound_of_survivingPairing_bound
    {Q : ℕ → ℝ} {d s : ℝ}
    (hSharp :
      ∀ m,
        aubrunSurvivingPairingSumNorm (p := p) (q := q) (σ := σ) m ≤
          aubrunOffDiagonalTraceMomentEnvelope Q d s m)
    {m : ℕ} (hm : 0 < m) :
    AubrunOffDiagonalTraceMomentPowerBound
      (p := p) (q := q) (σ := σ) m
      (aubrunOffDiagonalTraceMomentEnvelope Q d s (m - 1)) := by
  have h :=
    AubrunProposition71_traceMomentPowerBound_succ_of_survivingPairing_bound
      (p := p) (q := q) (σ := σ) (Q := Q) (d := d) (s := s) hSharp (m - 1)
  have hm_eq : m - 1 + 1 = m := by omega
  simpa [hm_eq] using h

/-- Proposition 7.1 packaged in the literal existential-polynomial form:
if one supplies a nonnegative polynomial envelope `Q` and proves Aubrun's
finite surviving-contraction estimate for it, then the corresponding
trace-moment statement follows.

The polynomial hypotheses are explicit rather than hidden in a structure:
`Q(m) ≤ C (m+1)^r` for fixed `C,r`, independently of `d` and `s`. -/
theorem AubrunProposition71_exists_traceMomentBound_of_survivingPairing_bound
    {Q : ℕ → ℝ} {d s : ℝ}
    (hQ_nonneg : ∀ m, 0 ≤ Q m)
    (hQ_poly :
      ∃ C : ℝ, ∃ r : ℕ, 0 ≤ C ∧
        ∀ m, Q m ≤ C * ((m : ℝ) + 1) ^ r)
    (hSharp :
      ∀ m,
        aubrunSurvivingPairingSumNorm (p := p) (q := q) (σ := σ) m ≤
          aubrunOffDiagonalTraceMomentEnvelope Q d s m) :
    ∃ Q' : ℕ → ℝ,
      (∀ m, 0 ≤ Q' m) ∧
      (∃ C : ℝ, ∃ r : ℕ, 0 ≤ C ∧
        ∀ m, Q' m ≤ C * ((m : ℝ) + 1) ^ r) ∧
      ∀ m,
        AubrunOffDiagonalTraceMomentBound
          (p := p) (q := q) (σ := σ) m
          (aubrunOffDiagonalTraceMomentEnvelope Q' d s m) := by
  refine ⟨Q, hQ_nonneg, hQ_poly, ?_⟩
  exact AubrunProposition71_traceMomentBound_of_survivingPairing_bound
    (p := p) (q := q) (σ := σ) (Q := Q) (d := d) (s := s) hSharp

/-! ## Concrete `Fin d, Fin d, Fin s` specialization -/

/-- Concrete specialization of the proposition-facing closure for the paper's
square bipartite model `p = q = Fin d`, with `s` Gaussian columns. -/
theorem AubrunProposition71_concrete_traceMomentBound_of_survivingPairing_bound
    {dNat sNat : ℕ} {Q : ℕ → ℝ}
    (hSharp :
      ∀ m,
        aubrunSurvivingPairingSumNorm
            (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) m ≤
          aubrunOffDiagonalTraceMomentEnvelope Q (dNat : ℝ) (sNat : ℝ) m) :
    ∀ m,
      AubrunOffDiagonalTraceMomentBound
        (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat) m
        (aubrunOffDiagonalTraceMomentEnvelope Q (dNat : ℝ) (sNat : ℝ) m) := by
  exact AubrunProposition71_traceMomentBound_of_survivingPairing_bound
    (p := Fin dNat) (q := Fin dNat) (σ := Fin sNat)
    (Q := Q) (d := (dNat : ℝ)) (s := (sNat : ℝ)) hSharp

/-! ## A checked polynomial example for the counting-core envelope -/

/-- The counting core's model envelope `(m+1)^r`, cast to reals, is genuinely
polynomial in the explicit sense used above.  This is not Aubrun's missing
encoding theorem; it only verifies the scalar polynomial side once such a
fixed-rank encoding is available. -/
theorem aubrunCountingCoreQ_real_polynomial (r : ℕ) :
    (∀ m, 0 ≤ ((TraceWickExpansion.AubrunCountingCore.Q r m : ℕ) : ℝ)) ∧
      ∃ C : ℝ, ∃ R : ℕ, 0 ≤ C ∧
        ∀ m,
          ((TraceWickExpansion.AubrunCountingCore.Q r m : ℕ) : ℝ) ≤
            C * ((m : ℝ) + 1) ^ R := by
  constructor
  · intro m
    positivity
  · refine ⟨1, r, by norm_num, ?_⟩
    intro m
    simp [TraceWickExpansion.AubrunCountingCore.Q]

end AppendixB
end PptFactorization
