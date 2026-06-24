import PptFactorization.AppendixBSpikeLowerBound
import PptFactorization.AristotleTargets.LowerMixedLowerConcreteChoices

/-!
Deterministic upper-bound core lemmas for the one-quadratic mixed-word branch.

These lemmas transport the lower-side cyclic one-`Q` word factorization to the
upper mixed-word envelope shape, using only the background operator-norm bound
on `K_N` and the sharp-radius quadratic bound.
-/

namespace AppendixB

open PptFactorization.RandomMatrixModel
open PptFactorization.HighProbabilityBounds
open scoped BigOperators Matrix.Norms.Frobenius

variable {p q : Type*}
variable [Fintype p] [Fintype q]
variable [DecidableEq p] [DecidableEq q]
variable [Nonempty p] [Nonempty q]

/-- Canonical background operator-norm scale for mixed-word envelopes. -/
noncomputable def upperMixedWordAbound (M N : ℝ) : ℝ :=
  M / N

/-- Canonical one-`Q` trace-envelope scale at the sharp spherical radius. -/
noncomputable def upperMixedWordQ1bound (N speed a : ℝ) : ℝ :=
  Real.sqrt (Fintype.card (BipIndex p q)) *
    sharpSphericalRadius N speed a ^ 2

omit [Nonempty p] [Nonempty q] in
theorem opNorm_pow_le_pow_opNorm
    (A : BipMatrix p q) (n : ℕ) :
    opNorm (p := p) (q := q) (A ^ n) ≤
      opNorm (p := p) (q := q) A ^ n := by
  induction n with
  | zero =>
      exact lower_opNorm_one_le (p := p) (q := q)
  | succ n ih =>
      have hop_nonneg : 0 ≤ opNorm (p := p) (q := q) A := by
        unfold opNorm
        positivity
      calc
        opNorm (p := p) (q := q) (A ^ (n + 1)) =
            opNorm (p := p) (q := q) (A * A ^ n) := by
              rw [pow_succ']
        _ ≤ opNorm (p := p) (q := q) A * opNorm (p := p) (q := q) (A ^ n) :=
            lower_opNorm_mul_le (p := p) (q := q) (A := A) (B := A ^ n)
        _ ≤ opNorm (p := p) (q := q) A * opNorm (p := p) (q := q) A ^ n :=
            mul_le_mul_of_nonneg_left ih hop_nonneg
        _ = opNorm (p := p) (q := q) A ^ (n + 1) := by
          rw [pow_succ']

omit [Nonempty p] [Nonempty q] in
theorem localWordMatrixProduct_eq_of_noL
    {k : ℕ} (A L L' Q : BipMatrix p q) (w : Fin k → LocalExpansionLetter)
    (hNoL : ∀ i : Fin k, w i ≠ LocalExpansionLetter.L) :
    localWordMatrixProduct (p := p) (q := q) A L Q w =
      localWordMatrixProduct (p := p) (q := q) A L' Q w := by
  induction k generalizing A L L' Q with
  | zero =>
      simp [localWordMatrixProduct]
  | succ k ih =>
      let wt : Fin k → LocalExpansionLetter := Fin.tail w
      have hNoL_tail : ∀ i : Fin k, wt i ≠ LocalExpansionLetter.L := by
        intro i hi
        exact hNoL i.succ hi
      have iht := ih A L L' Q wt hNoL_tail
      cases h : w 0 with
      | A =>
          change localLetterMatrix A L Q (w 0) *
              localWordMatrixProduct (p := p) (q := q) A L Q wt =
            localLetterMatrix A L' Q (w 0) *
              localWordMatrixProduct (p := p) (q := q) A L' Q wt
          rw [h]
          simp [localLetterMatrix, iht]
      | L =>
          exact False.elim (hNoL 0 h)
      | Q =>
          change localLetterMatrix A L Q (w 0) *
              localWordMatrixProduct (p := p) (q := q) A L Q wt =
            localLetterMatrix A L' Q (w 0) *
              localWordMatrixProduct (p := p) (q := q) A L' Q wt
          rw [h]
          simp [localLetterMatrix, iht]

theorem localWordHasOneQuadraticDefect_noLinear
    {k : ℕ} {w : Fin k → LocalExpansionLetter}
    (h : localWordHasOneQuadraticDefect w) :
    ∀ i : Fin k, w i ≠ LocalExpansionLetter.L := by
  intro i hi
  have hL :
      localWordLetterCount LocalExpansionLetter.L w = 0 := h.1
  have hpos :
      0 < localWordLetterCount LocalExpansionLetter.L w :=
    lower_localWordLetterCount_pos_of_exists
      (letter := LocalExpansionLetter.L) (w := w) ⟨i, hi⟩
  exact (ne_of_gt hpos hL).elim

omit [Nonempty p] [Nonempty q] in
/-- If a word has no linear letters, replacing the linear-letter matrix by
zero does not change its ordered matrix product. -/
theorem localWordMatrixProduct_eq_zeroLinear_of_noLinear
    {k : ℕ} {A L Q : BipMatrix p q} {w : Fin k → LocalExpansionLetter}
    (hNoL : ∀ i : Fin k, w i ≠ LocalExpansionLetter.L) :
    localWordMatrixProduct (p := p) (q := q) A L Q w =
      localWordMatrixProduct (p := p) (q := q) A 0 Q w :=
  localWordMatrixProduct_eq_of_noL (p := p) (q := q) A L 0 Q w hNoL

omit [Nonempty p] [Nonempty q] in
/-- Scaled trace version of
`localWordMatrixProduct_eq_zeroLinear_of_noLinear`. -/
theorem localWordScaledTraceTerm_eq_zeroLinear_of_noLinear
    {N : ℝ} {k : ℕ} {A L Q : BipMatrix p q}
    {w : Fin k → LocalExpansionLetter}
    (hNoL : ∀ i : Fin k, w i ≠ LocalExpansionLetter.L) :
    localWordScaledTraceTerm (p := p) (q := q) N A L Q w =
      localWordScaledTraceTerm (p := p) (q := q) N A 0 Q w := by
  simp [localWordScaledTraceTerm,
    localWordMatrixProduct_eq_zeroLinear_of_noLinear
      (p := p) (q := q) (A := A) (L := L) (Q := Q) (w := w) hNoL]

omit [Nonempty p] [Nonempty q] in
theorem localWordScaledTraceTerm_eq_of_noLinear
    (N : ℝ) (A L Q : BipMatrix p q) {k : ℕ} {w : Fin k → LocalExpansionLetter}
    (hNoL : ∀ i : Fin k, w i ≠ LocalExpansionLetter.L) :
    localWordScaledTraceTerm (p := p) (q := q) N A L Q w =
      localWordScaledTraceTerm (p := p) (q := q) N A 0 Q w :=
  localWordScaledTraceTerm_eq_zeroLinear_of_noLinear
    (p := p) (q := q) (N := N) (A := A) (L := L) (Q := Q) (w := w) hNoL

theorem localWordScaledTraceTerm_oneQuadratic_le_envelope
    {N M a speed : ℝ} {k : ℕ}
    {A L Q : BipMatrix p q} {w : Fin k → LocalExpansionLetter}
    (hNpos : 0 < N) (hM : 0 ≤ M) (hk3 : 3 ≤ k)
    (hA_op : opNorm (p := p) (q := q) A ≤ M / N)
    (hQ_frob :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) Q ≤
        upperMixedWordQ1bound (p := p) (q := q) N speed a /
          Real.sqrt (Fintype.card (BipIndex p q)))
    (hOneQ : localWordHasOneQuadraticDefect w) :
    |localWordScaledTraceTerm (p := p) (q := q) N A L Q w| ≤
      N ^ (k - 1) *
        upperMixedWordAbound M N ^ (k - 1) *
          upperMixedWordQ1bound (p := p) (q := q) N speed a := by
  have hNoL :=
    localWordHasOneQuadraticDefect_noLinear hOneQ
  have hQone :
      localWordLetterCount LocalExpansionLetter.Q w = 1 := hOneQ.2
  rw [localWordScaledTraceTerm_eq_zeroLinear_of_noLinear
    (p := p) (q := q) (N := N) (A := A) (L := L) (Q := Q) (w := w) hNoL]
  rcases lower_localWordMatrixProduct_exists_powA_Q_powA_of_oneQ_noL
      (p := p) (q := q) A Q w hNoL hQone with
    ⟨r, s, hrs, hprod⟩
  have hN : 0 ≤ N := le_of_lt hNpos
  have hNpow : 0 ≤ N ^ (k - 1) := pow_nonneg hN _
  have htrace_eq :
      (Matrix.trace
        (localWordMatrixProduct (p := p) (q := q) A 0 Q w)).re =
        (Matrix.trace (Q * A ^ (k - 1))).re := by
    rw [hprod]
    exact congrArg Complex.re
      (lower_trace_powA_Q_powA_eq_trace_Q_powA
        (p := p) (q := q) A Q hrs)
  have hk1 : k - 1 = (k - 2) + 1 := by omega
  have htrace :=
    matrix_abs_re_trace_le_sqrt_card_mul_frobenius_norm
      (n := BipIndex p q) (Q * A ^ (k - 1))
  have hfrob_mul :=
    lower_frobeniusNorm_mul_le_frobeniusNorm_mul_opNorm
      (p := p) (q := q) (A := Q) (B := A ^ (k - 1))
  have hop :
      opNorm (p := p) (q := q) (A ^ (k - 1)) ≤
        (M / N) ^ (k - 1) :=
    le_trans
      (opNorm_pow_le_pow_opNorm (p := p) (q := q) A (k - 1))
      (pow_le_pow_left₀ (by unfold opNorm; positivity) hA_op (k - 1))
  have hQ_nonneg :
      0 ≤ frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) Q := by
    unfold frobeniusNorm
    positivity
  have hsqrt_nonneg :
      0 ≤ Real.sqrt (Fintype.card (BipIndex p q)) := Real.sqrt_nonneg _
  have htrace_bound :
      |(Matrix.trace (Q * A ^ (k - 1))).re| ≤
        (Real.sqrt (Fintype.card (BipIndex p q)) *
            frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) Q) *
          (M / N) ^ (k - 1) := by
    calc
      |(Matrix.trace (Q * A ^ (k - 1))).re| ≤
          Real.sqrt (Fintype.card (BipIndex p q)) *
            frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
              (Q * A ^ (k - 1)) := by
            simpa [frobeniusNorm] using htrace
      _ ≤
          Real.sqrt (Fintype.card (BipIndex p q)) *
            (frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) Q *
              opNorm (p := p) (q := q) (A ^ (k - 1))) := by
            exact mul_le_mul_of_nonneg_left hfrob_mul hsqrt_nonneg
      _ =
          (Real.sqrt (Fintype.card (BipIndex p q)) *
              frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) Q) *
            opNorm (p := p) (q := q) (A ^ (k - 1)) := by ring
      _ ≤
          (Real.sqrt (Fintype.card (BipIndex p q)) *
              frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) Q) *
            (M / N) ^ (k - 1) := by
            exact mul_le_mul_of_nonneg_left hop
              (mul_nonneg hsqrt_nonneg hQ_nonneg)
  unfold localWordScaledTraceTerm
  rw [htrace_eq, abs_mul, abs_of_nonneg hNpow]
  have hbound :
      (Real.sqrt (Fintype.card (BipIndex p q)) *
          frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) Q) *
        (M / N) ^ (k - 1) ≤
        upperMixedWordAbound M N ^ (k - 1) *
          upperMixedWordQ1bound (p := p) (q := q) N speed a := by
    unfold upperMixedWordAbound upperMixedWordQ1bound
    haveI : Nonempty (BipIndex p q) := inferInstance
    have hcardpos : 0 < (Fintype.card (BipIndex p q) : ℝ) := by
      exact_mod_cast Fintype.card_pos
    have hsqrt_pos :
        0 < Real.sqrt (Fintype.card (BipIndex p q) : ℝ) :=
      Real.sqrt_pos.mpr hcardpos
    have hMN_nonneg : 0 ≤ (M / N) ^ (k - 1) := by
      exact pow_nonneg (div_nonneg hM (le_of_lt hNpos)) _
    calc
      (Real.sqrt (Fintype.card (BipIndex p q)) *
          frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) Q) *
        (M / N) ^ (k - 1) ≤
          (Real.sqrt (Fintype.card (BipIndex p q)) *
              (upperMixedWordQ1bound (p := p) (q := q) N speed a /
                Real.sqrt (Fintype.card (BipIndex p q)))) *
            (M / N) ^ (k - 1) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hQ_frob hsqrt_nonneg) hMN_nonneg
      _ = upperMixedWordQ1bound (p := p) (q := q) N speed a * (M / N) ^ (k - 1) := by
          field_simp [hsqrt_pos.ne']
      _ = upperMixedWordAbound M N ^ (k - 1) *
            upperMixedWordQ1bound (p := p) (q := q) N speed a := by
          unfold upperMixedWordAbound
          ring
  calc
    N ^ (k - 1) * |(Matrix.trace (Q * A ^ (k - 1))).re| ≤
        N ^ (k - 1) *
          ((Real.sqrt (Fintype.card (BipIndex p q)) *
              frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) Q) *
            (M / N) ^ (k - 1)) :=
      mul_le_mul_of_nonneg_left htrace_bound hNpow
    _ ≤ N ^ (k - 1) *
          (upperMixedWordAbound M N ^ (k - 1) *
            upperMixedWordQ1bound (p := p) (q := q) N speed a) := by
          exact mul_le_mul_of_nonneg_left hbound hNpow
    _ = N ^ (k - 1) * upperMixedWordAbound M N ^ (k - 1) *
          upperMixedWordQ1bound (p := p) (q := q) N speed a := by ring

end AppendixB
