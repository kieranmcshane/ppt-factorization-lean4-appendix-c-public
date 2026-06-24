import PptFactorization.AppendixBSpikeLowerBound
import PptFactorization.AristotleTargets.LowerMixedLowerConcreteChoices
import PptFactorization.UpperMixedOneQuadraticBranch

/-!
Deterministic upper-bound core lemmas for the one-linear mixed-word branch.

These lemmas mirror the closed one-quadratic branch: cyclic one-`L` word
factorization, trace pairing with the background operator-norm scale, and the
sharp-radius linear Frobenius bound.
-/

namespace AppendixB

open PptFactorization.RandomMatrixModel
open PptFactorization.HighProbabilityBounds
open scoped BigOperators Matrix.Norms.Frobenius

variable {p q : Type*}
variable [Fintype p] [Fintype q]
variable [DecidableEq p] [DecidableEq q]
variable [Nonempty p] [Nonempty q]

/-- Canonical one-`L` trace-envelope scale at the sharp spherical radius. -/
noncomputable def upperMixedWordL1bound (N M speed a : ℝ) : ℝ :=
  Real.sqrt (Fintype.card (BipIndex p q)) *
    (2 * (M / Real.sqrt N) * sharpSphericalRadius N speed a)

omit [Nonempty p] [Nonempty q] in
theorem localWordHasOneLinearDefect_noQuadratic
    {k : ℕ} {w : Fin k → LocalExpansionLetter}
    (h : localWordHasOneLinearDefect w) :
    ∀ i : Fin k, w i ≠ LocalExpansionLetter.Q := by
  intro i hi
  have hQ :
      localWordLetterCount LocalExpansionLetter.Q w = 0 := h.2
  have hpos :
      0 < localWordLetterCount LocalExpansionLetter.Q w :=
    lower_localWordLetterCount_pos_of_exists
      (letter := LocalExpansionLetter.Q) (w := w) ⟨i, hi⟩
  exact (ne_of_gt hpos hQ).elim

omit [Nonempty p] [Nonempty q] in
theorem localWordMatrixProduct_eq_of_noQ
    {k : ℕ} (A L Q Q' : BipMatrix p q) (w : Fin k → LocalExpansionLetter)
    (hNoQ : ∀ i : Fin k, w i ≠ LocalExpansionLetter.Q) :
    localWordMatrixProduct (p := p) (q := q) A L Q w =
      localWordMatrixProduct (p := p) (q := q) A L Q' w := by
  induction k generalizing A L Q Q' with
  | zero =>
      simp [localWordMatrixProduct]
  | succ k ih =>
      let wt : Fin k → LocalExpansionLetter := Fin.tail w
      have hNoQ_tail : ∀ i : Fin k, wt i ≠ LocalExpansionLetter.Q := by
        intro i hi
        exact hNoQ i.succ hi
      have iht := ih A L Q Q' wt hNoQ_tail
      cases h : w 0 with
      | A =>
          change localLetterMatrix A L Q (w 0) *
              localWordMatrixProduct (p := p) (q := q) A L Q wt =
            localLetterMatrix A L Q' (w 0) *
              localWordMatrixProduct (p := p) (q := q) A L Q' wt
          rw [h]
          simp [localLetterMatrix, iht]
      | L =>
          change localLetterMatrix A L Q (w 0) *
              localWordMatrixProduct (p := p) (q := q) A L Q wt =
            localLetterMatrix A L Q' (w 0) *
              localWordMatrixProduct (p := p) (q := q) A L Q' wt
          rw [h]
          simp [localLetterMatrix, iht]
      | Q =>
          exact False.elim (hNoQ 0 h)

omit [Nonempty p] [Nonempty q] in
/-- If a word has no quadratic letters, replacing the quadratic-letter matrix by
zero does not change its ordered matrix product. -/
theorem localWordMatrixProduct_eq_zeroQuadratic_of_noQuadratic
    {k : ℕ} {A L Q : BipMatrix p q} {w : Fin k → LocalExpansionLetter}
    (hNoQ : ∀ i : Fin k, w i ≠ LocalExpansionLetter.Q) :
    localWordMatrixProduct (p := p) (q := q) A L Q w =
      localWordMatrixProduct (p := p) (q := q) A L 0 w :=
  localWordMatrixProduct_eq_of_noQ (p := p) (q := q) A L Q 0 (w := w) hNoQ

omit [Nonempty p] [Nonempty q] in
theorem localWordScaledTraceTerm_eq_zeroQuadratic_of_noQuadratic
    {N : ℝ} {k : ℕ} {A L Q : BipMatrix p q}
    {w : Fin k → LocalExpansionLetter}
    (hNoQ : ∀ i : Fin k, w i ≠ LocalExpansionLetter.Q) :
    localWordScaledTraceTerm (p := p) (q := q) N A L Q w =
      localWordScaledTraceTerm (p := p) (q := q) N A L 0 w := by
  simp [localWordScaledTraceTerm,
    localWordMatrixProduct_eq_zeroQuadratic_of_noQuadratic
      (p := p) (q := q) (A := A) (L := L) (Q := Q) (w := w) hNoQ]

omit [Nonempty p] [Nonempty q] in
theorem localWordScaledTraceTerm_eq_of_noQuadratic
    (N : ℝ) (A L Q : BipMatrix p q) {k : ℕ} {w : Fin k → LocalExpansionLetter}
    (hNoQ : ∀ i : Fin k, w i ≠ LocalExpansionLetter.Q) :
    localWordScaledTraceTerm (p := p) (q := q) N A L Q w =
      localWordScaledTraceTerm (p := p) (q := q) N A L 0 w :=
  localWordScaledTraceTerm_eq_zeroQuadratic_of_noQuadratic
    (p := p) (q := q) (N := N) (A := A) (L := L) (Q := Q) (w := w) hNoQ

/-- A word with exactly one linear defect and no quadratic defect evaluates as
a background power, then the linear letter, then another background power. -/
theorem lower_localWordMatrixProduct_exists_powA_L_powA_of_oneL_noQ
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    {k : ℕ} (A L : BipMatrix p q) (w : Fin k → LocalExpansionLetter)
    (hNoQ : ∀ i : Fin k, w i ≠ LocalExpansionLetter.Q)
    (hLone : localWordLetterCount LocalExpansionLetter.L w = 1) :
    ∃ r s : ℕ, r + 1 + s = k ∧
      localWordMatrixProduct (p := p) (q := q) A L 0 w = A ^ r * L * A ^ s := by
  induction k with
  | zero =>
      simp [localWordLetterCount] at hLone
  | succ k ih =>
      let wt : Fin k → LocalExpansionLetter := Fin.tail w
      have hcount := localWordLetterCount_cons LocalExpansionLetter.L (w 0) wt
      by_cases h0L : w 0 = LocalExpansionLetter.L
      · have htailL0 : localWordLetterCount LocalExpansionLetter.L wt = 0 := by
          have hcountw :
              localWordLetterCount LocalExpansionLetter.L w =
                (if w 0 = LocalExpansionLetter.L then 1 else 0) +
                  localWordLetterCount LocalExpansionLetter.L wt := by
            simpa [wt, Fin.cons_self_tail] using hcount
          rw [hcountw] at hLone
          simp [h0L] at hLone
          exact hLone
        have hNoQ_tail : ∀ i : Fin k, wt i ≠ LocalExpansionLetter.Q := by
          intro i hi
          exact hNoQ i.succ hi
        have hNoL_tail : ∀ i : Fin k, wt i ≠ LocalExpansionLetter.L := by
          intro i hi
          exact lower_localWord_no_letter_of_count_zero htailL0 i hi
        refine ⟨0, k, ?_, ?_⟩
        · omega
        · have htail :=
            lower_localWordMatrixProduct_pow_A_of_noL_noQ
              (p := p) (q := q) A 0 wt hNoL_tail hNoQ_tail
          have htail' :
              localWordMatrixProduct (p := p) (q := q) A L 0 wt = A ^ k := by
            have hNoL_prod :=
              localWordMatrixProduct_eq_of_noL
                (p := p) (q := q) A L 0 0 (w := wt) hNoL_tail
            calc
              localWordMatrixProduct (p := p) (q := q) A L 0 wt
                  = localWordMatrixProduct (p := p) (q := q) A 0 0 wt := hNoL_prod
              _ = A ^ k := htail
          have hprod :
              localWordMatrixProduct (p := p) (q := q) A L 0 w =
                L * localWordMatrixProduct (p := p) (q := q) A L 0 wt := by
            have hwt : (fun i : Fin k => w i.succ) = wt := rfl
            simp [localWordMatrixProduct, localLetterMatrix, h0L, hwt]
          calc
            localWordMatrixProduct (p := p) (q := q) A L 0 w =
                L * localWordMatrixProduct (p := p) (q := q) A L 0 wt := hprod
            _ = L * A ^ k := by rw [htail']
            _ = A ^ 0 * L * A ^ k := by simp
      · have h0A : w 0 = LocalExpansionLetter.A := by
          cases h : w 0 with
          | A => rfl
          | L => exact False.elim (h0L h)
          | Q => exact False.elim (hNoQ 0 h)
        have htailLone : localWordLetterCount LocalExpansionLetter.L wt = 1 := by
          have hcountw :
              localWordLetterCount LocalExpansionLetter.L w =
                (if w 0 = LocalExpansionLetter.L then 1 else 0) +
                  localWordLetterCount LocalExpansionLetter.L wt := by
            simpa [wt, Fin.cons_self_tail] using hcount
          rw [hcountw] at hLone
          simp [h0L] at hLone
          exact hLone
        have hNoQ_tail : ∀ i : Fin k, wt i ≠ LocalExpansionLetter.Q := by
          intro i hi
          exact hNoQ i.succ hi
        rcases ih (w := wt) hNoQ_tail htailLone with ⟨r, s, hrs, hprod⟩
        refine ⟨r + 1, s, ?_, ?_⟩
        · omega
        · change localLetterMatrix A L 0 (w 0) *
              localWordMatrixProduct (p := p) (q := q) A L 0 wt =
            A ^ (r + 1) * L * A ^ s
          rw [h0A, hprod]
          simp [localLetterMatrix, pow_succ', mul_assoc]

/-- Cyclic trace reduction for a word with one linear letter. -/
theorem lower_trace_powA_L_powA_eq_trace_L_powA
    {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    (A L : BipMatrix p q) {k r s : ℕ}
    (hrs : r + 1 + s = k) :
    Matrix.trace (A ^ r * L * A ^ s) =
      Matrix.trace (L * A ^ (k - 1)) := by
  have hcyc := Matrix.trace_mul_cycle (A := A ^ r) (B := L) (C := A ^ s)
  have hcomm := Matrix.trace_mul_comm (A := A ^ s * A ^ r) (B := L)
  calc
    Matrix.trace (A ^ r * L * A ^ s)
        = Matrix.trace (A ^ s * A ^ r * L) := hcyc
    _ = Matrix.trace (L * (A ^ s * A ^ r)) := hcomm
    _ = Matrix.trace (L * A ^ (k - 1)) := by
      have hsadd : s + r = k - 1 := by omega
      rw [← pow_add]
      rw [hsadd]

theorem localWordScaledTraceTerm_oneLinear_le_envelope
    {N M a speed : ℝ} {k : ℕ}
    {A L Q : BipMatrix p q} {w : Fin k → LocalExpansionLetter}
    (hNpos : 0 < N) (hM : 0 ≤ M) (_hk3 : 3 ≤ k)
    (hA_op : opNorm (p := p) (q := q) A ≤ M / N)
    (hL_frob :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) L ≤
        upperMixedWordL1bound (p := p) (q := q) N M speed a /
          Real.sqrt (Fintype.card (BipIndex p q)))
    (hOneL : localWordHasOneLinearDefect w) :
    |localWordScaledTraceTerm (p := p) (q := q) N A L Q w| ≤
      N ^ (k - 1) *
        upperMixedWordAbound M N ^ (k - 1) *
          upperMixedWordL1bound (p := p) (q := q) N M speed a := by
  have hNoQ :=
    localWordHasOneLinearDefect_noQuadratic hOneL
  have hLone :
      localWordLetterCount LocalExpansionLetter.L w = 1 := hOneL.1
  rw [localWordScaledTraceTerm_eq_zeroQuadratic_of_noQuadratic
    (p := p) (q := q) (N := N) (A := A) (L := L) (Q := Q) (w := w) hNoQ]
  rcases lower_localWordMatrixProduct_exists_powA_L_powA_of_oneL_noQ
      (p := p) (q := q) A L w hNoQ hLone with
    ⟨r, s, hrs, hprod⟩
  have hN : 0 ≤ N := le_of_lt hNpos
  have hNpow : 0 ≤ N ^ (k - 1) := pow_nonneg hN _
  have htrace_eq :
      (Matrix.trace
        (localWordMatrixProduct (p := p) (q := q) A L 0 w)).re =
        (Matrix.trace (L * A ^ (k - 1))).re := by
    rw [hprod]
    exact congrArg Complex.re
      (lower_trace_powA_L_powA_eq_trace_L_powA
        (p := p) (q := q) A L hrs)
  have htrace :=
    matrix_abs_re_trace_mul_le_frobenius_norm_mul
      (n := BipIndex p q) L (A ^ (k - 1))
  have hop :
      opNorm (p := p) (q := q) (A ^ (k - 1)) ≤
        (M / N) ^ (k - 1) :=
    le_trans
      (opNorm_pow_le_pow_opNorm (p := p) (q := q) A (k - 1))
      (pow_le_pow_left₀ (by unfold opNorm; positivity) hA_op (k - 1))
  have hL_nonneg :
      0 ≤ frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) L := by
    unfold frobeniusNorm
    positivity
  have hsqrt_nonneg :
      0 ≤ Real.sqrt (Fintype.card (BipIndex p q)) := Real.sqrt_nonneg _
  have htrace_bound :
      |(Matrix.trace (L * A ^ (k - 1))).re| ≤
        (Real.sqrt (Fintype.card (BipIndex p q)) *
            frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) L) *
          (M / N) ^ (k - 1) := by
    calc
      |(Matrix.trace (L * A ^ (k - 1))).re| ≤
          Real.sqrt (Fintype.card (BipIndex p q)) *
            frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
              (L * A ^ (k - 1)) := by
            simpa [frobeniusNorm] using
              matrix_abs_re_trace_le_sqrt_card_mul_frobenius_norm
                (n := BipIndex p q) (L * A ^ (k - 1))
      _ ≤
          Real.sqrt (Fintype.card (BipIndex p q)) *
            (frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) L *
              opNorm (p := p) (q := q) (A ^ (k - 1))) := by
            exact mul_le_mul_of_nonneg_left
              (lower_frobeniusNorm_mul_le_frobeniusNorm_mul_opNorm
                (p := p) (q := q) L (A ^ (k - 1)))
              (Real.sqrt_nonneg _)
      _ =
          (Real.sqrt (Fintype.card (BipIndex p q)) *
              frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) L) *
            opNorm (p := p) (q := q) (A ^ (k - 1)) := by ring
      _ ≤
          (Real.sqrt (Fintype.card (BipIndex p q)) *
              frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) L) *
            (M / N) ^ (k - 1) := by
            exact mul_le_mul_of_nonneg_left hop
              (mul_nonneg (Real.sqrt_nonneg _) hL_nonneg)
  unfold localWordScaledTraceTerm
  rw [htrace_eq, abs_mul, abs_of_nonneg hNpow]
  have hbound :
      (Real.sqrt (Fintype.card (BipIndex p q)) *
          frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) L) *
        (M / N) ^ (k - 1) ≤
        upperMixedWordAbound M N ^ (k - 1) *
          upperMixedWordL1bound (p := p) (q := q) N M speed a := by
    unfold upperMixedWordAbound upperMixedWordL1bound
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
          frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) L) *
        (M / N) ^ (k - 1) ≤
          (Real.sqrt (Fintype.card (BipIndex p q)) *
              (upperMixedWordL1bound (p := p) (q := q) N M speed a /
                Real.sqrt (Fintype.card (BipIndex p q)))) *
            (M / N) ^ (k - 1) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hL_frob hsqrt_nonneg) hMN_nonneg
      _ = upperMixedWordL1bound (p := p) (q := q) N M speed a * (M / N) ^ (k - 1) := by
          field_simp [hsqrt_pos.ne']
      _ = upperMixedWordAbound M N ^ (k - 1) *
            upperMixedWordL1bound (p := p) (q := q) N M speed a := by
          unfold upperMixedWordAbound
          ring
  calc
    N ^ (k - 1) * |(Matrix.trace (L * A ^ (k - 1))).re| ≤
        N ^ (k - 1) *
          ((Real.sqrt (Fintype.card (BipIndex p q)) *
              frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) L) *
            (M / N) ^ (k - 1)) :=
      mul_le_mul_of_nonneg_left htrace_bound hNpow
    _ ≤ N ^ (k - 1) *
          (upperMixedWordAbound M N ^ (k - 1) *
            upperMixedWordL1bound (p := p) (q := q) N M speed a) := by
          exact mul_le_mul_of_nonneg_left hbound hNpow
    _ = N ^ (k - 1) * upperMixedWordAbound M N ^ (k - 1) *
          upperMixedWordL1bound (p := p) (q := q) N M speed a := by ring

end AppendixB
