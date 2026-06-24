import PptFactorization.AppendixBSpikeLowerBound
import PptFactorization.AristotleTargets.LowerMixedLowerConcreteChoices
import PptFactorization.UpperMixedOneLinearBranch
import PptFactorization.UpperMixedOneQuadraticBranch

/-!
Deterministic upper-bound core lemmas for the multi-defect mixed-word branch.

The proof is casewise on the linear/quadratic letter counts, routing to the
closed many-`Q` lower bound when no linear letters occur, a relabelled many-`Q`
bound when no quadratic letters occur, and a head-`Q` trace peel otherwise.
-/

namespace AppendixB

open PptFactorization.RandomMatrixModel
open PptFactorization.HighProbabilityBounds
open scoped BigOperators Matrix.Norms.Frobenius

variable {p q : Type*}
variable [Fintype p] [Fintype q]
variable [DecidableEq p] [DecidableEq q]
variable [Nonempty p] [Nonempty q]

/-- Canonical Hilbert--Schmidt scale for linear letters at the sharp radius. -/
noncomputable def upperMixedWordL2bound (N M speed a : ℝ) : ℝ :=
  upperMixedWordL1bound (p := p) (q := q) N M speed a

/-- Canonical Hilbert--Schmidt scale for quadratic letters at the sharp radius. -/
noncomputable def upperMixedWordQ2bound (N speed a : ℝ) : ℝ :=
  upperMixedWordQ1bound (p := p) (q := q) N speed a

omit [DecidableEq p] [DecidableEq q] in
theorem upperMixedWordQ1bound_div_sqrt_le_Q2bound (N speed a : ℝ) :
    upperMixedWordQ1bound (p := p) (q := q) N speed a /
      Real.sqrt (Fintype.card (BipIndex p q)) ≤
      upperMixedWordQ2bound (p := p) (q := q) N speed a := by
  dsimp [upperMixedWordQ2bound, upperMixedWordQ1bound]
  have hcardpos : 0 < (Fintype.card (BipIndex p q) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (BipIndex p q))
  have hsqrt_pos : 0 < Real.sqrt (Fintype.card (BipIndex p q)) :=
    Real.sqrt_pos.mpr hcardpos
  calc
    Real.sqrt (Fintype.card (BipIndex p q)) * sharpSphericalRadius N speed a ^ 2 /
        Real.sqrt (Fintype.card (BipIndex p q)) =
        sharpSphericalRadius N speed a ^ 2 := by field_simp [hsqrt_pos.ne']
    _ ≤
        Real.sqrt (Fintype.card (BipIndex p q)) * sharpSphericalRadius N speed a ^ 2 := by
      have hsqrt_one : (1 : ℝ) ≤ Real.sqrt (Fintype.card (BipIndex p q)) := by
        rw [← Real.sqrt_one]
        apply Real.sqrt_le_sqrt
        exact_mod_cast show (1 : ℕ) ≤ Fintype.card (BipIndex p q) from
          Nat.succ_le_of_lt (Fintype.card_pos : 0 < Fintype.card (BipIndex p q))
      nlinarith [sq_nonneg (sharpSphericalRadius N speed a), hsqrt_one]

omit [DecidableEq p] [DecidableEq q] in
theorem frobeniusNorm_Q_le_Q2bound_of_div_sqrt
    (N speed a : ℝ) {Q : BipMatrix p q}
    (hQ_frob :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) Q ≤
        upperMixedWordQ1bound (p := p) (q := q) N speed a /
          Real.sqrt (Fintype.card (BipIndex p q))) :
    frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) Q ≤
      upperMixedWordQ2bound (p := p) (q := q) N speed a :=
  le_trans hQ_frob (upperMixedWordQ1bound_div_sqrt_le_Q2bound N speed a)

/-- Relabel each linear letter as a quadratic letter (same matrix slot in the
`A / 0 / L` product). -/
noncomputable def localWordSwapLToQ {k : ℕ}
    (w : Fin k → LocalExpansionLetter) : Fin k → LocalExpansionLetter :=
  fun i => if w i = LocalExpansionLetter.L then LocalExpansionLetter.Q else w i

omit [Nonempty p] [Nonempty q] in
theorem localWordMatrixProduct_eq_noQ_swapLToQ
    {k : ℕ} {A L Q : BipMatrix p q} {w : Fin k → LocalExpansionLetter}
    (hNoQ : ∀ i : Fin k, w i ≠ LocalExpansionLetter.Q) :
    localWordMatrixProduct (p := p) (q := q) A L Q w =
      localWordMatrixProduct (p := p) (q := q) A 0 L (localWordSwapLToQ w) := by
  induction k generalizing A L Q with
  | zero => simp [localWordMatrixProduct]
  | succ k ih =>
      let wt : Fin k → LocalExpansionLetter := Fin.tail w
      have hNoQ_tail : ∀ i : Fin k, wt i ≠ LocalExpansionLetter.Q := by
        intro i hi
        exact hNoQ i.succ hi
      have iht :=
        ih (A := A) (L := L) (Q := Q) (w := wt) hNoQ_tail
      have hwt : (fun i : Fin k => w i.succ) = wt := rfl
      have hswapwt :
          localWordSwapLToQ wt = fun i : Fin k =>
            if w (Fin.succ i) = LocalExpansionLetter.L then LocalExpansionLetter.Q
            else w (Fin.succ i) := by
        funext i
        simp [localWordSwapLToQ, wt, Fin.tail]
      cases h : w 0 with
      | A =>
          simp [localWordMatrixProduct, localLetterMatrix, localWordSwapLToQ, h, hwt, iht, hswapwt]
      | L =>
          simp [localWordMatrixProduct, localLetterMatrix, localWordSwapLToQ, h, hwt, iht, hswapwt]
      | Q => exact False.elim (hNoQ 0 h)

omit [Nonempty p] [Nonempty q] in
theorem localWordScaledTraceTerm_eq_noQ_swapLToQ
    {N : ℝ} {k : ℕ} {A L Q : BipMatrix p q}
    {w : Fin k → LocalExpansionLetter}
    (hNoQ : ∀ i : Fin k, w i ≠ LocalExpansionLetter.Q) :
    localWordScaledTraceTerm (p := p) (q := q) N A L Q w =
      localWordScaledTraceTerm (p := p) (q := q) N A 0 L (localWordSwapLToQ w) := by
  simp [localWordScaledTraceTerm,
    localWordMatrixProduct_eq_noQ_swapLToQ (p := p) (q := q) (A := A) (L := L) (Q := Q)
      (w := w) hNoQ]

/-- Operator-norm envelope for a general local word. -/
theorem localWordMatrixProduct_opNorm_le_envelope
    {N M a speed : ℝ} {k : ℕ}
    {A L Q : BipMatrix p q} {w : Fin k → LocalExpansionLetter}
    (hM : 0 ≤ M) (hNpos : 0 < N)
    (hA_op : opNorm (p := p) (q := q) A ≤ M / N)
    (hL_frob :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) L ≤
        upperMixedWordL2bound (p := p) (q := q) N M speed a)
    (hQ_frob :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) Q ≤
        upperMixedWordQ1bound (p := p) (q := q) N speed a /
          Real.sqrt (Fintype.card (BipIndex p q))) :
    opNorm (p := p) (q := q)
        (localWordMatrixProduct (p := p) (q := q) A L Q w) ≤
      upperMixedWordAbound M N ^
        localWordLetterCount LocalExpansionLetter.A w *
        upperMixedWordL2bound (p := p) (q := q) N M speed a ^
          localWordLetterCount LocalExpansionLetter.L w *
        upperMixedWordQ2bound (p := p) (q := q) N speed a ^
          localWordLetterCount LocalExpansionLetter.Q w := by
  have hMN : 0 ≤ M / N := div_nonneg hM (le_of_lt hNpos)
  haveI : Nonempty (BipIndex p q) := inferInstance
  have hL2 : 0 ≤ upperMixedWordL2bound (p := p) (q := q) N M speed a := by
    dsimp [upperMixedWordL2bound, upperMixedWordL1bound, sharpSphericalRadius]
    positivity
  have hQ2 : 0 ≤ upperMixedWordQ2bound (p := p) (q := q) N speed a := by
    dsimp [upperMixedWordQ2bound, upperMixedWordQ1bound, sharpSphericalRadius]
    positivity
  have hL_op :
      opNorm (p := p) (q := q) L ≤
        upperMixedWordL2bound (p := p) (q := q) N M speed a :=
    le_trans (opNorm_le_frobeniusNorm (p := p) (q := q) L) hL_frob
  have hQ_op :
      opNorm (p := p) (q := q) Q ≤
        upperMixedWordQ2bound (p := p) (q := q) N speed a :=
    le_trans (opNorm_le_frobeniusNorm (p := p) (q := q) Q)
      (frobeniusNorm_Q_le_Q2bound_of_div_sqrt N speed a hQ_frob)
  induction k with
  | zero =>
      simp [localWordMatrixProduct, localWordLetterCount, upperMixedWordAbound]
  | succ k ih =>
      let wt : Fin k → LocalExpansionLetter := Fin.tail w
      have iht := ih (w := wt)
      have hcountA :
          localWordLetterCount LocalExpansionLetter.A w =
            (if w 0 = LocalExpansionLetter.A then 1 else 0) +
              localWordLetterCount LocalExpansionLetter.A wt := by
        simpa [wt, Fin.cons_self_tail] using
          localWordLetterCount_cons (k := k) LocalExpansionLetter.A (w 0) wt
      have hcountL :
          localWordLetterCount LocalExpansionLetter.L w =
            (if w 0 = LocalExpansionLetter.L then 1 else 0) +
              localWordLetterCount LocalExpansionLetter.L wt := by
        simpa [wt, Fin.cons_self_tail] using
          localWordLetterCount_cons (k := k) LocalExpansionLetter.L (w 0) wt
      have hcountQ :
          localWordLetterCount LocalExpansionLetter.Q w =
            (if w 0 = LocalExpansionLetter.Q then 1 else 0) +
              localWordLetterCount LocalExpansionLetter.Q wt := by
        simpa [wt, Fin.cons_self_tail] using
          localWordLetterCount_cons (k := k) LocalExpansionLetter.Q (w 0) wt
      have htail_nonneg :
          0 ≤ opNorm (p := p) (q := q)
              (localWordMatrixProduct (p := p) (q := q) A L Q wt) := by
        unfold opNorm
        positivity
      have htail_bound_nonneg :
          0 ≤
            upperMixedWordAbound M N ^
                localWordLetterCount LocalExpansionLetter.A wt *
              upperMixedWordL2bound (p := p) (q := q) N M speed a ^
                localWordLetterCount LocalExpansionLetter.L wt *
              upperMixedWordQ2bound (p := p) (q := q) N speed a ^
                localWordLetterCount LocalExpansionLetter.Q wt := by
        positivity
      cases h : w 0 with
      | A =>
          have hmul :=
            lower_opNorm_mul_le (p := p) (q := q) A
              (localWordMatrixProduct (p := p) (q := q) A L Q wt)
          calc
            opNorm (p := p) (q := q)
                (localWordMatrixProduct (p := p) (q := q) A L Q w) ≤
              opNorm (p := p) (q := q) A *
                opNorm (p := p) (q := q)
                  (localWordMatrixProduct (p := p) (q := q) A L Q wt) := by
                have hwt : (fun i : Fin k => w i.succ) = wt := rfl
                simpa [localWordMatrixProduct, localLetterMatrix, h, hwt, opNorm, map_mul] using hmul
            _ ≤
                (M / N) *
                  (upperMixedWordAbound M N ^
                      localWordLetterCount LocalExpansionLetter.A wt *
                    upperMixedWordL2bound (p := p) (q := q) N M speed a ^
                      localWordLetterCount LocalExpansionLetter.L wt *
                    upperMixedWordQ2bound (p := p) (q := q) N speed a ^
                      localWordLetterCount LocalExpansionLetter.Q wt) := by
                exact mul_le_mul hA_op iht htail_nonneg hMN
            _ =
                upperMixedWordAbound M N ^
                    localWordLetterCount LocalExpansionLetter.A w *
                  upperMixedWordL2bound (p := p) (q := q) N M speed a ^
                    localWordLetterCount LocalExpansionLetter.L w *
                  upperMixedWordQ2bound (p := p) (q := q) N speed a ^
                    localWordLetterCount LocalExpansionLetter.Q w := by
              rw [hcountA, hcountL, hcountQ]
              simp [h, upperMixedWordAbound]
              ring
      | L =>
          have hmul :=
            lower_opNorm_mul_le (p := p) (q := q) L
              (localWordMatrixProduct (p := p) (q := q) A L Q wt)
          calc
            opNorm (p := p) (q := q)
                (localWordMatrixProduct (p := p) (q := q) A L Q w) ≤
              opNorm (p := p) (q := q) L *
                opNorm (p := p) (q := q)
                  (localWordMatrixProduct (p := p) (q := q) A L Q wt) := by
                have hwt : (fun i : Fin k => w i.succ) = wt := rfl
                simpa [localWordMatrixProduct, localLetterMatrix, h, hwt, opNorm, map_mul] using hmul
            _ ≤
                upperMixedWordL2bound (p := p) (q := q) N M speed a *
                  (upperMixedWordAbound M N ^
                      localWordLetterCount LocalExpansionLetter.A wt *
                    upperMixedWordL2bound (p := p) (q := q) N M speed a ^
                      localWordLetterCount LocalExpansionLetter.L wt *
                    upperMixedWordQ2bound (p := p) (q := q) N speed a ^
                      localWordLetterCount LocalExpansionLetter.Q wt) := by
                exact mul_le_mul hL_op iht htail_nonneg hL2
            _ =
                upperMixedWordAbound M N ^
                    localWordLetterCount LocalExpansionLetter.A w *
                  upperMixedWordL2bound (p := p) (q := q) N M speed a ^
                    localWordLetterCount LocalExpansionLetter.L w *
                  upperMixedWordQ2bound (p := p) (q := q) N speed a ^
                    localWordLetterCount LocalExpansionLetter.Q w := by
              rw [hcountA, hcountL, hcountQ]
              simp [h, upperMixedWordAbound]
              ring
      | Q =>
          have hmul :=
            lower_opNorm_mul_le (p := p) (q := q) Q
              (localWordMatrixProduct (p := p) (q := q) A L Q wt)
          calc
            opNorm (p := p) (q := q)
                (localWordMatrixProduct (p := p) (q := q) A L Q w) ≤
              opNorm (p := p) (q := q) Q *
                opNorm (p := p) (q := q)
                  (localWordMatrixProduct (p := p) (q := q) A L Q wt) := by
                have hwt : (fun i : Fin k => w i.succ) = wt := rfl
                simpa [localWordMatrixProduct, localLetterMatrix, h, hwt, opNorm, map_mul] using hmul
            _ ≤
                upperMixedWordQ2bound (p := p) (q := q) N speed a *
                  (upperMixedWordAbound M N ^
                      localWordLetterCount LocalExpansionLetter.A wt *
                    upperMixedWordL2bound (p := p) (q := q) N M speed a ^
                      localWordLetterCount LocalExpansionLetter.L wt *
                    upperMixedWordQ2bound (p := p) (q := q) N speed a ^
                      localWordLetterCount LocalExpansionLetter.Q wt) := by
                exact mul_le_mul hQ_op iht htail_nonneg hQ2
            _ =
                upperMixedWordAbound M N ^
                    localWordLetterCount LocalExpansionLetter.A w *
                  upperMixedWordL2bound (p := p) (q := q) N M speed a ^
                    localWordLetterCount LocalExpansionLetter.L w *
                  upperMixedWordQ2bound (p := p) (q := q) N speed a ^
                    localWordLetterCount LocalExpansionLetter.Q w := by
              rw [hcountA, hcountL, hcountQ]
              simp [h, upperMixedWordAbound]
              ring

omit [Nonempty p] [Nonempty q] in
/-- Multi-defect mixed-word bound when no linear letter occurs. -/
theorem localWordScaledTraceTerm_multiDefect_manyQ_noL
    {N M a speed : ℝ} {k : ℕ}
    {A L Q : BipMatrix p q} {w : Fin k → LocalExpansionLetter}
    (Sbound : ℝ)
    (hNpos : 0 < N) (hM : 0 ≤ M) (hSbound : 0 ≤ Sbound)
    (hA_op : opNorm (p := p) (q := q) A ≤ M / N)
    (hQ_frob :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) Q ≤ Sbound)
    (hNoL : ∀ i : Fin k, w i ≠ LocalExpansionLetter.L)
    (hQtwo : 2 ≤ localWordLetterCount LocalExpansionLetter.Q w) :
    |localWordScaledTraceTerm (p := p) (q := q) N A L Q w| ≤
      N ^ (k - 1) *
        upperMixedWordAbound M N ^
          localWordLetterCount LocalExpansionLetter.A w *
        upperMixedWordL2bound (p := p) (q := q) N M speed a ^
          localWordLetterCount LocalExpansionLetter.L w *
        Sbound ^
          localWordLetterCount LocalExpansionLetter.Q w := by
  have hL0 : localWordLetterCount LocalExpansionLetter.L w = 0 :=
    lower_localWordLetterCount_zero_of_forall_ne hNoL
  have hk1 : 1 ≤ k := by
    have htotal := localWordLetterCount_total w
    omega
  have hkpred : (k - 1) + 1 = k := by omega
  have hNoL_cast :
      ∀ i : Fin ((k - 1) + 1), (w ∘ Fin.cast hkpred) i ≠ LocalExpansionLetter.L := by
    intro i hi
    exact hNoL (Fin.cast hkpred i) hi
  have hQtwo_cast :
      2 ≤ localWordLetterCount LocalExpansionLetter.Q (w ∘ Fin.cast hkpred) := by
    simpa [lower_localWordLetterCount_cast, hkpred] using hQtwo
  have hSbound_nonneg : 0 ≤ Sbound := hSbound
  have hQ_op :
      opNorm (p := p) (q := q) Q ≤ Sbound :=
    le_trans (opNorm_le_frobeniusNorm (p := p) (q := q) Q) hQ_frob
  have hMany_raw :=
    lower_localWordScaledTraceTerm_manyQ_noL_bound
      (p := p) (q := q) (N := N) (M := M) (Sbound := Sbound)
      (m := k - 1) (A := A) (Q := Q) (w := w ∘ Fin.cast hkpred)
      (le_of_lt hNpos) (div_nonneg hM (le_of_lt hNpos)) hSbound_nonneg
      hA_op hQ_op hQ_frob hNoL_cast hQtwo_cast
  rw [lower_localWordScaledTraceTerm_cast
      (p := p) (q := q) (N := N) (A := A) (L := 0) (Q := Q) (h := hkpred) (w := w)] at hMany_raw
  have hMany :
      |localWordScaledTraceTerm (p := p) (q := q) N A 0 Q w| ≤
        N ^ (k - 1) *
          ((M / N) ^ localWordLetterCount LocalExpansionLetter.A w *
            Sbound ^ localWordLetterCount LocalExpansionLetter.Q w) := by
    simpa [lower_localWordLetterCount_cast, hkpred] using hMany_raw
  rw [localWordScaledTraceTerm_eq_of_noLinear
      (p := p) (q := q) (N := N) (A := A) (L := L) (Q := Q) (w := w) hNoL]
  simp only [upperMixedWordAbound, upperMixedWordL2bound, hL0, pow_zero, mul_one, mul_assoc]
  exact hMany

/-- Mixed words with both letter types: peel the head `Q` and bound the tail in
operator norm. -/
theorem localWordScaledTraceTerm_posL_posQ_le_envelope
    {N M a speed : ℝ} {k : ℕ}
    {A L Q : BipMatrix p q} {w : Fin k → LocalExpansionLetter}
    (hNpos : 0 < N) (hM : 0 ≤ M)
    (hA_op : opNorm (p := p) (q := q) A ≤ M / N)
    (hL_frob :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) L ≤
        upperMixedWordL2bound (p := p) (q := q) N M speed a)
    (hQ_frob :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) Q ≤
        upperMixedWordQ1bound (p := p) (q := q) N speed a /
          Real.sqrt (Fintype.card (BipIndex p q)))
    (hLpos : 0 < localWordLetterCount LocalExpansionLetter.L w)
    (hQpos : 0 < localWordLetterCount LocalExpansionLetter.Q w) :
    |localWordScaledTraceTerm (p := p) (q := q) N A L Q w| ≤
      N ^ (k - 1) *
        upperMixedWordAbound M N ^
          localWordLetterCount LocalExpansionLetter.A w *
        upperMixedWordL2bound (p := p) (q := q) N M speed a ^
          localWordLetterCount LocalExpansionLetter.L w *
        upperMixedWordQ2bound (p := p) (q := q) N speed a ^
          localWordLetterCount LocalExpansionLetter.Q w := by
  obtain ⟨iQ, hiQ⟩ :=
    lower_localWord_exists_of_letterCount_pos
      (letter := LocalExpansionLetter.Q) (w := w) hQpos
  have hk1 : 1 ≤ k := by
    have htotal := localWordLetterCount_total w
    omega
  have hkpred : (k - 1) + 1 = k := by omega
  let wcast := w ∘ Fin.cast hkpred
  let iQcast := Fin.cast hkpred.symm iQ
  have hiQcast : wcast iQcast = LocalExpansionLetter.Q := by
    simp [wcast, iQcast, hiQ]
  rcases lower_localWord_exists_cyclicPrefixSplitAt wcast iQcast with
    ⟨r, n, hlen, u, v, hwcast⟩
  let vQ : Fin (n + 1) → LocalExpansionLetter :=
    Fin.cons LocalExpansionLetter.Q v
  have hw :
      wcast =
        (Fin.append u vQ ∘ Fin.cast hlen.symm) := by
    rw [hwcast]
    simp [vQ, iQcast, hiQcast]
  have hterm_rot :
      localWordScaledTraceTerm (p := p) (q := q) N A L Q w =
        localWordScaledTraceTerm (p := p) (q := q) N A L Q
          (Fin.append vQ u) := by
    calc
      localWordScaledTraceTerm (p := p) (q := q) N A L Q w =
          localWordScaledTraceTerm (p := p) (q := q) N A L Q wcast := by
            rw [lower_localWordScaledTraceTerm_cast
              (p := p) (q := q) (N := N) (A := A) (L := L) (Q := Q)
              (h := hkpred) (w := w)]
      _ = localWordScaledTraceTerm (p := p) (q := q) N A L Q
            (Fin.append u vQ ∘ Fin.cast hlen.symm) := by
            rw [hw]
      _ = localWordScaledTraceTerm (p := p) (q := q) N A L Q
            (Fin.append u vQ) := by
            simpa using
              lower_localWordScaledTraceTerm_cast
                (p := p) (q := q) (N := N) (A := A) (L := L) (Q := Q)
                (h := hlen.symm) (w := Fin.append u vQ)
      _ = localWordScaledTraceTerm (p := p) (q := q) N A L Q
            (Fin.append vQ u ∘ Fin.cast (Nat.add_comm r (n + 1))) := by
            rw [lower_localWordScaledTraceTerm_append_rotate
              (p := p) (q := q) (N := N) (A := A) (L := L) (Q := Q) u vQ]
      _ = localWordScaledTraceTerm (p := p) (q := q) N A L Q
            (Fin.append vQ u) := by
            rw [← lower_localWordScaledTraceTerm_cast
              (p := p) (q := q) (N := N) (A := A) (L := L) (Q := Q)
              (h := Nat.add_comm r (n + 1)) (w := Fin.append vQ u)]
  let wHead : Fin (n + 1 + r) → LocalExpansionLetter := Fin.append vQ u
  have hsucc : Nat.succ (n + r) = n + 1 + r := by
    simp [Nat.succ_add]
  let wHeadSucc : Fin (Nat.succ (n + r)) → LocalExpansionLetter :=
    wHead ∘ Fin.cast hsucc
  have h0cast :
      Fin.cast hsucc (0 : Fin (Nat.succ (n + r))) = (0 : Fin (n + 1 + r)) := by
    ext
    simp [Nat.succ_add]
  have hHeadw : wHead 0 = LocalExpansionLetter.Q :=
    Fin.append_left (u := vQ) (v := u) (0 : Fin (n + 1))
  have hHeadQ : wHeadSucc 0 = LocalExpansionLetter.Q := by
    simp [wHeadSucc, Function.comp_apply, h0cast, hHeadw]
  let wt : Fin (n + r) → LocalExpansionLetter := Fin.tail wHeadSucc
  have hcons : wHeadSucc = Fin.cons LocalExpansionLetter.Q wt := by
    rw [← Fin.cons_self_tail wHeadSucc]
    simp [wt, hHeadQ]
  have hmatHead :
      localWordMatrixProduct (p := p) (q := q) A L Q wHeadSucc =
        localWordMatrixProduct (p := p) (q := q) A L Q wHead := by
    dsimp [wHeadSucc]
    exact lower_localWordMatrixProduct_cast (p := p) (q := q) (A := A) (L := L) (Q := Q)
      (h := hsucc) (w := wHead)
  have hwHeadSucc :
      localWordScaledTraceTerm (p := p) (q := q) N A L Q wHeadSucc =
        localWordScaledTraceTerm (p := p) (q := q) N A L Q wHead := by
    dsimp [wHeadSucc]
    exact lower_localWordScaledTraceTerm_cast (p := p) (q := q) (N := N) (A := A) (L := L) (Q := Q)
      (h := hsucc) (w := wHead)
  have hprod :
      localWordMatrixProduct (p := p) (q := q) A L Q wHeadSucc =
        Q * localWordMatrixProduct (p := p) (q := q) A L Q wt := by
    rw [hcons]
    change localWordMatrixProduct _ _ _ (Fin.cons LocalExpansionLetter.Q wt) = _
    simp [localWordMatrixProduct, localLetterMatrix, Fin.cons_zero]
  have hN : 0 ≤ N := le_of_lt hNpos
  have hNpow : 0 ≤ N ^ (k - 1) := pow_nonneg hN _
  have hQ2 : 0 ≤ upperMixedWordQ2bound (p := p) (q := q) N speed a := by
    dsimp [upperMixedWordQ2bound, upperMixedWordQ1bound]
    positivity
  have hop_tail :=
    localWordMatrixProduct_opNorm_le_envelope
      (N := N) (M := M) (a := a) (speed := speed)
      (A := A) (L := L) (Q := Q) (w := wt) hM hNpos hA_op hL_frob hQ_frob
  have hcountA :
      localWordLetterCount LocalExpansionLetter.A w =
        localWordLetterCount LocalExpansionLetter.A wt := by
    have hcountHead :
        localWordLetterCount LocalExpansionLetter.A wHeadSucc =
          localWordLetterCount LocalExpansionLetter.A wt := by
      rw [hcons, localWordLetterCount_cons]
      simp
    have hcountW :
        localWordLetterCount LocalExpansionLetter.A w =
          localWordLetterCount LocalExpansionLetter.A wHead := by
      calc
        localWordLetterCount LocalExpansionLetter.A w =
            localWordLetterCount LocalExpansionLetter.A wcast := by
              rw [← lower_localWordLetterCount_cast (h := hkpred)]
        _ = localWordLetterCount LocalExpansionLetter.A
              (Fin.append u vQ ∘ Fin.cast hlen.symm) := by rw [hw]
        _ = localWordLetterCount LocalExpansionLetter.A (Fin.append u vQ) := by
            rw [lower_localWordLetterCount_cast (h := hlen.symm)]
        _ = localWordLetterCount LocalExpansionLetter.A (Fin.append vQ u) := by
            rw [lower_localWordLetterCount_append, lower_localWordLetterCount_append]
            ac_rfl
        _ = localWordLetterCount LocalExpansionLetter.A wHead := rfl
    have hcountSucc :
        localWordLetterCount LocalExpansionLetter.A wHead =
          localWordLetterCount LocalExpansionLetter.A wHeadSucc := by
      unfold wHeadSucc
      rw [lower_localWordLetterCount_cast (h := hsucc) (w := wHead)]
    exact hcountW.trans (hcountSucc.trans hcountHead)
  have hcountL :
      localWordLetterCount LocalExpansionLetter.L w =
        localWordLetterCount LocalExpansionLetter.L wt := by
    have hcountHead :
        localWordLetterCount LocalExpansionLetter.L wHeadSucc =
          localWordLetterCount LocalExpansionLetter.L wt := by
      rw [hcons, localWordLetterCount_cons]
      simp
    have hcountW :
        localWordLetterCount LocalExpansionLetter.L w =
          localWordLetterCount LocalExpansionLetter.L wHead := by
      calc
        localWordLetterCount LocalExpansionLetter.L w =
            localWordLetterCount LocalExpansionLetter.L wcast := by
              rw [← lower_localWordLetterCount_cast (h := hkpred)]
        _ = localWordLetterCount LocalExpansionLetter.L
              (Fin.append u vQ ∘ Fin.cast hlen.symm) := by rw [hw]
        _ = localWordLetterCount LocalExpansionLetter.L (Fin.append u vQ) := by
            rw [lower_localWordLetterCount_cast (h := hlen.symm)]
        _ = localWordLetterCount LocalExpansionLetter.L (Fin.append vQ u) := by
            rw [lower_localWordLetterCount_append, lower_localWordLetterCount_append]
            ac_rfl
        _ = localWordLetterCount LocalExpansionLetter.L wHead := rfl
    have hcountSucc :
        localWordLetterCount LocalExpansionLetter.L wHead =
          localWordLetterCount LocalExpansionLetter.L wHeadSucc := by
      unfold wHeadSucc
      rw [lower_localWordLetterCount_cast (h := hsucc) (w := wHead)]
    exact hcountW.trans (hcountSucc.trans hcountHead)
  have hcountQ :
      localWordLetterCount LocalExpansionLetter.Q w =
        1 + localWordLetterCount LocalExpansionLetter.Q wt := by
    have hcountHead :
        localWordLetterCount LocalExpansionLetter.Q wHeadSucc =
          1 + localWordLetterCount LocalExpansionLetter.Q wt := by
      rw [hcons, localWordLetterCount_cons]
      simp
    have hcountW :
        localWordLetterCount LocalExpansionLetter.Q w =
          localWordLetterCount LocalExpansionLetter.Q wHead := by
      calc
        localWordLetterCount LocalExpansionLetter.Q w =
            localWordLetterCount LocalExpansionLetter.Q wcast := by
              rw [← lower_localWordLetterCount_cast (h := hkpred)]
        _ = localWordLetterCount LocalExpansionLetter.Q
              (Fin.append u vQ ∘ Fin.cast hlen.symm) := by rw [hw]
        _ = localWordLetterCount LocalExpansionLetter.Q (Fin.append u vQ) := by
            rw [lower_localWordLetterCount_cast (h := hlen.symm)]
        _ = localWordLetterCount LocalExpansionLetter.Q (Fin.append vQ u) := by
            rw [lower_localWordLetterCount_append, lower_localWordLetterCount_append]
            ac_rfl
        _ = localWordLetterCount LocalExpansionLetter.Q wHead := rfl
    have hcountSucc :
        localWordLetterCount LocalExpansionLetter.Q wHead =
          localWordLetterCount LocalExpansionLetter.Q wHeadSucc := by
      unfold wHeadSucc
      rw [lower_localWordLetterCount_cast (h := hsucc) (w := wHead)]
    rw [hcountW, hcountSucc, hcountHead]
  have htrace_bound :
      |(Matrix.trace
          (localWordMatrixProduct (p := p) (q := q) A L Q wHeadSucc)).re| ≤
        upperMixedWordQ2bound (p := p) (q := q) N speed a *
          (upperMixedWordAbound M N ^
              localWordLetterCount LocalExpansionLetter.A wt *
            upperMixedWordL2bound (p := p) (q := q) N M speed a ^
              localWordLetterCount LocalExpansionLetter.L wt *
            upperMixedWordQ2bound (p := p) (q := q) N speed a ^
              localWordLetterCount LocalExpansionLetter.Q wt) := by
    have htrace_sqrt :=
      matrix_abs_re_trace_le_sqrt_card_mul_frobenius_norm
        (n := BipIndex p q)
        (Q * localWordMatrixProduct (p := p) (q := q) A L Q wt)
    have hfrob_mul :=
      lower_frobeniusNorm_mul_le_frobeniusNorm_mul_opNorm
        (p := p) (q := q) Q
        (localWordMatrixProduct (p := p) (q := q) A L Q wt)
    have hsqrt_nonneg :
        0 ≤ Real.sqrt (Fintype.card (BipIndex p q)) := Real.sqrt_nonneg _
    have hop_nonneg :
        0 ≤ opNorm (p := p) (q := q)
          (localWordMatrixProduct (p := p) (q := q) A L Q wt) := by
      unfold opNorm
      positivity
    calc
      |(Matrix.trace
          (localWordMatrixProduct (p := p) (q := q) A L Q wHeadSucc)).re| =
          |(Matrix.trace
              (Q *
                localWordMatrixProduct (p := p) (q := q) A L Q wt)).re| := by
            rw [hprod]
      _ ≤
          Real.sqrt (Fintype.card (BipIndex p q)) *
            frobeniusNorm (p := p) (q := q) (σ := BipIndex p q)
              (Q *
                localWordMatrixProduct (p := p) (q := q) A L Q wt) := by
            simpa [frobeniusNorm] using htrace_sqrt
      _ ≤
          Real.sqrt (Fintype.card (BipIndex p q)) *
            (frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) Q *
              opNorm (p := p) (q := q)
                (localWordMatrixProduct (p := p) (q := q) A L Q wt)) := by
            exact mul_le_mul_of_nonneg_left hfrob_mul hsqrt_nonneg
      _ ≤
          upperMixedWordQ2bound (p := p) (q := q) N speed a *
            opNorm (p := p) (q := q)
              (localWordMatrixProduct (p := p) (q := q) A L Q wt) := by
            haveI : Nonempty (BipIndex p q) := inferInstance
            have hcardpos : 0 < (Fintype.card (BipIndex p q) : ℝ) := by
              exact_mod_cast Fintype.card_pos
            have hsqrt_pos :
                0 < Real.sqrt (Fintype.card (BipIndex p q)) :=
              Real.sqrt_pos.mpr hcardpos
            have hsqrt_nonneg :
                0 ≤ Real.sqrt (Fintype.card (BipIndex p q)) := Real.sqrt_nonneg _
            calc
              Real.sqrt (Fintype.card (BipIndex p q)) *
                  (frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) Q *
                    opNorm (p := p) (q := q)
                      (localWordMatrixProduct (p := p) (q := q) A L Q wt)) =
                  (Real.sqrt (Fintype.card (BipIndex p q)) *
                      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) Q) *
                    opNorm (p := p) (q := q)
                      (localWordMatrixProduct (p := p) (q := q) A L Q wt) := by ring
              _ ≤
                  (Real.sqrt (Fintype.card (BipIndex p q)) *
                      (upperMixedWordQ1bound (p := p) (q := q) N speed a /
                        Real.sqrt (Fintype.card (BipIndex p q)))) *
                    opNorm (p := p) (q := q)
                      (localWordMatrixProduct (p := p) (q := q) A L Q wt) := by
                    exact mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_left hQ_frob hsqrt_nonneg) hop_nonneg
              _ =
                  upperMixedWordQ2bound (p := p) (q := q) N speed a *
                    opNorm (p := p) (q := q)
                      (localWordMatrixProduct (p := p) (q := q) A L Q wt) := by
                    dsimp [upperMixedWordQ2bound, upperMixedWordQ1bound]
                    field_simp [hsqrt_pos.ne']
      _ ≤
          upperMixedWordQ2bound (p := p) (q := q) N speed a *
            (upperMixedWordAbound M N ^
                localWordLetterCount LocalExpansionLetter.A wt *
              upperMixedWordL2bound (p := p) (q := q) N M speed a ^
                localWordLetterCount LocalExpansionLetter.L wt *
              upperMixedWordQ2bound (p := p) (q := q) N speed a ^
                localWordLetterCount LocalExpansionLetter.Q wt) := by
            exact mul_le_mul_of_nonneg_left hop_tail hQ2
  have hpow : k - 1 = n + r := by omega
  have hNnr : 0 ≤ N ^ (n + r) := pow_nonneg hN _
  rw [hterm_rot, hwHeadSucc.symm]
  unfold localWordScaledTraceTerm
  rw [Nat.succ_sub_one (n + r), abs_mul, abs_of_nonneg hNnr]
  calc
    N ^ (n + r) *
        |(Matrix.trace
          (localWordMatrixProduct (p := p) (q := q) A L Q wHeadSucc)).re| ≤
        N ^ (n + r) *
          (upperMixedWordQ2bound (p := p) (q := q) N speed a *
            (upperMixedWordAbound M N ^
                localWordLetterCount LocalExpansionLetter.A wt *
              upperMixedWordL2bound (p := p) (q := q) N M speed a ^
                localWordLetterCount LocalExpansionLetter.L wt *
              upperMixedWordQ2bound (p := p) (q := q) N speed a ^
                localWordLetterCount LocalExpansionLetter.Q wt)) :=
      mul_le_mul_of_nonneg_left htrace_bound hNnr
    _ ≤
        N ^ (k - 1) *
          upperMixedWordAbound M N ^
            localWordLetterCount LocalExpansionLetter.A w *
          upperMixedWordL2bound (p := p) (q := q) N M speed a ^
            localWordLetterCount LocalExpansionLetter.L w *
          upperMixedWordQ2bound (p := p) (q := q) N speed a ^
            localWordLetterCount LocalExpansionLetter.Q w := by
          have hstep :
              N ^ (n + r) *
                  (upperMixedWordQ2bound (p := p) (q := q) N speed a *
                    (upperMixedWordAbound M N ^
                        localWordLetterCount LocalExpansionLetter.A wt *
                      upperMixedWordL2bound (p := p) (q := q) N M speed a ^
                        localWordLetterCount LocalExpansionLetter.L wt *
                      upperMixedWordQ2bound (p := p) (q := q) N speed a ^
                        localWordLetterCount LocalExpansionLetter.Q wt)) ≤
                N ^ (k - 1) *
                  upperMixedWordAbound M N ^
                    localWordLetterCount LocalExpansionLetter.A w *
                  upperMixedWordL2bound (p := p) (q := q) N M speed a ^
                    localWordLetterCount LocalExpansionLetter.L w *
                  upperMixedWordQ2bound (p := p) (q := q) N speed a ^
                    localWordLetterCount LocalExpansionLetter.Q w := by
            have hbound_eq :
                N ^ (n + r) *
                    (upperMixedWordQ2bound (p := p) (q := q) N speed a *
                      (upperMixedWordAbound M N ^
                          localWordLetterCount LocalExpansionLetter.A wt *
                        upperMixedWordL2bound (p := p) (q := q) N M speed a ^
                          localWordLetterCount LocalExpansionLetter.L wt *
                        upperMixedWordQ2bound (p := p) (q := q) N speed a ^
                          localWordLetterCount LocalExpansionLetter.Q wt)) =
                  N ^ (k - 1) *
                    upperMixedWordAbound M N ^
                      localWordLetterCount LocalExpansionLetter.A w *
                    upperMixedWordL2bound (p := p) (q := q) N M speed a ^
                      localWordLetterCount LocalExpansionLetter.L w *
                    upperMixedWordQ2bound (p := p) (q := q) N speed a ^
                      localWordLetterCount LocalExpansionLetter.Q w := by
              rw [hpow, hcountA, hcountL, hcountQ, upperMixedWordAbound]
              ring
            exact le_of_eq hbound_eq
          exact hstep

theorem localWordScaledTraceTerm_multiDefect_le_envelope
    {N M a speed : ℝ} {k : ℕ}
    {A L Q : BipMatrix p q} {w : Fin k → LocalExpansionLetter}
    (hNpos : 0 < N) (hM : 0 ≤ M) (_ha : 0 ≤ a)
    (hA_op : opNorm (p := p) (q := q) A ≤ M / N)
    (hL_frob :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) L ≤
        upperMixedWordL2bound (p := p) (q := q) N M speed a)
    (hQ_frob :
      frobeniusNorm (p := p) (q := q) (σ := BipIndex p q) Q ≤
        upperMixedWordQ1bound (p := p) (q := q) N speed a /
          Real.sqrt (Fintype.card (BipIndex p q)))
    (hmix : localWordIsMixed w)
    (hNotOneL : ¬ localWordHasOneLinearDefect w)
    (hNotOneQ : ¬ localWordHasOneQuadraticDefect w) :
    |localWordScaledTraceTerm (p := p) (q := q) N A L Q w| ≤
      N ^ (k - 1) *
        upperMixedWordAbound M N ^
          localWordLetterCount LocalExpansionLetter.A w *
        upperMixedWordL2bound (p := p) (q := q) N M speed a ^
          localWordLetterCount LocalExpansionLetter.L w *
        upperMixedWordQ2bound (p := p) (q := q) N speed a ^
          localWordLetterCount LocalExpansionLetter.Q w := by
  by_cases hL0 : localWordLetterCount LocalExpansionLetter.L w = 0
  · have hNoL : ∀ i : Fin k, w i ≠ LocalExpansionLetter.L :=
      lower_localWord_no_letter_of_count_zero hL0
    have hQtwo : 2 ≤ localWordLetterCount LocalExpansionLetter.Q w := by
      by_cases hQ1 : localWordLetterCount LocalExpansionLetter.Q w = 1
      · exact False.elim (hNotOneQ ⟨hL0, hQ1⟩)
      · have hQpos :=
          lower_localWord_mixed_noL_Q_count_pos hmix hNoL
        omega
    exact
      localWordScaledTraceTerm_multiDefect_manyQ_noL
        (Sbound := upperMixedWordQ2bound (p := p) (q := q) N speed a)
        (N := N) (M := M) (a := a) (speed := speed) (k := k)
        (A := A) (L := L) (Q := Q) (w := w) hNpos hM
        (by dsimp [upperMixedWordQ2bound, upperMixedWordQ1bound, sharpSphericalRadius]; positivity)
        hA_op
        (frobeniusNorm_Q_le_Q2bound_of_div_sqrt N speed a hQ_frob)
        hNoL hQtwo
  · by_cases hQ0 : localWordLetterCount LocalExpansionLetter.Q w = 0
    · have hNoQ : ∀ i : Fin k, w i ≠ LocalExpansionLetter.Q :=
        lower_localWord_no_letter_of_count_zero hQ0
      have hLtwo : 2 ≤ localWordLetterCount LocalExpansionLetter.L w := by
        by_cases hL1 : localWordLetterCount LocalExpansionLetter.L w = 1
        · exact False.elim (hNotOneL ⟨hL1, hQ0⟩)
        · omega
      have hL2 :
          0 ≤ upperMixedWordL2bound (p := p) (q := q) N M speed a := by
        dsimp [upperMixedWordL2bound, upperMixedWordL1bound, sharpSphericalRadius]
        positivity
      have hswap :=
        localWordScaledTraceTerm_multiDefect_manyQ_noL
          (Sbound := upperMixedWordL2bound (p := p) (q := q) N M speed a)
          (N := N) (M := M) (a := a) (speed := speed) (k := k)
          (A := A) (L := L) (Q := L) (w := localWordSwapLToQ w)
          hNpos hM hL2 hA_op hL_frob
          (by
            intro i hi
            cases hwi : w i with
            | A => simp [localWordSwapLToQ, hwi] at hi
            | L => simp [localWordSwapLToQ, hwi] at hi
            | Q => exact False.elim (hNoQ i hwi))
          (by
            have hcount :
                localWordLetterCount LocalExpansionLetter.Q (localWordSwapLToQ w) =
                  localWordLetterCount LocalExpansionLetter.L w := by
              unfold localWordSwapLToQ localWordLetterCount
              simp [hNoQ]
            rw [hcount]
            exact hLtwo)
      have hNoLswap : ∀ i : Fin k, (localWordSwapLToQ w) i ≠ LocalExpansionLetter.L := by
        intro i
        cases hwi : w i with
        | A => simp [localWordSwapLToQ, hwi]
        | L => simp [localWordSwapLToQ, hwi]
        | Q => simp [localWordSwapLToQ, hwi]
      have hQcount_swap :
          localWordLetterCount LocalExpansionLetter.Q (localWordSwapLToQ w) =
            localWordLetterCount LocalExpansionLetter.L w := by
        unfold localWordSwapLToQ localWordLetterCount
        simp [hNoQ]
      have hAcount_swap :
          localWordLetterCount LocalExpansionLetter.A (localWordSwapLToQ w) =
            localWordLetterCount LocalExpansionLetter.A w := by
        have hLswap0 :
            localWordLetterCount LocalExpansionLetter.L (localWordSwapLToQ w) = 0 := by
          apply lower_localWordLetterCount_zero_of_forall_ne
          intro i hi
          cases hwi : w i with
          | A => simp [localWordSwapLToQ, hwi] at hi
          | L => simp [localWordSwapLToQ, hwi] at hi
          | Q => exact False.elim (hNoQ i hwi)
        have htot := localWordLetterCount_total w
        have htot' := localWordLetterCount_total (localWordSwapLToQ w)
        rw [hQcount_swap, hLswap0] at htot'
        rw [hQ0] at htot
        omega
      have hLcount_swap :
          localWordLetterCount LocalExpansionLetter.L (localWordSwapLToQ w) = 0 := by
        apply lower_localWordLetterCount_zero_of_forall_ne
        intro i hi
        cases hwi : w i with
        | A => simp [localWordSwapLToQ, hwi] at hi
        | L => simp [localWordSwapLToQ, hwi] at hi
        | Q => exact False.elim (hNoQ i hwi)
      calc
        |localWordScaledTraceTerm (p := p) (q := q) N A L Q w| =
            |localWordScaledTraceTerm (p := p) (q := q) N A 0 L (localWordSwapLToQ w)| := by
              rw [localWordScaledTraceTerm_eq_noQ_swapLToQ
                (p := p) (q := q) (N := N) (A := A) (L := L) (Q := Q) (w := w) hNoQ]
        _ =
            |localWordScaledTraceTerm (p := p) (q := q) N A L L (localWordSwapLToQ w)| := by
              rw [← localWordScaledTraceTerm_eq_of_noLinear
                  (p := p) (q := q) (N := N) (A := A) (L := L) (Q := L)
                  (w := localWordSwapLToQ w) hNoLswap]
        _ ≤
            N ^ (k - 1) *
              upperMixedWordAbound M N ^
                localWordLetterCount LocalExpansionLetter.A w *
              upperMixedWordL2bound (p := p) (q := q) N M speed a ^
                localWordLetterCount LocalExpansionLetter.L w *
              upperMixedWordQ2bound (p := p) (q := q) N speed a ^
                localWordLetterCount LocalExpansionLetter.Q w := by
          calc
            _ ≤
                N ^ (k - 1) *
                  upperMixedWordAbound M N ^
                    localWordLetterCount LocalExpansionLetter.A (localWordSwapLToQ w) *
                  upperMixedWordL2bound (p := p) (q := q) N M speed a ^
                    localWordLetterCount LocalExpansionLetter.L (localWordSwapLToQ w) *
                  upperMixedWordL2bound (p := p) (q := q) N M speed a ^
                    localWordLetterCount LocalExpansionLetter.Q (localWordSwapLToQ w) :=
              hswap
            _ =
                N ^ (k - 1) *
                  upperMixedWordAbound M N ^
                    localWordLetterCount LocalExpansionLetter.A w *
                  upperMixedWordL2bound (p := p) (q := q) N M speed a ^
                    localWordLetterCount LocalExpansionLetter.L w *
                  upperMixedWordQ2bound (p := p) (q := q) N speed a ^
                    localWordLetterCount LocalExpansionLetter.Q w := by
              rw [hAcount_swap, hLcount_swap, hQcount_swap, hQ0, pow_zero, mul_one]
              ring
    · have hLpos : 0 < localWordLetterCount LocalExpansionLetter.L w := by omega
      have hQpos : 0 < localWordLetterCount LocalExpansionLetter.Q w := by omega
      exact
        localWordScaledTraceTerm_posL_posQ_le_envelope
          (N := N) (M := M) (a := a) (speed := speed) (k := k)
          (A := A) (L := L) (Q := Q) (w := w) hNpos hM hA_op hL_frob hQ_frob
          hLpos hQpos

end AppendixB
