import PptFactorization.AppendixBAubrunProposition71

/-!
# Appendix B: real combinatorial bounds for the Aubrun Wick sum

This file separates the finite combinatorial estimates from the analytic
pipeline.  It proves a no-input real bound for the surviving Wick sum already
available in the repository.  This bound is intentionally crude: it counts all
closed walks, all sample words, and all permutations.

The sharp Aubrun Proposition 7.1 bound still requires the finer surviving
contraction encoding which improves this crude count to the polynomial
`Q(m)`-loss used in the paper.
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

omit [Fintype p] [Fintype q] [DecidableEq σ] in
/-- Each single off-diagonal Gamma edge coefficient has norm at most one. -/
theorem gammaEdgeCoeff_norm_le_one (i j : BipIndex p q) :
    ‖gammaEdgeCoeff (p := p) (q := q) (σ := σ) i j‖ ≤ (1 : ℝ) := by
  by_cases h : i = j
  · simp [gammaEdgeCoeff, h]
  · simpa [gammaEdgeCoeff, h] using
      sampleDimension_inv_norm_le_one (σ := σ)

omit [Fintype p] [Fintype q] [DecidableEq σ] in
/-- Crude coefficient bound for a full path: the norm of the product of edge
coefficients is bounded by the number of edges. -/
theorem pathGammaCoeff_norm_le_edgeCount
    (i j : BipIndex p q) {m : ℕ} (x : Fin m → BipIndex p q)
    (α : Fin (m + 1) → σ) :
    ‖pathGammaCoeff (p := p) (q := q) (σ := σ) i j x α‖ ≤
      (m + 1 : ℝ) := by
  calc
    ‖pathGammaCoeff (p := p) (q := q) (σ := σ) i j x α‖
        = ‖∏ e : Fin (m + 1),
            gammaEdgeCoeff (p := p) (q := q) (σ := σ)
              (pathSource i x e) (pathTarget j x e)‖ := by
            rfl
    _ ≤ ∏ e : Fin (m + 1),
          ‖gammaEdgeCoeff (p := p) (q := q) (σ := σ)
            (pathSource i x e) (pathTarget j x e)‖ := by
            exact
              Finset.norm_prod_le (Finset.univ : Finset (Fin (m + 1)))
                (fun e : Fin (m + 1) =>
                  gammaEdgeCoeff (p := p) (q := q) (σ := σ)
                    (pathSource i x e) (pathTarget j x e))
    _ ≤ ∏ _e : Fin (m + 1), (1 : ℝ) := by
            exact Finset.prod_le_prod (fun e _ => norm_nonneg _) fun e _ =>
              gammaEdgeCoeff_norm_le_one
                (p := p) (q := q) (σ := σ)
                (pathSource i x e) (pathTarget j x e)
    _ = (1 : ℝ) := by simp
    _ ≤ (m + 1 : ℝ) := by norm_num

omit [Fintype p] [Fintype q] [Fintype σ] in
/-- A surviving-pairing family is a subtype of all permutations. -/
theorem survivingClosedWalkPairing_card_le_perm_card
    {m : ℕ} (w : ClosedWalk (BipIndex p q) m)
    (α : Fin (m + 1) → σ) :
    Fintype.card
        (SurvivingClosedWalkPairing (p := p) (q := q) (σ := σ) w α) ≤
      Fintype.card (Equiv.Perm (Fin (m + 1))) := by
  change
    Fintype.card
        {π : Equiv.Perm (Fin (m + 1)) //
          ∀ k : Fin (m + 1),
            gammaEdgeHol (pathSource w.1 w.2 k) (pathTarget w.1 w.2 k) (α k) =
              gammaEdgeConj
                (pathSource w.1 w.2 (π k)) (pathTarget w.1 w.2 (π k))
                  (α (π k))} ≤
      Fintype.card (Equiv.Perm (Fin (m + 1)))
  exact Fintype.card_subtype_le _

omit [Fintype p] [Fintype q] in
/-- Crude real bound for one weighted surviving-pairing contribution. -/
theorem pathGammaCoeff_survivingCard_norm_le_crude
    {m : ℕ} (w : ClosedWalk (BipIndex p q) m)
    (α : Fin (m + 1) → σ) :
    ‖pathGammaCoeff (p := p) (q := q) (σ := σ) w.1 w.1 w.2 α *
        (Fintype.card
          (SurvivingClosedWalkPairing
            (p := p) (q := q) (σ := σ) w α) : ℂ)‖ ≤
      (m + 1 : ℝ) *
        (Fintype.card (Equiv.Perm (Fin (m + 1))) : ℝ) := by
  have hcoeff :
      ‖pathGammaCoeff (p := p) (q := q) (σ := σ) w.1 w.1 w.2 α‖ ≤
        (m + 1 : ℝ) :=
    pathGammaCoeff_norm_le_edgeCount
      (p := p) (q := q) (σ := σ) w.1 w.1 w.2 α
  have hcardNat :
      Fintype.card
          (SurvivingClosedWalkPairing (p := p) (q := q) (σ := σ) w α) ≤
        Fintype.card (Equiv.Perm (Fin (m + 1))) :=
    survivingClosedWalkPairing_card_le_perm_card
      (p := p) (q := q) (σ := σ) w α
  have hcard :
      (Fintype.card
          (SurvivingClosedWalkPairing
            (p := p) (q := q) (σ := σ) w α) : ℝ) ≤
        (Fintype.card (Equiv.Perm (Fin (m + 1))) : ℝ) := by
    exact_mod_cast hcardNat
  calc
    ‖pathGammaCoeff (p := p) (q := q) (σ := σ) w.1 w.1 w.2 α *
        (Fintype.card
          (SurvivingClosedWalkPairing
            (p := p) (q := q) (σ := σ) w α) : ℂ)‖
        ≤ ‖pathGammaCoeff (p := p) (q := q) (σ := σ) w.1 w.1 w.2 α‖ *
          ‖(Fintype.card
            (SurvivingClosedWalkPairing
              (p := p) (q := q) (σ := σ) w α) : ℂ)‖ := by
            exact norm_mul_le _ _
    _ = ‖pathGammaCoeff (p := p) (q := q) (σ := σ) w.1 w.1 w.2 α‖ *
          (Fintype.card
            (SurvivingClosedWalkPairing
              (p := p) (q := q) (σ := σ) w α) : ℝ) := by
            simp
    _ ≤ (m + 1 : ℝ) *
          (Fintype.card (Equiv.Perm (Fin (m + 1))) : ℝ) := by
            exact mul_le_mul hcoeff hcard (by positivity) (by positivity)

/-- No-input crude real combinatorial bound for Aubrun's surviving Wick sum. -/
theorem aubrunSurvivingPairingSumNorm_le_crude_real_sum (m : ℕ) :
    aubrunSurvivingPairingSumNorm (p := p) (q := q) (σ := σ) m ≤
      ∑ _w : ClosedWalk (BipIndex p q) m,
        ∑ _α : Fin (m + 1) → σ,
          (m + 1 : ℝ) *
            (Fintype.card (Equiv.Perm (Fin (m + 1))) : ℝ) := by
  unfold aubrunSurvivingPairingSumNorm
  exact Finset.sum_le_sum fun w _ =>
    Finset.sum_le_sum fun α _ =>
      pathGammaCoeff_survivingCard_norm_le_crude
        (p := p) (q := q) (σ := σ) w α

/-- Closed-form version of the crude real combinatorial bound. -/
theorem aubrunSurvivingPairingSumNorm_le_crude_real_count (m : ℕ) :
    aubrunSurvivingPairingSumNorm (p := p) (q := q) (σ := σ) m ≤
      (Fintype.card (ClosedWalk (BipIndex p q) m) : ℝ) *
        (Fintype.card (Fin (m + 1) → σ) : ℝ) *
          ((m + 1 : ℝ) *
            (Fintype.card (Equiv.Perm (Fin (m + 1))) : ℝ)) := by
  calc
    aubrunSurvivingPairingSumNorm (p := p) (q := q) (σ := σ) m
        ≤ ∑ _w : ClosedWalk (BipIndex p q) m,
            ∑ _α : Fin (m + 1) → σ,
              (m + 1 : ℝ) *
                (Fintype.card (Equiv.Perm (Fin (m + 1))) : ℝ) :=
          aubrunSurvivingPairingSumNorm_le_crude_real_sum
            (p := p) (q := q) (σ := σ) m
    _ =
      (Fintype.card (ClosedWalk (BipIndex p q) m) : ℝ) *
        (Fintype.card (Fin (m + 1) → σ) : ℝ) *
          ((m + 1 : ℝ) *
            (Fintype.card (Equiv.Perm (Fin (m + 1))) : ℝ)) := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]

/-- Branch from a real combinatorial bound on the crude count to the existing
Proposition 7.1-facing trace-moment theorem.

This is useful as a separate testing hook: replacing `hCrudeToEnvelope` by the
sharp Aubrun encoding/counting theorem is exactly the remaining combinatorial
upgrade. -/
theorem AubrunProposition71_traceMomentBound_of_crude_count_envelope
    {Q : ℕ → ℝ} {d s : ℝ}
    (hCrudeToEnvelope :
      ∀ m,
        (Fintype.card (ClosedWalk (BipIndex p q) m) : ℝ) *
            (Fintype.card (Fin (m + 1) → σ) : ℝ) *
              ((m + 1 : ℝ) *
                (Fintype.card (Equiv.Perm (Fin (m + 1))) : ℝ)) ≤
          aubrunOffDiagonalTraceMomentEnvelope Q d s m) :
    ∀ m,
      AubrunOffDiagonalTraceMomentBound
        (p := p) (q := q) (σ := σ) m
        (aubrunOffDiagonalTraceMomentEnvelope Q d s m) := by
  intro m
  exact
    (gaussianWishartGammaOffDiagonal_traceMoment_norm_le_aubrunSurvivingPairingSumNorm
      (p := p) (q := q) (σ := σ) m).trans
      ((aubrunSurvivingPairingSumNorm_le_crude_real_count
        (p := p) (q := q) (σ := σ) m).trans (hCrudeToEnvelope m))

/-!
Sharp fixed-defect counting closure in the style of Aubrun's Proposition 7.3.

The actual combinatorics of innovations/matching is packaged only through:

* a partition of the defect-`Δ` classes by finite innovation sets `I`,
* an embedding of each fiber over `I` into a pair of compatible-couple
  classes,
* the paper's large-innovation lower bound rewritten as
  `k ≤ 2 * |I| + 2 * Δ`,
* the paper's compatible-couple count
  `≤ (2k)^(9 * δ(I))`, where `δ(I) = k + 1 - |I⁺| - |I|`.

Once those are available, the exact paper arithmetic gives
`N_Δ ≤ 2^k (2k)^(36Δ)`.
-/

section AubrunSharpCounting

/-- Aubrun's `I⁺`: from an innovation set `I ⊂ [k - 1]`, add the initial
index and shift by one.  In Lean, `I : Finset (Fin k)` represents a subset of
`{0, ..., k - 1}`, and `I⁺ ⊂ {0, ..., k}` is `insert 0 (succ '' I)`. -/
def innovationLift (k : ℕ) (I : Finset (Fin k)) : Finset (Fin (k + 1)) :=
  insert 0 (I.image Fin.succ)

@[simp] theorem card_innovationLift (k : ℕ) (I : Finset (Fin k)) :
    (innovationLift k I).card = I.card + 1 := by
  have hnot : (0 : Fin (k + 1)) ∉ I.image Fin.succ := by
    simp
  have hinj : Function.Injective (@Fin.succ k) := Fin.succ_injective k
  calc
    (innovationLift k I).card = (I.image Fin.succ).card + 1 := by
      simp [innovationLift, hnot, Nat.add_comm]
    _ = I.card + 1 := by
      rw [Finset.card_image_of_injective I hinj]

/-- The compatibility defect `δ = k + 1 - |I⁺| - |I|` appearing in the proof
of Proposition 7.3. -/
def compatibilityDefect (k : ℕ) (I : Finset (Fin k)) : ℕ :=
  k + 1 - ((innovationLift k I).card + I.card)

@[simp] theorem compatibilityDefect_eq (k : ℕ) (I : Finset (Fin k)) :
    compatibilityDefect k I = k - 2 * I.card := by
  unfold compatibilityDefect
  rw [card_innovationLift]
  omega

/-- If one records Aubrun's lower-innovation inequality with natural-number
floor division, one loses one unit: `k / 2 ≤ |I| + Δ` implies
`k ≤ 2 * |I| + 2 * Δ + 1`.  The sharp paper hypothesis used below is the
floor-free form `k ≤ 2 * |I| + 2 * Δ`. -/
theorem largeInnovation_rewrite {k Δ : ℕ} {I : Finset (Fin k)}
    (hI : k / 2 ≤ I.card + Δ) :
    k ≤ 2 * I.card + 2 * Δ + 1 := by
  have hhalf : 2 * (k / 2) ≤ 2 * (I.card + Δ) := Nat.mul_le_mul_left 2 hI
  have hk : k = 2 * (k / 2) + k % 2 := by
    exact (Nat.div_add_mod k 2).symm
  have hmod : k % 2 ≤ 1 := by
    omega
  calc
    k = 2 * (k / 2) + k % 2 := hk
    _ ≤ 2 * (I.card + Δ) + 1 := by omega
    _ = 2 * I.card + 2 * Δ + 1 := by omega

/-- Under the large-innovation lower bound, Aubrun's auxiliary defect
parameter satisfies `δ ≤ 2Δ`. -/
theorem compatibilityDefect_le_two_mul {k Δ : ℕ} {I : Finset (Fin k)}
    (hI : k ≤ 2 * I.card + 2 * Δ) :
    compatibilityDefect k I ≤ 2 * Δ := by
  rw [compatibilityDefect_eq]
  omega

/-- Fiberwise closure of Aubrun's proof: if the fiber over a fixed innovation
set `I` embeds into a pair of compatible-couple classes, and each compatible
couple class is bounded by `(2k)^(9 * δ(I))`, then the whole fiber is bounded
by `(2k)^(36Δ)`. -/
theorem fiber_card_le_pow_of_compatible_bounds
    {k Δ : ℕ} (hk : 1 ≤ k)
    {I : Finset (Fin k)}
    {Fiber LeftCouples RightCouples : Type*}
    [Fintype Fiber] [Fintype LeftCouples] [Fintype RightCouples]
    (encode : Fiber ↪ LeftCouples × RightCouples)
    (hLeft :
      Fintype.card LeftCouples ≤ (2 * k) ^ (9 * compatibilityDefect k I))
    (hRight :
      Fintype.card RightCouples ≤ (2 * k) ^ (9 * compatibilityDefect k I))
    (hI : k ≤ 2 * I.card + 2 * Δ) :
    Fintype.card Fiber ≤ (2 * k) ^ (36 * Δ) := by
  have hδ : compatibilityDefect k I ≤ 2 * Δ :=
    compatibilityDefect_le_two_mul (I := I) hI
  have hbase : 1 ≤ 2 * k := by omega
  calc
    Fintype.card Fiber ≤ Fintype.card (LeftCouples × RightCouples) :=
      Fintype.card_le_of_embedding encode
    _ = Fintype.card LeftCouples * Fintype.card RightCouples := by simp
    _ ≤ (2 * k) ^ (9 * compatibilityDefect k I) *
          (2 * k) ^ (9 * compatibilityDefect k I) := by
          exact Nat.mul_le_mul hLeft hRight
    _ = (2 * k) ^ (18 * compatibilityDefect k I) := by
          rw [← Nat.pow_add]
          congr 1
          omega
    _ ≤ (2 * k) ^ (18 * (2 * Δ)) := by
          exact Nat.pow_le_pow_right hbase (Nat.mul_le_mul_left 18 hδ)
    _ = (2 * k) ^ (36 * Δ) := by
          congr 1
          omega

/-- Exact combinatorial closure of Aubrun's fixed-defect count once the local
innovation/compatibility bounds are available on each fiber. -/
theorem fixedDefectClassCount_le
    {k Δ : ℕ} (hk : 1 ≤ k)
    {Fiber LeftCouples RightCouples : Finset (Fin k) → Type*}
    [∀ I, Fintype (Fiber I)]
    [∀ I, Fintype (LeftCouples I)]
    [∀ I, Fintype (RightCouples I)]
    (encode :
      ∀ I : Finset (Fin k),
        Fiber I ↪ LeftCouples I × RightCouples I)
    (hLeft :
      ∀ I : Finset (Fin k),
        Fintype.card (LeftCouples I) ≤
          (2 * k) ^ (9 * compatibilityDefect k I))
    (hRight :
      ∀ I : Finset (Fin k),
        Fintype.card (RightCouples I) ≤
          (2 * k) ^ (9 * compatibilityDefect k I))
    (hLarge :
      ∀ I : Finset (Fin k),
        Fintype.card (Fiber I) ≠ 0 → k ≤ 2 * I.card + 2 * Δ) :
    Fintype.card (Σ I : Finset (Fin k), Fiber I) ≤
      2 ^ k * (2 * k) ^ (36 * Δ) := by
  rw [Fintype.card_sigma]
  calc
    (∑ I : Finset (Fin k), Fintype.card (Fiber I))
        ≤ ∑ _I : Finset (Fin k), (2 * k) ^ (36 * Δ) := by
          exact Finset.sum_le_sum fun I _ => by
            by_cases hZero : Fintype.card (Fiber I) = 0
            · simp [hZero]
            · exact fiber_card_le_pow_of_compatible_bounds
                (hk := hk)
                (I := I)
                (encode := encode I)
                (hLeft := hLeft I)
                (hRight := hRight I)
                (hI := hLarge I hZero)
    _ = Fintype.card (Finset (Fin k)) * (2 * k) ^ (36 * Δ) := by
          simp [Finset.sum_const]
    _ = 2 ^ k * (2 * k) ^ (36 * Δ) := by
          simp

end AubrunSharpCounting

end AppendixB
end PptFactorization
