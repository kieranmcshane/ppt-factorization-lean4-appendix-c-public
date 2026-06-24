import PptFactorization.TraceWickExpansion

/-!
# Polynomial counting bounds for Wick trace expansions

This file isolates the purely finite-combinatorial part of the
Aubrun-moment pipeline.

The useful pattern is the following.  A family of Wick contractions is
polynomially counted once every relevant contraction can be encoded by a
fixed number `r` of marked positions in a word of length `m`.  The explicit
polynomial control is then

`countingQ r m = (m + 1)^r`.

The final Aubrun estimate still needs the mathematical identification that
the surviving partial-transpose Wick contractions admit such an encoding.
This file proves the reusable, axiom-free counting closure around that
identification.
-/

open scoped BigOperators

namespace PptFactorization
namespace TraceWickExpansion

open MeasureTheory

universe u v w t

variable {ι : Type u} {Ω₀ : Type v} {η : Type w}

/-! ## Polynomial envelopes -/

/-- A concrete polynomial envelope `C * (m + 1)^r`. -/
def polynomialEnvelope (C r m : ℕ) : ℕ :=
  C * (m + 1) ^ r

/-- A natural-valued sequence is bounded by a fixed polynomial envelope. -/
def PolynomiallyBounded (f : ℕ → ℕ) : Prop :=
  ∃ C r : ℕ, ∀ m : ℕ, f m ≤ polynomialEnvelope C r m

/-- The explicit polynomial `Q_r(m) = (m + 1)^r` produced by an `r`-position
encoding. -/
def countingQ (r m : ℕ) : ℕ :=
  (m + 1) ^ r

theorem countingQ_pos (r m : ℕ) : 0 < countingQ r m := by
  unfold countingQ
  positivity

theorem countingQ_polynomiallyBounded (r : ℕ) :
    PolynomiallyBounded (countingQ r) := by
  refine ⟨1, r, ?_⟩
  intro m
  simp [polynomialEnvelope, countingQ]

theorem polynomiallyBounded_of_le_countingQ
    {f : ℕ → ℕ} {r : ℕ} (hf : ∀ m, f m ≤ countingQ r m) :
    PolynomiallyBounded f := by
  refine ⟨1, r, ?_⟩
  intro m
  simpa [polynomialEnvelope, countingQ] using hf m

/-! ## Encoding by marked positions -/

/-- `r` marked positions in a word with positions `0, ..., m`. -/
abbrev DefectConfig (m r : ℕ) :=
  Fin r → Fin (m + 1)

@[simp] theorem card_defectConfig (m r : ℕ) :
    Fintype.card (DefectConfig m r) = countingQ r m := by
  simp [DefectConfig, countingQ]

/-- A finite family is polynomially encoded at scale `m` and rank `r` if it
injects into the `r`-tuples of positions of a word of length `m + 1`. -/
structure PolynomiallyEncoded (α : Type u) (m r : ℕ) [Fintype α] where
  encode : α ↪ DefectConfig m r

namespace PolynomiallyEncoded

theorem card_le_countingQ {α : Type u} [Fintype α] {m r : ℕ}
    (E : PolynomiallyEncoded α m r) :
    Fintype.card α ≤ countingQ r m := by
  calc
    Fintype.card α ≤ Fintype.card (DefectConfig m r) :=
      Fintype.card_le_of_embedding E.encode
    _ = countingQ r m := card_defectConfig m r

theorem polynomiallyBounded_card {α : ℕ → Type u}
    (r : ℕ) [∀ m, Fintype (α m)]
    (E : ∀ m, PolynomiallyEncoded (α m) m r) :
    PolynomiallyBounded fun m => Fintype.card (α m) :=
  polynomiallyBounded_of_le_countingQ fun m =>
    card_le_countingQ (E m)

end PolynomiallyEncoded

/-! ## Pairing/contraction families -/

/-- Paper-facing package for a family of relevant Wick contractions/pairings
whose members are controlled by a fixed number of marked positions. -/
structure RelevantPairingFamily (m r : ℕ) where
  Pairing : Type u
  pairingFintype : Fintype Pairing
  encode : Pairing ↪ DefectConfig m r

attribute [instance] RelevantPairingFamily.pairingFintype

namespace RelevantPairingFamily

theorem card_le_countingQ {m r : ℕ} (P : RelevantPairingFamily m r) :
    Fintype.card P.Pairing ≤ countingQ r m := by
  letI := P.pairingFintype
  calc
    Fintype.card P.Pairing ≤ Fintype.card (DefectConfig m r) :=
      Fintype.card_le_of_embedding P.encode
    _ = countingQ r m := card_defectConfig m r

theorem card_polynomiallyBounded {r : ℕ}
    (P : ∀ m, RelevantPairingFamily m r) :
    PolynomiallyBounded fun m => Fintype.card ((P m).Pairing) :=
  polynomiallyBounded_of_le_countingQ fun m =>
    card_le_countingQ (P m)

end RelevantPairingFamily

/-! ## Closed walks and sample words -/

@[simp] theorem card_closedWalk [Fintype ι] (m : ℕ) :
    Fintype.card (ClosedWalk ι m) = Fintype.card ι ^ (m + 1) := by
  simp [ClosedWalk, pow_succ, Nat.mul_comm]

theorem card_closedWalk_le_add_countingQ_pow [Fintype ι] (m r : ℕ) :
    Fintype.card (ClosedWalk ι m) ≤
      (Fintype.card ι + countingQ r m) ^ (m + 1) := by
  rw [card_closedWalk]
  exact Nat.pow_le_pow_left
    (Nat.le_add_right (Fintype.card ι) (countingQ r m)) (m + 1)

/-- A word of sample-column choices along `edgeCount` edges. -/
abbrev SampleWord (σ : Type*) (edgeCount : ℕ) :=
  Fin edgeCount → σ

@[simp] theorem card_sampleWord [Fintype σ] (edgeCount : ℕ) :
    Fintype.card (SampleWord σ edgeCount) = Fintype.card σ ^ edgeCount := by
  simp [SampleWord]

theorem card_sampleWord_le_add_countingQ_pow [Fintype σ]
    (edgeCount r m : ℕ) :
    Fintype.card (SampleWord σ edgeCount) ≤
      (Fintype.card σ + countingQ r m) ^ edgeCount := by
  rw [card_sampleWord]
  exact Nat.pow_le_pow_left
    (Nat.le_add_right (Fintype.card σ) (countingQ r m)) edgeCount

/-! ## Polynomially counted monomial expansions -/

/-- A closed-walk monomial expansion whose term set over every walk admits
an `r`-position polynomial encoding. -/
structure PolynomiallyCountedExpansion
    [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω₀] [DecidableEq η]
    (μ : Measure Ω₀) (Z : Ω₀ → Matrix ι ι ℂ) (g : Ω₀ → η → ℂ)
    (m r : ℕ) where
  expansion : ClosedWalkMonomialExpansion.{u, v, w, t} μ Z g m
  termCardLe : ∀ w : ClosedWalk ι m, Fintype.card (expansion.Term w) ≤ countingQ r m

namespace PolynomiallyCountedExpansion

variable [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω₀] [DecidableEq η]
variable {μ : Measure Ω₀} {Z : Ω₀ → Matrix ι ι ℂ} {g : Ω₀ → η → ℂ}
variable {m r : ℕ}

/-- Build a polynomially counted expansion from an actual injection of each
term family into the marked-position configurations. -/
def ofEncodedTerms
    (E : ClosedWalkMonomialExpansion.{u, v, w, t} μ Z g m)
    (encodeTerm : ∀ w : ClosedWalk ι m, E.Term w ↪ DefectConfig m r) :
    PolynomiallyCountedExpansion μ Z g m r where
  expansion := E
  termCardLe := by
    intro walk
    calc
      Fintype.card (E.Term walk) ≤ Fintype.card (DefectConfig m r) :=
        Fintype.card_le_of_embedding (encodeTerm walk)
      _ = countingQ r m := card_defectConfig m r

theorem term_card_le_countingQ
    (E : PolynomiallyCountedExpansion μ Z g m r)
    (w : ClosedWalk ι m) :
    Fintype.card (E.expansion.Term w) ≤ countingQ r m := by
  exact E.termCardLe w

theorem total_terms_card_le_closedWalk_mul_countingQ
    (E : PolynomiallyCountedExpansion μ Z g m r) :
    Fintype.card (Σ w : ClosedWalk ι m, E.expansion.Term w) ≤
      Fintype.card (ClosedWalk ι m) * countingQ r m := by
  rw [Fintype.card_sigma]
  calc
    (∑ w : ClosedWalk ι m, Fintype.card (E.expansion.Term w))
        ≤ ∑ _w : ClosedWalk ι m, countingQ r m := by
          exact Finset.sum_le_sum fun w _ => term_card_le_countingQ E w
    _ = Fintype.card (ClosedWalk ι m) * countingQ r m := by
          simp

theorem total_terms_card_le_dim_pow_mul_countingQ
    (E : PolynomiallyCountedExpansion μ Z g m r) :
    Fintype.card (Σ w : ClosedWalk ι m, E.expansion.Term w) ≤
      Fintype.card ι ^ (m + 1) * countingQ r m := by
  calc
    Fintype.card (Σ w : ClosedWalk ι m, E.expansion.Term w)
        ≤ Fintype.card (ClosedWalk ι m) * countingQ r m :=
          total_terms_card_le_closedWalk_mul_countingQ E
    _ = Fintype.card ι ^ (m + 1) * countingQ r m := by
          rw [card_closedWalk]

/-- Paper-shaped version: the closed-walk dimension factor can be weakened to
`(d + Q(m))^(m+1)`. -/
theorem total_terms_card_le_paper_envelope
    (E : PolynomiallyCountedExpansion μ Z g m r) :
    Fintype.card (Σ w : ClosedWalk ι m, E.expansion.Term w) ≤
      (Fintype.card ι + countingQ r m) ^ (m + 1) * countingQ r m := by
  calc
    Fintype.card (Σ w : ClosedWalk ι m, E.expansion.Term w)
        ≤ Fintype.card ι ^ (m + 1) * countingQ r m :=
          total_terms_card_le_dim_pow_mul_countingQ E
    _ ≤ (Fintype.card ι + countingQ r m) ^ (m + 1) * countingQ r m := by
          exact Nat.mul_le_mul_right (countingQ r m)
            (Nat.pow_le_pow_left
              (Nat.le_add_right (Fintype.card ι) (countingQ r m)) (m + 1))

end PolynomiallyCountedExpansion

end TraceWickExpansion
end PptFactorization
