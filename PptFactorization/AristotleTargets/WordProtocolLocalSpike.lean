import Mathlib.Data.List.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring

/-!
# Local-spike word protocol, abstract reduction layer

This file is the first checked Lean module for the local-spike word protocol
behind the upper-tail proof.  It deliberately does not pretend to prove the
hard matrix estimates.  Instead it records:

* the word alphabet and basic word predicates;
* an abstract proposition interface for the exact expansion, pure terms, mixed
  terms, local certificate, local upper bound, and exclusion;
* checked reduction theorems saying which ingredients imply which local
  conclusion.

The hard branch containing both `P` and `C` remains a theorem-strength input in
the predicate/rule interface.  In particular, it is not replaced by a crude
Schatten counting table.
-/

namespace PptFactorization
namespace WordProtocol

universe u v

/-- The three formal letters in the local spike expansion. -/
inductive Letter where
  | A
  | P
  | C
  deriving DecidableEq, Repr

namespace Letter

/-- Evaluate a formal letter as one of three noncommutative terms. -/
def eval {α : Type u} (A P C : α) : Letter → α
  | .A => A
  | .P => P
  | .C => C

end Letter

/-- A noncommutative word in the alphabet `{A, P, C}`. -/
abbrev Word := List Letter

namespace Word

/-- Count of `A` letters. -/
def countA : Word → Nat
  | [] => 0
  | Letter.A :: w => countA w + 1
  | _ :: w => countA w

/-- Count of `P` letters. -/
def countP : Word → Nat
  | [] => 0
  | Letter.P :: w => countP w + 1
  | _ :: w => countP w

/-- Count of `C` letters. -/
def countC : Word → Nat
  | [] => 0
  | Letter.C :: w => countC w + 1
  | _ :: w => countC w

/-- The pure `A` word predicate. -/
def isPureA (w : Word) : Prop :=
  countA w = w.length

/-- The pure `P` word predicate. -/
def isPureP (w : Word) : Prop :=
  countP w = w.length

/-- A mixed word is neither the pure background word nor the pure spike word. -/
def isMixed (w : Word) : Prop :=
  ¬ isPureA w ∧ ¬ isPureP w

/-- The word contains a `P`. -/
def hasP : Word → Prop
  | [] => False
  | Letter.P :: _ => True
  | _ :: w => hasP w

/-- The word contains a `C`. -/
def hasC : Word → Prop
  | [] => False
  | Letter.C :: _ => True
  | _ :: w => hasC w

/-- The delicate branch: a word contains both `P` and `C`. -/
def hasPandC (w : Word) : Prop :=
  hasP w ∧ hasC w

@[simp] theorem countA_nil : countA ([] : Word) = 0 := rfl
@[simp] theorem countP_nil : countP ([] : Word) = 0 := rfl
@[simp] theorem countC_nil : countC ([] : Word) = 0 := rfl

@[simp] theorem countA_cons_A (w : Word) :
    countA (Letter.A :: w) = countA w + 1 := rfl

@[simp] theorem countP_cons_P (w : Word) :
    countP (Letter.P :: w) = countP w + 1 := rfl

@[simp] theorem countC_cons_C (w : Word) :
    countC (Letter.C :: w) = countC w + 1 := rfl

@[simp] theorem hasPandC_iff (w : Word) :
    hasPandC w ↔ hasP w ∧ hasC w := Iff.rfl

theorem isMixed_not_pureA {w : Word} (h : isMixed w) : ¬ isPureA w :=
  h.1

theorem isMixed_not_pureP {w : Word} (h : isMixed w) : ¬ isPureP w :=
  h.2

/-- Evaluate a word as an ordered noncommutative product. -/
def evalProduct {α : Type u} [Monoid α] (A P C : α) : Word → α
  | [] => 1
  | l :: w => Letter.eval A P C l * evalProduct A P C w

/-- All formal words of length `n`, in prefix-recursive order. -/
def all : Nat → List Word
  | 0 => [[]]
  | n + 1 => (all n).flatMap fun w => [Letter.A :: w, Letter.P :: w, Letter.C :: w]

/--
The corresponding list of evaluated word terms.  This auxiliary recursion makes
the noncommutative expansion proof transparent.
-/
def expansionTerms {α : Type u} [Monoid α] (A P C : α) : Nat → List α
  | 0 => [1]
  | n + 1 => (expansionTerms A P C n).flatMap fun t => [A * t, P * t, C * t]

/-- Mapping prefixed words through `evalProduct` gives prefixed evaluated terms. -/
theorem map_evalProduct_prefix_flatMap {α : Type u} [Monoid α] (A P C : α) :
    ∀ xs : List Word,
      (xs.flatMap fun w => [Letter.A :: w, Letter.P :: w, Letter.C :: w]).map
          (evalProduct A P C) =
        (xs.map (evalProduct A P C)).flatMap fun t => [A * t, P * t, C * t] := by
  intro xs
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp [evalProduct, Letter.eval, ih]

/-- The recursively generated words evaluate to the recursively generated terms. -/
theorem map_evalProduct_all_eq_expansionTerms {α : Type u} [Monoid α] (A P C : α) :
    ∀ n, (all n).map (evalProduct A P C) = expansionTerms A P C n := by
  intro n
  induction n with
  | zero => simp [all, expansionTerms, evalProduct]
  | succ n ih =>
      simp [all, expansionTerms]
      rw [map_evalProduct_prefix_flatMap, ih]

/-- Sum of one recursive expansion layer. -/
theorem sum_flatMap_mul_triple {α : Type u} [NonUnitalNonAssocSemiring α]
    (A P C : α) :
    ∀ xs : List α,
      (xs.flatMap fun t => [A * t, P * t, C * t]).sum =
        (A + P + C) * xs.sum := by
  intro xs
  induction xs with
  | nil => simp
  | cons t ts ih =>
      simp [ih, left_distrib, right_distrib]
      ac_rfl

/-- Exact noncommutative expansion as a finite list of evaluated terms. -/
theorem expansionTerms_sum {α : Type u} [Semiring α] (A P C : α) :
    ∀ n, (expansionTerms A P C n).sum = (A + P + C) ^ n := by
  intro n
  induction n with
  | zero => simp [expansionTerms]
  | succ n ih =>
      rw [expansionTerms, sum_flatMap_mul_triple, ih]
      rw [pow_succ']

/--
WP-03 abstract algebra theorem: `(A + P + C)^n` is the finite sum over all
formal words of length `n`, evaluated as ordered products.
-/
theorem exact_finite_word_expansion {α : Type u} [Semiring α] (A P C : α) :
    ∀ n, ((all n).map (evalProduct A P C)).sum = (A + P + C) ^ n := by
  intro n
  rw [map_evalProduct_all_eq_expansionTerms, expansionTerms_sum]

/-- Scalar coefficient attached to a word by letter counts. -/
def beta {α : Type u} [Monoid α] (a p c : α) (w : Word) : α :=
  a ^ countA w * p ^ countP w * c ^ countC w

/--
WP-04 scalar coefficient formula: in a commutative coefficient monoid, the
ordered product of scalar letter coefficients is exactly
`a^(#A) * p^(#P) * c^(#C)`.
-/
theorem evalProduct_coeff_eq_beta {α : Type u} [CommMonoid α] (a p c : α) :
    ∀ w : Word, evalProduct a p c w = beta a p c w := by
  intro w
  induction w with
  | nil => simp [evalProduct, beta, countA, countP, countC]
  | cons l w ih =>
      cases l
      · simp [evalProduct, Letter.eval, beta, countA, countP, countC, ih, pow_succ']
        ac_rfl
      · simp [evalProduct, Letter.eval, beta, countA, countP, countC, ih, pow_succ']
        ac_rfl
      · simp [evalProduct, Letter.eval, beta, countA, countP, countC, ih, pow_succ']
        ac_rfl

end Word

/--
Abstract local-spike objects.

The concrete specialization should eventually replace `Matrix` by the matrix
type used for partial transposes and `Scalar` by the scalar field.
-/
structure WordProtocolObjects (Scalar : Type u) (Matrix : Type v) where
  d : Nat
  k : Nat
  X : Matrix
  Y : Matrix
  V : Matrix
  A : Matrix
  P : Matrix
  C : Matrix
  theta : Scalar

/--
Abstract proposition interface for the word protocol.

Every field is a mathematical assertion about the current local-spike object.
No field is evidence by itself; evidence is supplied either by a certificate or
by the rule structure below.
-/
structure WordProtocolPredicates (Scalar : Type u) (Matrix : Type v) where
  exactPartialTransposeDecomposition :
    WordProtocolObjects Scalar Matrix → Prop
  exactFiniteWordExpansion :
    WordProtocolObjects Scalar Matrix → Prop
  wordCoefficientFormula :
    WordProtocolObjects Scalar Matrix → Word → Prop
  pureATermControl :
    WordProtocolObjects Scalar Matrix → Prop
  purePTermControl :
    WordProtocolObjects Scalar Matrix → Prop
  mixedWordStructuralBound :
    WordProtocolObjects Scalar Matrix → Word → Prop
  mixedWordSumSmall :
    WordProtocolObjects Scalar Matrix → Prop
  localSpikeCertificate :
    WordProtocolObjects Scalar Matrix → Prop
  localUpperBound :
    WordProtocolObjects Scalar Matrix → Prop
  localExclusion :
    WordProtocolObjects Scalar Matrix → Prop
  upperTailLocalInput :
    WordProtocolObjects Scalar Matrix → Prop

/--
Rules that assemble the abstract word protocol.

These are the named theorem leaves/rules for the first milestone.  Later files
should prove these rules from the concrete matrix API, one branch at a time.
-/
structure WordProtocolRules
    {Scalar : Type u} {Matrix : Type v}
    (PRED : WordProtocolPredicates Scalar Matrix) where
  exactExpansionOfDecomposition :
    ∀ obj,
      PRED.exactPartialTransposeDecomposition obj →
      PRED.exactFiniteWordExpansion obj
  coefficientFormulaOfExpansion :
    ∀ obj w,
      PRED.exactFiniteWordExpansion obj →
      PRED.wordCoefficientFormula obj w
  mixedWordSumSmallOfWordwise :
    ∀ obj,
      (∀ w : Word, Word.isMixed w → PRED.mixedWordStructuralBound obj w) →
      PRED.mixedWordSumSmall obj
  localSpikeCertificateOfPieces :
    ∀ obj,
      PRED.exactFiniteWordExpansion obj →
      (∀ w : Word, PRED.wordCoefficientFormula obj w) →
      PRED.pureATermControl obj →
      PRED.purePTermControl obj →
      PRED.mixedWordSumSmall obj →
      PRED.localSpikeCertificate obj
  localUpperBoundOfCertificate :
    ∀ obj,
      PRED.localSpikeCertificate obj →
      PRED.localUpperBound obj
  localExclusionOfLocalUpperBound :
    ∀ obj,
      PRED.localUpperBound obj →
      PRED.localExclusion obj
  upperTailLocalInputOfExclusion :
    ∀ obj,
      PRED.localExclusion obj →
      PRED.upperTailLocalInput obj

/-- A compact certificate containing the theorem-strength local inputs. -/
structure WordProtocolCertificate
    {Scalar : Type u} {Matrix : Type v}
    (PRED : WordProtocolPredicates Scalar Matrix)
    (obj : WordProtocolObjects Scalar Matrix) where
  exactPartialTransposeDecomposition :
    PRED.exactPartialTransposeDecomposition obj
  pureATermControl :
    PRED.pureATermControl obj
  purePTermControl :
    PRED.purePTermControl obj
  mixedWordStructuralBound :
    ∀ w : Word, Word.isMixed w → PRED.mixedWordStructuralBound obj w

variable {Scalar : Type u} {Matrix : Type v}
variable {PRED : WordProtocolPredicates Scalar Matrix}
variable {obj : WordProtocolObjects Scalar Matrix}

/--
WP-07 reduction: a finite mixed-word conclusion follows from wordwise mixed
structural bounds once the corresponding rule has been proved for the concrete
model.
-/
theorem mixed_word_sum_small_of_forall_mixed_word_bound
    (RULES : WordProtocolRules PRED)
    (hWord : ∀ w : Word, Word.isMixed w → PRED.mixedWordStructuralBound obj w) :
    PRED.mixedWordSumSmall obj :=
  RULES.mixedWordSumSmallOfWordwise obj hWord

/--
WP-08 reduction: exact expansion, coefficients, pure controls, and mixed
control imply the local spike certificate.
-/
theorem localSpikeCertificate_of_wordCertificate
    (RULES : WordProtocolRules PRED)
    (hExp : PRED.exactFiniteWordExpansion obj)
    (hCoeff : ∀ w : Word, PRED.wordCoefficientFormula obj w)
    (hA : PRED.pureATermControl obj)
    (hP : PRED.purePTermControl obj)
    (hMixed : PRED.mixedWordSumSmall obj) :
    PRED.localSpikeCertificate obj :=
  RULES.localSpikeCertificateOfPieces obj hExp hCoeff hA hP hMixed

/-- WP-09 reduction: local spike certificate implies local upper bound. -/
theorem localUpperBound_of_localSpikeCertificate
    (RULES : WordProtocolRules PRED)
    (hCert : PRED.localSpikeCertificate obj) :
    PRED.localUpperBound obj :=
  RULES.localUpperBoundOfCertificate obj hCert

/-- WP-09 reduction: local upper bound implies neighbourhood exclusion. -/
theorem localExclusion_of_localUpperBound
    (RULES : WordProtocolRules PRED)
    (hLocal : PRED.localUpperBound obj) :
    PRED.localExclusion obj :=
  RULES.localExclusionOfLocalUpperBound obj hLocal

/--
First useful endpoint: a word-protocol certificate plus concrete assembly rules
supplies the local input consumed by the upper-tail pipeline.
-/
theorem upperTailLocalInput_of_wordProtocol
    (RULES : WordProtocolRules PRED)
    (CERT : WordProtocolCertificate PRED obj) :
    PRED.upperTailLocalInput obj := by
  have hExp : PRED.exactFiniteWordExpansion obj :=
    RULES.exactExpansionOfDecomposition obj
      CERT.exactPartialTransposeDecomposition
  have hCoeff : ∀ w : Word, PRED.wordCoefficientFormula obj w :=
    fun w => RULES.coefficientFormulaOfExpansion obj w hExp
  have hMixed : PRED.mixedWordSumSmall obj :=
    mixed_word_sum_small_of_forall_mixed_word_bound
      (RULES := RULES) CERT.mixedWordStructuralBound
  have hCert : PRED.localSpikeCertificate obj :=
    localSpikeCertificate_of_wordCertificate
      (RULES := RULES) hExp hCoeff CERT.pureATermControl
      CERT.purePTermControl hMixed
  have hLocal : PRED.localUpperBound obj :=
    localUpperBound_of_localSpikeCertificate (RULES := RULES) hCert
  have hExcl : PRED.localExclusion obj :=
    localExclusion_of_localUpperBound (RULES := RULES) hLocal
  exact RULES.upperTailLocalInputOfExclusion obj hExcl

end WordProtocol
end PptFactorization
