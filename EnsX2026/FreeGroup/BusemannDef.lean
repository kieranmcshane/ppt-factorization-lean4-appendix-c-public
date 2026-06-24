import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Data.Nat.Find
import EnsX2026.Cayley.Growth
import EnsX2026.FreeGroup.TreeAndGrowth

/-!
# Busemann function on `F_2` — definitional preamble

Split out of `EnsX2026.FreeGroup.Busemann` so that the neighbour-structure
proofs in `EnsX2026.FreeGroup.BusemannLocal` can import these definitions
without creating a circular dependency with `Busemann.lean`'s downstream
theorems.

Contents: the generators `genA, genB`, the non-cancellation predicate,
the boundary `F2_boundary` with its notation `∂F2`, the prefix-matching
predicate `PrefixMatches`, and the Busemann function itself.
-/

namespace EnsX2026.FreeGroup

open scoped Classical
open EnsX2026.Cayley

/-! ### The free group `F_2`, its generators, and its generating set

`F2`, `F2_generating_set` are defined in
`EnsX2026.FreeGroup.TreeAndGrowth` and re-used here. -/

/-- Generator `a = FreeGroup.of 0` (alias for clarity, matching
`EnsX2026.FreeGroup.TreeAndGrowth`). -/
def genA : F2 := _root_.FreeGroup.of 0

/-- Generator `b = FreeGroup.of 1`. -/
def genB : F2 := _root_.FreeGroup.of 1

/-! ### The boundary `∂F_2` of infinite reduced words -/

/-- Two pairs `(g₁, b₁)` and `(g₂, b₂)` cancel iff `g₁ = g₂` and `b₂ = ¬ b₁`.
The *non-cancellation* predicate is therefore `g₁ ≠ g₂ ∨ b₁ = b₂`. -/
def NonCancellation (p q : (Fin 2) × Bool) : Prop := p.1 ≠ q.1 ∨ p.2 = q.2

/-- An infinite reduced word on the generators of `F_2`: a sequence
`φ : ℕ → (Fin 2) × Bool` such that no two consecutive letters cancel. -/
def F2_boundary : Type :=
  { φ : ℕ → (Fin 2) × Bool // ∀ n : ℕ, NonCancellation (φ n) (φ (n + 1)) }

@[inherit_doc] notation "∂F2" => F2_boundary

namespace F2_boundary

/-- Evaluate a boundary point at index `n`. -/
def eval (φ : ∂F2) (n : ℕ) : (Fin 2) × Bool := φ.val n

/-- The first `p` letters of `φ` as a `List`. -/
def prefixList (φ : ∂F2) (p : ℕ) : List ((Fin 2) × Bool) :=
  (List.range p).map (fun i => φ.val i)

@[simp] lemma prefixList_length (φ : ∂F2) (p : ℕ) :
    (prefixList φ p).length = p := by
  simp [prefixList]

/-- The element of `F_2` corresponding to the first `p` letters of `φ`.
In general this group element may reduce further (even though `φ` is reduced),
so we use `FreeGroup.mk` rather than asserting any list identity. -/
def valPrefix (φ : ∂F2) (p : ℕ) : F2 :=
  _root_.FreeGroup.mk (prefixList φ p)

end F2_boundary

/-! ### The Busemann function -/

/-- The predicate "the first `p` letters of `x.toWord` agree with the first
`p` letters of `φ`". -/
def PrefixMatches (x : F2) (φ : ∂F2) (p : ℕ) : Prop :=
  p ≤ x.toWord.length ∧
    ∀ i : ℕ, i < p → x.toWord[i]? = some (φ.val i)

/-- The common-prefix length `m(x, φ)`: the largest `p ≤ |x|` such that the
first `p` letters of `x.toWord` match the first `p` letters of `φ`.
Uses `Nat.findGreatest` on the interval `[0, |x|]`. -/
noncomputable def common_prefix_length (x : F2) (φ : ∂F2) : ℕ :=
  Nat.findGreatest (fun p => PrefixMatches x φ p) x.toWord.length

/-- The **Busemann function** `b_φ : F_2 → ℤ`, defined as
`b_φ(x) = |x| − 2 · m(x, φ)` where `|x|` is the reduced-word length of `x`
and `m` is the common-prefix length. -/
noncomputable def busemann (φ : ∂F2) (x : F2) : ℤ :=
  (x.toWord.length : ℤ) - 2 * (common_prefix_length x φ : ℤ)

end EnsX2026.FreeGroup
