import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.Coeff
import PptFactorization.ClosedFormDet

/-!
# Moments of the spectral distribution

## Description

This file defines the moments `c_k(λ)` of the empirical spectral distribution
and states the closed formula in terms of Catalan numbers.

**Definition** : `c_k(λ) := ∑_{l=0}^{⌊k/2⌋} C(k, 2l) * Cat(l) * λ^(k - l)`

where `Cat(l)` is the `l`-th Catalan number.

## References

- `Nat.catalan`  in `Mathlib.Combinatorics.Catalan`
- `Nat.choose`   in `Mathlib.Data.Nat.Choose.Basic`
-/

open scoped BigOperators Polynomial

open Nat Polynomial

/-- The `k`-th moment `c_k(λ)` as a polynomial in `λ` over `ℤ`. -/
noncomputable def momentPoly (k : ℕ) : Polynomial ℤ :=
  ∑ l ∈ Finset.range (k / 2 + 1),
    Polynomial.C (↑(Nat.choose k (2 * l) * catalan l) : ℤ) *
    Polynomial.X ^ (k - l)

/-- Closed formula for `c_k(λ)`:
    the `k`-th moment equals
    `∑_{l=0}^{⌊k/2⌋} C(k, 2l) * Catalan(l) * λ^(k - l)`. -/
theorem moment_closed_formula (k : ℕ) :
    momentPoly k =
    ∑ l ∈ Finset.range (k / 2 + 1),
      Polynomial.C (↑(Nat.choose k (2 * l) * catalan l) : ℤ) *
      Polynomial.X ^ (k - l) := by
  rfl
/-- Vandermonde convolution variant:
    `∑_{i+j=k} C(i, r) * C(j, s) = C(k+1, r+s+1)`
    Proof: double induction on r then k, using Pascal and the hockey-stick. -/
private lemma choose_antidiagonal_sum : ∀ (r s k : ℕ),
    ∑ ij ∈ Finset.antidiagonal k, ij.1.choose r * ij.2.choose s =
    (k + 1).choose (r + s + 1) := by
  intro r
  induction r with
  | zero =>
    intro s k
    simp only [Nat.choose_zero_right, one_mul]
    -- Sum becomes ∑ ij ∈ antidiag k, ij.2.choose s
    -- = ∑ j ∈ range(k+1), (k-j).choose s = ∑ j ∈ range(k+1), j.choose s = C(k+1, s+1)
    induction k with
    | zero =>
      simp only [Finset.antidiagonal_zero, Finset.sum_singleton, Nat.zero_add]
      -- goal: choose 0 s = choose 1 (s + 1)
      -- By Pascal: choose 1 (s+1) = choose 0 s + choose 0 (s+1), and choose 0 (s+1) = 0
      have hP := Nat.choose_succ_succ' 0 s
      have h0 : Nat.choose 0 (s + 1) = 0 :=
        Nat.choose_eq_zero_iff.mpr (Nat.succ_pos s)
      linarith
    | succ n ih =>
      rw [Finset.Nat.sum_antidiagonal_succ, ih]
      simp only [zero_add, ← Nat.choose_succ_succ']
  | succ r' ih_r =>
    intro s k
    induction k with
    | zero =>
      simp only [Finset.antidiagonal_zero, Finset.sum_singleton]
      -- use show to normalize (0+1) to 1 in the goal
      show Nat.choose 0 (r' + 1) * Nat.choose 0 s =
           Nat.choose 1 (r' + 1 + s + 1)
      rw [Nat.choose_eq_zero_iff.mpr (by omega : 0 < r' + 1),
          zero_mul,
          Nat.choose_eq_zero_iff.mpr (by omega : 1 < r' + 1 + s + 1)]
    | succ n ih_k =>
      rw [Finset.Nat.sum_antidiagonal_succ]
      dsimp only [Prod.fst, Prod.snd]
      -- choose 0 (r'+1) = 0 by the second pattern of the recursive definition
      have h0 : Nat.choose 0 (r' + 1) = 0 := rfl
      rw [h0, zero_mul, zero_add]
      simp_rw [Nat.choose_succ_succ' _ r', Nat.add_mul]
      rw [Finset.sum_add_distrib, ih_k, ih_r s n]
      rw [show r' + 1 + s + 1 = r' + s + 1 + 1 by ring]
      rw [← Nat.choose_succ_succ']

/-- The coefficient of `X^(k+1-s)` in `momentPoly k` is `C(k, 2s) * catalan s`,
    for `s ≤ k / 2`. -/
private lemma momentPoly_coeff (k s : ℕ) (hs : s ≤ k / 2) :
    (momentPoly k).coeff (k - s) = (k.choose (2 * s) * catalan s : ℕ) := by
  simp only [momentPoly, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow]
  rw [Finset.sum_eq_single s]
  · simp
  · intro b hb hbs
    simp only [Finset.mem_range] at hb
    have : k - s ≠ k - b := by omega
    simp [this]
  · intro h
    simp only [Finset.mem_range, not_lt] at h
    omega

private lemma momentPoly_coeff_zero (k : ℕ) (n : ℕ) (hn : n < k - k / 2) :
    (momentPoly k).coeff n = 0 := by
  simp only [momentPoly, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow]
  apply Finset.sum_eq_zero
  intro l hl
  simp only [Finset.mem_range] at hl
  have hkl : k - l ≠ n := by omega
  simp only [if_neg (Ne.symm hkl), mul_zero]

-- convolution_coeff_eq is no longer needed: moment_recurrence is proved
-- via the ℝ-valued identity in ClosedFormDet.moment_functional_coeff
-- and injectivity of ℤ ↪ ℝ.

/-- Bridge: evaluating `momentPoly k` at `lam : ℝ` gives `ClosedFormDet.M lam k`. -/
private lemma eval₂_momentPoly (k : ℕ) (lam : ℝ) :
    Polynomial.eval₂ (Int.castRingHom ℝ) lam (momentPoly k) =
    ClosedFormDet.M lam k := by
  simp only [momentPoly, ClosedFormDet.M, Polynomial.eval₂_finset_sum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Int.coe_castRingHom]
  apply Finset.sum_congr rfl; intro l _
  push_cast; ring

/-- A polynomial over ℝ (infinite integral domain) vanishing everywhere is zero.
    Standard consequence of `card_roots_le_degree`. -/
private lemma Polynomial.eq_zero_of_forall_eval_eq_zero (f : Polynomial ℝ)
    (h : ∀ x : ℝ, f.eval x = 0) : f = 0 := by
  by_contra hne
  have hfin : Multiset.card f.roots ≤ f.natDegree := Polynomial.card_roots' f
  -- Every x : ℝ is a root, but roots is a finite multiset
  have hmem : ∀ x : ℝ, x ∈ f.roots := fun x =>
    (Polynomial.mem_roots hne).mpr (h x)
  -- f.roots.toFinset contains all of ℝ, contradicting finiteness
  have : Set.univ ⊆ ↑f.roots.toFinset := fun x _ => Multiset.mem_toFinset.mpr (hmem x)
  exact absurd (Set.Finite.subset f.roots.toFinset.finite_toSet this)
    Set.infinite_univ.not_finite

/-- Two ℝ-polynomials agreeing everywhere are equal. -/
private lemma Polynomial.eq_of_forall_eval_eq (f g : Polynomial ℝ)
    (h : ∀ x : ℝ, f.eval x = g.eval x) : f = g := by
  have : f - g = 0 := Polynomial.eq_zero_of_forall_eval_eq_zero (f - g)
    (fun x => by rw [Polynomial.eval_sub, sub_eq_zero]; exact h x)
  exact sub_eq_zero.mp this

theorem moment_recurrence (k : ℕ) :
  momentPoly (k + 2) =
  Polynomial.X * (momentPoly (k + 1) +
  ∑ ij ∈ Finset.antidiagonal k, momentPoly ij.1 * momentPoly ij.2) := by
  -- Strategy: map to ℝ[X] via injective ℤ → ℝ, then show pointwise equality.
  apply Polynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective
  -- Two ℝ-polynomials are equal iff they agree at all points
  set LHS := (momentPoly (k + 2)).map (Int.castRingHom ℝ)
  set RHS := (Polynomial.X * (momentPoly (k + 1) +
    ∑ ij ∈ Finset.antidiagonal k, momentPoly ij.1 * momentPoly ij.2)).map (Int.castRingHom ℝ)
  apply Polynomial.eq_of_forall_eval_eq LHS RHS
  intro lam
  -- Evaluate both sides using eval₂_momentPoly bridge
  simp only [LHS, RHS, Polynomial.eval_map]
  rw [eval₂_momentPoly]
  -- RHS: eval₂ of X * (sum)
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_add,
    Polynomial.eval₂_finset_sum, Polynomial.eval₂_mul]
  simp_rw [eval₂_momentPoly]
  -- Goal: M lam (k+2) = lam * (M lam (k+1) + Σ M lam i * M lam j)
  -- From ClosedFormDet.moment_functional_coeff:
  --   M(k+2) − lam·M(k+1) = lam · Σ M(i)·M(j)
  have h := ClosedFormDet.moment_functional_coeff lam (k + 2) (by omega)
  simp only [show k + 2 - 1 = k + 1 from by omega,
             show k + 2 - 2 = k from by omega] at h
  linarith
