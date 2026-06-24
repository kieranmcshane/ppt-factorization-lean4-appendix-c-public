import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.RowCol
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.GroupTheory.Perm.Sign

/-!
# ENS/Polytechnique 2026 Math A — Q7, Q8

**Q7.** Determinant of the polynomial-valued arrowhead matrix
`delta_matrix n`: `δₙ(X) = (X - n)(X - 1)^{n-2}`.

**Q8.** Characteristic polynomial of the real arrowhead matrix
`S_matrix n`: `χ_{Sₙ}(X) = X(X - n)(X - 1)^{n-2}`.

### Strategy

We introduce a generalised arrowhead matrix `arrowhead n a b d` on
`Fin (n+1)` and compute its determinant directly from the Leibniz formula.

Only two classes of permutations give nonzero contributions:
* the identity (yielding `a · d^n`);
* transpositions `swap 0 k` with `k ≠ 0` (each yielding `- b^2 · d^(n-1)`;
  there are `n` such transpositions).

Hence `det(arrowhead n a b d) = a · d^n - n · b^2 · d^(n-1)` for `n ≥ 1`.

Both Q7 and Q8 follow by specialising `(a, b, d)`.

The formulas degenerate for `N < 2`, so the main theorems assume `2 ≤ N`.
-/

namespace EnsX2026.Matrices.Sn

open Matrix Polynomial Equiv Equiv.Perm Finset

noncomputable section

universe u

variable {R : Type u} [CommRing R]

/-! ### The arrowhead matrix (on `Fin n.succ`) -/

/-- "Arrowhead" matrix on `Fin (n+1)` with parameters `(a, b, d) : R³`:
`(0,0)` entry is `a`; off-diagonal first-row/column entries are `b`;
other diagonal entries are `d`; everything else is `0`.

We index by `Fin (n+1)` so that `0 : Fin (n+1)` is always well-defined. -/
def arrowhead (n : ℕ) (a b d : R) : Matrix (Fin (n+1)) (Fin (n+1)) R :=
  Matrix.of fun i j =>
    if i = 0 ∧ j = 0 then a
    else if i = 0 ∨ j = 0 then b
    else if i = j then d
    else 0

lemma arrowhead_zero_zero (n : ℕ) (a b d : R) :
    arrowhead n a b d 0 0 = a := by
  unfold arrowhead
  simp

lemma arrowhead_zero_of_ne {n : ℕ} (a b d : R) {j : Fin (n+1)} (hj : j ≠ 0) :
    arrowhead n a b d 0 j = b := by
  unfold arrowhead
  simp [Matrix.of_apply, hj]

lemma arrowhead_of_ne_zero {n : ℕ} (a b d : R) {i : Fin (n+1)} (hi : i ≠ 0) :
    arrowhead n a b d i 0 = b := by
  unfold arrowhead
  simp [Matrix.of_apply, hi]

lemma arrowhead_diag_of_ne_zero {n : ℕ} (a b d : R) {i : Fin (n+1)} (hi : i ≠ 0) :
    arrowhead n a b d i i = d := by
  unfold arrowhead
  simp [Matrix.of_apply, hi]

lemma arrowhead_off_diag {n : ℕ} (a b d : R) {i j : Fin (n+1)}
    (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) :
    arrowhead n a b d i j = 0 := by
  unfold arrowhead
  have h1 : ¬ (i = 0 ∧ j = 0) := fun h => hi h.1
  have h2 : ¬ (i = 0 ∨ j = 0) := fun h => h.elim hi hj
  simp [Matrix.of_apply, h1, h2, hij]

/-- Structural description of the arrowhead entry at `(σ i, i)`.
For the Leibniz product `∏ i, arrowhead (σ i) i` to be nonzero, each
pair `(σ i, i)` must fall into one of the four non-zero cases
enumerated by `arrowhead`. -/
lemma arrowhead_apply_eq_zero {n : ℕ} (a b d : R) {i j : Fin (n+1)}
    (hij_ne_both_zero : ¬ (i = 0 ∧ j = 0))
    (hnot_or : ¬ (i = 0 ∨ j = 0))
    (hij_ne : i ≠ j) : arrowhead n a b d i j = 0 := by
  unfold arrowhead
  simp [Matrix.of_apply, hij_ne_both_zero, hnot_or, hij_ne]

/-! ### Key: classifying permutations that give nonzero products -/

/-- If a permutation `σ : Perm (Fin (n+1))` satisfies `σ 0 = 0` and
contributes nonzero to the Leibniz sum for `arrowhead n a b d`, then
`σ` is the identity. -/
lemma perm_eq_id_of_fixes_zero_of_nonzero_prod {n : ℕ} (a b d : R)
    (σ : Perm (Fin (n+1))) (h0 : σ 0 = 0)
    (hprod : ∀ i, arrowhead n a b d (σ i) i ≠ 0) :
    σ = 1 := by
  apply Equiv.ext
  intro i
  by_cases hi : i = 0
  · subst hi
    simp [h0]
  -- σ i ≠ 0 because σ is a bijection and σ 0 = 0.
  have hσi_ne : σ i ≠ 0 := by
    intro h
    have heq : σ i = σ 0 := by rw [h, h0]
    exact hi (σ.injective heq)
  -- Now hprod i says arrowhead (σ i) i ≠ 0. Since σ i ≠ 0 and i ≠ 0,
  -- the only nonzero case is σ i = i.
  by_contra hne
  have hne' : σ i ≠ i := hne
  have h0' : arrowhead n a b d (σ i) i = 0 :=
    arrowhead_off_diag a b d hσi_ne hi hne'
  exact hprod i h0'

/-- If a permutation `σ : Perm (Fin (n+1))` satisfies `σ 0 ≠ 0` and
contributes nonzero to the Leibniz sum for `arrowhead n a b d`, then
`σ = swap 0 (σ 0)`. -/
lemma perm_eq_swap_of_moves_zero_of_nonzero_prod {n : ℕ} (a b d : R)
    (σ : Perm (Fin (n+1))) (h0 : σ 0 ≠ 0)
    (hprod : ∀ i, arrowhead n a b d (σ i) i ≠ 0) :
    σ = Equiv.swap 0 (σ 0) := by
  -- The key: σ (σ 0) = 0, since for i = σ 0 ≠ 0, the nonzero condition forces
  -- σ i ∈ {0, i}, and σ i = i would collide with σ 0 = i (contradiction).
  have hσ2 : σ (σ 0) = 0 := by
    have hk_ne : σ 0 ≠ 0 := h0
    -- We know arrowhead (σ (σ 0)) (σ 0) ≠ 0 (by hprod (σ 0)) and σ 0 ≠ 0.
    have hprodk := hprod (σ 0)
    -- Case split on whether σ (σ 0) = 0 or σ (σ 0) = σ 0.
    by_contra hcontra
    -- If σ (σ 0) ≠ 0 and σ 0 ≠ 0 and σ (σ 0) ≠ σ 0, the entry is 0.
    have hσk_ne_k : σ (σ 0) ≠ σ 0 := by
      intro hh
      -- σ (σ 0) = σ 0 would contradict injectivity.
      have heq : σ (σ 0) = σ 0 := hh
      have : σ 0 = 0 := σ.injective heq
      exact hk_ne this
    have h0' : arrowhead n a b d (σ (σ 0)) (σ 0) = 0 :=
      arrowhead_off_diag a b d hcontra hk_ne hσk_ne_k
    exact hprodk h0'
  -- Now show σ = swap 0 (σ 0).
  apply Equiv.ext
  intro i
  by_cases hi0 : i = 0
  · subst hi0
    simp [Equiv.swap_apply_left]
  by_cases hik : i = σ 0
  · subst hik
    rw [hσ2]
    simp [Equiv.swap_apply_right]
  -- For i ≠ 0, σ 0: show σ i = i.
  have hσi_ne_0 : σ i ≠ 0 := by
    intro h
    -- σ i = 0 = σ (σ 0) (since σ (σ 0) = 0)
    have heq : σ i = σ (σ 0) := by rw [h, hσ2]
    exact hik (σ.injective heq)
  have hσi_eq_i : σ i = i := by
    by_contra hne
    have h0' : arrowhead n a b d (σ i) i = 0 :=
      arrowhead_off_diag a b d hσi_ne_0 hi0 hne
    exact hprod i h0'
  rw [hσi_eq_i, Equiv.swap_apply_of_ne_of_ne hi0 hik]

/-! ### Computing the contributions -/

/-- The identity permutation's contribution to `det(arrowhead n a b d)`
is `a · d^n`. -/
lemma arrowhead_prod_id (n : ℕ) (a b d : R) :
    ∏ i : Fin (n+1), arrowhead n a b d ((1 : Perm (Fin (n+1))) i) i = a * d ^ n := by
  -- The product has one `a` (at i = 0) and n copies of `d`.
  rw [show (1 : Perm (Fin (n+1))) = Equiv.refl _ from rfl]
  simp only [Equiv.refl_apply]
  rw [Fin.prod_univ_succ]
  simp only [arrowhead_zero_zero]
  have : ∀ i : Fin n, arrowhead n a b d (Fin.succ i) (Fin.succ i) = d := by
    intro i
    exact arrowhead_diag_of_ne_zero a b d (Fin.succ_ne_zero i)
  simp [this, Finset.prod_const, Finset.card_univ]

/-- The product `∏ i, arrowhead n a b d ((swap 0 k) i) i = b^2 · d^(n-1)`
for any `k ≠ 0`. -/
lemma arrowhead_prod_swap {n : ℕ} (a b d : R) {k : Fin (n+1)} (hk : k ≠ 0) :
    ∏ i : Fin (n+1), arrowhead n a b d ((Equiv.swap (0 : Fin (n+1)) k) i) i =
      b * b * d ^ (n - 1) := by
  -- Split the product over i into three parts: i = 0, i = k, and i ∉ {0, k}.
  -- Value at i = 0: swap _ _ 0 = k, arrowhead k 0 = b.
  -- Value at i = k: swap 0 k k = 0, arrowhead 0 k = b.
  -- Value at i ∉ {0, k}: swap 0 k i = i, arrowhead i i = d.
  have h_univ : (Finset.univ : Finset (Fin (n+1))) = insert (0 : Fin (n+1)) (insert k ((Finset.univ : Finset (Fin (n+1))).erase 0 |>.erase k)) := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_univ, and_true]
    tauto
  rw [h_univ, Finset.prod_insert, Finset.prod_insert]
  rotate_left
  · -- k ∉ (univ \ {0, k})
    simp
  · -- 0 ∉ (insert k (univ \ {0, k}))
    simp [hk.symm]
  -- Now compute each factor.
  have hf0 : arrowhead n a b d ((Equiv.swap (0 : Fin (n+1)) k) 0) 0 = b := by
    rw [Equiv.swap_apply_left]
    exact arrowhead_of_ne_zero a b d hk
  have hfk : arrowhead n a b d ((Equiv.swap (0 : Fin (n+1)) k) k) k = b := by
    rw [Equiv.swap_apply_right]
    exact arrowhead_zero_of_ne a b d hk
  -- The remaining product over univ.erase 0 |>.erase k has all factors equal to d.
  have hrest : ∀ i ∈ ((Finset.univ : Finset (Fin (n+1))).erase 0 |>.erase k),
      arrowhead n a b d ((Equiv.swap (0 : Fin (n+1)) k) i) i = d := by
    intro i hi
    rw [Finset.mem_erase] at hi
    obtain ⟨hik, hi'⟩ := hi
    rw [Finset.mem_erase] at hi'
    obtain ⟨hi0, _⟩ := hi'
    rw [Equiv.swap_apply_of_ne_of_ne hi0 hik]
    exact arrowhead_diag_of_ne_zero a b d hi0
  rw [hf0, hfk, Finset.prod_congr rfl hrest, Finset.prod_const]
  -- Card of erase erase univ is (n+1) - 2 = n - 1.
  have hcard : ((Finset.univ : Finset (Fin (n+1))).erase 0 |>.erase k).card = n - 1 := by
    rw [Finset.card_erase_of_mem, Finset.card_erase_of_mem, Finset.card_univ, Fintype.card_fin]
    · omega
    · exact Finset.mem_univ _
    · rw [Finset.mem_erase]
      refine ⟨hk, Finset.mem_univ _⟩
  rw [hcard]
  ring

/-! ### Main determinant formula -/

/-- **Main arrowhead determinant formula.** For `n ≥ 1`:
`det(arrowhead n a b d) = a · d^n - n · b^2 · d^(n-1)`.

The `(n+1) × (n+1)` arrowhead matrix with `(0,0)`-entry `a`, off-diagonal
first-row/column entries `b`, remaining diagonal entries `d`, and zeros
elsewhere has determinant `a · d^n - n · b^2 · d^(n-1)`. -/
theorem arrowhead_det (n : ℕ) (hn : 1 ≤ n) (a b d : R) :
    (arrowhead n a b d).det = a * d ^ n - (n : R) * b ^ 2 * d ^ (n - 1) := by
  rw [Matrix.det_apply]
  -- We split the sum over all permutations into: σ = id, σ = swap 0 k for k ≠ 0, and "other".
  -- Other permutations contribute zero (by our classification lemmas).
  set S : Finset (Perm (Fin (n+1))) := Finset.univ with hS
  -- Express S = {id} ∪ {swap 0 k | k ≠ 0} ∪ rest.
  -- The "rest" has zero contribution; the first two contribute a·d^n and -n·b²·d^(n-1).
  -- We use Finset.sum_eq_zero for the "rest" indirectly via sum_bij or partitioning.
  -- For simplicity we use Finset.sum_congr combined with classify.
  -- Approach: use `Finset.sum_filter_add_sum_filter_not` with predicate
  -- `fun σ => σ 0 = 0`.
  have hsplit : ∑ σ : Perm (Fin (n+1)), σ.sign • ∏ i, arrowhead n a b d (σ i) i =
      (∑ σ ∈ (Finset.univ.filter (fun σ : Perm (Fin (n+1)) => σ 0 = 0)),
          σ.sign • ∏ i, arrowhead n a b d (σ i) i) +
      (∑ σ ∈ (Finset.univ.filter (fun σ : Perm (Fin (n+1)) => σ 0 ≠ 0)),
          σ.sign • ∏ i, arrowhead n a b d (σ i) i) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun σ => σ 0 = 0)]
  rw [hsplit]
  -- First piece: sum over σ with σ 0 = 0.
  have h_first : ∑ σ ∈ (Finset.univ.filter (fun σ : Perm (Fin (n+1)) => σ 0 = 0)),
      σ.sign • ∏ i, arrowhead n a b d (σ i) i = a * d ^ n := by
    -- Only σ = 1 contributes nonzero. Filter = {σ | σ 0 = 0}.
    -- The sum over such σ: if σ ≠ id, product = 0 (by classification).
    rw [Finset.sum_eq_single (1 : Perm (Fin (n+1)))]
    · simp only [sign_one, one_smul]
      exact arrowhead_prod_id n a b d
    · intro σ hσ hne1
      rw [Finset.mem_filter] at hσ
      obtain ⟨_, h0⟩ := hσ
      -- σ ≠ 1 and σ 0 = 0; classification says product = 0.
      have hzero : ∃ i, arrowhead n a b d (σ i) i = 0 := by
        by_contra hall
        push_neg at hall
        exact hne1 (perm_eq_id_of_fixes_zero_of_nonzero_prod a b d σ h0 hall)
      obtain ⟨i, hi⟩ := hzero
      have hp : ∏ j, arrowhead n a b d (σ j) j = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) hi
      rw [hp, smul_zero]
    · intro hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      exact absurd rfl hmem
  -- Second piece: sum over σ with σ 0 ≠ 0.
  -- Such σ is necessarily of the form swap 0 k for k = σ 0 ≠ 0 (by classification), if nonzero.
  have h_second : ∑ σ ∈ (Finset.univ.filter (fun σ : Perm (Fin (n+1)) => σ 0 ≠ 0)),
      σ.sign • ∏ i, arrowhead n a b d (σ i) i = - (n : R) * b ^ 2 * d ^ (n - 1) := by
    -- Reindex via k := σ 0; only σ = swap 0 k contributes nonzero for each k ≠ 0.
    -- For each k ≠ 0 (there are n such), swap 0 k contributes sign • product = -1 • (b·b·d^(n-1)) = -b²·d^(n-1).
    -- Sum = -n · b² · d^(n-1).
    have hsub : ∀ σ ∈ Finset.univ.filter (fun σ : Perm (Fin (n+1)) => σ 0 ≠ 0),
        σ.sign • ∏ i, arrowhead n a b d (σ i) i =
        if σ = Equiv.swap 0 (σ 0)
        then (-1 : R) * (b * b * d ^ (n - 1))
        else 0 := by
      intro σ hσ
      rw [Finset.mem_filter] at hσ
      obtain ⟨_, h0⟩ := hσ
      by_cases hsw : σ = Equiv.swap 0 (σ 0)
      · rw [if_pos hsw]
        -- sign(swap 0 (σ 0)) = -1, prod = b·b·d^(n-1)
        have hsign : σ.sign = -1 := by
          rw [hsw]; exact Equiv.Perm.sign_swap h0.symm
        have hprod : ∏ i, arrowhead n a b d (σ i) i = b * b * d ^ (n - 1) := by
          conv_lhs => rw [hsw]
          exact arrowhead_prod_swap a b d h0
        rw [hsign, hprod]
        simp [Units.smul_def]
      · rw [if_neg hsw]
        -- Classification: if σ 0 ≠ 0 and σ is not swap 0 (σ 0), then prod = 0.
        have hzero : ∃ i, arrowhead n a b d (σ i) i = 0 := by
          by_contra hall
          push_neg at hall
          exact hsw (perm_eq_swap_of_moves_zero_of_nonzero_prod a b d σ h0 hall)
        obtain ⟨i, hi⟩ := hzero
        have hp : ∏ j, arrowhead n a b d (σ j) j = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) hi
        rw [hp, smul_zero]
    -- Now rewrite the filtered sum using hsub.
    rw [Finset.sum_congr rfl hsub]
    -- The sum is now ∑ σ ∈ {σ | σ 0 ≠ 0}, (if σ = swap 0 (σ 0) then c else 0) where c := -1 * (b * b * d^(n-1)).
    -- We show this equals ∑ k ∈ univ.erase 0, c, by bijection σ ↦ σ 0 restricted to swap-permutations.
    set c : R := (-1 : R) * (b * b * d ^ (n - 1)) with hc_def
    -- First, rewrite to sum only over swap-of-zero permutations.
    have step1 : ∑ σ ∈ Finset.univ.filter (fun σ : Perm (Fin (n+1)) => σ 0 ≠ 0),
        (if σ = Equiv.swap 0 (σ 0) then c else 0) =
        ∑ σ ∈ (Finset.univ.filter (fun σ : Perm (Fin (n+1)) => σ 0 ≠ 0)).filter
          (fun σ => σ = Equiv.swap 0 (σ 0)), c :=
      (Finset.sum_filter _ _).symm
    rw [step1]
    -- The filter `{σ | σ 0 ≠ 0 ∧ σ = swap 0 (σ 0)}` is in bijection with `univ.erase 0` via `k ↦ swap 0 k`.
    have hbij : ((Finset.univ.filter (fun σ : Perm (Fin (n+1)) => σ 0 ≠ 0)).filter
        (fun σ => σ = Equiv.swap 0 (σ 0))).card = ((Finset.univ : Finset (Fin (n+1))).erase 0).card := by
      apply Finset.card_bij (fun (σ : Perm (Fin (n+1))) (_ : σ ∈ _) => σ 0)
      · -- σ 0 ∈ univ.erase 0
        intro σ hσ
        rw [Finset.mem_filter, Finset.mem_filter] at hσ
        rw [Finset.mem_erase]
        exact ⟨hσ.1.2, Finset.mem_univ _⟩
      · -- injective
        intro σ₁ hσ₁ σ₂ hσ₂ heq
        rw [Finset.mem_filter] at hσ₁ hσ₂
        have h1 : σ₁ = Equiv.swap 0 (σ₁ 0) := hσ₁.2
        have h2 : σ₂ = Equiv.swap 0 (σ₂ 0) := hσ₂.2
        rw [h1, h2, heq]
      · -- surjective
        intro k hk
        rw [Finset.mem_erase] at hk
        obtain ⟨hk_ne, _⟩ := hk
        refine ⟨Equiv.swap 0 k, ?_, ?_⟩
        · rw [Finset.mem_filter, Finset.mem_filter]
          refine ⟨⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · rw [Equiv.swap_apply_left]; exact hk_ne
          · rw [Equiv.swap_apply_left]
        · rw [Equiv.swap_apply_left]
    -- Now the sum equals (card) · c = n · c = n · (-1 * (b * b * d^(n-1))).
    rw [Finset.sum_const, hbij]
    have hcard_erase : ((Finset.univ : Finset (Fin (n+1))).erase 0).card = n := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      omega
    rw [hcard_erase, hc_def]
    ring
  rw [h_first, h_second]
  ring

/-! ### Q7: determinant of `delta_matrix` -/

/-- The exam's matrix `δ_n` (polynomial-valued). For `n ≥ 1`, the
`(0,0)` entry is `1`, first-row/column off-diagonal entries are `1`,
remaining diagonal entries are `X-1`, and everything else is `0`.

Our version is indexed by `Fin (n+1)`, matching the exam's `Fin n`
of size `n`. The main theorem (`delta_matrix_det`) computes its
determinant under the assumption `n ≥ 1` (so the matrix is at least
`2 × 2`). -/
def delta_matrix (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ[X] :=
  arrowhead n 1 1 (Polynomial.X - 1)

/-- **Q7** (ENS/X 2026 Math A). For `n ≥ 1`, the determinant of the
`(n+1) × (n+1)` polynomial arrowhead matrix `delta_matrix n` factors as

`δₙ(X) = (X - (n+1)) · (X - 1)^(n-1)`.

Writing `N := n + 1` for the matrix size (so `N ≥ 2`), the formula is
`δ_N(X) = (X - N) · (X - 1)^{N-2}` — the exam's statement. -/
theorem delta_matrix_det (n : ℕ) (hn : 1 ≤ n) :
    (delta_matrix n).det =
      (Polynomial.X - Polynomial.C ((n + 1 : ℕ) : ℝ)) * (Polynomial.X - 1) ^ (n - 1) := by
  unfold delta_matrix
  rw [arrowhead_det n hn 1 1 (Polynomial.X - 1)]
  -- 1 * (X - 1)^n - n * 1^2 * (X-1)^(n-1) = (X - (n+1)) * (X - 1)^(n-1)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [Nat.succ_sub_one, pow_succ]
  push_cast [Polynomial.C_eq_natCast, Polynomial.C_add, Polynomial.C_1]
  ring

/-- Variant of `delta_matrix_det` stated with `N = n + 1 ≥ 2`. -/
theorem delta_matrix_det' {N : ℕ} (hN : 2 ≤ N) :
    (delta_matrix (N - 1)).det =
      (Polynomial.X - Polynomial.C (N : ℝ)) * (Polynomial.X - 1) ^ (N - 2) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  show (delta_matrix n).det = _
  rw [delta_matrix_det n hn]
  have h1 : (n + 1 - 2) = n - 1 := by omega
  rw [h1]

/-! ### Q8: characteristic polynomial of `S_matrix` -/

/-- The exam's matrix `S_n` (real-valued): `(0,0)` entry is `n`,
first-row/column off-diagonal entries are `-1`, remaining diagonal
entries are `1`, rest is `0`. (Note: our indexing is `Fin (n+1)`, so
the "natural n" is `n+1`, and the entry at `(0,0)` is `n`, matching
`(matrix-size) - 1`.) -/
def S_matrix (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  arrowhead n (n : ℝ) (-1) 1

/-- **Q8** (ENS/X 2026 Math A). The characteristic polynomial of
`S_matrix n` (a `(n+1) × (n+1)` real matrix, matching the exam's
`S_N` for `N = n + 1`) factors as

`χ_{S_n}(X) = X · (X - (n+1)) · (X - 1)^{n-1}`.

Equivalently for `N ≥ 2`: `χ_{S_N}(X) = X (X - N) (X - 1)^{N-2}`. -/
theorem S_matrix_charpoly (n : ℕ) (hn : 1 ≤ n) :
    (S_matrix n).charpoly =
      Polynomial.X * (Polynomial.X - Polynomial.C ((n + 1 : ℕ) : ℝ)) *
        (Polynomial.X - 1) ^ (n - 1) := by
  -- `charpoly M = det (charmatrix M) = det (scalar X - C.mapMatrix M)`.
  -- charmatrix of S_matrix n equals the arrowhead over ℝ[X] with parameters
  --   (a, b, d) = (X - C n, 1, X - 1).
  -- Then apply arrowhead_det.
  rw [Matrix.charpoly]
  have hcharmat :
      (S_matrix n).charmatrix =
        arrowhead n (Polynomial.X - Polynomial.C (n : ℝ)) 1 (Polynomial.X - 1) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases hi : i = 0
      · subst hi
        rw [Matrix.charmatrix_apply_eq]
        unfold S_matrix
        rw [arrowhead_zero_zero, arrowhead_zero_zero]
      · rw [Matrix.charmatrix_apply_eq]
        unfold S_matrix
        rw [arrowhead_diag_of_ne_zero _ _ _ hi, arrowhead_diag_of_ne_zero _ _ _ hi]
        simp
    · rw [Matrix.charmatrix_apply_ne _ _ _ hij]
      by_cases hi : i = 0
      · subst hi
        have hj_ne : j ≠ 0 := fun h => hij h.symm
        unfold S_matrix
        rw [arrowhead_zero_of_ne _ _ _ hj_ne, arrowhead_zero_of_ne _ _ _ hj_ne]
        simp
      · by_cases hj : j = 0
        · subst hj
          unfold S_matrix
          rw [arrowhead_of_ne_zero _ _ _ hi, arrowhead_of_ne_zero _ _ _ hi]
          simp
        · unfold S_matrix
          rw [arrowhead_off_diag _ _ _ hi hj hij, arrowhead_off_diag _ _ _ hi hj hij]
          simp
  rw [hcharmat, arrowhead_det n hn _ _ _]
  -- Goal: (X - C n) * (X - 1)^n - n * 1^2 * (X - 1)^(n-1) = X * (X - C(n+1)) * (X - 1)^(n-1)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [Nat.succ_sub_one, pow_succ]
  push_cast [Polynomial.C_eq_natCast, Polynomial.C_add, Polynomial.C_1]
  ring

/-- Variant of `S_matrix_charpoly` stated with `N = n + 1 ≥ 2`. -/
theorem S_matrix_charpoly' {N : ℕ} (hN : 2 ≤ N) :
    (S_matrix (N - 1)).charpoly =
      Polynomial.X * (Polynomial.X - Polynomial.C (N : ℝ)) *
        (Polynomial.X - 1) ^ (N - 2) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  show (S_matrix n).charpoly = _
  rw [S_matrix_charpoly n hn]
  have h1 : (n + 1 - 2) = n - 1 := by omega
  rw [h1]

end

end EnsX2026.Matrices.Sn
