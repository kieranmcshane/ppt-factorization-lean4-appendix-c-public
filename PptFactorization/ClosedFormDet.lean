import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Roots
import PptFactorization.Poly

/-!
# Closed-form determinant of the shifted Hankel matrix

## Main Theorem

For every `m ≥ 0` and `λ > 0`:

    det H_m(λ) = λ^{m(m+1)/2} · d_{m+1}(λ)

where:
- `H_m(λ) = (M_{i+j+1}(λ))_{0≤i,j≤m}` is the shifted Hankel matrix
- `d_n` satisfies `d_{n+1} = λ·d_n − λ·d_{n-1}`, `d₀ = 1`, `d₁ = λ`

## Chebyshev interpretation

`d_n(λ) = (√λ)ⁿ · Uₙ(√λ/2)` where `Uₙ` is the Chebyshev polynomial of
the second kind. Substituting:

    det H_m(λ) = (√λ)^{(m+1)²} · U_{m+1}(√λ/2)

## Proof structure (paper reference)

1. Moments `M_k` defined by generating function `(1−λz)C = 1+λz²C²`
2. Monic orthogonal polynomials `Pₙ` via `P_{n+1} = (x−λ)Pₙ − λP_{n-1}`
3. Generating function identity: `Fₙ(z) = λⁿzⁿC(z)^{n+1}`  (induction)
4. Orthogonality `ℒ[Pₙ·xʲ] = 0` for `j<n`, norms `hₙ = λⁿ`
5. Change of basis: `H_m = L·G·Lᵀ`, `G` tridiagonal, `det L = 1`
6. Row factoring: `det G = λ^{m(m+1)/2} · det G'`
7. Cofactor expansion: `det G'` satisfies `d_{n+1} = λ·dₙ − λ·d_{n-1}`
8. Chebyshev substitution: `dₙ = (√λ)ⁿ · Uₙ(√λ/2)` by uniqueness
∂
## Verification

- `native_decide` proofs for `m = 0, 1, 2`
- `#eval` checks for `m = 0, …, 6`
- Numerical cross-check against Chebyshev `Uₙ`

Institut Fourier, Grenoble — Kieran McShane / Cécilia Lancien
-/

noncomputable section

open Finset

namespace ClosedFormDet

-- We work over ℝ. The parameter is called `lam` since `λ` is reserved in Lean 4.
variable (lam : ℝ)

-- ─────────────────────────────────────────────────────────────────────────────
-- §1. Moments
-- ─────────────────────────────────────────────────────────────────────────────

/-- The k-th moment: `M_k(λ) = Σ_{l=0}^{⌊k/2⌋} C(k,2l) · Cat(l) · λ^{k-l}`. -/
def M (k : ℕ) : ℝ :=
  ∑ l ∈ range (k / 2 + 1),
    (↑(Nat.choose k (2 * l) * catalan l) : ℝ) * lam ^ (k - l)

-- ─────────────────────────────────────────────────────────────────────────────
-- §1b. Generating function of the moments
-- ─────────────────────────────────────────────────────────────────────────────

/-- The generating function `C(z) = Σ_k M_k(λ) z^k`. -/
def genC : PowerSeries ℝ := PowerSeries.mk (fun k => M lam k)

@[simp] lemma genC_coeff (k : ℕ) :
    PowerSeries.coeff k (genC lam) = M lam k :=
  PowerSeries.coeff_mk k _

/-- `M_0(λ) = 1`. -/
@[simp] lemma M_zero : M lam 0 = 1 := by simp [M]

/-- `M_1(λ) = λ`. -/
@[simp] lemma M_one : M lam 1 = lam := by simp [M]

/-- Upper-index Vandermonde (Chu-Vandermonde):
    `Σ (a,b) ∈ antidiag n, C(a,r)·C(b,s) = C(n+1, r+s+1)`. -/
private theorem choose_upper_sum (r : ℕ) : ∀ n s,
    ∑ p ∈ antidiagonal n, p.1.choose r * p.2.choose s =
    (n + 1).choose (r + s + 1) := by
  intro n
  induction n with
  | zero =>
    intro s; simp only [antidiagonal_zero, sum_singleton]
    rcases r with _ | r
    · rcases s with _ | s
      · simp
      · simp [Nat.choose_zero_succ, Nat.choose_eq_zero_of_lt (by omega : 1 < s + 2)]
    · simp [Nat.choose_zero_succ, Nat.choose_eq_zero_of_lt (by omega : 1 < r + 1 + s + 1)]
  | succ n ih =>
    intro s
    rw [Nat.sum_antidiagonal_succ']
    cases s with
    | zero =>
      simp only [Nat.choose_zero_right, mul_one]
      have h := ih 0; simp only [Nat.choose_zero_right, mul_one] at h
      rw [h]; exact (Nat.choose_succ_succ (n + 1) r).symm
    | succ s =>
      simp only [Nat.choose_zero_succ, mul_zero, zero_add,
        Nat.choose_succ_succ, mul_add, sum_add_distrib, ih s, ih (s + 1)]
      exact (Nat.choose_succ_succ (n + 1) (r + s + 1)).symm

/-- Extension of `M` sum to a larger range (extra terms vanish since `C(k,2l)=0` for `2l>k`). -/
private lemma M_extend (k N : ℕ) (hN : k / 2 + 1 ≤ N) :
    M lam k = ∑ l ∈ range N,
      (↑(Nat.choose k (2 * l) * catalan l) : ℝ) * lam ^ (k - l) := by
  apply sum_subset (range_mono hN)
  intro l hl1 hl2
  simp only [mem_range] at hl1 hl2; push_neg at hl2
  simp [Nat.choose_eq_zero_of_lt (show k < 2 * l by omega)]

/-- Pascal step: `C(n, k+1) − C(n−1, k+1) = C(n−1, k)` for `n ≥ 1`. -/
private lemma choose_sub_pascal (n k : ℕ) (hn : 1 ≤ n) :
    n.choose (k + 1) - (n - 1).choose (k + 1) = (n - 1).choose k := by
  conv_lhs => rw [show n = (n - 1) + 1 by omega]
  rw [Nat.choose_succ_succ]
  exact Nat.add_sub_cancel_right ..

/-- LHS of the moment recurrence reduces to the target sum. -/
private lemma moment_lhs_eq (n : ℕ) (hn : 2 ≤ n) :
    M lam n - lam * M lam (n - 1) =
    ∑ l ∈ range (n / 2),
      (↑((n - 1).choose (2 * l + 1) * catalan (l + 1)) : ℝ) * lam ^ (n - 1 - l) := by
  -- Step 1: λ·M(n-1) = Σ_{l<n/2+1} C(n-1,2l)·Cat(l)·λ^{n-l}
  have hA : lam * M lam (n - 1) =
      ∑ l ∈ range (n / 2 + 1),
        (↑((n - 1).choose (2 * l) * catalan l) : ℝ) * lam ^ (n - l) := by
    simp only [M, Finset.mul_sum]
    have hab : ∀ l ∈ range ((n - 1) / 2 + 1),
        lam * ((↑((n - 1).choose (2 * l) * catalan l) : ℝ) * lam ^ ((n - 1) - l)) =
        (↑((n - 1).choose (2 * l) * catalan l) : ℝ) * lam ^ (n - l) := by
      intro l hl; simp only [mem_range] at hl
      have hln : l ≤ n - 1 := by have := Nat.div_le_self (n - 1) 2; omega
      have hexp : (n - 1) - l + 1 = n - l := by omega
      rw [← hexp]; ring
    rw [sum_congr rfl hab]
    exact sum_subset (range_mono (Nat.add_le_add_right
      (Nat.div_le_div_right (Nat.sub_le n 1)) 1))
      (fun l hl1 hl2 => by
        simp only [mem_range] at hl1 hl2; push_neg at hl2
        have := Nat.div_add_mod (n - 1) 2
        have := Nat.mod_lt (n - 1) (show 0 < 2 by omega)
        simp [Nat.choose_eq_zero_of_lt (show n - 1 < 2 * l by omega)])
  -- Step 2: Combine M(n) - λ·M(n-1) into a single sum
  rw [hA]; simp only [M]
  rw [← Finset.sum_sub_distrib]
  -- Step 3: Split off l=0 (vanishes) and apply Pascal for l≥1
  rw [sum_range_succ']
  simp only [show 2 * 0 = 0 from rfl, Nat.choose_zero_right, catalan_zero,
    Nat.cast_one, one_mul, Nat.sub_zero, sub_self, add_zero]
  apply sum_congr rfl; intro l hl; simp only [mem_range] at hl
  have hnd := Nat.div_le_self n 2
  rw [show 2 * (l + 1) = 2 * l + 2 from by ring,
      show n - (l + 1) = n - 1 - l from by omega, ← sub_mul]
  congr 1
  rw [← Nat.cast_sub (Nat.mul_le_mul_right _
    (Nat.choose_le_choose _ (show n - 1 ≤ n by omega)))]
  congr 1
  rw [← Nat.sub_mul, choose_sub_pascal n (2 * l + 1) (by omega)]

/-- Expand `M(a)·M(b)` with both sums extended to `range N`. -/
private lemma expand_M_prod (a b N : ℕ) (ha : a / 2 + 1 ≤ N) (hb : b / 2 + 1 ≤ N) :
    M lam a * M lam b =
    ∑ α ∈ range N, ∑ β ∈ range N,
      (↑(a.choose (2*α) * catalan α * (b.choose (2*β) * catalan β)) : ℝ) *
      lam ^ (a - α + (b - β)) := by
  rw [M_extend lam a N ha, M_extend lam b N hb, sum_mul]
  apply sum_congr rfl; intro α _; rw [mul_sum]
  apply sum_congr rfl; intro β _; push_cast; ring

/-- Vandermonde over ℝ. -/
private lemma choose_upper_sum_real (r s m : ℕ) :
    (∑ p ∈ antidiagonal m, (↑(p.1.choose r) : ℝ) * ↑(p.2.choose s)) =
    ↑((m + 1).choose (r + s + 1)) := by
  exact_mod_cast choose_upper_sum r m s

/-- RHS of the moment recurrence reduces to the same target sum.
    *Proof.*  Expand `M(a)·M(b)` as double sums, extend ranges to `range n`,
    swap via `sum_comm`, apply `choose_upper_sum` (Vandermonde), group by
    `l = α+β` via `sum_fiberwise_of_maps_to`, apply `catalan_succ'`. -/
private lemma moment_rhs_eq (n : ℕ) (hn : 2 ≤ n) :
    lam * ∑ p ∈ antidiagonal (n - 2), M lam p.1 * M lam p.2 =
    ∑ l ∈ range (n / 2),
      (↑((n - 1).choose (2 * l + 1) * catalan (l + 1)) : ℝ) * lam ^ (n - 1 - l) := by
  set m := n - 2
  have hmn : m + 2 = n := by omega
  have hmn1 : m + 1 = n - 1 := by omega
  -- Step 1: Pull lam inside, expand M products to range n
  rw [Finset.mul_sum]
  have hstep1 : ∀ p ∈ antidiagonal m,
      lam * (M lam p.1 * M lam p.2) =
      ∑ α ∈ range n, ∑ β ∈ range n,
        (↑(p.1.choose (2*α) * catalan α * (p.2.choose (2*β) * catalan β)) : ℝ) *
        lam ^ (n - 1 - (α + β)) := by
    intro p hp
    have hab := mem_antidiagonal.mp hp
    rw [expand_M_prod lam p.1 p.2 n (by omega) (by omega), Finset.mul_sum]
    apply sum_congr rfl; intro α hα; rw [Finset.mul_sum]
    apply sum_congr rfl; intro β hβ
    simp only [mem_range] at hα hβ
    by_cases hα' : 2 * α ≤ p.1
    · by_cases hβ' : 2 * β ≤ p.2
      · have : p.1 - α + (p.2 - β) = n - 2 - (α + β) := by omega
        rw [this, ← show n - 2 - (α + β) + 1 = n - 1 - (α + β) from by omega]; ring
      · simp [Nat.choose_eq_zero_of_lt (show p.2 < 2 * β by omega)]
    · simp [Nat.choose_eq_zero_of_lt (show p.1 < 2 * α by omega)]
  rw [sum_congr rfl hstep1]
  -- Step 2: Swap sums — antidiag goes inside α, β
  rw [sum_comm]; simp_rw [sum_comm (s := antidiagonal m)]
  -- Step 3: Factor out constants, apply Vandermonde
  have hstep3 : ∀ α ∈ range n, ∀ β ∈ range n,
      ∑ p ∈ antidiagonal m,
        (↑(p.1.choose (2*α) * catalan α * (p.2.choose (2*β) * catalan β)) : ℝ) *
        lam ^ (n - 1 - (α + β)) =
      (↑(catalan α * catalan β * (n - 1).choose (2 * α + 2 * β + 1)) : ℝ) *
        lam ^ (n - 1 - (α + β)) := by
    intro α _ β _
    rw [← Finset.sum_mul]; congr 1
    have hv := choose_upper_sum_real (2*α) (2*β) m
    rw [hmn1] at hv
    simp_rw [show ∀ p : ℕ × ℕ, (↑(p.1.choose (2*α) * catalan α *
        (p.2.choose (2*β) * catalan β)) : ℝ) =
      ↑(catalan α) * ↑(catalan β) * (↑(p.1.choose (2*α)) * ↑(p.2.choose (2*β)))
      from fun p => by push_cast; ring]
    rw [← Finset.mul_sum, hv]; push_cast; ring
  simp_rw [sum_congr rfl (fun α hα => sum_congr rfl (fun β hβ => hstep3 α hα β hβ))]
  -- Step 4: Group by l = α+β, apply Catalan, truncate range
  rw [← Finset.sum_product']
  rw [← sum_fiberwise_of_maps_to (g := fun p : ℕ × ℕ => p.1 + p.2)
    (t := range (2 * n))
    (fun p hp => by simp only [mem_product, mem_range] at hp ⊢; omega)]
  -- Factor out C(n-1,2l+1)*lam^{n-1-l} from each fiber
  have hstep4a : ∀ l ∈ range (2 * n),
      ∑ p ∈ (range n ×ˢ range n).filter (fun p => p.1 + p.2 = l),
        (↑(catalan p.1 * catalan p.2 * (n - 1).choose (2 * p.1 + 2 * p.2 + 1)) : ℝ) *
        lam ^ (n - 1 - (p.1 + p.2)) =
      (↑((n - 1).choose (2 * l + 1)) : ℝ) * lam ^ (n - 1 - l) *
        ∑ p ∈ (range n ×ˢ range n).filter (fun p => p.1 + p.2 = l),
          (↑(catalan p.1) : ℝ) * ↑(catalan p.2) := by
    intro l _; rw [Finset.mul_sum]
    apply sum_congr rfl; intro p hp
    simp only [mem_filter] at hp
    have : 2 * p.1 + 2 * p.2 + 1 = 2 * l + 1 := by omega
    rw [hp.2, this]; push_cast; ring
  rw [sum_congr rfl hstep4a]
  -- Replace filter with antidiag and apply Catalan recurrence
  have hfilt : ∀ l, l < n →
      (range n ×ˢ range n).filter (fun p => p.1 + p.2 = l) = antidiagonal l := by
    intro l hl; ext p; simp only [mem_filter, mem_product, mem_range, mem_antidiagonal]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨⟨by omega, by omega⟩, h⟩⟩
  have hstep4b : ∀ l ∈ range (2 * n),
      (↑((n - 1).choose (2 * l + 1)) : ℝ) * lam ^ (n - 1 - l) *
        ∑ p ∈ (range n ×ˢ range n).filter (fun p => p.1 + p.2 = l),
          (↑(catalan p.1) : ℝ) * ↑(catalan p.2) =
      (↑((n - 1).choose (2 * l + 1) * catalan (l + 1)) : ℝ) * lam ^ (n - 1 - l) := by
    intro l hl; simp only [mem_range] at hl
    by_cases hl' : l < n
    · rw [hfilt l hl']
      have hcat : (∑ p ∈ antidiagonal l, (↑(catalan p.1) : ℝ) * ↑(catalan p.2)) =
          ↑(catalan (l + 1)) := by rw [catalan_succ']; norm_cast
      rw [hcat]; push_cast; ring
    · simp [Nat.choose_eq_zero_of_lt (show n - 1 < 2 * l + 1 by omega)]
  rw [sum_congr rfl hstep4b]
  -- Truncate range from 2*n to n/2 (extras vanish)
  symm; apply sum_subset (range_mono (by omega : n / 2 ≤ 2 * n))
  intro l hl1 hl2; simp only [mem_range] at hl1 hl2; push_neg at hl2
  simp [Nat.choose_eq_zero_of_lt (show n - 1 < 2 * l + 1 by omega)]

/-- Core coefficient identity: `M_n − λ·M_{n−1} = λ·Σ M_j·M_{n−2−j}` for `n ≥ 2`.
    *Proof.* Both sides expand to `Σ_{l} C(n−1,2l+1)·Cat(l+1)·λ^{n−l−1}`.
    - **LHS→target:** Pascal gives `C(n,2l+2)−C(n−1,2l+2) = C(n−1,2l+1)`.
    - **RHS→target:** Expand `M_j·M_{n−2−j}`, swap sums, apply `choose_upper_sum`
      (Chu-Vandermonde) to collapse `Σ_j C(j,2α)·C(n−2−j,2β) = C(n−1,2(α+β)+1)`,
      then apply `catalan_succ'` to collect `Cat(l+1) = Σ Cat(α)·Cat(β)`. -/
lemma moment_functional_coeff (n : ℕ) (hn : 2 ≤ n) :
    M lam n - lam * M lam (n - 1) =
    lam * ∑ p ∈ Finset.antidiagonal (n - 2), M lam p.1 * M lam p.2 :=
  (moment_lhs_eq lam n hn).trans (moment_rhs_eq lam n hn).symm

/-- **Generating function equation.**
    `(1 − λz)·C(z) = 1 + λz²·C(z)²`. -/
private lemma genC_rearrange :
    (1 - PowerSeries.C lam * PowerSeries.X) * genC lam =
    genC lam - PowerSeries.C lam * (PowerSeries.X * genC lam) :=
  (sub_mul ..).trans (congr_arg₂ (· - ·) (one_mul _) (mul_assoc ..))

private lemma genC_rhs_rearrange :
    PowerSeries.C lam * PowerSeries.X ^ 2 * (genC lam) ^ 2 =
    PowerSeries.C lam * (PowerSeries.X ^ 2 * (genC lam * genC lam)) := by
  rw [sq (genC lam)]; exact mul_assoc ..

private lemma genC_lhs_coeff_zero :
    PowerSeries.coeff 0 ((1 - PowerSeries.C lam * PowerSeries.X) * genC lam) = 1 := by
  rw [genC_rearrange, map_sub, PowerSeries.coeff_C_mul, genC_coeff, M_zero]
  simp [PowerSeries.coeff_mul, antidiagonal_zero]

private lemma genC_lhs_coeff_succ (n : ℕ) :
    PowerSeries.coeff (n + 1) ((1 - PowerSeries.C lam * PowerSeries.X) * genC lam) =
    M lam (n + 1) - lam * M lam n := by
  rw [genC_rearrange, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
    genC_coeff, genC_coeff]

private lemma genC_rhs_coeff_zero :
    PowerSeries.coeff 0 (1 + PowerSeries.C lam * PowerSeries.X ^ 2 * (genC lam) ^ 2) = 1 := by
  rw [map_add, PowerSeries.coeff_one, if_pos rfl, genC_rhs_rearrange,
    PowerSeries.coeff_C_mul]
  simp [PowerSeries.coeff_mul, antidiagonal_zero]

private lemma genC_rhs_coeff_one :
    PowerSeries.coeff 1 (1 + PowerSeries.C lam * PowerSeries.X ^ 2 * (genC lam) ^ 2) = 0 := by
  rw [map_add, PowerSeries.coeff_one, if_neg (by omega : 1 ≠ 0), zero_add,
    genC_rhs_rearrange, PowerSeries.coeff_C_mul]
  suffices PowerSeries.coeff 1 (PowerSeries.X ^ 2 * (genC lam * genC lam)) = 0 by
    rw [this, mul_zero]
  rw [PowerSeries.coeff_mul]
  apply sum_eq_zero; intro p hp
  simp only [PowerSeries.coeff_X_pow]
  split <;> simp
  · exact absurd (mem_antidiagonal.mp hp) (by omega)

private lemma genC_rhs_coeff_succ_succ (n : ℕ) :
    PowerSeries.coeff (n + 2) (1 + PowerSeries.C lam * PowerSeries.X ^ 2 * (genC lam) ^ 2) =
    lam * ∑ p ∈ Finset.antidiagonal n, M lam p.1 * M lam p.2 := by
  rw [map_add, PowerSeries.coeff_one, if_neg (by omega : n + 2 ≠ 0), zero_add,
    genC_rhs_rearrange, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul,
    PowerSeries.coeff_mul]
  congr 1; apply sum_congr rfl; intro p _; simp [genC_coeff]

/-- **Generating function equation.**
    `(1 − λz)·C(z) = 1 + λz²·C(z)²`. -/
theorem genC_functional_eq :
    (1 - PowerSeries.C lam * PowerSeries.X) * genC lam =
    1 + PowerSeries.C lam * PowerSeries.X ^ 2 * (genC lam) ^ 2 := by
  ext n
  match n with
  | 0 => rw [genC_lhs_coeff_zero, genC_rhs_coeff_zero]
  | 1 => rw [genC_lhs_coeff_succ, genC_rhs_coeff_one, M_one, M_zero]; ring
  | n + 2 =>
    rw [genC_lhs_coeff_succ, genC_rhs_coeff_succ_succ]
    exact moment_functional_coeff lam (n + 2) (by omega)

-- ─────────────────────────────────────────────────────────────────────────────
-- §2. Linear functional
-- ─────────────────────────────────────────────────────────────────────────────

/-- The linear functional `ℒ[f] = Σ_k f_k · M_k`. -/
def L (f : Polynomial ℝ) : ℝ :=
  f.sum (fun k a => a * M lam k)

-- ─────────────────────────────────────────────────────────────────────────────
-- §3. Orthogonal polynomials
-- ─────────────────────────────────────────────────────────────────────────────

/-- Monic orthogonal polynomials: `P_{n+1} = (x − λ)Pₙ − λP_{n-1}`. -/
def P : ℕ → Polynomial ℝ
  | 0 => 1
  | 1 => Polynomial.X - Polynomial.C lam
  | (n + 2) =>
    (Polynomial.X - Polynomial.C lam) * P (n + 1) -
    Polynomial.C lam * P n

-- ─────────────────────────────────────────────────────────────────────────────
-- §4. Generating function Fₙ and orthogonality
-- ─────────────────────────────────────────────────────────────────────────────

/-- `Fₙ(z) = ∑_k ℒ[Pₙ · xᵏ] zᵏ` — generating function encoding the linear
    functional applied to `Pₙ · xᵏ`. -/
def F (n : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk (fun k => L lam (P lam n * Polynomial.X ^ k))

@[simp] lemma F_coeff (n k : ℕ) :
    PowerSeries.coeff k (F lam n) = L lam (P lam n * Polynomial.X ^ k) :=
  PowerSeries.coeff_mk k _

/-- Linearity of `ℒ`: `ℒ[monomial k a] = a · M_k`. -/
private lemma L_monomial (k : ℕ) (a : ℝ) : L lam (Polynomial.monomial k a) = a * M lam k :=
  Polynomial.sum_monomial_index a _ (zero_mul _)

/-- `ℒ[xᵏ] = M_k`. -/
lemma L_X_pow (k : ℕ) : L lam (Polynomial.X ^ k) = M lam k := by
  rw [Polynomial.X_pow_eq_monomial, L_monomial, one_mul]

private lemma L_add (f g : Polynomial ℝ) : L lam (f + g) = L lam f + L lam g :=
  Polynomial.sum_add_index f g _ (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

private lemma L_C_mul (c : ℝ) (f : Polynomial ℝ) : L lam (Polynomial.C c * f) = c * L lam f := by
  unfold L; rw [Polynomial.C_mul', Polynomial.sum_smul_index _ _ _ (fun _ => zero_mul _)]
  simp_rw [mul_assoc]; rw [← smul_eq_mul, Polynomial.smul_sum]; simp [smul_eq_mul]

private lemma L_sub (f g : Polynomial ℝ) : L lam (f - g) = L lam f - L lam g := by
  have : f - g = f + Polynomial.C (-1) * g := by simp [neg_mul, sub_eq_add_neg]
  rw [this, L_add, L_C_mul]; ring

/-- Recurrence for `ℒ[P_{n+2} · xᵏ]` from the OP three-term recurrence. -/
private lemma L_P_rec (n k : ℕ) :
    L lam (P lam (n + 2) * Polynomial.X ^ k) =
    L lam (P lam (n + 1) * Polynomial.X ^ (k + 1)) -
    lam * L lam (P lam (n + 1) * Polynomial.X ^ k) -
    lam * L lam (P lam n * Polynomial.X ^ k) := by
  show L lam (((Polynomial.X - Polynomial.C lam) * P lam (n + 1) -
    Polynomial.C lam * P lam n) * Polynomial.X ^ k) = _
  rw [sub_mul, L_sub,
    show (Polynomial.X - Polynomial.C lam) * P lam (n + 1) * Polynomial.X ^ k =
      Polynomial.X * P lam (n + 1) * Polynomial.X ^ k -
      Polynomial.C lam * P lam (n + 1) * Polynomial.X ^ k from by ring,
    L_sub,
    show Polynomial.X * P lam (n + 1) * Polynomial.X ^ k =
      P lam (n + 1) * Polynomial.X ^ (k + 1) from by
      rw [mul_comm Polynomial.X, mul_assoc]; congr 1; rw [mul_comm, ← pow_succ],
    show Polynomial.C lam * P lam (n + 1) * Polynomial.X ^ k =
      Polynomial.C lam * (P lam (n + 1) * Polynomial.X ^ k) from mul_assoc ..,
    show Polynomial.C lam * P lam n * Polynomial.X ^ k =
      Polynomial.C lam * (P lam n * Polynomial.X ^ k) from mul_assoc ..,
    L_C_mul, L_C_mul]

/-- Workaround for PowerSeries `One` instance diamond: `C(1) · X⁰ · f = f`. -/
private lemma PS_C_one_mul_X_pow_zero (f : PowerSeries ℝ) :
    PowerSeries.C (1 : ℝ) * PowerSeries.X ^ (0 : ℕ) * f = f :=
  (congr_arg (· * f)
    ((congr_arg (PowerSeries.C 1 * ·) (pow_zero _)).trans
      ((mul_one _).trans (map_one _)))).trans (one_mul f)

/-- `F₀ = C`. -/
private lemma F_eq_zero : F lam 0 = genC lam := by
  ext k; simp [F, P, L_X_pow, genC]

/-- `(1−λX)·C^{n+2} = C^{n+1} + λX²·C^{n+3}`, from the functional equation. -/
private lemma genC_pow_identity (n : ℕ) :
    (1 - PowerSeries.C lam * PowerSeries.X) * genC lam ^ (n + 2) =
    genC lam ^ (n + 1) +
      PowerSeries.C lam * PowerSeries.X ^ 2 * genC lam ^ (n + 3) :=
  calc (1 - PowerSeries.C lam * PowerSeries.X) * genC lam ^ (n + 2)
      = (1 - PowerSeries.C lam * PowerSeries.X) *
          (genC lam * genC lam ^ (n + 1)) :=
        congr_arg _ ((pow_succ ..).trans (mul_comm ..))
    _ = ((1 - PowerSeries.C lam * PowerSeries.X) * genC lam) *
          genC lam ^ (n + 1) :=
        (mul_assoc ..).symm
    _ = (1 + PowerSeries.C lam * PowerSeries.X ^ 2 * genC lam ^ 2) *
          genC lam ^ (n + 1) :=
        congr_arg (· * _) (genC_functional_eq lam)
    _ = genC lam ^ (n + 1) + PowerSeries.C lam * PowerSeries.X ^ 2 *
          genC lam ^ 2 * genC lam ^ (n + 1) :=
        ((mul_comm _ (genC lam ^ (n + 1))).trans ((mul_add ..).trans
          (congr_arg₂ (· + ·) ((mul_comm ..).trans (one_mul _)) (mul_comm ..))))
    _ = genC lam ^ (n + 1) + PowerSeries.C lam * PowerSeries.X ^ 2 *
          (genC lam ^ 2 * genC lam ^ (n + 1)) :=
        congr_arg (genC lam ^ (n + 1) + ·) (mul_assoc ..)
    _ = genC lam ^ (n + 1) + PowerSeries.C lam * PowerSeries.X ^ 2 *
          genC lam ^ (n + 3) :=
        congr_arg (genC lam ^ (n + 1) + PowerSeries.C lam * PowerSeries.X ^ 2 * ·)
          ((pow_add ..).symm.trans (congr_arg _ (by omega : 2 + (n + 1) = n + 3)))

/-- Coefficient recurrence from `genC_pow_identity`:
    `coeff(k+1)(C^{m+2}) − λ·coeff_k(C^{m+2}) − coeff(k+1)(C^{m+1})
     = coeff(k+1)(C(λ)·X²·C^{m+3})`. -/
private lemma genC_coeff_rec (m k : ℕ) :
    PowerSeries.coeff (k + 1) (genC lam ^ (m + 2)) -
      lam * PowerSeries.coeff k (genC lam ^ (m + 2)) -
      PowerSeries.coeff (k + 1) (genC lam ^ (m + 1)) =
    PowerSeries.coeff (k + 1)
      (PowerSeries.C lam * PowerSeries.X ^ 2 * genC lam ^ (m + 3)) := by
  have h := congr_arg (PowerSeries.coeff (k + 1)) (genC_pow_identity lam m)
  rw [show (1 - PowerSeries.C lam * PowerSeries.X) * genC lam ^ (m + 2) =
    genC lam ^ (m + 2) - PowerSeries.C lam * (PowerSeries.X * genC lam ^ (m + 2))
    from (sub_mul ..).trans (congr_arg₂ (· - ·) (one_mul _) (mul_assoc ..))] at h
  simp only [map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul] at h
  linarith

/-- **Key identity.** `Fₙ(z) = λⁿ · zⁿ · C(z)^{n+1}`.
    *Proof.* Pair induction on `n`.  Base `F₀ = C` is direct.
    The recurrence `ℒ[P_{n+2}·xᵏ] = ℒ[P_{n+1}·xᵏ⁺¹] − λℒ[P_{n+1}·xᵏ] − λℒ[Pₙ·xᵏ]`
    translates via IH to a coefficient identity closed by `genC_functional_eq`. -/
theorem F_eq (n : ℕ) :
    F lam n = PowerSeries.C (lam ^ n) * PowerSeries.X ^ n *
      genC lam ^ (n + 1) := by
  suffices h : ∀ m, F lam m = PowerSeries.C (lam ^ m) * PowerSeries.X ^ m *
      genC lam ^ (m + 1) ∧ F lam (m + 1) = PowerSeries.C (lam ^ (m + 1)) *
      PowerSeries.X ^ (m + 1) * genC lam ^ (m + 2) from (h n).1
  intro m; induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · -- F₀ = C = C(1)·X⁰·C¹
      rw [F_eq_zero]; simp only [show (0:ℕ)+1=1 from rfl]; rw [pow_one, pow_zero (M := ℝ)]
      exact (PS_C_one_mul_X_pow_zero (genC lam)).symm
    · -- F₁ = λXC²
      ext k; simp only [F, PowerSeries.coeff_mk, P]
      rw [sub_mul, L_sub,
        show Polynomial.X * Polynomial.X ^ k = Polynomial.X ^ (k + 1) from by
          rw [mul_comm, ← pow_succ],
        show Polynomial.C lam * Polynomial.X ^ k =
          Polynomial.C lam * (Polynomial.X ^ k) from rfl,
        L_C_mul, L_X_pow, L_X_pow]
      rw [show genC lam ^ 2 = genC lam * genC lam from sq _]
      rw [show PowerSeries.C (lam ^ 1) * PowerSeries.X ^ 1 * (genC lam * genC lam) =
        PowerSeries.C lam * (PowerSeries.X * (genC lam * genC lam)) from by
          rw [pow_one, pow_one]; exact mul_assoc ..,
        PowerSeries.coeff_C_mul]
      match k with
      | 0 =>
        simp [M_one, M_zero, PowerSeries.coeff_mul, antidiagonal_zero, PowerSeries.coeff_X]
      | k + 1 =>
        rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mul]
        have := moment_functional_coeff lam (k + 2) (by omega)
        simp only [show k + 2 - 1 = k + 1 from rfl, show k + 2 - 2 = k from rfl] at this
        convert this using 1
        congr 1; apply sum_congr rfl; intro p _; simp [genC_coeff]
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    -- F(m+2) = T(m+2)
    ext k; simp only [F, PowerSeries.coeff_mk]
    rw [L_P_rec]
    have h1 := congr_arg (PowerSeries.coeff (k + 1)) ih.2
    have h2 := congr_arg (PowerSeries.coeff k) ih.2
    have h0 := congr_arg (PowerSeries.coeff k) ih.1
    simp only [F, PowerSeries.coeff_mk] at h1 h2 h0
    rw [h1, h2, h0]
    -- Coefficient identity from genC_coeff_rec + algebra
    -- Extract C(lam^n) via mul_assoc + coeff_C_mul
    have Tc : ∀ (n j : ℕ), PowerSeries.coeff j (PowerSeries.C (lam ^ n) *
        PowerSeries.X ^ n * genC lam ^ (n + 1)) =
        lam ^ n * PowerSeries.coeff j (PowerSeries.X ^ n * genC lam ^ (n + 1)) :=
      fun n j => (congr_arg (PowerSeries.coeff j) (mul_assoc ..)).trans
        (PowerSeries.coeff_C_mul ..)
    rw [Tc, Tc, Tc, Tc, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul',
      PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul', Nat.succ_sub_succ]
    by_cases h4 : m + 2 ≤ k
    · simp only [show m+1 ≤ k+1 from by omega, show m+1 ≤ k from by omega,
        show m ≤ k from by omega, h4, ↓reduceIte]
      have h := genC_coeff_rec lam m (k - m - 1)
      rw [show k-m-1+1 = k-m from by omega,
        show PowerSeries.C lam * PowerSeries.X ^ 2 * genC lam ^ (m+3) =
          PowerSeries.C lam * (PowerSeries.X ^ 2 * genC lam ^ (m+3)) from mul_assoc ..,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
        if_pos (show 2 ≤ k-m from by omega), show k-m-2 = k-(m+2) from by omega,
        show k-m-1 = k-(m+1) from by omega] at h
      have key := congr_arg (lam ^ (m+1) * ·) h
      simp only [mul_sub] at key; ring_nf at key ⊢; linarith
    · by_cases h_mk : m ≤ k
      · simp only [show m+1 ≤ k+1 from by omega, show ¬(m+2 ≤ k) from h4,
          h_mk, ↓reduceIte, mul_zero]
        by_cases h2 : m + 1 ≤ k
        · have hkm : k = m+1 := by omega
          subst hkm
          simp only [le_refl, ↓reduceIte, Nat.sub_self, show m+1-m = 1 from by omega]
          have h := genC_coeff_rec lam m 0
          rw [show (0:ℕ)+1=1 from rfl,
            show PowerSeries.C lam * PowerSeries.X ^ 2 * genC lam ^ (m+3) =
              PowerSeries.C lam * (PowerSeries.X ^ 2 * genC lam ^ (m+3)) from mul_assoc ..,
            PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
            if_neg (show ¬(2 ≤ (1:ℕ)) from by omega), mul_zero] at h
          have key := congr_arg (lam ^ (m+1) * ·) h
          simp only [mul_sub, mul_zero] at key; ring_nf at key ⊢; linarith
        · -- k = m: coeff_0 terms cancel
          simp only [show ¬(m+1 ≤ k) from h2, ↓reduceIte, mul_zero, sub_zero]
          have hc : ∀ n, PowerSeries.coeff 0 (genC lam ^ n) = 1 := fun n => by
            rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
              show PowerSeries.constantCoeff (genC lam) = 1 from by
                rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, genC_coeff, M_zero],
              one_pow]
          rw [show k = m from by omega, Nat.sub_self, hc, hc]; ring
      · simp only [show ¬(m+1 ≤ k+1) from by omega, show ¬(m+1 ≤ k) from by omega,
          show ¬(m ≤ k) from h_mk, show ¬(m+2 ≤ k) from h4, ↓reduceIte, mul_zero, sub_zero]

/-- Coefficient of `zʲ` in `Xⁿ · f` vanishes for `j < n`. -/
private lemma coeff_X_pow_mul_eq_zero {R : Type*} [Semiring R]
    (f : PowerSeries R) (n j : ℕ) (hj : j < n) :
    PowerSeries.coeff j (PowerSeries.X ^ n * f) = 0 := by
  rw [PowerSeries.coeff_mul]
  apply sum_eq_zero; intro p hp
  simp only [PowerSeries.coeff_X_pow]
  split
  · exact absurd (mem_antidiagonal.mp hp) (by omega)
  · simp

/-- **Orthogonality.** `ℒ[Pₙ · xʲ] = 0` for `j < n`.
    *Proof.* The `j`-th coefficient of `Fₙ = λⁿzⁿC^{n+1}` vanishes for `j < n`
    since `zⁿ` divides `Fₙ`. -/
theorem orthogonality (n j : ℕ) (hj : j < n) :
    L lam (P lam n * Polynomial.X ^ j) = 0 := by
  have h := congr_arg (PowerSeries.coeff j) (F_eq lam n)
  simp only [F_coeff] at h; rw [h]
  have hassoc : PowerSeries.C (lam ^ n) * PowerSeries.X ^ n * genC lam ^ (n + 1) =
    PowerSeries.C (lam ^ n) * (PowerSeries.X ^ n * genC lam ^ (n + 1)) := mul_assoc ..
  rw [hassoc, PowerSeries.coeff_C_mul]
  exact mul_eq_zero_of_right _ (coeff_X_pow_mul_eq_zero _ n j hj)

/-- `ℒ[Pₙ · xⁿ] = λⁿ` — the `n`-th coefficient of `Fₙ`.
    *Proof.* Coefficient of `zⁿ` in `λⁿzⁿC^{n+1}` is `λⁿ · C(0)^{n+1} = λⁿ`. -/
theorem L_P_X_pow_n (n : ℕ) :
    L lam (P lam n * Polynomial.X ^ n) = lam ^ n := by
  have h := congr_arg (PowerSeries.coeff n) (F_eq lam n)
  simp only [F_coeff] at h; rw [h]
  have hassoc : PowerSeries.C (lam ^ n) * PowerSeries.X ^ n * genC lam ^ (n + 1) =
    PowerSeries.C (lam ^ n) * (PowerSeries.X ^ n * genC lam ^ (n + 1)) := mul_assoc ..
  rw [hassoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  simp only [le_refl, ↓reduceIte, Nat.sub_self]
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
    show PowerSeries.constantCoeff (genC lam) = 1 from by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, genC_coeff, M_zero],
    one_pow, mul_one]

/-- `Pₙ` is monic of degree `n`. -/
private lemma P_monic_degree : ∀ n, (P lam n).Monic ∧ (P lam n).natDegree = n := by
  intro n; induction n using Nat.strongRecOn with | _ n ih =>
  match n with
  | 0 => exact ⟨Polynomial.monic_one, Polynomial.natDegree_one⟩
  | 1 => exact ⟨Polynomial.monic_X_sub_C lam, Polynomial.natDegree_X_sub_C lam⟩
  | n + 2 =>
    have hm1 := ih (n + 1) (by omega); have hm0 := ih n (by omega)
    have hmul := (Polynomial.monic_X_sub_C lam).mul hm1.1
    have hdm : ((Polynomial.X - Polynomial.C lam) * P lam (n+1)).natDegree = n+2 := by
      rw [Polynomial.natDegree_mul (Polynomial.monic_X_sub_C lam).ne_zero hm1.1.ne_zero,
        Polynomial.natDegree_X_sub_C, hm1.2]; omega
    have hdl : (Polynomial.C lam * P lam n).natDegree ≤ n :=
      Polynomial.natDegree_mul_le.trans (by rw [Polynomial.natDegree_C, hm0.2]; omega)
    have hlt : (Polynomial.C lam * P lam n).degree <
        ((Polynomial.X - Polynomial.C lam) * P lam (n+1)).degree := by
      rw [Polynomial.degree_eq_natDegree hmul.ne_zero, hdm]
      exact lt_of_le_of_lt Polynomial.degree_le_natDegree
        (by exact_mod_cast (show _ < n + 2 from by omega))
    exact ⟨hmul.sub_of_left hlt, by
      show ((Polynomial.X - Polynomial.C lam) * P lam (n+1) -
        Polynomial.C lam * P lam n).natDegree = n+2
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt
        (hdm ▸ lt_of_le_of_lt hdl (by omega))]; exact hdm⟩

/-- `ℒ[Pₙ · q] = 0` when `natDegree q < n`. -/
private lemma L_mul_low_degree (n : ℕ) (q : Polynomial ℝ) (hq : q.natDegree < n) :
    L lam (P lam n * q) = 0 := by
  conv_lhs => rw [← Polynomial.sum_C_mul_X_pow_eq q]
  simp only [Polynomial.sum]
  rw [Finset.mul_sum]
  rw [show ∀ (s : Finset ℕ) (f : ℕ → Polynomial ℝ),
    L lam (∑ i ∈ s, f i) = ∑ i ∈ s, L lam (f i) from fun s f => by
      induction s using Finset.cons_induction with
      | empty => simp; unfold L; simp [Polynomial.sum]
      | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, ← ih, ← L_add]]
  apply Finset.sum_eq_zero; intro j hj
  rw [show P lam n * (Polynomial.C (q.coeff j) * Polynomial.X ^ j) =
    Polynomial.C (q.coeff j) * (P lam n * Polynomial.X ^ j) from by ring,
    L_C_mul, orthogonality _ n j (lt_of_le_of_lt
      (Polynomial.le_natDegree_of_ne_zero (Finsupp.mem_support_iff.mp hj)) hq), mul_zero]

/-- **Norms.** `hₙ = ℒ[Pₙ²] = λⁿ`.
    *Proof.* `Pₙ` is monic of degree `n`, so `Pₙ² = Pₙ·xⁿ + Pₙ·(Pₙ−xⁿ)`.
    Orthogonality kills `ℒ[Pₙ·(Pₙ−xⁿ)]`, and `ℒ[Pₙ·xⁿ] = λⁿ`. -/
theorem norm_squared (n : ℕ) :
    L lam ((P lam n) ^ 2) = lam ^ n := by
  have ⟨hmonic, hdeg⟩ := P_monic_degree lam n
  rw [sq, show P lam n * P lam n =
    P lam n * Polynomial.X ^ n + P lam n * (P lam n - Polynomial.X ^ n) from by ring,
    L_add, L_P_X_pow_n]
  suffices h : L lam (P lam n * (P lam n - Polynomial.X ^ n)) = 0 by linarith
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [show P lam 0 = 1 from rfl]; unfold L; simp [Polynomial.sum]
  · exact L_mul_low_degree lam n _
      ((Polynomial.IsMonicOfDegree.mk hdeg hmonic).natDegree_sub_lt (by omega)
        (Polynomial.IsMonicOfDegree.mk (Polynomial.natDegree_X_pow (n := n))
          (Polynomial.monic_X_pow n)))

-- ─────────────────────────────────────────────────────────────────────────────
-- §5. Hankel matrix, Gram matrix, and change of basis
-- ─────────────────────────────────────────────────────────────────────────────

/-- The `(m+1)×(m+1)` shifted Hankel matrix `H_m(λ) = (M_{i+j+1})`. -/
def hankelH (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  fun i j => M lam (↑i + ↑j + 1)

/-- The Gram matrix `G_{n,k} = ℒ[x·Pₙ·Pₖ]`. -/
def gramG (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  fun n k => L lam (Polynomial.X * P lam ↑n * P lam ↑k)

/-- Linearity of `ℒ` over finite sums. -/
private lemma L_sum' {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℝ) :
    L lam (∑ i ∈ s, f i) = ∑ i ∈ s, L lam (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp; unfold L; simp [Polynomial.sum]
  | cons a s ha ih => rw [Finset.sum_cons, L_add, ih, Finset.sum_cons]

/-- **Change of basis.**  `det H_m = det G`.
    *Proof.*  Let `S(n,k) = coeff k (Pₙ)`.  Since `Pₙ` is monic of degree `n`,
    `S` is unit lower-triangular (`det S = 1`).  By bilinearity of
    `ℒ[x·f·g]`, we get `G = S · H · Sᵀ`, hence `det H = det G`. -/
theorem det_H_eq_det_G (m : ℕ) :
    (hankelH lam m).det = (gramG lam m).det := by
  -- Change-of-basis matrix S(n,k) = (P_n).coeff k
  set S : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
    fun n k => (P lam ↑n).coeff ↑k with hS_def
  -- det S = 1 (S is unit lower triangular)
  have hdetS : S.det = 1 := by
    have hlt : Matrix.BlockTriangular S OrderDual.toDual := by
      intro i j hij
      show (P lam ↑i).coeff ↑j = 0
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by
        rw [(P_monic_degree lam ↑i).2]; exact hij)
    rw [Matrix.det_of_lowerTriangular _ hlt]
    apply Finset.prod_eq_one; intro i _
    show (P lam ↑i).coeff ↑i = 1
    have ⟨hm, hd⟩ := P_monic_degree lam ↑i
    have h : (P lam ↑i).coeff (P lam ↑i).natDegree = 1 := hm.leadingCoeff
    rwa [hd] at h
  -- gramG = S * hankelH * Sᵀ (entry-wise, via bilinearity of L)
  suffices h : gramG lam m = S * hankelH lam m * S.transpose by
    rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdetS]; ring
  ext ⟨n, hn⟩ ⟨k, hk⟩
  simp only [gramG, Matrix.mul_apply, Matrix.transpose_apply, hankelH, hS_def]
  -- Polynomial expansions as Fin(m+1) sums
  have hP_n : P lam n = ∑ i : Fin (m + 1),
      Polynomial.C ((P lam n).coeff ↑i) * Polynomial.X ^ (↑i : ℕ) := by
    conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow' (P lam n)
      (show (P lam n).natDegree < m + 1 from by rw [(P_monic_degree lam n).2]; omega)]
    exact (Fin.sum_univ_eq_sum_range _ _).symm
  have hP_k : P lam k = ∑ i : Fin (m + 1),
      Polynomial.C ((P lam k).coeff ↑i) * Polynomial.X ^ (↑i : ℕ) := by
    conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow' (P lam k)
      (show (P lam k).natDegree < m + 1 from by rw [(P_monic_degree lam k).2]; omega)]
    exact (Fin.sum_univ_eq_sum_range _ _).symm
  -- Both sides equal the double sum ∑_i ∑_j (P_n)_i * (P_k)_j * M(i+j+1).
  -- LHS via bilinearity of L
  have hLHS : L lam (Polynomial.X * P lam n * P lam k) =
      ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
        (P lam n).coeff ↑i * (P lam k).coeff ↑j * M lam ((↑i : ℕ) + (↑j : ℕ) + 1) := by
    -- Expand X * P_n
    have hXPn : Polynomial.X * P lam n = ∑ i : Fin (m + 1),
        Polynomial.C ((P lam n).coeff ↑i) * Polynomial.X ^ ((↑i : ℕ) + 1) := by
      conv_lhs => rw [hP_n]; rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _; ring
    rw [show Polynomial.X * P lam n * P lam k =
      (Polynomial.X * P lam n) * P lam k from by ring,
      hXPn, Finset.sum_mul, L_sum' lam]
    apply Finset.sum_congr rfl; intro i _
    rw [show Polynomial.C ((P lam n).coeff ↑i) * Polynomial.X ^ ((↑i : ℕ) + 1) * P lam k =
      Polynomial.C ((P lam n).coeff ↑i) * (Polynomial.X ^ ((↑i : ℕ) + 1) * P lam k)
      from mul_assoc _ _ _, L_C_mul]
    -- L(X^{i+1} * P_k) = ∑_j q_j * M(i+j+1)
    have hL : L lam (Polynomial.X ^ ((↑i : ℕ) + 1) * P lam k) =
        ∑ j : Fin (m + 1), (P lam k).coeff ↑j * M lam ((↑i : ℕ) + (↑j : ℕ) + 1) := by
      conv_lhs => rw [hP_k]
      rw [Finset.mul_sum, L_sum' lam]
      apply Finset.sum_congr rfl; intro j _
      rw [show Polynomial.X ^ ((↑i : ℕ) + 1) *
        (Polynomial.C ((P lam k).coeff ↑j) * Polynomial.X ^ (↑j : ℕ)) =
        Polynomial.C ((P lam k).coeff ↑j) * Polynomial.X ^ ((↑i : ℕ) + (↑j : ℕ) + 1)
        from by ring, L_C_mul, L_X_pow]
    rw [hL, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; ring
  -- RHS via algebraic rearrangement (sum_comm swaps summation order)
  have hRHS : (∑ x : Fin (m + 1),
      (∑ y : Fin (m + 1), (P lam n).coeff ↑y * M lam ((↑y : ℕ) + (↑x : ℕ) + 1)) *
        (P lam k).coeff ↑x) =
      ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
        (P lam n).coeff ↑i * (P lam k).coeff ↑j * M lam ((↑i : ℕ) + (↑j : ℕ) + 1) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _; ring
  rw [hLHS, hRHS]

/-- `ℒ[Pₙ · Pⱼ] = 0` when `n ≠ j`. -/
private lemma L_P_mul_P_ne (n j : ℕ) (hne : n ≠ j) :
    L lam (P lam n * P lam j) = 0 := by
  rcases lt_or_gt_of_ne hne with h | h
  · rw [mul_comm]; exact L_mul_low_degree lam j _ (by rw [(P_monic_degree lam n).2]; exact h)
  · exact L_mul_low_degree lam n _ (by rw [(P_monic_degree lam j).2]; exact h)

/-- `x · P_{k+1} = P_{k+2} + λP_{k+1} + λPₖ` from the OP recurrence. -/
private lemma X_mul_P_succ (k : ℕ) :
    Polynomial.X * P lam (k + 1) = P lam (k + 2) + Polynomial.C lam * P lam (k + 1) +
      Polynomial.C lam * P lam k := by
  show Polynomial.X * P lam (k + 1) = ((Polynomial.X - Polynomial.C lam) * P lam (k + 1) -
    Polynomial.C lam * P lam k) + Polynomial.C lam * P lam (k + 1) + Polynomial.C lam * P lam k
  ring

/-- `x · P₀ = P₁ + λP₀`. -/
private lemma X_mul_P_zero :
    Polynomial.X * P lam 0 = P lam 1 + Polynomial.C lam * P lam 0 := by
  show Polynomial.X * 1 = (Polynomial.X - Polynomial.C lam) + Polynomial.C lam * 1; ring

/-- **Tridiagonal structure of G.**
    From `xPₖ = Pₖ₊₁ + λPₖ + λPₖ₋₁` and orthogonality:
    `G_{n,k} = 0` if `|n−k| ≥ 2`. -/
theorem gram_tridiagonal (m : ℕ) (n k : Fin (m + 1))
    (h : (↑n : ℕ) + 2 ≤ ↑k ∨ (↑k : ℕ) + 2 ≤ ↑n) :
    gramG lam m n k = 0 := by
  unfold gramG
  rw [show Polynomial.X * P lam ↑n * P lam ↑k =
    P lam ↑n * (Polynomial.X * P lam ↑k) from by ring]
  rcases (↑k : ℕ).eq_zero_or_pos with hk0 | hkpos
  · rw [hk0, X_mul_P_zero, mul_add, L_add,
      show P lam ↑n * (Polynomial.C lam * P lam 0) =
        Polynomial.C lam * (P lam ↑n * P lam 0) from by ring,
      L_C_mul, L_P_mul_P_ne lam ↑n 1 (by rcases h with h | h <;> omega),
      L_P_mul_P_ne lam ↑n 0 (by rcases h with h | h <;> omega)]; ring
  · obtain ⟨j, hkj⟩ : ∃ j, (↑k : ℕ) = j + 1 := ⟨(↑k : ℕ) - 1, by omega⟩
    rw [show (↑k : ℕ) = j + 1 from hkj, X_mul_P_succ, mul_add, mul_add, L_add, L_add,
      show P lam ↑n * (Polynomial.C lam * P lam (j + 1)) =
        Polynomial.C lam * (P lam ↑n * P lam (j + 1)) from by ring,
      show P lam ↑n * (Polynomial.C lam * P lam j) =
        Polynomial.C lam * (P lam ↑n * P lam j) from by ring,
      L_C_mul, L_C_mul,
      L_P_mul_P_ne lam ↑n (j + 2) (by rcases h with h' | h' <;> omega),
      L_P_mul_P_ne lam ↑n (j + 1) (by rcases h with h' | h' <;> omega),
      L_P_mul_P_ne lam ↑n j (by rcases h with h' | h' <;> omega)]; ring

/-- Diagonal entry: `G_{n,n} = λⁿ⁺¹`. -/
private lemma gramG_diag (m : ℕ) (n : Fin (m + 1)) :
    gramG lam m n n = lam ^ ((↑n : ℕ) + 1) := by
  unfold gramG
  rw [show Polynomial.X * P lam ↑n * P lam ↑n = P lam ↑n * (Polynomial.X * P lam ↑n) from by ring]
  rcases (↑n : ℕ) with _ | k
  · rw [X_mul_P_zero, mul_add, L_add,
      show P lam 0 * (Polynomial.C lam * P lam 0) = Polynomial.C lam * (P lam 0 ^ 2) from by
        rw [sq]; ring,
      L_C_mul, L_P_mul_P_ne lam 0 1 (by omega), zero_add, norm_squared]; ring
  · rw [X_mul_P_succ, mul_add, mul_add, L_add, L_add,
      show P lam (k+1) * (Polynomial.C lam * P lam (k+1)) =
        Polynomial.C lam * (P lam (k+1) ^ 2) from by rw [sq]; ring,
      show P lam (k+1) * (Polynomial.C lam * P lam k) =
        Polynomial.C lam * (P lam (k+1) * P lam k) from by ring,
      L_C_mul, L_C_mul,
      L_P_mul_P_ne lam (k+1) (k+2) (by omega), L_P_mul_P_ne lam (k+1) k (by omega),
      norm_squared]; ring

/-- Super-diagonal: `G_{n,n+1} = λⁿ⁺¹`. -/
private lemma gramG_super (m : ℕ) (n : Fin (m + 1)) (hn : (↑n : ℕ) + 1 < m + 1) :
    gramG lam m n ⟨↑n + 1, hn⟩ = lam ^ ((↑n : ℕ) + 1) := by
  unfold gramG;
  rw [show Polynomial.X * P lam ↑n * P lam (↑n+1) =
    P lam ↑n * (Polynomial.X * P lam (↑n+1)) from by ring,
    X_mul_P_succ, mul_add, mul_add, L_add, L_add,
    show P lam ↑n * (Polynomial.C lam * P lam (↑n+1)) =
      Polynomial.C lam * (P lam ↑n * P lam (↑n+1)) from by ring,
    show P lam ↑n * (Polynomial.C lam * P lam ↑n) =
      Polynomial.C lam * (P lam ↑n ^ 2) from by rw [sq]; ring,
    L_C_mul, L_C_mul,
    L_P_mul_P_ne lam ↑n (↑n+2) (by omega), L_P_mul_P_ne lam ↑n (↑n+1) (by omega),
    norm_squared]; ring

/-- Sub-diagonal: `G_{n+1,n} = λⁿ⁺¹`. -/
private lemma gramG_sub (m : ℕ) (n : Fin (m + 1)) (hn : (↑n : ℕ) + 1 < m + 1) :
    gramG lam m ⟨↑n + 1, hn⟩ n = lam ^ ((↑n : ℕ) + 1) := by
  unfold gramG;
  rw [show Polynomial.X * P lam (↑n+1) * P lam ↑n =
    P lam (↑n+1) * (Polynomial.X * P lam ↑n) from by ring]
  rcases (↑n : ℕ) with _ | k
  · rw [X_mul_P_zero, mul_add, L_add,
      show P lam 1 * (Polynomial.C lam * P lam 0) =
        Polynomial.C lam * (P lam 1 * P lam 0) from by ring,
      L_C_mul, L_P_mul_P_ne lam 1 0 (by omega),
      show P lam 1 * P lam 1 = P lam 1 ^ 2 from (sq _).symm, norm_squared]; ring
  · rw [X_mul_P_succ, mul_add, mul_add, L_add, L_add,
      show P lam (k+2) * (Polynomial.C lam * P lam (k+1)) =
        Polynomial.C lam * (P lam (k+2) * P lam (k+1)) from by ring,
      show P lam (k+2) * (Polynomial.C lam * P lam k) =
        Polynomial.C lam * (P lam (k+2) * P lam k) from by ring,
      L_C_mul, L_C_mul,
      L_P_mul_P_ne lam (k+2) (k+1) (by omega), L_P_mul_P_ne lam (k+2) k (by omega),
      show P lam (k+2) * P lam (k+2) = P lam (k+2) ^ 2 from (sq _).symm, norm_squared]; ring

-- ─────────────────────────────────────────────────────────────────────────────
-- §6. Tridiagonal determinant and row factoring
-- ─────────────────────────────────────────────────────────────────────────────

/-- Tridiagonal determinant sequence:
    `d_{n+1} = λ·dₙ − λ·d_{n-1}`, `d₀ = 1`, `d₁ = λ`.
    This is `det G'` where `G'` is obtained from `G` by factoring `λⁿ`
    from row `n`. -/
def d : ℕ → ℝ
  | 0 => 1
  | 1 => lam
  | (n + 2) => lam * d (n + 1) - lam * d n

/-- Gauss sum: `2 · Σᵢ i = m(m+1)`. -/
private lemma two_mul_fin_sum (m : ℕ) : 2 * ∑ i : Fin (m + 1), (i : ℕ) = m * (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have := ih; ring_nf at this ⊢; linarith

/-- `∏ᵢ λⁱ = λ^{m(m+1)/2}`. -/
private lemma prod_lam_pow (m : ℕ) :
    ∏ i : Fin (m + 1), lam ^ (i : ℕ) = lam ^ (m * (m + 1) / 2) := by
  rw [Finset.prod_pow_eq_pow_sum]; congr 1
  have h := two_mul_fin_sum m
  have hdvd : 2 ∣ m * (m + 1) := by
    rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact ⟨k * (m + 1), by subst hk; ring⟩
    · exact ⟨m * (k + 1), by subst hk; ring⟩
  omega

/-- Constant tridiagonal matrix `G'`: diagonal `λ`, super-diagonal `λ`, sub-diagonal `1`. -/
private def tridG (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := fun i j =>
  if (i : ℕ) = j then lam
  else if (j : ℕ) = (i : ℕ) + 1 then lam
  else if (i : ℕ) = (j : ℕ) + 1 then 1
  else 0

/-- `G = D · G'` where `D = diag(1, λ, λ², …)`. -/
private lemma gramG_eq_diag_mul_trid (m : ℕ) :
    gramG lam m = Matrix.diagonal (fun i : Fin (m + 1) => lam ^ (i : ℕ)) * tridG lam m := by
  ext i j; rw [Matrix.diagonal_mul]; unfold tridG
  by_cases hij : (i : ℕ) = j
  · -- diagonal: i = j
    have heq := Fin.ext hij; subst heq; simp [gramG_diag]; ring
  · by_cases hj : (j : ℕ) = (i : ℕ) + 1
    · -- super-diagonal: j = i+1
      conv_lhs => rw [show j = ⟨↑i + 1, by omega⟩ from Fin.ext hj]
      rw [gramG_super lam m i (by omega)]
      simp only [show ¬((i : ℕ) = (i : ℕ) + 1) from by omega, hj, ↓reduceIte]; ring
    · by_cases hi : (i : ℕ) = (j : ℕ) + 1
      · -- sub-diagonal: i = j+1
        have hji : gramG lam m i j = gramG lam m ⟨↑j + 1, by omega⟩ j := by
          congr 1; exact Fin.ext hi
        rw [hji, gramG_sub lam m j (by omega),
          if_neg hij, if_neg hj, if_pos hi, mul_one, hi]
      · -- far off-diagonal
        simp only [hij, hj, hi, ↓reduceIte, mul_zero]
        exact gram_tridiagonal lam m i j (by
          rcases Nat.lt_or_ge (↑i) (↑j) with h | h <;> [left; right] <;> omega)

/-- `a + 1 = b + 1 ↔ a = b` as propositional equality. -/
private lemma nat_succ_eq (a b : ℕ) : (a + 1 = b + 1) = (a = b) :=
  propext (by omega)

/-- Minor(0,0) of `G'_{n+2}` is `G'_{n+1}`. -/
private lemma tridG_minor00 (n : ℕ) :
    (tridG lam (n + 2)).submatrix Fin.succ (Fin.succAbove 0) = tridG lam (n + 1) := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  simp only [Matrix.submatrix_apply, Fin.succAbove_zero]
  unfold tridG; simp only [Fin.val_succ]
  show (if i + 1 = j + 1 then lam else if j + 1 = (i + 1) + 1 then lam
    else if i + 1 = (j + 1) + 1 then 1 else 0) =
    (if i = j then lam else if j = i + 1 then lam else if i = j + 1 then 1 else 0)
  simp only [nat_succ_eq]

set_option maxHeartbeats 400000 in
/-- `det(minor(0,1))` of `G'_{n+2}` equals `det G'_n`. -/
private lemma tridG_minor01_det (n : ℕ) :
    ((tridG lam (n + 2)).submatrix Fin.succ (Fin.succAbove 1)).det =
    (tridG lam n).det := by
  rw [← Matrix.det_transpose]
  rw [Matrix.det_succ_row_zero]
  rw [Fin.sum_univ_succ]
  have htail : ∀ j : Fin (n + 1),
      (-1 : ℝ) ^ ((Fin.succ j : Fin (n + 2)) : ℕ) *
      ((tridG lam (n + 2)).submatrix Fin.succ (Fin.succAbove 1)).transpose 0 (Fin.succ j) *
      (((tridG lam (n + 2)).submatrix Fin.succ (Fin.succAbove 1)).transpose.submatrix
        Fin.succ (Fin.succAbove (Fin.succ j))).det = 0 := by
    intro ⟨j, hj⟩
    suffices h : ((tridG lam (n + 2)).submatrix Fin.succ (Fin.succAbove 1)).transpose 0
      (Fin.succ ⟨j, hj⟩) = 0 by rw [h, mul_zero, zero_mul]
    simp only [Matrix.transpose_apply, Matrix.submatrix_apply, tridG]
    show (if (Fin.succ (Fin.succ ⟨j, hj⟩) : Fin (n + 3)).val =
      (Fin.succAbove 1 (0 : Fin (n + 2)) : Fin (n + 3)).val then lam
      else if (Fin.succAbove 1 (0 : Fin (n + 2)) : Fin (n + 3)).val =
        (Fin.succ (Fin.succ ⟨j, hj⟩) : Fin (n + 3)).val + 1 then lam
      else if (Fin.succ (Fin.succ ⟨j, hj⟩) : Fin (n + 3)).val =
        (Fin.succAbove 1 (0 : Fin (n + 2)) : Fin (n + 3)).val + 1 then 1
      else 0) = 0
    simp [Fin.succAbove, Fin.lt_def]
  rw [Finset.sum_eq_zero (fun j _ => htail j), add_zero]
  rw [show ((0 : Fin (n + 2)) : ℕ) = 0 from rfl, pow_zero, one_mul]
  have hM00 : ((tridG lam (n + 2)).submatrix Fin.succ (Fin.succAbove 1)).transpose 0 0 = 1 := by
    simp only [Matrix.transpose_apply, Matrix.submatrix_apply, tridG]
    show (if (Fin.succ (0 : Fin (n + 2)) : Fin (n + 3)).val =
      (Fin.succAbove 1 (0 : Fin (n + 2)) : Fin (n + 3)).val then lam
      else if (Fin.succAbove 1 (0 : Fin (n + 2)) : Fin (n + 3)).val =
        (Fin.succ (0 : Fin (n + 2)) : Fin (n + 3)).val + 1 then lam
      else if (Fin.succ (0 : Fin (n + 2)) : Fin (n + 3)).val =
        (Fin.succAbove 1 (0 : Fin (n + 2)) : Fin (n + 3)).val + 1 then 1
      else 0) = 1
    simp [Fin.succAbove, Fin.lt_def]
  rw [hM00, one_mul]
  rw [← Matrix.det_transpose]
  congr 1
  ext ⟨i, hi⟩ ⟨j, hj⟩
  simp only [Matrix.transpose_apply, Matrix.submatrix_apply, Fin.succAbove_zero, tridG]
  have h1 : (Fin.succ (Fin.succ ⟨i, hi⟩) : Fin (n + 3)).val = i + 2 := by simp
  have h2 : (Fin.succAbove 1 (Fin.succ ⟨j, hj⟩) : Fin (n + 3)).val = j + 2 := by
    rw [Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def])]
    simp
  rw [h1, h2]; simp only [nat_succ_eq]

/-- `det G' = d(m+1)` by pair induction + cofactor expansion along row 0. -/
private lemma det_tridG (m : ℕ) : (tridG lam m).det = d lam (m + 1) := by
  suffices h : ∀ k, (tridG lam k).det = d lam (k + 1) ∧
    (tridG lam (k + 1)).det = d lam (k + 2) from (h m).1
  intro k; induction k with
  | zero =>
    exact ⟨by simp [tridG, d, Matrix.det_unique],
      by simp [tridG, d, Matrix.det_fin_two]⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
    -- Tail: tridG(n+2) 0 (succ(succ j)) = 0 for all j
    have htail : ∀ j : Fin (n + 1),
        (-1 : ℝ) ^ ((Fin.succ (Fin.succ j) : Fin (n + 3)) : ℕ) *
        tridG lam (n + 2) 0 (Fin.succ (Fin.succ j)) *
        ((tridG lam (n + 2)).submatrix Fin.succ
          (Fin.succAbove (Fin.succ (Fin.succ j)))).det = 0 := by
      intro ⟨j, hj⟩
      suffices h : tridG lam (n + 2) 0 (Fin.succ (Fin.succ ⟨j, hj⟩)) = 0 by
        rw [h, mul_zero, zero_mul]
      show tridG lam (n + 2) ⟨0, by omega⟩ ⟨j + 2, by omega⟩ = 0
      unfold tridG
      simp only [show ¬((0 : ℕ) = j + 2) from by omega,
        show ¬(j + 2 = (0 : ℕ) + 1) from by omega,
        show ¬((0 : ℕ) = (j + 2) + 1) from by omega, ↓reduceIte]
    rw [Finset.sum_eq_zero (fun j _ => htail j), add_zero]
    -- j=0 term
    rw [show ((0 : Fin (n + 3)) : ℕ) = 0 from rfl, pow_zero, one_mul]
    rw [show tridG lam (n + 2) 0 0 = lam from by simp [tridG]]
    rw [tridG_minor00]
    -- j=1 term
    rw [show ((Fin.succ (0 : Fin (n + 2)) : Fin (n + 3)) : ℕ) = 1 from rfl, pow_one]
    have h1e : tridG lam (n + 2) 0 (Fin.succ (0 : Fin (n + 2))) = lam := by
      show tridG lam (n + 2) ⟨0, by omega⟩ ⟨1, by omega⟩ = lam
      unfold tridG; simp
    rw [h1e, show Fin.succ (0 : Fin (n + 2)) = (1 : Fin (n + 3)) from rfl, tridG_minor01_det]
    rw [ih.2, ih.1]; simp [d]; ring

/-- **Row factoring.**  `det G = λ^{m(m+1)/2} · d_{m+1}`.
    *Proof.*  `G = D · G'` where `D = diag(λ⁰,…,λᵐ)` and `G'` is constant
    tridiagonal. Then `det G = det D · det G' = λ^{m(m+1)/2} · d(m+1)`. -/
theorem det_G_eq (m : ℕ) :
    (gramG lam m).det = lam ^ (m * (m + 1) / 2) * d lam (m + 1) := by
  rw [gramG_eq_diag_mul_trid, Matrix.det_mul, Matrix.det_diagonal,
    prod_lam_pow, det_tridG]

-- ─────────────────────────────────────────────────────────────────────────────
-- §7. Main theorem (algebraic form)
-- ─────────────────────────────────────────────────────────────────────────────

/-- **Main Theorem (algebraic).**
    `det H_m(λ) = λ^{m(m+1)/2} · d_{m+1}(λ)`.
    Assembles §5 (change of basis) and §6 (row factoring). -/
theorem det_hankel_main (m : ℕ) :
    (hankelH lam m).det = lam ^ (m * (m + 1) / 2) * d lam (m + 1) := by
  rw [det_H_eq_det_G]
  exact det_G_eq lam m

-- ─────────────────────────────────────────────────────────────────────────────
-- §8. Chebyshev connection
-- ─────────────────────────────────────────────────────────────────────────────

variable (hlam : 0 < lam)
include hlam

/-- **Chebyshev substitution.**  `dₙ(λ) = (√λ)ⁿ · Uₙ(√λ/2)`.
    *Proof (paper).*  Set `dₙ = λ^{n/2} fₙ`, substitute into the recurrence:
    `f_{n+1} = √λ · fₙ − f_{n-1}`, `f₀ = 1`, `f₁ = √λ`.
    With `t = √λ/2`: `f_{n+1} = 2t · fₙ − f_{n-1}`, `f₀ = 1`, `f₁ = 2t`.
    This is exactly the recurrence defining `Uₙ(t)`. -/
theorem d_eq_chebyshev (n : ℕ) :
    d lam n = (Real.sqrt lam) ^ n *
      (Polynomial.Chebyshev.U ℝ n).eval (Real.sqrt lam / 2) := by
  -- Both sides satisfy d₀=1, d₁=λ, f(n+2) = λ·f(n+1) − λ·f(n).
  -- We prove P(k) ∧ P(k+1) by induction on k.
  have hlam0 := hlam.le
  have hmul : Real.sqrt lam * Real.sqrt lam = lam := Real.mul_self_sqrt hlam0
  set s := Real.sqrt lam with hs_def
  set t := s / 2 with ht_def
  -- Abbreviation for the statement
  let Q k := d lam k = s ^ k * (Polynomial.Chebyshev.U ℝ (k : ℤ)).eval t
  suffices h : ∀ k, Q k ∧ Q (k + 1) from (h n).1
  intro k
  induction k with
  | zero =>
    constructor
    · -- Q 0: d lam 0 = 1 = s^0 * U_0(t)
      show d lam 0 = s ^ 0 * (Polynomial.Chebyshev.U ℝ (0 : ℤ)).eval t
      simp [d, Polynomial.Chebyshev.U_zero]
    · -- Q 1: d lam 1 = lam = s * U_1(t)
      show d lam 1 = s ^ 1 * (Polynomial.Chebyshev.U ℝ (1 : ℤ)).eval t
      simp only [d, Polynomial.Chebyshev.U_one, pow_one,
        Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
      -- Goal: lam = s * (2 * t)
      rw [show (2 : ℝ) * t = s from by rw [ht_def]; ring]
      exact hmul.symm
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    -- Need Q (m + 2): d lam (m+2) = s^(m+2) * U_{m+2}(t)
    show d lam (m + 2) = s ^ (m + 2) * (Polynomial.Chebyshev.U ℝ (↑(m + 2) : ℤ)).eval t
    -- Unfold d recurrence
    show lam * d lam (m + 1) - lam * d lam m =
      s ^ (m + 2) * (Polynomial.Chebyshev.U ℝ (↑(m + 2) : ℤ)).eval t
    -- Substitute IH
    rw [ih.2, ih.1]
    -- Expand U(m+2) via Chebyshev recurrence
    have hcast : (↑(m + 2) : ℤ) = (↑m : ℤ) + 2 := by push_cast; ring
    rw [hcast, Polynomial.Chebyshev.U_add_two ℝ (↑m : ℤ)]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X]
    -- Simplify 2 * t = s
    rw [show (2 : ℝ) * t = s from by rw [ht_def]; ring]
    -- Goal: lam * (s^(m+1) * u₁) - lam * (s^m * u₀)
    --     = s^(m+2) * (s * u₁ - u₀)
    -- Replace lam with s*s, then it's a ring identity
    rw [← hmul]
    push_cast
    ring

/-- **Corollary (Chebyshev form).**
    `det H_m(λ) = (√λ)^{(m+1)²} · U_{m+1}(√λ/2)`.
    *Proof.*  From `det H_m = λ^{m(m+1)/2} · d_{m+1}` and the substitution:
    `λ^{m(m+1)/2} · (√λ)^{m+1} = (√λ)^{m(m+1)+(m+1)} = (√λ)^{(m+1)²}`. -/
theorem det_hankel_chebyshev (m : ℕ) :
    (hankelH lam m).det = (Real.sqrt lam) ^ ((m + 1) ^ 2) *
      (Polynomial.Chebyshev.U ℝ (m + 1)).eval (Real.sqrt lam / 2) := by
  rw [det_hankel_main lam m, d_eq_chebyshev lam hlam (m + 1)]
  -- Exponent arithmetic:
  -- lam^{m(m+1)/2} · (√lam)^{m+1} · U = (√lam)^{(m+1)²} · U
  -- since lam^{m(m+1)/2} = ((√lam)²)^{m(m+1)/2} = (√lam)^{m(m+1)}
  -- and m(m+1) + (m+1) = (m+1)(m+1) = (m+1)²
  -- Step 1: m*(m+1) is even
  have hdvd : 2 ∣ m * (m + 1) := by
    rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact ⟨k * (m + 1), by subst hk; ring⟩
    · exact ⟨m * (k + 1), by subst hk; ring⟩
  -- Step 2: (√lam)² = lam
  have hsq : Real.sqrt lam ^ 2 = lam := by
    rw [sq]; exact Real.mul_self_sqrt hlam.le
  -- Step 3: lam^{m(m+1)/2} = (√lam)^{m(m+1)}
  have hpow : lam ^ (m * (m + 1) / 2) = Real.sqrt lam ^ (m * (m + 1)) := by
    conv_lhs => rw [← hsq, ← pow_mul, Nat.mul_div_cancel' hdvd]
  -- Step 4: reassemble exponents and close
  have hexp : m * (m + 1) + (m + 1) = (m + 1) ^ 2 := by ring
  rw [← mul_assoc, hpow, ← pow_add, hexp]
  norm_cast

end ClosedFormDet

end -- noncomputable section

-- ═══════════════════════════════════════════════════════════════════════════
-- Part II. Computational verification (decidable, for native_decide)
-- ═══════════════════════════════════════════════════════════════════════════

namespace PPT

-- ─────────────────────────────────────────────────────────────────────────────
-- Tridiagonal determinant sequence (polynomial in λ)
-- ─────────────────────────────────────────────────────────────────────────────

/-- `d_n` as a polynomial in λ: `d_{n+1} = λ·dₙ − λ·d_{n-1}`, `d₀=1`, `d₁=λ`. -/
def dSeq : Nat → Poly
  | 0 => const 1
  | 1 => monome 1
  | (n + 2) =>
    sub (mul (monome 1) (dSeq (n + 1)))
        (mul (monome 1) (dSeq n))
termination_by n => n

/-- Closed-form candidate: `λ^{m(m+1)/2} · d_{m+1}`. -/
def detFormula (m : Nat) : Poly :=
  mul (monome (m * (m + 1) / 2)) (dSeq (m + 1))

/-- Boolean check: `det(B_m) = λ^{m(m+1)/2} · d_{m+1}`. -/
def checkDetFormula (m : Nat) : Bool :=
  beq (detB m) (detFormula m)

/-- Check that detFormula satisfies:
    detFormula(m+2) = λ^{m+3}·detFormula(m+1) − λ^{2m+4}·detFormula(m).
    This follows algebraically from dSeq(n+2) = λ·dSeq(n+1) − λ·dSeq(n). -/
def checkDetFormulaRec (m : Nat) : Bool :=
  beq (detFormula (m + 2))
      (sub (mul (monome (m + 3)) (detFormula (m + 1)))
           (mul (monome (2 * m + 4)) (detFormula m)))

/-- Check that detB satisfies the same recurrence:
    detB(m+2) = λ^{m+3}·detB(m+1) − λ^{2m+4}·detB(m). -/
def checkDetBRec (m : Nat) : Bool :=
  beq (detB (m + 2))
      (sub (mul (monome (m + 3)) (detB (m + 1)))
           (mul (monome (2 * m + 4)) (detB m)))

-- ─────────────────────────────────────────────────────────────────────────────
-- Formal kernel proofs (certified by native_decide)
-- (Runtime #eval cross-checks stripped — see ClosedFormDet_with_evals.lean.bak)
-- ─────────────────────────────────────────────────────────────────────────────

/-- m=0: det(B₀) = λ = λ⁰·d₁ = λ. -/
theorem closed_form_det_m0 : checkDetFormula 0 = true := by native_decide

/-- m=1: det(B₁) = λ²(λ−1) = λ¹·d₂ = λ·(λ²−λ). -/
theorem closed_form_det_m1 : checkDetFormula 1 = true := by native_decide

/-- m=2: det(B₂) = λ⁵(λ−2) = λ³·d₃ = λ³·(λ³−2λ²). -/
theorem closed_form_det_m2 : checkDetFormula 2 = true := by native_decide

/-- m=3: det(B₃) = λ^6·d₄ = λ^6·(λ⁴−3λ³+λ²). -/
theorem closed_form_det_m3 : checkDetFormula 3 = true := by native_decide

/-- m=4: det(B₄) = λ^10·d₅. -/
theorem closed_form_det_m4 : checkDetFormula 4 = true := by native_decide

/-- m=5: det(B₅) = λ^15·d₆. -/
theorem closed_form_det_m5 : checkDetFormula 5 = true := by native_decide

/-- m=6: det(B₆) = λ^21·d₇. -/
theorem closed_form_det_m6 : checkDetFormula 6 = true := by native_decide

-- ─────────────────────────────────────────────────────────────────────────────
-- Proof strategy for the general theorem
--
-- Both detB and detFormula satisfy the same 2-term recurrence:
--   f(m+2) = λ^{m+3} · f(m+1) − λ^{2m+4} · f(m)
--
-- For detFormula, this follows algebraically from the dSeq recurrence:
--   dSeq(n+2) = λ·dSeq(n+1) − λ·dSeq(n)
-- combined with the exponent arithmetic in detFormula.
--
-- For detB, this is the hard part: it requires the moment recurrence
--   M_{n+2} − λ·M_{n+1} = λ · Σ_{k=0}^{n} M_k · M_{n-k}
-- together with the Hankel structure of the matrix and either:
--   (a) the orthogonal polynomial change of basis, or
--   (b) the Desnanot-Jacobi identity applied to shifted Hankel matrices.
--
-- Given both recurrences and matching base cases (m=0,1 by native_decide),
-- det_hankel_general follows by strong induction.
-- ─────────────────────────────────────────────────────────────────────────────

/-- `beq` extracts trim equality. -/
private lemma beq_eq {p q : Poly} (h : PPT.beq p q = true) :
    PPT.trim p = PPT.trim q := by
  simp [PPT.beq] at h; exact h

/-- `beq` is transitive. -/
private lemma beq_trans {p q r : Poly}
    (h1 : PPT.beq p q = true) (h2 : PPT.beq q r = true) :
    PPT.beq p r = true := by
  simp [PPT.beq] at *; exact h1.trans h2

/-- `beq` is symmetric. -/
private lemma beq_symm {p q : Poly} (h : PPT.beq p q = true) :
    PPT.beq q p = true := by
  simp [PPT.beq] at *; exact h.symm

-- ─────────────────────────────────────────────────────────────────────────────
-- Eval-based congruence infrastructure
--
-- Strategy: route `beq` (trim equality) through `eval` (evaluation at all
-- integer points).  Three key lemmas:
--   (E1)  eval ∘ trim = eval                    (trailing zeros vanish)
--   (E2)  eval (mul p q) = eval p · eval q      (eval is a ring hom)
--   (E3)  eval (sub p q) = eval p − eval q
--   (PI)  (∀ x, eval p x = eval q x) → trim p = trim q    (poly identity)
-- Together these give: trim a = trim a' → trim (op e a) = trim (op e a').
-- ─────────────────────────────────────────────────────────────────────────────

/-- `p[i]! = p[i]` when in bounds. -/
private lemma getElem_bang_eq (p : Poly) (i : Nat) (hi : i < p.size) :
    p[i]! = p[i] := by
  show (if h : i < p.size then p[i] else default) = p[i]; simp [hi]

/-- Reconstruct an array from its pop and last element. -/
private lemma pop_push_last (p : Poly) (hp : 0 < p.size) :
    p.pop.push p[p.size - 1] = p := by
  apply Array.ext
  · simp [Array.size_pop]; omega
  · intro i hi1 hi2
    simp only [Array.size_push, Array.size_pop] at hi1
    by_cases h : i < p.size - 1
    · simp [Array.getElem_push, h]
    · have : i = p.size - 1 := by omega
      subst this; simp [Array.getElem_push]

/-- Eval ignores a trailing zero: the Horner step `(acc + 0·xⁱ, xⁱ·x)` preserves `acc`. -/
private lemma eval_pop_zero (p : Poly) (x : Int) (hp : 0 < p.size)
    (hz : p[p.size - 1]! = 0) : PPT.eval p x = PPT.eval p.pop x := by
  have hz2 : p[p.size - 1] = 0 := by
    rw [← getElem_bang_eq p _ (by omega)]; exact hz
  simp only [PPT.eval]
  rw [← pop_push_last p hp, Array.foldl_push, hz2]; simp

/-- Recursive characterization of `trim`: peel off trailing zeros one at a time.
    Requires unwinding the `while` loop in `PPT.trim` (pure `forIn` over `Lean.Loop`). -/
private lemma trim_rec (p : Poly) :
    PPT.trim p = if _h : 0 < p.size then
      if p[p.size - 1]! = 0 then PPT.trim p.pop else p
    else #[] := by
  exact PPT.trim.eq_1 p

private lemma trim_empty : PPT.trim (#[] : Poly) = #[] := by native_decide

private lemma trim_pop_zero (p : Poly) (hp : 0 < p.size) (hz : p[p.size - 1]! = 0) :
    PPT.trim p = PPT.trim p.pop := by
  rw [trim_rec, dif_pos hp]
  have : p[p.size - 1]! = 0 := hz
  rw [this]; simp

private lemma trim_self (p : Poly) (hp : 0 < p.size) (hnz : p[p.size - 1]! ≠ 0) :
    PPT.trim p = p := by
  rw [trim_rec, dif_pos hp]
  have : p[p.size - 1]! ≠ 0 := hnz
  simp [this]

/-- `eval` ignores trailing zeros: `eval (trim p) x = eval p x`. -/
private lemma eval_trim (p : Poly) (x : Int) :
    PPT.eval (PPT.trim p) x = PPT.eval p x := by
  suffices h : ∀ n (q : Poly), q.size = n → PPT.eval (PPT.trim q) x = PPT.eval q x from
    h p.size p rfl
  intro n; induction n with
  | zero =>
    intro q hq; have := Array.eq_empty_of_size_eq_zero hq; subst this
    rw [trim_empty]
  | succ n ih =>
    intro q hq
    by_cases hz : q[q.size - 1]! = 0
    · rw [trim_pop_zero q (by omega) hz,
        ih q.pop (by simp [Array.size_pop]; omega),
        eval_pop_zero q x (by omega) hz]
    · rw [trim_self q (by omega) hz]

/-- Coefficient-wise sum form of polynomial evaluation. -/
private def polySum (b : Poly) (x : Int) : Int :=
  (List.range b.size).foldl (fun acc i => acc + b[i]! * x ^ i) 0

/-- Foldl congr: if `f` and `g` agree on list elements, their foldls agree. -/
private lemma list_foldl_congr' {f g : Int → Nat → Int} {l : List Nat} {init : Int}
    (h : ∀ i, i ∈ l → ∀ acc, f acc i = g acc i) :
    l.foldl f init = l.foldl g init := by
  induction l generalizing init with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldl_cons]; rw [h j List.mem_cons_self]
    exact ih fun i hi acc => h i (List.mem_cons_of_mem j hi) acc

/-- `(b.push c)[i]! = b[i]!` for `i < b.size`. -/
private lemma push_getElem_bang' (b : Poly) (c : Int) (i : Nat) (hi : i < b.size) :
    (b.push c)[i]! = b[i]! := by
  show (if h : i < (b.push c).size then (b.push c)[i] else default) =
    (if h : i < b.size then b[i] else default)
  simp only [hi, dite_true, Array.size_push, show i < b.size + 1 from by omega,
    Array.getElem_push_lt hi]

/-- `polySum` respects `push`: adding a coefficient extends the sum. -/
private lemma polySum_push (b : Poly) (c : Int) (x : Int) :
    polySum (b.push c) x = polySum b x + c * x ^ b.size := by
  simp only [polySum, Array.size_push]
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  congr 1
  · exact list_foldl_congr' fun i hi acc => by
      rw [push_getElem_bang' b c i (List.mem_range.mp hi)]
  · show (if h : b.size < (b.push c).size then (b.push c)[b.size] else default) * _ = _
    simp only [Array.size_push, show b.size < b.size + 1 from by omega, dite_true,
      Array.getElem_push_eq]

/-- The Horner foldl computes `(acc + xi * polySum b x, xi * x^b.size)`. -/
private lemma foldl_eq_polySum (b : Poly) (x acc xi : Int) :
    (b.foldl (fun (s : Int × Int) c => (s.1 + c * s.2, s.2 * x)) (acc, xi) :
      Int × Int) =
    (acc + xi * polySum b x, xi * x ^ b.size) := by
  suffices h : ∀ n (b : Poly), b.size = n →
      (b.foldl (fun (s : Int × Int) c => (s.1 + c * s.2, s.2 * x)) (acc, xi) :
        Int × Int) = (acc + xi * polySum b x, xi * x ^ b.size) from h b.size b rfl
  intro n; induction n with
  | zero =>
    intro b hb; have := Array.eq_empty_of_size_eq_zero hb; subst this; simp [polySum]
  | succ n ih =>
    intro b hb
    have hp : 0 < b.size := by omega
    have hpopsize : b.pop.size = n := by simp [Array.size_pop]; omega
    have hev := polySum_push b.pop b[b.size - 1] x
    rw [hpopsize] at hev
    have hbsize : (b.pop.push b[b.size - 1]).size = n + 1 := by
      simp [Array.size_push, Array.size_pop]; omega
    rw [← pop_push_last b hp, Array.foldl_push, ih b.pop hpopsize, hpopsize]
    dsimp only [Prod.fst, Prod.snd]
    rw [hev, hbsize, Prod.mk.injEq]
    exact ⟨by ring, by ring⟩

/-- `eval = polySum`. -/
private lemma eval_eq_polySum (b : Poly) (x : Int) : PPT.eval b x = polySum b x := by
  show (b.foldl (fun (s : Int × Int) c => (s.1 + c * s.2, s.2 * x)) (0, 1)).1 = _
  rw [foldl_eq_polySum]; simp

/-- `p[i]! = 0` when `i` is out of bounds. -/
private lemma oob_getElem_bang (p : Poly) (i : Nat) (hi : ¬(i < p.size)) :
    p[i]! = 0 := by
  show (if h : i < p.size then _ else default) = 0; simp [hi]

/-- `(a.map (· * c))[i]! = a[i]! * c`. -/
private lemma map_mul_getElem_bang (a : Poly) (c : Int) (i : Nat) :
    (a.map (· * c))[i]! = a[i]! * c := by
  show (if h : i < (a.map (· * c)).size then _ else _) =
    (if h : i < a.size then _ else _) * c
  by_cases hj : i < a.size
  · simp [Array.size_map, hj, Array.getElem_map]
  · simp [Array.size_map, hj]

/-- `eval (smul c a) x = c * eval a x`. -/
private lemma eval_smul (c : Int) (a : Poly) (x : Int) :
    PPT.eval (PPT.smul c a) x = c * PPT.eval a x := by
  rw [eval_eq_polySum, eval_eq_polySum]
  simp only [polySum, PPT.smul, Array.size_map]
  -- Both sides are foldls over the same list; show the functions agree
  have hcongr : ∀ i, ∀ acc : Int,
      acc + (a.map (· * c))[i]! * x ^ i = acc + a[i]! * c * x ^ i := by
    intro i acc; rw [map_mul_getElem_bang]
  rw [list_foldl_congr' (fun i _ acc => hcongr i acc)]
  -- Now: foldl (fun acc i => acc + a[i]! * c * x^i) 0 (range a.size)
  --    = c * foldl (fun acc i => acc + a[i]! * x^i) 0 (range a.size)
  -- The additive foldl satisfies foldl f (a+b) l = a + foldl f b l
  have foldl_shift : ∀ (g : Nat → Int) (l : List Nat) (a b : Int),
      List.foldl (fun acc i => acc + g i) (a + b) l =
      a + List.foldl (fun acc i => acc + g i) b l := by
    intro g l; induction l with
    | nil => intros; simp
    | cons j l ih => intro a b; simp only [List.foldl_cons]; rw [show a + b + g j = a + (b + g j) from by ring]; exact ih a _
  -- Factor c out of the foldl
  suffices h : ∀ l (init : Int),
    List.foldl (fun acc i => acc + a[i]! * c * x ^ i) init l =
    init + c * List.foldl (fun acc i => acc + a[i]! * x ^ i) 0 l by rw [h]; ring
  intro l; induction l with
  | nil => intro init; simp
  | cons j l ih =>
    intro init; simp only [List.foldl_cons]
    rw [ih]
    conv_rhs => rw [show (0 : Int) + a[j]! * x ^ j = a[j]! * x ^ j + 0 from by ring]
    rw [foldl_shift (fun i => a[i]! * x ^ i) l (a[j]! * x ^ j) 0]; ring

/-- Extending the `polySum` range with zero coefficients does nothing. -/
private lemma polySum_extend (p : Poly) (x : Int) (n : Nat) (hn : p.size ≤ n) :
    (List.range n).foldl (fun acc i => acc + p[i]! * x ^ i) 0 = polySum p x := by
  induction n with
  | zero => simp at hn; simp [hn, polySum]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases h : p.size ≤ n
    · rw [oob_getElem_bang p n (by omega)]; simp; exact ih h
    · unfold polySum; rw [← show n + 1 = p.size from by omega,
        List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Splitting a coefficient-sum foldl into two independent sums. -/
private lemma foldl_add_split (x : Int) (l : List Nat) (f g : Nat → Int) :
    List.foldl (fun acc i => acc + (f i + g i) * x ^ i) (0 : Int) l =
    List.foldl (fun acc i => acc + f i * x ^ i) 0 l +
    List.foldl (fun acc i => acc + g i * x ^ i) 0 l := by
  suffices h : ∀ a b : Int,
    List.foldl (fun acc i => acc + (f i + g i) * x ^ i) (a + b) l =
    List.foldl (fun acc i => acc + f i * x ^ i) a l +
    List.foldl (fun acc i => acc + g i * x ^ i) b l from by simpa using h 0 0
  intro a b; induction l generalizing a b with
  | nil => simp
  | cons j l ih =>
    simp only [List.foldl_cons]
    rw [show a + b + (f j + g j) * x ^ j =
      (a + f j * x ^ j) + (b + g j * x ^ j) from by ring]
    exact ih _ _

/-- `eval (add p q) x = eval p x + eval q x`. -/
private lemma eval_add (p q : Poly) (x : Int) :
    PPT.eval (PPT.add p q) x = PPT.eval p x + PPT.eval q x := by
  rw [eval_eq_polySum, eval_eq_polySum, eval_eq_polySum]
  rw [← polySum_extend p x (max p.size q.size) (le_max_left _ _),
      ← polySum_extend q x (max p.size q.size) (le_max_right _ _)]
  simp only [polySum, PPT.add, Array.size_ofFn]
  -- The ofFn array has (ofFn f)[i]! = f i for i in range
  have hofn : ∀ i, i < max p.size q.size →
      (Array.ofFn (n := max p.size q.size) fun j =>
        (if (↑j : Nat) < p.size then p[(↑j : Nat)]! else 0) +
        (if (↑j : Nat) < q.size then q[(↑j : Nat)]! else 0))[i]! =
      p[i]! + q[i]! := by
    intro i hi
    show (if h : i < (Array.ofFn _).size then (Array.ofFn _)[i] else default) = _
    simp only [Array.size_ofFn, hi, dite_true, Array.getElem_ofFn]
    -- Goal: (if i < p.size then p[i]! else 0) + (if i < q.size then q[i]! else 0) = p[i]! + q[i]!
    have hp : (if i < p.size then p[i]! else 0) = p[i]! := by
      split <;> [rfl; exact (oob_getElem_bang _ _ (by omega)).symm]
    have hq : (if i < q.size then q[i]! else 0) = q[i]! := by
      split <;> [rfl; exact (oob_getElem_bang _ _ (by omega)).symm]
    rw [hp, hq]
  rw [list_foldl_congr' (fun i hi acc => by rw [hofn i (List.mem_range.mp hi)])]
  exact foldl_add_split _ _ _ _

/-- `(p.extract 1 p.size)[j]! = p[j+1]!` for `j < p.size - 1`. -/
private lemma extract_getElem_bang (p : Poly) (j : Nat) (hj : j < p.size - 1) :
    (p.extract 1 p.size)[j]! = p[j + 1]! := by
  show (if h : j < (p.extract 1 p.size).size then _ else _) =
    (if h : j + 1 < p.size then _ else _)
  simp only [Array.size_extract, show j < min p.size p.size - 1 from by omega, dite_true,
    show j + 1 < p.size from by omega]
  simp [Array.getElem_extract]; congr 1; omega

/-- Reindexing: `Σ p[i+1]*x^{i+1} = x * Σ (extract 1)[i]*x^i`. -/
private lemma shift_sum (p : Poly) (x : Int) (k : Nat) (hk : k ≤ p.size - 1) :
    (List.range k).foldl (fun acc i => acc + p[i + 1]! * x ^ (i + 1)) 0 =
    x * (List.range k).foldl (fun acc i => acc + (p.extract 1 p.size)[i]! * x ^ i) 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    conv_lhs => rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    conv_rhs => rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih (by omega), extract_getElem_bang p k (by omega)]; ring

/-- Peeling the first coefficient: `Σ_{i<n+1} = p[0]! + Σ_{i<n} p[i+1]*x^{i+1}`. -/
private lemma hstep_lemma (p : Poly) (x : Int) (n : Nat) :
    (List.range (n + 1)).foldl (fun acc i => acc + p[i]! * x ^ i) 0 =
    p[0]! + (List.range n).foldl (fun acc i => acc + p[i + 1]! * x ^ (i + 1)) 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    conv_lhs => rw [show n + 1 + 1 = (n + 1) + 1 from rfl,
        List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    conv_rhs => rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih]; ring

/-- Horner decomposition: `eval p x = p[0]! + x * eval (p.extract 1 p.size) x`. -/
private lemma eval_cons (p : Poly) (x : Int) (hp : 0 < p.size) :
    PPT.eval p x = p[0]! + x * PPT.eval (p.extract 1 p.size) x := by
  rw [eval_eq_polySum, eval_eq_polySum]
  simp only [polySum, Array.size_extract, show min p.size p.size - 1 = p.size - 1 from by omega]
  conv_lhs => rw [show p.size = (p.size - 1) + 1 from by omega]
  rw [hstep_lemma, shift_sum p x (p.size - 1) (by omega)]

/-- `eval (#[0] ++ r) x = x * eval r x`: prepending zero shifts by `x`. -/
private lemma eval_prepend_zero (r : Poly) (x : Int) :
    PPT.eval (#[(0 : Int)] ++ r) x = x * PPT.eval r x := by
  rw [eval_cons _ x (by simp [Array.size_append])]
  have h0 : (#[(0 : Int)] ++ r)[0]! = 0 := by
    show (if h : 0 < (#[(0:Int)] ++ r).size then _ else _) = 0
    simp [Array.size_append]
  have hext : (#[(0 : Int)] ++ r).extract 1 (#[(0 : Int)] ++ r).size = r := by
    rw [← Array.toList_inj, Array.toList_extract]
    simp
  rw [h0, hext]; ring

/-- `eval` is multiplicative.
    *Proof.* By induction on `p.size` using the recursive `mul` definition. -/
private lemma eval_mul (p q : Poly) (x : Int) :
    PPT.eval (PPT.mul p q) x = PPT.eval p x * PPT.eval q x := by
  suffices h : ∀ n (p : Poly), p.size = n → ∀ q : Poly,
      PPT.eval (PPT.mul p q) x = PPT.eval p x * PPT.eval q x from
    h p.size p rfl q
  intro n; induction n with
  | zero =>
    intro p hp q; have := Array.eq_empty_of_size_eq_zero hp; subst this
    simp [PPT.mul, PPT.eval]
  | succ n ih =>
    intro p hp q
    by_cases hq : q.size = 0
    · have := Array.eq_empty_of_size_eq_zero hq; subst this
      simp [PPT.mul, PPT.eval]
    · rw [PPT.mul.eq_1]
      simp only [show ¬(p.size = 0 ∨ q.size = 0) from by omega, dif_neg, not_false_eq_true]
      rw [eval_add, eval_smul, eval_prepend_zero,
          ih (p.extract 1 p.size) (by rw [Array.size_extract]; omega) q,
          eval_cons p x (by omega)]
      ring

/-- `eval` respects subtraction. -/
private lemma eval_sub (p q : Poly) (x : Int) :
    PPT.eval (PPT.sub p q) x = PPT.eval p x - PPT.eval q x := by
  simp only [PPT.sub]; rw [eval_add, eval_smul]; ring

/-- `trim` never increases size. -/
private lemma trim_size_le (p : Poly) : (PPT.trim p).size ≤ p.size := by
  suffices h : ∀ n (p : Poly), p.size = n → (PPT.trim p).size ≤ p.size from h p.size p rfl
  intro n; induction n with
  | zero => intro p hp; have := Array.eq_empty_of_size_eq_zero hp; subst this; simp [PPT.trim]
  | succ n ih =>
    intro p hp; rw [PPT.trim.eq_1, dif_pos (by omega)]
    split
    · calc (PPT.trim p.pop).size ≤ p.pop.size := ih p.pop (by simp [Array.size_pop]; omega)
        _ ≤ p.size := by simp [Array.size_pop]
    · omega

/-- `trim` is idempotent. -/
private lemma trim_idempotent (p : Poly) : PPT.trim (PPT.trim p) = PPT.trim p := by
  suffices h : ∀ n (p : Poly), p.size = n → PPT.trim (PPT.trim p) = PPT.trim p from h p.size p rfl
  intro n; induction n with
  | zero => intro p hp; have := Array.eq_empty_of_size_eq_zero hp; subst this; simp [PPT.trim]
  | succ n ih =>
    intro p hp; rw [PPT.trim.eq_1 p, dif_pos (by omega)]
    split
    · exact ih p.pop (by simp [Array.size_pop]; omega)
    · rename_i hnz; rw [PPT.trim.eq_1, dif_pos (by omega), if_neg hnz]

/-- Convert a `Poly` to a Mathlib `Polynomial ℤ`. -/
private noncomputable def toMP (p : Poly) : Polynomial ℤ :=
  ∑ i ∈ Finset.range p.size, Polynomial.monomial i (p[i]!)

/-- Coefficients of `toMP`: `(toMP a).coeff i = a[i]!`. -/
private lemma coeff_toMP (a : Poly) (i : Nat) : (toMP a).coeff i = a[i]! := by
  simp only [toMP]; rw [Polynomial.finset_sum_coeff]; simp only [Polynomial.coeff_monomial]
  by_cases hi : i < a.size
  · rw [Finset.sum_eq_single i (fun j _ hj => if_neg hj)
      (fun h => absurd (Finset.mem_range.mpr hi) h)]; simp
  · rw [oob_getElem_bang a i hi]; apply Finset.sum_eq_zero
    intro j hj; exact if_neg (by have := Finset.mem_range.mp hj; omega)

/-- `Finset.sum` = `List.foldl` over `range`. -/
private lemma finset_sum_eq_foldl (n : Nat) (f : Nat → Int) :
    ∑ i ∈ Finset.range n, f i = (List.range n).foldl (fun acc i => acc + f i) 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, List.range_succ, List.foldl_append,
        List.foldl_cons, List.foldl_nil]

/-- `toMP` agrees with `PPT.eval`. -/
private lemma toMP_eval (p : Poly) (x : Int) : (toMP p).eval x = PPT.eval p x := by
  rw [eval_eq_polySum]; simp only [toMP, polySum, Polynomial.eval_finset_sum,
    Polynomial.eval_monomial]; exact finset_sum_eq_foldl _ _

/-- Trimmed arrays with the same `getElem!` values are equal. -/
private lemma trimmed_eq_of_getElem_bang (p q : Poly)
    (htp : PPT.trim p = p) (htq : PPT.trim q = q)
    (h : ∀ i : Nat, p[i]! = q[i]!) : p = q := by
  have hsz : p.size = q.size := by
    by_contra hne
    wlog hlt : p.size < q.size with H
    · exact H q p htq htp (fun i => (h i).symm) (Ne.symm hne) (by omega)
    have hq_last : q[q.size - 1]! ≠ 0 := by
      intro hz
      have htq' := htq ▸ (PPT.trim.eq_1 q)
      rw [dif_pos (by omega : 0 < q.size), if_pos hz] at htq'
      have := congrArg Array.size htq'
      have := trim_size_le q.pop; simp [Array.size_pop] at *; omega
    exact hq_last (by rw [← h]; exact oob_getElem_bang p _ (by omega))
  apply Array.ext hsz; intro i hi1 hi2
  rw [show (p[i] : Int) = p[i]! from by
      show _ = (if h : i < p.size then p[i] else (default : Int)); simp [hi1],
    show (q[i] : Int) = q[i]! from by
      show _ = (if h : i < q.size then q[i] else (default : Int)); simp [hi2]]
  exact h i

/-- **Polynomial identity over ℤ.** If two `Poly` arrays agree on all integers,
    they have the same `trim`.  Uses `Polynomial.funext`: ℤ is infinite, so a
    polynomial vanishing everywhere must be zero. -/
private lemma trim_eq_of_eval_eq (p q : Poly)
    (h : ∀ x : Int, PPT.eval p x = PPT.eval q x) :
    PPT.trim p = PPT.trim q := by
  have heval : ∀ x : Int, (toMP (PPT.trim p)).eval x = (toMP (PPT.trim q)).eval x := by
    intro x; rw [toMP_eval, toMP_eval, eval_trim, eval_trim]; exact h x
  have hmp : toMP (PPT.trim p) = toMP (PPT.trim q) := Polynomial.funext heval
  have hcoeff : ∀ i : Nat, (PPT.trim p)[i]! = (PPT.trim q)[i]! := by
    intro i; rw [← coeff_toMP, ← coeff_toMP, hmp]
  exact trimmed_eq_of_getElem_bang _ _ (trim_idempotent p) (trim_idempotent q) hcoeff

/-- Trailing zeros don't affect multiplication (after trimming). -/
private lemma trim_mul_congr (e a a' : Poly) (h : PPT.trim a = PPT.trim a') :
    PPT.trim (PPT.mul e a) = PPT.trim (PPT.mul e a') :=
  trim_eq_of_eval_eq _ _ fun x => by
    rw [eval_mul, eval_mul]; congr 1
    rw [← eval_trim a, ← eval_trim a', h]

/-- Trailing zeros don't affect subtraction (after trimming). -/
private lemma trim_sub_congr (p p' q q' : Poly)
    (hp : PPT.trim p = PPT.trim p') (hq : PPT.trim q = PPT.trim q') :
    PPT.trim (PPT.sub p q) = PPT.trim (PPT.sub p' q') :=
  trim_eq_of_eval_eq _ _ fun x => by
    rw [eval_sub, eval_sub]
    congr 1 <;> [rw [← eval_trim p, ← eval_trim p', hp];
                  rw [← eval_trim q, ← eval_trim q', hq]]

/-- **Lemma C.** Congruence: if `beq a a' = true` and `beq b b' = true`,
    then `beq (sub (mul e a) (mul f b)) (sub (mul e a') (mul f b')) = true`. -/
private lemma beq_sub_mul_congr (e f a a' b b' : Poly)
    (ha : PPT.beq a a' = true) (hb : PPT.beq b b' = true) :
    PPT.beq (PPT.sub (PPT.mul e a) (PPT.mul f b))
            (PPT.sub (PPT.mul e a') (PPT.mul f b')) = true := by
  have ha' := beq_eq ha; have hb' := beq_eq hb
  show PPT.beq _ _ = true
  simp only [PPT.beq, beq_iff_eq]
  exact trim_sub_congr _ _ _ _ (trim_mul_congr e a a' ha') (trim_mul_congr f b b' hb')

/-- `monome k` has size `k + 1`. -/
private lemma monome_size (k : Nat) : (PPT.monome k).size = k + 1 := by
  simp [PPT.monome, Array.size_setIfInBounds, Array.size_ofFn]

/-- Coefficient of `monome k`: `1` at index `k`, `0` elsewhere. -/
private lemma monome_getElem_bang (k i : Nat) :
    (PPT.monome k)[i]! = if i = k then 1 else 0 := by
  simp only [PPT.monome]
  show (if h : i < ((Array.ofFn (n := k+1) fun _ => (0 : Int)).setIfInBounds k 1).size
    then ((Array.ofFn (n := k+1) fun _ => (0 : Int)).setIfInBounds k 1)[i] else default) = _
  simp only [Array.size_setIfInBounds, Array.size_ofFn]
  by_cases hi : i < k + 1
  · simp only [hi, dite_true]
    rw [Array.getElem_setIfInBounds (by simp [Array.size_ofFn]; omega)]
    by_cases hik : k = i
    · simp [hik]
    · simp [hik, show i ≠ k from fun h => hik h.symm, Array.getElem_ofFn]
  · simp only [hi, dite_false, show (default : Int) = 0 from rfl]
    simp [show i ≠ k from by omega]

/-- Foldl with zero addends: if the indicator `(if i = k then 1 else 0)` is 0
    for all `i ∈ l`, the foldl returns `init`. -/
private lemma foldl_zero_terms (l : List Nat) (x : Int) (k : Nat) (init : Int)
    (h : ∀ i ∈ l, i ≠ k) :
    List.foldl (fun acc i => acc + (if i = k then (1 : Int) else 0) * x ^ i) init l = init := by
  induction l generalizing init with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldl_cons, if_neg (h j List.mem_cons_self), Int.zero_mul, add_zero]
    exact ih _ (fun i hi => h i (List.mem_cons_of_mem j hi))

/-- `eval (monome k) x = x ^ k`. -/
private lemma eval_monome (k : Nat) (x : Int) :
    PPT.eval (PPT.monome k) x = x ^ k := by
  rw [eval_eq_polySum]
  simp only [polySum, monome_size]
  -- polySum = Σ_{i < k+1} (monome k)[i]! * x^i
  -- Replace (monome k)[i]! with indicator
  rw [show ∀ init, List.foldl (fun acc i => acc + (PPT.monome k)[i]! * x ^ i) init
      (List.range (k + 1)) =
    List.foldl (fun acc i => acc + (if i = k then (1 : Int) else 0) * x ^ i) init
      (List.range (k + 1)) from fun init => by
    apply list_foldl_congr' (fun i _ acc => by rw [monome_getElem_bang])]
  -- Split range(k+1) = range(k) ++ [k]
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      foldl_zero_terms _ _ _ _ (fun i hi => by have := List.mem_range.mp hi; omega)]
  simp

/-- Exponent identity: `(m+2)(m+3)/2 + 1 = (m+3) + (m+1)(m+2)/2`. -/
private lemma exp_arith1 (m : Nat) :
    (m + 2) * (m + 3) / 2 + 1 = (m + 3) + (m + 1) * (m + 2) / 2 := by
  rw [show (m + 2) * (m + 3) = (m + 1) * (m + 2) + 2 * (m + 2) from by ring,
    Nat.add_mul_div_left _ _ (by omega : 0 < 2)]; omega

/-- Exponent identity: `(m+2)(m+3)/2 + 1 = (2m+4) + m(m+1)/2`. -/
private lemma exp_arith2 (m : Nat) :
    (m + 2) * (m + 3) / 2 + 1 = (2 * m + 4) + m * (m + 1) / 2 := by
  rw [show (m + 2) * (m + 3) = m * (m + 1) + 2 * (2 * m + 3) from by ring,
    Nat.add_mul_div_left _ _ (by omega : 0 < 2)]; omega

/-- **Lemma A.** `detFormula` satisfies the 2-term recurrence.
    *Proof.* By `trim_eq_of_eval_eq`: show both sides agree on all integers.
    Unfold `detFormula` and `dSeq`, expand via `eval_mul`/`eval_sub`,
    then close by exponent arithmetic. -/
theorem detFormula_rec (m : Nat) : checkDetFormulaRec m = true := by
  simp only [checkDetFormulaRec, PPT.beq, beq_iff_eq]
  apply trim_eq_of_eval_eq; intro x
  simp only [detFormula]
  -- Unfold dSeq(m+3)
  conv_lhs => rw [show m + 2 + 1 = m + 3 from by omega]
  have hdseq : dSeq (m + 3) = sub (mul (monome 1) (dSeq (m + 2)))
        (mul (monome 1) (dSeq (m + 1))) := by
    have : m + 3 = (m + 1) + 2 := by omega
    rw [this]; simp only [dSeq]
  conv_lhs => rw [show m + 2 + 1 = m + 3 from by omega]
  rw [eval_mul, hdseq, eval_sub, eval_mul, eval_mul, eval_monome, eval_monome, pow_one]
  conv_rhs => rw [show m + 1 + 1 = m + 2 from by omega]
  simp only [eval_sub, eval_mul, eval_monome]
  set D₂ := PPT.eval (dSeq (m + 2)) x
  set D₁ := PPT.eval (dSeq (m + 1)) x
  set E := (m + 2) * (m + 3) / 2
  have h1 := exp_arith1 m
  have h2 := exp_arith2 m
  have hL : x ^ E * (x * D₂ - x * D₁) =
      x ^ (E + 1) * D₂ - x ^ (E + 1) * D₁ := by
    rw [mul_sub]; congr 1 <;> rw [← mul_assoc, ← pow_succ]
  have hR : x ^ (m + 3) * (x ^ ((m + 1) * (m + 2) / 2) * D₂) -
      x ^ (2 * m + 4) * (x ^ (m * (m + 1) / 2) * D₁) =
      x ^ (E + 1) * D₂ - x ^ (E + 1) * D₁ := by
    congr 1 <;> [rw [← mul_assoc, ← pow_add, h1]; rw [← mul_assoc, ← pow_add, h2]]
  rw [hL, hR]

/-- `PPT.binom` agrees with `Nat.choose`. -/
private lemma binom_eq_choose : ∀ n k, PPT.binom n k = ↑(Nat.choose n k) := by
  intro n; induction n with
  | zero => intro k; cases k <;> simp [PPT.binom]
  | succ n ih =>
    intro k; cases k with
    | zero => simp [PPT.binom]
    | succ k => rw [PPT.binom, ih k, ih (k + 1), Nat.choose_succ_succ]; push_cast; ring

/-- `PPT.catalan` agrees with Mathlib's `catalan`. -/
private lemma catalan_eq (l : Nat) : PPT.catalan l = ↑(_root_.catalan l) := by
  simp only [PPT.catalan, binom_eq_choose, _root_.catalan_eq_centralBinom_div, Nat.centralBinom]
  exact Int.natCast_ediv _ _

/-- `eval` distributes over `List.foldl PPT.add`. -/
private lemma eval_foldl_add (init : Poly) (terms : List Poly) (x : Int) :
    PPT.eval (terms.foldl PPT.add init) x =
    terms.foldl (fun acc t => acc + PPT.eval t x) (PPT.eval init x) := by
  induction terms generalizing init with
  | nil => rfl
  | cons t ts ih => simp only [List.foldl_cons]; rw [ih, eval_add]

/-- Evaluating `PPT.moment k` at integer `x` gives `ClosedFormDet.M ↑x k`.
    *Proof.* Distribute `eval` over the `foldl add` in `moment`, apply
    `eval_smul` + `eval_monome` to each term, then use `binom_eq_choose`
    and `catalan_eq` for coefficient agreement. -/
private lemma eval_moment_eq_M (k : Nat) (x : Int) :
    (↑(PPT.eval (PPT.moment k) x) : ℝ) = ClosedFormDet.M (↑x : ℝ) k := by
  simp only [PPT.moment]
  rw [eval_foldl_add, show PPT.eval (#[] : Poly) x = 0 from by simp [PPT.eval]]
  simp only [List.foldl_map]
  -- LHS: foldl (fun acc l => acc + eval(smul(coeff, monome(exp))) x) 0 (range(k/2+1))
  -- Simplify each term: eval(smul c (monome n)) x = c * x^n
  have hterm : ∀ l, PPT.eval (PPT.smul (PPT.binom k (2 * l) * PPT.catalan l)
      (PPT.monome (k - l))) x =
      ↑(Nat.choose k (2 * l) * _root_.catalan l) * x ^ (k - l) := by
    intro l; simp only [eval_smul, eval_monome, binom_eq_choose,
      Nat.cast_mul, mul_assoc]; congr 1; congr 1; exact catalan_eq l
  simp_rw [hterm]
  simp only [ClosedFormDet.M]
  rw [← finset_sum_eq_foldl]; push_cast
  apply Finset.sum_congr rfl; intro i _; ring

/-- `↑(eval(dSeq n) x) = d(↑x, n)`: both satisfy the same recurrence. -/
private lemma eval_dSeq_eq_d (n : Nat) (x : Int) :
    (↑(PPT.eval (dSeq n) x) : ℝ) = ClosedFormDet.d (↑x : ℝ) n := by
  suffices h : ∀ k, (↑(PPT.eval (dSeq k) x) : ℝ) = ClosedFormDet.d (↑x) k ∧
      (↑(PPT.eval (dSeq (k + 1)) x) : ℝ) = ClosedFormDet.d (↑x) (k + 1) from (h n).1
  intro k; induction k with
  | zero =>
    exact ⟨by simp [dSeq, PPT.const, PPT.eval, ClosedFormDet.d],
           by simp [dSeq, eval_monome, ClosedFormDet.d]⟩
  | succ k ih =>
    exact ⟨ih.2, by
      have hdseq : dSeq (k + 2) = sub (mul (monome 1) (dSeq (k + 1)))
          (mul (monome 1) (dSeq k)) := by
        conv_lhs => rw [show k + 2 = k + 2 from rfl]; unfold dSeq
      rw [hdseq, eval_sub, eval_mul, eval_mul, eval_monome]
      push_cast; rw [ih.2, ih.1]; simp [pow_one, ClosedFormDet.d]⟩

/-- `↑(eval(detFormula m) x) = hankelH(↑x, m).det`. -/
private lemma eval_detFormula_eq_hankel (m : Nat) (x : Int) :
    (↑(PPT.eval (detFormula m) x) : ℝ) = (ClosedFormDet.hankelH (↑x : ℝ) m).det := by
  rw [ClosedFormDet.det_hankel_main]
  show (↑(PPT.eval (mul (monome (m * (m + 1) / 2)) (dSeq (m + 1))) x) : ℝ) = _
  rw [eval_mul, eval_monome]; push_cast; rw [eval_dSeq_eq_d]

/-- Numerical cofactor expansion: cofactor det of an integer matrix. -/
private noncomputable def intDet : (n : Nat) → (Fin n → Fin n → Int) → Int
  | 0, _ => 1
  | 1, f => f 0 0
  | n + 2, f =>
    ∑ j : Fin (n + 2), (-1 : Int) ^ (↑j : Nat) * f 0 j *
      intDet (n + 1) (fun i' j' => f i'.succ (j.succAbove j'))

/-- `intDet` agrees with `Matrix.det` over ℝ. -/
private lemma intDet_eq_matrix_det : ∀ (n : Nat) (f : Fin n → Fin n → Int),
    (↑(intDet n f) : ℝ) = (Matrix.of (fun i j => (↑(f i j) : ℝ))).det := by
  intro n; induction n using Nat.strongRecOn with | _ n ih => ?_
  intro f
  match n with
  | 0 => simp [intDet, Matrix.det_isEmpty]
  | 1 =>
    simp only [intDet]
    rw [Matrix.det_unique]; simp [Matrix.of_apply]
  | n + 2 =>
    simp only [intDet]
    rw [Matrix.det_succ_row_zero]
    push_cast
    apply Finset.sum_congr rfl; intro j _
    have hf0 : (↑(f 0 j) : ℝ) = (Matrix.of (fun i j => (↑(f i j) : ℝ))) 0 j := by
      simp [Matrix.of_apply]
    have hdet : (↑(intDet (n + 1) (fun i' j' => f i'.succ (j.succAbove j'))) : ℝ) =
        ((Matrix.of (fun i j => (↑(f i j) : ℝ))).submatrix Fin.succ j.succAbove).det := by
      rw [ih (n + 1) (by omega)]; congr 1
    rw [hf0, hdet]

-- ── Bridge: PPT.eval(PPT.det M) = intDet ────────────────────────────────

/-- `Fin.succAbove j k` as natural: `if k < j then k else k + 1`. -/
private lemma succAbove_val (n : Nat) (j : Fin (n + 1)) (k : Fin n) :
    (j.succAbove k).val = if k.val < j.val then k.val else k.val + 1 := by
  simp only [Fin.succAbove]
  split
  · rename_i h
    simp only [Fin.val_castSucc]
    have : k.val < j.val := h
    simp [this]
  · rename_i h
    simp only [Fin.val_succ]
    have : ¬(k.val < j.val) := fun hlt => h hlt
    simp [this]

/-- Sign: `(if j % 2 == 0 then 1 else -1) = (-1)^j`. -/
private lemma sign_eq_neg_one_pow (j : Nat) :
    (if j % 2 == 0 then (1 : Int) else -1) = (-1) ^ j := by
  induction j with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← ih]
    by_cases hk : k % 2 = 0
    · have : (k + 1) % 2 = 1 := by omega
      simp [hk, this]
    · have : (k + 1) % 2 = 0 := by omega
      simp [hk, this]

/-- Foldl with `add` over `map` equals foldl with composed function. -/
private lemma foldl_add_map {α : Type} (l : List α) (g : α → Poly) (init : Poly) :
    (l.map g).foldl PPT.add init = l.foldl (fun acc a => PPT.add acc (g a)) init := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.foldl_cons]; exact ih _

/-- `eval (const 0) x = 0`. -/
private lemma eval_const_zero (x : Int) : PPT.eval (PPT.const 0) x = 0 := by
  simp [PPT.const, PPT.eval]

/-- `eval (const 1) x = 1`. -/
private lemma eval_const_one (x : Int) : PPT.eval (PPT.const 1) x = 1 := by
  simp [PPT.const, PPT.eval]

/-- Row index of `minor M 0 j`: the i-th row is row (i+1) of M. -/
private lemma minor_row_index (n i : Nat) (hi : i < n + 1) :
    ((List.range (n + 2)).filter (· ≠ 0)).toArray[i]'(by
      rw [List.size_toArray, PPT.filter_ne_range_length (n + 2) 0 (by omega)]; exact hi) =
    i + 1 := by
  rw [List.getElem_toArray]
  exact PPT.filter_ne_zero_getElem (n + 2) i (by omega)
    (by rw [PPT.filter_ne_range_length (n + 2) 0 (by omega)]; exact hi)

/-- Entry (i,k) of `minor M 0 j` = entry (i+1, if k < j then k else k+1) of M. -/
private lemma minor_entry_eq (M : Array (Array Poly)) (n j : Nat)
    (hM : M.size = n + 2) (hj : j < n + 2)
    (hsq : ∀ r, r < n + 2 → (M[r]!).size = n + 2)
    (i k : Nat) (hi : i < n + 1) (hk : k < n + 1) :
    ((PPT.minor M 0 j)[i]!)[k]! = (M[i + 1]!)[if k < j then k else k + 1]! := by
  have hrow_sz : (M[i + 1]!).size = n + 2 := hsq (i + 1) (by omega)
  -- Key filter facts
  have hrl : ((List.range (n + 2)).filter (· ≠ 0)).length = n + 1 :=
    PPT.filter_ne_range_length (n + 2) 0 (by omega)
  have hcol_len : ((List.range (n + 2)).filter (· ≠ j)).length = n + 1 :=
    PPT.filter_ne_range_length (n + 2) j hj
  have hrow_idx : ((List.range (n + 2)).filter (· ≠ 0))[i]'(by omega) = i + 1 :=
    PPT.filter_ne_zero_getElem (n + 2) i (by omega) (by omega)
  have hcol_idx : ((List.range (n + 2)).filter (· ≠ j))[k]'(by omega) =
      if k < j then k else k + 1 :=
    PPT.filter_ne_getElem_ite (n + 2) j k hj hk (by omega)
  -- Compute LHS step by step
  have hmsz : (PPT.minor M 0 j).size = n + 1 := by
    rw [PPT.minor_size M 0 j (by omega), hM]; omega
  have hi_lt : i < (PPT.minor M 0 j).size := by omega
  -- Convert [i]! to bounded [i]
  have h1 : (PPT.minor M 0 j)[i]! = (PPT.minor M 0 j)[i]'hi_lt := by
    simp [hi_lt]
  rw [h1]; clear h1
  -- Unfold minor: it is a mapped array
  -- minor M 0 j = rows.toArray.map (fun r => ...)
  -- [i]'_ on a mapped array gives the function applied to the i-th element
  show ((PPT.minor M 0 j)[i]'hi_lt)[k]! = _
  -- Unfold PPT.minor
  simp only [PPT.minor, Array.getElem_map, List.getElem_toArray, hM, hrow_idx, hrow_sz]
  -- Now goal: ((range (n+2)).filter(·≠j)).toArray.map(fun c => M[i+1]![c]!))[k]! = ...
  set row := ((List.range (n + 2)).filter (· ≠ j)).toArray.map (fun c => (M[i + 1]!)[c]!)
  have hk_lt : k < row.size := by
    simp only [row, Array.size_map, List.size_toArray, hcol_len]; exact hk
  -- Convert [k]! to bounded [k]
  have h2 : row[k]! = row[k]'hk_lt := by simp [hk_lt]
  rw [h2]; clear h2
  simp only [row, Array.getElem_map, List.getElem_toArray, hcol_idx]

/-- Row sizes of minor. -/
private lemma minor_row_size (M : Array (Array Poly)) (n j i : Nat)
    (hM : M.size = n + 2) (hj : j < n + 2) (hi : i < n + 1)
    (hsq : ∀ r, r < n + 2 → (M[r]!).size = n + 2) :
    ((PPT.minor M 0 j)[i]!).size = n + 1 := by
  have hmsz : (PPT.minor M 0 j).size = n + 1 := by
    rw [PPT.minor_size M 0 j (by omega), hM]; omega
  rw [getElem!_pos (h := by rw [hmsz]; exact hi)]
  simp only [PPT.minor, Array.getElem_map, List.getElem_toArray,
      Array.size_map, List.size_toArray, hM]
  rw [PPT.filter_ne_zero_getElem (n + 2) i (by omega)
    (by rw [PPT.filter_ne_range_length (n + 2) 0 (by omega)]; exact hi)]
  rw [hsq (i + 1) (by omega)]
  rw [PPT.filter_ne_range_length (n + 2) j hj]; omega

/-- `eval(PPT.det M) x = intDet n (eval entries)`. -/
private lemma eval_ppt_det_eq_intDet : ∀ (n : Nat) (M : Array (Array Poly)) (x : Int),
    M.size = n →
    (∀ i, i < n → (M[i]!).size = n) →
    ∀ (f : Fin n → Fin n → Int),
    (∀ i j : Fin n, PPT.eval ((M[↑i]!)[↑j]!) x = f i j) →
    PPT.eval (PPT.det M) x = intDet n f := by
  intro n; induction n using Nat.strongRecOn with | _ n ih => ?_
  intro M x hM hsq f hf
  match n with
  | 0 =>
    have hdet : PPT.det M = PPT.const 1 := by
      rw [PPT.det.eq_1]; split <;> [rfl; omega; omega]
    simp only [intDet, hdet]; show PPT.eval (PPT.const 1) x = 1
    simp [PPT.const, PPT.eval]
  | 1 =>
    have hdet : PPT.det M = (M[0]!)[0]! := by
      rw [PPT.det.eq_1]; split <;> [omega; rfl; omega]
    rw [hdet]; exact hf ⟨0, by omega⟩ ⟨0, by omega⟩
  | n + 2 =>
    have hdet : PPT.det M = (List.range (n + 2)).foldl (fun acc j =>
        PPT.add acc (PPT.smul (if j % 2 == 0 then 1 else -1)
          (PPT.mul (M[0]!)[j]! (PPT.det (PPT.minor M 0 j))))) (PPT.const 0) := by
      rw [PPT.det.eq_1]; split <;> [omega; omega; simp_all]
    rw [hdet]
    simp only [intDet]
    -- Distribute eval over foldl, convert to Finset.sum
    have heval : PPT.eval ((List.range (n + 2)).foldl (fun acc j =>
        PPT.add acc (PPT.smul (if j % 2 == 0 then 1 else -1)
          (PPT.mul (M[0]!)[j]! (PPT.det (PPT.minor M 0 j))))) (PPT.const 0)) x =
      ∑ j ∈ Finset.range (n + 2),
        PPT.eval (PPT.smul (if j % 2 == 0 then 1 else -1)
          (PPT.mul (M[0]!)[j]! (PPT.det (PPT.minor M 0 j)))) x := by
      rw [← foldl_add_map]
      rw [eval_foldl_add, eval_const_zero]
      rw [List.foldl_map, ← finset_sum_eq_foldl]
    rw [heval]; simp only [Finset.sum_range]
    apply Finset.sum_congr rfl; intro ⟨j, hj⟩ _
    rw [eval_smul, eval_mul, sign_eq_neg_one_pow]
    -- Goal: (-1)^j * (eval M[0]![j]! x * eval (det (minor M 0 j)) x) = (-1)^j * f 0 ⟨j,hj⟩ * intDet ...
    have hminor_sz := PPT.minor_size M 0 j (by omega)
    rw [hM] at hminor_sz; simp at hminor_sz
    let J : Fin (n + 2) := ⟨j, hj⟩
    suffices hih : PPT.eval (PPT.det (PPT.minor M 0 j)) x =
        intDet (n + 1) (fun i' j' => f i'.succ (J.succAbove j')) by
      rw [hih]; simp only [J]; erw [hf ⟨0, by omega⟩ ⟨j, hj⟩]
      simp [mul_assoc]
    exact ih (n + 1) (by omega) (PPT.minor M 0 j) x hminor_sz
      (fun i hi_i => minor_row_size M n j i hM hj hi_i hsq)
      (fun i' j' => f i'.succ (J.succAbove j'))
      (fun ⟨i', hi'⟩ ⟨k', hk'⟩ => by
        simp only [J]
        -- Goal: eval (minor M 0 j)[i']![k']! x = f (Fin.succ ⟨i', hi'⟩) (⟨j, hj⟩.succAbove ⟨k', hk'⟩)
        have hme := minor_entry_eq M n j hM hj hsq i' k' hi' hk'
        -- hme : (minor M 0 j)[i']![k']! = M[i'+1]![if k' < j then k' else k'+1]!
        erw [hme]
        -- Now: eval M[i'+1]![if k' < j then k' else k'+1]! x = ...
        -- Goal: eval M[i'+1]![if k' < j then k' else k'+1]! x = f (succ ⟨i', hi'⟩) (succAbove ⟨j,hj⟩ ⟨k',hk'⟩)
        -- RHS: f ⟨i'+1, _⟩ ⟨succAbove, _⟩ where succAbove = if k' < j then k' else k'+1
        -- Use hf with these Fin indices
        have hsa := succAbove_val (n + 1) ⟨j, hj⟩ ⟨k', hk'⟩
        -- hsa: (succAbove ⟨j,hj⟩ ⟨k',hk'⟩).val = if k' < j then k' else k'+1
        -- So M[i'+1]![if ...] = M[↑(succ ⟨i',hi'⟩)]![↑(succAbove ...)]!
        have key := hf (Fin.succ ⟨i', hi'⟩) ((⟨j, hj⟩ : Fin (n + 2)).succAbove ⟨k', hk'⟩)
        -- key: eval M[↑(succ ⟨i',hi'⟩)]![↑(succAbove ...)]! x = f (succ ⟨i',hi'⟩) (succAbove ...)
        -- The goal has same thing with different notation
        -- key and goal differ only in Fin↔Nat coercions
        convert key using 1
        congr 1; congr 1; simp [hsa])

/-- `arr[i]! = arr[i]` for any `Inhabited` element type. -/
private lemma arr_gb {α : Type} [Inhabited α] (arr : Array α) (i : Nat) (h : i < arr.size) :
    arr[i]! = arr[i] := by
  show (if h' : i < arr.size then arr[i] else default) = arr[i]; simp [h]

/-- Row `i` of `hankelB m`. -/
private lemma hankelB_row (m i : Nat) (hi : i < m + 1) :
    (hankelB m)[i]! =
    Array.ofFn (n := m + 1) fun j =>
      ((List.range (2 * m + 3)).map PPT.moment).toArray[i + j.val + 1]! := by
  rw [arr_gb _ _ (by simp [hankelB, Array.size_ofFn]; omega)]
  simp [hankelB, Array.getElem_ofFn]

/-- Entry (i,j) of `hankelB m` is `moment(i+j+1)`. -/
private lemma hankelB_entry (m i j : Nat) (hi : i < m + 1) (hj : j < m + 1) :
    ((hankelB m)[i]!)[j]! = PPT.moment (i + j + 1) := by
  rw [hankelB_row m i hi]
  have hj' : j < (Array.ofFn (n := m + 1) fun jj : Fin (m + 1) =>
    ((List.range (2 * m + 3)).map PPT.moment).toArray[i + jj.val + 1]!).size := by
    simp [Array.size_ofFn]; omega
  rw [arr_gb _ _ hj', Array.getElem_ofFn]
  have hij : i + j + 1 < ((List.range (2 * m + 3)).map PPT.moment).toArray.size := by
    simp [List.size_toArray, List.length_map, List.length_range]; omega
  rw [arr_gb _ _ hij, List.getElem_toArray, List.getElem_map, List.getElem_range]

/-- Bridge: evaluating `detB m` at integer `x` gives the ℝ Hankel determinant. -/
private lemma eval_detB_eq_hankel_det (m : Nat) (x : Int) :
    (↑(PPT.eval (detB m) x) : ℝ) = (ClosedFormDet.hankelH (↑x : ℝ) m).det := by
  set f : Fin (m + 1) → Fin (m + 1) → Int :=
    fun i j => PPT.eval (PPT.moment (↑i + ↑j + 1)) x
  have hBsz : (hankelB m).size = m + 1 := by simp [hankelB, Array.size_ofFn]
  have hBsq : ∀ i, i < m + 1 → ((hankelB m)[i]!).size = m + 1 := by
    intro i hi; rw [hankelB_row m i hi]; exact Array.size_ofFn
  have hBentry : ∀ i j : Fin (m + 1),
      PPT.eval (((hankelB m)[↑i]!)[↑j]!) x = f i j := by
    intro ⟨i, hi⟩ ⟨j, hj⟩; simp only [f]; congr 1
    exact hankelB_entry m i j hi hj
  have h1 : PPT.eval (detB m) x = intDet (m + 1) f :=
    eval_ppt_det_eq_intDet (m + 1) (hankelB m) x hBsz hBsq f hBentry
  have h2 : (↑(intDet (m + 1) f) : ℝ) = (ClosedFormDet.hankelH (↑x : ℝ) m).det := by
    rw [intDet_eq_matrix_det]; congr 1; ext ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Matrix.of_apply, ClosedFormDet.hankelH]
    exact eval_moment_eq_M (i + j + 1) x
  rw [h1, h2]

/-- The ℝ Hankel determinant satisfies the 2-term recurrence. -/
private lemma hankel_det_rec_real (lam : ℝ) (m : Nat) :
    (ClosedFormDet.hankelH lam (m + 2)).det =
    lam ^ (m + 3) * (ClosedFormDet.hankelH lam (m + 1)).det -
    lam ^ (2 * m + 4) * (ClosedFormDet.hankelH lam m).det := by
  rw [ClosedFormDet.det_hankel_main, ClosedFormDet.det_hankel_main,
      ClosedFormDet.det_hankel_main]
  show lam ^ ((m + 2) * (m + 3) / 2) *
    (lam * ClosedFormDet.d lam (m + 2) - lam * ClosedFormDet.d lam (m + 1)) =
    lam ^ (m + 3) * (lam ^ ((m + 1) * (m + 2) / 2) * ClosedFormDet.d lam (m + 2)) -
    lam ^ (2 * m + 4) * (lam ^ (m * (m + 1) / 2) * ClosedFormDet.d lam (m + 1))
  set D₂ := ClosedFormDet.d lam (m + 2)
  set D₁ := ClosedFormDet.d lam (m + 1)
  set E := (m + 2) * (m + 3) / 2
  have h1 := exp_arith1 m
  have h2 := exp_arith2 m
  have hL : lam ^ E * (lam * D₂ - lam * D₁) =
      lam ^ (E + 1) * D₂ - lam ^ (E + 1) * D₁ := by
    rw [mul_sub]; congr 1 <;> rw [← mul_assoc, ← pow_succ]
  have hR : lam ^ (m + 3) * (lam ^ ((m + 1) * (m + 2) / 2) * D₂) -
      lam ^ (2 * m + 4) * (lam ^ (m * (m + 1) / 2) * D₁) =
      lam ^ (E + 1) * D₂ - lam ^ (E + 1) * D₁ := by
    congr 1 <;> [rw [← mul_assoc, ← pow_add, h1]; rw [← mul_assoc, ← pow_add, h2]]
  rw [hL, hR]

/-- **Lemma B.** `detB` satisfies the same 2-term recurrence.
    *Proof.* Bridge through the ℝ theorem: `eval(detB m) x` equals the ℝ Hankel
    determinant at `λ = ↑x`, which satisfies the recurrence by `det_hankel_main`. -/
theorem detB_rec (m : Nat) : checkDetBRec m = true := by
  simp only [checkDetBRec, PPT.beq, beq_iff_eq]
  apply trim_eq_of_eval_eq; intro x
  rw [eval_sub, eval_mul, eval_mul, eval_monome, eval_monome]
  -- Cast to ℝ and use the ℝ recurrence
  suffices h : (↑(PPT.eval (detB (m + 2)) x) : ℝ) =
      ↑(x ^ (m + 3) * PPT.eval (detB (m + 1)) x -
        x ^ (2 * m + 4) * PPT.eval (detB m) x) by exact_mod_cast h
  push_cast
  rw [eval_detB_eq_hankel_det, eval_detB_eq_hankel_det, eval_detB_eq_hankel_det]
  exact hankel_det_rec_real (↑x) m

/-- **General theorem (computational formulation).**
    `det(B_m) = λ^{m(m+1)/2} · d_{m+1}` for all `m`.
    *Proof.* By strong induction using pair `P(n) ∧ P(n+1)`.
    Base cases `m=0,1` by `native_decide`.  Inductive step: both
    `detB` and `detFormula` satisfy the same 2-term recurrence
    (Lemmas A, B); substituting IH via congruence (Lemma C) closes the step. -/
theorem det_hankel_general (m : Nat) : checkDetFormula m = true := by
  suffices h : ∀ n, checkDetFormula n = true ∧ checkDetFormula (n + 1) = true from (h m).1
  intro n
  induction n with
  | zero => exact ⟨closed_form_det_m0, closed_form_det_m1⟩
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    -- Chain: detB(k+2) ≡ recurrence(detB) ≡ recurrence(detFormula) ≡ detFormula(k+2)
    exact beq_trans
      (beq_trans (detB_rec k)
        (beq_sub_mul_congr _ _ _ _ _ _ ih.2 ih.1))
      (beq_symm (detFormula_rec k))

end PPT
