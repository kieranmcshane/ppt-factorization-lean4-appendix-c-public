import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.NumberTheory.Divisors
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.Nat.Totient

/-!
# Reliquat cyclotomique : `cyclotomicRemainder m * (X − 1) = X^{m+2} − 1`

## Description

Ce fichier formalise en Lean 4 / Mathlib4 l'identité cyclotomique fondamentale
et la factorisation du polynôme `(X^n − 1)/(X − 1)` comme produit de
cyclotomiques.

1. **§1 — Identité cyclotomique** :
   `∏_{d ∣ n} Φ_d(X) = X^n − 1` dans `Polynomial ℤ`, avec le corollaire
   quotient `∏_{d ∣ b, d ∤ a} Φ_d · (X^a − 1) = X^b − 1`.

2. **§2 — Reliquat cyclotomique** :
   Le reliquat `cyclotomicRemainder m := ∏_{d ∣ (m+2), d ≥ 2} Φ_d(X)`
   satisfait `cyclotomicRemainder m * (X − 1) = X^{m+2} − 1`.
   On montre également que `cyclotomicFactor k = cyclotomicRemainder k`
   (les diviseurs de `k+2` qui ne divisent pas `k+1` sont exactement
   ceux `≥ 2`, car `gcd(k+1, k+2) = 1`).

3. **§3 — Énoncé synthétique** :
   Reformulation globale : `X^{m+2} − 1 = (X−1) · cyclotomicRemainder m`.

## Références Mathlib4

- `Polynomial.cyclotomic`                        in `Mathlib.RingTheory.Polynomial.Cyclotomic.Basic`
- `Polynomial.prod_cyclotomic_eq_X_pow_sub_one`  (ibid.)
- `Finset.prod`, `∏` notation                    in `Mathlib.Algebra.BigOperators.Group.Finset`
-/


open scoped BigOperators Polynomial
open Polynomial Nat Finset

namespace MoebiusCyclotomic

-- ============================================================================
-- §1. Identité cyclotomique fondamentale
-- ============================================================================

section IdentiteCyclotomique

/-- **Lemme 1a.** `∏ d ∈ n.divisors, Φ_d(X) = X^n − 1`. -/
lemma cyclotomic_prod_eq_xn_sub_one (n : ℕ) (hn : n ≠ 0) :
    ∏ d ∈ n.divisors, cyclotomic d ℤ = X ^ n - 1 :=
  prod_cyclotomic_eq_X_pow_sub_one (Nat.pos_of_ne_zero hn) ℤ

/-- **Lemme 1b.** Pour `a ∣ b`, `(∏_{d ∣ b, d ∤ a} Φ_d) * (X^a − 1) = X^b − 1`. -/
lemma cyclotomic_quotient_product
    (a b : ℕ) (hab : a ∣ b) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∏ d ∈ b.divisors.filter (fun d => ¬(d ∣ a)), cyclotomic d ℤ) *
    (X ^ a - 1) = X ^ b - 1 := by
  have hfa : b.divisors.filter (· ∣ a) = a.divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨fun h => ⟨h.2, ha⟩, fun h => ⟨⟨h.1.trans hab, hb⟩, h.1⟩⟩
  have hdisj : Disjoint (b.divisors.filter (· ∣ a))
                        (b.divisors.filter fun d => ¬(d ∣ a)) :=
    Finset.disjoint_filter.mpr fun _ _ h hn => hn h
  have key : (∏ d ∈ b.divisors.filter (· ∣ a), cyclotomic d ℤ) *
             (∏ d ∈ b.divisors.filter (fun d => ¬(d ∣ a)), cyclotomic d ℤ) =
             ∏ d ∈ b.divisors, cyclotomic d ℤ := by
    rw [← Finset.prod_union hdisj, Finset.filter_union_filter_not_eq]
  rw [← cyclotomic_prod_eq_xn_sub_one b hb, ← key, hfa,
      cyclotomic_prod_eq_xn_sub_one a ha]
  exact mul_comm _ _

/-- **Lemme 1c.** Coprimauté sur ℚ : `IsCoprime (Φ_m ℚ) (Φ_n ℚ)` pour `m ≠ n`.

    NB : sur ℤ[X] la coprimauté de Bézout est fausse en général
    (ex. Φ₁=X−1, Φ₂=X+1 : aucun a,b∈ℤ[X] ne satisfait a·Φ₁+b·Φ₂=1). -/
lemma cyclotomic_pairwise_coprime (m n : ℕ) (hmn : m ≠ n) :
    IsCoprime (cyclotomic m ℚ) (cyclotomic n ℚ) :=
  cyclotomic.isCoprime_rat hmn

end IdentiteCyclotomique

-- ============================================================================
-- §2. Reliquat cyclotomique
-- ============================================================================

section ReliquatCyclotomique

/-- Facteur élémentaire : `cyclotomicFactor k := ∏_{d ∣ (k+2), d ∤ (k+1)} Φ_d`. -/
noncomputable def cyclotomicFactor (k : ℕ) : Polynomial ℤ :=
  ∏ d ∈ (k + 2).divisors.filter (fun d => ¬(d ∣ (k + 1))), cyclotomic d ℤ

/-- Diviseurs survivants : `survivingDivisors m := {d ∣ m+2 | d ≥ 2}`. -/
def survivingDivisors (m : ℕ) : Finset ℕ :=
  (m + 2).divisors.filter (fun d => 2 ≤ d)

/-- Reliquat cyclotomique : `cyclotomicRemainder m := ∏_{d ∈ survivingDivisors m} Φ_d`. -/
noncomputable def cyclotomicRemainder (m : ℕ) : Polynomial ℤ :=
  ∏ d ∈ survivingDivisors m, cyclotomic d ℤ

-- --------------------------------------------------------------------------
-- Propriétés de survivingDivisors
-- --------------------------------------------------------------------------

lemma survivingDivisors_subset (m : ℕ) :
    survivingDivisors m ⊆ (m + 2).divisors :=
  Finset.filter_subset _ _

lemma one_not_mem_survivingDivisors (m : ℕ) :
    1 ∉ survivingDivisors m := by
  simp [survivingDivisors]

lemma self_mem_survivingDivisors (m : ℕ) :
    m + 2 ∈ survivingDivisors m := by
  simp [survivingDivisors, Nat.mem_divisors]

lemma survivingDivisors_eq_divisors_erase_one (m : ℕ) :
    survivingDivisors m = (m + 2).divisors.filter (fun d => d ≠ 1) := by
  ext d
  simp only [survivingDivisors, Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd, hn⟩, hge⟩; exact ⟨⟨hd, hn⟩, by omega⟩
  · rintro ⟨⟨hd, hn⟩, hne⟩
    exact ⟨⟨hd, hn⟩, by have := Nat.pos_of_dvd_of_pos hd (by omega); omega⟩

/-- `survivingDivisors m = (m+2).divisors.filter (¬ · ∣ 1)`
    (raccord avec `cyclotomic_quotient_product 1 (m+2)`). -/
lemma survivingDivisors_eq_filter_not_dvd_one (m : ℕ) :
    survivingDivisors m = (m + 2).divisors.filter (fun d => ¬(d ∣ 1)) := by
  ext d
  simp only [survivingDivisors, Finset.mem_filter, Nat.mem_divisors, Nat.dvd_one]
  constructor
  · rintro ⟨⟨hd, hn⟩, hge⟩; exact ⟨⟨hd, hn⟩, by omega⟩
  · rintro ⟨⟨hd, hn⟩, hne⟩
    exact ⟨⟨hd, hn⟩, by have := Nat.pos_of_dvd_of_pos hd (by omega); omega⟩

-- --------------------------------------------------------------------------
-- Lemme clé : cyclotomicFactor k = cyclotomicRemainder k
-- --------------------------------------------------------------------------

/-- `cyclotomicFactor k = cyclotomicRemainder k`.

    Car `gcd(k+1, k+2) = 1` : tout `d ≥ 2` divisant `k+2` ne divise pas `k+1`. -/
lemma cyclotomicFactor_eq_remainder (k : ℕ) :
    cyclotomicFactor k = cyclotomicRemainder k := by
  unfold cyclotomicFactor cyclotomicRemainder survivingDivisors
  congr 1
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd, hn⟩, hnd⟩
    refine ⟨⟨hd, hn⟩, ?_⟩
    by_contra hlt
    push_neg at hlt
    have hpos : 0 < d := Nat.pos_of_dvd_of_pos hd (by omega)
    have hd1 : d = 1 := by omega
    exact hnd (hd1 ▸ one_dvd (k + 1))
  · rintro ⟨⟨hd, hn⟩, hge⟩
    refine ⟨⟨hd, hn⟩, ?_⟩
    intro hdk1
    have hcop : Nat.Coprime (k + 1) (k + 2) := by
      rw [show k + 2 = k + 1 + 1 from by omega, Nat.coprime_self_add_right]
      exact (Nat.coprime_one_right_iff _).mpr trivial
    have h1 : d ∣ Nat.gcd (k + 1) (k + 2) := Nat.dvd_gcd hdk1 hd
    rw [hcop] at h1
    exact absurd (Nat.dvd_one.mp h1) (by omega)

-- --------------------------------------------------------------------------
-- Théorème central
-- --------------------------------------------------------------------------

/-- **Théorème central.** `cyclotomicRemainder m * (X − 1) = X^{m+2} − 1`.

    Preuve : `cyclotomic_quotient_product 1 (m+2)` avec `1 ∣ m+2`. -/
theorem remainder_mul_X_sub_one (m : ℕ) :
    cyclotomicRemainder m * (X - 1) = X ^ (m + 2) - 1 := by
  have key := cyclotomic_quotient_product 1 (m + 2) (one_dvd _) (by omega) (by omega)
  simp only [pow_one] at key
  unfold cyclotomicRemainder
  rw [survivingDivisors_eq_filter_not_dvd_one]
  exact key

/-- **Corollaire.** `cyclotomicFactor k * (X − 1) = X^{k+2} − 1`. -/
theorem cyclotomicFactor_mul_X_sub_one (k : ℕ) :
    cyclotomicFactor k * (X - 1) = X ^ (k + 2) - 1 := by
  rw [cyclotomicFactor_eq_remainder]
  exact remainder_mul_X_sub_one k

/-- **Corollaire 2b.** Si `m + 2 = 2^r` (`r ≥ 1`), le reliquat ne contient
    que les cyclotomiques aux puissances de 2. -/
theorem cyclotomic_remainder_prime_power_of_two
    (m r : ℕ) (hm : m + 2 = 2 ^ r) :
    cyclotomicRemainder m =
      ∏ i ∈ (Finset.range r).image (fun i => 2 ^ (i + 1)),
        cyclotomic i ℤ := by
  unfold cyclotomicRemainder survivingDivisors
  rw [hm]
  -- Montrer que les deux finsets sont égaux, puis conclure par prod_congr.
  apply Finset.prod_congr _ (fun x _ => rfl)
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, ne_eq, Finset.mem_image, Finset.mem_range]
  have hp2 : Nat.Prime 2 := Nat.prime_two
  constructor
  · rintro ⟨⟨hd, _⟩, hge⟩
    rw [Nat.dvd_prime_pow hp2] at hd
    obtain ⟨j, hjr, rfl⟩ := hd
    have hj : 1 ≤ j := by
      rcases j with _ | j
      · norm_num at hge
      · omega
    exact ⟨j - 1, by omega, by congr 1; omega⟩
  · rintro ⟨j, hjr, rfl⟩
    refine ⟨⟨Nat.pow_dvd_pow 2 (by omega), by norm_num⟩, ?_⟩
    calc 2 = 2 ^ 1 := (pow_one 2).symm
         _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **Corollaire 2c.** `(cyclotomicRemainder m).natDegree = ∑_{d ∈ survivingDivisors m} φ(d)`. -/
theorem cyclotomic_remainder_natDegree (m : ℕ) :
    (cyclotomicRemainder m).natDegree =
      ∑ d ∈ survivingDivisors m, (cyclotomic d ℤ).natDegree := by
  unfold cyclotomicRemainder
  exact Polynomial.natDegree_prod (survivingDivisors m) (fun d => cyclotomic d ℤ)
    (fun d _ => cyclotomic_ne_zero d ℤ)

/-- **Corollaire 2d.** `(cyclotomicRemainder m).natDegree = m + 1`. -/
theorem cyclotomic_remainder_natDegree_eq (m : ℕ) :
    (cyclotomicRemainder m).natDegree = m + 1 := by
  rw [cyclotomic_remainder_natDegree]
  simp only [survivingDivisors, Polynomial.natDegree_cyclotomic]
  -- Goal: ∑ d ∈ (m+2).divisors.filter (2 ≤ ·), φ(d) = m + 1
  -- Stratégie : séparer d=1 via erase, sans rw sur m+2 dans le LHS.
  have htot : ∑ d ∈ (m + 2).divisors, Nat.totient d = m + 2 := Nat.sum_totient (m + 2)
  have h1mem : (1 : ℕ) ∈ (m + 2).divisors := by
    rw [Nat.mem_divisors]; exact ⟨one_dvd _, by omega⟩
  have herase : (m + 2).divisors.erase 1 = (m + 2).divisors.filter (fun d => 2 ≤ d) := by
    ext d
    simp only [Finset.mem_erase, ne_eq, Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨hne, hdvd, hne0⟩
      refine ⟨⟨hdvd, hne0⟩, ?_⟩
      have hpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
      omega
    · rintro ⟨⟨hdvd, hne0⟩, hge⟩
      exact ⟨by omega, hdvd, hne0⟩
  rw [← herase]
  have hsum := Finset.sum_erase_add (m + 2).divisors Nat.totient h1mem
  simp only [Nat.totient_one] at hsum
  omega

end ReliquatCyclotomique

-- ============================================================================
-- §3. Énoncé synthétique
-- ============================================================================

section EnonceGlobal

/-- `cyclotomicRemainder m = ∏_{d ∣ m+2, d ≥ 2} Φ_d` (par définition). -/
theorem main_remainder_unfold (m : ℕ) :
    cyclotomicRemainder m =
    ∏ d ∈ (m + 2).divisors.filter (fun d => 2 ≤ d), cyclotomic d ℤ :=
  rfl

/-- **Théorème final.** `X^{m+2} − 1 = (X−1) · ∏_{d ∣ m+2, d ≥ 2} Φ_d`. -/
theorem xn_sub_one_factored (m : ℕ) :
    X ^ (m + 2) - 1 =
    (X - 1 : Polynomial ℤ) *
      ∏ d ∈ (m + 2).divisors.filter (fun d => 2 ≤ d), cyclotomic d ℤ := by
  rw [← main_remainder_unfold, mul_comm]
  exact (remainder_mul_X_sub_one m).symm

end EnonceGlobal

end MoebiusCyclotomic
