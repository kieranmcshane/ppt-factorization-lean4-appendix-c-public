import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import PptFactorization.General

/-!
# Moment–cumulant scaffold for the asymmetric PPT moments `c_k`

This file expresses `General.c₁ … General.c₇` as the moment–cumulant sum
applied to the specific free cumulants of the asymmetric PPT spectral
measure: `κ_{2m−1} = κ_{2m} = λ / d₁^{2m−1}` (see `General.lean` §14).

The moment–cumulant formula in free probability reads

    c_n = Σ_{π ∈ NC(n)} ∏_{B ∈ π} κ_{|B|}

which, grouping by block-size multiset `λ` of `n`, becomes

    c_n = Σ_{λ ⊢ n} N(n, λ) · ∏ᵢ κ_{λᵢ}

with Kreweras's formula

    N(n, λ)  =  (n! / (n − k + 1)!) / ∏ⱼ mⱼ!

where `k = #parts(λ)` and `mⱼ` is the multiplicity of the `j`-th distinct
part.  The Narayana-type multiplicities (`1, 6, 5, 15, …`) that appear as
numerals in the `cMC_k` definitions below are computed directly from
Kreweras.

## Deferred: NC-partition formalisation

The combinatorial identity `N(n, λ) = |NC(n, λ)|` is *axiomatised* here in
the informal sense: the Kreweras values are written as numerals in the
definitions, and no proof is provided that they count non-crossing
partitions of the given type.  Formalising `NCPart n` and proving
Kreweras's formula is left as future work — at that point

    cMC_n lam d₁  =  Σ_{π ∈ NC(n)} ∏_{B ∈ π} κ_{|B|}

will be a theorem.  Downstream code uses `cMC_k_eq : cMC_k lam d₁ =
General.c_k lam d₁` and is unaffected by the NC formalisation.

Institut Fourier, Grenoble — Kieran McShane / Cécilia Lancien
-/

namespace MomentCumulant

variable (lam d₁ : ℝ)

-- ═══════════════════════════════════════════════════════════════════
-- §1. Free cumulants
-- ═══════════════════════════════════════════════════════════════════

/-- Free cumulants of the asymmetric PPT spectral measure.
    `κ_{2m − 1} = κ_{2m} = λ / d₁^{2m − 1}`.  Defined directly for
    `n ≤ 7`; unused for `n ≥ 8`. -/
noncomputable def κ : ℕ → ℝ
  | 0     => 0
  | 1     => lam / d₁
  | 2     => lam / d₁
  | 3     => lam / d₁ ^ 3
  | 4     => lam / d₁ ^ 3
  | 5     => lam / d₁ ^ 5
  | 6     => lam / d₁ ^ 5
  | 7     => lam / d₁ ^ 7
  | _ + 8 => 0

@[simp] theorem κ_one   : κ lam d₁ 1 = lam / d₁     := rfl
@[simp] theorem κ_two   : κ lam d₁ 2 = lam / d₁     := rfl
@[simp] theorem κ_three : κ lam d₁ 3 = lam / d₁ ^ 3 := rfl
@[simp] theorem κ_four  : κ lam d₁ 4 = lam / d₁ ^ 3 := rfl
@[simp] theorem κ_five  : κ lam d₁ 5 = lam / d₁ ^ 5 := rfl
@[simp] theorem κ_six   : κ lam d₁ 6 = lam / d₁ ^ 5 := rfl
@[simp] theorem κ_seven : κ lam d₁ 7 = lam / d₁ ^ 7 := rfl

-- ═══════════════════════════════════════════════════════════════════
-- §2. Moment–cumulant expansion of c₁…c₇
-- ═══════════════════════════════════════════════════════════════════

/-- `c₁^{MC} = κ₁`.

    NC partitions of `[1]` (1 total):
    · `{{1}}`                   — type `(1)`, mult `1`.  -/
noncomputable def cMC_1 : ℝ := κ lam d₁ 1

/-- `c₂^{MC} = κ₂ + κ₁²`.

    NC partitions of `[2]` (2 total):
    · `{{1,2}}`                 — type `(2)`,   mult `1`
    · `{{1},{2}}`               — type `(1,1)`, mult `1`.  -/
noncomputable def cMC_2 : ℝ :=
  κ lam d₁ 2 + κ lam d₁ 1 ^ 2

/-- `c₃^{MC} = κ₃ + 3 κ₁ κ₂ + κ₁³`.

    NC partitions of `[3]` (C₃ = 5):
    · `(3)`      mult `1`
    · `(2,1)`    mult `3`
    · `(1,1,1)`  mult `1`.  -/
noncomputable def cMC_3 : ℝ :=
  κ lam d₁ 3 + 3 * κ lam d₁ 1 * κ lam d₁ 2 + κ lam d₁ 1 ^ 3

/-- `c₄^{MC} = κ₄ + 4 κ₁κ₃ + 2 κ₂² + 6 κ₁²κ₂ + κ₁⁴`.

    NC partitions of `[4]` (C₄ = 14):
    · `(4)`        mult `1`
    · `(3,1)`      mult `4`
    · `(2,2)`      mult `2`
    · `(2,1,1)`    mult `6`
    · `(1,1,1,1)`  mult `1`.  -/
noncomputable def cMC_4 : ℝ :=
  κ lam d₁ 4 +
  4 * κ lam d₁ 1 * κ lam d₁ 3 +
  2 * κ lam d₁ 2 ^ 2 +
  6 * κ lam d₁ 1 ^ 2 * κ lam d₁ 2 +
  κ lam d₁ 1 ^ 4

/-- `c₅^{MC} = κ₅ + 5 κ₁κ₄ + 5 κ₂κ₃ + 10 κ₁²κ₃ + 10 κ₁κ₂² + 10 κ₁³κ₂ + κ₁⁵`.

    NC partitions of `[5]` (C₅ = 42):
    · `(5)`          mult `1`
    · `(4,1)`        mult `5`
    · `(3,2)`        mult `5`
    · `(3,1,1)`      mult `10`
    · `(2,2,1)`      mult `10`
    · `(2,1,1,1)`    mult `10`
    · `(1,1,1,1,1)`  mult `1`.  -/
noncomputable def cMC_5 : ℝ :=
  κ lam d₁ 5 +
  5 * κ lam d₁ 1 * κ lam d₁ 4 +
  5 * κ lam d₁ 2 * κ lam d₁ 3 +
  10 * κ lam d₁ 1 ^ 2 * κ lam d₁ 3 +
  10 * κ lam d₁ 1 * κ lam d₁ 2 ^ 2 +
  10 * κ lam d₁ 1 ^ 3 * κ lam d₁ 2 +
  κ lam d₁ 1 ^ 5

/-- `c₆^{MC}`:

    NC partitions of `[6]` (C₆ = 132):
    · `(6)`            mult `1`
    · `(5,1)`          mult `6`
    · `(4,2)`          mult `6`
    · `(4,1,1)`        mult `15`
    · `(3,3)`          mult `3`
    · `(3,2,1)`        mult `30`
    · `(3,1,1,1)`      mult `20`
    · `(2,2,2)`        mult `5`
    · `(2,2,1,1)`      mult `30`
    · `(2,1,1,1,1)`    mult `15`
    · `(1,1,1,1,1,1)`  mult `1`.  -/
noncomputable def cMC_6 : ℝ :=
  κ lam d₁ 6 +
  6 * κ lam d₁ 1 * κ lam d₁ 5 +
  6 * κ lam d₁ 2 * κ lam d₁ 4 +
  15 * κ lam d₁ 1 ^ 2 * κ lam d₁ 4 +
  3 * κ lam d₁ 3 ^ 2 +
  30 * κ lam d₁ 1 * κ lam d₁ 2 * κ lam d₁ 3 +
  20 * κ lam d₁ 1 ^ 3 * κ lam d₁ 3 +
  5 * κ lam d₁ 2 ^ 3 +
  30 * κ lam d₁ 1 ^ 2 * κ lam d₁ 2 ^ 2 +
  15 * κ lam d₁ 1 ^ 4 * κ lam d₁ 2 +
  κ lam d₁ 1 ^ 6

/-- `c₇^{MC}`:

    NC partitions of `[7]` (C₇ = 429):
    · `(7)`              mult `1`
    · `(6,1)`            mult `7`
    · `(5,2)`            mult `7`
    · `(5,1,1)`          mult `21`
    · `(4,3)`            mult `7`
    · `(4,2,1)`          mult `42`
    · `(4,1,1,1)`        mult `35`
    · `(3,3,1)`          mult `21`
    · `(3,2,2)`          mult `21`
    · `(3,2,1,1)`        mult `105`
    · `(3,1,1,1,1)`      mult `35`
    · `(2,2,2,1)`        mult `35`
    · `(2,2,1,1,1)`      mult `70`
    · `(2,1,1,1,1,1)`    mult `21`
    · `(1,1,1,1,1,1,1)`  mult `1`.  -/
noncomputable def cMC_7 : ℝ :=
  κ lam d₁ 7 +
  7 * κ lam d₁ 1 * κ lam d₁ 6 +
  7 * κ lam d₁ 2 * κ lam d₁ 5 +
  21 * κ lam d₁ 1 ^ 2 * κ lam d₁ 5 +
  7 * κ lam d₁ 3 * κ lam d₁ 4 +
  42 * κ lam d₁ 1 * κ lam d₁ 2 * κ lam d₁ 4 +
  35 * κ lam d₁ 1 ^ 3 * κ lam d₁ 4 +
  21 * κ lam d₁ 1 * κ lam d₁ 3 ^ 2 +
  21 * κ lam d₁ 2 ^ 2 * κ lam d₁ 3 +
  105 * κ lam d₁ 1 ^ 2 * κ lam d₁ 2 * κ lam d₁ 3 +
  35 * κ lam d₁ 1 ^ 4 * κ lam d₁ 3 +
  35 * κ lam d₁ 1 * κ lam d₁ 2 ^ 3 +
  70 * κ lam d₁ 1 ^ 3 * κ lam d₁ 2 ^ 2 +
  21 * κ lam d₁ 1 ^ 5 * κ lam d₁ 2 +
  κ lam d₁ 1 ^ 7

-- ═══════════════════════════════════════════════════════════════════
-- §3. Match with General.c_k
-- ═══════════════════════════════════════════════════════════════════

theorem cMC_1_eq : cMC_1 lam d₁ = General.c₁ lam d₁ := by
  simp [cMC_1, General.c₁]

theorem cMC_2_eq (hd : d₁ ≠ 0) : cMC_2 lam d₁ = General.c₂ lam d₁ := by
  simp only [cMC_2, General.c₂, κ_one, κ_two]
  field_simp
  ring

theorem cMC_3_eq (hd : d₁ ≠ 0) : cMC_3 lam d₁ = General.c₃ lam d₁ := by
  simp only [cMC_3, General.c₃, κ_one, κ_two, κ_three]
  field_simp
  ring

theorem cMC_4_eq (hd : d₁ ≠ 0) : cMC_4 lam d₁ = General.c₄ lam d₁ := by
  simp only [cMC_4, General.c₄, κ_one, κ_two, κ_three, κ_four]
  field_simp
  ring

theorem cMC_5_eq (hd : d₁ ≠ 0) : cMC_5 lam d₁ = General.c₅ lam d₁ := by
  simp only [cMC_5, General.c₅, κ_one, κ_two, κ_three, κ_four, κ_five]
  field_simp
  ring

theorem cMC_6_eq (hd : d₁ ≠ 0) : cMC_6 lam d₁ = General.c₆ lam d₁ := by
  simp only [cMC_6, General.c₆,
             κ_one, κ_two, κ_three, κ_four, κ_five, κ_six]
  field_simp
  ring

theorem cMC_7_eq (hd : d₁ ≠ 0) : cMC_7 lam d₁ = General.c₇ lam d₁ := by
  simp only [cMC_7, General.c₇,
             κ_one, κ_two, κ_three, κ_four, κ_five, κ_six, κ_seven]
  field_simp
  ring

end MomentCumulant
