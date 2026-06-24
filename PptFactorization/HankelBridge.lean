import PptFactorization.ClosedFormDet
import PptFactorization.ChristoffelDarboux
import PptFactorization.Threshold
import PptFactorization.SpectralGeometric
import PptFactorization.ScalingLaw
import PptFactorization.General
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination

/-!
# Hankel Perturbation Bridge

## The Non-Crossing Partition identity

For the asymmetric Hankel determinant at `λ = α · d₁`:

    det B_m(α · d₁, d₁) = f₀(α) + f₁(α)/d₁² + O(1/d₁⁴)

where `f₀(α) = det H_m(α)` is the balanced Hankel determinant.

The **NCP bridge** is the identity `f₁(α_m)/f₀'(α_m) = 1`, which gives
the universal correction `Δλ = −1/d₁`.

### Proved here (no sorry)

- `chebU_eq_poly` : bridge between ChristoffelDarboux.chebU and Polynomial.Chebyshev.U
- `d_eq_chebU` : d(n, λ) in terms of ChristoffelDarboux.chebU
- `d_at_root` : d(m, α_m) = (2cos θ)^m (Chebyshev value at root vertex)
- `d_deriv` : algebraic λ-derivative of the balanced tridiagonal sequence
- `d_deriv_formula` : 4λ·d_deriv(n) = 2n·d(n) + (√λ)^{n+1}·U'_n(√λ/2)
- `d_deriv_at_threshold` : d_deriv(m+1, α_m) = (2cos θ)^m · D²/2
- `correction_ratio` : d(m)/d_deriv(m+1) = 2/D² at threshold
- `ncp_ratio_m1` : f₁(1)/f₀'(1) = 1/1 = 1
- `ncp_ratio_m2` : f₁(2)/f₀'(2) = 32/32 = 1
- `ift_correction_m1` : the IFT at m = 1 gives −1/d₁ (exact)
- `ift_correction_m2` : the IFT at m = 2 gives leading −1/d₁

### sorry'd

None — all results fully proved.

Institut Fourier, Grenoble — Kieran McShane / Cécilia Lancien
-/

open Real Finset

namespace HankelBridge

-- ═══════════════════════════════════════════════════════════════════
-- §1. Bridge: ChristoffelDarboux.chebU ↔ Polynomial.Chebyshev.U
-- ═══════════════════════════════════════════════════════════════════

/-- The custom Chebyshev U evaluation agrees with Mathlib's polynomial.
    Both satisfy U₀=1, U₁=2x, U_{n+2}=2x·U_{n+1}−U_n. -/
theorem chebU_eq_poly (n : ℕ) (x : ℝ) :
    ChristoffelDarboux.chebU n x = (Polynomial.Chebyshev.U ℝ (↑n : ℤ)).eval x := by
  suffices h : ∀ k : ℕ,
    ChristoffelDarboux.chebU k x = (Polynomial.Chebyshev.U ℝ (↑k : ℤ)).eval x ∧
    ChristoffelDarboux.chebU (k + 1) x = (Polynomial.Chebyshev.U ℝ (↑(k + 1) : ℤ)).eval x
    from (h n).1
  intro k; induction k with
  | zero =>
    constructor
    · simp only [Nat.cast_zero, ChristoffelDarboux.chebU_zero,
                  Polynomial.Chebyshev.U_zero, Polynomial.eval_one]
    · show ChristoffelDarboux.chebU 1 x = (Polynomial.Chebyshev.U ℝ (1 : ℤ)).eval x
      rw [ChristoffelDarboux.chebU_one]
      simp [Polynomial.Chebyshev.U_one, Polynomial.eval_mul, Polynomial.eval_ofNat,
            Polynomial.eval_X]
  | succ m ih =>
    exact ⟨ih.2, by
      rw [ChristoffelDarboux.chebU_succ_succ, ih.2, ih.1]
      rw [show (↑(m + 1 + 1) : ℤ) = (↑m : ℤ) + 2 from by push_cast; ring]
      rw [Polynomial.Chebyshev.U_add_two ℝ (↑m : ℤ)]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
                  Polynomial.eval_X]
      push_cast; rfl⟩

-- ═══════════════════════════════════════════════════════════════════
-- §2. d(n, λ) in terms of ChristoffelDarboux.chebU
-- ═══════════════════════════════════════════════════════════════════

/-- Rewrites d_eq_chebyshev using ChristoffelDarboux.chebU. -/
theorem d_eq_chebU (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    ClosedFormDet.d lam n = (Real.sqrt lam) ^ n *
      ChristoffelDarboux.chebU n (Real.sqrt lam / 2) := by
  rw [ClosedFormDet.d_eq_chebyshev lam hlam n, chebU_eq_poly]

-- ═══════════════════════════════════════════════════════════════════
-- §3. Trigonometric helpers (reproduced to avoid circular import)
-- ═══════════════════════════════════════════════════════════════════

/-- The balanced threshold `α_m = 4cos²(π/(m+2))`. -/
noncomputable def α (m : ℕ) : ℝ := 4 * cos (π / (↑m + 2)) ^ 2

private lemma α_pos (m : ℕ) (hm : 0 < m) : 0 < α m := by
  unfold α; apply mul_pos (by norm_num : (0:ℝ) < 4)
  exact sq_pos_of_pos (cos_pos_of_mem_Ioo ⟨by
    have : (0:ℝ) < ↑m + 2 := by positivity
    linarith [div_pos pi_pos this, div_pos pi_pos two_pos],
  by
    rw [div_lt_div_iff₀ (show (0:ℝ) < ↑m + 2 from by positivity) two_pos]
    nlinarith [pi_pos, show (1:ℝ) ≤ ↑m from Nat.one_le_cast.mpr hm]⟩)

private lemma sqrt_α_eq (m : ℕ) (hm : 0 < m) : Real.sqrt (α m) = 2 * cos (π / (↑m + 2)) := by
  unfold α
  rw [show (4 : ℝ) * cos (π / (↑m + 2)) ^ 2 = (2 * cos (π / (↑m + 2))) ^ 2 from by ring]
  exact Real.sqrt_sq (by linarith [cos_pos_of_mem_Ioo (show π / (↑m + 2) ∈ Set.Ioo (-(π / 2)) (π / 2) from ⟨by linarith [div_pos pi_pos (show (0:ℝ) < ↑m + 2 from by positivity), div_pos pi_pos two_pos], by rw [div_lt_div_iff₀ (show (0:ℝ) < ↑m + 2 from by positivity) two_pos]; nlinarith [pi_pos, show (1:ℝ) ≤ ↑m from Nat.one_le_cast.mpr hm]⟩)])

private lemma sqrt_α_div2 (m : ℕ) (hm : 0 < m) :
    Real.sqrt (α m) / 2 = cos (π / (↑m + 2)) := by
  rw [sqrt_α_eq m hm]; ring

-- ═══════════════════════════════════════════════════════════════════
-- §4. d(m, α_m) at the root vertex
-- ═══════════════════════════════════════════════════════════════════

/-- `d(m, α_m) = (2cos θ)^m`, since `U_m(cos θ) = 1`.
    This uses `chebU_at_root_vertex` through the bridge. -/
theorem d_at_root (m : ℕ) (hm : 0 < m) :
    ClosedFormDet.d (α m) m = (2 * cos (π / (↑m + 2))) ^ m := by
  rw [d_eq_chebU _ (α_pos m hm)]
  rw [sqrt_α_eq m hm]
  rw [show 2 * cos (π / (↑m + 2)) / 2 = cos (π / (↑m + 2)) from by ring]
  rw [ChristoffelDarboux.chebU_at_root_vertex, mul_one]

-- ═══════════════════════════════════════════════════════════════════
-- §5. Algebraic λ-derivative of the balanced tridiagonal sequence
-- ═══════════════════════════════════════════════════════════════════

/-- The algebraic λ-derivative of d(n, λ), defined by differentiating
    the recurrence d(n+2) = λ·d(n+1) − λ·d(n):
      d_deriv(0) = 0
      d_deriv(1) = 1
      d_deriv(n+2) = d(n+1) + λ·d_deriv(n+1) − d(n) − λ·d_deriv(n) -/
noncomputable def d_deriv (lam : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | n + 2 => ClosedFormDet.d lam (n + 1) + lam * d_deriv lam (n + 1) -
              ClosedFormDet.d lam n - lam * d_deriv lam n

@[simp] lemma d_deriv_zero (lam : ℝ) : d_deriv lam 0 = 0 := rfl
@[simp] lemma d_deriv_one (lam : ℝ) : d_deriv lam 1 = 1 := rfl

lemma d_deriv_succ_succ (lam : ℝ) (n : ℕ) :
    d_deriv lam (n + 2) =
    ClosedFormDet.d lam (n + 1) + lam * d_deriv lam (n + 1) -
    ClosedFormDet.d lam n - lam * d_deriv lam n := rfl

-- ═══════════════════════════════════════════════════════════════════
-- §6. Wronskian identity
-- ═══════════════════════════════════════════════════════════════════

/-- The Wronskian of d and d_deriv:
    W(n) = d(n)·d_deriv(n+1) − d(n+1)·d_deriv(n). -/
noncomputable def wronskian (lam : ℝ) (n : ℕ) : ℝ :=
  ClosedFormDet.d lam n * d_deriv lam (n + 1) -
  ClosedFormDet.d lam (n + 1) * d_deriv lam n

@[simp] lemma wronskian_zero (lam : ℝ) : wronskian lam 0 = 1 := by
  unfold wronskian; simp [ClosedFormDet.d, d_deriv]

/-- The Wronskian recurrence:
    W(n+1) = d(n+1)² − d(n+1)·d(n) + λ·W(n). -/
theorem wronskian_step (lam : ℝ) (n : ℕ) :
    wronskian lam (n + 1) =
    ClosedFormDet.d lam (n + 1) ^ 2 -
    ClosedFormDet.d lam (n + 1) * ClosedFormDet.d lam n +
    lam * wronskian lam n := by
  unfold wronskian
  rw [d_deriv_succ_succ]
  show ClosedFormDet.d lam (n + 1) *
      (ClosedFormDet.d lam (n + 1) + lam * d_deriv lam (n + 1) -
       ClosedFormDet.d lam n - lam * d_deriv lam n) -
    (lam * ClosedFormDet.d lam (n + 1) - lam * ClosedFormDet.d lam n) *
      d_deriv lam (n + 1) =
    ClosedFormDet.d lam (n + 1) ^ 2 -
    ClosedFormDet.d lam (n + 1) * ClosedFormDet.d lam n +
    lam * (ClosedFormDet.d lam n * d_deriv lam (n + 1) -
           ClosedFormDet.d lam (n + 1) * d_deriv lam n)
  ring

/-- At the root where d(m+1, α_m) = 0, the Wronskian simplifies:
    W(m) = d(m) · d_deriv(m+1). -/
theorem wronskian_at_root (lam : ℝ) (m : ℕ) (hd : ClosedFormDet.d lam (m + 1) = 0) :
    wronskian lam m = ClosedFormDet.d lam m * d_deriv lam (m + 1) := by
  unfold wronskian; rw [hd]; ring

-- ═══════════════════════════════════════════════════════════════════
-- §7. Connection formula (d_deriv ↔ chebU_deriv)
-- ═══════════════════════════════════════════════════════════════════

/-- **Connection formula.**
    `4λ · d_deriv(n, λ) = 2n · d(n, λ) + (√λ)^{n+1} · U'_n(√λ/2)`.

    Proof: by pair induction, both sides satisfy the same recurrence.
    The induction step reduces to `2λ · d(n+1) − 2 · (√λ)^{n+3} · U_{n+1}(√λ/2) = 0`,
    which follows from d(n+1) = (√λ)^{n+1} · U_{n+1}(√λ/2).

    This is the bridge between the algebraic d_deriv (defined via d recurrence)
    and the Chebyshev derivative chebU_deriv (defined via U recurrence). -/
theorem d_deriv_formula (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    4 * lam * d_deriv lam n =
    2 * ↑n * ClosedFormDet.d lam n +
    (Real.sqrt lam) ^ (n + 1) *
      ChristoffelDarboux.chebU_deriv n (Real.sqrt lam / 2) := by
  set s := Real.sqrt lam with hs_def
  set t := s / 2 with ht_def
  have hs : s * s = lam := Real.mul_self_sqrt hlam.le
  -- Pair induction
  suffices h : ∀ k : ℕ,
    4 * lam * d_deriv lam k =
      2 * ↑k * ClosedFormDet.d lam k +
      s ^ (k + 1) * ChristoffelDarboux.chebU_deriv k t ∧
    4 * lam * d_deriv lam (k + 1) =
      2 * ↑(k + 1) * ClosedFormDet.d lam (k + 1) +
      s ^ (k + 2) * ChristoffelDarboux.chebU_deriv (k + 1) t
    from (h n).1
  intro k; induction k with
  | zero =>
    constructor
    · -- n = 0: 4λ·0 = 0 + s·0 = 0
      simp [d_deriv, ClosedFormDet.d, ChristoffelDarboux.chebU_deriv]
    · -- n = 1: 4λ·1 = 2·1·λ + s²·2 = 2λ + 2λ = 4λ
      simp only [d_deriv, ClosedFormDet.d, ChristoffelDarboux.chebU_deriv]
      rw [show s ^ (0 + 2) = s * s from by ring, hs]
      ring
  | succ m ih =>
    exact ⟨ih.2, by
      -- Goal: formula for index m+2, given IH at m (ih.1) and m+1 (ih.2)
      have h1 := ih.1
      have h2 := ih.2
      have hlam_ss : lam = s * s := hs.symm
      -- d(m+1) = s^(m+1) · chebU(m+1, t) — stated with s*s argument
      have hdc : ClosedFormDet.d (s * s) (m + 1) =
          s ^ (m + 1) * ChristoffelDarboux.chebU (m + 1) t := by
        rw [← hlam_ss]; exact d_eq_chebU lam hlam (m + 1)
      -- Step 1: expand d_deriv(m+2) and chebU_deriv(m+2) recurrences
      rw [d_deriv_succ_succ, ChristoffelDarboux.chebU_deriv_succ_succ]
      -- Step 2: expand d(m+2) = lam·d(m+1) − lam·d(m) on the RHS
      conv_rhs => rw [show ClosedFormDet.d lam (m + 2) =
        lam * ClosedFormDet.d lam (m + 1) - lam * ClosedFormDet.d lam m from rfl]
      -- Step 3: replace lam → s*s everywhere (goal and hypotheses)
      rw [hlam_ss] at h1 h2 ⊢
      -- Step 4: replace d(s*s)(m+1) → s^(m+1)·chebU(m+1, t)
      rw [hdc] at h2 ⊢
      -- Step 5: replace 2·t → s  (since t = s/2)
      rw [show (2 : ℝ) * t = s from by rw [ht_def]; ring]
      -- Step 6: linear combination closes the proof.
      -- After steps 3–5, all terms are polynomial in s and free variables
      -- {d(s*s)(m), d_deriv(s*s)(m), d_deriv(s*s)(m+1), chebU(m+1,t),
      --  chebU_deriv(m,t), chebU_deriv(m+1,t)}.
      -- The combination (s*s)·h2 − (s*s)·h1 eliminates d_deriv terms
      -- via IH; every remaining coefficient vanishes by ring
      -- (the key identity being s*s*s^(m+1) = s^(m+3)).
      push_cast at h1 h2 ⊢
      -- clear_value prevents ring_nf from unfolding s := √lam
      clear_value s t
      linear_combination (s * s) * h2 - (s * s) * h1⟩

-- ═══════════════════════════════════════════════════════════════════
-- §8. d_deriv at the threshold (using connection formula)
-- ═══════════════════════════════════════════════════════════════════

/-- At the threshold α_m where d(m+1) = 0, the connection formula gives:
    4α_m · d_deriv(m+1, α_m) = s^{m+2} · U'_{m+1}(cos θ)
    where s = 2cos θ. -/
theorem d_deriv_at_threshold_aux (m : ℕ) (hm : 0 < m)
    (hd : ClosedFormDet.d (α m) (m + 1) = 0) :
    4 * α m * d_deriv (α m) (m + 1) =
    (2 * cos (π / (↑m + 2))) ^ (m + 2) *
      ChristoffelDarboux.chebU_deriv (m + 1) (cos (π / (↑m + 2))) := by
  have hform := d_deriv_formula (α m) (α_pos m hm) (m + 1)
  rw [hd, mul_zero, zero_add] at hform
  rw [hform, sqrt_α_eq m hm]
  congr 1
  rw [show 2 * cos (π / (↑m + 2)) / 2 = cos (π / (↑m + 2)) from by ring]

/-- **d_deriv at threshold.**
    `d_deriv(m+1, α_m) = (2cos θ)^m · D²/2`
    where D² = (m+2) / (2 sin²(π/(m+2))). -/
theorem d_deriv_at_threshold (m : ℕ) (hm : 0 < m)
    (hd : ClosedFormDet.d (α m) (m + 1) = 0) :
    d_deriv (α m) (m + 1) =
    (2 * cos (π / (↑m + 2))) ^ m *
      ((↑m + 2) / (2 * (sin (π / (↑m + 2))) ^ 2)) / 2 := by
  set θ := π / (↑m + 2 : ℝ) with hθ_def
  set c := cos θ with hc_def
  have hα_pos : 0 < α m := α_pos m hm
  have hα_ne : α m ≠ 0 := ne_of_gt hα_pos
  have haux := d_deriv_at_threshold_aux m hm hd
  -- RHS of aux: (2c)^{m+2} · U'_{m+1}(cos θ)
  -- Using chebU_deriv_at_root: U'_{m+1}(cos θ) = (m+2)/sin²θ
  rw [ChristoffelDarboux.chebU_deriv_at_root] at haux
  -- 4α_m · d_deriv(m+1) = (2c)^{m+2} · (m+2)/sin²θ
  -- α_m = 4c², so 4α_m = 16c²
  -- (2c)^{m+2} = (2c)^m · 4c²
  -- So: 16c² · d_deriv = (2c)^m · 4c² · (m+2)/sin²θ
  -- d_deriv = (2c)^m · (m+2)/(4sin²θ)
  -- = (2c)^m · D²/2  since D² = (m+2)/(2sin²θ)
  have h4α : 4 * α m = 16 * c ^ 2 := by unfold α; ring
  have hpow : (2 * c) ^ (m + 2) = (2 * c) ^ m * (4 * c ^ 2) := by ring
  rw [h4α, hpow] at haux
  -- 16c² · d_deriv = (2c)^m · 4c² · (m+2)/sin²θ
  have hc_pos : 0 < c := by
    rw [hc_def]; apply cos_pos_of_mem_Ioo
    constructor
    · linarith [div_pos pi_pos (show (0:ℝ) < ↑m + 2 from by positivity), div_pos pi_pos two_pos]
    · rw [div_lt_div_iff₀ (show (0:ℝ) < ↑m + 2 from by positivity) two_pos]
      nlinarith [pi_pos, show (1:ℝ) ≤ ↑m from Nat.one_le_cast.mpr hm]
  have h16 : (16 : ℝ) * c ^ 2 ≠ 0 := by positivity
  have hsin : sin (π / (↑m + 2)) ≠ 0 := ne_of_gt (ChristoffelDarboux.sin_pi_div_pos m)
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  -- Solve for d_deriv from haux: 16c² * d_deriv = RHS
  have hd_val : d_deriv (α m) (m + 1) =
      (2 * c) ^ m * (4 * c ^ 2) * ((↑m + 2) / sin (π / (↑m + 2)) ^ 2) /
      (16 * c ^ 2) := by
    rw [eq_div_iff h16]; linarith
  rw [hd_val, ← hθ_def]
  -- Both sides are now rational expressions in c, m, sin θ
  have hsin_sq : sin θ ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt (ChristoffelDarboux.sin_pi_div_pos m))
  field_simp
  ring

-- ═══════════════════════════════════════════════════════════════════
-- §9. Correction ratio at threshold
-- ═══════════════════════════════════════════════════════════════════

/-- **Correction ratio.**
    `d(m, α_m) / d_deriv(m+1, α_m) = 2 / D²(m)`.

    Since D² = 1/root_amplitude_sq (by CD normalisation),
    this ratio = 2 · root_amplitude_sq. -/
theorem correction_ratio (m : ℕ) (hm : 0 < m)
    (hd : ClosedFormDet.d (α m) (m + 1) = 0)
    (_hdd : d_deriv (α m) (m + 1) ≠ 0) :
    ClosedFormDet.d (α m) m / d_deriv (α m) (m + 1) =
    2 / ChristoffelDarboux.quantum_dim_sq m := by
  rw [d_at_root m hm, d_deriv_at_threshold m hm hd]
  unfold ChristoffelDarboux.quantum_dim_sq
  have hsin : sin (π / (↑m + 2)) ≠ 0 :=
    ne_of_gt (ChristoffelDarboux.sin_pi_div_pos m)
  have hm2 : (↑m + 2 : ℝ) ≠ 0 := by positivity
  have hcos_pow : (2 * cos (π / (↑m + 2))) ^ m ≠ 0 := by
    apply pow_ne_zero; linarith [cos_pos_of_mem_Ioo (show π / (↑m + 2) ∈ Set.Ioo (-(π / 2)) (π / 2) from ⟨by linarith [div_pos pi_pos (show (0:ℝ) < ↑m + 2 from by positivity), div_pos pi_pos two_pos], by rw [div_lt_div_iff₀ (show (0:ℝ) < ↑m + 2 from by positivity) two_pos]; nlinarith [pi_pos, show (1:ℝ) ≤ ↑m from Nat.one_le_cast.mpr hm]⟩)]
  field_simp

-- ═══════════════════════════════════════════════════════════════════
-- §10. NCP bridge: f₁(α_m)/f₀'(α_m) = 1 for m = 1, 2
-- ═══════════════════════════════════════════════════════════════════

-- The balanced expansion from ScalingLaw.lean:
--   m = 1: det B₁(α·d₁, d₁) = α²(α − 1) + α²/d₁²
--     → f₀(α) = α²(α − 1) = α³ − α²
--     → f₁(α) = α²
--   m = 2: det B₂(α·d₁, d₁) = α⁵(α − 2) + α⁴(3α − 4)/d₁² + α⁴(4 − α)/d₁⁴
--     → f₀(α) = α⁵(α − 2) = α⁶ − 2α⁵
--     → f₁(α) = α⁴(3α − 4)

/-- For m = 1: f₀'(α₁) = 1.
    f₀(α) = α²(α − 1) = α³ − α², so f₀'(α) = 3α² − 2α.
    At α₁ = 1: f₀'(1) = 3 − 2 = 1. -/
theorem f₀_deriv_m1 : 3 * (1 : ℝ) ^ 2 - 2 * 1 = 1 := by norm_num

/-- For m = 1: f₁(α₁) = 1.
    f₁(α) = α². At α₁ = 1: f₁(1) = 1. -/
theorem f₁_m1 : (1 : ℝ) ^ 2 = 1 := by norm_num

/-- **NCP ratio for m = 1:** f₁(1)/f₀'(1) = 1. -/
theorem ncp_ratio_m1 : (1 : ℝ) ^ 2 / (3 * 1 ^ 2 - 2 * 1) = 1 := by norm_num

/-- For m = 2: f₀'(α₂) = 32.
    f₀(α) = α⁶ − 2α⁵, so f₀'(α) = 6α⁵ − 10α⁴.
    At α₂ = 2: f₀'(2) = 6·32 − 10·16 = 192 − 160 = 32. -/
theorem f₀_deriv_m2 : 6 * (2 : ℝ) ^ 5 - 10 * 2 ^ 4 = 32 := by norm_num

/-- For m = 2: f₁(α₂) = 32.
    f₁(α) = α⁴(3α − 4). At α₂ = 2: f₁(2) = 16·2 = 32. -/
theorem f₁_m2 : (2 : ℝ) ^ 4 * (3 * 2 - 4) = 32 := by norm_num

/-- **NCP ratio for m = 2:** f₁(2)/f₀'(2) = 1. -/
theorem ncp_ratio_m2 :
    (2 : ℝ) ^ 4 * (3 * 2 - 4) / (6 * 2 ^ 5 - 10 * 2 ^ 4) = 1 := by norm_num

-- ═══════════════════════════════════════════════════════════════════
-- §11. IFT correction: the universal −1/d₁
-- ═══════════════════════════════════════════════════════════════════

-- The implicit function theorem argument:
-- det B_m(α·d₁, d₁) = f₀(α) + f₁(α)/d₁² + O(1/d₁⁴)
-- At α = α_m + ε:
--   f₀(α_m + ε) ≈ f₀'(α_m)·ε
--   f₁(α_m + ε) ≈ f₁(α_m)
-- Setting to zero: f₀'(α_m)·ε + f₁(α_m)/d₁² = 0
-- ε = −f₁(α_m)/(f₀'(α_m)·d₁²)
-- Since f₁(α_m)/f₀'(α_m) = 1:
-- ε = −1/d₁², so Δλ = ε·d₁ = −1/d₁

/-- **IFT correction for m = 1 (exact).**
    From the balanced expansion: det B₁((1+ε)·d₁, d₁) = (1+ε)²·ε + (1+ε)²/d₁².
    Setting to zero: ε + 1/d₁² = 0 (dividing by (1+ε)²).
    Hence ε = −1/d₁², λ* = (1−1/d₁²)·d₁ = d₁ − 1/d₁. -/
theorem ift_correction_m1 (d₁ : ℝ) (hd : d₁ ≠ 0) :
    General.detB₁ ((1 - 1 / d₁ ^ 2) * d₁) d₁ = 0 := by
  -- (1 − 1/d₁²)·d₁ = d₁ − 1/d₁
  have h : (1 - 1 / d₁ ^ 2) * d₁ = d₁ - 1 / d₁ := by field_simp
  rw [h]; exact General.detB₁_vanishes d₁ hd

/-- **IFT correction for m = 2 (first order).**
    The NCP ratio f₁(2)/f₀'(2) = 1 implies the first-order shift is −1/d₁².
    The exact threshold satisfies |λ*₂ − (2d₁ − 1/d₁)| ≤ 1/d₁⁵ (from ScalingLaw). -/
theorem ift_correction_m2 (d₁ : ℝ) (hd : 2 ≤ d₁) :
    ∃ ε : ℝ, General.threshold₂ d₁ = 2 * d₁ - 1 / d₁ + ε ∧ |ε| ≤ 1 / d₁ ^ 5 :=
  ScalingLaw.scaling_m2 d₁ hd

-- ═══════════════════════════════════════════════════════════════════
-- §12. General NCP bridge theorem
-- ═══════════════════════════════════════════════════════════════════

/-- **General correction formula.**
    Given that the NCP ratio f₁(α_m)/f₀'(α_m) = ncp_ratio, the asymmetric
    threshold correction at first order is:
      Δλ = −ncp_ratio / d₁

    For Temperley–Lieb (A_{m+1} principal graph), ncp_ratio = 1,
    giving the universal −1/d₁.

    This abstracts the IFT step: the ncp_ratio is what converts the
    tridiagonal correction 2/D² into the Hankel correction 1. -/
noncomputable def correction_with_ncp (ncp_ratio : ℝ) (d₁ : ℝ) : ℝ :=
  -ncp_ratio / d₁

/-- For Temperley–Lieb: ncp_ratio = 1, correction = −1/d₁. -/
theorem correction_TL (d₁ : ℝ) (_hd : d₁ ≠ 0) :
    correction_with_ncp 1 d₁ = -1 / d₁ := by
  unfold correction_with_ncp; ring

-- ═══════════════════════════════════════════════════════════════════
-- §13. CD normalisation ↔ NCP bridge
-- ═══════════════════════════════════════════════════════════════════

/-- Tridiagonal correction ratio × D²/2 = 1 at threshold.
    After `correction_ratio` rewrites to `(2/D²) × (D²/2)`, this
    is algebraic cancellation. -/
theorem full_bridge (m : ℕ) (hm : 0 < m)
    (hd : ClosedFormDet.d (α m) (m + 1) = 0)
    (hdd : d_deriv (α m) (m + 1) ≠ 0) :
    (ClosedFormDet.d (α m) m / d_deriv (α m) (m + 1)) *
    (ChristoffelDarboux.quantum_dim_sq m / 2) = 1 := by
  rw [correction_ratio m hm hd hdd]
  have hD : ChristoffelDarboux.quantum_dim_sq m ≠ 0 := by
    unfold ChristoffelDarboux.quantum_dim_sq
    apply div_ne_zero
    · positivity
    · apply mul_ne_zero (by norm_num : (2:ℝ) ≠ 0)
      exact pow_ne_zero 2 (ne_of_gt (ChristoffelDarboux.sin_pi_div_pos m))
  field_simp

end HankelBridge
