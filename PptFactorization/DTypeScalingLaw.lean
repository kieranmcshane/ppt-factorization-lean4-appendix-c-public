import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic.LinearCombination

/-!
# D-type Scaling Law (Experimental)

Establishes the D-type threshold framework in parallel to the A-type
`SelfContainedProof`.

The D_{m+2} principal graph has Jones index `α_D(m) = 4cos²(π/(2m+2))`.
The threshold equation is governed by Chebyshev polynomials of the
**first** kind `T_n`, whereas the A-type equation uses `U_n`.

Both families satisfy the same three-term recurrence
`f_{n+2} = 2x·f_{n+1} − f_n` but with different initial conditions:

- A-type: `U₀=1`, `U₁=2x`
- D-type: `T₀=1`, `T₁=x`

The balanced vanishing is clean: at `θ = π/(2m+2)`,
`(m+1)·θ = π/2`, so `T_{m+1}(cos θ) = cos((m+1)θ) = cos(π/2) = 0`.

## Scope of this file

- `chebT` : evaluated Chebyshev T
- `chebT_cos` : `T_n(cos θ) = cos(nθ)`
- `dT` : the D-type tridiagonal-like sequence
- `dT_eq_chebT` : closed form `dT n λ = (√λ)^n · T_n(√λ/2)`
- `α_D` : balanced threshold `4cos²(π/(2m+2))`
- `dT_vanishes_at_threshold` : `dT (α_D m) (m+1) = 0`
- `F_D` : threshold equation, smooth
- `F_D_vanishes` : `F_D (0, α_D m) = 0`

**Not yet covered**: transversality, IFT application, Taylor remainder.
Those would parallel the A-type proof.

Institut Fourier, Grenoble — Kieran McShane / Cécilia Lancien
-/

open Real

namespace DTypeScalingLaw

-- ═══════════════════════════════════════════════════════════════════
-- §1. Chebyshev T (first kind)
-- ═══════════════════════════════════════════════════════════════════

/-- Chebyshev polynomial of the first kind, evaluated:
    T₀(x) = 1,  T₁(x) = x,  T_{n+2}(x) = 2x·T_{n+1}(x) − T_n(x). -/
noncomputable def chebT : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, x => x
  | n + 2, x => 2 * x * chebT (n + 1) x - chebT n x

@[simp] lemma chebT_zero (x : ℝ) : chebT 0 x = 1 := rfl
@[simp] lemma chebT_one (x : ℝ) : chebT 1 x = x := rfl

lemma chebT_succ_succ (n : ℕ) (x : ℝ) :
    chebT (n + 2) x = 2 * x * chebT (n + 1) x - chebT n x := rfl

/-- **Trigonometric evaluation.**  `T_n(cos θ) = cos(nθ)`. -/
theorem chebT_cos (n : ℕ) (θ : ℝ) : chebT n (cos θ) = cos (↑n * θ) := by
  suffices h : ∀ k : ℕ,
    chebT k (cos θ) = cos (↑k * θ) ∧
    chebT (k + 1) (cos θ) = cos (↑(k + 1) * θ) from (h n).1
  intro k; induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp [chebT_zero]
    · simp [chebT_one]
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    rw [chebT_succ_succ, ih.2, ih.1]
    -- Goal: 2 cos θ · cos((m+1)θ) − cos(mθ) = cos((m+2)θ)
    have key : 2 * cos θ * cos ((↑m + 1) * θ) - cos (↑m * θ) =
        cos ((↑m + 2) * θ) := by
      have h1 := cos_add ((↑m + 1) * θ) θ
      have h2 := cos_sub ((↑m + 1) * θ) θ
      -- cos(A+B) + cos(A-B) = 2 cos A cos B
      have : cos (((↑m + 1) * θ) + θ) + cos (((↑m + 1) * θ) - θ) =
             2 * cos ((↑m + 1) * θ) * cos θ := by linarith
      rw [show (↑m + 1) * θ + θ = (↑m + 2) * θ from by ring,
          show (↑m + 1) * θ - θ = ↑m * θ from by ring] at this
      linarith
    rw [show (↑(m + 1 + 1) : ℝ) * θ = (↑m + 2) * θ from by push_cast; ring,
        show (↑(m + 1) : ℝ) * θ = (↑m + 1) * θ from by push_cast; ring]
    linarith [key]

-- ═══════════════════════════════════════════════════════════════════
-- §2. D-type tridiagonal sequence dT
-- ═══════════════════════════════════════════════════════════════════

/-- The D-type tridiagonal-like sequence:
    dT(0) = 1, dT(1) = λ/2, dT(n+2) = λ·dT(n+1) − λ·dT(n).

    Note `dT(1) = λ/2`, distinguishing this from the A-type `d(1) = λ`. -/
noncomputable def dT (lam : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => lam / 2
  | n + 2 => lam * dT lam (n + 1) - lam * dT lam n

@[simp] lemma dT_zero (lam : ℝ) : dT lam 0 = 1 := rfl
@[simp] lemma dT_one (lam : ℝ) : dT lam 1 = lam / 2 := rfl

lemma dT_succ_succ (lam : ℝ) (n : ℕ) :
    dT lam (n + 2) = lam * dT lam (n + 1) - lam * dT lam n := rfl

/-- **Closed form.**  `dT n λ = (√λ)^n · T_n(√λ/2)` for `λ > 0`. -/
theorem dT_eq_chebT (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    dT lam n = (Real.sqrt lam) ^ n * chebT n (Real.sqrt lam / 2) := by
  set s := Real.sqrt lam with hs_def
  have hs : s * s = lam := Real.mul_self_sqrt hlam.le
  set t := s / 2 with ht_def
  suffices h : ∀ k,
    dT lam k = s ^ k * chebT k t ∧
    dT lam (k + 1) = s ^ (k + 1) * chebT (k + 1) t
    from (h n).1
  intro k; induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp [dT_zero, chebT_zero]
    · show dT lam 1 = s ^ 1 * chebT 1 t
      simp only [dT_one, chebT_one, pow_one]
      rw [ht_def]
      field_simp
      linarith [hs]
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    show dT lam (m + 2) = s ^ (m + 2) * chebT (m + 2) t
    rw [dT_succ_succ, chebT_succ_succ, ih.2, ih.1]
    rw [show (2 : ℝ) * t = s from by rw [ht_def]; ring, ← hs]
    ring

-- ═══════════════════════════════════════════════════════════════════
-- §3. D-type balanced threshold
-- ═══════════════════════════════════════════════════════════════════

/-- The D_{m+2} balanced threshold `α_D(m) = 4cos²(π/(2m+2))`. -/
noncomputable def α_D (m : ℕ) : ℝ := 4 * cos (π / (2 * (↑m + 1))) ^ 2

private lemma cos_half_pos (m : ℕ) (hm : 0 < m) :
    0 < cos (π / (2 * (↑m + 1))) := by
  apply cos_pos_of_mem_Ioo
  constructor
  · have h1 : (0:ℝ) < 2 * (↑m + 1) := by positivity
    linarith [div_pos pi_pos h1, div_pos pi_pos two_pos]
  · have h1 : (0:ℝ) < 2 * (↑m + 1) := by positivity
    rw [div_lt_div_iff₀ h1 two_pos]
    have hm1 : (1:ℝ) ≤ ↑m := Nat.one_le_cast.mpr hm
    nlinarith [pi_pos]

lemma α_D_pos (m : ℕ) (hm : 0 < m) : 0 < α_D m := by
  unfold α_D
  exact mul_pos (by norm_num) (sq_pos_of_pos (cos_half_pos m hm))

private lemma sqrt_α_D (m : ℕ) (hm : 0 < m) :
    Real.sqrt (α_D m) = 2 * cos (π / (2 * (↑m + 1))) := by
  unfold α_D
  rw [show (4:ℝ) * cos (π / (2 * (↑m + 1))) ^ 2 =
    (2 * cos (π / (2 * (↑m + 1)))) ^ 2 from by ring]
  exact Real.sqrt_sq (by linarith [cos_half_pos m hm])

private lemma sqrt_α_D_div2 (m : ℕ) (hm : 0 < m) :
    Real.sqrt (α_D m) / 2 = cos (π / (2 * (↑m + 1))) := by
  rw [sqrt_α_D m hm]; ring

-- ═══════════════════════════════════════════════════════════════════
-- §4. Balanced vanishing: dT (α_D m) (m+1) = 0
-- ═══════════════════════════════════════════════════════════════════

/-- **Key angle identity.**  At `θ = π/(2(m+1))`, `(m+1)·θ = π/2`,
    so `cos((m+1)θ) = 0`. -/
private lemma cos_angle_vanishes (m : ℕ) :
    cos (↑(m + 1) * (π / (2 * (↑m + 1)))) = 0 := by
  have hm : (↑m + 1 : ℝ) ≠ 0 := by positivity
  rw [show ↑(m + 1) * (π / (2 * (↑m + 1))) = π / 2 from by
    push_cast; field_simp]
  exact cos_pi_div_two

/-- **Balanced vanishing.**  `T_{m+1}(cos(π/(2m+2))) = 0`. -/
theorem chebT_vanishes_at_root (m : ℕ) :
    chebT (m + 1) (cos (π / (2 * (↑m + 1)))) = 0 := by
  rw [chebT_cos]
  exact cos_angle_vanishes m

/-- **D-type balanced vanishing.**  `dT (α_D m) (m+1) = 0`. -/
theorem dT_vanishes_at_threshold (m : ℕ) (hm : 0 < m) :
    dT (α_D m) (m + 1) = 0 := by
  rw [dT_eq_chebT _ (α_D_pos m hm), sqrt_α_D_div2 m hm]
  rw [chebT_vanishes_at_root, mul_zero]

-- ═══════════════════════════════════════════════════════════════════
-- §5. D-type threshold equation F_D
-- ═══════════════════════════════════════════════════════════════════

/-- The D-type threshold equation
    `F_D(δ, α) = dT(m+1, α) − δ · dT(m, α)`. -/
noncomputable def F_D (m : ℕ) : ℝ × ℝ → ℝ :=
  fun p => dT p.2 (m + 1) - p.1 * dT p.2 m

theorem F_D_vanishes (m : ℕ) (hm : 0 < m) : F_D m (0, α_D m) = 0 := by
  simp only [F_D, zero_mul, sub_zero]
  exact dT_vanishes_at_threshold m hm

-- ═══════════════════════════════════════════════════════════════════
-- §6. Smoothness of dT and F_D
-- ═══════════════════════════════════════════════════════════════════

/-- `dT(n, ·)` is `C^∞` for every `n`.  Since the recurrence uses only
    polynomial operations in `λ`, each `dT(n, ·)` is a polynomial. -/
theorem dT_contDiff (n : ℕ) : ContDiff ℝ ⊤ (fun l => dT l n) := by
  suffices h : ∀ k : ℕ,
    ContDiff ℝ ⊤ (fun l => dT l k) ∧ ContDiff ℝ ⊤ (fun l => dT l (k + 1))
    from (h n).1
  intro k; induction k with
  | zero =>
    refine ⟨contDiff_const, ?_⟩
    show ContDiff ℝ ⊤ (fun l => dT l 1)
    simp only [dT_one]
    exact contDiff_id.div_const 2
  | succ m ih =>
    exact ⟨ih.2, by
      show ContDiff ℝ ⊤ (fun l => dT l (m + 2))
      simp only [dT_succ_succ]
      exact (contDiff_id.mul ih.2).sub (contDiff_id.mul ih.1)⟩

theorem F_D_contDiff (m : ℕ) : ContDiff ℝ ⊤ (F_D m) := by
  unfold F_D
  exact ((dT_contDiff (m + 1)).comp contDiff_snd).sub
    (contDiff_fst.mul ((dT_contDiff m).comp contDiff_snd))

-- ═══════════════════════════════════════════════════════════════════
-- §7. Algebraic derivative of Chebyshev T
-- ═══════════════════════════════════════════════════════════════════

/-- Algebraic derivative of `T_n(x)`, obtained by differentiating
    the three-term recurrence:
      T₀' = 0,  T₁' = 1,  T'_{n+2} = 2·T_{n+1} + 2x·T'_{n+1} − T'_n. -/
noncomputable def chebT_deriv : ℕ → ℝ → ℝ
  | 0, _ => 0
  | 1, _ => 1
  | n + 2, x => 2 * chebT (n + 1) x + 2 * x * chebT_deriv (n + 1) x - chebT_deriv n x

@[simp] lemma chebT_deriv_zero (x : ℝ) : chebT_deriv 0 x = 0 := rfl
@[simp] lemma chebT_deriv_one (x : ℝ) : chebT_deriv 1 x = 1 := rfl

lemma chebT_deriv_succ_succ (n : ℕ) (x : ℝ) :
    chebT_deriv (n + 2) x =
    2 * chebT (n + 1) x + 2 * x * chebT_deriv (n + 1) x - chebT_deriv n x := rfl

-- ═══════════════════════════════════════════════════════════════════
-- §8. Trigonometric formula: T'_n(cos φ) · sin φ = n · sin(nφ)
-- ═══════════════════════════════════════════════════════════════════

/-- **Key identity.**
    `T'_n(cos φ) · sin φ = n · sin(n·φ)`.

    Proof: pair induction.  The inductive step uses
      `2 sin A cos B = sin(A+B) + sin(A−B)`
      `2 cos A sin B = sin(A+B) − sin(A−B)` -/
theorem chebT_deriv_cos_sin (n : ℕ) (φ : ℝ) :
    chebT_deriv n (cos φ) * sin φ = ↑n * sin (↑n * φ) := by
  suffices h : ∀ k : ℕ,
    chebT_deriv k (cos φ) * sin φ = ↑k * sin (↑k * φ) ∧
    chebT_deriv (k + 1) (cos φ) * sin φ = ↑(k + 1) * sin (↑(k + 1) * φ)
    from (h n).1
  intro k; induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp
    · simp
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    show chebT_deriv (m + 2) (cos φ) * sin φ =
      (↑(m + 1 + 1) : ℝ) * sin ((↑(m + 1 + 1) : ℝ) * φ)
    rw [chebT_deriv_succ_succ]
    -- We have:
    --   ih.1 : T'_m(cos φ) · sin φ = m · sin(m·φ)
    --   ih.2 : T'_{m+1}(cos φ) · sin φ = (m+1) · sin((m+1)·φ)
    -- Also need:
    --   chebT (m+1) (cos φ) = cos((m+1)·φ)   [from chebT_cos]
    have hT : chebT (m + 1) (cos φ) = cos ((↑m + 1) * φ) := by
      rw [chebT_cos]; push_cast; ring_nf
    -- Product-to-sum identities:
    have h_prod1 : 2 * sin φ * cos ((↑m + 1) * φ) =
        sin ((↑m + 2) * φ) - sin (↑m * φ) := by
      have h := sin_add ((↑m + 1) * φ) φ
      have h' := sin_sub ((↑m + 1) * φ) φ
      rw [show (↑m + 1) * φ + φ = (↑m + 2) * φ from by ring] at h
      rw [show (↑m + 1) * φ - φ = ↑m * φ from by ring] at h'
      linarith
    have h_prod2 : 2 * cos φ * sin ((↑m + 1) * φ) =
        sin ((↑m + 2) * φ) + sin (↑m * φ) := by
      have h := sin_add ((↑m + 1) * φ) φ
      have h' := sin_sub ((↑m + 1) * φ) φ
      rw [show (↑m + 1) * φ + φ = (↑m + 2) * φ from by ring] at h
      rw [show (↑m + 1) * φ - φ = ↑m * φ from by ring] at h'
      linarith
    -- Cast normalisation
    have hih1 : chebT_deriv m (cos φ) * sin φ = (↑m : ℝ) * sin (↑m * φ) := ih.1
    have hih2 : chebT_deriv (m + 1) (cos φ) * sin φ =
        (↑m + 1 : ℝ) * sin ((↑m + 1) * φ) := by
      have := ih.2
      push_cast at this
      linarith
    push_cast
    -- Goal: (2 · T_{m+1} + 2·cos φ · T'_{m+1} − T'_m)(cos φ) · sin φ
    --     = (m+2) · sin((m+2)·φ)
    -- Expand: LHS = 2·T_{m+1}·sin φ + 2·cos φ · T'_{m+1} · sin φ − T'_m · sin φ
    rw [hT]
    have hgoal :
        (2 * cos ((↑m + 1) * φ) +
          2 * cos φ * chebT_deriv (m + 1) (cos φ) -
          chebT_deriv m (cos φ)) * sin φ =
        (↑m + 2) * sin ((↑m + 2) * φ) := by
      have eq1 : 2 * cos ((↑m + 1) * φ) * sin φ =
          sin ((↑m + 2) * φ) - sin (↑m * φ) := by linarith
      have eq2 : 2 * cos φ * (chebT_deriv (m + 1) (cos φ) * sin φ) =
          (↑m + 1) * (sin ((↑m + 2) * φ) + sin (↑m * φ)) := by
        rw [hih2]
        have : 2 * cos φ * ((↑m + 1) * sin ((↑m + 1) * φ)) =
            (↑m + 1) * (2 * cos φ * sin ((↑m + 1) * φ)) := by ring
        rw [this, h_prod2]
      linear_combination eq1 + eq2 - hih1
    have hgoal_norm :
        (2 * cos ((↑m + 1) * φ) +
          2 * cos φ * chebT_deriv (m + 1) (cos φ) -
          chebT_deriv m (cos φ)) * sin φ =
        (↑m + 1 + 1) * sin ((↑m + 1 + 1) * φ) := by
      have : (↑m + 1 + 1 : ℝ) = ↑m + 2 := by ring
      rw [this]; exact hgoal
    linarith [hgoal_norm]

-- ═══════════════════════════════════════════════════════════════════
-- §9. chebT_deriv at the D-type root: (m+1)/sin(π/(2m+2))
-- ═══════════════════════════════════════════════════════════════════

theorem chebT_deriv_at_root (m : ℕ) :
    chebT_deriv (m + 1) (cos (π / (2 * (↑m + 1)))) *
      sin (π / (2 * (↑m + 1))) = ↑(m + 1) := by
  have h := chebT_deriv_cos_sin (m + 1) (π / (2 * (↑m + 1)))
  rw [show (↑(m + 1) : ℝ) * (π / (2 * (↑m + 1))) = π / 2 from by
    push_cast; field_simp] at h
  rw [sin_pi_div_two, mul_one] at h
  exact h

private lemma sin_half_pos (m : ℕ) : 0 < sin (π / (2 * (↑m + 1))) := by
  apply sin_pos_of_pos_of_lt_pi
  · have h1 : (0:ℝ) < 2 * (↑m + 1) := by positivity
    exact div_pos pi_pos h1
  · have h1 : (0:ℝ) < 2 * (↑m + 1) := by positivity
    rw [div_lt_iff₀ h1]
    nlinarith [pi_pos, show (0:ℝ) ≤ ↑m from Nat.cast_nonneg m]

theorem chebT_deriv_at_root_pos (m : ℕ) :
    0 < chebT_deriv (m + 1) (cos (π / (2 * (↑m + 1)))) := by
  have hs := sin_half_pos m
  have hprod := chebT_deriv_at_root m
  have hmp : (0 : ℝ) < ↑(m + 1) := by positivity
  nlinarith [hprod, hs]

-- ═══════════════════════════════════════════════════════════════════
-- §10. Algebraic derivative of dT and HasDerivAt
-- ═══════════════════════════════════════════════════════════════════

/-- Algebraic λ-derivative of `dT(n, λ)`, satisfying the differentiated
    recurrence:
      dT'(0) = 0,  dT'(1) = 1/2,
      dT'(n+2) = dT(n+1) + λ·dT'(n+1) − dT(n) − λ·dT'(n). -/
noncomputable def dT_deriv : ℕ → ℝ → ℝ
  | 0, _ => 0
  | 1, _ => 1 / 2
  | n + 2, lam => dT lam (n + 1) + lam * dT_deriv (n + 1) lam -
                   dT lam n - lam * dT_deriv n lam

lemma dT_deriv_succ_succ (n : ℕ) (lam : ℝ) :
    dT_deriv (n + 2) lam = dT lam (n + 1) + lam * dT_deriv (n + 1) lam -
                            dT lam n - lam * dT_deriv n lam := rfl

theorem dT_hasDerivAt (n : ℕ) (lam : ℝ) :
    HasDerivAt (fun l => dT l n) (dT_deriv n lam) lam := by
  suffices h : ∀ k : ℕ,
    HasDerivAt (fun l => dT l k) (dT_deriv k lam) lam ∧
    HasDerivAt (fun l => dT l (k + 1)) (dT_deriv (k + 1) lam) lam
    from (h n).1
  intro k; induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · show HasDerivAt (fun l => dT l 0) 0 lam
      simp only [dT_zero]; exact hasDerivAt_const lam 1
    · show HasDerivAt (fun l => dT l 1) (1 / 2) lam
      simp only [dT_one]
      exact (hasDerivAt_id lam).div_const 2
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    show HasDerivAt (fun l => dT l (m + 2)) (dT_deriv (m + 2) lam) lam
    simp only [dT_succ_succ]
    rw [dT_deriv_succ_succ]
    have h1 := (hasDerivAt_id lam).mul ih.2
    have h2 := (hasDerivAt_id lam).mul ih.1
    convert h1.sub h2 using 1
    simp [id]; ring

-- ═══════════════════════════════════════════════════════════════════
-- §11. Connection formula: 4λ · dT'(n) = 2n · dT(n) + s^{n+1} · T'_n(s/2)
-- ═══════════════════════════════════════════════════════════════════

/-- **Connection formula** (D-type analog).
    `4λ · dT'(n, λ) = 2n · dT(n, λ) + (√λ)^{n+1} · T'_n(√λ/2)`.

    This bridges the algebraic `dT_deriv` to the Chebyshev-derivative
    `chebT_deriv`, parallelling the A-type `d_deriv_formula`. -/
theorem dT_deriv_formula (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    4 * lam * dT_deriv n lam =
    2 * ↑n * dT lam n +
    (Real.sqrt lam) ^ (n + 1) * chebT_deriv n (Real.sqrt lam / 2) := by
  set s := Real.sqrt lam with hs_def
  set t := s / 2 with ht_def
  have hs : s * s = lam := Real.mul_self_sqrt hlam.le
  suffices h : ∀ k : ℕ,
    4 * lam * dT_deriv k lam =
      2 * ↑k * dT lam k + s ^ (k + 1) * chebT_deriv k t ∧
    4 * lam * dT_deriv (k + 1) lam =
      2 * ↑(k + 1) * dT lam (k + 1) + s ^ (k + 2) * chebT_deriv (k + 1) t
    from (h n).1
  intro k; induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp [dT_deriv, dT_zero, chebT_deriv_zero]
    · -- n = 1: LHS = 4λ · (1/2) = 2λ.  RHS = 2·(λ/2) + s² · 1 = λ + λ = 2λ.
      simp only [dT_deriv, dT_one, chebT_deriv_one, Nat.zero_add, Nat.cast_one]
      have hpow : s ^ 2 = s * s := by ring
      rw [hpow, hs]; ring
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    have h1 := ih.1
    have h2 := ih.2
    have hlam_ss : lam = s * s := hs.symm
    -- Use the closed form to express dT (m+1) as s^(m+1) · T_{m+1}(t)
    have hdc : dT (s * s) (m + 1) = s ^ (m + 1) * chebT (m + 1) t := by
      rw [← hlam_ss]
      have := dT_eq_chebT lam hlam (m + 1)
      rw [← hs_def, ← ht_def] at this
      exact this
    -- Expand dT_deriv(m+2) recurrence on LHS
    rw [show dT_deriv (m + 1 + 1) lam = dT lam (m + 1) + lam * dT_deriv (m + 1) lam -
          dT lam m - lam * dT_deriv m lam from rfl]
    -- Expand chebT_deriv(m+2) recurrence on RHS
    rw [chebT_deriv_succ_succ]
    -- Expand dT(m+2) on the RHS
    conv_rhs => rw [show dT lam (m + 2) =
      lam * dT lam (m + 1) - lam * dT lam m from rfl]
    -- Replace lam with s*s to align all sides
    rw [hlam_ss] at h1 h2 ⊢
    -- Rewrite dT (m+1) via closed form
    rw [hdc] at h2 ⊢
    -- 2 * t = s
    rw [show (2 : ℝ) * t = s from by rw [ht_def]; ring]
    push_cast at h1 h2 ⊢
    clear_value s t
    linear_combination (s * s) * h2 - (s * s) * h1

-- ═══════════════════════════════════════════════════════════════════
-- §12. Transversality at the D-type threshold
-- ═══════════════════════════════════════════════════════════════════

/-- **D-type transversality.**
    `dT'(m+1, α_D m) > 0` at the balanced threshold.

    Using the connection formula at `λ = α_D m` (where `dT(m+1, α_D) = 0`):
      `4 α_D · dT'(m+1, α_D) = (2cos θ)^{m+2} · T'_{m+1}(cos θ)`
    and `T'_{m+1}(cos θ) = (m+1)/sin θ > 0`. -/
theorem dT_deriv_pos_at_threshold (m : ℕ) (hm : 0 < m) :
    0 < dT_deriv (m + 1) (α_D m) := by
  have hα_pos := α_D_pos m hm
  have hdT_zero : dT (α_D m) (m + 1) = 0 := dT_vanishes_at_threshold m hm
  have hform := dT_deriv_formula (α_D m) hα_pos (m + 1)
  rw [hdT_zero, mul_zero, zero_add, sqrt_α_D m hm] at hform
  rw [show (2 * cos (π / (2 * (↑m + 1)))) / 2 = cos (π / (2 * (↑m + 1)))
      from by ring] at hform
  -- hform : 4 α_D · dT'(m+1) = (2 cos θ)^{m+2} · chebT_deriv (m+1) (cos θ)
  set c := cos (π / (2 * (↑m + 1)))
  set θs := sin (π / (2 * (↑m + 1)))
  have hc_pos : 0 < c := cos_half_pos m hm
  have hs_pos : 0 < θs := sin_half_pos m
  have hT'_pos : 0 < chebT_deriv (m + 1) c := chebT_deriv_at_root_pos m
  have h4α_pos : 0 < 4 * α_D m := by positivity
  -- From hform: dT_deriv (m+1) (α_D m) = (2c)^{m+2} · chebT_deriv (m+1) c / (4 α_D)
  have h_pow_pos : 0 < (2 * c) ^ (m + 2) := by positivity
  have h_num_pos : 0 < (2 * c) ^ (m + 2) * chebT_deriv (m + 1) c :=
    mul_pos h_pow_pos hT'_pos
  -- hform says: 4 α_D · dT_deriv = h_num; so dT_deriv = h_num / (4 α_D) > 0
  have hprod : 4 * α_D m * dT_deriv (m + 1) (α_D m) > 0 := by linarith
  exact (mul_pos_iff_of_pos_left h4α_pos).mp hprod

end DTypeScalingLaw
