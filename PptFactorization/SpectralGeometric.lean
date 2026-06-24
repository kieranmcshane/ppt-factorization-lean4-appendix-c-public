import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import PptFactorization.General
import PptFactorization.ClosedFormDet
import PptFactorization.Threshold
import PptFactorization.SubfactorBridge

/-!
# Spectral-geometric route to the −1/d₁ correction

Recasts the asymmetric PPT perturbation in terms of the adjacency
matrix of the principal graph A_{m+1}.

Key results:
- `root_amplitude_sq` : |ψ_{m+1}(0)|² = 2sin²(π/(m+2))/(m+2)
- `correction_general_graph` : Δλ_Γ = −|ψ̃(v₀)|²_Tr / d₁
- `correction_TL` : trace-normalised root amplitude = 1 ⟹ Δλ = −1/d₁
- `cd_normalisation` : root_amplitude_sq × D² = 1 for all m

Institut Fourier, Grenoble — Kieran McShane / Cécilia Lancien
-/

open Real

namespace SpectralGeometric

-- ═══════════════════════════════════════════════════════════════════
-- §1. Eigenvector of A_{m+1} and root amplitude
-- ═══════════════════════════════════════════════════════════════════

/-- The normalised eigenvector of the path graph A_{m+1} at vertex k,
    for the j-th eigenvalue ν_j = 2cos(jπ/(m+2)).
    ψ_j(k) = √(2/(m+2)) · sin(j(k+1)π/(m+2)). -/
noncomputable def pf_eigenvector (m : ℕ) (j : Fin (m + 1)) (k : Fin (m + 1)) : ℝ :=
  Real.sqrt (2 / (↑m + 2)) *
  Real.sin (↑(j.val + 1) * (↑(k.val + 1)) * π / (↑m + 2))

/-- The squared amplitude of the Perron–Frobenius eigenvector at the
    root vertex (k = 0).  For j = m+1 (the extremal eigenvalue),
    |ψ_{m+1}(0)|² = (2/(m+2)) · sin²(π/(m+2)). -/
noncomputable def root_amplitude_sq (m : ℕ) : ℝ :=
  2 / (↑m + 2) * (Real.sin (π / (↑m + 2))) ^ 2

/-- The root amplitude equals the squared eigenvector at (j=m, k=0).
    Key step: sin((m+1)π/(m+2)) = sin(π − π/(m+2)) = sin(π/(m+2)). -/
theorem root_amplitude_eq_eigenvector_sq (m : ℕ) :
    (pf_eigenvector m ⟨m, Nat.lt_succ_iff.mpr le_rfl⟩ ⟨0, Nat.zero_lt_succ m⟩) ^ 2 =
    root_amplitude_sq m := by
  unfold pf_eigenvector root_amplitude_sq
  simp only [Nat.zero_add]
  rw [mul_pow]
  congr 1
  · exact sq_sqrt (by positivity : (2 : ℝ) / (↑m + 2) ≥ 0)
  · congr 1
    have hm2 : (↑m + 2 : ℝ) ≠ 0 := by positivity
    -- sin((m+1)·1·π/(m+2)) = sin(π − π/(m+2)) = sin(π/(m+2))
    simp only [Nat.cast_one, mul_one]
    have : (↑(m + 1) : ℝ) * π / (↑m + 2) = π - π / (↑m + 2) := by
      push_cast; field_simp; ring
    rw [this, Real.sin_pi_sub]

-- ═══════════════════════════════════════════════════════════════════
-- §2. Root amplitude values for m = 1, 2
-- ═══════════════════════════════════════════════════════════════════

/-- For m = 1: root_amplitude = 2/3 · sin²(π/3) = 2/3 · 3/4 = 1/2. -/
theorem root_amplitude_m1 : root_amplitude_sq 1 = 1 / 2 := by
  unfold root_amplitude_sq
  simp only [Nat.cast_one]
  -- Need: sin(π/3) = √3/2, so sin²(π/3) = 3/4
  have h3 : Real.sin (π / (1 + 2 : ℝ)) = Real.sin (π / 3) := by norm_num
  rw [h3, Real.sin_pi_div_three]
  rw [div_pow, sq_sqrt (by positivity : (3 : ℝ) ≥ 0)]
  norm_num

/-- For m = 2: root_amplitude = 2/4 · sin²(π/4) = 1/2 · 1/2 = 1/4. -/
theorem root_amplitude_m2 : root_amplitude_sq 2 = 1 / 4 := by
  unfold root_amplitude_sq
  simp only [Nat.cast_ofNat]
  have h4 : Real.sin (π / (2 + 2 : ℝ)) = Real.sin (π / 4) := by norm_num
  rw [h4, Real.sin_pi_div_four]
  rw [div_pow, sq_sqrt (by positivity : (2 : ℝ) ≥ 0)]
  norm_num

-- ═══════════════════════════════════════════════════════════════════
-- §3. Trace-normalised correction formula
-- ═══════════════════════════════════════════════════════════════════

/-- For a general principal graph Γ, the asymmetric correction is
      Δλ_Γ = −|ψ̃_min(v₀)|²_Tr / d₁
    where ψ̃ is normalised in the Markov-trace inner product. -/
noncomputable def correction_general_graph
    (root_amplitude_trace : ℝ)  -- |ψ̃_min(v₀)|²_Tr
    (d₁ : ℝ) : ℝ :=
  -root_amplitude_trace / d₁

/-- For Γ = A_{m+1} (Temperley–Lieb), the trace-normalised root
    amplitude is 1, giving the universal −1/d₁. -/
theorem correction_TL (d₁ : ℝ) (_hd : d₁ ≠ 0) :
    correction_general_graph 1 d₁ = -1 / d₁ := by
  unfold correction_general_graph; ring

-- ═══════════════════════════════════════════════════════════════════
-- §4. Christoffel–Darboux normalisation
-- ═══════════════════════════════════════════════════════════════════

/-- **Christoffel–Darboux normalisation.**
    root_amplitude_sq m · D² = 1, where
    D² = (m+2) / (2 sin²(π/(m+2))).

    This is the content of eq (11.8) in the notes: the trace-normalised
    root amplitude equals 1 for all m. -/
theorem cd_normalisation (m : ℕ) :
    root_amplitude_sq m * ((↑m + 2) / (2 * (Real.sin (π / (↑m + 2))) ^ 2)) = 1 := by
  unfold root_amplitude_sq
  have hm2 : (↑m + 2 : ℝ) ≠ 0 := by positivity
  have hsin : Real.sin (π / (↑m + 2)) ≠ 0 := by
    apply ne_of_gt
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · have hm2pos : (0 : ℝ) < ↑m + 2 := by positivity
      rw [div_lt_iff₀ hm2pos]
      nlinarith [pi_pos, show (0 : ℝ) ≤ ↑m from Nat.cast_nonneg m]
  field_simp

end SpectralGeometric
