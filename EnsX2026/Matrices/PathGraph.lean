import EnsX2026.Matrices.Circulant
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# ENS/Polytechnique 2026 Math A — Q25

We study the Laplacian `L_n` of the path graph on `n` vertices
`1 — 2 — ⋯ — n`, with endpoints of degree 1 and interior vertices of degree 2.

Exploiting reflection symmetry of the cycle `C_{2n}` we fold reflection-
symmetric eigenvectors of `C_{2n}` into eigenvectors of `L_n`. The concrete
family obtained is

  `v_k(j) = cos(π k (2 j + 1) / (2 n))`, `k ∈ [0, n)`,

with eigenvalues

  `4 sin²(π k / (2 n)) = 2 − 2 cos(π k / n)`.

* **Q25(a)** (folding theorem) — a pure recurrence check at the boundary.
* **Q25(b)** (cosine basis diagonalises `L_n`) — a direct trigonometric
  computation via `Complex.cos_add_cos`, `Complex.cos_sub_cos`, `Complex.sin_two_mul`
  and `Complex.cos_two_mul_eq_one_sub`.

Institut Fourier, Grenoble — Kieran McShane
-/

noncomputable section

namespace EnsX2026.Matrices.PathGraph

open Matrix Complex Finset

/-! ### Definition of the path graph Laplacian -/

/-- The Laplacian of the path graph on `n` vertices `0 — 1 — ⋯ — (n−1)`.
Endpoints `0` and `n−1` have degree `1`; interior vertices have degree `2`. -/
def path_laplacian (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j =>
    if i = j then
      (if i.val = 0 ∨ i.val + 1 = n then (1 : ℂ) else 2)
    else if i.val + 1 = j.val ∨ j.val + 1 = i.val then (-1 : ℂ)
    else 0

/-- Entry formula for `path_laplacian`. -/
lemma path_laplacian_apply (n : ℕ) (i j : Fin n) :
    path_laplacian n i j =
      if i = j then
        (if i.val = 0 ∨ i.val + 1 = n then (1 : ℂ) else 2)
      else if i.val + 1 = j.val ∨ j.val + 1 = i.val then (-1 : ℂ)
      else 0 := rfl

/-! ### Row expansion of `path_laplacian *ᵥ v`

For each row `i`, at most three entries are nonzero (the diagonal and the two
adjacent columns `i±1`). We peel off these contributions via `Finset.sum_insert`,
reducing the rest of the sum to zero. -/

/-- Three-term row formula at an *interior* vertex. -/
lemma path_laplacian_mulVec_interior (n : ℕ) (v : Fin n → ℂ)
    (i : Fin n) (hlo : 1 ≤ i.val) (hhi : i.val + 2 ≤ n) :
    (path_laplacian n).mulVec v i =
      2 * v i
        - v ⟨i.val - 1, by omega⟩
        - v ⟨i.val + 1, by omega⟩ := by
  set iL : Fin n := ⟨i.val - 1, by omega⟩
  set iR : Fin n := ⟨i.val + 1, by omega⟩
  have hiL_ne : iL ≠ i := by
    intro h; have := congrArg Fin.val h
    simp [iL] at this; omega
  have hiR_ne : iR ≠ i := by
    intro h; have := congrArg Fin.val h
    simp [iR] at this
  have hiL_ne_iR : iL ≠ iR := by
    intro h; have := congrArg Fin.val h
    simp [iL, iR] at this
  -- Decompose univ = {iL, i, iR} ∪ (univ \ {iL, i, iR}).
  have hiL_mem : iL ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
  have hi_mem : i ∈ (Finset.univ : Finset (Fin n)).erase iL := by
    rw [Finset.mem_erase]
    exact ⟨fun h => hiL_ne h.symm, Finset.mem_univ _⟩
  have hiR_mem : iR ∈ ((Finset.univ : Finset (Fin n)).erase iL).erase i := by
    rw [Finset.mem_erase, Finset.mem_erase]
    exact ⟨hiR_ne, fun h => hiL_ne_iR h.symm, Finset.mem_univ _⟩
  -- Convert mulVec to a sum.
  show ∑ j, path_laplacian n i j * v j = 2 * v i - v iL - v iR
  rw [← Finset.add_sum_erase _ _ hiL_mem]
  rw [← Finset.add_sum_erase _ _ hi_mem]
  rw [← Finset.add_sum_erase _ _ hiR_mem]
  -- Compute the three named contributions.
  have h_iL : path_laplacian n i iL * v iL = -1 * v iL := by
    rw [path_laplacian_apply]
    have hne : i ≠ iL := fun h => hiL_ne h.symm
    rw [if_neg hne]
    have hadj : iL.val + 1 = i.val := by simp [iL]; omega
    rw [if_pos (Or.inr hadj)]
  have h_i : path_laplacian n i i * v i = 2 * v i := by
    rw [path_laplacian_apply]
    rw [if_pos rfl]
    have : ¬ (i.val = 0 ∨ i.val + 1 = n) := by push_neg; exact ⟨by omega, by omega⟩
    rw [if_neg this]
  have h_iR : path_laplacian n i iR * v iR = -1 * v iR := by
    rw [path_laplacian_apply]
    have hne : i ≠ iR := fun h => hiR_ne h.symm
    rw [if_neg hne]
    have hadj : i.val + 1 = iR.val := by simp [iR]
    rw [if_pos (Or.inl hadj)]
  -- The remaining sum over `univ.erase iL .erase i .erase iR` is zero.
  have h_rest :
      (∑ k ∈ (((Finset.univ : Finset (Fin n)).erase iL).erase i).erase iR,
          path_laplacian n i k * v k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_erase, Finset.mem_erase, Finset.mem_erase] at hk
    obtain ⟨hkR, hki, hkL, _⟩ := hk
    rw [path_laplacian_apply]
    have hne : i ≠ k := fun h => hki h.symm
    rw [if_neg hne]
    have : ¬ (i.val + 1 = k.val ∨ k.val + 1 = i.val) := by
      push_neg
      refine ⟨?_, ?_⟩
      · intro heq
        apply hkR
        apply Fin.ext
        simp [iR]
        exact heq.symm
      · intro heq
        apply hkL
        apply Fin.ext
        simp [iL]
        omega
    rw [if_neg this, zero_mul]
  rw [h_iL, h_i, h_iR, h_rest]
  ring

/-- Two-term row formula at the *left* endpoint. -/
lemma path_laplacian_mulVec_left (n : ℕ) (hn : 2 ≤ n) (v : Fin n → ℂ) :
    (path_laplacian n).mulVec v ⟨0, by omega⟩ =
      v ⟨0, by omega⟩ - v ⟨1, by omega⟩ := by
  set i : Fin n := ⟨0, by omega⟩
  set iR : Fin n := ⟨1, by omega⟩
  have hiR_ne : iR ≠ i := by
    intro h; have := congrArg Fin.val h
    simp [i, iR] at this
  have hi_mem : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
  have hiR_mem : iR ∈ (Finset.univ : Finset (Fin n)).erase i := by
    rw [Finset.mem_erase]; exact ⟨hiR_ne, Finset.mem_univ _⟩
  show ∑ j, path_laplacian n i j * v j = v i - v iR
  rw [← Finset.add_sum_erase _ _ hi_mem]
  rw [← Finset.add_sum_erase _ _ hiR_mem]
  have h_i : path_laplacian n i i * v i = 1 * v i := by
    rw [path_laplacian_apply]
    rw [if_pos rfl]
    have : i.val = 0 ∨ i.val + 1 = n := Or.inl (by simp [i])
    rw [if_pos this]
  have h_iR : path_laplacian n i iR * v iR = -1 * v iR := by
    rw [path_laplacian_apply]
    have hne : i ≠ iR := fun h => hiR_ne h.symm
    rw [if_neg hne]
    have hadj : i.val + 1 = iR.val := by simp [i, iR]
    rw [if_pos (Or.inl hadj)]
  have h_rest :
      (∑ k ∈ ((Finset.univ : Finset (Fin n)).erase i).erase iR,
          path_laplacian n i k * v k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_erase, Finset.mem_erase] at hk
    obtain ⟨hkR, hki, _⟩ := hk
    rw [path_laplacian_apply]
    have hne : i ≠ k := fun h => hki h.symm
    rw [if_neg hne]
    have : ¬ (i.val + 1 = k.val ∨ k.val + 1 = i.val) := by
      push_neg
      refine ⟨?_, ?_⟩
      · intro heq
        apply hkR
        apply Fin.ext
        simp [iR]
        have : i.val = 0 := by simp [i]
        omega
      · intro heq
        -- i.val = 0 so k.val + 1 = 0 is impossible
        have : i.val = 0 := by simp [i]
        omega
    rw [if_neg this, zero_mul]
  rw [h_i, h_iR, h_rest]
  ring

/-- Two-term row formula at the *right* endpoint. -/
lemma path_laplacian_mulVec_right (n : ℕ) (hn : 2 ≤ n) (v : Fin n → ℂ) :
    (path_laplacian n).mulVec v ⟨n - 1, by omega⟩ =
      v ⟨n - 1, by omega⟩ - v ⟨n - 2, by omega⟩ := by
  set i : Fin n := ⟨n - 1, by omega⟩
  set iL : Fin n := ⟨n - 2, by omega⟩
  have hiL_ne : iL ≠ i := by
    intro h; have := congrArg Fin.val h
    simp [i, iL] at this; omega
  have hiL_mem : iL ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
  have hi_mem : i ∈ (Finset.univ : Finset (Fin n)).erase iL := by
    rw [Finset.mem_erase]; exact ⟨fun h => hiL_ne h.symm, Finset.mem_univ _⟩
  show ∑ j, path_laplacian n i j * v j = v i - v iL
  rw [← Finset.add_sum_erase _ _ hiL_mem]
  rw [← Finset.add_sum_erase _ _ hi_mem]
  have h_iL : path_laplacian n i iL * v iL = -1 * v iL := by
    rw [path_laplacian_apply]
    have hne : i ≠ iL := fun h => hiL_ne h.symm
    rw [if_neg hne]
    have hadj : iL.val + 1 = i.val := by simp [i, iL]; omega
    rw [if_pos (Or.inr hadj)]
  have h_i : path_laplacian n i i * v i = 1 * v i := by
    rw [path_laplacian_apply]
    rw [if_pos rfl]
    have : i.val = 0 ∨ i.val + 1 = n := Or.inr (by simp [i]; omega)
    rw [if_pos this]
  have h_rest :
      (∑ k ∈ ((Finset.univ : Finset (Fin n)).erase iL).erase i,
          path_laplacian n i k * v k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_erase, Finset.mem_erase] at hk
    obtain ⟨hki, hkL, _⟩ := hk
    rw [path_laplacian_apply]
    have hne : i ≠ k := fun h => hki h.symm
    rw [if_neg hne]
    have : ¬ (i.val + 1 = k.val ∨ k.val + 1 = i.val) := by
      push_neg
      have hi_val : i.val = n - 1 := by simp [i]
      have hiL_val : iL.val = n - 2 := by simp [iL]
      refine ⟨?_, ?_⟩
      · intro heq
        have hkl := k.isLt
        omega
      · intro heq
        apply hkL
        apply Fin.ext
        omega
    rw [if_neg this, zero_mul]
  rw [h_iL, h_i, h_rest]
  ring

/-! ### Q25(b) — Cosine eigenvectors of `L_n`

We show that `v_k(j) = cos(π k (2 j + 1) / (2 n))` is an eigenvector of
`L_n` with eigenvalue `4 sin²(π k / (2 n))`, by a direct trigonometric
computation. -/

/-- The `k`-th cosine mode on `Fin n`:
`cosine_mode n k (j) = cos(π k (2 j + 1) / (2 n))`. -/
def cosine_mode (n k : ℕ) : Fin n → ℂ :=
  fun j => Complex.cos (Real.pi * k * (2 * j.val + 1) / (2 * n))

/-- Helper: `1 − cos(2α) = 2 sin²(α)` over `ℂ`. -/
lemma one_sub_cos_two_mul (α : ℂ) : 1 - Complex.cos (2 * α) = 2 * Complex.sin α ^ 2 := by
  rw [Complex.cos_two_mul_eq_one_sub]; ring

/-- Left-endpoint trig identity:
`cos(α) − cos(3α) = 4 sin²(α) cos(α)`. -/
lemma cos_sub_cos_three (α : ℂ) :
    Complex.cos α - Complex.cos (3 * α) = 4 * Complex.sin α ^ 2 * Complex.cos α := by
  have h1 : Complex.cos α - Complex.cos (3 * α) =
      -2 * Complex.sin ((α + 3 * α) / 2) * Complex.sin ((α - 3 * α) / 2) :=
    Complex.cos_sub_cos α (3 * α)
  have hmid : (α + 3 * α) / 2 = 2 * α := by ring
  have hdif : (α - 3 * α) / 2 = -α := by ring
  rw [h1, hmid, hdif, Complex.sin_neg, Complex.sin_two_mul]
  ring

/-- Right-endpoint trig identity: at a phase `φ` satisfying `sin(φ + α) = 0`
(i.e. `φ + α = π · integer`), we have
`cos(φ) − cos(φ − 2α) = 4 sin²(α) cos(φ)`. -/
lemma cos_sub_cos_shift_of_sin_sum_zero (φ α : ℂ) (h : Complex.sin (φ + α) = 0) :
    Complex.cos φ - Complex.cos (φ - 2 * α) = 4 * Complex.sin α ^ 2 * Complex.cos φ := by
  -- cos φ − cos(φ − 2α) = −2 sin(φ − α) sin α.
  have hcc : Complex.cos φ - Complex.cos (φ - 2 * α)
      = -2 * Complex.sin (φ - α) * Complex.sin α := by
    have := Complex.cos_sub_cos φ (φ - 2 * α)
    have hmid : (φ + (φ - 2 * α)) / 2 = φ - α := by ring
    have hdif : (φ - (φ - 2 * α)) / 2 = α := by ring
    rw [this, hmid, hdif]
  rw [hcc]
  -- From sin(φ + α) = 0: sin φ cos α = − cos φ sin α.
  have hadd : Complex.sin (φ + α) =
      Complex.sin φ * Complex.cos α + Complex.cos φ * Complex.sin α :=
    Complex.sin_add φ α
  have hsp : Complex.sin φ * Complex.cos α = - (Complex.cos φ * Complex.sin α) := by
    have := hadd.symm.trans h
    linear_combination this
  -- sin(φ − α) = sin φ cos α − cos φ sin α = −2 cos φ sin α.
  have hsub : Complex.sin (φ - α) = -2 * (Complex.cos φ * Complex.sin α) := by
    rw [Complex.sin_sub]
    linear_combination hsp
  rw [hsub]
  ring

/-- (Q25b) The cosine mode is an eigenvector of the path Laplacian
with eigenvalue `4 sin²(π k / (2 n))`. -/
theorem path_laplacian_cosine_eigenvector (n : ℕ) (hn : 2 ≤ n) (k : ℕ) (_hk : k < n) :
    (path_laplacian n).mulVec (cosine_mode n k) =
      (4 * Real.sin (Real.pi * k / (2 * n)) ^ 2 : ℂ) • cosine_mode n k := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  -- Complex phase θ and eigenvalue simplification.
  set θC : ℂ := ((Real.pi * k / (2 * n) : ℝ) : ℂ) with hθCdef
  have heig : (4 * Real.sin (Real.pi * k / (2 * n)) ^ 2 : ℂ) = 4 * Complex.sin θC ^ 2 := by
    simp only [θC]
    push_cast
    rfl
  rw [heig]
  have hn_ne : (n : ℂ) ≠ 0 := by
    have : (n : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  -- Convenience: given a phase of the form `π k (2 m + 1) / (2 n)` with `m : ℂ`,
  -- rewrite it in terms of θC.
  have phase_eq : ∀ m : ℂ,
      (Real.pi : ℂ) * k * (2 * m + 1) / (2 * n) = (2 * m + 1) * θC := by
    intro m
    show (Real.pi : ℂ) * k * (2 * m + 1) / (2 * n)
           = (2 * m + 1) * ((Real.pi * k / (2 * n) : ℝ) : ℂ)
    push_cast
    field_simp
  -- Case-split.
  by_cases h0 : i.val = 0
  · -- Left endpoint.
    have hi : i = ⟨0, by omega⟩ := Fin.ext h0
    rw [hi]
    rw [path_laplacian_mulVec_left n hn (cosine_mode n k)]
    show Complex.cos ((Real.pi : ℂ) * k * (2 * ((⟨0, by omega⟩ : Fin n).val : ℂ) + 1) / (2 * n))
          - Complex.cos ((Real.pi : ℂ) * k * (2 * ((⟨1, by omega⟩ : Fin n).val : ℂ) + 1) / (2 * n))
         = 4 * Complex.sin θC ^ 2 *
             Complex.cos ((Real.pi : ℂ) * k * (2 * ((⟨0, by omega⟩ : Fin n).val : ℂ) + 1) / (2 * n))
    have h_v0 : ((⟨0, by omega⟩ : Fin n).val : ℂ) = 0 := by push_cast; rfl
    have h_v1 : ((⟨1, by omega⟩ : Fin n).val : ℂ) = 1 := by push_cast; rfl
    rw [h_v0, h_v1]
    rw [phase_eq 0, phase_eq 1]
    -- Goal: cos ((2·0+1)·θC) − cos ((2·1+1)·θC) = 4 sin² θC · cos ((2·0+1)·θC).
    -- Normalize `(2·0+1)·θC = θC` and `(2·1+1)·θC = 3·θC`.
    have h0' : (2 * (0 : ℂ) + 1) * θC = θC := by ring
    have h3' : (2 * (1 : ℂ) + 1) * θC = 3 * θC := by ring
    rw [h0', h3']
    exact cos_sub_cos_three θC
  · by_cases h1 : i.val + 1 = n
    · -- Right endpoint.
      have hi : i = ⟨n - 1, by omega⟩ := by
        apply Fin.ext
        show i.val = n - 1
        omega
      rw [hi]
      rw [path_laplacian_mulVec_right n hn (cosine_mode n k)]
      show Complex.cos ((Real.pi : ℂ) * k * (2 * ((⟨n - 1, by omega⟩ : Fin n).val : ℂ) + 1) / (2 * n))
            - Complex.cos ((Real.pi : ℂ) * k * (2 * ((⟨n - 2, by omega⟩ : Fin n).val : ℂ) + 1) / (2 * n))
           = 4 * Complex.sin θC ^ 2 *
               Complex.cos ((Real.pi : ℂ) * k * (2 * ((⟨n - 1, by omega⟩ : Fin n).val : ℂ) + 1) / (2 * n))
      -- Rewrite indices to concrete (n:ℂ) - 1 and (n:ℂ) - 2.
      have h_vnm1 : ((⟨n - 1, by omega⟩ : Fin n).val : ℂ) = (n : ℂ) - 1 := by
        show ((n - 1 : ℕ) : ℂ) = (n : ℂ) - 1
        rw [Nat.cast_sub (show 1 ≤ n by omega)]; push_cast; ring
      have h_vnm2 : ((⟨n - 2, by omega⟩ : Fin n).val : ℂ) = (n : ℂ) - 2 := by
        show ((n - 2 : ℕ) : ℂ) = (n : ℂ) - 2
        rw [Nat.cast_sub (show 2 ≤ n by omega)]; push_cast; ring
      rw [h_vnm1, h_vnm2]
      rw [phase_eq ((n : ℂ) - 1), phase_eq ((n : ℂ) - 2)]
      -- Now LHS is cos((2(n-1)+1)θ) - cos((2(n-2)+1)θ)
      --         = cos((2n-1)θ) - cos((2n-3)θ).
      -- Set φ = (2(n-1)+1)θ = (2(n-1)+1)·θ. Then the other phase is φ - 2θ.
      set φ : ℂ := (2 * ((n : ℂ) - 1) + 1) * θC with hφdef
      have hψ : (2 * ((n : ℂ) - 2) + 1) * θC = φ - 2 * θC := by
        simp [φ]; ring
      rw [hψ]
      -- Need: sin(φ + θ) = 0, i.e., (2(n-1)+1+1)θ = 2n·θ = πk.
      have hφθ_eq : φ + θC = ((Real.pi * k : ℝ) : ℂ) := by
        simp [φ, θC]
        field_simp
        ring
      have hsin_zero : Complex.sin (φ + θC) = 0 := by
        rw [hφθ_eq]
        have hoc : Complex.sin ((Real.pi * k : ℝ) : ℂ) = ((Real.sin (Real.pi * k) : ℝ) : ℂ) := by
          exact (Complex.ofReal_sin (Real.pi * k)).symm
        rw [hoc]
        have : Real.sin (Real.pi * k) = 0 := by
          rw [mul_comm]; exact Real.sin_nat_mul_pi k
        rw [this]; simp
      exact cos_sub_cos_shift_of_sin_sum_zero φ θC hsin_zero
    · -- Interior vertex.
      have hlo : 1 ≤ i.val := by omega
      have hhi : i.val + 2 ≤ n := by omega
      rw [path_laplacian_mulVec_interior n (cosine_mode n k) i hlo hhi]
      show 2 * Complex.cos ((Real.pi : ℂ) * k * (2 * (i.val : ℂ) + 1) / (2 * n))
            - Complex.cos ((Real.pi : ℂ) * k * (2 * ((⟨i.val - 1, by omega⟩ : Fin n).val : ℂ) + 1) / (2 * n))
            - Complex.cos ((Real.pi : ℂ) * k * (2 * ((⟨i.val + 1, by omega⟩ : Fin n).val : ℂ) + 1) / (2 * n))
          = 4 * Complex.sin θC ^ 2 * Complex.cos ((Real.pi : ℂ) * k * (2 * (i.val : ℂ) + 1) / (2 * n))
      have h_vim1 : ((⟨i.val - 1, by omega⟩ : Fin n).val : ℂ) = (i.val : ℂ) - 1 := by
        show ((i.val - 1 : ℕ) : ℂ) = (i.val : ℂ) - 1
        rw [Nat.cast_sub hlo]; push_cast; ring
      have h_vip1 : ((⟨i.val + 1, by omega⟩ : Fin n).val : ℂ) = (i.val : ℂ) + 1 := by
        show ((i.val + 1 : ℕ) : ℂ) = (i.val : ℂ) + 1
        push_cast; ring
      rw [h_vim1, h_vip1]
      rw [phase_eq (i.val : ℂ), phase_eq ((i.val : ℂ) - 1), phase_eq ((i.val : ℂ) + 1)]
      -- Set α := (2 i.val + 1) θ. Then the two other phases are α − 2θ and α + 2θ.
      set α : ℂ := (2 * (i.val : ℂ) + 1) * θC with hαdef
      have hβ : (2 * ((i.val : ℂ) - 1) + 1) * θC = α - 2 * θC := by simp [α]; ring
      have hγ : (2 * ((i.val : ℂ) + 1) + 1) * θC = α + 2 * θC := by simp [α]; ring
      rw [hβ, hγ]
      -- Apply the three-term identity.
      have hsum_id :
          Complex.cos (α - 2 * θC) + Complex.cos (α + 2 * θC)
            = 2 * Complex.cos α * Complex.cos (2 * θC) := by
        have := Complex.cos_add_cos (α - 2 * θC) (α + 2 * θC)
        have hmid : ((α - 2 * θC) + (α + 2 * θC)) / 2 = α := by ring
        have hdif : ((α - 2 * θC) - (α + 2 * θC)) / 2 = -(2 * θC) := by ring
        rw [this, hmid, hdif, Complex.cos_neg]
      have hone_sub := one_sub_cos_two_mul θC
      linear_combination Complex.cos α * hone_sub * 2 - hsum_id

/-! ### Q25(a) — Fold from `C_{2n}` to `L_n`

If `x : ZMod (2n) → ℂ` is an eigenvector of `C_{2n}` with eigenvalue `λ`
and satisfies the reflection-symmetric boundary conditions
`x(−1) = x(0)` and `x(n) = x(n−1)`, then the restriction
`y(i) := x(i.val)` to `Fin n` is an eigenvector of `L_n` with the same
eigenvalue.

**Note on boundary conditions.** The exam states `x_{n+1} = x_n` and
`x_{2n} = x_1` in 1-indexed notation. Converting to 0-indexed notation
(with `ZMod (2n) = {0, 1, …, 2n−1}`), `x_{2n}` is the cyclic predecessor of
`x_1`, i.e. `x_{2n−1} = x(−1)`, while `x_1` is `x(0)`. Thus `x_{2n} = x_1`
becomes `x(−1) = x(0)`. The second condition `x_{n+1} = x_n` becomes
`x(n) = x(n−1)`. These are the conditions under which the cycle and path
Laplacian equations match up exactly.
-/

/-- Row formula for the cycle Laplacian: `(C_{2n} x)(m) = 2 x(m) − x(m−1) − x(m+1)`. -/
private lemma cycle_laplacian_mulVec_apply (n : ℕ) (hn : 3 ≤ 2 * n)
    [NeZero (2 * n)]
    (x : ZMod (2 * n) → ℂ) (m : ZMod (2 * n)) :
    (Circulant.cycle_laplacian (2 * n) hn).mulVec x m =
      2 * x m - x (m - 1) - x (m + 1) := by
  rw [Circulant.cycle_laplacian_eq (2 * n) hn,
      Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  have hJ : (Circulant.shift_matrix (2 * n)).mulVec x m = x (m - 1) := by
    show ∑ j, (Circulant.shift_matrix (2 * n)) m j * x j = x (m - 1)
    unfold Circulant.shift_matrix
    simp only [Matrix.circulant_apply]
    rw [show (∑ j, (if m - j = (1 : ZMod (2*n)) then (1 : ℂ) else 0) * x j)
          = ∑ j, (if j = (1 : ZMod (2*n)) then (1 : ℂ) else 0) * x (m - j) from by
      refine Fintype.sum_equiv (Equiv.subLeft m) _ _ (fun j => ?_)
      simp]
    rw [Finset.sum_eq_single (1 : ZMod (2*n))]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; simp at h
  have hJinv : (Circulant.shift_matrix_inv (2 * n)).mulVec x m = x (m + 1) := by
    show ∑ j, (Circulant.shift_matrix_inv (2 * n)) m j * x j = x (m + 1)
    unfold Circulant.shift_matrix_inv
    simp only [Matrix.circulant_apply]
    rw [show (∑ j, (if m - j = (-1 : ZMod (2*n)) then (1 : ℂ) else 0) * x j)
          = ∑ j, (if j = (-1 : ZMod (2*n)) then (1 : ℂ) else 0) * x (m - j) from by
      refine Fintype.sum_equiv (Equiv.subLeft m) _ _ (fun j => ?_)
      simp]
    rw [Finset.sum_eq_single (-1 : ZMod (2*n))]
    · have hm : m - (-1 : ZMod (2*n)) = m + 1 := by ring
      simp [hm]
    · intro b _ hb; simp [hb]
    · intro h; simp at h
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hJ, hJinv]

theorem fold_cycle_eigenvector_to_path
    (n : ℕ) (hn2 : 2 ≤ n)
    (x : (ZMod (2 * n)) → ℂ) (lambda : ℂ)
    (h_eigen :
      haveI : NeZero (2 * n) := ⟨by omega⟩
      (Circulant.cycle_laplacian (2 * n) (by omega)).mulVec x = lambda • x)
    (h_boundary_0 : x (-(1 : ZMod (2 * n))) = x (0 : ZMod (2 * n)))
    (h_boundary_n : x ((n : ZMod (2 * n))) = x (((n - 1 : ℕ) : ZMod (2 * n)))) :
    (path_laplacian n).mulVec (fun i : Fin n => x ((i.val : ZMod (2 * n)))) =
      lambda • (fun i : Fin n => x ((i.val : ZMod (2 * n)))) := by
  have hn : 3 ≤ 2 * n := by omega
  haveI : NeZero (2 * n) := ⟨by omega⟩
  set y : Fin n → ℂ := fun i => x ((i.val : ZMod (2 * n))) with hy_def
  -- Pointwise eigenvector equation.
  have h_cycle_at : ∀ m : ZMod (2 * n),
      (Circulant.cycle_laplacian (2 * n) hn).mulVec x m = lambda * x m := by
    intro m
    have := congrFun h_eigen m
    simpa [Pi.smul_apply, smul_eq_mul] using this
  -- Row formula applied componentwise gives the recurrence 2 x m - x (m-1) - x (m+1) = λ x m.
  have h_rec : ∀ m : ZMod (2 * n),
      2 * x m - x (m - 1) - x (m + 1) = lambda * x m := by
    intro m
    rw [← cycle_laplacian_mulVec_apply n hn x m]
    exact h_cycle_at m
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases h0 : i.val = 0
  · -- Left endpoint.
    have hi : i = ⟨0, by omega⟩ := Fin.ext h0
    rw [hi]
    rw [path_laplacian_mulVec_left n hn2 y]
    show y ⟨0, _⟩ - y ⟨1, _⟩ = lambda * y ⟨0, _⟩
    have hrec0 := h_rec (0 : ZMod (2 * n))
    have h0sub1 : (0 : ZMod (2 * n)) - 1 = -1 := by ring
    have h0add1 : (0 : ZMod (2 * n)) + 1 = 1 := by ring
    rw [h0sub1, h0add1, h_boundary_0] at hrec0
    -- hrec0: 2 x(0) - x(0) - x(1) = λ x(0), i.e., x(0) - x(1) = λ x(0).
    have hy0 : y ⟨0, by omega⟩ = x (0 : ZMod (2 * n)) := by simp [y]
    have hy1 : y ⟨1, by omega⟩ = x (1 : ZMod (2 * n)) := by
      simp [y]
    rw [hy0, hy1]
    linear_combination hrec0
  · by_cases h1 : i.val + 1 = n
    · -- Right endpoint.
      have hi : i = ⟨n - 1, by omega⟩ := by
        apply Fin.ext
        show i.val = n - 1
        omega
      rw [hi]
      rw [path_laplacian_mulVec_right n hn2 y]
      show y ⟨n - 1, _⟩ - y ⟨n - 2, _⟩ = lambda * y ⟨n - 1, _⟩
      -- Apply the recurrence at ((n - 1 : ℕ) : ZMod (2n)).
      have hrec := h_rec ((n - 1 : ℕ) : ZMod (2 * n))
      -- Identify neighbours.
      have hp1 : ((n - 1 : ℕ) : ZMod (2 * n)) + 1 = ((n : ℕ) : ZMod (2 * n)) := by
        have hkey : (n - 1) + 1 = n := Nat.sub_add_cancel (show 1 ≤ n by omega)
        have : (((n - 1) + 1 : ℕ) : ZMod (2 * n)) = ((n : ℕ) : ZMod (2 * n)) := by
          rw [hkey]
        push_cast at this
        exact this
      have hm1 : ((n - 1 : ℕ) : ZMod (2 * n)) - 1 = ((n - 2 : ℕ) : ZMod (2 * n)) := by
        have hkey : (n - 2) + 1 = n - 1 := by omega
        have h : (((n - 2) + 1 : ℕ) : ZMod (2 * n)) = ((n - 1 : ℕ) : ZMod (2 * n)) := by
          rw [hkey]
        push_cast at h
        linear_combination -h
      rw [hp1, hm1, h_boundary_n] at hrec
      -- hrec: 2 x(n-1) - x(n-2) - x(n-1) = λ x(n-1), i.e., x(n-1) - x(n-2) = λ x(n-1).
      have hy_nm1 : y ⟨n - 1, by omega⟩ = x ((n - 1 : ℕ) : ZMod (2 * n)) := by simp [y]
      have hy_nm2 : y ⟨n - 2, by omega⟩ = x ((n - 2 : ℕ) : ZMod (2 * n)) := by simp [y]
      rw [hy_nm1, hy_nm2]
      linear_combination hrec
    · -- Interior vertex.
      have hlo : 1 ≤ i.val := by omega
      have hhi : i.val + 2 ≤ n := by omega
      rw [path_laplacian_mulVec_interior n y i hlo hhi]
      show 2 * y i - y ⟨i.val - 1, _⟩ - y ⟨i.val + 1, _⟩ = lambda * y i
      have hrec := h_rec ((i.val : ℕ) : ZMod (2 * n))
      have hp1 : ((i.val : ℕ) : ZMod (2 * n)) + 1 = (((i.val + 1) : ℕ) : ZMod (2 * n)) := by
        push_cast; ring
      have hm1 : ((i.val : ℕ) : ZMod (2 * n)) - 1 = (((i.val - 1) : ℕ) : ZMod (2 * n)) := by
        have hkey : (i.val - 1) + 1 = i.val := Nat.sub_add_cancel hlo
        have h : (((i.val - 1) + 1 : ℕ) : ZMod (2 * n)) = ((i.val : ℕ) : ZMod (2 * n)) := by
          rw [hkey]
        push_cast at h
        linear_combination -h
      rw [hp1, hm1] at hrec
      have hy_i : y i = x ((i.val : ℕ) : ZMod (2 * n)) := by simp [y]
      have hy_im1 : y ⟨i.val - 1, by omega⟩ = x (((i.val - 1) : ℕ) : ZMod (2 * n)) := by simp [y]
      have hy_ip1 : y ⟨i.val + 1, by omega⟩ = x (((i.val + 1) : ℕ) : ZMod (2 * n)) := by simp [y]
      rw [hy_i, hy_im1, hy_ip1]
      linear_combination hrec

end EnsX2026.Matrices.PathGraph

end
