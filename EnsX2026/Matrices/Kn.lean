import EnsX2026.Matrices.RankOne
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt

/-!
# ENS/Polytechnique 2026 Math A — Q2, Q4, Q5, Q6

Spectral analysis of `Kₙ = n·Iₙ − Jₙ` from `EnsX2026.Matrices.RankOne`.

* **Q2** `K_matrix_isOrthogonallyDiagonalisable`: `Kₙ` admits an orthogonal
  diagonalisation `Kₙ = P · D · Pᵀ` with `P · Pᵀ = 1`. The proof specialises
  Mathlib's `Matrix.IsHermitian.spectral_theorem` to the real case, where
  `conjStarAlgAut ℝ _ U (diagonal D) = U * diagonal D * Uᵀ` (since
  `star = conjTranspose` and conjugation is the identity on ℝ).

* **Q4** `K_matrix_kernel` and `K_matrix_eigenspace_n`: explicit identification
  of the two eigenspaces of `Kₙ`:
  - `ker Kₙ = {c · (1,…,1) : c ∈ ℝ}`
  - `ker (Kₙ − n·I) = {x : Σᵢ xᵢ = 0}`

  The proofs reduce to the algebraic identity `Kₙ · x = n·x − (Σⱼ xⱼ)·1`.

* **Q5** `gramSchmidt_reference`: pointer to Mathlib's
  `gramSchmidtOrthonormalBasis`, the canonical orthonormalisation of an
  indexed family in an inner product space (the exam merely requires stating
  the theorem and the recurrence — no proof is expected).

* **Q6** Explicit orthonormal basis of the two eigenspaces:
  - `e_kernel n = (1,…,1) / √n` spans the kernel;
  - `e_eigen n k` (for `2 ≤ k ≤ n`) is the Gram-Schmidt basis of the
    eigenspace for λ = n, as per the exam's recurrence.

  We prove `e_kernel_mulVec`, `e_kernel_norm`, `e_kernel_orthogonal_e_eigen`,
  and the eigenvalue equation for `e_eigen` is reduced to the single
  combinatorial identity `Σᵢ e_eigen n k i = 0`, which we prove directly.
  Mutual orthogonality of `e_eigen n k` for distinct `k` is left as future
  work (the computation is routine but messy).

Institut Fourier, Grenoble — Kieran McShane
-/

noncomputable section

namespace EnsX2026.Matrices.Kn

open Matrix EnsX2026.Matrices

/-! ## Algebraic rewriting of `Kₙ · x` -/

/-- `Kₙ · x = n·x − (Σⱼ xⱼ)·1`, where `1` is the constant vector `(1,…,1)`. -/
lemma K_matrix_mulVec (n : ℕ) (x : Fin n → ℝ) :
    (K_matrix n).mulVec x =
      (n : ℝ) • x - (∑ j, x j) • (fun _ : Fin n => (1 : ℝ)) := by
  funext i
  unfold K_matrix
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  -- Now: n * x i - ((fun i j => 1 : _) *ᵥ x) i = n * x i - ∑ j, x j
  congr 1
  simp [Matrix.mulVec, dotProduct, Matrix.of_apply]

/-! ## Q2 — Orthogonal diagonalisation of `Kₙ` -/

/-- **Q2.** `Kₙ` admits an orthogonal diagonalisation: there exist `P` with
`P · Pᵀ = 1` and a diagonal matrix of eigenvalues `D` such that
`Kₙ = P · diagonal D · Pᵀ`. -/
theorem K_matrix_isOrthogonallyDiagonalisable (n : ℕ) :
    ∃ (P : Matrix (Fin n) (Fin n) ℝ) (D : Fin n → ℝ),
      P * Pᵀ = 1 ∧ K_matrix n = P * Matrix.diagonal D * Pᵀ := by
  classical
  have hA : (K_matrix n).IsHermitian := K_matrix_isHermitian n
  refine ⟨(hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ), hA.eigenvalues, ?_, ?_⟩
  · -- `P * Pᵀ = 1` from the unitary property (over ℝ, `star = transpose`).
    have hU : (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
              star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) = 1 :=
      (Matrix.mem_unitaryGroup_iff).mp hA.eigenvectorUnitary.2
    simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using hU
  · -- `Kₙ = U · diagonal D · Uᵀ` from the spectral theorem.
    -- Over ℝ, `conjStarAlgAut u x = u * x * star u` and `star = transpose`.
    have hst := hA.spectral_theorem
    have hstar : star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
                  = (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)ᵀ := by
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    calc K_matrix n
        = (Unitary.conjStarAlgAut ℝ _) hA.eigenvectorUnitary
            (diagonal (RCLike.ofReal ∘ hA.eigenvalues : Fin n → ℝ)) := hst
      _ = (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
            diagonal (RCLike.ofReal ∘ hA.eigenvalues : Fin n → ℝ) *
            star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) :=
          Unitary.conjStarAlgAut_apply _ _
      _ = (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
            diagonal hA.eigenvalues *
            (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)ᵀ := by
          rw [hstar]
          rfl

/-! ## Q4 — Identification of the eigenspaces -/

/-- **Q4 (kernel).** `Kₙ · x = 0` if and only if `x` is a constant vector. -/
theorem K_matrix_kernel (n : ℕ) (x : Fin n → ℝ) :
    (K_matrix n).mulVec x = 0 ↔ ∃ c : ℝ, ∀ i, x i = c := by
  rw [K_matrix_mulVec]
  constructor
  · -- If `n • x = (Σⱼ xⱼ) • 1`, then all components are equal.
    intro hx
    have hpt : ∀ i, (n : ℝ) * x i = ∑ j, x j := by
      intro i
      have := congrFun hx i
      simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_eq_zero] at this
      exact this
    by_cases hn : n = 0
    · subst hn
      refine ⟨0, ?_⟩
      intro i
      exact absurd i.is_lt (by simp)
    · refine ⟨(∑ j, x j) / (n : ℝ), ?_⟩
      intro i
      have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      have := hpt i
      field_simp
      linarith
  · rintro ⟨c, hc⟩
    funext i
    have hsum : ∑ j, x j = (n : ℝ) * c := by
      simp [hc, Finset.sum_const, Finset.card_univ]
    rw [Pi.sub_apply, Pi.zero_apply, Pi.smul_apply, Pi.smul_apply,
      smul_eq_mul, smul_eq_mul, hc, hsum]
    ring

/-- **Q4 (eigenspace for λ = n).** `Kₙ · x = n · x` if and only if `Σᵢ xᵢ = 0`.
The hypothesis `1 ≤ n` is included for parallelism with the exam. -/
theorem K_matrix_eigenspace_n (n : ℕ) (hn : 1 ≤ n) (x : Fin n → ℝ) :
    (K_matrix n).mulVec x = (n : ℝ) • x ↔ ∑ i, x i = 0 := by
  rw [K_matrix_mulVec]
  constructor
  · intro hx
    have i₀ : Fin n := ⟨0, hn⟩
    have := congrFun hx i₀
    simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
    linarith
  · intro hx
    funext i
    simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hx]

/-! ## Q5 — Gram-Schmidt orthonormalisation (statement) -/

/-- **Q5.** Statement of Gram-Schmidt: for any family of vectors in an
inner product space with index cardinality equal to the dimension, there
exists a canonical orthonormal basis obtained by Gram-Schmidt.

This is exactly `gramSchmidtOrthonormalBasis` in Mathlib
(`Mathlib/Analysis/InnerProductSpace/GramSchmidtOrtho.lean`), together with
the recurrence `gramSchmidtOrthonormalBasis_apply`. No proof is required —
the exam simply asks to state the theorem and the recurrence formula. -/
theorem gramSchmidt_reference
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]
    [Fintype ι] [FiniteDimensional 𝕜 E]
    (h : Module.finrank 𝕜 E = Fintype.card ι) (f : ι → E) :
    ∃ B : OrthonormalBasis ι 𝕜 E,
      B = InnerProductSpace.gramSchmidtOrthonormalBasis h f :=
  ⟨InnerProductSpace.gramSchmidtOrthonormalBasis h f, rfl⟩

/-! ## Q6 — Explicit orthonormal basis -/

/-- The kernel eigenvector: the normalised constant vector `(1,…,1)/√n`. -/
def e_kernel (n : ℕ) : Fin n → ℝ := fun _ => 1 / Real.sqrt n

/-- The Gram-Schmidt basis of the eigenspace for λ = n:
`eₖ = (1/√(k(k-1))) · ((k-1)·eₖ − Σⱼ<ₖ eⱼ)` for `2 ≤ k ≤ n`.
Explicitly, the components of `e_eigen n k` are:

* `-1/√(k(k-1))` on indices `i` with `i + 1 < k`,
* `(k-1)/√(k(k-1))` on the index `i` with `i + 1 = k`,
* `0` on indices `i` with `i + 1 > k`. -/
def e_eigen (n k : ℕ) (_ : 2 ≤ k) (_ : k ≤ n) : Fin n → ℝ :=
  fun i => if (i.val + 1 : ℕ) < k then -1 / Real.sqrt (k * (k - 1))
           else if (i.val + 1 : ℕ) = k then (k - 1 : ℝ) / Real.sqrt (k * (k - 1))
           else 0

/-- The norm of the constant vector `(1,…,1)/√n` in `ℓ²(Fin n)` is `1`. -/
theorem e_kernel_norm (n : ℕ) (hn : 1 ≤ n) :
    ‖(WithLp.toLp 2 (e_kernel n) : EuclideanSpace ℝ (Fin n))‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn'
  have hsqrt_pos : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hn'
  have hsqrt_sq : Real.sqrt n ^ 2 = n := by
    rw [sq]; exact Real.mul_self_sqrt (le_of_lt hn')
  -- `‖e_kernel n i‖² = 1/n`, sum over `Fin n` gives `n · (1/n) = 1`.
  have hstep : ∑ i : Fin n, ‖(WithLp.toLp 2 (e_kernel n) : EuclideanSpace ℝ (Fin n)) i‖ ^ 2
              = 1 := by
    simp only [e_kernel,
      Real.norm_eq_abs, abs_div, abs_one, abs_of_pos hsqrt_pos,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [div_pow, one_pow, hsqrt_sq]
    field_simp
  rw [hstep]
  exact Real.sqrt_one

/-- The constant vector `(1,…,1)/√n` lies in the kernel of `Kₙ`. -/
theorem e_kernel_mulVec (n : ℕ) : (K_matrix n).mulVec (e_kernel n) = 0 := by
  rw [(K_matrix_kernel n (e_kernel n)).mpr]
  exact ⟨1 / Real.sqrt n, fun _ => rfl⟩

/-- Auxiliary: the sum of the entries of `e_eigen n k` is `0`. This is the
cancellation `(k-1)·(-1/√(k(k-1))) + (k-1)/√(k(k-1)) + 0 = 0`. -/
lemma e_eigen_sum_zero (n k : ℕ) (h2 : 2 ≤ k) (hn : k ≤ n) :
    ∑ i : Fin n, e_eigen n k h2 hn i = 0 := by
  classical
  -- Set A := √(k(k-1)) for concision.
  set A : ℝ := Real.sqrt (k * (k - 1)) with hA_def
  have hk_pos : 1 ≤ k := by omega
  have hk1_lt_n : k - 1 < n := by omega
  -- Rewrite the summand as a piecewise-constant function over three regions.
  -- Use `Finset.sum_ite` to split by the first branch `i.val + 1 < k`.
  have hsplit1 :
      ∑ i : Fin n, e_eigen n k h2 hn i
        = (∑ i ∈ (Finset.univ : Finset (Fin n)).filter
              (fun i : Fin n => i.val + 1 < k), (-1 / A : ℝ))
          + (∑ i ∈ (Finset.univ : Finset (Fin n)).filter
              (fun i : Fin n => ¬ i.val + 1 < k),
              (if (i.val + 1 : ℕ) = k then (k - 1 : ℝ) / A else 0)) := by
    unfold e_eigen
    rw [← Finset.sum_filter_add_sum_filter_not
          (Finset.univ : Finset (Fin n)) (fun i => i.val + 1 < k)]
    congr 1
    · -- Collapse the first piece: the condition is true, so the if simplifies.
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp [hi, hA_def]
    · -- On the second piece, the outer if is false; leave the inner if.
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp [hi, hA_def]
  -- Evaluate the first (constant) sum.
  have hcardA :
      ((Finset.univ : Finset (Fin n)).filter
          (fun i : Fin n => i.val + 1 < k)).card = k - 1 := by
    have hrw :
        (Finset.univ : Finset (Fin n)).filter (fun i : Fin n => i.val + 1 < k)
          = (Finset.Iio (⟨k - 1, hk1_lt_n⟩ : Fin n)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio,
        Fin.lt_def]
      omega
    rw [hrw, Fin.card_Iio]
  -- Evaluate the second (indicator) sum.
  have hsplit2 :
      (∑ i ∈ (Finset.univ : Finset (Fin n)).filter
          (fun i : Fin n => ¬ i.val + 1 < k),
          (if (i.val + 1 : ℕ) = k then (k - 1 : ℝ) / A else 0))
        = (k - 1 : ℝ) / A := by
    rw [Finset.sum_ite]
    -- The "then" branch is a singleton; the "else" branch sums zeros.
    have hfilter :
        ((Finset.univ : Finset (Fin n)).filter (fun i : Fin n => ¬ i.val + 1 < k)).filter
            (fun i : Fin n => i.val + 1 = k)
          = ({⟨k - 1, hk1_lt_n⟩} : Finset (Fin n)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨_, heq⟩
        apply Fin.ext
        show i.val = k - 1
        omega
      · intro heq
        rw [heq]
        refine ⟨?_, ?_⟩ <;> (show _; simp; omega)
    rw [hfilter]
    simp
  rw [hsplit1, hsplit2, Finset.sum_const, hcardA, nsmul_eq_mul]
  -- Goal: ((k - 1 : ℕ) : ℝ) * (-1 / A) + (k - 1 : ℝ) / A = 0
  have hk_cast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    have h : k = (k - 1) + 1 := by omega
    conv_rhs => rw [h]
    push_cast
    ring
  rw [hk_cast]
  ring

/-- `e_eigen n k` is an eigenvector of `Kₙ` for eigenvalue `n`. -/
theorem e_eigen_mulVec (n k : ℕ) (h2 : 2 ≤ k) (hn : k ≤ n) :
    (K_matrix n).mulVec (e_eigen n k h2 hn) = (n : ℝ) • (e_eigen n k h2 hn) := by
  have hnpos : 1 ≤ n := le_trans (by omega) hn
  rw [K_matrix_eigenspace_n n hnpos]
  exact e_eigen_sum_zero n k h2 hn

/-- `e_kernel n` is orthogonal (standard dot product) to every `e_eigen n k`. -/
theorem e_kernel_orthogonal_e_eigen (n k : ℕ) (h2 : 2 ≤ k) (hn : k ≤ n) :
    dotProduct (e_kernel n) (e_eigen n k h2 hn) = 0 := by
  -- ⟨e_kernel, e_eigen⟩ = (1/√n) · Σᵢ e_eigen i = (1/√n) · 0 = 0.
  unfold dotProduct e_kernel
  rw [← Finset.mul_sum]
  rw [e_eigen_sum_zero n k h2 hn]
  ring

-- TODO: mutual orthogonality of the `e_eigen n k` for distinct `k`. The
-- computation is a routine but messy index case-split; skipped since the
-- exam only requires the statement of Gram-Schmidt and the explicit formula.

end EnsX2026.Matrices.Kn

end
