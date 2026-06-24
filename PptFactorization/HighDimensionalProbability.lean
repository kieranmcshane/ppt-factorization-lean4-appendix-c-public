import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Moments.SubGaussian
import PptFactorization.AppendixB

open MeasureTheory Matrix ProbabilityTheory
open scoped BigOperators Matrix.Norms.L2Operator NNReal

noncomputable section

namespace HighDimensionalProbability

section OperatorNormNet

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Nontrivial E]
  [CompleteSpace E]

/-- Supremum of the absolute quadratic form over a subset of the unit sphere. -/
noncomputable def netQuadraticSup
    (T : E →L[𝕜] E) (N : Set (Metric.sphere (0 : E) 1)) : ℝ :=
  sSup ((fun u : Metric.sphere (0 : E) 1 => |T.reApplyInnerSelf (u : E)|) '' N)

omit [Nontrivial E] [CompleteSpace E] in
/-- An upper bound on the quadratic form over a nonempty net bounds
`netQuadraticSup`. -/
theorem netQuadraticSup_le_of_forall_le
    (T : E →L[𝕜] E) {N : Set (Metric.sphere (0 : E) 1)} {B : ℝ}
    (hN_nonempty : N.Nonempty)
    (hbound : ∀ u ∈ N, |T.reApplyInnerSelf (u : E)| ≤ B) :
    netQuadraticSup T N ≤ B := by
  let S :
      Set ℝ :=
    ((fun u : Metric.sphere (0 : E) 1 => |T.reApplyInnerSelf (u : E)|) '' N)
  have hS_nonempty : S.Nonempty := by
    rcases hN_nonempty with ⟨u, huN⟩
    exact ⟨_, ⟨u, huN, rfl⟩⟩
  have hS_le : ∀ x ∈ S, x ≤ B := by
    intro x hx
    rcases hx with ⟨u, huN, rfl⟩
    exact hbound u huN
  dsimp [netQuadraticSup, S]
  exact csSup_le hS_nonempty hS_le

omit [Nontrivial E] [CompleteSpace E] in
/-- Telescoping identity for the quadratic form difference. -/
lemma reApplyInnerSelf_telescope
    (T : E →L[𝕜] E) (x y : E) :
    T.reApplyInnerSelf x - T.reApplyInnerSelf y =
      RCLike.re
        (inner 𝕜 (T (x - y)) x + inner 𝕜 (T y) (x - y)) := by
  rw [ContinuousLinearMap.reApplyInnerSelf_apply,
    ContinuousLinearMap.reApplyInnerSelf_apply]
  simp [map_sub, inner_sub_left, inner_sub_right]

omit [Nontrivial E] [CompleteSpace E] in
/-- On the unit sphere, the quadratic form of a continuous linear map is `2 ‖T‖`-Lipschitz. -/
lemma reApplyInnerSelf_unitSphere_lipschitz
    (T : E →L[𝕜] E)
    (x y : Metric.sphere (0 : E) 1) :
    |T.reApplyInnerSelf (x : E) - T.reApplyInnerSelf (y : E)| ≤
      2 * ‖T‖ * ‖(x : E) - (y : E)‖ := by
  have hx : ‖(x : E)‖ = 1 := by simp
  have hy : ‖(y : E)‖ = 1 := by simp
  have hident := reApplyInnerSelf_telescope (T := T) (x := (x : E)) (y := (y : E))
  have hmul₁ :
      ‖inner 𝕜 (T ((x : E) - (y : E))) (x : E) +
          inner 𝕜 (T (y : E)) ((x : E) - (y : E))‖ ≤
        2 * ‖T‖ * ‖(x : E) - (y : E)‖ := by
    calc
      ‖inner 𝕜 (T ((x : E) - (y : E))) (x : E) +
          inner 𝕜 (T (y : E)) ((x : E) - (y : E))‖ ≤
          ‖inner 𝕜 (T ((x : E) - (y : E))) (x : E)‖ +
            ‖inner 𝕜 (T (y : E)) ((x : E) - (y : E))‖ := norm_add_le _ _
      _ ≤ ‖T ((x : E) - (y : E))‖ * ‖(x : E)‖ +
            ‖T (y : E)‖ * ‖(x : E) - (y : E)‖ := by
          gcongr
          · exact norm_inner_le_norm _ _
          · exact norm_inner_le_norm _ _
      _ ≤ (‖T‖ * ‖(x : E) - (y : E)‖) * ‖(x : E)‖ +
            (‖T‖ * ‖(y : E)‖) * ‖(x : E) - (y : E)‖ := by
          gcongr
          · exact T.le_opNorm ((x : E) - (y : E))
          · exact T.le_opNorm (y : E)
      _ = 2 * ‖T‖ * ‖(x : E) - (y : E)‖ := by
          simp [hx, hy]
          ring_nf
  calc
    |T.reApplyInnerSelf (x : E) - T.reApplyInnerSelf (y : E)| =
        |RCLike.re
          (inner 𝕜 (T ((x : E) - (y : E))) (x : E) +
            inner 𝕜 (T (y : E)) ((x : E) - (y : E)))| := by
          rw [hident]
    _ ≤ ‖inner 𝕜 (T ((x : E) - (y : E))) (x : E) +
          inner 𝕜 (T (y : E)) ((x : E) - (y : E))‖ := by
          exact RCLike.abs_re_le_norm _
    _ ≤ 2 * ‖T‖ * ‖(x : E) - (y : E)‖ := hmul₁

/-- A `(1/4)`-net on the unit sphere controls the operator norm of a self-adjoint operator by
its quadratic form on the net. -/
theorem netToOperatorNormSelfAdjoint
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T)
    {N : Set (Metric.sphere (0 : E) 1)}
    (hnet :
      ∀ x : Metric.sphere (0 : E) 1,
        ∃ u ∈ N, ‖(x : E) - (u : E)‖ ≤ (1 / 4 : ℝ)) :
    ‖T‖ ≤ 2 * netQuadraticSup T N := by
  let S := netQuadraticSup T N
  have hN_nonempty : N.Nonempty := by
    obtain ⟨x₀⟩ :=
      NormedSpace.sphere_nonempty_rclike (𝕜 := 𝕜) (E := E) (r := (1 : ℝ)) zero_le_one
    rcases hnet x₀ with ⟨u, huN, _⟩
    exact ⟨u, huN⟩
  have hBdd :
      BddAbove ((fun u : Metric.sphere (0 : E) 1 => |T.reApplyInnerSelf (u : E)|) '' N) := by
    refine ⟨‖T‖, ?_⟩
    rintro r ⟨u, huN, rfl⟩
    have hu : ‖(u : E)‖ = 1 := by simp
    simpa [ContinuousLinearMap.rayleighQuotient, hu]
      using T.rayleighQuotient_le_norm (u : E)
  have hS_nonneg : 0 ≤ S := by
    rcases hN_nonempty with ⟨u, huN⟩
    exact le_trans (by positivity : 0 ≤ |T.reApplyInnerSelf (u : E)|) (le_csSup hBdd ⟨u, huN, rfl⟩)
  have hbound : ∀ x : E, |T.rayleighQuotient x| ≤ S + ‖T‖ / 2 := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
      nlinarith [hS_nonneg, norm_nonneg T]
    · let x₁ : Metric.sphere (0 : E) 1 :=
        ⟨((‖x‖⁻¹ : 𝕜) • x), by simpa using norm_smul_inv_norm hx⟩
      have hx₁ : ‖(x₁ : E)‖ = 1 := by simp
      have hnorm_ne : ((‖x‖⁻¹ : 𝕜)) ≠ 0 := by
        exact inv_ne_zero (by simpa [norm_eq_zero] using hx)
      have hx_rayleigh : |T.rayleighQuotient x| = |T.reApplyInnerSelf (x₁ : E)| := by
        calc
          |T.rayleighQuotient x| = |T.rayleighQuotient (((‖x‖⁻¹ : 𝕜) • x) : E)| := by
            rw [T.rayleigh_smul x hnorm_ne]
          _ = |T.reApplyInnerSelf (x₁ : E)| := by
            simp [ContinuousLinearMap.rayleighQuotient, hx₁, x₁]
      rcases hnet x₁ with ⟨u, huN, hxu⟩
      have hu_le : |T.reApplyInnerSelf (u : E)| ≤ S := by
        exact le_csSup hBdd ⟨u, huN, rfl⟩
      have hdist :
          |T.reApplyInnerSelf (x₁ : E) - T.reApplyInnerSelf (u : E)| ≤ ‖T‖ / 2 := by
        refine (reApplyInnerSelf_unitSphere_lipschitz T x₁ u).trans ?_
        nlinarith [norm_nonneg T, hxu]
      have hmain : |T.reApplyInnerSelf (x₁ : E)| ≤ S + ‖T‖ / 2 := by
        calc
          |T.reApplyInnerSelf (x₁ : E)| =
              |(T.reApplyInnerSelf (x₁ : E) - T.reApplyInnerSelf (u : E)) +
                T.reApplyInnerSelf (u : E)| := by ring_nf
          _ ≤ |T.reApplyInnerSelf (x₁ : E) - T.reApplyInnerSelf (u : E)| +
                |T.reApplyInnerSelf (u : E)| := abs_add_le _ _
          _ ≤ ‖T‖ / 2 + S := by linarith
          _ = S + ‖T‖ / 2 := by ring
      simpa [hx_rayleigh] using hmain
  have hnorm : ‖T‖ = ⨆ x : E, |T.rayleighQuotient x| :=
    T.norm_eq_iSup_rayleighQuotient hT.isSymmetric
  have hstep : ‖T‖ ≤ S + ‖T‖ / 2 := by
    calc
      ‖T‖ = ⨆ x : E, |T.rayleighQuotient x| := hnorm
      _ ≤ S + ‖T‖ / 2 := ciSup_le hbound
  dsimp [S, netQuadraticSup] at hstep ⊢
  nlinarith [norm_nonneg T]

end OperatorNormNet

section MatrixForms

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Real quadratic form associated to a complex matrix, viewed as an operator on Euclidean space. -/
noncomputable def quadraticForm (H : Matrix n n ℂ) (x : EuclideanSpace ℂ n) : ℝ :=
  (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) H).reApplyInnerSelf x

/-- Centered sum of quadratic-form samples. -/
noncomputable def centeredQuadraticFormSum
    {Ω : Type*} [MeasurableSpace Ω] {s : ℕ}
    (g : Fin s → Ω → EuclideanSpace ℂ n) (H : Matrix n n ℂ) : Ω → ℝ :=
  fun ω => ∑ α, (quadraticForm H (g α ω) - RCLike.re H.trace)

/-- A sorry-free Bernstein-style two-sided tail bound for sums of centered quadratic-form
observables, assuming the centered summands are independent and sub-Gaussian.

This is the current axiom-free interface available from the local project and Mathlib; the
Gaussian-specific analytic input is packaged into the assumptions `hIndep` and `hSubG`. -/
theorem gaussianQuadraticFormBernstein
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {s : ℕ} (g : Fin s → Ω → EuclideanSpace ℂ n) (H : Matrix n n ℂ)
    {v : ℝ≥0} (hv : 0 < (v : ℝ))
    (hIndep :
      iIndepFun
        (fun α : Fin s => fun ω =>
          quadraticForm H (g α ω) - RCLike.re H.trace) μ)
    (hSubG :
      ∀ α : Fin s,
        HasSubgaussianMGF
          (fun ω => quadraticForm H (g α ω) - RCLike.re H.trace) v μ)
    {t : ℝ} (ht : 0 ≤ t) :
    ∃ c > 0,
      μ.real {ω | t * s ≤ |centeredQuadraticFormSum g H ω|} ≤
        2 * Real.exp (-(c * s * min (t ^ 2) t)) := by
  by_cases hs : s = 0
  · refine ⟨1 / (2 * (v : ℝ)), by positivity, ?_⟩
    simp [centeredQuadraticFormSum, hs]
  · have hs_pos : 0 < (s : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hs)
    have hPos :
        μ.real {ω | t * s ≤ centeredQuadraticFormSum g H ω} ≤
          Real.exp (-(t * s) ^ 2 / (2 * ((s : ℝ≥0) * v))) := by
      simpa [centeredQuadraticFormSum]
        using HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
          (μ := μ)
          (X := fun α : Fin s => fun ω =>
            quadraticForm H (g α ω) - RCLike.re H.trace)
          (c := fun _ : Fin s => v)
          (s := Finset.univ)
          hIndep
          (by intro α hα; simpa using hSubG α)
          (by positivity : 0 ≤ t * s)
    have hIndepNeg :
        iIndepFun
          (fun α : Fin s => fun ω =>
            -(quadraticForm H (g α ω) - RCLike.re H.trace)) μ := by
      have hEq :
          (fun α : Fin s => fun ω => -(quadraticForm H (g α ω) - RCLike.re H.trace)) =
            fun α : Fin s => (fun x : ℝ => -x) ∘
              (fun ω => quadraticForm H (g α ω) - RCLike.re H.trace) := by
        funext α ω
        rfl
      rw [hEq]
      exact hIndep.comp (fun _ => fun x : ℝ => -x) (fun _ => measurable_neg)
    have hSubGNeg :
        ∀ α : Fin s,
          HasSubgaussianMGF
            (fun ω => -(quadraticForm H (g α ω) - RCLike.re H.trace)) v μ := by
      intro α
      exact (hSubG α).neg
    have hNeg :
        μ.real {ω | t * s ≤ -centeredQuadraticFormSum g H ω} ≤
          Real.exp (-(t * s) ^ 2 / (2 * ((s : ℝ≥0) * v))) := by
      simpa [centeredQuadraticFormSum, Finset.sum_neg_distrib]
        using HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
          (μ := μ)
          (X := fun α : Fin s => fun ω =>
            -(quadraticForm H (g α ω) - RCLike.re H.trace))
          (c := fun _ : Fin s => v)
          (s := Finset.univ)
          hIndepNeg
          (by intro α hα; simpa using hSubGNeg α)
          (by positivity : 0 ≤ t * s)
    have hExpEq :
        (-(t * s) ^ 2 / (2 * ((s : ℝ≥0) * v)) : ℝ) =
          -(s * t ^ 2 / (2 * (v : ℝ))) := by
      have hs_ne : (s : ℝ) ≠ 0 := by exact_mod_cast hs
      have hv_ne : (v : ℝ) ≠ 0 := ne_of_gt hv
      change -(t * (s : ℝ)) ^ 2 / (2 * ((s : ℝ) * (v : ℝ))) = -(s * t ^ 2 / (2 * (v : ℝ)))
      field_simp [hs_ne, hv_ne]
    have hMinExp :
        Real.exp (-(s * t ^ 2 / (2 * (v : ℝ)))) ≤
          Real.exp (-((1 / (2 * (v : ℝ))) * s * min (t ^ 2) t)) := by
      apply Real.exp_le_exp.mpr
      have hmin : min (t ^ 2) t ≤ t ^ 2 := min_le_left _ _
      have hcoeff_nonneg : 0 ≤ (1 / (2 * (v : ℝ))) * s := by
        positivity
      have hscaled :
          (1 / (2 * (v : ℝ))) * s * min (t ^ 2) t ≤
            (1 / (2 * (v : ℝ))) * s * (t ^ 2) :=
        mul_le_mul_of_nonneg_left hmin hcoeff_nonneg
      have hrhs :
          (1 / (2 * (v : ℝ))) * s * (t ^ 2) =
            s * t ^ 2 / (2 * (v : ℝ)) := by
        field_simp [ne_of_gt hv]
      linarith
    have hExpLe :
        Real.exp (-(t * s) ^ 2 / (2 * ((s : ℝ≥0) * v))) ≤
          Real.exp (-((1 / (2 * (v : ℝ))) * s * min (t ^ 2) t)) := by
      rw [hExpEq]
      exact hMinExp
    have hAbsSubset :
        {ω | t * s ≤ |centeredQuadraticFormSum g H ω|} ⊆
          {ω | t * s ≤ centeredQuadraticFormSum g H ω} ∪
            {ω | t * s ≤ -centeredQuadraticFormSum g H ω} := by
      intro ω hω
      by_cases hsum : 0 ≤ centeredQuadraticFormSum g H ω
      · left
        simpa [abs_of_nonneg hsum] using hω
      · right
        simpa [abs_of_neg (lt_of_not_ge hsum)] using hω
    refine ⟨1 / (2 * (v : ℝ)), by positivity, ?_⟩
    calc
      μ.real {ω | t * s ≤ |centeredQuadraticFormSum g H ω|} ≤
          μ.real
            ({ω | t * s ≤ centeredQuadraticFormSum g H ω} ∪
              {ω | t * s ≤ -centeredQuadraticFormSum g H ω}) := by
            exact measureReal_mono (h₂ := (measure_lt_top μ _).ne) hAbsSubset
      _ ≤ μ.real {ω | t * s ≤ centeredQuadraticFormSum g H ω} +
            μ.real {ω | t * s ≤ -centeredQuadraticFormSum g H ω} := by
            exact measureReal_union_le _ _
      _ ≤ Real.exp (-(t * s) ^ 2 / (2 * ((s : ℝ≥0) * v))) +
            Real.exp (-(t * s) ^ 2 / (2 * ((s : ℝ≥0) * v))) := by
            gcongr
      _ = 2 * Real.exp (-(t * s) ^ 2 / (2 * ((s : ℝ≥0) * v))) := by ring
      _ ≤ 2 * Real.exp (-((1 / (2 * (v : ℝ))) * s * min (t ^ 2) t)) := by
            exact mul_le_mul_of_nonneg_left hExpLe (by positivity)

/-- Hermitian matrix version of the net-to-operator norm reduction.

The matrix norm is the Euclidean `L²` operator norm from the scoped matrix norm structure. -/
theorem netToOperatorNorm
    [Nonempty n]
    {A : Matrix n n ℂ}
    {N : Set (Metric.sphere (0 : EuclideanSpace ℂ n) 1)}
    (hA : A.IsHermitian)
    (hnet :
      ∀ x : Metric.sphere (0 : EuclideanSpace ℂ n) 1,
        ∃ u ∈ N, ‖(x : EuclideanSpace ℂ n) - (u : EuclideanSpace ℂ n)‖ ≤ (1 / 4 : ℝ)) :
    ‖A‖ ≤ 2 * sSup ((fun u : Metric.sphere (0 : EuclideanSpace ℂ n) 1 => |quadraticForm A u|) '' N) := by
  have hSelfAdjoint : IsSelfAdjoint (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A) := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff', ← ContinuousLinearMap.star_eq_adjoint]
    calc
      star (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A) =
          Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) Aᴴ := by
            symm
            simpa using map_star (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) A
      _ = Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A := by
            simpa using congrArg (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) hA.eq
  simpa [quadraticForm, netQuadraticSup]
    using netToOperatorNormSelfAdjoint
      (T := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A) hSelfAdjoint hnet

end MatrixForms

/-- Mean-centered concentration follows immediately from the corresponding median-centered
Lévy input once the integrated tail bound needed to compare mean and median is available. -/
theorem levyConcentration
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {μ : Measure (Metric.sphere (0 : E) 1)} [IsProbabilityMeasure μ]
    {F : Metric.sphere (0 : E) 1 → ℝ}
    {mean median range n t L C c : ℝ}
    (hmean : mean = ∫ x, F x ∂μ)
    (hF : Integrable F μ)
    (hRange : (fun x => |F x - median|) ≤ᵐ[μ] fun _ => range)
    (hTailIntegral :
      ∫ u in Set.Ioc 0 range, μ.real {x | u ≤ |F x - median|} ≤ t / 2)
    (hMedianTail :
      μ.real {x | t / 2 ≤ |F x - median|} ≤
        C * Real.exp (-(c * n * t ^ 2 / L ^ 2))) :
    μ.real {x | t ≤ |F x - mean|} ≤
      C * Real.exp (-(c * n * t ^ 2 / L ^ 2)) := by
  exact
    (AppendixB.mean_tail_probability_le_median_tail_probability_from_integrated_tail
      (μ := μ) (f := F) (mean := mean) (median := median)
      (scale := t) (range := range) hmean hF hRange hTailIntegral).trans hMedianTail

end HighDimensionalProbability
