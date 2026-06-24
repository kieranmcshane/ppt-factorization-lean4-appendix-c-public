import PptFactorization.AppendixBPipelineGraduate

/-!
# Tight Aubrun fiber-package endpoint

This file keeps the final `U-AUB-02` closure shape explicit: once one has a
`TightAubrunInnovationFiberPackage m Δ` for every tight-range defect slice
`Δ ≤ 2m`, the already-wired exact-square Aubrun pipeline can consume it without
unpacking the package fields by hand at the public frontier.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal

noncomputable section

namespace PptFactorization
namespace AppendixB

open RandomMatrixModel GaussianModel HighProbabilityBounds
open TraceWickExpansion
open TraceWickExpansion.AubrunSurvivingCounting

/-- Exact-square public endpoint fed by a tight-range family of packaged Aubrun
innovation-fiber data.

This is the ledger-aligned closure shape.  The remaining theorem-strength input
is exactly the construction of
`TightAubrunInnovationFiberPackage m Δ` for every `m` and every `Δ≤2m`; all
exact-square scalar/window side conditions are supplied internally. -/
theorem eventually_gammaExpectation_pipeline_to_spherical_bound_of_prop73_tightFiberPackages_exactSquare_Qone
    (pkg : ∀ᶠ d : ℕ in Filter.atTop,
      Nonempty (∀ Δ ∈
        Finset.range (2 * (aubrunEvenMomentParameter d - 1) + 1),
        TightAubrunInnovationFiberPackage
          (aubrunEvenMomentParameter d - 1) Δ)) :
    ∀ᶠ d : ℕ in Filter.atTop,
      gaussianWishartGammaOffDiagonalOpNormMean
          (p := Fin d) (q := Fin d) (σ := Fin (d * d)) ≤
        aubrunOffDiagonalExpectationEnvelope
          (aubrunProposition71Q 1) (d : ℝ) (d * d : ℝ)
          (aubrunEvenMomentParameter d) ∧
      gaussianWishartGammaOpNormMean
          (p := Fin d) (q := Fin d) (σ := Fin (d * d)) ≤
          (2 * Real.log 2 + 4 / (1 : ℝ)) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (d : ℝ) (d * d : ℝ)
              (aubrunEvenMomentParameter d) ∧
      gaussianQuadraticGammaLiftMean
          (p := Fin d) (q := Fin d) (σ := Fin (d * d)) ≤
        gaussianQuadraticRadialMean
          (p := Fin d) (q := Fin d) (σ := Fin (d * d)) *
          (((2 * Real.log 2 + 4 / (1 : ℝ)) +
              aubrunOffDiagonalExpectationEnvelope
                (aubrunProposition71Q 1) (d : ℝ) (d * d : ℝ)
                (aubrunEvenMomentParameter d)) / (d : ℝ) ^ 2) ∧
      sphericalGammaOpNormMean
          (p := Fin d) (q := Fin d) (σ := Fin (d * d)) ≤
        ((2 * Real.log 2 + 4 / (1 : ℝ)) +
            aubrunOffDiagonalExpectationEnvelope
              (aubrunProposition71Q 1) (d : ℝ) (d * d : ℝ)
              (aubrunEvenMomentParameter d)) / (d : ℝ) ^ 2 := by
  have hP := eventually_aubrunProposition73P_evenMoment_le_natCast
  have hdpos : ∀ᶠ d : ℕ in Filter.atTop, 0 < (d : ℝ) := by
    rw [Filter.eventually_atTop]
    exact ⟨1, fun d hd => by exact_mod_cast hd⟩
  filter_upwards [eventually_exactSquare_closeWindow_Qone, hP, hdpos,
    eventually_exactSquare_sample_pos, eventually_exactSquare_ratioModel_one,
    pkg] with
    d hclose_d hP_d hd_d hs_d hRatio_d pkg_d
  simpa [Nat.cast_mul] using
    gammaExpectation_pipeline_to_spherical_bound_of_graduate_relation_counting_canonical_explicitQ
      (dNat := d) (sNat := d * d) (C0 := 1) (lam := (1 : ℝ))
      hd_d hs_d (by norm_num) hRatio_d (by norm_num)
      (aubrunGraduateRelationCounting_of_prop73TightFiberPackagesAndCayleyRankBudget_closeWindow_Qone
        (d := (d : ℝ)) (s := (((d * d : ℕ) : ℝ)))
        (m := aubrunEvenMomentParameter d - 1)
        hd_d.le (Real.sqrt_nonneg _) hd_d hclose_d hP_d
        (Classical.choice pkg_d))

/-- The package route cannot be closed by a uniform old-envelope package if the
Motzkin-sized `m = 7` zero-defect count is confirmed.

This is the ledger-aligned guardrail: a family of
`TightAubrunInnovationFiberPackage m Δ` over every tight-range defect slice
would imply the old fixed-defect envelope for `Δ = 0`, which is exactly the
uniform zero-defect bound already ruled out conditionally by the `m = 7`
formula count. -/
theorem not_forall_tightFiberPackage_of_formula_seven_eq_323
    (h7 : Fintype.card (WickCyclePairTightClassFormula 7) = 323) :
    ¬ (∀ m : ℕ, ∀ Δ ∈ Finset.range (2 * m + 1),
      Nonempty (TightAubrunInnovationFiberPackage m Δ)) := by
  intro hpkg
  exact
    not_forall_wickPermutationDefectCount_zero_le_fixedEnvelope_of_formula_seven_eq_323
      h7
      (fun m =>
        wickPermutationDefectCount_real_le_fixedEnvelope_of_tightFiberPackage
          (Classical.choice (hpkg m 0 (by simp))))

end AppendixB
end PptFactorization
