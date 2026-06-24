import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Basic

/-!
# Reusable probability tools

Small zero-sorry probability helpers adapted from the local
`formal-conjectures` Erdős 524 project.  The source project uses a different
Lean toolchain, so we keep the reusable facts local instead of importing that
project as a dependency.
-/

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

noncomputable section

namespace PptFactorization
namespace ProbabilityTools

variable (n : Type*) [Fintype n]

/-- Standard multivariate Gaussian on `n → ℝ`: the product of independent
`N(0,1)` factors. -/
def standardMVGaussian : Measure (n → ℝ) :=
  Measure.pi (fun _ : n => gaussianReal 0 1)

instance instIsProbabilityMeasureStandardMVGaussian :
    IsProbabilityMeasure (standardMVGaussian n) := by
  unfold standardMVGaussian
  infer_instance

/-- Coordinate functions of the product standard multivariate Gaussian are
jointly independent. -/
theorem standardMVGaussian_iIndepFun_eval :
    iIndepFun (fun (i : n) (ω : n → ℝ) => ω i)
      (standardMVGaussian n) := by
  unfold standardMVGaussian
  exact iIndepFun_pi (μ := fun _ : n => gaussianReal 0 1)
    (X := fun _ => (id : ℝ → ℝ)) (fun _ => measurable_id.aemeasurable)

/-- Centred real Gaussian with variance `v` is sub-Gaussian with parameter
`v` for the identity test function. -/
theorem hasSubgaussianMGF_id_gaussianReal (v : ℝ≥0) :
    HasSubgaussianMGF (id : ℝ → ℝ) v (gaussianReal 0 v) where
  integrable_exp_mul t := integrable_exp_mul_gaussianReal t
  mgf_le t := by
    rw [mgf_id_gaussianReal]
    simp

/-- Two-sided Chernoff tail for a centred real Gaussian. -/
lemma gaussianReal_real_abs_ge_le (v : ℝ≥0) {ε : ℝ} (hε : 0 ≤ ε) :
    (gaussianReal 0 v).real {x : ℝ | ε ≤ |x|} ≤
      2 * exp (-ε ^ 2 / (2 * v)) := by
  have hX : HasSubgaussianMGF (id : ℝ → ℝ) v (gaussianReal 0 v) :=
    hasSubgaussianMGF_id_gaussianReal v
  have hsplit :
      {x : ℝ | ε ≤ |x|} ⊆ {x : ℝ | ε ≤ x} ∪ {x : ℝ | ε ≤ -x} := by
    intro x hx
    rcases abs_choice x with h | h
    · left
      rwa [Set.mem_setOf_eq, h] at hx
    · right
      rwa [Set.mem_setOf_eq, h] at hx
  have hpos :
      (gaussianReal 0 v).real {x : ℝ | ε ≤ x} ≤
        exp (-ε ^ 2 / (2 * v)) := by
    simpa using hX.measure_ge_le hε
  have hXneg : HasSubgaussianMGF (fun x : ℝ => -x) v (gaussianReal 0 v) := hX.neg
  have hneg :
      (gaussianReal 0 v).real {x : ℝ | ε ≤ -x} ≤
        exp (-ε ^ 2 / (2 * v)) := by
    have h := hXneg.measure_ge_le hε
    simpa [Pi.neg_apply] using h
  calc
    (gaussianReal 0 v).real {x : ℝ | ε ≤ |x|}
        ≤ (gaussianReal 0 v).real ({x | ε ≤ x} ∪ {x | ε ≤ -x}) :=
          measureReal_mono hsplit
    _ ≤ (gaussianReal 0 v).real {x | ε ≤ x} +
          (gaussianReal 0 v).real {x | ε ≤ -x} :=
          measureReal_union_le _ _
    _ ≤ exp (-ε ^ 2 / (2 * v)) + exp (-ε ^ 2 / (2 * v)) := by
          gcongr
    _ = 2 * exp (-ε ^ 2 / (2 * v)) := by ring

end ProbabilityTools
end PptFactorization
