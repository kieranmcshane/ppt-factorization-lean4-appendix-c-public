import PptFactorization.HighProbabilityBounds

/-!
# Appendix B: canonical concrete matrix model

This file fixes the concrete model used by Appendix B:

* left tensor factor `Fin d`,
* right tensor factor `Fin d`,
* sample/ancilla index `Fin s`,
* asymptotic regime `s d / d^2 → λ`.

It contains no analytic estimates.  Its purpose is to make the dimensions and
the asymptotic scaling canonical before the probabilistic and moment arguments
are attached.
-/

open Filter
open scoped Topology

noncomputable section

namespace PptFactorization
namespace AppendixB
namespace ConcreteModel

open RandomMatrixModel GaussianModel HighProbabilityBounds

/-! ## Fixed finite model -/

/-- Left tensor factor in the concrete Appendix B model. -/
abbrev LeftIndex (d : ℕ) := Fin d

/-- Right tensor factor in the concrete Appendix B model. -/
abbrev RightIndex (d : ℕ) := Fin d

/-- Sample/ancilla index in the concrete Appendix B model. -/
abbrev SampleIndex (s : ℕ) := Fin s

/-- Bipartite row index `Fin d × Fin d`. -/
abbrev HilbertIndex (d : ℕ) :=
  BipIndex (LeftIndex d) (RightIndex d)

/-- Rectangular Gaussian sample matrix space `M_{d^2,s}(ℂ)`. -/
abbrev SampleMatrix (d s : ℕ) :=
  RandomMatrixModel.SampleMatrix (LeftIndex d) (RightIndex d) (SampleIndex s)

/-- Square matrix space acting on `ℂ^(d^2)`. -/
abbrev BipMatrix (d : ℕ) :=
  RandomMatrixModel.BipMatrix (LeftIndex d) (RightIndex d)

/-- Concrete Gaussian sample space. -/
abbrev Ω (d s : ℕ) :=
  HighProbabilityBounds.Ω (LeftIndex d) (RightIndex d) (SampleIndex s)

/-- Concrete Gaussian probability measure. -/
def gaussianMeasure (d s : ℕ) : MeasureTheory.Measure (Ω d s) :=
  HighProbabilityBounds.gaussianMeasure (LeftIndex d) (RightIndex d) (SampleIndex s)

/-- Concrete Gaussian random matrix. -/
def gaussianMatrix (d s : ℕ) :
    Ω d s → SampleMatrix d s :=
  HighProbabilityBounds.gaussianMatrix (LeftIndex d) (RightIndex d) (SampleIndex s)

/-- Concrete bipartite dimension, as a real number. -/
def D (d : ℕ) : ℝ :=
  HighProbabilityBounds.bipartiteDimension (LeftIndex d) (RightIndex d)

/-- Concrete sample dimension, as a real number. -/
def S (s : ℕ) : ℝ :=
  HighProbabilityBounds.sampleDimension (SampleIndex s)

@[simp] theorem card_leftIndex (d : ℕ) :
    Fintype.card (LeftIndex d) = d := by
  simp [LeftIndex]

@[simp] theorem card_rightIndex (d : ℕ) :
    Fintype.card (RightIndex d) = d := by
  simp [RightIndex]

@[simp] theorem card_sampleIndex (s : ℕ) :
    Fintype.card (SampleIndex s) = s := by
  simp [SampleIndex]

@[simp] theorem D_eq (d : ℕ) :
    D d = (d : ℝ) ^ 2 := by
  simp [D, HighProbabilityBounds.bipartiteDimension, BipIndex, LeftIndex,
    RightIndex, pow_two]

@[simp] theorem S_eq (s : ℕ) :
    S s = (s : ℝ) := by
  simp [S, HighProbabilityBounds.sampleDimension, SampleIndex]

theorem D_pos {d : ℕ} (hd : 0 < d) :
    0 < D d := by
  rw [D_eq]
  exact sq_pos_of_ne_zero (by exact_mod_cast (Nat.ne_of_gt hd))

theorem S_pos {s : ℕ} (hs : 0 < s) :
    0 < S s := by
  rw [S_eq]
  exact_mod_cast hs

theorem nonempty_leftIndex {d : ℕ} (hd : 0 < d) :
    Nonempty (LeftIndex d) :=
  ⟨⟨0, hd⟩⟩

theorem nonempty_rightIndex {d : ℕ} (hd : 0 < d) :
    Nonempty (RightIndex d) :=
  ⟨⟨0, hd⟩⟩

theorem nonempty_hilbertIndex {d : ℕ} (hd : 0 < d) :
    Nonempty (HilbertIndex d) :=
  ⟨(⟨0, hd⟩, ⟨0, hd⟩)⟩

theorem nonempty_sampleIndex {s : ℕ} (hs : 0 < s) :
    Nonempty (SampleIndex s) :=
  ⟨⟨0, hs⟩⟩

theorem sampleIndex_card_ne_zero {s : ℕ} (hs : 0 < s) :
    Fintype.card (SampleIndex s) ≠ 0 := by
  simpa [SampleIndex] using Nat.ne_of_gt hs

theorem dimension_product_eq (d s : ℕ) :
    D d * S s = (d : ℝ) ^ 2 * (s : ℝ) := by
  simp

/-- A fixed nondegenerate concrete model, with positive bipartite and sample
dimensions. -/
structure Model where
  d : ℕ
  s : ℕ
  hd : 0 < d
  hs : 0 < s

namespace Model

/-- The left tensor factor of a fixed model. -/
abbrev p (M : Model) := LeftIndex M.d

/-- The right tensor factor of a fixed model. -/
abbrev q (M : Model) := RightIndex M.d

/-- The sample index of a fixed model. -/
abbrev σ (M : Model) := SampleIndex M.s

/-- The Gaussian sample space of a fixed model. -/
abbrev Ω (M : Model) := ConcreteModel.Ω M.d M.s

/-- The rectangular sample matrix space of a fixed model. -/
abbrev SampleMatrix (M : Model) := ConcreteModel.SampleMatrix M.d M.s

/-- The square matrix space of a fixed model. -/
abbrev BipMatrix (M : Model) := ConcreteModel.BipMatrix M.d

/-- The bipartite dimension of a fixed model. -/
def D (M : Model) : ℝ := ConcreteModel.D M.d

/-- The sample dimension of a fixed model. -/
def S (M : Model) : ℝ := ConcreteModel.S M.s

@[simp] theorem D_eq (M : Model) :
    M.D = (M.d : ℝ) ^ 2 := by
  simp [Model.D]

@[simp] theorem S_eq (M : Model) :
    M.S = (M.s : ℝ) := by
  simp [Model.S]

theorem D_pos (M : Model) : 0 < M.D := by
  simpa [Model.D] using ConcreteModel.D_pos (d := M.d) M.hd

theorem S_pos (M : Model) : 0 < M.S := by
  simpa [Model.S] using ConcreteModel.S_pos (s := M.s) M.hs

theorem bipartiteDimension_eq (M : Model) :
    HighProbabilityBounds.bipartiteDimension M.p M.q = M.D := rfl

theorem sampleDimension_eq (M : Model) :
    HighProbabilityBounds.sampleDimension M.σ = M.S := rfl

theorem bipartiteDimension_pos (M : Model) :
    0 < HighProbabilityBounds.bipartiteDimension M.p M.q := by
  simpa [bipartiteDimension_eq] using M.D_pos

theorem sampleDimension_pos (M : Model) :
    0 < HighProbabilityBounds.sampleDimension M.σ := by
  simpa [sampleDimension_eq] using M.S_pos

theorem sample_card_ne_zero (M : Model) :
    Fintype.card M.σ ≠ 0 :=
  sampleIndex_card_ne_zero (s := M.s) M.hs

end Model

/-! ## Asymptotic `s_d / d² → λ` regime -/

/-- The sample-to-bipartite-dimension ratio `s_d / d^2`. -/
def sampleRatio (sample : ℕ → ℕ) (d : ℕ) : ℝ :=
  (sample d : ℝ) / (d : ℝ) ^ 2

/-- The exact asymptotic regime used by Appendix B: `s_d / d² → λ`, with
positive limiting aspect ratio and eventually positive sample dimension. -/
structure BalancedRegime where
  sample : ℕ → ℕ
  lam : ℝ
  lam_pos : 0 < lam
  sample_pos_eventually : ∀ᶠ d in atTop, 0 < sample d
  ratio_tendsto : Tendsto (fun d : ℕ => sampleRatio sample d) atTop (𝓝 lam)

namespace BalancedRegime

/-- The concrete model at dimension `d`, when a proof of positivity for
`sample d` is available. -/
def modelAt (R : BalancedRegime) (d : ℕ) (hd : 0 < d)
    (hs : 0 < R.sample d) : Model where
  d := d
  s := R.sample d
  hd := hd
  hs := hs

/-- The ratio hypothesis rewritten with the canonical dimension functions. -/
theorem ratio_tendsto_dimension_form (R : BalancedRegime) :
    Tendsto
      (fun d : ℕ =>
        HighProbabilityBounds.sampleDimension (SampleIndex (R.sample d)) /
          HighProbabilityBounds.bipartiteDimension (LeftIndex d) (RightIndex d))
      atTop (𝓝 R.lam) := by
  simpa [sampleRatio, HighProbabilityBounds.sampleDimension,
    HighProbabilityBounds.bipartiteDimension, LeftIndex, RightIndex,
    SampleIndex, BipIndex, pow_two] using R.ratio_tendsto

/-- Eventually the sample index is nonempty. -/
theorem eventually_nonempty_sampleIndex (R : BalancedRegime) :
    ∀ᶠ d in atTop, Nonempty (SampleIndex (R.sample d)) := by
  exact R.sample_pos_eventually.mono fun _ hs => nonempty_sampleIndex hs

/-- Eventually both the Hilbert index and the sample index are nonempty. -/
theorem eventually_nonempty_indices (R : BalancedRegime) :
    ∀ᶠ d in atTop,
      Nonempty (HilbertIndex d) ∧ Nonempty (SampleIndex (R.sample d)) := by
  filter_upwards [eventually_gt_atTop 0, R.sample_pos_eventually] with d hd hs
  exact ⟨nonempty_hilbertIndex hd, nonempty_sampleIndex hs⟩

end BalancedRegime

end ConcreteModel
end AppendixB
end PptFactorization
