import PptFactorization.AppendixBGaussianIntegrability
import PptFactorization.AppendixBLevyPolarBridge
import PptFactorization.AppendixBSpikeLowerBound
import Mathlib.Probability.CDF

/-!
# Appendix B: spherical concentration bridge

This file isolates the clean paper-facing concentration step.

The repository already has the localized Levy reduction on the exact
Gaussian-direction spherical model.  The only geometric theorem it should
consume is the canonical Levy concentration theorem on the Hilbert--Schmidt
unit sphere, together with the Gaussian polar-law identification of the
direction with surface measure.

Accordingly, this file removes the raw `hGlobalLevy` hypothesis from the final
pipeline wrappers and replaces it by the two canonical inputs:

* `GlobalSurfaceSubtypeLevy`, the spherical isoperimetric/concentration theorem
  on the canonical surface law;
* the polar law identifying the concrete Gaussian direction law with that
  surface law.

It deliberately does not assert the geometric isoperimetric theorem itself.
That theorem is the remaining large external geometric ingredient if one wants
the appendix to be completely no-input.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal

noncomputable section

namespace PptFactorization
namespace AppendixB

open RandomMatrixModel GaussianModel HighProbabilityBounds
open Filter

variable {p q σ : Type*}
variable [Fintype p] [Fintype q] [Fintype σ]
variable [DecidableEq p] [DecidableEq q]

/-! ## Median existence and sharp-isoperimetry bridge -/

/-- Abstract half-measure enlargement bound on a metric probability space.

The front constant is intentionally `1`, not `2`: applied separately to the
two median halfspaces `{g ≤ m}` and `{m ≤ g}`, it yields the standard Levy
tail with front factor `2` after the final union bound. -/
def SurfaceIsoperimetricBound {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α]
    (μ : Measure α) (n : ℝ) : Prop :=
  ∀ ⦃A : Set α⦄, MeasurableSet A →
    (1 / 2 : ℝ) ≤ μ.real A →
    ∀ ⦃t : ℝ⦄, 0 < t →
      μ.real ((Metric.thickening t A)ᶜ) ≤
        Real.exp (-(n * t ^ 2 / 4))

/-- Every measurable real-valued observable on a probability space admits a
median.  We prove this by passing to the push-forward real distribution,
taking the infimum of the `1/2`-superlevel set of its cumulative distribution
function, and using the left/right continuity package already available for
Stieltjes functions. -/
theorem exists_isMedian_of_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ}
    (hf : Measurable f) :
    ∃ m, _root_.AppendixB.IsMedian μ f m := by
  let ν : Measure ℝ := Measure.map f μ
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hf.aemeasurable
  let F : StieltjesFunction ℝ := ProbabilityTheory.cdf ν
  let S : Set ℝ := {x | (1 / 2 : ℝ) ≤ F x}
  have hS_nonempty : S.Nonempty := by
    have hEventually : ∀ᶠ x in atTop, (1 / 2 : ℝ) < F x := by
      have hNhds : Set.Ioi (1 / 2 : ℝ) ∈ nhds (1 : ℝ) := by
        refine Ioi_mem_nhds ?_
        norm_num
      simpa [F] using (ProbabilityTheory.tendsto_cdf_atTop ν hNhds)
    obtain ⟨x, hx⟩ := Filter.Eventually.exists_forall_of_atTop hEventually
    exact ⟨x, le_of_lt (hx x le_rfl)⟩
  have hS_bddBelow : BddBelow S := by
    have hEventually : ∀ᶠ x in atBot, F x < (1 / 2 : ℝ) := by
      have hNhds : Set.Iio (1 / 2 : ℝ) ∈ nhds (0 : ℝ) := by
        refine Iio_mem_nhds ?_
        norm_num
      simpa [F] using (ProbabilityTheory.tendsto_cdf_atBot ν hNhds)
    obtain ⟨x, hx⟩ := Filter.Eventually.exists_forall_of_atBot hEventually
    refine ⟨x, ?_⟩
    intro y hy
    by_contra hyx
    exact not_lt_of_ge hy (hx y (le_of_not_ge hyx))
  refine ⟨sInf S, ?_⟩
  constructor
  · have hRight :
        (1 / 2 : ℝ) ≤ ProbabilityTheory.cdf ν (sInf S) := by
      have hEventuallyRight :
          ∀ᶠ y in nhdsWithin (sInf S) (Set.Ioi (sInf S)),
            (1 / 2 : ℝ) ≤ ProbabilityTheory.cdf ν y := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        rcases (csInf_lt_iff hS_bddBelow hS_nonempty).mp hy with ⟨z, hzS, hzy⟩
        exact hzS.trans ((ProbabilityTheory.monotone_cdf ν) hzy.le)
      exact ge_of_tendsto
        (((ProbabilityTheory.cdf ν).right_continuous (sInf S)).mono Set.Ioi_subset_Ici_self)
        hEventuallyRight
    have hIic :
        ProbabilityTheory.cdf ν (sInf S) = ν.real (Set.Iic (sInf S)) := by
      simpa using (ProbabilityTheory.cdf_eq_real ν (sInf S))
    calc
      (1 / 2 : ℝ) ≤ ProbabilityTheory.cdf ν (sInf S) := hRight
      _ = ν.real (Set.Iic (sInf S)) := hIic
      _ = μ.real {ω : Ω | f ω ≤ sInf S} := by
        simpa [ν] using
          (map_measureReal_apply (μ := μ) (f := f) hf (s := Set.Iic (sInf S)) measurableSet_Iic)
  · have hLeftLim :
        Function.leftLim (ProbabilityTheory.cdf ν) (sInf S) ≤ (1 / 2 : ℝ) := by
      have hEventuallyLeft :
          ∀ᶠ y in nhdsWithin (sInf S) (Set.Iio (sInf S)),
            ProbabilityTheory.cdf ν y ≤ (1 / 2 : ℝ) := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        by_contra hyGt
        have hyGt' : (1 / 2 : ℝ) < ProbabilityTheory.cdf ν y := by
          exact lt_of_not_ge hyGt
        have hyS : y ∈ S := by
          exact le_of_lt hyGt'
        exact (not_lt_of_ge (csInf_le hS_bddBelow hyS)) hy
      exact le_of_tendsto
        ((ProbabilityTheory.monotone_cdf ν).tendsto_leftLim (sInf S))
        hEventuallyLeft
    have hIci :
        ν.real (Set.Ici (sInf S)) =
          1 - Function.leftLim (ProbabilityTheory.cdf ν) (sInf S) := by
      have hMeasure :
          ν (Set.Ici (sInf S)) =
            ENNReal.ofReal (1 - Function.leftLim (ProbabilityTheory.cdf ν) (sInf S)) := by
        simpa [ProbabilityTheory.measure_cdf ν] using
          (ProbabilityTheory.cdf ν).measure_Ici
            (ProbabilityTheory.tendsto_cdf_atTop ν) (sInf S)
      rw [measureReal_def, hMeasure, ENNReal.toReal_ofReal]
      have hLeftLimLe :
          Function.leftLim (ProbabilityTheory.cdf ν) (sInf S) ≤ 1 := by
        exact (ProbabilityTheory.monotone_cdf ν).leftLim_le le_rfl |>.trans
          (ProbabilityTheory.cdf_le_one ν (sInf S))
      linarith
    calc
      (1 / 2 : ℝ) ≤ 1 - Function.leftLim (ProbabilityTheory.cdf ν) (sInf S) := by
        linarith
      _ = ν.real (Set.Ici (sInf S)) := by symm; exact hIci
      _ = μ.real {ω : Ω | sInf S ≤ f ω} := by
        simpa [ν] using
          (map_measureReal_apply (μ := μ) (f := f) hf (s := Set.Ici (sInf S)) measurableSet_Ici)

omit [DecidableEq p] [DecidableEq q] in
/-- An abstract half-measure enlargement theorem on the canonical surface
probability measure yields the strong fixed-median surface Levy theorem. -/
theorem strongGlobalSurfaceSubtypeLevy_of_surfaceIsoperimetric
    [Nonempty p] [Nonempty q] [Nonempty σ] {n : ℝ}
    (hIso :
      SurfaceIsoperimetricBound
        (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)) n) :
    StrongGlobalSurfaceSubtypeLevy (p := p) (q := q) (σ := σ) n := by
  classical
  let μ := sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)
  haveI : IsProbabilityMeasure μ :=
    sampleSurfaceProbabilityMeasure_isProbabilityMeasure (p := p) (q := q) (σ := σ)
  intro g K hg
  rcases exists_isMedian_of_measurable (μ := μ) (f := g) hg.continuous.measurable with
    ⟨Mg, hMg⟩
  by_cases hK0 : (K : ℝ) = 0
  · refine ⟨Mg, hMg, ?_⟩
    intro u hu
    have hprob :
        μ.real {X : Metric.sphere (0 : SampleMatrix p q σ) 1 | u ≤ |g X - Mg|} ≤ 1 := by
      calc
        μ.real {X : Metric.sphere (0 : SampleMatrix p q σ) 1 | u ≤ |g X - Mg|} ≤
            μ.real (Set.univ : Set (Metric.sphere (0 : SampleMatrix p q σ) 1)) :=
          measureReal_mono (Set.subset_univ _)
            (h₂ := (measure_lt_top μ _).ne)
        _ = 1 := by simp [μ]
    have hK0' : K = 0 := by
      exact_mod_cast hK0
    have hbound :
        1 ≤ 2 * Real.exp (-(n * u ^ 2 / (4 * K ^ 2))) := by
      simp [hK0']
    exact hprob.trans hbound
  · refine ⟨Mg, hMg, ?_⟩
    intro u hu
    let a : ℝ := u / (K : ℝ)
    have hKnn : (K : ℝ) ≠ 0 := hK0
    have hKnn' : K ≠ 0 := by
      intro hK
      apply hKnn
      exact_mod_cast hK
    have hKpos : 0 < (K : ℝ) := by
      exact_mod_cast (show 0 < K from pos_iff_ne_zero.mpr hKnn')
    have ha_pos : 0 < a := by
      exact div_pos hu hKpos
    have hKa : (K : ℝ) * a = u := by
      dsimp [a]
      field_simp [hKnn]
    let A : Set (Metric.sphere (0 : SampleMatrix p q σ) 1) := {X | g X ≤ Mg}
    let B : Set (Metric.sphere (0 : SampleMatrix p q σ) 1) := {X | Mg ≤ g X}
    let upperTail : Set (Metric.sphere (0 : SampleMatrix p q σ) 1) := {X | u ≤ g X - Mg}
    let lowerTail : Set (Metric.sphere (0 : SampleMatrix p q σ) 1) := {X | u ≤ Mg - g X}
    let allTail : Set (Metric.sphere (0 : SampleMatrix p q σ) 1) := {X | u ≤ |g X - Mg|}
    have hA_meas : MeasurableSet A :=
      measurableSet_le hg.continuous.measurable measurable_const
    have hB_meas : MeasurableSet B :=
      measurableSet_le measurable_const hg.continuous.measurable
    have hUpper_subset : upperTail ⊆ (Metric.thickening a A)ᶜ := by
      intro X hX
      rw [Set.mem_compl_iff]
      intro hXA
      rcases Metric.mem_thickening_iff.mp hXA with ⟨Y, hY, hdist⟩
      have hLipXY : |g X - g Y| ≤ (K : ℝ) * dist X Y := by
        simpa [Real.dist_eq] using hg.dist_le_mul X Y
      have hlt : (K : ℝ) * dist X Y < u := by
        calc
          (K : ℝ) * dist X Y < (K : ℝ) * a := mul_lt_mul_of_pos_left hdist hKpos
          _ = u := hKa
      have : u < u := by
        calc
          u ≤ g X - Mg := hX
          _ ≤ g X - g Y := by
            dsimp [A] at hY
            linarith
          _ ≤ |g X - g Y| := le_abs_self _
          _ ≤ (K : ℝ) * dist X Y := hLipXY
          _ < u := hlt
      exact (lt_irrefl u this)
    have hLower_subset : lowerTail ⊆ (Metric.thickening a B)ᶜ := by
      intro X hX
      rw [Set.mem_compl_iff]
      intro hXB
      rcases Metric.mem_thickening_iff.mp hXB with ⟨Y, hY, hdist⟩
      have hLipXY : |g X - g Y| ≤ (K : ℝ) * dist X Y := by
        simpa [Real.dist_eq] using hg.dist_le_mul X Y
      have hlt : (K : ℝ) * dist X Y < u := by
        calc
          (K : ℝ) * dist X Y < (K : ℝ) * a := mul_lt_mul_of_pos_left hdist hKpos
          _ = u := hKa
      have : u < u := by
        calc
          u ≤ Mg - g X := hX
          _ ≤ g Y - g X := by
            dsimp [B] at hY
            linarith
          _ ≤ |g X - g Y| := by
            have hneg : g Y - g X = -(g X - g Y) := by ring
            rw [hneg]
            exact neg_le_abs _
          _ ≤ (K : ℝ) * dist X Y := hLipXY
          _ < u := hlt
      exact (lt_irrefl u this)
    have hsplit : allTail ⊆ upperTail ∪ lowerTail := by
      intro X hX
      by_cases hGX : Mg ≤ g X
      · left
        have habs : |g X - Mg| = g X - Mg := abs_of_nonneg (sub_nonneg.mpr hGX)
        simpa [allTail, upperTail, habs] using hX
      · right
        have hGX' : g X ≤ Mg := le_of_not_ge hGX
        have habs : |g X - Mg| = Mg - g X := by
          rw [abs_of_nonpos (sub_nonpos.mpr hGX')]
          ring
        simpa [allTail, lowerTail, habs] using hX
    have hUpper :
        μ.real upperTail ≤ Real.exp (-(n * a ^ 2 / 4)) := by
      exact
        (measureReal_mono hUpper_subset (h₂ := (measure_lt_top μ _).ne)).trans
          (hIso hA_meas hMg.1 ha_pos)
    have hLower :
        μ.real lowerTail ≤ Real.exp (-(n * a ^ 2 / 4)) := by
      exact
        (measureReal_mono hLower_subset (h₂ := (measure_lt_top μ _).ne)).trans
          (hIso hB_meas hMg.2 ha_pos)
    have hArg : n * a ^ 2 / 4 = n * u ^ 2 / (4 * K ^ 2) := by
      change n * a ^ 2 / 4 = n * u ^ 2 / (4 * (K : ℝ) ^ 2)
      dsimp [a]
      field_simp [hKnn]
    calc
      μ.real allTail ≤ μ.real upperTail + μ.real lowerTail := by
        exact
          (measureReal_mono hsplit (h₂ := (measure_lt_top μ _).ne)).trans
            (measureReal_union_le _ _)
      _ ≤ Real.exp (-(n * a ^ 2 / 4)) + Real.exp (-(n * a ^ 2 / 4)) :=
        add_le_add hUpper hLower
      _ = 2 * Real.exp (-(n * a ^ 2 / 4)) := by ring
      _ = 2 * Real.exp (-(n * u ^ 2 / (4 * K ^ 2))) := by rw [hArg]

omit [DecidableEq p] [DecidableEq q] in
/-- Weak median-centered surface Levy concentration obtained from the abstract
surface isoperimetric bound by forgetting the fixed-median quantifier order. -/
theorem globalSurfaceSubtypeLevy_of_surfaceIsoperimetric
    [Nonempty p] [Nonempty q] [Nonempty σ] {n : ℝ}
    (hIso :
      SurfaceIsoperimetricBound
        (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)) n) :
    GlobalSurfaceSubtypeLevy (p := p) (q := q) (σ := σ) n :=
  StrongGlobalSurfaceSubtypeLevy.toGlobalSurfaceSubtypeLevy
    (p := p) (q := q) (σ := σ)
    (strongGlobalSurfaceSubtypeLevy_of_surfaceIsoperimetric
      (p := p) (q := q) (σ := σ) hIso)

omit [DecidableEq p] [DecidableEq q] in
/-- Direct subtype-sphere isoperimetry obtained by transporting
`FullSphericalIsoperimetry` to the Hilbert--Schmidt sphere of sample matrices.

The full real-sphere theorem gives the sharper half-set tail
`exp (-((D - 1) t^2 / 2))`; the `SurfaceIsoperimetricBound` API asks only for
`exp (-(surfaceLevyDimension * t^2 / 4))`, so the last step weakens the
constant by a factor of two. -/
theorem sampleSurfaceProbabilityMeasure_surfaceIsoperimetric_of_fullSphericalIsoperimetry
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (hIso : FullSphericalIsoperimetry) :
    SurfaceIsoperimetricBound
      (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ))
      (surfaceLevyDimension (p := p) (q := q) (σ := σ)) := by
  classical
  let E := SampleMatrix p q σ
  let n := Module.finrank ℝ E
  let U : E ≃ₗᵢ[ℝ] FinRealEuclideanSpace n :=
    sampleMatrixRealStdRepr (p := p) (q := q) (σ := σ)
  let S : Metric.sphere (0 : E) 1 → FinRealSphere n :=
    Subtype.map U (fun _ hx => by simpa using hx)
  let T : FinRealSphere n → Metric.sphere (0 : E) 1 :=
    Subtype.map U.symm (fun _ hx => by simpa using hx)
  have hn_pos : 0 < n := Module.finrank_pos (R := ℝ) (M := E)
  haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hn_pos⟩
  haveI : IsProbabilityMeasure
      (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)) :=
    sampleSurfaceProbabilityMeasure_isProbabilityMeasure (p := p) (q := q) (σ := σ)
  have hmap :
      Measure.map S (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)) =
        finRealSurfaceProbabilityMeasure n := by
    exact sampleSurfaceProbabilityMeasure_map_sampleMatrixRealStdRepr
      (p := p) (q := q) (σ := σ)
  haveI : IsProbabilityMeasure (finRealSurfaceProbabilityMeasure n) :=
    finRealSurfaceProbabilityMeasure_isProbabilityMeasure n
  intro A hA hhalf t ht
  let B : Set (FinRealSphere n) := {Y | T Y ∈ A}
  have hB_meas : MeasurableSet B := hA.preimage
    (U.symm.continuous.subtype_map (fun _ hx => by simpa using hx)).measurable
  have hB_half :
      (1 / 2 : ℝ) ≤ (finRealSurfaceProbabilityMeasure n).real B := by
    have hreal :
        (finRealSurfaceProbabilityMeasure n).real B =
          (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)).real A := by
      rw [← hmap]
      rw [map_measureReal_apply
        (U.continuous.subtype_map (fun _ hx => by simpa using hx)).measurable hB_meas]
      congr 1
      ext X
      have hTS : T (S X) = X := by
        apply Subtype.ext
        simp [S, T]
      change T (S X) ∈ A ↔ X ∈ A
      rw [hTS]
    rwa [hreal]
  have hgeoTail :
      (finRealSurfaceProbabilityMeasure n).real
          ((finRealSphereGeodesicThickening n t B)ᶜ) ≤
        Real.exp (-((((n : ℝ) - 1) * t ^ 2) / 2)) :=
    finRealSphereGeodesicIsoperimetricBound_of_fullSphericalIsoperimetry
      hIso n hB_meas hB_half (le_of_lt ht)
  have hmetricTail :
      (finRealSurfaceProbabilityMeasure n).real
          ((Metric.thickening t B)ᶜ) ≤
        Real.exp (-((((n : ℝ) - 1) * t ^ 2) / 2)) := by
    have hsubset :
        ((Metric.thickening t B)ᶜ) ⊆
          ((finRealSphereGeodesicThickening n t B)ᶜ) :=
      Set.compl_subset_compl.mpr
        (finRealSphereGeodesicThickening_subset_metricThickening n t B)
    exact
      (measureReal_mono hsubset
        (h₂ := (measure_lt_top (finRealSurfaceProbabilityMeasure n)
          ((finRealSphereGeodesicThickening n t B)ᶜ)).ne)).trans hgeoTail
  have hpre_eq :
      (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)).real
          (S ⁻¹' ((Metric.thickening t B)ᶜ)) =
        (finRealSurfaceProbabilityMeasure n).real
          ((Metric.thickening t B)ᶜ) := by
    rw [← hmap]
    rw [map_measureReal_apply
      (U.continuous.subtype_map (fun _ hx => by simpa using hx)).measurable
      Metric.isOpen_thickening.measurableSet.compl]
  have hsubset :
      ((Metric.thickening t A)ᶜ) ⊆ S ⁻¹' ((Metric.thickening t B)ᶜ) := by
    intro X hX
    rw [Set.mem_preimage, Set.mem_compl_iff]
    intro hthick
    rw [Metric.mem_thickening_iff] at hthick
    rcases hthick with ⟨Y, hYB, hdist⟩
    have hYA : T Y ∈ A := by
      simpa [B] using hYB
    have hdist_eq : dist (S X) Y = dist X (T Y) := by
      simpa [S, T] using (U.isometry.dist_eq X (T Y))
    have hdist' : dist X (T Y) < t := by
      simpa [hdist_eq] using hdist
    exact hX (by
      rw [Metric.mem_thickening_iff]
      exact ⟨T Y, hYA, hdist'⟩)
  have hsampleTail :
      (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)).real
          ((Metric.thickening t A)ᶜ) ≤
        Real.exp (-((((n : ℝ) - 1) * t ^ 2) / 2)) := by
    calc
      (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)).real
          ((Metric.thickening t A)ᶜ) ≤
        (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)).real
          (S ⁻¹' ((Metric.thickening t B)ᶜ)) :=
          measureReal_mono hsubset
            (h₂ := (measure_lt_top
              (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)) _).ne)
      _ = (finRealSurfaceProbabilityMeasure n).real
          ((Metric.thickening t B)ᶜ) := hpre_eq
      _ ≤ Real.exp (-((((n : ℝ) - 1) * t ^ 2) / 2)) := hmetricTail
  have hweak :
      Real.exp (-((((n : ℝ) - 1) * t ^ 2) / 2)) ≤
        Real.exp
          (-(surfaceLevyDimension (p := p) (q := q) (σ := σ) * t ^ 2 / 4)) := by
    have hdim_nonneg : 0 ≤ (n : ℝ) - 1 := by
      have hn1 : (1 : ℝ) ≤ n := by
        exact_mod_cast (Nat.succ_le_of_lt hn_pos)
      linarith
    have hnonneg : 0 ≤ ((n : ℝ) - 1) * t ^ 2 :=
      mul_nonneg hdim_nonneg (sq_nonneg t)
    have hle :
        -((((n : ℝ) - 1) * t ^ 2) / 2) ≤
          -((((n : ℝ) - 1) * t ^ 2) / 4) := by
      nlinarith
    simpa [surfaceLevyDimension, n, E] using Real.exp_le_exp.mpr hle
  exact hsampleTail.trans hweak

omit [DecidableEq p] [DecidableEq q] in
/-- Full real-sphere isoperimetry closes the fixed-median strong Levy theorem
on the canonical Hilbert--Schmidt surface subtype. -/
theorem strongGlobalSurfaceSubtypeLevy_of_fullSphericalIsoperimetry
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (hIso : FullSphericalIsoperimetry) :
    StrongGlobalSurfaceSubtypeLevy
      (p := p) (q := q) (σ := σ)
      (surfaceLevyDimension (p := p) (q := q) (σ := σ)) :=
  strongGlobalSurfaceSubtypeLevy_of_surfaceIsoperimetric
    (p := p) (q := q) (σ := σ)
    (sampleSurfaceProbabilityMeasure_surfaceIsoperimetric_of_fullSphericalIsoperimetry
      (p := p) (q := q) (σ := σ) hIso)

omit [DecidableEq p] [DecidableEq q] in
/-- Sharp ambient spherical isoperimetry implies the strong median-centered
Levy theorem for the same ambient surface law. -/
theorem strongGlobalSphericalLevy_of_sharpSphericalIsoperimetry
    [Nonempty p] [Nonempty q] [Nonempty σ]
    {μ : Measure (SampleMatrix p q σ)} {realDim : ℝ}
    (hDim : 0 ≤ realDim - 1)
    (I : _root_.AppendixB.SharpSphericalIsoperimetry
      (p := p) (q := q) (σ := σ) μ realDim) :
    StrongGlobalSphericalLevy (p := p) (q := q) (σ := σ) μ (realDim - 1) := by
  haveI : IsProbabilityMeasure μ := I.is_probability
  intro g K hg
  by_cases hK0 : (K : ℝ) = 0
  · let Mg := g 0
    have hconst : ∀ x y : SampleMatrix p q σ, g x = g y := by
      intro x y
      have hK0nn : K = 0 := by
        exact_mod_cast hK0
      have hxy : edist (g x) (g y) ≤ 0 := by
        have hxy' := hg x y
        simpa [hK0nn, zero_mul] using hxy'
      exact edist_eq_zero.mp (le_antisymm hxy bot_le)
    have hunivhalf : (1 / 2 : ℝ) ≤ μ.real Set.univ := by
      simpa using (show (1 / 2 : ℝ) ≤ (1 : ℝ) by norm_num)
    refine ⟨Mg, ?_, ?_⟩
    · constructor
      · have hset : {X : SampleMatrix p q σ | g X ≤ Mg} = Set.univ := by
          ext X
          simp [Mg, hconst X 0]
        simpa [hset] using hunivhalf
      · have hset : {X : SampleMatrix p q σ | Mg ≤ g X} = Set.univ := by
          ext X
          simp [Mg, hconst X 0]
        simpa [hset] using hunivhalf
    · intro u hu
      have hempty : {X : SampleMatrix p q σ | u ≤ |g X - Mg|} = ∅ := by
        ext X
        have hX : g X = Mg := hconst X 0
        simp [Mg, hX, not_le_of_gt hu]
      rw [hempty, measureReal_empty]
      positivity
  · rcases exists_isMedian_of_measurable (μ := μ) (f := g) hg.continuous.measurable with
      ⟨Mg, hMg⟩
    refine ⟨Mg, hMg, ?_⟩
    intro u hu
    let a : ℝ := u / (K : ℝ)
    have hKnn : K ≠ 0 := by
      intro hK
      apply hK0
      exact_mod_cast hK
    have hKpos : 0 < (K : ℝ) := by
      exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hKnn)
    have ha_pos : 0 < a := by
      exact div_pos hu hKpos
    let upperTail : Set (SampleMatrix p q σ) := {X | u ≤ g X - Mg}
    let lowerTail : Set (SampleMatrix p q σ) := {X | u ≤ Mg - g X}
    let allTail : Set (SampleMatrix p q σ) := {X | u ≤ |g X - Mg|}
    have hsplit : allTail ⊆ upperTail ∪ lowerTail := by
      intro X hX
      by_cases hGX : Mg ≤ g X
      · left
        have habs : |g X - Mg| = g X - Mg := abs_of_nonneg (sub_nonneg.mpr hGX)
        simpa [allTail, upperTail, habs] using hX
      · right
        have hGX' : g X ≤ Mg := le_of_not_ge hGX
        have habs : |g X - Mg| = Mg - g X := by
          rw [abs_of_nonpos (sub_nonpos.mpr hGX')]
          ring
        simpa [allTail, lowerTail, habs] using hX
    have hUpper :
        μ.real upperTail ≤
          Real.exp (-(((realDim - 1) * a ^ 2) / 2)) := by
      let A : Set (SampleMatrix p q σ) := {X | g X ≤ Mg}
      have hA_meas : MeasurableSet A :=
        measurableSet_le hg.continuous.measurable measurable_const
      have hA_half : (1 / 2 : ℝ) ≤ μ.real A := hMg.1
      let r : ℕ → ℝ := fun n => a - a / (n + 2 : ℝ)
      have hr_nonneg : ∀ n, 0 ≤ r n := by
        intro n
        dsimp [r]
        rw [sub_nonneg]
        have hden : 0 < (n + 2 : ℝ) := by positivity
        rw [div_le_iff₀ hden]
        have hn : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.zero_le n)
        nlinarith [le_of_lt ha_pos]
      have hr_lt : ∀ n, r n < a := by
        intro n
        dsimp [r]
        have hdivpos : 0 < a / (n + 2 : ℝ) := by positivity
        linarith
      have hupper_n :
          ∀ n, μ.real upperTail ≤ Real.exp (-(((realDim - 1) * (r n) ^ 2) / 2)) := by
        intro n
        have hsubset :
            upperTail ⊆
              (_root_.AppendixB.frobeniusNeighborhood
                (p := p) (q := q) (σ := σ) A (r n))ᶜ := by
          intro X hX hXnear
          rcases hXnear with ⟨Y, hY, hdist⟩
          have hAbs : |g X - g Y| ≤ (K : ℝ) * dist X Y := by
            simpa [Real.dist_eq] using hg.dist_le_mul X Y
          have hSub : g X - g Y ≤ (K : ℝ) * dist X Y := by
            exact (abs_le.mp hAbs).2
          change u ≤ g X - Mg at hX
          change g Y ≤ Mg at hY
          have hLower : u ≤ g X - g Y := by
            linarith
          have hdist' : dist X Y ≤ r n := by
            simpa [frobeniusNorm, dist_eq_norm] using hdist
          have hrn : r n < u / (K : ℝ) := by
            simpa [a] using hr_lt n
          have hkr : (K : ℝ) * r n < u := by
            calc
              (K : ℝ) * r n < (K : ℝ) * (u / (K : ℝ)) :=
                mul_lt_mul_of_pos_left hrn hKpos
              _ = u := by field_simp [hKnn]
          have hUpper' : g X - g Y < u := by
            exact lt_of_le_of_lt
              (le_trans hSub (mul_le_mul_of_nonneg_left hdist' hKpos.le))
              hkr
          exact (not_lt_of_ge hLower) hUpper'
        exact (measureReal_mono hsubset (h₂ := (measure_lt_top μ _).ne)).trans
          (I.tail hA_meas hA_half (hr_nonneg n))
      have hr_zero :
          Tendsto (fun n : ℕ => a / (n + 2 : ℝ)) atTop (nhds 0) := by
        convert
          (tendsto_const_div_atTop_nhds_zero_nat a).comp
            (tendsto_add_atTop_nat 2) using 1
        ext n
        simp [Function.comp]
      have hr_tend : Tendsto r atTop (nhds a) := by
        simpa [r] using tendsto_const_nhds.sub hr_zero
      have hExp_tend :
          Tendsto (fun n => Real.exp (-(((realDim - 1) * (r n) ^ 2) / 2))) atTop
            (nhds (Real.exp (-(((realDim - 1) * a ^ 2) / 2)))) := by
        have hcont :
            Continuous (fun x : ℝ => Real.exp (-(((realDim - 1) * x ^ 2) / 2))) := by
          continuity
        simpa [r] using hcont.tendsto a |>.comp hr_tend
      exact le_of_tendsto_of_tendsto' tendsto_const_nhds hExp_tend (fun n => hupper_n n)
    have hLower :
        μ.real lowerTail ≤
          Real.exp (-(((realDim - 1) * a ^ 2) / 2)) := by
      let B : Set (SampleMatrix p q σ) := {X | Mg ≤ g X}
      have hB_meas : MeasurableSet B :=
        measurableSet_le measurable_const hg.continuous.measurable
      have hB_half : (1 / 2 : ℝ) ≤ μ.real B := hMg.2
      let r : ℕ → ℝ := fun n => a - a / (n + 2 : ℝ)
      have hr_nonneg : ∀ n, 0 ≤ r n := by
        intro n
        dsimp [r]
        rw [sub_nonneg]
        have hden : 0 < (n + 2 : ℝ) := by positivity
        rw [div_le_iff₀ hden]
        have hn : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.zero_le n)
        nlinarith [le_of_lt ha_pos]
      have hr_lt : ∀ n, r n < a := by
        intro n
        dsimp [r]
        have hdivpos : 0 < a / (n + 2 : ℝ) := by positivity
        linarith
      have hlower_n :
          ∀ n, μ.real lowerTail ≤ Real.exp (-(((realDim - 1) * (r n) ^ 2) / 2)) := by
        intro n
        have hsubset :
            lowerTail ⊆
              (_root_.AppendixB.frobeniusNeighborhood
                (p := p) (q := q) (σ := σ) B (r n))ᶜ := by
          intro X hX hXnear
          rcases hXnear with ⟨Y, hY, hdist⟩
          have hAbs : |g X - g Y| ≤ (K : ℝ) * dist X Y := by
            simpa [Real.dist_eq] using hg.dist_le_mul X Y
          have hSub : g Y - g X ≤ (K : ℝ) * dist X Y := by
            have hAbs' := abs_le.mp hAbs
            linarith
          change u ≤ Mg - g X at hX
          change Mg ≤ g Y at hY
          have hLower : u ≤ g Y - g X := by
            linarith
          have hdist' : dist X Y ≤ r n := by
            simpa [frobeniusNorm, dist_eq_norm] using hdist
          have hrn : r n < u / (K : ℝ) := by
            simpa [a] using hr_lt n
          have hkr : (K : ℝ) * r n < u := by
            calc
              (K : ℝ) * r n < (K : ℝ) * (u / (K : ℝ)) :=
                mul_lt_mul_of_pos_left hrn hKpos
              _ = u := by field_simp [hKnn]
          have hUpper' : g Y - g X < u := by
            exact lt_of_le_of_lt
              (le_trans hSub (mul_le_mul_of_nonneg_left hdist' hKpos.le))
              hkr
          exact (not_lt_of_ge hLower) hUpper'
        exact (measureReal_mono hsubset (h₂ := (measure_lt_top μ _).ne)).trans
          (I.tail hB_meas hB_half (hr_nonneg n))
      have hr_zero :
          Tendsto (fun n : ℕ => a / (n + 2 : ℝ)) atTop (nhds 0) := by
        convert
          (tendsto_const_div_atTop_nhds_zero_nat a).comp
            (tendsto_add_atTop_nat 2) using 1
        ext n
        simp [Function.comp]
      have hr_tend : Tendsto r atTop (nhds a) := by
        simpa [r] using tendsto_const_nhds.sub hr_zero
      have hExp_tend :
          Tendsto (fun n => Real.exp (-(((realDim - 1) * (r n) ^ 2) / 2))) atTop
            (nhds (Real.exp (-(((realDim - 1) * a ^ 2) / 2)))) := by
        have hcont :
            Continuous (fun x : ℝ => Real.exp (-(((realDim - 1) * x ^ 2) / 2))) := by
          continuity
        simpa [r] using hcont.tendsto a |>.comp hr_tend
      exact le_of_tendsto_of_tendsto' tendsto_const_nhds hExp_tend (fun n => hlower_n n)
    have hUnion :
        μ.real allTail ≤ μ.real upperTail + μ.real lowerTail := by
      calc
        μ.real allTail ≤ μ.real (upperTail ∪ lowerTail) := by
          exact measureReal_mono hsplit (h₂ := (measure_lt_top μ _).ne)
        _ ≤ μ.real upperTail + μ.real lowerTail := measureReal_union_le _ _
    calc
      μ.real allTail ≤ μ.real upperTail + μ.real lowerTail := hUnion
      _ ≤
          Real.exp (-(((realDim - 1) * a ^ 2) / 2)) +
          Real.exp (-(((realDim - 1) * a ^ 2) / 2)) := by
            gcongr
      _ = 2 * Real.exp (-(((realDim - 1) * a ^ 2) / 2)) := by ring
      _ ≤ 2 * Real.exp (-(((realDim - 1) * u ^ 2) / (4 * K ^ 2))) := by
        have hKreal : (K : ℝ) ≠ 0 := by
          exact_mod_cast hKnn
        have haeq : a ^ 2 = u ^ 2 / (K : ℝ) ^ 2 := by
          unfold a
          field_simp [hKreal]
        have htarget :
            ((realDim - 1) * a ^ 2) / 2 =
              (realDim - 1) * u ^ 2 / (2 * (K : ℝ) ^ 2) := by
          rw [haeq]
          ring
        have hweaker :
            (realDim - 1) * u ^ 2 / (4 * (K : ℝ) ^ 2) ≤
              (realDim - 1) * u ^ 2 / (2 * (K : ℝ) ^ 2) := by
          have hnonneg :
              0 ≤ (realDim - 1) * u ^ 2 / (4 * (K : ℝ) ^ 2) := by
            exact div_nonneg (mul_nonneg hDim (sq_nonneg u)) (by positivity)
          have htwo :
              (realDim - 1) * u ^ 2 / (2 * (K : ℝ) ^ 2) =
                2 * ((realDim - 1) * u ^ 2 / (4 * (K : ℝ) ^ 2)) := by
            field_simp [hKreal]
            ring
          rw [htwo]
          nlinarith
        have hneg :
            -((realDim - 1) * u ^ 2 / (2 * (K : ℝ) ^ 2)) ≤
              -((realDim - 1) * u ^ 2 / (4 * (K : ℝ) ^ 2)) := by
          nlinarith [hweaker]
        rw [htarget]
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr hneg) (by norm_num)

omit [DecidableEq p] [DecidableEq q] in
/-- A global Levy theorem for the ambient surface law induces the corresponding
subtype-sphere theorem by McShane extension and restriction back to the sphere. -/
theorem globalSurfaceSubtypeLevy_of_surfaceModel
    [Nonempty p] [Nonempty q] [Nonempty σ] {n : ℝ}
    (hLevy :
      GlobalSphericalLevy
        (p := p) (q := q) (σ := σ)
        (surfaceModelMeasure (p := p) (q := q) (σ := σ)) n) :
    GlobalSurfaceSubtypeLevy (p := p) (q := q) (σ := σ) n := by
  classical
  intro g K hg u hu
  let Ω : Set (SampleMatrix p q σ) := Metric.sphere (0 : SampleMatrix p q σ) 1
  let f : SampleMatrix p q σ → ℝ :=
    fun X => if hX : X ∈ Ω then g ⟨X, hX⟩ else 0
  have hLipOn :
      _root_.AppendixB.LipschitzOn
        (fun X Y : SampleMatrix p q σ => dist X Y) Ω f K := by
    intro X Y hX hY
    change |f X - f Y| ≤ (K : ℝ) * dist X Y
    simp [f, hX, hY]
    simpa [Real.dist_eq] using hg.dist_le_mul ⟨X, hX⟩ ⟨Y, hY⟩
  rcases _root_.AppendixB.mcShane_extension_real
      (Ω := Ω) (f := f) (K := K) hLipOn with
    ⟨G, hG, hGΩ⟩
  rcases hLevy hG hu with ⟨Mg, hMg, hTail⟩
  have hG_sphere :
      ∀ X : Metric.sphere (0 : SampleMatrix p q σ) 1, G X = g X := by
    intro X
    have hEq := hGΩ (X : SampleMatrix p q σ) X.property
    simpa [Ω, f, X.property] using hEq.symm
  refine ⟨Mg, ?_, ?_⟩
  · rcases hMg with ⟨hLeft, hRight⟩
    constructor
    · have hmeas :
          MeasurableSet {X : SampleMatrix p q σ | G X ≤ Mg} :=
        measurableSet_le hG.continuous.measurable measurable_const
      calc
        (1 / 2 : ℝ) ≤
            (surfaceModelMeasure (p := p) (q := q) (σ := σ)).real
              {X : SampleMatrix p q σ | G X ≤ Mg} := hLeft
        _ =
            (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)).real
              {X : Metric.sphere (0 : SampleMatrix p q σ) 1 | g X ≤ Mg} := by
          unfold surfaceModelMeasure sampleSurfaceProbabilityMeasureAmbient
          rw [map_measureReal_apply continuous_subtype_val.measurable hmeas]
          congr 1
          ext X
          simp [hG_sphere X]
    · have hmeas :
          MeasurableSet {X : SampleMatrix p q σ | Mg ≤ G X} :=
        measurableSet_le measurable_const hG.continuous.measurable
      calc
        (1 / 2 : ℝ) ≤
            (surfaceModelMeasure (p := p) (q := q) (σ := σ)).real
              {X : SampleMatrix p q σ | Mg ≤ G X} := hRight
        _ =
            (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)).real
              {X : Metric.sphere (0 : SampleMatrix p q σ) 1 | Mg ≤ g X} := by
          unfold surfaceModelMeasure sampleSurfaceProbabilityMeasureAmbient
          rw [map_measureReal_apply continuous_subtype_val.measurable hmeas]
          congr 1
          ext X
          simp [hG_sphere X]
  · have hmeas :
        MeasurableSet {X : SampleMatrix p q σ | u ≤ |G X - Mg|} :=
      measurableSet_le measurable_const
        ((hG.continuous.sub continuous_const).abs.measurable)
    calc
      (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)).real
          {X : Metric.sphere (0 : SampleMatrix p q σ) 1 | u ≤ |g X - Mg|} =
        (surfaceModelMeasure (p := p) (q := q) (σ := σ)).real
          {X : SampleMatrix p q σ | u ≤ |G X - Mg|} := by
          unfold surfaceModelMeasure sampleSurfaceProbabilityMeasureAmbient
          rw [map_measureReal_apply continuous_subtype_val.measurable hmeas]
          congr 1
          ext X
          simp [hG_sphere X]
      _ ≤ 2 * Real.exp (-(n * u ^ 2 / (4 * K ^ 2))) := hTail

omit [DecidableEq p] [DecidableEq q] in
/-- Port the full real-sphere isoperimetric theorem to the project's sharp
ambient Hilbert--Schmidt-sphere interface.

This theorem is the mechanical transport step: the only geometric input is
`FullSphericalIsoperimetry` on the concrete real sphere `S^{n-1}`.  The
standard real-coordinate isometry identifies the matrix Frobenius sphere with
that real sphere, and the normalized surface laws are transported exactly by
`sampleSurfaceProbabilityMeasureAmbient_map_sampleMatrixRealStdRepr`. -/
theorem sharpSphericalIsoperimetry_of_fullSphericalIsoperimetry
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (hIso : FullSphericalIsoperimetry) :
    _root_.AppendixB.SharpSphericalIsoperimetry
      (p := p) (q := q) (σ := σ)
      (surfaceModelMeasure (p := p) (q := q) (σ := σ))
      (Module.finrank ℝ (SampleMatrix p q σ)) := by
  classical
  haveI : IsProbabilityMeasure
      (surfaceModelMeasure (p := p) (q := q) (σ := σ)) :=
    surfaceModelMeasure_isProbabilityMeasure (p := p) (q := q) (σ := σ)
  refine
    { is_probability := surfaceModelMeasure_isProbabilityMeasure
        (p := p) (q := q) (σ := σ)
      tail := ?_ }
  intro A r hA hhalf hr
  have hsubset :
      ((_root_.AppendixB.frobeniusNeighborhood
        (p := p) (q := q) (σ := σ) A r)ᶜ) ⊆ ((Metric.thickening r A)ᶜ) := by
    intro X hX
    rw [Set.mem_compl_iff]
    intro hthick
    rw [Metric.mem_thickening_iff] at hthick
    rcases hthick with ⟨Y, hYA, hdist⟩
    have hfro :
        frobeniusNorm
            (p := p) (q := q) (σ := σ) (X - Y) ≤ r := by
      have hle : dist X Y ≤ r := le_of_lt hdist
      change ‖X - Y‖ ≤ r
      simpa [dist_eq_norm] using hle
    exact hX ⟨Y, hYA, hfro⟩
  have htail :
      (surfaceModelMeasure (p := p) (q := q) (σ := σ)).real
          ((Metric.thickening r A)ᶜ) ≤
        Real.exp
          (-((((Module.finrank ℝ (SampleMatrix p q σ) : ℝ) - 1) * r ^ 2) / 2)) := by
    change
      (sampleSurfaceProbabilityMeasureAmbient (p := p) (q := q) (σ := σ)).real
          ((Metric.thickening r A)ᶜ) ≤
        Real.exp
          (-((((Module.finrank ℝ (SampleMatrix p q σ) : ℝ) - 1) * r ^ 2) / 2))
    exact
      sampleSurfaceProbabilityMeasureAmbient_euclideanThickening_compl_le_of_fullSphericalIsoperimetry
        (p := p) (q := q) (σ := σ) hIso hA (by simpa using hhalf) hr
  calc
    (surfaceModelMeasure (p := p) (q := q) (σ := σ)).real
        ((_root_.AppendixB.frobeniusNeighborhood
          (p := p) (q := q) (σ := σ) A r)ᶜ) ≤
      (surfaceModelMeasure (p := p) (q := q) (σ := σ)).real
        ((Metric.thickening r A)ᶜ) :=
        measureReal_mono hsubset
          (h₂ := (measure_lt_top
            (surfaceModelMeasure (p := p) (q := q) (σ := σ)) _).ne)
    _ ≤ Real.exp
          (-((((Module.finrank ℝ (SampleMatrix p q σ) : ℝ) - 1) * r ^ 2) / 2)) :=
        htail

/-- Sharp spherical isoperimetry for the canonical ambient surface law yields
the project's surface-subtype Levy theorem at the geometric sphere dimension. -/
theorem sampleSurfaceProbabilityMeasure_isoperimetric
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (I :
      _root_.AppendixB.SharpSphericalIsoperimetry
        (p := p) (q := q) (σ := σ)
        (surfaceModelMeasure (p := p) (q := q) (σ := σ))
        (Module.finrank ℝ (SampleMatrix p q σ))) :
    GlobalSurfaceSubtypeLevy
      (p := p) (q := q) (σ := σ)
      (surfaceLevyDimension (p := p) (q := q) (σ := σ)) := by
  classical
  letI : DecidableEq p := Classical.decEq p
  letI : DecidableEq q := Classical.decEq q
  haveI : Nontrivial (SampleMatrix p q σ) := by infer_instance
  have hfin : 0 < Module.finrank ℝ (SampleMatrix p q σ) :=
    Module.finrank_pos (R := ℝ) (M := SampleMatrix p q σ)
  have hDim :
      0 ≤ (Module.finrank ℝ (SampleMatrix p q σ) : ℝ) - 1 := by
    have hfin' : (1 : ℝ) ≤ Module.finrank ℝ (SampleMatrix p q σ) := by
      exact_mod_cast (Nat.succ_le_of_lt hfin)
    linarith
  have hAmbientStrong :
      StrongGlobalSphericalLevy
        (p := p) (q := q) (σ := σ)
        (surfaceModelMeasure (p := p) (q := q) (σ := σ))
        (surfaceLevyDimension (p := p) (q := q) (σ := σ)) := by
    change
      StrongGlobalSphericalLevy
        (p := p) (q := q) (σ := σ)
        (surfaceModelMeasure (p := p) (q := q) (σ := σ))
        (((Module.finrank ℝ (SampleMatrix p q σ) : ℝ)) - 1)
    exact
      strongGlobalSphericalLevy_of_sharpSphericalIsoperimetry
        (p := p) (q := q) (σ := σ)
        (μ := surfaceModelMeasure (p := p) (q := q) (σ := σ))
        (realDim := (Module.finrank ℝ (SampleMatrix p q σ) : ℝ))
        hDim I
  have hAmbient :
      GlobalSphericalLevy
        (p := p) (q := q) (σ := σ)
        (surfaceModelMeasure (p := p) (q := q) (σ := σ))
        (surfaceLevyDimension (p := p) (q := q) (σ := σ)) :=
    StrongGlobalSphericalLevy.toGlobalSphericalLevy
      (p := p) (q := q) (σ := σ) hAmbientStrong
  change
    ∀ {g : Metric.sphere (0 : SampleMatrix p q σ) 1 → ℝ} {K : ℝ≥0},
      LipschitzWith K g →
        ∀ {u : ℝ}, 0 < u →
          ∃ Mg,
            _root_.AppendixB.IsMedian
              (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)) g Mg ∧
              (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)).real
                  {X | u ≤ |g X - Mg|} ≤
                2 * Real.exp
                  (-(surfaceLevyDimension (p := p) (q := q) (σ := σ) *
                      u ^ 2 / (4 * K ^ 2)))
  exact
    globalSurfaceSubtypeLevy_of_surfaceModel
      (p := p) (q := q) (σ := σ)
      (n := surfaceLevyDimension (p := p) (q := q) (σ := σ))
      hAmbient

omit [DecidableEq p] [DecidableEq q] in
/-- Public one-step port: full sharp isoperimetry on the concrete real sphere
gives the project's canonical global spherical Levy theorem for the
Hilbert--Schmidt sphere. -/
theorem globalSurfaceSubtypeLevy_of_fullSphericalIsoperimetry
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (hIso : FullSphericalIsoperimetry) :
    GlobalSurfaceSubtypeLevy
      (p := p) (q := q) (σ := σ)
      (surfaceLevyDimension (p := p) (q := q) (σ := σ)) :=
  StrongGlobalSurfaceSubtypeLevy.toGlobalSurfaceSubtypeLevy
    (p := p) (q := q) (σ := σ)
    (strongGlobalSurfaceSubtypeLevy_of_fullSphericalIsoperimetry
      (p := p) (q := q) (σ := σ) hIso)

/-- The spherical isoperimetric/concentration theorem, once available on the
canonical surface sphere and transported by the Gaussian polar law, is exactly
the global median-centered Levy theorem required by the localized Appendix B
argument. -/
theorem spherical_isoperimetric_concentration_exact_model
    [Nonempty p] [Nonempty q] [Nonempty σ]
    {n : ℝ}
    (hPolarLaw :
      sphericalModelMeasure (p := p) (q := q) (σ := σ) =
        surfaceModelMeasure (p := p) (q := q) (σ := σ))
    (hSurfaceLevy :
      GlobalSurfaceSubtypeLevy (p := p) (q := q) (σ := σ) n) :
    ∀ {g : SampleMatrix p q σ → ℝ} {K : ℝ≥0},
      LipschitzWith K g →
      ∀ {u : ℝ}, 0 < u →
        ∃ Mg,
          _root_.AppendixB.IsMedian
            (sphericalModelMeasure (p := p) (q := q) (σ := σ)) g Mg ∧
          (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
              {X | u ≤ |g X - Mg|} ≤
            2 * Real.exp (-(n * u ^ 2 / (4 * K ^ 2))) := by
  exact globalSphericalLevy_sphericalModel_of_subtype_and_polar_law
    (p := p) (q := q) (σ := σ) (n := n) hPolarLaw hSurfaceLevy

/-- Final Appendix B pipeline with Gaussian integrability closed and the
global Levy input replaced by the canonical surface concentration theorem plus
the Gaussian polar-law identification. -/
theorem appendixB_pipeline_to_final_theorem_with_spherical_concentration
    [Nonempty p] [Nonempty q] [Nonempty σ] [DecidableEq σ]
    {Q : ℕ → ℝ} {dNat : ℕ}
    {f : SampleMatrix p q σ → ℝ}
    {gaussianMean radialMean sphericalMean C1 CDiag COff : ℝ}
    {mean median range bad a b C cDim d eps momentParameter s : ℝ}
    {r : ℕ}
    (H :
      AubrunOffDiagonalExpectationDerivation
        (p := p) (q := q) (σ := σ) Q dNat d s COff)
    (hDiag :
      gaussianWishartGammaDiagonalOpNormMean (p := p) (q := q) (σ := σ) ≤
        CDiag)
    (hIndepR2 :
      gaussianRadiusSq (p := p) (q := q) (σ := σ) ⟂ᵢ[gaussianMeasure p q σ]
        gaussianDirection (p := p) (q := q) (σ := σ))
    (hRadialMean : 0 < radialMean)
    (hSampleFactor : gaussianMean = radialMean * sphericalMean)
    (hSampleBound : gaussianMean ≤ radialMean * (C1 / d))
    (hd : 0 < d)
    (hs : 1 ≤ sampleDimension σ)
    (hDim : bipartiteDimension p q = d ^ 2)
    (hLarge : 12 * Real.log 2 ≤ d ^ 2)
    (hC : C ≠ 0)
    (hmoment : momentParameter ≠ 0)
    (hScalePos : 0 < _root_.AppendixB.naturalDeviationScale d eps r)
    (hmean :
      mean =
        ∫ X : SampleMatrix p q σ, f X
          ∂sphericalModelMeasure (p := p) (q := q) (σ := σ))
    (hf :
      Integrable f
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)))
    (hRange :
      (fun X : SampleMatrix p q σ => |f X - median|) ≤ᵐ[
        sphericalModelMeasure (p := p) (q := q) (σ := σ)] fun _ => range)
    (hRangeNonneg : 0 ≤ range)
    (hL :
      0 < _root_.AppendixB.localLipschitzScale C momentParameter d r)
    (hn : 0 < cDim * d ^ 4)
    (hSmall :
      _root_.AppendixB.localizedTailIntegralBound
          range bad
          (_root_.AppendixB.localLipschitzScale C momentParameter d r)
          (cDim * d ^ 4) ≤
        _root_.AppendixB.naturalDeviationScale d eps r / 2)
    (hLip :
      _root_.AppendixB.LipschitzOn
        (fun X Y : SampleMatrix p q σ => dist X Y)
        (sphericalOperatorNormGoodSet (p := p) (q := q) (σ := σ) a b d)
        f (_root_.AppendixB.localLipschitzScale C momentParameter d r))
    (hMedian :
      _root_.AppendixB.IsMedian
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)) f median)
    (hPolarLaw :
      sphericalModelMeasure (p := p) (q := q) (σ := σ) =
        surfaceModelMeasure (p := p) (q := q) (σ := σ))
    (hSurfaceLevy :
      GlobalSurfaceSubtypeLevy
        (p := p) (q := q) (σ := σ) (cDim * d ^ 4))
    (hBad :
      (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
          (sphericalOperatorNormGoodSet
            (p := p) (q := q) (σ := σ) a b d)ᶜ ≤ bad)
    (hGood : bad ≤ 2 * _root_.AppendixB.goodSetTail (1 / 12 : ℝ) d) :
    sphericalMean ≤ C1 / d ∧
    sphericalGammaOpNormMean (p := p) (q := q) (σ := σ) ≤
      (CDiag + COff) / d ^ 2 ∧
    (gaussianMeasure p q σ).real
        ((normalizedSampleOpNormEvent
          (p := p) (q := q) (σ := σ)
          (concreteSampleOpNormThreshold (p := p) (q := q) (σ := σ)) d)ᶜ) ≤
      Real.exp (-((1 / 12 : ℝ) * d ^ 2)) ∧
    (gaussianMeasure p q σ).real
        ((normalizedRhoGammaOpNormEvent
          (p := p) (q := q) (σ := σ)
          (concreteRhoGammaOpNormThreshold (p := p) (q := q) (σ := σ)) d)ᶜ) ≤
      Real.exp (-((1 / 12 : ℝ) * d ^ 2)) ∧
    (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
        {X | _root_.AppendixB.naturalDeviationScale d eps r ≤ |f X - mean|} ≤
      _root_.AppendixB.paperTailBound
        4 (1 / 12 : ℝ) (cDim / (64 * C ^ 2)) d eps momentParameter := by
  exact
    appendixB_pipeline_to_final_theorem_with_integrability_closed
      (p := p) (q := q) (σ := σ)
      (Q := Q) (dNat := dNat) (f := f)
      (gaussianMean := gaussianMean)
      (radialMean := radialMean)
      (sphericalMean := sphericalMean)
      (C1 := C1) (CDiag := CDiag) (COff := COff)
      (mean := mean) (median := median) (range := range)
      (bad := bad) (a := a) (b := b) (C := C)
      (cDim := cDim) (d := d) (eps := eps)
      (momentParameter := momentParameter) (s := s) (r := r)
      H hDiag hIndepR2 hRadialMean hSampleFactor hSampleBound
      hd hs hDim hLarge hC hmoment hScalePos
      hmean hf hRange hRangeNonneg hL hn hSmall hLip hMedian
      (spherical_isoperimetric_concentration_exact_model
        (p := p) (q := q) (σ := σ)
        (n := cDim * d ^ 4) hPolarLaw hSurfaceLevy)
      hBad hGood

/-- Same downstream Appendix B pipeline, but with the remaining geometric
polar/Levy input pair packaged as a single canonical object. -/
theorem appendixB_pipeline_to_final_theorem_with_remainingPolarLevyInputs
    [Nonempty p] [Nonempty q] [Nonempty σ] [DecidableEq σ]
    {Q : ℕ → ℝ} {dNat : ℕ}
    {f : SampleMatrix p q σ → ℝ}
    {gaussianMean radialMean sphericalMean C1 CDiag COff : ℝ}
    {mean median range bad a b C cDim d eps momentParameter s : ℝ}
    {r : ℕ}
    (H :
      AubrunOffDiagonalExpectationDerivation
        (p := p) (q := q) (σ := σ) Q dNat d s COff)
    (hDiag :
      gaussianWishartGammaDiagonalOpNormMean (p := p) (q := q) (σ := σ) ≤
        CDiag)
    (hIndepR2 :
      gaussianRadiusSq (p := p) (q := q) (σ := σ) ⟂ᵢ[gaussianMeasure p q σ]
        gaussianDirection (p := p) (q := q) (σ := σ))
    (hRadialMean : 0 < radialMean)
    (hSampleFactor : gaussianMean = radialMean * sphericalMean)
    (hSampleBound : gaussianMean ≤ radialMean * (C1 / d))
    (hd : 0 < d)
    (hs : 1 ≤ sampleDimension σ)
    (hDim : bipartiteDimension p q = d ^ 2)
    (hLarge : 12 * Real.log 2 ≤ d ^ 2)
    (hC : C ≠ 0)
    (hmoment : momentParameter ≠ 0)
    (hScalePos : 0 < _root_.AppendixB.naturalDeviationScale d eps r)
    (hmean :
      mean =
        ∫ X : SampleMatrix p q σ, f X
          ∂sphericalModelMeasure (p := p) (q := q) (σ := σ))
    (hf :
      Integrable f
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)))
    (hRange :
      (fun X : SampleMatrix p q σ => |f X - median|) ≤ᵐ[
        sphericalModelMeasure (p := p) (q := q) (σ := σ)] fun _ => range)
    (hRangeNonneg : 0 ≤ range)
    (hL :
      0 < _root_.AppendixB.localLipschitzScale C momentParameter d r)
    (hn : 0 < cDim * d ^ 4)
    (hSmall :
      _root_.AppendixB.localizedTailIntegralBound
          range bad
          (_root_.AppendixB.localLipschitzScale C momentParameter d r)
          (cDim * d ^ 4) ≤
        _root_.AppendixB.naturalDeviationScale d eps r / 2)
    (hLip :
      _root_.AppendixB.LipschitzOn
        (fun X Y : SampleMatrix p q σ => dist X Y)
        (sphericalOperatorNormGoodSet (p := p) (q := q) (σ := σ) a b d)
        f (_root_.AppendixB.localLipschitzScale C momentParameter d r))
    (hMedian :
      _root_.AppendixB.IsMedian
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)) f median)
    (I :
      RemainingPolarLevyInputs
        (p := p) (q := q) (σ := σ) (cDim * d ^ 4))
    (hBad :
      (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
          (sphericalOperatorNormGoodSet
            (p := p) (q := q) (σ := σ) a b d)ᶜ ≤ bad)
    (hGood : bad ≤ 2 * _root_.AppendixB.goodSetTail (1 / 12 : ℝ) d) :
    sphericalMean ≤ C1 / d ∧
    sphericalGammaOpNormMean (p := p) (q := q) (σ := σ) ≤
      (CDiag + COff) / d ^ 2 ∧
    (gaussianMeasure p q σ).real
        ((normalizedSampleOpNormEvent
          (p := p) (q := q) (σ := σ)
          (concreteSampleOpNormThreshold (p := p) (q := q) (σ := σ)) d)ᶜ) ≤
      Real.exp (-((1 / 12 : ℝ) * d ^ 2)) ∧
    (gaussianMeasure p q σ).real
        ((normalizedRhoGammaOpNormEvent
          (p := p) (q := q) (σ := σ)
          (concreteRhoGammaOpNormThreshold (p := p) (q := q) (σ := σ)) d)ᶜ) ≤
      Real.exp (-((1 / 12 : ℝ) * d ^ 2)) ∧
    (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
        {X | _root_.AppendixB.naturalDeviationScale d eps r ≤ |f X - mean|} ≤
      _root_.AppendixB.paperTailBound
        4 (1 / 12 : ℝ) (cDim / (64 * C ^ 2)) d eps momentParameter := by
  exact appendixB_pipeline_to_final_theorem_with_spherical_concentration
    (p := p) (q := q) (σ := σ)
    (Q := Q) (dNat := dNat) (f := f)
    (gaussianMean := gaussianMean)
    (radialMean := radialMean)
    (sphericalMean := sphericalMean)
    (C1 := C1) (CDiag := CDiag) (COff := COff)
    (mean := mean) (median := median) (range := range)
    (bad := bad) (a := a) (b := b) (C := C)
    (cDim := cDim) (d := d) (eps := eps)
    (momentParameter := momentParameter) (s := s) (r := r)
    H hDiag hIndepR2 hRadialMean hSampleFactor hSampleBound
    hd hs hDim hLarge hC hmoment hScalePos
    hmean hf hRange hRangeNonneg hL hn hSmall hLip hMedian
    I.polarLaw I.surfaceLevy hBad hGood

/-- Feed the downstream Appendix B pipeline directly from the exact canonical
surface Levy theorem at the paper's pipeline exponent. -/
theorem appendixB_pipeline_to_final_theorem_with_surfaceLevy
    [Nonempty p] [Nonempty q] [Nonempty σ] [DecidableEq σ]
    {Q : ℕ → ℝ} {dNat : ℕ}
    {f : SampleMatrix p q σ → ℝ}
    {gaussianMean radialMean sphericalMean C1 CDiag COff : ℝ}
    {mean median range bad a b C cDim d eps momentParameter s : ℝ}
    {r : ℕ}
    (H :
      AubrunOffDiagonalExpectationDerivation
        (p := p) (q := q) (σ := σ) Q dNat d s COff)
    (hDiag :
      gaussianWishartGammaDiagonalOpNormMean (p := p) (q := q) (σ := σ) ≤
        CDiag)
    (hIndepR2 :
      gaussianRadiusSq (p := p) (q := q) (σ := σ) ⟂ᵢ[gaussianMeasure p q σ]
        gaussianDirection (p := p) (q := q) (σ := σ))
    (hRadialMean : 0 < radialMean)
    (hSampleFactor : gaussianMean = radialMean * sphericalMean)
    (hSampleBound : gaussianMean ≤ radialMean * (C1 / d))
    (hd : 0 < d)
    (hs : 1 ≤ sampleDimension σ)
    (hDim : bipartiteDimension p q = d ^ 2)
    (hLarge : 12 * Real.log 2 ≤ d ^ 2)
    (hC : C ≠ 0)
    (hmoment : momentParameter ≠ 0)
    (hScalePos : 0 < _root_.AppendixB.naturalDeviationScale d eps r)
    (hmean :
      mean =
        ∫ X : SampleMatrix p q σ, f X
          ∂sphericalModelMeasure (p := p) (q := q) (σ := σ))
    (hf :
      Integrable f
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)))
    (hRange :
      (fun X : SampleMatrix p q σ => |f X - median|) ≤ᵐ[
        sphericalModelMeasure (p := p) (q := q) (σ := σ)] fun _ => range)
    (hRangeNonneg : 0 ≤ range)
    (hL :
      0 < _root_.AppendixB.localLipschitzScale C momentParameter d r)
    (hn : 0 < cDim * d ^ 4)
    (hSmall :
      _root_.AppendixB.localizedTailIntegralBound
          range bad
          (_root_.AppendixB.localLipschitzScale C momentParameter d r)
          (cDim * d ^ 4) ≤
        _root_.AppendixB.naturalDeviationScale d eps r / 2)
    (hLip :
      _root_.AppendixB.LipschitzOn
        (fun X Y : SampleMatrix p q σ => dist X Y)
        (sphericalOperatorNormGoodSet (p := p) (q := q) (σ := σ) a b d)
        f (_root_.AppendixB.localLipschitzScale C momentParameter d r))
    (hMedian :
      _root_.AppendixB.IsMedian
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)) f median)
    (hSurface :
      GlobalSurfaceSubtypeLevy
        (p := p) (q := q) (σ := σ) (cDim * d ^ 4))
    (hBad :
      (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
          (sphericalOperatorNormGoodSet
            (p := p) (q := q) (σ := σ) a b d)ᶜ ≤ bad)
    (hGood : bad ≤ 2 * _root_.AppendixB.goodSetTail (1 / 12 : ℝ) d) :
    sphericalMean ≤ C1 / d ∧
    sphericalGammaOpNormMean (p := p) (q := q) (σ := σ) ≤
      (CDiag + COff) / d ^ 2 ∧
    (gaussianMeasure p q σ).real
        ((normalizedSampleOpNormEvent
          (p := p) (q := q) (σ := σ)
          (concreteSampleOpNormThreshold (p := p) (q := q) (σ := σ)) d)ᶜ) ≤
      Real.exp (-((1 / 12 : ℝ) * d ^ 2)) ∧
    (gaussianMeasure p q σ).real
        ((normalizedRhoGammaOpNormEvent
          (p := p) (q := q) (σ := σ)
          (concreteRhoGammaOpNormThreshold (p := p) (q := q) (σ := σ)) d)ᶜ) ≤
      Real.exp (-((1 / 12 : ℝ) * d ^ 2)) ∧
    (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
        {X | _root_.AppendixB.naturalDeviationScale d eps r ≤ |f X - mean|} ≤
      _root_.AppendixB.paperTailBound
        4 (1 / 12 : ℝ) (cDim / (64 * C ^ 2)) d eps momentParameter := by
  exact appendixB_pipeline_to_final_theorem_with_remainingPolarLevyInputs
    (p := p) (q := q) (σ := σ)
    (Q := Q) (dNat := dNat) (f := f)
    (gaussianMean := gaussianMean)
    (radialMean := radialMean)
    (sphericalMean := sphericalMean)
    (C1 := C1) (CDiag := CDiag) (COff := COff)
    (mean := mean) (median := median) (range := range)
    (bad := bad) (a := a) (b := b) (C := C)
    (cDim := cDim) (d := d) (eps := eps)
    (momentParameter := momentParameter) (s := s) (r := r)
    H hDiag hIndepR2 hRadialMean hSampleFactor hSampleBound
    hd hs hDim hLarge hC hmoment hScalePos
    hmean hf hRange hRangeNonneg hL hn hSmall hLip hMedian
    (remainingPolarLevyInputs_of_surfaceLevy
      (p := p) (q := q) (σ := σ) hSurface)
    hBad hGood

/-- Feed the downstream Appendix B pipeline from the canonical surface Levy
theorem at the geometric sphere dimension, together with a comparison between
that dimension and the paper's pipeline exponent. -/
theorem appendixB_pipeline_to_final_theorem_with_surfaceLevyDimension
    [Nonempty p] [Nonempty q] [Nonempty σ] [DecidableEq σ]
    {Q : ℕ → ℝ} {dNat : ℕ}
    {f : SampleMatrix p q σ → ℝ}
    {gaussianMean radialMean sphericalMean C1 CDiag COff : ℝ}
    {mean median range bad a b C cDim d eps momentParameter s : ℝ}
    {r : ℕ}
    (H :
      AubrunOffDiagonalExpectationDerivation
        (p := p) (q := q) (σ := σ) Q dNat d s COff)
    (hDiag :
      gaussianWishartGammaDiagonalOpNormMean (p := p) (q := q) (σ := σ) ≤
        CDiag)
    (hIndepR2 :
      gaussianRadiusSq (p := p) (q := q) (σ := σ) ⟂ᵢ[gaussianMeasure p q σ]
        gaussianDirection (p := p) (q := q) (σ := σ))
    (hRadialMean : 0 < radialMean)
    (hSampleFactor : gaussianMean = radialMean * sphericalMean)
    (hSampleBound : gaussianMean ≤ radialMean * (C1 / d))
    (hd : 0 < d)
    (hs : 1 ≤ sampleDimension σ)
    (hDim : bipartiteDimension p q = d ^ 2)
    (hLarge : 12 * Real.log 2 ≤ d ^ 2)
    (hC : C ≠ 0)
    (hmoment : momentParameter ≠ 0)
    (hScalePos : 0 < _root_.AppendixB.naturalDeviationScale d eps r)
    (hmean :
      mean =
        ∫ X : SampleMatrix p q σ, f X
          ∂sphericalModelMeasure (p := p) (q := q) (σ := σ))
    (hf :
      Integrable f
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)))
    (hRange :
      (fun X : SampleMatrix p q σ => |f X - median|) ≤ᵐ[
        sphericalModelMeasure (p := p) (q := q) (σ := σ)] fun _ => range)
    (hRangeNonneg : 0 ≤ range)
    (hL :
      0 < _root_.AppendixB.localLipschitzScale C momentParameter d r)
    (hn : 0 < cDim * d ^ 4)
    (hSmall :
      _root_.AppendixB.localizedTailIntegralBound
          range bad
          (_root_.AppendixB.localLipschitzScale C momentParameter d r)
          (cDim * d ^ 4) ≤
        _root_.AppendixB.naturalDeviationScale d eps r / 2)
    (hLip :
      _root_.AppendixB.LipschitzOn
        (fun X Y : SampleMatrix p q σ => dist X Y)
        (sphericalOperatorNormGoodSet (p := p) (q := q) (σ := σ) a b d)
        f (_root_.AppendixB.localLipschitzScale C momentParameter d r))
    (hMedian :
      _root_.AppendixB.IsMedian
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)) f median)
    (hCompare :
      cDim * d ^ 4 ≤ surfaceLevyDimension (p := p) (q := q) (σ := σ))
    (hSurfaceTop :
      GlobalSurfaceSubtypeLevy
        (p := p) (q := q) (σ := σ)
        (surfaceLevyDimension (p := p) (q := q) (σ := σ)))
    (hBad :
      (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
          (sphericalOperatorNormGoodSet
            (p := p) (q := q) (σ := σ) a b d)ᶜ ≤ bad)
    (hGood : bad ≤ 2 * _root_.AppendixB.goodSetTail (1 / 12 : ℝ) d) :
    sphericalMean ≤ C1 / d ∧
    sphericalGammaOpNormMean (p := p) (q := q) (σ := σ) ≤
      (CDiag + COff) / d ^ 2 ∧
    (gaussianMeasure p q σ).real
        ((normalizedSampleOpNormEvent
          (p := p) (q := q) (σ := σ)
          (concreteSampleOpNormThreshold (p := p) (q := q) (σ := σ)) d)ᶜ) ≤
      Real.exp (-((1 / 12 : ℝ) * d ^ 2)) ∧
    (gaussianMeasure p q σ).real
        ((normalizedRhoGammaOpNormEvent
          (p := p) (q := q) (σ := σ)
          (concreteRhoGammaOpNormThreshold (p := p) (q := q) (σ := σ)) d)ᶜ) ≤
      Real.exp (-((1 / 12 : ℝ) * d ^ 2)) ∧
    (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
        {X | _root_.AppendixB.naturalDeviationScale d eps r ≤ |f X - mean|} ≤
      _root_.AppendixB.paperTailBound
        4 (1 / 12 : ℝ) (cDim / (64 * C ^ 2)) d eps momentParameter := by
  exact appendixB_pipeline_to_final_theorem_with_remainingPolarLevyInputs
    (p := p) (q := q) (σ := σ)
    (Q := Q) (dNat := dNat) (f := f)
    (gaussianMean := gaussianMean)
    (radialMean := radialMean)
    (sphericalMean := sphericalMean)
    (C1 := C1) (CDiag := CDiag) (COff := COff)
    (mean := mean) (median := median) (range := range)
    (bad := bad) (a := a) (b := b) (C := C)
    (cDim := cDim) (d := d) (eps := eps)
    (momentParameter := momentParameter) (s := s) (r := r)
    H hDiag hIndepR2 hRadialMean hSampleFactor hSampleBound
    hd hs hDim hLarge hC hmoment hScalePos
    hmean hf hRange hRangeNonneg hL hn hSmall hLip hMedian
    (remainingPolarLevyInputs_of_surfaceLevyDimension
      (p := p) (q := q) (σ := σ) hCompare hSurfaceTop)
    hBad hGood

/-- Same downstream Appendix B pipeline, but with the strong remaining
polar/Levy package as the direct input object. -/
theorem appendixB_pipeline_to_final_theorem_with_strongRemainingPolarLevyInputs
    [Nonempty p] [Nonempty q] [Nonempty σ] [DecidableEq σ]
    {Q : ℕ → ℝ} {dNat : ℕ}
    {f : SampleMatrix p q σ → ℝ}
    {gaussianMean radialMean sphericalMean C1 CDiag COff : ℝ}
    {mean median range bad a b C cDim d eps momentParameter s : ℝ}
    {r : ℕ}
    (H :
      AubrunOffDiagonalExpectationDerivation
        (p := p) (q := q) (σ := σ) Q dNat d s COff)
    (hDiag :
      gaussianWishartGammaDiagonalOpNormMean (p := p) (q := q) (σ := σ) ≤
        CDiag)
    (hIndepR2 :
      gaussianRadiusSq (p := p) (q := q) (σ := σ) ⟂ᵢ[gaussianMeasure p q σ]
        gaussianDirection (p := p) (q := q) (σ := σ))
    (hRadialMean : 0 < radialMean)
    (hSampleFactor : gaussianMean = radialMean * sphericalMean)
    (hSampleBound : gaussianMean ≤ radialMean * (C1 / d))
    (hd : 0 < d)
    (hs : 1 ≤ sampleDimension σ)
    (hDim : bipartiteDimension p q = d ^ 2)
    (hLarge : 12 * Real.log 2 ≤ d ^ 2)
    (hC : C ≠ 0)
    (hmoment : momentParameter ≠ 0)
    (hScalePos : 0 < _root_.AppendixB.naturalDeviationScale d eps r)
    (hmean :
      mean =
        ∫ X : SampleMatrix p q σ, f X
          ∂sphericalModelMeasure (p := p) (q := q) (σ := σ))
    (hf :
      Integrable f
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)))
    (hRange :
      (fun X : SampleMatrix p q σ => |f X - median|) ≤ᵐ[
        sphericalModelMeasure (p := p) (q := q) (σ := σ)] fun _ => range)
    (hRangeNonneg : 0 ≤ range)
    (hL :
      0 < _root_.AppendixB.localLipschitzScale C momentParameter d r)
    (hn : 0 < cDim * d ^ 4)
    (hSmall :
      _root_.AppendixB.localizedTailIntegralBound
          range bad
          (_root_.AppendixB.localLipschitzScale C momentParameter d r)
          (cDim * d ^ 4) ≤
        _root_.AppendixB.naturalDeviationScale d eps r / 2)
    (hLip :
      _root_.AppendixB.LipschitzOn
        (fun X Y : SampleMatrix p q σ => dist X Y)
        (sphericalOperatorNormGoodSet (p := p) (q := q) (σ := σ) a b d)
        f (_root_.AppendixB.localLipschitzScale C momentParameter d r))
    (hMedian :
      _root_.AppendixB.IsMedian
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)) f median)
    (I :
      @StrongRemainingPolarLevyInputs p q σ _ _ _ (cDim * d ^ 4))
    (hBad :
      (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
          (sphericalOperatorNormGoodSet
            (p := p) (q := q) (σ := σ) a b d)ᶜ ≤ bad)
    (hGood : bad ≤ 2 * _root_.AppendixB.goodSetTail (1 / 12 : ℝ) d) :
    sphericalMean ≤ C1 / d ∧
    sphericalGammaOpNormMean (p := p) (q := q) (σ := σ) ≤
      (CDiag + COff) / d ^ 2 ∧
    (gaussianMeasure p q σ).real
        ((normalizedSampleOpNormEvent
          (p := p) (q := q) (σ := σ)
          (concreteSampleOpNormThreshold (p := p) (q := q) (σ := σ)) d)ᶜ) ≤
      Real.exp (-((1 / 12 : ℝ) * d ^ 2)) ∧
    (gaussianMeasure p q σ).real
        ((normalizedRhoGammaOpNormEvent
          (p := p) (q := q) (σ := σ)
          (concreteRhoGammaOpNormThreshold (p := p) (q := q) (σ := σ)) d)ᶜ) ≤
      Real.exp (-((1 / 12 : ℝ) * d ^ 2)) ∧
    (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
        {X | _root_.AppendixB.naturalDeviationScale d eps r ≤ |f X - mean|} ≤
      _root_.AppendixB.paperTailBound
        4 (1 / 12 : ℝ) (cDim / (64 * C ^ 2)) d eps momentParameter := by
  exact appendixB_pipeline_to_final_theorem_with_remainingPolarLevyInputs
    (p := p) (q := q) (σ := σ)
    (Q := Q) (dNat := dNat) (f := f)
    (gaussianMean := gaussianMean)
    (radialMean := radialMean)
    (sphericalMean := sphericalMean)
    (C1 := C1) (CDiag := CDiag) (COff := COff)
    (mean := mean) (median := median) (range := range)
    (bad := bad) (a := a) (b := b) (C := C)
    (cDim := cDim) (d := d) (eps := eps)
    (momentParameter := momentParameter) (s := s) (r := r)
    H hDiag hIndepR2 hRadialMean hSampleFactor hSampleBound
    hd hs hDim hLarge hC hmoment hScalePos
    hmean hf hRange hRangeNonneg hL hn hSmall hLip hMedian
    I.toRemainingPolarLevyInputs hBad hGood

end AppendixB
end PptFactorization
