import PptFactorization.AppendixBNormalizedExpectations

/-!
# Localized Levy on the concrete spherical model

This file specializes the abstract localized Levy reduction from
`AppendixB.lean` to the exact spherical law used by the random-matrix model:
the push-forward law of `G / ‖G‖₂`.

It does not hide the global Levy inequality on that spherical law.  The
localized statements below take the global concentration theorem as an
explicit theorem-level hypothesis, because the project and current mathlib do
not yet contain the isoperimetric/concentration theorem for the uniform
Hilbert--Schmidt sphere.  Everything after that global theorem is wired to the
concrete model and the concrete good set.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal

noncomputable section

namespace PptFactorization
namespace AppendixB

open RandomMatrixModel GaussianModel HighProbabilityBounds

variable {p q σ : Type*}
variable [Fintype p] [Fintype q] [Fintype σ]
variable [DecidableEq p] [DecidableEq q]

/-- The exact spherical-law probability measure used in Appendix B. -/
abbrev sphericalModelMeasure : Measure (SampleMatrix p q σ) :=
  gaussianSphericalSampleMeasure (p := p) (q := q) (σ := σ)

omit [DecidableEq p] [DecidableEq q] in
/-- The spherical model measure is a probability measure. -/
theorem sphericalModelMeasure_isProbabilityMeasure :
    IsProbabilityMeasure
      (sphericalModelMeasure (p := p) (q := q) (σ := σ)) := by
  haveI : IsProbabilityMeasure (gaussianMeasure p q σ) := by
    rw [gaussianMeasure_eq]
    infer_instance
  exact Measure.isProbabilityMeasure_map
    (measurable_gaussianDirection (p := p) (q := q) (σ := σ)).aemeasurable

/-- The sample-operator good set on the exact spherical model. -/
def sphericalSampleOpNormGoodSet (a d : ℝ) :
    Set (SampleMatrix p q σ) :=
  {X | sampleOpNorm (p := p) (q := q) (σ := σ) X ≤ a / d}

/-- The partially-transposed-density good set on the exact spherical model. -/
def sphericalGammaOpNormGoodSet (b d : ℝ) :
    Set (SampleMatrix p q σ) :=
  {X | sphericalGammaOpNorm (p := p) (q := q) (σ := σ) X ≤ b / d ^ 2}

/-- The concrete Appendix B good set on the exact spherical model. -/
def sphericalOperatorNormGoodSet (a b d : ℝ) :
    Set (SampleMatrix p q σ) :=
  sphericalSampleOpNormGoodSet (p := p) (q := q) (σ := σ) a d ∩
    sphericalGammaOpNormGoodSet (p := p) (q := q) (σ := σ) b d

omit [DecidableEq p] [DecidableEq q] in
/-- Measurability of the sample-operator good set. -/
theorem measurableSet_sphericalSampleOpNormGoodSet (a d : ℝ) :
    MeasurableSet
      (sphericalSampleOpNormGoodSet (p := p) (q := q) (σ := σ) a d) := by
  exact measurableSet_le
    (sampleOpNorm_continuous (p := p) (q := q) (σ := σ)).measurable
    measurable_const

/-- Measurability of the Gamma good set. -/
theorem measurableSet_sphericalGammaOpNormGoodSet (b d : ℝ) :
    MeasurableSet
      (sphericalGammaOpNormGoodSet (p := p) (q := q) (σ := σ) b d) := by
  exact measurableSet_le
    (continuous_sphericalGammaOpNorm (p := p) (q := q) (σ := σ)).measurable
    measurable_const

/-- Measurability of the concrete Appendix B spherical good set. -/
theorem measurableSet_sphericalOperatorNormGoodSet (a b d : ℝ) :
    MeasurableSet
      (sphericalOperatorNormGoodSet (p := p) (q := q) (σ := σ) a b d) := by
  exact
    (measurableSet_sphericalSampleOpNormGoodSet
      (p := p) (q := q) (σ := σ) a d).inter
      (measurableSet_sphericalGammaOpNormGoodSet
        (p := p) (q := q) (σ := σ) b d)

omit [DecidableEq p] [DecidableEq q] in
/-- Localized Levy reduction instantiated on the exact spherical model, with
an arbitrary measurable good set. -/
theorem spherical_localized_levy_reduction_exact_model
    {A : Set (SampleMatrix p q σ)} {f : SampleMatrix p q σ → ℝ}
    {L n t Mf : ℝ}
    (ht : 0 < t)
    (hL : 0 ≤ L)
    (hLip :
      _root_.AppendixB.LipschitzOn
        (fun X Y : SampleMatrix p q σ => dist X Y) A f L)
    (hMf :
      _root_.AppendixB.IsMedian
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)) f Mf)
    (hGlobalLevy :
      ∀ {g : SampleMatrix p q σ → ℝ} {K : ℝ≥0},
        LipschitzWith K g →
        ∀ {u : ℝ}, 0 < u →
          ∃ Mg,
            _root_.AppendixB.IsMedian
              (sphericalModelMeasure (p := p) (q := q) (σ := σ)) g Mg ∧
              (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
                  {X | u ≤ |g X - Mg|} ≤
                2 * Real.exp (-(n * u ^ 2 / (4 * K ^ 2)))) :
    (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
        {X | t ≤ |f X - Mf|} ≤
      2 *
          (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real Aᶜ +
        4 * Real.exp (-(n * t ^ 2 / (16 * L ^ 2))) := by
  haveI :
      IsProbabilityMeasure
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)) :=
    sphericalModelMeasure_isProbabilityMeasure (p := p) (q := q) (σ := σ)
  exact _root_.AppendixB.localized_levy_lemma_reduction
    (μ := sphericalModelMeasure (p := p) (q := q) (σ := σ))
    (A := A) (h := f) (L := L) (n := n) (t := t) (Mh := Mf)
    ht hL hLip hMf hGlobalLevy

omit [DecidableEq p] [DecidableEq q] in
/-- Localized Levy reduction on the exact spherical model, using the
McShane extension followed by clipping to a prescribed interval.

This is the fully instantiated extension step used in the appendix: a function
that is locally Lipschitz and bounded on the good set is extended to the whole
sphere without increasing its Lipschitz constant and without leaving the same
range.  The only theorem-level input that remains is the genuinely global
spherical Levy inequality for globally Lipschitz maps. -/
theorem spherical_localized_levy_reduction_exact_model_clipped
    {A : Set (SampleMatrix p q σ)} {f : SampleMatrix p q σ → ℝ}
    {L n t Mf low high : ℝ}
    (ht : 0 < t)
    (hL : 0 ≤ L)
    (hlowhigh : low ≤ high)
    (hLip :
      _root_.AppendixB.LipschitzOn
        (fun X Y : SampleMatrix p q σ => dist X Y) A f L)
    (hRange : ∀ X ∈ A, f X ∈ Set.Icc low high)
    (hMf :
      _root_.AppendixB.IsMedian
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)) f Mf)
    (hGlobalLevy :
      ∀ {g : SampleMatrix p q σ → ℝ} {K : ℝ≥0},
        LipschitzWith K g →
        ∀ {u : ℝ}, 0 < u →
          ∃ Mg,
            _root_.AppendixB.IsMedian
              (sphericalModelMeasure (p := p) (q := q) (σ := σ)) g Mg ∧
              (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
                  {X | u ≤ |g X - Mg|} ≤
                2 * Real.exp (-(n * u ^ 2 / (4 * K ^ 2)))) :
    (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
        {X | t ≤ |f X - Mf|} ≤
      2 *
          (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real Aᶜ +
        4 * Real.exp (-(n * t ^ 2 / (16 * L ^ 2))) := by
  haveI :
      IsProbabilityMeasure
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)) :=
    sphericalModelMeasure_isProbabilityMeasure (p := p) (q := q) (σ := σ)
  let K : ℝ≥0 := ⟨L, hL⟩
  have hLipK :
      _root_.AppendixB.LipschitzOn
        (fun X Y : SampleMatrix p q σ => dist X Y) A f K := by
    simpa [K] using hLip
  rcases _root_.AppendixB.mcShane_extension_clip
      (α := SampleMatrix p q σ) (Ω := A) (f := f) (K := K)
      (a := low) (b := high) hLipK hlowhigh hRange with
    ⟨H, hHlip, hHA, _hHrange⟩
  have htHalf : 0 < t / 2 := by positivity
  rcases hGlobalLevy hHlip htHalf with ⟨MH, hMH, hTailH⟩
  have hsubset :
      {X | t / 2 ≤ |f X - MH|} ⊆
        Aᶜ ∪ {X | t / 2 ≤ |H X - MH|} := by
    intro X hX
    by_cases hXA : X ∈ A
    · right
      simpa [hHA X hXA] using hX
    · left
      exact hXA
  have hTailAroundExtension :
      (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
          {X | t / 2 ≤ |f X - MH|} ≤
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real Aᶜ +
          2 * Real.exp (-(n * (t / 2) ^ 2 / (4 * K ^ 2))) := by
    calc
      (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
          {X | t / 2 ≤ |f X - MH|} ≤
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
          (Aᶜ ∪ {X | t / 2 ≤ |H X - MH|}) := by
          exact measureReal_mono hsubset
            (h₂ := (measure_lt_top
              (sphericalModelMeasure (p := p) (q := q) (σ := σ)) _).ne)
      _ ≤ (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real Aᶜ +
          (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
            {X | t / 2 ≤ |H X - MH|} := by
          exact measureReal_union_le _ _
      _ ≤ (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real Aᶜ +
          2 * Real.exp (-(n * (t / 2) ^ 2 / (4 * K ^ 2))) := by
          gcongr
  have hMedianCompare :
      (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
          {X | t ≤ |f X - Mf|} ≤
        2 *
          (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
            {X | t / 2 ≤ |f X - MH|} :=
    _root_.AppendixB.median_tail_le_two_tail_about_any_center
      (μ := sphericalModelMeasure (p := p) (q := q) (σ := σ))
      (f := f) (m := Mf) (a := MH) (t := t) hMf
  calc
    (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
        {X | t ≤ |f X - Mf|} ≤
      2 *
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
          {X | t / 2 ≤ |f X - MH|} := hMedianCompare
    _ ≤ 2 *
        ((sphericalModelMeasure (p := p) (q := q) (σ := σ)).real Aᶜ +
          2 * Real.exp (-(n * (t / 2) ^ 2 / (4 * K ^ 2)))) := by
        gcongr
    _ = 2 *
          (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real Aᶜ +
        4 * Real.exp (-(n * t ^ 2 / (16 * L ^ 2))) := by
        have hKsq : (K : ℝ) ^ 2 = L ^ 2 := by rfl
        rw [hKsq]
        ring_nf

/-- Localized Levy on the concrete Appendix B spherical good set. -/
theorem spherical_localized_levy_exact_good_set
    {f : SampleMatrix p q σ → ℝ}
    {a b d L n t Mf : ℝ}
    (ht : 0 < t)
    (hL : 0 ≤ L)
    (hLip :
      _root_.AppendixB.LipschitzOn
        (fun X Y : SampleMatrix p q σ => dist X Y)
        (sphericalOperatorNormGoodSet (p := p) (q := q) (σ := σ) a b d)
        f L)
    (hMf :
      _root_.AppendixB.IsMedian
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)) f Mf)
    (hGlobalLevy :
      ∀ {g : SampleMatrix p q σ → ℝ} {K : ℝ≥0},
        LipschitzWith K g →
        ∀ {u : ℝ}, 0 < u →
          ∃ Mg,
            _root_.AppendixB.IsMedian
              (sphericalModelMeasure (p := p) (q := q) (σ := σ)) g Mg ∧
              (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
                  {X | u ≤ |g X - Mg|} ≤
                2 * Real.exp (-(n * u ^ 2 / (4 * K ^ 2)))) :
    (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
        {X | t ≤ |f X - Mf|} ≤
      2 *
          (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
            (sphericalOperatorNormGoodSet
              (p := p) (q := q) (σ := σ) a b d)ᶜ +
        4 * Real.exp (-(n * t ^ 2 / (16 * L ^ 2))) := by
  exact spherical_localized_levy_reduction_exact_model
    (p := p) (q := q) (σ := σ)
    (A := sphericalOperatorNormGoodSet (p := p) (q := q) (σ := σ) a b d)
    (f := f) (L := L) (n := n) (t := t) (Mf := Mf)
    ht hL hLip hMf hGlobalLevy

/-- Localized Levy on the exact spherical model with the bad-set mass replaced
by an explicit scalar upper bound. -/
theorem spherical_localized_levy_exact_good_set_with_bad_bound
    {f : SampleMatrix p q σ → ℝ}
    {a b d L n t Mf bad : ℝ}
    (ht : 0 < t)
    (hL : 0 ≤ L)
    (hLip :
      _root_.AppendixB.LipschitzOn
        (fun X Y : SampleMatrix p q σ => dist X Y)
        (sphericalOperatorNormGoodSet (p := p) (q := q) (σ := σ) a b d)
        f L)
    (hMf :
      _root_.AppendixB.IsMedian
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)) f Mf)
    (hGlobalLevy :
      ∀ {g : SampleMatrix p q σ → ℝ} {K : ℝ≥0},
        LipschitzWith K g →
        ∀ {u : ℝ}, 0 < u →
          ∃ Mg,
            _root_.AppendixB.IsMedian
              (sphericalModelMeasure (p := p) (q := q) (σ := σ)) g Mg ∧
              (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
                  {X | u ≤ |g X - Mg|} ≤
                2 * Real.exp (-(n * u ^ 2 / (4 * K ^ 2))))
    (hBad :
      (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
          (sphericalOperatorNormGoodSet
            (p := p) (q := q) (σ := σ) a b d)ᶜ ≤ bad) :
    (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
        {X | t ≤ |f X - Mf|} ≤
      2 * bad + 4 * Real.exp (-(n * t ^ 2 / (16 * L ^ 2))) := by
  have hBase := spherical_localized_levy_exact_good_set
    (p := p) (q := q) (σ := σ) (f := f)
    (a := a) (b := b) (d := d) (L := L) (n := n) (t := t) (Mf := Mf)
    ht hL hLip hMf hGlobalLevy
  nlinarith [hBase, hBad]

/-- Pointwise local tail bound on the exact spherical model, in the form
needed by the layer-cake integral lemma. -/
theorem spherical_localized_tail_pointwise_exact_good_set
    {f : SampleMatrix p q σ → ℝ}
    {a b d L n Mf bad range : ℝ}
    (hL : 0 ≤ L)
    (hLip :
      _root_.AppendixB.LipschitzOn
        (fun X Y : SampleMatrix p q σ => dist X Y)
        (sphericalOperatorNormGoodSet (p := p) (q := q) (σ := σ) a b d)
        f L)
    (hMf :
      _root_.AppendixB.IsMedian
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)) f Mf)
    (hGlobalLevy :
      ∀ {g : SampleMatrix p q σ → ℝ} {K : ℝ≥0},
        LipschitzWith K g →
        ∀ {u : ℝ}, 0 < u →
          ∃ Mg,
            _root_.AppendixB.IsMedian
              (sphericalModelMeasure (p := p) (q := q) (σ := σ)) g Mg ∧
              (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
                  {X | u ≤ |g X - Mg|} ≤
                2 * Real.exp (-(n * u ^ 2 / (4 * K ^ 2))))
    (hBad :
      (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
          (sphericalOperatorNormGoodSet
            (p := p) (q := q) (σ := σ) a b d)ᶜ ≤ bad) :
    ∀ ⦃u : ℝ⦄, u ∈ Set.Ioc 0 range →
      (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
          {X | u ≤ |f X - Mf|} ≤
        2 * bad + 4 * Real.exp (-(n * u ^ 2 / (16 * L ^ 2))) := by
  intro u hu
  exact spherical_localized_levy_exact_good_set_with_bad_bound
    (p := p) (q := q) (σ := σ) (f := f)
    (a := a) (b := b) (d := d) (L := L) (n := n) (t := u)
    (Mf := Mf) (bad := bad)
    hu.1 hL hLip hMf hGlobalLevy hBad

/-- The localized tail integral on the exact spherical model.  This removes
the raw `hTailIntegral` once the local Lipschitz estimate, the bad-set bound,
and the explicit global spherical Levy theorem is available. -/
theorem spherical_localized_tail_integral_bound_exact_good_set
    {f : SampleMatrix p q σ → ℝ}
    {a b d L n Mf bad range : ℝ}
    (hRange : 0 ≤ range)
    (hL : 0 < L)
    (hn : 0 < n)
    (hLip :
      _root_.AppendixB.LipschitzOn
        (fun X Y : SampleMatrix p q σ => dist X Y)
        (sphericalOperatorNormGoodSet (p := p) (q := q) (σ := σ) a b d)
        f L)
    (hMf :
      _root_.AppendixB.IsMedian
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)) f Mf)
    (hGlobalLevy :
      ∀ {g : SampleMatrix p q σ → ℝ} {K : ℝ≥0},
        LipschitzWith K g →
        ∀ {u : ℝ}, 0 < u →
          ∃ Mg,
            _root_.AppendixB.IsMedian
              (sphericalModelMeasure (p := p) (q := q) (σ := σ)) g Mg ∧
              (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
                  {X | u ≤ |g X - Mg|} ≤
                2 * Real.exp (-(n * u ^ 2 / (4 * K ^ 2))))
    (hBad :
      (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
          (sphericalOperatorNormGoodSet
            (p := p) (q := q) (σ := σ) a b d)ᶜ ≤ bad) :
    ∫ u in Set.Ioc 0 range,
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
          {X | u ≤ |f X - Mf|} ≤
      _root_.AppendixB.localizedTailIntegralBound range bad L n := by
  haveI :
      IsProbabilityMeasure
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)) :=
    sphericalModelMeasure_isProbabilityMeasure (p := p) (q := q) (σ := σ)
  exact _root_.AppendixB.localized_tail_integral_bound
    (μ := sphericalModelMeasure (p := p) (q := q) (σ := σ))
    (f := f) (median := Mf) (range := range) (bad := bad)
    (L := L) (n := n)
    hRange hL hn
    (spherical_localized_tail_pointwise_exact_good_set
      (p := p) (q := q) (σ := σ) (f := f)
      (a := a) (b := b) (d := d) (L := L) (n := n)
      (Mf := Mf) (bad := bad) (range := range)
      hL.le hLip hMf hGlobalLevy hBad)

/-- The exponent naturally produced by the localized Levy reduction after the
McShane extension and median comparison. -/
noncomputable def localizedReductionExponent (n t L : ℝ) : ℝ :=
  n * t ^ 2 / (16 * L ^ 2)

omit [DecidableEq p] [DecidableEq q] in
/-- No-input Levy-shaped tail bound on the concrete spherical model in the
small-exponent regime.

This is intentionally weaker than the genuine spherical Levy lemma: it uses
only that the spherical model is a probability measure.  It is nevertheless a
compiled, non-vacuous no-input branch with the same exponential shape whenever
the requested exponent is at most `log 4`. -/
theorem spherical_noInput_levy_tail_small_exponent
    {f : SampleMatrix p q σ → ℝ}
    {center n t L : ℝ}
    (hExponent : localizedReductionExponent n t L ≤ Real.log 4) :
    (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
        {X | t ≤ |f X - center|} ≤
      4 * Real.exp (-(localizedReductionExponent n t L)) := by
  haveI :
      IsProbabilityMeasure
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)) :=
    sphericalModelMeasure_isProbabilityMeasure (p := p) (q := q) (σ := σ)
  exact (_root_.AppendixB.probability_event_real_le_one
    (μ := sphericalModelMeasure (p := p) (q := q) (σ := σ))
    {X | t ≤ |f X - center|}).trans
      (_root_.AppendixB.one_le_four_exp_neg_of_le_log_four hExponent)

/-- No-input localized Levy shape on the exact spherical good set, valid in
the small-exponent regime.

The proof does not use local Lipschitzness or spherical isoperimetry; the
bad-set term is kept so that the conclusion has the same shape as the genuine
localized Levy reduction. -/
theorem spherical_localized_levy_exact_good_set_small_exponent_noInput
    {f : SampleMatrix p q σ → ℝ}
    {a b d L n t Mf : ℝ}
    (hExponent : localizedReductionExponent n t L ≤ Real.log 4) :
    (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
        {X | t ≤ |f X - Mf|} ≤
      2 *
          (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
            (sphericalOperatorNormGoodSet
              (p := p) (q := q) (σ := σ) a b d)ᶜ +
        4 * Real.exp (-(localizedReductionExponent n t L)) := by
  have hTail := spherical_noInput_levy_tail_small_exponent
    (p := p) (q := q) (σ := σ) (f := f)
    (center := Mf) (n := n) (t := t) (L := L) hExponent
  have hBadNonneg :
      0 ≤
        2 *
          (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
            (sphericalOperatorNormGoodSet
              (p := p) (q := q) (σ := σ) a b d)ᶜ := by
    positivity
  linarith

/-- Scalar-bad-set version of the no-input small-exponent localized Levy
branch. -/
theorem spherical_localized_levy_exact_good_set_with_bad_bound_small_exponent_noInput
    {f : SampleMatrix p q σ → ℝ}
    {a b d L n t Mf bad : ℝ}
    (hExponent : localizedReductionExponent n t L ≤ Real.log 4)
    (hBad :
      (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
          (sphericalOperatorNormGoodSet
            (p := p) (q := q) (σ := σ) a b d)ᶜ ≤ bad) :
    (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
        {X | t ≤ |f X - Mf|} ≤
      2 * bad + 4 * Real.exp (-(localizedReductionExponent n t L)) := by
  have hTail := spherical_noInput_levy_tail_small_exponent
    (p := p) (q := q) (σ := σ) (f := f)
    (center := Mf) (n := n) (t := t) (L := L) hExponent
  have hBadNonneg : 0 ≤ bad := by
    have hMeasureNonneg :
        0 ≤
          (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
            (sphericalOperatorNormGoodSet
              (p := p) (q := q) (σ := σ) a b d)ᶜ := by
      positivity
    exact hMeasureNonneg.trans hBad
  nlinarith

/-- Scale comparison for the localized-Levy reduction exponent.

Compared with `target_exponent_le_from_half_exact_scales` in `AppendixB.lean`,
this uses the actual exponent produced by the localized reduction, whose
denominator is `16 * L^2` rather than `4 * L^2`.  This accounts for the extra
factor `4` in the constant `cDim / (64 C^2)`. -/
theorem target_exponent_le_from_half_exact_scales_localized_reduction
    {cDim C cLocal d eps momentParameter : ℝ} {r : ℕ}
    (hd : d ≠ 0)
    (hC : C ≠ 0)
    (hk : momentParameter ≠ 0)
    (hcLocal : cLocal ≤ cDim / (64 * C ^ 2)) :
    _root_.AppendixB.targetLocalExponent cLocal d eps momentParameter ≤
      localizedReductionExponent
        (cDim * d ^ 4)
        (_root_.AppendixB.naturalDeviationScale d eps r / 2)
        (_root_.AppendixB.localLipschitzScale C momentParameter d r) := by
  unfold _root_.AppendixB.targetLocalExponent localizedReductionExponent
    _root_.AppendixB.naturalDeviationScale _root_.AppendixB.localLipschitzScale
  let q : ℝ := d ^ (2 * r - 2)
  have hq : q ≠ 0 := by
    dsimp [q]
    exact pow_ne_zero _ hd
  have hEq :
      (cDim * d ^ 4) * ((eps / q) / 2) ^ 2 /
          (16 * (C * momentParameter / q) ^ 2) =
        (cDim / (64 * C ^ 2)) * d ^ 4 * eps ^ 2 / momentParameter ^ 2 := by
    field_simp [hq, hC, hk]
    ring
  have hscale : 0 ≤ d ^ 4 * eps ^ 2 / momentParameter ^ 2 := by
    positivity
  have hmul := mul_le_mul_of_nonneg_right hcLocal hscale
  calc
    cLocal * d ^ 4 * eps ^ 2 / momentParameter ^ 2
        = cLocal * (d ^ 4 * eps ^ 2 / momentParameter ^ 2) := by ring
    _ ≤ (cDim / (64 * C ^ 2)) *
        (d ^ 4 * eps ^ 2 / momentParameter ^ 2) := hmul
    _ = (cDim * d ^ 4) * ((eps / q) / 2) ^ 2 /
          (16 * (C * momentParameter / q) ^ 2) := by
        rw [hEq]
        ring

/-- Median-to-mean passage on the exact spherical model, with the tail
integral supplied by the localized Levy bound rather than as an external
hypothesis. -/
theorem spherical_mean_tail_le_median_tail_from_localized_levy_exact_good_set
    {f : SampleMatrix p q σ → ℝ}
    {mean median scale range bad a b d L n : ℝ}
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
    (hL : 0 < L)
    (hn : 0 < n)
    (hLip :
      _root_.AppendixB.LipschitzOn
        (fun X Y : SampleMatrix p q σ => dist X Y)
        (sphericalOperatorNormGoodSet (p := p) (q := q) (σ := σ) a b d)
        f L)
    (hMedian :
      _root_.AppendixB.IsMedian
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)) f median)
    (hGlobalLevy :
      ∀ {g : SampleMatrix p q σ → ℝ} {K : ℝ≥0},
        LipschitzWith K g →
        ∀ {u : ℝ}, 0 < u →
          ∃ Mg,
            _root_.AppendixB.IsMedian
              (sphericalModelMeasure (p := p) (q := q) (σ := σ)) g Mg ∧
              (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
                  {X | u ≤ |g X - Mg|} ≤
                2 * Real.exp (-(n * u ^ 2 / (4 * K ^ 2))))
    (hBad :
      (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
          (sphericalOperatorNormGoodSet
            (p := p) (q := q) (σ := σ) a b d)ᶜ ≤ bad)
    (hSmall :
      _root_.AppendixB.localizedTailIntegralBound range bad L n ≤ scale / 2) :
    (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
        {X | scale ≤ |f X - mean|} ≤
      (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
        {X | scale / 2 ≤ |f X - median|} := by
  haveI :
      IsProbabilityMeasure
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)) :=
    sphericalModelMeasure_isProbabilityMeasure (p := p) (q := q) (σ := σ)
  have hTailIntegral :
      ∫ u in Set.Ioc 0 range,
          (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
            {X | u ≤ |f X - median|} ≤ scale / 2 :=
    (spherical_localized_tail_integral_bound_exact_good_set
      (p := p) (q := q) (σ := σ) (f := f)
      (a := a) (b := b) (d := d) (L := L) (n := n)
      (Mf := median) (bad := bad) (range := range)
      hRangeNonneg hL hn hLip hMedian hGlobalLevy hBad).trans hSmall
  exact _root_.AppendixB.mean_tail_probability_le_median_tail_probability_from_integrated_tail
    (μ := sphericalModelMeasure (p := p) (q := q) (σ := σ))
    (f := f) (mean := mean) (median := median)
    (scale := scale) (range := range)
    hmean hf hRange hTailIntegral

/-- Final spherical-model concentration wrapper with the median-to-mean shift
and its tail integration internalized.

The hypotheses now sit at the intended level:

* local Lipschitz control on the exact spherical good set,
* the explicit global Levy theorem for the exact spherical law,
* a bad-set bound for that good set,
* the explicit smallness check for the integrated localized tail.
-/
theorem spherical_paper_concentration_from_localized_levy_exact_good_set
    {f : SampleMatrix p q σ → ℝ}
    {mean median range bad a b C cDim cSphere cLocal d eps
      momentParameter K : ℝ}
    {r : ℕ}
    (hd : d ≠ 0)
    (hC : C ≠ 0)
    (hk : momentParameter ≠ 0)
    (hcLocal : cLocal ≤ cDim / (64 * C ^ 2))
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
    (hGlobalLevy :
      ∀ {g : SampleMatrix p q σ → ℝ} {K : ℝ≥0},
        LipschitzWith K g →
        ∀ {u : ℝ}, 0 < u →
          ∃ Mg,
            _root_.AppendixB.IsMedian
              (sphericalModelMeasure (p := p) (q := q) (σ := σ)) g Mg ∧
              (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
                  {X | u ≤ |g X - Mg|} ≤
                2 * Real.exp (-((cDim * d ^ 4) * u ^ 2 / (4 * K ^ 2))))
    (hBad :
      (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
          (sphericalOperatorNormGoodSet
            (p := p) (q := q) (σ := σ) a b d)ᶜ ≤ bad)
    (hGood : bad ≤ 2 * _root_.AppendixB.goodSetTail cSphere d)
    (hK : 4 ≤ K) :
    (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
        {X | _root_.AppendixB.naturalDeviationScale d eps r ≤ |f X - mean|} ≤
      _root_.AppendixB.paperTailBound K cSphere cLocal d eps momentParameter := by
  let scale := _root_.AppendixB.naturalDeviationScale d eps r
  let L := _root_.AppendixB.localLipschitzScale C momentParameter d r
  let nEff := cDim * d ^ 4
  let μ := sphericalModelMeasure (p := p) (q := q) (σ := σ)
  have hShift :
      μ.real {X | scale ≤ |f X - mean|} ≤
        μ.real {X | scale / 2 ≤ |f X - median|} := by
    exact spherical_mean_tail_le_median_tail_from_localized_levy_exact_good_set
      (p := p) (q := q) (σ := σ) (f := f)
      (mean := mean) (median := median) (scale := scale)
      (range := range) (bad := bad) (a := a) (b := b) (d := d)
      (L := L) (n := nEff)
      hmean hf hRange hRangeNonneg hL hn hLip hMedian hGlobalLevy hBad hSmall
  have hMedianTail :
      μ.real {X | scale / 2 ≤ |f X - median|} ≤
        2 * bad +
          4 * Real.exp (-(localizedReductionExponent nEff (scale / 2) L)) := by
    have ht : 0 < scale / 2 := by
      dsimp [scale]
      positivity
    simpa [μ, scale, L, nEff, localizedReductionExponent] using
      spherical_localized_levy_exact_good_set_with_bad_bound
        (p := p) (q := q) (σ := σ) (f := f)
        (a := a) (b := b) (d := d) (L := L) (n := nEff)
        (t := scale / 2) (Mf := median) (bad := bad)
        ht hL.le hLip hMedian hGlobalLevy hBad
  have hExponent :
      _root_.AppendixB.targetLocalExponent cLocal d eps momentParameter ≤
        localizedReductionExponent nEff (scale / 2) L := by
    simpa [scale, L, nEff] using
      target_exponent_le_from_half_exact_scales_localized_reduction
        (cDim := cDim) (C := C) (cLocal := cLocal) (d := d)
        (eps := eps) (momentParameter := momentParameter) (r := r)
        hd hC hk hcLocal
  have hExp :
      Real.exp (-(localizedReductionExponent nEff (scale / 2) L)) ≤
        Real.exp
          (-(_root_.AppendixB.targetLocalExponent cLocal d eps momentParameter)) := by
    exact (Real.exp_le_exp).2 (by linarith)
  have hExpMul :
      4 * Real.exp (-(localizedReductionExponent nEff (scale / 2) L)) ≤
        4 *
          Real.exp
            (-(_root_.AppendixB.targetLocalExponent cLocal d eps momentParameter)) :=
    mul_le_mul_of_nonneg_left hExp (by norm_num)
  have hMedianTarget :
      μ.real {X | scale / 2 ≤ |f X - median|} ≤
        4 * _root_.AppendixB.goodSetTail cSphere d +
          4 *
            Real.exp
              (-(_root_.AppendixB.targetLocalExponent cLocal d eps momentParameter)) := by
    calc
      μ.real {X | scale / 2 ≤ |f X - median|} ≤
          2 * bad +
            4 * Real.exp (-(localizedReductionExponent nEff (scale / 2) L)) :=
            hMedianTail
      _ ≤ 2 * (2 * _root_.AppendixB.goodSetTail cSphere d) +
            4 *
              Real.exp
                (-(_root_.AppendixB.targetLocalExponent cLocal d eps momentParameter)) := by
            nlinarith
      _ = 4 * _root_.AppendixB.goodSetTail cSphere d +
            4 *
              Real.exp
                (-(_root_.AppendixB.targetLocalExponent cLocal d eps momentParameter)) := by
            ring
  have hMeanTarget :
      μ.real {X | scale ≤ |f X - mean|} ≤
        4 * _root_.AppendixB.goodSetTail cSphere d +
          4 *
            Real.exp
              (-(_root_.AppendixB.targetLocalExponent cLocal d eps momentParameter)) :=
    hShift.trans hMedianTarget
  have hE₁ : 0 ≤ _root_.AppendixB.goodSetTail cSphere d :=
    le_of_lt (Real.exp_pos _)
  have hE₂ :
      0 ≤
        Real.exp
          (-(_root_.AppendixB.targetLocalExponent cLocal d eps momentParameter)) :=
    le_of_lt (Real.exp_pos _)
  have hAbsorb :
      4 * _root_.AppendixB.goodSetTail cSphere d +
          4 *
            Real.exp
              (-(_root_.AppendixB.targetLocalExponent cLocal d eps momentParameter)) ≤
        _root_.AppendixB.paperTailBound K cSphere cLocal d eps momentParameter := by
    dsimp [_root_.AppendixB.paperTailBound]
    have hFirst :
        4 * _root_.AppendixB.goodSetTail cSphere d ≤
          K * _root_.AppendixB.goodSetTail cSphere d :=
      mul_le_mul_of_nonneg_right hK hE₁
    have hSecond :
        4 *
            Real.exp
              (-(_root_.AppendixB.targetLocalExponent cLocal d eps momentParameter)) ≤
          K *
            Real.exp
              (-(_root_.AppendixB.targetLocalExponent cLocal d eps momentParameter)) :=
      mul_le_mul_of_nonneg_right hK hE₂
    linarith
  simpa [μ, scale] using hMeanTarget.trans hAbsorb

end AppendixB
end PptFactorization
