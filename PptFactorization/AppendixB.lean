import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-!
# Appendix B: local Lipschitz concentration

This file formalises the quantitative skeleton of Appendix B.

The genuinely analytic inputs of the appendix are kept as explicit hypotheses:

* the primitive deterministic matrix inequalities behind the trace-power
  perturbation estimate,
* the norm estimates defining the good set and the matrix difference,
* the local Levy lemma on the Hilbert--Schmidt sphere,
* the one-dimensional integral estimate obtained from the localized tail.

The formalized part covers the deterministic Lipschitz reduction from those
matrix inequalities, the union bound for the good set, the conversion of the
Levy exponent into the `d^4 ε^2 / k^2` scale, the median tail bound, and the
quantitative replacement of the median by the mean.  The file also contains a
Frobenius/operator-norm deterministic interface, including the telescoping
finite-sum step, so the paper proof does not need a separate trace-norm API.
It also contains a final two-branch wrapper for the large-deviation versus
small-deviation step.
-/

namespace AppendixB

open MeasureTheory
open scoped BigOperators
open scoped NNReal

/-! ## Local Lipschitz bookkeeping -/

variable {α : Type*}

/-- A real-valued map is `L`-Lipschitz on a good set `Ω`.

The distance is kept abstract because Appendix B works on the real
Hilbert--Schmidt sphere, while the proof only uses the resulting distance
inequalities. -/
def LipschitzOn (dist : α → α → ℝ) (Ω : Set α) (f : α → ℝ) (L : ℝ) : Prop :=
  ∀ ⦃x y : α⦄, x ∈ Ω → y ∈ Ω → |f x - f y| ≤ L * dist x y

/-- If a Lipschitz constant is enlarged, the local Lipschitz property is
preserved. This is the formal version of replacing the deterministic bound by
the cleaner scale `C(k,λ) k / d^(2k-2)`. -/
lemma LipschitzOn.mono_constant
    {dist : α → α → ℝ} {Ω : Set α} {f : α → ℝ} {L L' : ℝ}
    (hdist : ∀ ⦃x y : α⦄, x ∈ Ω → y ∈ Ω → 0 ≤ dist x y)
    (hL : L ≤ L') (hf : LipschitzOn dist Ω f L) :
    LipschitzOn dist Ω f L' := by
  intro x y hx hy
  calc
    |f x - f y| ≤ L * dist x y := hf hx hy
    _ ≤ L' * dist x y := mul_le_mul_of_nonneg_right hL (hdist hx hy)

/-- McShane extension, packaged in the appendix's `LipschitzOn` notation.

This is the standard real-valued extension theorem, specialized to a
nonnegative Lipschitz constant and the ambient metric distance. -/
theorem mcShane_extension_real
    [PseudoMetricSpace α] {Ω : Set α} {f : α → ℝ} {K : ℝ≥0}
    (hf : LipschitzOn (fun x y : α => dist x y) Ω f K) :
    ∃ g : α → ℝ, LipschitzWith K g ∧ ∀ x ∈ Ω, f x = g x := by
  have hf' : LipschitzOnWith K f Ω := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro x hx y hy
    simpa [Real.dist_eq] using hf hx hy
  rcases hf'.extend_real with ⟨g, hg, hEq⟩
  exact ⟨g, hg, hEq⟩

/-- Clipping a real-valued Lipschitz map to a closed interval does not increase
its Lipschitz constant. -/
theorem clip_interval_lipschitz
    [PseudoMetricSpace α] {f : α → ℝ} {K : ℝ≥0} {a b : ℝ}
    (hf : LipschitzWith K f) :
    LipschitzWith K (fun x => max a (min (f x) b)) := by
  simpa using (hf.min_const b).const_max a

/-- McShane extension followed by clipping to a closed interval.

This is the version used in the high-probability arguments when a local
Lipschitz function must first be extended to the whole ambient space and then
forced into a prescribed range without changing the Lipschitz constant. -/
theorem mcShane_extension_clip
    [PseudoMetricSpace α] {Ω : Set α} {f : α → ℝ} {K : ℝ≥0} {a b : ℝ}
    (hf : LipschitzOn (fun x y : α => dist x y) Ω f K) (hab : a ≤ b)
    (hbound : ∀ x ∈ Ω, f x ∈ Set.Icc a b) :
    ∃ g : α → ℝ, LipschitzWith K g ∧
      (∀ x ∈ Ω, f x = g x) ∧
      ∀ x, g x ∈ Set.Icc a b := by
  rcases mcShane_extension_real (Ω := Ω) (f := f) (K := K) hf with
    ⟨g, hg, hEq⟩
  refine ⟨fun x => max a (min (g x) b), ?_, ?_, ?_⟩
  · exact clip_interval_lipschitz (f := g) (K := K) (a := a) (b := b) hg
  · intro x hx
    have h1 : f x = max a (min (f x) b) := by
      rcases hbound x hx with ⟨ha, hb'⟩
      simp [ha, hb']
    rw [h1]
    simp [hEq x hx]
  · intro x
    constructor
    · exact le_max_left _ _
    · exact max_le_iff.mpr ⟨hab, min_le_right _ _⟩

/-- A real number `m` is a median of `f` under `μ` if each half-line through
`m` carries probability at least `1/2`. -/
def IsMedian {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (m : ℝ) : Prop :=
  (1 / 2 : ℝ) ≤ μ.real {ω | f ω ≤ m} ∧
    (1 / 2 : ℝ) ≤ μ.real {ω | m ≤ f ω}

/-- If a median is at distance at least `t` from an arbitrary center `a`, then
the `t`-tail around `a` already has probability at least `1/2`. -/
lemma half_le_tail_about_center_of_median_far
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {m a t : ℝ}
    (hm : IsMedian μ f m) (hfar : t ≤ |m - a|) :
    (1 / 2 : ℝ) ≤ μ.real {ω | t ≤ |f ω - a|} := by
  rcases hm with ⟨hmLeft, hmRight⟩
  by_cases ham : a ≤ m
  · have hdist : t ≤ m - a := by
      simpa [abs_of_nonneg (sub_nonneg.mpr ham)] using hfar
    have hsubset : {ω | m ≤ f ω} ⊆ {ω | t ≤ |f ω - a|} := by
      intro ω hω
      change m ≤ f ω at hω
      have hnonneg : 0 ≤ f ω - a := sub_nonneg.mpr (le_trans ham hω)
      have hbound : t ≤ f ω - a := by
        calc
          t ≤ m - a := hdist
          _ ≤ f ω - a := sub_le_sub_right hω a
      simpa [abs_of_nonneg hnonneg] using hbound
    exact hmRight.trans <|
      measureReal_mono hsubset (h₂ := (measure_lt_top μ _).ne)
  · have hma : m ≤ a := le_of_not_ge ham
    have hdist : t ≤ a - m := by
      simpa [abs_of_nonpos (sub_nonpos.mpr hma)] using hfar
    have hsubset : {ω | f ω ≤ m} ⊆ {ω | t ≤ |f ω - a|} := by
      intro ω hω
      change f ω ≤ m at hω
      have hnonpos : f ω - a ≤ 0 := by
        linarith
      have hbound : t ≤ a - f ω := by
        calc
          t ≤ a - m := hdist
          _ ≤ a - f ω := sub_le_sub_left hω a
      have habs : |f ω - a| = a - f ω := by
        rw [abs_of_nonpos hnonpos]
        ring
      simpa [habs] using hbound
    exact hmLeft.trans <|
      measureReal_mono hsubset (h₂ := (measure_lt_top μ _).ne)

/-- Comparing a tail around a median to a tail around any other center costs at
most a factor `2`, with the radius halved. This is the elementary median
comparison used in the localized Levy argument. -/
lemma median_tail_le_two_tail_about_any_center
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {m a t : ℝ}
    (hm : IsMedian μ f m) :
    μ.real {ω | t ≤ |f ω - m|} ≤
      2 * μ.real {ω | t / 2 ≤ |f ω - a|} := by
  by_cases hnear : |m - a| < t / 2
  · have hsubset :
        {ω | t ≤ |f ω - m|} ⊆ {ω | t / 2 ≤ |f ω - a|} := by
          intro ω hω
          change t ≤ |f ω - m| at hω
          have htri : |f ω - m| ≤ |f ω - a| + |a - m| := by
            calc
              |f ω - m| = |(f ω - a) + (a - m)| := by ring_nf
              _ ≤ |f ω - a| + |a - m| := abs_add_le _ _
          have hnear' : |a - m| < t / 2 := by simpa [abs_sub_comm] using hnear
          have hstrict : t / 2 < |f ω - a| := by linarith
          exact le_of_lt hstrict
    calc
      μ.real {ω | t ≤ |f ω - m|} ≤ μ.real {ω | t / 2 ≤ |f ω - a|} :=
        measureReal_mono hsubset (h₂ := (measure_lt_top μ _).ne)
      _ ≤ 2 * μ.real {ω | t / 2 ≤ |f ω - a|} := by
        nlinarith [show 0 ≤ μ.real {ω | t / 2 ≤ |f ω - a|} by positivity]
  · have hhalf :
        (1 / 2 : ℝ) ≤ μ.real {ω | t / 2 ≤ |f ω - a|} :=
      half_le_tail_about_center_of_median_far
        (μ := μ) (f := f) (m := m) (a := a) (t := t / 2)
        hm (le_of_not_gt hnear)
    have hleft :
        μ.real {ω | t ≤ |f ω - m|} ≤ 1 := by
      calc
        μ.real {ω | t ≤ |f ω - m|} ≤ μ.real (Set.univ : Set Ω) :=
          measureReal_mono (Set.subset_univ _) (h₂ := (measure_lt_top μ _).ne)
        _ = 1 := by simp
    calc
      μ.real {ω | t ≤ |f ω - m|} ≤ 1 := hleft
      _ = 2 * (1 / 2 : ℝ) := by ring
      _ ≤ 2 * μ.real {ω | t / 2 ≤ |f ω - a|} := by nlinarith

/-- Localized Levy reduction.

This is the exact McShane-extension argument from the appendix.  It is
slightly stronger than the text as stated: the proof only uses the bad-set mass
`μ.real Ωᶜ`, not the auxiliary lower bound `μ(Ω) ≥ 3/4`.

The only external input is a global median-centered concentration theorem for
globally Lipschitz maps on the ambient probability space. -/
theorem localized_levy_lemma_reduction
    {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A : Set Ω} {h : Ω → ℝ} {L n t Mh : ℝ}
    (ht : 0 < t)
    (hL : 0 ≤ L)
    (hLip : LipschitzOn (fun x y : Ω => dist x y) A h L)
    (hMh : IsMedian μ h Mh)
    (hGlobalLevy :
      ∀ {g : Ω → ℝ} {K : ℝ≥0} (_hg : LipschitzWith K g) {u : ℝ},
        0 < u →
        ∃ Mg, IsMedian μ g Mg ∧
          μ.real {ω | u ≤ |g ω - Mg|} ≤
            2 * Real.exp (-(n * u ^ 2 / (4 * K ^ 2)))) :
    μ.real {ω | t ≤ |h ω - Mh|} ≤
      2 * μ.real Aᶜ + 4 * Real.exp (-(n * t ^ 2 / (16 * L ^ 2))) := by
  let K : ℝ≥0 := ⟨L, hL⟩
  have hLipK : LipschitzOn (fun x y : Ω => dist x y) A h K := by
    simpa [K] using hLip
  rcases mcShane_extension_real (Ω := A) (f := h) (K := K) hLipK with
    ⟨H, hHlip, hHA⟩
  have htHalf : 0 < t / 2 := by positivity
  rcases hGlobalLevy hHlip htHalf with ⟨MhH, hMhH, hTailH⟩
  have hsubset :
      {ω | t / 2 ≤ |h ω - MhH|} ⊆
        Aᶜ ∪ {ω | t / 2 ≤ |H ω - MhH|} := by
    intro ω hω
    by_cases hωA : ω ∈ A
    · right
      simpa [hHA ω hωA] using hω
    · left
      exact hωA
  have hTailAroundExtension :
      μ.real {ω | t / 2 ≤ |h ω - MhH|} ≤
        μ.real Aᶜ + 2 * Real.exp (-(n * (t / 2) ^ 2 / (4 * K ^ 2))) := by
    calc
      μ.real {ω | t / 2 ≤ |h ω - MhH|} ≤
          μ.real (Aᶜ ∪ {ω | t / 2 ≤ |H ω - MhH|}) :=
        measureReal_mono hsubset (h₂ := (measure_lt_top μ _).ne)
      _ ≤ μ.real Aᶜ + μ.real {ω | t / 2 ≤ |H ω - MhH|} := by
        exact measureReal_union_le _ _
      _ ≤ μ.real Aᶜ + 2 * Real.exp (-(n * (t / 2) ^ 2 / (4 * K ^ 2))) := by
        gcongr
  have hMedianCompare :
      μ.real {ω | t ≤ |h ω - Mh|} ≤
        2 * μ.real {ω | t / 2 ≤ |h ω - MhH|} :=
    median_tail_le_two_tail_about_any_center
      (μ := μ) (f := h) (m := Mh) (a := MhH) (t := t) hMh
  calc
    μ.real {ω | t ≤ |h ω - Mh|} ≤
        2 * μ.real {ω | t / 2 ≤ |h ω - MhH|} := hMedianCompare
    _ ≤ 2 * (μ.real Aᶜ + 2 * Real.exp (-(n * (t / 2) ^ 2 / (4 * K ^ 2)))) := by
          gcongr
    _ = 2 * μ.real Aᶜ + 4 * Real.exp (-(n * t ^ 2 / (16 * L ^ 2))) := by
          have hKsq : (K : ℝ) ^ 2 = L ^ 2 := by rfl
          rw [hKsq]
          ring_nf

/-- Text-shaped localized Levy lemma.

The hypothesis `μ.real A ≥ 3/4` is included to mirror the manuscript, even
though the reduction proof only needs the bad-set mass appearing explicitly in
the conclusion. -/
theorem localized_levy_lemma
    {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A : Set Ω} {h : Ω → ℝ} {L n t Mh : ℝ}
    (hA_meas : MeasurableSet A)
    (hA : (3 / 4 : ℝ) ≤ μ.real A)
    (ht : 0 < t)
    (hL : 0 ≤ L)
    (hLip : LipschitzOn (fun x y : Ω => dist x y) A h L)
    (hMh : IsMedian μ h Mh)
    (hGlobalLevy :
      ∀ {g : Ω → ℝ} {K : ℝ≥0} (_hg : LipschitzWith K g) {u : ℝ},
        0 < u →
        ∃ Mg, IsMedian μ g Mg ∧
          μ.real {ω | u ≤ |g ω - Mg|} ≤
            2 * Real.exp (-(n * u ^ 2 / (4 * K ^ 2)))) :
    μ.real {ω | t ≤ |h ω - Mh|} ≤
      2 * μ.real Aᶜ + 4 * Real.exp (-(n * t ^ 2 / (16 * L ^ 2))) := by
  have _hA_compl : μ.real Aᶜ ≤ 1 / 4 := by
    calc
      μ.real Aᶜ = 1 - μ.real A := by
        simpa using measureReal_compl (μ := μ) hA_meas
      _ ≤ 1 - 3 / 4 := by gcongr
      _ = 1 / 4 := by norm_num
  exact localized_levy_lemma_reduction
    (μ := μ) (A := A) (h := h) (L := L) (n := n) (t := t) (Mh := Mh)
    ht hL hLip hMh hGlobalLevy

/-! ## Deterministic matrix Lipschitz bookkeeping -/

variable {β : Type*}

/-- Deterministic Lipschitz conclusion from two local matrix estimates.

This is the abstract algebraic core used in Appendix B: if the trace-power
functional is controlled by a trace-norm difference, and that trace-norm
difference is controlled by the Hilbert--Schmidt distance, then the trace-power
functional is Lipschitz on the good set. -/
theorem deterministic_lipschitz_from_trace_and_difference_bounds
    [Ring β]
    {dist : α → α → ℝ} {Ω : Set α}
    {A : α → β} {tr traceNorm : β → ℝ}
    {k : ℕ} {traceCoeff diffCoeff L : ℝ}
    (hdist : ∀ ⦃x y : α⦄, x ∈ Ω → y ∈ Ω → 0 ≤ dist x y)
    (hTrace :
      ∀ ⦃x y : α⦄, x ∈ Ω → y ∈ Ω →
        |tr ((A x) ^ k) - tr ((A y) ^ k)| ≤
          traceCoeff * traceNorm (A x - A y))
    (hDiff :
      ∀ ⦃x y : α⦄, x ∈ Ω → y ∈ Ω →
        traceNorm (A x - A y) ≤ diffCoeff * dist x y)
    (hTraceCoeff : 0 ≤ traceCoeff)
    (hL : traceCoeff * diffCoeff ≤ L) :
    LipschitzOn dist Ω (fun x => tr ((A x) ^ k)) L := by
  intro x y hx hy
  have hdistxy : 0 ≤ dist x y := hdist hx hy
  have hDiffScaled :
      traceCoeff * traceNorm (A x - A y) ≤
        traceCoeff * (diffCoeff * dist x y) :=
    mul_le_mul_of_nonneg_left (hDiff hx hy) hTraceCoeff
  calc
    |tr ((A x) ^ k) - tr ((A y) ^ k)| ≤
        traceCoeff * traceNorm (A x - A y) := hTrace hx hy
    _ ≤ traceCoeff * (diffCoeff * dist x y) := hDiffScaled
    _ = (traceCoeff * diffCoeff) * dist x y := by ring
    _ ≤ L * dist x y := mul_le_mul_of_nonneg_right hL hdistxy

/-- Paper-shaped deterministic reduction.

On the good set, Appendix B first proves a trace-power perturbation estimate
and then bounds the trace-norm difference by
`D * (size x + size y) * dist x y`.  If `size` is bounded by `sizeBound` on the
good set, the theorem gives the advertised local Lipschitz estimate. -/
theorem deterministic_lipschitz_from_good_set_bounds
    [Ring β]
    {dist : α → α → ℝ} {Ω : Set α}
    {A : α → β} {tr traceNorm : β → ℝ} {size : α → ℝ}
    {k : ℕ} {traceCoeff D sizeBound L : ℝ}
    (hdist : ∀ ⦃x y : α⦄, x ∈ Ω → y ∈ Ω → 0 ≤ dist x y)
    (hTrace :
      ∀ ⦃x y : α⦄, x ∈ Ω → y ∈ Ω →
        |tr ((A x) ^ k) - tr ((A y) ^ k)| ≤
          traceCoeff * traceNorm (A x - A y))
    (hDiff :
      ∀ ⦃x y : α⦄, x ∈ Ω → y ∈ Ω →
        traceNorm (A x - A y) ≤
          D * (size x + size y) * dist x y)
    (hSize : ∀ ⦃x : α⦄, x ∈ Ω → size x ≤ sizeBound)
    (hTraceCoeff : 0 ≤ traceCoeff)
    (hD : 0 ≤ D)
    (hL : traceCoeff * (D * (2 * sizeBound)) ≤ L) :
    LipschitzOn dist Ω (fun x => tr ((A x) ^ k)) L := by
  refine deterministic_lipschitz_from_trace_and_difference_bounds
    (dist := dist) (Ω := Ω) (A := A) (tr := tr) (traceNorm := traceNorm)
    (k := k) (traceCoeff := traceCoeff) (diffCoeff := D * (2 * sizeBound))
    (L := L) hdist hTrace ?_ hTraceCoeff hL
  intro x y hx hy
  have hsum : size x + size y ≤ 2 * sizeBound := by
    have hxSize := hSize hx
    have hySize := hSize hy
    linarith
  have hsumScaled :
      D * (size x + size y) ≤ D * (2 * sizeBound) :=
    mul_le_mul_of_nonneg_left hsum hD
  calc
    traceNorm (A x - A y) ≤ D * (size x + size y) * dist x y := hDiff hx hy
    _ ≤ (D * (2 * sizeBound)) * dist x y :=
        mul_le_mul_of_nonneg_right hsumScaled (hdist hx hy)

/-- Deterministic matrix analysis with an abstract trace-norm placeholder.

The remaining assumptions are the standard local matrix estimates:

* a trace-power perturbation bound with the maximum operator norm,
* an operator-norm bound on the good set,
* a trace-norm difference bound on the good set,
* a size bound on the good set.

These inputs imply the Lipschitz estimate with the clean constant `L`. -/
theorem deterministic_matrix_lipschitz_from_operator_and_difference_bounds
    [Ring β]
    {dist : α → α → ℝ} {Ω : Set α}
    {A : α → β} {tr traceNorm opNorm : β → ℝ} {size : α → ℝ}
    {k : ℕ} {opBound D sizeBound L : ℝ}
    (hdist : ∀ ⦃x y : α⦄, x ∈ Ω → y ∈ Ω → 0 ≤ dist x y)
    (hTraceNormNonneg : ∀ z : β, 0 ≤ traceNorm z)
    (hTracePower :
      ∀ ⦃x y : α⦄, x ∈ Ω → y ∈ Ω →
        |tr ((A x) ^ k) - tr ((A y) ^ k)| ≤
          (k : ℝ) *
            (max (opNorm (A x)) (opNorm (A y))) ^ (k - 1) *
              traceNorm (A x - A y))
    (hOp : ∀ ⦃x : α⦄, x ∈ Ω → opNorm (A x) ≤ opBound)
    (hOpNonneg : ∀ ⦃x : α⦄, x ∈ Ω → 0 ≤ opNorm (A x))
    (hOpBound : 0 ≤ opBound)
    (hDiff :
      ∀ ⦃x y : α⦄, x ∈ Ω → y ∈ Ω →
        traceNorm (A x - A y) ≤
          D * (size x + size y) * dist x y)
    (hSize : ∀ ⦃x : α⦄, x ∈ Ω → size x ≤ sizeBound)
    (hD : 0 ≤ D)
    (hL : ((k : ℝ) * opBound ^ (k - 1)) * (D * (2 * sizeBound)) ≤ L) :
    LipschitzOn dist Ω (fun x => tr ((A x) ^ k)) L := by
  have hTraceCoeff : 0 ≤ (k : ℝ) * opBound ^ (k - 1) :=
    mul_nonneg (Nat.cast_nonneg k) (pow_nonneg hOpBound _)
  refine deterministic_lipschitz_from_good_set_bounds
    (dist := dist) (Ω := Ω) (A := A) (tr := tr) (traceNorm := traceNorm)
    (size := size) (k := k) (traceCoeff := (k : ℝ) * opBound ^ (k - 1))
    (D := D) (sizeBound := sizeBound) (L := L)
    hdist ?_ hDiff hSize hTraceCoeff hD hL
  intro x y hx hy
  have hmax_le : max (opNorm (A x)) (opNorm (A y)) ≤ opBound :=
    max_le (hOp hx) (hOp hy)
  have hmax_nonneg : 0 ≤ max (opNorm (A x)) (opNorm (A y)) :=
    le_trans (hOpNonneg hx) (le_max_left _ _)
  have hpow :
      (max (opNorm (A x)) (opNorm (A y))) ^ (k - 1) ≤
        opBound ^ (k - 1) :=
    pow_le_pow_left₀ hmax_nonneg hmax_le _
  have hcoeff :
      (k : ℝ) *
          (max (opNorm (A x)) (opNorm (A y))) ^ (k - 1) ≤
        (k : ℝ) * opBound ^ (k - 1) :=
    mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg k)
  have hscaled :
      ((k : ℝ) *
          (max (opNorm (A x)) (opNorm (A y))) ^ (k - 1)) *
          traceNorm (A x - A y) ≤
        ((k : ℝ) * opBound ^ (k - 1)) *
          traceNorm (A x - A y) :=
    mul_le_mul_of_nonneg_right hcoeff (hTraceNormNonneg (A x - A y))
  calc
    |tr ((A x) ^ k) - tr ((A y) ^ k)| ≤
        (k : ℝ) *
          (max (opNorm (A x)) (opNorm (A y))) ^ (k - 1) *
            traceNorm (A x - A y) := hTracePower hx hy
    _ ≤ ((k : ℝ) * opBound ^ (k - 1)) *
          traceNorm (A x - A y) := hscaled

/-- Turn the telescoping expansion of `Tr(A^k)-Tr(B^k)` into the usual
trace-power perturbation estimate.

This lowers the level of abstraction: instead of assuming the full
trace-power perturbation inequality at once, it is enough to know the
telescoping domination and a uniform bound on each of the `k` summands. -/
theorem trace_power_bound_from_telescope_terms
    [Ring β]
    {A B : β} {tr hsNorm : β → ℝ}
    {k : ℕ} {dimensionFactor opBound : ℝ}
    (hTelescope :
      |tr (A ^ k) - tr (B ^ k)| ≤
        ∑ i ∈ Finset.range k,
          |tr (A ^ i * (A - B) * B ^ (k - 1 - i))|)
    (hTerm :
      ∀ i ∈ Finset.range k,
        |tr (A ^ i * (A - B) * B ^ (k - 1 - i))| ≤
          dimensionFactor * opBound ^ (k - 1) * hsNorm (A - B)) :
    |tr (A ^ k) - tr (B ^ k)| ≤
      dimensionFactor * (k : ℝ) * opBound ^ (k - 1) * hsNorm (A - B) := by
  have hsum :
      (∑ i ∈ Finset.range k,
          |tr (A ^ i * (A - B) * B ^ (k - 1 - i))|) ≤
        ∑ _i ∈ Finset.range k,
          dimensionFactor * opBound ^ (k - 1) * hsNorm (A - B) :=
    Finset.sum_le_sum hTerm
  calc
    |tr (A ^ k) - tr (B ^ k)| ≤
        ∑ i ∈ Finset.range k,
          |tr (A ^ i * (A - B) * B ^ (k - 1 - i))| := hTelescope
    _ ≤ ∑ _i ∈ Finset.range k,
          dimensionFactor * opBound ^ (k - 1) * hsNorm (A - B) := hsum
    _ = (k : ℝ) * (dimensionFactor * opBound ^ (k - 1) * hsNorm (A - B)) := by
        simp
    _ = dimensionFactor * (k : ℝ) * opBound ^ (k - 1) * hsNorm (A - B) := by
        ring

/-- Trace-power perturbation from primitive Hilbert-Schmidt/operator-norm
controls on each telescoping summand.

The hypotheses are now the usual deterministic matrix ingredients: trace is
controlled by the Hilbert-Schmidt norm, multiplication is controlled by
operator norm times Hilbert-Schmidt norm times operator norm, and the powers
of `A` and `B` are bounded by powers of a common operator-norm bound. -/
theorem trace_power_bound_from_telescope_and_hs_op_controls
    [Ring β]
    {A B : β} {tr hsNorm opNorm : β → ℝ}
    {k : ℕ} {dimensionFactor opBound : ℝ}
    (hHsNormNonneg : ∀ z : β, 0 ≤ hsNorm z)
    (hOpNormNonneg : ∀ z : β, 0 ≤ opNorm z)
    (hDimensionFactor : 0 ≤ dimensionFactor)
    (hOpBound : 0 ≤ opBound)
    (hTelescope :
      |tr (A ^ k) - tr (B ^ k)| ≤
        ∑ i ∈ Finset.range k,
          |tr (A ^ i * (A - B) * B ^ (k - 1 - i))|)
    (hTraceHS :
      ∀ i ∈ Finset.range k,
        |tr (A ^ i * (A - B) * B ^ (k - 1 - i))| ≤
          dimensionFactor * hsNorm (A ^ i * (A - B) * B ^ (k - 1 - i)))
    (hHsMul :
      ∀ i ∈ Finset.range k,
        hsNorm (A ^ i * (A - B) * B ^ (k - 1 - i)) ≤
          opNorm (A ^ i) * hsNorm (A - B) * opNorm (B ^ (k - 1 - i)))
    (hOpLeft :
      ∀ i ∈ Finset.range k, opNorm (A ^ i) ≤ opBound ^ i)
    (hOpRight :
      ∀ i ∈ Finset.range k,
        opNorm (B ^ (k - 1 - i)) ≤ opBound ^ (k - 1 - i)) :
    |tr (A ^ k) - tr (B ^ k)| ≤
      dimensionFactor * (k : ℝ) * opBound ^ (k - 1) * hsNorm (A - B) := by
  refine trace_power_bound_from_telescope_terms
    (A := A) (B := B) (tr := tr) (hsNorm := hsNorm)
    (k := k) (dimensionFactor := dimensionFactor) (opBound := opBound)
    hTelescope ?_
  intro i hi
  have hi_le : i ≤ k - 1 := Nat.le_pred_of_lt (Finset.mem_range.mp hi)
  have hpowprod :
      opBound ^ i * opBound ^ (k - 1 - i) = opBound ^ (k - 1) := by
    rw [← pow_add]
    rw [Nat.add_sub_of_le hi_le]
  have hleft :
      opNorm (A ^ i) * hsNorm (A - B) ≤
        opBound ^ i * hsNorm (A - B) :=
    mul_le_mul_of_nonneg_right (hOpLeft i hi) (hHsNormNonneg (A - B))
  have hmid_nonneg : 0 ≤ opBound ^ i * hsNorm (A - B) :=
    mul_nonneg (pow_nonneg hOpBound _) (hHsNormNonneg (A - B))
  have hproduct :
      opNorm (A ^ i) * hsNorm (A - B) * opNorm (B ^ (k - 1 - i)) ≤
        opBound ^ (k - 1) * hsNorm (A - B) := by
    calc
      opNorm (A ^ i) * hsNorm (A - B) * opNorm (B ^ (k - 1 - i)) ≤
          opBound ^ i * hsNorm (A - B) * opNorm (B ^ (k - 1 - i)) :=
        mul_le_mul_of_nonneg_right hleft (hOpNormNonneg (B ^ (k - 1 - i)))
      _ ≤ opBound ^ i * hsNorm (A - B) * opBound ^ (k - 1 - i) :=
        mul_le_mul_of_nonneg_left (hOpRight i hi) hmid_nonneg
      _ = opBound ^ (k - 1) * hsNorm (A - B) := by
        calc
          opBound ^ i * hsNorm (A - B) * opBound ^ (k - 1 - i)
              = (opBound ^ i * opBound ^ (k - 1 - i)) * hsNorm (A - B) := by
                ring
          _ = opBound ^ (k - 1) * hsNorm (A - B) := by
                rw [hpowprod]
  have hhs :
      hsNorm (A ^ i * (A - B) * B ^ (k - 1 - i)) ≤
        opBound ^ (k - 1) * hsNorm (A - B) :=
    (hHsMul i hi).trans hproduct
  calc
    |tr (A ^ i * (A - B) * B ^ (k - 1 - i))| ≤
        dimensionFactor * hsNorm (A ^ i * (A - B) * B ^ (k - 1 - i)) :=
      hTraceHS i hi
    _ ≤ dimensionFactor * (opBound ^ (k - 1) * hsNorm (A - B)) :=
      mul_le_mul_of_nonneg_left hhs hDimensionFactor
    _ = dimensionFactor * opBound ^ (k - 1) * hsNorm (A - B) := by
      ring

/-- Paper-safe deterministic matrix analysis using Frobenius and operator
norms.

Here `hsNorm` represents the Frobenius/Hilbert--Schmidt norm.  The scalar
`dimensionFactor` is the factor coming from the deterministic estimate
`|Tr M| <= dimensionFactor * ||M||_HS`.  In the concrete Appendix B
application this avoids having to route the proof through a trace-norm API:
the trace-power perturbation is controlled directly by the operator norm and
the Frobenius difference. -/
theorem deterministic_frobenius_lipschitz_from_operator_and_difference_bounds
    [Ring β]
    {dist : α → α → ℝ} {Ω : Set α}
    {A : α → β} {tr hsNorm opNorm : β → ℝ} {size : α → ℝ}
    {k : ℕ} {dimensionFactor opBound D sizeBound L : ℝ}
    (hdist : ∀ ⦃x y : α⦄, x ∈ Ω → y ∈ Ω → 0 ≤ dist x y)
    (hHsNormNonneg : ∀ z : β, 0 ≤ hsNorm z)
    (hDimensionFactor : 0 ≤ dimensionFactor)
    (hTracePowerHS :
      ∀ ⦃x y : α⦄, x ∈ Ω → y ∈ Ω →
        |tr ((A x) ^ k) - tr ((A y) ^ k)| ≤
          dimensionFactor * (k : ℝ) *
            (max (opNorm (A x)) (opNorm (A y))) ^ (k - 1) *
              hsNorm (A x - A y))
    (hOp : ∀ ⦃x : α⦄, x ∈ Ω → opNorm (A x) ≤ opBound)
    (hOpNonneg : ∀ ⦃x : α⦄, x ∈ Ω → 0 ≤ opNorm (A x))
    (hOpBound : 0 ≤ opBound)
    (hDiffHS :
      ∀ ⦃x y : α⦄, x ∈ Ω → y ∈ Ω →
        hsNorm (A x - A y) ≤
          D * (size x + size y) * dist x y)
    (hSize : ∀ ⦃x : α⦄, x ∈ Ω → size x ≤ sizeBound)
    (hD : 0 ≤ D)
    (hL :
      (dimensionFactor * ((k : ℝ) * opBound ^ (k - 1))) *
          (D * (2 * sizeBound)) ≤ L) :
    LipschitzOn dist Ω (fun x => tr ((A x) ^ k)) L := by
  have hTraceCoeff :
      0 ≤ dimensionFactor * ((k : ℝ) * opBound ^ (k - 1)) :=
    mul_nonneg hDimensionFactor
      (mul_nonneg (Nat.cast_nonneg k) (pow_nonneg hOpBound _))
  refine deterministic_lipschitz_from_good_set_bounds
    (dist := dist) (Ω := Ω) (A := A) (tr := tr) (traceNorm := hsNorm)
    (size := size) (k := k)
    (traceCoeff := dimensionFactor * ((k : ℝ) * opBound ^ (k - 1)))
    (D := D) (sizeBound := sizeBound) (L := L)
    hdist ?_ hDiffHS hSize hTraceCoeff hD hL
  intro x y hx hy
  have hmax_le : max (opNorm (A x)) (opNorm (A y)) ≤ opBound :=
    max_le (hOp hx) (hOp hy)
  have hmax_nonneg : 0 ≤ max (opNorm (A x)) (opNorm (A y)) :=
    le_trans (hOpNonneg hx) (le_max_left _ _)
  have hpow :
      (max (opNorm (A x)) (opNorm (A y))) ^ (k - 1) ≤
        opBound ^ (k - 1) :=
    pow_le_pow_left₀ hmax_nonneg hmax_le _
  have hinner :
      (k : ℝ) *
          (max (opNorm (A x)) (opNorm (A y))) ^ (k - 1) ≤
        (k : ℝ) * opBound ^ (k - 1) :=
    mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg k)
  have hcoeff :
      dimensionFactor *
          ((k : ℝ) *
            (max (opNorm (A x)) (opNorm (A y))) ^ (k - 1)) ≤
        dimensionFactor * ((k : ℝ) * opBound ^ (k - 1)) :=
    mul_le_mul_of_nonneg_left hinner hDimensionFactor
  have hscaled :
      (dimensionFactor *
          ((k : ℝ) *
            (max (opNorm (A x)) (opNorm (A y))) ^ (k - 1))) *
          hsNorm (A x - A y) ≤
        (dimensionFactor * ((k : ℝ) * opBound ^ (k - 1))) *
          hsNorm (A x - A y) :=
    mul_le_mul_of_nonneg_right hcoeff (hHsNormNonneg (A x - A y))
  calc
    |tr ((A x) ^ k) - tr ((A y) ^ k)| ≤
        dimensionFactor * (k : ℝ) *
          (max (opNorm (A x)) (opNorm (A y))) ^ (k - 1) *
            hsNorm (A x - A y) := hTracePowerHS hx hy
    _ = (dimensionFactor *
          ((k : ℝ) *
            (max (opNorm (A x)) (opNorm (A y))) ^ (k - 1))) *
          hsNorm (A x - A y) := by ring
    _ ≤ (dimensionFactor * ((k : ℝ) * opBound ^ (k - 1))) *
          hsNorm (A x - A y) := hscaled

/-- Deterministic Frobenius Lipschitz estimate from the actual telescoping
summands.

This is one level less raw than
`deterministic_frobenius_lipschitz_from_operator_and_difference_bounds`.
The caller supplies the telescoping expansion and the bound on each summand;
the theorem performs the finite-sum step, inserts the operator-norm good-set
bound, and then derives the local Lipschitz constant. -/
theorem deterministic_frobenius_lipschitz_from_telescoping_terms
    [Ring β]
    {dist : α → α → ℝ} {Ω : Set α}
    {A : α → β} {tr hsNorm opNorm : β → ℝ} {size : α → ℝ}
    {k : ℕ} {dimensionFactor opBound D sizeBound L : ℝ}
    (hdist : ∀ ⦃x y : α⦄, x ∈ Ω → y ∈ Ω → 0 ≤ dist x y)
    (hHsNormNonneg : ∀ z : β, 0 ≤ hsNorm z)
    (hDimensionFactor : 0 ≤ dimensionFactor)
    (hTelescope :
      ∀ ⦃x y : α⦄, x ∈ Ω → y ∈ Ω →
        |tr ((A x) ^ k) - tr ((A y) ^ k)| ≤
          ∑ i ∈ Finset.range k,
            |tr ((A x) ^ i * (A x - A y) * (A y) ^ (k - 1 - i))|)
    (hTerm :
      ∀ ⦃x y : α⦄, x ∈ Ω → y ∈ Ω →
        ∀ i ∈ Finset.range k,
          |tr ((A x) ^ i * (A x - A y) * (A y) ^ (k - 1 - i))| ≤
            dimensionFactor *
              (max (opNorm (A x)) (opNorm (A y))) ^ (k - 1) *
                hsNorm (A x - A y))
    (hOp : ∀ ⦃x : α⦄, x ∈ Ω → opNorm (A x) ≤ opBound)
    (hOpNonneg : ∀ ⦃x : α⦄, x ∈ Ω → 0 ≤ opNorm (A x))
    (hOpBound : 0 ≤ opBound)
    (hDiffHS :
      ∀ ⦃x y : α⦄, x ∈ Ω → y ∈ Ω →
        hsNorm (A x - A y) ≤
          D * (size x + size y) * dist x y)
    (hSize : ∀ ⦃x : α⦄, x ∈ Ω → size x ≤ sizeBound)
    (hD : 0 ≤ D)
    (hL :
      (dimensionFactor * ((k : ℝ) * opBound ^ (k - 1))) *
          (D * (2 * sizeBound)) ≤ L) :
    LipschitzOn dist Ω (fun x => tr ((A x) ^ k)) L := by
  refine deterministic_frobenius_lipschitz_from_operator_and_difference_bounds
    (dist := dist) (Ω := Ω) (A := A) (tr := tr) (hsNorm := hsNorm)
    (opNorm := opNorm) (size := size) (k := k)
    (dimensionFactor := dimensionFactor) (opBound := opBound)
    (D := D) (sizeBound := sizeBound) (L := L)
    hdist hHsNormNonneg hDimensionFactor ?_ hOp hOpNonneg hOpBound
    hDiffHS hSize hD hL
  intro x y hx hy
  exact trace_power_bound_from_telescope_terms
    (A := A x) (B := A y) (tr := tr) (hsNorm := hsNorm)
    (k := k) (dimensionFactor := dimensionFactor)
    (opBound := max (opNorm (A x)) (opNorm (A y)))
    (hTelescope hx hy) (hTerm hx hy)

/-- Deterministic Frobenius Lipschitz estimate from primitive trace and norm
controls.

This is the deepest abstract deterministic interface in this file.  The
trace-power perturbation estimate is no longer assumed.  It is reconstructed
from the telescoping expansion, the trace versus Hilbert-Schmidt estimate, the
Hilbert-Schmidt/operator product estimate, and the bounds on operator norms of
powers. -/
theorem deterministic_frobenius_lipschitz_from_hs_op_telescope_controls
    [Ring β]
    {dist : α → α → ℝ} {Ω : Set α}
    {A : α → β} {tr hsNorm opNorm : β → ℝ} {size : α → ℝ}
    {k : ℕ} {dimensionFactor opBound D sizeBound L : ℝ}
    (hdist : ∀ ⦃x y : α⦄, x ∈ Ω → y ∈ Ω → 0 ≤ dist x y)
    (hHsNormNonneg : ∀ z : β, 0 ≤ hsNorm z)
    (hOpNormNonneg : ∀ z : β, 0 ≤ opNorm z)
    (hDimensionFactor : 0 ≤ dimensionFactor)
    (hTelescope :
      ∀ ⦃x y : α⦄, x ∈ Ω → y ∈ Ω →
        |tr ((A x) ^ k) - tr ((A y) ^ k)| ≤
          ∑ i ∈ Finset.range k,
            |tr ((A x) ^ i * (A x - A y) * (A y) ^ (k - 1 - i))|)
    (hTraceHS :
      ∀ ⦃x y : α⦄, x ∈ Ω → y ∈ Ω →
        ∀ i ∈ Finset.range k,
          |tr ((A x) ^ i * (A x - A y) * (A y) ^ (k - 1 - i))| ≤
            dimensionFactor *
              hsNorm ((A x) ^ i * (A x - A y) * (A y) ^ (k - 1 - i)))
    (hHsMul :
      ∀ ⦃x y : α⦄, x ∈ Ω → y ∈ Ω →
        ∀ i ∈ Finset.range k,
          hsNorm ((A x) ^ i * (A x - A y) * (A y) ^ (k - 1 - i)) ≤
            opNorm ((A x) ^ i) * hsNorm (A x - A y) *
              opNorm ((A y) ^ (k - 1 - i)))
    (hOpLeftPower :
      ∀ ⦃x y : α⦄, x ∈ Ω → y ∈ Ω →
        ∀ i ∈ Finset.range k,
          opNorm ((A x) ^ i) ≤
            (max (opNorm (A x)) (opNorm (A y))) ^ i)
    (hOpRightPower :
      ∀ ⦃x y : α⦄, x ∈ Ω → y ∈ Ω →
        ∀ i ∈ Finset.range k,
          opNorm ((A y) ^ (k - 1 - i)) ≤
            (max (opNorm (A x)) (opNorm (A y))) ^ (k - 1 - i))
    (hOp : ∀ ⦃x : α⦄, x ∈ Ω → opNorm (A x) ≤ opBound)
    (hOpNonneg : ∀ ⦃x : α⦄, x ∈ Ω → 0 ≤ opNorm (A x))
    (hOpBound : 0 ≤ opBound)
    (hDiffHS :
      ∀ ⦃x y : α⦄, x ∈ Ω → y ∈ Ω →
        hsNorm (A x - A y) ≤
          D * (size x + size y) * dist x y)
    (hSize : ∀ ⦃x : α⦄, x ∈ Ω → size x ≤ sizeBound)
    (hD : 0 ≤ D)
    (hL :
      (dimensionFactor * ((k : ℝ) * opBound ^ (k - 1))) *
          (D * (2 * sizeBound)) ≤ L) :
    LipschitzOn dist Ω (fun x => tr ((A x) ^ k)) L := by
  refine deterministic_frobenius_lipschitz_from_operator_and_difference_bounds
    (dist := dist) (Ω := Ω) (A := A) (tr := tr) (hsNorm := hsNorm)
    (opNorm := opNorm) (size := size) (k := k)
    (dimensionFactor := dimensionFactor) (opBound := opBound)
    (D := D) (sizeBound := sizeBound) (L := L)
    hdist hHsNormNonneg hDimensionFactor ?_ hOp hOpNonneg hOpBound
    hDiffHS hSize hD hL
  intro x y hx hy
  have hmax_nonneg : 0 ≤ max (opNorm (A x)) (opNorm (A y)) :=
    le_trans (hOpNonneg hx) (le_max_left _ _)
  exact trace_power_bound_from_telescope_and_hs_op_controls
    (A := A x) (B := A y) (tr := tr) (hsNorm := hsNorm)
    (opNorm := opNorm) (k := k) (dimensionFactor := dimensionFactor)
    (opBound := max (opNorm (A x)) (opNorm (A y)))
    hHsNormNonneg hOpNormNonneg hDimensionFactor hmax_nonneg
    (hTelescope hx hy) (hTraceHS hx hy) (hHsMul hx hy)
    (hOpLeftPower hx hy) (hOpRightPower hx hy)

/-! ## Good-set probability bookkeeping -/

/-- Union bound for the good set `Ω = Ω₁ ∩ Ω₂`.

In Appendix B, `E = exp(-c d^2)`, and this gives
`P(Ωᶜ) ≤ 2 exp(-c d^2)`. -/
theorem good_set_intersection_bound
    {pΩc pΩ1c pΩ2c E : ℝ}
    (hUnion : pΩc ≤ pΩ1c + pΩ2c)
    (hΩ1 : pΩ1c ≤ E)
    (hΩ2 : pΩ2c ≤ E) :
    pΩc ≤ 2 * E := by
  linarith

/-! ## Exponential scale from the local Levy lemma -/

/-- The exponent comparison behind the stronger normalized-model estimate.

The hypothesis says exactly that the Levy exponent
`n t^2 / (4 L^2)` dominates the target scale
`c₂ d^4 ε^2 / k^2`. In the appendix this comes from
`n ≍ d^4`, `t = ε / d^(2k-2)`, and
`L ≲ k / d^(2k-2)`. -/
theorem levy_exponential_scale
    {n t L c₂ d eps k : ℝ}
    (hExponent :
      c₂ * d ^ 4 * eps ^ 2 / k ^ 2 ≤ n * t ^ 2 / (4 * L ^ 2)) :
    Real.exp (-(n * t ^ 2 / (4 * L ^ 2))) ≤
      Real.exp (-(c₂ * d ^ 4 * eps ^ 2 / k ^ 2)) := by
  exact (Real.exp_le_exp).2 (by linarith)

/-- Every event in a probability space has real measure at most one. -/
theorem probability_event_real_le_one
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (A : Set Ω) :
    μ.real A ≤ 1 := by
  calc
    μ.real A ≤ μ.real (Set.univ : Set Ω) :=
      measureReal_mono (Set.subset_univ _) (h₂ := (measure_lt_top μ _).ne)
    _ = 1 := by simp

/-- If the Levy exponent is at most `log 4`, the exponential Levy-shaped
right-hand side is already at least the trivial probability bound `1`.

This is a deliberately weak but no-input concentration fact: it is useful for
small-deviation branches, and it makes explicit that no spherical
isoperimetry is being smuggled into the proof. -/
theorem one_le_four_exp_neg_of_le_log_four
    {x : ℝ} (hx : x ≤ Real.log 4) :
    1 ≤ 4 * Real.exp (-x) := by
  have hquarter : (1 / 4 : ℝ) = Real.exp (-(Real.log 4)) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    norm_num
  have hExp : (1 / 4 : ℝ) ≤ Real.exp (-x) := by
    calc
      (1 / 4 : ℝ) = Real.exp (-(Real.log 4)) := hquarter
      _ ≤ Real.exp (-x) := (Real.exp_le_exp).2 (by linarith)
  nlinarith

/-- No-input small-exponent Levy-shaped tail bound.

This is not the full spherical Levy lemma.  It is the strongest completely
measure-theoretic statement available without geometric input: whenever the
desired exponent is small enough, the exponential right-hand side dominates
the universal probability bound. -/
theorem noInput_levy_tail_small_exponent
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {center n t L : ℝ}
    (hExponent : n * t ^ 2 / (4 * L ^ 2) ≤ Real.log 4) :
    μ.real {ω | t ≤ |f ω - center|} ≤
      4 * Real.exp (-(n * t ^ 2 / (4 * L ^ 2))) := by
  exact (probability_event_real_le_one
    (μ := μ) {ω | t ≤ |f ω - center|}).trans
      (one_le_four_exp_neg_of_le_log_four hExponent)

/-! ## Median concentration -/

/-- Combine the localized Levy lemma with the good-set estimate.

Here `bad` is `P(Ωᶜ)`.  The local Levy lemma gives
`tail ≤ 2 bad + 2 exp(-...)`, while the good-set estimate gives
`bad ≤ 2 exp(-c d^2)`.  The arithmetic then gives that the median tail is
therefore
bounded by
`4 exp(-c d^2) + 2 exp(-c₂ d^4 ε^2/k^2)`. -/
theorem appendixB_median_concentration
    {medianTail bad n t L c c₂ d eps k : ℝ}
    (hLevy :
      medianTail ≤ 2 * bad + 2 * Real.exp (-(n * t ^ 2 / (4 * L ^ 2))))
    (hGood : bad ≤ 2 * Real.exp (-(c * d ^ 2)))
    (hExponent :
      c₂ * d ^ 4 * eps ^ 2 / k ^ 2 ≤ n * t ^ 2 / (4 * L ^ 2)) :
    medianTail ≤
      4 * Real.exp (-(c * d ^ 2)) +
      2 * Real.exp (-(c₂ * d ^ 4 * eps ^ 2 / k ^ 2)) := by
  have hExp := levy_exponential_scale (n := n) (t := t) (L := L)
    (c₂ := c₂) (d := d) (eps := eps) (k := k) hExponent
  linarith

/-! ## Median-to-mean replacement -/

/-- Quantitative median-to-mean estimate from an integrated tail bound.

For a probability measure, if `mean` is the expectation of `f`, then the
distance from the mean to any reference value `median` is bounded by the first
absolute moment around `median`.  The layer-cake formula rewrites that moment
as the integral of the tail probabilities.  This is the formal replacement for
the informal sentence "`M_f` is close to `E f`". -/
theorem mean_median_gap_from_integrated_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {mean median range gapBound : ℝ}
    (hmean : mean = ∫ ω, f ω ∂μ)
    (hf : Integrable f μ)
    (hRange : (fun ω => |f ω - median|) ≤ᵐ[μ] fun _ => range)
    (hTailIntegral :
      ∫ u in Set.Ioc 0 range, μ.real {ω | u ≤ |f ω - median|} ≤ gapBound) :
    |mean - median| ≤ gapBound := by
  have hconst : Integrable (fun _ : Ω => median) μ := integrable_const median
  have hsub : Integrable (fun ω => f ω - median) μ := hf.sub hconst
  have hdev : Integrable (fun ω => |f ω - median|) μ := by
    simpa [Real.norm_eq_abs] using hsub.norm
  have hsubIntegral :
      (∫ ω, (f ω - median) ∂μ) = mean - median := by
    rw [integral_sub hf hconst, hmean]
    simp
  have hMoment :
      |mean - median| ≤ ∫ ω, |f ω - median| ∂μ := by
    calc
      |mean - median| = ‖∫ ω, (f ω - median) ∂μ‖ := by
        rw [hsubIntegral]
        simp [Real.norm_eq_abs]
      _ ≤ ∫ ω, ‖f ω - median‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ ω, |f ω - median| ∂μ := by
        simp [Real.norm_eq_abs]
  have hLayer :
      (∫ ω, |f ω - median| ∂μ) =
        ∫ u in Set.Ioc 0 range, μ.real {ω | u ≤ |f ω - median|} :=
    Integrable.integral_eq_integral_Ioc_meas_le hdev
      (Filter.Eventually.of_forall fun _ => abs_nonneg _) hRange
  exact hMoment.trans (by simpa [hLayer] using hTailIntegral)

/-- Deterministic inclusion of deviation events.

If the mean and median differ by at most half the target scale, then every
point that deviates from the mean by at least `scale` deviates from the
median by at least `scale / 2`. -/
lemma mean_deviation_implies_median_deviation
    {z mean median scale : ℝ}
    (hshift : |mean - median| ≤ scale / 2)
    (hdev : scale ≤ |z - mean|) :
    scale / 2 ≤ |z - median| := by
  have htri : |z - mean| ≤ |z - median| + |median - mean| := by
    calc
      |z - mean| = |(z - median) + (median - mean)| := by ring_nf
      _ ≤ |z - median| + |median - mean| := abs_add_le _ _
  have hshift' : |median - mean| ≤ scale / 2 := by
    simpa [abs_sub_comm] using hshift
  linarith

/-- Probability-level version of the deterministic median-to-mean inclusion.

Once the mean and the median are within half of the target scale, the event
centered at the mean is contained in the corresponding event centered at the
median with half the scale.  Hence the mean-centered tail is bounded by the
median-centered tail. -/
lemma mean_tail_probability_le_median_tail_probability
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → ℝ} {mean median scale : ℝ}
    (hshift : |mean - median| ≤ scale / 2) :
    μ.real {ω | scale ≤ |f ω - mean|} ≤
      μ.real {ω | scale / 2 ≤ |f ω - median|} := by
  apply measureReal_mono (h₂ := (measure_lt_top μ _).ne)
  intro ω hω
  exact mean_deviation_implies_median_deviation hshift hω

/-- Probability-level median-to-mean replacement from an integrated tail
estimate.

This is the quantitative form used in Appendix B: once the integrated median
tail is at most half of the target deviation scale, the mean-centered deviation
event is included in the half-scale median-centered event. -/
lemma mean_tail_probability_le_median_tail_probability_from_integrated_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {mean median scale range : ℝ}
    (hmean : mean = ∫ ω, f ω ∂μ)
    (hf : Integrable f μ)
    (hRange : (fun ω => |f ω - median|) ≤ᵐ[μ] fun _ => range)
    (hTailIntegral :
      ∫ u in Set.Ioc 0 range, μ.real {ω | u ≤ |f ω - median|} ≤ scale / 2) :
    μ.real {ω | scale ≤ |f ω - mean|} ≤
      μ.real {ω | scale / 2 ≤ |f ω - median|} := by
  have hgap :
      |mean - median| ≤ scale / 2 :=
    mean_median_gap_from_integrated_tail
      (μ := μ) (f := f) (mean := mean) (median := median)
      (range := range) (gapBound := scale / 2)
      hmean hf hRange hTailIntegral
  exact mean_tail_probability_le_median_tail_probability
    (μ := μ) (f := f) (mean := mean) (median := median) (scale := scale) hgap

/-- Paper-facing expectation shift from the median-centered surrogate `F_k`
to the mean-centered observable `f_k`.

This is the same integrated-tail median-to-mean comparison, restated in the
notation used in the manuscript. -/
theorem paper_expectation_shift_Fk_to_fk
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {mean median scale range : ℝ}
    (hmean : mean = ∫ ω, f ω ∂μ)
    (hf : Integrable f μ)
    (hRange : (fun ω => |f ω - median|) ≤ᵐ[μ] fun _ => range)
    (hTailIntegral :
      ∫ u in Set.Ioc 0 range, μ.real {ω | u ≤ |f ω - median|} ≤ scale / 2) :
    μ.real {ω | scale ≤ |f ω - mean|} ≤
      μ.real {ω | scale / 2 ≤ |f ω - median|} := by
  exact mean_tail_probability_le_median_tail_probability_from_integrated_tail
    (μ := μ) (f := f) (mean := mean) (median := median)
    (scale := scale) (range := range) hmean hf hRange hTailIntegral

/-- The explicit scale of the integrated median-to-mean error used in the
paper discussion.

The term `range * bad` is the contribution of the localized bad set on the
deterministic range of the variable.  The term `L / sqrt n` is the Gaussian
one-dimensional integral coming from the Levy tail. -/
noncomputable def quantitativeMedianMeanBound (range bad L n : ℝ) : ℝ :=
  range * bad + L / Real.sqrt n

/-- Explicit integrated bound obtained by integrating the localized tail
estimate

`u ↦ 2 * bad + 4 * exp(-(n * u^2 / (16 * L^2)))`

over `u ∈ (0, range]`.  The first term is the bad-set contribution; the second
term is the one-dimensional Gaussian integral written in the exact
`integral_gaussian_Ioi` normalization used by mathlib. -/
noncomputable def localizedTailIntegralBound (range bad L n : ℝ) : ℝ :=
  2 * range * bad + 2 * Real.sqrt (Real.pi / (n / (16 * L ^ 2)))

/-- Integrate the localized median tail bound over the layer-cake variable.

This removes the remaining external hypothesis `hTailIntegral`: if the median
tail is pointwise controlled on `u ∈ (0, range]` by the localized Levy shape
`2 * bad + 4 * exp(-(n * u^2 / (16 * L^2)))`, then its integral is bounded by
`localizedTailIntegralBound range bad L n`. -/
theorem localized_tail_integral_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → ℝ} {median range bad L n : ℝ}
    (hRange : 0 ≤ range)
    (hL : 0 < L)
    (hn : 0 < n)
    (hTail :
      ∀ ⦃u : ℝ⦄, u ∈ Set.Ioc 0 range →
        μ.real {ω | u ≤ |f ω - median|} ≤
          2 * bad + 4 * Real.exp (-(n * u ^ 2 / (16 * L ^ 2)))) :
    ∫ u in Set.Ioc 0 range, μ.real {ω | u ≤ |f ω - median|} ≤
      localizedTailIntegralBound range bad L n := by
  let b : ℝ := n / (16 * L ^ 2)
  have hDen : 0 < 16 * L ^ 2 := by positivity
  have hb : 0 < b := by
    dsimp [b]
    exact div_pos hn hDen
  have hExpEq :
      (fun u : ℝ => Real.exp (-(n * u ^ 2 / (16 * L ^ 2)))) =
        fun u : ℝ => Real.exp (-b * u ^ 2) := by
    ext u
    dsimp [b]
    congr 1
    ring_nf
  have hExpIntegrableIoi :
      IntegrableOn (fun u : ℝ => Real.exp (-(n * u ^ 2 / (16 * L ^ 2))))
        (Set.Ioi 0) volume := by
    rw [hExpEq]
    exact (integrableOn_Ioi_exp_neg_mul_sq_iff).2 hb
  have hExpIntegrable :
      IntegrableOn (fun u : ℝ => Real.exp (-(n * u ^ 2 / (16 * L ^ 2))))
        (Set.Ioc 0 range) volume :=
    IntegrableOn.mono_set hExpIntegrableIoi Set.Ioc_subset_Ioi_self
  have hUpperIntegrable :
      IntegrableOn
        (fun u : ℝ =>
          2 * bad + 4 * Real.exp (-(n * u ^ 2 / (16 * L ^ 2))))
        (Set.Ioc 0 range) volume := by
    refine (integrableOn_const ?_).add ?_
    · simp [Real.volume_Ioc]
    · exact hExpIntegrable.const_mul 4
  have hConstIntegrable :
      IntegrableOn (fun _ : ℝ => (2 * bad : ℝ)) (Set.Ioc 0 range) volume := by
    exact integrableOn_const (by simp [Real.volume_Ioc])
  have hScaledExpIntegrable :
      IntegrableOn
        (fun u : ℝ => 4 * Real.exp (-(n * u ^ 2 / (16 * L ^ 2))))
        (Set.Ioc 0 range) volume := by
    exact hExpIntegrable.const_mul 4
  have hNonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioc 0 range)]
        fun u : ℝ => μ.real {ω | u ≤ |f ω - median|} := by
    exact Filter.Eventually.of_forall fun _ => by positivity
  have hPointwise :
      ∀ᵐ u ∂(volume.restrict (Set.Ioc 0 range)),
        μ.real {ω | u ≤ |f ω - median|} ≤
          2 * bad + 4 * Real.exp (-(n * u ^ 2 / (16 * L ^ 2))) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall fun _ hu => hTail hu
  have hBoundByUpper :
      ∫ u in Set.Ioc 0 range, μ.real {ω | u ≤ |f ω - median|} ≤
        ∫ u in Set.Ioc 0 range,
          (2 * bad + 4 * Real.exp (-(n * u ^ 2 / (16 * L ^ 2)))) := by
    simpa [IntegrableOn] using
      (integral_mono_of_nonneg hNonneg hUpperIntegrable hPointwise)
  have hGaussianMono :
      ∫ u in Set.Ioc 0 range, Real.exp (-(n * u ^ 2 / (16 * L ^ 2))) ≤
        ∫ u in Set.Ioi (0 : ℝ), Real.exp (-(n * u ^ 2 / (16 * L ^ 2))) := by
    refine setIntegral_mono_set hExpIntegrableIoi ?_ ?_
    · exact Filter.Eventually.of_forall fun _ => le_of_lt (Real.exp_pos _)
    · exact Set.Ioc_subset_Ioi_self.eventuallyLE
  have hGaussianIoi :
      ∫ u in Set.Ioi (0 : ℝ), Real.exp (-(n * u ^ 2 / (16 * L ^ 2))) =
        Real.sqrt (Real.pi / b) / 2 := by
    rw [hExpEq]
    simpa using integral_gaussian_Ioi b
  have hConstIntegral :
      ∫ u in Set.Ioc 0 range, (2 * bad : ℝ) = 2 * range * bad := by
    rw [MeasureTheory.setIntegral_const]
    simp [hRange]
    ring
  have hSplitIntegral :
      ∫ u in Set.Ioc 0 range,
          (2 * bad + 4 * Real.exp (-(n * u ^ 2 / (16 * L ^ 2)))) =
        (∫ u in Set.Ioc 0 range, (2 * bad : ℝ)) +
          (∫ u in Set.Ioc 0 range,
            (4 * Real.exp (-(n * u ^ 2 / (16 * L ^ 2))))) := by
    simpa using integral_add hConstIntegrable hScaledExpIntegrable
  have hConstPlus :
      (∫ u in Set.Ioc 0 range, (2 * bad : ℝ)) +
          (∫ u in Set.Ioc 0 range,
            (4 * Real.exp (-(n * u ^ 2 / (16 * L ^ 2))))) =
        2 * range * bad +
          (∫ u in Set.Ioc 0 range,
            (4 * Real.exp (-(n * u ^ 2 / (16 * L ^ 2))))) := by
    rw [hConstIntegral]
  have hUpperExplicit :
      ∫ u in Set.Ioc 0 range,
          (2 * bad + 4 * Real.exp (-(n * u ^ 2 / (16 * L ^ 2)))) ≤
        localizedTailIntegralBound range bad L n := by
    calc
      ∫ u in Set.Ioc 0 range,
          (2 * bad + 4 * Real.exp (-(n * u ^ 2 / (16 * L ^ 2)))) =
          (∫ u in Set.Ioc 0 range, (2 * bad : ℝ)) +
            (∫ u in Set.Ioc 0 range,
              (4 * Real.exp (-(n * u ^ 2 / (16 * L ^ 2))))) := hSplitIntegral
      _ = 2 * range * bad +
            (∫ u in Set.Ioc 0 range,
              (4 * Real.exp (-(n * u ^ 2 / (16 * L ^ 2))))) := hConstPlus
      _ = 2 * range * bad +
            4 * (∫ u in Set.Ioc 0 range,
              Real.exp (-(n * u ^ 2 / (16 * L ^ 2)))) := by
            rw [integral_const_mul]
      _ ≤ 2 * range * bad +
            4 * (∫ u in Set.Ioi (0 : ℝ),
              Real.exp (-(n * u ^ 2 / (16 * L ^ 2)))) := by
            gcongr
      _ = 2 * range * bad + 4 * (Real.sqrt (Real.pi / b) / 2) := by
            rw [hGaussianIoi]
      _ = localizedTailIntegralBound range bad L n := by
            dsimp [localizedTailIntegralBound, b]
            ring
  exact hBoundByUpper.trans hUpperExplicit

/-- Median-to-mean replacement using the explicit integral of the localized
tail instead of a separate input `hTailIntegral`. -/
lemma mean_tail_probability_le_median_tail_probability_from_localized_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {mean median scale range bad L n : ℝ}
    (hmean : mean = ∫ ω, f ω ∂μ)
    (hf : Integrable f μ)
    (hRange : (fun ω => |f ω - median|) ≤ᵐ[μ] fun _ => range)
    (hRangeNonneg : 0 ≤ range)
    (hL : 0 < L)
    (hn : 0 < n)
    (hTail :
      ∀ ⦃u : ℝ⦄, u ∈ Set.Ioc 0 range →
        μ.real {ω | u ≤ |f ω - median|} ≤
          2 * bad + 4 * Real.exp (-(n * u ^ 2 / (16 * L ^ 2))))
    (hSmall : localizedTailIntegralBound range bad L n ≤ scale / 2) :
    μ.real {ω | scale ≤ |f ω - mean|} ≤
      μ.real {ω | scale / 2 ≤ |f ω - median|} := by
  exact mean_tail_probability_le_median_tail_probability_from_integrated_tail
    (μ := μ) (f := f) (mean := mean) (median := median)
    (scale := scale) (range := range) hmean hf hRange
    ((localized_tail_integral_bound
      (μ := μ) (f := f) (median := median) (range := range)
      (bad := bad) (L := L) (n := n)
      hRangeNonneg hL hn hTail).trans hSmall)

/-- Final Appendix B concentration bound with quantitative centering obtained
directly from the localized tail bound.

This is the same conclusion as
`appendixB_mean_concentration_from_integrated_centering`, but the auxiliary
integrated-tail input has been eliminated in favour of the pointwise localized
tail estimate together with the explicit smallness assumption on its integral. -/
theorem appendixB_mean_concentration_from_localized_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ}
    {mean median scale range bad n t L c c₂ d eps k : ℝ}
    (hmean : mean = ∫ ω, f ω ∂μ)
    (hf : Integrable f μ)
    (hRange : (fun ω => |f ω - median|) ≤ᵐ[μ] fun _ => range)
    (hRangeNonneg : 0 ≤ range)
    (hL : 0 < L)
    (hn : 0 < n)
    (hTail :
      ∀ ⦃u : ℝ⦄, u ∈ Set.Ioc 0 range →
        μ.real {ω | u ≤ |f ω - median|} ≤
          2 * bad + 4 * Real.exp (-(n * u ^ 2 / (16 * L ^ 2))))
    (hSmall : localizedTailIntegralBound range bad L n ≤ scale / 2)
    (hLevy :
      μ.real {ω | scale / 2 ≤ |f ω - median|} ≤
        2 * bad + 2 * Real.exp (-(n * t ^ 2 / (4 * L ^ 2))))
    (hGood : bad ≤ 2 * Real.exp (-(c * d ^ 2)))
    (hExponent :
      c₂ * d ^ 4 * eps ^ 2 / k ^ 2 ≤ n * t ^ 2 / (4 * L ^ 2)) :
    μ.real {ω | scale ≤ |f ω - mean|} ≤
      4 * Real.exp (-(c * d ^ 2)) +
      2 * Real.exp (-(c₂ * d ^ 4 * eps ^ 2 / k ^ 2)) := by
  have hCentering :
      μ.real {ω | scale ≤ |f ω - mean|} ≤
        μ.real {ω | scale / 2 ≤ |f ω - median|} :=
    mean_tail_probability_le_median_tail_probability_from_localized_tail
      (μ := μ) (f := f) (mean := mean) (median := median)
      (scale := scale) (range := range) (bad := bad) (L := L) (n := n)
      hmean hf hRange hRangeNonneg hL hn hTail hSmall
  have hMedian := appendixB_median_concentration
    (medianTail := μ.real {ω | scale / 2 ≤ |f ω - median|})
    (bad := bad) (n := n) (t := t) (L := L)
    (c := c) (c₂ := c₂) (d := d) (eps := eps) (k := k)
    hLevy hGood hExponent
  linarith

/-- Same as
`mean_tail_probability_le_median_tail_probability_from_integrated_tail`, but
with the paper's displayed bound `range * bad + L / sqrt n`. -/
lemma mean_tail_probability_le_median_tail_probability_from_quantitative_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {mean median scale range bad L n : ℝ}
    (hmean : mean = ∫ ω, f ω ∂μ)
    (hf : Integrable f μ)
    (hRange : (fun ω => |f ω - median|) ≤ᵐ[μ] fun _ => range)
    (hTailIntegral :
      ∫ u in Set.Ioc 0 range, μ.real {ω | u ≤ |f ω - median|} ≤
        quantitativeMedianMeanBound range bad L n)
    (hSmall : quantitativeMedianMeanBound range bad L n ≤ scale / 2) :
    μ.real {ω | scale ≤ |f ω - mean|} ≤
      μ.real {ω | scale / 2 ≤ |f ω - median|} := by
  exact mean_tail_probability_le_median_tail_probability_from_integrated_tail
    (μ := μ) (f := f) (mean := mean) (median := median)
    (scale := scale) (range := range) hmean hf hRange
    (hTailIntegral.trans hSmall)

/-- Final Appendix B concentration bound in the explicit median form.

`hCentering` is the probability-level consequence of the preceding event
inclusion and the small integrated median-to-mean error from the appendix. -/
theorem appendixB_mean_concentration
    {meanTail medianTail bad n t L c c₂ d eps k : ℝ}
    (hCentering : meanTail ≤ medianTail)
    (hLevy :
      medianTail ≤ 2 * bad + 2 * Real.exp (-(n * t ^ 2 / (4 * L ^ 2))))
    (hGood : bad ≤ 2 * Real.exp (-(c * d ^ 2)))
    (hExponent :
      c₂ * d ^ 4 * eps ^ 2 / k ^ 2 ≤ n * t ^ 2 / (4 * L ^ 2)) :
    meanTail ≤
      4 * Real.exp (-(c * d ^ 2)) +
      2 * Real.exp (-(c₂ * d ^ 4 * eps ^ 2 / k ^ 2)) := by
  have hMedian := appendixB_median_concentration
    (medianTail := medianTail) (bad := bad) (n := n) (t := t) (L := L)
    (c := c) (c₂ := c₂) (d := d) (eps := eps) (k := k)
    hLevy hGood hExponent
  linarith

/-- Final Appendix B concentration bound with quantitative median-to-mean
centering.

The median tail is evaluated at half the mean-centered deviation scale.  The
assumption `hTailIntegral` is the quantitative output of integrating the
localized tail bound around the median. -/
theorem appendixB_mean_concentration_from_integrated_centering
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ}
    {mean median scale range bad n t L c c₂ d eps k : ℝ}
    (hmean : mean = ∫ ω, f ω ∂μ)
    (hf : Integrable f μ)
    (hRange : (fun ω => |f ω - median|) ≤ᵐ[μ] fun _ => range)
    (hTailIntegral :
      ∫ u in Set.Ioc 0 range, μ.real {ω | u ≤ |f ω - median|} ≤ scale / 2)
    (hLevy :
      μ.real {ω | scale / 2 ≤ |f ω - median|} ≤
        2 * bad + 2 * Real.exp (-(n * t ^ 2 / (4 * L ^ 2))))
    (hGood : bad ≤ 2 * Real.exp (-(c * d ^ 2)))
    (hExponent :
      c₂ * d ^ 4 * eps ^ 2 / k ^ 2 ≤ n * t ^ 2 / (4 * L ^ 2)) :
    μ.real {ω | scale ≤ |f ω - mean|} ≤
      4 * Real.exp (-(c * d ^ 2)) +
      2 * Real.exp (-(c₂ * d ^ 4 * eps ^ 2 / k ^ 2)) := by
  have hCentering :
      μ.real {ω | scale ≤ |f ω - mean|} ≤
        μ.real {ω | scale / 2 ≤ |f ω - median|} :=
    mean_tail_probability_le_median_tail_probability_from_integrated_tail
      (μ := μ) (f := f) (mean := mean) (median := median)
      (scale := scale) (range := range)
      hmean hf hRange hTailIntegral
  exact appendixB_mean_concentration
    (meanTail := μ.real {ω | scale ≤ |f ω - mean|})
    (medianTail := μ.real {ω | scale / 2 ≤ |f ω - median|})
    (bad := bad) (n := n) (t := t) (L := L)
    (c := c) (c₂ := c₂) (d := d) (eps := eps) (k := k)
    hCentering hLevy hGood hExponent

/-- Absorb the numerical constants `4` and `2` into a single constant `K`.

This is the last step turning the explicit estimate into the paper's
`C e^{-c d^2} + C exp(-c d^4 ε^2/k^2)` form. -/
theorem absorb_numeric_constants
    {tail E₁ E₂ K : ℝ}
    (hTail : tail ≤ 4 * E₁ + 2 * E₂)
    (hK : 4 ≤ K)
    (hE₁ : 0 ≤ E₁)
    (hE₂ : 0 ≤ E₂) :
    tail ≤ K * E₁ + K * E₂ := by
  have hK₂ : 2 ≤ K := by linarith
  nlinarith

/-- The final Appendix B estimate, in the same big-constant form as the
manuscript theorem. -/
theorem local_lipschitz_concentration_theorem
    {meanTail medianTail bad n t L c c₂ d eps k K : ℝ}
    (hCentering : meanTail ≤ medianTail)
    (hLevy :
      medianTail ≤ 2 * bad + 2 * Real.exp (-(n * t ^ 2 / (4 * L ^ 2))))
    (hGood : bad ≤ 2 * Real.exp (-(c * d ^ 2)))
    (hExponent :
      c₂ * d ^ 4 * eps ^ 2 / k ^ 2 ≤ n * t ^ 2 / (4 * L ^ 2))
    (hK : 4 ≤ K) :
    meanTail ≤
      K * Real.exp (-(c * d ^ 2)) +
      K * Real.exp (-(c₂ * d ^ 4 * eps ^ 2 / k ^ 2)) := by
  have hExplicit := appendixB_mean_concentration
    (meanTail := meanTail) (medianTail := medianTail) (bad := bad)
    (n := n) (t := t) (L := L) (c := c) (c₂ := c₂)
    (d := d) (eps := eps) (k := k)
    hCentering hLevy hGood hExponent
  exact absorb_numeric_constants hExplicit hK
    (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _))

/-! ## Spherical normalization of expectation inputs -/

/-- Expectation bound under radial/spherical factorization.

Read `gaussianMean = radialMean * sphericalMean` as the polar decomposition
of a Gaussian expectation into an independent radial mean and a spherical
expectation.  Once the Gaussian estimate has the same radial factor, it
cancels to give the corresponding normalized spherical estimate. -/
theorem spherical_expectation_bound_from_radial_factorization
    {gaussianMean radialMean sphericalMean target : ℝ}
    (hRadialMean : 0 < radialMean)
    (hFactor : gaussianMean = radialMean * sphericalMean)
    (hBound : gaussianMean ≤ radialMean * target) :
    sphericalMean ≤ target := by
  have hmul : radialMean * sphericalMean ≤ radialMean * target := by
    rw [← hFactor]
    exact hBound
  exact (mul_le_mul_iff_of_pos_left hRadialMean).mp hmul

/-- Gamma/Wishart expectation bound under the spherical normalization.

This is the same cancellation lemma as
`spherical_expectation_bound_from_radial_factorization`, named for the
partial-transpose/Wishart input used in Appendix B. -/
theorem spherical_gamma_expectation_bound_from_radial_factorization
    {wishartGammaMean radialSecondMean sphericalGammaMean target : ℝ}
    (hRadialSecondMean : 0 < radialSecondMean)
    (hFactor : wishartGammaMean = radialSecondMean * sphericalGammaMean)
    (hBound : wishartGammaMean ≤ radialSecondMean * target) :
    sphericalGammaMean ≤ target := by
  exact spherical_expectation_bound_from_radial_factorization
    (hRadialMean := hRadialSecondMean)
    (hFactor := hFactor)
    (hBound := hBound)

/-- Autonomous Appendix B package for the two expectation normalizations.

The hypotheses are exactly the analytic inputs one gets from the standard
Gaussian/Gamma estimates plus polar factorization:

* a sample-operator expectation factorization through the Gaussian radius,
* a Gaussian sample-operator bound with that same radial factor,
* a Wishart/partial-transpose expectation factorization through the squared
  radius,
* a Wishart/partial-transpose bound with that same squared-radius factor.

The conclusion is the normalized pair of spherical expectation bounds used by
Appendix B. -/
theorem spherical_normalization_expectation_inputs
    {gaussianMean radialMean sphericalMean sampleTarget
      wishartGammaMean radialSecondMean sphericalGammaMean gammaTarget : ℝ}
    (hRadialMean : 0 < radialMean)
    (hSampleFactor : gaussianMean = radialMean * sphericalMean)
    (hSampleBound : gaussianMean ≤ radialMean * sampleTarget)
    (hRadialSecondMean : 0 < radialSecondMean)
    (hGammaFactor : wishartGammaMean = radialSecondMean * sphericalGammaMean)
    (hGammaBound : wishartGammaMean ≤ radialSecondMean * gammaTarget) :
    sphericalMean ≤ sampleTarget ∧ sphericalGammaMean ≤ gammaTarget := by
  constructor
  · exact spherical_expectation_bound_from_radial_factorization
      hRadialMean hSampleFactor hSampleBound
  · exact spherical_gamma_expectation_bound_from_radial_factorization
      hRadialSecondMean hGammaFactor hGammaBound

/-- Paper-shaped version of the spherical expectation normalization step.

This packages the two Appendix B expectations in their final normalized
scales: the sample operator norm at scale `C1 / d`, and the partial transpose
at scale `C2 / d^2`. -/
theorem appendixB_spherical_normalization_expectation_inputs
    {gaussianMean radialMean sphericalMean
      wishartGammaMean radialSecondMean sphericalGammaMean C1 C2 d : ℝ}
    (hRadialMean : 0 < radialMean)
    (hSampleFactor : gaussianMean = radialMean * sphericalMean)
    (hSampleBound : gaussianMean ≤ radialMean * (C1 / d))
    (hRadialSecondMean : 0 < radialSecondMean)
    (hGammaFactor : wishartGammaMean = radialSecondMean * sphericalGammaMean)
    (hGammaBound : wishartGammaMean ≤ radialSecondMean * (C2 / d ^ 2)) :
    sphericalMean ≤ C1 / d ∧ sphericalGammaMean ≤ C2 / d ^ 2 := by
  exact spherical_normalization_expectation_inputs
    hRadialMean hSampleFactor hSampleBound
    hRadialSecondMean hGammaFactor hGammaBound

/-! ## Paper-facing notation

The next declarations do not prove new analysis.  They pin down the notation
used in the current LaTeX Appendix B, so that the formal statement is visibly
the same as the manuscript statement:

* `d` is the local Hilbert-space dimension,
* `s` is the Wishart ancilla/sample dimension,
* `r` is the fixed moment order in `f_r`,
* `sphereDimension d s = 2 d^2 s` is the real dimension of the
  Hilbert-Schmidt sphere in `M_{d^2,s}(\mathbb C)`,
* `naturalDeviationScale d eps r = eps / d^{2r-2}`,
* the final tail has the form
  `K exp(-cSphere d^2) + K exp(-cLocal d^4 eps^2 / k^2)`.

All analytic inputs remain explicit hypotheses.  This is intentional: it makes
the file an auditable interface between the paper proof and the future full
formalization.
-/

/-- Real dimension of the Hilbert-Schmidt ambient space
`M_{d^2,s}(\mathbb C)`, written as a real Euclidean space. -/
def sphereDimension (d s : ℝ) : ℝ :=
  2 * d ^ 2 * s

/-- The normalized deviation scale appearing in Appendix B:
`epsilon / d^(2r-2)`. -/
noncomputable def naturalDeviationScale (d eps : ℝ) (r : ℕ) : ℝ :=
  eps / d ^ (2 * r - 2)

/-- Abstract form of the deterministic local Lipschitz scale for `f_r`.

The manuscript proves this with matrix norm estimates on the good set.  The
constant `C` hides the fixed parameters of the regime, while the important
feature is the factor `momentParameter / d^(2r-2)`. -/
noncomputable def localLipschitzScale (C momentParameter d : ℝ) (r : ℕ) : ℝ :=
  C * momentParameter / d ^ (2 * r - 2)

/-- The Levy exponent before simplifying the matrix scales. -/
noncomputable def localLevyExponent (n t L : ℝ) : ℝ :=
  n * t ^ 2 / (4 * L ^ 2)

/-- The target exponent after inserting the Appendix B scales. -/
noncomputable def targetLocalExponent (cLocal d eps momentParameter : ℝ) : ℝ :=
  cLocal * d ^ 4 * eps ^ 2 / momentParameter ^ 2

/-- Tail from the bad set, in the scale used in the manuscript. -/
noncomputable def goodSetTail (cSphere d : ℝ) : ℝ :=
  Real.exp (-(cSphere * d ^ 2))

/-- Explicit median tail before absorbing numerical constants. -/
noncomputable def paperMedianTailBound (cSphere cLocal d eps momentParameter : ℝ) : ℝ :=
  4 * goodSetTail cSphere d +
  2 * Real.exp (-(targetLocalExponent cLocal d eps momentParameter))

/-- Final big-constant tail bound in the statement of Appendix B. -/
noncomputable def paperTailBound (K cSphere cLocal d eps momentParameter : ℝ) : ℝ :=
  K * goodSetTail cSphere d +
  K * Real.exp (-(targetLocalExponent cLocal d eps momentParameter))

/-- Explicit sufficient condition for the small-deviation branch.

If the target exponent is at most `log K`, then the second exponential term in
the final bound is at least `1 / K`.  Hence the whole right-hand side is at
least `1`, and the trivial probability bound closes this branch. -/
theorem paperTailBound_ge_one_of_target_exponent_le_log
    {K cSphere cLocal d eps momentParameter : ℝ}
    (hKpos : 0 < K)
    (hSmall :
      targetLocalExponent cLocal d eps momentParameter ≤ Real.log K) :
    1 ≤ paperTailBound K cSphere cLocal d eps momentParameter := by
  have hneg :
      -Real.log K ≤ -(targetLocalExponent cLocal d eps momentParameter) := by
    linarith
  have hexp :
      Real.exp (-Real.log K) ≤
        Real.exp (-(targetLocalExponent cLocal d eps momentParameter)) :=
    (Real.exp_le_exp).2 hneg
  have hExpLog : Real.exp (-Real.log K) = K⁻¹ := by
    rw [Real.exp_neg, Real.exp_log hKpos]
  have hinv :
      K⁻¹ ≤ Real.exp (-(targetLocalExponent cLocal d eps momentParameter)) := by
    simpa [hExpLog] using hexp
  have hSecond :
      1 ≤ K * Real.exp (-(targetLocalExponent cLocal d eps momentParameter)) := by
    have hmul :=
      mul_le_mul_of_nonneg_left hinv (le_of_lt hKpos)
    have hcancel : K * K⁻¹ = 1 := mul_inv_cancel₀ hKpos.ne'
    simpa [hcancel] using hmul
  have hFirstNonneg : 0 ≤ K * goodSetTail cSphere d :=
    mul_nonneg (le_of_lt hKpos) (le_of_lt (Real.exp_pos _))
  dsimp [paperTailBound]
  linarith

/-- Paper notation for the deterministic median-to-mean event inclusion. -/
lemma paper_mean_deviation_implies_median_deviation
    {z mean median d eps : ℝ} {r : ℕ}
    (hshift : |mean - median| ≤ naturalDeviationScale d eps r / 2)
    (hdev : naturalDeviationScale d eps r ≤ |z - mean|) :
    naturalDeviationScale d eps r / 2 ≤ |z - median| :=
  mean_deviation_implies_median_deviation hshift hdev

/-- Paper notation for `Omega = Omega_1 ∩ Omega_2`. -/
theorem paper_good_set_intersection_bound
    {bad bad₁ bad₂ cSphere d : ℝ}
    (hUnion : bad ≤ bad₁ + bad₂)
    (hΩ₁ : bad₁ ≤ goodSetTail cSphere d)
    (hΩ₂ : bad₂ ≤ goodSetTail cSphere d) :
    bad ≤ 2 * goodSetTail cSphere d := by
  exact good_set_intersection_bound hUnion hΩ₁ hΩ₂

/-- Paper notation for the median concentration estimate. -/
theorem paper_median_concentration
    {medianTail bad n t L cSphere cLocal d eps momentParameter : ℝ}
    (hLevy :
      medianTail ≤ 2 * bad + 2 * Real.exp (-(localLevyExponent n t L)))
    (hGood : bad ≤ 2 * goodSetTail cSphere d)
    (hExponent :
      targetLocalExponent cLocal d eps momentParameter ≤ localLevyExponent n t L) :
    medianTail ≤ paperMedianTailBound cSphere cLocal d eps momentParameter := by
  simpa [paperMedianTailBound, goodSetTail, targetLocalExponent, localLevyExponent]
    using appendixB_median_concentration
      (medianTail := medianTail) (bad := bad) (n := n) (t := t) (L := L)
      (c := cSphere) (c₂ := cLocal) (d := d) (eps := eps)
      (k := momentParameter) hLevy hGood hExponent

/-- The scale computation used in Appendix B.

This removes the earlier raw assumption that the Levy exponent has the desired
`d^4 epsilon^2 / k^2` size.  If the effective dimension is `cDim d^4`, the
deviation is `epsilon / d^(2r-2)`, and the Lipschitz constant is
`C k / d^(2r-2)`, then the Levy exponent is exactly
`(cDim / (4 C^2)) d^4 epsilon^2 / k^2`. -/
theorem target_exponent_le_from_exact_scales
    {cDim C cLocal d eps momentParameter : ℝ} {r : ℕ}
    (hd : d ≠ 0)
    (hC : C ≠ 0)
    (hk : momentParameter ≠ 0)
    (hcLocal : cLocal ≤ cDim / (4 * C ^ 2)) :
    targetLocalExponent cLocal d eps momentParameter ≤
      localLevyExponent
        (cDim * d ^ 4)
        (naturalDeviationScale d eps r)
        (localLipschitzScale C momentParameter d r) := by
  unfold targetLocalExponent localLevyExponent naturalDeviationScale localLipschitzScale
  let q : ℝ := d ^ (2 * r - 2)
  have hq : q ≠ 0 := by
    dsimp [q]
    exact pow_ne_zero _ hd
  have hEq :
      (cDim * d ^ 4) * (eps / q) ^ 2 /
          (4 * (C * momentParameter / q) ^ 2) =
        (cDim / (4 * C ^ 2)) * d ^ 4 * eps ^ 2 / momentParameter ^ 2 := by
    field_simp [hq, hC, hk]
  have hscale : 0 ≤ d ^ 4 * eps ^ 2 / momentParameter ^ 2 := by
    positivity
  have hmul := mul_le_mul_of_nonneg_right hcLocal hscale
  calc
    cLocal * d ^ 4 * eps ^ 2 / momentParameter ^ 2
        = cLocal * (d ^ 4 * eps ^ 2 / momentParameter ^ 2) := by ring
    _ ≤ (cDim / (4 * C ^ 2)) *
        (d ^ 4 * eps ^ 2 / momentParameter ^ 2) := hmul
    _ = (cDim * d ^ 4) * (eps / q) ^ 2 /
          (4 * (C * momentParameter / q) ^ 2) := by
        rw [hEq]
        ring

/-- The same scale computation with the half-scale deviation needed for the
median-to-mean replacement.

When the final deviation around the mean is `epsilon / d^(2r-2)`, the median
tail must be evaluated at half that scale.  This costs a factor `4` in the
Levy exponent, hence the constant `cDim / (16 C^2)` rather than
`cDim / (4 C^2)`. -/
theorem target_exponent_le_from_half_exact_scales
    {cDim C cLocal d eps momentParameter : ℝ} {r : ℕ}
    (hd : d ≠ 0)
    (hC : C ≠ 0)
    (hk : momentParameter ≠ 0)
    (hcLocal : cLocal ≤ cDim / (16 * C ^ 2)) :
    targetLocalExponent cLocal d eps momentParameter ≤
      localLevyExponent
        (cDim * d ^ 4)
        (naturalDeviationScale d eps r / 2)
        (localLipschitzScale C momentParameter d r) := by
  unfold targetLocalExponent localLevyExponent naturalDeviationScale localLipschitzScale
  let q : ℝ := d ^ (2 * r - 2)
  have hq : q ≠ 0 := by
    dsimp [q]
    exact pow_ne_zero _ hd
  have hEq :
      (cDim * d ^ 4) * ((eps / q) / 2) ^ 2 /
          (4 * (C * momentParameter / q) ^ 2) =
        (cDim / (16 * C ^ 2)) * d ^ 4 * eps ^ 2 / momentParameter ^ 2 := by
    field_simp [hq, hC, hk]
    ring
  have hscale : 0 ≤ d ^ 4 * eps ^ 2 / momentParameter ^ 2 := by
    positivity
  have hmul := mul_le_mul_of_nonneg_right hcLocal hscale
  calc
    cLocal * d ^ 4 * eps ^ 2 / momentParameter ^ 2
        = cLocal * (d ^ 4 * eps ^ 2 / momentParameter ^ 2) := by ring
    _ ≤ (cDim / (16 * C ^ 2)) *
        (d ^ 4 * eps ^ 2 / momentParameter ^ 2) := hmul
    _ = (cDim * d ^ 4) * ((eps / q) / 2) ^ 2 /
          (4 * (C * momentParameter / q) ^ 2) := by
        rw [hEq]
        ring

/-- The complete list of analytic inputs needed for the paper version of
Appendix B.

`meanTail` should be read as
`P(|f_r - E f_r| >= epsilon / d^(2r-2))`.
`medianTail` is the same probability centered at a median, with half the
deviation scale after the median-to-mean reduction.  `bad` is `P(Omega^c)`.
-/
structure PaperConcentrationInputs where
  meanTail : ℝ
  medianTail : ℝ
  bad : ℝ
  sphereDim : ℝ
  deviation : ℝ
  lipschitzConstant : ℝ
  cSphere : ℝ
  cLocal : ℝ
  d : ℝ
  eps : ℝ
  momentParameter : ℝ
  K : ℝ
  hCentering : meanTail ≤ medianTail
  hLocalLevy :
    medianTail ≤
      2 * bad +
      2 * Real.exp (-(localLevyExponent sphereDim deviation lipschitzConstant))
  hGood : bad ≤ 2 * goodSetTail cSphere d
  hExponent :
    targetLocalExponent cLocal d eps momentParameter ≤
      localLevyExponent sphereDim deviation lipschitzConstant
  hK : 4 ≤ K

/-- Appendix B in the manuscript notation, conditional on the analytic inputs
listed in `PaperConcentrationInputs`. -/
theorem paper_local_lipschitz_concentration (I : PaperConcentrationInputs) :
    I.meanTail ≤
      paperTailBound I.K I.cSphere I.cLocal I.d I.eps I.momentParameter := by
  simpa [paperTailBound, goodSetTail, targetLocalExponent, localLevyExponent]
    using local_lipschitz_concentration_theorem
      (meanTail := I.meanTail) (medianTail := I.medianTail) (bad := I.bad)
      (n := I.sphereDim) (t := I.deviation) (L := I.lipschitzConstant)
      (c := I.cSphere) (c₂ := I.cLocal) (d := I.d) (eps := I.eps)
      (k := I.momentParameter) (K := I.K)
      I.hCentering I.hLocalLevy I.hGood I.hExponent I.hK

/-- Paper-facing final branch.

In the large-deviation branch, the median-to-mean replacement gives
`meanTail <= medianTail`.  In the small-deviation branch, the final right-hand
side has already been enlarged so that it is at least `1`, and the trivial
probability bound suffices. -/
theorem paper_local_lipschitz_concentration_with_centering_or_trivial_branch
    {meanTail medianTail bad sphereDim deviation lipschitzConstant
      cSphere cLocal d eps momentParameter K : ℝ}
    (hMeanTailLeOne : meanTail ≤ 1)
    (hBranch :
      meanTail ≤ medianTail ∨
        1 ≤ paperTailBound K cSphere cLocal d eps momentParameter)
    (hLocalLevy :
      medianTail ≤
        2 * bad +
        2 * Real.exp (-(localLevyExponent sphereDim deviation lipschitzConstant)))
    (hGood : bad ≤ 2 * goodSetTail cSphere d)
    (hExponent :
      targetLocalExponent cLocal d eps momentParameter ≤
        localLevyExponent sphereDim deviation lipschitzConstant)
    (hK : 4 ≤ K) :
    meanTail ≤ paperTailBound K cSphere cLocal d eps momentParameter := by
  rcases hBranch with hCentering | hTrivial
  · exact paper_local_lipschitz_concentration
      { meanTail := meanTail
        medianTail := medianTail
        bad := bad
        sphereDim := sphereDim
        deviation := deviation
        lipschitzConstant := lipschitzConstant
        cSphere := cSphere
        cLocal := cLocal
        d := d
        eps := eps
        momentParameter := momentParameter
        K := K
        hCentering := hCentering
        hLocalLevy := hLocalLevy
        hGood := hGood
        hExponent := hExponent
        hK := hK }
  · exact hMeanTailLeOne.trans hTrivial

/-- Paper-facing final branch with an explicit small-deviation threshold.

The small branch is no longer the raw assumption that the right-hand side is
at least `1`.  It is the checkable exponent condition
`targetLocalExponent <= log K`, which is exactly the condition making the
second exponential term alone at least `1 / K`. -/
theorem paper_local_lipschitz_concentration_with_explicit_small_branch
    {meanTail medianTail bad sphereDim deviation lipschitzConstant
      cSphere cLocal d eps momentParameter K : ℝ}
    (hMeanTailLeOne : meanTail ≤ 1)
    (hBranch :
      meanTail ≤ medianTail ∨
        targetLocalExponent cLocal d eps momentParameter ≤ Real.log K)
    (hLocalLevy :
      medianTail ≤
        2 * bad +
        2 * Real.exp (-(localLevyExponent sphereDim deviation lipschitzConstant)))
    (hGood : bad ≤ 2 * goodSetTail cSphere d)
    (hExponent :
      targetLocalExponent cLocal d eps momentParameter ≤
        localLevyExponent sphereDim deviation lipschitzConstant)
    (hK : 4 ≤ K) :
    meanTail ≤ paperTailBound K cSphere cLocal d eps momentParameter := by
  have hKpos : 0 < K := by linarith
  refine paper_local_lipschitz_concentration_with_centering_or_trivial_branch
    (meanTail := meanTail) (medianTail := medianTail) (bad := bad)
    (sphereDim := sphereDim) (deviation := deviation)
    (lipschitzConstant := lipschitzConstant) (cSphere := cSphere)
    (cLocal := cLocal) (d := d) (eps := eps)
    (momentParameter := momentParameter) (K := K)
    hMeanTailLeOne ?_ hLocalLevy hGood hExponent hK
  rcases hBranch with hCentering | hSmall
  · exact Or.inl hCentering
  · exact Or.inr
      (paperTailBound_ge_one_of_target_exponent_le_log
        (K := K) (cSphere := cSphere) (cLocal := cLocal) (d := d)
        (eps := eps) (momentParameter := momentParameter) hKpos hSmall)

/-- A convenience specialization in which the abstract `sphereDim`,
`deviation`, and local Lipschitz constant have already been instantiated with
the scales displayed in the paper. -/
theorem paper_local_lipschitz_concentration_with_scales
    {meanTail medianTail bad C cSphere cLocal d eps s momentParameter K : ℝ}
    {r : ℕ}
    (hCentering : meanTail ≤ medianTail)
    (hLocalLevy :
      medianTail ≤
        2 * bad +
        2 * Real.exp
          (-(localLevyExponent
            (sphereDimension d s)
            (naturalDeviationScale d eps r)
            (localLipschitzScale C momentParameter d r))))
    (hGood : bad ≤ 2 * goodSetTail cSphere d)
    (hExponent :
      targetLocalExponent cLocal d eps momentParameter ≤
        localLevyExponent
          (sphereDimension d s)
          (naturalDeviationScale d eps r)
          (localLipschitzScale C momentParameter d r))
    (hK : 4 ≤ K) :
    meanTail ≤ paperTailBound K cSphere cLocal d eps momentParameter := by
  exact paper_local_lipschitz_concentration
    { meanTail := meanTail
      medianTail := medianTail
      bad := bad
      sphereDim := sphereDimension d s
      deviation := naturalDeviationScale d eps r
      lipschitzConstant := localLipschitzScale C momentParameter d r
      cSphere := cSphere
      cLocal := cLocal
      d := d
      eps := eps
      momentParameter := momentParameter
      K := K
      hCentering := hCentering
      hLocalLevy := hLocalLevy
      hGood := hGood
      hExponent := hExponent
      hK := hK }

/-- A less raw paper wrapper.

Compared with `paper_local_lipschitz_concentration_with_scales`, this theorem
does not ask for the exponent comparison as a hypothesis: that comparison
follows from the displayed Appendix B scales.  It also takes the two
separate good-set estimates and proves the union bound internally. -/
theorem paper_local_lipschitz_concentration_from_good_sets_and_scales
    {meanTail medianTail bad bad₁ bad₂ C cDim cSphere cLocal d eps
      momentParameter K : ℝ}
    {r : ℕ}
    (hd : d ≠ 0)
    (hC : C ≠ 0)
    (hk : momentParameter ≠ 0)
    (hcLocal : cLocal ≤ cDim / (4 * C ^ 2))
    (hCentering : meanTail ≤ medianTail)
    (hGoodUnion : bad ≤ bad₁ + bad₂)
    (hΩ₁ : bad₁ ≤ goodSetTail cSphere d)
    (hΩ₂ : bad₂ ≤ goodSetTail cSphere d)
    (hLocalLevy :
      medianTail ≤
        2 * bad +
        2 * Real.exp
          (-(localLevyExponent
            (cDim * d ^ 4)
            (naturalDeviationScale d eps r)
            (localLipschitzScale C momentParameter d r))))
    (hK : 4 ≤ K) :
    meanTail ≤ paperTailBound K cSphere cLocal d eps momentParameter := by
  have hGood : bad ≤ 2 * goodSetTail cSphere d :=
    paper_good_set_intersection_bound hGoodUnion hΩ₁ hΩ₂
  have hExponent :
      targetLocalExponent cLocal d eps momentParameter ≤
        localLevyExponent
          (cDim * d ^ 4)
          (naturalDeviationScale d eps r)
          (localLipschitzScale C momentParameter d r) :=
    target_exponent_le_from_exact_scales
      (cDim := cDim) (C := C) (cLocal := cLocal) (d := d)
      (eps := eps) (momentParameter := momentParameter) (r := r)
      hd hC hk hcLocal
  exact paper_local_lipschitz_concentration
    { meanTail := meanTail
      medianTail := medianTail
      bad := bad
      sphereDim := cDim * d ^ 4
      deviation := naturalDeviationScale d eps r
      lipschitzConstant := localLipschitzScale C momentParameter d r
      cSphere := cSphere
      cLocal := cLocal
      d := d
      eps := eps
      momentParameter := momentParameter
      K := K
      hCentering := hCentering
      hLocalLevy := hLocalLevy
      hGood := hGood
      hExponent := hExponent
      hK := hK }

/-- Strongest paper-facing wrapper for Appendix B currently formalized.

This version removes the raw centering hypothesis.  The input is the
quantitative integrated-tail estimate which gives
`|E f - M| <= epsilon /(2 d^(2r-2))`.  The localized Levy estimate is applied at
half the final deviation scale, with the corresponding factor `16`
in the exponent constant. -/
theorem paper_local_lipschitz_concentration_from_integrated_centering_and_scales
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ}
    {mean median range bad bad₁ bad₂ C cDim cSphere cLocal d eps
      momentParameter K : ℝ}
    {r : ℕ}
    (hd : d ≠ 0)
    (hC : C ≠ 0)
    (hk : momentParameter ≠ 0)
    (hcLocal : cLocal ≤ cDim / (16 * C ^ 2))
    (hmean : mean = ∫ ω, f ω ∂μ)
    (hf : Integrable f μ)
    (hRange : (fun ω => |f ω - median|) ≤ᵐ[μ] fun _ => range)
    (hTailIntegral :
      ∫ u in Set.Ioc 0 range, μ.real {ω | u ≤ |f ω - median|} ≤
        naturalDeviationScale d eps r / 2)
    (hGoodUnion : bad ≤ bad₁ + bad₂)
    (hΩ₁ : bad₁ ≤ goodSetTail cSphere d)
    (hΩ₂ : bad₂ ≤ goodSetTail cSphere d)
    (hLocalLevy :
      μ.real
          {ω | naturalDeviationScale d eps r / 2 ≤ |f ω - median|} ≤
        2 * bad +
        2 * Real.exp
          (-(localLevyExponent
            (cDim * d ^ 4)
            (naturalDeviationScale d eps r / 2)
            (localLipschitzScale C momentParameter d r))))
    (hK : 4 ≤ K) :
    μ.real {ω | naturalDeviationScale d eps r ≤ |f ω - mean|} ≤
      paperTailBound K cSphere cLocal d eps momentParameter := by
  have hGood : bad ≤ 2 * goodSetTail cSphere d :=
    paper_good_set_intersection_bound hGoodUnion hΩ₁ hΩ₂
  have hExponent :
      targetLocalExponent cLocal d eps momentParameter ≤
        localLevyExponent
          (cDim * d ^ 4)
          (naturalDeviationScale d eps r / 2)
          (localLipschitzScale C momentParameter d r) :=
    target_exponent_le_from_half_exact_scales
      (cDim := cDim) (C := C) (cLocal := cLocal) (d := d)
      (eps := eps) (momentParameter := momentParameter) (r := r)
      hd hC hk hcLocal
  have hExplicit :
      μ.real {ω | naturalDeviationScale d eps r ≤ |f ω - mean|} ≤
        4 * goodSetTail cSphere d +
        2 * Real.exp (-(targetLocalExponent cLocal d eps momentParameter)) := by
    simpa [goodSetTail, targetLocalExponent, localLevyExponent]
      using appendixB_mean_concentration_from_integrated_centering
        (μ := μ) (f := f) (mean := mean) (median := median)
        (scale := naturalDeviationScale d eps r) (range := range)
        (bad := bad) (n := cDim * d ^ 4)
        (t := naturalDeviationScale d eps r / 2)
        (L := localLipschitzScale C momentParameter d r)
        (c := cSphere) (c₂ := cLocal) (d := d) (eps := eps)
        (k := momentParameter)
        hmean hf hRange hTailIntegral hLocalLevy
        (by simpa [goodSetTail] using hGood)
        (by simpa [targetLocalExponent, localLevyExponent] using hExponent)
  exact absorb_numeric_constants
    (tail := μ.real {ω | naturalDeviationScale d eps r ≤ |f ω - mean|})
    (E₁ := goodSetTail cSphere d)
    (E₂ := Real.exp (-(targetLocalExponent cLocal d eps momentParameter)))
    (K := K) hExplicit hK
    (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _))

/-- Final paper-facing assembly of the main concentration theorem.

This is the same tail bound as `paper_local_lipschitz_concentration_from_integrated_centering_and_scales`,
but the proof explicitly passes through the expectation-shift bridge
`F_k → f_k` before invoking the final concentration wrapper. -/
theorem paper_main_theorem_assembled
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ}
    {mean median range bad bad₁ bad₂ C cDim cSphere cLocal d eps
      momentParameter K : ℝ}
    {r : ℕ}
    (hd : d ≠ 0)
    (hC : C ≠ 0)
    (hk : momentParameter ≠ 0)
    (hcLocal : cLocal ≤ cDim / (16 * C ^ 2))
    (hmean : mean = ∫ ω, f ω ∂μ)
    (hf : Integrable f μ)
    (hRange : (fun ω => |f ω - median|) ≤ᵐ[μ] fun _ => range)
    (hTailIntegral :
      ∫ u in Set.Ioc 0 range, μ.real {ω | u ≤ |f ω - median|} ≤
        naturalDeviationScale d eps r / 2)
    (hGoodUnion : bad ≤ bad₁ + bad₂)
    (hΩ₁ : bad₁ ≤ goodSetTail cSphere d)
    (hΩ₂ : bad₂ ≤ goodSetTail cSphere d)
    (hLocalLevy :
      μ.real
          {ω | naturalDeviationScale d eps r / 2 ≤ |f ω - median|} ≤
        2 * bad +
        2 * Real.exp
          (-(localLevyExponent
            (cDim * d ^ 4)
            (naturalDeviationScale d eps r / 2)
            (localLipschitzScale C momentParameter d r))))
    (hK : 4 ≤ K) :
    μ.real {ω | naturalDeviationScale d eps r ≤ |f ω - mean|} ≤
      paperTailBound K cSphere cLocal d eps momentParameter := by
  have hShift :
      μ.real {ω | naturalDeviationScale d eps r ≤ |f ω - mean|} ≤
        μ.real
          {ω | naturalDeviationScale d eps r / 2 ≤ |f ω - median|} :=
    paper_expectation_shift_Fk_to_fk
      (μ := μ) (f := f) (mean := mean) (median := median)
      (scale := naturalDeviationScale d eps r) (range := range)
      hmean hf hRange hTailIntegral
  have hFinal :
      μ.real {ω | naturalDeviationScale d eps r ≤ |f ω - mean|} ≤
        paperTailBound K cSphere cLocal d eps momentParameter := by
    exact paper_local_lipschitz_concentration_from_integrated_centering_and_scales
      (μ := μ) (f := f) (mean := mean) (median := median)
      (range := range) (bad := bad) (bad₁ := bad₁) (bad₂ := bad₂)
      (C := C) (cDim := cDim) (cSphere := cSphere) (cLocal := cLocal)
      (d := d) (eps := eps) (momentParameter := momentParameter) (K := K)
      (r := r) hd hC hk hcLocal hmean hf hRange hTailIntegral hGoodUnion hΩ₁
      hΩ₂ hLocalLevy hK
  exact hFinal

end AppendixB
